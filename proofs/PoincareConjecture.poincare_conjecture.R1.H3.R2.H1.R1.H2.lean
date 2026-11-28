import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R2_H1_R1
import Mathlib

-- Credit: @ZenimXD

/-!
The proof assembles the parallel Cairns smoothing development in open-math-agents.
Re-embedding and transitions adapt PRs 7914 and 7488. The chart construction
adapts @NicholasWierenga’s proofs. The plane and leaf field proofs adapt
commits 7c5d6531a and cb6ad05ab, ported from PoincareLib.
Copyright 2026 The Formal Conjectures Authors. Apache-2.0.
-/

/-
# Transverse planes of the positive-dimensional stars of a finite three-complex

Adapted from the PoincareLib contributors' PoincareMT M76 formalization
at LehengChen/PoincareConjecture commit `60de1a94ca7038d04ed123b490a3229f8aa5fa75`.
Copyright (c) 2026 the PoincareLib contributors. Licensed under Apache 2.0.
This file consolidates the dependency modules of `contractible_positiveFaceStarPlanes`,
scopes each original module body, removes per-file `autoImplicit` settings, and replaces the
plane extensionality attribute with an explicit lemma.
See Cairns (1940), pp. 799–801 and 807, and M76 derivation 42.
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

/- ## ParallelAtlas -/
section
open Set Geometry
open scoped Manifold ContDiff
namespace OMA.CairnsAtlas

def H1 : Prop :=
  let Good (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
    let carrier (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    K.faces.Finite ∧ (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
    (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
    (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → EuclideanSpace ℝ (Fin 3),
      (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3), EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty)
  ∀ (n : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))), Good n K →
    ∃ (m : ℕ) (L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
      AffineIndependent ℝ ((↑) : L.vertices → EuclideanSpace ℝ (Fin m)) ∧
      Good m L ∧ Nonempty (K.space ≃ₜ L.space)

def H2 : Prop :=
  let Good (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
    let carrier (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    K.faces.Finite ∧ (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
    (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
    (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → EuclideanSpace ℝ (Fin 3),
      (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3), EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty)
  ∀ (m : ℕ) (L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    AffineIndependent ℝ ((↑) : L.vertices → EuclideanSpace ℝ (Fin m)) → Good m L →
    let E := EuclideanSpace ℝ (Fin m)
    let V := EuclideanSpace ℝ (Fin 3)
    ∀ (M : Type) [TopologicalSpace M] (e : M ≃ₜ L.space),
    let v := fun y : M => (e y : E)
    ∃ (c : M → OpenPartialHomeomorph M V) (P : M → Submodule ℝ E)
      (b : M → V →ᴬ[ℝ] E) (Q : M → E → E →L[ℝ] V),
    (∀ y : M, ∃ i, y ∈ (c i).source) ∧
    (∀ i z, z ∈ (c i).target → ContDiffAt ℝ ∞ (Q i) (b i z)) ∧
    (∀ i y, y ∈ (c i).source → Function.RightInverse (b i).contLinear (Q i (v y)) ∧
      (Q i (v y)).ker = P y ∧ Q i (b i (c i y)) = Q i (v y) ∧ b i (c i y) - v y ∈ P y)

end OMA.CairnsAtlas

end

/- ## LeafCoordinates -/
section
open Set Filter Geometry Metric unitInterval
open scoped ContDiff NNReal Topology

namespace OMA.CairnsLeafCoordinates

private theorem eq_of_sub_mem_ker_of_convex {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Q : E → E →L[ℝ] V} {U : Set E} (hQ : ContinuousOn Q U) (hU : Convex ℝ U)
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ (Q y).ker → Q z = Q y)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hxy : y - x ∈ (Q x).ker) : Q y = Q x := by
  let c : I → E := fun t => AffineMap.lineMap x y (t : ℝ)
  have hc : Continuous c := by
    simp only [c, AffineMap.lineMap_apply_module']
    fun_prop
  have hcU (t : I) : c t ∈ U := hU.lineMap_mem hx hy t.property
  have hcont : Continuous (fun t : I => Q (c t)) := hQ.comp_continuous hc hcU
  let S : Set I := {t | Q (c t) = Q x}
  have hclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hnear := hc.continuousAt.eventually (hleaf (c t) (hcU t))
    filter_upwards [hnear] with u hu
    change Q (c u) = Q x
    rw [hu, ht]
    rw [ht]
    have hdiff : c u - c t = ((u : ℝ) - (t : ℝ)) • (y - x) := by
      simp only [c, AffineMap.lineMap_apply_module', sub_smul]
      abel
    rw [hdiff]
    exact (Q x).ker.smul_mem _ hxy
  have hnonempty : S.Nonempty := ⟨0, by simp [S, c]⟩
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  have h1 : (1 : I) ∈ S := hall.symm ▸ mem_univ _
  simpa [S, c] using h1

private theorem normalized_slice_neighborhood {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : E} {U : Set E} {Q : E → E →L[ℝ] V} (hU : IsOpen U) (ha : a ∈ U)
    (hQ : ContinuousOn Q U) (J : V →L[ℝ] E)
    (hJ : ∀ y ∈ U, Function.RightInverse J (Q y))
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ (Q y).ker → Q z = Q y) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, a + J (Q y (y - a)) ∈ U ∧
        Q (a + J (Q y (y - a))) = Q y ∧ a + J (Q y (y - a)) - y ∈ (Q y).ker := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU a ha
  let f := fun y => a + J (Q y (y - a))
  have hf : ContinuousOn f (ball a r) :=
    continuousOn_const.add (J.continuous.comp_continuousOn
      ((hQ.mono hball).clm_apply (continuous_id.sub continuous_const).continuousOn))
  let W := ball a r ∩ f ⁻¹' ball a r
  have hW : IsOpen W := hf.isOpen_inter_preimage isOpen_ball isOpen_ball
  have haW : a ∈ W := by simp [W, f, hr]
  refine ⟨W, hW, haW, fun y hy => hball hy.1, fun y hy => ?_⟩
  have hyU := hball hy.1
  have hfyU := hball hy.2
  have hker : f y - y ∈ (Q y).ker := by
    change Q y (a + J (Q y (y - a)) - y) = 0
    rw [map_sub, map_add, hJ y hyU, map_sub]
    abel
  exact ⟨hfyU, eq_of_sub_mem_ker_of_convex (hQ.mono hball) (convex_ball a r)
    (fun z hz => hleaf z (hball hz)) hy.1 hy.2 hker, hker⟩

def H1 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    let V := EuclideanSpace ℝ (Fin 3)
    letI : DecidableEq E := Classical.decEq E
    let C (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (s : Finset E) := {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}
    AffineIndependent ℝ ((↑) : K.vertices → E) → K.faces.Finite →
    (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    (∀ s ∈ K.faces, s.card = 2 → IsConnected (C (link s))) →
    (∀ s ∈ K.faces, s.card = 3 → ({p : E | {p} ∈ link s} : Set E).ncard = 2) →
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → V,
      (∀ s ∈ star {p}, ∃ a : E →ᴬ[ℝ] V, EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (C (star {p})) ∧ (interior (f '' C (star {p}))).Nonempty) →
    ∃ P : E → Submodule ℝ E,
      ∀ a : K.space, ∃ (s : Finset E) (U : Set E) (J : V →L[ℝ] E) (Q : E → E →L[ℝ] V),
          s ∈ K.faces ∧ (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
          IsOpen U ∧ (a : E) ∈ U ∧ ContDiffOn ℝ ∞ Q U ∧
          (∃ L : ℝ≥0, ∀ x ∈ C (star s), ∀ y ∈ C (star s),
            ‖x - y‖ ≤ L * ‖Q a x - Q a y‖) ∧
          ∀ y ∈ U, Function.RightInverse J (Q y) ∧ (Q y).ker = P y ∧
            ∀ᶠ z in 𝓝 y, z - y ∈ P y → Q z = Q y

def H2 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    let V := EuclideanSpace ℝ (Fin 3)
    letI : DecidableEq E := Classical.decEq E
    K.faces.Finite → (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    (∀ s ∈ K.faces, s.card = 3 →
      ({p : E | {p} ∈ K.faces ∧ Disjoint s {p} ∧ s ∪ {p} ∈ K.faces} : Set E).ncard = 2) →
    ∀ s ∈ K.faces, ∀ a : K.space, (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) →
      ∀ (Q : E → E →L[ℝ] V) (J : V →L[ℝ] E) (W : Set K.space),
        ContDiffAt ℝ ∞ Q (a : E) → Function.RightInverse J (Q a) →
        (let S := ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)
         ∃ L : ℝ≥0, ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖Q a x - Q a y‖) → W ∈ 𝓝 a →
        ∃ c : OpenPartialHomeomorph K.space V, a ∈ c.source ∧ c.source ⊆ W ∧
          ∀ y ∈ c.source, c y = Q y ((y : E) - a)

theorem main : H1 → H2 → OMA.CairnsAtlas.H2 := by
  classical
  intro hfield hchart m K hind hgood
  obtain ⟨hfinite, hpure, he, ht, hv⟩ := hgood
  obtain ⟨P, hP⟩ := hfield m K hind hfinite hpure he ht hv
  let E := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℝ (Fin 3)
  have hcharts (a : K.space) :
      ∃ (c : OpenPartialHomeomorph K.space V) (b : V →ᴬ[ℝ] E) (Q : E → E →L[ℝ] V),
        a ∈ c.source ∧ (∀ z ∈ c.target, ContDiffAt ℝ ∞ Q (b z)) ∧
        ∀ y ∈ c.source, Function.RightInverse b.contLinear (Q y) ∧
          (Q y).ker = P y ∧ Q (b (c y)) = Q y ∧ b (c y) - y ∈ P y := by
    obtain ⟨s, U, J, Q, hs, ha, hU, haU, hQ, hbound, hproj⟩ := hP a
    obtain ⟨W, hW, haW, hWU, hslice⟩ := normalized_slice_neighborhood hU haU hQ.continuousOn J
      (fun y hy => (hproj y hy).1) (fun y hy => by
        rw [(hproj y hy).2.1]
        exact (hproj y hy).2.2)
    have hn : (Subtype.val ⁻¹' W : Set K.space) ∈ 𝓝 a :=
      (hW.preimage continuous_subtype_val).mem_nhds haW
    obtain ⟨c, hc, hsub, hformula⟩ := hchart m K hfinite hpure ht s hs a ha Q J _
      (hQ.contDiffAt (hU.mem_nhds haU)) (hproj a haU).1 hbound hn
    let b : V →ᴬ[ℝ] E := ContinuousAffineMap.const ℝ V (a : E) + J.toContinuousAffineMap
    have hlinear : b.contLinear = J := by
      apply ContinuousLinearMap.ext
      intro z
      change (0 : E) + J z = J z
      exact zero_add _
    have hdata (y : K.space) (hy : y ∈ c.source) :
        b (c y) ∈ U ∧ Q (b (c y)) = Q y ∧ b (c y) - y ∈ (Q y).ker := by
      change (a : E) + J (c y) ∈ U ∧ Q (a + J (c y)) = Q y ∧
        (a : E) + J (c y) - y ∈ (Q y).ker
      rw [hformula y hy]
      exact hslice y (hsub hy)
    refine ⟨c, b, Q, hc, ?_, fun y hy => ?_⟩
    · intro z hz
      have h := (hdata (c.symm z) (c.map_target hz)).1
      rw [c.right_inv hz] at h
      exact hQ.contDiffAt (hU.mem_nhds h)
    · have hyU := hWU (hsub hy)
      obtain ⟨_, heq, hker⟩ := hdata y hy
      rw [(hproj y hyU).2.1] at hker
      exact ⟨hlinear.symm ▸ (hproj y hyU).1, (hproj y hyU).2.1, heq, hker⟩
  choose c b Q hc hQ hspec using hcharts
  dsimp only
  intro M _ e
  let cM := fun i : M => e.transOpenPartialHomeomorph (c (e i))
  refine ⟨cM, fun y => P (e y), fun i => b (e i), fun i => Q (e i), ?_, ?_, ?_⟩
  · intro y
    exact ⟨y, hc (e y)⟩
  · intro i z hz
    exact hQ (e i) z hz
  · intro i y hy
    exact hspec (e i) (e y) hy

end OMA.CairnsLeafCoordinates

end

/- ## FacePlaneGluing -/
section
open Geometry Set
open scoped BigOperators

namespace Fleet.FaceCarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem mem_intrinsicInterior_convexHull_iff_pos {s : Finset E}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → E))
    {w : E → ℝ} (hw : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i • i) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ↔
      ∀ i ∈ s, 0 < w i := by
  classical
  obtain ⟨p, hp⟩ := hs
  let S := affineSpan ℝ (s : Set E)
  let p' : S := ⟨p, subset_affineSpan ℝ (s : Set E) hp⟩
  let : Nonempty (s : Set E) := ⟨⟨p, hp⟩⟩
  let : Nonempty S := ⟨p'⟩
  let e : S.direction ≃ᵃⁱ[ℝ] S := AffineIsometryEquiv.vaddConst ℝ p'
  let f : S.direction →ᵃ[ℝ] E := S.subtype.comp e.toAffineEquiv.toAffineMap
  let v : s → S.direction := fun i => e.symm ⟨i, subset_affineSpan ℝ (s : Set E) i.property⟩
  have hv (i : s) : f (v i) = (i : E) := by
    change (↑(e (e.symm ⟨i, subset_affineSpan ℝ (s : Set E) i.property⟩)) : E) = i
    rw [e.apply_symm_apply]
  have hv' : f ∘ v = ((↑) : s → E) := funext hv
  have hfi : Function.Injective f := S.subtype_injective.comp e.injective
  have hfv : f '' range v = (s : Set E) := by
    rw [← Set.range_comp, hv']
    exact Subtype.range_coe_subtype
  have hpre : range v = e.toAffineEquiv ⁻¹' (((↑) : S → E) ⁻¹' (s : Set E)) := by
    ext z
    change z ∈ range v ↔ f z ∈ (s : Set E)
    constructor
    · rintro ⟨i, rfl⟩
      rw [hv]
      exact i.property
    · intro hz
      exact ⟨⟨f z, hz⟩, hfi (hv ⟨f z, hz⟩)⟩
  let b : AffineBasis s ℝ S.direction := ⟨v, by
    apply AffineIndependent.of_comp f
    rwa [hv'], by
    rw [hpre, ← AffineSubspace.comap_span, affineSpan_coe_preimage_eq_top,
      AffineSubspace.comap_top]⟩
  have hfconv : f ⁻¹' convexHull ℝ (s : Set E) = convexHull ℝ (range b) := by
    change _ = convexHull ℝ (range v)
    calc
      _ = f ⁻¹' (f '' convexHull ℝ (range v)) := by rw [f.image_convexHull, hfv]
      _ = _ := Set.preimage_image_eq _ hfi
  let z := Finset.univ.affineCombination ℝ b (fun i : s => w i)
  have hsum : (∑ i : s, w i) = 1 := (Finset.sum_coe_sort s w).trans hw
  have hfz : f z = ∑ i ∈ s, w i • i := by
    dsimp only [z]
    rw [Finset.map_affineCombination _ _ _ hsum f,
      Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    change (∑ i : s, w i • f (v i)) = _
    simp only [hv]
    exact Finset.sum_coe_sort s (fun i => w i • i)
  rw [← hfz, intrinsicInterior, affineSpan_convexHull]
  change e z ∈ Subtype.val ⁻¹'
    (Subtype.val '' interior (((↑) : S → E) ⁻¹' convexHull ℝ (s : Set E))) ↔ _
  rw [Set.preimage_image_eq _ Subtype.val_injective]
  change z ∈ e.toHomeomorph ⁻¹'
    interior (((↑) : S → E) ⁻¹' convexHull ℝ (s : Set E)) ↔ _
  rw [e.toHomeomorph.preimage_interior]
  change z ∈ interior (f ⁻¹' convexHull ℝ (s : Set E)) ↔ _
  rw [hfconv, b.interior_convexHull]
  change (∀ i : s, 0 < b.coord i z) ↔ _
  have hcoord (i : s) : b.coord i z = w i :=
    b.coord_apply_combination_of_mem (Finset.mem_univ i) hsum
  simp only [hcoord, Subtype.forall]

theorem mem_space_iff_exists_carrierFace {K : SimplicialComplex ℝ E} {x : E} :
    x ∈ K.space ↔
      ∃ s ∈ K.faces, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.1 hx
    obtain ⟨w, hw₀, hw₁, hwx⟩ := Finset.mem_convexHull'.1 hxt
    let s := t.filter fun i => 0 < w i
    have hst : s ⊆ t := Finset.filter_subset _ _
    have hz (i : E) (hi : i ∈ t) (his : i ∉ s) : w i = 0 :=
      le_antisymm (le_of_not_gt fun hh => his (Finset.mem_filter.mpr ⟨hi, hh⟩)) (hw₀ i hi)
    have hws : ∑ i ∈ s, w i = 1 := (Finset.sum_subset hst hz).trans hw₁
    have hxs : ∑ i ∈ s, w i • i = x :=
      (Finset.sum_subset hst fun i hi his => by rw [hz i hi his, zero_smul]).trans hwx
    have hsne : s.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at hws
    have hs := K.down_closed ht hst hsne
    refine ⟨s, hs, ?_⟩
    rw [← hxs]
    exact (mem_intrinsicInterior_convexHull_iff_pos hsne (K.indep hs) hws).2
      (fun i hi => (Finset.mem_filter.1 hi).2)
  · rintro ⟨s, hs, hx⟩
    exact K.convexHull_subset_space hs (intrinsicInterior_subset hx)

theorem exists_carrierFace (K : SimplicialComplex ℝ E) (a : K.space) :
    ∃ s ∈ K.faces, (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) :=
  mem_space_iff_exists_carrierFace.1 a.property

theorem carrierFace_subset {K : SimplicialComplex ℝ E} {s t : Finset E} {x : E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxt : x ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  have hx' : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨intrinsicInterior_subset hx, hxt⟩
  obtain ⟨w, _, hw, hwx⟩ := Finset.mem_convexHull'.1 hx'
  let v : E → ℝ := ((s ∩ t : Finset E) : Set E).indicator w
  have hsub : s ∩ t ⊆ s := Finset.inter_subset_left
  have hv : ∑ i ∈ s, v i = 1 := (Finset.sum_indicator_subset w hsub).trans hw
  have hvx : ∑ i ∈ s, v i • i = x :=
    (Finset.sum_indicator_subset_of_eq_zero w (fun i r => r • i) hsub
      (fun i => zero_smul ℝ i)).trans hwx
  have hvpos := (mem_intrinsicInterior_convexHull_iff_pos
    (K.nonempty_of_mem_faces hs) (K.indep hs) hv).1 (hvx.symm ▸ hx)
  intro i hi
  by_contra hni
  exact (ne_of_gt (hvpos i hi)) (by simp [v, hni])

end Fleet.FaceCarrier

open Set Geometry
open scoped NNReal

namespace Fleet.StarLinear

variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

theorem exists_affineMap_eqOn {S : Set E} (hS : AffineIndependent ℝ ((↑) : S → E))
    (f : E → V) : ∃ A : E →ᵃ[ℝ] V, EqOn f A S := by
  obtain ⟨T, hST, hT, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hS
  let b : AffineBasis T ℝ E :=
    ⟨Subtype.val, hT, by simpa only [Subtype.range_coe] using hspan⟩
  obtain ⟨i⟩ := b.nonempty
  let L := (b.basisOf i).constr ℝ (fun j => f (b j) - f (b i))
  let A : E →ᵃ[ℝ] V :=
    AffineMap.mk' (fun x => L (x - b i) + f (b i)) L (b i) (by simp)
  refine ⟨A, fun x hx => ?_⟩
  let j : T := ⟨x, hST hx⟩
  change f (b j) = L (b j - b i) + f (b i)
  by_cases hji : j = i
  · simp [hji]
  · have hL : L (b j - b i) = f (b j) - f (b i) := by
      simpa [L] using (b.basisOf i).constr_basis ℝ (fun j => f (b j) - f (b i)) ⟨j, hji⟩
    rw [hL, sub_add_cancel]

variable (K : SimplicialComplex ℝ E)

theorem star_subset_star [DecidableEq E] {s s' : Finset E} (h : s ⊆ s') :
    ({t : Finset E | t ∈ K.faces ∧ s' ∪ t ∈ K.faces}) ⊆ ({t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}) := by
  intro t ht
  refine ⟨ht.1, K.down_closed ht.2 (Finset.union_subset_union h Subset.rfl) ?_⟩
  exact (K.nonempty_of_mem_faces ht.1).mono Finset.subset_union_right

theorem carrier_mono {F G : Set (Finset E)} (h : F ⊆ G) : (⋃ t ∈ F, convexHull ℝ (t : Set E)) ⊆ (⋃ t ∈ G, convexHull ℝ (t : Set E)) :=
  fun _ hx => by
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨t, h ht, hxt⟩

theorem exists_affineMap_eqOn_carrier
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) {F : Set (Finset E)}
    (hF : F ⊆ K.faces) {f : E → V}
    (hf : ∀ t ∈ F, ∃ B : E →ᵃ[ℝ] V, EqOn f B (convexHull ℝ (t : Set E))) :
    ∃ A : E →ᵃ[ℝ] V, EqOn f A ((⋃ t ∈ F, convexHull ℝ (t : Set E))) := by
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn hK f
  refine ⟨A, fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
  obtain ⟨B, hB⟩ := hf t ht
  have hAB : EqOn B A (t : Set E) := by
    intro y hy
    exact (hB (subset_convexHull ℝ _ hy)).symm.trans (hA (K.down_closed (hF ht)
      (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty _)))
  exact (hB hxt).trans (AffineMap.eqOn_affineSpan hAB (convexHull_subset_affineSpan _ hxt))

private theorem sum_extend_by_zero {ι M : Type*} [AddCommMonoid M] [DecidableEq ι]
    {s t : Finset ι} (hst : s ⊆ t) (w : ι → M) :
    (∑ z ∈ t, if z ∈ s then w z else 0) = ∑ z ∈ s, w z := by
  calc
    _ = ∑ z ∈ s, if z ∈ s then w z else 0 :=
      (Finset.sum_subset hst fun z _ hz => if_neg hz).symm
    _ = _ := Finset.sum_congr rfl fun z hz => if_pos hz

private theorem secant_rescale {s t : Finset E} {x y : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hy : y ∈ convexHull ℝ (t : Set E))
    (hxy : x ≠ y) :
    ∃ (a b : Finset E) (x' y' : E) (r : ℝ), a ⊆ s ∧ b ⊆ t ∧ Disjoint a b ∧
      x' ∈ convexHull ℝ (a : Set E) ∧ y' ∈ convexHull ℝ (b : Set E) ∧
      0 < r ∧ x - y = r • (x' - y') := by
  classical
  obtain ⟨u, hu₀, hu₁, hux⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨v, hv₀, hv₁, hvy⟩ := Finset.mem_convexHull'.mp hy
  let u' (z : E) := if z ∈ s then u z else 0
  let v' (z : E) := if z ∈ t then v z else 0
  let w (z : E) := u' z - v' z
  let a := (s ∪ t).filter (fun z => 0 < w z)
  let b := (s ∪ t).filter (fun z => w z < 0)
  have hu' (z : E) : 0 ≤ u' z := by
    by_cases hz : z ∈ s <;> simp [u', hz, hu₀]
  have hv' (z : E) : 0 ≤ v' z := by
    by_cases hz : z ∈ t <;> simp [v', hz, hv₀]
  have ha : a ⊆ s := by
    intro z hz
    have hp := (Finset.mem_filter.mp hz).2
    by_contra h
    have hu : u' z = 0 := if_neg h
    exact (not_lt_of_ge (sub_nonpos.mpr ((le_of_eq hu).trans (hv' z)))) hp
  have hb : b ⊆ t := by
    intro z hz
    have hn := (Finset.mem_filter.mp hz).2
    by_contra h
    have hv : v' z = 0 := if_neg h
    exact (not_lt_of_ge (sub_nonneg.mpr ((le_of_eq hv).trans (hu' z)))) hn
  have hab : Disjoint a b := Finset.disjoint_left.mpr fun z ha' hb' =>
    (not_lt_of_ge (le_of_lt (Finset.mem_filter.mp ha').2)) (Finset.mem_filter.mp hb').2
  have hsplit (z : E) :
      (if 0 < w z then w z else 0) - (if w z < 0 then -w z else 0) = w z := by
    by_cases hp : 0 < w z
    · simp [hp, not_lt_of_ge hp.le]
    by_cases hn : w z < 0
    · simp [hp, hn]
    have he : w z = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    simp [he]
  have hmass : (∑ z ∈ a, w z) = ∑ z ∈ b, -w z := by
    apply sub_eq_zero.mp
    simp only [a, b, Finset.sum_filter, ← Finset.sum_sub_distrib, hsplit]
    change (∑ z ∈ s ∪ t, (u' z - v' z)) = 0
    rw [Finset.sum_sub_distrib, sum_extend_by_zero Finset.subset_union_left,
      sum_extend_by_zero Finset.subset_union_right, hu₁, hv₁, sub_self]
  have hvec : (∑ z ∈ a, w z • z) - (∑ z ∈ b, (-w z) • z) = x - y := by
    have hvsplit (z : E) :
        (if 0 < w z then w z • z else 0) - (if w z < 0 then (-w z) • z else 0) =
          w z • z := by
      simpa only [sub_smul, ite_smul, zero_smul] using congrArg (fun c : ℝ => c • z) (hsplit z)
    simp only [a, b, Finset.sum_filter, ← Finset.sum_sub_distrib]
    simp_rw [hvsplit, w, sub_smul]
    rw [Finset.sum_sub_distrib]
    simp only [u', v', ite_smul, zero_smul]
    rw [sum_extend_by_zero Finset.subset_union_left, sum_extend_by_zero Finset.subset_union_right,
      hux, hvy]
  let r := ∑ z ∈ a, w z
  have hr : 0 < r := by
    by_contra hn
    have h := le_of_not_gt hn
    have ha₀ : a = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hne =>
      (not_lt_of_ge h) (Finset.sum_pos (fun z hz => (Finset.mem_filter.mp hz).2) hne)
    have hb₀ : b = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hne => by
      have hp := Finset.sum_pos (fun z hz => neg_pos.mpr (Finset.mem_filter.mp hz).2) hne
      rw [← hmass, ha₀, Finset.sum_empty] at hp
      exact (lt_irrefl 0) hp
    apply hxy (sub_eq_zero.mp _)
    simpa [ha₀, hb₀] using hvec.symm
  let x' := r⁻¹ • ∑ z ∈ a, w z • z
  let y' := r⁻¹ • ∑ z ∈ b, (-w z) • z
  refine ⟨a, b, x', y', r, ha, hb, hab, ?_, ?_, hr, ?_⟩
  · refine Finset.mem_convexHull'.mpr ⟨fun z => r⁻¹ * w z, fun z hz => ?_, ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.mpr hr.le) (le_of_lt (Finset.mem_filter.mp hz).2)
    · rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hr.ne'
    · simp only [x', mul_smul, Finset.smul_sum]
  · refine Finset.mem_convexHull'.mpr ⟨fun z => r⁻¹ * (-w z), fun z hz => ?_, ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.mpr hr.le) (le_of_lt (neg_pos.mpr (Finset.mem_filter.mp hz).2))
    · rw [← Finset.mul_sum, ← hmass]
      exact inv_mul_cancel₀ hr.ne'
    · simp only [y', mul_smul, Finset.smul_sum]
  · dsimp only [x', y']
    rw [← smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, hvec]

section Normed

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_rightInverse_linear_of_nonempty_interior
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] {A : X →ᵃ[ℝ] Y} {S : Set X}
    (hA : (interior (A '' S)).Nonempty) : A.linear.toContinuousLinearMap.HasRightInverse := by
  have htop : (⊤ : AffineSubspace ℝ X).map A = ⊤ := by
    have hspan : affineSpan ℝ (interior (A '' S)) ≤ (⊤ : AffineSubspace ℝ X).map A := by
      apply affineSpan_le.mpr
      intro y hy
      obtain ⟨x, -, rfl⟩ := interior_subset hy
      exact AffineSubspace.mem_map_of_mem A (AffineSubspace.mem_top ℝ X x)
    rw [isOpen_interior.affineSpan_eq_top hA] at hspan
    exact top_unique hspan
  have hsurj : Function.Surjective A := by
    intro y
    have hy : y ∈ (⊤ : AffineSubspace ℝ X).map A := htop.symm ▸ AffineSubspace.mem_top ℝ Y y
    obtain ⟨x, -, hx⟩ := AffineSubspace.mem_map.mp hy
    exact ⟨x, hx⟩
  exact ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
    (A.linear_surjective_iff.mpr hsurj)

theorem norm_sub_le_mul_of_injOn_carrier (K : SimplicialComplex ℝ X) {F : Set (Finset X)}
    (hF : F ⊆ K.faces) (hFfin : F.Finite)
    (hdown : ∀ ⦃s t : Finset X⦄, s ∈ F → t ⊆ s → t.Nonempty → t ∈ F)
    (Q : X →L[ℝ] Y) (hQ : InjOn Q ((⋃ t ∈ F, convexHull ℝ (t : Set X)))) :
    ∃ L : ℝ≥0, ∀ x ∈ (⋃ t ∈ F, convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ F, convexHull ℝ (t : Set X)), ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  classical
  let pairs : Set (Finset X × Finset X) := {p ∈ F ×ˢ F | Disjoint p.1 p.2}
  let faceHull (s : Finset X) := convexHull ℝ (s : Set X)
  let diff (p : X × X) := p.1 - p.2
  let D := ⋃ p ∈ pairs, diff '' (faceHull p.1 ×ˢ faceHull p.2)
  have hD : IsCompact D :=
    ((hFfin.prod hFfin).subset (sep_subset ..)).isCompact_biUnion fun p _ =>
      (((Finset.finite_toSet p.1).isCompact_convexHull ℝ).prod
        ((Finset.finite_toSet p.2).isCompact_convexHull ℝ)).image
          (continuous_fst.sub continuous_snd)
  have hDpos : ∀ d ∈ D, 0 < ‖Q d‖ := by
    intro d hd
    obtain ⟨⟨s, t⟩, ⟨⟨hs, ht⟩, hst⟩, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩⟩ := mem_iUnion₂.mp hd
    apply norm_pos_iff.mpr
    intro hzero
    have hQxy : Q x = Q y := sub_eq_zero.mp (by simpa only [diff, map_sub] using hzero)
    have hxy : x = y :=
      hQ (mem_iUnion₂.mpr ⟨s, hs, hx⟩) (mem_iUnion₂.mpr ⟨t, ht, hy⟩) hQxy
    subst y
    change Disjoint s t at hst
    have h := K.inter_subset_convexHull (hF hs) (hF ht) ⟨hx, hy⟩
    simp [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp hst] at h
  obtain ⟨ε, hε, hεD⟩ := hD.exists_forall_le' Q.continuous.norm.continuousOn hDpos
  obtain ⟨M, hM, hMD⟩ := hD.isBounded.exists_pos_norm_le
  let L : ℝ≥0 := ⟨M / ε, (div_pos hM hε).le⟩
  refine ⟨L, fun x hx y hy => ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
  obtain ⟨a, b, x', y', r, ha, hb, hab, hx', hy', hr, hsec⟩ := secant_rescale hxs hyt hxy
  have haF : a ∈ F := hdown hs ha (by simpa using convexHull_nonempty_iff.mp ⟨x', hx'⟩)
  have hbF : b ∈ F := hdown ht hb (by simpa using convexHull_nonempty_iff.mp ⟨y', hy'⟩)
  have hd : x' - y' ∈ D := mem_iUnion₂.mpr
    ⟨(a, b), ⟨⟨haF, hbF⟩, hab⟩, ⟨(x', y'), ⟨hx', hy'⟩, rfl⟩⟩
  have hsecbound : ‖x' - y'‖ ≤ (L : ℝ) * ‖Q (x' - y')‖ :=
    (hMD _ hd).trans <| by
      dsimp [L]
      calc
        M = M / ε * ε := (div_mul_cancel₀ M hε.ne').symm
        _ ≤ M / ε * ‖Q (x' - y')‖ := mul_le_mul_of_nonneg_left (hεD _ hd) (div_pos hM hε).le
  rw [← map_sub, hsec, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hr.le]
  simpa only [mul_left_comm (L : ℝ) r] using mul_le_mul_of_nonneg_left hsecbound hr.le

theorem exists_star_projection (K : SimplicialComplex ℝ X) [DecidableEq X]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → X)) (hfin : K.faces.Finite)
    {p : X} {f : X → Y}
    (haff : ∀ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), ∃ B : X →ᵃ[ℝ] Y, EqOn f B (convexHull ℝ (t : Set X)))
    (hinj : InjOn f ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X))))
    (hint : (interior (f '' (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))).Nonempty) :
    ∃ (Q : X →L[ℝ] Y) (J : Y →L[ℝ] X) (L : ℝ≥0), Function.RightInverse J Q ∧
      ∀ x ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  have hsub : ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}) ⊆ K.faces := fun _ ht => ht.1
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_carrier K hK hsub haff
  let Q := A.linear.toContinuousLinearMap
  have hintA : (interior (A '' (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))).Nonempty := hA.image_eq ▸ hint
  obtain ⟨J, hJ⟩ := exists_rightInverse_linear_of_nonempty_interior hintA
  have hQ : InjOn Q ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X))) := by
    intro x hx y hy hxy
    apply hinj hx hy
    rw [hA hx, hA hy, ← sub_eq_zero, ← vsub_eq_sub, ← A.linearMap_vsub]
    change Q (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hdown ⦃s t : Finset X⦄ (hs : s ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces})) (hst : t ⊆ s) (ht : t.Nonempty) :
      t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}) :=
    ⟨K.down_closed hs.1 hst ht, K.down_closed hs.2 (Finset.union_subset_union_right hst)
      (ht.mono Finset.subset_union_right)⟩
  obtain ⟨L, hL⟩ := norm_sub_le_mul_of_injOn_carrier K hsub (hfin.subset hsub) hdown Q hQ
  exact ⟨Q, J, L, hJ, hL⟩

theorem exists_face_projection (K : SimplicialComplex ℝ X) [DecidableEq X]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → X)) (hfin : K.faces.Finite)
    (hvertex : ∀ p : X, {p} ∈ K.faces → ∃ f : X → Y,
      (∀ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), ∃ B : X →ᵃ[ℝ] Y, EqOn f B (convexHull ℝ (t : Set X))) ∧
        InjOn f ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X))) ∧ (interior (f '' (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))).Nonempty)
    {s : Finset X} (hs : s ∈ K.faces) :
    ∃ (Q : X →L[ℝ] Y) (J : Y →L[ℝ] X) (L : ℝ≥0), Function.RightInverse J Q ∧
      ∀ x ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces hs
  have hps : {p} ⊆ s := Finset.singleton_subset_iff.mpr hp
  have hpK := K.down_closed hs hps (Finset.singleton_nonempty p)
  obtain ⟨f, haff, hinj, hint⟩ := hvertex p hpK
  obtain ⟨Q, J, L, hJ, hL⟩ := exists_star_projection K hK hfin haff hinj hint
  have hsub := carrier_mono (star_subset_star K hps)
  exact ⟨Q, J, L, hJ, fun x hx y hy => hL x (hsub hx) y (hsub hy)⟩

theorem norm_sub_le_mul_of_injOn_star (K : SimplicialComplex ℝ X) [DecidableEq X]
    (hfin : K.faces.Finite) {s : Finset X} (Q : X →L[ℝ] Y)
    (hQ : InjOn Q ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))) :
    ∃ L : ℝ≥0, ∀ x ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)),
      ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  have hsub : ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}) ⊆ K.faces := fun _ ht => ht.1
  apply norm_sub_le_mul_of_injOn_carrier K hsub (hfin.subset hsub) _ Q hQ
  intro t u ht htu hu
  exact ⟨K.down_closed ht.1 htu hu, K.down_closed ht.2 (Finset.union_subset_union_right htu)
    (hu.mono Finset.subset_union_right)⟩

end Normed

end Fleet.StarLinear

open Set Filter Function Geometry Metric
open scoped ContDiff NNReal Topology

namespace Fleet.Planes

theorem exists_normalized_field {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    {P : E → Submodule ℝ E} {a : E} {U : Set E} {R : E → E →L[ℝ] V}
    (hU : IsOpen U) (ha : a ∈ U) (hR : ContDiffOn ℝ ∞ R U) (hsurj : Surjective (R a))
    (hker : ∀ y ∈ U, (R y).ker = P y)
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ P y → P z = P y) :
    ∃ (U' : Set E) (J : V →L[ℝ] E) (Q : E → E →L[ℝ] V),
      IsOpen U' ∧ a ∈ U' ∧ ContDiffOn ℝ ∞ Q U' ∧ Q a = R a ∧
      ∀ y ∈ U', RightInverse J (Q y) ∧ (Q y).ker = P y ∧
        ∀ᶠ z in 𝓝 y, z - y ∈ P y → Q z = Q y := by
  obtain ⟨J, hJ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj
  let B := fun y => (R y).comp J
  have hB : ContDiffOn ℝ ∞ B U := hR.clm_comp contDiffOn_const
  have hBa : B a = 1 := by
    ext v
    exact hJ v
  let U' := U ∩ B ⁻¹' {b | IsUnit b}
  have hU' : IsOpen U' := hB.continuousOn.isOpen_inter_preimage hU Units.isOpen
  have ha' : a ∈ U' := ⟨ha, by change IsUnit (B a); rw [hBa]; exact isUnit_one⟩
  have hB' (y) (hy : y ∈ U') : (B y).IsInvertible := by
    have h : IsUnit (B y) := hy.2
    obtain ⟨u, hu⟩ := h
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ V u, hu⟩
  let Q := fun y => (B y).inverse.comp (R y)
  have hQ : ContDiffOn ℝ ∞ Q U' := by
    intro y hy
    have hny := hU.mem_nhds hy.1
    exact (((hB' y hy).contDiffAt_map_inverse.comp y (hB.contDiffAt hny)).clm_comp
      (hR.contDiffAt hny)).contDiffWithinAt
  have hbase : Q a = R a := by
    change (B a).inverse.comp (R a) = R a
    rw [hBa]
    simp [ContinuousLinearMap.one_def]
  have hright (y) (hy : y ∈ U') : RightInverse J (Q y) := fun v =>
    (hB' y hy).inverse_apply_self v
  have hQker (y) (hy : y ∈ U') : (Q y).ker = P y := by
    rw [← hker y hy.1]
    ext x
    change (B y).inverse (R y x) = 0 ↔ R y x = 0
    constructor
    · intro hx
      simpa only [(hB' y hy).self_apply_inverse, map_zero] using congrArg (B y) hx
    · intro hx
      rw [hx, map_zero]
  refine ⟨U', J, Q, hU', ha', hQ, hbase, fun y hy => ⟨hright y hy, hQker y hy, ?_⟩⟩
  filter_upwards [hU'.mem_nhds hy, hleaf y hy.1] with z hz hP
  intro hzy
  have hPzy := hP hzy
  ext v
  have hv : v - J (Q y v) ∈ (Q y).ker := by
    change Q y (v - J (Q y v)) = 0
    rw [map_sub, hright y hy, sub_self]
  have hvz : v - J (Q y v) ∈ (Q z).ker := by
    rwa [hQker z hz, hPzy, ← hQker y hy]
  change Q z (v - J (Q y v)) = 0 at hvz
  rw [map_sub, hright z hz] at hvz
  exact sub_eq_zero.mp hvz

theorem injOn_closedStar_of_local {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {a : E} {s : Finset E} {r : ℝ} {q : E →L[ℝ] V}
    (ha : a ∈ convexHull ℝ (s : Set E)) (hr : 0 < r)
    (hinj : InjOn q (K.space ∩ ball a r)) :
    InjOn q (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)) := by
  intro x hx y hy hxy
  simp only [mem_iUnion, mem_ofPred_eq] at hx hy
  obtain ⟨t, ⟨_, ht⟩, hx⟩ := hx
  obtain ⟨u, ⟨_, hu⟩, hy⟩ := hy
  have hnear (z : E) : ∀ᶠ c : ℝ in 𝓝 0, AffineMap.lineMap a z c ∈ ball a r := by
    have hcont : Continuous (fun c : ℝ => AffineMap.lineMap a z c) := by
      simp only [AffineMap.lineMap_apply_module']
      fun_prop
    have ht : Tendsto (fun c : ℝ => AffineMap.lineMap a z c) (𝓝 0)
        (𝓝 (AffineMap.lineMap a z (0 : ℝ))) := hcont.continuousAt
    rw [AffineMap.lineMap_apply_zero] at ht
    exact ht.eventually (show ∀ᶠ w in 𝓝 a, w ∈ ball a r from isOpen_ball.mem_nhds (mem_ball_self hr))
  have hboth := (hnear x).and (hnear y)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hboth
  let c := min (ε / 2) (1 / 2)
  have hc : 0 < c := lt_min (half_pos hε) (by norm_num)
  have hcε : c ∈ ball (0 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.le, (min_le_right _ _).trans (by norm_num)⟩
  have hmem (w : Finset E) (hw : s ∪ w ∈ K.faces) (z : E) (hz : z ∈ convexHull ℝ (w : Set E)) :
      AffineMap.lineMap a z c ∈ K.space := by
    apply K.convexHull_subset_space hw
    apply (convex_convexHull ℝ _).lineMap_mem _ _ hcI
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) ha
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right) hz
  have heq : AffineMap.lineMap a x c = AffineMap.lineMap a y c := by
    apply hinj ⟨hmem t ht x hx, (hεsub hcε).1⟩ ⟨hmem u hu y hy, (hεsub hcε).2⟩
    simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, hxy]
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', add_right_cancel_iff] at heq
  have hdiff : x - a = y - a := (smul_right_injective E hc.ne') heq
  calc
    x = (x - a) + a := (sub_add_cancel x a).symm
    _ = (y - a) + a := congrArg (· + a) hdiff
    _ = y := sub_add_cancel y a

theorem codim_and_secants_of_projection {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set E} (q : E →L[ℝ] V) (hsurj : Surjective q) (hinj : InjOn q S) :
    Module.finrank ℝ q.ker + Module.finrank ℝ V = Module.finrank ℝ E ∧
      ∀ x ∈ S, ∀ y ∈ S, x - y ∈ q.ker → x = y := by
  constructor
  · have htop : LinearMap.range q.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have h := q.toLinearMap.finrank_range_add_finrank_ker
    rw [htop, finrank_top, add_comm] at h
    exact h
  · intro x hx y hy hxy
    apply hinj hx hy
    change q (x - y) = 0 at hxy
    rwa [map_sub, sub_eq_zero] at hxy

end Fleet.Planes

namespace OMA.CairnsPlaneField

def H1 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S (s : Finset E) := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)
    let G (s : Finset E) := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S s, ∀ y ∈ S s, x - y ∈ P → x = y}
    let topo (s : Finset E) : TopologicalSpace (G s) :=
      TopologicalSpace.induced (fun P : G s => P.val.starProjection) inferInstance
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    AffineIndependent ℝ ((↑) : K.vertices → E) → K.faces.Finite →
    (∀ s ∈ K.faces, s.card ≤ 4) →
    (∀ s ∈ K.faces, s.card = 2 →
      IsConnected (⋃ t ∈ link s, convexHull ℝ (t : Set E))) →
    (∀ s ∈ K.faces, s.card = 3 → ({p : E | {p} ∈ link s} : Set E).ncard = 2) →
    ∀ s ∈ K.faces, 2 ≤ s.card → @ContractibleSpace (G s) (topo s)

def H2 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S (s : Finset E) := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)
    let G (s : Finset E) := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S s, ∀ y ∈ S s, x - y ∈ P → x = y}
    let topo (s : Finset E) : TopologicalSpace (G s) :=
      TopologicalSpace.induced (fun P : G s => P.val.starProjection) inferInstance
    let V := EuclideanSpace ℝ (Fin 3)
    K.faces.Finite → (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    (∀ s ∈ K.faces, s.card = 1 → Nonempty (G s)) →
    (∀ s ∈ K.faces, 2 ≤ s.card → @ContractibleSpace (G s) (topo s)) →
    ∃ P : E → Submodule ℝ E,
      ∀ a : K.space, ∃ (U : Set E) (R : E → E →L[ℝ] V) (r : ℝ),
        IsOpen U ∧ (a : E) ∈ U ∧ ContDiffOn ℝ ∞ R U ∧ Function.Surjective (R a) ∧
        0 < r ∧ InjOn (R a) (K.space ∩ ball (a : E) r) ∧
        (∀ y ∈ U, (R y).ker = P y) ∧
        (∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ P y → P z = P y)

theorem main : H1 → H2 → OMA.CairnsLeafCoordinates.H1 := by
  classical
  intro hcontract hglue m K
  dsimp only
  intro hind hfinite hpure hedges htriangles hvertices
  let : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  have hsmall (s : Finset (EuclideanSpace ℝ (Fin m))) (hs : s ∈ K.faces) : s.card ≤ 4 := by
    obtain ⟨t, _, hst, hcard⟩ := hpure s hs
    exact hcard ▸ Finset.card_le_card hst
  have hfield := hglue m K hfinite hpure (by
    intro s hs _
    obtain ⟨Q, J, L, hJ, hL⟩ := Fleet.StarLinear.exists_face_projection
      (Y := EuclideanSpace ℝ (Fin 3)) K hind hfinite (by
        intro p hp
        obtain ⟨f, haff, hinj, hint⟩ := hvertices p hp
        refine ⟨f, ?_, hinj, hint⟩
        intro t ht
        obtain ⟨A, hA⟩ := haff t ht
        exact ⟨A.toAffineMap, hA⟩) hs
    have hi : InjOn Q (⋃ t ∈ {t : Finset (EuclideanSpace ℝ (Fin m)) | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
        convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin m)))) := by
      intro x hx y hy hxy
      have h := hL x hx y hy
      exact sub_eq_zero.mp (norm_eq_zero.mp
        (le_antisymm (by simpa [hxy] using h) (norm_nonneg _)))
    have h := Fleet.Planes.codim_and_secants_of_projection Q hJ.surjective hi
    exact ⟨⟨Q.ker, by simpa only [finrank_euclideanSpace_fin] using h.1, h.2⟩⟩)
    (hcontract m K hind hfinite hsmall hedges htriangles)
  obtain ⟨P, hP⟩ := hfield
  refine ⟨P, ?_⟩
  intro a
  obtain ⟨s, hs, hsa⟩ := Fleet.FaceCarrier.exists_carrierFace K a
  obtain ⟨U, R, r, hU, ha, hR, hsurj, hr, hlocal, hker, hleaf⟩ := hP a
  obtain ⟨U', J, Q, hU', ha', hQ, hbase, hprops⟩ :=
    Fleet.Planes.exists_normalized_field hU ha hR hsurj hker hleaf
  have hstar := Fleet.Planes.injOn_closedStar_of_local (intrinsicInterior_subset hsa) hr hlocal
  have hb := Fleet.StarLinear.norm_sub_le_mul_of_injOn_star K hfinite (s := s) (R a) hstar
  refine ⟨s, U', J, Q, hs, hsa, hU', ha', hQ, ?_, hprops⟩
  rwa [hbase]

end OMA.CairnsPlaneField

end

/- ## Reembed -/
section
open Set Geometry

namespace OMA.Helpers

lemma image_image_eq {E F : Type*} [DecidableEq E] [DecidableEq F] {iota : E → F} {A : F → E}
    {V : Set E} (hA : ∀ v ∈ V, A (iota v) = v) {s : Finset E} (hs : (s : Set E) ⊆ V) :
    (s.image iota).image A = s := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := s)]
  exact Finset.image_congr (fun v hv => hA v (hs hv))

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma face_subset_vertices {K : SimplicialComplex ℝ E} {s : Finset E} (hs : s ∈ K.faces) :
    (s : Set E) ⊆ K.vertices := fun v hv =>
  K.down_closed hs (Finset.singleton_subset_iff.2 hv) (Finset.singleton_nonempty v)

noncomputable def reembed [DecidableEq F] (K : SimplicialComplex ℝ E) (iota : E → F)
    (hind : AffineIndependent ℝ (Subtype.val : ↥(iota '' K.vertices) → F)) :
    SimplicialComplex ℝ F :=
  SimplicialComplex.ofAffineIndependent (K.toPreAbstractSimplicialComplex.map iota)
    (hind.mono (by
      intro x hx
      simp only [Set.mem_iUnion, Finset.mem_coe] at hx
      obtain ⟨s, ⟨s', hs', rfl⟩, hx⟩ := hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨v, face_subset_vertices hs' hv, rfl⟩))

variable [DecidableEq E] [DecidableEq F] {K : SimplicialComplex ℝ E} {iota : E → F}
  {hind : AffineIndependent ℝ (Subtype.val : ↥(iota '' K.vertices) → F)} {A : F →L[ℝ] E}

lemma mem_reembed_faces_iff (hA : ∀ v ∈ K.vertices, A (iota v) = v) {s : Finset E}
    (hs : (s : Set E) ⊆ K.vertices) :
    s.image iota ∈ (reembed K iota hind).faces ↔ s ∈ K.faces := by
  constructor
  · rintro ⟨u, hu, hus⟩
    have hus' : u.image iota = s.image iota := hus
    have h1 := image_image_eq hA (face_subset_vertices hu)
    rw [hus', image_image_eq hA hs] at h1
    rw [h1]; exact hu
  · intro h; exact ⟨s, h, rfl⟩

omit [DecidableEq E] in
lemma image_convexHull_image (hA : ∀ v ∈ K.vertices, A (iota v) = v) {s : Finset E}
    (hs : (s : Set E) ⊆ K.vertices) :
    A '' convexHull ℝ ↑(s.image iota) = convexHull ℝ ↑s := by
  have h := (A : F →ₗ[ℝ] E).image_convexHull (↑(s.image iota) : Set F)
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [h, Finset.coe_image, Set.image_image, Set.image_congr (g := fun v => v)
    (fun v hv => hA v (hs hv)), Set.image_id']

omit [DecidableEq E] in
lemma injOn_convexHull_image (hA : ∀ v ∈ K.vertices, A (iota v) = v) {s : Finset E}
    (hs : s ∈ K.faces) : InjOn A (convexHull ℝ ↑(s.image iota)) := by
  intro x hx y hy hxy
  have hsV := face_subset_vertices hs
  have hinj : Set.InjOn iota ↑s := fun a ha b hb hab => by
    rw [← hA a (hsV ha), ← hA b (hsV hb), hab]
  rw [Finset.mem_convexHull'] at hx hy
  obtain ⟨w, -, hw1, rfl⟩ := hx
  obtain ⟨u, -, hu1, rfl⟩ := hy
  simp only [Finset.sum_image hinj, map_sum, map_smul] at hw1 hu1 hxy ⊢
  have hxy' : ∑ v ∈ s, w (iota v) • v = ∑ v ∈ s, u (iota v) • v := by
    calc ∑ v ∈ s, w (iota v) • v = ∑ v ∈ s, w (iota v) • A (iota v) :=
          Finset.sum_congr rfl (fun v hv => by rw [hA v (hsV hv)])
      _ = ∑ v ∈ s, u (iota v) • A (iota v) := hxy
      _ = ∑ v ∈ s, u (iota v) • v := Finset.sum_congr rfl (fun v hv => by rw [hA v (hsV hv)])
  have key := (K.indep hs).eq_of_sum_eq_sum_subtype (w₁ := fun v => w (iota v))
    (w₂ := fun v => u (iota v)) (by rw [hw1, hu1]) hxy'
  exact Finset.sum_congr rfl (fun v hv => by rw [key v hv])

lemma injOn_space (hA : ∀ v ∈ K.vertices, A (iota v) = v) :
    InjOn A (reembed K iota hind).space := by
  intro x hx y hy hxy
  rw [SimplicialComplex.mem_space_iff] at hx hy
  obtain ⟨_, ⟨s, hs, rfl⟩, hx⟩ := hx
  obtain ⟨_, ⟨t, ht, rfl⟩, hy⟩ := hy
  have hsV := face_subset_vertices hs
  have htV := face_subset_vertices ht
  have hAx : A x ∈ convexHull ℝ (s : Set E) := by
    rw [← image_convexHull_image hA hsV]; exact ⟨x, hx, rfl⟩
  have hAy : A y ∈ convexHull ℝ (t : Set E) := by
    rw [← image_convexHull_image hA htV]; exact ⟨y, hy, rfl⟩
  have hint : A x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hs ht ⟨hAx, hxy ▸ hAy⟩
  have hstV : ((s ∩ t : Finset E) : Set E) ⊆ K.vertices :=
    (Finset.coe_subset.2 Finset.inter_subset_left).trans hsV
  rw [← image_convexHull_image hA hstV] at hint
  obtain ⟨z, hz, hzx⟩ := hint
  have hz1 : z ∈ convexHull ℝ ↑(s.image iota) :=
    convexHull_mono (Finset.coe_subset.2 (Finset.image_subset_image Finset.inter_subset_left)) hz
  have hz2 : z ∈ convexHull ℝ ↑(t.image iota) :=
    convexHull_mono (Finset.coe_subset.2 (Finset.image_subset_image Finset.inter_subset_right)) hz
  have e1 : z = x := injOn_convexHull_image hA hs hz1 hx hzx
  have e2 : z = y := injOn_convexHull_image hA ht hz2 hy (hzx.trans hxy)
  exact e1.symm.trans e2

omit [DecidableEq E] in
lemma image_carrier (hA : ∀ v ∈ K.vertices, A (iota v) = v) {G : Set (Finset E)}
    (hG : G ⊆ K.faces) :
    A '' (⋃ s ∈ (fun s => s.image iota) '' G, convexHull ℝ (s : Set F)) =
      ⋃ s ∈ G, convexHull ℝ (s : Set E) := by
  rw [Set.biUnion_image, Set.image_iUnion₂]
  exact Set.iUnion₂_congr (fun s hs => image_convexHull_image hA (face_subset_vertices (hG hs)))

omit [DecidableEq E] in
lemma image_space (hA : ∀ v ∈ K.vertices, A (iota v) = v) :
    A '' (reembed K iota hind).space = K.space :=
  image_carrier hA subset_rfl

omit [DecidableEq E] in
lemma isCompact_space (hfin : K.faces.Finite) : IsCompact (reembed K iota hind).space := by
  refine (hfin.image _).isCompact_biUnion (fun s _ => ?_)
  exact s.finite_toSet.isCompact_convexHull ℝ

omit [DecidableEq E] [DecidableEq F] in
lemma injOn_iota (hA : ∀ v ∈ K.vertices, A (iota v) = v) : InjOn iota K.vertices :=
  fun a ha b hb hab => by rw [← hA a ha, ← hA b hb, hab]

lemma reembed_link (hA : ∀ v ∈ K.vertices, A (iota v) = v) {t : Finset E} (ht : t ∈ K.faces) :
    {u | u ∈ (reembed K iota hind).faces ∧ Disjoint (t.image iota) u ∧
        t.image iota ∪ u ∈ (reembed K iota hind).faces} =
      (fun s => s.image iota) '' {u | u ∈ K.faces ∧ Disjoint t u ∧ t ∪ u ∈ K.faces} := by
  have htV := face_subset_vertices ht
  ext u
  constructor
  · rintro ⟨⟨u', hu', rfl⟩, hdisj, hunion⟩
    have hu'V := face_subset_vertices hu'
    have hU : ((t ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union]; exact Set.union_subset htV hu'V
    refine ⟨u', ⟨hu', Disjoint.of_image_finset hdisj, ?_⟩, rfl⟩
    rw [← mem_reembed_faces_iff (hind := hind) hA hU, Finset.image_union]
    exact hunion
  · rintro ⟨u', ⟨hu', hdisj, hunion⟩, rfl⟩
    have hu'V := face_subset_vertices hu'
    have hU : ((t ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union]; exact Set.union_subset htV hu'V
    refine ⟨⟨u', hu', rfl⟩, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx1
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 hx2
      have hba : b = a := by rw [← hA b (hu'V hb), hab, hA a (htV ha)]
      exact Finset.disjoint_left.1 hdisj ha (hba ▸ hb)
    · show t.image iota ∪ u'.image iota ∈ (reembed K iota hind).faces
      rw [← Finset.image_union]
      exact (mem_reembed_faces_iff hA hU).2 hunion

lemma reembed_star (hA : ∀ v ∈ K.vertices, A (iota v) = v) {p : E} (hp : p ∈ K.vertices) :
    {u | u ∈ (reembed K iota hind).faces ∧ {iota p} ∪ u ∈ (reembed K iota hind).faces} =
      (fun s => s.image iota) '' {u | u ∈ K.faces ∧ {p} ∪ u ∈ K.faces} := by
  ext u
  constructor
  · rintro ⟨⟨u', hu', rfl⟩, hunion⟩
    have hU : (({p} ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union, Finset.coe_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.2 hp) (face_subset_vertices hu')
    refine ⟨u', ⟨hu', ?_⟩, rfl⟩
    rw [← mem_reembed_faces_iff (hind := hind) hA hU, Finset.image_union, Finset.image_singleton]
    exact hunion
  · rintro ⟨u', ⟨hu', hunion⟩, rfl⟩
    have hU : (({p} ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union, Finset.coe_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.2 hp) (face_subset_vertices hu')
    refine ⟨⟨u', hu', rfl⟩, ?_⟩
    show {iota p} ∪ u'.image iota ∈ (reembed K iota hind).faces
    rw [← Finset.image_singleton iota p, ← Finset.image_union]
    exact (mem_reembed_faces_iff hA hU).2 hunion

lemma reembed_link_vertices (hA : ∀ v ∈ K.vertices, A (iota v) = v) {t : Finset E}
    (ht : t ∈ K.faces) :
    {q : F | {q} ∈ {u | u ∈ (reembed K iota hind).faces ∧ Disjoint (t.image iota) u ∧
        t.image iota ∪ u ∈ (reembed K iota hind).faces}} =
      iota '' {q : E | {q} ∈ {u | u ∈ K.faces ∧ Disjoint t u ∧ t ∪ u ∈ K.faces}} := by
  rw [reembed_link hA ht]
  ext q
  constructor
  · rintro ⟨u', hu', hq⟩
    have hq' : u'.image iota = {q} := hq
    have h1 := image_image_eq hA (face_subset_vertices hu'.1)
    rw [hq', Finset.image_singleton] at h1
    refine ⟨A q, ?_, ?_⟩
    · show ({A q} : Finset E) ∈ {u | u ∈ K.faces ∧ Disjoint t u ∧ t ∪ u ∈ K.faces}
      rw [h1]; exact hu'
    · have h2 : ({iota (A q)} : Finset F) = {q} := by
        rw [← Finset.image_singleton, h1, hq']
      exact Finset.singleton_injective h2
  · rintro ⟨q', hq', rfl⟩
    exact ⟨{q'}, hq', Finset.image_singleton iota q'⟩

omit [DecidableEq E] in
lemma carrier_subset_space {G : Set (Finset E)} (hG : G ⊆ K.faces) :
    (⋃ s ∈ (fun s => s.image iota) '' G, convexHull ℝ (s : Set F)) ⊆
      (reembed K iota hind).space := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨_, ⟨u, hu, rfl⟩, hx⟩ := hx
  exact SimplicialComplex.mem_space_iff.2 ⟨_, ⟨u, hG hu, rfl⟩, hx⟩

end Generic

section Topo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

lemma homeomorph_of_injOn {f : X → Y} {S : Set X} {T : Set Y} (hS : IsCompact S)
    (hf : Continuous f) (hinj : InjOn f S) (himg : f '' S = T) : Nonempty (T ≃ₜ S) := by
  have hbij : BijOn f S T := ⟨fun x hx => himg ▸ ⟨x, hx, rfl⟩, hinj, himg ▸ subset_rfl⟩
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (hbij.equiv f) :=
    (hf.comp continuous_subtype_val).subtype_mk _
  exact ⟨(hc.homeoOfEquivCompactToT2).symm⟩

lemma isConnected_of_injOn {f : X → Y} {S U : Set X} (hS : IsCompact S)
    (hf : Continuous f) (hinj : InjOn f S) (hU : U ⊆ S) (h : IsConnected (f '' U)) :
    IsConnected U := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let g : S → Y := fun x => f x
  have hg : Continuous g := hf.comp continuous_subtype_val
  have hginj : Function.Injective g := fun a b hab => Subtype.ext (hinj a.2 b.2 hab)
  have hind : Topology.IsInducing g := (hg.isClosedEmbedding hginj).isInducing
  let U' : Set S := Subtype.val ⁻¹' U
  have hU' : Subtype.val '' U' = U := by
    simp only [U', Subtype.image_preimage_coe]; exact Set.inter_eq_right.2 hU
  have hgU : g '' U' = f '' U := by
    rw [← hU', Set.image_image]
  refine ⟨?_, ?_⟩
  · obtain ⟨y, x, hx, -⟩ := h.nonempty
    exact ⟨x, hx⟩
  · have h1 : IsPreconnected U' := by
      rw [← hind.isPreconnected_image, hgU]; exact h.isPreconnected
    rw [← hU']
    exact h1.image _ continuous_subtype_val.continuousOn

end Topo

lemma exists_reembedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set E)
    (hV : V.Finite) :
    ∃ (m : ℕ) (iota : E → EuclideanSpace ℝ (Fin m)) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] E),
      (∀ v ∈ V, A (iota v) = v) ∧
      AffineIndependent ℝ (Subtype.val : ↥(iota '' V) → EuclideanSpace ℝ (Fin m)) := by
  classical
  have : Finite V := hV.to_subtype
  let eV : V ≃ Fin (Nat.card V) := Finite.equivFin V
  let b := (EuclideanSpace.basisFun (Fin (Nat.card V)) ℝ).toBasis
  refine ⟨Nat.card V, fun v => if hv : v ∈ V then b (eV ⟨v, hv⟩) else 0,
    LinearMap.toContinuousLinearMap (b.constr ℝ (fun j => (eV.symm j : E))), ?_, ?_⟩
  · intro v hv
    simp only [hv, dite_true]
    rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.constr_basis, Equiv.symm_apply_apply]
  · refine b.linearIndependent.affineIndependent.range.mono ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨eV ⟨v, hv⟩, by simp [hv]⟩

def Good (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
    let carrier (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    K.faces.Finite ∧ (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
    (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
    (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → EuclideanSpace ℝ (Fin 3),
      (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3), EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty)

theorem main_thm (n : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : Good n K) :
    ∃ (m : ℕ) (L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
      AffineIndependent ℝ ((↑) : L.vertices → EuclideanSpace ℝ (Fin m)) ∧
      Good m L ∧ Nonempty (K.space ≃ₜ L.space) := by
  obtain ⟨hfin, h4, hconn, htri, hchart⟩ := hK
  have hVfin : K.vertices.Finite := by
    rw [SimplicialComplex.vertices_eq]
    exact hfin.biUnion (fun s _ => s.finite_toSet)
  obtain ⟨m, iota, A, hA, hind⟩ := exists_reembedding K.vertices hVfin
  let : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
  refine ⟨m, reembed K iota hind, ?_, ?_, ?_⟩
  · refine hind.mono ?_
    intro q hq
    obtain ⟨u, hu, hq⟩ := hq
    have hq' : u.image iota = {q} := hq
    have hmem : q ∈ u.image iota := by rw [hq']; exact Finset.mem_singleton_self q
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hmem
    exact ⟨v, face_subset_vertices hu hv, rfl⟩
  · dsimp only [Good]
    refine ⟨hfin.image _, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hst, hcard⟩ := h4 s hs
      refine ⟨t.image iota, ⟨t, ht, rfl⟩, Finset.image_subset_image hst, ?_⟩
      rw [Finset.card_image_of_injOn ((injOn_iota hA).mono (face_subset_vertices ht))]
      exact hcard
    · rintro _ ⟨t, ht, rfl⟩ hcard
      beta_reduce at hcard ⊢
      have hcard' : t.card = 2 := by
        rw [← Finset.card_image_of_injOn ((injOn_iota hA).mono (face_subset_vertices ht))]
        exact hcard
      rw [reembed_link hA ht]
      refine isConnected_of_injOn (isCompact_space (hind := hind) hfin) A.continuous
        (injOn_space (hind := hind) hA) (carrier_subset_space (hind := hind) (fun u hu => hu.1)) ?_
      rw [image_carrier hA (fun u hu => hu.1)]
      exact hconn t ht hcard'
    · rintro _ ⟨t, ht, rfl⟩ hcard
      beta_reduce at hcard ⊢
      have hcard' : t.card = 3 := by
        rw [← Finset.card_image_of_injOn ((injOn_iota hA).mono (face_subset_vertices ht))]
        exact hcard
      rw [reembed_link_vertices hA ht, ((injOn_iota hA).mono ?_).ncard_image]
      · exact htri t ht hcard'
      · intro q hq
        exact face_subset_vertices hq.1 (Finset.mem_singleton_self q)
    · intro q hq
      obtain ⟨u, hu, hq⟩ := hq
      have hq' : u.image iota = {q} := hq
      have hmem : q ∈ u.image iota := by rw [hq']; exact Finset.mem_singleton_self q
      obtain ⟨p, hpu, rfl⟩ := Finset.mem_image.1 hmem
      have hp : p ∈ K.vertices := face_subset_vertices hu hpu
      obtain ⟨f, hf1, hf2, hf3⟩ := hchart p hp
      rw [reembed_star hA hp]
      refine ⟨f ∘ A, ?_, ?_, ?_⟩
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨a, ha⟩ := hf1 s hs
        refine ⟨a.comp A.toContinuousAffineMap, ?_⟩
        intro x hx
        have hAx : A x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n))) := by
          rw [← image_convexHull_image hA (face_subset_vertices hs.1)]
          exact ⟨x, hx, rfl⟩
        simp only [Function.comp, ContinuousAffineMap.comp_apply,
          ContinuousLinearMap.coe_toContinuousAffineMap]
        exact ha hAx
      · have hc := image_carrier (G := {u | u ∈ K.faces ∧ {p} ∪ u ∈ K.faces}) hA (fun u hu => hu.1)
        refine hf2.comp ((injOn_space (hind := hind) hA).mono
          (carrier_subset_space (hind := hind) (fun u hu => hu.1))) ?_
        intro x hx
        have hx' : A x ∈ A '' _ := ⟨x, hx, rfl⟩
        rw [hc] at hx'
        exact hx'
      · have hc := image_carrier (G := {u | u ∈ K.faces ∧ {p} ∪ u ∈ K.faces}) hA (fun u hu => hu.1)
        rw [Set.image_comp, hc]
        exact hf3
  · exact homeomorph_of_injOn (isCompact_space hfin) A.continuous (injOn_space hA)
      (image_space hA)

end OMA.Helpers

theorem OMA.CairnsAssembly.reembed : OMA.CairnsAtlas.H1 :=
  fun n K hK => OMA.Helpers.main_thm n K hK

end

/- ## Contract -/
section
section

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

def link (K : SimplicialComplex 𝕜 E) (p : E) : SimplicialComplex 𝕜 E where
  faces := {s | s ∈ K.faces ∧ p ∉ s ∧ insert p s ∈ K.faces}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, fun hp => hs.2.1 (hts hp),
      K.down_closed hs.2.2 (Finset.insert_subset_insert p hts) (Finset.insert_nonempty p t)⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

end Geometry.SimplicialComplex

end

section

open Set

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem isInvertible_self_comp_adjoint_of_surjective (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) : (Q.comp (adjoint Q)).IsInvertible := by
  have hker : (Q.comp (adjoint Q)).ker = ⊥ := by
    rw [ker_self_comp_adjoint, ← orthogonal_range,
      LinearMap.range_eq_top.mpr hQ, Submodule.top_orthogonal_eq_bot]
  have hinj : Function.Injective (Q.comp (adjoint Q)) := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective (Q.comp (adjoint Q)) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective (Q.comp (adjoint Q)) hker
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

noncomputable def kernelProjectionFormula (Q : E →L[ℝ] F) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ((adjoint Q).comp (Q.comp (adjoint Q)).inverse).comp Q

theorem starProjection_ker_eq_formula (Q : E →L[ℝ] F) (hQ : Function.Surjective Q) :
    Q.ker.starProjection = Q.kernelProjectionFormula := by
  have hS := Q.isInvertible_self_comp_adjoint_of_surjective hQ
  ext x
  change Q.ker.starProjection x = x - (adjoint Q) ((Q.comp (adjoint Q)).inverse (Q x))
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change Q (x - (adjoint Q) ((Q.comp (adjoint Q)).inverse (Q x))) = 0
    have he := hS.self_apply_inverse (Q x)
    change Q ((adjoint Q) ((Q.comp (adjoint Q)).inverse (Q x))) = Q x at he
    rw [map_sub, he, sub_self]
  · intro w hw
    have hw' : Q w = 0 := hw
    rw [sub_sub_cancel, adjoint_inner_left, hw', inner_zero_right]

theorem continuousAt_kernelProjectionFormula (Q : E →L[ℝ] F) (hQ : Function.Surjective Q) :
    ContinuousAt (kernelProjectionFormula : (E →L[ℝ] F) → E →L[ℝ] E) Q := by
  have hadj : ContinuousAt (adjoint : (E →L[ℝ] F) → F →L[ℝ] E) Q :=
    adjoint.continuous.continuousAt
  have hS : ContinuousAt (fun R : E →L[ℝ] F => R.comp (adjoint R)) Q :=
    continuousAt_id.clm_comp hadj
  have hinverse : ContinuousAt (inverse : (F →L[ℝ] F) → F →L[ℝ] F)
      (Q.comp (adjoint Q)) :=
    (Q.isInvertible_self_comp_adjoint_of_surjective hQ).contDiffAt_map_inverse
      (n := 0) |>.continuousAt
  have hi : ContinuousAt (fun R : E →L[ℝ] F => (R.comp (adjoint R)).inverse) Q :=
    hinverse.comp (f := fun R : E →L[ℝ] F => R.comp (adjoint R)) hS
  exact continuousAt_const.sub ((hadj.clm_comp hi).clm_comp continuousAt_id)

theorem continuous_kernel_starProjection :
    Continuous (fun Q : {Q : E →L[ℝ] F // Function.Surjective Q} => Q.val.ker.starProjection) := by
  have he : (fun Q : {Q : E →L[ℝ] F // Function.Surjective Q} => Q.val.ker.starProjection) =
      (fun Q => Q.val.kernelProjectionFormula) :=
    funext (fun Q => Q.val.starProjection_ker_eq_formula Q.property)
  rw [he]
  exact continuous_iff_continuousAt.mpr (fun Q =>
    (Q.val.continuousAt_kernelProjectionFormula Q.property).comp
      continuous_subtype_val.continuousAt)

end ContinuousLinearMap

end

section

namespace Module.Basis

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable def evaluationContinuousLinearEquiv (b : Basis ι 𝕜 E) :
    (E →L[𝕜] F) ≃L[𝕜] (ι → F) :=
  (b.equivFunL.arrowCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans
    (ContinuousLinearEquiv.piRing ι)

@[simp] theorem evaluationContinuousLinearEquiv_apply (b : Basis ι 𝕜 E)
    (Q : E →L[𝕜] F) (i : ι) : b.evaluationContinuousLinearEquiv Q i = Q (b i) := by
  change Q (b.equivFunL.symm (Pi.single i 1)) = Q (b i)
  congr 1
  apply b.equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j
  simp only [equivFunL_apply, repr_self_apply, Pi.single_apply, eq_comm]

@[simp] theorem evaluationContinuousLinearEquiv_symm_apply_basis (b : Basis ι 𝕜 E)
    (v : ι → F) (i : ι) : b.evaluationContinuousLinearEquiv.symm v (b i) = v i := by
  rw [← evaluationContinuousLinearEquiv_apply]
  exact congrFun (b.evaluationContinuousLinearEquiv.apply_symm_apply v) i

end Module.Basis

end

section

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure EuclideanSubspace where

  subspace : Submodule ℝ E

variable {E} in

theorem EuclideanSubspace.ext {U V : EuclideanSubspace E} (h : U.subspace = V.subspace) : U = V := by
  cases U
  cases V
  cases h
  rfl

variable [FiniteDimensional ℝ E]

noncomputable instance EuclideanSubspace.instTopologicalSpace :
    TopologicalSpace (EuclideanSubspace E) :=
  TopologicalSpace.induced (fun K : EuclideanSubspace E => K.subspace.starProjection)
    inferInstance

theorem EuclideanSubspace.continuous_projector :
    Continuous (fun K : EuclideanSubspace E => K.subspace.starProjection) :=
  continuous_induced_dom

variable {E}

theorem EuclideanSubspace.continuous_iff_projector {X : Type*} [TopologicalSpace X]
    {f : X → EuclideanSubspace E} :
    Continuous f ↔ Continuous (fun x => (f x).subspace.starProjection) :=
  continuous_induced_rng

end Geometry

end

section

open Set NormedSpace

section LinearExtension

variable {𝕜 E F ι : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] {v : ι → E}

theorem LinearIndependent.exists_linearMap_apply_eq (hv : LinearIndependent 𝕜 v) (f : ι → F) :
    ∃ L : E →ₗ[𝕜] F, ∀ i, L (v i) = f i := by
  classical
  let b := Module.Basis.span hv
  obtain ⟨L, hL⟩ := (b.constr ℤ f).exists_extend
  refine ⟨L, fun i => ?_⟩
  have h := LinearMap.congr_fun hL (b i)
  rw [Module.Basis.constr_basis] at h
  simpa [b] using h

end LinearExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LinearMap.eqOn_const_convexHull (L : E →ₗ[ℝ] ℝ) {s : Set E} {c : ℝ}
    (hs : ∀ x ∈ s, L x = c) : ∀ x ∈ convexHull ℝ s, L x = c :=
  convexHull_min hs ((convex_singleton c).linear_preimage L)

theorem LinearIndependent.exists_eq_one_on_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    ∃ L : E →ₗ[ℝ] ℝ, ∀ x ∈ convexHull ℝ s, L x = 1 := by
  obtain ⟨L, hL⟩ := hs.exists_linearMap_apply_eq (fun _ => (1 : ℝ))
  exact ⟨L, L.eqOn_const_convexHull (fun x hx => hL ⟨x, hx⟩)⟩

theorem LinearIndependent.zero_notMem_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) : (0 : E) ∉ convexHull ℝ s := by
  obtain ⟨L, hL⟩ := hs.exists_eq_one_on_convexHull
  intro hzero
  simpa using hL 0 hzero

theorem continuousAt_normalize_of_ne_zero {x : E} (hx : x ≠ 0) :
    ContinuousAt (normalize : E → E) x :=
  (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

theorem LinearMap.injOn_normalize_of_eq_one (L : E →ₗ[ℝ] ℝ) {s : Set E}
    (hs : ∀ x ∈ s, L x = 1) : InjOn (normalize : E → E) s := by
  intro x hx y hy hxy
  have hnorm : ‖x‖ = ‖y‖ := by
    have h := congrArg L hxy
    simp only [NormedSpace.normalize, map_smul, hs x hx, hs y hy, smul_eq_mul, mul_one] at h
    exact inv_injective h
  calc
    x = ‖x‖ • normalize x := (norm_smul_normalize x).symm
    _ = ‖y‖ • normalize y := by rw [hnorm, hxy]
    _ = y := norm_smul_normalize y

theorem LinearIndependent.injOn_normalize_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    InjOn (normalize : E → E) (convexHull ℝ s) := by
  obtain ⟨L, hL⟩ := hs.exists_eq_one_on_convexHull
  exact L.injOn_normalize_of_eq_one hL

end

section

open Set NormedSpace

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_norm_lower_bound_on_cone [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] F) {C : Set E} (hclosed : IsClosed C)
    (hsmul : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r • x ∈ C)
    (hker : ∀ x ∈ C, Q x = 0 → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ C, c * ‖x‖ ≤ ‖Q x‖ := by
  have hcompact : IsCompact (Metric.sphere (0 : E) 1 ∩ C) :=
    (isCompact_sphere (0 : E) 1).inter_right hclosed
  obtain ⟨c, hc, hb⟩ := hcompact.exists_forall_le' Q.continuous.norm.continuousOn
    (a := (0 : ℝ)) (fun x hx => by
      apply norm_pos_iff.mpr
      intro he
      have hx0 := hker x hx.2 he
      simpa [hx0] using hx.1)
  refine ⟨c, hc, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have hnx : normalize x ∈ Metric.sphere (0 : E) 1 ∩ C :=
    ⟨by simpa [Metric.mem_sphere] using norm_normalize hx0,
      hsmul x hx ‖x‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hx0))⟩
  calc
    c * ‖x‖ = ‖x‖ * c := mul_comm _ _
    _ ≤ ‖x‖ * ‖Q (normalize x)‖ := mul_le_mul_of_nonneg_left (hb _ hnx) (norm_nonneg x)
    _ = ‖Q (‖x‖ • normalize x)‖ := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
    _ = ‖Q x‖ := by rw [norm_smul_normalize]

end ContinuousLinearMap

end

section

open Set

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsSecantTransverse (K : Submodule ℝ E) (S : Set E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ S, ∀ y ∈ S,
    c * ‖x - y‖ ≤ ‖(x - y) - K.starProjection (x - y)‖

theorem isSecantTransverse_ker_of_lower_bound (Q : E →L[ℝ] F) {S : Set E}
    {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ S, ∀ y ∈ S, c * ‖x - y‖ ≤ ‖Q x - Q y‖) :
    Q.ker.IsSecantTransverse S := by
  have hden : 0 < ‖Q‖ + 1 := by positivity
  refine ⟨c / (‖Q‖ + 1), div_pos hc hden, fun x hx y hy => ?_⟩
  have hk : Q (Q.ker.starProjection (x - y)) = 0 :=
    Q.ker.starProjection_apply_mem (x - y)
  have hop : ‖Q x - Q y‖ ≤ ‖Q‖ * ‖(x - y) - Q.ker.starProjection (x - y)‖ := by
    calc
      ‖Q x - Q y‖ = ‖Q ((x - y) - Q.ker.starProjection (x - y))‖ := by
        rw [map_sub, hk, map_sub, sub_zero]
      _ ≤ _ := Q.le_opNorm ((x - y) - Q.ker.starProjection (x - y))
  calc
    c / (‖Q‖ + 1) * ‖x - y‖ = (c * ‖x - y‖) / (‖Q‖ + 1) := by ring
    _ ≤ ‖(x - y) - Q.ker.starProjection (x - y)‖ := by
      apply (div_le_iff₀ hden).mpr
      have hn := norm_nonneg ((x - y) - Q.ker.starProjection (x - y))
      have hxy := hb x hx y hy
      nlinarith

theorem IsSecantTransverse.injOn {K : Submodule ℝ E} {S : Set E}
    (hK : K.IsSecantTransverse S) (Q : E →L[ℝ] F) (hker : Q.ker = K) :
    InjOn Q S := by
  obtain ⟨c, hc, hb⟩ := hK
  intro x hx y hy he
  have hxy : x - y ∈ K := by
    rw [← hker]
    change Q (x - y) = 0
    rw [map_sub, he, sub_self]
  have h := hb x hx y hy
  rw [K.starProjection_eq_self_iff.mpr hxy, sub_self, norm_zero] at h
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem IsSecantTransverse.mono {K : Submodule ℝ E} {S T : Set E}
    (hK : K.IsSecantTransverse T) (hST : S ⊆ T) : K.IsSecantTransverse S := by
  obtain ⟨c, hc, hb⟩ := hK
  exact ⟨c, hc, fun x hx y hy => hb x (hST hx) y (hST hy)⟩

theorem isSecantTransverse_of_projector_dist_le {K L : Submodule ℝ E} {S : Set E}
    {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ S, ∀ y ∈ S, c * ‖x - y‖ ≤ ‖(x - y) - K.starProjection (x - y)‖)
    (hKL : ‖K.starProjection - L.starProjection‖ ≤ c / 2) :
    L.IsSecantTransverse S := by
  refine ⟨c / 2, half_pos hc, fun x hx y hy => ?_⟩
  have hop := (K.starProjection - L.starProjection).le_opNorm (x - y)
  have hd := norm_sub_norm_le ((x - y) - K.starProjection (x - y))
    ((x - y) - L.starProjection (x - y))
  have he : (x - y - K.starProjection (x - y)) -
      (x - y - L.starProjection (x - y)) =
      -(K.starProjection (x - y) - L.starProjection (x - y)) := by abel
  rw [he, norm_neg] at hd
  have hmul := mul_le_mul_of_nonneg_right hKL (norm_nonneg (x - y))
  have hxy := hb x hx y hy
  change ‖K.starProjection (x - y) - L.starProjection (x - y)‖ ≤ _ at hop
  linarith

end Submodule

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isOpen_isSecantTransverse (S : Set E) :
    IsOpen {K : EuclideanSubspace E | K.subspace.IsSecantTransverse S} := by
  apply isOpen_iff_mem_nhds.mpr
  intro K hK
  obtain ⟨c, hc, hb⟩ := hK
  have hn := (continuous_projector E).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds K.subspace.starProjection (half_pos hc))
  apply Filter.mem_of_superset hn
  intro L hL
  apply Submodule.isSecantTransverse_of_projector_dist_le hc hb
  exact (by simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    using hL : ‖K.subspace.starProjection - L.subspace.starProjection‖ < c / 2).le

end Geometry.EuclideanSubspace

end

section

open Set
open scoped Pointwise Topology

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

end

section

open Set
open scoped Pointwise Topology

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

def closedFaceStar (K : SimplicialComplex 𝕜 E) (s : Finset E) : SimplicialComplex 𝕜 E where
  faces := {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}
  indep ht := K.indep ht.1
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨K.nonempty_of_mem_faces ht.1, ?_⟩
    intro u hut hu
    exact ⟨K.down_closed ht.1 hut hu,
      K.down_closed ht.2 (Finset.union_subset_union Subset.rfl hut)
        (Finset.union_nonempty.mpr (Or.inr hu))⟩
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1

theorem closedFaceStar_antitone (K : SimplicialComplex 𝕜 E) : Antitone K.closedFaceStar := by
  intro s t hst r hr
  refine ⟨hr.1, K.down_closed hr.2 (Finset.union_subset_union hst Finset.Subset.rfl) ?_⟩
  exact Finset.union_nonempty.mpr (Or.inr (K.nonempty_of_mem_faces hr.1))

end Algebraic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem starConvex_closedFaceStar (K : SimplicialComplex ℝ E) (s : Finset E)
    {p : E} (hp : p ∈ convexHull ℝ (s : Set E)) : StarConvex ℝ p (K.closedFaceStar s).space := by
  intro x hx a b ha hb hab
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
  have hst : s ∪ t ∈ (K.closedFaceStar s).faces :=
    ⟨ht.2, by simpa only [← Finset.union_assoc, Finset.union_self] using ht.2⟩
  apply convexHull_subset_space hst
  exact (convex_convexHull ℝ _)
    (convexHull_mono (by simp only [Finset.coe_union]; exact subset_union_left) hp)
    (convexHull_mono (by simp only [Finset.coe_union]; exact subset_union_right) hxt) ha hb hab

end Geometry.SimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

end Submodule

end

section

open Set NormedSpace

namespace ConvexCone

section Algebra

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

omit [IsStrictOrderedRing 𝕜] in

theorem hull_convexHull (s : Set E) : hull 𝕜 (convexHull 𝕜 s) = hull 𝕜 s := by
  apply le_antisymm
  · exact hull_min (convexHull_min subset_hull (hull 𝕜 s).convex)
  · exact hull_min ((subset_convexHull 𝕜 s).trans subset_hull)

theorem hull_image_pos_smul (s : Set E) (r : E → 𝕜) (hr : ∀ x ∈ s, 0 < r x) :
    hull 𝕜 ((fun x => r x • x) '' s) = hull 𝕜 s := by
  apply le_antisymm
  · apply hull_min
    rintro _ ⟨x, hx, rfl⟩
    exact (hull 𝕜 s).smul_mem (hr x hx) (subset_hull hx)
  · apply hull_min
    intro x hx
    have hmem : r x • x ∈ hull 𝕜 ((fun y => r y • y) '' s) :=
      subset_hull ⟨x, hx, rfl⟩
    have h := (hull 𝕜 ((fun y => r y • y) '' s)).smul_mem (inv_pos.mpr (hr x hx)) hmem
    rw [inv_smul_smul₀ (hr x hx).ne'] at h
    exact h

theorem zero_notMem_hull_iff (s : Set E) : (0 : E) ∉ hull 𝕜 s ↔ 0 ∉ convexHull 𝕜 s := by
  constructor
  · intro h hzero
    apply h
    rw [← hull_convexHull s]
    exact subset_hull hzero
  · intro h hzero
    rw [← hull_convexHull s] at hzero
    obtain ⟨r, hr, y, hy, hry⟩ := (mem_hull_of_convex (convex_convexHull 𝕜 s)).mp hzero
    have hy0 : y = 0 := (smul_eq_zero.mp hry).resolve_left hr.ne'
    exact h (hy0 ▸ hy)

end Algebra

end ConvexCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalize_image_convexHull_eq_sphere_inter_cone {s : Set E}
    (hs : (0 : E) ∉ convexHull ℝ s) :
    NormedSpace.normalize '' convexHull ℝ s =
      Metric.sphere (0 : E) 1 ∩ (ConvexCone.hull ℝ s : Set E) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := fun h => hs (h ▸ hx)
    refine ⟨by simpa [Metric.mem_sphere] using norm_normalize hx0, ?_⟩
    have hxc : x ∈ ConvexCone.hull ℝ s := by
      rw [← ConvexCone.hull_convexHull s]
      exact ConvexCone.subset_hull hx
    exact (ConvexCone.hull ℝ s).smul_mem (inv_pos.mpr (norm_pos_iff.mpr hx0)) hxc
  · rintro x ⟨hxsphere, hxcone⟩
    rw [← ConvexCone.hull_convexHull s] at hxcone
    obtain ⟨r, hr, y, hy, hry⟩ :=
      (ConvexCone.mem_hull_of_convex (convex_convexHull ℝ s)).mp hxcone
    refine ⟨y, hy, ?_⟩
    calc
      NormedSpace.normalize y = NormedSpace.normalize (r • y) :=
        (normalize_smul_of_pos hr y).symm
      _ = NormedSpace.normalize x := congrArg NormedSpace.normalize hry
      _ = x := normalize_eq_self_of_norm_eq_one (by simpa [Metric.mem_sphere] using hxsphere)

theorem normalize_image_convexHull_pos_smul {s : Set E} (hs : (0 : E) ∉ convexHull ℝ s)
    (r : E → ℝ) (hr : ∀ x ∈ s, 0 < r x) :
    NormedSpace.normalize '' convexHull ℝ ((fun x => r x • x) '' s) =
      NormedSpace.normalize '' convexHull ℝ s := by
  have hs' : (0 : E) ∉ convexHull ℝ ((fun x => r x • x) '' s) := by
    rw [← ConvexCone.zero_notMem_hull_iff, ConvexCone.hull_image_pos_smul s r hr]
    exact (ConvexCone.zero_notMem_hull_iff s).mpr hs
  rw [normalize_image_convexHull_eq_sphere_inter_cone hs',
    normalize_image_convexHull_eq_sphere_inter_cone hs, ConvexCone.hull_image_pos_smul s r hr]

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def AffineOnFaces (K : SimplicialComplex ℝ E) (f : E → F) : Prop :=
  ∀ s ∈ K.faces, ∃ a : E →ᴬ[ℝ] F, EqOn f a (convexHull ℝ (s : Set E))

variable {K L : SimplicialComplex ℝ E} {f g : E → F}

theorem affineOnFaces_affine (K : SimplicialComplex ℝ E) (a : E →ᴬ[ℝ] F) :
    K.AffineOnFaces a :=
  fun _ _ => ⟨a, fun _ _ => rfl⟩

theorem AffineOnFaces.congr (hf : K.AffineOnFaces f) (hfg : EqOn f g K.space) :
    K.AffineOnFaces g := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  exact ⟨a, fun _ hx => (hfg (convexHull_subset_space hs hx)).symm.trans (ha hx)⟩

theorem AffineOnFaces.continuousOn_of_locallyFinite (hf : K.AffineOnFaces f)
    (hlocal : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E))) :
    ContinuousOn f K.space := by
  have hcont : ContinuousOn f (⋃ s : K.faces, convexHull ℝ (s.val : Set E)) := by
    apply hlocal.continuousOn_iUnion
    · intro s
      exact s.val.finite_toSet.isClosed_convexHull ℝ
    · intro s
      obtain ⟨a, ha⟩ := hf s.val s.property
      exact a.continuous.continuousOn.congr ha
  simpa only [space, iUnion_subtype] using hcont

theorem AffineOnFaces.continuousOn (hf : K.AffineOnFaces f) (hfinite : K.faces.Finite) :
    ContinuousOn f K.space := by
  let := hfinite.fintype
  exact hf.continuousOn_of_locallyFinite (locallyFinite_of_finite _)

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isCompact_space_of_finite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    IsCompact K.space :=
  hK.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ

variable {K : SimplicialComplex ℝ E} {f : E → F}

noncomputable def AffineOnFaces.homeomorphImage (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hinj : InjOn f K.space) : K.space ≃ₜ f '' K.space := by
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite K hK)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn f K.space hinj)
    ((hf.continuousOn hK).domRestrict.subtype_mk _)

noncomputable def AffineOnFaces.homeomorphOfBijOn (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) {S : Set F} (hbij : BijOn f K.space S) : K.space ≃ₜ S :=
  (hf.homeomorphImage hK hbij.injOn).trans (Homeomorph.setCongr hbij.image_eq)

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LinearIndependent.image_smul_of_ne_zero {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) (r : E → ℝ)
    (hr : ∀ x ∈ s, r x ≠ 0) :
    LinearIndependent ℝ ((↑) : ((fun x => r x • x) '' s) → E) := by
  have h := hs.units_smul (fun x : s => Units.mk0 (r x) (hr x x.property))
  have hi : LinearIndependent ℝ (fun x : s => r x • (x : E)) := h
  change LinearIndepOn ℝ id ((fun x => r x • x) '' s)
  rw [Set.image_eq_range]
  exact hi.linearIndepOn_id

namespace Geometry.SimplicialComplex

variable {K : SimplicialComplex ℝ E}

theorem face_subset_vertices {s : Finset E} (hs : s ∈ K.faces) :
    (s : Set E) ⊆ K.vertices := by
  rw [vertices_eq]
  exact subset_biUnion_of_mem hs

private theorem radial_rescale_common_face
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) {z w : E}
    (hz : z ∈ convexHull ℝ ((fun x => r x • x) '' (s : Set E)))
    (hw : w ∈ convexHull ℝ ((fun x => r x • x) '' (t : Set E)))
    (hzw : NormedSpace.normalize z = NormedSpace.normalize w) :
    z = w ∧ z ∈ convexHull ℝ ((fun x => r x • x) '' ((s : Set E) ∩ t)) := by
  have hrs : ∀ x ∈ (s : Set E), 0 < r x := fun x hx => hr x (face_subset_vertices hs hx)
  have hrt : ∀ x ∈ (t : Set E), 0 < r x := fun x hx => hr x (face_subset_vertices ht hx)
  have hsnorm := normalize_image_convexHull_pos_smul (hlin s hs).zero_notMem_convexHull r hrs
  have htnorm := normalize_image_convexHull_pos_smul (hlin t ht).zero_notMem_convexHull r hrt
  obtain ⟨x, hxs, hxz⟩ := hsnorm.subset ⟨z, hz, rfl⟩
  obtain ⟨y, hyt, hyw⟩ := htnorm.subset ⟨w, hw, rfl⟩
  have hxy := hinj (convexHull_subset_space hs hxs) (convexHull_subset_space ht hyt)
    (hxz.trans (hzw.trans hyw.symm))
  have hxinter : x ∈ convexHull ℝ ((s : Set E) ∩ t) :=
    K.inter_subset_convexHull hs ht ⟨hxs, hxy ▸ hyt⟩
  have hzero : (0 : E) ∉ convexHull ℝ ((s : Set E) ∩ t) :=
    fun h => (hlin s hs).zero_notMem_convexHull (convexHull_mono inter_subset_left h)
  have hinter := normalize_image_convexHull_pos_smul hzero r (fun x hx => hrs x hx.1)
  obtain ⟨p, hp, hpx⟩ := hinter.symm.subset ⟨x, hxinter, rfl⟩
  have hps : p ∈ convexHull ℝ ((fun x => r x • x) '' (s : Set E)) :=
    convexHull_mono (image_mono inter_subset_left) hp
  have hpt : p ∈ convexHull ℝ ((fun x => r x • x) '' (t : Set E)) :=
    convexHull_mono (image_mono inter_subset_right) hp
  have hsind := (hlin s hs).image_smul_of_ne_zero r (fun x hx => (hrs x hx).ne')
  have htind := (hlin t ht).image_smul_of_ne_zero r (fun x hx => (hrt x hx).ne')
  have hpz := hsind.injOn_normalize_convexHull hps hz (hpx.trans hxz)
  have hpw := htind.injOn_normalize_convexHull hpt hw (hpx.trans (hxz.trans hzw))
  exact ⟨hpz.symm.trans hpw, hpz ▸ hp⟩

variable [DecidableEq E]

def radialRescale (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) : SimplicialComplex ℝ E where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.map (fun x => r x • x)
  indep := by
    rintro _ ⟨s, hs, rfl⟩
    have h := (hlin s hs).image_smul_of_ne_zero r
      (fun x hx => (hr x (face_subset_vertices hs hx)).ne')
    rw [← Finset.coe_image] at h
    exact h.affineIndependent
  inter_subset_convexHull := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ z ⟨hz, hzt⟩
    simp only [Finset.coe_image] at hz hzt ⊢
    exact convexHull_mono (Set.image_inter_subset _ _ _)
      (radial_rescale_common_face hlin hinj r hr hs ht hz hzt rfl).2

theorem linearIndependent_radialRescale_face
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    {s : Finset E} (hs : s ∈ (K.radialRescale hlin hinj r hr).faces) :
    LinearIndependent ℝ ((↑) : s → E) := by
  obtain ⟨t, ht, rfl⟩ := hs
  have h := (hlin t ht).image_smul_of_ne_zero r
    (fun x hx => (hr x (face_subset_vertices ht hx)).ne')
  rwa [← Finset.coe_image] at h

theorem injOn_normalize_radialRescale
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    InjOn (NormedSpace.normalize : E → E) (K.radialRescale hlin hinj r hr).space := by
  intro z hz w hw hzw
  obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := mem_space_iff.mp hz
  obtain ⟨_, ⟨t, ht, rfl⟩, hwt⟩ := mem_space_iff.mp hw
  simp only [Finset.coe_image] at hzs hwt
  exact (radial_rescale_common_face hlin hinj r hr hs ht hzs hwt hzw).1

end Geometry.SimplicialComplex

end

section

open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem AffineIndependent.exists_continuousAffineMap_eqOn {s : Set E}
    (hs : AffineIndependent 𝕜 ((↑) : s → E)) (f : E → F) :
    ∃ a : E →ᴬ[𝕜] F, EqOn a f s := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t 𝕜 E := ⟨Subtype.val, ht, by simpa using hspan⟩
  let : Finite t := b.finite
  let : Fintype t := Fintype.ofFinite t
  let a : E →ᵃ[𝕜] F :=
    (Fintype.linearCombination 𝕜 (fun i : t => f i)).toAffineMap.comp b.coords
  refine ⟨⟨a, a.continuous_of_finiteDimensional⟩, ?_⟩
  intro x hx
  have hbx : b ⟨x, hst hx⟩ = x := rfl
  change (Fintype.linearCombination 𝕜 (fun i : t => f i)) (b.coords x) = f x
  rw [← hbx, Fintype.linearCombination_apply]
  simp [AffineBasis.coords_apply, AffineBasis.coord_apply]
  rfl

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

theorem AffineOnFaces.eqOn_of_eqOn_vertices (hf : K.AffineOnFaces f)
    (hg : K.AffineOnFaces g) (hfg : EqOn f g K.vertices) : EqOn f g K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg s hs
  have hv : (s : Set E) ⊆ K.vertices := by
    rw [vertices_eq]
    exact subset_biUnion_of_mem hs
  have hab : EqOn a.toAffineMap b.toAffineMap (s : Set E) := by
    intro y hy
    exact (ha (subset_convexHull ℝ _ hy)).symm.trans
      ((hfg (hv hy)).trans (hb (subset_convexHull ℝ _ hy)))
  exact (ha hxs).trans
    ((AffineMap.eqOn_affineSpan hab (convexHull_subset_affineSpan _ hxs)).trans (hb hxs).symm)

variable [FiniteDimensional ℝ E]

theorem exists_affineOnFaces_eqOn_vertices (K : SimplicialComplex ℝ E) (v : E → F) :
    ∃ f : E → F, K.AffineOnFaces f ∧ EqOn f v K.vertices := by
  classical
  choose a ha using fun s : K.faces => (K.indep s.property).exists_continuousAffineMap_eqOn v
  have hcompat (s t : K.faces) : EqOn (a s) (a t)
      (convexHull ℝ (s.val : Set E) ∩ convexHull ℝ (t.val : Set E)) := by
    have hab : EqOn (a s).toAffineMap (a t).toAffineMap
        ((s.val : Set E) ∩ (t.val : Set E)) := by
      intro x hx
      exact (ha s hx.1).trans (ha t hx.2).symm
    intro x hx
    rw [K.convexHull_inter_convexHull s.property t.property] at hx
    exact AffineMap.eqOn_affineSpan hab (convexHull_subset_affineSpan _ hx)
  choose s hs hxs using fun x : K.space => mem_space_iff.mp x.property
  let face : K.space → K.faces := fun x => ⟨s x, hs x⟩
  have hface (x : K.space) : (x : E) ∈ convexHull ℝ ((face x).val : Set E) := hxs x
  let f : E → F := fun x => if hx : x ∈ K.space then a (face ⟨x, hx⟩) x else 0
  have hformula (t : K.faces) : EqOn f (a t) (convexHull ℝ (t.val : Set E)) := by
    intro x hx
    have hxK := convexHull_subset_space t.property hx
    dsimp only [f]
    rw [dif_pos hxK]
    exact hcompat _ t ⟨hface ⟨x, hxK⟩, hx⟩
  refine ⟨f, fun t ht => ⟨a ⟨t, ht⟩, hformula ⟨t, ht⟩⟩, ?_⟩
  intro x hx
  exact (hformula ⟨{x}, hx⟩ (by simp)).trans (ha ⟨{x}, hx⟩ (by simp))

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}
  {f : E → F} {g : F → G}

theorem AffineOnFaces.image_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) :
    f '' convexHull ℝ (s : Set E) = convexHull ℝ (f '' (s : Set E)) := by
  obtain ⟨a, ha⟩ := hf s hs
  have hav : EqOn f a (s : Set E) := ha.mono (subset_convexHull ℝ _)
  calc
    f '' convexHull ℝ (s : Set E) = a '' convexHull ℝ (s : Set E) := ha.image_eq
    _ = convexHull ℝ (a '' (s : Set E)) := a.toAffineMap.image_convexHull _
    _ = convexHull ℝ (f '' (s : Set E)) := congrArg (convexHull ℝ) hav.image_eq.symm

theorem AffineOnFaces.mapsTo_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) {t : Set F} (hst : f '' (s : Set E) ⊆ t) :
    MapsTo f (convexHull ℝ (s : Set E)) (convexHull ℝ t) := by
  intro x hx
  apply convexHull_mono hst
  rw [← hf.image_convexHull hs]
  exact mem_image_of_mem f hx

theorem AffineOnFaces.mapsTo_space (hf : K.AffineOnFaces f)
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    MapsTo f K.space L.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  exact convexHull_subset_space ht (hf.mapsTo_convexHull hs hst hxs)

theorem AffineOnFaces.comp_of_face_images (hf : K.AffineOnFaces f)
    (hg : L.AffineOnFaces g)
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    K.AffineOnFaces (g ∘ f) := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg t ht
  refine ⟨b.comp a, fun x hx => ?_⟩
  exact (hb (hf.mapsTo_convexHull hs hst hx)).trans (congrArg b (ha hx))

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

private theorem mapsTo_vertices_of_face_images {f : E → F}
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    MapsTo f K.vertices L.vertices := by
  intro x hx
  obtain ⟨t, ht, hst⟩ := hfaces {x} hx
  exact L.down_closed ht
    (Finset.singleton_subset_iff.mpr (hst ⟨x, by simp, rfl⟩)) (Finset.singleton_nonempty _)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_homeomorph_of_vertex_maps (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite) (v : E → F) (w : F → E)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F))
    (hw : ∀ t ∈ L.faces, ∃ s ∈ K.faces, w '' (t : Set F) ⊆ (s : Set E))
    (hleft : LeftInvOn w v K.vertices) (hright : RightInvOn w v L.vertices) :
    ∃ (f : E → F) (g : F → E) (e : K.space ≃ₜ L.space),
      K.AffineOnFaces f ∧ L.AffineOnFaces g ∧
      EqOn f v K.vertices ∧ EqOn g w L.vertices ∧
      (∀ x : K.space, (e x : F) = f x) ∧
      (∀ y : L.space, (e.symm y : E) = g y) := by
  obtain ⟨f, hf, hfv⟩ := K.exists_affineOnFaces_eqOn_vertices v
  obtain ⟨g, hg, hgw⟩ := L.exists_affineOnFaces_eqOn_vertices w
  have hfacesF : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := hv s hs
    have hvS : (s : Set E) ⊆ K.vertices := by
      rw [vertices_eq]
      exact subset_biUnion_of_mem hs
    exact ⟨t, ht, ((hfv.mono hvS).image_eq).subset.trans hst⟩
  have hfacesG : ∀ t ∈ L.faces, ∃ s ∈ K.faces, g '' (t : Set F) ⊆ (s : Set E) := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := hw t ht
    have hwT : (t : Set F) ⊆ L.vertices := by
      rw [vertices_eq]
      exact subset_biUnion_of_mem ht
    exact ⟨s, hs, ((hgw.mono hwT).image_eq).subset.trans hts⟩
  have hfv_map := mapsTo_vertices_of_face_images hfacesF
  have hgw_map := mapsTo_vertices_of_face_images hfacesG
  have hgf : LeftInvOn g f K.space :=
    (hf.comp_of_face_images hg hfacesF).eqOn_of_eqOn_vertices
      (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)) fun x hx => by
        change g (f x) = x
        rw [hgw (hfv_map hx), hfv hx]
        exact hleft hx
  have hfg : RightInvOn g f L.space :=
    (hg.comp_of_face_images hf hfacesG).eqOn_of_eqOn_vertices
      (L.affineOnFaces_affine (ContinuousAffineMap.id ℝ F)) fun y hy => by
        change f (g y) = y
        rw [hfv (hgw_map hy), hgw hy]
        exact hright hy
  have hbij : BijOn f K.space L.space :=
    ⟨hf.mapsTo_space hfacesF, hgf.injOn,
      fun y hy => ⟨g y, hg.mapsTo_space hfacesG hy, hfg hy⟩⟩
  let e := hf.homeomorphOfBijOn hK hbij
  refine ⟨f, g, e, hf, hg, hfv, hgw, fun _ => rfl, ?_⟩
  intro y
  have hval : f (e.symm y) = (y : F) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  exact (hgf (e.symm y).property).symm.trans (congrArg g hval)

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E}

theorem injOn_pos_smul_vertices
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    InjOn (fun x => r x • x) K.vertices := by
  intro x hx y hy hxy
  apply hinj (vertices_subset_space hx) (vertices_subset_space hy)
  have h := congrArg NormedSpace.normalize hxy
  simpa only [normalize_smul_of_pos (hr x hx), normalize_smul_of_pos (hr y hy)] using h

variable [DecidableEq E]

variable [FiniteDimensional ℝ E]

end Geometry.SimplicialComplex

end

section

open Set NormedSpace Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsRadialEmbedding (A : AbstractSimplicialComplex ι) (v : ι → E) : Prop :=
  Function.Injective v ∧ ∃ L : SimplicialComplex ℝ E,
    L.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)} ∧
    (∀ t ∈ L.faces, LinearIndependent ℝ ((↑) : t → E)) ∧
    InjOn (NormedSpace.normalize : E → E) L.space

abbrev RadialEmbedding (A : AbstractSimplicialComplex ι) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] := {v : ι → E // A.IsRadialEmbedding v}

variable {A : AbstractSimplicialComplex ι} {v : ι → E}

private theorem vertices_eq_range_of_faces {L : SimplicialComplex ℝ E}
    (hfaces : L.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)}) :
    L.vertices = range v := by
  ext y
  constructor
  · intro hy
    change {y} ∈ L.faces at hy
    rw [hfaces] at hy
    obtain ⟨s, _, he⟩ := hy
    have hmem : y ∈ v '' (s : Set ι) := he ▸ (by simp : y ∈ ({y} : Finset E))
    obtain ⟨i, _, hi⟩ := hmem
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    change {v i} ∈ L.faces
    rw [hfaces]
    exact ⟨{i}, A.singleton_mem i, by simp⟩

theorem IsRadialEmbedding.ne_zero (hv : A.IsRadialEmbedding v) (i : ι) : v i ≠ 0 := by
  obtain ⟨L, hfaces, hlin, _⟩ := hv.2
  have hvertex : v i ∈ L.vertices := by
    rw [vertices_eq_range_of_faces hfaces]
    exact mem_range_self i
  intro hi
  apply (hlin {v i} hvertex).zero_notMem_convexHull
  simp [hi]

theorem IsRadialEmbedding.pos_smul (hv : A.IsRadialEmbedding v)
    (r : E → ℝ) (hr : ∀ i, 0 < r (v i)) :
    A.IsRadialEmbedding (fun i => r (v i) • v i) := by
  classical
  obtain ⟨L, hfaces, hlin, hinj⟩ := hv.2
  have hvertices := vertices_eq_range_of_faces hfaces
  have hpos : ∀ x ∈ L.vertices, 0 < r x := by
    intro x hx
    rw [hvertices] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hr i
  have hvinj := SimplicialComplex.injOn_pos_smul_vertices hinj r hpos
  refine ⟨fun i j hij => hv.1 (hvinj ?_ ?_ hij), L.radialRescale hlin hinj r hpos, ?_,
    fun _ hs => SimplicialComplex.linearIndependent_radialRescale_face hlin hinj r hpos hs,
    SimplicialComplex.injOn_normalize_radialRescale hlin hinj r hpos⟩
  · rw [hvertices]
    exact mem_range_self i
  · rw [hvertices]
    exact mem_range_self j
  · ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hfaces] at hu
      obtain ⟨s, hs, hus⟩ := hu
      exact ⟨s, hs, by simp only [Finset.coe_image, hus, Set.image_image]⟩
    · rintro ⟨s, hs, hts⟩
      refine ⟨s.image v, ?_, ?_⟩
      · rw [hfaces]
        exact ⟨s, hs, Finset.coe_image⟩
      · apply Finset.coe_injective
        simpa only [Finset.coe_image, Set.image_image] using hts.symm

theorem IsRadialEmbedding.normalize (hv : A.IsRadialEmbedding v) :
    A.IsRadialEmbedding (fun i => NormedSpace.normalize (v i)) :=
  hv.pos_smul (fun x => ‖x‖⁻¹) (fun i => inv_pos.mpr (norm_pos_iff.mpr (hv.ne_zero i)))

end AbstractSimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

section General

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

def vertexAbstractComplex (K : SimplicialComplex 𝕜 E) : AbstractSimplicialComplex K.vertices where
  faces := {s | s.map (Function.Embedding.subtype _) ∈ K.faces}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.map_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact K.down_closed hs (Finset.map_subset_map.mpr hts) (Finset.map_nonempty.mpr ht)
  singleton_mem v := by
    change ({v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
    rw [Finset.map_singleton]
    exact v.property

theorem faces_eq_vertexAbstractComplex_images (K : SimplicialComplex 𝕜 E) :
    K.faces = {t : Finset E | ∃ s ∈ K.vertexAbstractComplex.faces,
      (t : Set E) = Subtype.val '' (s : Set K.vertices)} := by
  classical
  ext t
  constructor
  · intro ht
    have hv : ∀ x ∈ t, x ∈ K.vertices := by
      intro x hx
      rw [vertices_eq]
      exact mem_iUnion₂.mpr ⟨t, ht, hx⟩
    have he := Finset.subtype_map_of_mem hv
    refine ⟨t.subtype (fun x => x ∈ K.vertices), ?_, ?_⟩
    · change (t.subtype (fun x => x ∈ K.vertices)).map (Function.Embedding.subtype _) ∈ K.faces
      rwa [he]
    · simpa only [Finset.coe_map, Function.Embedding.coe_subtype] using
        (congrArg (fun s : Finset E => (s : Set E)) he).symm
  · rintro ⟨s, hs, he⟩
    have heq : s.map (Function.Embedding.subtype _) = t := by
      apply Finset.coe_injective
      simpa only [Finset.coe_map, Function.Embedding.coe_subtype] using he.symm
    change s.map (Function.Embedding.subtype _) ∈ K.faces at hs
    rwa [heq] at hs

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [DecidableEq E]

end Geometry.SimplicialComplex

end

section

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ι → E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem image_face_subset_range {A : AbstractSimplicialComplex ι}
    [DecidableEq E] {t : Finset E}
    (ht : t ∈ (A.toPreAbstractSimplicialComplex.map v).faces) :
    (t : Set E) ⊆ range v := by
  obtain ⟨s, _, rfl⟩ := ht
  simpa only [Finset.coe_image] using image_subset_range v s

noncomputable def independentComplex (A : AbstractSimplicialComplex ι)
    (hv : LinearIndependent ℝ v) : SimplicialComplex ℝ E := by
  classical
  refine { A.toPreAbstractSimplicialComplex.map v with
    indep := fun hs => (hv.linearIndepOn_id.mono (image_face_subset_range hs)).affineIndependent
    inter_subset_convexHull := ?_ }
  intro s t hs ht
  have hsub : ((s ∪ t : Finset E) : Set E) ⊆ range v := by
    simpa only [Finset.coe_union] using
      union_subset (image_face_subset_range hs) (image_face_subset_range ht)
  exact ((hv.linearIndepOn_id.mono hsub).affineIndependent.convexHull_inter').symm.subset

theorem independentComplex_faces (A : AbstractSimplicialComplex ι)
    (hv : LinearIndependent ℝ v) :
    (A.independentComplex hv).faces =
      {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)} := by
  classical
  ext t
  change (∃ s ∈ A.faces, s.image v = t) ↔ _
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, Finset.coe_image⟩
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, Finset.coe_injective (Finset.coe_image.trans he.symm)⟩

theorem isRadialEmbedding_of_linearIndependent (A : AbstractSimplicialComplex ι)
    (hv : LinearIndependent ℝ v) : A.IsRadialEmbedding v := by
  classical
  refine ⟨hv.injective, A.independentComplex hv, A.independentComplex_faces hv,
    fun _ ht => hv.linearIndepOn_id.mono (image_face_subset_range ht), ?_⟩
  apply hv.linearIndepOn_id.injOn_normalize_convexHull.mono
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact convexHull_mono (image_face_subset_range hs) hxs

end AbstractSimplicialComplex

end

section

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LinearIndependent.affineIndependent_insert_zero {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    AffineIndependent ℝ ((↑) : ↥(insert (0 : E) s) → E) := by
  have hnonzero : ∀ x ∈ s, x ≠ (0 : E) := fun x hx he =>
    hs.zero_notMem_convexHull (he ▸ subset_convexHull ℝ s hx)
  have h := (linearIndependent_set_iff_affineIndependent_vadd_union_singleton
    ℝ hnonzero (0 : E)).mp hs
  let f : ↥(insert (0 : E) s) →
      ↥({(0 : E)} ∪ (fun v : E => v +ᵥ (0 : E)) '' s) :=
    fun x => ⟨x.val, by
      rcases x.property with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨x.val, hx, by simp [vadd_eq_add]⟩⟩
  exact h.comp_embedding ⟨f, fun x y hxy => Subtype.ext
    (congrArg (fun z : ↥({(0 : E)} ∪ (fun v : E => v +ᵥ (0 : E)) '' s) => (z : E)) hxy)⟩

theorem exists_pos_smul_of_mem_convexHull_insert_zero {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ (insert (0 : E) s)) (hx0 : x ≠ 0) :
    ∃ y ∈ convexHull ℝ s, ∃ r ∈ Ioc (0 : ℝ) 1, x = r • y := by
  have hs : s.Nonempty := by
    by_contra hs
    exact hx0 (by simpa [Set.not_nonempty_iff_eq_empty.mp hs] using hx)
  rw [convexHull_insert hs, mem_convexJoin] at hx
  obtain ⟨p, hp, y, hy, a, b, ha, hb, hab, heq⟩ := hx
  rw [mem_singleton_iff] at hp
  subst p
  simp only [smul_zero, zero_add] at heq
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_smul] at heq
    exact hx0 heq.symm
  exact ⟨y, hy, b, ⟨lt_of_le_of_ne hb hb0.symm, by linarith⟩, heq.symm⟩

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

omit [NormedSpace ℝ E] in
private theorem subset_insert_erased (s : Finset E) :
    (s : Set E) ⊆ insert (0 : E) (s.erase 0 : Set E) := by
  intro x hx
  by_cases h : x = 0
  · exact Or.inl h
  · exact Or.inr (Finset.mem_erase.mpr ⟨h, hx⟩)

private theorem cone_face_independent
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    {s : Finset E} (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces) :
    AffineIndependent ℝ ((↑) : s → E) := by
  rcases hs with he | hface
  · apply (affineIndependent_of_subsingleton ℝ ((↑) : ↥({(0 : E)} : Set E) → E)).mono
    intro x hx
    change x = 0
    by_contra hx0
    have hmem : x ∈ s.erase 0 := Finset.mem_erase.mpr ⟨hx0, hx⟩
    exact Finset.notMem_empty x (he ▸ hmem)
  · exact (hlin _ hface).affineIndependent_insert_zero.mono (subset_insert_erased s)

private theorem cone_face_zero_mem
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    {s : Finset E} (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces)
    (hzero : (0 : E) ∈ convexHull ℝ (s : Set E)) : (0 : E) ∈ s := by
  by_contra hs0
  rw [Finset.erase_eq_of_notMem hs0] at hs
  rcases hs with he | hface
  · simp [he] at hzero
  · exact (hlin _ hface).zero_notMem_convexHull hzero

private theorem cone_face_base_point {s : Finset E}
    (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hx0 : x ≠ 0) :
    s.erase 0 ∈ K.faces ∧
      ∃ y ∈ convexHull ℝ (s.erase 0 : Set E), ∃ r ∈ Ioc (0 : ℝ) 1, x = r • y := by
  obtain ⟨y, hy, r, hr, he⟩ := exists_pos_smul_of_mem_convexHull_insert_zero
    (convexHull_mono (subset_insert_erased s) hx) hx0
  have hsK : s.erase 0 ∈ K.faces := hs.resolve_left (fun hempty => by simp [hempty] at hy)
  exact ⟨hsK, y, hy, r, hr, he⟩

private theorem cone_faces_inter_subset
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    {s t : Finset E} (hs : s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces)
    (ht : t.erase 0 = ∅ ∨ t.erase 0 ∈ K.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ t) := by
  rintro x ⟨hxs, hxt⟩
  by_cases hx0 : x = 0
  · subst x
    exact subset_convexHull ℝ _ ⟨cone_face_zero_mem hlin hs hxs, cone_face_zero_mem hlin ht hxt⟩
  obtain ⟨hsK, y, hy, a, ha, hxa⟩ := cone_face_base_point hs hxs hx0
  obtain ⟨htK, z, hz, b, hb, hxb⟩ := cone_face_base_point ht hxt hx0
  have hyx : NormedSpace.normalize y = NormedSpace.normalize x := by
    rw [hxa, normalize_smul_of_pos ha.1]
  have hzx : NormedSpace.normalize z = NormedSpace.normalize x := by
    rw [hxb, normalize_smul_of_pos hb.1]
  have hyz := hinj (convexHull_subset_space hsK hy) (convexHull_subset_space htK hz)
    (hyx.trans hzx.symm)
  have hyinter := K.inter_subset_convexHull hsK htK ⟨hy, hyz ▸ hz⟩
  have hsubset : (s.erase 0 : Set E) ∩ (t.erase 0 : Set E) ⊆ (s : Set E) ∩ t :=
    fun _ hv => ⟨Finset.erase_subset _ _ hv.1, Finset.erase_subset _ _ hv.2⟩
  have hybase : y ∈ convexHull ℝ ((s : Set E) ∩ t) := convexHull_mono hsubset hyinter
  by_cases hs0 : (0 : E) ∈ s
  · by_cases ht0 : (0 : E) ∈ t
    · rw [hxa]
      exact (convex_convexHull ℝ ((s : Set E) ∩ t)).smul_mem_of_zero_mem
        (subset_convexHull ℝ _ ⟨hs0, ht0⟩) hybase ⟨ha.1.le, ha.2⟩
    · have hxt' : x ∈ convexHull ℝ (t.erase 0 : Set E) := by
        simpa only [Finset.erase_eq_of_notMem ht0] using hxt
      have hxy := hinj (convexHull_subset_space htK hxt')
        (convexHull_subset_space hsK hy) hyx.symm
      simpa only [hxy] using hybase
  · have hxs' : x ∈ convexHull ℝ (s.erase 0 : Set E) := by
      simpa only [Finset.erase_eq_of_notMem hs0] using hxs
    have hxy := hinj (convexHull_subset_space hsK hxs')
      (convexHull_subset_space hsK hy) hyx.symm
    simpa only [hxy] using hybase

def coneAtZero (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) : SimplicialComplex ℝ E where
  faces := {s | s.Nonempty ∧ (s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces)}
  indep hs := cone_face_independent hlin hs.2
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    by_cases he : t.erase 0 = ∅
    · exact Or.inl he
    · right
      rcases hs.2 with hs' | hs'
      · have hsub := Finset.erase_subset_erase (0 : E) hts
        rw [hs'] at hsub
        exact (he (Finset.subset_empty.mp hsub)).elim
      · exact K.down_closed hs' (Finset.erase_subset_erase _ hts)
          (Finset.nonempty_iff_ne_empty.mpr he)
  inter_subset_convexHull hs ht := cone_faces_inter_subset hlin hinj hs.2 ht.2

theorem zero_mem_coneAtZero_vertices
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (0 : E) ∈ (K.coneAtZero hlin hinj).vertices :=
  ⟨Finset.singleton_nonempty _, Or.inl (by simp)⟩

theorem le_coneAtZero
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) : K ≤ K.coneAtZero hlin hinj := by
  intro s hs
  have hs0 : (0 : E) ∉ s := fun h =>
    (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
  exact ⟨K.nonempty_of_mem_faces hs, Or.inr (by rwa [Finset.erase_eq_of_notMem hs0])⟩

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

theorem coneAtZero_vertices
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).vertices = insert (0 : E) K.vertices := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hbase := hx.2
      have hnot : (0 : E) ∉ ({x} : Finset E) := by simpa using Ne.symm hx0
      rw [Finset.erase_eq_of_notMem hnot] at hbase
      exact hbase.resolve_left (Finset.singleton_nonempty x).ne_empty
  · rintro (hx | hx)
    · subst x
      exact zero_mem_coneAtZero_vertices hlin hinj
    · exact le_coneAtZero hlin hinj hx

theorem insert_zero_mem_coneAtZero_faces
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    {s : Finset E} (hs : s ∈ K.faces) : insert (0 : E) s ∈ (K.coneAtZero hlin hinj).faces := by
  have hs0 : (0 : E) ∉ s := fun h =>
    (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
  exact ⟨Finset.insert_nonempty _ _, Or.inr (by rwa [Finset.erase_insert hs0])⟩

theorem finite_coneAtZero_faces (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).faces.Finite := by
  apply ((hK.union (hK.image (fun s => insert (0 : E) s))).union
    (Set.finite_singleton ({0} : Finset E))).subset
  intro s hs
  rcases hs.2 with he | hface
  · right
    rcases (Finset.erase_eq_empty_iff s 0).mp he with he | he
    · exact (hs.1.ne_empty he).elim
    · exact he
  · left
    by_cases hs0 : (0 : E) ∈ s
    · exact Or.inr ⟨s.erase 0, hface, Finset.insert_erase hs0⟩
    · exact Or.inl (by simpa only [Finset.erase_eq_of_notMem hs0] using hface)

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

theorem coneAtZero_face_images
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (v : E → F) (hv0 : v 0 = 0)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F)) :
    ∀ s ∈ (K.coneAtZero hlinK hinjK).faces,
      ∃ t ∈ (L.coneAtZero hlinL hinjL).faces, v '' (s : Set E) ⊆ (t : Set F) := by
  intro s hs
  rcases hs.2 with he | hface
  · refine ⟨{0}, zero_mem_coneAtZero_vertices hlinL hinjL, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x = 0 := by
      by_contra hx0
      have hmem := Finset.mem_erase.mpr ⟨hx0, hx⟩
      rw [he] at hmem
      exact Finset.notMem_empty x hmem
    simp [hx0, hv0]
  · obtain ⟨t, ht, hst⟩ := hv _ hface
    refine ⟨insert (0 : F) t, insert_zero_mem_coneAtZero_faces hlinL hinjL ht, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · simp [hx0, hv0]
    · exact Finset.mem_insert_of_mem (hst ⟨x, Finset.mem_erase.mpr ⟨hx0, hx⟩, rfl⟩)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_cone_homeomorph_of_vertex_maps (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (v : E → F) (w : F → E) (hv0 : v 0 = 0) (hw0 : w 0 = 0)
    (hv : ∀ s ∈ K.faces, ∃ t ∈ L.faces, v '' (s : Set E) ⊆ (t : Set F))
    (hw : ∀ t ∈ L.faces, ∃ s ∈ K.faces, w '' (t : Set F) ⊆ (s : Set E))
    (hleft : LeftInvOn w v K.vertices) (hright : RightInvOn w v L.vertices) :
    ∃ (f : E → F) (g : F → E)
      (e : (K.coneAtZero hlinK hinjK).space ≃ₜ (L.coneAtZero hlinL hinjL).space),
      (K.coneAtZero hlinK hinjK).AffineOnFaces f ∧
      (L.coneAtZero hlinL hinjL).AffineOnFaces g ∧
      EqOn f v (K.coneAtZero hlinK hinjK).vertices ∧
      EqOn g w (L.coneAtZero hlinL hinjL).vertices ∧
      (∀ x : (K.coneAtZero hlinK hinjK).space, (e x : F) = f x) ∧
      (∀ y : (L.coneAtZero hlinL hinjL).space, (e.symm y : E) = g y) := by
  apply (K.coneAtZero hlinK hinjK).exists_homeomorph_of_vertex_maps
    (L.coneAtZero hlinL hinjL) (finite_coneAtZero_faces hK hlinK hinjK) v w
    (coneAtZero_face_images hlinK hinjK hlinL hinjL v hv0 hv)
    (coneAtZero_face_images hlinL hinjL hlinK hinjK w hw0 hw)
  · intro x hx
    rw [coneAtZero_vertices] at hx
    rcases hx with hx | hx
    · rw [hx, hv0, hw0]
    · exact hleft hx
  · intro y hy
    rw [coneAtZero_vertices] at hy
    rcases hy with hy | hy
    · rw [hy, hw0, hv0]
    · exact hright hy

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

omit [DecidableEq E] in

theorem vertices_image_of_faces {v : E → F}
    (hfaces : L.faces = (fun s : Finset E => s.image v) '' K.faces) :
    L.vertices = v '' K.vertices := by
  ext y
  constructor
  · intro hy
    change {y} ∈ L.faces at hy
    rw [hfaces] at hy
    obtain ⟨s, hs, he⟩ := hy
    dsimp only at he
    have hmem : y ∈ s.image v := by rw [he]; simp
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hmem
    exact ⟨x, K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty _), hxy⟩
  · rintro ⟨x, hx, rfl⟩
    change {v x} ∈ L.faces
    rw [hfaces]
    exact ⟨{x}, hx, by simp⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_cone_homeomorph_of_linear_map (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (Q : E →L[ℝ] F) (hQ : InjOn Q K.vertices)
    (hfaces : L.faces = (fun s : Finset E => s.image Q) '' K.faces) :
    ∃ (g : F → E)
      (e : (K.coneAtZero hlinK hinjK).space ≃ₜ (L.coneAtZero hlinL hinjL).space),
      (L.coneAtZero hlinL hinjL).AffineOnFaces g ∧
      (∀ x : (K.coneAtZero hlinK hinjK).space, (e x : F) = Q x) ∧
      (∀ y : (L.coneAtZero hlinL hinjL).space, (e.symm y : E) = g y) := by
  let w : F → E := fun y => if y = 0 then 0 else Function.invFunOn Q K.vertices y
  have hvertices := vertices_image_of_faces hfaces
  have hleft : LeftInvOn w Q K.vertices := by
    intro x hx
    have hvx : Q x ∈ L.vertices := hvertices ▸ mem_image_of_mem Q hx
    have hne : Q x ≠ 0 := by
      intro he
      apply (hlinL {Q x} hvx).zero_notMem_convexHull
      simp [he]
    dsimp only [w]
    rw [if_neg hne]
    exact hQ.leftInvOn_invFunOn hx
  have hvfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces,
      Q '' (s : Set E) ⊆ (t : Set F) := by
    intro s hs
    exact ⟨s.image Q, hfaces ▸ mem_image_of_mem _ hs, by simp⟩
  have hwfaces : ∀ t ∈ L.faces, ∃ s ∈ K.faces,
      w '' (t : Set F) ⊆ (s : Set E) := by
    intro t ht
    rw [hfaces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s, hs, ?_⟩
    rw [Finset.coe_image]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [hleft (K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty _))]
    exact hx
  have hright : RightInvOn w Q L.vertices := by
    intro y hy
    rw [hvertices] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hleft hx]
  obtain ⟨f, g, e, hf, hg, hfv, _, hef, heg⟩ :=
    K.exists_cone_homeomorph_of_vertex_maps L hK hlinK hinjK hlinL hinjL
      Q w (map_zero Q) (by simp [w]) hvfaces hwfaces hleft hright
  have hfQ : EqOn f Q (K.coneAtZero hlinK hinjK).space :=
    hf.eqOn_of_eqOn_vertices
      ((K.coneAtZero hlinK hinjK).affineOnFaces_affine Q.toContinuousAffineMap) hfv
  exact ⟨g, e, hg, fun x => (hef x).trans (hfQ x.property), heg⟩

end Geometry.SimplicialComplex

end

section

open Set NormedSpace
open scoped unitInterval

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

theorem AffineOnFaces.interpolate (hf : K.AffineOnFaces f) (hg : K.AffineOnFaces g) (t : ℝ) :
    K.AffineOnFaces (fun x => (1 - t) • f x + t • g x) := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg s hs
  refine ⟨(1 - t) • a + t • b, fun x hx => ?_⟩
  simp only [ContinuousAffineMap.add_apply, ContinuousAffineMap.smul_apply, ha hx, hb hx]

theorem radial_interpolation_pos {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t + t * r := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · simp [← h]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos h hr)

variable [DecidableEq E] [FiniteDimensional ℝ E] {f : E → E}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

noncomputable def RadialEmbedding.normalized (v : A.RadialEmbedding E) : A.RadialEmbedding E :=
  ⟨fun i => NormedSpace.normalize (v.val i), v.property.normalize⟩

theorem RadialEmbedding.continuous_normalized :
    Continuous (RadialEmbedding.normalized : A.RadialEmbedding E → A.RadialEmbedding E) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro v
  exact (continuousAt_normalize_of_ne_zero (v.property.ne_zero i)).comp
    (f := fun v : A.RadialEmbedding E => v.val i)
    (((continuous_apply i).comp continuous_subtype_val).continuousAt)

theorem RadialEmbedding.norm_normalized (v : A.RadialEmbedding E) (i : ι) :
    ‖v.normalized.val i‖ = 1 := norm_normalize (v.property.ne_zero i)

theorem RadialEmbedding.normalized_eq_self (v : A.RadialEmbedding E)
    (hv : ∀ i, ‖v.val i‖ = 1) : v.normalized = v :=
  Subtype.ext (funext fun i => normalize_eq_self_of_norm_eq_one (hv i))

noncomputable def RadialEmbedding.interpolate (t : I) (v : A.RadialEmbedding E) :
    A.RadialEmbedding E :=
  ⟨fun i => (1 - (t : ℝ)) • v.val i + (t : ℝ) • NormedSpace.normalize (v.val i), by
    have h := v.property.pos_smul (fun x => 1 - (t : ℝ) + (t : ℝ) * ‖x‖⁻¹)
      (fun i => Geometry.SimplicialComplex.radial_interpolation_pos
        (inv_pos.mpr (norm_pos_iff.mpr (v.property.ne_zero i))) t.property)
    simpa only [add_smul, mul_smul, NormedSpace.normalize] using h⟩

theorem RadialEmbedding.continuous_interpolate :
    Continuous (fun tv : I × A.RadialEmbedding E => tv.2.interpolate tv.1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have ht : Continuous (fun tv : I × A.RadialEmbedding E => (tv.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun tv : I × A.RadialEmbedding E => tv.2.val i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  have hn : Continuous (fun tv : I × A.RadialEmbedding E =>
      NormedSpace.normalize (tv.2.val i)) :=
    (continuous_apply i).comp (continuous_subtype_val.comp
      (RadialEmbedding.continuous_normalized.comp continuous_snd))
  exact ((continuous_const.sub ht).smul hv).add (ht.smul hn)

@[simp] theorem RadialEmbedding.interpolate_zero (v : A.RadialEmbedding E) :
    v.interpolate 0 = v := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) • v.val i + (0 : ℝ) • NormedSpace.normalize (v.val i) = v.val i
  simp

@[simp] theorem RadialEmbedding.interpolate_one (v : A.RadialEmbedding E) :
    v.interpolate 1 = v.normalized := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) • v.val i + (1 : ℝ) • NormedSpace.normalize (v.val i) =
    NormedSpace.normalize (v.val i)
  simp

abbrev UnitRadialEmbedding (A : AbstractSimplicialComplex ι) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {v : A.RadialEmbedding E // ∀ i, ‖v.val i‖ = 1}

end AbstractSimplicialComplex

end

section

open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev FixedRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.RadialEmbedding E // EqOn v.val w s}

abbrev FixedUnitRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.UnitRadialEmbedding E // EqOn v.val.val w s}

variable {A : AbstractSimplicialComplex ι} {s : Set ι} {w : ι → E}

noncomputable def FixedRadialEmbedding.normalized (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (v : A.FixedRadialEmbedding s w) : A.FixedUnitRadialEmbedding s w :=
  ⟨⟨v.val.normalized, v.val.norm_normalized⟩, by
    intro i hi
    change NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi)]⟩

def FixedUnitRadialEmbedding.toFixedRadial (v : A.FixedUnitRadialEmbedding s w) :
    A.FixedRadialEmbedding s w := ⟨v.val.val, v.property⟩

theorem FixedRadialEmbedding.continuous_normalized (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (FixedRadialEmbedding.normalized hw :
      A.FixedRadialEmbedding s w → A.FixedUnitRadialEmbedding s w) :=
  ((RadialEmbedding.continuous_normalized.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem FixedUnitRadialEmbedding.continuous_toFixedRadial :
    Continuous (FixedUnitRadialEmbedding.toFixedRadial :
      A.FixedUnitRadialEmbedding s w → A.FixedRadialEmbedding s w) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

noncomputable def FixedRadialEmbedding.interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (t : I) (v : A.FixedRadialEmbedding s w) : A.FixedRadialEmbedding s w :=
  ⟨v.val.interpolate t, by
    intro i hi
    change (1 - (t : ℝ)) • v.val.val i + (t : ℝ) • NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi), ← add_smul]
    simp⟩

theorem FixedRadialEmbedding.continuous_interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (fun tv : I × A.FixedRadialEmbedding s w => tv.2.interpolate hw tv.1) :=
  (RadialEmbedding.continuous_interpolate.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

noncomputable def fixedRadialNormalizationHomotopyEquiv (A : AbstractSimplicialComplex ι)
    (s : Set ι) (w : ι → E) (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ContinuousMap.HomotopyEquiv (A.FixedRadialEmbedding s w) (A.FixedUnitRadialEmbedding s w) := by
  let f : C(A.FixedRadialEmbedding s w, A.FixedUnitRadialEmbedding s w) :=
    ⟨FixedRadialEmbedding.normalized hw, FixedRadialEmbedding.continuous_normalized hw⟩
  let g : C(A.FixedUnitRadialEmbedding s w, A.FixedRadialEmbedding s w) :=
    ⟨FixedUnitRadialEmbedding.toFixedRadial, FixedUnitRadialEmbedding.continuous_toFixedRadial⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id (A.FixedRadialEmbedding s w)) (g.comp f) :=
    { toFun := fun tv => tv.2.interpolate hw tv.1
      continuous_toFun := FixedRadialEmbedding.continuous_interpolate hw
      map_zero_left := fun v => Subtype.ext v.val.interpolate_zero
      map_one_left := fun v => Subtype.ext v.val.interpolate_one }
  refine ⟨f, g, ⟨H.symm⟩, ?_⟩
  have heq : f.comp g = ContinuousMap.id (A.FixedUnitRadialEmbedding s w) := by
    apply ContinuousMap.ext
    intro v
    exact Subtype.ext (Subtype.ext (v.val.val.normalized_eq_self v.val.property))
  rw [heq]

theorem contractible_fixedRadialEmbedding_iff (A : AbstractSimplicialComplex ι)
    (s : Set ι) (w : ι → E) (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ContractibleSpace (A.FixedRadialEmbedding s w) ↔
      ContractibleSpace (A.FixedUnitRadialEmbedding s w) :=
  (fixedRadialNormalizationHomotopyEquiv A s w hw).contractibleSpace_iff

end AbstractSimplicialComplex

end

section

open Set

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev BasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  {Q : E →L[ℝ] F // A.IsRadialEmbedding (fun i => Q (b i))}

noncomputable def basisRadialProjectionHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    A.BasisRadialProjection b F ≃ₜ A.RadialEmbedding F :=
  b.evaluationContinuousLinearEquiv.toHomeomorph.subtype (fun Q => by
    change A.IsRadialEmbedding (fun i => Q (b i)) ↔
      A.IsRadialEmbedding (b.evaluationContinuousLinearEquiv Q)
    have he : b.evaluationContinuousLinearEquiv Q = fun i => Q (b i) :=
      funext (b.evaluationContinuousLinearEquiv_apply Q)
    rw [he])

abbrev FixedBasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (s : Set ι) (w : ι → F) :=
  {Q : A.BasisRadialProjection b F // EqOn (fun i => Q.val (b i)) w s}

noncomputable def fixedBasisRadialProjectionHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (s : Set ι) (w : ι → F) :
    A.FixedBasisRadialProjection b s w ≃ₜ A.FixedRadialEmbedding s w :=
  (basisRadialProjectionHomeomorph A b F).subtype (fun Q => by
    change EqOn (fun i => Q.val (b i)) w s ↔
      EqOn (b.evaluationContinuousLinearEquiv Q.val) w s
    have he : b.evaluationContinuousLinearEquiv Q.val = fun i => Q.val (b i) :=
      funext (b.evaluationContinuousLinearEquiv_apply Q.val)
    rw [he])

end AbstractSimplicialComplex

end

section

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {A : AbstractSimplicialComplex ι}

noncomputable def RadialEmbedding.complex (v : A.RadialEmbedding E) :
    SimplicialComplex ℝ E := v.property.2.choose

theorem RadialEmbedding.complex_faces (v : A.RadialEmbedding E) :
    v.complex.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v.val '' (s : Set ι)} :=
  v.property.2.choose_spec.1

theorem RadialEmbedding.complex_linearIndependent (v : A.RadialEmbedding E) :
    ∀ s ∈ v.complex.faces, LinearIndependent ℝ ((↑) : s → E) :=
  v.property.2.choose_spec.2.1

theorem RadialEmbedding.complex_injOn_normalize (v : A.RadialEmbedding E) :
    InjOn (NormedSpace.normalize : E → E) v.complex.space :=
  v.property.2.choose_spec.2.2

theorem RadialEmbedding.complex_faces_image [DecidableEq E] (v : A.RadialEmbedding E) :
    v.complex.faces = (fun s : Finset ι => s.image v.val) '' A.faces := by
  rw [v.complex_faces]
  ext t
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, Finset.coe_injective (Finset.coe_image.trans he.symm)⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, Finset.coe_image⟩

theorem RadialEmbedding.complex_vertices (v : A.RadialEmbedding E) :
    v.complex.vertices = range v.val := by
  classical
  ext y
  change {y} ∈ v.complex.faces ↔ _
  rw [v.complex_faces_image]
  constructor
  · rintro ⟨s, _, he⟩
    dsimp only at he
    have hy : y ∈ s.image v.val := by rw [he]; simp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨{i}, A.singleton_mem i, by simp⟩

theorem RadialEmbedding.finite_complex_faces [Finite ι] (v : A.RadialEmbedding E) :
    v.complex.faces.Finite := by
  classical
  let := Fintype.ofFinite ι
  rw [v.complex_faces_image]
  exact (Set.toFinite A.faces).image _

noncomputable def RadialEmbedding.cone (v : A.RadialEmbedding E) : SimplicialComplex ℝ E := by
  classical
  exact v.complex.coneAtZero v.complex_linearIndependent v.complex_injOn_normalize

theorem RadialEmbedding.exists_cone_homeomorph_of_linearMap [Finite ι]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (v : A.RadialEmbedding E) (w : A.RadialEmbedding F)
    (Q : E →L[ℝ] F) (hQ : ∀ i, Q (v.val i) = w.val i) :
    ∃ (g : F → E) (e : v.cone.space ≃ₜ w.cone.space),
      w.cone.AffineOnFaces g ∧ (∀ x : v.cone.space, (e x : F) = Q x) ∧
      (∀ y : w.cone.space, (e.symm y : E) = g y) := by
  classical
  apply v.complex.exists_cone_homeomorph_of_linear_map w.complex v.finite_complex_faces
    v.complex_linearIndependent v.complex_injOn_normalize
    w.complex_linearIndependent w.complex_injOn_normalize Q
  · intro x hx y hy he
    rw [v.complex_vertices] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    rw [hQ, hQ] at he
    exact congrArg v.val (w.property.1 he)
  · rw [v.complex_faces_image, w.complex_faces_image, Set.image_image]
    congr 1
    funext s
    rw [Finset.image_image]
    congr 1
    exact funext hQ |>.symm

theorem RadialEmbedding.injOn_cone_of_linearMap [Finite ι]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (v : A.RadialEmbedding E) (w : A.RadialEmbedding F)
    (Q : E →L[ℝ] F) (hQ : ∀ i, Q (v.val i) = w.val i) : InjOn Q v.cone.space := by
  obtain ⟨_, e, _, he, _⟩ := v.exists_cone_homeomorph_of_linearMap w Q hQ
  intro x hx y hy hxy
  have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
    Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm))
  exact congrArg Subtype.val (e.injective hexy)

noncomputable def basisRadialEmbedding (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) : A.RadialEmbedding E :=
  ⟨b, A.isRadialEmbedding_of_linearIndependent b.linearIndependent⟩

theorem BasisRadialProjection.injOn_basisCone [Finite ι]
    [FiniteDimensional ℝ F] {b : Module.Basis ι ℝ E}
    (Q : A.BasisRadialProjection b F) : InjOn Q.val (A.basisRadialEmbedding b).cone.space := by
  let := b.finiteDimensional_of_finite
  exact (A.basisRadialEmbedding b).injOn_cone_of_linearMap
    ⟨fun i => Q.val (b i), Q.property⟩ Q.val (fun _ => rfl)

end AbstractSimplicialComplex

end

section

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

theorem RadialEmbedding.cone_space (v : A.RadialEmbedding E) :
    v.cone.space = ⋃ s ∈ insert ∅ A.faces,
      convexHull ℝ (insert 0 (v.val '' (s : Set ι))) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
    have ht' : t.Nonempty ∧ (t.erase 0 = ∅ ∨ t.erase 0 ∈ v.complex.faces) := ht
    have hsub : (t : Set E) ⊆ insert 0 (t.erase 0 : Set E) := by
      simpa only [Finset.coe_insert] using
        (show (t : Set E) ⊆ (insert 0 (t.erase 0) : Finset E) from
          Finset.insert_erase_subset _ _)
    rcases ht'.2 with he | he
    · refine mem_iUnion₂.mpr ⟨∅, mem_insert _ _, ?_⟩
      have h := convexHull_mono hsub hxt
      simpa only [he, Finset.coe_empty, Set.image_empty] using h
    · rw [v.complex_faces] at he
      obtain ⟨s, hs, hts⟩ := he
      exact mem_iUnion₂.mpr ⟨s, mem_insert_of_mem _ hs,
        convexHull_mono (hts ▸ hsub) hxt⟩
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    rcases hs with rfl | hs
    · have hx0 : x = 0 := by simpa using hxs
      subst x
      exact SimplicialComplex.vertices_subset_space
        (SimplicialComplex.zero_mem_coneAtZero_vertices
          v.complex_linearIndependent v.complex_injOn_normalize)
    · have hface : s.image v.val ∈ v.complex.faces := by
        rw [v.complex_faces_image]
        exact mem_image_of_mem _ hs
      have hcone := SimplicialComplex.insert_zero_mem_coneAtZero_faces
        v.complex_linearIndependent v.complex_injOn_normalize hface
      apply SimplicialComplex.convexHull_subset_space hcone
      simpa only [Finset.coe_insert, Finset.coe_image] using hxs

end AbstractSimplicialComplex

end

section

open Set AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

def faceLink (K : SimplicialComplex 𝕜 E) (s : Finset E) : SimplicialComplex 𝕜 E where
  faces := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
  indep ht := K.indep ht.1
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨K.nonempty_of_mem_faces ht.1, ?_⟩
    intro u hut hu
    exact ⟨K.down_closed ht.1 hut hu, ht.2.1.mono_right hut,
      K.down_closed ht.2.2 (Finset.union_subset_union Subset.rfl hut)
        (Finset.union_nonempty.mpr (Or.inr hu))⟩
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1

theorem finite_faceLink_faces {K : SimplicialComplex 𝕜 E}
    (hK : K.faces.Finite) (s : Finset E) : (K.faceLink s).faces.Finite :=
  hK.subset (fun _ ht => ht.1)

theorem faceLink_vertices_subset (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    (K.faceLink s).vertices ⊆ K.vertices \ (s : Set E) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxs
  exact Finset.disjoint_left.mp hx.2.1 hxs (Finset.mem_singleton_self x)

theorem sdiff_mem_faceLink_or_empty (K : SimplicialComplex 𝕜 E) (s : Finset E)
    {t : Finset E} (ht : t ∈ (K.closedFaceStar s).faces) :
    t \ s ∈ insert ∅ (K.faceLink s).faces := by
  by_cases he : t \ s = ∅
  · exact Or.inl he
  · exact Or.inr ⟨K.down_closed ht.1 Finset.sdiff_subset
      (Finset.nonempty_iff_ne_empty.mpr he),
      Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx),
      by simpa only [Finset.union_sdiff_self_eq_union] using ht.2⟩

end Algebraic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E]

private theorem image_union_of_zero_on (f : E →ᵃ[ℝ] F) {s : Finset E}
    (hs : s.Nonempty) (hf : ∀ x ∈ s, f x = 0) (t : Finset E) :
    f '' ((s ∪ t : Finset E) : Set E) = insert 0 (f '' (t : Set E)) := by
  rw [Finset.coe_union, image_union]
  have hsimage : f '' (s : Set E) = {0} := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hf x hx
    · obtain ⟨x, hx⟩ := hs
      rintro _ rfl
      exact ⟨x, hx, hf x hx⟩
  rw [hsimage, singleton_union]

theorem affine_image_closedFaceStar (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0) :
    f '' (K.closedFaceStar s).space =
      ⋃ t ∈ insert ∅ (K.faceLink s).faces,
        convexHull ℝ (insert 0 (f '' (t : Set E))) := by
  have hsne := K.nonempty_of_mem_faces hs
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    refine mem_iUnion₂.mpr ⟨t \ s, K.sdiff_mem_faceLink_or_empty s ht, ?_⟩
    have hsub : (t : Set E) ⊆ ((s ∪ (t \ s) : Finset E) : Set E) := by
      rw [Finset.union_sdiff_self_eq_union]
      exact Finset.subset_union_right
    have hximage : f x ∈ f '' convexHull ℝ ((s ∪ (t \ s) : Finset E) : Set E) :=
      mem_image_of_mem f (convexHull_mono hsub hxt)
    rwa [f.image_convexHull, image_union_of_zero_on f hsne hf] at hximage
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
    have hst : s ∪ t ∈ (K.closedFaceStar s).faces := by
      rcases ht with rfl | ht
      · change s ∪ ∅ ∈ K.faces ∧ s ∪ (s ∪ ∅) ∈ K.faces
        simpa only [Finset.union_empty, Finset.union_self] using And.intro hs hs
      · exact ⟨ht.2.2, by simpa only [← Finset.union_assoc, Finset.union_self] using ht.2.2⟩
    rw [← image_union_of_zero_on f hsne hf, ← f.image_convexHull] at hyt
    obtain ⟨x, hx, rfl⟩ := hyt
    exact mem_image_of_mem f (convexHull_subset_space hst hx)

theorem affine_image_closedFaceStar_eq_radialCone (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0)
    (hr : (K.faceLink s).vertexAbstractComplex.IsRadialEmbedding
      (fun v : (K.faceLink s).vertices => f v)) :
    f '' (K.closedFaceStar s).space =
      (RadialEmbedding.cone
        (⟨_, hr⟩ : (K.faceLink s).vertexAbstractComplex.RadialEmbedding F)).space := by
  rw [K.affine_image_closedFaceStar hs f hf, AbstractSimplicialComplex.RadialEmbedding.cone_space]
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
    rcases ht with rfl | ht
    · exact mem_iUnion₂.mpr ⟨∅, Or.inl rfl, by simpa only [Finset.coe_empty, image_empty] using hyt⟩
    · rw [(K.faceLink s).faces_eq_vertexAbstractComplex_images] at ht
      obtain ⟨r, hr, htr⟩ := ht
      refine mem_iUnion₂.mpr ⟨r, Or.inr hr, ?_⟩
      simpa only [htr, image_image, Function.comp_def] using hyt
  · intro hy
    obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.mp hy
    let t := r.map (Function.Embedding.subtype (fun x => x ∈ (K.faceLink s).vertices))
    have ht : t ∈ insert ∅ (K.faceLink s).faces := by
      rcases hr with rfl | hr
      · exact Or.inl (Finset.map_empty _)
      · exact Or.inr hr
    refine mem_iUnion₂.mpr ⟨t, ht, ?_⟩
    simpa only [t, Finset.coe_map, Function.Embedding.coe_subtype, image_image,
      Function.comp_def] using hyr

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

section Combinatorial

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

theorem card_add_card_le_of_mem_faceLink (K : SimplicialComplex 𝕜 E)
    {m : ℕ} (hbound : ∀ t ∈ K.faces, t.card ≤ m) (s : Finset E)
    {t : Finset E} (ht : t ∈ (K.faceLink s).faces) : s.card + t.card ≤ m := by
  have h := hbound (s ∪ t) ht.2.2
  rwa [Finset.card_union_of_disjoint ht.2.1] at h

theorem faceLink_faces_eq_empty_of_card_eq (K : SimplicialComplex 𝕜 E)
    {m : ℕ} (hbound : ∀ t ∈ K.faces, t.card ≤ m) {s : Finset E} (hs : s.card = m) :
    (K.faceLink s).faces = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h := K.card_add_card_le_of_mem_faceLink hbound s ht
  have htpos := Finset.card_pos.mpr ((K.faceLink s).nonempty_of_mem_faces ht)
  omega

omit [DecidableEq E] in

theorem exists_faces_eq_two_singletons (K : SimplicialComplex 𝕜 E)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 1) (hvertices : K.vertices.ncard = 2) :
    ∃ u v : E, u ≠ v ∧ K.faces = {({u} : Finset E), {v}} := by
  classical
  obtain ⟨u, v, huv, he⟩ := Set.ncard_eq_two.mp hvertices
  refine ⟨u, v, huv, ?_⟩
  ext t
  constructor
  · intro ht
    have htpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
    have htle := hbound t ht
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
    have hx : x ∈ K.vertices := ht
    rw [he] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · change u ∈ K.vertices
      rw [he]
      exact Or.inl rfl
    · change v ∈ K.vertices
      rw [he]
      exact Or.inr rfl

end Combinatorial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finrank_faceDirection_of_card (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {n : ℕ} (hcard : s.card = n + 1) :
    Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction = n := by
  have h := (K.indep hs).finrank_vectorSpan (n := n) (by simpa using hcard)
  have hrange : range ((↑) : s → E) = (s : Set E) := by
    ext x
    simp
  rw [hrange] at h
  rw [direction_affineSpan]
  exact h

end Geometry.SimplicialComplex

end

section

open Set

namespace SimpleGraph

variable {V : Type*} [Finite V]

theorem exists_cyclic_labels_of_two_neighbors (G : SimpleGraph V) (hc : G.Connected)
    (hdegree : ∀ v, (G.neighborSet v).ncard = 2) :
    ∃ (n : ℕ) (e : Fin (n + 3) ≃ V), ∀ x y,
      G.Adj x y ↔ ∃ i, (e i = x ∧ e (i + 1) = y) ∨
        (e i = y ∧ e (i + 1) = x) := by
  classical
  let := Fintype.ofFinite V
  let := hc.nonempty
  let a : V := Classical.arbitrary V
  have hcycles : G.IsCycles := fun {v} _ => hdegree v
  have ha : (G.neighborSet a).Nonempty :=
    nonempty_of_ncard_ne_zero (by rw [hdegree]; norm_num)
  obtain ⟨p, hp, hvertices⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk a) (show a ∈ (G.connectedComponentMk a).supp from rfl) ha
  have hall : ∀ x, x ∈ p.toSubgraph.verts := by
    intro x
    rw [hvertices, ConnectedComponent.mem_supp_iff]
    exact ConnectedComponent.sound (hc x a)
  let n := p.length - 3
  have hlength : n + 3 = p.length := Nat.sub_add_cancel hp.three_le_length
  let v : Fin (n + 3) → V := fun i => p.getVert i.val
  have hvinj : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) hij
  have hvsurj : Function.Surjective v := by
    intro x
    obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp
      (p.mem_verts_toSubgraph.mp (hall x))
    by_cases hilt : i < p.length
    · exact ⟨⟨i, by omega⟩, hi⟩
    · have hieq : i = p.length := by omega
      have hax : a = x := by simpa only [hieq, Walk.getVert_length] using hi
      exact ⟨0, (p.getVert_zero).trans hax⟩
  have hnext : ∀ i : Fin (n + 3), v (i + 1) = p.getVert (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < n + 3
    · change p.getVert (i + 1).val = p.getVert (i.val + 1)
      rw [Fin.val_add_one_of_lt' hi]
    · have he : i.val + 1 = p.length := by omega
      have hzero : i + 1 = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one, Fin.val_zero]
        rw [he, ← hlength, Nat.mod_self]
      rw [hzero, he, Walk.getVert_length]
      exact p.getVert_zero
  let e : Fin (n + 3) ≃ V := Equiv.ofBijective v ⟨hvinj, hvsurj⟩
  refine ⟨n, e, ?_⟩
  intro x y
  rw [← hp.adj_toSubgraph_iff_of_isCycles hcycles (hall x) y, p.toSubgraph_adj_iff]
  constructor
  · rintro ⟨i, hi, hil⟩
    refine ⟨⟨i, by omega⟩, ?_⟩
    change (v ⟨i, by omega⟩ = x ∧ v (⟨i, by omega⟩ + 1) = y) ∨
      (v ⟨i, by omega⟩ = y ∧ v (⟨i, by omega⟩ + 1) = x)
    rw [hnext]
    exact Sym2.eq_iff.mp hi
  · rintro ⟨i, hi⟩
    refine ⟨i.val, ?_, by omega⟩
    apply Sym2.eq_iff.mpr
    change (v i = x ∧ v (i + 1) = y) ∨ (v i = y ∧ v (i + 1) = x) at hi
    rwa [hnext] at hi

end SimpleGraph

end

section

namespace AbstractSimplicialComplex

variable {V : Type*} [DecidableEq V]

def edgeGraph (A : AbstractSimplicialComplex V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ {x, y} ∈ A.faces
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem mem_faces_iff_singleton_or_edge (A : AbstractSimplicialComplex V)
    (hdim : ∀ s ∈ A.faces, s.card ≤ 2) (s : Finset V) :
    s ∈ A.faces ↔ (∃ x, s = {x}) ∨ ∃ x y, A.edgeGraph.Adj x y ∧ s = {x, y} := by
  constructor
  · intro hs
    have hpos : 0 < s.card := Finset.card_pos.mpr (A.isRelLowerSet_faces hs).1
    have hle := hdim s hs
    by_cases hone : s.card = 1
    · exact Or.inl (Finset.card_eq_one.mp hone)
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
      exact Or.inr ⟨x, y, ⟨hxy, hs⟩, rfl⟩
  · rintro (⟨x, rfl⟩ | ⟨x, y, hxy, rfl⟩)
    · exact A.singleton_mem x
    · exact hxy.2

variable [Finite V]

theorem exists_cyclic_face_labels (A : AbstractSimplicialComplex V)
    (hdim : ∀ s ∈ A.faces, s.card ≤ 2) (hc : A.edgeGraph.Connected)
    (hdegree : ∀ v, (A.edgeGraph.neighborSet v).ncard = 2) :
    ∃ (n : ℕ) (e : Fin (n + 3) ≃ V), ∀ s : Finset (Fin (n + 3)),
      s.map e.toEmbedding ∈ A.faces ↔ s.Nonempty ∧ ∃ i, s ⊆ {i, i + 1} := by
  obtain ⟨n, e, he⟩ := A.edgeGraph.exists_cyclic_labels_of_two_neighbors hc hdegree
  refine ⟨n, e, ?_⟩
  intro s
  constructor
  · intro hs
    have hne : s.Nonempty := Finset.map_nonempty.mp (A.isRelLowerSet_faces hs).1
    refine ⟨hne, ?_⟩
    rcases (A.mem_faces_iff_singleton_or_edge hdim _).mp hs with
      ⟨x, hx⟩ | ⟨x, y, hxy, hxyface⟩
    · have hsx : s = {e.symm x} := by
        apply Finset.map_injective e.toEmbedding
        simpa only [Finset.map_singleton, Equiv.coe_toEmbedding, e.apply_symm_apply] using hx
      exact ⟨e.symm x, hsx ▸ Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)⟩
    · obtain ⟨i, hi⟩ := (he x y).mp hxy
      have hpair : ({x, y} : Finset V) = {e i, e (i + 1)} := by
        rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Finset.pair_comm _ _
      have hsi : s = {i, i + 1} := by
        apply Finset.map_injective e.toEmbedding
        simpa only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding] using
          hxyface.trans hpair
      exact ⟨i, hsi ▸ Finset.Subset.refl _⟩
  · rintro ⟨hne, i, hsi⟩
    have hi : A.edgeGraph.Adj (e i) (e (i + 1)) :=
      (he _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩
    apply (A.isRelLowerSet_faces hi.2).2 _ (Finset.map_nonempty.mpr hne)
    simpa only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding] using
      (Finset.map_subset_map.mpr hsi : s.map e.toEmbedding ⊆
        ({i, i + 1} : Finset (Fin (n + 3))).map e.toEmbedding)

end AbstractSimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

omit [DecidableEq E] in

theorem finite_vertices_of_finite_faces (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) : K.vertices.Finite :=
  hfinite.preimage Finset.singleton_injective.injOn

theorem reachable_vertices_of_mem_face (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (u v : K.vertices)
    (hu : u.val ∈ s) (hv : v.val ∈ s) :
    K.vertexAbstractComplex.edgeGraph.Reachable u v := by
  by_cases huv : u = v
  · exact huv ▸ SimpleGraph.Reachable.refl u
  · apply SimpleGraph.Adj.reachable
    refine ⟨huv, ?_⟩
    change ({u, v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
    simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
    exact K.down_closed hs (by simpa only [Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro hu hv) (Finset.insert_nonempty _ _)

variable [FiniteDimensional ℝ E]

theorem preconnected_edgeGraph_of_isPreconnected (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (hc : IsPreconnected K.space) :
    K.vertexAbstractComplex.edgeGraph.Preconnected := by
  classical
  intro u v
  let G := K.vertexAbstractComplex.edgeGraph
  let r : E → ℝ := fun x => if hx : x ∈ K.vertices then
    if G.Reachable u ⟨x, hx⟩ then 0 else 1 else 0
  have hr (x : K.vertices) : r x = if G.Reachable u x then 0 else 1 := by
    simp only [r, dif_pos x.property]
  have hrrange : ∀ x, r x ∈ ({0, 1} : Set ℝ) := by
    intro x
    dsimp only [r]
    split_ifs <;> simp
  obtain ⟨f, hf, hfv⟩ := K.exists_affineOnFaces_eqOn_vertices r
  have hfrange : MapsTo f K.space ({0, 1} : Set ℝ) := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha⟩ := K.nonempty_of_mem_faces hs
    have hsvertices : (s : Set E) ⊆ K.vertices := by
      rw [vertices_eq]
      exact subset_biUnion_of_mem hs
    let a' : K.vertices := ⟨a, hsvertices ha⟩
    obtain ⟨b, hb⟩ := hf s hs
    have heq : EqOn b.toAffineMap (AffineMap.const ℝ E (r a)) (s : Set E) := by
      intro y hy
      let y' : K.vertices := ⟨y, hsvertices hy⟩
      have hya : G.Reachable y' a' := K.reachable_vertices_of_mem_face hs y' a' hy ha
      have hre : G.Reachable u y' ↔ G.Reachable u a' :=
        ⟨fun h => h.trans hya, fun h => h.trans hya.symm⟩
      have hray : r y = r a := by
        change r y' = r a'
        rw [hr, hr, hre]
      exact (hb (subset_convexHull ℝ _ hy)).symm.trans ((hfv (hsvertices hy)).trans hray)
    have hfx : f x = r a := (hb hxs).trans
      (AffineMap.eqOn_affineSpan heq (convexHull_subset_affineSpan _ hxs))
    rw [hfx]
    exact hrrange a
  have hconst : f u = f v := hc.constant_of_mapsTo ((finite_singleton (1 : ℝ)).insert 0).isDiscrete
    (hf.continuousOn hfinite) hfrange
      (vertices_subset_space u.property) (vertices_subset_space v.property)
  rw [hfv u.property, hfv v.property, hr, hr,
    if_pos (SimpleGraph.Reachable.refl u)] at hconst
  by_contra hnot
  rw [if_neg hnot] at hconst
  exact zero_ne_one hconst

theorem connected_edgeGraph_of_isConnected (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (hc : IsConnected K.space) :
    K.vertexAbstractComplex.edgeGraph.Connected := by
  obtain ⟨x, hx⟩ := hc.1
  obtain ⟨s, hs, _⟩ := mem_space_iff.mp hx
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hvK : v ∈ K.vertices := by
    rw [vertices_eq]
    exact mem_iUnion₂.mpr ⟨s, hs, hv⟩
  let : Nonempty K.vertices := ⟨⟨v, hvK⟩⟩
  exact ⟨K.preconnected_edgeGraph_of_isPreconnected hfinite hc.2⟩

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

theorem faceLink_faceLink (K : SimplicialComplex 𝕜 E) (s t : Finset E)
    (hst : Disjoint s t) : (K.faceLink s).faceLink t = K.faceLink (s ∪ t) := by
  ext u
  change ((u ∈ K.faces ∧ Disjoint s u ∧ s ∪ u ∈ K.faces) ∧ Disjoint t u ∧
      (t ∪ u ∈ K.faces ∧ Disjoint s (t ∪ u) ∧ s ∪ (t ∪ u) ∈ K.faces)) ↔
    (u ∈ K.faces ∧ Disjoint (s ∪ t) u ∧ (s ∪ t) ∪ u ∈ K.faces)
  constructor
  · rintro ⟨hu, htu, hstu⟩
    exact ⟨hu.1, Finset.disjoint_union_left.mpr ⟨hu.2.1, htu⟩,
      by simpa only [Finset.union_assoc] using hstu.2.2⟩
  · rintro ⟨hu, hsu, hstu⟩
    obtain ⟨hsu, htu⟩ := Finset.disjoint_union_left.mp hsu
    have hne := K.nonempty_of_mem_faces hu
    refine ⟨⟨hu, hsu, ?_⟩, htu, ?_, Finset.disjoint_union_right.mpr ⟨hst, hsu⟩, ?_⟩
    · exact K.down_closed hstu
        (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl u))
        (Finset.union_nonempty.mpr (Or.inr hne))
    · exact K.down_closed hstu
        (Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl u))
        (Finset.union_nonempty.mpr (Or.inr hne))
    · simpa only [Finset.union_assoc] using hstu

theorem edgeGraph_adj_iff_mem_faceLink (K : SimplicialComplex 𝕜 E) (u v : K.vertices) :
    K.vertexAbstractComplex.edgeGraph.Adj u v ↔ v.val ∈ (K.faceLink {u.val}).vertices := by
  change (u ≠ v ∧ ({u, v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces) ↔
    ({v.val} ∈ K.faces ∧ Disjoint ({u.val} : Finset E) {v.val} ∧
      ({u.val} : Finset E) ∪ {v.val} ∈ K.faces)
  simp only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype,
    Finset.singleton_union, Finset.disjoint_singleton_left, Finset.mem_singleton]
  constructor
  · rintro ⟨huv, hface⟩
    exact ⟨v.property, fun h => huv (Subtype.ext h), hface⟩
  · rintro ⟨_, huv, hface⟩
    exact ⟨fun h => huv (congrArg Subtype.val h), hface⟩

theorem image_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E) (u : K.vertices) :
    Subtype.val '' K.vertexAbstractComplex.edgeGraph.neighborSet u =
      (K.faceLink {u.val}).vertices := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (K.edgeGraph_adj_iff_mem_faceLink u v).mp hv
  · intro hx
    let v : K.vertices := ⟨x, (K.faceLink_vertices_subset {u.val} hx).1⟩
    exact ⟨v, (K.edgeGraph_adj_iff_mem_faceLink u v).mpr hx, rfl⟩

theorem ncard_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E) (u : K.vertices) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink {u.val}).vertices.ncard := by
  rw [← K.image_edgeGraph_neighborSet u, ncard_image_of_injective _ Subtype.val_injective]

theorem ncard_faceLink_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E)
    (s : Finset E) (u : (K.faceLink s).vertices) :
    ((K.faceLink s).vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink (s ∪ {u.val})).vertices.ncard := by
  rw [(K.faceLink s).ncard_edgeGraph_neighborSet u,
    K.faceLink_faceLink s {u.val} u.property.2.1]

end Geometry.SimplicialComplex

end

section

open Set

namespace AbstractSimplicialComplex

variable {ι κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι} {B : AbstractSimplicialComplex κ}

theorem RadialEmbedding.complex_eq_of_reindex (v : A.RadialEmbedding E)
    (w : B.RadialEmbedding E) (e : κ ≃ ι)
    (hfaces : ∀ s : Finset κ, s ∈ B.faces ↔ s.map e.toEmbedding ∈ A.faces)
    (hvertices : ∀ i, w.val i = v.val (e i)) : w.complex = v.complex := by
  classical
  have himage : ∀ s : Finset κ, w.val '' (s : Set κ) =
      v.val '' (s.map e.toEmbedding : Set ι) := by
    intro s
    simp only [Finset.coe_map, image_image, Equiv.coe_toEmbedding, ← hvertices]
  ext t
  rw [w.complex_faces, v.complex_faces]
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨s.map e.toEmbedding, (hfaces s).mp hs, ht.trans (himage s)⟩
  · rintro ⟨s, hs, ht⟩
    obtain ⟨r, hr⟩ := e.finsetCongr.surjective s
    have hr' : r.map e.toEmbedding = s := hr
    refine ⟨r, (hfaces r).mpr (hr'.symm ▸ hs), ?_⟩
    exact ht.trans (hr' ▸ (himage r).symm)

theorem RadialEmbedding.cone_eq_of_reindex (v : A.RadialEmbedding E)
    (w : B.RadialEmbedding E) (e : κ ≃ ι)
    (hfaces : ∀ s : Finset κ, s ∈ B.faces ↔ s.map e.toEmbedding ∈ A.faces)
    (hvertices : ∀ i, w.val i = v.val (e i)) : w.cone = v.cone := by
  classical
  have he := v.complex_eq_of_reindex w e hfaces hvertices
  ext t
  change (t.Nonempty ∧ (t.erase 0 = ∅ ∨ t.erase 0 ∈ w.complex.faces)) ↔
    (t.Nonempty ∧ (t.erase 0 = ∅ ∨ t.erase 0 ∈ v.complex.faces))
  rw [he]

theorem RadialEmbedding.subtype_basis_span_cone_space (v : A.RadialEmbedding E)
    (hv : LinearIndependent ℝ v.val) :
    (Submodule.span ℝ (range v.val)).subtype ''
      (A.basisRadialEmbedding (Module.Basis.span hv)).cone.space = v.cone.space := by
  let V := Submodule.span ℝ (range v.val)
  let b : Module.Basis ι ℝ V := Module.Basis.span hv
  have hb : (fun i => V.subtype (b i)) = v.val :=
    funext (fun i => Module.Basis.coe_span_apply hv i)
  change V.subtype '' (A.basisRadialEmbedding b).cone.space = v.cone.space
  simp only [RadialEmbedding.cone_space, image_iUnion, V.subtype.image_convexHull,
    image_insert_eq, map_zero, image_image, basisRadialEmbedding, hb]

end AbstractSimplicialComplex

end

section

open Set

section Algebraic

variable {𝕜 ι E F : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

theorem AffineIndependent.linearIndependent_collapse_direction {v : ι → E}
    (hv : AffineIndependent 𝕜 v) {s : Set ι} (hs : s.Nonempty) {p : E}
    (hp : p ∈ affineSpan 𝕜 (v '' s)) (Q : E →ₗ[𝕜] F)
    (hker : Q.ker = (affineSpan 𝕜 (v '' s)).direction) :
    LinearIndependent 𝕜 (fun i : {i // i ∉ s} => Q (v i - p)) := by
  classical
  obtain ⟨i0, hi0⟩ := hs
  let v0 : {i : ι // i ≠ i0} → E := fun i => v i - v i0
  have hv0 : LinearIndependent 𝕜 v0 := by
    simpa only [vsub_eq_sub] using
      (affineIndependent_iff_linearIndependent_vsub 𝕜 v i0).mp hv
  let outer : {i // i ∉ s} → {i : ι // i ≠ i0} :=
    fun i => ⟨i.val, fun he => i.property (he ▸ hi0)⟩
  have hout : Function.Injective outer := by
    intro i j hij
    exact Subtype.ext (congrArg (fun z : {i : ι // i ≠ i0} => z.val) hij)
  let central : Set {i : ι // i ≠ i0} := {i | i.val ∈ s}
  have hd : Disjoint (range outer) central := by
    apply disjoint_left.mpr
    rintro _ ⟨i, rfl⟩ hi
    exact i.property hi
  have hdir : (affineSpan 𝕜 (v '' s)).direction =
      Submodule.span 𝕜 (v0 '' central) := by
    rw [direction_affineSpan, vectorSpan_image_eq_span_vsub_set_right_ne 𝕜 v hi0]
    congr 1
    rw [image_image]
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi.2⟩, hi.1, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.val, ⟨hi, i.property⟩, rfl⟩
  have hmap : LinearIndependent 𝕜 (Q ∘ (v0 ∘ outer)) := by
    apply (hv0.comp outer hout).map
    rw [hker, hdir, Set.range_comp]
    exact hv0.disjoint_span_image hd
  have hpa : Q (p - v i0) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact (affineSpan 𝕜 (v '' s)).vsub_mem_direction hp
      (mem_affineSpan 𝕜 (mem_image_of_mem v hi0))
  have he : (fun i : {i // i ∉ s} => Q (v i - p)) = Q ∘ (v0 ∘ outer) := by
    funext i
    change Q (v i - p) = Q (v i - v i0)
    have hvp : v i - p = (v i - v i0) - (p - v i0) := by abel
    rw [hvp, map_sub, hpa, sub_zero]
  rwa [he]

end Algebraic

section Orthogonal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AffineIndependent.linearIndependent_orthogonal_normal {v : ι → E}
    (hv : AffineIndependent ℝ v) {s : Set ι} (hs : s.Nonempty) {p : E}
    (hp : p ∈ affineSpan ℝ (v '' s)) :
    LinearIndependent ℝ (fun i : {i // i ∉ s} =>
      (affineSpan ℝ (v '' s)).directionᗮ.orthogonalProjectionOnto (v i - p)) := by
  apply hv.linearIndependent_collapse_direction hs hp
  exact Submodule.ker_orthogonalProjectionOnto.trans
    (Submodule.orthogonal_orthogonal _)

end Orthogonal

end

section

open Set AbstractSimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def normalAffineProjection (L : Submodule ℝ E) (p : E) : E →ᵃ[ℝ] ↥(Lᗮ) :=
  Lᗮ.orthogonalProjectionOnto.toLinearMap.toAffineMap.comp
    (AffineEquiv.vaddConst ℝ p).symm.toAffineMap

theorem normalAffineProjection_eq_zero (L : Submodule ℝ E) (p : E) {x : E}
    (hx : x - p ∈ L) : L.normalAffineProjection p x = 0 :=
  L.orthogonalProjectionOnto_orthogonal_apply_eq_zero hx

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem linearIndependent_faceLink_normal (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    LinearIndependent ℝ (fun v : (K.faceLink s).vertices =>
      (affineSpan ℝ (s : Set E)).direction.normalAffineProjection p v) := by
  let central : Set K.vertices := {v | v.val ∈ s}
  have hsvertices : (s : Set E) ⊆ K.vertices := by
    intro x hx
    rw [vertices_eq]
    exact mem_iUnion₂.mpr ⟨s, hs, hx⟩
  have hcentral : ((↑) : K.vertices → E) '' central = (s : Set E) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hsvertices hx⟩, hx, rfl⟩
  have hcne : central.Nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces hs
    exact ⟨⟨x, hsvertices hx⟩, hx⟩
  have hp' : p ∈ affineSpan ℝ (((↑) : K.vertices → E) '' central) := by
    rwa [hcentral]
  have hnormal := hv.linearIndependent_orthogonal_normal hcne hp'
  rw [hcentral] at hnormal
  let outer : (K.faceLink s).vertices → {v : K.vertices // v ∉ central} :=
    fun v => ⟨⟨v.val, (K.faceLink_vertices_subset s v.property).1⟩,
      (K.faceLink_vertices_subset s v.property).2⟩
  have houter : Function.Injective outer := by
    intro v w hvw
    exact Subtype.ext (congrArg
      (fun z : {v : K.vertices // v ∉ central} => z.val.val) hvw)
  exact hnormal.comp outer houter

noncomputable def faceNormalRadialEmbedding (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    (K.faceLink s).vertexAbstractComplex.RadialEmbedding
      ↥((affineSpan ℝ (s : Set E)).directionᗮ) :=
  ⟨_, (K.faceLink s).vertexAbstractComplex.isRadialEmbedding_of_linearIndependent
    (K.linearIndependent_faceLink_normal hv hs hp)⟩

theorem normal_image_closedFaceStar (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    (affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
      (K.closedFaceStar s).space =
        (RadialEmbedding.cone (K.faceNormalRadialEmbedding hv hs hp)).space := by
  apply K.affine_image_closedFaceStar_eq_radialCone hs
  intro x hx
  exact Submodule.normalAffineProjection_eq_zero _ p
    ((affineSpan ℝ (s : Set E)).vsub_mem_direction (mem_affineSpan ℝ hx) hp)

end Geometry.SimplicialComplex

end

section

open Set
open scoped Pointwise

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def normalTangentEquiv (L : Submodule ℝ E) : E ≃L[ℝ] (↥(Lᗮ) × L) where
  toFun x := (Lᗮ.orthogonalProjectionOnto x, L.orthogonalProjectionOnto x)
  invFun y := (y.1 : E) + (y.2 : E)
  left_inv x := by
    change Lᗮ.starProjection x + L.starProjection x = x
    rw [add_comm, L.starProjection_add_starProjection_orthogonal]
  right_inv y := by
    apply Prod.ext
    · change Lᗮ.orthogonalProjectionOnto ((y.1 : E) + (y.2 : E)) = y.1
      rw [map_add, Lᗮ.orthogonalProjectionOnto_mem_subspace_eq_self,
        L.orthogonalProjectionOnto_orthogonal_apply_eq_zero y.2.property, add_zero]
    · change L.orthogonalProjectionOnto ((y.1 : E) + (y.2 : E)) = y.2
      rw [map_add, L.orthogonalProjectionOnto_apply_of_mem_orthogonal y.1.property,
        L.orthogonalProjectionOnto_mem_subspace_eq_self, zero_add]
  map_add' x y := by ext <;> simp only [map_add, Prod.fst_add, Prod.snd_add]
  map_smul' c x := by ext <;> simp only [map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
  continuous_toFun := Lᗮ.orthogonalProjectionOnto.continuous.prodMk
    L.orthogonalProjectionOnto.continuous
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)

noncomputable def normalTangentCoordinates (L : Submodule ℝ E) (p : E) :
    E ≃ₜ (↥(Lᗮ) × L) where
  toFun x := L.normalTangentEquiv (x - p)
  invFun y := L.normalTangentEquiv.symm y + p
  left_inv x := by
    dsimp only
    rw [ContinuousLinearEquiv.symm_apply_apply, sub_add_cancel]
  right_inv y := by
    dsimp only
    rw [add_sub_cancel_right, ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := L.normalTangentEquiv.continuous.comp (continuous_id.sub continuous_const)
  continuous_invFun := L.normalTangentEquiv.symm.continuous.add continuous_const

theorem image_normalTangentCoordinates_add (L : Submodule ℝ E) (p : E) (S : Set E) :
    L.normalTangentCoordinates p '' (S + (L : Set E)) =
      (L.normalAffineProjection p '' S) ×ˢ (univ : Set L) := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, l, hl, rfl⟩, rfl⟩
    refine ⟨⟨x, hx, ?_⟩, mem_univ _⟩
    change Lᗮ.orthogonalProjectionOnto (x - p) =
      Lᗮ.orthogonalProjectionOnto ((x + l) - p)
    have he : (x + l) - p = (x - p) + l := by abel
    rw [he, map_add, L.orthogonalProjectionOnto_orthogonal_apply_eq_zero hl, add_zero]
  · rintro ⟨⟨x, hx, hn⟩, _⟩
    let l : L := y.2 - L.orthogonalProjectionOnto (x - p)
    refine ⟨x + (l : E), ⟨x, hx, l, l.property, rfl⟩, ?_⟩
    apply Prod.ext
    · change Lᗮ.orthogonalProjectionOnto ((x + (l : E)) - p) = y.1
      have he : (x + (l : E)) - p = (x - p) + l := by abel
      rw [he, map_add, L.orthogonalProjectionOnto_orthogonal_apply_eq_zero l.property, add_zero]
      exact hn
    · change L.orthogonalProjectionOnto ((x + (l : E)) - p) = y.2
      have he : (x + (l : E)) - p = (x - p) + l := by abel
      rw [he, map_add, L.orthogonalProjectionOnto_mem_subspace_eq_self]
      exact add_sub_cancel _ _

end Submodule

end

section

open Set
open scoped Pointwise Topology

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_pos_smul_add_mem_of_intrinsicInterior {C : Set E} {p l : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hl : l ∈ (affineSpan ℝ C).direction) :
    ∃ r : ℝ, 0 < r ∧ r • l + p ∈ C := by
  obtain ⟨q, hq, rfl⟩ := mem_intrinsicInterior.mp hp
  let f : ℝ → affineSpan ℝ C := fun r =>
    ⟨r • l + (q : E), (affineSpan ℝ C).vadd_mem_of_mem_direction
      ((affineSpan ℝ C).direction.smul_mem r hl) q.property⟩
  have hf : Continuous f :=
    ((continuous_id.smul continuous_const).add continuous_const).subtype_mk _
  have hzero : f 0 = q := by apply Subtype.ext; simp [f]
  have hpre : f ⁻¹' ((↑) ⁻¹' C : Set (affineSpan ℝ C)) ∈ 𝓝 (0 : ℝ) :=
    hf.continuousAt.preimage_mem_nhds (hzero ▸ mem_interior_iff_mem_nhds.mp hq)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r / 2, half_pos hr, hb ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    using half_lt_self hr

theorem exists_pos_secant_of_mem_add_direction {C S : Set E} {p : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hstar : ∀ q ∈ C, StarConvex ℝ q S)
    {x y : E} (hx : x ∈ S + ((affineSpan ℝ C).direction : Set E))
    (hy : y ∈ S + ((affineSpan ℝ C).direction : Set E)) :
    ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y) := by
  obtain ⟨x, hx, l, hl, rfl⟩ := hx
  obtain ⟨y, hy, m, hm, rfl⟩ := hy
  obtain ⟨t, ht, htc⟩ := exists_pos_smul_add_mem_of_intrinsicInterior hp
    ((affineSpan ℝ C).direction.sub_mem hl hm)
  have hden : 0 < 1 + t := by linarith
  let a : ℝ := 1 / (1 + t)
  let r : ℝ := t / (1 + t)
  have ha : 0 < a := div_pos one_pos hden
  have hr : 0 < r := div_pos ht hden
  have hsum : a + r = 1 := by
    dsimp only [a, r]
    rw [← add_div, div_self hden.ne']
  have har : a * t = r := by dsimp only [a, r]; ring
  refine ⟨r, hr, a • (t • (l - m) + p) + r • x,
    hstar _ htc hx ha.le hr.le hsum, a • p + r • y,
    hstar _ (intrinsicInterior_subset hp) hy ha.le hr.le hsum, ?_⟩
  rw [smul_add, smul_smul, har]
  simp only [smul_add, smul_sub]
  abel

end Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

end

section

open Set
open scoped Pointwise

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem injOn_of_secant_rescaling (Q : E →ₗ[ℝ] F) {S T : Set E}
    (hQ : InjOn Q S)
    (hscale : ∀ x ∈ T, ∀ y ∈ T,
      ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y)) :
    InjOn Q T := by
  intro x hx y hy he
  obtain ⟨r, hr, u, hu, v, hv, huv⟩ := hscale x hx y hy
  have hzero : Q (u - v) = 0 := by
    rw [huv, map_smul, map_sub, he, sub_self, smul_zero]
  have huv' : u = v := hQ hu hv (sub_eq_zero.mp (by simpa only [map_sub] using hzero))
  have hscaled : r • (x - y) = 0 := by rw [← huv, huv', sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hscaled).resolve_left hr.ne')

end LinearMap

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem injOn_add_direction_iff {C S : Set E} {p : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hstar : ∀ q ∈ C, StarConvex ℝ q S)
    (Q : E →ₗ[ℝ] F) :
    InjOn Q (S + ((affineSpan ℝ C).direction : Set E)) ↔ InjOn Q S := by
  constructor
  · intro h
    apply h.mono
    intro x hx
    exact ⟨x, hx, 0, (affineSpan ℝ C).direction.zero_mem, add_zero x⟩
  · intro h
    exact Q.injOn_of_secant_rescaling h (fun _ hx _ hy =>
      exists_pos_secant_of_mem_add_direction hp hstar hx hy)

end Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [AddCommGroup F] [Module ℝ F]

theorem injOn_closedFaceStar_tangent_iff (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (Q : E →ₗ[ℝ] F) :
    InjOn Q ((K.closedFaceStar s).space +
      ((affineSpan ℝ (s : Set E)).direction : Set E)) ↔
      InjOn Q (K.closedFaceStar s).space := by
  have hne : (convexHull ℝ (s : Set E)).Nonempty :=
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
  obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _) hne
  simpa only [affineSpan_convexHull] using Set.injOn_add_direction_iff hp
    (fun _ hq => K.starConvex_closedFaceStar s hq) Q

end Geometry.SimplicialComplex

end

section

open Set
open scoped BigOperators

namespace Module.Basis

variable {ι E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def nonnegativeCone (b : Basis ι ℝ E) (s : Set ι) : ConvexCone ℝ E where
  carrier := {x | (∀ i, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i = 0}
  smul_mem' := by
    intro c hc x hx
    constructor
    · intro i
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using mul_nonneg hc.le (hx.1 i)
    · intro i hi
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hx.2 i hi, mul_zero]
  add_mem' := by
    intro x hx y hy
    constructor
    · intro i
      simpa only [map_add, Finsupp.add_apply] using add_nonneg (hx.1 i) (hy.1 i)
    · intro i hi
      simp only [map_add, Finsupp.add_apply, hx.2 i hi, hy.2 i hi, add_zero]

variable [Finite ι]

theorem nonnegativeCone_eq_hull (b : Basis ι ℝ E) (s : Set ι) :
    b.nonnegativeCone s = ConvexCone.hull ℝ (insert 0 (b '' s)) := by
  classical
  let := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    let C := ConvexCone.hull ℝ (insert (0 : E) (b '' s))
    have hzero : (0 : E) ∈ C := ConvexCone.subset_hull (mem_insert _ _)
    have hterm : ∀ i : ι, b.repr x i • b i ∈ C := by
      intro i
      by_cases hi : i ∈ s
      · rcases (hx.1 i).eq_or_lt with hc | hc
        · rw [← hc, zero_smul]
          exact hzero
        · exact C.smul_mem hc (ConvexCone.subset_hull (mem_insert_of_mem _ ⟨i, hi, rfl⟩))
      · rw [hx.2 i hi, zero_smul]
        exact hzero
    rw [← b.sum_repr x]
    exact Finset.sum_induction _ (fun y => y ∈ C) (fun _ _ hx hy => C.add_mem hx hy)
      hzero (fun i _ => hterm i)
  · apply ConvexCone.hull_min
    rintro x (rfl | hx)
    · constructor <;> simp
    · obtain ⟨i, hi, rfl⟩ := hx
      constructor
      · intro j
        simp only [repr_self_apply]
        split_ifs <;> norm_num
      · intro j hj
        have hij : i ≠ j := fun he => hj (he ▸ hi)
        simp only [repr_self_apply, if_neg hij]

theorem exists_pos_smul_mem_simplex_of_mem_nonnegativeCone (b : Basis ι ℝ E)
    {s : Set ι} {x : E} (hx : x ∈ b.nonnegativeCone s) :
    ∃ r : ℝ, 0 < r ∧ ∃ y ∈ convexHull ℝ (insert 0 (b '' s)), r • y = x := by
  rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull] at hx
  exact (ConvexCone.mem_hull_of_convex (convex_convexHull ℝ _)).mp hx

end Module.Basis

end

section

open Set

namespace Module.Basis

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def secantCone (b : Basis ι ℝ E) (s t : Set ι) : Set E :=
  {x | (∀ i ∉ t, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i ≤ 0}

theorem isClosed_secantCone [Finite ι] (b : Basis ι ℝ E) (s t : Set ι) :
    IsClosed (b.secantCone s t) := by
  classical
  let := Fintype.ofFinite ι
  have hc : ∀ i, Continuous (fun x : E => b.repr x i) :=
    fun i => (continuous_apply i).comp b.equivFunL.continuous
  change IsClosed {x : E | (∀ i ∉ t, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i ≤ 0}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter (fun i => isClosed_iInter (fun _ : i ∉ t =>
    isClosed_le (continuous_const (y := (0 : ℝ))) (hc i)))).inter
    (isClosed_iInter (fun i => isClosed_iInter (fun _ : i ∉ s =>
      isClosed_le (hc i) (continuous_const (y := (0 : ℝ))))))

theorem smul_mem_secantCone (b : Basis ι ℝ E) {s t : Set ι} {x : E}
    (hx : x ∈ b.secantCone s t) {r : ℝ} (hr : 0 ≤ r) : r • x ∈ b.secantCone s t := by
  constructor
  · intro i hi
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using mul_nonneg hr (hx.1 i hi)
  · intro i hi
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
      mul_nonpos_of_nonneg_of_nonpos hr (hx.2 i hi)

theorem mem_secantCone_iff [Finite ι] (b : Basis ι ℝ E) (s t : Set ι) (z : E) :
    z ∈ b.secantCone s t ↔ ∃ x ∈ b.nonnegativeCone s,
      ∃ y ∈ b.nonnegativeCone t, z = x - y := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro hz
    let x := b.equivFunL.symm (fun i => max (b.repr z i) 0)
    let y := b.equivFunL.symm (fun i => max (-b.repr z i) 0)
    have hx : ∀ i, b.repr x i = max (b.repr z i) 0 :=
      fun i => congrFun (b.equivFunL.apply_symm_apply _) i
    have hy : ∀ i, b.repr y i = max (-b.repr z i) 0 :=
      fun i => congrFun (b.equivFunL.apply_symm_apply _) i
    refine ⟨x, ⟨fun i => ?_, fun i hi => ?_⟩,
      y, ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
    · rw [hx]
      exact le_max_right _ _
    · rw [hx, max_eq_right (hz.2 i hi)]
    · rw [hy]
      exact le_max_right _ _
    · rw [hy, max_eq_right (neg_nonpos.mpr (hz.1 i hi))]
    · apply b.repr.injective
      ext i
      simp only [map_sub, Finsupp.sub_apply, hx, hy, max_zero_sub_eq_self]
  · rintro ⟨x, hx, y, hy, rfl⟩
    constructor
    · intro i hi
      simpa only [map_sub, Finsupp.sub_apply, hy.2 i hi, sub_zero] using hx.1 i
    · intro i hi
      simpa only [map_sub, Finsupp.sub_apply, hx.2 i hi, zero_sub] using neg_nonpos.mpr (hy.1 i)

theorem eq_zero_of_mem_secantCone_of_injOn [Finite ι] (b : Basis ι ℝ E) {s t : Set ι}
    (Q : E →L[ℝ] F)
    (hQ : InjOn Q (convexHull ℝ (insert 0 (b '' s)) ∪ convexHull ℝ (insert 0 (b '' t))))
    {z : E} (hz : z ∈ b.secantCone s t) (hQz : Q z = 0) : z = 0 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (b.mem_secantCone_iff s t z).mp hz
  obtain ⟨r, hr, u, hu, hru⟩ := b.exists_pos_smul_mem_simplex_of_mem_nonnegativeCone hx
  obtain ⟨q, hq, v, hv, hqv⟩ := b.exists_pos_smul_mem_simplex_of_mem_nonnegativeCone hy
  have hsum : 0 < r + q := add_pos hr hq
  let u' : E := (r / (r + q)) • u
  let v' : E := (q / (r + q)) • v
  have hu' : u' ∈ convexHull ℝ (insert 0 (b '' s)) :=
    (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (mem_insert _ _)) hu
      ⟨div_nonneg hr.le hsum.le, (div_le_one hsum).mpr (by linarith)⟩
  have hv' : v' ∈ convexHull ℝ (insert 0 (b '' t)) :=
    (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (mem_insert _ _)) hv
      ⟨div_nonneg hq.le hsum.le, (div_le_one hsum).mpr (by linarith)⟩
  have hru' : (r + q) • u' = x := by
    dsimp only [u']
    rw [smul_smul, mul_div_cancel₀ _ hsum.ne', hru]
  have hqv' : (r + q) • v' = y := by
    dsimp only [v']
    rw [smul_smul, mul_div_cancel₀ _ hsum.ne', hqv]
  have he : (r + q) • Q u' = (r + q) • Q v' := by
    rw [← map_smul, ← map_smul, hru', hqv']
    exact sub_eq_zero.mp (by simpa only [map_sub] using hQz)
  have he' : Q u' = Q v' := by
    have h := congrArg (fun w : F => (r + q)⁻¹ • w) he
    simpa only [inv_smul_smul₀ hsum.ne'] using h
  have huv := hQ (Or.inl hu') (Or.inr hv') he'
  have hxy : x = y := hru'.symm.trans ((congrArg (fun w : E => (r + q) • w) huv).trans hqv')
  exact sub_eq_zero.mpr hxy

end Module.Basis

end

section

open Set

namespace Module.Basis

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem secantCone_self_eq_span (b : Basis ι ℝ E) (s : Set ι) :
    b.secantCone s s = (Submodule.span ℝ (b '' s) : Set E) := by
  ext x
  constructor
  · intro hx
    apply b.mem_span_image.mpr
    intro i hi
    by_contra his
    exact Finsupp.mem_support_iff.mp hi (le_antisymm (hx.2 i his) (hx.1 i his))
  · intro hx
    have hs := b.mem_span_image.mp hx
    have hz : ∀ i ∉ s, b.repr x i = 0 := by
      intro i hi
      exact Finsupp.notMem_support_iff.mp (fun h => hi (hs h))
    exact ⟨fun i hi => (hz i hi).ge, fun i hi => (hz i hi).le⟩

theorem injOn_span_of_injOn_simplex [Finite ι] (b : Basis ι ℝ E) {s : Set ι}
    (Q : E →L[ℝ] F) (hQ : InjOn Q (convexHull ℝ (insert 0 (b '' s)))) :
    InjOn Q (Submodule.span ℝ (b '' s)) := by
  intro x hx y hy he
  apply sub_eq_zero.mp
  apply b.eq_zero_of_mem_secantCone_of_injOn (s := s) (t := s) Q
    (by simpa only [union_self] using hQ)
  · rw [b.secantCone_self_eq_span]
    exact (Submodule.span ℝ (b '' s)).sub_mem hx hy
  · rw [map_sub, he, sub_self]

end Module.Basis

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E}

private theorem linear_image_convexHull (Q : E →L[ℝ] F) (s : Set E) :
    Q '' convexHull ℝ s = convexHull ℝ (Q '' s) := by
  simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using
    Q.toLinearMap.toAffineMap.image_convexHull s

theorem linearIndependent_linear_face_image (Q : E →L[ℝ] F) {s : Finset E}
    (hlin : LinearIndependent ℝ ((↑) : s → E))
    (hQ : InjOn Q (Submodule.span ℝ (s : Set E))) :
    LinearIndependent ℝ ((↑) : ↥(Q '' (s : Set E)) → F) := by
  have hs : LinearIndepOn ℝ id (s : Set E) := hlin
  have hmap := hs.map_injOn Q.toLinearMap
    (by simpa only [image_id, ContinuousLinearMap.coe_coe] using hQ)
  simpa only [LinearIndepOn, Function.comp_def, id_eq, ContinuousLinearMap.coe_coe]
    using hmap.id_image

noncomputable def linearImage (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) : SimplicialComplex ℝ F := by
  classical
  refine { K.toPreAbstractSimplicialComplex.map Q with
    indep := ?_
    inter_subset_convexHull := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    have h := linearIndependent_linear_face_image Q (hlin s hs) (hspan s hs)
    change AffineIndependent ℝ ((↑) : ↥((s.image Q : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact h.affineIndependent
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ x ⟨hxs, hxt⟩
    simp only [Finset.coe_image] at hxs hxt ⊢
    rw [← linear_image_convexHull] at hxs hxt
    obtain ⟨y, hy, hyx⟩ := hxs
    obtain ⟨z, hz, hzx⟩ := hxt
    have he : y = z := hinj (convexHull_subset_space hs hy)
      (convexHull_subset_space ht hz) (hyx.trans hzx.symm)
    have hyinter := K.inter_subset_convexHull hs ht ⟨hy, he.symm ▸ hz⟩
    have hximage : x ∈ convexHull ℝ (Q '' ((s : Set E) ∩ t)) := by
      rw [← linear_image_convexHull]
      exact ⟨y, hyinter, hyx⟩
    apply convexHull_mono (s := Q '' ((s : Set E) ∩ t)) ?_ hximage
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩

theorem linearImage_faces [DecidableEq F]
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) :
    (K.linearImage hlin Q hspan hinj).faces =
      (fun s : Finset E => s.image Q) '' K.faces := by
  classical
  change (fun s : Finset E => @Finset.image E F (Classical.decEq F) Q s) '' K.faces = _
  congr 1
  funext s
  ext x
  simp only [Finset.mem_image]

theorem linearIndependent_linearImage_face
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) {t : Finset F} (ht : t ∈ (K.linearImage hlin Q hspan hinj).faces) :
    LinearIndependent ℝ ((↑) : t → F) := by
  classical
  rw [linearImage_faces] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  change LinearIndependent ℝ ((↑) : ↥((s.image Q : Finset F) : Set F) → F)
  rw [Finset.coe_image]
  exact linearIndependent_linear_face_image Q (hlin s hs) (hspan s hs)

theorem linearImage_space
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) :
    (K.linearImage hlin Q hspan hinj).space = Q '' K.space := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
    rw [linearImage_faces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [Finset.coe_image, ← linear_image_convexHull] at hyt
    obtain ⟨x, hx, hxy⟩ := hyt
    exact ⟨x, convexHull_subset_space hs hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    apply convexHull_subset_space (s := s.image Q)
      (show s.image Q ∈ (K.linearImage hlin Q hspan hinj).faces from
        (linearImage_faces hlin Q hspan hinj) ▸ mem_image_of_mem _ hs)
    rw [Finset.coe_image, ← linear_image_convexHull]
    exact mem_image_of_mem Q hxs

end Geometry.SimplicialComplex

end

section

open Set

namespace Module.Basis

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_secant_bound_of_injOn (b : Basis ι ℝ E)
    (faces : Set (Finset ι)) (Q : E →L[ℝ] F)
    (hQ : InjOn Q (⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι))))) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι)))),
      ∀ y ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι)))),
      c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  classical
  let := Fintype.ofFinite ι
  let := b.finiteDimensional_of_finite
  let C : Set E := ⋃ s ∈ faces, ⋃ t ∈ faces, b.secantCone (s : Set ι) (t : Set ι)
  have hclosed : IsClosed C :=
    (Set.toFinite faces).isClosed_biUnion (fun s _ =>
      (Set.toFinite faces).isClosed_biUnion (fun t _ => b.isClosed_secantCone s t))
  have hsmul : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r • x ∈ C := by
    intro x hx r hr
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr
      ⟨t, ht, b.smul_mem_secantCone hxt hr.le⟩⟩
  have hker : ∀ x ∈ C, Q x = 0 → x = 0 := by
    intro x hx he
    obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    apply b.eq_zero_of_mem_secantCone_of_injOn Q (hQ.mono ?_) hxt he
    exact union_subset (subset_iUnion₂_of_subset s hs Subset.rfl)
      (subset_iUnion₂_of_subset t ht Subset.rfl)
  obtain ⟨c, hc, hb⟩ := Q.exists_pos_norm_lower_bound_on_cone hclosed hsmul hker
  refine ⟨c, hc, fun x hx y hy => ?_⟩
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
  have hxc : x ∈ b.nonnegativeCone (s : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    exact ConvexCone.subset_hull hxs
  have hyc : y ∈ b.nonnegativeCone (t : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    exact ConvexCone.subset_hull hyt
  have hxy : x - y ∈ C := mem_iUnion₂.mpr ⟨s, hs, mem_iUnion₂.mpr ⟨t, ht,
    (b.mem_secantCone_iff s t (x - y)).mpr ⟨x, hxc, y, hyc, rfl⟩⟩⟩
  simpa only [map_sub] using hb (x - y) hxy

end Module.Basis

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {A : AbstractSimplicialComplex ι} {b : Module.Basis ι ℝ E}

theorem BasisRadialProjection.exists_pos_secant_bound (Q : A.BasisRadialProjection b F) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (A.basisRadialEmbedding b).cone.space,
      ∀ y ∈ (A.basisRadialEmbedding b).cone.space,
      c * ‖x - y‖ ≤ ‖Q.val x - Q.val y‖ := by
  have hQ := Q.injOn_basisCone
  rw [RadialEmbedding.cone_space] at hQ ⊢
  exact b.exists_pos_secant_bound_of_injOn (insert ∅ A.faces) Q.val hQ

end AbstractSimplicialComplex

end

section

open Set Geometry NormedSpace

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isRadialEmbedding_of_injOn_basisCone (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (Q : E →L[ℝ] F)
    (hQ : InjOn Q (A.basisRadialEmbedding b).cone.space) :
    A.IsRadialEmbedding (fun i => Q (b i)) := by
  classical
  let v := A.basisRadialEmbedding b
  let K := v.complex
  have hsimplex : ∀ s ∈ A.faces,
      convexHull ℝ (insert 0 (b '' (s : Set ι))) ⊆ v.cone.space := by
    intro s hs
    rw [v.cone_space]
    exact subset_iUnion₂_of_subset s (mem_insert_of_mem _ hs) Subset.rfl
  have hbase : K.space ⊆ v.cone.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact SimplicialComplex.convexHull_subset_space
      (SimplicialComplex.le_coneAtZero v.complex_linearIndependent v.complex_injOn_normalize hs) hxs
  have hzero : (0 : E) ∈ v.cone.space :=
    SimplicialComplex.vertices_subset_space
      (SimplicialComplex.zero_mem_coneAtZero_vertices
        v.complex_linearIndependent v.complex_injOn_normalize)
  have hvertices : ∀ i, b i ∈ v.cone.space := by
    intro i
    apply hbase
    apply SimplicialComplex.vertices_subset_space
    rw [v.complex_vertices]
    exact mem_range_self i
  have hspan : ∀ t ∈ K.faces, InjOn Q (Submodule.span ℝ (t : Set E)) := by
    intro t ht
    rw [v.complex_faces] at ht
    obtain ⟨s, hs, hts⟩ := ht
    change (t : Set E) = b '' (s : Set ι) at hts
    rw [hts]
    exact b.injOn_span_of_injOn_simplex Q (hQ.mono (hsimplex s hs))
  let L := K.linearImage v.complex_linearIndependent Q hspan (hQ.mono hbase)
  have hfaces : L.faces = {t : Finset F |
      ∃ s ∈ A.faces, (t : Set F) = (fun i => Q (b i)) '' (s : Set ι)} := by
    rw [SimplicialComplex.linearImage_faces, v.complex_faces_image, Set.image_image]
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, by simp only [Finset.coe_image, Set.image_image]; rfl⟩
    · rintro ⟨s, hs, he⟩
      refine ⟨s, hs, Finset.coe_injective ?_⟩
      simpa only [Finset.coe_image, Set.image_image] using
        (show (fun i => Q (v.val i)) '' (s : Set ι) = (t : Set F) from he.symm)
  refine ⟨fun i j he => b.injective (hQ (hvertices i) (hvertices j) he), L, hfaces,
    fun t ht => SimplicialComplex.linearIndependent_linearImage_face
      v.complex_linearIndependent Q hspan (hQ.mono hbase) ht, ?_⟩
  intro x hx y hy he
  rw [SimplicialComplex.linearImage_space] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨s', hs', hus⟩ := SimplicialComplex.mem_space_iff.mp hu
  obtain ⟨t', ht', hwt⟩ := SimplicialComplex.mem_space_iff.mp hw
  have hu0 : u ≠ 0 := fun he =>
    (v.complex_linearIndependent s' hs').zero_notMem_convexHull (he ▸ hus)
  have hw0 : w ≠ 0 := fun he =>
    (v.complex_linearIndependent t' ht').zero_notMem_convexHull (he ▸ hwt)
  have hQu : Q u ≠ 0 := fun he => hu0 (hQ (hbase hu) hzero (he.trans (map_zero Q).symm))
  have hQw : Q w ≠ 0 := fun he => hw0 (hQ (hbase hw) hzero (he.trans (map_zero Q).symm))
  rw [v.complex_faces] at hs' ht'
  obtain ⟨s, hs, hss'⟩ := hs'
  obtain ⟨t, ht, htt'⟩ := ht'
  have huc : u ∈ b.nonnegativeCone (s : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    apply ConvexCone.subset_hull
    exact convexHull_mono (subset_insert 0 (b '' (s : Set ι))) (hss' ▸ hus)
  have hwc : w ∈ b.nonnegativeCone (t : Set ι) := by
    rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull]
    apply ConvexCone.subset_hull
    exact convexHull_mono (subset_insert 0 (b '' (t : Set ι))) (htt' ▸ hwt)
  have hru : 0 < ‖Q u‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hQu)
  have hrw : 0 < ‖Q w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hQw)
  have hdir : ‖Q u‖⁻¹ • u = ‖Q w‖⁻¹ • w := by
    apply sub_eq_zero.mp
    apply b.eq_zero_of_mem_secantCone_of_injOn (s := s) (t := t) Q
      (hQ.mono (union_subset (hsimplex s hs) (hsimplex t ht)))
    · exact (b.mem_secantCone_iff _ _ _).mpr
        ⟨_, (b.nonnegativeCone s).smul_mem hru huc,
          _, (b.nonnegativeCone t).smul_mem hrw hwc, rfl⟩
    · simpa only [map_sub, map_smul, NormedSpace.normalize] using sub_eq_zero.mpr he
  have hnorm : normalize u = normalize w := by
    calc
      normalize u = normalize (‖Q u‖⁻¹ • u) := (normalize_smul_of_pos hru u).symm
      _ = normalize (‖Q w‖⁻¹ • w) := congrArg NormedSpace.normalize hdir
      _ = normalize w := normalize_smul_of_pos hrw w
  exact congrArg Q (v.complex_injOn_normalize hu hw hnorm)

end AbstractSimplicialComplex

end

section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem isInvertible_adjoint_comp_self_of_injective (J : F →L[ℝ] E)
    (hJ : Function.Injective J) : ((adjoint J).comp J).IsInvertible := by
  have hker : ((adjoint J).comp J).ker = ⊥ := by
    rw [ker_adjoint_comp_self, LinearMap.ker_eq_bot.mpr hJ]
  have hinj : Function.Injective ((adjoint J).comp J) := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective ((adjoint J).comp J) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective ((adjoint J).comp J) hker
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

def perpendicularFrame (J : F →L[ℝ] E) (P : E →L[ℝ] E) : F →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ E - P).comp J

noncomputable def frameProjectionFormula (J : F →L[ℝ] E) (P : E →L[ℝ] E) : E →L[ℝ] F :=
  (((adjoint (perpendicularFrame J P)).comp (perpendicularFrame J P)).inverse.comp
    (adjoint (perpendicularFrame J P))).comp (ContinuousLinearMap.id ℝ E - P)

omit [FiniteDimensional ℝ F] in

theorem injective_perpendicularFrame_of_rightInverse (Q : E →L[ℝ] F) (J : F →L[ℝ] E)
    (hJ : Function.RightInverse J Q) :
    Function.Injective (perpendicularFrame J Q.ker.starProjection) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  change J x - Q.ker.starProjection (J x) = 0 at hx
  have hmem : J x ∈ Q.ker := by
    rw [sub_eq_zero.mp hx]
    exact Q.ker.starProjection_apply_mem _
  have he : Q (J x) = 0 := hmem
  simpa only [hJ x] using he

theorem frameProjectionFormula_ker (Q : E →L[ℝ] F) (J : F →L[ℝ] E)
    (hJ : Function.RightInverse J Q) :
    frameProjectionFormula J Q.ker.starProjection = Q := by
  let P := Q.ker.starProjection
  let A := perpendicularFrame J P
  have hA : Function.Injective A := Q.injective_perpendicularFrame_of_rightInverse J hJ
  have hG := A.isInvertible_adjoint_comp_self_of_injective hA
  ext x
  have hmem : x - J (Q x) ∈ Q.ker := by
    change Q (x - J (Q x)) = 0
    rw [map_sub, hJ, sub_self]
  have hzero : (ContinuousLinearMap.id ℝ E - P) (x - J (Q x)) = 0 := by
    change (x - J (Q x)) - Q.ker.starProjection (x - J (Q x)) = 0
    rw [Q.ker.starProjection_eq_self_iff.mpr hmem, sub_self]
  have he : (ContinuousLinearMap.id ℝ E - P) x = A (Q x) := by
    change (ContinuousLinearMap.id ℝ E - P) x =
      (ContinuousLinearMap.id ℝ E - P) (J (Q x))
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  change ((adjoint A).comp A).inverse ((adjoint A) ((ContinuousLinearMap.id ℝ E - P) x)) = Q x
  rw [he]
  exact hG.inverse_apply_self (Q x)

theorem continuousAt_frameProjectionFormula (J : F →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : Function.Injective (perpendicularFrame J P)) :
    ContinuousAt (frameProjectionFormula J) P := by
  have hD : ContinuousAt (fun R : E →L[ℝ] E => ContinuousLinearMap.id ℝ E - R) P :=
    continuousAt_const.sub continuousAt_id
  have hA : ContinuousAt (perpendicularFrame J) P := hD.clm_comp continuousAt_const
  have hAdj : ContinuousAt (fun R => adjoint (perpendicularFrame J R)) P :=
    adjoint.continuous.continuousAt.comp hA
  have hG : ContinuousAt (fun R => (adjoint (perpendicularFrame J R)).comp
      (perpendicularFrame J R)) P := hAdj.clm_comp hA
  have hinverse : ContinuousAt (inverse : (F →L[ℝ] F) → F →L[ℝ] F)
      ((adjoint (perpendicularFrame J P)).comp (perpendicularFrame J P)) := by
    have hInv := (perpendicularFrame J P).isInvertible_adjoint_comp_self_of_injective hP
    exact (hInv.contDiffAt_map_inverse (n := 0)).continuousAt
  have hi : ContinuousAt (fun R => ((adjoint (perpendicularFrame J R)).comp
      (perpendicularFrame J R)).inverse) P :=
    hinverse.comp (f := fun R => (adjoint (perpendicularFrame J R)).comp
      (perpendicularFrame J R)) hG
  exact (hi.clm_comp hAdj).clm_comp hD

end ContinuousLinearMap

end

section

open Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev ComplementPlaneSpace (U : Submodule ℝ E) :=
  {K : EuclideanSubspace E // IsCompl U K.subspace}

abbrev RetractionSpace (U : Submodule ℝ E) :=
  {Q : E →L[ℝ] U // ∀ u : U, Q u = u}

noncomputable def complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    U.RetractionSpace :=
  ⟨(U.projectionOnto K.val.subspace K.property).toContinuousLinearMap,
    fun u => projectionOnto_apply_left K.property u⟩

theorem ker_complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val.ker = K.val.subspace :=
  ker_projectionOnto K.property

def retractionKernel (U : Submodule ℝ E) (Q : U.RetractionSpace) : U.ComplementPlaneSpace :=
  ⟨⟨Q.val.ker⟩, LinearMap.isCompl_of_proj Q.property⟩

theorem retractionKernel_complementRetraction (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) : U.retractionKernel (U.complementRetraction K) = K := by
  apply Subtype.ext
  apply EuclideanSubspace.ext
  exact U.ker_complementRetraction K

theorem complementRetraction_retractionKernel (U : Submodule ℝ E)
    (Q : U.RetractionSpace) : U.complementRetraction (U.retractionKernel Q) = Q := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun L : E →ₗ[ℝ] U => L x)
    (Q.val.toLinearMap.projectionOnto_of_proj Q.property)

theorem continuous_retractionKernel (U : Submodule ℝ E) : Continuous U.retractionKernel := by
  apply Continuous.subtype_mk
  change Continuous (fun Q : U.RetractionSpace => (⟨Q.val.ker⟩ : EuclideanSubspace E))
  apply EuclideanSubspace.continuous_iff_projector.mpr
  change Continuous (fun Q : U.RetractionSpace => Q.val.ker.starProjection)
  have he : (fun Q : U.RetractionSpace => Q.val.ker.starProjection) =
      (fun Q => Q.val.kernelProjectionFormula) :=
    funext (fun Q => Q.val.starProjection_ker_eq_formula (fun u => ⟨u, Q.property u⟩))
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro Q
  exact (Q.val.continuousAt_kernelProjectionFormula (fun u => ⟨u, Q.property u⟩)).comp
    (f := fun R : U.RetractionSpace => R.val) continuous_subtype_val.continuousAt

theorem complementRetraction_eq_frameFormula (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val =
      ContinuousLinearMap.frameProjectionFormula U.subtypeL K.val.subspace.starProjection := by
  have he := (U.complementRetraction K).val.frameProjectionFormula_ker U.subtypeL
    (U.complementRetraction K).property
  simpa only [U.ker_complementRetraction K] using he.symm

theorem continuous_complementRetraction (U : Submodule ℝ E) :
    Continuous U.complementRetraction := by
  apply Continuous.subtype_mk
  change Continuous (fun K : U.ComplementPlaneSpace => (U.complementRetraction K).val)
  have he : (fun K : U.ComplementPlaneSpace => (U.complementRetraction K).val) =
      (fun K => ContinuousLinearMap.frameProjectionFormula U.subtypeL
        K.val.subspace.starProjection) :=
    funext (U.complementRetraction_eq_frameFormula)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro K
  have hinj : Function.Injective (ContinuousLinearMap.perpendicularFrame U.subtypeL
      K.val.subspace.starProjection) := by
    have h := (U.complementRetraction K).val.injective_perpendicularFrame_of_rightInverse
      U.subtypeL (U.complementRetraction K).property
    simpa only [U.ker_complementRetraction K] using h
  exact (ContinuousLinearMap.continuousAt_frameProjectionFormula U.subtypeL _ hinj).comp
    (f := fun K : U.ComplementPlaneSpace => K.val.subspace.starProjection)
    ((EuclideanSubspace.continuous_projector E).comp continuous_subtype_val).continuousAt

noncomputable def complementPlaneHomeomorph (U : Submodule ℝ E) :
    U.ComplementPlaneSpace ≃ₜ U.RetractionSpace where
  toFun := U.complementRetraction
  invFun := U.retractionKernel
  left_inv := U.retractionKernel_complementRetraction
  right_inv := U.complementRetraction_retractionKernel
  continuous_toFun := U.continuous_complementRetraction
  continuous_invFun := U.continuous_retractionKernel

end Submodule

end

section

open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev TransverseComplementPlaneSpace (U : Submodule ℝ E) (S : Set E) :=
  {K : U.ComplementPlaneSpace // K.val.subspace.IsSecantTransverse S}

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

end AbstractSimplicialComplex

end

section

namespace ContinuousLinearMap

abbrev FrameProjectionSpace {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J : F →L[ℝ] E) :=
  {Q : E →L[ℝ] F // Function.RightInverse J Q}

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

noncomputable def frameRetractionHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J) :
    J.FrameProjectionSpace ≃ₜ J.range.RetractionSpace := by
  let e := (LinearEquiv.ofInjective J.toLinearMap hJ).toContinuousLinearEquiv
  refine ((ContinuousLinearEquiv.refl ℝ E).arrowCongr e).toHomeomorph.subtype ?_
  intro Q
  change Function.RightInverse J Q ↔ ∀ u : J.range, e (Q u) = u
  constructor
  · intro h u
    obtain ⟨u, z, rfl⟩ := u
    change e (Q (J z)) = e z
    rw [h z]
  · intro h z
    apply e.injective
    exact h (e z)

omit [FiniteDimensional ℝ E] in

theorem ker_frameRetractionHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (Q : J.FrameProjectionSpace) :
    ((J.frameRetractionHomeomorph hJ) Q).val.ker = Q.val.ker := by
  let e := (LinearEquiv.ofInjective J.toLinearMap hJ).toContinuousLinearEquiv
  ext x
  change e (Q.val x) = 0 ↔ Q.val x = 0
  exact e.map_eq_zero_iff

noncomputable def frameComplementPlaneHomeomorph (J : F →L[ℝ] E)
    (hJ : Function.Injective J) :
    J.range.ComplementPlaneSpace ≃ₜ J.FrameProjectionSpace :=
  J.range.complementPlaneHomeomorph.trans (J.frameRetractionHomeomorph hJ).symm

theorem ker_frameComplementPlaneHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (K : J.range.ComplementPlaneSpace) :
    ((J.frameComplementPlaneHomeomorph hJ) K).val.ker = K.val.subspace := by
  rw [← J.ker_frameRetractionHomeomorph hJ]
  have he : (J.frameRetractionHomeomorph hJ) ((J.frameComplementPlaneHomeomorph hJ) K) =
      J.range.complementRetraction K :=
    (J.frameRetractionHomeomorph hJ).apply_symm_apply _
  rw [he]
  exact J.range.ker_complementRetraction K

end ContinuousLinearMap

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

end AbstractSimplicialComplex

end

section

open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

def tangentCylinderProjection (B : E →L[ℝ] F) (A : E →L[ℝ] T) : (E × T) →L[ℝ] (F × T) :=
  (B.comp (fst ℝ E T)).prod (snd ℝ E T + A.comp (fst ℝ E T))

theorem tangentCylinderProjection_apply (B : E →L[ℝ] F) (A : E →L[ℝ] T) (x : E) (t : T) :
    tangentCylinderProjection B A (x, t) = (B x, t + A x) := rfl

theorem injOn_tangentCylinderProjection_iff (B : E →L[ℝ] F) (A : E →L[ℝ] T) (S : Set E) :
    InjOn (tangentCylinderProjection B A) (S ×ˢ (univ : Set T)) ↔ InjOn B S := by
  constructor
  · intro h x hx y hy he
    have hxy := h (x₁ := (x, -A x)) (x₂ := (y, -A y)) ⟨hx, mem_univ _⟩
      ⟨hy, mem_univ _⟩ (by simp only [tangentCylinderProjection_apply, neg_add_cancel, he])
    exact congrArg Prod.fst hxy
  · intro h x hx y hy he
    have hn : x.1 = y.1 := h hx.1 hy.1 (congrArg Prod.fst he)
    apply Prod.ext hn
    have ht := congrArg Prod.snd he
    change x.2 + A x.1 = y.2 + A y.1 at ht
    rw [hn] at ht
    exact add_right_cancel ht

theorem rightInverse_tangentCylinderProjection_iff (J : F →L[ℝ] E)
    (B : E →L[ℝ] F) (A : E →L[ℝ] T) :
    Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) (tangentCylinderProjection B A) ↔
      Function.RightInverse J B ∧ A.comp J = 0 := by
  constructor
  · intro h
    refine ⟨fun f => congrArg Prod.fst (h (f, 0)), ?_⟩
    apply ContinuousLinearMap.ext
    intro f
    have ht := congrArg Prod.snd (h (f, 0))
    change (0 : T) + A (J f) = 0 at ht
    change A (J f) = 0
    simpa only [zero_add] using ht
  · rintro ⟨hB, hA⟩ ⟨f, t⟩
    change (B (J f), t + A (J f)) = (f, t)
    have hz : A (J f) = 0 := congrArg (fun L : F →L[ℝ] T => L f) hA
    rw [hB f, hz, add_zero]

theorem eq_tangentCylinderProjection_of_fixed_tangent (Q : (E × T) →L[ℝ] (F × T))
    (hT : ∀ t : T, Q (0, t) = (0, t)) :
    Q = tangentCylinderProjection ((fst ℝ F T).comp (Q.comp (inl ℝ E T)))
      ((snd ℝ F T).comp (Q.comp (inl ℝ E T))) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  change Q (x, t) = ((Q (x, 0)).1, t + (Q (x, 0)).2)
  have he : (x, t) = (x, (0 : T)) + (0, t) := by simp
  rw [he, map_add, hT]
  ext <;> simp [add_comm]

theorem fixed_tangent_of_rightInverse_productFrame (J : F →L[ℝ] E)
    (Q : (E × T) →L[ℝ] (F × T))
    (hQ : Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) Q) (t : T) :
    Q (0, t) = (0, t) := by
  have he := hQ (0, t)
  change Q (J 0, t) = (0, t) at he
  simpa only [map_zero] using he

end ContinuousLinearMap

end

section

open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

abbrev FrameEmbeddingSpace (J : F →L[ℝ] E) (S : Set E) :=
  {B : E →L[ℝ] F // Function.RightInverse J B ∧ InjOn B S}

abbrev TangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :=
  {Q : (E × T) →L[ℝ] (F × T) //
    Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) Q ∧
      InjOn Q (S ×ˢ (univ : Set T))}

noncomputable def frameShears (J : F →L[ℝ] E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :
    Submodule ℝ (E →L[ℝ] T) :=
  (J.precomp T : (E →L[ℝ] T) →L[ℝ] (F →L[ℝ] T)).ker

def tangentCylinderBlocks (J : F →L[ℝ] E) (S : Set E)
    (Q : TangentCylinderEmbeddingSpace J S T) :
    FrameEmbeddingSpace J S × J.frameShears T := by
  let B := (fst ℝ F T).comp (Q.val.comp (inl ℝ E T))
  let A := (snd ℝ F T).comp (Q.val.comp (inl ℝ E T))
  have hform : Q.val = tangentCylinderProjection B A :=
    Q.val.eq_tangentCylinderProjection_of_fixed_tangent
      (fixed_tangent_of_rightInverse_productFrame J Q.val Q.property.1)
  have hnorm := (rightInverse_tangentCylinderProjection_iff J B A).mp
    (hform ▸ Q.property.1)
  have hinj := (injOn_tangentCylinderProjection_iff B A S).mp (hform ▸ Q.property.2)
  exact (⟨B, hnorm.1, hinj⟩, ⟨A, hnorm.2⟩)

def assembleTangentCylinder (J : F →L[ℝ] E) (S : Set E)
    (R : FrameEmbeddingSpace J S × J.frameShears T) :
    TangentCylinderEmbeddingSpace J S T :=
  ⟨tangentCylinderProjection R.1.val R.2.val,
    (rightInverse_tangentCylinderProjection_iff J R.1.val R.2.val).mpr
      ⟨R.1.property.1, R.2.property⟩,
    (injOn_tangentCylinderProjection_iff R.1.val R.2.val S).mpr R.1.property.2⟩

noncomputable def tangentCylinderSpaceHomeomorph (J : F →L[ℝ] E) (S : Set E) :
    TangentCylinderEmbeddingSpace J S T ≃ₜ
      (FrameEmbeddingSpace J S × J.frameShears T) where
  toFun := tangentCylinderBlocks J S
  invFun := assembleTangentCylinder J S
  left_inv Q := by
    apply Subtype.ext
    exact (Q.val.eq_tangentCylinderProjection_of_fixed_tangent
      (fixed_tangent_of_rightInverse_productFrame J Q.val Q.property.1)).symm
  right_inv R := by
    apply Prod.ext
    · apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      rfl
    · apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      change (0 : T) + R.2.val x = R.2.val x
      exact zero_add _
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_const.clm_comp
        (continuous_subtype_val.clm_comp continuous_const)).subtype_mk (fun _ => _)
    · exact (continuous_const.clm_comp
        (continuous_subtype_val.clm_comp continuous_const)).subtype_mk (fun _ => _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun R : FrameEmbeddingSpace J S × J.frameShears T =>
      tangentCylinderProjection R.1.val R.2.val)
    exact (prodL ℝ).continuous.comp
      (((continuous_subtype_val.comp continuous_fst).clm_comp continuous_const).prodMk
        (continuous_const.add
          ((continuous_subtype_val.comp continuous_snd).clm_comp continuous_const)))

theorem contractible_tangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    [ContractibleSpace (FrameEmbeddingSpace J S)] :
    ContractibleSpace (TangentCylinderEmbeddingSpace J S T) :=
  (tangentCylinderSpaceHomeomorph J S).contractibleSpace

end ContinuousLinearMap

end

section

open Set ContinuousLinearMap
open scoped Pointwise

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem injOn_centered_image_iff (Q : E →L[ℝ] F) (e : E ≃L[ℝ] G) (p : E) (S : Set E) :
    InjOn (Q.comp e.symm.toContinuousLinearMap) ((fun x => e (x - p)) '' S) ↔
      InjOn Q S := by
  constructor
  · intro h x hx y hy he
    have he' : e (x - p) = e (y - p) := h (mem_image_of_mem _ hx)
      (mem_image_of_mem _ hy) (by
        simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply, map_sub] using
          congrArg (fun z => z - Q p) he)
    exact sub_left_inj.mp (e.injective he')
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
    have he' : Q x - Q p = Q y - Q p := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, map_sub] using he
    rw [h hx hy (sub_left_inj.mp he')]

end ContinuousLinearMap

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def frameWithTangent (L : Submodule ℝ E) (J : F →L[ℝ] ↥(Lᗮ)) :
    (F × L) →L[ℝ] E :=
  L.normalTangentEquiv.symm.toContinuousLinearMap.comp
    (J.prodMap (ContinuousLinearMap.id ℝ L))

theorem injective_frameWithTangent (L : Submodule ℝ E) {J : F →L[ℝ] ↥(Lᗮ)}
    (hJ : Function.Injective J) : Function.Injective (L.frameWithTangent J) := by
  intro x y hxy
  have h := L.normalTangentEquiv.symm.injective hxy
  exact Prod.ext (hJ (congrArg (fun z : ↥(Lᗮ) × L => z.1) h))
    (congrArg (fun z : ↥(Lᗮ) × L => z.2) h)

end Submodule

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def faceStarCylinderHomeomorph (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (p : E)
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ)) :
    FrameEmbeddingSpace ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J)
        (K.closedFaceStar s).space ≃ₜ
      TangentCylinderEmbeddingSpace J
        ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
          (K.closedFaceStar s).space) (affineSpan ℝ (s : Set E)).direction := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let S := (K.closedFaceStar s).space
  refine (L.normalTangentEquiv.arrowCongr
    (ContinuousLinearEquiv.refl ℝ (F × L))).toHomeomorph.subtype ?_
  intro Q
  change (Function.RightInverse (L.frameWithTangent J) Q ∧ InjOn Q S) ↔
    (Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ L))
      (Q.comp L.normalTangentEquiv.symm.toContinuousLinearMap) ∧
      InjOn (Q.comp L.normalTangentEquiv.symm.toContinuousLinearMap)
        ((L.normalAffineProjection p '' S) ×ˢ (univ : Set L)))
  apply and_congr Iff.rfl
  rw [← L.image_normalTangentCoordinates_add p S]
  exact ((Q.injOn_centered_image_iff L.normalTangentEquiv p (S + (L : Set E))).trans
    (K.injOn_closedFaceStar_tangent_iff hs Q.toLinearMap)).symm

theorem contractible_faceStarFrameEmbeddingSpace (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (p : E)
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    [ContractibleSpace (FrameEmbeddingSpace J
      ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
        (K.closedFaceStar s).space))] :
    ContractibleSpace (FrameEmbeddingSpace
      ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J) (K.closedFaceStar s).space) := by
  let := contractible_tangentCylinderEmbeddingSpace J
    ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p '' (K.closedFaceStar s).space)
    (T := (affineSpan ℝ (s : Set E)).direction)
  exact (K.faceStarCylinderHomeomorph hs p J).contractibleSpace

end Geometry.SimplicialComplex

end

section

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem frameWithTangent_range_le (L U : Submodule ℝ E) (J : F →L[ℝ] ↥(Lᗮ))
    (hL : L ≤ U) (hJ : ∀ z, (J z : E) ∈ U) : (L.frameWithTangent J).range ≤ U := by
  rintro x ⟨z, rfl⟩
  change (J z.1 : E) + (z.2 : E) ∈ U
  exact U.add_mem (hJ z.1) (hL z.2.property)

end Submodule

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem normalAffineProjection_mem_direction (U V : AffineSubspace ℝ E)
    (hUV : U ≤ V) {p x : E} (hp : p ∈ U) (hx : x ∈ V) :
    (U.direction.normalAffineProjection p x : E) ∈ V.direction := by
  change U.directionᗮ.starProjection (x - p) ∈ V.direction
  rw [U.direction.starProjection_orthogonal_val]
  exact V.direction.sub_mem (V.vsub_mem_direction hx (hUV hp))
    (direction_le hUV (U.direction.starProjection_apply_mem (x - p)))

theorem normalLineFrame_range_le_direction (U V : AffineSubspace ℝ E)
    (hUV : U ≤ V) {p x : E} (hp : p ∈ U) (hx : x ∈ V) :
    (U.direction.frameWithTangent
      (ContinuousLinearMap.toSpanSingleton ℝ (U.direction.normalAffineProjection p x))).range ≤
      V.direction := by
  apply U.direction.frameWithTangent_range_le V.direction _ (direction_le hUV)
  intro r
  exact V.direction.smul_mem r (U.normalAffineProjection_mem_direction V hUV hp hx)

end AffineSubspace

end

section

open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem exists_pos_secant_bound_tangentCylinderProjection
    (B : E →L[ℝ] F) (A : E →L[ℝ] T) {S : Set E} {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ S, ∀ y ∈ S, c * ‖x - y‖ ≤ ‖B x - B y‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S ×ˢ (univ : Set T), ∀ y ∈ S ×ˢ (univ : Set T),
      d * ‖x - y‖ ≤ ‖tangentCylinderProjection B A x - tangentCylinderProjection B A y‖ := by
  let e := (ContinuousLinearEquiv.refl ℝ E).skewProd (ContinuousLinearEquiv.refl ℝ T) A
  let c0 : ℝ := min c 1
  have hc0 : 0 < c0 := lt_min hc one_pos
  let k : ℝ := ‖e.symm.toContinuousLinearMap‖
  have hk : 0 ≤ k := norm_nonneg _
  have hden : 0 < k + 1 := by linarith
  refine ⟨c0 / (k + 1), div_pos hc0 hden, fun x hx y hy => ?_⟩
  have hnormal : c0 * ‖x.1 - y.1‖ ≤ ‖B x.1 - B y.1‖ :=
    (mul_le_mul_of_nonneg_right (min_le_left c 1) (norm_nonneg _)).trans
      (hb x.1 hx.1 y.1 hy.1)
  have htangent : c0 * ‖(e (x - y)).2‖ ≤ ‖(e (x - y)).2‖ := by
    exact (mul_le_mul_of_nonneg_right (min_le_right c 1) (norm_nonneg _)).trans_eq
      (one_mul _)
  have heQ : tangentCylinderProjection B A x - tangentCylinderProjection B A y =
      (B x.1 - B y.1, (e (x - y)).2) := by
    apply Prod.ext
    · rfl
    · change (x.2 + A x.1) - (y.2 + A y.1) = (x.2 - y.2) + A (x.1 - y.1)
      rw [map_sub]
      abel
  have hout : c0 * ‖e (x - y)‖ ≤
      ‖tangentCylinderProjection B A x - tangentCylinderProjection B A y‖ := by
    rw [heQ, Prod.norm_def, Prod.norm_def]
    change c0 * max ‖x.1 - y.1‖ ‖(e (x - y)).2‖ ≤ _
    rw [mul_max_of_nonneg _ _ hc0.le]
    exact max_le_max hnormal htangent
  have hinv : ‖x - y‖ ≤ k * ‖e (x - y)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      e.symm.toContinuousLinearMap.le_opNorm (e (x - y))
  have hi := mul_le_mul_of_nonneg_left hinv hc0.le
  have ho := mul_le_mul_of_nonneg_left hout hk
  calc
    c0 / (k + 1) * ‖x - y‖ = (c0 * ‖x - y‖) / (k + 1) := by ring
    _ ≤ ‖tangentCylinderProjection B A x - tangentCylinderProjection B A y‖ := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hi, ho,
        norm_nonneg (tangentCylinderProjection B A x - tangentCylinderProjection B A y)]

end ContinuousLinearMap

end

section

open Set

namespace ContinuousLinearEquiv

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_pos_secant_bound_of_centered_image (e : E ≃L[ℝ] G)
    (Q : E →L[ℝ] F) (p : E) {S : Set E} {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ (fun z => e (z - p)) '' S,
      ∀ y ∈ (fun z => e (z - p)) '' S,
        c * ‖x - y‖ ≤ ‖Q (e.symm x) - Q (e.symm y)‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S, ∀ y ∈ S, d * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  let k : ℝ := ‖e.symm.toContinuousLinearMap‖
  have hk : 0 ≤ k := norm_nonneg _
  have hden : 0 < k + 1 := by linarith
  refine ⟨c / (k + 1), div_pos hc hden, fun x hx y hy => ?_⟩
  have h := hb _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
  have hcoord : e (x - p) - e (y - p) = e (x - y) := by
    rw [← map_sub, sub_sub_sub_cancel_right]
  have hout : Q (x - p) - Q (y - p) = Q x - Q y := by
    rw [Q.map_sub, Q.map_sub]
    abel
  rw [hcoord, e.symm_apply_apply, e.symm_apply_apply, hout] at h
  have hinv : ‖x - y‖ ≤ k * ‖e (x - y)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      e.symm.toContinuousLinearMap.le_opNorm (e (x - y))
  have hi := mul_le_mul_of_nonneg_left hinv hc.le
  have ho := mul_le_mul_of_nonneg_left h hk
  calc
    c / (k + 1) * ‖x - y‖ = (c * ‖x - y‖) / (k + 1) := by ring
    _ ≤ ‖Q x - Q y‖ := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hi, ho, norm_nonneg (Q x - Q y)]

end ContinuousLinearEquiv

end

section

open Set

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem LinearIndependent.exists_pos_secant_bound_of_injOn {v : ι → E}
    (hv : LinearIndependent ℝ v) (faces : Set (Finset ι)) (Q : E →L[ℝ] F)
    (hQ : InjOn Q (⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι))))) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι)))),
      ∀ y ∈ (⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι)))),
      c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  let V := Submodule.span ℝ (range v)
  let b : Module.Basis ι ℝ V := Module.Basis.span hv
  let S : Set V := ⋃ s ∈ faces, convexHull ℝ (insert 0 (b '' (s : Set ι)))
  have hb : (fun i => V.subtype (b i)) = v :=
    funext (fun i => Module.Basis.coe_span_apply hv i)
  have himage : V.subtype '' S =
      ⋃ s ∈ faces, convexHull ℝ (insert 0 (v '' (s : Set ι))) := by
    simp only [S, image_iUnion, V.subtype.image_convexHull, image_insert_eq,
      map_zero, image_image, hb]
  have hQV : InjOn (Q.comp V.subtypeL) S := by
    intro x hx y hy he
    apply Subtype.ext
    apply hQ
    · rw [← himage]
      exact mem_image_of_mem _ hx
    · rw [← himage]
      exact mem_image_of_mem _ hy
    · exact he
  obtain ⟨c, hc, hbound⟩ := b.exists_pos_secant_bound_of_injOn faces (Q.comp V.subtypeL) hQV
  refine ⟨c, hc, ?_⟩
  rw [← himage]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hbound x hx y hy

namespace AbstractSimplicialComplex

theorem RadialEmbedding.exists_pos_secant_bound_of_linearIndependent
    {A : AbstractSimplicialComplex ι} (v : A.RadialEmbedding E)
    (hv : LinearIndependent ℝ v.val) (Q : E →L[ℝ] F) (hQ : InjOn Q v.cone.space) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ v.cone.space, ∀ y ∈ v.cone.space,
      c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  rw [RadialEmbedding.cone_space] at hQ ⊢
  exact hv.exists_pos_secant_bound_of_injOn (insert ∅ A.faces) Q hQ

end AbstractSimplicialComplex

end

section

open Set ContinuousLinearMap AbstractSimplicialComplex
open scoped Pointwise

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_secant_bound_frame_closedFaceStar (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (Q : FrameEmbeddingSpace ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J)
      (K.closedFaceStar s).space) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (K.closedFaceStar s).space,
      ∀ y ∈ (K.closedFaceStar s).space, c * ‖x - y‖ ≤ ‖Q.val x - Q.val y‖ := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let S := (K.closedFaceStar s).space
  let N := L.normalAffineProjection p '' S
  let R : TangentCylinderEmbeddingSpace J N L := K.faceStarCylinderHomeomorph hs p J Q
  let blocks := tangentCylinderBlocks J N R
  have hform : R.val = tangentCylinderProjection blocks.1.val blocks.2.val :=
    R.val.eq_tangentCylinderProjection_of_fixed_tangent
      (fixed_tangent_of_rightInverse_productFrame J R.val R.property.1)
  have hlin := K.linearIndependent_faceLink_normal hv hs hp
  let : Finite (K.faceLink s).vertices :=
    finite_of_fin_dim_affineIndependent ℝ hlin.affineIndependent
  let v := K.faceNormalRadialEmbedding hv hs hp
  have hnormal : N = v.cone.space := K.normal_image_closedFaceStar hv hs hp
  have hinj : InjOn blocks.1.val v.cone.space := hnormal ▸ blocks.1.property.2
  obtain ⟨c, hc, hb⟩ :=
    v.exists_pos_secant_bound_of_linearIndependent hlin blocks.1.val hinj
  have hbN : ∀ x ∈ N, ∀ y ∈ N, c * ‖x - y‖ ≤ ‖blocks.1.val x - blocks.1.val y‖ := by
    rwa [← hnormal] at hb
  obtain ⟨d, hd, hdc⟩ := exists_pos_secant_bound_tangentCylinderProjection
    blocks.1.val blocks.2.val hc hbN
  have hsubset : (fun x => L.normalTangentEquiv (x - p)) '' S ⊆ N ×ˢ (univ : Set L) := by
    rw [show N ×ˢ (univ : Set L) =
      L.normalTangentCoordinates p '' (S + (L : Set E)) from
        (L.image_normalTangentCoordinates_add p S).symm]
    apply image_mono
    intro x hx
    exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  apply L.normalTangentEquiv.exists_pos_secant_bound_of_centered_image Q.val p hd
  intro x hx y hy
  have h := hdc x (hsubset hx) y (hsubset hy)
  rw [← hform] at h
  exact h

theorem isSecantTransverse_ker_iff_injOn_frame_closedFaceStar
    (K : SimplicialComplex ℝ E) (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (Q : E →L[ℝ] (F × (affineSpan ℝ (s : Set E)).direction))
    (hQ : Function.RightInverse ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J) Q) :
    Q.ker.IsSecantTransverse (K.closedFaceStar s).space ↔
      InjOn Q (K.closedFaceStar s).space := by
  constructor
  · intro h
    exact h.injOn Q rfl
  · intro h
    obtain ⟨c, hc, hb⟩ := K.exists_pos_secant_bound_frame_closedFaceStar hv hs hp J ⟨Q, hQ, h⟩
    exact Submodule.isSecantTransverse_ker_of_lower_bound Q hc hb

end Geometry.SimplicialComplex

end

section

open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsSecantTransverse.disjoint_affineDirection {P : Submodule ℝ E} {S C : Set E}
    (hP : P.IsSecantTransverse S) (hC : Convex ℝ C) (hne : C.Nonempty) (hCS : C ⊆ S) :
    Disjoint (affineSpan ℝ C).direction P := by
  obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior hC hne
  obtain ⟨c, hc, hb⟩ := hP
  apply Submodule.disjoint_def.mpr
  intro x hx hxp
  obtain ⟨r, hr, hrp⟩ := exists_pos_smul_add_mem_of_intrinsicInterior hp hx
  have h := hb _ (hCS hrp) p (hCS (intrinsicInterior_subset hp))
  rw [add_sub_cancel_right,
    P.starProjection_eq_self_iff.mpr (P.smul_mem r hxp), sub_self, norm_zero] at h
  have hn : ‖r • x‖ = 0 := by nlinarith only [h, hc, norm_nonneg (r • x)]
  exact (smul_eq_zero.mp (norm_eq_zero.mp hn)).resolve_left hr.ne'

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem disjoint_faceDirection_of_isSecantTransverse (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {P : Submodule ℝ E}
    (hP : P.IsSecantTransverse K.space) :
    Disjoint (affineSpan ℝ (s : Set E)).direction P := by
  have hne := (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull (𝕜 := ℝ)
  simpa only [affineSpan_convexHull] using hP.disjoint_affineDirection
    (convex_convexHull ℝ _) hne (convexHull_subset_space hs)

end Geometry.SimplicialComplex

end

section

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev SecantTransversePlaneSpace (d : ℕ) (S : Set E) :=
  {K : EuclideanSubspace E // Module.finrank ℝ K.subspace + d = Module.finrank ℝ E ∧
    K.subspace.IsSecantTransverse S}

noncomputable def transverseComplementHomeomorph (d : ℕ) (S : Set E)
    (U : Submodule ℝ E) (hU : Module.finrank ℝ U = d)
    (hdisjoint : ∀ K : Submodule ℝ E, K.IsSecantTransverse S → Disjoint U K) :
    SecantTransversePlaneSpace d S ≃ₜ U.TransverseComplementPlaneSpace S where
  toFun K := ⟨⟨K.val, (Submodule.isCompl_iff_disjoint U K.val.subspace (by
    have hdim := K.property.1
    omega)).mpr (hdisjoint _ K.property.2)⟩, K.property.2⟩
  invFun K := ⟨K.val.val, ⟨by
    have hdim := Submodule.finrank_add_eq_of_isCompl K.val.property
    omega, K.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun _ => _)

end Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end AbstractSimplicialComplex

end

section

open Set ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def frameEmbeddingHomeomorph (J : F →L[ℝ] E) (S : Set E) :
    {Q : J.FrameProjectionSpace // InjOn Q.val S} ≃ₜ FrameEmbeddingSpace J S where
  toFun Q := ⟨Q.val.val, Q.val.property, Q.property⟩
  invFun Q := ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun _ => _)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)

end ContinuousLinearMap

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

noncomputable def faceStarComplementPlaneHomeomorph (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (hJ : Function.Injective J) :
    ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J).range.TransverseComplementPlaneSpace
        (K.closedFaceStar s).space ≃ₜ
      FrameEmbeddingSpace ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J)
        (K.closedFaceStar s).space := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let J' := L.frameWithTangent J
  have hJ' : Function.Injective J' := L.injective_frameWithTangent hJ
  refine ((J'.frameComplementPlaneHomeomorph hJ').subtype ?_).trans
    (frameEmbeddingHomeomorph J' (K.closedFaceStar s).space)
  intro P
  rw [← K.isSecantTransverse_ker_iff_injOn_frame_closedFaceStar hv hs hp J
    ((J'.frameComplementPlaneHomeomorph hJ') P).val
      ((J'.frameComplementPlaneHomeomorph hJ') P).property,
    J'.ker_frameComplementPlaneHomeomorph hJ']

theorem contractible_faceStarComplementPlaneSpace (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (hJ : Function.Injective J)
    [ContractibleSpace (FrameEmbeddingSpace J
      ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
        (K.closedFaceStar s).space))] :
    ContractibleSpace (Submodule.TransverseComplementPlaneSpace
      ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J).range
      (K.closedFaceStar s).space) := by
  let := K.contractible_faceStarFrameEmbeddingSpace hs p J
  exact (K.faceStarComplementPlaneHomeomorph hv hs hp J hJ).contractibleSpace

theorem contractible_faceStarTransversePlaneSpace (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E))
    (J : F →L[ℝ] ↥((affineSpan ℝ (s : Set E)).directionᗮ))
    (hJ : Function.Injective J)
    {t : Finset E} (ht : t ∈ (K.closedFaceStar s).faces)
    (hframe : ((affineSpan ℝ (s : Set E)).direction.frameWithTangent J).range ≤
      (affineSpan ℝ (t : Set E)).direction)
    [ContractibleSpace (FrameEmbeddingSpace J
      ((affineSpan ℝ (s : Set E)).direction.normalAffineProjection p ''
        (K.closedFaceStar s).space))] :
    ContractibleSpace (SecantTransversePlaneSpace
      (Module.finrank ℝ F + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction)
      (K.closedFaceStar s).space) := by
  let L := (affineSpan ℝ (s : Set E)).direction
  let J' := L.frameWithTangent J
  have hdim : Module.finrank ℝ J'.range = Module.finrank ℝ F + Module.finrank ℝ L := by
    rw [LinearMap.finrank_range_of_inj (L.injective_frameWithTangent hJ), Module.finrank_prod]
  let := K.contractible_faceStarComplementPlaneSpace hv hs hp J hJ
  exact (transverseComplementHomeomorph _ (K.closedFaceStar s).space J'.range hdim
    (fun _ hP => ((K.closedFaceStar s).disjoint_faceDirection_of_isSecantTransverse ht hP).mono_left
      hframe)).contractibleSpace

end Geometry.SimplicialComplex

end

section

open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isRadialEmbedding_iff_isSecantTransverse_ker_subtype
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔
      Q.ker.IsSecantTransverse (V.subtype '' (A.basisRadialEmbedding b).cone.space) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ := BasisRadialProjection.exists_pos_secant_bound
      (⟨Q.comp V.subtypeL, h⟩ : A.BasisRadialProjection b F)
    apply Submodule.isSecantTransverse_ker_of_lower_bound Q hc
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hb x hx y hy
  · intro h
    apply A.isRadialEmbedding_of_injOn_basisCone b (Q.comp V.subtypeL)
    intro x hx y hy he
    apply Subtype.ext
    exact h.injOn Q rfl ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ he

theorem isRadialEmbedding_iff_injOn_basisCone_subtype
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔
      InjOn Q (V.subtype '' (A.basisRadialEmbedding b).cone.space) := by
  constructor
  · intro h
    exact ((A.isRadialEmbedding_iff_isSecantTransverse_ker_subtype V b Q).mp h).injOn Q rfl
  · intro h
    apply A.isRadialEmbedding_of_injOn_basisCone b (Q.comp V.subtypeL)
    intro x hx y hy he
    exact Subtype.ext (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ he)

end AbstractSimplicialComplex

end

section

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def operatorOrthogonalSplitHomeomorph (V : Submodule ℝ E) :
    (E →L[ℝ] F) ≃ₜ ((V →L[ℝ] F) × (Vᗮ →L[ℝ] F)) where
  toFun Q := (Q.comp V.subtypeL, Q.comp Vᗮ.subtypeL)
  invFun R := R.1.comp V.orthogonalProjectionOnto + R.2.comp Vᗮ.orthogonalProjectionOnto
  left_inv Q := by
    apply ContinuousLinearMap.ext
    intro x
    change Q (V.starProjection x) + Q (Vᗮ.starProjection x) = Q x
    rw [← map_add, V.starProjection_add_starProjection_orthogonal x]
  right_inv R := by
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro x
      change R.1 (V.orthogonalProjectionOnto (x : E)) +
        R.2 (Vᗮ.orthogonalProjectionOnto (x : E)) = R.1 x
      rw [V.orthogonalProjectionOnto_mem_subspace_eq_self,
        V.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.property, map_zero, add_zero]
    · apply ContinuousLinearMap.ext
      intro x
      change R.1 (V.orthogonalProjectionOnto (x : E)) +
        R.2 (Vᗮ.orthogonalProjectionOnto (x : E)) = R.2 x
      rw [V.orthogonalProjectionOnto_apply_of_mem_orthogonal x.property,
        Vᗮ.orthogonalProjectionOnto_mem_subspace_eq_self, map_zero, zero_add]
  continuous_toFun := (continuous_id.clm_comp continuous_const).prodMk
    (continuous_id.clm_comp continuous_const)
  continuous_invFun := (continuous_fst.clm_comp continuous_const).add
    (continuous_snd.clm_comp continuous_const)

noncomputable def operatorRestrictionHomeomorph (V : Submodule ℝ E)
    (p : (V →L[ℝ] F) → Prop) :
    {Q : E →L[ℝ] F // p (Q.comp V.subtypeL)} ≃ₜ
      ({R : V →L[ℝ] F // p R} × (Vᗮ →L[ℝ] F)) := by
  let e : (E →L[ℝ] F) ≃ₜ ((V →L[ℝ] F) × (Vᗮ →L[ℝ] F)) :=
    V.operatorOrthogonalSplitHomeomorph
  refine
    { toFun := fun Q => (⟨(e Q.val).1, Q.property⟩, (e Q.val).2)
      invFun := fun R => ⟨e.symm (R.1.val, R.2), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change p ((e (e.symm (R.1.val, R.2))).1)
    rw [e.apply_symm_apply]
    exact R.1.property
  · intro Q
    apply Subtype.ext
    exact e.symm_apply_apply Q.val
  · intro R
    apply Prod.ext
    · apply Subtype.ext
      change (e (e.symm (R.1.val, R.2))).1 = R.1.val
      exact congrArg Prod.fst (e.apply_symm_apply (R.1.val, R.2))
    · change (e (e.symm (R.1.val, R.2))).2 = R.2
      exact congrArg Prod.snd (e.apply_symm_apply (R.1.val, R.2))
  · exact ((e.continuous.comp continuous_subtype_val).fst.subtype_mk (fun _ => _)).prodMk
      (e.continuous.comp continuous_subtype_val).snd
  · exact (e.symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk (fun _ => _)

end Submodule

end

section

open Set NormedSpace

namespace Complex

theorem linearIndependent_one_circleExp {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    LinearIndependent ℝ ((↑) : ↥({(1 : ℂ), (Circle.exp theta : ℂ)} : Set ℂ) → ℂ) := by
  change LinearIndepOn ℝ id {(1 : ℂ), (Circle.exp theta : ℂ)}
  apply linearIndepOn_id_pair one_ne_zero
  intro a ha
  have hi := congrArg Complex.im ha
  have hsin := Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
  simp only [smul_im, one_im, smul_zero, Circle.coe_exp, exp_ofReal_mul_I_im] at hi
  linarith

theorem im_circleExp_neg_mul (theta : ℝ) (z : ℂ) :
    ((Circle.exp (-theta) : ℂ) * z).im = ‖z‖ * Real.sin (z.arg - theta) := by
  calc
    ((Circle.exp (-theta) : ℂ) * z).im = Real.cos theta * z.im - Real.sin theta * z.re := by
      simp only [mul_im, Circle.coe_exp, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
        Real.cos_neg, Real.sin_neg]
      ring
    _ = ‖z‖ * Real.sin (z.arg - theta) := by
      rw [← norm_mul_sin_arg z, ← norm_mul_cos_arg z, Real.sin_sub]
      ring

theorem arg_mem_Icc_of_short_sector {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    {z : ℂ} (hz : z ≠ 0) (him : 0 ≤ z.im)
    (hrot : ((Circle.exp (-theta) : ℂ) * z).im ≤ 0) : z.arg ∈ Icc (0 : ℝ) theta := by
  refine ⟨arg_nonneg_iff.mpr him, ?_⟩
  rw [im_circleExp_neg_mul] at hrot
  by_contra hle
  have hthetaarg : theta < z.arg := lt_of_not_ge hle
  have hsin : 0 < Real.sin (z.arg - theta) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hthetaarg) (by
      have harg := arg_le_pi z
      linarith [htheta.1])
  exact (not_lt_of_ge hrot) (mul_pos (norm_pos_iff.mpr hz) hsin)

theorem segment_one_circleExp_subset_slitPlane {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    segment ℝ (1 : ℂ) (Circle.exp theta) ⊆ slitPlane := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1, mem_slitPlane_iff]
  · apply Or.inr
    have hsin := Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    simpa only [add_im, smul_im, one_im, smul_zero, zero_add, Circle.coe_exp,
      exp_ofReal_mul_I_im, smul_eq_mul, mul_zero] using (mul_pos hbpos hsin).ne'

theorem arg_mem_Icc_of_mem_segment_one_circleExp {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) {z : ℂ}
    (hz : z ∈ segment ℝ (1 : ℂ) (Circle.exp theta)) : z.arg ∈ Icc (0 : ℝ) theta := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (segment_one_circleExp_subset_slitPlane htheta hz)
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  apply arg_mem_Icc_of_short_sector htheta hz0
  · simpa only [add_im, smul_im, one_im, smul_zero, zero_add, Circle.coe_exp,
      exp_ofReal_mul_I_im, smul_eq_mul, mul_zero] using
      mul_nonneg hb (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1.le htheta.2.le)
  · have he : ((Circle.exp (-theta) : ℂ) *
        (a • (1 : ℂ) + b • (Circle.exp theta : ℂ))).im = -a * Real.sin theta := by
      simp only [mul_im, add_im, smul_im, one_im, add_re, smul_re, one_re, smul_eq_mul,
        Circle.coe_exp, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
      ring
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
      (Real.sin_nonneg_of_nonneg_of_le_pi htheta.1.le htheta.2.le)

theorem arg_image_segment_one_circleExp {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    Complex.arg '' segment ℝ (1 : ℂ) (Circle.exp theta) = Icc (0 : ℝ) theta := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact arg_mem_Icc_of_mem_segment_one_circleExp htheta hz
  · intro phi hphi
    let f : ℝ → ℂ := fun t => (1 - t) • (1 : ℂ) + t • (Circle.exp theta : ℂ)
    have hfseg : MapsTo f (Icc (0 : ℝ) 1) (segment ℝ (1 : ℂ) (Circle.exp theta)) := by
      intro t ht
      exact ⟨1 - t, t, sub_nonneg.mpr ht.2, ht.1, by ring, rfl⟩
    have hf : Continuous f := by fun_prop
    have harg : ContinuousOn (Complex.arg ∘ f) (Icc (0 : ℝ) 1) :=
      continuousOn_arg.comp hf.continuousOn
        (fun t ht => segment_one_circleExp_subset_slitPlane htheta (hfseg ht))
    have hends : phi ∈ Icc ((Complex.arg ∘ f) 0) ((Complex.arg ∘ f) 1) := by
      simpa only [Function.comp_apply, f, sub_zero, one_smul, zero_smul, add_zero, arg_one,
        sub_self, zero_add, Circle.arg_exp (by linarith [Real.pi_pos, htheta.1]) htheta.2.le]
        using hphi
    obtain ⟨t, ht, htf⟩ := intermediate_value_Icc zero_le_one harg hends
    exact ⟨f t, hfseg ht, htf⟩

theorem normalize_eq_circleExp_arg {z : ℂ} (hz : z ≠ 0) :
    NormedSpace.normalize z = (Circle.exp z.arg : ℂ) := by
  have hpolar : ‖z‖ • (Circle.exp z.arg : ℂ) = z := by
    simpa only [Circle.coe_exp, real_smul] using norm_mul_exp_arg_mul_I z
  calc
    NormedSpace.normalize z = ‖z‖⁻¹ • (‖z‖ • (Circle.exp z.arg : ℂ)) :=
      congrArg (fun x : ℂ => ‖z‖⁻¹ • x) hpolar.symm
    _ = (Circle.exp z.arg : ℂ) := inv_smul_smul₀ (norm_ne_zero_iff.mpr hz) _

theorem normalize_image_segment_one_circleExp {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    NormedSpace.normalize '' segment ℝ (1 : ℂ) (Circle.exp theta) =
      (fun phi => (Circle.exp phi : ℂ)) '' Icc (0 : ℝ) theta := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.arg, arg_mem_Icc_of_mem_segment_one_circleExp htheta hz,
      (normalize_eq_circleExp_arg
        (slitPlane_ne_zero (segment_one_circleExp_subset_slitPlane htheta hz))).symm⟩
  · rintro _ ⟨phi, hphi, rfl⟩
    obtain ⟨z, hz, harg⟩ := (arg_image_segment_one_circleExp htheta).symm.subset hphi
    refine ⟨z, hz, ?_⟩
    rw [normalize_eq_circleExp_arg
      (slitPlane_ne_zero (segment_one_circleExp_subset_slitPlane htheta hz)), harg]

theorem normalize_circle_mul (a : Circle) (z : ℂ) :
    NormedSpace.normalize ((a : ℂ) * z) = (a : ℂ) * NormedSpace.normalize z := by
  simp only [NormedSpace.normalize, norm_mul, Circle.norm_coe, one_mul, mul_smul_comm]

theorem circleExp_mul_image_segment (a b : ℝ) :
    (fun z : ℂ => (Circle.exp a : ℂ) * z) ''
      segment ℝ (1 : ℂ) (Circle.exp (b - a)) =
        segment ℝ (Circle.exp a : ℂ) (Circle.exp b) := by
  have h := image_segment ℝ (rotation (Circle.exp a)).toLinearEquiv.toAffineMap
    (1 : ℂ) (Circle.exp (b - a))
  change (fun z : ℂ => (Circle.exp a : ℂ) * z) '' _ =
    segment ℝ ((Circle.exp a : ℂ) * 1)
      ((Circle.exp a : ℂ) * (Circle.exp (b - a) : ℂ)) at h
  simpa only [mul_one, ← Circle.coe_mul, ← Circle.exp_add, add_sub_cancel] using h

theorem linearIndependent_circleExp_pair {a b : ℝ} (hab : a < b) (hba : b - a < Real.pi) :
    LinearIndependent ℝ ((↑) : ↥({(Circle.exp a : ℂ), (Circle.exp b : ℂ)} : Set ℂ) → ℂ) := by
  change LinearIndepOn ℝ id ({(Circle.exp a : ℂ), (Circle.exp b : ℂ)} : Set ℂ)
  have h : LinearIndepOn ℝ id ({(1 : ℂ), (Circle.exp (b - a) : ℂ)} : Set ℂ) :=
    linearIndependent_one_circleExp ⟨sub_pos.mpr hab, hba⟩
  have hr := h.id_imageₛ (f := (rotation (Circle.exp a)).toLinearEquiv.toLinearMap)
    (rotation (Circle.exp a)).injective.injOn
  simpa only [image_pair, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    rotation_apply, mul_one, ← Circle.coe_mul, ← Circle.exp_add, add_sub_cancel] using hr

theorem normalize_image_segment_circleExp {a b : ℝ} (hab : a < b)
    (hba : b - a < Real.pi) :
    NormedSpace.normalize '' segment ℝ (Circle.exp a : ℂ) (Circle.exp b) =
      (fun phi => (Circle.exp phi : ℂ)) '' Icc a b := by
  rw [← circleExp_mul_image_segment a b, image_image]
  simp_rw [normalize_circle_mul]
  rw [← image_image, normalize_image_segment_one_circleExp ⟨sub_pos.mpr hab, hba⟩,
    image_image]
  simp only [← Circle.coe_mul, ← Circle.exp_add]
  apply Subset.antisymm
  · rintro _ ⟨phi, hphi, rfl⟩
    exact ⟨a + phi, ⟨by linarith [hphi.1], by linarith [hphi.2]⟩, rfl⟩
  · rintro _ ⟨phi, hphi, rfl⟩
    refine ⟨phi - a, ⟨sub_nonneg.mpr hphi.1, sub_le_sub_right hphi.2 a⟩, ?_⟩
    simp only [add_sub_cancel]

end Complex

end

section

open Set NormedSpace

namespace Complex

theorem lt_of_no_radial_backtracking {a b c : ℝ} (hab : a < b)
    (hba : b - a < Real.pi) (hbc : b - c < Real.pi)
    (hc : (Circle.exp c : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp a : ℂ) (Circle.exp b))
    (ha : (Circle.exp a : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp b : ℂ) (Circle.exp c)) : b < c := by
  by_contra h
  have hcb : c ≤ b := le_of_not_gt h
  by_cases hac : a ≤ c
  · apply hc
    rw [normalize_image_segment_circleExp hab hba]
    exact ⟨c, ⟨hac, hcb⟩, rfl⟩
  · have hca : c < a := lt_of_not_ge hac
    apply ha
    rw [segment_symm ℝ, normalize_image_segment_circleExp (hca.trans hab) hbc]
    exact ⟨a, ⟨hca.le, hab.le⟩, rfl⟩

end Complex

namespace Circle

noncomputable def shortIncrement (x y : Circle) : ℝ := Complex.arg (y / x : Circle)

theorem mul_exp_shortIncrement (x y : Circle) : x * Circle.exp (shortIncrement x y) = y := by
  rw [shortIncrement, Circle.exp_arg]
  exact mul_div_cancel _ _

theorem neg_pi_lt_shortIncrement (x y : Circle) : -Real.pi < shortIncrement x y :=
  Complex.neg_pi_lt_arg _

theorem shortIncrement_lt_pi {x y : Circle}
    (hlin : LinearIndependent ℝ ((↑) : ↥({(x : ℂ), (y : ℂ)} : Set ℂ) → ℂ)) :
    shortIncrement x y < Real.pi := by
  apply lt_of_le_of_ne (Complex.arg_le_pi _)
  intro hpi
  have hpi' : shortIncrement x y = Real.pi := hpi
  have he := congrArg (fun z : Circle => (z : ℂ)) (mul_exp_shortIncrement x y)
  rw [hpi'] at he
  have hy : (y : ℂ) = -(x : ℂ) := by
    simpa only [coe_mul, coe_exp, Complex.exp_pi_mul_I, mul_neg_one] using he.symm
  apply hlin.zero_notMem_convexHull
  rw [convexHull_pair]
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  rw [hy, smul_neg, add_neg_cancel]

end Circle

end

section

open Set Geometry NormedSpace

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι} {v : ι → E}

theorem IsRadialEmbedding.linearIndependent_face_image (hv : A.IsRadialEmbedding v)
    {s : Finset ι} (hs : s ∈ A.faces) :
    LinearIndependent ℝ ((↑) : ↥(v '' (s : Set ι)) → E) := by
  classical
  obtain ⟨L, hfaces, hlin, _⟩ := hv.2
  have hsi : s.image v ∈ L.faces := by
    rw [hfaces]
    exact ⟨s, hs, Finset.coe_image⟩
  have h : LinearIndependent ℝ ((↑) : ↥(s.image v : Set E) → E) := hlin _ hsi
  rwa [Finset.coe_image] at h

theorem IsRadialEmbedding.vertex_mem_normalize_face_iff (hv : A.IsRadialEmbedding v)
    {s : Finset ι} (hs : s ∈ A.faces) (i : ι) :
    NormedSpace.normalize (v i) ∈ NormedSpace.normalize '' convexHull ℝ (v '' (s : Set ι)) ↔
      i ∈ s := by
  classical
  obtain ⟨L, hfaces, _, hinj⟩ := hv.2
  have hsi : s.image v ∈ L.faces := by
    rw [hfaces]
    exact ⟨s, hs, Finset.coe_image⟩
  have hvi : v i ∈ L.vertices := by
    change {v i} ∈ L.faces
    rw [hfaces]
    exact ⟨{i}, A.singleton_mem i, by simp⟩
  constructor
  · rintro ⟨x, hx, hxi⟩
    have hxs : x ∈ convexHull ℝ (s.image v : Set E) := by
      simpa only [Finset.coe_image] using hx
    have hix : v i = x := hinj (L.vertices_subset_space hvi)
      (SimplicialComplex.convexHull_subset_space hsi hxs) hxi.symm
    have himem := (L.vertex_mem_convexHull_iff hvi hsi).mp (hix ▸ hxs)
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp himem
    exact hv.1 hji ▸ hj
  · intro hi
    exact ⟨v i, subset_convexHull ℝ _ ⟨i, hi, rfl⟩, rfl⟩

end AbstractSimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {F : Set (Finset E)}

private theorem subface_inter_subset
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T))
    {s t S T : Finset E} (hS : S ∈ F) (hs : s ⊆ S) (hT : T ∈ F) (ht : t ⊆ T) :
    convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 (t : Set E) ⊆
      convexHull 𝕜 ((s : Set E) ∩ t) := by
  classical
  rintro x ⟨hxs, hxt⟩
  have hxST := hinter S hS T hT ⟨convexHull_mono hs hxs, convexHull_mono ht hxt⟩
  have hxsST : x ∈ convexHull 𝕜 (s ∩ (S ∩ T) : Set E) := by
    have he := (hind S hS).convexHull_inter hs (t₂ := S ∩ T) Finset.inter_subset_left
    simp only [Finset.coe_inter] at he
    rw [he]
    exact ⟨hxs, hxST⟩
  have hxsT : s ∩ (S ∩ T) ⊆ T :=
    Finset.inter_subset_right.trans Finset.inter_subset_right
  have hxst : x ∈ convexHull 𝕜 ((s ∩ (S ∩ T)) ∩ t : Set E) := by
    have he := (hind T hT).convexHull_inter hxsT ht
    simp only [Finset.coe_inter] at he
    rw [he]
    exact ⟨hxsST, hxt⟩
  have hsub : ((s : Set E) ∩ ((S : Set E) ∩ T)) ∩ t ⊆ (s : Set E) ∩ t :=
    fun _ hx => ⟨hx.1.1, hx.2⟩
  exact convexHull_mono hsub hxst

def ofGenerators (F : Set (Finset E))
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) : SimplicialComplex 𝕜 E where
  faces := {s | s.Nonempty ∧ ∃ S ∈ F, s ⊆ S}
  isRelLowerSet_faces := by
    rintro s ⟨hs, S, hS, hsS⟩
    exact ⟨hs, fun t hts ht => ⟨ht, S, hS, hts.trans hsS⟩⟩
  indep := by
    rintro s ⟨_, S, hS, hsS⟩
    exact (hind S hS).mono hsS
  inter_subset_convexHull := by
    rintro s t ⟨_, S, hS, hsS⟩ ⟨_, T, hT, htT⟩
    exact subface_inter_subset hind hinter hS hsS hT htT

theorem space_ofGenerators
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) :
    (ofGenerators F hind hinter).space = ⋃ S ∈ F, convexHull 𝕜 (S : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨_, S, hS, hsS⟩, hxs⟩ := mem_space_iff.mp hx
    exact mem_iUnion₂.mpr ⟨S, hS, convexHull_mono hsS hxs⟩
  · intro hx
    obtain ⟨S, hS, hxS⟩ := mem_iUnion₂.mp hx
    have hne : S.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.coe_empty,
        convexHull_empty, notMem_empty] at hxS
    exact mem_space_iff.mpr ⟨S, ⟨hne, S, hS, Finset.Subset.refl _⟩, hxS⟩

end Geometry.SimplicialComplex

end

section

open Set

namespace PoincareMT.M76.Smoothing

def shortArcGapSpace (n : ℕ) (theta : ℝ) : Set (Fin (n + 3) → ℝ) :=
  {w | (∀ i, w i ∈ Ioo (0 : ℝ) Real.pi) ∧
    (∑ i, w i) = 2 * Real.pi ∧ w 0 = theta}

theorem convex_shortArcGapSpace (n : ℕ) (theta : ℝ) :
    Convex ℝ (shortArcGapSpace n theta) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact (convex_Ioo (0 : ℝ) Real.pi) (hx.1 i) (hy.1 i) ha hb hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2.1, hy.2.1, ← add_mul, hab, one_mul]
  · change a * x 0 + b * y 0 = theta
    rw [hx.2.2, hy.2.2, ← add_mul, hab, one_mul]

theorem nonempty_shortArcGapSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) : (shortArcGapSpace n theta).Nonempty := by
  let r : ℝ := (2 * Real.pi - theta) / (n + 2)
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hr0 : 0 < r := div_pos (by linarith [Real.pi_pos, htheta.2]) hn
  have hrpi : r < Real.pi := by
    rw [div_lt_iff₀ hn]
    nlinarith [htheta.1, mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]
  refine ⟨Fin.cons theta (fun _ : Fin (n + 2) => r), ?_, ?_, by simp⟩
  · intro i
    exact Fin.cases htheta (fun _ => ⟨hr0, hrpi⟩) i
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
    dsimp only [r]
    field_simp [ne_of_gt hn]
    ring

theorem contractible_shortArcGapSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (shortArcGapSpace n theta) :=
  (convex_shortArcGapSpace n theta).contractibleSpace (nonempty_shortArcGapSpace n htheta)

end PoincareMT.M76.Smoothing

end

section

open Set

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

def gapAngle (w : Fin (n + 3) → ℝ) (i : Fin (n + 3)) : ℝ :=
  ∑ j ∈ Finset.Iio i, w j

@[simp] theorem gapAngle_zero (w : Fin (n + 3) → ℝ) : gapAngle w 0 = 0 := by
  change (∑ j ∈ Finset.Iio (⊥ : Fin (n + 3)), w j) = 0
  rw [Finset.Iio_bot, Finset.sum_empty]

theorem gapAngle_succ (w : Fin (n + 3) → ℝ) (i : Fin (n + 2)) :
    gapAngle w i.succ = gapAngle w i.castSucc + w i.castSucc := by
  have hset : Finset.Iio i.succ = insert i.castSucc (Finset.Iio i.castSucc) := by
    ext j
    simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def,
      Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    omega
  simp only [gapAngle]
  rw [hset, Finset.sum_insert (by simp)]
  exact add_comm _ _

theorem strictMono_gapAngle {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    StrictMono (gapAngle w) := by
  intro i j hij
  apply Finset.sum_lt_sum_of_subset
    (fun k hk => Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hk).trans hij))
    (Finset.mem_Iio.mpr hij) (by simp) (hw.1 i).1
  intro k _ _
  exact (hw.1 k).1.le

theorem gapAngle_mem_Ico {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta)
    (i : Fin (n + 3)) : gapAngle w i ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  refine ⟨Finset.sum_nonneg (fun j _ => (hw.1 j).1.le), ?_⟩
  calc
    gapAngle w i < ∑ j, w j :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ i)
        (by simp) (hw.1 i).1 (fun j _ _ => (hw.1 j).1.le)
    _ = 2 * Real.pi := hw.2.1

theorem gapAngle_one {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    gapAngle w 1 = theta := by
  have h := gapAngle_succ w (0 : Fin (n + 2))
  simpa [hw.2.2] using h

theorem continuous_gapAngle (i : Fin (n + 3)) :
    Continuous (fun w : Fin (n + 3) → ℝ => gapAngle w i) :=
  continuous_finsetSum _ fun j _ => continuous_apply j

noncomputable def circleGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    AddCircle (2 * Real.pi) := (gapAngle w i : AddCircle (2 * Real.pi))

theorem injective_circleGapVertices (w : shortArcGapSpace n theta) :
    Function.Injective (circleGapVertices w) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro i j hij
  apply (strictMono_gapAngle w.property).injective
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
    (by simpa using gapAngle_mem_Ico w.property i)
    (by simpa using gapAngle_mem_Ico w.property j)).mp hij

end PoincareMT.M76.Smoothing

end

section

open Set

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

theorem gapAngle_last_add (w : Fin (n + 3) → ℝ) :
    gapAngle w (Fin.last (n + 2)) + w (Fin.last (n + 2)) = ∑ i, w i := by
  have hs : Finset.univ = insert (Fin.last (n + 2))
      (Finset.Iio (Fin.last (n + 2))) := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_Iio, true_iff,
      Fin.ext_iff, Fin.lt_def, Fin.val_last]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  exact add_comm _ _

end PoincareMT.M76.Smoothing

end

section

open Set

namespace AddCircle

variable {p a b : ℝ}

end AddCircle

end

section

open Set

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

def circleGapArc (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Set (AddCircle (2 * Real.pi)) :=
  (fun x : ℝ => (x : AddCircle (2 * Real.pi))) '' Icc (gapAngle w i) (gapAngle w i + w.val i)

def circleGapArcInterior (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Set (AddCircle (2 * Real.pi)) :=
  (fun x : ℝ => (x : AddCircle (2 * Real.pi))) '' Ioo (gapAngle w i) (gapAngle w i + w.val i)

theorem gapAngle_add_le_fullTurn (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    gapAngle w i + w.val i ≤ 2 * Real.pi := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (gapAngle_last_add w.val).trans w.property.2.1 |>.le
  · rw [← gapAngle_succ]
    exact (gapAngle_mem_Ico w.property j.succ).2.le

theorem gapAngle_add_le_of_lt (w : shortArcGapSpace n theta)
    {i j : Fin (n + 3)} (hij : i < j) : gapAngle w i + w.val i ≤ gapAngle w j := by
  have hi : i.val < n + 2 := by have := j.isLt; exact Nat.lt_of_lt_of_le hij (by omega)
  let k : Fin (n + 2) := ⟨i.val, hi⟩
  have hki : k.castSucc = i := Fin.ext rfl
  calc
    gapAngle w i + w.val i = gapAngle w k.succ := by rw [← hki, gapAngle_succ]
    _ ≤ gapAngle w j := (strictMono_gapAngle w.property).monotone (by
      change k.val + 1 ≤ j.val
      exact hij)

theorem pairwise_disjoint_circleGapArcInterior (w : shortArcGapSpace n theta) :
    Pairwise (fun i j => Disjoint (circleGapArcInterior w i) (circleGapArcInterior w j)) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro i j hij
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxrange : x ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    ⟨(gapAngle_mem_Ico w.property i).1.trans hx.1.le,
      by simpa using hx.2.trans_le (gapAngle_add_le_fullTurn w i)⟩
  have hyrange : y ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    ⟨(gapAngle_mem_Ico w.property j).1.trans hy.1.le,
      by simpa using hy.2.trans_le (gapAngle_add_le_fullTurn w j)⟩
  have hxy : x = y :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hxrange hyrange).mp (hxz.trans hyz.symm)
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hle := gapAngle_add_le_of_lt w hij
    linarith [hx.2, hy.1]
  · have hle := gapAngle_add_le_of_lt w hji
    linarith [hy.2, hx.1]

theorem circleGapArc_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    ((gapAngle w i + w.val i : ℝ) : AddCircle (2 * Real.pi)) =
      circleGapVertices w (i + 1) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [gapAngle_last_add, w.property.2.1, Fin.last_add_one]
    simp [circleGapVertices, AddCircle.coe_period]
  · rw [Fin.coeSucc_eq_succ, ← gapAngle_succ]
    rfl

theorem circleGapVertex_notMem_arcInterior (w : shortArcGapSpace n theta)
    (i k : Fin (n + 3)) : circleGapVertices w k ∉ circleGapArcInterior w i := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rintro ⟨x, hx, hxk⟩
  have hxrange : x ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
    ⟨(gapAngle_mem_Ico w.property i).1.trans hx.1.le,
      by simpa using hx.2.trans_le (gapAngle_add_le_fullTurn w i)⟩
  change (x : AddCircle (2 * Real.pi)) = (gapAngle w k : AddCircle (2 * Real.pi)) at hxk
  have hxreal : x = gapAngle w k :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hxrange
      (by simpa using gapAngle_mem_Ico w.property k)).mp hxk
  rcases le_or_gt k i with hki | hik
  · have hle := (strictMono_gapAngle w.property).monotone hki
    linarith [hx.1]
  · have hle := gapAngle_add_le_of_lt w hik
    linarith [hx.2]

theorem circleGapArc_eq_interior_union_endpoints (w : shortArcGapSpace n theta)
    (i : Fin (n + 3)) : circleGapArc w i =
      circleGapArcInterior w i ∪ {circleGapVertices w i, circleGapVertices w (i + 1)} := by
  unfold circleGapArc circleGapArcInterior
  rw [← Ioo_union_both (show gapAngle w i ≤ gapAngle w i + w.val i by
    linarith [(w.property.1 i).1]), image_union, image_pair, circleGapArc_endpoint]
  rfl

theorem circleGapArc_inter (w : shortArcGapSpace n theta) {i j : Fin (n + 3)} (hij : i ≠ j) :
    circleGapArc w i ∩ circleGapArc w j =
      {circleGapVertices w i, circleGapVertices w (i + 1)} ∩
        {circleGapVertices w j, circleGapVertices w (j + 1)} := by
  ext z
  rw [circleGapArc_eq_interior_union_endpoints, circleGapArc_eq_interior_union_endpoints]
  constructor
  · rintro ⟨hi, hj⟩
    have hnoti : z ∉ circleGapArcInterior w i := by
      intro hz
      rcases hj with hj | hj
      · exact (pairwise_disjoint_circleGapArcInterior w hij).le_bot ⟨hz, hj⟩
      · rcases hj with rfl | hj
        · exact circleGapVertex_notMem_arcInterior w i j hz
        · rw [mem_singleton_iff] at hj
          subst z
          exact circleGapVertex_notMem_arcInterior w i (j + 1) hz
    have hiends := hi.resolve_left hnoti
    refine ⟨hiends, hj.resolve_left ?_⟩
    intro hz
    rcases hiends with rfl | hiends
    · exact circleGapVertex_notMem_arcInterior w j i hz
    · rw [mem_singleton_iff] at hiends
      subst z
      exact circleGapVertex_notMem_arcInterior w j (i + 1) hz
  · rintro ⟨hi, hj⟩
    exact ⟨Or.inr hi, Or.inr hj⟩

end PoincareMT.M76.Smoothing

end

section

open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

noncomputable def planarGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) : ℂ :=
  Circle.exp (gapAngle w i)

theorem norm_planarGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    ‖planarGapVertices w i‖ = 1 := Circle.norm_coe _

theorem injective_planarGapVertices (w : shortArcGapSpace n theta) :
    Function.Injective (planarGapVertices w) := by
  intro i j hij
  apply injective_circleGapVertices w
  apply AddCircle.homeomorphCircle'.injective
  exact Subtype.ext hij

theorem continuous_planarGapVertices :
    Continuous (planarGapVertices : shortArcGapSpace n theta → Fin (n + 3) → ℂ) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (Circle.exp.continuous.comp
    ((continuous_gapAngle i).comp continuous_subtype_val))

theorem planarGapVertices_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    (Circle.exp (gapAngle w i + w.val i) : ℂ) = planarGapVertices w (i + 1) :=
  congrArg (fun z : AddCircle (2 * Real.pi) => (AddCircle.homeomorphCircle' z : ℂ))
    (circleGapArc_endpoint w i)

theorem linearIndependent_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    LinearIndependent ℝ
      ((↑) : ↥({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) → ℂ) := by
  have h := Complex.linearIndependent_circleExp_pair
    (a := gapAngle w i) (b := gapAngle w i + w.val i)
    (by linarith [(w.property.1 i).1]) (by simpa using (w.property.1 i).2)
  rw [planarGapVertices_endpoint] at h
  exact h

def planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) : Set ℂ :=
  segment ℝ (planarGapVertices w i) (planarGapVertices w (i + 1))

theorem injOn_normalize_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (planarGapEdge w i) := by
  simpa only [convexHull_pair, planarGapEdge] using
    (linearIndependent_planarGapEdge w i).injOn_normalize_convexHull

theorem normalize_image_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    NormedSpace.normalize '' planarGapEdge w i =
      (fun z : AddCircle (2 * Real.pi) => (AddCircle.homeomorphCircle' z : ℂ)) ''
        circleGapArc w i := by
  calc
    NormedSpace.normalize '' planarGapEdge w i =
        (fun phi => (Circle.exp phi : ℂ)) '' Icc (gapAngle w i) (gapAngle w i + w.val i) := by
      unfold planarGapEdge
      rw [← planarGapVertices_endpoint]
      exact Complex.normalize_image_segment_circleExp
        (by linarith [(w.property.1 i).1]) (by simpa using (w.property.1 i).2)
    _ = _ := by rw [circleGapArc, image_image]; rfl

private theorem planar_circle_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3))
    {z : AddCircle (2 * Real.pi)}
    (hz : z ∈ ({circleGapVertices w i, circleGapVertices w (i + 1)} :
      Set (AddCircle (2 * Real.pi)))) :
    (AddCircle.homeomorphCircle' z : ℂ) ∈
      ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) := by
  rcases hz with rfl | hz
  · exact mem_insert _ _
  · rw [mem_singleton_iff] at hz
    subst z
    exact mem_insert_of_mem _ (mem_singleton _)

private theorem planar_endpoint_mem_edge (w : shortArcGapSpace n theta) (i : Fin (n + 3))
    {z : ℂ} (hz : z ∈ ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ)) :
    z ∈ planarGapEdge w i := by
  rw [planarGapEdge, ← convexHull_pair]
  exact subset_convexHull ℝ _ hz

theorem planarGapEdges_common_direction (w : shortArcGapSpace n theta)
    {i j : Fin (n + 3)} (hij : i ≠ j) {x y : ℂ}
    (hx : x ∈ planarGapEdge w i) (hy : y ∈ planarGapEdge w j)
    (hxy : NormedSpace.normalize x = NormedSpace.normalize y) :
    x = y ∧ x ∈ ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) ∩
      {planarGapVertices w j, planarGapVertices w (j + 1)} := by
  obtain ⟨z, hz, hzx⟩ := (normalize_image_planarGapEdge w i).subset ⟨x, hx, rfl⟩
  obtain ⟨z', hz', hzy⟩ := (normalize_image_planarGapEdge w j).subset ⟨y, hy, rfl⟩
  have hzz : z = z' := AddCircle.homeomorphCircle'.injective
    (Subtype.ext (hzx.trans (hxy.trans hzy.symm)))
  subst z'
  have hends := (circleGapArc_inter w hij).subset ⟨hz, hz'⟩
  have he_i := planar_circle_endpoint w i hends.1
  have he_j := planar_circle_endpoint w j hends.2
  have hunit : NormedSpace.normalize (AddCircle.homeomorphCircle' z : ℂ) =
      (AddCircle.homeomorphCircle' z : ℂ) :=
    normalize_eq_self_of_norm_eq_one (Circle.norm_coe _)
  have hxe : x = (AddCircle.homeomorphCircle' z : ℂ) :=
    injOn_normalize_planarGapEdge w i hx (planar_endpoint_mem_edge w i he_i)
      (hzx.symm.trans hunit.symm)
  have hye : y = (AddCircle.homeomorphCircle' z : ℂ) :=
    injOn_normalize_planarGapEdge w j hy (planar_endpoint_mem_edge w j he_j)
      (hzy.symm.trans hunit.symm)
  exact ⟨hxe.trans hye.symm, hxe ▸ ⟨he_i, he_j⟩⟩

theorem injOn_normalize_iUnion_planarGapEdge (w : shortArcGapSpace n theta) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (⋃ i, planarGapEdge w i) := by
  intro x hx y hy hxy
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
  by_cases hij : i = j
  · subst j
    exact injOn_normalize_planarGapEdge w i hxi hyj hxy
  · exact (planarGapEdges_common_direction w hij hxi hyj hxy).1

theorem planarGapEdge_inter_subset (w : shortArcGapSpace n theta) (i j : Fin (n + 3)) :
    planarGapEdge w i ∩ planarGapEdge w j ⊆
      convexHull ℝ ({planarGapVertices w i, planarGapVertices w (i + 1)} ∩
        {planarGapVertices w j, planarGapVertices w (j + 1)}) := by
  by_cases hij : i = j
  · subst j
    rw [inter_self, inter_self, convexHull_pair]
    exact Subset.rfl
  · intro x hx
    exact subset_convexHull ℝ _ (planarGapEdges_common_direction w hij hx.1 hx.2 rfl).2

end PoincareMT.M76.Smoothing

end

section

open Set Geometry NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

noncomputable def planarGapEdgeVertices (w : shortArcGapSpace n theta)
    (i : Fin (n + 3)) : Finset ℂ := by
  classical
  exact {planarGapVertices w i, planarGapVertices w (i + 1)}

private theorem planar_generators_independent (w : shortArcGapSpace n theta) :
    ∀ s ∈ range (planarGapEdgeVertices w), AffineIndependent ℝ ((↑) : s → ℂ) := by
  rintro _ ⟨i, rfl⟩
  have h := (linearIndependent_planarGapEdge w i).affineIndependent
  have he : (planarGapEdgeVertices w i : Set ℂ) =
      {planarGapVertices w i, planarGapVertices w (i + 1)} := by
    simp only [planarGapEdgeVertices, Finset.coe_pair]
  rw [← he] at h
  exact h

private theorem planar_generators_inter (w : shortArcGapSpace n theta) :
    ∀ s ∈ range (planarGapEdgeVertices w), ∀ t ∈ range (planarGapEdgeVertices w),
      convexHull ℝ (s : Set ℂ) ∩ convexHull ℝ (t : Set ℂ) ⊆
        convexHull ℝ ((s : Set ℂ) ∩ t) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  simpa only [planarGapEdgeVertices, Finset.coe_pair, convexHull_pair, planarGapEdge] using
    planarGapEdge_inter_subset w i j

noncomputable def planarCircleComplex (w : shortArcGapSpace n theta) : SimplicialComplex ℝ ℂ :=
  SimplicialComplex.ofGenerators (range (planarGapEdgeVertices w))
    (planar_generators_independent w) (planar_generators_inter w)

theorem mem_planarCircleComplex_faces (w : shortArcGapSpace n theta) (s : Finset ℂ) :
    s ∈ (planarCircleComplex w).faces ↔ s.Nonempty ∧ ∃ i, s ⊆ planarGapEdgeVertices w i := by
  change (s.Nonempty ∧ ∃ t ∈ range (planarGapEdgeVertices w), s ⊆ t) ↔ _
  constructor
  · rintro ⟨hs, _, ⟨i, rfl⟩, hsi⟩
    exact ⟨hs, i, hsi⟩
  · rintro ⟨hs, i, hsi⟩
    exact ⟨hs, _, mem_range_self i, hsi⟩

theorem planarCircleComplex_space (w : shortArcGapSpace n theta) :
    (planarCircleComplex w).space = ⋃ i, planarGapEdge w i := by
  rw [planarCircleComplex, SimplicialComplex.space_ofGenerators]
  ext x
  constructor
  · intro hx
    obtain ⟨_, ⟨i, rfl⟩, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨i, by
      simpa only [planarGapEdgeVertices, Finset.coe_pair, convexHull_pair, planarGapEdge]
        using hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    refine mem_iUnion₂.mpr ⟨_, mem_range_self i, ?_⟩
    simpa only [planarGapEdgeVertices, Finset.coe_pair, convexHull_pair, planarGapEdge] using hxi

theorem linearIndependent_planarCircleComplex_face (w : shortArcGapSpace n theta)
    {s : Finset ℂ} (hs : s ∈ (planarCircleComplex w).faces) :
    LinearIndependent ℝ ((↑) : s → ℂ) := by
  obtain ⟨_, i, hsi⟩ := (mem_planarCircleComplex_faces w s).mp hs
  change LinearIndepOn ℝ id (s : Set ℂ)
  have hi : LinearIndepOn ℝ id
      ({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) :=
    linearIndependent_planarGapEdge w i
  apply hi.mono
  change (s : Set ℂ) ⊆ (planarGapEdgeVertices w i : Set ℂ) at hsi
  simpa only [planarGapEdgeVertices, Finset.coe_pair] using hsi

theorem injOn_normalize_planarCircleComplex (w : shortArcGapSpace n theta) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (planarCircleComplex w).space := by
  rw [planarCircleComplex_space]
  exact injOn_normalize_iUnion_planarGapEdge w

def cyclicEdgeComplex (n : ℕ) : AbstractSimplicialComplex (Fin (n + 3)) where
  faces := {s | s.Nonempty ∧ ∃ i, s ⊆ {i, i + 1}}
  isRelLowerSet_faces := by
    rintro s ⟨hs, i, hsi⟩
    exact ⟨hs, fun t hts ht => ⟨ht, i, hts.trans hsi⟩⟩
  singleton_mem i := ⟨Finset.singleton_nonempty i, i, by simp⟩

theorem planarCircleComplex_faces_image (w : shortArcGapSpace n theta) :
    (planarCircleComplex w).faces =
      {t : Finset ℂ | ∃ s ∈ (cyclicEdgeComplex n).faces,
        (t : Set ℂ) = planarGapVertices w '' (s : Set (Fin (n + 3)))} := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨hne, i, hti⟩ := (mem_planarCircleComplex_faces w t).mp ht
    have hsub : t ⊆ ({i, i + 1} : Finset (Fin (n + 3))).image (planarGapVertices w) := by
      simpa only [Finset.image_insert, Finset.image_singleton, planarGapEdgeVertices] using hti
    obtain ⟨s, hsi, rfl⟩ := Finset.subset_image_iff.mp hsub
    exact ⟨s, ⟨Finset.image_nonempty.mp hne, i, hsi⟩, Finset.coe_image⟩
  · rintro ⟨s, ⟨hs, i, hsi⟩, hts⟩
    have ht : t = s.image (planarGapVertices w) :=
      Finset.coe_injective (hts.trans Finset.coe_image.symm)
    rw [ht, mem_planarCircleComplex_faces]
    refine ⟨Finset.image_nonempty.mpr hs, i, ?_⟩
    simpa only [Finset.image_insert, Finset.image_singleton, planarGapEdgeVertices] using
      Finset.image_subset_image (f := planarGapVertices w) hsi

theorem isRadialEmbedding_planarGapVertices (w : shortArcGapSpace n theta) :
    (cyclicEdgeComplex n).IsRadialEmbedding (planarGapVertices w) :=
  ⟨injective_planarGapVertices w, planarCircleComplex w, planarCircleComplex_faces_image w,
    fun _ hs => linearIndependent_planarCircleComplex_face w hs,
    injOn_normalize_planarCircleComplex w⟩

noncomputable def planarGapEmbedding (w : shortArcGapSpace n theta) :
    (cyclicEdgeComplex n).UnitRadialEmbedding ℂ :=
  ⟨⟨planarGapVertices w, isRadialEmbedding_planarGapVertices w⟩, norm_planarGapVertices w⟩

theorem continuous_planarGapEmbedding :
    Continuous (planarGapEmbedding : shortArcGapSpace n theta →
      (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) :=
  (continuous_planarGapVertices.subtype_mk _).subtype_mk _

end PoincareMT.M76.Smoothing

end

section

open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ}

noncomputable def unitCycleVertex (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : Circle :=
  ⟨v.val.val i, mem_sphere_zero_iff_norm.mpr (v.property i)⟩

noncomputable def cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : ℝ :=
  Circle.shortIncrement (unitCycleVertex v i) (unitCycleVertex v (i + 1))

theorem linearIndependent_unitCycleEdge (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : LinearIndependent ℝ
      ((↑) : ↥({(unitCycleVertex v i : ℂ), (unitCycleVertex v (i + 1) : ℂ)} : Set ℂ) → ℂ) := by
  have hs : ({i, i + 1} : Finset (Fin (n + 3))) ∈ (cyclicEdgeComplex n).faces :=
    ⟨by simp, i, Finset.Subset.refl _⟩
  have h := v.val.property.linearIndependent_face_image hs
  rw [show (({i, i + 1} : Finset (Fin (n + 3))) : Set (Fin (n + 3))) =
    {i, i + 1} from Finset.coe_pair, image_pair] at h
  exact h

theorem cycleIncrement_mem_Ioo (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : cycleIncrement v i ∈ Ioo (-Real.pi) Real.pi :=
  ⟨Circle.neg_pi_lt_shortIncrement _ _,
    Circle.shortIncrement_lt_pi (linearIndependent_unitCycleEdge v i)⟩

theorem unitCycleVertex_mem_normalize_edge_iff
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) (i k : Fin (n + 3)) :
    (unitCycleVertex v k : ℂ) ∈ NormedSpace.normalize ''
      segment ℝ (unitCycleVertex v i : ℂ) (unitCycleVertex v (i + 1)) ↔ k = i ∨ k = i + 1 := by
  have hs : ({i, i + 1} : Finset (Fin (n + 3))) ∈ (cyclicEdgeComplex n).faces :=
    ⟨by simp, i, Finset.Subset.refl _⟩
  have h := v.val.property.vertex_mem_normalize_face_iff hs k
  simpa only [Finset.coe_pair, image_pair, convexHull_pair, Finset.mem_insert,
    Finset.mem_singleton, normalize_eq_self_of_norm_eq_one (v.property k), unitCycleVertex] using h

private theorem cycle_add_one_ne (i : Fin (n + 3)) : i + 1 ≠ i := by
  intro h
  have hzero : (1 : Fin (n + 3)) = 0 := add_left_cancel (h.trans (add_zero i).symm)
  have hv := congrArg Fin.val hzero
  simp only [Fin.val_one, Fin.val_zero] at hv
  omega

private theorem cycle_add_two_ne (i : Fin (n + 3)) : i + 1 + 1 ≠ i := by
  intro h
  have hzero : (1 : Fin (n + 3)) + 1 = 0 := by
    apply add_left_cancel (a := i)
    simpa only [add_assoc, add_zero] using h
  have hv := congrArg Fin.val hzero
  simp only [Fin.val_add, Fin.val_one, Fin.val_zero] at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 + 1 < n + 3)] at hv
  omega

theorem cycleIncrement_pos_next (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) (hi : 0 < cycleIncrement v i) : 0 < cycleIncrement v (i + 1) := by
  let a := Complex.arg (unitCycleVertex v i)
  let b := a + cycleIncrement v i
  let c := b + cycleIncrement v (i + 1)
  have hea : Circle.exp a = unitCycleVertex v i := Circle.exp_arg _
  have heb : Circle.exp b = unitCycleVertex v (i + 1) := by
    dsimp only [b]
    rw [Circle.exp_add, hea]
    exact Circle.mul_exp_shortIncrement _ _
  have hec : Circle.exp c = unitCycleVertex v (i + 1 + 1) := by
    dsimp only [c]
    rw [Circle.exp_add, heb]
    exact Circle.mul_exp_shortIncrement _ _
  have hc : (Circle.exp c : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp a : ℂ) (Circle.exp b) := by
    rw [hea, heb, hec, unitCycleVertex_mem_normalize_edge_iff]
    exact fun h => h.elim (cycle_add_two_ne i) (cycle_add_one_ne (i + 1))
  have ha : (Circle.exp a : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp b : ℂ) (Circle.exp c) := by
    rw [hea, heb, hec, unitCycleVertex_mem_normalize_edge_iff]
    exact fun h => h.elim (Ne.symm (cycle_add_one_ne i)) (Ne.symm (cycle_add_two_ne i))
  have hbc := Complex.lt_of_no_radial_backtracking
    (a := a) (b := b) (c := c) (by dsimp [b]; linarith)
    (by dsimp [b]; linarith [(cycleIncrement_mem_Ioo v i).2])
    (by dsimp [c]; linarith [(cycleIncrement_mem_Ioo v (i + 1)).1]) hc ha
  dsimp only [c] at hbc
  linarith

theorem cycleIncrement_zero (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    cycleIncrement v 0 = theta := by
  change Complex.arg ((unitCycleVertex v (0 + 1) / unitCycleVertex v 0 : Circle) : ℂ) = theta
  rw [zero_add, hzero, hone, div_one]
  exact Circle.arg_exp (by linarith [Real.pi_pos, htheta.1]) htheta.2.le

theorem cycleIncrement_pos (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta)
    (i : Fin (n + 3)) : 0 < cycleIncrement v i := by
  induction i using Fin.induction with
  | zero => rw [cycleIncrement_zero v htheta hzero hone]; exact htheta.1
  | succ i ih =>
      have h := cycleIncrement_pos_next v i.castSucc ih
      simpa only [Fin.coeSucc_eq_succ] using h

end PoincareMT.M76.Smoothing

end

section

open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ}

theorem exp_gapAngle_cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (hzero : unitCycleVertex v 0 = 1) (i : Fin (n + 3)) :
    Circle.exp (gapAngle (cycleIncrement v) i) = unitCycleVertex v i := by
  induction i using Fin.induction with
  | zero => rw [gapAngle_zero, Circle.exp_zero, hzero]
  | succ i ih =>
      rw [gapAngle_succ, Circle.exp_add, ih]
      simpa only [cycleIncrement, Fin.coeSucc_eq_succ] using
        Circle.mul_exp_shortIncrement (unitCycleVertex v i.castSucc)
          (unitCycleVertex v (i.castSucc + 1))

theorem exp_sum_cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (hzero : unitCycleVertex v 0 = 1) : Circle.exp (∑ i, cycleIncrement v i) = 1 := by
  rw [← gapAngle_last_add, Circle.exp_add, exp_gapAngle_cycleIncrement v hzero]
  simpa only [cycleIncrement, Fin.last_add_one, hzero] using
    Circle.mul_exp_shortIncrement (unitCycleVertex v (Fin.last (n + 2)))
      (unitCycleVertex v (Fin.last (n + 2) + 1))

theorem gapAngle_cycleIncrement_lt_fullTurn
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta)
    (i : Fin (n + 3)) : gapAngle (cycleIncrement v) i < 2 * Real.pi := by
  induction i using Fin.induction with
  | zero => rw [gapAngle_zero]; positivity
  | succ i ih =>
      by_cases hi0 : i.castSucc = 0
      · rw [gapAngle_succ, hi0, gapAngle_zero, zero_add]
        linarith [(cycleIncrement_mem_Ioo v 0).2, Real.pi_pos]
      · by_contra hlt
        have hhigh := le_of_not_gt hlt
        have hgap : gapAngle (cycleIncrement v) i.succ -
            gapAngle (cycleIncrement v) i.castSucc = cycleIncrement v i.castSucc := by
          rw [gapAngle_succ]
          ring
        have hpos : gapAngle (cycleIncrement v) i.castSucc <
            gapAngle (cycleIncrement v) i.succ := by
          have hp := cycleIncrement_pos v htheta hzero hone i.castSucc
          linarith
        have hshort : gapAngle (cycleIncrement v) i.succ -
            gapAngle (cycleIncrement v) i.castSucc < Real.pi := by
          rw [hgap]
          exact (cycleIncrement_mem_Ioo v i.castSucc).2
        have hmem : (Circle.exp (2 * Real.pi) : ℂ) ∈ NormedSpace.normalize ''
            segment ℝ (Circle.exp (gapAngle (cycleIncrement v) i.castSucc) : ℂ)
              (Circle.exp (gapAngle (cycleIncrement v) i.succ)) := by
          rw [Complex.normalize_image_segment_circleExp hpos hshort]
          exact ⟨2 * Real.pi, ⟨ih.le, hhigh⟩, rfl⟩
        rw [Circle.exp_two_pi, exp_gapAngle_cycleIncrement v hzero,
          exp_gapAngle_cycleIncrement v hzero] at hmem
        have hends := (unitCycleVertex_mem_normalize_edge_iff v i.castSucc 0).mp
          (by simpa only [Fin.coeSucc_eq_succ, hzero] using hmem)
        rcases hends with he | he
        · exact hi0 he.symm
        · exact Fin.succ_ne_zero i (by simpa only [Fin.coeSucc_eq_succ] using he.symm)

theorem sum_cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    (∑ i, cycleIncrement v i) = 2 * Real.pi := by
  have hpositive : 0 < ∑ i, cycleIncrement v i :=
    Finset.sum_pos (fun i _ => cycleIncrement_pos v htheta hzero hone i) Finset.univ_nonempty
  have hbound : (∑ i, cycleIncrement v i) < 3 * Real.pi := by
    have hlast := gapAngle_cycleIncrement_lt_fullTurn v htheta hzero hone (Fin.last (n + 2))
    have hgap := (cycleIncrement_mem_Ioo v (Fin.last (n + 2))).2
    linarith [gapAngle_last_add (cycleIncrement v)]
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp (exp_sum_cycleIncrement v hzero)
  have hmpos : (0 : ℝ) < m := by nlinarith [Real.pi_pos]
  have hmlt : (m : ℝ) < 2 := by nlinarith [Real.pi_pos]
  have hmpos' : (0 : ℤ) < m := by exact_mod_cast hmpos
  have hmlt' : m < (2 : ℤ) := by exact_mod_cast hmlt
  have hmone : m = 1 := by omega
  simpa only [hmone, Int.cast_one, one_mul] using hm

theorem cycleIncrement_mem_shortArcGapSpace
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    cycleIncrement v ∈ shortArcGapSpace n theta :=
  ⟨fun i => ⟨cycleIncrement_pos v htheta hzero hone i, (cycleIncrement_mem_Ioo v i).2⟩,
    sum_cycleIncrement v htheta hzero hone, cycleIncrement_zero v htheta hzero hone⟩

theorem planarGapVertices_cycleIncrement
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    planarGapVertices ⟨cycleIncrement v, cycleIncrement_mem_shortArcGapSpace v htheta hzero hone⟩ =
      v.val.val := by
  funext i
  exact congrArg (fun z : Circle => (z : ℂ)) (exp_gapAngle_cycleIncrement v hzero i)

end PoincareMT.M76.Smoothing

end

section

open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

def normalizedUnitCycleSpace (n : ℕ) (theta : ℝ) :
    Set ((cyclicEdgeComplex n).UnitRadialEmbedding ℂ) :=
  {v | unitCycleVertex v 0 = 1 ∧ unitCycleVertex v 1 = Circle.exp theta}

theorem unitCycleVertex_planarGapEmbedding (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    unitCycleVertex (planarGapEmbedding w) i = Circle.exp (gapAngle w i) := rfl

noncomputable def normalizedGapEmbedding (w : shortArcGapSpace n theta) :
    normalizedUnitCycleSpace n theta :=
  ⟨planarGapEmbedding w, by
    constructor
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_zero, Circle.exp_zero]
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_one w.property]⟩

theorem cycleIncrement_planarGapEmbedding (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    cycleIncrement (planarGapEmbedding w) i = w.val i := by
  have hend : unitCycleVertex (planarGapEmbedding w) (i + 1) =
      unitCycleVertex (planarGapEmbedding w) i * Circle.exp (w.val i) := by
    rw [unitCycleVertex_planarGapEmbedding, unitCycleVertex_planarGapEmbedding,
      ← Circle.exp_add]
    apply Circle.ext
    exact (planarGapVertices_endpoint w i).symm
  unfold cycleIncrement Circle.shortIncrement
  rw [hend, mul_div_cancel_left]
  exact Circle.arg_exp (by linarith [Real.pi_pos, (w.property.1 i).1]) (w.property.1 i).2.le

theorem continuous_unitCycleVertex (i : Fin (n + 3)) :
    Continuous (fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ => unitCycleVertex v i) :=
  ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem continuous_cycleIncrement :
    Continuous (cycleIncrement : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ →
      Fin (n + 3) → ℝ) := by
  apply continuous_pi
  intro i
  have hc : Continuous (fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ =>
      ((unitCycleVertex v (i + 1) / unitCycleVertex v i : Circle) : ℂ)) :=
    continuous_subtype_val.comp
      ((continuous_unitCycleVertex (i + 1)).div' (continuous_unitCycleVertex i))
  apply continuous_iff_continuousAt.mpr
  intro v
  have hs : ((unitCycleVertex v (i + 1) / unitCycleVertex v i : Circle) : ℂ) ∈
      Complex.slitPlane :=
    Complex.mem_slitPlane_iff_arg.mpr
      ⟨(cycleIncrement_mem_Ioo v i).2.ne, Circle.coe_ne_zero _⟩
  exact (Complex.continuousAt_arg hs).comp
    (f := fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ =>
      ((unitCycleVertex v (i + 1) / unitCycleVertex v i : Circle) : ℂ)) hc.continuousAt

noncomputable def gapUnitCycleHomeomorph (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    shortArcGapSpace n theta ≃ₜ normalizedUnitCycleSpace n theta where
  toFun := normalizedGapEmbedding
  invFun v := ⟨cycleIncrement v.val,
    cycleIncrement_mem_shortArcGapSpace v.val htheta v.property.1 v.property.2⟩
  left_inv w := Subtype.ext (funext (cycleIncrement_planarGapEmbedding w))
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact planarGapVertices_cycleIncrement v.val htheta v.property.1 v.property.2
  continuous_toFun := continuous_planarGapEmbedding.subtype_mk _
  continuous_invFun := (continuous_cycleIncrement.comp continuous_subtype_val).subtype_mk _

theorem contractible_normalizedUnitCycleSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (normalizedUnitCycleSpace n theta) := by
  let := contractible_shortArcGapSpace n htheta
  exact (gapUnitCycleHomeomorph n htheta).symm.contractibleSpace

end PoincareMT.M76.Smoothing

end

section

open Set

namespace PoincareMT.M76.Smoothing

noncomputable def cycleFrame (n : ℕ) (theta : ℝ) (i : Fin (n + 3)) : ℂ :=
  if i = 0 then 1 else Circle.exp theta

theorem fixedCycleVertexValues_iff {n : ℕ} {theta : ℝ}
    (v : (cyclicEdgeComplex n).RadialEmbedding ℂ) :
    EqOn v.val (cycleFrame n theta) ({0, 1} : Set (Fin (n + 3))) ↔
      v.val 0 = 1 ∧ v.val 1 = (Circle.exp theta : ℂ) := by
  have hne : (1 : Fin (n + 3)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_one, Fin.val_zero] at hv
    omega
  constructor
  · intro h
    exact ⟨by simpa [cycleFrame] using h (by simp : (0 : Fin (n + 3)) ∈
      ({0, 1} : Set (Fin (n + 3)))),
      by simpa only [cycleFrame, if_neg hne] using h (by simp : (1 : Fin (n + 3)) ∈
        ({0, 1} : Set (Fin (n + 3))))⟩
  · rintro ⟨hzero, hone⟩ i (rfl | hi)
    · simpa [cycleFrame] using hzero
    · rw [mem_singleton_iff] at hi
      subst i
      simpa only [cycleFrame, if_neg hne] using hone

abbrev FixedEdgeCycleSpace (n : ℕ) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedRadialEmbedding ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)

noncomputable def fixedUnitCycleHomeomorph (n : ℕ) (theta : ℝ) :
    (cyclicEdgeComplex n).FixedUnitRadialEmbedding ({0, 1} : Set (Fin (n + 3)))
      (cycleFrame n theta) ≃ₜ normalizedUnitCycleSpace n theta := by
  apply Homeomorph.setCongr
  ext v
  change EqOn v.val.val (cycleFrame n theta) ({0, 1} : Set (Fin (n + 3))) ↔
    unitCycleVertex v 0 = 1 ∧ unitCycleVertex v 1 = Circle.exp theta
  rw [fixedCycleVertexValues_iff]
  constructor
  · rintro ⟨hzero, hone⟩
    exact ⟨Circle.ext hzero, Circle.ext hone⟩
  · rintro ⟨hzero, hone⟩
    exact ⟨congrArg (fun z : Circle => (z : ℂ)) hzero,
      congrArg (fun z : Circle => (z : ℂ)) hone⟩

theorem contractible_fixedEdgeCycleSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) : ContractibleSpace (FixedEdgeCycleSpace n theta) := by
  apply (AbstractSimplicialComplex.contractible_fixedRadialEmbedding_iff
    (cyclicEdgeComplex n) ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta) ?_).mpr
  · let := contractible_normalizedUnitCycleSpace n htheta
    exact (fixedUnitCycleHomeomorph n theta).contractibleSpace
  · intro i _
    dsimp only [cycleFrame]
    split_ifs
    · exact norm_one
    · exact Circle.norm_coe _

end PoincareMT.M76.Smoothing

end

section

open Set

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev CycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedBasisRadialProjection b
    ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)

theorem contractible_cycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (CycleProjectionSpace n b theta) := by
  let := contractible_fixedEdgeCycleSpace n htheta
  exact (AbstractSimplicialComplex.fixedBasisRadialProjectionHomeomorph
    (cyclicEdgeComplex n) b ({0, 1} : Set (Fin (n + 3)))
    (cycleFrame n theta)).contractibleSpace

end PoincareMT.M76.Smoothing

end

section

open Set

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def cycleFrameInclusion {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight (b 0) + Complex.imCLM.smulRight (b 1)

theorem cycleFrameInclusion_one {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b 1 = b 0 := by simp [cycleFrameInclusion]

theorem cycleFrameInclusion_I {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b Complex.I = b 1 := by simp [cycleFrameInclusion]

theorem injective_cycleFrameInclusion {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    Function.Injective (cycleFrameInclusion b) := by
  have hne : (0 : Fin (n + 3)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_one] at hv
    omega
  intro z w h
  apply Complex.ext
  · have he := congrArg (fun x => b.repr x 0) h
    simpa [cycleFrameInclusion, hne, Ne.symm hne] using he
  · have he := congrArg (fun x => b.repr x 1) h
    simpa [cycleFrameInclusion, hne, Ne.symm hne] using he

theorem rightInverse_cycleFrameInclusion_iff {n : ℕ}
    (b : Module.Basis (Fin (n + 3)) ℝ E) (Q : E →L[ℝ] ℂ) :
    Function.RightInverse (cycleFrameInclusion b) Q ↔ Q (b 0) = 1 ∧ Q (b 1) = Complex.I := by
  constructor
  · intro h
    exact ⟨by simpa only [cycleFrameInclusion_one] using h 1,
      by simpa only [cycleFrameInclusion_I] using h Complex.I⟩
  · rintro ⟨hzero, hone⟩ z
    change Q (z.re • b 0 + z.im • b 1) = z
    rw [map_add, map_smul, map_smul, hzero, hone, Complex.real_smul, Complex.real_smul,
      mul_one, Complex.re_add_im]

theorem rightInverse_cycleFrameInclusion_iff_fixed {n : ℕ}
    (b : Module.Basis (Fin (n + 3)) ℝ E)
    (Q : (cyclicEdgeComplex n).BasisRadialProjection b ℂ) :
    Function.RightInverse (cycleFrameInclusion b) Q.val ↔
      EqOn (fun i => Q.val (b i)) (cycleFrame n (Real.pi / 2)) ({0, 1} : Set (Fin (n + 3))) := by
  rw [rightInverse_cycleFrameInclusion_iff]
  have he : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
    rw [Circle.coe_exp]
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using Complex.exp_pi_div_two_mul_I
  simpa only [he] using (fixedCycleVertexValues_iff (theta := Real.pi / 2)
    (⟨fun i => Q.val (b i), Q.property⟩ : (cyclicEdgeComplex n).RadialEmbedding ℂ)).symm

noncomputable def cycleFrameProjectionHomeomorph (n : ℕ)
    (b : Module.Basis (Fin (n + 3)) ℝ E) :
    {Q : (cycleFrameInclusion b).FrameProjectionSpace //
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q.val (b i))} ≃ₜ
      CycleProjectionSpace n b (Real.pi / 2) where
  toFun Q := ⟨⟨Q.val.val, Q.property⟩,
    (rightInverse_cycleFrameInclusion_iff_fixed b ⟨Q.val.val, Q.property⟩).mp Q.val.property⟩
  invFun Q := ⟨⟨Q.val.val, (rightInverse_cycleFrameInclusion_iff_fixed b Q.val).mpr Q.property⟩,
    Q.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun _ => _) |>.subtype_mk (fun _ => _)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun _ => _) |>.subtype_mk (fun _ => _)

end PoincareMT.M76.Smoothing

end

section

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev CycleFrameRadialOperatorSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (cycleFrameInclusion b) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}

noncomputable def cycleFrameRadialOperatorHomeomorph (n : ℕ)
    (b : Module.Basis (Fin (n + 3)) ℝ E) :
    CycleFrameRadialOperatorSpace n b ≃ₜ CycleProjectionSpace n b (Real.pi / 2) := by
  let e : CycleFrameRadialOperatorSpace n b ≃ₜ
      {Q : (cycleFrameInclusion b).FrameProjectionSpace //
        (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q.val (b i))} :=
    { toFun := fun Q => ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
      invFun := fun Q => ⟨Q.val.val, Q.val.property, Q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun _ => _) }
  exact e.trans (cycleFrameProjectionHomeomorph n b)

abbrev AmbientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (V.subtypeL.comp (cycleFrameInclusion b)) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}

noncomputable def ambientCycleProjectionHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    AmbientCycleProjectionSpace n V b ≃ₜ
      (CycleProjectionSpace n b (Real.pi / 2) × (Vᗮ →L[ℝ] ℂ)) :=
  (V.operatorRestrictionHomeomorph (fun R : V →L[ℝ] ℂ =>
    Function.RightInverse (cycleFrameInclusion b) R ∧
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => R (b i)))).trans
        ((cycleFrameRadialOperatorHomeomorph n b).prodCongr (Homeomorph.refl _))

theorem contractible_ambientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (AmbientCycleProjectionSpace n V b) := by
  let := contractible_cycleProjectionSpace n b
    (show Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi from
      ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩)
  exact (ambientCycleProjectionHomeomorph n V b).contractibleSpace

end PoincareMT.M76.Smoothing

end

section

open Set ContinuousLinearMap

namespace PoincareMT.M76.Smoothing

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup T] [NormedSpace ℝ T]

noncomputable def ambientCycleFrameEmbeddingHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space) ≃ₜ
      AmbientCycleProjectionSpace n V b :=
  Homeomorph.setCongr (by
    ext Q
    exact and_congr Iff.rfl
      ((cyclicEdgeComplex n).isRadialEmbedding_iff_injOn_basisCone_subtype V b Q).symm)

theorem contractible_ambientCycleFrameEmbeddingSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space)) := by
  let := contractible_ambientCycleProjectionSpace n V b
  exact (ambientCycleFrameEmbeddingHomeomorph n V b).contractibleSpace

end PoincareMT.M76.Smoothing

end

section

open Set Geometry ContinuousLinearMap AbstractSimplicialComplex

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem contractible_cyclicFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {n : ℕ}
    (e : Fin (n + 3) ≃ (K.faceLink s).vertices)
    (hfaces : ∀ t : Finset (Fin (n + 3)),
      t ∈ (cyclicEdgeComplex n).faces ↔
        t.map e.toEmbedding ∈ (K.faceLink s).vertexAbstractComplex.faces) :
    ContractibleSpace (SecantTransversePlaneSpace
      (2 + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction)
      (K.closedFaceStar s).space) := by
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ affineSpan ℝ (s : Set E) := mem_affineSpan ℝ hps
  let L := (affineSpan ℝ (s : Set E)).direction
  let f := L.normalAffineProjection p
  let v := K.faceNormalRadialEmbedding hK hs hp
  have hw : LinearIndependent ℝ (fun i => f (e i)) :=
    (K.linearIndependent_faceLink_normal hK hs hp).comp e e.injective
  let w : (cyclicEdgeComplex n).RadialEmbedding ↥(Lᗮ) :=
    ⟨fun i => f (e i), (cyclicEdgeComplex n).isRadialEmbedding_of_linearIndependent hw⟩
  let V := Submodule.span ℝ (range w.val)
  let b : Module.Basis (Fin (n + 3)) ℝ V := Module.Basis.span hw
  let J := V.subtypeL.comp (cycleFrameInclusion b)
  have hJ : Function.Injective J :=
    fun x y h => injective_cycleFrameInclusion b (Subtype.val_injective h)
  have hnormal : f '' (K.closedFaceStar s).space =
      V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space := by
    rw [K.normal_image_closedFaceStar hK hs hp]
    have hcone : w.cone = v.cone := v.cone_eq_of_reindex w e hfaces (fun _ => rfl)
    rw [w.subtype_basis_span_cone_space hw, hcone]
  let : ContractibleSpace (FrameEmbeddingSpace J (f '' (K.closedFaceStar s).space)) := by
    rw [hnormal]
    exact contractible_ambientCycleFrameEmbeddingSpace n V b
  let t : Finset E := {(e 0 : E), (e 1 : E)}
  have htlink : t ∈ (K.faceLink s).faces := by
    have h := (hfaces {0, 1}).mp
      (show ({0, 1} : Finset (Fin (n + 3))) ∈ (cyclicEdgeComplex n).faces from
        ⟨Finset.insert_nonempty _ _, 0, by simp⟩)
    change (({0, 1} : Finset (Fin (n + 3))).map e.toEmbedding).map
      (Function.Embedding.subtype _) ∈ (K.faceLink s).faces at h
    simpa only [Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype, Equiv.coe_toEmbedding] using h
  have ht : s ∪ t ∈ (K.closedFaceStar s).faces :=
    ⟨htlink.2.2, by simpa only [← Finset.union_assoc, Finset.union_self] using htlink.2.2⟩
  let U := affineSpan ℝ ((s ∪ t : Finset E) : Set E)
  have hsub : affineSpan ℝ (s : Set E) ≤ U :=
    affineSpan_mono ℝ (show (s : Set E) ⊆ ((s ∪ t : Finset E) : Set E) from
      Finset.subset_union_left)
  have hvertices : ∀ i ∈ ({0, 1} : Finset (Fin (n + 3))), (f (e i) : E) ∈ U.direction := by
    intro i hi
    apply AffineSubspace.normalAffineProjection_mem_direction _ U hsub hp
    apply mem_affineSpan ℝ
    apply Finset.mem_union_right s
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hb : ∀ i, (V.subtype (b i) : ↥(Lᗮ)) = f (e i) :=
    fun i => Module.Basis.coe_span_apply hw i
  have hframe : (L.frameWithTangent J).range ≤ U.direction := by
    apply L.frameWithTangent_range_le U.direction J (AffineSubspace.direction_le hsub)
    intro z
    change ((V.subtype (z.re • b 0 + z.im • b 1) : ↥(Lᗮ)) : E) ∈ U.direction
    rw [map_add, map_smul, map_smul, hb, hb]
    exact U.direction.add_mem (U.direction.smul_mem z.re (hvertices 0 (by simp)))
      (U.direction.smul_mem z.im (hvertices 1 (by simp)))
  have h := K.contractible_faceStarTransversePlaneSpace hK hs hp J hJ ht hframe
  rwa [Complex.finrank_real_complex] at h

end PoincareMT.M76.Smoothing

end

section

open Set Geometry

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem contractible_faceStarPlanes_of_link_incidence (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hc : IsConnected (K.faceLink s).space)
    (hdim : ∀ t ∈ (K.faceLink s).faces, t.card ≤ 2)
    (hlinks : ∀ u : (K.faceLink s).vertices,
      (K.faceLink (s ∪ {u.val})).vertices.ncard = 2) :
    ContractibleSpace (SecantTransversePlaneSpace
      (2 + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction)
      (K.closedFaceStar s).space) := by
  let L := K.faceLink s
  have hL : L.faces.Finite := SimplicialComplex.finite_faceLink_faces hfinite s
  let : Finite L.vertices := (L.finite_vertices_of_finite_faces hL).to_subtype
  have hdim' : ∀ t ∈ L.vertexAbstractComplex.faces, t.card ≤ 2 := by
    intro t ht
    simpa only [Finset.card_map] using hdim (t.map (Function.Embedding.subtype _)) ht
  have hdegree : ∀ u, (L.vertexAbstractComplex.edgeGraph.neighborSet u).ncard = 2 := by
    intro u
    rw [K.ncard_faceLink_edgeGraph_neighborSet s u]
    exact hlinks u
  obtain ⟨n, e, he⟩ := L.vertexAbstractComplex.exists_cyclic_face_labels hdim'
    (L.connected_edgeGraph_of_isConnected hL hc) hdegree
  exact contractible_cyclicFaceStarPlanes K hK hs e (fun t => (he t).symm)

end PoincareMT.M76.Smoothing

end

section

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def twoRayStar (u v : E) : Set E := segment ℝ 0 u ∪ segment ℝ 0 v

private theorem segment_zero_eq_image (u : E) :
    segment ℝ 0 u = (fun a : ℝ => a • u) '' Icc (0 : ℝ) 1 := by
  simpa only [smul_zero, zero_add] using segment_eq_image ℝ (0 : E) u

theorem injOn_twoRayStar_iff (u v : E) (hv : LinearIndependent ℝ ![u, v])
    (Q : E →L[ℝ] ℝ) (hu : Q u = 1) : InjOn Q (twoRayStar u v) ↔ Q v < 0 := by
  constructor
  · intro h
    by_contra hn
    have hq : 0 ≤ Q v := le_of_not_gt hn
    have hd : 0 < 1 + Q v := by linarith
    let a : ℝ := Q v / (1 + Q v)
    let b : ℝ := 1 / (1 + Q v)
    have ha : a ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hq hd.le, (div_le_one hd).mpr (by linarith)⟩
    have hb : b ∈ Icc (0 : ℝ) 1 :=
      ⟨(div_pos one_pos hd).le, (div_le_one hd).mpr (by linarith)⟩
    have he : a • u = b • v := h
      (Or.inl (segment_zero_eq_image u ▸ mem_image_of_mem _ ha))
      (Or.inr (segment_zero_eq_image v ▸ mem_image_of_mem _ hb)) (by
        rw [map_smul, map_smul, hu]
        change a * 1 = b * Q v
        dsimp only [a, b]
        ring)
    have hbzero := (hv.eq_zero_of_pair' he).2
    exact (div_pos one_pos hd).ne' hbzero
  · intro hvneg x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      have hab : a = b := by simpa only [map_smul, hu, smul_eq_mul, mul_one] using he
      rw [hab]
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have he' : a = b * Q v := by simpa only [map_smul, hu, smul_eq_mul, mul_one] using he
      have hb0 : b = 0 := by nlinarith [ha.1, hb.1]
      have ha0 : a = 0 := by simpa only [hb0, zero_mul] using he'
      simp only [ha0, hb0, zero_smul]
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have he' : a * Q v = b := by simpa only [map_smul, hu, smul_eq_mul, mul_one] using he
      have ha0 : a = 0 := by nlinarith [ha.1, hb.1]
      have hb0 : b = 0 := by simpa only [ha0, zero_mul] using he'.symm
      simp only [ha0, hb0, zero_smul]
    · rw [segment_zero_eq_image] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      have he' : a * Q v = b * Q v := by simpa only [map_smul, smul_eq_mul] using he
      rw [mul_right_cancel₀ hvneg.ne he']

end Geometry

end

section

open Set Geometry ContinuousLinearMap

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rightInverse_rayFrame_iff (u : E) (Q : E →L[ℝ] ℝ) :
    Function.RightInverse (toSpanSingleton ℝ u) Q ↔ Q u = 1 := by
  constructor
  · intro h
    simpa only [toSpanSingleton_apply_one] using h 1
  · intro h r
    change Q (r • u) = r
    rw [map_smul, h, smul_eq_mul, mul_one]

theorem convex_twoPointOperatorSet (u v : E) :
    Convex ℝ {Q : E →L[ℝ] ℝ | Q u = 1 ∧ Q v < 0} := by
  intro Q hQ R hR a b ha hb hab
  constructor
  · change a * Q u + b * R u = 1
    rw [hQ.1, hR.1, mul_one, mul_one, hab]
  · change a * Q v + b * R v < 0
    exact convex_Iio (0 : ℝ) hQ.2 hR.2 ha hb hab

noncomputable def twoPointFrameEmbeddingHomeomorph (u v : E)
    (hv : LinearIndependent ℝ ![u, v]) :
    FrameEmbeddingSpace (toSpanSingleton ℝ u) (twoRayStar u v) ≃ₜ
      {Q : E →L[ℝ] ℝ // Q u = 1 ∧ Q v < 0} :=
  Homeomorph.setCongr (by
    ext Q
    change (Function.RightInverse (toSpanSingleton ℝ u) Q ∧ InjOn Q (twoRayStar u v)) ↔ _
    rw [rightInverse_rayFrame_iff]
    exact and_congr_right (fun hu => injOn_twoRayStar_iff u v hv Q hu))

end PoincareMT.M76.Smoothing

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem nonempty_twoPointOperatorSet (u v : E) (hv : LinearIndependent ℝ ![u, v]) :
    ({Q : E →L[ℝ] ℝ | Q u = 1 ∧ Q v < 0} : Set (E →L[ℝ] ℝ)).Nonempty := by
  let V := Submodule.span ℝ (range ![u, v])
  let b : Module.Basis (Fin 2) ℝ V := Module.Basis.span hv
  let A : V →L[ℝ] ℝ := (b.coord 0 - b.coord 1).toContinuousLinearMap
  let Q : E →L[ℝ] ℝ := A.comp V.orthogonalProjectionOnto
  have hzero : (b 0 : E) = u := Module.Basis.coe_span_apply hv 0
  have hone : (b 1 : E) = v := Module.Basis.coe_span_apply hv 1
  refine ⟨Q, ?_, ?_⟩
  · rw [← hzero]
    simp [Q, A, Module.Basis.coord_apply]
  · rw [← hone]
    simp [Q, A, Module.Basis.coord_apply]

theorem contractible_twoPointFrameEmbeddingSpace (u v : E)
    (hv : LinearIndependent ℝ ![u, v]) :
    ContractibleSpace (FrameEmbeddingSpace (toSpanSingleton ℝ u) (twoRayStar u v)) := by
  let : ContractibleSpace {Q : E →L[ℝ] ℝ // Q u = 1 ∧ Q v < 0} :=
    (convex_twoPointOperatorSet u v).contractibleSpace (nonempty_twoPointOperatorSet u v hv)
  exact (twoPointFrameEmbeddingHomeomorph u v hv).contractibleSpace

end PoincareMT.M76.Smoothing

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E]

theorem affine_image_closedFaceStar_twoPoint (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0) {u v : E}
    (hlink : (K.faceLink s).faces = {({u} : Finset E), {v}}) :
    f '' (K.closedFaceStar s).space = twoRayStar (f u) (f v) := by
  rw [K.affine_image_closedFaceStar hs f hf, hlink]
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
    rcases ht with rfl | rfl | rfl
    · have hy0 : y = 0 := by simpa only [Finset.coe_empty, image_empty,
        insert_empty_eq, convexHull_singleton, mem_singleton_iff] using hyt
      subst y
      exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inl (by
        simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hyt)
    · exact Or.inr (by
        simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hyt)
  · rintro (hy | hy)
    · refine mem_iUnion₂.mpr ⟨{u}, Or.inr (Or.inl rfl), ?_⟩
      simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hy
    · refine mem_iUnion₂.mpr ⟨{v}, Or.inr (Or.inr rfl), ?_⟩
      simpa only [Finset.coe_singleton, image_singleton, convexHull_pair] using hy

theorem affine_image_closedFaceStar_emptyLink (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0) (hlink : (K.faceLink s).faces = ∅) :
    f '' (K.closedFaceStar s).space = {0} := by
  rw [K.affine_image_closedFaceStar hs f hf, hlink]
  simp only [insert_empty_eq, mem_singleton_iff, iUnion_iUnion_eq_left,
    Finset.coe_empty, image_empty, convexHull_singleton]

end Geometry.SimplicialComplex

end

section

open Set Geometry ContinuousLinearMap

namespace PoincareMT.M76.Smoothing

section Singleton

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F]

theorem contractible_singletonFrameEmbeddingSpace (J : F →L[ℝ] E) :
    ContractibleSpace (FrameEmbeddingSpace J ({0} : Set E)) := by
  have : Nonempty (FrameEmbeddingSpace J ({0} : Set E)) := by
    refine ⟨⟨0, (fun _ => Subsingleton.elim _ _), ?_⟩⟩
    intro x hx y hy _
    exact (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm
  infer_instance

end Singleton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem contractible_twoPointFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {u v : E} (huv : u ≠ v)
    (hlink : (K.faceLink s).faces = {({u} : Finset E), {v}}) :
    ContractibleSpace (SecantTransversePlaneSpace
      (1 + Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction) (K.closedFaceStar s).space) := by
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ affineSpan ℝ (s : Set E) := mem_affineSpan ℝ hps
  let L := (affineSpan ℝ (s : Set E)).direction
  let f := L.normalAffineProjection p
  have hf : ∀ x ∈ s, f x = 0 := fun x hx =>
    L.normalAffineProjection_eq_zero p
      ((affineSpan ℝ (s : Set E)).vsub_mem_direction (mem_affineSpan ℝ hx) hp)
  have hu : u ∈ (K.faceLink s).vertices := by
    change {u} ∈ (K.faceLink s).faces
    rw [hlink]
    exact Or.inl rfl
  have hv : v ∈ (K.faceLink s).vertices := by
    change {v} ∈ (K.faceLink s).faces
    rw [hlink]
    exact Or.inr rfl
  let labels : Fin 2 → (K.faceLink s).vertices := ![⟨u, hu⟩, ⟨v, hv⟩]
  have hlabels : Function.Injective labels := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (huv (congrArg Subtype.val hij)).elim
    · exact (huv (congrArg Subtype.val hij).symm).elim
    · rfl
  have hpair : LinearIndependent ℝ ![f u, f v] := by
    convert (K.linearIndependent_faceLink_normal hK hs hp).comp labels hlabels using 1
    funext i
    fin_cases i <;> rfl
  let J : ℝ →L[ℝ] ↥(Lᗮ) := toSpanSingleton ℝ (f u)
  have hJ : Function.Injective J := smul_left_injective ℝ (hpair.ne_zero 0)
  have hnormal : f '' (K.closedFaceStar s).space = twoRayStar (f u) (f v) :=
    K.affine_image_closedFaceStar_twoPoint hs f hf hlink
  let : ContractibleSpace (FrameEmbeddingSpace J (f '' (K.closedFaceStar s).space)) := by
    rw [hnormal]
    exact contractible_twoPointFrameEmbeddingSpace (f u) (f v) hpair
  have ht : s ∪ {u} ∈ (K.closedFaceStar s).faces :=
    ⟨hu.2.2, by simpa only [← Finset.union_assoc, Finset.union_self] using hu.2.2⟩
  have hframe : (L.frameWithTangent J).range ≤
      (affineSpan ℝ ((s ∪ {u} : Finset E) : Set E)).direction := by
    apply AffineSubspace.normalLineFrame_range_le_direction _ _
      (affineSpan_mono ℝ (show (s : Set E) ⊆ ((s ∪ {u} : Finset E) : Set E) from
        Finset.subset_union_left)) hp
    exact mem_affineSpan ℝ (Finset.mem_union_right s (Finset.mem_singleton_self u))
  have h := K.contractible_faceStarTransversePlaneSpace hK hs hp J hJ ht hframe
  rwa [CommSemiring.finrank_self] at h

theorem contractible_emptyLinkFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) (hlink : (K.faceLink s).faces = ∅) :
    ContractibleSpace (SecantTransversePlaneSpace
      (Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction) (K.closedFaceStar s).space) := by
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ affineSpan ℝ (s : Set E) := mem_affineSpan ℝ hps
  let L := (affineSpan ℝ (s : Set E)).direction
  let f := L.normalAffineProjection p
  have hf : ∀ x ∈ s, f x = 0 := fun x hx =>
    L.normalAffineProjection_eq_zero p
      ((affineSpan ℝ (s : Set E)).vsub_mem_direction (mem_affineSpan ℝ hx) hp)
  let J : (Fin 0 → ℝ) →L[ℝ] ↥(Lᗮ) := 0
  have hJ : Function.Injective J := fun _ _ _ => Subsingleton.elim _ _
  have hnormal : f '' (K.closedFaceStar s).space = {0} :=
    K.affine_image_closedFaceStar_emptyLink hs f hf hlink
  let : ContractibleSpace (FrameEmbeddingSpace J (f '' (K.closedFaceStar s).space)) := by
    rw [hnormal]
    exact contractible_singletonFrameEmbeddingSpace J
  have ht : s ∈ (K.closedFaceStar s).faces := ⟨hs, by simpa only [Finset.union_self] using hs⟩
  have hframe : (L.frameWithTangent J).range ≤ (affineSpan ℝ (s : Set E)).direction :=
    L.frameWithTangent_range_le L J le_rfl (fun _ => L.zero_mem)
  have h := K.contractible_faceStarTransversePlaneSpace hK hs hp J hJ ht hframe
  rwa [Module.finrank_zero_of_subsingleton, zero_add] at h

end PoincareMT.M76.Smoothing

end

section

open Set Geometry

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem contractible_positiveFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    {s : Finset E} (hs : s ∈ K.faces) (hpositive : 2 ≤ s.card) :
    ContractibleSpace (SecantTransversePlaneSpace 3 (K.closedFaceStar s).space) := by
  have hle := hbound s hs
  have hcases : s.card = 2 ∨ s.card = 3 ∨ s.card = 4 := by omega
  rcases hcases with htwo | hthree | hfour
  · have hdim : ∀ t ∈ (K.faceLink s).faces, t.card ≤ 2 := by
      intro t ht
      have h := K.card_add_card_le_of_mem_faceLink hbound s ht
      omega
    have hlinks : ∀ u : (K.faceLink s).vertices,
        (K.faceLink (s ∪ {u.val})).vertices.ncard = 2 := by
      intro u
      apply htriangles (s ∪ {u.val}) u.property.2.2
      rw [Finset.card_union_of_disjoint u.property.2.1, Finset.card_singleton, htwo]
    have h := contractible_faceStarPlanes_of_link_incidence K hK hfinite hs
      (hedges s hs htwo) hdim hlinks
    rwa [K.finrank_faceDirection_of_card hs (n := 1) htwo] at h
  · have hdim : ∀ t ∈ (K.faceLink s).faces, t.card ≤ 1 := by
      intro t ht
      have h := K.card_add_card_le_of_mem_faceLink hbound s ht
      omega
    obtain ⟨u, v, huv, hlink⟩ := (K.faceLink s).exists_faces_eq_two_singletons hdim
      (htriangles s hs hthree)
    have h := contractible_twoPointFaceStarPlanes K hK hs huv hlink
    rwa [K.finrank_faceDirection_of_card hs (n := 2) hthree] at h
  · have hlink := K.faceLink_faces_eq_empty_of_card_eq hbound hfour
    have h := contractible_emptyLinkFaceStarPlanes K hK hs hlink
    rwa [K.finrank_faceDirection_of_card hs (n := 3) hfour] at h

end PoincareMT.M76.Smoothing

end

namespace OMA.SecantAdapter

open Geometry Set

theorem star_secant_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : SimplicialComplex ℝ E) [DecidableEq E] (hfin : K.faces.Finite) (s : Finset E)
    (P : Submodule ℝ E) [P.HasOrthogonalProjection] :
    let S := ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)
    (∃ c : ℝ, 0 < c ∧ ∀ x ∈ S, ∀ y ∈ S,
      c * ‖x - y‖ ≤ ‖(x - y) - P.starProjection (x - y)‖) ↔
      (∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y) := by
  dsimp only
  constructor
  · rintro ⟨c, hc, h⟩ x hx y hy hxy
    have hb := h x hx y hy
    rw [Submodule.starProjection_eq_self_iff.mpr hxy, sub_self, norm_zero] at hb
    have hn : ‖x - y‖ = 0 := le_antisymm
      (nonpos_of_mul_nonpos_right hb hc) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · intro h
    let Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P.starProjection
    have hQ : InjOn Q (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
        convexHull ℝ (t : Set E)) := by
      intro x hx y hy hxy
      have hz : Q (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      change (x - y) - P.starProjection (x - y) = 0 at hz
      exact h x hx y hy (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm)
    obtain ⟨L, hL⟩ := Fleet.StarLinear.norm_sub_le_mul_of_injOn_star K hfin (s := s) Q hQ
    have hpos : 0 < (L : ℝ) + 1 := by positivity
    refine ⟨((L : ℝ) + 1)⁻¹, inv_pos.mpr hpos, ?_⟩
    intro x hx y hy
    change ((L : ℝ) + 1)⁻¹ * ‖x - y‖ ≤ ‖Q (x - y)‖
    rw [map_sub Q]
    rw [← div_eq_inv_mul, div_le_iff₀ hpos]
    calc
      ‖x - y‖ ≤ (L : ℝ) * ‖Q x - Q y‖ := hL x hx y hy
      _ ≤ ‖Q x - Q y‖ * ((L : ℝ) + 1) := by
        rw [mul_comm (L : ℝ)]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)

end OMA.SecantAdapter

namespace OMA.PoincareFacePlanesPort

open Geometry Set

private theorem contractible_qualitative_planes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (hm : Module.finrank ℝ E = m) (S : Set E)
    (hsecant : ∀ P : Submodule ℝ E,
      P.IsSecantTransverse S ↔ ∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y)
    (h : ContractibleSpace (SecantTransversePlaneSpace 3 S)) :
    let G := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y}
    @ContractibleSpace G (TopologicalSpace.induced
      (fun P : G => P.val.starProjection) inferInstance) := by
  let G := {P : Submodule ℝ E //
    Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y}
  let _ : TopologicalSpace G := TopologicalSpace.induced
    (fun P : G => P.val.starProjection) inferInstance
  let _ : ContractibleSpace (SecantTransversePlaneSpace 3 S) := h
  let e : SecantTransversePlaneSpace 3 S ≃ₜ G :=
    { toFun := fun P => ⟨P.val.subspace, P.property.1.trans hm,
        (hsecant _).mp P.property.2⟩
      invFun := fun P => ⟨⟨P.val⟩, P.property.1.trans hm.symm,
        (hsecant _).mpr P.property.2⟩
      left_inv := by rintro ⟨⟨P⟩, hP⟩; rfl
      right_inv := by rintro ⟨P, hP⟩; rfl
      continuous_toFun := continuous_induced_rng.mpr
        ((EuclideanSubspace.continuous_projector E).comp continuous_subtype_val)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact EuclideanSubspace.continuous_iff_projector.mpr continuous_induced_dom }
  exact e.symm.contractibleSpace

theorem exact_face_planes :
    OMA.CairnsPlaneField.H1 := by
  classical
  intro m K
  dsimp only
  intro hind hfinite hbound hedges htriangles s hs hpositive
  let E := EuclideanSpace ℝ (Fin m)
  let _ : DecidableEq E := Classical.decEq E
  have hedges' : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space :=
    by simpa only [SimplicialComplex.space, SimplicialComplex.faceLink] using hedges
  have htriangles' : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2 :=
    by simpa only [SimplicialComplex.vertices, SimplicialComplex.faceLink] using htriangles
  have hcontractible := PoincareMT.M76.Smoothing.contractible_positiveFaceStarPlanes K
    hind hfinite hbound hedges' htriangles' hs hpositive
  have hdim : Module.finrank ℝ E = m := finrank_euclideanSpace_fin
  have h := contractible_qualitative_planes m hdim (K.closedFaceStar s).space
    (fun P => OMA.SecantAdapter.star_secant_iff K hfinite s P) hcontractible
  exact h

end OMA.PoincareFacePlanesPort

theorem OMA.CairnsAssembly.contract : OMA.CairnsPlaneField.H1 :=
  OMA.PoincareFacePlanesPort.exact_face_planes

end

/- ## Leaves -/
section
section

open Set

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

end ContinuousLinearMap

end

section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

end ContinuousLinearMap

end

section

open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem contDiffAt_kernelProjectionFormula (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) {n : ℕ∞ω} :
    ContDiffAt ℝ n (kernelProjectionFormula : (E →L[ℝ] F) → E →L[ℝ] E) Q := by
  have hadj : ContDiffAt ℝ n (adjoint : (E →L[ℝ] F) → F →L[ℝ] E) Q :=
    (adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E)).toContinuousLinearEquiv.contDiff.contDiffAt
  have hS : ContDiffAt ℝ n (fun R : E →L[ℝ] F => R.comp (adjoint R)) Q :=
    contDiffAt_id.clm_comp hadj
  have hi := (Q.isInvertible_self_comp_adjoint_of_surjective hQ).contDiffAt_map_inverse.comp Q hS
  exact contDiffAt_const.sub ((hadj.clm_comp hi).clm_comp contDiffAt_id)

theorem contDiffAt_frameProjectionFormula (J : F →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : Function.Injective (perpendicularFrame J P)) {n : ℕ∞ω} :
    ContDiffAt ℝ n (frameProjectionFormula J) P := by
  have hD : ContDiffAt ℝ n (fun R : E →L[ℝ] E => ContinuousLinearMap.id ℝ E - R) P :=
    contDiffAt_const.sub contDiffAt_id
  have hA : ContDiffAt ℝ n (perpendicularFrame J) P := hD.clm_comp contDiffAt_const
  have hAdj : ContDiffAt ℝ n (fun R => adjoint (perpendicularFrame J R)) P :=
    (adjoint : (F →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] F)).toContinuousLinearEquiv.contDiff.contDiffAt.comp P hA
  have hGram := (perpendicularFrame J P).isInvertible_adjoint_comp_self_of_injective hP
  have hi := hGram.contDiffAt_map_inverse.comp P (hAdj.clm_comp hA)
  exact (hi.clm_comp hAdj).clm_comp hD

end ContinuousLinearMap

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem ContDiffOn.ker_starProjection {Q : X → E →L[ℝ] F} {U : Set X} {n : ℕ∞ω}
    (hQ : ContDiffOn ℝ n Q U) (hsurj : ∀ x ∈ U, Function.Surjective (Q x)) :
    ContDiffOn ℝ n (fun x => (Q x).ker.starProjection) U := by
  have hreg : ContDiffOn ℝ n (fun x => (Q x).kernelProjectionFormula) U :=
    fun x hx => ((Q x).contDiffAt_kernelProjectionFormula (hsurj x hx)).comp_contDiffWithinAt
      x (hQ x hx)
  exact hreg.congr (fun x hx => (Q x).starProjection_ker_eq_formula (hsurj x hx))

end

section

namespace Module.Basis

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

end Module.Basis

end

section

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E} in

variable [FiniteDimensional ℝ E]

variable {E}

end Geometry

end

section

open Set Filter
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

structure IsSmoothLeafFieldOn (P : E → EuclideanSubspace E) (U : Set E) : Prop where

  contDiffOn_projector : ContDiffOn ℝ ∞ (fun x => (P x).subspace.starProjection) U

  eventually_eq : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (P x).subspace → P y = P x

theorem IsSmoothLeafFieldOn.const (P : EuclideanSubspace E) (U : Set E) :
    IsSmoothLeafFieldOn (fun _ => P) U :=
  ⟨contDiffOn_const, fun _ _ => Eventually.of_forall (fun _ _ => rfl)⟩

theorem IsSmoothLeafFieldOn.mono {P : E → EuclideanSubspace E} {U V : Set E}
    (hP : IsSmoothLeafFieldOn P U) (hVU : V ⊆ U) : IsSmoothLeafFieldOn P V :=
  ⟨hP.contDiffOn_projector.mono hVU, fun x hx => hP.eventually_eq x (hVU hx)⟩

theorem IsSmoothLeafFieldOn.continuousOn {P : E → EuclideanSubspace E} {U : Set E}
    (hP : IsSmoothLeafFieldOn P U) : ContinuousOn P U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_iff_projector.mpr hP.contDiffOn_projector.continuousOn.domRestrict

theorem IsSmoothLeafFieldOn.congr {P Q : E → EuclideanSubspace E} {U : Set E}
    (hP : IsSmoothLeafFieldOn P U) (hU : IsOpen U) (hQP : EqOn Q P U) :
    IsSmoothLeafFieldOn Q U := by
  refine ⟨hP.contDiffOn_projector.congr (fun x hx =>
    congrArg (fun R : EuclideanSubspace E => R.subspace.starProjection) (hQP hx)), ?_⟩
  intro x hx
  filter_upwards [hU.mem_nhds hx, hP.eventually_eq x hx] with y hy hconst hxy
  rw [hQP hy, hQP hx]
  apply hconst
  simpa only [hQP hx] using hxy

theorem IsSmoothLeafFieldOn.union {P : E → EuclideanSubspace E} {U V : Set E}
    (hPU : IsSmoothLeafFieldOn P U) (hPV : IsSmoothLeafFieldOn P V)
    (hU : IsOpen U) (hV : IsOpen V) : IsSmoothLeafFieldOn P (U ∪ V) := by
  refine ⟨hPU.contDiffOn_projector.union_of_isOpen hPV.contDiffOn_projector hU hV, ?_⟩
  rintro x (hx | hx)
  · exact hPU.eventually_eq x hx
  · exact hPV.eventually_eq x hx

theorem IsSmoothLeafFieldOn.of_operator {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {Q : E → E →L[ℝ] F} {U : Set E} (hQ : ContDiffOn ℝ ∞ Q U)
    (hsurj : ∀ x ∈ U, Function.Surjective (Q x))
    (hleaf : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (Q x).ker → Q y = Q x) :
    IsSmoothLeafFieldOn (fun x => ⟨(Q x).ker⟩) U := by
  refine ⟨hQ.ker_starProjection hsurj, ?_⟩
  intro x hx
  filter_upwards [hleaf x hx] with y hy hxy
  exact congrArg (fun R : E →L[ℝ] F => (⟨R.ker⟩ : EuclideanSubspace E)) (hy hxy)

end Geometry.EuclideanSubspace

end

section

open Set NormedSpace

section LinearExtension

variable {𝕜 E F ι : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] {v : ι → E}

end LinearExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end

section

open Set NormedSpace

namespace ConvexCone

section Algebra

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

end Algebra

end ConvexCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end

section

open Set
open scoped BigOperators

namespace Module.Basis

variable {ι E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [Finite ι]

end Module.Basis

end

section

open Set

namespace Module.Basis

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Module.Basis

end

section

open Set

namespace Module.Basis

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Module.Basis

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

variable {K L : SimplicialComplex ℝ E} {f g : E → F}

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}
  {f : E → F} {g : F → G}

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end ContinuousLinearMap

end

section

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {K : SimplicialComplex ℝ E} {f : E → F}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Geometry.SimplicialComplex

variable {K : SimplicialComplex ℝ E}

variable [DecidableEq E]

end Geometry.SimplicialComplex

end

section

open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

variable [FiniteDimensional ℝ E]

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E}

variable [DecidableEq E]

variable [FiniteDimensional ℝ E]

end Geometry.SimplicialComplex

end

section

open Set NormedSpace Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {A : AbstractSimplicialComplex ι} {v : ι → E}

end AbstractSimplicialComplex

end

section

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ι → E}

end AbstractSimplicialComplex

end

section

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

end Geometry.SimplicialComplex

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

end Geometry.SimplicialComplex

end

section

open Set NormedSpace
open scoped unitInterval

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

variable [DecidableEq E] [FiniteDimensional ℝ E] {f : E → E}

end Geometry.SimplicialComplex

end

section

open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

end AbstractSimplicialComplex

end

section

open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {A : AbstractSimplicialComplex ι} {s : Set ι} {w : ι → E}

end AbstractSimplicialComplex

end

section

open Set

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end AbstractSimplicialComplex

end

section

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {A : AbstractSimplicialComplex ι}

end AbstractSimplicialComplex

end

section

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

end AbstractSimplicialComplex

end

section

open Set

namespace Module.Basis

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Module.Basis

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {A : AbstractSimplicialComplex ι} {b : Module.Basis ι ℝ E}

end AbstractSimplicialComplex

end

section

open Set Geometry NormedSpace

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end AbstractSimplicialComplex

end

section

open Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

end

section

open Set

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

end Submodule

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Geometry.EuclideanSubspace

end

section

open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

end AbstractSimplicialComplex

end

section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

end ContinuousLinearMap

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

end AbstractSimplicialComplex

end

section

open Set Filter Geometry
open scoped Topology ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem frameProjectionFormula_spec (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (P : EuclideanSubspace E) (hP : IsCompl J.range P.subspace) :
    Function.RightInverse J (frameProjectionFormula J P.subspace.starProjection) ∧
      (frameProjectionFormula J P.subspace.starProjection).ker = P.subspace := by
  let Q := J.frameComplementPlaneHomeomorph hJ ⟨P, hP⟩
  have hker : Q.val.ker = P.subspace := J.ker_frameComplementPlaneHomeomorph hJ ⟨P, hP⟩
  have he : frameProjectionFormula J P.subspace.starProjection = Q.val := by
    simpa only [hker] using Q.val.frameProjectionFormula_ker J Q.property
  rw [he]
  exact ⟨Q.property, hker⟩

end ContinuousLinearMap

namespace Geometry.EuclideanSubspace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsSmoothLeafFieldOn.exists_frameRepresentation {P : E → EuclideanSubspace E}
    {U : Set E} (hP : IsSmoothLeafFieldOn P U) (J : F →L[ℝ] E)
    (hJ : Function.Injective J) (hcompl : ∀ x ∈ U, IsCompl J.range (P x).subspace) :
    ∃ Q : E → E →L[ℝ] F, ContDiffOn ℝ ∞ Q U ∧
      (∀ x ∈ U, Function.RightInverse J (Q x) ∧ (Q x).ker = (P x).subspace) ∧
      ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (Q x).ker → Q y = Q x := by
  let Q : E → E →L[ℝ] F := fun x =>
    ContinuousLinearMap.frameProjectionFormula J (P x).subspace.starProjection
  have hspec (x : E) (hx : x ∈ U) :
      Function.RightInverse J (Q x) ∧ (Q x).ker = (P x).subspace :=
    J.frameProjectionFormula_spec hJ (P x) (hcompl x hx)
  refine ⟨Q, ?_, hspec, ?_⟩
  · intro x hx
    have hi := (Q x).injective_perpendicularFrame_of_rightInverse J (hspec x hx).1
    have hi' : Function.Injective (ContinuousLinearMap.perpendicularFrame J
        (P x).subspace.starProjection) := by
      simpa only [(hspec x hx).2] using hi
    exact (J.contDiffAt_frameProjectionFormula _ hi').comp_contDiffWithinAt x
      (hP.contDiffOn_projector x hx)
  · intro x hx
    filter_upwards [hP.eventually_eq x hx] with y hy hxy
    rw [(hspec x hx).2] at hxy
    exact congrArg (fun R : EuclideanSubspace E =>
      ContinuousLinearMap.frameProjectionFormula J R.subspace.starProjection) (hy hxy)

end Geometry.EuclideanSubspace

end

section

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end AbstractSimplicialComplex

end

section

open Set Filter
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsSmoothLeafFieldOn.exists_transverse_frame_neighborhood
    {P : E → EuclideanSubspace E} {U S : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hSU : S ⊆ U) (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ F = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint J.range L)
    (htrans : ∀ x ∈ S, (P x).subspace.IsSecantTransverse A) :
    ∃ V : Set E, IsOpen V ∧ S ⊆ V ∧ V ⊆ U ∧
      ∃ Q : E → E →L[ℝ] F, ContDiffOn ℝ ∞ Q V ∧
        (∀ x ∈ V, Function.RightInverse J (Q x) ∧ (Q x).ker = (P x).subspace ∧
          (Q x).ker.IsSecantTransverse A) ∧
        ∀ x ∈ V, ∀ᶠ y in 𝓝 x, y - x ∈ (Q x).ker → Q y = Q x := by
  let V : Set E := U ∩ P ⁻¹' {L : EuclideanSubspace E | L.subspace.IsSecantTransverse A}
  have hV : IsOpen V := hP.continuousOn.isOpen_inter_preimage hU (isOpen_isSecantTransverse A)
  have hSV : S ⊆ V := fun x hx => ⟨hSU hx, htrans x hx⟩
  have hcompl (x : E) (hx : x ∈ V) : IsCompl J.range (P x).subspace := by
    apply (Submodule.isCompl_iff_disjoint J.range (P x).subspace ?_).mpr
    · exact hdisjoint _ hx.2
    · have hfd : Module.finrank ℝ J.range = Module.finrank ℝ F :=
        LinearMap.finrank_range_of_inj hJ
      have hxd := hdim x hx.1
      omega
  obtain ⟨Q, hQ, hspec, hleaf⟩ :=
    (hP.mono (show V ⊆ U from inter_subset_left)).exists_frameRepresentation J hJ hcompl
  refine ⟨V, hV, hSV, inter_subset_left, Q, hQ, ?_, hleaf⟩
  intro x hx
  refine ⟨(hspec x hx).1, (hspec x hx).2, ?_⟩
  rw [(hspec x hx).2]
  exact hx.2

end Geometry.EuclideanSubspace

end

section

open Set Metric unitInterval

namespace NormedSpace

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def unitSphereRadialMap : C(I × sphere (0 : E) 1, closedBall (0 : E) 1) := by
  refine ⟨fun z => ⟨(z.1 : ℝ) • (z.2 : E), ?_⟩, ?_⟩
  · rename_i z
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg z.1.property.1,
      norm_eq_of_mem_sphere z.2, mul_one]
    exact z.1.property.2
  · fun_prop

theorem norm_unitSphereRadialMap (z : I × sphere (0 : E) 1) :
    ‖(unitSphereRadialMap E z : E)‖ = (z.1 : ℝ) := by
  change ‖(z.1 : ℝ) • (z.2 : E)‖ = (z.1 : ℝ)
  rw [norm_smul, Real.norm_of_nonneg z.1.property.1, norm_eq_of_mem_sphere z.2, mul_one]

theorem unitSphereRadialMap_eq_iff (z w : I × sphere (0 : E) 1) :
    unitSphereRadialMap E z = unitSphereRadialMap E w ↔
      z.1 = w.1 ∧ (z.1 = 0 ∨ z.2 = w.2) := by
  constructor
  · intro h
    have ht : z.1 = w.1 := Subtype.ext (by
      simpa only [norm_unitSphereRadialMap] using
        congrArg (fun x : closedBall (0 : E) 1 => ‖(x : E)‖) h)
    refine ⟨ht, ?_⟩
    by_cases hz : z.1 = 0
    · exact Or.inl hz
    · apply Or.inr
      apply Subtype.ext
      have htz : (z.1 : ℝ) ≠ 0 := fun h => hz (Subtype.ext h)
      apply smul_right_injective E htz
      have hv := congrArg Subtype.val h
      change (z.1 : ℝ) • (z.2 : E) = (w.1 : ℝ) • (w.2 : E) at hv
      rwa [← ht] at hv
  · rintro ⟨ht, hz | hu⟩
    · apply Subtype.ext
      change (z.1 : ℝ) • (z.2 : E) = (w.1 : ℝ) • (w.2 : E)
      rw [← ht, hz]
      simp
    · exact congrArg (unitSphereRadialMap E) (Prod.ext ht hu)

variable [Nontrivial E]

theorem surjective_unitSphereRadialMap : Function.Surjective (unitSphereRadialMap E) := by
  intro x
  by_cases hx : (x : E) = 0
  · obtain ⟨u, hu⟩ := (sphere_nonempty (E := E) (x := 0) (r := 1)).mpr zero_le_one
    refine ⟨(0, ⟨u, hu⟩), Subtype.ext ?_⟩
    change (0 : ℝ) • u = (x : E)
    rw [zero_smul, hx]
  · have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let t : I := ⟨‖(x : E)‖, norm_nonneg _, by
      simpa only [mem_closedBall, dist_zero_right] using x.property⟩
    let u : sphere (0 : E) 1 := ⟨‖(x : E)‖⁻¹ • (x : E), by
      rw [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]⟩
    refine ⟨(t, u), Subtype.ext ?_⟩
    change ‖(x : E)‖ • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

variable [ProperSpace E]

theorem isQuotientMap_unitSphereRadialMap : Topology.IsQuotientMap (unitSphereRadialMap E) :=
  Topology.IsQuotientMap.of_surjective_continuous (surjective_unitSphereRadialMap E)
    (unitSphereRadialMap E).continuous

end NormedSpace

end

section

open Set Metric unitInterval NormedSpace

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace Y]

theorem Nullhomotopic.exists_closedBall_extension (f : C(sphere (0 : E) 1, Y))
    (hf : f.Nullhomotopic) :
    ∃ g : C(closedBall (0 : E) 1, Y),
      ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = f x := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    refine ⟨ContinuousMap.const _ y, ?_⟩
    intro x
    have hn := norm_eq_of_mem_sphere x
    rw [Subsingleton.elim (x : E) 0, norm_zero] at hn
    exact (zero_ne_one hn).elim
  · let := hE
    let q := unitSphereRadialMap E
    have hq : Topology.IsQuotientMap q := isQuotientMap_unitSphereRadialMap E
    have hfactor : Function.FactorsThrough H.symm.toContinuousMap q := by
      intro z w hzw
      obtain ⟨ht, hz | hu⟩ := (unitSphereRadialMap_eq_iff E z w).mp hzw
      · have hw : w.1 = 0 := ht.symm.trans hz
        change H.symm (z.1, z.2) = H.symm (w.1, w.2)
        rw [hz, hw, H.symm.apply_zero, H.symm.apply_zero]
        rfl
      · exact congrArg H.symm.toContinuousMap (Prod.ext ht hu)
    let g := hq.lift H.symm.toContinuousMap hfactor
    refine ⟨g, ?_⟩
    intro x
    have hqx : q (1, x) = ⟨x, sphere_subset_closedBall x.property⟩ :=
      Subtype.ext (one_smul ℝ (x : E))
    rw [← hqx]
    exact (congrArg (fun k : C(I × sphere (0 : E) 1, Y) => k (1, x))
      (hq.lift_comp H.symm.toContinuousMap hfactor)).trans (H.symm.apply_one x)

variable [ContractibleSpace Y]

theorem exists_closedBall_extension_of_contractible (f : C(sphere (0 : E) 1, Y)) :
    ∃ g : C(closedBall (0 : E) 1, Y),
      ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = f x := by
  have hf : f.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using (id_nullhomotopic Y).comp_left f
  exact hf.exists_closedBall_extension f

end ContinuousMap

end

section

open Set Metric

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace Y] [ContractibleSpace Y]

theorem exists_convexBody_extension_of_contractible {s : Set E}
    (hs : IsClosed s) (hc : Convex ℝ s) (hi : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) (f : C(frontier s, Y)) :
    ∃ g : C(s, Y), ∀ x : frontier s, g ⟨x, hs.frontier_subset x.property⟩ = f x := by
  obtain ⟨e, _, heclosure, hefrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hi hb
  have hes : e '' s = closedBall (0 : E) 1 := by
    simpa only [hs.closure_eq] using heclosure
  let a : frontier s ≃ₜ sphere (0 : E) 1 :=
    (e.image (frontier s)).trans (Homeomorph.setCongr hefrontier)
  let b : s ≃ₜ closedBall (0 : E) 1 :=
    (e.image s).trans (Homeomorph.setCongr hes)
  obtain ⟨g, hg⟩ := (f.comp ⟨a.symm, a.symm.continuous⟩).exists_closedBall_extension_of_contractible
  refine ⟨g.comp ⟨b, b.continuous⟩, ?_⟩
  intro x
  have hcomm : b ⟨x, hs.frontier_subset x.property⟩ =
      ⟨a x, sphere_subset_closedBall (a x).property⟩ := Subtype.ext rfl
  change g (b ⟨x, hs.frontier_subset x.property⟩) = f x
  rw [hcomm, hg]
  exact congrArg f (a.symm_apply_apply x)

end ContinuousMap

end

section

open unitInterval

namespace ContinuousMap

theorem contractibleSpace_of_target (B Y : Type*) [TopologicalSpace B]
    [LocallyCompactSpace B] [TopologicalSpace Y] [ContractibleSpace Y] :
    ContractibleSpace C(B, Y) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic Y
  apply (contractible_iff_id_nullhomotopic C(B, Y)).mpr
  refine ⟨ContinuousMap.const B y, ⟨{
    toFun := fun z => ⟨fun b => H (z.1, z.2 b),
      H.continuous.comp (continuous_const.prodMk z.2.continuous)⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · apply continuous_of_continuous_uncurry
    exact H.continuous.comp (continuous_fst.fst.prodMk
      (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)))
  · intro f
    ext b
    exact H.apply_zero (f b)
  · intro f
    ext b
    exact H.apply_one (f b)

end ContinuousMap

end

section

open Set

namespace ContinuousMap

variable {E B Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace B] [LocallyCompactSpace B] [TopologicalSpace Y] [ContractibleSpace Y]

theorem exists_convexBody_parametric_extension {C : Set E}
    (hC : IsClosed C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hb : Bornology.IsBounded C) (f : C(frontier C × B, Y)) :
    ∃ g : C(C × B, Y), ∀ x : frontier C, ∀ b : B,
      g (⟨x, hC.frontier_subset x.property⟩, b) = f (x, b) := by
  let : ContractibleSpace C(B, Y) := contractibleSpace_of_target B Y
  obtain ⟨g, hg⟩ := exists_convexBody_extension_of_contractible hC hc hi hb f.curry
  refine ⟨g.uncurry, ?_⟩
  intro x b
  exact congrArg (fun k : C(B, Y) => k b) (hg x)

end ContinuousMap

end

section

open Set Filter
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem IsCompact.exists_convex_innerCore {C U : Set E} (hC : IsCompact C)
    (hc : Convex ℝ C) (hi : (interior C).Nonempty) (hU : IsOpen U)
    (hfront : frontier C ⊆ U) :
    ∃ D : Set E, IsCompact D ∧ Convex ℝ D ∧ (interior D).Nonempty ∧
      D ⊆ interior C ∧ C \ interior D ⊆ U := by
  obtain ⟨p, hp⟩ := hi
  let K := C \ U
  have hK : IsCompact K := hC.diff hU
  have hKi : K ⊆ interior C := by
    intro x hx
    by_contra hxi
    exact hx.2 (hfront (by
      rw [frontier, hC.isClosed.closure_eq]
      exact ⟨hx.1, hxi⟩))
  have hnear : ∀ᶠ t : ℝ in 𝓝 1, ∀ x ∈ K, t⁻¹ • (x - p) + p ∈ interior C := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hcont : ContinuousAt (fun z : ℝ × E => z.1⁻¹ • (z.2 - p) + p) (1, x) :=
      ((continuousAt_fst.inv₀ one_ne_zero).smul
        (continuousAt_snd.sub continuousAt_const)).add continuousAt_const
    apply hcont.eventually_mem
    simpa only [inv_one, one_smul, sub_add_cancel] using
      isOpen_interior.mem_nhds (hKi hx)
  have hparam : ∀ᶠ t : ℝ in 𝓝[<] 1,
      0 < t ∧ t < 1 ∧ ∀ x ∈ K, t⁻¹ • (x - p) + p ∈ interior C := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hpos hlt
    exact ⟨hpos, hlt, ht⟩
  obtain ⟨t, ht0, ht1, htK⟩ := hparam.exists
  let D := AffineMap.homothety p t '' C
  have hopen := AffineMap.homothety_isOpenMap p t ht0.ne'
  have hDi : AffineMap.homothety p t '' interior C ⊆ interior D :=
    hopen.image_interior_subset C
  have hKD : K ⊆ interior D := by
    intro x hx
    apply hDi
    refine ⟨AffineMap.homothety p t⁻¹ x, htK x hx, ?_⟩
    exact (AffineEquiv.homothetyUnitsMulHom p (Units.mk0 t ht0.ne')).apply_symm_apply x
  refine ⟨D, hC.image (AffineMap.homothety_continuous p t),
    hc.affine_image _, ⟨AffineMap.homothety p t p, hDi ⟨p, hp, rfl⟩⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc.openSegment_interior_self_subset_interior hp hx
      (lineMap_mem_openSegment ℝ p x ⟨ht0, ht1⟩)
  · intro x hx
    by_contra hxu
    exact hx.2 (hKD ⟨hx.1, hxu⟩)

end

section

open Set Filter
open scoped Topology

namespace ContinuousMap

variable {E B Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace B] [LocallyCompactSpace B] [TopologicalSpace Z]

theorem exists_parametric_convexCore_replacement {D : Set E}
    (hD : IsCompact D) (hc : Convex ℝ D) (hi : (interior D).Nonempty)
    (f : C(E × B, Z)) (T : Set Z) [ContractibleSpace T]
    (hfront : ∀ x ∈ frontier D, ∀ b : B, f (x, b) ∈ T) :
    ∃ g : C(E × B, Z),
      (∀ x ∉ interior D, ∀ b : B, g (x, b) = f (x, b)) ∧
      ∀ x ∈ D, ∀ b : B, g (x, b) ∈ T := by
  classical
  let b : C(frontier D × B, T) :=
    ⟨fun z => ⟨f (z.1, z.2), hfront z.1 z.1.property z.2⟩,
      (f.continuous.comp (continuous_subtype_val.prodMap continuous_id)).subtype_mk _⟩
  obtain ⟨e, he⟩ := exists_convexBody_parametric_extension hD.isClosed hc hi hD.isBounded b
  let g : E × B → Z := fun z =>
    if hx : z.1 ∈ D then (e (⟨z.1, hx⟩, z.2) : Z) else f z
  have hfix : EqOn g f (Prod.fst ⁻¹' (interior D)ᶜ) := by
    intro z hz
    by_cases hzd : z.1 ∈ D
    · have hzf : z.1 ∈ frontier D := by
        rw [frontier, hD.isClosed.closure_eq]
        exact ⟨hzd, hz⟩
      change (if hx : z.1 ∈ D then (e (⟨z.1, hx⟩, z.2) : Z) else f z) = f z
      rw [dif_pos hzd]
      exact congrArg Subtype.val (he ⟨z.1, hzf⟩ z.2)
    · simp only [g, dif_neg hzd]
  have hcontD : ContinuousOn g (Prod.fst ⁻¹' D) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let k : (Prod.fst ⁻¹' D : Set (E × B)) → D × B :=
      fun z => (⟨z.1.1, z.2⟩, z.1.2)
    have hk : Continuous k :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
    convert (continuous_subtype_val.comp e.continuous).comp hk using 1
    ext z
    have hz : z.1.1 ∈ D := z.property
    simp only [domRestrict_apply, g, dif_pos hz]
    rfl
  have hcover : (Prod.fst ⁻¹' D : Set (E × B)) ∪
      Prod.fst ⁻¹' (interior D)ᶜ = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z.1 ∈ D
    · exact Or.inl hz
    · exact Or.inr (fun h => hz (interior_subset h))
  have hg : Continuous g := by
    have h := hcontD.union_of_isClosed (f.continuous.continuousOn.congr hfix)
      (hD.isClosed.preimage continuous_fst) (isOpen_interior.isClosed_compl.preimage
        continuous_fst)
    rw [hcover] at h
    exact continuousOn_univ.mp h
  refine ⟨⟨g, hg⟩, fun x hx b => hfix hx, ?_⟩
  intro x hx b
  change (if hy : x ∈ D then (e (⟨x, hy⟩, b) : Z) else f (x, b)) ∈ T
  rw [dif_pos hx]
  exact (e (⟨x, hx⟩, b)).property

theorem exists_parametric_convexCore_replacement_near_compl {C U : Set E}
    (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hU : IsOpen U) (hfront : frontier C ⊆ U)
    (f : C(E × B, Z)) (T : Set Z) [ContractibleSpace T]
    (hmem : ∀ x ∈ C ∩ U, ∀ b : B, f (x, b) ∈ T) :
    ∃ g : C(E × B, Z),
      (∀ᶠ x in 𝓝ˢ ((interior C)ᶜ), ∀ b : B, g (x, b) = f (x, b)) ∧
      ∀ x ∈ C, ∀ b : B, g (x, b) ∈ T := by
  obtain ⟨D, hD, hDc, hDi, hDC, hcollar⟩ := hC.exists_convex_innerCore hc hi hU hfront
  have hDf : frontier D ⊆ C ∩ U := by
    intro x hx
    have hxd : x ∈ D := hD.isClosed.frontier_subset hx
    have hxc : x ∈ C := interior_subset (hDC hxd)
    exact ⟨hxc, hcollar ⟨hxc, hx.2⟩⟩
  obtain ⟨g, hfix, hgm⟩ := f.exists_parametric_convexCore_replacement hD hDc hDi T
    (fun x hx => hmem x (hDf hx))
  refine ⟨g, ?_, ?_⟩
  · have hnear : Dᶜ ∈ 𝓝ˢ ((interior C)ᶜ) :=
      hD.isClosed.isOpen_compl.mem_nhdsSet.mpr (compl_subset_compl.mpr hDC)
    filter_upwards [hnear] with x hx b
    exact hfix x (fun hxi => hx (interior_subset hxi)) b
  · intro x hx b
    by_cases hxd : x ∈ D
    · exact hgm x hxd b
    · have hxi : x ∉ interior D := fun h => hxd (interior_subset h)
      rw [hfix x hxi b]
      exact hmem x ⟨hx, hcollar ⟨hx, hxi⟩⟩ b

end ContinuousMap

end

section

open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def frameNormalize (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F) : E →L[ℝ] F :=
  Q + (ContinuousLinearMap.id ℝ F - Q.comp J).comp Q0

theorem rightInverse_frameNormalize (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (Q : E →L[ℝ] F) :
    Function.RightInverse J (frameNormalize J Q0 Q) := by
  intro x
  change Q (J x) + (Q0 (J x) - Q (J (Q0 (J x)))) = x
  rw [h0 x]
  abel

theorem frameNormalize_eq_self (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F)
    (hQ : Function.RightInverse J Q) : frameNormalize J Q0 Q = Q := by
  ext x
  change Q x + (Q0 x - Q (J (Q0 x))) = Q x
  rw [hQ (Q0 x), sub_self, add_zero]

theorem contDiff_frameNormalize (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F) (n : ℕ∞ω) :
    ContDiff ℝ n (frameNormalize J Q0) :=
  contDiff_id.add ((contDiff_const.sub (contDiff_id.clm_comp contDiff_const)).clm_comp
    contDiff_const)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem isOpen_frameNormalize_transverse (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (S : Set E) :
    IsOpen {Q : E →L[ℝ] F | (frameNormalize J Q0 Q).ker.IsSecantTransverse S} := by
  let g : (E →L[ℝ] F) → {Q : E →L[ℝ] F // Function.Surjective Q} := fun Q =>
    ⟨frameNormalize J Q0 Q, (rightInverse_frameNormalize J Q0 h0 Q).surjective⟩
  have hg : Continuous g := (contDiff_frameNormalize J Q0 0).continuous.subtype_mk _
  have hc : Continuous (fun Q : E →L[ℝ] F =>
      (⟨(frameNormalize J Q0 Q).ker⟩ : Geometry.EuclideanSubspace E)) := by
    rw [Geometry.EuclideanSubspace.continuous_iff_projector]
    change Continuous (fun Q => (g Q).val.ker.starProjection)
    exact continuous_kernel_starProjection.comp hg
  exact (Geometry.EuclideanSubspace.isOpen_isSecantTransverse S).preimage hc

end ContinuousLinearMap

end

section

open Set ContinuousLinearMap

namespace ContinuousMap

variable {X E F : Type*} [TopologicalSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_frame_extension {s : Set X} (hs : IsClosed s)
    (f : C(s, E →L[ℝ] F)) (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (hf : ∀ x, Function.RightInverse J (f x)) :
    ∃ g : C(X, E →L[ℝ] F), (∀ x, Function.RightInverse J (g x)) ∧
      ∀ x : s, g x = f x := by
  obtain ⟨g, hg⟩ := f.exists_restrict_eq hs
  refine ⟨⟨fun x => frameNormalize J Q0 (g x),
    (contDiff_frameNormalize J Q0 0).continuous.comp g.continuous⟩,
    fun x => rightInverse_frameNormalize J Q0 h0 (g x), ?_⟩
  intro x
  have hx : g x = f x := congrArg (fun k : C(s, E →L[ℝ] F) => k x) hg
  change frameNormalize J Q0 (g x) = f x
  rw [hx, frameNormalize_eq_self J Q0 (f x) (hf x)]

end ContinuousMap

end

section

open Set Filter ContinuousLinearMap ContinuousMap
open scoped Topology ContDiff

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem Continuous.exists_frameTransverse_parametric_coreExtension
    {f : X × Y → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ z, Function.RightInverse J (f z))
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    {P : Set Y} (hP : IsCompact P) (A : Set E)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A}]
    (hfront : ∀ x ∈ frontier C, ∀ p ∈ P, (f (x, p)).ker.IsSecantTransverse A) :
    ∃ g : C(X × Y, E →L[ℝ] F), (∀ z, Function.RightInverse J (g z)) ∧
      (g : X × Y → E →L[ℝ] F) =ᶠ[𝓝ˢ ((interior C)ᶜ ×ˢ interior P)] f ∧
      ∀ z ∈ C ×ˢ P, (g z).ker.IsSecantTransverse A := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let T : Set (E →L[ℝ] F) :=
    {Q | Function.RightInverse J Q ∧ Q.ker.IsSecantTransverse A}
  let : ContractibleSpace T :=
    inferInstanceAs (ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A})
  let fP : C(X × P, E →L[ℝ] F) :=
    ⟨fun z => f (z.1, z.2), hf.comp (continuous_id.prodMap continuous_subtype_val)⟩
  let W : Set (E →L[ℝ] F) :=
    {Q | (frameNormalize J (f (0, 0)) Q).ker.IsSecantTransverse A}
  have hW : IsOpen W := isOpen_frameNormalize_transverse J (f (0, 0)) (hframe (0, 0)) A
  have hWeq (z : X × Y) : f z ∈ W ↔ (f z).ker.IsSecantTransverse A := by
    change (frameNormalize J (f (0, 0)) (f z)).ker.IsSecantTransverse A ↔ _
    rw [frameNormalize_eq_self J (f (0, 0)) (f z) (hframe z)]
  let U : Set X := fP.curry ⁻¹' {q : C(P, E →L[ℝ] F) | MapsTo q univ W}
  have hU : IsOpen U := (isOpen_setOfPred_mapsTo isCompact_univ hW).preimage fP.curry.continuous
  have hCU : frontier C ⊆ U := by
    intro x hx p _
    exact (hWeq (x, p)).mpr (hfront x hx p p.property)
  obtain ⟨g, heq, hgt⟩ := fP.exists_parametric_convexCore_replacement_near_compl
    hC hc hi hU hCU T (fun x hx p =>
      ⟨hframe (x, p), (hWeq (x, p)).mp (hx.2 (mem_univ p))⟩)
  have hgn (z : X × P) : Function.RightInverse J (g z) := by
    by_cases hx : z.1 ∈ C
    · exact (hgt z.1 hx z.2).1
    · rw [show g z = fP z from
        heq.self_of_nhdsSet z.1 (fun hxi => hx (interior_subset hxi)) z.2]
      exact hframe (z.1, z.2)
  let D : Set (X × Y) := univ ×ˢ P
  have hD : IsClosed D := isClosed_univ.prod hP.isClosed
  let k : D → X × P := fun z => (z.1.1, ⟨z.1.2, z.2.2⟩)
  have hk : Continuous k :=
    continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  let gD : C(D, E →L[ℝ] F) := g.comp ⟨k, hk⟩
  obtain ⟨G, hGn, hGeq⟩ := gD.exists_frame_extension hD J (f (0, 0)) (hframe (0, 0))
    (fun z => hgn (k z))
  have hGvalue (x : X) (p : P) : G (x, (p : Y)) = g (x, p) :=
    hGeq ⟨(x, (p : Y)), mem_univ x, p.property⟩
  obtain ⟨O, hO, hCO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp heq
  have hOS : O ×ˢ interior P ∈ 𝓝ˢ ((interior C)ᶜ ×ˢ interior P) :=
    (hO.prod isOpen_interior).mem_nhdsSet.mpr (prod_mono hCO Subset.rfl)
  refine ⟨G, hGn, ?_, ?_⟩
  · filter_upwards [hOS] with z hz
    rw [hGvalue z.1 ⟨z.2, interior_subset hz.2⟩]
    exact hOeq z.1 hz.1 ⟨z.2, interior_subset hz.2⟩
  · intro z hz
    rw [hGvalue z.1 ⟨z.2, hz.2⟩]
    exact (hgt z.1 hz.1 ⟨z.2, hz.2⟩).2

end

section

open Set
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Continuous.exists_contDiff_eqOn_mem_open {f : E → F} (hf : Continuous f)
    (n : ℕ∞) {C S U : Set E} (hC : IsCompact C) (hS : IsClosed S)
    (hU : U ∈ 𝓝ˢ S) (hfU : ContDiffOn ℝ n f U)
    {T : Set F} (hT : IsOpen T) (hmem : MapsTo f C T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ n g ∧ EqOn g f S ∧
      (∀ x, dist (g x) (f x) < ε) ∧ MapsTo g C T := by
  obtain ⟨δ, hδ, hthick⟩ := (hC.image hf).exists_thickening_subset_open hT
    (image_subset_iff.mpr hmem)
  obtain ⟨g, hg, happrox, heq, _⟩ := hf.exists_contDiff_approx_and_eqOn n
    (show Continuous (fun _ : E => min ε δ) from continuous_const)
    (fun _ => lt_min hε hδ) hS hU hfU
  refine ⟨g, hg, heq, fun x => (happrox x).trans_le (min_le_left ε δ), fun x hx => ?_⟩
  apply hthick
  exact Metric.mem_thickening_iff.mpr
    ⟨f x, mem_image_of_mem f hx, (happrox x).trans_le (min_le_right ε δ)⟩

end

section

open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem Continuous.exists_contDiff_frameTransverse_eqOn
    {f : X → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ x, Function.RightInverse J (f x)) (n : ℕ∞)
    {C S U : Set X} (hC : IsCompact C) (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContDiffOn ℝ n f U) (A : Set E)
    (htrans : ∀ x ∈ C, (f x).ker.IsSecantTransverse A) :
    ∃ g : X → E →L[ℝ] F, ContDiff ℝ n g ∧
      (∀ x, Function.RightInverse J (g x)) ∧ EqOn g f S ∧
      ∀ x ∈ C, (g x).ker.IsSecantTransverse A := by
  let Q0 := f 0
  let T : Set (E →L[ℝ] F) := {Q | (frameNormalize J Q0 Q).ker.IsSecantTransverse A}
  have hT : IsOpen T := isOpen_frameNormalize_transverse J Q0 (hframe 0) A
  have hmem : MapsTo f C T := by
    intro x hx
    change (frameNormalize J Q0 (f x)).ker.IsSecantTransverse A
    rw [frameNormalize_eq_self J Q0 (f x) (hframe x)]
    exact htrans x hx
  obtain ⟨g, hg, heq, _, hgt⟩ := hf.exists_contDiff_eqOn_mem_open n hC hS hU hfU hT hmem
    (ε := 1) zero_lt_one
  refine ⟨fun x => frameNormalize J Q0 (g x),
    (contDiff_frameNormalize J Q0 n).comp hg,
    fun x => rightInverse_frameNormalize J Q0 (hframe 0) (g x), ?_, hgt⟩
  intro x hx
  change frameNormalize J Q0 (g x) = f x
  rw [heq hx, frameNormalize_eq_self J Q0 (f x) (hframe x)]

end

section

open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem Continuous.exists_contDiff_frameTransverse_eventuallyEq
    {f : X → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ x, Function.RightInverse J (f x)) (n : ℕ∞)
    {C S U : Set X} (hC : IsCompact C) (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContDiffOn ℝ n f U) (A : Set E)
    (htrans : ∀ x ∈ C, (f x).ker.IsSecantTransverse A) :
    ∃ g : X → E →L[ℝ] F, ContDiff ℝ n g ∧
      (∀ x, Function.RightInverse J (g x)) ∧ g =ᶠ[𝓝ˢ S] f ∧
      ∀ x ∈ C, (g x).ker.IsSecantTransverse A := by
  obtain ⟨O, hO, hSO, hOU⟩ := mem_nhdsSet_iff_exists.mp hU
  obtain ⟨D, hDS, hD, hDO⟩ := exists_mem_nhdsSet_isClosed_subset
    (hO.mem_nhdsSet.mpr hSO) hS
  obtain ⟨g, hg, hgn, hgeq, hgt⟩ := hf.exists_contDiff_frameTransverse_eqOn J hframe n
    hC hD (hO.mem_nhdsSet.mpr hDO) (hfU.mono hOU) A htrans
  exact ⟨g, hg, hgn, Filter.mem_of_superset hDS (fun x hx => hgeq hx), hgt⟩

end

section

open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem Continuous.exists_contDiff_frameTransverse_parametric_coreExtension
    {f : X × Y → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ z, Function.RightInverse J (f z)) (n : ℕ∞)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    {P K : Set Y} (hP : IsCompact P) (hK : IsCompact K) (hKP : K ⊆ interior P)
    {S V : Set (X × Y)} (hS : IsClosed S) (hSC : S ⊆ (interior C)ᶜ ×ˢ K)
    (hV : V ∈ 𝓝ˢ S) (hfV : ContDiffOn ℝ n f V) (A : Set E)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A}]
    (hfront : ∀ x ∈ frontier C, ∀ p ∈ P, (f (x, p)).ker.IsSecantTransverse A) :
    ∃ g : X × Y → E →L[ℝ] F, ContDiff ℝ n g ∧
      (∀ z, Function.RightInverse J (g z)) ∧ g =ᶠ[𝓝ˢ S] f ∧
      ∀ z ∈ C ×ˢ K, (g z).ker.IsSecantTransverse A := by
  obtain ⟨g, hgn, heq, hgt⟩ := hf.exists_frameTransverse_parametric_coreExtension
    J hframe hC hc hi hP A hfront
  have heqS : (g : X × Y → E →L[ℝ] F) =ᶠ[𝓝ˢ S] f :=
    heq.filter_mono (nhdsSet_mono (hSC.trans (prod_mono Subset.rfl hKP)))
  obtain ⟨O, hO, hSO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp heqS
  have hVO : V ∩ O ∈ 𝓝ˢ S := Filter.inter_mem hV (hO.mem_nhdsSet.mpr hSO)
  have hgsmooth : ContDiffOn ℝ n (g : X × Y → E →L[ℝ] F) (V ∩ O) :=
    (hfV.mono inter_subset_left).congr (fun z hz => hOeq z hz.2)
  obtain ⟨k, hk, hkn, hkeq, hkt⟩ :=
    g.continuous.exists_contDiff_frameTransverse_eventuallyEq J hgn n
      (hC.prod hK) hS hVO hgsmooth A
      (fun z hz => hgt z ⟨hz.1, interior_subset (hKP hz.2)⟩)
  exact ⟨k, hk, hkn, hkeq.trans heqS, hkt⟩

end

section

open Set ContinuousLinearMap
open scoped Topology

variable {X E F : Type*} [TopologicalSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem ContinuousOn.exists_frame_extension_eventuallyEq
    {f : X → E →L[ℝ] F} {S V : Set X} (hf : ContinuousOn f V)
    (hS : IsClosed S) (hV : V ∈ 𝓝ˢ S) (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (hnorm : ∀ x ∈ V, Function.RightInverse J (f x)) :
    ∃ g : C(X, E →L[ℝ] F), (∀ x, Function.RightInverse J (g x)) ∧
      (g : X → E →L[ℝ] F) =ᶠ[𝓝ˢ S] f := by
  obtain ⟨O, hO, hSO, hOV⟩ := mem_nhdsSet_iff_exists.mp hV
  obtain ⟨D, hDS, hD, hDO⟩ := exists_mem_nhdsSet_isClosed_subset
    (hO.mem_nhdsSet.mpr hSO) hS
  let fD : C(D, E →L[ℝ] F) := ⟨fun x => f x, (hf.mono (hDO.trans hOV)).domRestrict⟩
  obtain ⟨g, hgn, hgeq⟩ := fD.exists_frame_extension hD J Q0 h0
    (fun x => hnorm x (hOV (hDO x.property)))
  refine ⟨g, hgn, ?_⟩
  filter_upwards [hDS] with x hx
  exact hgeq ⟨x, hx⟩

end

section

open Set
open scoped Topology ContDiff

namespace ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_openPartialHomeomorph_on {f : E → F} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hn : n ≠ 0) {U : Set E} (hU : IsOpen U)
    (hinj : InjOn f U) (hderiv : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ e.source = U ∧
      ContDiffOn ℝ n e.symm e.target := by
  have hopen : IsOpenMap (U.domRestrict f) := by
    rw [isOpenMap_iff_nhds_le]
    intro x
    obtain ⟨A, hA⟩ := hderiv x x.property
    have hd : HasFDerivAt f (A : E →L[ℝ] F) x := by
      rw [hA]
      exact (hf.differentiable hn).differentiableAt.hasFDerivAt
    have hs := hf.contDiffAt.hasStrictFDerivAt' hd hn
    change 𝓝 (f x) ≤ Filter.map (f ∘ Subtype.val) (𝓝 x)
    rw [← Filter.map_map, hU.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hs.map_nhds_eq_of_equiv]
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U)
    hf.continuous.continuousOn hopen hU
  refine ⟨e, rfl, rfl, ?_⟩
  intro y hy
  obtain ⟨B, hB⟩ := hderiv (e.symm y) (e.map_target hy)
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm (f₀' := B) hy
  · change HasFDerivAt f (B : E →L[ℝ] F) (e.symm y)
    rw [hB]
    exact (hf.differentiable hn).differentiableAt.hasFDerivAt
  · exact hf.contDiffAt

end ContDiff

end

section

open Set
open scoped ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def affineLeafMap (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F) (x0 : F)
    (z : F × (Q x0).ker) : E :=
  a z.1 + (z.2 : E) - a.contLinear (Q z.1 z.2)

theorem affineLeafMap_zero (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 x : F) : a.affineLeafMap Q x0 (x, 0) = a x := by
  simp [affineLeafMap]

theorem affineLeafMap_sub_mem_ker (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (hQ : ∀ x, Function.RightInverse a.contLinear (Q x))
    (z : F × (Q x0).ker) : a.affineLeafMap Q x0 z - a z.1 ∈ (Q z.1).ker := by
  change Q z.1 (a z.1 + (z.2 : E) - a.contLinear (Q z.1 z.2) - a z.1) = 0
  rw [map_sub, map_sub, map_add, hQ]
  abel

theorem contDiff_affineLeafMap (a : F →ᴬ[ℝ] E) {Q : F → E →L[ℝ] F}
    {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (x0 : F) :
    ContDiff ℝ n (a.affineLeafMap Q x0) := by
  have hz : ContDiff ℝ n (fun z : F × (Q x0).ker => (z.2 : E)) :=
    (Q x0).ker.subtypeL.contDiff.comp contDiff_snd
  exact ((a.contDiff.comp contDiff_fst).add hz).sub
    (a.contLinear.contDiff.comp ((hQ.comp contDiff_fst).clm_apply hz))

variable [CompleteSpace E] [CompleteSpace F]

end ContinuousAffineMap

end

section

open Set Filter
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem projKer_affineLeafMap_sub (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    (z : F × (Q x0).ker) :
    (Q x0).projKerOfRightInverse a.contLinear h0
      (a.affineLeafMap Q x0 z - a z.1) = z.2 := by
  have he : a.affineLeafMap Q x0 z - a z.1 =
      (z.2 : E) - a.contLinear (Q z.1 z.2) := by
    unfold affineLeafMap
    abel
  rw [he, map_sub, ContinuousLinearMap.projKerOfRightInverse_apply_idem,
    ContinuousLinearMap.projKerOfRightInverse_comp_inv, sub_zero]

theorem affineLeafMap_projKer (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    {x : F} (hx : Function.RightInverse a.contLinear (Q x)) {y : E}
    (hy : y - a x ∈ (Q x).ker) :
    a.affineLeafMap Q x0
      (x, (Q x0).projKerOfRightInverse a.contLinear h0 (y - a x)) = y := by
  change Q x (y - a x) = 0 at hy
  change a x + ((y - a x) - a.contLinear (Q x0 (y - a x))) -
    a.contLinear (Q x ((y - a x) - a.contLinear (Q x0 (y - a x)))) = y
  rw [(Q x).map_sub, hx, hy, zero_sub, map_neg]
  abel

theorem eventually_affineLeaf_base_eq (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (hQ : ∀ x, Function.RightInverse a.contLinear (Q x))
    (e : OpenPartialHomeomorph (F × (Q x0).ker) E)
    (he : (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0)
    {y : E} (hy : y ∈ e.target) :
    ∀ᶠ w in 𝓝 y, w - y ∈ (Q (e.symm y).1).ker →
      (e.symm w).1 = (e.symm y).1 := by
  let x := (e.symm y).1
  let k : E → F × (Q x0).ker := fun w =>
    (x, (Q x0).projKerOfRightInverse a.contLinear (hQ x0) (w - a x))
  have hk : Continuous k := continuous_const.prodMk
    (((Q x0).projKerOfRightInverse a.contLinear (hQ x0)).continuous.comp
      (continuous_id.sub continuous_const))
  have hey : a.affineLeafMap Q x0 (e.symm y) = y := by
    rw [← he]
    exact e.right_inv hy
  have hky : k y = e.symm y := by
    refine Prod.ext rfl ?_
    change (Q x0).projKerOfRightInverse a.contLinear (hQ x0)
      (y - a (e.symm y).1) = (e.symm y).2
    have h := a.projKer_affineLeafMap_sub Q x0 (hQ x0) (e.symm y)
    rwa [hey] at h
  have hnear : ∀ᶠ w in 𝓝 y, k w ∈ e.source :=
    hk.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (hky.symm ▸ e.map_target hy))
  have hyker : y - a x ∈ (Q x).ker := by
    simpa only [hey] using a.affineLeafMap_sub_mem_ker Q x0 hQ (e.symm y)
  filter_upwards [hnear] with w hw hwy
  have hwker : w - a x ∈ (Q x).ker := by
    convert (Q x).ker.add_mem hwy hyker using 1
    abel
  have hew : e (k w) = w := by
    rw [he]
    exact a.affineLeafMap_projKer Q x0 (hQ x0) (hQ x) hwker
  have hi := e.left_inv hw
  rw [hew] at hi
  simpa only [k] using congrArg Prod.fst hi

end ContinuousAffineMap

end

section

open Set
open scoped ContDiff NNReal

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem projKer_affineLeafMap_sub_zero (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    (z : F × (Q x0).ker) :
    (Q x0).projKerOfRightInverse a.contLinear h0 (a.affineLeafMap Q x0 z - a 0) = z.2 := by
  have ha : a z.1 - a 0 = a.contLinear z.1 := by
    simpa using (a.contLinear_map_vsub z.1 0).symm
  have he : a.affineLeafMap Q x0 z - a 0 =
      (a.affineLeafMap Q x0 z - a z.1) + a.contLinear z.1 := by
    rw [← ha]
    abel
  rw [he, map_add, a.projKer_affineLeafMap_sub Q x0 h0,
    ContinuousLinearMap.projKerOfRightInverse_comp_inv, add_zero]

theorem apply_affineLeafMap_sub_zero (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    (z : F × (Q x0).ker) :
    Q x0 (a.affineLeafMap Q x0 z - a 0) = z.1 - Q z.1 z.2 := by
  have ha : a z.1 - a 0 = a.contLinear z.1 := by
    simpa using (a.contLinear_map_vsub z.1 0).symm
  have he : a.affineLeafMap Q x0 z - a 0 =
      (a z.1 - a 0) + (z.2 : E) - a.contLinear (Q z.1 z.2) := by
    unfold affineLeafMap
    abel
  have hz : Q x0 (z.2 : E) = 0 := z.2.property
  rw [he, map_sub, map_add, ha, h0, h0, hz, add_zero]

theorem injOn_affineLeafMap_of_lipschitz (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    {C : Set F} {K : ℝ≥0} (hQ : LipschitzOnWith K Q C) :
    InjOn (a.affineLeafMap Q x0) (C ×ˢ {z : (Q x0).ker | (K : ℝ) * ‖z‖ < 1}) := by
  intro u hu v hv he
  have hz : u.2 = v.2 := by
    have h := congrArg (fun w => (Q x0).projKerOfRightInverse a.contLinear h0 (w - a 0)) he
    simpa only [a.projKer_affineLeafMap_sub_zero Q x0 h0] using h
  have hc := congrArg (fun w => Q x0 (w - a 0)) he
  rw [a.apply_affineLeafMap_sub_zero Q x0 h0,
    a.apply_affineLeafMap_sub_zero Q x0 h0, ← hz] at hc
  have hd : u.1 - v.1 = (Q u.1 - Q v.1) (u.2 : E) := by
    change u.1 - v.1 = Q u.1 (u.2 : E) - Q v.1 (u.2 : E)
    calc
      u.1 - v.1 = (Q u.1 (u.2 : E) + (u.1 - Q u.1 (u.2 : E))) - v.1 := by abel
      _ = (Q u.1 (u.2 : E) + (v.1 - Q v.1 (u.2 : E))) - v.1 := by rw [hc]
      _ = _ := by abel
  have hbound : ‖Q u.1 - Q v.1‖ ≤ (K : ℝ) * ‖u.1 - v.1‖ := by
    simpa only [dist_eq_norm] using hQ.dist_le_mul u.1 hu.1 v.1 hv.1
  have hop := (Q u.1 - Q v.1).le_opNorm (u.2 : E)
  have hmul := mul_le_mul_of_nonneg_right hbound (norm_nonneg (u.2 : E))
  have hsmall : (K : ℝ) * ‖(u.2 : E)‖ < 1 := hu.2
  have hzbase : ‖u.1 - v.1‖ = 0 := by
    rw [← hd] at hop
    nlinarith [norm_nonneg (u.1 - v.1)]
  exact Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hzbase)) hz

theorem exists_pos_injOn_affineLeafMap (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (h0 : Function.RightInverse a.contLinear (Q x0))
    {C : Set F} {K : ℝ≥0} (hQ : LipschitzOnWith K Q C) :
    ∃ ε : ℝ, 0 < ε ∧ InjOn (a.affineLeafMap Q x0)
      (C ×ˢ Metric.ball (0 : (Q x0).ker) ε) := by
  let ε : ℝ := ((K : ℝ) + 1)⁻¹
  have hden : 0 < (K : ℝ) + 1 := by positivity
  have hKε : (K : ℝ) * ε < 1 := by
    change (K : ℝ) * ((K : ℝ) + 1)⁻¹ < 1
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    linarith
  refine ⟨ε, inv_pos.mpr hden, (a.injOn_affineLeafMap_of_lipschitz Q x0 h0 hQ).mono ?_⟩
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  refine ⟨hx, lt_of_le_of_lt ?_ hKε⟩
  exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hz).le K.coe_nonneg

theorem exists_pos_injOn_affineLeafMap_of_compact (a : F →ᴬ[ℝ] E)
    (Q : F → E →L[ℝ] F) (x0 : F)
    (h0 : Function.RightInverse a.contLinear (Q x0)) {C : Set F}
    (hC : IsCompact C) (hc : Convex ℝ C) (hQ : ContDiffOn ℝ 1 Q C) :
    ∃ ε : ℝ, 0 < ε ∧ InjOn (a.affineLeafMap Q x0)
      (C ×ˢ Metric.ball (0 : (Q x0).ker) ε) := by
  obtain ⟨K, hK⟩ := hQ.exists_lipschitzOnWith one_ne_zero hc hC
  exact a.exists_pos_injOn_affineLeafMap Q x0 h0 hK

end ContinuousAffineMap

end

section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def affineLeafLinearEquiv (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (hQ : Function.RightInverse J Q) :
    (F × Q0.ker) ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse
    (J.coprod ((ContinuousLinearMap.id ℝ E - J.comp Q).comp Q0.ker.subtypeL))
    (Q.prod (Q0.projKerOfRightInverse J h0))
    (fun z => by
      apply Prod.ext
      · change Q (J z.1 + ((z.2 : E) - J (Q z.2))) = z.1
        rw [map_add, map_sub, hQ, hQ, sub_self, add_zero]
      · change Q0.projKerOfRightInverse J h0
          (J z.1 + ((z.2 : E) - J (Q z.2))) = z.2
        rw [map_add, map_sub, projKerOfRightInverse_comp_inv,
          projKerOfRightInverse_apply_idem, projKerOfRightInverse_comp_inv,
          sub_zero, zero_add])
    (fun y => by
      change J (Q y) + ((y - J (Q0 y)) - J (Q (y - J (Q0 y)))) = y
      rw [Q.map_sub, hQ, J.map_sub]
      abel)

end ContinuousLinearMap

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_affineLeafMap_zeroSection (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (x0 x : F) (hQ : DifferentiableAt ℝ Q x) :
    HasFDerivAt (a.affineLeafMap Q x0)
      (a.contLinear.coprod ((ContinuousLinearMap.id ℝ E - a.contLinear.comp (Q x)).comp
        (Q x0).ker.subtypeL)) (x, 0) := by
  let H := (Q x0).ker
  have hx : HasFDerivAt (fun z : F × H => a z.1)
      (a.contLinear.comp (ContinuousLinearMap.fst ℝ F H)) (x, 0) :=
    a.hasFDerivAt.comp (x, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hz : HasFDerivAt (fun z : F × H => (z.2 : E))
      (H.subtypeL.comp (ContinuousLinearMap.snd ℝ F H)) (x, 0) :=
    H.subtypeL.hasFDerivAt.comp (x, (0 : H))
      (ContinuousLinearMap.snd ℝ F H).hasFDerivAt
  have hq : HasFDerivAt (fun z : F × H => Q z.1)
      ((fderiv ℝ Q x).comp (ContinuousLinearMap.fst ℝ F H)) (x, 0) :=
    hQ.hasFDerivAt.comp (x, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hd := (hx.add hz).sub (a.contLinear.hasFDerivAt.comp (x, (0 : H)) (hq.clm_apply hz))
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro z
  simp [ContinuousLinearMap.coprod_apply]
  abel

theorem isInvertible_fderiv_affineLeafMap_zeroSection (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (x0 x : F) (hQ : DifferentiableAt ℝ Q x)
    (h0 : Function.RightInverse a.contLinear (Q x0))
    (hx : Function.RightInverse a.contLinear (Q x)) :
    (fderiv ℝ (a.affineLeafMap Q x0) (x, 0)).IsInvertible := by
  rw [(a.hasFDerivAt_affineLeafMap_zeroSection x0 x hQ).fderiv]
  exact ⟨a.contLinear.affineLeafLinearEquiv (Q x0) (Q x) h0 hx, rfl⟩

end ContinuousAffineMap

end

section

open Set
open scoped ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_smooth_affineLeaf_chart_of_compact (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (hQ : ContDiff ℝ ∞ Q)
    (hnorm : ∀ x, Function.RightInverse a.contLinear (Q x))
    (x0 : F) {C : Set F} (hC : IsCompact C) :
    ∃ e : OpenPartialHomeomorph (F × (Q x0).ker) E,
      (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0 ∧
      (∀ x ∈ C, (x, 0) ∈ e.source) ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨r, hCr⟩ := hC.isBounded.subset_ball (0 : F)
  obtain ⟨ε, hε, hinj⟩ := a.exists_pos_injOn_affineLeafMap_of_compact Q x0 (hnorm x0)
    (isCompact_closedBall (0 : F) r) (convex_closedBall (0 : F) r)
    ((hQ.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffOn)
  let f := a.affineLeafMap Q x0
  have hf : ContDiff ℝ ∞ f := a.contDiff_affineLeafMap hQ x0
  let V := {z : F × (Q x0).ker | (fderiv ℝ f z).IsInvertible}
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv (by simp))
  let U := (Metric.ball (0 : F) r ×ˢ Metric.ball (0 : (Q x0).ker) ε) ∩ V
  have hU : IsOpen U := (Metric.isOpen_ball.prod Metric.isOpen_ball).inter hV
  have hi : InjOn f U := by
    apply hinj.mono
    intro z hz
    exact ⟨Metric.ball_subset_closedBall hz.1.1, hz.1.2⟩
  obtain ⟨e, he, hes, hei⟩ := hf.exists_smooth_openPartialHomeomorph_on
    (by simp) hU hi (fun z hz => hz.2)
  refine ⟨e, he, ?_, hei⟩
  intro x hx
  rw [hes]
  refine ⟨⟨hCr hx, Metric.mem_ball_self hε⟩, ?_⟩
  exact a.isInvertible_fderiv_affineLeafMap_zeroSection x0 x
    (hQ.differentiable (by simp)).differentiableAt (hnorm x0) (hnorm x)

end ContinuousAffineMap

end

section

open Set Filter unitInterval
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ContinuousOn.eq_of_sub_mem_ker_of_convex {G : E → E →L[ℝ] F}
    {V : Set E} (hG : ContinuousOn G V) (hV : Convex ℝ V)
    (hleaf : ∀ z ∈ V, ∀ᶠ w in 𝓝 z, w - z ∈ (G z).ker → G w = G z)
    {x y : E} (hx : x ∈ V) (hy : y ∈ V) (hxy : y - x ∈ (G x).ker) :
    G y = G x := by
  let c : I → E := fun t => AffineMap.lineMap x y (t : ℝ)
  have hc : Continuous c := by
    simp only [c, AffineMap.lineMap_apply_module']
    fun_prop
  have hcV (t : I) : c t ∈ V := hV.lineMap_mem hx hy t.property
  have hcont : Continuous (fun t : I => G (c t)) := hG.comp_continuous hc hcV
  let S : Set I := {t | G (c t) = G x}
  have hclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hnear := hc.continuousAt.eventually (hleaf (c t) (hcV t))
    filter_upwards [hnear] with u hu
    change G (c u) = G x
    rw [hu, ht]
    rw [ht]
    have heq : c u - c t = ((u : ℝ) - (t : ℝ)) • (y - x) := by
      simp only [c, AffineMap.lineMap_apply_module', sub_smul]
      abel
    rw [heq]
    exact (G x).ker.smul_mem _ hxy
  have hnonempty : S.Nonempty := ⟨0, by simp [S, c]⟩
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  have h1 : (1 : I) ∈ S := hall.symm ▸ mem_univ _
  simpa [S, c] using h1

end

section

open Set Filter
open scoped Topology

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eventuallyEq_affineLeaf_extension (a : F →ᴬ[ℝ] E)
    (Q : F → E →L[ℝ] F) (x0 : F)
    (hnorm : ∀ x, Function.RightInverse a.contLinear (Q x))
    (e : OpenPartialHomeomorph (F × (Q x0).ker) E)
    (he : (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0)
    {x : F} (hsource : (x, 0) ∈ e.source) {G : E → E →L[ℝ] F} {V : Set E}
    (hV : V ∈ 𝓝 (a x)) (hG : ContinuousOn G V)
    (hleaf : ∀ z ∈ V, ∀ᶠ w in 𝓝 z, w - z ∈ (G z).ker → G w = G z)
    (hslice : (fun v => G (a v)) =ᶠ[𝓝 x] Q) :
    G =ᶠ[𝓝 (a x)] (fun y => Q (e.symm y).1) := by
  have hzero : e (x, 0) = a x := by rw [he, a.affineLeafMap_zero]
  have htarget : a x ∈ e.target := hzero ▸ e.map_source hsource
  have hinv : e.symm (a x) = (x, 0) := by
    rw [← hzero]
    exact e.left_inv hsource
  have hbase : Tendsto (fun y => (e.symm y).1) (𝓝 (a x)) (𝓝 x) := by
    simpa only [hinv] using (e.continuousAt_symm htarget).fst.tendsto
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hbaseball : ∀ᶠ y in 𝓝 (a x), a (e.symm y).1 ∈ Metric.ball (a x) r :=
    (a.continuous.continuousAt.tendsto.comp hbase)
      (Metric.ball_mem_nhds (a x) hr)
  filter_upwards [e.open_target.mem_nhds htarget, Metric.ball_mem_nhds (a x) hr,
    hbaseball, hbase.eventually hslice] with y hy hyball hbball hslice_y
  have hey : a.affineLeafMap Q x0 (e.symm y) = y := by
    rw [← he]
    exact e.right_inv hy
  have hker : y - a (e.symm y).1 ∈ (G (a (e.symm y).1)).ker := by
    rw [hslice_y]
    simpa only [hey] using a.affineLeafMap_sub_mem_ker Q x0 hnorm (e.symm y)
  exact ((hG.mono hball).eq_of_sub_mem_ker_of_convex
    (convex_ball (a x) r) (fun z hz => hleaf z (hball hz)) hbball hyball hker).trans
    hslice_y

end ContinuousAffineMap

end

section

open Set Filter
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_smooth_affineLeaf_extension_matching (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (hQ : ContDiff ℝ ∞ Q)
    (hnorm : ∀ x, Function.RightInverse a.contLinear (Q x))
    {C S : Set F} (hC : IsCompact C) (hSC : S ⊆ C)
    {W : Set (E →L[ℝ] F)} (hW : IsOpen W) (hQW : MapsTo Q C W)
    {G : E → E →L[ℝ] F} {V : Set E} (hV : V ∈ 𝓝ˢ (a '' S))
    (hG : ContinuousOn G V)
    (hleaf : ∀ z ∈ V, ∀ᶠ w in 𝓝 z, w - z ∈ (G z).ker → G w = G z)
    (hslice : ∀ x ∈ S, (fun v => G (a v)) =ᶠ[𝓝 x] Q) :
    ∃ U : Set E, IsOpen U ∧ a '' C ⊆ U ∧
      ∃ g : E → E →L[ℝ] F, ContDiffOn ℝ ∞ g U ∧
        (∀ x ∈ C, ∀ᶠ v in 𝓝 x, g (a v) = Q v) ∧
        (∀ y ∈ U, Function.RightInverse a.contLinear (g y) ∧ g y ∈ W) ∧
        (∀ y ∈ U, ∀ᶠ w in 𝓝 y, w - y ∈ (g y).ker → g w = g y) ∧
        G =ᶠ[𝓝ˢ (a '' S)] g := by
  obtain ⟨e, he, hzero, hi⟩ := a.exists_smooth_affineLeaf_chart_of_compact hQ hnorm 0 hC
  let g : E → E →L[ℝ] F := fun y => Q (e.symm y).1
  have hg : ContDiffOn ℝ ∞ g e.target := hQ.comp_contDiffOn hi.fst
  have he0 (x : F) : e (x, 0) = a x := by rw [he, a.affineLeafMap_zero]
  have hbase (x : F) (hx : x ∈ C) : ∀ᶠ v in 𝓝 x, g (a v) = Q v := by
    have hn : ∀ᶠ v in 𝓝 x, (v, (0 : (Q 0).ker)) ∈ e.source :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds (hzero x hx))
    filter_upwards [hn] with v hv
    have h := e.left_inv hv
    rw [he0] at h
    change Q (e.symm (a v)).1 = Q v
    rw [h]
  let U := e.target ∩ g ⁻¹' W
  have hU : IsOpen U := hg.continuousOn.isOpen_inter_preimage e.open_target hW
  refine ⟨U, hU, ?_, g, hg.mono inter_subset_left, hbase, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← he0]
      exact e.map_source (hzero x hx)
    · change g (a x) ∈ W
      rw [(hbase x hx).self_of_nhds]
      exact hQW hx
  · exact fun y hy => ⟨hnorm (e.symm y).1, hy.2⟩
  · intro y hy
    filter_upwards [a.eventually_affineLeaf_base_eq Q 0 hnorm e he hy.1] with w hw hwy
    exact congrArg Q (hw hwy)
  · apply eventually_nhdsSet_iff_forall.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact a.eventuallyEq_affineLeaf_extension Q 0 hnorm e he (hzero x (hSC hx))
      (mem_nhdsSet_iff_forall.mp hV (a x) ⟨x, hx, rfl⟩) hG hleaf (hslice x hx)

end ContinuousAffineMap

end

section

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_smooth_parametric_leafAttachment (a : F →ᴬ[ℝ] E)
    (b : (X × Y) ≃L[ℝ] F) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse a.contLinear Q0)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    {P K : Set Y} (hP : IsCompact P) (hK : IsCompact K) (hKP : K ⊆ interior P)
    {G : E → E →L[ℝ] F} {V : Set E} (hV : IsOpen V) (hG : ContDiffOn ℝ ∞ G V)
    (hnorm : ∀ y ∈ V, Function.RightInverse a.contLinear (G y))
    (hleaf : ∀ y ∈ V, ∀ᶠ w in 𝓝 y, w - y ∈ (G y).ker → G w = G y)
    (hboundary : (a ∘ b) '' (frontier C ×ˢ P) ⊆ V) (A : Set E)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ z ∈ frontier C ×ˢ P, (G (a (b z))).ker.IsSecantTransverse A) :
    ∃ U : Set E, IsOpen U ∧ (a ∘ b) '' (C ×ˢ K) ⊆ U ∧
      ∃ g : E → E →L[ℝ] F, ContDiffOn ℝ ∞ g U ∧
        (∀ y ∈ U, Function.RightInverse a.contLinear (g y) ∧ (g y).ker.IsSecantTransverse A) ∧
        (∀ y ∈ U, ∀ᶠ w in 𝓝 y, w - y ∈ (g y).ker → g w = g y) ∧
        G =ᶠ[𝓝ˢ ((a ∘ b) '' (frontier C ×ˢ K))] g := by
  let H : X × Y → E →L[ℝ] F := fun z => G (a (b z))
  let D : Set (X × Y) := frontier C ×ˢ P
  let S : Set (X × Y) := frontier C ×ˢ K
  let T : Set (X × Y) := (a ∘ b) ⁻¹' V
  have hKP' : K ⊆ P := hKP.trans interior_subset
  have hSD : S ⊆ D := prod_mono Subset.rfl hKP'
  have hS : IsClosed S := isClosed_frontier.prod hK.isClosed
  have hD : IsClosed D := isClosed_frontier.prod hP.isClosed
  have hab : ContDiff ℝ ∞ (a ∘ b) := a.contDiff.comp b.contDiff
  have hT : IsOpen T := hV.preimage hab.continuous
  have hDT : D ⊆ T := fun z hz => hboundary ⟨z, hz, rfl⟩
  have hH : ContDiffOn ℝ ∞ H T := hG.comp hab.contDiffOn (fun _ hz => hz)
  obtain ⟨f, hfn, hfH⟩ := hH.continuousOn.exists_frame_extension_eventuallyEq hD
    (hT.mem_nhdsSet.mpr hDT) a.contLinear Q0 h0 (fun z hz => hnorm _ hz)
  have hfHS : (f : X × Y → E →L[ℝ] F) =ᶠ[𝓝ˢ S] H :=
    hfH.filter_mono (nhdsSet_mono hSD)
  obtain ⟨O, hO, hSO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp hfHS
  have hTO : T ∩ O ∈ 𝓝ˢ S :=
    Filter.inter_mem (hT.mem_nhdsSet.mpr (hSD.trans hDT)) (hO.mem_nhdsSet.mpr hSO)
  have hfsmooth : ContDiffOn ℝ ∞ (f : X × Y → E →L[ℝ] F) (T ∩ O) :=
    (hH.mono inter_subset_left).congr (fun z hz => hOeq z hz.2)
  have hftrans : ∀ x ∈ frontier C, ∀ p ∈ P, (f (x, p)).ker.IsSecantTransverse A := by
    intro x hx p hp
    rw [hfH.self_of_nhdsSet ⟨hx, hp⟩]
    exact htrans (x, p) ⟨hx, hp⟩
  obtain ⟨k, hk, hkn, hkeq, hkt⟩ :=
    f.continuous.exists_contDiff_frameTransverse_parametric_coreExtension a.contLinear hfn (⊤ : ℕ∞)
      hC hc hi hP hK hKP hS (fun z hz => ⟨hz.1.2, hz.2⟩) hTO hfsmooth A hftrans
  have hkH : k =ᶠ[𝓝ˢ S] H := hkeq.trans hfHS
  let Q : F → E →L[ℝ] F := fun v => k (b.symm v)
  have hQ : ContDiff ℝ ∞ Q := hk.comp b.symm.contDiff
  have hQn (v : F) : Function.RightInverse a.contLinear (Q v) := hkn (b.symm v)
  let C' := b '' (C ×ˢ K)
  let S' := b '' S
  have hC' : IsCompact C' := (hC.prod hK).image b.continuous
  have hS'C' : S' ⊆ C' := image_mono (prod_mono hC.isClosed.frontier_subset Subset.rfl)
  have hV' : V ∈ 𝓝ˢ (a '' S') := by
    apply hV.mem_nhdsSet.mpr
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hboundary ⟨z, hSD hz, rfl⟩
  have hslice : ∀ v ∈ S', (fun u => G (a u)) =ᶠ[𝓝 v] Q := by
    rintro _ ⟨z, hz, rfl⟩
    have hzEq : k =ᶠ[𝓝 z] H := eventually_nhdsSet_iff_forall.mp hkH z hz
    have hbeq : Tendsto b.symm (𝓝 (b z)) (𝓝 z) := by
      simpa only [b.symm_apply_apply] using
        (b.symm.continuous.continuousAt (x := b z)).tendsto
    filter_upwards [hbeq.eventually hzEq] with v hv
    simpa only [Q, H, b.apply_symm_apply] using hv.symm
  let W : Set (E →L[ℝ] F) :=
    {R | (frameNormalize a.contLinear Q0 R).ker.IsSecantTransverse A}
  have hW : IsOpen W := isOpen_frameNormalize_transverse a.contLinear Q0 h0 A
  have hQW : MapsTo Q C' W := by
    rintro _ ⟨z, hz, rfl⟩
    change (frameNormalize a.contLinear Q0 (Q (b z))).ker.IsSecantTransverse A
    rw [frameNormalize_eq_self a.contLinear Q0 _ (hQn (b z))]
    simpa only [Q, b.symm_apply_apply] using hkt z hz
  obtain ⟨U, hU, hCU, g, hg, _, hgm, hgl, hgeq⟩ :=
    a.exists_smooth_affineLeaf_extension_matching hQ hQn hC' hS'C' hW hQW hV'
      hG.continuousOn hleaf hslice
  refine ⟨U, hU, ?_, g, hg, ?_, hgl, ?_⟩
  · simpa only [C', image_image, Function.comp_def] using hCU
  · intro y hy
    obtain ⟨hgn, hgw⟩ := hgm y hy
    refine ⟨hgn, ?_⟩
    change (frameNormalize a.contLinear Q0 (g y)).ker.IsSecantTransverse A at hgw
    rwa [frameNormalize_eq_self a.contLinear Q0 (g y) hgn] at hgw
  · simpa only [S', S, image_image, Function.comp_def] using hgeq

end ContinuousAffineMap

end

section

open Set
open scoped Topology

variable {X Y Z : Type*} [TopologicalSpace X] [NormedAddCommGroup Y] [TopologicalSpace Z]

theorem Continuous.exists_pos_closedBall_thickening {f : X × Y → Z} (hf : Continuous f)
    {C : Set X} (hC : IsCompact C) {U : Set Z} (hU : IsOpen U)
    (hzero : ∀ x ∈ C, f (x, 0) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ MapsTo f (C ×ˢ Metric.closedBall (0 : Y) r) U := by
  have hz : C ×ˢ ({0} : Set Y) ⊆ f ⁻¹' U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [mem_singleton_iff] at hy
    change y = 0 at hy
    subst y
    exact hzero x hx
  obtain ⟨O, V, _, hV, hCO, h0V, hOV⟩ :=
    generalized_tube_lemma hC isCompact_singleton (hU.preimage hf) hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro z hz
  exact hOV ⟨hCO hz.1, hball (Metric.closedBall_subset_ball (half_lt_self hr) hz.2)⟩

end

section

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsSmoothLeafFieldOn.exists_coreAttachment
    {P : E → EuclideanSubspace E} {U : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (a : F →ᴬ[ℝ] E) (b : (X × Y) ≃L[ℝ] F)
    (hJ : Function.Injective a.contLinear)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hboundary : (fun x => a (b (x, 0))) '' frontier C ⊆ U)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ F = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint a.contLinear.range L)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ x ∈ frontier C, (P (a (b (x, 0)))).subspace.IsSecantTransverse A) :
    ∃ V : Set E, IsOpen V ∧ (fun x => a (b (x, 0))) '' C ⊆ V ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R V ∧
        (∀ y ∈ V, Module.finrank ℝ (R y).subspace + Module.finrank ℝ F =
          Module.finrank ℝ E ∧ (R y).subspace.IsSecantTransverse A) ∧
        P =ᶠ[𝓝ˢ ((fun x => a (b (x, 0))) '' frontier C)] R := by
  let c : X → E := fun x => a (b (x, 0))
  let S := c '' frontier C
  obtain ⟨V, hV, hSV, _, G, hG, hspec, hleaf⟩ :=
    hP.exists_transverse_frame_neighborhood hU hboundary a.contLinear hJ hdim A hdisjoint
      (by rintro _ ⟨x, hx, rfl⟩; exact htrans x hx)
  have hfront : IsCompact (frontier C) :=
    hC.of_isClosed_subset isClosed_frontier hC.isClosed.frontier_subset
  obtain ⟨r, hr, hthick⟩ :=
    (a.continuous.comp b.continuous).exists_pos_closedBall_thickening hfront hV
      (fun x hx => hSV ⟨x, hx, rfl⟩)
  have hsmall : ({0} : Set Y) ⊆ interior (Metric.closedBall (0 : Y) r) := by
    apply singleton_subset_iff.mpr
    exact mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds (0 : Y) hr)
  obtain ⟨Q0⟩ : Nonempty {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A} := inferInstance
  obtain ⟨W, hW, hCW, q, hq, hqn, hql, hGq⟩ :=
    a.exists_smooth_parametric_leafAttachment b Q0.val Q0.property.1 hC hc hi
      (isCompact_closedBall (0 : Y) r) isCompact_singleton hsmall hV hG
      (fun y hy => (hspec y hy).1) hleaf
      (by rintro _ ⟨z, hz, rfl⟩; exact hthick hz) A
      (fun z hz => (hspec _ (hthick hz)).2.2)
  let R : E → EuclideanSubspace E := fun y => ⟨(q y).ker⟩
  have hqsurj (y : E) (hy : y ∈ W) : Function.Surjective (q y) :=
    fun v => ⟨a.contLinear v, (hqn y hy).1 v⟩
  have hR : IsSmoothLeafFieldOn R W := IsSmoothLeafFieldOn.of_operator hq hqsurj hql
  have hSsub : S ⊆ (a ∘ b) '' (frontier C ×ˢ ({0} : Set Y)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(x, 0), ⟨hx, mem_singleton 0⟩, rfl⟩
  have hGqS : G =ᶠ[𝓝ˢ S] q := hGq.filter_mono (nhdsSet_mono hSsub)
  refine ⟨W, hW, ?_, R, hR, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hCW ⟨(x, 0), ⟨hx, mem_singleton 0⟩, rfl⟩
  · intro y hy
    refine ⟨?_, (hqn y hy).2⟩
    have hdimq := (q y).toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (hqsurj y hy), finrank_top] at hdimq
    change Module.finrank ℝ (q y).ker + Module.finrank ℝ F = Module.finrank ℝ E
    omega
  · filter_upwards [hGqS, hV.mem_nhdsSet.mpr hSV] with y hyq hyV
    apply EuclideanSubspace.ext
    change (P y).subspace = (q y).ker
    rw [← (hspec y hyV).2.1, hyq]

end Geometry.EuclideanSubspace

end

section

open Set

variable {X : Type*} [TopologicalSpace X]

theorem IsClosed.collar_inter_eq_frontier {C D : Set X} (hD : IsClosed D) (hDC : D ⊆ C) :
    (C \ interior D) ∩ D = frontier D := by
  rw [frontier, hD.closure_eq]
  ext x
  constructor
  · exact fun hx => ⟨hx.2, hx.1.2⟩
  · exact fun hx => ⟨⟨hDC hx.1, hx.2⟩, hx.1⟩

theorem collar_union_inner_eq {C D : Set X} (hDC : D ⊆ C) :
    (C \ interior D) ∪ D = C := by
  ext x
  constructor
  · exact fun hx => hx.elim And.left (fun h => hDC h)
  · intro hx
    by_cases hxd : x ∈ D
    · exact Or.inr hxd
    · exact Or.inl ⟨hx, fun hxi => hxd (interior_subset hxi)⟩

variable [AddCommGroup X] [Module ℝ X] [T2Space X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem IsCompact.exists_convex_core_decomposition {C U : Set X} (hC : IsCompact C)
    (hc : Convex ℝ C) (hi : (interior C).Nonempty) (hU : IsOpen U)
    (hfront : frontier C ⊆ U) :
    ∃ D : Set X, IsCompact D ∧ Convex ℝ D ∧ (interior D).Nonempty ∧
      D ⊆ interior C ∧ IsCompact (C \ interior D) ∧ C \ interior D ⊆ U ∧
      (C \ interior D) ∩ D = frontier D ∧ (C \ interior D) ∪ D = C := by
  obtain ⟨D, hD, hDc, hDi, hDC, hcollar⟩ := hC.exists_convex_innerCore hc hi hU hfront
  have hDC' : D ⊆ C := hDC.trans interior_subset
  exact ⟨D, hD, hDc, hDi, hDC, hC.diff isOpen_interior, hcollar,
    hD.isClosed.collar_inter_eq_frontier hDC', collar_union_inner_eq hDC'⟩

end

section

open Set

variable {X : Type*} [TopologicalSpace X] [NormalSpace X]

theorem IsClosed.exists_open_neighborhoods_inter_subset {A B U V W : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hU : IsOpen U) (hV : IsOpen V)
    (hW : IsOpen W) (hAU : A ⊆ U) (hBV : B ⊆ V) (hAB : A ∩ B ⊆ W) :
    ∃ U' V' : Set X, IsOpen U' ∧ IsOpen V' ∧ A ⊆ U' ∧ B ⊆ V' ∧
      U' ⊆ U ∧ V' ⊆ V ∧ U' ∩ V' ⊆ W := by
  have hd : Disjoint (A \ W) (B \ W) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hx.2 (hAB ⟨hx.1, hy.1⟩)
  obtain ⟨U0, V0, hU0, hV0, hAU0, hBV0, hdisj⟩ :=
    normal_separation (hA.inter hW.isClosed_compl) (hB.inter hW.isClosed_compl) hd
  refine ⟨U ∩ (W ∪ U0), V ∩ (W ∪ V0), hU.inter (hW.union hU0),
    hV.inter (hW.union hV0), ?_, ?_, inter_subset_left, inter_subset_left, ?_⟩
  · intro x hx
    refine ⟨hAU hx, ?_⟩
    by_cases hxw : x ∈ W
    · exact Or.inl hxw
    · exact Or.inr (hAU0 ⟨hx, hxw⟩)
  · intro x hx
    refine ⟨hBV hx, ?_⟩
    by_cases hxw : x ∈ W
    · exact Or.inl hxw
    · exact Or.inr (hBV0 ⟨hx, hxw⟩)
  · rintro x ⟨⟨_, hx | hx⟩, ⟨_, hy | hy⟩⟩
    · exact hx
    · exact hx
    · exact hy
    · exact (disjoint_left.mp hdisj hx hy).elim

end

section

open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsSmoothLeafFieldOn.exists_gluing {P Q : E → EuclideanSubspace E}
    {A B U V : Set E} (hP : IsSmoothLeafFieldOn P U) (hQ : IsSmoothLeafFieldOn Q V)
    (hU : IsOpen U) (hV : IsOpen V) (hA : IsClosed A) (hB : IsClosed B)
    (hAU : A ⊆ U) (hBV : B ⊆ V) (heq : P =ᶠ[𝓝ˢ (A ∩ B)] Q) :
    ∃ W : Set E, IsOpen W ∧ A ∪ B ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ x ∈ W, (x ∈ U ∧ R x = P x) ∨ (x ∈ V ∧ R x = Q x)) ∧
        R =ᶠ[𝓝ˢ A] P ∧ R =ᶠ[𝓝ˢ B] Q := by
  classical
  obtain ⟨O, hO, hABO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp heq
  obtain ⟨U', V', hU', hV', hAU', hBV', hU'U, hV'V, hUV'O⟩ :=
    hA.exists_open_neighborhoods_inter_subset hB hU hV hO hAU hBV hABO
  let R : E → EuclideanSubspace E := U'.piecewise P Q
  have hRP : EqOn R P U' := U'.piecewise_eqOn P Q
  have hRQ : EqOn R Q V' := by
    intro x hx
    by_cases hxu : x ∈ U'
    · exact (hRP hxu).trans (hOeq x (hUV'O ⟨hxu, hx⟩))
    · exact piecewise_eq_of_notMem U' P Q hxu
  refine ⟨U' ∪ V', hU'.union hV', union_subset_union hAU' hBV', R,
    ((hP.mono hU'U).congr hU' hRP).union ((hQ.mono hV'V).congr hV' hRQ) hU' hV',
    ?_, ?_, ?_⟩
  · rintro x (hx | hx)
    · exact Or.inl ⟨hU'U hx, hRP hx⟩
    · exact Or.inr ⟨hV'V hx, hRQ hx⟩
  · filter_upwards [hU'.mem_nhdsSet.mpr hAU'] with x hx
    exact hRP hx
  · filter_upwards [hV'.mem_nhdsSet.mpr hBV'] with x hx
    exact hRQ hx

end Geometry.EuclideanSubspace

end

section

open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem IsSmoothLeafFieldOn.exists_convexCellAttachment
    {P : E → EuclideanSubspace E} {U B : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hB : IsClosed B) (hBU : B ⊆ U)
    (a : F →ᴬ[ℝ] E) (b : (X × Y) ≃L[ℝ] F) (hJ : Function.Injective a.contLinear)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hboundary : (fun x => a (b (x, 0))) '' frontier C ⊆ U)
    (hBC : B ∩ (fun x => a (b (x, 0))) '' C ⊆
      (fun x => a (b (x, 0))) '' frontier C)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ F = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint a.contLinear.range L)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ x ∈ frontier C, (P (a (b (x, 0)))).subspace.IsSecantTransverse A) :
    ∃ W : Set E, IsOpen W ∧ B ∪ (fun x => a (b (x, 0))) '' C ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ y ∈ W, Module.finrank ℝ (R y).subspace + Module.finrank ℝ F = Module.finrank ℝ E) ∧
        R =ᶠ[𝓝ˢ B] P ∧
        ∀ x ∈ C, (R (a (b (x, 0)))).subspace.IsSecantTransverse A := by
  let c : X → E := fun x => a (b (x, 0))
  have hcc : Continuous c := a.continuous.comp
    (b.continuous.comp (continuous_id.prodMk continuous_const))
  have hci : Function.Injective c := by
    intro x y hxy
    exact congrArg Prod.fst (b.injective (a.toAffineMap.linear_injective_iff.mp hJ hxy))
  let V := U ∩ P ⁻¹' {L : EuclideanSubspace E | L.subspace.IsSecantTransverse A}
  have hV : IsOpen V := hP.continuousOn.isOpen_inter_preimage hU (isOpen_isSecantTransverse A)
  have hfrontC : frontier C ⊆ c ⁻¹' V := by
    intro x hx
    exact ⟨hboundary ⟨x, hx, rfl⟩, htrans x hx⟩
  obtain ⟨D, hD, hDc, hDi, hDC, hcollarCompact, hcollar, hinter, hcover⟩ :=
    hC.exists_convex_core_decomposition hc hi (hV.preimage hcc) hfrontC
  have hDC' : D ⊆ C := hDC.trans interior_subset
  have hfrontD : frontier D ⊆ C \ interior D := fun x hx =>
    ⟨hDC' (hD.isClosed.frontier_subset hx), hx.2⟩
  have hfrontDV : c '' frontier D ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcollar (hfrontD hx)
  obtain ⟨N, hN, hDN, Q, hQ, hQdim, hPQ⟩ :=
    (hP.mono (show V ⊆ U from inter_subset_left)).exists_coreAttachment hV a b hJ
      hD hDc hDi hfrontDV (fun x hx => hdim x hx.1) A hdisjoint
      (fun x hx => (hcollar (hfrontD hx)).2)
  let B' := B ∪ c '' (C \ interior D)
  have hB' : IsClosed B' := hB.union (hcollarCompact.image hcc).isClosed
  have hB'U : B' ⊆ U := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact hBU hy
    · exact (hcollar hx).1
  have hBD : Disjoint B (c '' D) := by
    apply disjoint_left.mpr
    rintro _ hyB ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hBC ⟨hyB, ⟨x, hDC' hx, rfl⟩⟩
    have he : z = x := hci hzx
    subst z
    exact hz.2 (hDC hx)
  have hBDinter : B' ∩ c '' D = c '' frontier D := by
    dsimp only [B']
    rw [union_inter_distrib_right, hBD.inter_eq, empty_union, ← image_inter hci, hinter]
  have hBcover : B' ∪ c '' D = B ∪ c '' C := by
    dsimp only [B']
    rw [union_assoc, ← image_union, hcover]
  have hPQ' : P =ᶠ[𝓝ˢ (B' ∩ c '' D)] Q := by
    rw [hBDinter]
    exact hPQ
  obtain ⟨W, hW, hBW, R, hR, hsource, hRP, hRQ⟩ :=
    hP.exists_gluing hQ hU hN hB' (hD.image hcc).isClosed hB'U hDN hPQ'
  refine ⟨W, hW, ?_, R, hR, ?_, ?_, ?_⟩
  · rwa [hBcover] at hBW
  · intro y hy
    rcases hsource y hy with ⟨hyU, hRy⟩ | ⟨hyN, hRy⟩
    · rw [hRy]
      exact hdim y hyU
    · rw [hRy]
      exact (hQdim y hyN).1
  · exact hRP.filter_mono (nhdsSet_mono (show B ⊆ B' from subset_union_left))
  · intro x hx
    by_cases hxD : x ∈ D
    · rw [hRQ.self_of_nhdsSet ⟨x, hxD, rfl⟩]
      exact (hQdim (c x) (hDN ⟨x, hxD, rfl⟩)).2
    · have hxcol : x ∈ C \ interior D := ⟨hx, fun hxi => hxD (interior_subset hxi)⟩
      rw [hRP.self_of_nhdsSet (show c x ∈ B' from Or.inr ⟨x, hxcol, rfl⟩)]
      exact (hcollar hxcol).2

end Geometry.EuclideanSubspace

end

section

open Set
open scoped Pointwise Topology

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

end

section

open Set
open scoped Pointwise Topology

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

end Algebraic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

end Geometry.SimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

end Submodule

end

section

open Set

namespace Geometry.SimplicialComplex

section General

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [DecidableEq E]

end Geometry.SimplicialComplex

end

section

open Set AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

end Algebraic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E]

end Geometry.SimplicialComplex

end

section

open Set

section Algebraic

variable {𝕜 ι E F : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

end Algebraic

section Orthogonal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Orthogonal

end

section

open Set AbstractSimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

end Geometry.SimplicialComplex

end

section

open Set
open scoped Pointwise

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

end

section

open Set

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Y] [ContractibleSpace Y]

end ContinuousMap

end

section

open Set

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def directionCoordinates (A : AffineSubspace ℝ E) (p : A) :
    A.direction →ᵃⁱ[ℝ] E := by
  let : Nonempty A := ⟨p⟩
  exact A.subtypeₐᵢ.comp (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry

theorem directionCoordinates_apply (A : AffineSubspace ℝ E) (p : A) (x : A.direction) :
    A.directionCoordinates p x = (x : E) + (p : E) := rfl

theorem range_directionCoordinates (A : AffineSubspace ℝ E) (p : A) :
    range (A.directionCoordinates p) = (A : Set E) := by
  let : Nonempty A := ⟨p⟩
  change range (Subtype.val ∘ (AffineIsometryEquiv.vaddConst ℝ p)) = _
  rw [range_comp, (AffineIsometryEquiv.vaddConst ℝ p).surjective.range_eq]
  simp

variable [FiniteDimensional ℝ E]

theorem convexBody_directionCoordinates {S : Set E} (hS : IsCompact S)
    (hc : Convex ℝ S) (p : affineSpan ℝ S) :
    let a := (affineSpan ℝ S).directionCoordinates p
    IsCompact (a ⁻¹' S) ∧ Convex ℝ (a ⁻¹' S) ∧ (interior (a ⁻¹' S)).Nonempty ∧
      a '' (a ⁻¹' S) = S ∧ a '' frontier (a ⁻¹' S) = intrinsicFrontier ℝ S := by
  let A := affineSpan ℝ S
  let : Nonempty A := ⟨p⟩
  let e := AffineIsometryEquiv.vaddConst ℝ p
  let a := A.directionCoordinates p
  have hrange : S ⊆ range a := by
    rw [range_directionCoordinates]
    exact subset_affineSpan ℝ S
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp h
    have hp : (p : E) ∈ (⊥ : AffineSubspace ℝ E) := by
      simpa only [he, span_empty] using p.property
    exact notMem_bot ℝ E (p : E) hp
  refine ⟨a.isometry.isEmbedding.isInducing.isCompact_preimage' hS hrange,
    hc.affine_preimage a.toAffineMap, ?_, image_preimage_eq_of_subset hrange, ?_⟩
  · obtain ⟨_, q, hq, rfl⟩ := Set.Nonempty.intrinsicInterior hc hne
    change (interior (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' S : Set A))).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    refine ⟨e.symm q, ?_⟩
    change e (e.symm q) ∈ interior (Subtype.val ⁻¹' S : Set A)
    rwa [e.apply_symm_apply]
  · change (Subtype.val ∘ e.toHomeomorph) ''
        frontier (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' S : Set A)) =
      Subtype.val '' frontier (Subtype.val ⁻¹' S : Set A)
    rw [← e.toHomeomorph.preimage_frontier]
    calc
      (Subtype.val ∘ e.toHomeomorph) ''
          (e.toHomeomorph ⁻¹' frontier (Subtype.val ⁻¹' S : Set A)) =
        Subtype.val '' (e.toHomeomorph ''
          (e.toHomeomorph ⁻¹' frontier (Subtype.val ⁻¹' S : Set A))) := by
            rw [image_image]
            rfl
      _ = _ := by rw [e.toHomeomorph.surjective.image_preimage]

end AffineSubspace

end

section

open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def nestedDirectionCoordinates (L T : Submodule ℝ E) (hLT : L ≤ T) :
    (L × ↥((L.comap T.subtype)ᗮ)) ≃L[ℝ] T :=
  (((comapSubtypeEquivOfLe hLT).symm.toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ ↥((L.comap T.subtype)ᗮ))).trans
      (ContinuousLinearEquiv.prodComm ℝ _ _)).trans
        (L.comap T.subtype).normalTangentEquiv.symm

theorem nestedDirectionCoordinates_apply_zero (L T : Submodule ℝ E) (hLT : L ≤ T)
    (x : L) : ((L.nestedDirectionCoordinates T hLT (x, 0) : T) : E) = x := by
  change ((0 : T) + ((comapSubtypeEquivOfLe hLT).symm x : T) : E) = x
  change (0 : E) + (x : E) = x
  exact zero_add _

noncomputable def affineSlice (T : Submodule ℝ E) (p : E) : T →ᴬ[ℝ] E :=
  ((AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.comp
    T.subtypeₗᵢ.toAffineIsometry).toContinuousAffineMap

omit [FiniteDimensional ℝ E] in

theorem affineSlice_apply (T : Submodule ℝ E) (p : E) (x : T) :
    T.affineSlice p x = (x : E) + p := rfl

omit [FiniteDimensional ℝ E] in

theorem affineSlice_contLinear (T : Submodule ℝ E) (p : E) :
    (T.affineSlice p).contLinear = T.subtypeL := by
  ext x
  rfl

theorem affineSlice_nestedDirectionCoordinates (A : AffineSubspace ℝ E)
    (T : Submodule ℝ E) (hAT : A.direction ≤ T) (p : A) (x : A.direction) :
    T.affineSlice p (A.direction.nestedDirectionCoordinates T hAT (x, 0)) =
      A.directionCoordinates p x := by
  rw [affineSlice_apply, nestedDirectionCoordinates_apply_zero,
    AffineSubspace.directionCoordinates_apply]

end Submodule

end

section

open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsSmoothLeafFieldOn.exists_intrinsicCellAttachment
    {P : E → EuclideanSubspace E} {U B S : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hB : IsClosed B) (hBU : B ⊆ U)
    (hS : IsCompact S) (hc : Convex ℝ S) (hne : S.Nonempty)
    (hboundary : intrinsicFrontier ℝ S ⊆ U)
    (hBS : B ∩ S ⊆ intrinsicFrontier ℝ S)
    (T : Submodule ℝ E) (hT : (affineSpan ℝ S).direction ≤ T)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ T = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint T L)
    [ContractibleSpace {Q : E →L[ℝ] T // Function.RightInverse T.subtypeL Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ x ∈ intrinsicFrontier ℝ S, (P x).subspace.IsSecantTransverse A) :
    ∃ W : Set E, IsOpen W ∧ B ∪ S ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ y ∈ W, Module.finrank ℝ (R y).subspace + Module.finrank ℝ T = Module.finrank ℝ E) ∧
        R =ᶠ[𝓝ˢ B] P ∧ ∀ x ∈ S, (R x).subspace.IsSecantTransverse A := by
  obtain ⟨p, hp⟩ := hne
  let pA : affineSpan ℝ S := ⟨p, subset_affineSpan ℝ S hp⟩
  let c := (affineSpan ℝ S).directionCoordinates pA
  let C := c ⁻¹' S
  obtain ⟨hC, hCc, hCi, himage, hfront⟩ :=
    AffineSubspace.convexBody_directionCoordinates hS hc pA
  let a := T.affineSlice p
  let b := (affineSpan ℝ S).direction.nestedDirectionCoordinates T hT
  have ha : a.contLinear = T.subtypeL := T.affineSlice_contLinear p
  have hzero : (fun x => a (b (x, 0))) = c := by
    funext x
    exact Submodule.affineSlice_nestedDirectionCoordinates (affineSpan ℝ S) T hT pA x
  let : ContractibleSpace {Q : E →L[ℝ] T // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A} := by rw [ha]; infer_instance
  have hJ : Function.Injective a.contLinear := by rw [ha]; exact Subtype.val_injective
  have hboundary' : (fun x => a (b (x, 0))) '' frontier C ⊆ U := by
    rw [hzero]
    exact hfront ▸ hboundary
  have hBS' : B ∩ (fun x => a (b (x, 0))) '' C ⊆
      (fun x => a (b (x, 0))) '' frontier C := by
    rw [hzero, himage, hfront]
    exact hBS
  obtain ⟨W, hW, hcover, R, hR, hRdim, hRP, hRT⟩ :=
    hP.exists_convexCellAttachment hU hB hBU a b hJ hC hCc hCi hboundary' hBS'
      hdim A (by
        rw [ha]
        change ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint T.subtype.range L
        simpa only [Submodule.range_subtype] using hdisjoint)
      (fun x hx => htrans _ (hfront ▸ (hzero ▸ mem_image_of_mem c hx)))
  refine ⟨W, hW, ?_, R, hR, hRdim, hRP, ?_⟩
  · rwa [hzero, himage] at hcover
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := himage ▸ hx
    change (R (c y)).subspace.IsSecantTransverse A
    rw [← congrFun hzero y]
    exact hRT y hy

end Geometry.EuclideanSubspace

end

section

open Set Geometry

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

noncomputable def frameTransversePlaneHomeomorph (J : F →L[ℝ] E)
    (hJ : Function.Injective J) (A : Set E) :
    J.range.TransverseComplementPlaneSpace A ≃ₜ
      {Q : E →L[ℝ] F // Function.RightInverse J Q ∧ Q.ker.IsSecantTransverse A} := by
  let e : {Q : J.FrameProjectionSpace // Q.val.ker.IsSecantTransverse A} ≃ₜ
      {Q : E →L[ℝ] F // Function.RightInverse J Q ∧ Q.ker.IsSecantTransverse A} := {
    toFun := fun Q => ⟨Q.val.val, Q.val.property, Q.property⟩
    invFun := fun Q => ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ |>.subtype_mk _ }
  refine ((J.frameComplementPlaneHomeomorph hJ).subtype ?_).trans e
  intro P
  rw [J.ker_frameComplementPlaneHomeomorph hJ]

theorem contractible_frameTransverseSpace_of_planes (J : F →L[ℝ] E)
    (hJ : Function.Injective J) (A : Set E)
    (hdisjoint : ∀ P : Submodule ℝ E, P.IsSecantTransverse A → Disjoint J.range P)
    [ContractibleSpace (SecantTransversePlaneSpace (Module.finrank ℝ F) A)] :
    ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A} := by
  have hdim : Module.finrank ℝ J.range = Module.finrank ℝ F :=
    LinearMap.finrank_range_of_inj hJ
  exact ((transverseComplementHomeomorph (Module.finrank ℝ F) A J.range hdim hdisjoint).trans
    (J.frameTransversePlaneHomeomorph hJ A)).symm.contractibleSpace

end ContinuousLinearMap

end

section

open Set

namespace Geometry.SimplicialComplex

section Combinatorial

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

end Combinatorial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Geometry.SimplicialComplex

end

section

open Set
open scoped Pointwise Topology

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

end

section

open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end Geometry.SimplicialComplex

end

section

open Set Filter Geometry
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem IsSmoothLeafFieldOn.exists_simplicialFaceAttachment
    {P : E → EuclideanSubspace E} {U B : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hB : IsClosed B) (hBU : B ⊆ U)
    (K : SimplicialComplex ℝ E) {s t : Finset E} (hs : s ∈ K.faces)
    (ht : t ∈ K.faces) (hst : s ⊆ t) (m : ℕ) (hcard : t.card = m + 1)
    (hboundary : intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ⊆ U)
    (hBS : B ∩ convexHull ℝ (s : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hdim : ∀ x ∈ U, Module.finrank ℝ (P x).subspace + m = Module.finrank ℝ E)
    [ContractibleSpace (SecantTransversePlaneSpace m (K.closedFaceStar s).space)]
    (htrans : ∀ x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)),
      (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space) :
    ∃ W : Set E, IsOpen W ∧ B ∪ convexHull ℝ (s : Set E) ⊆ W ∧
      ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
        (∀ y ∈ W, Module.finrank ℝ (R y).subspace + m = Module.finrank ℝ E) ∧
        R =ᶠ[𝓝ˢ B] P ∧ ∀ x ∈ convexHull ℝ (s : Set E),
          (R x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  let T := (affineSpan ℝ (t : Set E)).direction
  have hTdim : Module.finrank ℝ T = m := K.finrank_faceDirection_of_card ht hcard
  have htstar : t ∈ (K.closedFaceStar s).faces :=
    ⟨ht, by simpa only [Finset.union_eq_right.mpr hst] using ht⟩
  have hdisjoint : ∀ L : Submodule ℝ E,
      L.IsSecantTransverse (K.closedFaceStar s).space → Disjoint T L :=
    fun _ hL => (K.closedFaceStar s).disjoint_faceDirection_of_isSecantTransverse htstar hL
  let : ContractibleSpace
      (SecantTransversePlaneSpace (Module.finrank ℝ T) (K.closedFaceStar s).space) :=
    hTdim.symm ▸ inferInstance
  let := T.subtypeL.contractible_frameTransverseSpace_of_planes Subtype.val_injective
    (K.closedFaceStar s).space (by
      change ∀ L : Submodule ℝ E,
        L.IsSecantTransverse (K.closedFaceStar s).space → Disjoint T.subtype.range L
      simpa only [Submodule.range_subtype] using hdisjoint)
  have hT : (affineSpan ℝ (convexHull ℝ (s : Set E))).direction ≤ T := by
    rw [affineSpan_convexHull]
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hst)
  have h := hP.exists_intrinsicCellAttachment hU hB hBU (s.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
    hboundary hBS T hT (by simpa only [hTdim] using hdim)
    (K.closedFaceStar s).space hdisjoint htrans
  simpa only [hTdim] using h

end Geometry.EuclideanSubspace

end

section

open Set

namespace AffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem intrinsicFrontier_image_of_injOn (f : E →ᵃ[ℝ] F) (s : Set E)
    (hf : InjOn f (affineSpan ℝ s)) :
    intrinsicFrontier ℝ (f '' s) = f '' intrinsicFrontier ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let A := affineSpan ℝ s
  let B := affineSpan ℝ (f '' s)
  let : Nonempty A := ⟨⟨hs.choose, subset_affineSpan ℝ s hs.choose_spec⟩⟩
  let : Nonempty B := ⟨⟨f hs.choose,
    subset_affineSpan ℝ (f '' s) (mem_image_of_mem f hs.choose_spec)⟩⟩
  have hmap : A.map f = B := AffineSubspace.map_span f s
  let g : A →ᵃ[ℝ] B := f.restrict hmap.le
  have hginj : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (hf x.property y.property (congrArg Subtype.val hxy))
  let e : A ≃ᵃ[ℝ] B := AffineEquiv.ofBijective
    ⟨hginj, AffineMap.restrict.surjective f hmap⟩
  let h := e.toContinuousAffineEquiv.toHomeomorph
  have hpre : h '' (Subtype.val ⁻¹' s : Set A) =
      (Subtype.val ⁻¹' (f '' s) : Set B) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, subset_affineSpan ℝ s hx⟩, hx, ?_⟩
      exact Subtype.ext hxy
  change Subtype.val '' frontier (Subtype.val ⁻¹' (f '' s) : Set B) =
    f '' (Subtype.val '' frontier (Subtype.val ⁻¹' s : Set A))
  rw [← hpre, ← h.image_frontier, image_image, image_image]
  rfl

end AffineMap

end

section

open Set

variable (ι : Type*) [Fintype ι]

def stdSimplexCore (η : ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, η ≤ q i) ∧ ∑ i, q i = 1}

theorem isClosed_stdSimplexCore (η : ℝ) : IsClosed (stdSimplexCore ι η) := by
  have he : stdSimplexCore ι η =
      (⋂ i, {q : ι → ℝ | η ≤ q i}) ∩ {q | ∑ i, q i = 1} := by
    ext q
    simp [stdSimplexCore]
  rw [he]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)

variable [Nonempty ι]

namespace ContinuousMap

variable {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]

end ContinuousMap

end

section

open Set

namespace StdSimplexCore

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

variable {κ}

variable {ι}

variable (ι κ)

variable {ι κ}

end StdSimplexCore

end

section

namespace StdSimplexCore

variable {ι : Type*} [DecidableEq ι]

end StdSimplexCore

end

section

open Set
open scoped ContDiff

namespace StdSimplexCore

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

end StdSimplexCore

end

section

open Set

variable {ι : Type*} [Fintype ι]

theorem sum_eq_one_of_mem_affineSpan_stdSimplexCore {η : ℝ} {q : ι → ℝ}
    (hq : q ∈ affineSpan ℝ (stdSimplexCore ι η)) : ∑ i, q i = 1 := by
  refine affineSpan_induction hq (fun r hr => hr.2) (fun c u v w hu hv hw => ?_)
  simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    hu, hv, hw, sub_self, mul_zero, zero_add]

variable [Nonempty ι]

theorem mem_intrinsicInterior_stdSimplexCore_iff {η : ℝ}
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ} :
    q ∈ intrinsicInterior ℝ (stdSimplexCore ι η) ↔
      (∑ i, q i = 1) ∧ ∀ i, η < q i := by
  constructor
  · intro hq
    have hqc := intrinsicInterior_subset hq
    refine ⟨hqc.2, fun i => ?_⟩
    have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    let p : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
    have hpstrict : ∀ j, η < p j := by
      intro j
      change η < (Fintype.card ι : ℝ)⁻¹
      rw [inv_eq_one_div, lt_div_iff₀ hn]
      nlinarith [hbound]
    have hp : p ∈ stdSimplexCore ι η := ⟨fun j => (hpstrict j).le, by simp [p]⟩
    by_contra hnot
    have he : q i = η := le_antisymm (not_lt.mp hnot) (hqc.1 i)
    have hdir : q - p ∈ (affineSpan ℝ (stdSimplexCore ι η)).direction :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan _ _ hqc) (subset_affineSpan _ _ hp)
    obtain ⟨r, hr, hmem⟩ := Set.exists_pos_smul_add_mem_of_intrinsicInterior hq hdir
    have hlow := hmem.1 i
    change η ≤ r * (q i - p i) + q i at hlow
    rw [he] at hlow
    nlinarith [hpstrict i]
  · rintro ⟨hsum, hstrict⟩
    have hqc : q ∈ stdSimplexCore ι η := ⟨fun i => (hstrict i).le, hsum⟩
    let A := affineSpan ℝ (stdSimplexCore ι η)
    let qA : A := ⟨q, subset_affineSpan _ _ hqc⟩
    have hcont (i : ι) : Continuous (fun r : A => (r : ι → ℝ) i) :=
      (continuous_apply i).comp continuous_subtype_val
    have ho : IsOpen {r : A | ∀ i, η < (r : ι → ℝ) i} := by
      convert isOpen_iInter_of_finite (fun i : ι =>
        isOpen_lt (show Continuous (fun _ : A => η) from continuous_const) (hcont i)) using 1
      ext r
      simp
    refine mem_intrinsicInterior.mpr ⟨qA, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
    have hmem : qA ∈ {r : A | ∀ i, η < (r : ι → ℝ) i} := hstrict
    apply Filter.mem_of_superset (ho.mem_nhds hmem)
    intro r hr
    exact ⟨fun i => (hr i).le, sum_eq_one_of_mem_affineSpan_stdSimplexCore r.property⟩

theorem mem_intrinsicFrontier_stdSimplexCore_iff {η : ℝ}
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ} :
    q ∈ intrinsicFrontier ℝ (stdSimplexCore ι η) ↔
      q ∈ stdSimplexCore ι η ∧ ∃ i, q i = η := by
  rw [← closure_sdiff_intrinsicInterior (𝕜 := ℝ) (stdSimplexCore ι η),
    (isClosed_stdSimplexCore ι η).closure_eq]
  change (q ∈ stdSimplexCore ι η ∧ q ∉ intrinsicInterior ℝ (stdSimplexCore ι η)) ↔ _
  constructor
  · rintro ⟨hq, hn⟩
    have hnot : ¬∀ i, η < q i := fun hi =>
      hn ((mem_intrinsicInterior_stdSimplexCore_iff hbound).mpr ⟨hq.2, hi⟩)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact ⟨hq, i, le_antisymm (not_lt.mp hi) (hq.1 i)⟩
  · rintro ⟨hq, i, hi⟩
    refine ⟨hq, fun hn => ?_⟩
    have h := ((mem_intrinsicInterior_stdSimplexCore_iff hbound).mp hn).2 i
    simp only [hi, lt_self_iff_false] at h

end

section

open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]

variable [DecidableEq ι]

end StdSimplexCore

end

section

open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]

variable [DecidableEq ι]

end StdSimplexCore

end

section

open Set
open scoped ContDiff

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end StdSimplexCore

end

section

open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def faceInclusion (s : Finset ι) : (s → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => if hi : i ∈ s then
    ContinuousLinearMap.proj ⟨i, hi⟩ else 0)

omit [Fintype ι] in

theorem faceInclusion_apply_mem (s : Finset ι) (q : s → ℝ) {i : ι} (hi : i ∈ s) :
    faceInclusion s q i = q ⟨i, hi⟩ := by
  simp only [faceInclusion, ContinuousLinearMap.pi_apply, dif_pos hi,
    ContinuousLinearMap.proj_apply]

omit [Fintype ι] in

theorem faceInclusion_apply_notMem (s : Finset ι) (q : s → ℝ) {i : ι} (hi : i ∉ s) :
    faceInclusion s q i = 0 := by
  simp only [faceInclusion, ContinuousLinearMap.pi_apply, dif_neg hi,
    zero_apply]

theorem sum_faceInclusion (s : Finset ι) (q : s → ℝ) :
    ∑ i, faceInclusion s q i = ∑ i, q i := by
  have he : (∑ i, faceInclusion s q i) = ∑ i ∈ s, faceInclusion s q i := by
    symm
    apply Fintype.sum_subset
    intro i hi
    by_contra his
    exact hi (faceInclusion_apply_notMem s q his)
  rw [he, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl (fun i _ => faceInclusion_apply_mem s q i.property)

def barycentricFace (s : Finset ι) : Set (ι → ℝ) :=
  {q | q ∈ stdSimplex ℝ ι ∧ ∀ i ∉ s, q i = 0}

theorem faceInclusion_mem_barycentricFace (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    {q : s → ℝ} (hq : q ∈ stdSimplexCore s η) : faceInclusion s q ∈ barycentricFace s := by
  refine ⟨⟨fun i => ?_, (sum_faceInclusion s q).trans hq.2⟩,
    fun i hi => faceInclusion_apply_notMem s q hi⟩
  by_cases hi : i ∈ s
  · rw [faceInclusion_apply_mem s q hi]
    exact hη.trans (hq.1 ⟨i, hi⟩)
  · rw [faceInclusion_apply_notMem s q hi]

end StdSimplexCore

namespace PreAbstractSimplicialComplex

open StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end PreAbstractSimplicialComplex

end

section

open Set Geometry

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem barycentricFace_eq_image (s : Finset ι) :
    barycentricFace s = faceInclusion s '' stdSimplex ℝ s := by
  apply Subset.antisymm
  · intro q hq
    let r : s → ℝ := fun i => q i
    have he : faceInclusion s r = q := by
      ext i
      by_cases hi : i ∈ s
      · exact faceInclusion_apply_mem s r hi
      · rw [faceInclusion_apply_notMem s r hi, hq.2 i hi]
    refine ⟨r, ⟨fun i => hq.1.1 i, ?_⟩, he⟩
    rw [← sum_faceInclusion s r, he]
    exact hq.1.2
  · rintro _ ⟨q, hq, rfl⟩
    exact faceInclusion_mem_barycentricFace s (le_refl (0 : ℝ)) hq

omit [Fintype ι] in

theorem faceInclusion_single (s : Finset ι) (i : s) :
    faceInclusion s (Pi.single i 1) = Pi.single i.val 1 := by
  ext j
  by_cases hj : j ∈ s
  · rw [faceInclusion_apply_mem s _ hj]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · rw [faceInclusion_apply_notMem s _ hj]
    have hne : i.val ≠ j := fun he => hj (he ▸ i.property)
    simp [hne]

theorem barycentricFace_eq_convexHull (s : Finset ι) :
    barycentricFace s = convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (s : Set ι)) := by
  rw [barycentricFace_eq_image, ← convexHull_rangle_single_eq_stdSimplex ℝ s]
  change (faceInclusion s).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull, ← range_comp]
  congr 1
  ext q
  change (∃ i : s, faceInclusion s (Pi.single i 1) = q) ↔ ∃ i ∈ s, Pi.single i 1 = q
  simp only [faceInclusion_single, Subtype.exists, exists_prop]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def barycentricMap (v : ι → E) : (ι → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

omit [DecidableEq ι] in

theorem barycentricMap_apply (v : ι → E) (q : ι → ℝ) :
    barycentricMap v q = ∑ i, q i • v i := by
  simp only [barycentricMap, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

theorem barycentricMap_single (v : ι → E) (i : ι) : barycentricMap v (Pi.single i 1) = v i := by
  simp [barycentricMap_apply, Pi.single_apply, ite_smul]

omit [DecidableEq ι] in

theorem image_barycentricFace (v : ι → E) (s : Finset ι) :
    barycentricMap v '' barycentricFace s = convexHull ℝ (v '' (s : Set ι)) := by
  classical
  rw [barycentricFace_eq_convexHull]
  change (barycentricMap v).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull, image_image]
  change convexHull ℝ ((fun i => barycentricMap v (Pi.single i 1)) '' (s : Set ι)) = _
  simp only [barycentricMap_single]

end StdSimplexCore

namespace Geometry.SimplicialComplex

open StdSimplexCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Geometry.SimplicialComplex

end

section

open Set

namespace StdSimplexCore

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem injOn_barycentricMap_affineSpan (v : ι → E) (hv : AffineIndependent ℝ v) :
    InjOn (barycentricMap v) (affineSpan ℝ (stdSimplex ℝ ι)) := by
  intro q hq r hr he
  have hqsum := sum_eq_one_of_mem_affineSpan_stdSimplexCore (η := 0) hq
  have hrsum := sum_eq_one_of_mem_affineSpan_stdSimplexCore (η := 0) hr
  funext i
  exact hv.eq_of_sum_eq_sum (hqsum.trans hrsum.symm)
    (by simpa only [barycentricMap_apply] using he) i (Finset.mem_univ i)

variable [Nonempty ι]

omit [Fintype ι] in

theorem intrinsicFrontier_convexHull_range [Finite ι] (v : ι → E)
    (hv : AffineIndependent ℝ v) :
    intrinsicFrontier ℝ (convexHull ℝ (range v)) =
      ⋃ i : ι, convexHull ℝ (v '' {j | j ≠ i}) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have himage : barycentricMap v '' stdSimplex ℝ ι = convexHull ℝ (range v) := by
    simpa [barycentricFace] using image_barycentricFace v Finset.univ
  have hfront := (barycentricMap v).toLinearMap.toAffineMap.intrinsicFrontier_image_of_injOn
    (stdSimplex ℝ ι) (injOn_barycentricMap_affineSpan v hv)
  change intrinsicFrontier ℝ (barycentricMap v '' stdSimplex ℝ ι) =
    barycentricMap v '' intrinsicFrontier ℝ (stdSimplex ℝ ι) at hfront
  rw [himage] at hfront
  rw [hfront]
  have hbound : (Fintype.card ι : ℝ) * 0 < 1 := by simp
  have herase (i : ι) : ((Finset.univ.erase i : Finset ι) : Set ι) = {j | j ≠ i} := by
    ext j
    simp
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hqs, i, hi⟩ := (mem_intrinsicFrontier_stdSimplexCore_iff hbound).mp hq
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hqface : q ∈ barycentricFace (Finset.univ.erase i) := by
      refine ⟨hqs, fun j hj => ?_⟩
      have hji : j = i := by simpa using hj
      simpa only [hji] using hi
    have h := mem_image_of_mem (barycentricMap v) hqface
    rw [image_barycentricFace] at h
    simpa only [herase] using h
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hi' : x ∈ barycentricMap v '' barycentricFace (Finset.univ.erase i) := by
      rw [image_barycentricFace]
      simpa only [herase] using hi
    obtain ⟨q, hq, rfl⟩ := hi'
    refine ⟨q, (mem_intrinsicFrontier_stdSimplexCore_iff hbound).mpr ?_, rfl⟩
    exact ⟨hq.1, i, hq.2 i (Finset.notMem_erase i Finset.univ)⟩

end StdSimplexCore

namespace AffineIndependent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem mem_intrinsicFrontier_convexHull_finset {s : Finset E} (hs : s.Nonempty)
    (hv : AffineIndependent ℝ ((↑) : s → E)) (x : E) :
    x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ↔
      ∃ i ∈ s, x ∈ convexHull ℝ ((s.erase i : Finset E) : Set E) := by
  let : Nonempty s := hs.to_subtype
  have he (i : s) : ((↑) : s → E) '' {j | j ≠ i} = (s.erase i : Set E) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩
    · intro hy
      obtain ⟨hyi, hys⟩ := Finset.mem_erase.mp hy
      exact ⟨⟨y, hys⟩, fun h => hyi (congrArg Subtype.val h), rfl⟩
  have hfront := StdSimplexCore.intrinsicFrontier_convexHull_range ((↑) : s → E) hv
  have hrange : range ((↑) : s → E) = (s : Set E) := by ext; simp
  rw [hrange] at hfront
  simp only [he] at hfront
  rw [hfront, mem_iUnion]
  simp only [Subtype.exists, exists_prop]

omit [DecidableEq E] in

theorem convexHull_subset_intrinsicFrontier {s t : Finset E}
    (hv : AffineIndependent ℝ ((↑) : s → E)) (ht : t ⊂ s) :
    convexHull ℝ (t : Set E) ⊆ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨i, hi, hit⟩ := Finset.exists_of_ssubset ht
  intro x hx
  apply (mem_intrinsicFrontier_convexHull_finset ⟨i, hi⟩ hv x).mpr
  refine ⟨i, hi, convexHull_mono ?_ hx⟩
  intro y hy
  exact Finset.mem_erase.mpr ⟨fun h => hit (h ▸ hy), ht.subset hy⟩

end AffineIndependent

end

section

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_properFace_of_mem_intrinsicFrontier (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {x : E}
    (hx : x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E))) :
    ∃ t ∈ K.faces, t ⊂ s ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨i, hi, hxi⟩ :=
    (AffineIndependent.mem_intrinsicFrontier_convexHull_finset
      (K.nonempty_of_mem_faces hs) (K.indep hs) x).mp hx
  have hne : (s.erase i).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hxi
  exact ⟨s.erase i, K.down_closed hs (Finset.erase_subset i s) hne,
    Finset.erase_ssubset hi, hxi⟩

theorem inter_subset_intrinsicFrontier_of_card_le (K : SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hne : t ≠ s) (hcard : t.card ≤ s.card) :
    convexHull ℝ (t : Set E) ∩ convexHull ℝ (s : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  have hproper : t ∩ s ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro he
    have hst : s ⊆ t := he ▸ Finset.inter_subset_left
    exact hne (Finset.eq_of_subset_of_card_le hst hcard).symm
  intro x hx
  apply (K.indep hs).convexHull_subset_intrinsicFrontier hproper
  simpa only [Finset.coe_inter] using K.inter_subset_convexHull ht hs hx

end Geometry.SimplicialComplex

end

section

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

open EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_smoothLeafField_near_faces (K : SimplicialComplex ℝ E) (m : ℕ)
    (hfull : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = m + 1)
    (hvertices : ∀ s ∈ K.faces, s.card = 1 →
      Nonempty (SecantTransversePlaneSpace m (K.closedFaceStar s).space))
    (hpositive : ∀ s ∈ K.faces, 2 ≤ s.card →
      ContractibleSpace (SecantTransversePlaneSpace m (K.closedFaceStar s).space))
    (S : Finset (Finset E)) (hSK : ∀ s ∈ S, s ∈ K.faces)
    (hdown : ∀ s ∈ S, ∀ t ∈ K.faces, t ⊆ s → t ∈ S) :
    ∃ U : Set E, IsOpen U ∧ (⋃ s ∈ S, convexHull ℝ (s : Set E)) ⊆ U ∧
      ∃ P : E → EuclideanSubspace E, IsSmoothLeafFieldOn P U ∧
        (∀ x ∈ U, Module.finrank ℝ (P x).subspace + m = Module.finrank ℝ E) ∧
        ∀ s ∈ S, ∀ x ∈ convexHull ℝ (s : Set E),
          (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  classical
  revert hSK hdown
  induction S using Finset.induction_on_max_value (fun t : Finset E => t.card) with
  | empty =>
      intro _ _
      refine ⟨∅, isOpen_empty, by simp, fun _ => ⟨⊥⟩,
        IsSmoothLeafFieldOn.const ⟨⊥⟩ ∅, ?_, ?_⟩ <;> simp
  | insert s S hsnot hmax ih =>
      intro hSK hdown
      have hsK : s ∈ K.faces := hSK s (Finset.mem_insert_self s S)
      have hSK' : ∀ t ∈ S, t ∈ K.faces := fun t ht => hSK t (Finset.mem_insert_of_mem ht)
      have hdown' : ∀ t ∈ S, ∀ r ∈ K.faces, r ⊆ t → r ∈ S := by
        intro t ht r hr hrt
        rcases Finset.mem_insert.mp (hdown t (Finset.mem_insert_of_mem ht) r hr hrt) with he | hrS
        · subst r
          have hts : t = s := (Finset.eq_of_subset_of_card_le hrt (hmax t ht)).symm
          exact False.elim (hsnot (hts ▸ ht))
        · exact hrS
      obtain ⟨U, hU, hBU, P, hP, hdim, hPT⟩ := ih hSK' hdown'
      let B := ⋃ t ∈ S, convexHull ℝ (t : Set E)
      have hB : IsClosed B :=
        (S.finite_toSet.isCompact_biUnion
          (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
      have hproper : ∀ t ∈ K.faces, t ⊂ s → t ∈ S := by
        intro t ht hts
        exact Finset.mem_of_mem_insert_of_ne
          (hdown s (Finset.mem_insert_self s S) t ht hts.subset) hts.ne
      have hboundary : intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ⊆ U := by
        intro x hx
        obtain ⟨t, ht, hts, hxt⟩ := K.exists_properFace_of_mem_intrinsicFrontier hsK hx
        exact hBU (mem_iUnion₂.mpr ⟨t, hproper t ht hts, hxt⟩)
      have hBS : B ∩ convexHull ℝ (s : Set E) ⊆
          intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
        rintro x ⟨hxB, hxs⟩
        obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxB
        exact K.inter_subset_intrinsicFrontier_of_card_le hsK (hSK' t ht)
          (fun he => hsnot (he ▸ ht)) (hmax t ht) ⟨hxt, hxs⟩
      have hstep : ∃ W : Set E, IsOpen W ∧ B ∪ convexHull ℝ (s : Set E) ⊆ W ∧
          ∃ R : E → EuclideanSubspace E, IsSmoothLeafFieldOn R W ∧
            (∀ x ∈ W, Module.finrank ℝ (R x).subspace + m = Module.finrank ℝ E) ∧
            R =ᶠ[𝓝ˢ B] P ∧ ∀ x ∈ convexHull ℝ (s : Set E),
              (R x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
        by_cases hpos : 2 ≤ s.card
        · let := hpositive s hsK hpos
          obtain ⟨t, ht, hst, hcard⟩ := hfull s hsK
          apply hP.exists_simplicialFaceAttachment hU hB hBU K hsK ht hst m hcard
            hboundary hBS hdim
          intro x hx
          obtain ⟨r, hr, hrs, hxr⟩ := K.exists_properFace_of_mem_intrinsicFrontier hsK hx
          apply (hPT r (hproper r hr hrs) x hxr).mono
          intro y hy
          obtain ⟨q, hq, hyq⟩ := mem_space_iff.mp hy
          exact mem_space_iff.mpr ⟨q, K.closedFaceStar_antitone hrs.subset hq, hyq⟩
        · have hcard : s.card = 1 := by
            have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hsK)
            omega
          obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
          obtain ⟨Q⟩ := hvertices {v} hsK (by simp)
          have hinter : B ∩ {v} = ∅ := by
            apply subset_empty_iff.mp
            simpa only [Finset.coe_singleton, convexHull_singleton,
              intrinsicFrontier_singleton] using hBS
          have hPQ : P =ᶠ[𝓝ˢ (B ∩ {v})] (fun _ => Q.val) := by
            rw [hinter, nhdsSet_empty]
            exact Filter.eventually_bot
          obtain ⟨W, hW, hBW, R, hR, hsource, hRP, hRQ⟩ :=
            hP.exists_gluing (IsSmoothLeafFieldOn.const Q.val univ) hU isOpen_univ
              hB isClosed_singleton hBU (subset_univ _) hPQ
          simp only [Finset.coe_singleton, convexHull_singleton]
          refine ⟨W, hW, hBW, R, hR, ?_, hRP, ?_⟩
          · intro x hx
            rcases hsource x hx with ⟨hxU, hRx⟩ | ⟨_, hRx⟩
            · rw [hRx]
              exact hdim x hxU
            · rw [hRx]
              exact Q.property.1
          · intro x hx
            have hxv : x = v := hx
            subst x
            rw [hRQ.self_of_nhdsSet (mem_singleton v)]
            exact Q.property.2
      obtain ⟨W, hW, hcover, R, hR, hRdim, hRP, hRT⟩ := hstep
      refine ⟨W, hW, ?_, R, hR, hRdim, ?_⟩
      · intro x hx
        obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hcover (Or.inr hxt)
        · exact hcover (Or.inl (mem_iUnion₂.mpr ⟨t, ht, hxt⟩))
      · intro t ht x hx
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hRT x hx
        · rw [hRP.self_of_nhdsSet (show x ∈ B from mem_iUnion₂.mpr ⟨t, ht, hx⟩)]
          exact hPT t ht x hx

theorem exists_smoothLeafField_near_space (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (m : ℕ)
    (hfull : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = m + 1)
    (hvertices : ∀ s ∈ K.faces, s.card = 1 →
      Nonempty (SecantTransversePlaneSpace m (K.closedFaceStar s).space))
    (hpositive : ∀ s ∈ K.faces, 2 ≤ s.card →
      ContractibleSpace (SecantTransversePlaneSpace m (K.closedFaceStar s).space)) :
    ∃ U : Set E, IsOpen U ∧ K.space ⊆ U ∧
      ∃ P : E → EuclideanSubspace E, IsSmoothLeafFieldOn P U ∧
        (∀ x ∈ U, Module.finrank ℝ (P x).subspace + m = Module.finrank ℝ E) ∧
        ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
          (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
  classical
  have h := K.exists_smoothLeafField_near_faces m hfull hvertices hpositive hfinite.toFinset
    (by simp) (by intro _ _ _ ht _; exact hfinite.mem_toFinset.mpr ht)
  simpa only [Set.Finite.mem_toFinset, space] using h

end Geometry.SimplicialComplex

end

namespace OMA.SecantAdapter

open Geometry Set

end OMA.SecantAdapter

namespace OMA.PoincareSmoothLeafPort

open Geometry Set Filter Metric
open scoped ContDiff Topology

private theorem contractible_quantitative_planes
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (hm : Module.finrank ℝ E = m) (S : Set E)
    (hsecant : ∀ P : Submodule ℝ E,
      P.IsSecantTransverse S ↔ ∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y)
    (h :
      let G := {P : Submodule ℝ E //
        Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y}
      @ContractibleSpace G (TopologicalSpace.induced
        (fun P : G => P.val.starProjection) inferInstance)) :
    ContractibleSpace (SecantTransversePlaneSpace 3 S) := by
  let G := {P : Submodule ℝ E //
    Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S, ∀ y ∈ S, x - y ∈ P → x = y}
  let _ : TopologicalSpace G := TopologicalSpace.induced
    (fun P : G => P.val.starProjection) inferInstance
  let _ : ContractibleSpace G := h
  let e : SecantTransversePlaneSpace 3 S ≃ₜ G :=
    { toFun := fun P => ⟨P.val.subspace, P.property.1.trans hm,
        (hsecant _).mp P.property.2⟩
      invFun := fun P => ⟨⟨P.val⟩, P.property.1.trans hm.symm,
        (hsecant _).mpr P.property.2⟩
      left_inv := by rintro ⟨⟨P⟩, hP⟩; rfl
      right_inv := by rintro ⟨P, hP⟩; rfl
      continuous_toFun := continuous_induced_rng.mpr
        ((EuclideanSubspace.continuous_projector E).comp continuous_subtype_val)
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact EuclideanSubspace.continuous_iff_projector.mpr continuous_induced_dom }
  exact e.contractibleSpace

private theorem exists_ball_inter_space_subset_star
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) {a : E}
    (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    ∃ r : ℝ, 0 < r ∧ K.space ∩ ball a r ⊆ (K.closedFaceStar s).space := by
  let F : Set (Finset E) := {t | t ∈ K.faces ∧ ¬ s ⊆ t}
  let B : Set E := ⋃ t ∈ F, convexHull ℝ (t : Set E)
  have hF : F.Finite := hfinite.subset fun _ ht => ht.1
  have hB : IsCompact B := hF.isCompact_biUnion
    (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)
  have haB : a ∉ B := by
    intro hb
    obtain ⟨t, ht, hat⟩ := mem_iUnion₂.mp hb
    exact ht.2 (Fleet.FaceCarrier.carrierFace_subset hs ht.1 ha hat)
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl a haB
  refine ⟨r, hr, ?_⟩
  rintro x ⟨hxK, hxball⟩
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxK
  have hst : s ⊆ t := by
    by_contra hn
    exact hrB hxball (mem_iUnion₂.mpr ⟨t, ⟨ht, hn⟩, hxt⟩)
  apply (K.closedFaceStar s).convexHull_subset_space _ hxt
  exact ⟨ht, by simpa only [Finset.union_eq_right.mpr hst] using ht⟩

theorem exact_smooth_leaf_field :
    OMA.CairnsPlaneField.H2 := by
  classical
  intro m K
  dsimp only
  intro hfinite hpure hvertices hpositive
  let E := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℝ (Fin 3)
  let _ : DecidableEq E := Classical.decEq E
  have hdimE : Module.finrank ℝ E = m := finrank_euclideanSpace_fin
  have hdimV : Module.finrank ℝ V = 3 := finrank_euclideanSpace_fin
  have hvertices' (s : Finset E) (hs : s ∈ K.faces) (hcard : s.card = 1) :
      Nonempty (SecantTransversePlaneSpace 3 (K.closedFaceStar s).space) := by
    obtain ⟨P, hdim, htrans⟩ := hvertices s hs hcard
    exact ⟨⟨⟨P⟩, hdim.trans hdimE.symm,
      (OMA.SecantAdapter.star_secant_iff K hfinite s P).mpr htrans⟩⟩
  have hpositive' (s : Finset E) (hs : s ∈ K.faces) (hcard : 2 ≤ s.card) :
      ContractibleSpace (SecantTransversePlaneSpace 3 (K.closedFaceStar s).space) :=
    contractible_quantitative_planes m hdimE (K.closedFaceStar s).space
      (fun P => OMA.SecantAdapter.star_secant_iff K hfinite s P) (hpositive s hs hcard)
  obtain ⟨U, hU, hcover, P, hP, hdim, htrans⟩ :=
    K.exists_smoothLeafField_near_space hfinite 3 hpure hvertices' hpositive'
  refine ⟨fun y => (P y).subspace, ?_⟩
  intro a
  obtain ⟨s, hs, ha⟩ := Fleet.FaceCarrier.exists_carrierFace K a
  obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
  let T := (affineSpan ℝ (t : Set E)).direction
  have hTdim : Module.finrank ℝ T = Module.finrank ℝ V :=
    K.finrank_faceDirection_of_card ht (by simpa only [hdimV] using htcard)
  let A : V ≃L[ℝ] T := ContinuousLinearEquiv.ofFinrankEq hTdim.symm
  let J : V →L[ℝ] E := T.subtypeL.comp A.toContinuousLinearMap
  have hJ : Function.Injective J := Subtype.val_injective.comp A.injective
  have hJrange : J.range ≤ T := by
    rintro x ⟨z, rfl⟩
    exact (A z).property
  have htstar : t ∈ (K.closedFaceStar s).faces :=
    ⟨ht, by simpa only [Finset.union_eq_right.mpr hst] using ht⟩
  have hdisjoint (L : Submodule ℝ E) (hL : L.IsSecantTransverse (K.closedFaceStar s).space) :
      Disjoint J.range L :=
    ((K.closedFaceStar s).disjoint_faceDirection_of_isSecantTransverse htstar hL).mono_left hJrange
  have haU : (a : E) ∈ U := hcover a.property
  have htrans_single : ∀ x ∈ ({(a : E)} : Set E),
      (P x).subspace.IsSecantTransverse (K.closedFaceStar s).space := by
    intro x hx
    rw [mem_singleton_iff.mp hx]
    exact htrans s hs a (intrinsicInterior_subset ha)
  obtain ⟨W, hW, haW, hWU, R, hR, hspec, _⟩ :=
    hP.exists_transverse_frame_neighborhood hU (singleton_subset_iff.mpr haU) J hJ
      (by simpa only [hdimV] using hdim) (K.closedFaceStar s).space hdisjoint htrans_single
  have haW' : (a : E) ∈ W := haW (mem_singleton _)
  obtain ⟨r, hr, hrstar⟩ := exists_ball_inter_space_subset_star K hfinite hs ha
  refine ⟨W, R, r, hW, haW', hR, (hspec a haW').1.surjective, hr,
    ((hspec a haW').2.2.injOn (R a) rfl).mono hrstar,
    fun y hy => (hspec y hy).2.1, ?_⟩
  intro y hy
  filter_upwards [hP.eventually_eq y (hWU hy)] with z hz hzy
  exact congrArg EuclideanSubspace.subspace (hz hzy)

end OMA.PoincareSmoothLeafPort

theorem OMA.CairnsAssembly.leaves : OMA.CairnsPlaneField.H2 :=
  OMA.PoincareSmoothLeafPort.exact_smooth_leaf_field

end

/- ## Charts -/
section
open Set Filter Geometry
open scoped Topology

namespace FleetCharts

theorem face_subset_of_intrinsicInterior_mem_convexHull {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : SimplicialComplex ℝ E}
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) {a : E}
    (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hat : a ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  intro v hvs
  by_contra hvt
  obtain ⟨u, hsu, hi, hu⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top
      (s := (s : Set E)) (K.indep hs)
  let b : AffineBasis u ℝ E :=
    ⟨Subtype.val, hi, by simpa only [Subtype.range_coe] using hu⟩
  let i : u := ⟨v, hsu hvs⟩
  let f := b.coord i
  have hfv : f v = 1 := b.coord_apply_eq i
  have hf_zero {w : E} (hws : w ∈ s) (hwv : w ≠ v) : f w = 0 :=
    b.coord_apply_ne (i := i) (j := ⟨w, hsu hws⟩) (fun h => hwv (congrArg Subtype.val h).symm)
  have hf_nonneg : convexHull ℝ (s : Set E) ⊆ f ⁻¹' Ici 0 := by
    refine convexHull_min (fun w hw => ?_) ((convex_Ici (0 : ℝ)).affine_preimage f)
    change 0 ≤ f w
    by_cases hwv : w = v
    · rw [hwv, hfv]
      exact zero_le_one
    · exact (hf_zero hw hwv).ge
  have hf_face : convexHull ℝ ((s : Set E) ∩ t) ⊆ f ⁻¹' {0} := by
    refine convexHull_min (fun w hw => ?_) ((convex_singleton (0 : ℝ)).affine_preimage f)
    exact hf_zero hw.1 (fun h => hvt (h ▸ hw.2))
  have hfa : f (a : E) = 0 := hf_face (K.inter_subset_convexHull hs ht
    ⟨intrinsicInterior_subset ha, hat⟩)
  obtain ⟨a', ha', hcoe⟩ := mem_intrinsicInterior.mp ha
  let A := affineSpan ℝ (convexHull ℝ (s : Set E))
  have : Nonempty A := ⟨a'⟩
  let v' : A := ⟨v, subset_affineSpan _ _ (subset_convexHull ℝ (s : Set E) hvs)⟩
  let q : ℝ → A := AffineMap.lineMap a' v'
  have hq : Continuous q := AffineMap.lineMap_continuous
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] (0 : ℝ), (q r : E) ∈ convexHull ℝ (s : Set E) := by
    have htop : (Subtype.val ⁻¹' convexHull ℝ (s : Set E) : Set A) ∈ 𝓝 (q 0) := by
      simpa only [q, AffineMap.lineMap_apply_zero] using mem_interior_iff_mem_nhds.mp ha'
    exact hq.continuousWithinAt.eventually_mem htop
  have hneg : ∀ᶠ r : ℝ in 𝓝[<] (0 : ℝ), r < 0 := self_mem_nhdsWithin
  obtain ⟨r, hr, hrneg⟩ := (hnear.and hneg).exists
  have hnonneg : 0 ≤ f (q r : E) := hf_nonneg hr
  have hline : (q r : E) = AffineMap.lineMap (a : E) v r := by
    change A.subtype (AffineMap.lineMap a' v' r) = _
    rw [AffineMap.apply_lineMap]
    change AffineMap.lineMap (a' : E) v r = _
    rw [hcoe]
  rw [hline, AffineMap.apply_lineMap, hfa, hfv] at hnonneg
  exact hrneg.not_ge (by simpa [AffineMap.lineMap_apply_ring] using hnonneg)

theorem closedStar_mem_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) {a : K.space}
    (ha : (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    {y : K.space | (y : E) ∈ ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)} ∈ 𝓝 a := by
  let F := {t : Finset E | t ∈ K.faces ∧ ¬ s ⊆ t}
  let B := ⋃ t ∈ F, convexHull ℝ (t : Set E)
  have hF : F.Finite := hfinite.subset fun _ ht => ht.1
  have hB : IsClosed B := hF.isClosed_biUnion fun t _ => t.finite_toSet.isClosed_convexHull ℝ
  have haB : (a : E) ∉ B := by
    intro haB
    obtain ⟨t, ht, hat⟩ := mem_iUnion₂.mp haB
    exact ht.2 (face_subset_of_intrinsicInterior_mem_convexHull hs ht.1 ha hat)
  have hn : (Subtype.val ⁻¹' Bᶜ : Set K.space) ∈ 𝓝 a :=
    (hB.isOpen_compl.preimage continuous_subtype_val).mem_nhds haB
  refine mem_of_superset hn fun y hy => ?_
  change (y : E) ∉ B at hy
  obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp y.property
  have hst : s ⊆ t := by
    by_contra hst
    exact hy (mem_iUnion₂.mpr ⟨t, ⟨ht, hst⟩, hyt⟩)
  exact mem_iUnion₂.mpr ⟨t, ⟨ht, by rwa [Finset.union_eq_right.mpr hst]⟩, hyt⟩

end FleetCharts

open Set Filter Geometry Metric
open scoped NNReal Topology

namespace Fleet.ChartImage

abbrev Target := EuclideanSpace ℝ (Fin 3)

theorem subset_of_frontier_covered_by_lines {D U : Set Target} (hD : IsClosed D)
    (hU : IsOpen U) (hcU : Convex ℝ U) (hinside : (U ∩ interior D).Nonempty)
    {B : Set (Set Target)} (hf : B.Finite)
    (hdim : ∀ b ∈ B, Module.finrank ℝ (vectorSpan ℝ b) ≤ 1)
    (hfrontier : ∀ z ∈ U ∩ frontier D, ∃ b ∈ B, z ∈ affineSpan ℝ b) : U ⊆ D := by
  intro x hx
  by_contra hxD
  let A (b : Set Target) : AffineSubspace ℝ Target := affineSpan ℝ (insert x b)
  have hAproper (b : Set Target) (hb : b ∈ B) : A b ≠ ⊤ := by
    have hle := (finrank_vectorSpan_insert_le_set ℝ b x).trans
      (Nat.add_le_add_right (hdim b hb) 1)
    intro ht
    rw [← direction_affineSpan, show affineSpan ℝ (insert x b) = ⊤ from ht,
      AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace_fin] at hle
    omega
  have hAclosed (b : Set Target) : IsClosed (A b : Set Target) :=
    (A b).closed_of_finiteDimensional
  have hAdense (b : Set Target) (hb : b ∈ B) : Dense (A b : Set Target)ᶜ := by
    rw [← interior_eq_empty_iff_dense_compl, ← Set.not_nonempty_iff_eq_empty]
    intro hn
    apply hAproper b hb
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top hn, affineSpan_le]
    exact interior_subset
  let O := (fun b : Set Target => (A b : Set Target)ᶜ) '' B
  have hdense : Dense (⋂₀ O) := (hf.image _).dense_sInter
    (by rintro _ ⟨b, hb, rfl⟩; exact (hAclosed b).isOpen_compl)
    (by rintro _ ⟨b, hb, rfl⟩; exact hAdense b hb)
  obtain ⟨y, ⟨hyU, hyD⟩, hyO⟩ := hdense.inter_open_nonempty _ (hU.inter isOpen_interior) hinside
  obtain ⟨z, hzD, hxyz, hv⟩ := hD.exists_wbtw_isVisible (interior_subset hyD) x
  have hxz : x ≠ z := ne_of_mem_of_not_mem hzD hxD |>.symm
  have hzfront : z ∈ frontier D := ⟨subset_closure hzD, fun h => hxz (hv.eq_of_mem_interior h)⟩
  obtain ⟨b, hb, hz⟩ := hfrontier z ⟨hcU.mem_of_wbtw hxyz hx hyU, hzfront⟩
  have hy : y ∈ A b := AffineSubspace.right_mem_of_wbtw hxyz
    (subset_affineSpan ℝ _ (mem_insert x b))
    (affineSpan_mono ℝ (subset_insert x b) hz) hxz
  exact (mem_sInter.mp hyO _ (mem_image_of_mem _ hb)) hy

theorem affineIndependent_comp_of_injOn_convexHull {E V ι : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    {p : ι → E} (hp : AffineIndependent ℝ p) (f : E →ᵃ[ℝ] V)
    (hf : InjOn f (convexHull ℝ (range p))) : AffineIndependent ℝ (f ∘ p) := by
  by_contra h
  obtain ⟨I, z, hz, hz'⟩ := Convex.radon_partition h
  change z ∈ convexHull ℝ ((fun i => f (p i)) '' I) at hz
  change z ∈ convexHull ℝ ((fun i => f (p i)) '' Iᶜ) at hz'
  rw [← Set.image_image f p I, ← f.image_convexHull] at hz
  rw [← Set.image_image f p Iᶜ, ← f.image_convexHull] at hz'
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨y, hy, hyz⟩ := hz'
  have hxy := hf (convexHull_mono (image_subset_range p I) hx)
    (convexHull_mono (image_subset_range p Iᶜ) hy) (hxz.trans hyz.symm)
  subst y
  exact (Set.disjoint_left.mp (hp.affineSpan_disjoint_of_disjoint disjoint_compl_right))
    (convexHull_subset_affineSpan _ hx) (convexHull_subset_affineSpan _ hy)

section Facet

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private theorem isOpen_positive_coords [Finite ι] (b : AffineBasis ι ℝ V) (i : ι) :
    IsOpen {x : V | ∀ j : {j : ι // j ≠ i}, 0 < b.coord j x} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_barycentric_coord b j)

omit [FiniteDimensional ℝ V] in

theorem mem_convexHull_opposite_iff [Fintype ι] (b : AffineBasis ι ℝ V) {x : V}
    (hx : x ∈ convexHull ℝ (range b)) (i : ι) :
    x ∈ convexHull ℝ (b '' ({i}ᶜ : Set ι)) ↔ b.coord i x = 0 := by
  classical
  constructor
  · intro h
    have h' := mem_image_of_mem (b.coord i) h
    rw [(b.coord i).image_convexHull] at h'
    have hnull : (b.coord i) '' (b '' ({i}ᶜ : Set ι)) ⊆ ({0} : Set ℝ) := by
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact b.coord_apply_ne (fun h => hj (Set.mem_singleton_iff.mpr h.symm))
    simpa using convexHull_mono hnull h'
  · intro hz
    rw [b.convexHull_eq_nonneg_coord] at hx
    let p := Finset.univ.erase i
    have hsum : ∑ j ∈ p, b.coord j x = 1 := by
      simp only [p, Finset.sum_erase_eq_sub (Finset.mem_univ i), b.sum_coord_apply_eq_one, hz,
        sub_zero]
    have hvec : ∑ j ∈ p, b.coord j x • b j = x := by
      simp only [p, Finset.sum_erase_eq_sub (Finset.mem_univ i),
        b.linear_combination_coord_eq_self, hz, zero_smul, sub_zero]
    rw [← hvec]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => hx j) hsum fun j hj =>
      subset_convexHull _ _ (mem_image_of_mem _ (by simpa [p] using hj))

theorem mem_interior_union_of_adjacent_simplices [Fintype ι] [Fintype κ]
    (b : AffineBasis ι ℝ V) (c : AffineBasis κ ℝ V) (i₀ : ι) (j₀ : κ)
    (hshare : ∀ j ≠ j₀, ∃ i ≠ i₀, b i = c j)
    (hdis : Disjoint (interior (convexHull ℝ (range b))) (interior (convexHull ℝ (range c))))
    {x : V} (hx : x ∈ convexHull ℝ (range c))
    (hxb : ∀ i ≠ i₀, 0 < b.coord i x) (hxc : ∀ j ≠ j₀, 0 < c.coord j x) :
    x ∈ interior (convexHull ℝ (range b) ∪ convexHull ℝ (range c)) := by
  let k := b.coord i₀ (c j₀)
  have heq : b.coord i₀ = k • c.coord j₀ := by
    apply AffineMap.ext_on c.tot
    rintro _ ⟨j, rfl⟩
    change b.coord i₀ (c j) = k • c.coord j₀ (c j)
    by_cases hj : j = j₀
    · subst j
      simp [k]
    · obtain ⟨i, hi, hij⟩ := hshare j hj
      rw [c.coord_apply_ne (Ne.symm hj), smul_zero, ← hij, b.coord_apply_ne hi.symm]
  have hscale (y : V) : b.coord i₀ y = k * c.coord j₀ y := by
    simpa only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] using DFunLike.congr_fun heq y
  let U := {y : V | ∀ i : {i : ι // i ≠ i₀}, 0 < b.coord i y}
  let W := {y : V | ∀ j : {j : κ // j ≠ j₀}, 0 < c.coord j y}
  have hU : IsOpen U := isOpen_positive_coords b i₀
  have hW : IsOpen W := isOpen_positive_coords c j₀
  have hxU : x ∈ U := fun i => hxb i i.property
  have hxW : x ∈ W := fun j => hxc j j.property
  have hk : k < 0 := by
    by_contra! hk
    have hk' : 0 < k := lt_of_le_of_ne hk fun hn => by
      simpa [← hn] using hscale (b i₀)
    have hcconv := convex_convexHull ℝ (range c)
    have hcl := hcconv.closure_interior_eq_closure_of_nonempty_interior
      ⟨_, c.centroid_mem_interior_convexHull⟩
    have hxcl : x ∈ closure (interior (convexHull ℝ (range c))) := hcl.symm ▸ subset_closure hx
    obtain ⟨y, hyU, hyc⟩ := mem_closure_iff_nhds.mp hxcl _ (hU.mem_nhds hxU)
    refine (Set.disjoint_left.mp hdis) (a := y) ?_ hyc
    rw [b.interior_convexHull]
    intro i
    by_cases hi : i = i₀
    · subst i
      rw [hscale]
      rw [c.interior_convexHull] at hyc
      exact mul_pos hk' (hyc j₀)
    · exact hyU ⟨i, hi⟩
  apply mem_interior_iff_mem_nhds.2
  apply Filter.mem_of_superset ((hU.inter hW).mem_nhds ⟨hxU, hxW⟩)
  rintro y ⟨hyU, hyW⟩
  by_cases hi₀ : 0 ≤ b.coord i₀ y
  · apply Or.inl
    rw [b.convexHull_eq_nonneg_coord]
    intro i
    by_cases hi : i = i₀
    · simpa [hi] using hi₀
    · exact (hyU ⟨i, hi⟩).le
  · apply Or.inr
    rw [c.convexHull_eq_nonneg_coord]
    intro j
    by_cases hj : j = j₀
    · subst j
      exact le_of_lt (pos_of_mul_neg_right (hscale y ▸ lt_of_not_ge hi₀) hk.le)
    · exact (hyW ⟨j, hj⟩).le

end Facet

theorem mem_interior_affine_image_closedStar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4)
    (htriangle : ∀ t ∈ K.faces, t.card = 3 →
      ({p : E | {p} ∈ K.faces ∧ Disjoint t {p} ∧ t ∪ {p} ∈ K.faces} : Set E).ncard = 2)
    {s : Finset E} (hs : s ∈ K.faces) {a : E}
    (ha : a ∈ convexHull ℝ (s : Set E))
    (hminimal : ∀ t ∈ K.faces, a ∈ convexHull ℝ (t : Set E) → s ⊆ t)
    (f : E →ᵃ[ℝ] Target)
    (hf : InjOn f (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E))) :
    f a ∈ interior (f '' (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E))) := by
  classical
  let F : Set (Finset E) := {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}
  let T : Set (Finset E) := {t | t ∈ K.faces ∧ s ⊆ t ∧ t.card = 4}
  let H (t : Finset E) := convexHull ℝ (f '' (t : Set E))
  let D := ⋃ t ∈ T, H t
  have hTstar {t : Finset E} (ht : t ∈ T) : t ∈ F :=
    ⟨ht.1, by simpa [Finset.union_eq_right.mpr ht.2.1] using ht.1⟩
  have hsubstar {t u : Finset E} (ht : t ∈ T) (hu : u ⊆ t) (hne : u.Nonempty) : u ∈ F :=
    ⟨K.down_closed ht.1 hu hne, K.down_closed ht.1 (Finset.union_subset ht.2.1 hu)
      (hne.mono Finset.subset_union_right)⟩
  have hH (t : Finset E) : H t = f '' convexHull ℝ (t : Set E) :=
    (f.image_convexHull _).symm
  have hHD {t : Finset E} (ht : t ∈ T) : H t ⊆ D := subset_iUnion₂ (s := fun t _ => H t) t ht
  have hD : f '' (⋃ t ∈ F, convexHull ℝ (t : Set E)) = D := by
    rw [image_iUnion]
    simp only [image_iUnion, ← hH]
    refine subset_antisymm ?_ (iUnion₂_subset fun t ht => ?_)
    · refine iUnion₂_subset fun u hu => ?_
      obtain ⟨t, ht, hst, h4⟩ := hpure (s ∪ u) hu.2
      exact (convexHull_mono (image_mono (Finset.coe_subset.mpr
        (Finset.subset_union_right.trans hst)))).trans
          (hHD ⟨ht, Finset.subset_union_left.trans hst, h4⟩)
    · exact subset_iUnion₂ (s := fun t _ => H t) t (hTstar ht)
  change f a ∈ interior (f '' (⋃ t ∈ F, convexHull ℝ (t : Set E)))
  rw [hD]
  have hclosed (A : Set (Finset E)) (hA : A ⊆ K.faces) : IsClosed (⋃ t ∈ A, H t) :=
    (hfinite.subset hA).isClosed_biUnion fun t _ =>
      ((t.finite_toSet.image f).isCompact_convexHull ℝ).isClosed
  let O : Set (Finset E) := {t ∈ F | ¬ s ⊆ t}
  let C := (⋃ t ∈ O, H t)ᶜ
  have hC : IsOpen C := (hclosed O fun t ht => ht.1.1).isOpen_compl
  have hsF : s ∈ F := ⟨hs, by simpa using hs⟩
  have haS : a ∈ ⋃ t ∈ F, convexHull ℝ (t : Set E) := mem_iUnion₂.mpr ⟨s, hsF, ha⟩
  have haC : f a ∈ C := by
    rintro h
    obtain ⟨t, ht, hta⟩ := mem_iUnion₂.mp h
    rw [hH] at hta
    obtain ⟨x, hx, hxa⟩ := hta
    have he : x = a := hf (mem_iUnion₂.mpr ⟨t, ht.1, hx⟩) haS hxa
    exact ht.2 (hminimal t ht.1.1 (he ▸ hx))
  obtain ⟨r, hr, hrC⟩ := Metric.isOpen_iff.mp hC (f a) haC
  let U := ball (f a) r
  have haU : f a ∈ U := mem_ball_self hr
  have hCoeRange (t : Finset E) : range ((↑) : t → E) = (t : Set E) := by
    ext x
    simp
  have hRange (t : Finset E) : range (fun x : t => f x) = f '' (t : Set E) := by
    change range (f ∘ ((↑) : t → E)) = _
    rw [Set.range_comp, hCoeRange]
  let b (t : Finset E) (ht : t ∈ T) : AffineBasis t ℝ Target := by
    have hind : AffineIndependent ℝ (fun x : t => f x) := by
      apply affineIndependent_comp_of_injOn_convexHull (K.indep ht.1) f
      rw [hCoeRange t]
      exact hf.mono (fun _ hx => mem_iUnion₂.mpr ⟨t, hTstar ht, hx⟩)
    exact ⟨_, hind, hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by simpa using ht.2.2)⟩
  have hb (t : Finset E) (ht : t ∈ T) : range (b t ht) = f '' (t : Set E) := hRange t
  have hinside : (U ∩ interior D).Nonempty := by
    obtain ⟨t, ht, hst, hcard⟩ := hpure s hs
    have htT : t ∈ T := ⟨ht, hst, hcard⟩
    have hta : f a ∈ H t := by rw [hH]; exact mem_image_of_mem _ (convexHull_mono hst ha)
    have hne : (interior (H t)).Nonempty := by
      change (interior (convexHull ℝ (f '' (t : Set E)))).Nonempty
      rw [← hb t htT]
      exact ⟨_, (b t htT).centroid_mem_interior_convexHull⟩
    have hcl : f a ∈ closure (interior (H t)) := by
      have hConv : Convex ℝ (H t) := convex_convexHull ℝ _
      rw [hConv.closure_interior_eq_closure_of_nonempty_interior hne]
      exact subset_closure hta
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff_nhds.mp hcl U (isOpen_ball.mem_nhds haU)
    exact ⟨z, hzU, interior_mono (hHD htT) hz⟩
  let B : Set (Finset E) := {u ∈ K.faces | u.card = 2}
  have hBF : B ⊆ K.faces := fun _ hu => hu.1
  have hcap {u v : Finset E} (hu : u ∈ F) (hv : v ∈ F) : H u ∩ H v ⊆ H (u ∩ v) := by
    rw [hH, hH, hH]
    rintro _ ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    have he : y = x := hf (mem_iUnion₂.mpr ⟨v, hv, hy⟩) (mem_iUnion₂.mpr ⟨u, hu, hx⟩) hyx
    refine mem_image_of_mem _ ?_
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hu.1 hv.1]
    exact ⟨hx, he ▸ hy⟩
  have hOpp (t : Finset E) (ht : t ∈ T) (i : t) :
      b t ht '' ({i}ᶜ : Set t) = f '' (t.erase (i : E) : Set E) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hvi, hvt⟩ := Finset.mem_erase.mp hv
      exact ⟨⟨v, hvt⟩, fun h => hvi (congrArg Subtype.val h), rfl⟩
  have hErase (t : Finset E) (ht : t ∈ T) (i : t) : t.erase (i : E) ∈ F :=
    hsubstar ht (Finset.erase_subset _ _) (Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem i.property, ht.2.2]; decide))
  have hCoord (t : Finset E) (ht : t ∈ T) {z : Target} (hz : z ∈ H t) (i : t) :
      z ∈ H (t.erase (i : E)) ↔ (b t ht).coord i z = 0 := by
    change z ∈ convexHull ℝ (f '' (t.erase (i : E) : Set E)) ↔ _
    rw [← hOpp t ht i]
    exact mem_convexHull_opposite_iff (b t ht) (by rwa [hb t ht]) i
  refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (isOpen_ball.mem_nhds haU) ?_)
  apply subset_of_frontier_covered_by_lines (hclosed T fun t ht => ht.1) isOpen_ball
    (convex_ball _ _) hinside ((hfinite.subset hBF).image
      (fun u : Finset E => f '' (u : Set E)))
  · rintro _ ⟨u, hu, rfl⟩
    change Module.finrank ℝ (vectorSpan ℝ (f '' (u : Set E))) ≤ 1
    rw [← hRange u]
    exact finrank_vectorSpan_range_le ℝ (fun x : u => f x) (by simpa using hu.2)
  intro z hz
  by_cases hsmall : ∃ u ∈ B, z ∈ H u
  · obtain ⟨u, hu, hzu⟩ := hsmall
    exact ⟨_, mem_image_of_mem _ hu, convexHull_subset_affineSpan _ hzu⟩
  exfalso
  have hzD := (hclosed T fun t ht => ht.1).frontier_subset hz.2
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzD
  have hnot : ¬ ∀ i, 0 < (b t ht).coord i z := by
    intro h
    apply hz.2.2
    apply interior_mono (hHD ht)
    rw [show H t = convexHull ℝ (range (b t ht)) by rw [hb t ht], (b t ht).interior_convexHull]
    exact h
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hnonneg {t : Finset E} (ht : t ∈ T) (hzt : z ∈ H t) (k : t) :
      0 ≤ (b t ht).coord k z := by
    rw [show H t = convexHull ℝ (range (b t ht)) by rw [hb t ht],
      (b t ht).convexHull_eq_nonneg_coord] at hzt
    exact hzt k
  let u := t.erase (i : E)
  have hzu : z ∈ H u := (hCoord t ht hzt i).2 (le_antisymm (le_of_not_gt hi) (hnonneg ht hzt i))
  have huF : u ∈ F := hErase t ht i
  have hu3 : u.card = 3 := by rw [Finset.card_erase_of_mem i.property, ht.2.2]
  have hti : u ∪ {(i : E)} = t := by rw [Finset.union_singleton, Finset.insert_erase i.property]
  have hsu : s ⊆ u := by
    by_contra hs'
    exact (hrC hz.1) (mem_iUnion₂.mpr ⟨u, ⟨huF, hs'⟩, hzu⟩)
  let L : Set E := {p | {p} ∈ K.faces ∧ Disjoint u {p} ∧ u ∪ {p} ∈ K.faces}
  have hLn : L.ncard = 2 := htriangle u huF.1 hu3
  obtain ⟨p, q, hpq, hL⟩ := Set.ncard_eq_two.mp hLn
  have hother : ∃ j ∈ L, j ≠ (i : E) := by
    rw [hL]
    by_cases hpi : p = (i : E)
    · exact ⟨q, by simp, fun hqi => hpq (hpi.trans hqi.symm)⟩
    · exact ⟨p, by simp, hpi⟩
  obtain ⟨j, hj, hji⟩ := hother
  have hju := Finset.disjoint_singleton_right.mp hj.2.1
  let v := u ∪ {j}
  have hv : v ∈ T := ⟨hj.2.2, hsu.trans Finset.subset_union_left, by
    change (u ∪ {j}).card = 4
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hju, hu3]⟩
  have hjv : j ∈ v := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  let j₀ : v := ⟨j, hjv⟩
  have hve : v.erase j = u := by
    change (u ∪ {j}).erase j = u
    rw [Finset.union_singleton, Finset.erase_insert hju]
  have hzv : z ∈ H v := convexHull_mono (image_mono (Finset.coe_subset.mpr
    (Finset.subset_union_left : u ⊆ v))) hzu
  have huv : t ∩ v = u := by
    rw [← hti]
    ext x
    simp only [v, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hxi, hx' | hxj⟩
      · exact hx
      · exact hx
      · exact hx'
      · exact (hji (hxj.symm.trans hxi)).elim
    · intro hx
      exact ⟨Or.inl hx, Or.inl hx⟩
  have hpositive {t : Finset E} (ht : t ∈ T) (hzt : z ∈ H t) (i : t)
      (hzfacet : z ∈ H (t.erase (i : E))) (k : t) (hki : k ≠ i) : 0 < (b t ht).coord k z := by
    have hki' : (k : E) ≠ i := fun h => hki (Subtype.ext h)
    by_contra! hnot
    have hzero := le_antisymm hnot (hnonneg ht hzt k)
    have hzk := (hCoord t ht hzt k).2 hzero
    have he := hcap (hErase t ht k) (hErase t ht i) ⟨hzk, hzfacet⟩
    rw [Finset.erase_inter, Finset.inter_eq_right.mpr (Finset.erase_subset _ _)] at he
    have hkface : (k : E) ∈ t.erase (i : E) := Finset.mem_erase.2 ⟨hki', k.property⟩
    have hcard : ((t.erase (i : E)).erase (k : E)).card = 2 := by
      rw [Finset.card_erase_of_mem hkface, Finset.card_erase_of_mem i.property, ht.2.2]
    have hne : ((t.erase (i : E)).erase (k : E)).Nonempty := Finset.card_pos.mp (by simp [hcard])
    exact hsmall ⟨_, ⟨K.down_closed (hErase t ht i).1 (Finset.erase_subset _ _) hne, hcard⟩, he⟩
  have hshare (k : v) (hkj : k ≠ j₀) : ∃ l : t, l ≠ i ∧ b t ht l = b v hv k := by
    have hkU : (k : E) ∈ u := by
      rw [← hve]
      exact Finset.mem_erase.2 ⟨fun h => hkj (Subtype.ext h), k.property⟩
    have hku := Finset.mem_erase.mp hkU
    exact ⟨⟨k, hku.2⟩, fun h => hku.1 (congrArg Subtype.val h), rfl⟩
  have hdis : Disjoint (interior (convexHull ℝ (range (b t ht))))
      (interior (convexHull ℝ (range (b v hv)))) := by
    apply Set.disjoint_left.2
    intro y hyt hyv
    have hy : y ∈ H u := by
      rw [← huv]
      apply hcap (hTstar ht) (hTstar hv)
      simp only [hb] at hyt hyv
      exact ⟨interior_subset hyt, interior_subset hyv⟩
    have hy0 := (hCoord t ht (interior_subset (by simpa only [hb] using hyt)) i).1 hy
    rw [(b t ht).interior_convexHull] at hyt
    exact (hyt i).ne' hy0
  have hzfacet : z ∈ H (v.erase (j₀ : E)) := hve.symm ▸ hzu
  have hzint := mem_interior_union_of_adjacent_simplices (b t ht) (b v hv) i j₀ hshare hdis
    (by rwa [hb v hv]) (hpositive ht hzt i hzu) (hpositive hv hzv j₀ hzfacet)
  simp only [hb] at hzint
  exact hz.2.2 (interior_mono (Set.union_subset (hHD ht) (hHD hv)) hzint)

theorem zero_mem_interior_frozenProjection_closedStar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4)
    (htriangle : ∀ t ∈ K.faces, t.card = 3 →
      ({p : E | {p} ∈ K.faces ∧ Disjoint t {p} ∧ t ∪ {p} ∈ K.faces} : Set E).ncard = 2)
    {s : Finset E} (hs : s ∈ K.faces) {a : E}
    (ha : a ∈ convexHull ℝ (s : Set E))
    (hminimal : ∀ t ∈ K.faces, a ∈ convexHull ℝ (t : Set E) → s ⊆ t)
    (Q : E →L[ℝ] Target) (L : ℝ≥0)
    (hL : let S := ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
        convexHull ℝ (t : Set E)
      ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖Q x - Q y‖) :
    (0 : Target) ∈ interior ((fun x : E => Q (x - a)) ''
      (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
        convexHull ℝ (t : Set E))) := by
  let f : E →ᵃ[ℝ] Target := Q.toLinearMap.toAffineMap - AffineMap.const ℝ E (Q a)
  have hf : (f : E → Target) = fun x => Q (x - a) := by
    funext x
    change Q x - Q a = Q (x - a)
    rw [map_sub]
  have hinj : InjOn f (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)) := by
    intro x hx y hy hxy
    have hQxy : Q x = Q y := by
      simpa only [sub_add_cancel] using
        congrArg (fun z : Target => z + Q a) (show Q x - Q a = Q y - Q a from hxy)
    have h := hL x hx y hy
    have hnorm : ‖x - y‖ = 0 := le_antisymm (by simpa [hQxy] using h) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  simpa only [hf, sub_self, map_zero] using
    mem_interior_affine_image_closedStar K hfinite hpure htriangle hs ha hminimal f hinj

end Fleet.ChartImage

open Set Filter
open scoped ContDiff NNReal Topology

namespace Fleet.Charts

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasStrictFDerivAt_varyingProjection {Q : E → E →L[ℝ] V} {a : E}
    (hQ : ContDiffAt ℝ ∞ Q a) :
    HasStrictFDerivAt (fun y => Q y (y - a)) (Q a) a := by
  have hzero : (fderiv ℝ Q a).flip (a - a) = 0 := by
    ext x
    simp
  simpa only [ContinuousLinearMap.comp_id, hzero, add_zero] using
    (hQ.hasStrictFDerivAt (by simp)).clm_apply
      (hasStrictFDerivAt_sub_const (𝕜 := ℝ) (x := a) a)

theorem exists_approximatesLinearOn_varyingProjection {Q : E → E →L[ℝ] V} {a : E}
    (hQ : ContDiffAt ℝ ∞ Q a) (L : ℝ≥0) :
    ∃ (c : ℝ≥0) (U : Set E), c < (L + 1)⁻¹ ∧ c * L < 1 ∧ IsOpen U ∧ a ∈ U ∧
      ApproximatesLinearOn (fun y => Q y (y - a)) (Q a) U c := by
  have hden : 0 < L + 1 := zero_lt_one.trans_le (le_add_of_nonneg_left zero_le)
  have hpos : 0 < (L + 1)⁻¹ := inv_pos.mpr hden
  let c : ℝ≥0 := (L + 1)⁻¹ / 2
  have hc : 0 < c := half_pos hpos
  have hlt : c < (L + 1)⁻¹ := half_lt_self hpos
  have hinv : (L + 1)⁻¹ * L < 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_one hden).mpr (lt_add_of_pos_right L zero_lt_one)
  have hmul : c * L < 1 := (mul_le_mul_of_nonneg_right hlt.le (show 0 ≤ L from zero_le)).trans_lt hinv
  obtain ⟨U, hU, happrox⟩ :=
    (hasStrictFDerivAt_varyingProjection hQ).approximates_deriv_on_nhds (Or.inr hc)
  obtain ⟨U₀, hsub, hopen, ha⟩ := _root_.mem_nhds_iff.mp hU
  exact ⟨c, U₀, hlt, hmul, hopen, ha, happrox.mono_set hsub⟩

theorem exists_varyingProjection_chart [CompleteSpace V] [Nontrivial V]
    {X : Type*} [TopologicalSpace X] {v : X → E} (hv : Continuous v) {a : X}
    {Q : E → E →L[ℝ] V} (hQ : ContDiffAt ℝ ∞ Q (v a))
    {S : Set E} (L : ℝ≥0)
    (hL : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖Q (v a) x - Q (v a) y‖)
    (d : OpenPartialHomeomorph X V) (ha : a ∈ d.source)
    (hS : ∀ x ∈ d.source, v x ∈ S)
    (hd : ∀ x ∈ d.source, d x = Q (v a) (v x - v a))
    {W : Set X} (hW : W ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph X V, a ∈ e.source ∧ e.source ⊆ W ∧
      ∀ x ∈ e.source, e x = Q (v x) (v x - v a) := by
  obtain ⟨c, U, _, hcL, hU, haU, happrox⟩ := exists_approximatesLinearOn_varyingProjection hQ L
  obtain ⟨W₀, hW₀W, hW₀, haW₀⟩ := _root_.mem_nhds_iff.mp hW
  let d₀ := d.restrOpen (W₀ ∩ v ⁻¹' U) (hW₀.inter (hU.preimage hv))
  have ha₀ : a ∈ d₀.source := ⟨ha, haW₀, haU⟩
  let f := fun z : V => Q (v (d₀.symm z)) (v (d₀.symm z) - v a)
  let idV := ContinuousLinearEquiv.refl ℝ V
  have hcoord (z : V) (hz : z ∈ d₀.target) : Q (v a) (v (d₀.symm z) - v a) = z := by
    have hs : d₀.symm z ∈ d₀.source := d₀.map_target hz
    exact (hd _ hs.1).symm.trans (d₀.right_inv hz)
  have happ : ApproximatesLinearOn f (idV : V →L[ℝ] V) d₀.target (c * L) := by
    intro x hx y hy
    have hx₀ : d₀.symm x ∈ d₀.source := d₀.map_target hx
    have hy₀ : d₀.symm y ∈ d₀.source := d₀.map_target hy
    have hlin : Q (v a) (v (d₀.symm x) - v (d₀.symm y)) = x - y := by
      rw [← sub_sub_sub_cancel_right (v (d₀.symm x)) (v (d₀.symm y)) (v a),
        map_sub, hcoord x hx, hcoord y hy]
    have hlower := hL _ (hS _ hx₀.1) _ (hS _ hy₀.1)
    rw [← map_sub, hlin] at hlower
    have hres := happrox _ hx₀.2.2 _ hy₀.2.2
    rw [hlin] at hres
    change ‖f x - f y - (x - y)‖ ≤ (c : ℝ) * (L : ℝ) * ‖x - y‖
    rw [mul_assoc]
    exact hres.trans (mul_le_mul_of_nonneg_left hlower c.coe_nonneg)
  have hid : ‖(idV.symm : V →L[ℝ] V)‖₊ = 1 := ContinuousLinearMap.nnnorm_id
  have hcId : Subsingleton V ∨ c * L < ‖(idV.symm : V →L[ℝ] V)‖₊⁻¹ := by
    exact Or.inr (by rwa [hid, inv_one])
  let p := happ.toOpenPartialHomeomorph f d₀.target hcId d₀.open_target
  refine ⟨d₀.trans' p rfl, ha₀, fun x hx => hW₀W hx.2.1, ?_⟩
  · intro x hx
    change f (d₀ x) = Q (v x) (v x - v a)
    simp only [f, d₀.left_inv hx]

end Fleet.Charts

open Set Filter Metric
open scoped NNReal Topology

namespace Fleet.Charts

private theorem fixedProjectionChart {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Continuous f) {a : X} {S : Set X} (hS : S ∈ 𝓝 a)
    (himage : f '' S ∈ 𝓝 (f a)) (L : ℝ≥0)
    (hL : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ L * dist (f x) (f y)) :
    ∃ e : OpenPartialHomeomorph X Y, a ∈ e.source ∧ e.source ⊆ S ∧ EqOn e f e.source := by
  classical
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨R, hR, hRS⟩ := Metric.mem_nhds_iff.mp himage
  have hpos : 0 < (L : ℝ) + 1 := by positivity
  let δ := min R (r / ((L : ℝ) + 1))
  have hδ : 0 < δ := lt_min hR (div_pos hr hpos)
  have hδr : ((L : ℝ) + 1) * δ ≤ r := by
    calc
      _ ≤ ((L : ℝ) + 1) * (r / ((L : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le
      _ = r := by field_simp [hpos.ne']
  let T := ball a r ∩ f ⁻¹' ball (f a) δ
  have hT : T ⊆ S := fun _ hx => hrS hx.1
  have haT : a ∈ T := ⟨mem_ball_self hr, mem_ball_self hδ⟩
  have hopen : IsOpen T := isOpen_ball.inter (isOpen_ball.preimage hf)
  have htarget : f '' T = ball (f a) δ := by
    refine subset_antisymm (fun z ⟨y, hy, h⟩ => h ▸ hy.2) ?_
    intro z hz
    have hzR : z ∈ ball (f a) R := (mem_ball.mp hz).trans_le (min_le_left _ _)
    obtain ⟨y, hy, rfl⟩ := hRS hzR
    refine ⟨y, ⟨?_, hz⟩, rfl⟩
    calc
      dist y a ≤ (L : ℝ) * dist (f y) (f a) := hL y hy a (mem_of_mem_nhds hS)
      _ ≤ ((L : ℝ) + 1) * dist (f y) (f a) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg
      _ < ((L : ℝ) + 1) * δ := mul_lt_mul_of_pos_left (mem_ball.mp hz) hpos
      _ ≤ r := hδr
  have hi : InjOn f T := by
    intro x hx y hy hxy
    have h := hL x (hT hx) y (hT hy)
    simpa [hxy] using h
  let : Nonempty X := ⟨a⟩
  let p := hi.toPartialEquiv f T
  have hpinv : LipschitzOnWith L p.symm p.target := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hL _ (hT (p.map_target hx)) _ (hT (p.map_target hy))
    change dist (p.symm x) (p.symm y) ≤ L * dist (p (p.symm x)) (p (p.symm y)) at h
    simpa only [p.right_inv hx, p.right_inv hy] using h
  exact ⟨{ toPartialEquiv := p
           open_source := hopen
           open_target := by change IsOpen (f '' T); rw [htarget]; exact isOpen_ball
           continuousOn_toFun := hf.continuousOn
           continuousOn_invFun := hpinv.continuousOn }, haT, hT, fun _ _ => rfl⟩

theorem exists_fixedProjection_chart {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {A S : Set E} (hSA : S ⊆ A)
    (a : A) (q : E →L[ℝ] V) (L : ℝ≥0)
    (hL : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖q x - q y‖)
    (hn : (Subtype.val ⁻¹' S : Set A) ∈ 𝓝 a)
    (hi : (0 : V) ∈ interior ((fun x : E => q (x - (a : E))) '' S)) :
    ∃ d : OpenPartialHomeomorph A V, a ∈ d.source ∧
      (∀ x ∈ d.source, (x : E) ∈ S) ∧
      ∀ x ∈ d.source, d x = q ((x : E) - (a : E)) := by
  let g := fun x : E => q (x - (a : E))
  let f := fun x : A => g x
  have hf : Continuous f := q.continuous.comp (continuous_subtype_val.sub continuous_const)
  have hEq : f '' (Subtype.val ⁻¹' S : Set A) = g '' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hSA hy⟩, hy, rfl⟩
  have hImage : f '' (Subtype.val ⁻¹' S : Set A) ∈ 𝓝 (f a) := by
    rw [hEq]
    have ha : f a = 0 := by simp [f, g]
    rw [ha]
    exact mem_interior_iff_mem_nhds.mp hi
  have hdist (x : A) (hx : x ∈ (Subtype.val ⁻¹' S : Set A))
      (y : A) (hy : y ∈ (Subtype.val ⁻¹' S : Set A)) :
      dist x y ≤ L * dist (f x) (f y) := by
    change dist (x : E) (y : E) ≤ L * dist (g x) (g y)
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : g x - g y = q x - q y := by
      simp only [g, map_sub]
      abel
    rw [hsub]
    exact hL x hx y hy
  exact fixedProjectionChart hf hn hImage L hdist

end Fleet.Charts

open Set Filter Geometry
open scoped NNReal Topology

theorem OMA.CairnsAssembly.charts : OMA.CairnsLeafCoordinates.H2 := by
  classical
  intro m K
  dsimp only
  intro hfinite hpure htriangle s hs a ha Q J _W hQ _hJ hbound hW
  let E := EuclideanSpace ℝ (Fin m)
  let : DecidableEq E := Classical.decEq E
  let S : Set E :=
    ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)
  obtain ⟨L, hL⟩ := hbound
  have hSA : S ⊆ K.space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact K.convexHull_subset_space ht.1 hxt
  have hn : (Subtype.val ⁻¹' S : Set K.space) ∈ 𝓝 a :=
    FleetCharts.closedStar_mem_nhds K hfinite hs ha
  have hi : (0 : EuclideanSpace ℝ (Fin 3)) ∈
      interior ((fun x : E => Q a (x - (a : E))) '' S) := by
    exact Fleet.ChartImage.zero_mem_interior_frozenProjection_closedStar K hfinite hpure htriangle hs
      (intrinsicInterior_subset ha)
      (fun t ht hat => FleetCharts.face_subset_of_intrinsicInterior_mem_convexHull hs ht ha hat)
      (Q a) L hL
  obtain ⟨d, had, hSd, hd⟩ :=
    Fleet.Charts.exists_fixedProjection_chart hSA a (Q a) L hL hn hi
  exact Fleet.Charts.exists_varyingProjection_chart continuous_subtype_val hQ L hL
    d had hSd hd hW

end

/- ## Overlap -/
section
open Set Geometry
open scoped Manifold ContDiff

namespace OMA.Helpers

theorem transition_smooth {m : ℕ} {M : Type} [TopologicalSpace M]
    (c : M → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (v : M → EuclideanSpace ℝ (Fin m)) (P : M → Submodule ℝ (EuclideanSpace ℝ (Fin m)))
    (b : M → EuclideanSpace ℝ (Fin 3) →ᴬ[ℝ] EuclideanSpace ℝ (Fin m))
    (Q : M → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hsm : ∀ i z, z ∈ (c i).target → ContDiffAt ℝ ∞ (Q i) (b i z))
    (hlin : ∀ i y, y ∈ (c i).source → Function.RightInverse (b i).contLinear (Q i (v y)) ∧
      (Q i (v y)).ker = P y ∧ Q i (b i (c i y)) = Q i (v y) ∧ b i (c i y) - v y ∈ P y)
    (i j : M) :
    ContDiffOn ℝ ∞ ((c i).symm ≫ₕ c j) ((c i).symm ≫ₕ c j).source := by
  let T : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun z => (Q i (b i z)).comp (b j).contLinear
  let Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun z => (T z).inverse (Q i (b i z) (b i z - b j 0))
  have key : ∀ z ∈ ((c i).symm ≫ₕ c j).source,
      ∃ e : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3),
        (e : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) = T z ∧
        Φ z = ((c i).symm ≫ₕ c j) z := by
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hzt, hzj⟩ := hz
    set y := (c i).symm z with hy
    have hyi : y ∈ (c i).source := (c i).map_target hzt
    have hzi : c i y = z := (c i).right_inv hzt
    obtain ⟨-, hki, hQi, hmi⟩ := hlin i y hyi
    obtain ⟨hrj, hkj, -, hmj⟩ := hlin j y hzj
    rw [hzi] at hQi hmi
    have hTz : T z = (Q i (v y)).comp (b j).contLinear := by
      simp only [T, hQi]
    have hinj : (T z).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro u hu
      have h1 : (b j).contLinear u ∈ P y := by
        rw [← hki, LinearMap.mem_ker]
        rw [hTz] at hu
        simpa using hu
      rw [← hkj, LinearMap.mem_ker] at h1
      have := hrj u
      simp only at this
      rw [← this]
      exact h1
    have hsurj : (T z).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      have hi : Function.Injective ((T z : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
          EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :=
        LinearMap.ker_eq_bot.mp hinj
      exact LinearMap.injective_iff_surjective.mp hi
    let e := ContinuousLinearEquiv.ofBijective (T z) hinj hsurj
    refine ⟨e, ContinuousLinearEquiv.coe_ofBijective _ _ _, ?_⟩
    have hw : T z (c j y) = Q i (b i z) (b i z - b j 0) := by
      have hsplit : (b j).contLinear (c j y) = b j (c j y) - b j 0 := by
        have := (b j).contLinear_map_vsub (c j y) 0
        simpa [vsub_eq_sub] using this
      have hdiff : b j (c j y) - b i z ∈ P y := by
        have := Submodule.sub_mem _ hmj hmi
        simpa using this
      rw [← hki, LinearMap.mem_ker] at hdiff
      simp only [ContinuousLinearMap.coe_coe] at hdiff
      have h3 : b i z - b j 0 = (b j (c j y) - b j 0) - (b j (c j y) - b i z) := by abel
      have h2 : Q i (v y) (b i z - b j 0) = Q i (v y) (b j (c j y) - b j 0) := by
        rw [h3, map_sub, hdiff, sub_zero]
      rw [hTz, hQi, h2]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hsplit]
    have hinv : (T z).IsInvertible := ⟨e, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
    simp only [Φ, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rw [← hw, ContinuousLinearMap.IsInvertible.inverse_apply_self hinv]
  intro z hz
  obtain ⟨e, he, -⟩ := key z hz
  have hz' := hz
  rw [OpenPartialHomeomorph.trans_source] at hz'
  have hQ : ContDiffAt ℝ ∞ (fun z => Q i (b i z)) z :=
    (hsm i z hz'.1).comp z
      (b i).contDiff.contDiffAt
  have hT : ContDiffAt ℝ ∞ T z := hQ.clm_comp contDiffAt_const
  have hinv : ContDiffAt ℝ ∞ (fun z => (T z).inverse) z := by
    have := contDiffAt_map_inverse (n := ∞) e
    rw [he] at this
    exact this.comp z hT
  have hrhs : ContDiffAt ℝ ∞ (fun z => Q i (b i z) (b i z - b j 0)) z :=
    hQ.clm_apply (((b i).contDiff.contDiffAt).sub contDiffAt_const)
  have hΦ : ContDiffAt ℝ ∞ Φ z := hinv.clm_apply hrhs
  refine hΦ.contDiffWithinAt.congr (fun z' hz' => ?_) ?_
  · exact ((key z' hz').choose_spec.2).symm
  · exact ((key z hz).choose_spec.2).symm

end OMA.Helpers

end

open Geometry Set
open scoped ContDiff

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R2_H1_R1.H2 := by
  intro n
  dsimp only
  intro K
  try dsimp only
  intro hfin hpure he ht hv
  obtain ⟨m, L, hind, hL, ⟨e⟩⟩ :=
    OMA.CairnsAssembly.reembed n K ⟨hfin, hpure, he, ht, hv⟩
  have hfield :=
    OMA.CairnsPlaneField.main
      OMA.CairnsAssembly.contract OMA.CairnsAssembly.leaves
  have hcoords :=
    OMA.CairnsLeafCoordinates.main
      hfield OMA.CairnsAssembly.charts
  obtain ⟨c, P, b, Q, hcover, hsm, hlin⟩ := hcoords m L hind hL K.space e
  exact ⟨K.space, c, hcover, OMA.Helpers.transition_smooth c (fun y => (e y).val) P b Q hsm hlin⟩

