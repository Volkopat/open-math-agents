import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Subdivision source is adapted from DifferentialGeometry at
9f65eaf95b9ff5f1b39cfb2d2d24e51aed891568.

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


DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

The files under DifferentialGeometry/External/Schoenflies derive from
https://github.com/alonamaloh/schoenflies-lean
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License 2.0.
See that directory's LICENSE, MODIFICATIONS.md and provenance records.

The selected source under DifferentialGeometry/External/TauCeti derives from
https://github.com/TauCetiProject/TauCeti
revision 3358033ba2fd35f321356dceaf2372a0fd6c0bfd.
Copyright (c) 2026 Joseph Tooby-Smith and The Tau Ceti contributors.
Authors include Joseph Tooby-Smith, Codex and The Tau Ceti contributors,
as recorded in the preserved original source headers.
Released under the Apache License 2.0.
See that directory's LICENSE, SOURCE_MAP.json and MODIFICATIONS.md.
Native Sard, Morse, embedding and extension modules consume this external API.

The source under DifferentialGeometry/External/CanonicalTopology is restored
from the canonical-topology/Poincare project by Ayush Khaitan and its
contributors. See its pinned source archives, SOURCE_MAP.json, LICENSE
and MODIFICATIONS.md for exact revisions and declaration-level adaptations.
The derivative homotopy includes adapted source from plby/HopfProblem,
Solution.lean at 9ac8a456b526527837d7082ff775213ca8bc9809, lines 62156–62228,
under Apache-2.0; the nested attribution and license are preserved.

The source under DifferentialGeometry/External/ClassificationOfSurfaces
derives from https://github.com/mccorvie/classification-of-surfaces.
It includes work by the ClassificationOfSurfaces contributors, Steven Sivek
and Kai Lam, as recorded in the original source and nested provenance.
Released under the Apache License 2.0. See its LICENSE and MODIFICATIONS.md.

Additional MathDB preparation backports
--------------------------------------
The homotopy-sphere bridge added on this branch comes from DifferentialGeometry
v0.1.4, commit 788efe97894474c032de6dfb1289d515f613d15a.
Selected Mathlib compatibility files derive from mathlib4 commit
c55e6e786f49471c72fbddbec5415808896aec1e, under Apache-2.0. Original copyright
headers and contributor attribution are retained in those files. They have been
adapted to the pinned Lean/Mathlib v4.33.1 APIs. See MATHDB_SUBMISSION.md.

-/

/- Local integration check using Apache-2.0 sources at 9f65eaf95b9ff5f1b39cfb2d2d24e51aed891568. -/

/- DifferentialGeometry.Topology.Homology.Algebra.CokernelHomotopy -/
section

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k]
  {A K : ChainComplex (ModuleCat.{v} k) ℕ} (i : A ⟶ K)

def cokernelDescAt (n : ℕ) {M : ModuleCat.{v} k} (φ : K.X n ⟶ M) (hφ : (CategoryTheory.CategoryStruct.comp (i.f n) (φ)) = 0) :
    (cokernel i).X n ⟶ M :=
  (CategoryTheory.CategoryStruct.comp ((PreservesCokernel.iso (_root_.HomologicalComplex.eval _ _ n) i).hom) (cokernel.desc (i.f n) φ hφ))


@[simp]
theorem cokernel_π_descAt (n : ℕ) {M : ModuleCat.{v} k} (φ : K.X n ⟶ M) (hφ : (CategoryTheory.CategoryStruct.comp (i.f n) (φ)) = 0) :
    (CategoryTheory.CategoryStruct.comp ((cokernel.π i).f n) (cokernelDescAt i n φ hφ)) = φ := by
  exact (PreservesCokernel.π_iso_hom_assoc (_root_.HomologicalComplex.eval _ _ n) i
    (cokernel.desc ((_root_.HomologicalComplex.eval _ _ n).map i) φ hφ)).trans
      (cokernel.π_desc _ _ _)

variable (a : A ⟶ A) (b : K ⟶ K) (hab : (CategoryTheory.CategoryStruct.comp (i) (b)) = (CategoryTheory.CategoryStruct.comp (a) (i)))


def cokernelEndomorphism : cokernel i ⟶ cokernel i := cokernel.map i i a b hab


@[simp]
theorem cokernel_π_endomorphism :
    (CategoryTheory.CategoryStruct.comp (cokernel.π i) (cokernelEndomorphism i a b hab)) = (CategoryTheory.CategoryStruct.comp (b) (cokernel.π i)) :=
  cokernel.π_desc _ _ _

variable (H : Homotopy b (𝟙 K))
  (hA : ∀ n : ℕ, A.X n ⟶ A.X (n + 1))
  (hcompat : ∀ n, (CategoryTheory.CategoryStruct.comp (i.f n) (H.hom n (n + 1))) = (CategoryTheory.CategoryStruct.comp (hA n) (i.f (n + 1))))

include hcompat in
private theorem desc_condition (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (i.f n) (((CategoryTheory.CategoryStruct.comp (H.hom n (n + 1)) ((cokernel.π i).f (n + 1)))))) = 0 := by
  rw [← Category.assoc, hcompat, Category.assoc]
  have h := _root_.HomologicalComplex.congr_hom (cokernel.condition i) (n + 1)
  simp only [_root_.HomologicalComplex.comp_f, _root_.HomologicalComplex.zero_f_apply] at h
  rw [h, comp_zero]

private def descHom (n : ℕ) : (cokernel i).X n ⟶ (cokernel i).X (n + 1) :=
  cokernelDescAt i n ((CategoryTheory.CategoryStruct.comp (H.hom n (n + 1)) ((cokernel.π i).f (n + 1))))
    (desc_condition i b H hA hcompat n)

private theorem projection_descHom (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((cokernel.π i).f n) (descHom i b H hA hcompat n)) =
      (CategoryTheory.CategoryStruct.comp (H.hom n (n + 1)) ((cokernel.π i).f (n + 1))) :=
  cokernel_π_descAt _ _ _ _

def cokernelHomotopy : Homotopy (cokernelEndomorphism i a b hab) (𝟙 (cokernel i)) where
  hom n m := if h : n + 1 = m then
    (CategoryTheory.CategoryStruct.comp (descHom i b H hA hcompat n) (eqToHom (congrArg (cokernel i).X h))) else 0
  zero n m hnm := by
    change ¬ n + 1 = m at hnm
    exact dif_neg hnm
  comm n := by
    have hπ : (CategoryTheory.CategoryStruct.comp ((cokernel.π i).f n) ((cokernelEndomorphism i a b hab).f n)) =
        (CategoryTheory.CategoryStruct.comp (b.f n) ((cokernel.π i).f n)) :=
      _root_.HomologicalComplex.congr_hom (cokernel_π_endomorphism i a b hab) n
    have hh := H.comm n
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hh ⊢
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        _root_.HomologicalComplex.id_f, zero_add] at hh ⊢
      apply (cancel_epi ((cokernel.π i).f 0)).mp
      rw [hπ, Preadditive.comp_add, Category.comp_id, ← Category.assoc,
        projection_descHom, Category.assoc, (cokernel.π i).comm, ← Category.assoc]
      exact congrArg (fun f ↦ (CategoryTheory.CategoryStruct.comp (f) ((cokernel.π i).f 0))) hh |>.trans (by simp)
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hh ⊢
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        _root_.HomologicalComplex.id_f] at hh ⊢
      apply (cancel_epi ((cokernel.π i).f (n + 1))).mp
      rw [hπ]
      simp only [Preadditive.comp_add, Category.comp_id]
      rw [← Category.assoc ((cokernel.π i).f (n + 1)), (cokernel.π i).comm]
      rw [Category.assoc, projection_descHom]
      rw [← Category.assoc ((cokernel.π i).f (n + 1)), projection_descHom,
        Category.assoc, (cokernel.π i).comm]
      simpa only [Preadditive.add_comp, Category.assoc, Category.id_comp] using
        congrArg (fun f ↦ (CategoryTheory.CategoryStruct.comp (f) ((cokernel.π i).f (n + 1)))) hh

end DifferentialGeometry.HomologicalComplex
end
end


/- DifferentialGeometry.Topology.Homology.Algebra.LocallyNilpotent -/
section

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k] {ι : Type*} {c : ComplexShape ι}
  (K : _root_.HomologicalComplex (ModuleCat.{v} k) c) (B : End K)


theorem homologyMap_pow_eq_id (H : Homotopy B (𝟙 K)) (N : ℕ) (n : ι) :
    _root_.HomologicalComplex.homologyMap (B ^ N) n = 𝟙 _ := by
  have hB : _root_.HomologicalComplex.homologyMap B n = 𝟙 _ :=
    (H.homologyMap_eq n).trans (_root_.HomologicalComplex.homologyMap_id K n)
  induction N with
  | zero => exact _root_.HomologicalComplex.homologyMap_id K n
  | succ N hN =>
    rw [pow_succ, End.mul_def, _root_.HomologicalComplex.homologyMap_comp, hN, hB,
      Category.id_comp]

theorem isZero_homology_of_locallyNilpotent (H : Homotopy B (𝟙 K))
    (hnil : ∀ n : ι, ∀ x : K.X n, ∃ N : ℕ, ((B ^ N).f n) x = 0) (n : ι) :
    IsZero (K.homology n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance a
  obtain ⟨N, hN⟩ := hnil n ((K.iCycles n) z)
  have hz : (_root_.HomologicalComplex.cyclesMap (B ^ N) n) z = 0 := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have hh := ConcreteCategory.congr_hom (_root_.HomologicalComplex.cyclesMap_i (B ^ N) n) z
    change (K.iCycles n) ((_root_.HomologicalComplex.cyclesMap (B ^ N) n) z) =
      ((B ^ N).f n) ((K.iCycles n) z) at hh
    simpa only [map_zero] using hh.trans hN
  have hh := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.homologyπ_naturality (B ^ N) n) z
  rw [homologyMap_pow_eq_id K B H N n] at hh
  change (K.homologyπ n) z =
    (K.homologyπ n) ((_root_.HomologicalComplex.cyclesMap (B ^ N) n) z) at hh
  rw [hz, map_zero] at hh
  exact hh

end DifferentialGeometry.HomologicalComplex
end
end


/- DifferentialGeometry.Topology.Homology.Algebra.EventualImage -/
section

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k]
  {A K : ChainComplex (ModuleCat.{v} k) ℕ} (i : A ⟶ K)


theorem quasiIso_of_isZero_cokernel_homology [Mono i]
    (hQ : ∀ n, IsZero ((cokernel i).homology n)) :
    _root_.QuasiIso i := by
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
    mono_f := inferInstanceAs (Mono i)
    epi_g := inferInstanceAs (Epi (cokernel.π i)) }
  rw [_root_.quasiIso_iff]
  intro n
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (_root_.HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₁ (n + 1) n rfl).mono_g ((hQ (n + 1)).eq_zero_of_src _)
  have : Epi (_root_.HomologicalComplex.homologyMap i n) :=
    (hS.homology_exact₂ n).epi_f ((hQ n).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

variable (a : A ⟶ A) (b : End K) (hab : (CategoryTheory.CategoryStruct.comp (i) (b)) = (CategoryTheory.CategoryStruct.comp (a) (i)))


theorem cokernel_π_endomorphism_pow (N : ℕ) :
    (CategoryTheory.CategoryStruct.comp (cokernel.π i) ((End.of (cokernelEndomorphism i a b hab) ^ N))) =
      (CategoryTheory.CategoryStruct.comp ((b ^ N)) (cokernel.π i)) := by
  induction N with
  | zero => simp
  | succ N hN =>
    rw [pow_succ, End.mul_def, ← Category.assoc, cokernel_π_endomorphism,
      Category.assoc, hN, ← Category.assoc, ← End.mul_def, ← pow_succ]

theorem cokernelEndomorphism_locallyNilpotent
    (henter : ∀ n, ∀ x : K.X n, ∃ N : ℕ,
      ((b ^ N).f n) x ∈ LinearMap.range (i.f n).hom) :
    ∀ n, ∀ x : (cokernel i).X n, ∃ N : ℕ,
      ((End.of (cokernelEndomorphism i a b hab) ^ N).f n) x = 0 := by
  intro n x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective ((cokernel.π i).f n)).mp inferInstance x
  obtain ⟨N, z, hz⟩ := henter n y
  refine ⟨N, ?_⟩
  have hh := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.congr_hom (cokernel_π_endomorphism_pow i a b hab N) n) y
  change ((End.of (cokernelEndomorphism i a b hab) ^ N).f n) ((cokernel.π i).f n y) =
    (cokernel.π i).f n (((b ^ N).f n) y) at hh
  rw [← hz] at hh
  have hz0 := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.congr_hom (cokernel.condition i) n) z
  exact hh.trans hz0

include hab in
theorem quasiIso_of_eventually_in_image [Mono i]
    (H : Homotopy b (𝟙 K)) (hA : ∀ n : ℕ, A.X n ⟶ A.X (n + 1))
    (hcompat : ∀ n, (CategoryTheory.CategoryStruct.comp (i.f n) (H.hom n (n + 1))) = (CategoryTheory.CategoryStruct.comp (hA n) (i.f (n + 1))))
    (henter : ∀ n, ∀ x : K.X n, ∃ N : ℕ,
      ((b ^ N).f n) x ∈ LinearMap.range (i.f n).hom) :
    _root_.QuasiIso i := by
  apply quasiIso_of_isZero_cokernel_homology i
  exact isZero_homology_of_locallyNilpotent (cokernel i)
    (End.of (cokernelEndomorphism i a b hab)) (cokernelHomotopy i a b hab H hA hcompat)
    (cokernelEndomorphism_locallyNilpotent i a b hab henter)

end DifferentialGeometry.HomologicalComplex
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.AffineSimplex -/
section

noncomputable section

open CategoryTheory Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def affineSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    C(stdSimplex ℝ (Fin (n + 1)), E) where
  toFun x := ∑ i, x i • v i
  continuous_toFun := continuous_finsetSum _ (fun i _ ↦
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)


@[simp]
theorem affineSimplex_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    affineSimplex v (stdSimplex.vertex i) = v i := by
  simp [affineSimplex, Pi.single_apply]

theorem affineSimplex_comp_map {n m : ℕ} (v : Fin (n + 1) → E)
    (f : Fin (m + 1) → Fin (n + 1)) :
    (affineSimplex v).comp ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ =
      affineSimplex (v ∘ f) := by
  ext x
  change ∑ j, (FunOnFinite.linearMap ℝ ℝ f x.val) j • v j = ∑ i, x i • v (f i)
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  calc
    _ = ∑ j, ∑ i ∈ Finset.univ with f i = j, x i • v (f i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
      rfl
    _ = _ := Finset.sum_fiberwise Finset.univ f _


theorem range_affineSimplex_subset {n : ℕ} (v : Fin (n + 1) → E) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s) : Set.range (affineSimplex v) ⊆ s := by
  rintro _ ⟨x, rfl⟩
  exact hs.sum_mem (fun i _ ↦ x.property.1 i) x.property.2 (fun i _ ↦ hv i)


def affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    TopCat.toSSet.obj (TopCat.of E) _⦋n⦌ :=
  ((TopCat.of E).toSSetObjEquiv (op ⦋n⦌)).symm (affineSimplex v)


def singularSimplexVertices {n : ℕ} (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    Fin (n + 1) → E :=
  fun i ↦ (TopCat.of E).toSSetObjEquiv (op ⦋n⦌) σ (stdSimplex.vertex i)


@[simp]
theorem singularSimplexVertices_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    singularSimplexVertices (affineSingularSimplex v) = v := by
  funext i
  exact affineSimplex_vertex v i

omit [NormedSpace ℝ E] in
theorem singularSimplexVertices_map {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).map f.op σ) =
      singularSimplexVertices σ ∘ f := by
  funext i
  change (TopCat.of E).toSSetObjEquiv (op ⦋n⦌) σ
      (stdSimplex.map f (stdSimplex.vertex i)) = _
  rw [stdSimplex.map_vertex]
  rfl

omit [NormedSpace ℝ E] in
@[simp]
theorem singularSimplexVertices_δ {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) (i : Fin (n + 2)) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).δ i σ) =
      singularSimplexVertices σ ∘ i.succAbove :=
  singularSimplexVertices_map (SimplexCategory.δ i) σ


theorem map_affineSingularSimplex {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (v : Fin (n + 1) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).map f.op (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ f) := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋m⦌)).injective
  change (affineSimplex v).comp
    ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ = affineSimplex (v ∘ f)
  exact affineSimplex_comp_map v f

def affineStraightening : TopCat.toSSet.obj (TopCat.of E) ⟶ TopCat.toSSet.obj (TopCat.of E) where
  app n := ↾fun σ ↦ affineSingularSimplex (n := n.unop.len) (singularSimplexVertices σ)
  naturality n m f := by
    ext σ
    change affineSingularSimplex (singularSimplexVertices
      ((TopCat.toSSet.obj (TopCat.of E)).map f σ)) =
        (TopCat.toSSet.obj (TopCat.of E)).map f
          (affineSingularSimplex (singularSimplexVertices σ))
    exact (congrArg affineSingularSimplex (singularSimplexVertices_map f.unop σ)).trans
      (map_affineSingularSimplex f.unop (singularSimplexVertices σ)).symm


@[simp]
theorem affineStraightening_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    (affineStraightening (E := E)).app (op ⦋n⦌) (affineSingularSimplex v) =
      affineSingularSimplex v := by
  change affineSingularSimplex (singularSimplexVertices (affineSingularSimplex v)) = _
  rw [singularSimplexVertices_affineSingularSimplex]


theorem affineSingularSimplex_vertices_zero (σ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌) :
    affineSingularSimplex (singularSimplexVertices σ) = σ := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋0⦌)).injective
  ext x
  obtain rfl := Subsingleton.elim x (stdSimplex.vertex (0 : Fin 1))
  exact affineSimplex_vertex _ 0


@[simp]
theorem δ_affineSingularSimplex {n : ℕ} (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ i.succAbove) := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋n⦌)).injective
  change (affineSimplex v).comp
    ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩ =
      affineSimplex (v ∘ i.succAbove)
  exact affineSimplex_comp_map v i.succAbove


end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Cone -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem affineCone_boundary_generator {n : ℕ} (p : E) (v : Fin (n + 2) → E) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p v))) (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1))) =
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) -
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
          (affineSingularSimplex (Fin.cons p (v ∘ i.succAbove))) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_succ]
  simp only [δ_affineSingularSimplex, Fin.val_zero, pow_zero, one_zsmul,
    Fin.succAbove_zero, Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove,
    Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  rfl


theorem affineCone_boundary_generator_zero (p q : E) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p (fun _ : Fin 1 ↦ q)))) (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0)) =
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (fun _ : Fin 1 ↦ q)) -
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (fun _ : Fin 1 ↦ p)) := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [δ_affineSingularSimplex]
  have h₀ : Fin.cons p (fun _ : Fin 1 ↦ q) ∘ (0 : Fin 2).succAbove =
      (fun _ : Fin 1 ↦ q) := rfl
  have h₁ : Fin.cons p (fun _ : Fin 1 ↦ q) ∘ (1 : Fin 2).succAbove =
      (fun _ : Fin 1 ↦ p) := by
    funext i
    fin_cases i
    rfl
  rw [h₀, h₁]
  simp [sub_eq_add_neg]

def affineCone (p : E) (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X (n + 1) :=
  Sigma.desc (fun σ ↦ (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
    (affineSingularSimplex (Fin.cons p (singularSimplexVertices σ))))


@[simp]
theorem ι_affineCone (p : E) {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (affineCone R p n)) =
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
        (affineSingularSimplex (Fin.cons p (singularSimplexVertices σ))) :=
  Sigma.ι_desc _ _

theorem affineCone_boundary (p : E) (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineCone R p (n + 1)) (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1))) +
      (CategoryTheory.CategoryStruct.comp (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n) (affineCone R p n)) =
        (SSet.chainComplexMap (affineStraightening (E := E)) R).f (n + 1) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Preadditive.comp_add, ← Category.assoc, ι_affineCone,
    affineCone_boundary_generator, ← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ι_affineCone,
    SSet.ι_chainComplexMap_f, singularSimplexVertices_δ]
  apply sub_add_cancel


def singularChainAugmentation :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X 0 ⟶ R :=
  Sigma.desc (fun _ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌ ↦ 𝟙 R)

omit [NormedSpace ℝ E] in
@[simp]
theorem ι_singularChainAugmentation (σ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (singularChainAugmentation (E := E) R)) = 𝟙 R :=
  Sigma.ι_desc _ _

omit [NormedSpace ℝ E] in
theorem d_singularChainAugmentation :
    (CategoryTheory.CategoryStruct.comp (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0) (singularChainAugmentation (E := E) R)) = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp only [Preadditive.add_comp, Preadditive.neg_comp,
    ι_singularChainAugmentation, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, add_neg_cancel, comp_zero]


theorem affineCone_boundary_zero (p : E) :
    (CategoryTheory.CategoryStruct.comp (affineCone R p 0) (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d 1 0)) =
      𝟙 _ - (CategoryTheory.CategoryStruct.comp (singularChainAugmentation (E := E) R) ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
            (affineSingularSimplex (fun _ : Fin 1 ↦ p)))) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, Preadditive.comp_sub, Category.comp_id]
  have hσ : singularSimplexVertices σ = (fun _ : Fin 1 ↦ singularSimplexVertices σ 0) := by
    funext i
    fin_cases i
    rfl
  rw [hσ, affineCone_boundary_generator_zero]
  have hpoint : affineSingularSimplex (fun _ : Fin 1 ↦ singularSimplexVertices σ 0) = σ := by
    rw [← hσ]
    exact affineSingularSimplex_vertices_zero σ
  rw [hpoint]
  rw [← Category.assoc, ι_singularChainAugmentation, Category.id_comp]


theorem affineStraightening_f_zero :
    (SSet.chainComplexMap (affineStraightening (E := E)) R).f 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [SSet.ι_chainComplexMap_f, Category.comp_id]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      (affineSingularSimplex (singularSimplexVertices σ)) = _
  rw [affineSingularSimplex_vertices_zero]


theorem affineCone_straightening (p : E) (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineCone R p n) ((SSet.chainComplexMap (affineStraightening (E := E)) R).f (n + 1))) =
      affineCone R p n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, SSet.ι_chainComplexMap_f,
    affineStraightening_affineSingularSimplex]


end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Barycentric -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def singularSimplexBarycenter {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) : E :=
  Finset.univ.centerMass (fun _ : Fin (n + 1) ↦ (1 : ℝ)) (singularSimplexVertices σ)


theorem singularSimplexBarycenter_mem {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, singularSimplexVertices σ i ∈ s) :
    singularSimplexBarycenter σ ∈ s :=
  hs.centerMass_mem (fun _ _ ↦ zero_le_one)
    (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))
    (fun i _ ↦ hv i)

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def affineSubdivisionMap (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => Sigma.desc (fun σ ↦
      (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n) ((CategoryTheory.CategoryStruct.comp (affineSubdivisionMap n) (affineCone R (singularSimplexBarycenter σ) n)))))))


@[simp]
theorem affineSubdivisionMap_zero : affineSubdivisionMap (E := E) R 0 = 𝟙 _ := rfl


theorem ι_affineSubdivisionMap_succ (n : ℕ)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (affineSubdivisionMap R (n + 1))) =
      (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n) ((CategoryTheory.CategoryStruct.comp (affineSubdivisionMap R n) (affineCone R (singularSimplexBarycenter σ) n)))))) :=
  Sigma.ι_desc _ _


theorem affineSubdivisionMap_straightening (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineSubdivisionMap (E := E) R n) ((SSet.chainComplexMap (affineStraightening (E := E)) R).f n)) =
        affineSubdivisionMap R n := by
  cases n with
  | zero => rw [affineSubdivisionMap_zero, affineStraightening_f_zero, Category.id_comp]
  | succ n =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc, affineCone_straightening]


theorem affineSubdivisionMap_comm (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineSubdivisionMap (E := E) R (n + 1)) (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n)) =
      (CategoryTheory.CategoryStruct.comp (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n) (affineSubdivisionMap R n)) := by
  induction n with
  | zero =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [affineSubdivisionMap_zero, Category.id_comp, Category.comp_id, Category.assoc]
    rw [affineCone_boundary_zero]
    simp only [Preadditive.comp_sub, Category.comp_id]
    rw [← Category.assoc _ (singularChainAugmentation (E := E) R),
      d_singularChainAugmentation, zero_comp, comp_zero, sub_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [eq_sub_of_add_eq (affineCone_boundary R (singularSimplexBarycenter σ) n)]
    simp only [Preadditive.comp_sub, affineSubdivisionMap_straightening]
    rw [← Category.assoc (affineSubdivisionMap R (n + 1)), hn]
    simp only [Category.assoc]
    rw [← Category.assoc
      (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1))]
    simp only [HomologicalComplex.d_comp_d, zero_comp, comp_zero, sub_zero]

def affineSubdivision :
    (TopCat.toSSet.obj (TopCat.of E)).chainComplex R ⟶
      (TopCat.toSSet.obj (TopCat.of E)).chainComplex R where
  f := affineSubdivisionMap R
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact affineSubdivisionMap_comm R j


@[simp]
theorem affineSubdivision_f (n : ℕ) :
    (affineSubdivision (E := E) R).f n = affineSubdivisionMap R n := rfl


end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Homotopy -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


private theorem straightening_f_idempotent (n : ℕ) : (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexMap (affineStraightening (E := E)) R)).f n) (((SSet.chainComplexMap (affineStraightening (E := E)) R)).f n)) = ((SSet.chainComplexMap (affineStraightening (E := E)) R)).f n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      ((affineStraightening (E := E)).app (op ⦋n⦌)
        (affineSingularSimplex (singularSimplexVertices σ))) = _
  rw [affineStraightening_affineSingularSimplex]
  rfl

private theorem difference_f_straightening (n : ℕ) : (CategoryTheory.CategoryStruct.comp (((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f n) (((SSet.chainComplexMap (affineStraightening (E := E)) R)).f n)) = ((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f n := by
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, affineSubdivision_f,
    affineSubdivisionMap_straightening, straightening_f_idempotent]

private theorem difference_f_zero : ((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f 0 = 0 := by
  rw [HomologicalComplex.sub_f_apply, affineSubdivision_f, affineSubdivisionMap_zero,
    affineStraightening_f_zero, sub_self]


theorem affineCone_fills_cycle (p : E) {n : ℕ} {T : ModuleCat.{u} k}
    (z : T ⟶ ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X (n + 1)) (hz : (CategoryTheory.CategoryStruct.comp (z) (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n)) = 0)
    (haff : (CategoryTheory.CategoryStruct.comp (z) (((SSet.chainComplexMap (affineStraightening (E := E)) R)).f (n + 1))) = z) :
    (CategoryTheory.CategoryStruct.comp (z) ((CategoryTheory.CategoryStruct.comp (affineCone R p (n + 1)) (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 2) (n + 1))))) = z := by
  rw [eq_sub_of_add_eq (affineCone_boundary R p n), Preadditive.comp_sub, haff,
    ← Category.assoc, hz, zero_comp, sub_zero]


def affineSubdivisionHomotopyMap (n : ℕ) : ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X n ⟶ ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => Sigma.desc (fun σ ↦
      (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f (n + 1))) -
        (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap n)))))) (affineCone R (singularSimplexBarycenter σ) (n + 1))))


@[simp]
theorem affineSubdivisionHomotopyMap_zero : affineSubdivisionHomotopyMap (E := E) R 0 = 0 := rfl


theorem ι_affineSubdivisionHomotopyMap_succ (n : ℕ)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (affineSubdivisionHomotopyMap R (n + 1))) =
      (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f (n + 1))) -
        (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n)))))) (affineCone R (singularSimplexBarycenter σ) (n + 1))) :=
  Sigma.ι_desc _ _


theorem affineSubdivisionHomotopyMap_straightening (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineSubdivisionHomotopyMap (E := E) R n) (((SSet.chainComplexMap (affineStraightening (E := E)) R)).f (n + 1))) =
      affineSubdivisionHomotopyMap R n := by
  cases n with
  | zero => rw [affineSubdivisionHomotopyMap_zero, zero_comp]
  | succ n =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionHomotopyMap_succ]
    simp only [Category.assoc, affineCone_straightening]

private def homotopyPrev (n : ℕ) : ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X n ⟶ ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X n :=
  match n with
  | 0 => 0
  | n + 1 => (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n))

private theorem d_homotopyPrev (n : ℕ) : (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (homotopyPrev R n)) = 0 := by
  cases n with
  | zero => exact comp_zero
  | succ n =>
    change (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 2) (n + 1)) (((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n))))) = 0
    rw [← Category.assoc, ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d_comp_d, zero_comp]

private theorem affineSubdivisionHomotopyMap_comm_aux (n : ℕ) :
    ((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f n = homotopyPrev R n +
      (CategoryTheory.CategoryStruct.comp (affineSubdivisionHomotopyMap R n) (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n)) := by
  induction n with
  | zero => simp only [homotopyPrev, affineSubdivisionHomotopyMap_zero,
      difference_f_zero, zero_comp, add_zero]
  | succ n hn =>
    change ((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f (n + 1) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n)) +
      (CategoryTheory.CategoryStruct.comp (affineSubdivisionHomotopyMap R (n + 1)) (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 2) (n + 1)))
    apply SSet.chainComplex_hom_ext
    intro σ
    simp only [Preadditive.comp_add]
    rw [← Category.assoc _ (affineSubdivisionHomotopyMap R (n + 1)),
      ι_affineSubdivisionHomotopyMap_succ, Category.assoc]
    let z : R ⟶ ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X (n + 1) :=
      (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f (n + 1))) -
        (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n))))
    have hza : (CategoryTheory.CategoryStruct.comp (z) (((SSet.chainComplexMap (affineStraightening (E := E)) R)).f (n + 1))) = z := by
      dsimp only [z]
      simp only [Preadditive.sub_comp, Category.assoc, difference_f_straightening,
        affineSubdivisionHomotopyMap_straightening]
    have hzc : (CategoryTheory.CategoryStruct.comp (z) (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n)) = 0 := by
      dsimp only [z]
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).comm, hn]
      simp only [Preadditive.comp_add]
      rw [d_homotopyPrev]
      simp only [comp_zero, zero_add, sub_self]
    rw [affineCone_fills_cycle R (singularSimplexBarycenter σ) z hzc hza]
    dsimp only [z]
    abel


theorem affineSubdivisionHomotopyMap_comm (n : ℕ) :
    ((((affineSubdivision (E := E) R) - (SSet.chainComplexMap (affineStraightening (E := E)) R)))).f (n + 1) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n)) +
      (CategoryTheory.CategoryStruct.comp (affineSubdivisionHomotopyMap R (n + 1)) (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 2) (n + 1))) :=
  affineSubdivisionHomotopyMap_comm_aux R (n + 1)

def affineSubdivisionHomotopy : Homotopy ((affineSubdivision (E := E) R)) ((SSet.chainComplexMap (affineStraightening (E := E)) R)) where
  hom i j := if h : i + 1 = j then
    (CategoryTheory.CategoryStruct.comp (affineSubdivisionHomotopyMap R i) (eqToHom (congrArg ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X h))) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dif_neg hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        affineSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        affineSubdivision_f, affineSubdivisionMap_zero, affineStraightening_f_zero]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id]
      exact sub_eq_iff_eq_add.mp (affineSubdivisionHomotopyMap_comm R n)


@[simp]
theorem affineSubdivisionHomotopy_hom (n : ℕ) :
    (affineSubdivisionHomotopy (E := E) R).hom n (n + 1) =
      affineSubdivisionHomotopyMap R n := by
  change (if h : n + 1 = n + 1 then
    (CategoryTheory.CategoryStruct.comp (affineSubdivisionHomotopyMap R n) (eqToHom (congrArg ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X h))) else 0) = _
  rw [dif_pos rfl, eqToHom_refl, Category.comp_id]

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.SmallChains -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe u v w

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)


def smallSingularSimplices : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i}
  map f σ h := by
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨stdSimplex.map f.unop z, rfl⟩


theorem smallSingularSimplices_le {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularSimplices X U ≤ smallSingularSimplices X V := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨j, hj⟩ := hUV i
  exact ⟨j, hi.trans hj⟩


variable {X U} {Y : TopCat.{u}} {κ : Type w} {V : κ → Set Y}


def smallSingularSimplicesMap (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    (smallSingularSimplices X U : SSet) ⟶ smallSingularSimplices Y V where
  app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map f).app n σ.val, by
    obtain ⟨i, hi⟩ := σ.property
    obtain ⟨j, hj⟩ := hf i
    refine ⟨j, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hj (hi ⟨z, rfl⟩)⟩
  naturality _ _ _ := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map f).naturality _) σ.val


@[simp]
theorem smallSingularSimplicesMap_ι (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    (CategoryTheory.CategoryStruct.comp (smallSingularSimplicesMap f hf) ((smallSingularSimplices Y V).ι)) =
      (CategoryTheory.CategoryStruct.comp ((smallSingularSimplices X U).ι) (TopCat.toSSet.map f)) := rfl

variable (X U) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def smallChainMap :
    (smallSingularSimplices X U : SSet).chainComplex R ⟶
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X :=
  SSet.chainComplexMap (smallSingularSimplices X U).ι R


@[simp]
theorem ι_smallChainMap_f {n : ℕ}
    (σ : (smallSingularSimplices X U : SSet) _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp ((smallSingularSimplices X U : SSet).ιChainComplex σ) ((smallChainMap X U R).f n)) =
      (TopCat.toSSet.obj X).ιChainComplex σ.val :=
  SSet.ι_chainComplexMap_f _ _ _ R σ

private def smallChainProjection (n : ℕ) :
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X).X n ⟶
      ((smallSingularSimplices X U : SSet).chainComplex R).X n := by
  classical
  exact Sigma.desc (fun σ ↦ if hσ : σ ∈ (smallSingularSimplices X U).obj (op ⦋n⦌)
    then (smallSingularSimplices X U : SSet).ιChainComplex ⟨σ, hσ⟩ else 0)

private theorem smallChainMap_projection (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((smallChainMap X U R).f n) (smallChainProjection X U R n)) = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallChainMap_f]
  change (CategoryTheory.CategoryStruct.comp (Sigma.ι _ σ.val) (Sigma.desc _)) = _
  rw [Sigma.ι_desc]
  simp only [dif_pos σ.property, Category.comp_id]
  rfl


theorem mono_smallChainMap_f (n : ℕ) : Mono ((smallChainMap X U R).f n) := by
  have : IsSplitMono ((smallChainMap X U R).f n) :=
    IsSplitMono.mk' ⟨smallChainProjection X U R n, smallChainMap_projection X U R n⟩
  infer_instance


theorem mono_smallChainMap : Mono (smallChainMap X U R) :=
  HomologicalComplex.mono_of_mono_f _ (mono_smallChainMap_f X U R)


def smallChainRefinement {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    (smallSingularSimplices X U : SSet).chainComplex R ⟶
      (smallSingularSimplices X V : SSet).chainComplex R :=
  SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (smallSingularSimplices_le X U V hUV)) R


@[simp]
theorem smallChainRefinement_smallChainMap {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    (CategoryTheory.CategoryStruct.comp (smallChainRefinement X U R V hUV) (smallChainMap X V R)) = smallChainMap X U R := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) = _
  rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  rfl

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Support -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} (hs : Convex ℝ s)


omit [NormedSpace ℝ E] in
private theorem small_vertices_mem {n : ℕ} (σ : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n⦌) (i : Fin (n + 1)) :
    singularSimplexVertices σ.val i ∈ s := by
  obtain ⟨_, hσ⟩ := σ.property
  exact hσ ⟨stdSimplex.vertex i, rfl⟩


def smallBarycenter {n : ℕ} (σ : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n⦌) : s :=
  ⟨singularSimplexBarycenter σ.val,
    singularSimplexBarycenter_mem _ hs (small_vertices_mem σ)⟩


def smallAffineSimplex {n : ℕ} (σ : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n⦌) : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n⦌ :=
  ⟨affineSingularSimplex (singularSimplexVertices σ.val), by
    refine ⟨(), ?_⟩
    exact range_affineSimplex_subset _ hs (small_vertices_mem σ)⟩


def smallConeSimplex (p : s) {n : ℕ} (σ : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n⦌) :
    ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n + 1⦌ :=
  ⟨affineSingularSimplex (Fin.cons (p : E) (singularSimplexVertices σ.val)), by
    refine ⟨(), ?_⟩
    exact range_affineSimplex_subset _ hs (Fin.cases p.property (small_vertices_mem σ))⟩


def smallAffineStraightening : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) ⟶ ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) :=
  SSet.Subcomplex.lift ((CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s))).ι) (affineStraightening))) (by
    intro n τ hτ
    obtain ⟨σ, rfl⟩ := hτ
    exact (smallAffineSimplex hs (n := n.unop.len) σ).property)


theorem smallAffineStraightening_ι :
    (CategoryTheory.CategoryStruct.comp (smallAffineStraightening hs) (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s))).ι)) = (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s))).ι) (affineStraightening)) := rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)



theorem smallAffineStraightening_inclusion : (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (smallAffineStraightening hs) R))) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)))) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R))) (((_root_.SSet.chainComplexMap (affineStraightening (E := E)) R)))) := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _))
  rw [← Functor.map_comp, ← Functor.map_comp, smallAffineStraightening_ι]


def smallAffineCone (p : s) (n : ℕ) : ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X n ⟶ ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X (n + 1) :=
  Sigma.desc (fun σ ↦ ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex (smallConeSimplex hs p σ))


theorem ι_smallAffineCone (p : s) {n : ℕ} (σ : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) (smallAffineCone hs R p n)) =
      ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex (smallConeSimplex hs p σ) :=
  Sigma.ι_desc _ _


theorem smallAffineCone_inclusion (p : s) (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallAffineCone hs R p n) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1))) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n) (affineCone R (p : E) n)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallAffineCone, SSet.ι_chainComplexMap_f,
    ← Category.assoc, SSet.ι_chainComplexMap_f, ι_affineCone]
  rfl


def smallAffineSubdivisionMap (n : ℕ) : ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X n ⟶ ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => Sigma.desc (fun σ ↦ (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n) ((CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionMap n) (smallAffineCone hs R (smallBarycenter hs σ) n)))))))


@[simp]
theorem smallAffineSubdivisionMap_zero : smallAffineSubdivisionMap hs R 0 = 𝟙 _ := rfl


theorem ι_smallAffineSubdivisionMap_succ (n : ℕ) (σ : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n + 1⦌) :
    (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) (smallAffineSubdivisionMap hs R (n + 1))) =
      (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n) ((CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionMap hs R n) (smallAffineCone hs R (smallBarycenter hs σ) n)))))) :=
  Sigma.ι_desc _ _


theorem smallAffineSubdivisionMap_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionMap hs R n) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n)) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n) (affineSubdivisionMap R n)) := by
  induction n with
  | zero => rw [smallAffineSubdivisionMap_zero, affineSubdivisionMap_zero,
      Category.id_comp, Category.comp_id]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_smallAffineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [smallAffineCone_inclusion]
    rw [← Category.assoc (smallAffineSubdivisionMap hs R n), hn]
    simp only [Category.assoc]
    rw [← Category.assoc (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).comm]
    simp only [Category.assoc]
    rw [← Category.assoc _ (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1)), SSet.ι_chainComplexMap_f]
    rw [← Category.assoc (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionMap_succ]
    rfl

private theorem smallDifference_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((smallAffineSubdivisionMap hs R n - ((_root_.SSet.chainComplexMap (smallAffineStraightening hs) R)).f n)) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n) ((affineSubdivision R - (_root_.SSet.chainComplexMap (affineStraightening (E := E)) R)).f n)) := by
  rw [Preadditive.sub_comp, smallAffineSubdivisionMap_inclusion]
  have h := HomologicalComplex.congr_hom (smallAffineStraightening_inclusion hs R) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, affineSubdivision_f]


def smallAffineSubdivisionHomotopyMap (n : ℕ) : ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X n ⟶ ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => Sigma.desc (fun σ ↦
      (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((smallAffineSubdivisionMap hs R (n + 1) - ((_root_.SSet.chainComplexMap (smallAffineStraightening hs) R)).f (n + 1)))) -
        (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n) (smallAffineSubdivisionHomotopyMap n)))))) (smallAffineCone hs R (smallBarycenter hs σ) (n + 1))))


@[simp]
theorem smallAffineSubdivisionHomotopyMap_zero :
    smallAffineSubdivisionHomotopyMap hs R 0 = 0 := rfl


theorem ι_smallAffineSubdivisionHomotopyMap_succ (n : ℕ) (σ : ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) _⦋n + 1⦌) :
    (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) (smallAffineSubdivisionHomotopyMap hs R (n + 1))) =
      (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((smallAffineSubdivisionMap hs R (n + 1) - ((_root_.SSet.chainComplexMap (smallAffineStraightening hs) R)).f (n + 1)))) -
        (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n) (smallAffineSubdivisionHomotopyMap hs R n)))))) (smallAffineCone hs R (smallBarycenter hs σ) (n + 1))) :=
  Sigma.ι_desc _ _

theorem smallAffineSubdivisionHomotopyMap_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionHomotopyMap hs R n) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1))) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n) (affineSubdivisionHomotopyMap R n)) := by
  induction n with
  | zero => rw [smallAffineSubdivisionHomotopyMap_zero, affineSubdivisionHomotopyMap_zero,
      zero_comp, comp_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    have hz :
        (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((smallAffineSubdivisionMap hs R (n + 1) - ((_root_.SSet.chainComplexMap (smallAffineStraightening hs) R)).f (n + 1)))) -
          (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n) (smallAffineSubdivisionHomotopyMap hs R n)))))) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1))) =
        (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ.val) ((affineSubdivision R - (_root_.SSet.chainComplexMap (affineStraightening (E := E)) R)).f (n + 1))) -
          (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ.val) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n)))) := by
      rw [Preadditive.sub_comp]
      simp only [Category.assoc]
      rw [smallDifference_inclusion, hn]
      rw [← Category.assoc (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).comm]
      simp only [Category.assoc]
      rw [← Category.assoc (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rw [← Category.assoc (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rfl
    rw [← Category.assoc, ι_smallAffineSubdivisionHomotopyMap_succ, Category.assoc,
      smallAffineCone_inclusion, ← Category.assoc, hz]
    rw [← Category.assoc (((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet).ιChainComplex σ) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionHomotopyMap_succ]
    rfl

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Naturality -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E E' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E →L[ℝ] E')



theorem affineSimplex_map_linear {n : ℕ} (v : Fin (n + 1) → E) :
    (⟨f, f.continuous⟩ : C(E, E')).comp (affineSimplex v) = affineSimplex (f ∘ v) := by
  ext x
  change f (∑ i, x i • v i) = ∑ i, x i • f (v i)
  simp only [map_sum, map_smul]


theorem map_affineSingularSimplex_linear {n : ℕ} (v : Fin (n + 1) → E) :
    ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))).app (op ⦋n⦌) (affineSingularSimplex v) = affineSingularSimplex (f ∘ v) := by
  apply ((TopCat.of E').toSSetObjEquiv (op ⦋n⦌)).injective
  exact affineSimplex_map_linear f v


theorem singularSimplexVertices_map_linear {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexVertices (((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))).app (op ⦋n⦌) σ) = f ∘ singularSimplexVertices σ := rfl


theorem singularSimplexBarycenter_map_linear {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexBarycenter (((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))).app (op ⦋n⦌) σ) = f (singularSimplexBarycenter σ) := by
  simp only [singularSimplexBarycenter, singularSimplexVertices_map_linear,
    Finset.centerMass, Function.comp_apply, map_smul, map_sum]


theorem affineStraightening_naturality_linear :
    (CategoryTheory.CategoryStruct.comp (((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))))) (affineStraightening (E := E'))) = (CategoryTheory.CategoryStruct.comp (affineStraightening (E := E)) (((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))))) := by
  ext n σ
  exact (congrArg affineSingularSimplex (singularSimplexVertices_map_linear f σ)).trans
    (map_affineSingularSimplex_linear f (singularSimplexVertices σ)).symm

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)



theorem affineStraightening_chain_naturality_linear : (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R))) (((_root_.SSet.chainComplexMap (affineStraightening (E := E')) R)))) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (affineStraightening (E := E)) R))) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)))) := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _))
  rw [← Functor.map_comp, ← Functor.map_comp, affineStraightening_naturality_linear]


theorem affineCone_naturality_linear (p : E) (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineCone R p n) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1))) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n) (affineCone R (f p) n)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_affineCone, SSet.ι_chainComplexMap_f,
    map_affineSingularSimplex_linear]
  rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n),
    SSet.ι_chainComplexMap_f, ι_affineCone, singularSimplexVertices_map_linear, Fin.comp_cons]


theorem affineSubdivisionMap_naturality_linear (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineSubdivisionMap (E := E) R n) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n) (affineSubdivisionMap (E := E') R n)) := by
  induction n with
  | zero => rw [affineSubdivisionMap_zero, affineSubdivisionMap_zero,
      Category.id_comp, Category.comp_id]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [affineCone_naturality_linear]
    rw [← Category.assoc (affineSubdivisionMap (E := E) R n), hn]
    simp only [Category.assoc]
    rw [← Category.assoc (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).comm]
    simp only [Category.assoc]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1)),
      SSet.ι_chainComplexMap_f]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionMap_succ, singularSimplexBarycenter_map_linear]


private theorem difference_naturality_linear (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((affineSubdivision (E := E) R - (_root_.SSet.chainComplexMap (affineStraightening (E := E)) R)).f n) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n) ((affineSubdivision (E := E') R - (_root_.SSet.chainComplexMap (affineStraightening (E := E')) R)).f n)) := by
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, affineSubdivision_f,
    affineSubdivisionMap_naturality_linear]
  have h := HomologicalComplex.congr_hom (affineStraightening_chain_naturality_linear f R) n
  simp only [HomologicalComplex.comp_f] at h
  rw [← h, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, affineSubdivision_f]


theorem affineSubdivisionHomotopyMap_naturality_linear (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (affineSubdivisionHomotopyMap (E := E) R n) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1))) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n) (affineSubdivisionHomotopyMap (E := E') R n)) := by
  induction n with
  | zero => rw [affineSubdivisionHomotopyMap_zero, affineSubdivisionHomotopyMap_zero,
      zero_comp, comp_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    have hz :
        (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((affineSubdivision (E := E) R - (_root_.SSet.chainComplexMap (affineStraightening (E := E)) R)).f (n + 1))) -
          (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n)))))) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1))) =
        (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E')).ιChainComplex (((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))).app (op ⦋n + 1⦌) σ)) ((affineSubdivision (E := E') R - (_root_.SSet.chainComplexMap (affineStraightening (E := E')) R)).f (n + 1))) -
          (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E')).ιChainComplex (((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))).app (op ⦋n + 1⦌) σ)) ((CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E')) R)).d (n + 1) n) (affineSubdivisionHomotopyMap R n)))) := by
      rw [Preadditive.sub_comp]
      simp only [Category.assoc]
      rw [difference_naturality_linear, hn]
      rw [← Category.assoc (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).comm]
      simp only [Category.assoc]
      rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1)),
        SSet.ι_chainComplexMap_f]
    rw [← Category.assoc, ι_affineSubdivisionHomotopyMap_succ, Category.assoc,
      affineCone_naturality_linear, ← Category.assoc, hz]
    rw [← Category.assoc ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionHomotopyMap_succ,
      singularSimplexBarycenter_map_linear]

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.SmallChains.Subspace -/
section

noncomputable section

open CategoryTheory Opposite Simplicial AlgebraicTopology

universe u

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) (s : Set X)



def singularSubspaceEquiv (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj (TopCat.of s)).obj n ≃ ((smallSingularSimplices X (fun _ : Unit ↦ s)) : SSet).obj n where
  toFun σ := ⟨((TopCat.toSSet.map (TopCat.ofHom
  (ContinuousMap.mk Subtype.val (continuous_subtype_val : Continuous (Subtype.val : s → X)))))).app n σ, by
    refine ⟨(), ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (((TopCat.of s).toSSetObjEquiv n) σ z).property⟩
  invFun σ := ((TopCat.of s).toSSetObjEquiv n).symm
    ⟨fun z ↦ ⟨X.toSSetObjEquiv n σ.val z, σ.property.choose_spec ⟨z, rfl⟩⟩,
      (X.toSSetObjEquiv n σ.val).continuous.subtype_mk _⟩
  left_inv σ := by
    apply ((TopCat.of s).toSSetObjEquiv n).injective
    ext z
    rfl
  right_inv σ := by
    apply Subtype.ext
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl


def singularSubspaceIso : TopCat.toSSet.obj (TopCat.of s) ≅ ((smallSingularSimplices X (fun _ : Unit ↦ s)) : SSet) :=
  NatIso.ofComponents (fun n ↦ (singularSubspaceEquiv X s n).toIso) (by
    intro n m f
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (((TopCat.toSSet.map (TopCat.ofHom
  (ContinuousMap.mk Subtype.val (continuous_subtype_val : Continuous (Subtype.val : s → X)))))).naturality f) σ)


@[simp]
theorem singularSubspaceIso_hom_ι :
    (CategoryTheory.CategoryStruct.comp ((singularSubspaceIso X s).hom) (((smallSingularSimplices X (fun _ : Unit ↦ s))).ι)) = ((TopCat.toSSet.map (TopCat.ofHom
  (ContinuousMap.mk Subtype.val (continuous_subtype_val : Continuous (Subtype.val : s → X)))))) := rfl


@[simp]
theorem singularSubspaceIso_inv_inclusion :
    (CategoryTheory.CategoryStruct.comp ((singularSubspaceIso X s).inv) (((TopCat.toSSet.map (TopCat.ofHom
  (ContinuousMap.mk Subtype.val (continuous_subtype_val : Continuous (Subtype.val : s → X)))))))) = ((smallSingularSimplices X (fun _ : Unit ↦ s))).ι := by
  rw [← singularSubspaceIso_hom_ι X s, Iso.inv_hom_id_assoc]

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def singularSubspaceChainIso :
    (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (TopCat.of s)) ≅
      ((smallSingularSimplices X (fun _ : Unit ↦ s)) : SSet).chainComplex R :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso (singularSubspaceIso X s)


@[simp]
theorem singularSubspaceChainIso_hom_inclusion :
    (CategoryTheory.CategoryStruct.comp ((singularSubspaceChainIso X s R).hom) (smallChainMap X (fun _ : Unit ↦ s) R)) =
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, singularSubspaceIso_hom_ι]


@[simp]
theorem singularSubspaceChainIso_inv_inclusion :
    (CategoryTheory.CategoryStruct.comp ((singularSubspaceChainIso X s R).inv) (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))))) =
      smallChainMap X (fun _ : Unit ↦ s) R := by
  rw [← singularSubspaceChainIso_hom_inclusion X s R, Iso.inv_hom_id_assoc]

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Restriction -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} (hs : Convex ℝ s) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


private theorem smallSubdivision_comm (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionMap hs R (n + 1)) (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n) (smallAffineSubdivisionMap hs R n)) := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n) := mono_smallChainMap_f _ _ R n
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n)).mp
  simp only [Category.assoc]
  rw [← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).comm, ← Category.assoc, smallAffineSubdivisionMap_inclusion,
    Category.assoc, affineSubdivisionMap_comm, smallAffineSubdivisionMap_inclusion]
  rw [← Category.assoc (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).comm]
  simp only [Category.assoc]


def smallAffineSubdivision : ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)) ⟶ ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)) where
  f := smallAffineSubdivisionMap hs R
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact smallSubdivision_comm hs R j


@[simp]
theorem smallAffineSubdivision_f (n : ℕ) :
    (smallAffineSubdivision hs R).f n = smallAffineSubdivisionMap hs R n := rfl


theorem smallAffineSubdivision_inclusion :
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivision hs R) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)))) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R))) (affineSubdivision R)) := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact smallAffineSubdivisionMap_inclusion hs R n

private theorem smallHomotopy_comm (n : ℕ) :
    (smallAffineSubdivision hs R - (_root_.SSet.chainComplexMap (smallAffineStraightening hs) R)).f (n + 1) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n) (smallAffineSubdivisionHomotopyMap hs R n)) +
        (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionHomotopyMap hs R (n + 1)) (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 2) (n + 1))) := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1)) := mono_smallChainMap_f _ _ R (n + 1)
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1))).mp
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, smallAffineSubdivision_f,
    smallAffineSubdivisionMap_inclusion]
  have hS := HomologicalComplex.congr_hom (smallAffineStraightening_inclusion hs R) (n + 1)
  simp only [HomologicalComplex.comp_f] at hS
  rw [hS, ← Preadditive.comp_sub]
  change (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f (n + 1)) ((affineSubdivision R - (_root_.SSet.chainComplexMap (affineStraightening (E := E)) R)).f (n + 1))) = _
  rw [affineSubdivisionHomotopyMap_comm, Preadditive.comp_add, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [smallAffineSubdivisionHomotopyMap_inclusion]
  rw [← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).comm, ← Category.assoc (smallAffineSubdivisionHomotopyMap hs R (n + 1)),
    smallAffineSubdivisionHomotopyMap_inclusion]
  rw [← Category.assoc (((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).comm]
  simp only [Category.assoc]

private theorem smallStraightening_zero : ((_root_.SSet.chainComplexMap (smallAffineStraightening hs) R)).f 0 = 𝟙 _ := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f 0) := mono_smallChainMap_f _ _ R 0
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f 0)).mp
  have h := HomologicalComplex.congr_hom (smallAffineStraightening_inclusion hs R) 0
  simpa only [HomologicalComplex.comp_f, affineStraightening_f_zero,
    Category.id_comp, Category.comp_id] using h


def smallAffineSubdivisionHomotopy : Homotopy (smallAffineSubdivision hs R) ((_root_.SSet.chainComplexMap (smallAffineStraightening hs) R)) where
  hom i j := if h : i + 1 = j then
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionHomotopyMap hs R i) (eqToHom (congrArg ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X h))) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dif_neg hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        smallAffineSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        smallAffineSubdivision_f, smallAffineSubdivisionMap_zero, smallStraightening_zero]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id]
      exact sub_eq_iff_eq_add.mp (smallHomotopy_comm hs R n)


@[simp]
theorem smallAffineSubdivisionHomotopy_hom (n : ℕ) :
    (smallAffineSubdivisionHomotopy hs R).hom n (n + 1) =
      smallAffineSubdivisionHomotopyMap hs R n := by
  change (if h : n + 1 = n + 1 then
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionHomotopyMap hs R n) (eqToHom (congrArg ((_root_.SSet.chainComplex ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)) : SSet) R)).X h))) else 0) = _
  rw [dif_pos rfl, eqToHom_refl, Category.comp_id]

variable {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {t : Set E'} (ht : Convex ℝ t) (f : E →L[ℝ] E') (hf : Set.MapsTo f s t)


private theorem supported_linear_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R)).f n) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E') (fun _ : Unit ↦ t)))) R)).f n)) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R)).f n) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)).f n)) := by
  have h : (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R))) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E') (fun _ : Unit ↦ t)))) R)))) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)))) R))) (((_root_.SSet.chainComplexMap ((TopCat.toSSet.map
  (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f))))) R)))) := by
    change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
      (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _))
    rw [← Functor.map_comp, ← Functor.map_comp, smallSingularSimplicesMap_ι]
  exact HomologicalComplex.congr_hom h n


theorem smallAffineSubdivisionMap_naturality_linear (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionMap hs R n) (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R)).f n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R)).f n) (smallAffineSubdivisionMap ht R n)) := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E') (fun _ : Unit ↦ t)))) R)).f n) := mono_smallChainMap_f _ _ R n
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E') (fun _ : Unit ↦ t)))) R)).f n)).mp
  simp only [Category.assoc]
  rw [supported_linear_inclusion R f hf, smallAffineSubdivisionMap_inclusion]
  rw [← Category.assoc, smallAffineSubdivisionMap_inclusion, Category.assoc,
    affineSubdivisionMap_naturality_linear]
  rw [← Category.assoc (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R)).f n), supported_linear_inclusion R f hf]
  simp only [Category.assoc]


theorem smallAffineSubdivisionHomotopyMap_naturality_linear (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionHomotopyMap hs R n) (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R)).f (n + 1))) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R)).f n) (smallAffineSubdivisionHomotopyMap ht R n)) := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E') (fun _ : Unit ↦ t)))) R)).f (n + 1)) := mono_smallChainMap_f _ _ R (n + 1)
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices (TopCat.of E') (fun _ : Unit ↦ t)))) R)).f (n + 1))).mp
  simp only [Category.assoc]
  rw [supported_linear_inclusion R f hf, smallAffineSubdivisionHomotopyMap_inclusion]
  rw [← Category.assoc, smallAffineSubdivisionHomotopyMap_inclusion, Category.assoc,
    affineSubdivisionHomotopyMap_naturality_linear]
  rw [← Category.assoc (((_root_.SSet.chainComplexMap
  (smallSingularSimplicesMap (X := TopCat.of E) (Y := TopCat.of E')
    (U := fun _ : Unit ↦ s) (V := fun _ : Unit ↦ t)
    (TopCat.ofHom (ContinuousMap.mk f (ContinuousLinearMap.continuous f)))
    (fun _ ↦ Exists.intro Unit.unit hf)) R)).f n), supported_linear_inclusion R f hf]
  simp only [Category.assoc]

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Universal -/
section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
universe u
noncomputable section
namespace DifferentialGeometry.Homology
private abbrev simplexAmbient (n : ℕ) := ULift.{u} (Fin (n + 1) → ℝ)
private def simplexRegion (n : ℕ) : Set (simplexAmbient.{u} n) :=
  ULift.down ⁻¹' stdSimplex ℝ (Fin (n + 1))
private theorem convex_simplexRegion (n : ℕ) : Convex ℝ (simplexRegion.{u} n) := by
  intro x hx y hy a b ha hb hab
  exact (convex_stdSimplex ℝ (Fin (n + 1))) hx hy ha hb hab
private def simplexRegionHomeo (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ≃ₜ simplexRegion.{u} n where
  toFun x := ⟨⟨x.down.val⟩, x.down.property⟩
  invFun x := ⟨⟨x.val.down, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _
  continuous_invFun :=
    continuous_uliftUp.comp ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)
private def simplexCoordinatesMap {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    simplexAmbient.{u} n →L[ℝ] simplexAmbient.{u} m where
  toFun x := ⟨FunOnFinite.linearMap ℝ ℝ f x.down⟩
  map_add' x y := by
    apply ULift.ext
    exact map_add (FunOnFinite.linearMap ℝ ℝ f) x.down y.down
  map_smul' a x := by
    apply ULift.ext
    exact map_smul (FunOnFinite.linearMap ℝ ℝ f) a x.down
  cont := continuous_uliftUp.comp ((FunOnFinite.continuous_linearMap ℝ ℝ f).comp
    continuous_uliftDown)
private theorem simplexCoordinatesMap_mem {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    Set.MapsTo (simplexCoordinatesMap.{u} f) (simplexRegion n) (simplexRegion m) := by
  intro x hx
  exact (stdSimplex.map f ⟨x.down, hx⟩).property
private def simplexEmbedding (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶ TopCat.of (simplexAmbient.{u} n) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.down.val⟩,
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩
private def simplexSupportedIso (n : ℕ) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) ≅
      (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
        (fun _ : Unit ↦ simplexRegion n) : SSet) :=
  TopCat.toSSet.mapIso (TopCat.isoOfHomeo (simplexRegionHomeo n)) ≪≫
    singularSubspaceIso _ _

private def simplexSupportedMap {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (smallSingularSimplices (TopCat.of (simplexAmbient.{u} n))
      (fun _ : Unit ↦ simplexRegion n) : SSet) ⟶
    (smallSingularSimplices (TopCat.of (simplexAmbient.{u} m))
      (fun _ : Unit ↦ simplexRegion m) : SSet) :=
  smallSingularSimplicesMap
    (TopCat.ofHom (⟨simplexCoordinatesMap f, (simplexCoordinatesMap f).continuous⟩ :
      C(simplexAmbient n, simplexAmbient m))) (fun _ ↦ ⟨(), simplexCoordinatesMap_mem f⟩)

private theorem simplexSupportedIso_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (CategoryTheory.CategoryStruct.comp (TopCat.toSSet.map (SimplexCategory.toTop.map f)) ((simplexSupportedIso.{u} m).hom)) =
      (CategoryTheory.CategoryStruct.comp ((simplexSupportedIso.{u} n).hom) (simplexSupportedMap f)) := by
  ext d σ
  apply Subtype.ext
  rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def simplexSupportedChainIso (n : ℕ) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso (simplexSupportedIso.{u} n)

private theorem simplexSupportedChainIso_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R) ((simplexSupportedChainIso R m).hom)) =
      (CategoryTheory.CategoryStruct.comp ((simplexSupportedChainIso R n).hom) (SSet.chainComplexMap (simplexSupportedMap f) R)) := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _))
  rw [← Functor.map_comp, ← Functor.map_comp, simplexSupportedIso_naturality]

private theorem simplexSupportedChainIso_inv_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (CategoryTheory.CategoryStruct.comp ((simplexSupportedChainIso R n).inv) (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R)) =
      (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (simplexSupportedMap f) R) ((simplexSupportedChainIso R m).inv)) := by
  apply (Iso.inv_comp_eq _).mpr
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr (simplexSupportedChainIso_naturality R f)


def simplexSubdivision (n : ℕ) :
    (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R ⟶
      (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R :=
  (CategoryTheory.CategoryStruct.comp ((simplexSupportedChainIso R n).hom) ((CategoryTheory.CategoryStruct.comp (smallAffineSubdivision (convex_simplexRegion n) R) ((simplexSupportedChainIso R n).inv))))


def simplexStraightening (n : ℕ) :
    (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R ⟶
      (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R :=
  (CategoryTheory.CategoryStruct.comp ((simplexSupportedChainIso R n).hom) ((CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R) ((simplexSupportedChainIso R n).inv))))


def simplexSubdivisionHomotopy (n : ℕ) :
    Homotopy (simplexSubdivision R n) (simplexStraightening R n) :=
  ((smallAffineSubdivisionHomotopy (convex_simplexRegion n) R).compLeft
    (simplexSupportedChainIso R n).hom).compRight (simplexSupportedChainIso R n).inv

theorem simplexSubdivision_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (CategoryTheory.CategoryStruct.comp (simplexSubdivision R n) (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R)) =
      (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R) (simplexSubdivision R m)) := by
  have hB : (CategoryTheory.CategoryStruct.comp (smallAffineSubdivision (convex_simplexRegion n) R) (SSet.chainComplexMap (simplexSupportedMap f) R)) =
      (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (simplexSupportedMap f) R) (smallAffineSubdivision (convex_simplexRegion m) R)) := by
    apply HomologicalComplex.hom_f_injective
    funext d
    exact smallAffineSubdivisionMap_naturality_linear _ R _ (simplexCoordinatesMap f)
      (simplexCoordinatesMap_mem f) d
  simp only [simplexSubdivision, Category.assoc]
  rw [simplexSupportedChainIso_inv_naturality]
  rw [← Category.assoc (smallAffineSubdivision (convex_simplexRegion n) R), hB]
  simp only [Category.assoc]
  rw [← Category.assoc ((simplexSupportedChainIso R n).hom),
    ← simplexSupportedChainIso_naturality]
  simp only [Category.assoc]


theorem simplexSubdivisionHomotopy_naturality {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (d : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((simplexSubdivisionHomotopy R n).hom d (d + 1)) ((SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R).f (d + 1))) =
      (CategoryTheory.CategoryStruct.comp ((SSet.chainComplexMap (TopCat.toSSet.map (SimplexCategory.toTop.map f)) R).f d) ((simplexSubdivisionHomotopy R m).hom d (d + 1))) := by
  have h := HomologicalComplex.congr_hom (simplexSupportedChainIso_naturality R f) d
  have hi := HomologicalComplex.congr_hom (simplexSupportedChainIso_inv_naturality R f) (d + 1)
  simp only [HomologicalComplex.comp_f] at h hi
  simp only [simplexSubdivisionHomotopy, Homotopy.compRight_hom, Homotopy.compLeft_hom,
    smallAffineSubdivisionHomotopy_hom, Category.assoc]
  rw [hi]
  rw [← Category.assoc (smallAffineSubdivisionHomotopyMap (convex_simplexRegion n) R d)]
  have hH : (CategoryTheory.CategoryStruct.comp (smallAffineSubdivisionHomotopyMap (convex_simplexRegion n) R d) ((SSet.chainComplexMap (simplexSupportedMap f) R).f (d + 1))) =
      (CategoryTheory.CategoryStruct.comp ((SSet.chainComplexMap (simplexSupportedMap f) R).f d) (smallAffineSubdivisionHomotopyMap (convex_simplexRegion m) R d)) :=
    smallAffineSubdivisionHomotopyMap_naturality_linear _ R _ (simplexCoordinatesMap f)
      (simplexCoordinatesMap_mem f) d
  rw [hH]
  simp only [Category.assoc]
  rw [← Category.assoc ((simplexSupportedChainIso R n).hom.f d), ← h]
  simp only [Category.assoc]


def fundamentalSingularSimplex (n : ℕ) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) _⦋n⦌ :=
  ULift.up (𝟙 _)


def fundamentalSimplexChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X n :=
  (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).ιChainComplex
    (fundamentalSingularSimplex n)


def barycentricSimplexChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X n :=
  (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((simplexSubdivision R n).f n))


def barycentricSimplexHomotopyChain (n : ℕ) :
    R ⟶ ((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).chainComplex R).X (n + 1) :=
  (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((simplexSubdivisionHomotopy R n).hom n (n + 1)))


theorem fundamentalSimplexChain_boundary (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R (n + 1)) (((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 1) n)) =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        ((CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f n))) := by
  rw [fundamentalSimplexChain, SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [fundamentalSimplexChain, SSet.ι_chainComplexMap_f]
  rfl


theorem barycentricSimplexChain_boundary (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (barycentricSimplexChain R (n + 1)) (((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 1) n)) =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        ((CategoryTheory.CategoryStruct.comp (barycentricSimplexChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f n))) := by
  rw [barycentricSimplexChain, Category.assoc, (simplexSubdivision R (n + 1)).comm,
    ← Category.assoc, fundamentalSimplexChain_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  have h := HomologicalComplex.congr_hom (simplexSubdivision_naturality R (SimplexCategory.δ i)) n
  simp only [HomologicalComplex.comp_f] at h
  rw [← h]
  rfl

private theorem simplexEmbedding_fundamental (n : ℕ) :
    (TopCat.toSSet.map (simplexEmbedding.{u} n)).app (op ⦋n⦌) (fundamentalSingularSimplex n) =
      affineSingularSimplex (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val) := by
  apply ((TopCat.of (simplexAmbient.{u} n)).toSSetObjEquiv (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro x
  apply ULift.ext
  change x.val = (∑ i, x i • ULift.up (stdSimplex.vertex (S := ℝ) i).val).down
  change x.val = (ULift.moduleEquiv : simplexAmbient.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (∑ i, x i • ULift.up (stdSimplex.vertex (S := ℝ) i).val)
  rw [map_sum]
  simp only [map_smul, ULift.moduleEquiv_apply]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]
  rfl


theorem fundamentalSimplexChain_straightening (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((simplexStraightening R n).f n)) =
      fundamentalSimplexChain R n := by
  have hσ : (smallAffineStraightening (convex_simplexRegion n)).app (op ⦋n⦌)
        ((simplexSupportedIso.{u} n).hom.app (op ⦋n⦌) (fundamentalSingularSimplex n)) =
      (simplexSupportedIso.{u} n).hom.app (op ⦋n⦌) (fundamentalSingularSimplex n) := by
    apply Subtype.ext
    change affineSingularSimplex (singularSimplexVertices
        ((TopCat.toSSet.map (simplexEmbedding n)).app (op ⦋n⦌) (fundamentalSingularSimplex n))) =
      (TopCat.toSSet.map (simplexEmbedding n)).app (op ⦋n⦌) (fundamentalSingularSimplex n)
    rw [simplexEmbedding_fundamental, singularSimplexVertices_affineSingularSimplex]
  have h : (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((CategoryTheory.CategoryStruct.comp ((simplexSupportedChainIso R n).hom.f n) ((SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R).f n)))) =
      (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((simplexSupportedChainIso R n).hom.f n)) := by
    rw [fundamentalSimplexChain, ← Category.assoc]
    change (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex
        (fundamentalSingularSimplex n)) ((SSet.chainComplexMap (simplexSupportedIso n).hom R).f n)))) (_)) = _
    rw [SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f, hσ]
    exact (SSet.ι_chainComplexMap_f _ _ _ R (fundamentalSingularSimplex n)).symm
  have hid := HomologicalComplex.congr_hom (simplexSupportedChainIso R n).hom_inv_id n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hid
  change (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((CategoryTheory.CategoryStruct.comp ((simplexSupportedChainIso R n).hom.f n) ((CategoryTheory.CategoryStruct.comp ((SSet.chainComplexMap (smallAffineStraightening (convex_simplexRegion n)) R).f n) ((simplexSupportedChainIso R n).inv.f n)))))) = _
  simpa only [Category.assoc, hid, Category.comp_id] using
    congrArg (fun q ↦ (CategoryTheory.CategoryStruct.comp (q) ((simplexSupportedChainIso R n).inv.f n))) h


@[simp]
theorem barycentricSimplexChain_zero :
    barycentricSimplexChain R 0 = fundamentalSimplexChain R 0 := by
  have hid := HomologicalComplex.congr_hom (simplexSupportedChainIso R 0).hom_inv_id 0
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hid
  simp only [barycentricSimplexChain, simplexSubdivision, HomologicalComplex.comp_f,
    smallAffineSubdivision_f, smallAffineSubdivisionMap_zero, Category.id_comp,
    hid, Category.comp_id]


@[simp]
theorem barycentricSimplexHomotopyChain_zero : barycentricSimplexHomotopyChain R 0 = 0 := by
  simp only [barycentricSimplexHomotopyChain, simplexSubdivisionHomotopy,
    Homotopy.compRight_hom, Homotopy.compLeft_hom, smallAffineSubdivisionHomotopy_hom,
    smallAffineSubdivisionHomotopyMap_zero, comp_zero, zero_comp]


theorem barycentricSimplexHomotopyChain_boundary (n : ℕ) :
    barycentricSimplexChain R (n + 1) - fundamentalSimplexChain R (n + 1) =
      (∑ i : Fin (n + 2), (-1) ^ i.val •
        ((CategoryTheory.CategoryStruct.comp (barycentricSimplexHomotopyChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map
            (SimplexCategory.toTop.map (SimplexCategory.δ i))) R).f (n + 1))))) +
      (CategoryTheory.CategoryStruct.comp (barycentricSimplexHomotopyChain R (n + 1)) (((TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)).chainComplex R).d (n + 2) (n + 1))) := by
  have h := (simplexSubdivisionHomotopy R (n + 1)).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have he := congrArg (fun q ↦ (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R (n + 1)) (q))) h
  simp only [Preadditive.comp_add] at he
  rw [fundamentalSimplexChain_straightening] at he
  apply (sub_eq_iff_eq_add).mpr
  change (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R (n + 1)) ((simplexSubdivision R (n + 1)).f (n + 1))) = _
  rw [he]
  congr 2
  rw [← Category.assoc, fundamentalSimplexChain_boundary]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro i _
  rw [← simplexSubdivisionHomotopy_naturality R (SimplexCategory.δ i) n]
  rfl

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Singular -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology

universe u

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k) (X : TopCat.{u})


def singularSimplexMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    SimplexCategory.toTop.obj ⦋n⦌ ⟶ X := σ.down



theorem fundamentalSimplexChain_pushforward {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n)) =
      (TopCat.toSSet.obj X).ιChainComplex σ := by
  rw [fundamentalSimplexChain, SSet.ι_chainComplexMap_f]
  rfl

private theorem pushforward_face {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map
        (SimplexCategory.toTop.map (SimplexCategory.δ i))) R) (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R)) =
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X ((TopCat.toSSet.obj X).δ i σ))) R := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← TopCat.toSSet.map_comp]
  rfl


def singularSubdivisionMap (n : ℕ) : ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n ⟶ ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n :=
  Sigma.desc (fun σ : TopCat.toSSet.obj X _⦋n⦌ ↦ (CategoryTheory.CategoryStruct.comp (barycentricSimplexChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n)))


theorem ι_singularSubdivisionMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj X).ιChainComplex σ) (singularSubdivisionMap R X n)) =
      (CategoryTheory.CategoryStruct.comp (barycentricSimplexChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n)) :=
  Sigma.ι_desc _ _


@[simp]
theorem singularSubdivisionMap_zero : singularSubdivisionMap R X 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_singularSubdivisionMap, barycentricSimplexChain_zero,
    fundamentalSimplexChain_pushforward, Category.comp_id]


theorem singularSubdivisionMap_comm (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (singularSubdivisionMap R X (n + 1)) (((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).d (n + 1) n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).d (n + 1) n) (singularSubdivisionMap R X n)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionMap, Category.assoc,
    (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).comm, ← Category.assoc, barycentricSimplexChain_boundary]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ), SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
    ι_singularSubdivisionMap]
  apply Finset.sum_congr rfl
  intro i _
  have h := HomologicalComplex.congr_hom (pushforward_face R X σ i) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]


def singularSubdivision : ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)) ⟶ ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)) where
  f := singularSubdivisionMap R X
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact singularSubdivisionMap_comm R X j


@[simp]
theorem singularSubdivision_f (n : ℕ) :
    (singularSubdivision R X).f n = singularSubdivisionMap R X n := rfl


def singularSubdivisionHomotopyMap (n : ℕ) : ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n ⟶ ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X (n + 1) :=
  Sigma.desc (fun σ : TopCat.toSSet.obj X _⦋n⦌ ↦ (CategoryTheory.CategoryStruct.comp (barycentricSimplexHomotopyChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f (n + 1))))


theorem ι_singularSubdivisionHomotopyMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj X).ιChainComplex σ) (singularSubdivisionHomotopyMap R X n)) =
      (CategoryTheory.CategoryStruct.comp (barycentricSimplexHomotopyChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f (n + 1))) :=
  Sigma.ι_desc _ _


@[simp]
theorem singularSubdivisionHomotopyMap_zero : singularSubdivisionHomotopyMap R X 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_singularSubdivisionHomotopyMap, barycentricSimplexHomotopyChain_zero,
    zero_comp, comp_zero]


theorem singularSubdivisionHomotopyMap_comm (n : ℕ) :
    singularSubdivisionMap R X (n + 1) - 𝟙 _ =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).d (n + 1) n) (singularSubdivisionHomotopyMap R X n)) +
        (CategoryTheory.CategoryStruct.comp (singularSubdivisionHomotopyMap R X (n + 1)) (((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).d (n + 2) (n + 1))) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Preadditive.comp_sub, ι_singularSubdivisionMap, Category.comp_id,
    ← fundamentalSimplexChain_pushforward R X σ, ← Preadditive.sub_comp,
    barycentricSimplexHomotopyChain_boundary, Preadditive.add_comp, Preadditive.comp_add,
    fundamentalSimplexChain_pushforward]
  congr 1
  · rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
      ι_singularSubdivisionHomotopyMap]
    apply Finset.sum_congr rfl
    intro i _
    have h := HomologicalComplex.congr_hom (pushforward_face R X σ i) (n + 1)
    simp only [HomologicalComplex.comp_f] at h
    rw [h]
  · rw [Category.assoc, ← (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).comm]
    rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
      ι_singularSubdivisionHomotopyMap, Category.assoc]


def singularSubdivisionHomotopy : Homotopy (singularSubdivision R X) (𝟙 ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R))) where
  hom i j := if h : i + 1 = j then
    (CategoryTheory.CategoryStruct.comp (singularSubdivisionHomotopyMap R X i) (eqToHom (congrArg ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X h))) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dif_neg hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        singularSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        singularSubdivision_f, singularSubdivisionMap_zero, HomologicalComplex.id_f]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        singularSubdivision_f, HomologicalComplex.id_f]
      exact sub_eq_iff_eq_add.mp (singularSubdivisionHomotopyMap_comm R X n)


@[simp]
theorem singularSubdivisionHomotopy_hom (n : ℕ) :
    (singularSubdivisionHomotopy R X).hom n (n + 1) =
      singularSubdivisionHomotopyMap R X n := by
  change (if h : n + 1 = n + 1 then
    (CategoryTheory.CategoryStruct.comp (singularSubdivisionHomotopyMap R X n) (eqToHom (congrArg ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X h))) else 0) = _
  rw [dif_pos rfl, eqToHom_refl, Category.comp_id]

variable {Y : TopCat.{u}} (f : X ⟶ Y)


theorem singularSimplexMap_naturality {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    singularSimplexMap Y ((TopCat.toSSet.map f).app (op ⦋n⦌) σ) =
      (CategoryTheory.CategoryStruct.comp (singularSimplexMap X σ) (f)) := rfl

private theorem pushforward_postcomp {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R) (SSet.chainComplexMap (TopCat.toSSet.map f) R)) =
      SSet.chainComplexMap (TopCat.toSSet.map
        (singularSimplexMap Y ((TopCat.toSSet.map f).app (op ⦋n⦌) σ))) R := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← TopCat.toSSet.map_comp, singularSimplexMap_naturality]


theorem singularSubdivisionMap_naturality (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (singularSubdivisionMap R X n) ((SSet.chainComplexMap (TopCat.toSSet.map f) R).f n)) =
      (CategoryTheory.CategoryStruct.comp ((SSet.chainComplexMap (TopCat.toSSet.map f) R).f n) (singularSubdivisionMap R Y n)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionMap, Category.assoc]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
    SSet.ι_chainComplexMap_f, ι_singularSubdivisionMap]
  have h := HomologicalComplex.congr_hom (pushforward_postcomp R X f σ) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]


theorem singularSubdivision_naturality :
    (CategoryTheory.CategoryStruct.comp (singularSubdivision R X) (SSet.chainComplexMap (TopCat.toSSet.map f) R)) =
      (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map f) R) (singularSubdivision R Y)) := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact singularSubdivisionMap_naturality R X f n


end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.SingularSupport -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)



def smallSingularSimplexPushforward {n : ℕ} (σ : ((smallSingularSimplices X U) : SSet) _⦋n⦌) :
    TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌) ⟶ ((smallSingularSimplices X U) : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (singularSimplexMap X σ.val)) (by
    intro m τ hτ
    obtain ⟨ρ, rfl⟩ := hτ
    obtain ⟨i, hi⟩ := σ.property
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨((SimplexCategory.toTop.obj ⦋n⦌).toSSetObjEquiv m ρ z).down, rfl⟩)


@[simp]
theorem smallSingularSimplexPushforward_ι {n : ℕ} (σ : ((smallSingularSimplices X U) : SSet) _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp (smallSingularSimplexPushforward X U σ) (((smallSingularSimplices X U)).ι)) =
      TopCat.toSSet.map (singularSimplexMap X σ.val) := rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


private theorem smallPushforward_inclusion {n : ℕ} (σ : ((smallSingularSimplices X U) : SSet) _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)))) =
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ.val)) R := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, smallSingularSimplexPushforward_ι]


def smallSingularSubdivisionMap (n : ℕ) : ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).X n ⟶ ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).X n :=
  Sigma.desc (fun σ : ((smallSingularSimplices X U) : SSet) _⦋n⦌ ↦ (CategoryTheory.CategoryStruct.comp (barycentricSimplexChain R n) ((SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f n)))


theorem ι_smallSingularSubdivisionMap {n : ℕ} (σ : ((smallSingularSimplices X U) : SSet) _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices X U) : SSet).ιChainComplex σ) (smallSingularSubdivisionMap X U R n)) =
      (CategoryTheory.CategoryStruct.comp (barycentricSimplexChain R n) ((SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f n)) :=
  Sigma.ι_desc _ _


theorem smallSingularSubdivisionMap_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallSingularSubdivisionMap X U R n) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f n) (singularSubdivisionMap R X n)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallSingularSubdivisionMap, Category.assoc,
    ← Category.assoc (((smallSingularSimplices X U) : SSet).ιChainComplex σ), SSet.ι_chainComplexMap_f,
    ι_singularSubdivisionMap]
  have h := HomologicalComplex.congr_hom (smallPushforward_inclusion X U R σ) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]
  rfl


def smallSingularSubdivisionHomotopyMap (n : ℕ) : ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).X n ⟶ ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).X (n + 1) :=
  Sigma.desc (fun σ : ((smallSingularSimplices X U) : SSet) _⦋n⦌ ↦ (CategoryTheory.CategoryStruct.comp (barycentricSimplexHomotopyChain R n) ((SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f (n + 1))))


theorem ι_smallSingularSubdivisionHomotopyMap {n : ℕ} (σ : ((smallSingularSimplices X U) : SSet) _⦋n⦌) :
    (CategoryTheory.CategoryStruct.comp (((smallSingularSimplices X U) : SSet).ιChainComplex σ) (smallSingularSubdivisionHomotopyMap X U R n)) =
      (CategoryTheory.CategoryStruct.comp (barycentricSimplexHomotopyChain R n) ((SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f (n + 1))) :=
  Sigma.ι_desc _ _


theorem smallSingularSubdivisionHomotopyMap_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallSingularSubdivisionHomotopyMap X U R n) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f (n + 1))) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f n) (singularSubdivisionHomotopyMap R X n)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallSingularSubdivisionHomotopyMap, Category.assoc,
    ← Category.assoc (((smallSingularSimplices X U) : SSet).ιChainComplex σ), SSet.ι_chainComplexMap_f,
    ι_singularSubdivisionHomotopyMap]
  have h := HomologicalComplex.congr_hom (smallPushforward_inclusion X U R σ) (n + 1)
  simp only [HomologicalComplex.comp_f] at h
  rw [h]
  rfl

private theorem smallSingularSubdivision_comm (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (smallSingularSubdivisionMap X U R (n + 1)) (((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).d (n + 1) n)) =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).d (n + 1) n) (smallSingularSubdivisionMap X U R n)) := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f n) := mono_smallChainMap_f X U R n
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f n)).mp
  simp only [Category.assoc]
  rw [← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).comm, ← Category.assoc, smallSingularSubdivisionMap_inclusion,
    Category.assoc, singularSubdivisionMap_comm, smallSingularSubdivisionMap_inclusion]
  rw [← Category.assoc (((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).comm]
  simp only [Category.assoc]


def smallSingularSubdivision : ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)) ⟶ ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)) where
  f := smallSingularSubdivisionMap X U R
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact smallSingularSubdivision_comm X U R j


@[simp]
theorem smallSingularSubdivision_f (n : ℕ) :
    (smallSingularSubdivision X U R).f n = smallSingularSubdivisionMap X U R n := rfl


theorem smallSingularSubdivision_inclusion :
    (CategoryTheory.CategoryStruct.comp (smallSingularSubdivision X U R) (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)))) = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R))) (singularSubdivision R X)) := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact smallSingularSubdivisionMap_inclusion X U R n

private theorem smallSingularSubdivisionHomotopy_comm (n : ℕ) :
    smallSingularSubdivisionMap X U R (n + 1) - 𝟙 _ =
      (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).d (n + 1) n) (smallSingularSubdivisionHomotopyMap X U R n)) +
        (CategoryTheory.CategoryStruct.comp (smallSingularSubdivisionHomotopyMap X U R (n + 1)) (((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).d (n + 2) (n + 1))) := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f (n + 1)) := mono_smallChainMap_f X U R (n + 1)
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f (n + 1))).mp
  calc
    _ = (CategoryTheory.CategoryStruct.comp (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f (n + 1)) ((singularSubdivisionMap R X (n + 1) - 𝟙 _))) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, smallSingularSubdivisionMap_inclusion]
    _ = _ := by
      rw [singularSubdivisionHomotopyMap_comm, Preadditive.comp_add, Preadditive.add_comp]
      simp only [Category.assoc]
      rw [smallSingularSubdivisionHomotopyMap_inclusion]
      rw [← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).comm, ← Category.assoc (smallSingularSubdivisionHomotopyMap X U R (n + 1)),
        smallSingularSubdivisionHomotopyMap_inclusion]
      rw [← Category.assoc (((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).d (n + 1) n), ← ((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).comm]
      simp only [Category.assoc]


@[simp]
theorem smallSingularSubdivisionMap_zero : smallSingularSubdivisionMap X U R 0 = 𝟙 _ := by
  have : Mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f 0) := mono_smallChainMap_f X U R 0
  apply (cancel_mono (((_root_.SSet.chainComplexMap (SSet.Subcomplex.ι ((smallSingularSimplices X U))) R)).f 0)).mp
  rw [smallSingularSubdivisionMap_inclusion, singularSubdivisionMap_zero,
    Category.id_comp, Category.comp_id]


@[simp]
theorem smallSingularSubdivisionHomotopyMap_zero :
    smallSingularSubdivisionHomotopyMap X U R 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_smallSingularSubdivisionHomotopyMap, barycentricSimplexHomotopyChain_zero,
    zero_comp, comp_zero]


def smallSingularSubdivisionHomotopy : Homotopy (smallSingularSubdivision X U R) (𝟙 ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R))) where
  hom i j := if h : i + 1 = j then
    (CategoryTheory.CategoryStruct.comp (smallSingularSubdivisionHomotopyMap X U R i) (eqToHom (congrArg ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).X h))) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dif_neg hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        smallSingularSubdivisionHomotopyMap_zero, zero_comp, zero_add,
        smallSingularSubdivision_f, smallSingularSubdivisionMap_zero, HomologicalComplex.id_f]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, eqToHom_refl, Category.comp_id,
        smallSingularSubdivision_f, HomologicalComplex.id_f]
      exact sub_eq_iff_eq_add.mp (smallSingularSubdivisionHomotopy_comm X U R n)


@[simp]
theorem smallSingularSubdivisionHomotopy_hom (n : ℕ) :
    (smallSingularSubdivisionHomotopy X U R).hom n (n + 1) =
      smallSingularSubdivisionHomotopyMap X U R n := by
  change (if h : n + 1 = n + 1 then
    (CategoryTheory.CategoryStruct.comp (smallSingularSubdivisionHomotopyMap X U R n) (eqToHom (congrArg ((_root_.SSet.chainComplex ((smallSingularSimplices X U) : SSet) R)).X h))) else 0) = _
  rw [dif_pos rfl, eqToHom_refl, Category.comp_id]

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.UniversalGeometry -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology


def simplexCoordinateEmbedding (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶ TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.down.val⟩,
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩

private def coordinateRegion (n : ℕ) : Set (ULift.{u} (Fin (n + 1) → ℝ)) :=
  ULift.down ⁻¹' stdSimplex ℝ (Fin (n + 1))

private theorem convex_coordinateRegion (n : ℕ) : Convex ℝ (coordinateRegion.{u} n) := by
  intro x hx y hy a b ha hb hab
  exact (convex_stdSimplex ℝ (Fin (n + 1))) hx hy ha hb hab

private def coordinateRegionHomeo (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ≃ₜ coordinateRegion.{u} n where
  toFun x := ⟨⟨x.down.val⟩, x.down.property⟩
  invFun x := ⟨⟨x.val.down, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _
  continuous_invFun :=
    continuous_uliftUp.comp ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def coordinateChainIso (n : ℕ) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso
    (TopCat.toSSet.mapIso (TopCat.isoOfHomeo (coordinateRegionHomeo n)) ≪≫
      singularSubspaceIso (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))) (coordinateRegion n))

private theorem coordinateChainIso_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((coordinateChainIso R n).hom) (SSet.chainComplexMap
        (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
          (fun _ : Unit ↦ coordinateRegion n)).ι R)) =
      SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R := by
  change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp]
  rfl

private theorem coordinateChainIso_inv_inclusion (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((coordinateChainIso R n).inv) (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R)) =
      SSet.chainComplexMap
        (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
          (fun _ : Unit ↦ coordinateRegion n)).ι R := by
  rw [← coordinateChainIso_inclusion R n, Iso.inv_hom_id_assoc]


theorem mono_simplexCoordinateEmbedding_chainMap_f (n d : ℕ) :
    Mono ((SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f d) := by
  have h := HomologicalComplex.congr_hom (coordinateChainIso_inclusion R n) d
  simp only [HomologicalComplex.comp_f] at h
  rw [← h]
  have : Mono ((SSet.chainComplexMap
      (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
        (fun _ : Unit ↦ coordinateRegion n)).ι R).f d) :=
    mono_smallChainMap_f _ _ R d
  infer_instance


theorem simplexSubdivision_coordinateEmbedding (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (simplexSubdivision R n) (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R)) =
      (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R) (affineSubdivision R)) := by
  change (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp ((coordinateChainIso R n).hom) ((CategoryTheory.CategoryStruct.comp (smallAffineSubdivision (convex_coordinateRegion n) R) ((coordinateChainIso R n).inv)))))) (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R)) = _
  simp only [Category.assoc]
  rw [coordinateChainIso_inv_inclusion]
  rw [smallAffineSubdivision_inclusion]
  rw [← Category.assoc ((coordinateChainIso R n).hom), coordinateChainIso_inclusion]


theorem affineSimplex_coordinateVertices (n : ℕ) (x : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex (fun i ↦ (ULift.up (stdSimplex.vertex (S := ℝ) i).val :
      ULift.{u} (Fin (n + 1) → ℝ))) x = ULift.up x.val := by
  apply ULift.ext
  change (ULift.moduleEquiv : ULift.{u} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
      (∑ i, x i • ULift.up (stdSimplex.vertex (S := ℝ) i).val) = x.val
  rw [map_sum]
  simp only [map_smul, ULift.moduleEquiv_apply]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]
  rfl


theorem singularSimplexMap_coordinateVertices (n : ℕ) :
    singularSimplexMap (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
        (affineSingularSimplex (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val)) =
      simplexCoordinateEmbedding n := by
  apply TopCat.ext
  intro x
  exact affineSimplex_coordinateVertices n x.down


theorem barycentricSimplexChain_coordinateEmbedding (n : ℕ) :
    (CategoryTheory.CategoryStruct.comp (barycentricSimplexChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f n)) =
      (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
        (affineSingularSimplex (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val))) (affineSubdivisionMap R n)) := by
  have h := HomologicalComplex.congr_hom (simplexSubdivision_coordinateEmbedding R n) n
  simp only [HomologicalComplex.comp_f, affineSubdivision_f] at h
  rw [barycentricSimplexChain, Category.assoc, h, ← Category.assoc]
  rw [← singularSimplexMap_coordinateVertices, fundamentalSimplexChain_pushforward]

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def vertexCoordinateMap {n : ℕ} (v : Fin (n + 1) → E) :
    ULift.{u} (Fin (n + 1) → ℝ) →L[ℝ] E where
  toFun x := ∑ i, x.down i • v i
  map_add' x y := by
    change (∑ i, (x.down i + y.down i) • v i) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (a * x.down i) • v i) = a • ∑ i, x.down i • v i
    simp only [Finset.smul_sum, mul_smul]
  cont := continuous_finsetSum _ (fun i _ ↦
    ((continuous_apply i).comp continuous_uliftDown).smul continuous_const)


@[simp]
theorem vertexCoordinateMap_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    vertexCoordinateMap v (ULift.up (stdSimplex.vertex (S := ℝ) i).val) = v i := by
  simp [vertexCoordinateMap, Pi.single_apply]


theorem simplexCoordinateEmbedding_vertexCoordinateMap {n : ℕ} (v : Fin (n + 1) → E) :
    (CategoryTheory.CategoryStruct.comp (simplexCoordinateEmbedding n) (TopCat.ofHom (⟨vertexCoordinateMap v,
        (vertexCoordinateMap v).continuous⟩ : C(ULift.{u} (Fin (n + 1) → ℝ), E)))) =
      singularSimplexMap (TopCat.of E) (affineSingularSimplex v) := rfl


theorem singularSubdivisionMap_affine {n : ℕ} (v : Fin (n + 1) → E) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v)) (singularSubdivisionMap R (TopCat.of E) n)) =
      (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v)) (affineSubdivisionMap R n)) := by
  let F := SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (⟨vertexCoordinateMap v, (vertexCoordinateMap v).continuous⟩ :
      C(ULift.{u} (Fin (n + 1) → ℝ), E)))) R
  have hF : (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R) (F)) =
      SSet.chainComplexMap (TopCat.toSSet.map
        (singularSimplexMap (TopCat.of E) (affineSingularSimplex v))) R := by
    change (CategoryTheory.CategoryStruct.comp (((SSet.chainComplexFunctor _).obj R).map _) (((SSet.chainComplexFunctor _).obj R).map _)) =
      ((SSet.chainComplexFunctor _).obj R).map _
    rw [← Functor.map_comp, ← TopCat.toSSet.map_comp,
      simplexCoordinateEmbedding_vertexCoordinateMap]
  have hf := HomologicalComplex.congr_hom hF n
  simp only [HomologicalComplex.comp_f] at hf
  rw [ι_singularSubdivisionMap, ← hf, ← Category.assoc,
    barycentricSimplexChain_coordinateEmbedding, Category.assoc]
  have hn : (CategoryTheory.CategoryStruct.comp (affineSubdivisionMap R n) (F.f n)) = (CategoryTheory.CategoryStruct.comp (F.f n) (affineSubdivisionMap R n)) :=
    affineSubdivisionMap_naturality_linear (vertexCoordinateMap v) R n
  rw [hn, ← Category.assoc]
  change (CategoryTheory.CategoryStruct.comp (((CategoryTheory.CategoryStruct.comp (_) ((SSet.chainComplexMap _ R).f n)))) (_)) = _
  rw [SSet.ι_chainComplexMap_f, map_affineSingularSimplex_linear]
  have hv : vertexCoordinateMap v ∘
      (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val) = v := by
    funext i
    exact vertexCoordinateMap_vertex v i
  rw [hv]

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.AffinePieces -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology


def BarycentricFlag (n : ℕ) : Type :=
  match n with
  | 0 => Unit
  | n + 1 => Fin (n + 2) × BarycentricFlag n

instance (n : ℕ) : Fintype (BarycentricFlag n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n hn => exact inferInstanceAs (Fintype (Fin (n + 2) × BarycentricFlag n))


def barycentricFlagSign (n : ℕ) : BarycentricFlag n → ℤ :=
  match n with
  | 0 => fun _ ↦ 1
  | n + 1 => fun p ↦ (-1) ^ p.1.val * barycentricFlagSign n p.2

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def barycentricPieceVertices (n : ℕ) :
    (Fin (n + 1) → E) → BarycentricFlag n → Fin (n + 1) → E :=
  match n with
  | 0 => fun v _ ↦ v
  | n + 1 => fun v p ↦ Fin.cons (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v)
      (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2)


theorem barycentricPieceVertices_mem (n : ℕ) (v : Fin (n + 1) → E)
    (p : BarycentricFlag n) {s : Set E} (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s)
    (i : Fin (n + 1)) : barycentricPieceVertices n v p i ∈ s := by
  induction n with
  | zero => exact hv i
  | succ n hn =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hs.centerMass_mem (fun _ _ ↦ zero_le_one)
        (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos (n + 1)) :
          (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ))) (fun j _ ↦ hv j)
    · exact hn (v ∘ p.1.succAbove) p.2 (fun j ↦ hv (p.1.succAbove j)) j

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem affineSubdivisionMap_pieces (n : ℕ) (v : Fin (n + 1) → E) :
    (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v)) (affineSubdivisionMap R n)) =
      ∑ p : BarycentricFlag n, barycentricFlagSign n p •
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
          (affineSingularSimplex (barycentricPieceVertices n v p)) := by
  induction n with
  | zero =>
    rw [affineSubdivisionMap_zero, Category.comp_id]
    change _ = ∑ _ : Unit, (1 : ℤ) • _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rfl
  | succ n hn =>
    rw [ι_affineSubdivisionMap_succ]
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
      singularSimplexBarycenter, singularSimplexVertices_affineSingularSimplex,
      δ_affineSingularSimplex]
    simp only [← Category.assoc, hn, Preadditive.sum_comp, Preadditive.zsmul_comp,
      ι_affineCone]
    change _ = ∑ p : Fin (n + 2) × BarycentricFlag n, _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [← mul_smul, singularSimplexVertices_affineSingularSimplex]
    rfl

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.Mesh -/
section

noncomputable section

open Finset

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem dist_vertexBarycenter_le (n : ℕ) (v : Fin (n + 1) → E) (j : Fin (n + 1)) {D : ℝ}
    (hv : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v) (v j) ≤
      (n : ℝ) / (n + 1) * D := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have he : Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v - v j =
      ((n : ℝ) + 1)⁻¹ • ∑ i, (v i - v j) := by
    simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, one_smul, Nat.cast_add, Nat.cast_one, nsmul_eq_mul, mul_one,
      Finset.sum_sub_distrib]
    rw [smul_sub]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hn]
  have hs : (∑ i, ‖v i - v j‖) ≤ (n : ℝ) * D := by
    calc
      _ = ∑ i ∈ Finset.univ.erase j, ‖v i - v j‖ := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
        simp
      _ ≤ ∑ _i ∈ Finset.univ.erase j, D := by
        apply Finset.sum_le_sum
        intro i _
        exact (dist_eq_norm (v i) (v j)) ▸ hv i j
      _ = _ := by simp
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((n : ℝ) + 1)⁻¹ * (∑ i, ‖v i - v j‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring


theorem dist_affineSimplex_le {n : ℕ} (v : Fin (n + 1) → E) {D : ℝ}
    (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : stdSimplex ℝ (Fin (n + 1))) :
    dist (affineSimplex v x) (affineSimplex v y) ≤ D := by
  have hy : ∀ i, affineSimplex v y ∈ Metric.closedBall (v i) D := fun i ↦
    range_affineSimplex_subset v (convex_closedBall (v i) D)
      (fun j ↦ hv j i) ⟨y, rfl⟩
  exact range_affineSimplex_subset v (convex_closedBall (affineSimplex v y) D)
    (fun i ↦ by simpa only [Metric.mem_closedBall, dist_comm] using hy i) ⟨x, rfl⟩


theorem dist_barycentricPieceVertices_le (n : ℕ) (v : Fin (n + 1) → E)
    (p : BarycentricFlag n) {D : ℝ} (hv : ∀ i j, dist (v i) (v j) ≤ D)
    (i j : Fin (n + 1)) :
    dist (barycentricPieceVertices n v p i) (barycentricPieceVertices n v p j) ≤
      (n : ℝ) / (n + 1) * D := by
  induction n with
  | zero =>
    have hij : i = j := @Subsingleton.elim (Fin 1) inferInstance i j
    rw [hij, dist_self]
    simp
  | succ n hn =>
    have hD : 0 ≤ D := le_trans dist_nonneg (hv 0 0)
    have hface : ∀ a b, dist ((v ∘ p.1.succAbove) a) ((v ∘ p.1.succAbove) b) ≤ D :=
      fun a b ↦ hv _ _
    have hapex (a : Fin (n + 1)) :
        dist (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 a)
            (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v) ≤
          ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1) * D := by
      apply barycentricPieceVertices_mem n (v ∘ p.1.succAbove) p.2
        (convex_closedBall _ _) _ a
      intro b
      exact (dist_comm _ _).le.trans (dist_vertexBarycenter_le (n + 1) v _ hv)
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · refine Fin.cases ?_ (fun b ↦ ?_) j
      · change dist _ _ ≤ _
        rw [dist_self]
        positivity
      · change dist (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v)
          (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 b) ≤ _
        rw [dist_comm]
        exact hapex b
    · refine Fin.cases ?_ (fun b ↦ ?_) j
      · exact hapex a
      · change dist (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 a)
          (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2 b) ≤ _
        refine (hn (v ∘ p.1.succAbove) p.2 hface a b).trans ?_
        apply mul_le_mul_of_nonneg_right _ hD
        push_cast
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith


end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.MeshChains -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)



def affineMeshSubmodule (s : Set E) (n : ℕ) (D : ℝ) : Submodule k (((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X n) :=
  Submodule.span k {c | ∃ v : Fin (n + 1) → E, (∀ i, v i ∈ s) ∧
    (∀ i j, dist (v i) (v j) ≤ D) ∧ ∃ r : R,
      c = (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (R := R) (affineSingularSimplex v) r}


theorem affineGenerator_mem_affineMeshSubmodule {s : Set E} {n : ℕ} {D : ℝ}
    (v : Fin (n + 1) → E) (hvs : ∀ i, v i ∈ s)
    (hvD : ∀ i j, dist (v i) (v j) ≤ D) (r : R) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (R := R) (affineSingularSimplex v) r ∈
      affineMeshSubmodule R s n D :=
  Submodule.subset_span ⟨v, hvs, hvD, r, rfl⟩


theorem affineMeshSubmodule_le_comap_subdivision {s : Set E} (hs : Convex ℝ s)
    (n : ℕ) (D : ℝ) :
    affineMeshSubmodule R s n D ≤
      (affineMeshSubmodule R s n ((n : ℝ) / (n + 1) * D)).comap
        (singularSubdivisionMap R (TopCat.of E) n).hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hvs, hvD, r, rfl⟩
  change (singularSubdivisionMap R (TopCat.of E) n)
    ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (R := R) (affineSingularSimplex v) r) ∈
      affineMeshSubmodule R s n ((n : ℝ) / (n + 1) * D)
  have he := congrArg (fun f ↦ ModuleCat.Hom.hom f r)
    ((singularSubdivisionMap_affine R v).trans (affineSubdivisionMap_pieces R n v))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply] at he
  rw [he]
  apply Submodule.sum_mem
  intro p _
  apply (affineMeshSubmodule R s n ((n : ℝ) / (n + 1) * D)).toAddSubgroup.zsmul_mem
  exact affineGenerator_mem_affineMeshSubmodule R (barycentricPieceVertices n v p)
    (barycentricPieceVertices_mem n v p hs hvs)
    (dist_barycentricPieceVertices_le n v p hvD) r


theorem singularSubdivision_pow_mem_affineMeshSubmodule {s : Set E} (hs : Convex ℝ s)
    (n m : ℕ) {D : ℝ} {c : ((_root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R)).X n} (hc : c ∈ affineMeshSubmodule R s n D) :
    (End.of (singularSubdivision R (TopCat.of E)) ^ m).f n c ∈
      affineMeshSubmodule R s n (((n : ℝ) / (n + 1)) ^ m * D) := by
  induction m with
  | zero => simpa only [pow_zero, End.one_def, HomologicalComplex.id_f,
      ModuleCat.id_apply, one_mul] using hc
  | succ m hm =>
    rw [pow_succ' (End.of (singularSubdivision R (TopCat.of E))) m, End.mul_def, HomologicalComplex.comp_f, ModuleCat.comp_apply]
    have h := affineMeshSubmodule_le_comap_subdivision R hs n
      (((n : ℝ) / (n + 1)) ^ m * D) hm
    simpa only [Submodule.mem_comap, pow_succ', mul_assoc, singularSubdivision_f] using h


theorem exists_uniform_subdivision_mesh_threshold {s : Set E} (hs : Convex ℝ s)
    (n : ℕ) (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N,
      ((n : ℝ) / (n + 1)) ^ m * D < ε ∧
      ∀ c ∈ affineMeshSubmodule R s n D,
        (End.of (singularSubdivision R (TopCat.of E)) ^ m).f n c ∈
          affineMeshSubmodule R s n (((n : ℝ) / (n + 1)) ^ m * D) := by
  have hr0 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
  have hr1 : (n : ℝ) / (n + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (lt_add_one (n : ℝ))
  have ht : Filter.Tendsto (fun m : ℕ ↦ ((n : ℝ) / (n + 1)) ^ m * D)
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const D
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  exact ⟨N, fun m hm ↦ ⟨hN m hm,
    fun _ hc ↦ singularSubdivision_pow_mem_affineMeshSubmodule R hs n m hc⟩⟩

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.SmallChains.Compactness -/
section

noncomputable section

open CategoryTheory Opposite Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)
  (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

include hopen hcover

theorem exists_small_precomp_radius {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (m : ℕ)
      (τ : C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ (Fin (n + 1)))),
      (∀ a b, dist (τ a) (τ b) < δ) →
        ((X.toSSetObjEquiv (op ⦋m⦌)).symm
          ((X.toSSetObjEquiv (op ⦋n⦌) σ).comp τ)) ∈
            (smallSingularSimplices X U).obj (op ⦋m⦌) := by
  let f : C(stdSimplex ℝ (Fin (n + 1)), X) := X.toSSetObjEquiv (op ⦋n⦌) σ
  have hUopen : ∀ i, IsOpen (f ⁻¹' U i) := fun i ↦ (hopen i).preimage f.continuous
  have hUcover : Set.univ ⊆ ⋃ i, f ⁻¹' U i := by
    intro x _
    exact Set.mem_iUnion.mpr (hcover (f x))
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))))
    hUopen hUcover
  refine ⟨δ, hδ, ?_⟩
  intro m τ hτ
  let a : stdSimplex ℝ (Fin (m + 1)) :=
    ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  obtain ⟨i, hi⟩ := hball (τ a) (Set.mem_univ _)
  refine ⟨i, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact hi (hτ b a)

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.SimplexSmallness -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace DifferentialGeometry.Homology

private theorem convex_coordinateSimplex (n : ℕ) :
    Convex ℝ (ULift.down ⁻¹' stdSimplex ℝ (Fin (n + 1)) :
      Set (ULift.{u} (Fin (n + 1) → ℝ))) := by
  intro x hx y hy a b ha hb hab
  exact (convex_stdSimplex ℝ (Fin (n + 1))) hx hy ha hb hab


def affineSimplexCoordinateLift {n : ℕ} (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ stdSimplex ℝ (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ ⟨(affineSimplex v x).down,
      range_affineSimplex_subset v (convex_coordinateSimplex n) hv ⟨x, rfl⟩⟩,
    (continuous_uliftDown.comp (affineSimplex v).continuous).subtype_mk _⟩


theorem dist_affineSimplexCoordinateLift_le {n : ℕ}
    (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ stdSimplex ℝ (Fin (n + 1))) {D : ℝ}
    (hD : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : stdSimplex ℝ (Fin (n + 1))) :
    dist (affineSimplexCoordinateLift v hv x) (affineSimplexCoordinateLift v hv y) ≤ D :=
  dist_affineSimplex_le v hD x y


def affineSingularSimplexCoordinateLift {n : ℕ}
    (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ stdSimplex ℝ (Fin (n + 1))) :
    TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌) _⦋n⦌ :=
  ((SimplexCategory.toTop.obj ⦋n⦌).toSSetObjEquiv (op ⦋n⦌)).symm
    ⟨fun x ↦ ULift.up (affineSimplexCoordinateLift v hv x),
      continuous_uliftUp.comp (affineSimplexCoordinateLift v hv).continuous⟩


theorem affineSingularSimplexCoordinateLift_embedding {n : ℕ}
    (v : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ))
    (hv : ∀ i, (v i).down ∈ stdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSet.map (simplexCoordinateEmbedding n)).app (op ⦋n⦌)
        (affineSingularSimplexCoordinateLift v hv) = affineSingularSimplex v := by
  apply ((TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))).toSSetObjEquiv (op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro x
  rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem singularSubdivision_pow_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) (m : ℕ) :
    (CategoryTheory.CategoryStruct.comp ((End.of (singularSubdivision R X) ^ m)) (SSet.chainComplexMap (TopCat.toSSet.map f) R)) =
      (CategoryTheory.CategoryStruct.comp (SSet.chainComplexMap (TopCat.toSSet.map f) R) ((End.of (singularSubdivision R Y) ^ m))) := by
  induction m with
  | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
  | succ m hm =>
    rw [pow_succ' (End.of (singularSubdivision R X)) m,
      pow_succ' (End.of (singularSubdivision R Y)) m, End.mul_def, End.mul_def]
    simp only [Category.assoc]
    rw [singularSubdivision_naturality]
    rw [← Category.assoc (End.of (singularSubdivision R X) ^ m), hm]
    simp only [Category.assoc]

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

private theorem affineMeshSubmodule_le_coordinate_map {n : ℕ}
    (σ : TopCat.toSSet.obj X _⦋n⦌) {δ : ℝ}
    (hsmall : ∀ τ : C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))),
      (∀ a b, dist (τ a) (τ b) < δ) →
        ((X.toSSetObjEquiv (op ⦋n⦌)).symm ((X.toSSetObjEquiv (op ⦋n⦌) σ).comp τ)) ∈
          (smallSingularSimplices X U).obj (op ⦋n⦌)) {D : ℝ} (hDδ : D < δ) :
    affineMeshSubmodule R
      (ULift.down ⁻¹' stdSimplex ℝ (Fin (n + 1)) : Set (ULift.{u} (Fin (n + 1) → ℝ))) n D ≤
    ((LinearMap.range ((smallChainMap X U R).f n).hom).comap
      ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n).hom).map
      ((SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f n).hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hvs, hvD, r, rfl⟩
  let τ := affineSingularSimplexCoordinateLift v hvs
  have hτ : (TopCat.toSSet.map (singularSimplexMap X σ)).app (op ⦋n⦌) τ ∈
      (smallSingularSimplices X U).obj (op ⦋n⦌) := by
    change ((X.toSSetObjEquiv (op ⦋n⦌)).symm
      ((X.toSSetObjEquiv (op ⦋n⦌) σ).comp (affineSimplexCoordinateLift v hvs))) ∈ _
    exact hsmall _ (fun a b ↦ (dist_affineSimplexCoordinateLift_le v hvs hvD a b).trans_lt hDδ)
  let τsmall : (smallSingularSimplices X U : SSet) _⦋n⦌ :=
    ⟨(TopCat.toSSet.map (singularSimplexMap X σ)).app (op ⦋n⦌) τ, hτ⟩
  refine Submodule.mem_map.mpr ⟨(TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex
    (R := R) τ r, ?_, ?_⟩
  · change (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n
      ((TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex (R := R) τ r) ∈
        LinearMap.range ((smallChainMap X U R).f n).hom
    refine ⟨(smallSingularSimplices X U : SSet).ιChainComplex (R := R) τsmall r, ?_⟩
    have he : (CategoryTheory.CategoryStruct.comp ((smallSingularSimplices X U : SSet).ιChainComplex
        τsmall) ((smallChainMap X U R).f n)) =
        (CategoryTheory.CategoryStruct.comp ((TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌)).ιChainComplex τ) ((SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n)) := by
      rw [ι_smallChainMap_f, SSet.ι_chainComplexMap_f]
    exact congrArg (fun q ↦ ModuleCat.Hom.hom q r) he
  · have he := SSet.ι_chainComplexMap_f _ _
      (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R τ
    change _ = (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
      (R := R) (affineSingularSimplex v) r
    rw [show τ = affineSingularSimplexCoordinateLift v hvs from rfl,
      affineSingularSimplexCoordinateLift_embedding] at he
    exact congrArg (fun q ↦ ModuleCat.Hom.hom q r) he

theorem exists_small_subdivision_power_generator
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ r : R,
      (End.of (singularSubdivision R X) ^ m).f n
          ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ r) ∈
        LinearMap.range ((smallChainMap X U R).f n).hom := by
  let v₀ : Fin (n + 1) → ULift.{u} (Fin (n + 1) → ℝ) :=
    fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val
  let D₀ : ℝ := Metric.diam (Set.range v₀)
  have hv₀ : ∀ i, (v₀ i).down ∈ stdSimplex ℝ (Fin (n + 1)) :=
    fun i ↦ (stdSimplex.vertex (S := ℝ) i).property
  have hD₀ : ∀ i j, dist (v₀ i) (v₀ j) ≤ D₀ := fun i j ↦
    Metric.dist_le_diam_of_mem (Set.finite_range v₀).isBounded ⟨i, rfl⟩ ⟨j, rfl⟩
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_precomp_radius X U hopen hcover σ
  obtain ⟨N, hN⟩ := exists_uniform_subdivision_mesh_threshold R
    (convex_coordinateSimplex n) n D₀ hδ
  refine ⟨N, ?_⟩
  intro m hm r
  let J := SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R
  let F := SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R
  let c := (End.of (singularSubdivision R (SimplexCategory.toTop.obj ⦋n⦌)) ^ m).f n
    (fundamentalSimplexChain R n r)
  have hJfund : (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) (J.f n)) =
      (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
        (R := R) (affineSingularSimplex v₀) := by
    change (CategoryTheory.CategoryStruct.comp (fundamentalSimplexChain R n) ((SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f n)) = _
    rw [← singularSimplexMap_coordinateVertices, fundamentalSimplexChain_pushforward]
  have hJc : J.f n c =
      (End.of (singularSubdivision R (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))) ^ m).f n
        ((TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
          (R := R) (affineSingularSimplex v₀) r) := by
    have hn := HomologicalComplex.congr_hom
      (singularSubdivision_pow_naturality R (simplexCoordinateEmbedding n) m) n
    have he := congrArg (fun q ↦ ModuleCat.Hom.hom q (fundamentalSimplexChain R n r)) hn
    change J.f n c =
      (End.of (singularSubdivision R (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))) ^ m).f n
        (J.f n (fundamentalSimplexChain R n r)) at he
    rw [show J.f n (fundamentalSimplexChain R n r) =
      (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
        (R := R) (affineSingularSimplex v₀) r from
      congrArg (fun q ↦ ModuleCat.Hom.hom q r) hJfund] at he
    exact he
  have hmesh : J.f n c ∈ affineMeshSubmodule R
      (ULift.down ⁻¹' stdSimplex ℝ (Fin (n + 1)) : Set (ULift.{u} (Fin (n + 1) → ℝ)))
      n (((n : ℝ) / (n + 1)) ^ m * D₀) := by
    rw [hJc]
    exact (hN m hm).2 _ (affineGenerator_mem_affineMeshSubmodule R v₀ hv₀ hD₀ r)
  have himage := affineMeshSubmodule_le_coordinate_map R X U σ (hsmall n)
    (hN m hm).1 hmesh
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.mp himage
  have hJmono : Mono (J.f n) := mono_simplexCoordinateEmbedding_chainMap_f R n n
  have hac' : a = c := (ModuleCat.mono_iff_injective (J.f n)).mp hJmono hac
  subst a
  have hFfund := fundamentalSimplexChain_pushforward R X σ
  have hn := HomologicalComplex.congr_hom
    (singularSubdivision_pow_naturality R (singularSimplexMap X σ) m) n
  have he := congrArg (fun q ↦ ModuleCat.Hom.hom q (fundamentalSimplexChain R n r)) hn
  change F.f n c = (End.of (singularSubdivision R X) ^ m).f n
    (F.f n (fundamentalSimplexChain R n r)) at he
  rw [show F.f n (fundamentalSimplexChain R n r) =
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ r from
      congrArg (fun q ↦ ModuleCat.Hom.hom q r) hFfund] at he
  rw [← he]
  exact ha

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.Subdivision.EventualSmallness -/
section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)


private def eventuallySmallChainSubmodule (n : ℕ) : Submodule k (((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n) where
  carrier := {c | ∃ N : ℕ, ∀ m ≥ N,
    (End.of (singularSubdivision R X) ^ m).f n c ∈
      LinearMap.range ((smallChainMap X U R).f n).hom}
  zero_mem' := ⟨0, fun _ _ ↦ by rw [map_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro c d ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun m hm ↦ ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (hN m ((le_max_left _ _).trans hm))
      (hM m ((le_max_right _ _).trans hm))
  smul_mem' := by
    rintro a c ⟨N, hN⟩
    refine ⟨N, fun m hm ↦ ?_⟩
    rw [map_smul]
    exact Submodule.smul_mem _ a (hN m hm)

private theorem singularChain_submodule_eq_top {n : ℕ} (P : Submodule k (((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n))
    (hP : ∀ (σ : TopCat.toSSet.obj X _⦋n⦌) (r : R),
      (TopCat.toSSet.obj X).ιChainComplex (R := R) σ r ∈ P) : P = ⊤ := by
  let q : ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n ⟶ ModuleCat.of k ((((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n) ⧸ P) := ModuleCat.ofHom P.mkQ
  have hq : q = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change P.mkQ ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ r) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hP σ r)
  apply top_unique
  intro c _
  have hc := congrArg (fun f ↦ ModuleCat.Hom.hom f c) hq
  exact (Submodule.Quotient.mk_eq_zero P).mp hc

theorem exists_eventually_small_subdivision_power
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (n : ℕ) (c : ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n) :
    ∃ N : ℕ, ∀ m ≥ N,
      (End.of (singularSubdivision R X) ^ m).f n c ∈
        LinearMap.range ((smallChainMap X U R).f n).hom := by
  have htop : eventuallySmallChainSubmodule R X U n = ⊤ := by
    apply singularChain_submodule_eq_top
    intro σ r
    obtain ⟨N, hN⟩ := exists_small_subdivision_power_generator R X U hopen hcover σ
    exact ⟨N, fun m hm ↦ hN m hm r⟩
  have hc : c ∈ eventuallySmallChainSubmodule R X U n := by rw [htop]; trivial
  exact hc

theorem exists_small_subdivision_power
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (n : ℕ) (c : ((_root_.SSet.chainComplex (TopCat.toSSet.obj X) R)).X n) :
    ∃ N : ℕ, (End.of (singularSubdivision R X) ^ N).f n c ∈
      LinearMap.range ((smallChainMap X U R).f n).hom := by
  obtain ⟨N, hN⟩ := exists_eventually_small_subdivision_power R X U hopen hcover n c
  exact ⟨N, hN N le_rfl⟩

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso -/
section

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem quasiIso_smallChainMap
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (smallChainMap X U R) := by
  let := mono_smallChainMap X U R
  apply DifferentialGeometry.HomologicalComplex.quasiIso_of_eventually_in_image (smallChainMap X U R)
    (smallSingularSubdivision X U R) (End.of (singularSubdivision R X))
    (smallSingularSubdivision_inclusion X U R).symm
    (singularSubdivisionHomotopy R X) (smallSingularSubdivisionHomotopyMap X U R)
  · intro n
    rw [singularSubdivisionHomotopy_hom]
    exact (smallSingularSubdivisionHomotopyMap_inclusion X U R n).symm
  · exact exists_small_subdivision_power R X U hopen hcover


def smallChainHomologyIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    ((smallSingularSimplices X U : SSet).chainComplex R).homology n ≅
      ((TopCat.toSSet.obj X).chainComplex R).homology n := by
  letI := quasiIso_smallChainMap X U R hopen hcover
  exact isoOfQuasiIsoAt (smallChainMap X U R) n


@[simp]
theorem smallChainHomologyIso_hom
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (smallChainHomologyIso X U R hopen hcover n).hom =
      _root_.HomologicalComplex.homologyMap (smallChainMap X U R) n := rfl

end DifferentialGeometry.Homology
end
end


/- DifferentialGeometry.Topology.SimplicialSet.ChainColimits -/
section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
noncomputable section
universe u
namespace DifferentialGeometry.SSet
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


instance chainComplexFunctor_preservesColimits :
    PreservesColimitsOfSize.{u, u} ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R) where
  preservesColimitsOfShape {J _} := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌) ⋙ sigmaConst.obj R)
    infer_instance


instance chainComplexFunctor_preservesMonomorphisms :
    ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).PreservesMonomorphisms where
  preserves f _ := by
    dsimp [_root_.SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
    apply +allowSynthFailures Functor.map_mono
    dsimp [_root_.SSet, SimplicialObject.whiskering, SimplicialObject]
    infer_instance

end DifferentialGeometry.SSet
end
end


/- DifferentialGeometry.Topology.Homology.Algebra.PushoutExact -/
section

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DifferentialGeometry.ShortComplex
variable {C : Type*} [Category* C] [Abelian C]
  {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}
  (sq : IsPushout f g r s)


end DifferentialGeometry.ShortComplex
end
end


/- DifferentialGeometry.Topology.SimplicialSet.UnionChains -/
section

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
namespace DifferentialGeometry.SSet
variable {X : _root_.SSet.{u}} (A B : X.Subcomplex)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem unionChainSquare :
    IsPushout
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ B from inf_le_right)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ≤ A ⊔ B from le_sup_left)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) := by
  have sq : _root_.SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  exact ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_isPushout sq.isPushout


def unionRelativeChainIso :
    cokernel (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R) ≅
    cokernel (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) := by
  let sq := unionChainSquare A B R
  have := isIso_cokernel_map_of_isPushout sq
  exact asIso (cokernel.map _ _ _ _ sq.w)


@[simp]
theorem unionRelativeChainIso_projection :
    (CategoryTheory.CategoryStruct.comp (cokernel.π (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R)) ((unionRelativeChainIso A B R).hom)) =
      (CategoryTheory.CategoryStruct.comp (_root_.SSet.chainComplexMap
        (_root_.SSet.Subcomplex.homOfLE (show A ≤ A ⊔ B from le_sup_left)) R) (cokernel.π (_root_.SSet.chainComplexMap
        (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R))) :=
  cokernel.π_desc _ _ _

end DifferentialGeometry.SSet
end
end


/- DifferentialGeometry.Topology.Homology.SmallChains.Union -/
section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s t : Set X)


def twoSetFamily : Bool → Set X := fun b => if b then s else t


theorem smallSingularSimplices_inter :
    smallSingularSimplices X (fun _ : Unit => s ∩ t) =
      smallSingularSimplices X (fun _ : Unit => s) ⊓
        smallSingularSimplices X (fun _ : Unit => t) := by
  ext n σ
  change (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s ∩ t) ↔
    ((∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s) ∧
      (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ t))
  simp only [exists_const, Set.subset_inter_iff]


theorem smallSingularSimplices_twoSet :
    smallSingularSimplices X (twoSetFamily X s t) =
      smallSingularSimplices X (fun _ : Unit => s) ⊔
        smallSingularSimplices X (fun _ : Unit => t) := by
  ext n σ
  change (∃ b : Bool, Set.range (X.toSSetObjEquiv n σ) ⊆ twoSetFamily X s t b) ↔
    ((∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s) ∨
      (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ t))
  simp only [exists_const, Bool.exists_bool, twoSetFamily, Bool.false_eq_true,
    if_false, if_true, or_comm]


def subspaceInclusion {s t : Set X} (h : s ⊆ t) : TopCat.of s ⟶ TopCat.of t :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩


def firstSubspaceToSmall : TopCat.toSSet.obj (TopCat.of s) ⟶
    (smallSingularSimplices X (twoSetFamily X s t) : SSet) :=
  (CategoryTheory.CategoryStruct.comp ((singularSubspaceIso X s).hom) (SSet.Subcomplex.homOfLE
    (smallSingularSimplices_le X (fun _ : Unit => s) (twoSetFamily X s t)
      (fun _ => ⟨true, Set.Subset.rfl⟩))))


def secondSubspaceToSmall : TopCat.toSSet.obj (TopCat.of t) ⟶
    (smallSingularSimplices X (twoSetFamily X s t) : SSet) :=
  (CategoryTheory.CategoryStruct.comp ((singularSubspaceIso X t).hom) (SSet.Subcomplex.homOfLE
    (smallSingularSimplices_le X (fun _ : Unit => t) (twoSetFamily X s t)
      (fun _ => ⟨false, Set.Subset.rfl⟩))))


@[simp]
theorem firstSubspaceToSmall_ι :
    (CategoryTheory.CategoryStruct.comp (firstSubspaceToSmall X s t) ((smallSingularSimplices X (twoSetFamily X s t)).ι)) =
      TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := rfl


@[simp]
theorem secondSubspaceToSmall_ι :
    (CategoryTheory.CategoryStruct.comp (secondSubspaceToSmall X s t) ((smallSingularSimplices X (twoSetFamily X s t)).ι)) =
      TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X))) := rfl


theorem subspaceSmallSquare :
    IsPushout (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)))
      (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right)))
      (firstSubspaceToSmall X s t) (secondSubspaceToSmall X s t) := by
  let A := smallSingularSimplices X (fun _ : Unit => s)
  let B := smallSingularSimplices X (fun _ : Unit => t)
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  apply sq.isPushout.of_iso'
    (singularSubspaceIso X (s ∩ t) ≪≫ SSet.Subcomplex.eqToIso (smallSingularSimplices_inter X s t))
    (singularSubspaceIso X s) (singularSubspaceIso X t)
    (SSet.Subcomplex.eqToIso (smallSingularSimplices_twoSet X s t))
  all_goals
    ext n σ
    apply Subtype.ext
    rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


end DifferentialGeometry.Homology
end
end


/-! Transport singular-chain calculations from integral modules to abelian groups. -/

open CategoryTheory CategoryTheory.Limits Simplicial

noncomputable section

namespace PoincareExcision

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasCoproducts.{0} C] [HasCoproducts.{0} D]
    (F : C ⥤ D) [F.Additive] [PreservesColimitsOfSize.{0, 0} F] (R : C)

private def coefficientIsoAt (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (F.obj R)).X n ≅ F.obj ((X.chainComplex R).X n) :=
  (PreservesCoproduct.iso F (fun (_ : X _⦋n⦌) ↦ R)).symm

private theorem coefficientIsoAt_ι (X : SSet.{0}) {n : ℕ} (σ : X _⦋n⦌) :
    CategoryStruct.comp (X.ιChainComplex (R := F.obj R) σ) (coefficientIsoAt F R X n).hom =
      F.map (X.ιChainComplex (R := R) σ) := by
  change CategoryStruct.comp (Sigma.ι _ σ)
    (PreservesCoproduct.iso F (fun (_ : X _⦋n⦌) ↦ R)).inv = _
  simp [SSet.ιChainComplex] <;> rfl

def chainCoefficientIso (X : SSet.{0}) :
    X.chainComplex (F.obj R) ≅ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (X.chainComplex R) :=
  HomologicalComplex.Hom.isoOfComponents (coefficientIsoAt F R X) (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    apply SSet.chainComplex_hom_ext
    intro σ
    change CategoryStruct.comp (X.ιChainComplex σ)
      (CategoryStruct.comp (coefficientIsoAt F R X (j + 1)).hom
        (F.map ((X.chainComplex R).d (j + 1) j))) =
      CategoryStruct.comp (X.ιChainComplex σ)
        (CategoryStruct.comp ((X.chainComplex (F.obj R)).d (j + 1) j)
          (coefficientIsoAt F R X j).hom)
    rw [← Category.assoc, coefficientIsoAt_ι, ← F.map_comp, SSet.ιChainComplex_d,
      F.map_sum, ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [Preadditive.zsmul_comp, coefficientIsoAt_ι, F.map_zsmul])

theorem chainCoefficientIso_naturality {X Y : SSet.{0}} (f : X ⟶ Y) :
    CategoryStruct.comp (SSet.chainComplexMap f (F.obj R)) (chainCoefficientIso F R Y).hom =
      CategoryStruct.comp (chainCoefficientIso F R X).hom
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (SSet.chainComplexMap f R)) := by
  ext n : 1
  apply SSet.chainComplex_hom_ext
  intro σ
  change CategoryStruct.comp (X.ιChainComplex σ)
    (CategoryStruct.comp ((SSet.chainComplexMap f (F.obj R)).f n)
      (coefficientIsoAt F R Y n).hom) =
    CategoryStruct.comp (X.ιChainComplex σ)
      (CategoryStruct.comp (coefficientIsoAt F R X n).hom (F.map ((SSet.chainComplexMap f R).f n)))
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, coefficientIsoAt_ι,
    ← Category.assoc, coefficientIsoAt_ι, ← F.map_comp, SSet.ι_chainComplexMap_f]

theorem quasiIso_chainComplexMap_abelian_of_integral {X Y : SSet.{0}} (f : X ⟶ Y)
    (h : QuasiIso (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ))) :
    QuasiIso (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)) := by
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat.{0}
  let R := ModuleCat.of ℤ ℤ
  let G := F.mapHomologicalComplex (ComplexShape.down ℕ)
  let : QuasiIso (SSet.chainComplexMap f R) := h
  let : QuasiIso (G.map (SSet.chainComplexMap f R)) := by infer_instance
  change QuasiIso (SSet.chainComplexMap f (F.obj R))
  have hmap : SSet.chainComplexMap f (F.obj R) =
      CategoryStruct.comp (chainCoefficientIso F R X).hom
        (CategoryStruct.comp (G.map (SSet.chainComplexMap f R)) (chainCoefficientIso F R Y).inv) := by
    rw [← Category.assoc, ← chainCoefficientIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hmap]
  infer_instance

end PoincareExcision

end

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open DifferentialGeometry.Homology

noncomputable section

namespace PoincareExcision

private def includeSet {X : Type} [TopologicalSpace X] {U V : Set X}
    (h : U ⊆ V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

private def subspaceWithin {X : Type} [TopologicalSpace X] {U V : Set X}
    (h : U ⊆ V) : U ≃ₜ ((Subtype.val : V → X) ⁻¹' U) where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private abbrev ordinaryChains :=
  (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)

private theorem abelianChains_preserveColimits (R : AddCommGrpCat.{0}) :
    PreservesColimitsOfSize.{0, 0} ((SSet.chainComplexFunctor AddCommGrpCat.{0}).obj R) where
  preservesColimitsOfShape {J _} := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    change PreservesColimitsOfShape J
      ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R)
    infer_instance

theorem quasiIso_openUnion {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (h : CategoryStruct.comp
        (ordinaryChains.map (includeSet (Set.inter_subset_left (s := U) (t := V))))
        (ordinaryChains.map (includeSet (Set.subset_union_left (s := U) (t := V)))) =
      CategoryStruct.comp
        (ordinaryChains.map (includeSet (Set.inter_subset_right (s := U) (t := V))))
        (ordinaryChains.map (includeSet (Set.subset_union_right (s := U) (t := V))))) :
    QuasiIso (pushout.desc
      (ordinaryChains.map (includeSet (Set.subset_union_left (s := U) (t := V))))
      (ordinaryChains.map (includeSet (Set.subset_union_right (s := U) (t := V)))) h) := by
  let Z := TopCat.of (U ∪ V : Set X)
  let A : Set Z := (Subtype.val : Z → X) ⁻¹' U
  let B : Set Z := (Subtype.val : Z → X) ⁻¹' V
  let P := smallSingularSimplices Z (twoSetFamily Z A B)
  let E := TopCat.toSSet
  let eU : E.obj (TopCat.of U) ≅ E.obj (TopCat.of A) :=
    E.mapIso (TopCat.isoOfHomeo (subspaceWithin Set.subset_union_left))
  let eV : E.obj (TopCat.of V) ≅ E.obj (TopCat.of B) :=
    E.mapIso (TopCat.isoOfHomeo (subspaceWithin Set.subset_union_right))
  let eI : E.obj (TopCat.of (U ∩ V : Set X)) ≅ E.obj (TopCat.of (A ∩ B : Set Z)) :=
    E.mapIso (TopCat.isoOfHomeo (subspaceWithin (Set.inter_subset_left.trans Set.subset_union_left)))
  let l := eU.hom ≫ firstSubspaceToSmall Z A B
  let r := eV.hom ≫ secondSubspaceToSmall Z A B
  have hs : IsPushout
      (E.map (includeSet (Set.inter_subset_left (s := U) (t := V))))
      (E.map (includeSet (Set.inter_subset_right (s := U) (t := V)))) l r := by
    apply (subspaceSmallSquare Z A B).of_iso' eI eU eV (Iso.refl _)
    all_goals
      ext n σ
      first | rfl | (apply Subtype.ext; rfl)
  have hl : CategoryStruct.comp l P.ι =
      E.map (includeSet (Set.subset_union_left (s := U) (t := V))) := by
    dsimp [l, P]
    rw [Category.assoc, firstSubspaceToSmall_ι]
    change CategoryStruct.comp (E.map _) (E.map _) = E.map _
    rw [← E.map_comp]
    rfl
  have hr : CategoryStruct.comp r P.ι =
      E.map (includeSet (Set.subset_union_right (s := U) (t := V))) := by
    dsimp [r, P]
    rw [Category.assoc, secondSubspaceToSmall_ι]
    change CategoryStruct.comp (E.map _) (E.map _) = E.map _
    rw [← E.map_comp]
    rfl
  have hOpen : ∀ i, IsOpen (twoSetFamily Z A B i) := by
    intro i
    cases i
    · simpa [twoSetFamily] using hV.preimage (continuous_subtype_val : Continuous (Subtype.val : Z → X))
    · simpa [twoSetFamily] using hU.preimage (continuous_subtype_val : Continuous (Subtype.val : Z → X))
  have hCover : ∀ z : Z, ∃ i, z ∈ twoSetFamily Z A B i := by
    intro z
    rcases z.property with h | h
    · exact ⟨true, by change z ∈ A; exact h⟩
    · exact ⟨false, by change z ∈ B; exact h⟩
  let F := (SSet.chainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
  let : PreservesColimitsOfSize.{0, 0} F := abelianChains_preserveColimits _
  have hp := F.map_isPushout hs
  have hi : QuasiIso (F.map P.ι) :=
    quasiIso_chainComplexMap_abelian_of_integral P.ι
      (quasiIso_smallChainMap Z (twoSetFamily Z A B) (ModuleCat.of ℤ ℤ) hOpen hCover)
  let i := ordinaryChains.map (includeSet (Set.inter_subset_left (s := U) (t := V)))
  let j := ordinaryChains.map (includeSet (Set.inter_subset_right (s := U) (t := V)))
  let e : F.obj P.toSSet ≅ pushout i j := hp.isoPushout
  have heq : CategoryStruct.comp e.inv (F.map P.ι) =
      pushout.desc
        (ordinaryChains.map (includeSet (Set.subset_union_left (s := U) (t := V))))
        (ordinaryChains.map (includeSet (Set.subset_union_right (s := U) (t := V)))) h := by
    change CategoryStruct.comp hp.isoPushout.inv (F.map P.ι) = _
    apply pushout.hom_ext
    · rw [← Category.assoc, IsPushout.inl_isoPushout_inv, ← F.map_comp, hl]
      exact (pushout.inl_desc _ _ _).symm
    · rw [← Category.assoc, IsPushout.inr_isoPushout_inv, ← F.map_comp, hr]
      exact (pushout.inr_desc _ _ _).symm
  rw [← heq]
  let : QuasiIso (F.map P.ι) := hi
  let : QuasiIso e.inv := by infer_instance
  exact quasiIso_comp e.inv (F.map P.ι)

end PoincareExcision

end

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro X _ U V hU hV
  refine PoincareExcision.quasiIso_openUnion U V hU hV ?_
