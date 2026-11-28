import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Algebra.BigOperators.Field
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UnitInterval

/-!
# Smooth leaf fields near a finite three-complex

Adapted from the PoincareLib contributors' PoincareMT M76 formalization
at LehengChen/PoincareConjecture commit `60de1a94ca7038d04ed123b490a3229f8aa5fa75`.
Copyright (c) 2026 the PoincareLib contributors. Licensed under Apache 2.0.
This file consolidates the dependency modules of `exists_smoothLeafField_near_space`,
scopes each original module body, removes per-file `autoImplicit` settings, and replaces
the plane extensionality attribute with an explicit lemma. The final adapter identifies
the registered plane spaces and extracts the required local projection maps.
See Cairns (1940), pp. 803–805 and 807, and M76 derivation 65.
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


-- Source: PoincareMT/Proofs/M76/Mathlib/OrthogonalKernelProjection.lean
section

/-!
# Orthogonal projectors onto surjective kernels

The kernel of a surjective operator varies continuously in the actual
orthogonal-projector coordinates of planes. The projector is computed
as `I - Q* (Q Q*)⁻¹ Q`. This is the topology calculation for Cairns
1940, Section 4, p. 800, and Lemma 5.1, p. 801; see M76 derivation 28.
-/


open Set

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- A surjective operator has invertible adjoint Gram operator on its
target, including when the target is zero-dimensional.
See Cairns p. 801 and M76 derivation 28. -/
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

/-- The totalized formula for a kernel projector. Its interpretation
as the orthogonal projector requires surjectivity.
See Cairns p. 801 and M76 derivation 28. -/
noncomputable def kernelProjectionFormula (Q : E →L[ℝ] F) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ((adjoint Q).comp (Q.comp (adjoint Q)).inverse).comp Q

/-- The Gram formula is the geometric orthogonal projector onto the
kernel. See Cairns pp. 800--801 and M76 derivation 28. -/
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

/-- The projector formula is continuous at every surjective map.
Invertibility of the Gram operator is checked before invoking smooth
operator inversion. See Cairns p. 801 and M76 derivation 28. -/
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

/-- Kernels vary continuously on the surjective locus in orthogonal
projector coordinates. No continuity is asserted across a rank drop.
See Cairns p. 800 and M76 derivation 28. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/FrameProjectionFormula.lean
section

/-!
# Recovering normalized projections from their kernels

For a fixed frame inclusion, the normalized projection is recovered
continuously from the orthogonal projector onto its kernel. This is
the inverse coordinate calculation in Cairns 1940, Lemma 5.1, p. 801;
see M76 derivation 28. No orthonormality of the fixed frame is assumed.
-/


namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The Gram operator of an injective frame is invertible.
See Cairns p. 801 and M76 derivation 28. -/
theorem isInvertible_adjoint_comp_self_of_injective (J : F →L[ℝ] E)
    (hJ : Function.Injective J) : ((adjoint J).comp J).IsInvertible := by
  have hker : ((adjoint J).comp J).ker = ⊥ := by
    rw [ker_adjoint_comp_self, LinearMap.ker_eq_bot.mpr hJ]
  have hinj : Function.Injective ((adjoint J).comp J) := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective ((adjoint J).comp J) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective ((adjoint J).comp J) hker
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

/-- The frame followed by orthogonal projection away from a proposed
kernel. See Cairns p. 801 and M76 derivation 28. -/
def perpendicularFrame (J : F →L[ℝ] E) (P : E →L[ℝ] E) : F →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ E - P).comp J

/-- The normalized projection formula associated with a kernel
projector. It has geometric meaning when the perpendicular frame is
injective. See Cairns p. 801 and M76 derivation 28. -/
noncomputable def frameProjectionFormula (J : F →L[ℝ] E) (P : E →L[ℝ] E) : E →L[ℝ] F :=
  (((adjoint (perpendicularFrame J P)).comp (perpendicularFrame J P)).inverse.comp
    (adjoint (perpendicularFrame J P))).comp (ContinuousLinearMap.id ℝ E - P)

omit [FiniteDimensional ℝ F] in
/-- A right inverse remains injective after orthogonal projection
away from the corresponding kernel.
See Cairns p. 801 and M76 derivation 28. -/
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

/-- Recover a normalized projection from its geometric kernel
projector. The frame need not be orthonormal.
See Cairns p. 801 and M76 derivation 28. -/
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

/-- The inverse formula varies continuously wherever the projected
frame is independent. See Cairns p. 801 and M76 derivation 28. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/PlaneProjectionSmoothness.lean
section

/-!
# Smoothness of the geometric kernel and frame coordinates

The checked Gram formulas are smooth on their natural invertibility
loci. This permits assembly of smooth plane fields independently
of any single frame. See Cairns 1940, pp. 800--801, 804--805 and
M76 derivation 60.
-/


open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The kernel-projector formula is smooth at every surjective
operator. See Cairns pp. 800--801 and M76 derivation 60. -/
theorem contDiffAt_kernelProjectionFormula (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) {n : ℕ∞ω} :
    ContDiffAt ℝ n (kernelProjectionFormula : (E →L[ℝ] F) → E →L[ℝ] E) Q := by
  have hadj : ContDiffAt ℝ n (adjoint : (E →L[ℝ] F) → F →L[ℝ] E) Q :=
    (adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E)).toContinuousLinearEquiv.contDiff.contDiffAt
  have hS : ContDiffAt ℝ n (fun R : E →L[ℝ] F => R.comp (adjoint R)) Q :=
    contDiffAt_id.clm_comp hadj
  have hi := (Q.isInvertible_self_comp_adjoint_of_surjective hQ).contDiffAt_map_inverse.comp Q hS
  exact contDiffAt_const.sub ((hadj.clm_comp hi).clm_comp contDiffAt_id)

/-- The fixed-frame projection formula is smooth where the
perpendicular frame is injective. See Cairns p. 801 and M76 derivation 60. -/
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

/-- Smooth surjective operator fields have smooth geometric
kernel projectors on the same domain. No rank-drop claim is made.
See Cairns pp. 800--801, 804 and M76 derivation 60. -/
theorem ContDiffOn.ker_starProjection {Q : X → E →L[ℝ] F} {U : Set X} {n : ℕ∞ω}
    (hQ : ContDiffOn ℝ n Q U) (hsurj : ∀ x ∈ U, Function.Surjective (Q x)) :
    ContDiffOn ℝ n (fun x => (Q x).ker.starProjection) U := by
  have hreg : ContDiffOn ℝ n (fun x => (Q x).kernelProjectionFormula) U :=
    fun x hx => ((Q x).contDiffAt_kernelProjectionFormula (hsurj x hx)).comp_contDiffWithinAt
      x (hQ x hx)
  exact hreg.congr (fun x hx => (Q x).starProjection_ker_eq_formula (hsurj x hx))

end

-- Source: PoincareMT/Proofs/M76/Mathlib/BasisEvaluation.lean
section

/-!
# Operator coordinates given by a finite basis

Evaluation on a finite basis identifies continuous linear maps with
their tuples of vertex values in the actual operator and product
topologies. This is the linear-coordinate calculation in Cairns 1940,
pp. 799, 801; see M76 derivation 25.
-/


namespace Module.Basis

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear map is continuously determined by its values
on a finite basis. See Cairns pp. 799, 801 and M76 derivation 25. -/
noncomputable def evaluationContinuousLinearEquiv (b : Basis ι 𝕜 E) :
    (E →L[𝕜] F) ≃L[𝕜] (ι → F) :=
  (b.equivFunL.arrowCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans
    (ContinuousLinearEquiv.piRing ι)

/-- The operator coordinate indexed by `i` is evaluation at `b i`.
See Cairns p. 799 and M76 derivation 25. -/
@[simp] theorem evaluationContinuousLinearEquiv_apply (b : Basis ι 𝕜 E)
    (Q : E →L[𝕜] F) (i : ι) : b.evaluationContinuousLinearEquiv Q i = Q (b i) := by
  change Q (b.equivFunL.symm (Pi.single i 1)) = Q (b i)
  congr 1
  apply b.equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j
  simp only [equivFunL_apply, repr_self_apply, Pi.single_apply, eq_comm]

/-- The inverse operator has exactly the prescribed basis values.
See Cairns p. 799 and M76 derivation 25. -/
@[simp] theorem evaluationContinuousLinearEquiv_symm_apply_basis (b : Basis ι 𝕜 E)
    (v : ι → F) (i : ι) : b.evaluationContinuousLinearEquiv.symm v (b i) = v i := by
  rw [← evaluationContinuousLinearEquiv_apply]
  exact congrFun (b.evaluationContinuousLinearEquiv.apply_symm_apply v) i

end Module.Basis

end

-- Source: PoincareMT/Proofs/M76/Mathlib/EuclideanPlaneTopology.lean
section

/-!
# Euclidean subspaces in orthogonal-projector topology

Subspaces are topologized by their actual orthogonal projectors, the
basis-independent version of direction-cosine coordinates. This is
the plane topology of Cairns 1940, Section 4, p. 800; see M76 derivation
28. No topology is transported from normalized projection operators.
-/


namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A linear subspace, wrapped to specify its geometric plane
topology without assigning a global topology to all submodules.
See Cairns p. 800 and M76 derivation 28. -/
structure EuclideanSubspace where
  /-- The underlying linear subspace; see Cairns p. 800. -/
  subspace : Submodule ℝ E

variable {E} in
/-- The underlying submodule determines the wrapped plane. -/
theorem EuclideanSubspace.ext {U V : EuclideanSubspace E} (h : U.subspace = V.subspace) : U = V := by
  cases U
  cases V
  cases h
  rfl

variable [FiniteDimensional ℝ E]

/-- The topology induced by orthogonal projectors, equivalently by
their matrices in any fixed orthonormal basis.
See Cairns p. 800 and M76 derivation 28. -/
noncomputable instance EuclideanSubspace.instTopologicalSpace :
    TopologicalSpace (EuclideanSubspace E) :=
  TopologicalSpace.induced (fun K : EuclideanSubspace E => K.subspace.starProjection)
    inferInstance

/-- The geometric projector coordinate map is continuous by the
specified plane topology. See Cairns p. 800 and M76 derivation 28. -/
theorem EuclideanSubspace.continuous_projector :
    Continuous (fun K : EuclideanSubspace E => K.subspace.starProjection) :=
  continuous_induced_dom

variable {E}

/-- A plane-valued family is continuous exactly when its orthogonal
projectors are continuous. See Cairns p. 800 and M76 derivation 28. -/
theorem EuclideanSubspace.continuous_iff_projector {X : Type*} [TopologicalSpace X]
    {f : X → EuclideanSubspace E} :
    Continuous f ↔ Continuous (fun x => (f x).subspace.starProjection) :=
  continuous_induced_rng

/-- Orthogonal projectors determine their subspaces, so the plane
coordinates are faithful. See Cairns p. 800 and M76 derivation 28. -/
theorem EuclideanSubspace.projector_injective :
    Function.Injective (fun K : EuclideanSubspace E => K.subspace.starProjection) := by
  intro K L he
  apply EuclideanSubspace.ext
  have h := congrArg (fun Q : E →L[ℝ] E => Q.range) he
  simpa only [Submodule.range_starProjection] using h

/-- The geometric plane topology is exactly convergence of all
projector matrix coordinates in any finite basis. In an orthonormal
basis these are direction-cosine coordinates.
See Cairns p. 800 and M76 derivation 28. -/
theorem EuclideanSubspace.continuous_iff_projector_coordinates
    {ι X : Type*} [Finite ι] [TopologicalSpace X] (b : Module.Basis ι ℝ E)
    {f : X → EuclideanSubspace E} :
    Continuous f ↔ ∀ i j, Continuous (fun x => b.repr ((f x).subspace.starProjection (b i)) j) := by
  classical
  let := Fintype.ofFinite ι
  rw [continuous_iff_projector]
  constructor
  · intro h i j
    exact (continuous_apply j).comp (b.equivFunL.continuous.comp (h.clm_apply continuous_const))
  · intro h
    have hvec : ∀ i, Continuous (fun x => (f x).subspace.starProjection (b i)) := by
      intro i
      have hc : Continuous (fun x => b.equivFunL ((f x).subspace.starProjection (b i))) :=
        continuous_pi (fun j => h i j)
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
        b.equivFunL.symm.continuous.comp hc
    have he : Continuous (fun x => b.evaluationContinuousLinearEquiv
        (f x).subspace.starProjection) := by
      apply continuous_pi
      intro i
      simpa only [Module.Basis.evaluationContinuousLinearEquiv_apply] using hvec i
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
      b.evaluationContinuousLinearEquiv.symm.continuous.comp he

end Geometry

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SmoothPlaneLeaves.lean
section

/-!
# Smooth affine-leaf fields in geometric plane coordinates

Smoothness is measured by the actual orthogonal projectors; local
constancy is along the assigned affine planes. Thus local normalized
operators supply the invariant without a global frame. See Cairns
1940, pp. 800--801, 804--805 and M76 derivation 60.
-/


open Set Filter
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A smooth geometric plane field that is locally constant along
each assigned affine plane. Rank and transversality are separate
requirements. See Cairns Hypotheses III--IV, p. 804 and M76 derivation 60. -/
structure IsSmoothLeafFieldOn (P : E → EuclideanSubspace E) (U : Set E) : Prop where
  /-- Smoothness in the actual projector coordinates; Cairns pp. 800, 804. -/
  contDiffOn_projector : ContDiffOn ℝ ∞ (fun x => (P x).subspace.starProjection) U
  /-- The geometric field is constant locally along each leaf; Cairns p. 804. -/
  eventually_eq : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, y - x ∈ (P x).subspace → P y = P x

/-- A constant plane gives a smooth affine-leaf field on every
domain. See Cairns initial step, p. 804 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.const (P : EuclideanSubspace E) (U : Set E) :
    IsSmoothLeafFieldOn (fun _ => P) U :=
  ⟨contDiffOn_const, fun _ _ => Eventually.of_forall (fun _ _ => rfl)⟩

/-- Restricting the ambient domain preserves the smooth leaf
invariant. See Cairns pp. 804--805 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.mono {P : E → EuclideanSubspace E} {U V : Set E}
    (hP : IsSmoothLeafFieldOn P U) (hVU : V ⊆ U) : IsSmoothLeafFieldOn P V :=
  ⟨hP.contDiffOn_projector.mono hVU, fun x hx => hP.eventually_eq x (hVU hx)⟩

/-- A smooth geometric leaf field is continuous in the actual
plane topology. See Cairns pp. 800, 804 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.continuousOn {P : E → EuclideanSubspace E} {U : Set E}
    (hP : IsSmoothLeafFieldOn P U) : ContinuousOn P U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_iff_projector.mpr hP.contDiffOn_projector.continuousOn.domRestrict

/-- Equal fields on an open domain have the same smooth leaf
invariant, irrespective of their total values outside it.
See Cairns pp. 804--805 and M76 derivation 60. -/
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

/-- Smooth leaf regularity is local on a union of open ambient
domains. See Cairns pp. 804--805 and M76 derivation 60. -/
theorem IsSmoothLeafFieldOn.union {P : E → EuclideanSubspace E} {U V : Set E}
    (hPU : IsSmoothLeafFieldOn P U) (hPV : IsSmoothLeafFieldOn P V)
    (hU : IsOpen U) (hV : IsOpen V) : IsSmoothLeafFieldOn P (U ∪ V) := by
  refine ⟨hPU.contDiffOn_projector.union_of_isOpen hPV.contDiffOn_projector hU hV, ?_⟩
  rintro x (hx | hx)
  · exact hPU.eventually_eq x hx
  · exact hPV.eventually_eq x hx

/-- A smooth surjective operator field locally constant on its
kernel leaves supplies a smooth geometric plane field. Its
coordinate frame need only be local. See Cairns pp. 800--801,
804--805 and M76 derivation 60. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialSimplex.lean
section

/-!
# Central projection of linearly independent simplices

The convex hull of linearly independent position vectors is disjoint from
the origin. Normalization identifies each finite such simplex with its
spherical image. This is the simplex calculation in Cairns 1940,
Sections 5--6, pp. 801--802. See M76 derivation 16.
-/


open Set NormedSpace

section LinearExtension

variable {𝕜 E F ι : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] {v : ι → E}

/-- Any values on a linearly independent family extend to a linear map.
This supplies the separating functional for central projection;
see Cairns p. 802 and M76 derivation 16. -/
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

/-- A linear functional constant on a set is constant on its convex hull.
See the affine-level-set argument in M76 derivation 16. -/
theorem LinearMap.eqOn_const_convexHull (L : E →ₗ[ℝ] ℝ) {s : Set E} {c : ℝ}
    (hs : ∀ x ∈ s, L x = c) : ∀ x ∈ convexHull ℝ s, L x = c :=
  convexHull_min hs ((convex_singleton c).linear_preimage L)

/-- A simplex of linearly independent position vectors lies on a linear
functional's level set at one. See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.exists_eq_one_on_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    ∃ L : E →ₗ[ℝ] ℝ, ∀ x ∈ convexHull ℝ s, L x = 1 := by
  obtain ⟨L, hL⟩ := hs.exists_linearMap_apply_eq (fun _ => (1 : ℝ))
  exact ⟨L, L.eqOn_const_convexHull (fun x hx => hL ⟨x, hx⟩)⟩

/-- The origin is outside the convex hull of linearly independent
position vectors. See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.zero_notMem_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) : (0 : E) ∉ convexHull ℝ s := by
  obtain ⟨L, hL⟩ := hs.exists_eq_one_on_convexHull
  intro hzero
  simpa using hL 0 hzero

/-- Normalization is continuous at each nonzero vector.
See the central projection in Cairns p. 802 and M76 derivation 16. -/
theorem continuousAt_normalize_of_ne_zero {x : E} (hx : x ≠ 0) :
    ContinuousAt (normalize : E → E) x :=
  (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id

/-- Central projection is injective on any set contained in a linear
functional's level set at one. See M76 derivation 16. -/
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

/-- Central projection is injective on a simplex of linearly independent
position vectors. See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.injOn_normalize_convexHull {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    InjOn (normalize : E → E) (convexHull ℝ s) := by
  obtain ⟨L, hL⟩ := hs.exists_eq_one_on_convexHull
  exact L.injOn_normalize_of_eq_one hL

/-- All points of the projected simplex lie on the unit sphere.
See Cairns p. 802 and M76 derivation 16. -/
theorem LinearIndependent.normalize_convexHull_subset_sphere {s : Set E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    NormedSpace.normalize '' convexHull ℝ s ⊆ Metric.sphere (0 : E) 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_sphere, dist_zero_right]
  exact norm_normalize (fun h => hs.zero_notMem_convexHull (h ▸ hx))

/-- A finite simplex of independent position vectors is homeomorphic to
its spherical image under central projection. See Cairns p. 802 and
M76 derivation 16. -/
noncomputable def LinearIndependent.radialSimplexHomeomorph {s : Finset E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) :
    convexHull ℝ (s : Set E) ≃ₜ NormedSpace.normalize '' convexHull ℝ (s : Set E) := by
  letI : CompactSpace (convexHull ℝ (s : Set E)) :=
    isCompact_iff_compactSpace.mp (s.finite_toSet.isCompact_convexHull ℝ)
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn _ _ hs.injOn_normalize_convexHull)
  have hc : ContinuousOn (NormedSpace.normalize : E → E) (convexHull ℝ (s : Set E)) := by
    intro x hx
    exact (continuousAt_normalize_of_ne_zero
      (fun h => hs.zero_notMem_convexHull (h ▸ hx))).continuousWithinAt
  exact hc.domRestrict.subtype_mk _

/-- The central-projection homeomorphism agrees with normalization.
See M76 derivation 16. -/
theorem LinearIndependent.radialSimplexHomeomorph_apply {s : Finset E}
    (hs : LinearIndependent ℝ ((↑) : s → E)) (x : convexHull ℝ (s : Set E)) :
    (hs.radialSimplexHomeomorph x : E) = normalize x.val := rfl

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialConvexHull.lean
section

/-!
# Positive vertex rescaling and spherical convex hulls

Positive rescaling of individual vertices preserves their cone hull and,
when the convex hull avoids zero, its central projection to the sphere.
This is the radial invariance in Cairns 1940, Lemma 5.3, pp. 801--802.
See M76 derivation 16.
-/


open Set NormedSpace

namespace ConvexCone

section Algebra

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

omit [IsStrictOrderedRing 𝕜] in
/-- Taking the convex hull before the cone hull does not change the
cone. See Cairns pp. 801--802 and M76 derivation 16. -/
theorem hull_convexHull (s : Set E) : hull 𝕜 (convexHull 𝕜 s) = hull 𝕜 s := by
  apply le_antisymm
  · exact hull_min (convexHull_min subset_hull (hull 𝕜 s).convex)
  · exact hull_min ((subset_convexHull 𝕜 s).trans subset_hull)

/-- Positive rescaling of each generator preserves a cone hull.
See Cairns Lemma 5.3, pp. 801--802 and M76 derivation 16. -/
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

/-- A cone hull contains zero exactly when the convex hull does.
See M76 derivation 16. -/
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

/-- The spherical image of a convex hull avoiding zero is precisely
its cone's unit section. See Cairns p. 802 and M76 derivation 16. -/
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

/-- Positive rescaling of vertices preserves the full spherical image
of their convex hull. See Cairns Lemma 5.3, pp. 801--802 and M76 derivation 16. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/BasisConeCoordinates.lean
section

/-!
# Nonnegative cones in finite basis coordinates

The cone generated by selected independent source vertices is exactly
the set of nonnegative coordinate vectors supported on those vertices.
See Cairns 1940, pp. 799--800, and M76 derivation 27. This supplies the
closed secant-direction calculation for general-position stars.
-/


open Set
open scoped BigOperators

namespace Module.Basis

variable {ι E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonnegative cone supported on selected basis coordinates.
The empty set gives the zero cone. See Cairns p. 800 and M76 derivation 27. -/
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

/-- Membership is nonnegativity together with the support restriction.
See Cairns p. 800 and M76 derivation 27. -/
theorem mem_nonnegativeCone_iff (b : Basis ι ℝ E) (s : Set ι) (x : E) :
    x ∈ b.nonnegativeCone s ↔ (∀ i, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i = 0 := Iff.rfl

variable [Finite ι]

/-- Nonnegative supported coordinates are exactly the cone generated
by the selected basis vectors and zero. See Cairns pp. 799--800 and
M76 derivation 27. -/
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

/-- Each nonnegative coordinate cone is closed in the ambient norm
topology. See Cairns p. 800 and M76 derivation 27. -/
theorem isClosed_nonnegativeCone (b : Basis ι ℝ E) (s : Set ι) :
    IsClosed (b.nonnegativeCone s : Set E) := by
  classical
  let := Fintype.ofFinite ι
  have hc : ∀ i, Continuous (fun x : E => b.repr x i) :=
    fun i => (continuous_apply i).comp b.equivFunL.continuous
  change IsClosed {x : E | (∀ i, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i = 0}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter (fun i => isClosed_le (continuous_const (y := (0 : ℝ)))
    (hc i))).inter (isClosed_iInter (fun i =>
      isClosed_iInter (fun _ : i ∉ s =>
        isClosed_eq (hc i) (continuous_const (y := (0 : ℝ))))))

/-- A vector in a coordinate cone is a positive multiple of a point
in the bounded simplex containing zero. See Cairns p. 799 and
M76 derivation 27. -/
theorem exists_pos_smul_mem_simplex_of_mem_nonnegativeCone (b : Basis ι ℝ E)
    {s : Set ι} {x : E} (hx : x ∈ b.nonnegativeCone s) :
    ∃ r : ℝ, 0 < r ∧ ∃ y ∈ convexHull ℝ (insert 0 (b '' s)), r • y = x := by
  rw [b.nonnegativeCone_eq_hull, ← ConvexCone.hull_convexHull] at hx
  exact (ConvexCone.mem_hull_of_convex (convex_convexHull ℝ _)).mp hx

end Module.Basis

end

-- Source: PoincareMT/Proofs/M76/Mathlib/BasisSecantCones.lean
section

/-!
# Closed secant cones of independent simplices

Differences of nonnegative basis cones are given by closed coordinate
sign conditions. Injectivity on the bounded source simplices excludes
every nonzero vector of these cones from the projection kernel.
See Cairns 1940, pp. 799--800, and M76 derivation 27.
-/


open Set

namespace Module.Basis

variable {ι E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coordinate sign conditions for differences of two nonnegative
basis cones. See Cairns p. 800 and M76 derivation 27. -/
def secantCone (b : Basis ι ℝ E) (s t : Set ι) : Set E :=
  {x | (∀ i ∉ t, 0 ≤ b.repr x i) ∧ ∀ i ∉ s, b.repr x i ≤ 0}

/-- A difference cone of independent simplices is closed, including
when either face is empty. See Cairns p. 800 and M76 derivation 27. -/
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

/-- Nonnegative rescaling preserves the secant-direction cone.
See Cairns p. 800 and M76 derivation 27. -/
theorem smul_mem_secantCone (b : Basis ι ℝ E) {s t : Set ι} {x : E}
    (hx : x ∈ b.secantCone s t) {r : ℝ} (hr : 0 ≤ r) : r • x ∈ b.secantCone s t := by
  constructor
  · intro i hi
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using mul_nonneg hr (hx.1 i hi)
  · intro i hi
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
      mul_nonpos_of_nonneg_of_nonpos hr (hx.2 i hi)

/-- The sign conditions describe exactly differences of vectors in
the two nonnegative coordinate cones. See Cairns p. 800 and M76 derivation 27. -/
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

/-- Injectivity on two bounded cone simplices excludes nonzero kernel
vectors from their full difference cone. The rescaling is common to
the two points. See Cairns p. 799 and M76 derivation 27. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/BasisFaceSpanProjection.lean
section

/-!
# Face-span injectivity from bounded simplex injectivity

The difference cone of one independent simplex with itself is its
linear span. Hence an injective linear projection of the bounded
cone simplex preserves independence of all its position vectors.
See Cairns 1940, p. 799, and M76 derivation 29.
-/


open Set

namespace Module.Basis

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A face's difference cone with itself is its entire linear span.
See Cairns p. 799 and M76 derivation 29. -/
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

/-- Injectivity on the bounded cone simplex implies injectivity on
the entire face span. See Cairns p. 799 and M76 derivation 29. -/
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

/-- Projected face vectors stay linearly independent when the full
bounded cone simplex is embedded. See Cairns p. 799 and M76 derivation 29. -/
theorem linearIndepOn_of_injOn_simplex [Finite ι] (b : Basis ι ℝ E) {s : Set ι}
    (Q : E →L[ℝ] F) (hQ : InjOn Q (convexHull ℝ (insert 0 (b '' s)))) :
    LinearIndepOn ℝ (fun i => Q (b i)) s :=
  (b.linearIndependent.linearIndepOn s).map_injOn Q.toLinearMap
    (b.injOn_span_of_injOn_simplex Q hQ)

end Module.Basis

end

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineOnFaces.lean
section

/-!
# Maps affine on simplicial faces

The elementary piecewise-affine map data used in Hamilton 1976, p. 64,
and Cairns 1940, pp. 797--798. Continuity follows by locally finite pasting
on closed simplices. See M76 derivation 07. No smoothness across faces and
no existence of a subdivision is asserted.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A map is affine on each face of a specified complex, with an explicit
continuous affine extension for each face. See Cairns pp. 797--798 and
M76 derivation 07; this property depends on the specified triangulation. -/
def AffineOnFaces (K : SimplicialComplex ℝ E) (f : E → F) : Prop :=
  ∀ s ∈ K.faces, ∃ a : E →ᴬ[ℝ] F, EqOn f a (convexHull ℝ (s : Set E))

variable {K L : SimplicialComplex ℝ E} {f g : E → F}

/-- A globally affine map is affine on every face of every complex.
See M76 derivation 07. -/
theorem affineOnFaces_affine (K : SimplicialComplex ℝ E) (a : E →ᴬ[ℝ] F) :
    K.AffineOnFaces a :=
  fun _ _ => ⟨a, fun _ _ => rfl⟩

/-- The property depends only on values on the carrier.
See M76 derivation 07, including the total-function semantics. -/
theorem AffineOnFaces.congr (hf : K.AffineOnFaces f) (hfg : EqOn f g K.space) :
    K.AffineOnFaces g := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  exact ⟨a, fun _ hx => (hfg (convexHull_subset_space hs hx)).symm.trans (ha hx)⟩

/-- Affine behavior is preserved when every new face lies in an old one.
This includes restriction and subdivision; see M76 derivation 07. -/
theorem AffineOnFaces.of_face_containment (hf : K.AffineOnFaces f)
    (hLK : ∀ s ∈ L.faces, ∃ t ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) : L.AffineOnFaces f := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hLK s hs
  obtain ⟨a, ha⟩ := hf t ht
  exact ⟨a, fun _ hx => ha (hst hx)⟩

/-- Postcomposition with a globally affine map preserves affine behavior on
the same faces. See M76 derivation 07. -/
theorem AffineOnFaces.postcomp (hf : K.AffineOnFaces f) (b : F →ᴬ[ℝ] G) :
    K.AffineOnFaces (b ∘ f) := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  exact ⟨b.comp a, fun _ hx => congrArg b (ha hx)⟩

/-- A map affine on the faces of a locally finite complex is continuous on
its carrier. See Hamilton's locally finite triangulations and M76 derivation 07. -/
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

/-- A map affine on the faces of a finite complex is continuous on its carrier.
See Cairns' finite polyhedral pieces and M76 derivation 07. -/
theorem AffineOnFaces.continuousOn (hf : K.AffineOnFaces f) (hfinite : K.faces.Finite) :
    ContinuousOn f K.space := by
  let := hfinite.fintype
  exact hf.continuousOn_of_locallyFinite (locallyFinite_of_finite _)

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineFaceMaps.lean
section

/-!
# Images and aligned compositions of face-affine maps

A map affine on each face takes that face onto the convex hull of the vertex
images. When the source and target faces align, face-affine maps compose on
the same source complex. These are the elementary PL calculations used in
Hamilton 1976, p. 64, and Cairns 1940, pp. 797--798. See M76 derivation 08.
Existence of a subdivision for unaligned maps is a separate obligation.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}
  {f : E → F} {g : F → G}

/-- The image of a simplex under a face-affine map is the convex hull of its
vertex images. See Cairns pp. 797--798 and M76 derivation 08. -/
theorem AffineOnFaces.image_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) :
    f '' convexHull ℝ (s : Set E) = convexHull ℝ (f '' (s : Set E)) := by
  obtain ⟨a, ha⟩ := hf s hs
  have hav : EqOn f a (s : Set E) := ha.mono (subset_convexHull ℝ _)
  calc
    f '' convexHull ℝ (s : Set E) = a '' convexHull ℝ (s : Set E) := ha.image_eq
    _ = convexHull ℝ (a '' (s : Set E)) := a.toAffineMap.image_convexHull _
    _ = convexHull ℝ (f '' (s : Set E)) := congrArg (convexHull ℝ) hav.image_eq.symm

/-- Containment of vertex images implies containment of the whole simplex
image in the corresponding convex hull. See M76 derivation 08. -/
theorem AffineOnFaces.mapsTo_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) {t : Set F} (hst : f '' (s : Set E) ⊆ t) :
    MapsTo f (convexHull ℝ (s : Set E)) (convexHull ℝ t) := by
  intro x hx
  apply convexHull_mono hst
  rw [← hf.image_convexHull hs]
  exact mem_image_of_mem f hx

/-- A face-affine map sending each set of vertices into a target face maps
the entire source carrier into the target carrier. See M76 derivation 08. -/
theorem AffineOnFaces.mapsTo_space (hf : K.AffineOnFaces f)
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    MapsTo f K.space L.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  exact convexHull_subset_space ht (hf.mapsTo_convexHull hs hst hxs)

/-- Face-affine maps compose on the same source faces when each source face
maps into one target face. The alignment premise is explicit; see M76
derivation 08 and the PL maps of Hamilton p. 64. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplicialLinearImage.lean
section

/-!
# Geometric linear images of independent complexes

A linear map injective on every face span and on the carrier takes
a complex with independent position vectors to a geometric complex
with exactly its mapped faces. See Cairns 1940, p. 799, and M76
derivation 29. Neither global ambient injectivity nor a subdivision
is required.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E}

private theorem linear_image_convexHull (Q : E →L[ℝ] F) (s : Set E) :
    Q '' convexHull ℝ s = convexHull ℝ (Q '' s) := by
  simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using
    Q.toLinearMap.toAffineMap.image_convexHull s

/-- Independent position vectors stay independent under a linear
map injective on their span. See Cairns p. 799 and M76 derivation 29. -/
theorem linearIndependent_linear_face_image (Q : E →L[ℝ] F) {s : Finset E}
    (hlin : LinearIndependent ℝ ((↑) : s → E))
    (hQ : InjOn Q (Submodule.span ℝ (s : Set E))) :
    LinearIndependent ℝ ((↑) : ↥(Q '' (s : Set E)) → F) := by
  have hs : LinearIndepOn ℝ id (s : Set E) := hlin
  have hmap := hs.map_injOn Q.toLinearMap
    (by simpa only [image_id, ContinuousLinearMap.coe_coe] using hQ)
  simpa only [LinearIndepOn, Function.comp_def, id_eq, ContinuousLinearMap.coe_coe]
    using hmap.id_image

/-- Linear image of a complex whose face spans and entire carrier
are embedded. All faces are exact images of source faces.
See Cairns p. 799 and M76 derivation 29. -/
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

/-- The faces of the linear image are the exact mapped finite faces.
See Cairns p. 799 and M76 derivation 29. -/
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

/-- Every image face still has independent position vectors.
See Cairns p. 799 and M76 derivation 29. -/
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

/-- The image-complex carrier is the actual linear image of the
source carrier. See Cairns p. 799 and M76 derivation 29. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ClosedConeProjectionBound.lean
section

/-!
# Uniform lower bounds for projections on closed direction sets

On a closed positively homogeneous set in a finite-dimensional space,
avoidance of the projection kernel gives a uniform positive lower
bound. The bound persists under operator perturbation and separates
directions from kernel vectors. See Cairns 1940, pp. 799--800, and
M76 derivation 27.
-/


open Set NormedSpace

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A kernel avoiding a closed set of directions has a uniform lower
projection bound. The empty direction set and zero-dimensional source
are allowed. See Cairns p. 800 and M76 derivation 27. -/
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

/-- A positive projection lower bound loses at most half its value
under a sufficiently small operator perturbation.
See Cairns pp. 798--800 and M76 derivation 27. -/
theorem norm_lower_bound_of_perturbation (Q R : E →L[ℝ] F) {C : Set E} {c : ℝ}
    (hb : ∀ x ∈ C, c * ‖x‖ ≤ ‖Q x‖) (hR : ‖Q - R‖ ≤ c / 2) :
    ∀ x ∈ C, (c / 2) * ‖x‖ ≤ ‖R x‖ := by
  intro x hx
  have hdiff : ‖Q x‖ - ‖R x‖ ≤ (c / 2) * ‖x‖ :=
    (norm_sub_norm_le (Q x) (R x)).trans
      ((Q - R).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg x)))
  have h := hb x hx
  linarith

/-- The quantitative projection bound separates every direction from
every vector in the kernel. This is the distance form of the secant
angle condition; see Cairns p. 799 and M76 derivation 27. -/
theorem norm_lower_bound_le_kernel_distance (Q : E →L[ℝ] F) {C : Set E} {c : ℝ}
    (hb : ∀ x ∈ C, c * ‖x‖ ≤ ‖Q x‖) {x k : E} (hx : x ∈ C) (hk : Q k = 0) :
    c * ‖x‖ ≤ ‖Q‖ * ‖x - k‖ := by
  have he : Q (x - k) = Q x := by rw [map_sub, hk, sub_zero]
  exact (hb x hx).trans (he ▸ Q.le_opNorm (x - k))

end ContinuousLinearMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplicialStar.lean
section

/-!
# Closed stars and links in geometric simplicial complexes

The closed star of a vertex consists of the faces that can be joined to
that vertex; the link removes the vertex. These are the stars used by
Cairns 1940, Sections 4--6, pp. 800--802. See M76 derivation 16.
-/


open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

/-- The closed star contains exactly the faces that can be joined to
the specified vertex. See Cairns pp. 800--802 and M76 derivation 16. -/
def closedStar (K : SimplicialComplex 𝕜 E) (p : E) : SimplicialComplex 𝕜 E where
  faces := {s | s ∈ K.faces ∧ insert p s ∈ K.faces}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht,
      K.down_closed hs.2 (Finset.insert_subset_insert p hts) (Finset.insert_nonempty p t)⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

/-- The link contains the closed-star faces omitting its vertex.
See Cairns pp. 800--802 and M76 derivation 16. -/
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

/-- Taking a closed star preserves finiteness. See M76 derivation 16. -/
theorem finite_closedStar_faces {K : SimplicialComplex 𝕜 E} (hK : K.faces.Finite) (p : E) :
    (K.closedStar p).faces.Finite := hK.subset (fun _ hs => hs.1)

/-- Taking a link preserves finiteness. See M76 derivation 16. -/
theorem finite_link_faces {K : SimplicialComplex 𝕜 E} (hK : K.faces.Finite) (p : E) :
    (K.link p).faces.Finite := hK.subset (fun _ hs => hs.1)

/-- Every link face belongs to the closed star. See M76 derivation 16. -/
theorem link_le_closedStar (K : SimplicialComplex 𝕜 E) (p : E) :
    K.link p ≤ K.closedStar p := fun _ hs => ⟨hs.1, hs.2.2⟩

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/FinitePolyhedronMaps.lean
section

/-!
# Homeomorphisms from finite polyhedron maps

A finite complex has compact carrier. An injective map affine on its faces
therefore identifies that carrier homeomorphically with its image. This is
the topological component of the PL maps in Hamilton 1976, pp. 64, 69, and
Cairns 1940, pp. 797--798. See M76 derivation 08. No claim about an affine
or PL inverse is made here.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The carrier of a finite geometric complex is compact.
See Hamilton p. 69 and M76 derivation 08. -/
theorem isCompact_space_of_finite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    IsCompact K.space :=
  hK.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ

variable {K : SimplicialComplex ℝ E} {f : E → F}

/-- An injective map affine on the faces of a finite complex is a homeomorphism
onto its image, with the subspace topologies. See M76 derivation 08. -/
noncomputable def AffineOnFaces.homeomorphImage (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hinj : InjOn f K.space) : K.space ≃ₜ f '' K.space := by
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite K hK)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn f K.space hinj)
    ((hf.continuousOn hK).domRestrict.subtype_mk _)

/-- The induced homeomorphism has the original function as its forward map.
See M76 derivation 08. -/
theorem AffineOnFaces.homeomorphImage_apply (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hinj : InjOn f K.space) (x : K.space) :
    (hf.homeomorphImage hK hinj x : F) = f x := rfl

/-- A face-affine bijection from a finite complex to a prescribed subset is
a homeomorphism for the subspace topology. See M76 derivation 08. -/
noncomputable def AffineOnFaces.homeomorphOfBijOn (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) {S : Set F} (hbij : BijOn f K.space S) : K.space ≃ₜ S :=
  (hf.homeomorphImage hK hbij.injOn).trans (Homeomorph.setCongr hbij.image_eq)

/-- The homeomorphism onto a prescribed target agrees with the original map.
See M76 derivation 08. -/
theorem AffineOnFaces.homeomorphOfBijOn_apply (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) {S : Set F} (hbij : BijOn f K.space S) (x : K.space) :
    (hf.homeomorphOfBijOn hK hbij x : F) = f x := rfl

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialStar.lean
section

/-!
# Central projection of the link of a straight star

The simplicial intersection law makes radial projection injective on the
link of the origin. For a finite star this gives a homeomorphism onto its
spherical image. See Cairns 1940, Section 6, p. 802 and M76 derivation 16.
-/


open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

/-- Position vectors of a face in the link of zero are linearly
independent. See Cairns p. 802 and M76 derivation 16. -/
theorem linearIndependent_of_mem_link_zero {s : Finset E} (hs : s ∈ (K.link 0).faces) :
    LinearIndependent ℝ ((↑) : s → E) := by
  have hnonzero : ∀ v ∈ (s : Set E), v ≠ (0 : E) := fun v hv h => hs.2.1 (h ▸ hv)
  have h := (linearIndependent_set_iff_affineIndependent_vadd_union_singleton
    ℝ hnonzero (0 : E)).mpr
  apply h
  let f : ↥({(0 : E)} ∪ (fun v : E => v +ᵥ (0 : E)) '' (s : Set E)) →
      ↥(insert (0 : E) s) := fun v => ⟨v.val, by simpa [vadd_eq_add] using v.property⟩
  exact (K.indep hs.2.2).comp_embedding
    ⟨f, fun x y hxy => Subtype.ext
      (congrArg (fun z : ↥(insert (0 : E) s) => (z : E)) hxy)⟩

/-- The link of zero does not contain zero. See M76 derivation 16. -/
theorem zero_notMem_link_space (K : SimplicialComplex ℝ E) : (0 : E) ∉ (K.link 0).space := by
  intro hzero
  obtain ⟨s, hs, hx⟩ := mem_space_iff.mp hzero
  exact (linearIndependent_of_mem_link_zero hs).zero_notMem_convexHull hx

/-- If two link points have the same direction and the first is nearer
the origin, the simplicial intersection law puts them in one common face.
See M76 derivation 16. -/
theorem eq_of_normalize_eq_of_norm_le_on_link {x y : E}
    (hx : x ∈ (K.link 0).space) (hy : y ∈ (K.link 0).space)
    (hxy : NormedSpace.normalize x = NormedSpace.normalize y) (hnorm : ‖x‖ ≤ ‖y‖) : x = y := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
  have hy0 : y ≠ 0 := fun h =>
    (linearIndependent_of_mem_link_zero ht).zero_notMem_convexHull (h ▸ hyt)
  have hys : y ∈ convexHull ℝ ((insert 0 t : Finset E) : Set E) :=
    convexHull_mono (by intro z hz; exact Finset.mem_insert_of_mem hz) hyt
  have hratio : ‖x‖ / ‖y‖ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (norm_nonneg _) (norm_nonneg _), (div_le_one (norm_pos_iff.mpr hy0)).mpr hnorm⟩
  have hxeq : x = (‖x‖ / ‖y‖) • y := by
    calc
      x = ‖x‖ • NormedSpace.normalize x := (norm_smul_normalize x).symm
      _ = ‖x‖ • NormedSpace.normalize y := by rw [hxy]
      _ = (‖x‖ / ‖y‖) • y := by rw [NormedSpace.normalize, smul_smul, div_eq_mul_inv]
  have hxcone : x ∈ convexHull ℝ ((insert 0 t : Finset E) : Set E) := by
    rw [hxeq]
    exact (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _)) hys hratio
  have hinter := K.inter_subset_convexHull hs.1 ht.2.2 ⟨hxs, hxcone⟩
  rw [Finset.coe_insert, Set.inter_insert_of_notMem hs.2.1] at hinter
  have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono inter_subset_right hinter
  exact (linearIndependent_of_mem_link_zero ht).injOn_normalize_convexHull hxt hyt hxy

/-- Central projection is injective on the entire link, across different
faces as well as within a face. See Cairns p. 802 and M76 derivation 16. -/
theorem injOn_normalize_link (K : SimplicialComplex ℝ E) :
    InjOn (NormedSpace.normalize : E → E) (K.link 0).space := by
  intro x hx y hy hxy
  rcases le_total ‖x‖ ‖y‖ with hle | hle
  · exact eq_of_normalize_eq_of_norm_le_on_link hx hy hxy hle
  · exact (eq_of_normalize_eq_of_norm_le_on_link hy hx hxy.symm hle).symm

/-- A finite star's link is homeomorphic to its image under central
projection. See Cairns p. 802 and M76 derivation 16. -/
noncomputable def radialLinkHomeomorph (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    (K.link 0).space ≃ₜ NormedSpace.normalize '' (K.link 0).space := by
  letI : CompactSpace (K.link 0).space := isCompact_iff_compactSpace.mp
    (isCompact_space_of_finite _ (finite_link_faces hK 0))
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn _ _ (injOn_normalize_link K))
  have hc : ContinuousOn (NormedSpace.normalize : E → E) (K.link 0).space := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => zero_notMem_link_space K (by simpa only [h] using hx)
    exact (continuousAt_normalize_of_ne_zero hx0).continuousWithinAt
  exact hc.domRestrict.subtype_mk _

/-- The link homeomorphism is the geometric central projection.
See M76 derivation 16. -/
theorem radialLinkHomeomorph_apply (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (x : (K.link 0).space) :
    (K.radialLinkHomeomorph hK x : E) = NormedSpace.normalize x.val := rfl

/-- Every nonzero point of the closed star lies on a segment from zero
to a link point, with strictly positive parameter. See Cairns p. 802 and
M76 derivation 16. -/
theorem exists_linkPoint_smul {x : E} (hx : x ∈ (K.closedStar 0).space) (hx0 : x ≠ 0) :
    ∃ y ∈ (K.link 0).space, ∃ r ∈ Ioc (0 : ℝ) 1, x = r • y := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  have hu : (s.erase 0).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rcases (Finset.erase_eq_empty_iff s 0).mp he with he | he
    · simp [he] at hxs
    · exact hx0 (by simpa [he] using hxs)
  have hulink : s.erase 0 ∈ (K.link 0).faces :=
    ⟨K.down_closed hs.1 (Finset.erase_subset _ _) hu, Finset.notMem_erase _ _,
      K.down_closed hs.2 (Finset.insert_subset_insert _ (Finset.erase_subset _ _))
        (Finset.insert_nonempty _ _)⟩
  have hxcone : x ∈ convexHull ℝ ((insert 0 (s.erase 0) : Finset E) : Set E) :=
    convexHull_mono (Finset.insert_erase_subset _ _) hxs
  rw [Finset.coe_insert, convexHull_insert hu, mem_convexJoin] at hxcone
  obtain ⟨p, hp, y, hy, a, b, ha, hb, hab, heq⟩ := hxcone
  rw [mem_singleton_iff] at hp
  subst p
  simp only [smul_zero, zero_add] at heq
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_smul] at heq
    exact hx0 heq.symm
  exact ⟨y, convexHull_subset_space hulink hy, b, ⟨lt_of_le_of_ne hb hb0.symm, by linarith⟩,
    heq.symm⟩

/-- A star containing a neighborhood of its center projects onto every
unit direction. See Cairns p. 802 and M76 derivation 16. -/
theorem normalize_image_link_eq_sphere (K : SimplicialComplex ℝ E)
    (hzero : (0 : E) ∈ interior (K.closedStar 0).space) :
    NormedSpace.normalize '' (K.link 0).space = Metric.sphere (0 : E) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_normalize (fun h => zero_notMem_link_space K (by simpa only [h] using hx))
  · intro z hz
    have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hznorm
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
    have hx : (r / 2) • z ∈ (K.closedStar 0).space := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), hznorm,
        mul_one]
      linarith
    have hx0 : (r / 2) • z ≠ 0 := smul_ne_zero (by positivity) hz0
    obtain ⟨y, hy, c, hc, hcy⟩ := exists_linkPoint_smul hx hx0
    refine ⟨y, hy, ?_⟩
    calc
      NormedSpace.normalize y = NormedSpace.normalize (c • y) :=
        (normalize_smul_of_pos hc.1 y).symm
      _ = NormedSpace.normalize ((r / 2) • z) := congrArg NormedSpace.normalize hcy.symm
      _ = NormedSpace.normalize z := normalize_smul_of_pos (by positivity) z
      _ = z := normalize_eq_self_of_norm_eq_one hznorm

/-- The link of a finite straight star containing a neighborhood of its
center is homeomorphic to the unit sphere by central projection.
See Cairns p. 802 and M76 derivation 16. -/
noncomputable def radialLinkSphereHomeomorph (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hzero : (0 : E) ∈ interior (K.closedStar 0).space) :
    (K.link 0).space ≃ₜ Metric.sphere (0 : E) 1 :=
  (K.radialLinkHomeomorph hK).trans (Homeomorph.setCongr (K.normalize_image_link_eq_sphere hzero))

/-- The link-to-sphere homeomorphism is the central projection itself.
See M76 derivation 16. -/
theorem radialLinkSphereHomeomorph_apply (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hzero : (0 : E) ∈ interior (K.closedStar 0).space)
    (x : (K.link 0).space) :
    (K.radialLinkSphereHomeomorph hK hzero x : E) = NormedSpace.normalize x.val := rfl

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialRescaling.lean
section

/-!
# Positive radial rescaling of simplicial complexes

For a complex with linearly independent faces and radially injective
carrier, positive rescaling of its vertices defines another geometric
complex. Its spherical image is unchanged. Links of straight stars
satisfy these hypotheses. This is the geometric part of Cairns 1940,
Lemma 5.3, pp. 801--802; see M76 derivation 17.
-/


open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nonzero rescaling preserves independence of a set of position
vectors. See Cairns Lemma 5.3, pp. 801--802 and M76 derivation 17. -/
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

/-- Every vertex of a face is a vertex of its complex. This is used in
the radial vertex assignment of Cairns p. 801; see M76 derivation 17. -/
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

/-- Positively rescale every vertex of a radially embedded complex.
The independent-face and radial-injectivity hypotheses hold for the
link of a straight star. See Cairns Lemma 5.3 and M76 derivation 17. -/
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

/-- The faces after radial rescaling are exactly the vertex images of
the original faces. See Cairns p. 801 and M76 derivation 17. -/
theorem radialRescale_faces (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    (K.radialRescale hlin hinj r hr).faces =
      (fun s : Finset E => s.image (fun x => r x • x)) '' K.faces := rfl

/-- A finite complex remains finite after radial rescaling.
See Cairns Lemma 5.3 and M76 derivation 17. -/
theorem finite_radialRescale_faces (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    (K.radialRescale hlin hinj r hr).faces.Finite := hK.image _

/-- The rescaled vertices retain linear independence on each face.
See Cairns p. 801 and M76 derivation 17. -/
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

/-- The rescaled carrier still meets each positive ray at most once.
See Cairns Lemma 5.3 and M76 derivation 17. -/
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

/-- Positive vertex rescaling preserves the entire spherical carrier.
See Cairns Lemma 5.3, pp. 801--802 and M76 derivation 17. -/
theorem normalize_image_radialRescale_space
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    NormedSpace.normalize '' (K.radialRescale hlin hinj r hr).space =
      NormedSpace.normalize '' K.space := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨_, ⟨s, hs, rfl⟩, hzs⟩ := mem_space_iff.mp hz
    rw [Finset.coe_image] at hzs
    have h := normalize_image_convexHull_pos_smul (hlin s hs).zero_notMem_convexHull r
      (fun x hx => hr x (face_subset_vertices hs hx))
    obtain ⟨x, hx, he⟩ := h.subset ⟨z, hzs, rfl⟩
    exact ⟨x, convexHull_subset_space hs hx, he⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    have h := normalize_image_convexHull_pos_smul (hlin s hs).zero_notMem_convexHull r
      (fun x hx => hr x (face_subset_vertices hs hx))
    obtain ⟨z, hz, he⟩ := h.symm.subset ⟨x, hxs, rfl⟩
    refine ⟨z, convexHull_subset_space (K := K.radialRescale hlin hinj r hr)
      (show s.image (fun x => r x • x) ∈ _ from ⟨s, hs, rfl⟩) ?_, he⟩
    simpa only [Finset.coe_image] using hz

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineInterpolation.lean
section

/-!
# Continuous affine interpolation at independent points

Prescribed values on an affinely independent set in a finite-dimensional
normed vector space extend to a continuous affine map. This supplies the
simplex inverse maps used in Hamilton 1976, pp. 64, 69, and Cairns 1940,
pp. 797--798. See M76 derivation 09 for the argument and hypotheses.
-/


open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Values on an affinely independent set have a continuous affine extension
over a complete field when the domain is finite-dimensional. See M76 derivation 09, the simplex
maps of Hamilton p. 64, and Cairns pp. 797--798. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineVertexExtension.lean
section

/-!
# Extension and uniqueness of simplicial vertex maps

Vertex values determine a face-affine map on its carrier. In a
finite-dimensional ambient space they always extend to such a map, using
affine interpolation and the common-face intersection axiom. This is the
simplex-map construction used in Hamilton 1976, pp. 64, 69, and Cairns 1940,
pp. 797--798. See M76 derivation 12.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

/-- Two face-affine maps agreeing on vertices agree on the whole carrier.
See the simplex correspondences of Cairns pp. 797--798 and M76 derivation 12. -/
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

/-- Any vertex assignment extends to a function affine on each face.
Continuity on the carrier follows under local finiteness from
`AffineOnFaces.continuousOn_of_locallyFinite`. See Hamilton p. 64,
Cairns pp. 797--798 and M76 derivation 12. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplicialHomeomorph.lean
section

/-!
# Polyhedral homeomorphisms from inverse vertex maps

Mutually inverse vertex maps preserving faces extend to mutually inverse
face-affine maps. For a finite source complex the induced carrier map is
a homeomorphism. This constructs the simplicial correspondences used in
Hamilton 1976, pp. 64, 69, and Cairns 1940, pp. 797--798.
See M76 derivation 12; the affine certificates in both directions are retained.
-/


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

/-- Inverse face-preserving vertex assignments induce a homeomorphism of
carriers with affine formulas on source and target faces. The inverse
identities are assumed only at vertices; see Hamilton p. 64, Cairns
pp. 797--798 and M76 derivation 12. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialRescalingHomeomorph.lean
section

/-!
# Piecewise affine homeomorphisms for radial vertex rescaling

Positive vertex rescaling gives a face-preserving vertex bijection,
hence a homeomorphism affine on every source and target simplex. This
is the PL correspondence in Cairns 1940, Lemma 5.3, pp. 801--802.
See M76 derivation 17.
-/


open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E}

/-- Positive radial rescaling is injective on vertices of a complex
whose carrier has injective central projection. See Cairns p. 801 and
M76 derivation 17. -/
theorem injOn_pos_smul_vertices
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    InjOn (fun x => r x • x) K.vertices := by
  intro x hx y hy hxy
  apply hinj (vertices_subset_space hx) (vertices_subset_space hy)
  have h := congrArg NormedSpace.normalize hxy
  simpa only [normalize_smul_of_pos (hr x hx), normalize_smul_of_pos (hr y hy)] using h

variable [DecidableEq E]

/-- The rescaled complex has exactly the rescaled original vertices.
See Cairns Lemma 5.3 and M76 derivation 17. -/
theorem radialRescale_vertices
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    (K.radialRescale hlin hinj r hr).vertices = (fun x => r x • x) '' K.vertices := by
  ext y
  constructor
  · intro hy
    obtain ⟨s, hs, he⟩ := hy
    change s.image (fun x => r x • x) = {y} at he
    have hyimage : y ∈ s.image (fun x => r x • x) := by rw [he]; simp
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyimage
    exact ⟨x, face_subset_vertices hs hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨{x}, hx, by simp⟩

variable [FiniteDimensional ℝ E]

/-- Radial vertex rescaling extends to a carrier homeomorphism with
affine formulas on every face in both directions. Positivity is required
only on vertices. See Cairns Lemma 5.3 and M76 derivation 17. -/
theorem exists_radialRescale_homeomorph (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) :
    ∃ (f g : E → E) (e : K.space ≃ₜ (K.radialRescale hlin hinj r hr).space),
      K.AffineOnFaces f ∧ (K.radialRescale hlin hinj r hr).AffineOnFaces g ∧
      EqOn f (fun x => r x • x) K.vertices ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      (∀ y : (K.radialRescale hlin hinj r hr).space, (e.symm y : E) = g y) := by
  let v : E → E := fun x => r x • x
  let w : E → E := Function.invFunOn v K.vertices
  have hv := injOn_pos_smul_vertices hinj r hr
  obtain ⟨f, g, e, hf, hg, hfv, _, hef, heg⟩ :=
    K.exists_homeomorph_of_vertex_maps (K.radialRescale hlin hinj r hr) hK v w
      (fun s hs => ⟨s.image v, ⟨s, hs, rfl⟩, by simp⟩)
      (by
        rintro _ ⟨s, hs, rfl⟩
        refine ⟨s, hs, ?_⟩
        rw [Finset.coe_image]
        exact (hv.invFunOn_image (face_subset_vertices hs)).subset)
      hv.leftInvOn_invFunOn
      (by
        rw [radialRescale_vertices]
        exact (surjOn_image v K.vertices).rightInvOn_invFunOn)
  exact ⟨f, g, e, hf, hg, hfv, hef, heg⟩

/-- The preceding rescaling construction applies to the link of zero
in any finite straight complex. See Cairns p. 802 and M76 derivation 17. -/
theorem exists_link_radialRescale_homeomorph (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (r : E → ℝ)
    (hr : ∀ x ∈ (K.link 0).vertices, 0 < r x) :
    ∃ (f g : E → E)
      (e : (K.link 0).space ≃ₜ
        ((K.link 0).radialRescale (fun _ hs => linearIndependent_of_mem_link_zero hs)
          (injOn_normalize_link K) r hr).space),
      (K.link 0).AffineOnFaces f ∧
      ((K.link 0).radialRescale (fun _ hs => linearIndependent_of_mem_link_zero hs)
        (injOn_normalize_link K) r hr).AffineOnFaces g ∧
      EqOn f (fun x => r x • x) (K.link 0).vertices ∧
      (∀ x : (K.link 0).space, (e x : E) = f x) ∧
      (∀ y, (e.symm y : E) = g y) :=
  (K.link 0).exists_radialRescale_homeomorph (finite_link_faces hK 0)
    (fun _ hs => linearIndependent_of_mem_link_zero hs) (injOn_normalize_link K) r hr

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialEmbeddingSpace.lean
section

/-!
# Radial embeddings in vertex coordinates

A faithful geometric realization whose faces have independent position
vectors and whose carrier has injective central projection is a radial
embedding. Positive radial rescaling preserves this space. This is the
unquotiented vertex space used in Cairns 1940, Section 5, pp. 801--802.
See M76 derivation 18; the star and coordinate-quotient identifications
are separate assertions.
-/


open Set NormedSpace Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A vertex assignment faithfully realizes an abstract complex by
independent position-vector simplices with injective central projection.
See Cairns pp. 801--802 and M76 derivation 18. -/
def IsRadialEmbedding (A : AbstractSimplicialComplex ι) (v : ι → E) : Prop :=
  Function.Injective v ∧ ∃ L : SimplicialComplex ℝ E,
    L.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v '' (s : Set ι)} ∧
    (∀ t ∈ L.faces, LinearIndependent ℝ ((↑) : t → E)) ∧
    InjOn (NormedSpace.normalize : E → E) L.space

/-- Radial vertex embeddings with the subspace topology of the product
of vertex positions. See Cairns p. 801 and M76 derivation 18. -/
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

/-- Every vertex of a radial embedding is nonzero. Requiring every
singleton in the abstract complex makes all coordinates constrained.
See Cairns p. 801 and M76 derivation 18. -/
theorem IsRadialEmbedding.ne_zero (hv : A.IsRadialEmbedding v) (i : ι) : v i ≠ 0 := by
  obtain ⟨L, hfaces, hlin, _⟩ := hv.2
  have hvertex : v i ∈ L.vertices := by
    rw [vertices_eq_range_of_faces hfaces]
    exact mem_range_self i
  intro hi
  apply (hlin {v i} hvertex).zero_notMem_convexHull
  simp [hi]

/-- Positive scaling of each embedded vertex preserves radial
embeddings and their labelled faces. See Cairns Lemma 5.3 and
M76 derivations 17--18. -/
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

/-- Vertex normalization preserves the faithful radial realization.
See Cairns Lemma 5.3 and M76 derivation 18. -/
theorem IsRadialEmbedding.normalize (hv : A.IsRadialEmbedding v) :
    A.IsRadialEmbedding (fun i => NormedSpace.normalize (v i)) :=
  hv.pos_smul (fun x => ‖x‖⁻¹) (fun i => inv_pos.mpr (norm_pos_iff.mpr (hv.ne_zero i)))

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/IndependentRealization.lean
section

/-!
# General-position geometric realizations

Independent position vectors realize every abstract simplicial complex
on their labels faithfully and radially. This is the general-position
source of Cairns 1940, Section 3, pp. 798--799, and Lemma 5.1,
p. 801. See M76 derivation 26.
-/


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

/-- The geometric realization whose vertices are an independent
family, with exactly the prescribed labelled faces.
See Cairns pp. 798--799 and M76 derivation 26. -/
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

/-- Faces of the independent realization are precisely the labelled
abstract faces. See Cairns p. 799 and M76 derivation 26. -/
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

/-- Every abstract complex has a faithful radial realization on any
linearly independent assignment of position vectors.
See Cairns pp. 798--799 and M76 derivation 26. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ConeSimplex.lean
section

/-!
# Simplices coned to the origin

Independent position vectors give an affinely independent simplex after
adjoining zero. Nonzero points of its cone hull lie on positive segments
to the base. See Cairns 1940, pp. 799, 801--802 and M76 derivation 19.
-/


open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Adjoining zero to independent position vectors gives an affinely
independent set. See Cairns' conical stars on p. 799 and M76 derivation 19. -/
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

/-- A nonzero point in the convex hull with zero adjoined lies on a
positive segment to a base-hull point. The base may initially be empty.
See Cairns pp. 799, 802 and M76 derivation 19. -/
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

/-- The segment from zero to a base-hull point lies in the coned hull.
See Cairns pp. 799, 802 and M76 derivation 19. -/
theorem smul_mem_convexHull_insert_zero {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : r • x ∈ convexHull ℝ (insert (0 : E) s) :=
  (convex_convexHull ℝ _).smul_mem_of_zero_mem
    (subset_convexHull ℝ _ (Set.mem_insert _ _))
    (convexHull_mono (Set.subset_insert _ _) hx) hr

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplicialCone.lean
section

/-!
# Geometric cones on radial simplicial complexes

Adjoining the origin to every face of a radially embedded complex gives
a geometric simplicial cone. This reconstructs closed stars from their
links. See Cairns 1940, pp. 799, 801--802 and M76 derivation 19.
-/


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

/-- Cone a complex to zero. Independent faces and injective central
projection ensure the geometric intersection law. The empty base has
the one-point cone. See Cairns pp. 799, 802 and M76 derivation 19. -/
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

/-- Face membership in the geometric cone is given by deleting its
center. See Cairns p. 799 and M76 derivation 19. -/
theorem mem_coneAtZero_faces
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) (s : Finset E) :
    s ∈ (K.coneAtZero hlin hinj).faces ↔
      s.Nonempty ∧ (s.erase 0 = ∅ ∨ s.erase 0 ∈ K.faces) := Iff.rfl

/-- The cone contains its center, even for an empty base complex.
See Cairns p. 799 and M76 derivation 19. -/
theorem zero_mem_coneAtZero_vertices
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (0 : E) ∈ (K.coneAtZero hlin hinj).vertices :=
  ⟨Finset.singleton_nonempty _, Or.inl (by simp)⟩

/-- Every base face remains a face of its cone.
See Cairns p. 799 and M76 derivation 19. -/
theorem le_coneAtZero
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) : K ≤ K.coneAtZero hlin hinj := by
  intro s hs
  have hs0 : (0 : E) ∉ s := fun h =>
    (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
  exact ⟨K.nonempty_of_mem_faces hs, Or.inr (by rwa [Finset.erase_eq_of_notMem hs0])⟩

/-- The link of the cone center is exactly the original complex.
See Cairns p. 802 and M76 derivation 19. -/
theorem link_coneAtZero
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).link 0 = K := by
  ext s
  constructor
  · intro hs
    have hbase := hs.1.2
    rw [Finset.erase_eq_of_notMem hs.2.1] at hbase
    exact hbase.resolve_left hs.1.1.ne_empty
  · intro hs
    have hs0 : (0 : E) ∉ s := fun h =>
      (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
    exact ⟨le_coneAtZero hlin hinj hs, hs0, Finset.insert_nonempty _ _,
      Or.inr (by rwa [Finset.erase_insert hs0])⟩

/-- Every face of a geometric cone belongs to the closed star of its
center. See Cairns p. 799 and M76 derivation 19. -/
theorem closedStar_coneAtZero
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    (K.coneAtZero hlin hinj).closedStar 0 = K.coneAtZero hlin hinj := by
  ext s
  refine ⟨fun hs => hs.1, fun hs => ⟨hs, Finset.insert_nonempty _ _, ?_⟩⟩
  simpa only [Finset.erase_insert_eq_erase] using hs.2

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/ConicalStar.lean
section

/-!
# Finite cones and reconstruction of closed stars

A geometric cone has precisely its base vertices and its center, remains
finite when its base is finite, and reconstructs the closed star of a
vertex from its link. See Cairns 1940, pp. 799, 801--802 and M76 derivation 19.
-/


open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}

/-- The cone vertices are exactly the base vertices and zero.
See Cairns p. 799 and M76 derivation 19. -/
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

/-- Inserting the center into a base face gives a cone face.
See Cairns p. 799 and M76 derivation 19. -/
theorem insert_zero_mem_coneAtZero_faces
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    {s : Finset E} (hs : s ∈ K.faces) : insert (0 : E) s ∈ (K.coneAtZero hlin hinj).faces := by
  have hs0 : (0 : E) ∉ s := fun h =>
    (hlin s hs).zero_notMem_convexHull (subset_convexHull ℝ _ h)
  exact ⟨Finset.insert_nonempty _ _, Or.inr (by rwa [Finset.erase_insert hs0])⟩

/-- Coning preserves finiteness of the face collection.
See Cairns p. 799 and M76 derivation 19. -/
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

/-- A closed star of an actual vertex is exactly the cone on its link.
The vertex hypothesis includes the isolated-center case. See Cairns
pp. 799, 802 and M76 derivation 19. -/
theorem coneAtZero_link_eq_closedStar (K : SimplicialComplex ℝ E)
    (hzero : (0 : E) ∈ K.vertices) :
    (K.link 0).coneAtZero (fun _ hs => linearIndependent_of_mem_link_zero hs)
      (injOn_normalize_link K) = K.closedStar 0 := by
  ext s
  constructor
  · intro hs
    rcases hs.2 with he | hlink
    · rcases (Finset.erase_eq_empty_iff s 0).mp he with he | he
      · exact (hs.1.ne_empty he).elim
      · subst s
        refine ⟨hzero, ?_⟩
        rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self (0 : E))]
        exact hzero
    · have hsubset : s ⊆ insert (0 : E) (s.erase 0) := Finset.insert_erase_subset _ _
      refine ⟨K.down_closed hlink.2.2 hsubset hs.1, ?_⟩
      exact K.down_closed hlink.2.2
        ((Finset.insert_subset_insert 0 hsubset).trans (by simp)) (Finset.insert_nonempty _ _)
  · intro hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    by_cases he : s.erase 0 = ∅
    · exact Or.inl he
    · right
      exact ⟨K.down_closed hs.1 (Finset.erase_subset _ _) (Finset.nonempty_iff_ne_empty.mpr he),
        Finset.notMem_erase _ _,
        K.down_closed hs.2 (Finset.insert_subset_insert 0 (Finset.erase_subset _ _))
          (Finset.insert_nonempty _ _)⟩

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/ConicalVertexMaps.lean
section

/-!
# Extending simplicial vertex maps over cones

Inverse face-preserving vertex maps fixing zero induce piecewise affine
homeomorphisms of finite cones. See Cairns 1940, pp. 799, 801--802 and
M76 derivation 20.
-/


open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

/-- A face-preserving vertex map fixing zero preserves cone faces.
See Cairns pp. 799, 801 and M76 derivation 20. -/
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

/-- Inverse vertex maps preserving base faces and fixing zero induce a
PL homeomorphism of the cones. See Cairns pp. 799, 801--802 and
M76 derivation 20. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ConicalLinearProjection.lean
section

/-!
# Linear projections realizing conical homeomorphisms

A linear map inducing a faithful correspondence of radial link faces
restricts to a PL homeomorphism of the entire cones. Its inverse is
affine on target faces. This is the projection construction of Cairns
1940, Section 3, p. 799; see M76 derivation 26.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}

omit [DecidableEq E] in
/-- Exact images of all faces give the exact image of the vertex set.
See Cairns p. 799 and M76 derivation 26. -/
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

/-- A linear map with faithful radial face images is a homeomorphism
on the full cone, with a face-affine inverse. The forward map is the
given linear projection itself. See Cairns p. 799 and M76 derivation 26. -/
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

/-- The same ambient linear map is injective on the source cone.
See Cairns p. 799 and M76 derivation 26. -/
theorem linear_injOn_cone_of_face_images (K : SimplicialComplex ℝ E)
    (L : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinjK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ L.faces, LinearIndependent ℝ ((↑) : s → F))
    (hinjL : InjOn (NormedSpace.normalize : F → F) L.space)
    (Q : E →L[ℝ] F) (hQ : InjOn Q K.vertices)
    (hfaces : L.faces = (fun s : Finset E => s.image Q) '' K.faces) :
    InjOn Q (K.coneAtZero hlinK hinjK).space := by
  obtain ⟨_, e, _, he, _⟩ := K.exists_cone_homeomorph_of_linear_map L hK
    hlinK hinjK hlinL hinjL Q hQ hfaces
  intro x hx y hy hxy
  have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
    Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm))
  exact congrArg Subtype.val (e.injective hexy)

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialRescalingHomotopy.lean
section

/-!
# A continuous PL deformation for radial vertex rescaling

Linear interpolation between the identity and a positive radial vertex
map stays an embedding of the carrier at every time. Joint continuity
uses one explicit interpolation formula. See Cairns 1940, Lemma 5.3,
pp. 801--802 and M76 derivation 17. This treats a fixed embedded complex;
dependence on varying original embeddings is a separate assertion.
-/


open Set NormedSpace
open scoped unitInterval

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

/-- Interpolation of two face-affine maps remains affine on each face.
See the vertex deformation in Cairns p. 801 and M76 derivation 17. -/
theorem AffineOnFaces.interpolate (hf : K.AffineOnFaces f) (hg : K.AffineOnFaces g) (t : ℝ) :
    K.AffineOnFaces (fun x => (1 - t) • f x + t • g x) := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg s hs
  refine ⟨(1 - t) • a + t • b, fun x hx => ?_⟩
  simp only [ContinuousAffineMap.add_apply, ContinuousAffineMap.smul_apply, ha hx, hb hx]

/-- Interpolation of the positive numbers one and r stays positive
throughout the closed unit interval. See Cairns p. 801 and M76 derivation 17. -/
theorem radial_interpolation_pos {r t : ℝ} (hr : 0 < r) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 - t + t * r := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · simp [← h]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos h hr)

variable [DecidableEq E] [FiniteDimensional ℝ E] {f : E → E}

/-- At each time, the explicit interpolation is the homeomorphism
onto the complex with interpolated vertex radii. The inverse remains
affine on every target face. See Cairns Lemma 5.3 and M76 derivation 17. -/
theorem exists_radial_interpolation_homeomorph
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hf : K.AffineOnFaces f) (hfv : EqOn f (fun x => r x • x) K.vertices)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (g : E → E)
      (e : K.space ≃ₜ
        (K.radialRescale hlin hinj (fun x => 1 - t + t * r x)
          (fun x hx => radial_interpolation_pos (hr x hx) ht)).space),
      (K.radialRescale hlin hinj (fun x => 1 - t + t * r x)
        (fun x hx => radial_interpolation_pos (hr x hx) ht)).AffineOnFaces g ∧
      (∀ x : K.space, (e x : E) = (1 - t) • (x : E) + t • f x) ∧
      (∀ y, (e.symm y : E) = g y) := by
  obtain ⟨F, g, e, hF, hg, hFv, heF, heg⟩ :=
    K.exists_radialRescale_homeomorph hK hlin hinj (fun x => 1 - t + t * r x)
      (fun x hx => radial_interpolation_pos (hr x hx) ht)
  have hinterp := (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).interpolate hf t
  have heq : EqOn F (fun x => (1 - t) • x + t • f x) K.space :=
    hF.eqOn_of_eqOn_vertices hinterp (fun x hx => by
      simp only [hFv hx, hfv hx, add_smul, mul_smul])
  exact ⟨g, e, hg, fun x => (heF x).trans (heq x.property), heg⟩

/-- The explicit radial vertex interpolation is a homotopy through
embeddings affine on the fixed source faces. See Cairns Lemma 5.3,
pp. 801--802 and M76 derivation 17. -/
noncomputable def radialRescaleHomotopy
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hf : K.AffineOnFaces f) (hfv : EqOn f (fun x => r x • x) K.vertices) :
    ContinuousMap.HomotopyWith
      (⟨Subtype.val, continuous_subtype_val⟩ : C(K.space, E))
      ⟨fun x => f x, (hf.continuousOn hK).domRestrict⟩
      (fun F => Topology.IsEmbedding F ∧
        ∃ g : E → E, K.AffineOnFaces g ∧ ∀ x : K.space, g x = F x) where
  toFun tx := (1 - (tx.1 : ℝ)) • (tx.2 : E) + (tx.1 : ℝ) • f tx.2
  continuous_toFun := by
    have ht : Continuous (fun tx : I × K.space => (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun tx : I × K.space => (tx.2 : E)) :=
      continuous_subtype_val.comp continuous_snd
    have hfx : Continuous (fun tx : I × K.space => f tx.2) :=
      (hf.continuousOn hK).domRestrict.comp continuous_snd
    exact ((continuous_const.sub ht).smul hx).add (ht.smul hfx)
  map_zero_left x := by simp
  map_one_left x := by
    change (1 - (1 : ℝ)) • (x : E) + (1 : ℝ) • f x = f x
    simp
  prop' t := by
    obtain ⟨g, e, _, he, _⟩ :=
      exists_radial_interpolation_homeomorph hK hlin hinj r hr hf hfv t.property
    refine ⟨?_, fun x => (1 - (t : ℝ)) • x + (t : ℝ) • f x,
      (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).interpolate hf t, fun _ => rfl⟩
    have h := (Topology.IsEmbedding.subtypeVal).comp e.isEmbedding
    convert h using 1
    ext x
    exact (he x).symm

/-- A vertex whose target radius is unchanged is fixed for the whole
radial interpolation. See Cairns p. 801 and M76 derivation 17. -/
theorem radialRescaleHomotopy_fixed_vertex
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space)
    (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hf : K.AffineOnFaces f) (hfv : EqOn f (fun x => r x • x) K.vertices)
    {x : E} (hx : x ∈ K.vertices) (hxr : r x = 1) (t : I) :
    radialRescaleHomotopy hK hlin hinj r hr hf hfv (t, ⟨x, vertices_subset_space hx⟩) = x := by
  change (1 - (t : ℝ)) • x + (t : ℝ) • f x = x
  simp only [hfv hx, hxr, one_smul]
  rw [← add_smul]
  simp

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialEmbeddingNormalization.lean
section

/-!
# Normalization of radial embedding spaces

The vertex-coordinate space of radial embeddings deforms onto its
unit-vertex subspace. The deformation is jointly continuous in time
and the original embedding and fixes that subspace. This is the radial
deformation in Cairns 1940, Lemma 5.3, pp. 801--802 before taking any
coordinate-change quotient. See M76 derivation 18.
-/


open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

/-- Normalize all vertices of a radial embedding. See Cairns
Lemma 5.3, pp. 801--802 and M76 derivation 18. -/
noncomputable def RadialEmbedding.normalized (v : A.RadialEmbedding E) : A.RadialEmbedding E :=
  ⟨fun i => NormedSpace.normalize (v.val i), v.property.normalize⟩

/-- Vertex normalization is continuous in the actual vertex topology.
See Cairns p. 801 and M76 derivation 18. -/
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

/-- Every vertex of the normalized embedding lies on the unit sphere.
See Cairns p. 801 and M76 derivation 18. -/
theorem RadialEmbedding.norm_normalized (v : A.RadialEmbedding E) (i : ι) :
    ‖v.normalized.val i‖ = 1 := norm_normalize (v.property.ne_zero i)

/-- Normalization fixes an embedding whose vertices are already unit
vectors. See Cairns Lemma 5.3 and M76 derivation 18. -/
theorem RadialEmbedding.normalized_eq_self (v : A.RadialEmbedding E)
    (hv : ∀ i, ‖v.val i‖ = 1) : v.normalized = v :=
  Subtype.ext (funext fun i => normalize_eq_self_of_norm_eq_one (hv i))

/-- Move each vertex along its segment to the unit sphere. Positive
radial scaling keeps the result in the radial embedding space.
See Cairns Lemma 5.3 and M76 derivation 18. -/
noncomputable def RadialEmbedding.interpolate (t : I) (v : A.RadialEmbedding E) :
    A.RadialEmbedding E :=
  ⟨fun i => (1 - (t : ℝ)) • v.val i + (t : ℝ) • NormedSpace.normalize (v.val i), by
    have h := v.property.pos_smul (fun x => 1 - (t : ℝ) + (t : ℝ) * ‖x‖⁻¹)
      (fun i => Geometry.SimplicialComplex.radial_interpolation_pos
        (inv_pos.mpr (norm_pos_iff.mpr (v.property.ne_zero i))) t.property)
    simpa only [add_smul, mul_smul, NormedSpace.normalize] using h⟩

/-- The deformation is continuous simultaneously in time and every
vertex coordinate. See Cairns p. 801 and M76 derivation 18. -/
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

/-- At time zero, every original vertex is unchanged.
See Cairns p. 801 and M76 derivation 18. -/
@[simp] theorem RadialEmbedding.interpolate_zero (v : A.RadialEmbedding E) :
    v.interpolate 0 = v := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) • v.val i + (0 : ℝ) • NormedSpace.normalize (v.val i) = v.val i
  simp

/-- At time one, all vertices have been normalized.
See Cairns p. 801 and M76 derivation 18. -/
@[simp] theorem RadialEmbedding.interpolate_one (v : A.RadialEmbedding E) :
    v.interpolate 1 = v.normalized := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) • v.val i + (1 : ℝ) • NormedSpace.normalize (v.val i) =
    NormedSpace.normalize (v.val i)
  simp

/-- The entire deformation fixes the unit-vertex subspace.
See Cairns Lemma 5.3 and M76 derivation 18. -/
theorem RadialEmbedding.interpolate_eq_self (v : A.RadialEmbedding E)
    (hv : ∀ i, ‖v.val i‖ = 1) (t : I) : v.interpolate t = v := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) • v.val i + (t : ℝ) • NormedSpace.normalize (v.val i) = v.val i
  rw [normalize_eq_self_of_norm_eq_one (hv i), ← add_smul]
  simp

/-- The radial normalization as an actual homotopy of vertex spaces.
See Cairns Lemma 5.3 and M76 derivation 18. -/
noncomputable def radialNormalizationHomotopy (A : AbstractSimplicialComplex ι)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.Homotopy (ContinuousMap.id (A.RadialEmbedding E))
      ⟨RadialEmbedding.normalized, RadialEmbedding.continuous_normalized⟩ where
  toFun tv := tv.2.interpolate tv.1
  continuous_toFun := RadialEmbedding.continuous_interpolate
  map_zero_left v := v.interpolate_zero
  map_one_left v := v.interpolate_one

/-- The unit-vertex subspace, with its inherited vertex topology.
See Cairns' normalized mapping space on p. 801 and M76 derivation 18. -/
abbrev UnitRadialEmbedding (A : AbstractSimplicialComplex ι) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {v : A.RadialEmbedding E // ∀ i, ‖v.val i‖ = 1}

/-- The full radial embedding space and its unit-vertex subspace are
homotopy equivalent via normalization and inclusion. This precedes the
coordinate-change quotient in Cairns Lemma 5.3; see M76 derivation 18. -/
noncomputable def radialNormalizationHomotopyEquiv (A : AbstractSimplicialComplex ι)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.HomotopyEquiv (A.RadialEmbedding E) (A.UnitRadialEmbedding E) where
  toFun := ⟨fun v => ⟨v.normalized, v.norm_normalized⟩,
    RadialEmbedding.continuous_normalized.subtype_mk _⟩
  invFun := ⟨Subtype.val, continuous_subtype_val⟩
  left_inv := ⟨(radialNormalizationHomotopy A E).symm⟩
  right_inv := by
    have heq : (⟨fun v : A.RadialEmbedding E => ⟨v.normalized, v.norm_normalized⟩,
        RadialEmbedding.continuous_normalized.subtype_mk _⟩ :
          C(A.RadialEmbedding E, A.UnitRadialEmbedding E)).comp
        ⟨Subtype.val, continuous_subtype_val⟩ = ContinuousMap.id (A.UnitRadialEmbedding E) := by
      apply ContinuousMap.ext
      intro v
      exact Subtype.ext (v.val.normalized_eq_self v.property)
    rw [heq]

/-- Contractibility transfers exactly between a radial vertex space
and its unit-vertex subspace. See Cairns pp. 801, 807 and M76 derivation 18. -/
theorem contractible_radialEmbedding_iff (A : AbstractSimplicialComplex ι)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContractibleSpace (A.RadialEmbedding E) ↔ ContractibleSpace (A.UnitRadialEmbedding E) :=
  (radialNormalizationHomotopyEquiv A E).contractibleSpace_iff

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/FixedRadialNormalization.lean
section

/-!
# Radial normalization relative to prescribed unit vertices

The radial deformation restricts to realizations fixing any chosen set
of unit vertex positions. It gives a homotopy equivalence with their
unit-vertex subspace. This is the fixed-simplex version of Cairns 1940,
Lemma 5.3, pp. 801--802; see M76 derivation 24.
-/


open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial realizations with prescribed values on selected labels.
See Cairns p. 801 and M76 derivation 24. -/
abbrev FixedRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.RadialEmbedding E // EqOn v.val w s}

/-- Unit radial realizations with the same selected vertex values.
See Cairns p. 801 and M76 derivation 24. -/
abbrev FixedUnitRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.UnitRadialEmbedding E // EqOn v.val.val w s}

variable {A : AbstractSimplicialComplex ι} {s : Set ι} {w : ι → E}

/-- Normalize a constrained realization while retaining each prescribed
unit coordinate. See Cairns Lemma 5.3 and M76 derivation 24. -/
noncomputable def FixedRadialEmbedding.normalized (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (v : A.FixedRadialEmbedding s w) : A.FixedUnitRadialEmbedding s w :=
  ⟨⟨v.val.normalized, v.val.norm_normalized⟩, by
    intro i hi
    change NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi)]⟩

/-- Forget the unit condition while preserving the prescribed values.
See Cairns Lemma 5.3 and M76 derivation 24. -/
def FixedUnitRadialEmbedding.toFixedRadial (v : A.FixedUnitRadialEmbedding s w) :
    A.FixedRadialEmbedding s w := ⟨v.val.val, v.property⟩

/-- Constrained vertex normalization is continuous in vertex topology.
See Cairns p. 801 and M76 derivation 24. -/
theorem FixedRadialEmbedding.continuous_normalized (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (FixedRadialEmbedding.normalized hw :
      A.FixedRadialEmbedding s w → A.FixedUnitRadialEmbedding s w) :=
  ((RadialEmbedding.continuous_normalized.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- Forgetting the unit condition is continuous.
See Cairns p. 801 and M76 derivation 24. -/
theorem FixedUnitRadialEmbedding.continuous_toFixedRadial :
    Continuous (FixedUnitRadialEmbedding.toFixedRadial :
      A.FixedUnitRadialEmbedding s w → A.FixedRadialEmbedding s w) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The straight radial deformation preserves all prescribed unit
vertices at every time. See Cairns Lemma 5.3 and M76 derivation 24. -/
noncomputable def FixedRadialEmbedding.interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (t : I) (v : A.FixedRadialEmbedding s w) : A.FixedRadialEmbedding s w :=
  ⟨v.val.interpolate t, by
    intro i hi
    change (1 - (t : ℝ)) • v.val.val i + (t : ℝ) • NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi), ← add_smul]
    simp⟩

/-- The constrained deformation is jointly continuous in time and the
original realization. See Cairns p. 801 and M76 derivation 24. -/
theorem FixedRadialEmbedding.continuous_interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (fun tv : I × A.FixedRadialEmbedding s w => tv.2.interpolate hw tv.1) :=
  (RadialEmbedding.continuous_interpolate.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- Radial normalization is a homotopy equivalence relative to any
prescribed collection of unit vertices, including an empty collection.
See Cairns Lemma 5.3 and M76 derivation 24. -/
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

/-- Contractibility transfers between radial realizations with fixed
unit coordinates and their unit-vertex subspace.
See Cairns pp. 801, 807 and M76 derivation 24. -/
theorem contractible_fixedRadialEmbedding_iff (A : AbstractSimplicialComplex ι)
    (s : Set ι) (w : ι → E) (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ContractibleSpace (A.FixedRadialEmbedding s w) ↔
      ContractibleSpace (A.FixedUnitRadialEmbedding s w) :=
  (fixedRadialNormalizationHomotopyEquiv A s w hw).contractibleSpace_iff

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/BasisRadialProjection.lean
section

/-!
# Radial realizations in ambient linear-map coordinates

When the source vertices form a basis of their span, their radial
realizations correspond homeomorphically to ambient linear maps with
the same column data. Prescribed vertex values are retained. This is
the coordinate part of Cairns 1940, Lemma 5.1, p. 801, preceding the
comparison with transverse kernels; see M76 derivation 25.
-/


open Set

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ambient linear maps whose basis images form a faithful radial
realization. This is a coordinate model, prior to the transverse-kernel
comparison. See Cairns p. 801 and M76 derivation 25. -/
abbrev BasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  {Q : E →L[ℝ] F // A.IsRadialEmbedding (fun i => Q (b i))}

/-- Evaluation on the source vertex basis identifies the linear-map
model with the actual radial vertex space.
See Cairns p. 801 and M76 derivation 25. -/
noncomputable def basisRadialProjectionHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    A.BasisRadialProjection b F ≃ₜ A.RadialEmbedding F :=
  b.evaluationContinuousLinearEquiv.toHomeomorph.subtype (fun Q => by
    change A.IsRadialEmbedding (fun i => Q (b i)) ↔
      A.IsRadialEmbedding (b.evaluationContinuousLinearEquiv Q)
    have he : b.evaluationContinuousLinearEquiv Q = fun i => Q (b i) :=
      funext (b.evaluationContinuousLinearEquiv_apply Q)
    rw [he])

/-- The linear-map model with selected column values fixed.
See Cairns p. 801 and M76 derivation 25. -/
abbrev FixedBasisRadialProjection (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E)
    (s : Set ι) (w : ι → F) :=
  {Q : A.BasisRadialProjection b F // EqOn (fun i => Q.val (b i)) w s}

/-- Fixed source-basis columns correspond exactly to fixed vertex
coordinates, with both subspace topologies unchanged.
See Cairns p. 801 and M76 derivation 25. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialRealizationCones.lean
section

/-!
# Geometric cones of labelled radial realizations

The actual geometric complexes underlying faithful radial vertex data
have conical carriers. A linear map preserving the vertex labels gives
a homeomorphism of these cones. This connects the operator coordinates
to the stars in Cairns 1940, pp. 799, 801; see M76 derivation 26.
-/


open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {A : AbstractSimplicialComplex ι}

/-- The geometric complex certified by a faithful radial realization.
Its faces are determined uniquely by the labelled data.
See Cairns p. 801 and M76 derivation 26. -/
noncomputable def RadialEmbedding.complex (v : A.RadialEmbedding E) :
    SimplicialComplex ℝ E := v.property.2.choose

/-- The realized complex has exactly the prescribed labelled faces.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_faces (v : A.RadialEmbedding E) :
    v.complex.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v.val '' (s : Set ι)} :=
  v.property.2.choose_spec.1

/-- Position vectors on every realized face are independent.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_linearIndependent (v : A.RadialEmbedding E) :
    ∀ s ∈ v.complex.faces, LinearIndependent ℝ ((↑) : s → E) :=
  v.property.2.choose_spec.2.1

/-- Central projection is injective on the realized link.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_injOn_normalize (v : A.RadialEmbedding E) :
    InjOn (NormedSpace.normalize : E → E) v.complex.space :=
  v.property.2.choose_spec.2.2

/-- Face images can equivalently be expressed as finite-set images.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_faces_image [DecidableEq E] (v : A.RadialEmbedding E) :
    v.complex.faces = (fun s : Finset ι => s.image v.val) '' A.faces := by
  rw [v.complex_faces]
  ext t
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, Finset.coe_injective (Finset.coe_image.trans he.symm)⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, Finset.coe_image⟩

/-- The realized vertices are exactly the labelled vertex range.
See Cairns p. 801 and M76 derivation 26. -/
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

/-- Finite labels give a finite geometric complex.
See Cairns pp. 799, 801 and M76 derivation 26. -/
theorem RadialEmbedding.finite_complex_faces [Finite ι] (v : A.RadialEmbedding E) :
    v.complex.faces.Finite := by
  classical
  let := Fintype.ofFinite ι
  rw [v.complex_faces_image]
  exact (Set.toFinite A.faces).image _

/-- Cone the realized radial link to the origin.
See Cairns pp. 799, 801 and M76 derivation 26. -/
noncomputable def RadialEmbedding.cone (v : A.RadialEmbedding E) : SimplicialComplex ℝ E := by
  classical
  exact v.complex.coneAtZero v.complex_linearIndependent v.complex_injOn_normalize

/-- A vertex-compatible linear map restricts to a PL homeomorphism of
the two full cones. See Cairns p. 799 and M76 derivation 26. -/
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

/-- A vertex-compatible linear map is injective on the full cone.
See Cairns p. 799 and M76 derivation 26. -/
theorem RadialEmbedding.injOn_cone_of_linearMap [Finite ι]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (v : A.RadialEmbedding E) (w : A.RadialEmbedding F)
    (Q : E →L[ℝ] F) (hQ : ∀ i, Q (v.val i) = w.val i) : InjOn Q v.cone.space := by
  obtain ⟨_, e, _, he, _⟩ := v.exists_cone_homeomorph_of_linearMap w Q hQ
  intro x hx y hy hxy
  have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
    Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm))
  exact congrArg Subtype.val (e.injective hexy)

/-- A source basis is a faithful radial realization of any labelled
complex on the same index type. See Cairns p. 799 and M76 derivation 26. -/
noncomputable def basisRadialEmbedding (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) : A.RadialEmbedding E :=
  ⟨b, A.isRadialEmbedding_of_linearIndependent b.linearIndependent⟩

/-- A point of the operator-coordinate model is geometrically
injective on the cone of the source basis realization.
See Cairns p. 799 and M76 derivation 26. -/
theorem BasisRadialProjection.injOn_basisCone [Finite ι]
    [FiniteDimensional ℝ F] {b : Module.Basis ι ℝ E}
    (Q : A.BasisRadialProjection b F) : InjOn Q.val (A.basisRadialEmbedding b).cone.space := by
  let := b.finiteDimensional_of_finite
  exact (A.basisRadialEmbedding b).injOn_cone_of_linearMap
    ⟨fun i => Q.val (b i), Q.property⟩ Q.val (fun _ => rfl)

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialConeCarriers.lean
section

/-!
# Labelled simplices in radial cone carriers

The cone of a radial realization is the union of its labelled bounded
cone simplices, with the empty labelled face supplying the center.
See Cairns 1940, pp. 799--800, and M76 derivation 27.
-/


open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

/-- The cone carrier is the union of the bounded labelled simplices
obtained by adjoining zero. The extra empty label face accounts for
the center when there are no vertices. See Cairns p. 799 and
M76 derivation 27. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/UniformSecantProjection.lean
section

/-!
# Uniform secant bounds for general-position star projections

A linear map injective on a finite union of basis cone simplices has
a uniform positive lower bound on all secants. In particular the
radial operator-coordinate model supplies the geometric transversality
estimate. See Cairns 1940, pp. 799--800, and M76 derivation 27.
-/


open Set

namespace Module.Basis

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A projection injective on a union of bounded independent cone
simplices has a uniform positive lower secant bound. No manifold or
intersection-law premise is needed for this estimate.
See Cairns p. 799 and M76 derivation 27. -/
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

/-- Every radial basis projection satisfies a uniform secant bound
on its actual source star. This supplies the quantitative geometric
part of Cairns' transversality condition, not merely injectivity of
the vertex list. See Cairns p. 799 and M76 derivation 27. -/
theorem BasisRadialProjection.exists_pos_secant_bound (Q : A.BasisRadialProjection b F) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (A.basisRadialEmbedding b).cone.space,
      ∀ y ∈ (A.basisRadialEmbedding b).cone.space,
      c * ‖x - y‖ ≤ ‖Q.val x - Q.val y‖ := by
  have hQ := Q.injOn_basisCone
  rw [RadialEmbedding.cone_space] at hQ ⊢
  exact b.exists_pos_secant_bound_of_injOn (insert ∅ A.faces) Q.val hQ

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/BasisProjectionConverse.lean
section

/-!
# Geometric converse for radial basis projections

Injectivity of a linear projection on the entire independent source
cone implies faithful radial realization of its labelled link. Thus
the operator-coordinate model has precisely the geometric projection
domain. See Cairns 1940, pp. 799, 801, and M76 derivation 29.
-/


open Set Geometry NormedSpace

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear map embedding the full basis cone gives a faithful
radial realization of the labelled link. Both face independence and
radial injectivity follow from the geometric premise.
See Cairns p. 799 and M76 derivation 29. -/
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

/-- Radial operator coordinates are equivalent to injective linear
projections of the actual full source star.
See Cairns pp. 799, 801 and M76 derivation 29. -/
theorem isRadialEmbedding_iff_injOn_basisCone [FiniteDimensional ℝ F]
    (A : AbstractSimplicialComplex ι) (b : Module.Basis ι ℝ E) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔ InjOn Q (A.basisRadialEmbedding b).cone.space :=
  ⟨fun h => BasisRadialProjection.injOn_basisCone (⟨Q, h⟩ : A.BasisRadialProjection b F),
    A.isRadialEmbedding_of_injOn_basisCone b Q⟩

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/ComplementPlaneCoordinates.lean
section

/-!
# Complementary planes and normalized projection coordinates

Planes complementary to a fixed coordinate subspace are homeomorphic
to linear retractions onto that subspace. The plane topology is given
by orthogonal projectors; continuity in both directions follows from
the geometric kernel and frame formulas. See Cairns 1940, Lemma 5.1,
p. 801, and M76 derivation 28.
-/


open Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Complements of a fixed coordinate plane with their geometric
subspace topology. See Cairns p. 801 and M76 derivation 28. -/
abbrev ComplementPlaneSpace (U : Submodule ℝ E) :=
  {K : EuclideanSubspace E // IsCompl U K.subspace}

/-- Continuous linear projections fixing the prescribed coordinate
plane pointwise, with the operator topology.
See Cairns p. 801 and M76 derivation 28. -/
abbrev RetractionSpace (U : Submodule ℝ E) :=
  {Q : E →L[ℝ] U // ∀ u : U, Q u = u}

/-- A complementary plane determines the linear retraction along it.
See Cairns p. 801 and M76 derivation 28. -/
noncomputable def complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    U.RetractionSpace :=
  ⟨(U.projectionOnto K.val.subspace K.property).toContinuousLinearMap,
    fun u => projectionOnto_apply_left K.property u⟩

/-- The retraction along a complementary plane has exactly that
kernel. See Cairns p. 801 and M76 derivation 28. -/
theorem ker_complementRetraction (U : Submodule ℝ E) (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val.ker = K.val.subspace :=
  ker_projectionOnto K.property

/-- A normalized projection has a complementary kernel.
See Cairns p. 801 and M76 derivation 28. -/
def retractionKernel (U : Submodule ℝ E) (Q : U.RetractionSpace) : U.ComplementPlaneSpace :=
  ⟨⟨Q.val.ker⟩, LinearMap.isCompl_of_proj Q.property⟩

/-- Passing from a complementary plane to its projection and back
recovers the geometric plane. See Cairns p. 801 and M76 derivation 28. -/
theorem retractionKernel_complementRetraction (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) : U.retractionKernel (U.complementRetraction K) = K := by
  apply Subtype.ext
  apply EuclideanSubspace.ext
  exact U.ker_complementRetraction K

/-- Passing from a projection to its kernel and back recovers the
normalized projection. See Cairns p. 801 and M76 derivation 28. -/
theorem complementRetraction_retractionKernel (U : Submodule ℝ E)
    (Q : U.RetractionSpace) : U.complementRetraction (U.retractionKernel Q) = Q := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun L : E →ₗ[ℝ] U => L x)
    (Q.val.toLinearMap.projectionOnto_of_proj Q.property)

/-- The kernel map is continuous in orthogonal-projector topology.
Every retraction is surjective by its fixed-plane identity.
See Cairns pp. 800--801 and M76 derivation 28. -/
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

/-- The retraction associated with a plane is its fixed-frame Gram
formula in the plane's geometric projector coordinates.
See Cairns p. 801 and M76 derivation 28. -/
theorem complementRetraction_eq_frameFormula (U : Submodule ℝ E)
    (K : U.ComplementPlaneSpace) :
    (U.complementRetraction K).val =
      ContinuousLinearMap.frameProjectionFormula U.subtypeL K.val.subspace.starProjection := by
  have he := (U.complementRetraction K).val.frameProjectionFormula_ker U.subtypeL
    (U.complementRetraction K).property
  simpa only [U.ker_complementRetraction K] using he.symm

/-- The inverse kernel correspondence is continuous in the actual
plane topology, including for a nonorthogonal complement.
See Cairns p. 801 and M76 derivation 28. -/
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

/-- Complementary planes and normalized projections are homeomorphic
with their geometric and operator topologies respectively.
See Cairns Lemma 5.1, p. 801, and M76 derivation 28. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SecantTransversality.lean
section

/-!
# Geometric secant transversality

A plane is transverse to a set when all its secants have a uniform
positive relative distance from the plane. This orthogonal-projector
form of Cairns' angle condition is independent of projection coordinates.
See Cairns 1940, pp. 799--800, and M76 derivation 30.
-/


open Set

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A uniform positive relative distance of all secants from a plane.
The dimension of the plane is specified separately.
See Cairns pp. 799--800 and M76 derivation 30. -/
def IsSecantTransverse (K : Submodule ℝ E) (S : Set E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ S, ∀ y ∈ S,
    c * ‖x - y‖ ≤ ‖(x - y) - K.starProjection (x - y)‖

/-- A positive lower projection bound implies the geometric secant
condition for its kernel, including for a zero operator on a singleton.
See Cairns p. 799 and M76 derivation 30. -/
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

/-- Geometric transversality implies injectivity of any linear map
with the specified kernel. See Cairns p. 799 and M76 derivation 30. -/
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

/-- Restricting a set preserves the uniform secant condition.
See Cairns Section 4(B), p. 800, and M76 derivation 30. -/
theorem IsSecantTransverse.mono {K : Submodule ℝ E} {S T : Set E}
    (hK : K.IsSecantTransverse T) (hST : S ⊆ T) : K.IsSecantTransverse S := by
  obtain ⟨c, hc, hb⟩ := hK
  exact ⟨c, hc, fun x hx y hy => hb x (hST hx) y (hST hy)⟩

/-- The secant condition survives a small change of the geometric
orthogonal projector. See Cairns pp. 798--800 and M76 derivation 30. -/
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

/-- Planes transverse to a fixed set form an open subset in geometric
projector topology. See Cairns pp. 798--800 and M76 derivation 30. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/BasisTransversePlanes.lean
section

/-!
# Transverse planes of independent source stars

Geometric secant transversality is equivalent to the radial realization
condition on basis images. Restricting the complementary-plane
homeomorphism therefore gives the actual transverse-plane coordinates.
See Cairns 1940, pp. 799--801, and M76 derivation 30.
-/


open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Planes transverse to the source set and complementary to the
specified coordinate plane, in geometric projector topology.
See Cairns pp. 799--801 and M76 derivation 30. -/
abbrev TransverseComplementPlaneSpace (U : Submodule ℝ E) (S : Set E) :=
  {K : U.ComplementPlaneSpace // K.val.subspace.IsSecantTransverse S}

/-- The complementary-plane correspondence restricts to transverse
kernels with their actual geometric secant condition.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def transversePlaneRetractionHomeomorph (U : Submodule ℝ E) (S : Set E) :
    U.TransverseComplementPlaneSpace S ≃ₜ
      {Q : U.RetractionSpace // Q.val.ker.IsSecantTransverse S} :=
  U.complementPlaneHomeomorph.subtype (fun K => by
    change K.val.subspace.IsSecantTransverse S ↔
      (U.complementRetraction K).val.ker.IsSecantTransverse S
    rw [U.ker_complementRetraction K])

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The kernel-plane angle condition is exactly faithful radial
realization for the images of the independent source vertices.
See Cairns pp. 799--801 and M76 derivation 30. -/
theorem isRadialEmbedding_iff_isSecantTransverse_ker (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (Q : E →L[ℝ] F) :
    A.IsRadialEmbedding (fun i => Q (b i)) ↔
      Q.ker.IsSecantTransverse (A.basisRadialEmbedding b).cone.space := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ :=
      BasisRadialProjection.exists_pos_secant_bound (⟨Q, h⟩ : A.BasisRadialProjection b F)
    exact Submodule.isSecantTransverse_ker_of_lower_bound Q hc hb
  · intro h
    exact A.isRadialEmbedding_of_injOn_basisCone b Q (h.injOn Q rfl)

/-- Transverse planes of a full basis star are homeomorphic to radial
retractions onto the chosen coordinate plane. Both topologies are
the pre-existing geometric and operator subspace topologies.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def basisTransversePlaneHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (U : Submodule ℝ E) :
    U.TransverseComplementPlaneSpace (A.basisRadialEmbedding b).cone.space ≃ₜ
      {Q : U.RetractionSpace // A.IsRadialEmbedding (fun i => Q.val (b i))} :=
  (U.transversePlaneRetractionHomeomorph (A.basisRadialEmbedding b).cone.space).trans
    (Homeomorph.setCongr (by
      ext Q
      exact (A.isRadialEmbedding_iff_isSecantTransverse_ker b Q.val).symm))

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/FramePlaneCoordinates.lean
section

/-!
# Coordinates in an arbitrary independent frame

The normalized kernel correspondence can use an arbitrary injective
frame with its own coordinate type, rather than the subtype of its
image. Only a continuous linear change of target coordinates is used.
See Cairns 1940, Lemma 5.1, p. 801, and M76 derivation 30.
-/


namespace ContinuousLinearMap

/-- Projection operators fixing a given coordinate frame.
See Cairns p. 801 and M76 derivation 30. -/
abbrev FrameProjectionSpace {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J : F →L[ℝ] E) :=
  {Q : E →L[ℝ] F // Function.RightInverse J Q}

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Changing the target from frame coordinates to the actual frame
subspace identifies normalized operators with retractions.
See Cairns p. 801 and M76 derivation 30. -/
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
/-- Target-coordinate conversion preserves the geometric kernel.
See Cairns p. 801 and M76 derivation 30. -/
theorem ker_frameRetractionHomeomorph (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (Q : J.FrameProjectionSpace) :
    ((J.frameRetractionHomeomorph hJ) Q).val.ker = Q.val.ker := by
  let e := (LinearEquiv.ofInjective J.toLinearMap hJ).toContinuousLinearEquiv
  ext x
  change e (Q.val x) = 0 ↔ Q.val x = 0
  exact e.map_eq_zero_iff

/-- Complementary geometric planes correspond to projections fixing
any independent coordinate frame.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def frameComplementPlaneHomeomorph (J : F →L[ℝ] E)
    (hJ : Function.Injective J) :
    J.range.ComplementPlaneSpace ≃ₜ J.FrameProjectionSpace :=
  J.range.complementPlaneHomeomorph.trans (J.frameRetractionHomeomorph hJ).symm

/-- The frame-normalized projection has exactly its original plane
as kernel. See Cairns p. 801 and M76 derivation 30. -/
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

/-- The geometric transverse-plane correspondence in independent
frame coordinates, with exact radial realization as its range.
See Cairns Lemma 5.1, p. 801, and M76 derivation 30. -/
noncomputable def frameBasisPlaneHomeomorph (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) (J : F →L[ℝ] E) (hJ : Function.Injective J) :
    J.range.TransverseComplementPlaneSpace (A.basisRadialEmbedding b).cone.space ≃ₜ
      {Q : J.FrameProjectionSpace // A.IsRadialEmbedding (fun i => Q.val (b i))} :=
  (J.frameComplementPlaneHomeomorph hJ).subtype (fun K => by
    rw [A.isRadialEmbedding_iff_isSecantTransverse_ker,
      J.ker_frameComplementPlaneHomeomorph hJ])

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/GeometricFrameField.lean
section

/-!
# A common-frame representative of a geometric smooth leaf field

Where the planes complement a fixed frame, their Gram formula
gives one smooth normalized operator field with exactly the same
geometric kernels and local leaf constancy. See Cairns 1940,
pp. 800--801, 804--805 and M76 derivation 60.
-/


open Set Filter Geometry
open scoped Topology ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The geometric frame formula fixes the frame and has exactly
the prescribed complementary plane as its kernel.
See Cairns p. 801 and M76 derivation 60. -/
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

/-- Complementarity to one frame on a domain provides a single
smooth normalized representative of a geometric leaf field there,
with exact kernels and local leaf constancy.
See Cairns pp. 801, 804--805 and M76 derivation 60. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/TransversePlaneDimension.lean
section

/-!
# The dimension and face-complement condition for transverse planes

For an independent source star, a transverse plane meets each face
span only in zero. With complementary dimensions this is the full
complement condition, so choosing a frame face does not restrict the
geometric transverse-plane space. See Cairns 1940, pp. 799--801,
and M76 derivation 31.
-/


open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- All geometric planes of the indicated codimension transverse to
a set. The dimension equation avoids truncated subtraction.
See Cairns p. 800 and M76 derivation 31. -/
abbrev SecantTransversePlaneSpace (d : ℕ) (S : Set E) :=
  {K : EuclideanSubspace E // Module.finrank ℝ K.subspace + d = Module.finrank ℝ E ∧
    K.subspace.IsSecantTransverse S}

/-- When every transverse plane misses a fixed d-dimensional frame,
the full codimension-d plane space equals the transverse-complement
space in geometric topology. See Cairns p. 801 and M76 derivation 31. -/
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

/-- A transverse kernel misses the entire span of any source face,
including vectors outside its bounded cone simplex.
See Cairns pp. 799--801 and M76 derivation 31. -/
theorem disjoint_faceSpan_of_isSecantTransverse (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) {s : Finset ι} (hs : s ∈ A.faces)
    {K : Submodule ℝ E} (hK : K.IsSecantTransverse (A.basisRadialEmbedding b).cone.space) :
    Disjoint (Submodule.span ℝ (b '' (s : Set ι))) K := by
  let R := ContinuousLinearMap.id ℝ E - K.starProjection
  have hker : R.ker = K := by
    ext x
    change (x - K.starProjection x = 0) ↔ x ∈ K
    rw [sub_eq_zero, eq_comm, K.starProjection_eq_self_iff]
  have hsimplex : convexHull ℝ (insert 0 (b '' (s : Set ι))) ⊆
      (A.basisRadialEmbedding b).cone.space := by
    rw [RadialEmbedding.cone_space]
    exact subset_iUnion₂_of_subset s (mem_insert_of_mem _ hs) Subset.rfl
  have hinj := b.injOn_span_of_injOn_simplex R ((hK.injOn R hker).mono hsimplex)
  apply Submodule.disjoint_def.mpr
  intro x hx hk
  apply hinj hx (Submodule.zero_mem _)
  change x - K.starProjection x = 0 - K.starProjection 0
  rw [K.starProjection_eq_self_iff.mpr hk, map_zero, sub_self, sub_self]

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SmoothTransverseFrames.lean
section

/-!
# Common-frame neighborhoods for smooth transverse plane fields

Geometric transversality is open. A coface frame and the codimension
equation imply complementarity throughout this open restriction,
so the field has one smooth normalized representative there.
See Cairns 1940, pp. 800--801, 804--805 and M76 derivation 60.
-/


open Set Filter
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- An open transverse restriction of a geometric smooth leaf
field admits a common-frame representative. Disjointness from the
frame and the exact codimension equation imply complementarity.
See Cairns pp. 800--801, 804--805 and M76 derivation 60. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialBallQuotient.lean
section

/-!
# The closed ball as a quotient of radial sphere coordinates

The radial map from the unit interval times the unit sphere onto
the closed unit ball collapses only the radius-zero fiber. For a
proper normed space it is a quotient map. This is the elementary
cone construction used for Cairns' core extension, p. 804; see M76
derivation 43.
-/


open Set Metric unitInterval

namespace NormedSpace

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial sphere coordinates on the closed unit ball, with
radius in the unit interval. See Cairns p. 804 and M76 derivation 43. -/
noncomputable def unitSphereRadialMap : C(I × sphere (0 : E) 1, closedBall (0 : E) 1) := by
  refine ⟨fun z => ⟨(z.1 : ℝ) • (z.2 : E), ?_⟩, ?_⟩
  · rename_i z
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg z.1.property.1,
      norm_eq_of_mem_sphere z.2, mul_one]
    exact z.1.property.2
  · fun_prop

/-- The norm of a radial point is its nonnegative radius.
See Cairns p. 804 and M76 derivation 43. -/
theorem norm_unitSphereRadialMap (z : I × sphere (0 : E) 1) :
    ‖(unitSphereRadialMap E z : E)‖ = (z.1 : ℝ) := by
  change ‖(z.1 : ℝ) • (z.2 : E)‖ = (z.1 : ℝ)
  rw [norm_smul, Real.norm_of_nonneg z.1.property.1, norm_eq_of_mem_sphere z.2, mul_one]

/-- Radial coordinates identify only equal positive-radius points
and the entire radius-zero fiber.
See Cairns p. 804 and M76 derivation 43. -/
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

/-- Every point of the closed unit ball has radial sphere
coordinates, choosing any sphere point over the origin.
See Cairns p. 804 and M76 derivation 43. -/
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

/-- Compact radial sphere coordinates make the closed ball a
quotient of the interval times the sphere.
See Cairns p. 804 and M76 derivation 43. -/
theorem isQuotientMap_unitSphereRadialMap : Topology.IsQuotientMap (unitSphereRadialMap E) :=
  Topology.IsQuotientMap.of_surjective_continuous (surjective_unitSphereRadialMap E)
    (unitSphereRadialMap E).continuous

end NormedSpace

end

-- Source: PoincareMT/Proofs/M76/Mathlib/ContractibleBallExtension.lean
section

/-!
# Extending sphere maps into contractible targets

A nullhomotopy descends through radial sphere coordinates to the
closed ball. Thus every continuous sphere map into a contractible
space extends over the ball, including dimension zero. See Cairns
1940, Section 8, p. 804, and M76 derivation 43.
-/


open Set Metric unitInterval NormedSpace

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace Y]

/-- A nullhomotopic sphere map extends continuously over the
closed unit ball, with exact agreement on the whole sphere.
See Cairns p. 804 and M76 derivation 43. -/
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

/-- Every sphere map into a contractible target has a continuous
closed-ball extension. Target compactness and separation are not
required. See Cairns p. 804 and M76 derivation 43. -/
theorem exists_closedBall_extension_of_contractible (f : C(sphere (0 : E) 1, Y)) :
    ∃ g : C(closedBall (0 : E) 1, Y),
      ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = f x := by
  have hf : f.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using (id_nullhomotopic Y).comp_left f
  exact hf.exists_closedBall_extension f

end ContinuousMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/ContractibleConvexExtension.lean
section

/-!
# Extending frontier maps across convex cores

Gauge coordinates carry a bounded convex body's closure and frontier
to the closed ball and sphere. Thus maps into a contractible target
extend across the body with exact boundary agreement. See Cairns
1940, Section 8, p. 804, and M76 derivation 43.
-/


open Set Metric

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace Y] [ContractibleSpace Y]

/-- Every continuous frontier map of a closed bounded convex
body with nonempty interior extends across the body into the same
contractible target. Apply this in a core's affine span.
See Cairns p. 804 and M76 derivation 43. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ContractibleMappingSpace.lean
section

/-!
# Contracting a space of continuous parameter families

A contraction of the target induces a contraction of the compact-open
mapping space when the source is locally compact. This retains all
transverse-slice parameters in Cairns' core extension, pp. 804--805;
see M76 derivation 56.
-/


open unitInterval

namespace ContinuousMap

/-- Contractibility of the target gives contractibility of its
continuous mapping space over any locally compact source, using
the compact-open topology. See Cairns p. 804 and M76 derivation 56. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ParametricConvexExtension.lean
section

/-!
# Continuous core extension retaining all slice parameters

Currying into a contractible compact-open mapping space extends
boundary data jointly in the core and parameter coordinates.
See Cairns 1940, pp. 804--805 and M76 derivation 56.
-/


open Set

namespace ContinuousMap

variable {E B Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace B] [LocallyCompactSpace B] [TopologicalSpace Y] [ContractibleSpace Y]

/-- A continuous family of maps on a convex body's frontier
extends jointly over the body, retaining every parameter and
exact boundary values. See Cairns p. 804 and M76 derivation 56. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ConvexCoreCollar.lean
section

/-!
# A smaller convex core inside a prescribed collar

A compact convex body with nonempty interior contains a smaller
compact convex body whose exterior collar lies in any prescribed
open neighborhood of the original frontier. The construction is
an inward homothety about an interior point. See Cairns 1940,
Section 8, p. 804, and M76 derivation 47.
-/


open Set Filter
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Shrink a compact convex body into its interior, retaining
every point away from the prescribed boundary neighborhood in
the smaller body's interior. See Cairns p. 804 and M76 derivation 47. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ParametricCorePasting.lean
section

/-!
# Pasting a core filling uniformly in the slice parameters

The parameterized frontier extension pastes to the existing map
on the whole product space. A uniform boundary collar permits
retaining a neighborhood of the original exterior for every
parameter. See Cairns 1940, pp. 804--805 and M76 derivation 56.
-/


open Set Filter
open scoped Topology

namespace ContinuousMap

variable {E B Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace B] [LocallyCompactSpace B] [TopologicalSpace Z]

/-- Fill a convex core jointly in all parameters, preserving the
old map outside the core interior for every parameter. See Cairns
p. 804 and M76 derivation 56. -/
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

/-- A uniform target-valued boundary collar permits a filling
that retains the original map near the exterior of the core,
simultaneously for all parameters. See Cairns p. 804 and M76 derivation 56. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineFrameNormalization.lean
section

/-!
# Smooth affine normalization to a fixed projection frame

A fixed right inverse gives an affine retraction onto all
operators fixing the same frame. Kernel planes vary continuously
after this normalization, and secant transversality pulls back
to an open operator condition. See Cairns 1940, pp. 801, 804,
and M76 derivation 46.
-/


open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Affine retraction onto the operators fixing `J`, when `Q0`
is a right inverse of that frame. See Cairns pp. 801, 804 and
M76 derivation 46. -/
def frameNormalize (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F) : E →L[ℝ] F :=
  Q + (ContinuousLinearMap.id ℝ F - Q.comp J).comp Q0

/-- The normalized operator fixes the frame exactly.
See Cairns pp. 801, 804 and M76 derivation 46. -/
theorem rightInverse_frameNormalize (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (Q : E →L[ℝ] F) :
    Function.RightInverse J (frameNormalize J Q0 Q) := by
  intro x
  change Q (J x) + (Q0 (J x) - Q (J (Q0 (J x)))) = x
  rw [h0 x]
  abel

/-- Already normalized operators are fixed by the affine
normalization. See Cairns pp. 801, 804 and M76 derivation 46. -/
theorem frameNormalize_eq_self (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F)
    (hQ : Function.RightInverse J Q) : frameNormalize J Q0 Q = Q := by
  ext x
  change Q x + (Q0 x - Q (J (Q0 x))) = Q x
  rw [hQ (Q0 x), sub_self, add_zero]

/-- The affine normalization is smooth on the whole operator
space. See Cairns p. 804 and M76 derivation 46. -/
theorem contDiff_frameNormalize (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F) (n : ℕ∞ω) :
    ContDiff ℝ n (frameNormalize J Q0) :=
  contDiff_id.add ((contDiff_const.sub (contDiff_id.clm_comp contDiff_const)).clm_comp
    contDiff_const)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Transversality after frame normalization is an open
condition on the unrestricted operator space.
See Cairns pp. 799--801, 804 and M76 derivation 46. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/NormalizedFieldExtension.lean
section

/-!
# Ambient extension of normalized operator fields

Finite-dimensional Tietze extension followed by affine frame
normalization extends continuous field data from a closed subset,
retaining their exact values and fixed frame. See Cairns 1940,
Section 8, p. 804, and M76 derivation 46.
-/


open Set ContinuousLinearMap

namespace ContinuousMap

variable {X E F : Type*} [TopologicalSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Extend a continuous normalized field from any closed set
to the entire ambient source, with exact restriction and frame
normalization. See Cairns p. 804 and M76 derivation 46. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ParametricNormalizedExtension.lean
section

/-!
# Normalized ambient extension of a parameterized transverse filling

Compact-open neighborhoods supply a uniform collar for all parameters
in a compact set. After the core filling, normalized Tietze extension
gives a field on the full slice, preserving the old germ over the
interior of the parameter set. See Cairns 1940, pp. 804--805 and
M76 derivation 57.
-/


open Set Filter ContinuousLinearMap ContinuousMap
open scoped Topology ContDiff

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Fill a normalized field jointly in compact parameters, then
extend it continuously to the whole slice. The old germ is retained
over the core exterior and the parameter interior. See Cairns p. 804
and M76 derivation 57. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/RelativeSmoothOpenTarget.lean
section

/-!
# Relative smooth approximation preserving an open target

Compactness gives a positive tolerance inside an open target.
Mathlib's relative smooth approximation then preserves the target
on the compact set and agrees exactly with existing smooth data
on a closed relative set. See Cairns 1940, Section 8, p. 804,
and M76 derivation 46.
-/


open Set
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Approximate a continuous map smoothly, preserving an open
target on a compact set and agreeing exactly on a closed set
near which the original map is already smooth.
See Cairns p. 804 and M76 derivation 46. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/RelativeTransverseSmoothing.lean
section

/-!
# Relative smoothing of normalized transverse fields

Smooth approximation in the open preimage of the transverse-plane
space, followed by affine frame normalization, keeps the kernels
transverse on the compact core and fixes existing smooth data.
See Cairns 1940, Section 8, p. 804, and M76 derivation 46.
-/


open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A continuous normalized projection field admits relative
smooth replacement, with the same normalization everywhere and
transverse kernels on the whole compact core. The original field
must already be smooth near the closed relative set.
See Cairns p. 804 and M76 derivation 46. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/RelativeTransverseGerms.lean
section

/-!
# Relative transverse smoothing preserving whole germs

Fix a closed neighborhood of the prescribed relative set during
smooth approximation. The resulting normalized transverse field
agrees with the old field on a neighborhood of that set, as needed
for Cairns' ambient gluing, pp. 804--805. See M76 derivation 57.
-/


open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Relative smoothing may retain the whole germ near a closed
relative set, while preserving normalization and transversality
on a compact control set. See Cairns p. 804 and M76 derivation 57. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ParametricSmoothCore.lean
section

/-!
# Smooth core filling with full-slice parameters and preserved germs

Fill on a compact parameter neighborhood, extend to the ambient
slice, and smooth on a smaller compact parameter set while retaining
the old germ near a closed part of the exterior. See Cairns 1940,
pp. 804--805 and M76 derivation 57.
-/


open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A normalized field on a full slice can be filled smoothly in
the core coordinates, retaining the parameter coordinates and all
old germs near a prescribed closed exterior set. See Cairns p. 804
and M76 derivation 57. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/NormalizedFieldGerms.lean
section

/-!
# Extending local normalized field germs

Normalized Tietze extension on a closed neighborhood retains the
entire old germ near a prescribed closed set. This prepares the
local full-slice data for Cairns' recurrence, pp. 804--805; see
M76 derivation 58.
-/


open Set ContinuousLinearMap
open scoped Topology

variable {X E F : Type*} [TopologicalSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A normalized continuous field defined near a closed set has
a globally continuous normalized extension retaining its entire
germ near that set. See Cairns p. 804 and M76 derivation 58. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SmoothLocalInverse.lean
section

/-!
# A smooth inverse on an open neighborhood

Restrict the inverse-function chart to the open set where the
derivative is invertible. Its inverse is then smooth at every
point of its target, as needed for the affine-leaf neighborhoods
in Cairns 1940, pp. 804--805. See M76 derivation 52.
-/


open Set
open scoped Topology ContDiff

namespace ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An invertible derivative of a globally smooth map supplies a
local inverse smooth throughout its open target, including order
infinity. See Cairns pp. 804--805 and M76 derivation 52. -/
theorem exists_smooth_openPartialHomeomorph {f : E → F} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hn : n ≠ 0) {x : E} (A : E ≃L[ℝ] F)
    (hA : HasFDerivAt f (A : E →L[ℝ] F) x) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ x ∈ e.source ∧
      ContDiffOn ℝ n e.symm e.target := by
  let V := {y : E | (fderiv ℝ f y).IsInvertible}
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv hn)
  let e := (hf.contDiffAt.toOpenPartialHomeomorph f hA hn).restrOpen V hV
  refine ⟨e, rfl, ?_, ?_⟩
  · refine ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hA hn, ?_⟩
    change (fderiv ℝ f x).IsInvertible
    rw [hA.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  · intro y hy
    have hmem := e.map_target hy
    obtain ⟨B, hB⟩ := hmem.2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm (f₀' := B) hy
    · change HasFDerivAt f (B : E →L[ℝ] F) (e.symm y)
      rw [hB]
      exact (hf.differentiable hn).differentiableAt.hasFDerivAt
    · exact hf.contDiffAt

/-- An injective smooth map on an open set of invertible
derivatives has a smooth inverse on its entire image. This
assembles the local inverses into one core neighborhood.
See Cairns p. 805 and M76 derivation 54. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineLeafCoordinates.lean
section

/-!
# Local coordinates along a smooth family of affine leaves

A normalized projection field along an affine base parametrizes
its kernel leaves using one fixed kernel. At the zero section,
the derivative is the complementary direct-sum equivalence, so
the inverse function theorem gives unique smooth coordinates.
See Cairns 1940, pp. 804--805, and M76 derivation 52.
-/


open Set
open scoped ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Parametrize the affine kernel leaves using the kernel at one
fixed basepoint. Geometric interpretation requires normalization
on the affine frame. See Cairns pp. 804--805 and M76 derivation 52. -/
def affineLeafMap (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F) (x0 : F)
    (z : F × (Q x0).ker) : E :=
  a z.1 + (z.2 : E) - a.contLinear (Q z.1 z.2)

/-- The zero section of the affine-leaf map is its affine base.
See Cairns p. 805 and M76 derivation 52. -/
theorem affineLeafMap_zero (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 x : F) : a.affineLeafMap Q x0 (x, 0) = a x := by
  simp [affineLeafMap]

/-- The displacement of a leaf point lies in its assigned kernel.
See Cairns Hypothesis III, p. 804 and M76 derivation 52. -/
theorem affineLeafMap_sub_mem_ker (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (hQ : ∀ x, Function.RightInverse a.contLinear (Q x))
    (z : F × (Q x0).ker) : a.affineLeafMap Q x0 z - a z.1 ∈ (Q z.1).ker := by
  change Q z.1 (a z.1 + (z.2 : E) - a.contLinear (Q z.1 z.2) - a z.1) = 0
  rw [map_sub, map_sub, map_add, hQ]
  abel

/-- A smooth projection field gives a smooth affine-leaf map on
the fixed product space. See Cairns p. 805 and M76 derivation 52. -/
theorem contDiff_affineLeafMap (a : F →ᴬ[ℝ] E) {Q : F → E →L[ℝ] F}
    {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (x0 : F) :
    ContDiff ℝ n (a.affineLeafMap Q x0) := by
  have hz : ContDiff ℝ n (fun z : F × (Q x0).ker => (z.2 : E)) :=
    (Q x0).ker.subtypeL.contDiff.comp contDiff_snd
  exact ((a.contDiff.comp contDiff_fst).add hz).sub
    (a.contLinear.contDiff.comp ((hQ.comp contDiff_fst).clm_apply hz))

/-- At the zero section, variation of the projection field makes
no contribution to the derivative. See Cairns p. 805 and M76 derivation 52. -/
theorem hasFDerivAt_affineLeafMap_zero (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} {x0 : F} (hQ : DifferentiableAt ℝ Q x0) :
    HasFDerivAt (a.affineLeafMap Q x0)
      (a.contLinear.coprod (Q x0).ker.subtypeL) (x0, 0) := by
  let H := (Q x0).ker
  have hx : HasFDerivAt (fun z : F × H => a z.1)
      (a.contLinear.comp (ContinuousLinearMap.fst ℝ F H)) (x0, 0) :=
    a.hasFDerivAt.comp (x0, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hz : HasFDerivAt (fun z : F × H => (z.2 : E))
      (H.subtypeL.comp (ContinuousLinearMap.snd ℝ F H)) (x0, 0) :=
    H.subtypeL.hasFDerivAt.comp (x0, (0 : H))
      (ContinuousLinearMap.snd ℝ F H).hasFDerivAt
  have hq : HasFDerivAt (fun z : F × H => Q z.1)
      ((fderiv ℝ Q x0).comp (ContinuousLinearMap.fst ℝ F H)) (x0, 0) :=
    hQ.hasFDerivAt.comp (x0, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hd := (hx.add hz).sub (a.contLinear.hasFDerivAt.comp (x0, (0 : H))
    (hq.clm_apply hz))
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro z
  have hz0 : Q x0 (z.2 : E) = 0 := z.2.property
  simp [ContinuousLinearMap.coprod_apply, hz0]

variable [CompleteSpace E] [CompleteSpace F]

/-- A smooth normalized field on an affine base gives local
unique leaf coordinates with a smooth inverse throughout the
open target. See Cairns pp. 804--805 and M76 derivation 52. -/
theorem exists_smooth_affineLeaf_chart (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (hQ : ContDiff ℝ ∞ Q) (x0 : F)
    (hnorm : Function.RightInverse a.contLinear (Q x0)) :
    ∃ e : OpenPartialHomeomorph (F × (Q x0).ker) E,
      (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0 ∧
      (x0, 0) ∈ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let A := (ContinuousLinearEquiv.equivOfRightInverse (Q x0) a.contLinear hnorm).symm
  apply (a.contDiff_affineLeafMap hQ x0).exists_smooth_openPartialHomeomorph (by simp) A
  exact a.hasFDerivAt_affineLeafMap_zero (hQ.differentiable (by simp)).differentiableAt

end ContinuousAffineMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineLeafInverse.lean
section

/-!
# Exact inverse coordinates on affine leaves

The fixed-kernel projection recovers the normal coordinate. This
gives local constancy of the inverse base coordinate along each
affine leaf, with the neighborhood supplied by the chart's open
source. See Cairns 1940, pp. 804--805, and M76 derivation 52.
-/


open Set Filter
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed-kernel projection recovers the normal parameter of
every affine-leaf point. See Cairns p. 805 and M76 derivation 52. -/
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

/-- Every point of an assigned affine leaf is reconstructed from
its fixed-kernel coordinate. See Cairns p. 805 and M76 derivation 52. -/
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

/-- The inverse base coordinate is locally constant on each
assigned affine leaf throughout the target of an affine-leaf chart.
The neighborhood excludes remote intersections of the same planes.
See Cairns Hypotheses III--IV, p. 804 and M76 derivation 52. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineLeafInjectivity.lean
section

/-!
# Uniform injectivity of affine-leaf tubes

Fixed complementary coordinates reduce collisions of affine leaves
to a Lipschitz estimate in the base. This gives a uniform positive
normal radius over every compact convex core. See Cairns 1940,
pp. 804--805, and M76 derivation 54.
-/


open Set
open scoped ContDiff NNReal

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed kernel coordinate is independent of the affine
basepoint. See Cairns p. 805 and M76 derivation 54. -/
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

/-- The fixed tangential coordinate of an affine-leaf point has
an explicit shear formula. See Cairns p. 805 and M76 derivation 54. -/
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

/-- A Lipschitz field has no collisions between sufficiently
short affine-leaf parameters. Only normalization at the fixed
basepoint is needed for this estimate. See Cairns p. 805 and
M76 derivation 54. -/
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

/-- A Lipschitz bound supplies a uniform positive radius,
including when the field is constant. See Cairns p. 805 and
M76 derivation 54. -/
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

/-- A continuously differentiable field on a compact convex core
admits one uniform injective leaf tube. See Cairns p. 805 and
M76 derivation 54. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineLeafDifferential.lean
section

/-!
# Invertible leaf differentials along the entire zero section

Keep one reference kernel while moving the basepoint. The leaf
derivative is an explicit complementary shear, with inverse given
by the current projection and the fixed-kernel projection.
See Cairns 1940, p. 805, and M76 derivation 54.
-/


namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two projections normalized on one frame give a complementary
linear shear from the reference kernel to the current kernel.
See Cairns p. 805 and M76 derivation 54. -/
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

/-- With a fixed reference kernel, the derivative along the
whole zero section is the complementary shear at the current
basepoint. See Cairns p. 805 and M76 derivation 54. -/
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

/-- Normalization makes the derivative invertible at every point
of the zero section, even with a single fixed reference kernel.
See Cairns p. 805 and M76 derivation 54. -/
theorem isInvertible_fderiv_affineLeafMap_zeroSection (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (x0 x : F) (hQ : DifferentiableAt ℝ Q x)
    (h0 : Function.RightInverse a.contLinear (Q x0))
    (hx : Function.RightInverse a.contLinear (Q x)) :
    (fderiv ℝ (a.affineLeafMap Q x0) (x, 0)).IsInvertible := by
  rw [(a.hasFDerivAt_affineLeafMap_zeroSection x0 x hQ).fderiv]
  exact ⟨a.contLinear.affineLeafLinearEquiv (Q x0) (Q x) h0 hx, rfl⟩

end ContinuousAffineMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/CompactAffineLeafChart.lean
section

/-!
# A single smooth leaf chart around an entire compact core

Enlarge the compact base into a convex compact ball, use the
uniform injectivity estimate there, and restrict to the open set
of invertible derivatives. The resulting smooth inverse covers
the whole zero section over the core. See Cairns 1940, p. 805,
and M76 derivation 54.
-/


open Set
open scoped ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A smooth normalized affine-leaf field admits one smooth
inverse neighborhood covering an entire compact subset of its
base. See Cairns Hypothesis III, pp. 804--805 and M76 derivation 54. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/KernelLeafConstancy.lean
section

/-!
# Propagating local kernel-leaf constancy along segments

A continuous operator field locally constant along its own kernel
planes is constant along every such segment contained in a convex
domain. This supplies the uniqueness step in matching the ambient
fields of Cairns 1940, pp. 804--806; see M76 derivation 55.
-/


open Set Filter unitInterval
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local constancy on kernel leaves propagates along a segment
inside a convex domain. The field need only be continuous there.
See Cairns Hypotheses III--IV, pp. 804--805 and M76 derivation 55. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineLeafGerm.lean
section

/-!
# Uniqueness of ambient leaf germs from a full transverse slice

An ambient field locally constant along its kernel planes is
determined near a slice point by its restriction to the full
transverse slice. The segment joining a point to its slice base
stays in a small convex ball. See Cairns 1940, pp. 804--806 and
M76 derivation 55. A proper face alone does not supply this datum.
-/


open Set Filter
open scoped Topology

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Agreement on a full transverse affine slice determines the
ambient germ of a continuous field locally constant on its own
kernel leaves. See Cairns pp. 804--806 and M76 derivation 55. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/CompactLeafGluing.lean
section

/-!
# Compact leaf extensions matching an existing ambient field

Full-slice germ uniqueness upgrades a compact affine-leaf tube
to an extension preserving an existing ambient leaf field near
a designated part of the core. An open operator target can be
retained. See Cairns 1940, pp. 804--805 and M76 derivation 55.
-/


open Set Filter
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A normalized smooth full-slice field extends around a compact
core, retaining an open target and the old ambient leaf germs
wherever the slice germs agree. See Cairns pp. 804--805 and
M76 derivation 55. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ParametricLeafGluing.lean
section

/-!
# One smooth transverse leaf attachment across a compact face core

Extend the old full-slice germ, fill and smooth with the extra slice
coordinates retained as parameters, then use full-slice uniqueness
to match the old ambient field. See Cairns 1940, pp. 804--805 and
M76 derivation 59. The geometric finite recurrence is separate.
-/


open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Attach a smooth ambient transverse leaf field across a compact
core, preserving the old germs near its thickened boundary. The
full-slice parameter neighborhood and its old field are explicit.
See Cairns pp. 804--805 and M76 derivation 59. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/CompactParameterThickening.lean
section

/-!
# Uniform thickening of a compact slice set

An open neighborhood of the image of a compact zero section
contains a uniformly thick closed parameter neighborhood.
This chooses the full-slice parameters in Cairns' recurrence,
pp. 804--805; see M76 derivation 61.
-/


open Set
open scoped Topology

variable {X Y Z : Type*} [TopologicalSpace X] [NormedAddCommGroup Y] [TopologicalSpace Z]

/-- A compact zero section has a uniform positive closed-ball
parameter thickening inside any prescribed open image neighborhood.
See Cairns pp. 804--805 and M76 derivation 61. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/GeometricCoreAttachment.lean
section

/-!
# A geometric smooth leaf attachment from compact boundary data

The common-frame restriction, compact thickening and full-slice
attachment give a new geometric field near the core with the
old boundary germ and the same codimension. See Cairns 1940,
pp. 803--805 and M76 derivation 62.
-/


open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A smooth geometric leaf field near the boundary of an embedded
compact convex core extends across that core, retaining the boundary
germ, exact codimension and transversality to the prescribed set.
See Cairns pp. 804--805 and M76 derivation 62. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ConvexCoreDecomposition.lean
section

/-!
# Exact compact core and collar attachments

The inner convex core and its exterior collar cover the old body
and meet exactly along the new core frontier. A previously processed
carrier meeting only the original frontier remains disjoint from
the new core. See Cairns 1940, pp. 803--805 and M76 derivation 61.
-/


open Set

variable {X : Type*} [TopologicalSpace X]

/-- The exterior collar of a closed inner set meets it exactly
along its frontier. See Cairns pp. 803--805 and M76 derivation 61. -/
theorem IsClosed.collar_inter_eq_frontier {C D : Set X} (hD : IsClosed D) (hDC : D ⊆ C) :
    (C \ interior D) ∩ D = frontier D := by
  rw [frontier, hD.closure_eq]
  ext x
  constructor
  · exact fun hx => ⟨hx.2, hx.1.2⟩
  · exact fun hx => ⟨⟨hDC hx.1, hx.2⟩, hx.1⟩

/-- The collar and its inner set cover the original body.
See Cairns pp. 803--805 and M76 derivation 61. -/
theorem collar_union_inner_eq {C D : Set X} (hDC : D ⊆ C) :
    (C \ interior D) ∪ D = C := by
  ext x
  constructor
  · exact fun hx => hx.elim And.left (fun h => hDC h)
  · intro hx
    by_cases hxd : x ∈ D
    · exact Or.inr hxd
    · exact Or.inl ⟨hx, fun hxi => hxd (interior_subset hxi)⟩

/-- A carrier meeting a body only on its frontier is disjoint
from every core in the body's interior.
See Cairns pp. 803--805 and M76 derivation 61. -/
theorem disjoint_innerCore_of_inter_subset_frontier {A C D : Set X}
    (hAC : A ∩ C ⊆ frontier C) (hD : D ⊆ interior C) : Disjoint A D := by
  apply disjoint_left.mpr
  intro x hxA hxD
  exact (hAC ⟨hxA, interior_subset (hD hxD)⟩).2 (hD hxD)

variable [AddCommGroup X] [Module ℝ X] [T2Space X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- A compact convex body decomposes into an inner compact convex
core and a compact exterior collar inside any prescribed boundary
neighborhood, with exact common frontier and coverage.
See Cairns pp. 803--805 and M76 derivation 61. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ClosedGermNeighborhoods.lean
section

/-!
# Shrinking neighborhoods to a prescribed common germ

Two closed sets have open neighborhoods whose overlap lies in any
open neighborhood of their intersection, inside given original
domains. This prepares the pasting of Cairns' ambient fields,
pp. 804--805; see M76 derivation 60.
-/


open Set

variable {X : Type*} [TopologicalSpace X] [NormalSpace X]

/-- Shrink prescribed neighborhoods of two closed sets so that
their overlap lies in the designated common-germ domain.
See Cairns pp. 804--805 and M76 derivation 60. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SmoothLeafGermGluing.lean
section

/-!
# Gluing geometric smooth leaf germs near closed sets

Shrink the two open domains so their overlap lies in the equality
germ, then paste the geometric fields. Smoothness and local leaf
constancy are retained on the union without choosing a global
frame. See Cairns 1940, pp. 804--805 and M76 derivation 60.
-/


open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Smooth affine-leaf fields with equal germs near the intersection
of two closed sets glue near their union, preserving both original
germs. See Cairns pp. 804--805 and M76 derivation 60. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ConvexCellLeafAttachment.lean
section

/-!
# Attaching an embedded convex cell to a geometric smooth leaf field

Choose an inner core with old transverse collar, attach the core,
and glue the ambient fields while preserving both germs. This is
the geometric cell step of Cairns' recurrence, pp. 803--805; see
M76 derivation 63.
-/


open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- An embedded compact convex cell attaches to an old smooth
geometric leaf field, retaining the old carrier's germ and the
codimension, with prescribed transversality on the whole new cell.
The old carrier must meet the cell only on its frontier.
See Cairns pp. 803--805 and M76 derivation 63. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/TangentSecantSaturation.lean
section

/-!
# Secants of a star and its tangent saturation

A star containing a relative neighborhood of its central face has
the same secant directions after adding the face's tangent subspace.
Consequently its geometric transverse-plane condition is unchanged.
See Cairns 1940, pp. 799--800, and M76 derivation 34.
-/


open Set
open scoped Pointwise Topology

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A neighborhood of zero relative to a subspace contains a
positive multiple of every vector in that subspace.
See Cairns pp. 799--800 and M76 derivation 34. -/
theorem exists_pos_smul_mem_of_submodule_nhds (L : Submodule ℝ E) {C : Set E}
    (hC : L.subtype ⁻¹' C ∈ 𝓝 (0 : L)) {v : E} (hv : v ∈ L) :
    ∃ r : ℝ, 0 < r ∧ r • v ∈ C := by
  have hcont : Continuous (fun r : ℝ => r • (⟨v, hv⟩ : L)) :=
    continuous_id.smul continuous_const
  have hpre : {r : ℝ | r • (⟨v, hv⟩ : L) ∈ L.subtype ⁻¹' C} ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa only [zero_smul] using hC)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r / 2, half_pos hr, hb ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    using half_lt_self hr

/-- Every tangent-saturated secant has a positive rescaling that is
an actual secant of the bounded star.
See Cairns Section 3(B), p. 799, Section 4(C), p. 800, and M76 derivation 34. -/
theorem exists_pos_secant_of_mem_add_submodule (L : Submodule ℝ E) {C S : Set E}
    (hzero : (0 : E) ∈ C) (hstar : ∀ p ∈ C, StarConvex ℝ p S)
    (habsorb : ∀ l ∈ L, ∃ r : ℝ, 0 < r ∧ r • l ∈ C)
    {x y : E} (hx : x ∈ S + (L : Set E)) (hy : y ∈ S + (L : Set E)) :
    ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y) := by
  obtain ⟨x, hx, l, hl, rfl⟩ := hx
  obtain ⟨y, hy, m, hm, rfl⟩ := hy
  obtain ⟨t, ht, htc⟩ := habsorb (l - m) (L.sub_mem hl hm)
  have hden : 0 < 1 + t := by linarith
  let a : ℝ := 1 / (1 + t)
  let r : ℝ := t / (1 + t)
  have ha : 0 < a := div_pos one_pos hden
  have hr : 0 < r := div_pos ht hden
  have hsum : a + r = 1 := by
    dsimp only [a, r]
    rw [← add_div, div_self hden.ne']
  have har : a * t = r := by dsimp only [a, r]; ring
  refine ⟨r, hr, a • (t • (l - m)) + r • x,
    hstar _ htc hx ha.le hr.le hsum, a • (0 : E) + r • y,
    hstar _ hzero hy ha.le hr.le hsum, ?_⟩
  rw [smul_smul, har, smul_zero, zero_add]
  simp only [smul_add, smul_sub]
  abel

/-- Linear injectivity on the star is equivalent to injectivity on
its entire tangent saturation.
See Cairns pp. 799--800 and M76 derivation 34. -/
theorem injOn_add_submodule_iff (L : Submodule ℝ E) {C S : Set E}
    (hzero : (0 : E) ∈ C) (hstar : ∀ p ∈ C, StarConvex ℝ p S)
    (habsorb : ∀ l ∈ L, ∃ r : ℝ, 0 < r ∧ r • l ∈ C) (Q : E →L[ℝ] F) :
    InjOn Q (S + (L : Set E)) ↔ InjOn Q S := by
  constructor
  · intro h
    apply h.mono
    intro x hx
    exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  · intro h x hx y hy he
    obtain ⟨r, hr, u, hu, v, hv, huv⟩ :=
      exists_pos_secant_of_mem_add_submodule L hzero hstar habsorb hx hy
    have hQ : Q (u - v) = 0 := by rw [huv, map_smul, map_sub, he, sub_self, smul_zero]
    have hsame : u = v := h hu hv (sub_eq_zero.mp (by simpa only [map_sub] using hQ))
    have hscaled : r • (x - y) = 0 := by rw [← huv, hsame, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hscaled).resolve_left hr.ne')

end Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The geometric secant-angle condition is unchanged by tangent
saturation of a star. The same positive constant works on both sets.
See Cairns pp. 799--800 and M76 derivation 34. -/
theorem isSecantTransverse_add_submodule_iff (K L : Submodule ℝ E) {C S : Set E}
    (hzero : (0 : E) ∈ C) (hstar : ∀ p ∈ C, StarConvex ℝ p S)
    (habsorb : ∀ l ∈ L, ∃ r : ℝ, 0 < r ∧ r • l ∈ C) :
    K.IsSecantTransverse (S + (L : Set E)) ↔ K.IsSecantTransverse S := by
  constructor
  · intro h
    exact h.mono (fun x hx => ⟨x, hx, 0, L.zero_mem, add_zero x⟩)
  · rintro ⟨c, hc, hb⟩
    refine ⟨c, hc, fun x hx y hy => ?_⟩
    obtain ⟨r, hr, u, hu, v, hv, huv⟩ :=
      Set.exists_pos_secant_of_mem_add_submodule L hzero hstar habsorb hx hy
    have h := hb u hu v hv
    rw [huv, map_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg hr.le] at h
    have hscaled : r * (c * ‖x - y‖) ≤ r * ‖(x - y) - K.starProjection (x - y)‖ := by
      nlinarith only [h]
    exact (mul_le_mul_iff_right₀ hr).mp (by nlinarith only [hscaled])

end Submodule

end

-- Source: PoincareMT/Proofs/M76/Mathlib/FaceStarSaturation.lean
section

/-!
# Closed face stars and tangent saturation

The closed star of a face is star-convex at every point of that
face. If its translated central face contains a relative neighborhood
of zero, the full star and its tangent saturation have exactly the
same transverse planes. See Cairns 1940, pp. 799--800, and
M76 derivation 34.
-/


open Set
open scoped Pointwise Topology

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

/-- The closed star contains the faces which can be joined to the
entire specified central face.
See Cairns pp. 799--800 and M76 derivation 34. -/
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

/-- Closed face stars are subcomplexes of the original complex.
See Cairns p. 799 and M76 derivation 34. -/
theorem closedFaceStar_le (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    K.closedFaceStar s ≤ K := fun _ ht => ht.1

/-- Enlarging the central face shrinks its closed star.
See Cairns Section 4(B), p. 800 and M76 derivation 49. -/
theorem closedFaceStar_antitone (K : SimplicialComplex 𝕜 E) : Antitone K.closedFaceStar := by
  intro s t hst r hr
  refine ⟨hr.1, K.down_closed hr.2 (Finset.union_subset_union hst Finset.Subset.rfl) ?_⟩
  exact Finset.union_nonempty.mpr (Or.inr (K.nonempty_of_mem_faces hr.1))

/-- Taking the closed star of a face preserves finiteness.
See Cairns p. 799 and M76 derivation 34. -/
theorem finite_closedFaceStar_faces {K : SimplicialComplex 𝕜 E}
    (hK : K.faces.Finite) (s : Finset E) : (K.closedFaceStar s).faces.Finite :=
  hK.subset (K.closedFaceStar_le s)

end Algebraic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

/-- Every point of the central convex face is a star center of its
closed geometric star. See Cairns p. 799 and M76 derivation 34. -/
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

/-- For an actual closed face star with a relative central
neighborhood, tangent saturation preserves the geometric plane
condition. See Cairns pp. 799--800 and M76 derivation 34. -/
theorem isSecantTransverse_closedFaceStar_add_iff
    (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) (P L : Submodule ℝ E)
    (hzero : (0 : E) ∈ convexHull ℝ (s : Set E))
    (hface : L.subtype ⁻¹' convexHull ℝ (s : Set E) ∈ 𝓝 (0 : L)) :
    P.IsSecantTransverse ((K.closedFaceStar s).space + (L : Set E)) ↔
      P.IsSecantTransverse (K.closedFaceStar s).space :=
  P.isSecantTransverse_add_submodule_iff L hzero
    (fun _ hp => K.starConvex_closedFaceStar s hp)
    (fun _ hl => Set.exists_pos_smul_mem_of_submodule_nhds L hface hl)

end Submodule

end

-- Source: PoincareMT/Proofs/M76/Mathlib/VertexAbstractComplex.lean
section

/-!
# Abstract complexes on the actual vertex type

Restrict a geometric complex's labels to its vertices. This gives an
abstract complex with every singleton present and exactly the original
geometric faces. A straight star's link thereby defines an element of
the radial vertex-embedding space. See Cairns 1940, Section 5, pp. 801--802
and M76 derivation 18.
-/


open Set

namespace Geometry.SimplicialComplex

section General

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Restrict the abstract vertex type to the actual geometric vertices,
so that every singleton is a face. See Cairns p. 801 and M76 derivation 18. -/
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

/-- Forgetting subtype labels recovers exactly the original face
collection. See Cairns p. 801 and M76 derivation 18. -/
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

/-- Restricting to actual vertex labels preserves finiteness of the
face collection. See Cairns p. 801 and M76 derivation 18. -/
theorem finite_vertexAbstractComplex_faces {K : SimplicialComplex 𝕜 E}
    (hK : K.faces.Finite) : K.vertexAbstractComplex.faces.Finite :=
  Set.Finite.preimage (Finset.map_injective (Function.Embedding.subtype _)).injOn hK

end General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forgetting vertex labels is a radial embedding of an independent,
radially injective geometric complex. See Cairns p. 801 and M76 derivation 18. -/
theorem isRadialEmbedding_vertex_inclusion (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hinj : InjOn (NormedSpace.normalize : E → E) K.space) :
    K.vertexAbstractComplex.IsRadialEmbedding ((↑) : K.vertices → E) :=
  ⟨Subtype.val_injective, K, K.faces_eq_vertexAbstractComplex_images, hlin, hinj⟩

variable [DecidableEq E]

/-- The link of zero in a straight complex is an actual radial vertex
embedding, supplying the input to the normalization deformation.
See Cairns p. 802 and M76 derivation 18. -/
theorem isRadialEmbedding_link_vertex_inclusion (K : SimplicialComplex ℝ E) :
    (K.link 0).vertexAbstractComplex.IsRadialEmbedding ((↑) : (K.link 0).vertices → E) :=
  (K.link 0).isRadialEmbedding_vertex_inclusion
    (fun _ hs => linearIndependent_of_mem_link_zero hs) (injOn_normalize_link K)

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/FaceLinkProjection.lean
section

/-!
# Face links and affine projections of their closed stars

An affine map collapsing a nonempty central face sends its closed
star onto the union of the cones on the mapped link faces. The
empty link is included and gives the one-point cone. See Cairns
1940, Section 4, p. 800, and M76 derivation 37.
-/


open Set AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

/-- The link of a face contains its disjoint faces which can be
joined to the entire central face. See Cairns p. 800 and M76 derivation 37. -/
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

/-- A face link is a subcomplex of its closed face star.
See Cairns p. 800 and M76 derivation 37. -/
theorem faceLink_le_closedFaceStar (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    K.faceLink s ≤ K.closedFaceStar s := fun _ ht => ⟨ht.1, ht.2.2⟩

/-- The link of a face of a finite complex is finite.
See Cairns p. 800 and M76 derivation 37. -/
theorem finite_faceLink_faces {K : SimplicialComplex 𝕜 E}
    (hK : K.faces.Finite) (s : Finset E) : (K.faceLink s).faces.Finite :=
  hK.subset (fun _ ht => ht.1)

/-- A link vertex is an original vertex outside the central face.
See Cairns p. 800 and M76 derivation 37. -/
theorem faceLink_vertices_subset (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    (K.faceLink s).vertices ⊆ K.vertices \ (s : Set E) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxs
  exact Finset.disjoint_left.mp hx.2.1 hxs (Finset.mem_singleton_self x)

/-- Removing the central vertices from any closed-star face gives
either the empty face or a face of the link.
See Cairns p. 800 and M76 derivation 37. -/
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

/-- An affine collapse of a nonempty central face maps its actual
closed star onto the cones on the mapped link faces. The extra empty
face supplies the cone center. See Cairns p. 800 and M76 derivation 37. -/
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

/-- A radial realization of the projected actual link has a cone
carrier equal to the affine image of the original closed face star.
See Cairns p. 800 and M76 derivation 37. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineNormalIndependence.lean
section

/-!
# Independent normal vectors to an affine face

Collapsing the direction space of part of an affinely independent
family leaves independent normal vectors at the remaining vertices.
This applies to the actual orthogonal projection used by Cairns
1940, Section 4, p. 800. See M76 derivation 37.
-/


open Set

section Algebraic

variable {𝕜 ι E F : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- Projecting an affinely independent family along the direction
space of a nonempty subfamily leaves independent vectors at all
remaining labels. The center may be any point of the central affine
span. See Cairns pp. 799--800 and M76 derivation 37. -/
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

/-- Orthogonal projection normal to a central affine face preserves
independence of the remaining displacement vectors of a family in
general position. See Cairns p. 800 and M76 derivation 37. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/NormalFaceStar.lean
section

/-!
# The normal link of an actual geometric face star

The actual orthogonal normal projection of a closed face star in
general position is the cone on its independently realized face link.
See Cairns 1940, Section 4, p. 800, and M76 derivation 37.
-/


open Set AbstractSimplicialComplex

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Affine orthogonal projection to the normal space of a plane
through the specified center. See Cairns p. 800 and M76 derivation 37. -/
noncomputable def normalAffineProjection (L : Submodule ℝ E) (p : E) : E →ᵃ[ℝ] ↥(Lᗮ) :=
  Lᗮ.orthogonalProjectionOnto.toLinearMap.toAffineMap.comp
    (AffineEquiv.vaddConst ℝ p).symm.toAffineMap

/-- The normal affine projection acts on the displacement from its
center. See Cairns p. 800 and M76 derivation 37. -/
theorem normalAffineProjection_apply (L : Submodule ℝ E) (p x : E) :
    L.normalAffineProjection p x = Lᗮ.orthogonalProjectionOnto (x - p) := rfl

/-- Every point of the centered tangent plane has zero normal
projection. See Cairns p. 800 and M76 derivation 37. -/
theorem normalAffineProjection_eq_zero (L : Submodule ℝ E) (p : E) {x : E}
    (hx : x - p ∈ L) : L.normalAffineProjection p x = 0 :=
  L.orthogonalProjectionOnto_orthogonal_apply_eq_zero hx

end Submodule

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- In general position, the projected vertices of the actual face
link are linearly independent in the normal space.
See Cairns pp. 799--800 and M76 derivation 37. -/
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

/-- The normal projection of the actual link gives a faithful
independent radial realization on its actual vertex labels.
See Cairns p. 800 and M76 derivation 37. -/
noncomputable def faceNormalRadialEmbedding (K : SimplicialComplex ℝ E)
    (hv : AffineIndependent ℝ ((↑) : K.vertices → E))
    {s : Finset E} (hs : s ∈ K.faces) {p : E}
    (hp : p ∈ affineSpan ℝ (s : Set E)) :
    (K.faceLink s).vertexAbstractComplex.RadialEmbedding
      ↥((affineSpan ℝ (s : Set E)).directionᗮ) :=
  ⟨_, (K.faceLink s).vertexAbstractComplex.isRadialEmbedding_of_linearIndependent
    (K.linearIndependent_faceLink_normal hv hs hp)⟩

/-- The normal image of the original closed face star is exactly
the conical carrier of its actual normal link, including empty links.
See Cairns Section 4, p. 800, and M76 derivation 37. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/OrthogonalCylinderCoordinates.lean
section

/-!
# Orthogonal cylinder coordinates for tangent saturation

Centered normal and tangent coordinates map the tangent saturation
of any set exactly onto its normal image times the full tangent
space. See Cairns 1940, pp. 800--801, and M76 derivation 38.
-/


open Set
open scoped Pointwise

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Normal and tangent orthogonal projections give continuous
linear coordinates in the ambient space.
See Cairns p. 800 and M76 derivation 38. -/
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

/-- The normal coordinate is the actual orthogonal projection.
See Cairns p. 800 and M76 derivation 38. -/
theorem normalTangentEquiv_fst (L : Submodule ℝ E) (x : E) :
    (L.normalTangentEquiv x).1 = Lᗮ.orthogonalProjectionOnto x := rfl

/-- The tangent coordinate is the actual orthogonal projection.
See Cairns p. 800 and M76 derivation 38. -/
theorem normalTangentEquiv_snd (L : Submodule ℝ E) (x : E) :
    (L.normalTangentEquiv x).2 = L.orthogonalProjectionOnto x := rfl

/-- The inverse orthogonal coordinates add the included components.
See Cairns p. 800 and M76 derivation 38. -/
theorem normalTangentEquiv_symm_apply (L : Submodule ℝ E) (y : ↥(Lᗮ) × L) :
    L.normalTangentEquiv.symm y = (y.1 : E) + (y.2 : E) := rfl

/-- Center the normal and tangent coordinates at an actual point
of the central face. See Cairns p. 800 and M76 derivation 38. -/
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

/-- Centered orthogonal coordinates act on displacements from the
center. See Cairns p. 800 and M76 derivation 38. -/
theorem normalTangentCoordinates_apply (L : Submodule ℝ E) (p x : E) :
    L.normalTangentCoordinates p x = L.normalTangentEquiv (x - p) := rfl

/-- The centered normal coordinate equals the affine normal map.
See Cairns p. 800 and M76 derivation 38. -/
theorem normalTangentCoordinates_fst (L : Submodule ℝ E) (p x : E) :
    (L.normalTangentCoordinates p x).1 = L.normalAffineProjection p x := rfl

/-- The full tangent saturation becomes exactly the normal-image
cylinder in centered orthogonal coordinates, for every source set.
See Cairns p. 800 and M76 derivation 38. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ContractibleIntrinsicExtension.lean
section

/-!
# Extending maps from the intrinsic frontier of a convex core

Work in the direction space of the core's affine span. Intrinsic
frontier becomes ordinary frontier there, and the convex-body
extension applies without an ambient-interior assumption. See
Cairns 1940, Section 8, p. 804, and M76 derivation 43.
-/


open Set

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Y] [ContractibleSpace Y]

/-- A map from the entire intrinsic frontier of a nonempty
compact convex set into a contractible target extends over the set.
This includes lower-dimensional cores in a larger ambient space.
See Cairns p. 804 and M76 derivation 43. -/
theorem exists_intrinsicFrontier_extension_of_contractible {s : Set E}
    (hs : IsCompact s) (hc : Convex ℝ s) (hne : s.Nonempty)
    (f : C(intrinsicFrontier ℝ s, Y)) :
    ∃ g : C(s, Y), ∀ x : intrinsicFrontier ℝ s,
      g ⟨x, intrinsicFrontier_subset hs.isClosed x.property⟩ = f x := by
  obtain ⟨p, hp⟩ := hne
  let A := affineSpan ℝ s
  let pA : A := ⟨p, subset_affineSpan ℝ s hp⟩
  let : Nonempty A := ⟨pA⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ pA
  let a : A.direction →ᵃⁱ[ℝ] E := A.subtypeₐᵢ.comp e.toAffineIsometry
  let C : Set A.direction := a ⁻¹' s
  let B : Set A := Subtype.val ⁻¹' s
  have hrange : s ⊆ range a := by
    intro x hx
    refine ⟨e.symm ⟨x, subset_affineSpan ℝ s hx⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, subset_affineSpan ℝ s hx⟩)
  have hCcompact : IsCompact C := a.isometry.isEmbedding.isInducing.isCompact_preimage' hs hrange
  have hCconvex : Convex ℝ C := hc.affine_preimage a.toAffineMap
  have hCinterior : (interior C).Nonempty := by
    obtain ⟨_, q, hq, rfl⟩ := Set.Nonempty.intrinsicInterior hc ⟨p, hp⟩
    change (interior (e.toHomeomorph ⁻¹' B)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    refine ⟨e.symm q, ?_⟩
    change e (e.symm q) ∈ interior B
    rwa [e.apply_symm_apply]
  have hfrontier : a '' frontier C = intrinsicFrontier ℝ s := by
    change (Subtype.val ∘ e.toHomeomorph) '' frontier (e.toHomeomorph ⁻¹' B) =
      Subtype.val '' frontier B
    rw [← e.toHomeomorph.preimage_frontier]
    calc
      (Subtype.val ∘ e.toHomeomorph) '' (e.toHomeomorph ⁻¹' frontier B) =
          Subtype.val '' (e.toHomeomorph '' (e.toHomeomorph ⁻¹' frontier B)) := by
        rw [image_image]
        rfl
      _ = Subtype.val '' frontier B := by
        rw [e.toHomeomorph.surjective.image_preimage]
  let b : C ≃ₜ s := a.isometry.isEmbedding.homeomorphOfSubsetRange hrange
  let d : frontier C ≃ₜ intrinsicFrontier ℝ s :=
    (a.isometry.isEmbedding.homeomorphImage (frontier C)).trans (Homeomorph.setCongr hfrontier)
  obtain ⟨g, hg⟩ := exists_convexBody_extension_of_contractible hCcompact.isClosed hCconvex
    hCinterior hCcompact.isBounded (f.comp ⟨d, d.continuous⟩)
  refine ⟨g.comp ⟨b.symm, b.symm.continuous⟩, ?_⟩
  intro x
  let z := d.symm x
  have hdz : a z = (x : E) := congrArg Subtype.val (d.apply_symm_apply x)
  have hcomm : b.symm ⟨x, intrinsicFrontier_subset hs.isClosed x.property⟩ =
      ⟨z, hCcompact.isClosed.frontier_subset z.property⟩ := by
    apply b.injective
    rw [b.apply_symm_apply]
    exact Subtype.ext hdz.symm
  change g (b.symm ⟨x, intrinsicFrontier_subset hs.isClosed x.property⟩) = f x
  rw [hcomm, hg]
  exact congrArg f (d.apply_symm_apply x)

end ContinuousMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/IntrinsicConvexCoordinates.lean
section

/-!
# Intrinsic affine coordinates of a compact convex set

Translation from its affine-span direction space makes a nonempty
compact convex set into a full-dimensional convex body, with the
correct frontier. See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/


open Set

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation from the direction space parametrizes an affine
subspace isometrically. See Cairns pp. 803--805 and M76 derivation 64. -/
noncomputable def directionCoordinates (A : AffineSubspace ℝ E) (p : A) :
    A.direction →ᵃⁱ[ℝ] E := by
  let : Nonempty A := ⟨p⟩
  exact A.subtypeₐᵢ.comp (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry

/-- Intrinsic coordinates add the chosen origin to the included
direction. See Cairns pp. 803--805 and M76 derivation 64. -/
theorem directionCoordinates_apply (A : AffineSubspace ℝ E) (p : A) (x : A.direction) :
    A.directionCoordinates p x = (x : E) + (p : E) := rfl

/-- The intrinsic coordinate image is the entire affine subspace.
See Cairns pp. 803--805 and M76 derivation 64. -/
theorem range_directionCoordinates (A : AffineSubspace ℝ E) (p : A) :
    range (A.directionCoordinates p) = (A : Set E) := by
  let : Nonempty A := ⟨p⟩
  change range (Subtype.val ∘ (AffineIsometryEquiv.vaddConst ℝ p)) = _
  rw [range_comp, (AffineIsometryEquiv.vaddConst ℝ p).surjective.range_eq]
  simp

variable [FiniteDimensional ℝ E]

/-- A compact convex set is a full-dimensional convex body in its
intrinsic coordinates; the frontier image is its intrinsic frontier.
See Cairns pp. 803--805 and M76 derivation 64. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/NestedDirectionCoordinates.lean
section

/-!
# A full frame adapted to a smaller affine direction

Orthogonal decomposition inside a containing direction space supplies
the extra slice parameters while retaining intrinsic cell coordinates.
See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/


open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Split a containing direction space into a prescribed subspace
and its internal orthogonal complement. See Cairns pp. 803--805
and M76 derivation 64. -/
noncomputable def nestedDirectionCoordinates (L T : Submodule ℝ E) (hLT : L ≤ T) :
    (L × ↥((L.comap T.subtype)ᗮ)) ≃L[ℝ] T :=
  (((comapSubtypeEquivOfLe hLT).symm.toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ ↥((L.comap T.subtype)ᗮ))).trans
      (ContinuousLinearEquiv.prodComm ℝ _ _)).trans
        (L.comap T.subtype).normalTangentEquiv.symm

/-- With the extra coordinates zero, the full frame is exactly
the included smaller direction. See Cairns pp. 803--805 and
M76 derivation 64. -/
theorem nestedDirectionCoordinates_apply_zero (L T : Submodule ℝ E) (hLT : L ≤ T)
    (x : L) : ((L.nestedDirectionCoordinates T hLT (x, 0) : T) : E) = x := by
  change ((0 : T) + ((comapSubtypeEquivOfLe hLT).symm x : T) : E) = x
  change (0 : E) + (x : E) = x
  exact zero_add _

/-- A full linear slice translated to a cell basepoint is a
continuous affine map. See Cairns pp. 803--805 and M76 derivation 64. -/
noncomputable def affineSlice (T : Submodule ℝ E) (p : E) : T →ᴬ[ℝ] E :=
  ((AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.comp
    T.subtypeₗᵢ.toAffineIsometry).toContinuousAffineMap

omit [FiniteDimensional ℝ E] in
/-- The affine slice is translation of the included direction.
See Cairns pp. 803--805 and M76 derivation 64. -/
theorem affineSlice_apply (T : Submodule ℝ E) (p : E) (x : T) :
    T.affineSlice p x = (x : E) + p := rfl

omit [FiniteDimensional ℝ E] in
/-- The linear part of the full affine slice is the subtype map.
See Cairns pp. 803--805 and M76 derivation 64. -/
theorem affineSlice_contLinear (T : Submodule ℝ E) (p : E) :
    (T.affineSlice p).contLinear = T.subtypeL := by
  ext x
  rfl

/-- The zero-parameter full slice recovers the intrinsic affine
coordinates of the cell exactly. See Cairns pp. 803--805 and
M76 derivation 64. -/
theorem affineSlice_nestedDirectionCoordinates (A : AffineSubspace ℝ E)
    (T : Submodule ℝ E) (hAT : A.direction ≤ T) (p : A) (x : A.direction) :
    T.affineSlice p (A.direction.nestedDirectionCoordinates T hAT (x, 0)) =
      A.directionCoordinates p x := by
  rw [affineSlice_apply, nestedDirectionCoordinates_apply_zero,
    AffineSubspace.directionCoordinates_apply]

end Submodule

end

-- Source: PoincareMT/Proofs/M76/Mathlib/IntrinsicCellLeafAttachment.lean
section

/-!
# Attaching a convex cell in its intrinsic affine span

A containing direction space supplies the full transverse frame.
Intrinsic coordinates provide all cell and frontier hypotheses of
the checked attachment. See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/


open Set Filter
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A nonempty compact convex cell attaches using its intrinsic
frontier and any containing full transverse direction. The old
ambient germ and codimension are retained. See Cairns pp. 803--805
and M76 derivation 64. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/NormalizedTransverseTarget.lean
section

/-!
# Contractibility of normalized transverse operator targets

The geometric transverse-complement plane coordinates identify the
normalized operator target with its actual subspace topology. A
coface frame can then transfer contractibility of the full plane
space. See Cairns 1940, pp. 801, 804, and M76 derivation 48.
-/


open Set Geometry

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Transverse planes complementary to a fixed frame correspond
to exactly the normalized operators with transverse kernels.
See Cairns p. 801 and M76 derivation 48. -/
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

/-- When all transverse planes miss the chosen frame, geometric
plane-space contractibility gives contractibility of the actual
normalized operator target. See Cairns pp. 801, 804 and M76 derivation 48. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/FaceLinkDimension.lean
section

/-!
# Face dimensions and low-dimensional links

Disjoint-coface incidence bounds the size of link faces. Maximal-size
faces have empty links, and zero-dimensional links with two vertices
are exactly two singleton faces. See Cairns 1940, p. 807, and M76
derivation 42.
-/


open Set

namespace Geometry.SimplicialComplex

section Combinatorial

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

/-- A central face and a link face have disjoint vertices, so
their combined size obeys the original face-size bound.
See Cairns pp. 800, 807 and M76 derivation 42. -/
theorem card_add_card_le_of_mem_faceLink (K : SimplicialComplex 𝕜 E)
    {m : ℕ} (hbound : ∀ t ∈ K.faces, t.card ≤ m) (s : Finset E)
    {t : Finset E} (ht : t ∈ (K.faceLink s).faces) : s.card + t.card ≤ m := by
  have h := hbound (s ∪ t) ht.2.2
  rwa [Finset.card_union_of_disjoint ht.2.1] at h

/-- A face attaining the global face-size bound has empty link.
See Cairns p. 807 and M76 derivation 42. -/
theorem faceLink_faces_eq_empty_of_card_eq (K : SimplicialComplex 𝕜 E)
    {m : ℕ} (hbound : ∀ t ∈ K.faces, t.card ≤ m) {s : Finset E} (hs : s.card = m) :
    (K.faceLink s).faces = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have h := K.card_add_card_le_of_mem_faceLink hbound s ht
  have htpos := Finset.card_pos.mpr ((K.faceLink s).nonempty_of_mem_faces ht)
  omega

omit [DecidableEq E] in
/-- A complex with singleton faces and exactly two vertices
consists of exactly those two distinct singleton faces.
See Cairns p. 807 and M76 derivation 42. -/
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

/-- The actual direction space of an independent face has one
less dimension than its number of vertices.
See Cairns pp. 800, 807 and M76 derivation 42. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/IntrinsicFaceSaturation.lean
section

/-!
# Intrinsic face centers supply tangent saturation

An intrinsic-interior point of a central convex face absorbs every
tangent direction. The rescaled secant calculation therefore applies
to actual closed face stars without a separate neighborhood premise.
See Cairns 1940, pp. 799--800, and M76 derivation 35.
-/


open Set
open scoped Pointwise Topology

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An intrinsic-interior center can move a positive amount in any
direction of its affine span while staying in the set.
See Cairns pp. 799--800 and M76 derivation 35. -/
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

/-- A star at every point of a central set absorbs tangent-saturated
secants whenever that central set has an intrinsic-interior point.
See Cairns pp. 799--800 and M76 derivation 35. -/
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

/-- A secant-angle bound transfers whenever every target secant can
be positively rescaled into a source secant.
See Cairns p. 799 and M76 derivation 35. -/
theorem IsSecantTransverse.of_secant_rescaling {K : Submodule ℝ E} {S T : Set E}
    (hK : K.IsSecantTransverse S)
    (hscale : ∀ x ∈ T, ∀ y ∈ T,
      ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y)) :
    K.IsSecantTransverse T := by
  obtain ⟨c, hc, hb⟩ := hK
  refine ⟨c, hc, fun x hx y hy => ?_⟩
  obtain ⟨r, hr, u, hu, v, hv, huv⟩ := hscale x hx y hy
  have h := hb u hu v hv
  rw [huv, map_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg hr.le] at h
  exact (mul_le_mul_iff_right₀ hr).mp (by nlinarith only [h])

/-- Intrinsic interior of the central set suffices for geometric
transversality to be invariant under its full tangent saturation.
See Cairns pp. 799--800 and M76 derivation 35. -/
theorem isSecantTransverse_add_direction_iff (K : Submodule ℝ E) {C S : Set E} {p : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hstar : ∀ q ∈ C, StarConvex ℝ q S) :
    K.IsSecantTransverse (S + ((affineSpan ℝ C).direction : Set E)) ↔
      K.IsSecantTransverse S := by
  constructor
  · intro h
    exact h.mono (fun x hx => ⟨x, hx, 0, (affineSpan ℝ C).direction.zero_mem, add_zero x⟩)
  · intro h
    exact h.of_secant_rescaling (fun _ hx _ hy =>
      Set.exists_pos_secant_of_mem_add_direction hp hstar hx hy)

/-- For every actual nonempty geometric face, the closed star and
its saturation by the face directions have the same transverse planes.
No relative-neighborhood assumption remains.
See Cairns pp. 799--800 and M76 derivation 35. -/
theorem isSecantTransverse_closedFaceStar_tangent_iff [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (P : Submodule ℝ E) :
    P.IsSecantTransverse ((K.closedFaceStar s).space +
      ((affineSpan ℝ (s : Set E)).direction : Set E)) ↔
      P.IsSecantTransverse (K.closedFaceStar s).space := by
  have hne : (convexHull ℝ (s : Set E)).Nonempty :=
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
  obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _) hne
  simpa only [affineSpan_convexHull] using P.isSecantTransverse_add_direction_iff hp
    (fun _ hq => K.starConvex_closedFaceStar s hq)

end Submodule

end

-- Source: PoincareMT/Proofs/M76/Mathlib/ConvexFaceTransversality.lean
section

/-!
# Transverse planes miss convex face directions

Intrinsic interior allows every direction of a nonempty convex
face to be rescaled to a face secant. Consequently geometric
transversality implies disjointness from the full affine direction
space. See Cairns 1940, pp. 799--801, and M76 derivation 38.
-/


open Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A plane transverse to a set misses the full affine direction
space of every nonempty convex subset, even when the subset has
empty ambient interior. See Cairns pp. 799--801 and M76 derivation 38. -/
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

/-- Every geometric transverse plane misses the direction space
of each actual face of a simplicial complex.
See Cairns pp. 799--801 and M76 derivation 38. -/
theorem disjoint_faceDirection_of_isSecantTransverse (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {P : Submodule ℝ E}
    (hP : P.IsSecantTransverse K.space) :
    Disjoint (affineSpan ℝ (s : Set E)).direction P := by
  have hne := (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull (𝕜 := ℝ)
  simpa only [affineSpan_convexHull] using hP.disjoint_affineDirection
    (convex_convexHull ℝ _) hne (convexHull_subset_space hs)

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplicialFaceLeafAttachment.lean
section

/-!
# Smooth leaf attachment of an actual simplicial face

A containing full-dimensional coface supplies the transverse frame.
The geometric plane target supplies normalized contractibility.
See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/


open Set Filter Geometry
open scoped Topology

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Attach an actual face using a full coface and the contractible
space of its transverse planes. The old carrier's ambient germ
persists. See Cairns pp. 803--805 and M76 derivation 64. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AffineIntrinsicFrontier.lean
section

/-!
# Intrinsic frontiers under affine embeddings of the span

An affine map injective on the affine span preserves the intrinsic
frontier in finite dimension. Global injectivity is unnecessary for
barycentric synthesis. See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/


open Set

namespace AffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Injectivity on the affine span suffices to transport an
intrinsic frontier through an affine map. See Cairns pp. 803--805
and M76 derivation 64. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/StdSimplexCore.lean
section

/-!
# Closed barycentric cores

The closed core of a simplex has all barycentric coordinates at
least the fixed threshold. It is compact, convex and nonempty below
the reciprocal vertex-count bound, so maps from its intrinsic
frontier into contractible targets extend across it. See Cairns
1940, Section 7(A), pp. 802--803, Section 8, p. 804, and M76
derivation 44.
-/


open Set

variable (ι : Type*) [Fintype ι]

/-- The closed core, including its boundary, of the standard
simplex. See Cairns pp. 802--803 and M76 derivation 44. -/
def stdSimplexCore (η : ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, η ≤ q i) ∧ ∑ i, q i = 1}

/-- All defining conditions of a barycentric core are closed.
See Cairns pp. 802--803 and M76 derivation 44. -/
theorem isClosed_stdSimplexCore (η : ℝ) : IsClosed (stdSimplexCore ι η) := by
  have he : stdSimplexCore ι η =
      (⋂ i, {q : ι → ℝ | η ≤ q i}) ∩ {q | ∑ i, q i = 1} := by
    ext q
    simp [stdSimplexCore]
  rw [he]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)

/-- A barycentric core is convex, including at degenerate
thresholds. See Cairns pp. 802--803 and M76 derivation 44. -/
theorem convex_stdSimplexCore (η : ℝ) : Convex ℝ (stdSimplexCore ι η) := by
  intro q hq r hr a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · change η ≤ a * q i + b * r i
    calc
      η = a * η + b * η := by rw [← add_mul, hab, one_mul]
      _ ≤ a * q i + b * r i := add_le_add
        (mul_le_mul_of_nonneg_left (hq.1 i) ha) (mul_le_mul_of_nonneg_left (hr.1 i) hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hq.2, hr.2, mul_one, hab]

/-- At a nonnegative threshold the closed core is a subset of
the original simplex. See Cairns pp. 802--803 and M76 derivation 44. -/
theorem stdSimplexCore_subset_stdSimplex {η : ℝ} (hη : 0 ≤ η) :
    stdSimplexCore ι η ⊆ stdSimplex ℝ ι :=
  fun _ hq => ⟨fun i => hη.trans (hq.1 i), hq.2⟩

/-- A closed core is compact as a closed subset of its simplex.
See Cairns pp. 802--803 and M76 derivation 44. -/
theorem isCompact_stdSimplexCore {η : ℝ} (hη : 0 ≤ η) :
    IsCompact (stdSimplexCore ι η) :=
  (isCompact_stdSimplex ℝ ι).of_isClosed_subset (isClosed_stdSimplexCore ι η)
    (stdSimplexCore_subset_stdSimplex ι hη)

variable [Nonempty ι]

/-- The barycenter belongs to the closed core below the reciprocal
vertex-count threshold. See Cairns pp. 802--803 and M76 derivation 44. -/
theorem nonempty_stdSimplexCore {η : ℝ} (hη : (Fintype.card ι : ℝ) * η < 1) :
    (stdSimplexCore ι η).Nonempty := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨fun _ => (Fintype.card ι : ℝ)⁻¹, fun i => ?_, ?_⟩
  · rw [inv_eq_one_div, le_div_iff₀ hn]
    nlinarith [hη]
  · simp

namespace ContinuousMap

variable {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]

/-- Exact extension from the whole boundary of a closed simplex
core into any contractible target. The frontier is intrinsic to
the affine hyperplane of barycentric coordinates.
See Cairns p. 804 and M76 derivations 43--44. -/
theorem exists_stdSimplexCore_extension {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1)
    (f : C(intrinsicFrontier ℝ (stdSimplexCore ι η), Y)) :
    ∃ g : C(stdSimplexCore ι η, Y),
      ∀ x : intrinsicFrontier ℝ (stdSimplexCore ι η),
        g ⟨x, intrinsicFrontier_subset (isClosed_stdSimplexCore ι η) x.property⟩ = f x :=
  exists_intrinsicFrontier_extension_of_contractible (isCompact_stdSimplexCore ι hη)
    (convex_stdSimplexCore ι η) (nonempty_stdSimplexCore ι hbound) f

end ContinuousMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplexCoreBox.lean
section

/-!
# Barycentric boxes around simplex cores

For a partition of the simplex's vertices into a face and its
complement, the core neighborhood has large face coordinates and
small complementary coordinates. The positive radial factor gives
explicit coordinates by a core point and a complementary cube.
See Cairns 1940, Section 7(A), pp. 802--803, and M76 derivation 44.
-/


open Set

namespace StdSimplexCore

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

/-- The closed box neighborhood of a face core, in barycentric
coordinates partitioned into face and complementary vertices.
See Cairns (7.1)--(7.3), pp. 802--803 and M76 derivation 44. -/
def boxRegion (η : ℝ) : Set ((ι → ℝ) × (κ → ℝ)) :=
  {z | (∀ i, η ≤ z.1 i) ∧ z.2 ∈ Icc 0 (fun _ => η) ∧
    (∑ i, z.1 i) + ∑ j, z.2 j = 1}

variable {κ}

/-- The radial factor of the face coordinates after the outside
barycentric mass is assigned. See Cairns p. 803 and M76 derivation 44. -/
noncomputable def boxScale (η : ℝ) (v : κ → ℝ) : ℝ :=
  1 - (∑ j, v j) / (1 - (Fintype.card ι : ℝ) * η)

variable {ι}

/-- The full vertex-count bound keeps the face denominator
positive. See Cairns p. 803 and M76 derivation 44. -/
theorem boxDenominator_pos {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1) :
    0 < 1 - (Fintype.card ι : ℝ) * η := by
  have hκ : 0 ≤ (Fintype.card κ : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη
  nlinarith [hbound]

/-- The radial factor stays strictly positive on the entire
closed complementary cube. See Cairns p. 803 and M76 derivation 44. -/
theorem boxScale_pos {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    {v : κ → ℝ} (hv : v ∈ Icc 0 (fun _ => η)) : 0 < boxScale ι η v := by
  have hden := boxDenominator_pos hη hbound
  have hsum : (∑ j, v j) ≤ (Fintype.card κ : ℝ) * η := by
    calc
      (∑ j, v j) ≤ ∑ _j : κ, η := Finset.sum_le_sum (fun j _ => hv.2 j)
      _ = (Fintype.card κ : ℝ) * η := by simp
  rw [boxScale, sub_pos, div_lt_one hden]
  nlinarith [hbound, hsum]

/-- The radial factor accounts exactly for the complementary
barycentric mass. See Cairns p. 803 and M76 derivation 44. -/
theorem boxScale_mul {η : ℝ} (hden : 1 - (Fintype.card ι : ℝ) * η ≠ 0)
    (v : κ → ℝ) :
    boxScale ι η v * (1 - (Fintype.card ι : ℝ) * η) =
      1 - (Fintype.card ι : ℝ) * η - ∑ j, v j := by
  rw [boxScale, sub_mul, one_mul, div_mul_cancel₀ _ hden]

/-- The radial factor depends continuously on the outside
coordinates, with a fixed threshold. See Cairns p. 803 and M76 derivation 44. -/
theorem continuous_boxScale (ι : Type*) [Fintype ι] (η : ℝ) :
    Continuous (boxScale ι η : (κ → ℝ) → ℝ) := by
  unfold boxScale
  fun_prop

variable (ι κ)

/-- The point on the box over a core point with prescribed
outside coordinates. See Cairns p. 803 and M76 derivation 44. -/
noncomputable def boxPoint (η : ℝ) (q : ι → ℝ) (v : κ → ℝ) :
    (ι → ℝ) × (κ → ℝ) :=
  (fun i => η + boxScale ι η v * (q i - η), v)

/-- The core point under a box-neighborhood point. Its geometric
use is restricted to the positive-factor region.
See Cairns p. 803 and M76 derivation 44. -/
noncomputable def boxBase (η : ℝ) (z : (ι → ℝ) × (κ → ℝ)) : ι → ℝ :=
  fun i => η + (z.1 i - η) / boxScale ι η z.2

variable {ι κ}

/-- A core point and complementary cube coordinate give a point
of the closed core neighborhood. See Cairns p. 803 and M76 derivation 44. -/
theorem boxPoint_mem {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    {q : ι → ℝ} (hq : q ∈ stdSimplexCore ι η)
    {v : κ → ℝ} (hv : v ∈ Icc 0 (fun _ => η)) :
    boxPoint ι κ η q v ∈ boxRegion ι κ η := by
  have ha := boxScale_pos hη hbound hv
  refine ⟨fun i => ?_, hv, ?_⟩
  · change η ≤ η + boxScale ι η v * (q i - η)
    exact le_add_of_nonneg_right (mul_nonneg ha.le (sub_nonneg.mpr (hq.1 i)))
  · change (∑ i, (η + boxScale ι η v * (q i - η))) + ∑ j, v j = 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hq.2]
    rw [boxScale_mul (boxDenominator_pos hη hbound).ne']
    ring

/-- The inverse formula stays in the core, with barycentric sum
exactly one. See Cairns p. 803 and M76 derivation 44. -/
theorem boxBase_mem {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    {z : (ι → ℝ) × (κ → ℝ)} (hz : z ∈ boxRegion ι κ η) :
    boxBase ι κ η z ∈ stdSimplexCore ι η := by
  have ha := boxScale_pos hη hbound hz.2.1
  have hsum : (∑ i, z.1 i) - (Fintype.card ι : ℝ) * η =
      boxScale ι η z.2 * (1 - (Fintype.card ι : ℝ) * η) := by
    rw [boxScale_mul (boxDenominator_pos hη hbound).ne']
    linarith [hz.2.2]
  refine ⟨fun i => ?_, ?_⟩
  · change η ≤ η + (z.1 i - η) / boxScale ι η z.2
    exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (hz.1 i)) ha.le)
  · change (∑ i, (η + (z.1 i - η) / boxScale ι η z.2)) = 1
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hsum, mul_div_cancel_left₀ _ ha.ne']
    ring

/-- Recover the core point from its box coordinates wherever
the radial factor is nonzero. See Cairns p. 803 and M76 derivation 44. -/
theorem boxBase_boxPoint (η : ℝ) (q : ι → ℝ) (v : κ → ℝ)
    (ha : boxScale ι η v ≠ 0) :
    boxBase ι κ η (boxPoint ι κ η q v) = q := by
  funext i
  simp only [boxBase, boxPoint, add_sub_cancel_left]
  rw [mul_div_cancel_left₀ _ ha]
  ring

/-- Recover a box point from its core base and outside
coordinates. See Cairns p. 803 and M76 derivation 44. -/
theorem boxPoint_boxBase (η : ℝ) (z : (ι → ℝ) × (κ → ℝ))
    (ha : boxScale ι η z.2 ≠ 0) :
    boxPoint ι κ η (boxBase ι κ η z) z.2 = z := by
  apply Prod.ext
  · funext i
    simp only [boxPoint, boxBase, add_sub_cancel_left]
    rw [mul_div_cancel₀ _ ha]
    ring
  · rfl

end StdSimplexCore

end

-- Source: PoincareMT/Proofs/M76/Mathlib/CoreProjectionAlgebra.lean
section

/-!
# Nested barycentric core projections

Core projections are rational barycentric formulas. Their residual
masses transform by a scalar, so projections onto nested faces
compose exactly wherever the required denominators are nonzero.
See Cairns 1940, Section 7(B), p. 803, Section 8, pp. 804--805,
and M76 derivation 45.
-/


namespace StdSimplexCore

variable {ι : Type*} [DecidableEq ι]

/-- The barycentric mass above the threshold on a finite face.
See Cairns pp. 803--804 and M76 derivation 45. -/
noncomputable def residualMass (s : Finset ι) (η : ℝ) (q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (q i - η)

/-- The totalized core projection formula. Its geometric use
requires positive residual mass and a positive core-size factor.
See Cairns pp. 803--804 and M76 derivation 45. -/
noncomputable def projectToFace (s : Finset ι) (η : ℝ) (q : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ s then
    η + (q i - η) * (1 - (s.card : ℝ) * η) / residualMass s η q else 0

/-- A core projection has barycentric sum one on its face
whenever the residual mass is nonzero.
See Cairns p. 803 and M76 derivation 45. -/
theorem sum_projectToFace (s : Finset ι) (η : ℝ) (q : ι → ℝ)
    (hm : residualMass s η q ≠ 0) : ∑ i ∈ s, projectToFace s η q i = 1 := by
  have he : (∑ i ∈ s, projectToFace s η q i) =
      ∑ i ∈ s, (η + (q i - η) * (1 - (s.card : ℝ) * η) / residualMass s η q) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [projectToFace, if_pos hi]
  rw [he, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  change (∑ _i ∈ s, η) + residualMass s η q * (1 - (s.card : ℝ) * η) /
    residualMass s η q = 1
  rw [mul_div_cancel_left₀ _ hm]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Already normalized coordinates supported on a face are
fixed by its core projection.
See Cairns p. 803 and M76 derivation 45. -/
theorem projectToFace_eq_self (s : Finset ι) (η : ℝ) (q : ι → ℝ)
    (hsum : ∑ i ∈ s, q i = 1) (hsupport : ∀ i ∉ s, q i = 0)
    (hden : 1 - (s.card : ℝ) * η ≠ 0) : projectToFace s η q = q := by
  have hm : residualMass s η q = 1 - (s.card : ℝ) * η := by
    simp only [residualMass, Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul]
  funext i
  by_cases hi : i ∈ s
  · simp only [projectToFace, if_pos hi, hm, mul_div_cancel_right₀ _ hden]
    ring
  · simp only [projectToFace, if_neg hi, hsupport i hi]

/-- A nested face's residual mass transforms by the outer
projection's scalar factor. This identity needs no cancellation
hypotheses. See Cairns pp. 803--805 and M76 derivation 45. -/
theorem residualMass_projectToFace {r s : Finset ι} (hrs : r ⊆ s)
    (η : ℝ) (q : ι → ℝ) :
    residualMass r η (projectToFace s η q) =
      residualMass r η q * (1 - (s.card : ℝ) * η) / residualMass s η q := by
  unfold residualMass
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [projectToFace, if_pos (hrs hi), add_sub_cancel_left, residualMass]

/-- Nested core projections compose exactly wherever all
denominators used in cancellation are nonzero.
See Cairns pp. 803--805 and M76 derivation 45. -/
theorem projectToFace_projectToFace {r s : Finset ι} (hrs : r ⊆ s)
    (η : ℝ) (q : ι → ℝ) (hden : 1 - (s.card : ℝ) * η ≠ 0)
    (hr : residualMass r η q ≠ 0) (hs : residualMass s η q ≠ 0) :
    projectToFace r η (projectToFace s η q) = projectToFace r η q := by
  funext i
  by_cases hi : i ∈ r
  · simp only [projectToFace, if_pos hi, if_pos (hrs hi), add_sub_cancel_left]
    rw [residualMass_projectToFace hrs]
    have hden' : 1 - η * (s.card : ℝ) ≠ 0 := by simpa only [mul_comm] using hden
    field_simp [hden', hr, hs]
  · simp only [projectToFace, if_neg hi]

end StdSimplexCore

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplexCoreBoxCoordinates.lean
section

/-!
# Product coordinates for closed core neighborhoods

The barycentric box maps are inverse homeomorphisms. Their formulas
are smooth on a neighborhood of the closed box region, so pulling
back a core field gives the required constancy along boxes. See
Cairns 1940, Section 7(A), p. 803, Section 8, p. 804, and M76
derivation 44.
-/


open Set
open scoped ContDiff

namespace StdSimplexCore

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The radial factor is smooth as a function of the outside
coordinates. See Cairns pp. 803--804 and M76 derivation 44. -/
theorem contDiff_boxScale (ι : Type*) [Fintype ι] (η : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (boxScale ι η : (κ → ℝ) → ℝ) := by
  unfold boxScale
  fun_prop

/-- The box-point formula is smooth on the entire coordinate
vector space. See Cairns pp. 803--804 and M76 derivation 44. -/
theorem contDiff_boxPoint (ι κ : Type*) [Fintype ι] [Fintype κ] (η : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun z : (ι → ℝ) × (κ → ℝ) => boxPoint ι κ η z.1 z.2) := by
  unfold boxPoint
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    exact contDiff_const.add (((contDiff_boxScale ι η n).comp contDiff_snd).mul
      (((contDiff_apply ℝ ℝ i).comp contDiff_fst).sub contDiff_const))
  · exact contDiff_snd

/-- The core-base formula is smooth wherever its radial factor
is nonzero. See Cairns pp. 803--804 and M76 derivation 44. -/
theorem contDiffAt_boxBase (η : ℝ) (n : ℕ∞ω) (z : (ι → ℝ) × (κ → ℝ))
    (hz : boxScale ι η z.2 ≠ 0) : ContDiffAt ℝ n (boxBase ι κ η) z := by
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_const.add
    ((((contDiff_apply ℝ ℝ i).comp contDiff_fst).contDiffAt.sub contDiffAt_const).div
      ((contDiff_boxScale ι η n).comp contDiff_snd).contDiffAt hz)

/-- Each closed core neighborhood is the product of its core
with the complementary closed cube, including all common faces.
See Cairns p. 803 and M76 derivation 44. -/
noncomputable def boxHomeomorph {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1) :
    (stdSimplexCore ι η × Icc (0 : κ → ℝ) (fun _ => η)) ≃ₜ boxRegion ι κ η where
  toFun z := ⟨boxPoint ι κ η z.1 z.2, boxPoint_mem hη hbound z.1.property z.2.property⟩
  invFun z := (⟨boxBase ι κ η z, boxBase_mem hη hbound z.property⟩,
    ⟨z.val.2, z.property.2.1⟩)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change boxBase ι κ η (boxPoint ι κ η z.1.val z.2.val) = z.1.val
      exact boxBase_boxPoint η z.1.val z.2.val
        (boxScale_pos (ι := ι) hη hbound z.2.property).ne'
    · rfl
  right_inv z := by
    apply Subtype.ext
    change boxPoint ι κ η (boxBase ι κ η z.val) z.val.2 = z.val
    exact boxPoint_boxBase η z.val (boxScale_pos (ι := ι) hη hbound z.property.2.1).ne'
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (contDiff_boxPoint ι κ η 0).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      rw [continuous_iff_continuousAt]
      intro z
      exact (contDiffAt_boxBase η 0 z.val
        (boxScale_pos (ι := ι) hη hbound z.property.2.1).ne').continuousAt.comp
          continuous_subtype_val.continuousAt
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _

/-- Extending a core map constantly over each box is continuous.
The target has only its given topology.
See Cairns (8.1), p. 804 and M76 derivation 44. -/
noncomputable def boxExtension {Y : Type*} [TopologicalSpace Y] {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    (f : C(stdSimplexCore ι η, Y)) : C(boxRegion ι κ η, Y) :=
  f.comp ⟨fun z => ((boxHomeomorph hη hbound).symm z).1,
    continuous_fst.comp (boxHomeomorph hη hbound).symm.continuous⟩

/-- The extended field has exactly its core value at every point
of the corresponding box. See Cairns (8.1), p. 804 and M76 derivation 44. -/
theorem boxExtension_boxPoint {Y : Type*} [TopologicalSpace Y] {η : ℝ} (hη : 0 ≤ η)
    (hbound : ((Fintype.card ι : ℝ) + Fintype.card κ) * η < 1)
    (f : C(stdSimplexCore ι η, Y)) (q : stdSimplexCore ι η)
    (v : Icc (0 : κ → ℝ) (fun _ => η)) :
    boxExtension hη hbound f ((boxHomeomorph hη hbound) (q, v)) = f q := by
  change f (((boxHomeomorph hη hbound).symm ((boxHomeomorph hη hbound) (q, v))).1) = f q
  rw [Homeomorph.symm_apply_apply]

end StdSimplexCore

end

-- Source: PoincareMT/Proofs/M76/Mathlib/StdSimplexCoreBoundary.lean
section

/-!
# The intrinsic boundary of a barycentric core

Strict barycentric inequalities characterize the intrinsic interior.
The boundary consists exactly of the core points where some
coordinate reaches the threshold. This includes the empty boundary
of a one-vertex core. See Cairns 1940, Section 7(B), p. 803, and
M76 derivation 44.
-/


open Set

variable {ι : Type*} [Fintype ι]

/-- The barycentric sum is one on the whole affine span of a
closed core. See Cairns p. 803 and M76 derivation 44. -/
theorem sum_eq_one_of_mem_affineSpan_stdSimplexCore {η : ℝ} {q : ι → ℝ}
    (hq : q ∈ affineSpan ℝ (stdSimplexCore ι η)) : ∑ i, q i = 1 := by
  refine affineSpan_induction hq (fun r hr => hr.2) (fun c u v w hu hv hw => ?_)
  simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    hu, hv, hw, sub_self, mul_zero, zero_add]

variable [Nonempty ι]

/-- A core's intrinsic interior is given by strict barycentric
inequalities and the usual sum equation.
See Cairns pp. 802--803 and M76 derivation 44. -/
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

/-- The intrinsic frontier of a closed core is precisely where
at least one barycentric coordinate reaches the threshold.
See Cairns Section 7(B), p. 803 and M76 derivation 44. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplexCoreRegions.lean
section

/-!
# The closed core regions cover a simplex

Partitioning barycentric coordinates by a face gives the box
regions from Cairns' recurrence. They cover the simplex, and
overlaps with earlier faces attach at threshold coordinates.
See Cairns 1940, Section 7(A)--(B), pp. 802--803, and M76
derivation 44.
-/


open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]

/-- The closed core region associated with a face of a simplex,
using the full simplex's barycentric coordinates.
See Cairns (7.1)--(7.3), pp. 802--803 and M76 derivation 44. -/
def faceRegion (s : Finset ι) (η : ℝ) : Set (ι → ℝ) :=
  {q | q ∈ stdSimplex ℝ ι ∧ (∀ i ∈ s, η ≤ q i) ∧ ∀ i ∉ s, q i ≤ η}

/-- Every core region is closed, retaining all its attachment
faces. See Cairns p. 803 and M76 derivation 44. -/
theorem isClosed_faceRegion (s : Finset ι) (η : ℝ) : IsClosed (faceRegion s η) := by
  have he : faceRegion s η = stdSimplex ℝ ι ∩
      (⋂ i ∈ s, {q : ι → ℝ | η ≤ q i}) ∩ (⋂ i ∉ s, {q : ι → ℝ | q i ≤ η}) := by
    ext q
    simp only [faceRegion, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [he]
  exact ((isClosed_stdSimplex ℝ ι).inter (isClosed_iInter fun i =>
    isClosed_iInter fun _ => isClosed_le continuous_const (continuous_apply i))).inter
      (isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_le (continuous_apply i) continuous_const)

/-- Core regions are compact subsets of their simplex.
See Cairns p. 803 and M76 derivation 44. -/
theorem isCompact_faceRegion (s : Finset ι) (η : ℝ) : IsCompact (faceRegion s η) :=
  (isCompact_stdSimplex ℝ ι).of_isClosed_subset (isClosed_faceRegion s η) (fun _ h => h.1)

/-- The closed regions cover the simplex. The chosen face is
nonempty and lies in the positive support of the point.
See Cairns p. 803 and M76 derivation 44. -/
theorem exists_mem_faceRegion {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ}
    (hq : q ∈ stdSimplex ℝ ι) :
    ∃ s : Finset ι, s.Nonempty ∧ (∀ i ∈ s, 0 < q i) ∧ q ∈ faceRegion s η := by
  classical
  let s := Finset.univ.filter (fun i => η < q i)
  have hs : s.Nonempty := by
    by_contra hn
    have hle : ∀ i, q i ≤ η := by
      intro i
      by_contra hi
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_not_ge hi⟩⟩
    have hsum : (∑ i, q i) ≤ (Fintype.card ι : ℝ) * η := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hle i)
    linarith [hq.2]
  refine ⟨s, hs, ?_, hq, ?_, ?_⟩
  · intro i hi
    exact hη.trans_lt (Finset.mem_filter.mp hi).2
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  · intro i hi
    exact le_of_not_gt (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))

/-- On two intersecting regions, a coordinate belonging to only
the first face must equal the threshold.
See Cairns Section 7(B), p. 803 and M76 derivation 44. -/
theorem coordinate_eq_of_mem_faceRegions {s t : Finset ι} {η : ℝ} {q : ι → ℝ}
    (hs : q ∈ faceRegion s η) (ht : q ∈ faceRegion t η)
    {i : ι} (hi : i ∈ s) (hit : i ∉ t) : q i = η :=
  le_antisymm (ht.2.2 i hit) (hs.2.1 i hi)

/-- Distinct regions of no larger face dimension meet only on
threshold coordinates of the first face.
See Cairns Section 7(B), p. 803 and M76 derivation 44. -/
theorem exists_threshold_of_mem_faceRegions {s t : Finset ι} {η : ℝ} {q : ι → ℝ}
    (hs : q ∈ faceRegion s η) (ht : q ∈ faceRegion t η)
    (hne : s ≠ t) (hcard : t.card ≤ s.card) : ∃ i ∈ s, i ∉ t ∧ q i = η := by
  have hnot : ¬s ⊆ t := fun h => hne (Finset.eq_of_subset_of_card_le h hcard)
  obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp hnot
  exact ⟨i, hi, hit, coordinate_eq_of_mem_faceRegions hs ht hi hit⟩

variable [DecidableEq ι]

/-- Splitting the barycentric coordinates into a face and its
complement gives exactly the previously checked box region.
See Cairns p. 803 and M76 derivation 44. -/
noncomputable def faceRegionBoxHomeomorph (s : Finset ι) {η : ℝ} (hη : 0 ≤ η) :
    faceRegion s η ≃ₜ boxRegion s {i // i ∉ s} η := by
  classical
  let e := Homeomorph.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => ℝ)
  apply e.subtype
  intro q
  change q ∈ faceRegion s η ↔
    (∀ i : s, η ≤ q i) ∧ (fun i : {i // i ∉ s} => q i) ∈ Icc 0 (fun _ => η) ∧
      (∑ i : s, q i) + ∑ i : {i // i ∉ s}, q i = 1
  have hsum : (∑ i : s, q i) + ∑ i : {i // i ∉ s}, q i = ∑ i, q i := by
    convert Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) q using 1
    congr 1
    congr 1
    ext i
    simp
  rw [hsum]
  constructor
  · intro hq
    exact ⟨fun i => hq.2.1 i i.property,
      ⟨fun i => hq.1.1 i, fun i => hq.2.2 i i.property⟩, hq.1.2⟩
  · rintro ⟨hi, hv, hsum⟩
    refine ⟨⟨fun i => ?_, hsum⟩, fun i his => hi ⟨i, his⟩, fun i his => hv.2 ⟨i, his⟩⟩
    by_cases his : i ∈ s
    · exact hη.trans (hi ⟨i, his⟩)
    · exact hv.1 ⟨i, his⟩

/-- Every face region has product coordinates by its closed
core and complementary cube. See Cairns p. 803 and M76 derivation 44. -/
noncomputable def faceRegionProductHomeomorph (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) :
    (stdSimplexCore s η × Icc (0 : {i // i ∉ s} → ℝ) (fun _ => η)) ≃ₜ faceRegion s η := by
  classical
  have hc : (Fintype.card s : ℝ) + Fintype.card {i // i ∉ s} = Fintype.card ι := by
    simpa using Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) (fun _ => (1 : ℝ))
  exact (boxHomeomorph hη (hc ▸ hbound)).trans (faceRegionBoxHomeomorph s hη).symm

end StdSimplexCore

end

-- Source: PoincareMT/Proofs/M76/Mathlib/CoreRegionBoundary.lean
section

/-!
# Boundary attachments between core regions

In product coordinates, any overlap with an earlier face region
lies above the intrinsic frontier of the core. This is the boundary
condition in Cairns' recurrence, Section 7(B), p. 803; see M76
derivation 44. Equality of the actual fields on these attachments
is a subsequent gluing obligation.
-/


open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]

/-- The full simplex's threshold bound also holds for each
face. See Cairns pp. 802--803 and M76 derivation 44. -/
theorem face_threshold_bound (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) : (Fintype.card s : ℝ) * η < 1 := by
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ hη) hbound
  rw [Fintype.card_coe]
  exact_mod_cast (show s.card ≤ Fintype.card ι from Finset.card_le_univ s)

variable [DecidableEq ι]

/-- A threshold coordinate of a region point places its core
base on the intrinsic frontier of the core.
See Cairns Section 7(B), p. 803 and M76 derivation 44. -/
theorem faceRegion_base_mem_intrinsicFrontier (s : Finset ι) (hs : s.Nonempty)
    {η : ℝ} (hη : 0 ≤ η) (hbound : (Fintype.card ι : ℝ) * η < 1)
    (q : faceRegion s η) {i : ι} (hi : i ∈ s) (he : q.val i = η) :
    (((faceRegionProductHomeomorph s hη hbound).symm q).1 : s → ℝ) ∈
      intrinsicFrontier ℝ (stdSimplexCore s η) := by
  have : Nonempty s := by
    obtain ⟨j, hj⟩ := hs
    exact ⟨⟨j, hj⟩⟩
  apply (mem_intrinsicFrontier_stdSimplexCore_iff (face_threshold_bound s hη hbound)).mpr
  refine ⟨((faceRegionProductHomeomorph s hη hbound).symm q).1.property, ⟨i, hi⟩, ?_⟩
  change η + (q.val i - η) / _ = η
  rw [he, sub_self, zero_div, add_zero]

/-- Every intersection with a distinct region of no larger face
dimension attaches over the intrinsic core boundary. All common
faces are retained. See Cairns Section 7(B), p. 803 and M76 derivation 44. -/
theorem faceRegion_base_mem_intrinsicFrontier_of_overlap (s t : Finset ι)
    (hs : s.Nonempty) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η)
    (ht : q.val ∈ faceRegion t η) (hne : s ≠ t) (hcard : t.card ≤ s.card) :
    (((faceRegionProductHomeomorph s hη hbound).symm q).1 : s → ℝ) ∈
      intrinsicFrontier ℝ (stdSimplexCore s η) := by
  obtain ⟨i, hi, _, he⟩ := exists_threshold_of_mem_faceRegions q.property ht hne hcard
  exact faceRegion_base_mem_intrinsicFrontier s hs hη hbound q hi he

end StdSimplexCore

end

-- Source: PoincareMT/Proofs/M76/Mathlib/CoreProjectionCoordinates.lean
section

/-!
# Rational core projections are the geometric box bases

Region membership supplies positive residual mass. The rational
projection therefore agrees with the core base in the product
homeomorphism, preserves simplex coordinates, and is smooth near
every region point. See Cairns 1940, pp. 803--805, and M76
derivation 45.
-/


open Set
open scoped ContDiff

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Residual mass on a face is the product of its core-size
factor and the box radial factor.
See Cairns p. 803 and M76 derivation 45. -/
theorem residualMass_eq_boxScale_mul (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    residualMass s η q.val = boxScale s η (fun j : {i // i ∉ s} => q.val j) *
      (1 - (Fintype.card s : ℝ) * η) := by
  have hsum : (∑ i : s, q.val i) + ∑ j : {i // i ∉ s}, q.val j = 1 :=
    ((faceRegionBoxHomeomorph s hη) q).property.2.2
  have hm : residualMass s η q.val = (∑ i : s, q.val i) - (Fintype.card s : ℝ) * η := by
    simp only [residualMass, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.sum_coe_sort, Fintype.card_coe]
  rw [hm, boxScale_mul (sub_pos.mpr (face_threshold_bound s hη hbound)).ne']
  linarith

omit [DecidableEq ι] in
/-- A region point has strictly positive face residual mass,
including all its boundary attachments.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem residualMass_pos_of_mem_faceRegion (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    0 < residualMass s η q.val := by
  classical
  have hc : (Fintype.card s : ℝ) + Fintype.card {i // i ∉ s} = Fintype.card ι := by
    simpa using Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) (fun _ => (1 : ℝ))
  have ha := boxScale_pos (ι := s) hη (hc ▸ hbound)
    ((faceRegionBoxHomeomorph s hη) q).property.2.1
  rw [residualMass_eq_boxScale_mul s hη hbound q]
  exact mul_pos ha (sub_pos.mpr (face_threshold_bound s hη hbound))

/-- The rational projection restricted to its face is exactly
the geometric core base from the product homeomorphism.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem projectToFace_eq_boxBase (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    (fun i : s => projectToFace s η q.val i) =
      (((faceRegionProductHomeomorph s hη hbound).symm q).1 : s → ℝ) := by
  have hden : 1 - (s.card : ℝ) * η ≠ 0 := by
    simpa only [Fintype.card_coe] using (sub_pos.mpr (face_threshold_bound s hη hbound)).ne'
  funext i
  simp only [projectToFace, if_pos i.property]
  change η + (q.val i - η) * (1 - (s.card : ℝ) * η) / residualMass s η q.val =
    η + (q.val i - η) / boxScale s η (fun j : {i // i ∉ s} => q.val j)
  rw [residualMass_eq_boxScale_mul s hη hbound q, Fintype.card_coe,
    mul_div_mul_right _ _ hden]

/-- The projection of a region point lies in the actual closed
face core in barycentric coordinates.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem projectToFace_mem_core (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    (fun i : s => projectToFace s η q.val i) ∈ stdSimplexCore s η := by
  rw [projectToFace_eq_boxBase s hη hbound q]
  exact ((faceRegionProductHomeomorph s hη hbound).symm q).1.property

/-- The core projection remains in the original full simplex.
See Cairns pp. 803--804 and M76 derivation 45. -/
theorem projectToFace_mem_stdSimplex (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η) :
    projectToFace s η q.val ∈ stdSimplex ℝ ι := by
  have hcore := projectToFace_mem_core s hη hbound q
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hi : i ∈ s
    · exact hη.trans (hcore.1 ⟨i, hi⟩)
    · simp only [projectToFace, if_neg hi, le_refl]
  · have hsum : (∑ i, projectToFace s η q.val i) = ∑ i ∈ s, projectToFace s η q.val i := by
      symm
      apply Fintype.sum_subset
      intro i hi
      by_contra his
      exact hi (by simp only [projectToFace, if_neg his])
    rw [hsum]
    exact sum_projectToFace s η q.val (residualMass_pos_of_mem_faceRegion s hη hbound q).ne'

/-- The rational core projection is smooth wherever its
residual mass is nonzero. See Cairns pp. 804--805 and M76 derivation 45. -/
theorem contDiffAt_projectToFace (s : Finset ι) (η : ℝ) (n : ℕ∞ω) (q : ι → ℝ)
    (hq : residualMass s η q ≠ 0) : ContDiffAt ℝ n (projectToFace s η) q := by
  have hm : ContDiff ℝ n (residualMass s η) := by
    unfold residualMass
    fun_prop
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i ∈ s
  · simp only [projectToFace, if_pos hi]
    exact contDiffAt_const.add
      ((((contDiff_apply ℝ ℝ i).contDiffAt.sub contDiffAt_const).mul contDiffAt_const).div
        hm.contDiffAt hq)
  · simpa only [projectToFace, if_neg hi] using
      (contDiffAt_const : ContDiffAt ℝ n (fun _ : ι → ℝ => (0 : ℝ)) q)

end StdSimplexCore

end

-- Source: PoincareMT/Proofs/M76/Mathlib/BarycentricCoreComplex.lean
section

/-!
# Core regions on a finite barycentric complex

Global barycentric coordinates make the box bases independent of
the containing simplex. A positive threshold makes every region
label an actual face. See Cairns 1940, Sections 7--8, pp. 802--805,
and M76 derivation 49.
-/


open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Zero extension of face coordinates into the common barycentric
space. See Cairns pp. 802--803 and M76 derivation 49. -/
noncomputable def faceInclusion (s : Finset ι) : (s → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => if hi : i ∈ s then
    ContinuousLinearMap.proj ⟨i, hi⟩ else 0)

omit [Fintype ι] in
/-- Face coordinates are unchanged by their zero extension.
See Cairns pp. 802--803 and M76 derivation 49. -/
theorem faceInclusion_apply_mem (s : Finset ι) (q : s → ℝ) {i : ι} (hi : i ∈ s) :
    faceInclusion s q i = q ⟨i, hi⟩ := by
  simp only [faceInclusion, ContinuousLinearMap.pi_apply, dif_pos hi,
    ContinuousLinearMap.proj_apply]

omit [Fintype ι] in
/-- Coordinates outside the chosen face vanish under zero extension.
See Cairns pp. 802--803 and M76 derivation 49. -/
theorem faceInclusion_apply_notMem (s : Finset ι) (q : s → ℝ) {i : ι} (hi : i ∉ s) :
    faceInclusion s q i = 0 := by
  simp only [faceInclusion, ContinuousLinearMap.pi_apply, dif_neg hi,
    zero_apply]

/-- Zero extension retains the sum of barycentric coordinates.
See Cairns pp. 802--803 and M76 derivation 49. -/
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

/-- A closed face simplex in common barycentric coordinates.
See Cairns pp. 802--803 and M76 derivation 49. -/
def barycentricFace (s : Finset ι) : Set (ι → ℝ) :=
  {q | q ∈ stdSimplex ℝ ι ∧ ∀ i ∉ s, q i = 0}

omit [DecidableEq ι] in
/-- A face simplex is closed in the common coordinate space.
See Cairns p. 803 and M76 derivation 49. -/
theorem isClosed_barycentricFace (s : Finset ι) : IsClosed (barycentricFace s) := by
  have he : barycentricFace s = stdSimplex ℝ ι ∩
      ⋂ i ∉ s, {q : ι → ℝ | q i = 0} := by
    ext q
    simp only [barycentricFace, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [he]
  exact (isClosed_stdSimplex ℝ ι).inter (isClosed_iInter fun i =>
    isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const)

omit [DecidableEq ι] in
/-- Every face simplex is compact. See Cairns p. 803 and
M76 derivation 49. -/
theorem isCompact_barycentricFace (s : Finset ι) : IsCompact (barycentricFace s) :=
  (isCompact_stdSimplex ℝ ι).of_isClosed_subset (isClosed_barycentricFace s) (fun _ h => h.1)

/-- Zero extension embeds a closed core into its actual face simplex.
See Cairns pp. 802--803 and M76 derivation 49. -/
theorem faceInclusion_mem_barycentricFace (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    {q : s → ℝ} (hq : q ∈ stdSimplexCore s η) : faceInclusion s q ∈ barycentricFace s := by
  refine ⟨⟨fun i => ?_, (sum_faceInclusion s q).trans hq.2⟩,
    fun i hi => faceInclusion_apply_notMem s q hi⟩
  by_cases hi : i ∈ s
  · rw [faceInclusion_apply_mem s q hi]
    exact hη.trans (hq.1 ⟨i, hi⟩)
  · rw [faceInclusion_apply_notMem s q hi]

/-- An embedded core lies in its own closed face region.
See Cairns p. 803 and M76 derivation 49. -/
theorem faceInclusion_mem_faceRegion (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    {q : s → ℝ} (hq : q ∈ stdSimplexCore s η) : faceInclusion s q ∈ faceRegion s η := by
  refine ⟨(faceInclusion_mem_barycentricFace s hη hq).1, ?_, ?_⟩
  · intro i hi
    rw [faceInclusion_apply_mem s q hi]
    exact hq.1 ⟨i, hi⟩
  · intro i hi
    simpa only [faceInclusion_apply_notMem s q hi] using hη

/-- The rational core base belongs to its actual face simplex.
See Cairns pp. 803--805 and M76 derivation 49. -/
theorem projectToFace_mem_barycentricFace (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ}
    (hq : q ∈ faceRegion s η) : projectToFace s η q ∈ barycentricFace s := by
  refine ⟨projectToFace_mem_stdSimplex s hη hbound ⟨q, hq⟩, ?_⟩
  intro i hi
  simp only [projectToFace, if_neg hi]

omit [Fintype ι] in
/-- Zero extension recovers the full rational projection from its
face coordinates. See Cairns pp. 803--805 and M76 derivation 49. -/
theorem faceInclusion_projectToFace (s : Finset ι) (η : ℝ) (q : ι → ℝ) :
    faceInclusion s (fun i : s => projectToFace s η q i) = projectToFace s η q := by
  ext i
  by_cases hi : i ∈ s
  · exact faceInclusion_apply_mem s _ hi
  · simp only [faceInclusion_apply_notMem s _ hi, projectToFace, if_neg hi]

omit [DecidableEq ι] in
/-- Positive thresholds force a region label to lie in any face
containing the point. See Cairns p. 803 and M76 derivation 49. -/
theorem subset_of_mem_barycentricFace_faceRegion {s t : Finset ι} {η : ℝ} (hη : 0 < η)
    {q : ι → ℝ} (hqt : q ∈ barycentricFace t) (hqs : q ∈ faceRegion s η) : s ⊆ t := by
  intro i hi
  by_contra hit
  have h := hqs.2.1 i hi
  rw [hqt.2 i hit] at h
  exact hη.not_ge h

end StdSimplexCore

namespace PreAbstractSimplicialComplex

open StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite complex's carrier in common barycentric coordinates.
See Cairns pp. 802--803 and M76 derivation 49. -/
def barycentricSpace (A : PreAbstractSimplicialComplex ι) : Set (ι → ℝ) :=
  ⋃ s ∈ A.faces, barycentricFace s

omit [DecidableEq ι] in
/-- The barycentric carrier of a complex on finitely many labels
is compact. See Cairns p. 803 and M76 derivation 49. -/
theorem isCompact_barycentricSpace (A : PreAbstractSimplicialComplex ι) :
    IsCompact A.barycentricSpace :=
  (Set.toFinite A.faces).isCompact_biUnion (fun s _ => isCompact_barycentricFace s)

omit [DecidableEq ι] in
/-- A face simplex lies in the barycentric carrier.
See Cairns p. 803 and M76 derivation 49. -/
theorem barycentricFace_subset_barycentricSpace (A : PreAbstractSimplicialComplex ι)
    {s : Finset ι} (hs : s ∈ A.faces) : barycentricFace s ⊆ A.barycentricSpace :=
  subset_iUnion₂_of_subset s hs Subset.rfl

/-- The closed union of a core's boxes over all incident simplexes.
See Cairns (7.4), p. 803 and M76 derivation 49. -/
def coreRegion (A : PreAbstractSimplicialComplex ι) (s : Finset ι) (η : ℝ) : Set (ι → ℝ) :=
  A.barycentricSpace ∩ faceRegion s η

omit [DecidableEq ι] in
/-- Each core region on the entire complex is compact.
See Cairns p. 803 and M76 derivation 49. -/
theorem isCompact_coreRegion (A : PreAbstractSimplicialComplex ι) (s : Finset ι) (η : ℝ) :
    IsCompact (A.coreRegion s η) :=
  A.isCompact_barycentricSpace.inter_right (isClosed_faceRegion s η)

/-- Core projections stay in the corresponding region on the
whole complex. See Cairns pp. 803--805 and M76 derivation 49. -/
theorem projectToFace_mem_coreRegion (A : PreAbstractSimplicialComplex ι)
    {s : Finset ι} (hs : s ∈ A.faces) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) {q : ι → ℝ}
    (hq : q ∈ faceRegion s η) : projectToFace s η q ∈ A.coreRegion s η := by
  refine ⟨A.barycentricFace_subset_barycentricSpace hs
    (projectToFace_mem_barycentricFace s hη hbound hq), ?_⟩
  rw [← faceInclusion_projectToFace s η q]
  exact faceInclusion_mem_faceRegion s hη (projectToFace_mem_core s hη hbound ⟨q, hq⟩)

omit [DecidableEq ι] in
/-- The actual nonempty face regions cover the entire finite
complex. See Cairns p. 803 and M76 derivation 49. -/
theorem exists_mem_coreRegion (A : PreAbstractSimplicialComplex ι)
    {η : ℝ} (hη : 0 < η) (hbound : (Fintype.card ι : ℝ) * η < 1)
    {q : ι → ℝ} (hq : q ∈ A.barycentricSpace) :
    ∃ s ∈ A.faces, q ∈ A.coreRegion s η := by
  classical
  obtain ⟨t, ht, hqt⟩ := mem_iUnion₂.mp hq
  obtain ⟨s, hs, _, hqs⟩ := exists_mem_faceRegion hη.le hbound hqt.1
  have hst := subset_of_mem_barycentricFace_faceRegion hη hqt hqs
  exact ⟨s, (A.isRelLowerSet_faces ht).2 hst hs, hq, hqs⟩

end PreAbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/BarycentricRealization.lean
section

/-!
# The barycentric realization homeomorphism

Summing the weighted actual vertices identifies the compact
barycentric carrier with an independent geometric complex in its
original topology. See Cairns 1940, pp. 798--799, 804, and M76
derivation 50.
-/


open Set Geometry

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A face simplex is the image of its own standard simplex by
zero extension. See Cairns pp. 802--803 and M76 derivation 50. -/
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
/-- Zero extension carries a face vertex to its matching global
barycentric vertex. See Cairns pp. 802--803 and M76 derivation 50. -/
theorem faceInclusion_single (s : Finset ι) (i : s) :
    faceInclusion s (Pi.single i 1) = Pi.single i.val 1 := by
  ext j
  by_cases hj : j ∈ s
  · rw [faceInclusion_apply_mem s _ hj]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · rw [faceInclusion_apply_notMem s _ hj]
    have hne : i.val ≠ j := fun he => hj (he ▸ i.property)
    simp [hne]

/-- The global face simplex is the convex hull of its labelled
coordinate vertices. See Cairns pp. 802--803 and M76 derivation 50. -/
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

/-- Finite barycentric synthesis into the actual vertex positions.
See Cairns pp. 798--799 and M76 derivation 50. -/
noncomputable def barycentricMap (v : ι → E) : (ι → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (v i)

omit [DecidableEq ι] in
/-- Barycentric synthesis is the weighted sum of actual vertices.
See Cairns pp. 798--799 and M76 derivation 50. -/
theorem barycentricMap_apply (v : ι → E) (q : ι → ℝ) :
    barycentricMap v q = ∑ i, q i • v i := by
  simp only [barycentricMap, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- Coordinate vertices synthesize to the actual vertices.
See Cairns pp. 798--799 and M76 derivation 50. -/
theorem barycentricMap_single (v : ι → E) (i : ι) : barycentricMap v (Pi.single i 1) = v i := by
  simp [barycentricMap_apply, Pi.single_apply, ite_smul]

omit [DecidableEq ι] in
/-- Synthesis maps a face onto the convex hull of its actual
vertices. See Cairns pp. 798--799 and M76 derivation 50. -/
theorem image_barycentricFace (v : ι → E) (s : Finset ι) :
    barycentricMap v '' barycentricFace s = convexHull ℝ (v '' (s : Set ι)) := by
  classical
  rw [barycentricFace_eq_convexHull]
  change (barycentricMap v).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull, image_image]
  change convexHull ℝ ((fun i => barycentricMap v (Pi.single i 1)) '' (s : Set ι)) = _
  simp only [barycentricMap_single]

omit [DecidableEq ι] in
/-- Affine independence gives unique barycentric coordinates on
the standard simplex. See Cairns p. 798 and M76 derivation 50. -/
theorem injOn_barycentricMap (v : ι → E) (hv : AffineIndependent ℝ v) :
    InjOn (barycentricMap v) (stdSimplex ℝ ι) := by
  intro q hq r hr he
  funext i
  exact hv.eq_of_sum_eq_sum (hq.2.trans hr.2.symm)
    (by simpa only [barycentricMap_apply] using he) i (Finset.mem_univ i)

end StdSimplexCore

namespace Geometry.SimplicialComplex

open StdSimplexCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Synthesis of the actual vertex labels maps the entire
barycentric carrier onto the geometric carrier.
See Cairns pp. 798--799 and M76 derivation 50. -/
theorem image_barycentricSpace (K : SimplicialComplex ℝ E) [Fintype K.vertices] :
    barycentricMap ((↑) : K.vertices → E) ''
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace = K.space := by
  classical
  apply Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.mp hq
    refine mem_space_iff.mpr ⟨s.map (Function.Embedding.subtype _), hs, ?_⟩
    rw [Finset.coe_map, Function.Embedding.coe_subtype,
      ← image_barycentricFace ((↑) : K.vertices → E) s]
    exact mem_image_of_mem _ hqs
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨s, hs, he⟩ := K.faces_eq_vertexAbstractComplex_images ▸ ht
    rw [he, ← image_barycentricFace ((↑) : K.vertices → E) s] at hxt
    obtain ⟨q, hq, rfl⟩ := hxt
    exact ⟨q, mem_iUnion₂.mpr ⟨s, hs, hq⟩, rfl⟩

/-- An independent finite geometric complex is homeomorphic to
the barycentric carrier on its actual vertices, including the
empty complex. See Cairns p. 798 and M76 derivation 50. -/
noncomputable def barycentricHomeomorph (K : SimplicialComplex ℝ E) [Fintype K.vertices]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) :
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace ≃ₜ K.space := by
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let v := ((↑) : K.vertices → E)
  have hinj : InjOn (barycentricMap v) A.barycentricSpace :=
    (injOn_barycentricMap v hK).mono (by
      intro q hq
      obtain ⟨s, _, hqs⟩ := mem_iUnion₂.mp hq
      exact hqs.1)
  let : CompactSpace A.barycentricSpace :=
    isCompact_iff_compactSpace.mp A.isCompact_barycentricSpace
  let e : A.barycentricSpace ≃ₜ barycentricMap v '' A.barycentricSpace :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn (barycentricMap v) A.barycentricSpace hinj)
      (((barycentricMap v).continuous.comp continuous_subtype_val).subtype_mk _)
  exact e.trans (Homeomorph.setCongr K.image_barycentricSpace)

/-- The realization homeomorphism retains the explicit barycentric
formula. See Cairns p. 798 and M76 derivation 50. -/
theorem barycentricHomeomorph_apply (K : SimplicialComplex ℝ E) [Fintype K.vertices]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E))
    (q : K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace) :
    (K.barycentricHomeomorph hK q : E) = barycentricMap ((↑) : K.vertices → E) q := rfl

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplexIntrinsicFrontier.lean
section

/-!
# The intrinsic frontier of a geometric simplex

Barycentric synthesis is injective on the affine span of the standard
simplex. Transporting its frontier identifies the geometric frontier
with the proper faces. See Cairns 1940, pp. 803--805 and M76 derivation 64.
-/


open Set

namespace StdSimplexCore

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Barycentric synthesis is injective on the full affine span
of the simplex. See Cairns pp. 803--805 and M76 derivation 64. -/
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
/-- The intrinsic frontier of a finite independent simplex is
the union of the convex hulls with one vertex omitted.
See Cairns pp. 803--805 and M76 derivation 64. -/
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

/-- A point lies in a geometric simplex's intrinsic frontier
exactly when it lies in the hull omitting some vertex.
See Cairns pp. 803--805 and M76 derivation 64. -/
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
/-- The hull of every proper subface lies in the intrinsic
frontier of an independent simplex. See Cairns pp. 803--805
and M76 derivation 64. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplicialFrontierAttachment.lean
section

/-!
# Frontier and intersection conditions for finite simplex attachment

The intrinsic frontier is covered by proper faces, and a distinct
face of no larger dimension meets a new face only there. These are
the geometric hypotheses of Cairns' finite recurrence, pp. 803--805;
see M76 derivation 64.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every intrinsic-boundary point of a face lies in a nonempty
proper face of the complex. See Cairns pp. 803--805 and M76 derivation 64. -/
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

/-- Distinct faces of no larger cardinality meet the new face
only in its intrinsic frontier. See Cairns pp. 803--805 and
M76 derivation 64. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/FiniteSmoothLeafField.lean
section

/-!
# Finite smooth transverse leaf fields

Attach simplices in increasing cardinality, preserving ambient germs
on the processed carrier. Full cofaces, nonempty vertex targets and
contractible positive-face targets are explicit. See Cairns 1940,
pp. 803--805 and M76 derivation 65.
-/


open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

open EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- A finite downward-closed face family admits a smooth ambient
leaf field transverse to the original closed star of each face.
See Cairns pp. 803--805 and M76 derivation 65. -/
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

/-- A finite pure complex with nonempty vertex plane spaces and
contractible positive-face plane spaces admits a smooth ambient
leaf field of the prescribed codimension. See Cairns pp. 803--805
and M76 derivation 65. -/
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

/-- For a finite closed star, absence of a nonzero secant in a plane is equivalent to
orthogonal projection away from that plane retaining a positive fraction of every secant's
length. -/
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

/-! Adapt the finite PoincareMT leaf construction to the registered plane gluing step. -/
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

/-- The finite smooth leaf field gives the registered kernels and local projection maps. -/
theorem exact_smooth_leaf_field :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1.H2 := by
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

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1.H2 :=
  OMA.PoincareSmoothLeafPort.exact_smooth_leaf_field
