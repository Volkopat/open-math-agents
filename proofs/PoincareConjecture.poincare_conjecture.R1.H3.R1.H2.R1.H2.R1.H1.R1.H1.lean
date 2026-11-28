import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
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

-- Source: PoincareMT/Proofs/M76/Mathlib/FiniteCycleLabels.lean
section

/-!
# Cyclic labels for finite connected graphs of degree two

Mathlib's cycle theorem supplies a simple closed walk covering the
connected component. Removing its repeated endpoint gives cyclic
labels for every vertex and exactly the graph's edges. This is the
finite incidence step for the circle links in Cairns 1940, pp. 802,
807; see M76 derivation 41.
-/


open Set

namespace SimpleGraph

variable {V : Type*} [Finite V]

/-- A finite connected simple graph with two neighbors at each
vertex admits a cyclic labelling of all vertices. Every graph edge
is a consecutive cyclic pair, with either orientation allowed.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ComplexCycleLabels.lean
section

/-!
# Cyclic labels from one-dimensional complex incidence

The graph of distinct two-vertex faces determines a complex whose
faces have at most two vertices. Finite connected degree-two incidence
therefore gives exact cyclic labels for all its faces. See Cairns
1940, pp. 802, 807, and M76 derivation 41.
-/


namespace AbstractSimplicialComplex

variable {V : Type*} [DecidableEq V]

/-- The graph whose edges are the distinct two-vertex faces.
Higher-dimensional faces do not themselves contribute extra edges.
See Cairns pp. 802, 807 and M76 derivation 41. -/
def edgeGraph (A : AbstractSimplicialComplex V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ {x, y} ∈ A.faces
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- If all faces have at most two vertices, they are precisely
the singletons and graph edges.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

/-- Finite connected degree-two incidence supplies a vertex
bijection preserving every cyclic singleton and edge face, in both
directions. The explicit size bound excludes higher faces.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/ConnectedComplexGraph.lean
section

/-!
# Connected geometric carriers and their edge graphs

On a finite complex, a vertex component's zero-one indicator extends
to a continuous facewise constant function. A preconnected carrier
forces it to be constant, so the edge graph is preconnected. See
Cairns 1940, pp. 802, 807, and M76 derivation 41.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

omit [DecidableEq E] in
/-- A finite face collection has only finitely many actual vertices.
See Cairns pp. 802, 807 and M76 derivation 41. -/
theorem finite_vertices_of_finite_faces (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) : K.vertices.Finite :=
  hfinite.preimage Finset.singleton_injective.injOn

/-- Two actual vertices of one face are reachable in the edge
graph, using their two-vertex subface when distinct.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

/-- A preconnected finite geometric carrier has a preconnected
edge graph. The proof extends a vertex component indicator and uses
connectedness of its continuous zero-one-valued image.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

/-- A connected finite geometric carrier has a connected edge
graph on its actual vertices, including the required nonemptiness.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/LinkGraphIncidence.lean
section

/-!
# Edge degrees as vertex counts of actual links

Iterated links along disjoint faces equal the link of their union.
The neighbors of an actual vertex are exactly its singleton-link
vertices. This supplies the incidence condition for cyclic normal
links in Cairns 1940, pp. 800, 802, 807; see M76 derivation 41.
-/


open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

/-- Taking successive links along disjoint finite vertex sets
equals taking the link of their union. Downward closure supplies
all intermediate cofaces.
See Cairns pp. 800, 807 and M76 derivation 41. -/
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

/-- Two actual vertices are adjacent exactly when the second is
a vertex of the first vertex's link.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

/-- Forgetting actual-vertex subtype labels maps the entire
neighbor set onto the singleton-link vertex set.
See Cairns pp. 802, 807 and M76 derivation 41. -/
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

/-- The neighbor count is the number of actual singleton-link
vertices, with the same convention for infinite sets on both sides.
See Cairns pp. 802, 807 and M76 derivation 41. -/
theorem ncard_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E) (u : K.vertices) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink {u.val}).vertices.ncard := by
  rw [← K.image_edgeGraph_neighborSet u, ncard_image_of_injective _ Subtype.val_injective]

/-- Degree at a vertex of a face link equals the vertex count
of the enlarged-face link in the original complex.
See Cairns pp. 800, 807 and M76 derivation 41. -/
theorem ncard_faceLink_edgeGraph_neighborSet (K : SimplicialComplex 𝕜 E)
    (s : Finset E) (u : (K.faceLink s).vertices) :
    ((K.faceLink s).vertexAbstractComplex.edgeGraph.neighborSet u).ncard =
      (K.faceLink (s ∪ {u.val})).vertices.ncard := by
  rw [(K.faceLink s).ncard_edgeGraph_neighborSet u,
    K.faceLink_faceLink s {u.val} u.property.2.1]

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialConeLabels.lean
section

/-!
# Removing labels and restricting to the actual radial span

Face-preserving changes of labels leave radial complexes and their
cones unchanged. An independent realization is exactly the inclusion
of its basis realization in its actual span. See Cairns 1940,
pp. 800--801, and M76 derivation 40.
-/


open Set

namespace AbstractSimplicialComplex

variable {ι κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι} {B : AbstractSimplicialComplex κ}

/-- A bijective relabelling preserving every finite face and its
vertex values leaves the actual geometric realization unchanged.
See Cairns pp. 800--801 and M76 derivation 40. -/
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

/-- Relabelling a radial complex does not change its full conical
star, including the empty-link case.
See Cairns pp. 800--801 and M76 derivation 40. -/
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

/-- An independent radial cone is exactly the included basis cone
of the span of its actual vertex vectors.
See Cairns pp. 800--801 and M76 derivation 40. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/FaceStarInjectivity.lean
section

/-!
# Linear injectivity on an actual face star and its saturation

The common positive rescaling of saturated secants transfers
injectivity of arbitrary linear maps. Intrinsic interior supplies
this comparison for every nonempty face. See Cairns 1940,
pp. 799--800, and M76 derivations 35 and 38.
-/


open Set
open scoped Pointwise

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Linear injectivity transfers when every target secant can be
positively rescaled to a source secant.
See Cairns p. 799 and M76 derivation 38. -/
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

/-- Intrinsic interior of the central face makes linear injectivity
equivalent on a star and its full tangent saturation.
See Cairns pp. 799--800 and M76 derivation 38. -/
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

/-- Every nonempty face star and its tangent saturation have the
same injective linear maps. No separate relative-neighborhood premise
is needed. See Cairns pp. 799--800 and M76 derivation 38. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/TangentCylinderProjection.lean
section

/-!
# Linear projections of tangent cylinders

Normalized projections fixing a tangent factor have a triangular
block form. Injectivity on a full cylinder is exactly injectivity of
the normal block on its source set. See Cairns 1940, Section 4,
pp. 800--801, and M76 derivation 33.
-/


open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The triangular projection with normal block B and tangent shear A.
See Cairns Section 4, pp. 800--801, and M76 derivation 33. -/
def tangentCylinderProjection (B : E →L[ℝ] F) (A : E →L[ℝ] T) : (E × T) →L[ℝ] (F × T) :=
  (B.comp (fst ℝ E T)).prod (snd ℝ E T + A.comp (fst ℝ E T))

/-- The block formula on an actual cylinder point.
See Cairns p. 800 and M76 derivation 33. -/
theorem tangentCylinderProjection_apply (B : E →L[ℝ] F) (A : E →L[ℝ] T) (x : E) (t : T) :
    tangentCylinderProjection B A (x, t) = (B x, t + A x) := rfl

/-- A triangular map embeds the cylinder exactly when its normal
block embeds the normal source set.
See Cairns pp. 800--801 and M76 derivation 33. -/
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

/-- The normal and tangential blocks fix the product frame exactly
when BJ=I and AJ=0.
See Cairns pp. 800--801 and M76 derivation 33. -/
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

/-- A linear map fixing tangent vectors has the triangular form
determined by its normal-coordinate restriction.
See Cairns p. 800 and M76 derivation 33. -/
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

/-- A normalized product-frame projection fixes every tangent
direction, including when the normal source set is empty.
See Cairns p. 800 and M76 derivation 33. -/
theorem fixed_tangent_of_rightInverse_productFrame (J : F →L[ℝ] E)
    (Q : (E × T) →L[ℝ] (F × T))
    (hQ : Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) Q) (t : T) :
    Q (0, t) = (0, t) := by
  have he := hQ (0, t)
  change Q (J 0, t) = (0, t) at he
  simpa only [map_zero] using he

end ContinuousLinearMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/TangentCylinderSpace.lean
section

/-!
# Projection spaces of tangent cylinders

Normalized projections embedding a full cylinder split into normal
embeddings and a linear space of tangent shears vanishing on the
frame. This gives the operator-space part of Cairns' face-star
reduction, Section 4, pp. 800--801; see M76 derivation 33.
-/


open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Normalized operators embedding a prescribed source set.
See Cairns pp. 800--801 and M76 derivation 33. -/
abbrev FrameEmbeddingSpace (J : F →L[ℝ] E) (S : Set E) :=
  {B : E →L[ℝ] F // Function.RightInverse J B ∧ InjOn B S}

/-- Normalized operators embedding the entire tangent cylinder.
See Cairns pp. 800--801 and M76 derivation 33. -/
abbrev TangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :=
  {Q : (E × T) →L[ℝ] (F × T) //
    Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) Q ∧
      InjOn Q (S ×ˢ (univ : Set T))}

/-- Tangent shear operators vanishing on the specified normal frame.
See Cairns pp. 800--801 and M76 derivation 33. -/
noncomputable def frameShears (J : F →L[ℝ] E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :
    Submodule ℝ (E →L[ℝ] T) :=
  (J.precomp T : (E →L[ℝ] T) →L[ℝ] (F →L[ℝ] T)).ker

/-- Extract the normal operator and the tangent shear; the latter
vanishes on the fixed frame.
See Cairns pp. 800--801 and M76 derivation 33. -/
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

/-- The two operator factors reconstruct a normalized cylinder
embedding. See Cairns pp. 800--801 and M76 derivation 33. -/
def assembleTangentCylinder (J : F →L[ℝ] E) (S : Set E)
    (R : FrameEmbeddingSpace J S × J.frameShears T) :
    TangentCylinderEmbeddingSpace J S T :=
  ⟨tangentCylinderProjection R.1.val R.2.val,
    (rightInverse_tangentCylinderProjection_iff J R.1.val R.2.val).mpr
      ⟨R.1.property.1, R.2.property⟩,
    (injOn_tangentCylinderProjection_iff R.1.val R.2.val S).mpr R.1.property.2⟩

/-- The cylinder projection space is a product of its normal
projection space and the vector space of frame-vanishing shears.
See Cairns Section 4, pp. 800--801, and M76 derivation 33. -/
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

/-- A contractible normal projection space stays contractible after
adding tangent directions fixed by the frame normalization.
See Cairns Section 4, pp. 800--801, and M76 derivation 33. -/
theorem contractible_tangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    [ContractibleSpace (FrameEmbeddingSpace J S)] :
    ContractibleSpace (TangentCylinderEmbeddingSpace J S T) :=
  (tangentCylinderSpaceHomeomorph J S).contractibleSpace

end ContinuousLinearMap

end

-- Source: PoincareMT/Proofs/M76/Mathlib/FaceStarOperatorCoordinates.lean
section

/-!
# Normalized operators on actual face stars

Centered orthogonal coordinates identify operators embedding a
closed face star with operators embedding its exact normal cylinder.
This transfers the normal-times-shear decomposition in actual
operator topology. See Cairns 1940, pp. 800--801, and M76 derivation 38.
-/


open Set ContinuousLinearMap
open scoped Pointwise

namespace ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Changing linear coordinates and their center preserves
injectivity of an operator on the corresponding source set.
See Cairns p. 800 and M76 derivation 38. -/
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

/-- Include a normal coordinate frame together with all tangent
directions into the actual ambient Euclidean space.
See Cairns pp. 800--801 and M76 derivation 38. -/
noncomputable def frameWithTangent (L : Submodule ℝ E) (J : F →L[ℝ] ↥(Lᗮ)) :
    (F × L) →L[ℝ] E :=
  L.normalTangentEquiv.symm.toContinuousLinearMap.comp
    (J.prodMap (ContinuousLinearMap.id ℝ L))

/-- An independent normal frame stays independent after adjoining
the tangent directions. See Cairns p. 800 and M76 derivation 38. -/
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

/-- The normalized operator space of an actual nonempty face star
has exactly the coordinates of its full normal cylinder.
See Cairns Section 4, pp. 800--801, and M76 derivation 38. -/
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

/-- Contractibility of the actual normal embedding space transfers
to normalized operators on the original closed face star.
See Cairns pp. 800--801 and M76 derivation 38. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/CofaceFrames.lean
section

/-!
# Normal frames contained in actual coface directions

A normal vector to a central affine face remains in the direction
of every containing coface. Adjoining the tangent directions thus
gives the coface frames used for geometric plane coordinates.
See Cairns 1940, pp. 800--801, and M76 derivations 38--39.
-/


namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A subspace containing the normal frame and all tangent vectors
contains the full frame with tangent directions adjoined.
See Cairns pp. 800--801 and M76 derivation 39. -/
theorem frameWithTangent_range_le (L U : Submodule ℝ E) (J : F →L[ℝ] ↥(Lᗮ))
    (hL : L ≤ U) (hJ : ∀ z, (J z : E) ∈ U) : (L.frameWithTangent J).range ≤ U := by
  rintro x ⟨z, rfl⟩
  change (J z.1 : E) + (z.2 : E) ∈ U
  exact U.add_mem (hJ z.1) (hL z.2.property)

end Submodule

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Projecting normally to a central affine subspace keeps every
coface displacement in the coface direction space.
See Cairns pp. 800--801 and M76 derivation 39. -/
theorem normalAffineProjection_mem_direction (U V : AffineSubspace ℝ E)
    (hUV : U ≤ V) {p x : E} (hp : p ∈ U) (hx : x ∈ V) :
    (U.direction.normalAffineProjection p x : E) ∈ V.direction := by
  change U.directionᗮ.starProjection (x - p) ∈ V.direction
  rw [U.direction.starProjection_orthogonal_val]
  exact V.direction.sub_mem (V.vsub_mem_direction hx (hUV hp))
    (direction_le hUV (U.direction.starProjection_apply_mem (x - p)))

/-- The normal line through a coface vertex, together with the
central tangent space, lies in that actual coface direction space.
See Cairns pp. 800--801 and M76 derivation 39. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/TangentCylinderBound.lean
section

/-!
# Uniform secant bounds on tangent cylinders

A lower secant bound on the normal projection gives a uniform
positive lower bound on the entire tangent cylinder, despite its
unbounded tangent directions. See Cairns 1940, pp. 799--801,
and M76 derivation 36.
-/


open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- A triangular tangent-cylinder projection has a uniform positive
secant bound whenever its normal block does. The tangent factor is
unbounded. See Cairns pp. 799--801 and M76 derivation 36. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/CenteredSecantBounds.lean
section

/-!
# Quantitative projection bounds after centered coordinates

A uniform lower secant bound transfers through a continuous linear
coordinate equivalence, with an explicit adjustment for its inverse
operator norm. Centers cancel from secants. See Cairns 1940,
pp. 799--801, and M76 derivation 38.
-/


open Set

namespace ContinuousLinearEquiv

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A positive bound on centered coordinate secants transfers to
the original ambient norm. The inverse-norm denominator includes one
so the formula also handles zero-dimensional spaces.
See Cairns pp. 799--801 and M76 derivation 38. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/IndependentSecantBound.lean
section

/-!
# Uniform secant bounds in the actual span of independent vertices

An independent family is a basis of its own span. The subtype
inclusion preserves norms, so the checked basis-cone estimate
applies in any larger ambient normed space. See Cairns 1940,
pp. 799--800, and M76 derivations 27 and 38.
-/


open Set

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Injectivity on a finite union of independent cone simplices
gives a uniform positive secant bound in the original ambient norm.
The independent vertices need not span the ambient space.
See Cairns p. 799 and M76 derivation 38. -/
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

/-- Every injective projection of a full independent radial cone
has a uniform positive secant bound, even in a larger ambient space.
See Cairns pp. 799--800 and M76 derivation 38. -/
theorem RadialEmbedding.exists_pos_secant_bound_of_linearIndependent
    {A : AbstractSimplicialComplex ι} (v : A.RadialEmbedding E)
    (hv : LinearIndependent ℝ v.val) (Q : E →L[ℝ] F) (hQ : InjOn Q v.cone.space) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ v.cone.space, ∀ y ∈ v.cone.space,
      c * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  rw [RadialEmbedding.cone_space] at hQ ⊢
  exact hv.exists_pos_secant_bound_of_injOn (insert ∅ A.faces) Q hQ

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/FaceStarSecantBound.lean
section

/-!
# Geometric secant bounds for actual face-star projections

General position makes the actual normal-link vertices independent.
The quantitative normal-cone bound, cylinder formula, and centered
coordinate estimate therefore give geometric transversality for
every normalized embedding of the original face star. See Cairns
1940, pp. 799--801, and M76 derivation 38.
-/


open Set ContinuousLinearMap AbstractSimplicialComplex
open scoped Pointwise

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every frame-normalized embedding of a general-position closed
face star has a uniform positive lower secant bound in the original
ambient Euclidean norm. See Cairns pp. 799--801 and M76 derivation 38. -/
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

/-- For normalized face-star projections, plain injectivity is
equivalent to geometric secant transversality of the actual kernel.
See Cairns pp. 799--801 and M76 derivation 38. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/FaceStarPlaneCoordinates.lean
section

/-!
# Geometric plane coordinates for actual face stars

Kernel coordinates identify actual transverse complementary planes
with normalized face-star embeddings. A frame contained in the
direction of a coface is automatically complementary to every
transverse plane of the required dimension. See Cairns 1940,
pp. 800--801, and M76 derivation 38.
-/


open Set ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Combine the frame and carrier-embedding predicates into one
operator subtype, retaining its original topology.
See Cairns p. 801 and M76 derivation 38. -/
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

/-- Actual transverse planes complementary to a normal-plus-tangent
frame have exactly the normalized embedding-operator coordinates.
Both sides use their geometric or operator subspace topology.
See Cairns pp. 800--801 and M76 derivation 38. -/
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

/-- Normal embedding-space contractibility transfers to actual
geometric transverse planes complementary to the chosen frame.
See Cairns pp. 800--801 and M76 derivation 38. -/
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

/-- If the normal-plus-tangent frame lies in one actual coface,
the full geometric transverse-plane space of complementary dimension
is contractible whenever the normal embedding space is contractible.
Frame complementarity is derived from the coface and dimension.
See Cairns pp. 800--801 and M76 derivation 38. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/AmbientBasisTransversePlanes.lean
section

/-!
# Transverse-plane coordinates for a star in a larger ambient space

The radial condition on an operator's restriction to the source span
is precisely geometric transversality of its ambient kernel to the
included full star. Face-span disjointness and the normalized frame
correspondence persist in the larger ambient space.
See Cairns 1940, pp. 800--801, and M76 derivation 32.
-/


open Set Geometry

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Intersecting an ambient transverse plane with the source subspace
preserves geometric transversality in the inherited inner product.
See Cairns Section 4(A), p. 800, and M76 derivation 32. -/
theorem IsSecantTransverse.comap_subtype {K V : Submodule ℝ E} {S : Set V}
    (hK : K.IsSecantTransverse (V.subtype '' S)) :
    (K.comap V.subtype).IsSecantTransverse S := by
  let Q := (ContinuousLinearMap.id ℝ E - K.starProjection).comp V.subtypeL
  have hker : Q.ker = K.comap V.subtype := by
    ext x
    change ((x : E) - K.starProjection (x : E) = 0) ↔ (x : E) ∈ K
    rw [sub_eq_zero, eq_comm, K.starProjection_eq_self_iff]
  obtain ⟨c, hc, hb⟩ := hK
  rw [← hker]
  apply isSecantTransverse_ker_of_lower_bound Q hc
  intro x hx y hy
  rw [← map_sub]
  exact hb (x : E) ⟨x, hx, rfl⟩ (y : E) ⟨y, hy, rfl⟩

end Submodule

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [Finite ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The radial restriction predicate is exactly the geometric kernel
condition on the included full basis star.
See Cairns pp. 800--801 and M76 derivation 32. -/
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

/-- An ambient transverse plane misses the included span of each
source face. See Cairns pp. 799--801 and M76 derivation 32. -/
theorem disjoint_map_faceSpan_of_isSecantTransverse
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) {s : Finset ι} (hs : s ∈ A.faces)
    {K : Submodule ℝ E}
    (hK : K.IsSecantTransverse (V.subtype '' (A.basisRadialEmbedding b).cone.space)) :
    Disjoint ((Submodule.span ℝ (b '' (s : Set ι))).map V.subtype) K := by
  have hd := A.disjoint_faceSpan_of_isSecantTransverse b hs hK.comap_subtype
  apply Submodule.disjoint_def.mpr
  intro x hx hk
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
  have hz := Submodule.disjoint_def.mp hd v hv hk
  exact congrArg Subtype.val hz

/-- The radial restriction predicate is also equivalent to plain
injectivity on the included full basis star.
See Cairns pp. 799--801 and M76 derivation 32. -/
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

/-- Frame-normalized projection coordinates for geometric transverse
planes when the star spans only a subspace of the ambient space.
See Cairns Lemmas 5.1--5.2, p. 801, and M76 derivation 32. -/
noncomputable def frameAmbientBasisPlaneHomeomorph
    (A : AbstractSimplicialComplex ι) (V : Submodule ℝ E)
    (b : Module.Basis ι ℝ V) (J : F →L[ℝ] V) (hJ : Function.Injective J) :
    (V.subtypeL.comp J).range.TransverseComplementPlaneSpace
      (V.subtype '' (A.basisRadialEmbedding b).cone.space) ≃ₜ
      {Q : (V.subtypeL.comp J).FrameProjectionSpace //
        A.IsRadialEmbedding (fun i => Q.val (b i))} := by
  let J' : F →L[ℝ] E := V.subtypeL.comp J
  have hJ' : Function.Injective J' := fun x y h => hJ (Subtype.val_injective h)
  refine (J'.frameComplementPlaneHomeomorph hJ').subtype ?_
  intro K
  rw [A.isRadialEmbedding_iff_isSecantTransverse_ker_subtype,
    J'.ker_frameComplementPlaneHomeomorph hJ' K]

end AbstractSimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Mathlib/OrthogonalOperatorSplit.lean
section

/-!
# Ambient operator extension across an orthogonal complement

Restriction to a subspace and its orthogonal complement gives a
homeomorphism on continuous linear operator spaces. Constraints on
the first restriction leave an unrestricted, contractible second
factor. See Cairns 1940, Lemma 5.2, p. 801, and M76 derivation 32.
-/


namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Operators are continuously determined by their restrictions to
an orthogonal pair of complementary subspaces.
See Cairns p. 801 and M76 derivation 32. -/
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

/-- Any constraint on the source-subspace restriction leaves the
orthogonal-complement operator completely free.
See Cairns Lemma 5.2, p. 801, and M76 derivation 32. -/
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

/-- A contractible space of operators on a subspace remains
contractible after extending the operators to a larger ambient space.
See Cairns Lemma 5.2, p. 801, and M76 derivation 32. -/
theorem contractible_operatorRestriction (V : Submodule ℝ E)
    (p : (V →L[ℝ] F) → Prop) [ContractibleSpace {R : V →L[ℝ] F // p R}] :
    ContractibleSpace {Q : E →L[ℝ] F // p (Q.comp V.subtypeL)} :=
  (V.operatorRestrictionHomeomorph p).contractibleSpace

end Submodule

end

-- Source: PoincareMT/Proofs/M76/Mathlib/PlanarRadialArc.lean
section

/-!
# Central projection of a straight planar edge

The segment from one to a unit vector at angle theta in (0, pi)
projects exactly to the short circle arc with angles in [0, theta].
See Cairns 1940, Section 6, p. 802 and M76 derivation 21.
-/


open Set NormedSpace

namespace Complex

/-- The endpoints of a short positively oriented circle arc are
independent as real position vectors. See Cairns p. 802 and M76 derivation 21. -/
theorem linearIndependent_one_circleExp {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    LinearIndependent ℝ ((↑) : ↥({(1 : ℂ), (Circle.exp theta : ℂ)} : Set ℂ) → ℂ) := by
  change LinearIndepOn ℝ id {(1 : ℂ), (Circle.exp theta : ℂ)}
  apply linearIndepOn_id_pair one_ne_zero
  intro a ha
  have hi := congrArg Complex.im ha
  have hsin := Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2
  simp only [smul_im, one_im, smul_zero, Circle.coe_exp, exp_ofReal_mul_I_im] at hi
  linarith

/-- Rotated imaginary part in polar coordinates. See the planar cone
calculation in Cairns p. 802 and M76 derivation 21. -/
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

/-- Two oriented half-plane bounds put a nonzero vector's argument
in the short angular interval. See Cairns p. 802 and M76 derivation 21. -/
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

/-- The straight edge for a short arc stays in the principal argument's
continuity domain. See Cairns p. 802 and M76 derivation 21. -/
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

/-- Every projected edge direction lies between its endpoint angles.
See Cairns p. 802 and M76 derivation 21. -/
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

/-- The arguments of all points of the straight edge fill the entire
short angular interval. See Cairns p. 802 and M76 derivation 21. -/
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

/-- Normalizing a nonzero complex number gives its unit argument vector.
See Cairns' central projection on p. 802 and M76 derivation 21. -/
theorem normalize_eq_circleExp_arg {z : ℂ} (hz : z ≠ 0) :
    NormedSpace.normalize z = (Circle.exp z.arg : ℂ) := by
  have hpolar : ‖z‖ • (Circle.exp z.arg : ℂ) = z := by
    simpa only [Circle.coe_exp, real_smul] using norm_mul_exp_arg_mul_I z
  calc
    NormedSpace.normalize z = ‖z‖⁻¹ • (‖z‖ • (Circle.exp z.arg : ℂ)) :=
      congrArg (fun x : ℂ => ‖z‖⁻¹ • x) hpolar.symm
    _ = (Circle.exp z.arg : ℂ) := inv_smul_smul₀ (norm_ne_zero_iff.mpr hz) _

/-- Central projection of the straight edge is exactly the short unit
circle arc, with both endpoints included. See Cairns p. 802 and
M76 derivation 21. -/
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

/-- Unit rotations commute with central projection, including at zero.
See Cairns p. 802 and M76 derivation 21. -/
theorem normalize_circle_mul (a : Circle) (z : ℂ) :
    NormedSpace.normalize ((a : ℂ) * z) = (a : ℂ) * NormedSpace.normalize z := by
  simp only [NormedSpace.normalize, norm_mul, Circle.norm_coe, one_mul, mul_smul_comm]

/-- A short edge with arbitrary lifted endpoint angles is a rotation of
the edge based at one. See Cairns p. 802 and M76 derivation 21. -/
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

/-- Distinct endpoints of any positively oriented arc shorter than a
half-turn are independent as real position vectors. The lifted angles
may cross the argument cut. See Cairns p. 802 and M76 derivation 21. -/
theorem linearIndependent_circleExp_pair {a b : ℝ} (hab : a < b) (hba : b - a < Real.pi) :
    LinearIndependent ℝ ((↑) : ↥({(Circle.exp a : ℂ), (Circle.exp b : ℂ)} : Set ℂ) → ℂ) := by
  change LinearIndepOn ℝ id ({(Circle.exp a : ℂ), (Circle.exp b : ℂ)} : Set ℂ)
  have h : LinearIndepOn ℝ id ({(1 : ℂ), (Circle.exp (b - a) : ℂ)} : Set ℂ) :=
    linearIndependent_one_circleExp ⟨sub_pos.mpr hab, hba⟩
  have hr := h.id_imageₛ (f := (rotation (Circle.exp a)).toLinearEquiv.toLinearMap)
    (rotation (Circle.exp a)).injective.injOn
  simpa only [image_pair, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    rotation_apply, mul_one, ← Circle.coe_mul, ← Circle.exp_add, add_sub_cancel] using hr

/-- Central projection of an arbitrary short straight circle edge is
the closed short arc between its lifted angles. This statement also
covers arcs crossing the argument cut. See Cairns p. 802 and
M76 derivation 21. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/PlanarNoBacktracking.lean
section

/-!
# No reversal of adjacent projected planar edges

Two consecutive short straight edges cannot turn back along the circle
when neither outer vertex belongs to the other edge's spherical image.
This is the local cyclic-order argument in Cairns 1940, Section 6,
p. 802; see M76 derivation 23.
-/


open Set NormedSpace

namespace Complex

/-- Nonincident vertex directions prohibit reversal along two adjacent
short edges. The angles are arbitrary real lifts.
See Cairns p. 802 and M76 derivation 23. -/
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

/-- The signed short angular increment between two unit vertices.
See Cairns p. 802 and M76 derivation 23. -/
noncomputable def shortIncrement (x y : Circle) : ℝ := Complex.arg (y / x : Circle)

/-- The signed increment recovers the second circle vertex by rotation.
See Cairns p. 802 and M76 derivation 23. -/
theorem mul_exp_shortIncrement (x y : Circle) : x * Circle.exp (shortIncrement x y) = y := by
  rw [shortIncrement, Circle.exp_arg]
  exact mul_div_cancel _ _

/-- The principal angular increment is strictly larger than minus pi.
See Cairns p. 802 and M76 derivation 23. -/
theorem neg_pi_lt_shortIncrement (x y : Circle) : -Real.pi < shortIncrement x y :=
  Complex.neg_pi_lt_arg _

/-- Independent endpoint vectors exclude the antipodal value of the
principal increment. See Cairns p. 802 and M76 derivation 23. -/
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

/-- Distinct unit vertices have a nonzero signed angular increment.
See Cairns p. 802 and M76 derivation 23. -/
theorem shortIncrement_ne_zero {x y : Circle} (hxy : x ≠ y) : shortIncrement x y ≠ 0 := by
  intro hzero
  have he := mul_exp_shortIncrement x y
  rw [hzero, Circle.exp_zero, mul_one] at he
  exact hxy he

end Circle

end

-- Source: PoincareMT/Proofs/M76/Mathlib/RadialEmbeddingIncidence.lean
section

/-!
# Vertex incidence after radial projection

For a faithful radial realization, a vertex direction belongs to a
projected face exactly when the corresponding label belongs to that
face. This is used to recover cyclic order of planar links in Cairns
1940, Section 6, p. 802; see M76 derivation 23.
-/


open Set Geometry NormedSpace

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι} {v : ι → E}

/-- Position vectors of every labelled face are independent in a
faithful radial realization. See Cairns p. 802 and M76 derivation 23. -/
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

/-- Radial projection preserves exact vertex-face incidence.
No unit-norm or finiteness assumption is needed.
See Cairns p. 802 and M76 derivation 23. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/SimplicialGenerators.lean
section

/-!
# Simplicial complexes generated by compatible simplices

A family of independent simplices satisfying the geometric intersection
law generates a complex by adjoining all nonempty subfaces. Its carrier
is the union of the generating simplices. This is used for the straight
planar links in Cairns 1940, Section 6, p. 802; see M76 derivation 22.
-/


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

/-- Adjoin all nonempty subfaces of a compatible family of simplices.
The generators need not be maximal, nonempty, or distinct. See Cairns
p. 802 and M76 derivation 22. -/
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

/-- The generated faces are exactly the nonempty subfaces of generators.
See Cairns p. 802 and M76 derivation 22. -/
theorem mem_ofGenerators_faces
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) (s : Finset E) :
    s ∈ (ofGenerators F hind hinter).faces ↔ s.Nonempty ∧ ∃ S ∈ F, s ⊆ S := Iff.rfl

/-- Adding subfaces does not change the union of the generating convex
hulls, even for an empty family or empty generators.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- Finitely many generating simplices produce finitely many faces.
See the finite planar links of Cairns p. 802 and M76 derivation 22. -/
theorem finite_ofGenerators_faces (hF : F.Finite)
    (hind : ∀ S ∈ F, AffineIndependent 𝕜 ((↑) : S → E))
    (hinter : ∀ S ∈ F, ∀ T ∈ F, convexHull 𝕜 (S : Set E) ∩ convexHull 𝕜 (T : Set E) ⊆
      convexHull 𝕜 ((S : Set E) ∩ T)) :
    (ofGenerators F hind hinter).faces.Finite := by
  classical
  apply (hF.biUnion (fun S _ => S.powerset.finite_toSet)).subset
  rintro s ⟨_, S, hS, hsS⟩
  exact mem_iUnion₂.mpr ⟨S, hS, Finset.mem_powerset.mpr hsS⟩

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Smoothing/CircleGapConfigurations.lean
section

/-!
# Angular-gap configurations for normalized circle triangulations

Positive cyclic gaps shorter than a semicircle, with total angle two pi and
a prescribed first gap, form a nonempty convex and hence contractible space.
These are the coordinate conditions for the circle-triangulation step in
Cairns 1940, Section 6, p. 802, and Lemma 11.1, p. 807, footnote 14.
See M76 derivation 13. The geometric correspondence with Brouwer-star
transverse-plane spaces is a separate obligation.
-/


open Set

namespace PoincareMT.M76.Smoothing

/-- Cyclic short-arc gap coordinates for n+3 vertices, with the first two
marked vertices separated by `theta`. See Cairns pp. 802, 807 and
M76 derivation 13. -/
def shortArcGapSpace (n : ℕ) (theta : ℝ) : Set (Fin (n + 3) → ℝ) :=
  {w | (∀ i, w i ∈ Ioo (0 : ℝ) Real.pi) ∧
    (∑ i, w i) = 2 * Real.pi ∧ w 0 = theta}

/-- The angular-gap constraints are convex, so linear interpolation preserves
them. This is the coordinate calculation behind Cairns p. 807, footnote 14;
see M76 derivation 13. -/
theorem convex_shortArcGapSpace (n : ℕ) (theta : ℝ) :
    Convex ℝ (shortArcGapSpace n theta) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact (convex_Ioo (0 : ℝ) Real.pi) (hx.1 i) (hy.1 i) ha hb hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2.1, hy.2.1, ← add_mul, hab, one_mul]
  · change a * x 0 + b * y 0 = theta
    rw [hx.2.2, hy.2.2, ← add_mul, hab, one_mul]

/-- Equal gaps on the complementary arc give a configuration for every
admissible first gap. See Cairns p. 807, footnote 14 and M76 derivation 13. -/
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

/-- The normalized short-arc coordinate space is contractible. The geometric
identification with Cairns' T(r^1) is separate; see p. 807, footnote 14 and
M76 derivation 13. -/
theorem contractible_shortArcGapSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (shortArcGapSpace n theta) :=
  (convex_shortArcGapSpace n theta).contractibleSpace (nonempty_shortArcGapSpace n htheta)

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/CircleGapVertices.lean
section

/-!
# Circle vertices recovered from angular gaps

Prefix sums of positive cyclic gaps give distinct, continuously varying
vertices of the additive circle, with the first marked edge fixed. This is
the angular-coordinate step for Cairns 1940, Section 6, p. 802, and
Lemma 11.1, p. 807, footnote 14. See M76 derivation 13.
-/


open Set

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- The real angle of a vertex is the sum of preceding cyclic gaps.
See Cairns p. 802 and M76 derivation 13. -/
def gapAngle (w : Fin (n + 3) → ℝ) (i : Fin (n + 3)) : ℝ :=
  ∑ j ∈ Finset.Iio i, w j

/-- The first vertex is at angle zero. See M76 derivation 13. -/
@[simp] theorem gapAngle_zero (w : Fin (n + 3) → ℝ) : gapAngle w 0 = 0 := by
  change (∑ j ∈ Finset.Iio (⊥ : Fin (n + 3)), w j) = 0
  rw [Finset.Iio_bot, Finset.sum_empty]

/-- Consecutive lifted angles differ by their intervening gap.
See Cairns p. 802 and M76 derivation 13. -/
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

/-- Positive gaps give strictly ordered lifted vertex angles.
See Cairns p. 802 and M76 derivation 13. -/
theorem strictMono_gapAngle {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    StrictMono (gapAngle w) := by
  intro i j hij
  apply Finset.sum_lt_sum_of_subset
    (fun k hk => Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hk).trans hij))
    (Finset.mem_Iio.mpr hij) (by simp) (hw.1 i).1
  intro k _ _
  exact (hw.1 k).1.le

/-- Every lifted vertex angle lies in one fundamental interval, with a
strict upper bound even at the final vertex. See M76 derivation 13. -/
theorem gapAngle_mem_Ico {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta)
    (i : Fin (n + 3)) : gapAngle w i ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  refine ⟨Finset.sum_nonneg (fun j _ => (hw.1 j).1.le), ?_⟩
  calc
    gapAngle w i < ∑ j, w j :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ i)
        (by simp) (hw.1 i).1 (fun j _ _ => (hw.1 j).1.le)
    _ = 2 * Real.pi := hw.2.1

/-- The second marked vertex is at the prescribed angle.
See Cairns p. 802 and M76 derivation 13. -/
theorem gapAngle_one {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    gapAngle w 1 = theta := by
  have h := gapAngle_succ w (0 : Fin (n + 2))
  simpa [hw.2.2] using h

/-- Lifted vertex angles depend continuously on the gap coordinates.
See M76 derivation 13. -/
theorem continuous_gapAngle (i : Fin (n + 3)) :
    Continuous (fun w : Fin (n + 3) → ℝ => gapAngle w i) :=
  continuous_finsetSum _ fun j _ => continuous_apply j

/-- The cyclic vertices in the circle of circumference two pi.
See Cairns p. 802 and M76 derivation 13. -/
noncomputable def circleGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    AddCircle (2 * Real.pi) := (gapAngle w i : AddCircle (2 * Real.pi))

/-- The recovered circle vertices are pairwise distinct. Reduction modulo
two pi cannot identify two lifted angles in the fundamental interval.
See M76 derivation 13. -/
theorem injective_circleGapVertices (w : shortArcGapSpace n theta) :
    Function.Injective (circleGapVertices w) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro i j hij
  apply (strictMono_gapAngle w.property).injective
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
    (by simpa using gapAngle_mem_Ico w.property i)
    (by simpa using gapAngle_mem_Ico w.property j)).mp hij

/-- The circle vertices move continuously with the angular-gap parameters.
See Cairns p. 802 and M76 derivation 13. -/
theorem continuous_circleGapVertices :
    Continuous (circleGapVertices : shortArcGapSpace n theta → Fin (n + 3) →
      AddCircle (2 * Real.pi)) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (2 * Real.pi)).comp
    ((continuous_gapAngle i).comp continuous_subtype_val)

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/CircleAngleCoordinates.lean
section

/-!
# Inverse coordinates for circle configurations

Prefix sums identify normalized short-arc gaps with normalized lifted
angles. Both directions are continuous. This supplies the real-coordinate
part of Cairns 1940, Section 6, p. 802, and p. 807, footnote 14.
See M76 derivation 15 for normalization and empty-space cases.
-/


open Set

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- Normalized lifted angles for a labelled short-arc circle subdivision.
The final inequality controls the closing edge. See Cairns p. 802 and
M76 derivation 15. -/
def shortArcAngleSpace (n : ℕ) (theta : ℝ) : Set (Fin (n + 3) → ℝ) :=
  {a | a 0 = 0 ∧ a 1 = theta ∧
    (∀ i : Fin (n + 2), a i.succ - a i.castSucc ∈ Ioo (0 : ℝ) Real.pi) ∧
    2 * Real.pi - a (Fin.last (n + 2)) ∈ Ioo (0 : ℝ) Real.pi}

/-- Consecutive differences recover the gaps, with a full-turn endpoint
for the closing edge. See Cairns p. 802 and M76 derivation 15. -/
noncomputable def angleGaps (a : Fin (n + 3) → ℝ) : Fin (n + 3) → ℝ :=
  Fin.lastCases (2 * Real.pi - a (Fin.last (n + 2)))
    (fun i => a i.succ - a i.castSucc)

/-- The last prefix sum and the closing gap give the total angle.
See M76 derivation 15. -/
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

/-- Taking consecutive differences undoes prefix sums when the total
angle is one full turn. See M76 derivation 15. -/
theorem angleGaps_gapAngle (w : Fin (n + 3) → ℝ) (hw : (∑ i, w i) = 2 * Real.pi) :
    angleGaps (gapAngle w) = w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [angleGaps, Fin.lastCases_last]
    linarith [gapAngle_last_add w]
  · simp [angleGaps, gapAngle_succ]

/-- Prefix sums of consecutive differences recover all angles relative
to the first. See M76 derivation 15. -/
theorem gapAngle_angleGaps (a : Fin (n + 3) → ℝ) (i : Fin (n + 3)) :
    gapAngle (angleGaps a) i = a i - a 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      rw [gapAngle_succ, ih]
      simp only [angleGaps, Fin.lastCases_castSucc]
      ring

/-- The sum of all recovered gaps is the full turn minus the first
angle. See M76 derivation 15. -/
theorem sum_angleGaps (a : Fin (n + 3) → ℝ) :
    (∑ i, angleGaps a i) = 2 * Real.pi - a 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [angleGaps, Fin.lastCases_castSucc, Fin.lastCases_last,
    Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ a
  have hlast := Fin.sum_univ_castSucc a
  linarith

/-- Normalized gaps yield normalized lifted angles.
See Cairns p. 802 and M76 derivation 15. -/
theorem gapAngle_mem_shortArcAngleSpace {w : Fin (n + 3) → ℝ}
    (hw : w ∈ shortArcGapSpace n theta) : gapAngle w ∈ shortArcAngleSpace n theta := by
  refine ⟨gapAngle_zero w, gapAngle_one hw, ?_, ?_⟩
  · intro i
    simpa [gapAngle_succ] using hw.1 i.castSucc
  · have hlast : 2 * Real.pi - gapAngle w (Fin.last (n + 2)) =
        w (Fin.last (n + 2)) := by linarith [gapAngle_last_add w, hw.2.1]
    rw [hlast]
    exact hw.1 _

/-- Normalized lifted angles yield normalized short-arc gaps.
See Cairns p. 802 and M76 derivation 15. -/
theorem angleGaps_mem_shortArcGapSpace {a : Fin (n + 3) → ℝ}
    (ha : a ∈ shortArcAngleSpace n theta) : angleGaps a ∈ shortArcGapSpace n theta := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [angleGaps, Fin.lastCases_last] using ha.2.2.2
    · simpa only [angleGaps, Fin.lastCases_castSucc] using ha.2.2.1 j
  · rw [sum_angleGaps, ha.1, sub_zero]
  · change angleGaps a (Fin.castSucc (0 : Fin (n + 2))) = theta
    rw [angleGaps, Fin.lastCases_castSucc]
    simpa using sub_eq_iff_eq_add.mpr (show a 1 = theta + a 0 by rw [ha.1, ha.2.1, add_zero])

/-- The difference map is continuous, including the closing coordinate.
See M76 derivation 15. -/
theorem continuous_angleGaps :
    Continuous (angleGaps : (Fin (n + 3) → ℝ) → Fin (n + 3) → ℝ) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [angleGaps, Fin.lastCases_last]
    exact continuous_const.sub (continuous_apply _)
  · simp only [angleGaps, Fin.lastCases_castSucc]
    exact (continuous_apply _).sub (continuous_apply _)

/-- Gap coordinates and lifted-angle coordinates have the same topology.
See Cairns p. 802 and M76 derivation 15. -/
noncomputable def gapAngleHomeomorph (n : ℕ) (theta : ℝ) :
    shortArcGapSpace n theta ≃ₜ shortArcAngleSpace n theta where
  toFun w := ⟨gapAngle w, gapAngle_mem_shortArcAngleSpace w.property⟩
  invFun a := ⟨angleGaps a, angleGaps_mem_shortArcGapSpace a.property⟩
  left_inv w := by
    apply Subtype.ext
    exact angleGaps_gapAngle w.val w.property.2.1
  right_inv a := Subtype.ext (funext fun i => by
    change gapAngle (angleGaps a.val) i = a.val i
    rw [gapAngle_angleGaps, a.property.1, sub_zero])
  continuous_toFun := (continuous_pi (fun i =>
    (continuous_gapAngle i).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (continuous_angleGaps.comp continuous_subtype_val).subtype_mk _

/-- The inequalities defining lifted angles force strict order.
See Cairns p. 802 and M76 derivation 15. -/
theorem strictMono_shortArcAngles {a : Fin (n + 3) → ℝ}
    (ha : a ∈ shortArcAngleSpace n theta) : StrictMono a := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact sub_pos.mp (ha.2.2.1 i).1

/-- Every normalized lifted vertex is in the fundamental interval.
See M76 derivation 15. -/
theorem shortArcAngles_mem_Ico {a : Fin (n + 3) → ℝ}
    (ha : a ∈ shortArcAngleSpace n theta) (i : Fin (n + 3)) :
    a i ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  have hmono := (strictMono_shortArcAngles ha).monotone
  constructor
  · simpa [ha.1] using hmono (Fin.zero_le i)
  · have hle := hmono (Fin.le_last i)
    linarith [ha.2.2.2.1]

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Mathlib/ShortCircleArc.lean
section

/-!
# Short arcs of an additive circle

An interval of length at most half the period embeds isometrically in the
additive circle and is homeomorphic to its image. This is the elementary
short-geodesic fact used in Cairns 1940, Section 6, p. 802.
See M76 derivation 15. Empty intervals are allowed.
-/


open Set

namespace AddCircle

variable {p a b : ℝ}

/-- The quotient onto a circle preserves distances on any interval of
length at most half the positive period. See Cairns p. 802 and
M76 derivation 15. -/
theorem isometry_coe_shortInterval (hp : 0 < p) (hab : b - a ≤ p / 2) :
    Isometry (fun x : Icc a b => (x.val : AddCircle p)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, Subtype.dist_eq, Real.dist_eq]
  apply (norm_coe_eq_abs_iff p hp.ne').mpr
  rw [abs_of_pos hp, abs_le]
  constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]

/-- A closed interval shorter than half the period has no quotient
identifications. See Cairns p. 802 and M76 derivation 15. -/
theorem injOn_coe_shortInterval (hp : 0 < p) (hab : b - a ≤ p / 2) :
    InjOn (fun x : ℝ => (x : AddCircle p)) (Icc a b) := by
  intro x hx y hy hxy
  exact congrArg Subtype.val
    ((isometry_coe_shortInterval hp hab).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

/-- A short closed arc has its usual interval topology. The forward map
is reduction modulo the period. See Cairns p. 802 and M76 derivation 15. -/
noncomputable def shortArcHomeomorph (hp : 0 < p) (hab : b - a ≤ p / 2) :
    Icc a b ≃ₜ (fun x : ℝ => (x : AddCircle p)) '' Icc a b :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn _ _ (injOn_coe_shortInterval hp hab))
    ((AddCircle.continuous_mk' p).comp continuous_subtype_val |>.subtype_mk _)

/-- The short-arc homeomorphism is the usual quotient map.
See M76 derivation 15. -/
theorem shortArcHomeomorph_apply (hp : 0 < p) (hab : b - a ≤ p / 2) (x : Icc a b) :
    (shortArcHomeomorph hp hab x : AddCircle p) = (x.val : AddCircle p) := rfl

end AddCircle

end

-- Source: PoincareMT/Proofs/M76/Smoothing/CircleSubdivision.lean
section

/-!
# Short-arc circle subdivisions from gap coordinates

Normalized gap data give embedded geodesic arcs covering the circle with
pairwise disjoint interiors. This verifies the one-dimensional geodesic
subdivision underlying Cairns 1940, Section 6, p. 802, and the configuration
space on p. 807. See M76 derivation 15.
-/


open Set

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- The closed arc beginning at the vertex indexed by `i`.
See Cairns p. 802 and M76 derivation 15. -/
def circleGapArc (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Set (AddCircle (2 * Real.pi)) :=
  (fun x : ℝ => (x : AddCircle (2 * Real.pi))) '' Icc (gapAngle w i) (gapAngle w i + w.val i)

/-- The open part of a gap arc, excluding its two vertices.
See Cairns p. 802 and M76 derivation 15. -/
def circleGapArcInterior (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Set (AddCircle (2 * Real.pi)) :=
  (fun x : ℝ => (x : AddCircle (2 * Real.pi))) '' Ioo (gapAngle w i) (gapAngle w i + w.val i)

/-- The lifted end of any edge is at most one full turn.
See M76 derivation 15. -/
theorem gapAngle_add_le_fullTurn (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    gapAngle w i + w.val i ≤ 2 * Real.pi := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (gapAngle_last_add w.val).trans w.property.2.1 |>.le
  · rw [← gapAngle_succ]
    exact (gapAngle_mem_Ico w.property j.succ).2.le

/-- An edge ends before any later vertex. See M76 derivation 15. -/
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

/-- Every real angle in the full turn belongs to at least one edge
interval, including both terminal endpoints. See M76 derivation 15. -/
theorem exists_gapAngle_interval (w : shortArcGapSpace n theta) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    ∃ i, x ∈ Icc (gapAngle w i) (gapAngle w i + w.val i) := by
  classical
  let s : Finset (Fin (n + 3)) := Finset.univ.filter (fun i => gapAngle w i ≤ x)
  have hs : s.Nonempty := ⟨0, by simp [s, hx.1]⟩
  let i := s.max' hs
  have himem : i ∈ s := Finset.max'_mem _ _
  refine ⟨i, (Finset.mem_filter.mp himem).2, ?_⟩
  by_cases hilast : i = Fin.last (n + 2)
  · rw [hilast, gapAngle_last_add, w.property.2.1]
    exact hx.2
  · have hi : i.val < n + 2 := by
      have hil := i.isLt
      have hine : i.val ≠ n + 2 := fun h => hilast (Fin.ext h)
      omega
    let j : Fin (n + 2) := ⟨i.val, hi⟩
    have hji : j.castSucc = i := Fin.ext rfl
    have hnot : j.succ ∉ s := by
      intro hmem
      have hle : j.succ ≤ i := Finset.le_max' _ _ hmem
      change j.val + 1 ≤ i.val at hle
      dsimp [j] at hle
      omega
    have hxj : x < gapAngle w j.succ := by
      apply lt_of_not_ge
      intro hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
    rw [gapAngle_succ, hji] at hxj
    exact hxj.le

/-- The closed short arcs cover the entire circle.
See Cairns p. 802 and M76 derivation 15. -/
theorem iUnion_circleGapArc (w : shortArcGapSpace n theta) :
    ⋃ i, circleGapArc w i = univ := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  apply eq_univ_iff_forall.mpr
  intro z
  obtain ⟨x, hx, hxz⟩ := AddCircle.eq_coe_Ico z
  obtain ⟨i, hi⟩ := exists_gapAngle_interval w (Ico_subset_Icc_self hx)
  exact mem_iUnion.mpr ⟨i, ⟨x, hi, hxz⟩⟩

/-- The interiors of distinct arcs do not overlap. No identification
across the branch cut occurs in an arc interior. See M76 derivation 15. -/
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

/-- Each gap interval embeds isometrically into the circle, so the arc
has its short-geodesic parametrization. See Cairns p. 802 and M76 derivation 15. -/
theorem isometry_circleGapArc (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Isometry (fun x : Icc (gapAngle w i) (gapAngle w i + w.val i) =>
      (x.val : AddCircle (2 * Real.pi))) :=
  AddCircle.isometry_coe_shortInterval (by positivity) (by linarith [(w.property.1 i).2])

/-- The short arc is homeomorphic to its lifted interval.
See Cairns p. 802 and M76 derivation 15. -/
noncomputable def circleGapArcHomeomorph (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    Icc (gapAngle w i) (gapAngle w i + w.val i) ≃ₜ circleGapArc w i :=
  AddCircle.shortArcHomeomorph (by positivity) (by linarith [(w.property.1 i).2])

/-- The upper endpoint of an arc is the next cyclic vertex, including
the closing edge. See Cairns p. 802 and M76 derivation 15. -/
theorem circleGapArc_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    ((gapAngle w i + w.val i : ℝ) : AddCircle (2 * Real.pi)) =
      circleGapVertices w (i + 1) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [gapAngle_last_add, w.property.2.1, Fin.last_add_one]
    simp [circleGapVertices, AddCircle.coe_period]
  · rw [Fin.coeSucc_eq_succ, ← gapAngle_succ]
    rfl

/-- No vertex lies in any open edge. See M76 derivation 15. -/
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

/-- Each closed edge is its open edge together with precisely its two
cyclic endpoint vertices. See Cairns p. 802 and M76 derivation 15. -/
theorem circleGapArc_eq_interior_union_endpoints (w : shortArcGapSpace n theta)
    (i : Fin (n + 3)) : circleGapArc w i =
      circleGapArcInterior w i ∪ {circleGapVertices w i, circleGapVertices w (i + 1)} := by
  unfold circleGapArc circleGapArcInterior
  rw [← Ioo_union_both (show gapAngle w i ≤ gapAngle w i + w.val i by
    linarith [(w.property.1 i).1]), image_union, image_pair, circleGapArc_endpoint]
  rfl

/-- Vertex-edge incidence is exactly the combinatorial cycle incidence.
See Cairns p. 802 and M76 derivation 15. -/
theorem circleGapVertex_mem_arc_iff (w : shortArcGapSpace n theta)
    (i k : Fin (n + 3)) : circleGapVertices w k ∈ circleGapArc w i ↔ k = i ∨ k = i + 1 := by
  rw [circleGapArc_eq_interior_union_endpoints, mem_union,
    or_iff_right (circleGapVertex_notMem_arcInterior w i k)]
  simp only [mem_insert_iff, mem_singleton_iff, (injective_circleGapVertices w).eq_iff]

/-- Distinct closed edges meet only along their common endpoint vertices.
See Cairns p. 802 and M76 derivation 15. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/PlanarCircleEdges.lean
section

/-!
# Straight planar edges of a cyclic circle configuration

Short cyclic gaps give a polygonal curve with injective radial projection
onto the circle. Distinct edges intersect only at their common vertices.
This is the planar link construction in Cairns 1940, Section 6, p. 802;
see M76 derivation 22.
-/


open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- The unit complex vertices of a short-gap circle configuration.
See Cairns p. 802 and M76 derivation 22. -/
noncomputable def planarGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) : ℂ :=
  Circle.exp (gapAngle w i)

/-- The complex-plane vertex map is the standard embedding of the
additive-circle vertex map. See Cairns p. 802 and M76 derivation 22. -/
theorem planarGapVertices_eq_circle (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    planarGapVertices w i = (AddCircle.homeomorphCircle' (circleGapVertices w i) : ℂ) := rfl

/-- All vertices are unit vectors. See Cairns p. 802 and M76 derivation 22. -/
theorem norm_planarGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    ‖planarGapVertices w i‖ = 1 := Circle.norm_coe _

/-- The labelled planar vertices are distinct.
See Cairns p. 802 and M76 derivation 22. -/
theorem injective_planarGapVertices (w : shortArcGapSpace n theta) :
    Function.Injective (planarGapVertices w) := by
  intro i j hij
  apply injective_circleGapVertices w
  apply AddCircle.homeomorphCircle'.injective
  exact Subtype.ext hij

/-- The planar vertices depend continuously on the gap parameters in
the product topology. See Cairns p. 802 and M76 derivation 22. -/
theorem continuous_planarGapVertices :
    Continuous (planarGapVertices : shortArcGapSpace n theta → Fin (n + 3) → ℂ) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (Circle.exp.continuous.comp
    ((continuous_gapAngle i).comp continuous_subtype_val))

/-- The lifted upper angle gives the next cyclic vertex, including the
last edge. See Cairns p. 802 and M76 derivation 22. -/
theorem planarGapVertices_endpoint (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    (Circle.exp (gapAngle w i + w.val i) : ℂ) = planarGapVertices w (i + 1) :=
  congrArg (fun z : AddCircle (2 * Real.pi) => (AddCircle.homeomorphCircle' z : ℂ))
    (circleGapArc_endpoint w i)

/-- The position vectors at the two ends of an edge are independent.
See Cairns p. 802 and M76 derivation 22. -/
theorem linearIndependent_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    LinearIndependent ℝ
      ((↑) : ↥({planarGapVertices w i, planarGapVertices w (i + 1)} : Set ℂ) → ℂ) := by
  have h := Complex.linearIndependent_circleExp_pair
    (a := gapAngle w i) (b := gapAngle w i + w.val i)
    (by linarith [(w.property.1 i).1]) (by simpa using (w.property.1 i).2)
  rw [planarGapVertices_endpoint] at h
  exact h

/-- The straight edge between consecutive cyclic vertices.
See Cairns p. 802 and M76 derivation 22. -/
def planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) : Set ℂ :=
  segment ℝ (planarGapVertices w i) (planarGapVertices w (i + 1))

/-- Central projection is injective on each full straight edge.
See Cairns p. 802 and M76 derivation 22. -/
theorem injOn_normalize_planarGapEdge (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (planarGapEdge w i) := by
  simpa only [convexHull_pair, planarGapEdge] using
    (linearIndependent_planarGapEdge w i).injOn_normalize_convexHull

/-- A straight edge projects onto exactly its short circle arc.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- Distinct edges with a common projected direction meet at the same
unit vertex, which is an endpoint of each edge.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- The polygonal union meets each positive ray at most once.
See Cairns p. 802 and M76 derivation 22. -/
theorem injOn_normalize_iUnion_planarGapEdge (w : shortArcGapSpace n theta) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (⋃ i, planarGapEdge w i) := by
  intro x hx y hy hxy
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
  by_cases hij : i = j
  · subst j
    exact injOn_normalize_planarGapEdge w i hxi hyj hxy
  · exact (planarGapEdges_common_direction w hij hxi hyj hxy).1

/-- Any two straight edges satisfy the simplicial intersection law.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- Every unit direction occurs on the polygonal union.
See Cairns p. 802 and M76 derivation 22. -/
theorem normalize_image_iUnion_planarGapEdge (w : shortArcGapSpace n theta) :
    NormedSpace.normalize '' (⋃ i, planarGapEdge w i) = Metric.sphere (0 : ℂ) 1 := by
  rw [image_iUnion]
  simp_rw [normalize_image_planarGapEdge]
  rw [← image_iUnion, iUnion_circleGapArc]
  apply Subset.antisymm
  · rintro _ ⟨z, _, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using Circle.norm_coe
      (AddCircle.homeomorphCircle' z)
  · intro z hz
    let u : Circle := ⟨z, hz⟩
    exact ⟨AddCircle.homeomorphCircle'.symm u, mem_univ _,
      congrArg Subtype.val (AddCircle.homeomorphCircle'.apply_symm_apply u)⟩

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/PlanarCircleComplex.lean
section

/-!
# Faithful planar realizations of the cyclic link

A short-gap circle configuration supplies a finite geometric complex
realizing the abstract cycle. Its faces have independent position vectors
and its radial projection is a bijection onto the unit circle. This is
the planar link in Cairns 1940, Section 6, p. 802; see M76 derivation 22.
-/


open Set Geometry NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- The finite vertex set of one straight edge of the polygon.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- The finite geometric polygon determined by a short-gap configuration.
See Cairns p. 802 and M76 derivation 22. -/
noncomputable def planarCircleComplex (w : shortArcGapSpace n theta) : SimplicialComplex ℝ ℂ :=
  SimplicialComplex.ofGenerators (range (planarGapEdgeVertices w))
    (planar_generators_independent w) (planar_generators_inter w)

/-- Polygon faces are precisely the nonempty subsets of its edge pairs.
See Cairns p. 802 and M76 derivation 22. -/
theorem mem_planarCircleComplex_faces (w : shortArcGapSpace n theta) (s : Finset ℂ) :
    s ∈ (planarCircleComplex w).faces ↔ s.Nonempty ∧ ∃ i, s ⊆ planarGapEdgeVertices w i := by
  change (s.Nonempty ∧ ∃ t ∈ range (planarGapEdgeVertices w), s ⊆ t) ↔ _
  constructor
  · rintro ⟨hs, _, ⟨i, rfl⟩, hsi⟩
    exact ⟨hs, i, hsi⟩
  · rintro ⟨hs, i, hsi⟩
    exact ⟨hs, _, mem_range_self i, hsi⟩

/-- The polygon has finitely many faces.
See Cairns p. 802 and M76 derivation 22. -/
theorem finite_planarCircleComplex_faces (w : shortArcGapSpace n theta) :
    (planarCircleComplex w).faces.Finite :=
  SimplicialComplex.finite_ofGenerators_faces (finite_range _) _ _

/-- The polygon's carrier is the union of its straight edges.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- Each polygon face has linearly independent position vectors.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- Central projection is injective on the polygon's entire carrier.
See Cairns p. 802 and M76 derivation 22. -/
theorem injOn_normalize_planarCircleComplex (w : shortArcGapSpace n theta) :
    InjOn (NormedSpace.normalize : ℂ → ℂ) (planarCircleComplex w).space := by
  rw [planarCircleComplex_space]
  exact injOn_normalize_iUnion_planarGapEdge w

/-- The projected polygon fills the unit circle.
See Cairns p. 802 and M76 derivation 22. -/
theorem normalize_image_planarCircleComplex (w : shortArcGapSpace n theta) :
    NormedSpace.normalize '' (planarCircleComplex w).space = Metric.sphere (0 : ℂ) 1 := by
  rw [planarCircleComplex_space]
  exact normalize_image_iUnion_planarGapEdge w

/-- The abstract cycle on at least three labels, including all nonempty
subfaces of its cyclic edges. See Cairns p. 802 and M76 derivation 22. -/
def cyclicEdgeComplex (n : ℕ) : AbstractSimplicialComplex (Fin (n + 3)) where
  faces := {s | s.Nonempty ∧ ∃ i, s ⊆ {i, i + 1}}
  isRelLowerSet_faces := by
    rintro s ⟨hs, i, hsi⟩
    exact ⟨hs, fun t hts ht => ⟨ht, i, hts.trans hsi⟩⟩
  singleton_mem i := ⟨Finset.singleton_nonempty i, i, by simp⟩

/-- The polygon's geometric faces are exactly the images of abstract
cycle faces under the labelled vertex assignment.
See Cairns p. 802 and M76 derivation 22. -/
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

/-- The gap-coordinate vertex assignment is a faithful radial embedding
of the abstract cycle. See Cairns p. 802 and M76 derivation 22. -/
theorem isRadialEmbedding_planarGapVertices (w : shortArcGapSpace n theta) :
    (cyclicEdgeComplex n).IsRadialEmbedding (planarGapVertices w) :=
  ⟨injective_planarGapVertices w, planarCircleComplex w, planarCircleComplex_faces_image w,
    fun _ hs => linearIndependent_planarCircleComplex_face w hs,
    injOn_normalize_planarCircleComplex w⟩

/-- A gap configuration gives a unit radial embedding, with the actual
subspace topology on its vertex positions.
See Cairns p. 802 and M76 derivation 22. -/
noncomputable def planarGapEmbedding (w : shortArcGapSpace n theta) :
    (cyclicEdgeComplex n).UnitRadialEmbedding ℂ :=
  ⟨⟨planarGapVertices w, isRadialEmbedding_planarGapVertices w⟩, norm_planarGapVertices w⟩

/-- The resulting unit radial embedding varies continuously with the
gap parameters. See Cairns pp. 801--802 and M76 derivation 22. -/
theorem continuous_planarGapEmbedding :
    Continuous (planarGapEmbedding : shortArcGapSpace n theta →
      (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) :=
  (continuous_planarGapVertices.subtype_mk _).subtype_mk _

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/PlanarCycleGaps.lean
section

/-!
# Positive angular increments of normalized planar cycles

Exact radial vertex-face incidence prevents adjacent cycle edges from
reversing angular direction. Fixing the first edge positively therefore
orients every edge positively. This recovers the local gap inequalities
in Cairns 1940, Section 6, p. 802; see M76 derivation 23.
-/


open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ}

/-- The unit vertices of a radial cycle, regarded as circle points.
See Cairns p. 802 and M76 derivation 23. -/
noncomputable def unitCycleVertex (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : Circle :=
  ⟨v.val.val i, mem_sphere_zero_iff_norm.mpr (v.property i)⟩

/-- The signed principal angular increment on a cyclic edge.
See Cairns p. 802 and M76 derivation 23. -/
noncomputable def cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : ℝ :=
  Circle.shortIncrement (unitCycleVertex v i) (unitCycleVertex v (i + 1))

/-- The endpoints of each edge have independent position vectors.
See Cairns p. 802 and M76 derivation 23. -/
theorem linearIndependent_unitCycleEdge (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : LinearIndependent ℝ
      ((↑) : ↥({(unitCycleVertex v i : ℂ), (unitCycleVertex v (i + 1) : ℂ)} : Set ℂ) → ℂ) := by
  have hs : ({i, i + 1} : Finset (Fin (n + 3))) ∈ (cyclicEdgeComplex n).faces :=
    ⟨by simp, i, Finset.Subset.refl _⟩
  have h := v.val.property.linearIndependent_face_image hs
  rw [show (({i, i + 1} : Finset (Fin (n + 3))) : Set (Fin (n + 3))) =
    {i, i + 1} from Finset.coe_pair, image_pair] at h
  exact h

/-- Each recovered increment is strictly between minus pi and pi.
See Cairns p. 802 and M76 derivation 23. -/
theorem cycleIncrement_mem_Ioo (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : cycleIncrement v i ∈ Ioo (-Real.pi) Real.pi :=
  ⟨Circle.neg_pi_lt_shortIncrement _ _,
    Circle.shortIncrement_lt_pi (linearIndependent_unitCycleEdge v i)⟩

/-- A unit vertex belongs to a projected edge precisely at one of the
edge's two labels. See Cairns p. 802 and M76 derivation 23. -/
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

/-- Positivity on one edge forces positivity on the next: otherwise
one outer vertex lies on the other's projected edge.
See Cairns p. 802 and M76 derivation 23. -/
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

/-- Prescribing the initial unit edge fixes its principal increment.
See Cairns p. 802 and M76 derivation 23. -/
theorem cycleIncrement_zero (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    cycleIncrement v 0 = theta := by
  change Complex.arg ((unitCycleVertex v (0 + 1) / unitCycleVertex v 0 : Circle) : ℂ) = theta
  rw [zero_add, hzero, hone, div_one]
  exact Circle.arg_exp (by linarith [Real.pi_pos, htheta.1]) htheta.2.le

/-- Every edge has a positive short increment once the first two
vertices fix a positive short edge. No cyclic-order premise is assumed.
See Cairns p. 802 and M76 derivation 23. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/PlanarCycleCoordinates.lean
section

/-!
# Global gap coordinates of normalized radial cycles

The positive short increments of a normalized unit radial cycle add to
one full turn and reconstruct every vertex. Thus the geometry forces
the cyclic order used in gap coordinates. See Cairns 1940, Section 6,
p. 802 and Section 11, p. 807, footnote 14; M76 derivation 23.
-/


open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ}

/-- Exponentiating prefix sums of the recovered increments reconstructs
each original vertex. See Cairns p. 802 and M76 derivation 23. -/
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

/-- The closing edge makes the total increment an integer number of
full turns. See Cairns p. 802 and M76 derivation 23. -/
theorem exp_sum_cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (hzero : unitCycleVertex v 0 = 1) : Circle.exp (∑ i, cycleIncrement v i) = 1 := by
  rw [← gapAngle_last_add, Circle.exp_add, exp_gapAngle_cycleIncrement v hzero]
  simpa only [cycleIncrement, Fin.last_add_one, hzero] using
    Circle.mul_exp_shortIncrement (unitCycleVertex v (Fin.last (n + 2)))
      (unitCycleVertex v (Fin.last (n + 2) + 1))

/-- No nonclosing edge can complete a full turn: that would put the
marked origin vertex on a nonincident edge.
See Cairns p. 802 and M76 derivation 23. -/
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

/-- The recovered positive angular increments sum to exactly one turn,
not a larger winding number. See Cairns p. 802 and M76 derivation 23. -/
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

/-- A normalized unit radial realization yields valid short-gap
coordinates, with positivity and cyclic order derived from its geometry.
See Cairns pp. 802, 807 and M76 derivation 23. -/
theorem cycleIncrement_mem_shortArcGapSpace
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    cycleIncrement v ∈ shortArcGapSpace n theta :=
  ⟨fun i => ⟨cycleIncrement_pos v htheta hzero hone i, (cycleIncrement_mem_Ioo v i).2⟩,
    sum_cycleIncrement v htheta hzero hone, cycleIncrement_zero v htheta hzero hone⟩

/-- Reconstructing the planar vertices from the recovered gaps gives
the original vertex assignment exactly.
See Cairns p. 802 and M76 derivation 23. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/PlanarCycleConfigurationSpace.lean
section

/-!
# Contractibility of normalized planar cycle realizations

Fixing the first two unit vertices identifies the full radial cycle
realization space with the convex short-gap space. Both maps are
continuous in the actual vertex topology. No angular-order premise is
assumed on the realization side. This is the planar configuration-space
calculation of Cairns 1940, pp. 802, 807; see M76 derivation 23.
-/


open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- Unit radial cycle realizations with only the two marked adjacent
vertices prescribed. See Cairns pp. 801--802 and M76 derivation 23. -/
def normalizedUnitCycleSpace (n : ℕ) (theta : ℝ) :
    Set ((cyclicEdgeComplex n).UnitRadialEmbedding ℂ) :=
  {v | unitCycleVertex v 0 = 1 ∧ unitCycleVertex v 1 = Circle.exp theta}

/-- The circle vertex of the constructed polygon is its prescribed
exponential. See Cairns p. 802 and M76 derivation 23. -/
theorem unitCycleVertex_planarGapEmbedding (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    unitCycleVertex (planarGapEmbedding w) i = Circle.exp (gapAngle w i) := rfl

/-- The polygon constructed from gaps satisfies the two marked-vertex
constraints. See Cairns p. 802 and M76 derivation 23. -/
noncomputable def normalizedGapEmbedding (w : shortArcGapSpace n theta) :
    normalizedUnitCycleSpace n theta :=
  ⟨planarGapEmbedding w, by
    constructor
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_zero, Circle.exp_zero]
    · rw [unitCycleVertex_planarGapEmbedding, gapAngle_one w.property]⟩

/-- Recovering increments from a constructed polygon returns its
original gaps, including the closing gap.
See Cairns p. 802 and M76 derivation 23. -/
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

/-- Unit circle vertices depend continuously on radial vertex
coordinates. See Cairns p. 801 and M76 derivation 23. -/
theorem continuous_unitCycleVertex (i : Fin (n + 3)) :
    Continuous (fun v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ => unitCycleVertex v i) :=
  ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

/-- The short-increment tuple is continuous on the entire unit radial
cycle space: independent edges exclude the argument cut.
See Cairns p. 802 and M76 derivation 23. -/
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

/-- The full normalized unit radial cycle space is homeomorphic to its
short-gap coordinates. Geometric incidence forces the positive cyclic
order in the inverse construction. See Cairns pp. 802, 807 and
M76 derivation 23. -/
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

/-- Normalized planar cycle realizations are contractible in the
subspace topology of their vertex positions.
See Cairns p. 807, footnote 14 and M76 derivation 23. -/
theorem contractible_normalizedUnitCycleSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (normalizedUnitCycleSpace n theta) := by
  let := contractible_shortArcGapSpace n htheta
  exact (gapUnitCycleHomeomorph n htheta).symm.contractibleSpace

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/FixedEdgeCycleSpace.lean
section

/-!
# Contractibility of radial cycles with a fixed edge

The two marked unit vertices remain fixed during radial normalization.
Consequently the full radial realization space with that frame is
contractible, without unit-norm restrictions on its other vertices.
See Cairns 1940, Lemma 5.3, pp. 801--802, and p. 807, footnote 14;
M76 derivation 24.
-/


open Set

namespace PoincareMT.M76.Smoothing

/-- Prescribed values for the two marked vertices. Values outside
labels zero and one do not constrain the realization.
See Cairns p. 801 and M76 derivation 24. -/
noncomputable def cycleFrame (n : ℕ) (theta : ℝ) (i : Fin (n + 3)) : ℂ :=
  if i = 0 then 1 else Circle.exp theta

/-- The fixed-frame equations prescribe exactly the two adjacent
vertices. See Cairns p. 801 and M76 derivation 24. -/
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

/-- Faithful radial cycle realizations with the first two vertices
fixed as a coordinate frame. Other vertices may have arbitrary positive
radii. See Cairns pp. 801--802 and M76 derivation 24. -/
abbrev FixedEdgeCycleSpace (n : ℕ) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedRadialEmbedding ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)

/-- The constrained unit subspace is exactly the normalized unit cycle
space previously described in angular coordinates.
See Cairns pp. 801--802 and M76 derivation 24. -/
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

/-- Fixing an independent unit edge makes the full radial cycle
realization space contractible in vertex topology. Unit norms on other
vertices are not assumed. See Cairns pp. 801--802, 807 and
M76 derivation 24. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/CycleProjectionSpace.lean
section

/-!
# Contractible linear projections of cyclic links

Basis evaluation transfers the fixed-edge contraction to the ambient
linear maps used in Cairns 1940, Section 3, p. 799, and Lemma 5.1,
p. 801. This is the operator-coordinate step of M76 derivation 25;
the geometric kernel comparison is separate.
-/


open Set

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Linear maps realizing a cyclic link with the two frame columns
fixed. See Cairns pp. 799, 801 and M76 derivation 25. -/
abbrev CycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) (theta : ℝ) :=
  (cyclicEdgeComplex n).FixedBasisRadialProjection b
    ({0, 1} : Set (Fin (n + 3))) (cycleFrame n theta)

/-- The constrained ambient linear-map space is contractible in its
operator topology. See Cairns Lemma 5.1 and M76 derivation 25. -/
theorem contractible_cycleProjectionSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (CycleProjectionSpace n b theta) := by
  let := contractible_fixedEdgeCycleSpace n htheta
  exact (AbstractSimplicialComplex.fixedBasisRadialProjectionHomeomorph
    (cyclicEdgeComplex n) b ({0, 1} : Set (Fin (n + 3)))
    (cycleFrame n theta)).contractibleSpace

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/CycleFrameCoordinates.lean
section

/-!
# A fixed coordinate frame in a cyclic basis star

The first two source basis vectors provide a real-linear complex frame.
Fixing that frame is exactly the previously used cycle normalization
at angle pi/2. See Cairns 1940, p. 801 and p. 807, footnote 14,
and M76 derivation 31.
-/


open Set

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complex coordinate plane spanned by the first cyclic edge.
See Cairns p. 801 and M76 derivation 31. -/
noncomputable def cycleFrameInclusion {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight (b 0) + Complex.imCLM.smulRight (b 1)

/-- The real unit maps to the first source vertex.
See Cairns p. 801 and M76 derivation 31. -/
theorem cycleFrameInclusion_one {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b 1 = b 0 := by simp [cycleFrameInclusion]

/-- The imaginary unit maps to the second source vertex.
See Cairns p. 801 and M76 derivation 31. -/
theorem cycleFrameInclusion_I {n : ℕ} (b : Module.Basis (Fin (n + 3)) ℝ E) :
    cycleFrameInclusion b Complex.I = b 1 := by simp [cycleFrameInclusion]

/-- The two distinct basis coefficients make this frame injective.
See Cairns p. 801 and M76 derivation 31. -/
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

/-- Fixing the complex frame means fixing its two basis vectors.
See Cairns p. 801 and M76 derivation 31. -/
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

/-- At angle pi/2 the fixed-edge conditions are exactly the right
inverse condition for the source frame.
See Cairns pp. 801, 807 and M76 derivation 31. -/
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

/-- The normalized frame operators and the fixed-edge projection
space are homeomorphic, retaining their operator coordinates.
See Cairns pp. 801, 807 and M76 derivation 31. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/AmbientCycleOperators.lean
section

/-!
# Cyclic projection coordinates in a larger ambient space

The source-subspace constraints fix a complex frame and a faithful
radial cycle. All operator coordinates on the orthogonal complement
are unrestricted. Thus the ambient operator space is a product with
a contractible vector space. See Cairns 1940, Lemma 5.2, p. 801,
and M76 derivation 32.
-/


namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Simultaneous frame and radial conditions expressed on a single
operator subtype. See Cairns p. 801 and M76 derivation 32. -/
abbrev CycleFrameRadialOperatorSpace (n : ℕ) (b : Module.Basis (Fin (n + 3)) ℝ E) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (cycleFrameInclusion b) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}

/-- Combining the frame and radial conditions does not change the
topology of the normalized cycle projection space.
See Cairns p. 801 and M76 derivation 32. -/
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

/-- Ambient operators whose restrictions realize the source cycle
with its first edge fixed. See Cairns p. 801 and M76 derivation 32. -/
abbrev AmbientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :=
  {Q : E →L[ℝ] ℂ // Function.RightInverse (V.subtypeL.comp (cycleFrameInclusion b)) Q ∧
    (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q (b i))}

/-- Ambient cyclic operators split into the original constrained
projection space and arbitrary operators on the orthogonal complement.
See Cairns Lemma 5.2, p. 801, and M76 derivation 32. -/
noncomputable def ambientCycleProjectionHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    AmbientCycleProjectionSpace n V b ≃ₜ
      (CycleProjectionSpace n b (Real.pi / 2) × (Vᗮ →L[ℝ] ℂ)) :=
  (V.operatorRestrictionHomeomorph (fun R : V →L[ℝ] ℂ =>
    Function.RightInverse (cycleFrameInclusion b) R ∧
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => R (b i)))).trans
        ((cycleFrameRadialOperatorHomeomorph n b).prodCongr (Homeomorph.refl _))

/-- Enlarging the ambient space preserves contractibility of the
normalized cyclic operator space.
See Cairns Lemma 5.2, p. 801, and M76 derivation 32. -/
theorem contractible_ambientCycleProjectionSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (AmbientCycleProjectionSpace n V b) := by
  let := contractible_cycleProjectionSpace n b
    (show Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi from
      ⟨half_pos Real.pi_pos, half_lt_self Real.pi_pos⟩)
  exact (ambientCycleProjectionHomeomorph n V b).contractibleSpace

/-- Flatten the two geometric frame-coordinate conditions without
altering the operator or its topology.
See Cairns p. 801 and M76 derivation 32. -/
noncomputable def ambientFrameCycleHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    {Q : (V.subtypeL.comp (cycleFrameInclusion b)).FrameProjectionSpace //
      (cyclicEdgeComplex n).IsRadialEmbedding (fun i => Q.val (b i))} ≃ₜ
      AmbientCycleProjectionSpace n V b where
  toFun Q := ⟨Q.val.val, Q.val.property, Q.property⟩
  invFun Q := ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun _ => _)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun _ => _) |>.subtype_mk (fun _ => _)

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/TangentCycleProjections.lean
section

/-!
# Contractible projections of cyclic tangent cylinders

The ambient cyclic-star projection calculation supplies the normal
factor of the tangent-cylinder decomposition. Hence adding any fixed
tangent space preserves contractibility in the actual operator
topology. See Cairns 1940, Section 4, pp. 800--801, Section 11,
p. 807, and M76 derivations 32--33.
-/


open Set ContinuousLinearMap

namespace PoincareMT.M76.Smoothing

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Geometric injectivity and the radial coordinate condition give
the same normalized ambient cycle operators.
See Cairns pp. 799--801 and M76 derivations 32--33. -/
noncomputable def ambientCycleFrameEmbeddingHomeomorph (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space) ≃ₜ
      AmbientCycleProjectionSpace n V b :=
  Homeomorph.setCongr (by
    ext Q
    exact and_congr Iff.rfl
      ((cyclicEdgeComplex n).isRadialEmbedding_iff_injOn_basisCone_subtype V b Q).symm)

/-- Normalized operators embedding the actual included cyclic star
form a contractible space.
See Cairns pp. 801, 807 and M76 derivations 32--33. -/
theorem contractible_ambientCycleFrameEmbeddingSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (FrameEmbeddingSpace (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space)) := by
  let := contractible_ambientCycleProjectionSpace n V b
  exact (ambientCycleFrameEmbeddingHomeomorph n V b).contractibleSpace

/-- Cyclic normal stars with any tangent factor have contractible
normalized cylinder-projection spaces. The source is the full
saturated cylinder, not a finite list of vertices.
See Cairns pp. 800--801, 807 and M76 derivation 33. -/
theorem contractible_tangentCycleEmbeddingSpace (n : ℕ) (V : Submodule ℝ E)
    (b : Module.Basis (Fin (n + 3)) ℝ V) :
    ContractibleSpace (TangentCylinderEmbeddingSpace
      (V.subtypeL.comp (cycleFrameInclusion b))
      (V.subtype '' ((cyclicEdgeComplex n).basisRadialEmbedding b).cone.space) T) := by
  let := contractible_ambientCycleFrameEmbeddingSpace n V b
  exact contractible_tangentCylinderEmbeddingSpace _ _

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Smoothing/CyclicFacePlanes.lean
section

/-!
# Transverse planes of actual cyclic face stars

An exact cyclic labelling of the actual face link identifies its normal
cone with the included independent cyclic model. The first edge gives
an actual coface containing the normal frame and the central tangent
space. Thus the full geometric transverse-plane space is contractible.
See Cairns 1940, pp. 800--801, 807, and M76 derivation 40.
-/


open Set Geometry ContinuousLinearMap AbstractSimplicialComplex

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- An actual general-position face star with exactly cyclic link
incidence has contractible full transverse-plane space. The cyclic
labelling and its first edge construct the normal model and coface
frame; they are not separate carrier or complement assumptions.
See Cairns pp. 800--801, 807 and M76 derivation 40. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/LinkIncidencePlanes.lean
section

/-!
# Transverse planes from actual link incidence

A connected finite one-dimensional face link whose vertex links each
have two vertices supplies exact cyclic labels. Hence its actual
closed face star has contractible transverse-plane space. See Cairns
1940, pp. 800--802, 807, and M76 derivation 41.
-/


open Set Geometry

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Geometric connectedness and two vertices in every enlarged-face
link construct the cyclic labels needed for the actual transverse-plane
theorem. Only original-complex incidence is assumed.
See Cairns pp. 800--802, 807 and M76 derivation 41. -/
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

-- Source: PoincareMT/Proofs/M76/Mathlib/TwoRayProjection.lean
section

/-!
# Normalized scalar projections of a two-ray star

A projection fixing the first endpoint embeds two independent source
segments precisely when the second endpoint has negative image.
See Cairns 1940, Section 11, p. 807, and M76 derivation 39.
-/


open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The one-dimensional full star with its two outer endpoints.
See Cairns pp. 800, 807 and M76 derivation 39. -/
def twoRayStar (u v : E) : Set E := segment ℝ 0 u ∪ segment ℝ 0 v

private theorem segment_zero_eq_image (u : E) :
    segment ℝ 0 u = (fun a : ℝ => a • u) '' Icc (0 : ℝ) 1 := by
  simpa only [smul_zero, zero_add] using segment_eq_image ℝ (0 : E) u

/-- Fixing the first endpoint forces the other endpoint to lie
strictly on the opposite side of zero for a scalar projection to
embed the entire independent two-ray star.
See Cairns p. 807 and M76 derivation 39. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/TwoPointNormalSpace.lean
section

/-!
# The two-point normal-link projection space

Fixing one endpoint of a two-ray star identifies its entire
embedding-operator space with a nonempty convex set. This proves
the normal one-dimensional case of Cairns 1940, Section 11,
p. 807. See M76 derivation 39.
-/


open Set Geometry ContinuousLinearMap

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixing the scalar frame generated by a vector is equivalent
to sending that vector to one. See Cairns p. 807 and M76 derivation 39. -/
theorem rightInverse_rayFrame_iff (u : E) (Q : E →L[ℝ] ℝ) :
    Function.RightInverse (toSpanSingleton ℝ u) Q ↔ Q u = 1 := by
  constructor
  · intro h
    simpa only [toSpanSingleton_apply_one] using h 1
  · intro h r
    change Q (r • u) = r
    rw [map_smul, h, smul_eq_mul, mul_one]

/-- The scalar endpoint constraints define a convex subset of the
actual ambient operator space. See Cairns p. 807 and M76 derivation 39. -/
theorem convex_twoPointOperatorSet (u v : E) :
    Convex ℝ {Q : E →L[ℝ] ℝ | Q u = 1 ∧ Q v < 0} := by
  intro Q hQ R hR a b ha hb hab
  constructor
  · change a * Q u + b * R u = 1
    rw [hQ.1, hR.1, mul_one, mul_one, hab]
  · change a * Q v + b * R v < 0
    exact convex_Iio (0 : ℝ) hQ.2 hR.2 ha hb hab

/-- A two-ray embedding with its first endpoint fixed has exactly
one linear equality and one strict endpoint inequality as its
coordinates. See Cairns p. 807 and M76 derivation 39. -/
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

/-- Independent endpoints admit an ambient scalar operator taking
values one and minus one. The construction extends coordinates on
their span by orthogonal projection.
See Cairns pp. 800, 807 and M76 derivation 39. -/
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

/-- The complete normalized projection space of an independent
two-point normal link is contractible in any finite ambient space.
See Cairns Section 11, p. 807, and M76 derivation 39. -/
theorem contractible_twoPointFrameEmbeddingSpace (u v : E)
    (hv : LinearIndependent ℝ ![u, v]) :
    ContractibleSpace (FrameEmbeddingSpace (toSpanSingleton ℝ u) (twoRayStar u v)) := by
  let : ContractibleSpace {Q : E →L[ℝ] ℝ // Q u = 1 ∧ Q v < 0} :=
    (convex_twoPointOperatorSet u v).contractibleSpace (nonempty_twoPointOperatorSet u v hv)
  exact (twoPointFrameEmbeddingHomeomorph u v hv).contractibleSpace

end PoincareMT.M76.Smoothing

end

-- Source: PoincareMT/Proofs/M76/Mathlib/SmallFaceLinks.lean
section

/-!
# Carriers of two-point and empty actual normal links

An actual two-vertex discrete face link projects to precisely the
two-ray star, while an empty link projects to the center. These
are the low-dimensional normal stars used by Cairns 1940,
Section 11, p. 807. See M76 derivation 39.
-/


open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E]

/-- A face with exactly two singleton link faces projects to the
entire two-ray star, with its actual projected endpoints.
See Cairns pp. 800, 807 and M76 derivation 39. -/
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

/-- An empty actual face link projects to a singleton center.
The source central face is still nonempty.
See Cairns pp. 800, 807 and M76 derivation 39. -/
theorem affine_image_closedFaceStar_emptyLink (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0) (hlink : (K.faceLink s).faces = ∅) :
    f '' (K.closedFaceStar s).space = {0} := by
  rw [K.affine_image_closedFaceStar hs f hf, hlink]
  simp only [insert_empty_eq, mem_singleton_iff, iUnion_iUnion_eq_left,
    Finset.coe_empty, image_empty, convexHull_singleton]

end Geometry.SimplicialComplex

end

-- Source: PoincareMT/Proofs/M76/Smoothing/SmallNormalFacePlanes.lean
section

/-!
# Geometric planes for actual two-point and empty face links

The low-dimensional normal models give contractibility of all
transverse planes of the required dimension for actual face stars.
Their normal-plus-tangent frames are constructed in actual cofaces,
so no separate frame-complement hypothesis is imposed. See Cairns
1940, Section 11, p. 807, and M76 derivation 39.
-/


open Set Geometry ContinuousLinearMap

namespace PoincareMT.M76.Smoothing

section Singleton

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F]

/-- A singleton normal star has a unique normalized projection
to a zero-dimensional target, hence a contractible operator space.
See Cairns p. 807 and M76 derivation 39. -/
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

/-- An actual general-position face star whose link is exactly
two distinct isolated vertices has contractible full transverse-plane
space of the expected codimension. Its coface frame is constructed.
See Cairns pp. 800--801, 807 and M76 derivation 39. -/
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

/-- An actual general-position face with empty link has a
contractible full transverse-plane space. The zero normal frame
leaves exactly the tangent frame of the central face.
See Cairns pp. 800--801, 807 and M76 derivation 39. -/
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

-- Source: PoincareMT/Proofs/M76/Smoothing/PositiveFacePlanes.lean
section

/-!
# All positive-dimensional face stars in dimension three

Finite general-position complexes with connected edge links and
two-vertex triangle links have contractible codimension-three
transverse-plane spaces at every positive-dimensional face. The
face-size bound supplies all normal-link dimensions. See Cairns
1940, Section 11, p. 807, and M76 derivation 42.
-/


open Set Geometry

namespace PoincareMT.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- The incidence conditions of a closed combinatorial
three-manifold make the full transverse-plane spaces of all its
positive-dimensional face stars contractible. Vertex stars remain
the separate Brouwer-star existence step.
See Cairns pp. 799--801, 807 and M76 derivation 42. -/
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

namespace OMA.PoincareFacePlanesPort

open Geometry Set

/-- Identify the plane spaces by their submodules and orthogonal projectors. -/
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
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1.H1 := by
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

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1.H1 :=
  OMA.PoincareFacePlanesPort.exact_face_planes
