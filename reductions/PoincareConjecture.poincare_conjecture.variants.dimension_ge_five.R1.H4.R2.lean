import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1
import Mathlib

/-!
# Compact high-dimensional recognition via two open cells

Adapted from Will (Ziang) Li, Poincare-High-Dim at cffda864, Apache-2.0.
The finite-cover proofs come from `Topology/Recognition/FiniteCellCover.lean`
and `Topology/Engulfing/ConnellCover.lean`. This version places the generic
finite-cover argument between the two named hypotheses of the Left to Solve reduction.
Copyright (c) 2026 Will (Ziang) Li. The original license follows the proof.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R2
open Set Metric Topology ContinuousMap
open scoped Manifold ContinuousMap

/-- A Euclidean-charted space has an open Euclidean cell centered at each point. -/
theorem exists_openEmbedding_euclidean_at {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → M, IsOpenEmbedding φ ∧ φ 0 = x := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) (mem_chart_target _ x)
  let u : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    OpenPartialHomeomorph.univBall (c x) r
  have hu_source : u.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hu_target : u.target = ball (c x) r := OpenPartialHomeomorph.univBall_target _ hr
  let ψ := u.trans c.symm
  have hsource : ψ.source = univ := by
    ext v
    simp only [ψ, OpenPartialHomeomorph.trans_source, mem_inter_iff, hu_source,
      mem_univ, true_and, mem_preimage, iff_true]
    exact hball (hu_target ▸ u.map_source (hu_source ▸ mem_univ v))
  refine ⟨ψ, ψ.isOpenEmbedding hsource, ?_⟩
  change c.symm (OpenPartialHomeomorph.univBall (c x) r 0) = x
  rw [OpenPartialHomeomorph.univBall_apply_zero]
  exact c.left_inv (mem_chart_source _ x)

/-- A compact topological manifold admits a finite cover by the half-radius balls of open
Euclidean cells, each with a compact closed unit ball. -/
theorem exists_finite_euclidean_cell_cover {n : ℕ} {M : Type*}
    [TopologicalSpace M] [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∃ k : ℕ, ∃ φ : Fin k → EuclideanSpace ℝ (Fin n) → M,
      (∀ i, IsOpenEmbedding (φ i)) ∧
      (⋃ i, φ i '' ball 0 (1 / 2 : ℝ)) = univ ∧
      (∀ i, IsCompact (φ i '' closedBall 0 1)) := by
  classical
  choose φ hφ hcenter using
    (fun x : M => exists_openEmbedding_euclidean_at (n := n) x)
  have hcover : (univ : Set M) ⊆ ⋃ x, φ x '' ball 0 (1 / 2 : ℝ) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, 0, by simp, hcenter x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => φ x '' ball 0 (1 / 2 : ℝ))
    (fun x => (hφ x).isOpenMap _ isOpen_ball) hcover
  let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (by simp)).symm
  refine ⟨s.card, fun i => φ (e i), fun i => hφ (e i), ?_, ?_⟩
  · apply eq_univ_of_univ_subset
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    refine mem_iUnion.mpr ⟨e.symm ⟨y, hy⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hxy
  · intro i
    exact (isCompact_closedBall _ _).image (hφ (e i)).continuous

/-- Split a compact set covered by two open sets into two compact protected cores. -/
theorem exists_compact_pair_subsets_of_open_cover {X : Type*}
    [TopologicalSpace X] [T2Space X] [NormalSpace X]
    {T U V : Set X} (hT : IsCompact T) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : T ⊆ U ∪ V) :
    ∃ A B, IsCompact A ∧ IsCompact B ∧ A ⊆ U ∧ B ⊆ V ∧ T ⊆ A ∪ B := by
  have hC : IsCompact (T \ V) := hT.diff hV
  have hCU : T \ V ⊆ U := by
    intro x hx
    exact (hcover hx.1).resolve_right hx.2
  obtain ⟨O, hO, hCO, hOU⟩ := normal_exists_closure_subset hC.isClosed hU hCU
  refine ⟨T ∩ closure O, T ∩ Oᶜ, hT.inter_right isClosed_closure,
    hT.inter_right hO.isClosed_compl, fun _ hx => hOU hx.2, ?_, ?_⟩
  · intro x hx
    by_contra hxV
    exact hx.2 (hCO ⟨hx.1, hxV⟩)
  · intro x hx
    by_cases hxO : x ∈ O
    · exact Or.inl ⟨hx, subset_closure hxO⟩
    · exact Or.inr ⟨hx, hxO⟩

/-- Finite cover reduction with compact cores at every step. The three-core hypothesis
does not require covering the entirety of any of the original open sets. -/
theorem exists_pair_cover_of_finite_compact_core_cover {X ι : Type*}
    [TopologicalSpace X] [T2Space X] [NormalSpace X] [Fintype ι]
    (P : Set X → Prop) (hopen : ∀ U, P U → IsOpen U) (hne : ∃ U, P U)
    (hmerge : ∀ A B C U V W, IsCompact A → IsCompact B → IsCompact C →
      P U → P V → P W → A ⊆ U → B ⊆ V → C ⊆ W →
      ∃ U' V', P U' ∧ P V' ∧ A ∪ B ∪ C ⊆ U' ∪ V')
    (A U : ι → Set X) (hA : ∀ i, IsCompact (A i)) (hU : ∀ i, P (U i))
    (hAU : ∀ i, A i ⊆ U i) (hcover : (⋃ i, A i) = univ) :
    ∃ U' V', P U' ∧ P V' ∧ U' ∪ V' = univ := by
  classical
  have hfinite (s : Finset ι) :
      ∃ V W, P V ∧ P W ∧ (⋃ i ∈ s, A i) ⊆ V ∪ W := by
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨V, hV⟩ := hne
        exact ⟨V, V, hV, hV, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨V, W, hV, hW, hs⟩ := ih
        have hT : IsCompact (⋃ j ∈ s, A j) :=
          s.finite_toSet.isCompact_biUnion (fun j _ => hA j)
        obtain ⟨B, C, hB, hC, hBV, hCW, hBC⟩ :=
          exists_compact_pair_subsets_of_open_cover hT (hopen V hV) (hopen W hW) hs
        obtain ⟨V', W', hV', hW', hnew⟩ :=
          hmerge (A i) B C (U i) V W (hA i) hB hC (hU i) hV hW (hAU i) hBV hCW
        refine ⟨V', W', hV', hW', ?_⟩
        intro x hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hnew (Or.inl (Or.inl hxj))
        · rcases hBC (mem_iUnion₂.mpr ⟨j, hj, hxj⟩) with hxB | hxC
          · exact hnew (Or.inl (Or.inr hxB))
          · exact hnew (Or.inr hxC)
  obtain ⟨V, W, hV, hW, hVW⟩ := hfinite Finset.univ
  refine ⟨V, W, hV, hW, eq_univ_of_univ_subset ?_⟩
  simpa only [Finset.mem_univ, iUnion_true, hcover] using hVW

/-- Applying compact-core reduction to a finite chart cover produces two open cells. -/
theorem exists_two_open_cells_of_compact_three_core_reduction {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (hmerge : ∀ (A B C : Set M) (u v w : EuclideanSpace ℝ (Fin n) → M),
      IsCompact A → IsCompact B → IsCompact C →
      IsOpenEmbedding u → IsOpenEmbedding v → IsOpenEmbedding w →
      A ⊆ range u → B ⊆ range v → C ⊆ range w →
      ∃ u' v' : EuclideanSpace ℝ (Fin n) → M,
        IsOpenEmbedding u' ∧ IsOpenEmbedding v' ∧ A ∪ B ∪ C ⊆ range u' ∪ range v') :
    ∃ u v : EuclideanSpace ℝ (Fin n) → M,
      IsOpenEmbedding u ∧ IsOpenEmbedding v ∧ range u ∪ range v = univ := by
  classical
  let P : Set M → Prop := fun U =>
    ∃ u : EuclideanSpace ℝ (Fin n) → M, IsOpenEmbedding u ∧ range u = U
  have hopen : ∀ U, P U → IsOpen U := by
    rintro U ⟨u, hu, rfl⟩
    exact hu.isOpen_range
  have hne : ∃ U, P U := by
    obtain ⟨u, hu, -⟩ := exists_openEmbedding_euclidean_at
      (n := n) (Classical.arbitrary M)
    exact ⟨range u, u, hu, rfl⟩
  obtain ⟨k, φ, hφ, hcover, hcompact⟩ :=
    exists_finite_euclidean_cell_cover (n := n) (M := M)
  have hcover' : (⋃ i, φ i '' closedBall 0 1) = univ := by
    apply eq_univ_of_univ_subset
    rw [← hcover]
    exact iUnion_mono fun i => image_mono
      ((ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans ball_subset_closedBall)
  obtain ⟨U, V, hU, hV, hUV⟩ := exists_pair_cover_of_finite_compact_core_cover P hopen hne
    (by
      rintro A B C U V W hA hB hC ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩ hAu hBv hCw
      obtain ⟨u', v', hu', hv', hcov⟩ := hmerge A B C u v w hA hB hC hu hv hw hAu hBv hCw
      exact ⟨range u', range v', ⟨u', hu', rfl⟩, ⟨v', hv', rfl⟩, hcov⟩)
    (fun i => φ i '' closedBall 0 1) (fun i => range (φ i)) hcompact
    (fun i => ⟨φ i, hφ i, rfl⟩) (fun _ => image_subset_range _ _) hcover'
  obtain ⟨u, hu, rfl⟩ := hU
  obtain ⟨v, hv, rfl⟩ := hV
  exact ⟨u, v, hu, hv, hUV⟩

/-- Connell's geometric input. Every three compact sets, each lying in its own
open Euclidean cell, can be covered by two open Euclidean cells. -/
def H1 : Prop := ∀ (n : ℕ), 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [SimplyConnectedSpace M] [CompactSpace M],
    (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) →
    ∀ (A B C : Set M) (u v w : EuclideanSpace ℝ (Fin n) → M),
      IsCompact A → IsCompact B → IsCompact C →
      IsOpenEmbedding u → IsOpenEmbedding v → IsOpenEmbedding w →
      A ⊆ range u → B ⊆ range v → C ⊆ range w →
      ∃ u' v' : EuclideanSpace ℝ (Fin n) → M,
        IsOpenEmbedding u' ∧ IsOpenEmbedding v' ∧ A ∪ B ∪ C ⊆ range u' ∪ range v'

/-- Brown's recognition theorem for a compact metric space covered by two open cells. -/
def H2 : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (X : Type) [MetricSpace X] [CompactSpace X]
    (u v : EuclideanSpace ℝ (Fin n) → X), IsOpenEmbedding u → IsOpenEmbedding v →
    range u ∪ range v = univ → Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1.H4 := by
  intro merge brown n hn M _ _ _ _ _ e
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let : Nonempty M := ⟨e.invFun ⟨EuclideanSpace.single 0 (1 : ℝ), by simp⟩⟩
  obtain ⟨u, v, hu, hv, cover⟩ := exists_two_open_cells_of_compact_three_core_reduction (merge n hn M e)
  exact brown n (by omega) M u v hu hv cover

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R2

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
