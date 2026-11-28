import FormalConjectures.Wikipedia.InscribedSquare
import Mathlib

/-
Adapted Sperner/simplicial-complex foundation (OAI.Tingley) from OpenAI,
openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (via open-math-agents proofs/mo-387291.lean).
Original Apache 2.0 license notice preserved below:
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

namespace OAI.Tingley

variable {E : Type*} [PseudoMetricSpace E]

/-- Every pair of points in a set is at distance at most the given radius. -/
def DiameterLE (A : Set E) (δ : ℝ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ δ

end OAI.Tingley

-- Adapted from OAI.Analysis.SphereIsometry.ProbabilitySimplex

namespace OAI

/-!
# Finite probability simplices

The coordinates are nonnegative real numbers with sum one. The positive-coordinate
selection lemma is the boundary-compatible labelling rule used in Sperner's argument.
-/

open scoped BigOperators

namespace Tingley

def probabilitySimplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

theorem convex_probabilitySimplexSet (ι : Type*) [Fintype ι] :
    Convex ℝ (probabilitySimplexSet ι) := by
  intro left hleft right hright first second hfirst hsecond hsum
  refine ⟨fun index => add_nonneg (mul_nonneg hfirst (hleft.1 index))
    (mul_nonneg hsecond (hright.1 index)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hleft.2, hright.2, mul_one, hsum]

theorem single_mem_probabilitySimplexSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (index : ι) : Pi.single index 1 ∈ probabilitySimplexSet ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

theorem mem_Icc_of_mem_probabilitySimplexSet {ι : Type*} [Fintype ι]
    {weights : ι → ℝ} (hweights : weights ∈ probabilitySimplexSet ι) (index : ι) :
    weights index ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hweights.1 index, hweights.2 ▸
    Finset.single_le_sum (fun other _ => hweights.1 other) (Finset.mem_univ index)⟩

abbrev ProbabilitySimplex (ι : Type*) [Fintype ι] := ↥(probabilitySimplexSet ι)

instance probabilitySimplex_compactSpace (ι : Type*) [Fintype ι] :
    CompactSpace (ProbabilitySimplex ι) := by
  apply isCompact_iff_compactSpace.mp
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1))
  · change IsClosed ({weights : ι → ℝ | ∀ index, 0 ≤ weights index} ∩
      {weights | ∑ index, weights index = 1})
    apply IsClosed.inter
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun index =>
        isClosed_le continuous_const (continuous_apply index)
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro weights hweights
    exact ⟨fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).1,
      fun index => (mem_Icc_of_mem_probabilitySimplexSet hweights index).2⟩

namespace ProbabilitySimplex

variable {ι : Type*} [Fintype ι]

theorem coordinate_nonneg (a : ProbabilitySimplex ι) (i : ι) : 0 ≤ a.val i :=
  a.property.1 i

theorem sum_coordinates (a : ProbabilitySimplex ι) : ∑ i, a.val i = 1 :=
  a.property.2

noncomputable def pointMass (i : ι) : ProbabilitySimplex ι := by
  classical
  exact ⟨Pi.single i 1, single_mem_probabilitySimplexSet i⟩

instance [Nonempty ι] : Nonempty (ProbabilitySimplex ι) :=
  ⟨pointMass (Classical.choice ‹Nonempty ι›)⟩

theorem exists_positive_coordinate (a : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i := by
  classical
  by_contra h
  have hz : a.val = 0 := by
    funext i
    exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (a.coordinate_nonneg i)
  have hs := a.sum_coordinates
  simp [hz] at hs

theorem eq_of_coordinate_le (a b : ProbabilitySimplex ι)
    (hab : ∀ i, a.val i ≤ b.val i) : a = b := by
  classical
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ b.val i - a.val i :=
    fun i _ => sub_nonneg.mpr (hab i)
  have hsum : ∑ i, (b.val i - a.val i) = 0 := by
    rw [Finset.sum_sub_distrib, b.sum_coordinates, a.sum_coordinates, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  apply Subtype.ext
  funext i
  exact (sub_eq_zero.mp (hz i (Finset.mem_univ i))).symm

end ProbabilitySimplex

theorem exists_positive_dominating_coordinate {ι : Type*} [Fintype ι]
    (a b : ProbabilitySimplex ι) :
    ∃ i, 0 < a.val i ∧ b.val i ≤ a.val i := by
  classical
  by_contra h
  have hstrict : ∀ i, 0 < a.val i → a.val i < b.val i := by
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, hi, hle⟩)
  have hweak : ∀ i, a.val i ≤ b.val i := by
    intro i
    by_cases hi : 0 < a.val i
    · exact (hstrict i hi).le
    · have hz : a.val i = 0 :=
        le_antisymm (le_of_not_gt hi) (a.coordinate_nonneg i)
      rw [hz]
      exact b.coordinate_nonneg i
  obtain ⟨i, hi⟩ := a.exists_positive_coordinate
  have hsum : (∑ j, a.val j) < ∑ j, b.val j :=
    Finset.sum_lt_sum (fun j _ => hweak j) ⟨i, Finset.mem_univ i, hstrict i hi⟩
  rw [a.sum_coordinates, b.sum_coordinates] at hsum
  exact (lt_irrefl (1 : ℝ)) hsum

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SimplexLimit

namespace OAI

/-!
# Extracting a fixed point from shrinking labelled simplex cells

The analytic limit step of the simplex fixed-point argument starts with
a concrete family of simplex points, one for each coordinate at every subdivision level.
The finite Sperner argument supplies this family, and the subdivision estimates supply its
shrinking diameter. No fixed-point principle is assumed here.
-/

open Filter
open scoped BigOperators Topology

namespace Tingley

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Relabelling the coordinates is a homeomorphism of probability simplexes. -/
def probabilitySimplexReindex (e : ι ≃ κ) : ProbabilitySimplex ι ≃ₜ ProbabilitySimplex κ where
  toFun x :=
    ⟨fun j => x.val (e.symm j),
      ⟨fun j => x.property.1 _, (e.symm.sum_comp x.val).trans x.property.2⟩⟩
  invFun y :=
    ⟨fun i => y.val (e i),
      ⟨fun i => y.property.1 _, (e.sum_comp y.val).trans y.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (e.symm_apply_apply i)
  right_inv y := by
    apply Subtype.ext
    funext j
    exact congrArg y.val (e.apply_symm_apply j)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun j =>
      (continuous_apply (e.symm j)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (continuous_apply (e i)).comp continuous_subtype_val

@[simp]
theorem probabilitySimplexReindex_apply_val (e : ι ≃ κ) (x : ProbabilitySimplex ι) (j : κ) :
    (probabilitySimplexReindex e x).val j = x.val (e.symm j) := rfl

@[simp]
theorem probabilitySimplexReindex_symm_apply_val (e : ι ≃ κ) (y : ProbabilitySimplex κ) (i : ι) :
    ((probabilitySimplexReindex e).symm y).val i = y.val (e i) := rfl

variable [Nonempty ι]

/-- Coordinate inequalities at points in shrinking cells produce an actual fixed point.

Only one sequence is passed to compactness. The mesh estimate forces all the coordinate-labelled
sequences along that same subsequence to converge to the same simplex point. -/
theorem probabilitySimplex_fixedPoint_of_shrinking_family
    (P : ProbabilitySimplex ι → ProbabilitySimplex ι) (hP : Continuous P)
    (a : ℕ → ι → ProbabilitySimplex ι) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i j, dist (a k i) (a k j) ≤ δ k)
    (hcoordinate : ∀ k i, (P (a k i)).val i ≤ (a k i).val i) :
    ∃ x, P x = x := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨x, φ, hφ, hx⟩ := CompactSpace.tendsto_subseq (fun k => a k i₀)
  have hδφ : Tendsto (fun k => δ (φ k)) atTop (𝓝 0) :=
    hδ.comp hφ.tendsto_atTop
  have ha : ∀ i, Tendsto (fun k => a (φ k) i) atTop (𝓝 x) := by
    intro i
    apply hx.congr_dist
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun k => hmesh (φ k) i₀ i) hδφ
  have hle : ∀ i, (P x).val i ≤ x.val i := by
    intro i
    have hc : Continuous (fun y : ProbabilitySimplex ι => y.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact le_of_tendsto_of_tendsto'
      (((hc.comp hP).tendsto x).comp (ha i))
      ((hc.tendsto x).comp (ha i))
      (fun k => hcoordinate (φ k) i)
  have hsum : (∑ i, (x.val i - (P x).val i)) = 0 := by
    rw [Finset.sum_sub_distrib, x.property.2, (P x).property.2, sub_self]
  have hzero : ∀ i ∈ Finset.univ, x.val i - (P x).val i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hle i))).mp hsum
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext i
  exact (sub_eq_zero.mp (hzero i (Finset.mem_univ i))).symm

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.FiniteComplex

namespace OAI

/-!
# Finite complexes and their actual face-chain subdivision

The empty face is included. A subdivision vertex is always a nonempty old
face, and a subdivision face is an actual finite inclusion-chain.
-/

noncomputable section

namespace Tingley

universe u v

structure FiniteComplex (V : Type u) [Fintype V] [DecidableEq V] where
  faces : Finset (Finset V)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

namespace FiniteComplex

variable {V : Type u} [Fintype V] [DecidableEq V]

def full : FiniteComplex V where
  faces := Finset.univ
  empty_mem := Finset.mem_univ _
  down_closed := fun _ _ => Finset.mem_univ _

@[simp] theorem mem_full (s : Finset V) : s ∈ (full : FiniteComplex V).faces :=
  Finset.mem_univ _

abbrev FaceVertex (K : FiniteComplex V) :=
  {s : Finset V // s ∈ K.faces ∧ s.Nonempty}

instance (K : FiniteComplex V) : Fintype (FaceVertex K) := by
  classical
  unfold FaceVertex
  infer_instance

def chain (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Prop :=
  ∀ a ∈ c, ∀ b ∈ c, a.val ⊆ b.val ∨ b.val ⊆ a.val

theorem chain_mono {K : FiniteComplex V} {c d : Finset (FaceVertex K)}
    (hc : K.chain c) (hd : d ⊆ c) : K.chain d :=
  fun a ha b hb => hc a (hd ha) b (hd hb)

def sd (K : FiniteComplex V) : FiniteComplex (FaceVertex K) := by
  classical
  exact
    { faces := Finset.univ.filter K.chain
      empty_mem := by simp [chain]
      down_closed := by
        intro s t hs hts
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, K.chain_mono (Finset.mem_filter.mp hs).2 hts⟩ }

@[simp] theorem mem_sd_iff {K : FiniteComplex V} {c : Finset (FaceVertex K)} :
    c ∈ K.sd.faces ↔ K.chain c := by
  classical
  simp [sd]

def topCells (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m + 1)

def codimFaces (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m)

def incidentTop (K : FiniteComplex V) (m : ℕ) (s : Finset V) : Finset (Finset V) :=
  (K.topCells m).filter (fun t => s ⊆ t)

@[simp] theorem mem_topCells {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.topCells m ↔ s ∈ K.faces ∧ s.card = m + 1 :=
  Finset.mem_filter

@[simp] theorem mem_codimFaces {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.codimFaces m ↔ s ∈ K.faces ∧ s.card = m :=
  Finset.mem_filter

@[simp] theorem mem_incidentTop {K : FiniteComplex V} {m : ℕ}
    {s t : Finset V} :
    t ∈ K.incidentTop m s ↔ t ∈ K.faces ∧ t.card = m + 1 ∧ s ⊆ t := by
  simp [incidentTop, and_assoc]

def CardBound (K : FiniteComplex V) (m : ℕ) : Prop :=
  ∀ s ∈ K.faces, s.card ≤ m + 1

def Pure (K : FiniteComplex V) (m : ℕ) : Prop :=
  ∀ s ∈ K.faces, ∃ t ∈ K.topCells m, s ⊆ t

theorem Pure.cardBound {K : FiniteComplex V} {m : ℕ} (h : K.Pure m) :
    K.CardBound m := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := h s hs
  exact (Finset.card_le_card hst).trans_eq (mem_topCells.mp ht).2

variable {I : Type v} [DecidableEq I]

def faceCarrier (carrier : V → Finset I) (s : Finset V) : Finset I :=
  s.biUnion carrier

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_faceCarrier {carrier : V → Finset I} {s : Finset V} {i : I} :
    i ∈ faceCarrier carrier s ↔ ∃ v ∈ s, i ∈ carrier v :=
  Finset.mem_biUnion

omit [Fintype V] [DecidableEq V] in
theorem faceCarrier_mono (carrier : V → Finset I) {s t : Finset V} (h : s ⊆ t) :
    faceCarrier carrier s ⊆ faceCarrier carrier t :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_empty (carrier : V → Finset I) :
    faceCarrier carrier ∅ = ∅ := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_singleton (carrier : V → Finset I) (v : V) :
    faceCarrier carrier {v} = carrier v := by
  simp [faceCarrier]

def sdCarrier (K : FiniteComplex V) (carrier : V → Finset I) :
    FaceVertex K → Finset I := fun s => faceCarrier carrier s.val

theorem sdCarrier_nonempty {K : FiniteComplex V} {carrier : V → Finset I}
    (h : ∀ v, (carrier v).Nonempty) (s : FaceVertex K) :
    (K.sdCarrier carrier s).Nonempty := by
  obtain ⟨v, hv⟩ := s.property.2
  obtain ⟨i, hi⟩ := h v
  exact ⟨i, mem_faceCarrier.mpr ⟨v, hv, hi⟩⟩

end FiniteComplex

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricFlags

namespace OAI

/-! # Ranks and carriers of finite face-chains -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

theorem chain_eq_of_card_eq {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card = b.val.card) :
    a = b := by
  apply Subtype.ext
  rcases hc a ha b hb with hab | hba
  · exact Finset.eq_of_subset_of_card_le hab h.ge
  · exact (Finset.eq_of_subset_of_card_le hba h.le).symm

theorem chain_subset_of_card_le {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a b : FaceVertex K} (ha : a ∈ c) (hb : b ∈ c) (h : a.val.card ≤ b.val.card) :
    a.val ⊆ b.val := by
  rcases hc a ha b hb with hab | hba
  · exact hab
  · intro x hx
    rw [Finset.eq_of_subset_of_card_le hba h]
    exact hx

def ranks (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Finset ℕ :=
  c.image (fun a => a.val.card)

@[simp] theorem mem_ranks {c : Finset (FaceVertex K)} {r : ℕ} :
    r ∈ K.ranks c ↔ ∃ a ∈ c, a.val.card = r :=
  Finset.mem_image

theorem card_ranks {c : Finset (FaceVertex K)} (hc : K.chain c) :
    (K.ranks c).card = c.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact chain_eq_of_card_eq hc ha hb hab

theorem ranks_subset {m : ℕ} (hK : K.CardBound m) (c : Finset (FaceVertex K)) :
    K.ranks c ⊆ Finset.Icc 1 (m + 1) := by
  intro r hr
  obtain ⟨a, _, rfl⟩ := mem_ranks.mp hr
  exact Finset.mem_Icc.mpr
    ⟨Finset.card_pos.mpr a.property.2, hK a.val a.property.1⟩

theorem sd_cardBound {m : ℕ} (hK : K.CardBound m) : K.sd.CardBound m := by
  intro c hc
  have h := Finset.card_le_card (ranks_subset hK c)
  rw [card_ranks (mem_sd_iff.mp hc)] at h
  simpa using h

theorem top_ranks {m : ℕ} (hK : K.CardBound m) {c : Finset (FaceVertex K)}
    (hc : c ∈ K.sd.topCells m) : K.ranks c = Finset.Icc 1 (m + 1) := by
  obtain ⟨hc, hcard⟩ := mem_topCells.mp hc
  apply Finset.eq_of_subset_of_card_le (ranks_subset hK c)
  rw [card_ranks (mem_sd_iff.mp hc), hcard]
  simp

theorem missing_rank {m : ℕ} (hK : K.CardBound m) {c : Finset (FaceVertex K)}
    (hc : c ∈ K.sd.codimFaces m) :
    ∃ r, 1 ≤ r ∧ r ≤ m + 1 ∧ K.ranks c = (Finset.Icc 1 (m + 1)).erase r := by
  obtain ⟨hchain, hcard⟩ := mem_codimFaces.mp hc
  have hsub := ranks_subset hK c
  have hd : ((Finset.Icc 1 (m + 1)) \ K.ranks c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, card_ranks (mem_sd_iff.mp hchain), hcard]
    simp
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hd
  have hrmem : r ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c := by
    rw [hr]
    exact Finset.mem_singleton_self _
  obtain ⟨hrI, hrnot⟩ := Finset.mem_sdiff.mp hrmem
  refine ⟨r, (Finset.mem_Icc.mp hrI).1, (Finset.mem_Icc.mp hrI).2, ?_⟩
  ext q
  constructor
  · intro hq
    exact Finset.mem_erase.mpr ⟨fun hqr => hrnot (hqr ▸ hq), hsub hq⟩
  · intro hq
    obtain ⟨hqr, hqI⟩ := Finset.mem_erase.mp hq
    by_contra hnot
    have : q ∈ (Finset.Icc 1 (m + 1)) \ K.ranks c :=
      Finset.mem_sdiff.mpr ⟨hqI, hnot⟩
    rw [hr] at this
    exact hqr (Finset.mem_singleton.mp this)

theorem exists_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    (hne : c.Nonempty) : ∃ a ∈ c, ∀ b ∈ c, b.val ⊆ a.val := by
  obtain ⟨a, ha, hmax⟩ := c.exists_max_image (fun b => b.val.card) hne
  exact ⟨a, ha, fun b hb => chain_subset_of_card_le hc hb ha (hmax b hb)⟩

theorem card_le_greatest {c : Finset (FaceVertex K)} (hc : K.chain c)
    {a : FaceVertex K} (_ha : a ∈ c) (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    c.card ≤ a.val.card := by
  have hsub : K.ranks c ⊆ Finset.Icc 1 a.val.card := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := mem_ranks.mp hr
    exact Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr b.property.2, Finset.card_le_card (hmax b hb)⟩
  have h := Finset.card_le_card hsub
  rw [card_ranks hc] at h
  simpa using h

variable {I : Type v} [DecidableEq I]

theorem faceCarrier_sd_eq_greatest {carrier : V → Finset I}
    {c : Finset (FaceVertex K)} {a : FaceVertex K} (ha : a ∈ c)
    (hmax : ∀ b ∈ c, b.val ⊆ a.val) :
    faceCarrier (K.sdCarrier carrier) c = faceCarrier carrier a.val := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨b, hb, hbi⟩ := mem_faceCarrier.mp hi
    exact faceCarrier_mono carrier (hmax b hb) hbi
  · intro i hi
    exact mem_faceCarrier.mpr ⟨a, ha, hi⟩

theorem sd_card_le_carrier {carrier : V → Finset I}
    (hK : ∀ s ∈ K.faces, s.card ≤ (faceCarrier carrier s).card)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.faces) :
    c.card ≤ (faceCarrier (K.sdCarrier carrier) c).card := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨a, ha, hmax⟩ := exists_greatest (mem_sd_iff.mp hc) hne
    rw [faceCarrier_sd_eq_greatest ha hmax]
    exact (card_le_greatest (mem_sd_iff.mp hc) ha hmax).trans (hK a.val a.property.1)

end Tingley.FiniteComplex

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SubdivisionData

namespace OAI

/-! # The concrete recursively iterated subdivision of a finite simplex -/

noncomputable section

namespace Tingley

structure CarrierComplex (I : Type) [DecidableEq I] where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  complex : FiniteComplex Vertex
  carrier : Vertex → Finset I

instance {I : Type} [DecidableEq I] (D : CarrierComplex I) : Fintype D.Vertex := D.vertexFintype
instance {I : Type} [DecidableEq I] (D : CarrierComplex I) : DecidableEq D.Vertex := D.vertexDecidableEq

namespace CarrierComplex

variable {I : Type} [DecidableEq I]

def sd (D : CarrierComplex I) : CarrierComplex I where
  Vertex := FiniteComplex.FaceVertex D.complex
  complex := D.complex.sd
  carrier := D.complex.sdCarrier D.carrier

def initial (I : Type) [Fintype I] [DecidableEq I] : CarrierComplex I where
  Vertex := I
  complex := FiniteComplex.full
  carrier := fun i => {i}

end CarrierComplex

def iterData (I : Type) [Fintype I] [DecidableEq I] : ℕ → CarrierComplex I
  | 0 => CarrierComplex.initial I
  | n + 1 => (iterData I n).sd

abbrev IterVertex (m k : ℕ) := (iterData (Fin (m + 1)) k).Vertex

def iterComplex (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.faces

def iterCarrier (m k : ℕ) : IterVertex m k → Finset (Fin (m + 1)) :=
  (iterData (Fin (m + 1)) k).carrier

def topCells (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.topCells m

def codimFaces (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.codimFaces m

def faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) : Finset (Fin (m + 1)) :=
  FiniteComplex.faceCarrier (iterCarrier m k) s

def incidentTop (m k : ℕ) (s : Finset (IterVertex m k)) :
    Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.incidentTop m s

@[simp] theorem mem_topCells {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ topCells m k ↔ s ∈ iterComplex m k ∧ s.card = m + 1 :=
  FiniteComplex.mem_topCells

@[simp] theorem mem_codimFaces {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ codimFaces m k ↔ s ∈ iterComplex m k ∧ s.card = m :=
  FiniteComplex.mem_codimFaces

@[simp] theorem mem_incidentTop {m k : ℕ} {s t : Finset (IterVertex m k)} :
    t ∈ incidentTop m k s ↔
      t ∈ iterComplex m k ∧ t.card = m + 1 ∧ s ⊆ t :=
  FiniteComplex.mem_incidentTop

theorem iterComplex_empty_mem (m k : ℕ) : ∅ ∈ iterComplex m k :=
  (iterData (Fin (m + 1)) k).complex.empty_mem

theorem iterComplex_down_closed {m k : ℕ} {s t : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) (ht : t ⊆ s) : t ∈ iterComplex m k :=
  (iterData (Fin (m + 1)) k).complex.down_closed hs ht

theorem iterData_carrier_nonempty (I : Type) [Fintype I] [DecidableEq I] (k : ℕ) :
    ∀ v : (iterData I k).Vertex, ((iterData I k).carrier v).Nonempty := by
  induction k with
  | zero => intro v; exact Finset.singleton_nonempty v
  | succ k ih => exact FiniteComplex.sdCarrier_nonempty ih

theorem iterData_card_le_carrier (I : Type) [Fintype I] [DecidableEq I] (k : ℕ) :
    ∀ s ∈ (iterData I k).complex.faces,
      s.card ≤ (FiniteComplex.faceCarrier (iterData I k).carrier s).card := by
  induction k with
  | zero =>
      intro s hs
      simp [iterData, CarrierComplex.initial, FiniteComplex.faceCarrier]
      exact (congrArg (fun t : Finset I => t.card)
        (Finset.biUnion_singleton_eq_self (s := s))).ge
  | succ k ih =>
      intro s hs
      exact FiniteComplex.sd_card_le_carrier ih hs

theorem iter_card_le_carrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ (faceCarrier m k s).card :=
  iterData_card_le_carrier (Fin (m + 1)) k s hs

theorem iter_card_le {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ m + 1 := by
  have h := (iter_card_le_carrier hs).trans (Finset.card_le_univ (faceCarrier m k s))
  simpa using h

theorem top_faceCarrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) : faceCarrier m k s = Finset.univ := by
  obtain ⟨hs, hcard⟩ := mem_topCells.mp hs
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [hcard] using iter_card_le_carrier hs

theorem codim_faceCarrier_card {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ codimFaces m k) :
    (faceCarrier m k s).card = m ∨ (faceCarrier m k s).card = m + 1 := by
  obtain ⟨hs, hcard⟩ := mem_codimFaces.mp hs
  have hlo := iter_card_le_carrier hs
  have hhi : (faceCarrier m k s).card ≤ m + 1 := by
    simpa using Finset.card_le_univ (faceCarrier m k s)
  omega

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricBasic

namespace OAI

/-!
# Finite barycenters

The point attached to a nonempty face in barycentric subdivision is its
ordinary finite average. The definition also assigns zero to the empty set.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V W E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def finiteBarycenter (p : V → E) (S : Finset V) : E :=
  (S.card : ℝ)⁻¹ • ∑ v ∈ S, p v

theorem finiteBarycenter_eq_centerMass (p : V → E) (S : Finset V) :
    finiteBarycenter p S = S.centerMass (fun _ => (1 : ℝ)) p := by
  simp [finiteBarycenter, Finset.centerMass]

@[simp] theorem finiteBarycenter_empty (p : V → E) :
    finiteBarycenter p ∅ = 0 := by
  simp [finiteBarycenter]

@[simp] theorem finiteBarycenter_singleton (p : V → E) (v : V) :
    finiteBarycenter p {v} = p v := by
  simp [finiteBarycenter]

theorem finiteBarycenter_congr {p q : V → E} {S : Finset V}
    (h : ∀ v ∈ S, p v = q v) :
    finiteBarycenter p S = finiteBarycenter q S := by
  unfold finiteBarycenter
  congr 1
  exact Finset.sum_congr rfl h

theorem finiteBarycenter_mem_convex {K : Set E} (hK : Convex ℝ K)
    {p : V → E} {S : Finset V} (hs : S.Nonempty)
    (hp : ∀ v ∈ S, p v ∈ K) : finiteBarycenter p S ∈ K := by
  rw [finiteBarycenter_eq_centerMass]
  apply hK.centerMass_mem
  · intro v hv
    exact zero_le_one
  · simpa using (Nat.cast_pos.mpr (Finset.card_pos.mpr hs) : 0 < (S.card : ℝ))
  · exact hp

theorem finiteBarycenter_mem_convexHull {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) :
    finiteBarycenter p S ∈ convexHull ℝ (p '' (↑T : Set V)) := by
  apply finiteBarycenter_mem_convex (convex_convexHull ℝ _) hs
  intro v hv
  exact subset_convexHull ℝ _ ⟨v, hst hv, rfl⟩

theorem map_finiteBarycenter (L : E →ₗ[ℝ] F) (p : V → E) (S : Finset V) :
    L (finiteBarycenter p S) = finiteBarycenter (L ∘ p) S := by
  simp [finiteBarycenter]

theorem finiteBarycenter_map (e : V ↪ W) (p : W → E) (S : Finset V) :
    finiteBarycenter p (S.map e) = finiteBarycenter (p ∘ e) S := by
  simp [finiteBarycenter]

theorem finiteBarycenter_map_of_eq (e : V ↪ W) (p : V → E) (q : W → E)
    (S : Finset V) (h : ∀ v ∈ S, q (e v) = p v) :
    finiteBarycenter q (S.map e) = finiteBarycenter p S := by
  rw [finiteBarycenter_map]
  exact finiteBarycenter_congr h

theorem finiteBarycenter_apply {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (S : Finset V) (i : ι) :
    finiteBarycenter p S i = (S.card : ℝ)⁻¹ * ∑ v ∈ S, p v i := by
  simp [finiteBarycenter, Finset.sum_apply]

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricSupport

namespace OAI

/-!
# Supports of finite barycenters

A nonempty average of simplex vectors is a simplex vector. Its strict-positive
coordinate support is exactly the union of the supports being averaged.
These statements concern the actual finite average and require no geometric
coverage assumption.
-/

noncomputable section

open scoped BigOperators Classical

namespace Tingley

variable {V ι : Type*} [Fintype ι]

/-- The coordinates at which a vector is strictly positive. -/
def positiveCarrier (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < x i)

@[simp] theorem mem_positiveCarrier {x : ι → ℝ} {i : ι} :
    i ∈ positiveCarrier x ↔ 0 < x i := by
  simp [positiveCarrier]

/-- Outside the positive carrier, a nonnegative vector has zero coordinates. -/
theorem not_mem_positiveCarrier_iff {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (i : ι) :
    i ∉ positiveCarrier x ↔ x i = 0 := by
  rw [mem_positiveCarrier, not_lt]
  exact ⟨fun h => le_antisymm h (hx i), fun h => h.le⟩

/-- Containment in a coordinate face is exactly vanishing outside that face. -/
theorem positiveCarrier_subset_iff {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (I : Finset ι) :
    positiveCarrier x ⊆ I ↔ ∀ i, i ∉ I → x i = 0 := by
  constructor
  · intro h i hi
    apply (not_mem_positiveCarrier_iff hx i).mp
    intro hix
    exact hi (h hix)
  · intro h i hi
    by_contra hn
    have hzero := h i hn
    have hpos := mem_positiveCarrier.mp hi
    rw [hzero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos

/-- Finite averaging preserves nonnegative coordinates, including for the empty set. -/
theorem finiteBarycenter_apply_nonneg (p : V → ι → ℝ) (S : Finset V)
    (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) (i : ι) :
    0 ≤ finiteBarycenter p S i := by
  rw [finiteBarycenter_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg S.card))
    (Finset.sum_nonneg (fun v hv => hp v hv i))

/-- A nonempty finite average stays in the standard simplex. -/
theorem finiteBarycenter_mem_stdSimplex (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, p v ∈ probabilitySimplexSet ι) :
    finiteBarycenter p S ∈ probabilitySimplexSet ι := by
  exact finiteBarycenter_mem_convex (convex_probabilitySimplexSet ι) hs hp

/-- A coordinate of a nonempty nonnegative average is positive exactly when
one of the averaged coordinates is positive. -/
theorem finiteBarycenter_pos_iff (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) (i : ι) :
    0 < finiteBarycenter p S i ↔ ∃ v ∈ S, 0 < p v i := by
  have hcard : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hinv : 0 < (S.card : ℝ)⁻¹ := inv_pos.mpr hcard
  rw [finiteBarycenter_apply]
  constructor
  · intro h
    have hsum : 0 < ∑ v ∈ S, p v i := pos_of_mul_pos_right h hinv.le
    by_contra hn
    have hzero : ∀ v ∈ S, p v i = 0 := by
      intro v hv
      apply le_antisymm _ (hp v hv i)
      exact le_of_not_gt (fun hpos => hn ⟨v, hv, hpos⟩)
    have heq : ∑ v ∈ S, p v i = 0 := Finset.sum_eq_zero hzero
    rw [heq] at hsum
    exact (lt_irrefl (0 : ℝ)) hsum
  · intro h
    exact mul_pos hinv (Finset.sum_pos' (fun v hv => hp v hv i) h)

/-- The support of a nonempty nonnegative average is the exact support union. -/
theorem positiveCarrier_finiteBarycenter (p : V → ι → ℝ) {S : Finset V}
    (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i) :
    positiveCarrier (finiteBarycenter p S) =
      S.biUnion (fun v => positiveCarrier (p v)) := by
  ext i
  simp only [mem_positiveCarrier, Finset.mem_biUnion]
  exact finiteBarycenter_pos_iff p hs hp i

/-- The new vertex belongs to an original coordinate face exactly when every
averaged vertex belongs to that face. -/
theorem positiveCarrier_finiteBarycenter_subset_iff (p : V → ι → ℝ)
    {S : Finset V} (hs : S.Nonempty) (hp : ∀ v ∈ S, ∀ i, 0 ≤ p v i)
    (I : Finset ι) :
    positiveCarrier (finiteBarycenter p S) ⊆ I ↔
      ∀ v ∈ S, positiveCarrier (p v) ⊆ I := by
  rw [positiveCarrier_finiteBarycenter p hs hp]
  exact Finset.biUnion_subset

/-- A simplex vector has a positive coordinate because its total mass is one. -/
theorem positiveCarrier_nonempty_of_mem_stdSimplex {x : ι → ℝ}
    (hx : x ∈ probabilitySimplexSet ι) : (positiveCarrier x).Nonempty := by
  by_contra hn
  have hzero : ∀ i, x i = 0 := by
    intro i
    apply le_antisymm _ (hx.1 i)
    exact le_of_not_gt (fun hpos => hn ⟨i, mem_positiveCarrier.mpr hpos⟩)
  have hsum : ∑ i, x i = 0 := Finset.sum_eq_zero (fun i _ => hzero i)
  exact one_ne_zero (hx.2.symm.trans hsum)

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.ConvexDiameter

namespace OAI

/-! # Diameter bounds for convex hulls

Convex hulls preserve diameter bounds.
-/

namespace Tingley

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taking a convex hull preserves a pairwise diameter bound. -/
theorem DiameterLE.convexHull {A : Set E} {δ : ℝ} (h : DiameterLE A δ) :
    DiameterLE (convexHull ℝ A) δ := by
  intro x hx y hy
  obtain ⟨x', hx', y', hy', hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans (h x' hx' y' hy')

/-- A norm bound on a set also holds on its convex hull. -/
theorem norm_le_of_mem_convexHull {A : Set E} {R : ℝ}
    (hR : ∀ x ∈ A, ‖x‖ ≤ R) {x : E} (hx : x ∈ convexHull ℝ A) : ‖x‖ ≤ R := by
  have hsub : A ⊆ Metric.closedBall (0 : E) R := by
    intro y hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR y hy
  have hxball := convexHull_min hsub (convex_closedBall (0 : E) R) hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hxball

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricMesh

namespace OAI

/-!
# The mesh estimate for barycentric subdivision

The larger face is split into the smaller face and its complement. Its
barycenter is the corresponding weighted average, giving the exact factor
`1 - S.card / T.card`. A dimension bound gives the uniform contraction.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq V] in
theorem norm_finiteBarycenter_sub_le_of_subsets {p : V → E}
    {S R T : Finset V} {D : ℝ} (hs : S.Nonempty) (hr : R.Nonempty)
    (hst : S ⊆ T) (hrt : R ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p R‖ ≤ D := by
  have hdiam : DiameterLE (p '' (↑T : Set V)) D := by
    rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
    simpa only [dist_eq_norm] using hpair u hu v hv
  have h := hdiam.convexHull
    (finiteBarycenter p S) (finiteBarycenter_mem_convexHull hs hst)
    (finiteBarycenter p R) (finiteBarycenter_mem_convexHull hr hrt)
  simpa only [dist_eq_norm] using h

theorem finiteBarycenter_partition {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) (hr : (T \ S).Nonempty) :
    finiteBarycenter p T =
      ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S +
      (((T \ S).card : ℝ) / (T.card : ℝ)) • finiteBarycenter p (T \ S) := by
  classical
  have hs0 : (S.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
  have hr0 : ((T \ S).card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hr))
  have ht0 : (T.card : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr (hs.mono hst)))
  have hS : ((S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S =
      (T.card : ℝ)⁻¹ • ∑ v ∈ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hs0, ht0]
  have hR : (((T \ S).card : ℝ) / (T.card : ℝ)) •
      finiteBarycenter p (T \ S) =
      (T.card : ℝ)⁻¹ • ∑ v ∈ T \ S, p v := by
    rw [finiteBarycenter, smul_smul]
    congr 1
    field_simp [hr0, ht0]
  rw [hS, hR, ← smul_add]
  unfold finiteBarycenter
  congr 1
  simpa only [add_comm] using (Finset.sum_sdiff (f := p) hst).symm

theorem norm_finiteBarycenter_sub_le_card {p : V → E}
    {S T : Finset V} {D : ℝ} (hs : S.Nonempty) (hst : S ⊆ T)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      (1 - (S.card : ℝ) / (T.card : ℝ)) * D := by
  classical
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  by_cases heq : S = T
  · subst S
    simp [ne_of_gt htpos]
  have hr : (T \ S).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hts
    exact heq (Finset.Subset.antisymm hst hts))
  have hcard : ((T \ S).card : ℝ) + (S.card : ℝ) = (T.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hst
  have hfrac : ((T \ S).card : ℝ) / (T.card : ℝ) =
      1 - (S.card : ℝ) / (T.card : ℝ) := by
    apply (div_eq_iff (ne_of_gt htpos)).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt htpos)]
    linarith
  have hnonneg : 0 ≤ ((T \ S).card : ℝ) / (T.card : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) htpos.le
  have hid : finiteBarycenter p S - finiteBarycenter p T =
      (((T \ S).card : ℝ) / (T.card : ℝ)) •
        (finiteBarycenter p S - finiteBarycenter p (T \ S)) := by
    calc
      finiteBarycenter p S - finiteBarycenter p T =
          (1 - (S.card : ℝ) / (T.card : ℝ)) • finiteBarycenter p S -
            (((T \ S).card : ℝ) / (T.card : ℝ)) •
              finiteBarycenter p (T \ S) := by
        rw [finiteBarycenter_partition hs hst hr, sub_smul, one_smul]
        abel
      _ = _ := by rw [← hfrac, smul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    ((T \ S).card : ℝ) / (T.card : ℝ) *
        ‖finiteBarycenter p S - finiteBarycenter p (T \ S)‖ ≤
        ((T \ S).card : ℝ) / (T.card : ℝ) * D :=
      mul_le_mul_of_nonneg_left
        (norm_finiteBarycenter_sub_le_of_subsets hs hr hst Finset.sdiff_subset hpair)
        hnonneg
    _ = _ := by rw [hfrac]

theorem norm_finiteBarycenter_sub_le_mesh {p : V → E}
    {S T : Finset V} {D : ℝ} (m : ℕ) (hD : 0 ≤ D)
    (hs : S.Nonempty) (hst : S ⊆ T) (hcard : T.card ≤ m + 1)
    (hpair : ∀ u ∈ T, ∀ v ∈ T, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      ((m : ℝ) / (m + 1 : ℝ)) * D := by
  have ht : T.Nonempty := hs.mono hst
  have htpos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  have hmpos : 0 < (m + 1 : ℝ) := by positivity
  have hsone : (1 : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hs))
  have htcard : (T.card : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast hcard
  have hlow : 1 / (m + 1 : ℝ) ≤ (S.card : ℝ) / (T.card : ℝ) := by
    calc
      1 / (m + 1 : ℝ) ≤ 1 / (T.card : ℝ) :=
        one_div_le_one_div_of_le htpos htcard
      _ ≤ (S.card : ℝ) / (T.card : ℝ) :=
        (div_le_div_iff_of_pos_right htpos).2 hsone
  have hfactor : 1 - (S.card : ℝ) / (T.card : ℝ) ≤
      (m : ℝ) / (m + 1 : ℝ) := by
    have heq : (m : ℝ) / (m + 1 : ℝ) = 1 - 1 / (m + 1 : ℝ) := by
      apply (div_eq_iff (ne_of_gt hmpos)).2
      rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hmpos)]
      ring
    rw [heq]
    linarith
  exact (norm_finiteBarycenter_sub_le_card hs hst hpair).trans
    (mul_le_mul_of_nonneg_right hfactor hD)

theorem norm_finiteBarycenter_sub_le_of_comparable {p : V → E}
    {S T U : Finset V} {D : ℝ} (m : ℕ) (hD : 0 ≤ D)
    (hs : S.Nonempty) (ht : T.Nonempty) (hsu : S ⊆ U) (htu : T ⊆ U)
    (hcmp : S ⊆ T ∨ T ⊆ S) (hcard : U.card ≤ m + 1)
    (hpair : ∀ u ∈ U, ∀ v ∈ U, ‖p u - p v‖ ≤ D) :
    ‖finiteBarycenter p S - finiteBarycenter p T‖ ≤
      ((m : ℝ) / (m + 1 : ℝ)) * D := by
  rcases hcmp with hst | hts
  · exact norm_finiteBarycenter_sub_le_mesh m hD hs hst
      ((Finset.card_le_card htu).trans hcard)
      (fun u hu v hv => hpair u (htu hu) v (htu hv))
  · simpa only [norm_sub_rev] using
      norm_finiteBarycenter_sub_le_mesh m hD ht hts
        ((Finset.card_le_card hsu).trans hcard)
        (fun u hu v hv => hpair u (hsu hu) v (hsu hv))

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricPoints

/-!
# Geometric vertices of barycentric subdivision

Finite averages give simplex membership, exact coordinate support,
naturality, and shrinking mesh.
-/

-- Adapted from OAI.Analysis.SphereIsometry.IteratedPoints

namespace OAI

/-!
# Actual geometric points of iterated subdivision

Initial vertices are coordinate unit vectors. Every later vertex is the finite
barycenter of the nonempty old face that it represents. Simplex membership,
exact carriers, and the geometric mesh bound follow from this recursive formula.
-/

noncomputable section

namespace Tingley

/-- The actual geometric realization of every recursively constructed vertex. -/
def iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    (k : ℕ) → (iterData I k).Vertex → I → ℝ
  | 0, v => Pi.single v 1
  | k + 1, v => finiteBarycenter (iterDataPoint I k) v.val

@[simp] theorem iterDataPoint_zero (I : Type) [Fintype I] [DecidableEq I] (v : I) :
    iterDataPoint I 0 v = Pi.single v 1 := rfl

@[simp] theorem iterDataPoint_succ (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (v : (iterData I (k + 1)).Vertex) :
    iterDataPoint I (k + 1) v = finiteBarycenter (iterDataPoint I k) v.val := rfl

/-- The recursion produces simplex vectors at every level. -/
theorem iterDataPoint_mem_stdSimplex (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      iterDataPoint I k v ∈ probabilitySimplexSet I := by
  intro k
  induction k with
  | zero =>
      intro v
      exact single_mem_probabilitySimplexSet v
  | succ k ih =>
      intro v
      exact finiteBarycenter_mem_stdSimplex (iterDataPoint I k) v.property.2
        (fun u _ => ih u)

/-- The recursively defined combinatorial carrier is exactly the set of
strict-positive coordinates of the actual recursive point. -/
theorem positiveCarrier_iterDataPoint (I : Type) [Fintype I] [DecidableEq I] :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      positiveCarrier (iterDataPoint I k v) = (iterData I k).carrier v := by
  intro k
  induction k with
  | zero =>
      intro v
      change positiveCarrier (Pi.single v (1 : ℝ)) = {v}
      ext i
      by_cases hi : v = i
      · subst i
        simp [positiveCarrier]
      · simp [positiveCarrier, Pi.single_apply, Ne.symm hi]
  | succ k ih =>
      intro v
      change positiveCarrier (finiteBarycenter (iterDataPoint I k) v.val) =
        v.val.biUnion (fun u => (iterData I k).carrier u)
      rw [positiveCarrier_finiteBarycenter (iterDataPoint I k) v.property.2
        (fun u _ i => (iterDataPoint_mem_stdSimplex I k u).1 i)]
      ext i
      simp only [Finset.mem_biUnion, ih]

/-- The coordinate form used by the simplex fixed-point argument. -/
abbrev iterPoint (m k : ℕ) : IterVertex m k → Fin (m + 1) → ℝ :=
  iterDataPoint (Fin (m + 1)) k

@[simp] theorem iterPoint_zero (m : ℕ) (v : Fin (m + 1)) :
    iterPoint m 0 v = Pi.single v 1 := rfl

@[simp] theorem iterPoint_succ (m k : ℕ) (v : IterVertex m (k + 1)) :
    iterPoint m (k + 1) v = finiteBarycenter (iterPoint m k) v.val := rfl

theorem iterPoint_mem_stdSimplex (m k : ℕ) (v : IterVertex m k) :
    iterPoint m k v ∈ probabilitySimplexSet (Fin (m + 1)) :=
  iterDataPoint_mem_stdSimplex (Fin (m + 1)) k v

theorem positiveCarrier_iterPoint (m k : ℕ) (v : IterVertex m k) :
    positiveCarrier (iterPoint m k v) = iterCarrier m k v :=
  positiveCarrier_iterDataPoint (Fin (m + 1)) k v

/-- Exact boundary compatibility of the coordinate labelling rule. -/
theorem iterPoint_pos_iff (m k : ℕ) (v : IterVertex m k) (i : Fin (m + 1)) :
    0 < iterPoint m k v i ↔ i ∈ iterCarrier m k v := by
  rw [← mem_positiveCarrier, positiveCarrier_iterPoint]

/-- Any two probability vectors have distance at most one in the ambient sup norm. -/
theorem norm_sub_le_one_of_mem_stdSimplex {I : Type*} [Fintype I]
    {x y : I → ℝ} (hx : x ∈ probabilitySimplexSet I) (hy : y ∈ probabilitySimplexSet I) :
    ‖x - y‖ ≤ 1 := by
  rw [← dist_eq_norm]
  apply (dist_pi_le_iff zero_le_one).mpr
  intro i
  have hxi := mem_Icc_of_mem_probabilitySimplexSet hx i
  have hyi := mem_Icc_of_mem_probabilitySimplexSet hy i
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- The mesh of each actual level-k face is bounded by the kth power of the
barycentric contraction factor. No face coverage assertion is assumed. -/
theorem iterPoint_mesh (m : ℕ) :
    ∀ (k : ℕ) (s : Finset (IterVertex m k)), s ∈ iterComplex m k →
      ∀ u ∈ s, ∀ v ∈ s,
        ‖iterPoint m k u - iterPoint m k v‖ ≤
          ((m : ℝ) / (m + 1 : ℝ)) ^ k := by
  intro k
  induction k with
  | zero =>
      intro s _ u _ v _
      simpa only [pow_zero] using norm_sub_le_one_of_mem_stdSimplex
        (iterPoint_mem_stdSimplex m 0 u) (iterPoint_mem_stdSimplex m 0 v)
  | succ k ih =>
      intro s hs u hu v hv
      have hchain : (iterData (Fin (m + 1)) k).complex.chain s :=
        FiniteComplex.mem_sd_iff.mp hs
      have hD : 0 ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ k :=
        pow_nonneg (div_nonneg (Nat.cast_nonneg m)
          (add_nonneg (Nat.cast_nonneg m) zero_le_one)) k
      rcases hchain u hu v hv with huv | hvu
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          u.property.2 huv (iter_card_le (m := m) (k := k) v.property.1)
          (ih v.val v.property.1)
        simpa only [iterPoint_succ, pow_succ'] using h
      · have h := norm_finiteBarycenter_sub_le_mesh (p := iterPoint m k) m hD
          v.property.2 hvu (iter_card_le (m := m) (k := k) u.property.1)
          (ih u.val u.property.1)
        calc
          ‖iterPoint m (k + 1) u - iterPoint m (k + 1) v‖ =
              ‖iterPoint m (k + 1) v - iterPoint m (k + 1) u‖ := norm_sub_rev _ _
          _ ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ (k + 1) := by
            simpa only [iterPoint_succ, pow_succ'] using h

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SpernerFacet

namespace OAI

/-!
# The local facet count in geometric Sperner's lemma

A simplex with `m + 1` vertices has an odd number of facets labelled by all
labels except the last precisely when the simplex is fully labelled. The
proof below identifies the good facets explicitly: one in the fully labelled
case, and two whenever a good facet exists but the simplex is not full.
-/

namespace Tingley

/-- The labels on the distinguished boundary face. -/
def spernerSmallLabels (m : ℕ) : Finset (Fin (m + 1)) :=
  Finset.univ.erase (Fin.last m)

@[simp] theorem mem_spernerSmallLabels {m : ℕ} {i : Fin (m + 1)} :
    i ∈ spernerSmallLabels m ↔ i ≠ Fin.last m := by
  simp [spernerSmallLabels]

@[simp] theorem card_spernerSmallLabels (m : ℕ) :
    (spernerSmallLabels m).card = m := by
  simp [spernerSmallLabels]

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- The codimension-one subsets carrying every label except the last. -/
def spernerGoodFacets (m : ℕ) (label : V → Fin (m + 1)) (σ : Finset V) :
    Finset (Finset V) :=
  σ.powerset.filter fun τ => τ.card = m ∧ τ.image label = spernerSmallLabels m

omit [DecidableEq V] in
@[simp] theorem mem_spernerGoodFacets {label : V → Fin (m + 1)}
    {σ τ : Finset V} :
    τ ∈ spernerGoodFacets m label σ ↔
      τ ⊆ σ ∧ τ.card = m ∧ τ.image label = spernerSmallLabels m := by
  simp [spernerGoodFacets]

omit [DecidableEq V] in
/-- A good facet has one vertex of each of its labels. -/
theorem spernerGoodFacet_injOn {label : V → Fin (m + 1)}
    {σ τ : Finset V} (hτ : τ ∈ spernerGoodFacets m label σ) :
    Set.InjOn label (↑τ : Set V) := by
  obtain ⟨_, hc, hi⟩ := mem_spernerGoodFacets.mp hτ
  apply Finset.card_image_iff.mp
  rw [hi, card_spernerSmallLabels, hc]

/-- A fully labelled simplex has exactly one distinguished good facet. -/
theorem spernerGoodFacets_card_of_full (label : V → Fin (m + 1))
    (σ : Finset V) (hσ : σ.card = m + 1)
    (hfull : σ.image label = Finset.univ) :
    (spernerGoodFacets m label σ).card = 1 := by
  classical
  have hinj : Set.InjOn label (↑σ : Set V) := by
    apply Finset.card_image_iff.mp
    simp [hfull, hσ]
  have hlast : Fin.last m ∈ σ.image label := by
    rw [hfull]
    exact Finset.mem_univ _
  obtain ⟨w, hwσ, hwlabel⟩ := Finset.mem_image.mp hlast
  have hcard : (σ.erase w).card = m := by
    simpa [hσ] using (Finset.card_erase_of_mem hwσ)
  have himage : (σ.erase w).image label = spernerSmallLabels m := by
    ext i
    constructor
    · intro hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      apply mem_spernerSmallLabels.mpr
      intro hvl
      exact (Finset.mem_erase.mp hv).1
        (hinj (Finset.mem_erase.mp hv).2 hwσ (hvl.trans hwlabel.symm))
    · intro hi
      have hine : i ≠ Fin.last m := mem_spernerSmallLabels.mp hi
      have hiσ : i ∈ σ.image label := by simp [hfull]
      obtain ⟨v, hvσ, hvi⟩ := Finset.mem_image.mp hiσ
      refine Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨?_, hvσ⟩, hvi⟩
      intro hvw
      apply hine
      calc
        i = label v := hvi.symm
        _ = label w := congrArg label hvw
        _ = Fin.last m := hwlabel
  have hgood : σ.erase w ∈ spernerGoodFacets m label σ :=
    mem_spernerGoodFacets.mpr ⟨Finset.erase_subset _ _, hcard, himage⟩
  have hfamily : spernerGoodFacets m label σ = {σ.erase w} := by
    ext τ
    constructor
    · intro hτ
      obtain ⟨hτσ, hτcard, hτimage⟩ := mem_spernerGoodFacets.mp hτ
      have hwnot : w ∉ τ := by
        intro hwτ
        have hwmem : label w ∈ spernerSmallLabels m := by
          rw [← hτimage]
          exact Finset.mem_image.mpr ⟨w, hwτ, rfl⟩
        exact (mem_spernerSmallLabels.mp hwmem) hwlabel
      have hsub : τ ⊆ σ.erase w := Finset.subset_erase.mpr ⟨hτσ, hwnot⟩
      apply Finset.mem_singleton.mpr
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hτcard])
    · intro hτ
      have hτeq : τ = σ.erase w := Finset.mem_singleton.mp hτ
      simpa [hτeq] using hgood
  rw [hfamily, Finset.card_singleton]

/-- In a non-full simplex, one good facet determines exactly two good facets.
The second is obtained by exchanging the extra vertex with its equal-label
partner in the first facet. -/
theorem spernerGoodFacets_card_of_nonempty_not_full
    (label : V → Fin (m + 1)) (σ : Finset V) (hσ : σ.card = m + 1)
    (hfull : σ.image label ≠ Finset.univ)
    (hne : (spernerGoodFacets m label σ).Nonempty) :
    (spernerGoodFacets m label σ).card = 2 := by
  classical
  obtain ⟨τ, hτ⟩ := hne
  obtain ⟨hτσ, hτcard, hτimage⟩ := mem_spernerGoodFacets.mp hτ
  obtain ⟨w, hwτ, hwσeq⟩ := Finset.exists_eq_insert_iff.mpr
    (show τ ⊆ σ ∧ τ.card + 1 = σ.card from ⟨hτσ, by rw [hτcard, hσ]⟩)
  have hwσ : w ∈ σ := hwσeq ▸ Finset.mem_insert_self w τ
  have hwlabel : label w ≠ Fin.last m := by
    intro hwlast
    apply hfull
    rw [← hwσeq, Finset.image_insert, hwlast, hτimage, spernerSmallLabels]
    exact Finset.insert_erase (Finset.mem_univ _)
  have hwimage : label w ∈ τ.image label := by
    rw [hτimage]
    exact mem_spernerSmallLabels.mpr hwlabel
  obtain ⟨u, huτ, hulabel⟩ := Finset.mem_image.mp hwimage
  have huw : u ≠ w := by
    intro huw
    exact hwτ (huw ▸ huτ)
  let υ : Finset V := insert w (τ.erase u)
  have hwυ : w ∈ υ := Finset.mem_insert_self _ _
  have hυcard : υ.card = m := by
    have hw : w ∉ τ.erase u := fun h => hwτ (Finset.erase_subset _ _ h)
    dsimp only [υ]
    rw [Finset.card_insert_of_notMem hw, Finset.card_erase_add_one huτ, hτcard]
  have hυimage : υ.image label = spernerSmallLabels m := by
    calc
      υ.image label = insert (label w) ((τ.erase u).image label) :=
        Finset.image_insert _ _ _
      _ = insert (label u) ((τ.erase u).image label) := by rw [hulabel]
      _ = (insert u (τ.erase u)).image label := (Finset.image_insert _ _ _).symm
      _ = τ.image label := by rw [Finset.insert_erase huτ]
      _ = spernerSmallLabels m := hτimage
  have hυσ : υ ⊆ σ := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact hv.symm ▸ hwσ
    · exact hτσ (Finset.erase_subset _ _ hv)
  have hυgood : υ ∈ spernerGoodFacets m label σ :=
    mem_spernerGoodFacets.mpr ⟨hυσ, hυcard, hυimage⟩
  have hτυ : τ ≠ υ := by
    intro heq
    exact hwτ (heq.symm ▸ hwυ)
  have hfamily : spernerGoodFacets m label σ = {τ, υ} := by
    ext η
    constructor
    · intro hη
      obtain ⟨hησ, hηcard, _⟩ := mem_spernerGoodFacets.mp hη
      have hηinsert : η ⊆ insert w τ := by simpa only [hwσeq] using hησ
      by_cases hwη : w ∈ η
      · have huη : u ∉ η := by
          intro huη
          exact huw ((spernerGoodFacet_injOn hη) huη hwη hulabel)
        have hηυ : η ⊆ υ := by
          intro v hvη
          rcases Finset.mem_insert.mp (hηinsert hvη) with hvw | hvτ
          · exact Finset.mem_insert.mpr (Or.inl hvw)
          · apply Finset.mem_insert.mpr
            right
            apply Finset.mem_erase.mpr
            refine ⟨?_, hvτ⟩
            intro hvu
            exact huη (hvu ▸ hvη)
        have hηeq : η = υ := Finset.eq_of_subset_of_card_le hηυ
          (by rw [hυcard, hηcard])
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr hηeq
      · have hητ : η ⊆ τ := by
          intro v hvη
          rcases Finset.mem_insert.mp (hηinsert hvη) with hvw | hvτ
          · exact False.elim (hwη (hvw ▸ hvη))
          · exact hvτ
        have hηeq : η = τ := Finset.eq_of_subset_of_card_le hητ
          (by rw [hτcard, hηcard])
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl hηeq
    · intro hη
      rcases Finset.mem_insert.mp hη with hη | hη
      · simpa [hη] using hτ
      · have hηeq : η = υ := Finset.mem_singleton.mp hη
        simpa [hηeq] using hυgood
  rw [hfamily]
  simp [hτυ]

/-- The local mod-two incidence identity, valid also in dimension zero. -/
theorem spernerGoodFacets_card_mod_two (label : V → Fin (m + 1))
    (σ : Finset V) (hσ : σ.card = m + 1) :
    ((spernerGoodFacets m label σ).card : ZMod 2) =
      if σ.image label = Finset.univ then 1 else 0 := by
  classical
  by_cases hfull : σ.image label = Finset.univ
  · simpa only [if_pos hfull, spernerGoodFacets_card_of_full label σ hσ hfull]
      using (Nat.cast_one : ((1 : ℕ) : ZMod 2) = 1)
  · rw [if_neg hfull]
    by_cases hne : (spernerGoodFacets m label σ).Nonempty
    · simpa only [spernerGoodFacets_card_of_nonempty_not_full label σ hσ hfull hne]
        using (ZMod.natCast_self 2)
    · have hempty : spernerGoodFacets m label σ = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty]

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SpernerIncidence

namespace OAI

/-!
# Counting labelled incidences in a finite complex

The two orders of summation count the same actual top-cell/facet pairs. Local
facet parity leaves the fully labelled top cells on one side. Degree two
facets cancel on the other side, leaving only the degree one boundary facets.
-/

open scoped BigOperators

namespace Tingley.FiniteComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem goodFacets_eq_codim_filter (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) {σ : Finset V} (hσ : σ ∈ K.topCells m) :
    (K.codimFaces m).filter
        (fun τ => τ ⊆ σ ∧ τ.image label = spernerSmallLabels m) =
      spernerGoodFacets m label σ := by
  classical
  ext τ
  rw [Finset.mem_filter, mem_spernerGoodFacets]
  constructor
  · rintro ⟨hτ, hsub, hlabel⟩
    exact ⟨hsub, (mem_codimFaces.mp hτ).2, hlabel⟩
  · rintro ⟨hsub, hcard, hlabel⟩
    exact ⟨mem_codimFaces.mpr
      ⟨K.down_closed (mem_topCells.mp hσ).1 hsub, hcard⟩, hsub, hlabel⟩

/-- Finite incidence parity, before the boundary restriction is identified with
the lower-dimensional simplex. All hypotheses concern finite face incidence. -/
theorem sperner_count_mod_two (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2) :
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
      (((K.codimFaces m).filter
        (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) := by
  classical
  have hrow : ∀ σ ∈ K.topCells m,
      (∑ τ ∈ K.codimFaces m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if σ.image label = Finset.univ then 1 else 0 := by
    intro σ hσ
    rw [Finset.sum_boole, goodFacets_eq_codim_filter K m label hσ]
    exact spernerGoodFacets_card_mod_two label σ (mem_topCells.mp hσ).2
  have hcolumn : ∀ τ ∈ K.codimFaces m,
      (∑ σ ∈ K.topCells m,
        if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0) =
      if τ.image label = spernerSmallLabels m ∧ boundary τ then 1 else 0 := by
    intro τ hτ
    by_cases hg : τ.image label = spernerSmallLabels m
    · simp only [hg, and_true, true_and]
      rw [Finset.sum_boole]
      change ((K.incidentTop m τ).card : ZMod 2) = if boundary τ then 1 else 0
      rw [hdegree τ hτ]
      by_cases hb : boundary τ
      · simp [hb]
      · simp only [hb, ite_false]
        exact ZMod.natCast_self 2
    · simp [hg]
  calc
    (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card : ZMod 2) =
        ∑ σ ∈ K.topCells m,
          if σ.image label = Finset.univ then (1 : ZMod 2) else 0 :=
      Finset.natCast_card_filter _ _
    _ = ∑ σ ∈ K.topCells m, ∑ τ ∈ K.codimFaces m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl (fun σ hσ => (hrow σ hσ).symm)
    _ = ∑ τ ∈ K.codimFaces m, ∑ σ ∈ K.topCells m,
          if τ ⊆ σ ∧ τ.image label = spernerSmallLabels m then (1 : ZMod 2) else 0 :=
      Finset.sum_comm
    _ = ∑ τ ∈ K.codimFaces m,
          if τ.image label = spernerSmallLabels m ∧ boundary τ then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl hcolumn
    _ = (((K.codimFaces m).filter
          (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card : ZMod 2) :=
      Finset.sum_boole _ _

/-- An odd number of good boundary facets gives an odd number of fully labelled cells. -/
theorem sperner_odd_of_boundary_odd (K : FiniteComplex V) (m : ℕ)
    (label : V → Fin (m + 1)) (boundary : Finset V → Prop)
    [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2)
    (hboundary : Odd (((K.codimFaces m).filter
      (fun τ => τ.image label = spernerSmallLabels m ∧ boundary τ)).card)) :
    Odd (((K.topCells m).filter (fun σ => σ.image label = Finset.univ)).card) := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  rw [sperner_count_mod_two K m label boundary hdegree]
  exact ZMod.natCast_eq_one_iff_odd.mpr hboundary

end Tingley.FiniteComplex

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SpernerBoundary

namespace OAI

/-!
# Boundary labels and restriction of the finite Sperner count

Admissible labels lie in the union of the vertex carriers. A good boundary
facet therefore has exactly the carrier omitting the last coordinate. Mapping
lower-dimensional faces through a vertex embedding preserves the label count
after the coordinate embedding `Fin.castSucc`.
-/

namespace Tingley

variable {V W I : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq I]

omit [DecidableEq V] in
/-- Vertexwise carrier membership implies membership in the face carrier. -/
theorem sperner_label_image_subset_carrier (label : V → I)
    (carrier : V → Finset I) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v) :
    σ.image label ⊆ σ.biUnion carrier := by
  intro i hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_biUnion.mpr ⟨v, hv, hlabel v hv⟩

omit [DecidableEq V] in
/-- A good boundary facet can only lie on the original face missing the last
coordinate. The conclusion follows from containment and equal cardinality. -/
theorem carrier_eq_spernerSmallLabels {m : ℕ} (label : V → Fin (m + 1))
    (carrier : V → Finset (Fin (m + 1))) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v)
    (hgood : σ.image label = spernerSmallLabels m)
    (hcard : (σ.biUnion carrier).card = m) :
    σ.biUnion carrier = spernerSmallLabels m := by
  have hsub : spernerSmallLabels m ⊆ σ.biUnion carrier := by
    rw [← hgood]
    exact sperner_label_image_subset_carrier label carrier σ hlabel
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard, card_spernerSmallLabels])).symm

omit [DecidableEq V] in
/-- For a good face, the boundary cardinality condition is equivalent to
omission of the last coordinate from its carrier. -/
theorem good_carrier_card_iff_last_not_mem {m : ℕ} (label : V → Fin (m + 1))
    (carrier : V → Finset (Fin (m + 1))) (σ : Finset V)
    (hlabel : ∀ v ∈ σ, label v ∈ carrier v)
    (hgood : σ.image label = spernerSmallLabels m) :
    (σ.biUnion carrier).card = m ↔ Fin.last m ∉ σ.biUnion carrier := by
  constructor
  · intro hcard
    rw [carrier_eq_spernerSmallLabels label carrier σ hlabel hgood hcard]
    simp
  · intro hlast
    have hsub : σ.biUnion carrier ⊆ spernerSmallLabels m := by
      intro i hi
      apply mem_spernerSmallLabels.mpr
      intro hilast
      exact hlast (hilast ▸ hi)
    have hsup : spernerSmallLabels m ⊆ σ.biUnion carrier := by
      rw [← hgood]
      exact sperner_label_image_subset_carrier label carrier σ hlabel
    rw [Finset.Subset.antisymm hsub hsup, card_spernerSmallLabels]

omit [DecidableEq V] in
/-- Among good faces, all boundary faces are exactly those on the last face.
This is the filter identity used before transporting the incidence count. -/
theorem good_boundary_filter_eq_last_face_filter {m : ℕ}
    (label : V → Fin (m + 1)) (carrier : V → Finset (Fin (m + 1)))
    (faces : Finset (Finset V)) (hlabel : ∀ v, label v ∈ carrier v) :
    faces.filter (fun σ => σ.image label = spernerSmallLabels m ∧
        (σ.biUnion carrier).card = m) =
      (faces.filter (fun σ => Fin.last m ∉ σ.biUnion carrier)).filter
        (fun σ => σ.image label = spernerSmallLabels m) := by
  classical
  ext σ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hσ, hg, hc⟩
    exact ⟨⟨hσ, (good_carrier_card_iff_last_not_mem label carrier σ
      (fun v _ => hlabel v) hg).mp hc⟩, hg⟩
  · rintro ⟨⟨hσ, hl⟩, hg⟩
    exact ⟨hσ, hg, (good_carrier_card_iff_last_not_mem label carrier σ
      (fun v _ => hlabel v) hg).mpr hl⟩

/-- Remove the last coordinate from labels on an embedded boundary face. -/
def spernerRestrictedLabel {n : ℕ} (e : W ↪ V) (label : V → Fin (n + 1))
    (hne : ∀ w, label (e w) ≠ Fin.last n) : W → Fin n :=
  fun w => (label (e w)).castPred (hne w)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem castSucc_spernerRestrictedLabel {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (hne : ∀ w, label (e w) ≠ Fin.last n) (w : W) :
    (spernerRestrictedLabel e label hne w).castSucc = label (e w) :=
  Fin.castSucc_castPred _ _

/-- The smaller label set is exactly the image of the smaller coordinate type. -/
theorem image_univ_castSucc_eq_spernerSmallLabels (n : ℕ) :
    (Finset.univ : Finset (Fin n)).image Fin.castSucc = spernerSmallLabels n := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact mem_spernerSmallLabels.mpr j.castSucc_ne_last
  · intro hi
    obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last (mem_spernerSmallLabels.mp hi)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

omit [DecidableEq W] in
/-- Compatible vertex and coordinate embeddings commute with the label image. -/
theorem mapped_label_image_eq {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc) (σ : Finset W) :
    (σ.map e).image label = (σ.image lowerLabel).image Fin.castSucc := by
  rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro w _
  exact hlabel w

omit [DecidableEq W] in
/-- A mapped face is good exactly when its lower-dimensional face is full. -/
theorem mapped_fully_labelled_iff {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc) (σ : Finset W) :
    (σ.map e).image label = spernerSmallLabels n ↔
      σ.image lowerLabel = Finset.univ := by
  rw [mapped_label_image_eq e label lowerLabel hlabel σ,
    ← image_univ_castSucc_eq_spernerSmallLabels n]
  exact Finset.image_inj (Fin.castSucc_injective n)

omit [DecidableEq V] [DecidableEq W] in
/-- Restricting an admissible embedded label preserves membership in the
lower-dimensional carrier. -/
theorem restricted_label_mem_carrier {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (hne : ∀ w, label (e w) ≠ Fin.last n)
    (carrier : W → Finset (Fin n))
    (hlabel : ∀ w, label (e w) ∈ (carrier w).image Fin.castSucc) (w : W) :
    spernerRestrictedLabel e label hne w ∈ carrier w := by
  obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp (hlabel w)
  have heq : i = spernerRestrictedLabel e label hne w :=
    Fin.castSucc_injective n
      (hieq.trans (castSucc_spernerRestrictedLabel e label hne w).symm)
  simpa only [heq] using hi

omit [DecidableEq W] in
/-- A finite family of faces can be filtered before or after an injective
vertex map, without changing its cardinality. -/
theorem mapped_family_filter_card (e : W ↪ V)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (p : Finset W → Prop) (q : Finset V → Prop)
    [DecidablePred p] [DecidablePred q]
    (hfamily : higherFamily = lowerFamily.image (fun σ => σ.map e))
    (hpred : ∀ σ ∈ lowerFamily, q (σ.map e) ↔ p σ) :
    (higherFamily.filter q).card = (lowerFamily.filter p).card := by
  classical
  have hfilter : lowerFamily.filter (fun σ => q (σ.map e)) = lowerFamily.filter p :=
    Finset.filter_congr hpred
  rw [hfamily, Finset.filter_image, hfilter]
  exact Finset.card_image_of_injective _ (Finset.map_injective e)

omit [DecidableEq W] in
/-- Exact transport of the good-face count under a raw face-family bijection. -/
theorem mapped_good_family_card {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (hfamily : higherFamily = lowerFamily.image (fun σ => σ.map e)) :
    (higherFamily.filter (fun τ => τ.image label = spernerSmallLabels n)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  exact mapped_family_filter_card e lowerFamily higherFamily _ _ hfamily
    (fun σ _ => mapped_fully_labelled_iff e label lowerLabel hlabel σ)

omit [DecidableEq W] in
/-- Count transport in the `Finset.map` form produced by the subdivision
restriction theorem. -/
theorem mapped_good_family_card_of_map {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (hfamily : higherFamily = lowerFamily.map (Finset.mapEmbedding e).toEmbedding) :
    (higherFamily.filter (fun τ => τ.image label = spernerSmallLabels n)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  apply mapped_good_family_card e label lowerLabel hlabel lowerFamily higherFamily
  calc
    higherFamily = lowerFamily.map (Finset.mapEmbedding e).toEmbedding := hfamily
    _ = lowerFamily.image (fun σ => σ.map e) := Finset.map_eq_image _ _

omit [DecidableEq W] in
/-- The same count transport with a membership characterization of the raw
boundary family, rather than an equality already assembled by the caller. -/
theorem mapped_good_family_card_of_mem_iff {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (hfamily : ∀ τ, τ ∈ higherFamily ↔ ∃ σ ∈ lowerFamily, σ.map e = τ) :
    (higherFamily.filter (fun τ => τ.image label = spernerSmallLabels n)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  apply mapped_good_family_card e label lowerLabel hlabel lowerFamily higherFamily
  ext τ
  exact (hfamily τ).trans Finset.mem_image.symm

omit [DecidableEq W] in
/-- The exact good-boundary expression used in the incidence count becomes the
fully labelled lower-dimensional expression. -/
theorem good_boundary_family_card {n : ℕ} (e : W ↪ V)
    (label : V → Fin (n + 1)) (lowerLabel : W → Fin n)
    (hlabel : ∀ w, label (e w) = (lowerLabel w).castSucc)
    (lowerFamily : Finset (Finset W)) (higherFamily : Finset (Finset V))
    (boundary : Finset V → Prop) [DecidablePred boundary]
    (hfamily : higherFamily.filter boundary = lowerFamily.image (fun σ => σ.map e)) :
    (higherFamily.filter
      (fun τ => τ.image label = spernerSmallLabels n ∧ boundary τ)).card =
      (lowerFamily.filter (fun σ => σ.image lowerLabel = Finset.univ)).card := by
  classical
  simpa only [Finset.filter_filter, and_comm] using
    mapped_good_family_card e label lowerLabel hlabel lowerFamily
      (higherFamily.filter boundary) hfamily

end Tingley

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricRestriction

namespace OAI

/-! # Embeddings of complexes and exact restriction under subdivision -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v w z
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]

structure Embedding (K : FiniteComplex V) (L : FiniteComplex W) where
  toEmbedding : V ↪ W
  map_mem_iff : ∀ s : Finset V, s.map toEmbedding ∈ L.faces ↔ s ∈ K.faces

namespace Embedding

variable {K : FiniteComplex V} {L : FiniteComplex W}

def full (e : V ↪ W) : Embedding (FiniteComplex.full : FiniteComplex V)
    (FiniteComplex.full : FiniteComplex W) where
  toEmbedding := e
  map_mem_iff := fun _ => by simp

def faceMap (e : Embedding K L) : FaceVertex K ↪ FaceVertex L where
  toFun s := ⟨s.val.map e.toEmbedding,
    (e.map_mem_iff s.val).mpr s.property.1, Finset.map_nonempty.mpr s.property.2⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact Finset.map_injective e.toEmbedding (congrArg Subtype.val h)

@[simp] theorem faceMap_val (e : Embedding K L) (s : FaceVertex K) :
    (e.faceMap s).val = s.val.map e.toEmbedding := rfl

def sd (e : Embedding K L) : Embedding K.sd L.sd where
  toEmbedding := e.faceMap
  map_mem_iff := by
    intro c
    rw [mem_sd_iff, mem_sd_iff]
    constructor
    · intro hc a ha b hb
      have h := hc (e.faceMap a) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
        (e.faceMap b) (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
      exact h.imp Finset.map_subset_map.mp Finset.map_subset_map.mp
    · intro hc a ha b hb
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
      exact (hc a' ha' b' hb').imp Finset.map_subset_map.mpr Finset.map_subset_map.mpr

def preimage (e : Embedding K L) (s : Finset W) : Finset V :=
  Finset.univ.filter (fun v => e.toEmbedding v ∈ s)

@[simp] theorem mem_preimage (e : Embedding K L) {s : Finset W} {v : V} :
    v ∈ e.preimage s ↔ e.toEmbedding v ∈ s := by
  simp [preimage]

theorem map_preimage (e : Embedding K L) (s : Finset W)
    (hs : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    (e.preimage s).map e.toEmbedding = s := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (e.mem_preimage).mp hv
  · intro hw
    obtain ⟨v, rfl⟩ := hs w hw
    exact Finset.mem_map.mpr ⟨v, e.mem_preimage.mpr hw, rfl⟩

theorem exists_face_preimage (e : Embedding K L) {s : Finset W} (hs : s ∈ L.faces)
    (hrange : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  refine ⟨e.preimage s, ?_, e.map_preimage s hrange⟩
  apply (e.map_mem_iff _).mp
  rwa [e.map_preimage s hrange]

variable {I : Type w} {J : Type z} [DecidableEq I] [DecidableEq J]

theorem faceCarrier_map (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : Finset V) :
    faceCarrier cW (s.map e.toEmbedding) = (faceCarrier cV s).map i := by
  ext j
  constructor
  · intro hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    rw [h] at hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_map.mpr ⟨a, mem_faceCarrier.mpr ⟨v, hv, ha⟩, rfl⟩
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨v, hv, ha⟩ := mem_faceCarrier.mp ha
    refine mem_faceCarrier.mpr ⟨e.toEmbedding v,
      Finset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [h]
    exact Finset.mem_map.mpr ⟨a, ha, rfl⟩

theorem sdCarrier_faceMap (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : FaceVertex K) :
    L.sdCarrier cW (e.faceMap s) = (K.sdCarrier cV s).map i :=
  e.faceCarrier_map i h s.val

theorem faceMap_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) (s : FaceVertex L) :
    L.sdCarrier cW s ⊆ A ↔ ∃ t : FaceVertex K, e.faceMap t = s := by
  constructor
  · intro hs
    have hvertices : ∀ w ∈ s.val, ∃ v, e.toEmbedding v = w := by
      intro w hw
      apply (h w).mp
      intro j hj
      exact hs (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
    obtain ⟨t, ht, hts⟩ := e.exists_face_preimage s.property.1 hvertices
    have hne : t.Nonempty := by
      have : (t.map e.toEmbedding).Nonempty := hts.symm ▸ s.property.2
      exact Finset.map_nonempty.mp this
    refine ⟨⟨t, ht, hne⟩, ?_⟩
    exact Subtype.ext hts
  · rintro ⟨t, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

theorem face_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) {s : Finset W}
    (hs : s ∈ L.faces) :
    faceCarrier cW s ⊆ A ↔ ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  constructor
  · intro hsub
    apply e.exists_face_preimage hs
    intro w hw
    apply (h w).mp
    intro j hj
    exact hsub (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
  · rintro ⟨t, ht, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

end Embedding

end Tingley.FiniteComplex

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SubdivisionRestriction

namespace OAI

/-! # The exact original-face restriction of every concrete subdivision -/

noncomputable section

namespace Tingley

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def iterEmbedding (e : I ↪ J) : (k : ℕ) →
    FiniteComplex.Embedding (iterData I k).complex (iterData J k).complex
  | 0 => FiniteComplex.Embedding.full e
  | k + 1 => (iterEmbedding e k).sd

theorem iterEmbedding_carrier (e : I ↪ J) (k : ℕ)
    (v : (iterData I k).Vertex) :
    (iterData J k).carrier ((iterEmbedding e k).toEmbedding v) =
      ((iterData I k).carrier v).map e := by
  induction k with
  | zero =>
      change I at v
      change ({e v} : Finset J) = ({v} : Finset I).map e
      exact (Finset.map_singleton e v).symm
  | succ k ih =>
      exact (iterEmbedding e k).sdCarrier_faceMap e ih v

theorem iterEmbedding_range_iff (e : I ↪ J) (k : ℕ)
    (v : (iterData J k).Vertex) :
    (iterData J k).carrier v ⊆ Finset.univ.map e ↔
      ∃ w, (iterEmbedding e k).toEmbedding w = v := by
  induction k with
  | zero =>
      change J at v
      change ({v} : Finset J) ⊆ Finset.univ.map e ↔ ∃ w : I, e w = v
      simp only [Finset.singleton_subset_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
  | succ k ih => exact (iterEmbedding e k).faceMap_range_iff ih v

theorem iterEmbedding_faceCarrier (e : I ↪ J) (k : ℕ)
    (s : Finset (iterData I k).Vertex) :
    FiniteComplex.faceCarrier (iterData J k).carrier
        (s.map (iterEmbedding e k).toEmbedding) =
      (FiniteComplex.faceCarrier (iterData I k).carrier s).map e :=
  (iterEmbedding e k).faceCarrier_map e (iterEmbedding_carrier e k) s

theorem iterEmbedding_face_range_iff (e : I ↪ J) (k : ℕ)
    {s : Finset (iterData J k).Vertex} (hs : s ∈ (iterData J k).complex.faces) :
    FiniteComplex.faceCarrier (iterData J k).carrier s ⊆ Finset.univ.map e ↔
      ∃ t ∈ (iterData I k).complex.faces, t.map (iterEmbedding e k).toEmbedding = s :=
  (iterEmbedding e k).face_range_iff (iterEmbedding_range_iff e k) hs

def lastFaceEmbedding (m k : ℕ) : IterVertex m k ↪ IterVertex (m + 1) k :=
  (iterEmbedding (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k).toEmbedding

theorem lastFace_carrier (m k : ℕ) (v : IterVertex m k) :
    iterCarrier (m + 1) k (lastFaceEmbedding m k v) =
      (iterCarrier m k v).map Fin.castSuccEmb :=
  iterEmbedding_carrier Fin.castSuccEmb k v

theorem lastFace_faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) :
    faceCarrier (m + 1) k (s.map (lastFaceEmbedding m k)) =
      (faceCarrier m k s).map Fin.castSuccEmb :=
  iterEmbedding_faceCarrier Fin.castSuccEmb k s

theorem lastFace_range_iff (m k : ℕ) (v : IterVertex (m + 1) k) :
    Fin.last (m + 1) ∉ iterCarrier (m + 1) k v ↔
      ∃ w, lastFaceEmbedding m k w = v := by
  have h := iterEmbedding_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k v
  simpa only [iterCarrier, lastFaceEmbedding, Finset.map_eq_image,
    Fin.coe_castSuccEmb, Fin.image_castSucc, Finset.subset_compl_singleton] using h

theorem lastFace_mem_iff (m k : ℕ) (s : Finset (IterVertex m k)) :
    s.map (lastFaceEmbedding m k) ∈ iterComplex (m + 1) k ↔ s ∈ iterComplex m k :=
  (iterEmbedding Fin.castSuccEmb k).map_mem_iff s

theorem lastFace_face_range_iff {m k : ℕ} {s : Finset (IterVertex (m + 1) k)}
    (hs : s ∈ iterComplex (m + 1) k) :
    Fin.last (m + 1) ∉ faceCarrier (m + 1) k s ↔
      ∃ t ∈ iterComplex m k, t.map (lastFaceEmbedding m k) = s := by
  have h := iterEmbedding_face_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k hs
  simpa only [faceCarrier, iterCarrier, iterComplex, lastFaceEmbedding,
    Finset.map_eq_image, Fin.coe_castSuccEmb, Fin.image_castSucc,
    Finset.subset_compl_singleton] using h

theorem lastFace_map_top_mem (m k : ℕ) {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) :
    s.map (lastFaceEmbedding m k) ∈ codimFaces (m + 1) k := by
  obtain ⟨hsface, hscard⟩ := mem_topCells.mp hs
  exact mem_codimFaces.mpr ⟨(lastFace_mem_iff m k s).mpr hsface, by simpa using hscard⟩

theorem lastFace_top_image (m k : ℕ) :
    (topCells m k).map (Finset.mapEmbedding (lastFaceEmbedding m k)).toEmbedding =
      (codimFaces (m + 1) k).filter
        (fun s => Fin.last (m + 1) ∉ faceCarrier (m + 1) k s) := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    apply Finset.mem_filter.mpr
    refine ⟨lastFace_map_top_mem m k ht, ?_⟩
    change Fin.last (m + 1) ∉ faceCarrier (m + 1) k (t.map (lastFaceEmbedding m k))
    rw [lastFace_faceCarrier]
    simp only [Finset.mem_map, not_exists, not_and]
    intro i hi
    exact Fin.castSucc_ne_last i
  · intro hs
    obtain ⟨hscodim, hboundary⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsface, hscard⟩ := mem_codimFaces.mp hscodim
    obtain ⟨t, htface, hts⟩ := (lastFace_face_range_iff hsface).mp hboundary
    apply Finset.mem_map.mpr
    refine ⟨t, mem_topCells.mpr ⟨htface, ?_⟩, hts⟩
    have hcard := congrArg Finset.card hts
    simpa [hscard] using hcard

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricIncidence

namespace OAI

/-!
# Codimension-one incidence in the actual face-chain subdivision

Completions of a flag are counted by inserting its unique missing rank.
An interior missing rank has two completions. A missing top rank inherits
the incidence count of the greatest old face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

theorem chain_insert_iff {c : Finset (FaceVertex K)} {a : FaceVertex K} :
    K.chain (insert a c) ↔ K.chain c ∧
      ∀ b ∈ c, a.val ⊆ b.val ∨ b.val ⊆ a.val := by
  classical
  constructor
  · intro h
    exact ⟨K.chain_mono h (Finset.subset_insert _ _),
      fun b hb => h a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨hc, ha⟩ b hb d hd
    rcases Finset.mem_insert.mp hb with hba | hbc
    · subst b
      rcases Finset.mem_insert.mp hd with hda | hdc
      · subst d
        exact Or.inl (Finset.Subset.refl _)
      · exact ha d hdc
    · rcases Finset.mem_insert.mp hd with hda | hdc
      · subst d
        exact (ha b hbc).symm
      · exact hc b hbc d hdc

def insertionVertices (K : FiniteComplex V) (c : Finset (FaceVertex K)) :
    Finset (FaceVertex K) := by
  classical
  exact Finset.univ.filter (fun a => a ∉ c ∧ K.chain (insert a c))

@[simp] theorem mem_insertionVertices {c : Finset (FaceVertex K)} {a : FaceVertex K} :
    a ∈ K.insertionVertices c ↔ a ∉ c ∧ K.chain (insert a c) := by
  classical
  simp [insertionVertices]

theorem incidentTop_sd_eq_image_insert {m : ℕ} {c : Finset (FaceVertex K)}
    (hc : c.card = m) :
    K.sd.incidentTop m c = (K.insertionVertices c).image (fun a => insert a c) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨hdface, hdcard, hcd⟩ := mem_incidentTop.mp hd
    obtain ⟨a, ha, had⟩ := Finset.exists_eq_insert_iff.mpr
      (show c ⊆ d ∧ c.card + 1 = d.card from ⟨hcd, by omega⟩)
    apply Finset.mem_image.mpr
    refine ⟨a, mem_insertionVertices.mpr ⟨ha, ?_⟩, had⟩
    rw [had]
    exact mem_sd_iff.mp hdface
  · intro hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨ha, hchain⟩ := mem_insertionVertices.mp ha
    exact mem_incidentTop.mpr ⟨mem_sd_iff.mpr hchain,
      by rw [Finset.card_insert_of_notMem ha, hc], Finset.subset_insert _ _⟩

theorem incidentTop_sd_card_eq_insertionVertices {m : ℕ}
    {c : Finset (FaceVertex K)} (hc : c.card = m) :
    (K.sd.incidentTop m c).card = (K.insertionVertices c).card := by
  classical
  rw [incidentTop_sd_eq_image_insert hc]
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact (Finset.insert_inj (mem_insertionVertices.mp ha).1).mp hab

theorem rank_ne_of_missing {m r : ℕ} {c : Finset (FaceVertex K)}
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    {a : FaceVertex K} (ha : a ∈ c) : a.val.card ≠ r := by
  have h : a.val.card ∈ K.ranks c := mem_ranks.mpr ⟨a, ha, rfl⟩
  rw [hr] at h
  exact (Finset.mem_erase.mp h).1

theorem missing_rank_unique {m r s : ℕ} {c : Finset (FaceVertex K)}
    (hr₁ : 1 ≤ r) (hr₂ : r ≤ m + 1)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    (hs : K.ranks c = (Finset.Icc 1 (m + 1)).erase s) : r = s := by
  by_contra hrs
  have hmem : r ∈ K.ranks c := by
    rw [hs]
    exact Finset.mem_erase.mpr ⟨hrs, Finset.mem_Icc.mpr ⟨hr₁, hr₂⟩⟩
  rw [hr] at hmem
  exact (Finset.mem_erase.mp hmem).1 rfl

theorem insertionVertices_card_eq_missing {m r : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)}
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r)
    {a : FaceVertex K} (ha : a ∈ K.insertionVertices c) : a.val.card = r := by
  classical
  obtain ⟨hanot, hchain⟩ := mem_insertionVertices.mp ha
  by_contra har
  have hmem : a.val.card ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨har, Finset.mem_Icc.mpr
      ⟨Finset.card_pos.mpr a.property.2, hK a.val a.property.1⟩⟩
  obtain ⟨b, hb, hba⟩ := mem_ranks.mp hmem
  have hab : a = b := chain_eq_of_card_eq hchain (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem hb) hba.symm
  apply hanot
  rw [hab]
  exact hb

/-- Count possible inserted old faces between two consecutive retained ranks. -/
theorem card_insertionVertices_eq_sdiff {c : Finset (FaceVertex K)}
    {L U : Finset V} (hU : U ∈ K.faces) (hLU : L ⊆ U)
    (hmem : ∀ a : FaceVertex K, a ∈ K.insertionVertices c ↔
      L ⊆ a.val ∧ a.val ⊆ U ∧ a.val.card = L.card + 1) :
    (K.insertionVertices c).card = (U \ L).card := by
  classical
  let f : ∀ a ∈ U \ L, FaceVertex K := fun a ha =>
    ⟨insert a L,
      K.down_closed hU (Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp ha).1, hLU⟩),
      ⟨a, Finset.mem_insert_self _ _⟩⟩
  have hf : ∀ a ha, f a ha ∈ K.insertionVertices c := by
    intro a ha
    apply (hmem _).mpr
    exact ⟨Finset.subset_insert _ _,
      Finset.insert_subset_iff.mpr ⟨(Finset.mem_sdiff.mp ha).1, hLU⟩,
      Finset.card_insert_of_notMem (Finset.mem_sdiff.mp ha).2⟩
  have hinj : ∀ a ha b hb, f a ha = f b hb → a = b := by
    intro a ha b hb hab
    have heq : insert a L = insert b L := congrArg Subtype.val hab
    exact (Finset.insert_inj (Finset.mem_sdiff.mp ha).2).mp heq
  have hsurj : ∀ b ∈ K.insertionVertices c, ∃ a ha, f a ha = b := by
    intro b hb
    obtain ⟨hLb, hbU, hbcard⟩ := (hmem b).mp hb
    obtain ⟨a, haL, hab⟩ := Finset.exists_eq_insert_iff.mpr
      (show L ⊆ b.val ∧ L.card + 1 = b.val.card from ⟨hLb, hbcard.symm⟩)
    have haU : a ∈ U := by
      apply hbU
      rw [← hab]
      exact Finset.mem_insert_self _ _
    refine ⟨a, Finset.mem_sdiff.mpr ⟨haU, haL⟩, ?_⟩
    apply Subtype.ext
    exact hab
  exact (Finset.card_bij f hf hinj hsurj).symm

/-- An omitted rank strictly below the top has exactly two completions. -/
theorem incidentTop_sd_card_two_of_missing_rank {m r : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr₁ : 1 ≤ r) (hrm : r ≤ m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase r) :
    (K.sd.incidentTop m c).card = 2 := by
  classical
  obtain ⟨hcface, hccard⟩ := mem_codimFaces.mp hc
  have hcchain := mem_sd_iff.mp hcface
  have hUr : r + 1 ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  obtain ⟨U, hUc, hUcard⟩ := mem_ranks.mp hUr
  obtain ⟨L, hLcard, hLU, hLmem, hgap⟩ :
      ∃ L : Finset V, L.card + 1 = r ∧ L ⊆ U.val ∧
        (L = ∅ ∨ ∃ a ∈ c, a.val = L) ∧
        ∀ b ∈ c, b.val ⊆ L ∨ U.val ⊆ b.val := by
    by_cases hrone : r = 1
    · refine ⟨∅, by simp [hrone], Finset.empty_subset _, Or.inl rfl, ?_⟩
      intro b hb
      right
      apply chain_subset_of_card_le hcchain hUc hb
      have hbpos := Finset.card_pos.mpr b.property.2
      have hbne := rank_ne_of_missing hr hb
      omega
    · have hLr : r - 1 ∈ K.ranks c := by
        rw [hr]
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      obtain ⟨L, hLc, hLc_card⟩ := mem_ranks.mp hLr
      refine ⟨L.val, by omega,
        chain_subset_of_card_le hcchain hLc hUc (by omega),
        Or.inr ⟨L, hLc, rfl⟩, ?_⟩
      intro b hb
      have hbne := rank_ne_of_missing hr hb
      by_cases hbsmall : b.val.card ≤ L.val.card
      · exact Or.inl (chain_subset_of_card_le hcchain hb hLc hbsmall)
      · exact Or.inr (chain_subset_of_card_le hcchain hUc hb (by omega))
  have hmem : ∀ a : FaceVertex K, a ∈ K.insertionVertices c ↔
      L ⊆ a.val ∧ a.val ⊆ U.val ∧ a.val.card = L.card + 1 := by
    intro a
    constructor
    · intro ha
      have hacard := insertionVertices_card_eq_missing hK hr ha
      have hachain := (mem_insertionVertices.mp ha).2
      refine ⟨?_, chain_subset_of_card_le hachain (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hUc) (by omega), by omega⟩
      rcases hLmem with hLempty | ⟨b, hbc, hbL⟩
      · rw [hLempty]
        exact Finset.empty_subset _
      · rw [← hbL]
        apply chain_subset_of_card_le hachain (Finset.mem_insert_of_mem hbc)
          (Finset.mem_insert_self _ _)
        have hbcard : b.val.card = L.card := congrArg Finset.card hbL
        omega
    · rintro ⟨hLa, haU, hacard⟩
      apply mem_insertionVertices.mpr
      refine ⟨?_, chain_insert_iff.mpr ⟨hcchain, ?_⟩⟩
      · intro hac
        exact rank_ne_of_missing hr hac (by omega)
      · intro b hb
        rcases hgap b hb with hbL | hUb
        · exact Or.inr (hbL.trans hLa)
        · exact Or.inl (haU.trans hUb)
  rw [incidentTop_sd_card_eq_insertionVertices hccard,
    card_insertionVertices_eq_sdiff U.property.1 hLU hmem,
    Finset.card_sdiff_of_subset hLU, hUcard]
  omega

/-- If the omitted rank is the top rank, completions are exactly the old
top faces containing the retained rank-`m` face. -/
theorem incidentTop_sd_card_eq_of_missing_top {m : ℕ} (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase (m + 1))
    {T : FaceVertex K} (hTc : T ∈ c) (hTcard : T.val.card = m) :
    (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card := by
  classical
  obtain ⟨hcface, hccard⟩ := mem_codimFaces.mp hc
  have hcchain := mem_sd_iff.mp hcface
  have hmax : ∀ b ∈ c, b.val ⊆ T.val := by
    intro b hb
    apply chain_subset_of_card_le hcchain hb hTc
    have hbcard := hK b.val b.property.1
    have hbne := rank_ne_of_missing hr hb
    omega
  let f : ∀ W ∈ K.incidentTop m T.val, FaceVertex K := fun W hW =>
    ⟨W, (mem_incidentTop.mp hW).1,
      Finset.card_pos.mp (by have h := (mem_incidentTop.mp hW).2.1; omega)⟩
  have hf : ∀ W hW, f W hW ∈ K.insertionVertices c := by
    intro W hW
    obtain ⟨hWface, hWcard, hTW⟩ := mem_incidentTop.mp hW
    apply mem_insertionVertices.mpr
    refine ⟨?_, chain_insert_iff.mpr ⟨hcchain, ?_⟩⟩
    · intro hWc
      have hle := Finset.card_le_card (hmax (f W hW) hWc)
      change W.card ≤ T.val.card at hle
      omega
    · intro b hb
      exact Or.inr ((hmax b hb).trans hTW)
  have hinj : ∀ W hW U hU, f W hW = f U hU → W = U := by
    intro W hW U hU h
    exact congrArg Subtype.val h
  have hsurj : ∀ a ∈ K.insertionVertices c,
      ∃ W hW, f W hW = a := by
    intro a ha
    have hacard := insertionVertices_card_eq_missing hK hr ha
    have hTa : T.val ⊆ a.val :=
      chain_subset_of_card_le (mem_insertionVertices.mp ha).2
        (Finset.mem_insert_of_mem hTc) (Finset.mem_insert_self _ _) (by omega)
    have hav : a.val ∈ K.incidentTop m T.val :=
      mem_incidentTop.mpr ⟨a.property.1, hacard, hTa⟩
    exact ⟨a.val, hav, Subtype.ext rfl⟩
  rw [incidentTop_sd_card_eq_insertionVertices hccard]
  exact (Finset.card_bij f hf hinj hsurj).symm

theorem incidentTop_sd_missing_top_data {m : ℕ} (hm : 0 < m) (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m)
    (hr : K.ranks c = (Finset.Icc 1 (m + 1)).erase (m + 1)) :
    ∃ T ∈ c, T.val.card = m ∧ (∀ b ∈ c, b.val ⊆ T.val) ∧
      (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card := by
  have hmrank : m ∈ K.ranks c := by
    rw [hr]
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hm, by omega⟩⟩
  obtain ⟨T, hTc, hTcard⟩ := mem_ranks.mp hmrank
  refine ⟨T, hTc, hTcard, ?_, incidentTop_sd_card_eq_of_missing_top hK hc hr hTc hTcard⟩
  intro b hb
  apply chain_subset_of_card_le (mem_sd_iff.mp (mem_codimFaces.mp hc).1) hb hTc
  have hbcard := hK b.val b.property.1
  have hbne := rank_ne_of_missing hr hb
  omega

/-- The complete positive-dimensional codimension-one alternative. The first
case also records a retained old top face for transferring carrier information. -/
theorem incidentTop_sd_cases {m : ℕ} (hm : 0 < m) (hK : K.CardBound m)
    {c : Finset (FaceVertex K)} (hc : c ∈ K.sd.codimFaces m) :
    ((K.sd.incidentTop m c).card = 2 ∧
      ∃ T ∈ c, T.val.card = m + 1 ∧ ∀ b ∈ c, b.val ⊆ T.val) ∨
    (∃ T ∈ c, T.val.card = m ∧ (∀ b ∈ c, b.val ⊆ T.val) ∧
      (K.sd.incidentTop m c).card = (K.incidentTop m T.val).card) := by
  obtain ⟨r, hr₁, hr₂, hr⟩ := missing_rank hK hc
  by_cases hrm : r ≤ m
  · left
    refine ⟨incidentTop_sd_card_two_of_missing_rank hK hc hr₁ hrm hr, ?_⟩
    have hmrank : m + 1 ∈ K.ranks c := by
      rw [hr]
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩⟩
    obtain ⟨T, hTc, hTcard⟩ := mem_ranks.mp hmrank
    refine ⟨T, hTc, hTcard, ?_⟩
    intro b hb
    apply chain_subset_of_card_le (mem_sd_iff.mp (mem_codimFaces.mp hc).1) hb hTc
    rw [hTcard]
    exact hK b.val b.property.1
  · right
    have hre : r = m + 1 := by omega
    subst r
    exact incidentTop_sd_missing_top_data hm hK hc hr

end Tingley.FiniteComplex

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.SubdivisionIncidence

namespace OAI

/-!
# Incidence counts for the concrete iterated simplex

The missing-rank alternative for an actual flag transports the old boundary
count, or gives two completions around a retained old top face. Iteration
therefore gives one incident top cell on the original boundary and two in
the interior.
-/

noncomputable section

namespace Tingley

/-- At depth zero the unique top cell is the full original vertex set. -/
theorem incidentTop_zero_eq_singleton (m : ℕ) (s : Finset (IterVertex m 0)) :
    incidentTop m 0 s = {Finset.univ} := by
  classical
  change Finset (Fin (m + 1)) at s
  change (FiniteComplex.full : FiniteComplex (Fin (m + 1))).incidentTop m s =
    {Finset.univ}
  ext t
  rw [FiniteComplex.mem_incidentTop, Finset.mem_singleton]
  constructor
  · rintro ⟨_, ht, _⟩
    exact t.eq_univ_of_card (by simpa only [Fintype.card_fin] using ht)
  · rintro rfl
    exact ⟨FiniteComplex.mem_full _, Finset.card_fin _, Finset.subset_univ _⟩

/-- The initial carrier of a face is that face itself. -/
theorem faceCarrier_zero (m : ℕ) (s : Finset (IterVertex m 0)) :
    faceCarrier m 0 s = s := by
  change Finset (Fin (m + 1)) at s
  change s.biUnion (fun i => {i}) = s
  exact Finset.biUnion_singleton_eq_self

/-- Actual codimension-one incidence for every positive-dimensional iterated
standard simplex. The boundary condition refers to the original coordinates. -/
theorem incidentTop_card_eq_if_boundary {m k : ℕ} (hm : 0 < m) :
    ∀ {s : Finset (IterVertex m k)}, s ∈ codimFaces m k →
      (incidentTop m k s).card =
        if (faceCarrier m k s).card = m then 1 else 2 := by
  classical
  induction k with
  | zero =>
      intro s hs
      have hcard := (mem_codimFaces.mp hs).2
      have hface : (faceCarrier m 0 s).card = m :=
        (congrArg (fun t : Finset (Fin (m + 1)) => t.card)
          (faceCarrier_zero m s)).trans hcard
      rw [incidentTop_zero_eq_singleton, Finset.card_singleton, if_pos hface]
  | succ k ih =>
      intro s hs
      let K := (iterData (Fin (m + 1)) k).complex
      have hK : K.CardBound m := by
        intro t ht
        exact iter_card_le ht
      change s ∈ K.sd.codimFaces m at hs
      rcases FiniteComplex.incidentTop_sd_cases hm hK hs with
        ⟨hcount, T, hTs, hTcard, hmax⟩ | ⟨T, hTs, hTcard, hmax, hcount⟩
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have htop : T.val ∈ topCells m k :=
          mem_topCells.mpr ⟨T.property.1, hTcard⟩
        have hnot : (Finset.univ : Finset (Fin (m + 1))).card ≠ m := by simp
        rw [hcarrier, top_faceCarrier htop, if_neg hnot]
        exact hcount
      · have hcarrier : faceCarrier m (k + 1) s = faceCarrier m k T.val :=
          FiniteComplex.faceCarrier_sd_eq_greatest hTs hmax
        have hcodim : T.val ∈ codimFaces m k :=
          mem_codimFaces.mpr ⟨T.property.1, hTcard⟩
        calc
          (incidentTop m (k + 1) s).card = (incidentTop m k T.val).card := hcount
          _ = if (faceCarrier m k T.val).card = m then 1 else 2 := ih hcodim
          _ = if (faceCarrier m (k + 1) s).card = m then 1 else 2 := by rw [hcarrier]

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.BarycentricZero

namespace OAI

/-!
# The zero-dimensional subdivision and its empty codimension-one face

The subdivision of a zero-dimensional complex has one vertex for each old
singleton face. In particular, iterated subdivision of the point has one
top face, incident to its unique empty codimension-one face.
-/

noncomputable section

namespace Tingley.FiniteComplex

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : FiniteComplex V}

@[simp] theorem incidentTop_empty (K : FiniteComplex V) (m : ℕ) :
    K.incidentTop m ∅ = K.topCells m := by
  classical
  ext s
  simp [incidentTop]

theorem sd_topCells_zero_card (hK : K.CardBound 0) :
    (K.sd.topCells 0).card = (K.topCells 0).card := by
  classical
  let v : ∀ s ∈ K.topCells 0, FaceVertex K := fun s hs =>
    ⟨s, (mem_topCells.mp hs).1,
      Finset.card_pos.mp (by have h := (mem_topCells.mp hs).2; omega)⟩
  let f : ∀ s ∈ K.topCells 0, Finset (FaceVertex K) := fun s hs => {v s hs}
  have hf : ∀ s hs, f s hs ∈ K.sd.topCells 0 := by
    intro s hs
    apply mem_topCells.mpr
    constructor
    · apply mem_sd_iff.mpr
      change K.chain {v s hs}
      simp [chain]
    · change ({v s hs} : Finset (FaceVertex K)).card = 0 + 1
      simp
  have hinj : ∀ s hs t ht, f s hs = f t ht → s = t := by
    intro s hs t ht h
    have hv : v s hs = v t ht := Finset.singleton_inj.mp h
    exact congrArg Subtype.val hv
  have hsurj : ∀ c ∈ K.sd.topCells 0, ∃ s hs, f s hs = c := by
    intro c hc
    obtain ⟨hcface, hccard⟩ := mem_topCells.mp hc
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show c.card = 1 by omega)
    have hacard : a.val.card = 0 + 1 := by
      have hlo := Finset.card_pos.mpr a.property.2
      have hhi := hK a.val a.property.1
      omega
    have ha : a.val ∈ K.topCells 0 := mem_topCells.mpr ⟨a.property.1, hacard⟩
    refine ⟨a.val, ha, ?_⟩
    change ({v a.val ha} : Finset (FaceVertex K)) = {a}
    congr 1
  exact (Finset.card_bij f hf hinj hsurj).symm

theorem sd_pure_zero (hK : K.Pure 0) : K.sd.Pure 0 := by
  classical
  intro c hc
  rcases c.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨s, hs, _⟩ := hK ∅ K.empty_mem
    let a : FaceVertex K := ⟨s, (mem_topCells.mp hs).1,
      Finset.card_pos.mp (by have h := (mem_topCells.mp hs).2; omega)⟩
    refine ⟨{a}, mem_topCells.mpr ⟨mem_sd_iff.mpr ?_, by simp⟩,
      Finset.empty_subset _⟩
    simp [chain]
  · refine ⟨c, mem_topCells.mpr ⟨hc, ?_⟩, Finset.Subset.refl _⟩
    have hlo := Finset.card_pos.mpr hne
    have hhi := sd_cardBound hK.cardBound c hc
    omega

end Tingley.FiniteComplex

namespace Tingley

theorem iter_topCells_zero_card (k : ℕ) : (topCells 0 k).card = 1 := by
  classical
  induction k with
  | zero =>
      change ((FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0).card = 1
      have hfull : (FiniteComplex.full : FiniteComplex (Fin 1)).topCells 0 =
          {Finset.univ} := by
        ext s
        simp only [FiniteComplex.mem_topCells, FiniteComplex.mem_full,
          true_and, Finset.mem_singleton]
        constructor
        · intro hs
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          simpa using hs.ge
        · rintro rfl
          simp
      rw [hfull]
      simp
  | succ k ih =>
      change (((iterData (Fin 1) k).complex).sd.topCells 0).card = 1
      have hK : (iterData (Fin 1) k).complex.CardBound 0 := by
        intro s hs
        exact iter_card_le (m := 0) (k := k) hs
      rw [FiniteComplex.sd_topCells_zero_card hK]
      exact ih

theorem iter_incidentTop_zero_card (k : ℕ) {c : Finset (IterVertex 0 k)}
    (hc : c ∈ codimFaces 0 k) : (incidentTop 0 k c).card = 1 := by
  have hczero : c = ∅ := Finset.card_eq_zero.mp (mem_codimFaces.mp hc).2
  subst c
  change ((iterData (Fin 1) k).complex.incidentTop 0 ∅).card = 1
  rw [FiniteComplex.incidentTop_empty]
  exact iter_topCells_zero_card k

end Tingley

end

end OAI

-- Adapted from OAI.Analysis.SphereIsometry.Sperner

namespace OAI

/-!
# Geometric Sperner parity for the concrete iterated subdivisions

The labels belong to the actual recursively constructed vertex carriers.
The incidence theorem and the exact original-face restriction discharge the
finite counting hypotheses. Induction on dimension proves an odd number of
fully labelled top cells at every subdivision depth.
-/

namespace Tingley

theorem iterated_sperner_odd (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    Odd (((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card) := by
  classical
  induction m with
  | zero =>
      have hfull : ∀ σ ∈ topCells 0 k, σ.image label = Finset.univ := by
        intro σ hσ
        have hcard : σ.card = 1 := (mem_topCells.mp hσ).2
        have hne : σ.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.zero_lt_one)
        obtain ⟨v, hv⟩ := hne
        apply Finset.eq_univ_iff_forall.mpr
        intro i
        refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
        apply Fin.ext
        exact (Nat.lt_one_iff.mp (label v).isLt).trans
          (Nat.lt_one_iff.mp i.isLt).symm
      have hfilter : (topCells 0 k).filter
          (fun σ => σ.image label = Finset.univ) = topCells 0 k :=
        Finset.filter_eq_self.mpr hfull
      rw [hfilter, iter_topCells_zero_card]
      exact ⟨0, rfl⟩
  | succ m ih =>
      let e := lastFaceEmbedding m k
      have hne : ∀ v, label (e v) ≠ Fin.last (m + 1) := by
        intro v hv
        have hlast : Fin.last (m + 1) ∉ iterCarrier (m + 1) k (e v) :=
          (lastFace_range_iff m k (e v)).mpr ⟨v, rfl⟩
        exact hlast (hv ▸ hlabel (e v))
      let lowerLabel : IterVertex m k → Fin (m + 1) :=
        spernerRestrictedLabel e label hne
      have hcast : ∀ v, label (e v) = (lowerLabel v).castSucc :=
        fun v => (castSucc_spernerRestrictedLabel e label hne v).symm
      have hlower : ∀ v, lowerLabel v ∈ iterCarrier m k v := by
        apply restricted_label_mem_carrier e label hne (iterCarrier m k)
        intro v
        have h := hlabel (e v)
        change label (lastFaceEmbedding m k v) ∈
          iterCarrier (m + 1) k (lastFaceEmbedding m k v) at h
        rw [lastFace_carrier] at h
        simpa only [e, Finset.map_eq_image, Fin.coe_castSuccEmb] using h
      have hboundaryCard :
          (((codimFaces (m + 1) k).filter
            (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
              (faceCarrier (m + 1) k τ).card = m + 1)).card) =
          (((topCells m k).filter
            (fun σ => σ.image lowerLabel = Finset.univ)).card) := by
        change (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (τ.biUnion (iterCarrier (m + 1) k)).card = m + 1)).card) = _
        rw [good_boundary_filter_eq_last_face_filter label
          (iterCarrier (m + 1) k) (codimFaces (m + 1) k) hlabel]
        exact mapped_good_family_card_of_map e label lowerLabel hcast
          (topCells m k)
          ((codimFaces (m + 1) k).filter
            (fun τ => Fin.last (m + 1) ∉ faceCarrier (m + 1) k τ))
          (lastFace_top_image m k).symm
      apply FiniteComplex.sperner_odd_of_boundary_odd
        (iterData (Fin ((m + 1) + 1)) k).complex (m + 1) label
        (fun τ => (faceCarrier (m + 1) k τ).card = m + 1)
      · intro τ hτ
        exact incidentTop_card_eq_if_boundary (Nat.succ_pos m) hτ
      · change Odd (((codimFaces (m + 1) k).filter
          (fun τ => τ.image label = spernerSmallLabels (m + 1) ∧
            (faceCarrier (m + 1) k τ).card = m + 1)).card)
        rw [hboundaryCard]
        exact ih lowerLabel hlower

/-- Each actual subdivision contains an actual fully labelled top cell. -/
theorem iterated_sperner_exists (m k : ℕ)
    (label : IterVertex m k → Fin (m + 1))
    (hlabel : ∀ v, label v ∈ iterCarrier m k v) :
    ∃ σ, σ ∈ topCells m k ∧ σ.image label = Finset.univ := by
  classical
  have hodd := iterated_sperner_odd m k label hlabel
  have hcard : ((topCells m k).filter
      (fun σ => σ.image label = Finset.univ)).card ≠ 0 := by
    intro hzero
    rw [hzero] at hodd
    simp at hodd
  obtain ⟨σ, hσ⟩ := Finset.card_ne_zero.mp hcard
  exact ⟨σ, (Finset.mem_filter.mp hσ).1, (Finset.mem_filter.mp hσ).2⟩

end Tingley

end OAI

namespace OMA.C2Square

open Topology ContDiff Manifold
open scoped EuclideanGeometry RealInnerProductSpace

/-- Periodic lift of a curve `γ : Circle → ℝ²` to `ℝ` with period `1`. -/
noncomputable def liftCurve (γ : Circle → ℝ²) (t : ℝ) : ℝ² :=
  γ (Circle.exp (2 * Real.pi * t))

theorem liftCurve_periodic (γ : Circle → ℝ²) : Function.Periodic (liftCurve γ) 1 := by
  intro t
  unfold liftCurve
  have harg : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
  rw [harg]
  congr 1
  exact Circle.periodic_exp (2 * Real.pi * t)

theorem liftCurve_continuous {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ) :
    Continuous (liftCurve γ) :=
  hγ.isEmbedding.continuous.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))

theorem liftCurve_eq_iff {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ)
    (s t : ℝ) : liftCurve γ s = liftCurve γ t ↔ ∃ k : ℤ, s - t = k := by
  unfold liftCurve
  rw [hγ.isEmbedding.injective.eq_iff, Circle.exp_eq_exp]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpi
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hs : s = t + (k : ℝ) := by linarith
    rw [hs]
    ring

theorem liftCurve_injOn {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ) :
    Set.InjOn (liftCurve γ) (Set.Ico 0 1) := by
  intro s hs t ht hst
  obtain ⟨k, hk⟩ := (liftCurve_eq_iff hγ s t).mp hst
  have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hs.1, ht.2]
  have h2 : (k : ℝ) < 1 := by linarith [hs.2, ht.1]
  have hk0 : k = 0 := by
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega
  subst hk0
  simp only [Int.cast_zero] at hk
  linarith

private theorem liftCurve_contDiff {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ) :
    ContDiff ℝ 2 (liftCurve γ) := by
  have he : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 2 (fun t : ℝ => Circle.exp (2 * Real.pi * t)) := by
    have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 2 (fun t : ℝ => 2 * Real.pi * t) :=
      (contDiff_const.mul contDiff_id).contMDiff
    exact (contMDiff_circleExp (m := (2 : WithTop ℕ∞))).comp hlin
  have hw : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 2 (liftCurve γ) := hγ.contMDiff.comp he
  exact contMDiff_iff_contDiff.mp hw

private theorem liftCurve_deriv_ne_zero {γ : Circle → ℝ²}
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ) (t : ℝ) :
    deriv (liftCurve γ) t ≠ 0 := by
  let e : ℝ → Circle := fun s => Circle.exp (2 * Real.pi * s)
  have he_cont : Continuous e := Circle.exp.continuous.comp (continuous_const.mul continuous_id)
  have he_mdiff : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) 2 e :=
    (contMDiff_circleExp (m := (2 : WithTop ℕ∞))).comp
      (contDiff_const.mul contDiff_id).contMDiff
  obtain ⟨F, _, _, himmAll⟩ := hγ.isImmersion
  have himm := himmAll (e t)
  let φ := himm.domChart
  let ψ := himm.codChart
  let eqv := himm.equiv
  have hxt : e t ∈ φ.source := himm.mem_domChart_source
  have hγxt : γ (e t) ∈ ψ.source := himm.mem_codChart_source
  have hφ_mem : φ ∈ IsManifold.maximalAtlas (𝓡 1) 2 Circle := himm.domChart_mem_maximalAtlas
  have hψ_mem : ψ ∈ IsManifold.maximalAtlas (𝓡 2) 2 ℝ² := himm.codChart_mem_maximalAtlas
  have hwr := himm.writtenInCharts
  have hU_mem : e ⁻¹' φ.source ∈ 𝓝 t :=
    he_cont.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hxt)
  -- Differentiability of `φ ∘ e` at `t`
  have hφ_mdiff : ContMDiffAt (𝓡 1) (𝓡 1) 2 φ (e t) :=
    contMDiffAt_of_mem_maximalAtlas hφ_mem hxt
  have hu_diff : DifferentiableAt ℝ (φ ∘ e) t := by
    have hcmd : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 1) 2 (φ ∘ e) t :=
      hφ_mdiff.comp t he_mdiff.contMDiffAt
    exact (contMDiffAt_iff_contDiffAt.mp hcmd).differentiableAt (by simp)
  -- Differentiability of `ψ` at `liftCurve γ t`
  have hψ_diff : DifferentiableAt ℝ ψ (liftCurve γ t) := by
    have hcmd : ContMDiffAt (𝓡 2) (𝓡 2) 2 ψ (liftCurve γ t) :=
      contMDiffAt_of_mem_maximalAtlas hψ_mem hγxt
    exact (contMDiffAt_iff_contDiffAt.mp hcmd).differentiableAt (by simp)
  -- Differentiability of `(fun z : Circle => (z : ℂ)) ∘ φ.symm : ℝ^1 → ℂ` at `φ (e t)`
  have hcoe_diff : DifferentiableAt ℝ ((fun z : Circle => (z : ℂ)) ∘ φ.symm) (φ (e t)) := by
    have : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
    have hφsymm : ContMDiffAt (𝓡 1) (𝓡 1) 2 φ.symm (φ (e t)) :=
      contMDiffAt_symm_of_mem_maximalAtlas hφ_mem (φ.map_source hxt)
    have hcoe_all : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ω (fun z : Circle => (z : ℂ)) :=
      contMDiff_coe_sphere (E := ℂ) (n := 1)
    have hcoe : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) 2 (fun z : Circle => (z : ℂ)) (φ.symm (φ (e t))) :=
      (hcoe_all.of_le (by simp)).contMDiffAt
    have hcomp := hcoe.comp (φ (e t)) hφsymm
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)
  -- Equality near `t`: `ψ ∘ liftCurve γ = eqv ∘ (·, 0) ∘ (φ ∘ e)`
  have h_eq1 : (ψ ∘ liftCurve γ) =ᶠ[𝓝 t] (fun s => eqv ((φ ∘ e) s, (0 : F))) := by
    filter_upwards [hU_mem] with s hs
    have hmem : φ (e s) ∈ (φ.extend (𝓡 1)).target := by
      simpa using φ.map_source hs
    have hval := hwr hmem
    have hleft : φ.symm (φ (e s)) = e s := φ.left_inv hs
    simpa [Function.comp_apply, liftCurve, e, φ, ψ, eqv, hleft] using hval
  -- Equality near `t`: `(fun z : Circle => (z : ℂ)) ∘ e = ((fun z : Circle => (z : ℂ)) ∘ φ.symm) ∘ (φ ∘ e)`
  have h_eq2 : ((fun z : Circle => (z : ℂ)) ∘ e) =ᶠ[𝓝 t]
      (((fun z : Circle => (z : ℂ)) ∘ φ.symm) ∘ (φ ∘ e)) := by
    filter_upwards [hU_mem] with s hs
    change ((e s : ℂ)) = ((φ.symm (φ (e s)) : ℂ))
    rw [φ.left_inv hs]
  intro hzero
  have hw_diff : DifferentiableAt ℝ (liftCurve γ) t :=
    (liftCurve_contDiff hγ).differentiable (by simp) t
  have hfw_zero : fderiv ℝ (liftCurve γ) t = 0 := by
    apply ContinuousLinearMap.ext_ring
    rw [fderiv_apply_one_eq_deriv, hzero]
    rfl
  -- Hence `fderiv ℝ (ψ ∘ liftCurve γ) t = 0`
  have hfg_zero : fderiv ℝ (ψ ∘ liftCurve γ) t = 0 := by
    rw [fderiv_comp t hψ_diff hw_diff, hfw_zero, ContinuousLinearMap.comp_zero]
  -- Hence `fderiv ℝ (fun s => eqv ((φ ∘ e) s, 0)) t = 0`
  have hfg_eq : fderiv ℝ (ψ ∘ liftCurve γ) t =
      (eqv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ F)).comp
        (fderiv ℝ (φ ∘ e) t) := by
    rw [h_eq1.fderiv_eq]
    have hlin : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 1) => eqv (x, (0 : F)))
        (eqv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ F)) ((φ ∘ e) t) :=
      (eqv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ F)).hasFDerivAt
    exact (hlin.comp t hu_diff.hasFDerivAt).fderiv
  have hfu_zero : fderiv ℝ (φ ∘ e) t = 0 := by
    apply ContinuousLinearMap.ext_ring
    have h1 : eqv ((fderiv ℝ (φ ∘ e) t 1), (0 : F)) = 0 := by
      have h0 := congrArg (fun L => L 1) (hfg_eq.symm.trans hfg_zero)
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearEquiv.coe_coe, zero_apply] using h0
    have hpair : ((fderiv ℝ (φ ∘ e) t 1), (0 : F)) = (0, 0) :=
      eqv.injective (by rw [h1]; exact (map_zero eqv).symm)
    exact (congrArg Prod.fst hpair).trans (by rfl)
  -- Hence `fderiv ℝ ((fun z : Circle => (z : ℂ)) ∘ e) t = 0`
  have hfe_zero : fderiv ℝ ((fun z : Circle => (z : ℂ)) ∘ e) t = 0 := by
    rw [h_eq2.fderiv_eq, fderiv_comp t hcoe_diff hu_diff, hfu_zero, ContinuousLinearMap.comp_zero]
  -- But `deriv ((fun z : Circle => (z : ℂ)) ∘ e) t = 2 * π * I * exp (2 * π * t * I) ≠ 0`
  have hfe_deriv : HasDerivAt ((fun z : Circle => (z : ℂ)) ∘ e)
      ((2 * Real.pi : ℂ) * Complex.I * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) t := by
    have hfn : ((fun z : Circle => (z : ℂ)) ∘ e) =
        fun s : ℝ => Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I) := by
      ext s
      change (Circle.exp (2 * Real.pi * s) : ℂ) = _
      rw [Circle.coe_exp]
    rw [hfn]
    have h1 : HasDerivAt (fun s : ℝ => (2 * Real.pi * s : ℝ)) (2 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)
    have h2 : HasDerivAt (fun s : ℝ => (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I))
        (((2 * Real.pi : ℝ) : ℂ) * Complex.I) t := by
      simpa using (h1.ofReal_comp).mul_const Complex.I
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2.cexp
  have hval0 : (2 * Real.pi : ℂ) * Complex.I * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) = 0 := by
    have h1 := congrArg (fun L => L 1) hfe_zero
    rw [fderiv_apply_one_eq_deriv, hfe_deriv.deriv] at h1
    exact h1
  have hne : (2 * Real.pi : ℂ) * Complex.I * Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ Complex.I_ne_zero) (Complex.exp_ne_zero _)
    exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  exact hne hval0

private theorem deriv_liftCurve_periodic {γ : Circle → ℝ²} :
    Function.Periodic (deriv (liftCurve γ)) 1 := by
  intro t
  have hcomp : (fun s => liftCurve γ (s + 1)) = liftCurve γ := funext (liftCurve_periodic γ)
  have h := deriv_comp_add_const (liftCurve γ) 1 t
  simpa [hcomp] using h.symm

theorem exists_local_chord_bound {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ t₁ t₂ t₃ t₄ : ℝ, t₁ ≤ t₂ → t₂ ≤ t₃ → t₃ ≤ t₄ → t₄ - t₁ ≤ δ →
        dist (liftCurve γ t₁) (liftCurve γ t₂) ≤ dist (liftCurve γ t₁) (liftCurve γ t₄) ∧
        dist (liftCurve γ t₂) (liftCurve γ t₃) ≤ dist (liftCurve γ t₁) (liftCurve γ t₄) ∧
        dist (liftCurve γ t₃) (liftCurve γ t₄) ≤ dist (liftCurve γ t₁) (liftCurve γ t₄) := by
  let w := liftCurve γ
  let w' := deriv w
  have hw_c1 : ContDiff ℝ 1 w := (liftCurve_contDiff hγ).of_le (by simp)
  have hw'_cont : Continuous w' := hw_c1.continuous_deriv le_rfl
  have hw_hasDeriv : ∀ t, HasDerivAt w (w' t) t := fun t =>
    (hw_c1.differentiable (by simp) t).hasDerivAt
  -- Positive lower bound `m ≤ ‖w' t‖` on all of `ℝ` by compactness + 1-periodicity
  have hne_Icc : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨t_min, _, ht_min⟩ := isCompact_Icc.exists_isMinOn hne_Icc
    (continuous_norm.comp hw'_cont).continuousOn
  let m : ℝ := ‖w' t_min‖
  have hm_pos : 0 < m := norm_pos_iff.mpr (liftCurve_deriv_ne_zero hγ t_min)
  have hm_le : ∀ t : ℝ, m ≤ ‖w' t‖ := by
    intro t
    let k : ℤ := ⌊t⌋
    have hf : Int.fract t ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    have hper : w' t = w' (Int.fract t) := by
      have hsplit : t = Int.fract t + (k : ℝ) * 1 := by
        have := Int.floor_add_fract t
        dsimp only [k]
        linarith
      calc w' t = w' (Int.fract t + (k : ℝ) * 1) := by rw [← hsplit]
        _ = w' (Int.fract t) := deriv_liftCurve_periodic.int_mul k (Int.fract t)
    rw [hper]
    exact ht_min hf
  -- Uniform continuity of `w'` on `[-1, 2]` gives global `δ ∈ (0, 1/2)` with `‖w' s - w' t‖ ≤ m/4`
  have huc : UniformContinuousOn w' (Set.Icc (-1 : ℝ) 2) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hw'_cont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := huc (m / 4) (by linarith)
  let δ : ℝ := min (δ₀ / 2) (1 / 4)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_lt : δ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hosc : ∀ s t : ℝ, |s - t| ≤ δ → ‖w' s - w' t‖ ≤ m / 4 := by
    intro s t hst
    let k : ℤ := ⌊t⌋
    let t' : ℝ := Int.fract t
    let s' : ℝ := s - k
    have ht'_mem : t' ∈ Set.Icc (-1 : ℝ) 2 := by
      constructor
      · linarith [Int.fract_nonneg t]
      · linarith [Int.fract_lt_one t]
    have hkt : (k : ℝ) + t' = t := Int.floor_add_fract t
    have hdiff : s' - t' = s - t := by dsimp only [s', t']; linarith
    have hs'_mem : s' ∈ Set.Icc (-1 : ℝ) 2 := by
      have h1 : |s' - t'| ≤ 1 / 4 := by rw [hdiff]; exact hst.trans (min_le_right _ _)
      have h2 := abs_le.mp h1
      constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t, h2.1, h2.2]
    have hdist_lt : dist s' t' < δ₀ := by
      rw [Real.dist_eq, hdiff]
      exact hst.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    have hper_s : w' s = w' s' := by
      have hs_eq : s = s' + (k : ℝ) * 1 := by dsimp only [s']; ring
      calc w' s = w' (s' + (k : ℝ) * 1) := by rw [← hs_eq]
        _ = w' s' := deriv_liftCurve_periodic.int_mul k s'
    have hper_t : w' t = w' t' := by
      have ht_eq : t = t' + (k : ℝ) * 1 := by linarith
      calc w' t = w' (t' + (k : ℝ) * 1) := by rw [← ht_eq]
        _ = w' t' := deriv_liftCurve_periodic.int_mul k t'
    rw [hper_s, hper_t, ← dist_eq_norm]
    exact (hδ₀ s' hs'_mem t' ht'_mem hdist_lt).le
  -- Helper: for `a ≤ b ≤ c` in `[t₁, t₄]` with `t₄ - t₁ ≤ δ`, `‖w b - w a‖ ≤ ‖w c - w a‖` and `‖w c - w b‖ ≤ ‖w c - w a‖`
  have hmono_triple : ∀ t₁ t₄ a b c : ℝ,
      t₄ - t₁ ≤ δ → t₁ ≤ a → a ≤ b → b ≤ c → c ≤ t₄ →
      dist (w a) (w b) ≤ dist (w a) (w c) ∧ dist (w b) (w c) ≤ dist (w a) (w c) := by
    intro t₁ t₄ a b c hspan ha hab hbc hc
    let v := w' t₁
    have hv_ge : m ≤ ‖v‖ := hm_le t₁
    have happrox : ∀ p q : ℝ, t₁ ≤ p → p ≤ q → q ≤ t₄ →
        ‖(w q - w p) - (q - p) • v‖ ≤ (‖v‖ / 4) * (q - p) := by
      intro p q hp hpq hq
      let g : ℝ → ℝ² := fun s => w s - s • v
      have hg_deriv : ∀ s ∈ Set.Icc p q, HasDerivWithinAt g (w' s - v) (Set.Icc p q) s := by
        intro s _
        have hsub := ((hw_hasDeriv s).sub ((hasDerivAt_id s).smul_const v)).hasDerivWithinAt
          (s := Set.Icc p q)
        rw [one_smul] at hsub
        exact hsub
      have hg_bound : ∀ s ∈ Set.Icc p q, ‖w' s - v‖ ≤ ‖v‖ / 4 := by
        intro s hs
        have hst : |s - t₁| ≤ δ := by
          rw [abs_of_nonneg (by linarith [hp, hs.1])]
          linarith [hs.2, hq, hspan]
        exact (hosc s t₁ hst).trans (by linarith)
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := g) (f' := fun s => w' s - v) (s := Set.Icc p q) (C := ‖v‖ / 4)
        (fun s hs => hg_deriv s hs) hg_bound (convex_Icc p q)
        (Set.left_mem_Icc.mpr hpq) (Set.right_mem_Icc.mpr hpq)
      have hge : g q - g p = (w q - w p) - (q - p) • v := by
        simp only [g, sub_smul]; abel
      rw [hge, Real.norm_of_nonneg (by linarith)] at hmvt
      exact hmvt
    let u₁ : ℝ² := w b - w a
    let u₂ : ℝ² := w c - w b
    let r₁ : ℝ := b - a
    let r₂ : ℝ := c - b
    let e₁ : ℝ² := u₁ - r₁ • v
    let e₂ : ℝ² := u₂ - r₂ • v
    have hr₁ : 0 ≤ r₁ := by linarith
    have hr₂ : 0 ≤ r₂ := by linarith
    have he₁ : ‖e₁‖ ≤ (‖v‖ / 4) * r₁ := happrox a b ha hab (hbc.trans hc)
    have he₂ : ‖e₂‖ ≤ (‖v‖ / 4) * r₂ := happrox b c (ha.trans hab) hbc hc
    have hu₁_eq : u₁ = r₁ • v + e₁ := by simp [e₁]
    have hu₂_eq : u₂ = r₂ • v + e₂ := by simp [e₂]
    have hinner : 0 ≤ ⟪u₁, u₂⟫ := by
      rw [hu₁_eq, hu₂_eq, inner_add_left, inner_add_right, inner_add_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        real_inner_self_eq_norm_sq]
      simp only [conj_trivial]
      have hcs1 : |⟪v, e₂⟫| ≤ ‖v‖ * ‖e₂‖ := abs_real_inner_le_norm v e₂
      have hcs2 : |⟪e₁, v⟫| ≤ ‖e₁‖ * ‖v‖ := abs_real_inner_le_norm e₁ v
      have hcs3 : |⟪e₁, e₂⟫| ≤ ‖e₁‖ * ‖e₂‖ := abs_real_inner_le_norm e₁ e₂
      have h1 : -(r₁ * (‖v‖ * ((‖v‖ / 4) * r₂))) ≤ r₁ * ⟪v, e₂⟫ := by
        have h10 : -(‖v‖ * ((‖v‖ / 4) * r₂)) ≤ ⟪v, e₂⟫ := by
          have := (abs_le.mp hcs1).1
          nlinarith [norm_nonneg v]
        have := mul_le_mul_of_nonneg_left h10 hr₁
        linarith
      have h2 : -(r₂ * (((‖v‖ / 4) * r₁) * ‖v‖)) ≤ r₂ * ⟪e₁, v⟫ := by
        have h20 : -(((‖v‖ / 4) * r₁) * ‖v‖) ≤ ⟪e₁, v⟫ := by
          have := (abs_le.mp hcs2).1
          nlinarith [norm_nonneg v]
        have := mul_le_mul_of_nonneg_left h20 hr₂
        linarith
      have h3 : -(((‖v‖ / 4) * r₁) * ((‖v‖ / 4) * r₂)) ≤ ⟪e₁, e₂⟫ := by
        have := (abs_le.mp hcs3).1
        nlinarith [norm_nonneg e₁, norm_nonneg e₂, norm_nonneg v]
      have hpos_prod : 0 ≤ r₁ * r₂ * ‖v‖ ^ 2 := by positivity
      linarith
    have hsum : u₁ + u₂ = w c - w a := by simp [u₁, u₂]
    have hnorm_sq : ‖u₁ + u₂‖ ^ 2 = ‖u₁‖ ^ 2 + 2 * ⟪u₁, u₂⟫ + ‖u₂‖ ^ 2 := by
      rw [norm_add_sq_real]
    have hle1 : ‖u₁‖ ≤ ‖u₁ + u₂‖ := by
      nlinarith [norm_nonneg u₁, norm_nonneg (u₁ + u₂), sq_nonneg ‖u₂‖]
    have hle2 : ‖u₂‖ ≤ ‖u₁ + u₂‖ := by
      nlinarith [norm_nonneg u₂, norm_nonneg (u₁ + u₂), sq_nonneg ‖u₁‖]
    rw [hsum] at hle1 hle2
    refine ⟨?_, ?_⟩
    · simpa [dist_eq_norm, norm_sub_rev, u₁] using hle1
    · simpa [dist_eq_norm, norm_sub_rev, u₂] using hle2
  refine ⟨δ, hδ_pos, hδ_lt, fun t₁ t₂ t₃ t₄ h12 h23 h34 hspan => ?_⟩
  have h_12_14 := (hmono_triple t₁ t₄ t₁ t₂ t₄ hspan le_rfl h12 (h23.trans h34) le_rfl)
  have h_23_24 := (hmono_triple t₁ t₄ t₂ t₃ t₄ hspan h12 h23 h34 le_rfl)
  have h_34_14 := (hmono_triple t₁ t₄ t₁ t₃ t₄ hspan le_rfl (h12.trans h23) h34 le_rfl)
  exact ⟨h_12_14.1, h_23_24.1.trans h_12_14.2, h_34_14.2⟩

private lemma mid_eq_of_sq_eq (a0 a1 b0 b1 c0 c1 d0 d1 : ℝ)
    (e1 : (a0 - b0) ^ 2 + (a1 - b1) ^ 2 = (b0 - c0) ^ 2 + (b1 - c1) ^ 2)
    (e2 : (b0 - c0) ^ 2 + (b1 - c1) ^ 2 = (c0 - d0) ^ 2 + (c1 - d1) ^ 2)
    (e3 : (c0 - d0) ^ 2 + (c1 - d1) ^ 2 = (d0 - a0) ^ 2 + (d1 - a1) ^ 2)
    (hu_sq : 0 < (a0 - c0) ^ 2 + (a1 - c1) ^ 2)
    (hv_sq : 0 < (b0 - d0) ^ 2 + (b1 - d1) ^ 2) :
    a0 + c0 = b0 + d0 ∧ a1 + c1 = b1 + d1 := by
  have huz : (a0 - c0) * (a0 + c0 - b0 - d0) + (a1 - c1) * (a1 + c1 - b1 - d1) = 0 := by
    linear_combination (e1 - e3) / 2
  have huv : (a0 - c0) * (b0 - d0) + (a1 - c1) * (b1 - d1) = 0 := by
    linear_combination (-e1 - e3) / 2
  have hvz : (b0 - d0) * (a0 + c0 - b0 - d0) + (b1 - d1) * (a1 + c1 - b1 - d1) = 0 := by
    linear_combination -(e1 + 2 * e2 + e3) / 2
  have hdet_sq :
      ((a0 - c0) * (b1 - d1) - (a1 - c1) * (b0 - d0)) ^ 2 =
        ((a0 - c0) ^ 2 + (a1 - c1) ^ 2) * ((b0 - d0) ^ 2 + (b1 - d1) ^ 2) := by
    linear_combination -((a0 - c0) * (b0 - d0) + (a1 - c1) * (b1 - d1)) * huv
  have hdet_ne : (a0 - c0) * (b1 - d1) - (a1 - c1) * (b0 - d0) ≠ 0 := by
    intro hdet
    have hprod : 0 < ((a0 - c0) ^ 2 + (a1 - c1) ^ 2) * ((b0 - d0) ^ 2 + (b1 - d1) ^ 2) :=
      mul_pos hu_sq hv_sq
    rw [hdet] at hdet_sq
    linarith
  have hz0 : a0 + c0 - b0 - d0 = 0 := by
    have h : ((a0 - c0) * (b1 - d1) - (a1 - c1) * (b0 - d0)) * (a0 + c0 - b0 - d0) = 0 := by
      linear_combination (b1 - d1) * huz - (a1 - c1) * hvz
    exact (mul_eq_zero.mp h).resolve_left hdet_ne
  have hz1 : a1 + c1 - b1 - d1 = 0 := by
    have h : ((a0 - c0) * (b1 - d1) - (a1 - c1) * (b0 - d0)) * (a1 + c1 - b1 - d1) = 0 := by
      linear_combination (a0 - c0) * hvz - (b0 - d0) * huz
    exact (mul_eq_zero.mp h).resolve_left hdet_ne
  exact ⟨by linarith, by linarith⟩

theorem equilateral_equal_diagonals_isRectangle {a b c d : ℝ²}
    (hab_pos : 0 < dist a b)
    (heq1 : dist a b = dist b c)
    (heq2 : dist b c = dist c d)
    (heq3 : dist c d = dist d a)
    (hdiag : dist a c = dist b d)
    (hac : a ≠ c) (hbd : b ≠ d) :
    InscribedSquare.IsRectangle a b c d 1 := by
  have hbc_pos : 0 < dist b c := heq1 ▸ hab_pos
  have hab_ne : a ≠ b := dist_pos.mp hab_pos
  have hbc_ne : b ≠ c := dist_pos.mp hbc_pos
  have hmid : a + c = b + d := by
    have hsq (p q : ℝ²) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
      rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
      simp [Real.dist_eq]
    have e1 : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 = (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 := by
      rw [← hsq a b, ← hsq b c, heq1]
    have e2 : (b 0 - c 0) ^ 2 + (b 1 - c 1) ^ 2 = (c 0 - d 0) ^ 2 + (c 1 - d 1) ^ 2 := by
      rw [← hsq b c, ← hsq c d, heq2]
    have e3 : (c 0 - d 0) ^ 2 + (c 1 - d 1) ^ 2 = (d 0 - a 0) ^ 2 + (d 1 - a 1) ^ 2 := by
      rw [← hsq c d, ← hsq d a, heq3]
    have hu_sq : 0 < (a 0 - c 0) ^ 2 + (a 1 - c 1) ^ 2 := by
      rw [← hsq a c]
      exact sq_pos_of_pos (dist_pos.mpr hac)
    have hv_sq : 0 < (b 0 - d 0) ^ 2 + (b 1 - d 1) ^ 2 := by
      rw [← hsq b d]
      exact sq_pos_of_pos (dist_pos.mpr hbd)
    obtain ⟨h0, h1⟩ := mid_eq_of_sq_eq (a 0) (a 1) (b 0) (b 1) (c 0) (c 1) (d 0) (d 1)
      e1 e2 e3 hu_sq hv_sq
    ext i
    fin_cases i
    · exact h0
    · exact h1
  exact ⟨hmid, hdiag, hab_ne, hbc_ne, by rw [heq1, div_self hbc_pos.ne']⟩

end OMA.C2Square

/-
Part B: signed Sperner parity contradiction on the iterated barycentric subdivision of the
four-dimensional simplex.

The two facets F₀ (first coordinate zero) and F₄ (last coordinate zero) of the 4-simplex are
identified with the subdivided 3-simplex through `face0Emb` and `face4Emb`.  A double count of
(top cell, fully labelled positive facet) incidences shows that the fully labelled positive
boundary facets are even in number, whereas the seam hypotheses identify that number with the
odd Sperner count of the subdivided 3-simplex.
-/

namespace OMA.C2Square

open OAI.Tingley

noncomputable section

/-- Embedding of the k-th subdivision of Δ³ into face F₀ (λ₀ = 0) of Δ⁴. -/
def face0Emb (k : ℕ) : IterVertex 3 k ↪ IterVertex 4 k :=
  (iterEmbedding (Fin.succEmb 4 : Fin 4 ↪ Fin 5) k).toEmbedding

/-- Embedding of the k-th subdivision of Δ³ into face F₄ (λ₄ = 0) of Δ⁴. -/
def face4Emb (k : ℕ) : IterVertex 3 k ↪ IterVertex 4 k :=
  (iterEmbedding (Fin.castSuccEmb : Fin 4 ↪ Fin 5) k).toEmbedding

/- ### Coordinates of embedded subdivision vertices -/

/-- The geometric point of an embedded subdivision vertex: its coordinates along the range of
the coordinate embedding are the old coordinates, and all other coordinates vanish. -/
theorem iterDataPoint_iterEmbedding {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ↪ J) :
    ∀ (k : ℕ) (v : (iterData I k).Vertex),
      (∀ i : I, iterDataPoint J k ((iterEmbedding e k).toEmbedding v) (e i) =
          iterDataPoint I k v i) ∧
        (∀ j : J, (∀ i : I, e i ≠ j) →
          iterDataPoint J k ((iterEmbedding e k).toEmbedding v) j = 0) := by
  intro k
  induction k with
  | zero =>
      intro v
      change I at v
      constructor
      · intro i
        change (Pi.single (e v) (1 : ℝ) : J → ℝ) (e i) = (Pi.single v (1 : ℝ) : I → ℝ) i
        by_cases h : i = v
        · subst h
          rw [Pi.single_eq_same, Pi.single_eq_same]
        · have h' : e i ≠ e v := fun he => h (e.injective he)
          rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']
      · intro j hj
        change (Pi.single (e v) (1 : ℝ) : J → ℝ) j = 0
        exact Pi.single_eq_of_ne (fun h => hj v h.symm) 1
  | succ k ih =>
      intro v
      constructor
      · intro i
        change finiteBarycenter (iterDataPoint J k)
            (v.val.map (iterEmbedding e k).toEmbedding) (e i) =
          finiteBarycenter (iterDataPoint I k) v.val i
        rw [finiteBarycenter_apply, finiteBarycenter_apply, Finset.card_map, Finset.sum_map]
        congr 1
        exact Finset.sum_congr rfl (fun u _ => (ih u).1 i)
      · intro j hj
        change finiteBarycenter (iterDataPoint J k)
            (v.val.map (iterEmbedding e k).toEmbedding) j = 0
        rw [finiteBarycenter_apply, Finset.sum_map,
          Finset.sum_eq_zero (fun u _ => (ih u).2 j hj), mul_zero]

/-- Coordinates of a vertex of the face F₀: the first coordinate vanishes and the remaining
four are the coordinates in the subdivided 3-simplex. -/
theorem iterPoint_face0Emb (k : ℕ) (v : IterVertex 3 k) :
    iterPoint 4 k (face0Emb k v) 0 = 0 ∧
      ∀ j : Fin 4, iterPoint 4 k (face0Emb k v) j.succ = iterPoint 3 k v j := by
  have h := iterDataPoint_iterEmbedding (Fin.succEmb 4 : Fin 4 ↪ Fin 5) k v
  exact ⟨h.2 0 (fun i => Fin.succ_ne_zero i), fun j => h.1 j⟩

/-- Coordinates of a vertex of the face F₄: the last coordinate vanishes and the remaining
four are the coordinates in the subdivided 3-simplex. -/
theorem iterPoint_face4Emb (k : ℕ) (v : IterVertex 3 k) :
    iterPoint 4 k (face4Emb k v) 4 = 0 ∧
      ∀ j : Fin 4, iterPoint 4 k (face4Emb k v) j.castSucc = iterPoint 3 k v j := by
  have h := iterDataPoint_iterEmbedding (Fin.castSuccEmb : Fin 4 ↪ Fin 5) k v
  refine ⟨h.2 4 (fun i hi => ?_), fun j => h.1 j⟩
  have h4 : (i : ℕ) = 4 := congrArg Fin.val hi
  omega

/- ### The signed incidence count -/

/-- Signed incidence parity.  In a finite complex whose codimension-one faces have exactly one
incident top cell on the boundary and exactly two otherwise, suppose that the fully labelled
facets of each top cell all carry the same sign.  Then the fully labelled positive boundary
facets are even in number. -/
theorem signed_boundary_even {V : Type*} [Fintype V] [DecidableEq V]
    (K : FiniteComplex V) (m : ℕ) (label : V → Fin m)
    (pos : Finset V → Prop) [DecidablePred pos]
    (boundary : Finset V → Prop) [DecidablePred boundary]
    (hdegree : ∀ τ ∈ K.codimFaces m,
      (K.incidentTop m τ).card = if boundary τ then 1 else 2)
    (hstable : ∀ σ ∈ K.topCells m,
      ∀ τ₁ ∈ K.codimFaces m, ∀ τ₂ ∈ K.codimFaces m,
        τ₁ ⊆ σ → τ₂ ⊆ σ →
        τ₁.image label = Finset.univ → τ₂.image label = Finset.univ →
        (pos τ₁ ↔ pos τ₂)) :
    Even (((K.codimFaces m).filter
      (fun τ => τ.image label = Finset.univ ∧ pos τ ∧ boundary τ)).card) := by
  -- Regard the labels as labels of a simplex of one more dimension that never use the last one.
  obtain ⟨lab, hlabdef⟩ : ∃ lab : V → Fin (m + 1), ∀ v, lab v = (label v).castSucc :=
    ⟨fun v => (label v).castSucc, fun _ => rfl⟩
  have hlab : ∀ τ : Finset V,
      τ.image lab = spernerSmallLabels m ↔ τ.image label = Finset.univ := by
    intro τ
    have h := mapped_fully_labelled_iff (Function.Embedding.refl V) lab label hlabdef τ
    rwa [Finset.map_refl] at h
  have hnotfull : ∀ σ : Finset V, σ.image lab ≠ Finset.univ := by
    intro σ h
    have hlast : Fin.last m ∈ σ.image lab := by
      rw [h]
      exact Finset.mem_univ _
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hlast
    rw [hlabdef] at hv
    exact Fin.castSucc_ne_last (label v) hv
  -- Each top cell has an even number of fully labelled positive facets.
  have hrow : ∀ σ ∈ K.topCells m,
      (∑ τ ∈ K.codimFaces m,
        if τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ then (1 : ZMod 2) else 0) = 0 := by
    intro σ hσ
    have hG : (((K.codimFaces m).filter
        (fun τ => τ ⊆ σ ∧ τ.image label = Finset.univ)).card : ZMod 2) = 0 := by
      have h1 : (K.codimFaces m).filter (fun τ => τ ⊆ σ ∧ τ.image label = Finset.univ) =
          spernerGoodFacets m lab σ := by
        rw [← FiniteComplex.goodFacets_eq_codim_filter K m lab hσ]
        exact Finset.filter_congr (fun τ _ => by rw [hlab])
      rw [h1, spernerGoodFacets_card_mod_two lab σ (FiniteComplex.mem_topCells.mp hσ).2,
        if_neg (hnotfull σ)]
    rw [Finset.sum_boole]
    by_cases hex : ∃ τ ∈ K.codimFaces m, τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ
    · obtain ⟨τ₀, hτ₀, hτ₀σ, hτ₀full, hτ₀pos⟩ := hex
      have hcongr : (K.codimFaces m).filter
            (fun τ => τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ) =
          (K.codimFaces m).filter (fun τ => τ ⊆ σ ∧ τ.image label = Finset.univ) := by
        apply Finset.filter_congr
        intro τ hτ
        constructor
        · rintro ⟨h1, h2, _⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2, (hstable σ hσ τ₀ hτ₀ τ hτ hτ₀σ h1 hτ₀full h2).mp hτ₀pos⟩
      rw [hcongr]
      exact hG
    · have hempty : (K.codimFaces m).filter
            (fun τ => τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ) = ∅ := by
        apply Finset.filter_false_of_mem
        intro τ hτ h
        exact hex ⟨τ, hτ, h⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero]
  -- Each fully labelled positive facet lies in one or two top cells.
  have hcolumn : ∀ τ ∈ K.codimFaces m,
      (∑ σ ∈ K.topCells m,
        if τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ then (1 : ZMod 2) else 0) =
      if τ.image label = Finset.univ ∧ pos τ ∧ boundary τ then 1 else 0 := by
    intro τ hτ
    by_cases hg : τ.image label = Finset.univ ∧ pos τ
    · have hsum : (∑ σ ∈ K.topCells m,
            if τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ then (1 : ZMod 2) else 0) =
          ∑ σ ∈ K.topCells m, if τ ⊆ σ then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr rfl
        intro σ _
        by_cases hs : τ ⊆ σ
        · rw [if_pos hs, if_pos ⟨hs, hg⟩]
        · rw [if_neg hs, if_neg (fun h => hs h.1)]
      rw [hsum, Finset.sum_boole]
      change ((K.incidentTop m τ).card : ZMod 2) = _
      rw [hdegree τ hτ]
      by_cases hb : boundary τ
      · rw [if_pos hb, if_pos ⟨hg.1, hg.2, hb⟩]
        exact Nat.cast_one
      · rw [if_neg hb, if_neg (fun h => hb h.2.2)]
        exact ZMod.natCast_self 2
    · rw [if_neg (fun h => hg ⟨h.1, h.2.1⟩)]
      exact Finset.sum_eq_zero (fun σ _ => if_neg (fun h => hg h.2))
  apply ZMod.natCast_eq_zero_iff_even.mp
  calc
    (((K.codimFaces m).filter
        (fun τ => τ.image label = Finset.univ ∧ pos τ ∧ boundary τ)).card : ZMod 2) =
        ∑ τ ∈ K.codimFaces m,
          if τ.image label = Finset.univ ∧ pos τ ∧ boundary τ then (1 : ZMod 2) else 0 :=
      Finset.natCast_card_filter _ _
    _ = ∑ τ ∈ K.codimFaces m, ∑ σ ∈ K.topCells m,
          if τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl (fun τ hτ => (hcolumn τ hτ).symm)
    _ = ∑ σ ∈ K.topCells m, ∑ τ ∈ K.codimFaces m,
          if τ ⊆ σ ∧ τ.image label = Finset.univ ∧ pos τ then (1 : ZMod 2) else 0 :=
      Finset.sum_comm
    _ = ∑ σ ∈ K.topCells m, (0 : ZMod 2) := Finset.sum_congr rfl hrow
    _ = 0 := Finset.sum_const_zero

/- ### Boundary facets of the subdivided 4-simplex -/

/-- A codimension-one face that misses an original coordinate has the complementary facet as
its carrier. -/
theorem faceCarrier_eq_erase {k : ℕ} {τ : Finset (IterVertex 4 k)}
    (hτ : τ ∈ codimFaces 4 k) {j : Fin 5} (hj : j ∉ faceCarrier 4 k τ) :
    faceCarrier 4 k τ = Finset.univ.erase j := by
  obtain ⟨hτface, hτcard⟩ := mem_codimFaces.mp hτ
  have hsub : faceCarrier 4 k τ ⊆ Finset.univ.erase j := by
    intro i hi
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    subst h
    exact hj hi
  apply Finset.eq_of_subset_of_card_le hsub
  have hlo := iter_card_le_carrier hτface
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  omega

/-- Such a face has a carrier with exactly four elements. -/
theorem faceCarrier_card_of_not_mem {k : ℕ} {τ : Finset (IterVertex 4 k)}
    (hτ : τ ∈ codimFaces 4 k) {j : Fin 5} (hj : j ∉ faceCarrier 4 k τ) :
    (faceCarrier 4 k τ).card = 4 := by
  have h := congrArg Finset.card (faceCarrier_eq_erase hτ hj)
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin] at h
  omega

/-- A carrier with four elements misses some original coordinate. -/
theorem exists_not_mem_faceCarrier {k : ℕ} {τ : Finset (IterVertex 4 k)}
    (hcard : (faceCarrier 4 k τ).card = 4) : ∃ j : Fin 5, j ∉ faceCarrier 4 k τ := by
  by_contra hall
  have huniv : faceCarrier 4 k τ = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun j => not_not.mp (fun h => hall ⟨j, h⟩))
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- The codimension-one faces missing the coordinate `j` are exactly the images of the top
cells of the subdivided 3-simplex under the embedding of the facet opposite to `j`. -/
theorem faceEmb_top_image (e : Fin 4 ↪ Fin 5) (j : Fin 5)
    (hj : ∀ i : Fin 5, (∃ a, e a = i) ↔ i ≠ j) (k : ℕ) :
    (codimFaces 4 k).filter (fun τ => j ∉ faceCarrier 4 k τ) =
      (topCells 3 k).image (fun s => s.map (iterEmbedding e k).toEmbedding) := by
  ext τ
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hτ, hjτ⟩
    obtain ⟨hτface, hτcard⟩ := mem_codimFaces.mp hτ
    have hsub : FiniteComplex.faceCarrier (iterData (Fin 5) k).carrier τ ⊆
        Finset.univ.map e := by
      intro i hi
      have hne : i ≠ j := by
        intro h
        subst h
        exact hjτ hi
      obtain ⟨a, ha⟩ := (hj i).mpr hne
      exact Finset.mem_map.mpr ⟨a, Finset.mem_univ _, ha⟩
    obtain ⟨t, htface, hts⟩ := (iterEmbedding_face_range_iff e k hτface).mp hsub
    refine ⟨t, mem_topCells.mpr ⟨htface, ?_⟩, hts⟩
    have hcard := congrArg Finset.card hts
    rw [Finset.card_map] at hcard
    omega
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hsface, hscard⟩ := mem_topCells.mp hs
    refine ⟨mem_codimFaces.mpr ⟨((iterEmbedding e k).map_mem_iff s).mpr hsface, ?_⟩, ?_⟩
    · rw [Finset.card_map]
      exact hscard
    · intro hmem
      have hmem' : j ∈ (FiniteComplex.faceCarrier (iterData (Fin 4) k).carrier s).map e := by
        rw [← iterEmbedding_faceCarrier e k s]
        exact hmem
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hmem'
      exact (hj j).mp ⟨a, ha⟩ rfl

/-- The codimension-one faces on F₀ are the images of the top cells of the 3-simplex. -/
theorem face0_top_image (k : ℕ) :
    (codimFaces 4 k).filter (fun τ => (0 : Fin 5) ∉ faceCarrier 4 k τ) =
      (topCells 3 k).image (fun s => s.map (face0Emb k)) :=
  faceEmb_top_image (Fin.succEmb 4) 0 (fun _ => Fin.exists_succ_eq) k

/-- The codimension-one faces on F₄ are the images of the top cells of the 3-simplex. -/
theorem face4_top_image (k : ℕ) :
    (codimFaces 4 k).filter (fun τ => (4 : Fin 5) ∉ faceCarrier 4 k τ) =
      (topCells 3 k).image (fun s => s.map (face4Emb k)) :=
  faceEmb_top_image Fin.castSuccEmb 4 (fun _ => Fin.exists_castSucc_eq) k

/-- A fully labelled face cannot miss any of the coordinates 1, 2, 3. -/
theorem not_mem_faceCarrier_cases {k : ℕ} (label : IterVertex 4 k → Fin 4)
    (hmiss1 : ∀ v : IterVertex 4 k, (1 : Fin 5) ∉ iterCarrier 4 k v → label v ≠ 0)
    (hmiss2 : ∀ v : IterVertex 4 k, (2 : Fin 5) ∉ iterCarrier 4 k v → label v ≠ 1)
    (hmiss3 : ∀ v : IterVertex 4 k, (3 : Fin 5) ∉ iterCarrier 4 k v → label v ≠ 2)
    {τ : Finset (IterVertex 4 k)} (hfull : τ.image label = Finset.univ)
    {j : Fin 5} (hj : j ∉ faceCarrier 4 k τ) : j = 0 ∨ j = 4 := by
  have hnot : ∀ (c : Fin 5) (a : Fin 4),
      (∀ v : IterVertex 4 k, c ∉ iterCarrier 4 k v → label v ≠ a) →
      c ∈ faceCarrier 4 k τ := by
    intro c a hmiss
    by_contra hc
    have ha : a ∈ τ.image label := by
      rw [hfull]
      exact Finset.mem_univ a
    obtain ⟨v, hv, hva⟩ := Finset.mem_image.mp ha
    refine hmiss v (fun hcv => hc ?_) hva
    exact FiniteComplex.mem_faceCarrier.mpr ⟨v, hv, hcv⟩
  have hj1 : j ≠ 1 := by
    intro h
    subst h
    exact hj (hnot 1 0 hmiss1)
  have hj2 : j ≠ 2 := by
    intro h
    subst h
    exact hj (hnot 2 1 hmiss2)
  have hj3 : j ≠ 3 := by
    intro h
    subst h
    exact hj (hnot 3 2 hmiss3)
  have key : ∀ i : Fin 5, i ≠ 1 → i ≠ 2 → i ≠ 3 → i = 0 ∨ i = 4 := by decide
  exact key j hj1 hj2 hj3

/- ### The parity contradiction -/

/-- Abstract signed-facet Sperner parity contradiction on the k-th barycentric subdivision of Δ⁴.
If a 4-coloring `label : IterVertex 4 k → Fin 4` and a predicate `pos : Finset (IterVertex 4 k) → Prop`
satisfy:
- `hmiss1/2/3`: on faces F₁, F₂, F₃ (missing coordinate 1, 2, 3), colors 0, 1, 2 respectively never occur;
- `hF0_sperner`: on face F₀ (`face0Emb k`), the restricted labeling is a valid Sperner labeling of Δ³;
- `hseam_full`: a top 3-simplex `s` of Δ³ maps to a fully-labelled 3-facet on F₀ iff it does on F₄;
- `hseam_sign`: on every fully-labelled top 3-simplex `s` of Δ³, `pos` has opposite truth values on F₀ and F₄;
- `hstable`: within any top 4-simplex `σ ∈ topCells 4 k`, any two fully-labelled 3-facets have the same `pos` value;
then a parity contradiction (`False`) ensues. -/
theorem signed_sperner_contradiction (k : ℕ)
    (label : IterVertex 4 k → Fin 4)
    (pos : Finset (IterVertex 4 k) → Prop)
    [DecidablePred pos]
    (hmiss1 : ∀ v : IterVertex 4 k, (1 : Fin 5) ∉ iterCarrier 4 k v → label v ≠ 0)
    (hmiss2 : ∀ v : IterVertex 4 k, (2 : Fin 5) ∉ iterCarrier 4 k v → label v ≠ 1)
    (hmiss3 : ∀ v : IterVertex 4 k, (3 : Fin 5) ∉ iterCarrier 4 k v → label v ≠ 2)
    (hF0_sperner : ∀ v : IterVertex 3 k, label (face0Emb k v) ∈ iterCarrier 3 k v)
    (hseam_full : ∀ s ∈ topCells 3 k,
      (s.map (face0Emb k)).image label = Finset.univ ↔
        (s.map (face4Emb k)).image label = Finset.univ)
    (hseam_sign : ∀ s ∈ topCells 3 k,
      (s.map (face0Emb k)).image label = Finset.univ →
        (pos (s.map (face4Emb k)) ↔ ¬ pos (s.map (face0Emb k))))
    (hstable : ∀ σ ∈ topCells 4 k,
      ∀ τ₁ ∈ codimFaces 4 k, ∀ τ₂ ∈ codimFaces 4 k,
        τ₁ ⊆ σ → τ₂ ⊆ σ →
        τ₁.image label = Finset.univ → τ₂.image label = Finset.univ →
        (pos τ₁ ↔ pos τ₂)) :
    False := by
  -- Step 1: the fully labelled positive boundary facets are even in number.
  have heven : Even (((codimFaces 4 k).filter
      (fun τ => τ.image label = Finset.univ ∧ pos τ ∧ (faceCarrier 4 k τ).card = 4)).card) :=
    signed_boundary_even (iterData (Fin (4 + 1)) k).complex 4 label pos
      (fun τ => (faceCarrier 4 k τ).card = 4)
      (fun τ hτ => incidentTop_card_eq_if_boundary (m := 4) (k := k) (by decide) hτ)
      hstable
  -- Step 2: every such facet lies on F₀ or on F₄.
  have hsplit : (codimFaces 4 k).filter
        (fun τ => τ.image label = Finset.univ ∧ pos τ ∧ (faceCarrier 4 k τ).card = 4) =
      ((codimFaces 4 k).filter (fun τ => (0 : Fin 5) ∉ faceCarrier 4 k τ)).filter
          (fun τ => τ.image label = Finset.univ ∧ pos τ) ∪
        ((codimFaces 4 k).filter (fun τ => (4 : Fin 5) ∉ faceCarrier 4 k τ)).filter
          (fun τ => τ.image label = Finset.univ ∧ pos τ) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hτ, hfull, hpos, hcard⟩
      obtain ⟨j, hj⟩ := exists_not_mem_faceCarrier hcard
      rcases not_mem_faceCarrier_cases label hmiss1 hmiss2 hmiss3 hfull hj with h | h
      · subst h
        exact Or.inl ⟨⟨hτ, hj⟩, hfull, hpos⟩
      · subst h
        exact Or.inr ⟨⟨hτ, hj⟩, hfull, hpos⟩
    · rintro (⟨⟨hτ, hj⟩, hfull, hpos⟩ | ⟨⟨hτ, hj⟩, hfull, hpos⟩)
      · exact ⟨hτ, hfull, hpos, faceCarrier_card_of_not_mem hτ hj⟩
      · exact ⟨hτ, hfull, hpos, faceCarrier_card_of_not_mem hτ hj⟩
  -- The two families are disjoint: a facet cannot miss two coordinates.
  have hdisj : Disjoint
      (((codimFaces 4 k).filter (fun τ => (0 : Fin 5) ∉ faceCarrier 4 k τ)).filter
        (fun τ => τ.image label = Finset.univ ∧ pos τ))
      (((codimFaces 4 k).filter (fun τ => (4 : Fin 5) ∉ faceCarrier 4 k τ)).filter
        (fun τ => τ.image label = Finset.univ ∧ pos τ)) := by
    rw [Finset.disjoint_left]
    intro τ h0 h4
    obtain ⟨hτ, hj0⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp h0).1
    have hj4 := (Finset.mem_filter.mp (Finset.mem_filter.mp h4).1).2
    apply hj4
    rw [faceCarrier_eq_erase hτ hj0]
    exact Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩
  -- Step 3: transport both families to the subdivided 3-simplex.
  have hcard0 : (((codimFaces 4 k).filter (fun τ => (0 : Fin 5) ∉ faceCarrier 4 k τ)).filter
        (fun τ => τ.image label = Finset.univ ∧ pos τ)).card =
      ((topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ ∧
        pos (s.map (face0Emb k)))).card :=
    mapped_family_filter_card (face0Emb k) (topCells 3 k) _ _ _ (face0_top_image k)
      (fun s _ => Iff.rfl)
  have hcard4 : (((codimFaces 4 k).filter (fun τ => (4 : Fin 5) ∉ faceCarrier 4 k τ)).filter
        (fun τ => τ.image label = Finset.univ ∧ pos τ)).card =
      ((topCells 3 k).filter (fun s => (s.map (face4Emb k)).image label = Finset.univ ∧
        pos (s.map (face4Emb k)))).card :=
    mapped_family_filter_card (face4Emb k) (topCells 3 k) _ _ _ (face4_top_image k)
      (fun s _ => Iff.rfl)
  -- Step 4: the seam turns the positive facets on F₄ into the negative facets on F₀.
  have hseam : (topCells 3 k).filter (fun s => (s.map (face4Emb k)).image label = Finset.univ ∧
        pos (s.map (face4Emb k))) =
      (topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ ∧
        ¬ pos (s.map (face0Emb k))) := by
    apply Finset.filter_congr
    intro s hs
    constructor
    · rintro ⟨hfull4, hpos4⟩
      have hfull0 := (hseam_full s hs).mpr hfull4
      exact ⟨hfull0, (hseam_sign s hs hfull0).mp hpos4⟩
    · rintro ⟨hfull0, hneg0⟩
      exact ⟨(hseam_full s hs).mp hfull0, (hseam_sign s hs hfull0).mpr hneg0⟩
  have htotal : ((topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ ∧
        pos (s.map (face0Emb k)))).card +
      ((topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ ∧
        ¬ pos (s.map (face0Emb k)))).card =
      ((topCells 3 k).filter
        (fun s => (s.map (face0Emb k)).image label = Finset.univ)).card := by
    have hP : (topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ ∧
          pos (s.map (face0Emb k))) =
        ((topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ)).filter
          (fun s => pos (s.map (face0Emb k))) := by
      rw [Finset.filter_filter]
    have hN : (topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ ∧
          ¬ pos (s.map (face0Emb k))) =
        ((topCells 3 k).filter (fun s => (s.map (face0Emb k)).image label = Finset.univ)).filter
          (fun s => ¬ pos (s.map (face0Emb k))) := by
      rw [Finset.filter_filter]
    rw [hP, hN]
    exact Finset.card_filter_add_card_filter_not _
  -- Step 5: Sperner's lemma on F₀ makes the total odd.
  have hodd := iterated_sperner_odd 3 k (fun v => label (face0Emb k v)) hF0_sperner
  have himage : (topCells 3 k).filter
        (fun s => (s.map (face0Emb k)).image label = Finset.univ) =
      (topCells 3 k).filter
        (fun s => s.image (fun v => label (face0Emb k v)) = Finset.univ) := by
    apply Finset.filter_congr
    intro s _
    rw [Finset.map_eq_image, Finset.image_image]
    rfl
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hcard0, hcard4, hseam, htotal, himage] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

end

end OMA.C2Square

namespace OMA.C2Square

open Topology ContDiff Manifold OAI.Tingley Filter
open scoped EuclideanGeometry

noncomputable section

def quadTime (s : Fin 5 → ℝ) : Fin 4 → ℝ :=
  ![s 0, s 0 + s 1, s 0 + s 1 + s 2, s 0 + s 1 + s 2 + s 3]

def cyclicGap (s : Fin 5 → ℝ) : Fin 4 → ℝ :=
  ![s 1, s 2, s 3, s 0 + s 4]

def sideLen (γ : Circle → ℝ²) (s : Fin 5 → ℝ) (i : Fin 4) : ℝ :=
  dist (liftCurve γ (quadTime s i)) (liftCurve γ (quadTime s (i + 1)))

def diagDiff (γ : Circle → ℝ²) (s : Fin 5 → ℝ) : ℝ :=
  dist (liftCurve γ (quadTime s 0)) (liftCurve γ (quadTime s 2)) -
    dist (liftCurve γ (quadTime s 1)) (liftCurve γ (quadTime s 3))

def startFract (s : Fin 5 → ℝ) (i : Fin 4) : ℝ := Int.fract (quadTime s i)

-- The last coordinate distinguishes tied positive gaps after moving the starting point through the seam.
private def sideKey (γ : Circle → ℝ²) (s : Fin 5 → ℝ) (i : Fin 4) : ℝ ×ₗ (ℝ ×ₗ ℝ) :=
  toLex (sideLen γ s i, toLex (cyclicGap s i, startFract s i))

private theorem exists_best (γ : Circle → ℝ²) (s : Fin 5 → ℝ) :
    ∃ i, ∀ j, sideKey γ s j ≤ sideKey γ s i := by
  obtain ⟨i, _, h⟩ := Finset.univ.exists_max_image (sideKey γ s) Finset.univ_nonempty
  exact ⟨i, fun j => h j (Finset.mem_univ _)⟩

def chooseSideLabel (γ : Circle → ℝ²) (s : Fin 5 → ℝ) : Fin 4 :=
  (exists_best γ s).choose

private theorem key_best (γ : Circle → ℝ²) (s : Fin 5 → ℝ) (j : Fin 4) :
    sideKey γ s j ≤ sideKey γ s (chooseSideLabel γ s) :=
  (exists_best γ s).choose_spec j

private theorem side_best (γ : Circle → ℝ²) (s : Fin 5 → ℝ) (j : Fin 4) :
    sideLen γ s j ≤ sideLen γ s (chooseSideLabel γ s) :=
  (Prod.Lex.toLex_le_toLex'.mp (key_best γ s j)).1

private theorem key_lt_of_gap (γ : Circle → ℝ²) (s : Fin 5 → ℝ) {i j : Fin 4}
    (h : sideLen γ s i ≤ sideLen γ s j) (hg : cyclicGap s i < cyclicGap s j) :
    sideKey γ s i < sideKey γ s j := by
  rcases h.lt_or_eq with hl | he
  · exact Prod.Lex.toLex_lt_toLex.mpr (.inl hl)
  · exact Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨he, Prod.Lex.toLex_lt_toLex.mpr (.inl hg)⟩)

private theorem coords {s : Fin 5 → ℝ} (h : s ∈ probabilitySimplexSet (Fin 5)) :
    0 ≤ s 0 ∧ 0 ≤ s 1 ∧ 0 ≤ s 2 ∧ 0 ≤ s 3 ∧ 0 ≤ s 4 ∧
      s 0 + s 1 + s 2 + s 3 + s 4 = 1 := by
  exact ⟨h.1 _, h.1 _, h.1 _, h.1 _, h.1 _, by
    have hh := h.2
    rw [Fin.sum_univ_succ, Fin.sum_univ_four] at hh
    change s 0 + (s 1 + s 2 + s 3 + s 4) = 1 at hh
    linarith⟩

private theorem gap_nonneg {s : Fin 5 → ℝ} (h : s ∈ probabilitySimplexSet (Fin 5)) (i : Fin 4) :
    0 ≤ cyclicGap s i := by
  fin_cases i <;> first | exact h.1 _ | exact add_nonneg (h.1 _) (h.1 _)

private theorem gap_sum {s : Fin 5 → ℝ} (h : s ∈ probabilitySimplexSet (Fin 5)) :
    ∑ i, cyclicGap s i = 1 := by
  obtain ⟨_, _, _, _, _, hs⟩ := coords h
  simpa [Fin.sum_univ_four, cyclicGap, add_comm, add_left_comm, add_assoc] using hs

private theorem time_step {s : Fin 5 → ℝ} (h : s ∈ probabilitySimplexSet (Fin 5)) (i : Fin 4) :
    quadTime s i + cyclicGap s i =
      if i = 3 then quadTime s (i+1) + 1 else quadTime s (i+1) := by
  obtain ⟨_, _, _, _, _, hs⟩ := coords h
  fin_cases i <;> first | rfl |
    change s 0 + s 1 + s 2 + s 3 + (s 0 + s 4) = s 0 + 1; linarith

private theorem lift_step (γ : Circle → ℝ²) {s : Fin 5 → ℝ}
    (h : s ∈ probabilitySimplexSet (Fin 5)) (i : Fin 4) :
    liftCurve γ (quadTime s i + cyclicGap s i) = liftCurve γ (quadTime s (i+1)) := by
  rw [time_step h]
  split
  · exact liftCurve_periodic γ _
  · rfl

private theorem side_zero_of_gap (γ : Circle → ℝ²) {s : Fin 5 → ℝ}
    (h : s ∈ probabilitySimplexSet (Fin 5)) {i : Fin 4} (hg : cyclicGap s i = 0) :
    sideLen γ s i = 0 := by
  rw [sideLen, ← lift_step γ h, hg, add_zero, dist_self]

private theorem best_gap_pos (γ : Circle → ℝ²) {s : Fin 5 → ℝ}
    (h : s ∈ probabilitySimplexSet (Fin 5)) : 0 < cyclicGap s (chooseSideLabel γ s) := by
  by_contra! hz
  have hzero := le_antisymm hz (gap_nonneg h _)
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => gap_nonneg h j)).mp
    (show 0 < ∑ i, cyclicGap s i by rw [gap_sum h]; norm_num)
  exact (not_lt_of_ge (key_best γ s j)) (key_lt_of_gap γ s
    (by rw [side_zero_of_gap γ h hzero]; exact dist_nonneg) (hzero ▸ hj))

private theorem fract_injective_on_gaps {s : Fin 5 → ℝ} (hs : s ∈ probabilitySimplexSet (Fin 5))
    {i j : Fin 4} (hi : 0 < cyclicGap s i) (hj : 0 < cyclicGap s j)
    (he : startFract s i = startFract s j) : i = j := by
  obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp he
  obtain ⟨h0,h1,h2,h3,h4,ht⟩ := coords hs
  have hint : k = 0 ∨ k = 1 ∨ k = -1 := by
    have hb : -1 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 1 := by
      fin_cases i <;> fin_cases j <;> norm_num [quadTime] at hk <;> constructor <;> linarith
    have hl : (-1 : ℤ) ≤ k := by exact_mod_cast hb.1
    have hr : k ≤ (1 : ℤ) := by exact_mod_cast hb.2
    omega
  rcases hint with rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;> first | rfl |
      exfalso; norm_num [quadTime, cyclicGap] at hi hj hk; linarith


private def seam0 (x : Fin 4 → ℝ) : Fin 5 → ℝ := ![0, x 0, x 1, x 2, x 3]
private def seam4 (x : Fin 4 → ℝ) : Fin 5 → ℝ := ![x 0, x 1, x 2, x 3, 0]

private theorem face_point0 (k : ℕ) (v : IterVertex 3 k) :
    iterPoint 4 k (face0Emb k v) = seam0 (iterPoint 3 k v) := by
  obtain ⟨hz, h⟩ := iterPoint_face0Emb k v
  funext i
  exact Fin.cases hz (fun j => by fin_cases j <;> exact h _) i

private theorem face_point4 (k : ℕ) (v : IterVertex 3 k) :
    iterPoint 4 k (face4Emb k v) = seam4 (iterPoint 3 k v) := by
  obtain ⟨hz, h⟩ := iterPoint_face4Emb k v
  funext i
  fin_cases i <;> first | exact hz | exact h 0 | exact h 1 | exact h 2 | exact h 3

private theorem seam_times {x : Fin 4 → ℝ} (hx : x ∈ probabilitySimplexSet (Fin 4)) (i : Fin 4) :
    quadTime (seam4 x) i = quadTime (seam0 x) (i+1) + (if i = 3 then 1 else 0) := by
  have h := hx.2
  rw [Fin.sum_univ_four] at h
  fin_cases i
  · change x 0 = 0 + x 0 + 0
    ring
  · change x 0 + x 1 = 0 + x 0 + x 1 + 0
    ring
  · change x 0 + x 1 + x 2 = 0 + x 0 + x 1 + x 2 + 0
    ring
  · change x 0 + x 1 + x 2 + x 3 = 0 + 1
    linarith

private theorem seam_gaps (x : Fin 4 → ℝ) (i : Fin 4) :
    cyclicGap (seam4 x) i = cyclicGap (seam0 x) (i+1) := by
  fin_cases i <;> simp [cyclicGap, seam0, seam4]

private theorem seam_lift (γ : Circle → ℝ²) {x : Fin 4 → ℝ} (hx : x ∈ probabilitySimplexSet (Fin 4))
    (i : Fin 4) : liftCurve γ (quadTime (seam4 x) i) =
      liftCurve γ (quadTime (seam0 x) (i+1)) := by
  rw [seam_times hx]
  split
  · exact liftCurve_periodic γ _
  · rw [add_zero]

private theorem seam_keys (γ : Circle → ℝ²) {x : Fin 4 → ℝ} (hx : x ∈ probabilitySimplexSet (Fin 4))
    (i : Fin 4) : sideKey γ (seam4 x) i = sideKey γ (seam0 x) (i+1) := by
  simp only [sideKey, sideLen, seam_lift γ hx, seam_gaps, startFract]
  rw [seam_times hx i]
  split <;> simp

private theorem seam_labels (γ : Circle → ℝ²) (k : ℕ) (v : IterVertex 3 k) :
    chooseSideLabel γ (iterPoint 4 k (face4Emb k v)) + 1 =
      chooseSideLabel γ (iterPoint 4 k (face0Emb k v)) := by
  let x := iterPoint 3 k v
  have hx := iterPoint_mem_stdSimplex 3 k v
  have hs : seam0 x ∈ probabilitySimplexSet (Fin 5) := face_point0 k v ▸
    iterPoint_mem_stdSimplex 4 k (face0Emb k v)
  have ht : seam4 x ∈ probabilitySimplexSet (Fin 5) := face_point4 k v ▸
    iterPoint_mem_stdSimplex 4 k (face4Emb k v)
  rw [face_point4, face_point0]
  let a := chooseSideLabel γ (seam4 x)
  let b := chooseSideLabel γ (seam0 x)
  have hh : sideKey γ (seam0 x) (a+1) = sideKey γ (seam0 x) b := by
    refine le_antisymm (key_best γ _ _) ?_
    rw [← seam_keys γ hx a]
    have he : b - 1 + 1 = b := sub_add_cancel _ _
    calc
      _ = sideKey γ (seam4 x) (b-1) := by rw [seam_keys γ hx, he]
      _ ≤ _ := key_best γ _ _
  apply fract_injective_on_gaps hs
  · rw [← seam_gaps]
    exact best_gap_pos γ ht
  · exact best_gap_pos γ hs
  · exact congrArg (fun z : ℝ ×ₗ (ℝ ×ₗ ℝ) => (ofLex (ofLex z).2).2) hh

private theorem seam_diag (γ : Circle → ℝ²) (k : ℕ) (v : IterVertex 3 k) :
    diagDiff γ (iterPoint 4 k (face4Emb k v)) = -diagDiff γ (iterPoint 4 k (face0Emb k v)) := by
  rw [face_point4, face_point0]
  simp only [diagDiff, seam_lift γ (iterPoint_mem_stdSimplex 3 k v)]
  let q := fun i => liftCurve γ (quadTime (seam0 (iterPoint 3 k v)) i)
  change dist (q 1) (q 3) - dist (q 2) (q 0) = -(dist (q 0) (q 2) - dist (q 1) (q 3))
  rw [dist_comm (q 2) (q 0)]
  ring

private theorem continuous_time (i : Fin 4) : Continuous (fun s => quadTime s i) := by
  fin_cases i <;> simp [quadTime] <;> fun_prop

private theorem continuous_gap (i : Fin 4) : Continuous (fun s => cyclicGap s i) := by
  fin_cases i <;> simp [cyclicGap] <;> fun_prop

private theorem continuous_side {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ)
    (i : Fin 4) : Continuous (fun s => sideLen γ s i) :=
  ((liftCurve_continuous hγ).comp (continuous_time i)).dist
    ((liftCurve_continuous hγ).comp (continuous_time (i+1)))

private theorem continuous_diag {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ) :
    Continuous (diagDiff γ) :=
  (((liftCurve_continuous hγ).comp (continuous_time 0)).dist
    ((liftCurve_continuous hγ).comp (continuous_time 2))).sub
    (((liftCurve_continuous hγ).comp (continuous_time 1)).dist
      ((liftCurve_continuous hγ).comp (continuous_time 3)))


private def ChordBound (γ : Circle → ℝ²) (δ : ℝ) : Prop :=
  ∀ a b c d : ℝ, a ≤ b → b ≤ c → c ≤ d → d - a ≤ δ →
    dist (liftCurve γ a) (liftCurve γ b) ≤ dist (liftCurve γ a) (liftCurve γ d) ∧
    dist (liftCurve γ b) (liftCurve γ c) ≤ dist (liftCurve γ a) (liftCurve γ d) ∧
    dist (liftCurve γ c) (liftCurve γ d) ≤ dist (liftCurve γ a) (liftCurve γ d)

-- Unwrap the three short sides into a single interval opposite the long parameter gap.
private theorem local_dominance {γ : Circle → ℝ²} {δ : ℝ} (hc : ChordBound γ δ)
    {s : Fin 5 → ℝ} (hs : s ∈ probabilitySimplexSet (Fin 5)) (j : Fin 4)
    (hj : 1 - δ ≤ cyclicGap s j) (i : Fin 4) : sideLen γ s i ≤ sideLen γ s j := by
  obtain ⟨h0,h1,h2,h3,h4,hsum⟩ := coords hs
  have hp (t : ℝ) : liftCurve γ (t + 1) = liftCurve γ t := liftCurve_periodic γ t
  fin_cases j
  · change 1 - δ ≤ s 1 at hj
    have hh := hc (quadTime s 1) (quadTime s 2) (quadTime s 3) (quadTime s 0 + 1)
      (by change (s 0 + s 1) ≤ (s 0 + s 1 + s 2); linarith)
      (by change (s 0 + s 1 + s 2) ≤ (s 0 + s 1 + s 2 + s 3); linarith)
      (by change (s 0 + s 1 + s 2 + s 3) ≤ (s 0 + 1); linarith)
      (by change (s 0 + 1) - (s 0 + s 1) ≤ δ; linarith)
    simp only [hp] at hh
    rw [dist_comm (liftCurve γ (quadTime s 1)) (liftCurve γ (quadTime s 0))] at hh
    obtain ⟨ha,hb,hd⟩ := hh
    fin_cases i <;> first | exact le_rfl | exact ha | exact hb | exact hd
  · change 1 - δ ≤ s 2 at hj
    have hh := hc (quadTime s 2) (quadTime s 3) (quadTime s 0 + 1) (quadTime s 1 + 1)
      (by change (s 0 + s 1 + s 2) ≤ (s 0 + s 1 + s 2 + s 3); linarith)
      (by change (s 0 + s 1 + s 2 + s 3) ≤ (s 0 + 1); linarith)
      (by change (s 0 + 1) ≤ (s 0 + s 1 + 1); linarith)
      (by change (s 0 + s 1 + 1) - (s 0 + s 1 + s 2) ≤ δ; linarith)
    simp only [hp] at hh
    rw [dist_comm (liftCurve γ (quadTime s 2)) (liftCurve γ (quadTime s 1))] at hh
    obtain ⟨ha,hb,hd⟩ := hh
    fin_cases i <;> first | exact le_rfl | exact ha | exact hb | exact hd
  · change 1 - δ ≤ s 3 at hj
    have hh := hc (quadTime s 3) (quadTime s 0 + 1) (quadTime s 1 + 1) (quadTime s 2 + 1)
      (by change (s 0 + s 1 + s 2 + s 3) ≤ (s 0 + 1); linarith)
      (by change (s 0 + 1) ≤ (s 0 + s 1 + 1); linarith)
      (by change (s 0 + s 1 + 1) ≤ (s 0 + s 1 + s 2 + 1); linarith)
      (by change (s 0 + s 1 + s 2 + 1) - (s 0 + s 1 + s 2 + s 3) ≤ δ; linarith)
    simp only [hp] at hh
    rw [dist_comm (liftCurve γ (quadTime s 3)) (liftCurve γ (quadTime s 2))] at hh
    obtain ⟨ha,hb,hd⟩ := hh
    fin_cases i <;> first | exact le_rfl | exact ha | exact hb | exact hd
  · change 1 - δ ≤ s 0 + s 4 at hj
    have hh := hc (quadTime s 0) (quadTime s 1) (quadTime s 2) (quadTime s 3)
      (by change (s 0) ≤ (s 0 + s 1); linarith)
      (by change (s 0 + s 1) ≤ (s 0 + s 1 + s 2); linarith)
      (by change (s 0 + s 1 + s 2) ≤ (s 0 + s 1 + s 2 + s 3); linarith)
      (by change (s 0 + s 1 + s 2 + s 3) - (s 0) ≤ δ; linarith)
    rw [dist_comm (liftCurve γ (quadTime s 0)) (liftCurve γ (quadTime s 3))] at hh
    obtain ⟨ha,hb,hd⟩ := hh
    fin_cases i <;> first | exact le_rfl | exact ha | exact hb | exact hd

private theorem label_of_large_gap {γ : Circle → ℝ²} {δ : ℝ} (hd : δ < 1/2)
    (hc : ChordBound γ δ) {s : Fin 5 → ℝ} (hs : s ∈ probabilitySimplexSet (Fin 5))
    (j : Fin 4) (hj : 1-δ ≤ cyclicGap s j) : chooseSideLabel γ s = j := by
  by_contra hn
  let i := chooseSideLabel γ s
  have hsum : cyclicGap s i + cyclicGap s j ≤ 1 := by
    calc
      _ = ∑ m ∈ ({i,j} : Finset (Fin 4)), cyclicGap s m := by simp [i, hn]
      _ ≤ ∑ m, cyclicGap s m := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun x _ _ => gap_nonneg hs x)
      _ = 1 := gap_sum hs
  exact (not_lt_of_ge (key_best γ s j)) (key_lt_of_gap γ s
    (local_dominance hc hs j hj i) (by linarith : cyclicGap s i < cyclicGap s j))


private theorem square_of_limit {γ : Circle → ℝ²} (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ)
    {s : Fin 5 → ℝ} (hs : s ∈ probabilitySimplexSet (Fin 5))
    (he : ∀ i j, sideLen γ s i = sideLen γ s j)
    (hd : diagDiff γ s = 0) (hg : ∀ i, cyclicGap s i < 1) :
    ∃ t₁ t₂ t₃ t₄, InscribedSquare.IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1 := by
  have hp : 0 < sideLen γ s 0 := by
    by_contra! hz
    have hz0 : sideLen γ s 0 = 0 := le_antisymm hz dist_nonneg
    have hall (i : Fin 4) : cyclicGap s i = 0 := by
      have hlen := (he i 0).trans hz0
      rw [sideLen, ← lift_step γ hs, dist_eq_zero] at hlen
      obtain ⟨n, hn⟩ := (liftCurve_eq_iff hγ _ _).mp hlen.symm
      have hn' : cyclicGap s i = (n : ℝ) := by linarith
      have h0 : (0 : ℤ) ≤ n := by exact_mod_cast (hn' ▸ gap_nonneg hs i : 0 ≤ (n : ℝ))
      have h1 : n < (1 : ℤ) := by exact_mod_cast (hn' ▸ hg i : (n : ℝ) < 1)
      have : n = 0 := by omega
      simpa [this] using hn'
    have hh := gap_sum hs
    simp [hall] at hh
  have hpos (i : Fin 4) : 0 < cyclicGap s i := by
    by_contra! hh
    have := side_zero_of_gap γ hs (le_antisymm hh (gap_nonneg hs i))
    linarith [he i 0]
  have hne (i j : Fin 4) (hij : i ≠ j) :
      liftCurve γ (quadTime s i) ≠ liftCurve γ (quadTime s j) := by
    intro h
    exact hij (fract_injective_on_gaps hs (hpos i) (hpos j)
      (Int.fract_eq_fract.mpr ((liftCurve_eq_iff hγ _ _).mp h)))
  exact ⟨_, _, _, _, equilateral_equal_diagonals_isRectangle hp (he 0 1) (he 1 2) (he 2 3)
    (sub_eq_zero.mp hd) (hne 0 2 (by decide)) (hne 1 3 (by decide))⟩

private def vertexLabel (γ : Circle → ℝ²) (k : ℕ) (v : IterVertex 4 k) :=
  chooseSideLabel γ (iterPoint 4 k v)

private def vertexDiag (γ : Circle → ℝ²) (k : ℕ) (v : IterVertex 4 k) :=
  diagDiff γ (iterPoint 4 k v)

def facetDiagSum (γ : Circle → ℝ²) (k : ℕ) (τ : Finset (IterVertex 4 k)) : ℝ :=
  ∑ v ∈ τ, vertexDiag γ k v

private theorem full_iff_witness {α β : Type*} [Fintype β] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.image f = Finset.univ ↔ ∀ i, ∃ v ∈ s, f v = i := by
  constructor
  · intro h i
    apply Finset.mem_image.mp
    rw [h]
    exact Finset.mem_univ _
  · intro h
    exact Finset.eq_univ_of_forall (fun i => Finset.mem_image.mpr (h i))

private theorem seam_full (γ : Circle → ℝ²) (k : ℕ) (s : Finset (IterVertex 3 k)) :
    (s.map (face0Emb k)).image (vertexLabel γ k) = Finset.univ ↔
      (s.map (face4Emb k)).image (vertexLabel γ k) = Finset.univ := by
  rw [full_iff_witness, full_iff_witness]
  constructor
  · intro h i
    obtain ⟨_, hv, hi⟩ := h (i+1)
    obtain ⟨v,hvin,rfl⟩ := Finset.mem_map.mp hv
    exact ⟨_, Finset.mem_map.mpr ⟨v,hvin,rfl⟩, add_right_cancel ((seam_labels γ k v).trans hi)⟩
  · intro h i
    obtain ⟨_, hv, hi⟩ := h (i-1)
    obtain ⟨v,hvin,rfl⟩ := Finset.mem_map.mp hv
    exact ⟨_, Finset.mem_map.mpr ⟨v,hvin,rfl⟩,
      (seam_labels γ k v).symm.trans ((congrArg (· + 1) hi).trans (sub_add_cancel i 1))⟩

private theorem vertex_boundary (γ : Circle → ℝ²) (k : ℕ) (v : IterVertex 4 k)
    (i : Fin 4) (hi : i ≠ 3) (hm : i.succ ∉ iterCarrier 4 k v) : vertexLabel γ k v ≠ i := by
  intro hl
  have hp := best_gap_pos γ (iterPoint_mem_stdSimplex 4 k v)
  change 0 < cyclicGap (iterPoint 4 k v) (vertexLabel γ k v) at hp
  rw [hl] at hp
  apply hm
  apply (iterPoint_pos_iff _ _ _ _).mp
  fin_cases i <;> first | exact hp | contradiction

private theorem face0_boundary (γ : Circle → ℝ²) (k : ℕ) (v : IterVertex 3 k) :
    vertexLabel γ k (face0Emb k v) ∈ iterCarrier 3 k v := by
  apply (iterPoint_pos_iff 3 k v _).mp
  have h := best_gap_pos γ (iterPoint_mem_stdSimplex 4 k (face0Emb k v))
  change 0 < cyclicGap (iterPoint 4 k (face0Emb k v)) (vertexLabel γ k (face0Emb k v)) at h
  rw [face_point0] at h
  generalize vertexLabel γ k (face0Emb k v) = i at *
  fin_cases i <;> simpa [cyclicGap, seam0] using h

private theorem facet_in_top {k : ℕ} {τ : Finset (IterVertex 4 k)} (hτ : τ ∈ codimFaces 4 k) :
    ∃ σ ∈ topCells 4 k, τ ⊆ σ := by
  have hc := incidentTop_card_eq_if_boundary (by decide : 0 < 4) hτ
  have hp : 0 < (incidentTop 4 k τ).card := by rw [hc]; split <;> decide
  obtain ⟨σ,hσ⟩ := Finset.card_pos.mp hp
  obtain ⟨ha,hb,hs⟩ := mem_incidentTop.mp hσ
  exact ⟨σ,mem_topCells.mpr ⟨ha,hb⟩,hs⟩

private def Crossing (γ : Circle → ℝ²) (k : ℕ) (σ : Finset (IterVertex 4 k)) : Prop :=
  (∀ i, ∃ v ∈ σ, vertexLabel γ k v = i) ∧
  (∃ u ∈ σ, vertexDiag γ k u ≤ 0) ∧ ∃ w ∈ σ, 0 ≤ vertexDiag γ k w

private theorem uniform_sign {γ : Circle → ℝ²} {k : ℕ} {σ τ : Finset (IterVertex 4 k)}
    (hc : ¬ Crossing γ k σ) (ht : τ ⊆ σ) (hf : τ.image (vertexLabel γ k) = Finset.univ) :
    (∀ v ∈ σ, 0 < vertexDiag γ k v) ∨ (∀ v ∈ σ, vertexDiag γ k v < 0) := by
  classical
  have hfull := (full_iff_witness _ _).mp hf
  by_contra! hn
  exact hc ⟨fun i => by
    obtain ⟨v,hv,hi⟩ := hfull i
    exact ⟨v,ht hv,hi⟩, hn.1, hn.2⟩

private def GoodLevel (γ : Circle → ℝ²) (k : ℕ) : Prop :=
  (∀ τ ∈ codimFaces 4 k, τ.image (vertexLabel γ k) = Finset.univ → facetDiagSum γ k τ ≠ 0) ∧
    ∀ σ ∈ topCells 4 k, ∀ a ∈ codimFaces 4 k, ∀ b ∈ codimFaces 4 k, a ⊆ σ → b ⊆ σ →
      a.image (vertexLabel γ k) = Finset.univ → b.image (vertexLabel γ k) = Finset.univ →
      (0 < facetDiagSum γ k a ↔ 0 < facetDiagSum γ k b)

-- If no fully labelled cell contains both diagonal signs, each of its full facets
-- has a nonzero diagonal sum and the sums in a common cell have the same sign.
private theorem good_of_no_crossing {γ : Circle → ℝ²} {k : ℕ}
    (hn : ∀ σ ∈ topCells 4 k, ¬ Crossing γ k σ) : GoodLevel γ k := by
  constructor
  · intro τ ht hf
    obtain ⟨σ,hσ,hsub⟩ := facet_in_top ht
    have hpos : τ.Nonempty := Finset.card_pos.mp (by rw [(mem_codimFaces.mp ht).2]; decide)
    rcases uniform_sign (hn σ hσ) hsub hf with ha | hb
    · exact (Finset.sum_pos (fun v hv => ha v (hsub hv)) hpos).ne'
    · exact (Finset.sum_neg (fun v hv => hb v (hsub hv)) hpos).ne
  · intro σ hσ a ha b hb hsuba hsubb hfa _
    have hna := Finset.card_pos.mp (show 0 < a.card by rw [(mem_codimFaces.mp ha).2]; decide)
    have hnb := Finset.card_pos.mp (show 0 < b.card by rw [(mem_codimFaces.mp hb).2]; decide)
    rcases uniform_sign (hn σ hσ) hsuba hfa with hp | hm
    · exact iff_of_true (Finset.sum_pos (fun v hv => hp v (hsuba hv)) hna)
        (Finset.sum_pos (fun v hv => hp v (hsubb hv)) hnb)
    · exact iff_of_false (not_lt_of_ge (Finset.sum_neg (fun v hv => hm v (hsuba hv)) hna).le)
        (not_lt_of_ge (Finset.sum_neg (fun v hv => hm v (hsubb hv)) hnb).le)

private theorem contradiction_of_good_level (γ : Circle → ℝ²) (k : ℕ) (hk : GoodLevel γ k) : False := by
  classical
  apply signed_sperner_contradiction k (vertexLabel γ k) (fun τ => 0 < facetDiagSum γ k τ)
  · intro v
    exact vertex_boundary γ k v 0 (by decide)
  · intro v
    exact vertex_boundary γ k v 1 (by decide)
  · intro v
    exact vertex_boundary γ k v 2 (by decide)
  · exact face0_boundary γ k
  · exact fun s _ => seam_full γ k s
  · intro s hs hf
    have ht : s.map (face4Emb k) ∈ codimFaces 4 k := lastFace_map_top_mem 3 k hs
    have hne := hk.1 _ ht ((seam_full γ k s).mp hf)
    have he : facetDiagSum γ k (s.map (face4Emb k)) = -facetDiagSum γ k (s.map (face0Emb k)) := by
      simp only [facetDiagSum, Finset.sum_map, vertexDiag, seam_diag, Finset.sum_neg_distrib]
    change 0 < facetDiagSum γ k _ ↔ ¬ 0 < facetDiagSum γ k _
    constructor <;> intro hh <;> push Not at * <;> rcases hne.lt_or_gt with h | h <;> linarith
  · exact hk.2


set_option maxHeartbeats 800000 in
private theorem square_of_crossings (γ : Circle → ℝ²)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ)
    (hc : ∀ k, ∃ σ ∈ topCells 4 k, Crossing γ k σ) :
    ∃ t₁ t₂ t₃ t₄, InscribedSquare.IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1 := by
  classical
  obtain ⟨δ, hδ, hhalf, hchord⟩ := exists_local_chord_bound hγ
  choose σ hσ hcross using hc
  choose v hv hvlabel using fun k => (hcross k).1
  choose u hu huneg using fun k => (hcross k).2.1
  choose w hw hwpos using fun k => (hcross k).2.2
  let p (k : ℕ) := iterPoint 4 k (v k 0)
  have hcompact : IsCompact (probabilitySimplexSet (Fin 5)) := isCompact_iff_compactSpace.mpr
    (probabilitySimplex_compactSpace _)
  obtain ⟨s, hs, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (x := p) (fun k => iterPoint_mem_stdSimplex 4 k _)
  -- Shrinking mesh gives the same limit for every choice of vertex in these cells.
  have hall (z : (k : ℕ) → IterVertex 4 k) (hz : ∀ k, z k ∈ σ k) :
      Tendsto (fun n => iterPoint 4 (φ n) (z (φ n))) atTop (𝓝 s) := by
    apply hlim.congr_dist
    apply squeeze_zero (g := fun n => ((4 : ℝ) / (4+1)) ^ (φ n)) (fun _ => dist_nonneg)
    · intro n
      rw [dist_eq_norm]
      exact iterPoint_mesh 4 _ _ (mem_topCells.mp (hσ _)).1 _ (hv _ 0) _ (hz _)
    · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (4:ℝ)/(4+1))
        (by norm_num)).comp hφ.tendsto_atTop
  have hsides (i j : Fin 4) : sideLen γ s j ≤ sideLen γ s i := by
    have hh := hall (fun k => v k i) (fun k => hv k i)
    apply le_of_tendsto_of_tendsto' ((continuous_side hγ j).continuousAt.tendsto.comp hh)
      ((continuous_side hγ i).continuousAt.tendsto.comp hh)
    intro n
    have h := side_best γ (iterPoint 4 (φ n) (v (φ n) i)) j
    change sideLen γ _ j ≤ sideLen γ _ (vertexLabel γ (φ n) (v (φ n) i)) at h
    rwa [hvlabel] at h
  apply square_of_limit hγ hs (fun i j => le_antisymm (hsides j i) (hsides i j))
  · exact le_antisymm
      (le_of_tendsto_of_tendsto' ((continuous_diag hγ).continuousAt.tendsto.comp (hall u hu))
        tendsto_const_nhds (fun n => huneg (φ n)))
      (le_of_tendsto_of_tendsto' tendsto_const_nhds
        ((continuous_diag hγ).continuousAt.tendsto.comp (hall w hw)) (fun n => hwpos (φ n)))
  · intro j
    suffices cyclicGap s j < 1-δ/2 by linarith
    by_contra! hlarge
    let i : Fin 4 := j + 1
    have hne : i ≠ j := by dsimp [i]; fin_cases j <;> decide
    have hnear := (continuous_gap j).continuousAt.tendsto.comp
      (hall (fun k => v k i) (fun k => hv k i))
    have hev := hnear.eventually (lt_mem_nhds (show 1-δ < cyclicGap s j by linarith))
    obtain ⟨n,hn⟩ := hev.exists
    exact hne ((hvlabel (φ n) i).symm.trans
      (label_of_large_gap hhalf hchord (iterPoint_mem_stdSimplex 4 (φ n) _) j hn.le))

theorem exists_inscribed_square_of_C2_proof (γ : Circle → ℝ²)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ) :
    ∃ t₁ t₂ t₃ t₄, InscribedSquare.IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1 := by
  classical
  by_contra hno
  have hgood : ∃ k, GoodLevel γ k := by
    by_contra! hbad
    apply hno
    apply square_of_crossings γ hγ
    intro k
    by_contra! hn
    exact hbad k (good_of_no_crossing hn)
  obtain ⟨k, hk⟩ := hgood
  exact contradiction_of_good_level γ k hk

end

end OMA.C2Square

theorem OMA.solution : type_of% @InscribedSquare.exists_inscribed_square_of_C2 :=
  OMA.C2Square.exists_inscribed_square_of_C2_proof
