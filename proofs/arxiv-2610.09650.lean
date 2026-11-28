import OMAStatements.S_arxiv_2610_09650

/-
Proof modules adapted from James Fairfax-Ball's TreeStack formalization.
Donor pin: 4d4969703a9f0ca7a51cbe7edf0f0338cc95cafb.
The module imports were consolidated for the standalone checker.

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
/- Source module: TreeStack.Basic.lean -/
namespace TreeStack

/-- A pebble configuration on a vertex type. -/
abbrev Configuration (V : Type*) := V → ℕ

/-- Total number of pebbles in a finite configuration. -/
def mass {V : Type*} [Fintype V] (C : Configuration V) : ℕ :=
  ∑ v, C v

/-- The (set-valued) support of a configuration. -/
def support {V : Type*} (C : Configuration V) : Set V :=
  {v | 0 < C v}

/-- A finite simple tree, using Mathlib's connected-acyclic tree predicate. -/
structure FiniteTree (V : Type*) [Fintype V] where
  graph : SimpleGraph V
  isTree : graph.IsTree

@[simp] theorem mem_support_iff {V : Type*} {C : Configuration V} {v : V} :
    v ∈ support C ↔ 0 < C v := Iff.rfl

end TreeStack

/- Source module: TreeStack.Estimator.lean -/
namespace TreeStack

open scoped BigOperators Classical

/-- Degree-one vertices other than the chosen root. -/
noncomputable def leafVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v ≠ r ∧ T.graph.degree v = 1

/-- Vertices that contribute to the source definition of sigma:
the root, together with every vertex of degree greater than one. -/
noncomputable def sigmaVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v = r ∨ 1 < T.graph.degree v

/-- Internal vertices different from the root.  This is the part of
`sigmaVertices` left after splitting off the root contribution. -/
noncomputable def nonRootInternalVertices {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    v ≠ r ∧ 1 < T.graph.degree v

/-- The source leaf count: degree-one vertices other than the root. -/
noncomputable def leafCount {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  (leafVertices T r).card

/-- The source quantity sigma_T(r), including its leading one. -/
noncomputable def sigma {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  1 + ∑ v ∈ sigmaVertices T r,
    T.graph.degree v * 2 ^ T.graph.dist r v

/-- The source rooted estimator sigma_T(r) + leaf_T(r). -/
noncomputable def rootEstimate {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) : ℕ :=
  sigma T r + leafCount T r

/-- The source tree estimator, the maximum rooted estimator. -/
noncomputable def estim {V : Type*} [Fintype V]
    (T : FiniteTree V) : ℕ :=
  (Finset.univ : Finset V).sup (rootEstimate T)

/-- Split the sigma support into the root and the non-root internal vertices. -/
theorem sigmaVertices_eq_insert {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    sigmaVertices T r = insert r (nonRootInternalVertices T r) := by
  ext v
  by_cases hvr : v = r
  · simp [sigmaVertices, nonRootInternalVertices, hvr]
  · simp [sigmaVertices, nonRootInternalVertices, hvr]

/-- Correct root-sensitive expansion of sigma.  In particular, the root
contribution is retained even when the root itself is a leaf. -/
theorem sigma_corrected_expansion {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    sigma T r =
      1 + T.graph.degree r +
        ∑ v ∈ nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by
  rw [sigma, sigmaVertices_eq_insert]
  have hnot : r ∉ nonRootInternalVertices T r := by
    simp [nonRootInternalVertices]
  rw [Finset.sum_insert hnot]
  simp [Nat.add_assoc]

/-- Correct root-sensitive expansion of the rooted estimator.
This replaces the false helper identity that drops a degree-one root. -/
theorem rootEstimate_corrected_expansion {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + leafCount T r + T.graph.degree r +
        ∑ v ∈ nonRootInternalVertices T r,
          T.graph.degree v * 2 ^ T.graph.dist r v := by
  rw [rootEstimate, sigma_corrected_expansion]
  omega

/-- If all degrees are positive, every non-root vertex is either a leaf or
a non-root internal vertex. -/
theorem erase_root_eq_leaf_union_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    (Finset.univ : Finset V).erase r =
      leafVertices T r ∪ nonRootInternalVertices T r := by
  ext v
  by_cases hvr : v = r
  · simp [leafVertices, nonRootInternalVertices, hvr]
  · have hv := hdeg v
    simp [leafVertices, nonRootInternalVertices, hvr]
    omega

theorem leafVertices_disjoint_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    Disjoint (leafVertices T r) (nonRootInternalVertices T r) := by
  rw [Finset.disjoint_left]
  intro v hleaf hint
  simp only [leafVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hleaf
  simp only [nonRootInternalVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hint
  omega

theorem card_erase_root_eq_leafCount_add_internal {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    ((Finset.univ : Finset V).erase r).card =
      leafCount T r + (nonRootInternalVertices T r).card := by
  rw [erase_root_eq_leaf_union_internal T r hdeg,
    Finset.card_union_of_disjoint (leafVertices_disjoint_internal T r)]
  rfl

/-- Each weighted non-root internal contribution is at least one. -/
theorem card_internal_le_weighted_sum {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    (nonRootInternalVertices T r).card ≤
      ∑ v ∈ nonRootInternalVertices T r,
        T.graph.degree v * 2 ^ T.graph.dist r v := by
  calc
    (nonRootInternalVertices T r).card =
        ∑ _v ∈ nonRootInternalVertices T r, 1 := by simp
    _ ≤ ∑ v ∈ nonRootInternalVertices T r,
        T.graph.degree v * 2 ^ T.graph.dist r v := by
      exact Finset.sum_le_sum fun v hv => by
        have hv' : v ≠ r ∧ 1 < T.graph.degree v := by
          simpa [nonRootInternalVertices] using hv
        have hprod :
            0 < T.graph.degree v * 2 ^ T.graph.dist r v := by
          exact Nat.mul_pos (by omega) (by positivity)
        omega

/-- Arithmetic form of the elementary estimator lower bound, assuming
positive degree at every vertex. -/
theorem card_add_one_le_rootEstimate_of_degree_pos
    {V : Type*} [Fintype V] (T : FiniteTree V) (r : V)
    (hdeg : ∀ v, 0 < T.graph.degree v) :
    Fintype.card V + 1 ≤ rootEstimate T r := by
  have hpart := card_erase_root_eq_leafCount_add_internal T r hdeg
  have herase :=
    Finset.card_erase_add_one (s := (Finset.univ : Finset V))
      (a := r) (Finset.mem_univ r)
  have hsum := card_internal_le_weighted_sum T r
  have hroot := hdeg r
  simp only [Finset.card_univ] at herase
  rw [rootEstimate_corrected_expansion]
  omega

/-- Elementary estimator lower bound for every root of a nontrivial finite
tree.  The root may itself have degree one. -/
theorem card_add_one_le_rootEstimate {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) (r : V) :
    Fintype.card V + 1 ≤ rootEstimate T r := by
  apply card_add_one_le_rootEstimate_of_degree_pos T r
  intro v
  exact T.isTree.connected.preconnected.degree_pos_of_nontrivial v

/-- Every rooted estimator is bounded by the tree estimator. -/
theorem rootEstimate_le_estim {V : Type*} [Fintype V]
    (T : FiniteTree V) (r : V) :
    rootEstimate T r ≤ estim T := by
  simpa [estim] using
    (Finset.le_sup (f := rootEstimate T) (Finset.mem_univ r))

/-- The tree estimator is at least one more than the vertex count for every
nontrivial finite tree. -/
theorem card_add_one_le_estim {V : Type*} [Fintype V] [Nontrivial V]
    (T : FiniteTree V) :
    Fintype.card V + 1 ≤ estim T := by
  let r : V := T.isTree.connected.nonempty.some
  exact (card_add_one_le_rootEstimate T r).trans (rootEstimate_le_estim T r)

end TreeStack

/- Source module: TreeStack.PebblingMove.lean -/
namespace TreeStack

/-- The pointwise configuration obtained by moving two pebbles from `u`
to one pebble at `v`. Legality is recorded separately by `PebbleStep`. -/
def move {V : Type*} [DecidableEq V] (C : Configuration V) (u v : V) :
    Configuration V :=
  Function.update (Function.update C u (C u - 2)) v (C v + 1)

/-- One legal pebbling move along an edge. The source contains at least two
pebbles, so the natural subtraction in `move` has its intended meaning. -/
def PebbleStep {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C D : Configuration V) : Prop :=
  ∃ u v, G.Adj u v ∧ 2 ≤ C u ∧ D = move C u v

/-- Reachability by finitely many legal pebbling moves. -/
def Reach {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C D : Configuration V) : Prop :=
  Relation.ReflTransGen (PebbleStep G) C D

/-- A positive configuration supported exactly at the specified root. -/
def StackedAt {V : Type*} (C : Configuration V) (r : V) : Prop :=
  0 < C r ∧ ∀ v, v ≠ r → C v = 0

/-- Reachability of a stack at a specified root. -/
def StackableAt {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C : Configuration V) (r : V) : Prop :=
  ∃ D, Reach G C D ∧ StackedAt D r

/-- Reachability of a stack at some vertex. -/
def Stackable {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (C : Configuration V) : Prop :=
  ∃ r, StackableAt G C r

/-- The source convention: every configuration of exactly `t` pebbles is
stackable. No "at least t" replacement is made. -/
def UniversalStackable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ C : Configuration V, mass C = t → Stackable G C

/-- A legal move lowers total mass by exactly one. -/
theorem mass_move_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (C : Configuration V) {u v : V} (huv : u ≠ v) (hu : 2 ≤ C u) :
    mass (move C u v) + 1 = mass C := by
  classical
  simp only [mass, move]
  rw [Finset.sum_update_of_mem (Finset.mem_univ v),
    Finset.sdiff_singleton_eq_erase]
  have huv_mem : u ∈ Finset.univ.erase v := by simp [huv]
  rw [Finset.sum_update_of_mem (s := Finset.univ.erase v) (i := u)
      (f := C) (b := C u - 2) huv_mem,
    Finset.sdiff_singleton_eq_erase]
  have hv := Finset.sum_erase_add Finset.univ C (Finset.mem_univ v)
  have hu' := Finset.sum_erase_add (Finset.univ.erase v) C huv_mem
  omega

/-- A stack is already stackable without making a move. -/
theorem stackableAt_of_stackedAt {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (C : Configuration V) (r : V) (h : StackedAt C r) :
    StackableAt G C r :=
  ⟨C, Relation.ReflTransGen.refl, h⟩

/-- Stackability is preserved when one legal move is prefixed. -/
theorem stackable_of_step {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {C D : Configuration V}
    (hCD : PebbleStep G C D) (hD : Stackable G D) : Stackable G C := by
  rcases hD with ⟨r, E, hDE, hE⟩
  exact ⟨r, E, Relation.ReflTransGen.head hCD hDE, hE⟩

/-- The configuration placing one pebble on every vertex of `s` and none
elsewhere. -/
def oneOn {V : Type*} [DecidableEq V] (s : Finset V) : Configuration V :=
  fun v => if v ∈ s then 1 else 0

@[simp] theorem oneOn_apply {V : Type*} [DecidableEq V] (s : Finset V) (v : V) :
    oneOn s v = if v ∈ s then 1 else 0 := rfl

@[simp] theorem mass_oneOn {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V) :
    mass (oneOn s) = s.card := by
  classical
  simp [mass, oneOn]

theorem no_step_oneOn {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s : Finset V) {D : Configuration V} : ¬ PebbleStep G (oneOn s) D := by
  rintro ⟨u, v, -, hu, -⟩
  by_cases hus : u ∈ s <;> simp [oneOn, hus] at hu

theorem not_stackable_oneOn_of_two_le_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {s : Finset V} (hs : 2 ≤ s.card) :
    ¬ Stackable G (oneOn s) := by
  rintro ⟨r, D, hreach, hstack⟩
  rcases hreach.cases_head with hEq | ⟨E, hstep, -⟩
  · subst D
    have hr : r ∈ s := by
      by_contra hnr
      have hz : oneOn s r = 0 := by simp [oneOn, hnr]
      have hpos := hstack.1
      rw [hz] at hpos
      omega
    have hsub : s ⊆ {r} := by
      intro v hv
      simp only [Finset.mem_singleton]
      by_contra hvr
      have hz := hstack.2 v hvr
      simp [oneOn, hv] at hz
    have hcard : s.card ≤ 1 := by
      simpa using (Finset.card_le_card hsub)
    have : 2 ≤ 1 := le_trans hs hcard
    omega
  · exact no_step_oneOn s hstep

/-- Audit repair for the exact-size convention: if every configuration of
exactly `t` pebbles is stackable and `t ≥ 2`, then `t` strictly exceeds
the number of vertices. -/
theorem universal_stackable_gt_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {t : ℕ} (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    Fintype.card V < t := by
  by_contra h
  have hle : t ≤ Fintype.card V := Nat.le_of_not_gt h
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (by simpa using hle)
  have hm : mass (oneOn s) = t := by simpa [hs]
  exact not_stackable_oneOn_of_two_le_card (G := G) (s := s) (by omega)
    (hU (oneOn s) hm)

/-- If the total mass exceeds the vertex count, some vertex carries at least
two pebbles. -/
theorem exists_two_le_of_card_lt_mass {V : Type*} [Fintype V]
    (C : Configuration V) (h : Fintype.card V < mass C) :
    ∃ v, 2 ≤ C v := by
  by_contra hn
  push Not at hn
  have hmass : mass C ≤ Fintype.card V := by
    rw [mass]
    calc
      (∑ v, C v) ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => by
        have hv := hn v
        omega
      _ = Fintype.card V := by simp
  omega

/-- Audit repair for exact-size universality. On a connected nontrivial finite
graph, universality at an exact size `t ≥ 2` propagates to exact size
`t + 1`. -/
theorem universal_stackable_succ {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} {t : ℕ}
    (hconn : G.Connected) (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    UniversalStackable G (t + 1) := by
  intro C hCmass
  by_cases hstack : Stackable G C
  · exact hstack
  have hcard : Fintype.card V < t := universal_stackable_gt_card hU ht
  have hmassgt : Fintype.card V < mass C := by omega
  obtain ⟨u, hu⟩ := exists_two_le_of_card_lt_mass C hmassgt
  obtain ⟨v, huv⟩ := hconn.preconnected.exists_adj_of_nontrivial u
  let D := move C u v
  have hstep : PebbleStep G C D := ⟨u, v, huv, hu, rfl⟩
  have hdrop := mass_move_add_one C huv.ne hu
  have hDmass : mass D = t := by
    dsimp [D] at hdrop ⊢
    omega
  exact stackable_of_step hstep (hU D hDmass)

end TreeStack

/- Source module: TreeStack.Transfer.lean -/
namespace TreeStack

/-- Exact integer transfer function from the branch-clearing proof. -/
def F (x : ℤ) : ℤ :=
  if x ≤ 1 then
    2 * x - 3
  else if x = 2 then
    1
  else if x = 3 then
    0
  else if x % 2 = 0 then
    x / 2
  else
    (x - 3) / 2

/-- Branch messages distinguish the empty branch from every integer message. -/
abbrev Message := Option ℤ

def EMPTY : Message := none

@[simp] theorem empty_ne_integer_zero : EMPTY ≠ some 0 := by
  simp [EMPTY]

theorem F_of_le_one {x : ℤ} (h : x ≤ 1) : F x = 2 * x - 3 := by
  simp [F, h]

@[simp] theorem F_two : F 2 = 1 := by
  norm_num [F]

@[simp] theorem F_three : F 3 = 0 := by
  norm_num [F]

theorem F_of_ge_four_even {x : ℤ} (h4 : 4 ≤ x) (he : x % 2 = 0) :
    F x = x / 2 := by
  simp [F, show ¬ x ≤ 1 by omega, show x ≠ 2 by omega,
    show x ≠ 3 by omega, he]

theorem F_of_ge_five_odd {x : ℤ} (h5 : 5 ≤ x) (ho : x % 2 ≠ 0) :
    F x = (x - 3) / 2 := by
  simp [F, show ¬ x ≤ 1 by omega, show x ≠ 2 by omega,
    show x ≠ 3 by omega, ho]

/-- Lowering an effective input by three cannot increase the transfer. -/
theorem F_sub_three_le (z : ℤ) : F (z - 3) ≤ F z := by
  unfold F
  split_ifs <;> omega

/-- The transfer is negative exactly on inputs at most one. -/
theorem F_neg_iff (z : ℤ) : F z < 0 ↔ z ≤ 1 := by
  unfold F
  split_ifs <;> omega

/-- Zero is an exceptional transfer value: it has the unique preimage three. -/
theorem F_eq_zero_iff (z : ℤ) : F z = 0 ↔ z = 3 := by
  unfold F
  split_ifs <;> omega

/-- Negative outputs are precisely the negative odd integers, with their
preimages written in the form used by the branch induction. -/
theorem F_eq_neg_odd_iff {z r : ℤ} (hr : 0 ≤ r) :
    F z = -(2 * r + 1) ↔ z = 1 - r := by
  unfold F
  split_ifs <;> omega

/-- For a nonnegative target transfer value `k`, the two generic preimages
are `2k` and `2k+3`; the first disappears at `k=0`. -/
theorem F_eq_nonneg_iff {z k : ℤ} (hk : 0 ≤ k) :
    F z = k ↔ (0 < k ∧ z = 2 * k) ∨ z = 2 * k + 3 := by
  unfold F
  split_ifs <;> omega

/-- The one-vertex signature inequality. `A` counts outward moves and is
positive; `B` counts inward moves. -/
theorem one_vertex_flux_le {y A B : ℤ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hbal : y + B - 2 * A = 0) :
    A - 2 * B ≤ F y := by
  unfold F
  split_ifs <;> omega

/-- The one-vertex flux and the maximizing transfer have the same residue
modulo three. -/
theorem one_vertex_flux_mod_three {y A B : ℤ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hbal : y + B - 2 * A = 0) :
    (A - 2 * B) % 3 = F y % 3 := by
  unfold F
  split_ifs <;> omega

/-- Equality in the one-vertex bound for effective input at most one. -/
theorem one_vertex_flux_attained_le_one {y : ℤ} (hy : y ≤ 1) :
    let A : ℤ := 1
    let B : ℤ := 2 - y
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  rw [F_of_le_one hy]
  omega

/-- Equality in the one-vertex bound for positive even effective input. -/
theorem one_vertex_flux_attained_even {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k
    let A : ℤ := k
    let B : ℤ := 0
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  have hy : 4 ≤ 2 * k ∨ k = 1 := by omega
  rcases hy with hy | rfl
  · rw [F_of_ge_four_even hy (by omega)]
    omega
  · norm_num

/-- Equality in the one-vertex bound for odd effective input at least three. -/
theorem one_vertex_flux_attained_odd {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k + 1
    let A : ℤ := k + 1
    let B : ℤ := 1
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  by_cases hk1 : k = 1
  · subst k
    norm_num
  · have hy : 5 ≤ 2 * k + 1 := by omega
    rw [F_of_ge_five_odd hy (by omega)]
    omega

end TreeStack

/- Source module: TreeStack.Branch.lean -/
namespace TreeStack

/-- An oriented branch is determined by an edge `root → parent`.
Its vertex set is the component containing `root` after deleting that edge. -/
structure OrientedBranch {V : Type*} [Fintype V] (T : FiniteTree V) where
  root : V
  parent : V
  adj : T.graph.Adj root parent

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The tree with the boundary edge of an oriented branch deleted. -/
noncomputable def deletedGraph (B : OrientedBranch T) : SimpleGraph V :=
  T.graph.deleteEdges {s(B.root, B.parent)}

/-- The connected component on the root side of the deleted boundary edge. -/
noncomputable def component (B : OrientedBranch T) :
    B.deletedGraph.ConnectedComponent :=
  B.deletedGraph.connectedComponentMk B.root

/-- The finite vertex set of the oriented branch. -/
noncomputable def vertices (B : OrientedBranch T) : Finset V := by
  classical
  exact B.component.supp.toFinset

/-- Cardinality of an oriented branch, used as the recursion measure later. -/
noncomputable def card (B : OrientedBranch T) : ℕ :=
  B.vertices.card

@[simp] theorem root_ne_parent (B : OrientedBranch T) :
    B.root ≠ B.parent :=
  B.adj.ne

@[simp] theorem root_mem_vertices (B : OrientedBranch T) :
    B.root ∈ B.vertices := by
  classical
  rw [vertices, Set.mem_toFinset]
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- In a tree, the parent endpoint is not in the root-side component after
deleting the boundary edge. -/
theorem parent_not_mem_vertices (B : OrientedBranch T) :
    B.parent ∉ B.vertices := by
  classical
  intro hp
  have hp' : B.parent ∈ B.component.supp := by
    rw [vertices, Set.mem_toFinset] at hp
    exact hp
  have hr' : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach : B.deletedGraph.Reachable B.root B.parent :=
    B.component.reachable_of_mem_supp hr' hp'
  have hbridge : T.graph.IsBridge s(B.root, B.parent) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) B.adj
  have hnot :
      ¬ (T.graph.deleteEdges {s(B.root, B.parent)}).Reachable B.root B.parent :=
    SimpleGraph.isBridge_iff.mp hbridge
  exact hnot (by simpa [deletedGraph] using hreach)

/-- Every oriented branch is nonempty. -/
theorem vertices_nonempty (B : OrientedBranch T) :
    B.vertices.Nonempty :=
  ⟨B.root, B.root_mem_vertices⟩

theorem card_pos (B : OrientedBranch T) : 0 < B.card := by
  classical
  simpa [card] using Finset.card_pos.mpr B.vertices_nonempty

/-- The branch is a proper subset of the whole finite vertex set. -/
theorem vertices_ssubset_univ (B : OrientedBranch T) :
    B.vertices ⊂ (Finset.univ : Finset V) := by
  classical
  rw [Finset.ssubset_iff_of_subset (Finset.subset_univ B.vertices)]
  exact ⟨B.parent, Finset.mem_univ _, B.parent_not_mem_vertices⟩

/-- The branch-cardinality measure is strictly smaller than the whole tree. -/
theorem card_lt_total (B : OrientedBranch T) :
    B.card < Fintype.card V := by
  classical
  simpa [card] using Finset.card_lt_card B.vertices_ssubset_univ

/-- A child choice at the root of an oriented branch. -/
structure Child (B : OrientedBranch T) where
  vertex : V
  adj : T.graph.Adj B.root vertex
  ne_parent : vertex ≠ B.parent

/-- A child choice is determined by its vertex; the remaining fields are
propositions and hence proof-irrelevant. -/
theorem Child.eq_of_vertex_eq {B : OrientedBranch T} {c d : B.Child}
    (h : c.vertex = d.vertex) : c = d := by
  cases c with
  | mk cv ca cn =>
      cases d with
      | mk dv da dn =>
          simp only at h
          subst dv
          rfl

/-- The oriented branch hanging below a chosen child. -/
def childBranch (B : OrientedBranch T) (c : B.Child) : OrientedBranch T where
  root := c.vertex
  parent := B.root
  adj := c.adj.symm

@[simp] theorem childBranch_root (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).root = c.vertex := rfl

@[simp] theorem childBranch_parent (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).parent = B.root := rfl

/-- The child edge differs from the boundary edge of its parent branch. -/
theorem childEdge_ne_boundary (B : OrientedBranch T) (c : B.Child) :
    s(B.root, c.vertex) ≠ s(B.root, B.parent) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · exact c.ne_parent h.2
  · exact B.root_ne_parent h.1

/-- Every vertex on a genuine child side also lies on the parent branch side.
The proof uses the fact that both deleted edges are bridges in the tree:
a walk in the child side cannot cross the parent's boundary edge without first
reaching the parent-branch root while avoiding the child edge. -/
theorem childBranch_vertices_subset (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊆ B.vertices := by
  classical
  intro x hx
  rw [vertices, Set.mem_toFinset] at hx ⊢
  have hc :
      c.vertex ∈ (B.childBranch c).component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreachChild :
      (B.childBranch c).deletedGraph.Reachable c.vertex x :=
    (B.childBranch c).component.reachable_of_mem_supp hc hx
  have hreachChild' :
      (T.graph.deleteEdges {s(c.vertex, B.root)}).Reachable c.vertex x := by
    simpa [deletedGraph, childBranch] using hreachChild
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreachChild' with
    ⟨p, hchildEdge⟩
  have hparentEdge : s(B.root, B.parent) ∉ p.edges := by
    intro hp
    have hrootSupp : B.root ∈ p.support :=
      p.fst_mem_support_of_mem_edges hp
    let q : T.graph.Walk c.vertex B.root := p.takeUntil B.root hrootSupp
    have hqChild : s(c.vertex, B.root) ∉ q.edges := by
      intro hq
      exact hchildEdge (p.edges_takeUntil_subset_edges hrootSupp hq)
    have hreachRoot :
        (T.graph.deleteEdges {s(c.vertex, B.root)}).Reachable c.vertex B.root :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨q, hqChild⟩
    have hbridge : T.graph.IsBridge s(c.vertex, B.root) :=
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp T.isTree.isAcyclic) c.adj.symm
    exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot
  have hreachInParent :
      B.deletedGraph.Reachable c.vertex x := by
    simpa [deletedGraph] using
      (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hparentEdge⟩)
  have hrootChild :
      B.deletedGraph.Adj B.root c.vertex := by
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨c.adj, ?_⟩
    simpa using B.childEdge_ne_boundary c
  have hrootReach : B.deletedGraph.Reachable B.root x :=
    hrootChild.reachable.trans hreachInParent
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff, component]
  exact (SimpleGraph.ConnectedComponent.sound hrootReach).symm

/-- A genuine child branch is a strict subset of its parent branch. -/
theorem childBranch_vertices_ssubset (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).vertices ⊂ B.vertices := by
  classical
  rw [Finset.ssubset_iff_of_subset (B.childBranch_vertices_subset c)]
  refine ⟨B.root, B.root_mem_vertices, ?_⟩
  simpa using (B.childBranch c).parent_not_mem_vertices

/-- Child-branch cardinality strictly decreases relative to the parent branch.
This is the recursion measure needed for branch messages. -/
theorem childBranch_card_lt (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).card < B.card := by
  classical
  simpa [card] using Finset.card_lt_card (B.childBranch_vertices_ssubset c)

/-- Any tree edge leaving an oriented branch is exactly its deleted boundary
edge.  Every other adjacent edge survives in the deleted graph and therefore
keeps both endpoints in the same connected component. -/
theorem edge_leaving_vertices_eq_boundary (B : OrientedBranch T)
    {u v : V} (hu : u ∈ B.vertices) (hv : v ∉ B.vertices)
    (huv : T.graph.Adj u v) :
    s(u, v) = s(B.root, B.parent) := by
  classical
  by_contra hne
  have hu' : u ∈ B.component.supp := by
    simpa [vertices] using hu
  have hadjDeleted : B.deletedGraph.Adj u v := by
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    exact ⟨huv, by simpa using hne⟩
  have hv' : v ∈ B.component.supp :=
    B.component.mem_supp_of_adj_mem_supp hu' hadjDeleted
  exact hv (by simpa [vertices] using hv')

/-- The external boundary vertex has no neighbor inside the branch other than
the branch root. -/
theorem eq_root_of_mem_vertices_adj_parent (B : OrientedBranch T)
    {u : V} (hu : u ∈ B.vertices) (hup : T.graph.Adj u B.parent) :
    u = B.root := by
  have hEdge :=
    B.edge_leaving_vertices_eq_boundary hu B.parent_not_mem_vertices hup
  rw [Sym2.eq_iff] at hEdge
  rcases hEdge with h | h
  · exact h.1
  · exact (B.root_ne_parent h.2.symm).elim


/-- Every non-root vertex of an oriented branch lies in one of the genuine
child branches at the branch root.  This is the existence half of the child
decomposition used by the constructive boundary induction; sibling
disjointness supplies uniqueness. -/
theorem exists_childBranch_mem_of_mem_vertices_ne_root
    (B : OrientedBranch T) {x : V}
    (hx : x ∈ B.vertices) (hxr : x ≠ B.root) :
    ∃ c : B.Child, x ∈ (B.childBranch c).vertices := by
  classical
  have hxComp : x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hrComp : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hreach : B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrComp hxComp
  rcases hreach.exists_isPath with ⟨p, hp⟩
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hxr.symm p with
    ⟨v, hrv, p', hpEq⟩
  rw [hpEq] at hp
  have hpData :=
    (SimpleGraph.Walk.cons_isPath_iff hrv p').mp hp
  have hrootNot : B.root ∉ p'.support := hpData.2
  have hrvData := hrv
  rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hrvData
  rcases hrvData with ⟨hrvT, hedge⟩
  have hvne : v ≠ B.parent := by
    intro hvp
    subst v
    simp at hedge
  let c : B.Child :=
    { vertex := v
      adj := hrvT
      ne_parent := hvne }
  have hle : B.deletedGraph ≤ T.graph := by
    intro a b hab
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hab
    exact hab.1
  let q : T.graph.Walk v x := p'.mapLe hle
  have havoid : s(v, B.root) ∉ q.edges := by
    intro he
    have he' : s(v, B.root) ∈ p'.edges := by
      simpa [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using he
    exact hrootNot (p'.snd_mem_support_of_mem_edges he')
  let q' : (T.graph.deleteEdges {s(v, B.root)}).Walk v x :=
    q.toDeleteEdges {s(v, B.root)} (by
      intro e he
      simp only [Set.mem_singleton_iff]
      intro heq
      subst e
      exact havoid he)
  have hreachChild :
      (B.childBranch c).deletedGraph.Reachable c.vertex x := by
    change (T.graph.deleteEdges {s(v, B.root)}).Reachable v x
    exact ⟨q'⟩
  refine ⟨c, ?_⟩
  rw [vertices, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff, component]
  exact (SimpleGraph.ConnectedComponent.sound hreachChild).symm

end OrientedBranch

end TreeStack

/- Source module: TreeStack.Message.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The configuration restriction to an oriented branch is nonempty exactly
when some branch vertex carries a pebble.  This is different from structural
nonemptiness: every `OrientedBranch` has at least its root as a vertex. -/
def Occupied (C : Configuration V) (B : OrientedBranch T) : Prop :=
  ∃ v ∈ B.vertices, 0 < C v

noncomputable instance (C : Configuration V) (B : OrientedBranch T) :
    Decidable (B.Occupied C) := Classical.dec _

/-- Integer contribution of a message to a parent sum.  `EMPTY` contributes
nothing to the sum, but remains categorically distinct from the integer
message zero. -/
def messageContribution : Message → ℤ
  | none => 0
  | some d => d

@[simp] theorem messageContribution_empty :
    messageContribution EMPTY = 0 := rfl

@[simp] theorem messageContribution_some (d : ℤ) :
    messageContribution (some d) = d := rfl

/-- The audited recursive branch message.  A configuration-empty branch has
the separate message `EMPTY`.  A nonempty branch applies the exact transfer
`F` to the pebbles at its root plus the contributions of every genuine
child branch.

Recursion is by strict child-branch cardinality decrease; no whole-tree bound
is used as the recursive measure. -/
noncomputable def branchMessage (C : Configuration V) (B : OrientedBranch T) :
    Message :=
  if hB : B.Occupied C then
    some <| F <|
      (C B.root : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            messageContribution
              (branchMessage C
                (B.childBranch
                  { vertex := v
                    adj := h.1
                    ne_parent := h.2 }))
          else
            0
  else
    EMPTY
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt
    { vertex := v
      adj := h.1
      ne_parent := h.2 }

/-- Sum of the recursively computed genuine-child messages, omitting
configuration-empty child branches.  Omitting an `EMPTY` contribution here
does not identify `EMPTY` with the integer zero as a message. -/
noncomputable def childMessageSum (C : Configuration V) (B : OrientedBranch T) : ℤ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      messageContribution
        (branchMessage C
          (B.childBranch
            { vertex := v
              adj := h.1
              ne_parent := h.2 }))
    else
      0

/-- Effective integer input at the root of a nonempty oriented branch. -/
noncomputable def effectiveInput (C : Configuration V) (B : OrientedBranch T) : ℤ :=
  (C B.root : ℤ) + childMessageSum C B

theorem branchMessage_eq_empty_of_not_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : ¬ B.Occupied C) :
    branchMessage C B = EMPTY := by
  rw [branchMessage]
  simp [hB]

theorem branchMessage_eq_some_of_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : B.Occupied C) :
    branchMessage C B = some (F (effectiveInput C B)) := by
  rw [branchMessage]
  simp [hB, effectiveInput, childMessageSum]

/-- Exact empty-state classification for branch messages. -/
theorem branchMessage_eq_empty_iff
    (C : Configuration V) (B : OrientedBranch T) :
    branchMessage C B = EMPTY ↔ ¬ B.Occupied C := by
  constructor
  · intro h
    by_contra hB
    have hs := branchMessage_eq_some_of_occupied C B hB
    rw [hs] at h
    simp [EMPTY] at h
  · exact branchMessage_eq_empty_of_not_occupied C B

/-- A configuration-nonempty branch always has an integer message. -/
theorem branchMessage_ne_empty_of_occupied
    (C : Configuration V) (B : OrientedBranch T) (hB : B.Occupied C) :
    branchMessage C B ≠ EMPTY := by
  rw [branchMessage_eq_some_of_occupied C B hB]
  simp [EMPTY]

end OrientedBranch

end TreeStack

/- Source module: TreeStack.Boundary.lean -/
namespace TreeStack

open scoped BigOperators Classical

/-- Oriented move counts extracted from a clearing sequence.  Positive counts
are required to lie on actual tree edges. -/
structure MoveSignature {V : Type*} [Fintype V] (T : FiniteTree V) where
  count : V → V → ℕ
  supported : ∀ {u v}, 0 < count u v → T.graph.Adj u v

namespace MoveSignature

variable {V : Type*} [Fintype V] {T : FiniteTree V}

def incoming (m : MoveSignature T) (v : V) : ℕ :=
  ∑ u, m.count u v

def outgoing (m : MoveSignature T) (v : V) : ℕ :=
  ∑ w, m.count v w

/-- Integer form of the local clearing balance
`C(v) + incoming(v) - 2*outgoing(v) = 0`. -/
def BalancesAt (m : MoveSignature T) (C : Configuration V) (v : V) : Prop :=
  (C v : ℤ) + (m.incoming v : ℤ) - 2 * (m.outgoing v : ℤ) = 0

/-- The empty move signature. -/
def zero (T : FiniteTree V) : MoveSignature T where
  count := fun _ _ => 0
  supported := by simp

/-- Extend a move signature by one actual oriented move. -/
def extend [DecidableEq V] (m : MoveSignature T) (u v : V)
    (huv : T.graph.Adj u v) : MoveSignature T where
  count := fun a b => m.count a b + if a = u ∧ b = v then 1 else 0
  supported := by
    intro a b hpos
    by_cases hnew : a = u ∧ b = v
    · rcases hnew with ⟨rfl, rfl⟩
      exact huv
    · have hm : 0 < m.count a b := by
        simpa [hnew] using hpos
      exact m.supported hm

@[simp] theorem zero_count (u v : V) :
    (zero T).count u v = 0 := rfl

@[simp] theorem incoming_zero (v : V) :
    (zero T).incoming v = 0 := by
  simp [incoming, zero]

@[simp] theorem outgoing_zero (v : V) :
    (zero T).outgoing v = 0 := by
  simp [outgoing, zero]

@[simp] theorem extend_count_same [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) :
    (m.extend u v huv).count u v = m.count u v + 1 := by
  simp [extend]

theorem incoming_extend [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) (w : V) :
    (m.extend u v huv).incoming w =
      m.incoming w + if w = v then 1 else 0 := by
  classical
  by_cases hw : w = v
  · subst w
    simp [incoming, extend, Finset.sum_add_distrib]
  · simp [incoming, extend, Finset.sum_add_distrib, hw]

theorem outgoing_extend [DecidableEq V]
    (m : MoveSignature T) {u v : V} (huv : T.graph.Adj u v) (w : V) :
    (m.extend u v huv).outgoing w =
      m.outgoing w + if w = u then 1 else 0 := by
  classical
  by_cases hw : w = u
  · subst w
    simp [outgoing, extend, Finset.sum_add_distrib]
  · simp [outgoing, extend, Finset.sum_add_distrib, hw]

end MoveSignature

section TaskScheduling

variable {α : Type*}

/-- Sum of the integer gains of a finite list of executable tasks. -/
def taskGainSum (gain : α → ℤ) : List α → ℤ
  | [] => 0
  | t :: ts => gain t + taskGainSum gain ts

/-- The recursive task sum is the ordinary sum of the mapped list. -/
theorem taskGainSum_eq_list_sum (gain : α → ℤ) :
    ∀ tasks : List α,
      taskGainSum gain tasks = (tasks.map gain).sum
  | [] => by simp [taskGainSum]
  | t :: ts => by
      simp [taskGainSum, taskGainSum_eq_list_sum gain ts]

/-- The list sum agrees with the corresponding finite-set sum. -/
theorem taskGainSum_toList [DecidableEq α]
    (gain : α → ℤ) (s : Finset α) :
    taskGainSum gain s.toList = Finset.sum s gain := by
  rw [taskGainSum_eq_list_sum]
  exact Finset.sum_map_toList s gain

/-- A task order is safe from an initial pile `a` if every successive task
leaves a strictly positive pile.  This is exactly the precondition needed to
apply the occupied-child boundary invariant task by task. -/
def TaskScheduleSafe (gain : α → ℤ) : ℤ → List α → Prop
  | _, [] => True
  | a, t :: ts =>
      0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts

def positiveTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => 0 < gain t

def zeroTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => gain t = 0

def negativeTasks (gain : α → ℤ) (tasks : List α) : List α :=
  tasks.filter fun t => gain t < 0

/-- Audited scheduling order: positive gains first, then zero gains, then
negative gains.  Empty branches are not represented by tasks at all. -/
def orderedTasks (gain : α → ℤ) (tasks : List α) : List α :=
  positiveTasks gain tasks ++
    (zeroTasks gain tasks ++ negativeTasks gain tasks)

theorem taskGainSum_append (gain : α → ℤ) (xs ys : List α) :
    taskGainSum gain (xs ++ ys) =
      taskGainSum gain xs + taskGainSum gain ys := by
  induction xs with
  | nil => simp [taskGainSum]
  | cons x xs ih =>
      simp [taskGainSum, ih]
      ring

theorem taskScheduleSafe_append (gain : α → ℤ) (a : ℤ)
    (xs ys : List α) :
    TaskScheduleSafe gain a (xs ++ ys) ↔
      TaskScheduleSafe gain a xs ∧
        TaskScheduleSafe gain (a + taskGainSum gain xs) ys := by
  induction xs generalizing a with
  | nil => simp [TaskScheduleSafe, taskGainSum]
  | cons x xs ih =>
      simp [TaskScheduleSafe, taskGainSum, ih, add_assoc, and_assoc]

theorem taskGainSum_nonpos (gain : α → ℤ) :
    ∀ tasks : List α,
      (∀ t ∈ tasks, gain t ≤ 0) →
      taskGainSum gain tasks ≤ 0
  | [], _ => by simp [taskGainSum]
  | t :: ts, h => by
      have ht : gain t ≤ 0 := h t (by simp)
      have hts : ∀ u ∈ ts, gain u ≤ 0 := by
        intro u hu
        exact h u (by simp [hu])
      have ih := taskGainSum_nonpos gain ts hts
      simp only [taskGainSum]
      linarith

theorem taskScheduleSafe_of_all_pos (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 ≤ a →
      (∀ t ∈ tasks, 0 < gain t) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, ha, hpos => by
      have ht : 0 < gain t := hpos t (by simp)
      have hts : ∀ u ∈ ts, 0 < gain u := by
        intro u hu
        exact hpos u (by simp [hu])
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      constructor
      · linarith
      · exact taskScheduleSafe_of_all_pos gain (by linarith) hts

theorem taskScheduleSafe_of_all_zero (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a →
      (∀ t ∈ tasks, gain t = 0) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, ha, hzero => by
      have ht : gain t = 0 := hzero t (by simp)
      have hts : ∀ u ∈ ts, gain u = 0 := by
        intro u hu
        exact hzero u (by simp [hu])
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      constructor
      · simpa [ht] using ha
      · simpa [ht] using
          (taskScheduleSafe_of_all_zero gain ha hts)

theorem taskScheduleSafe_of_all_nonpos_of_final_pos
    (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a + taskGainSum gain tasks →
      (∀ t ∈ tasks, gain t ≤ 0) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, hfinal, hnonpos => by
      have ht : gain t ≤ 0 := hnonpos t (by simp)
      have hts : ∀ u ∈ ts, gain u ≤ 0 := by
        intro u hu
        exact hnonpos u (by simp [hu])
      have htail := taskGainSum_nonpos gain ts hts
      have hfirst : 0 < a + gain t := by
        simp only [taskGainSum] at hfinal
        linarith
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      refine ⟨hfirst, ?_⟩
      apply taskScheduleSafe_of_all_nonpos_of_final_pos gain
      · simp only [taskGainSum] at hfinal
        linarith
      · exact hts

/-- Positive, zero, and negative filtering preserves the total task gain. -/
theorem taskGainSum_partition (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (positiveTasks gain tasks) +
        taskGainSum gain (zeroTasks gain tasks) +
        taskGainSum gain (negativeTasks gain tasks) =
      taskGainSum gain tasks := by
  induction tasks with
  | nil =>
      simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks]
  | cons t ts ih =>
      by_cases hp : 0 < gain t
      · have hz : gain t ≠ 0 := by linarith
        have hn : ¬ gain t < 0 := by linarith
        have ih' := ih
        simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
        simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
          hp, hz, hn]
        linarith
      · by_cases hz : gain t = 0
        · have hn : ¬ gain t < 0 := by linarith
          have ih' := ih
          simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
          simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
            hp, hz, hn]
          exact ih'
        · have hn : gain t < 0 := by omega
          have ih' := ih
          simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
          simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
            hp, hz, hn]
          linarith

theorem taskGainSum_orderedTasks (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (orderedTasks gain tasks) =
      taskGainSum gain tasks := by
  rw [orderedTasks, taskGainSum_append, taskGainSum_append]
  linarith [taskGainSum_partition gain tasks]

theorem mem_orderedTasks_iff (gain : α → ℤ) (tasks : List α) (t : α) :
    t ∈ orderedTasks gain tasks ↔ t ∈ tasks := by
  constructor
  · intro ht
    simp only [orderedTasks, List.mem_append] at ht
    rcases ht with ht | ht
    · have hpos : t ∈ tasks ∧ 0 < gain t := by
        simpa [positiveTasks] using ht
      exact hpos.1
    · rcases ht with ht | ht
      · have hzero : t ∈ tasks ∧ gain t = 0 := by
          simpa [zeroTasks] using ht
        exact hzero.1
      · have hneg : t ∈ tasks ∧ gain t < 0 := by
          simpa [negativeTasks] using ht
        exact hneg.1
  · intro ht
    by_cases hp : 0 < gain t
    · have : t ∈ positiveTasks gain tasks := by
        simpa [positiveTasks, ht, hp]
      exact by
        simp only [orderedTasks, List.mem_append]
        exact Or.inl this
    · by_cases hz : gain t = 0
      · have : t ∈ zeroTasks gain tasks := by
          simpa [zeroTasks, ht, hz]
        exact by
          simp only [orderedTasks, List.mem_append]
          exact Or.inr (Or.inl this)
      · have hn : gain t < 0 := by omega
        have : t ∈ negativeTasks gain tasks := by
          simpa [negativeTasks, ht, hn]
        exact by
          simp only [orderedTasks, List.mem_append]
          exact Or.inr (Or.inr this)

theorem orderedTasks_nodup (gain : α → ℤ) {tasks : List α}
    (h : tasks.Nodup) :
    (orderedTasks gain tasks).Nodup := by
  rw [orderedTasks]
  have hp := h.filter (fun t => 0 < gain t)
  have hz := h.filter (fun t => gain t = 0)
  have hn := h.filter (fun t => gain t < 0)
  rw [List.nodup_append]
  constructor
  · exact hp
  · constructor
    · rw [List.nodup_append]
      exact ⟨hz, hn, by
        intro a ha b hb hab
        subst b
        have hZeroData : a ∈ tasks ∧ gain a = 0 := by
          simpa [zeroTasks] using ha
        have hNegData : a ∈ tasks ∧ gain a < 0 := by
          simpa [negativeTasks] using hb
        have hZero : gain a = 0 := hZeroData.2
        have hNeg : gain a < 0 := hNegData.2
        omega⟩
    · intro a ha b hb hab
      subst b
      have hPosData : a ∈ tasks ∧ 0 < gain a := by
        simpa [positiveTasks] using ha
      have hPos : 0 < gain a := hPosData.2
      simp only [List.mem_append] at hb
      rcases hb with hZeroMem | hNegMem
      · have hZeroData : a ∈ tasks ∧ gain a = 0 := by
          simpa [zeroTasks] using hZeroMem
        have hZero : gain a = 0 := hZeroData.2
        omega
      · have hNegData : a ∈ tasks ∧ gain a < 0 := by
          simpa [negativeTasks] using hNegMem
        have hNeg : gain a < 0 := hNegData.2
        omega

/-- Positive/zero/negative scheduling lemma from the audited construction.
If the starting pile is nonnegative and the final total is positive, placing
positive tasks first, zero tasks next, and negative tasks last makes every
individual task executable. -/
theorem orderedTasks_safe (gain : α → ℤ) (tasks : List α) (a : ℤ)
    (ha : 0 ≤ a)
    (hfinal : 0 < a + taskGainSum gain tasks) :
    TaskScheduleSafe gain a (orderedTasks gain tasks) := by
  let ps := positiveTasks gain tasks
  let zs := zeroTasks gain tasks
  let ns := negativeTasks gain tasks
  have hpos : ∀ t ∈ ps, 0 < gain t := by
    intro t ht
    have ht' : t ∈ tasks ∧ 0 < gain t := by
      simpa [ps, positiveTasks] using ht
    exact ht'.2
  have hnonpos : ∀ t ∈ zs ++ ns, gain t ≤ 0 := by
    intro t ht
    have ht' :
        (t ∈ tasks ∧ gain t = 0) ∨
          (t ∈ tasks ∧ gain t < 0) := by
      simpa [zs, ns, zeroTasks, negativeTasks] using ht
    rcases ht' with ht' | ht' <;> linarith [ht'.2]
  have hsafePos :
      TaskScheduleSafe gain a ps :=
    taskScheduleSafe_of_all_pos gain ha hpos
  have horderedFinal :
      0 < a + taskGainSum gain (orderedTasks gain tasks) := by
    rw [taskGainSum_orderedTasks]
    exact hfinal
  have hrestFinal :
      0 < (a + taskGainSum gain ps) +
        taskGainSum gain (zs ++ ns) := by
    rw [orderedTasks, taskGainSum_append] at horderedFinal
    change
      0 < (a + taskGainSum gain ps) +
        taskGainSum gain (zs ++ ns)
    simpa [ps, zs, ns, add_assoc] using horderedFinal
  have hsafeRest :
      TaskScheduleSafe gain
        (a + taskGainSum gain ps) (zs ++ ns) :=
    taskScheduleSafe_of_all_nonpos_of_final_pos gain
      hrestFinal hnonpos
  rw [orderedTasks, taskScheduleSafe_append]
  simpa [ps, zs, ns] using And.intro hsafePos hsafeRest

end TaskScheduling

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Vertices on which a branch-local clearing sequence is allowed to move:
the branch itself together with its external boundary vertex. -/
noncomputable def carrier (B : OrientedBranch T) : Finset V :=
  insert B.parent B.vertices

@[simp] theorem root_mem_carrier (B : OrientedBranch T) :
    B.root ∈ B.carrier := by
  classical
  simp [carrier, B.root_mem_vertices]

@[simp] theorem parent_mem_carrier (B : OrientedBranch T) :
    B.parent ∈ B.carrier := by
  classical
  simp [carrier]

@[simp] theorem carrier_erase_parent [DecidableEq V] (B : OrientedBranch T) :
    B.carrier.erase B.parent = B.vertices := by
  ext v
  constructor
  · intro hv
    have hv' : v ≠ B.parent ∧ v ∈ B.carrier := by
      simpa using hv
    have hcases : v = B.parent ∨ v ∈ B.vertices := by
      simpa [carrier] using hv'.2
    exact hcases.resolve_left hv'.1
  · intro hv
    have hne : v ≠ B.parent := by
      intro h
      subst v
      exact B.parent_not_mem_vertices hv
    simp [carrier, hv, hne]

/-- A move signature uses no vertex outside the branch plus its boundary
vertex. -/
def MoveSignature.SupportedOn (m : MoveSignature T) (B : OrientedBranch T) : Prop :=
  ∀ ⦃u v⦄, 0 < m.count u v → u ∈ B.carrier ∧ v ∈ B.carrier

/-- Static balance condition imposed by clearing every branch vertex. -/
def MoveSignature.Clears (m : MoveSignature T)
    (C : Configuration V) (B : OrientedBranch T) : Prop :=
  ∀ v ∈ B.vertices, m.BalancesAt C v

/-- Net change at the external boundary contributed by crossing the unique
boundary edge. -/
def MoveSignature.boundaryFlux (m : MoveSignature T)
    (B : OrientedBranch T) : ℤ :=
  (m.count B.root B.parent : ℤ) -
    2 * (m.count B.parent B.root : ℤ)

/-- The causal condition required for a nonempty branch clearing: at least one
outward crossing of the unique boundary edge occurs. -/
def MoveSignature.CausalOutward (m : MoveSignature T)
    (B : OrientedBranch T) : Prop :=
  0 < m.count B.root B.parent

/-- Signature-level data used by the upper-bound induction for a nonempty
branch.  This deliberately includes causal outward crossing; balance equations
alone permit phantom unschedulable solutions at nonpositive effective input. -/
def MoveSignature.FeasibleClearing (m : MoveSignature T)
    (C : Configuration V) (B : OrientedBranch T) : Prop :=
  MoveSignature.SupportedOn m B ∧
    MoveSignature.Clears m C B ∧
    MoveSignature.CausalOutward m B

/-- Signature-level balance for an initially and finally empty branch.
Unlike `FeasibleClearing`, no causal outward condition is imposed; these
signatures model optional empty-branch excursions. -/
def MoveSignature.EmptyExcursion (m : MoveSignature T)
    (B : OrientedBranch T) : Prop :=
  MoveSignature.SupportedOn m B ∧
    ∀ v ∈ B.vertices,
      (m.incoming v : ℤ) - 2 * (m.outgoing v : ℤ) = 0

theorem occupied_congr_vertices
    (B : OrientedBranch T) (C D : Configuration V)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    B.Occupied C ↔ B.Occupied D := by
  constructor
  · rintro ⟨v, hv, hpos⟩
    refine ⟨v, hv, ?_⟩
    rw [← hCD v hv]
    exact hpos
  · rintro ⟨v, hv, hpos⟩
    refine ⟨v, hv, ?_⟩
    rw [hCD v hv]
    exact hpos

/-- Recursive branch messages are insensitive to configuration values outside
the branch.  In particular, changing a child's external boundary pile does not
change that child's message. -/
theorem branchMessage_congr_vertices
    (C D : Configuration V) (B : OrientedBranch T)
    (hCD : ∀ v ∈ B.vertices, C v = D v) :
    branchMessage C B = branchMessage D B := by
  have hOcc := B.occupied_congr_vertices C D hCD
  by_cases hC : B.Occupied C
  · have hD : B.Occupied D := hOcc.mp hC
    have hRoot : (C B.root : ℤ) = (D B.root : ℤ) := by
      exact_mod_cast hCD B.root B.root_mem_vertices
    have hChild :
        childMessageSum C B = childMessageSum D B := by
      rw [childMessageSum, childMessageSum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hSub :
            ∀ w ∈ (B.childBranch c).vertices, C w = D w := by
          intro w hw
          exact hCD w (B.childBranch_vertices_subset c hw)
        have hRec :=
          branchMessage_congr_vertices C D (B.childBranch c) hSub
        simp [h, c, hRec]
      · simp [h]
    rw [branchMessage_eq_some_of_occupied C B hC,
      branchMessage_eq_some_of_occupied D B hD]
    congr 2
    rw [effectiveInput, effectiveInput, hRoot, hChild]
  · have hD : ¬ B.Occupied D := by
      intro hD
      exact hC (hOcc.mpr hD)
    rw [branchMessage_eq_empty_of_not_occupied C B hC,
      branchMessage_eq_empty_of_not_occupied D B hD]
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c

/-- A genuine child carrier lies entirely inside the parent branch carrier. -/
theorem childBranch_carrier_subset
    (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).carrier ⊆ B.carrier := by
  classical
  intro v hv
  have hvCases :
      v = (B.childBranch c).parent ∨
        v ∈ (B.childBranch c).vertices := by
    simpa [carrier] using hv
  rcases hvCases with hp | hvChild
  · subst v
    simpa [childBranch] using B.root_mem_carrier
  · have hvB := B.childBranch_vertices_subset c hvChild
    rw [carrier]
    exact Finset.mem_insert.mpr (Or.inr hvB)

/-- The external parent of a branch is outside every genuine child carrier. -/
theorem parent_not_mem_childBranch_carrier
    (B : OrientedBranch T) (c : B.Child) :
    B.parent ∉ (B.childBranch c).carrier := by
  classical
  intro hp
  have hpCases :
      B.parent = B.root ∨
        B.parent ∈ (B.childBranch c).vertices := by
    simpa [carrier, childBranch] using hp
  rcases hpCases with hroot | hpChild
  · exact B.root_ne_parent hroot.symm
  · exact B.parent_not_mem_vertices
      (B.childBranch_vertices_subset c hpChild)

/-- Distinct genuine child branches of the same oriented branch have disjoint
vertex sets.  A common vertex would give a path in one child component that
crosses the other's unique boundary edge and hence reaches the deleted parent
edge endpoint, contradicting the bridge separation. -/
theorem childBranch_vertices_disjoint
    (B : OrientedBranch T) (c d : B.Child)
    (hcd : c.vertex ≠ d.vertex) :
    Disjoint (B.childBranch c).vertices (B.childBranch d).vertices := by
  classical
  rw [Finset.disjoint_left]
  intro x hxc hxd
  have hdOutside : d.vertex ∉ (B.childBranch c).vertices := by
    intro hd
    have heq :=
      (B.childBranch c).eq_root_of_mem_vertices_adj_parent
        hd d.adj.symm
    exact hcd heq.symm
  have hdComp :
      d.vertex ∈ (B.childBranch d).component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hxComp :
      x ∈ (B.childBranch d).component.supp := by
    simpa [vertices] using hxd
  have hreach :
      (B.childBranch d).deletedGraph.Reachable d.vertex x :=
    (B.childBranch d).component.reachable_of_mem_supp hdComp hxComp
  have hreach' :
      (T.graph.deleteEdges {s(d.vertex, B.root)}).Reachable d.vertex x := by
    simpa [deletedGraph, childBranch] using hreach
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach' with
    ⟨p, havoidD⟩
  have hxcSet :
      x ∈ ((B.childBranch c).vertices : Set V) := by
    simpa using hxc
  have hdOutsideSet :
      d.vertex ∉ ((B.childBranch c).vertices : Set V) := by
    simpa using hdOutside
  rcases p.reverse.exists_boundary_dart
      ((B.childBranch c).vertices : Set V)
      hxcSet hdOutsideSet with
    ⟨⟨⟨u, v⟩, huv⟩, hdart, huSet, hvSet⟩
  have huFin : u ∈ (B.childBranch c).vertices := by
    simpa using huSet
  have hvFin : v ∉ (B.childBranch c).vertices := by
    simpa using hvSet
  have hedge :=
    (B.childBranch c).edge_leaving_vertices_eq_boundary
      huFin hvFin huv
  have hvRoot : v = B.root := by
    rw [Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · simpa [childBranch] using h.2
    · have huParent : u = (B.childBranch c).parent := h.1
      subst u
      exact ((B.childBranch c).parent_not_mem_vertices huFin).elim
  have hrootRev : B.root ∈ p.reverse.support := by
    rw [← hvRoot]
    exact p.reverse.dart_snd_mem_support_of_mem_darts hdart
  have hroot : B.root ∈ p.support := by
    simpa using hrootRev
  let q : T.graph.Walk d.vertex B.root :=
    p.takeUntil B.root hroot
  have hqAvoid : s(d.vertex, B.root) ∉ q.edges := by
    intro hq
    exact havoidD (p.edges_takeUntil_subset_edges hroot hq)
  have hreachRoot :
      (T.graph.deleteEdges {s(d.vertex, B.root)}).Reachable
        d.vertex B.root :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨q, hqAvoid⟩
  have hbridge : T.graph.IsBridge s(d.vertex, B.root) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) d.adj.symm
  exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot


/-- A vertex in one child branch is outside the full carrier of every
distinct sibling.  The only extra carrier vertex of a child is the common
parent root, which lies in no child vertex set. -/
theorem mem_childBranch_vertices_not_mem_sibling_carrier
    (B : OrientedBranch T) (c d : B.Child)
    (hcd : c.vertex ≠ d.vertex) {w : V}
    (hw : w ∈ (B.childBranch c).vertices) :
    w ∉ (B.childBranch d).carrier := by
  classical
  intro hwCarrier
  have hwCases :
      w = B.root ∨ w ∈ (B.childBranch d).vertices := by
    simpa [carrier, childBranch] using hwCarrier
  rcases hwCases with hroot | hwd
  · subst w
    exact (B.childBranch c).parent_not_mem_vertices hw
  · exact
      (Finset.disjoint_left.mp
        (B.childBranch_vertices_disjoint c d hcd)) hw hwd

section LegalSequences

variable [DecidableEq V]

/-- A legal pebbling move whose endpoints stay inside the branch carrier.
No move elsewhere in the tree is allowed. -/
def BranchPebbleStep (B : OrientedBranch T)
    (C D : Configuration V) : Prop :=
  ∃ u v,
    T.graph.Adj u v ∧
    2 ≤ C u ∧
    u ∈ B.carrier ∧
    v ∈ B.carrier ∧
    D = move C u v

/-- Reachability using only legal branch-carrier moves. -/
def BranchReach (B : OrientedBranch T)
    (C D : Configuration V) : Prop :=
  Relation.ReflTransGen B.BranchPebbleStep C D

/-- A branch-local legal sequence cannot alter a vertex outside its carrier. -/
theorem BranchReach.eq_of_not_mem_carrier
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) {w : V}
    (hw : w ∉ B.carrier) :
    D w = C w := by
  induction hreach with
  | refl => rfl
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, hu, hv, rfl⟩
      have hwu : w ≠ u := by
        intro h
        subst w
        exact hw hu
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw hv
      simp [move, hwu, hwv, ih]

/-- A legal sequence inside a genuine child carrier is also a legal sequence
inside the parent branch carrier. -/
theorem BranchReach.of_child
    (B : OrientedBranch T) (c : B.Child)
    {C D : Configuration V}
    (hreach : (B.childBranch c).BranchReach C D) :
    B.BranchReach C D := by
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hED with ⟨u, v, huv, hlegal, hu, hv, rfl⟩
      exact
        ⟨u, v, huv, hlegal,
          B.childBranch_carrier_subset c hu,
          B.childBranch_carrier_subset c hv, rfl⟩

/-- Repeating one legal oriented edge move a prescribed number of times
gives exact endpoint counts and leaves every other vertex unchanged. -/
theorem BranchReach.repeat_move
    (B : OrientedBranch T) {u v : V}
    (huv : T.graph.Adj u v)
    (huCarrier : u ∈ B.carrier) (hvCarrier : v ∈ B.carrier) :
    ∀ (C : Configuration V) (n : ℕ),
      2 * n ≤ C u →
      ∃ D : Configuration V,
        B.BranchReach C D ∧
        D u = C u - 2 * n ∧
        D v = C v + n ∧
        (∀ w : V, w ≠ u → w ≠ v → D w = C w) := by
  classical
  intro C n
  induction n generalizing C with
  | zero =>
      intro h
      refine ⟨C, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro w hwu hwv
        rfl
  | succ n ih =>
      intro hTotal
      have hLegal : 2 ≤ C u := by omega
      let E : Configuration V := move C u v
      have hStep : B.BranchPebbleStep C E :=
        ⟨u, v, huv, hLegal, huCarrier, hvCarrier, rfl⟩
      have hReachStep : B.BranchReach C E :=
        Relation.ReflTransGen.single hStep
      have hEu : E u = C u - 2 := by
        simp [E, move, huv.ne]
      have hEv : E v = C v + 1 := by
        simp [E, move, huv.ne]
      have hRemain : 2 * n ≤ E u := by
        rw [hEu]
        omega
      rcases ih E hRemain with ⟨D, hReachRest, hDu, hDv, hOther⟩
      have hReach : B.BranchReach C D :=
        Relation.ReflTransGen.trans hReachStep hReachRest
      refine ⟨D, hReach, ?_, ?_, ?_⟩
      · rw [hDu, hEu]
        omega
      · rw [hDv, hEv]
        omega
      · intro w hwu hwv
        rw [hOther w hwu hwv]
        simp [E, move, hwu, hwv]

/-- All vertices of the branch have been cleared. -/
def Cleared (B : OrientedBranch T) (D : Configuration V) : Prop :=
  ∀ v ∈ B.vertices, D v = 0

/-- Replace the initial number of pebbles at the external boundary vertex by
`q`; branch messages themselves never inspect this boundary value. -/
def withBoundary (B : OrientedBranch T) (C : Configuration V) (q : ℕ) :
    Configuration V :=
  Function.update C B.parent q

@[simp] theorem withBoundary_parent (B : OrientedBranch T)
    (C : Configuration V) (q : ℕ) :
    B.withBoundary C q B.parent = q := by
  simp [withBoundary]

@[simp] theorem withBoundary_self (B : OrientedBranch T)
    (C : Configuration V) :
    B.withBoundary C (C B.parent) = C := by
  funext v
  by_cases h : v = B.parent <;> simp [withBoundary, h]

@[simp] theorem withBoundary_of_mem_vertices (B : OrientedBranch T)
    (C : Configuration V) (q : ℕ) {v : V} (hv : v ∈ B.vertices) :
    B.withBoundary C q v = C v := by
  have hne : v ≠ B.parent := by
    intro h
    subst v
    exact B.parent_not_mem_vertices hv
  simp [withBoundary, hne]

theorem occupied_withBoundary_iff (B : OrientedBranch T)
    (C : Configuration V) (q : ℕ) :
    B.Occupied (B.withBoundary C q) ↔ B.Occupied C := by
  constructor
  · rintro ⟨v, hv, hpos⟩
    exact ⟨v, hv, by simpa [B.withBoundary_of_mem_vertices C q hv] using hpos⟩
  · rintro ⟨v, hv, hpos⟩
    exact ⟨v, hv, by simpa [B.withBoundary_of_mem_vertices C q hv] using hpos⟩

/-- Predicate saying that a vertex indexes a genuine child branch. -/
def IsChildVertex (B : OrientedBranch T) (v : V) : Prop :=
  T.graph.Adj B.root v ∧ v ≠ B.parent

/-- The genuine child branch indexed by a vertex satisfying the child predicate. -/
def childOfVertex (B : OrientedBranch T) (v : V)
    (h : B.IsChildVertex v) : B.Child where
  vertex := v
  adj := h.1
  ne_parent := h.2

/-- Predicate for vertices indexing occupied genuine children. -/
def IsOccupiedChildVertex
    (B : OrientedBranch T) (C : Configuration V) (v : V) : Prop :=
  ∃ h : B.IsChildVertex v,
    (B.childBranch (B.childOfVertex v h)).Occupied C

/-- An executable child task is a genuine child branch that is occupied in
the original configuration. Empty child branches are absent from this type,
rather than represented by zero-gain tasks. -/
def OccupiedChild (B : OrientedBranch T) (C : Configuration V) :=
  {v : V // B.IsOccupiedChildVertex C v}

noncomputable instance OccupiedChild.instFintype
    (B : OrientedBranch T) (C : Configuration V) :
    Fintype (B.OccupiedChild C) :=
  Fintype.ofInjective
    (fun t : B.OccupiedChild C => (t.1 : V))
    Subtype.val_injective

/-- The genuine child carried by an occupied-child task. -/
noncomputable def OccupiedChild.child
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) : B.Child :=
  B.childOfVertex t.1 (Classical.choose t.2)

/-- The child represented by an occupied-child task is occupied. -/
theorem OccupiedChild.occupied
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    (B.childBranch t.child).Occupied C := by
  exact Classical.choose_spec t.2

@[simp] theorem OccupiedChild.child_vertex
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.child.vertex = t.1 := rfl

/-- The summand appearing in childMessageSum at a vertex. -/
noncomputable def childMessageTerm
    (B : OrientedBranch T) (C : Configuration V) (v : V) : ℤ :=
  if h : B.IsChildVertex v then
    messageContribution
      (branchMessage C (B.childBranch (B.childOfVertex v h)))
  else
    0

theorem childMessageSum_eq_sum_term
    (B : OrientedBranch T) (C : Configuration V) :
    childMessageSum C B = ∑ v : V, B.childMessageTerm C v := by
  rw [childMessageSum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
  · simp [childMessageTerm, IsChildVertex, childOfVertex, h]
  · simp [childMessageTerm, IsChildVertex, h]

theorem childMessageTerm_eq_zero_of_not_occupiedChild
    (B : OrientedBranch T) (C : Configuration V) {v : V}
    (hv : ¬ B.IsOccupiedChildVertex C v) :
    B.childMessageTerm C v = 0 := by
  by_cases h : B.IsChildVertex v
  · have hnot :
        ¬ (B.childBranch (B.childOfVertex v h)).Occupied C := by
      intro hocc
      exact hv ⟨h, hocc⟩
    simp [childMessageTerm, h,
      branchMessage_eq_empty_of_not_occupied C
        (B.childBranch (B.childOfVertex v h)) hnot]
  · simp [childMessageTerm, h]

/-- Recursive integer gain attached to an occupied child task. -/
noncomputable def OccupiedChild.gain
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) : ℤ :=
  messageContribution (branchMessage C (B.childBranch t.child))

theorem OccupiedChild.gain_eq_F
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.gain = F (effectiveInput C (B.childBranch t.child)) := by
  rw [OccupiedChild.gain,
    branchMessage_eq_some_of_occupied C (B.childBranch t.child) t.occupied]
  rfl

theorem OccupiedChild.gain_eq_term
    {B : OrientedBranch T} {C : Configuration V}
    (t : B.OccupiedChild C) :
    t.gain = B.childMessageTerm C t.1 := by
  have h : B.IsChildVertex t.1 := Classical.choose t.2
  simp [OccupiedChild.gain, OccupiedChild.child,
    childMessageTerm, h]

/-- The unscheduled child-task list contains every occupied genuine child once
and contains no empty branch. -/
noncomputable def occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V) :
    List (B.OccupiedChild C) := by
  classical
  exact (Finset.univ : Finset (B.OccupiedChild C)).toList

theorem occupiedChildTasks_nodup
    (B : OrientedBranch T) (C : Configuration V) :
    (B.occupiedChildTasks C).Nodup := by
  classical
  exact Finset.nodup_toList (Finset.univ : Finset (B.OccupiedChild C))

@[simp] theorem mem_occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V)
    (t : B.OccupiedChild C) :
    t ∈ B.occupiedChildTasks C := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

/-- The occupied executable tasks carry exactly the recursive child-message
sum. Empty genuine children contribute zero to childMessageSum but are absent
from the task list. -/
theorem taskGainSum_occupiedChildTasks
    (B : OrientedBranch T) (C : Configuration V) :
    taskGainSum
        (fun t : B.OccupiedChild C => t.gain)
        (B.occupiedChildTasks C) =
      childMessageSum C B := by
  classical
  calc
    taskGainSum
        (fun t : B.OccupiedChild C => t.gain)
        (B.occupiedChildTasks C) =
        ∑ t : B.OccupiedChild C, t.gain := by
          rw [occupiedChildTasks, taskGainSum_toList]
    _ = ∑ t : B.OccupiedChild C,
          B.childMessageTerm C t.1 := by
          apply Finset.sum_congr rfl
          intro t _
          exact t.gain_eq_term
    _ = ∑ v ∈
          (Finset.univ.filter fun v : V =>
            B.IsOccupiedChildVertex C v),
          B.childMessageTerm C v := by
          symm
          simpa [OccupiedChild] using
            (Finset.sum_subtype
              (Finset.univ.filter fun v : V =>
                B.IsOccupiedChildVertex C v)
              (fun v => by simp)
              (fun v => B.childMessageTerm C v))
    _ = ∑ v : V, B.childMessageTerm C v := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro v hvUniv hvNot
          have hvNotOcc : ¬ B.IsOccupiedChildVertex C v := by
            intro hvOcc
            exact hvNot (Finset.mem_filter.mpr ⟨hvUniv, hvOcc⟩)
          exact B.childMessageTerm_eq_zero_of_not_occupiedChild C hvNotOcc
    _ = childMessageSum C B := (B.childMessageSum_eq_sum_term C).symm

/-- A final configuration obtained by a legal branch-local sequence which
clears the entire branch. -/
def ClearOutcome (B : OrientedBranch T) (C : Configuration V)
    (q : ℕ) (D : Configuration V) : Prop :=
  B.BranchReach (B.withBoundary C q) D ∧ B.Cleared D

/-- Execute a safe list of occupied child tasks by recursively attaining each
child's exact boundary gain.  The theorem records the parent-root gain,
preservation of the external boundary, clearing of every scheduled child, and
pointwise preservation of every sibling omitted from the list. -/
theorem executeOccupiedTaskSchedule
    (B : OrientedBranch T) (C : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E →
        branchMessage E (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E q D ∧
            (D B.root : ℤ) = (q : ℤ) + d) :
    ∀ (tasks : List (B.OccupiedChild C)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ (B.childBranch t.child).vertices,
        E v = C v) →
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ) tasks →
      ∃ D : Configuration V,
        B.BranchReach E D ∧
        (D B.root : ℤ) =
          (E B.root : ℤ) +
            taskGainSum
              (fun t : B.OccupiedChild C => t.gain) tasks ∧
        D B.parent = E B.parent ∧
        (∀ t ∈ tasks, (B.childBranch t.child).Cleared D) ∧
        (∀ c : B.Child,
          (∀ t ∈ tasks, t.1 ≠ c.vertex) →
          ∀ v ∈ (B.childBranch c).vertices, D v = E v) := by
  classical
  intro tasks
  induction tasks with
  | nil =>
      intro E hNodup hSame hSafe
      refine ⟨E, Relation.ReflTransGen.refl, ?_, rfl, ?_, ?_⟩
      · simp [taskGainSum]
      · intro t ht
        simp at ht
      · intro c hnot v hv
        rfl
  | cons t ts ih =>
      intro E hNodup hSame hSafe
      have hNodupData := List.nodup_cons.mp hNodup
      have htNot : t ∉ ts := hNodupData.1
      have hNodupTail : ts.Nodup := hNodupData.2
      change
        0 < (E B.root : ℤ) + t.gain ∧
          TaskScheduleSafe
            (fun s : B.OccupiedChild C => s.gain)
            ((E B.root : ℤ) + t.gain) ts at hSafe
      have hSameHead :
          ∀ v ∈ (B.childBranch t.child).vertices, E v = C v :=
        hSame t (by simp)
      have hCE :
          ∀ v ∈ (B.childBranch t.child).vertices, C v = E v := by
        intro v hv
        exact (hSameHead v hv).symm
      have hOccE :
          (B.childBranch t.child).Occupied E :=
        ((B.childBranch t.child).occupied_congr_vertices C E hCE).mp
          t.occupied
      have hMsgC :
          branchMessage C (B.childBranch t.child) = some t.gain := by
        rw [branchMessage_eq_some_of_occupied C
          (B.childBranch t.child) t.occupied, t.gain_eq_F]
      have hMsgE :
          branchMessage E (B.childBranch t.child) = some t.gain := by
        calc
          branchMessage E (B.childBranch t.child) =
              branchMessage C (B.childBranch t.child) :=
            (branchMessage_congr_vertices C E
              (B.childBranch t.child) hCE).symm
          _ = some t.gain := hMsgC
      rcases hChildAttain t.child E t.gain (E B.root)
          hOccE hMsgE hSafe.1 with
        ⟨E₁, hClear₁, hRoot₁⟩
      rcases hClear₁ with ⟨hReachRaw, hCleared₁⟩
      have hStart :
          (B.childBranch t.child).withBoundary E (E B.root) = E := by
        have hSelf := (B.childBranch t.child).withBoundary_self E
        simpa [childBranch] using hSelf
      have hReachChild :
          (B.childBranch t.child).BranchReach E E₁ := by
        rw [hStart] at hReachRaw
        exact hReachRaw
      have hReachParent : B.BranchReach E E₁ :=
        BranchReach.of_child B t.child hReachChild
      have hParent₁ : E₁ B.parent = E B.parent :=
        BranchReach.eq_of_not_mem_carrier
          (B.childBranch t.child) hReachChild
          (B.parent_not_mem_childBranch_carrier t.child)
      have hSameTail :
          ∀ s ∈ ts, ∀ v ∈ (B.childBranch s.child).vertices,
            E₁ v = C v := by
        intro s hs v hv
        have hst : s.1 ≠ t.1 := by
          intro hEq
          have hObj : s = t := Subtype.ext hEq
          subst s
          exact htNot hs
        have hChildNe : s.child.vertex ≠ t.child.vertex := by
          simpa using hst
        have hOutside :
            v ∉ (B.childBranch t.child).carrier :=
          B.mem_childBranch_vertices_not_mem_sibling_carrier
            s.child t.child hChildNe hv
        have hEqStep :=
          BranchReach.eq_of_not_mem_carrier
            (B.childBranch t.child) hReachChild hOutside
        calc
          E₁ v = E v := hEqStep
          _ = C v := hSame s (by simp [hs]) v hv
      have hSafeTail :
          TaskScheduleSafe
            (fun s : B.OccupiedChild C => s.gain)
            (E₁ B.root : ℤ) ts := by
        rw [hRoot₁]
        exact hSafe.2
      rcases ih E₁ hNodupTail hSameTail hSafeTail with
        ⟨D, hReachTail, hRootTail, hParentTail,
          hClearedTail, hUntouchedTail⟩
      have hReachAll : B.BranchReach E D :=
        Relation.ReflTransGen.trans hReachParent hReachTail
      have hRootAll :
          (D B.root : ℤ) =
            (E B.root : ℤ) +
              taskGainSum
                (fun s : B.OccupiedChild C => s.gain) (t :: ts) := by
        rw [hRootTail, hRoot₁]
        simp only [taskGainSum]
        ring
      have hParentAll : D B.parent = E B.parent := by
        rw [hParentTail, hParent₁]
      have hHeadNotTail :
          ∀ s ∈ ts, s.1 ≠ t.child.vertex := by
        intro s hs hEq
        have hEq' : s.1 = t.1 := by
          simpa using hEq
        have hObj : s = t := Subtype.ext hEq'
        subst s
        exact htNot hs
      have hHeadPres :
          ∀ v ∈ (B.childBranch t.child).vertices, D v = E₁ v :=
        hUntouchedTail t.child hHeadNotTail
      have hClearedHead :
          (B.childBranch t.child).Cleared D := by
        intro v hv
        rw [hHeadPres v hv]
        exact hCleared₁ v hv
      have hClearedAll :
          ∀ s ∈ t :: ts, (B.childBranch s.child).Cleared D := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hClearedHead
        · exact hClearedTail s hs
      have hUntouchedAll :
          ∀ c : B.Child,
            (∀ s ∈ t :: ts, s.1 ≠ c.vertex) →
            ∀ v ∈ (B.childBranch c).vertices, D v = E v := by
        intro c hnot v hv
        have hnotHead : t.1 ≠ c.vertex :=
          hnot t (by simp)
        have hnotTail : ∀ s ∈ ts, s.1 ≠ c.vertex := by
          intro s hs
          exact hnot s (by simp [hs])
        have hcHead : c.vertex ≠ t.child.vertex := by
          simpa using hnotHead.symm
        have hOutside :
            v ∉ (B.childBranch t.child).carrier :=
          B.mem_childBranch_vertices_not_mem_sibling_carrier
            c t.child hcHead hv
        have hStep :=
          BranchReach.eq_of_not_mem_carrier
            (B.childBranch t.child) hReachChild hOutside
        calc
          D v = E₁ v := hUntouchedTail c hnotTail v hv
          _ = E v := hStep
      exact
        ⟨D, hReachAll, hRootAll, hParentAll,
          hClearedAll, hUntouchedAll⟩

/-- Execute every occupied genuine child in the audited order.  The resulting
configuration has accumulated exactly childMessageSum at the root, leaves the
external parent unchanged, and clears every non-root vertex of the branch.
Configuration-empty children are never tasks and remain untouched. -/
theorem executeAllOccupiedChildren
    (B : OrientedBranch T) (C E : Configuration V)
    (hChildAttain :
      ∀ (c : B.Child) (E' : Configuration V) (d : ℤ) (q : ℕ),
        (B.childBranch c).Occupied E' →
        branchMessage E' (B.childBranch c) = some d →
        0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E' q D ∧
            (D B.root : ℤ) = (q : ℤ) + d)
    (hSame :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = C v)
    (hSafe :
      TaskScheduleSafe
        (fun t : B.OccupiedChild C => t.gain)
        (E B.root : ℤ)
        (orderedTasks
          (fun t : B.OccupiedChild C => t.gain)
          (B.occupiedChildTasks C))) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      (D B.root : ℤ) =
        (E B.root : ℤ) + childMessageSum C B ∧
      D B.parent = E B.parent ∧
      (∀ v ∈ B.vertices, v ≠ B.root → D v = 0) := by
  classical
  let gain : B.OccupiedChild C → ℤ := fun t => t.gain
  let baseTasks : List (B.OccupiedChild C) := B.occupiedChildTasks C
  let scheduled : List (B.OccupiedChild C) :=
    orderedTasks gain baseTasks
  have hNodupBase : baseTasks.Nodup := by
    simpa [baseTasks] using B.occupiedChildTasks_nodup C
  have hNodupScheduled : scheduled.Nodup := by
    exact orderedTasks_nodup gain hNodupBase
  have hSameScheduled :
      ∀ t ∈ scheduled, ∀ v ∈ (B.childBranch t.child).vertices,
        E v = C v := by
    intro t ht v hv
    have hvB : v ∈ B.vertices :=
      B.childBranch_vertices_subset t.child hv
    have hvRoot : v ≠ B.root := by
      intro hvr
      subst v
      exact (B.childBranch t.child).parent_not_mem_vertices
        (by simpa using hv)
    exact hSame v hvB hvRoot
  have hSafe' :
      TaskScheduleSafe gain (E B.root : ℤ) scheduled := by
    simpa [gain, baseTasks, scheduled] using hSafe
  rcases executeOccupiedTaskSchedule B C hChildAttain
      scheduled E hNodupScheduled hSameScheduled hSafe' with
    ⟨D, hReach, hRoot, hParent, hCleared, hUntouched⟩
  have hRoot' :
      (D B.root : ℤ) =
        (E B.root : ℤ) + childMessageSum C B := by
    calc
      (D B.root : ℤ) =
          (E B.root : ℤ) + taskGainSum gain scheduled := hRoot
      _ =
          (E B.root : ℤ) + taskGainSum gain baseTasks := by
            change
              (E B.root : ℤ) +
                  taskGainSum gain (orderedTasks gain baseTasks) =
                (E B.root : ℤ) + taskGainSum gain baseTasks
            rw [taskGainSum_orderedTasks]
      _ = (E B.root : ℤ) + childMessageSum C B := by
            change
              (E B.root : ℤ) +
                  taskGainSum
                    (fun t : B.OccupiedChild C => t.gain)
                    (B.occupiedChildTasks C) =
                (E B.root : ℤ) + childMessageSum C B
            rw [taskGainSum_occupiedChildTasks]
  have hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → D v = 0 := by
    intro v hvB hvRoot
    rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hvB hvRoot with
      ⟨c, hvc⟩
    by_cases hOcc : (B.childBranch c).Occupied C
    · let hcv : B.IsChildVertex c.vertex := ⟨c.adj, c.ne_parent⟩
      have hcEq : B.childOfVertex c.vertex hcv = c :=
        Child.eq_of_vertex_eq rfl
      let t : B.OccupiedChild C :=
        ⟨c.vertex, ⟨hcv, by
          rw [hcEq]
          exact hOcc⟩⟩
      have htChild : t.child = c := by
        apply Child.eq_of_vertex_eq
        calc
          t.child.vertex = t.1 := t.child_vertex
          _ = c.vertex := rfl
      have htBase : t ∈ baseTasks := by
        simpa [baseTasks] using B.mem_occupiedChildTasks C t
      have htScheduled : t ∈ scheduled := by
        change t ∈ orderedTasks gain baseTasks
        exact (mem_orderedTasks_iff gain baseTasks t).2 htBase
      have htClear := hCleared t htScheduled
      rw [htChild] at htClear
      exact htClear v hvc
    · have hNoTask :
          ∀ t ∈ scheduled, t.1 ≠ c.vertex := by
        intro t ht hEq
        have htc : t.child = c := by
          apply Child.eq_of_vertex_eq
          simpa using hEq
        have htOcc := t.occupied
        rw [htc] at htOcc
        exact hOcc htOcc
      have hPres : D v = E v :=
        hUntouched c hNoTask v hvc
      have hEC : E v = C v :=
        hSame v hvB hvRoot
      have hC0 : C v = 0 := by
        by_contra hne
        exact hOcc ⟨v, hvc, Nat.pos_of_ne_zero hne⟩
      calc
        D v = E v := hPres
        _ = C v := hEC
        _ = 0 := hC0
  exact ⟨D, hReach, hRoot', hParent, hNonroot⟩

/-- Once all non-root branch vertices are clear, an even root pile 2k
with k at least one is cleared optimally by k outward boundary moves. -/
theorem attainRootTransfer_even
    (B : OrientedBranch T) (E : Configuration V) (k : ℕ)
    (hk : 1 ≤ k)
    (hRoot : E B.root = 2 * k)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  have hEnough : 2 * k ≤ E B.root := by
    omega
  rcases BranchReach.repeat_move B B.adj
      B.root_mem_carrier B.parent_mem_carrier E k hEnough with
    ⟨D, hReach, hDroot, hDparent, hOther⟩
  have hRootZero : D B.root = 0 := by
    rw [hDroot, hRoot]
    omega
  have hCleared : B.Cleared D := by
    intro v hv
    by_cases hvr : v = B.root
    · subst v
      exact hRootZero
    · have hvp : v ≠ B.parent := by
        intro hvp
        subst v
        exact B.parent_not_mem_vertices hv
      rw [hOther v hvr hvp]
      exact hNonroot v hv hvr
  have hkZ : 0 ≤ (k : ℤ) := by positivity
  have hkPosZ : 0 < (k : ℤ) := by exact_mod_cast hk
  have hRootZ : (E B.root : ℤ) = 2 * (k : ℤ) := by
    exact_mod_cast hRoot
  have hF : F (E B.root : ℤ) = (k : ℤ) := by
    apply (F_eq_nonneg_iff (z := (E B.root : ℤ))
      (k := (k : ℤ)) hkZ).2
    exact Or.inl ⟨hkPosZ, hRootZ⟩
  have hParentZ :
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + (k : ℤ) := by
    exact_mod_cast hDparent
  refine ⟨D, hReach, hCleared, ?_⟩
  rw [hF]
  exact hParentZ

/-- Once all non-root branch vertices are clear, an odd root pile 2k+1
with k at least one attains the exact transfer by an explicit legal sequence.
If the boundary is empty, two outward moves are made first; otherwise one
outward move suffices to fund the single inward move. -/
theorem attainRootTransfer_odd
    (B : OrientedBranch T) (E : Configuration V) (k : ℕ)
    (hk : 1 ≤ k)
    (hRoot : E B.root = 2 * k + 1)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0)
    (hPos :
      0 < (E B.parent : ℤ) + F (E B.root : ℤ)) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  have hkMinus : 0 ≤ (k : ℤ) - 1 := by
    omega
  have hRootZ :
      (E B.root : ℤ) = 2 * (k : ℤ) + 1 := by
    exact_mod_cast hRoot
  have hF :
      F (E B.root : ℤ) = (k : ℤ) - 1 := by
    apply (F_eq_nonneg_iff (z := (E B.root : ℤ))
      (k := (k : ℤ) - 1) hkMinus).2
    exact Or.inr (by
      rw [hRootZ]
      ring)
  by_cases hq : E B.parent = 0
  · have hk2 : 2 ≤ k := by
      rw [hF, hq] at hPos
      norm_num at hPos
      omega
    have hEnough1 : 2 * 2 ≤ E B.root := by
      rw [hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E 2 hEnough1 with
      ⟨E₁, hReach₁, h1root, h1parent, h1other⟩
    have hEnough2 : 2 * 1 ≤ E₁ B.parent := by
      omega
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier E₁ 1 hEnough2 with
      ⟨E₂, hReach₂, h2parent, h2root, h2other⟩
    have hEnough3 : 2 * (k - 1) ≤ E₂ B.root := by
      rw [h2root, h1root, hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E₂ (k - 1) hEnough3 with
      ⟨D, hReach₃, h3root, h3parent, h3other⟩
    have hReach :
        B.BranchReach E D :=
      Relation.ReflTransGen.trans hReach₁
        (Relation.ReflTransGen.trans hReach₂ hReach₃)
    have hRootZero : D B.root = 0 := by
      omega
    have hCleared : B.Cleared D := by
      intro v hv
      by_cases hvr : v = B.root
      · subst v
        exact hRootZero
      · have hvp : v ≠ B.parent := by
          intro hvp
          subst v
          exact B.parent_not_mem_vertices hv
        calc
          D v = E₂ v := h3other v hvr hvp
          _ = E₁ v := h2other v hvp hvr
          _ = E v := h1other v hvr hvp
          _ = 0 := hNonroot v hv hvr
    have hParentNat :
        D B.parent = E B.parent + (k - 1) := by
      omega
    have hParentZ :
        (D B.parent : ℤ) =
          (E B.parent : ℤ) + ((k : ℤ) - 1) := by
      calc
        (D B.parent : ℤ) =
            ((E B.parent + (k - 1) : ℕ) : ℤ) := by
              exact_mod_cast hParentNat
        _ = (E B.parent : ℤ) + ((k : ℤ) - 1) := by
              rw [Nat.cast_add, Nat.cast_sub hk]
              norm_num

    refine ⟨D, hReach, hCleared, ?_⟩
    rw [hF]
    exact hParentZ
  · have hq1 : 1 ≤ E B.parent := Nat.one_le_iff_ne_zero.mpr hq
    have hEnough1 : 2 * 1 ≤ E B.root := by
      rw [hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E 1 hEnough1 with
      ⟨E₁, hReach₁, h1root, h1parent, h1other⟩
    have hEnough2 : 2 * 1 ≤ E₁ B.parent := by
      omega
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier E₁ 1 hEnough2 with
      ⟨E₂, hReach₂, h2parent, h2root, h2other⟩
    have hEnough3 : 2 * k ≤ E₂ B.root := by
      rw [h2root, h1root, hRoot]
      omega
    rcases BranchReach.repeat_move B B.adj
        B.root_mem_carrier B.parent_mem_carrier E₂ k hEnough3 with
      ⟨D, hReach₃, h3root, h3parent, h3other⟩
    have hReach :
        B.BranchReach E D :=
      Relation.ReflTransGen.trans hReach₁
        (Relation.ReflTransGen.trans hReach₂ hReach₃)
    have hRootZero : D B.root = 0 := by
      omega
    have hCleared : B.Cleared D := by
      intro v hv
      by_cases hvr : v = B.root
      · subst v
        exact hRootZero
      · have hvp : v ≠ B.parent := by
          intro hvp
          subst v
          exact B.parent_not_mem_vertices hv
        calc
          D v = E₂ v := h3other v hvr hvp
          _ = E₁ v := h2other v hvp hvr
          _ = E v := h1other v hvr hvp
          _ = 0 := hNonroot v hv hvr
    have hParentNat :
        D B.parent = E B.parent + (k - 1) := by
      omega
    have hParentZ :
        (D B.parent : ℤ) =
          (E B.parent : ℤ) + ((k : ℤ) - 1) := by
      calc
        (D B.parent : ℤ) =
            ((E B.parent + (k - 1) : ℕ) : ℤ) := by
              exact_mod_cast hParentNat
        _ = (E B.parent : ℤ) + ((k : ℤ) - 1) := by
              rw [Nat.cast_add, Nat.cast_sub hk]
              norm_num
    refine ⟨D, hReach, hCleared, ?_⟩
    rw [hF]
    exact hParentZ

/-- Root/boundary attainment for every effective root pile at least two. -/
theorem attainRootTransfer_ge_two
    (B : OrientedBranch T) (E : Configuration V)
    (hRootTwo : 2 ≤ E B.root)
    (hNonroot :
      ∀ v ∈ B.vertices, v ≠ B.root → E v = 0)
    (hPos :
      0 < (E B.parent : ℤ) + F (E B.root : ℤ)) :
    ∃ D : Configuration V,
      B.BranchReach E D ∧
      B.Cleared D ∧
      (D B.parent : ℤ) =
        (E B.parent : ℤ) + F (E B.root : ℤ) := by
  classical
  by_cases hEven : Even (E B.root)
  · rcases hEven with ⟨k, hkEq⟩
    have hRoot : E B.root = 2 * k := by
      omega
    have hk : 1 ≤ k := by
      omega
    exact B.attainRootTransfer_even E k hk hRoot hNonroot
  · have hOdd : Odd (E B.root) :=
      Nat.not_even_iff_odd.mp hEven
    rcases hOdd with ⟨k, hkEq⟩
    have hRoot : E B.root = 2 * k + 1 := by
      omega
    have hk : 1 ≤ k := by
      omega
    exact B.attainRootTransfer_odd E k hk hRoot hNonroot hPos

theorem MoveSignature.zero_supportedOn (B : OrientedBranch T) :
    MoveSignature.SupportedOn (MoveSignature.zero T) B := by
  intro u v h
  simp at h

theorem MoveSignature.extend_supportedOn
    (B : OrientedBranch T) (m : MoveSignature T)
    {u v : V} (huv : T.graph.Adj u v)
    (hm : MoveSignature.SupportedOn m B) (hu : u ∈ B.carrier) (hv : v ∈ B.carrier) :
    MoveSignature.SupportedOn (m.extend u v huv) B := by
  intro a b hpos
  by_cases hnew : a = u ∧ b = v
  · rcases hnew with ⟨rfl, rfl⟩
    exact ⟨hu, hv⟩
  · apply hm
    simpa [MoveSignature.extend, hnew] using hpos

/-- Exact pointwise integer accounting for one legal move. -/
theorem move_balance_int (C : Configuration V) {u v : V}
    (huv : u ≠ v) (hu : 2 ≤ C u) (w : V) :
    (move C u v w : ℤ) =
      (C w : ℤ) + (if w = v then 1 else 0) -
        2 * (if w = u then 1 else 0) := by
  classical
  by_cases hwu : w = u
  · subst w
    simp [move, huv, hu]
  · by_cases hwv : w = v
    · subst w
      simp [move, huv.symm, hwu]
    · simp [move, hwu, hwv]

/-- A branch-local reachability proof has an exact oriented move-count
signature.  The final clause is causal on every oriented subbranch contained
in the ambient branch: if no outward boundary move of that subbranch occurs,
initial occupancy of the subbranch persists. -/
theorem BranchReach.exists_moveSignature
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    ∃ m : MoveSignature T,
      MoveSignature.SupportedOn m B ∧
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        m.count A.root A.parent = 0 →
        A.Occupied D) := by
  induction hreach with
  | refl =>
      refine ⟨MoveSignature.zero T, MoveSignature.zero_supportedOn B, ?_, ?_⟩
      · intro w
        simp
      · intro A _ hOcc _
        exact hOcc
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huCarrier, hvCarrier, rfl⟩
      rcases ih with ⟨m, hmSupp, hmBal, hmPersist⟩
      let m' : MoveSignature T := m.extend u v huv
      refine ⟨m', ?_, ?_, ?_⟩
      · exact MoveSignature.extend_supportedOn B m huv hmSupp huCarrier hvCarrier
      · intro w
        rw [move_balance_int _ huv.ne hlegal w, hmBal w]
        simp [m', MoveSignature.incoming_extend, MoveSignature.outgoing_extend]
        by_cases hwu : w = u <;> simp [hwu] <;> ring
      · intro A hAB hOcc hzero
        have hmzero : m.count A.root A.parent = 0 := by
          have hle :
              m.count A.root A.parent ≤ m'.count A.root A.parent := by
            dsimp [m', MoveSignature.extend]
            omega
          omega
        rcases hmPersist A hAB hOcc hmzero with ⟨w, hwA, hwpos⟩
        by_cases hvA : v ∈ A.vertices
        · refine ⟨v, hvA, ?_⟩
          simp [move, huv.ne]
        · have huA : u ∉ A.vertices := by
            intro huA
            have hEdge :=
              A.edge_leaving_vertices_eq_boundary huA hvA huv
            rw [Sym2.eq_iff] at hEdge
            rcases hEdge with h | h
            · rcases h with ⟨huRoot, hvParent⟩
              subst u
              subst v
              dsimp [m', MoveSignature.extend] at hzero
              simp at hzero
            · rcases h with ⟨huParent, hvRoot⟩
              subst u
              exact A.parent_not_mem_vertices huA
          have hwu : w ≠ u := by
            intro h
            subst w
            exact huA hwA
          have hwv : w ≠ v := by
            intro h
            subst w
            exact hvA hwA
          refine ⟨w, hwA, ?_⟩
          simpa [move, hwu, hwv] using hwpos

theorem MoveSignature.incoming_parent_eq_boundary
    (B : OrientedBranch T) (m : MoveSignature T)
    (hm : MoveSignature.SupportedOn m B) :
    m.incoming B.parent = m.count B.root B.parent := by
  classical
  rw [MoveSignature.incoming]
  apply Finset.sum_eq_single B.root
  · intro u _ hune
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hadj := m.supported hpos
    have hcar := (hm hpos).1
    have huCases : u = B.parent ∨ u ∈ B.vertices := by
      simpa [carrier] using hcar
    rcases huCases with hup | hub
    · subst u
      exact hadj.ne rfl
    · exact hune (B.eq_root_of_mem_vertices_adj_parent hub hadj)
  · simp

theorem MoveSignature.outgoing_parent_eq_boundary
    (B : OrientedBranch T) (m : MoveSignature T)
    (hm : MoveSignature.SupportedOn m B) :
    m.outgoing B.parent = m.count B.parent B.root := by
  classical
  rw [MoveSignature.outgoing]
  apply Finset.sum_eq_single B.root
  · intro v _ hvne
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hadj := m.supported hpos
    have hcar := (hm hpos).2
    have hvCases : v = B.parent ∨ v ∈ B.vertices := by
      simpa [carrier] using hcar
    rcases hvCases with hvp | hvb
    · subst v
      exact hadj.ne rfl
    · exact hvne (B.eq_root_of_mem_vertices_adj_parent hvb hadj.symm)
  · simp

/-- Every legal clearing of an initially occupied branch yields a genuine
feasible clearing signature, and the final boundary pile is exactly the
initial boundary pile plus the signature's boundary flux. -/
theorem ClearOutcome.exists_feasibleClearing_signature
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hOcc : B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      MoveSignature.FeasibleClearing m C B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hClears : MoveSignature.Clears m C B := by
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv] at h
    simpa [MoveSignature.BalancesAt] using h.symm
  have hCausal : MoveSignature.CausalOutward m B := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hInitialOcc : B.Occupied (B.withBoundary C q) := by
      exact (B.occupied_withBoundary_iff C q).2 hOcc
    have hFinalOcc :=
      hmPersist B (by intro v hv; exact hv) hInitialOcc hzero
    rcases hFinalOcc with ⟨v, hv, hpos⟩
    rw [hClear.2 v hv] at hpos
    omega
  refine ⟨m, ⟨hmSupp, hClears, hCausal⟩, ?_⟩
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  calc
    (D B.parent : ℤ) =
        (q : ℤ) + (m.count B.root B.parent : ℤ) -
          2 * (m.count B.parent B.root : ℤ) := hParent
    _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
      rw [MoveSignature.boundaryFlux]
      ring


/-- Total pebble mass on the branch carrier. -/
noncomputable def carrierMass (B : OrientedBranch T) (C : Configuration V) : ℕ :=
  ∑ v ∈ B.carrier, C v

theorem carrierMass_move_add_one (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : u ≠ v) (hu : 2 ≤ C u)
    (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.carrierMass (move C u v) + 1 = B.carrierMass C := by
  classical
  simp only [carrierMass, move]
  rw [Finset.sum_update_of_mem hvB, Finset.sdiff_singleton_eq_erase]
  have hu_mem : u ∈ B.carrier.erase v := by
    simp [huB, huv]
  rw [Finset.sum_update_of_mem (s := B.carrier.erase v) (i := u)
      (f := C) (b := C u - 2) hu_mem,
    Finset.sdiff_singleton_eq_erase]
  have hv := Finset.sum_erase_add B.carrier C hvB
  have hu' := Finset.sum_erase_add (B.carrier.erase v) C hu_mem
  omega

theorem BranchReach.carrierMass_le
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    B.carrierMass D ≤ B.carrierMass C := by
  induction hreach with
  | refl => rfl
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huB, hvB, rfl⟩
      have hdrop :=
        B.carrierMass_move_add_one _ huv.ne hlegal huB hvB
      omega

theorem not_occupied_iff_zero_on_vertices
    (B : OrientedBranch T) (C : Configuration V) :
    ¬ B.Occupied C ↔ ∀ v ∈ B.vertices, C v = 0 := by
  constructor
  · intro h v hv
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact h ⟨v, hv, hpos⟩
  · intro hz hOcc
    rcases hOcc with ⟨v, hv, hpos⟩
    rw [hz v hv] at hpos
    omega

theorem carrierMass_withBoundary_eq_of_not_occupied
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    (hEmpty : ¬ B.Occupied C) :
    B.carrierMass (B.withBoundary C q) = q := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hz := (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hsum : ∑ v ∈ B.vertices, B.withBoundary C q v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [B.withBoundary_of_mem_vertices C q hv, hz v hv]
  have hdecomp :=
    Finset.sum_erase_add B.carrier (B.withBoundary C q) hp
  simp only [herase, hsum, B.withBoundary_parent] at hdecomp
  rw [carrierMass]
  omega

theorem carrierMass_eq_parent_of_cleared
    (B : OrientedBranch T) (D : Configuration V) (hClear : B.Cleared D) :
    B.carrierMass D = D B.parent := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hsum : ∑ v ∈ B.vertices, D v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hClear v hv
  have hdecomp := Finset.sum_erase_add B.carrier D hp
  simp only [herase, hsum] at hdecomp
  rw [carrierMass]
  omega

/-- A legal initially empty excursion cannot increase the boundary pile. -/
theorem BranchReach.empty_boundary_nonincrease
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hreach : B.BranchReach (B.withBoundary C q) D)
    (hClear : B.Cleared D) :
    D B.parent ≤ q := by
  have hle := BranchReach.carrierMass_le B hreach
  rw [B.carrierMass_eq_parent_of_cleared D hClear,
    B.carrierMass_withBoundary_eq_of_not_occupied C q hEmpty] at hle
  exact hle

/-- The ±1 bipartite weight based at the exterior boundary vertex. -/
noncomputable def boundaryParityWeight (B : OrientedBranch T) (v : V) : ℤ :=
  if T.graph.dist B.parent v % 2 = 0 then 1 else -1

@[simp] theorem boundaryParityWeight_parent (B : OrientedBranch T) :
    B.boundaryParityWeight B.parent = 1 := by
  simp [boundaryParityWeight]

theorem boundaryParityWeight_adj_neg (B : OrientedBranch T)
    {u v : V} (huv : T.graph.Adj u v) :
    B.boundaryParityWeight v = -B.boundaryParityWeight u := by
  let col := T.isTree.coloringTwoOfVert B.parent
  have hne : col u ≠ col v := col.valid huv
  have hval :
      T.graph.dist B.parent u % 2 ≠ T.graph.dist B.parent v % 2 := by
    intro h
    apply hne
    apply Fin.ext
    exact h
  have huLt : T.graph.dist B.parent u % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  have hvLt : T.graph.dist B.parent v % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  unfold boundaryParityWeight
  by_cases hu0 : T.graph.dist B.parent u % 2 = 0
  · have hv0 : T.graph.dist B.parent v % 2 ≠ 0 := by
      intro hv0
      exact hval (hu0.trans hv0.symm)
    simp [hu0, hv0]
  · have hu1 : T.graph.dist B.parent u % 2 = 1 := by omega
    have hv0 : T.graph.dist B.parent v % 2 = 0 := by
      by_contra hv0
      have hv1 : T.graph.dist B.parent v % 2 = 1 := by omega
      exact hval (hu1.trans hv1.symm)
    simp [hu0, hv0]

/-- Signed carrier mass for the tree bipartition based at the boundary. -/
noncomputable def signedCarrierMass
    (B : OrientedBranch T) (C : Configuration V) : ℤ :=
  ∑ v ∈ B.carrier, B.boundaryParityWeight v * (C v : ℤ)

theorem signedCarrierMass_move (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : T.graph.Adj u v)
    (hu : 2 ≤ C u) (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.signedCarrierMass (move C u v) =
      B.signedCarrierMass C - 3 * B.boundaryParityWeight u := by
  classical
  rw [signedCarrierMass]
  calc
    (∑ w ∈ B.carrier,
        B.boundaryParityWeight w * (move C u v w : ℤ)) =
        ∑ w ∈ B.carrier,
          B.boundaryParityWeight w *
            ((C w : ℤ) + (if w = v then 1 else 0) -
              2 * (if w = u then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [move_balance_int C huv.ne hu w]
    _ =
        (∑ w ∈ B.carrier, B.boundaryParityWeight w * (C w : ℤ)) +
          B.boundaryParityWeight v - 2 * B.boundaryParityWeight u := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        mul_add, mul_sub, huB, hvB] <;> ring
    _ = B.signedCarrierMass C - 3 * B.boundaryParityWeight u := by
      rw [B.boundaryParityWeight_adj_neg huv, signedCarrierMass]
      ring

theorem signedCarrierMass_move_mod_three (B : OrientedBranch T)
    (C : Configuration V) {u v : V} (huv : T.graph.Adj u v)
    (hu : 2 ≤ C u) (huB : u ∈ B.carrier) (hvB : v ∈ B.carrier) :
    B.signedCarrierMass (move C u v) ≡ B.signedCarrierMass C [ZMOD 3] := by
  rw [B.signedCarrierMass_move C huv hu huB hvB, Int.modEq_iff_dvd]
  refine ⟨B.boundaryParityWeight u, ?_⟩
  ring

theorem BranchReach.signedCarrierMass_modEq
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    B.signedCarrierMass D ≡ B.signedCarrierMass C [ZMOD 3] := by
  induction hreach with
  | refl => exact Int.ModEq.refl _
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huB, hvB, rfl⟩
      exact (B.signedCarrierMass_move_mod_three _ huv hlegal huB hvB).trans ih

theorem signedCarrierMass_withBoundary_eq_of_not_occupied
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    (hEmpty : ¬ B.Occupied C) :
    B.signedCarrierMass (B.withBoundary C q) = q := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hz := (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hsum :
      ∑ v ∈ B.vertices,
        B.boundaryParityWeight v * (B.withBoundary C q v : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [B.withBoundary_of_mem_vertices C q hv, hz v hv]
    simp
  have hdecomp :=
    Finset.sum_erase_add B.carrier
      (fun v => B.boundaryParityWeight v * (B.withBoundary C q v : ℤ)) hp
  simp only [herase, hsum, B.withBoundary_parent,
    B.boundaryParityWeight_parent, zero_add, one_mul] at hdecomp
  rw [signedCarrierMass]
  norm_num at hdecomp ⊢
  linarith

theorem signedCarrierMass_eq_parent_of_cleared
    (B : OrientedBranch T) (D : Configuration V) (hClear : B.Cleared D) :
    B.signedCarrierMass D = D B.parent := by
  classical
  have hp : B.parent ∈ B.carrier := by
    simp [carrier]
  have herase := B.carrier_erase_parent
  have hsum :
      ∑ v ∈ B.vertices, B.boundaryParityWeight v * (D v : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [hClear v hv]
    simp
  have hdecomp :=
    Finset.sum_erase_add B.carrier
      (fun v => B.boundaryParityWeight v * (D v : ℤ)) hp
  simp only [herase, hsum, B.boundaryParityWeight_parent,
    zero_add, one_mul] at hdecomp
  rw [signedCarrierMass]
  norm_num at hdecomp ⊢
  linarith

/-- An initially and finally empty legal branch excursion preserves the
boundary pile modulo three. -/
theorem BranchReach.empty_boundary_mod_three
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hreach : B.BranchReach (B.withBoundary C q) D)
    (hClear : B.Cleared D) :
    (D B.parent : ℤ) ≡ (q : ℤ) [ZMOD 3] := by
  have hmod := BranchReach.signedCarrierMass_modEq B hreach
  rw [B.signedCarrierMass_eq_parent_of_cleared D hClear,
    B.signedCarrierMass_withBoundary_eq_of_not_occupied C q hEmpty] at hmod
  exact hmod

/-- Every legal empty-branch excursion has exact boundary flux -3k for some
nonnegative integer k.  The branch remains EMPTY at the message level; zero is
used here only as the omitted formal gain in this excursion calculation. -/
theorem ClearOutcome.exists_emptyExcursion_signature
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      MoveSignature.EmptyExcursion m B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B ∧
      ∃ k : ℤ, 0 ≤ k ∧ MoveSignature.boundaryFlux m B = -3 * k := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hz := (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hExc : MoveSignature.EmptyExcursion m B := by
    refine ⟨hmSupp, ?_⟩
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv, hz v hv] at h
    omega
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  have hFlux :
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
    calc
      (D B.parent : ℤ) =
          (q : ℤ) + (m.count B.root B.parent : ℤ) -
            2 * (m.count B.parent B.root : ℤ) := hParent
      _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
        rw [MoveSignature.boundaryFlux]
        ring
  have hNonpos : MoveSignature.boundaryFlux m B ≤ 0 := by
    have hle :=
      BranchReach.empty_boundary_nonincrease B C q hEmpty hClear.1 hClear.2
    omega
  have hBoundaryMod :=
    BranchReach.empty_boundary_mod_three B C q hEmpty hClear.1 hClear.2
  have hFluxMod :
      MoveSignature.boundaryFlux m B ≡ 0 [ZMOD 3] := by
    rw [Int.modEq_iff_dvd] at hBoundaryMod ⊢
    have heq :
        (q : ℤ) - (D B.parent : ℤ) =
          -MoveSignature.boundaryFlux m B := by
      omega
    rw [heq] at hBoundaryMod
    simpa using hBoundaryMod
  have hDvd : (3 : ℤ) ∣ MoveSignature.boundaryFlux m B :=
    Int.modEq_zero_iff_dvd.mp hFluxMod
  rcases hDvd with ⟨a, ha⟩
  have haNonpos : a ≤ 0 := by
    rw [ha] at hNonpos
    omega
  refine ⟨m, hExc, hFlux, -a, by omega, ?_⟩
  rw [ha]
  ring


/-- Net signature flux contributed by all genuine child edges at the branch
root. This is the signature analogue of the recursive child-message sum. -/
noncomputable def signatureChildFluxSum
    (m : MoveSignature T) (B : OrientedBranch T) : ℤ :=
  ∑ v : V,
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
    else
      0

theorem MoveSignature.incoming_root_eq_parent_add_children
    (m : MoveSignature T) (B : OrientedBranch T) :
    (m.incoming B.root : ℤ) =
      (m.count B.parent B.root : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (m.count v B.root : ℤ)
          else
            0 := by
  classical
  rw [MoveSignature.incoming]
  push_cast
  calc
    (∑ v : V, (m.count v B.root : ℤ)) =
        ∑ v : V,
          ((if v = B.parent then (m.count B.parent B.root : ℤ) else 0) +
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ)
            else
              0) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hvp : v = B.parent
      · subst v
        simp
      · by_cases hadj : T.graph.Adj B.root v
        · simp [hvp, hadj]
        · have hz : m.count v B.root = 0 := by
            apply Nat.eq_zero_of_not_pos
            intro hpos
            exact hadj (m.supported hpos).symm
          simp [hvp, hadj, hz]
    _ =
        (m.count B.parent B.root : ℤ) +
          ∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ)
            else
              0 := by
      rw [Finset.sum_add_distrib]
      simp

theorem MoveSignature.outgoing_root_eq_parent_add_children
    (m : MoveSignature T) (B : OrientedBranch T) :
    (m.outgoing B.root : ℤ) =
      (m.count B.root B.parent : ℤ) +
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (m.count B.root v : ℤ)
          else
            0 := by
  classical
  rw [MoveSignature.outgoing]
  push_cast
  calc
    (∑ v : V, (m.count B.root v : ℤ)) =
        ∑ v : V,
          ((if v = B.parent then (m.count B.root B.parent : ℤ) else 0) +
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count B.root v : ℤ)
            else
              0) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hvp : v = B.parent
      · subst v
        simp
      · by_cases hadj : T.graph.Adj B.root v
        · simp [hvp, hadj]
        · have hz : m.count B.root v = 0 := by
            apply Nat.eq_zero_of_not_pos
            intro hpos
            exact hadj (m.supported hpos)
          simp [hvp, hadj, hz]
    _ =
        (m.count B.root B.parent : ℤ) +
          ∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count B.root v : ℤ)
            else
              0 := by
      rw [Finset.sum_add_distrib]
      simp

theorem signatureChildFluxSum_eq
    (m : MoveSignature T) (B : OrientedBranch T) :
    signatureChildFluxSum m B =
      (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count v B.root : ℤ)
        else
          0) -
      2 * (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count B.root v : ℤ)
        else
          0) := by
  classical
  rw [signatureChildFluxSum]
  calc
    (∑ v : V,
      if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
        (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
      else 0) =
        ∑ v : V,
          ((if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ)
            else 0) -
            2 * (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count B.root v : ℤ)
            else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent <;> simp [h]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The clearing balance at the branch root, separated into the external
boundary edge and the total flux of genuine child branches. -/
theorem MoveSignature.root_balance_with_child_flux
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hbal : m.BalancesAt C B.root) :
    (C B.root : ℤ) + signatureChildFluxSum m B +
        (m.count B.parent B.root : ℤ) -
      2 * (m.count B.root B.parent : ℤ) = 0 := by
  rw [MoveSignature.BalancesAt,
    MoveSignature.incoming_root_eq_parent_add_children m B,
    MoveSignature.outgoing_root_eq_parent_add_children m B] at hbal
  rw [signatureChildFluxSum_eq]
  ring_nf at hbal ⊢
  exact hbal

/-- If a is no larger than b and the two integers have the same residue
modulo three, then a is exactly b minus three times a natural number. -/
theorem exists_nat_three_loss {a b : ℤ}
    (hle : a ≤ b) (hmod : a % 3 = b % 3) :
    ∃ k : ℕ, a = b - 3 * (k : ℤ) := by
  have hme : a ≡ b [ZMOD 3] := by
    change a % 3 = b % 3
    exact hmod
  have hdvd : (3 : ℤ) ∣ b - a :=
    Int.modEq_iff_dvd.mp hme
  rcases hdvd with ⟨k, hk⟩
  have hk0 : 0 ≤ k := by
    omega
  refine ⟨k.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hk0]
  omega

/-- The transfer keeps the same residue modulo three when its input is
lowered by three. -/
theorem F_sub_three_mod_three (z : ℤ) :
    F (z - 3) % 3 = F z % 3 := by
  unfold F
  split_ifs <;> omega

/-- Iterated form of the three-step transfer inequality. -/
theorem F_sub_three_mul_le (z : ℤ) :
    ∀ k : ℕ, F (z - 3 * (k : ℤ)) ≤ F z
  | 0 => by simp
  | k + 1 => by
      calc
        F (z - 3 * ((k + 1 : ℕ) : ℤ)) =
            F ((z - 3 * (k : ℤ)) - 3) := by
              congr 1
              push_cast
              ring
        _ ≤ F (z - 3 * (k : ℤ)) :=
          F_sub_three_le _
        _ ≤ F z :=
          F_sub_three_mul_le z k

/-- Iterated residue form accompanying the three-step transfer inequality. -/
theorem F_sub_three_mul_mod_three (z : ℤ) :
    ∀ k : ℕ, F (z - 3 * (k : ℤ)) % 3 = F z % 3
  | 0 => by simp
  | k + 1 => by
      have harg :
          z - 3 * ((k + 1 : ℕ) : ℤ) =
            (z - 3 * (k : ℤ)) - 3 := by
        push_cast
        ring
      rw [harg, F_sub_three_mod_three]
      exact F_sub_three_mul_mod_three z k


/-- Recursive signature bound.  Every genuine child contributes its recursive
message minus a nonnegative multiple of three; an empty child contributes only
such a three-step loss.  At an occupied branch the resulting boundary flux is
bounded by the recursive transfer and has the same residue modulo three. -/
theorem signature_branchFlux_bounds
    (m : MoveSignature T) (C : Configuration V) (B : OrientedBranch T)
    (hClears : MoveSignature.Clears m C B)
    (hCausal :
      ∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        MoveSignature.CausalOutward m A) :
    (B.Occupied C →
      MoveSignature.boundaryFlux m B ≤ F (effectiveInput C B) ∧
      MoveSignature.boundaryFlux m B % 3 =
        F (effectiveInput C B) % 3) ∧
    (¬ B.Occupied C →
      ∃ k : ℕ,
        MoveSignature.boundaryFlux m B = -3 * (k : ℤ)) := by
  classical
  have hChildLoss :
      ∀ v : V,
        ∃ k : ℕ,
          (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              (m.count v B.root : ℤ) -
                2 * (m.count B.root v : ℤ)
            else
              0) =
            (if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                messageContribution
                  (branchMessage C
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }))
              else
                0) -
              3 * (k : ℤ) := by
    intro v
    by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
    · let c : B.Child :=
        { vertex := v
          adj := h.1
          ne_parent := h.2 }
      have hChildClears :
          MoveSignature.Clears m C (B.childBranch c) := by
        intro w hw
        exact hClears w (B.childBranch_vertices_subset c hw)
      have hChildCausal :
          ∀ A : OrientedBranch T,
            A.vertices ⊆ (B.childBranch c).vertices →
            A.Occupied C →
            MoveSignature.CausalOutward m A := by
        intro A hA hOcc
        apply hCausal A
        intro w hw
        exact B.childBranch_vertices_subset c (hA hw)
        exact hOcc
      have hRec :=
        signature_branchFlux_bounds m C (B.childBranch c)
          hChildClears hChildCausal
      by_cases hOcc : (B.childBranch c).Occupied C
      · have hBound := hRec.1 hOcc
        rcases exists_nat_three_loss hBound.1 hBound.2 with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmsg :=
          branchMessage_eq_some_of_occupied C (B.childBranch c) hOcc
        simpa [h, c, MoveSignature.boundaryFlux, hmsg] using hk
      · rcases hRec.2 hOcc with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmsg :=
          branchMessage_eq_empty_of_not_occupied C (B.childBranch c) hOcc
        simpa [h, c, MoveSignature.boundaryFlux, hmsg] using hk
    · refine ⟨0, ?_⟩
      simp [h]
  choose k hk using hChildLoss
  let K : ℕ := ∑ v : V, k v
  have hK :
      (K : ℤ) = ∑ v : V, (k v : ℤ) := by
    simp [K]
  have hChildSum :
      signatureChildFluxSum m B =
        childMessageSum C B - 3 * (K : ℤ) := by
    rw [signatureChildFluxSum, childMessageSum]
    calc
      (∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          (m.count v B.root : ℤ) - 2 * (m.count B.root v : ℤ)
        else
          0) =
          ∑ v : V,
            ((if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                messageContribution
                  (branchMessage C
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }))
              else
                0) - 3 * (k v : ℤ)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact hk v
      _ =
          (∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              messageContribution
                (branchMessage C
                  (B.childBranch
                    { vertex := v
                      adj := h.1
                      ne_parent := h.2 }))
            else
              0) -
            3 * (∑ v : V, (k v : ℤ)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = childMessageSum C B - 3 * (K : ℤ) := by
        rw [childMessageSum, hK]
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent <;> simp [h]
  have hRoot :=
    MoveSignature.root_balance_with_child_flux m C B
      (hClears B.root B.root_mem_vertices)
  have hBal :
      (effectiveInput C B - 3 * (K : ℤ)) +
          (m.count B.parent B.root : ℤ) -
        2 * (m.count B.root B.parent : ℤ) = 0 := by
    rw [hChildSum] at hRoot
    rw [effectiveInput]
    omega
  constructor
  · intro hOcc
    have hOut :=
      hCausal B (by intro w hw; exact hw) hOcc
    have hA : 1 ≤ (m.count B.root B.parent : ℤ) := by
      exact_mod_cast hOut
    have hIn : 0 ≤ (m.count B.parent B.root : ℤ) := by
      positivity
    have hLocalLe :=
      one_vertex_flux_le
        (y := effectiveInput C B - 3 * (K : ℤ))
        (A := (m.count B.root B.parent : ℤ))
        (B := (m.count B.parent B.root : ℤ))
        hA hIn hBal
    have hLocalMod :=
      one_vertex_flux_mod_three
        (y := effectiveInput C B - 3 * (K : ℤ))
        (A := (m.count B.root B.parent : ℤ))
        (B := (m.count B.parent B.root : ℤ))
        hA hIn hBal
    constructor
    · rw [MoveSignature.boundaryFlux]
      exact hLocalLe.trans
        (F_sub_three_mul_le (effectiveInput C B) K)
    · rw [MoveSignature.boundaryFlux]
      calc
        ((m.count B.root B.parent : ℤ) -
              2 * (m.count B.parent B.root : ℤ)) % 3 =
            F (effectiveInput C B - 3 * (K : ℤ)) % 3 :=
          hLocalMod
        _ = F (effectiveInput C B) % 3 :=
          F_sub_three_mul_mod_three (effectiveInput C B) K
  · intro hEmpty
    have hZero :=
      (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
    have hRootZero : C B.root = 0 :=
      hZero B.root B.root_mem_vertices
    have hChildMessageZero : childMessageSum C B = 0 := by
      rw [childMessageSum]
      apply Finset.sum_eq_zero
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hChildEmpty : ¬ (B.childBranch c).Occupied C := by
          rintro ⟨w, hw, hwpos⟩
          exact hEmpty
            ⟨w, B.childBranch_vertices_subset c hw, hwpos⟩
        have hmsg :=
          branchMessage_eq_empty_of_not_occupied C (B.childBranch c)
            hChildEmpty
        simp [h, c, hmsg]
      · simp [h]
    rw [hChildSum] at hRoot
    simp [hRootZero, hChildMessageZero] at hRoot
    refine ⟨m.count B.root B.parent + 2 * K, ?_⟩
    rw [MoveSignature.boundaryFlux]
    push_cast
    omega
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c


/-- Necessity half of the exact boundary invariant.  Any legal clearing of an
occupied branch leaves no more than its recursive message gain at the external
boundary. -/
theorem ClearOutcome.boundary_le_message
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hClear : B.ClearOutcome C q D) :
    (D B.parent : ℤ) ≤ (q : ℤ) + d := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hClears : MoveSignature.Clears m C B := by
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv] at h
    simpa [MoveSignature.BalancesAt] using h.symm
  have hCausal :
      ∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        MoveSignature.CausalOutward m A := by
    intro A hAB hAOcc
    apply Nat.pos_of_ne_zero
    intro hzero
    have hAOcc' : A.Occupied (B.withBoundary C q) := by
      rcases hAOcc with ⟨v, hvA, hvpos⟩
      have hvB : v ∈ B.vertices := hAB hvA
      refine ⟨v, hvA, ?_⟩
      simpa [B.withBoundary_of_mem_vertices C q hvB] using hvpos
    have hFinalOcc := hmPersist A hAB hAOcc' hzero
    rcases hFinalOcc with ⟨v, hvA, hvpos⟩
    have hvB : v ∈ B.vertices := hAB hvA
    rw [hClear.2 v hvB] at hvpos
    omega
  have hBound :=
    (signature_branchFlux_bounds m C B hClears hCausal).1 hOcc
  have hMsgCanonical :=
    branchMessage_eq_some_of_occupied C B hOcc
  have hd : d = F (effectiveInput C B) := by
    rw [hMsgCanonical] at hMsg
    exact (Option.some.inj hMsg).symm
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  have hFlux :
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
    calc
      (D B.parent : ℤ) =
          (q : ℤ) + (m.count B.root B.parent : ℤ) -
            2 * (m.count B.parent B.root : ℤ) := hParent
      _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
        rw [MoveSignature.boundaryFlux]
        ring
  rw [hFlux, hd]
  linarith [hBound.1]

/-- If the boundary plus recursive message is nonpositive, no legal clearing
can leave a positive boundary pile. -/
theorem ClearOutcome.no_positive_boundary_of_message_nonpos
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hNonpos : (q : ℤ) + d ≤ 0) :
    ¬ ∃ D : Configuration V,
      B.ClearOutcome C q D ∧ 0 < D B.parent := by
  rintro ⟨D, hClear, hPos⟩
  have hle :=
    ClearOutcome.boundary_le_message B C q hOcc hMsg hClear
  have hPosInt : 0 < (D B.parent : ℤ) := by
    exact_mod_cast hPos
  omega

/-- Constructive half of the exact boundary invariant.  For every occupied
branch, whenever the requested final boundary value q+d is positive, there is
a legal branch-local clearing that attains it exactly.  The recursion is on
strict child-branch cardinality. -/
theorem boundary_attainment
    (C : Configuration V) (B : OrientedBranch T)
    (hOcc : B.Occupied C) :
    ∀ d : ℤ, branchMessage C B = some d →
      ∀ q : ℕ, 0 < (q : ℤ) + d →
        ∃ D : Configuration V,
          B.ClearOutcome C q D ∧
            (D B.parent : ℤ) = (q : ℤ) + d := by
  classical
  intro d hMsg q hPos
  have hCanonical :=
    branchMessage_eq_some_of_occupied C B hOcc
  have hd : d = F (effectiveInput C B) := by
    rw [hCanonical] at hMsg
    exact (Option.some.inj hMsg).symm
  have hFinalF :
      0 < (q : ℤ) + F (effectiveInput C B) := by
    simpa [hd] using hPos
  have hChildAttain :
      ∀ (c : B.Child) (E : Configuration V) (d' : ℤ) (q' : ℕ),
        (B.childBranch c).Occupied E →
        branchMessage E (B.childBranch c) = some d' →
        0 < (q' : ℤ) + d' →
        ∃ D : Configuration V,
          (B.childBranch c).ClearOutcome E q' D ∧
            (D B.root : ℤ) = (q' : ℤ) + d' := by
    intro c E d' q' hOcc' hMsg' hPos'
    exact boundary_attainment E (B.childBranch c)
      hOcc' d' hMsg' q' hPos'
  by_cases hy : effectiveInput C B ≤ 1
  · have hF :
        F (effectiveInput C B) =
          2 * effectiveInput C B - 3 :=
      F_of_le_one hy
    have hbNonneg :
        0 ≤ 2 - effectiveInput C B := by
      omega
    let b : ℕ := (2 - effectiveInput C B).toNat
    have hbCast :
        (b : ℤ) = 2 - effectiveInput C B := by
      change (((2 - effectiveInput C B).toNat : ℕ) : ℤ) =
        2 - effectiveInput C B
      rw [Int.toNat_of_nonneg hbNonneg]
    have hqEnoughZ :
        2 * (b : ℤ) ≤ (q : ℤ) := by
      rw [hF] at hFinalF
      rw [hbCast]
      omega
    have hqEnough : 2 * b ≤ q := by
      exact_mod_cast hqEnoughZ
    have hPreEnough :
        2 * b ≤ (B.withBoundary C q) B.parent := by
      simpa using hqEnough
    rcases BranchReach.repeat_move B B.adj.symm
        B.parent_mem_carrier B.root_mem_carrier
        (B.withBoundary C q) b hPreEnough with
      ⟨Epre, hPreReach, hPreParent, hPreRoot, hPreOther⟩
    have hPreRootNat :
        Epre B.root = C B.root + b := by
      simpa [B.withBoundary_of_mem_vertices C q
        B.root_mem_vertices] using hPreRoot
    have hPreRootZ :
        (Epre B.root : ℤ) =
          (C B.root : ℤ) + (b : ℤ) := by
      exact_mod_cast hPreRootNat
    have hScheduleFinal :
        (Epre B.root : ℤ) + childMessageSum C B = 2 := by
      calc
        (Epre B.root : ℤ) + childMessageSum C B =
            (C B.root : ℤ) + (b : ℤ) +
              childMessageSum C B := by rw [hPreRootZ]
        _ = effectiveInput C B + (b : ℤ) := by
              rw [effectiveInput]
              ring
        _ = 2 := by
              rw [hbCast]
              ring
    have hSamePre :
        ∀ v ∈ B.vertices, v ≠ B.root → Epre v = C v := by
      intro v hv hvRoot
      have hvParent : v ≠ B.parent := by
        intro hvp
        subst v
        exact B.parent_not_mem_vertices hv
      calc
        Epre v = B.withBoundary C q v :=
          hPreOther v hvParent hvRoot
        _ = C v := B.withBoundary_of_mem_vertices C q hv
    have hSafe :
        TaskScheduleSafe
          (fun t : B.OccupiedChild C => t.gain)
          (Epre B.root : ℤ)
          (orderedTasks
            (fun t : B.OccupiedChild C => t.gain)
            (B.occupiedChildTasks C)) := by
      apply orderedTasks_safe
      · positivity
      · rw [taskGainSum_occupiedChildTasks]
        omega
    rcases B.executeAllOccupiedChildren C Epre hChildAttain
        hSamePre hSafe with
      ⟨E₁, hChildReach, hChildRoot, hChildParent, hNonroot⟩
    have hE₁RootZ : (E₁ B.root : ℤ) = 2 := by
      calc
        (E₁ B.root : ℤ) =
            (Epre B.root : ℤ) + childMessageSum C B :=
          hChildRoot
        _ = 2 := hScheduleFinal
    have hE₁Root : E₁ B.root = 2 := by
      exact_mod_cast hE₁RootZ
    rcases B.attainRootTransfer_even E₁ 1 (by omega)
        hE₁Root hNonroot with
      ⟨D, hRootReach, hCleared, hDParent⟩
    have hPreParentNat :
        Epre B.parent = q - 2 * b := by
      simpa [B.withBoundary_parent C q] using hPreParent
    have hPreParentZ :
        (Epre B.parent : ℤ) =
          (q : ℤ) - 2 * (b : ℤ) := by
      calc
        (Epre B.parent : ℤ) = ((q - 2 * b : ℕ) : ℤ) := by
          exact_mod_cast hPreParentNat
        _ = (q : ℤ) - 2 * (b : ℤ) := by
          rw [Nat.cast_sub hqEnough]
          norm_num
    have hParentFinal :
        (D B.parent : ℤ) = (q : ℤ) + d := by
      rw [hDParent, hChildParent, hE₁RootZ, F_two,
        hPreParentZ, hd, hF, hbCast]
      ring
    have hReach :
        B.BranchReach (B.withBoundary C q) D :=
      Relation.ReflTransGen.trans hPreReach
        (Relation.ReflTransGen.trans hChildReach hRootReach)
    exact ⟨D, ⟨hReach, hCleared⟩, hParentFinal⟩
  · have hyTwo : 2 ≤ effectiveInput C B := by
      omega
    have hyPos : 0 < effectiveInput C B := by
      omega
    have hSafe :
        TaskScheduleSafe
          (fun t : B.OccupiedChild C => t.gain)
          ((B.withBoundary C q) B.root : ℤ)
          (orderedTasks
            (fun t : B.OccupiedChild C => t.gain)
            (B.occupiedChildTasks C)) := by
      apply orderedTasks_safe
      · positivity
      · rw [taskGainSum_occupiedChildTasks,
          B.withBoundary_of_mem_vertices C q B.root_mem_vertices]
        simpa [effectiveInput] using hyPos
    have hSame :
        ∀ v ∈ B.vertices, v ≠ B.root →
          B.withBoundary C q v = C v := by
      intro v hv hvr
      exact B.withBoundary_of_mem_vertices C q hv
    rcases B.executeAllOccupiedChildren C (B.withBoundary C q)
        hChildAttain hSame hSafe with
      ⟨E₁, hChildReach, hChildRoot, hChildParent, hNonroot⟩
    have hE₁RootZ :
        (E₁ B.root : ℤ) = effectiveInput C B := by
      calc
        (E₁ B.root : ℤ) =
            ((B.withBoundary C q) B.root : ℤ) +
              childMessageSum C B := hChildRoot
        _ = effectiveInput C B := by
              rw [B.withBoundary_of_mem_vertices C q
                B.root_mem_vertices]
              rfl
    have hE₁RootTwo : 2 ≤ E₁ B.root := by
      have hz : (2 : ℤ) ≤ (E₁ B.root : ℤ) := by
        rw [hE₁RootZ]
        exact hyTwo
      exact_mod_cast hz
    have hE₁Parent : E₁ B.parent = q := by
      rw [hChildParent, B.withBoundary_parent C q]
    have hTransferPos :
        0 < (E₁ B.parent : ℤ) + F (E₁ B.root : ℤ) := by
      rw [hE₁Parent, hE₁RootZ]
      exact hFinalF
    rcases B.attainRootTransfer_ge_two E₁ hE₁RootTwo
        hNonroot hTransferPos with
      ⟨D, hRootReach, hCleared, hDParent⟩
    have hParentFinal :
        (D B.parent : ℤ) = (q : ℤ) + d := by
      rw [hDParent, hE₁Parent, hE₁RootZ, hd]
    have hReach :
        B.BranchReach (B.withBoundary C q) D :=
      Relation.ReflTransGen.trans hChildReach hRootReach
    exact ⟨D, ⟨hReach, hCleared⟩, hParentFinal⟩
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt c


/-- The exact boundary theorem in the form targeted by the Phase 1 induction.
This is a proposition/target definition; later proofs must establish it from
legal move sequences and the recursive message.

For an occupied branch with integer message `d`, every clear outcome leaves
at most `q+d` pebbles at the boundary; when `q+d>0` that value is attained;
when `q+d≤0` no positive boundary pile after clearing is reachable. -/
def ExactBoundaryInvariant (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.Occupied C →
    ∀ d : ℤ, branchMessage C B = some d →
      ∀ q : ℕ,
        (0 < (q : ℤ) + d →
          ∃ D : Configuration V,
            B.ClearOutcome C q D ∧
              (D B.parent : ℤ) = (q : ℤ) + d) ∧
        (∀ D : Configuration V,
          B.ClearOutcome C q D →
            (D B.parent : ℤ) ≤ (q : ℤ) + d) ∧
        ((q : ℤ) + d ≤ 0 →
          ¬ ∃ D : Configuration V,
            B.ClearOutcome C q D ∧ 0 < D B.parent)

/-- Full machine-checkable exact boundary invariant: constructive exact
attainment, universal upper bound, and nonpositive impossibility. -/
theorem exactBoundaryInvariant
    (C : Configuration V) (B : OrientedBranch T) :
    ExactBoundaryInvariant C B := by
  intro hOcc d hMsg q
  refine ⟨?_, ?_, ?_⟩
  · intro hPos
    exact boundary_attainment C B hOcc d hMsg q hPos
  · intro D hClear
    exact ClearOutcome.boundary_le_message
      B C q hOcc hMsg hClear
  · intro hNonpos
    exact ClearOutcome.no_positive_boundary_of_message_nonpos
      B C q hOcc hMsg hNonpos

end LegalSequences

end OrientedBranch

end TreeStack

/- Source module: TreeStack.RootScore.lean -/
namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The oriented branch on the u-side of an edge u-r, viewed toward target r. -/
def incidentBranch (T : FiniteTree V) (r u : V)
    (h : T.graph.Adj u r) : OrientedBranch T where
  root := u
  parent := r
  adj := h

@[simp] theorem incidentBranch_root (r u : V) (h : T.graph.Adj u r) :
    (incidentBranch T r u h).root = u := rfl

@[simp] theorem incidentBranch_parent (r u : V) (h : T.graph.Adj u r) :
    (incidentBranch T r u h).parent = r := rfl

/-- Distinct incident branches at one target have disjoint interiors. -/
theorem incidentBranch_vertices_disjoint
    (r : V) {u v : V}
    (hu : T.graph.Adj u r) (hv : T.graph.Adj v r)
    (huv : u ≠ v) :
    Disjoint
      (incidentBranch T r u hu).vertices
      (incidentBranch T r v hv).vertices := by
  classical
  let A : OrientedBranch T := incidentBranch T r u hu
  let B : OrientedBranch T := incidentBranch T r v hv
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have hvOutside : v ∉ A.vertices := by
    intro hvA
    have heq :=
      A.eq_root_of_mem_vertices_adj_parent
        hvA (by simpa [A, incidentBranch] using hv)
    have heq' : v = u := by
      simpa [A, incidentBranch] using heq
    exact huv heq'.symm
  have hvComp0 : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hvComp : v ∈ B.component.supp := by
    simpa [B, incidentBranch] using hvComp0
  have hxComp : x ∈ B.component.supp := by
    simpa [OrientedBranch.vertices] using hxB
  have hreach : B.deletedGraph.Reachable v x := by
    have :=
      B.component.reachable_of_mem_supp hvComp hxComp
    simpa [B, incidentBranch] using this
  have hreach' :
      (T.graph.deleteEdges {s(v, r)}).Reachable v x := by
    simpa [B, incidentBranch, OrientedBranch.deletedGraph] using hreach
  rcases SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach' with
    ⟨p, havoidB⟩
  have hxASet : x ∈ (A.vertices : Set V) := by
    simpa using hxA
  have hvOutsideSet : v ∉ (A.vertices : Set V) := by
    simpa using hvOutside
  rcases p.reverse.exists_boundary_dart
      (A.vertices : Set V) hxASet hvOutsideSet with
    ⟨⟨⟨a, b⟩, hab⟩, hdart, haSet, hbSet⟩
  have haFin : a ∈ A.vertices := by simpa using haSet
  have hbFin : b ∉ A.vertices := by simpa using hbSet
  have hedge :=
    A.edge_leaving_vertices_eq_boundary haFin hbFin hab
  have hbRoot : b = r := by
    rw [Sym2.eq_iff] at hedge
    rcases hedge with h | h
    · have : b = A.parent := h.2
      simpa [A, incidentBranch] using this
    · have haParent : a = A.parent := h.1
      have : a = r := by simpa [A, incidentBranch] using haParent
      subst a
      have hrNot : r ∉ A.vertices := by
        simpa [A, incidentBranch] using A.parent_not_mem_vertices
      exact (hrNot haFin).elim
  have hrRev : r ∈ p.reverse.support := by
    rw [← hbRoot]
    exact p.reverse.dart_snd_mem_support_of_mem_darts hdart
  have hr : r ∈ p.support := by simpa using hrRev
  let q : T.graph.Walk v r := p.takeUntil r hr
  have hqAvoid : s(v, r) ∉ q.edges := by
    intro hq
    exact havoidB (p.edges_takeUntil_subset_edges hr hq)
  have hreachRoot :
      (T.graph.deleteEdges {s(v, r)}).Reachable v r :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨q, hqAvoid⟩
  have hbridge : T.graph.IsBridge s(v, r) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) hv
  exact (SimpleGraph.isBridge_iff.mp hbridge) hreachRoot

/-- A vertex inside one incident branch is outside every distinct incident
branch carrier.  The only shared carrier point is the target itself. -/
theorem mem_incidentBranch_vertices_not_mem_sibling_carrier
    (r : V) {u v w : V}
    (hu : T.graph.Adj u r) (hv : T.graph.Adj v r)
    (huv : u ≠ v)
    (hw : w ∈ (incidentBranch T r u hu).vertices) :
    w ∉ (incidentBranch T r v hv).carrier := by
  classical
  intro hwCarrier
  have hwCases :
      w = r ∨ w ∈ (incidentBranch T r v hv).vertices := by
    simpa [OrientedBranch.carrier, incidentBranch] using hwCarrier
  rcases hwCases with hroot | hwv
  · subst w
    exact (incidentBranch T r u hu).parent_not_mem_vertices hw
  · exact
      (Finset.disjoint_left.mp
        (incidentBranch_vertices_disjoint (T := T) r hu hv huv)) hw hwv

/-- Every vertex other than the target lies in a genuine incident branch. -/
theorem exists_incidentBranch_mem_of_ne_root
    (r : V) {x : V} (hxr : x ≠ r) :
    ∃ u : V, ∃ h : T.graph.Adj u r,
      x ∈ (incidentBranch T r u h).vertices := by
  classical
  obtain ⟨p, hp⟩ :=
    T.isTree.connected.preconnected.exists_isPath r x
  rcases SimpleGraph.Walk.exists_eq_cons_of_ne hxr.symm p with
    ⟨u, hru, p', hpEq⟩
  rw [hpEq] at hp
  have hpData :=
    (SimpleGraph.Walk.cons_isPath_iff hru p').mp hp
  have hrNot : r ∉ p'.support := hpData.2
  have hur : T.graph.Adj u r := hru.symm
  have havoid : s(u, r) ∉ p'.edges := by
    intro he
    exact hrNot (p'.snd_mem_support_of_mem_edges he)
  let q :
      (T.graph.deleteEdges {s(u, r)}).Walk u x :=
    p'.toDeleteEdges {s(u, r)} (by
      intro e he
      simp only [Set.mem_singleton_iff]
      intro heq
      subst e
      exact havoid he)
  have hreach :
      (incidentBranch T r u hur).deletedGraph.Reachable u x := by
    change (T.graph.deleteEdges {s(u, r)}).Reachable u x
    exact ⟨q⟩
  refine ⟨u, hur, ?_⟩
  rw [OrientedBranch.vertices, Set.mem_toFinset,
    SimpleGraph.ConnectedComponent.mem_supp_iff,
    OrientedBranch.component]
  exact (SimpleGraph.ConnectedComponent.sound hreach).symm

/-- Integer contribution of one possible neighbor to the rooted score. -/
noncomputable def rootMessageTerm
    (T : FiniteTree V) (C : Configuration V) (r u : V) : ℤ :=
  if h : T.graph.Adj u r then
    OrientedBranch.messageContribution
      (OrientedBranch.branchMessage C (incidentBranch T r u h))
  else
    0

/-- Sum of all non-EMPTY incident branch messages toward a target root. -/
noncomputable def rootMessageSum
    (T : FiniteTree V) (C : Configuration V) (r : V) : ℤ :=
  ∑ u : V, rootMessageTerm T C r u

/-- Rooted stackability score from the audited branch-message theorem. -/
noncomputable def score
    (T : FiniteTree V) (C : Configuration V) (r : V) : ℤ :=
  (C r : ℤ) + rootMessageSum T C r

/-- Predicate saying that u indexes an occupied incident branch toward r. -/
def IsOccupiedRootNeighbor
    (T : FiniteTree V) (C : Configuration V) (r u : V) : Prop :=
  ∃ h : T.graph.Adj u r, (incidentBranch T r u h).Occupied C

/-- Executable rooted task: an occupied genuine incident branch. -/
def RootTask
    (T : FiniteTree V) (C : Configuration V) (r : V) :=
  {u : V // IsOccupiedRootNeighbor T C r u}

noncomputable instance RootTask.instFintype
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    Fintype (RootTask T C r) :=
  Fintype.ofInjective
    (fun t : RootTask T C r => (t.1 : V))
    Subtype.val_injective

/-- Incident branch represented by a rooted executable task. -/
noncomputable def RootTask.branch
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) : OrientedBranch T :=
  incidentBranch T r t.1 (Classical.choose t.2)

theorem RootTask.occupied
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.Occupied C := by
  exact Classical.choose_spec t.2

theorem RootTask.branch_eq_incident
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) (h : T.graph.Adj t.1 r) :
    t.branch = incidentBranch T r t.1 h := by
  have hp :
      Classical.choose t.2 = h :=
    Subsingleton.elim _ _
  simp [RootTask.branch, hp]

@[simp] theorem RootTask.branch_root
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.root = t.1 := rfl

@[simp] theorem RootTask.branch_parent
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.parent = r := rfl

/-- Recursive gain attached to a rooted executable task. -/
noncomputable def RootTask.gain
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) : ℤ :=
  OrientedBranch.messageContribution
    (OrientedBranch.branchMessage C t.branch)

theorem RootTask.gain_eq_F
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.gain = F (OrientedBranch.effectiveInput C t.branch) := by
  rw [RootTask.gain,
    OrientedBranch.branchMessage_eq_some_of_occupied C t.branch t.occupied]
  rfl

theorem rootMessageTerm_eq_zero_of_not_occupied
    (T : FiniteTree V) (C : Configuration V) (r : V) {u : V}
    (hu : ¬ IsOccupiedRootNeighbor T C r u) :
    rootMessageTerm T C r u = 0 := by
  by_cases h : T.graph.Adj u r
  · have hEmpty : ¬ (incidentBranch T r u h).Occupied C := by
      intro hOcc
      exact hu ⟨h, hOcc⟩
    simp [rootMessageTerm, h,
      OrientedBranch.branchMessage_eq_empty_of_not_occupied
        C (incidentBranch T r u h) hEmpty]
  · simp [rootMessageTerm, h]

theorem RootTask.gain_eq_term
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.gain = rootMessageTerm T C r t.1 := by
  have h : T.graph.Adj t.1 r := Classical.choose t.2
  simp [RootTask.gain, RootTask.branch, rootMessageTerm, h]

/-- Unscheduled rooted task list: every occupied incident branch exactly once. -/
noncomputable def rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    List (RootTask T C r) := by
  classical
  exact (Finset.univ : Finset (RootTask T C r)).toList

theorem rootTasks_nodup
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    (rootTasks T C r).Nodup := by
  classical
  exact Finset.nodup_toList (Finset.univ : Finset (RootTask T C r))

@[simp] theorem mem_rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (t : RootTask T C r) :
    t ∈ rootTasks T C r := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

/-- Rooted executable task gains sum to the full rooted message sum.
Configuration-empty branches contribute zero to the mathematical sum but
never appear as tasks. -/
theorem taskGainSum_rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    taskGainSum
        (fun t : RootTask T C r => t.gain)
        (rootTasks T C r) =
      rootMessageSum T C r := by
  classical
  calc
    taskGainSum
        (fun t : RootTask T C r => t.gain)
        (rootTasks T C r) =
        ∑ t : RootTask T C r, t.gain := by
          rw [rootTasks, taskGainSum_toList]
    _ = ∑ t : RootTask T C r,
          rootMessageTerm T C r t.1 := by
          apply Finset.sum_congr rfl
          intro t _
          exact t.gain_eq_term
    _ = ∑ u ∈
          (Finset.univ.filter fun u : V =>
            IsOccupiedRootNeighbor T C r u),
          rootMessageTerm T C r u := by
          symm
          simpa [RootTask] using
            (Finset.sum_subtype
              (Finset.univ.filter fun u : V =>
                IsOccupiedRootNeighbor T C r u)
              (fun u => by simp)
              (fun u => rootMessageTerm T C r u))
    _ = ∑ u : V, rootMessageTerm T C r u := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro u huUniv huNot
          have huNotOcc : ¬ IsOccupiedRootNeighbor T C r u := by
            intro huOcc
            exact huNot (Finset.mem_filter.mpr ⟨huUniv, huOcc⟩)
          exact rootMessageTerm_eq_zero_of_not_occupied T C r huNotOcc
    _ = rootMessageSum T C r := rfl



/-- A branch-local legal reach is in particular a global legal reach. -/
theorem OrientedBranch.BranchReach.toReach
    [DecidableEq V] (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    Reach T.graph C D := by
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hCE hED ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hED with ⟨u, v, huv, hlegal, huCarrier, hvCarrier, rfl⟩
      exact ⟨u, v, huv, hlegal, rfl⟩

/-- A vertex in one rooted task interior lies outside the carrier of every
distinct rooted task. -/
theorem RootTask.mem_vertices_not_mem_sibling_carrier
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (s t : RootTask T C r) (hst : s.1 ≠ t.1) {v : V}
    (hv : v ∈ s.branch.vertices) :
    v ∉ t.branch.carrier := by
  change
    v ∈ (incidentBranch T r s.1 (Classical.choose s.2)).vertices at hv
  change
    v ∉ (incidentBranch T r t.1 (Classical.choose t.2)).carrier
  exact mem_incidentBranch_vertices_not_mem_sibling_carrier
    (T := T) r (Classical.choose s.2) (Classical.choose t.2) hst hv

/-- Execute a safe list of occupied incident branches toward one target root.
Every task attains its exact branch message gain; distinct incident interiors
are preserved by locality. -/
theorem executeRootTaskSchedule
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    ∀ (tasks : List (RootTask T C r)) (E : Configuration V),
      tasks.Nodup →
      (∀ t ∈ tasks, ∀ v ∈ t.branch.vertices, E v = C v) →
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (E r : ℤ) tasks →
      ∃ D : Configuration V,
        Reach T.graph E D ∧
        (D r : ℤ) =
          (E r : ℤ) +
            taskGainSum (fun t : RootTask T C r => t.gain) tasks ∧
        (∀ t ∈ tasks, t.branch.Cleared D) ∧
        (∀ (u : V) (h : T.graph.Adj u r),
          (∀ t ∈ tasks, t.1 ≠ u) →
          ∀ v ∈ (incidentBranch T r u h).vertices, D v = E v) := by
  classical
  intro tasks
  induction tasks with
  | nil =>
      intro E hNodup hSame hSafe
      refine ⟨E, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp [taskGainSum]
      · intro t ht
        simp at ht
      · intro u h hnot v hv
        rfl
  | cons t ts ih =>
      intro E hNodup hSame hSafe
      have hNodupData := List.nodup_cons.mp hNodup
      have htNot : t ∉ ts := hNodupData.1
      have hNodupTail : ts.Nodup := hNodupData.2
      change
        0 < (E r : ℤ) + t.gain ∧
          TaskScheduleSafe
            (fun s : RootTask T C r => s.gain)
            ((E r : ℤ) + t.gain) ts at hSafe
      have hSameHead :
          ∀ v ∈ t.branch.vertices, E v = C v :=
        hSame t (by simp)
      have hCE :
          ∀ v ∈ t.branch.vertices, C v = E v := by
        intro v hv
        exact (hSameHead v hv).symm
      have hOccE : t.branch.Occupied E :=
        (t.branch.occupied_congr_vertices C E hCE).mp t.occupied
      have hMsgC :
          OrientedBranch.branchMessage C t.branch = some t.gain := by
        rw [OrientedBranch.branchMessage_eq_some_of_occupied
          C t.branch t.occupied, t.gain_eq_F]
      have hMsgE :
          OrientedBranch.branchMessage E t.branch = some t.gain := by
        calc
          OrientedBranch.branchMessage E t.branch =
              OrientedBranch.branchMessage C t.branch :=
            (OrientedBranch.branchMessage_congr_vertices
              C E t.branch hCE).symm
          _ = some t.gain := hMsgC
      rcases OrientedBranch.boundary_attainment
          E t.branch hOccE t.gain hMsgE (E r) hSafe.1 with
        ⟨E₁, hClear₁, hRoot₁⟩
      rcases hClear₁ with ⟨hReachRaw, hCleared₁⟩
      have hStart : t.branch.withBoundary E (E r) = E := by
        have hSelf := t.branch.withBoundary_self E
        simpa using hSelf
      have hReachBranch : t.branch.BranchReach E E₁ := by
        rw [hStart] at hReachRaw
        exact hReachRaw
      have hReachGlobal : Reach T.graph E E₁ :=
        OrientedBranch.BranchReach.toReach t.branch hReachBranch
      have hRoot₁' :
          (E₁ r : ℤ) = (E r : ℤ) + t.gain := by
        simpa using hRoot₁
      have hSameTail :
          ∀ s ∈ ts, ∀ v ∈ s.branch.vertices, E₁ v = C v := by
        intro s hs v hv
        have hst : s.1 ≠ t.1 := by
          intro hEq
          have hObj : s = t := Subtype.ext hEq
          subst s
          exact htNot hs
        have hOutside : v ∉ t.branch.carrier :=
          s.mem_vertices_not_mem_sibling_carrier t hst hv
        have hEqStep :=
          OrientedBranch.BranchReach.eq_of_not_mem_carrier
            t.branch hReachBranch hOutside
        calc
          E₁ v = E v := hEqStep
          _ = C v := hSame s (by simp [hs]) v hv
      have hSafeTail :
          TaskScheduleSafe
            (fun s : RootTask T C r => s.gain)
            (E₁ r : ℤ) ts := by
        rw [hRoot₁']
        exact hSafe.2
      rcases ih E₁ hNodupTail hSameTail hSafeTail with
        ⟨D, hReachTail, hRootTail, hClearedTail, hUntouchedTail⟩
      have hReachAll : Reach T.graph E D :=
        Relation.ReflTransGen.trans hReachGlobal hReachTail
      have hRootAll :
          (D r : ℤ) =
            (E r : ℤ) +
              taskGainSum
                (fun s : RootTask T C r => s.gain) (t :: ts) := by
        rw [hRootTail, hRoot₁']
        simp only [taskGainSum]
        ring
      have hHeadNotTail :
          ∀ s ∈ ts, s.1 ≠ t.1 := by
        intro s hs hEq
        have hObj : s = t := Subtype.ext hEq
        subst s
        exact htNot hs
      have hHeadPres :
          ∀ v ∈ t.branch.vertices, D v = E₁ v := by
        intro v hv
        have hv' :
            v ∈ (incidentBranch T r t.1 (Classical.choose t.2)).vertices := by
          simpa [RootTask.branch] using hv
        exact
          hUntouchedTail t.1 (Classical.choose t.2)
            hHeadNotTail v hv'
      have hClearedHead : t.branch.Cleared D := by
        intro v hv
        rw [hHeadPres v hv]
        exact hCleared₁ v hv
      have hClearedAll :
          ∀ s ∈ t :: ts, s.branch.Cleared D := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hClearedHead
        · exact hClearedTail s hs
      have hUntouchedAll :
          ∀ (u : V) (h : T.graph.Adj u r),
            (∀ s ∈ t :: ts, s.1 ≠ u) →
            ∀ v ∈ (incidentBranch T r u h).vertices, D v = E v := by
        intro u h hnot v hv
        have hnotHead : t.1 ≠ u :=
          hnot t (by simp)
        have hnotTail : ∀ s ∈ ts, s.1 ≠ u := by
          intro s hs
          exact hnot s (by simp [hs])
        have hOutside : v ∉ t.branch.carrier := by
          change
            v ∉ (incidentBranch T r t.1 (Classical.choose t.2)).carrier
          exact mem_incidentBranch_vertices_not_mem_sibling_carrier
            (T := T) r h (Classical.choose t.2) hnotHead.symm hv
        have hStep :=
          OrientedBranch.BranchReach.eq_of_not_mem_carrier
            t.branch hReachBranch hOutside
        calc
          D v = E₁ v := hUntouchedTail u h hnotTail v hv
          _ = E v := hStep
      exact ⟨D, hReachAll, hRootAll, hClearedAll, hUntouchedAll⟩

/-- Execute every occupied incident branch in the audited order.  The result
clears every non-root vertex and leaves exactly the rooted score at r. -/
theorem executeAllRootTasks
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hSafe :
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (C r : ℤ)
        (orderedTasks
          (fun t : RootTask T C r => t.gain)
          (rootTasks T C r))) :
    ∃ D : Configuration V,
      Reach T.graph C D ∧
      (D r : ℤ) = score T C r ∧
      (∀ v : V, v ≠ r → D v = 0) := by
  classical
  let gain : RootTask T C r → ℤ := fun t => t.gain
  let baseTasks : List (RootTask T C r) := rootTasks T C r
  let scheduled : List (RootTask T C r) :=
    orderedTasks gain baseTasks
  have hNodupBase : baseTasks.Nodup := by
    simpa [baseTasks] using rootTasks_nodup T C r
  have hNodupScheduled : scheduled.Nodup :=
    orderedTasks_nodup gain hNodupBase
  have hSame :
      ∀ t ∈ scheduled, ∀ v ∈ t.branch.vertices, C v = C v := by
    intro t ht v hv
    rfl
  have hSafe' :
      TaskScheduleSafe gain (C r : ℤ) scheduled := by
    simpa [gain, baseTasks, scheduled] using hSafe
  rcases executeRootTaskSchedule T C r
      scheduled C hNodupScheduled hSame hSafe' with
    ⟨D, hReach, hRoot, hCleared, hUntouched⟩
  have hRootScore : (D r : ℤ) = score T C r := by
    calc
      (D r : ℤ) =
          (C r : ℤ) + taskGainSum gain scheduled := hRoot
      _ = (C r : ℤ) + taskGainSum gain baseTasks := by
            change
              (C r : ℤ) +
                  taskGainSum gain (orderedTasks gain baseTasks) =
                (C r : ℤ) + taskGainSum gain baseTasks
            rw [taskGainSum_orderedTasks]
      _ = (C r : ℤ) + rootMessageSum T C r := by
            change
              (C r : ℤ) +
                  taskGainSum
                    (fun t : RootTask T C r => t.gain)
                    (rootTasks T C r) =
                (C r : ℤ) + rootMessageSum T C r
            rw [taskGainSum_rootTasks]
      _ = score T C r := rfl
  have hOffRoot : ∀ v : V, v ≠ r → D v = 0 := by
    intro v hvr
    rcases exists_incidentBranch_mem_of_ne_root (T := T) r hvr with
      ⟨u, h, hv⟩
    by_cases hOcc : (incidentBranch T r u h).Occupied C
    · let t : RootTask T C r := ⟨u, ⟨h, hOcc⟩⟩
      have htBase : t ∈ baseTasks := by
        simpa [baseTasks] using mem_rootTasks T C r t
      have htScheduled : t ∈ scheduled := by
        change t ∈ orderedTasks gain baseTasks
        exact (mem_orderedTasks_iff gain baseTasks t).2 htBase
      have htBranch :
          t.branch = incidentBranch T r u h := by
        exact t.branch_eq_incident h
      have htClear := hCleared t htScheduled
      rw [htBranch] at htClear
      exact htClear v hv
    · have hNoTask :
          ∀ t ∈ scheduled, t.1 ≠ u := by
        intro t ht hEq
        have htOcc := t.occupied
        have htBranch :
            t.branch = incidentBranch T r u h := by
          subst u
          exact t.branch_eq_incident h
        rw [htBranch] at htOcc
        exact hOcc htOcc
      have hPres : D v = C v :=
        hUntouched u h hNoTask v hv
      have hC0 : C v = 0 := by
        exact
          ((incidentBranch T r u h).not_occupied_iff_zero_on_vertices C).1
            hOcc v hv
      exact hPres.trans hC0
  exact ⟨D, hReach, hRootScore, hOffRoot⟩

/-- Positive rooted score gives an explicit legal stack at the chosen root. -/
theorem stackableAt_of_score_pos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hScore : 0 < score T C r) :
    StackableAt T.graph C r := by
  classical
  have hSafe :
      TaskScheduleSafe
        (fun t : RootTask T C r => t.gain)
        (C r : ℤ)
        (orderedTasks
          (fun t : RootTask T C r => t.gain)
          (rootTasks T C r)) := by
    apply orderedTasks_safe
    · positivity
    · rw [taskGainSum_rootTasks]
      simpa [score] using hScore
  rcases executeAllRootTasks T C r hSafe with
    ⟨D, hReach, hRoot, hOffRoot⟩
  refine ⟨D, hReach, ?_⟩
  constructor
  · have hPosZ : 0 < (D r : ℤ) := by
      rw [hRoot]
      exact hScore
    exact_mod_cast hPosZ
  · exact hOffRoot

/-- A global legal reach has an exact move-count signature.  Moreover, if an
oriented branch starts occupied and its outward boundary count is zero, then
that branch remains occupied. -/
theorem Reach.exists_moveSignature
    [DecidableEq V] {C D : Configuration V}
    (hreach : Reach T.graph C D) :
    ∃ m : MoveSignature T,
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (∀ A : OrientedBranch T,
        A.Occupied C →
        m.count A.root A.parent = 0 →
        A.Occupied D) := by
  induction hreach with
  | refl =>
      refine ⟨MoveSignature.zero T, ?_, ?_⟩
      · intro w
        simp
      · intro A hOcc hzero
        exact hOcc
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, rfl⟩
      rcases ih with ⟨m, hmBal, hmPersist⟩
      let m' : MoveSignature T := m.extend u v huv
      refine ⟨m', ?_, ?_⟩
      · intro w
        rw [OrientedBranch.move_balance_int _ huv.ne hlegal w, hmBal w]
        simp [m', MoveSignature.incoming_extend, MoveSignature.outgoing_extend]
        by_cases hwu : w = u <;> simp [hwu] <;> ring
      · intro A hOcc hzero
        have hmzero : m.count A.root A.parent = 0 := by
          have hle :
              m.count A.root A.parent ≤ m'.count A.root A.parent := by
            dsimp [m', MoveSignature.extend]
            omega
          omega
        rcases hmPersist A hOcc hmzero with ⟨w, hwA, hwpos⟩
        by_cases hvA : v ∈ A.vertices
        · refine ⟨v, hvA, ?_⟩
          simp [move]
        · have huA : u ∉ A.vertices := by
            intro huA
            have hEdge :=
              A.edge_leaving_vertices_eq_boundary huA hvA huv
            rw [Sym2.eq_iff] at hEdge
            rcases hEdge with h | h
            · rcases h with ⟨huRoot, hvParent⟩
              subst u
              subst v
              dsimp [m', MoveSignature.extend] at hzero
              simp at hzero
            · rcases h with ⟨huParent, hvRoot⟩
              subst u
              exact A.parent_not_mem_vertices huA
          have hwu : w ≠ u := by
            intro h
            subst w
            exact huA hwA
          have hwv : w ≠ v := by
            intro h
            subst w
            exact hvA hwA
          refine ⟨w, hwA, ?_⟩
          simpa [move, hwu, hwv] using hwpos


/-- Net signature flux into a candidate target, summed over all possible
neighbors. Nonedges contribute zero because every positive signature count is
supported on an actual tree edge. -/
noncomputable def rootSignatureFluxSum
    (m : MoveSignature T) (r : V) : ℤ :=
  ∑ u : V,
    ((m.count u r : ℤ) - 2 * (m.count r u : ℤ))

theorem rootSignatureFluxSum_eq
    (m : MoveSignature T) (r : V) :
    rootSignatureFluxSum m r =
      (m.incoming r : ℤ) - 2 * (m.outgoing r : ℤ) := by
  rw [rootSignatureFluxSum, MoveSignature.incoming, MoveSignature.outgoing]
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Any legal stack at r forces the rooted score to be positive. -/
theorem score_pos_of_stackableAt
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hStackable : StackableAt T.graph C r) :
    0 < score T C r := by
  classical
  rcases hStackable with ⟨D, hReach, hStack⟩
  rcases Reach.exists_moveSignature hReach with
    ⟨m, hmBal, hmPersist⟩
  have hTerm :
      ∀ u : V,
        (m.count u r : ℤ) - 2 * (m.count r u : ℤ) ≤
          rootMessageTerm T C r u := by
    intro u
    by_cases hAdj : T.graph.Adj u r
    · let B : OrientedBranch T := incidentBranch T r u hAdj
      have hClears : OrientedBranch.MoveSignature.Clears m C B := by
        intro w hw
        have hwr : w ≠ r := by
          intro hEq
          subst w
          exact B.parent_not_mem_vertices hw
        have hzero : D w = 0 := hStack.2 w hwr
        have hbal := hmBal w
        rw [hzero] at hbal
        simpa [MoveSignature.BalancesAt] using hbal.symm
      have hCausal :
          ∀ A : OrientedBranch T,
            A.vertices ⊆ B.vertices →
            A.Occupied C →
            OrientedBranch.MoveSignature.CausalOutward m A := by
        intro A hAB hOcc
        apply Nat.pos_of_ne_zero
        intro hzero
        rcases hmPersist A hOcc hzero with ⟨w, hwA, hwpos⟩
        have hwB : w ∈ B.vertices := hAB hwA
        have hwr : w ≠ r := by
          intro hEq
          subst w
          exact B.parent_not_mem_vertices hwB
        have hz : D w = 0 := hStack.2 w hwr
        rw [hz] at hwpos
        omega
      have hBounds :=
        OrientedBranch.signature_branchFlux_bounds
          m C B hClears hCausal
      have hFlux :
          (m.count u r : ℤ) - 2 * (m.count r u : ℤ) =
            OrientedBranch.MoveSignature.boundaryFlux m B := by
        rfl
      rw [hFlux]
      by_cases hOcc : B.Occupied C
      · have hBound := (hBounds.1 hOcc).1
        have hMsg :=
          OrientedBranch.branchMessage_eq_some_of_occupied C B hOcc
        have hTermEq :
            rootMessageTerm T C r u =
              F (OrientedBranch.effectiveInput C B) := by
          rw [rootMessageTerm]
          simp only [dif_pos hAdj]
          change
            OrientedBranch.messageContribution
                (OrientedBranch.branchMessage C B) =
              F (OrientedBranch.effectiveInput C B)
          rw [hMsg]
          rfl
        rw [hTermEq]
        exact hBound
      · rcases hBounds.2 hOcc with ⟨k, hk⟩
        have hMsg :=
          OrientedBranch.branchMessage_eq_empty_of_not_occupied C B hOcc
        have hTermZero : rootMessageTerm T C r u = 0 := by
          rw [rootMessageTerm]
          simp only [dif_pos hAdj]
          change
            OrientedBranch.messageContribution
                (OrientedBranch.branchMessage C B) = 0
          rw [hMsg]
          rfl
        rw [hTermZero, hk]
        omega
    · have hIn : m.count u r = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        exact hAdj (m.supported hpos)
      have hOut : m.count r u = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        exact hAdj (m.supported hpos).symm
      simp [rootMessageTerm, hAdj, hIn, hOut]
  have hFluxLe :
      rootSignatureFluxSum m r ≤ rootMessageSum T C r := by
    rw [rootSignatureFluxSum, rootMessageSum]
    exact Finset.sum_le_sum fun u _ => hTerm u
  have hRootBal := hmBal r
  have hDle : (D r : ℤ) ≤ score T C r := by
    calc
      (D r : ℤ) =
          (C r : ℤ) + (m.incoming r : ℤ) -
            2 * (m.outgoing r : ℤ) := hRootBal
      _ = (C r : ℤ) + rootSignatureFluxSum m r := by
            rw [rootSignatureFluxSum_eq]
            ring
      _ ≤ (C r : ℤ) + rootMessageSum T C r := by
            linarith
      _ = score T C r := rfl
  have hDpos : 0 < (D r : ℤ) := by
    exact_mod_cast hStack.1
  omega

/-- Exact rooted characterization: a configuration can be stacked at r
exactly when its recursive rooted score is positive. -/
theorem stackableAt_iff_score_pos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    StackableAt T.graph C r ↔ 0 < score T C r := by
  constructor
  · exact score_pos_of_stackableAt T C r
  · exact stackableAt_of_score_pos T C r

/-- Global non-stackability is equivalent to every rooted score being
nonpositive. -/
theorem not_stackable_iff_all_scores_nonpos
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) :
    ¬ Stackable T.graph C ↔ ∀ r : V, score T C r ≤ 0 := by
  rw [Stackable]
  push_neg
  constructor
  · intro h r
    have hn : ¬ 0 < score T C r := by
      intro hp
      exact h r ((stackableAt_iff_score_pos T C r).2 hp)
    omega
  · intro h r hs
    have hp := (stackableAt_iff_score_pos T C r).1 hs
    have hn := h r
    omega

end TreeStack

/- Source module: TreeStack.Obstruction.lean -/
namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The explicit rooted estimator obstruction: `sigma T r - 1` pebbles at
the selected root, one pebble at every other leaf, and zero elsewhere. -/
noncomputable def obstruction (T : FiniteTree V) (r : V) : Configuration V := by
  classical
  exact fun v =>
    if v = r then
      sigma T r - 1
    else if v ∈ leafVertices T r then
      1
    else
      0

@[simp] theorem obstruction_root (T : FiniteTree V) (r : V) :
    obstruction T r r = sigma T r - 1 := by
  simp [obstruction]

theorem obstruction_apply_ne (T : FiniteTree V) (r v : V) (hvr : v ≠ r) :
    obstruction T r v = if T.graph.degree v = 1 then 1 else 0 := by
  classical
  simp [obstruction, leafVertices, hvr]

theorem obstruction_leaf (T : FiniteTree V) (r v : V)
    (hvr : v ≠ r) (hdeg : T.graph.degree v = 1) :
    obstruction T r v = 1 := by
  simp [obstruction_apply_ne T r v hvr, hdeg]

theorem obstruction_internal (T : FiniteTree V) (r v : V)
    (hvr : v ≠ r) (hdeg : T.graph.degree v ≠ 1) :
    obstruction T r v = 0 := by
  simp [obstruction_apply_ne T r v hvr, hdeg]

/-- Exact mass of the explicit rooted obstruction. -/
theorem mass_obstruction (T : FiniteTree V) (r : V) :
    mass (obstruction T r) = rootEstimate T r - 1 := by
  classical
  have hsigma : 1 ≤ sigma T r := by
    simp [sigma]
  have hsum :
      ∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v =
        leafCount T r := by
    rw [leafCount]
    calc
      (∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v) =
          ∑ v ∈ (Finset.univ : Finset V).erase r,
            if v ∈ leafVertices T r then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro v hv
              have hvr : v ≠ r := by
                exact (Finset.mem_erase.mp hv).1
              simp [obstruction, hvr]
      _ = (((Finset.univ : Finset V).erase r).filter
            (fun v => v ∈ leafVertices T r)).card := by
              simpa using
                (Finset.sum_boole (R := ℕ)
                  (fun v : V => v ∈ leafVertices T r)
                  ((Finset.univ : Finset V).erase r))
      _ = (leafVertices T r).card := by
              congr 1
              ext v
              simp [leafVertices]
  rw [mass]
  calc
    (∑ v : V, obstruction T r v) =
        (∑ v ∈ (Finset.univ : Finset V).erase r, obstruction T r v) +
          obstruction T r r := by
            symm
            exact Finset.sum_erase_add (Finset.univ : Finset V)
              (obstruction T r) (Finset.mem_univ r)
    _ = leafCount T r + (sigma T r - 1) := by
          rw [hsum, obstruction_root]
    _ = rootEstimate T r - 1 := by
          rw [rootEstimate]
          omega

namespace OrientedBranch

/-- Recursive obstruction height on an oriented branch.  The recursion follows
exactly the genuine child branches used by `branchMessage`. -/
noncomputable def obstructionHeight (B : OrientedBranch T) : ℕ :=
  if hLeaf : T.graph.degree B.root = 1 then
    1
  else
    3 + 2 *
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt
    { vertex := v
      adj := h.1
      ne_parent := h.2 }

theorem obstructionHeight_leaf (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) :
    obstructionHeight B = 1 := by
  rw [obstructionHeight]
  simp [hLeaf]

theorem obstructionHeight_internal (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    obstructionHeight B =
      3 + 2 *
        ∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            obstructionHeight
              (B.childBranch
                { vertex := v
                  adj := h.1
                  ne_parent := h.2 })
          else
            0 := by
  rw [obstructionHeight]
  simp [show T.graph.degree B.root ≠ 1 by omega]

theorem obstructionHeight_pos (B : OrientedBranch T) :
    0 < obstructionHeight B := by
  rw [obstructionHeight]
  split_ifs <;> positivity


/-- A degree-one branch root has no genuine child besides its boundary parent. -/
theorem no_child_of_degree_one (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) (v : V) :
    ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by
  intro h
  have huniq :
      ∃! w : V, T.graph.Adj B.root w :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hLeaf
  exact h.2 (huniq.unique h.1 B.adj)

/-- An internal branch root has at least one genuine child. -/
theorem child_nonempty_of_internal (B : OrientedBranch T)
    (hInternal : 1 < T.graph.degree B.root) :
    Nonempty B.Child := by
  by_contra hnone
  have huniq : ∃! w : V, T.graph.Adj B.root w := by
    refine ⟨B.parent, B.adj, ?_⟩
    intro y hy
    by_contra hyne
    exact hnone
      ⟨{ vertex := y
         adj := hy
         ne_parent := hyne }⟩
  have hdeg :
      T.graph.degree B.root = 1 :=
    (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr huniq
  omega


/-- In a tree, every path is the unique shortest path between its endpoints. -/
theorem tree_path_length_eq_dist {u v : V} (p : T.graph.Walk u v)
    (hp : p.IsPath) :
    p.length = T.graph.dist u v := by
  obtain ⟨q, hq, hqdist⟩ :=
    T.isTree.connected.exists_path_of_dist u v
  have hEq :
      (⟨p, hp⟩ : T.graph.Path u v) =
        ⟨q, hq⟩ :=
    T.isTree.isAcyclic.subsingleton_path u v |>.elim _ _
  have hpq : p = q := congrArg Subtype.val hEq
  rw [hpq, hqdist]

/-- A degree-one oriented branch consists only of its root. -/
theorem vertices_eq_singleton_of_degree_one (B : OrientedBranch T)
    (hLeaf : T.graph.degree B.root = 1) :
    B.vertices = {B.root} := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    by_cases hxr : x = B.root
    · simpa [hxr]
    · rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
        ⟨c, hc⟩
      exact
        (B.no_child_of_degree_one hLeaf c.vertex
          ⟨c.adj, c.ne_parent⟩).elim
  · intro x hx
    have hxr : x = B.root := by
      simpa using hx
    subst x
    exact B.root_mem_vertices



/-- Every vertex of an oriented branch is one edge farther from the external
parent than from the branch root. -/
theorem dist_parent_eq_root_dist_add_one
    (B : OrientedBranch T) {x : V} (hx : x ∈ B.vertices) :
    T.graph.dist B.parent x =
      T.graph.dist B.root x + 1 := by
  classical
  have hrComp :
      B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hxComp :
      x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hreach :
      B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrComp hxComp
  obtain ⟨p₀, hp₀⟩ := hreach.exists_isPath
  have hle : B.deletedGraph ≤ T.graph := by
    intro a b hab
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hab
    exact hab.1
  let p : T.graph.Walk B.root x := p₀.mapLe hle
  have hp : p.IsPath := hp₀.mapLe hle
  have hparentNot : B.parent ∉ p.support := by
    intro hparent
    have hparent₀ : B.parent ∈ p₀.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hparent
    let q₀ := p₀.takeUntil B.parent hparent₀
    have hparentMem : B.parent ∈ B.vertices := by
      rw [vertices, Set.mem_toFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff, component]
      exact
        (SimpleGraph.ConnectedComponent.sound q₀.reachable).symm
    exact B.parent_not_mem_vertices hparentMem
  let q : T.graph.Walk B.parent x := p.cons B.adj.symm
  have hq : q.IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hp, hparentNot⟩
  have hpdist := tree_path_length_eq_dist (T := T) p hp
  have hqdist := tree_path_length_eq_dist (T := T) q hq
  simpa [q, p, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_mapLe, hpdist] using hqdist.symm

/-- Distances into a genuine child branch increase by exactly one when
measured from the parent-branch root. -/
theorem dist_root_eq_child_dist_add_one
    (B : OrientedBranch T) (c : B.Child) {x : V}
    (hx : x ∈ (B.childBranch c).vertices) :
    T.graph.dist B.root x =
      T.graph.dist c.vertex x + 1 := by
  simpa [childBranch] using
    (B.childBranch c).dist_parent_eq_root_dist_add_one hx

/-- Child choices form a finite type because a child is determined by its
underlying vertex. -/
noncomputable instance childFintype (B : OrientedBranch T) :
    Fintype B.Child :=
  Fintype.ofInjective
    (fun c : B.Child => c.vertex)
    (fun _ _ h => Child.eq_of_vertex_eq h)

/-- A child vertex, tagged by the unique genuine child branch containing it. -/
abbrev ChildVertex (B : OrientedBranch T) :=
  Σ c : B.Child, {x : V // x ∈ (B.childBranch c).vertices}

/-- The non-root vertices of an oriented branch. -/
abbrev ProperVertex (B : OrientedBranch T) :=
  {x : V // x ∈ B.vertices.erase B.root}

/-- The child branches partition the non-root vertices of an oriented branch. -/
noncomputable def childVertexEquivProper (B : OrientedBranch T) :
    B.ChildVertex ≃ B.ProperVertex := by
  classical
  have hnotRoot :
      ∀ (c : B.Child) {x : V},
        x ∈ (B.childBranch c).vertices → x ≠ B.root := by
    intro c x hx hxr
    apply (B.childBranch c).parent_not_mem_vertices
    simpa [childBranch, hxr] using hx
  let chosen : B.ProperVertex → B.Child := fun x =>
    Classical.choose
      (B.exists_childBranch_mem_of_mem_vertices_ne_root
        (Finset.mem_erase.mp x.2).2
        (by
          intro h
          exact (Finset.mem_erase.mp x.2).1 h))
  have hchosen :
      ∀ x : B.ProperVertex,
        x.1 ∈ (B.childBranch (chosen x)).vertices := by
    intro x
    exact
      Classical.choose_spec
        (B.exists_childBranch_mem_of_mem_vertices_ne_root
          (Finset.mem_erase.mp x.2).2
          (by
            intro h
            exact (Finset.mem_erase.mp x.2).1 h))
  refine
    { toFun := fun z =>
        ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨hnotRoot z.1 z.2.2,
              B.childBranch_vertices_subset z.1 z.2.2⟩⟩
      invFun := fun x =>
        ⟨chosen x, ⟨x.1, hchosen x⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let x : B.ProperVertex :=
      ⟨z.2.1,
        Finset.mem_erase.mpr
          ⟨hnotRoot z.1 z.2.2,
            B.childBranch_vertices_subset z.1 z.2.2⟩⟩
    have hc : chosen x = z.1 := by
      apply Child.eq_of_vertex_eq
      by_contra hne
      have hne' : z.1.vertex ≠ (chosen x).vertex := by
        intro h
        exact hne h.symm
      have hdisj :=
        B.childBranch_vertices_disjoint z.1 (chosen x) hne'
      exact
        (Finset.disjoint_left.mp hdisj) z.2.2 (hchosen x)
    apply Sigma.ext hc
    apply
      (Subtype.heq_iff_coe_eq
        (by
          intro y
          change
            y ∈ (B.childBranch (chosen x)).vertices ↔
              y ∈ (B.childBranch z.1).vertices
          rw [hc])).2
    rfl
  · intro x
    apply Subtype.ext
    rfl

/-- The finite set of genuine child vertices of an oriented branch. -/
noncomputable def childFinset (B : OrientedBranch T) : Finset V :=
  (T.graph.neighborFinset B.root).erase B.parent

@[simp] theorem mem_childFinset (B : OrientedBranch T) (v : V) :
    v ∈ B.childFinset ↔
      T.graph.Adj B.root v ∧ v ≠ B.parent := by
  classical
  simp [childFinset, and_left_comm, and_comm]

/-- A dependent sum over genuine child vertices agrees with the corresponding
sum over the finite child type. -/
theorem sum_dite_children {M : Type*} [AddCommMonoid M]
    (B : OrientedBranch T) (f : B.Child → M) :
    (∑ v : V,
      if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
        f { vertex := v, adj := h.1, ne_parent := h.2 }
      else
        0) =
      ∑ c : B.Child, f c := by
  classical
  let term : V → M := fun v =>
    if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
      f { vertex := v, adj := h.1, ne_parent := h.2 }
    else
      0
  have hrestrict :
      (∑ v ∈ B.childFinset, term v) =
        ∑ v : V, term v := by
    apply Finset.sum_subset (Finset.subset_univ B.childFinset)
    intro v hvUniv hvNot
    have hnot :
        ¬ (T.graph.Adj B.root v ∧ v ≠ B.parent) := by
      intro h
      exact hvNot ((B.mem_childFinset v).2 h)
    simp [term, hnot]
  rw [← hrestrict]
  change
    (∑ v ∈ B.childFinset, term v) =
      ∑ c ∈ (Finset.univ : Finset B.Child), f c
  apply Finset.sum_bij
    (fun v hv =>
      { vertex := v
        adj := ((B.mem_childFinset v).1 hv).1
        ne_parent := ((B.mem_childFinset v).1 hv).2 })
  · intro v hv
    exact Finset.mem_univ _
  · intro v₁ hv₁ v₂ hv₂ hEq
    exact congrArg Child.vertex hEq
  · intro c hc
    refine ⟨c.vertex, ?_, ?_⟩
    · exact (B.mem_childFinset c.vertex).2 ⟨c.adj, c.ne_parent⟩
    · apply Child.eq_of_vertex_eq
      rfl
  · intro v hv
    have h := (B.mem_childFinset v).1 hv
    simp [term, h]

/-- Summing over every child interior is exactly summing over the non-root
vertices of the parent branch. -/
theorem sum_childBranch_vertices (B : OrientedBranch T) (f : V → ℕ) :
    (∑ c : B.Child, ∑ x ∈ (B.childBranch c).vertices, f x) =
      ∑ x ∈ B.vertices.erase B.root, f x := by
  classical
  calc
    (∑ c : B.Child, ∑ x ∈ (B.childBranch c).vertices, f x) =
        ∑ c : B.Child,
          ∑ x : {x : V // x ∈ (B.childBranch c).vertices}, f x.1 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_subtype
              (B.childBranch c).vertices
              (fun _ => Iff.rfl) f]
    _ = ∑ z : B.ChildVertex, f z.2.1 := by
          rw [Fintype.sum_sigma]
    _ = ∑ x : B.ProperVertex, f x.1 := by
          exact
            Fintype.sum_equiv B.childVertexEquivProper
              (fun z : B.ChildVertex => f z.2.1)
              (fun x : B.ProperVertex => f x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ B.vertices.erase B.root, f x := by
          symm
          exact
            Finset.sum_subtype
              (B.vertices.erase B.root)
              (fun _ => Iff.rfl) f


/-- Weighted internal-vertex potential carried by an oriented branch. -/
noncomputable def internalPotential (B : OrientedBranch T) : ℕ :=
  ∑ x ∈ B.vertices,
    if 1 < T.graph.degree x then
      T.graph.degree x * 2 ^ T.graph.dist B.root x
    else
      0

theorem card_childFinset_add_one (B : OrientedBranch T) :
    B.childFinset.card + 1 = T.graph.degree B.root := by
  classical
  have hp : B.parent ∈ T.graph.neighborFinset B.root := by
    simpa using B.adj
  simpa [childFinset] using
    Finset.card_erase_add_one hp

/-- Doubling the total child potential exactly recovers the parent-rooted
potential of all non-root branch vertices. -/
theorem two_mul_sum_child_internalPotential (B : OrientedBranch T) :
    2 * (∑ c : B.Child, (B.childBranch c).internalPotential) =
      ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0 := by
  classical
  calc
    2 * (∑ c : B.Child, (B.childBranch c).internalPotential) =
        ∑ c : B.Child, 2 * (B.childBranch c).internalPotential := by
          rw [Finset.mul_sum]
    _ = ∑ c : B.Child,
        ∑ x ∈ (B.childBranch c).vertices,
          if 1 < T.graph.degree x then
            T.graph.degree x * 2 ^ T.graph.dist B.root x
          else
            0 := by
          apply Finset.sum_congr rfl
          intro c _
          rw [internalPotential, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hInt : 1 < T.graph.degree x
          · have hdist :=
              B.dist_root_eq_child_dist_add_one c hx
            simp [hInt, hdist, pow_succ]
            ring
          · simp [hInt]
    _ = ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0 := by
          exact
            B.sum_childBranch_vertices
              (fun x =>
                if 1 < T.graph.degree x then
                  T.graph.degree x * 2 ^ T.graph.dist B.root x
                else
                  0)


/-- Closed form for the recursive obstruction height. -/
theorem obstructionHeight_eq_one_add_two_mul_internalPotential
    (B : OrientedBranch T) :
    B.obstructionHeight = 1 + 2 * B.internalPotential := by
  classical
  by_cases hLeaf : T.graph.degree B.root = 1
  · rw [B.obstructionHeight_leaf hLeaf, internalPotential,
      B.vertices_eq_singleton_of_degree_one hLeaf]
    simp [hLeaf]
  · have hPos : 0 < T.graph.degree B.root := by
      rw [T.graph.degree_pos_iff_exists_adj B.root]
      exact ⟨B.parent, B.adj⟩
    have hInternal : 1 < T.graph.degree B.root := by
      omega
    let H : ℕ :=
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
    let P : ℕ :=
      ∑ c : B.Child, (B.childBranch c).internalPotential
    have hRec :
        H =
          ∑ v : V,
            if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
              1 + 2 *
                (B.childBranch
                  { vertex := v
                    adj := h.1
                    ne_parent := h.2 }).internalPotential
            else
              0 := by
      dsimp [H]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · simp [h,
          obstructionHeight_eq_one_add_two_mul_internalPotential
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })]
      · simp [h]
    have hCount :
        (∑ v : V,
          if T.graph.Adj B.root v ∧ v ≠ B.parent then
            (1 : ℕ)
          else
            0) =
          B.childFinset.card := by
      calc
        (∑ v : V,
          if T.graph.Adj B.root v ∧ v ≠ B.parent then
            (1 : ℕ)
          else
            0) =
            ((Finset.univ : Finset V).filter
              (fun v => T.graph.Adj B.root v ∧ v ≠ B.parent)).card := by
                simpa using
                  (Finset.sum_boole (R := ℕ)
                    (fun v : V =>
                      T.graph.Adj B.root v ∧ v ≠ B.parent)
                    (Finset.univ : Finset V))
        _ = B.childFinset.card := by
              congr 1
              ext v
              simp [childFinset, and_left_comm, and_comm]
    have hPSum :
        (∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 }).internalPotential
          else
            0) = P := by
      dsimp [P]
      exact
        B.sum_dite_children
          (fun c : B.Child => (B.childBranch c).internalPotential)
    have hH :
        H = B.childFinset.card + 2 * P := by
      rw [hRec]
      calc
        (∑ v : V,
          if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
            1 + 2 *
              (B.childBranch
                { vertex := v
                  adj := h.1
                  ne_parent := h.2 }).internalPotential
          else
            0) =
            (∑ v : V,
              if T.graph.Adj B.root v ∧ v ≠ B.parent then
                (1 : ℕ)
              else
                0) +
              2 *
                (∑ v : V,
                  if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
                    (B.childBranch
                      { vertex := v
                        adj := h.1
                        ne_parent := h.2 }).internalPotential
                  else
                    0) := by
                      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                      apply Finset.sum_congr rfl
                      intro v _
                      by_cases h :
                          T.graph.Adj B.root v ∧ v ≠ B.parent
                      · simp [h]
                      · simp [h]
        _ = B.childFinset.card + 2 * P := by
              rw [hCount, hPSum]
    let Q : ℕ :=
      ∑ x ∈ B.vertices.erase B.root,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0
    have hQ : 2 * P = Q := by
      dsimp [P, Q]
      exact B.two_mul_sum_child_internalPotential
    have hPot :
        B.internalPotential = Q + T.graph.degree B.root := by
      let weight : V → ℕ := fun x =>
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist B.root x
        else
          0
      rw [internalPotential]
      change
        (∑ x ∈ B.vertices, weight x) =
          Q + T.graph.degree B.root
      calc
        (∑ x ∈ B.vertices, weight x) =
            (∑ x ∈ B.vertices.erase B.root, weight x) +
              weight B.root := by
                symm
                exact
                  Finset.sum_erase_add B.vertices weight
                    B.root_mem_vertices
        _ = Q + T.graph.degree B.root := by
              dsimp [Q, weight]
              simp [hInternal]
    rw [B.obstructionHeight_internal hInternal]
    change 3 + 2 * H = 1 + 2 * B.internalPotential
    have hCard := B.card_childFinset_add_one
    omega
termination_by B.card
decreasing_by
  all_goals
    exact B.childBranch_card_lt _

/-- Every descendant branch of the selected root is occupied by the explicit
obstruction, and its exact recursive message is the negative obstruction
height.  The hypothesis says precisely that the selected root lies outside
the descendant-side component. -/
theorem obstruction_branchMessage (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices) :
    B.Occupied (obstruction T r) ∧
      branchMessage (obstruction T r) B =
        some (-(B.obstructionHeight : ℤ)) := by
  classical
  have hRootNe : B.root ≠ r := by
    intro h
    subst r
    exact hAway B.root_mem_vertices
  by_cases hLeaf : T.graph.degree B.root = 1
  · have hRoot :
        obstruction T r B.root = 1 :=
      obstruction_leaf T r B.root hRootNe hLeaf
    have hOcc : B.Occupied (obstruction T r) := by
      refine ⟨B.root, B.root_mem_vertices, ?_⟩
      rw [hRoot]
      omega
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ _ hOcc]
    have hEff :
        effectiveInput (obstruction T r) B = 1 := by
      rw [effectiveInput, childMessageSum]
      simp [hRoot, B.no_child_of_degree_one hLeaf]
    rw [hEff, B.obstructionHeight_leaf hLeaf]
    norm_num [F]
  · have hPos : 0 < T.graph.degree B.root := by
      rw [T.graph.degree_pos_iff_exists_adj B.root]
      exact ⟨B.parent, B.adj⟩
    have hInternal : 1 < T.graph.degree B.root := by
      omega
    have hRoot :
        obstruction T r B.root = 0 :=
      obstruction_internal T r B.root hRootNe hLeaf
    let H : ℕ :=
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
    have hChildSum :
        childMessageSum (obstruction T r) B = -(H : ℤ) := by
      rw [childMessageSum]
      dsimp [H]
      push_cast
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
      · let c : B.Child :=
          { vertex := v
            adj := h.1
            ne_parent := h.2 }
        have hAwayChild :
            r ∉ (B.childBranch c).vertices := by
          intro hr
          exact hAway (B.childBranch_vertices_subset c hr)
        have hRec :=
          obstruction_branchMessage r (B.childBranch c) hAwayChild
        simp [h, c, hRec.2]
      · simp [h]
    have hOcc : B.Occupied (obstruction T r) := by
      let c : B.Child := Classical.choice (B.child_nonempty_of_internal hInternal)
      have hAwayChild :
          r ∉ (B.childBranch c).vertices := by
        intro hr
        exact hAway (B.childBranch_vertices_subset c hr)
      have hRec :=
        obstruction_branchMessage r (B.childBranch c) hAwayChild
      rcases hRec.1 with ⟨w, hw, hpos⟩
      exact ⟨w, B.childBranch_vertices_subset c hw, hpos⟩
    refine ⟨hOcc, ?_⟩
    rw [branchMessage_eq_some_of_occupied _ _ hOcc]
    have hEff :
        effectiveInput (obstruction T r) B = -(H : ℤ) := by
      rw [effectiveInput, hRoot, hChildSum]
      simp
    rw [hEff]
    have hle : -(H : ℤ) ≤ 1 := by omega
    rw [F_of_le_one hle, B.obstructionHeight_internal hInternal]
    dsimp [H]
    push_cast
    ring_nf
termination_by B.card
decreasing_by
  all_goals
    exact B.childBranch_card_lt _


/-- The same tree edge with its orientation reversed. -/
def reverseBranch (B : OrientedBranch T) : OrientedBranch T where
  root := B.parent
  parent := B.root
  adj := B.adj.symm

@[simp] theorem reverseBranch_root (B : OrientedBranch T) :
    B.reverseBranch.root = B.parent := rfl

@[simp] theorem reverseBranch_parent (B : OrientedBranch T) :
    B.reverseBranch.parent = B.root := rfl

@[simp] theorem reverseBranch_reverse (B : OrientedBranch T) :
    B.reverseBranch.reverseBranch = B := by
  cases B
  rfl

/-- A rooted score at the root of an oriented branch splits into the branch's
effective input from its genuine children plus the message from the reverse
(parent-side) branch. -/
theorem score_eq_effectiveInput_add_reverse
    (C : Configuration V) (B : OrientedBranch T) :
    score T C B.root =
      B.effectiveInput C +
        messageContribution (branchMessage C B.reverseBranch) := by
  classical
  have hTerm (u : V) :
      rootMessageTerm T C B.root u =
        (if h : T.graph.Adj B.root u ∧ u ≠ B.parent then
          messageContribution
            (branchMessage C
              (B.childBranch
                { vertex := u
                  adj := h.1
                  ne_parent := h.2 }))
        else
          0) +
        if u = B.parent then
          messageContribution (branchMessage C B.reverseBranch)
        else
          0 := by
    by_cases hup : u = B.parent
    · subst u
      have hadj : T.graph.Adj B.parent B.root := B.adj.symm
      rw [rootMessageTerm]
      simp only [dif_pos hadj]
      simp only [ne_eq, not_true, and_false, dite_false, if_true, zero_add]
      congr 2
    · by_cases hadj : T.graph.Adj B.root u
      · have hadj' : T.graph.Adj u B.root := hadj.symm
        simp [rootMessageTerm, reverseBranch, incidentBranch, childBranch,
          hadj, hadj', hup]
      · have hadj' : ¬ T.graph.Adj u B.root := by
          intro h
          exact hadj h.symm
        simp [rootMessageTerm, hadj, hadj', hup]
  rw [score, rootMessageSum, effectiveInput, childMessageSum]
  simp_rw [hTerm]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- If an oriented branch is configuration-empty, its effective input is zero.
This does not identify the branch message with integer zero: its message is
still the separate value \`EMPTY\`. -/
theorem effectiveInput_eq_zero_of_not_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hEmpty : ¬ B.Occupied C) :
    B.effectiveInput C = 0 := by
  classical
  have hZero :=
    (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hRoot : C B.root = 0 :=
    hZero B.root B.root_mem_vertices
  rw [effectiveInput, childMessageSum, hRoot]
  simp only [Nat.cast_zero, zero_add]
  apply Finset.sum_eq_zero
  intro v hv
  by_cases h : T.graph.Adj B.root v ∧ v ≠ B.parent
  · let c : B.Child :=
      { vertex := v
        adj := h.1
        ne_parent := h.2 }
    have hChildEmpty : ¬ (B.childBranch c).Occupied C := by
      intro hOcc
      rcases hOcc with ⟨w, hw, hpos⟩
      exact hEmpty
        ⟨w, B.childBranch_vertices_subset c hw, hpos⟩
    rw [dif_pos h]
    change
      messageContribution
          (branchMessage C (B.childBranch c)) = 0
    rw [branchMessage_eq_empty_of_not_occupied C (B.childBranch c) hChildEmpty]
    rfl
  · simp [h]

/-- Zero score propagates from the parent of a descendant obstruction branch
to that branch root.  The proof uses the exact reverse-side effective input,
so no executable task is ever introduced for an empty branch. -/
theorem obstruction_score_root_of_parent_score_zero
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    score T (obstruction T r) B.root = 0 := by
  classical
  let C : Configuration V := obstruction T r
  let R : OrientedBranch T := B.reverseBranch
  have hData := obstruction_branchMessage r B hAway
  have hOccB : B.Occupied C := by
    simpa [C] using hData.1
  have hMsgB :
      branchMessage C B =
        some (-(B.obstructionHeight : ℤ)) := by
    simpa [C] using hData.2
  have hFEff :
      F (B.effectiveInput C) =
        -(B.obstructionHeight : ℤ) := by
    have hDef :=
      branchMessage_eq_some_of_occupied C B hOccB
    rw [hMsgB] at hDef
    exact Option.some.inj hDef.symm
  have hParentDecomp :
      score T C B.parent =
        R.effectiveInput C +
          messageContribution (branchMessage C R.reverseBranch) := by
    simpa [R] using score_eq_effectiveInput_add_reverse C R
  have hRevRev : R.reverseBranch = B := by
    simp [R]
  have hParentC : score T C B.parent = 0 := by
    simpa [C] using hParent
  have hEffR :
      R.effectiveInput C = (B.obstructionHeight : ℤ) := by
    rw [hParentC, hRevRev, hMsgB] at hParentDecomp
    simp only [messageContribution_some] at hParentDecomp
    linarith
  have hOccR : R.Occupied C := by
    by_contra hEmpty
    have hZero :=
      effectiveInput_eq_zero_of_not_occupied C R hEmpty
    rw [hZero] at hEffR
    have hPos : 0 < (B.obstructionHeight : ℤ) := by
      exact_mod_cast B.obstructionHeight_pos
    linarith
  have hMsgR :
      branchMessage C R =
        some (F (B.obstructionHeight : ℤ)) := by
    rw [branchMessage_eq_some_of_occupied C R hOccR, hEffR]
  have hRootDecomp :=
    score_eq_effectiveInput_add_reverse C B
  change
    score T C B.root =
      B.effectiveInput C +
        messageContribution (branchMessage C R) at hRootDecomp
  rw [hMsgR] at hRootDecomp
  simp only [messageContribution_some] at hRootDecomp
  by_cases hLeaf : T.graph.degree B.root = 1
  · have hHeight : B.obstructionHeight = 1 :=
      B.obstructionHeight_leaf hLeaf
    have hFEff' :
        F (B.effectiveInput C) = -(2 * (0 : ℤ) + 1) := by
      simpa [hHeight] using hFEff
    have hInput :
        B.effectiveInput C = 1 := by
      exact
        (F_eq_neg_odd_iff (z := B.effectiveInput C) (r := (0 : ℤ))
          (by omega)).1 hFEff'
    rw [hHeight] at hRootDecomp
    norm_num [F] at hRootDecomp
    linarith
  · have hPosDegree : 0 < T.graph.degree B.root := by
      rw [T.graph.degree_pos_iff_exists_adj B.root]
      exact ⟨B.parent, B.adj⟩
    have hInternal : 1 < T.graph.degree B.root := by
      omega
    let H : ℕ :=
      ∑ v : V,
        if h : T.graph.Adj B.root v ∧ v ≠ B.parent then
          obstructionHeight
            (B.childBranch
              { vertex := v
                adj := h.1
                ne_parent := h.2 })
        else
          0
    have hHeight :
        B.obstructionHeight = 3 + 2 * H := by
      simpa [H] using B.obstructionHeight_internal hInternal
    have hFEff' :
        F (B.effectiveInput C) =
          -(2 * ((H : ℤ) + 1) + 1) := by
      rw [hHeight] at hFEff
      push_cast at hFEff
      linarith
    have hInput :
        B.effectiveInput C = -(H : ℤ) := by
      have hInv :=
        (F_eq_neg_odd_iff
          (z := B.effectiveInput C)
          (r := (H : ℤ) + 1) (by positivity)).1 hFEff'
      linarith
    have hFHeight :
        F (B.obstructionHeight : ℤ) = (H : ℤ) := by
      apply
        (F_eq_nonneg_iff
          (z := (B.obstructionHeight : ℤ))
          (k := (H : ℤ)) (by positivity)).2
      right
      rw [hHeight]
      push_cast
      ring
    rw [hFHeight, hInput] at hRootDecomp
    linarith


end OrientedBranch

/-- A neighbor of a selected root, oriented toward that root. -/
abbrev RootNeighbor (T : FiniteTree V) (r : V) :=
  {u : V // T.graph.Adj u r}

namespace RootNeighbor

noncomputable def branch {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) : OrientedBranch T :=
  incidentBranch T r n.1 n.2

@[simp] theorem branch_root {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) :
    n.branch.root = n.1 := rfl

@[simp] theorem branch_parent {T : FiniteTree V} {r : V}
    (n : RootNeighbor T r) :
    n.branch.parent = r := rfl

end RootNeighbor

/-- A vertex tagged by the unique incident root branch containing it. -/
abbrev RootBranchVertex (T : FiniteTree V) (r : V) :=
  Σ n : RootNeighbor T r,
    {x : V // x ∈ n.branch.vertices}

/-- A non-root vertex. -/
abbrev RootProperVertex (r : V) :=
  {x : V // x ∈ (Finset.univ : Finset V).erase r}

/-- Incident branches at a root partition all vertices other than the root. -/
noncomputable def rootBranchVertexEquivProper
    (T : FiniteTree V) (r : V) :
    RootBranchVertex T r ≃ RootProperVertex r := by
  classical
  have hnotRoot :
      ∀ (n : RootNeighbor T r) {x : V},
        x ∈ n.branch.vertices → x ≠ r := by
    intro n x hx hxr
    apply n.branch.parent_not_mem_vertices
    simpa [RootNeighbor.branch, incidentBranch, hxr] using hx
  have hex :
      ∀ x : RootProperVertex r,
        ∃ n : RootNeighbor T r, x.1 ∈ n.branch.vertices := by
    intro x
    have hxr : x.1 ≠ r := (Finset.mem_erase.mp x.2).1
    rcases exists_incidentBranch_mem_of_ne_root (T := T) r hxr with
      ⟨u, h, hx⟩
    exact ⟨⟨u, h⟩, hx⟩
  let chosen : RootProperVertex r → RootNeighbor T r :=
    fun x => Classical.choose (hex x)
  have hchosen :
      ∀ x : RootProperVertex r,
        x.1 ∈ (chosen x).branch.vertices := by
    intro x
    exact Classical.choose_spec (hex x)
  refine
    { toFun := fun z =>
        ⟨z.2.1,
          Finset.mem_erase.mpr
            ⟨hnotRoot z.1 z.2.2, Finset.mem_univ _⟩⟩
      invFun := fun x =>
        ⟨chosen x, ⟨x.1, hchosen x⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let x : RootProperVertex r :=
      ⟨z.2.1,
        Finset.mem_erase.mpr
          ⟨hnotRoot z.1 z.2.2, Finset.mem_univ _⟩⟩
    have hn : chosen x = z.1 := by
      apply Subtype.ext
      by_contra hne
      have hne' : z.1.1 ≠ (chosen x).1 := by
        intro h
        exact hne h.symm
      have hdisj :=
        incidentBranch_vertices_disjoint
          (T := T) r z.1.2 (chosen x).2 hne'
      exact
        (Finset.disjoint_left.mp hdisj)
          z.2.2 (hchosen x)
    apply Sigma.ext hn
    apply
      (Subtype.heq_iff_coe_eq
        (by
          intro y
          change
            y ∈ (chosen x).branch.vertices ↔
              y ∈ z.1.branch.vertices
          rw [hn])).2
    rfl
  · intro x
    apply Subtype.ext
    rfl

/-- A dependent sum over root neighbors agrees with the corresponding sum over
the finite subtype of actual neighbors. -/
theorem sum_dite_rootNeighbors {M : Type*} [AddCommMonoid M]
    (T : FiniteTree V) (r : V) (f : RootNeighbor T r → M) :
    (∑ u : V,
      if h : T.graph.Adj u r then
        f ⟨u, h⟩
      else
        0) =
      ∑ n : RootNeighbor T r, f n := by
  classical
  let term : V → M := fun u =>
    if h : T.graph.Adj u r then f ⟨u, h⟩ else 0
  have hrestrict :
      (∑ u ∈ T.graph.neighborFinset r, term u) =
        ∑ u : V, term u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u huUniv huNot
    have hnot : ¬ T.graph.Adj u r := by
      intro h
      exact huNot (by simpa using h.symm)
    simp [term, hnot]
  rw [← hrestrict]
  change
    (∑ u ∈ T.graph.neighborFinset r, term u) =
      ∑ n ∈ (Finset.univ : Finset (RootNeighbor T r)), f n
  apply Finset.sum_bij
    (fun u hu =>
      ⟨u, by simpa using
        ((T.graph.mem_neighborFinset r u).mp hu).symm⟩)
  · intro u hu
    exact Finset.mem_univ _
  · intro u₁ hu₁ u₂ hu₂ hEq
    exact congrArg Subtype.val hEq
  · intro n hn
    refine ⟨n.1, ?_, ?_⟩
    · exact (T.graph.mem_neighborFinset r n.1).mpr n.2.symm
    · apply Subtype.ext
      rfl
  · intro u hu
    have h : T.graph.Adj u r := by
      simpa using ((T.graph.mem_neighborFinset r u).mp hu).symm
    simp [term, h]

/-- The number of root neighbors is the degree of the root. -/
theorem card_rootNeighbor (T : FiniteTree V) (r : V) :
    Fintype.card (RootNeighbor T r) = T.graph.degree r := by
  classical
  calc
    Fintype.card (RootNeighbor T r) =
        ∑ _n : RootNeighbor T r, (1 : ℕ) := by simp
    _ = ∑ u : V,
        if T.graph.Adj u r then (1 : ℕ) else 0 := by
          symm
          simpa using
            sum_dite_rootNeighbors T r
              (fun _ : RootNeighbor T r => (1 : ℕ))
    _ = T.graph.degree r := by
          simpa [T.graph.adj_comm] using
            (T.graph.degree_eq_sum_if_adj (R := ℕ) r).symm

/-- Summing over all incident branch interiors is exactly summing over all
non-root vertices. -/
theorem sum_rootBranch_vertices
    (T : FiniteTree V) (r : V) (f : V → ℕ) :
    (∑ n : RootNeighbor T r, ∑ x ∈ n.branch.vertices, f x) =
      ∑ x ∈ (Finset.univ : Finset V).erase r, f x := by
  classical
  calc
    (∑ n : RootNeighbor T r, ∑ x ∈ n.branch.vertices, f x) =
        ∑ n : RootNeighbor T r,
          ∑ x : {x : V // x ∈ n.branch.vertices}, f x.1 := by
            apply Finset.sum_congr rfl
            intro n _
            rw [Finset.sum_subtype
              n.branch.vertices
              (fun _ => Iff.rfl) f]
    _ = ∑ z : RootBranchVertex T r, f z.2.1 := by
          rw [Fintype.sum_sigma]
    _ = ∑ x : RootProperVertex r, f x.1 := by
          exact
            Fintype.sum_equiv
              (rootBranchVertexEquivProper T r)
              (fun z : RootBranchVertex T r => f z.2.1)
              (fun x : RootProperVertex r => f x.1)
              (fun _ => rfl)
    _ = ∑ x ∈ (Finset.univ : Finset V).erase r, f x := by
          symm
          exact
            Finset.sum_subtype
              ((Finset.univ : Finset V).erase r)
              (fun _ => Iff.rfl) f

/-- Doubling all incident branch potentials recovers the root-distance
potential of every non-root internal vertex. -/
theorem two_mul_sum_root_internalPotential
    (T : FiniteTree V) (r : V) :
    2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) =
      ∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0 := by
  classical
  calc
    2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) =
        ∑ n : RootNeighbor T r, 2 * n.branch.internalPotential := by
          rw [Finset.mul_sum]
    _ = ∑ n : RootNeighbor T r,
        ∑ x ∈ n.branch.vertices,
          if 1 < T.graph.degree x then
            T.graph.degree x * 2 ^ T.graph.dist r x
          else
            0 := by
          apply Finset.sum_congr rfl
          intro n _
          rw [OrientedBranch.internalPotential, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hInt : 1 < T.graph.degree x
          · have hdist :=
              n.branch.dist_parent_eq_root_dist_add_one hx
            simp [RootNeighbor.branch, hInt] at hdist ⊢
            rw [hdist, pow_succ]
            ring
          · simp [hInt]
    _ = ∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0 := by
          exact
            sum_rootBranch_vertices T r
              (fun x =>
                if 1 < T.graph.degree x then
                  T.graph.degree x * 2 ^ T.graph.dist r x
                else
                  0)

/-- The incident obstruction heights at a selected root sum to exactly
\`sigma T r - 1\`. -/
theorem sum_root_obstructionHeight_eq_sigma_sub_one
    (T : FiniteTree V) (r : V) :
    (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
      sigma T r - 1 := by
  classical
  have hHeights :
      (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
        Fintype.card (RootNeighbor T r) +
          2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) := by
    calc
      (∑ n : RootNeighbor T r, n.branch.obstructionHeight) =
          ∑ n : RootNeighbor T r,
            (1 + 2 * n.branch.internalPotential) := by
              apply Finset.sum_congr rfl
              intro n _
              rw [OrientedBranch.obstructionHeight_eq_one_add_two_mul_internalPotential]
      _ = Fintype.card (RootNeighbor T r) +
          2 * (∑ n : RootNeighbor T r, n.branch.internalPotential) := by
            rw [Finset.sum_add_distrib]
            simp [← Finset.mul_sum]
  have hPotential :=
    two_mul_sum_root_internalPotential T r
  have hInternal :
      (∑ x ∈ (Finset.univ : Finset V).erase r,
        if 1 < T.graph.degree x then
          T.graph.degree x * 2 ^ T.graph.dist r x
        else
          0) =
        ∑ x ∈ nonRootInternalVertices T r,
          T.graph.degree x * 2 ^ T.graph.dist r x := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [nonRootInternalVertices, and_left_comm, and_comm]
  rw [hHeights, card_rootNeighbor T r, hPotential, hInternal,
    sigma_corrected_expansion]
  omega

/-- At the selected root itself, the obstruction score is exactly zero. -/
theorem obstruction_score_selected_root
    (T : FiniteTree V) (r : V) :
    score T (obstruction T r) r = 0 := by
  classical
  have hTerms :
      rootMessageSum T (obstruction T r) r =
        -((sigma T r - 1 : ℕ) : ℤ) := by
    rw [rootMessageSum]
    calc
      (∑ u : V, rootMessageTerm T (obstruction T r) r u) =
          ∑ u : V,
            if h : T.graph.Adj u r then
              -((incidentBranch T r u h).obstructionHeight : ℤ)
            else
              0 := by
                apply Finset.sum_congr rfl
                intro u _
                by_cases h : T.graph.Adj u r
                · let B : OrientedBranch T := incidentBranch T r u h
                  have hAway : r ∉ B.vertices := by
                    simpa [B, incidentBranch] using B.parent_not_mem_vertices
                  have hMsg :=
                    (B.obstruction_branchMessage r hAway).2
                  simp [rootMessageTerm, h, B, hMsg]
                · simp [rootMessageTerm, h]
      _ = ∑ n : RootNeighbor T r,
            -((n.branch.obstructionHeight : ℕ) : ℤ) := by
              exact
                sum_dite_rootNeighbors T r
                  (fun n : RootNeighbor T r =>
                    -((n.branch.obstructionHeight : ℕ) : ℤ))
      _ = -((∑ n : RootNeighbor T r,
            n.branch.obstructionHeight : ℕ) : ℤ) := by
              push_cast
              rw [Finset.sum_neg_distrib]
      _ = -((sigma T r - 1 : ℕ) : ℤ) := by
              rw [sum_root_obstructionHeight_eq_sigma_sub_one]
  rw [score, obstruction_root, hTerms]
  ring


namespace OrientedBranch

/-- Once the parent score is zero, zero score propagates recursively through
every vertex of a descendant obstruction branch. -/
theorem obstruction_scores_zero_on_vertices
    (r : V) (B : OrientedBranch T)
    (hAway : r ∉ B.vertices)
    (hParent :
      score T (obstruction T r) B.parent = 0) :
    ∀ x ∈ B.vertices,
      score T (obstruction T r) x = 0 := by
  classical
  have hRoot :
      score T (obstruction T r) B.root = 0 :=
    B.obstruction_score_root_of_parent_score_zero r hAway hParent
  intro x hx
  by_cases hxr : x = B.root
  · subst x
    exact hRoot
  · rcases
      B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
      ⟨c, hxc⟩
    have hAwayChild :
        r ∉ (B.childBranch c).vertices := by
      intro hr
      exact hAway (B.childBranch_vertices_subset c hr)
    exact
      obstruction_scores_zero_on_vertices
        r (B.childBranch c) hAwayChild hRoot x hxc
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt _

end OrientedBranch

/-- Every rooted score of the explicit estimator obstruction is exactly zero. -/
theorem obstruction_score_eq_zero
    (T : FiniteTree V) (r v : V) :
    score T (obstruction T r) v = 0 := by
  classical
  by_cases hvr : v = r
  · subst v
    exact obstruction_score_selected_root T r
  · rcases
      exists_incidentBranch_mem_of_ne_root (T := T) r hvr with
      ⟨u, h, hv⟩
    let B : OrientedBranch T := incidentBranch T r u h
    have hAway : r ∉ B.vertices := by
      simpa [B, incidentBranch] using B.parent_not_mem_vertices
    have hRoot :
        score T (obstruction T r) r = 0 :=
      obstruction_score_selected_root T r
    exact
      B.obstruction_scores_zero_on_vertices r hAway hRoot v
        (by simpa [B] using hv)

/-- The explicit obstruction is globally non-stackable. -/
theorem obstruction_not_stackable
    (T : FiniteTree V) (r : V) :
    ¬ Stackable T.graph (obstruction T r) := by
  classical
  apply
    (not_stackable_iff_all_scores_nonpos
      T (obstruction T r)).2
  intro v
  rw [obstruction_score_eq_zero T r v]

/-- The finite maximum defining the estimator is attained by some root. -/
theorem exists_rootEstimate_eq_estim
    (T : FiniteTree V) :
    ∃ r : V, rootEstimate T r = estim T := by
  classical
  have hnon :
      (Finset.univ : Finset V).Nonempty :=
    ⟨T.isTree.connected.nonempty.some, Finset.mem_univ _⟩
  have hmem :=
    Finset.sup_mem_of_nonempty
      (s := (Finset.univ : Finset V))
      (f := rootEstimate T) hnon
  rcases hmem with ⟨r, hr, hEq⟩
  refine ⟨r, ?_⟩
  simpa [estim] using hEq

/-- At an estimator-maximizing root there is a non-stackable configuration of
exactly \`estim T - 1\` pebbles. -/
theorem exists_nonstackable_mass_estim_sub_one
    [Nontrivial V] (T : FiniteTree V) :
    ∃ C : Configuration V,
      mass C = estim T - 1 ∧
        ¬ Stackable T.graph C := by
  classical
  rcases exists_rootEstimate_eq_estim T with ⟨r, hr⟩
  refine ⟨obstruction T r, ?_, obstruction_not_stackable T r⟩
  rw [mass_obstruction T r, hr]

end TreeStack

/- Source module: TreeStack.Defect.lean -/
namespace TreeStack

/-- If the message from `u` to `v` is nonnegative, then the reverse
message is forced negative and the tail defect is either exactly twice the
head defect or three more than twice the head defect.  The latter alternative
requires a strictly positive forward message. -/
theorem defect_left_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3)) := by
  have hinB : -δv - a ≤ 1 := by
    omega
  have hb' : b = 2 * (-δv - a) - 3 := by
    simpa only [F_of_le_one hinB] using hb
  have hpre :
      (0 < a ∧ -δu - b = 2 * a) ∨
        -δu - b = 2 * a + 3 := by
    exact
      (F_eq_nonneg_iff
        (z := -δu - b) (k := a) ha0).1 ha.symm
  refine ⟨?_, ?_⟩
  · omega
  · rcases hpre with hpre | hpre
    · right
      exact ⟨hpre.1, by omega⟩
    · left
      omega

/-- Symmetric form of `defect_left_nonneg`. -/
theorem defect_right_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (hb0 : 0 ≤ b) :
    a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3)) := by
  simpa using
    (defect_left_nonneg
      (a := b) (b := a) (δu := δv) (δv := δu)
      hδv hδu hb ha hb0)

/-- Under nonnegative endpoint defects, both edge messages cannot be
nonnegative simultaneously. -/
theorem defect_not_both_nonneg
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    ¬ (0 ≤ a ∧ 0 ≤ b) := by
  intro hboth
  have h :=
    defect_left_nonneg hδu hδv ha hb hboth.1
  omega

/-- When both edge messages are negative, they are uniquely of odd negative
form and the two endpoint defects are the corresponding linear combinations. -/
theorem defect_two_negative
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (haNeg : a < 0) (hbNeg : b < 0) :
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r := by
  have hFaNeg : F (-δu - b) < 0 := by
    simpa [ha] using haNeg
  have hFbNeg : F (-δv - a) < 0 := by
    simpa [hb] using hbNeg
  have hinA : -δu - b ≤ 1 :=
    (F_neg_iff (-δu - b)).1 hFaNeg
  have hinB : -δv - a ≤ 1 :=
    (F_neg_iff (-δv - a)).1 hFbNeg
  have ha' : a = 2 * (-δu - b) - 3 := by
    simpa only [F_of_le_one hinA] using ha
  have hb' : b = 2 * (-δv - a) - 3 := by
    simpa only [F_of_le_one hinB] using hb
  let r : ℤ := 1 + δu + b
  let q : ℤ := 1 + δv + a
  have har : a = -(2 * r + 1) := by
    dsimp [r]
    omega
  have hbq : b = -(2 * q + 1) := by
    dsimp [q]
    omega
  have hr : 0 ≤ r := by
    rw [har] at haNeg
    omega
  have hq : 0 ≤ q := by
    rw [hbq] at hbNeg
    omega
  refine ⟨r, q, hr, hq, har, hbq, ?_, ?_⟩
  · dsimp [r, q]
    omega
  · dsimp [r, q]
    omega

/-- Exhaustive arbitrary-defect classification for the two integer messages
across a genuine edge.  This is the local algebraic core used by the global
defect-flow upper-bound argument. -/
theorem defect_edge_classification
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    (0 ≤ a ∧
      b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3))) ∨
    (0 ≤ b ∧
      a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3))) ∨
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r := by
  by_cases ha0 : 0 ≤ a
  · left
    exact ⟨ha0, defect_left_nonneg hδu hδv ha hb ha0⟩
  · have haNeg : a < 0 := by
      omega
    by_cases hb0 : 0 ≤ b
    · right
      left
      exact ⟨hb0, defect_right_nonneg hδu hδv ha hb hb0⟩
    · have hbNeg : b < 0 := by
        omega
      right
      right
      exact defect_two_negative hδu hδv ha hb haNeg hbNeg

/-- In the oriented case, the tail defect always has enough budget to pay
twice the head defect. -/
theorem defect_left_budget
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    2 * δv ≤ δu := by
  rcases (defect_left_nonneg hδu hδv ha hb ha0).2 with h | h
  · omega
  · omega

/-- Symmetric tail-budget inequality. -/
theorem defect_right_budget
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (hb0 : 0 ≤ b) :
    2 * δu ≤ δv := by
  simpa using
    (defect_left_budget
      (a := b) (b := a) (δu := δv) (δv := δu)
      hδv hδu hb ha hb0)


/-- The nonnegative defect attached to a nonpositive rooted score. -/
noncomputable def scoreDefect
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (v : V) : ℤ :=
  -score T C v

@[simp] theorem scoreDefect_nonneg_iff
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (v : V) :
    0 ≤ scoreDefect T C v ↔ score T C v ≤ 0 := by
  simp [scoreDefect]

/-- Reusable predicate packaging the exhaustive local defect-edge states. -/
def DefectEdgeState (a b δu δv : ℤ) : Prop :=
  (0 ≤ a ∧
      b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3))) ∨
    (0 ≤ b ∧
      a = -2 * (b + δu) - 3 ∧
      (δv = 2 * δu ∨
        (0 < b ∧ δv = 2 * δu + 3))) ∨
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      a = -(2 * r + 1) ∧
      b = -(2 * q + 1) ∧
      δu = r + 2 * q ∧
      δv = q + 2 * r

theorem defectEdgeState_of_equations
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a)) :
    DefectEdgeState a b δu δv := by
  simpa [DefectEdgeState] using
    (defect_edge_classification hδu hδv ha hb)

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- On an edge whose two sides are both occupied, the actual recursive branch
messages satisfy exactly the abstract defect equations used by the global
defect-flow argument. -/
theorem defect_equations_of_both_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hB : B.Occupied C)
    (hR : B.reverseBranch.Occupied C) :
    let a :=
      messageContribution (branchMessage C B)
    let b :=
      messageContribution (branchMessage C B.reverseBranch)
    let δu := scoreDefect T C B.root
    let δv := scoreDefect T C B.parent
    a = F (-δu - b) ∧
      b = F (-δv - a) := by
  dsimp
  have hMsgB :=
    branchMessage_eq_some_of_occupied C B hB
  have hMsgR :=
    branchMessage_eq_some_of_occupied C B.reverseBranch hR
  have hScoreB :
      score T C B.root =
        B.effectiveInput C +
          F (B.reverseBranch.effectiveInput C) := by
    simpa [hMsgR] using
      (score_eq_effectiveInput_add_reverse C B)
  have hScoreR :
      score T C B.parent =
        B.reverseBranch.effectiveInput C +
          F (B.effectiveInput C) := by
    have h :=
      score_eq_effectiveInput_add_reverse C B.reverseBranch
    simpa [hMsgB] using h
  simp only [scoreDefect, hMsgB, hMsgR,
    messageContribution_some, neg_neg]
  constructor
  · congr 1
    omega
  · congr 1
    omega

/-- Concrete TreeStack form of the arbitrary-defect edge classification:
for an edge with occupied support on both sides and nonpositive endpoint
scores, its two recursive messages lie in one of the exhaustive defect states. -/
theorem defectEdgeState_of_scores_nonpos
    (C : Configuration V) (B : OrientedBranch T)
    (hB : B.Occupied C)
    (hR : B.reverseBranch.Occupied C)
    (hRoot : score T C B.root ≤ 0)
    (hParent : score T C B.parent ≤ 0) :
    DefectEdgeState
      (messageContribution (branchMessage C B))
      (messageContribution (branchMessage C B.reverseBranch))
      (scoreDefect T C B.root)
      (scoreDefect T C B.parent) := by
  have hEq :=
    B.defect_equations_of_both_occupied C hB hR
  apply defectEdgeState_of_equations
  · exact (scoreDefect_nonneg_iff T C B.root).2 hRoot
  · exact (scoreDefect_nonneg_iff T C B.parent).2 hParent
  · exact hEq.1
  · exact hEq.2

end OrientedBranch

end TreeStack

/- Source module: TreeStack.Support.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The two orientations of a tree edge determine disjoint vertex sides. -/
theorem vertices_disjoint_reverseBranch (B : OrientedBranch T) :
    Disjoint B.vertices B.reverseBranch.vertices := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hxR
  have hxComp : x ∈ B.component.supp := by
    simpa [vertices] using hx
  have hrootComp : B.root ∈ B.component.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrootx : B.deletedGraph.Reachable B.root x :=
    B.component.reachable_of_mem_supp hrootComp hxComp
  have hxRComp : x ∈ B.reverseBranch.component.supp := by
    simpa [vertices] using hxR
  have hparentComp : B.parent ∈ B.reverseBranch.component.supp := by
    have hroot := B.reverseBranch.root_mem_vertices
    simpa [vertices] using hroot
  have hparentxR :
      B.reverseBranch.deletedGraph.Reachable B.parent x :=
    B.reverseBranch.component.reachable_of_mem_supp hparentComp hxRComp
  have hparentx : B.deletedGraph.Reachable B.parent x := by
    change
      (T.graph.deleteEdges {s(B.root, B.parent)}).Reachable B.parent x
    rw [Sym2.eq_swap]
    simpa [deletedGraph, reverseBranch] using hparentxR
  have hreach : B.deletedGraph.Reachable B.root B.parent :=
    hrootx.trans hparentx.symm
  have hbridge : T.graph.IsBridge s(B.root, B.parent) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      T.isTree.isAcyclic) B.adj
  exact (SimpleGraph.isBridge_iff.mp hbridge) (by
    simpa [deletedGraph] using hreach)

/-- Every vertex lies on one of the two sides of an oriented tree edge. -/
theorem mem_vertices_or_mem_reverseBranch
    (B : OrientedBranch T) (x : V) :
    x ∈ B.vertices ∨ x ∈ B.reverseBranch.vertices := by
  classical
  by_cases hxr : x = B.root
  · left
    simpa [hxr] using B.root_mem_vertices
  · rcases exists_incidentBranch_mem_of_ne_root (T := T) B.root hxr with
      ⟨u, hu, hx⟩
    by_cases hup : u = B.parent
    · right
      subst u
      simpa [reverseBranch, incidentBranch] using hx
    · left
      let c : B.Child :=
        { vertex := u
          adj := hu.symm
          ne_parent := hup }
      have hxChild : x ∈ (B.childBranch c).vertices := by
        simpa [c, childBranch, incidentBranch] using hx
      exact B.childBranch_vertices_subset c hxChild

/-- The two edge sides partition the whole finite vertex type. -/
theorem vertices_union_reverseBranch (B : OrientedBranch T) :
    B.vertices ∪ B.reverseBranch.vertices = (Finset.univ : Finset V) := by
  classical
  ext x
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  exact B.mem_vertices_or_mem_reverseBranch x

/-- At least one edge side is occupied as soon as the configuration has a
positive pile somewhere. -/
theorem occupied_or_reverse_occupied
    (C : Configuration V) (B : OrientedBranch T)
    {x : V} (hx : 0 < C x) :
    B.Occupied C ∨ B.reverseBranch.Occupied C := by
  rcases B.mem_vertices_or_mem_reverseBranch x with hxB | hxR
  · exact Or.inl ⟨x, hxB, hx⟩
  · exact Or.inr ⟨x, hxR, hx⟩

/-- A retained support edge is a tree edge with occupied configuration support
on both sides.  This is the in-place substitute for transporting the whole
problem to a subtype-valued minimal support tree. -/
def SupportEdge (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.Occupied C ∧ B.reverseBranch.Occupied C

@[simp] theorem supportEdge_reverse_iff
    (C : Configuration V) (B : OrientedBranch T) :
    B.reverseBranch.SupportEdge C ↔ B.SupportEdge C := by
  simp [SupportEdge, and_comm]


/-- The occupied exterior side of a retained edge lies on the reverse side of
every genuine child edge.  This is the one-step separation fact that makes the
retained support core path-closed without changing the ambient vertex type. -/
theorem reverse_child_occupied_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).reverseBranch.Occupied C := by
  rcases hEdge.2 with ⟨y, hyReverseB, hyPos⟩
  have hyNotChild : y ∉ (B.childBranch c).vertices := by
    intro hyChild
    have hyB : y ∈ B.vertices :=
      B.childBranch_vertices_subset c hyChild
    exact
      (Finset.disjoint_left.mp B.vertices_disjoint_reverseBranch)
        hyB hyReverseB
  rcases (B.childBranch c).mem_vertices_or_mem_reverseBranch y with
    hyChild | hyReverseChild
  · exact (hyNotChild hyChild).elim
  · exact ⟨y, hyReverseChild, hyPos⟩

/-- Below a retained support edge, a genuine child edge is retained exactly
when its child branch contains positive support.  The occupied reverse side is
supplied by the exterior witness of the parent retained edge. -/
theorem child_supportEdge_iff_occupied_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (c : B.Child) :
    (B.childBranch c).SupportEdge C ↔
      (B.childBranch c).Occupied C := by
  constructor
  · intro hChild
    exact hChild.1
  · intro hChildOcc
    exact
      ⟨hChildOcc,
        B.reverse_child_occupied_of_supportEdge C hEdge c⟩

/-- A rooted certificate that a vertex is reached from an oriented-branch root
by descending only through retained support edges.  It is an in-place path
object for the minimal support core. -/
inductive SupportDescent (C : Configuration V) :
    (B : OrientedBranch T) → V → Prop
  | root (B : OrientedBranch T) :
      SupportDescent C B B.root
  | child (B : OrientedBranch T) (c : B.Child) {x : V}
      (hEdge : (B.childBranch c).SupportEdge C)
      (hTail : SupportDescent C (B.childBranch c) x) :
      SupportDescent C B x

/-- Every positive-support vertex on the root side of a retained edge is joined
to the edge root by a descent consisting entirely of retained support edges.
This is the rooted path-closure form of connectedness of the minimal support
subtree. -/
theorem supportDescent_of_mem_pos
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) {x : V}
    (hx : x ∈ B.vertices) (hxPos : 0 < C x) :
    SupportDescent C B x := by
  classical
  by_cases hxr : x = B.root
  · subst x
    exact SupportDescent.root B
  · rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hx hxr with
      ⟨c, hxChild⟩
    have hChildOcc : (B.childBranch c).Occupied C :=
      ⟨x, hxChild, hxPos⟩
    have hChildEdge : (B.childBranch c).SupportEdge C :=
      (B.child_supportEdge_iff_occupied_of_supportEdge C hEdge c).2 hChildOcc
    exact
      SupportDescent.child B c hChildEdge
        (supportDescent_of_mem_pos
          C (B.childBranch c) hChildEdge hxChild hxPos)
termination_by B.card
decreasing_by
  exact B.childBranch_card_lt _

/-- If the root of a retained edge is not itself occupied, some retained child
edge continues the support core. -/
theorem exists_child_supportEdge_of_supportEdge_of_root_not_pos
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) (hRoot : ¬ 0 < C B.root) :
    ∃ c : B.Child, (B.childBranch c).SupportEdge C := by
  rcases hEdge.1 with ⟨x, hxB, hxPos⟩
  have hxNe : x ≠ B.root := by
    intro hxr
    subst x
    exact hRoot hxPos
  rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hxB hxNe with
    ⟨c, hxChild⟩
  refine ⟨c, ?_⟩
  exact
    (B.child_supportEdge_iff_occupied_of_supportEdge C hEdge c).2
      ⟨x, hxChild, hxPos⟩


/-- If an edge is retained by the support core and there is no retained child
edge at its root, then that root is occupied.  This is the in-place form of
the statement that every leaf of the minimal connected support subtree is
occupied. -/
theorem root_pos_of_supportEdge_of_no_child_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hNoChild : ∀ c : B.Child, ¬ (B.childBranch c).SupportEdge C) :
    0 < C B.root := by
  classical
  by_contra hRootPos
  have hRootZero : C B.root = 0 := Nat.eq_zero_of_not_pos hRootPos
  rcases hEdge.1 with ⟨x, hxB, hxPos⟩
  have hxNe : x ≠ B.root := by
    intro hxr
    subst x
    simp [hRootZero] at hxPos
  rcases B.exists_childBranch_mem_of_mem_vertices_ne_root hxB hxNe with
    ⟨c, hxChild⟩
  have hChildOcc : (B.childBranch c).Occupied C :=
    ⟨x, hxChild, hxPos⟩
  rcases hEdge.2 with ⟨y, hyReverseB, hyPos⟩
  have hyNotChild : y ∉ (B.childBranch c).vertices := by
    intro hyChild
    have hyB : y ∈ B.vertices :=
      B.childBranch_vertices_subset c hyChild
    exact
      (Finset.disjoint_left.mp B.vertices_disjoint_reverseBranch)
        hyB hyReverseB
  have hReverseChildOcc : (B.childBranch c).reverseBranch.Occupied C := by
    rcases (B.childBranch c).mem_vertices_or_mem_reverseBranch y with
      hyChild | hyReverseChild
    · exact (hyNotChild hyChild).elim
    · exact ⟨y, hyReverseChild, hyPos⟩
  exact hNoChild c ⟨hChildOcc, hReverseChildOcc⟩

/-- If the exterior side of an oriented edge is empty, its message remains
literally `EMPTY`, and therefore contributes zero to the rooted score. -/
theorem score_eq_effectiveInput_of_reverse_not_occupied
    (C : Configuration V) (B : OrientedBranch T)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    score T C B.root = B.effectiveInput C := by
  rw [score_eq_effectiveInput_add_reverse C B,
    branchMessage_eq_empty_of_not_occupied C B.reverseBranch hEmpty]
  simp [messageContribution, EMPTY]

/-- The already-proved local defect classification applies directly to every
retained support edge, without changing the ambient vertex type. -/
theorem defectEdgeState_of_supportEdge
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0) :
    DefectEdgeState
      (messageContribution (branchMessage C B))
      (messageContribution (branchMessage C B.reverseBranch))
      (scoreDefect T C B.root)
      (scoreDefect T C B.parent) := by
  exact B.defectEdgeState_of_scores_nonpos C
    hEdge.1 hEdge.2 (hScores B.root) (hScores B.parent)


/-- A forced oriented-type support edge: the message in the displayed
orientation is nonnegative.  Under all-nonpositive scores the reverse message
is then forced negative, so the orientation is unique. -/
def DefectArrow (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.SupportEdge C ∧
    0 ≤ messageContribution (branchMessage C B)

/-- A forced defect arrow has a strictly negative reverse message under
all-nonpositive rooted scores. -/
theorem reverse_message_neg_of_defectArrow
    (C : Configuration V) (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hScores : ∀ v, score T C v ≤ 0) :
    messageContribution (branchMessage C B.reverseBranch) < 0 := by
  have hEq :=
    B.defect_equations_of_both_occupied C hArrow.1.1 hArrow.1.2
  have hNotBoth :=
    defect_not_both_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2
  apply lt_of_not_ge
  intro hReverse
  exact hNotBoth ⟨hArrow.2, hReverse⟩

/-- Forced orientations on retained support edges are antisymmetric. -/
theorem not_defectArrow_reverse
    (C : Configuration V) (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hScores : ∀ v, score T C v ≤ 0) :
    ¬ B.reverseBranch.DefectArrow C := by
  intro hReverse
  exact
    (not_lt_of_ge hReverse.2)
      (B.reverse_message_neg_of_defectArrow C hArrow hScores)

/-- The tail of a forced defect arrow has enough endpoint-defect budget to pay
twice the head defect.  This is the concrete support-core form of the local
oriented-edge budget inequality. -/
theorem defectArrow_tail_budget
    (C : Configuration V) (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hScores : ∀ v, score T C v ≤ 0) :
    2 * scoreDefect T C B.parent ≤ scoreDefect T C B.root := by
  have hEq :=
    B.defect_equations_of_both_occupied C hArrow.1.1 hArrow.1.2
  exact
    defect_left_budget
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2

/-- Every retained support edge has either a nonnegative message in one
orientation or two negative messages.  Together with
`not_defectArrow_reverse`, all-nonpositive scores make the nonnegative
orientation unique when it exists. -/
theorem supportEdge_defectArrow_or_reverse_or_both_neg
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) :
    B.DefectArrow C ∨
      B.reverseBranch.DefectArrow C ∨
        (messageContribution (branchMessage C B) < 0 ∧
          messageContribution (branchMessage C B.reverseBranch) < 0) := by
  by_cases hForward :
      0 ≤ messageContribution (branchMessage C B)
  · exact Or.inl ⟨hEdge, hForward⟩
  · have hForwardNeg :
        messageContribution (branchMessage C B) < 0 :=
      lt_of_not_ge hForward
    by_cases hReverse :
        0 ≤ messageContribution (branchMessage C B.reverseBranch)
    · right
      left
      exact
        ⟨(B.supportEdge_reverse_iff C).2 hEdge, hReverse⟩
    · right
      right
      exact ⟨hForwardNeg, lt_of_not_ge hReverse⟩


/-- Retained edges whose later weighted edge estimate has a genuine defect
excess.  Oriented-type edges are defective exactly when the head defect is
positive; a two-negative edge is defective exactly when at least one endpoint
defect is positive (equivalently, it is not the neutral (-1,-1) state under the
defect equations).  The definition is symmetric in the underlying edge. -/
def DefectiveSupportEdge (C : Configuration V) (B : OrientedBranch T) : Prop :=
  B.SupportEdge C ∧
    ((0 ≤ messageContribution (branchMessage C B) ∧
        0 < scoreDefect T C B.parent) ∨
      (0 ≤ messageContribution (branchMessage C B.reverseBranch) ∧
        0 < scoreDefect T C B.root) ∨
      ((messageContribution (branchMessage C B) < 0 ∧
          messageContribution (branchMessage C B.reverseBranch) < 0) ∧
        (0 < scoreDefect T C B.root ∨
          0 < scoreDefect T C B.parent)))

@[simp] theorem defectiveSupportEdge_reverse_iff
    (C : Configuration V) (B : OrientedBranch T) :
    B.reverseBranch.DefectiveSupportEdge C ↔
      B.DefectiveSupportEdge C := by
  simp only [DefectiveSupportEdge, supportEdge_reverse_iff,
    reverseBranch_reverse, reverseBranch_root, reverseBranch_parent]
  aesop

end OrientedBranch

/-- If all positive piles are concentrated at one vertex, that vertex's rooted
score is exactly its pile size.  Every incident branch is genuinely empty,
not an integer-message zero branch. -/
theorem score_eq_of_support_subset_singleton
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hSupport : ∀ v, 0 < C v → v = r) :
    score T C r = (C r : ℤ) := by
  classical
  have hNoOccupied (u : V) :
      ¬ IsOccupiedRootNeighbor T C r u := by
    rintro ⟨hAdj, hOcc⟩
    rcases hOcc with ⟨w, hw, hpos⟩
    have hwr : w = r := hSupport w hpos
    subst w
    exact (incidentBranch T r u hAdj).parent_not_mem_vertices hw
  have hTerm (u : V) :
      rootMessageTerm T C r u = 0 :=
    rootMessageTerm_eq_zero_of_not_occupied T C r (hNoOccupied u)
  rw [score, rootMessageSum]
  simp_rw [hTerm]
  simp

/-- Under all-nonpositive scores, every occupied vertex has another distinct
occupied vertex.  In particular, a nonzero counterconfiguration cannot have
singleton support. -/
theorem exists_other_occupied_of_all_scores_nonpos
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r : V} (hr : 0 < C r) :
    ∃ v, v ≠ r ∧ 0 < C v := by
  by_contra hOther
  have hSupport : ∀ v, 0 < C v → v = r := by
    intro v hv
    by_contra hvr
    exact hOther ⟨v, hvr, hv⟩
  have hEq := score_eq_of_support_subset_singleton T C r hSupport
  have hPos : 0 < score T C r := by
    rw [hEq]
    exact_mod_cast hr
  exact (not_lt_of_ge (hScores r)) hPos

end TreeStack

/- Source module: TreeStack.ForestOwner.lean -/
namespace TreeStack

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The graph of defective retained support edges.  Adjacency is defined by
presenting the ambient tree edge in one orientation and asking for the
orientation-invariant defective-support predicate. -/
noncomputable def defectiveGraph
    (C : Configuration V) : SimpleGraph V where
  Adj u v :=
    ∃ h : T.graph.Adj u v,
      (incidentBranch T v u h).DefectiveSupportEdge C
  symm.symm u v huv := by
    rcases huv with ⟨h, hDef⟩
    refine ⟨h.symm, ?_⟩
    have hRev :
        (incidentBranch T v u h).reverseBranch.DefectiveSupportEdge C :=
      ((incidentBranch T v u h).defectiveSupportEdge_reverse_iff C).2 hDef
    simpa [incidentBranch, reverseBranch] using hRev
  loopless.irrefl u huu := by
    rcases huu with ⟨h, _⟩
    exact h.ne rfl

/-- The defective-edge graph is a spanning subgraph of the ambient tree. -/
theorem defectiveGraph_le_tree
    (C : Configuration V) :
    defectiveGraph (T := T) C ≤ T.graph := by
  intro u v huv
  rcases huv with ⟨h, _⟩
  exact h

/-- Defective retained edges form a forest: their graph is acyclic because it
is a subgraph of the ambient tree. -/
theorem defectiveGraph_isAcyclic
    (C : Configuration V) :
    (defectiveGraph (T := T) C).IsAcyclic := by
  exact
    SimpleGraph.IsAcyclic.anti
      (defectiveGraph_le_tree (T := T) C)
      T.isTree.isAcyclic


/-- For an oriented presentation of a tree edge and a fixed ambient root,
choose the endpoint farther from the root.  Tree acyclicity ensures adjacent
endpoints have distinct distances, so this choice is canonical on the
underlying undirected edge. -/
noncomputable def rootedOwner (r : V) (B : OrientedBranch T) : V :=
  if T.graph.dist r B.root = T.graph.dist r B.parent + 1 then
    B.root
  else
    B.parent

/-- The other endpoint of the edge after choosing `rootedOwner`. -/
noncomputable def rootedOther (r : V) (B : OrientedBranch T) : V :=
  if T.graph.dist r B.root = T.graph.dist r B.parent + 1 then
    B.parent
  else
    B.root

/-- The rooted owner and the other endpoint are adjacent. -/
theorem rootedOther_adj_rootedOwner
    (r : V) (B : OrientedBranch T) :
    T.graph.Adj (B.rootedOther r) (B.rootedOwner r) := by
  classical
  simp only [rootedOther, rootedOwner]
  split
  · exact B.adj.symm
  · exact B.adj

/-- The owner is exactly one level farther from the fixed root than the other
endpoint. -/
theorem rootedOwner_dist_eq_rootedOther_add_one
    (r : V) (B : OrientedBranch T) :
    T.graph.dist r (B.rootedOwner r) =
      T.graph.dist r (B.rootedOther r) + 1 := by
  classical
  simp only [rootedOwner, rootedOther]
  split
  next h =>
    exact h
  next h =>
    rcases T.isTree.dist_eq_dist_add_one_of_adj r B.adj with hForward | hReverse
    · exact (h hForward).elim
    · exact hReverse

/-- If the ambient root lies on the displayed root side of an edge, the
farther endpoint (and hence the rooted owner) is the displayed parent. -/
theorem rootedOwner_eq_parent_of_mem_vertices
    (r : V) (B : OrientedBranch T) (hr : r ∈ B.vertices) :
    B.rootedOwner r = B.parent := by
  classical
  have hdist := B.dist_parent_eq_root_dist_add_one hr
  have hdist' :
      T.graph.dist r B.parent = T.graph.dist r B.root + 1 := by
    simpa only [T.graph.dist_comm] using hdist
  simp only [rootedOwner]
  split
  · next h => omega
  · rfl

/-- Reordering an edge as owner/other does not change its underlying
undirected edge. -/
theorem rootedOwner_other_edge
    (r : V) (B : OrientedBranch T) :
    s(B.rootedOwner r, B.rootedOther r) =
      s(B.root, B.parent) := by
  classical
  simp only [rootedOwner, rootedOther]
  split
  · rfl
  · exact Sym2.eq_swap

/-- A vertex has at most one adjacent predecessor that is exactly one level
closer to a fixed root in a tree. -/
theorem eq_of_adj_owner_of_dist
    (r x u v : V)
    (hu : T.graph.Adj u x) (hv : T.graph.Adj v x)
    (hdu : T.graph.dist r x = T.graph.dist r u + 1)
    (hdv : T.graph.dist r x = T.graph.dist r v + 1) :
    u = v := by
  classical
  obtain ⟨pu, hpu⟩ :=
    (T.isTree.connected r u).exists_walk_length_eq_dist
  obtain ⟨pv, hpv⟩ :=
    (T.isTree.connected r v).exists_walk_length_eq_dist
  have hpuLen :
      (pu.concat hu).length = T.graph.dist r x := by
    simp [hpu, hdu]
  have hpvLen :
      (pv.concat hv).length = T.graph.dist r x := by
    simp [hpv, hdv]
  have hpuPath : (pu.concat hu).IsPath :=
    (pu.concat hu).isPath_of_length_eq_dist hpuLen
  have hpvPath : (pv.concat hv).IsPath :=
    (pv.concat hv).isPath_of_length_eq_dist hpvLen
  have hPathEq :
      (⟨pu.concat hu, hpuPath⟩ : T.graph.Path r x) =
        ⟨pv.concat hv, hpvPath⟩ :=
    T.isTree.isAcyclic.subsingleton_path r x |>.elim _ _
  have hWalkEq : pu.concat hu = pv.concat hv :=
    Subtype.mk.inj hPathEq
  have hPenultimate :=
    congrArg SimpleGraph.Walk.penultimate hWalkEq
  simpa using hPenultimate

/-- The ambient-root owner assignment is injective on underlying tree edges:
two edges with the same owner are the same undirected edge.  Consequently its
restriction to any defective-edge forest is an injective incident-owner
assignment, without rooting forest components separately. -/
theorem edge_eq_of_rootedOwner_eq
    (r : V) (B D : OrientedBranch T)
    (hOwner : B.rootedOwner r = D.rootedOwner r) :
    s(B.root, B.parent) = s(D.root, D.parent) := by
  have hOther :
      B.rootedOther r = D.rootedOther r := by
    apply eq_of_adj_owner_of_dist
      (T := T) r (B.rootedOwner r)
    · exact B.rootedOther_adj_rootedOwner r
    · rw [hOwner]
      exact D.rootedOther_adj_rootedOwner r
    · exact B.rootedOwner_dist_eq_rootedOther_add_one r
    · rw [hOwner]
      exact D.rootedOwner_dist_eq_rootedOther_add_one r
  calc
    s(B.root, B.parent) =
        s(B.rootedOwner r, B.rootedOther r) :=
      (B.rootedOwner_other_edge r).symm
    _ = s(D.rootedOwner r, D.rootedOther r) := by
      rw [hOwner, hOther]
    _ = s(D.root, D.parent) :=
      D.rootedOwner_other_edge r

/-- Reversing the presentation of an edge does not change its rooted owner. -/
theorem rootedOwner_reverse
    (r : V) (B : OrientedBranch T) :
    B.reverseBranch.rootedOwner r = B.rootedOwner r := by
  classical
  rcases T.isTree.dist_eq_dist_add_one_of_adj r B.adj with hForward | hReverse
  · simp [rootedOwner, reverseBranch, hForward]
    omega
  · simp [rootedOwner, reverseBranch, hReverse]
    omega


end OrientedBranch

end TreeStack

/- Source module: TreeStack.DefectCharge.lean -/
namespace TreeStack

/-- Weighted edge estimate for an oriented-type defect edge.  If the auxiliary
weight at the head is at least twice the weight at the tail, the edge
contribution is bounded by the neutral endpoint weights plus the standard
head-defect excess. -/
theorem oriented_edge_excess_bound
    {a b deltaHead weightTail weightHead : ℤ}
    (ha : 0 ≤ a)
    (hb : b = -2 * (a + deltaHead) - 3)
    (hDouble : 2 * weightTail ≤ weightHead) :
    -(weightHead * a + weightTail * b) ≤
      weightTail + weightHead + 2 * weightTail * deltaHead := by
  have hCoeff : 2 * weightTail - weightHead ≤ 0 := by
    linarith
  have hMul : a * (2 * weightTail - weightHead) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha hCoeff
  rw [hb]
  calc
    -(weightHead * a + weightTail * (-2 * (a + deltaHead) - 3)) =
        3 * weightTail +
          a * (2 * weightTail - weightHead) +
          2 * weightTail * deltaHead := by
            ring
    _ ≤ 3 * weightTail + 2 * weightTail * deltaHead := by
          linarith
    _ ≤ weightTail + weightHead + 2 * weightTail * deltaHead := by
          linarith

/-- The oriented-edge excess can be paid by the tail endpoint whenever the
local defect classification supplies the factor-two tail budget. -/
theorem oriented_excess_le_tail_budget
    {deltaTail deltaHead weightTail : ℤ}
    (hWeight : 0 ≤ weightTail)
    (hBudget : 2 * deltaHead ≤ deltaTail) :
    2 * weightTail * deltaHead ≤ weightTail * deltaTail := by
  have h :=
    mul_le_mul_of_nonneg_left hBudget hWeight
  nlinarith

/-- The same oriented-edge excess can instead be paid by the head endpoint
whenever the auxiliary orientation doubles weights along the edge. -/
theorem oriented_excess_le_head_budget
    {deltaHead weightTail weightHead : ℤ}
    (hDelta : 0 ≤ deltaHead)
    (hDouble : 2 * weightTail ≤ weightHead) :
    2 * weightTail * deltaHead ≤ weightHead * deltaHead := by
  exact mul_le_mul_of_nonneg_right hDouble hDelta

/-- Exact weighted contribution of a two-negative edge in its odd-negative
parameterization. -/
theorem two_negative_edge_excess_eq
    {a b r q weightTail weightHead : ℤ}
    (ha : a = -(2 * r + 1))
    (hb : b = -(2 * q + 1)) :
    -(weightHead * a + weightTail * b) =
      weightTail + weightHead +
        2 * (weightHead * r + weightTail * q) := by
  rw [ha, hb]
  ring

/-- If a two-negative edge is oriented toward its owner and owner weight is at
least twice tail weight, the complete excess is paid by the owner's endpoint
defect.  Here `deltaOwner = q + 2*r` is exactly the local defect equation. -/
theorem two_negative_excess_le_owner_budget
    {r q deltaOwner weightTail weightOwner : ℤ}
    (hq : 0 ≤ q)
    (hDouble : 2 * weightTail ≤ weightOwner)
    (hDelta : deltaOwner = q + 2 * r) :
    2 * (weightOwner * r + weightTail * q) ≤
      weightOwner * deltaOwner := by
  have hqMul :
      (2 * weightTail) * q ≤ weightOwner * q :=
    mul_le_mul_of_nonneg_right hDouble hq
  rw [hDelta]
  calc
    2 * (weightOwner * r + weightTail * q) =
        2 * weightOwner * r + (2 * weightTail) * q := by
          ring
    _ ≤ 2 * weightOwner * r + weightOwner * q := by
          linarith
    _ = weightOwner * (q + 2 * r) := by
          ring

end TreeStack

/- Source module: TreeStack.Auxiliary.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Reversing an incident presentation of an edge gives the reverse branch. -/
@[simp] theorem incidentBranch_reverse
    (u v : V) (h : T.graph.Adj u v) :
    incidentBranch T u v h.symm =
      (incidentBranch T v u h).reverseBranch := by
  rfl

/-- In the two-negative state, presenting the edge toward its fixed ambient
rooted owner puts the local defect equation in exactly the orientation used by
`two_negative_excess_le_owner_budget`. -/
theorem two_negative_parameters_toward_rootedOwner
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0)
    (haNeg :
      messageContribution (branchMessage C B) < 0)
    (hbNeg :
      messageContribution (branchMessage C B.reverseBranch) < 0)
    (hOwner : B.parent = B.rootedOwner ambientRoot) :
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      messageContribution (branchMessage C B) = -(2 * r + 1) ∧
      messageContribution (branchMessage C B.reverseBranch) = -(2 * q + 1) ∧
      scoreDefect T C B.root = r + 2 * q ∧
      scoreDefect T C (B.rootedOwner ambientRoot) = q + 2 * r := by
  have hEq :=
    B.defect_equations_of_both_occupied C hEdge.1 hEdge.2
  rcases
      defect_two_negative
        ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
        ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
        hEq.1 hEq.2 haNeg hbNeg with
    ⟨r, q, hr, hq, ha, hb, hRoot, hParent⟩
  refine ⟨r, q, hr, hq, ha, hb, hRoot, ?_⟩
  rw [← hOwner]
  exact hParent

/-- A defective two-negative support edge, presented from the other endpoint
toward its injectively chosen ambient-root owner. -/
def TwoNegativeOwnerArrow
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T) : Prop :=
  B.DefectiveSupportEdge C ∧
    messageContribution (branchMessage C B) < 0 ∧
    messageContribution (branchMessage C B.reverseBranch) < 0 ∧
    B.parent = B.rootedOwner ambientRoot

/-- The owner of an edge is one of its endpoints. -/
theorem rootedOwner_eq_root_or_parent
    (ambientRoot : V) (B : OrientedBranch T) :
    B.rootedOwner ambientRoot = B.root ∨
      B.rootedOwner ambientRoot = B.parent := by
  classical
  simp only [rootedOwner]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The same two-negative edge cannot point toward its rooted owner in both
presentations. -/
theorem not_twoNegativeOwnerArrow_reverse
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hArrow : B.TwoNegativeOwnerArrow C ambientRoot) :
    ¬ B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
  intro hReverse
  have hParentOwner :
      B.parent = B.rootedOwner ambientRoot :=
    hArrow.2.2.2
  have hRootOwner :
      B.root = B.rootedOwner ambientRoot := by
    have h := hReverse.2.2.2
    simpa [rootedOwner_reverse] using h
  exact B.root_ne_parent (hRootOwner.trans hParentOwner.symm)

/-- Combined auxiliary orientation on retained support edges.  Every
oriented-type edge keeps its forced defect-arrow direction, including the
zero-excess states needed for the powers-of-two baseline estimate.
Two-negative edges are directed only when defective, toward the fixed rooted
owner. -/
def AuxArrow
    (C : Configuration V) (ambientRoot : V) (u v : V) : Prop :=
  ∃ h : T.graph.Adj u v,
    let B := incidentBranch T v u h
    B.DefectArrow C ∨
      B.TwoNegativeOwnerArrow C ambientRoot

/-- Rebuilding an oriented branch from its own endpoints and adjacency proof
returns the same branch. -/
@[simp] theorem incidentBranch_self
    (B : OrientedBranch T) :
    incidentBranch T B.parent B.root B.adj = B := by
  cases B
  rfl

/-- Rebuilding the reverse orientation from the swapped endpoints gives the
stored reverse branch. -/
@[simp] theorem incidentBranch_reverse_self
    (B : OrientedBranch T) :
    incidentBranch T B.root B.parent B.adj.symm = B.reverseBranch := by
  cases B
  rfl

/-- Every defective retained support edge receives an auxiliary direction.
Oriented-type edges use their forced message direction; two-negative edges
point toward the fixed rooted owner. -/
theorem auxArrow_or_reverse_of_defectiveSupportEdge
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C) :
    AuxArrow (T := T) C ambientRoot B.root B.parent ∨
      AuxArrow (T := T) C ambientRoot B.parent B.root := by
  rcases
      B.supportEdge_defectArrow_or_reverse_or_both_neg C hDef.1 with
    hForward | hReverse | hBothNeg
  · left
    refine ⟨B.adj, ?_⟩
    simpa using
      (Or.inl hForward :
        B.DefectArrow C ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  · right
    have hDefReverse :
        B.reverseBranch.DefectiveSupportEdge C :=
      (B.defectiveSupportEdge_reverse_iff C).2 hDef
    refine ⟨B.adj.symm, ?_⟩
    have hInc :
        incidentBranch T B.root B.parent B.adj.symm =
          B.reverseBranch := by
      exact incidentBranch_reverse_self B
    change
      (incidentBranch T B.root B.parent B.adj.symm).DefectArrow C ∨
        (incidentBranch T B.root B.parent B.adj.symm).TwoNegativeOwnerArrow
          C ambientRoot
    rw [hInc]
    exact Or.inl hReverse
  · rcases B.rootedOwner_eq_root_or_parent ambientRoot with
      hOwnerRoot | hOwnerParent
    · right
      have hDefReverse :
          B.reverseBranch.DefectiveSupportEdge C :=
        (B.defectiveSupportEdge_reverse_iff C).2 hDef
      have hOwnerReverse :
          B.reverseBranch.parent =
            B.reverseBranch.rootedOwner ambientRoot := by
        simpa [rootedOwner_reverse] using hOwnerRoot.symm
      have hTwoReverse :
          B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
        refine ⟨hDefReverse, hBothNeg.2, ?_, hOwnerReverse⟩
        simpa using hBothNeg.1
      refine ⟨B.adj.symm, ?_⟩
      have hInc :
          incidentBranch T B.root B.parent B.adj.symm =
            B.reverseBranch := by
        exact incidentBranch_reverse_self B
      change
        (incidentBranch T B.root B.parent B.adj.symm).DefectArrow C ∨
          (incidentBranch T B.root B.parent B.adj.symm).TwoNegativeOwnerArrow
            C ambientRoot
      rw [hInc]
      exact Or.inr hTwoReverse
    · left
      have hTwo :
          B.TwoNegativeOwnerArrow C ambientRoot :=
        ⟨hDef, hBothNeg.1, hBothNeg.2, hOwnerParent.symm⟩
      refine ⟨B.adj, ?_⟩
      simpa using
        (Or.inr hTwo :
          B.DefectArrow C ∨
            B.TwoNegativeOwnerArrow C ambientRoot)

/-- Every auxiliary arrow is an ambient tree edge. -/
theorem auxArrow_adj
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    T.graph.Adj u v := by
  rcases hArrow with ⟨h, _⟩
  exact h

/-- Every auxiliary arrow lies on a retained support edge. -/
theorem auxArrow_supportEdge
    (C : Configuration V) (ambientRoot : V) {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    (incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)).SupportEdge C := by
  rcases hArrow with ⟨h, hState⟩
  dsimp only at hState
  have hp : auxArrow_adj C ambientRoot ⟨h, hState⟩ = h :=
    Subsingleton.elim _ _
  rw [hp]
  rcases hState with hOriented | hTwo
  · exact hOriented.1
  · exact hTwo.1.1

/-- No auxiliary arrow can enter the root of a configuration-empty oriented
branch.  An arrow across the boundary would retain the empty side, while an
arrow from a genuine child would retain an occupied subbranch inside it. -/
theorem no_auxArrow_to_root_of_not_occupied
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T) (hEmpty : ¬ B.Occupied C) (u : V) :
    ¬ AuxArrow (T := T) C ambientRoot u B.root := by
  intro hArrow
  have hAdj := auxArrow_adj C ambientRoot hArrow
  have hSupport := auxArrow_supportEdge C ambientRoot hArrow
  by_cases hup : u = B.parent
  · subst u
    have hBranch :
        incidentBranch T B.root B.parent hAdj = B.reverseBranch := by
      cases B
      rfl
    rw [hBranch] at hSupport
    exact hEmpty hSupport.2
  · let c : B.Child :=
      { vertex := u
        adj := hAdj.symm
        ne_parent := hup }
    have hBranch :
        incidentBranch T B.root u hAdj = B.childBranch c := by
      rfl
    rw [hBranch] at hSupport
    rcases hSupport.1 with ⟨x, hx, hxPos⟩
    exact hEmpty ⟨x, B.childBranch_vertices_subset c hx, hxPos⟩

/-- Under all-nonpositive rooted scores, the combined orientation never places
both directions on the same defective edge. -/
theorem not_auxArrow_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    ¬ AuxArrow (T := T) C ambientRoot v u := by
  intro hReverse
  rcases hArrow with ⟨huv, hForwardState⟩
  rcases hReverse with ⟨hvu, hReverseState⟩
  let B : OrientedBranch T := incidentBranch T v u huv
  have hRevBranch :
      incidentBranch T u v hvu = B.reverseBranch := by
    have hp : hvu = huv.symm := Subsingleton.elim _ _
    subst hvu
    rfl
  dsimp only at hForwardState hReverseState
  change
    B.DefectArrow C ∨
      B.TwoNegativeOwnerArrow C ambientRoot at hForwardState
  rw [hRevBranch] at hReverseState
  rcases hForwardState with hForward | hForward
  · rcases hReverseState with hReverse | hReverse
    · exact
        (B.not_defectArrow_reverse C hForward hScores)
          hReverse
    · exact
        (not_lt_of_ge hForward.2)
          hReverse.2.2.1
  · rcases hReverseState with hReverse | hReverse
    · exact
        (not_lt_of_ge hReverse.2)
          hForward.2.2.1
    · exact
        (B.not_twoNegativeOwnerArrow_reverse C ambientRoot hForward)
          hReverse

/-- Once an auxiliary arrow crosses an ambient tree edge, there is no directed
return path across that edge.  The proof uses the deleted-edge branch cut:
every path from the parent side back to the root side must cross the same
unique tree edge in the forbidden reverse direction. -/
theorem auxArrow_no_reflTransGen_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    ¬ Relation.ReflTransGen
        (AuxArrow (T := T) C ambientRoot) v u := by
  intro hReturn
  let B : OrientedBranch T :=
    incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)
  have hOutside :
      ∀ {x : V},
        Relation.ReflTransGen
            (AuxArrow (T := T) C ambientRoot) v x →
          x ∉ B.vertices := by
    intro x hx
    induction hx with
    | refl =>
        simpa [B] using B.parent_not_mem_vertices
    | tail hReach hStep ih =>
        intro hxIn
        have hAdj :=
          (auxArrow_adj C ambientRoot hStep).symm
        have hEdge :=
          B.edge_leaving_vertices_eq_boundary hxIn ih hAdj
        rw [Sym2.eq_iff] at hEdge
        rcases hEdge with hEdge | hEdge
        · have hReverse :
              AuxArrow (T := T) C ambientRoot v u := by
            rcases hEdge with ⟨hRoot, hParent⟩
            subst_vars
            simpa [B] using hStep
          exact
            (not_auxArrow_reverse C ambientRoot hScores hArrow)
              hReverse
        · have : B.parent ∈ B.vertices := by
            rw [← hEdge.1]
            exact hxIn
          exact B.parent_not_mem_vertices this
  have huOutside := hOutside hReturn
  exact huOutside (by simpa [B] using B.root_mem_vertices)

/-- The directed auxiliary relation is acyclic: its transitive closure is
irreflexive.  This is derived directly from the ambient tree cut argument,
without rooting defective-forest components. -/
theorem auxArrow_transGen_irrefl
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    ¬ Relation.TransGen
        (AuxArrow (T := T) C ambientRoot) v v := by
  intro hCycle
  rcases Relation.TransGen.head'_iff.mp hCycle with
    ⟨u, hFirst, hReturn⟩
  exact
    (auxArrow_no_reflTransGen_reverse
      C ambientRoot hScores hFirst) hReturn

/-- Strict directed predecessors of a vertex in the auxiliary DAG. -/
noncomputable def auxPred
    (C : Configuration V) (ambientRoot : V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter fun u =>
    Relation.TransGen (AuxArrow (T := T) C ambientRoot) u v

@[simp] theorem mem_auxPred
    (C : Configuration V) (ambientRoot : V) (u v : V) :
    u ∈ auxPred (T := T) C ambientRoot v ↔
      Relation.TransGen (AuxArrow (T := T) C ambientRoot) u v := by
  simp [auxPred]

/-- A directed edge strictly enlarges the finite set of strict directed
predecessors. -/
theorem auxPred_ssubset_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxPred (T := T) C ambientRoot u ⊂
      auxPred (T := T) C ambientRoot v := by
  have hSubset :
      auxPred (T := T) C ambientRoot u ⊆
        auxPred (T := T) C ambientRoot v := by
    intro x hx
    rw [mem_auxPred] at hx ⊢
    exact Relation.TransGen.tail hx hArrow
  rw [Finset.ssubset_iff_of_subset hSubset]
  refine ⟨u, ?_, ?_⟩
  · rw [mem_auxPred]
    exact Relation.TransGen.single hArrow
  · rw [mem_auxPred]
    exact auxArrow_transGen_irrefl C ambientRoot hScores u

/-- A finite topological rank for the auxiliary DAG, used as the recursion
measure for the genuine longest-directed-path height below. -/
noncomputable def auxRank
    (C : Configuration V) (ambientRoot : V) (v : V) : ℕ :=
  (auxPred (T := T) C ambientRoot v).card

/-- Auxiliary rank strictly increases along every directed edge. -/
theorem auxRank_lt_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxRank (T := T) C ambientRoot u <
      auxRank (T := T) C ambientRoot v := by
  exact Finset.card_lt_card
    (auxPred_ssubset_of_auxArrow
      C ambientRoot hScores hArrow)

/-- Length of a longest auxiliary directed path ending at a vertex.  The
well-founded measure is the strict-predecessor rank, which increases along
every arrow. -/
noncomputable def auxHeight
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℕ :=
  (Finset.univ : Finset V).sup fun u =>
    if h : AuxArrow (T := T) C ambientRoot u v then
      auxHeight C ambientRoot hScores u + 1
    else
      0
termination_by auxRank (T := T) C ambientRoot v
decreasing_by
  exact auxRank_lt_of_auxArrow C ambientRoot hScores h

/-- Every auxiliary arrow extends a longest directed path by one step. -/
theorem auxHeight_succ_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    auxHeight C ambientRoot hScores u + 1 ≤
      auxHeight C ambientRoot hScores v := by
  nth_rewrite 2 [auxHeight]
  have hLe :=
    Finset.le_sup
      (f := fun x : V =>
        if h : AuxArrow (T := T) C ambientRoot x v then
          auxHeight C ambientRoot hScores x + 1
        else
          0)
      (Finset.mem_univ u)
  simpa [hArrow] using hLe

/-- A vertex with no incoming auxiliary arrow has auxiliary height zero. -/
theorem auxHeight_eq_zero_of_no_incoming
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V)
    (hNo : ∀ u, ¬ AuxArrow (T := T) C ambientRoot u v) :
    auxHeight C ambientRoot hScores v = 0 := by
  rw [auxHeight]
  simp [hNo]

/-- Powers-of-two auxiliary weights attached to longest-path heights. -/
noncomputable def auxWeight
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℕ :=
  2 ^ auxHeight C ambientRoot hScores v

/-- Auxiliary weights are positive (and in particular at least one). -/
theorem auxWeight_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    0 < auxWeight C ambientRoot hScores v := by
  simp [auxWeight]

/-- The key doubling inequality: weights at least double along every auxiliary
directed edge. -/
theorem two_mul_auxWeight_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    2 * auxWeight C ambientRoot hScores u ≤
      auxWeight C ambientRoot hScores v := by
  have hHeight :=
    auxHeight_succ_le_of_auxArrow
      C ambientRoot hScores hArrow
  have hPow :
      2 ^ (auxHeight C ambientRoot hScores u + 1) ≤
        2 ^ auxHeight C ambientRoot hScores v :=
    Nat.pow_le_pow_of_le (by omega) hHeight
  simpa [auxWeight, Nat.two_pow_succ, two_mul] using hPow

/-- Integer form of the powers-of-two auxiliary weight, convenient for the
weighted defect inequalities, which are stated over integers. -/
noncomputable def auxWeightInt
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : ℤ :=
  (auxWeight C ambientRoot hScores v : ℤ)

/-- Integer auxiliary weights are nonnegative. -/
theorem auxWeightInt_nonneg
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    0 ≤ auxWeightInt C ambientRoot hScores v := by
  simp [auxWeightInt]

/-- The root of an empty branch has unit auxiliary weight. -/
theorem auxWeightInt_eq_one_of_not_occupied
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) (hEmpty : ¬ B.Occupied C) :
    auxWeightInt C ambientRoot hScores B.root = 1 := by
  have hHeight : auxHeight C ambientRoot hScores B.root = 0 :=
    auxHeight_eq_zero_of_no_incoming C ambientRoot hScores B.root
      (no_auxArrow_to_root_of_not_occupied C ambientRoot B hEmpty)
  simp [auxWeightInt, auxWeight, hHeight]

/-- Integer doubling form used directly by `DefectCharge.lean`. -/
theorem two_mul_auxWeightInt_le_of_auxArrow
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {u v : V}
    (hArrow : AuxArrow (T := T) C ambientRoot u v) :
    2 * auxWeightInt C ambientRoot hScores u ≤
      auxWeightInt C ambientRoot hScores v := by
  change
    (2 : ℤ) * (auxWeight C ambientRoot hScores u : ℤ) ≤
      (auxWeight C ambientRoot hScores v : ℤ)
  exact_mod_cast
    (two_mul_auxWeight_le_of_auxArrow
      C ambientRoot hScores hArrow)

end OrientedBranch

end TreeStack

/- Source module: TreeStack.AuxiliaryCharge.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Weighted message contribution of one retained edge, using the auxiliary
powers-of-two weights.  The displayed branch is oriented root (tail) toward
parent (head). -/
noncomputable def auxEdgeContribution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  -(auxWeightInt C ambientRoot hScores B.parent *
        messageContribution (branchMessage C B) +
      auxWeightInt C ambientRoot hScores B.root *
        messageContribution (branchMessage C B.reverseBranch))

/-- The weighted contribution does not depend on which orientation is used to
display the underlying edge. -/
@[simp] theorem auxEdgeContribution_reverse
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) :
    auxEdgeContribution C ambientRoot hScores B.reverseBranch =
      auxEdgeContribution C ambientRoot hScores B := by
  simp [auxEdgeContribution]
  ring

/-- A defective forced arrow has its weighted edge excess payable by its tail
defect. -/
theorem defectArrow_auxEdgeContribution_le_tail_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C)
    (hArrow : B.DefectArrow C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.root *
          scoreDefect T C B.root := by
  have hAux :
      AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inl hArrow :
        B.DefectArrow C ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  have hEq :=
    B.defect_equations_of_both_occupied
      C hArrow.1.1 hArrow.1.2
  have hLeft :=
    defect_left_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2
  have hEdge :=
    oriented_edge_excess_bound
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      (deltaHead := scoreDefect T C B.parent)
      hArrow.2 hLeft.1 hDouble
  have hPay :=
    oriented_excess_le_tail_budget
      (auxWeightInt_nonneg C ambientRoot hScores B.root)
      (B.defectArrow_tail_budget C hArrow hScores)
  unfold auxEdgeContribution
  linarith

/-- The same defective forced-arrow excess can instead be paid by its head
defect, using the auxiliary doubling inequality. -/
theorem defectArrow_auxEdgeContribution_le_head_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C)
    (hArrow : B.DefectArrow C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.parent *
          scoreDefect T C B.parent := by
  have hAux :
      AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inl hArrow :
        B.DefectArrow C ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  have hEq :=
    B.defect_equations_of_both_occupied
      C hArrow.1.1 hArrow.1.2
  have hLeft :=
    defect_left_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2
  have hEdge :=
    oriented_edge_excess_bound
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      (deltaHead := scoreDefect T C B.parent)
      hArrow.2 hLeft.1 hDouble
  have hPay :=
    oriented_excess_le_head_budget
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hDouble
  unfold auxEdgeContribution
  linarith

/-- A defective two-negative edge directed toward its rooted owner has its
entire weighted excess payable by the owner endpoint defect. -/
theorem twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hTwo : B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores B.parent *
          scoreDefect T C B.parent := by
  have hAux :
      AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inr hTwo :
        B.DefectArrow C ∨
          B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  rcases
      B.two_negative_parameters_toward_rootedOwner
        C ambientRoot hTwo.1.1 hScores
        hTwo.2.1 hTwo.2.2.1 hTwo.2.2.2 with
    ⟨r, q, hr, hq, ha, hb, hRoot, hOwner⟩
  have hParent :
      scoreDefect T C B.parent = q + 2 * r := by
    rw [hTwo.2.2.2]
    exact hOwner
  have hEdge :=
    two_negative_edge_excess_eq
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      ha hb
  have hPay :=
    two_negative_excess_le_owner_budget
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightOwner := auxWeightInt C ambientRoot hScores B.parent)
      (deltaOwner := scoreDefect T C B.parent)
      hq hDouble hParent
  unfold auxEdgeContribution
  linarith

/-- For a displayed auxiliary edge state, the weighted excess is payable by
the fixed rooted owner of the underlying edge.  This is the local statement
that the future global sum will combine with injectivity of `rootedOwner`. -/
theorem auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hState :
      (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
        B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
          scoreDefect T C (B.rootedOwner ambientRoot) := by
  rcases hState with hOriented | hTwo
  · rcases B.rootedOwner_eq_root_or_parent ambientRoot with
      hOwnerRoot | hOwnerParent
    · have h :=
        defectArrow_auxEdgeContribution_le_tail_charge
          C ambientRoot hScores B hOriented.1 hOriented.2
      rw [hOwnerRoot]
      exact h
    · have h :=
        defectArrow_auxEdgeContribution_le_head_charge
          C ambientRoot hScores B hOriented.1 hOriented.2
      rw [hOwnerParent]
      exact h
  · have h :=
      twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
        C ambientRoot hScores B hTwo
    rw [← hTwo.2.2.2]
    exact h

/-- A forced oriented edge with zero head defect has no positive excess over
the endpoint baseline. -/
theorem defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hDeltaZero : scoreDefect T C B.parent = 0) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent := by
  have hAux : AuxArrow (T := T) C ambientRoot B.root B.parent := by
    refine ⟨B.adj, ?_⟩
    simpa only [incidentBranch_self] using
      (Or.inl hArrow :
        B.DefectArrow C ∨ B.TwoNegativeOwnerArrow C ambientRoot)
  have hDouble :=
    two_mul_auxWeightInt_le_of_auxArrow
      C ambientRoot hScores hAux
  have hEq :=
    B.defect_equations_of_both_occupied C hArrow.1.1 hArrow.1.2
  have hLeft :=
    defect_left_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2
  have hBound :=
    oriented_edge_excess_bound
      (weightTail := auxWeightInt C ambientRoot hScores B.root)
      (weightHead := auxWeightInt C ambientRoot hScores B.parent)
      (deltaHead := scoreDefect T C B.parent)
      hArrow.2 hLeft.1 hDouble
  unfold auxEdgeContribution
  rw [hDeltaZero] at hBound
  linarith

/-- A retained edge with no positive defect excess contributes at most its two
endpoint weights.  Oriented zero-excess states still use their forced
auxiliary direction, which is why every `DefectArrow` participates in
`AuxArrow`, not only defective ones. -/
theorem nondefectiveSupportEdge_auxEdgeContribution_le_baseline
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hNondef : ¬ B.DefectiveSupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent := by
  rcases B.supportEdge_defectArrow_or_reverse_or_both_neg C hEdge with
    hForward | hReverse | hBothNeg
  · have hDeltaZero : scoreDefect T C B.parent = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.parent := by omega
      exact hNondef ⟨hEdge, Or.inl ⟨hForward.2, hPos⟩⟩
    exact
      defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
        C ambientRoot hScores B hForward hDeltaZero
  · have hDeltaZero : scoreDefect T C B.root = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.root).2 (hScores B.root)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.root := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inl ⟨hReverse.2, hPos⟩)⟩
    have h :=
      defectArrow_auxEdgeContribution_le_baseline_of_head_defect_zero
        C ambientRoot hScores B.reverseBranch hReverse (by simpa using hDeltaZero)
    simpa [add_comm] using h
  · have hRootZero : scoreDefect T C B.root = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.root).2 (hScores B.root)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.root := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inr ⟨hBothNeg, Or.inl hPos⟩)⟩
    have hParentZero : scoreDefect T C B.parent = 0 := by
      have hNonneg :=
        (scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent)
      by_contra hne
      have hPos : 0 < scoreDefect T C B.parent := by omega
      exact hNondef ⟨hEdge, Or.inr (Or.inr ⟨hBothNeg, Or.inr hPos⟩)⟩
    have hEq :=
      B.defect_equations_of_both_occupied C hEdge.1 hEdge.2
    rcases
        defect_two_negative
          ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
          ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
          hEq.1 hEq.2 hBothNeg.1 hBothNeg.2 with
      ⟨r, q, hr, hq, ha, hb, hRoot, hParent⟩
    have hrZero : r = 0 := by omega
    have hqZero : q = 0 := by omega
    unfold auxEdgeContribution
    rw [ha, hb, hrZero, hqZero]
    ring_nf
    exact le_rfl

/-- Every defective retained edge has its weighted contribution bounded by
the endpoint baseline plus the charge at its injective rooted owner. -/
theorem defectiveSupportEdge_auxEdgeContribution_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hDef : B.DefectiveSupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
          scoreDefect T C (B.rootedOwner ambientRoot) := by
  rcases B.auxArrow_or_reverse_of_defectiveSupportEdge C ambientRoot hDef with
    hForward | hReverse
  · rcases hForward with ⟨h, hState⟩
    have hp : h = B.adj := Subsingleton.elim _ _
    subst h
    simp only [incidentBranch_self] at hState
    have hState' :
        (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
          B.TwoNegativeOwnerArrow C ambientRoot := by
      rcases hState with hArrow | hTwo
      · exact Or.inl ⟨hDef, hArrow⟩
      · exact Or.inr hTwo
    exact
      auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
        C ambientRoot hScores B hState'
  · have hDefReverse : B.reverseBranch.DefectiveSupportEdge C :=
      (B.defectiveSupportEdge_reverse_iff C).2 hDef
    rcases hReverse with ⟨h, hState⟩
    have hp : h = B.adj.symm := Subsingleton.elim _ _
    subst h
    simp only [incidentBranch_reverse_self] at hState
    have hState' :
        (B.reverseBranch.DefectiveSupportEdge C ∧
            B.reverseBranch.DefectArrow C) ∨
          B.reverseBranch.TwoNegativeOwnerArrow C ambientRoot := by
      rcases hState with hArrow | hTwo
      · exact Or.inl ⟨hDefReverse, hArrow⟩
      · exact Or.inr hTwo
    have h :=
      auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
        C ambientRoot hScores B.reverseBranch hState'
    simpa [add_comm, rootedOwner_reverse] using h

/-- Uniform retained-edge estimate, exposing a charge exactly when the edge is
defective. -/
theorem supportEdge_auxEdgeContribution_le
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hEdge : B.SupportEdge C) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        if B.DefectiveSupportEdge C then
          auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
            scoreDefect T C (B.rootedOwner ambientRoot)
        else 0 := by
  by_cases hDef : B.DefectiveSupportEdge C
  · simpa [hDef] using
      defectiveSupportEdge_auxEdgeContribution_le_owner_charge
        C ambientRoot hScores B hDef
  · have h :=
      nondefectiveSupportEdge_auxEdgeContribution_le_baseline
        C ambientRoot hScores B hEdge hDef
    simp only [hDef, ↓reduceIte, add_zero]
    exact h

/-- Across a nonretained edge with an occupied displayed root side, the other
message remains literally `EMPTY`.  The whole weighted edge contribution is
exactly the defect charge at the empty-side endpoint, whose auxiliary weight
is one. -/
theorem auxEdgeContribution_eq_emptySide_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hOccupied : B.Occupied C)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    auxEdgeContribution C ambientRoot hScores B =
      auxWeightInt C ambientRoot hScores B.parent *
        scoreDefect T C B.parent := by
  have hEmptyMessage :=
    branchMessage_eq_empty_of_not_occupied C B.reverseBranch hEmpty
  have hEmptyInput :=
    effectiveInput_eq_zero_of_not_occupied C B.reverseBranch hEmpty
  have hWeight :
      auxWeightInt C ambientRoot hScores B.parent = 1 := by
    simpa using
      auxWeightInt_eq_one_of_not_occupied
        C ambientRoot hScores B.reverseBranch hEmpty
  have hScore := score_eq_effectiveInput_add_reverse C B.reverseBranch
  simp only [reverseBranch_root, reverseBranch_reverse] at hScore
  rw [hEmptyInput] at hScore
  unfold auxEdgeContribution scoreDefect
  rw [hEmptyMessage, hWeight, hScore]
  simp

/-- When the fixed ambient root carries a pebble, the empty-side endpoint of a
nonretained edge is exactly its rooted owner. -/
theorem rootedOwner_eq_emptySide_of_root_pos
    (C : Configuration V) (ambientRoot : V)
    (B : OrientedBranch T)
    (hRootPos : 0 < C ambientRoot)
    (hEmpty : ¬ B.reverseBranch.Occupied C) :
    B.rootedOwner ambientRoot = B.parent := by
  have hNotReverse : ambientRoot ∉ B.reverseBranch.vertices := by
    intro hmem
    exact hEmpty ⟨ambientRoot, hmem, hRootPos⟩
  have hMem : ambientRoot ∈ B.vertices := by
    rcases B.mem_vertices_or_mem_reverseBranch ambientRoot with h | h
    · exact h
    · exact (hNotReverse h).elim
  exact B.rootedOwner_eq_parent_of_mem_vertices ambientRoot hMem

/-- Owner-paid defect excess for a retained edge.  This term is nonzero only
when the retained edge is genuinely defective. -/
noncomputable def retainedDefectCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  if B.DefectiveSupportEdge C then
    auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
      scoreDefect T C (B.rootedOwner ambientRoot)
  else
    0

/-- Cancellation term created by a nonretained edge whose opposite branch is
literally `EMPTY`.  This is deliberately kept separate from retained-edge
defect charging. -/
noncomputable def emptyBoundaryCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  if B.SupportEdge C then
    0
  else
    auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
      scoreDefect T C (B.rootedOwner ambientRoot)

/-- Uniform ambient-edge estimate with the two cancellation mechanisms kept
separate: only genuinely defective retained edges receive owner-paid defect
charge, while nonretained edges use their distinct `EMPTY`-boundary term. -/
theorem auxEdgeContribution_le_endpoint_add_separated_charges
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        retainedDefectCharge C ambientRoot hScores B +
        emptyBoundaryCharge C ambientRoot hScores B := by
  by_cases hEdge : B.SupportEdge C
  · have h :=
      supportEdge_auxEdgeContribution_le
        C ambientRoot hScores B hEdge
    simpa [retainedDefectCharge, emptyBoundaryCharge, hEdge, add_assoc] using h
  · have hNondef : ¬ B.DefectiveSupportEdge C := by
      intro hDef
      exact hEdge hDef.1
    have hOwnerBound :
        auxEdgeContribution C ambientRoot hScores B ≤
          auxWeightInt C ambientRoot hScores B.root +
            auxWeightInt C ambientRoot hScores B.parent +
            auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
              scoreDefect T C (B.rootedOwner ambientRoot) := by
      rcases B.occupied_or_reverse_occupied C hRootPos with hOcc | hRevOcc
      · have hEmpty : ¬ B.reverseBranch.Occupied C := by
          intro hRev
          exact hEdge ⟨hOcc, hRev⟩
        have hOwner :=
          rootedOwner_eq_emptySide_of_root_pos
            C ambientRoot B hRootPos hEmpty
        have hEq :=
          auxEdgeContribution_eq_emptySide_charge
            C ambientRoot hScores B hOcc hEmpty
        rw [hEq, hOwner]
        have hRootWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.root
        have hParentWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.parent
        linarith
      · have hEmpty : ¬ B.Occupied C := by
          intro hOcc
          exact hEdge ⟨hOcc, hRevOcc⟩
        have hOwner :=
          rootedOwner_eq_emptySide_of_root_pos
            C ambientRoot B.reverseBranch hRootPos hEmpty
        have hEq :=
          auxEdgeContribution_eq_emptySide_charge
            C ambientRoot hScores B.reverseBranch hRevOcc hEmpty
        have hOwner' : B.rootedOwner ambientRoot = B.root := by
          simpa [rootedOwner_reverse] using hOwner
        have hEq' :
            auxEdgeContribution C ambientRoot hScores B =
              auxWeightInt C ambientRoot hScores B.root *
                scoreDefect T C B.root := by
          simpa using hEq
        rw [hEq', hOwner']
        have hRootWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.root
        have hParentWeight :=
          auxWeightInt_nonneg C ambientRoot hScores B.parent
        linarith
    simpa [retainedDefectCharge, emptyBoundaryCharge, hEdge, hNondef,
      add_assoc] using hOwnerBound

end OrientedBranch

end TreeStack

/- Source module: TreeStack.GlobalCharge.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Every undirected edge has a dart presentation. -/
theorem exists_edgeDart (e : T.graph.edgeFinset) :
    ∃ d : T.graph.Dart, d.edge = e.1 := by
  rcases Sym2.mk_surjective e.1 with ⟨⟨u, v⟩, huv⟩
  have hedge : e.1 ∈ T.graph.edgeSet :=
    SimpleGraph.mem_edgeFinset.mp e.2
  have hadj : T.graph.Adj u v := by
    rw [← huv] at hedge
    simpa using hedge
  refine ⟨⟨(u, v), hadj⟩, ?_⟩
  simpa using huv

/-- A fixed choice of orientation for each ambient undirected edge.  All later
quantities are proved independent of this presentation. -/
noncomputable def edgeDart (e : T.graph.edgeFinset) : T.graph.Dart :=
  Classical.choose (exists_edgeDart (T := T) e)

@[simp] theorem edgeDart_edge (e : T.graph.edgeFinset) :
    (edgeDart (T := T) e).edge = e.1 :=
  Classical.choose_spec (exists_edgeDart (T := T) e)

/-- The chosen oriented-branch presentation of an ambient edge. -/
noncomputable def edgeBranch (e : T.graph.edgeFinset) : OrientedBranch T :=
  incidentBranch T (edgeDart (T := T) e).snd
    (edgeDart (T := T) e).fst (edgeDart (T := T) e).adj

@[simp] theorem edgeBranch_root (e : T.graph.edgeFinset) :
    (edgeBranch (T := T) e).root = (edgeDart (T := T) e).fst := rfl

@[simp] theorem edgeBranch_parent (e : T.graph.edgeFinset) :
    (edgeBranch (T := T) e).parent = (edgeDart (T := T) e).snd := rfl

theorem edgeBranch_edge (e : T.graph.edgeFinset) :
    s((edgeBranch (T := T) e).root, (edgeBranch (T := T) e).parent) = e.1 := by
  exact edgeDart_edge (T := T) e

/-- The ambient-root owner, viewed as a function on undirected edge indices. -/
noncomputable def edgeOwner (ambientRoot : V)
    (e : T.graph.edgeFinset) : V :=
  (edgeBranch (T := T) e).rootedOwner ambientRoot

/-- Rooted owners are injective on all ambient tree edges. -/
theorem edgeOwner_injective (ambientRoot : V) :
    Function.Injective (edgeOwner (T := T) ambientRoot) := by
  intro e f hOwner
  apply Subtype.ext
  have hEdge :=
    edge_eq_of_rootedOwner_eq ambientRoot
      (edgeBranch (T := T) e) (edgeBranch (T := T) f) hOwner
  rw [edgeBranch_edge (T := T) e, edgeBranch_edge (T := T) f] at hEdge
  exact hEdge

/-- Integer weighted mass for the auxiliary powers-of-two weights. -/
noncomputable def auxWeightedMass
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V, auxWeightInt C ambientRoot hScores v * (C v : ℤ)

/-- Total available weighted vertex-defect budget. -/
noncomputable def auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V,
    auxWeightInt C ambientRoot hScores v * scoreDefect T C v

/-- Weighted degree potential appearing after defect cancellation. -/
noncomputable def auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V, (T.graph.degree v : ℤ) *
    auxWeightInt C ambientRoot hScores v

/-- The owner charges over all ambient edges fit inside the total vertex
defect budget, by injectivity of the rooted-owner assignment. -/
theorem sum_edgeOwner_charge_le_auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
        scoreDefect T C (edgeOwner ambientRoot e)) ≤
      auxDefectBudget C ambientRoot hScores := by
  let f : V → ℤ := fun v =>
    auxWeightInt C ambientRoot hScores v * scoreDefect T C v
  have hf : ∀ v, 0 ≤ f v := by
    intro v
    exact mul_nonneg
      (auxWeightInt_nonneg C ambientRoot hScores v)
      ((scoreDefect_nonneg_iff T C v).2 (hScores v))
  let owner : T.graph.edgeFinset → V := edgeOwner ambientRoot
  have hOwner : Function.Injective owner :=
    edgeOwner_injective (T := T) ambientRoot
  calc
    (∑ e : T.graph.edgeFinset,
        auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
          scoreDefect T C (edgeOwner ambientRoot e)) =
        ∑ e : T.graph.edgeFinset, f (owner e) := by rfl
    _ = ∑ v ∈ (Finset.univ : Finset T.graph.edgeFinset).image owner, f v := by
      rw [Finset.sum_image]
      intro e _ g _ heg
      exact hOwner heg
    _ ≤ ∑ v : V, f v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
        (fun v _ _ => hf v)
    _ = auxDefectBudget C ambientRoot hScores := by
      rfl

/-- The two distinct edge-level cancellation mechanisms, packaged on the
finite undirected-edge index. -/
noncomputable def edgeSeparatedCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) : ℤ :=
  retainedDefectCharge C ambientRoot hScores (edgeBranch e) +
    emptyBoundaryCharge C ambientRoot hScores (edgeBranch e)

/-- A separated edge charge never exceeds the single rooted-owner defect
budget assigned to that ambient edge. -/
theorem edgeSeparatedCharge_le_owner_charge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    edgeSeparatedCharge C ambientRoot hScores e ≤
      auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
        scoreDefect T C (edgeOwner ambientRoot e) := by
  let B := edgeBranch (T := T) e
  have hBudget :
      0 ≤ auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
        scoreDefect T C (B.rootedOwner ambientRoot) :=
    mul_nonneg
      (auxWeightInt_nonneg C ambientRoot hScores _)
      ((scoreDefect_nonneg_iff T C _).2 (hScores _))
  by_cases hEdge : B.SupportEdge C
  · by_cases hDef : B.DefectiveSupportEdge C
    · simp [edgeSeparatedCharge, retainedDefectCharge, emptyBoundaryCharge,
        edgeOwner, B, hEdge, hDef]
    · simpa [edgeSeparatedCharge, retainedDefectCharge, emptyBoundaryCharge,
        edgeOwner, B, hEdge, hDef] using hBudget
  · have hDef : ¬ B.DefectiveSupportEdge C := by
      intro h
      exact hEdge h.1
    simp [edgeSeparatedCharge, retainedDefectCharge, emptyBoundaryCharge,
      edgeOwner, B, hEdge, hDef]

/-- The total separated charge is bounded by the available weighted vertex
defect budget.  Injectivity is used only after retained-defect and
nonretained-`EMPTY` charges have been distinguished. -/
theorem sum_edgeSeparatedCharge_le_auxDefectBudget
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      edgeSeparatedCharge C ambientRoot hScores e) ≤
      auxDefectBudget C ambientRoot hScores := by
  calc
    (∑ e : T.graph.edgeFinset,
        edgeSeparatedCharge C ambientRoot hScores e) ≤
        ∑ e : T.graph.edgeFinset,
          auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
            scoreDefect T C (edgeOwner ambientRoot e) := by
      exact Finset.sum_le_sum fun e _ =>
        edgeSeparatedCharge_le_owner_charge C ambientRoot hScores e
    _ ≤ auxDefectBudget C ambientRoot hScores :=
      sum_edgeOwner_charge_le_auxDefectBudget C ambientRoot hScores

/-- The uniform local edge inequality, packaged on the fixed finite edge
index while preserving the separation between retained defect charging and
literal-`EMPTY` boundary cancellation. -/
theorem edgeContribution_le_endpoint_add_separated_charge
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    auxEdgeContribution C ambientRoot hScores (edgeBranch e) ≤
      auxWeightInt C ambientRoot hScores (edgeBranch e).root +
        auxWeightInt C ambientRoot hScores (edgeBranch e).parent +
        edgeSeparatedCharge C ambientRoot hScores e := by
  simpa [edgeSeparatedCharge, add_assoc] using
    auxEdgeContribution_le_endpoint_add_separated_charges
      C ambientRoot hRootPos hScores (edgeBranch e)

/-- The two darts belonging to a chosen undirected edge presentation. -/
noncomputable def dartOfEdgeBool
    (p : T.graph.edgeFinset × Bool) : T.graph.Dart :=
  if p.2 then (edgeDart (T := T) p.1).symm else edgeDart (T := T) p.1

@[simp] theorem dartOfEdgeBool_edge
    (p : T.graph.edgeFinset × Bool) :
    (dartOfEdgeBool (T := T) p).edge = p.1.1 := by
  rcases p with ⟨e, b⟩
  cases b <;> simp [dartOfEdgeBool, edgeDart_edge]

theorem dartOfEdgeBool_injective :
    Function.Injective (dartOfEdgeBool (T := T)) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  have hEdge : e = f := by
    apply Subtype.ext
    have h' := congrArg SimpleGraph.Dart.edge h
    simpa using h'
  subst f
  cases b <;> cases c
  · rfl
  · have h' : edgeDart (T := T) e =
        (edgeDart (T := T) e).symm := by
      simpa [dartOfEdgeBool] using h
    exact ((edgeDart (T := T) e).symm_ne h'.symm).elim
  · have h' : (edgeDart (T := T) e).symm =
        edgeDart (T := T) e := by
      simpa [dartOfEdgeBool] using h
    exact ((edgeDart (T := T) e).symm_ne h').elim
  · rfl

theorem dartOfEdgeBool_surjective :
    Function.Surjective (dartOfEdgeBool (T := T)) := by
  intro d
  let e : T.graph.edgeFinset :=
    ⟨d.edge, SimpleGraph.mem_edgeFinset.mpr d.edge_mem⟩
  have hSameEdge : (edgeDart (T := T) e).edge = d.edge := by
    exact edgeDart_edge (T := T) e
  rcases (SimpleGraph.dart_edge_eq_iff (edgeDart (T := T) e) d).mp hSameEdge with
    h | h
  · refine ⟨(e, false), ?_⟩
    simpa [dartOfEdgeBool] using h
  · refine ⟨(e, true), ?_⟩
    simp [dartOfEdgeBool, h]

/-- Ambient darts are exactly an undirected edge together with a Boolean
choice of its two orientations. -/
noncomputable def edgeBoolEquivDart :
    T.graph.edgeFinset × Bool ≃ T.graph.Dart :=
  Equiv.ofBijective (dartOfEdgeBool (T := T))
    ⟨dartOfEdgeBool_injective (T := T),
      dartOfEdgeBool_surjective (T := T)⟩

@[simp] theorem edgeBoolEquivDart_apply
    (p : T.graph.edgeFinset × Bool) :
    edgeBoolEquivDart (T := T) p = dartOfEdgeBool (T := T) p :=
  rfl

/-- Sum a dart function by grouping the two orientations of each undirected
edge. -/
theorem sum_dart_eq_sum_edge_pair (f : T.graph.Dart → ℤ) :
    (∑ d : T.graph.Dart, f d) =
      ∑ e : T.graph.edgeFinset,
        (f (edgeDart (T := T) e) + f (edgeDart (T := T) e).symm) := by
  calc
    (∑ d : T.graph.Dart, f d) =
        ∑ p : T.graph.edgeFinset × Bool,
          f (edgeBoolEquivDart (T := T) p) := by
      exact (Equiv.sum_comp (edgeBoolEquivDart (T := T)) f).symm
    _ = ∑ e : T.graph.edgeFinset,
          (f (edgeDart (T := T) e) + f (edgeDart (T := T) e).symm) := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro e
      rw [Fintype.sum_bool]
      simp [edgeBoolEquivDart_apply, dartOfEdgeBool, add_comm]

/-- Reindex a dart by its head vertex and its tail as a neighbor of that
head. -/
def dartEquivHeadNeighbor :
    T.graph.Dart ≃ Σ v : V, T.graph.neighborSet v where
  toFun d := ⟨d.snd, ⟨d.fst, d.adj.symm⟩⟩
  invFun p := ⟨(p.2.1, p.1), p.2.2.symm⟩
  left_inv d := by ext <;> rfl
  right_inv p := by cases p; rfl

/-- A root message sum may be indexed only by genuine neighbors; all
nonneighbors already contribute zero by definition. -/
theorem sum_neighbor_rootMessageTerm_eq
    (C : Configuration V) (v : V) :
    (∑ u : T.graph.neighborSet v, rootMessageTerm T C v u) =
      rootMessageSum T C v := by
  classical
  rw [rootMessageSum]
  calc
    (∑ u : T.graph.neighborSet v, rootMessageTerm T C v u) =
        ∑ u ∈ T.graph.neighborFinset v, rootMessageTerm T C v u := by
      rw [Finset.sum_subtype (T.graph.neighborFinset v)]
      intro u
      simp [SimpleGraph.mem_neighborFinset, T.graph.adj_comm]
    _ = ∑ u : V, rootMessageTerm T C v u := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro u _ hu
      have hNotAdj : ¬ T.graph.Adj u v := by
        simpa [SimpleGraph.mem_neighborFinset, T.graph.adj_comm] using hu
      simp [rootMessageTerm, hNotAdj]

/-- One directed half of the weighted root-message sum. -/
noncomputable def auxDartMessageTerm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (d : T.graph.Dart) : ℤ :=
  auxWeightInt C ambientRoot hScores d.snd *
    rootMessageTerm T C d.snd d.fst

/-- Summing directed message terms by their head recovers the weighted rooted
message sums. -/
theorem sum_auxDartMessageTerm_eq
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ d : T.graph.Dart,
      auxDartMessageTerm C ambientRoot hScores d) =
      ∑ v : V,
        auxWeightInt C ambientRoot hScores v * rootMessageSum T C v := by
  calc
    (∑ d : T.graph.Dart,
        auxDartMessageTerm C ambientRoot hScores d) =
        ∑ p : Σ v : V, T.graph.neighborSet v,
          auxDartMessageTerm C ambientRoot hScores
            ((dartEquivHeadNeighbor (T := T)).symm p) := by
      exact
        (Equiv.sum_comp (dartEquivHeadNeighbor (T := T)).symm
          (auxDartMessageTerm C ambientRoot hScores)).symm
    _ = ∑ v : V,
          ∑ u : T.graph.neighborSet v,
            auxWeightInt C ambientRoot hScores v *
              rootMessageTerm T C v u := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ v : V,
          auxWeightInt C ambientRoot hScores v * rootMessageSum T C v := by
      apply Fintype.sum_congr
      intro v
      rw [← Finset.mul_sum, sum_neighbor_rootMessageTerm_eq]

/-- The two dart terms of an edge are exactly the negative of its auxiliary
edge contribution. -/
theorem auxDartMessageTerm_add_symm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (e : T.graph.edgeFinset) :
    auxDartMessageTerm C ambientRoot hScores (edgeDart e) +
        auxDartMessageTerm C ambientRoot hScores (edgeDart e).symm =
      -auxEdgeContribution C ambientRoot hScores (edgeBranch e) := by
  have hAdj := (edgeDart (T := T) e).adj
  have hAdjSymm := hAdj.symm
  simp [auxDartMessageTerm, auxEdgeContribution, edgeBranch,
    rootMessageTerm, incidentBranch, reverseBranch, hAdj, hAdjSymm]

/-- The sum of undirected weighted edge contributions is the negative
weighted root-message sum. -/
theorem sum_auxEdgeContribution_eq_neg_messages
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxEdgeContribution C ambientRoot hScores (edgeBranch e)) =
      -(∑ v : V,
        auxWeightInt C ambientRoot hScores v * rootMessageSum T C v) := by
  have hGroup :=
    sum_dart_eq_sum_edge_pair (T := T)
      (auxDartMessageTerm C ambientRoot hScores)
  simp_rw [auxDartMessageTerm_add_symm C ambientRoot hScores] at hGroup
  rw [sum_auxDartMessageTerm_eq C ambientRoot hScores] at hGroup
  calc
    (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) =
        -∑ e : T.graph.edgeFinset,
          -auxEdgeContribution C ambientRoot hScores (edgeBranch e) := by
      simp
    _ = -(∑ v : V,
          auxWeightInt C ambientRoot hScores v * rootMessageSum T C v) := by
      rw [← hGroup]

/-- Exact weighted score expansion: weighted mass is the edge contribution
sum minus the total weighted defect budget. -/
theorem auxWeightedMass_eq_edges_sub_defect
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores =
      (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) -
        auxDefectBudget C ambientRoot hScores := by
  rw [sum_auxEdgeContribution_eq_neg_messages]
  unfold auxWeightedMass auxDefectBudget scoreDefect score
  simp only [mul_neg, mul_add, Finset.sum_neg_distrib,
    Finset.sum_add_distrib]
  ring

/-- Sum of the two endpoint weights over undirected edges equals the weighted
degree potential. -/
theorem sum_edgeEndpointWeight_eq_auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      (auxWeightInt C ambientRoot hScores (edgeBranch e).root +
        auxWeightInt C ambientRoot hScores (edgeBranch e).parent)) =
      auxDegreePotential C ambientRoot hScores := by
  let f : T.graph.Dart → ℤ := fun d =>
    auxWeightInt C ambientRoot hScores d.snd
  have hGroup := sum_dart_eq_sum_edge_pair (T := T) f
  have hPair (e : T.graph.edgeFinset) :
      f (edgeDart e) + f (edgeDart e).symm =
        auxWeightInt C ambientRoot hScores (edgeBranch e).root +
          auxWeightInt C ambientRoot hScores (edgeBranch e).parent := by
    simp [f, edgeBranch, add_comm]
  simp_rw [hPair] at hGroup
  have hDart :
      (∑ d : T.graph.Dart, f d) =
        ∑ v : V, (T.graph.degree v : ℤ) *
          auxWeightInt C ambientRoot hScores v := by
    calc
      (∑ d : T.graph.Dart, f d) =
          ∑ p : Σ v : V, T.graph.neighborSet v,
            f ((dartEquivHeadNeighbor (T := T)).symm p) := by
        exact
          (Equiv.sum_comp (dartEquivHeadNeighbor (T := T)).symm f).symm
      _ = ∑ v : V,
            ∑ _u : T.graph.neighborSet v,
              auxWeightInt C ambientRoot hScores v := by
        rw [Fintype.sum_sigma]
        rfl
      _ = ∑ v : V, (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v := by
        apply Fintype.sum_congr
        intro v
        rw [Finset.sum_const, Finset.card_univ,
          SimpleGraph.card_neighborSet_eq_degree]
        simp [nsmul_eq_mul, mul_comm]
  rw [hDart] at hGroup
  exact hGroup.symm

set_option maxHeartbeats 800000 in
/-- Global sum of the local edge inequalities with retained-defect and
literal-`EMPTY` cancellation kept distinct until after summation. -/
theorem sum_auxEdgeContribution_le_degree_add_defect
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxEdgeContribution C ambientRoot hScores (edgeBranch e)) ≤
      auxDegreePotential C ambientRoot hScores +
        auxDefectBudget C ambientRoot hScores := by
  have hLocal :
      (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) ≤
        ∑ e : T.graph.edgeFinset,
          ((auxWeightInt C ambientRoot hScores (edgeBranch e).root +
              auxWeightInt C ambientRoot hScores (edgeBranch e).parent) +
            edgeSeparatedCharge C ambientRoot hScores e) := by
    exact Finset.sum_le_sum fun e _ =>
      edgeContribution_le_endpoint_add_separated_charge
        C ambientRoot hRootPos hScores e
  rw [Finset.sum_add_distrib,
    sum_edgeEndpointWeight_eq_auxDegreePotential] at hLocal
  exact hLocal.trans (add_le_add (le_refl _)
    (sum_edgeSeparatedCharge_le_auxDefectBudget
      C ambientRoot hScores))

set_option maxHeartbeats 200000 in
/-- Global weighted defect cancellation.  This is the major Stage 1 bound:
the defect budget in the exact score expansion cancels all owner charges. -/
theorem auxWeightedMass_le_auxDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores ≤
      auxDegreePotential C ambientRoot hScores := by
  rw [auxWeightedMass_eq_edges_sub_defect]
  have h :=
    sum_auxEdgeContribution_le_degree_add_defect
      C ambientRoot hRootPos hScores
  linarith

end OrientedBranch

end TreeStack

/- Source module: TreeStack.LeafSlack.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Ambient degree-one vertices.  Unlike `leafVertices T r`, this set is
independent of a chosen estimator root. -/
noncomputable def ambientLeaves : Finset V :=
  (Finset.univ : Finset V).filter fun v => T.graph.degree v = 1

/-- Number of ambient degree-one vertices. -/
noncomputable def ambientLeafCount : ℕ :=
  (ambientLeaves (T := T)).card

/-- The amount removed when converting auxiliary weighted mass back to ordinary
mass.  Every summand is nonnegative because every auxiliary weight is at least
one. -/
noncomputable def auxConfigurationSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v : V,
    (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ)

/-- The part of the weighted degree potential that must be removed at ambient
leaves. -/
noncomputable def auxLeafSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v ∈ ambientLeaves (T := T),
    (auxWeightInt C ambientRoot hScores v - 1)

/-- Integer auxiliary weights are at least one. -/
theorem one_le_auxWeightInt
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    1 ≤ auxWeightInt C ambientRoot hScores v := by
  have hpos : 0 < auxWeight C ambientRoot hScores v :=
    auxWeight_pos C ambientRoot hScores v
  have hone : 1 ≤ auxWeight C ambientRoot hScores v := by
    omega
  change (1 : ℤ) ≤ (auxWeight C ambientRoot hScores v : ℤ)
  exact Int.ofNat_le.mpr hone

/-- If an ambient leaf has non-unit auxiliary weight, then it is occupied.
Positive height supplies an incoming auxiliary arrow; that arrow is retained,
and the leaf-side deleted-edge branch is the singleton leaf. -/
theorem leaf_pos_of_auxWeightInt_ne_one
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V)
    (hLeaf : T.graph.degree v = 1)
    (hWeight : auxWeightInt C ambientRoot hScores v ≠ 1) :
    0 < C v := by
  have hHeightNe : auxHeight C ambientRoot hScores v ≠ 0 := by
    intro hZero
    apply hWeight
    simp [auxWeightInt, auxWeight, hZero]
  have hIncoming :
      ∃ u : V, AuxArrow (T := T) C ambientRoot u v := by
    by_contra hNoExists
    have hNo : ∀ u : V, ¬ AuxArrow (T := T) C ambientRoot u v := by
      intro u hArrow
      exact hNoExists ⟨u, hArrow⟩
    exact hHeightNe
      (auxHeight_eq_zero_of_no_incoming
        C ambientRoot hScores v hNo)
  rcases hIncoming with ⟨u, hArrow⟩
  let B : OrientedBranch T :=
    incidentBranch T v u (auxArrow_adj C ambientRoot hArrow)
  have hSupport : B.SupportEdge C := by
    simpa [B] using auxArrow_supportEdge C ambientRoot hArrow
  rcases hSupport.2 with ⟨x, hx, hxPos⟩
  have hLeaf' : T.graph.degree B.reverseBranch.root = 1 := by
    change T.graph.degree v = 1
    exact hLeaf
  have hSingleton : B.reverseBranch.vertices = {v} := by
    have h :=
      vertices_eq_singleton_of_degree_one B.reverseBranch hLeaf'
    simpa [B] using h
  have hxv : x = v := by
    rw [hSingleton] at hx
    simpa using hx
  simpa [hxv] using hxPos

/-- At an ambient leaf, the configuration-weight slack pays the entire excess
of the auxiliary leaf weight over one. -/
theorem leafWeightSlackTerm_le_configurationSlackTerm
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V)
    (hLeaf : T.graph.degree v = 1) :
    auxWeightInt C ambientRoot hScores v - 1 ≤
      (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
  have hWeightOne :=
    one_le_auxWeightInt C ambientRoot hScores v
  by_cases hEq : auxWeightInt C ambientRoot hScores v = 1
  · simp [hEq]
  · have hCPos :=
      leaf_pos_of_auxWeightInt_ne_one
        C ambientRoot hScores v hLeaf hEq
    have hCOneNat : 1 ≤ C v := by omega
    have hCOne : (1 : ℤ) ≤ (C v : ℤ) := by
      exact_mod_cast hCOneNat
    calc
      auxWeightInt C ambientRoot hScores v - 1 =
          (auxWeightInt C ambientRoot hScores v - 1) * 1 := by ring
      _ ≤
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
        exact mul_le_mul_of_nonneg_left hCOne
          (sub_nonneg.mpr hWeightOne)

/-- Every configuration-slack summand is nonnegative. -/
theorem configurationSlackTerm_nonneg
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    0 ≤
      (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
  exact mul_nonneg
    (sub_nonneg.mpr (one_le_auxWeightInt C ambientRoot hScores v))
    (by positivity)

/-- The exact conversion identity from weighted mass to ordinary mass. -/
theorem auxWeightedMass_sub_configurationSlack_eq_mass
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores -
        auxConfigurationSlack C ambientRoot hScores =
      (mass C : ℤ) := by
  unfold auxWeightedMass auxConfigurationSlack
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ v : V,
        (auxWeightInt C ambientRoot hScores v * (C v : ℤ) -
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ))) =
        ∑ v : V, (C v : ℤ) := by
      apply Fintype.sum_congr
      intro v
      ring
    _ = (mass C : ℤ) := by
      simp [mass]

/-- Occupied ambient leaves pay all of the leaf-weight slack. -/
theorem auxLeafSlack_le_auxConfigurationSlack
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxLeafSlack C ambientRoot hScores ≤
      auxConfigurationSlack C ambientRoot hScores := by
  unfold auxLeafSlack auxConfigurationSlack
  calc
    (∑ v ∈ ambientLeaves (T := T),
        (auxWeightInt C ambientRoot hScores v - 1)) ≤
        ∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
      exact Finset.sum_le_sum fun v hv => by
        have hLeaf : T.graph.degree v = 1 := by
          simpa [ambientLeaves] using hv
        exact
          leafWeightSlackTerm_le_configurationSlackTerm
            C ambientRoot hScores v hLeaf
    _ ≤ ∑ v : V,
          (auxWeightInt C ambientRoot hScores v - 1) * (C v : ℤ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun v _ _ =>
          configurationSlackTerm_nonneg C ambientRoot hScores v)

/-- Ordinary mass is bounded by the weighted degree potential after removing
the leaf-weight slack.  This is the ambient-tree leaf-slack conversion and
does not require transporting the configuration to a support subtype. -/
theorem mass_le_auxDegreePotential_sub_leafSlack
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (mass C : ℤ) ≤
      auxDegreePotential C ambientRoot hScores -
        auxLeafSlack C ambientRoot hScores := by
  have hWeighted :=
    auxWeightedMass_le_auxDegreePotential
      C ambientRoot hRootPos hScores
  have hSlack :=
    auxLeafSlack_le_auxConfigurationSlack
      C ambientRoot hScores
  have hMass :=
    auxWeightedMass_sub_configurationSlack_eq_mass
      C ambientRoot hScores
  linarith

/-- Ambient vertices of degree greater than one. -/
noncomputable def ambientInternalVertices : Finset V :=
  (Finset.univ : Finset V).filter fun v => 1 < T.graph.degree v

/-- The internal-vertex part of the auxiliary degree potential. -/
noncomputable def auxInternalDegreePotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  ∑ v ∈ ambientInternalVertices (T := T),
    (T.graph.degree v : ℤ) * auxWeightInt C ambientRoot hScores v

/-- Compact auxiliary potential after the occupied-leaf slack has removed the
unwanted powers of two at leaves. -/
noncomputable def auxCompactPotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) : ℤ :=
  (ambientLeafCount (T := T) : ℤ) +
    auxInternalDegreePotential C ambientRoot hScores

/-- The rooted internal part of the Csernák--Soukup estimator. -/
noncomputable def rootedInternalPotential
    (T : FiniteTree V) (r : V) : ℕ :=
  ∑ v ∈ ambientInternalVertices (T := T),
    T.graph.degree v * 2 ^ T.graph.dist r v

theorem ambientLeaves_disjoint_ambientInternal :
    Disjoint
      (ambientLeaves (T := T))
      (ambientInternalVertices (T := T)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvLeaf hvInternal
  have hLeaf : T.graph.degree v = 1 := by
    simpa [ambientLeaves] using hvLeaf
  have hInternal : 1 < T.graph.degree v := by
    simpa [ambientInternalVertices] using hvInternal
  omega

/-- In a nontrivial tree, every vertex is either a leaf or has degree greater
than one. -/
theorem ambientLeaves_union_ambientInternal [Nontrivial V] :
    ambientLeaves (T := T) ∪ ambientInternalVertices (T := T) =
      (Finset.univ : Finset V) := by
  classical
  ext v
  have hdeg :
      0 < T.graph.degree v :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial v
  simp [ambientLeaves, ambientInternalVertices]
  omega

/-- Split the weighted degree potential into leaf and internal terms. -/
theorem auxDegreePotential_eq_leaf_add_internal [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxDegreePotential C ambientRoot hScores =
      (∑ v ∈ ambientLeaves (T := T),
        auxWeightInt C ambientRoot hScores v) +
      auxInternalDegreePotential C ambientRoot hScores := by
  classical
  unfold auxDegreePotential auxInternalDegreePotential
  have hDis :=
    ambientLeaves_disjoint_ambientInternal (T := T)
  have hUnion :=
    ambientLeaves_union_ambientInternal (T := T)
  have hLeafSum :
      (∑ v ∈ ambientLeaves (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v) =
        ∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hLeaf : T.graph.degree v = 1 := by
      simpa [ambientLeaves] using hv
    simp [hLeaf]
  calc
    (∑ v : V, (T.graph.degree v : ℤ) *
        auxWeightInt C ambientRoot hScores v) =
      ∑ v ∈
          (ambientLeaves (T := T) ∪
            ambientInternalVertices (T := T)),
        (T.graph.degree v : ℤ) *
          auxWeightInt C ambientRoot hScores v := by
      rw [hUnion]
    _ =
      (∑ v ∈ ambientLeaves (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v) +
        ∑ v ∈ ambientInternalVertices (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v := by
      rw [Finset.sum_union hDis]
    _ =
      (∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v) +
        ∑ v ∈ ambientInternalVertices (T := T),
          (T.graph.degree v : ℤ) *
            auxWeightInt C ambientRoot hScores v := by
      rw [hLeafSum]

/-- Removing the leaf slack from the degree potential leaves exactly one unit
per ambient leaf plus the weighted internal-vertex potential. -/
theorem auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
    [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxDegreePotential C ambientRoot hScores -
        auxLeafSlack C ambientRoot hScores =
      auxCompactPotential C ambientRoot hScores := by
  rw [auxDegreePotential_eq_leaf_add_internal
    C ambientRoot hScores]
  unfold auxLeafSlack auxCompactPotential ambientLeafCount
  have hLeafDiff :
      (∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v) -
        (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1)) =
        ((ambientLeaves (T := T)).card : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v -
            (auxWeightInt C ambientRoot hScores v - 1))) =
          ∑ _v ∈ ambientLeaves (T := T), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = ((ambientLeaves (T := T)).card : ℤ) := by
        simp
  calc
    ((∑ v ∈ ambientLeaves (T := T),
        auxWeightInt C ambientRoot hScores v) +
        auxInternalDegreePotential C ambientRoot hScores) -
        (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1)) =
      ((∑ v ∈ ambientLeaves (T := T),
          auxWeightInt C ambientRoot hScores v) -
        (∑ v ∈ ambientLeaves (T := T),
          (auxWeightInt C ambientRoot hScores v - 1))) +
        auxInternalDegreePotential C ambientRoot hScores := by
      ring
    _ = ((ambientLeaves (T := T)).card : ℤ) +
        auxInternalDegreePotential C ambientRoot hScores := by
      rw [hLeafDiff]

/-- Final ordinary-mass form of the leaf-slack inequality. -/
theorem mass_le_auxCompactPotential [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (mass C : ℤ) ≤
      auxCompactPotential C ambientRoot hScores := by
  rw [← auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
    C ambientRoot hScores]
  exact
    mass_le_auxDegreePotential_sub_leafSlack
      C ambientRoot hRootPos hScores

theorem ambientLeaves_eq_insert_leafVertices_of_root_leaf
    (T : FiniteTree V) (r : V)
    (hLeaf : T.graph.degree r = 1) :
    ambientLeaves (T := T) = insert r (leafVertices T r) := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientLeaves, leafVertices, hLeaf]
  · simp [ambientLeaves, leafVertices, hvr]

theorem ambientLeaves_eq_leafVertices_of_root_not_leaf
    (T : FiniteTree V) (r : V)
    (hNotLeaf : T.graph.degree r ≠ 1) :
    ambientLeaves (T := T) = leafVertices T r := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientLeaves, leafVertices, hNotLeaf]
  · simp [ambientLeaves, leafVertices, hvr]

theorem ambientInternal_eq_nonRootInternal_of_root_not_internal
    (T : FiniteTree V) (r : V)
    (hNotInternal : ¬ 1 < T.graph.degree r) :
    ambientInternalVertices (T := T) =
      nonRootInternalVertices T r := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientInternalVertices, nonRootInternalVertices, hNotInternal]
  · simp [ambientInternalVertices, nonRootInternalVertices, hvr]

theorem ambientInternal_eq_insert_nonRootInternal_of_root_internal
    (T : FiniteTree V) (r : V)
    (hInternal : 1 < T.graph.degree r) :
    ambientInternalVertices (T := T) =
      insert r (nonRootInternalVertices T r) := by
  classical
  ext v
  by_cases hvr : v = r
  · subst v
    simp [ambientInternalVertices, nonRootInternalVertices, hInternal]
  · simp [ambientInternalVertices, nonRootInternalVertices, hvr]

/-- Root-insensitive decomposition of the rooted estimator.  This statement
handles degree-one roots explicitly: the root term in `sigma` exactly replaces
the leaf omitted from `leafCount T r`. -/
theorem rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
    [Nontrivial V] (T : FiniteTree V) (r : V) :
    rootEstimate T r =
      1 + ambientLeafCount (T := T) + rootedInternalPotential T r := by
  classical
  have hdeg :
      0 < T.graph.degree r :=
    T.isTree.connected.preconnected.degree_pos_of_nontrivial r
  by_cases hLeaf : T.graph.degree r = 1
  · have hLeaves :=
      ambientLeaves_eq_insert_leafVertices_of_root_leaf T r hLeaf
    have hrNotLeaf : r ∉ leafVertices T r := by
      simp [leafVertices]
    have hLeafCount :
        ambientLeafCount (T := T) = leafCount T r + 1 := by
      unfold ambientLeafCount leafCount
      rw [hLeaves]
      simp [hrNotLeaf]
    have hNotInternal : ¬ 1 < T.graph.degree r := by
      omega
    have hInternal :=
      ambientInternal_eq_nonRootInternal_of_root_not_internal
        T r hNotInternal
    have hPotential :
        rootedInternalPotential T r =
          ∑ v ∈ nonRootInternalVertices T r,
            T.graph.degree v * 2 ^ T.graph.dist r v := by
      unfold rootedInternalPotential
      rw [hInternal]
    rw [rootEstimate_corrected_expansion, hLeafCount, hPotential, hLeaf]
    omega
  · have hInternalRoot : 1 < T.graph.degree r := by
      omega
    have hLeaves :=
      ambientLeaves_eq_leafVertices_of_root_not_leaf T r hLeaf
    have hLeafCount :
        ambientLeafCount (T := T) = leafCount T r := by
      unfold ambientLeafCount leafCount
      rw [hLeaves]
    have hInternal :=
      ambientInternal_eq_insert_nonRootInternal_of_root_internal
        T r hInternalRoot
    have hrNotInternal : r ∉ nonRootInternalVertices T r := by
      simp [nonRootInternalVertices]
    have hPotential :
        rootedInternalPotential T r =
          T.graph.degree r +
            ∑ v ∈ nonRootInternalVertices T r,
              T.graph.degree v * 2 ^ T.graph.dist r v := by
      unfold rootedInternalPotential
      rw [hInternal, Finset.sum_insert hrNotInternal]
      simp
    rw [rootEstimate_corrected_expansion, hLeafCount, hPotential]
    omega

end OrientedBranch

end TreeStack

/- Source module: TreeStack.HeightSource.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- Positive auxiliary height is realized by an incoming auxiliary arrow whose
height is exactly one smaller. -/
theorem exists_auxHeight_predecessor_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    ∃ u : V,
      AuxArrow (T := T) C ambientRoot u v ∧
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
  let f : V → ℕ := fun u =>
    if h : AuxArrow (T := T) C ambientRoot u v then
      auxHeight C ambientRoot hScores u + 1
    else
      0
  have hNonempty : (Finset.univ : Finset V).Nonempty :=
    ⟨v, Finset.mem_univ v⟩
  rcases Finset.exists_mem_eq_sup (Finset.univ : Finset V) hNonempty f with
    ⟨u, -, hSup⟩
  have hEq :
      auxHeight C ambientRoot hScores v = f u := by
    rw [auxHeight]
    exact hSup
  by_cases hArrow : AuxArrow (T := T) C ambientRoot u v
  · refine ⟨u, hArrow, ?_⟩
    simpa [f, hArrow] using hEq.symm
  · have hZero : auxHeight C ambientRoot hScores v = 0 := by
      simpa [f, hArrow] using hEq
    omega

/-- A canonical predecessor realizing positive auxiliary height.  At height
zero it is harmlessly defined to be the vertex itself. -/
noncomputable def auxParent
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : V :=
  if h : 0 < auxHeight C ambientRoot hScores v then
    Classical.choose
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v h)
  else
    v

theorem auxParent_arrow_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    AuxArrow (T := T) C ambientRoot
      (auxParent C ambientRoot hScores v) v := by
  rw [auxParent, dif_pos hPos]
  exact
    (Classical.choose_spec
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v hPos)).1

theorem auxParent_height_add_one
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxHeight C ambientRoot hScores
        (auxParent C ambientRoot hScores v) + 1 =
      auxHeight C ambientRoot hScores v := by
  rw [auxParent, dif_pos hPos]
  exact
    (Classical.choose_spec
      (exists_auxHeight_predecessor_of_pos
        C ambientRoot hScores v hPos)).2

/-- The canonical height-realizing walk, written from a vertex backwards to
its height-zero source.  Heights strictly decrease at each recursive step. -/
noncomputable def auxSourceWalk
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : Σ r : V, T.graph.Walk v r :=
  if hZero : auxHeight C ambientRoot hScores v = 0 then
    ⟨v, SimpleGraph.Walk.nil⟩
  else
    let hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    let tailCert := auxSourceWalk C ambientRoot hScores u
    ⟨tailCert.1,
      SimpleGraph.Walk.cons
        (auxArrow_adj C ambientRoot
          (auxParent_arrow_of_pos C ambientRoot hScores v hPos)).symm
        tailCert.2⟩
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v
      (Nat.pos_of_ne_zero hZero)
  omega

/-- One-step equation for the canonical source walk at height zero. -/
theorem auxSourceWalk_eq_of_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hZero : auxHeight C ambientRoot hScores v = 0) :
    auxSourceWalk C ambientRoot hScores v =
      ⟨v, SimpleGraph.Walk.nil⟩ := by
  rw [auxSourceWalk]
  simp [hZero]

/-- One-step equation for the canonical source walk at positive height. -/
theorem auxSourceWalk_eq_of_height_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxSourceWalk C ambientRoot hScores v =
      let u := auxParent C ambientRoot hScores v
      let tailCert := auxSourceWalk C ambientRoot hScores u
      ⟨tailCert.1,
        SimpleGraph.Walk.cons
          (auxArrow_adj C ambientRoot
            (auxParent_arrow_of_pos C ambientRoot hScores v hPos)).symm
          tailCert.2⟩ := by
  rw [auxSourceWalk]
  simp only [dif_neg (Nat.ne_of_gt hPos)]

/-- The height-zero source selected by the canonical predecessor chain. -/
noncomputable def auxSource
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) : V :=
  (auxSourceWalk C ambientRoot hScores v).1

/-- The underlying canonical walk from a vertex to its auxiliary source. -/
noncomputable def auxWalk
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    T.graph.Walk v (auxSource C ambientRoot hScores v) :=
  (auxSourceWalk C ambientRoot hScores v).2

/-- Every vertex occurring on the canonical source walk has height at most the
height of the starting vertex. -/
theorem auxSourceWalk_support_height_le
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v x : V)
    (hx : x ∈ (auxSourceWalk C ambientRoot hScores v).2.support) :
    auxHeight C ambientRoot hScores x ≤
      auxHeight C ambientRoot hScores v := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero] at hx
    simp at hx
    subst x
    exact le_rfl
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hEq :
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
      simpa [u] using
        auxParent_height_add_one C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos] at hx
    simp only [SimpleGraph.Walk.support_cons] at hx
    rcases List.mem_cons.mp hx with hEqX | hxTail
    · subst x
      exact le_rfl
    · have hRec :=
        auxSourceWalk_support_height_le
          C ambientRoot hScores u x hxTail
      omega
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- The canonical source walk is simple because height strictly decreases
backwards along it. -/
theorem auxSourceWalk_isPath
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    (auxSourceWalk C ambientRoot hScores v).2.IsPath := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero]
    simp
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hEq :
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
      simpa [u] using
        auxParent_height_add_one C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos]
    have hTail :
        (auxSourceWalk C ambientRoot hScores u).2.IsPath :=
      auxSourceWalk_isPath C ambientRoot hScores u
    apply (SimpleGraph.Walk.cons_isPath_iff _ _).2
    refine ⟨hTail, ?_⟩
    intro hvMem
    have hLe :=
      auxSourceWalk_support_height_le
        C ambientRoot hScores u v hvMem
    omega
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- The canonical source walk has exactly the recorded auxiliary height. -/
theorem auxSourceWalk_length
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    (auxSourceWalk C ambientRoot hScores v).2.length =
      auxHeight C ambientRoot hScores v := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero]
    simp [hZero]
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hEq :
        auxHeight C ambientRoot hScores u + 1 =
          auxHeight C ambientRoot hScores v := by
      simpa [u] using
        auxParent_height_add_one C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos]
    simp only [SimpleGraph.Walk.length_cons]
    rw [auxSourceWalk_length C ambientRoot hScores u]
    omega
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- Auxiliary height is a genuine tree distance from the canonical source. -/
theorem auxHeight_eq_dist_auxSource
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    auxHeight C ambientRoot hScores v =
      T.graph.dist (auxSource C ambientRoot hScores v) v := by
  have hPath :=
    auxSourceWalk_isPath C ambientRoot hScores v
  have hDist :=
    tree_path_length_eq_dist
      (T := T) (auxSourceWalk C ambientRoot hScores v).2 hPath
  have hLen :=
    auxSourceWalk_length C ambientRoot hScores v
  change
    auxHeight C ambientRoot hScores v =
      T.graph.dist (auxSource C ambientRoot hScores v) v
  calc
    auxHeight C ambientRoot hScores v =
        (auxSourceWalk C ambientRoot hScores v).2.length := hLen.symm
    _ = T.graph.dist v (auxSource C ambientRoot hScores v) := hDist
    _ = T.graph.dist (auxSource C ambientRoot hScores v) v :=
      T.graph.dist_comm

/-- A zero-height vertex is its own canonical source. -/
theorem auxSource_eq_self_of_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hZero : auxHeight C ambientRoot hScores v = 0) :
    auxSource C ambientRoot hScores v = v := by
  unfold auxSource
  rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero]

/-- At positive height, passing to the canonical predecessor does not change
the canonical source. -/
theorem auxSource_auxParent_of_pos
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) (hPos : 0 < auxHeight C ambientRoot hScores v) :
    auxSource C ambientRoot hScores
        (auxParent C ambientRoot hScores v) =
      auxSource C ambientRoot hScores v := by
  unfold auxSource
  rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos]

/-- Every canonical source really has auxiliary height zero. -/
theorem auxSource_height_zero
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v : V) :
    auxHeight C ambientRoot hScores
      (auxSource C ambientRoot hScores v) = 0 := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSource_eq_self_of_height_zero
      C ambientRoot hScores v hZero]
    exact hZero
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    have hSource :=
      auxSource_auxParent_of_pos
        C ambientRoot hScores v hPos
    rw [← hSource]
    exact
      auxSource_height_zero C ambientRoot hScores
        (auxParent C ambientRoot hScores v)
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

/-- Every vertex appearing on the canonical source walk has the same canonical
source as the walk's starting vertex.  Thus source fibres are path-connected
inside the ambient tree. -/
theorem auxSource_eq_of_mem_auxSourceWalk_support
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (v x : V)
    (hx : x ∈ (auxSourceWalk C ambientRoot hScores v).2.support) :
    auxSource C ambientRoot hScores x =
      auxSource C ambientRoot hScores v := by
  by_cases hZero : auxHeight C ambientRoot hScores v = 0
  · rw [auxSourceWalk_eq_of_height_zero C ambientRoot hScores v hZero] at hx
    simp at hx
    subst x
    rfl
  · have hPos : 0 < auxHeight C ambientRoot hScores v :=
      Nat.pos_of_ne_zero hZero
    let u := auxParent C ambientRoot hScores v
    have hSource :
        auxSource C ambientRoot hScores u =
          auxSource C ambientRoot hScores v := by
      simpa [u] using
        auxSource_auxParent_of_pos C ambientRoot hScores v hPos
    rw [auxSourceWalk_eq_of_height_pos C ambientRoot hScores v hPos] at hx
    simp only [SimpleGraph.Walk.support_cons] at hx
    rcases List.mem_cons.mp hx with hEq | hxTail
    · subst x
      rfl
    · have hRec :=
        auxSource_eq_of_mem_auxSourceWalk_support
          C ambientRoot hScores u x hxTail
      exact hRec.trans hSource
termination_by auxHeight C ambientRoot hScores v
decreasing_by
  have hEq :=
    auxParent_height_add_one C ambientRoot hScores v hPos
  omega

end OrientedBranch

end TreeStack

/- Source module: TreeStack.Consolidation.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The fibre of the canonical height-zero source map.  These fibres are the
connected parts that will be consolidated to a single estimator root. -/
noncomputable def auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r : V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    auxSource C ambientRoot hScores v = r

@[simp] theorem mem_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r v : V) :
    v ∈ auxSourceFiber C ambientRoot hScores r ↔
      auxSource C ambientRoot hScores v = r := by
  simp [auxSourceFiber]

/-- Every vertex belongs to the fibre indexed by its canonical source. -/
theorem mem_auxSourceFiber_self_source
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    v ∈ auxSourceFiber C ambientRoot hScores
      (auxSource C ambientRoot hScores v) := by
  simp

/-- A source fibre is nonempty exactly when its index is itself a canonical
height-zero source. -/
theorem auxSourceFiber_nonempty_iff
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (r : V) :
    (auxSourceFiber C ambientRoot hScores r).Nonempty ↔
      auxHeight C ambientRoot hScores r = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hsrc : auxSource C ambientRoot hScores v = r := by
      simpa using hv
    rw [← hsrc]
    exact auxSource_height_zero C ambientRoot hScores v
  · intro hzero
    refine ⟨r, ?_⟩
    simp [auxSource_eq_self_of_height_zero C ambientRoot hScores r hzero]

/-- The canonical walk from a vertex stays entirely in its source fibre. -/
theorem auxWalk_support_subset_sourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) (v : V) :
    ∀ x ∈ (auxWalk C ambientRoot hScores v).support,
      x ∈ auxSourceFiber C ambientRoot hScores
        (auxSource C ambientRoot hScores v) := by
  intro x hx
  rw [mem_auxSourceFiber]
  exact
    auxSource_eq_of_mem_auxSourceWalk_support
      C ambientRoot hScores v x hx

/-- Any two vertices in one source fibre are joined by an ambient-tree walk
whose support stays in that fibre.  This is the path-connectedness interface
needed by the connected-partition consolidation argument. -/
theorem exists_walk_within_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r x y : V)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores r) :
    ∃ p : T.graph.Walk x y,
      ∀ z ∈ p.support,
        z ∈ auxSourceFiber C ambientRoot hScores r := by
  have hsx : auxSource C ambientRoot hScores x = r := by
    simpa using hx
  have hsy : auxSource C ambientRoot hScores y = r := by
    simpa using hy
  let px : T.graph.Walk x r :=
    (auxWalk C ambientRoot hScores x).copy rfl hsx
  let py : T.graph.Walk y r :=
    (auxWalk C ambientRoot hScores y).copy rfl hsy
  let p : T.graph.Walk x y := px.append py.reverse
  refine ⟨p, ?_⟩
  intro z hz
  have hz' :
      z ∈ px.support ∨ z ∈ py.support := by
    simpa [p] using hz
  rcases hz' with hzx | hzy
  · have hzsrc :=
      auxWalk_support_subset_sourceFiber C ambientRoot hScores x z
        (by simpa [px] using hzx)
    simpa [hsx] using hzsrc
  · have hzsrc :=
      auxWalk_support_subset_sourceFiber C ambientRoot hScores y z
        (by simpa [py] using hzy)
    simpa [hsy] using hzsrc

/-- Distinct canonical sources have disjoint fibres. -/
theorem auxSourceFiber_disjoint_of_ne
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s : V} (hrs : r ≠ s) :
    Disjoint
      (auxSourceFiber C ambientRoot hScores r)
      (auxSourceFiber C ambientRoot hScores s) := by
  rw [Finset.disjoint_left]
  intro v hvr hvs
  have hr : auxSource C ambientRoot hScores v = r := by
    simpa using hvr
  have hs : auxSource C ambientRoot hScores v = s := by
    simpa using hvs
  exact hrs (hr.symm.trans hs)

/-- A source fibre is path-connected by a simple ambient-tree path whose
support remains entirely inside the fibre. -/
theorem exists_path_within_auxSourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r x y : V)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores r) :
    ∃ p : T.graph.Walk x y,
      p.IsPath ∧
        ∀ z ∈ p.support,
          z ∈ auxSourceFiber C ambientRoot hScores r := by
  rcases
      exists_walk_within_auxSourceFiber
        C ambientRoot hScores r x y hx hy with
    ⟨w, hw⟩
  refine ⟨w.toPath, w.toPath.2, ?_⟩
  intro z hz
  exact hw z (w.support_toPath_subset_support hz)

/-- A finite carrier is tree-path-connected when every two of its vertices
are joined by a simple ambient-tree path whose support stays in the carrier. -/
def TreePathConnected (S : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ S → y ∈ S →
    ∃ p : T.graph.Walk x y,
      p.IsPath ∧ ∀ z ∈ p.support, z ∈ S

/-- Every canonical source fibre is tree-path-connected. -/
theorem auxSourceFiber_treePathConnected
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V) :
    TreePathConnected (T := T)
      (auxSourceFiber C ambientRoot hScores r) := by
  intro x y hx hy
  exact exists_path_within_auxSourceFiber
    C ambientRoot hScores r x y hx hy

/-- Generic boundary additivity for two disjoint path-connected carriers.
Because the ambient graph is a tree, concatenating an internal path in the
first carrier, the crossing edge, and an internal path in the second carrier
is itself the unique simple path between the endpoints. -/
theorem dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
    {A B : Finset V}
    (hA : TreePathConnected (T := T) A)
    (hB : TreePathConnected (T := T) B)
    (hDisj : Disjoint A B)
    {a b x y : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b)
    (hx : x ∈ A) (hy : y ∈ B) :
    T.graph.dist x y =
      T.graph.dist x a + 1 + T.graph.dist b y := by
  rcases hA hx ha with ⟨px, hpxPath, hpxCarrier⟩
  rcases hB hb hy with ⟨py, hpyPath, hpyCarrier⟩
  have hbNotPx : b ∉ px.support := by
    intro hbpx
    have hbA := hpxCarrier b hbpx
    exact (Finset.disjoint_left.mp hDisj) hbA hb
  let q : T.graph.Walk x b := px.concat hadj
  have hqPath : q.IsPath :=
    hpxPath.concat hbNotPx hadj
  have hbNotPyTail : b ∉ py.support.tail := by
    have hNodup := hpyPath.support_nodup
    rw [← py.cons_tail_support, List.nodup_cons] at hNodup
    exact hNodup.1
  have hSupportsDisjoint : q.support.Disjoint py.support.tail := by
    rw [List.disjoint_left]
    intro z hzq hzpyTail
    have hzpy : z ∈ py.support :=
      List.mem_of_mem_tail hzpyTail
    have hzB := hpyCarrier z hzpy
    have hzq' : z ∈ px.support ∨ z = b := by
      simpa [q] using hzq
    rcases hzq' with hzpx | rfl
    · have hzA := hpxCarrier z hzpx
      exact (Finset.disjoint_left.mp hDisj) hzA hzB
    · exact hbNotPyTail hzpyTail
  have hpPath : (q.append py).IsPath := by
    rw [SimpleGraph.Walk.isPath_def,
      SimpleGraph.Walk.support_append, List.nodup_append']
    exact
      ⟨hqPath.support_nodup,
        hpyPath.support_nodup.tail,
        hSupportsDisjoint⟩
  have hpxDist :=
    tree_path_length_eq_dist (T := T) px hpxPath
  have hpyDist :=
    tree_path_length_eq_dist (T := T) py hpyPath
  have hpDist :=
    tree_path_length_eq_dist (T := T) (q.append py) hpPath
  calc
    T.graph.dist x y = (q.append py).length := hpDist.symm
    _ = px.length + 1 + py.length := by simp [q]
    _ = T.graph.dist x a + 1 + T.graph.dist b y := by
      rw [hpxDist, hpyDist]

/-- A height profile is dominated on a carrier by a root when the root lies
in the carrier and every profile height is at most the ambient distance from
that root. -/
def HeightDominated
    (h : V → ℕ) (S : Finset V) (r : V) : Prop :=
  r ∈ S ∧ ∀ v ∈ S, h v ≤ T.graph.dist r v

/-- The union of two path-connected carriers joined by an ambient edge is
again path-connected. -/
theorem treePathConnected_union_of_adj
    {A B : Finset V}
    (hA : TreePathConnected (T := T) A)
    (hB : TreePathConnected (T := T) B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b) :
    TreePathConnected (T := T) (A ∪ B) := by
  intro x y hx hy
  rw [Finset.mem_union] at hx hy
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · rcases hA hxA hyA with ⟨p, hpPath, hpSupp⟩
      refine ⟨p, hpPath, ?_⟩
      intro z hz
      exact Finset.mem_union_left _ (hpSupp z hz)
    · rcases hA hxA ha with ⟨p, hpPath, hpSupp⟩
      rcases hB hb hyB with ⟨q, hqPath, hqSupp⟩
      let w : T.graph.Walk x y := (p.concat hadj).append q
      refine ⟨w.toPath, w.toPath.2, ?_⟩
      intro z hz
      have hzw : z ∈ w.support :=
        w.support_toPath_subset_support hz
      have hzCases :
          (z ∈ p.support ∨ z = b) ∨ z ∈ q.support := by
        simpa [w] using hzw
      rcases hzCases with (hzp | hzb) | hzq
      · exact Finset.mem_union_left _ (hpSupp z hzp)
      · subst z
        exact Finset.mem_union_right _ hb
      · exact Finset.mem_union_right _ (hqSupp z hzq)
  · rcases hy with hyA | hyB
    · rcases hB hxB hb with ⟨p, hpPath, hpSupp⟩
      rcases hA ha hyA with ⟨q, hqPath, hqSupp⟩
      let w : T.graph.Walk x y := (p.concat hadj.symm).append q
      refine ⟨w.toPath, w.toPath.2, ?_⟩
      intro z hz
      have hzw : z ∈ w.support :=
        w.support_toPath_subset_support hz
      have hzCases :
          (z ∈ p.support ∨ z = a) ∨ z ∈ q.support := by
        simpa [w] using hzw
      rcases hzCases with (hzp | hza) | hzq
      · exact Finset.mem_union_right _ (hpSupp z hzp)
      · subst z
        exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_left _ (hqSupp z hzq)
    · rcases hB hxB hyB with ⟨p, hpPath, hpSupp⟩
      refine ⟨p, hpPath, ?_⟩
      intro z hz
      exact Finset.mem_union_right _ (hpSupp z hz)

/-- Merge two disjoint connected dominated carriers across one boundary edge.
The root on the side whose boundary depth is large enough dominates the whole
union; if that comparison fails, the opposite root necessarily works. -/
theorem exists_heightDominatingRoot_union_of_adj
    (h : V → ℕ)
    {A B : Finset V}
    (hAConn : TreePathConnected (T := T) A)
    (hBConn : TreePathConnected (T := T) B)
    (hDisj : Disjoint A B)
    {a b r s : V}
    (ha : a ∈ A) (hb : b ∈ B)
    (hadj : T.graph.Adj a b)
    (hADom : HeightDominated (T := T) h A r)
    (hBDom : HeightDominated (T := T) h B s) :
    ∃ t : V,
      HeightDominated (T := T) h (A ∪ B) t := by
  rcases hADom with ⟨hrA, hAHeight⟩
  rcases hBDom with ⟨hsB, hBHeight⟩
  by_cases hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1
  · refine ⟨r, Finset.mem_union_left _ hrA, ?_⟩
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvA | hvB
    · exact hAHeight v hvA
    · have hCross :=
        dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
          hAConn hBConn hDisj ha hb hadj hrA hvB
      have hTri :
          T.graph.dist s v ≤
            T.graph.dist s b + T.graph.dist b v :=
        T.isTree.connected.dist_triangle
      have hBase := hBHeight v hvB
      rw [hCross]
      omega
  · have hDepth' :
        T.graph.dist r a ≤ T.graph.dist s b + 1 := by
      omega
    refine ⟨s, Finset.mem_union_right _ hsB, ?_⟩
    intro v hv
    rw [Finset.mem_union] at hv
    rcases hv with hvA | hvB
    · have hCross :=
        dist_eq_dist_add_one_add_dist_of_adj_disjoint_carriers
          hBConn hAConn hDisj.symm hb ha hadj.symm hsB hvA
      have hTri :
          T.graph.dist r v ≤
            T.graph.dist r a + T.graph.dist a v :=
        T.isTree.connected.dist_triangle
      have hBase := hAHeight v hvA
      rw [hCross]
      omega
    · exact hBHeight v hvB

/-- Every nonempty proper finite vertex carrier in a connected tree has an
ambient edge crossing from the carrier to its complement. -/
theorem exists_adj_mem_not_mem_of_nonempty_ne_univ
    (S : Finset V)
    (hNonempty : S.Nonempty)
    (hProper : S ≠ (Finset.univ : Finset V)) :
    ∃ a b : V, a ∈ S ∧ b ∉ S ∧ T.graph.Adj a b := by
  classical
  rcases hNonempty with ⟨x, hx⟩
  have hOutside : ∃ y : V, y ∉ S := by
    by_contra hOutside
    apply hProper
    rw [Finset.eq_univ_iff_forall]
    intro y
    by_contra hy
    exact hOutside ⟨y, hy⟩
  rcases hOutside with ⟨y, hy⟩
  rcases T.isTree.connected x y with ⟨p⟩
  have hCross :
      ∀ {u v : V} (q : T.graph.Walk u v),
        u ∈ S → v ∉ S →
          ∃ a b : V, a ∈ S ∧ b ∉ S ∧ T.graph.Adj a b := by
    intro u v q hu hv
    induction q with
    | nil =>
        exact (hv hu).elim
    | @cons u w v hadj q ih =>
        by_cases hw : w ∈ S
        · exact ih hw hv
        · exact ⟨u, w, hu, hw, hadj⟩
  exact hCross p hx hy

/-- Vertices whose selected canonical source belongs to a chosen source set. -/
noncomputable def auxSourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter fun v =>
    auxSource C ambientRoot hScores v ∈ R

@[simp] theorem mem_auxSourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (v : V) :
    v ∈ auxSourceCarrier C ambientRoot hScores R ↔
      auxSource C ambientRoot hScores v ∈ R := by
  simp [auxSourceCarrier]

/-- Inserting one source adds exactly its whole canonical fibre. -/
theorem auxSourceCarrier_insert
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (r : V) :
    auxSourceCarrier C ambientRoot hScores (insert r R) =
      auxSourceCarrier C ambientRoot hScores R ∪
        auxSourceFiber C ambientRoot hScores r := by
  ext v
  simp [auxSourceCarrier, auxSourceFiber, or_comm]

/-- A singleton source carrier is exactly its source fibre. -/
theorem auxSourceCarrier_singleton
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V) :
    auxSourceCarrier C ambientRoot hScores {r} =
      auxSourceFiber C ambientRoot hScores r := by
  ext v
  simp [auxSourceCarrier, auxSourceFiber]

/-- Selecting every source gives the whole ambient vertex set. -/
theorem auxSourceCarrier_univ
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxSourceCarrier C ambientRoot hScores (Finset.univ : Finset V) =
      (Finset.univ : Finset V) := by
  ext v
  simp [auxSourceCarrier]

/-- If a source has not yet been selected, its entire fibre is disjoint from
the current source carrier. -/
theorem auxSourceCarrier_disjoint_fiber_of_not_mem
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) {s : V} (hs : s ∉ R) :
    Disjoint
      (auxSourceCarrier C ambientRoot hScores R)
      (auxSourceFiber C ambientRoot hScores s) := by
  rw [Finset.disjoint_left]
  intro v hvCarrier hvFiber
  have hmem :
      auxSource C ambientRoot hScores v ∈ R := by
    simpa using hvCarrier
  have heq :
      auxSource C ambientRoot hScores v = s := by
    simpa using hvFiber
  rw [heq] at hmem
  exact hs hmem

/-- Every nonempty canonical source fibre is height-dominated by its own
source, in fact with equality pointwise. -/
theorem auxSourceFiber_heightDominated_of_nonempty
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V)
    (hNonempty : (auxSourceFiber C ambientRoot hScores r).Nonempty) :
    HeightDominated (T := T)
      (fun v => auxHeight C ambientRoot hScores v)
      (auxSourceFiber C ambientRoot hScores r) r := by
  have hZero :=
    (auxSourceFiber_nonempty_iff C ambientRoot hScores r).1 hNonempty
  have hr :
      r ∈ auxSourceFiber C ambientRoot hScores r := by
    simp [auxSource_eq_self_of_height_zero
      C ambientRoot hScores r hZero]
  refine ⟨hr, ?_⟩
  intro v hv
  have hsrc : auxSource C ambientRoot hScores v = r := by
    simpa using hv
  change auxHeight C ambientRoot hScores v ≤ T.graph.dist r v
  rw [auxHeight_eq_dist_auxSource, hsrc]

/-- Starting from any nonempty connected union of canonical source
fibres whose auxiliary height is dominated by one root, repeatedly adjoin the
source fibre across a boundary edge.  The process terminates when the carrier
is all vertices and returns one ambient root dominating every auxiliary
height. -/
theorem exists_global_heightDominatingRoot_from_sourceCarrier
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (R : Finset V) (r : V)
    (hConn :
      TreePathConnected (T := T)
        (auxSourceCarrier C ambientRoot hScores R))
    (hDom :
      HeightDominated (T := T)
        (fun v => auxHeight C ambientRoot hScores v)
        (auxSourceCarrier C ambientRoot hScores R) r) :
    ∃ t : V, ∀ v : V,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist t v := by
  let S := auxSourceCarrier C ambientRoot hScores R
  by_cases hFull : S = (Finset.univ : Finset V)
  · refine ⟨r, ?_⟩
    intro v
    exact hDom.2 v (by simpa [S, hFull])
  · have hNonempty : S.Nonempty :=
      ⟨r, hDom.1⟩
    rcases
        exists_adj_mem_not_mem_of_nonempty_ne_univ
          (T := T) S hNonempty hFull with
      ⟨a, b, ha, hb, hadj⟩
    let s := auxSource C ambientRoot hScores b
    have hsNotR : s ∉ R := by
      intro hsR
      apply hb
      change b ∈ auxSourceCarrier C ambientRoot hScores R
      rw [mem_auxSourceCarrier]
      simpa [s] using hsR
    have hbFiber :
        b ∈ auxSourceFiber C ambientRoot hScores s := by
      simp [s]
    have hFiberNonempty :
        (auxSourceFiber C ambientRoot hScores s).Nonempty :=
      ⟨b, hbFiber⟩
    have hFiberConn :
        TreePathConnected (T := T)
          (auxSourceFiber C ambientRoot hScores s) :=
      auxSourceFiber_treePathConnected C ambientRoot hScores s
    have hFiberDom :
        HeightDominated (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          (auxSourceFiber C ambientRoot hScores s) s :=
      auxSourceFiber_heightDominated_of_nonempty
        C ambientRoot hScores s hFiberNonempty
    have hDisj :
        Disjoint S (auxSourceFiber C ambientRoot hScores s) := by
      simpa [S] using
        auxSourceCarrier_disjoint_fiber_of_not_mem
          C ambientRoot hScores R hsNotR
    have hMergedConn :
        TreePathConnected (T := T)
          (S ∪ auxSourceFiber C ambientRoot hScores s) :=
      treePathConnected_union_of_adj
        hConn hFiberConn ha hbFiber hadj
    rcases
        exists_heightDominatingRoot_union_of_adj
          (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          hConn hFiberConn hDisj ha hbFiber hadj hDom hFiberDom with
      ⟨t, hMergedDom⟩
    have hCarrierInsert :
        auxSourceCarrier C ambientRoot hScores (insert s R) =
          S ∪ auxSourceFiber C ambientRoot hScores s := by
      simpa [S] using
        auxSourceCarrier_insert C ambientRoot hScores R s
    have hConn' :
        TreePathConnected (T := T)
          (auxSourceCarrier C ambientRoot hScores (insert s R)) := by
      rw [hCarrierInsert]
      exact hMergedConn
    have hDom' :
        HeightDominated (T := T)
          (fun v => auxHeight C ambientRoot hScores v)
          (auxSourceCarrier C ambientRoot hScores (insert s R)) t := by
      rw [hCarrierInsert]
      exact hMergedDom
    exact
      exists_global_heightDominatingRoot_from_sourceCarrier
        C ambientRoot hScores (insert s R) t hConn' hDom'
termination_by ((Finset.univ : Finset V) \ R).card
decreasing_by
  have hsDiff : s ∈ ((Finset.univ : Finset V) \ R) := by
    simp [hsNotR]
  rw [Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem hsDiff

/-- The canonical source partition therefore consolidates to one ambient root
whose distance profile dominates every auxiliary height. -/
theorem exists_root_auxHeight_le_dist
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    ∃ r : V, ∀ v : V,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v := by
  let r₀ := auxSource C ambientRoot hScores ambientRoot
  let R₀ : Finset V := {r₀}
  have hFiberNonempty :
      (auxSourceFiber C ambientRoot hScores r₀).Nonempty := by
    refine ⟨ambientRoot, ?_⟩
    simp [r₀]
  have hCarrier :
      auxSourceCarrier C ambientRoot hScores R₀ =
        auxSourceFiber C ambientRoot hScores r₀ := by
    simpa [R₀] using
      auxSourceCarrier_singleton C ambientRoot hScores r₀
  have hConn :
      TreePathConnected (T := T)
        (auxSourceCarrier C ambientRoot hScores R₀) := by
    rw [hCarrier]
    exact auxSourceFiber_treePathConnected C ambientRoot hScores r₀
  have hDom :
      HeightDominated (T := T)
        (fun v => auxHeight C ambientRoot hScores v)
        (auxSourceCarrier C ambientRoot hScores R₀) r₀ := by
    rw [hCarrier]
    exact
      auxSourceFiber_heightDominated_of_nonempty
        C ambientRoot hScores r₀ hFiberNonempty
  exact
    exists_global_heightDominatingRoot_from_sourceCarrier
      C ambientRoot hScores R₀ r₀ hConn hDom

/-- Across an edge joining two distinct source fibres, tree distance splits
exactly at that boundary edge. -/
theorem dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b x y : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hx : x ∈ auxSourceFiber C ambientRoot hScores r)
    (hy : y ∈ auxSourceFiber C ambientRoot hScores s) :
    T.graph.dist x y =
      T.graph.dist x a + 1 + T.graph.dist b y := by
  rcases
      exists_path_within_auxSourceFiber
        C ambientRoot hScores r x a hx ha with
    ⟨px, hpxPath, hpxFiber⟩
  rcases
      exists_path_within_auxSourceFiber
        C ambientRoot hScores s b y hb hy with
    ⟨py, hpyPath, hpyFiber⟩
  have hFibDisj :=
    auxSourceFiber_disjoint_of_ne
      C ambientRoot hScores hrs
  have hbNotPx : b ∉ px.support := by
    intro hbpx
    have hbR := hpxFiber b hbpx
    exact (Finset.disjoint_left.mp hFibDisj) hbR hb
  let q : T.graph.Walk x b := px.concat hadj
  have hqPath : q.IsPath := by
    exact hpxPath.concat hbNotPx hadj
  have hbNotPyTail : b ∉ py.support.tail := by
    have hNodup := hpyPath.support_nodup
    rw [← py.cons_tail_support, List.nodup_cons] at hNodup
    exact hNodup.1
  have hDisjoint : q.support.Disjoint py.support.tail := by
    rw [List.disjoint_left]
    intro z hzq hzpyTail
    have hzpy : z ∈ py.support :=
      List.mem_of_mem_tail hzpyTail
    have hzS := hpyFiber z hzpy
    have hzq' :
        z ∈ px.support ∨ z = b := by
      simpa [q] using hzq
    rcases hzq' with hzpx | rfl
    · have hzR := hpxFiber z hzpx
      exact (Finset.disjoint_left.mp hFibDisj) hzR hzS
    · exact hbNotPyTail hzpyTail
  have hpPath : (q.append py).IsPath := by
    rw [SimpleGraph.Walk.isPath_def,
      SimpleGraph.Walk.support_append, List.nodup_append']
    exact
      ⟨hqPath.support_nodup, hpyPath.support_nodup.tail, hDisjoint⟩
  have hpxDist :=
    tree_path_length_eq_dist (T := T) px hpxPath
  have hpyDist :=
    tree_path_length_eq_dist (T := T) py hpyPath
  have hpDist :=
    tree_path_length_eq_dist (T := T) (q.append py) hpPath
  calc
    T.graph.dist x y = (q.append py).length := hpDist.symm
    _ = px.length + 1 + py.length := by
      simp [q]
    _ = T.graph.dist x a + 1 + T.graph.dist b y := by
      rw [hpxDist, hpyDist]

/-- The index of every nonempty source fibre belongs to that fibre. -/
theorem source_mem_auxSourceFiber_of_nonempty
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r : V}
    (hNonempty : (auxSourceFiber C ambientRoot hScores r).Nonempty) :
    r ∈ auxSourceFiber C ambientRoot hScores r := by
  have hZero :=
    (auxSourceFiber_nonempty_iff C ambientRoot hScores r).1 hNonempty
  rw [mem_auxSourceFiber]
  exact auxSource_eq_self_of_height_zero
    C ambientRoot hScores r hZero

/-- If the depth of the first source to its boundary endpoint plus the crossing
edge dominates the depth of the second source to its endpoint, then the first
source is at least as far from every vertex in the second fibre as the second
source is. -/
theorem sourceFiber_dist_le_of_boundary_depth
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b v : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores s) :
    T.graph.dist s v ≤ T.graph.dist r v := by
  have hr :
      r ∈ auxSourceFiber C ambientRoot hScores r :=
    source_mem_auxSourceFiber_of_nonempty
      C ambientRoot hScores ⟨a, ha⟩
  have hCross :=
    dist_eq_dist_add_one_add_dist_of_adj_sourceFibers
      C ambientRoot hScores hrs ha hb hadj hr hv
  have hTri :
      T.graph.dist s v ≤
        T.graph.dist s b + T.graph.dist b v :=
    T.isTree.connected.dist_triangle
  rw [hCross]
  omega

/-- On a source fibre, the auxiliary weight is exactly the power of two of
ambient-tree distance from that fibre's height-zero source. -/
theorem auxWeight_eq_two_pow_dist_of_mem_sourceFiber
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r v : V)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores r) :
    auxWeight C ambientRoot hScores v =
      2 ^ T.graph.dist r v := by
  have hsrc : auxSource C ambientRoot hScores v = r := by
    simpa using hv
  rw [auxWeight, auxHeight_eq_dist_auxSource, hsrc]

/-- Under the same boundary-depth comparison, the first source's rooted
power-of-two weight pointwise dominates the auxiliary weight throughout the
second fibre. -/
theorem auxWeight_le_two_pow_dist_of_boundary_depth
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r s a b v : V}
    (hrs : r ≠ s)
    (ha : a ∈ auxSourceFiber C ambientRoot hScores r)
    (hb : b ∈ auxSourceFiber C ambientRoot hScores s)
    (hadj : T.graph.Adj a b)
    (hDepth :
      T.graph.dist s b ≤ T.graph.dist r a + 1)
    (hv : v ∈ auxSourceFiber C ambientRoot hScores s) :
    auxWeight C ambientRoot hScores v ≤
      2 ^ T.graph.dist r v := by
  rw [auxWeight_eq_two_pow_dist_of_mem_sourceFiber
    C ambientRoot hScores s v hv]
  exact Nat.pow_le_pow_right Nat.zero_lt_two
    (sourceFiber_dist_le_of_boundary_depth
      C ambientRoot hScores hrs ha hb hadj hDepth hv)

end OrientedBranch

end TreeStack

/- Source module: TreeStack.UpperBound.lean -/
namespace TreeStack

open scoped BigOperators Classical

namespace OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- A pointwise domination of auxiliary height by distance from one root gives
the corresponding powers-of-two domination in the integer weights. -/
theorem auxWeightInt_le_two_pow_dist
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r v : V)
    (hHeight :
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxWeightInt C ambientRoot hScores v ≤
      ((2 ^ T.graph.dist r v : ℕ) : ℤ) := by
  change
    (auxWeight C ambientRoot hScores v : ℤ) ≤
      ((2 ^ T.graph.dist r v : ℕ) : ℤ)
  exact_mod_cast
    Nat.pow_le_pow_right Nat.zero_lt_two hHeight

/-- Once one root dominates all auxiliary heights, the weighted internal
degree potential is bounded by the rooted internal estimator potential. -/
theorem auxInternalDegreePotential_le_rootedInternalPotential
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (r : V)
    (hHeight : ∀ v,
      auxHeight C ambientRoot hScores v ≤ T.graph.dist r v) :
    auxInternalDegreePotential C ambientRoot hScores ≤
      (rootedInternalPotential T r : ℤ) := by
  unfold auxInternalDegreePotential rootedInternalPotential
  calc
    (∑ v ∈ ambientInternalVertices (T := T),
        (T.graph.degree v : ℤ) *
          auxWeightInt C ambientRoot hScores v) ≤
      ∑ v ∈ ambientInternalVertices (T := T),
        (T.graph.degree v : ℤ) *
          ((2 ^ T.graph.dist r v : ℕ) : ℤ) := by
      exact Finset.sum_le_sum fun v _ => by
        exact mul_le_mul_of_nonneg_left
          (auxWeightInt_le_two_pow_dist
            C ambientRoot hScores r v (hHeight v))
          (by positivity)
    _ = (∑ v ∈ ambientInternalVertices (T := T),
          T.graph.degree v * 2 ^ T.graph.dist r v : ℕ) := by
      norm_cast

/-- Consolidation turns the compact auxiliary potential into one rooted
Csernák--Soukup estimator, with the leading one removed. -/
theorem exists_root_auxCompactPotential_le_rootEstimate_sub_one
    [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    ∃ r : V,
      auxCompactPotential C ambientRoot hScores ≤
        (rootEstimate T r : ℤ) - 1 := by
  rcases
      exists_root_auxHeight_le_dist C ambientRoot hScores with
    ⟨r, hHeight⟩
  refine ⟨r, ?_⟩
  have hInternal :=
    auxInternalDegreePotential_le_rootedInternalPotential
      C ambientRoot hScores r hHeight
  rw [rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
    T r]
  unfold auxCompactPotential
  push_cast
  linarith

end OrientedBranch

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- A positive-mass configuration has an occupied vertex. -/
theorem exists_pos_of_mass_pos
    (C : Configuration V) (hMass : 0 < mass C) :
    ∃ v : V, 0 < C v := by
  by_contra hNone
  push Not at hNone
  have hZero : ∀ v : V, C v = 0 := by
    intro v
    have hv := hNone v
    omega
  have hm : mass C = 0 := by
    simp [mass, hZero]
  omega

/-- The arbitrary-defect upper bound in additive form.  If every rooted score
is nonpositive, then the configuration has at most `estim T - 1` pebbles. -/
theorem mass_add_one_le_estim_of_all_scores_nonpos
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C + 1 ≤ estim T := by
  by_cases hMassZero : mass C = 0
  · rw [hMassZero]
    have hEstim := card_add_one_le_estim T
    omega
  · have hMassPos : 0 < mass C :=
      Nat.pos_of_ne_zero hMassZero
    rcases exists_pos_of_mass_pos C hMassPos with
      ⟨ambientRoot, hRootPos⟩
    have hMassCompact :=
      OrientedBranch.mass_le_auxCompactPotential
        C ambientRoot hRootPos hScores
    rcases
        OrientedBranch.exists_root_auxCompactPotential_le_rootEstimate_sub_one
          C ambientRoot hScores with
      ⟨r, hCompactRoot⟩
    have hRootEstim := rootEstimate_le_estim T r
    have hRootEstimInt :
        (rootEstimate T r : ℤ) ≤ (estim T : ℤ) := by
      exact_mod_cast hRootEstim
    have hMassEstimInt :
        (mass C : ℤ) + 1 ≤ (estim T : ℤ) := by
      linarith
    exact_mod_cast hMassEstimInt

/-- Natural-subtraction form of the arbitrary-defect estimator bound. -/
theorem mass_le_estim_sub_one_of_all_scores_nonpos
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0) :
    mass C ≤ estim T - 1 := by
  have h :=
    mass_add_one_le_estim_of_all_scores_nonpos T C hScores
  omega

/-- Every globally non-stackable configuration lies below the estimator
threshold. -/
theorem nonstackable_mass_le_estim_sub_one
    [Nontrivial V]
    (T : FiniteTree V) (C : Configuration V)
    (hNot : ¬ Stackable T.graph C) :
    mass C ≤ estim T - 1 := by
  exact
    mass_le_estim_sub_one_of_all_scores_nonpos T C
      ((not_stackable_iff_all_scores_nonpos T C).1 hNot)

/-- Every configuration of exactly the estimator size is stackable. -/
theorem universalStackable_estim
    [Nontrivial V]
    (T : FiniteTree V) :
    UniversalStackable T.graph (estim T) := by
  intro C hMass
  by_contra hNot
  have hUpper :=
    nonstackable_mass_le_estim_sub_one T C hNot
  rw [hMass] at hUpper
  have hEstimPos := card_add_one_le_estim T
  omega

end TreeStack

/- Source module: TreeStack.Stacking.lean -/
namespace TreeStack

open scoped BigOperators Classical

variable {V : Type*} [Fintype V] {T : FiniteTree V}

/-- The exact-size source predicate whose least witness is the stacking
number.  The source convention requires the threshold itself to be at least
two. -/
def StackingCandidate (T : FiniteTree V) (t : ℕ) : Prop :=
  2 ≤ t ∧ UniversalStackable T.graph t

/-- The Csernák--Soukup stacking number: the least exact size at least two
for which every configuration is stackable. -/
noncomputable def stack (T : FiniteTree V) : ℕ :=
  sInf {t : ℕ | StackingCandidate T t}

/-- Exact-size universality propagates to every larger exact size on a
nontrivial connected finite graph. -/
theorem universal_stackable_mono
    [Nontrivial V]
    (T : FiniteTree V) {s t : ℕ}
    (hU : UniversalStackable T.graph s)
    (hs : 2 ≤ s) (hst : s ≤ t) :
    UniversalStackable T.graph t := by
  induction t, hst using Nat.le_induction with
  | base =>
      exact hU
  | succ t hst ih =>
      exact
        universal_stackable_succ
          T.isTree.connected ih (by omega)

/-- On every nontrivial finite tree the estimator itself is an admissible
stacking candidate. -/
theorem estim_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (estim T) := by
  constructor
  · have hcard : 1 < Fintype.card V :=
      Fintype.one_lt_card
    have hEstim := card_add_one_le_estim T
    omega
  · exact universalStackable_estim T

/-- The exact-size candidate set is nonempty for every nontrivial finite
tree. -/
theorem stackingCandidate_nonempty
    [Nontrivial V] (T : FiniteTree V) :
    Set.Nonempty {t : ℕ | StackingCandidate T t} :=
  ⟨estim T, estim_stackingCandidate T⟩

/-- The defined stacking number is itself an exact-size stacking candidate. -/
theorem stack_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) :
    StackingCandidate T (stack T) := by
  unfold stack
  exact Nat.sInf_mem (stackingCandidate_nonempty T)

/-- Minimality of the exact-size stacking number. -/
theorem stack_le_of_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    stack T ≤ t := by
  unfold stack
  exact Nat.sInf_le ht

/-- Every admissible exact stacking threshold is at least the estimator.
Otherwise exact-size upward closure would make the estimator-minus-one
obstruction stackable. -/
theorem estim_le_of_stackingCandidate
    [Nontrivial V] (T : FiniteTree V) {t : ℕ}
    (ht : StackingCandidate T t) :
    estim T ≤ t := by
  rcases ht with ⟨htTwo, hU⟩
  by_contra hNot
  have htLt : t < estim T := Nat.lt_of_not_ge hNot
  have htLe : t ≤ estim T - 1 := by omega
  have hUObs :
      UniversalStackable T.graph (estim T - 1) :=
    universal_stackable_mono T hU htTwo htLe
  rcases exists_nonstackable_mass_estim_sub_one T with
    ⟨C, hMass, hNotStackable⟩
  exact hNotStackable (hUObs C hMass)

/-- Exact Csernák--Soukup stacking equality for every nontrivial finite
tree. -/
theorem stack_eq_estim
    [Nontrivial V] (T : FiniteTree V) :
    stack T = estim T := by
  apply Nat.le_antisymm
  · exact stack_le_of_stackingCandidate T (estim_stackingCandidate T)
  · exact estim_le_of_stackingCandidate T (stack_stackingCandidate T)

/-- Headline form with the source's explicit nontriviality hypothesis.  The
one-vertex tree is intentionally excluded because the source stacking number
uses thresholds at least two while the displayed estimator is one there. -/
theorem stack_eq_estim_of_two_le_card
    (T : FiniteTree V)
    (hcard : 2 ≤ Fintype.card V) :
    stack T = estim T := by
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact stack_eq_estim T

end TreeStack

/-!
The tree stacking conjecture is due to Tamás Csernák and Lajos Soukup
(arXiv:2610.09650, Conjecture 5.6). The nontrivial-tree proof is adapted
from James Fairfax-Ball's TreeStack formalization of his result
"The stacking number of a tree" (https://arxiv.org/html/2609.31811v2).
Credit for the registered formulation's proof: @grp06.
-/

section

open OMA.S_arxiv_2610_09650
open scoped BigOperators Classical

private theorem treeStack_stackable_iff {V : Type} (G : SimpleGraph V) (c : V → ℕ) :
    TreeStack.Stackable G c ↔ Stackable G c := by
  constructor
  · rintro ⟨r, d, hreach, hstack⟩
    exact ⟨d, hreach, r, hstack⟩
  · rintro ⟨d, hreach, r, hstack⟩
    exact ⟨r, d, hreach, hstack⟩

private theorem treeStack_stack_eq {V : Type} [Fintype V] (T : TreeStack.FiniteTree V) :
    TreeStack.stack T = stack T.graph := by
  unfold TreeStack.stack stack
  apply congrArg (sInf : Set ℕ → ℕ)
  ext t
  change (2 ≤ t ∧ ∀ c : V → ℕ, TreeStack.mass c = t → TreeStack.Stackable T.graph c) ↔
    (2 ≤ t ∧ ∀ c : V → ℕ, size c = t → Stackable T.graph c)
  constructor
  · rintro ⟨ht, hc⟩
    exact ⟨ht, fun c hm => (treeStack_stackable_iff T.graph c).mp (hc c hm)⟩
  · rintro ⟨ht, hc⟩
    exact ⟨ht, fun c hm => (treeStack_stackable_iff T.graph c).mpr (hc c hm)⟩

private theorem treeStack_estim_eq {V : Type} [Fintype V] (T : TreeStack.FiniteTree V) :
    TreeStack.estim T = 1 + Finset.univ.sup (fun r => rho T.graph r + leafCount T.graph r) := by
  let f : V → ℕ := fun r => rho T.graph r + leafCount T.graph r
  have hroot (r : V) : TreeStack.rootEstimate T r = 1 + f r := by
    change (1 + rho T.graph r) + leafCount T.graph r = _
    exact Nat.add_assoc _ _ _
  change Finset.univ.sup (TreeStack.rootEstimate T) = 1 + Finset.univ.sup f
  have huniv : (Finset.univ : Finset V).Nonempty :=
    ⟨T.isTree.connected.nonempty.some, Finset.mem_univ _⟩
  apply le_antisymm
  · apply Finset.sup_le
    intro r hr
    rw [hroot]
    exact Nat.add_le_add_left (Finset.le_sup (f := f) hr) 1
  · obtain ⟨r, hr, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ huniv f
    rw [hmax, ← hroot]
    exact Finset.le_sup hr

private theorem stack_estim_subsingleton {V : Type} [Fintype V] [Subsingleton V]
    (G : SimpleGraph V) (hG : G.IsTree) : stack G = estim G := by
  obtain ⟨r⟩ := hG.connected.nonempty
  have huniv : (Finset.univ : Finset V) = {r} := by
    ext v
    simp [Subsingleton.elim v r]
  have hstack : stack G = 2 := by
    unfold stack
    have htwo : (2 : ℕ) ∈ {t : ℕ | 2 ≤ t ∧ ∀ c : V → ℕ, size c = t → Stackable G c} := by
      refine ⟨le_rfl, ?_⟩
      intro c hmass
      have hc : c r = 2 := by simpa [size, huniv] using hmass
      have hpos : 0 < c r := by omega
      exact ⟨c, Relation.ReflTransGen.refl, r, hpos,
        fun v hv => (hv (Subsingleton.elim v r)).elim⟩
    refine le_antisymm (Nat.sInf_le htwo) ?_
    have hmin := Nat.sInf_mem (Set.nonempty_of_mem htwo)
    exact hmin.1
  have hdegree (v : V) : G.degree v = 0 :=
    SimpleGraph.degree_eq_zero_of_subsingleton v
  rw [hstack]
  simp [estim, rho, leafCount, hdegree, huniv]

theorem OMA.solution : type_of% @OMA.S_arxiv_2610_09650.main := by
  intro V _ G hG
  by_cases hcard : 2 ≤ Fintype.card V
  · let T : TreeStack.FiniteTree V := ⟨G, hG⟩
    letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have htwo : 2 ≤ TreeStack.estim T := (TreeStack.estim_stackingCandidate T).1
    change stack T.graph = estim T.graph
    rw [← treeStack_stack_eq T, TreeStack.stack_eq_estim_of_two_le_card T hcard]
    unfold estim
    rw [← treeStack_estim_eq T, max_eq_right htwo]
  · letI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact stack_estim_subsingleton G hG

end
