import OMAReductions.R_wp_bipartite_graph_R1


/-
Adapted from the uniform-word certificate of Matthew J. Colbrook and Catherine
Drysdale, Crown graphs maximise the representation number of bipartite graphs,
at miinadietrich/crown_graphs_maximise revision
f7496aebabdac7ec8c64ce8f0e14072e8038bd5a, Apache License 2.0.
This adaptation selects the graph and word transport lemmas, scopes the finite
checks to each theorem, and relates the resulting words to the registered H1.
Crown graph representation bounds
Copyright 2026 Matthew J. Colbrook and Catherine Drysdale.

The certificate replay helpers in lean/generated/CertificateReplay.lean,
CertificateReplaySix.lean, CertificateReplayDirectKernel.lean and
CertificateOriginalCache.lean adapt Mathlib/Tactic/Sat/FromLRAT.lean
by Mario Carneiro, distributed under the Apache License, Version 2.0.

The proof development uses Lean, its standard library, mathlib and the
dependencies identified in lean/lake-manifest.json. These dependencies retain
their respective copyright notices and licences. External checking tools
and their licences are listed in tools/pins.json and docs/dependencies.md.

The paired word construction follows the construction of Mozhui and Krishna,
as developed in the accompanying paper by Colbrook and Drysdale. Mathematical
sources and the formal theorem map are listed in docs/mathematics.md.

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
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

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

/- Source module Crown.Definitions -/
namespace Crown


def restrictPair {V : Type*} [DecidableEq V] (w : List V) (a b : V) : List V :=
  w.filter fun x => x = a ∨ x = b


def Alternates {V : Type*} [DecidableEq V] (w : List V) (a b : V) : Prop :=
  (restrictPair w a b).IsChain (· ≠ ·)


def Uniform {V : Type*} [DecidableEq V] (k : ℕ) (w : List V) : Prop :=
  ∀ v, w.count v = k


def Represents {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (w : List V) : Prop :=
  0 < k ∧ Uniform k w ∧ ∀ a b, a ≠ b → (G.Adj a b ↔ Alternates w a b)


def KRepresentable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ w, Represents G k w


end Crown

/- Source module Crown.Words -/
namespace Crown
variable {V : Type*} [DecidableEq V]

theorem restrictPair_map {W : Type*} [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (w : List V) (a b : V) :
    restrictPair (w.map f) (f a) (f b) = (restrictPair w a b).map f := by
  unfold restrictPair
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases hx : x = a ∨ x = b <;> simp [hf.eq_iff, hx] <;>
      simpa only [Bool.decide_or] using ih

theorem alternates_map {W : Type*} [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (w : List V) (a b : V) :
    Alternates (w.map f) (f a) (f b) ↔ Alternates w a b := by
  simp only [Alternates, restrictPair_map f hf, List.isChain_map, hf.ne_iff]


theorem represents_equiv {W : Type*} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b)
    {k : ℕ} {w : List V} (h : Represents G k w) :
    Represents H k (w.map e) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    simpa only [List.count_map_of_injective w e e.injective] using h.2.1 u
  · intro a b hab
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [he, alternates_map e e.injective]
    exact h.2.2 a b (fun hh => hab (congrArg e hh))



def restrictVertices (p : V → Prop) [DecidablePred p] (w : List V) : List {v // p v} :=
  w.filterMap fun v => if h : p v then some ⟨v, h⟩ else none

omit [DecidableEq V] in
theorem map_restrictVertices (p : V → Prop) [DecidablePred p] (w : List V) :
    (restrictVertices p w).map Subtype.val = w.filter (fun v => decide (p v)) := by
  unfold restrictVertices
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases hx : p x <;> simpa [hx] using ih

theorem restrictPair_filter (p : V → Prop) [DecidablePred p]
    (w : List V) (a b : V) (ha : p a) (hb : p b) :
    restrictPair (w.filter fun v => decide (p v)) a b = restrictPair w a b := by
  unfold restrictPair
  rw [List.filter_filter]
  congr 1
  funext x
  by_cases hx : x = a ∨ x = b
  · have hp : p x := hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
    simp [hx, hp]
  · simp [hx]

theorem alternates_restrictVertices (p : V → Prop) [DecidablePred p]
    (w : List V) (a b : {v // p v}) :
    Alternates (restrictVertices p w) a b ↔ Alternates w a.val b.val := by
  rw [← alternates_map Subtype.val Subtype.val_injective, map_restrictVertices]
  simp only [Alternates, restrictPair_filter p w a.val b.val a.property b.property]

theorem count_restrictVertices (p : V → Prop) [DecidablePred p]
    (w : List V) (a : {v // p v}) : (restrictVertices p w).count a = w.count a.val := by
  rw [← List.count_map_of_injective (restrictVertices p w) Subtype.val
    Subtype.val_injective, map_restrictVertices]
  exact List.count_filter (by simp [a.property])


theorem represents_induce {G : SimpleGraph V} {k : ℕ} {w : List V}
    (h : Represents G k w) (p : V → Prop) [DecidablePred p] :
    Represents (G.induce {v | p v}) k (restrictVertices p w) := by
  refine ⟨h.1, fun a => ?_, fun a b hab => ?_⟩
  · have ha := (count_restrictVertices p w a).trans (h.2.1 a.val)
    have hcount : @List.count _ instBEqOfDecidableEq a (restrictVertices p w) =
        @List.count _ Subtype.instBEq a (restrictVertices p w) := by
      apply List.countP_congr
      intro x _
      simp only [beq_iff_eq]
    exact hcount.trans ha
  · rw [alternates_restrictVertices]
    exact h.2.2 a.val b.val (fun he => hab (Subtype.ext he))

theorem kRepresentable_induce {G : SimpleGraph V} {k : ℕ}
    (h : KRepresentable G k) (p : V → Prop) [DecidablePred p] :
    KRepresentable (G.induce {v | p v}) k := by
  obtain ⟨w, hw⟩ := h
  exact ⟨restrictVertices p w, represents_induce hw p⟩



theorem kRepresentable_of_inducedEmbedding {W : Type*} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (he : ∀ a b, G.Adj a b ↔ H.Adj (f a) (f b)) {k : ℕ}
    (h : KRepresentable H k) : KRepresentable G k := by
  classical
  obtain ⟨w, hw⟩ := kRepresentable_induce h (fun v => v ∈ Set.range f)
  let e : V ≃ Set.range f := Equiv.ofInjective f f.injective
  refine ⟨w.map e.symm, represents_equiv e.symm ?_ hw⟩
  intro a b
  have ha : f (e.symm a) = a.val := congrArg Subtype.val (e.apply_symm_apply a)
  have hb : f (e.symm b) = b.val := congrArg Subtype.val (e.apply_symm_apply b)
  simpa only [SimpleGraph.induce_adj, ha, hb] using he (e.symm a) (e.symm b)



end Crown

/- Source module Crown.SmallBipartiteData -/
namespace Crown.SmallBipartite

def words0 : Array (List (Fin 6)) := #[
  [0, 1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0]
]

def words1 : Array (List (Fin 6)) := #[
  [0, 1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0],
  [2, 3, 4, 5, 0, 1, 0, 1, 5, 4, 3, 2],
  [1, 3, 4, 5, 0, 2, 0, 2, 5, 4, 3, 1],
  [3, 4, 5, 0, 1, 2, 0, 2, 1, 5, 4, 3],
  [1, 2, 4, 5, 0, 3, 0, 3, 5, 4, 2, 1],
  [2, 4, 5, 0, 1, 3, 0, 3, 1, 5, 4, 2],
  [1, 4, 5, 0, 2, 3, 0, 3, 2, 5, 4, 1],
  [4, 5, 0, 1, 2, 3, 0, 3, 2, 1, 5, 4],
  [1, 2, 3, 5, 0, 4, 0, 4, 5, 3, 2, 1],
  [2, 3, 5, 0, 1, 4, 0, 4, 1, 5, 3, 2],
  [1, 3, 5, 0, 2, 4, 0, 4, 2, 5, 3, 1],
  [3, 5, 0, 1, 2, 4, 0, 4, 2, 1, 5, 3],
  [1, 2, 5, 0, 3, 4, 0, 4, 3, 5, 2, 1],
  [2, 5, 0, 1, 3, 4, 0, 4, 3, 1, 5, 2],
  [1, 5, 0, 2, 3, 4, 0, 4, 3, 2, 5, 1],
  [5, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 5],
  [1, 2, 3, 4, 0, 5, 0, 5, 4, 3, 2, 1],
  [2, 3, 4, 0, 1, 5, 0, 5, 1, 4, 3, 2],
  [1, 3, 4, 0, 2, 5, 0, 5, 2, 4, 3, 1],
  [3, 4, 0, 1, 2, 5, 0, 5, 2, 1, 4, 3],
  [1, 2, 4, 0, 3, 5, 0, 5, 3, 4, 2, 1],
  [2, 4, 0, 1, 3, 5, 0, 5, 3, 1, 4, 2],
  [1, 4, 0, 2, 3, 5, 0, 5, 3, 2, 4, 1],
  [4, 0, 1, 2, 3, 5, 0, 5, 3, 2, 1, 4],
  [1, 2, 3, 0, 4, 5, 0, 5, 4, 3, 2, 1],
  [2, 3, 0, 1, 4, 5, 0, 5, 4, 1, 3, 2],
  [1, 3, 0, 2, 4, 5, 0, 5, 4, 2, 3, 1],
  [3, 0, 1, 2, 4, 5, 0, 5, 4, 2, 1, 3],
  [1, 2, 0, 3, 4, 5, 0, 5, 4, 3, 2, 1],
  [2, 0, 1, 3, 4, 5, 0, 5, 4, 3, 1, 2],
  [1, 0, 2, 3, 4, 5, 0, 5, 4, 3, 2, 1],
  [0, 1, 2, 3, 4, 5, 0, 5, 4, 3, 2, 1]
]

def words2 : Array (List (Fin 6)) := #[
  [0, 1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0],
  [1, 3, 4, 5, 0, 2, 0, 2, 5, 4, 3, 1],
  [1, 2, 4, 5, 0, 3, 0, 3, 5, 4, 2, 1],
  [1, 4, 5, 0, 2, 3, 0, 3, 2, 5, 4, 1],
  [1, 2, 3, 5, 0, 4, 0, 4, 5, 3, 2, 1],
  [1, 3, 5, 0, 2, 4, 0, 4, 2, 5, 3, 1],
  [1, 2, 5, 0, 3, 4, 0, 4, 3, 5, 2, 1],
  [1, 5, 0, 2, 3, 4, 0, 4, 3, 2, 5, 1],
  [1, 2, 3, 4, 0, 5, 0, 5, 4, 3, 2, 1],
  [1, 3, 4, 0, 2, 5, 0, 5, 2, 4, 3, 1],
  [1, 2, 4, 0, 3, 5, 0, 5, 3, 4, 2, 1],
  [1, 4, 0, 2, 3, 5, 0, 5, 3, 2, 4, 1],
  [1, 2, 3, 0, 4, 5, 0, 5, 4, 3, 2, 1],
  [1, 3, 0, 2, 4, 5, 0, 5, 4, 2, 3, 1],
  [1, 2, 0, 3, 4, 5, 0, 5, 4, 3, 2, 1],
  [1, 0, 2, 3, 4, 5, 0, 5, 4, 3, 2, 1],
  [0, 3, 4, 5, 1, 2, 1, 2, 5, 4, 3, 0],
  [3, 4, 5, 2, 0, 1, 2, 1, 0, 5, 4, 3],
  [4, 5, 0, 3, 1, 2, 1, 2, 0, 3, 5, 4],
  [4, 5, 1, 0, 2, 3, 0, 3, 1, 2, 5, 4],
  [3, 5, 0, 4, 1, 2, 1, 2, 0, 4, 5, 3],
  [3, 5, 1, 0, 2, 4, 0, 4, 1, 2, 5, 3],
  [5, 1, 2, 0, 3, 4, 0, 4, 3, 1, 2, 5],
  [5, 1, 0, 2, 3, 4, 0, 4, 3, 1, 2, 5],
  [3, 4, 0, 5, 1, 2, 1, 2, 0, 5, 4, 3],
  [3, 4, 1, 0, 2, 5, 0, 5, 1, 2, 4, 3],
  [4, 1, 2, 0, 3, 5, 0, 5, 3, 1, 2, 4],
  [4, 1, 0, 2, 3, 5, 0, 5, 3, 1, 2, 4],
  [3, 1, 2, 0, 4, 5, 0, 5, 4, 1, 2, 3],
  [3, 1, 0, 2, 4, 5, 0, 5, 4, 1, 2, 3],
  [1, 2, 0, 3, 4, 5, 0, 5, 4, 3, 1, 2],
  [1, 0, 2, 3, 4, 5, 0, 5, 4, 3, 1, 2],
  [0, 2, 4, 5, 1, 3, 1, 3, 5, 4, 2, 0],
  [4, 5, 0, 2, 1, 3, 1, 3, 0, 2, 5, 4],
  [2, 4, 5, 3, 0, 1, 3, 1, 0, 5, 4, 2],
  [4, 5, 1, 0, 3, 2, 0, 2, 1, 3, 5, 4],
  [2, 5, 0, 4, 1, 3, 1, 3, 0, 4, 5, 2],
  [5, 1, 3, 0, 2, 4, 0, 4, 2, 1, 3, 5],
  [2, 5, 1, 0, 3, 4, 0, 4, 1, 3, 5, 2],
  [5, 1, 0, 3, 2, 4, 0, 4, 2, 1, 3, 5],
  [2, 4, 0, 5, 1, 3, 1, 3, 0, 5, 4, 2],
  [4, 1, 3, 0, 2, 5, 0, 5, 2, 1, 3, 4],
  [2, 4, 1, 0, 3, 5, 0, 5, 1, 3, 4, 2],
  [4, 1, 0, 3, 2, 5, 0, 5, 2, 1, 3, 4],
  [2, 1, 3, 0, 4, 5, 0, 5, 4, 1, 3, 2],
  [1, 3, 0, 2, 4, 5, 0, 5, 4, 2, 1, 3],
  [2, 1, 0, 3, 4, 5, 0, 5, 4, 1, 3, 2],
  [1, 0, 3, 2, 4, 5, 0, 5, 4, 2, 1, 3],
  [0, 4, 5, 1, 2, 3, 1, 3, 2, 5, 4, 0],
  [4, 5, 0, 1, 2, 3, 1, 3, 0, 2, 5, 4],
  [4, 5, 0, 1, 3, 2, 1, 2, 0, 3, 5, 4],
  [4, 5, 0, 1, 2, 3, 1, 0, 3, 2, 5, 4],
  [5, 0, 4, 1, 2, 3, 1, 3, 2, 0, 4, 5],
  [5, 0, 4, 1, 2, 3, 1, 3, 0, 2, 4, 5],
  [5, 0, 4, 1, 3, 2, 1, 2, 0, 3, 4, 5],
  [5, 1, 0, 2, 3, 4, 0, 4, 1, 3, 2, 5],
  [4, 0, 5, 1, 2, 3, 1, 3, 2, 0, 5, 4],
  [4, 0, 5, 1, 2, 3, 1, 3, 0, 2, 5, 4],
  [4, 0, 5, 1, 3, 2, 1, 2, 0, 3, 5, 4],
  [4, 1, 0, 2, 3, 5, 0, 5, 1, 3, 2, 4],
  [0, 4, 5, 1, 2, 3, 1, 3, 2, 0, 5, 4],
  [1, 3, 0, 2, 4, 5, 0, 5, 4, 1, 2, 3],
  [1, 2, 0, 3, 4, 5, 0, 5, 4, 1, 3, 2],
  [1, 0, 2, 3, 4, 5, 0, 5, 4, 1, 3, 2],
  [0, 2, 3, 5, 1, 4, 1, 4, 5, 3, 2, 0],
  [3, 5, 0, 2, 1, 4, 1, 4, 0, 2, 5, 3],
  [2, 5, 0, 3, 1, 4, 1, 4, 0, 3, 5, 2],
  [5, 1, 4, 0, 2, 3, 0, 3, 2, 1, 4, 5],
  [2, 3, 5, 4, 0, 1, 4, 1, 0, 5, 3, 2],
  [3, 5, 1, 0, 4, 2, 0, 2, 1, 4, 5, 3],
  [2, 5, 1, 0, 4, 3, 0, 3, 1, 4, 5, 2],
  [5, 1, 0, 4, 2, 3, 0, 3, 2, 1, 4, 5],
  [2, 3, 0, 5, 1, 4, 1, 4, 0, 5, 3, 2],
  [3, 1, 4, 0, 2, 5, 0, 5, 2, 1, 4, 3],
  [2, 1, 4, 0, 3, 5, 0, 5, 3, 1, 4, 2],
  [1, 4, 0, 2, 3, 5, 0, 5, 3, 2, 1, 4],
  [2, 3, 1, 0, 4, 5, 0, 5, 1, 4, 3, 2],
  [3, 1, 0, 4, 2, 5, 0, 5, 2, 1, 4, 3],
  [2, 1, 0, 4, 3, 5, 0, 5, 3, 1, 4, 2],
  [1, 0, 4, 2, 3, 5, 0, 5, 3, 2, 1, 4],
  [0, 3, 5, 1, 2, 4, 1, 4, 2, 5, 3, 0],
  [3, 5, 0, 1, 2, 4, 1, 4, 0, 2, 5, 3],
  [5, 0, 3, 1, 2, 4, 1, 4, 2, 0, 3, 5],
  [5, 0, 3, 1, 2, 4, 1, 4, 0, 2, 3, 5],
  [3, 5, 0, 1, 4, 2, 1, 2, 0, 4, 5, 3],
  [3, 5, 0, 1, 2, 4, 1, 0, 4, 2, 5, 3],
  [5, 0, 3, 1, 4, 2, 1, 2, 0, 4, 3, 5],
  [5, 1, 0, 2, 4, 3, 0, 3, 1, 4, 2, 5],
  [3, 0, 5, 1, 2, 4, 1, 4, 2, 0, 5, 3],
  [3, 0, 5, 1, 2, 4, 1, 4, 0, 2, 5, 3],
  [0, 3, 5, 1, 2, 4, 1, 4, 2, 0, 5, 3],
  [1, 4, 0, 2, 3, 5, 0, 5, 3, 1, 2, 4],
  [3, 0, 5, 1, 4, 2, 1, 2, 0, 4, 5, 3],
  [3, 1, 0, 2, 4, 5, 0, 5, 1, 4, 2, 3],
  [1, 2, 0, 4, 3, 5, 0, 5, 3, 1, 4, 2],
  [1, 0, 2, 4, 3, 5, 0, 5, 3, 1, 4, 2],
  [0, 2, 5, 1, 3, 4, 1, 4, 3, 5, 2, 0],
  [5, 0, 2, 1, 3, 4, 1, 4, 3, 0, 2, 5],
  [2, 5, 0, 1, 3, 4, 1, 4, 0, 3, 5, 2],
  [5, 0, 2, 1, 3, 4, 1, 4, 0, 3, 2, 5],
  [2, 5, 0, 1, 4, 3, 1, 3, 0, 4, 5, 2],
  [5, 0, 2, 1, 4, 3, 1, 3, 0, 4, 2, 5],
  [2, 5, 0, 1, 3, 4, 1, 0, 4, 3, 5, 2],
  [5, 1, 0, 3, 4, 2, 0, 2, 1, 4, 3, 5],
  [2, 0, 5, 1, 3, 4, 1, 4, 3, 0, 5, 2],
  [0, 2, 5, 1, 3, 4, 1, 4, 3, 0, 5, 2],
  [2, 0, 5, 1, 3, 4, 1, 4, 0, 3, 5, 2],
  [1, 4, 0, 3, 2, 5, 0, 5, 2, 1, 3, 4],
  [2, 0, 5, 1, 4, 3, 1, 3, 0, 4, 5, 2],
  [1, 3, 0, 4, 2, 5, 0, 5, 2, 1, 4, 3],
  [2, 1, 0, 3, 4, 5, 0, 5, 1, 4, 3, 2],
  [1, 0, 3, 4, 2, 5, 0, 5, 2, 1, 4, 3],
  [0, 5, 1, 2, 3, 4, 1, 4, 3, 2, 5, 0],
  [5, 0, 1, 2, 3, 4, 1, 4, 3, 0, 2, 5],
  [5, 0, 1, 3, 2, 4, 1, 4, 2, 0, 3, 5],
  [5, 0, 1, 2, 3, 4, 1, 4, 0, 3, 2, 5],
  [5, 0, 1, 4, 2, 3, 1, 3, 2, 0, 4, 5],
  [5, 0, 1, 2, 4, 3, 1, 3, 0, 4, 2, 5],
  [5, 0, 1, 3, 4, 2, 1, 2, 0, 4, 3, 5],
  [5, 0, 1, 2, 3, 4, 1, 0, 4, 3, 2, 5],
  [0, 5, 1, 2, 3, 4, 1, 4, 3, 2, 0, 5],
  [0, 5, 1, 2, 3, 4, 1, 4, 3, 0, 2, 5],
  [0, 5, 1, 3, 2, 4, 1, 4, 2, 0, 3, 5],
  [0, 5, 1, 2, 3, 4, 1, 4, 0, 3, 2, 5],
  [0, 5, 1, 4, 2, 3, 1, 3, 2, 0, 4, 5],
  [0, 5, 1, 2, 4, 3, 1, 3, 0, 4, 2, 5],
  [0, 5, 1, 3, 4, 2, 1, 2, 0, 4, 3, 5],
  [1, 0, 2, 3, 4, 5, 0, 5, 1, 4, 3, 2],
  [0, 2, 3, 4, 1, 5, 1, 5, 4, 3, 2, 0],
  [3, 4, 0, 2, 1, 5, 1, 5, 0, 2, 4, 3],
  [2, 4, 0, 3, 1, 5, 1, 5, 0, 3, 4, 2],
  [4, 1, 5, 0, 2, 3, 0, 3, 2, 1, 5, 4],
  [2, 3, 0, 4, 1, 5, 1, 5, 0, 4, 3, 2],
  [3, 1, 5, 0, 2, 4, 0, 4, 2, 1, 5, 3],
  [2, 1, 5, 0, 3, 4, 0, 4, 3, 1, 5, 2],
  [1, 5, 0, 2, 3, 4, 0, 4, 3, 2, 1, 5],
  [2, 3, 4, 5, 0, 1, 5, 1, 0, 4, 3, 2],
  [3, 4, 1, 0, 5, 2, 0, 2, 1, 5, 4, 3],
  [2, 4, 1, 0, 5, 3, 0, 3, 1, 5, 4, 2],
  [4, 1, 0, 5, 2, 3, 0, 3, 2, 1, 5, 4],
  [2, 3, 1, 0, 5, 4, 0, 4, 1, 5, 3, 2],
  [3, 1, 0, 5, 2, 4, 0, 4, 2, 1, 5, 3],
  [2, 1, 0, 5, 3, 4, 0, 4, 3, 1, 5, 2],
  [1, 0, 5, 2, 3, 4, 0, 4, 3, 2, 1, 5],
  [0, 3, 4, 1, 2, 5, 1, 5, 2, 4, 3, 0],
  [3, 4, 0, 1, 2, 5, 1, 5, 0, 2, 4, 3],
  [4, 0, 3, 1, 2, 5, 1, 5, 2, 0, 3, 4],
  [4, 0, 3, 1, 2, 5, 1, 5, 0, 2, 3, 4],
  [3, 0, 4, 1, 2, 5, 1, 5, 2, 0, 4, 3],
  [3, 0, 4, 1, 2, 5, 1, 5, 0, 2, 4, 3],
  [0, 3, 4, 1, 2, 5, 1, 5, 2, 0, 4, 3],
  [1, 5, 0, 2, 3, 4, 0, 4, 3, 1, 2, 5],
  [3, 4, 0, 1, 5, 2, 1, 2, 0, 5, 4, 3],
  [3, 4, 0, 1, 2, 5, 1, 0, 5, 2, 4, 3],
  [4, 0, 3, 1, 5, 2, 1, 2, 0, 5, 3, 4],
  [4, 1, 0, 2, 5, 3, 0, 3, 1, 5, 2, 4],
  [3, 0, 4, 1, 5, 2, 1, 2, 0, 5, 4, 3],
  [3, 1, 0, 2, 5, 4, 0, 4, 1, 5, 2, 3],
  [1, 2, 0, 5, 3, 4, 0, 4, 3, 1, 5, 2],
  [1, 0, 2, 5, 3, 4, 0, 4, 3, 1, 5, 2],
  [0, 2, 4, 1, 3, 5, 1, 5, 3, 4, 2, 0],
  [4, 0, 2, 1, 3, 5, 1, 5, 3, 0, 2, 4],
  [2, 4, 0, 1, 3, 5, 1, 5, 0, 3, 4, 2],
  [4, 0, 2, 1, 3, 5, 1, 5, 0, 3, 2, 4],
  [2, 0, 4, 1, 3, 5, 1, 5, 3, 0, 4, 2],
  [0, 2, 4, 1, 3, 5, 1, 5, 3, 0, 4, 2],
  [2, 0, 4, 1, 3, 5, 1, 5, 0, 3, 4, 2],
  [1, 5, 0, 3, 2, 4, 0, 4, 2, 1, 3, 5],
  [2, 4, 0, 1, 5, 3, 1, 3, 0, 5, 4, 2],
  [4, 0, 2, 1, 5, 3, 1, 3, 0, 5, 2, 4],
  [2, 4, 0, 1, 3, 5, 1, 0, 5, 3, 4, 2],
  [4, 1, 0, 3, 5, 2, 0, 2, 1, 5, 3, 4],
  [2, 0, 4, 1, 5, 3, 1, 3, 0, 5, 4, 2],
  [1, 3, 0, 5, 2, 4, 0, 4, 2, 1, 5, 3],
  [2, 1, 0, 3, 5, 4, 0, 4, 1, 5, 3, 2],
  [1, 0, 3, 5, 2, 4, 0, 4, 2, 1, 5, 3],
  [0, 4, 1, 2, 3, 5, 1, 5, 3, 2, 4, 0],
  [4, 0, 1, 2, 3, 5, 1, 5, 3, 0, 2, 4],
  [4, 0, 1, 3, 2, 5, 1, 5, 2, 0, 3, 4],
  [4, 0, 1, 2, 3, 5, 1, 5, 0, 3, 2, 4],
  [0, 4, 1, 2, 3, 5, 1, 5, 3, 2, 0, 4],
  [0, 4, 1, 2, 3, 5, 1, 5, 3, 0, 2, 4],
  [0, 4, 1, 3, 2, 5, 1, 5, 2, 0, 3, 4],
  [0, 4, 1, 2, 3, 5, 1, 5, 0, 3, 2, 4],
  [4, 0, 1, 5, 2, 3, 1, 3, 2, 0, 5, 4],
  [4, 0, 1, 2, 5, 3, 1, 3, 0, 5, 2, 4],
  [4, 0, 1, 3, 5, 2, 1, 2, 0, 5, 3, 4],
  [4, 0, 1, 2, 3, 5, 1, 0, 5, 3, 2, 4],
  [0, 4, 1, 5, 2, 3, 1, 3, 2, 0, 5, 4],
  [0, 4, 1, 2, 5, 3, 1, 3, 0, 5, 2, 4],
  [0, 4, 1, 3, 5, 2, 1, 2, 0, 5, 3, 4],
  [1, 0, 2, 3, 5, 4, 0, 4, 1, 5, 3, 2],
  [0, 2, 3, 1, 4, 5, 1, 5, 4, 3, 2, 0],
  [3, 0, 2, 1, 4, 5, 1, 5, 4, 0, 2, 3],
  [2, 0, 3, 1, 4, 5, 1, 5, 4, 0, 3, 2],
  [0, 2, 3, 1, 4, 5, 1, 5, 4, 0, 3, 2],
  [2, 3, 0, 1, 4, 5, 1, 5, 0, 4, 3, 2],
  [3, 0, 2, 1, 4, 5, 1, 5, 0, 4, 2, 3],
  [2, 0, 3, 1, 4, 5, 1, 5, 0, 4, 3, 2],
  [1, 5, 0, 4, 2, 3, 0, 3, 2, 1, 4, 5],
  [2, 3, 0, 1, 5, 4, 1, 4, 0, 5, 3, 2],
  [3, 0, 2, 1, 5, 4, 1, 4, 0, 5, 2, 3],
  [2, 0, 3, 1, 5, 4, 1, 4, 0, 5, 3, 2],
  [1, 4, 0, 5, 2, 3, 0, 3, 2, 1, 5, 4],
  [2, 3, 0, 1, 4, 5, 1, 0, 5, 4, 3, 2],
  [3, 1, 0, 4, 5, 2, 0, 2, 1, 5, 4, 3],
  [2, 1, 0, 4, 5, 3, 0, 3, 1, 5, 4, 2],
  [1, 0, 4, 5, 2, 3, 0, 3, 2, 1, 5, 4],
  [0, 3, 1, 2, 4, 5, 1, 5, 4, 2, 3, 0],
  [3, 0, 1, 2, 4, 5, 1, 5, 4, 0, 2, 3],
  [0, 3, 1, 2, 4, 5, 1, 5, 4, 2, 0, 3],
  [0, 3, 1, 2, 4, 5, 1, 5, 4, 0, 2, 3],
  [3, 0, 1, 4, 2, 5, 1, 5, 2, 0, 4, 3],
  [3, 0, 1, 2, 4, 5, 1, 5, 0, 4, 2, 3],
  [0, 3, 1, 4, 2, 5, 1, 5, 2, 0, 4, 3],
  [0, 3, 1, 2, 4, 5, 1, 5, 0, 4, 2, 3],
  [3, 0, 1, 5, 2, 4, 1, 4, 2, 0, 5, 3],
  [3, 0, 1, 2, 5, 4, 1, 4, 0, 5, 2, 3],
  [0, 3, 1, 5, 2, 4, 1, 4, 2, 0, 5, 3],
  [0, 3, 1, 2, 5, 4, 1, 4, 0, 5, 2, 3],
  [3, 0, 1, 4, 5, 2, 1, 2, 0, 5, 4, 3],
  [3, 0, 1, 2, 4, 5, 1, 0, 5, 4, 2, 3],
  [0, 3, 1, 4, 5, 2, 1, 2, 0, 5, 4, 3],
  [1, 0, 2, 4, 5, 3, 0, 3, 1, 5, 4, 2],
  [0, 2, 1, 3, 4, 5, 1, 5, 4, 3, 2, 0],
  [0, 2, 1, 3, 4, 5, 1, 5, 4, 3, 0, 2],
  [2, 0, 1, 3, 4, 5, 1, 5, 4, 0, 3, 2],
  [0, 2, 1, 3, 4, 5, 1, 5, 4, 0, 3, 2],
  [2, 0, 1, 4, 3, 5, 1, 5, 3, 0, 4, 2],
  [0, 2, 1, 4, 3, 5, 1, 5, 3, 0, 4, 2],
  [2, 0, 1, 3, 4, 5, 1, 5, 0, 4, 3, 2],
  [0, 2, 1, 3, 4, 5, 1, 5, 0, 4, 3, 2],
  [2, 0, 1, 5, 3, 4, 1, 4, 3, 0, 5, 2],
  [0, 2, 1, 5, 3, 4, 1, 4, 3, 0, 5, 2],
  [2, 0, 1, 3, 5, 4, 1, 4, 0, 5, 3, 2],
  [0, 2, 1, 3, 5, 4, 1, 4, 0, 5, 3, 2],
  [2, 0, 1, 4, 5, 3, 1, 3, 0, 5, 4, 2],
  [0, 2, 1, 4, 5, 3, 1, 3, 0, 5, 4, 2],
  [2, 0, 1, 3, 4, 5, 1, 0, 5, 4, 3, 2],
  [1, 0, 3, 4, 5, 2, 0, 2, 1, 5, 4, 3],
  [0, 1, 2, 3, 4, 5, 1, 5, 4, 3, 2, 0],
  [0, 1, 2, 3, 4, 5, 1, 5, 4, 3, 0, 2],
  [0, 1, 3, 2, 4, 5, 1, 5, 4, 2, 0, 3],
  [0, 1, 2, 3, 4, 5, 1, 5, 4, 0, 3, 2],
  [0, 1, 4, 2, 3, 5, 1, 5, 3, 2, 0, 4],
  [0, 1, 2, 4, 3, 5, 1, 5, 3, 0, 4, 2],
  [0, 1, 3, 4, 2, 5, 1, 5, 2, 0, 4, 3],
  [0, 1, 2, 3, 4, 5, 1, 5, 0, 4, 3, 2],
  [0, 1, 5, 2, 3, 4, 1, 4, 3, 2, 0, 5],
  [0, 1, 2, 5, 3, 4, 1, 4, 3, 0, 5, 2],
  [0, 1, 3, 5, 2, 4, 1, 4, 2, 0, 5, 3],
  [0, 1, 2, 3, 5, 4, 1, 4, 0, 5, 3, 2],
  [0, 1, 4, 5, 2, 3, 1, 3, 2, 0, 5, 4],
  [0, 1, 2, 4, 5, 3, 1, 3, 0, 5, 4, 2],
  [0, 1, 3, 4, 5, 2, 1, 2, 0, 5, 4, 3],
  [0, 1, 2, 3, 4, 5, 1, 0, 5, 4, 3, 2]
]

def words3 : Array (List (Fin 6)) := #[
  [0, 1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0],
  [1, 2, 4, 5, 0, 3, 0, 3, 5, 4, 2, 1],
  [1, 2, 3, 5, 0, 4, 0, 4, 5, 3, 2, 1],
  [1, 2, 5, 0, 3, 4, 0, 4, 3, 5, 2, 1],
  [1, 2, 3, 4, 0, 5, 0, 5, 4, 3, 2, 1],
  [1, 2, 4, 0, 3, 5, 0, 5, 3, 4, 2, 1],
  [1, 2, 3, 0, 4, 5, 0, 5, 4, 3, 2, 1],
  [1, 2, 0, 3, 4, 5, 0, 5, 4, 3, 2, 1],
  [0, 2, 4, 5, 1, 3, 1, 3, 5, 4, 2, 0],
  [2, 4, 5, 3, 0, 1, 3, 1, 0, 5, 4, 2],
  [2, 5, 0, 4, 1, 3, 1, 3, 0, 4, 5, 2],
  [2, 5, 1, 0, 3, 4, 0, 4, 1, 3, 5, 2],
  [2, 4, 0, 5, 1, 3, 1, 3, 0, 5, 4, 2],
  [2, 4, 1, 0, 3, 5, 0, 5, 1, 3, 4, 2],
  [2, 1, 3, 0, 4, 5, 0, 5, 4, 1, 3, 2],
  [2, 1, 0, 3, 4, 5, 0, 5, 4, 1, 3, 2],
  [0, 2, 3, 5, 1, 4, 1, 4, 5, 3, 2, 0],
  [2, 5, 0, 3, 1, 4, 1, 4, 0, 3, 5, 2],
  [2, 3, 5, 4, 0, 1, 4, 1, 0, 5, 3, 2],
  [2, 5, 1, 0, 4, 3, 0, 3, 1, 4, 5, 2],
  [2, 3, 0, 5, 1, 4, 1, 4, 0, 5, 3, 2],
  [2, 1, 4, 0, 3, 5, 0, 5, 3, 1, 4, 2],
  [2, 3, 1, 0, 4, 5, 0, 5, 1, 4, 3, 2],
  [2, 1, 0, 4, 3, 5, 0, 5, 3, 1, 4, 2],
  [0, 2, 5, 1, 3, 4, 1, 4, 3, 5, 2, 0],
  [2, 5, 0, 1, 3, 4, 1, 4, 0, 3, 5, 2],
  [2, 5, 0, 1, 4, 3, 1, 3, 0, 4, 5, 2],
  [2, 5, 0, 1, 3, 4, 1, 0, 4, 3, 5, 2],
  [2, 0, 5, 1, 3, 4, 1, 4, 3, 0, 5, 2],
  [2, 0, 5, 1, 3, 4, 1, 4, 0, 3, 5, 2],
  [2, 0, 5, 1, 4, 3, 1, 3, 0, 4, 5, 2],
  [2, 1, 0, 3, 4, 5, 0, 5, 1, 4, 3, 2],
  [0, 2, 3, 4, 1, 5, 1, 5, 4, 3, 2, 0],
  [2, 4, 0, 3, 1, 5, 1, 5, 0, 3, 4, 2],
  [2, 3, 0, 4, 1, 5, 1, 5, 0, 4, 3, 2],
  [2, 1, 5, 0, 3, 4, 0, 4, 3, 1, 5, 2],
  [2, 3, 4, 5, 0, 1, 5, 1, 0, 4, 3, 2],
  [2, 4, 1, 0, 5, 3, 0, 3, 1, 5, 4, 2],
  [2, 3, 1, 0, 5, 4, 0, 4, 1, 5, 3, 2],
  [2, 1, 0, 5, 3, 4, 0, 4, 3, 1, 5, 2],
  [0, 2, 4, 1, 3, 5, 1, 5, 3, 4, 2, 0],
  [2, 4, 0, 1, 3, 5, 1, 5, 0, 3, 4, 2],
  [2, 0, 4, 1, 3, 5, 1, 5, 3, 0, 4, 2],
  [2, 0, 4, 1, 3, 5, 1, 5, 0, 3, 4, 2],
  [2, 4, 0, 1, 5, 3, 1, 3, 0, 5, 4, 2],
  [2, 4, 0, 1, 3, 5, 1, 0, 5, 3, 4, 2],
  [2, 0, 4, 1, 5, 3, 1, 3, 0, 5, 4, 2],
  [2, 1, 0, 3, 5, 4, 0, 4, 1, 5, 3, 2],
  [0, 2, 3, 1, 4, 5, 1, 5, 4, 3, 2, 0],
  [2, 0, 3, 1, 4, 5, 1, 5, 4, 0, 3, 2],
  [2, 3, 0, 1, 4, 5, 1, 5, 0, 4, 3, 2],
  [2, 0, 3, 1, 4, 5, 1, 5, 0, 4, 3, 2],
  [2, 3, 0, 1, 5, 4, 1, 4, 0, 5, 3, 2],
  [2, 0, 3, 1, 5, 4, 1, 4, 0, 5, 3, 2],
  [2, 3, 0, 1, 4, 5, 1, 0, 5, 4, 3, 2],
  [2, 1, 0, 4, 5, 3, 0, 3, 1, 5, 4, 2],
  [0, 2, 1, 3, 4, 5, 1, 5, 4, 3, 2, 0],
  [2, 0, 1, 3, 4, 5, 1, 5, 4, 0, 3, 2],
  [2, 0, 1, 4, 3, 5, 1, 5, 3, 0, 4, 2],
  [2, 0, 1, 3, 4, 5, 1, 5, 0, 4, 3, 2],
  [2, 0, 1, 5, 3, 4, 1, 4, 3, 0, 5, 2],
  [2, 0, 1, 3, 5, 4, 1, 4, 0, 5, 3, 2],
  [2, 0, 1, 4, 5, 3, 1, 3, 0, 5, 4, 2],
  [2, 0, 1, 3, 4, 5, 1, 0, 5, 4, 3, 2],
  [0, 1, 4, 5, 2, 3, 2, 3, 5, 4, 1, 0],
  [1, 4, 5, 3, 0, 2, 3, 2, 0, 5, 4, 1],
  [1, 5, 0, 4, 2, 3, 2, 3, 0, 4, 5, 1],
  [1, 5, 2, 0, 3, 4, 0, 4, 2, 3, 5, 1],
  [1, 4, 0, 5, 2, 3, 2, 3, 0, 5, 4, 1],
  [1, 4, 2, 0, 3, 5, 0, 5, 2, 3, 4, 1],
  [1, 2, 3, 0, 4, 5, 0, 5, 4, 2, 3, 1],
  [1, 2, 0, 3, 4, 5, 0, 5, 4, 2, 3, 1],
  [0, 4, 5, 3, 1, 2, 3, 2, 1, 5, 4, 0],
  [4, 5, 3, 0, 1, 2, 3, 2, 1, 0, 5, 4],
  [5, 0, 4, 3, 1, 2, 3, 2, 1, 0, 4, 5],
  [5, 4, 3, 0, 1, 2, 3, 2, 1, 4, 0, 5],
  [4, 0, 5, 3, 1, 2, 3, 2, 1, 0, 5, 4],
  [4, 5, 3, 0, 1, 2, 3, 2, 1, 5, 0, 4],
  [0, 4, 5, 3, 1, 2, 3, 2, 1, 0, 5, 4],
  [1, 2, 0, 3, 4, 5, 0, 5, 4, 2, 1, 3],
  [0, 5, 1, 4, 2, 3, 2, 3, 1, 4, 5, 0],
  [5, 1, 4, 3, 0, 2, 3, 2, 0, 1, 4, 5],
  [5, 2, 3, 4, 0, 1, 4, 1, 0, 2, 3, 5],
  [5, 4, 1, 3, 0, 2, 3, 2, 4, 0, 1, 5],
  [0, 5, 1, 4, 2, 3, 2, 3, 1, 4, 0, 5],
  [1, 4, 2, 0, 3, 5, 0, 5, 2, 3, 1, 4],
  [2, 3, 1, 0, 4, 5, 0, 5, 1, 4, 2, 3],
  [4, 1, 5, 3, 0, 2, 3, 2, 5, 4, 0, 1],
  [0, 5, 2, 1, 3, 4, 1, 4, 2, 3, 5, 0],
  [5, 4, 3, 1, 0, 2, 3, 2, 0, 4, 1, 5],
  [5, 4, 0, 3, 1, 2, 3, 2, 4, 1, 0, 5],
  [5, 4, 3, 0, 1, 2, 3, 2, 4, 1, 0, 5],
  [0, 5, 2, 1, 3, 4, 1, 4, 2, 3, 0, 5],
  [0, 5, 2, 1, 3, 4, 1, 4, 2, 0, 3, 5],
  [2, 1, 3, 0, 4, 5, 0, 5, 1, 4, 2, 3],
  [2, 1, 0, 3, 4, 5, 0, 5, 1, 4, 2, 3],
  [0, 4, 1, 5, 2, 3, 2, 3, 1, 5, 4, 0],
  [4, 1, 5, 3, 0, 2, 3, 2, 0, 1, 5, 4],
  [0, 4, 1, 5, 2, 3, 2, 3, 1, 5, 0, 4],
  [1, 5, 2, 0, 3, 4, 0, 4, 2, 3, 1, 5],
  [4, 2, 3, 5, 0, 1, 5, 1, 0, 2, 3, 4],
  [4, 5, 1, 3, 0, 2, 3, 2, 5, 0, 1, 4],
  [2, 3, 1, 0, 5, 4, 0, 4, 1, 5, 2, 3],
  [5, 1, 4, 3, 0, 2, 3, 2, 4, 5, 0, 1],
  [0, 4, 2, 1, 3, 5, 1, 5, 2, 3, 4, 0],
  [4, 5, 3, 1, 0, 2, 3, 2, 0, 5, 1, 4],
  [0, 4, 2, 1, 3, 5, 1, 5, 2, 3, 0, 4],
  [0, 4, 2, 1, 3, 5, 1, 5, 2, 0, 3, 4],
  [4, 5, 0, 3, 1, 2, 3, 2, 5, 1, 0, 4],
  [4, 5, 3, 0, 1, 2, 3, 2, 5, 1, 0, 4],
  [2, 1, 3, 0, 5, 4, 0, 4, 1, 5, 2, 3],
  [2, 1, 0, 3, 5, 4, 0, 4, 1, 5, 2, 3],
  [0, 2, 3, 1, 4, 5, 1, 5, 4, 2, 3, 0],
  [1, 4, 5, 3, 0, 2, 3, 2, 0, 1, 5, 4],
  [2, 3, 0, 1, 4, 5, 1, 5, 0, 4, 2, 3],
  [2, 0, 3, 1, 4, 5, 1, 5, 0, 4, 2, 3],
  [2, 3, 0, 1, 5, 4, 1, 4, 0, 5, 2, 3],
  [2, 0, 3, 1, 5, 4, 1, 4, 0, 5, 2, 3],
  [2, 3, 0, 1, 4, 5, 1, 0, 5, 4, 2, 3],
  [2, 0, 3, 1, 4, 5, 1, 0, 5, 4, 2, 3],
  [0, 2, 1, 3, 4, 5, 1, 5, 4, 2, 3, 0],
  [0, 2, 1, 3, 4, 5, 1, 5, 4, 2, 0, 3],
  [4, 0, 5, 3, 1, 2, 3, 2, 5, 4, 1, 0],
  [2, 0, 1, 3, 4, 5, 1, 5, 0, 4, 2, 3],
  [5, 0, 4, 3, 1, 2, 3, 2, 4, 5, 1, 0],
  [2, 0, 1, 3, 5, 4, 1, 4, 0, 5, 2, 3],
  [2, 1, 3, 0, 4, 5, 0, 1, 5, 4, 2, 3],
  [2, 0, 1, 3, 4, 5, 1, 0, 5, 4, 2, 3],
  [0, 1, 3, 5, 2, 4, 2, 4, 5, 3, 1, 0],
  [1, 5, 0, 3, 2, 4, 2, 4, 0, 3, 5, 1],
  [1, 3, 5, 4, 0, 2, 4, 2, 0, 5, 3, 1],
  [1, 5, 2, 0, 4, 3, 0, 3, 2, 4, 5, 1],
  [1, 3, 0, 5, 2, 4, 2, 4, 0, 5, 3, 1],
  [1, 2, 4, 0, 3, 5, 0, 5, 3, 2, 4, 1],
  [1, 3, 2, 0, 4, 5, 0, 5, 2, 4, 3, 1],
  [1, 2, 0, 4, 3, 5, 0, 5, 3, 2, 4, 1],
  [0, 5, 1, 3, 2, 4, 2, 4, 1, 3, 5, 0],
  [5, 2, 4, 3, 0, 1, 3, 1, 0, 2, 4, 5],
  [5, 1, 3, 4, 0, 2, 4, 2, 0, 1, 3, 5],
  [5, 3, 1, 4, 0, 2, 4, 2, 3, 0, 1, 5],
  [0, 5, 1, 3, 2, 4, 2, 4, 1, 3, 0, 5],
  [2, 4, 1, 0, 3, 5, 0, 5, 1, 3, 2, 4],
  [1, 3, 2, 0, 4, 5, 0, 5, 2, 4, 1, 3],
  [3, 1, 5, 4, 0, 2, 4, 2, 5, 3, 0, 1],
  [0, 3, 5, 4, 1, 2, 4, 2, 1, 5, 3, 0],
  [5, 0, 3, 4, 1, 2, 4, 2, 1, 0, 3, 5],
  [3, 5, 4, 0, 1, 2, 4, 2, 1, 0, 5, 3],
  [5, 3, 4, 0, 1, 2, 4, 2, 1, 3, 0, 5],
  [3, 0, 5, 4, 1, 2, 4, 2, 1, 0, 5, 3],
  [0, 3, 5, 4, 1, 2, 4, 2, 1, 0, 5, 3],
  [3, 5, 4, 0, 1, 2, 4, 2, 1, 5, 0, 3],
  [1, 2, 0, 4, 3, 5, 0, 5, 3, 2, 1, 4],
  [0, 5, 2, 1, 4, 3, 1, 3, 2, 4, 5, 0],
  [5, 3, 0, 4, 1, 2, 4, 2, 3, 1, 0, 5],
  [5, 3, 4, 1, 0, 2, 4, 2, 0, 3, 1, 5],
  [5, 3, 4, 0, 1, 2, 4, 2, 3, 1, 0, 5],
  [0, 5, 2, 1, 4, 3, 1, 3, 2, 4, 0, 5],
  [2, 1, 4, 0, 3, 5, 0, 5, 1, 3, 2, 4],
  [0, 5, 2, 1, 4, 3, 1, 3, 2, 0, 4, 5],
  [2, 1, 0, 4, 3, 5, 0, 5, 1, 3, 2, 4],
  [0, 3, 1, 5, 2, 4, 2, 4, 1, 5, 3, 0],
  [0, 3, 1, 5, 2, 4, 2, 4, 1, 5, 0, 3],
  [3, 1, 5, 4, 0, 2, 4, 2, 0, 1, 5, 3],
  [1, 5, 2, 0, 4, 3, 0, 3, 2, 4, 1, 5],
  [3, 2, 4, 5, 0, 1, 5, 1, 0, 2, 4, 3],
  [2, 4, 1, 0, 5, 3, 0, 3, 1, 5, 2, 4],
  [3, 5, 1, 4, 0, 2, 4, 2, 5, 0, 1, 3],
  [5, 1, 3, 4, 0, 2, 4, 2, 3, 5, 0, 1],
  [0, 2, 4, 1, 3, 5, 1, 5, 3, 2, 4, 0],
  [2, 4, 0, 1, 3, 5, 1, 5, 0, 3, 2, 4],
  [1, 3, 5, 4, 0, 2, 4, 2, 0, 1, 5, 3],
  [2, 0, 4, 1, 3, 5, 1, 5, 0, 3, 2, 4],
  [2, 4, 0, 1, 5, 3, 1, 3, 0, 5, 2, 4],
  [2, 4, 0, 1, 3, 5, 1, 0, 5, 3, 2, 4],
  [2, 0, 4, 1, 5, 3, 1, 3, 0, 5, 2, 4],
  [2, 0, 4, 1, 3, 5, 1, 0, 5, 3, 2, 4],
  [0, 3, 2, 1, 4, 5, 1, 5, 2, 4, 3, 0],
  [0, 3, 2, 1, 4, 5, 1, 5, 2, 4, 0, 3],
  [3, 5, 4, 1, 0, 2, 4, 2, 0, 5, 1, 3],
  [0, 3, 2, 1, 4, 5, 1, 5, 2, 0, 4, 3],
  [3, 5, 0, 4, 1, 2, 4, 2, 5, 1, 0, 3],
  [2, 1, 4, 0, 5, 3, 0, 3, 1, 5, 2, 4],
  [3, 5, 4, 0, 1, 2, 4, 2, 5, 1, 0, 3],
  [2, 1, 0, 4, 5, 3, 0, 3, 1, 5, 2, 4],
  [0, 2, 1, 4, 3, 5, 1, 5, 3, 2, 4, 0],
  [3, 0, 5, 4, 1, 2, 4, 2, 5, 3, 1, 0],
  [0, 2, 1, 4, 3, 5, 1, 5, 3, 2, 0, 4],
  [2, 0, 1, 4, 3, 5, 1, 5, 0, 3, 2, 4],
  [5, 0, 3, 4, 1, 2, 4, 2, 3, 5, 1, 0],
  [2, 1, 4, 0, 3, 5, 0, 1, 5, 3, 2, 4],
  [2, 0, 1, 4, 5, 3, 1, 3, 0, 5, 2, 4],
  [2, 0, 1, 4, 3, 5, 1, 0, 5, 3, 2, 4],
  [0, 1, 5, 2, 3, 4, 2, 4, 3, 5, 1, 0],
  [1, 5, 0, 2, 3, 4, 2, 4, 0, 3, 5, 1],
  [1, 5, 0, 2, 4, 3, 2, 3, 0, 4, 5, 1],
  [1, 5, 0, 2, 3, 4, 2, 0, 4, 3, 5, 1],
  [1, 0, 5, 2, 3, 4, 2, 4, 3, 0, 5, 1],
  [1, 0, 5, 2, 3, 4, 2, 4, 0, 3, 5, 1],
  [1, 0, 5, 2, 4, 3, 2, 3, 0, 4, 5, 1],
  [1, 2, 0, 3, 4, 5, 0, 5, 2, 4, 3, 1],
  [0, 5, 1, 2, 3, 4, 2, 4, 1, 3, 5, 0],
  [5, 4, 3, 2, 0, 1, 3, 1, 0, 4, 2, 5],
  [5, 4, 0, 3, 2, 1, 3, 1, 4, 2, 0, 5],
  [5, 4, 3, 0, 2, 1, 3, 1, 4, 2, 0, 5],
  [0, 5, 1, 2, 3, 4, 2, 4, 1, 3, 0, 5],
  [0, 5, 1, 2, 3, 4, 2, 4, 1, 0, 3, 5],
  [1, 2, 3, 0, 4, 5, 0, 5, 2, 4, 1, 3],
  [1, 2, 0, 3, 4, 5, 0, 5, 2, 4, 1, 3],
  [0, 5, 1, 2, 4, 3, 2, 3, 1, 4, 5, 0],
  [5, 3, 0, 4, 2, 1, 4, 1, 3, 2, 0, 5],
  [5, 3, 4, 2, 0, 1, 4, 1, 0, 3, 2, 5],
  [5, 3, 4, 0, 2, 1, 4, 1, 3, 2, 0, 5],
  [0, 5, 1, 2, 4, 3, 2, 3, 1, 4, 0, 5],
  [1, 2, 4, 0, 3, 5, 0, 5, 2, 3, 1, 4],
  [0, 5, 1, 2, 4, 3, 2, 3, 1, 0, 4, 5],
  [1, 2, 0, 4, 3, 5, 0, 5, 2, 3, 1, 4],
  [0, 5, 1, 2, 3, 4, 2, 1, 4, 3, 5, 0],
  [5, 4, 3, 1, 2, 0, 3, 0, 4, 2, 1, 5],
  [5, 3, 4, 1, 2, 0, 4, 0, 3, 2, 1, 5],
  [5, 3, 4, 0, 1, 2, 4, 3, 2, 1, 0, 5],
  [0, 5, 1, 2, 3, 4, 2, 1, 4, 3, 0, 5],
  [5, 3, 0, 4, 1, 2, 4, 3, 2, 1, 5, 0],
  [5, 4, 0, 3, 1, 2, 3, 4, 2, 1, 5, 0],
  [5, 3, 4, 0, 1, 2, 4, 3, 2, 1, 5, 0],
  [0, 1, 5, 2, 3, 4, 2, 4, 3, 1, 5, 0],
  [1, 5, 0, 2, 3, 4, 2, 4, 0, 3, 1, 5],
  [1, 5, 0, 2, 4, 3, 2, 3, 0, 4, 1, 5],
  [1, 5, 0, 2, 3, 4, 2, 0, 4, 3, 1, 5],
  [2, 3, 4, 5, 0, 1, 5, 1, 0, 2, 4, 3],
  [1, 0, 5, 2, 3, 4, 2, 4, 0, 3, 1, 5],
  [1, 0, 5, 2, 4, 3, 2, 3, 0, 4, 1, 5],
  [1, 0, 5, 2, 3, 4, 2, 0, 4, 3, 1, 5],
  [0, 1, 5, 2, 3, 4, 2, 4, 1, 3, 5, 0],
  [1, 5, 0, 2, 3, 4, 2, 4, 0, 1, 3, 5],
  [0, 2, 4, 1, 3, 5, 1, 5, 2, 3, 0, 4],
  [5, 3, 1, 4, 0, 2, 4, 3, 2, 0, 5, 1],
  [0, 1, 5, 2, 3, 4, 2, 4, 1, 3, 0, 5],
  [4, 3, 2, 5, 0, 1, 5, 3, 1, 0, 4, 2],
  [0, 1, 5, 3, 1, 2, 3, 4, 2, 0, 4, 5],
  [1, 0, 5, 2, 3, 4, 2, 0, 4, 1, 3, 5],
  [0, 1, 5, 2, 4, 3, 2, 3, 1, 4, 5, 0],
  [0, 2, 3, 1, 4, 5, 1, 5, 2, 4, 0, 3],
  [1, 5, 0, 2, 4, 3, 2, 3, 0, 1, 4, 5],
  [5, 4, 1, 3, 0, 2, 3, 4, 2, 0, 5, 1],
  [0, 1, 5, 2, 4, 3, 2, 3, 1, 4, 0, 5],
  [0, 1, 5, 4, 1, 2, 4, 3, 2, 0, 3, 5],
  [3, 4, 2, 5, 0, 1, 5, 4, 1, 0, 3, 2],
  [1, 0, 5, 2, 4, 3, 2, 0, 3, 1, 4, 5],
  [0, 2, 1, 3, 4, 5, 1, 5, 2, 4, 3, 0],
  [0, 2, 1, 3, 4, 5, 1, 5, 2, 4, 0, 3],
  [0, 2, 1, 4, 3, 5, 1, 5, 2, 3, 0, 4],
  [5, 3, 4, 1, 0, 2, 4, 3, 2, 0, 5, 1],
  [0, 1, 5, 2, 3, 4, 2, 1, 4, 3, 0, 5],
  [0, 1, 5, 2, 3, 4, 2, 1, 4, 0, 3, 5],
  [0, 1, 5, 2, 4, 3, 2, 1, 3, 0, 4, 5],
  [2, 0, 1, 3, 4, 5, 1, 0, 5, 2, 4, 3],
  [0, 1, 3, 4, 2, 5, 2, 5, 4, 3, 1, 0],
  [1, 4, 0, 3, 2, 5, 2, 5, 0, 3, 4, 1],
  [1, 3, 0, 4, 2, 5, 2, 5, 0, 4, 3, 1],
  [1, 2, 5, 0, 3, 4, 0, 4, 3, 2, 5, 1],
  [1, 3, 4, 5, 0, 2, 5, 2, 0, 4, 3, 1],
  [1, 4, 2, 0, 5, 3, 0, 3, 2, 5, 4, 1],
  [1, 3, 2, 0, 5, 4, 0, 4, 2, 5, 3, 1],
  [1, 2, 0, 5, 3, 4, 0, 4, 3, 2, 5, 1],
  [0, 4, 1, 3, 2, 5, 2, 5, 1, 3, 4, 0],
  [4, 2, 5, 3, 0, 1, 3, 1, 0, 2, 5, 4],
  [0, 4, 1, 3, 2, 5, 2, 5, 1, 3, 0, 4],
  [2, 5, 1, 0, 3, 4, 0, 4, 1, 3, 2, 5],
  [4, 1, 3, 5, 0, 2, 5, 2, 0, 1, 3, 4],
  [4, 3, 1, 5, 0, 2, 5, 2, 3, 0, 1, 4],
  [1, 3, 2, 0, 5, 4, 0, 4, 2, 5, 1, 3],
  [3, 1, 4, 5, 0, 2, 5, 2, 4, 3, 0, 1],
  [0, 3, 1, 4, 2, 5, 2, 5, 1, 4, 3, 0],
  [0, 3, 1, 4, 2, 5, 2, 5, 1, 4, 0, 3],
  [3, 2, 5, 4, 0, 1, 4, 1, 0, 2, 5, 3],
  [2, 5, 1, 0, 4, 3, 0, 3, 1, 4, 2, 5],
  [3, 1, 4, 5, 0, 2, 5, 2, 0, 1, 4, 3],
  [1, 4, 2, 0, 5, 3, 0, 3, 2, 5, 1, 4],
  [3, 4, 1, 5, 0, 2, 5, 2, 4, 0, 1, 3],
  [4, 1, 3, 5, 0, 2, 5, 2, 3, 4, 0, 1],
  [0, 2, 5, 1, 3, 4, 1, 4, 3, 2, 5, 0],
  [2, 5, 0, 1, 3, 4, 1, 4, 0, 3, 2, 5],
  [2, 5, 0, 1, 4, 3, 1, 3, 0, 4, 2, 5],
  [2, 5, 0, 1, 3, 4, 1, 0, 4, 3, 2, 5],
  [1, 3, 4, 5, 0, 2, 5, 2, 0, 1, 4, 3],
  [2, 0, 5, 1, 3, 4, 1, 4, 0, 3, 2, 5],
  [2, 0, 5, 1, 4, 3, 1, 3, 0, 4, 2, 5],
  [2, 0, 5, 1, 3, 4, 1, 0, 4, 3, 2, 5],
  [0, 3, 4, 5, 1, 2, 5, 2, 1, 4, 3, 0],
  [4, 0, 3, 5, 1, 2, 5, 2, 1, 0, 3, 4],
  [3, 0, 4, 5, 1, 2, 5, 2, 1, 0, 4, 3],
  [0, 3, 4, 5, 1, 2, 5, 2, 1, 0, 4, 3],
  [3, 4, 5, 0, 1, 2, 5, 2, 1, 0, 4, 3],
  [4, 3, 5, 0, 1, 2, 5, 2, 1, 3, 0, 4],
  [3, 4, 5, 0, 1, 2, 5, 2, 1, 4, 0, 3],
  [1, 2, 0, 5, 3, 4, 0, 4, 3, 2, 1, 5],
  [0, 4, 2, 1, 5, 3, 1, 3, 2, 5, 4, 0],
  [4, 3, 0, 5, 1, 2, 5, 2, 3, 1, 0, 4],
  [0, 4, 2, 1, 5, 3, 1, 3, 2, 5, 0, 4],
  [2, 1, 5, 0, 3, 4, 0, 4, 1, 3, 2, 5],
  [4, 3, 5, 1, 0, 2, 5, 2, 0, 3, 1, 4],
  [4, 3, 5, 0, 1, 2, 5, 2, 3, 1, 0, 4],
  [0, 4, 2, 1, 5, 3, 1, 3, 2, 0, 5, 4],
  [2, 1, 0, 5, 3, 4, 0, 4, 1, 3, 2, 5],
  [0, 3, 2, 1, 5, 4, 1, 4, 2, 5, 3, 0],
  [0, 3, 2, 1, 5, 4, 1, 4, 2, 5, 0, 3],
  [3, 4, 0, 5, 1, 2, 5, 2, 4, 1, 0, 3],
  [2, 1, 5, 0, 4, 3, 0, 3, 1, 4, 2, 5],
  [3, 4, 5, 1, 0, 2, 5, 2, 0, 4, 1, 3],
  [0, 3, 2, 1, 5, 4, 1, 4, 2, 0, 5, 3],
  [3, 4, 5, 0, 1, 2, 5, 2, 4, 1, 0, 3],
  [2, 1, 0, 5, 4, 3, 0, 3, 1, 4, 2, 5],
  [0, 2, 1, 5, 3, 4, 1, 4, 3, 2, 5, 0],
  [3, 0, 4, 5, 1, 2, 5, 2, 4, 3, 1, 0],
  [4, 0, 3, 5, 1, 2, 5, 2, 3, 4, 1, 0],
  [2, 1, 5, 0, 3, 4, 0, 1, 4, 3, 2, 5],
  [0, 2, 1, 5, 3, 4, 1, 4, 3, 2, 0, 5],
  [2, 0, 1, 5, 3, 4, 1, 4, 0, 3, 2, 5],
  [2, 0, 1, 5, 4, 3, 1, 3, 0, 4, 2, 5],
  [2, 0, 1, 5, 3, 4, 1, 0, 4, 3, 2, 5],
  [0, 1, 4, 2, 3, 5, 2, 5, 3, 4, 1, 0],
  [1, 4, 0, 2, 3, 5, 2, 5, 0, 3, 4, 1],
  [1, 0, 4, 2, 3, 5, 2, 5, 3, 0, 4, 1],
  [1, 0, 4, 2, 3, 5, 2, 5, 0, 3, 4, 1],
  [1, 4, 0, 2, 5, 3, 2, 3, 0, 5, 4, 1],
  [1, 4, 0, 2, 3, 5, 2, 0, 5, 3, 4, 1],
  [1, 0, 4, 2, 5, 3, 2, 3, 0, 5, 4, 1],
  [1, 2, 0, 3, 5, 4, 0, 4, 2, 5, 3, 1],
  [0, 4, 1, 2, 3, 5, 2, 5, 1, 3, 4, 0],
  [4, 5, 3, 2, 0, 1, 3, 1, 0, 5, 2, 4],
  [0, 4, 1, 2, 3, 5, 2, 5, 1, 3, 0, 4],
  [0, 4, 1, 2, 3, 5, 2, 5, 1, 0, 3, 4],
  [4, 5, 0, 3, 2, 1, 3, 1, 5, 2, 0, 4],
  [4, 5, 3, 0, 2, 1, 3, 1, 5, 2, 0, 4],
  [1, 2, 3, 0, 5, 4, 0, 4, 2, 5, 1, 3],
  [1, 2, 0, 3, 5, 4, 0, 4, 2, 5, 1, 3],
  [0, 1, 4, 2, 3, 5, 2, 5, 3, 1, 4, 0],
  [1, 4, 0, 2, 3, 5, 2, 5, 0, 3, 1, 4],
  [2, 3, 5, 4, 0, 1, 4, 1, 0, 2, 5, 3],
  [1, 0, 4, 2, 3, 5, 2, 5, 0, 3, 1, 4],
  [1, 4, 0, 2, 5, 3, 2, 3, 0, 5, 1, 4],
  [1, 4, 0, 2, 3, 5, 2, 0, 5, 3, 1, 4],
  [1, 0, 4, 2, 5, 3, 2, 3, 0, 5, 1, 4],
  [1, 0, 4, 2, 3, 5, 2, 0, 5, 3, 1, 4],
  [0, 1, 4, 2, 3, 5, 2, 5, 1, 3, 4, 0],
  [1, 4, 0, 2, 3, 5, 2, 5, 0, 1, 3, 4],
  [0, 1, 4, 2, 3, 5, 2, 5, 1, 3, 0, 4],
  [5, 3, 2, 4, 0, 1, 4, 3, 1, 0, 5, 2],
  [0, 2, 5, 1, 3, 4, 1, 4, 2, 3, 0, 5],
  [4, 3, 1, 5, 0, 2, 5, 3, 2, 0, 4, 1],
  [0, 1, 4, 3, 1, 2, 3, 5, 2, 0, 5, 4],
  [1, 0, 4, 2, 3, 5, 2, 0, 5, 1, 3, 4],
  [0, 4, 1, 2, 5, 3, 2, 3, 1, 5, 4, 0],
  [4, 3, 0, 5, 2, 1, 5, 1, 3, 2, 0, 4],
  [0, 4, 1, 2, 5, 3, 2, 3, 1, 5, 0, 4],
  [1, 2, 5, 0, 3, 4, 0, 4, 2, 3, 1, 5],
  [4, 3, 5, 2, 0, 1, 5, 1, 0, 3, 2, 4],
  [4, 3, 5, 0, 2, 1, 5, 1, 3, 2, 0, 4],
  [0, 4, 1, 2, 5, 3, 2, 3, 1, 0, 5, 4],
  [1, 2, 0, 5, 3, 4, 0, 4, 2, 3, 1, 5],
  [0, 4, 1, 2, 3, 5, 2, 1, 5, 3, 4, 0],
  [4, 5, 3, 1, 2, 0, 3, 0, 5, 2, 1, 4],
  [0, 4, 1, 2, 3, 5, 2, 1, 5, 3, 0, 4],
  [4, 3, 0, 5, 1, 2, 5, 3, 2, 1, 4, 0],
  [4, 3, 5, 1, 2, 0, 5, 0, 3, 2, 1, 4],
  [4, 3, 5, 0, 1, 2, 5, 3, 2, 1, 0, 4],
  [4, 5, 0, 3, 1, 2, 3, 5, 2, 1, 4, 0],
  [4, 3, 5, 0, 1, 2, 5, 3, 2, 1, 4, 0],
  [0, 1, 4, 2, 5, 3, 2, 3, 1, 5, 4, 0],
  [0, 2, 3, 1, 5, 4, 1, 4, 2, 5, 0, 3],
  [0, 1, 4, 2, 5, 3, 2, 3, 1, 5, 0, 4],
  [0, 1, 4, 5, 1, 2, 5, 3, 2, 0, 3, 4],
  [1, 4, 0, 2, 5, 3, 2, 3, 0, 1, 5, 4],
  [4, 5, 1, 3, 0, 2, 3, 5, 2, 0, 4, 1],
  [3, 5, 2, 4, 0, 1, 4, 5, 1, 0, 3, 2],
  [1, 0, 4, 2, 5, 3, 2, 0, 3, 1, 5, 4],
  [0, 2, 1, 3, 5, 4, 1, 4, 2, 5, 3, 0],
  [0, 2, 1, 3, 5, 4, 1, 4, 2, 5, 0, 3],
  [0, 1, 4, 2, 3, 5, 2, 1, 5, 3, 0, 4],
  [0, 1, 4, 2, 3, 5, 2, 1, 5, 0, 3, 4],
  [0, 2, 1, 5, 3, 4, 1, 4, 2, 3, 0, 5],
  [4, 3, 5, 1, 0, 2, 5, 3, 2, 0, 4, 1],
  [0, 1, 4, 2, 5, 3, 2, 1, 3, 0, 5, 4],
  [2, 0, 1, 3, 5, 4, 1, 0, 4, 2, 5, 3],
  [0, 1, 3, 2, 4, 5, 2, 5, 4, 3, 1, 0],
  [1, 0, 3, 2, 4, 5, 2, 5, 4, 0, 3, 1],
  [1, 3, 0, 2, 4, 5, 2, 5, 0, 4, 3, 1],
  [1, 0, 3, 2, 4, 5, 2, 5, 0, 4, 3, 1],
  [1, 3, 0, 2, 5, 4, 2, 4, 0, 5, 3, 1],
  [1, 0, 3, 2, 5, 4, 2, 4, 0, 5, 3, 1],
  [1, 3, 0, 2, 4, 5, 2, 0, 5, 4, 3, 1],
  [1, 2, 0, 4, 5, 3, 0, 3, 2, 5, 4, 1],
  [0, 1, 3, 2, 4, 5, 2, 5, 4, 1, 3, 0],
  [2, 4, 5, 3, 0, 1, 3, 1, 0, 2, 5, 4],
  [1, 3, 0, 2, 4, 5, 2, 5, 0, 4, 1, 3],
  [1, 0, 3, 2, 4, 5, 2, 5, 0, 4, 1, 3],
  [1, 3, 0, 2, 5, 4, 2, 4, 0, 5, 1, 3],
  [1, 0, 3, 2, 5, 4, 2, 4, 0, 5, 1, 3],
  [1, 3, 0, 2, 4, 5, 2, 0, 5, 4, 1, 3],
  [1, 0, 3, 2, 4, 5, 2, 0, 5, 4, 1, 3],
  [0, 3, 1, 2, 4, 5, 2, 5, 1, 4, 3, 0],
  [0, 3, 1, 2, 4, 5, 2, 5, 1, 4, 0, 3],
  [3, 5, 4, 2, 0, 1, 4, 1, 0, 5, 2, 3],
  [0, 3, 1, 2, 4, 5, 2, 5, 1, 0, 4, 3],
  [3, 5, 0, 4, 2, 1, 4, 1, 5, 2, 0, 3],
  [1, 2, 4, 0, 5, 3, 0, 3, 2, 5, 1, 4],
  [3, 5, 4, 0, 2, 1, 4, 1, 5, 2, 0, 3],
  [1, 2, 0, 4, 5, 3, 0, 3, 2, 5, 1, 4],
  [0, 1, 3, 2, 4, 5, 2, 5, 1, 4, 3, 0],
  [0, 1, 3, 2, 4, 5, 2, 5, 1, 4, 0, 3],
  [1, 3, 0, 2, 4, 5, 2, 5, 0, 1, 4, 3],
  [5, 4, 2, 3, 0, 1, 3, 4, 1, 0, 5, 2],
  [0, 2, 5, 1, 4, 3, 1, 3, 2, 4, 0, 5],
  [0, 1, 3, 4, 1, 2, 4, 5, 2, 0, 5, 3],
  [3, 4, 1, 5, 0, 2, 5, 4, 2, 0, 3, 1],
  [1, 0, 3, 2, 4, 5, 2, 0, 5, 1, 4, 3],
  [0, 3, 1, 2, 5, 4, 2, 4, 1, 5, 3, 0],
  [0, 3, 1, 2, 5, 4, 2, 4, 1, 5, 0, 3],
  [3, 4, 0, 5, 2, 1, 5, 1, 4, 2, 0, 3],
  [1, 2, 5, 0, 4, 3, 0, 3, 2, 4, 1, 5],
  [3, 4, 5, 2, 0, 1, 5, 1, 0, 4, 2, 3],
  [0, 3, 1, 2, 5, 4, 2, 4, 1, 0, 5, 3],
  [3, 4, 5, 0, 2, 1, 5, 1, 4, 2, 0, 3],
  [1, 2, 0, 5, 4, 3, 0, 3, 2, 4, 1, 5],
  [0, 1, 3, 2, 5, 4, 2, 4, 1, 5, 3, 0],
  [0, 1, 3, 2, 5, 4, 2, 4, 1, 5, 0, 3],
  [0, 2, 4, 1, 5, 3, 1, 3, 2, 5, 0, 4],
  [0, 1, 3, 5, 1, 2, 5, 4, 2, 0, 4, 3],
  [1, 3, 0, 2, 5, 4, 2, 4, 0, 1, 5, 3],
  [4, 5, 2, 3, 0, 1, 3, 5, 1, 0, 4, 2],
  [3, 5, 1, 4, 0, 2, 4, 5, 2, 0, 3, 1],
  [1, 0, 3, 2, 5, 4, 2, 0, 4, 1, 5, 3],
  [0, 3, 1, 2, 4, 5, 2, 1, 5, 4, 3, 0],
  [0, 3, 1, 2, 4, 5, 2, 1, 5, 4, 0, 3],
  [3, 5, 4, 1, 2, 0, 4, 0, 5, 2, 1, 3],
  [3, 4, 0, 5, 1, 2, 5, 4, 2, 1, 3, 0],
  [3, 4, 5, 1, 2, 0, 5, 0, 4, 2, 1, 3],
  [3, 5, 0, 4, 1, 2, 4, 5, 2, 1, 3, 0],
  [3, 4, 5, 0, 1, 2, 5, 4, 2, 1, 0, 3],
  [3, 4, 5, 0, 1, 2, 5, 4, 2, 1, 3, 0],
  [0, 2, 1, 4, 5, 3, 1, 3, 2, 5, 4, 0],
  [0, 1, 3, 2, 4, 5, 2, 1, 5, 4, 0, 3],
  [0, 2, 1, 4, 5, 3, 1, 3, 2, 5, 0, 4],
  [0, 1, 3, 2, 4, 5, 2, 1, 5, 0, 4, 3],
  [0, 2, 1, 5, 4, 3, 1, 3, 2, 4, 0, 5],
  [0, 1, 3, 2, 5, 4, 2, 1, 4, 0, 5, 3],
  [3, 4, 5, 1, 0, 2, 5, 4, 2, 0, 3, 1],
  [2, 0, 1, 4, 5, 3, 1, 0, 3, 2, 5, 4],
  [0, 1, 2, 3, 4, 5, 2, 5, 4, 3, 1, 0],
  [1, 0, 2, 3, 4, 5, 2, 5, 4, 0, 3, 1],
  [1, 0, 2, 4, 3, 5, 2, 5, 3, 0, 4, 1],
  [1, 0, 2, 3, 4, 5, 2, 5, 0, 4, 3, 1],
  [1, 0, 2, 5, 3, 4, 2, 4, 3, 0, 5, 1],
  [1, 0, 2, 3, 5, 4, 2, 4, 0, 5, 3, 1],
  [1, 0, 2, 4, 5, 3, 2, 3, 0, 5, 4, 1],
  [1, 0, 2, 3, 4, 5, 2, 0, 5, 4, 3, 1],
  [0, 1, 2, 3, 4, 5, 2, 5, 4, 1, 3, 0],
  [0, 1, 2, 3, 4, 5, 2, 5, 4, 1, 0, 3],
  [4, 0, 5, 3, 2, 1, 3, 1, 5, 4, 2, 0],
  [1, 0, 2, 3, 4, 5, 2, 5, 0, 4, 1, 3],
  [5, 0, 4, 3, 2, 1, 3, 1, 4, 5, 2, 0],
  [1, 0, 2, 3, 5, 4, 2, 4, 0, 5, 1, 3],
  [1, 2, 3, 0, 4, 5, 0, 2, 5, 4, 1, 3],
  [1, 0, 2, 3, 4, 5, 2, 0, 5, 4, 1, 3],
  [0, 1, 2, 4, 3, 5, 2, 5, 3, 1, 4, 0],
  [3, 0, 5, 4, 2, 1, 4, 1, 5, 3, 2, 0],
  [0, 1, 2, 4, 3, 5, 2, 5, 3, 1, 0, 4],
  [1, 0, 2, 4, 3, 5, 2, 5, 0, 3, 1, 4],
  [5, 0, 3, 4, 2, 1, 4, 1, 3, 5, 2, 0],
  [1, 2, 4, 0, 3, 5, 0, 2, 5, 3, 1, 4],
  [1, 0, 2, 4, 5, 3, 2, 3, 0, 5, 1, 4],
  [1, 0, 2, 4, 3, 5, 2, 0, 5, 3, 1, 4],
  [0, 1, 2, 3, 4, 5, 2, 5, 1, 4, 3, 0],
  [0, 1, 2, 3, 4, 5, 2, 5, 1, 4, 0, 3],
  [0, 1, 2, 4, 3, 5, 2, 5, 1, 3, 0, 4],
  [5, 3, 4, 2, 0, 1, 4, 3, 1, 0, 5, 2],
  [0, 2, 5, 1, 3, 4, 1, 2, 4, 3, 0, 5],
  [0, 2, 5, 1, 3, 4, 1, 2, 4, 0, 3, 5],
  [0, 2, 5, 1, 4, 3, 1, 2, 3, 0, 4, 5],
  [1, 0, 2, 3, 4, 5, 2, 0, 5, 1, 4, 3],
  [0, 1, 2, 5, 3, 4, 2, 4, 3, 1, 5, 0],
  [3, 0, 4, 5, 2, 1, 5, 1, 4, 3, 2, 0],
  [4, 0, 3, 5, 2, 1, 5, 1, 3, 4, 2, 0],
  [1, 2, 5, 0, 3, 4, 0, 2, 4, 3, 1, 5],
  [0, 1, 2, 5, 3, 4, 2, 4, 3, 1, 0, 5],
  [1, 0, 2, 5, 3, 4, 2, 4, 0, 3, 1, 5],
  [1, 0, 2, 5, 4, 3, 2, 3, 0, 4, 1, 5],
  [1, 0, 2, 5, 3, 4, 2, 0, 4, 3, 1, 5],
  [0, 1, 2, 3, 5, 4, 2, 4, 1, 5, 3, 0],
  [0, 1, 2, 3, 5, 4, 2, 4, 1, 5, 0, 3],
  [0, 2, 4, 1, 3, 5, 1, 2, 5, 3, 0, 4],
  [0, 2, 4, 1, 3, 5, 1, 2, 5, 0, 3, 4],
  [0, 1, 2, 5, 3, 4, 2, 4, 1, 3, 0, 5],
  [4, 3, 5, 2, 0, 1, 5, 3, 1, 0, 4, 2],
  [0, 2, 4, 1, 5, 3, 1, 2, 3, 0, 5, 4],
  [1, 0, 2, 3, 5, 4, 2, 0, 4, 1, 5, 3],
  [0, 1, 2, 4, 5, 3, 2, 3, 1, 5, 4, 0],
  [0, 2, 3, 1, 4, 5, 1, 2, 5, 4, 0, 3],
  [0, 1, 2, 4, 5, 3, 2, 3, 1, 5, 0, 4],
  [0, 2, 3, 1, 4, 5, 1, 2, 5, 0, 4, 3],
  [0, 1, 2, 5, 4, 3, 2, 3, 1, 4, 0, 5],
  [0, 2, 3, 1, 5, 4, 1, 2, 4, 0, 5, 3],
  [3, 4, 5, 2, 0, 1, 5, 4, 1, 0, 3, 2],
  [1, 0, 2, 4, 5, 3, 2, 0, 3, 1, 5, 4],
  [0, 1, 2, 3, 4, 5, 2, 1, 5, 4, 3, 0],
  [0, 1, 2, 3, 4, 5, 2, 1, 5, 4, 0, 3],
  [0, 1, 2, 4, 3, 5, 2, 1, 5, 3, 0, 4],
  [0, 1, 2, 3, 4, 5, 2, 1, 5, 0, 4, 3],
  [0, 1, 2, 5, 3, 4, 2, 1, 4, 3, 0, 5],
  [0, 1, 2, 3, 5, 4, 2, 1, 4, 0, 5, 3],
  [0, 1, 2, 4, 5, 3, 2, 1, 3, 0, 5, 4],
  [0, 1, 2, 3, 4, 5, 2, 1, 0, 5, 4, 3]
]

end Crown.SmallBipartite

/- Source module Crown.SmallBipartite -/
namespace Crown.SmallBipartite

def crossGraph {A B : Type*} (edge : A → B → Bool) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inr b => edge a b = true
    | .inr b, .inl a => edge a b = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

instance {A B : Type*} (edge : A → B → Bool) : DecidableRel (crossGraph edge).Adj :=
  fun a b => by cases a <;> cases b <;> dsimp [crossGraph] <;> infer_instance

def edgeIndex (m : ℕ) (edge : Fin m → Fin (6-m) → Bool) : ℕ :=
  ∑ a : Fin m, ∑ b : Fin (6-m), if edge a b then 2 ^ (a.val * (6-m) + b.val) else 0

def decodeVertex (m : ℕ) (hm : m ≤ 6) (v : Fin 6) : Fin m ⊕ Fin (6-m) :=
  if h : v.val < m then .inl ⟨v.val, h⟩ else .inr ⟨v.val - m, by omega⟩

def candidate (m : ℕ) (hm : m ≤ 6) (table : Array (List (Fin 6)))
    (edge : Fin m → Fin (6-m) → Bool) : List (Fin m ⊕ Fin (6-m)) :=
  (table.getD (edgeIndex m edge) []).map (decodeVertex m hm)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem all_zero_six : ∀ edge : Fin 0 → Fin 6 → Bool,
    Represents (crossGraph edge) 2 (candidate 0 (by decide) words0 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem all_one_five : ∀ edge : Fin 1 → Fin 5 → Bool,
    Represents (crossGraph edge) 2 (candidate 1 (by decide) words1 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem all_two_four : ∀ edge : Fin 2 → Fin 4 → Bool,
    Represents (crossGraph edge) 2 (candidate 2 (by decide) words2 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem all_three_three : ∀ edge : Fin 3 → Fin 3 → Bool,
    Represents (crossGraph edge) 2 (candidate 3 (by decide) words3 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide


end Crown.SmallBipartite

/- Source module Crown.SmallGraph -/
namespace Crown

open SmallBipartite

theorem six_cross_two_uniform (m : ℕ) (hm : m ≤ 3)
    (edge : Fin m → Fin (6-m) → Bool) : KRepresentable (crossGraph edge) 2 := by
  interval_cases m
  · exact ⟨_, all_zero_six edge⟩
  · exact ⟨_, all_one_five edge⟩
  · exact ⟨_, all_two_four edge⟩
  · exact ⟨_, all_three_three edge⟩

theorem small_cross_ordered {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (edge : A → B → Bool)
    (hA : Fintype.card A ≤ 3) (hN : Fintype.card A + Fintype.card B ≤ 6) :
    KRepresentable (crossGraph edge) 2 := by
  classical
  let m := Fintype.card A
  let n := Fintype.card B
  let eA : A ≃ Fin m := Fintype.equivFin A
  let eB : B ≃ Fin n := Fintype.equivFin B
  have hn : n ≤ 6-m := by dsimp [m,n]; omega
  let fB : B ↪ Fin (6-m) :=
    ⟨fun b => ⟨(eB b).val, Nat.lt_of_lt_of_le (eB b).isLt hn⟩,
      fun _ _ h => eB.injective (Fin.ext (congrArg (fun x : Fin (6-m) => x.val) h))⟩
  let f : A ⊕ B ↪ Fin m ⊕ Fin (6-m) := eA.toEmbedding.sumMap fB
  let expanded : Fin m → Fin (6-m) → Bool := fun a b =>
    if h : b.val < n then edge (eA.symm a) (eB.symm ⟨b.val,h⟩) else false
  have hexp (a : A) (b : B) : expanded (eA a) (fB b) = edge a b := by
    change (if h : (eB b).val < n then
      edge (eA.symm (eA a)) (eB.symm ⟨(eB b).val,h⟩) else false) = edge a b
    rw [dif_pos (eB b).isLt]
    simp
  apply kRepresentable_of_inducedEmbedding f ?_ (six_cross_two_uniform m hA expanded)
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change edge a b = true ↔ expanded (eA a) (fB b) = true
      rw [hexp]
  | inr a =>
    cases b with
    | inl b =>
      change edge b a = true ↔ expanded (eA b) (fB a) = true
      rw [hexp]
    | inr b => rfl

theorem small_cross_two_uniform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (edge : A → B → Bool)
    (hN : Fintype.card A + Fintype.card B ≤ 6) :
    KRepresentable (crossGraph edge) 2 := by
  by_cases hA : Fintype.card A ≤ 3
  · exact small_cross_ordered edge hA hN
  · have hB : Fintype.card B ≤ 3 := by omega
    obtain ⟨w, hw⟩ := small_cross_ordered (fun b a => edge a b) hB (by omega)
    refine ⟨w.map (Equiv.sumComm B A), represents_equiv (Equiv.sumComm B A) ?_ hw⟩
    intro a b
    cases a <;> cases b <;> rfl

theorem small_bipartite_two_uniform_proof {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : Fintype.card V ≤ 6) :
    KRepresentable G 2 := by
  classical
  obtain ⟨c, hc⟩ := hb
  let p : V → Prop := fun v => c v = 0
  let A := {v // p v}
  let B := {v // ¬p v}
  let e : A ⊕ B ≃ V := Equiv.sumCompl p
  let edge : A → B → Bool := fun a b => decide (G.Adj a.val b.val)
  have hcard : Fintype.card A + Fintype.card B ≤ 6 := by
    have he := Fintype.card_congr e
    simpa using he.le.trans hN
  obtain ⟨w, hw⟩ := small_cross_two_uniform edge hcard
  refine ⟨w.map e, represents_equiv e ?_ hw⟩
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change G.Adj a.val b.val ↔ False
      refine ⟨fun h => ?_, False.elim⟩
      have hne := hc h
      have ha := a.property
      have hb := b.property
      change c a.val = 0 at ha
      change c b.val = 0 at hb
      exact hne (ha.trans hb.symm)
    | inr b =>
      change G.Adj a.val b.val ↔ decide (G.Adj a.val b.val) = true
      simp
  | inr a =>
    cases b with
    | inl b =>
      change G.Adj a.val b.val ↔ decide (G.Adj b.val a.val) = true
      simpa using G.adj_comm a.val b.val
    | inr b =>
      change G.Adj a.val b.val ↔ False
      refine ⟨fun h => ?_, False.elim⟩
      have hne := hc h
      have ha := a.property
      have hb := b.property
      change c a.val ≠ 0 at ha
      change c b.val ≠ 0 at hb
      change c a.val ≠ c b.val at hne
      omega


end Crown

theorem OMA.solution : OMA.R_wp_bipartite_graph_R1.H1 := by
  intro V instV instD G hcard hb
  obtain ⟨w, hw⟩ := Crown.small_bipartite_two_uniform_proof G hb hcard
  exact ⟨w, hw.2⟩
