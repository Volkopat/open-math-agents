import OMAReductions.R_wp_bipartite_graph_R1

/-
Adapted from Matthew J. Colbrook and Catherine Drysdale,
Crown graphs maximise the representation number of bipartite graphs,
https://github.com/miinadietrich/crown_graphs_maximise at
f7496aebabdac7ec8c64ce8f0e14072e8038bd5a (Apache-2.0).
The paired-word construction follows Mozhui and Krishna. This file selects
the constructive three-uniform case, keeps its induced-subgraph and relabelling
proofs, and supplies the interface to the eight-vertex target.
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

private theorem crownChainSegment {V : Type*} {r : V → V → Prop} {u w : List V}
    (h : w.IsChain r) (hs : u <:+: w) : u.IsChain r := by
  obtain ⟨a,b,rfl⟩ := hs
  exact h.left_of_append.right_of_append

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

theorem restrictPair_comm (w : List V) (a b : V) :
    restrictPair w a b = restrictPair w b a := by
  simp [restrictPair, or_comm]

theorem alternates_comm (w : List V) (a b : V) :
    Alternates w a b ↔ Alternates w b a := by
  rw [Alternates, Alternates, restrictPair_comm]

theorem restrictPair_append (u w : List V) (a b : V) :
    restrictPair (u ++ w) a b = restrictPair u a b ++ restrictPair w a b := by
  simp [restrictPair]

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


theorem not_alternates_of_repeat {w : List V} {a b x : V}
    (h : [x, x] <:+: restrictPair w a b) : ¬Alternates w a b := by
  intro hc
  have hx := crownChainSegment hc h
  simp at hx


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

/- Source module Crown.Ranks -/
namespace Crown.Ranks

universe u v w
variable {I : Type u} {V : Type v} {X : Type w}

abbrev InitialRow (I : Type u) := I → Option (Fin 3)
abbrev CompletedRow (I : Type u) := I → Fin 5

variable {ρ σ : InitialRow I} {r : CompletedRow I}

def prescribed (u : Fin 3) : Fin 5 := ⟨u.val + 1, by omega⟩

def completeEntry (a : Option (Fin 3)) (t : Bool) : Fin 5 :=
  match a with
  | none => if t then 4 else 0
  | some u => prescribed u

def complete (ρ : InitialRow I) (t : Bool) : CompletedRow I :=
  fun i => completeEntry (ρ i) t

def StrictBelow (r s : CompletedRow I) : Prop := ∀ i, r i < s i

end Crown.Ranks

/- Source module Crown.Orders -/
namespace Crown.Orders

open scoped BigOperators

variable {V : Type*} [Fintype V]

noncomputable def enumeration : List V := (Finset.univ : Finset V).toList

theorem mem_enumeration (b : V) : b ∈ enumeration (V := V) := by
  simp [enumeration]

theorem enumeration_nodup : (enumeration (V := V)).Nodup := Finset.nodup_toList _

noncomputable def sortByKey {K : Type*} [LinearOrder K] (key : V → K) : List V :=
  (enumeration (V := V)).mergeSort (fun b c => key b ≤ key c)

theorem sortByKey_perm {K : Type*} [LinearOrder K] (key : V → K) :
    (sortByKey key).Perm enumeration := List.mergeSort_perm _ _

theorem sortByKey_nodup {K : Type*} [LinearOrder K] (key : V → K) :
    (sortByKey key).Nodup := (sortByKey_perm key).nodup_iff.mpr enumeration_nodup

theorem mem_sortByKey {K : Type*} [LinearOrder K] (key : V → K) (b : V) :
    b ∈ sortByKey key := (sortByKey_perm key).mem_iff.mpr (mem_enumeration b)

theorem sortByKey_pairwise {K : Type*} [LinearOrder K] (key : V → K) :
    (sortByKey key).Pairwise (fun b c => key b ≤ key c) := by
  let rel : V → V → Prop := fun b c => key b ≤ key c
  let : IsTrans V rel := ⟨fun _ _ _ => le_trans⟩
  let : Std.Total rel := ⟨fun _ _ => le_total _ _⟩
  exact List.pairwise_mergeSort' rel enumeration

variable [DecidableEq V]

def Before (l : List V) (b c : V) : Prop := l.idxOf b < l.idxOf c

theorem key_le_of_before {K : Type*} [LinearOrder K] (key : V → K)
    (h : Before (sortByKey key) b c) : key b ≤ key c := by
  have hb := List.idxOf_lt_length_iff.mpr (mem_sortByKey key b)
  have hc := List.idxOf_lt_length_iff.mpr (mem_sortByKey key c)
  have hs := List.pairwise_iff_getElem.mp (sortByKey_pairwise key)
    _ _ hb hc h
  simpa using hs

omit [Fintype V] in
theorem before_or_before (l : List V) (hb : b ∈ l) (_hc : c ∈ l) (hbc : b ≠ c) :
    Before l b c ∨ Before l c b := by
  have hn : l.idxOf b ≠ l.idxOf c := fun h => hbc ((List.idxOf_inj hb).mp h)
  exact lt_or_gt_of_ne hn

variable {k : ℕ}

def rankSum (r : V → Ranks.CompletedRow (Fin k)) (b : V) : ℕ :=
  ∑ i, (r b i).val

noncomputable def firstKey (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k) (b : V) :
    ℕ ×ₗ (ℕᵒᵈ ×ₗ ℕ) :=
  toLex ((r b z).val, toLex (OrderDual.toDual (rankSum r b), enumeration.idxOf b))

noncomputable def firstOrder (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k) : List V :=
  sortByKey (firstKey r z)

noncomputable def laterKey (r : V → Ranks.CompletedRow (Fin k))
    (z i : Fin k) (b : V) : ℕ ×ₗ ℕᵒᵈ :=
  toLex ((r b i).val, OrderDual.toDual ((firstOrder r z).idxOf b))

noncomputable def orders (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) : List V :=
  if i = z then firstOrder r z else sortByKey (laterKey r z i)

theorem orders_nodup (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) :
    (orders r z i).Nodup := by
  unfold orders firstOrder
  split <;> apply sortByKey_nodup

theorem mem_orders (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) (b : V) :
    b ∈ orders r z i := by
  unfold orders firstOrder
  split <;> apply mem_sortByKey

theorem first_key_consequences (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k)
    (h : Before (firstOrder r z) b c) :
    (r b z).val ≤ (r c z).val ∧
      ((r b z).val = (r c z).val → rankSum r c ≤ rankSum r b) := by
  have hh := key_le_of_before (firstKey r z) h
  have hh' := Prod.Lex.toLex_le_toLex'.mp hh
  refine ⟨hh'.1, ?_⟩
  intro he
  have hh'' := Prod.Lex.toLex_le_toLex'.mp (hh'.2 he)
  exact hh''.1

theorem later_key_consequences (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k)
    (h : Before (sortByKey (laterKey r z i)) b c) :
    (r b i).val ≤ (r c i).val ∧
      ((r b i).val = (r c i).val →
        (firstOrder r z).idxOf c ≤ (firstOrder r z).idxOf b) := by
  exact Prod.Lex.toLex_le_toLex'.mp (key_le_of_before (laterKey r z i) h)

theorem coordinate_mono (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k)
    (h : Before (orders r z i) b c) : r b i ≤ r c i := by
  by_cases hi : i = z
  · subst i
    have h' : Before (firstOrder r z) b c := by simpa [orders] using h
    exact (first_key_consequences r z h').1
  · have h' : Before (sortByKey (laterKey r z i)) b c := by
      simpa [orders, hi] using h
    exact (later_key_consequences r z i h').1


theorem all_before_strict (hk : 2 ≤ k) (r : V → Ranks.CompletedRow (Fin k))
    (z : Fin k) (h : ∀ i, Before (orders r z i) b c) : Ranks.StrictBelow (r b) (r c) := by
  have hz : Before (firstOrder r z) b c := by simpa [orders] using h z
  have hle : ∀ i, (r b i).val ≤ (r c i).val := fun i => coordinate_mono r z i (h i)
  have hstrict : ∀ i, i ≠ z → (r b i).val < (r c i).val := by
    intro i hi
    have h' : Before (sortByKey (laterKey r z i)) b c := by
      simpa [orders, hi] using h i
    have he := (later_key_consequences r z i h').2
    change (firstOrder r z).idxOf b < (firstOrder r z).idxOf c at hz
    have hneq : (r b i).val ≠ (r c i).val := fun hh => (not_le_of_gt hz) (he hh)
    exact lt_of_le_of_ne (hle i) hneq
  have hzlt : (r b z).val < (r c z).val := by
    have hneq : (r b z).val ≠ (r c z).val := by
      intro he
      have hsumle := (first_key_consequences r z hz).2 he
      have hother : ∃ i : Fin k, i ≠ z := by
        by_cases hz0 : z = ⟨0, by omega⟩
        · exact ⟨⟨1, by omega⟩, by rw [hz0]; simp [Fin.ext_iff]⟩
        · exact ⟨⟨0, by omega⟩, Ne.symm hz0⟩
      obtain ⟨i, hi⟩ := hother
      have hsumlt : rankSum r b < rankSum r c :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hstrict i hi⟩
      exact (not_le_of_gt hsumlt) hsumle
    exact lt_of_le_of_ne (hle z) hneq
  intro i
  by_cases hi : i = z
  · simpa [hi] using hzlt
  · exact hstrict i hi


theorem coordinate_orders (hk : 2 ≤ k) (r : V → Ranks.CompletedRow (Fin k))
    (hn : ∀ b c, b ≠ c → ¬ Ranks.StrictBelow (r b) (r c)) :
    ∃ π : Fin k → List V,
      (∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) ∧
      (∀ i b c, Before (π i) b c → r b i ≤ r c i) ∧
      ∀ b c, b ≠ c → (∃ i, Before (π i) b c) ∧ (∃ i, Before (π i) c b) := by
  classical
  let z : Fin k := ⟨0, by omega⟩
  refine ⟨orders r z, fun i => ⟨orders_nodup r z i, mem_orders r z i⟩,
    fun i b c h => coordinate_mono r z i h, ?_⟩
  have hex : ∀ b c, b ≠ c → ∃ i, Before (orders r z i) b c := by
    intro b c hbc
    by_contra! hnone
    have hall : ∀ i, Before (orders r z i) c b := by
      intro i
      exact (before_or_before _ (mem_orders r z i b) (mem_orders r z i c) hbc).resolve_left
        (hnone i)
    exact hn c b (Ne.symm hbc) (all_before_strict hk r z hall)
  intro b c hbc
  exact ⟨hex b c hbc, hex c b (Ne.symm hbc)⟩


end Crown.Orders

/- Source module Crown.Blocks -/
namespace Crown.Blocks

open scoped BigOperators

variable {k : ℕ} {B : Type*} [DecidableEq B]

abbrev Alphabet (k : ℕ) (B : Type*) := Sum (Fin k × Bool) B

-- Use the equality test chosen by `Crown.Uniform`, including on the sum type.
local instance : BEq (Alphabet k B) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Alphabet k B) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def x (i : Fin k) : Alphabet k B := Sum.inl (i, false)
def y (i : Fin k) : Alphabet k B := Sum.inl (i, true)

def gap (rank : B → Fin 5) (π : List B) (j : Fin 5) : List (Alphabet k B) :=
  (π.filter fun b => rank b = j).map Sum.inr

def block (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) (i : Fin k) :
    List (Alphabet k B) :=
  gap (fun b => r b i) (π i) 0 ++ [x i] ++
  gap (fun b => r b i) (π i) 1 ++ [y i] ++
  gap (fun b => r b i) (π i) 2 ++ [x i] ++
  gap (fun b => r b i) (π i) 3 ++ [y i] ++
  gap (fun b => r b i) (π i) 4

def retained (i : Fin k) : List (Fin k) :=
  (List.finRange k).filter fun j => j ≠ i ∧ j ≠ finRotate k i

def separator (i : Fin k) : List (Alphabet k B) :=
  (retained i).map y ++ (retained i).map x

def word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) :
    List (Alphabet k B) :=
  (List.finRange k).flatMap fun i => block r π i ++ separator i

theorem count_gap_left (rank : B → Fin 5) (π : List B) (j : Fin 5)
    (a : Fin k × Bool) : (gap rank π j).count (Sum.inl a) = 0 := by
  simp [gap, List.count_eq_zero]

theorem count_gap_right (rank : B → Fin 5) (π : List B) (j : Fin 5) (b : B) :
    (gap rank π j : List (Alphabet k B)).count (Sum.inr b) =
      if rank b = j then π.count b else 0 := by
  rw [gap, List.count_map_of_injective _ Sum.inr Sum.inr_injective]
  by_cases h : rank b = j
  · simp [h]
  · simp [h, List.count_eq_zero]

theorem count_block_left (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) :
    (block r π i).count (Sum.inl (j, side)) = if j = i then 2 else 0 := by
  simp only [block, List.count_append, count_gap_left]
  by_cases h : j = i
  · subst j
    cases side <;> simp [x, y]
  · cases side <;> simp [x, y, h, Ne.symm h]

theorem count_block_right (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (b : B) : (block r π i).count (Sum.inr b) = (π i).count b := by
  have hb : r b i = 0 ∨ r b i = 1 ∨ r b i = 2 ∨ r b i = 3 ∨ r b i = 4 := by
    have hv := (r b i).isLt
    simp only [Fin.ext_iff]
    omega
  rcases hb with hb | hb | hb | hb | hb <;>
    simp [block, x, y, count_gap_right, hb]

theorem count_side_list (is : List (Fin k)) (a b : Bool) (j : Fin k) :
    (is.map (fun i => Sum.inl (i, a) : Fin k → Alphabet k B)).count (Sum.inl (j, b)) =
      if a = b then is.count j else 0 := by
  induction is with
  | nil => simp
  | cons i is ih =>
    cases a <;> cases b <;> simp [ih, List.count_cons]

theorem count_retained (i j : Fin k) :
    (retained i).count j = if j ≠ i ∧ j ≠ finRotate k i then 1 else 0 := by
  simp only [retained]
  split_ifs with h
  · rw [List.count_filter (by simpa only [decide_eq_true_eq] using h), List.count_finRange]
  · apply List.count_eq_zero.mpr
    simpa only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using h

theorem count_separator_left (i j : Fin k) (side : Bool) :
    (separator i : List (Alphabet k B)).count (Sum.inl (j, side)) =
      if j ≠ i ∧ j ≠ finRotate k i then 1 else 0 := by
  rw [separator, List.count_append]
  change ((retained i).map (fun j => Sum.inl (j, true) : Fin k → Alphabet k B)).count
      (Sum.inl (j, side)) +
    ((retained i).map (fun j => Sum.inl (j, false) : Fin k → Alphabet k B)).count
      (Sum.inl (j, side)) = _
  rw [count_side_list, count_side_list]
  cases side <;> simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
    zero_add, add_zero, count_retained]

theorem count_separator_right (i : Fin k) (b : B) :
    (separator i : List (Alphabet k B)).count (Sum.inr b) = 0 := by
  simp [separator, x, y, List.count_eq_zero]

theorem rotate_ne (hk : 2 ≤ k) (i : Fin k) : finRotate k i ≠ i := by
  cases k with
  | zero => omega
  | succ n =>
    intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate] at hv
    split_ifs at hv with hi
    · simp [hi] at hv
      omega
    · omega

theorem count_block_separator_balance (hk : 2 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) :
    (block r π i ++ separator i).count (Sum.inl (j, side)) +
      (if j = finRotate k i then 1 else 0) = 1 + (if j = i then 1 else 0) := by
  have hi := rotate_ne hk i
  simp only [List.count_append, count_block_left, count_separator_left]
  by_cases hji : j = i <;> by_cases hjr : j = finRotate k i <;>
    simp_all

theorem count_word_eq_sum (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (a : Alphabet k B) :
    (word r π).count a = ∑ i : Fin k, (block r π i ++ separator i).count a := by
  rw [word, List.count_flatMap, ← List.sum_toFinset _ (List.nodup_finRange k)]
  simp


theorem word_uniform (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) :
    Crown.Uniform k (word r π) := by
  intro a
  rw [count_word_eq_sum]
  cases a with
  | inr b =>
    have hc : ∀ i, (block r π i ++ separator i).count (Sum.inr b) = 1 := by
      intro i
      simp only [List.count_append, count_block_right, count_separator_right, Nat.add_zero]
      exact List.count_eq_one_of_mem (hπ i).1 ((hπ i).2 b)
    simp [hc]
  | inl a =>
    obtain ⟨j, side⟩ := a
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ => count_block_separator_balance hk r π i j side)
    have hr : (∑ i : Fin k, if j = finRotate k i then 1 else 0) = 1 := by
      rw [Equiv.sum_comp (finRotate k) (fun i => if j = i then (1 : ℕ) else 0)]
      simp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hr] at hs
    have hone : (∑ _i : Fin k, (1 : ℕ)) = k := by simp
    have hj : (∑ i : Fin k, if j = i then (1 : ℕ) else 0) = 1 := by simp
    rw [hone, hj] at hs
    omega

theorem restrictPair_cons (d : B) (l : List B) (b c : B) :
    Crown.restrictPair (d :: l) b c =
      if d = b ∨ d = c then d :: Crown.restrictPair l b c else Crown.restrictPair l b c := by
  simp [Crown.restrictPair, List.filter_cons]

theorem restrictPair_of_not_mem_left (l : List B) (b c : B) (hb : b ∉ l) :
    Crown.restrictPair l b c = l.filter (fun x => x = c) := by
  apply List.filter_congr
  intro d hd
  have hdb : d ≠ b := fun he => hb (he ▸ hd)
  simp [hdb]


theorem restrictPair_permutation (l : List B) (hn : l.Nodup) (b c : B)
    (hb : b ∈ l) (hc : c ∈ l) (hbc : b ≠ c) :
    Crown.restrictPair l b c = if l.idxOf b < l.idxOf c then [b, c] else [c, b] := by
  induction l with
  | nil => simp at hb
  | cons d l ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases hdb : d = b
    · subst d
      have hcl : c ∈ l := (List.mem_cons.mp hc).resolve_left (Ne.symm hbc)
      have ht : Crown.restrictPair l b c = [c] := by
        rw [restrictPair_of_not_mem_left l b c hn'.1, List.filter_eq,
          List.count_eq_one_of_mem hn'.2 hcl]
        rfl
      simp [restrictPair_cons, ht, hbc]
    by_cases hdc : d = c
    · subst d
      have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left hbc
      have ht : Crown.restrictPair l b c = [b] := by
        rw [Crown.restrictPair_comm, restrictPair_of_not_mem_left l c b hn'.1,
          List.filter_eq, List.count_eq_one_of_mem hn'.2 hbl]
        rfl
      simp [restrictPair_cons, ht, hbc.symm]
    · have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left (Ne.symm hdb)
      have hcl : c ∈ l := (List.mem_cons.mp hc).resolve_left (Ne.symm hdc)
      have hh := ih hn'.2 hbl hcl
      simpa [restrictPair_cons, Orders.Before, List.idxOf_cons, hdb, hdc,
        Ne.symm hdb, Ne.symm hdc] using hh

def buckets (rank : B → Fin 5) (l : List B) : List B :=
  l.filter (fun b => rank b = 0) ++ l.filter (fun b => rank b = 1) ++
    l.filter (fun b => rank b = 2) ++ l.filter (fun b => rank b = 3) ++
      l.filter (fun b => rank b = 4)

omit [DecidableEq B] in

theorem buckets_eq (rank : B → Fin 5) (l : List B)
    (hs : l.Pairwise (fun b c => rank b ≤ rank c)) : buckets rank l = l := by
  induction l with
  | nil => simp [buckets]
  | cons d l ih =>
    obtain ⟨hd, hl⟩ := List.pairwise_cons.mp hs
    have hz : ∀ j : Fin 5, j < rank d → l.filter (fun b => rank b = j) = [] := by
      intro j hj
      apply List.filter_eq_nil_iff.mpr
      intro b hb he
      have he' : rank b = j := of_decide_eq_true he
      have hh := hd b hb
      rw [he'] at hh
      exact (not_le_of_gt hj) hh
    have hi := ih hl
    have hr : rank d = 0 ∨ rank d = 1 ∨ rank d = 2 ∨ rank d = 3 ∨ rank d = 4 := by
      have hv := (rank d).isLt
      simp only [Fin.ext_iff]
      omega
    conv_rhs => rw [← hi]
    rcases hr with hr | hr | hr | hr | hr <;>
      simp [buckets, hr, hz]

theorem pairwise_of_before (l : List B) (hn : l.Nodup) (rank : B → Fin 5)
    (hm : ∀ b c, Orders.Before l b c → rank b ≤ rank c) :
    l.Pairwise (fun b c => rank b ≤ rank c) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  apply hm
  simpa only [Orders.Before, hn.idxOf_getElem i hi, hn.idxOf_getElem j hj] using hij

def rightProjection (w : List (Alphabet k B)) : List B := w.filterMap Sum.getRight?

omit [DecidableEq B] in
theorem rightProjection_block (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (hs : (π i).Pairwise (fun b c => r b i ≤ r c i)) :
    rightProjection (block r π i) = π i := by
  simpa [rightProjection, block, gap, x, y, List.filterMap_map, List.filterMap_cons,
    Sum.getRight?, Function.comp_def,
    buckets] using buckets_eq (fun b => r b i) (π i) hs

omit [DecidableEq B] in
theorem rightProjection_separator (i : Fin k) :
    rightProjection (separator i : List (Alphabet k B)) = [] := by
  simp [rightProjection, separator, x, y, List.filterMap_map, Function.comp_def]

omit [DecidableEq B] in
theorem rightProjection_word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hs : ∀ i, (π i).Pairwise (fun b c => r b i ≤ r c i)) :
    rightProjection (word r π) = (List.finRange k).flatMap π := by
  simp only [rightProjection, word, List.filterMap_flatMap]
  apply List.flatMap_congr
  intro i _
  change rightProjection (block r π i ++ separator i) = π i
  simp only [rightProjection, List.filterMap_append]
  change rightProjection (block r π i) ++ rightProjection (separator i) = π i
  rw [rightProjection_block r π i (hs i), rightProjection_separator, List.append_nil]

theorem restrictPair_rightProjection (w : List (Alphabet k B)) (b c : B) :
    Crown.restrictPair w (Sum.inr b) (Sum.inr c) =
      (Crown.restrictPair (rightProjection w) b c).map Sum.inr := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | inl a => simpa [Crown.restrictPair, rightProjection, List.filterMap_cons] using ih
    | inr a =>
      by_cases h : a = b ∨ a = c <;>
        simp [Crown.restrictPair, rightProjection, h] at ih ⊢ <;> exact ih

omit [DecidableEq B] in
theorem block_infix_word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) : block r π i <:+: word r π := by
  obtain ⟨as, bs, he⟩ := List.mem_iff_append.mp (List.mem_finRange i)
  refine ⟨as.flatMap (fun j => block r π j ++ separator j),
    separator i ++ bs.flatMap (fun j => block r π j ++ separator j), ?_⟩
  simp [word, he, List.flatMap_append, List.append_assoc]

theorem restrict_gap_left_pair (rank : B → Fin 5) (π : List B) (q : Fin 5)
    (a b : Fin k × Bool) :
    Crown.restrictPair (gap rank π q) (Sum.inl a) (Sum.inl b) = [] := by
  simp [Crown.restrictPair, gap, List.filter_map, Function.comp_def]

theorem different_pair_nonedge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (s t : Bool) (hij : i ≠ j) :
    ¬ Crown.Alternates (word r π) (Sum.inl (i, s)) (Sum.inl (j, t)) := by
  have hr : Crown.restrictPair (block r π i) (Sum.inl (i, s)) (Sum.inl (j, t)) =
      [Sum.inl (i, s), Sum.inl (i, s)] := by
    simp only [block, Crown.restrictPair_append, restrict_gap_left_pair]
    cases s <;> cases t <;>
      simp [Crown.restrictPair, x, y, hij]
  apply Crown.not_alternates_of_repeat (x := Sum.inl (i, s))
  rw [← hr]
  exact List.IsInfix.filter _ (block_infix_word r π i)

def pairChunk (b c : B) (t : Bool) : List B := if t then [b, c] else [c, b]

omit [DecidableEq B] in
theorem pairChunk_front_eq (b c : B) (s t : Bool) (w : List B)
    (hc : (pairChunk b c s ++ pairChunk b c t ++ w).IsChain (· ≠ ·)) : s = t := by
  cases s <;> cases t <;> first | rfl | simp [pairChunk, List.isChain_cons_cons] at hc

omit [DecidableEq B] in
theorem pairChunks_same_head (b c : B) (t : Bool) (ts : List Bool)
    (hc : (pairChunk b c t ++ ts.flatMap (pairChunk b c)).IsChain (· ≠ ·)) :
    ∀ u ∈ ts, u = t := by
  induction ts generalizing t with
  | nil => simp
  | cons s ts ih =>
    have he : t = s := pairChunk_front_eq b c t s (ts.flatMap (pairChunk b c))
      (by simpa only [List.flatMap_cons, List.append_assoc] using hc)
    have ht : (pairChunk b c s ++ ts.flatMap (pairChunk b c)).IsChain (· ≠ ·) := by
      cases t <;> exact hc.tail.tail
    intro u hu
    rcases List.mem_cons.mp hu with hus | hu
    · exact hus.trans he.symm
    · exact (ih s ht u hu).trans he.symm

omit [DecidableEq B] in
theorem pairChunks_nonchain (b c : B) (ts : List Bool)
    (hf : false ∈ ts) (ht : true ∈ ts) :
    ¬ (ts.flatMap (pairChunk b c)).IsChain (· ≠ ·) := by
  intro hc
  cases ts with
  | nil => simp at hf
  | cons s ts =>
    have hh := pairChunks_same_head b c s ts hc
    cases s with
    | false => exact Bool.noConfusion (hh true (by simpa using ht))
    | true => exact Bool.noConfusion (hh false (by simpa using hf))

theorem permutations_nonedge (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) (b c : B) (hbc : b ≠ c)
    (hf : ∃ i, Orders.Before (π i) b c) (hr : ∃ i, Orders.Before (π i) c b) :
    ¬ Crown.Alternates ((List.finRange k).flatMap π) b c := by
  let ts : List Bool := (List.finRange k).map fun i => decide ((π i).idxOf b < (π i).idxOf c)
  have hrestrict : Crown.restrictPair ((List.finRange k).flatMap π) b c =
      ts.flatMap (pairChunk b c) := by
    simp only [Crown.restrictPair, List.filter_flatMap, ts, List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    simpa only [Crown.restrictPair, pairChunk, decide_eq_true_eq] using
      restrictPair_permutation (π i) (hπ i).1 b c ((hπ i).2 b) ((hπ i).2 c) hbc
  have htrue : true ∈ ts := by
    obtain ⟨i, hi⟩ := hf
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, decide_eq_true hi⟩
  have hfalse : false ∈ ts := by
    obtain ⟨i, hi⟩ := hr
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, decide_eq_false (not_lt_of_gt hi)⟩
  unfold Crown.Alternates
  rw [hrestrict]
  exact pairChunks_nonchain b c ts hfalse htrue

theorem right_pair_nonedge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i)
    (b c : B) (hbc : b ≠ c)
    (hf : ∃ i, Orders.Before (π i) b c) (hr : ∃ i, Orders.Before (π i) c b) :
    ¬ Crown.Alternates (word r π) (Sum.inr b) (Sum.inr c) := by
  have hs : ∀ i, (π i).Pairwise (fun b c => r b i ≤ r c i) :=
    fun i => pairwise_of_before (π i) (hπ i).1 (fun b => r b i) (hm i)
  unfold Crown.Alternates
  rw [restrictPair_rightProjection, rightProjection_word r π hs, List.isChain_map]
  simpa only [Sum.inr.injEq, ne_eq, Crown.Alternates] using permutations_nonedge π hπ b c hbc hf hr

theorem restrict_block_same_pair (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) : Crown.restrictPair (block r π j) (x i) (y i) =
      if j = i then [x i, y i, x i, y i] else [] := by
  simp only [block, x, y, Crown.restrictPair_append, restrict_gap_left_pair]
  by_cases h : j = i
  · subst j
    simp [Crown.restrictPair]
  · simp [Crown.restrictPair, h]

theorem restrict_side_list (js : List (Fin k)) (side : Bool) (i : Fin k) :
    Crown.restrictPair (js.map (fun j => Sum.inl (j, side) : Fin k → Alphabet k B))
      (x i) (y i) = List.replicate (js.count i) (Sum.inl (i, side)) := by
  cases side <;>
    simp [Crown.restrictPair, x, y, List.filter_map, Function.comp_def,
      List.filter_eq, List.map_replicate]

theorem restrict_separator_same_pair (i j : Fin k) :
    Crown.restrictPair (separator j : List (Alphabet k B)) (x i) (y i) =
      if i ≠ j ∧ i ≠ finRotate k j then [y i, x i] else [] := by
  rw [separator, Crown.restrictPair_append]
  change Crown.restrictPair ((retained j).map (fun j => Sum.inl (j, true))) (x i) (y i) ++
    Crown.restrictPair ((retained j).map (fun j => Sum.inl (j, false))) (x i) (y i) = _
  rw [restrict_side_list, restrict_side_list, count_retained]
  by_cases h : i ≠ j ∧ i ≠ finRotate k j <;> simp [h, x, y, -finRotate_apply]

def pairTokens (i j : Fin k) : List Bool :=
  (if j = i then [true, true] else []) ++
    if i ≠ j ∧ i ≠ finRotate k j then [false] else []

theorem restrict_word_same_pair (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) : Crown.restrictPair (word r π) (x i) (y i) =
      ((List.finRange k).flatMap (pairTokens i)).flatMap (pairChunk (x i : Alphabet k B) (y i)) := by
  simp only [word, Crown.restrictPair, List.filter_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro j _
  change Crown.restrictPair (block r π j ++ separator j) (x i) (y i) = _
  rw [Crown.restrictPair_append, restrict_block_same_pair, restrict_separator_same_pair]
  by_cases hj : j = i <;> by_cases hi : i ≠ j ∧ i ≠ finRotate k j <;>
    simp [pairTokens, pairChunk, hj, hi, -finRotate_apply]

theorem coordinate_avoiding_two (hk : 3 ≤ k) (a b : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b := by
  classical
  apply Classical.byContradiction
  intro hn
  have h : ∀ i : Fin k, i = a ∨ i = b := by
    intro i
    by_cases ha : i = a
    · exact Or.inl ha
    exact Or.inr (Classical.byContradiction (fun hb => hn ⟨i, ha, hb⟩))
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  simp only [Fin.ext_iff] at h0 h1 h2
  omega

theorem same_pair_nonedge (hk : 3 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) (i : Fin k) :
    ¬ Crown.Alternates (word r π) (x i) (y i) := by
  have ht : true ∈ (List.finRange k).flatMap (pairTokens i) := by
    exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp [pairTokens]⟩
  have hf : false ∈ (List.finRange k).flatMap (pairTokens i) := by
    obtain ⟨j, hji, hjr⟩ := coordinate_avoiding_two hk i ((finRotate k).symm i)
    have hir : i ≠ finRotate k j := by
      intro he
      apply hjr
      rw [he, Equiv.symm_apply_apply]
    exact List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
      by simp [pairTokens, hji, Ne.symm hji, hir, -finRotate_apply]⟩
  unfold Crown.Alternates
  rw [restrict_word_same_pair]
  exact pairChunks_nonchain (x i) (y i) _ hf ht

def RankAdjacent (q : Fin 5) (side : Bool) : Prop :=
  if side then q = 2 ∨ q = 3 else q = 1 ∨ q = 2

def beforeCount (q : Fin 5) (side : Bool) : ℕ :=
  (q.val + if side then 0 else 1) / 2

def crossLocal (q : Fin 5) (side : Bool) (a b : Alphabet k B) : List (Alphabet k B) :=
  List.replicate (beforeCount q side) a ++ [b] ++
    List.replicate (2 - beforeCount q side) a

theorem rank_cases (q : Fin 5) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by
  have hq := q.isLt
  simp only [Fin.ext_iff]
  omega

omit [DecidableEq B] in
theorem crossLocal_edge (q : Fin 5) (side : Bool) (a b : Alphabet k B)
    (h : RankAdjacent q side) : crossLocal q side a b = [a, b, a] := by
  rcases rank_cases q with hq | hq | hq | hq | hq <;> subst q <;> cases side <;>
    simp [RankAdjacent, crossLocal, beforeCount] at h ⊢

omit [DecidableEq B] in
theorem crossLocal_nonedge (q : Fin 5) (side : Bool) (a b : Alphabet k B)
    (h : ¬ RankAdjacent q side) : ¬ (crossLocal q side a b).IsChain (· ≠ ·) := by
  rcases rank_cases q with hq | hq | hq | hq | hq <;> subst q <;> cases side <;>
    simp [RankAdjacent, crossLocal, beforeCount, List.isChain_cons_cons] at h ⊢

theorem restrict_gap_cross (rank : B → Fin 5) (π : List B) (q : Fin 5)
    (a : Fin k × Bool) (b : B) (hb : π.count b = 1) :
    Crown.restrictPair (gap rank π q) (Sum.inl a) (Sum.inr b) =
      if rank b = q then [Sum.inr b] else [] := by
  rw [restrictPair_of_not_mem_left _ _ _ (by simp [gap]), List.filter_eq, count_gap_right]
  by_cases h : rank b = q <;> simp [h, hb]

theorem restrict_block_cross (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) (b : B) (hb : (π j).count b = 1) :
    Crown.restrictPair (block r π j) (Sum.inl (i, side)) (Sum.inr b) =
      if j = i then crossLocal (r b i) side (Sum.inl (i, side)) (Sum.inr b)
      else [Sum.inr b] := by
  simp only [block, Crown.restrictPair_append, restrict_gap_cross _ _ _ _ _ hb]
  by_cases hji : j = i
  · subst j
    rcases rank_cases (r b i) with hq | hq | hq | hq | hq <;> cases side <;>
      simp [Crown.restrictPair, x, y, hq, crossLocal, beforeCount]
  · rcases rank_cases (r b j) with hq | hq | hq | hq | hq <;> cases side <;>
      simp [Crown.restrictPair, x, y, hq, hji]

theorem restrict_separator_cross (i j : Fin k) (side : Bool) (b : B) :
    Crown.restrictPair (separator j : List (Alphabet k B)) (Sum.inl (i, side)) (Sum.inr b) =
      if i ≠ j ∧ i ≠ finRotate k j then [Sum.inl (i, side)] else [] := by
  rw [Crown.restrictPair_comm, restrictPair_of_not_mem_left _ _ _
    (by simp [separator, x, y]), List.filter_eq, count_separator_left]
  by_cases h : i ≠ j ∧ i ≠ finRotate k j <;> simp [h, -finRotate_apply]

theorem cross_nonedge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (side : Bool) (b : B) (hb : (π i).count b = 1)
    (hn : ¬ RankAdjacent (r b i) side) :
    ¬ Crown.Alternates (word r π) (Sum.inl (i, side)) (Sum.inr b) := by
  intro hc
  have hi := List.IsInfix.filter
    (fun a => decide (a = Sum.inl (i, side) ∨ a = Sum.inr b)) (block_infix_word r π i)
  have hlocal := crownChainSegment hc hi
  change (Crown.restrictPair (block r π i) (Sum.inl (i, side)) (Sum.inr b)).IsChain (· ≠ ·) at hlocal
  rw [restrict_block_cross r π i i side b hb, if_pos rfl] at hlocal
  exact crossLocal_nonedge (r b i) side (Sum.inl (i, side)) (Sum.inr b) hn hlocal

def edgeCell (a b : Alphabet k B) (i j : Fin k) : List (Alphabet k B) :=
  if j = i then [a, b, a] else if i = finRotate k j then [b] else [b, a]

omit [DecidableEq B] in
theorem edgeCell_nonempty (a b : Alphabet k B) (i j : Fin k) : edgeCell a b i j ≠ [] := by
  unfold edgeCell
  split_ifs <;> simp

omit [DecidableEq B] in
theorem edgeCell_chain (a b : Alphabet k B) (hab : a ≠ b) (i j : Fin k) :
    (edgeCell a b i j).IsChain (· ≠ ·) := by
  unfold edgeCell
  split_ifs <;> simp [List.isChain_cons_cons, hab, Ne.symm hab]

omit [DecidableEq B] in
theorem edgeCell_boundary (hk : 2 ≤ k) (a b : Alphabet k B) (hab : a ≠ b) (i j : Fin k) :
    ∀ u ∈ (edgeCell a b i j).getLast?, ∀ v ∈ (edgeCell a b i (finRotate k j)).head?, u ≠ v := by
  by_cases hji : j = i
  · subst j
    have hi := rotate_ne hk i
    simp only [edgeCell, if_neg hi]
    split_ifs <;> simp [hab]
  · by_cases hir : i = finRotate k j
    · have hjr : j ≠ finRotate k j := Ne.symm (rotate_ne hk j)
      simp [edgeCell, hir, hjr, Ne.symm hab, -finRotate_apply]
    · simp only [edgeCell, if_neg hji, if_neg hir, if_neg (Ne.symm hir)]
      split_ifs <;> simp [hab]

theorem finRange_successor_chain (k : ℕ) :
    (List.finRange k).IsChain (fun i j => j = finRotate k i) := by
  apply List.isChain_iff_getElem.mpr
  intro n hn
  simp only [List.length_finRange] at hn
  simp only [List.getElem_finRange]
  cases k with
  | zero => omega
  | succ m => exact (finRotate_of_lt (by omega : n < m)).symm

omit [DecidableEq B] in
theorem edgeCells_chain (hk : 2 ≤ k) (a b : Alphabet k B) (hab : a ≠ b) (i : Fin k) :
    ((List.finRange k).flatMap (edgeCell a b i)).IsChain (· ≠ ·) := by
  rw [List.flatMap_def]
  apply (List.isChain_flatten ?_).mpr
  · refine ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
      exact edgeCell_chain a b hab i j
    · rw [List.isChain_map]
      apply (finRange_successor_chain k).imp
      intro j l he
      subst l
      exact edgeCell_boundary hk a b hab i j
  · intro he
    obtain ⟨j, _, hj⟩ := List.mem_map.mp he
    exact edgeCell_nonempty a b i j hj

theorem restrict_cell_edge (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) (b : B) (hb : (π j).count b = 1)
    (he : RankAdjacent (r b i) side) :
    Crown.restrictPair (block r π j ++ separator j) (Sum.inl (i, side)) (Sum.inr b) =
      edgeCell (Sum.inl (i, side)) (Sum.inr b) i j := by
  rw [Crown.restrictPair_append, restrict_block_cross r π i j side b hb,
    restrict_separator_cross]
  by_cases hji : j = i
  · subst j
    simp [edgeCell, crossLocal_edge _ _ _ _ he]
  · by_cases hir : i = finRotate k j
    · have hjr : j ≠ finRotate k j := fun hh => hji (hh.trans hir.symm)
      simp [edgeCell, hir, hjr, -finRotate_apply]
    · simp [edgeCell, hji, Ne.symm hji, hir, -finRotate_apply]

theorem cross_edge (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (side : Bool) (b : B) (hb : ∀ j, (π j).count b = 1)
    (he : RankAdjacent (r b i) side) :
    Crown.Alternates (word r π) (Sum.inl (i, side)) (Sum.inr b) := by
  have hw : Crown.restrictPair (word r π) (Sum.inl (i, side)) (Sum.inr b) =
      (List.finRange k).flatMap (edgeCell (Sum.inl (i, side)) (Sum.inr b) i) := by
    simp only [word, Crown.restrictPair, List.filter_flatMap]
    apply List.flatMap_congr
    intro j _
    exact restrict_cell_edge r π i j side b (hb j) he
  unfold Crown.Alternates
  rw [hw]
  exact edgeCells_chain hk _ _ (by simp) i

theorem cross_iff (hk : 2 ≤ k) (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i : Fin k) (side : Bool) (b : B) (hb : ∀ j, (π j).count b = 1) :
    Crown.Alternates (word r π) (Sum.inl (i, side)) (Sum.inr b) ↔ RankAdjacent (r b i) side := by
  constructor
  · intro ha
    exact Classical.byContradiction (fun hn => cross_nonedge r π i side b (hb i) hn ha)
  · exact cross_edge hk r π i side b hb

theorem left_pair_nonedge (hk : 3 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (a b : Fin k × Bool) (hab : a ≠ b) :
    ¬ Crown.Alternates (word r π) (Sum.inl a) (Sum.inl b) := by
  obtain ⟨i, s⟩ := a
  obtain ⟨j, t⟩ := b
  by_cases hij : i = j
  · subst j
    cases s <;> cases t
    · exact False.elim (hab rfl)
    · exact same_pair_nonedge hk r π i
    · rw [Crown.alternates_comm]
      exact same_pair_nonedge hk r π i
    · exact False.elim (hab rfl)
  · exact different_pair_nonedge r π i j s t hij

def rankGraph (r : B → Ranks.CompletedRow (Fin k)) : SimpleGraph (Alphabet k B) where
  Adj a b := match a, b with
    | Sum.inl p, Sum.inr b => RankAdjacent (r b p.1) p.2
    | Sum.inr b, Sum.inl p => RankAdjacent (r b p.1) p.2
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> simp⟩


theorem word_represents_rankGraph (hk : 3 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i)
    (ho : ∀ b c, b ≠ c → (∃ i, Orders.Before (π i) b c) ∧
      (∃ i, Orders.Before (π i) c b)) :
    Crown.Represents (rankGraph r) k (word r π) := by
  have hk2 : 2 ≤ k := by omega
  have hc : ∀ b j, (π j).count b = 1 :=
    fun b j => List.count_eq_one_of_mem (hπ j).1 ((hπ j).2 b)
  refine ⟨by omega, word_uniform hk2 r π hπ, ?_⟩
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hn := left_pair_nonedge hk r π a b (fun he => hab (congrArg Sum.inl he))
      exact ⟨False.elim, fun ha => False.elim (hn ha)⟩
    | inr b => exact (cross_iff hk2 r π a.1 a.2 b (hc b)).symm
  | inr a =>
    cases b with
    | inl b =>
      rw [Crown.alternates_comm]
      exact (cross_iff hk2 r π b.1 b.2 a (hc a)).symm
    | inr b =>
      have hab' : a ≠ b := fun he => hab (congrArg Sum.inr he)
      have hn := right_pair_nonedge r π hπ hm a b hab' (ho a b hab').1 (ho a b hab').2
      exact ⟨False.elim, fun ha => False.elim (hn ha)⟩


def initialRankGraph (rows : B → Ranks.InitialRow (Fin k)) : SimpleGraph (Alphabet k B) :=
  rankGraph (fun b => Ranks.complete (rows b) false)

end Crown.Blocks

/- Source module Crown.Orientations -/
namespace Crown.Orientations

open Crown.Ranks

abbrev NeighbourRow (I : Type*) := I → Bool × Bool

def entry : Bool × Bool → Bool → Option (Fin 3)
  | (false, false), _ => none
  | (true, true), _ => some 1
  | (true, false), o => if o then some 2 else some 0
  | (false, true), o => if o then some 0 else some 2

def row {I : Type*} (N : NeighbourRow I) (o : I → Bool) : InitialRow I :=
  fun i => entry (N i) (o i)

end Crown.Orientations

/- Source module Crown.BalancedLarge -/
namespace Crown.BalancedLarge

variable {k : ℕ} {B : Type*}

def bit (p : Bool × Bool) (side : Bool) : Bool := if side then p.2 else p.1

def rawGraph (N : B → Orientations.NeighbourRow (Fin k)) :
    SimpleGraph (Blocks.Alphabet k B) where
  Adj a b := match a, b with
    | Sum.inl p, Sum.inr b => bit (N b p.1) p.2 = true
    | Sum.inr b, Sum.inl p => bit (N b p.1) p.2 = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

def endpointSwap (o : Fin k → Bool) : (Fin k × Bool) ≃ (Fin k × Bool) where
  toFun p := (p.1, xor p.2 (o p.1))
  invFun p := (p.1, xor p.2 (o p.1))
  left_inv := by rintro ⟨i, s⟩; cases s <;> cases h : o i <;> simp [h]
  right_inv := by rintro ⟨i, s⟩; cases s <;> cases h : o i <;> simp [h]

def alphabetSwap (o : Fin k → Bool) : Blocks.Alphabet k B ≃ Blocks.Alphabet k B :=
  Equiv.sumCongr (endpointSwap o) (Equiv.refl B)

theorem entry_adjacent : ∀ p : Bool × Bool, ∀ o s : Bool,
    Blocks.RankAdjacent (Ranks.completeEntry (Orientations.entry p o) false) s ↔
      bit p (xor s o) = true := by
  rintro ⟨a, b⟩ o s
  cases a <;> cases b <;> cases o <;> cases s <;>
    simp [Blocks.RankAdjacent, Ranks.completeEntry, Ranks.prescribed, Orientations.entry, bit]

theorem swap_adj (N : B → Orientations.NeighbourRow (Fin k)) (o : Fin k → Bool)
    (a b : Blocks.Alphabet k B) :
    (rawGraph N).Adj (alphabetSwap o a) (alphabetSwap o b) ↔
      (Blocks.initialRankGraph (fun b => Orientations.row (N b) o)).Adj a b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b => exact (entry_adjacent (N b a.1) (o a.1) a.2).symm
  | inr a =>
    cases b with
    | inl b => exact (entry_adjacent (N a b.1) (o b.1) b.2).symm
    | inr b => rfl


def matrixGraph {A B : Type*} (M : A → B → Bool) : SimpleGraph (A ⊕ B) where
  Adj a b := match a, b with
    | Sum.inl a, Sum.inr b => M a b = true
    | Sum.inr b, Sum.inl a => M a b = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

noncomputable def pairEquiv (k : ℕ) : (Fin k × Bool) ≃ Fin (2 * k) :=
  Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])


end Crown.BalancedLarge

/- Source module Crown.Baseline -/
namespace Crown.Baseline

variable {k : ℕ} {B : Type*}

def reverseRank (r : Fin 5) : Fin 5 := ⟨4 - r.val, by omega⟩

def extendedRanks (z : Fin k) (r : B → Ranks.CompletedRow (Fin k)) :
    B → Ranks.CompletedRow (Fin (k + 1)) :=
  fun b => Fin.lastCases (reverseRank (r b z)) (r b)

theorem extendedRanks_incomparable (z : Fin k) (r : B → Ranks.CompletedRow (Fin k))
    (b c : B) : ¬ Ranks.StrictBelow (extendedRanks z r b) (extendedRanks z r c) := by
  intro h
  have hfirst := h z.castSucc
  have hlast := h (Fin.last k)
  simp only [extendedRanks, Fin.lastCases_castSucc, Fin.lastCases_last] at hfirst hlast
  change (r b z).val < (r c z).val at hfirst
  change 4 - (r b z).val < 4 - (r c z).val at hlast
  have hb := (r b z).isLt
  have hc := (r c z).isLt
  omega

def alphabetEmbedding : Blocks.Alphabet k B ↪ Blocks.Alphabet (k + 1) B where
  toFun := Sum.map (fun p => (p.1.castSucc, p.2)) id
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [Sum.map_inl, Sum.inl.injEq, Prod.mk.injEq] at h
        have hi := Fin.castSucc_injective k h.1
        exact congrArg Sum.inl (Prod.ext hi h.2)
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (Sum.inr.inj h)


theorem rankGraph_representable [Fintype B] [DecidableEq B] (hk : 2 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) :
    Crown.KRepresentable (Blocks.rankGraph r) (k + 1) := by
  let z : Fin k := ⟨0, by omega⟩
  obtain ⟨π, hπ, hm, ho⟩ := Orders.coordinate_orders (by omega : 2 ≤ k + 1)
    (extendedRanks z r) (fun b c _ => extendedRanks_incomparable z r b c)
  have hrep : Crown.KRepresentable (Blocks.rankGraph (extendedRanks z r)) (k + 1) :=
    ⟨_, Blocks.word_represents_rankGraph (by omega) _ π hπ hm ho⟩
  apply Crown.kRepresentable_of_inducedEmbedding alphabetEmbedding _ hrep
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change Blocks.RankAdjacent (r b a.1) a.2 ↔
        Blocks.RankAdjacent (Fin.lastCases (reverseRank (r b z)) (r b) a.1.castSucc) a.2
      rw [Fin.lastCases_castSucc]
  | inr a =>
    cases b with
    | inl b =>
      change Blocks.RankAdjacent (r a b.1) b.2 ↔
        Blocks.RankAdjacent (Fin.lastCases (reverseRank (r a z)) (r a) b.1.castSucc) b.2
      rw [Fin.lastCases_castSucc]
    | inr b => rfl

theorem raw_representable [Fintype B] [DecidableEq B] (hk : 2 ≤ k)
    (N : B → Orientations.NeighbourRow (Fin k)) :
    Crown.KRepresentable (BalancedLarge.rawGraph N) (k + 1) := by
  let rows := fun b => Orientations.row (N b) (fun _ => false)
  obtain ⟨w, hw⟩ := rankGraph_representable hk (fun b => Ranks.complete (rows b) false)
  exact ⟨w.map (BalancedLarge.alphabetSwap (fun _ => false)),
    Crown.represents_equiv (BalancedLarge.alphabetSwap (fun _ => false))
      (BalancedLarge.swap_adj N (fun _ => false)) hw⟩


theorem matrix_representable [Fintype B] [DecidableEq B] (k : ℕ) (hk : 2 ≤ k)
    (M : Fin (2 * k) → B → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) (k + 1) := by
  let N : B → Orientations.NeighbourRow (Fin k) :=
    fun b i => (M (BalancedLarge.pairEquiv k (i, false)) b,
      M (BalancedLarge.pairEquiv k (i, true)) b)
  let e := Equiv.sumCongr (BalancedLarge.pairEquiv k) (Equiv.refl B)
  obtain ⟨w, hw⟩ := raw_representable hk N
  refine ⟨w.map e, Crown.represents_equiv e ?_ hw⟩
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b => cases a with | mk i s => cases s <;> rfl
  | inr a =>
    cases b with
    | inl b => cases b with | mk i s => cases s <;> rfl
    | inr b => rfl


end Crown.Baseline

/- Source module Crown.GraphPadding -/
namespace Crown.GraphPadding
open Crown.BalancedLarge

variable {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

omit [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] in
theorem of_embeddings (f : A ↪ A') (g : B ↪ B') (k : ℕ)
    (h : ∀ M' : A' → B' → Bool, KRepresentable (matrixGraph M') k)
    (M : A → B → Bool) : KRepresentable (matrixGraph M) k := by
  classical
  let expanded : A' → B' → Bool := Function.extend f
    (fun a => Function.extend g (M a) (fun _ => false)) (fun _ _ => false)
  have hexp (a : A) (b : B) : expanded (f a) (g b) = M a b := by
    dsimp [expanded]
    rw [f.injective.extend_apply, g.injective.extend_apply]
  apply kRepresentable_of_inducedEmbedding (f.sumMap g) ?_ (h expanded)
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change M a b = true ↔ expanded (f a) (g b) = true
      rw [hexp]
  | inr a =>
    cases b with
    | inl b =>
      change M b a = true ↔ expanded (f b) (g a) = true
      rw [hexp]
    | inr b => rfl

theorem of_card_le (hA : Fintype.card A ≤ Fintype.card A')
    (hB : Fintype.card B ≤ Fintype.card B') (k : ℕ)
    (h : ∀ M' : A' → B' → Bool, KRepresentable (matrixGraph M') k)
    (M : A → B → Bool) : KRepresentable (matrixGraph M) k := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hA
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hB
  exact of_embeddings f g k h M

theorem baseline (k : ℕ) (hk : 2 ≤ k) (hA : Fintype.card A ≤ 2*k)
    (M : A → B → Bool) : KRepresentable (matrixGraph M) (k+1) := by
  apply of_card_le (A' := Fin (2*k)) (B' := B) (by simpa using hA) le_rfl
  exact Crown.Baseline.matrix_representable k hk

theorem at_most_four (hA : Fintype.card A ≤ 4) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) 3 := baseline 2 (by decide) hA M

end Crown.GraphPadding

/- Source module Crown.SmallEight -/
namespace Crown.SmallEight
open Crown.BalancedLarge

theorem matrix {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : A → B → Bool) (hN : Fintype.card A + Fintype.card B ≤ 8) :
    KRepresentable (matrixGraph M) 3 := by
  by_cases hA : Fintype.card A ≤ 4
  · exact GraphPadding.at_most_four hA M
  · obtain ⟨w, hw⟩ := GraphPadding.at_most_four (by omega : Fintype.card B ≤ 4)
      (fun b a => M a b)
    refine ⟨w.map (Equiv.sumComm B A), represents_equiv (Equiv.sumComm B A) ?_ hw⟩
    intro a b
    cases a <;> cases b <;> rfl

theorem graph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : Fintype.card V ≤ 8) :
    KRepresentable G 3 := by
  classical
  obtain ⟨c, hc⟩ := hb
  let p : V → Prop := fun v => c v = 0
  let A := {v // p v}
  let B := {v // ¬p v}
  let e : A ⊕ B ≃ V := Equiv.sumCompl p
  let M : A → B → Bool := fun a b => decide (G.Adj a.val b.val)
  have hcard : Fintype.card A + Fintype.card B = Fintype.card V := by
    simpa using Fintype.card_congr e
  obtain ⟨w, hw⟩ := matrix M (by omega)
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

end Crown.SmallEight

theorem OMA.solution : OMA.R_wp_bipartite_graph_R1.H2 := by
  intro V instV instD G hcard hb
  obtain ⟨w, hw⟩ := Crown.SmallEight.graph G hb hcard.le
  exact ⟨w, hw.2⟩
