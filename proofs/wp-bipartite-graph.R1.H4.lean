import OMAReductions.R_wp_bipartite_graph_R1

/-
Adapted from miinadietrich/crown_graphs_maximise, commit
f7496aebabdac7ec8c64ce8f0e14072e8038bd5a. The donor is licensed under
Apache-2.0. Changes select and combine the lower-bound declarations, scope
the finite kernel checks, and translate the words, graphs, and infimum to
the registered statement. The general crown lower bound is due to Glen,
Kitaev and Pyatkin. The finite four-crown proof is due to Colbrook and Drysdale.

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

def crownGraph (n : ℕ) : SimpleGraph (Bool × Fin n) where
  Adj a b := a.1 ≠ b.1 ∧ a.2 ≠ b.2
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def halfCeil (n : ℕ) : ℕ := (n + 1) / 2

end Crown

/- Source module Crown.Words -/
namespace Crown

variable {V : Type*} [DecidableEq V]

theorem restrictPair_comm (w : List V) (a b : V) :
    restrictPair w a b = restrictPair w b a := by
  simp [restrictPair, or_comm]

theorem sum_counts [Fintype V] (w : List V) :
    (∑ v : V, w.count v) = w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem uniform_length [Fintype V] {k : ℕ} {w : List V}
    (h : Uniform k w) : w.length = Fintype.card V * k := by
  calc
    w.length = ∑ v : V, w.count v := (sum_counts w).symm
    _ = ∑ _v : V, k := Finset.sum_congr rfl (fun v _ => h v)
    _ = Fintype.card V * k := by simp

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

theorem one_uniform_complete {G : SimpleGraph V} (h : KRepresentable G 1) :
    ∀ a b, a ≠ b → G.Adj a b := by
  obtain ⟨w, hw⟩ := h
  have hnd : w.Nodup := List.nodup_iff_count.mpr (fun a => by rw [hw.2.1 a])
  intro a b hab
  apply (hw.2.2 a b hab).mpr
  exact (hnd.filter _).isChain

end Crown

/- Source module Crown.Ranks -/
namespace Crown.Ranks

theorem coordinate_avoiding_three (hk : 4 ≤ k) (a b c : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b ∧ i ≠ c := by
  classical
  apply Classical.byContradiction
  intro hn
  have h : ∀ i : Fin k, i = a ∨ i = b ∨ i = c := by
    intro i
    by_cases ha : i = a
    · exact Or.inl ha
    by_cases hb : i = b
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr (Classical.byContradiction (fun hc => hn ⟨i, ha, hb, hc⟩)))
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  have h3 := h ⟨3, by omega⟩
  simp only [Fin.ext_iff] at h0 h1 h2 h3
  omega

end Crown.Ranks

/- Source module Crown.Blocks -/
namespace Crown.Blocks

open scoped BigOperators

variable {B : Type*} [DecidableEq B]

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

end Crown.Blocks

/- Source module Crown.Cyclic -/
namespace Crown

variable {V : Type*} [DecidableEq V]

theorem balanced_chain_endpoints (a b : V) (hab : a ≠ b) (w : List V)
    (hm : ∀ x ∈ w, x = a ∨ x = b) (he : w.count a = w.count b)
    (hc : w.IsChain (· ≠ ·)) :
    ∀ x ∈ w.head?, ∀ y ∈ w.getLast?, x ≠ y := by
  induction w using List.twoStepInduction with
  | nil => simp
  | singleton x =>
    rcases hm x (by simp) with rfl | rfl <;> simp [hab, Ne.symm hab] at he
  | cons_cons x y w ih _ =>
    have hx := hm x (by simp)
    have hy := hm y (by simp)
    have hxy : x ≠ y := (List.isChain_cons_cons.mp hc).1
    have hew : w.count a = w.count b := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        simp_all [List.count_cons, Ne.symm hab]
    have hmw : ∀ z ∈ w, z = a ∨ z = b := fun z hz => hm z (by simp [hz])
    have hcw : w.IsChain (· ≠ ·) := hc.tail.tail
    have hend := ih hmw hew hcw
    cases w with
    | nil => simpa using hxy
    | cons z zs =>
      have hz := hmw z (by simp)
      have hyz : y ≠ z := (List.isChain_cons_cons.mp hc.tail).1
      have hzx : z = x := by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
          rcases hz with rfl | rfl <;>
          first | rfl | exact False.elim (hxy rfl) | exact False.elim (hyz rfl)
      subst z
      simpa using hend

theorem balanced_chain_swap (a b : V) (hab : a ≠ b) (u v : List V)
    (hm : ∀ x ∈ u ++ v, x = a ∨ x = b)
    (he : (u ++ v).count a = (u ++ v).count b)
    (hc : (u ++ v).IsChain (· ≠ ·)) : (v ++ u).IsChain (· ≠ ·) := by
  have hend := balanced_chain_endpoints a b hab (u ++ v) hm he hc
  apply hc.right_of_append.append hc.left_of_append
  intro x hx y hy
  have hu : u ≠ [] := by intro h; simp [h] at hy
  have hv : v ≠ [] := by intro h; simp [h] at hx
  apply Ne.symm
  apply hend y
  · simpa [List.head?_append, hu] using hy
  · simpa [List.getLast?_append, hv] using hx

theorem alternates_append_swap {u v : List V} {a b : V} (hab : a ≠ b)
    (he : (u ++ v).count a = (u ++ v).count b) :
    Alternates (u ++ v) a b ↔ Alternates (v ++ u) a b := by
  have step : ∀ u v : List V, (u ++ v).count a = (u ++ v).count b →
      Alternates (u ++ v) a b → Alternates (v ++ u) a b := by
    intro u v he hc
    rw [Alternates, restrictPair_append] at hc ⊢
    apply balanced_chain_swap a b hab _ _ ?_ ?_ hc
    · intro x hx
      have hx' : x ∈ restrictPair (u ++ v) a b := by
        simpa only [restrictPair_append] using hx
      simpa [restrictPair] using (List.mem_filter.mp hx').2
    · rw [← restrictPair_append]
      simpa [restrictPair, List.count_filter] using he
  exact ⟨step u v he, step v u (by simpa [List.count_append, Nat.add_comm] using he)⟩

theorem represents_append_swap {G : SimpleGraph V} {k : ℕ} {u v : List V}
    (h : Represents G k (u ++ v)) : Represents G k (v ++ u) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro a
    simpa [List.count_append, Nat.add_comm] using h.2.1 a
  · intro a b hab
    exact (h.2.2 a b hab).trans (alternates_append_swap hab ((h.2.1 a).trans (h.2.1 b).symm))

end Crown

/- Source module Crown.CrownLowerSegments -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem exists_segments (v : V) (w : List V) :
    ∃ p : List V, ∃ L : List (List V),
      w = p ++ L.flatMap (fun l => v :: l) ∧ v ∉ p ∧ ∀ l ∈ L, v ∉ l := by
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x w ih =>
    obtain ⟨p,L,hw,hp,hL⟩ := ih
    by_cases hx : x = v
    · subst x
      refine ⟨[],p::L,?_,by simp,?_⟩
      · simp [hw]
      · simpa using And.intro hp hL
    · refine ⟨x::p,L,?_,by simp [hx, Ne.symm hx,hp],hL⟩
      simp [hw]

theorem exists_segments_start (v : V) (w : List V) :
    ∃ L : List (List V), v :: w = L.flatMap (fun l => v :: l) ∧ ∀ l ∈ L, v ∉ l := by
  obtain ⟨p,L,hw,hp,hL⟩ := exists_segments v w
  exact ⟨p::L, by simp [hw], by simpa using And.intro hp hL⟩

theorem count_separator (v : V) (L : List (List V)) (hL : ∀ l ∈ L, v ∉ l) :
    (L.flatMap (fun l => v :: l)).count v = L.length := by
  induction L with
  | nil => simp
  | cons l L ih =>
    have hl := hL l (by simp)
    have ht : ∀ t ∈ L, v ∉ t := fun t ht => hL t (by simp [ht])
    simp [List.count_cons, List.count_eq_zero.mpr hl, ih ht]

theorem segment_infix (v : V) (L : List (List V)) (l : List V) (hl : l ∈ L) :
    l <:+: L.flatMap (fun t => v :: t) := by
  obtain ⟨p,s,hL⟩ := List.mem_iff_append.mp hl
  refine ⟨p.flatMap (fun t => v :: t) ++ [v], s.flatMap (fun t => v :: t), ?_⟩
  simp [hL, List.flatMap_append, List.append_assoc]

theorem repeat_chain_le_one (a : V) (n : ℕ)
    (h : (List.replicate n a).IsChain (· ≠ ·)) : n ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n => simp [List.replicate_succ, List.isChain_cons_cons] at h

theorem segment_neighbour_count_le (v a : V) (L : List (List V))
    (hL : ∀ l ∈ L, v ∉ l) (hc : Crown.Alternates (L.flatMap (fun l => v :: l)) v a)
    (l : List V) (hl : l ∈ L) : l.count a ≤ 1 := by
  have hi := List.IsInfix.filter (fun x => decide (x = v ∨ x = a)) (segment_infix v L l hl)
  have hh := crownChainSegment hc hi
  change (Crown.restrictPair l v a).IsChain (· ≠ ·) at hh
  rw [Blocks.restrictPair_of_not_mem_left l v a (hL l hl), List.filter_eq] at hh
  exact repeat_chain_le_one a _ hh

theorem sum_le_length (ns : List ℕ) (hn : ∀ n ∈ ns, n ≤ 1) : ns.sum ≤ ns.length := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hh := hn n (by simp)
    have ht := ih (fun m hm => hn m (by simp [hm]))
    simp only [List.sum_cons, List.length_cons]
    omega

theorem all_one_of_sum_eq_length (ns : List ℕ) (hn : ∀ n ∈ ns, n ≤ 1)
    (he : ns.sum = ns.length) : ∀ n ∈ ns, n = 1 := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hh := hn n (by simp)
    have ht : ∀ m ∈ ns, m ≤ 1 := fun m hm => hn m (by simp [hm])
    have hs := sum_le_length ns ht
    simp only [List.sum_cons, List.length_cons] at he
    have hn1 : n = 1 := by omega
    have he' : ns.sum = ns.length := by omega
    simpa only [List.mem_cons, forall_eq_or_imp, hn1, true_and] using ih ht he'

theorem segment_neighbour_count (v a : V) (hva : v ≠ a) (L : List (List V))
    (hL : ∀ l ∈ L, v ∉ l) (hc : Crown.Alternates (L.flatMap (fun l => v :: l)) v a)
    (he : (L.flatMap (fun l => v :: l)).count a = L.length) :
    ∀ l ∈ L, l.count a = 1 := by
  have hsum : (L.map (fun l => l.count a)).sum = L.length := by
    simpa only [List.count_flatMap, Function.comp_def, List.count_cons, beq_iff_eq, hva,
      if_false, Nat.zero_add, Nat.add_zero] using he
  have hle : ∀ n ∈ L.map (fun l => l.count a), n ≤ 1 := by
    intro n hn
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hn
    exact segment_neighbour_count_le v a L hL hc l hl
  have hall := all_one_of_sum_eq_length (L.map (fun l => l.count a)) hle
    (by simpa only [List.length_map] using hsum)
  intro l hl
  exact hall _ (List.mem_map.mpr ⟨l,hl,rfl⟩)

end Crown.CrownLower

/- Source module Crown.CrownLowerSplitting -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def IsPermutationOf (A : Set V) (l : List V) : Prop :=
  l.Nodup ∧ ∀ a, a ∈ l ↔ a ∈ A

def Splittable (w : List V) (k : ℕ) (A : Set V) : Prop := by
  classical
  exact ∃ u v : List V, ∃ L : List (List V), w = u ++ v ∧
    (v ++ u).filter (fun a => a ∈ A) = L.flatten ∧
    L.length = k ∧ ∀ l ∈ L, IsPermutationOf A l

theorem neighbourhood_splittable {G : SimpleGraph V} {k : ℕ} {w : List V}
    (hw : Crown.Represents G k w) (v : V) : Splittable w k {a | G.Adj v a} := by
  classical
  have hv : v ∈ w := List.count_pos_iff.mp (by rw [hw.2.1 v]; exact hw.1)
  obtain ⟨u,t,hwt⟩ := List.mem_iff_append.mp hv
  have hrot : Crown.Represents G k ((v :: t) ++ u) :=
    Crown.represents_append_swap (by simpa only [hwt] using hw)
  obtain ⟨L,hL,hno⟩ := exists_segments_start v (t ++ u)
  have hrep : Crown.Represents G k (L.flatMap (fun l => v :: l)) := by
    rw [← hL]; exact hrot
  have hlen : L.length = k := (count_separator v L hno).symm.trans (hrep.2.1 v)
  have hcount : ∀ a, G.Adj v a → ∀ l ∈ L, l.count a = 1 := by
    intro a hva
    have hne : v ≠ a := G.ne_of_adj hva
    exact segment_neighbour_count v a hne L hno ((hrep.2.2 v a hne).mp hva)
      ((hrep.2.1 a).trans hlen.symm)
  let P := L.map (fun l => l.filter (fun a => G.Adj v a))
  refine ⟨u,v::t,P,hwt,?_,by simpa [P] using hlen,?_⟩
  · change ((v::t)++u).filter (fun a => G.Adj v a) = P.flatten
    rw [show (v::t)++u = L.flatMap (fun l => v::l) from hL]
    simp [P, List.flatMap_def, Function.comp_def]
  · intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    constructor
    · apply List.nodup_iff_count_eq_one.mpr
      intro a ha
      have hadj : G.Adj v a := by simpa using (List.mem_filter.mp ha).2
      rw [List.count_filter (by simpa using hadj)]
      exact hcount a hadj l hl
    · intro a
      constructor
      · intro ha; simpa using (List.mem_filter.mp ha).2
      · intro ha
        apply List.mem_filter.mpr
        exact ⟨List.count_pos_iff.mp (by rw [hcount a ha l hl]; omega), by simpa using ha⟩

end Crown.CrownLower

/- Source module Crown.CrownLowerOrder -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def PrefixOrder (w : List V) (a b : V) : Prop :=
  ∀ p, p <+: w → p.count b ≤ p.count a ∧ p.count a ≤ p.count b + 1

def DirectedChain (w : List V) (a b : V) : Prop :=
  Crown.Alternates w a b ∧ ∀ x ∈ (Crown.restrictPair w a b).head?, x = a

theorem prefixOrder_cons_first (w : List V) (a b : V) (hab : a ≠ b) :
    PrefixOrder (a::w) a b ↔ PrefixOrder w b a := by
  constructor
  · intro h p hp
    have hh := h (a::p) (List.cons_prefix_cons.mpr ⟨rfl,hp⟩)
    simp only [List.count_cons, beq_iff_eq, hab, if_false, if_true,
      Nat.zero_add, Nat.add_zero] at hh
    omega
  · intro h p hp
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
    · simp
    · have hh := h t ht
      simp only [List.count_cons, beq_iff_eq, hab, if_false, if_true,
        Nat.zero_add, Nat.add_zero]
      omega

theorem prefixOrder_cons_second (w : List V) (a b : V) (hab : a ≠ b) :
    ¬ PrefixOrder (b::w) a b := by
  intro h
  have hh := h [b] (by simp)
  simpa [hab,Ne.symm hab] using hh.1

theorem prefixOrder_cons_other (w : List V) (a b x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
    PrefixOrder (x::w) a b ↔ PrefixOrder w a b := by
  constructor
  · intro h p hp
    simpa [List.count_cons,hxa,hxb] using h (x::p) (List.cons_prefix_cons.mpr ⟨rfl,hp⟩)
  · intro h p hp
    rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
    · simp
    · simpa [List.count_cons,hxa,hxb] using h t ht

theorem directedChain_cons_first (w : List V) (a b : V) (hab : a ≠ b) :
    DirectedChain (a::w) a b ↔ DirectedChain w b a := by
  have he : Crown.restrictPair (a::w) a b = a :: Crown.restrictPair w a b := by
    simp [Crown.restrictPair]
  have hr := Crown.restrictPair_comm w b a
  simp only [DirectedChain,Crown.Alternates,he,hr,List.isChain_cons,List.head?_cons,
    Option.mem_some_iff,forall_eq,and_true]
  constructor
  · rintro ⟨⟨hh,hc⟩,_⟩
    refine ⟨hc,?_⟩
    intro x hx
    have hm := List.mem_of_mem_head? hx
    have hm' : x = a ∨ x = b := by simpa [Crown.restrictPair] using (List.mem_filter.mp hm).2
    exact hm'.resolve_left (fun hxa => hh x hx hxa.symm)
  · rintro ⟨hc,hh⟩
    refine ⟨⟨?_,hc⟩,?_⟩
    · intro x hx
      simpa [hh x hx] using hab
    · intro x hx; exact hx.symm

theorem directedChain_cons_second (w : List V) (a b : V) (hab : a ≠ b) :
    ¬ DirectedChain (b::w) a b := by
  intro h
  have he : Crown.restrictPair (b::w) a b = b :: Crown.restrictPair w a b := by
    simp [Crown.restrictPair]
  have hh := h.2 b (by rw [he]; simp)
  exact hab hh.symm

theorem directedChain_cons_other (w : List V) (a b x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
    DirectedChain (x::w) a b ↔ DirectedChain w a b := by
  simp [DirectedChain,Crown.Alternates,Crown.restrictPair,hxa,hxb]

theorem prefixOrder_iff_directedChain (w : List V) (a b : V) (hab : a ≠ b) :
    PrefixOrder w a b ↔ DirectedChain w a b := by
  induction w generalizing a b with
  | nil => simp [PrefixOrder,DirectedChain,Crown.Alternates,Crown.restrictPair]
  | cons x w ih =>
    by_cases hxa : x = a
    · subst x
      rw [prefixOrder_cons_first w a b hab,directedChain_cons_first w a b hab]
      exact ih b a (Ne.symm hab)
    · by_cases hxb : x = b
      · subst x
        exact iff_of_false (prefixOrder_cons_second w a b hab) (directedChain_cons_second w a b hab)
      · rw [prefixOrder_cons_other w a b x hxa hxb,directedChain_cons_other w a b x hxa hxb]
        exact ih a b hab

theorem alternates_of_between (w : List V) (a b x : V) (hab : a ≠ b)
    (hax : PrefixOrder w a x) (hxb : PrefixOrder w x b)
    (hbound : ∀ p, p <+: w → p.count a ≤ p.count b + 1) : Crown.Alternates w a b := by
  apply ((prefixOrder_iff_directedChain w a b hab).mp ?_).1
  intro p hp
  exact ⟨Nat.le_trans (hxb p hp).1 (hax p hp).1,hbound p hp⟩

end Crown.CrownLower

/- Source module Crown.CrownLowerBetween -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem permutation_prefix_bound (A : Set V) (L : List (List V))
    (hL : ∀ l ∈ L, IsPermutationOf A l) (a b : V) (ha : a ∈ A) (hb : b ∈ A) :
    ∀ p, p <+: L.flatten → p.count a ≤ p.count b + 1 := by
  induction L with
  | nil =>
    intro p hp
    have hp' : p = [] := by simpa using hp
    subst p
    simp
  | cons l L ih =>
    have hl := hL l (by simp)
    have ht : ∀ t ∈ L, IsPermutationOf A t := fun t ht => hL t (by simp [ht])
    have hca : l.count a = 1 := List.count_eq_one_of_mem hl.1 ((hl.2 a).mpr ha)
    have hcb : l.count b = 1 := List.count_eq_one_of_mem hl.1 ((hl.2 b).mpr hb)
    intro p hp
    change p <+: l ++ L.flatten at hp
    rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append l L.flatten) with hpl | hlp
    · have hle := List.Sublist.count_le a hpl.sublist
      omega
    · obtain ⟨t,rfl⟩ := hlp
      have htp : t <+: L.flatten := List.prefix_append_right_inj l |>.mp hp
      have hi := ih ht t htp
      simpa only [List.count_append,hca,hcb,Nat.add_assoc] using Nat.add_le_add_left hi 1

theorem filtered_permutation_prefix_bound (A : Set V) [DecidablePred (· ∈ A)]
    (w : List V) (L : List (List V)) (hw : w.filter (fun a => a ∈ A) = L.flatten)
    (hL : ∀ l ∈ L, IsPermutationOf A l) (a b : V) (ha : a ∈ A) (hb : b ∈ A) :
    ∀ p, p <+: w → p.count a ≤ p.count b + 1 := by
  intro p hp
  have hpf := hp.filter (fun a => decide (a ∈ A))
  rw [hw] at hpf
  have h := permutation_prefix_bound A L hL a b ha hb _ hpf
  rw [List.count_filter (p := fun x => decide (x ∈ A)) (a := a) (by simpa using ha),
    List.count_filter (p := fun x => decide (x ∈ A)) (a := b) (by simpa using hb)] at h
  exact h

theorem between_permutations {G : SimpleGraph V} {k : ℕ} {w : List V}
    (hrep : Crown.Represents G k w) (A : Set V) [DecidablePred (· ∈ A)]
    (L : List (List V)) (hw : w.filter (fun a => a ∈ A) = L.flatten)
    (hL : ∀ l ∈ L, IsPermutationOf A l) (a b x : V)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hax : G.Adj a x) (hxb : G.Adj x b)
    (hafirst : ∀ y ∈ (Crown.restrictPair w a x).head?, y = a)
    (hxfirst : ∀ y ∈ (Crown.restrictPair w x b).head?, y = x) : G.Adj a b := by
  apply (hrep.2.2 a b hab).mpr
  apply alternates_of_between w a b x hab
  · exact (prefixOrder_iff_directedChain w a x (G.ne_of_adj hax)).mpr
      ⟨(hrep.2.2 a x (G.ne_of_adj hax)).mp hax,hafirst⟩
  · exact (prefixOrder_iff_directedChain w x b (G.ne_of_adj hxb)).mpr
      ⟨(hrep.2.2 x b (G.ne_of_adj hxb)).mp hxb,hxfirst⟩
  · exact filtered_permutation_prefix_bound A w L hw hL a b ha hb

end Crown.CrownLower

/- Source module Crown.CrownLowerIntervals -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem binary_chain_count_le (a b : V) (hab : a ≠ b) (w : List V)
    (hm : ∀ x ∈ w, x = a ∨ x = b) (hc : w.IsChain (· ≠ ·)) :
    w.count a ≤ w.count b + 1 := by
  induction w using List.twoStepInduction with
  | nil => simp
  | singleton x =>
    rcases hm x (by simp) with rfl | rfl <;> simp [hab,Ne.symm hab]
  | cons_cons x y w ih _ =>
    have hx := hm x (by simp)
    have hy := hm y (by simp)
    have hxy : x ≠ y := (List.isChain_cons_cons.mp hc).1
    have hmw : ∀ z ∈ w, z = a ∨ z = b := fun z hz => hm z (by simp [hz])
    have hcw : w.IsChain (· ≠ ·) := hc.tail.tail
    have hi := ih hmw hcw
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact False.elim (hxy rfl)
    · simpa [List.count_cons,hab,Ne.symm hab,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Nat.add_le_add_right hi 1
    · simpa [List.count_cons,hab,Ne.symm hab,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        Nat.add_le_add_right hi 1
    · exact False.elim (hxy rfl)

theorem alternating_count_le (a b : V) (hab : a ≠ b) (w : List V)
    (hc : Crown.Alternates w a b) : w.count a ≤ w.count b + 1 := by
  have h := binary_chain_count_le a b hab (Crown.restrictPair w a b) ?_ hc
  · simpa [Crown.restrictPair,List.count_filter] using h
  · intro x hx
    simpa [Crown.restrictPair] using (List.mem_filter.mp hx).2

theorem alternating_factor_count_le (a b : V) (hab : a ≠ b) (w u : List V)
    (hc : Crown.Alternates w a b) (hu : u <:+: w) : u.count a ≤ u.count b + 1 := by
  apply alternating_count_le a b hab u
  exact crownChainSegment hc (List.IsInfix.filter _ hu)

theorem alternating_same_ends_count (a b : V) (hab : a ≠ b) (w : List V)
    (hc : Crown.Alternates w a b)
    (hh : a ∈ (Crown.restrictPair w a b).head?)
    (ht : a ∈ (Crown.restrictPair w a b).getLast?) :
    w.count a = w.count b + 1 := by
  have hp := (prefixOrder_iff_directedChain w a b hab).mpr
    ⟨hc,fun x hx => Option.mem_unique hx hh⟩
  have hcounts := hp w (List.prefix_refl w)
  have hne : w.count a ≠ w.count b := by
    intro he
    have hb := Crown.balanced_chain_endpoints a b hab (Crown.restrictPair w a b) ?_ ?_ hc
    · exact hb a hh a ht rfl
    · intro x hx
      simpa [Crown.restrictPair] using (List.mem_filter.mp hx).2
    · simpa [Crown.restrictPair,List.count_filter] using he
  omega

end Crown.CrownLower

/- Source module Crown.CrownLowerCanonical -/
namespace Crown.CrownLower

variable {V : Type*}

def StartsIn (p : V → Bool) (w : List V) : Prop :=
  ∃ a t, w = a::t ∧ p a = true

def EndsIn (p : V → Bool) (w : List V) : Prop :=
  ∃ t a, w = t ++ [a] ∧ p a = true

theorem startsIn_append (p : V → Bool) (u v : List V) (h : StartsIn p u) :
    StartsIn p (u ++ v) := by
  obtain ⟨a,t,rfl,ha⟩ := h
  exact ⟨a,t++v,rfl,ha⟩

theorem startsIn_of_append (p : V → Bool) (u v : List V) (hu : u ≠ [])
    (h : StartsIn p (u ++ v)) : StartsIn p u := by
  cases u with
  | nil => contradiction
  | cons a u =>
    obtain ⟨b,t,he,hb⟩ := h
    have hab : a = b := (List.cons.inj he).1
    exact ⟨a,u,rfl,by simpa [hab] using hb⟩

theorem first_selected_split (p : V → Bool) (w : List V) (hne : w.filter p ≠ []) :
    ∃ u v, w = u ++ v ∧ u.filter p = [] ∧ StartsIn p v := by
  obtain ⟨a,t,ht⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨u,v,hw,hu,ha,_⟩ := List.filter_eq_cons_iff.mp ht
  exact ⟨u,a::v,hw,by simpa only [List.filter_eq_nil_iff] using hu,⟨a,v,rfl,ha⟩⟩

theorem initial_permutation_blocks (p : V → Bool) (w : List V) (L : List (List V))
    (hne : L ≠ []) (hparts : ∀ l ∈ L, l ≠ []) (hf : w.filter p = L.flatten) :
    ∃ q : List V, ∃ W : List (List V), w = q ++ W.flatten ∧ q.filter p = [] ∧
      W.map (List.filter p) = L ∧ ∀ s ∈ W, StartsIn p s := by
  induction L generalizing w with
  | nil => contradiction
  | cons l L ih =>
    have hl : l ≠ [] := hparts l (by simp)
    have htail : ∀ t ∈ L, t ≠ [] := fun t ht => hparts t (by simp [ht])
    have hfa : w.filter p = l ++ L.flatten := hf
    obtain ⟨u,v,hw,hu,hv⟩ := List.filter_eq_append_iff.mp hfa
    obtain ⟨q,r,hur,hq,hr⟩ := first_selected_split p u (by rw [hu]; exact hl)
    have hrf : r.filter p = l := by simpa [hur,hq] using hu
    cases L with
    | nil =>
      have hv0 : v.filter p = [] := by simpa using hv
      refine ⟨q,[r++v],?_,hq,?_,?_⟩
      · simp [hw,hur,List.append_assoc]
      · simp [hrf,hv0]
      · simpa using startsIn_append p r v hr
    | cons t L =>
      obtain ⟨s,W,hvw,hs,hW,hstart⟩ := ih v (by simp) htail hv
      refine ⟨q,(r++s)::W,?_,hq,?_,?_⟩
      · simp [hw,hur,hvw,List.append_assoc]
      · simp [hrf,hs,hW]
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact startsIn_append p r s hr
        · exact hstart a ha

theorem append_last_blocks (p : V → Bool) (W : List (List V)) (q : List V)
    (hne : W ≠ []) (hq : q.filter p = []) (hstart : ∀ s ∈ W, StartsIn p s) :
    ∃ W' : List (List V), W'.flatten = W.flatten ++ q ∧ W'.map (List.filter p) = W.map (List.filter p) ∧
      ∀ s ∈ W', StartsIn p s := by
  induction W with
  | nil => contradiction
  | cons w W ih =>
    have hw := hstart w (by simp)
    cases W with
    | nil =>
      exact ⟨[w++q],by simp,by simp [hq],by simpa using startsIn_append p w q hw⟩
    | cons t W =>
      obtain ⟨W',he,hm,hs⟩ := ih (by simp) (fun s h => hstart s (by simp [h]))
      exact ⟨w::W',by simp [he,List.append_assoc],by simp [hm],by simpa using And.intro hw hs⟩

theorem canonical_permutation_blocks (p : V → Bool) (w : List V) (L : List (List V))
    (hne : L ≠ []) (hparts : ∀ l ∈ L, l ≠ []) (hf : w.filter p = L.flatten) :
    ∃ q u : List V, ∃ W : List (List V), w = q ++ u ∧
      W.flatten = u ++ q ∧ W.map (List.filter p) = L ∧ ∀ s ∈ W, StartsIn p s := by
  obtain ⟨q,W,hw,hq,hm,hs⟩ := initial_permutation_blocks p w L hne hparts hf
  have hWne : W ≠ [] := by intro he; simp [he] at hm; exact hne hm
  obtain ⟨W',he,hm',hs'⟩ := append_last_blocks p W q hWne hq hs
  exact ⟨q,W.flatten,W',hw,he,hm'.trans hm,hs'⟩

theorem ending_core (p : V → Bool) (w : List V) (hne : w.filter p ≠ []) :
    ∃ c g : List V, w = c ++ g ∧ g.filter p = [] ∧ c ≠ [] ∧ EndsIn p c := by
  induction w with
  | nil => simp at hne
  | cons a w ih =>
    by_cases hw : w.filter p = []
    · have ha : p a = true := by
        cases hpa : p a <;> simp_all
      exact ⟨[a],w,rfl,hw,by simp,⟨[],a,rfl,ha⟩⟩
    · obtain ⟨c,g,hcg,hg,hc,he⟩ := ih hw
      obtain ⟨t,b,hcb,hb⟩ := he
      exact ⟨a::c,g,by simp [hcg],hg,by simp,⟨a::t,b,by simp [hcb],hb⟩⟩

theorem core_and_gap (p : V → Bool) (w : List V) (hs : StartsIn p w) :
    ∃ c g : List V, w = c ++ g ∧ c.filter p = w.filter p ∧ g.filter p = [] ∧
      StartsIn p c ∧ EndsIn p c := by
  have hne : w.filter p ≠ [] := by
    obtain ⟨a,t,rfl,ha⟩ := hs
    simp [ha]
  obtain ⟨c,g,hw,hg,hc,he⟩ := ending_core p w hne
  exact ⟨c,g,hw,by simp [hw,hg],hg,startsIn_of_append p c g hc (hw ▸ hs),he⟩

end Crown.CrownLower

/- Source module Crown.CrownLowerGeometry -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def GoodBlock (A : Set V) [DecidablePred (· ∈ A)] (d : List V × List V) : Prop :=
  IsPermutationOf A (d.1.filter (fun a => a ∈ A)) ∧
    d.2.filter (fun a => a ∈ A) = [] ∧
    StartsIn (fun a => decide (a ∈ A)) d.1 ∧ EndsIn (fun a => decide (a ∈ A)) d.1

def blockWord (D : List (List V × List V)) : List V := D.flatMap (fun d => d.1 ++ d.2)

theorem decompose_good_blocks (A : Set V) [DecidablePred (· ∈ A)] (W : List (List V))
    (hperm : ∀ w ∈ W, IsPermutationOf A (w.filter (fun a => a ∈ A)))
    (hstart : ∀ w ∈ W, StartsIn (fun a => decide (a ∈ A)) w) :
    ∃ D : List (List V × List V), blockWord D = W.flatten ∧ D.length = W.length ∧
      ∀ d ∈ D, GoodBlock A d := by
  induction W with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | cons w W ih =>
    obtain ⟨c,g,hw,hc,hg,hcs,hce⟩ := core_and_gap _ w (hstart w (by simp))
    obtain ⟨D,hD,hlen,hgood⟩ := ih (fun w hw => hperm w (by simp [hw]))
      (fun w hw => hstart w (by simp [hw]))
    refine ⟨(c,g)::D,?_,by simpa using hlen,?_⟩
    · simp [blockWord,hw,← hD]
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨hc.symm ▸ hperm w (by simp),hg,hcs,hce⟩
      · exact hgood d hd

theorem canonical_representation {G : SimpleGraph V} {k : ℕ} {w : List V}
    (hrep : Crown.Represents G k w) (A : Set V) [DecidablePred (· ∈ A)] (hA : A.Nonempty)
    (hsplit : Splittable w k A) :
    ∃ D : List (List V × List V), Crown.Represents G k (blockWord D) ∧ D.length = k ∧
      ∀ d ∈ D, GoodBlock A d := by
  classical
  obtain ⟨u,v,L,hw,hfilter,hlen,hperm⟩ := hsplit
  have hrot : Crown.Represents G k (v++u) := Crown.represents_append_swap (hw ▸ hrep)
  have hk := hrep.1
  have hne : L ≠ [] := by intro he; simp [he] at hlen; omega
  have hparts : ∀ l ∈ L, l ≠ [] := by
    intro l hl he
    obtain ⟨a,ha⟩ := hA
    have hm := ((hperm l hl).2 a).mpr ha
    simpa [he] using hm
  have hfilter' : (v++u).filter (fun a => decide (a ∈ A)) = L.flatten := by
    calc
      _ = (v++u).filter (fun a => @decide (a ∈ A) (Classical.propDecidable _)) := by
        apply List.filter_congr
        intro a ha
        simp
      _ = L.flatten := hfilter
  obtain ⟨q,t,W,hwt,hW,hmap,hstart⟩ := canonical_permutation_blocks
    (fun a => decide (a ∈ A)) (v++u) L hne hparts hfilter'
  have hrot' : Crown.Represents G k W.flatten := by
    rw [hW]
    exact Crown.represents_append_swap (hwt ▸ hrot)
  have hpermW : ∀ s ∈ W, IsPermutationOf A (s.filter (fun a => a ∈ A)) := by
    intro s hs
    apply hperm
    rw [← hmap]
    exact List.mem_map.mpr ⟨s,hs,rfl⟩
  obtain ⟨D,hD,hDL,hgood⟩ := decompose_good_blocks A W hpermW hstart
  refine ⟨D,hD ▸ hrot',?_,hgood⟩
  have hWL : W.length = L.length := by rw [← hmap,List.length_map]
  omega

theorem rotate_block_representation {G : SimpleGraph V} {k : ℕ}
    (P Q : List (List V × List V)) (hrep : Crown.Represents G k (blockWord (P++Q))) :
    Crown.Represents G k (blockWord (Q++P)) := by
  simp only [blockWord,List.flatMap_append] at hrep ⊢
  exact Crown.represents_append_swap hrep

end Crown.CrownLower

/- Source module Crown.CrownLowerCore -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem pair_head_of_prefix (u v : List V) (a b : V) (ha : a ∈ u) (hb : b ∉ u) :
    (Crown.restrictPair (u++v) a b).head? = some a := by
  rw [Crown.restrictPair_append,Crown.restrictPair_comm u a b,
    Blocks.restrictPair_of_not_mem_left u b a hb,List.filter_eq]
  have hc := List.count_pos_iff.mpr ha
  cases he : u.count a with
  | zero => omega
  | succ n => simp [List.replicate_succ]

theorem blockWord_filter (A : Set V) [DecidablePred (· ∈ A)]
    (D : List (List V × List V)) (hD : ∀ d ∈ D, GoodBlock A d) :
    (blockWord D).filter (fun a => a ∈ A) =
      (D.map (fun d => d.1.filter (fun a => a ∈ A))).flatten := by
  unfold blockWord
  rw [List.filter_flatMap,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro d hd
  simpa only [Function.comp_def,List.filter_append,(hD d hd).2.1,List.append_nil]

theorem blockWord_permutations (A : Set V) [DecidablePred (· ∈ A)]
    (D : List (List V × List V)) (hD : ∀ d ∈ D, GoodBlock A d) :
    ∀ l ∈ D.map (fun d => d.1.filter (fun a => a ∈ A)), IsPermutationOf A l := by
  intro l hl
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hl
  exact (hD d hd).1

theorem no_common_neighbour_in_first_core {G : SimpleGraph V} {k : ℕ}
    (A : Set V) [DecidablePred (· ∈ A)] (d : List V × List V)
    (D : List (List V × List V))
    (hrep : Crown.Represents G k (blockWord (d::D)))
    (hD : ∀ t ∈ d::D, GoodBlock A t) (a b x : V)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (has : StartsIn (fun y => decide (y = a)) d.1)
    (hbe : EndsIn (fun y => decide (y = b)) d.1)
    (hax : G.Adj a x) (hxb : G.Adj x b) : x ∉ d.1 := by
  intro hx
  obtain ⟨a',s,hs,ha'⟩ := has
  have haa : a' = a := by simpa using ha'
  subst a'
  obtain ⟨t,b',ht,hb'⟩ := hbe
  have hbb : b' = b := by simpa using hb'
  subst b'
  have hperm := (hD d (by simp)).1
  have hcount : d.1.count b = 1 := by
    have hh := List.count_eq_one_of_mem hperm.1 ((hperm.2 b).mpr hb)
    rw [List.count_filter (p := fun y => decide (y ∈ A)) (a := b) (by simpa using hb)] at hh
    exact hh
  have hbt : b ∉ t := by
    apply List.count_eq_zero.mp
    rw [ht,List.count_append] at hcount
    simpa using hcount
  have hxt : x ∈ t := by
    rw [ht,List.mem_append,List.mem_singleton] at hx
    exact hx.resolve_right (G.ne_of_adj hxb)
  have hafirst : ∀ y ∈ (Crown.restrictPair (blockWord (d::D)) a x).head?, y = a := by
    simp [blockWord,hs,Crown.restrictPair]
  have hxfirst : ∀ y ∈ (Crown.restrictPair (blockWord (d::D)) x b).head?, y = x := by
    have he : blockWord (d::D) = t ++ ([b] ++ d.2 ++ blockWord D) := by
      simp [blockWord,ht,List.append_assoc]
    rw [he,pair_head_of_prefix t _ x b hxt hbt]
    simp
  exact hnab (between_permutations hrep A _ (blockWord_filter A _ hD)
    (blockWord_permutations A _ hD) a b x ha hb hab hax hxb hafirst hxfirst)

end Crown.CrownLower

/- Source module Crown.CrownLowerCounts -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem goodBlock_core_count (A : Set V) [DecidablePred (· ∈ A)]
    (d : List V × List V) (hd : GoodBlock A d) (a : V) (ha : a ∈ A) : d.1.count a = 1 := by
  have h := List.count_eq_one_of_mem hd.1.1 ((hd.1.2 a).mpr ha)
  rw [List.count_filter (p := fun x => decide (x ∈ A)) (a := a) (by simpa using ha)] at h
  exact h

theorem goodBlock_gap_count (A : Set V) [DecidablePred (· ∈ A)]
    (d : List V × List V) (hd : GoodBlock A d) (a : V) (ha : a ∈ A) : d.2.count a = 0 := by
  have h := congrArg (List.count a) hd.2.1
  rw [List.count_filter (p := fun x => decide (x ∈ A)) (a := a) (by simpa using ha)] at h
  simpa using h

theorem goodBlocks_count (A : Set V) [DecidablePred (· ∈ A)]
    (D : List (List V × List V)) (hD : ∀ d ∈ D, GoodBlock A d) (a : V) (ha : a ∈ A) :
    (blockWord D).count a = D.length := by
  induction D with
  | nil => simp [blockWord]
  | cons d D ih =>
    have hd := hD d (by simp)
    have ht := ih (fun d hd => hD d (by simp [hd]))
    change ((d.1 ++ d.2) ++ blockWord D).count a = (d::D).length
    rw [List.count_append,List.count_append,goodBlock_core_count A d hd a ha,
      goodBlock_gap_count A d hd a ha,ht]
    simp [Nat.add_comm]

theorem nodup_endpoints_ne (l : List V) (hn : l.Nodup) (a b : V)
    (hs : StartsIn (fun x => decide (x = a)) l) (he : EndsIn (fun x => decide (x = b)) l)
    (hother : ∃ c ∈ l, c ≠ a) : a ≠ b := by
  intro hab
  subst b
  obtain ⟨a',s,hs,ha'⟩ := hs
  have haa : a' = a := by simpa using ha'
  subst a'
  obtain ⟨t,b,he,hb⟩ := he
  have hba : b = a := by simpa using hb
  subst b
  cases t with
  | nil =>
    obtain ⟨c,hc,hca⟩ := hother
    simp [he] at hc
    exact hca hc
  | cons x t =>
    have hcons : a::s = x::(t++[a]) := by simpa [hs] using he
    have htail : s = t++[a] := (List.cons.inj hcons).2
    have hnot : a ∉ s := (List.nodup_cons.mp (hs ▸ hn)).1
    exact hnot (by simp [htail])

theorem goodBlock_endpoints (A : Set V) [DecidablePred (· ∈ A)]
    (d : List V × List V) (hd : GoodBlock A d)
    (hA : ∀ a ∈ A, ∃ c ∈ A, c ≠ a) :
    ∃ a b : V, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧
      StartsIn (fun x => decide (x = a)) d.1 ∧ EndsIn (fun x => decide (x = b)) d.1 := by
  obtain ⟨a,s,hs,ha⟩ := hd.2.2.1
  obtain ⟨t,b,he,hb⟩ := hd.2.2.2
  have haA : a ∈ A := by simpa using ha
  have hbA : b ∈ A := by simpa using hb
  have hs' : StartsIn (fun x => decide (x = a)) (d.1.filter (fun x => x ∈ A)) :=
    ⟨a,s.filter (fun x => x ∈ A),by simp [hs,haA],by simp⟩
  have he' : EndsIn (fun x => decide (x = b)) (d.1.filter (fun x => x ∈ A)) :=
    ⟨t.filter (fun x => x ∈ A),b,by simp [he,hbA],by simp⟩
  have hab : a ≠ b := by
    apply nodup_endpoints_ne _ hd.1.1 a b hs' he'
    obtain ⟨c,hc,hca⟩ := hA a haA
    exact ⟨c,(hd.1.2 c).mpr hc,hca⟩
  exact ⟨a,b,haA,hbA,hab,⟨a,s,hs,by simp⟩,⟨t,b,he,by simp⟩⟩

end Crown.CrownLower

/- Source module Crown.CrownLowerCapacity -/
namespace Crown.CrownLower

local instance CrownLowerCapacityLocal1 {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩

local instance CrownLowerCapacityLocal2 {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

def leftExcept {n : ℕ} (z : Fin n) : Set (Bool × Fin n) :=
  {v | v.1 = false ∧ v.2 ≠ z}

instance {n : ℕ} (z : Fin n) : DecidablePred (· ∈ leftExcept z) :=
  fun v => inferInstanceAs (Decidable (v.1 = false ∧ v.2 ≠ z))

theorem avoiding_four {n : ℕ} (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ x : Fin n, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
  classical
  have hsmall : ({a,b,c,d} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have hh := Finset.card_le_four (a := a) (b := b) (c := c) (d := d)
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  obtain ⟨x,_,hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  exact ⟨x,by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hx⟩

theorem leftExcept_has_other {n : ℕ} (hn : 4 ≤ n) (z : Fin n) :
    ∀ a ∈ leftExcept z, ∃ c ∈ leftExcept z, c ≠ a := by
  intro a ha
  obtain ⟨i,hiz,hia,_⟩ := Ranks.coordinate_avoiding_three hn z a.2 a.2
  exact ⟨(false,i),⟨rfl,hiz⟩,fun he => hia (congrArg Prod.snd he)⟩

theorem core_avoids_prime {n k : ℕ} (z : Fin n)
    (d : List (Bool × Fin n) × List (Bool × Fin n))
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hrep : Crown.Represents (Crown.crownGraph n) k (blockWord (d::D)))
    (hD : ∀ t ∈ d::D, GoodBlock (leftExcept z) t)
    (a b : Bool × Fin n) (ha : a ∈ leftExcept z) (hb : b ∈ leftExcept z) (hab : a ≠ b)
    (has : StartsIn (fun y => decide (y = a)) d.1)
    (hbe : EndsIn (fun y => decide (y = b)) d.1)
    (x : Fin n) (hxa : x ≠ a.2) (hxb : x ≠ b.2) : (true,x) ∉ d.1 := by
  have hnab : ¬ (Crown.crownGraph n).Adj a b := by
    change ¬ (a.1 ≠ b.1 ∧ a.2 ≠ b.2)
    simp [ha.1,hb.1]
  have hax : (Crown.crownGraph n).Adj a (true,x) := ⟨by simp [ha.1],Ne.symm hxa⟩
  have hxb' : (Crown.crownGraph n).Adj (true,x) b := ⟨by simp [hb.1],hxb⟩
  exact no_common_neighbour_in_first_core (leftExcept z) d D hrep hD a b (true,x)
    ha hb hab hnab has hbe hax hxb'

theorem core_missing_count_le_one {n k : ℕ} (hn : 4 ≤ n) (z : Fin n)
    (d : List (Bool × Fin n) × List (Bool × Fin n))
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hrep : Crown.Represents (Crown.crownGraph n) k (blockWord (d::D)))
    (hD : ∀ t ∈ d::D, GoodBlock (leftExcept z) t) : d.1.count (false,z) ≤ 1 := by
  classical
  obtain ⟨a,b,ha,hb,hab,has,hbe⟩ := goodBlock_endpoints (leftExcept z) d (hD d (by simp))
    (leftExcept_has_other hn z)
  obtain ⟨x,hxz,hxa,hxb⟩ := Ranks.coordinate_avoiding_three hn z a.2 b.2
  have hx := core_avoids_prime z d D hrep hD a b ha hb hab has hbe x hxa hxb
  have hed : (Crown.crownGraph n).Adj (false,z) (true,x) := ⟨by simp,Ne.symm hxz⟩
  have halt := (hrep.2.2 (false,z) (true,x) (by simp)).mp hed
  have hin : d.1 <:+: blockWord (d::D) :=
    ⟨[],d.2 ++ blockWord D,by simp [blockWord,List.append_assoc]⟩
  have hc := alternating_factor_count_le (false,z) (true,x) (by simp) _ d.1 halt hin
  simpa [List.count_eq_zero.mpr hx] using hc

theorem prefix_span_missing_count_le {n k : ℕ} (hn : 5 ≤ n) (z : Fin n)
    (d e : List (Bool × Fin n) × List (Bool × Fin n))
    (T R : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hrep : Crown.Represents (Crown.crownGraph n) k (blockWord (d::(T ++ e::R))))
    (hD : ∀ t ∈ d::(T ++ e::R), GoodBlock (leftExcept z) t) :
    (blockWord (d::T) ++ e.1).count (false,z) ≤ T.length + 2 := by
  classical
  have hd := hD d (by simp)
  have he := hD e (by simp)
  obtain ⟨a,b,ha,hb,hab,has,hbe⟩ := goodBlock_endpoints (leftExcept z) d hd
    (leftExcept_has_other (by omega) z)
  obtain ⟨_,c,_,hc,_,_,hce⟩ := goodBlock_endpoints (leftExcept z) e he
    (leftExcept_has_other (by omega) z)
  obtain ⟨x,hxz,hxa,hxb,hxc⟩ := avoiding_four hn z a.2 b.2 c.2
  have hx := core_avoids_prime z d (T++e::R) hrep hD a b ha hb hab has hbe x hxa hxb
  let U := blockWord (d::T) ++ e.1
  have hin : U <:+: blockWord (d::(T++e::R)) :=
    ⟨[],e.2 ++ blockWord R,by simp [U,blockWord,List.flatMap_append,List.append_assoc]⟩
  have hadj : (Crown.crownGraph n).Adj c (true,x) := ⟨by simp [hc.1],Ne.symm hxc⟩
  have hne : c ≠ (true,x) := (Crown.crownGraph n).ne_of_adj hadj
  have hchain : Crown.Alternates U c (true,x) :=
    crownChainSegment ((hrep.2.2 c (true,x) hne).mp hadj) (List.IsInfix.filter _ hin)
  have hcmem : c ∈ d.1 := List.count_pos_iff.mp (by rw [goodBlock_core_count _ d hd c hc]; omega)
  have hhead : c ∈ (Crown.restrictPair U c (true,x)).head? := by
    have hu : U = d.1 ++ (d.2 ++ blockWord T ++ e.1) := by simp [U,blockWord,List.append_assoc]
    rw [hu,pair_head_of_prefix d.1 _ c (true,x) hcmem hx]
    simp
  have hlast : c ∈ (Crown.restrictPair U c (true,x)).getLast? := by
    obtain ⟨s,c',hs,hc'⟩ := hce
    have hcc : c' = c := by simpa using hc'
    subst c'
    simp [U,hs,Crown.restrictPair,List.filter_append,List.append_assoc]
  have hbalance := alternating_same_ends_count c (true,x) hne U hchain hhead hlast
  have hccount : U.count c = T.length + 2 := by
    have hpre : ∀ t ∈ d::T, GoodBlock (leftExcept z) t := by
      intro t ht
      rcases List.mem_cons.mp ht with ht | ht
      · exact ht ▸ hd
      · exact hD t (by simp [ht])
    change (blockWord (d::T) ++ e.1).count c = T.length + 2
    rw [List.count_append,goodBlocks_count _ (d::T) hpre c hc,goodBlock_core_count _ e he c hc]
    simp
  have hadjz : (Crown.crownGraph n).Adj (false,z) (true,x) := ⟨by simp,Ne.symm hxz⟩
  have hchainz := (hrep.2.2 (false,z) (true,x) (by simp)).mp hadjz
  have hbound := alternating_factor_count_le (false,z) (true,x) (by simp) _ U hchainz hin
  change U.count (false,z) ≤ T.length + 2
  omega

end Crown.CrownLower

/- Source module Crown.CrownLowerCycle -/
namespace Crown.CrownLower

variable {V : Type*}

def weightSum (f : V → ℤ) (L : List V) : ℤ := (L.map f).sum

@[simp] theorem weightSum_nil (f : V → ℤ) : weightSum f [] = 0 := rfl

@[simp] theorem weightSum_cons (f : V → ℤ) (a : V) (L : List V) :
    weightSum f (a::L) = f a + weightSum f L := by simp [weightSum]

@[simp] theorem weightSum_append (f : V → ℤ) (L M : List V) :
    weightSum f (L++M) = weightSum f L + weightSum f M := by simp [weightSum]

theorem exists_minimum_prefix (f : V → ℤ) (L : List V) :
    ∃ u v, L = u ++ v ∧ ∀ p, p <+: L → weightSum f u ≤ weightSum f p := by
  induction L with
  | nil =>
    refine ⟨[],[],rfl,?_⟩
    intro p hp
    have : p = [] := List.prefix_nil.mp hp
    simp [this]
  | cons a L ih =>
    obtain ⟨u,v,hL,hmin⟩ := ih
    by_cases hnonneg : 0 ≤ f a + weightSum f u
    · refine ⟨[],a::L,rfl,?_⟩
      intro p hp
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
      · simp
      · have := hmin t ht
        simp only [weightSum_nil,weightSum_cons]
        omega
    · refine ⟨a::u,v,by simp [hL],?_⟩
      intro p hp
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
      · simp only [weightSum_nil,weightSum_cons]
        omega
      · have := hmin t ht
        simp only [weightSum_cons]
        omega

theorem exists_nonnegative_rotation (f : V → ℤ) (L : List V)
    (hzero : weightSum f L = 0) :
    ∃ u v, L = u ++ v ∧ ∀ p, p <+: v ++ u → 0 ≤ weightSum f p := by
  obtain ⟨u,v,hL,hmin⟩ := exists_minimum_prefix f L
  refine ⟨u,v,hL,?_⟩
  have htotal : weightSum f u + weightSum f v = 0 := by simpa [hL] using hzero
  intro p hp
  rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append v u) with h | h
  · have hp' : u ++ p <+: L := by
      rw [hL]
      exact List.prefix_append_right_inj u |>.mpr h
    have hh := hmin (u++p) hp'
    simp only [weightSum_append] at hh
    omega
  · obtain ⟨r,hr⟩ := h
    have hp' : r <+: u := by
      rw [← hr] at hp
      exact (List.prefix_append_right_inj v).mp hp
    have hh := hmin r (by rw [hL]; exact List.prefix_append_of_prefix hp')
    rw [← hr,weightSum_append]
    omega

end Crown.CrownLower

/- Source module Crown.CrownLowerAllocation -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

theorem permutation_insert_of_count (A : Set V) (z : V) (hz : z ∉ A) (l : List V)
    (hp : IsPermutationOf A (l.filter (fun a => a ≠ z))) (hc : l.count z = 1) :
    IsPermutationOf (insert z A) l := by
  have hcount : ∀ a, l.count a ≤ 1 := by
    intro a
    by_cases haz : a = z
    · simpa [haz,hc]
    · have hh := List.nodup_iff_count_le_one.mp hp.1 a
      rwa [List.count_filter (p := fun x => decide (x ≠ z)) (a := a) (by simpa using haz)] at hh
  refine ⟨List.nodup_iff_count_le_one.mpr hcount,?_⟩
  intro a
  by_cases haz : a = z
  · subst a
    simp only [Set.mem_insert_iff, true_or, iff_true]
    exact List.count_pos_iff.mp (by omega)
  · have hh := hp.2 a
    simpa [List.mem_filter,haz] using hh

def allocationWord (z : V) (D : List (List V × ℕ)) : List V :=
  D.flatMap (fun d => d.1 ++ List.replicate d.2 z)

@[simp] theorem allocationWord_nil (z : V) : allocationWord z [] = [] := rfl

@[simp] theorem allocationWord_cons (z : V) (d : List V × ℕ) (D : List (List V × ℕ)) :
    allocationWord z (d::D) = d.1 ++ List.replicate d.2 z ++ allocationWord z D := rfl

theorem allocate_missing (A : Set V) (z : V) (hz : z ∉ A)
    (D : List (List V × ℕ)) (r : ℕ)
    (hperm : ∀ d ∈ D, IsPermutationOf A (d.1.filter (fun a => a ≠ z)))
    (htotal : r + (allocationWord z D).count z = D.length)
    (hlower : ∀ P, P <+: D → P.length ≤ r + (allocationWord z P).count z)
    (hupper : ∀ P d R, D = P ++ d::R →
      r + (allocationWord z P ++ d.1).count z ≤ P.length + 1) :
    ∃ L : List (List V), List.replicate r z ++ allocationWord z D = L.flatten ∧
      L.length = D.length ∧ ∀ l ∈ L, IsPermutationOf (insert z A) l := by
  induction D generalizing r with
  | nil =>
    have hr : r = 0 := by simpa using htotal
    exact ⟨[],by simp [hr],rfl,by simp⟩
  | cons d D ih =>
    have hsmall : r + d.1.count z ≤ 1 := by simpa using hupper [] d D rfl
    have hlarge : 1 ≤ r + d.1.count z + d.2 := by
      simpa [List.count_append,Nat.add_assoc] using hlower [d] (by simp)
    let t := 1 - (r + d.1.count z)
    let r' := d.2 - t
    have htr : t + r' = d.2 := by dsimp [t,r']; omega
    have hone : r + d.1.count z + t = 1 := by dsimp [t]; omega
    have hbalance : r + d.1.count z + d.2 = 1 + r' := by omega
    let l := List.replicate r z ++ d.1 ++ List.replicate t z
    have hl : IsPermutationOf (insert z A) l := by
      apply permutation_insert_of_count A z hz l
      · simpa [l,List.filter_append] using hperm d (by simp)
      · simp only [l,List.count_append,List.count_replicate_self]
        exact hone
    have ht' : r' + (allocationWord z D).count z = D.length := by
      simp only [allocationWord_cons,List.count_append,List.count_replicate_self,List.length_cons] at htotal
      omega
    have hlo' : ∀ P, P <+: D → P.length ≤ r' + (allocationWord z P).count z := by
      intro P hP
      have hh := hlower (d::P) (List.cons_prefix_cons.mpr ⟨rfl,hP⟩)
      simp only [allocationWord_cons,List.count_append,List.count_replicate_self,List.length_cons] at hh
      omega
    have hup' : ∀ P e R, D = P ++ e::R →
        r' + (allocationWord z P ++ e.1).count z ≤ P.length + 1 := by
      intro P e R he
      have hh := hupper (d::P) e R (by simp [he])
      simp only [allocationWord_cons,List.count_append,List.count_replicate_self,List.length_cons] at hh ⊢
      omega
    obtain ⟨L,hL,hlen,hLp⟩ := ih r' (fun d hd => hperm d (by simp [hd])) ht' hlo' hup'
    refine ⟨l::L,?_,by simp [hlen],?_⟩
    · simp only [List.flatten_cons,← hL,l,allocationWord_cons]
      rw [show d.2 = t + r' from htr.symm,List.replicate_add]
      simp only [List.replicate_add,List.append_assoc]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hl
      · exact hLp q hq

end Crown.CrownLower

/- Source module Crown.CrownLowerProjection -/
namespace Crown.CrownLower

local instance CrownLowerProjectionLocal1 {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩

local instance CrownLowerProjectionLocal2 {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

def leftSide (n : ℕ) : Set (Bool × Fin n) := {v | v.1 = false}

instance {n : ℕ} : DecidablePred (· ∈ leftSide n) :=
  fun v => inferInstanceAs (Decidable (v.1 = false))

def projectBlock {n : ℕ} (z : Fin n)
    (d : List (Bool × Fin n) × List (Bool × Fin n)) : List (Bool × Fin n) × ℕ :=
  (d.1.filter (fun v => v.1 = false),d.2.count (false,z))

theorem filter_left_except {n : ℕ} (z : Fin n) (l : List (Bool × Fin n)) :
    (l.filter (fun v => v.1 = false)).filter (fun v => v ≠ (false,z)) =
      l.filter (fun v => v ∈ leftExcept z) := by
  rw [List.filter_filter]
  apply List.filter_congr
  rintro ⟨b,i⟩ hi
  cases b <;> simp [leftExcept]

theorem filter_left_gap {n : ℕ} (z : Fin n) (l : List (Bool × Fin n))
    (hl : l.filter (fun v => v ∈ leftExcept z) = []) :
    l.filter (fun v => v.1 = false) = List.replicate (l.count (false,z)) (false,z) := by
  have hmem : ∀ v ∈ l.filter (fun v => v.1 = false), v = (false,z) := by
    intro v hv
    obtain ⟨hvl,hvf⟩ := List.mem_filter.mp hv
    have hvf' : v.1 = false := by simpa using hvf
    have hvz : v.2 = z := by
      by_contra hn
      have : v ∈ l.filter (fun v => v ∈ leftExcept z) := List.mem_filter.mpr ⟨hvl,decide_eq_true (show v ∈ leftExcept z from ⟨hvf',hn⟩)⟩
      simpa [hl] using this
    exact Prod.ext hvf' hvz
  have he := List.eq_replicate_of_mem hmem
  have hc := congrArg (List.count (false,z)) he
  simp only [List.count_replicate_self] at hc
  rw [List.count_filter (p := fun v : Bool × Fin n => decide (v.1 = false)) (by simp)] at hc
  exact he.trans (congrArg (fun t => List.replicate t (false,z)) hc.symm)

theorem allocationWord_project {n : ℕ} (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hD : ∀ d ∈ D, GoodBlock (leftExcept z) d) :
    allocationWord (false,z) (D.map (projectBlock z)) =
      (blockWord D).filter (fun v => v.1 = false) := by
  induction D with
  | nil => simp [blockWord]
  | cons d D ih =>
    have hd := hD d (by simp)
    have ht := ih (fun d hd => hD d (by simp [hd]))
    simp only [List.map_cons,allocationWord_cons,projectBlock,blockWord,List.flatMap_cons,
      List.filter_append] at ht ⊢
    rw [← ht,filter_left_gap z d.2 hd.2.1]

def blockWeight {V : Type*} [DecidableEq V] (z : V) (d : List V × List V) : ℤ :=
  ((d.1 ++ d.2).count z : ℤ) - 1

theorem weightSum_blockWeight {V : Type*} [DecidableEq V] (z : V)
    (D : List (List V × List V)) :
    weightSum (blockWeight z) D = ((blockWord D).count z : ℤ) - D.length := by
  induction D with
  | nil => simp [blockWord]
  | cons d D ih =>
    simp only [weightSum_cons,blockWeight,blockWord,List.flatMap_cons,List.count_append,
      List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
    rw [ih]
    omega

theorem closed_prefix_capacity {n k : ℕ} (hn : 5 ≤ n) (z : Fin n)
    (P : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (d : List (Bool × Fin n) × List (Bool × Fin n))
    (R : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord (P++d::R)))
    (hD : ∀ e ∈ P++d::R, GoodBlock (leftExcept z) e) :
    (blockWord P ++ d.1).count (false,z) ≤ P.length + 1 := by
  cases P with
  | nil => simpa [blockWord] using core_missing_count_le_one (by omega) z d R hr hD
  | cons e T =>
    simpa only [List.length_cons,Nat.add_assoc] using
      prefix_span_missing_count_le hn z e d T R hr hD

end Crown.CrownLower

/- Source module Crown.CrownLowerFullSide -/
namespace Crown.CrownLower

local instance CrownLowerFullSideLocal1 {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩

local instance CrownLowerFullSideLocal2 {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

theorem count_project_word {n : ℕ} (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hD : ∀ d ∈ D, GoodBlock (leftExcept z) d) :
    (allocationWord (false,z) (D.map (projectBlock z))).count (false,z) =
      (blockWord D).count (false,z) := by
  rw [allocationWord_project z D hD]
  exact List.count_filter (by simp)

theorem insert_leftExcept {n : ℕ} (z : Fin n) :
    insert (false,z) (leftExcept z) = leftSide n := by
  ext v
  rcases v with ⟨b,i⟩
  cases b <;> by_cases hi : i = z <;> simp [leftExcept,leftSide,hi]

theorem full_side_permutations {n k : ℕ} (hn : 5 ≤ n) (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hlen : D.length = k) (hD : ∀ d ∈ D, GoodBlock (leftExcept z) d)
    (hnonneg : ∀ P, P <+: D → 0 ≤ weightSum (blockWeight (false,z)) P) :
    ∃ L : List (List (Bool × Fin n)),
      (blockWord D).filter (fun v => v.1 = false) = L.flatten ∧
      L.length = k ∧ ∀ l ∈ L, IsPermutationOf (leftSide n) l := by
  classical
  have hperm : ∀ d ∈ D.map (projectBlock z),
      IsPermutationOf (leftExcept z) (d.1.filter (fun v => v ≠ (false,z))) := by
    intro d hd
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
    simpa only [projectBlock,filter_left_except] using (hD e he).1
  have ht : 0 + (allocationWord (false,z) (D.map (projectBlock z))).count (false,z) =
      (D.map (projectBlock z)).length := by
    rw [Nat.zero_add,count_project_word z D hD,List.length_map,hlen,hr.2.1]
  have hlo : ∀ P, P <+: D.map (projectBlock z) →
      P.length ≤ 0 + (allocationWord (false,z) P).count (false,z) := by
    intro P hP
    obtain ⟨P',hP',rfl⟩ := List.prefix_map_iff.mp hP
    have hpGood : ∀ d ∈ P', GoodBlock (leftExcept z) d :=
      fun d hd => hD d (hP'.subset hd)
    rw [Nat.zero_add,List.length_map,count_project_word z P' hpGood]
    have hh := hnonneg P' hP'
    rw [weightSum_blockWeight] at hh
    omega
  have hup : ∀ P d R, D.map (projectBlock z) = P ++ d::R →
      0 + (allocationWord (false,z) P ++ d.1).count (false,z) ≤ P.length + 1 := by
    intro P d R heq
    obtain ⟨P',S,hDS,hP,hS⟩ := List.map_eq_append_iff.mp heq
    obtain ⟨e,R',hS',he,hR⟩ := List.map_eq_cons_iff.mp hS
    have hDe : D = P' ++ e::R' := by simpa [hS'] using hDS
    subst P
    subst d
    have hpGood : ∀ d ∈ P', GoodBlock (leftExcept z) d := by
      intro d hd
      exact hD d (by simp [hDe,hd])
    simp only [Nat.zero_add,List.count_append,List.length_map,projectBlock]
    rw [count_project_word z P' hpGood,
      List.count_filter (p := fun v : Bool × Fin n => decide (v.1 = false)) (by simp)]
    have hh := closed_prefix_capacity hn z P' e R' (hDe ▸ hr)
      (fun e he => hD e (by simpa only [hDe] using he))
    simpa only [List.count_append] using hh
  obtain ⟨L,hL,hLL,hLP⟩ := allocate_missing (leftExcept z) (false,z)
    (by simp [leftExcept]) (D.map (projectBlock z)) 0 hperm ht hlo hup
  refine ⟨L,?_,by simpa [hlen] using hLL,?_⟩
  · simpa [allocationWord_project z D hD] using hL
  · simpa only [insert_leftExcept z] using hLP

theorem exists_full_side_split {n k : ℕ} (hn : 5 ≤ n) (w : List (Bool × Fin n))
    (hw : Crown.Represents (Crown.crownGraph n) k w) :
    ∃ w', Crown.Represents (Crown.crownGraph n) k w' ∧ Splittable w' k (leftSide n) := by
  classical
  let z : Fin n := ⟨0,by omega⟩
  have hN : {v | (Crown.crownGraph n).Adj (true,z) v} = leftExcept z := by
    apply Set.ext
    rintro ⟨b,i⟩
    change (true ≠ b ∧ z ≠ i) ↔ (b = false ∧ i ≠ z)
    cases b
    · exact ⟨fun h => ⟨rfl,Ne.symm h.2⟩,fun h => ⟨by decide,Ne.symm h.2⟩⟩
    · simp
  have hsplit : Splittable w k (leftExcept z) :=
    hN ▸ neighbourhood_splittable hw (true,z)
  obtain ⟨i,hiz,_,_⟩ := Ranks.coordinate_avoiding_three (by omega) z z z
  have hA : (leftExcept z).Nonempty := ⟨(false,i),rfl,hiz⟩
  obtain ⟨D,hDrep,hDlen,hDgood⟩ := canonical_representation hw (leftExcept z) hA hsplit
  have hzero : weightSum (blockWeight (false,z)) D = 0 := by
    rw [weightSum_blockWeight,hDrep.2.1,hDlen]
    omega
  obtain ⟨P,Q,hDQ,hmin⟩ := exists_nonnegative_rotation (blockWeight (false,z)) D hzero
  have hrot := rotate_block_representation P Q (hDQ ▸ hDrep)
  have hlen : (Q++P).length = k := by simpa [hDQ,List.length_append,Nat.add_comm] using hDlen
  have hgood : ∀ d ∈ Q++P, GoodBlock (leftExcept z) d := by
    intro d hd
    exact hDgood d (by simpa [hDQ,List.mem_append,or_comm] using hd)
  obtain ⟨L,hL,hLL,hLP⟩ := full_side_permutations hn z (Q++P) hrot hlen hgood hmin
  refine ⟨blockWord (Q++P),hrot,[],blockWord (Q++P),L,by simp,?_,hLL,hLP⟩
  simp only [List.append_nil]
  calc
    _ = (blockWord (Q++P)).filter (fun v => v.1 = false) := by
      apply List.filter_congr
      intro v hv
      by_cases hf : v.1 = false <;> simp [leftSide,hf]
    _ = L.flatten := hL

end Crown.CrownLower

/- Source module Crown.CrownLowerEndpoints -/
namespace Crown.CrownLower

variable {V : Type*} [DecidableEq V]

def endpointLetters (D : List (List V × List V)) : List V :=
  D.flatMap (fun d => d.1.take 1 ++ d.1.reverse.take 1)

theorem endpointLetters_length (D : List (List V × List V)) :
    (endpointLetters D).length ≤ 2 * D.length := by
  induction D with
  | nil => simp [endpointLetters]
  | cons d D ih =>
    have h1 : (d.1.take 1).length ≤ 1 := by simp only [List.length_take]; omega
    have h2 : (d.1.reverse.take 1).length ≤ 1 := by simp only [List.length_take]; omega
    simp only [endpointLetters,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
    omega

theorem endpointLetters_mem (D : List (List V × List V))
    (d : List V × List V) (hd : d ∈ D) (a : V)
    (ha : StartsIn (fun x => decide (x = a)) d.1 ∨ EndsIn (fun x => decide (x = a)) d.1) :
    a ∈ endpointLetters D := by
  apply List.mem_flatMap.mpr
  refine ⟨d,hd,?_⟩
  rcases ha with ⟨b,t,hb,he⟩ | ⟨t,b,hb,he⟩
  · have hba : b = a := by simpa using he
    subst b
    simp [hb]
  · have hba : b = a := by simpa using he
    subst b
    simp [hb]

theorem alternating_constant_pairs (a b : V) (hab : a ≠ b) (L : List α) :
    (L.flatMap (fun _ => [a,b])).IsChain (· ≠ ·) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases L with
    | nil => simp [List.isChain_cons_cons,hab]
    | cons y L =>
      change (a::b::a::b::L.flatMap (fun _ => [a,b])).IsChain (· ≠ ·)
      exact List.isChain_cons_cons.mpr ⟨hab,List.isChain_cons_cons.mpr ⟨Ne.symm hab,ih⟩⟩

local instance CrownLowerEndpointsLocal6 {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩

local instance CrownLowerEndpointsLocal7 {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

theorem leftSide_has_other {n : ℕ} (hn : 4 ≤ n) :
    ∀ a ∈ leftSide n, ∃ c ∈ leftSide n, c ≠ a := by
  intro a ha
  obtain ⟨i,hia,_,_⟩ := Ranks.coordinate_avoiding_three hn a.2 a.2 a.2
  exact ⟨(false,i),rfl,fun he => hia (congrArg Prod.snd he)⟩

theorem prime_absent_core_of_no_endpoint {n k : ℕ} (hn : 4 ≤ n) (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hD : ∀ d ∈ D, GoodBlock (leftSide n) d)
    (hno : ∀ d ∈ D, ¬ StartsIn (fun v => decide (v = (false,z))) d.1 ∧
      ¬ EndsIn (fun v => decide (v = (false,z))) d.1) :
    ∀ d ∈ D, (true,z) ∉ d.1 := by
  intro d hd
  obtain ⟨P,Q,hPQ⟩ := List.mem_iff_append.mp hd
  have hrot : Crown.Represents (Crown.crownGraph n) k (blockWord (d::(Q++P))) := by
    simpa only [List.cons_append] using rotate_block_representation P (d::Q) (hPQ ▸ hr)
  have hgood : ∀ e ∈ d::(Q++P), GoodBlock (leftSide n) e := by
    intro e he
    exact hD e (by simpa [hPQ,List.mem_append,or_assoc,or_comm,or_left_comm] using he)
  obtain ⟨a,b,ha,hb,hab,has,hbe⟩ := goodBlock_endpoints (leftSide n) d (hD d hd)
    (leftSide_has_other hn)
  have haf : a.1 = false := ha
  have hbf : b.1 = false := hb
  have haz : a.2 ≠ z := by
    intro he
    have hea : a = (false,z) := Prod.ext haf he
    exact (hno d hd).1 (hea ▸ has)
  have hbz : b.2 ≠ z := by
    intro he
    have heb : b = (false,z) := Prod.ext hbf he
    exact (hno d hd).2 (heb ▸ hbe)
  have hnab : ¬ (Crown.crownGraph n).Adj a b := by
    change ¬ (a.1 ≠ b.1 ∧ a.2 ≠ b.2)
    simp [haf,hbf]
  have hax : (Crown.crownGraph n).Adj a (true,z) := ⟨by simp [haf],haz⟩
  have hxb : (Crown.crownGraph n).Adj (true,z) b := ⟨by simp [hbf],Ne.symm hbz⟩
  exact no_common_neighbour_in_first_core (leftSide n) d (Q++P) hrot hgood a b (true,z)
    ha hb hab hnab has hbe hax hxb

theorem gap_prime_count_le_one {n k : ℕ} (hn : 4 ≤ n) (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hD : ∀ d ∈ D, GoodBlock (leftSide n) d) :
    ∀ d ∈ D, d.2.count (true,z) ≤ 1 := by
  intro d hd
  obtain ⟨i,hiz,_,_⟩ := Ranks.coordinate_avoiding_three hn z z z
  have hi : (false,i) ∈ leftSide n := rfl
  have hc := goodBlock_gap_count (leftSide n) d (hD d hd) (false,i) hi
  obtain ⟨P,Q,hPQ⟩ := List.mem_iff_append.mp hd
  have hin : d.2 <:+: blockWord D :=
    ⟨blockWord P ++ d.1,blockWord Q,by simp [hPQ,blockWord,List.flatMap_append,List.append_assoc]⟩
  have hed : (Crown.crownGraph n).Adj (true,z) (false,i) := ⟨by simp,Ne.symm hiz⟩
  have halt := (hr.2.2 (true,z) (false,i) (by simp)).mp hed
  simpa [hc] using alternating_factor_count_le (true,z) (false,i) (by simp) _ d.2 halt hin

theorem endpoint_coverage {n k : ℕ} (hn : 4 ≤ n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord D))
    (hlen : D.length = k) (hD : ∀ d ∈ D, GoodBlock (leftSide n) d) (z : Fin n) :
    ∃ d ∈ D, StartsIn (fun v => decide (v = (false,z))) d.1 ∨
      EndsIn (fun v => decide (v = (false,z))) d.1 := by
  classical
  by_contra h
  have hno : ∀ d ∈ D, ¬ StartsIn (fun v => decide (v = (false,z))) d.1 ∧
      ¬ EndsIn (fun v => decide (v = (false,z))) d.1 := by
    intro d hd
    exact ⟨fun hs => h ⟨d,hd,Or.inl hs⟩,fun he => h ⟨d,hd,Or.inr he⟩⟩
  have hcore := prime_absent_core_of_no_endpoint hn z D hr hD hno
  have hgap := gap_prime_count_le_one hn z D hr hD
  have hsum : (D.map (fun d => d.2.count (true,z))).sum = D.length := by
    have he := hr.2.1 (true,z)
    rw [blockWord,List.count_flatMap] at he
    have hm : D.map (fun d => (d.1 ++ d.2).count (true,z)) =
        D.map (fun d => d.2.count (true,z)) := by
      apply List.map_congr_left
      intro d hd
      simp [List.count_append,List.count_eq_zero.mpr (hcore d hd)]
    simpa only [Function.comp_def,hm,hlen] using he
  have hall := all_one_of_sum_eq_length (D.map (fun d => d.2.count (true,z)))
    (by intro m hm; obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm; exact hgap d hd)
    (by simpa only [List.length_map] using hsum)
  have hcell : ∀ d ∈ D, Crown.restrictPair (d.1 ++ d.2) (false,z) (true,z) = [(false,z),(true,z)] := by
    intro d hd
    have hfirst : Crown.restrictPair d.1 (false,z) (true,z) = [(false,z)] := by
      rw [Crown.restrictPair_comm,Blocks.restrictPair_of_not_mem_left _ (true,z) (false,z) (hcore d hd),
        List.filter_eq,goodBlock_core_count (leftSide n) d (hD d hd) (false,z) rfl]
      simp
    have hsecond : Crown.restrictPair d.2 (false,z) (true,z) = [(true,z)] := by
      have hnot : (false,z) ∉ d.2 := List.count_eq_zero.mp
        (goodBlock_gap_count (leftSide n) d (hD d hd) (false,z) rfl)
      rw [Blocks.restrictPair_of_not_mem_left _ (false,z) (true,z) hnot,List.filter_eq,
        hall _ (List.mem_map.mpr ⟨d,hd,rfl⟩)]
      simp
    rw [Crown.restrictPair_append,hfirst,hsecond]
    rfl
  have hrestriction : Crown.restrictPair (blockWord D) (false,z) (true,z) =
      D.flatMap (fun _ => [(false,z),(true,z)]) := by
    unfold Crown.restrictPair blockWord
    rw [List.filter_flatMap,List.flatMap_def,List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro d hd
    exact hcell d hd
  have halt : Crown.Alternates (blockWord D) (false,z) (true,z) := by
    unfold Crown.Alternates
    rw [hrestriction]
    exact alternating_constant_pairs (false,z) (true,z) (by simp) D
  have hed := (hr.2.2 (false,z) (true,z) (by simp)).mpr halt
  exact hed.2 rfl

end Crown.CrownLower

/- Source module Crown.CrownLower -/
namespace Crown.CrownLower

local instance CrownLowerLocal1 {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩

local instance CrownLowerLocal2 {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

theorem crown_size_le_twice_multiplicity {n k : ℕ} (hn : 5 ≤ n)
    (w : List (Bool × Fin n)) (hw : Crown.Represents (Crown.crownGraph n) k w) : n ≤ 2*k := by
  classical
  obtain ⟨w',hw',hsplit⟩ := exists_full_side_split hn w hw
  have hA : (leftSide n).Nonempty := ⟨(false,⟨0,by omega⟩),rfl⟩
  obtain ⟨D,hDrep,hDlen,hDgood⟩ := canonical_representation hw' (leftSide n) hA hsplit
  let E : List (Fin n) := (endpointLetters D).map Prod.snd
  have hcover : ∀ i : Fin n, i ∈ E := by
    intro i
    obtain ⟨d,hd,hi⟩ := endpoint_coverage (by omega) D hDrep hDlen hDgood i
    exact List.mem_map.mpr ⟨(false,i),endpointLetters_mem D d hd (false,i) hi,rfl⟩
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ E.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hcover i)
  calc
    n = (Finset.univ : Finset (Fin n)).card := by simp
    _ ≤ E.toFinset.card := Finset.card_le_card hsub
    _ ≤ E.length := List.toFinset_card_le E
    _ = (endpointLetters D).length := List.length_map Prod.snd
    _ ≤ 2 * D.length := endpointLetters_length D
    _ = 2*k := by rw [hDlen]

theorem halfCeil_le_of_kRepresentable {n k : ℕ} (hn : 5 ≤ n)
    (h : Crown.KRepresentable (Crown.crownGraph n) k) : Crown.halfCeil n ≤ k := by
  obtain ⟨w,hw⟩ := h
  have hh := crown_size_le_twice_multiplicity hn w hw
  unfold Crown.halfCeil
  omega

end Crown.CrownLower

/- Source module Crown.CrownFourFiniteCore -/
namespace Crown.CrownFourFinite

local instance CrownFourFiniteCoreLocal1 : BEq (Fin 4) := ⟨fun a b => decide (a = b)⟩

local instance CrownFourFiniteCoreLocal2 : LawfulBEq (Fin 4) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

instance (w : List (Fin 4)) (a b : Fin 4) : Decidable (Crown.Alternates w a b) :=
  inferInstanceAs (Decidable ((Crown.restrictPair w a b).IsChain (· ≠ ·)))

def IntervalPattern (w : List (Fin 4)) (z : Fin 4) (lo len : Fin 9) : Prop :=
  ∀ i : Fin 4, ((w.drop lo.val).take len.val).count i = 1 ↔ i ≠ z

instance (w : List (Fin 4)) (z : Fin 4) (lo len : Fin 9) :
    Decidable (IntervalPattern w z lo len) := by
  unfold IntervalPattern
  infer_instance

def Obstructed (w : List (Fin 4)) : Prop :=
  (∀ i : Fin 4, w.count i = 2) →
  (∀ a b : Fin 4, a ≠ b → ¬ Crown.Alternates w a b) →
  ∃ z : Fin 4, ∀ lo len : Fin 9, ¬ IntervalPattern w z lo len

instance (w : List (Fin 4)) : Decidable (Obstructed w) := by
  unfold Obstructed
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_012 : ∀ d e f g h : Fin 4, Obstructed [0,1,2,d,e,f,g,h] := by
  decide +kernel

end Crown.CrownFourFinite

/- Source module Crown.CrownFourFiniteData -/
namespace Crown.CrownFourFinite

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_000 : ∀ d e f g h : Fin 4, Obstructed [0,0,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_001 : ∀ d e f g h : Fin 4, Obstructed [0,0,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_002 : ∀ d e f g h : Fin 4, Obstructed [0,0,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_003 : ∀ d e f g h : Fin 4, Obstructed [0,0,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_010 : ∀ d e f g h : Fin 4, Obstructed [0,1,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_011 : ∀ d e f g h : Fin 4, Obstructed [0,1,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_013 : ∀ d e f g h : Fin 4, Obstructed [0,1,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_020 : ∀ d e f g h : Fin 4, Obstructed [0,2,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_021 : ∀ d e f g h : Fin 4, Obstructed [0,2,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_022 : ∀ d e f g h : Fin 4, Obstructed [0,2,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_023 : ∀ d e f g h : Fin 4, Obstructed [0,2,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_030 : ∀ d e f g h : Fin 4, Obstructed [0,3,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_031 : ∀ d e f g h : Fin 4, Obstructed [0,3,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_032 : ∀ d e f g h : Fin 4, Obstructed [0,3,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_033 : ∀ d e f g h : Fin 4, Obstructed [0,3,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_100 : ∀ d e f g h : Fin 4, Obstructed [1,0,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_101 : ∀ d e f g h : Fin 4, Obstructed [1,0,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_102 : ∀ d e f g h : Fin 4, Obstructed [1,0,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_103 : ∀ d e f g h : Fin 4, Obstructed [1,0,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_110 : ∀ d e f g h : Fin 4, Obstructed [1,1,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_111 : ∀ d e f g h : Fin 4, Obstructed [1,1,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_112 : ∀ d e f g h : Fin 4, Obstructed [1,1,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_113 : ∀ d e f g h : Fin 4, Obstructed [1,1,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_120 : ∀ d e f g h : Fin 4, Obstructed [1,2,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_121 : ∀ d e f g h : Fin 4, Obstructed [1,2,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_122 : ∀ d e f g h : Fin 4, Obstructed [1,2,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_123 : ∀ d e f g h : Fin 4, Obstructed [1,2,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_130 : ∀ d e f g h : Fin 4, Obstructed [1,3,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_131 : ∀ d e f g h : Fin 4, Obstructed [1,3,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_132 : ∀ d e f g h : Fin 4, Obstructed [1,3,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_133 : ∀ d e f g h : Fin 4, Obstructed [1,3,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_200 : ∀ d e f g h : Fin 4, Obstructed [2,0,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_201 : ∀ d e f g h : Fin 4, Obstructed [2,0,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_202 : ∀ d e f g h : Fin 4, Obstructed [2,0,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_203 : ∀ d e f g h : Fin 4, Obstructed [2,0,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_210 : ∀ d e f g h : Fin 4, Obstructed [2,1,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_211 : ∀ d e f g h : Fin 4, Obstructed [2,1,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_212 : ∀ d e f g h : Fin 4, Obstructed [2,1,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_213 : ∀ d e f g h : Fin 4, Obstructed [2,1,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_220 : ∀ d e f g h : Fin 4, Obstructed [2,2,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_221 : ∀ d e f g h : Fin 4, Obstructed [2,2,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_222 : ∀ d e f g h : Fin 4, Obstructed [2,2,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_223 : ∀ d e f g h : Fin 4, Obstructed [2,2,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_230 : ∀ d e f g h : Fin 4, Obstructed [2,3,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_231 : ∀ d e f g h : Fin 4, Obstructed [2,3,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_232 : ∀ d e f g h : Fin 4, Obstructed [2,3,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_233 : ∀ d e f g h : Fin 4, Obstructed [2,3,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_300 : ∀ d e f g h : Fin 4, Obstructed [3,0,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_301 : ∀ d e f g h : Fin 4, Obstructed [3,0,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_302 : ∀ d e f g h : Fin 4, Obstructed [3,0,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_303 : ∀ d e f g h : Fin 4, Obstructed [3,0,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_310 : ∀ d e f g h : Fin 4, Obstructed [3,1,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_311 : ∀ d e f g h : Fin 4, Obstructed [3,1,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_312 : ∀ d e f g h : Fin 4, Obstructed [3,1,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_313 : ∀ d e f g h : Fin 4, Obstructed [3,1,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_320 : ∀ d e f g h : Fin 4, Obstructed [3,2,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_321 : ∀ d e f g h : Fin 4, Obstructed [3,2,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_322 : ∀ d e f g h : Fin 4, Obstructed [3,2,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_323 : ∀ d e f g h : Fin 4, Obstructed [3,2,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_330 : ∀ d e f g h : Fin 4, Obstructed [3,3,0,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_331 : ∀ d e f g h : Fin 4, Obstructed [3,3,1,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_332 : ∀ d e f g h : Fin 4, Obstructed [3,3,2,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem check_333 : ∀ d e f g h : Fin 4, Obstructed [3,3,3,d,e,f,g,h] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem all_words : ∀ a b c d e f g h : Fin 4, Obstructed [a,b,c,d,e,f,g,h] := by
  intro a b c
  fin_cases a
  · fin_cases b
    · fin_cases c
      · exact check_000
      · exact check_001
      · exact check_002
      · exact check_003
    · fin_cases c
      · exact check_010
      · exact check_011
      · exact check_012
      · exact check_013
    · fin_cases c
      · exact check_020
      · exact check_021
      · exact check_022
      · exact check_023
    · fin_cases c
      · exact check_030
      · exact check_031
      · exact check_032
      · exact check_033
  · fin_cases b
    · fin_cases c
      · exact check_100
      · exact check_101
      · exact check_102
      · exact check_103
    · fin_cases c
      · exact check_110
      · exact check_111
      · exact check_112
      · exact check_113
    · fin_cases c
      · exact check_120
      · exact check_121
      · exact check_122
      · exact check_123
    · fin_cases c
      · exact check_130
      · exact check_131
      · exact check_132
      · exact check_133
  · fin_cases b
    · fin_cases c
      · exact check_200
      · exact check_201
      · exact check_202
      · exact check_203
    · fin_cases c
      · exact check_210
      · exact check_211
      · exact check_212
      · exact check_213
    · fin_cases c
      · exact check_220
      · exact check_221
      · exact check_222
      · exact check_223
    · fin_cases c
      · exact check_230
      · exact check_231
      · exact check_232
      · exact check_233
  · fin_cases b
    · fin_cases c
      · exact check_300
      · exact check_301
      · exact check_302
      · exact check_303
    · fin_cases c
      · exact check_310
      · exact check_311
      · exact check_312
      · exact check_313
    · fin_cases c
      · exact check_320
      · exact check_321
      · exact check_322
      · exact check_323
    · fin_cases c
      · exact check_330
      · exact check_331
      · exact check_332
      · exact check_333

end Crown.CrownFourFinite

/- Source module Crown.CrownFourFinite -/
namespace Crown.CrownFourFinite

theorem obstruction_length_eight (w : List (Fin 4)) (hlen : w.length = 8) : Obstructed w := by
  let f : Fin 8 → Fin 4 := fun i => w[i.val]'(by simpa [hlen] using i.isLt)
  have hf : List.ofFn f = w := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  rw [← hf]
  change Obstructed [f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7]
  exact all_words _ _ _ _ _ _ _ _

end Crown.CrownFourFinite

/- Source module Crown.CrownFourIntervals -/
namespace Crown.CrownFourIntervals

variable {V : Type*} [DecidableEq V]

theorem two_occurrence_interval {G : SimpleGraph V} (w : List V)
    (hr : Crown.Represents G 2 w) (v : V) :
    ∃ s : List V, s <:+: w ∧ ∀ a, a ≠ v → (G.Adj v a ↔ s.count a = 1) := by
  obtain ⟨p,L,hw,hp,hL⟩ := Crown.CrownLower.exists_segments v w
  have hlen : L.length = 2 := by
    have hc := hr.2.1 v
    rw [hw,List.count_append,Crown.CrownLower.count_separator v L hL,
      List.count_eq_zero.mpr hp,Nat.zero_add] at hc
    exact hc
  obtain ⟨s,t,hLt⟩ := List.length_eq_two.mp hlen
  subst L
  have hs : v ∉ s := hL s (by simp)
  have ht : v ∉ t ++ p := by
    have ht := hL t (by simp)
    simpa using And.intro ht hp
  let W := (v::s) ++ v::(t++p)
  have hrot : Crown.Represents G 2 W := by
    have hh := Crown.represents_append_swap (hw ▸ hr)
    simpa [W,List.append_assoc] using hh
  refine ⟨s,⟨p++[v],v::t,by simp [hw,List.append_assoc]⟩,?_⟩
  intro a hav
  have hva := Ne.symm hav
  constructor
  · intro ha
    have hc : Crown.Alternates ([s,t++p].flatMap (fun l => v::l)) v a := by
      simpa [W] using (hrot.2.2 v a hva).mp ha
    have hn : ∀ l ∈ [s,t++p], v ∉ l := by simpa using And.intro hs ht
    have hcounts : ([s,t++p].flatMap (fun l => v::l)).count a = [s,t++p].length := by
      simpa [W] using hrot.2.1 a
    exact Crown.CrownLower.segment_neighbour_count v a hva [s,t++p] hn hc hcounts s (by simp)
  · intro hsa
    have hta : (t++p).count a = 1 := by
      have hc := hrot.2.1 a
      simp [W,List.count_append,List.count_cons,hva,hsa] at hc
      rw [List.count_append]
      omega
    have hrs : Crown.restrictPair s v a = [a] := by
      rw [Crown.Blocks.restrictPair_of_not_mem_left s v a hs,List.filter_eq,hsa]
      rfl
    have hrt : Crown.restrictPair (t++p) v a = [a] := by
      rw [Crown.Blocks.restrictPair_of_not_mem_left (t++p) v a ht,List.filter_eq,hta]
      rfl
    have he : Crown.restrictPair W v a = [v,a,v,a] := by
      simp only [W,Crown.restrictPair_append,Crown.Blocks.restrictPair_cons,
        eq_self_iff_true,true_or,if_true,hrs,hrt,List.cons_append,List.nil_append]
    apply (hrot.2.2 v a hva).mpr
    unfold Crown.Alternates
    rw [he]
    simp [List.isChain_cons_cons,hva,hav]

end Crown.CrownFourIntervals

/- Source module Crown.CrownFour -/
namespace Crown.CrownFour

local instance CrownFourLocal1 : BEq (Fin 4) := ⟨fun a b => decide (a = b)⟩

local instance CrownFourLocal2 : LawfulBEq (Fin 4) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

local instance CrownFourLocal3 : BEq (Bool × Fin 4) := ⟨fun a b => decide (a = b)⟩

local instance CrownFourLocal4 : LawfulBEq (Bool × Fin 4) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

def leftWord (w : List (Bool × Fin 4)) : List (Fin 4) :=
  w.filterMap fun v => if v.1 then none else some v.2

theorem map_leftWord (w : List (Bool × Fin 4)) :
    (leftWord w).map (fun i => (false,i)) = w.filter (fun v => !v.1) := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    rcases v with ⟨b,i⟩
    cases b <;> simp [leftWord] at ih ⊢ <;> exact ih

theorem count_leftWord (w : List (Bool × Fin 4)) (i : Fin 4) :
    (leftWord w).count i = w.count (false,i) := by
  have hinj : Function.Injective (fun i : Fin 4 => (false,i)) := by
    intro a b h
    exact congrArg Prod.snd h
  rw [← List.count_map_of_injective (leftWord w) _ hinj, map_leftWord]
  exact List.count_filter (by simp)

theorem alternates_leftWord (w : List (Bool × Fin 4)) (a b : Fin 4) :
    Crown.Alternates (leftWord w) a b ↔ Crown.Alternates w (false,a) (false,b) := by
  have hinj : Function.Injective (fun i : Fin 4 => (false,i)) := by
    intro a b h
    exact congrArg Prod.snd h
  rw [← Crown.alternates_map _ hinj, map_leftWord]
  unfold Crown.Alternates
  have he : w.filter (fun v => !v.1) = w.filter (fun v => decide (v.1 = false)) := by
    apply List.filter_congr
    intro v _
    cases v.1 <;> rfl
  rw [he,Crown.restrictPair_filter (fun v : Bool × Fin 4 => v.1 = false) w
    (false,a) (false,b) rfl rfl]

theorem interval_parameters {w s : List (Fin 4)} (hlen : w.length = 8)
    (hs : s <:+: w) :
    ∃ lo len : Fin 9, (w.drop lo.val).take len.val = s := by
  obtain ⟨p,q,he⟩ := hs
  have hp : p.length < 9 := by
    have hh := congrArg List.length he
    simp only [List.length_append] at hh
    omega
  have hl : s.length < 9 := by
    have hh := congrArg List.length he
    simp only [List.length_append] at hh
    omega
  refine ⟨⟨p.length,hp⟩,⟨s.length,hl⟩,?_⟩
  rw [← he]
  simp [List.append_assoc]

theorem not_two_representable : ¬Crown.KRepresentable (Crown.crownGraph 4) 2 := by
  rintro ⟨w,hw⟩
  have hu : Crown.Uniform 2 (leftWord w) := by
    intro i
    exact (count_leftWord w i).trans (hw.2.1 (false,i))
  have hl : (leftWord w).length = 8 := by
    simpa using Crown.uniform_length hu
  have hn : ∀ a b : Fin 4, a ≠ b → ¬Crown.Alternates (leftWord w) a b := by
    intro a b hab ha
    have hh := (hw.2.2 (false,a) (false,b) (by simpa using hab)).mpr
      ((alternates_leftWord w a b).mp ha)
    simpa [Crown.crownGraph] using hh
  obtain ⟨z,hz⟩ := Crown.CrownFourFinite.obstruction_length_eight (leftWord w) hl hu hn
  obtain ⟨s,hs,hi⟩ := Crown.CrownFourIntervals.two_occurrence_interval w hw (true,z)
  have hsub : leftWord s <:+: leftWord w := hs.filterMap _
  obtain ⟨lo,len,he⟩ := interval_parameters hl hsub
  apply hz lo len
  intro i
  rw [he,count_leftWord]
  have hh := hi (false,i) (by simp)
  simpa [Crown.crownGraph,ne_comm] using hh.symm

end Crown.CrownFour

namespace CrownTransfer
open OMA.S_wp_bipartite_graph

def sides (n : ℕ) : (Fin n ⊕ Fin n) ≃ Bool × Fin n where
  toFun := Sum.elim (fun i => (false,i)) (fun i => (true,i))
  invFun := fun p => if p.1 then .inr p.2 else .inl p.2
  left_inv x := by cases x <;> rfl
  right_inv := by rintro ⟨b,i⟩; cases b <;> rfl

theorem sides_adj (n : ℕ) (u v : Fin n ⊕ Fin n) :
    (Crown.crownGraph n).Adj (sides n u) (sides n v) ↔ (crownGraph n).Adj u v := by
  cases u <;> cases v <;> simp [sides,Crown.crownGraph,crownGraph,SimpleGraph.fromRel_adj,ne_comm]

theorem word_iff {V : Type} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) (w : List V) :
    Crown.Represents G k w ↔ 0 < k ∧ IsRepresentedBy G k w := by rfl

theorem transport {n k : ℕ} {w : List (Fin n ⊕ Fin n)} (hk : 0 < k)
    (hw : IsRepresentedBy (crownGraph n) k w) : Crown.KRepresentable (Crown.crownGraph n) k :=
  ⟨_, Crown.represents_equiv (sides n) (sides_adj n) ((word_iff _ _ _).mpr ⟨hk,hw⟩)⟩

theorem positive_word_two {n k : ℕ} (hn : 1 ≤ n) (hw : Crown.KRepresentable (Crown.crownGraph n) k) :
    2 ≤ k := by
  have hp := hw.choose_spec.1
  by_contra! h
  obtain rfl : k = 1 := by omega
  let i : Fin n := ⟨0, hn⟩
  exact ((Crown.one_uniform_complete hw (false,i) (true,i) (by simp)).2) rfl

end CrownTransfer

theorem OMA.solution : OMA.R_wp_bipartite_graph_R1.H4 := by
  intro n hn k hk w hw
  have h := CrownTransfer.transport hk hw
  by_cases he : n = 4
  · subst n
    simp only [if_true]
    have htwo := CrownTransfer.positive_word_two (by decide : 1 ≤ 4) h
    by_contra! hlt
    obtain rfl : k = 2 := by omega
    exact Crown.CrownFour.not_two_representable h
  · rw [if_neg he]
    exact Crown.CrownLower.halfCeil_le_of_kRepresentable (by omega) h
