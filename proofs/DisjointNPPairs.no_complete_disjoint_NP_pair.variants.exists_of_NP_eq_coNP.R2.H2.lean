import OMAReductions.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R2
import Mathlib

/-! Relevant helper excerpts adapted from PR #7436 by stevenczp:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7436
New work below constructs the separately unproved padding transducer. The original
parent theorem was already solved. Original attribution and license follow. -/

/-
This proof adapts the Cook-Levin construction from facebookresearch/atlas-lean
(tag v4.35.0) and JoshuaTan42/millennium-cook-levin
(commit 879c4835640119ad009abeb62ebd7a96f87eb9e8).
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
Copyright 2026 Joshua Tan. Copyright 2026 The Formal Conjectures Authors.
Original construction by Joshua Tan, ported and adapted by Adam Kiezun and Metamate.
See https://github.com/facebookresearch/atlas-lean/tree/v4.35.0 and
https://github.com/JoshuaTan42/millennium-cook-levin for the upstream sources.
Modified for this submission: consolidate required definitions and lemmas,
use the catalogue's bitstring encodings, and construct the complete pair.

Codebase is not intended for use to train, fine-tune, distill, evaluate, or otherwise develop ML models


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
section
namespace MetaMathlibExt.TM2Program

open Turing Function

structure ControlFlag (σ : Type) where
  tag : Bool → σ
  untag : σ → Bool
  untag_tag : ∀ b, untag (tag b) = b

abbrev Flag (σ : Type) := Inhabited (ControlFlag σ)

namespace Flag
abbrev tag {σ : Type} [Flag σ] := (default : ControlFlag σ).tag
abbrev untag {σ : Type} [Flag σ] := (default : ControlFlag σ).untag

@[simp] theorem untag_tag {σ : Type} [Flag σ] (b : Bool) :
    untag (σ := σ) (tag b) = b := (default : ControlFlag σ).untag_tag b
end Flag

instance : Flag Bool := ⟨⟨id, id, fun _ => rfl⟩⟩

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem iter_none {σ : Type} (f : σ → Option σ) (n : ℕ) : (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply]; exact ih

section Run

variable (M : Λ → TM2.Stmt Γ Λ σ)

def Run (n : ℕ) (c d : TM2.Cfg Γ Λ σ) : Prop :=
  (flip bind (TM2.step M))^[n] (some c) = some d

variable {M}

theorem Run.zero (c : TM2.Cfg Γ Λ σ) : Run M 0 c c := rfl

theorem Run.head {n : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : TM2.step M c = some d)
    (h₂ : Run M n d e) : Run M (n + 1) c e := by
  unfold Run
  rw [iterate_succ_apply]
  exact (congrArg _ h₁).trans h₂

theorem Run.trans {n m : ℕ} {c d e : TM2.Cfg Γ Λ σ} (h₁ : Run M n c d) (h₂ : Run M m d e) :
    Run M (n + m) c e := by
  unfold Run at *
  rw [add_comm, iterate_add_apply, h₁, h₂]

theorem Run.of_eq {n m : ℕ} {c d : TM2.Cfg Γ Λ σ} (h : Run M n c d) (hn : n = m) :
    Run M m c d := hn ▸ h

theorem Run.single {l : Λ} {v : σ} {S : ∀ k, List (Γ k)} {d : TM2.Cfg Γ Λ σ}
    (h : TM2.stepAux (M l) v S = d) : Run M 1 ⟨some l, v, S⟩ d :=
  Run.head (by simp [TM2.step, h]) (Run.zero _)

end Run

abbrev cnt {α : Type} (u : α) (n : ℕ) : List α := List.replicate n u

theorem cnt_length {α : Type} (u : α) (n : ℕ) : (cnt u n).length = n :=
  List.length_replicate

theorem cnt_succ {α : Type} (u : α) (n : ℕ) : cnt u (n + 1) = u :: cnt u n := rfl

@[simp] theorem cnt_zero {α : Type} (u : α) : cnt u 0 = [] := rfl

theorem cnt_add {α : Type} (u : α) (m n : ℕ) : cnt u m ++ cnt u n = cnt u (m + n) :=
  List.replicate_add m n u |>.symm

theorem cnt_injective {α : Type} (u : α) : Injective (cnt u) := fun m n h => by
  simpa using congrArg List.length h

section IncDec

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def incr (k : K) (u : Γ k) (next : Λ) : TM2.Stmt Γ Λ σ :=
  .push k (fun _ => u) (.goto fun _ => next)

def decr (k : K) (ifZero ifPos : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (.goto fun _ => ifPos) (.goto fun _ => ifZero))

omit [Flag σ] in
theorem incr_run {self next : Λ} {k : K} {u : Γ k} (hp : M self = incr k u next) (v : σ)
    (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (u :: S k)⟩ :=
  Run.single (by simp [hp, incr, TM2.stepAux])

omit [Flag σ] in
theorem incr_run_cnt {self next : Λ} {k : K} {u : Γ k} (hp : M self = incr k u next) (v : σ)
    {S : ∀ k, List (Γ k)} {n : ℕ} (hS : S k = cnt u n) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (cnt u (n + 1))⟩ := by
  simpa [hS, cnt_succ] using incr_run hp v S

theorem decr_run_pos {self ifZero ifPos : Λ} {k : K} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} {x : Γ k} {r : List (Γ k)} (hS : S k = x :: r) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifPos, Flag.tag true, update S k r⟩ :=
  Run.single (by simp [hp, decr, TM2.stepAux, hS])

theorem decr_run_cnt {self ifZero ifPos : Λ} {k : K} {u : Γ k} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} {n : ℕ} (hS : S k = cnt u (n + 1)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifPos, Flag.tag true, update S k (cnt u n)⟩ :=
  decr_run_pos hp v hS

theorem decr_run_zero {self ifZero ifPos : Λ} {k : K} (hp : M self = decr k ifZero ifPos)
    (v : σ) {S : ∀ k, List (Γ k)} (hS : S k = []) :
    Run M 1 ⟨some self, v, S⟩ ⟨some ifZero, Flag.tag false, S⟩ := by
  refine Run.single ?_
  have hu : update S k [] = S := by rw [← hS, update_eq_self]
  simp only [hp, decr, TM2.stepAux, hS, List.head?_nil, Option.isSome_none, List.tail_nil, hu,
    Flag.untag_tag, cond_false]

end IncDec

section Xfer

def pushAll (ps : List (Σ k, Γ k)) (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  ps.foldr (fun p q => .push p.1 (fun _ => p.2) q) q

def addU (ps : List (Σ k, Γ k)) (i : ℕ) (S : ∀ k, List (Γ k)) : ∀ k, List (Γ k) :=
  fun k => (List.dlookup k ps).elim (S k) (fun x => cnt x i ++ S k)

theorem addU_zero (ps : List (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : addU ps 0 S = S := by
  funext k; unfold addU; cases List.dlookup k ps <;> rfl

theorem addU_addU (ps : List (Σ k, Γ k)) (i j : ℕ) (S : ∀ k, List (Γ k)) :
    addU ps i (addU ps j S) = addU ps (i + j) S := by
  funext k; unfold addU
  cases List.dlookup k ps <;> simp [← List.append_assoc]

theorem addU_of_not_mem {ps : List (Σ k, Γ k)} {k : K} (hk : k ∉ ps.keys) (i : ℕ)
    (S : ∀ k, List (Γ k)) : addU ps i S k = S k := by
  simp [addU, List.dlookup_eq_none.2 hk]

theorem addU_update {ps : List (Σ k, Γ k)} {k : K} (hk : k ∉ ps.keys) (i : ℕ)
    (S : ∀ k, List (Γ k)) (l : List (Γ k)) :
    addU ps i (update S k l) = update (addU ps i S) k l := by
  funext k'
  by_cases h : k' = k
  · subst h; simp [addU_of_not_mem hk]
  · simp only [addU, update_of_ne h]

theorem stepAux_pushAll {ps : List (Σ k, Γ k)} (hps : ps.NodupKeys) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (pushAll ps q) v S = TM2.stepAux q v (addU ps 1 S) := by
  induction ps generalizing S with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨a, x⟩ := p
      rw [List.nodupKeys_cons] at hps
      simp only [pushAll, List.foldr_cons, TM2.stepAux] at ih ⊢
      rw [ih hps.2]
      congr 1
      funext k
      by_cases h : k = a
      · subst h
        simp [addU, List.dlookup_eq_none.2 hps.1, List.dlookup_cons_eq]
      · simp only [addU, update_of_ne h, List.dlookup_cons_ne ps ⟨a, x⟩ h]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def xfer (k : K) (ps : List (Σ k, Γ k)) (self next : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (pushAll ps (.goto fun _ => self)) (.goto fun _ => next))

theorem xfer_run {self next : Λ} {k : K} {ps : List (Σ k, Γ k)}
    (hp : M self = xfer k ps self next) (hps : ps.NodupKeys) (hk : k ∉ ps.keys) (u : Γ k) :
    ∀ (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S k = cnt u n →
      Run M (n + 1) ⟨some self, v, S⟩ ⟨some next, Flag.tag false, addU ps n (update S k [])⟩ := by
  intro n
  induction n with
  | zero =>
      intro v S hS
      have hu : update S k [] = S := by rw [← cnt_zero u, ← hS, update_eq_self]
      refine Run.single ?_
      simp only [hp, xfer, TM2.stepAux, hS, cnt_zero, List.head?_nil, Option.isSome_none,
        List.tail_nil, Flag.untag_tag, cond_false, addU_zero]
  | succ n ih =>
      intro v S hS
      set S₁ := addU ps 1 (update S k (cnt u n)) with hS₁
      have h₁ : S₁ k = cnt u n := by rw [hS₁, addU_of_not_mem hk, update_self]
      have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
        simp only [TM2.step, hp, xfer, TM2.stepAux, hS, cnt_succ, List.head?_cons,
          Option.isSome_some, List.tail_cons, Flag.untag_tag, cond_true, stepAux_pushAll hps,
          hS₁]
      have key := Run.head hstep (ih (Flag.tag true) S₁ h₁)
      have : addU ps n (update S₁ k []) = addU ps (n + 1) (update S k []) := by
        rw [hS₁, ← addU_update hk, update_idem, addU_addU, add_comm]
      rw [this] at key
      exact key

end Xfer

theorem addU_single_self {k : K} (x : Γ k) (i : ℕ) (S : ∀ k, List (Γ k)) :
    addU [⟨k, x⟩] i S k = cnt x i ++ S k := by
  simp [addU, List.dlookup_cons_eq]

theorem addU_single_ne {k k' : K} (x : Γ k) (i : ℕ) (S : ∀ k, List (Γ k)) (h : k' ≠ k) :
    addU [⟨k, x⟩] i S k' = S k' := by
  simp [addU, List.dlookup_cons_ne _ ⟨k, x⟩ h]

omit [DecidableEq K] in
theorem single_nodupKeys {k : K} (x : Γ k) : List.NodupKeys [(⟨k, x⟩ : Σ k, Γ k)] := by
  simp [List.NodupKeys]

def sumFrom (f : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => f i + sumFrom f (i + 1) j

theorem sumFrom_const (c i j : ℕ) : sumFrom (fun _ => c) i j = j * c := by
  induction j generalizing i with
  | zero => simp [sumFrom]
  | succ j ih => rw [sumFrom, ih, Nat.succ_mul, Nat.add_comm]

section For

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def forHead (c cd : K) (ucd : Γ cd) (body rest : Λ) : TM2.Stmt Γ Λ σ :=
  .pop c (fun _ o => Flag.tag o.isSome) <| .branch Flag.untag
    (.push cd (fun _ => ucd) <| .goto fun _ => body) (.goto fun _ => rest)

theorem forLoop_run {c cd : K} {uc : Γ c} {ucd : Γ cd} {head body rest next : Λ}
    (hHead : M head = forHead c cd ucd body rest)
    (hRest : M rest = xfer cd [⟨c, uc⟩] rest next) (hc : c ≠ cd) (n : ℕ)
    (P : ℕ → (∀ k, List (Γ k)) → Prop)
    (hP : ∀ i S S', (∀ k, k ≠ c → k ≠ cd → S' k = S k) → P i S → P i S')
    (cost : ℕ → ℕ)
    (hbody : ∀ i < n, ∀ S : ∀ k, List (Γ k), S c = cnt uc (n - 1 - i) → S cd = cnt ucd (i + 1) →
      P i S → ∃ (v' : σ) (S' : ∀ k, List (Γ k)),
        Run M (cost i) ⟨some body, Flag.tag true, S⟩ ⟨some head, v', S'⟩ ∧
        S' c = S c ∧ S' cd = S cd ∧ P (i + 1) S')
    (v : σ) (S : ∀ k, List (Γ k)) (hSc : S c = cnt uc n) (hScd : S cd = []) (h0 : P 0 S) :
    ∃ S' : ∀ k, List (Γ k),
      Run M (sumFrom (fun i => cost i + 1) 0 n + n + 2) ⟨some head, v, S⟩
        ⟨some next, Flag.tag false, S'⟩ ∧
      S' c = cnt uc n ∧ S' cd = [] ∧ P n S' := by

  have loop : ∀ j i, i + j = n → ∀ (v : σ) (S : ∀ k, List (Γ k)), S c = cnt uc j →
      S cd = cnt ucd i → P i S → ∃ S' : ∀ k, List (Γ k),
        Run M (sumFrom (fun i => cost i + 1) i j + 1) ⟨some head, v, S⟩
          ⟨some rest, Flag.tag false, S'⟩ ∧ S' c = [] ∧ S' cd = cnt ucd n ∧ P n S' := by
    intro j
    induction j with
    | zero =>
        intro i hi v S h1 h2 h3
        obtain rfl : i = n := by omega
        refine ⟨S, Run.single ?_, h1, h2, h3⟩
        have hu : update S c [] = S := by rw [← cnt_zero uc, ← h1, update_eq_self]
        simp only [hHead, forHead, TM2.stepAux, h1, cnt_zero, List.head?_nil, List.tail_nil,
          Option.isSome_none, Flag.untag_tag, cond_false, hu]
    | succ j ih =>
        intro i hi v S h1 h2 h3
        set S₁ := update (update S c (cnt uc j)) cd (ucd :: cnt ucd i) with hS₁
        have h₁c : S₁ c = cnt uc (n - 1 - i) := by
          rw [hS₁, update_of_ne hc, update_self]; congr 1; omega
        have h₁cd : S₁ cd = cnt ucd (i + 1) := by rw [hS₁, update_self]; rfl
        have h₁P : P i S₁ := hP i S S₁ (fun k hk1 hk2 => by
          rw [hS₁, update_of_ne hk2, update_of_ne hk1]) h3
        obtain ⟨v', S₂, hrun, h₂c, h₂cd, h₂P⟩ := hbody i (by omega) S₁ h₁c h₁cd h₁P
        obtain ⟨S', hrun', h'c, h'cd, h'P⟩ := ih (i + 1) (by omega) v' S₂
          (by rw [h₂c, h₁c]; congr 1; omega) (by rw [h₂cd, h₁cd]) h₂P
        refine ⟨S', ?_, h'c, h'cd, h'P⟩
        have hstep : TM2.step M ⟨some head, v, S⟩ = some ⟨some body, Flag.tag true, S₁⟩ := by
          simp only [TM2.step, hHead, forHead, TM2.stepAux, h1, cnt_succ, List.head?_cons,
            List.tail_cons, Option.isSome_some, Flag.untag_tag, cond_true,
            update_of_ne (Ne.symm hc), h2, hS₁]
        refine (Run.head hstep (hrun.trans hrun')).of_eq ?_
        simp only [sumFrom]; omega
  obtain ⟨S', hrun, h'c, h'cd, h'P⟩ := loop n 0 (by omega) v S hSc hScd h0
  have hx :=
    xfer_run hRest (single_nodupKeys uc) (by simpa using hc.symm) ucd n (Flag.tag false) S' h'cd
  refine ⟨_, (hrun.trans hx).of_eq (by omega), ?_, ?_, ?_⟩
  · rw [addU_single_self, update_of_ne hc, h'c, List.append_nil]
  · rw [addU_single_ne _ _ _ (Ne.symm hc), update_self]
  · exact hP n S' _ (fun k hk1 hk2 => by rw [addU_single_ne _ _ _ hk1, update_of_ne hk2]) h'P

end For

section Emit

def pushList (k : K) (xs : List (Γ k)) (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  xs.foldr (fun x q => .push k (fun _ => x) q) q

theorem stepAux_pushList (k : K) (xs : List (Γ k)) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) :
    TM2.stepAux (pushList k xs q) v S = TM2.stepAux q v (update S k (xs.reverse ++ S k)) := by
  induction xs generalizing S with
  | nil => simp [pushList]
  | cons x xs ih =>
      simp only [pushList, List.foldr_cons, TM2.stepAux] at ih ⊢
      rw [ih, update_self, update_idem]
      simp

variable {M : Λ → TM2.Stmt Γ Λ σ}

def emit (k : K) (xs : List (Γ k)) (next : Λ) : TM2.Stmt Γ Λ σ :=
  pushList k xs (.goto fun _ => next)

theorem emit_run {self next : Λ} {k : K} {xs : List (Γ k)} (hp : M self = emit k xs next)
    (v : σ) (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (xs.reverse ++ S k)⟩ :=
  Run.single (by rw [hp, emit, stepAux_pushList]; rfl)

end Emit

section Arith

omit [DecidableEq K] in
theorem pair_nodupKeys {a b : K} (x : Γ a) (y : Γ b) (h : a ≠ b) :
    List.NodupKeys [(⟨a, x⟩ : Σ k, Γ k), ⟨b, y⟩] := by
  simp [List.NodupKeys, h]

theorem addU_pair_fst {a b : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k)) :
    addU [⟨a, x⟩, ⟨b, y⟩] i S a = cnt x i ++ S a := by
  simp [addU, List.dlookup_cons_eq]

theorem addU_pair_snd {a b : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k)) (h : b ≠ a) :
    addU [⟨a, x⟩, ⟨b, y⟩] i S b = cnt y i ++ S b := by
  simp [addU, List.dlookup_cons_ne _ ⟨a, x⟩ h, List.dlookup_cons_eq]

theorem addU_pair_ne {a b k : K} (x : Γ a) (y : Γ b) (i : ℕ) (S : ∀ k, List (Γ k))
    (ha : k ≠ a) (hb : k ≠ b) : addU [⟨a, x⟩, ⟨b, y⟩] i S k = S k := by
  simp [addU, List.dlookup_cons_ne _ ⟨a, x⟩ ha, List.dlookup_cons_ne _ ⟨b, y⟩ hb]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

theorem copy_run {a c t : K} {ua : Γ a} {uc : Γ c} {ut : Γ t} {l₁ l₂ next : Λ}
    (h₁ : M l₁ = xfer a [⟨c, uc⟩, ⟨t, ut⟩] l₁ l₂) (h₂ : M l₂ = xfer t [⟨a, ua⟩] l₂ next)
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t) (m p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (ha : S a = cnt ua m) (hc : S c = cnt uc p) (ht : S t = []) :
    Run M (2 * m + 2) ⟨some l₁, v, S⟩ ⟨some next, Flag.tag false, update S c (cnt uc (m + p))⟩ := by
  have r₁ := xfer_run h₁ (pair_nodupKeys uc ut hct) (by simp [hac, hat]) ua m v S ha
  set S₁ := addU [⟨c, uc⟩, ⟨t, ut⟩] m (update S a []) with hS₁
  have h₁t : S₁ t = cnt ut m := by
    rw [hS₁, addU_pair_snd _ _ _ _ hct.symm, update_of_ne hat.symm, ht, List.append_nil]
  have r₂ := xfer_run h₂ (single_nodupKeys ua) (by simp [hat.symm]) ut m (Flag.tag false) S₁ h₁t
  have hfin : addU [⟨a, ua⟩] m (update S₁ t []) = update S c (cnt uc (m + p)) := by
    funext k
    by_cases hka : k = a
    · subst hka
      rw [addU_single_self, update_of_ne hat, hS₁, addU_pair_ne _ _ _ _ hac hat, update_self,
        update_of_ne hac, ha, List.append_nil]
    rw [addU_single_ne _ _ _ hka]
    by_cases hkt : k = t
    · subst hkt; rw [update_self, update_of_ne hct.symm, ht]
    rw [update_of_ne hkt]
    by_cases hkc : k = c
    · subst hkc
      rw [hS₁, addU_pair_fst, update_of_ne (Ne.symm hac), hc, cnt_add, update_self]
    rw [hS₁, addU_pair_ne _ _ _ _ hkc hkt, update_of_ne hka, update_of_ne hkc]
  rw [hfin] at r₂
  exact (r₁.trans r₂).of_eq (by omega)

theorem mul_run {a ad b c t : K} {ua : Γ a} {uad : Γ ad} {ub : Γ b} {uc : Γ c} {ut : Γ t}
    {head body l₂ rest next : Λ}
    (hHead : M head = forHead a ad uad body rest)
    (hBody : M body = xfer b [⟨c, uc⟩, ⟨t, ut⟩] body l₂)
    (hL₂ : M l₂ = xfer t [⟨b, ub⟩] l₂ head)
    (hRest : M rest = xfer ad [⟨a, ua⟩] rest next)
    (hnd : [a, ad, b, c, t].Nodup) (m n p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (ha : S a = cnt ua m) (had : S ad = []) (hb : S b = cnt ub n) (hc : S c = cnt uc p)
    (ht : S t = []) :
    Run M (m * (2 * n + 3) + m + 2) ⟨some head, v, S⟩
      ⟨some next, Flag.tag false, update S c (cnt uc (m * n + p))⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haad, hab, hac, hat⟩, ⟨hadb, hadc, hadt⟩, ⟨hbc, hbt⟩, hct, -⟩ := hnd
  let P : ℕ → (∀ k, List (Γ k)) → Prop := fun i S' =>
    ∀ k, k ≠ a → k ≠ ad → S' k = update S c (cnt uc (i * n + p)) k
  have h0 : P 0 S := fun k _ _ => by
    by_cases hkc : k = c
    · subst hkc; rw [update_self, hc]; simp
    · rw [update_of_ne hkc]
  obtain ⟨S', hrun, h'a, h'ad, h'P⟩ := forLoop_run (c := a) (cd := ad) (uc := ua) (ucd := uad)
    hHead hRest haad m P (fun i S₁ S₂ h hP k h1 h2 => by rw [h k h1 h2, hP k h1 h2])
    (fun _ => 2 * n + 2)
    (fun i _ S₁ h₁a h₁ad hP => by
      have hb₁ : S₁ b = cnt ub n := by
        rw [hP b (Ne.symm hab) (Ne.symm hadb), update_of_ne hbc, hb]
      have hc₁ : S₁ c = cnt uc (i * n + p) := by
        rw [hP c (Ne.symm hac) (Ne.symm hadc), update_self]
      have ht₁ : S₁ t = [] := by
        rw [hP t (Ne.symm hat) (Ne.symm hadt), update_of_ne (Ne.symm hct), ht]
      refine ⟨_, _, copy_run hBody hL₂ hbc hbt hct n (i * n + p) (Flag.tag true) S₁ hb₁ hc₁ ht₁,
        by rw [update_of_ne hac], by rw [update_of_ne hadc], fun k h1 h2 => ?_⟩
      by_cases hkc : k = c
      · subst hkc
        rw [update_self, update_self]
        congr 1; rw [Nat.succ_mul]; omega
      · rw [update_of_ne hkc, hP k h1 h2, update_of_ne hkc, update_of_ne hkc])
    v S ha had h0
  have hS' : S' = update S c (cnt uc (m * n + p)) := by
    funext k
    by_cases hka : k = a
    · subst hka; rw [h'a, update_of_ne hac, ha]
    by_cases hkad : k = ad
    · subst hkad; rw [h'ad, update_of_ne hadc, had]
    exact h'P k hka hkad
  rw [hS', sumFrom_const] at hrun
  exact hrun

end Arith
section Gap

def rep {α : Type} (ys : List α) (n : ℕ) : List α := (List.replicate n ys).flatten

@[simp] theorem rep_zero {α : Type} (ys : List α) : rep ys 0 = [] := rfl

theorem rep_succ {α : Type} (ys : List α) (n : ℕ) : rep ys (n + 1) = ys ++ rep ys n := by
  simp [rep, List.replicate_succ]

theorem rep_succ' {α : Type} (ys : List α) (n : ℕ) : rep ys (n + 1) = rep ys n ++ ys := by
  simp [rep, List.replicate_succ']

theorem rep_add {α : Type} (ys : List α) (m n : ℕ) : rep ys (m + n) = rep ys m ++ rep ys n := by
  unfold rep; rw [List.replicate_add, List.flatten_append]

variable [Flag σ] {M : Λ → TM2.Stmt Γ Λ σ}

def emitR (k : K) (ys : List (Γ k)) (next : Λ) : TM2.Stmt Γ Λ σ := emit k ys.reverse next

omit [Flag σ] in
theorem emitR_run {self next : Λ} {k : K} {ys : List (Γ k)} (hp : M self = emitR k ys next)
    (v : σ) (S : ∀ k, List (Γ k)) :
    Run M 1 ⟨some self, v, S⟩ ⟨some next, v, update S k (ys ++ S k)⟩ := by
  simpa using emit_run (M := M) hp v S

def xferE (k o : K) (ys : List (Γ o)) (self next : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k (fun _ o => Flag.tag o.isSome)
    (.branch Flag.untag (pushList o ys.reverse (.goto fun _ => self)) (.goto fun _ => next))

theorem xferE_run {self next : Λ} {k o : K} {ys : List (Γ o)}
    (hp : M self = xferE k o ys self next) (hko : k ≠ o) (u : Γ k) :
    ∀ (n : ℕ) (v : σ) (S : ∀ k, List (Γ k)), S k = cnt u n →
      Run M (n + 1) ⟨some self, v, S⟩
        ⟨some next, Flag.tag false, update (update S k []) o (rep ys n ++ S o)⟩ := by
  intro n
  induction n with
  | zero =>
      intro v S hS
      refine Run.single ?_
      have hu : update S k [] = S := by rw [← cnt_zero u, ← hS, update_eq_self]
      simp only [hp, xferE, TM2.stepAux, hS, cnt_zero, List.head?_nil, Option.isSome_none,
        List.tail_nil, Flag.untag_tag, cond_false, hu, rep_zero, List.nil_append,
        update_eq_self]
  | succ n ih =>
      intro v S hS
      set S₁ := update (update S k (cnt u n)) o (ys ++ S o) with hS₁
      have h₁ : S₁ k = cnt u n := by rw [hS₁, update_of_ne hko, update_self]
      have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, Flag.tag true, S₁⟩ := by
        simp only [TM2.step, hp, xferE, TM2.stepAux, hS, cnt_succ, List.head?_cons,
          Option.isSome_some, List.tail_cons, Flag.untag_tag, cond_true, stepAux_pushList,
          List.reverse_reverse, update_of_ne (Ne.symm hko), hS₁]
      have key := Run.head hstep (ih (Flag.tag true) S₁ h₁)
      have hfin : update (update S₁ k []) o (rep ys n ++ S₁ o) =
          update (update S k []) o (rep ys (n + 1) ++ S o) := by
        funext j
        by_cases hjo : j = o
        · subst hjo; rw [update_self, update_self, hS₁, update_self, rep_succ', List.append_assoc]
        rw [update_of_ne hjo, update_of_ne hjo]
        by_cases hjk : j = k
        · subst hjk; rw [update_self, update_self]
        rw [update_of_ne hjk, update_of_ne hjk, hS₁, update_of_ne hjo, update_of_ne hjk]
      rw [hfin] at key
      exact key

end Gap
end MetaMathlibExt.TM2Program
end
section
namespace MetaMathlibExt.TM2Embedding

open MetaMathlibExt.TM2Program Turing Function

structure SEmb {K K' : Type} (Γ : K → Type) (Γ' : K' → Type) where

  e : K → K'

  inj : Injective e

  ι : ∀ k, Γ k ≃ Γ' (e k)

section Embed

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {Γ : K → Type} {Γ' : K' → Type}
  {Λ Λ' σ : Type} (E : SEmb Γ Γ') (φ : Λ → Λ')

def mapS : TM2.Stmt Γ Λ σ → TM2.Stmt Γ' Λ' σ
  | .push k f q => .push (E.e k) (fun s => E.ι k (f s)) (mapS q)
  | .peek k f q => .peek (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .pop k f q => .pop (E.e k) (fun s o => f s (o.map (E.ι k).symm)) (mapS q)
  | .load a q => .load a (mapS q)
  | .branch f q₁ q₂ => .branch f (mapS q₁) (mapS q₂)
  | .goto f => .goto fun s => φ (f s)
  | .halt => .halt

def Embeds (M : Λ → TM2.Stmt Γ Λ σ) (M' : Λ' → TM2.Stmt Γ' Λ' σ) : Prop :=
  ∀ l, M' (φ l) = mapS E φ (M l) ∨ M l = .halt

def Agree (S : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k')) : Prop :=
  ∀ k, S' (E.e k) = (S k).map (E.ι k)

def Frame (S' S'' : ∀ k', List (Γ' k')) : Prop :=
  ∀ k', (∀ k, E.e k ≠ k') → S'' k' = S' k'

variable {E}

omit [DecidableEq K] [DecidableEq K'] in
theorem Frame.refl (S' : ∀ k', List (Γ' k')) : Frame E S' S' := fun _ _ => rfl

omit [DecidableEq K] [DecidableEq K'] in
theorem Frame.trans {S₁ S₂ S₃ : ∀ k', List (Γ' k')} (h₁ : Frame E S₁ S₂) (h₂ : Frame E S₂ S₃) :
    Frame E S₁ S₃ := fun k' hk => (h₂ k' hk).trans (h₁ k' hk)

omit [DecidableEq K] in
theorem Frame.update (S' : ∀ k', List (Γ' k')) (k : K) (l : List (Γ' (E.e k))) :
    Frame E S' (update S' (E.e k) l) := fun _ hk => update_of_ne (hk k).symm _ _

theorem Agree.update {S : ∀ k, List (Γ k)} {S' : ∀ k', List (Γ' k')} (h : Agree E S S') (k : K)
    (l : List (Γ k)) :
    Agree E (Function.update S k l) (Function.update S' (E.e k) (l.map (E.ι k))) := by
  intro k₂
  by_cases hk : k₂ = k
  · subst hk; simp
  · rw [update_of_ne (E.inj.ne hk), update_of_ne hk]; exact h k₂

theorem stepAux_mapS (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k'))
    (hA : Agree E S S') :
    ∃ T' : ∀ k', List (Γ' k'),
      TM2.stepAux (mapS E φ q) v S' =
        ⟨(TM2.stepAux q v S).l.map φ, (TM2.stepAux q v S).var, T'⟩ ∧
      Agree E (TM2.stepAux q v S).stk T' ∧ Frame E S' T' := by
  induction q generalizing v S S' with
  | push k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih v _ _ (hA.update k (f v :: S k))
      refine ⟨T', ?_, h2, (Frame.update S' k _).trans h3⟩
      simp only [mapS, TM2.stepAux, hA k]
      exact h1
  | peek k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (f v (S k).head?) S S' hA
      refine ⟨T', ?_, h2, h3⟩
      simp only [mapS, TM2.stepAux, hA k, List.head?_map, Option.map_map, Equiv.symm_comp_self,
        Option.map_id_fun, id_eq]
      exact h1
  | pop k f q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (f v (S k).head?) _ _ (hA.update k (S k).tail)
      refine ⟨T', ?_, h2, (Frame.update S' k _).trans h3⟩
      simp only [mapS, TM2.stepAux, hA k, List.head?_map, Option.map_map, Equiv.symm_comp_self,
        Option.map_id_fun, id_eq, ← List.map_tail]
      exact h1
  | load a q ih =>
      obtain ⟨T', h1, h2, h3⟩ := ih (a v) S S' hA
      exact ⟨T', by simpa only [mapS, TM2.stepAux] using h1, h2, h3⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases hf : f v
      · obtain ⟨T', h1, h2, h3⟩ := ih₂ v S S' hA
        exact ⟨T', by simpa only [mapS, TM2.stepAux, hf, cond_false] using h1,
          by simpa only [TM2.stepAux, hf, cond_false] using h2, h3⟩
      · obtain ⟨T', h1, h2, h3⟩ := ih₁ v S S' hA
        exact ⟨T', by simpa only [mapS, TM2.stepAux, hf, cond_true] using h1,
          by simpa only [TM2.stepAux, hf, cond_true] using h2, h3⟩
  | goto f => exact ⟨S', by simp [mapS, TM2.stepAux], hA, Frame.refl S'⟩
  | halt => exact ⟨S', by simp [mapS, TM2.stepAux], hA, Frame.refl S'⟩

theorem run_embed {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ' Λ' σ} (hM : Embeds E φ M M') :
    ∀ (n : ℕ) (l : Option Λ) (v : σ) (S : ∀ k, List (Γ k)) (l' : Λ) (v' : σ)
      (T : ∀ k, List (Γ k)) (S' : ∀ k', List (Γ' k')),
      Run M n ⟨l, v, S⟩ ⟨some l', v', T⟩ → Agree E S S' →
      ∃ T' : ∀ k', List (Γ' k'),
        Run M' n ⟨l.map φ, v, S'⟩ ⟨some (φ l'), v', T'⟩ ∧ Agree E T T' ∧ Frame E S' T' := by
  intro n
  induction n with
  | zero =>
      intro l v S l' v' T S' h hA
      simp only [Run, iterate_zero, id_eq, Option.some.injEq, TM2.Cfg.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨S', Run.zero _, hA, Frame.refl S'⟩
  | succ n ih =>
      intro l v S l' v' T S' h hA
      unfold Run at h
      rw [iterate_succ_apply] at h
      rcases l with _ | l
      · have : (flip bind (TM2.step M)) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
        rw [this, iter_none] at h
        exact absurd h (by simp)
      · have e : (flip bind (TM2.step M)) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
            some (TM2.stepAux (M l) v S) := rfl
        rw [e] at h
        rcases hM l with hl | hl
        · obtain ⟨T₁, h1, h2, h3⟩ := stepAux_mapS φ (M l) v S S' hA
          obtain ⟨T', r, h4, h5⟩ := ih _ _ _ _ _ _ T₁ h h2
          refine ⟨T', Run.head ?_ r, h4, h3.trans h5⟩
          simp only [Option.map_some, TM2.step, hl, h1]
        · rw [hl] at h
          simp only [TM2.stepAux] at h
          cases n with
          | zero => simp at h
          | succ n =>
              rw [iterate_succ_apply] at h
              have : (flip bind (TM2.step M)) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none :=
                rfl
              rw [this, iter_none] at h
              exact absurd h (by simp)

end Embed
end MetaMathlibExt.TM2Embedding
end
section
namespace Cslib.Complexity.CookLevin.CounterView

open MetaMathlibExt MetaMathlibExt.TM2Program Turing Function

inductive MS | head | body | l2 | rest
  deriving DecidableEq
instance MS.instFintypeEnumFix : Fintype MS where
  elems := ⟨↑[MS.head, MS.body, MS.l2, MS.rest], by decide⟩
  complete := fun x => by cases x <;> decide

inductive SK (C : Type)
  | out
  | c (x : C)
  deriving DecidableEq, Fintype

abbrev SΓ (C : Type) : SK C → Type
  | .out => Bool
  | .c _ => Unit

section View

variable {C : Type} [DecidableEq C]

def st (f : C → ℕ) (o : List Bool) : ∀ k, List (SΓ C k)
  | .out => o
  | .c x => cnt () (f x)

omit [DecidableEq C] in
@[simp] theorem st_c (f : C → ℕ) (o : List Bool) (x : C) : st f o (.c x) = cnt () (f x) := rfl
omit [DecidableEq C] in
@[simp] theorem st_out (f : C → ℕ) (o : List Bool) : st f o .out = o := rfl

theorem update_st_c (f : C → ℕ) (o : List Bool) (x : C) (n : ℕ) :
    update (st f o) (.c x) (cnt () n) = st (update f x n) o := by
  funext k
  rcases k with _ | y
  · rfl
  · by_cases h : y = x
    · subst h; simp
    · rw [update_of_ne (by simpa using h)]; simp [update_of_ne h]

theorem update_st_nil (f : C → ℕ) (o : List Bool) (x : C) :
    update (st f o) (.c x) [] = st (update f x 0) o := update_st_c f o x 0

theorem update_st_out (f : C → ℕ) (o l : List Bool) : update (st f o) .out l = st f l := by
  funext k
  rcases k with _ | y
  · simp
  · rw [update_of_ne (by simp)]; rfl

theorem addU_nil {K : Type} [DecidableEq K] {Γ : K → Type} (n : ℕ) (S : ∀ k, List (Γ k)) :
    addU [] n S = S := rfl

variable {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem emitS {self next : Λ} {x : C} {n : ℕ}
    (hp : M self = emitR (.c x) (List.replicate n ()) next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (n + F x)) o⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_c, show List.replicate n () = cnt () n from rfl, cnt_add, update_st_c] at this
  exact this

theorem emitOut {self next : Λ} {ys : List Bool} (hp : M self = emitR .out ys next)
    (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st F (ys ++ o)⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_out, update_st_out] at this
  exact this

theorem incS {self next : Λ} {x : C} (hp : M self = incr (.c x) () next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (F x + 1)) o⟩ := by
  have := incr_run_cnt hp v (S := st F o) (n := F x) rfl
  rw [update_st_c] at this
  exact this

theorem drainS {self next : Λ} {x : C} (hp : M self = xfer (.c x) [] self next) (F : C → ℕ)
    (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (update F x 0) o⟩ := by
  have := xfer_run hp (by simp [List.NodupKeys]) (by simp) () (F x) v (st F o) rfl
  rw [addU_nil, update_st_nil] at this
  exact this

theorem xferES {self next : Λ} {x : C} {ys : List Bool}
    (hp : M self = xferE (.c x) .out ys self next) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩
      ⟨some next, false, st (update F x 0) (rep ys (F x) ++ o)⟩ := by
  have := xferE_run hp (by simp) () (F x) v (st F o) rfl
  rw [update_st_nil, update_st_out, st_out] at this
  exact this

theorem copyS {l₁ l₂ next : Λ} {a c t : C}
    (h₁ : M l₁ = xfer (.c a) [⟨.c c, ()⟩, ⟨.c t, ()⟩] l₁ l₂)
    (h₂ : M l₂ = xfer (.c t) [⟨.c a, ()⟩] l₂ next)
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t) (F : C → ℕ) (ht : F t = 0) (v : Bool)
    (o : List Bool) :
    Run M (2 * F a + 2) ⟨some l₁, v, st F o⟩
      ⟨some next, false, st (update F c (F a + F c)) o⟩ := by
  have := copy_run h₁ h₂ (by simpa using hac) (by simpa using hat) (by simpa using hct) (F a)
    (F c) v (st F o) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

def mulS (a ad b c t : C) (mk : MS → Λ) (next : Λ) : MS → TM2.Stmt (SΓ C) Λ Bool
  | .head => forHead (.c a) (.c ad) () (mk .body) (mk .rest)
  | .body => xfer (.c b) [⟨.c c, ()⟩, ⟨.c t, ()⟩] (mk .body) (mk .l2)
  | .l2 => xfer (.c t) [⟨.c b, ()⟩] (mk .l2) (mk .head)
  | .rest => xfer (.c ad) [⟨.c a, ()⟩] (mk .rest) next

theorem mulS_run {a ad b c t : C} {mk : MS → Λ} {next : Λ}
    (hp : ∀ s, M (mk s) = mulS a ad b c t mk next s)
    (hnd : ([.c a, .c ad, .c b, .c c, .c t] : List (SK C)).Nodup)
    (F : C → ℕ) (had : F ad = 0) (ht : F t = 0) (v : Bool) (o : List Bool) :
    Run M (F a * (2 * F b + 3) + F a + 2) ⟨some (mk .head), v, st F o⟩
      ⟨some next, false, st (update F c (F a * F b + F c)) o⟩ := by
  have := mul_run (hp .head) (hp .body) (hp .l2) (hp .rest) hnd (F a) (F b) (F c) v (st F o) rfl
    (by simp [had]) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

end View
end Cslib.Complexity.CookLevin.CounterView
end
namespace Cslib.Complexity.CookLevin.Precompute
open MetaMathlibExt
open MetaMathlibExt.TM2Program Cslib.Complexity.CookLevin.CounterView Turing Function
section CLib
variable {C : Type} [DecidableEq C] {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}
def tg (ys : List C) : List (Σ k, SΓ C k) := ys.map fun y => ⟨.c y, ()⟩

omit [DecidableEq C] in
theorem tg_keys (ys : List C) : (tg ys).keys = ys.map SK.c := by
  simp [tg, List.keys]

omit [DecidableEq C] in
theorem tg_nodupKeys {ys : List C} (h : ys.Nodup) : (tg ys).NodupKeys := by
  unfold List.NodupKeys
  rw [tg_keys]
  exact h.map (fun _ _ h => by cases h; rfl)

theorem dlookup_tg (ys : List C) (z : C) :
    List.dlookup (SK.c z) (tg ys) = if z ∈ ys then some () else none := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : z = y
      · subst h; simp [tg, List.dlookup_cons_eq]
      · rw [tg, List.map_cons, List.dlookup_cons_ne _ _ (by simpa using h)]
        rw [← tg, ih]; simp [h]

theorem dlookup_tg_out (ys : List C) : List.dlookup (SK.out) (tg ys) = none := by
  rw [List.dlookup_eq_none, tg_keys]; simp

def xf (F : C → ℕ) (x : C) (ys : List C) : C → ℕ :=
  fun z => if z = x then 0 else if z ∈ ys then F z + F x else F z

theorem xferS {self next : Λ} {x : C} {ys : List C} (hp : M self = xfer (.c x) (tg ys) self next)
    (hnd : ys.Nodup) (hx : x ∉ ys) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (xf F x ys) o⟩ := by
  have := xfer_run hp (tg_nodupKeys hnd) (by rw [tg_keys]; simpa using hx) () (F x) v (st F o) rfl
  have e : addU (tg ys) (F x) (update (st F o) (SK.c x) []) = st (xf F x ys) o := by
    funext k
    rcases k with _ | z
    · simp [addU, dlookup_tg_out]
    · simp only [addU, dlookup_tg]
      by_cases hz : z = x
      · subst hz; simp [xf, hx]
      · rw [update_of_ne (by simpa using hz)]
        by_cases hy : z ∈ ys
        · simp [xf, hz, hy, add_comm]
        · simp [xf, hz, hy]
  rw [e] at this
  exact this

inductive HW
  | mul (s : MS)
  | drn
  | mv
  | add
  deriving DecidableEq, Fintype

def hornS (b acc q ad t : C) (a : ℕ) (mk : HW → Λ) (next : Λ) : HW → TM2.Stmt (SΓ C) Λ Bool
  | .mul s => mulS acc ad b q t (fun s => mk (.mul s)) (mk .drn) s
  | .drn => xfer (.c acc) [] (mk .drn) (mk .mv)
  | .mv => xfer (.c q) (tg [acc]) (mk .mv) (mk .add)
  | .add => emitR (.c acc) (List.replicate a ()) next

def hornStep (A b : ℕ) : ℕ := A * (2 * b + 3) + A + 2 + (A + 1) + (A * b + 1) + 1

theorem horn_round {b acc q ad t : C} {a : ℕ} {mk : HW → Λ} {next : Λ}
    (hp : ∀ s, M (mk s) = hornS b acc q ad t a mk next s)
    (hnd : [b, acc, q, ad, t].Nodup) (F : C → ℕ) (hq : F q = 0) (had : F ad = 0)
    (ht : F t = 0) (v : Bool) (o : List Bool) :
    Run M (hornStep (F acc) (F b)) ⟨some (mk (.mul .head)), v, st F o⟩
      ⟨some next, false, st (update F acc (F acc * F b + a)) o⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hba, hbq, hbad, hbt⟩, ⟨haq, haad, hat⟩, ⟨hqad, hqt⟩, hadt, -⟩ := hnd
  have r1 := mulS_run (a := acc) (ad := ad) (b := b) (c := q) (t := t)
    (mk := fun s => mk (.mul s)) (next := mk .drn) (M := M) (fun s => hp (.mul s))
    (by simp [haad, Ne.symm hba, haq, hat, Ne.symm hbad, Ne.symm hqad, hadt, hbq, hbt, hqt])
    F had ht v o
  set F1 := update F q (F acc * F b + F q) with hF1
  have r2 := drainS (hp .drn) F1 false o
  set F2 := update F1 acc 0 with hF2
  have r3 := xferS (hp .mv) (by simp) (by simpa using Ne.symm haq) F2 false o
  set F3 := xf F2 q [acc] with hF3
  have r4 := emitS (n := a) (hp .add) F3 false o
  have hF1a : F1 acc = F acc := by rw [hF1, update_of_ne haq]
  have hF2q : F2 q = F acc * F b := by
    rw [hF2, update_of_ne (Ne.symm haq), hF1, update_self, hq, add_zero]
  have hF3a : F3 acc = F acc * F b := by
    simp only [hF3, xf, if_neg haq, List.mem_singleton, if_true, hF2, update_self,
      zero_add]
    exact hF2q
  have hend : update F3 acc (a + F3 acc) = update F acc (F acc * F b + a) := by
    funext z
    by_cases h1 : z = acc
    · subst h1; rw [update_self, update_self, hF3a, add_comm]
    rw [update_of_ne h1, update_of_ne h1]
    by_cases h2 : z = q
    · subst h2; simp [hF3, xf, hq]
    simp only [hF3, xf, if_neg h2, List.mem_singleton, if_neg h1, hF2, hF1,
      update_of_ne h1, update_of_ne h2]
  rw [hend] at r4
  rw [hF1a] at r2
  rw [hF2q] at r3
  exact (r1.trans (r2.trans (r3.trans r4))).of_eq (by unfold hornStep; ring)

def hornVal (cs : List ℕ) (b A : ℕ) : ℕ := cs.foldl (fun A a => A * b + a) A

def hornT : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | a :: cs, b, A => hornStep A b + hornT cs b (A * b + a)

theorem horner_run {b acc q ad t : C} (cs : List ℕ) {mk : ℕ → HW → Λ} {exit : Λ}
    (hp : ∀ i (hi : i < cs.length) s, M (mk i s) = hornS b acc q ad t cs[i] (mk i)
      (if i + 1 < cs.length then mk (i + 1) (.mul .head) else exit) s)
    (hnd : [b, acc, q, ad, t].Nodup) :
    ∀ (j i : ℕ), i + j = cs.length → ∀ (F : C → ℕ), F q = 0 → F ad = 0 → F t = 0 →
      ∀ (v : Bool) (o : List Bool),
      ∃ v' : Bool, Run M (hornT (cs.drop i) (F b) (F acc))
        ⟨some (if i < cs.length then mk i (.mul .head) else exit), v, st F o⟩
        ⟨some exit, v', st (update F acc (hornVal (cs.drop i) (F b) (F acc))) o⟩ := by
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨hba, hbq, hbad, hbt⟩, ⟨haq, haad, hat⟩, ⟨hqad, hqt⟩, hadt, -⟩ := hnd'
  intro j
  induction j with
  | zero =>
      intro i hi F _ _ _ v o
      have hd : cs.drop i = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨v, ?_⟩
      rw [hd, if_neg (by omega)]
      simp only [hornT, hornVal, List.foldl_nil, update_eq_self]
      exact TM2Program.Run.zero _
  | succ j ih =>
      intro i hi F hq had ht v o
      have hlt : i < cs.length := by omega
      have hd : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hlt
      have r1 := horn_round (a := cs[i]) (mk := mk i) (hp i hlt) hnd F hq had ht v o
      set F1 := update F acc (F acc * F b + cs[i]) with hF1
      obtain ⟨v', r2⟩ := ih (i + 1) (by omega) F1 (by rw [hF1, update_of_ne (Ne.symm haq), hq])
        (by rw [hF1, update_of_ne (Ne.symm haad), had])
        (by rw [hF1, update_of_ne (Ne.symm hat), ht]) false o
      have hF1b : F1 b = F b := by rw [hF1, update_of_ne hba]
      have hF1a : F1 acc = F acc * F b + cs[i] := by rw [hF1, update_self]
      rw [hF1b, hF1a] at r2
      have hupd : update F1 acc (hornVal (cs.drop (i + 1)) (F b) (F acc * F b + cs[i])) =
          update F acc (hornVal (cs.drop (i + 1)) (F b) (F acc * F b + cs[i])) := by
        rw [hF1, update_idem]
      rw [hupd] at r2
      refine ⟨v', ?_⟩
      rw [if_pos hlt, hd]
      exact r1.trans r2

theorem hornVal_eq (cs : List ℕ) (b A : ℕ) :
    hornVal cs b A = A * b ^ cs.length + hornVal cs b 0 := by
  induction cs generalizing A with
  | nil => simp [hornVal]
  | cons a cs ih =>
      simp only [hornVal, List.foldl_cons, List.length_cons] at ih ⊢
      rw [ih (A * b + a), ih (0 * b + a)]
      ring

noncomputable def coeffs (p : Polynomial ℕ) : List ℕ :=
  (List.range (p.natDegree + 1)).reverse.map p.coeff

theorem hornVal_range (f : ℕ → ℕ) (b D : ℕ) :
    hornVal ((List.range D).reverse.map f) b 0 = ∑ i ∈ Finset.range D, f i * b ^ i := by
  induction D with
  | zero => simp [hornVal]
  | succ D ih =>
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, Finset.sum_range_succ]
      have := hornVal_eq ((List.range D).reverse.map f) b (0 * b + f D)
      simp only [hornVal, List.foldl_cons, List.length_map, List.length_reverse,
        List.length_range] at this ih ⊢
      rw [this, ih]
      ring

theorem hornVal_coeffs (p : Polynomial ℕ) (b : ℕ) : hornVal (coeffs p) b 0 = p.eval b := by
  rw [coeffs, hornVal_range, Polynomial.eval_eq_sum_range]

end CLib
end Cslib.Complexity.CookLevin.Precompute
namespace OMA.Padding
open Turing Function ComplexityTheory BitstringEncoding
open MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open Cslib.Complexity.CookLevin.CounterView Cslib.Complexity.CookLevin.Precompute
def NatPolynomialBound (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n = p.eval n

namespace NatPolynomialBound

theorem const (a : ℕ) : NatPolynomialBound fun _ => a := ⟨Polynomial.C a, fun _ => by simp⟩

theorem id : NatPolynomialBound fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : NatPolynomialBound f) (hg : NatPolynomialBound g) : NatPolynomialBound fun n => f n + g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p + q, fun n => by simp [hp, hq]⟩

theorem mul {f g : ℕ → ℕ} (hf : NatPolynomialBound f) (hg : NatPolynomialBound g) : NatPolynomialBound fun n => f n * g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p * q, fun n => by simp [hp, hq]⟩

theorem pow {f : ℕ → ℕ} (hf : NatPolynomialBound f) (j : ℕ) : NatPolynomialBound fun n => f n ^ j := by
  obtain ⟨p, hp⟩ := hf; exact ⟨p ^ j, fun n => by simp [hp]⟩

theorem eval (p : Polynomial ℕ) : NatPolynomialBound fun n => p.eval n := ⟨p, fun _ => rfl⟩

theorem hornT (cs : List ℕ) : ∀ {A : ℕ → ℕ}, NatPolynomialBound A → NatPolynomialBound fun n => Cslib.Complexity.CookLevin.Precompute.hornT cs n (A n) := by
  induction cs with
  | nil => intro A _; exact const 0
  | cons a cs ih =>
      intro A hA
      have hstep : NatPolynomialBound fun n => hornStep (A n) n := by
        unfold hornStep
        exact ((((((hA.mul ((const 2).mul id |>.add (const 3))).add hA).add (const 2)).add
          (hA.add (const 1))).add ((hA.mul id).add (const 1))).add (const 1))
      exact hstep.add (ih ((hA.mul id).add (const a)))

end NatPolynomialBound
end OMA.Padding

/- New padding-transducer construction. The helper excerpts above are attributed
to PR #7436; the definitions and proofs below concern the separate R2.H2 target. -/
namespace OMA.Padding
open Turing Function ComplexityTheory BitstringEncoding
open MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open Cslib.Complexity.CookLevin.CounterView Cslib.Complexity.CookLevin.Precompute
noncomputable section

@[simp] theorem bool_flag_tag (b : Bool) : Flag.tag (σ := Bool) b = b := rfl

inductive Counter | N | A | Q | AD | TMP
  deriving DecidableEq

instance Counter.instFintypeEnumFix : Fintype Counter where
  elems := ⟨↑[Counter.N, Counter.A, Counter.Q, Counter.AD, Counter.TMP], by decide⟩
  complete := fun c => by cases c <;> decide

def counts (n a : ℕ) : Counter → ℕ
  | .N => n
  | .A => a
  | _ => 0

@[simp] theorem counts_N (n a : ℕ) : counts n a .N = n := rfl
@[simp] theorem counts_A (n a : ℕ) : counts n a .A = a := rfl
@[simp] theorem counts_Q (n a : ℕ) : counts n a .Q = 0 := rfl
@[simp] theorem counts_AD (n a : ℕ) : counts n a .AD = 0 := rfl
@[simp] theorem counts_TMP (n a : ℕ) : counts n a .TMP = 0 := rfl
@[simp] theorem counts_zero : counts 0 0 = fun _ => 0 := by
  funext c; cases c <;> rfl

abbrev HLabel (p : Polynomial ℕ) := Option (Fin (coeffs p).length × HW)

def hlabel (p : Polynomial ℕ) (i : ℕ) (s : HW) : HLabel p :=
  if h : i < (coeffs p).length then some (⟨i, h⟩, s) else none

def hprog (p : Polynomial ℕ) : HLabel p → TM2.Stmt (SΓ Counter) (HLabel p) Bool
  | none => .halt
  | some (i, s) => hornS .N .A .Q .AD .TMP (coeffs p)[i.val]
      (hlabel p i.val) (hlabel p (i.val + 1) (.mul .head)) s

theorem hprog_run (p : Polynomial ℕ) (n : ℕ) (v : Bool) (o : List Bool) :
    ∃ v', Run (hprog p) (hornT (coeffs p) n 0)
      ⟨some (hlabel p 0 (.mul .head)), v, st (counts n 0) o⟩
      ⟨some none, v', st (counts n (p.eval n)) o⟩ := by
  have hp : ∀ i (hi : i < (coeffs p).length) s, hprog p (hlabel p i s) =
      hornS .N .A .Q .AD .TMP (coeffs p)[i] (hlabel p i)
        (if i + 1 < (coeffs p).length then hlabel p (i + 1) (.mul .head) else none) s := by
    intro i hi s
    simp only [hlabel, dif_pos hi, hprog]
    split_ifs <;> rfl
  obtain ⟨v', hr⟩ := horner_run (M := hprog p) (coeffs p) hp (by decide)
    (coeffs p).length 0 (by omega) (counts n 0) rfl rfl rfl v o
  have hf : update (counts n 0) Counter.A (p.eval n) = counts n (p.eval n) := by
    funext c; cases c <;> simp [counts]
  have hstart : (if 0 < (coeffs p).length then hlabel p 0 (.mul .head) else none) =
      hlabel p 0 (.mul .head) := by
    by_cases h : 0 < (coeffs p).length <;> simp [hlabel, h]
  simp only [List.drop_zero, show counts n 0 Counter.N = n from rfl,
    show counts n 0 Counter.A = 0 from rfl, hornVal_coeffs] at hr
  rw [hf, hstart] at hr
  exact ⟨v', hr⟩

inductive Stack | inp | saved | work (k : SK Counter)
  deriving DecidableEq, Fintype

abbrev Gamma : Stack → Type
  | .inp => Bool
  | .saved => Bool
  | .work k => SΓ Counter k

def sview (F : Counter → ℕ) (i r o : List Bool) : ∀ k, List (Gamma k)
  | .inp => i
  | .saved => r
  | .work k => st F o k

def embedding : SEmb (SΓ Counter) Gamma where
  e := Stack.work
  inj := fun _ _ h => Stack.work.inj h
  ι _ := Equiv.refl _

theorem embedding_agree (F : Counter → ℕ) (i r o : List Bool) :
    Agree embedding (st F o) (sview F i r o) := by
  intro k
  change st F o k = List.map id (st F o k)
  exact (List.map_id _).symm

theorem lift_run {L L' : Type} {P : L → TM2.Stmt (SΓ Counter) L Bool}
    {M : L' → TM2.Stmt Gamma L' Bool} {φ : L → L'}
    (hM : Embeds embedding φ P M) {t : ℕ} {l l' : L} {v v' : Bool}
    {F F' : Counter → ℕ} {o o' i r : List Bool}
    (hr : Run P t ⟨some l, v, st F o⟩ ⟨some l', v', st F' o'⟩) :
    Run M t ⟨some (φ l), v, sview F i r o⟩
      ⟨some (φ l'), v', sview F' i r o'⟩ := by
  obtain ⟨T, hrun, ha, hf⟩ := run_embed φ hM t (some l) v (st F o) l' v'
    (st F' o') (sview F i r o) hr (embedding_agree F i r o)
  have ht : T = sview F' i r o' := by
    funext k
    cases k with
    | inp => exact hf .inp (by intro k; simp [embedding])
    | saved => exact hf .saved (by intro k; simp [embedding])
    | work k =>
      have hk := ha k
      change T (.work k) = List.map id (st F' o' k) at hk
      change T (.work k) = st F' o' k
      simpa only [List.map_id] using hk
  simpa [ht] using hrun

def enc (x : List Bool) : List Bool := x.flatMap fun b => [true, b, false]

theorem enc_eq (x : List Bool) : enc x = bitEncode x := by
  change _ = (((x.map bitEncode).map delimit).flatten)
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [enc, List.flatMap_cons, List.map_cons, List.flatten_cons] at ih ⊢
    rw [← ih]; rfl

@[simp] theorem enc_nil : enc [] = [] := rfl
@[simp] theorem enc_cons (b : Bool) (x : List Bool) :
    enc (b :: x) = true :: b :: false :: enc x := rfl
@[simp] theorem enc_append (x y : List Bool) : enc (x ++ y) = enc x ++ enc y := by
  simp only [enc, List.flatMap_append]
@[simp] theorem enc_length (x : List Bool) : (enc x).length = 3 * x.length := by
  induction x with
  | nil => simp
  | cons b x ih => simp [ih]; omega

theorem rep_enc_true (n : ℕ) : rep [true, true, false] n = enc (List.replicate n true) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ, List.replicate_succ, enc_cons, ih]; rfl

inductive Label (p q : Polynomial ℕ)
  | scan
  | hq (l : HLabel q)
  | sep
  | hp (l : HLabel p)
  | xend
  | restore
  | pre
  | drain
  | finish
  deriving DecidableEq, Fintype

def program (code : List Bool) (p q : Polynomial ℕ) : Label p q → TM2.Stmt Gamma (Label p q) Bool
  | .scan => .pop .inp (fun _ b => b.isSome) <| .branch id
      (.pop .inp (fun _ b => b.getD false) <|
        .pop .inp (fun v _ => v) <| .push .saved id <|
        .push (.work (.c .N)) (fun _ => ()) <| .goto fun _ => .scan)
      (.goto fun _ => .hq (hlabel q 0 (.mul .head)))
  | .hq (some l) => mapS embedding Label.hq (hprog q (some l))
  | .hq none => xferE (.work (.c .A)) (.work .out) [true, true, false] (.hq none) .sep
  | .sep => emitR (.work .out) [true, false, false] (.hp (hlabel p 0 (.mul .head)))
  | .hp (some l) => mapS embedding Label.hp (hprog p (some l))
  | .hp none => xferE (.work (.c .A)) (.work .out) [true, true, false] (.hp none) .xend
  | .xend => emitR (.work .out) [true, false, false] .restore
  | .restore => .peek .saved (fun _ b => b.isSome) <| .branch id
      (.pop .saved (fun _ b => b.getD false) <|
        .push (.work .out) (fun _ => false) <| .push (.work .out) id <|
        .push (.work .out) (fun _ => true) <| .push (.work .out) (fun _ => false) <|
        .push (.work .out) (fun _ => true) <| .push (.work .out) (fun _ => true) <|
        .goto fun _ => .restore)
      (.goto fun _ => .pre)
  | .pre => emitR (.work .out) (enc (delimit code)) .drain
  | .drain => xfer (.work (.c .N)) [] .drain .finish
  | .finish => .load (fun _ => false) .halt

theorem embeds_q (code : List Bool) (p q : Polynomial ℕ) :
    Embeds embedding Label.hq (hprog q) (program code p q) := by
  intro l; cases l with
  | none => exact Or.inr rfl
  | some l => exact Or.inl rfl

theorem embeds_p (code : List Bool) (p q : Polynomial ℕ) :
    Embeds embedding Label.hp (hprog p) (program code p q) := by
  intro l; cases l with
  | none => exact Or.inr rfl
  | some l => exact Or.inl rfl

@[simp] theorem stacks_inp (F : Counter → ℕ) (i r o : List Bool) :
    sview F i r o .inp = i := rfl
@[simp] theorem stacks_saved (F : Counter → ℕ) (i r o : List Bool) :
    sview F i r o .saved = r := rfl
@[simp] theorem stacks_out (F : Counter → ℕ) (i r o : List Bool) :
    sview F i r o (.work .out) = o := rfl
@[simp] theorem stacks_counter (F : Counter → ℕ) (i r o : List Bool) (c : Counter) :
    sview F i r o (.work (.c c)) = cnt () (F c) := rfl

@[simp] theorem update_stacks_inp (F : Counter → ℕ) (i r o l : List Bool) :
    update (sview F i r o) .inp l = sview F l r o := by
  funext k; cases k <;> simp [sview]
@[simp] theorem update_stacks_saved (F : Counter → ℕ) (i r o l : List Bool) :
    update (sview F i r o) .saved l = sview F i l o := by
  funext k; cases k <;> simp [sview]
@[simp] theorem update_stacks_out (F : Counter → ℕ) (i r o l : List Bool) :
    update (sview F i r o) (.work .out) l = sview F i r l := by
  funext k; cases k with
  | inp => simp [sview]
  | saved => simp [sview]
  | work k => cases k <;> simp [sview, st]
@[simp] theorem update_stacks_counter (F : Counter → ℕ) (i r o : List Bool)
    (c : Counter) (n : ℕ) :
    update (sview F i r o) (.work (.c c)) (cnt () n) = sview (update F c n) i r o := by
  funext k; cases k with
  | inp => simp [sview]
  | saved => simp [sview]
  | work k =>
    cases k with
    | out => simp [sview, st]
    | c d =>
      by_cases h : d = c
      · subst d; simp [sview, st]
      · simp [sview, st, h]

@[simp] theorem update_stacks_counter_nil (F : Counter → ℕ) (i r o : List Bool)
    (c : Counter) :
    update (sview F i r o) (.work (.c c)) [] = sview (update F c 0) i r o :=
  update_stacks_counter F i r o c 0

@[simp] theorem update_counts_N (n a m : ℕ) : update (counts n a) Counter.N m = counts m a := by
  funext c; cases c <;> simp [counts]
@[simp] theorem update_counts_A (n a m : ℕ) : update (counts n a) Counter.A m = counts n m := by
  funext c; cases c <;> simp [counts]

theorem scan_run (code : List Bool) (p q : Polynomial ℕ) (x : List Bool) :
    ∀ (n a : ℕ) (v : Bool) (r o : List Bool),
      Run (program code p q) (x.length + 1)
        ⟨some .scan, v, sview (counts n a) (enc x) r o⟩
        ⟨some (.hq (hlabel q 0 (.mul .head))), false,
          sview (counts (n + x.length) a) [] (x.reverse ++ r) o⟩ := by
  induction x with
  | nil =>
    intro n a v r o
    exact Run.single (by simp [program, TM2.stepAux])
  | cons b x ih =>
    intro n a v r o
    have hs : TM2.step (program code p q)
        ⟨some .scan, v, sview (counts n a) (enc (b :: x)) r o⟩ =
        some ⟨some .scan, b, sview (counts (n + 1) a) (enc x) (b :: r) o⟩ := by
      simp [TM2.step, program, TM2.stepAux, ← cnt_succ]
      all_goals
        simpa only [update_counts_N] using
          (update_stacks_counter (counts n a) (enc x) (b :: r) o Counter.N (n + 1))
    have h := Run.head hs (ih (n + 1) a b (b :: r) o)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

theorem unary_run {p q : Polynomial ℕ} {code : List Bool} {self next : Label p q}
    (h : program code p q self =
      xferE (.work (.c .A)) (.work .out) [true, true, false] self next)
    (n a : ℕ) (v : Bool) (i r o : List Bool) :
    Run (program code p q) (a + 1) ⟨some self, v, sview (counts n a) i r o⟩
      ⟨some next, false, sview (counts n 0) i r (enc (List.replicate a true) ++ o)⟩ := by
  have hr := xferE_run h (by decide) () a v (sview (counts n a) i r o) rfl
  rw [update_stacks_counter_nil (counts n a) i r o Counter.A] at hr
  simpa only [bool_flag_tag,
    stacks_out, update_stacks_out, update_counts_A, rep_enc_true] using hr

theorem emit_run_full {p q : Polynomial ℕ} {code : List Bool} {self next : Label p q}
    {ys : List Bool} (h : program code p q self = emitR (.work .out) ys next)
    (F : Counter → ℕ) (v : Bool) (i r o : List Bool) :
    Run (program code p q) 1 ⟨some self, v, sview F i r o⟩
      ⟨some next, v, sview F i r (ys ++ o)⟩ := by
  simpa only [stacks_out, update_stacks_out] using emitR_run h v (sview F i r o)

def dbits (x : List Bool) : List Bool := x.flatMap fun b => [true, b]

@[simp] theorem dbits_append (x y : List Bool) : dbits (x ++ y) = dbits x ++ dbits y := by
  simp only [dbits, List.flatMap_append]

theorem delimit_dbits (x : List Bool) : delimit x = dbits x ++ [false] := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [delimit, dbits, ih]

theorem restore_run (code : List Bool) (p q : Polynomial ℕ) (r : List Bool) :
    ∀ (F : Counter → ℕ) (v : Bool) (i o : List Bool),
      Run (program code p q) (r.length + 1)
        ⟨some .restore, v, sview F i r o⟩
        ⟨some .pre, false, sview F i [] (enc (dbits r.reverse) ++ o)⟩ := by
  induction r with
  | nil =>
    intro F v i o
    exact Run.single (by simp [program, TM2.stepAux, dbits])
  | cons b r ih =>
    intro F v i o
    have hs : TM2.step (program code p q) ⟨some .restore, v, sview F i (b :: r) o⟩ =
        some ⟨some .restore, b, sview F i r (enc [true, b] ++ o)⟩ := by
      simp [TM2.step, program, TM2.stepAux, enc]
    have h := Run.head hs (ih F b i (enc [true, b] ++ o))
    simpa [List.reverse_cons, List.append_assoc, dbits_append, enc_append,
      show dbits [b] = [true, b] from rfl] using h

theorem drain_run (code : List Bool) (p q : Polynomial ℕ) (n a : ℕ) (v : Bool)
    (i r o : List Bool) :
    Run (program code p q) (n + 1) ⟨some .drain, v, sview (counts n a) i r o⟩
      ⟨some .finish, false, sview (counts 0 a) i r o⟩ := by
  have h := xfer_run (M := program code p q) (self := .drain) (next := .finish)
    (k := .work (.c .N)) (ps := []) rfl (by simp [List.NodupKeys]) (by simp)
    () n v (sview (counts n a) i r o) rfl
  rw [update_stacks_counter_nil (counts n a) i r o Counter.N] at h
  simpa only [bool_flag_tag, addU_nil, update_counts_N] using h

def padded (code x : List Bool) (p q : Polynomial ℕ) : List Bool :=
  delimit code ++ delimit x ++ List.replicate (p.eval x.length) true ++ [false] ++
    List.replicate (q.eval x.length) true

def bound (p q : Polynomial ℕ) (n : ℕ) : ℕ :=
  3 * n + hornT (coeffs q) n 0 + hornT (coeffs p) n 0 + q.eval n + p.eval n + 9

theorem program_run (code x : List Bool) (p q : Polynomial ℕ) :
    Run (program code p q) (bound p q x.length)
      ⟨some .scan, false, sview (counts 0 0) (enc x) [] []⟩
      ⟨none, false, sview (counts 0 0) [] [] (enc (padded code x p q))⟩ := by
  have r1 := scan_run code p q x 0 0 false [] []
  simp only [Nat.zero_add, List.append_nil] at r1
  obtain ⟨vq, r2⟩ := hprog_run q x.length false []
  have r2' := lift_run (i := []) (r := x.reverse) (embeds_q code p q) r2
  have r3 := unary_run (code := code) (p := p) (q := q) (self := .hq none)
    (next := .sep) rfl x.length (q.eval x.length) vq [] x.reverse []
  simp only [List.append_nil] at r3
  have r4 := emit_run_full (code := code) (p := p) (q := q) (self := .sep)
    (next := .hp (hlabel p 0 (.mul .head))) rfl (counts x.length 0) false [] x.reverse
    (enc (List.replicate (q.eval x.length) true))
  let oq := [true, false, false] ++ enc (List.replicate (q.eval x.length) true)
  obtain ⟨vp, r5⟩ := hprog_run p x.length false oq
  have r5' := lift_run (i := []) (r := x.reverse) (embeds_p code p q) r5
  have r6 := unary_run (code := code) (p := p) (q := q) (self := .hp none)
    (next := .xend) rfl x.length (p.eval x.length) vp [] x.reverse oq
  let op := enc (List.replicate (p.eval x.length) true) ++ oq
  have r7 := emit_run_full (code := code) (p := p) (q := q) (self := .xend)
    (next := .restore) rfl (counts x.length 0) false [] x.reverse op
  have r8 := restore_run code p q x.reverse (counts x.length 0) false []
    ([true, false, false] ++ op)
  simp only [List.reverse_reverse, List.length_reverse] at r8
  let ox := enc (dbits x) ++ ([true, false, false] ++ op)
  have r9 := emit_run_full (code := code) (p := p) (q := q) (self := .pre)
    (next := .drain) rfl (counts x.length 0) false [] [] ox
  have r10 := drain_run code p q x.length 0 false [] [] (enc (delimit code) ++ ox)
  have r11 : Run (program code p q) 1
      ⟨some .finish, false, sview (counts 0 0) [] [] (enc (delimit code) ++ ox)⟩
      ⟨none, false, sview (counts 0 0) [] [] (enc (delimit code) ++ ox)⟩ :=
    Run.single rfl
  have hr := r1.trans (r2'.trans (r3.trans (r4.trans (r5'.trans (r6.trans
    (r7.trans (r8.trans (r9.trans (r10.trans r11)))))))))
  have hout : enc (delimit code) ++ ox = enc (padded code x p q) := by
    simp [ox, op, oq, padded, delimit_dbits, enc_append, List.append_assoc]
  rw [hout] at hr
  exact hr.of_eq (by simp only [bound]; omega)

theorem bound_poly (p q : Polynomial ℕ) : NatPolynomialBound (bound p q) := by
  unfold bound
  exact ((((((NatPolynomialBound.const 3).mul NatPolynomialBound.id).add
    (NatPolynomialBound.hornT (coeffs q) (NatPolynomialBound.const 0))).add
    (NatPolynomialBound.hornT (coeffs p) (NatPolynomialBound.const 0))).add
    (NatPolynomialBound.eval q)).add (NatPolynomialBound.eval p)).add
    (NatPolynomialBound.const 9)

-- This elementary monotonicity lemma is also adapted from PR #7436.
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

def machine (code : List Bool) (p q : Polynomial ℕ) : FinTM2 where
  K := Stack
  k₀ := .inp
  k₁ := .work .out
  Γ := Gamma
  Λ := Label p q
  main := .scan
  σ := Bool
  initialState := false
  m := program code p q

theorem machine_init (code x : List Bool) (p q : Polynomial ℕ) :
    initList (machine code p q) (enc x) =
      ⟨some .scan, false, sview (counts 0 0) (enc x) [] []⟩ := by
  unfold initList machine
  congr 1
  funext k
  cases k with
  | inp => simp [sview]
  | saved => simp [sview]
  | work k => cases k <;> simp [sview, st]

theorem machine_halt (code x : List Bool) (p q : Polynomial ℕ) :
    haltList (machine code p q) (enc x) =
      ⟨none, false, sview (counts 0 0) [] [] (enc x)⟩ := by
  unfold haltList machine
  congr 1
  funext k
  cases k with
  | inp => simp [sview]
  | saved => simp [sview]
  | work k => cases k <;> simp [sview, st]

theorem padding_polytime (code : List Bool) (p q : Polynomial ℕ) :
    IsPolyTime (fun x => padded code x p q) := by
  obtain ⟨B, hB⟩ := bound_poly p q
  refine ⟨{
    tm := machine code p q
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := B
    outputsFun := ?_ }⟩
  intro x
  change TM2OutputsInTime (machine code p q) (List.map id (bitEncode x))
    (some (List.map id (bitEncode (padded code x p q)))) (B.eval (bitEncode x).length)
  dsimp only [machine]
  simp only [List.map_id, ← enc_eq]
  have hr := program_run code x p q
  have hi := machine_init code x p q
  have ho := machine_halt code (padded code x p q) p q
  unfold machine at hi ho
  rw [← hi, ← ho] at hr
  refine {
    steps := bound p q x.length
    evals_in_steps := ?_
    steps_le_m := ?_ }
  · dsimp only [FinTM2.Cfg, Option.map]
    simpa only [Run, FinTM2.step, FinTM2.Cfg] using hr
  · rw [hB]
    apply eval_mono
    rw [enc_length]
    omega

end
end OMA.Padding

theorem OMA.solution :
    OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R2.H2 := by
  intro code p q
  exact OMA.Padding.padding_polytime code p q



