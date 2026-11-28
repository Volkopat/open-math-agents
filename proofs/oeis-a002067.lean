import OMAStatements.S_oeis_a002067

/-
Copyright 2026 The Omega Institute

Adapted from CallanA002067Dyck.lean and CallanA002067Hafnian.lean at commit
687878cf845802aba2692eeb304cb960d1306431:
https://github.com/the-omega-institute/trureturing/tree/687878cf845802aba2692eeb304cb960d1306431/D5/S3/Combinatorics/PerfectMatchings

Changes: extract the polynomial recurrence and matching argument, remove the
unneeded Dyck and graph constructions, and prove the bridge from partial
involutions to this statement's finite sum over fixed-point-free permutations.

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

   Copyright 2026 The Omega Institute

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

namespace CallanProof

open Finset Polynomial
open scoped BigOperators Classical

/-- The NAME recurrence, with its initial term from the source's terms and program.
The source index n >= 1 is written n + 1, so each summand has k <= n. -/
def IsSourceSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ,
    a (n + 1) = ∑ k ∈ Finset.range (n + 1),
      Nat.choose (2 * (n + 1)) (2 * k) * a k * a (n - k)

theorem source_unique {a b : ℕ → ℕ}
    (ha : IsSourceSequence a) (hb : IsSourceSequence b) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ha.1.trans hb.1.symm
    | succ n =>
      rw [ha.2 n, hb.2 n]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      rw [ih k hk', ih (n - k) (by omega)]

noncomputable def walkPoly : ℕ → Polynomial ℕ
  | 0 => 1
  | n + 1 => (walkPoly n).derivative + C (n + 1) * X * walkPoly n

private theorem truncated_pascal {R : Type*} [CommSemiring R]
    (f : ℕ → R) (hf : f 0 = 1) (n : ℕ) :
    (∑ k ∈ range (n + 2), ((n + 3).choose k : R) * f k * f (n + 1 - k)) =
      (n + 2 : R) * f (n + 1) +
        ∑ k ∈ range (n + 1), ((n + 2).choose k : R) *
          (f (k + 1) * f (n - k) + f k * f (n + 1 - k)) := by
  have hend : (n + 2).choose (n + 1) = n + 2 := by
    exact Nat.choose_succ_self_right (n + 1)
  have hs :
      (∑ k ∈ range (n + 1), ((n + 2).choose (k + 1) : R) * f (k + 1) * f (n - k)) +
        f (n + 1) =
      (∑ k ∈ range (n + 1), ((n + 2).choose k : R) * f k * f (n + 1 - k)) +
        (n + 2 : R) * f (n + 1) := by
    rw [sum_range_succ (f := fun k => ((n + 2).choose (k + 1) : R) *
      f (k + 1) * f (n - k))]
    rw [sum_range_succ' (f := fun k => ((n + 2).choose k : R) *
      f k * f (n + 1 - k))]
    simp only [Nat.sub_self, hf, mul_one, hend, Nat.cast_add,
      Nat.cast_one, Nat.choose_zero_right, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
    ring
  rw [sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, hf, Nat.sub_zero]
  have pascal (k : ℕ) : ((n + 3).choose (k + 1) : R) =
      ((n + 2).choose k : R) + ((n + 2).choose (k + 1) : R) := by
    rw [show n + 3 = (n + 2) + 1 by omega, Nat.choose_succ_succ', Nat.cast_add]
  simp only [pascal, add_mul, sum_add_distrib]
  simp only [Nat.add_sub_add_right]
  calc
    _ = (∑ k ∈ range (n + 1), ((n + 2).choose k : R) * f (k + 1) * f (n - k)) +
        ((∑ k ∈ range (n + 1), ((n + 2).choose (k + 1) : R) *
          f (k + 1) * f (n - k)) + f (n + 1)) := by ring
    _ = _ := by rw [hs]; simp_rw [mul_add, sum_add_distrib]; ring

private theorem derivative_convolution (n : ℕ) :
    (walkPoly (n + 1)).derivative =
      ∑ k ∈ range (n + 1), C ((n + 2).choose k) * walkPoly k * walkPoly (n - k) := by
  induction n with
  | zero => simp [walkPoly]
  | succ n ih =>
    let S : Polynomial ℕ := ∑ k ∈ range (n + 1),
      C ((n + 2).choose k) * walkPoly k * walkPoly (n - k)
    have hs : S.derivative + C (n + 2) * X * S =
        ∑ k ∈ range (n + 1), C ((n + 2).choose k) *
          (walkPoly (k + 1) * walkPoly (n - k) +
            walkPoly k * walkPoly (n + 1 - k)) := by
      dsimp [S]
      rw [derivative_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ n := mem_range_succ_iff.mp hk
      have hn : n + 1 - k = n - k + 1 := by exact Nat.sub_add_comm hk'
      have hc : C (n + 2) = C (k + 1) + C (n - k + 1) := by
        rw [← C_add]
        congr 1
        omega
      rw [hn, walkPoly, walkPoly]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add]
      rw [hc]
      ring
    have hd : (walkPoly (n + 2)).derivative =
        C (n + 2) * walkPoly (n + 1) +
          (S.derivative + C (n + 2) * X * S) := by
      rw [walkPoly]
      simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
        zero_mul, zero_add, mul_one]
      change (walkPoly (n + 1)).derivative.derivative +
        (C (n + 2) * walkPoly (n + 1) +
          C (n + 2) * X * (walkPoly (n + 1)).derivative) = _
      rw [ih]
      dsimp [S]
      ring
    rw [show n + 1 + 1 = n + 2 by omega, hd, hs]
    have hp := truncated_pascal walkPoly (by rfl) n
    convert hp.symm using 1 <;> simp only [← C_eq_natCast, Nat.cast_id, Nat.add_assoc, C_add, C_ofNat]

private theorem walkPoly_coeff_parity (n k : ℕ) (h : (n + k) % 2 = 1) :
    (walkPoly n).coeff k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => simp [walkPoly, coeff_one]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [walkPoly, coeff_add, coeff_derivative, mul_one,
        mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero]
      simpa only [Nat.zero_add, Nat.cast_zero, zero_add, mul_one] using ih 1 (by omega)
    | succ k =>
      simp only [walkPoly, coeff_add, coeff_derivative, mul_assoc,
        coeff_C_mul, coeff_X_mul]
      rw [ih (k + 1 + 1) (by omega), ih k (by omega)]
      simp

private theorem polyConst_odd (n : ℕ) : (walkPoly (2 * n + 1)).eval 0 = 0 := by
  simpa only [coeff_zero_eq_eval_zero] using walkPoly_coeff_parity (2 * n + 1) 0 (by omega)

private theorem sum_even_only {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (hf : ∀ n, f (2 * n + 1) = 0) (n : ℕ) :
    (∑ k ∈ range (2 * n + 1), f k) = ∑ k ∈ range (n + 1), f (2 * k) := by
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => 2 * a) ?_ ?_ ?_ ?_
  · intro a ha hfa
    exact mem_range.mpr (by have := mem_range.mp ha; omega)
  · intro a ha hfa b hb hfb he
    omega
  · intro b hb hfb
    have heven : b % 2 = 0 := by
      by_contra h
      have hodd : b = 2 * (b / 2) + 1 := by omega
      rw [hodd, hf] at hfb
      exact hfb rfl
    have he : 2 * (b / 2) = b := by omega
    refine ⟨b / 2, mem_range.mpr (by have := mem_range.mp hb; omega), ?_, he⟩
    simpa only [he] using hfb
  · intro a ha hfa
    rfl

private theorem polyConst_convolution (r : ℕ) :
    (walkPoly (r + 2)).eval 0 = ∑ k ∈ range (r + 1),
      (r + 2).choose k * (walkPoly (k)).eval 0 * (walkPoly (r - k)).eval 0 := by
  change (walkPoly (r + 1 + 1)).eval 0 = _
  rw [walkPoly]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_mul, add_zero]
  rw [derivative_convolution]
  simp only [eval_finsetSum, eval_mul, eval_C]

private theorem polyConst_source_recurrence (n : ℕ) :
    (walkPoly (2 * (n + 1))).eval 0 = ∑ k ∈ range (n + 1),
      (2 * (n + 1)).choose (2 * k) * (walkPoly (2 * k)).eval 0 * (walkPoly (2 * (n - k))).eval 0 := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, polyConst_convolution]
  rw [sum_even_only (hf := fun m => by rw [polyConst_odd]; simp)]
  apply sum_congr rfl
  intro k hk
  rw [show 2 * n - 2 * k = 2 * (n - k) by omega]

theorem poly_is_source : IsSourceSequence (fun n => (walkPoly (2 * n)).eval 0) := by
  refine ⟨?_, polyConst_source_recurrence⟩
  simp [walkPoly]

private noncomputable def extendInvFun {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) :
    Fin (r + 1) → Fin (r + 1) :=
  Fin.lastCases (q.elim (Fin.last r) (fun i => i.val.castSucc))
    (fun j => if ∃ i, q = some i ∧ j = i.val then Fin.last r else (f.val j).castSucc)

private theorem extendInvFun_none_last {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    extendInvFun f none (Fin.last r) = Fin.last r := by simp [extendInvFun]

private theorem extendInvFun_none_castSucc {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (j : Fin r) :
    extendInvFun f none j.castSucc = (f.val j).castSucc := by simp [extendInvFun]

private theorem extendInvFun_some_last {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) :
    extendInvFun f (some i) (Fin.last r) = i.val.castSucc := by simp [extendInvFun]

private theorem extendInvFun_some_castSucc {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) (j : Fin r) :
    extendInvFun f (some i) j.castSucc =
      if j = i.val then Fin.last r else (f.val j).castSucc := by simp [extendInvFun]

private theorem extendInvFun_involutive {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) :
    Function.Involutive (extendInvFun f q) := by
  intro x
  induction x using Fin.lastCases with
  | last =>
    cases q with
    | none => simp [extendInvFun_none_last]
    | some i => simp [extendInvFun_some_last, extendInvFun_some_castSucc]
  | cast j =>
    cases q with
    | none => simp [extendInvFun_none_castSucc, f.property j]
    | some i =>
      by_cases hj : j = i.val
      · subst j
        simp [extendInvFun_some_castSucc, extendInvFun_some_last]
      · have hf : f.val j ≠ i.val := by
          intro he
          have he' := congrArg f.val he
          rw [f.property j, i.property] at he'
          exact hj he'
        simp [extendInvFun_some_castSucc, hj, hf, f.property j]

private noncomputable abbrev extendInv {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f} :=
  ⟨extendInvFun f q, extendInvFun_involutive f q⟩

private noncomputable def dropInvFun {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) (j : Fin r) : Fin r :=
  if h : g.val j.castSucc = Fin.last r then j
  else ⟨(g.val j.castSucc).val, by
    have hv := (g.val j.castSucc).isLt
    have hn : (g.val j.castSucc).val ≠ r := by
      intro he; exact h (Fin.ext he)
    omega⟩

private theorem dropInvFun_last {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) (j : Fin r)
    (h : g.val j.castSucc = Fin.last r) : dropInvFun g j = j := by
  simp [dropInvFun, h]

private theorem dropInvFun_castSucc {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) (j : Fin r)
    (h : g.val j.castSucc ≠ Fin.last r) :
    (dropInvFun g j).castSucc = g.val j.castSucc := by
  apply Fin.ext
  simp [dropInvFun, h]

private theorem dropInvFun_involutive {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) :
    Function.Involutive (dropInvFun g) := by
  intro j
  by_cases hj : g.val j.castSucc = Fin.last r
  · rw [dropInvFun_last g j hj, dropInvFun_last g j hj]
  · have he := dropInvFun_castSucc g j hj
    have hh : g.val (dropInvFun g j).castSucc = j.castSucc := by
      rw [he, g.property]
    have hn : g.val (dropInvFun g j).castSucc ≠ Fin.last r := by
      rw [hh]; exact Fin.castSucc_ne_last j
    have ht := dropInvFun_castSucc g (dropInvFun g j) hn
    rw [hh] at ht
    exact Fin.castSucc_inj.mp ht

private noncomputable abbrev dropInv {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) : {f : Fin r → Fin r // Function.Involutive f} :=
  ⟨dropInvFun g, dropInvFun_involutive g⟩

private noncomputable def partner {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) : Option ({i : _ // (dropInv g).val i = i}) :=
  if h : g.val (Fin.last r) = Fin.last r then none
  else some ⟨⟨(g.val (Fin.last r)).val, by
      have hv := (g.val (Fin.last r)).isLt
      have hn : (g.val (Fin.last r)).val ≠ r := by
        intro he; exact h (Fin.ext he)
      omega⟩, by
    apply dropInvFun_last
    have hg := g.property (Fin.last r)
    convert hg using 1
    apply congrArg g.val
    apply Fin.ext
    rfl⟩

private theorem drop_extend {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (q : Option ({i : _ // (f).val i = i})) :
    dropInv (extendInv f q) = f := by
  apply Subtype.ext
  funext j
  cases q with
  | none =>
    apply Fin.castSucc_inj.mp
    calc
      (dropInvFun (extendInv f none) j).castSucc =
          (extendInv f none).val j.castSucc := dropInvFun_castSucc _ _ (by
            simp [extendInv, extendInvFun_none_castSucc, Fin.castSucc_ne_last])
      _ = (f.val j).castSucc := extendInvFun_none_castSucc f j
  | some i =>
    by_cases hj : j = i.val
    · subst j
      change dropInvFun (extendInv f (some i)) i.val = f.val i.val
      rw [dropInvFun_last _ _ (by simp [extendInv, extendInvFun_some_castSucc]), i.property]
    · apply Fin.castSucc_inj.mp
      calc
        (dropInvFun (extendInv f (some i)) j).castSucc =
            (extendInv f (some i)).val j.castSucc := dropInvFun_castSucc _ _ (by
              simp [extendInv, extendInvFun_some_castSucc, hj, Fin.castSucc_ne_last])
        _ = (f.val j).castSucc := by simp [extendInv, extendInvFun_some_castSucc, hj]

private theorem partner_image {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) :
    (partner g).elim (Fin.last r) (fun i => i.val.castSucc) = g.val (Fin.last r) := by
  unfold partner
  split
  · rename_i h
    exact h.symm
  · simp only [Option.elim_some]
    apply Fin.ext
    rfl

private theorem extend_drop {r : ℕ} (g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f}) :
    extendInv (dropInv g) (partner g) = g := by
  apply Subtype.ext
  funext x
  have he := partner_image g
  induction x using Fin.lastCases with
  | last => simpa only [extendInv, extendInvFun, Fin.lastCases_last] using he
  | cast j =>
    cases hq : partner g with
    | none =>
      rw [hq] at he
      simp only [Option.elim_none] at he
      have hn : g.val j.castSucc ≠ Fin.last r := by
        intro hh
        have ht := congrArg g.val hh
        rw [g.property, ← he] at ht
        exact Fin.castSucc_ne_last j ht
      change extendInvFun (dropInv g) none j.castSucc = g.val j.castSucc
      rw [extendInvFun_none_castSucc]
      exact dropInvFun_castSucc g j hn
    | some i =>
      rw [hq] at he
      simp only [Option.elim_some] at he
      change extendInvFun (dropInv g) (some i) j.castSucc = g.val j.castSucc
      rw [extendInvFun_some_castSucc]
      by_cases hj : j = i.val
      · rw [if_pos hj, hj, he, g.property]
      · rw [if_neg hj]
        apply dropInvFun_castSucc
        intro hh
        have ht := congrArg g.val hh
        rw [g.property, ← he] at ht
        exact hj (Fin.castSucc_inj.mp ht)

private theorem extend_injective (r : ℕ) :
    Function.Injective (fun s : (Σ f : {f : Fin r → Fin r // Function.Involutive f}, Option ({i : _ // (f).val i = i})) => extendInv s.1 s.2) := by
  rintro ⟨f, q⟩ ⟨f', q'⟩ h
  have hf := congrArg dropInv h
  simp only [drop_extend] at hf
  cases hf
  have he := congrArg (fun g : {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f} => g.val (Fin.last r)) h
  have hq : q = q' := by
    cases q with
    | none =>
      cases q' with
      | none => rfl
      | some i =>
        simp only [extendInv, extendInvFun_none_last, extendInvFun_some_last] at he
        exact False.elim ((Fin.castSucc_ne_last i.val) he.symm)
    | some i =>
      cases q' with
      | none =>
        simp only [extendInv, extendInvFun_none_last, extendInvFun_some_last] at he
        exact False.elim ((Fin.castSucc_ne_last i.val) he)
      | some i' =>
        simp only [extendInv, extendInvFun_some_last] at he
        have hi : i = i' := Subtype.ext (Fin.castSucc_inj.mp he)
        subst i'
        rfl
  subst q'
  rfl

private noncomputable def invSuccEquiv (r : ℕ) :
    (Σ f : {f : Fin r → Fin r // Function.Involutive f}, Option ({i : _ // (f).val i = i})) ≃ {f : Fin (r + 1) → Fin (r + 1) // Function.Involutive f} :=
  Equiv.ofBijective (fun s => extendInv s.1 s.2)
    ⟨extend_injective r, fun g => ⟨⟨dropInv g, partner g⟩, extend_drop g⟩⟩

private noncomputable def invWeight {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) : ℕ :=
  ∏ i : Fin r, if i ≤ f.val i then i.val + 1 else 1

private noncomputable def invMonomial {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) : Polynomial ℕ :=
  C (invWeight f) * X ^ (Fintype.card {x : _ // (f).val x = x})

private noncomputable def invSum (r : ℕ) : Polynomial ℕ := ∑ f : {f : Fin r → Fin r // Function.Involutive f}, invMonomial f

private theorem fixedCount_sum {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (Fintype.card {x : _ // (f).val x = x}) = ∑ j : Fin r, if f.val j = j then 1 else 0 := by
  classical
  rw [Fintype.card_subtype, card_filter]

private theorem invWeight_none {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    invWeight (extendInv f none) = (r + 1) * invWeight f := by
  unfold invWeight
  rw [Fin.prod_univ_castSucc]
  simp only [extendInv, extendInvFun_none_last, le_refl, ↓reduceIte,
    Fin.val_last, extendInvFun_none_castSucc, Fin.castSucc_le_castSucc_iff,
    Fin.val_castSucc]
  exact mul_comm _ _

private theorem invWeight_some {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) :
    invWeight (extendInv f (some i)) = invWeight f := by
  unfold invWeight
  rw [Fin.prod_univ_castSucc]
  have hn : ¬ Fin.last r ≤ i.val.castSucc := by
    intro h
    have := i.val.isLt
    change r ≤ i.val.val at h
    omega
  simp only [extendInv, extendInvFun_some_last, hn, ↓reduceIte, mul_one]
  apply prod_congr rfl
  intro j hj
  simp only [extendInvFun_some_castSucc]
  by_cases he : j = i.val
  · subst j
    have hi : i.val.castSucc ≤ Fin.last r := by exact Fin.le_last _
    simp [i.property, hi]
  · simp [he]

private theorem fixedCount_none {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (Fintype.card {x : _ // (extendInv f none).val x = x}) = (Fintype.card {x : _ // (f).val x = x}) + 1 := by
  rw [fixedCount_sum, fixedCount_sum, Fin.sum_univ_castSucc]
  simp only [extendInv, extendInvFun_none_last, ↓reduceIte,
    extendInvFun_none_castSucc, Fin.castSucc_inj]

private theorem fixedCount_some {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) (i : {i : _ // (f).val i = i}) :
    (Fintype.card {x : _ // (extendInv f (some i)).val x = x}) + 1 = (Fintype.card {x : _ // (f).val x = x}) := by
  rw [fixedCount_sum, fixedCount_sum, Fin.sum_univ_castSucc]
  simp only [extendInv, extendInvFun_some_last, Fin.castSucc_ne_last, ↓reduceIte, add_zero]
  have he : ∀ j : Fin r,
      (if extendInvFun f (some i) j.castSucc = j.castSucc then 1 else 0) +
        (if j = i.val then 1 else 0) = if f.val j = j then 1 else 0 := by
    intro j
    rw [extendInvFun_some_castSucc]
    by_cases hj : j = i.val
    · subst j
      simp [i.property, Ne.symm (Fin.castSucc_ne_last i.val)]
    · simp [hj]
  have hs := sum_congr (s₁ := univ) (s₂ := univ) rfl (fun j _ => he j)
  simpa only [sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte] using hs

private theorem invMonomial_option {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (∑ q : Option ({i : _ // (f).val i = i}), invMonomial (extendInv f q)) =
      (invMonomial f).derivative + C (r + 1) * X * invMonomial f := by
  classical
  rw [Fintype.sum_option]
  have hnone : invMonomial (extendInv f none) = C (r + 1) * X * invMonomial f := by
    simp only [invMonomial, invWeight_none, fixedCount_none, C_mul, pow_succ]
    ring
  have hsome : ∀ i : {i : _ // (f).val i = i}, invMonomial (extendInv f (some i)) =
      C (invWeight f) * X ^ ((Fintype.card {x : _ // (f).val x = x}) - 1) := by
    intro i
    have h := fixedCount_some f i
    have he : (Fintype.card {x : _ // (extendInv f (some i)).val x = x}) = (Fintype.card {x : _ // (f).val x = x}) - 1 := by omega
    simp [invMonomial, invWeight_some, he]
  rw [hnone]
  simp_rw [hsome]
  simp only [sum_const, nsmul_eq_mul, invMonomial, derivative_C_mul_X_pow]
  change C (r + 1) * X * (C (invWeight f) * X ^ (Fintype.card {x : _ // (f).val x = x})) +
    ((Fintype.card {x : _ // (f).val x = x}) : Polynomial ℕ) * (C (invWeight f) * X ^ ((Fintype.card {x : _ // (f).val x = x}) - 1)) = _
  simp only [← C_eq_natCast, C_mul]
  ring

private theorem invSum_succ (r : ℕ) :
    invSum (r + 1) = (invSum r).derivative + C (r + 1) * X * invSum r := by
  classical
  unfold invSum
  rw [← Equiv.sum_comp (invSuccEquiv r)]
  rw [Fintype.sum_sigma]
  change (∑ f : {f : Fin r → Fin r // Function.Involutive f}, ∑ q : Option ({i : _ // (f).val i = i}), invMonomial (extendInv f q)) = _
  simp_rw [invMonomial_option]
  rw [sum_add_distrib, ← derivative_sum, ← mul_sum]

private theorem invSum_zero : invSum 0 = 1 := by
  classical
  letI : Unique ({f : Fin 0 → Fin 0 // Function.Involutive f}) :=
    { default := ⟨id, fun x => rfl⟩
      uniq := fun f => Subtype.ext (funext (fun x => Fin.elim0 x)) }
  simp [invSum, invMonomial, invWeight]

private theorem invSum_walkPoly (r : ℕ) : invSum r = walkPoly r := by
  induction r with
  | zero => exact invSum_zero
  | succ r ih => rw [invSum_succ, ih, walkPoly]

private def P (n : ℕ) :=
    {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ ∀ i, f i ≠ i}

private noncomputable instance (n : ℕ) : Fintype (P n) := by
  unfold P
  infer_instance

private theorem fixedCount_zero_iff {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (Fintype.card {x : _ // (f).val x = x}) = 0 ↔ ∀ i, f.val i ≠ i := by
  constructor
  · intro hz i hi
    have hp : 0 < (Fintype.card {x : _ // (f).val x = x}) := Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    omega
  · intro hn
    letI : IsEmpty ({i : _ // (f).val i = i}) := ⟨fun i => hn i.val i.property⟩
    exact Fintype.card_eq_zero

private noncomputable def pairingInvEquiv (n : ℕ) :
    P n ≃ {f : {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f} // (Fintype.card {x : _ // (f).val x = x}) = 0} where
  toFun p := ⟨⟨(p).val, (p).property.1⟩, (fixedCount_zero_iff _).mpr p.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, (fixedCount_zero_iff _).mp f.property⟩
  left_inv p := rfl
  right_inv f := rfl

private theorem invMonomial_eval_zero {r : ℕ} (f : {f : Fin r → Fin r // Function.Involutive f}) :
    (invMonomial f).eval 0 = if (Fintype.card {x : _ // (f).val x = x}) = 0 then invWeight f else 0 := by
  by_cases h : (Fintype.card {x : _ // (f).val x = x}) = 0 <;> simp [invMonomial, h]

private theorem polyConst_pairings (n : ℕ) :
    (walkPoly (2 * n)).eval 0 = ∑ p : P n, invWeight (⟨(p).val, (p).property.1⟩) := by
  classical
  rw [← invSum_walkPoly, invSum, eval_finsetSum]
  simp only [invMonomial_eval_zero]
  rw [← sum_filter]
  rw [sum_subtype (p := fun f : {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f} => (Fintype.card {x : _ // (f).val x = x}) = 0) _ (by simp)]
  exact (Equiv.sum_comp (pairingInvEquiv n) (fun f => invWeight f.val)).symm


private noncomputable def fixedPermEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin (2 * n)) // ∀ i, σ i ≠ i ∧ σ (σ i) = i} ≃ P n where
  toFun σ := ⟨σ.val, fun i => (σ.property i).2, fun i => (σ.property i).1⟩
  invFun f := ⟨⟨f.val, f.val, f.property.1, f.property.1⟩,
    fun i => ⟨f.property.2 i, f.property.1 i⟩⟩
  left_inv σ := Subtype.ext (Equiv.ext fun _ => rfl)
  right_inv f := rfl

private theorem haf_pairings (n : ℕ) :
    OMA.S_oeis_a002067.haf n = ∑ p : P n, invWeight ⟨p.val, p.property.1⟩ := by
  classical
  unfold OMA.S_oeis_a002067.haf
  rw [Finset.sum_subtype (p := fun σ : Equiv.Perm (Fin (2 * n)) =>
    ∀ i, σ i ≠ i ∧ σ (σ i) = i) _ (by simp)]
  calc
    _ = ∑ σ : {σ : Equiv.Perm (Fin (2 * n)) // ∀ i, σ i ≠ i ∧ σ (σ i) = i},
        invWeight ⟨(fixedPermEquiv n σ).val, (fixedPermEquiv n σ).property.1⟩ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.prod_filter]
      unfold invWeight
      apply Finset.prod_congr rfl
      intro i _
      change (if i < σ.val i then i.val + 1 else 1) =
        (if i ≤ σ.val i then i.val + 1 else 1)
      have h : i < σ.val i ↔ i ≤ σ.val i :=
        lt_iff_le_and_ne.trans (and_iff_left (σ.property i).1.symm)
      exact ite_congr (propext h) (fun _ => rfl) (fun _ => rfl)
    _ = _ := Equiv.sum_comp (fixedPermEquiv n) (fun p => invWeight ⟨p.val, p.property.1⟩)

private theorem a_is_source : IsSourceSequence OMA.S_oeis_a002067.a := by
  refine ⟨by rw [OMA.S_oeis_a002067.a], fun n => ?_⟩
  rw [OMA.S_oeis_a002067.a]
  exact Fin.sum_univ_eq_sum_range
    (fun k => (2 * (n + 1)).choose (2 * k) * OMA.S_oeis_a002067.a k *
      OMA.S_oeis_a002067.a (n - k)) (n + 1)

end CallanProof

theorem OMA.solution : type_of% @OMA.S_oeis_a002067.main := by
  intro n
  calc
    OMA.S_oeis_a002067.a n = (CallanProof.walkPoly (2 * n)).eval 0 :=
      congrFun (CallanProof.source_unique CallanProof.a_is_source CallanProof.poly_is_source) n
    _ = OMA.S_oeis_a002067.haf n :=
      (CallanProof.polyConst_pairings n).trans (CallanProof.haf_pairings n).symm
