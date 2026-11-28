import FormalConjectures.ErdosProblems.«245»
import Mathlib

/-!
# Erdős Problem 245

Gregory Freiman proved that the upper limiting ratio of the count of sums
to the count of elements is at least three for an infinite set of natural
numbers of density zero.

The finite additive-combinatorial and geometric arguments are adapted
from the Lean development in `plby/lean-proofs` at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. The final proof there is
credited to Codex and GPT-5.6 Sol. The source is copyright (c) 2026
Boris Alexeev and released under the Apache License, Version 2.0.
This adaptation combines the relevant modules, specializes the GAP
cover to the rank and coefficient-box bounds needed here, and matches
the desk's pinned statement.
https://www.apache.org/licenses/LICENSE-2.0
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

section Erdos245_Conic

open scoped BigOperators

namespace Erdos245Scratch

def nzSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) : Finset ι :=
  Finset.univ.filter fun i ↦ a i ≠ 0

@[simp] lemma mem_nzSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (i : ι) : i ∈ nzSupport a ↔ a i ≠ 0 := by
  simp [nzSupport]

/-- A finite nonnegative rational linear combination can be chosen with
linearly independent nonzero support. -/
theorem exists_nonnegative_linearIndependent_support
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V]
    (w : ι → V) (a : ι → ℚ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ι → ℚ,
      (∀ i, 0 ≤ b i) ∧
      (∑ i, b i • w i) = ∑ i, a i • w i ∧
      LinearIndependent ℚ (fun i : ↥(nzSupport b) ↦ w i.1) := by
  classical
  let target : V := ∑ i, a i • w i
  let Good : ℕ → Prop := fun n ↦
    ∃ b : ι → ℚ, (∀ i, 0 ≤ b i) ∧
      (∑ i, b i • w i) = target ∧ (nzSupport b).card = n
  have hGood : ∃ n, Good n := by
    refine ⟨(nzSupport a).card, a, ha, rfl, rfl⟩
  let n := Nat.find hGood
  obtain ⟨b, hb, hbsum, hbcard⟩ := Nat.find_spec hGood
  refine ⟨b, hb, by simpa [target] using hbsum, ?_⟩
  by_contra hdependent
  obtain ⟨g, hg, i₀, hi₀⟩ :=
    Fintype.not_linearIndependent_iff.mp hdependent
  let g' : ↥(nzSupport b) → ℚ :=
    if 0 < g i₀ then g else -g
  have hg'sum : ∑ i, g' i • w i.1 = 0 := by
    by_cases hpos : 0 < g i₀
    · simpa [g', hpos] using hg
    · have hneg : g i₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi₀
      simpa [g', hpos] using congrArg Neg.neg hg
  have hi₀pos : 0 < g' i₀ := by
    by_cases hpos : 0 < g i₀
    · simp [g', hpos]
    · have hneg : g i₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi₀
      simp [g', hpos, hneg]
  let P : Finset ↥(nzSupport b) := Finset.univ.filter fun i ↦ 0 < g' i
  have hP : P.Nonempty := by
    refine ⟨i₀, ?_⟩
    simp [P, hi₀pos]
  let R : Finset ℚ := P.image fun i ↦ b i.1 / g' i
  have hR : R.Nonempty := hP.image _
  let t : ℚ := R.min' hR
  obtain ⟨iMin, hiMinP, htEq⟩ := Finset.mem_image.mp (R.min'_mem hR)
  have hiMinG : 0 < g' iMin := (Finset.mem_filter.mp hiMinP).2
  have hiMinB : 0 < b iMin.1 := by
    have hne : b iMin.1 ≠ 0 := (mem_nzSupport b iMin.1).mp iMin.2
    exact lt_of_le_of_ne (hb iMin.1) (Ne.symm hne)
  have htpos : 0 < t := by
    change 0 < R.min' hR
    rw [← htEq]
    exact div_pos hiMinB hiMinG
  let gFull : ι → ℚ := fun i ↦
    if hi : i ∈ nzSupport b then g' ⟨i, hi⟩ else 0
  have hgFull : ∑ i, gFull i • w i = 0 := by
    calc
      ∑ i, gFull i • w i = ∑ i ∈ nzSupport b, gFull i • w i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _hi hi
        have hbi : b i = 0 := not_ne_iff.mp (mt (mem_nzSupport b i).mpr hi)
        simp [gFull, hbi]
      _ = ∑ i : ↥(nzSupport b), g' i • w i.1 := by
        rw [← (nzSupport b).sum_attach]
        apply Finset.sum_congr rfl
        intro i hi
        have hbi : b i.1 ≠ 0 := (mem_nzSupport b i.1).mp i.2
        simp [gFull, hbi]
      _ = 0 := hg'sum
  let b' : ι → ℚ := fun i ↦ b i - t * gFull i
  have hb' : ∀ i, 0 ≤ b' i := by
    intro i
    by_cases hi : i ∈ nzSupport b
    · let ii : ↥(nzSupport b) := ⟨i, hi⟩
      have hbi0 : b i ≠ 0 := (mem_nzSupport b i).mp hi
      by_cases hgpos : 0 < g' ii
      · have hiP : ii ∈ P := by simp [P, hgpos]
        have hratio : t ≤ b i / g' ii := by
          apply Finset.min'_le R
          exact Finset.mem_image.mpr ⟨ii, hiP, rfl⟩
        have hmul : t * g' ii ≤ b i :=
          (le_div_iff₀ hgpos).mp hratio
        simpa [b', gFull, hi, hbi0, ii] using sub_nonneg.mpr hmul
      · have hgle : g' ii ≤ 0 := le_of_not_gt hgpos
        have htg : t * g' ii ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hgle
        have : 0 ≤ b i - t * g' ii := sub_nonneg.mpr (htg.trans (hb i))
        simpa [b', gFull, hi, hbi0, ii] using this
    · have hbi : b i = 0 := not_ne_iff.mp (mt (mem_nzSupport b i).mpr hi)
      simp [b', gFull, hbi]
  have hb'sum : (∑ i, b' i • w i) = ∑ i, b i • w i := by
    simp only [b', sub_smul, mul_smul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hgFull, smul_zero, sub_zero]
  have hsupport : nzSupport b' ⊆ nzSupport b := by
    intro i hi'
    by_contra hi
    have hbi : b i = 0 := not_ne_iff.mp (mt (mem_nzSupport b i).mpr hi)
    have hzero : b' i = 0 := by simp [b', gFull, hbi]
    exact (mem_nzSupport b' i).mp hi' hzero
  have hiMinZero : b' iMin.1 = 0 := by
    have ht : t = b iMin.1 / g' iMin := htEq.symm
    simp only [b', gFull, iMin.2, dite_true, ht]
    rw [div_mul_cancel₀ _ hiMinG.ne']
    exact sub_self _
  have hproper : nzSupport b' ⊂ nzSupport b := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsupport, ?_⟩
    intro heq
    have : iMin.1 ∈ nzSupport b' := by
      rw [heq]
      exact iMin.2
    exact (mem_nzSupport b' iMin.1).mp this hiMinZero
  have hcardlt : (nzSupport b').card < (nzSupport b).card :=
    Finset.card_lt_card hproper
  have hminimal : n ≤ (nzSupport b').card := by
    apply Nat.find_min' hGood
    refine ⟨b', hb', ?_, rfl⟩
    exact hb'sum.trans hbsum
  rw [hbcard] at hcardlt
  omega

/-- Columnwise bounds give the elementary Leibniz bound for an integer
determinant. -/
theorem natAbs_det_le_factorial_mul_prod
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (B : n → ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B j) :
    A.det.natAbs ≤ (Fintype.card n).factorial * ∏ j, B j := by
  have natAbs_prod (f : n → ℤ) :
      (∏ i, f i).natAbs = ∏ i, (f i).natAbs := by
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => simp [hx, Int.natAbs_mul, ih]
  rw [Matrix.det_apply']
  calc
    (∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i)).natAbs
        ≤ ∑ σ : Equiv.Perm n,
          (((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i).natAbs) :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm n, ∏ i, B i := by
      apply Finset.sum_le_sum
      intro σ _hσ
      rw [Int.natAbs_mul, natAbs_prod (fun i ↦ A (σ i) i)]
      have hsign : ((Equiv.Perm.sign σ : ℤ)).natAbs = 1 := by simp
      rw [hsign, one_mul]
      exact Finset.prod_le_prod' fun i _hi ↦ hA (σ i) i
    _ = (Fintype.card n).factorial * ∏ i, B i := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
      rfl

def castVec {d : ℕ} (z : Fin d → ℤ) : Fin d → ℚ :=
  fun i ↦ z i

lemma castVec_injective {d : ℕ} :
    Function.Injective (@castVec d) := by
  intro x y h
  ext j
  have hj := congrFun h j
  change (x j : ℚ) = (y j : ℚ) at hj
  exact_mod_cast hj

@[simp] lemma castVec_apply {d : ℕ} (z : Fin d → ℤ) (i : Fin d) :
    castVec z i = (z i : ℚ) := rfl

/-- Cramer's-rule bound in the form needed for the coefficient chain.  The
independent integer vectors are extended using only standard basis vectors,
so a columnwise integral bound is preserved. -/
theorem coefficient_le_of_integral_linearIndependent
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Fin d → ℤ) (v : Fin d → ℤ) (a : ι → ℚ) (i₀ : ι)
    (hli : LinearIndependent ℚ (fun i ↦ castVec (w i)))
    (hrel : castVec v = ∑ i, a i • castVec (w i))
    (B : Fin d → ℕ) (hB : ∀ j, 1 ≤ B j)
    (hw : ∀ i j, (w i j).natAbs ≤ B j)
    (hv : ∀ j, (v j).natAbs ≤ B j) :
    a i₀ ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by
  classical
  let f : ι → (Fin d → ℚ) := fun i ↦ castVec (w i)
  let s : Set (Fin d → ℚ) := Set.range f
  let stdZ : Fin d → Fin d → ℤ := fun j ↦ Pi.single j 1
  let stdQ : Fin d → Fin d → ℚ := fun j ↦ castVec (stdZ j)
  let t : Set (Fin d → ℚ) := s ∪ Set.range stdQ
  have hs : LinearIndepOn ℚ id s := by
    exact hli.linearIndepOn_id
  have hst : s ⊆ t := Set.subset_union_left
  have ht : (⊤ : Submodule ℚ (Fin d → ℚ)) ≤ Submodule.span ℚ t := by
    rw [← (Pi.basisFun ℚ (Fin d)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    apply Set.mem_union_right
    refine ⟨j, ?_⟩
    ext k
    by_cases hjk : j = k
    · subst k
      simp [stdQ, stdZ, Pi.basisFun_apply]
    · simp [stdQ, stdZ, Pi.basisFun_apply, hjk]
  let basis : Module.Basis (hs.extend hst) ℚ (Fin d → ℚ) :=
    Module.Basis.extendLe hs hst ht
  let I := hs.extend hst
  let : Fintype I := Fintype.ofFinite I
  have hIntegral (i : I) :
      ∃ z : Fin d → ℤ, castVec z = basis i := by
    have hi : basis i ∈ t := by
      apply Module.Basis.extendLe_subset hs hst ht
      exact Set.mem_range_self i
    rcases hi with hi | hi
    · obtain ⟨j, hj⟩ := hi
      exact ⟨w j, by simpa [f, s] using hj⟩
    · obtain ⟨j, hj⟩ := hi
      exact ⟨stdZ j, by simpa [stdQ] using hj⟩
  choose bz hbz using hIntegral
  have hcard : Fintype.card I = d := by
    rw [← Module.finrank_eq_card_basis basis]
    simp
  let e : I ≃ Fin d := Fintype.equivOfCardEq (by simpa using hcard)
  let A : Matrix I I ℤ := fun i j ↦ bz i (e j)
  let AQ : Matrix I I ℚ := fun i j ↦ basis i (e j)
  have hAmap : A.map (Int.castRingHom ℚ) = AQ := by
    ext i j
    exact congrFun (hbz i) (e j)
  let E : (Fin d → ℚ) ≃ₗ[ℚ] (I → ℚ) :=
    LinearEquiv.piCongrLeft' ℚ (fun _ : Fin d ↦ ℚ) e.symm
  have hAQli : LinearIndependent ℚ (fun i ↦ AQ i) := by
    have hmap := basis.linearIndependent.map' E.toLinearMap (by simp [E])
    have heq : (fun i ↦ AQ i) = E ∘ basis := by
      funext i j
      rfl
    rw [heq]
    exact hmap
  have hAdetQ : AQ.det ≠ 0 := by
    have hunitA : IsUnit AQ :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hAQli
    exact ((Matrix.isUnit_iff_isUnit_det AQ).mp hunitA).ne_zero
  have hcast : (A.det : ℚ) = AQ.det :=
    (Int.cast_det A).trans (congrArg Matrix.det hAmap)
  have hAdet : A.det ≠ 0 := by
    intro hzero
    apply hAdetQ
    rw [← hcast, hzero]
    simp
  let ii : ι → I := fun i ↦
    ⟨f i, hs.subset_extend hst (Set.mem_range_self i)⟩
  let ic : I := ii i₀
  have hbasis_ii (i : ι) : basis (ii i) = f i := by
    exact Module.Basis.extendLe_apply_self hs hst ht (ii i)
  have hii_injective : Function.Injective ii := by
    intro i j hij
    apply hli.injective
    have := congrArg Subtype.val hij
    simpa [ii] using this
  have hrepr_w (i : ι) :
      basis.repr (castVec (w i)) ic = if i = i₀ then 1 else 0 := by
    rw [show castVec (w i) = basis (ii i) by simpa [f] using (hbasis_ii i).symm]
    rw [basis.repr_self_apply]
    by_cases hi : i = i₀
    · subst i
      simp [ic]
    · have hne : ii i ≠ ic := by
        simpa [ic] using fun h ↦ hi (hii_injective h)
      simp [hne, hi]
  have hrepr : basis.repr (castVec v) ic = a i₀ := by
    calc
      basis.repr (castVec v) ic =
          basis.repr (∑ i, a i • castVec (w i)) ic := by rw [hrel]
      _ = ∑ i, a i * basis.repr (castVec (w i)) ic := by simp
      _ = a i₀ := by simp [hrepr_w]
  have hbzBound (i j : I) : (bz i (e j)).natAbs ≤ B (e j) := by
    have hi : basis i ∈ t := by
      apply Module.Basis.extendLe_subset hs hst ht
      exact Set.mem_range_self i
    rcases hi with hi | hi
    · obtain ⟨k, hk⟩ := hi
      have heq : bz i (e j) = w k (e j) := by
        have := castVec_injective ((hbz i).trans hk.symm)
        exact congrFun this (e j)
      rw [heq]
      exact hw k (e j)
    · obtain ⟨k, hk⟩ := hi
      have heq : bz i (e j) = stdZ k (e j) := by
        have := castVec_injective ((hbz i).trans hk.symm)
        exact congrFun this (e j)
      rw [heq]
      by_cases hkj : k = e j
      · subst k
        simpa [stdZ] using hB (e j)
      · simp [stdZ, hkj]
  let vRow : I → ℤ := fun j ↦ v (e j)
  let Av : Matrix I I ℤ := A.updateRow ic vRow
  have hAvBound (i j : I) : (Av i j).natAbs ≤ B (e j) := by
    by_cases hi : i = ic
    · subst i
      simpa [Av, vRow, Matrix.updateRow_self] using hv (e j)
    · change ((A.updateRow ic vRow) i j).natAbs ≤ B (e j)
      rw [Matrix.updateRow_apply, if_neg hi]
      exact hbzBound i j
  have hAvdet : Av.det.natAbs ≤ d.factorial * ∏ j, B j := by
    have h := natAbs_det_le_factorial_mul_prod Av (fun j ↦ B (e j)) hAvBound
    rw [hcard] at h
    simpa only [Equiv.prod_comp e] using h
  have hvrow : (fun j : I ↦ (v (e j) : ℚ)) =
      ∑ i, (basis.repr (castVec v) i) • AQ i := by
    funext j
    have hsum := congrFun (basis.sum_repr (castVec v)) (e j)
    simpa [AQ] using hsum.symm
  have hAvmap : Av.map (Int.castRingHom ℚ) =
      AQ.updateRow ic (fun j ↦ (v (e j) : ℚ)) := by
    ext i j
    by_cases hi : i = ic
    · subst i
      simp [Av, vRow, Matrix.updateRow_self]
    · change ((A.updateRow ic vRow i j : ℤ) : ℚ) =
          AQ.updateRow ic (fun j ↦ (v (e j) : ℚ)) i j
      rw [Matrix.updateRow_apply, Matrix.updateRow_apply, if_neg hi, if_neg hi]
      change (bz i (e j) : ℚ) = basis i (e j)
      exact congrFun (hbz i) (e j)
  have hdetrel : (Av.det : ℚ) = a i₀ * (A.det : ℚ) := by
    calc
      (Av.det : ℚ) = (Av.map (Int.castRingHom ℚ)).det := Int.cast_det Av
      _ = (AQ.updateRow ic (fun j ↦ (v (e j) : ℚ))).det := by rw [hAvmap]
      _ = (AQ.updateRow ic
          (∑ i, (basis.repr (castVec v) i) • AQ i)).det := by rw [hvrow]
      _ = basis.repr (castVec v) ic * AQ.det := by
        simpa only [smul_eq_mul] using
          Matrix.det_updateRow_sum AQ ic (fun i ↦ basis.repr (castVec v) i)
      _ = a i₀ * (A.det : ℚ) := by
        rw [hrepr, ← hcast]
  have habs : |a i₀| * (A.det.natAbs : ℚ) = (Av.det.natAbs : ℚ) := by
    have := congrArg abs hdetrel
    simpa [abs_mul, mul_comm] using this.symm
  have hdetOne : 1 ≤ A.det.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hAdet)
  calc
    a i₀ ≤ |a i₀| := le_abs_self _
    _ ≤ |a i₀| * (A.det.natAbs : ℚ) := by
      have : (1 : ℚ) ≤ A.det.natAbs := by exact_mod_cast hdetOne
      nlinarith [abs_nonneg (a i₀)]
    _ = (Av.det.natAbs : ℚ) := habs
    _ ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by exact_mod_cast hAvdet

end Erdos245Scratch

end Erdos245_Conic

section Erdos245_Chain

open scoped BigOperators

namespace Erdos245Scratch

def chainGen {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) : Fin (n + 1) → V :=
  Fin.cases (u 0) fun j : Fin n ↦ u (j + 1) - (2 : ℚ) • u j

private lemma chainGen_castSucc {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) (i : Fin (n + 1)) :
    chainGen u (n + 1) i.castSucc = chainGen u n i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

private lemma chainGen_last {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) :
    chainGen u (n + 1) (Fin.last (n + 1)) =
      u (n + 1) - (2 : ℚ) • u n := by
  rfl

lemma exists_nonnegative_chain_coefficients
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : ℕ → V) (n : ℕ) :
    ∃ a : Fin (n + 1) → ℚ, (∀ i, 0 ≤ a i) ∧
      u n = ∑ i, a i • chainGen u n i := by
  induction n with
  | zero =>
      refine ⟨fun _ ↦ 1, fun _ ↦ by positivity, ?_⟩
      simp [chainGen]
  | succ n ih =>
      obtain ⟨a, ha, hrepr⟩ := ih
      let a' : Fin (n + 2) → ℚ := Fin.lastCases 1 (fun i ↦ 2 * a i)
      refine ⟨a', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [a']
        · simp [a', ha]
      · rw [Fin.sum_univ_castSucc]
        simp only [a', Fin.lastCases_castSucc, Fin.lastCases_last,
          chainGen_castSucc, chainGen_last]
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, ← hrepr]
        module

def chainGenInt {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ) :
    Fin (n + 1) → Fin d → ℤ :=
  Fin.cases (u 0) fun j : Fin n ↦ u (j + 1) - 2 • u j

lemma castVec_chainGenInt {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ)
    (i : Fin (n + 1)) :
    castVec (chainGenInt u n i) =
      chainGen (fun k ↦ castVec (u k)) n i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · ext q
    simp [chainGenInt, chainGen, castVec, sub_eq_add_neg]

/-- The doubling-chain representation, reduced to linearly independent
nonzero support and with its initial coefficient bounded by Cramer's rule. -/
lemma exists_bounded_reduced_chain_coefficients
    {d : ℕ} (u : ℕ → Fin d → ℤ) (n : ℕ) (q : Fin d)
    (hq : ∀ i, u i q = 1)
    (B : Fin d → ℕ) (hB : ∀ j, 1 ≤ B j)
    (hgen : ∀ i j, (chainGenInt u n i j).natAbs ≤ B j)
    (hv : ∀ j, (u n j).natAbs ≤ B j) :
    ∃ b : Fin (n + 1) → ℚ,
      (∀ i, 0 ≤ b i) ∧
      castVec (u n) = ∑ i, b i • castVec (chainGenInt u n i) ∧
      0 < b 0 ∧
      b 0 ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by
  classical
  obtain ⟨a, ha, harepr⟩ :=
    exists_nonnegative_chain_coefficients (fun k ↦ castVec (u k)) n
  have harepr' :
      castVec (u n) = ∑ i, a i • castVec (chainGenInt u n i) := by
    rw [harepr]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [castVec_chainGenInt]
  obtain ⟨b, hb, hbsum, hbli⟩ :=
    exists_nonnegative_linearIndependent_support
      (fun i ↦ castVec (chainGenInt u n i)) a ha
  have hrel :
      castVec (u n) = ∑ i, b i • castVec (chainGenInt u n i) := by
    rw [harepr', ← hbsum]
  have hgenq (i : Fin (n + 1)) :
      chainGenInt u n i q = if i = 0 then 1 else -1 := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [chainGenInt, hq]
    · have hsucc : (Fin.succ j : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero j
      simp [chainGenInt, hq, hsucc]
  have hcoord :
      (1 : ℚ) = ∑ i, b i * (chainGenInt u n i q : ℚ) := by
    have h := congrFun hrel q
    simpa only [castVec_apply, hq, Int.cast_one, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h
  have hbzero : 0 < b 0 := by
    by_contra hnpos
    have hb0 : b 0 = 0 := le_antisymm (le_of_not_gt hnpos) (hb 0)
    have hterm (i : Fin (n + 1)) :
        b i * (chainGenInt u n i q : ℚ) ≤ 0 := by
      by_cases hi : i = 0
      · subst i
        simp [hb0]
      · rw [hgenq, if_neg hi]
        simp [hb i]
    have hsum :
        (∑ i, b i * (chainGenInt u n i q : ℚ)) ≤ 0 :=
      Finset.sum_nonpos fun i _hi ↦ hterm i
    linarith
  let i0 : ↥(nzSupport b) := ⟨0, (mem_nzSupport b 0).2 hbzero.ne'⟩
  have hrel_support :
      castVec (u n) =
        ∑ i : ↥(nzSupport b),
          b i.1 • castVec (chainGenInt u n i.1) := by
    calc
      castVec (u n) =
          ∑ i, b i • castVec (chainGenInt u n i) := hrel
      _ = ∑ i ∈ nzSupport b,
          b i • castVec (chainGenInt u n i) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _hi hnot
        have hbi : b i = 0 :=
          not_ne_iff.mp (mt (mem_nzSupport b i).mpr hnot)
        simp [hbi]
      _ = ∑ i : ↥(nzSupport b),
          b i.1 • castVec (chainGenInt u n i.1) := by
        rw [← (nzSupport b).sum_attach]
        rfl
  have hcoeff := coefficient_le_of_integral_linearIndependent
    (fun i : ↥(nzSupport b) ↦ chainGenInt u n i.1) (u n)
    (fun i : ↥(nzSupport b) ↦ b i.1) i0 hbli hrel_support B hB
    (fun i j ↦ hgen i.1 j) hv
  refine ⟨b, hb, hrel, hbzero, ?_⟩
  simpa [i0] using hcoeff

end Erdos245Scratch

end Erdos245_Chain

section Erdos13_Erdos13MulStab

/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/

/-
# Stabilizer of a finset

This file defines the stabilizer of a finset of a group as a finset.

## Main declarations

* `Finset.mulStab`: The stabilizer of a **nonempty** finset as a finset.
-/


open Function MulAction
open scoped Pointwise

namespace Finset
variable {ι α : Type*}


section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

instance (s : Finset α) : DecidablePred (· ∈ stabilizer α (s : Set α)) :=
  fun a ↦ decidable_of_iff (a ∈ stabilizer α s) (by simp)

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`. -/
def mulStab (s : Finset α) : Finset α := {a ∈ s / s | a • s = s}

@[simp]
lemma mem_mulStab (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s = s := by
  rw [mulStab, mem_filter, mem_div, and_iff_right_of_imp]
  obtain ⟨b, hb⟩ := hs
  exact fun h ↦ ⟨_, by rw [← h]; exact smul_mem_smul_finset hb, _, hb, mul_div_cancel_right _ _⟩

lemma mulStab_subset_div_right (ha : a ∈ s) : s.mulStab ⊆ s / {a} := by
  refine fun b hb ↦ mem_div.2 ⟨_, ?_, _, mem_singleton_self _, mul_div_cancel_right _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rw [← hb]
  exact smul_mem_smul_finset ha

@[simp]
lemma coe_mulStab (hs : s.Nonempty) : (s.mulStab : Set α) = stabilizer α (s : Set α) := by
  ext; simp [mem_mulStab hs]

lemma mem_mulStab_iff_subset_smul_finset (hs : s.Nonempty) : a ∈ s.mulStab ↔ s ⊆ a • s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_subset_smul_finset]

lemma mem_mulStab_iff_smul_finset_subset (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s ⊆ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_smul_finset_subset]

lemma mem_mulStab' (hs : s.Nonempty) : a ∈ s.mulStab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset, mem_stabilizer_finset']

@[simp]
lemma mulStab_empty : mulStab (∅ : Finset α) = ∅ := by simp [mulStab]

@[simp]
lemma mulStab_singleton (a : α) : mulStab ({a} : Finset α) = 1 := by
  simp [mulStab, singleton_one, filter_true_of_mem]

lemma Nonempty.of_mulStab : s.mulStab.Nonempty → s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, not_imp_not]; rintro rfl; exact mulStab_empty

@[simp]
lemma one_mem_mulStab : (1 : α) ∈ s.mulStab ↔ s.Nonempty :=
  ⟨fun h ↦ Nonempty.of_mulStab ⟨_, h⟩, fun h ↦ (mem_mulStab h).2 <| one_smul _ _⟩

lemma Nonempty.mulStab (h : s.Nonempty) : s.mulStab.Nonempty := ⟨_, (one_mem_mulStab.mpr h)⟩

@[simp]
lemma mulStab_nonempty : s.mulStab.Nonempty ↔ s.Nonempty := ⟨Nonempty.of_mulStab, Nonempty.mulStab⟩

@[simp]
lemma card_mulStab_eq_one : #s.mulStab = 1 ↔ s.mulStab = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, card_one]⟩
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  rw [ha]
  rw [eq_singleton_iff_nonempty_unique_mem, mulStab_nonempty, ← one_mem_mulStab] at ha
  rw [← ha.2 _ ha.1, singleton_one]

lemma Nonempty.mulStab_nontrivial (h : s.Nonempty) : s.mulStab.Nontrivial ↔ s.mulStab ≠ 1 :=
  nontrivial_iff_ne_singleton (one_mem_mulStab.mpr h)

lemma subset_mulStab_mul_left (ht : t.Nonempty) : s.mulStab ⊆ (s * t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  simp_rw [subset_iff, mem_mulStab hs, mem_mulStab (hs.mul ht)]
  rintro a h
  rw [← smul_mul_assoc, h]

@[simp]
lemma mulStab_mul (s : Finset α) : s.mulStab * s = s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact mul_empty _
  · simp only [← coe_inj, hs, coe_mul, coe_mulStab, stabilizer_mul_self]

lemma mul_subset_right_iff (ht : t.Nonempty) : s * t ⊆ t ↔ s ⊆ t.mulStab := by
  simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_subset,
    ← mem_mulStab_iff_smul_finset_subset ht, subset_iff]

lemma smul_mulStab (ha : a ∈ s.mulStab) : a • s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe] at ha
  rw [← coe_inj, coe_smul_finset, coe_mulStab hs, smul_coe_set ha]

@[simp]
lemma mulStab_mul_mulStab (s : Finset α) : s.mulStab * s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_congr rfl fun _ ↦ smul_mulStab,
      ← sup_eq_biUnion, sup_const hs.mulStab]

lemma inter_mulStab_subset_mulStab_union : s.mulStab ∩ t.mulStab ⊆ (s ∪ t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  intro x hx
  rw [mem_mulStab (hs.mono subset_union_left), smul_finset_union,
    (mem_mulStab hs).mp (mem_of_mem_inter_left hx),
    (mem_mulStab ht).mp (mem_of_mem_inter_right hx)]

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

lemma subset_mulStab_mul_right (hs : s.Nonempty) : t.mulStab ⊆ (s * t).mulStab := by
  rw [mul_comm]; exact subset_mulStab_mul_left hs

@[simp]
lemma mul_mulStab (s : Finset α) : s * s.mulStab = s := by rw [mul_comm]; exact mulStab_mul _

@[simp]
lemma mul_mulStab_mul_mul_mul_mulStab_mul :
    s * (s * t).mulStab * (t * (s * t).mulStab) = s * t := by
  rw [mul_mul_mul_comm, mulStab_mul_mulStab, mul_mulStab]

lemma smul_finset_mulStab_subset (ha : a ∈ s) : a • s.mulStab ⊆ s :=
  (smul_finset_subset_smul ha).trans s.mul_mulStab.subset

lemma mul_subset_left_iff (hs : s.Nonempty) : s * t ⊆ s ↔ t ⊆ s.mulStab := by
  rw [mul_comm, mul_subset_right_iff hs]

@[simp]
lemma mulStab_idem (s : Finset α) : s.mulStab.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.mulStab, coe_mulStab hs]
  simp

@[simp]
lemma mulStab_smul (a : α) (s : Finset α) : (a • s).mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.smul_finset, stabilizer_coe_finset,
    stabilizer_coe_finset, stabilizer_smul_eq_right]

lemma mulStab_image_coe_quotient (hs : s.Nonempty) :
    (s.image (↑) : Finset (α ⧸ stabilizer α (s : Set α))).mulStab = 1 := by
  simp_rw [← coe_inj, coe_mulStab (hs.image _), coe_image, coe_one]
  rw [stabilizer_image_coe_quotient, Subgroup.coe_bot, Set.singleton_one]

lemma preimage_image_quotientMk_stabilizer_eq_mul_mulStab (ht : t.Nonempty) (s : Finset α) :
    QuotientGroup.mk ⁻¹' (Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s) = s * t.mulStab := by
  rw [QuotientGroup.preimage_image_mk_eq_mul, coe_mulStab ht, stabilizer_coe_finset]

omit [DecidableEq α] in
lemma preimage_image_quotientMk_mulStabilizer (s : Finset α) :
    QuotientGroup.mk ⁻¹' (Set.image ((↑) : α → α ⧸ stabilizer α (s : Set α)) s) = s := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab hs s, ← coe_mul, mul_mulStab]

lemma pairwiseDisjoint_smul_finset_mulStab (s : Finset α) :
    (Set.range fun a : α ↦ a • s.mulStab).PairwiseDisjoint id := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [onFun, id_eq]
  simp_rw [← disjoint_coe, ← coe_injective.ne_iff, coe_smul_finset, coe_mulStab hs]
  exact fun h ↦ isBlock_subgroup h

lemma disjoint_smul_finset_mulStab_mul_mulStab :
    ¬a • s.mulStab ⊆ t * s.mulStab → Disjoint (a • s.mulStab) (t * s.mulStab) := by
  simp_rw [@not_imp_comm (_ ≤ _), ← smul_eq_mul, ← biUnion_smul_finset, disjoint_biUnion_right,
    Classical.not_forall]
  rintro ⟨b, hb, h⟩
  rw [s.pairwiseDisjoint_smul_finset_mulStab.eq (Set.mem_range_self _) (Set.mem_range_self _) h]
  exact subset_biUnion_of_mem (· • mulStab s) hb

lemma card_mulStab_dvd_card_mul_mulStab (s t : Finset α) : #t.mulStab ∣ #(s * t.mulStab) :=
  card_dvd_card_smul_right <|
    t.pairwiseDisjoint_smul_finset_mulStab.subset <| Set.image_subset_range _ _

lemma card_mulStab_dvd_card (s : Finset α) : #s.mulStab ∣ #s := by
  simpa only [mul_mulStab] using s.card_mulStab_dvd_card_mul_mulStab s

/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.mulStab`. -/
private abbrev fintypeStabilizerOfMulStab (hs : s.Nonempty) : Fintype (stabilizer α s) where
  elems := s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩
  complete a := mem_map.2
    ⟨⟨_, (mem_mulStab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mulStab hs).2 a.2⟩, Subtype.ext rfl⟩

lemma card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    #s.mulStab ∣ #t.mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  rw [← coe_subset, coe_mulStab hs, coe_mulStab ht, SetLike.coe_subset_coe] at h
  let _ : Fintype (stabilizer α s) := fintypeStabilizerOfMulStab hs
  let _ : Fintype (stabilizer α t) := fintypeStabilizerOfMulStab ht
  convert Subgroup.card_dvd_of_le h using 1
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩)
    simp
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(t.mulStab.attach.map
      ⟨Subtype.map id fun _ ↦ (mem_mulStab ht).1, Subtype.map_injective _ injective_id⟩)
    simp

/-- A version of Lagrange's theorem. -/
lemma card_mulStab_mul_card_image_coe' (s t : Finset α)
    [DecidableEq (α ⧸ stabilizer α (t : Set α))] :
    #t.mulStab * #(Finset.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s) = #(s * t.mulStab) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ (Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s)
  have that : ↥(stabilizer α (t : Set α)) = ↥t.mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans ((Equiv.cast that).prodCongr (Equiv.refl _))
  rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab ht] at temp
  simpa only [coe_sort_coe, ← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe, mem_image, Set.mem_image, mem_coe, forall_const, eq_comm]
    using Fintype.card_congr temp

lemma card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #(Finset.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) (s * t)) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ <|
    Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) ↑(s * t)
  have that : ↥(stabilizer α (↑(s * t) : Set α)) = ↥(s * t).mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans <| (Equiv.cast that).prodCongr (Equiv.refl _)
  rw [preimage_image_quotientMk_mulStabilizer] at temp
  simpa [-coe_mul] using Fintype.card_congr temp

end Finset

end Erdos13_Erdos13MulStab

section Erdos13_Erdos13Kneser

/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/

/-
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`. Further,
if the inequality is strict, then we in fact have `|s + H| + |t + H| ≤ |s + t|`.

## Main declarations

* `Finset.mul_kneser`: Kneser's theorem.
* `Finset.mul_strict_kneser`: Strict Kneser theorem.

## References

* [Imre Ruzsa, *Sumsets and structure*][ruzsa2009]
* Matt DeVos, *A short proof of Kneser's addition theorem*
-/


open Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

namespace Finset

/- ### Auxiliary results -/

lemma mulStab_mul_ssubset_mulStab (hs₁ : (s ∩ a • C.mulStab).Nonempty)
    (ht₁ : (t ∩ b • C.mulStab).Nonempty) (hab : ¬(a * b) • C.mulStab ⊆ s * t) :
    (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊂ C.mulStab := by
  have hCne : C.Nonempty := by
    contrapose! hab
    simp only [hab, mulStab_empty, smul_finset_empty, empty_subset]
  obtain ⟨x, hx⟩ := hs₁
  obtain ⟨y, hy⟩ := ht₁
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx)
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy)
  have hsubset : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab := by
    have hxymem : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
    apply subset_trans (mulStab_subset_div_right hxymem)
    have : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (x * y) • C.mulStab := by
      apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
      rw [smul_mul_smul_comm]
      rw [← hac, ← had, smul_mul_smul_comm, smul_assoc]
      apply smul_finset_subset_smul_finset
      rw [← smul_smul]
      rw [mul_subset_iff]
      intro x hx y hy
      rw [smul_mulStab hd, smul_mulStab hc, mem_mulStab hCne, ← smul_smul,
        (mem_mulStab hCne).mp hy, (mem_mulStab hCne).mp hx]
    apply subset_trans (div_subset_div_right this) _
    simp [singleton_mul, div_eq_inv_mul, smul_smul, mul_assoc]
  have : (a * b) • C.mulStab = (a * c * (b * d)) • C.mulStab := by
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc, ←
      mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_cancel (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mulStab hc, smul_mulStab hd]
  have hsub : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (a * b) • C.mulStab := by
    apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  have hxy : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
  rw [this] at hsub
  rw [this] at hab
  obtain ⟨z, hz, hzst⟩ := not_subset.1 hab
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, ?_⟩
  rw [mem_mulStab' ⟨x * y, hxy⟩]
  push Not
  refine ⟨a * c * (b * d), by simp_all, ?_⟩
  rw [smul_eq_mul, mul_comm w, ← smul_eq_mul (b := w), hwz]
  exact notMem_mono (mul_subset_mul inter_subset_left inter_subset_left) hzst

lemma mulStab_union (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
    (hab : ¬(a * b) • C.mulStab ⊆ s * t)
    (hC : Disjoint C (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))) :
    (C ∪ s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab =
      (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab := by
  obtain rfl | hCne := C.eq_empty_or_nonempty
  · simp
  refine
    ((subset_inter (mulStab_mul_ssubset_mulStab hs₁ ht₁ hab).subset Subset.rfl).trans
          inter_mulStab_subset_mulStab_union).antisymm'
      fun x hx => ?_
  replace hx := (mem_mulStab <| (hs₁.mul ht₁).mono subset_union_right).mp hx
  rw [smul_finset_union] at hx
  suffices hxC : x ∈ C.mulStab by
    rw [(mem_mulStab hCne).mp hxC] at hx
    rw [mem_mulStab_iff_subset_smul_finset (hs₁.mul ht₁)]
    exact hC.symm.left_le_of_le_sup_left (le_sup_right.trans hx.ge)
  rw [mem_mulStab_iff_smul_finset_subset hCne]
  obtain h | h := disjoint_or_nonempty_inter (x • C) (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))
  · exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx)
  have hUn :
    ((C.biUnion fun y => x • y • C.mulStab) ∩
        (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))).Nonempty := by
    have : (x • C.biUnion fun y => y • C.mulStab) = C.biUnion fun y => x • y • C.mulStab :=
      biUnion_image
    simpa [← this]
  simp_rw [biUnion_inter, biUnion_nonempty, ← smul_assoc, smul_eq_mul] at hUn
  obtain ⟨y, hy, hyne⟩ := hUn
  have hxyCsubC : (x * y) • C.mulStab ⊆ x • C := by
    rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff]
    exact smul_finset_mulStab_subset hy
  have hxyC : Disjoint ((x * y) • C.mulStab) C := by
    convert disjoint_smul_finset_mulStab_mul_mulStab fun hxyC => _
    · exact C.mul_mulStab.symm
    rw [mul_mulStab] at hxyC
    exact hyne.not_disjoint (hC.mono_left hxyC)
  have hxysub : (x * y) • C.mulStab ⊆ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) :=
    hxyC.left_le_of_le_sup_left (hxyCsubC.trans <| subset_union_left.trans hx.subset)
  suffices s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊂ (a * b) • C.mulStab by
    have := (card_le_card hxysub).not_gt ((card_lt_card this).trans_eq ?_)
    cases this
    simp_rw [card_smul_finset]
  apply ssubset_of_subset_not_subset
  · refine (mul_subset_mul inter_subset_right inter_subset_right).trans ?_
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  · contrapose! hab
    exact hab.trans (mul_subset_mul inter_subset_left inter_subset_left)

lemma mul_aux1
    (ih : #(s' * (s' * t').mulStab) + #(t' * (s' * t').mulStab) ≤ #(s' * t') + #(s' * t').mulStab)
    (hconv : #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab)
    (hnotconv :
      #(C ∪ s' * t') + #(C ∪ s' * t').mulStab < #(s ∩ t) + #((s ∪ t) * (C ∪ s' * t').mulStab))
    (hCun : (C ∪ s' * t').mulStab = (s' * t').mulStab) (hdisj : Disjoint C (s' * t')) :
    (#((s ∪ t) * C.mulStab) - #((s ∪ t) * (s' * t').mulStab) : ℤ) <
      #C.mulStab - #(s' * (s' * t').mulStab) - #(t' * (s' * t').mulStab) := by
  set H := C.mulStab
  set H' := (s' * t').mulStab
  set C' := C ∪ s' * t'
  zify at hconv hnotconv ih
  calc
    (#((s ∪ t) * H) - #((s ∪ t) * H') : ℤ) < #C + #H - #(s ∩ t) - (#C' + #H' - #(s ∩ t)) := by
      rw [← hCun]
      linarith [hconv, hnotconv]
    _ = #H - #(s' * t') - #H' := by
      rw [card_union_of_disjoint hdisj, Int.natCast_add]
      abel
    _ ≤ #H - #(s' * H') - #(t' * H') := by linarith [ih]

lemma disjoint_smul_mulStab (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by
  suffices Disjoint (a • s.mulStab) (s * s.mulStab) by
    simpa [mul_comm, disjoint_comm, mulStab_mul]
  apply disjoint_smul_finset_mulStab_mul_mulStab
  rw [mul_comm, mulStab_mul]
  contrapose! has
  exact subset_trans has hst

lemma disjoint_mul_sub_card_le {a : α} (b : α) {s t C : Finset α} (has : a ∈ s)
    (hsC : Disjoint t (a • C.mulStab))
    (hst : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
        #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) =
        #(a • C.mulStab \
            (s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset
          (subset_trans (mul_subset_mul_left hst)
            (subset_trans (mul_subset_mul_right inter_subset_right) _)),
        card_smul_finset, Int.ofNat_sub]
      · apply le_trans (card_le_card (mul_subset_mul_left hst))
        apply
          le_trans (card_le_card inter_mul_subset)
            (le_of_le_of_eq (card_le_card inter_subset_right) _)
        rw [smul_mul_assoc, mulStab_mul_mulStab, card_smul_finset]
      · simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      gcongr #?_
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose! hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp (mem_union.mp hyst)
        contrapose! hsC
        exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

lemma inter_mul_sub_card_le {a : α} {s t C : Finset α} (has : a ∈ s)
    (hst : (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
        #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
            #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
          #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
        #(a • C.mulStab \
            ((s ∩ a • C.mulStab ∪ t ∩ a • C.mulStab) *
              (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset, Int.ofNat_sub (card_le_card _), card_smul_finset]
      · grw [union_mul, le_sub_iff_add_le, card_union_le]
        norm_num
      all_goals
        apply subset_trans (mul_subset_mul_left hst)
        rw [← union_inter_distrib_right]
        refine subset_trans (mul_subset_mul_right inter_subset_right) ?_
        simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      apply card_le_card
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose! hx'
      rw [← union_inter_distrib_right]
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd


private lemma card_mul_add_card_lt (hC : C.Nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hCst : C ⊆ s * t) (hCst' : Disjoint C (s' * t')) :
    #(s' * t') + #s' < #(s * t) + #s :=
  add_lt_add_of_lt_of_le
      (by
        rw [← tsub_pos_iff_lt, ← card_sdiff_of_subset (mul_subset_mul hs ht), card_pos]
        exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩)) <|
    card_le_card hs

/- ### Kneser's theorem -/

variable (s t)

/-- **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
stabilizer. -/
theorem mul_kneser :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by
  -- We're doing induction on `#(s * t) + #s` generalizing the group. This is a bit tricky
  -- in Lean.
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing α with | h n ih =>
  subst hn
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
  -- We distinguish whether `s * t` has trivial stabilizer.
  obtain hstab | hstab := ne_or_eq (s * t).mulStab 1
  · have image_coe_mul :
      ((s * t).image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) =
        s.image (↑) * t.image (↑) :=
      image_mul (QuotientGroup.mk' _ : α →* α ⧸ stabilizer α (↑(s * t) : Set α))
    suffices hineq :
      #(s * t).mulStab *
          (#(s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) +
              #(t.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) -  1) ≤
        #(s * t) by
    -- now to prove that `#(s * (s * t).mulStab) = #(s * t).mulStab * #(s.image (↑))` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
      rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mulStab_mul_card_image_coe',
        card_mulStab_mul_card_image_coe'] at hineq
      convert! hineq using 1
      exact add_comm _ _
    refine le_of_le_of_eq (mul_le_mul_right ?_ _) (card_mul_card_eq_mulStab_card_mul_coe s t).symm
    have := ih _ ?_ (s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) (t.image (↑)) rfl
    · classical
      simpa only [← image_coe_mul, mulStab_image_coe_quotient (hs.mul ht), mul_one,
        tsub_le_iff_right, card_one] using this
    rw [← image_coe_mul, card_mul_card_eq_mulStab_card_mul_coe]
    exact
      add_lt_add_of_lt_of_le
        (lt_mul_left ((hs.mul ht).image _).card_pos <|
          Finset.one_lt_card.2 ((hs.mul ht).mulStab_nontrivial.2 hstab))
        card_image_le
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ih ⊢
  replace ih := fun s' t' h => @ih _ h α _ _ s' t' rfl
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · rw [card_singleton, card_singleton_mul, add_comm]
  have : b / a ∉ t.mulStab := by
    refine fun h => hab (Eq.symm (eq_of_div_eq_one ?_))
    replace h := subset_mulStab_mul_right hs h
    rw [hstab, mem_one] at h
    exact h
  simp only [mem_mulStab' ht, smul_eq_mul, Classical.not_forall, exists_prop] at this
  obtain ⟨c, hc, hbac⟩ := this
  set t' := (a / c) • t with ht'
  clear_value t'
  rw [← inv_smul_eq_iff] at ht'
  subst ht'
  rename' t' => t
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel] at hc
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ← mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac
  rw [smul_finset_nonempty] at ht
  simp only [mul_smul_comm, mulStab_smul, card_smul_finset] at *
  have hst : (s ∩ t).Nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left, not_subset.2 ⟨_, hb, fun h => hbac <| inter_subset_right h⟩⟩
  clear! a b
  set convergent : Set (Finset α) :=
    {C | C ⊆ s * t ∧ #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab}
  have convergent_nonempty : convergent.Nonempty := by
    refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_left (card_le_card <|
      subset_mul_left _ <| one_mem_mulStab.2 <| hst.mul <| hs.mono subset_union_left) _).trans <|
        ih (s ∩ t) (s ∪ t) ?_⟩
    exact add_lt_add_of_le_of_lt (card_le_card inter_mul_union_subset) (card_lt_card hsts)
  let C := argminOn (fun C : Finset α => #C.mulStab) _ convergent_nonempty
  set H := C.mulStab with hH
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argminOn_mem _ _ _
  have hCmin (D : Finset α) (hDH : D.mulStab ⊂ H) : D ∉ convergent := fun hD ↦
    (card_lt_card hDH).not_ge <| argminOn_le (fun D : Finset α => #D.mulStab) _ hD
  clear_value C
  clear convergent_nonempty
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp [hst.ne_empty] at hCcard
  -- If the stabilizer of `C` is trivial, then
  -- `#s + #t - 1 = #(s ∩ t) + #(s ∪ t) - 1 = ≤ #C ≤ #(s * t)`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mulStab.2 hC)
  · simp only [hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard
    grw [hCcard, hCst]
  exfalso
  have : ¬s * t * H ⊆ s * t := by
    rw [mul_subset_left_iff (hs.mul ht), hstab, ← coe_subset, coe_one]
    exact hCstab.coe.not_subset_singleton
  simp_rw [mul_subset_iff_left, Classical.not_forall, mem_mul] at this
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hab⟩ := this
  set s₁ := s ∩ a • H with hs₁
  set s₂ := s ∩ b • H with hs₂
  set t₁ := t ∩ b • H with ht₁
  set t₂ := t ∩ a • H with ht₂
  have hs₁s : s₁ ⊆ s := inter_subset_left
  have hs₂s : s₂ ⊆ s := inter_subset_left
  have ht₁t : t₁ ⊆ t := inter_subset_left
  have ht₂t : t₂ ⊆ t := inter_subset_left
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hs₁ne : s₁.Nonempty := ⟨_, has₁⟩
  have ht₁ne : t₁.Nonempty := ⟨_, hbt₁⟩
  set C₁ := C ∪ s₁ * t₁
  set C₂ := C ∪ s₂ * t₂
  set H₁ := (s₁ * t₁).mulStab with hH₁
  set H₂ := (s₂ * t₂).mulStab
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t)
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t)
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm, mul_comm s₂ t₂]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_mulStab hCst hab)
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_mulStab hCst hab)
  have hst₁ : #(s₁ * t₁) + #s₁ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁
  have hst₂ : #(s₂ * t₂) + #s₂ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂
  have hC₁stab : C₁.mulStab = H₁ := mulStab_union hs₁ne ht₁ne hab hCst₁
  have hH₁H : H₁ ⊂ H := mulStab_mul_ssubset_mulStab hs₁ne ht₁ne hab
  have aux1₁ :=
    mul_aux1 (ih _ _ hst₁) hCcard
      (not_le.1 fun h => hCmin _ (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hCst₁
  obtain ht₂ | ht₂ne := t₂.eq_empty_or_nonempty
  · have aux₁_contr :=
      disjoint_mul_sub_card_le b (hs₁s has₁) (disjoint_iff_inter_eq_empty.2 ht₂) hH₁H.subset
    linarith [aux1₁, aux₁_contr, Int.natCast_nonneg #(t₁ * (s₁ * t₁).mulStab)]
  obtain hs₂ | hs₂ne := s₂.eq_empty_or_nonempty
  · have aux1₁_contr :
      (#C.mulStab : ℤ) - #(t₁ * (s₁ * t₁).mulStab) ≤
        #((s ∪ t) * C.mulStab) - #((s ∪ t) * (s₁ * t₁).mulStab) := by
      simpa [union_comm, mul_comm s₁ t₁] using
        disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.2 hs₂)
          (by rw [mul_comm]; exact hH₁H.subset)
    linarith [aux1₁, aux1₁_contr, Int.natCast_nonneg #(s₁ * (s₁ * t₁).mulStab)]
  have hC₂stab : C₂.mulStab = H₂ := mulStab_union hs₂ne ht₂ne (by rwa [mul_comm]) hCst₂
  have hH₂H : H₂ ⊂ H := mulStab_mul_ssubset_mulStab hs₂ne ht₂ne (by rwa [mul_comm])
  have aux1₂ :=
    mul_aux1 (ih _ _ hst₂) hCcard
      (not_le.1 fun h => hCmin _ (hC₂stab.trans_ssubset hH₂H) ⟨hC₂st, h⟩) hC₂stab hCst₂
  obtain habH | habH := eq_or_ne (a • H) (b • H)
  · rw [hH₁, hs₁, ht₁, ← habH, hH] at hH₁H
    refine aux1₁.not_ge ?_
    simp only [hs₁, ht₁, ← habH, inter_mul_sub_card_le (hs₁s has₁) hH₁H.subset, H]
  -- temporarily skipping deduction of inequality (2)
  set S := a • H \ (s₁ ∪ t₂) with hS
  set T := b • H \ (s₂ ∪ t₁) with hT
  have hST : Disjoint S T :=
    (C.pairwiseDisjoint_smul_finset_mulStab (Set.mem_range_self _) (Set.mem_range_self _)
          habH).mono
      sdiff_le sdiff_le
  have hSst : S ⊆ a • H \ (s ∪ t) := by
    simp only [hS, hs₁, ht₂, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hTst : T ⊆ b • H \ (s ∪ t) := by
    simp only [hT, hs₂, ht₁, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hSTst : Disjoint (S ∪ T) (s ∪ t) := (subset_sdiff.1 hSst).2.sup_left (subset_sdiff.1 hTst).2
  have hstconv : s * t ∉ convergent := by
    apply hCmin (s * t)
    rw [hstab]
    refine (hC.mulStab_nontrivial.mp hCstab).symm.ssubset_of_subset ?_
    simp only [one_subset, one_mem_mulStab, hC]
  simp only [Set.mem_ofPred_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
    convergent] at hstconv
  zify at hstconv
  have hSTcard : (#S : ℤ) + #T + #(s ∪ t) ≤ #((s ∪ t) * H) := by
    norm_cast
    conv_lhs => rw [← card_union_of_disjoint hST, ← card_union_of_disjoint hSTst, ← mul_one (s ∪ t)]
    refine card_le_card
      (union_subset (union_subset ?_ ?_) <| mul_subset_mul_left <| one_subset.2 (one_mem_mulStab.mpr hC))
    · exact hSst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_left _ ha)
    · exact hTst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_right _ hb)
  have hH₁ne : H₁.Nonempty := (hs₁ne.mul ht₁ne).mulStab
  have hH₂ne : H₂.Nonempty := (hs₂ne.mul ht₂ne).mulStab
  -- Now we prove inequality (2)
  have aux2₁ : (#s₁ : ℤ) + #t₁ + #H₁ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₁H.subset).trans_lt aux1₁) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₁ne.mul ht₁ne) hH₁H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    gcongr _ - (Nat.cast ?_ + Nat.cast ?_) <;> exact card_le_card_mul_right hH₁ne
  have aux2₂ : (#s₂ : ℤ) + #t₂ + #H₂ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₂H.subset).trans_lt aux1₂) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₂ne.mul ht₂ne) hH₂H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    exact sub_le_sub_left (add_le_add (Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) <|
      Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) _
  -- Now we deduce inequality (3) using the above lemma in addition to the facts that `s * t` is not
  -- convergent and then induction hypothesis applied to `sᵢ` and `tᵢ`
  have aux3₁ : (#S : ℤ) + #T + #s₁ + #t₁ - #H₁ < #H :=
    calc
      (#S : ℤ) + #T + #s₁ + #t₁ - #H₁
        < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₁ * t₁) := by
        have ih₁ :=
          (add_le_add (card_le_card_mul_right hH₁ne) <| card_le_card_mul_right hH₁ne).trans
            (ih _ _ hst₁)
        zify at ih₁
        linarith [hstconv, ih₁]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₁ * t₁) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₁] using card_le_card hC₁st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux3₂ : (#S : ℤ) + #T + #s₂ + #t₂ - #H₂ < #H :=
    calc
      (#S : ℤ) + #T + #s₂ + #t₂ - #H₂
       < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₂ * t₂) := by
        have ih₂ :=
          (add_le_add (card_le_card_mul_right hH₂ne) <| card_le_card_mul_right hH₂ne).trans
            (ih _ _ hst₂)
        zify at hstconv ih₂
        linarith [ih₂]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₂ * t₂) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₂] using card_le_card hC₂st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux4₁ : #H ≤ #S + (#s₁ + #t₂) := by
    grw [← card_smul_finset a H, card_le_card_sdiff_add_card, card_union_le]
  have aux4₂ : #H ≤ #T + (#s₂ + #t₁) := by
    grw [← card_smul_finset b H, card_le_card_sdiff_add_card, card_union_le]
  linarith [aux2₁, aux2₂, aux3₁, aux3₂, aux4₁, aux4₂]

/-- The strict version of **Kneser's multiplication theorem**. If the LHS of `Finset.mul_kneser`
does not equal the RHS, then it is in fact much smaller. -/
lemma mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) :=
  Nat.le_of_lt_add_of_dvd h
      ((card_mulStab_dvd_card_mul_mulStab _ _).add <| card_mulStab_dvd_card_mul_mulStab _ _) <|
    card_mulStab_dvd_card _

end Finset

end Erdos13_Erdos13Kneser

namespace Finset

open scoped Pointwise

/-- The finite stabilizer of an additive set, via the multiplicative type tag. -/
abbrev addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) : Finset G :=
  mulStab (α := Multiplicative G) S

lemma Nonempty.zero_mem_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    {S : Finset G} (hS : S.Nonempty) : 0 ∈ S.addStab :=
  (one_mem_mulStab (α := Multiplicative G)).2 hS

lemma coe_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    {S : Finset G} (hS : S.Nonempty) :
    (S.addStab : Set G) = AddAction.stabilizer G (S : Set G) :=
  coe_mulStab (α := Multiplicative G) hS

lemma add_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) : S + S.addStab = S :=
  mul_mulStab (α := Multiplicative G) S

/-- Kneser's bound for additive groups. -/
theorem add_kneser {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S T : Finset G) :
    (S + (S + T).addStab).card + (T + (S + T).addStab).card ≤
      (S + T).card + (S + T).addStab.card :=
  mul_kneser (α := Multiplicative G) S T

end Finset

section Erdos13_Erdos13Additive

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/




open Finset Nat
open scoped Pointwise

namespace Erdos13Additive

/- ## Residue representatives for Ruzsa's diameter estimate -/

def modImage (S : Finset ℕ) (v : ℕ) : Finset (ZMod v) :=
  S.image fun x : ℕ ↦ (x : ZMod v)

def modFiber (S : Finset ℕ) (v : ℕ) (c : ZMod v) : Finset ℕ :=
  S.filter fun x ↦ (x : ZMod v) = c

@[simp] lemma mem_modImage {S : Finset ℕ} {v : ℕ} {c : ZMod v} :
    c ∈ modImage S v ↔ ∃ x ∈ S, (x : ZMod v) = c := by
  simp [modImage]

@[simp] lemma mem_modFiber {S : Finset ℕ} {v x : ℕ} {c : ZMod v} :
    x ∈ modFiber S v c ↔ x ∈ S ∧ (x : ZMod v) = c := by
  simp [modFiber]

lemma modFiber_nonempty {S : Finset ℕ} {v : ℕ} {c : ZMod v}
    (hc : c ∈ modImage S v) : (modFiber S v c).Nonempty := by
  obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
  exact ⟨x, mem_modFiber.mpr ⟨hx, hxc⟩⟩

/-- The least integer of `S` in a residue represented by `S`. -/
noncomputable def residueRep (S : Finset ℕ) (v : ℕ)
    (c : ↑(modImage S v)) : ℕ :=
  (modFiber S v c.1).min' (modFiber_nonempty c.2)

lemma residueRep_mem (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    residueRep S v c ∈ S := by
  exact (mem_modFiber.mp ((modFiber S v c.1).min'_mem (modFiber_nonempty c.2))).1

lemma residueRep_cast (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    ((residueRep S v c : ℕ) : ZMod v) = c.1 := by
  exact (mem_modFiber.mp ((modFiber S v c.1).min'_mem (modFiber_nonempty c.2))).2

lemma residueRep_le {S : Finset ℕ} {v z : ℕ} (c : ↑(modImage S v))
    (hz : z ∈ S) (hzc : (z : ZMod v) = c.1) : residueRep S v c ≤ z := by
  apply (modFiber S v c.1).min'_le z
  exact mem_modFiber.mpr ⟨hz, hzc⟩

lemma residueRep_injective (S : Finset ℕ) (v : ℕ) :
    Function.Injective (residueRep S v) := by
  intro c d hcd
  apply Subtype.ext
  rw [← residueRep_cast S v c, ← residueRep_cast S v d, hcd]

noncomputable def residueReps (S : Finset ℕ) (v : ℕ) : Finset ℕ :=
  (modImage S v).attach.image (residueRep S v)

lemma card_residueReps (S : Finset ℕ) (v : ℕ) :
    (residueReps S v).card = (modImage S v).card := by
  rw [residueReps, card_image_of_injective _ (residueRep_injective S v)]
  simp

lemma residueReps_subset (S : Finset ℕ) (v : ℕ) : residueReps S v ⊆ S := by
  intro z hz
  simp only [residueReps, mem_image] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  exact residueRep_mem S v c

/-- Reduction modulo `v` commutes with a natural-number sumset. -/
lemma modImage_add (A B : Finset ℕ) (v : ℕ) :
    modImage (A + B) v = modImage A v + modImage B v := by
  ext c
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc
    simp only [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    apply Finset.mem_add.mpr
    refine ⟨(a : ZMod v), mem_modImage.mpr ⟨a, ha, rfl⟩,
      (b : ZMod v), mem_modImage.mpr ⟨b, hb, rfl⟩, ?_⟩
    simpa using hzc
  · intro hc
    simp only [Finset.mem_add] at hc
    obtain ⟨a, ha, b, hb, rfl⟩ := hc
    obtain ⟨x, hx, hxa⟩ := mem_modImage.mp ha
    obtain ⟨y, hy, hyb⟩ := mem_modImage.mp hb
    apply mem_modImage.mpr
    refine ⟨x + y, Finset.add_mem_add hx hy, ?_⟩
    push_cast
    rw [hxa, hyb]

/-- The `v`-shifted copy of `A` used for the extra lift in every residue
represented by `A`. -/
def shiftedBy (A : Finset ℕ) (v : ℕ) : Finset ℕ := A.image fun a ↦ a + v

lemma card_shiftedBy (A : Finset ℕ) (v : ℕ) : (shiftedBy A v).card = A.card := by
  rw [shiftedBy, Finset.card_image_of_injective]
  intro x y h
  change x + v = y + v at h
  omega

lemma shiftedBy_subset_add {A B : Finset ℕ} {v : ℕ} (hvB : v ∈ B) :
    shiftedBy A v ⊆ A + B := by
  intro z hz
  simp only [shiftedBy, mem_image] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  exact Finset.add_mem_add ha hvB

lemma residueReps_disjoint_shiftedBy {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (_huv : u ≤ v) (hv : 0 < v)
    (_hA0 : 0 ∈ A) (hB0 : 0 ∈ B) :
    Disjoint (residueReps (A + B) v) (shiftedBy A v) := by
  rw [Finset.disjoint_left]
  intro z hzR hzE
  simp only [shiftedBy, mem_image] at hzE
  obtain ⟨a, ha, rfl⟩ := hzE
  simp only [residueReps, mem_image] at hzR
  obtain ⟨c, hc, hrep⟩ := hzR
  have hcast : c.1 = (a : ZMod v) := by
    rw [← residueRep_cast (A + B) v c, hrep]
    simp
  let ca : ↑(modImage (A + B) v) :=
    ⟨(a : ZMod v), mem_modImage.mpr ⟨a, Finset.add_mem_add ha hB0, rfl⟩⟩
  have hca : c = ca := by
    apply Subtype.ext
    exact hcast
  subst c
  have hle : residueRep (A + B) v ca ≤ a :=
    residueRep_le ca (Finset.add_mem_add ha hB0) rfl
  have haU := mem_Icc.mp (hA ha)
  dsimp [ca] at hrep hle
  omega

/-- Ruzsa's basic lift count, equation (4.3): there is one sum for each
sum residue and one further sum for each member of the smaller-diameter
summand. -/
lemma card_modImage_add_add_card_le {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (huv : u ≤ v) (hv : 0 < v) (hA0 : 0 ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B) :
    (modImage (A + B) v).card + A.card ≤ (A + B).card := by
  have hR := residueReps_subset (A + B) v
  have hE := shiftedBy_subset_add (A := A) hvB
  have hdisj := residueReps_disjoint_shiftedBy hA huv hv hA0 hB0
  rw [← card_residueReps (A + B) v, ← card_shiftedBy A v,
    ← card_union_of_disjoint hdisj]
  exact card_le_card (union_subset hR hE)

lemma natCast_injOn_Ico {v : ℕ} :
    Set.InjOn (fun x : ℕ ↦ (x : ZMod v)) (Ico 0 v) := by
  intro x hx y hy hxy
  have hx' := mem_Ico.mp hx
  have hy' := mem_Ico.mp hy
  have hv : 0 < v := by omega
  have hvx := congrArg ZMod.val hxy
  rw [ZMod.val_natCast_of_lt hx'.2, ZMod.val_natCast_of_lt hy'.2] at hvx
  exact hvx

lemma card_modImage_eq_card_of_lt {S : Finset ℕ} {u v : ℕ}
    (hS : S ⊆ Icc 0 u) (huv : u < v) : (modImage S v).card = S.card := by
  apply card_image_iff.mpr
  apply (natCast_injOn_Ico (v := v)).mono
  intro x hx
  have hx' := mem_Icc.mp (hS hx)
  exact mem_Ico.mpr ⟨hx'.1, hx'.2.trans_lt huv⟩

lemma erase_top_subset_Ico {S : Finset ℕ} {v : ℕ} (hS : S ⊆ Icc 0 v) :
    S.erase v ⊆ Ico 0 v := by
  intro x hx
  have hxS := mem_of_mem_erase hx
  have hxI := mem_Icc.mp (hS hxS)
  have hxne := ne_of_mem_erase hx
  exact mem_Ico.mpr ⟨hxI.1, lt_of_le_of_ne hxI.2 hxne⟩

lemma modImage_erase_top {S : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (h0 : 0 ∈ S) (_hvS : v ∈ S) : modImage (S.erase v) v = modImage S v := by
  ext c
  constructor
  · intro hc
    obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
    exact mem_modImage.mpr ⟨x, mem_of_mem_erase hx, hxc⟩
  · intro hc
    obtain ⟨x, hx, hxc⟩ := mem_modImage.mp hc
    by_cases hxv : x = v
    · subst x
      apply mem_modImage.mpr
      refine ⟨0, mem_erase.mpr ⟨by omega, h0⟩, ?_⟩
      simpa using hxc
    · exact mem_modImage.mpr ⟨x, mem_erase.mpr ⟨hxv, hx⟩, hxc⟩

lemma card_modImage_add_one_eq {S : Finset ℕ} {v : ℕ} (hv : 0 < v)
    (hS : S ⊆ Icc 0 v) (h0 : 0 ∈ S) (hvS : v ∈ S) :
    (modImage S v).card + 1 = S.card := by
  have hinj : Set.InjOn (fun x : ℕ ↦ (x : ZMod v)) (S.erase v) :=
    (natCast_injOn_Ico (v := v)).mono (erase_top_subset_Ico hS)
  rw [← modImage_erase_top hv h0 hvS, modImage, card_image_iff.mpr hinj,
    card_erase_of_mem hvS]
  have : 0 < S.card := card_pos.mpr ⟨v, hvS⟩
  omega

lemma zero_mem_modImage {S : Finset ℕ} {v : ℕ} (h0 : 0 ∈ S) :
    (0 : ZMod v) ∈ modImage S v := mem_modImage.mpr ⟨0, h0, by simp⟩

lemma zero_mem_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) : 0 ∈ C.addStab := by
  exact hC.zero_mem_addStab

lemma addStab_add_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) {x y : G}
    (hx : x ∈ C.addStab) (hy : y ∈ C.addStab) : x + y ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at hx hy ⊢
  exact (AddAction.stabilizer G (C : Set G)).add_mem hx hy

lemma addStab_neg_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C : Finset G} (hC : C.Nonempty) {x : G}
    (hx : x ∈ C.addStab) : -x ∈ C.addStab := by
  rw [← mem_coe, coe_addStab hC] at hx ⊢
  exact (AddAction.stabilizer G (C : Set G)).neg_mem hx

/-- If all residues of a set of integers lie in a subgroup and their
integer gcd is one, that subgroup is all of `ZMod v`. -/
lemma stabilizer_eq_top_of_gcd_one {S : Finset ℕ} {v : ℕ}
    (hgcd : S.gcd (fun n ↦ (n : ℤ)) = 1)
    (K : AddSubgroup (ZMod v)) (hS : ∀ n ∈ S, (n : ZMod v) ∈ K) : K = ⊤ := by
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul S (fun n ↦ (n : ℤ))
  have hterms : ∀ n ∈ S, (n : ZMod v) * (g n : ZMod v) ∈ K := by
    intro n hn
    have hnK := hS n hn
    have hz := K.zsmul_mem hnK (g n)
    simpa [smul_eq_mul, mul_comm] using hz
  have hsum : ((∑ n ∈ S, (n : ℤ) * g n : ℤ) : ZMod v) ∈ K := by
    push_cast
    exact K.sum_mem fun n hn ↦ hterms n hn
  have hone : (1 : ZMod v) ∈ K := by
    rw [hgcd] at hg
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod v)) hg
    norm_num at hcast
    rw [hcast]
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using hsum
  apply (AddSubgroup.eq_top_iff' K).mpr
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x
  rw [← hz]
  simpa [smul_eq_mul] using K.zsmul_mem hone z

/- ## The refined lift across a missing stabilizer coset -/

/-- The least integer representative of a residue of `S` which is outside
the prescribed residue set `D`. -/
noncomputable def residueRepOutside (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) (c : ↑(modImage S v \ D)) : ℕ :=
  residueRep S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

/-- One least representative for every residue of `S` outside `D`. -/
noncomputable def residueRepsOutside (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  (modImage S v \ D).attach.image (residueRepOutside S v D)

lemma residueRepOutside_mem (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v))
    (c : ↑(modImage S v \ D)) : residueRepOutside S v D c ∈ S := by
  exact residueRep_mem S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

lemma residueRepOutside_cast (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v))
    (c : ↑(modImage S v \ D)) :
    ((residueRepOutside S v D c : ℕ) : ZMod v) = c.1 := by
  exact residueRep_cast S v ⟨c.1, (mem_sdiff.mp c.2).1⟩

lemma residueRepOutside_injective (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    Function.Injective (residueRepOutside S v D) := by
  intro c e hce
  apply Subtype.ext
  rw [← residueRepOutside_cast S v D c,
    ← residueRepOutside_cast S v D e, hce]

lemma card_residueRepsOutside (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    (residueRepsOutside S v D).card = (modImage S v \ D).card := by
  rw [residueRepsOutside,
    card_image_of_injective _ (residueRepOutside_injective S v D)]
  simp

lemma residueRepsOutside_subset (S : Finset ℕ) (v : ℕ) (D : Finset (ZMod v)) :
    residueRepsOutside S v D ⊆ S := by
  intro z hz
  simp only [residueRepsOutside, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact residueRepOutside_mem S v D c

lemma cast_not_mem_of_mem_residueRepsOutside {S : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} (hz : z ∈ residueRepsOutside S v D) :
    (z : ZMod v) ∉ D := by
  simp only [residueRepsOutside, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  rw [residueRepOutside_cast]
  exact (mem_sdiff.mp c.2).2

/-- Sums in a chosen residue set. -/
def sumsOverResidues (A B : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  (A + B).filter fun z ↦ (z : ZMod v) ∈ D

@[simp] lemma mem_sumsOverResidues {A B : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} :
    z ∈ sumsOverResidues A B v D ↔ z ∈ A + B ∧ (z : ZMod v) ∈ D := by
  simp [sumsOverResidues]

/-- Ruzsa's refined lift: besides one representative outside `D`, retain
the shifted copy of `A` and every actual sum whose residue lies in `D`.
When `D` misses all residues of `A`, these three collections are disjoint. -/
lemma card_modImage_add_add_card_add_fiber_le {A B : Finset ℕ} {u v : ℕ}
    (D : Finset (ZMod v))
    (hA : A ⊆ Icc 0 u) (huv : u ≤ v) (hv : 0 < v) (hA0 : 0 ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hD : D ⊆ modImage (A + B) v)
    (hDA : Disjoint D (modImage A v)) :
    (modImage (A + B) v).card + A.card +
        (sumsOverResidues A B v D).card ≤ (A + B).card + D.card := by
  let R := residueRepsOutside (A + B) v D
  let E := shiftedBy A v
  let F := sumsOverResidues A B v D
  have hRS : R ⊆ A + B := residueRepsOutside_subset (A + B) v D
  have hES : E ⊆ A + B := shiftedBy_subset_add hvB
  have hFS : F ⊆ A + B := filter_subset _ _
  have hRE : Disjoint R E := by
    apply Disjoint.mono_left _ (residueReps_disjoint_shiftedBy hA huv hv hA0 hB0)
    intro z hz
    change z ∈ residueRepsOutside (A + B) v D at hz
    simp only [residueRepsOutside, residueReps, mem_image] at hz ⊢
    obtain ⟨c, -, rfl⟩ := hz
    exact ⟨⟨c.1, (mem_sdiff.mp c.2).1⟩, by simp,
      rfl⟩
  have hRF : Disjoint R F := by
    rw [Finset.disjoint_left]
    intro z hzR hzF
    exact (cast_not_mem_of_mem_residueRepsOutside hzR)
      (mem_sumsOverResidues.mp hzF).2
  have hEF : Disjoint E F := by
    rw [Finset.disjoint_left]
    intro z hzE hzF
    simp only [E, shiftedBy, mem_image] at hzE
    obtain ⟨a, ha, rfl⟩ := hzE
    have haD : (a : ZMod v) ∈ D := by
      simpa using (mem_sumsOverResidues.mp hzF).2
    exact (Finset.disjoint_left.mp hDA) haD
      (mem_modImage.mpr ⟨a, ha, rfl⟩)
  have hREF : Disjoint (R ∪ E) F := by
    rw [Finset.disjoint_left]
    intro z hz hzF
    rcases mem_union.mp hz with hzR | hzE
    · exact (Finset.disjoint_left.mp hRF) hzR hzF
    · exact (Finset.disjoint_left.mp hEF) hzE hzF
  have hU : (R ∪ E) ∪ F ⊆ A + B := union_subset (union_subset hRS hES) hFS
  have hcardU := card_le_card hU
  rw [card_union_of_disjoint hREF, card_union_of_disjoint hRE,
    card_residueRepsOutside, card_shiftedBy] at hcardU
  have hsplit := card_sdiff_add_card_eq_card hD
  change (modImage (A + B) v \ D).card + D.card =
    (modImage (A + B) v).card at hsplit
  change (modImage (A + B) v).card + A.card + F.card ≤
    (A + B).card + D.card
  omega

/-- The integers of `S` whose residues belong to `D`. -/
def residueFiberSet (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) : Finset ℕ :=
  S.filter fun z ↦ (z : ZMod v) ∈ D

@[simp] lemma mem_residueFiberSet {S : Finset ℕ} {v : ℕ}
    {D : Finset (ZMod v)} {z : ℕ} :
    z ∈ residueFiberSet S v D ↔ z ∈ S ∧ (z : ZMod v) ∈ D := by
  simp [residueFiberSet]

lemma modImage_residueFiberSet (S : Finset ℕ) (v : ℕ)
    (D : Finset (ZMod v)) :
    modImage (residueFiberSet S v D) v = modImage S v ∩ D := by
  ext c
  constructor
  · intro hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc
    have hz' := mem_residueFiberSet.mp hz
    exact mem_inter.mpr ⟨mem_modImage.mpr ⟨z, hz'.1, hzc⟩, by simpa [hzc] using hz'.2⟩
  · intro hc
    have hc' := mem_inter.mp hc
    obtain ⟨z, hz, hzc⟩ := mem_modImage.mp hc'.1
    apply mem_modImage.mpr
    exact ⟨z, mem_residueFiberSet.mpr ⟨hz, by simpa [hzc] using hc'.2⟩, hzc⟩

lemma card_modImage_le (S : Finset ℕ) (v : ℕ) :
    (modImage S v).card ≤ S.card := by
  exact card_image_le

/-- Saturating a residue set by `H` fills the coset through any occupied
residue.  The only overcount in adjoining that coset is paid for by the
corresponding integer fiber. -/
lemma card_modImage_add_card_le_saturation_add_fiber
    {S : Finset ℕ} {v : ℕ} {H : Finset (ZMod v)} {a : ZMod v}
    (h0 : (0 : ZMod v) ∈ H) (ha : a ∈ modImage S v) :
    (modImage S v).card + H.card ≤
      (modImage S v + H).card +
        (residueFiberSet S v (a +ᵥ H)).card := by
  let X := modImage S v
  let D := a +ᵥ H
  have hX : X ⊆ X + H := by
    intro x hx
    have : x + 0 ∈ X + H := Finset.add_mem_add hx h0
    simpa using this
  have hD : D ⊆ X + H := vadd_finset_subset_add ha
  have hU : X ∪ D ⊆ X + H := union_subset hX hD
  have hinter : (X ∩ D).card ≤ (residueFiberSet S v D).card := by
    rw [← modImage_residueFiberSet]
    exact card_modImage_le _ _
  have hcardU := card_le_card hU
  have hcardD : D.card = H.card := card_vadd_finset a H
  have hIE := card_union_add_card_inter X D
  change X.card + H.card ≤ (X + H).card + (residueFiberSet S v D).card
  omega

lemma disjoint_vadd_add_of_not_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {X H : Finset G} {c : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hc : c ∉ X + H) :
    Disjoint (c +ᵥ H) (X + H) := by
  rw [Finset.disjoint_left]
  intro z hzD hzX
  obtain ⟨h₂, hh₂, hh₂z⟩ := mem_vadd_finset.mp hzD
  obtain ⟨x, hx, h₁, hh₁, hh₁z⟩ := mem_add.mp hzX
  change c + h₂ = z at hh₂z
  apply hc
  apply mem_add.mpr
  refine ⟨x, hx, h₁ + -h₂, hadd h₁ hh₁ (-h₂) (hneg h₂ hh₂), ?_⟩
  calc
    x + (h₁ + -h₂) = (x + h₁) + -h₂ := by abel
    _ = z + -h₂ := by rw [hh₁z]
    _ = (c + h₂) + -h₂ := by rw [hh₂z]
    _ = c := by abel

lemma disjoint_self_vadd_of_not_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    {H : Finset G} {b : G}
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (hneg : ∀ x ∈ H, -x ∈ H) (hb : b ∉ H) :
    Disjoint H (b +ᵥ H) := by
  rw [Finset.disjoint_left]
  intro z hzH hzD
  obtain ⟨h, hh, hhz⟩ := mem_vadd_finset.mp hzD
  change b + h = z at hhz
  apply hb
  have : z + -h ∈ H := hadd z hzH (-h) (hneg h hh)
  convert this using 1
  rw [← hhz]
  abel

lemma residueFiberSet_add_subset_sumsOverResidues
    {A B : Finset ℕ} {v : ℕ} {H : Finset (ZMod v)} {a b c : ZMod v}
    (hc : a + b = c)
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) :
    residueFiberSet A v (a +ᵥ H) + residueFiberSet B v (b +ᵥ H) ⊆
      sumsOverResidues A B v (c +ᵥ H) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
  have hx' := mem_residueFiberSet.mp hx
  have hy' := mem_residueFiberSet.mp hy
  obtain ⟨h₁, hh₁, ha⟩ := mem_vadd_finset.mp hx'.2
  obtain ⟨h₂, hh₂, hb⟩ := mem_vadd_finset.mp hy'.2
  change a + h₁ = (x : ZMod v) at ha
  change b + h₂ = (y : ZMod v) at hb
  apply mem_sumsOverResidues.mpr
  constructor
  · exact Finset.add_mem_add hx'.1 hy'.1
  · apply mem_vadd_finset.mpr
    refine ⟨h₁ + h₂, hadd h₁ hh₁ h₂ hh₂, ?_⟩
    change c + (h₁ + h₂) = ((x + y : ℕ) : ZMod v)
    push_cast
    rw [← ha, ← hb, ← hc]
    abel

/- ## Ruzsa's diameter estimate -/

/-- Ruzsa's modular diameter estimate in the normalized situation.  The
set of all elements of the two summands has integer gcd one. -/
theorem ruzsa_normalized_diameter_bound
    {A B : Finset ℕ} {u v : ℕ}
    (hA : A ⊆ Icc 0 u) (hB : B ⊆ Icc 0 v) (huv : u ≤ v)
    (hv : 0 < v) (hA0 : 0 ∈ A) (huA : u ∈ A)
    (hB0 : 0 ∈ B) (hvB : v ∈ B)
    (hgcd : (A ∪ B).gcd (fun n ↦ (n : ℤ)) = 1) :
    min (A.card + v)
      (A.card + B.card + min A.card B.card - 3) ≤ (A + B).card := by
  let _ : NeZero v := ⟨Nat.ne_of_gt hv⟩
  let A₀ := modImage A v
  let B₀ := modImage B v
  let C₀ := A₀ + B₀
  let H := C₀.addStab
  have hA₀zero : (0 : ZMod v) ∈ A₀ := zero_mem_modImage hA0
  have hB₀zero : (0 : ZMod v) ∈ B₀ := zero_mem_modImage hB0
  have hA₀ne : A₀.Nonempty := ⟨0, hA₀zero⟩
  have hB₀ne : B₀.Nonempty := ⟨0, hB₀zero⟩
  have hC₀ne : C₀.Nonempty := by
    rw [Finset.add_nonempty]
    exact ⟨hA₀ne, hB₀ne⟩
  have hHzero : (0 : ZMod v) ∈ H := zero_mem_addStab hC₀ne
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact addStab_add_mem hC₀ne hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact addStab_neg_mem hC₀ne hx
  have hA₀C₀ : A₀ ⊆ C₀ := by
    intro a ha
    exact mem_add.mpr ⟨a, ha, 0, hB₀zero, by simp⟩
  have hB₀C₀ : B₀ ⊆ C₀ := by
    intro b hb
    exact mem_add.mpr ⟨0, hA₀zero, b, hb, by simp⟩
  have hA₀sat : A₀ ⊆ A₀ + H := by
    intro a ha
    exact mem_add.mpr ⟨a, ha, 0, hHzero, by simp⟩
  have hB₀sat : B₀ ⊆ B₀ + H := by
    intro b hb
    exact mem_add.mpr ⟨b, hb, 0, hHzero, by simp⟩
  have hA₀H_C₀ : A₀ + H ⊆ C₀ := by
    have hs := add_subset_add hA₀C₀ (subset_rfl : H ⊆ H)
    change A₀ + H ⊆ C₀ + H at hs
    simpa only [H, add_addStab] using hs
  have hB₀H_C₀ : B₀ + H ⊆ C₀ := by
    have hs := add_subset_add hB₀C₀ (subset_rfl : H ⊆ H)
    change B₀ + H ⊆ C₀ + H at hs
    simpa only [H, add_addStab] using hs
  have hB₀card : B₀.card + 1 = B.card := by
    exact card_modImage_add_one_eq hv hB hB0 hvB
  have hA₀card : A.card ≤ A₀.card + 1 := by
    by_cases hlt : u < v
    · have h := card_modImage_eq_card_of_lt hA hlt
      change A₀.card = A.card at h
      omega
    · have huv' : u = v := by omega
      subst u
      have h := card_modImage_add_one_eq hv hA hA0 huA
      change A₀.card + 1 = A.card at h
      omega
  have hC₀image : C₀ = modImage (A + B) v := by
    change modImage A v + modImage B v = modImage (A + B) v
    exact (modImage_add A B v).symm
  have hlift : C₀.card + A.card ≤ (A + B).card := by
    rw [hC₀image]
    exact card_modImage_add_add_card_le hA huv hv hA0 hB0 hvB
  have hkneser : (A₀ + H).card + (B₀ + H).card ≤ C₀.card + H.card := by
    have hk := Finset.add_kneser A₀ B₀
    change (A₀ + C₀.addStab).card + (B₀ + C₀.addStab).card ≤
      C₀.card + C₀.addStab.card at hk
    exact hk
  have hHcard : H.card ≤ v := by
    calc
      H.card ≤ (Finset.univ : Finset (ZMod v)).card := card_le_card (subset_univ H)
      _ = v := by simp [ZMod.card]
  by_cases hwhole : H.card = v
  · have hHC₀ : H ⊆ C₀ := by
      intro h hh
      exact hA₀H_C₀ (mem_add.mpr ⟨0, hA₀zero, h, hh, by simp⟩)
    have hC₀cardle : C₀.card ≤ v := by
      calc
        C₀.card ≤ (Finset.univ : Finset (ZMod v)).card :=
          card_le_card (subset_univ C₀)
        _ = v := by simp [ZMod.card]
    have hC₀card : C₀.card = v := by
      have := card_le_card hHC₀
      omega
    apply (min_le_left _ _).trans
    omega
  · have hHlt : H.card < v := by omega
    have hnotBoth : ¬ (A₀ ⊆ H ∧ B₀ ⊆ H) := by
      rintro ⟨hAH, hBH⟩
      let K : AddSubgroup (ZMod v) := AddAction.stabilizer (ZMod v) (C₀ : Set (ZMod v))
      have hHK : (H : Set (ZMod v)) = (K : Set (ZMod v)) := by
        change (↑C₀.addStab : Set (ZMod v)) = _
        exact coe_addStab hC₀ne
      have hUK : ∀ n ∈ A ∪ B, (n : ZMod v) ∈ K := by
        intro n hn
        have hnH : (n : ZMod v) ∈ H := by
          rcases mem_union.mp hn with hnA | hnB
          · exact hAH (mem_modImage.mpr ⟨n, hnA, rfl⟩)
          · exact hBH (mem_modImage.mpr ⟨n, hnB, rfl⟩)
        have hnHs : (n : ZMod v) ∈ (H : Set (ZMod v)) := hnH
        rw [hHK] at hnHs
        exact hnHs
      have hKtop := stabilizer_eq_top_of_gcd_one hgcd K hUK
      have hHuniv : H = (Finset.univ : Finset (ZMod v)) := by
        ext x
        simp only [mem_univ, iff_true]
        have hxK : x ∈ K := by rw [hKtop]; trivial
        have hxKs : x ∈ (K : Set (ZMod v)) := hxK
        rw [← hHK] at hxKs
        exact hxKs
      have : H.card = v := by simp [hHuniv, ZMod.card]
      omega
    by_cases hBH : B₀ ⊆ H
    · have hAnH : ¬ A₀ ⊆ H := fun hAH ↦ hnotBoth ⟨hAH, hBH⟩
      obtain ⟨a, haA, haH⟩ := Finset.not_subset.mp hAnH
      have hdisj : Disjoint H (a +ᵥ H) :=
        disjoint_self_vadd_of_not_mem hHadd hHneg haH
      have hHsub : H ⊆ A₀ + H := by
        intro h hh
        exact mem_add.mpr ⟨0, hA₀zero, h, hh, by simp⟩
      have hacoset : a +ᵥ H ⊆ A₀ + H := vadd_finset_subset_add haA
      have hAsat : 2 * H.card ≤ (A₀ + H).card := by
        have hc := card_le_card (union_subset hHsub hacoset)
        rw [card_union_of_disjoint hdisj, card_vadd_finset] at hc
        omega
      have hBsatEq : B₀ + H = H := by
        apply Subset.antisymm
        · intro z hz
          obtain ⟨b, hb, h, hh, rfl⟩ := mem_add.mp hz
          exact hHadd b (hBH hb) h hh
        · intro h hh
          exact mem_add.mpr ⟨0, hB₀zero, h, hh, by simp⟩
      have hC₀lower : 2 * H.card ≤ C₀.card := by
        rw [hBsatEq] at hkneser
        omega
      have hBsmall : B.card ≤ H.card + 1 := by
        have hc := card_le_card hBH
        omega
      apply (min_le_right _ _).trans
      have hm := min_le_left A.card B.card
      omega
    · obtain ⟨b', hb'B, hb'H⟩ := Finset.not_subset.mp hBH
      have hdisjBH : Disjoint H (b' +ᵥ H) :=
        disjoint_self_vadd_of_not_mem hHadd hHneg hb'H
      have hHsubB : H ⊆ B₀ + H := by
        intro h hh
        exact mem_add.mpr ⟨0, hB₀zero, h, hh, by simp⟩
      have hbcoset : b' +ᵥ H ⊆ B₀ + H := vadd_finset_subset_add hb'B
      have hBsat : 2 * H.card ≤ (B₀ + H).card := by
        have hc := card_le_card (union_subset hHsubB hbcoset)
        rw [card_union_of_disjoint hdisjBH, card_vadd_finset] at hc
        omega
      have hAproperCard : (A₀ + H).card + H.card ≤ C₀.card := by omega
      have hHpos : 0 < H.card := card_pos.mpr ⟨0, hHzero⟩
      have hnotSubset : ¬ C₀ ⊆ A₀ + H := by
        intro hs
        have hc := card_le_card hs
        omega
      obtain ⟨c, hcC, hcA⟩ := Finset.not_subset.mp hnotSubset
      have hDsubC : c +ᵥ H ⊆ C₀ := by
        have hs : c +ᵥ H ⊆ C₀ + H := vadd_finset_subset_add hcC
        change c +ᵥ H ⊆ C₀ + C₀.addStab at hs
        simpa only [add_addStab] using hs
      have hDdisjSat : Disjoint (c +ᵥ H) (A₀ + H) :=
        disjoint_vadd_add_of_not_mem hHadd hHneg hcA
      have hDdisjA : Disjoint (c +ᵥ H) A₀ :=
        hDdisjSat.mono_right hA₀sat
      obtain ⟨a, haA, b, hbB, hab⟩ := mem_add.mp hcC
      let X := a +ᵥ H
      let Y := b +ᵥ H
      let D := c +ᵥ H
      let R := residueFiberSet A v X
      let S := residueFiberSet B v Y
      let F := sumsOverResidues A B v D
      have hRne : R.Nonempty := by
        obtain ⟨x, hxA, hxa⟩ := mem_modImage.mp haA
        refine ⟨x, mem_residueFiberSet.mpr ⟨hxA, ?_⟩⟩
        apply mem_vadd_finset.mpr
        exact ⟨0, hHzero, by simpa using hxa.symm⟩
      have hSne : S.Nonempty := by
        obtain ⟨y, hyB, hyb⟩ := mem_modImage.mp hbB
        refine ⟨y, mem_residueFiberSet.mpr ⟨hyB, ?_⟩⟩
        apply mem_vadd_finset.mpr
        exact ⟨0, hHzero, by simpa using hyb.symm⟩
      have hRF : R + S ⊆ F := by
        exact residueFiberSet_add_subset_sumsOverResidues hab hHadd
      have hcauchy := cauchy_davenport_add_of_linearOrder_isCancelAdd hRne hSne
      have hFcard : R.card + S.card ≤ F.card + 1 := by
        have hs := card_le_card hRF
        change R.card + S.card - 1 ≤ (R + S).card at hcauchy
        have hRp : 0 < R.card := card_pos.mpr hRne
        have hSp : 0 < S.card := card_pos.mpr hSne
        omega
      have hAsatFiber : A₀.card + H.card ≤ (A₀ + H).card + R.card := by
        exact card_modImage_add_card_le_saturation_add_fiber hHzero haA
      have hBsatFiber : B₀.card + H.card ≤ (B₀ + H).card + S.card := by
        exact card_modImage_add_card_le_saturation_add_fiber hHzero hbB
      have hDcard : D.card = H.card := card_vadd_finset c H
      have hDimage : D ⊆ modImage (A + B) v := by
        rw [← hC₀image]
        exact hDsubC
      have hrefined : C₀.card + A.card + F.card ≤
          (A + B).card + H.card := by
        have hr := card_modImage_add_add_card_add_fiber_le D hA huv hv hA0 hB0 hvB
          hDimage hDdisjA
        rw [← hC₀image, hDcard] at hr
        exact hr
      apply (min_le_right _ _).trans
      have hm := min_le_left A.card B.card
      omega

/- ## Translation and division by the common gcd -/

lemma nat_int_finset_gcd (S : Finset ℕ) :
    S.gcd (fun n ↦ (n : ℤ)) =
      (((S.gcd (fun n : ℕ ↦ n) : ℕ) : ℤ)) := by
  induction S using Finset.cons_induction_on with
  | empty => simp
  | cons a S ha ih =>
    rw [Finset.gcd_cons ha, Finset.gcd_cons ha, ih]
    rw [← Int.coe_gcd]
    rfl

/-- Translate a natural finset down by `m` and divide by `d`. -/
def normalizeNat (S : Finset ℕ) (m d : ℕ) : Finset ℕ :=
  S.image fun x ↦ (x - m) / d

lemma mem_normalizeNat {S : Finset ℕ} {m d q : ℕ} :
    q ∈ normalizeNat S m d ↔ ∃ x ∈ S, (x - m) / d = q := by
  simp [normalizeNat]

lemma normalizeNat_spec {S : Finset ℕ} {m d : ℕ}
    (hd : 0 < d) (hmin : ∀ x ∈ S, m ≤ x) (hdiv : ∀ x ∈ S, d ∣ x - m)
    {q : ℕ} : q ∈ normalizeNat S m d ↔ ∃ x ∈ S, x = m + d * q := by
  constructor
  · intro hq
    obtain ⟨x, hx, rfl⟩ := mem_normalizeNat.mp hq
    refine ⟨x, hx, ?_⟩
    have hcancel := Nat.mul_div_cancel' (hdiv x hx)
    have hmx := hmin x hx
    omega
  · rintro ⟨x, hx, rfl⟩
    apply mem_normalizeNat.mpr
    refine ⟨m + d * q, hx, ?_⟩
    have : m + d * q - m = d * q := by omega
    rw [this]
    exact Nat.mul_div_cancel_left q hd

lemma card_normalizeNat {S : Finset ℕ} {m d : ℕ}
    (_hd : 0 < d) (hmin : ∀ x ∈ S, m ≤ x) (hdiv : ∀ x ∈ S, d ∣ x - m) :
    (normalizeNat S m d).card = S.card := by
  apply card_image_iff.mpr
  intro x hx y hy hxy
  have hdx := Nat.mul_div_cancel' (hdiv x hx)
  have hdy := Nat.mul_div_cancel' (hdiv y hy)
  have hmx := hmin x hx
  have hmy := hmin y hy
  change (x - m) / d = (y - m) / d at hxy
  have := congrArg (fun z ↦ d * z) hxy
  rw [hdx, hdy] at this
  omega

lemma normalizeNat_subset_Icc {S : Finset ℕ} {m d M : ℕ}
    (hS : S ⊆ Icc m M) : normalizeNat S m d ⊆ Icc 0 ((M - m) / d) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := mem_normalizeNat.mp hq
  have hxI := mem_Icc.mp (hS hx)
  exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right (Nat.sub_le_sub_right hxI.2 m)⟩

lemma zero_mem_normalizeNat {S : Finset ℕ} {m d : ℕ} (hm : m ∈ S) :
    0 ∈ normalizeNat S m d := by
  apply mem_normalizeNat.mpr
  exact ⟨m, hm, by simp⟩

lemma top_mem_normalizeNat {S : Finset ℕ} {m d M : ℕ} (hM : M ∈ S) :
    (M - m) / d ∈ normalizeNat S m d := by
  apply mem_normalizeNat.mpr
  exact ⟨M, hM, rfl⟩

/-- Reconstructing the original sumset from the translated, divided
summands. -/
lemma sumset_eq_image_normalized {S T : Finset ℕ} {s t d : ℕ}
    (hd : 0 < d) (hSmin : ∀ x ∈ S, s ≤ x) (hTmin : ∀ x ∈ T, t ≤ x)
    (hSdiv : ∀ x ∈ S, d ∣ x - s) (hTdiv : ∀ x ∈ T, d ∣ x - t) :
    S + T = (normalizeNat S s d + normalizeNat T t d).image
      (fun q ↦ s + t + d * q) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.mp hz
    let a := (x - s) / d
    let b := (y - t) / d
    have ha : a ∈ normalizeNat S s d := mem_normalizeNat.mpr ⟨x, hx, rfl⟩
    have hb : b ∈ normalizeNat T t d := mem_normalizeNat.mpr ⟨y, hy, rfl⟩
    apply mem_image.mpr
    refine ⟨a + b, Finset.add_mem_add ha hb, ?_⟩
    have hdx := Nat.mul_div_cancel' (hSdiv x hx)
    have hdy := Nat.mul_div_cancel' (hTdiv y hy)
    have hsx := hSmin x hx
    have hty := hTmin y hy
    have hxa : x = s + d * a := by dsimp [a]; omega
    have hyb : y = t + d * b := by dsimp [b]; omega
    change s + t + d * (a + b) = x + y
    rw [hxa, hyb]
    ring
  · intro hz
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hq
    obtain ⟨x, hx, hxa⟩ := (normalizeNat_spec hd hSmin hSdiv).mp ha
    obtain ⟨y, hy, hyb⟩ := (normalizeNat_spec hd hTmin hTdiv).mp hb
    apply mem_add.mpr
    refine ⟨x, hx, y, hy, ?_⟩
    rw [hxa, hyb]
    ring

lemma card_sumset_eq_card_normalized {S T : Finset ℕ} {s t d : ℕ}
    (hd : 0 < d)
    (hSmin : ∀ x ∈ S, s ≤ x) (hTmin : ∀ x ∈ T, t ≤ x)
    (hSdiv : ∀ x ∈ S, d ∣ x - s) (hTdiv : ∀ x ∈ T, d ∣ x - t) :
    (S + T).card = (normalizeNat S s d + normalizeNat T t d).card := by
  rw [sumset_eq_image_normalized hd hSmin hTmin hSdiv hTdiv,
    card_image_iff.mpr]
  intro x hx y hy hxy
  change s + t + d * x = s + t + d * y at hxy
  have hmul : d * x = d * y := Nat.add_left_cancel hxy
  exact Nat.eq_of_mul_eq_mul_left hd hmul

/-- The local arithmetic progression notation used by the final additive
alternative. -/
def natAP (a d len : ℕ) : Finset ℕ :=
  (range len).image fun j ↦ a + d * j

@[simp] lemma mem_natAP {a d len x : ℕ} :
    x ∈ natAP a d len ↔ ∃ j < len, a + d * j = x := by
  simp [natAP]

end Erdos13Additive

end Erdos13_Erdos13Additive

section Erdos587_FiniteFourier

/-
# Elementary finite Fourier identities for cyclic groups
-/

namespace Erdos587

open scoped BigOperators ComplexConjugate
open Finset

noncomputable def cyclicFinsetFourier {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (k : ZMod N) : ℂ :=
  ∑ a ∈ A, ZMod.stdAddChar (-(a * k))

@[simp] lemma cyclicFinsetFourier_zero {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    cyclicFinsetFourier A 0 = A.card := by
  simp [cyclicFinsetFourier]

lemma cyclic_character_orthogonality {N : ℕ} [NeZero N] (x : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (x * k)) =
      if x = 0 then (N : ℂ) else 0 := by
  simpa [mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

/-- Parseval for the unnormalized Fourier transform of a finite-set
indicator. -/
theorem sum_fourier_mul_conj {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ k : ZMod N,
      cyclicFinsetFourier A k * conj (cyclicFinsetFourier A k)) =
      (N : ℂ) * A.card := by
  classical
  simp only [cyclicFinsetFourier, map_sum, Finset.sum_mul_sum]
  have hconj (y : ZMod N) :
      conj (ZMod.stdAddChar (-y)) = ZMod.stdAddChar y := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  simp_rw [hconj]
  simp_rw [← AddChar.map_add_eq_mul]
  have harg (i j k : ZMod N) : -(i * k) + j * k = (j - i) * k := by ring
  simp_rw [harg]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y ∈ A, (N : ℂ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
      simp_rw [cyclic_character_orthogonality]
      rw [Finset.sum_eq_single y]
      · simp
      · intro b hb hby
        simp only [if_neg (sub_ne_zero.mpr hby)]
      · exact fun h => (h hy).elim
    _ = (N : ℂ) * A.card := by
      rw [Finset.sum_const]
      simp [mul_comm]

/-- Real-valued Parseval form. -/
theorem sum_norm_sq_cyclicFinsetFourier {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) :
    (∑ k : ZMod N, ‖cyclicFinsetFourier A k‖ ^ 2) =
      (N : ℝ) * A.card := by
  have hc := sum_fourier_mul_conj A
  have h := congrArg Complex.re hc
  have hre (z : ℂ) : (z * conj z).re = Complex.normSq z := by
    rw [Complex.mul_conj]
    simp
  rw [Complex.re_sum] at h
  simp_rw [hre] at h
  simpa [Complex.normSq_eq_norm_sq] using h

/-- Frequencies where the unnormalized Fourier coefficient has norm at least
`τ`. -/
noncomputable def cyclicLargeSpectrum {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (τ : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter fun k => τ ≤ ‖cyclicFinsetFourier A k‖

/-- Parseval bounds the cardinality of the large spectrum. -/
theorem card_cyclicLargeSpectrum_mul_sq_le {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((cyclicLargeSpectrum A τ).card : ℝ) * τ ^ 2 ≤
      (N : ℝ) * A.card := by
  classical
  let Γ := cyclicLargeSpectrum A τ
  have hpoint : ∀ k ∈ Γ, τ ^ 2 ≤ ‖cyclicFinsetFourier A k‖ ^ 2 := by
    intro k hk
    have hk' : τ ≤ ‖cyclicFinsetFourier A k‖ := by
      simpa [Γ, cyclicLargeSpectrum] using hk
    nlinarith [norm_nonneg (cyclicFinsetFourier A k)]
  have hlower := Finset.card_nsmul_le_sum Γ
    (fun k => ‖cyclicFinsetFourier A k‖ ^ 2) (τ ^ 2) hpoint
  have hupper :
      (∑ k ∈ Γ, ‖cyclicFinsetFourier A k‖ ^ 2) ≤
        ∑ k : ZMod N, ‖cyclicFinsetFourier A k‖ ^ 2 := by
    exact Finset.sum_le_univ_sum_of_nonneg fun k => sq_nonneg _
  rw [sum_norm_sq_cyclicFinsetFourier A] at hupper
  simpa [nsmul_eq_mul] using le_trans hlower hupper

end Erdos587

end Erdos587_FiniteFourier

section Erdos587_FiniteBogolyubov

/-
# A finite cyclic Bogolyubov lemma
-/

namespace Erdos587

open scoped BigOperators ComplexConjugate
open Finset

/-- Explicit membership in `2A-2A` in a cyclic group. -/
def ZModInFourfoldDifference {N : ℕ} (A : Finset (ZMod N)) (x : ZMod N) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A, x = a + b - c - d

/-- The fourth Fourier moment with a character twist is the exact weighted
count of representations in `2A-2A`. -/
theorem fourth_fourier_identity {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    (∑ k : ZMod N,
      cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
        ZMod.stdAddChar (x * k)) =
    ∑ a ∈ A, ∑ c ∈ A, ∑ b ∈ A, ∑ d ∈ A,
      if x = a + b - c - d then (N : ℂ) else 0 := by
  classical
  simp only [cyclicFinsetFourier, pow_two, map_sum, Finset.sum_mul_sum]
  have hconj (y : ZMod N) :
      conj (ZMod.stdAddChar (-y)) = ZMod.stdAddChar y := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  simp_rw [hconj]
  have hprod (a b c d k : ZMod N) :
      ZMod.stdAddChar (-(a * k)) * ZMod.stdAddChar (-(b * k)) *
          (ZMod.stdAddChar (c * k) * ZMod.stdAddChar (d * k)) *
          ZMod.stdAddChar (x * k) =
        ZMod.stdAddChar ((x - a - b + c + d) * k) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [Finset.sum_mul]
  simp_rw [hprod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [cyclic_character_orthogonality]
  congr 1
  apply propext
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

lemma fourth_fourier_sum_eq_zero_of_not_mem {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N)
    (hx : ¬ ZModInFourfoldDifference A x) :
    (∑ k : ZMod N,
      cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
        ZMod.stdAddChar (x * k)) = 0 := by
  rw [fourth_fourier_identity A x]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro c hc
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro d hd
  simp only [ite_eq_right_iff]
  intro hEq
  exfalso
  apply hx
  exact ⟨a, ha, b, hb, c, hc, d, hd, hEq⟩

lemma pow_two_mul_conj_pow_two (z : ℂ) :
    z ^ 2 * conj z ^ 2 = ((‖z‖ ^ 4 : ℝ) : ℂ) := by
  calc
    z ^ 2 * conj z ^ 2 = (z * conj z) ^ 2 := by ring
    _ = (((‖z‖ : ℂ) ^ 2)) ^ 2 := by rw [Complex.mul_conj']
    _ = ((‖z‖ ^ 4 : ℝ) : ℂ) := by
      push_cast
      ring

lemma stdAddChar_re_ge_half_of_close {N : ℕ} [NeZero N]
    {y : ZMod N}
    (hy : ‖ZMod.stdAddChar y - 1‖ ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ (ZMod.stdAddChar y).re := by
  have hre := Complex.abs_re_le_norm (ZMod.stdAddChar y - 1)
  have habs : |(ZMod.stdAddChar y - 1).re| ≤ (1 / 2 : ℝ) :=
    le_trans hre hy
  have hneg := neg_abs_le ((ZMod.stdAddChar y - 1).re)
  norm_num [Complex.sub_re] at habs hneg ⊢
  linarith

lemma stdAddChar_re_ge_neg_one {N : ℕ} [NeZero N] (y : ZMod N) :
    (-1 : ℝ) ≤ (ZMod.stdAddChar y).re := by
  have hre := Complex.abs_re_le_norm (ZMod.stdAddChar y)
  have hnorm : ‖ZMod.stdAddChar y‖ = (1 : ℝ) := by simp
  rw [hnorm] at hre
  exact le_trans (neg_le_neg hre) (neg_abs_le _)

/-- Quantitative Fourier Bogolyubov criterion.  A point approximately
annihilating every large Fourier frequency belongs to `2A-2A`. -/
theorem mem_fourfoldDifference_of_largeSpectrum_close
    {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (x : ZMod N)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτA : τ ≤ A.card)
    (hsmall :
      2 * ((N : ℝ) * A.card * τ ^ 2) < (A.card : ℝ) ^ 4)
    (hclose : ∀ k ∈ cyclicLargeSpectrum A τ,
      ‖ZMod.stdAddChar (x * k) - 1‖ ≤ (1 / 2 : ℝ)) :
    ZModInFourfoldDifference A x := by
  classical
  let F : ZMod N → ℂ := cyclicFinsetFourier A
  let w : ZMod N → ℝ := fun k => ‖F k‖ ^ 4
  let Γ : Finset (ZMod N) := cyclicLargeSpectrum A τ
  let Δ : Finset (ZMod N) :=
    Finset.univ.filter fun k => ¬ τ ≤ ‖F k‖
  have h0Γ : (0 : ZMod N) ∈ Γ := by
    simp only [Γ, cyclicLargeSpectrum, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [F] using hτA
  have hw0 : w (0 : ZMod N) = (A.card : ℝ) ^ 4 := by
    simp [w, F]
  have hw_nonneg (k : ZMod N) : 0 ≤ w k := by
    exact pow_nonneg (norm_nonneg _) _
  have hlarge_point : ∀ k ∈ Γ,
      (1 / 2 : ℝ) * w k ≤
        w k * (ZMod.stdAddChar (x * k)).re := by
    intro k hk
    have hre := stdAddChar_re_ge_half_of_close (hclose k hk)
    nlinarith [hw_nonneg k]
  have hlarge :
      (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 ≤
        ∑ k ∈ Γ, w k * (ZMod.stdAddChar (x * k)).re := by
    have hsum := Finset.sum_le_sum hlarge_point
    have hsingle : w 0 ≤ ∑ k ∈ Γ, w k := by
      exact Finset.single_le_sum (fun k _ => hw_nonneg k) h0Γ
    rw [hw0] at hsingle
    calc
      (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 ≤
          (1 / 2 : ℝ) * ∑ k ∈ Γ, w k := by nlinarith
      _ = ∑ k ∈ Γ, (1 / 2 : ℝ) * w k := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Γ, w k * (ZMod.stdAddChar (x * k)).re := hsum
  have hsmall_point : ∀ k ∈ Δ,
      w k ≤ τ ^ 2 * ‖F k‖ ^ 2 := by
    intro k hk
    have hk' : ‖F k‖ < τ := by
      have := (Finset.mem_filter.mp hk).2
      exact lt_of_not_ge this
    have hn := norm_nonneg (F k)
    have hsquare : ‖F k‖ ^ 2 ≤ τ ^ 2 :=
      (sq_le_sq₀ hn hτ).2 (le_of_lt hk')
    dsimp [w]
    calc
      ‖F k‖ ^ 4 = ‖F k‖ ^ 2 * ‖F k‖ ^ 2 := by ring
      _ ≤ τ ^ 2 * ‖F k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
  have hsmall_sum :
      (∑ k ∈ Δ, w k) ≤ (N : ℝ) * A.card * τ ^ 2 := by
    calc
      (∑ k ∈ Δ, w k) ≤ ∑ k ∈ Δ, τ ^ 2 * ‖F k‖ ^ 2 :=
        Finset.sum_le_sum hsmall_point
      _ = τ ^ 2 * ∑ k ∈ Δ, ‖F k‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ τ ^ 2 * ∑ k : ZMod N, ‖F k‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_univ_sum_of_nonneg fun k => sq_nonneg _) (sq_nonneg τ)
      _ = (N : ℝ) * A.card * τ ^ 2 := by
        rw [show (∑ k : ZMod N, ‖F k‖ ^ 2) = (N : ℝ) * A.card by
          simpa [F] using sum_norm_sq_cyclicFinsetFourier A]
        ring
  have hsmall_lower :
      -(∑ k ∈ Δ, w k) ≤
        ∑ k ∈ Δ, w k * (ZMod.stdAddChar (x * k)).re := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hre := stdAddChar_re_ge_neg_one (x * k)
    nlinarith [hw_nonneg k]
  have hsplit (v : ZMod N → ℝ) :
      (∑ k ∈ Γ, v k) + ∑ k ∈ Δ, v k = ∑ k : ZMod N, v k := by
    simpa [Γ, Δ, cyclicLargeSpectrum] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k => τ ≤ ‖F k‖) v)
  have hreal :
      0 < (∑ k : ZMod N,
        cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
          ZMod.stdAddChar (x * k)).re := by
    have hbound :
        0 < (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 -
          ((N : ℝ) * A.card * τ ^ 2) := by
      linarith
    have hcombined :
        (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 -
            ((N : ℝ) * A.card * τ ^ 2) ≤
          (∑ k ∈ Γ, w k * (ZMod.stdAddChar (x * k)).re) +
            ∑ k ∈ Δ, w k * (ZMod.stdAddChar (x * k)).re := by
      linarith [hlarge, hsmall_sum, hsmall_lower]
    rw [hsplit (fun k => w k * (ZMod.stdAddChar (x * k)).re)] at hcombined
    have hrewrite :
        (∑ k : ZMod N,
          cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
            ZMod.stdAddChar (x * k)).re =
          ∑ k : ZMod N, w k * (ZMod.stdAddChar (x * k)).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_two_mul_conj_pow_two, Complex.re_ofReal_mul]
    rw [hrewrite]
    exact lt_of_lt_of_le hbound hcombined
  by_contra hx
  have hz := fourth_fourier_sum_eq_zero_of_not_mem A x hx
  rw [hz] at hreal
  norm_num at hreal

/-- A parameter-free density form. If `A` has density at least `1/q`, at most
`16q³` frequencies cut out a radius-`1/2` Bohr set contained in `2A-2A`. -/
theorem finite_cyclic_bogolyubov_uniform
    {N : ℕ} [NeZero N] (q : ℕ) (hq : 1 ≤ q)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hdense : N ≤ q * A.card) (x : ZMod N)
    (hclose : ∀ k ∈ cyclicLargeSpectrum A
        ((A.card : ℝ) / (4 * q)),
      ‖ZMod.stdAddChar (x * k) - 1‖ ≤ (1 / 2 : ℝ)) :
    ZModInFourfoldDifference A x ∧
      (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))).card ≤ 16 * q ^ 3 := by
  classical
  let a : ℝ := A.card
  let n : ℝ := N
  let qr : ℝ := q
  let den : ℝ := 4 * qr
  let τ : ℝ := a / den
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast hA.card_pos
  have hqr : 1 ≤ qr := by
    dsimp [qr]
    exact_mod_cast hq
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hdenseR : n ≤ qr * a := by
    dsimp [n, qr, a]
    exact_mod_cast hdense
  have hτ : 0 ≤ τ := by
    dsimp [τ]
    positivity
  have hτA : τ ≤ a := by
    dsimp [τ]
    apply div_le_self (le_of_lt ha)
    dsimp [den]
    nlinarith
  have hsmall : 2 * (n * a * τ ^ 2) < a ^ 4 := by
    have hmul : n * a ≤ (qr * a) * a :=
      mul_le_mul_of_nonneg_right hdenseR (le_of_lt ha)
    calc
      2 * (n * a * τ ^ 2) ≤ 2 * ((qr * a) * a * τ ^ 2) := by
        gcongr
      _ = a ^ 4 / (8 * qr) := by
        dsimp [τ, den]
        field_simp
        ring
      _ < a ^ 4 := by
        apply div_lt_self (pow_pos ha 4)
        nlinarith
  have hmem : ZModInFourfoldDifference A x := by
    apply mem_fourfoldDifference_of_largeSpectrum_close A x hτ
    · simpa [a] using hτA
    · simpa [n, a, τ, den, qr] using hsmall
    · intro k hk
      exact hclose k (by simpa [τ, a, den, qr] using hk)
  have hspectrum := card_cyclicLargeSpectrum_mul_sq_le A hτ
  have hspectrum' :
      ((cyclicLargeSpectrum A τ).card : ℝ) * a ^ 2 ≤
        n * a * den ^ 2 := by
    calc
      ((cyclicLargeSpectrum A τ).card : ℝ) * a ^ 2 =
          (((cyclicLargeSpectrum A τ).card : ℝ) * τ ^ 2) * den ^ 2 := by
            dsimp [τ]
            field_simp
      _ ≤ (n * a) * den ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · simpa [n, a] using hspectrum
        · exact sq_nonneg den
  have hright : n * a * den ^ 2 ≤ (16 * qr ^ 3) * a ^ 2 := by
    calc
      n * a * den ^ 2 ≤ (qr * a) * a * den ^ 2 := by gcongr
      _ = (16 * qr ^ 3) * a ^ 2 := by
        dsimp [den]
        ring
  have hcardR : ((cyclicLargeSpectrum A τ).card : ℝ) ≤ 16 * qr ^ 3 := by
    have hprod := le_trans hspectrum' hright
    apply le_of_mul_le_mul_right (a := a ^ 2) (by simpa [mul_assoc] using hprod)
    exact pow_pos ha 2
  refine ⟨hmem, ?_⟩
  have hcardN : (cyclicLargeSpectrum A τ).card ≤ 16 * q ^ 3 := by
    dsimp [qr] at hcardR
    exact_mod_cast hcardR
  simpa [τ, a, den, qr] using hcardN

end Erdos587

end Erdos587_FiniteBogolyubov

section Erdos587_Bohr

open scoped BigOperators ComplexConjugate Pointwise

namespace Erdos587

noncomputable def cyclicBohrSet {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (rho : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter fun x => ∀ k ∈ Gamma,
    ‖ZMod.stdAddChar (x * k) - 1‖ ≤ rho

@[simp] lemma mem_cyclicBohrSet {N : ℕ} [NeZero N]
    {Gamma : Finset (ZMod N)} {rho : ℝ} {x : ZMod N} :
    x ∈ cyclicBohrSet Gamma rho ↔
      ∀ k ∈ Gamma, ‖ZMod.stdAddChar (x * k) - 1‖ ≤ rho := by
  simp [cyclicBohrSet]

lemma zmodInFourfoldDifference_iff_mem_pointwise
    {N : ℕ} [NeZero N] {A : Finset (ZMod N)} {x : ZMod N} :
    ZModInFourfoldDifference A x ↔ x ∈ 2 • A - 2 • A := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    apply Finset.mem_sub.mpr
    refine ⟨a + b, ?_, c + d, ?_, by ring⟩
    · rw [show 2 • A = A + A by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩
    · rw [show 2 • A = A + A by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨c, hc, d, hd, rfl⟩
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hx
    rw [show 2 • A = A + A by simp [two_nsmul]] at hu hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hu
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hv
    refine ⟨a, ha, b, hb, c, hc, d, hd, ?_⟩
    rw [← huv, ← hab, ← hcd]
    ring

theorem cyclicBohrSet_subset_fourfoldDifference
    {N : ℕ} [NeZero N] (q : ℕ) (hq : 1 ≤ q)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hdense : N ≤ q * A.card) :
    cyclicBohrSet
        (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))) (1 / 2) ⊆
      2 • A - 2 • A := by
  intro x hx
  rw [← zmodInFourfoldDifference_iff_mem_pointwise]
  exact (finite_cyclic_bogolyubov_uniform q hq A hA hdense x
    (mem_cyclicBohrSet.mp hx)).1

theorem card_largeSpectrum_le_of_density
    {N : ℕ} [NeZero N] (q : ℕ) (hq : 1 ≤ q)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hdense : N ≤ q * A.card) :
    (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))).card ≤
      16 * q ^ 3 := by
  have hzero : (0 : ZMod N) ∈ cyclicBohrSet
      (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))) (1 / 2) := by
    simp
  exact (finite_cyclic_bogolyubov_uniform q hq A hA hdense 0
    (mem_cyclicBohrSet.mp hzero)).2

/-- A residue represented by an integer of absolute value at most `N / 16`
lies in the analytic radius-`1/2` Bohr neighborhood. -/
lemma stdAddChar_intCast_close {N : ℕ} [NeZero N] (t : ℤ)
    (hsmall : 16 * t.natAbs ≤ N) :
    ‖ZMod.stdAddChar (t : ZMod N) - 1‖ ≤ (1 / 2 : ℝ) := by
  rw [ZMod.stdAddChar_coe]
  have hformula : (2 * Real.pi * Complex.I * (t : ℂ) / (N : ℂ)) =
      Complex.I * ((2 * Real.pi * (t : ℝ) / N : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hformula]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi * (t : ℝ) / N)).trans ?_
  have htAbs : |(t : ℝ)| = (t.natAbs : ℝ) := by
    rw [← Int.cast_abs]
    simp
  have hNAbs : |(N : ℝ)| = (N : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg N)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_nonneg Real.pi_pos.le, htAbs, hNAbs]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hsmallR : (16 : ℝ) * t.natAbs ≤ N := by
    exact_mod_cast hsmall
  rw [div_le_iff₀ hN]
  nlinarith

end Erdos587

end Erdos587_Bohr

section Erdos587_BohrPhase

open scoped BigOperators Pointwise

namespace Erdos587

end Erdos587

end Erdos587_BohrPhase

section Erdos407_AdelicMinkowski

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
namespace Erdos407.AdelicMinkowski

open scoped BigOperators Matrix NNReal ENNReal Pointwise
open MeasureTheory Module Submodule Set

/-- A closed coordinate box centered at the origin. -/
def realBox {n : ℕ} (r : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.Icc (-r) r

/-- A concrete upper certificate for the product of the successive minima of
a symmetric coordinate box with respect to a specified lattice: it gives `n`
independent lattice points, the scale at which each enters the box, and a
bound for the product of those scales. -/
structure SuccessiveProductCertificate {n : ℕ} (Λ : AddSubgroup (Fin n → ℝ))
    (r : Fin n → ℝ) (B : ℝ) where
  scale : Fin n → ℝ
  point : Fin n → Fin n → ℝ
  scale_nonneg : ∀ i, 0 ≤ scale i
  point_mem : ∀ i, point i ∈ Λ
  independent : LinearIndependent ℝ point
  mem_scaledBox : ∀ i, point i ∈ realBox (scale i • r)
  product_le : ∏ i, scale i ≤ B

end Erdos407.AdelicMinkowski

end Erdos407_AdelicMinkowski

section Erdos407_Primitive

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/


/-
# Primitive integral representatives of rational projective points

This file supplies the elementary normalization layer used in the proof of
Erdős Problem 407.  A nonzero vector over `ℚ` is cleared of denominators and
then divided by the gcd of its integral coordinates.  We characterize
primitivity by a Bézout identity; this makes uniqueness up to sign especially
convenient to use.
-/

namespace Erdos407.Primitive

open scoped BigOperators LinearAlgebra.Projectivization

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise coercion of an integral vector to a rational vector. -/
def intCastVec (z : ι → ℤ) : ι → ℚ := fun i => z i

omit [Fintype ι] in
@[simp] theorem intCastVec_apply (z : ι → ℤ) (i : ι) :
    intCastVec z i = (z i : ℚ) := rfl

/-- A finite integral vector is primitive when its coordinates have a
Bézout combination equal to one. -/
def IsPrimitive (z : ι → ℤ) : Prop :=
  ∃ u : ι → ℤ, ∑ i, u i * z i = 1

theorem IsPrimitive.ne_zero {z : ι → ℤ} (hz : IsPrimitive z) : z ≠ 0 := by
  rintro rfl
  simp [IsPrimitive] at hz

/-- The (nonnegative) gcd of the coordinates of an integral vector. -/
def content (z : ι → ℤ) : ℤ := Finset.univ.gcd z

theorem content_dvd (z : ι → ℤ) (i : ι) : content z ∣ z i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

theorem content_ne_zero {z : ι → ℤ} (hz : z ≠ 0) : content z ≠ 0 := by
  rw [content, Finset.gcd_ne_zero_iff]
  simpa [funext_iff] using hz

/-- Divide an integral vector by the gcd of all its coordinates. -/
def divideContent (z : ι → ℤ) : ι → ℤ := fun i => z i / content z

theorem content_mul_divideContent (z : ι → ℤ) (i : ι) :
    content z * divideContent z i = z i := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (content_dvd z i)

omit [Fintype ι] in
private theorem exists_bezout_finset (s : Finset ι) (z : ι → ℤ) :
    ∃ u : ι → ℤ, ∑ i ∈ s, u i * z i = s.gcd z := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨u, hu⟩ := ih
      let A : ℤ := Int.gcdA (z a) (s.gcd z)
      let B : ℤ := Int.gcdB (z a) (s.gcd z)
      refine ⟨fun i => if i = a then A else B * u i, ?_⟩
      rw [Finset.sum_insert ha, Finset.gcd_insert]
      simp only [if_pos]
      have hsum :
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
            B * s.gcd z := by
        calc
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
              ∑ i ∈ s, B * (u i * z i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [if_neg (by intro hia; subst i; exact ha hi)]
                ring
          _ = B * ∑ i ∈ s, u i * z i := by
                rw [Finset.mul_sum]
          _ = B * s.gcd z := by rw [hu]
      rw [hsum]
      dsimp [A, B]
      rw [mul_comm B, mul_comm (Int.gcdA (z a) (s.gcd z))]
      exact (Int.gcd_eq_gcd_ab (z a) (s.gcd z)).symm

theorem isPrimitive_of_content_eq_one {z : ι → ℤ} (hz : content z = 1) :
    IsPrimitive z := by
  obtain ⟨u, hu⟩ := exists_bezout_finset Finset.univ z
  have hu' : ∑ i, u i * z i = content z := by
    simpa [content] using hu
  exact ⟨u, hu'.trans hz⟩

theorem divideContent_primitive {z : ι → ℤ} (hz : z ≠ 0) :
    IsPrimitive (divideContent z) := by
  apply isPrimitive_of_content_eq_one
  rw [content]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

theorem divideContent_ne_zero {z : ι → ℤ} (hz : z ≠ 0) :
    divideContent z ≠ 0 := (divideContent_primitive hz).ne_zero

/-- Two nonzero rational vectors are projectively equivalent when one is a
nonzero scalar multiple of the other. -/
def ProjectivelyEquivalent (x y : ι → ℚ) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ x = q • y

omit [Fintype ι] in
theorem ProjectivelyEquivalent.refl {x : ι → ℚ} (_hx : x ≠ 0) :
    ProjectivelyEquivalent x x := ⟨1, one_ne_zero, by simp⟩

omit [Fintype ι] in
theorem ProjectivelyEquivalent.symm {x y : ι → ℚ}
    (h : ProjectivelyEquivalent x y) : ProjectivelyEquivalent y x := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨q⁻¹, inv_ne_zero hq, ?_⟩
  ext i
  simp [hq]

omit [Fintype ι] in
theorem ProjectivelyEquivalent.trans {x y z : ι → ℚ}
    (hxy : ProjectivelyEquivalent x y) (hyz : ProjectivelyEquivalent y z) :
    ProjectivelyEquivalent x z := by
  obtain ⟨q, hq, rfl⟩ := hxy
  obtain ⟨r, hr, rfl⟩ := hyz
  refine ⟨q * r, mul_ne_zero hq hr, ?_⟩
  simp [smul_smul]

/- ## Preservation of equations and nondegenerate subsums -/

/- ## Uniqueness of primitive representatives -/

/- ## A primitive representative chosen for each projective point -/

end Erdos407.Primitive

end Erdos407_Primitive

section Erdos407_PrimitiveExtension

namespace Erdos407.PrimitiveExtension

open scoped BigOperators
open Module

noncomputable section

/-- The integral linear functional represented by an integral row vector. -/
def dotLinear {n : ℕ} (u : Fin n → ℤ) : (Fin n → ℤ) →ₗ[ℤ] ℤ where
  toFun z := ∑ i, u i * z i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_left_comm]

@[simp] theorem dotLinear_apply {n : ℕ} (u z : Fin n → ℤ) :
    dotLinear u z = ∑ i, u i * z i := rfl

/-- A nonzero vector of least positive homogeneous gauge in an integral
lattice is primitive.  The gauge need not satisfy any triangle inequality. -/
theorem isPrimitive_of_minimal_gauge {n : ℕ} (z : Fin n → ℤ)
    (hz : z ≠ 0) (μ : (Fin n → ℤ) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ z ≤ μ x) :
    Erdos407.Primitive.IsPrimitive z := by
  let c : ℤ := Erdos407.Primitive.content z
  have hc0 : 0 ≤ c := by
    have hn := Finset.normalize_gcd (s := Finset.univ) (f := z)
    have habs : |c| = c := by
      rw [Int.abs_eq_normalize]
      exact hn
    rw [← habs]
    exact abs_nonneg c
  have hcne : c ≠ 0 := Erdos407.Primitive.content_ne_zero hz
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  suffices hc : c = 1 by
    apply Erdos407.Primitive.isPrimitive_of_content_eq_one
    exact hc
  by_contra hc
  have hc2 : (2 : ℤ) ≤ c := by omega
  let z' : Fin n → ℤ := Erdos407.Primitive.divideContent z
  have hz' : z' ≠ 0 := Erdos407.Primitive.divideContent_ne_zero hz
  have hz_eq : z = c • z' := by
    funext i
    exact (Erdos407.Primitive.content_mul_divideContent z i).symm
  have hscale : μ z = (c : ℝ) * μ z' := by
    rw [hz_eq]
    exact hμhom c hcpos z'
  have hle : μ z ≤ μ z' := hmin z' hz'
  have hz'pos : 0 < μ z' := hμpos z' hz'
  have hc2r : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
  rw [hscale] at hle
  nlinarith

/-- A primitive integral vector can be made the zeroth vector of an integral basis. -/
theorem exists_basis_zero_eq_of_isPrimitive {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℤ) (hz : Erdos407.Primitive.IsPrimitive z) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ), b ⟨0, hn⟩ = z := by
  obtain ⟨u, hu⟩ := hz
  let f : (Fin n → ℤ) →ₗ[ℤ] ℤ := dotLinear u
  have hfz : f z = 1 := by
    simpa [f, dotLinear] using hu
  let K : Submodule ℤ (Fin n → ℤ) := LinearMap.ker f
  let kb := K.basisOfPid (Pi.basisFun ℤ (Fin n))
  let k : ℕ := kb.1
  let bK : Basis (Fin k) ℤ K := kb.2
  have hli : ∀ (c : ℤ), ∀ x ∈ K, c • z + x = 0 → c = 0 := by
    intro c x hx hzero
    have hx0 : f x = 0 := by
      exact (LinearMap.mem_ker.mp hx)
    have h : f (c • z + x) = f 0 := congr_arg f hzero
    rw [map_add, map_smul, hfz, hx0, map_zero] at h
    simpa using h
  have hsp : ∀ x : Fin n → ℤ, ∃ c : ℤ, x + c • z ∈ K := by
    intro x
    refine ⟨-f x, ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [map_add, map_smul, hfz]
    simp
  let b' : Basis (Fin (k + 1)) ℤ (Fin n → ℤ) :=
    Basis.mkFinCons z bK hli hsp
  have hb'0 : b' 0 = z := by
    simp [b', Basis.coe_mkFinCons]
  have hkn : k + 1 = n := by
    have hc := Fintype.card_congr (b'.indexEquiv (Pi.basisFun ℤ (Fin n)))
    simpa using hc
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := b'.reindex (finCongr hkn)
  refine ⟨b, ?_⟩
  simp only [b, Basis.reindex_apply]
  have hzero : (finCongr hkn).symm ⟨0, hn⟩ = (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  rw [hzero, hb'0]

/-- Integral coordinates identify the `ℤ`-span of a real basis with the
standard free integral module. -/
def zspanCoordEquiv {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Submodule.span ℤ (Set.range b) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (b.restrictScalars ℤ).repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

/-- The canonical integral basis of the `ℤ`-span of a real basis.  Its
coordinate equivalence is `zspanCoordEquiv`. -/
def zspanBasis {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)) :=
  b.restrictScalars ℤ

@[simp] theorem zspanBasis_apply_coe {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    ((zspanBasis b i : Submodule.span ℤ (Set.range b)) : E) = b i := by
  exact b.restrictScalars_apply ℤ i

@[simp] theorem zspanCoordEquiv_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (x : Submodule.span ℤ (Set.range b)) (i : Fin n) :
    zspanCoordEquiv b x i = (b.restrictScalars ℤ).repr x i := by
  rfl

/-- A shortest nonzero point in the integral span of a real basis is
primitive in lattice coordinates, and it extends to an integral basis with
that point as its zeroth vector. -/
theorem shortest_zspan_vector_primitive_and_extends
    {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ} (hn : 0 < n)
    (b : Basis (Fin n) ℝ E)
    (v : Submodule.span ℤ (Set.range b)) (hv : v ≠ 0)
    (μ : Submodule.span ℤ (Set.range b) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ v ≤ μ x) :
    Erdos407.Primitive.IsPrimitive (zspanCoordEquiv b v) ∧
      ∃ B : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)),
        B ⟨0, hn⟩ = v := by
  let e := zspanCoordEquiv b
  let z : Fin n → ℤ := e v
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply e.injective
    simpa [z] using hz0
  let ν : (Fin n → ℤ) → ℝ := fun x => μ (e.symm x)
  have hνpos : ∀ x ≠ 0, 0 < ν x := by
    intro x hx
    apply hμpos
    simpa using e.symm.injective.ne hx
  have hνhom : ∀ (c : ℤ), 0 < c → ∀ x, ν (c • x) = (c : ℝ) * ν x := by
    intro c hc x
    dsimp [ν]
    rw [map_smul]
    exact hμhom c hc (e.symm x)
  have hνmin : ∀ x ≠ 0, ν z ≤ ν x := by
    intro x hx
    dsimp [ν, z]
    rw [e.symm_apply_apply]
    apply hmin
    simpa using e.symm.injective.ne hx
  have hzprim : Erdos407.Primitive.IsPrimitive z :=
    isPrimitive_of_minimal_gauge z hz ν hνpos hνhom hνmin
  refine ⟨hzprim, ?_⟩
  obtain ⟨B, hB⟩ := exists_basis_zero_eq_of_isPrimitive hn z hzprim
  refine ⟨B.map e.symm, ?_⟩
  rw [Basis.map_apply, hB]
  exact e.symm_apply_apply v

end

end Erdos407.PrimitiveExtension

end Erdos407_PrimitiveExtension

section Erdos407_MinkowskiSecondBox

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/




/-
# A non-sharp upper half of Minkowski's second theorem for boxes

This file proves the form of Minkowski's second theorem needed in the
three-place argument.  The proof is by dimension induction.  At each step a
shortest primitive lattice vector is made the first vector of an integral
basis, one coordinate on which its box norm is attained is deleted, and the
remaining lattice is projected along that vector.  Rounding the coefficient
of a lifted point costs at most one half of the shortest vector.  This gives
the harmless recurrence `C (n+1) = 2^n C n`.
-/

namespace Erdos407.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos407.AdelicMinkowski Set Module Submodule

/-- The dimension-only loss in the coordinate-projection proof. -/
noncomputable def minkowskiSecondConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (n * (n - 1) / 2)

@[simp] theorem minkowskiSecondConstant_zero : minkowskiSecondConstant 0 = 1 := by
  simp [minkowskiSecondConstant]

@[simp] theorem minkowskiSecondConstant_one : minkowskiSecondConstant 1 = 1 := by
  simp [minkowskiSecondConstant]

/-- A full lattice has a shortest nonzero vector for the sup norm. -/
theorem exists_shortest_nonzero_of_basis {n : ℕ}
    (b : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ)) :
    ∃ v : Fin (n + 1) → ℝ,
      v ∈ Submodule.span ℤ (Set.range b) ∧ v ≠ 0 ∧
        ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → ‖v‖ ≤ ‖x‖ := by
  classical
  let e : Fin (n + 1) := 0
  have hbe_mem : b e ∈ Submodule.span ℤ (Set.range b) :=
    Submodule.subset_span ⟨e, rfl⟩
  have hbe_ne : b e ≠ 0 := b.ne_zero e
  let S : Set (Fin (n + 1) → ℝ) :=
    Metric.closedBall 0 ‖b e‖ ∩ Submodule.span ℤ (Set.range b)
  have hSfin : S.Finite := by
    exact ZSpan.setFinite_inter b Metric.isBounded_closedBall
  let T : Set (Fin (n + 1) → ℝ) := {x ∈ S | x ≠ 0}
  have hTfin : T.Finite := hSfin.subset (by intro x hx; exact hx.1)
  have hbeS : b e ∈ S := by
    refine ⟨?_, hbe_mem⟩
    simp
  have hTne : T.Nonempty := ⟨b e, hbeS, hbe_ne⟩
  obtain ⟨v, hvT, hvmin⟩ := Set.exists_min_image T norm hTfin hTne
  refine ⟨v, hvT.1.2, hvT.2, ?_⟩
  intro x hxL hx0
  by_cases hxle : ‖x‖ ≤ ‖b e‖
  · exact hvmin x ⟨⟨by simpa [Metric.mem_closedBall] using hxle, hxL⟩, hx0⟩
  · have hvle : ‖v‖ ≤ ‖b e‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hvT.1.1
    exact hvle.trans (le_of_not_ge hxle)

/-- Any integral basis of the same full lattice has the same absolute real
determinant. -/
theorem abs_det_zspan_basis_eq {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (B : Basis (Fin n) ℤ (span ℤ (Set.range b))) :
    |(Matrix.of (((↑) : span ℤ (Set.range b) → (Fin n → ℝ)) ∘ B)).det| =
      |(Matrix.of b).det| := by
  let L : Submodule ℤ (Fin n → ℝ) := span ℤ (Set.range b)
  have hB := ZLattice.covolume_eq_det L B
  have hb := ZLattice.covolume_eq_det L
    (Erdos407.PrimitiveExtension.zspanBasis b)
  calc
    |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘ B)).det| =
        ZLattice.covolume L := hB.symm
    _ = |(Matrix.of (((↑) : L → (Fin n → ℝ)) ∘
        Erdos407.PrimitiveExtension.zspanBasis b)).det| := hb
    _ = |(Matrix.of b).det| := by
      congr 2
      ext i j
      simp [L]

/-- Cast an integral coordinate vector to a real coordinate vector. -/
def intCastVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ (z i : ℝ)

@[simp] theorem intCastVec_zero {n : ℕ} :
    intCastVec (0 : Fin n → ℤ) = 0 := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_add {n : ℕ} (z w : Fin n → ℤ) :
    intCastVec (z + w) = intCastVec z + intCastVec w := by
  funext i
  simp [intCastVec]

@[simp] theorem intCastVec_smul {n : ℕ} (a : ℤ) (z : Fin n → ℤ) :
    intCastVec (a • z) = (a : ℝ) • intCastVec z := by
  funext i
  simp [intCastVec]

/-- The sup norm is membership in a symmetric unit coordinate box. -/
theorem mem_realBox_const_iff_norm_le {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) :
    x ∈ realBox (fun _ ↦ s) ↔ ‖x‖ ≤ s := by
  rw [pi_norm_le_iff_of_nonneg hs]
  constructor
  · intro hx i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    constructor <;> intro i
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.1
    · have hi := hx i
      rw [Real.norm_eq_abs, abs_le] at hi
      exact hi.2

/-- The rounding operation used when lifting a projected lattice point. -/
noncomputable def roundedCoefficient (a : ℝ) : ℤ := round a

theorem abs_sub_roundedCoefficient_le_half (a : ℝ) :
    |a - (roundedCoefficient a : ℝ)| ≤ (1 : ℝ) / 2 := by
  simpa [roundedCoefficient] using abs_sub_round a

/-- Delete the coordinate `h` after projecting along `v` to the hyperplane
whose `h`-coordinate is zero. -/
noncomputable def deleteProjection {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ x (h.succAbove i) - (x h / v h) * v (h.succAbove i)

/-- `deleteProjection` bundled as a real linear map in its point argument. -/
noncomputable def deleteProjectionLinear {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := deleteProjection h v
  map_add' x y := by
    funext i
    simp only [deleteProjection, Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp [deleteProjection]
    ring

@[simp] theorem deleteProjectionLinear_apply {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) :
    deleteProjectionLinear h v x = deleteProjection h v x := rfl

theorem deleteProjection_add_smul {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (a : ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v (x + a • v) = deleteProjection h v x := by
  funext i
  simp only [deleteProjection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem deleteProjection_self {n : ℕ} (h : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) (hvh : v h ≠ 0) :
    deleteProjection h v v = 0 := by
  funext i
  simp [deleteProjection, hvh]

theorem abs_apply_le_norm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have hi := (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mp (le_refl ‖x‖) i
  simpa only [Real.norm_eq_abs] using hi

/-- If `h` is a coordinate on which the sup norm of `v` is attained, then a
point whose deleted projection has norm at most `t` can be reduced modulo
`v` into the box of radius `t + ‖v‖/2`. -/
theorem reducedLift_apply_le {n : ℕ} (h : Fin (n + 1))
    (v x : Fin (n + 1) → ℝ) (t a : ℝ)
    (hh : |v h| = ‖v‖) (hvh : v h ≠ 0)
    (ha : |x h / v h + a| ≤ (1 : ℝ) / 2)
    (hx : ‖deleteProjection h v x‖ ≤ t) :
    ‖x + a • v‖ ≤ t + ‖v‖ / 2 := by
  have ht : 0 ≤ t := (norm_nonneg _).trans hx
  rw [pi_norm_le_iff_of_nonneg (add_nonneg ht (by positivity))]
  rw [h.forall_iff_succAbove]
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have heq : x h + a * v h = (x h / v h + a) * v h := by
      field_simp
    rw [heq, abs_mul, hh]
    calc
      |x h / v h + a| * ‖v‖ ≤ ((1 : ℝ) / 2) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ha (norm_nonneg v)
      _ ≤ t + ‖v‖ / 2 := by linarith
  · intro j
    have hproj : |deleteProjection h v x j| ≤ t := by
      simpa only [Real.norm_eq_abs] using
        (abs_apply_le_norm (deleteProjection h v x) j).trans hx
    have hv : |v (h.succAbove j)| ≤ ‖v‖ :=
      abs_apply_le_norm v (h.succAbove j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    have hdecomp : x (h.succAbove j) + a * v (h.succAbove j) =
        deleteProjection h v x j +
          (x h / v h + a) * v (h.succAbove j) := by
      rw [deleteProjection]
      ring
    rw [hdecomp]
    calc
      |deleteProjection h v x j + (x h / v h + a) * v (h.succAbove j)| ≤
          |deleteProjection h v x j| +
            |x h / v h + a| * |v (h.succAbove j)| := by
            simpa only [abs_mul] using
              abs_add_le (deleteProjection h v x j)
                ((x h / v h + a) * v (h.succAbove j))
      _ ≤ t + ((1 : ℝ) / 2) * ‖v‖ := by
        exact add_le_add hproj
          (mul_le_mul ha hv (abs_nonneg _) (by norm_num))
      _ = t + ‖v‖ / 2 := by ring

/- ## The coordinate quotient determinant -/

/-- The elementary column shear which kills row `h` in every column except
the first one. -/
noncomputable def tailShear {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦
    if j = 0 then (if i = 0 then 1 else 0)
    else if i = 0 then -(B h j / B h 0)
    else if i = j then 1 else 0

@[simp] theorem tailShear_apply_zero_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    tailShear h B 0 0 = 1 := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n) :
    tailShear h B i.succ 0 = 0 := by simp [tailShear]

@[simp] theorem tailShear_apply_zero_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin n) :
    tailShear h B 0 j.succ = -(B h j.succ / B h 0) := by simp [tailShear]

@[simp] theorem tailShear_apply_succ_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin n) :
    tailShear h B i.succ j.succ = if i = j then 1 else 0 := by
  simp [tailShear]

theorem tailShear_det {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (tailShear h B).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = 0
    · subst i
      simp [tailShear]
    · simp [tailShear, hi]
  · intro i j hji
    have hi0 : i ≠ 0 := by
      intro hi
      subst i
      exact (not_lt_of_ge (Fin.zero_le j)) hji
    have hij : i ≠ j := ne_of_gt hji
    simp [tailShear, hi0, hij]

/-- The projected tail matrix after deleting row `h`. -/
noncomputable def projectedTail {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ B (h.succAbove i) j.succ -
    (B h j.succ / B h 0) * B (h.succAbove i) 0

theorem mul_tailShear_apply_zero {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    (B * tailShear h B) i 0 = B i 0 := by
  simp [Matrix.mul_apply, tailShear]

theorem mul_tailShear_apply_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (j : Fin n) :
    (B * tailShear h B) i j.succ =
      B i j.succ - (B h j.succ / B h 0) * B i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ, tailShear]
  ring

theorem mul_tailShear_pivot_succ {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hB : B h 0 ≠ 0)
    (j : Fin n) :
    (B * tailShear h B) h j.succ = 0 := by
  rw [mul_tailShear_apply_succ]
  field_simp
  ring

theorem mul_tailShear_minor {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (B * tailShear h B).submatrix h.succAbove Fin.succ = projectedTail h B := by
  ext i j
  simp [projectedTail, mul_tailShear_apply_succ]

/-- Exact covolume factor for the coordinate quotient. -/
theorem abs_det_eq_abs_pivot_mul_abs_det_projectedTail {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hB : B h 0 ≠ 0) :
    |B.det| = |B h 0| * |(projectedTail h B).det| := by
  have hdetC : (B * tailShear h B).det = B.det := by
    simp [Matrix.det_mul, tailShear_det]
  have hminor :
      (B * tailShear h B).submatrix h.succAbove (Fin.succAbove 0) =
        projectedTail h B := by
    simpa using mul_tailShear_minor h B
  have hLaplace := Matrix.det_succ_row (B * tailShear h B) h
  rw [Fin.sum_univ_succ] at hLaplace
  rw [mul_tailShear_apply_zero] at hLaplace
  simp_rw [mul_tailShear_pivot_succ h B hB] at hLaplace
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero] at hLaplace
  rw [hdetC] at hLaplace
  rw [hminor] at hLaplace
  rw [hLaplace, abs_mul, abs_mul]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul]

end Erdos407.MinkowskiSecondBox

end Erdos407_MinkowskiSecondBox

section Erdos407_MinkowskiSecondBoxBasis

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/


/-
# The projected-tail basis for the box reduction

The coordinate projection in `MinkowskiSecondBox` has nonsingular tail
matrix whenever the original matrix and chosen pivot are nonsingular.  This
module packages its columns as a real basis for the induction step.
-/

namespace Erdos407.MinkowskiSecondBox

open Module

/-- The projected tail matrix is nonsingular. -/
theorem projectedTail_det_ne_zero {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    (projectedTail h B).det ≠ 0 := by
  intro hq
  have habs := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h B hB
  rw [hq, abs_zero, mul_zero] at habs
  exact hdet (abs_eq_zero.mp habs)

/-- The columns of the projected tail matrix, as a real basis. -/
noncomputable def projectedTailBasis {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (projectedTail h B).col
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (projectedTail_det_ne_zero h B hdet hB))
    (by simp)

@[simp] theorem projectedTailBasis_apply {n : ℕ}
    (h : Fin (n + 1)) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hdet : B.det ≠ 0) (hB : B h 0 ≠ 0) (j : Fin n) :
    projectedTailBasis h B hdet hB j = (projectedTail h B).col j := by
  simp [projectedTailBasis]

end Erdos407.MinkowskiSecondBox

end Erdos407_MinkowskiSecondBoxBasis

section Erdos407_MinkowskiSecondBoxGlue

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/


/-
# Coordinate quotient glue for the box form of Minkowski's second theorem

This file records the compatibility of an integral combination of the tail
columns of a matrix with the coordinate quotient used in
`MinkowskiSecondBox`.
-/

namespace Erdos407.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos407.AdelicMinkowski Set Module Submodule

/-- The lift to the original space of an integral vector in the tail-column
coordinates.  Its first coordinate in the matrix basis is zero. -/
def rawTailLift {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (z : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  Matrix.mulVec B (Fin.cons 0 (intCastVec z))

/-- Taking the coordinate quotient of a raw tail lift is multiplication by
the projected tail matrix. -/
theorem deleteProjection_rawTailLift {n : ℕ} (h : Fin (n + 1))
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (z : Fin n → ℤ) :
    deleteProjection h (fun i ↦ B i 0) (rawTailLift B z) =
      Matrix.mulVec (projectedTail h B) (intCastVec z) := by
  funext i
  simp only [deleteProjection, rawTailLift, Matrix.mulVec, dotProduct,
    projectedTail]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero,
    zero_add]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The basis of `ℝ^n` whose columns are those of a nonsingular matrix. -/
noncomputable def matrixBasis {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map
    (D.toLinearEquiv' (D.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hD)))

@[simp] theorem matrixBasis_apply {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : D.det ≠ 0) (j : Fin n) :
    matrixBasis D hD j = fun i ↦ D i j := by
  ext i
  rw [matrixBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Matrix.mulVec D (Pi.single j 1) i = D i j
  simp [Matrix.mulVec]

/- ## Induction for the unit cube -/

theorem minkowskiSecondConstant_succ (n : ℕ) :
    minkowskiSecondConstant (n + 1) =
      (2 : ℝ) ^ n * minkowskiSecondConstant n := by
  unfold minkowskiSecondConstant
  have he : (n + 1) * ((n + 1) - 1) / 2 = n + n * (n - 1) / 2 := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right]
    simp [Nat.choose_succ_succ]
  rw [he, pow_add]

theorem exists_abs_apply_eq_norm {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∃ h, |x h| = ‖x‖ := by
  classical
  obtain ⟨h, -, hh⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    Finset.univ_nonempty
  refine ⟨h, le_antisymm (abs_apply_le_norm x h) ?_⟩
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg (x h))]
  intro i
  simpa only [Real.norm_eq_abs] using hh i (Finset.mem_univ i)

theorem realBox_smul_one_eq_const {n : ℕ} (s : ℝ) :
    realBox (s • (fun _ : Fin n ↦ (1 : ℝ))) = realBox (fun _ ↦ s) := by
  congr 1
  funext i
  simp

/-- The upper half of Minkowski's second theorem for a full lattice and the
unit coordinate cube.  The factor is `2^(n(n-1)/2)`. -/
theorem cube_has_successiveProductCertificate :
    ∀ {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ)),
      Nonempty (SuccessiveProductCertificate
        (span ℤ (Set.range b)).toAddSubgroup (fun _ ↦ 1)
        (minkowskiSecondConstant n * |(Matrix.of b).det|)) := by
  intro n
  induction n with
  | zero =>
      intro b
      refine ⟨{
        scale := fun i ↦ Fin.elim0 i
        point := fun i ↦ Fin.elim0 i
        scale_nonneg := fun i ↦ Fin.elim0 i
        point_mem := fun i ↦ Fin.elim0 i
        independent := linearIndependent_empty_type
        mem_scaledBox := fun i ↦ Fin.elim0 i
        product_le := ?_ }⟩
      simp [minkowskiSecondConstant]
  | succ n ih =>
      intro b
      classical
      let L : Submodule ℤ (Fin (n + 1) → ℝ) := span ℤ (Set.range b)
      obtain ⟨v, hvL, hv0, hvmin⟩ := exists_shortest_nonzero_of_basis b
      let vL : L := ⟨v, hvL⟩
      have hvL0 : vL ≠ 0 := by
        intro h
        apply hv0
        exact congrArg Subtype.val h
      have hμpos : ∀ x : L, x ≠ 0 → 0 < ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact norm_pos_iff.mpr (by
          intro h
          apply hx
          exact Subtype.ext h)
      have hμhom : ∀ (c : ℤ), 0 < c → ∀ x : L,
          ‖((c • x : L) : Fin (n + 1) → ℝ)‖ =
            (c : ℝ) * ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro c hc x
        have hcast : (((c • x : L) : Fin (n + 1) → ℝ)) =
            (c : ℝ) • (x : Fin (n + 1) → ℝ) := by
          ext i
          simp
        rw [hcast]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos]
        exact_mod_cast hc
      have hμmin : ∀ x : L, x ≠ 0 →
          ‖(vL : Fin (n + 1) → ℝ)‖ ≤ ‖(x : Fin (n + 1) → ℝ)‖ := by
        intro x hx
        exact hvmin x x.property (by
          intro h
          apply hx
          exact Subtype.ext h)
      obtain ⟨-, Bz, hBz0⟩ :=
        Erdos407.PrimitiveExtension.shortest_zspan_vector_primitive_and_extends
          (Nat.succ_pos n) b vL hvL0
          (fun x : L ↦ ‖(x : Fin (n + 1) → ℝ)‖) hμpos hμhom hμmin
      let b' : Basis (Fin (n + 1)) ℝ (Fin (n + 1) → ℝ) :=
        Bz.ofZLatticeBasis ℝ L
      have hb'0 : b' 0 = v := by
        rw [show b' 0 = ((Bz 0 : L) : Fin (n + 1) → ℝ) by
          exact Basis.ofZLatticeBasis_apply ℝ L Bz 0]
        exact congrArg Subtype.val (by simpa using hBz0)
      have hb'span : span ℤ (Set.range b') = L := by
        exact Bz.ofZLatticeBasis_span ℝ L
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (Matrix.of b')ᵀ
      have hMdet : M.det ≠ 0 := by
        have hbdet : (Pi.basisFun ℝ (Fin (n + 1))).det b' ≠ 0 :=
          (AlternatingMap.map_basis_ne_zero_iff b'
            (Pi.basisFun ℝ (Fin (n + 1))).det).mpr
              (Pi.basisFun ℝ (Fin (n + 1))).det_ne_zero
        rw [Pi.basisFun_det_apply] at hbdet
        simpa [M] using hbdet
      obtain ⟨h, hh⟩ := exists_abs_apply_eq_norm v
      have hvh : v h ≠ 0 := by
        intro hz
        have : ‖v‖ = 0 := by simpa [hz] using hh.symm
        exact hv0 (norm_eq_zero.mp this)
      have hMh0 : M h 0 ≠ 0 := by
        simpa [M, Matrix.of_apply, hb'0] using hvh
      let Q : Matrix (Fin n) (Fin n) ℝ := projectedTail h M
      have hQdet : Q.det ≠ 0 := projectedTail_det_ne_zero h M hMdet hMh0
      let qB : Basis (Fin n) ℝ (Fin n → ℝ) := projectedTailBasis h M hMdet hMh0
      obtain ⟨cq⟩ := ih qB
      have hQpoint : ∀ j, ∃ z : Fin n → ℤ,
          Matrix.mulVec Q (intCastVec z) = cq.point j := by
        intro j
        have hm := cq.point_mem j
        change cq.point j ∈ span ℤ (Set.range qB) at hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨z, hz⟩ := hm
        refine ⟨z, ?_⟩
        rw [← hz]
        ext i
        simp [Q, qB, Matrix.mulVec, dotProduct, intCastVec, mul_comm]
      choose z hz using hQpoint
      let raw : Fin n → Fin (n + 1) → ℝ := fun j ↦ rawTailLift M (z j)
      let a : Fin n → ℤ := fun j ↦ -roundedCoefficient (raw j h / v h)
      let lift : Fin n → Fin (n + 1) → ℝ :=
        fun j ↦ raw j + (a j) • v
      let scale : Fin (n + 1) → ℝ := Fin.cons ‖v‖ (fun j ↦ 2 * cq.scale j)
      let point : Fin (n + 1) → Fin (n + 1) → ℝ := Fin.cons v lift
      have hraw_eq : ∀ j, raw j = ∑ k, (z j k) • b' k.succ := by
        intro j
        ext i
        simp [raw, rawTailLift, M, Matrix.mulVec, dotProduct, intCastVec,
          Fin.sum_univ_succ, mul_comm]
      have hrawL : ∀ j, raw j ∈ L := by
        intro j
        rw [hraw_eq]
        rw [← hb'span]
        apply sum_mem
        intro k hk
        exact smul_mem _ _ (subset_span (Set.mem_range_self k.succ))
      have hliftL : ∀ j, lift j ∈ L := by
        intro j
        change raw j + (a j) • v ∈ L
        exact add_mem (hrawL j) (smul_mem L (a j) hvL)
      have hcol0 : (fun i ↦ M i 0) = v := by
        funext i
        simp [M, Matrix.of_apply, hb'0]
      have hproj_raw : ∀ j, deleteProjection h v (raw j) = cq.point j := by
        intro j
        rw [← hcol0]
        rw [deleteProjection_rawTailLift]
        exact hz j
      have hproj_lift : ∀ j, deleteProjection h v (lift j) = cq.point j := by
        intro j
        change deleteProjection h v (raw j + (a j) • v) = cq.point j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        rw [hcast, deleteProjection_add_smul h v (raw j) (a j : ℝ) hvh]
        exact hproj_raw j
      have hqnorm : ∀ j, ‖cq.point j‖ ≤ cq.scale j := by
        intro j
        apply (mem_realBox_const_iff_norm_le (cq.scale_nonneg j) _).mp
        rw [← realBox_smul_one_eq_const]
        exact cq.mem_scaledBox j
      have ha : ∀ j, |raw j h / v h + (a j : ℝ)| ≤ (1 : ℝ) / 2 := by
        intro j
        simpa [a, sub_eq_add_neg] using
          abs_sub_roundedCoefficient_le_half (raw j h / v h)
      have hlift_upper : ∀ j, ‖lift j‖ ≤ cq.scale j + ‖v‖ / 2 := by
        intro j
        have hcast : (a j) • v = (a j : ℝ) • v := by
          ext i
          simp
        change ‖raw j + (a j) • v‖ ≤ cq.scale j + ‖v‖ / 2
        rw [hcast]
        exact reducedLift_apply_le h v (raw j) (cq.scale j) (a j : ℝ)
          hh hvh (ha j) ((congrArg norm (hproj_raw j)).le.trans (hqnorm j))
      have hlift0 : ∀ j, lift j ≠ 0 := by
        intro j hj
        apply cq.independent.ne_zero j
        rw [← hproj_lift j, hj]
        ext i
        simp [deleteProjection]
      have hshortlift : ∀ j, ‖v‖ ≤ ‖lift j‖ := by
        intro j
        exact hvmin (lift j) (hliftL j) (hlift0 j)
      have hliftnorm : ∀ j, ‖lift j‖ ≤ 2 * cq.scale j := by
        intro j
        have hu := hlift_upper j
        have hs := hshortlift j
        linarith
      have hind : LinearIndependent ℝ point := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hprojrel : ∑ j, g j.succ • cq.point j = 0 := by
          have hm := congrArg (deleteProjectionLinear h v) hg
          rw [map_sum] at hm
          rw [Fin.sum_univ_succ] at hm
          simp only [point, Fin.cons_zero, Fin.cons_succ] at hm
          rw [map_smul, deleteProjectionLinear_apply,
            deleteProjection_self h v hvh, smul_zero, zero_add] at hm
          simp only [map_smul, deleteProjectionLinear_apply, map_zero] at hm
          simp_rw [hproj_lift] at hm
          exact hm
        have htail : ∀ j : Fin n, g j.succ = 0 :=
          (Fintype.linearIndependent_iff.mp cq.independent) _ hprojrel
        refine Fin.cases ?_ htail i
        rw [Fin.sum_univ_succ] at hg
        simp only [point, Fin.cons_zero, Fin.cons_succ] at hg
        simp_rw [htail] at hg
        simp only [zero_smul, Finset.sum_const_zero, add_zero] at hg
        exact (smul_eq_zero.mp hg).resolve_right hv0
      have hqdet : |(Matrix.of qB).det| = |Q.det| := by
        have hmat : Matrix.of qB = Qᵀ := by
          ext i j
          simp [qB, Q, Matrix.of_apply, Matrix.col]
        rw [hmat, Matrix.det_transpose]
      have hMabs : |M.det| = |(Matrix.of b).det| := by
        have hchange := abs_det_zspan_basis_eq b Bz
        have hmat : Matrix.of (((↑) : L → (Fin (n + 1) → ℝ)) ∘ Bz) =
            Matrix.of b' := by
          ext i j
          simp [b', Matrix.of_apply]
        rw [hmat] at hchange
        simpa [M] using hchange
      have hfactor : |(Matrix.of b).det| = ‖v‖ * |Q.det| := by
        rw [← hMabs]
        have hd := abs_det_eq_abs_pivot_mul_abs_det_projectedTail h M hMh0
        have hentry : M h 0 = v h := congrFun hcol0 h
        rw [hentry, hh] at hd
        simpa [Q] using hd
      refine ⟨{
        scale := scale
        point := point
        scale_nonneg := ?_
        point_mem := ?_
        independent := hind
        mem_scaledBox := ?_
        product_le := ?_ }⟩
      · intro i
        refine Fin.cases (norm_nonneg v) (fun j ↦ ?_) i
        exact mul_nonneg (by norm_num) (cq.scale_nonneg j)
      · intro i
        refine Fin.cases hvL (fun j ↦ hliftL j) i
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rw [realBox_smul_one_eq_const]
          apply (mem_realBox_const_iff_norm_le (norm_nonneg v) v).mpr
          simp
        · have hm := (mem_realBox_const_iff_norm_le
              (mul_nonneg (by norm_num) (cq.scale_nonneg j)) (lift j)).mpr
              (hliftnorm j)
          rw [realBox_smul_one_eq_const]
          simpa [scale, point] using hm
      · have hcq : ∏ j, cq.scale j ≤ minkowskiSecondConstant n * |Q.det| := by
          simpa [hqdet] using cq.product_le
        calc
          ∏ i, scale i = ‖v‖ * ((2 : ℝ) ^ n * ∏ j, cq.scale j) := by
            simp [scale, Fin.prod_univ_succ, Finset.prod_mul_distrib,
              Finset.prod_const]
          _ ≤ ‖v‖ * ((2 : ℝ) ^ n *
              (minkowskiSecondConstant n * |Q.det|)) := by
            gcongr
          _ = minkowskiSecondConstant (n + 1) * |(Matrix.of b).det| := by
            rw [minkowskiSecondConstant_succ, hfactor]
            ring

end Erdos407.MinkowskiSecondBox

end Erdos407_MinkowskiSecondBoxGlue

section Erdos407_MinkowskiDiagonalNormalization

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/



/-
# Diagonal normalization of coordinate boxes

This file transports a full real lattice and a rectangular coordinate box
through the diagonal map `x i ↦ x i / r i`.  It isolates the normalization
step used in the dimension-induction proof of Minkowski's second theorem for
boxes.
-/

namespace Erdos407.MinkowskiDiagonalNormalization

open scoped BigOperators Matrix
open Erdos407.AdelicMinkowski Set Submodule Module

noncomputable section

/-- Divide each coordinate by a prescribed positive radius. -/
def divideCoordinates {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i / r i
  invFun x i := x i * r i
  left_inv x := by
    funext i
    exact div_mul_cancel₀ (x i) (hr i).ne'
  right_inv x := by
    funext i
    exact mul_div_cancel_right₀ (x i) (hr i).ne'
  map_add' x y := by
    funext i
    exact add_div (x i) (y i) (r i)
  map_smul' a x := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc]

@[simp] theorem divideCoordinates_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    divideCoordinates r hr x i = x i / r i := rfl

@[simp] theorem divideCoordinates_symm_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    (divideCoordinates r hr).symm x i = x i * r i := rfl

/-- The basis obtained after dividing every ambient coordinate by its radius. -/
def normalizedBasis {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  b.map (divideCoordinates r hr)

@[simp] theorem normalizedBasis_apply {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (j i : Fin n) :
    normalizedBasis b r hr j i = b j i / r i := by
  simp [normalizedBasis]

/-- A rectangular box becomes a constant-radius box after diagonal
normalization. -/
theorem mem_realBox_mul_iff {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (s : ℝ) (_hs : 0 ≤ s) (x : Fin n → ℝ) :
    x ∈ realBox (fun i ↦ s * r i) ↔
      divideCoordinates r hr x ∈ realBox (fun _ ↦ s) := by
  constructor
  · intro hx
    constructor
    · intro i
      apply (le_div_iff₀ (hr i)).2
      simpa [mul_comm] using hx.1 i
    · intro i
      apply (div_le_iff₀ (hr i)).2
      simpa [mul_comm] using hx.2 i
  · intro hx
    constructor
    · intro i
      have hi := (le_div_iff₀ (hr i)).1 (hx.1 i)
      simpa [mul_comm] using hi
    · intro i
      have hi := (div_le_iff₀ (hr i)).1 (hx.2 i)
      simpa [mul_comm] using hi

/-- Diagonal normalization divides the absolute determinant by the product
of the radii. -/
theorem abs_det_normalizedBasis {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    |(Matrix.of (normalizedBasis b r hr)).det| =
      |(Matrix.of b).det| * (∏ i, r i)⁻¹ := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i ↦ (r i)⁻¹)
  have hmatrix : Matrix.of (normalizedBasis b r hr) = Matrix.of b * D := by
    ext j i
    change b j i / r i = ∑ k, b j k * D k i
    rw [Finset.sum_eq_single i]
    · simp [D, div_eq_mul_inv]
    · intro k _ hki
      simp [D, hki]
    · simp
  have hdetD : D.det = (∏ i, r i)⁻¹ := by
    simp [D, Finset.prod_inv_distrib]
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ ↦ hr i
  rw [hmatrix, Matrix.det_mul, hdetD, abs_mul, abs_inv, abs_of_pos hprod]

/-- The diagonal equivalence carries the integral span of a basis onto the
integral span of the normalized basis. -/
theorem divideCoordinates_mem_span_iff {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) :
    divideCoordinates r hr x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔
      x ∈ Submodule.span ℤ (Set.range b) := by
  let e : (Fin n → ℝ) ≃ₗ[ℤ] (Fin n → ℝ) :=
    (divideCoordinates r hr).restrictScalars ℤ
  have hrange : Set.range (normalizedBasis b r hr) = e '' Set.range b := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      simp [e, normalizedBasis]
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [e, normalizedBasis]
  change e x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔ _
  rw [hrange]
  exact Submodule.apply_mem_span_image_iff_mem_span e.injective

end

end Erdos407.MinkowskiDiagonalNormalization

end Erdos407_MinkowskiDiagonalNormalization

section Erdos407_MinkowskiSecondInduction

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/



/-
# The rectangular-box form of Minkowski's second theorem

The coordinate induction in `MinkowskiSecondBoxGlue` constructs the product
certificate for the unit cube.  Diagonal normalization transports it to a
box with arbitrary positive coordinate radii.
-/

namespace Erdos407.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos407.AdelicMinkowski Set Module Submodule

noncomputable section

/-- The rectangular-box form of the upper half of Minkowski's second
theorem, obtained by diagonal normalization from the unit-cube induction. -/
theorem realBox_has_minkowskiSecondCertificate {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Nonempty (AdelicMinkowski.SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range b)).toAddSubgroup r
      (minkowskiSecondConstant n * |(Matrix.of b).det| *
        (∏ i, r i)⁻¹)) := by
  classical
  open Erdos407.MinkowskiDiagonalNormalization in
    let b' := normalizedBasis b r hr
    let e := divideCoordinates r hr
    obtain ⟨C⟩ := cube_has_successiveProductCertificate b'
    let point : Fin n → Fin n → ℝ := fun i ↦ e.symm (C.point i)
    refine ⟨{
      scale := C.scale
      point := point
      scale_nonneg := C.scale_nonneg
      point_mem := ?_
      independent := ?_
      mem_scaledBox := ?_
      product_le := ?_ }⟩
    · intro i
      change point i ∈ Submodule.span ℤ (Set.range b)
      apply (divideCoordinates_mem_span_iff b r hr (point i)).mp
      simpa [point, e, b'] using C.point_mem i
    · apply LinearIndependent.of_comp e.toLinearMap
      convert C.independent using 1
      funext i
      simp [point, e]
    · intro i
      change point i ∈ realBox (fun j ↦ C.scale i * r j)
      apply (mem_realBox_mul_iff r hr (C.scale i) (C.scale_nonneg i) (point i)).mpr
      have hi : C.point i ∈ realBox (fun _ ↦ C.scale i) := by
        rw [← realBox_smul_one_eq_const]
        exact C.mem_scaledBox i
      simpa [point, e] using hi
    · simpa [b', abs_det_normalizedBasis, mul_assoc] using C.product_le

end

end Erdos407.MinkowskiSecondBox

end Erdos407_MinkowskiSecondInduction

section Erdos587_BohrProgression

open scoped BigOperators Matrix Pointwise

namespace Erdos587

open Erdos407.AdelicMinkowski
open Erdos407.MinkowskiSecondBox

noncomputable section

/-
## A full congruence lattice for a cyclic Bohr set

The distinguished zeroth character is `1`.  The remaining coordinates list
the supplied frequencies.  The lattice basis has first column
`(1, k₁, ..., k_d)` (using standard representatives) and remaining columns
`N e_i`.  Consequently its determinant is `N^d`, while every lattice point
satisfies the simultaneous congruences needed for the Bohr set.
-/

noncomputable def indexedCyclicCharacter {N : ℕ}
    (Gamma : Finset (ZMod N)) : Fin (Gamma.card + 1) → ZMod N :=
  Fin.cases 1 fun i => (Gamma.equivFin.symm i : Gamma)

@[simp] lemma indexedCyclicCharacter_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) : indexedCyclicCharacter Gamma 0 = 1 := rfl

def bohrLatticeMatrixInt {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℤ :=
  fun i j => if j = 0 then ((indexedCyclicCharacter Gamma i).val : ℤ)
    else if i = j then (N : ℤ) else 0

def bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) :
    Matrix (Fin (Gamma.card + 1)) (Fin (Gamma.card + 1)) ℝ :=
  (bohrLatticeMatrixInt Gamma).map (Int.castRingHom ℝ)

@[simp] lemma bohrLatticeMatrixInt_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrixInt Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrixInt, (Fin.succ_ne_zero j).symm]

@[simp] lemma bohrLatticeMatrix_zero_zero {N : ℕ}
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    bohrLatticeMatrix Gamma 0 0 = 1 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1)]

@[simp] lemma bohrLatticeMatrix_zero_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma 0 j.succ = 0 := by
  simp [bohrLatticeMatrix]

@[simp] lemma bohrLatticeMatrix_succ_succ {N : ℕ}
    (Gamma : Finset (ZMod N)) (i j : Fin Gamma.card) :
    bohrLatticeMatrix Gamma i.succ j.succ =
      if i = j then (N : ℝ) else 0 := by
  simp [bohrLatticeMatrix, bohrLatticeMatrixInt, Fin.succ_inj]

lemma det_bohrLatticeMatrix {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det = (N : ℝ) ^ Gamma.card := by
  have hminor :
      (bohrLatticeMatrix Gamma).submatrix Fin.succ (Fin.succAbove 0) =
        Matrix.diagonal (fun _ : Fin Gamma.card => (N : ℝ)) := by
    ext i j
    rw [Matrix.diagonal_apply]
    simp [Matrix.submatrix]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [bohrLatticeMatrix_zero_zero Gamma hN, bohrLatticeMatrix_zero_succ]
  rw [hminor]
  rw [Matrix.det_diagonal]
  simp

lemma det_bohrLatticeMatrix_ne_zero {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    (bohrLatticeMatrix Gamma).det ≠ 0 := by
  rw [det_bohrLatticeMatrix Gamma hN]
  positivity

noncomputable def bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Module.Basis (Fin (Gamma.card + 1)) ℝ
      (Fin (Gamma.card + 1) → ℝ) :=
  matrixBasis (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN)

@[simp] lemma bohrLatticeBasis_apply {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (j i : Fin (Gamma.card + 1)) :
    bohrLatticeBasis Gamma hN j i = bohrLatticeMatrix Gamma i j := by
  exact congrFun (matrixBasis_apply (bohrLatticeMatrix Gamma)
    (det_bohrLatticeMatrix_ne_zero Gamma hN) j) i

def bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  Matrix.mulVec (bohrLatticeMatrixInt Gamma) z

lemma intCastVec_bohrLatticePoint {N : ℕ} (Gamma : Finset (ZMod N))
    (z : Fin (Gamma.card + 1) → ℤ) :
    intCastVec (bohrLatticePoint Gamma z) =
      Matrix.mulVec (bohrLatticeMatrix Gamma) (intCastVec z) := by
  funext i
  simp [bohrLatticePoint, bohrLatticeMatrix, Matrix.mulVec, dotProduct,
    intCastVec]

lemma bohrLatticePoint_zero {N : ℕ} (Gamma : Finset (ZMod N)) (hN : 1 < N)
    (z : Fin (Gamma.card + 1) → ℤ) :
    bohrLatticePoint Gamma z 0 = z 0 := by
  simp [bohrLatticePoint, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    bohrLatticeMatrixInt, ZMod.val_one'' (by omega : N ≠ 1),
    (fun x : Fin Gamma.card => (Fin.succ_ne_zero x).symm)]

lemma bohrLatticePoint_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (z : Fin (Gamma.card + 1) → ℤ)
    (hN : 1 < N)
    (i : Fin (Gamma.card + 1)) :
    (bohrLatticePoint Gamma z i : ZMod N) =
      (bohrLatticePoint Gamma z 0 : ZMod N) *
        indexedCyclicCharacter Gamma i := by
  rw [bohrLatticePoint_zero Gamma hN]
  simp only [bohrLatticePoint, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_succ]
  simp only [bohrLatticeMatrixInt]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [mul_comm]

/- ## Centred progressions in a finite cyclic group -/

structure CyclicCenteredGAP (N : ℕ) where
  rank : ℕ
  step : Fin rank → ZMod N
  radius : Fin rank → ℕ

namespace CyclicCenteredGAP

abbrev Param {N : ℕ} (Q : CyclicCenteredGAP N) :=
  (i : Fin Q.rank) → Fin (2 * Q.radius i + 1)

def coeff {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) : ℤ := (x i : ℤ) - Q.radius i

def eval {N : ℕ} (Q : CyclicCenteredGAP N) (x : Q.Param) : ZMod N :=
  ∑ i, (Q.coeff x i : ZMod N) * Q.step i

noncomputable def carrier {N : ℕ} (Q : CyclicCenteredGAP N) : Finset (ZMod N) :=
  (Finset.univ : Finset Q.Param).image Q.eval

def Proper {N : ℕ} (Q : CyclicCenteredGAP N) : Prop :=
  Function.Injective Q.eval

lemma card_carrier_of_proper {N : ℕ} (Q : CyclicCenteredGAP N)
    (hQ : Q.Proper) :
    Q.carrier.card = ∏ i, (2 * Q.radius i + 1) := by
  rw [carrier, Finset.card_image_of_injective _ hQ, Finset.card_univ]
  simp [Param]

lemma coeff_abs_le {N : ℕ} (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i| ≤ (Q.radius i : ℤ) := by
  change |(x i : ℤ) - Q.radius i| ≤ (Q.radius i : ℤ)
  rw [abs_le]
  have hi := (x i).isLt
  change (x i : ℕ) < 2 * Q.radius i + 1 at hi
  constructor <;> omega

lemma coeff_sub_abs_le_two_mul {N : ℕ} (Q : CyclicCenteredGAP N)
    (x y : Q.Param) (i : Fin Q.rank) :
    |Q.coeff x i - Q.coeff y i| ≤ (2 * Q.radius i : ℕ) := by
  calc
    |Q.coeff x i - Q.coeff y i| ≤
        |Q.coeff x i| + |Q.coeff y i| := abs_sub _ _
    _ ≤ (Q.radius i : ℤ) + Q.radius i :=
      add_le_add (Q.coeff_abs_le x i) (Q.coeff_abs_le y i)
    _ = (2 * Q.radius i : ℕ) := by push_cast; ring

end CyclicCenteredGAP

/- ## Integral representatives of a successive-minimum certificate -/

noncomputable def bohrSuccessiveCertificate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range (bohrLatticeBasis Gamma hN))).toAddSubgroup
      (fun _ => R)
      (minkowskiSecondConstant (Gamma.card + 1) *
        |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
          (∏ _i : Fin (Gamma.card + 1), R)⁻¹) :=
  Classical.choice
    (realBox_has_minkowskiSecondCertificate
      (bohrLatticeBasis Gamma hN) (fun _ => R) (fun _ => hR))

noncomputable def bohrCertificateCoeff {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  Classical.choose
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

lemma bohrCertificateCoeff_spec {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    ∑ j, bohrCertificateCoeff Gamma hN R hR i j •
        bohrLatticeBasis Gamma hN j =
      (bohrSuccessiveCertificate Gamma hN R hR).point i :=
  Classical.choose_spec
    ((Submodule.mem_span_range_iff_exists_fun ℤ).mp
      ((bohrSuccessiveCertificate Gamma hN R hR).point_mem i))

noncomputable def bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : Fin (Gamma.card + 1) → ℤ :=
  bohrLatticePoint Gamma (bohrCertificateCoeff Gamma hN R hR i)

lemma intCastVec_bohrCertificatePoint {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    intCastVec (bohrCertificatePoint Gamma hN R hR i) =
      (bohrSuccessiveCertificate Gamma hN R hR).point i := by
  rw [bohrCertificatePoint, intCastVec_bohrLatticePoint]
  rw [← bohrCertificateCoeff_spec Gamma hN R hR i]
  funext k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [bohrLatticeBasis_apply]
  simp [intCastVec, mul_comm]

lemma bohrCertificatePoint_independent {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    LinearIndependent ℝ (fun i =>
      intCastVec (bohrCertificatePoint Gamma hN R hR i)) := by
  simpa only [intCastVec_bohrCertificatePoint] using
    (bohrSuccessiveCertificate Gamma hN R hR).independent

lemma bohrCertificate_scale_pos {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hs := C.scale_nonneg i
  refine hs.lt_of_ne ?_
  intro hz
  have hpzero : C.point i = 0 := by
    have hm := C.mem_scaledBox i
    rw [← hz, zero_smul] at hm
    ext j
    have hlo := hm.1 j
    have hhi := hm.2 j
    simp only [Pi.zero_apply, neg_zero] at hlo hhi
    exact le_antisymm hhi hlo
  exact C.independent.ne_zero i hpzero

noncomputable def bohrProgressionRadius {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) : ℕ :=
  ⌊((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹⌋₊

noncomputable def bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R) :
    CyclicCenteredGAP N where
  rank := Gamma.card + 1
  step i := (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N)
  radius := bohrProgressionRadius Gamma hN R hR

lemma bohrProgressionRadius_mul_scale_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (bohrProgressionRadius Gamma hN R hR i : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i ≤
      1 / (4 * (Gamma.card + 1) : ℝ) := by
  let s := (bohrSuccessiveCertificate Gamma hN R hR).scale i
  have hs : 0 < s := bohrCertificate_scale_pos Gamma hN R hR i
  have hm : (0 : ℝ) < 4 * (Gamma.card + 1) := by positivity
  have hfloor :
      (bohrProgressionRadius Gamma hN R hR i : ℝ) ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ := by
    apply Nat.floor_le
    positivity
  calc
    (bohrProgressionRadius Gamma hN R hR i : ℝ) * s ≤
        ((4 * (Gamma.card + 1) : ℝ) * s)⁻¹ * s :=
      mul_le_mul_of_nonneg_right hfloor hs.le
    _ = 1 / (4 * (Gamma.card + 1) : ℝ) := by
      field_simp

lemma abs_intCast_bohrCertificatePoint_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i j : Fin (Gamma.card + 1)) :
    |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      (bohrSuccessiveCertificate Gamma hN R hR).scale i * R := by
  let C := bohrSuccessiveCertificate Gamma hN R hR
  have hm := C.mem_scaledBox i
  have hlo := hm.1 j
  have hhi := hm.2 j
  rw [← intCastVec_bohrCertificatePoint Gamma hN R hR i] at hlo hhi
  change -(C.scale i * R) ≤
      (bohrCertificatePoint Gamma hN R hR i j : ℝ) at hlo
  change (bohrCertificatePoint Gamma hN R hR i j : ℝ) ≤
      C.scale i * R at hhi
  exact (abs_le.mpr ⟨hlo, hhi⟩)

def bohrCertificateCombination {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) : Fin (Gamma.card + 1) → ℤ :=
  fun j => ∑ i, u i * bohrCertificatePoint Gamma hN R hR i j

lemma bohrCertificateCombination_cast_coordinate {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (u : Fin (Gamma.card + 1) → ℤ) (j : Fin (Gamma.card + 1)) :
    (bohrCertificateCombination Gamma hN R hR u j : ZMod N) =
      (bohrCertificateCombination Gamma hN R hR u 0 : ZMod N) *
        indexedCyclicCharacter Gamma j := by
  simp only [bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hp := bohrLatticePoint_cast_coordinate Gamma
    (bohrCertificateCoeff Gamma hN R hR i) hN j
  change (bohrCertificatePoint Gamma hN R hR i j : ZMod N) =
    (bohrCertificatePoint Gamma hN R hR i 0 : ZMod N) *
      indexedCyclicCharacter Gamma j at hp
  rw [hp]
  ring

lemma abs_intCast_bohrCertificateCombination_le {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (a : ℕ) (u : Fin (Gamma.card + 1) → ℤ)
    (hu : ∀ i, |u i| ≤ (a * bohrProgressionRadius Gamma hN R hR i : ℕ))
    (j : Fin (Gamma.card + 1)) :
    |(bohrCertificateCombination Gamma hN R hR u j : ℝ)| ≤
      (a : ℝ) * R / 4 := by
  let m := Gamma.card + 1
  have hm : (0 : ℝ) < m := by positivity
  have hR0 : 0 ≤ R := hR.le
  have hterm (i : Fin m) :
      |(u i : ℝ) *
          (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        (a : ℝ) * R / (4 * m : ℝ) := by
    rw [abs_mul]
    have huR : |(u i : ℝ)| ≤
        (a : ℝ) * bohrProgressionRadius Gamma hN R hR i := by
      rw [← Int.cast_abs]
      exact_mod_cast hu i
    calc
      |(u i : ℝ)| *
          |(bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
        ((a : ℝ) * bohrProgressionRadius Gamma hN R hR i) *
          ((bohrSuccessiveCertificate Gamma hN R hR).scale i * R) := by
            gcongr
            exact abs_intCast_bohrCertificatePoint_le Gamma hN R hR i j
      _ = (a : ℝ) *
          ((bohrProgressionRadius Gamma hN R hR i : ℝ) *
            (bohrSuccessiveCertificate Gamma hN R hR).scale i) * R := by ring
      _ ≤ (a : ℝ) * (1 / (4 * m : ℝ)) * R := by
        gcongr
        simpa [m, Nat.cast_add, Nat.cast_one] using
          bohrProgressionRadius_mul_scale_le Gamma hN R hR i
      _ = (a : ℝ) * R / (4 * m : ℝ) := by ring
  have hcast : (bohrCertificateCombination Gamma hN R hR u j : ℝ) =
      ∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ) := by
    simp [bohrCertificateCombination]
  rw [hcast]
  calc
    |∑ i, (u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| ≤
      ∑ i, |(u i : ℝ) *
        (bohrCertificatePoint Gamma hN R hR i j : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, ((a : ℝ) * R / (4 * m : ℝ)) := by
      exact Finset.sum_le_sum fun i hi => hterm i
    _ = (a : ℝ) * R / 4 := by
      simp [m]
      field_simp

lemma eval_bohrCyclicProgression {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (x : (bohrCyclicProgression Gamma hN R hR).Param) :
    (bohrCyclicProgression Gamma hN R hR).eval x =
      (bohrCertificateCombination Gamma hN R hR
        ((bohrCyclicProgression Gamma hN R hR).coeff x) 0 : ZMod N) := by
  simp only [CyclicCenteredGAP.eval, bohrCyclicProgression,
    bohrCertificateCombination, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

lemma int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt {N : ℕ} [NeZero N]
    {t : ℤ} (ht0 : (t : ZMod N) = 0) (htN : |(t : ℝ)| < N) : t = 0 := by
  have hdvd : (N : ℤ) ∣ t :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd t N).mp ht0
  have habs : (t.natAbs : ℝ) = |(t : ℝ)| := by
    calc
      (t.natAbs : ℝ) = (((t.natAbs : ℕ) : ℤ) : ℝ) := by norm_num
      _ = ((|t| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(t : ℝ)| := Int.cast_abs
  have hnat : t.natAbs < N := by
    exact_mod_cast (habs.trans_lt htN)
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  simpa using hnat

theorem bohrCyclicProgression_proper {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    (bohrCyclicProgression Gamma hN R hR).Proper := by
  let Q := bohrCyclicProgression Gamma hN R hR
  intro x y hxy
  let u : Fin (Gamma.card + 1) → ℤ := fun i => Q.coeff x i - Q.coeff y i
  let v := bohrCertificateCombination Gamma hN R hR u
  have hu (i : Fin (Gamma.card + 1)) :
      |u i| ≤ (2 * bohrProgressionRadius Gamma hN R hR i : ℕ) := by
    exact CyclicCenteredGAP.coeff_sub_abs_le_two_mul Q x y i
  have hv0cast : (v 0 : ZMod N) = 0 := by
    have hx := eval_bohrCyclicProgression Gamma hN R hR x
    have hy := eval_bohrCyclicProgression Gamma hN R hR y
    have hvsub : (v 0 : ZMod N) =
        (bohrCyclicProgression Gamma hN R hR).eval x -
          (bohrCyclicProgression Gamma hN R hR).eval y := by
      rw [hx, hy]
      simp only [v, u, bohrCertificateCombination, Int.cast_sum, Int.cast_mul,
        Int.cast_sub]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hvsub, hxy, sub_self]
  have hvcast (j : Fin (Gamma.card + 1)) : (v j : ZMod N) = 0 := by
    rw [bohrCertificateCombination_cast_coordinate Gamma hN R hR u j,
      hv0cast, zero_mul]
  have hvabs (j : Fin (Gamma.card + 1)) : |(v j : ℝ)| ≤ R / 2 := by
    convert abs_intCast_bohrCertificateCombination_le Gamma hN R hR 2 u hu j
      using 1; norm_num; ring
  have hvzero : v = 0 := by
    funext j
    apply int_eq_zero_of_cast_zmod_eq_zero_of_abs_lt (hvcast j)
    exact (hvabs j).trans_lt (by linarith)
  have hsum : ∑ i, (u i : ℝ) •
      intCastVec (bohrCertificatePoint Gamma hN R hR i) = 0 := by
    funext j
    have hj := congrFun hvzero j
    have hjR : (v j : ℝ) = 0 := by exact_mod_cast hj
    simpa [v, bohrCertificateCombination, intCastVec] using hjR
  have huR : ∀ i, (u i : ℝ) = 0 :=
    (Fintype.linearIndependent_iff.mp
      (bohrCertificatePoint_independent Gamma hN R hR)) _ hsum
  have hu0 : u = 0 := by
    funext i
    change u i = 0
    exact_mod_cast huR i
  funext i
  apply Fin.ext
  have hi0 : u i = 0 := by
    change u i = (0 : Fin (Gamma.card + 1) → ℤ) i
    exact congrFun hu0 i
  have hi : (x i : ℤ) = (y i : ℤ) := by
    dsimp only [u, Q] at hi0
    simp only [CyclicCenteredGAP.coeff] at hi0
    omega
  exact_mod_cast hi

theorem bohrCyclicProgression_carrier_subset {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : 4 * R ≤ N) :
    (bohrCyclicProgression Gamma hN R hR).carrier ⊆
      cyclicBohrSet Gamma (1 / 2) := by
  intro z hz
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hz
  rw [mem_cyclicBohrSet]
  intro k hk
  let i : Fin Gamma.card := Gamma.equivFin ⟨k, hk⟩
  let u : Fin (Gamma.card + 1) → ℤ :=
    (bohrCyclicProgression Gamma hN R hR).coeff x
  let v := bohrCertificateCombination Gamma hN R hR u
  have hu (j : Fin (Gamma.card + 1)) :
      |u j| ≤ (bohrProgressionRadius Gamma hN R hR j : ℕ) := by
    exact CyclicCenteredGAP.coeff_abs_le
      (bohrCyclicProgression Gamma hN R hR) x j
  have heval : (bohrCyclicProgression Gamma hN R hR).eval x =
      (v 0 : ZMod N) := eval_bohrCyclicProgression Gamma hN R hR x
  have hchar : indexedCyclicCharacter Gamma i.succ = k := by
    change ((Gamma.equivFin.symm i : Gamma) : ZMod N) = k
    simp [i]
  have hvchar : (v i.succ : ZMod N) =
      (bohrCyclicProgression Gamma hN R hR).eval x * k := by
    rw [bohrCertificateCombination_cast_coordinate Gamma hN R hR u i.succ,
      hchar, heval]
  rw [← hvchar]
  apply stdAddChar_intCast_close
  have hvabs : |(v i.succ : ℝ)| ≤ R / 4 := by
    simpa using
      abs_intCast_bohrCertificateCombination_le Gamma hN R hR 1 u
        (by simpa using hu) i.succ
  have habs : (v i.succ).natAbs = |(v i.succ : ℝ)| := by
    calc
      ((v i.succ).natAbs : ℝ) =
          ((((v i.succ).natAbs : ℕ) : ℤ) : ℝ) := by norm_num
      _ = ((|v i.succ| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(v i.succ : ℝ)| := Int.cast_abs
  have hreal : (16 : ℝ) * (v i.succ).natAbs ≤ N := by
    rw [habs]
    nlinarith
  exact_mod_cast hreal

/- ## Quantitative size of the progression -/

lemma matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    Matrix.of (bohrLatticeBasis Gamma hN) =
      (bohrLatticeMatrix Gamma)ᵀ := by
  ext i j
  rw [Matrix.of_apply, Matrix.transpose_apply]
  exact bohrLatticeBasis_apply Gamma hN i j

lemma abs_det_matrixOf_bohrLatticeBasis {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) :
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| =
      (N : ℝ) ^ Gamma.card := by
  rw [matrixOf_bohrLatticeBasis Gamma hN,
    Matrix.det_transpose, det_bohrLatticeMatrix Gamma hN, abs_of_nonneg]
  positivity

lemma inv_scale_le_two_mul_bohrProgressionRadius_add_one
    {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (i : Fin (Gamma.card + 1)) :
    (((4 * (Gamma.card + 1) : ℝ) *
        (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) ≤
      2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 := by
  have hlt := Nat.lt_floor_add_one
    (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹)
  change (((4 * (Gamma.card + 1) : ℝ) *
      (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹) <
    (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1 at hlt
  have hradius : 0 ≤ (bohrProgressionRadius Gamma hN R hR i : ℝ) := by
    positivity
  linarith

theorem bohrCyclicProgression_card_lower_bound {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hN : 1 < N) (R : ℝ) (hR : 0 < R)
    (hsmall : R < 2 * N) :
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) ≤
      ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
  let c : ℝ := 4 * (Gamma.card + 1)
  let B : ℝ := minkowskiSecondConstant (Gamma.card + 1) *
    |(Matrix.of (bohrLatticeBasis Gamma hN)).det| *
      (∏ _i : Fin (Gamma.card + 1), R)⁻¹
  have hc : 0 < c := by positivity
  have hscale (i : Fin (Gamma.card + 1)) :
      0 < (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact bohrCertificate_scale_pos Gamma hN R hR i
  have hprodscale : 0 <
      ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i := by
    exact Finset.prod_pos fun i _ => hscale i
  have hB : 0 < B := by
    simp only [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    unfold minkowskiSecondConstant
    positivity
  have hcertificate :
      (∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i) ≤ B := by
    exact (bohrSuccessiveCertificate Gamma hN R hR).product_le
  have hreciprocal : (c ^ (Gamma.card + 1) * B)⁻¹ ≤
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
    apply (inv_le_inv₀ (mul_pos (pow_pos hc _) hB)
      (mul_pos (pow_pos hc _) hprodscale)).2
    exact mul_le_mul_of_nonneg_left hcertificate (pow_nonneg hc.le _)
  have hproduct :
      (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ ≤
      ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
    calc
      (c ^ (Gamma.card + 1) *
          ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ =
          (∏ i : Fin (Gamma.card + 1),
            c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            congr 1
            rw [Finset.prod_mul_distrib]
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∏ i : Fin (Gamma.card + 1),
          (c * (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ := by
            rw [Finset.prod_inv_distrib]
      _ ≤ ∏ i : Fin (Gamma.card + 1),
          (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := by
            apply Finset.prod_le_prod
            · intro i hi
              exact inv_nonneg.mpr (mul_nonneg hc.le
                ((bohrSuccessiveCertificate Gamma hN R hR).scale_nonneg i))
            · intro i hi
              simpa [c] using
                inv_scale_le_two_mul_bohrProgressionRadius_add_one
                  Gamma hN R hR i
  have hcard := CyclicCenteredGAP.card_carrier_of_proper
    (bohrCyclicProgression Gamma hN R hR)
    (bohrCyclicProgression_proper Gamma hN R hR hsmall)
  have hBform : B = minkowskiSecondConstant (Gamma.card + 1) *
      (N : ℝ) ^ Gamma.card * (R ^ (Gamma.card + 1))⁻¹ := by
    simp [B, abs_det_matrixOf_bohrLatticeBasis Gamma hN,
      Finset.prod_const]
  calc
    ((((4 * (Gamma.card + 1) : ℝ) ^ (Gamma.card + 1)) *
        (minkowskiSecondConstant (Gamma.card + 1) *
          (N : ℝ) ^ Gamma.card *
            (R ^ (Gamma.card + 1))⁻¹))⁻¹) =
        (c ^ (Gamma.card + 1) * B)⁻¹ := by
      rw [hBform]
    _ ≤ (c ^ (Gamma.card + 1) *
        ∏ i, (bohrSuccessiveCertificate Gamma hN R hR).scale i)⁻¹ :=
      hreciprocal
    _ ≤ ∏ i : Fin (Gamma.card + 1),
        (2 * (bohrProgressionRadius Gamma hN R hR i : ℝ) + 1) := hproduct
    _ = ((bohrCyclicProgression Gamma hN R hR).carrier.card : ℝ) := by
      rw [hcard]
      norm_cast

/- ## The Nguyen--Vu cyclic progression furnished by Bogolyubov -/

noncomputable def bohrProgressionLowerBound (N d : ℕ) (R : ℝ) : ℝ :=
  (((4 * (d + 1) : ℝ) ^ (d + 1)) *
    (minkowskiSecondConstant (d + 1) * (N : ℝ) ^ d *
      (R ^ (d + 1))⁻¹))⁻¹

/-- The dimension-only denominator obtained by taking the Bohr radius to be
one quarter of the ambient cyclic modulus. -/
noncomputable def bohrQuarterDenominator (d : ℕ) : ℝ :=
  (4 * (d + 1) : ℝ) ^ (d + 1) *
    minkowskiSecondConstant (d + 1) * 4 ^ (d + 1)

lemma bohrQuarterDenominator_pos (d : ℕ) :
    0 < bohrQuarterDenominator d := by
  unfold bohrQuarterDenominator minkowskiSecondConstant
  positivity

lemma bohrProgressionLowerBound_quarter (N d : ℕ) (hN : 0 < N) :
    bohrProgressionLowerBound N d ((N : ℝ) / 4) =
      (N : ℝ) / bohrQuarterDenominator d := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold bohrProgressionLowerBound bohrQuarterDenominator
  rw [div_pow]
  field_simp
  ring

theorem exists_proper_cyclicProgression_in_fourfoldDifference
    {N : ℕ} [NeZero N] (hN : 1 < N)
    (q : ℕ) (hq : 1 ≤ q) (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hdense : N ≤ q * A.card) (R : ℝ) (hR : 0 < R)
    (hsmall : 4 * R ≤ N) :
    ∃ Q : CyclicCenteredGAP N,
      Q.rank ≤ 16 * q ^ 3 + 1 ∧
      Q.Proper ∧
      Q.carrier ⊆ 2 • A - 2 • A ∧
      bohrProgressionLowerBound N
          (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))).card R ≤
        (Q.carrier.card : ℝ) := by
  let Gamma := cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))
  let Q := bohrCyclicProgression Gamma hN R hR
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hproperSmall : R < 2 * N := by
    nlinarith
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · change Gamma.card + 1 ≤ 16 * q ^ 3 + 1
    exact Nat.add_le_add_right
      (card_largeSpectrum_le_of_density q hq A hA hdense) 1
  · exact bohrCyclicProgression_proper Gamma hN R hR hproperSmall
  · exact (bohrCyclicProgression_carrier_subset Gamma hN R hR hsmall).trans
      (cyclicBohrSet_subset_fourfoldDifference q hq A hA hdense)
  · simpa only [bohrProgressionLowerBound, Gamma, Q] using
      bohrCyclicProgression_card_lower_bound Gamma hN R hR hproperSmall

end

end Erdos587

end Erdos587_BohrProgression

section Erdos587_FreimanModel

open scoped BigOperators Pointwise

namespace Erdos587

def badMultipliers (q M : ℕ) [NeZero q] (x : ℤ) : Finset (ZMod q) :=
  Finset.univ.filter fun lam => M ∣ (lam * (x : ZMod q)).val

@[simp] lemma mem_badMultipliers {q M : ℕ} [NeZero q] {x : ℤ} {lam : ZMod q} :
    lam ∈ badMultipliers q M x ↔ M ∣ (lam * (x : ZMod q)).val := by
  simp [badMultipliers]

lemma card_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (_hM : 0 < M) {x : ℤ} (hx : (x : ZMod q) ≠ 0) :
    (badMultipliers q M x).card ≤ q / M + 1 := by
  let f : ZMod q → ℕ := fun lam => (lam * (x : ZMod q)).val / M
  rw [← Finset.card_range (q / M + 1)]
  apply Finset.card_le_card_of_injOn f
      (s := badMultipliers q M x) (t := Finset.range (q / M + 1))
  · intro lam hlam
    dsimp only [f]
    have hval := (lam * (x : ZMod q)).val_lt
    have hdiv : (lam * (x : ZMod q)).val / M ≤ q / M :=
      Nat.div_le_div_right hval.le
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.succ_eq_add_one] using
      Nat.lt_succ_of_le hdiv
  · intro lam hlam mu hmu heq
    have hlamDiv : M ∣ (lam * (x : ZMod q)).val :=
      mem_badMultipliers.mp hlam
    have hmuDiv : M ∣ (mu * (x : ZMod q)).val :=
      mem_badMultipliers.mp hmu
    dsimp only [f] at heq
    have hval : (lam * (x : ZMod q)).val = (mu * (x : ZMod q)).val := by
      calc
        (lam * (x : ZMod q)).val =
            M * ((lam * (x : ZMod q)).val / M) :=
              (Nat.mul_div_cancel' hlamDiv).symm
        _ = M * ((mu * (x : ZMod q)).val / M) := by rw [heq]
        _ = (mu * (x : ZMod q)).val := Nat.mul_div_cancel' hmuDiv
    have hprod : lam * (x : ZMod q) = mu * (x : ZMod q) := by
      rw [← ZMod.natCast_zmod_val (lam * (x : ZMod q)),
        ← ZMod.natCast_zmod_val (mu * (x : ZMod q)), hval]
    exact mul_right_cancel₀ hx hprod

lemma intCast_zmod_ne_zero_of_natAbs_lt {q : ℕ} [NeZero q]
    {x : ℤ} (hx0 : x ≠ 0) (hxq : x.natAbs < q) :
    (x : ZMod q) ≠ 0 := by
  intro hx
  have hdiv : (q : ℤ) ∣ x :=
    (CharP.intCast_eq_zero_iff (ZMod q) q x).mp hx
  have hqle : q ≤ x.natAbs := by
    exact_mod_cast Int.natAbs_le_of_dvd_ne_zero hdiv hx0
  omega

lemma card_biUnion_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (hM : 0 < M) {D : Finset ℤ}
    (hx : ∀ x ∈ D, (x : ZMod q) ≠ 0) :
    (D.biUnion (badMultipliers q M)).card ≤ D.card * (q / M + 1) := by
  calc
    (D.biUnion (badMultipliers q M)).card ≤
        ∑ x ∈ D, (badMultipliers q M x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ D, (q / M + 1) := by
      gcongr with x hxD
      exact card_badMultipliers_le hM (hx x hxD)
    _ = D.card * (q / M + 1) := by simp

lemma multiplier_union_card_lt {N q : ℕ} (hN : 0 < N)
    (hq : 4 * N < q) :
    N * (q / (2 * N) + 1) < q := by
  have hden : 0 < 2 * N := by omega
  have hdiv := Nat.mul_div_le q (2 * N)
  have hmul : 2 * (N * (q / (2 * N))) ≤ q := by
    calc
      2 * (N * (q / (2 * N))) = (2 * N) * (q / (2 * N)) := by ring
      _ ≤ q := hdiv
  nlinarith

theorem exists_good_multiplier {D : Finset ℤ} {N q : ℕ}
    [NeZero q] [Fact q.Prime] (hN : 0 < N) (hcard : D.card ≤ N)
    (habs : ∀ x ∈ D, x.natAbs < q) (hq : 4 * N < q) :
    ∃ lam : ZMod q, lam ≠ 0 ∧
      ∀ x ∈ D, x ≠ 0 → ¬ (2 * N ∣ (lam * (x : ZMod q)).val) := by
  classical
  let D₀ := D.erase 0
  by_cases hD₀ : D₀.Nonempty
  · let U : Finset (ZMod q) := D₀.biUnion (badMultipliers q (2 * N))
    have hxcast : ∀ x ∈ D₀, (x : ZMod q) ≠ 0 := by
      intro x hxD
      have hxD' := Finset.mem_erase.mp hxD
      exact intCast_zmod_ne_zero_of_natAbs_lt hxD'.1 (habs x hxD'.2)
    have hUcard : U.card < q := by
      calc
        U.card ≤ D₀.card * (q / (2 * N) + 1) :=
          card_biUnion_badMultipliers_le (by omega) hxcast
        _ ≤ N * (q / (2 * N) + 1) := by
          gcongr
          exact Finset.card_erase_le.trans hcard
        _ < q := multiplier_union_card_lt hN hq
    have hUne : U ≠ Finset.univ := by
      intro hEq
      have : U.card = q := by simp [hEq]
      omega
    have hex : ∃ lam : ZMod q, lam ∉ U := by
      by_contra h
      push Not at h
      apply hUne
      ext lam
      simp [h lam]
    obtain ⟨lam, hlamU⟩ := hex
    refine ⟨lam, ?_, ?_⟩
    · intro hlam0
      have hxU : (0 : ZMod q) ∈ U := by
        obtain ⟨x, hxD₀⟩ := hD₀
        apply Finset.mem_biUnion.mpr
        refine ⟨x, hxD₀, ?_⟩
        simp
      exact hlamU (by simpa [hlam0] using hxU)
    · intro x hxD hx0 hbad
      apply hlamU
      apply Finset.mem_biUnion.mpr
      exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩,
        mem_badMultipliers.mpr hbad⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    intro x hxD hx0
    exfalso
    apply hD₀
    exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩⟩

lemma multiset_sum_mem_nsmul (A : Finset ℤ) {T : Multiset ℤ}
    (hT : ∀ x ∈ T, x ∈ A) : T.sum ∈ T.card • A := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons a T ih =>
      rw [Multiset.card_cons, succ_nsmul, Finset.mem_add]
      refine ⟨T.sum, ih ?_, a, hT a (by simp), ?_⟩
      · intro x hx
        exact hT x (by simp [hx])
      · simp [add_comm]

def ruzsaRepresentative (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  (lam * (a : ZMod q)).val

def ruzsaColor (q s : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  ruzsaRepresentative q lam a / (q / (2 * s) + 1)

def ruzsaModelMap (q M : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ZMod M :=
  ruzsaRepresentative q lam a

lemma ruzsaRepresentative_lt (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    ruzsaRepresentative q lam a < q := by
  exact (lam * (a : ZMod q)).val_lt

lemma ruzsaRepresentative_cast (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    (ruzsaRepresentative q lam a : ZMod q) = lam * (a : ZMod q) := by
  exact ZMod.natCast_zmod_val _

lemma ruzsaColor_lt {q s : ℕ} [NeZero q] (lam : ZMod q)
    (hs : 0 < s) (_hq : 2 * s < q) (a : ℤ) :
    ruzsaColor q s lam a < 2 * s := by
  let L := q / (2 * s) + 1
  have hden : 0 < 2 * s := by omega
  have hqL : q < (2 * s) * L := by
    simp only [L]
    exact Nat.lt_mul_div_succ q hden
  have hrep : ruzsaRepresentative q lam a < q := ruzsaRepresentative_lt q lam a
  dsimp [ruzsaColor]
  rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
  simpa only [L] using hrep.trans hqL

lemma ruzsaRepresentative_bounds_of_color_eq {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {a : ℤ} (hcolor : ruzsaColor q s lam a = c) :
    c * (q / (2 * s) + 1) ≤ ruzsaRepresentative q lam a ∧
      ruzsaRepresentative q lam a < (c + 1) * (q / (2 * s) + 1) := by
  have hL : 0 < q / (2 * s) + 1 := Nat.succ_pos _
  have hdiv : ruzsaRepresentative q lam a / (q / (2 * s) + 1) = c := by
    simpa [ruzsaColor] using hcolor
  constructor
  · rw [← hdiv]
    simpa [mul_comm] using Nat.div_mul_le_self
      (ruzsaRepresentative q lam a) (q / (2 * s) + 1)
  · rw [← hdiv]
    simpa [mul_comm] using Nat.lt_mul_div_succ (ruzsaRepresentative q lam a) hL

def ruzsaRepresentativeSum (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) : ℕ :=
  (T.map (ruzsaRepresentative q lam)).sum

lemma ruzsaRepresentativeSum_bounds {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T : Multiset ℤ} (hcard : T.card = s) (hs : 0 < s)
    (hcolor : ∀ x ∈ T, ruzsaColor q s lam x = c) :
    s * (c * (q / (2 * s) + 1)) ≤ ruzsaRepresentativeSum q lam T ∧
      ruzsaRepresentativeSum q lam T < s * ((c + 1) * (q / (2 * s) + 1)) := by
  let L := q / (2 * s) + 1
  have hlo : T.card • (c * L) ≤ ruzsaRepresentativeSum q lam T := by
    have hlo' := Multiset.card_nsmul_le_sum
      (s := T.map (ruzsaRepresentative q lam)) (a := c * L) (by
        intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨x, hxT, rfl⟩ := hy
        simpa only [L] using
          (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).1)
    simpa only [ruzsaRepresentativeSum, Multiset.card_map] using hlo'
  have hTne : T ≠ 0 := by
    intro hT
    simp [hT] at hcard
    omega
  have hhi : ruzsaRepresentativeSum q lam T < T.card • ((c + 1) * L) := by
    have hhi' := Multiset.sum_lt_sum_of_nonempty hTne fun x hxT =>
      (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).2
    simpa only [ruzsaRepresentativeSum, Multiset.map_const',
      Multiset.sum_replicate, L] using hhi'
  simpa only [hcard, L, Nat.nsmul_eq_mul] using And.intro hlo hhi

lemma ruzsaRepresentativeSum_sub_abs_lt {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T U : Multiset ℤ}
    (hTcard : T.card = s) (hUcard : U.card = s) (hs : 0 < s)
    (hTcolor : ∀ x ∈ T, ruzsaColor q s lam x = c)
    (hUcolor : ∀ x ∈ U, ruzsaColor q s lam x = c) :
    (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U <
        s * (q / (2 * s) + 1) ∧
      -((s * (q / (2 * s) + 1) : ℕ) : ℤ) <
        (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U := by
  obtain ⟨hTlo, hThi⟩ :=
    ruzsaRepresentativeSum_bounds lam hTcard hs hTcolor
  obtain ⟨hUlo, hUhi⟩ :=
    ruzsaRepresentativeSum_bounds lam hUcard hs hUcolor
  have hTU : ruzsaRepresentativeSum q lam T <
      ruzsaRepresentativeSum q lam U + s * (q / (2 * s) + 1) := by
    nlinarith
  have hUT : ruzsaRepresentativeSum q lam U <
      ruzsaRepresentativeSum q lam T + s * (q / (2 * s) + 1) := by
    nlinarith
  have hTU' : (ruzsaRepresentativeSum q lam T : ℤ) <
      (ruzsaRepresentativeSum q lam U : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hTU
  have hUT' : (ruzsaRepresentativeSum q lam U : ℤ) <
      (ruzsaRepresentativeSum q lam T : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hUT
  constructor <;> omega

lemma ruzsaRepresentativeSum_cast (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) :
    (ruzsaRepresentativeSum q lam T : ZMod q) = lam * (T.sum : ZMod q) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      rw [show ruzsaRepresentativeSum q lam (a ::ₘ T) =
        ruzsaRepresentative q lam a + ruzsaRepresentativeSum q lam T by
          simp [ruzsaRepresentativeSum]]
      rw [Nat.cast_add, ruzsaRepresentative_cast, ih, Multiset.sum_cons,
        Int.cast_add]
      ring

lemma ruzsaModelMap_sum (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
      (ruzsaRepresentativeSum q lam T : ZMod M) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      simp only [ruzsaModelMap, ruzsaRepresentativeSum, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add, ih]

lemma ruzsaBlockWidth_lt {q s : ℕ} (_hs : 0 < s) (hq : 2 * s < q) :
    s * (q / (2 * s) + 1) < q := by
  have hdiv := Nat.mul_div_le q (2 * s)
  have hhalf : 2 * (s * (q / (2 * s))) ≤ q := by
    simpa only [mul_assoc] using hdiv
  nlinarith

lemma ruzsaRepresentativeSum_sub_cast (q : ℕ) [NeZero q]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q) =
      lam * ((T.sum - U.sum : ℤ) : ZMod q) := by
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    ruzsaRepresentativeSum_cast, ruzsaRepresentativeSum_cast, Int.cast_sub]
  ring

lemma ruzsaModelMap_sum_eq_iff_dvd (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔
      (M : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) := by
  rw [ruzsaModelMap_sum, ruzsaModelMap_sum]
  constructor
  · intro h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  · intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr h
    simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using hz

lemma zmod_val_eq_natAbs_of_nonneg {q : ℕ} [NeZero q]
    {y : ℤ} {z : ZMod q} (hy : 0 ≤ y) (hyq : y.natAbs < q)
    (hcast : (y : ZMod q) = z) : z.val = y.natAbs := by
  have hycoe : (y.natAbs : ℤ) = y := Int.natAbs_of_nonneg hy
  have hcastNat : (y.natAbs : ZMod q) = z := by
    rw [← hcast]
    simpa using congrArg (fun t : ℤ => (t : ZMod q)) hycoe
  rw [← hcastNat, ZMod.val_natCast_of_lt hyq]

lemma int_natAbs_lt_of_neg_lt_and_lt {y : ℤ} {B : ℕ}
    (hlo : -(B : ℤ) < y) (hhi : y < B) : y.natAbs < B := by
  by_cases hy : 0 ≤ y
  · have hcast : (y.natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hy]
      exact hhi
    exact_mod_cast hcast
  · have hyneg : 0 ≤ -y := by omega
    have hcast : ((-y).natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hyneg]
      omega
    rw [Int.natAbs_neg] at hcast
    exact_mod_cast hcast

lemma ruzsaModelMap_multiset_sum_eq_iff
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val))
    {T U : Multiset ℤ}
    (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
    (hTcard : T.card = s) (hUcard : U.card = s) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔ T.sum = U.sum := by
  have hTsum : T.sum ∈ s • A := by
    simpa only [hTcard] using multiset_sum_mem_nsmul A hTA
  have hUsum : U.sum ∈ s • A := by
    simpa only [hUcard] using multiset_sum_mem_nsmul A hUA
  have hTUmem : T.sum - U.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨T.sum, hTsum, U.sum, hUsum, rfl⟩
  have hUTmem : U.sum - T.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨U.sum, hUsum, T.sum, hTsum, rfl⟩
  have hshort := ruzsaRepresentativeSum_sub_abs_lt lam hTcard hUcard hs
    (fun x hx => hmono x (hTA x hx)) (fun x hx => hmono x (hUA x hx))
  have hwidth := ruzsaBlockWidth_lt hs hq
  have hsmall :
      (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs < q := by
    have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
      exact_mod_cast hwidth
    apply int_natAbs_lt_of_neg_lt_and_lt
    · exact (by omega : -(q : ℤ) <
        -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hshort.2
    · exact hshort.1.trans hwidthZ
  constructor
  · intro hmap
    by_contra hsum
    have hx : T.sum - U.sum ≠ 0 := sub_ne_zero.mpr hsum
    by_cases hy : 0 ≤ (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U
    · have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam T U).mp hmap
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((T.sum - U.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hy hsmall
        exact ruzsaRepresentativeSum_sub_cast q lam T U
      exact hgood (T.sum - U.sum) hTUmem hx (by rwa [hval])
    · have hswapNonneg : 0 ≤ (ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T := by omega
      have hswapShort := ruzsaRepresentativeSum_sub_abs_lt lam hUcard hTcard hs
        (fun x hx => hmono x (hUA x hx)) (fun x hx => hmono x (hTA x hx))
      have hswapSmall :
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs < q := by
        have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
          exact_mod_cast hwidth
        apply int_natAbs_lt_of_neg_lt_and_lt
        · exact (by omega : -(q : ℤ) <
            -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hswapShort.2
        · exact hswapShort.1.trans hwidthZ
      have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam U T).mp hmap.symm
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((U.sum - T.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hswapNonneg hswapSmall
        exact ruzsaRepresentativeSum_sub_cast q lam U T
      have hx' : U.sum - T.sum ≠ 0 := sub_ne_zero.mpr (Ne.symm hsum)
      exact hgood (U.sum - T.sum) hUTmem hx' (by rwa [hval])
  · intro hsum
    have hcast : ((((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q)) = 0 := by
      rw [ruzsaRepresentativeSum_sub_cast, hsum, sub_self, Int.cast_zero, mul_zero]
    have hdiv : (q : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcast
    have hzero : (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
      simpa only [Int.natAbs_natCast] using hsmall
    have hrepeq : ruzsaRepresentativeSum q lam T =
        ruzsaRepresentativeSum q lam U := by omega
    rw [ruzsaModelMap_sum, ruzsaModelMap_sum, hrepeq]

theorem isAddFreimanIso_ruzsaModelMap
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val)) :
    IsAddFreimanIso s (A : Set ℤ)
      (A.image (ruzsaModelMap q M lam) : Set (ZMod M))
      (ruzsaModelMap q M lam) := by
  let f := ruzsaModelMap q M lam
  have hrel {T U : Multiset ℤ}
      (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
      (hTcard : T.card = s) (hUcard : U.card = s) :
      (T.map f).sum = (U.map f).sum ↔ T.sum = U.sum :=
    ruzsaModelMap_multiset_sum_eq_iff lam hs hq hmono hgood
      hTA hUA hTcard hUcard
  have hinj : Set.InjOn f (A : Set ℤ) := by
    intro a ha b hb hab
    have hrepl := hrel
      (T := Multiset.replicate s a) (U := Multiset.replicate s b)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using hb)
      (by simp) (by simp)
    have hsum := hrepl.mp (by simp [f, hab])
    simp only [Multiset.sum_replicate, nsmul_eq_mul] at hsum
    have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
    nlinarith
  refine ⟨⟨?_, hinj, ?_⟩, ?_⟩
  · intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩)
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, Finset.mem_coe.mpr ha, rfl⟩
  · intro T U hTA hUA hTcard hUcard
    apply hrel
    · intro x hx
      exact Finset.mem_coe.mp (hTA hx)
    · intro x hx
      exact Finset.mem_coe.mp (hUA hx)
    · exact hTcard
    · exact hUcard

/-- A multiplicative form of the same pigeonhole estimate.  This formulation
has no floor-error term and is the one needed to transfer density to the
cyclic Freiman model. -/
lemma exists_nonempty_large_color_fiber_mul {A : Finset ℤ} {k : ℕ}
    (hA : A.Nonempty) (hk : 0 < k) (f : ℤ → ℕ)
    (hf : ∀ a ∈ A, f a < k) :
    ∃ c < k, let B := A.filter fun a => f a = c
      B.Nonempty ∧ A.card ≤ k * B.card := by
  classical
  let n := (A.card - 1) / k
  have hApos : 0 < A.card := Finset.card_pos.mpr hA
  have hkn : k * n < A.card := by
    have hle : k * n ≤ A.card - 1 := by
      simpa only [n] using Nat.mul_div_le (A.card - 1) k
    omega
  obtain ⟨c, hc, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A) (t := Finset.range k) (f := f)
      (fun a ha => Finset.mem_range.mpr (hf a ha)) (by simpa using hkn)
  refine ⟨c, Finset.mem_range.mp hc, ?_⟩
  dsimp
  have hceil : A.card - 1 < k * (n + 1) := by
    simpa only [n] using Nat.lt_mul_div_succ (A.card - 1) hk
  have hmul : k * (n + 1) ≤
      k * (A.filter fun a => f a = c).card := by
    exact Nat.mul_le_mul_left k (by omega)
  constructor
  · exact Finset.card_pos.mp ((Nat.zero_le n).trans_lt hcard)
  · have hpred : A.card - 1 + 1 = A.card :=
      Nat.sub_one_add_one hApos.ne'
    have hlt : A.card - 1 <
        k * (A.filter fun a => f a = c).card := hceil.trans_le hmul
    omega

theorem exists_large_cyclic_freiman_model (A : Finset ℤ) (s : ℕ)
    (hA : A.Nonempty) (hs : 0 < s) :
    let D := s • A - s • A
    ∃ (A' : Finset ℤ) (B : Finset (ZMod (2 * D.card)))
      (f : ℤ → ZMod (2 * D.card)),
      A'.Nonempty ∧ A' ⊆ A ∧ A.card ≤ (2 * s) * A'.card ∧
        B = A'.image f ∧ IsAddFreimanIso s (A' : Set ℤ) (B : Set _) f := by
  classical
  let D := s • A - s • A
  have hD : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate s a).sum ∈ s • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate s a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hDcard : 0 < D.card := Finset.card_pos.mpr hD
  let R := D.sup Int.natAbs
  let K := max (max (4 * D.card) (2 * s)) R + 1
  obtain ⟨q, hKq, hqPrime⟩ := Nat.exists_infinite_primes K
  have h4q : 4 * D.card < q := by
    dsimp [K] at hKq
    omega
  have h2sq : 2 * s < q := by
    dsimp [K] at hKq
    omega
  have hRq : R < q := by
    dsimp [K] at hKq
    omega
  let : Fact q.Prime := ⟨hqPrime⟩
  let : NeZero q := ⟨hqPrime.ne_zero⟩
  obtain ⟨lam, hlam, hgood⟩ := exists_good_multiplier
    (D := D) (N := D.card) (q := q) hDcard le_rfl
    (fun x hx => (Finset.le_sup hx).trans_lt hRq) h4q
  obtain ⟨c, hc, hfiber⟩ :=
    exists_nonempty_large_color_fiber_mul hA (by omega)
      (ruzsaColor q s lam) (fun a _ha => ruzsaColor_lt lam hs h2sq a)
  let A' := A.filter fun a => ruzsaColor q s lam a = c
  have hA'ne : A'.Nonempty := hfiber.1
  have hA'card : A.card ≤ (2 * s) * A'.card := hfiber.2
  have hA'sub : A' ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hmono : ∀ a ∈ A', ruzsaColor q s lam a = c := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hsumSub : s • A' ⊆ s • A := by
    exact nsmul_le_nsmul_right hA'sub s
  have hdiffSub : s • A' - s • A' ⊆ D := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨u, hsumSub hu, v, hsumSub hv, rfl⟩
  have hgood' : ∀ x ∈ s • A' - s • A', x ≠ 0 →
      ¬ (2 * D.card ∣ (lam * (x : ZMod q)).val) := by
    intro x hx hx0
    exact hgood x (hdiffSub hx) hx0
  have hM : 0 < 2 * D.card := by omega
  let : NeZero (2 * D.card) := ⟨hM.ne'⟩
  let f : ℤ → ZMod (2 * D.card) := ruzsaModelMap q (2 * D.card) lam
  let B := A'.image f
  refine ⟨A', B, f, hA'ne, hA'sub, hA'card, rfl, ?_⟩
  exact isAddFreimanIso_ruzsaModelMap lam hs h2sq hmono hgood'

end Erdos587

end Erdos587_FreimanModel

section Erdos587_FreimanLift

open scoped BigOperators Pointwise

namespace Erdos587

noncomputable section

/-
## Extending an order-eight Freiman isomorphism to `2B - 2B`

A point of `2B - 2B` is represented by four elements of `B`.  The inverse
Freiman map is applied to the four entries.  Order four proves that the
result is independent of the chosen presentation; order eight proves the
order-two Freiman relation on the whole fourfold difference set.
-/

structure FourfoldPresentation (β : Type*) where
  pos₁ : β
  pos₂ : β
  neg₁ : β
  neg₂ : β

namespace FourfoldPresentation

variable {β : Type*} [AddCommGroup β]

def eval (p : FourfoldPresentation β) : β :=
  p.pos₁ + p.pos₂ - p.neg₁ - p.neg₂

def Mem (B : Finset β) (p : FourfoldPresentation β) : Prop :=
  p.pos₁ ∈ B ∧ p.pos₂ ∈ B ∧ p.neg₁ ∈ B ∧ p.neg₂ ∈ B

end FourfoldPresentation

variable {α β : Type*} [AddCommGroup α] [AddCommGroup β]
  [DecidableEq β]

lemma mem_two_nsmul_sub_two_nsmul_iff
    {B : Finset β} {x : β} :
    x ∈ 2 • B - 2 • B ↔
      ∃ p : FourfoldPresentation β,
        p.Mem B ∧ p.eval = x := by
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hx
    rw [show 2 • B = B + B by simp [two_nsmul]] at hu hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hu
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hv
    refine ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd⟩, ?_⟩
    dsimp only [FourfoldPresentation.eval]
    rw [← huv, ← hab, ← hcd]
    abel
  · rintro ⟨p, hp, rfl⟩
    apply Finset.mem_sub.mpr
    refine ⟨p.pos₁ + p.pos₂, ?_, p.neg₁ + p.neg₂, ?_, ?_⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.pos₁, hp.1, p.pos₂, hp.2.1, rfl⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.neg₁, hp.2.2.1, p.neg₂, hp.2.2.2, rfl⟩
    · dsimp only [FourfoldPresentation.eval]
      abel

noncomputable def defaultFourfoldPresentation (B : Finset β)
    (hB : B.Nonempty) : FourfoldPresentation β :=
  let b := Classical.choose hB
  ⟨b, b, b, b⟩

noncomputable def selectedFourfoldPresentation (B : Finset β)
    (hB : B.Nonempty) (x : β) : FourfoldPresentation β := by
  classical
  exact if hx : ∃ p : FourfoldPresentation β, p.Mem B ∧ p.eval = x then
      Classical.choose hx
    else defaultFourfoldPresentation B hB

lemma selectedFourfoldPresentation_spec (B : Finset β)
    (hB : B.Nonempty) {x : β} (hx : x ∈ 2 • B - 2 • B) :
    (selectedFourfoldPresentation B hB x).Mem B ∧
      (selectedFourfoldPresentation B hB x).eval = x := by
  have hex := mem_two_nsmul_sub_two_nsmul_iff.mp hx
  simp only [selectedFourfoldPresentation, dif_pos hex]
  exact Classical.choose_spec hex

def fourfoldMapValue (g : β → α) (p : FourfoldPresentation β) : α :=
  g p.pos₁ + g p.pos₂ - g p.neg₁ - g p.neg₂

lemma fourfold_sub_eq_iff_cross_add {G : Type*} [AddCommGroup G]
    (a b c d e f g h : G) :
    a + b - c - d = e + f - g - h ↔
      a + b + g + h = e + f + c + d := by
  constructor
  · intro heq
    calc
      a + b + g + h = (a + b - c - d) + (c + d + g + h) := by abel
      _ = (e + f - g - h) + (c + d + g + h) := by rw [heq]
      _ = e + f + c + d := by abel
  · intro heq
    calc
      a + b - c - d =
          (a + b + g + h) - (c + d + g + h) := by abel
      _ = (e + f + c + d) - (c + d + g + h) := by rw [heq]
      _ = e + f - g - h := by abel

lemma add_fourfold_sub_eq_iff_cross_add {G : Type*} [AddCommGroup G]
    (a₁ a₂ c₁ c₂ b₁ b₂ d₁ d₂
      e₁ e₂ g₁ g₂ f₁ f₂ h₁ h₂ : G) :
    (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
        (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) ↔
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
        e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by
  constructor
  · intro heq
    calc
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
          ((a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = ((e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by abel
  · intro heq
    calc
      (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
          (a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = (e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) := by abel

omit [DecidableEq β] in
lemma fourfoldMapValue_eq_iff_eval_eq
    {A : Set α} {B : Finset β} {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g)
    {p r : FourfoldPresentation β} (hp : p.Mem B) (hr : r.Mem B) :
    fourfoldMapValue g p = fourfoldMapValue g r ↔ p.eval = r.eval := by
  let s : Multiset β :=
    p.pos₁ ::ₘ p.pos₂ ::ₘ r.neg₁ ::ₘ r.neg₂ ::ₘ 0
  let t : Multiset β :=
    r.pos₁ ::ₘ r.pos₂ ::ₘ p.neg₁ ::ₘ p.neg₂ ::ₘ 0
  have hsB : ∀ ⦃x⦄, x ∈ s → x ∈ (B : Set β) := by
    intro x hx
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hr.2.2.1, hr.2.2.2]
  have htB : ∀ ⦃x⦄, x ∈ t → x ∈ (B : Set β) := by
    intro x hx
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hr.1, hr.2.1, hp.2.2.1, hp.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = p.pos₁ + p.pos₂ + r.neg₁ + r.neg₂ := by
    simp [s]
    abel
  have ht : t.sum = r.pos₁ + r.pos₂ + p.neg₁ + p.neg₂ := by
    simp [t]
    abel
  have hgs : (s.map g).sum =
      g p.pos₁ + g p.pos₂ + g r.neg₁ + g r.neg₂ := by
    simp [s]
    abel
  have hgt : (t.map g).sum =
      g r.pos₁ + g r.pos₂ + g p.neg₁ + g p.neg₂ := by
    simp [t]
    abel
  rw [hs, ht, hgs, hgt] at hrel
  exact (fourfold_sub_eq_iff_cross_add
    (g p.pos₁) (g p.pos₂) (g p.neg₁) (g p.neg₂)
    (g r.pos₁) (g r.pos₂) (g r.neg₁) (g r.neg₂)).trans
      (hrel.trans (fourfold_sub_eq_iff_cross_add
        p.pos₁ p.pos₂ p.neg₁ p.neg₂ r.pos₁ r.pos₂ r.neg₁ r.neg₂).symm)

noncomputable def freimanFourfoldLift (B : Finset β) (hB : B.Nonempty)
    (g : β → α) (x : β) : α :=
  fourfoldMapValue g (selectedFourfoldPresentation B hB x)

lemma freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul [DecidableEq α]
    {A : Finset α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : Set.MapsTo g (B : Set β) (A : Set α))
    {x : β} (hx : x ∈ 2 • B - 2 • B) :
    freimanFourfoldLift B hB g x ∈ 2 • A - 2 • A := by
  let p := selectedFourfoldPresentation B hB x
  have hp := selectedFourfoldPresentation_spec B hB hx
  rw [mem_two_nsmul_sub_two_nsmul_iff]
  refine ⟨⟨g p.pos₁, g p.pos₂, g p.neg₁, g p.neg₂⟩, ?_, rfl⟩
  exact ⟨hg hp.1.1, hg hp.1.2.1, hg hp.1.2.2.1, hg hp.1.2.2.2⟩

theorem freimanFourfoldLift_injOn
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g) :
    Set.InjOn (freimanFourfoldLift B hB g) (2 • B - 2 • B : Finset β) := by
  intro x hx y hy hxy
  have hsx := selectedFourfoldPresentation_spec B hB hx
  have hsy := selectedFourfoldPresentation_spec B hB hy
  have heval := (fourfoldMapValue_eq_iff_eval_eq hg hsx.1 hsy.1).mp hxy
  rw [hsx.2, hsy.2] at heval
  exact heval

lemma freimanFourfoldLift_add_eq_add
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 8 (B : Set β) A g)
    {x y z w : β}
    (hx : x ∈ 2 • B - 2 • B) (hy : y ∈ 2 • B - 2 • B)
    (hz : z ∈ 2 • B - 2 • B) (hw : w ∈ 2 • B - 2 • B) :
    freimanFourfoldLift B hB g x + freimanFourfoldLift B hB g y =
        freimanFourfoldLift B hB g z + freimanFourfoldLift B hB g w ↔
      x + y = z + w := by
  let px := selectedFourfoldPresentation B hB x
  let py := selectedFourfoldPresentation B hB y
  let pz := selectedFourfoldPresentation B hB z
  let pw := selectedFourfoldPresentation B hB w
  have hpx := selectedFourfoldPresentation_spec B hB hx
  have hpy := selectedFourfoldPresentation_spec B hB hy
  have hpz := selectedFourfoldPresentation_spec B hB hz
  have hpw := selectedFourfoldPresentation_spec B hB hw
  let s : Multiset β := px.pos₁ ::ₘ px.pos₂ ::ₘ py.pos₁ ::ₘ py.pos₂ ::ₘ
    pz.neg₁ ::ₘ pz.neg₂ ::ₘ pw.neg₁ ::ₘ pw.neg₂ ::ₘ 0
  let t : Multiset β := pz.pos₁ ::ₘ pz.pos₂ ::ₘ pw.pos₁ ::ₘ pw.pos₂ ::ₘ
    px.neg₁ ::ₘ px.neg₂ ::ₘ py.neg₁ ::ₘ py.neg₂ ::ₘ 0
  have hsB : ∀ ⦃a⦄, a ∈ s → a ∈ (B : Set β) := by
    intro a ha
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpx.1.1, hpx.1.2.1, hpy.1.1, hpy.1.2.1,
      hpz.1.2.2.1, hpz.1.2.2.2, hpw.1.2.2.1, hpw.1.2.2.2]
  have htB : ∀ ⦃a⦄, a ∈ t → a ∈ (B : Set β) := by
    intro a ha
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpz.1.1, hpz.1.2.1, hpw.1.1, hpw.1.2.1,
      hpx.1.2.2.1, hpx.1.2.2.2, hpy.1.2.2.1, hpy.1.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = px.pos₁ + px.pos₂ + py.pos₁ + py.pos₂ +
      pz.neg₁ + pz.neg₂ + pw.neg₁ + pw.neg₂ := by
    simp [s]
    abel
  have ht : t.sum = pz.pos₁ + pz.pos₂ + pw.pos₁ + pw.pos₂ +
      px.neg₁ + px.neg₂ + py.neg₁ + py.neg₂ := by
    simp [t]
    abel
  have hgs : (s.map g).sum =
      g px.pos₁ + g px.pos₂ + g py.pos₁ + g py.pos₂ +
        g pz.neg₁ + g pz.neg₂ + g pw.neg₁ + g pw.neg₂ := by
    simp [s]
    abel
  have hgt : (t.map g).sum =
      g pz.pos₁ + g pz.pos₂ + g pw.pos₁ + g pw.pos₂ +
        g px.neg₁ + g px.neg₂ + g py.neg₁ + g py.neg₂ := by
    simp [t]
    abel
  rw [hs, ht, hgs, hgt] at hrel
  have hmapCross := add_fourfold_sub_eq_iff_cross_add
    (g px.pos₁) (g px.pos₂) (g px.neg₁) (g px.neg₂)
    (g py.pos₁) (g py.pos₂) (g py.neg₁) (g py.neg₂)
    (g pz.pos₁) (g pz.pos₂) (g pz.neg₁) (g pz.neg₂)
    (g pw.pos₁) (g pw.pos₂) (g pw.neg₁) (g pw.neg₂)
  have horiginalCross := add_fourfold_sub_eq_iff_cross_add
    px.pos₁ px.pos₂ px.neg₁ px.neg₂ py.pos₁ py.pos₂ py.neg₁ py.neg₂
    pz.pos₁ pz.pos₂ pz.neg₁ pz.neg₂ pw.pos₁ pw.pos₂ pw.neg₁ pw.neg₂
  have hvalues :
      px.eval + py.eval = pz.eval + pw.eval ↔ x + y = z + w := by
    rw [hpx.2, hpy.2, hpz.2, hpw.2]
  exact hmapCross.trans (hrel.trans (horiginalCross.symm.trans hvalues))

end

end Erdos587

end Erdos587_FreimanLift

section Erdos587_CyclicGapLift

open scoped BigOperators Pointwise

namespace Erdos587

noncomputable section

/- ## Linearizing a Freiman map on a cyclic progression -/

structure IntegerGeneralizedAP where
  rank : ℕ
  base : ℤ
  step : Fin rank → ℤ
  length : Fin rank → ℕ

namespace IntegerGeneralizedAP

abbrev Param (Q : IntegerGeneralizedAP) :=
  (i : Fin Q.rank) → Fin (Q.length i + 1)

def eval (Q : IntegerGeneralizedAP) (x : Q.Param) : ℤ :=
  Q.base + ∑ i, (x i : ℤ) * Q.step i

noncomputable def carrier (Q : IntegerGeneralizedAP) : Finset ℤ :=
  (Finset.univ : Finset Q.Param).image Q.eval

def Proper (Q : IntegerGeneralizedAP) : Prop := Function.Injective Q.eval

lemma mem_carrier_iff (Q : IntegerGeneralizedAP) {z : ℤ} :
    z ∈ Q.carrier ↔ ∃ x : Q.Param, Q.eval x = z := by
  simp [carrier]

lemma card_carrier_of_proper (Q : IntegerGeneralizedAP) (hQ : Q.Proper) :
    Q.carrier.card = ∏ i, (Q.length i + 1) := by
  rw [carrier, Finset.card_image_of_injective _ hQ, Finset.card_univ]
  simp [Param]

end IntegerGeneralizedAP

namespace CyclicCenteredGAP

variable {N : ℕ}

def minParam (Q : CyclicCenteredGAP N) : Q.Param := fun _ => 0

def unitParam (Q : CyclicCenteredGAP N) (i : Fin Q.rank)
    (hi : 0 < Q.radius i) : Q.Param := fun j =>
  if hji : j = i then ⟨1, by subst j; omega⟩ else 0

def predParam (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) : Q.Param := fun j =>
  if hji : j = i then
    ⟨(x i : ℕ) - 1, by
      subst j
      have hx := (x i).isLt
      omega⟩
  else x j

@[simp] lemma minParam_apply (Q : CyclicCenteredGAP N) (i : Fin Q.rank) :
    (Q.minParam i : ℕ) = 0 := rfl

@[simp] lemma unitParam_apply_self (Q : CyclicCenteredGAP N)
    (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    (Q.unitParam i hi i : ℕ) = 1 := by
  simp [unitParam]

@[simp] lemma unitParam_apply_ne (Q : CyclicCenteredGAP N)
    (i j : Fin Q.rank) (hi : 0 < Q.radius i) (hji : j ≠ i) :
    (Q.unitParam i hi j : ℕ) = 0 := by
  simp [unitParam, hji]

@[simp] lemma predParam_apply_self (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (Q.predParam x i hi i : ℕ) = (x i : ℕ) - 1 := by
  simp [predParam]

@[simp] lemma predParam_apply_ne (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i j : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hji : j ≠ i) :
    (Q.predParam x i hi j : ℕ) = x j := by
  simp [predParam, hji]

lemma eval_eq_eval_minParam_add_sum {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param) :
    Q.eval x = Q.eval Q.minParam +
      ∑ i, (x i : ZMod N) * Q.step i := by
  simp only [eval, coeff, minParam, Fin.val_zero,
    Nat.cast_zero, Int.cast_sub, Int.cast_natCast,
    zero_sub]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Int.cast_neg, Int.cast_natCast]
  ring

lemma eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    Q.eval (Q.unitParam i hi) = Q.eval Q.minParam + Q.step i := by
  rw [Q.eval_eq_eval_minParam_add_sum]
  congr 1
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  simp only [unitParam_apply_self, Nat.cast_one, one_mul]
  have hzero : ∑ j ∈ Finset.univ.erase i,
      ((Q.unitParam i hi j : ℕ) : ZMod N) * Q.step j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by
      exact Finset.ne_of_mem_erase hj
    simp [Q.unitParam_apply_ne i j hi hji]
  rw [hzero, zero_add]

lemma eval_predParam_add_eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    Q.eval (Q.predParam x i hi) + Q.eval (Q.unitParam i hradius) =
      Q.eval x + Q.eval Q.minParam := by
  have hpred := Q.eval_eq_eval_minParam_add_sum (Q.predParam x i hi)
  have hunit := Q.eval_unitParam i hradius
  have hx := Q.eval_eq_eval_minParam_add_sum x
  rw [hpred, hunit, hx]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          Q.step i =
        ∑ j, (x j : ZMod N) * Q.step j := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => (x j : ZMod N) * Q.step j) (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i,
        ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j =
      ∑ j ∈ Finset.univ.erase i, (x j : ZMod N) * Q.step j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Q.predParam_apply_ne x i j hi hji]
    rw [hrest, Q.predParam_apply_self]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    rw [← hxi]
    push_cast
    ring
  calc
    Q.eval Q.minParam +
          (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          (Q.eval Q.minParam + Q.step i) =
        Q.eval Q.minParam + Q.eval Q.minParam +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
            Q.step i) := by abel
    _ = Q.eval Q.minParam + Q.eval Q.minParam +
          ∑ j, (x j : ZMod N) * Q.step j := by rw [hsum]
    _ = Q.eval Q.minParam + (∑ j, (x j : ZMod N) * Q.step j) +
          Q.eval Q.minParam := by abel

lemma sum_predParam_add_one (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (∑ j, (Q.predParam x i hi j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ)) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (Q.predParam x i hi j : ℕ) =
        ∑ j ∈ Finset.univ.erase i, (x j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)
  rw [hrest, Q.predParam_apply_self]
  omega

end CyclicCenteredGAP

noncomputable def cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) : IntegerGeneralizedAP where
  rank := Q.rank
  base := L (Q.eval Q.minParam)
  step i := if hi : 0 < Q.radius i then
      L (Q.eval (Q.unitParam i hi)) - L (Q.eval Q.minParam)
    else 0
  length i := 2 * Q.radius i

@[simp] lemma cyclicGapFreimanImage_rank {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) :
    (cyclicGapFreimanImage Q L).rank = Q.rank := rfl

@[simp] lemma cyclicGapFreimanImage_length {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) (i : Fin Q.rank) :
    (cyclicGapFreimanImage Q L).length i = 2 * Q.radius i := rfl

lemma eval_cyclicGapFreimanImage_pred_add_step {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (L : ZMod N → ℤ) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    (cyclicGapFreimanImage Q L).eval x =
      (cyclicGapFreimanImage Q L).eval (Q.predParam x i hi) +
        ((cyclicGapFreimanImage Q L).step i) := by
  simp only [IntegerGeneralizedAP.eval, cyclicGapFreimanImage, dif_pos hradius]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
          (if hj : 0 < Q.radius j then
            L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
        (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) =
      ∑ j, ((x j : ℕ) : ℤ) *
          (if hj : 0 < Q.radius j then
            L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => ((x j : ℕ) : ℤ) *
        (if hj : 0 < Q.radius j then
          L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0))
      (Finset.mem_univ i)]
    have hrest :
        ∑ j ∈ Finset.univ.erase i, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) =
          ∑ j ∈ Finset.univ.erase i, ((x j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)]
    rw [hrest, Q.predParam_apply_self]
    simp only [dif_pos hradius]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    have hxiZ : (((x i : ℕ) - 1 : ℕ) : ℤ) + 1 = (x i : ℤ) := by
      exact_mod_cast hxi
    linear_combination
      (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) * hxiZ
  calc
    L (Q.eval Q.minParam) +
          ∑ j, ((x j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0) =
        L (Q.eval Q.minParam) +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
            (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam))) := by
              rw [hsum]
    _ = (L (Q.eval Q.minParam) +
          ∑ j, ((Q.predParam x i hi j : ℕ) : ℤ) *
            (if hj : 0 < Q.radius j then
              L (Q.eval (Q.unitParam j hj)) - L (Q.eval Q.minParam) else 0)) +
          (L (Q.eval (Q.unitParam i hradius)) - L (Q.eval Q.minParam)) := by
            ring

theorem eval_cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (D : Finset (ZMod N))
    (hQD : Q.carrier ⊆ D) (L : ZMod N → ℤ)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d)
    (x : Q.Param) :
    (cyclicGapFreimanImage Q L).eval x = L (Q.eval x) := by
  classical
  have hmem (y : Q.Param) : Q.eval y ∈ D := by
    apply hQD
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  induction hweight : (∑ i, (x i : ℕ)) using Nat.strong_induction_on generalizing x with
  | h k ih =>
      by_cases hk : k = 0
      · have hsumzero : ∑ i, (x i : ℕ) = 0 := hweight.trans hk
        have hxzero (i : Fin Q.rank) : (x i : ℕ) = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun _ _ => Nat.zero_le _)).mp hsumzero i (Finset.mem_univ i)
        have hx : x = Q.minParam := by
          funext i
          apply Fin.ext
          exact hxzero i
        subst x
        simp [IntegerGeneralizedAP.eval, cyclicGapFreimanImage,
          CyclicCenteredGAP.minParam]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hsumpos : 0 < ∑ i, (x i : ℕ) := by omega
        rw [Finset.sum_pos_iff_of_nonneg (by simp)] at hsumpos
        obtain ⟨i, _hiuniv, hi⟩ := hsumpos
        have hradius : 0 < Q.radius i := by
          have hix := (x i).isLt
          change (x i : ℕ) < 2 * Q.radius i + 1 at hix
          omega
        let y := Q.predParam x i hi
        have hyweight : (∑ j, (y j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
          exact Q.sum_predParam_add_one x i hi
        have hylt : (∑ j, (y j : ℕ)) < k := by omega
        have ihy : (cyclicGapFreimanImage Q L).eval y = L (Q.eval y) :=
          ih _ hylt y rfl
        have hrel : L (Q.eval y) + L (Q.eval (Q.unitParam i hradius)) =
            L (Q.eval x) + L (Q.eval Q.minParam) := by
          apply hadd (hmem y) (hmem (Q.unitParam i hradius))
            (hmem x) (hmem Q.minParam)
          exact Q.eval_predParam_add_eval_unitParam x i hi hradius
        rw [eval_cyclicGapFreimanImage_pred_add_step Q L x i hi hradius, ihy]
        simp only [cyclicGapFreimanImage, dif_pos hradius]
        omega

theorem proper_cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (hQ : Q.Proper)
    (D : Finset (ZMod N)) (hQD : Q.carrier ⊆ D)
    (L : ZMod N → ℤ) (hLinj : Set.InjOn L D)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d) :
    (cyclicGapFreimanImage Q L).Proper := by
  intro x y hxy
  have hx := eval_cyclicGapFreimanImage Q D hQD L hadd x
  have hy := eval_cyclicGapFreimanImage Q D hQD L hadd y
  rw [hx, hy] at hxy
  apply hQ
  exact hLinj (by
    apply hQD
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩) (by
    apply hQD
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩) hxy

theorem carrier_cyclicGapFreimanImage {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (D : Finset (ZMod N))
    (hQD : Q.carrier ⊆ D) (L : ZMod N → ℤ)
    (hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d) :
    (cyclicGapFreimanImage Q L).carrier = Q.carrier.image L := by
  ext z
  simp only [IntegerGeneralizedAP.mem_carrier_iff, Finset.mem_image]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Q.eval x, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    · exact (eval_cyclicGapFreimanImage Q D hQD L hadd x).symm
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨x, eval_cyclicGapFreimanImage Q D hQD L hadd x⟩

/-
## Lifting a cyclic progression back through a Freiman model

The inverse of an order-eight Freiman isomorphism extends to the fourfold
difference set.  On a proper cyclic GAP the preceding linearization theorem
turns that extension into a proper affine GAP in `ℤ`, with no loss of rank or
cardinality.
-/

theorem exists_proper_integerGAP_lift_of_cyclic
    {N : ℕ} [NeZero N]
    (A : Finset ℤ) (B : Finset (ZMod N)) (hB : B.Nonempty)
    (f : ℤ → ZMod N)
    (hf : IsAddFreimanIso 8 (A : Set ℤ) (B : Set (ZMod N)) f)
    (Q : CyclicCenteredGAP N) (hQproper : Q.Proper)
    (hQsub : Q.carrier ⊆ 2 • B - 2 • B) :
    ∃ P : IntegerGeneralizedAP,
      P.rank = Q.rank ∧
      P.Proper ∧
      P.carrier ⊆ 2 • A - 2 • A ∧
      P.carrier.card = Q.carrier.card := by
  let g : ZMod N → ℤ := Function.invFunOn f (A : Set ℤ)
  have hg : IsAddFreimanIso 8 (B : Set (ZMod N)) (A : Set ℤ) g := by
    simpa only [g] using hf.invFunOn
  let D : Finset (ZMod N) := 2 • B - 2 • B
  let L : ZMod N → ℤ := freimanFourfoldLift B hB g
  have hLinj : Set.InjOn L D := by
    simpa only [L, D] using
      (freimanFourfoldLift_injOn hB (hg.mono (hmn := by omega)))
  have hadd : ∀ {a b c d : ZMod N},
      a ∈ D → b ∈ D → c ∈ D → d ∈ D →
      a + b = c + d → L a + L b = L c + L d := by
    intro a b c d ha hb hc hd hab
    exact (freimanFourfoldLift_add_eq_add hB hg ha hb hc hd).mpr hab
  let P : IntegerGeneralizedAP := cyclicGapFreimanImage Q L
  have hPproper : P.Proper := by
    exact proper_cyclicGapFreimanImage Q hQproper D hQsub L hLinj hadd
  have hPcarrier : P.carrier = Q.carrier.image L := by
    exact carrier_cyclicGapFreimanImage Q D hQsub L hadd
  refine ⟨P, rfl, hPproper, ?_, ?_⟩
  · rw [hPcarrier]
    intro z hz
    obtain ⟨x, hxQ, rfl⟩ := Finset.mem_image.mp hz
    exact freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul hB
      hg.bijOn.mapsTo (hQsub hxQ)
  · rw [hPcarrier]
    exact Finset.card_image_of_injOn (hLinj.mono hQsub)

end

end Erdos587

end Erdos587_CyclicGapLift

section Erdos587_GAPDefinitions

/- Elementary GAP presentations, independent of the analytic square-location inputs. -/

open scoped BigOperators Pointwise

namespace Erdos587

/- ## Generalized arithmetic progressions -/

/-- An affine generalized arithmetic progression in `ℤ`, presented by a
finite box of coefficients. -/
structure GeneralizedAP where
  rank : ℕ
  base : ℤ
  step : Fin rank → ℤ
  length : Fin rank → ℕ

namespace GeneralizedAP

/-- The common integer-GAP presentation constructed by the cyclic-model
lifting module, viewed as the GAP type used by the Nguyen--Vu properization
machinery below. -/
def ofInteger (P : IntegerGeneralizedAP) : GeneralizedAP where
  rank := P.rank
  base := P.base
  step := P.step
  length := P.length

/-- Coefficient vectors in the defining box. -/
abbrev Param (Q : GeneralizedAP) := (i : Fin Q.rank) → Fin (Q.length i + 1)

/-- Evaluation of a coefficient vector. -/
def eval (Q : GeneralizedAP) (x : Q.Param) : ℤ :=
  Q.base + ∑ i : Fin Q.rank, (x i : ℤ) * Q.step i

/-- The finite carrier of a GAP. -/
def carrier (Q : GeneralizedAP) : Finset ℤ :=
  (Finset.univ : Finset Q.Param).image Q.eval

/-- A GAP is proper when its coefficient map is injective. -/
def Proper (Q : GeneralizedAP) : Prop := Function.Injective Q.eval

@[simp] lemma rank_ofInteger (P : IntegerGeneralizedAP) :
    (ofInteger P).rank = P.rank := rfl

@[simp] lemma eval_ofInteger (P : IntegerGeneralizedAP) (x : P.Param) :
    (ofInteger P).eval x = P.eval x := rfl

@[simp] lemma carrier_ofInteger (P : IntegerGeneralizedAP) :
    (ofInteger P).carrier = P.carrier := rfl

@[simp] lemma proper_ofInteger (P : IntegerGeneralizedAP) :
    (ofInteger P).Proper ↔ P.Proper := Iff.rfl

lemma mem_carrier_iff (Q : GeneralizedAP) {z : ℤ} :
    z ∈ Q.carrier ↔ ∃ x : Q.Param, Q.eval x = z := by
  simp [carrier]

/-- A proper GAP has the cardinality of its coefficient box. -/
lemma card_carrier_of_proper (Q : GeneralizedAP) (hQ : Q.Proper) :
    Q.carrier.card = ∏ i : Fin Q.rank, (Q.length i + 1) := by
  rw [carrier, Finset.card_image_of_injective (Finset.univ : Finset Q.Param) hQ,
    Finset.card_univ]
  simp [Param]

/-- Paper notation `nQ`: multiply the affine base and every side length by
`n`, while retaining the difference set. -/
def dilate (n : ℕ) (Q : GeneralizedAP) : GeneralizedAP where
  rank := Q.rank
  base := n * Q.base
  step := Q.step
  length i := n * Q.length i

@[simp] lemma rank_dilate (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate n).rank = Q.rank := rfl

/-- The coefficient-box cardinality of a GAP presentation. -/
def boxCard (Q : GeneralizedAP) : ℕ :=
  ∏ i : Fin Q.rank, (Q.length i + 1)

end GeneralizedAP

end Erdos587

end Erdos587_GAPDefinitions

section FreimanEstimates

open Filter MeasureTheory
open scoped Pointwise

namespace Erdos587

/-- Natural-number specialization of Mathlib's Ruzsa covering lemma for
finite integer sets. -/
lemma ruzsa_covering_int {A B : Finset ℤ} {K : ℕ} (hB : B.Nonempty)
    (hsmall : (A + B).card ≤ K * B.card) :
    ∃ F ⊆ A, F.card ≤ K ∧ A ⊆ F + (B - B) := by
  have hsmall' : ((A + B).card : ℝ) ≤ (K : ℝ) * (B.card : ℝ) := by
    exact_mod_cast hsmall
  obtain ⟨F, hFA, hFK, hcover⟩ := Finset.ruzsa_covering_add hB hsmall'
  refine ⟨F, hFA, ?_, hcover⟩
  exact_mod_cast hFK

/-- Natural-number consequence of Mathlib's Plünnecke--Ruzsa inequality. -/
lemma pluennecke_ruzsa_int {A B : Finset ℤ} {K m n : ℕ} (hA : A.Nonempty)
    (hsmall : (A + B).card ≤ K * A.card) :
    (m • B - n • B).card ≤ K ^ (m + n) * A.card := by
  have hratio :
      ((A + B).card : ℚ≥0) / (A.card : ℚ≥0) ≤ (K : ℚ≥0) := by
    rw [div_le_iff₀]
    · exact_mod_cast hsmall
    · exact_mod_cast hA.card_pos
  have hbound := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B m n
  have hbound' :
      ((m • B - n • B).card : ℚ≥0) ≤
        (K : ℚ≥0) ^ (m + n) * (A.card : ℚ≥0) := by
    refine hbound.trans ?_
    gcongr
  exact_mod_cast hbound'

/-- The faithful image of a finite natural-number set in the additive group
of integers.  Nguyen--Vu's inverse theorems are stated in `ℤ`, while the
distinct-summand construction above naturally lives in `ℕ`. -/
def natToIntFinset (A : Finset ℕ) : Finset ℤ :=
  A.image (Int.ofNatHom : ℕ →+* ℤ)

@[simp] lemma card_natToIntFinset (A : Finset ℕ) :
    (natToIntFinset A).card = A.card := by
  exact Finset.card_image_of_injective A Int.ofNat_injective

lemma natToIntFinset_add (A B : Finset ℕ) :
    natToIntFinset (A + B) = natToIntFinset A + natToIntFinset B := by
  exact Finset.image_add (Int.ofNatHom : ℕ →+* ℤ)


lemma natToIntFinset_nonempty {A : Finset ℕ} :
    (natToIntFinset A).Nonempty ↔ A.Nonempty := by
  simp [natToIntFinset]

@[simp] lemma natCast_mem_natToIntFinset {A : Finset ℕ} {n : ℕ} :
    (n : ℤ) ∈ natToIntFinset A ↔ n ∈ A := by
  simp [natToIntFinset]

/-- Freiman's `3k - 4` theorem in the natural-number form needed as the
rank-one base of the Nguyen--Vu inverse argument.  The proof is internal: it
normalizes by the gcd and applies the Kneser-based Ruzsa diameter estimate
already proved for Erdős Problem 13. -/
theorem exists_short_natAP_of_three_k_minus_four
    {S : Finset ℕ} (hS : S.Nonempty) (hcard : 2 ≤ S.card)
    (hsmall : (S + S).card ≤ 3 * S.card - 4) :
    ∃ a d L : ℕ, 0 < d ∧ L ≤ 2 * S.card - 3 ∧
      S ⊆ Erdos13Additive.natAP a d L := by
  let s := S.min' hS
  let M := S.max' hS
  let v := M - s
  have hsS : s ∈ S := S.min'_mem hS
  have hMS : M ∈ S := S.max'_mem hS
  have hSmin : ∀ x ∈ S, s ≤ x := fun x hx ↦ S.min'_le x hx
  have hSmax : ∀ x ∈ S, x ≤ M := fun x hx ↦ S.le_max' x hx
  have hvpos : 0 < v := by
    by_contra hv
    have hvzero : v = 0 := Nat.eq_zero_of_not_pos hv
    have hSM : s = M := by
      have hsM : s ≤ M := hSmin M hMS
      dsimp [v, s, M] at hvzero ⊢
      omega
    have hsingle : S = {s} := by
      ext x
      constructor
      · intro hx
        have hxlo := hSmin x hx
        have hxhi := hSmax x hx
        simp only [Finset.mem_singleton]
        omega
      · intro hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact hsS
    rw [hsingle] at hcard
    simp at hcard
  let W := Erdos13Additive.normalizeNat S s 1
  let d := W.gcd (fun n : ℕ ↦ n)
  have hvW : v ∈ W := by
    have h := Erdos13Additive.top_mem_normalizeNat
      (m := s) (d := 1) hMS
    simpa [W, v, M, s] using h
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hz := (Finset.gcd_eq_zero_iff.mp hd) v hvW
    omega
  have hSdiv : ∀ x ∈ S, d ∣ x - s := by
    intro x hx
    apply Finset.gcd_dvd
    apply Erdos13Additive.mem_normalizeNat.mpr
    exact ⟨x, hx, by simp⟩
  have hdv : d ∣ v := Finset.gcd_dvd hvW
  have hdvle : d ≤ v := Nat.le_of_dvd hvpos hdv
  have hvqpos : 0 < v / d := Nat.div_pos hdvle hdpos
  let A := Erdos13Additive.normalizeNat S s d
  have hAint : A ⊆ Finset.Icc 0 (v / d) := by
    apply Erdos13Additive.normalizeNat_subset_Icc
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hSmin x hx, hSmax x hx⟩
  have hAzero : 0 ∈ A := Erdos13Additive.zero_mem_normalizeNat hsS
  have hAtop : v / d ∈ A := by
    simpa [A, v, M, s] using
      (Erdos13Additive.top_mem_normalizeNat
        (m := s) (d := d) hMS)
  have hAW : A = W.image (fun z ↦ z / d) := by
    ext q
    simp only [A, W, Erdos13Additive.normalizeNat,
      Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x - s, ⟨x, hx, by simp⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simpa using congrArg (fun n ↦ n / d) hxz
  have hWgcd : W.gcd (fun z ↦ z / d) = 1 := by
    exact Finset.gcd_div_id_eq_one hvW hvpos.ne'
  have hAgcdNat : A.gcd (fun n : ℕ ↦ n) = 1 := by
    rw [hAW, Finset.gcd_image]
    exact hWgcd
  have hAgcdInt : A.gcd (fun n ↦ (n : ℤ)) = 1 := by
    rw [Erdos13Additive.nat_int_finset_gcd, hAgcdNat]
    norm_num
  have hAcard : A.card = S.card := by
    exact Erdos13Additive.card_normalizeNat hdpos hSmin hSdiv
  have hsumcard : (A + A).card = (S + S).card := by
    symm
    exact Erdos13Additive.card_sumset_eq_card_normalized
      hdpos hSmin hSmin hSdiv hSdiv
  have hruzsa := Erdos13Additive.ruzsa_normalized_diameter_bound
    hAint hAint (le_refl _) hvqpos hAzero hAtop hAzero hAtop
      (by simpa using hAgcdInt)
  have hthree : (A + A).card < 3 * S.card - 3 := by
    rw [hsumcard]
    omega
  have hdiameter : S.card + v / d ≤ (A + A).card := by
    rw [hAcard] at hruzsa
    by_contra hnot
    have hfirst : (A + A).card < S.card + v / d :=
      Nat.lt_of_not_ge hnot
    have hsecond : (A + A).card <
        S.card + S.card + min S.card S.card - 3 := by
      rw [min_self]
      have heq : S.card + S.card + S.card - 3 =
          3 * S.card - 3 := by omega
      rw [heq]
      exact hthree
    exact (not_lt_of_ge hruzsa) (lt_min hfirst hsecond)
  have hLbound : v / d + 1 ≤ 2 * S.card - 3 := by
    rw [hsumcard] at hdiameter
    omega
  refine ⟨s, d, v / d + 1, hdpos, hLbound, ?_⟩
  intro x hx
  have hqmem : (x - s) / d ∈ A :=
    Erdos13Additive.mem_normalizeNat.mpr ⟨x, hx, rfl⟩
  have hqle : (x - s) / d ≤ v / d :=
    (Finset.mem_Icc.mp (hAint hqmem)).2
  apply Erdos13Additive.mem_natAP.mpr
  refine ⟨(x - s) / d, by omega, ?_⟩
  have hsx : s ≤ x := hSmin x hx
  calc
    s + d * ((x - s) / d) = s + (x - s) := by
      rw [Nat.mul_div_cancel' (hSdiv x hx)]
    _ = x := Nat.add_sub_of_le hsx

namespace GeneralizedAP

@[simp] lemma boxCard_dilate (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate n).boxCard =
      ∏ i : Fin Q.rank, (n * Q.length i + 1) := by
  rfl

/-- A `g`-dilated coefficient box grows by at most `g^rank` when `g ≥ 1`. -/
lemma boxCard_dilate_le_pow_mul_boxCard (Q : GeneralizedAP)
    {g : ℕ} (hg : 1 ≤ g) :
    (Q.dilate g).boxCard ≤ g ^ Q.rank * Q.boxCard := by
  rw [boxCard_dilate, boxCard]
  calc
    ∏ i : Fin Q.rank, (g * Q.length i + 1) ≤
        ∏ i : Fin Q.rank, g * (Q.length i + 1) := by
      apply Finset.prod_le_prod'
      intro i _hi
      calc
        g * Q.length i + 1 ≤ g * Q.length i + g :=
          Nat.add_le_add_left hg _
        _ = g * (Q.length i + 1) := by ring
    _ = g ^ Q.rank * ∏ i : Fin Q.rank, (Q.length i + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

end GeneralizedAP

/- ## The quantitative Freiman step in Nguyen--Vu -/

/-- Density loss in the order-eight Ruzsa model. -/
def freimanModelDensity (K : ℕ) : ℕ := 32 * K ^ 16

/-- Uniform rank of the cyclic progression extracted from the model. -/
def freimanCyclicRank (K : ℕ) : ℕ :=
  16 * (freimanModelDensity K) ^ 3 + 1

/-- A deliberately coarse uniform majorant for all the geometry-of-numbers
denominators in ranks at most `freimanCyclicRank K`. -/
noncomputable def freimanCyclicDenominator (K : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (freimanCyclicRank K + 1), bohrQuarterDenominator d

/-- Natural cardinality loss for the proper integer GAP transported out of
the cyclic model. -/
noncomputable def freimanCyclicCardFactor (K : ℕ) : ℕ :=
  ⌈16 * freimanCyclicDenominator K⌉₊

lemma freimanModelDensity_pos {K : ℕ} (hK : 1 ≤ K) :
    0 < freimanModelDensity K := by
  unfold freimanModelDensity
  positivity

/-- The proper-GAP core of Freiman's theorem, in the exact fourfold
difference set needed for Ruzsa covering.  All constants depend only on the
doubling parameter `K`. -/
theorem exists_large_proper_GAP_in_fourfoldDifference
    (A : Finset ℤ) (hA : A.Nonempty) (K : ℕ) (hK : 1 ≤ K)
    (hsmall : (A + A).card ≤ K * A.card) :
    ∃ P : GeneralizedAP,
      P.rank ≤ freimanCyclicRank K ∧
      P.Proper ∧
      P.carrier ⊆ 2 • A - 2 • A ∧
      A.card ≤ freimanCyclicCardFactor K * P.carrier.card := by
  classical
  let D : Finset ℤ := 8 • A - 8 • A
  have hDne : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate 8 a).sum ∈ 8 • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate 8 a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hDpos : 0 < D.card := Finset.card_pos.mpr hDne
  obtain ⟨A', B, f, hA'ne, hA'sub, hA'large, hBimage, hf⟩ :=
    exists_large_cyclic_freiman_model A 8 hA (by norm_num)
  have hDdef : (8 • A - 8 • A) = D := rfl
  have hBne : B.Nonempty := by
    rw [hBimage]
    exact hA'ne.image f
  have hBcard : B.card = A'.card := by
    rw [hBimage]
    exact Finset.card_image_of_injOn hf.bijOn.injOn
  have hDupper : D.card ≤ K ^ 16 * A.card := by
    simpa only [D, Nat.reduceAdd] using
      (pluennecke_ruzsa_int hA hsmall (m := 8) (n := 8))
  let M : ℕ := 2 * D.card
  have hMpos : 0 < M := by dsimp [M]; omega
  have hMtwo : 1 < M := by dsimp [M]; omega
  let : NeZero M := ⟨hMpos.ne'⟩
  let q := freimanModelDensity K
  have hqpos : 1 ≤ q := by
    dsimp [q]
    exact freimanModelDensity_pos hK
  have hMdense : M ≤ q * B.card := by
    dsimp only [M, q, freimanModelDensity]
    rw [hBcard]
    calc
      2 * D.card ≤ 2 * (K ^ 16 * A.card) := Nat.mul_le_mul_left 2 hDupper
      _ ≤ 2 * (K ^ 16 * (16 * A'.card)) := by
        gcongr
      _ = (32 * K ^ 16) * A'.card := by ring
  let R : ℝ := (M : ℝ) / 4
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hRsmall : 4 * R ≤ (M : ℝ) := by
    dsimp [R]
    ring_nf
    exact le_rfl
  obtain ⟨Q, hQrank, hQproper, hQsub, hQcard⟩ :=
    exists_proper_cyclicProgression_in_fourfoldDifference
      hMtwo q hqpos B hBne hMdense R hRpos hRsmall
  have hQrank' : Q.rank ≤ freimanCyclicRank K := by
    simpa only [q, freimanCyclicRank] using hQrank
  obtain ⟨P₀, hP₀rank, hP₀proper, hP₀sub, hP₀card⟩ :=
    exists_proper_integerGAP_lift_of_cyclic A' B hBne f hf Q hQproper hQsub
  let P : GeneralizedAP := GeneralizedAP.ofInteger P₀
  have hsumSub : 2 • A' ⊆ 2 • A := nsmul_le_nsmul_right hA'sub 2
  have hPsub : P.carrier ⊆ 2 • A - 2 • A := by
    intro z hz
    have hz₀ : z ∈ P₀.carrier := by simpa only [P, GeneralizedAP.carrier_ofInteger] using hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp (hP₀sub hz₀)
    exact Finset.mem_sub.mpr ⟨u, hsumSub hu, v, hsumSub hv, rfl⟩
  let d : ℕ :=
    (cyclicLargeSpectrum B ((B.card : ℝ) / (4 * q))).card
  have hd : d ≤ freimanCyclicRank K := by
    have hspectrum := card_largeSpectrum_le_of_density q hqpos B hBne hMdense
    dsimp only [d]
    exact hspectrum.trans (by
      dsimp only [freimanCyclicRank, q]
      omega)
  have hdmem : d ∈ Finset.range (freimanCyclicRank K + 1) := by
    exact Finset.mem_range.mpr (by omega)
  have hdenomLe : bohrQuarterDenominator d ≤ freimanCyclicDenominator K := by
    exact Finset.single_le_sum
      (fun e he => (bohrQuarterDenominator_pos e).le) hdmem
  have hQcard' : (M : ℝ) / bohrQuarterDenominator d ≤
      (Q.carrier.card : ℝ) := by
    rw [← bohrProgressionLowerBound_quarter M d hMpos]
    simpa only [R, d] using hQcard
  have hMcard : (M : ℝ) ≤
      bohrQuarterDenominator d * (Q.carrier.card : ℝ) := by
    have := (div_le_iff₀ (bohrQuarterDenominator_pos d)).mp hQcard'
    nlinarith
  have hMcardUniform : (M : ℝ) ≤
      freimanCyclicDenominator K * (P.carrier.card : ℝ) := by
    calc
      (M : ℝ) ≤ bohrQuarterDenominator d * (Q.carrier.card : ℝ) := hMcard
      _ = bohrQuarterDenominator d * (P.carrier.card : ℝ) := by
        rw [show P.carrier.card = P₀.carrier.card by rfl, hP₀card]
      _ ≤ freimanCyclicDenominator K * (P.carrier.card : ℝ) := by
        gcongr
  have hBcardM : B.card ≤ M := by
    calc
      B.card ≤ Fintype.card (ZMod M) := Finset.card_le_univ B
      _ = M := ZMod.card M
  have hAreal : (A.card : ℝ) ≤
      16 * freimanCyclicDenominator K * (P.carrier.card : ℝ) := by
    have hAtoM : A.card ≤ 16 * M := by
      calc
        A.card ≤ 16 * A'.card := by simpa using hA'large
        _ = 16 * B.card := by rw [hBcard]
        _ ≤ 16 * M := Nat.mul_le_mul_left 16 hBcardM
    have hAtoMR : (A.card : ℝ) ≤ 16 * (M : ℝ) := by
      exact_mod_cast hAtoM
    calc
      (A.card : ℝ) ≤ 16 * (M : ℝ) := hAtoMR
      _ ≤ 16 * (freimanCyclicDenominator K * (P.carrier.card : ℝ)) := by
        gcongr
      _ = 16 * freimanCyclicDenominator K * (P.carrier.card : ℝ) := by ring
  have hceil : 16 * freimanCyclicDenominator K ≤
      (freimanCyclicCardFactor K : ℝ) := by
    exact Nat.le_ceil (16 * freimanCyclicDenominator K)
  have hAreal' : (A.card : ℝ) ≤
      (freimanCyclicCardFactor K : ℝ) * (P.carrier.card : ℝ) := by
    calc
      (A.card : ℝ) ≤
          16 * freimanCyclicDenominator K * (P.carrier.card : ℝ) := hAreal
      _ ≤ (freimanCyclicCardFactor K : ℝ) * (P.carrier.card : ℝ) := by
        gcongr
  refine ⟨P, ?_, ?_, hPsub, ?_⟩
  · simpa only [P, GeneralizedAP.rank_ofInteger, hP₀rank] using hQrank'
  · simpa only [P, GeneralizedAP.proper_ofInteger] using hP₀proper
  · exact_mod_cast hAreal'

namespace GeneralizedAP

/-- A GAP presentation containing the difference set `P - P`. -/
def differenceAP (P : GeneralizedAP) : GeneralizedAP where
  rank := P.rank
  base := -∑ i, (P.length i : ℤ) * P.step i
  step := P.step
  length i := 2 * P.length i

def differenceParam (P : GeneralizedAP) (x y : P.Param) :
    P.differenceAP.Param := fun i =>
  ⟨P.length i + (x i : ℕ) - (y i : ℕ), by
    have hx := (x i).isLt
    have hy := (y i).isLt
    dsimp [differenceAP]
    omega⟩

lemma eval_differenceParam (P : GeneralizedAP) (x y : P.Param) :
    P.differenceAP.eval (P.differenceParam x y) = P.eval x - P.eval y := by
  simp only [eval, differenceAP, differenceParam]
  have hcast (i : Fin P.rank) :
      ((P.length i + (x i : ℕ) - (y i : ℕ) : ℕ) : ℤ) =
        (P.length i : ℤ) + (x i : ℤ) - (y i : ℤ) := by
    have hy := (y i).isLt
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp_rw [hcast]
  change (-∑ i : Fin P.rank, (P.length i : ℤ) * P.step i) +
      ∑ i : Fin P.rank,
        ((P.length i : ℤ) + (x i : ℤ) - (y i : ℤ)) * P.step i =
    P.base + ∑ i : Fin P.rank, (x i : ℤ) * P.step i -
      (P.base + ∑ i : Fin P.rank, (y i : ℤ) * P.step i)
  have hsum :
      (∑ i : Fin P.rank,
        ((P.length i : ℤ) + (x i : ℤ) - (y i : ℤ)) * P.step i) =
      (∑ i : Fin P.rank, (P.length i : ℤ) * P.step i) +
        (∑ i : Fin P.rank, (x i : ℤ) * P.step i) -
        ∑ i : Fin P.rank, (y i : ℤ) * P.step i := by
    calc
      (∑ i : Fin P.rank,
          ((P.length i : ℤ) + (x i : ℤ) - (y i : ℤ)) * P.step i) =
          ∑ i : Fin P.rank,
            ((P.length i : ℤ) * P.step i +
              (x i : ℤ) * P.step i - (y i : ℤ) * P.step i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin P.rank, (P.length i : ℤ) * P.step i) +
          (∑ i : Fin P.rank, (x i : ℤ) * P.step i) -
          ∑ i : Fin P.rank, (y i : ℤ) * P.step i := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsum]
  ring

lemma sub_carrier_subset_differenceAP (P : GeneralizedAP) :
    P.carrier - P.carrier ⊆ P.differenceAP.carrier := by
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨x, hx⟩ := P.mem_carrier_iff.mp hu
  obtain ⟨y, hy⟩ := P.mem_carrier_iff.mp hv
  rw [← hx, ← hy]
  exact P.differenceAP.mem_carrier_iff.mpr
    ⟨P.differenceParam x y, P.eval_differenceParam x y⟩

@[simp] lemma rank_differenceAP (P : GeneralizedAP) :
    P.differenceAP.rank = P.rank := rfl

lemma boxCard_differenceAP (P : GeneralizedAP) :
    P.differenceAP.boxCard = (P.dilate 2).boxCard := rfl

/-- Add one binary generator for every element of a finite translating set. -/
noncomputable def translateCoverAP (P : GeneralizedAP) (F : Finset ℤ) :
    GeneralizedAP where
  rank := P.rank + F.card
  base := P.base
  step := Fin.addCases P.step (fun j => (F.equivFin.symm j : ℤ))
  length := Fin.addCases P.length (fun _ => 1)

noncomputable def translateCoverParam (P : GeneralizedAP) (F : Finset ℤ)
    (x : P.Param) (j : Fin F.card) : (P.translateCoverAP F).Param :=
  Fin.addCases
    (fun i => ⟨x i, by
      simpa only [translateCoverAP, Fin.addCases_left] using (x i).isLt⟩)
    (fun k => if hkj : k = j then
      ⟨1, by simp [translateCoverAP]⟩ else 0)

lemma eval_translateCoverParam (P : GeneralizedAP) (F : Finset ℤ)
    (x : P.Param) (j : Fin F.card) :
    (P.translateCoverAP F).eval (P.translateCoverParam F x j) =
      P.eval x + (F.equivFin.symm j : ℤ) := by
  change P.base +
      ∑ i : Fin (P.rank + F.card),
        ((P.translateCoverParam F x j i : ℕ) : ℤ) *
          (P.translateCoverAP F).step i =
    P.base + ∑ i : Fin P.rank, (x i : ℤ) * P.step i +
      (F.equivFin.symm j : ℤ)
  rw [Fin.sum_univ_add]
  simp only [translateCoverParam, translateCoverAP,
    Fin.addCases_left, Fin.addCases_right]
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro k hk hkj
    simp [hkj]
  · simp

lemma add_subset_translateCoverAP (P : GeneralizedAP) (F : Finset ℤ) :
    F + P.carrier ⊆ (P.translateCoverAP F).carrier := by
  intro z hz
  obtain ⟨f, hf, p, hp, rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨x, hx⟩ := P.mem_carrier_iff.mp hp
  let j : Fin F.card := F.equivFin ⟨f, hf⟩
  apply (P.translateCoverAP F).mem_carrier_iff.mpr
  refine ⟨P.translateCoverParam F x j, ?_⟩
  rw [P.eval_translateCoverParam F x j, hx]
  have hj : (F.equivFin.symm j : F) = ⟨f, hf⟩ := by
    exact F.equivFin.symm_apply_apply ⟨f, hf⟩
  have hjval : (F.equivFin.symm j : ℤ) = f := congrArg Subtype.val hj
  rw [hjval]
  exact add_comm p f

@[simp] lemma rank_translateCoverAP (P : GeneralizedAP) (F : Finset ℤ) :
    (P.translateCoverAP F).rank = P.rank + F.card := rfl

lemma boxCard_translateCoverAP (P : GeneralizedAP) (F : Finset ℤ) :
    (P.translateCoverAP F).boxCard = P.boxCard * 2 ^ F.card := by
  change (∏ i : Fin (P.rank + F.card),
      (Fin.addCases P.length (fun _ => 1) i + 1)) =
    (∏ i : Fin P.rank, (P.length i + 1)) * 2 ^ F.card
  rw [Fin.prod_univ_add]
  simp

lemma boxCard_translateCoverAP_differenceAP_le (P : GeneralizedAP)
    (hP : P.Proper) (F : Finset ℤ) :
    (P.differenceAP.translateCoverAP F).boxCard ≤
      2 ^ (P.rank + F.card) * P.carrier.card := by
  rw [boxCard_translateCoverAP, boxCard_differenceAP,
    P.card_carrier_of_proper hP]
  have hdiff := P.boxCard_dilate_le_pow_mul_boxCard (g := 2) (by omega)
  calc
    (P.dilate 2).boxCard * 2 ^ F.card ≤
        (2 ^ P.rank * P.boxCard) * 2 ^ F.card :=
      Nat.mul_le_mul_right _ hdiff
    _ = 2 ^ (P.rank + F.card) * P.boxCard := by rw [pow_add]; ring

end GeneralizedAP

/-- Number of Ruzsa translates used to cover a small-doubling set. -/
noncomputable def freimanCoverCount (K : ℕ) : ℕ :=
  K ^ 5 * freimanCyclicCardFactor K

/-- Uniform rank in the integer Freiman theorem used by Nguyen--Vu. -/
noncomputable def freimanRank (K : ℕ) : ℕ :=
  freimanCyclicRank K + freimanCoverCount K

/-- Uniform coefficient-box factor after adding the Ruzsa translates. -/
noncomputable def freimanSizeFactor (K : ℕ) : ℕ :=
  2 ^ (freimanRank K) * K ^ 4

theorem exists_GAP_cover_of_small_doubling
    (A : Finset ℤ) (hA : A.Nonempty) (K : ℕ) (hK : 1 ≤ K)
    (hsmall : (A + A).card ≤ K * A.card) :
    ∃ Q : GeneralizedAP,
      Q.rank ≤ freimanRank K ∧
      A ⊆ Q.carrier ∧
      Q.boxCard ≤ freimanSizeFactor K * A.card := by
  classical
  obtain ⟨P, hPrank, hPproper, hPsub, hPlarge⟩ :=
    exists_large_proper_GAP_in_fourfoldDifference A hA K hK hsmall
  have hPne : P.carrier.Nonempty := by
    apply Finset.card_pos.mp
    have hApos := Finset.card_pos.mpr hA
    by_contra hzero
    have hz : P.carrier.card = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hz, mul_zero] at hPlarge
    omega
  have hAPsub : A + P.carrier ⊆ 3 • A - 2 • A := by
    intro z hz
    obtain ⟨a, ha, p, hp, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, hpval⟩ := Finset.mem_sub.mp (hPsub hp)
    apply Finset.mem_sub.mpr
    refine ⟨a + u, ?_, v, hv, ?_⟩
    · rw [show 3 • A = A + 2 • A by simp [succ_nsmul, add_comm]]
      exact Finset.mem_add.mpr ⟨a, ha, u, hu, rfl⟩
    · rw [← hpval]
      abel
  have hAPcard : (A + P.carrier).card ≤
      freimanCoverCount K * P.carrier.card := by
    have hfive := pluennecke_ruzsa_int hA hsmall (m := 3) (n := 2)
    calc
      (A + P.carrier).card ≤ (3 • A - 2 • A).card :=
        Finset.card_le_card hAPsub
      _ ≤ K ^ 5 * A.card := by simpa using hfive
      _ ≤ K ^ 5 * (freimanCyclicCardFactor K * P.carrier.card) := by
        exact Nat.mul_le_mul_left _ hPlarge
      _ = freimanCoverCount K * P.carrier.card := by
        unfold freimanCoverCount
        ring
  obtain ⟨F, hFA, hFcard, hcover⟩ :=
    ruzsa_covering_int hPne hAPcard
  let C : GeneralizedAP := P.differenceAP.translateCoverAP F
  have hAC : A ⊆ C.carrier := by
    intro a ha
    have haCover := hcover ha
    obtain ⟨f, hf, d, hd, rfl⟩ := Finset.mem_add.mp haCover
    apply P.differenceAP.add_subset_translateCoverAP F
    exact Finset.mem_add.mpr
      ⟨f, hf, d, P.sub_carrier_subset_differenceAP hd, rfl⟩
  have hCrank : C.rank ≤ freimanRank K := by
    change P.rank + F.card ≤ freimanCyclicRank K + freimanCoverCount K
    exact Nat.add_le_add hPrank hFcard
  have hPupper : P.carrier.card ≤ K ^ 4 * A.card := by
    have hfour := pluennecke_ruzsa_int hA hsmall (m := 2) (n := 2)
    exact (Finset.card_le_card hPsub).trans (by simpa using hfour)
  have hCbox : C.boxCard ≤ 2 ^ (freimanRank K) * K ^ 4 * A.card := by
    calc
      C.boxCard ≤ 2 ^ (P.rank + F.card) * P.carrier.card :=
        P.boxCard_translateCoverAP_differenceAP_le hPproper F
      _ ≤ 2 ^ (freimanRank K) * P.carrier.card := by
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hCrank)
      _ ≤ 2 ^ (freimanRank K) * (K ^ 4 * A.card) :=
        Nat.mul_le_mul_left _ hPupper
      _ = 2 ^ (freimanRank K) * K ^ 4 * A.card := by ring
  exact ⟨C, hCrank, hAC, hCbox⟩

end Erdos587

end FreimanEstimates

section Erdos245_GAPTheory

open scoped BigOperators

namespace Erdos245Scratch

open Erdos587
open Erdos587.GeneralizedAP

/-- Homogeneous coordinates for a parameter of an affine GAP. -/
def homParam (Q : GeneralizedAP) (x : Q.Param) : Fin (Q.rank + 1) → ℤ :=
  Fin.cases 1 fun i ↦ (x i : ℕ)

@[simp] lemma homParam_zero (Q : GeneralizedAP) (x : Q.Param) :
    homParam Q x 0 = 1 := rfl

@[simp] lemma homParam_succ (Q : GeneralizedAP) (x : Q.Param) (i : Fin Q.rank) :
    homParam Q x i.succ = (x i : ℕ) := rfl

/-- Rational extension of the affine evaluation map in homogeneous
coordinates. -/
def gapEvalLinear (Q : GeneralizedAP) :
    (Fin (Q.rank + 1) → ℚ) →ₗ[ℚ] ℚ where
  toFun v := (Q.base : ℚ) * v 0 +
    ∑ i : Fin Q.rank, (Q.step i : ℚ) * v i.succ
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add,
      Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _hi
      ring

@[simp] lemma gapEvalLinear_homParam (Q : GeneralizedAP) (x : Q.Param) :
    gapEvalLinear Q (castVec (homParam Q x)) = (Q.eval x : ℚ) := by
  simp only [gapEvalLinear, LinearMap.coe_mk, AddHom.coe_mk, homParam_zero,
    homParam_succ, castVec_apply, eval, Int.cast_add, Int.cast_sum,
    Int.cast_mul, Int.cast_natCast, Int.cast_one, mul_one]
  apply congrArg ((Q.base : ℚ) + ·)
  apply Finset.sum_congr rfl
  intro i _hi
  ring

lemma gapEvalLinear_chainGenInt_zero
    (Q : GeneralizedAP) (x : ℕ → Q.Param) (n : ℕ) :
    gapEvalLinear Q
        (castVec (chainGenInt (fun k ↦ homParam Q (x k)) n 0)) =
      (Q.eval (x 0) : ℚ) := by
  rw [castVec_chainGenInt]
  simp [chainGen]

lemma gapEvalLinear_chainGenInt_succ
    (Q : GeneralizedAP) (x : ℕ → Q.Param) (n : ℕ) (j : Fin n) :
    gapEvalLinear Q
        (castVec (chainGenInt (fun k ↦ homParam Q (x k)) n j.succ)) =
      (Q.eval (x (j + 1)) : ℚ) - 2 * (Q.eval (x j) : ℚ) := by
  rw [castVec_chainGenInt]
  simp [chainGen]

lemma natAbs_homParam_le (Q : GeneralizedAP) (x : Q.Param)
    (j : Fin (Q.rank + 1)) :
    (homParam Q x j).natAbs ≤
      Fin.cases 1 (fun i ↦ 3 * (Q.length i + 1)) j := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp
  · simp only [homParam_succ, Fin.cases_succ, Int.natAbs_natCast]
    have hx : (x i : ℕ) ≤ Q.length i := Nat.le_of_lt_succ (x i).isLt
    omega

lemma natAbs_chainGenInt_homParam_le
    (Q : GeneralizedAP) (x : ℕ → Q.Param) (n : ℕ)
    (i : Fin (n + 1)) (j : Fin (Q.rank + 1)) :
    (chainGenInt (fun k ↦ homParam Q (x k)) n i j).natAbs ≤
      Fin.cases 1 (fun q ↦ 3 * (Q.length q + 1)) j := by
  refine Fin.cases ?_ (fun r ↦ ?_) i
  · exact natAbs_homParam_le Q (x 0) j
  · refine Fin.cases ?_ (fun q ↦ ?_) j
    · simp [chainGenInt, homParam]
    · simp only [chainGenInt]
      rw [Fin.cases_succ]
      change
        (((x (r + 1) q : ℕ) : ℤ) -
          2 * ((x r q : ℕ) : ℤ)).natAbs ≤
            3 * (Q.length q + 1)
      have hx1 : (x (r + 1) q : ℕ) ≤ Q.length q :=
        Nat.le_of_lt_succ (x (r + 1) q).isLt
      have hx0 : (x r q : ℕ) ≤ Q.length q :=
        Nat.le_of_lt_succ (x r q).isLt
      have habs :
          (((x (r + 1) q : ℕ) : ℤ) -
            2 * ((x r q : ℕ) : ℤ)).natAbs ≤
            (x (r + 1) q : ℕ) + 2 * (x r q : ℕ) := by
        calc
          _ ≤ (((x (r + 1) q : ℕ) : ℤ)).natAbs +
              (2 * ((x r q : ℕ) : ℤ)).natAbs := Int.natAbs_sub_le _ _
          _ = (x (r + 1) q : ℕ) + 2 * (x r q : ℕ) := by
            rw [Int.natAbs_mul]
            simp
      exact habs.trans (by omega)

lemma prod_chainBounds (Q : GeneralizedAP) :
    (∏ j : Fin (Q.rank + 1),
        Fin.cases 1 (fun i ↦ 3 * (Q.length i + 1)) j) =
      3 ^ Q.rank * Q.boxCard := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, one_mul, boxCard,
    Finset.prod_mul_distrib]
  simp

/-- If a string of positive elements of one GAP has no doubling gap, then
its last element is at most a fixed rank-dependent multiple of the first,
times the coefficient-box cardinality. -/
lemma gap_chain_diameter_bound
    (Q : GeneralizedAP) (x : ℕ → Q.Param) (n : ℕ)
    (hpos : ∀ i ≤ n, 0 ≤ Q.eval (x i))
    (hnogap : ∀ i < n, Q.eval (x (i + 1)) ≤ 2 * Q.eval (x i)) :
    (Q.eval (x n) : ℚ) ≤
      (((Q.rank + 1).factorial *
          (3 ^ Q.rank * Q.boxCard) : ℕ) : ℚ) *
        (Q.eval (x 0) : ℚ) := by
  let u : ℕ → Fin (Q.rank + 1) → ℤ := fun k ↦ homParam Q (x k)
  let B : Fin (Q.rank + 1) → ℕ :=
    Fin.cases 1 fun i ↦ 3 * (Q.length i + 1)
  have hB : ∀ j, 1 ≤ B j := by
    intro j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp [B]
    · simp only [B, Fin.cases_succ]
      omega
  obtain ⟨b, hb, hrel, hb0, hb0le⟩ :=
    exists_bounded_reduced_chain_coefficients u n 0
      (by intro i; simp [u]) B hB
      (by intro i j; exact natAbs_chainGenInt_homParam_le Q x n i j)
      (by intro j; exact natAbs_homParam_le Q (x n) j)
  have hevalrel :
      (Q.eval (x n) : ℚ) =
        ∑ i, b i *
          gapEvalLinear Q (castVec (chainGenInt u n i)) := by
    have h := congrArg (gapEvalLinear Q) hrel
    simpa [u] using h
  have hterm (i : Fin (n + 1)) :
      b i * gapEvalLinear Q (castVec (chainGenInt u n i)) ≤
        if i = 0 then b 0 * (Q.eval (x 0) : ℚ) else 0 := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [u, gapEvalLinear_chainGenInt_zero]
    · have hj : (j : ℕ) < n := j.isLt
      have hgap :
          (Q.eval (x (j + 1)) : ℚ) -
              2 * (Q.eval (x j) : ℚ) ≤ 0 := by
        exact_mod_cast sub_nonpos.mpr (hnogap j hj)
      have hmul := mul_nonpos_of_nonneg_of_nonpos (hb j.succ) hgap
      simpa [u, gapEvalLinear_chainGenInt_succ, Fin.succ_ne_zero] using hmul
  have hsum :
      (∑ i, b i * gapEvalLinear Q (castVec (chainGenInt u n i))) ≤
        b 0 * (Q.eval (x 0) : ℚ) := by
    calc
      _ ≤ ∑ i, if i = 0 then b 0 * (Q.eval (x 0) : ℚ) else 0 :=
        Finset.sum_le_sum fun i _hi ↦ hterm i
      _ = b 0 * (Q.eval (x 0) : ℚ) := by simp
  rw [← hevalrel] at hsum
  have hx0 : (0 : ℚ) ≤ (Q.eval (x 0) : ℚ) := by
    exact_mod_cast hpos 0 (Nat.zero_le n)
  calc
    (Q.eval (x n) : ℚ) ≤ b 0 * (Q.eval (x 0) : ℚ) := hsum
    _ ≤ (((Q.rank + 1).factorial * ∏ j, B j : ℕ) : ℚ) *
        (Q.eval (x 0) : ℚ) := mul_le_mul_of_nonneg_right hb0le hx0
    _ = (((Q.rank + 1).factorial *
          (3 ^ Q.rank * Q.boxCard) : ℕ) : ℚ) *
        (Q.eval (x 0) : ℚ) := by rw [prod_chainBounds]

end Erdos245Scratch

end Erdos245_GAPTheory

section Erdos899

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 899.
https://www.erdosproblems.com/forum/thread/899

Informal authors:
- Imre Ruzsa

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos899.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/899.lean
-/


/-
# Erdős Problem 899

Ruzsa's translate-layer proof that an infinite set of natural numbers of
asymptotic density zero has an unbounded positive-difference/count ratio.

The mathematical proof and a detailed formalization guide are in `tex/899.tex`.
-/

open Filter Set
open scoped Pointwise Topology

namespace Erdos899

/- ## Finite-window counting and increasing enumerations -/

/-- The finite window consisting of the elements of `S` in `[1, N]`. -/
noncomputable def window (S : Set ℕ) (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 N).filter (fun n ↦ n ∈ S)

/-- The number of elements of `S` in the natural-number interval `[1, N]`. -/
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  (window S N).card

@[simp] lemma mem_window {S : Set ℕ} {N x : ℕ} :
    x ∈ window S N ↔ 1 ≤ x ∧ x ≤ N ∧ x ∈ S := by
  classical
  simp [window, and_assoc]

lemma countIn_eq_ncard (S : Set ℕ) (N : ℕ) :
    countIn S N = (S ∩ Icc 1 N).ncard := by
  classical
  rw [countIn, window, ← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_left_comm, and_comm]

lemma countIn_mono_set {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    countIn S N ≤ countIn T N := by
  classical
  unfold countIn window
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hST hn.2⟩

lemma countIn_mono_nat (S : Set ℕ) : Monotone (countIn S) := by
  intro M N hMN
  classical
  unfold countIn window
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hMN⟩, hn.2⟩

/-- The increasing enumeration of an infinite set of natural numbers. -/
noncomputable def enumerate (S : Set ℕ) : ℕ → ℕ :=
  Nat.nth (fun n ↦ n ∈ S)

lemma enumerate_strictMono {S : Set ℕ} (hS : S.Infinite) :
    StrictMono (enumerate S) :=
  Nat.nth_strictMono hS

lemma enumerate_mem {S : Set ℕ} (hS : S.Infinite) (i : ℕ) : enumerate S i ∈ S :=
  Nat.nth_mem_of_infinite hS i

lemma range_enumerate {S : Set ℕ} (hS : S.Infinite) : Set.range (enumerate S) = S :=
  Nat.range_nth_of_infinite hS

lemma countIn_enumerate_ge {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) (k : ℕ) :
    k + 1 ≤ countIn S (enumerate S k) := by
  classical
  let F : Fin (k + 1) → ℕ := fun i ↦ enumerate S i
  have hF_inj : Function.Injective F := fun i j hij ↦ by
    apply Fin.ext
    exact (enumerate_strictMono hS).injective hij
  have hF_mem (i : Fin (k + 1)) : F i ∈ S ∩ Icc 1 (enumerate S k) := by
    have hi : i.1 ≤ k := by omega
    exact ⟨enumerate_mem hS i, hpos (enumerate_mem hS i),
      (enumerate_strictMono hS).monotone hi⟩
  rw [countIn_eq_ncard]
  calc
    k + 1 = (Set.range F).ncard := by
      rw [Set.ncard_range_of_injective hF_inj]
      simp
    _ ≤ (S ∩ Icc 1 (enumerate S k)).ncard := by
      apply Set.ncard_le_ncard (ht := (Set.finite_Icc 1 (enumerate S k)).subset inter_subset_right)
      rintro x ⟨i, rfl⟩
      exact hF_mem i

lemma countIn_tendsto_atTop {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) :
    Tendsto (countIn S) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨enumerate S k, ?_⟩
  intro N hN
  exact (Nat.le_succ k).trans
    ((countIn_enumerate_ge hS hpos k).trans (countIn_mono_nat S hN))

lemma eventually_countIn_pos {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) :
    ∀ᶠ N in atTop, 0 < countIn S N := by
  exact (countIn_tendsto_atTop hS hpos).eventually (eventually_gt_atTop 0)

lemma density_eventually_mul_lt (a : ℕ → ℕ)
    (hden : Tendsto (fun N ↦ (a N : ℝ) / N) atTop (𝓝 0))
    {M : ℕ} (hM : 0 < M) :
    ∀ᶠ N in atTop, M * a N < N := by
  have hratio : ∀ᶠ N in atTop, (a N : ℝ) / N < 1 / (M : ℝ) :=
    hden.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hcross : (a N : ℝ) * M < (N : ℝ) := by
    simpa only [one_mul] using (div_lt_div_iff₀ hNr hMr).mp hN
  have hcross' : (M : ℝ) * (a N : ℝ) < (N : ℝ) := by
    simpa only [mul_comm] using hcross
  exact_mod_cast hcross'

end Erdos899

end Erdos899

section Erdos245_Counting

open Filter Set
open scoped Pointwise Topology BigOperators

namespace Erdos245Scratch

open Erdos899
open Erdos587

lemma countIn_enumerate_eq {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Ici 1) (i : ℕ) :
    countIn S (enumerate S i) = i + 1 := by
  classical
  let F : Finset ℕ :=
    (Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) ↦ enumerate S j.1)
  have hFinj : Function.Injective
      (fun j : Fin (i + 1) ↦ enumerate S j.1) :=
    (enumerate_strictMono hS).injective.comp Fin.val_injective
  have hFcard : F.card = i + 1 := by
    change ((Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) ↦ enumerate S j.1)).card = i + 1
    calc
      _ = (Finset.univ : Finset (Fin (i + 1))).card :=
        Finset.card_image_of_injective _ hFinj
      _ = i + 1 := by simp
  have hFeq : F = window S (enumerate S i) := by
    ext x
    change x ∈ (Finset.univ : Finset (Fin (i + 1))).image
      (fun j : Fin (i + 1) ↦ enumerate S j.1) ↔
        x ∈ window S (enumerate S i)
    constructor
    · intro hx
      obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hx
      have hji : j.1 ≤ i := by omega
      exact mem_window.mpr ⟨hpos (enumerate_mem hS j),
        (enumerate_strictMono hS).monotone hji,
        enumerate_mem hS j⟩
    · intro hx
      have hxS := (mem_window.mp hx).2.2
      rw [← range_enumerate hS] at hxS
      obtain ⟨j, rfl⟩ := hxS
      have hji : j ≤ i :=
        (enumerate_strictMono hS).le_iff_le.mp (mem_window.mp hx).2.1
      apply Finset.mem_image.mpr
      exact ⟨⟨j, by omega⟩, Finset.mem_univ _, rfl⟩
  rw [countIn, ← hFeq, hFcard]

lemma enumerate_le_iff_lt_countIn {S : Set ℕ} (hS : S.Infinite)
    (hpos : S ⊆ Ici 1) (i N : ℕ) :
    enumerate S i ≤ N ↔ i < countIn S N := by
  constructor
  · intro hiN
    have hmono := countIn_mono_nat S hiN
    rw [countIn_enumerate_eq hS hpos i] at hmono
    omega
  · intro hicount
    by_contra hnot
    have hNlt : N < enumerate S i := Nat.lt_of_not_ge hnot
    have hsub : window S N ⊂ window S (enumerate S i) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro x hx
        apply mem_window.mpr
        have hx' := mem_window.mp hx
        exact ⟨hx'.1, hx'.2.1.trans hNlt.le, hx'.2.2⟩
      · intro heq
        have hemem : enumerate S i ∈ window S (enumerate S i) :=
          mem_window.mpr ⟨hpos (enumerate_mem hS i), le_rfl,
            enumerate_mem hS i⟩
        rw [← heq] at hemem
        exact (Nat.not_le_of_gt hNlt) (mem_window.mp hemem).2.1
    have hcardlt := Finset.card_lt_card hsub
    change countIn S N < countIn S (enumerate S i) at hcardlt
    rw [countIn_enumerate_eq hS hpos i] at hcardlt
    omega

lemma window_add_subset (S : Set ℕ) (N : ℕ) :
    window S N + window S N ⊆ window (S + S) (2 * N) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  have hx' := mem_window.mp hx
  have hy' := mem_window.mp hy
  apply mem_window.mpr
  exact ⟨by omega, by omega, Set.add_mem_add hx'.2.2 hy'.2.2⟩

/-- Density zero forces arbitrarily large scales at which doubling the
cutoff multiplies the counting function by at most four. -/
lemma frequently_countIn_two_mul_le_four
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1)
    (hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N) atTop (nhds 0)) :
    ∃ᶠ N in atTop, countIn S (2 * N) ≤ 4 * countIn S N := by
  by_contra hfreq
  have hgrow : ∀ᶠ N in atTop, 4 * countIn S N < countIn S (2 * N) := by
    filter_upwards [(Filter.not_frequently.mp hfreq)] with N hN
    omega
  have hdense : ∀ᶠ N in atTop, 2 * countIn S N < N :=
    density_eventually_mul_lt (countIn S) hden (by omega)
  have hpositive : ∀ᶠ N in atTop, 0 < countIn S N :=
    eventually_countIn_pos hS hpos
  obtain ⟨L, hL⟩ := eventually_atTop.1 (hgrow.and (hdense.and hpositive))
  let N₀ := max 1 L
  have hN₀L : L ≤ N₀ := le_max_right _ _
  have hN₀pos : 0 < N₀ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have haN₀ : 0 < countIn S N₀ := (hL N₀ hN₀L).2.2
  have hiter : ∀ t : ℕ,
      4 ^ t * countIn S N₀ ≤ countIn S (2 ^ t * N₀) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hscale : L ≤ 2 ^ t * N₀ := by
          have hp : 1 ≤ 2 ^ t := by
            have : 0 < 2 ^ t := pow_pos (by omega) _
            omega
          calc
            L ≤ N₀ := hN₀L
            _ = 1 * N₀ := by simp
            _ ≤ 2 ^ t * N₀ := Nat.mul_le_mul_right N₀ hp
        have hstep := (hL (2 ^ t * N₀) hscale).1
        calc
          4 ^ (t + 1) * countIn S N₀ =
              4 * (4 ^ t * countIn S N₀) := by ring
          _ ≤ 4 * countIn S (2 ^ t * N₀) :=
            Nat.mul_le_mul_left 4 ih
          _ ≤ countIn S (2 * (2 ^ t * N₀)) := hstep.le
          _ = countIn S (2 ^ (t + 1) * N₀) := by ring_nf
  have hscale : L ≤ 2 ^ N₀ * N₀ := by
    have hp : 1 ≤ 2 ^ N₀ := by
      have : 0 < 2 ^ N₀ := pow_pos (by omega) _
      omega
    calc
      L ≤ N₀ := hN₀L
      _ = 1 * N₀ := by simp
      _ ≤ 2 ^ N₀ * N₀ := Nat.mul_le_mul_right N₀ hp
  have hsmall := (hL (2 ^ N₀ * N₀) hscale).2.1
  have hlower := hiter N₀
  have hpow : 2 ^ N₀ * N₀ < 4 ^ N₀ := by
    calc
      2 ^ N₀ * N₀ < 2 ^ N₀ * 2 ^ N₀ :=
        (Nat.mul_lt_mul_left (pow_pos (by omega) _)).2 N₀.lt_two_pow_self
      _ = 4 ^ N₀ := by rw [← Nat.mul_pow]
  have hfour : 4 ^ N₀ ≤ countIn S (2 ^ N₀ * N₀) := by
    calc
      4 ^ N₀ = 4 ^ N₀ * 1 := by simp
      _ ≤ 4 ^ N₀ * countIn S N₀ :=
        Nat.mul_le_mul_left _ haN₀
      _ ≤ countIn S (2 ^ N₀ * N₀) := hlower
  have hcontra : 2 * 4 ^ N₀ < 2 ^ N₀ * N₀ := by
    exact (Nat.mul_le_mul_left 2 hfour).trans_lt hsmall
  omega

end Erdos245Scratch

end Erdos245_Counting

section Erdos245_Gap

open Filter Set
open scoped Pointwise Topology BigOperators

namespace Erdos245Scratch

open Erdos899
open Erdos587
open Erdos587.GeneralizedAP

/-- Under an eventual sumset ratio strictly below three, a positive
density-zero set has doubling gaps arbitrarily far out in its increasing
enumeration. -/
lemma exists_doubling_gap_of_eventually_three
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1)
    (hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N) atTop (nhds 0))
    (hsum : ∀ᶠ N in atTop,
      countIn (S + S) N < 3 * countIn S N) :
    ∀ s : ℕ, ∃ i ≥ s,
      2 * enumerate S i < enumerate S (i + 1) := by
  intro s
  by_contra hgap
  push Not at hgap
  have hnogap : ∀ i ≥ s,
      enumerate S (i + 1) ≤ 2 * enumerate S i := by
    intro i hi
    exact hgap i hi
  let R := freimanRank 12
  let C := freimanSizeFactor 12
  let D := (R + 1).factorial * (3 ^ R * C) * enumerate S s
  have hdenseD : ∀ᶠ M in atTop,
      (D + 1) * countIn S M < M :=
    density_eventually_mul_lt (countIn S) hden (by omega)
  obtain ⟨L, hL⟩ := eventually_atTop.1 hdenseD
  have hlarge : ∀ᶠ N in atTop,
      countIn S L + s + 2 < countIn S N :=
    (countIn_tendsto_atTop hS hpos).eventually
      (eventually_gt_atTop (countIn S L + s + 2))
  obtain ⟨Lsum, hLsum⟩ := eventually_atTop.1 hsum
  have hsum2 : ∀ᶠ N in atTop,
      countIn (S + S) (2 * N) < 3 * countIn S (2 * N) :=
    eventually_atTop.2 ⟨Lsum, fun N hN ↦ hLsum (2 * N) (by omega)⟩
  obtain ⟨N, hstop, hsumN, hklarge⟩ :=
    ((frequently_countIn_two_mul_le_four hS hpos hden).and_eventually
      (hsum2.and hlarge)).exists
  let X := window S N
  let k := countIn S N
  have hsk : s < k := by
    dsimp [k]
    omega
  have hkpos : 0 < k := hsk.trans_le' (Nat.zero_le s)
  have hXcard : X.card = k := rfl
  have hXne : X.Nonempty := Finset.card_pos.mp (by simpa [hXcard] using hkpos)
  have hXsmall : (X + X).card ≤ 12 * X.card := by
    have hsub := Finset.card_le_card (window_add_subset S N)
    change (X + X).card ≤ countIn (S + S) (2 * N) at hsub
    change countIn S (2 * N) ≤ 4 * k at hstop
    change countIn (S + S) (2 * N) < 3 * countIn S (2 * N) at hsumN
    change X.card = k at hXcard
    omega
  let Xint := natToIntFinset X
  have hXintne : Xint.Nonempty := natToIntFinset_nonempty.mpr hXne
  have hXintsmall : (Xint + Xint).card ≤ 12 * Xint.card := by
    change (natToIntFinset X + natToIntFinset X).card ≤
      12 * (natToIntFinset X).card
    rw [← natToIntFinset_add, card_natToIntFinset,
      card_natToIntFinset]
    exact hXsmall
  obtain ⟨Q, hQrank, hQsub, hQcard⟩ :=
    exists_GAP_cover_of_small_doubling Xint hXintne 12
      (by omega) hXintsmall
  have hprefix (j : ℕ) (hj : j < k) : enumerate S j ∈ X := by
    apply mem_window.mpr
    exact ⟨hpos (enumerate_mem hS j),
      (enumerate_le_iff_lt_countIn hS hpos j N).mpr (by simpa [k] using hj),
      enumerate_mem hS j⟩
  have hparam (j : ℕ) (hj : j < k) :
      ∃ q : Q.Param, Q.eval q = (enumerate S j : ℤ) := by
    apply Q.mem_carrier_iff.mp
    apply hQsub
    exact natCast_mem_natToIntFinset.mpr (hprefix j hj)
  let x : ℕ → Q.Param := fun j ↦
    if hj : j < k then Classical.choose (hparam j hj) else default
  have hx (j : ℕ) (hj : j < k) :
      Q.eval (x j) = (enumerate S j : ℤ) := by
    simp only [x, dif_pos hj]
    exact Classical.choose_spec (hparam j hj)
  let n := k - 1 - s
  let y : ℕ → Q.Param := fun j ↦ x (s + j)
  have hsn : s + n = k - 1 := by
    dsimp [n]
    omega
  have hy (j : ℕ) (hj : j ≤ n) :
      Q.eval (y j) = (enumerate S (s + j) : ℤ) := by
    apply hx
    omega
  have hypos : ∀ j ≤ n, 0 ≤ Q.eval (y j) := by
    intro j hj
    rw [hy j hj]
    exact Int.natCast_nonneg _
  have hynogap : ∀ j < n,
      Q.eval (y (j + 1)) ≤ 2 * Q.eval (y j) := by
    intro j hj
    rw [hy (j + 1) (by omega), hy j hj.le]
    exact_mod_cast hnogap (s + j) (by omega)
  have hdiam := gap_chain_diameter_bound Q y n hypos hynogap
  have hdiamNat :
      enumerate S (k - 1) ≤
        ((Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard)) *
          enumerate S s := by
    have hy0 : Q.eval (y 0) = (enumerate S s : ℤ) := by
      simpa using hy 0 (Nat.zero_le n)
    have hyn : Q.eval (y n) = (enumerate S (k - 1) : ℤ) := by
      simpa [hsn] using hy n le_rfl
    rw [hyn, hy0] at hdiam
    exact_mod_cast hdiam
  have hcoef :
      (Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard) ≤
        (R + 1).factorial * (3 ^ R * (C * k)) := by
    have hfac : (Q.rank + 1).factorial ≤ (R + 1).factorial := by
      apply Nat.factorial_le
      dsimp [R]
      omega
    have hpow : 3 ^ Q.rank ≤ 3 ^ R := by
      apply Nat.pow_le_pow_right (by omega)
      simpa [R] using hQrank
    have hcard : Q.boxCard ≤ C * k := by
      rw [card_natToIntFinset] at hQcard
      change Q.boxCard ≤ C * X.card at hQcard
      rwa [hXcard] at hQcard
    exact Nat.mul_le_mul hfac (Nat.mul_le_mul hpow hcard)
  have hlinear : enumerate S (k - 1) ≤ D * k := by
    calc
      enumerate S (k - 1) ≤
          ((Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard)) *
            enumerate S s := hdiamNat
      _ ≤ ((R + 1).factorial * (3 ^ R * (C * k))) *
            enumerate S s := Nat.mul_le_mul_right _ hcoef
      _ = D * k := by simp only [D]; ring
  have hlastL : L < enumerate S (k - 1) := by
    have hcountL : countIn S L < k := by
      dsimp [k] at hklarge ⊢
      omega
    have hnot : ¬(k - 1 < countIn S L) := by omega
    exact Nat.lt_of_not_ge fun hle ↦
      hnot ((enumerate_le_iff_lt_countIn hS hpos (k - 1) L).mp hle)
  have hdenseLast := hL (enumerate S (k - 1)) hlastL.le
  rw [countIn_enumerate_eq hS hpos (k - 1)] at hdenseLast
  have hkpred : k - 1 + 1 = k := by omega
  rw [hkpred] at hdenseLast
  rw [add_mul, one_mul] at hdenseLast
  omega

end Erdos245Scratch

end Erdos245_Gap

section Erdos245_Inverse

open Filter Set
open scoped Pointwise Topology BigOperators

namespace Erdos245Scratch

open Erdos899
open Erdos587

lemma window_add_eq_at_doubling_gap
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1) (i : ℕ)
    (hgap : 2 * enumerate S i < enumerate S (i + 1)) :
    window S (enumerate S i) + window S (enumerate S i) =
      window (S + S) (2 * enumerate S i) := by
  classical
  apply Finset.Subset.antisymm
  · exact window_add_subset S (enumerate S i)
  · intro z hz
    have hz' := mem_window.mp hz
    have hzle := hz'.2.1
    obtain ⟨x, hxS, y, hyS, rfl⟩ := hz'.2.2
    have hxle : x ≤ enumerate S i := by
      by_contra hx
      have hxgt : enumerate S i < x := Nat.lt_of_not_ge hx
      rw [← range_enumerate hS] at hxS
      obtain ⟨j, rfl⟩ := hxS
      have hij : i < j := (enumerate_strictMono hS).lt_iff_lt.mp hxgt
      have hnext : enumerate S (i + 1) ≤ enumerate S j :=
        (enumerate_strictMono hS).monotone (by omega)
      have htooLarge : 2 * enumerate S i < enumerate S j + y :=
        hgap.trans_le (hnext.trans (Nat.le_add_right _ _))
      exact (Nat.not_lt_of_ge hzle) htooLarge
    have hyle : y ≤ enumerate S i := by
      by_contra hy
      have hygt : enumerate S i < y := Nat.lt_of_not_ge hy
      rw [← range_enumerate hS] at hyS
      obtain ⟨j, rfl⟩ := hyS
      have hij : i < j := (enumerate_strictMono hS).lt_iff_lt.mp hygt
      have hnext : enumerate S (i + 1) ≤ enumerate S j :=
        (enumerate_strictMono hS).monotone (by omega)
      have htooLarge : 2 * enumerate S i < x + enumerate S j :=
        hgap.trans_le (hnext.trans (Nat.le_add_left _ _))
      exact (Nat.not_lt_of_ge hzle) htooLarge
    exact Finset.mem_add.mpr ⟨x,
      mem_window.mpr ⟨hpos hxS, hxle, hxS⟩, y,
      mem_window.mpr ⟨hpos hyS, hyle, hyS⟩, rfl⟩

/-- A rationally separated eventual ratio below three is incompatible with
zero density.  The integer `m` records the reciprocal separation from three. -/
lemma not_eventually_scaled_sum_lt_three
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1)
    (hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N) atTop (nhds 0))
    (m : ℕ) (hm : 0 < m)
    (hscaled : ∀ᶠ N in atTop,
      m * countIn (S + S) N < (3 * m - 1) * countIn S N) : False := by
  have hsum : ∀ᶠ N in atTop,
      countIn (S + S) N < 3 * countIn S N := by
    filter_upwards [hscaled] with N hN
    apply (Nat.mul_lt_mul_left hm).mp
    calc
      m * countIn (S + S) N <
          (3 * m - 1) * countIn S N := hN
      _ ≤ (3 * m) * countIn S N :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = m * (3 * countIn S N) := by ring
  let e := enumerate S
  let D := e 0 + 2 * e 1
  have hdenseD : ∀ᶠ N in atTop,
      (D + 1) * countIn S N < N :=
    density_eventually_mul_lt (countIn S) hden (by omega)
  obtain ⟨Lden, hLden⟩ := eventually_atTop.1 hdenseD
  obtain ⟨Lscaled, hLscaled⟩ := eventually_atTop.1 hscaled
  let s := max (max Lden Lscaled) (4 * m)
  obtain ⟨i, his, hgap⟩ :=
    exists_doubling_gap_of_eventually_three hS hpos hden hsum s
  let k := i + 1
  let X := window S (e i)
  have hie : i ≤ e i := (enumerate_strictMono hS).id_le i
  have hLdeni : Lden ≤ e i := by
    dsimp [s] at his
    omega
  have hLscaledi : Lscaled ≤ 2 * e i := by
    dsimp [s] at his
    omega
  have hk4m : 4 * m ≤ k := by
    dsimp [s, k] at his ⊢
    omega
  have hkpos : 0 < k := by simp [k]
  have hXcard : X.card = k := by
    change countIn S (enumerate S i) = i + 1
    exact countIn_enumerate_eq hS hpos i
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hscaledGap := hLscaled (2 * e i) hLscaledi
  have hsumcard : (X + X).card = countIn (S + S) (2 * e i) := by
    change (window S (enumerate S i) + window S (enumerate S i)).card = _
    rw [window_add_eq_at_doubling_gap hS hpos i hgap]
    rfl
  have hcount2 : countIn S (2 * e i) = k := by
    have hlower : k ≤ countIn S (2 * e i) := by
      dsimp [k, e]
      rw [← countIn_enumerate_eq hS hpos i]
      exact countIn_mono_nat S (by omega)
    have hnot : ¬(i + 1 < countIn S (2 * e i)) := by
      intro hlt
      have hnextle :=
        (enumerate_le_iff_lt_countIn hS hpos (i + 1) (2 * e i)).mpr hlt
      dsimp [e] at hgap hnextle
      omega
    dsimp [k]
    omega
  have hscaledX : m * (X + X).card < (3 * m - 1) * k := by
    rw [hsumcard]
    simpa only [hcount2] using hscaledGap
  have hupper : (3 * m - 1) * k ≤ m * (3 * k - 4) := by
    calc
      (3 * m - 1) * k = 3 * m * k - k := by
        rw [Nat.sub_mul]
        simp
      _ ≤ 3 * m * k - 4 * m := Nat.sub_le_sub_left hk4m _
      _ = m * (3 * k - 4) := by
        rw [Nat.mul_sub_left_distrib]
        congr 1 <;> ring
  have hsmalllt : (X + X).card < 3 * k - 4 := by
    apply (Nat.mul_lt_mul_left hm).mp
    exact hscaledX.trans_le hupper
  have hsmall : (X + X).card ≤ 3 * X.card - 4 := by
    rw [hXcard]
    exact hsmalllt.le
  have hk2 : 2 ≤ X.card := by
    rw [hXcard]
    have : 4 ≤ 4 * m := by omega
    omega
  obtain ⟨a, d, L, hd, hL, hXAP⟩ :=
    exists_short_natAP_of_three_k_minus_four hXne hk2 hsmall
  have hmem (j : ℕ) (hj : j ≤ i) : e j ∈ X := by
    apply mem_window.mpr
    exact ⟨hpos (enumerate_mem hS j),
      (enumerate_strictMono hS).monotone hj,
      enumerate_mem hS j⟩
  obtain ⟨j0, hj0L, hj0⟩ :=
    Erdos13Additive.mem_natAP.mp (hXAP (hmem 0 (Nat.zero_le i)))
  obtain ⟨j1, hj1L, hj1⟩ :=
    Erdos13Additive.mem_natAP.mp (hXAP (hmem 1 (by omega)))
  obtain ⟨ji, hjiL, hji⟩ :=
    Erdos13Additive.mem_natAP.mp (hXAP (hmem i le_rfl))
  have he01 : e 0 < e 1 := enumerate_strictMono hS (by omega)
  have hj01 : j0 < j1 := by
    by_contra hnot
    have hjle : j1 ≤ j0 := Nat.le_of_not_gt hnot
    have hmul := Nat.mul_le_mul_left d hjle
    have he10 : e 1 ≤ e 0 := by
      rw [← hj1, ← hj0]
      exact Nat.add_le_add_left hmul a
    exact (Nat.not_le_of_gt he01) he10
  have hdle : d ≤ e 1 := by
    have hmul := Nat.mul_le_mul_left d (show j0 + 1 ≤ j1 by omega)
    calc
      d ≤ a + d * j0 + d := by omega
      _ = a + d * (j0 + 1) := by ring
      _ ≤ a + d * j1 := Nat.add_le_add_left hmul a
      _ = e 1 := hj1
  have hale : a ≤ e 0 := by omega
  have hji2k : ji ≤ 2 * k := by
    rw [hXcard] at hL
    omega
  have hdji : d * ji ≤ e 1 * (2 * k) :=
    Nat.mul_le_mul hdle hji2k
  have hlinear : e i ≤ D * k := by
    calc
      e i = a + d * ji := hji.symm
      _ ≤ e 0 + e 1 * (2 * k) := Nat.add_le_add hale hdji
      _ ≤ (e 0 + 2 * e 1) * k := by
        have he0mul : e 0 ≤ e 0 * k := by
          simpa only [mul_one] using Nat.mul_le_mul_left (e 0) (show 1 ≤ k by omega)
        calc
          e 0 + e 1 * (2 * k) = e 0 + (2 * e 1) * k := by ring
          _ ≤ e 0 * k + (2 * e 1) * k := Nat.add_le_add_right he0mul _
          _ = (e 0 + 2 * e 1) * k := by ring
      _ = D * k := rfl
  have hdenseLast := hLden (e i) hLdeni
  change (D + 1) * countIn S (enumerate S i) < e i at hdenseLast
  rw [countIn_enumerate_eq hS hpos i] at hdenseLast
  change (D + 1) * k < e i at hdenseLast
  rw [add_mul, one_mul] at hdenseLast
  omega

end Erdos245Scratch

end Erdos245_Inverse

section Erdos245_Core

open Filter Set
open scoped Pointwise Topology

namespace Erdos245Scratch

open Erdos899

lemma countIn_inter_Ici_one (A : Set ℕ) (N : ℕ) :
    countIn (A ∩ Ici 1) N = countIn A N := by
  rw [countIn_eq_ncard, countIn_eq_ncard]
  congr 1
  ext n
  simp only [mem_inter_iff, mem_Ici, mem_Icc]
  tauto

/-- The affirmative resolution of Erdős Problem 245. -/
theorem erdos_245 :
    ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N ↦ (A ∩ Icc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (nhds 0) →
      3 ≤ atTop.limsup
        fun N : ℝ ↦ ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
          (A ∩ Icc 1 ⌊N⌋₊).ncard := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _htrue A hA hdenReal
    let S := A ∩ Ici 1
    have hS : S.Infinite := by
      have hdiff : (A \ {0}).Infinite := hA.sdiff (Set.finite_singleton 0)
      have heq : A \ {0} = S := by
        ext n
        simp [S, Nat.one_le_iff_ne_zero]
      rwa [heq] at hdiff
    have hpos : S ⊆ Ici 1 := inter_subset_right
    have hcount (N : ℕ) : countIn S N = countIn A N := by
      simpa [S] using countIn_inter_Ici_one A N
    have hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N)
        atTop (nhds 0) := by
      have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have hcomp := hdenReal.comp hcast
      change Tendsto
        (fun n : ℕ ↦
          (A ∩ Icc 1 ⌊(n : ℝ)⌋₊ |>.ncard : ℝ) / (n : ℝ))
        atTop (nhds 0) at hcomp
      simpa only [Nat.floor_natCast, ← countIn_eq_ncard, hcount] using hcomp
    let ratio : ℝ → EReal := fun N ↦
      ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
        (A ∩ Icc 1 ⌊N⌋₊).ncard
    change 3 ≤ atTop.limsup ratio
    by_contra hnot
    have hlim : atTop.limsup ratio < (3 : EReal) := lt_of_not_ge hnot
    obtain ⟨c, hlimc, hc3E⟩ := EReal.lt_iff_exists_real_btwn.mp hlim
    have hc3 : c < 3 := by
      change (c : EReal) < ((3 : ℝ) : EReal) at hc3E
      exact EReal.coe_lt_coe_iff.mp hc3E
    obtain ⟨m, hm, hminv⟩ :=
      Real.exists_nat_pos_inv_lt (sub_pos.mpr hc3)
    have hcb : c < 3 - (m : ℝ)⁻¹ := by linarith
    have hlimb : atTop.limsup ratio <
        (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) :=
      hlimc.trans (EReal.coe_lt_coe hcb)
    have hratioReal : ∀ᶠ N in atTop,
        ratio N < (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt hlimb
    have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hratioNat : ∀ᶠ n : ℕ in atTop,
        (countIn (A + A) n : EReal) / countIn A n <
          (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) := by
      have hcomp := hcast.eventually hratioReal
      simpa only [ratio, Nat.floor_natCast, ← countIn_eq_ncard] using hcomp
    have hSS : S + S ⊆ A + A :=
      Set.add_subset_add inter_subset_left inter_subset_left
    have hpositive : ∀ᶠ n in atTop, 0 < countIn S n :=
      eventually_countIn_pos hS hpos
    have hscaled : ∀ᶠ n in atTop,
        m * countIn (S + S) n < (3 * m - 1) * countIn S n := by
      filter_upwards [hratioNat, hpositive] with n hratio hnpos
      have hratio' :
          (((countIn (A + A) n : ℝ) : EReal) /
              ((countIn A n : ℝ) : EReal)) <
            (((3 : ℝ) - (m : ℝ)⁻¹ : ℝ) : EReal) := by
        simpa only [EReal.coe_coe_eq_natCast] using hratio
      have hratioℝ :
          (countIn (A + A) n : ℝ) / (countIn A n : ℝ) <
            3 - (m : ℝ)⁻¹ := by
        rw [← EReal.coe_div, EReal.coe_lt_coe_iff] at hratio'
        exact hratio'
      have hApos : 0 < (countIn A n : ℝ) := by
        rw [← hcount]
        exact_mod_cast hnpos
      have hcross : (countIn (A + A) n : ℝ) <
          (3 - (m : ℝ)⁻¹) * countIn A n :=
        (div_lt_iff₀ hApos).mp hratioℝ
      have hsubcount : countIn (S + S) n ≤ countIn (A + A) n :=
        countIn_mono_set hSS n
      have hmℝ : 0 < (m : ℝ) := by exact_mod_cast hm
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmℝ
      have hid :
          (m : ℝ) * (3 - (m : ℝ)⁻¹) = ((3 * m - 1 : ℕ) : ℝ) := by
        rw [mul_sub, mul_inv_cancel₀ hmne]
        rw [Nat.cast_sub (by omega : 1 ≤ 3 * m), Nat.cast_mul]
        norm_num
        ring
      have hscaledℝ :
          (m : ℝ) * countIn (S + S) n <
            ((3 * m - 1 : ℕ) : ℝ) * countIn S n := by
        calc
          (m : ℝ) * countIn (S + S) n ≤
              (m : ℝ) * countIn (A + A) n := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsubcount) hmℝ.le
          _ < (m : ℝ) *
              ((3 - (m : ℝ)⁻¹) * countIn A n) :=
            mul_lt_mul_of_pos_left hcross hmℝ
          _ = ((3 * m - 1 : ℕ) : ℝ) * countIn S n := by
            rw [← mul_assoc, hid, hcount]
      exact_mod_cast hscaledℝ
    exact (not_eventually_scaled_sum_lt_three hS hpos hden m hm hscaled).elim
  · intro _h
    trivial


end Erdos245Scratch

end Erdos245_Core

theorem OMA.solution : type_of% @Erdos245.erdos_245 := by
  exact Erdos245Scratch.erdos_245
