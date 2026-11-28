import OMAReductions.R_Green92_green_92_variants_chase_lower_R1
import Mathlib
/- Adapted and condensed from OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, TraceReconstruction. The fixed initial pair suffices; the last testing argument changes to the registered deletion-mask model.
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
open Real renaming sqrt → Z0
open Real renaming exp → Z1
open Finset renaming sum_congr → Z2
open Finset renaming mul_sum → Z3
open Set renaming Ioo → Z4
open Finset renaming range → Z5
open Set renaming Icc → Z6
open Finset renaming sum_le_sum → Z7
open Real renaming log → Z8
open Filter renaming atTop → Z9
open Fintype renaming card → Z10
open Finset renaming sum_nonneg → Z11
open Set renaming Ioc → Z12
open Real renaming sq_sqrt → Z13
open Finset renaming sum_add_distrib → Z14
open Fin renaming cons → Z15
open Finset renaming univ → Z16
open Finset renaming sum_comm → Z17
open Equiv renaming swap → Z18
open Nat renaming cast_nonneg → Z19
open List renaming ofFn → Z20
open Finset renaming mem_univ → Z21
open Fin renaming last → Z22
open Nat renaming cast_add → Z23
open Real renaming sqrt_le_sqrt → Z24
open Nat renaming cast_one → Z25
open Fintype renaming card_fin → Z26
open Finset renaming sum_filter → Z27
open Function renaming Injective → Z28
open AddMonoidAlgebra renaming single → Z29
open Finset renaming prod_mul_distrib → Z30
open Finset renaming Iic → Z31
open Fintype renaming sum_prod_type → Z32
open Finset renaming sum_mul → Z33
open Fin renaming ext → Z34
open Nat renaming cast_mul → Z35
open Real renaming sqrt_nonneg → Z36
open Finset renaming prod_nonneg → Z37
open Fin renaming cases → Z38
open Finset renaming sum_sub_distrib → Z39
open Finset renaming sum_le_sum_of_subset_of_nonneg → Z40
open AddMonoidAlgebra renaming coeff_single → Z41
open Finsupp renaming single_apply → Z42
open Fintype renaming prod_sum → Z43
open Nat renaming choose_eq_zero_of_lt → Z44
open Finset renaming prod_le_prod → Z45
open Fin renaming consEquiv → Z46
open Nat renaming cast_sub → Z47
open Finset renaming card_univ → Z48
open Real renaming exp_nonneg → Z49
open Real renaming exp_add → Z50
open Nat renaming mul_le_mul_right → Z51
open Nat renaming cast_ofNat → Z52
open Fin renaming prod_univ_succ → Z53
open Fin renaming cons_zero → Z54
open Fin renaming cons_succ → Z55
open Finset renaming subset_univ → Z56
open Finset renaming mem_range → Z57
open AddMonoidAlgebra renaming coeff_sum → Z58
open Finset renaming sum_const → Z59
open Fin renaming lastCases → Z60
open Finset renaming sum_div → Z61
open Fintype renaming sum_bool → Z62
open Nat renaming le_of_lt_succ → Z63
open Fin renaming sum_univ_succ → Z64
open List renaming ofFn_succ → Z65
open Real renaming log_pos → Z66
open Function renaming comp_apply → Z67
open Nat renaming succ_le_of_lt → Z68
open Finset renaming prod_eq_zero → Z69
open Finset renaming abs_sum_le_sum_abs → Z70
open Finset renaming prod_congr → Z71
open Nat renaming lt_succ_of_le → Z72
open Finsupp renaming finsetSum_apply → Z73
open Real renaming exp_pos → Z74
open Real renaming exp_nat_mul → Z75
open Fin renaming sum_univ_eq_sum_range → Z76
open Real renaming rpow_natCast → Z77
open Finset renaming prod_const → Z78
open AddMonoidAlgebra renaming coeff_mul_apply_left → Z79
open AddMonoidAlgebra renaming single_pow → Z80
open Finset renaming sum_eq_zero → Z81
open Finset renaming single_le_sum → Z82
open Fintype renaming sum_sigma → Z83
open Finset renaming sum_sq_le_sum_mul_sum_of_sq_le_mul → Z84
open AddMonoidAlgebra renaming single_mul_single → Z85
open Finset renaming sum_eq_single → Z86
open Finset renaming sum_insert → Z87
open AddMonoidAlgebra renaming coeff_smul → Z88
open Finsupp renaming smul_apply → Z89
open Finset renaming range_mono → Z90
open Nat renaming zero_lt_of_lt → Z91
open Real renaming rpow_le_rpow → Z92
open Finset renaming filter_mem_eq_inter → Z93
open Finset renaming univ_inter → Z94
open Int renaming toNat_of_nonneg → Z95
open Real renaming log_le_sub_one_of_pos → Z96
open Finset renaming sum_subset → Z97
open Fintype renaming card_subtype → Z98
open Finset renaming prod_pow_eq_pow_sum → Z99
open Fin renaming succ_castSucc → Z100
open Finset renaming sum_erase_add → Z101
open Finset renaming sum_const_zero → Z102
open Equiv renaming apply_symm_apply → Z103
open Finset renaming sum_mul_sq_le_sq_mul_sq → Z104
open AddMonoidAlgebra renaming coeff_mul_single_apply → Z105
open Nat renaming exists_eq_succ_of_ne_zero → Z106
namespace OAI
open scoped ENNReal
noncomputable section
noncomputable section
namespace TraceReconstruction
structure FiniteLaw (α:Type*) [Fintype α] where
  mass:α → ℝ
  nonneg:∀ a,0 ≤ mass a
  total:∑ a,mass a = 1
namespace FiniteLaw
variable {α β:Type*} [Fintype α] [Fintype β]
def tv (P Q:FiniteLaw α):ℝ:=(1 / 2:ℝ) * ∑ a,|P.mass a - Q.mass a|
def Qbw (P Q:FiniteLaw α):ℝ :=
  ∑ a,(Z0 (P.mass a) - Z0 (Q.mass a)) ^ 2
def affinity (P Q:FiniteLaw α):ℝ :=
  ∑ a,Z0 (P.mass a) * Z0 (Q.mass a)
theorem Qjj (P Q:FiniteLaw α):0 ≤ affinity P Q:=by
  apply Z11
  intro a _; positivity
theorem Qfd (P Q:FiniteLaw α):0 ≤ Qbw P Q:=by
  apply Z11
  intro a _; positivity
theorem QdG (P Q:FiniteLaw α) :
    Qbw P Q = 2 - 2 * affinity P Q:=by
  unfold Qbw affinity
  calc
    _ = (∑ a,P.mass a) + (∑ a,Q.mass a) - 2 * ∑ a,
        Z0 (P.mass a) * Z0 (Q.mass a):=by
      rw [Z3,← Z14,← Z39]
      apply Z2 rfl
      intro a _
      have hp:=Z13 (P.nonneg a)
      have hq:=Z13 (Q.nonneg a)
      nlinarith only [hp,hq]
    _ = _:=by rw [P.total,Q.total]; ring
theorem QfQ (P Q:FiniteLaw α):affinity P Q ≤ 1:=by
  have h:=Qfd P Q
  rw [QdG] at h
  linarith
theorem QqZ (P Q:FiniteLaw α) :
    tv P Q ^ 2 ≤ Qbw P Q:=by
  have hpoint (a:α):|P.mass a - Q.mass a| ^ 2 ≤
      (Z0 (P.mass a) - Z0 (Q.mass a)) ^ 2 *
        (Z0 (P.mass a) + Z0 (Q.mass a)) ^ 2:=by
    rw [sq_abs]
    have hp:=Z13 (P.nonneg a)
    have hq:=Z13 (Q.nonneg a)
    nlinarith only [hp,hq,sq_nonneg (P.mass a - Q.mass a)]
  have h:=Z84
    (s:=Z16)
    (r:=fun a => |P.mass a - Q.mass a|)
    (f:=fun a => (Z0 (P.mass a) - Z0 (Q.mass a)) ^ 2)
    (g:=fun a => (Z0 (P.mass a) + Z0 (Q.mass a)) ^ 2)
    (fun a _ => sq_nonneg _) (fun a _ => sq_nonneg _) (fun a _ => hpoint a)
  have hplus:(∑ a,(Z0 (P.mass a) + Z0 (Q.mass a)) ^ 2) =
      2 + 2 * affinity P Q:=by
    unfold affinity
    calc
      _ = (∑ a,P.mass a) + (∑ a,Q.mass a) + 2 * ∑ a,
          Z0 (P.mass a) * Z0 (Q.mass a):=by
        rw [Z3,← Z14,← Z14]
        apply Z2 rfl
        intro a _
        have hp:=Z13 (P.nonneg a)
        have hq:=Z13 (Q.nonneg a)
        nlinarith only [hp,hq]
      _ = _:=by rw [P.total,Q.total]; ring
  rw [hplus] at h
  change (∑ a,|P.mass a - Q.mass a|) ^ 2 ≤ Qbw P Q * (2 + 2 * affinity P Q) at h
  have hbound:=mul_le_mul_of_nonneg_left (QfQ P Q) (Qfd P Q)
  unfold tv
  nlinarith only [h,hbound]
theorem QqX (P Q:FiniteLaw α) :
    tv P Q ≤ Z0 (Qbw P Q):=by
  have h:=QqZ P Q
  have hs:=Z13 (Qfd P Q)
  have hn:=Z36 (Qbw P Q)
  nlinarith only [h,hs,hn]
def product (P:FiniteLaw α) (m:ℕ):FiniteLaw (Fin m → α) where
  mass a:=∏ j,P.mass (a j)
  nonneg a:=Z37 fun j _ => P.nonneg (a j)
  total:=by
    rw [← Z43]
    simp [P.total]
theorem Qjk (P Q:FiniteLaw α) (m:ℕ) :
    affinity (P.product m) (Q.product m) = affinity P Q ^ m:=by
  unfold affinity product
  simp only
  have hexp (a:Fin m → α) :
      Z0 (∏ j,P.mass (a j)) * Z0 (∏ j,Q.mass (a j)) =
        ∏ j,(Z0 (P.mass (a j)) * Z0 (Q.mass (a j))):=by
    rw [Real.sqrt_prod _ (fun j _ => P.nonneg (a j)),
      Real.sqrt_prod _ (fun j _ => Q.nonneg (a j)),Z30]
  simp_rw [hexp]
  rw [← Z43 (fun (_:Fin m) a => Z0 (P.mass a) * Z0 (Q.mass a))]
  simp
theorem QlX (P Q:FiniteLaw α) (m:ℕ) :
    Qbw (P.product m) (Q.product m) ≤ (m:ℝ) * Qbw P Q:=by
  rw [QdG,Qjk,QdG]
  have ha:=Qjj P Q
  have hb:=QfQ P Q
  have hpow:1 - affinity P Q ^ m ≤ (m:ℝ) * (1 - affinity P Q):=by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ,Z23,Z25]
      have hmul:=mul_le_mul_of_nonneg_right ih ha
      have hm:(0:ℝ) ≤ (m:ℝ) * (1 - affinity P Q):=by positivity
      have hmon:=mul_le_mul_of_nonneg_left hb hm
      nlinarith only [hmul,hmon]
  linarith
theorem Qqm {t:ℝ} (ht:0 ≤ t) :
    (Z0 t - 1) ^ 2 ≤ (t - 1) ^ 2:=by
  have hs2:=Z13 ht
  have hprod:=mul_nonneg (Z36 t)
    (mul_nonneg (show 0 ≤ Z0 t + 2 by positivity) (sq_nonneg (Z0 t - 1)))
  conv_rhs => rw [← hs2]
  nlinarith only [hprod]
theorem QlW (P Q:FiniteLaw α) (Z:α → ℝ)
    (hZ:∀ a,Q.mass a = P.mass a * (1 + Z a)) :
    Qbw P Q ≤ ∑ a,P.mass a * Z a ^ 2:=by
  apply Z7
  intro a _
  by_cases hp0:P.mass a = 0
  · have hq0:Q.mass a = 0:=by rw [hZ,hp0,zero_mul]
    simp [hp0,hq0]
  have hp:0 < P.mass a:=lt_of_le_of_ne (P.nonneg a) (Ne.symm hp0)
  have ht:0 ≤ 1 + Z a:=by
    have hq:=Q.nonneg a
    rw [hZ] at hq
    exact nonneg_of_mul_nonneg_right hq hp
  have hs:=Qqm ht
  have hmul:=mul_le_mul_of_nonneg_left hs (P.nonneg a)
  have hp2:=Z13 (P.nonneg a)
  rw [hZ,Real.sqrt_mul (P.nonneg a)]
  calc
    _ = P.mass a * (Z0 (1 + Z a) - 1) ^ 2:=by
      calc
        _ = Z0 (P.mass a) ^ 2 * (Z0 (1 + Z a) - 1) ^ 2:=by ring
        _ = _:=by rw [hp2]
    _ ≤ P.mass a * ((1 + Z a) - 1) ^ 2:=hmul
    _ = _:=by ring
def bind (P:FiniteLaw α) (K:α → FiniteLaw β):FiniteLaw β where
  mass b:=∑ a,P.mass a * (K a).mass b
  nonneg b:=Z11 fun a _ => mul_nonneg (P.nonneg a) ((K a).nonneg b)
  total:=by
    rw [Z17]
    simp_rw [← Z3,(K _).total,mul_one]
    exact P.total
theorem Qjc (P Q R:FiniteLaw α):tv P R ≤ tv P Q + tv Q R:=by
  unfold tv
  rw [← mul_add,← Z14]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Z7
  intro a _
  exact abs_sub_le _ _ _
theorem tv_symm (P Q:FiniteLaw α):tv P Q = tv Q P:=by
  unfold tv
  congr 1
  apply Z2 rfl
  intro a _; exact abs_sub_comm _ _
theorem QgN (P Q:FiniteLaw α) (f:α → ℝ)
    (hf:∀ a,f a ∈ Z6 0 1) :
    (∑ a,P.mass a * f a) - (∑ a,Q.mass a * f a) ≤ tv P Q:=by
  have hz:(∑ a,(P.mass a - Q.mass a)) = 0:=by
    rw [Z39,P.total,Q.total,sub_self]
  have h (a:α):(P.mass a - Q.mass a) * f a ≤
      (|P.mass a - Q.mass a| + (P.mass a - Q.mass a)) / 2:=by
    by_cases hd:0 ≤ P.mass a - Q.mass a
    · rw [abs_of_nonneg hd]
      have:=mul_le_mul_of_nonneg_left (hf a).2 hd
      linarith
    · rw [abs_of_neg (lt_of_not_ge hd)]
      have:=mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) (hf a).1
      linarith
  calc
    _ = ∑ a,(P.mass a - Q.mass a) * f a:=by
      rw [← Z39]
      apply Z2 rfl
      intro a _; ring
    _ ≤ ∑ a,(|P.mass a - Q.mass a| + (P.mass a - Q.mass a)) / 2 :=
      Z7 fun a _ => h a
    _ = tv P Q:=by
      rw [← Z61,Z14,hz,add_zero]
      unfold tv
      ring
theorem sum_max_eq (P Q:FiniteLaw α) :
    (∑ a,max (P.mass a) (Q.mass a)) = 1 + tv P Q:=by
  have hpoint (a:α):max (P.mass a) (Q.mass a) =
      (P.mass a + Q.mass a + |P.mass a - Q.mass a|) / 2:=by
    by_cases h:P.mass a ≤ Q.mass a
    · rw [max_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left (le_of_not_ge h),abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]; ring
  simp_rw [hpoint]
  rw [← Z61,Z14,Z14,P.total,Q.total]
  unfold tv
  ring
def tensor (P:FiniteLaw α) (R:FiniteLaw β):FiniteLaw (α × β) where
  mass z:=P.mass z.1 * R.mass z.2
  nonneg z:=mul_nonneg (P.nonneg z.1) (R.nonneg z.2)
  total:=by
    rw [Z32]
    simp_rw [← Z3,R.total,mul_one]
    exact P.total
theorem Qra (P Q:FiniteLaw α) (R S:FiniteLaw β) :
    tv (P.tensor R) (Q.tensor S) ≤ tv P Q + tv R S:=by
  unfold tv tensor
  simp only
  rw [Z32,← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hpoint (a:α) (b:β) :
      |P.mass a * R.mass b - Q.mass a * S.mass b| ≤
        |P.mass a - Q.mass a| * R.mass b + Q.mass a * |R.mass b - S.mass b|:=by
    calc
      _ = |(P.mass a - Q.mass a) * R.mass b + Q.mass a * (R.mass b - S.mass b)|:=by
        congr 1; ring
      _ ≤ |(P.mass a - Q.mass a) * R.mass b| + |Q.mass a * (R.mass b - S.mass b)| :=
        abs_add_le _ _
      _ = _:=by rw [abs_mul,abs_mul,abs_of_nonneg (R.nonneg b),abs_of_nonneg (Q.nonneg a)]
  calc
    _ ≤ ∑ a,∑ b,(|P.mass a - Q.mass a| * R.mass b + Q.mass a * |R.mass b - S.mass b|):=by
      apply Z7
      intro a _
      exact Z7 fun b _ => hpoint a b
    _ = _:=by
      simp_rw [Z14,← Z3,R.total,mul_one]
      rw [← Z33,Q.total,one_mul]
theorem QqY (P Q:FiniteLaw α) (m:ℕ) :
    tv (P.product (m + 1)) (Q.product (m + 1)) =
      tv (P.tensor (P.product m)) (Q.tensor (Q.product m)):=by
  unfold tv product tensor
  simp only
  congr 1
  rw [← (Z46 (fun _:Fin (m + 1) => α)).sum_comp]
  apply Z2 rfl
  intro a _
  simp only [Z53,Fin.consEquiv_apply,Z54,Z55]
theorem Qja (P Q:FiniteLaw α) (m:ℕ) :
    tv (P.product m) (Q.product m) ≤ (m:ℝ) * tv P Q:=by
  induction m with
  | zero => simp [tv,product]
  | succ m ih =>
    rw [QqY]
    apply (Qra P Q (P.product m) (Q.product m)).trans
    simpa only [Z23,Z25,add_mul,one_mul,add_comm] using add_le_add_left ih (tv P Q)
theorem Qji (P Q:FiniteLaw α) (K:α → FiniteLaw β) :
    affinity P Q ≤ affinity (P.bind K) (Q.bind K):=by
  have hpoint (b:β) :
      (∑ a,Z0 (P.mass a) * Z0 (Q.mass a) * (K a).mass b) ≤
        Z0 ((P.bind K).mass b) * Z0 ((Q.bind K).mass b):=by
    have hcs:=Z84 (s:=Z16)
      (r:=fun a => Z0 (P.mass a) * Z0 (Q.mass a) * (K a).mass b)
      (f:=fun a => P.mass a * (K a).mass b) (g:=fun a => Q.mass a * (K a).mass b)
      (fun a _ => mul_nonneg (P.nonneg a) ((K a).nonneg b))
      (fun a _ => mul_nonneg (Q.nonneg a) ((K a).nonneg b)) (by
        intro a _
        rw [mul_pow,mul_pow,Z13 (P.nonneg a),Z13 (Q.nonneg a)]
        nlinarith only [sq_nonneg ((K a).mass b)])
    have hp2:=Z13 ((P.bind K).nonneg b)
    have hq2:=Z13 ((Q.bind K).nonneg b)
    have hsq:(Z0 ((P.bind K).mass b) * Z0 ((Q.bind K).mass b)) ^ 2 =
        (P.bind K).mass b * (Q.bind K).mass b:=by rw [mul_pow,hp2,hq2]
    change (∑ a,Z0 (P.mass a) * Z0 (Q.mass a) * (K a).mass b) ^ 2 ≤
      (P.bind K).mass b * (Q.bind K).mass b at hcs
    have hn:0 ≤ Z0 ((P.bind K).mass b) * Z0 ((Q.bind K).mass b):=by positivity
    nlinarith only [hcs,hsq,hn]
  calc
    affinity P Q = ∑ b,∑ a,Z0 (P.mass a) * Z0 (Q.mass a) * (K a).mass b:=by
      rw [Z17]
      simp_rw [← Z3,(K _).total,mul_one]
      rfl
    _ ≤ _:=Z7 fun b _ => hpoint b
theorem QlV (P Q:FiniteLaw α) (K:α → FiniteLaw β) :
    Qbw (P.bind K) (Q.bind K) ≤ Qbw P Q:=by
  rw [QdG,QdG]
  linarith [Qji P Q K]
def overlap (P Q:FiniteLaw α):ℝ:=∑ a,min (P.mass a) (Q.mass a)
theorem QdN (P Q:FiniteLaw α):overlap P Q = 1 - tv P Q:=by
  have hm:overlap P Q + (∑ a,max (P.mass a) (Q.mass a)) = 2:=by
    rw [overlap,← Z14]
    simp_rw [min_add_max]
    rw [Z14,P.total,Q.total]
    norm_num
  rw [sum_max_eq] at hm
  linarith
theorem QnT (P Q:FiniteLaw α):0 ≤ overlap P Q:=by
  apply Z11
  intro a _
  exact le_min (P.nonneg a) (Q.nonneg a)
def commonPart (P Q:FiniteLaw α) (h:0 < overlap P Q):FiniteLaw α where
  mass a:=min (P.mass a) (Q.mass a) / overlap P Q
  nonneg a:=div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le
  total:=by rw [← Z61]; exact div_self h.ne'
theorem QkB (P Q:FiniteLaw α) (h:0 < overlap P Q)
    {ω:ℝ} (hω:ω ≤ overlap P Q) (a:α) :
    ω * (commonPart P Q h).mass a ≤ P.mass a:=by
  change ω * (min (P.mass a) (Q.mass a) / overlap P Q) ≤ _
  calc
    _ ≤ overlap P Q * (min (P.mass a) (Q.mass a) / overlap P Q) :=
      mul_le_mul_of_nonneg_right hω (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
    _ = min (P.mass a) (Q.mass a):=by field_simp
    _ ≤ _:=min_le_left _ _
end FiniteLaw
end TraceReconstruction
namespace TraceReconstruction.FiniteLaw
variable {α β:Type*} [Fintype α] [Fintype β]
def prod (P:FiniteLaw α) (Q:FiniteLaw β):FiniteLaw (α × β) where
  mass x:=P.mass x.1 * Q.mass x.2
  nonneg x:=mul_nonneg (P.nonneg _) (Q.nonneg _)
  total:=by
    rw [Z32]
    simp_rw [← Z3,Q.total,mul_one]
    exact P.total
def expect (P:FiniteLaw α) (f:α → ℝ):ℝ:=∑ a,P.mass a * f a
theorem Qbi (P:FiniteLaw α) (c:ℝ):P.expect (fun _ => c) = c:=by
  unfold expect
  rw [← Z33,P.total,one_mul]
theorem QaZ (P:FiniteLaw α) {f g:α → ℝ} (h:∀ a,f a ≤ g a) :
    P.expect f ≤ P.expect g:=Z7 fun a _ =>
      mul_le_mul_of_nonneg_left (h a) (P.nonneg a)
theorem QbB (P:FiniteLaw α) (Q:FiniteLaw β) (f:α × β → ℝ) :
    (P.prod Q).expect f = P.expect (fun a => Q.expect (fun b => f (a,b))):=by
  unfold expect prod
  rw [Z32]
  simp_rw [Z3,mul_assoc]
def Associated [Preorder α] (P:FiniteLaw α):Prop :=
  ∀ f g:α → ℝ,Monotone f → Monotone g →
    P.expect f * P.expect g ≤ P.expect (fun a => f a * g a)
theorem Associated.prod [Preorder α] [Preorder β] {P:FiniteLaw α} {Q:FiniteLaw β}
    (hP:P.Associated) (hQ:Q.Associated):(P.prod Q).Associated:=by
  intro f g hf hg
  rw [QbB,QbB,QbB]
  calc
    _ ≤ P.expect (fun a => Q.expect (fun b => f (a,b)) * Q.expect (fun b => g (a,b))):=by
      apply hP
      · intro a a' ha
        exact Q.QaZ (fun b => hf ⟨ha,le_rfl⟩)
      · intro a a' ha
        exact Q.QaZ (fun b => hg ⟨ha,le_rfl⟩)
    _ ≤ _:=by
      apply P.QaZ
      intro a
      apply hQ
      · intro b b' hb; exact hf ⟨le_rfl,hb⟩
      · intro b b' hb; exact hg ⟨le_rfl,hb⟩
theorem Qet (P:FiniteLaw α) (n:ℕ) (f:(Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      P.expect (fun a => (P.product n).expect (fun b => f (Z15 a b))):=by
  unfold expect product
  rw [← (Z46 (fun _:Fin (n + 1) => α)).sum_comp,Z32]
  simp_rw [Z3]
  apply Z2 rfl
  intro a _
  apply Z2 rfl
  intro b _
  change (∏ j,P.mass ((Z15 a b:Fin (n + 1) → α) j)) * f (Z15 a b) = _
  rw [Z53]
  simp only [Z54,Z55]
  ring
theorem Qjn [Preorder α] (P:FiniteLaw α) (hP:P.Associated) (n:ℕ) :
    (P.product n).Associated:=by
  induction n with
  | zero =>
    intro f g _ _
    simp [expect,product]
  | succ n ih =>
    intro f g hf hg
    rw [Qet,Qet,Qet]
    have hcons {a a':α} {b b':Fin n → α} (ha:a ≤ a') (hb:b ≤ b') :
        (Z15 a b:Fin (n + 1) → α) ≤ (Z15 a' b':Fin (n + 1) → α):=by
      intro j
      refine Z38 ?_ (fun i => ?_) j
      · exact ha
      · exact hb i
    calc
      _ ≤ P.expect (fun a => (P.product n).expect (fun b => f (Z15 a b)) *
          (P.product n).expect (fun b => g (Z15 a b))):=by
        apply hP
        · intro a a' ha
          exact (P.product n).QaZ (fun b => hf (hcons ha le_rfl))
        · intro a a' ha
          exact (P.product n).QaZ (fun b => hg (hcons ha le_rfl))
      _ ≤ _:=by
        apply P.QaZ
        intro a
        apply ih
        · intro b b' hb; exact hf (hcons le_rfl hb)
        · intro b b' hb; exact hg (hcons le_rfl hb)
theorem QgE (P:FiniteLaw α) (f:α → ℝ)
    (hmean:P.expect f = 1) :
    (1:ℝ) / 4 ≤
      (P.expect (fun a => if 1 / 2 ≤ f a then 1 else 0)) * P.expect (fun a => f a ^ 2):=by
  classical
  let S:Finset α:=Finset.univ.filter (fun a => 1 / 2 ≤ f a)
  have hsmall:(∑ a ∈ Z16 \ S,P.mass a * f a) ≤ 1 / 2:=by
    calc
      _ ≤ ∑ a ∈ Z16 \ S,P.mass a * (1 / 2):=by
        apply Z7
        intro a ha
        have hnot:¬ 1 / 2 ≤ f a:=by simpa [S] using (Finset.mem_sdiff.mp ha).2
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hnot)) (P.nonneg a)
      _ ≤ ∑ a,P.mass a * (1 / 2):=by
        apply Z40 (Finset.sdiff_subset)
        intro a _ _; positivity [P.nonneg a]
      _ = 1 / 2:=P.Qbi _
  have hlarge:1 / 2 ≤ ∑ a ∈ S,P.mass a * f a:=by
    have hsplit:=Finset.sum_sdiff (Z56 S) (f:=fun a => P.mass a * f a)
    change (∑ a,P.mass a * f a) = 1 at hmean
    rw [hmean] at hsplit
    linarith
  have hc:=Z84 (s:=S)
    (r:=fun a => P.mass a * f a) (f:=P.mass) (g:=fun a => P.mass a * f a ^ 2)
    (fun a _ => P.nonneg a) (fun a _ => by positivity [P.nonneg a])
    (fun a _ => by nlinarith)
  have ht:(∑ a ∈ S,P.mass a * f a ^ 2) ≤ P.expect (fun a => f a ^ 2):=by
    apply Z40 (Z56 S)
    intro a _ _; positivity [P.nonneg a]
  have hmass:P.expect (fun a => if 1 / 2 ≤ f a then 1 else 0) = ∑ a ∈ S,P.mass a:=by
    unfold expect S
    simp_rw [mul_ite,mul_one,mul_zero]
    rw [Z27]
  rw [hmass]
  have hm:=mul_le_mul_of_nonneg_left ht (Z11 (s:=S) (fun a _ => P.nonneg a))
  nlinarith
theorem Qme [Preorder α] (P:FiniteLaw α) (hP:P.Associated)
    (f g:α → ℝ) (hf:∀ a,0 ≤ f a) (hg:∀ a,0 ≤ g a)
    (hfm:Monotone f) (hgm:Monotone g)
    (hf1:P.expect f = 1) (hg1:P.expect g = 1) :
    (1:ℝ) / 32 ≤ P.expect (fun a => min (f a) (g a)) *
      P.expect (fun a => f a ^ 2) * P.expect (fun a => g a ^ 2):=by
  let F:α → ℝ:=fun a => if 1 / 2 ≤ f a then 1 else 0
  let G:α → ℝ:=fun a => if 1 / 2 ≤ g a then 1 else 0
  have hF:Monotone F:=by
    intro a b hab
    dsimp [F]
    split_ifs with ha hb hb
    · rfl
    · exact False.elim (hb (ha.trans (hfm hab)))
    · norm_num
    · rfl
  have hG:Monotone G:=by
    intro a b hab
    dsimp [G]
    split_ifs with ha hb hb
    · rfl
    · exact False.elim (hb (ha.trans (hgm hab)))
    · norm_num
    · rfl
  have hcorr:=hP F G hF hG
  have hpoint:∀ a,(1 / 2:ℝ) * (F a * G a) ≤ min (f a) (g a):=by
    intro a
    dsimp [F,G]
    split_ifs <;> simp only [mul_one,mul_zero]
    · exact le_min ‹_› ‹_›
    all_goals exact le_min (hf a) (hg a)
  have hint:=P.QaZ hpoint
  have heq:P.expect (fun a => (1 / 2:ℝ) * (F a * G a)) =
      (1 / 2:ℝ) * P.expect (fun a => F a * G a):=by
    unfold expect
    rw [Z3]
    apply Z2 rfl
    intro a _; ring
  rw [heq] at hint
  have hfm2:0 ≤ P.expect (fun a => f a ^ 2) :=
    Z11 (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hgm2:0 ≤ P.expect (fun a => g a ^ 2) :=
    Z11 (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hff:=QgE P f hf1
  have hgg:=QgE P g hg1
  change 1 / 4 ≤ P.expect F * P.expect (fun a => f a ^ 2) at hff
  change 1 / 4 ≤ P.expect G * P.expect (fun a => g a ^ 2) at hgg
  have hmul:=mul_le_mul hff hgg (by norm_num:(0:ℝ) ≤ 1 / 4) (by linarith :
    0 ≤ P.expect F * P.expect (fun a => f a ^ 2))
  have hcomb:(1 / 2:ℝ) * (P.expect F * P.expect G) ≤
      P.expect (fun a => min (f a) (g a)):=by linarith
  have hmul2:=mul_le_mul_of_nonneg_right hcomb (mul_nonneg hfm2 hgm2)
  nlinarith only [hmul,hmul2]
end TraceReconstruction.FiniteLaw
namespace TraceReconstruction.FiniteLaw
variable {α:Type*} [Fintype α]
def Qcl (P Q:FiniteLaw α) (b:Bool):FiniteLaw (α × α) :=
  if b then Q.prod P else P.prod Q
def Qcm (H:FiniteLaw α) (ω:ℝ) (z:α × α):ℝ :=
  ω ^ 2 * H.mass z.1 * H.mass z.2
theorem Qqy (H:FiniteLaw α) (ω:ℝ) :
    (∑ z,Qcm H ω z) = ω ^ 2:=by
  unfold Qcm
  rw [Z32]
  simp_rw [← Z3,H.total,mul_one]
  rw [← Z3,H.total,mul_one]
theorem QnZ (P Q H:FiniteLaw α) {ω:ℝ} (hω:0 ≤ ω)
    (hP:∀ a,ω * H.mass a ≤ P.mass a) (hQ:∀ a,ω * H.mass a ≤ Q.mass a)
    (b:Bool) (z:α × α):Qcm H ω z ≤ (Qcl P Q b).mass z:=by
  have hm (R S:FiniteLaw α) (hR:∀ a,ω * H.mass a ≤ R.mass a)
      (hS:∀ a,ω * H.mass a ≤ S.mass a) :
      Qcm H ω z ≤ R.mass z.1 * S.mass z.2:=by
    calc
      _ = (ω * H.mass z.1) * (ω * H.mass z.2):=by unfold Qcm; ring
      _ ≤ _:=mul_le_mul (hR z.1) (hS z.2)
        (mul_nonneg hω (H.nonneg _)) (R.nonneg _)
  cases b
  · exact hm P Q hP hQ
  · exact hm Q P hQ hP
def Qbr (P Q H:FiniteLaw α) (ω:ℝ) (b:Bool)
    (z:Option Bool × (α × α)):ℝ :=
  match z.1 with
  | none => Qcm H ω z.2
  | some c => if c = b then (Qcl P Q b).mass z.2 - Qcm H ω z.2 else 0
theorem QhW (P Q H:FiniteLaw α) {ω:ℝ} (hω:0 ≤ ω)
    (hP:∀ a,ω * H.mass a ≤ P.mass a) (hQ:∀ a,ω * H.mass a ≤ Q.mass a)
    (b:Bool) (z:Option Bool × (α × α)):0 ≤ Qbr P Q H ω b z:=by
  unfold Qbr
  split
  · unfold Qcm
    positivity [H.nonneg z.2.1,H.nonneg z.2.2]
  · split_ifs
    · exact sub_nonneg.mpr (QnZ P Q H hω hP hQ b z.2)
    · rfl
theorem QhX (P Q H:FiniteLaw α) (ω:ℝ) (b:Bool) :
    (∑ z,Qbr P Q H ω b z) = 1:=by
  rw [Z32,Z17]
  have hp (z:α × α):(∑ c:Option Bool,Qbr P Q H ω b (c,z)) =
      (Qcl P Q b).mass z:=by
    cases b <;> simp [Qbr,Fintype.sum_option ]
  simp_rw [hp]
  exact (Qcl P Q b).total
def Qft (P Q H:FiniteLaw α) {ω:ℝ} (hω:0 ≤ ω)
    (hP:∀ a,ω * H.mass a ≤ P.mass a) (hQ:∀ a,ω * H.mass a ≤ Q.mass a)
    (b:Bool):FiniteLaw (Option Bool × (α × α)) :=
  ⟨Qbr P Q H ω b,QhW P Q H hω hP hQ b,
    QhX P Q H ω b⟩
theorem QnX (P Q H:FiniteLaw α) (ω:ℝ) (b:Bool) (z:α × α) :
    (∑ c:Option Bool,Qbr P Q H ω b (c,z)) =
      (Qcl P Q b).mass z:=by
  cases b <;> simp [Qbr,Fintype.sum_option ]
end TraceReconstruction.FiniteLaw
namespace TraceReconstruction.FiniteLaw
variable {α:Type*} [Fintype α]
theorem Qqe (n:ℕ) {x:ℝ} (hx:x ∈ Z6 0 (1 / 2)) :
    (∑ j ∈ Z5 n,x ^ j) ≤ 2:=by
  have he:=geom_sum_mul x n
  have hn:0 ≤ ∑ j ∈ Z5 n,x ^ j :=
    Z11 (fun j _ => pow_nonneg hx.1 j)
  have hp:=pow_nonneg hx.1 n
  nlinarith [mul_le_mul_of_nonneg_left hx.2 hn]
theorem Qqd (n:ℕ) {x:ℝ} (hx:0 ≤ x) (hsmall:(n:ℝ) * x ≤ 1 / 2) :
    (∑ j ∈ Z5 (n - 1),(n.choose (j + 2):ℝ) * x ^ (j + 2)) ≤
      2 * ((n:ℝ) * x) ^ 2:=by
  calc
    _ ≤ ∑ j ∈ Z5 (n - 1),((n:ℝ) * x) ^ 2 * ((n:ℝ) * x) ^ j:=by
      apply Z7
      intro j _
      have hc:(n.choose (j + 2):ℝ) ≤ (n:ℝ) ^ (j + 2):=by
        exact_mod_cast Nat.choose_le_pow n (j + 2)
      calc
        _ ≤ (n:ℝ) ^ (j + 2) * x ^ (j + 2) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
        _ = _:=by rw [← mul_pow,pow_add]; ring
    _ = ((n:ℝ) * x) ^ 2 * ∑ j ∈ Z5 (n - 1),((n:ℝ) * x) ^ j:=by
      rw [Z3]
    _ ≤ _:=by
      have h:=Qqe (n - 1) ⟨mul_nonneg (Z19 n) hx,hsmall⟩
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n:ℝ) * x))]
theorem QgM (P:FiniteLaw α) (Z:α → ℝ) (u:ℝ) (t:ℕ) :
    P.expect (fun a => (1 + u * Z a) ^ t) =
      ∑ j ∈ Z5 (t + 1),(t.choose j:ℝ) * u ^ j * P.expect (fun a => Z a ^ j):=by
  unfold expect
  simp_rw [add_comm (1:ℝ),add_pow,one_pow,mul_one,mul_pow,Z3]
  rw [Z17]
  apply Z2 rfl
  intro j _
  apply Z2 rfl
  intro a _
  ring
theorem Qlm (P:FiniteLaw α) (Z:α → ℝ) (t:ℕ) (ht:2 ≤ t)
    (hcenter:P.expect Z = 0)
    (hmom:∀ j ≤ t,|P.expect (fun a => Z a ^ j)| ≤ 2)
    {u:ℝ} (hu:(t:ℝ) * |u| ≤ 1 / 2) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 1 + 4 * ((t:ℝ) * u) ^ 2:=by
  rw [QgM]
  have ht':t + 1 = 2 + (t - 1):=by omega
  rw [ht',Finset.sum_range_add]
  have hz:P.expect (fun _:α => (1:ℝ)) = 1:=by simp [expect,P.total]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    Nat.choose_zero_right,Z25,pow_zero,mul_one,one_mul,
    Nat.choose_one_right,pow_one]
  rw [hz,hcenter]
  simp only [mul_zero,add_zero]
  have hb:(∑ j ∈ Z5 (t - 1),(t.choose (2 + j):ℝ) * u ^ (2 + j) *
      P.expect (fun a => Z a ^ (2 + j))) ≤
      2 * ∑ j ∈ Z5 (t - 1),(t.choose (j + 2):ℝ) * |u| ^ (j + 2):=by
    rw [Z3]
    apply Z7
    intro j hj
    have hjt:2 + j ≤ t:=by have:=Finset.mem_range.mp hj; omega
    have hm:=hmom (2 + j) hjt
    calc
      _ ≤ |(t.choose (2 + j):ℝ) * u ^ (2 + j) * P.expect (fun a => Z a ^ (2 + j))| :=
        le_abs_self _
      _ ≤ (t.choose (2 + j):ℝ) * |u| ^ (2 + j) * 2:=by
        rw [abs_mul,abs_mul,abs_of_nonneg (Z19 _),abs_pow]
        exact mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _:=by rw [Nat.add_comm 2 j]; ring
  have htail:=Qqd t (abs_nonneg u) hu
  have he:((t:ℝ) * |u|) ^ 2 = ((t:ℝ) * u) ^ 2:=by rw [mul_pow,mul_pow,sq_abs]
  rw [he] at htail
  linarith
theorem QgL (P:FiniteLaw α) (Z:α → ℝ) (t:ℕ)
    (ht:P.expect (fun a => |Z a| ^ t) ≤ 1) (j:ℕ) (hj:j ≤ t) :
    |P.expect (fun a => Z a ^ j)| ≤ 2:=by
  have hpoint (a:α):|Z a| ^ j ≤ 1 + |Z a| ^ t:=by
    by_cases hx:|Z a| ≤ 1
    · have h:=pow_le_one₀ (n:=j) (abs_nonneg _) hx
      nlinarith [pow_nonneg (abs_nonneg (Z a)) t]
    · have h:=pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) hj
      linarith
  calc
    _ ≤ ∑ a,|P.mass a * Z a ^ j|:=Z70 _ _
    _ = ∑ a,P.mass a * |Z a| ^ j:=by
      apply Z2 rfl
      intro a _
      rw [abs_mul,abs_of_nonneg (P.nonneg a),abs_pow]
    _ ≤ ∑ a,P.mass a * (1 + |Z a| ^ t):=by
      apply Z7
      intro a _
      exact mul_le_mul_of_nonneg_left (hpoint a) (P.nonneg a)
    _ = 1 + P.expect (fun a => |Z a| ^ t):=by
      simp_rw [mul_add,mul_one,Z14,P.total]
      rfl
    _ ≤ 2:=by linarith
theorem Qlj (P:FiniteLaw α) (Z:α → ℝ) (t:ℕ)
    (hmom:∀ j ≤ t,|P.expect (fun a => Z a ^ j)| ≤ 2) (u:ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 2 * (1 + |u|) ^ t:=by
  rw [QgM,add_comm (1:ℝ),add_pow,Z3]
  apply Z7
  intro j hj
  have h:=hmom j (by have:=Finset.mem_range.mp hj; omega)
  calc
    _ ≤ |(t.choose j:ℝ) * u ^ j * P.expect (fun a => Z a ^ j)|:=le_abs_self _
    _ ≤ (t.choose j:ℝ) * |u| ^ j * 2:=by
      rw [abs_mul,abs_mul,abs_of_nonneg (Z19 _),abs_pow]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = _:=by simp only [one_pow,mul_one]; ring
theorem Qpp (P:FiniteLaw α) (Z:α → ℝ) (k:ℕ) (hk:1 ≤ k)
    (hcenter:P.expect Z = 0) (ht:P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (u:ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ (2 * k)) ≤
      (1 + (6 * (2 * k:ℕ):ℝ) ^ 2 * u ^ 2) ^ k:=by
  have hmom:=QgL P Z (2 * k) ht
  have hkR:(1:ℝ) ≤ k:=by exact_mod_cast hk
  have htR:(1:ℝ) ≤ (2 * k:ℕ):=by exact_mod_cast (show 1 ≤ 2 * k by omega)
  have hbase:1 ≤ 1 + (6 * (2 * k:ℕ):ℝ) ^ 2 * u ^ 2:=by nlinarith [mul_nonneg (sq_nonneg (6 * ((2 * k:ℕ):ℝ))) (sq_nonneg u)]
  by_cases hu:((2 * k:ℕ):ℝ) * |u| ≤ 1 / 2
  · have hs:=Qlm P Z (2 * k) (by omega) hcenter hmom hu
    have hb:1 + 4 * (((2 * k:ℕ):ℝ) * u) ^ 2 ≤
        1 + (6 * (2 * k:ℕ):ℝ) ^ 2 * u ^ 2:=by nlinarith [sq_nonneg (((2 * k:ℕ):ℝ) * u)]
    exact hs.trans (hb.trans (le_self_pow₀ hbase (by omega)))
  · have hu':1 / 2 ≤ ((2 * k:ℕ):ℝ) * |u|:=le_of_lt (lt_of_not_ge hu)
    have hsum:1 + |u| ≤ 3 * ((2 * k:ℕ):ℝ) * |u|:=by
      have hh:=mul_le_mul_of_nonneg_right htR (abs_nonneg u)
      nlinarith
    have hc:(2:ℝ) ≤ (2:ℝ) ^ (2 * k):=le_self_pow₀ (by norm_num) (by omega)
    calc
      _ ≤ 2 * (1 + |u|) ^ (2 * k):=Qlj P Z (2 * k) hmom u
      _ ≤ 2 * (3 * ((2 * k:ℕ):ℝ) * |u|) ^ (2 * k):=by gcongr
      _ ≤ 2 ^ (2 * k) * (3 * ((2 * k:ℕ):ℝ) * |u|) ^ (2 * k):=by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ((6 * (2 * k:ℕ):ℝ) ^ 2 * u ^ 2) ^ k:=by
        rw [← mul_pow,pow_mul]
        congr 1
        simp only [mul_pow,sq_abs]
        ring
      _ ≤ _:=pow_le_pow_left₀ (by positivity) (by linarith) k
theorem Qpo (P:FiniteLaw α) (Z:α → ℝ) (k:ℕ) (hk:1 ≤ k)
    (hcenter:P.expect Z = 0) (ht:P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (b v:ℝ) :
    P.expect (fun a => (b + v * Z a) ^ (2 * k)) ≤
      (b ^ 2 + (6 * (2 * k:ℕ):ℝ) ^ 2 * v ^ 2) ^ k:=by
  have heven (a:α):|Z a| ^ (2 * k) = Z a ^ (2 * k):=by
    rw [pow_mul,sq_abs,← pow_mul]
  have hmoment:P.expect (fun a => Z a ^ (2 * k)) ≤ 1:=by
    simpa only [heven] using ht
  have hc:1 ≤ (6 * (2 * k:ℕ):ℝ) ^ 2:=by
    have hn:(1:ℝ) ≤ (2 * k:ℕ):=by exact_mod_cast (show 1 ≤ 2 * k by omega)
    nlinarith
  by_cases hb:b = 0
  · subst b
    simp only [zero_add,zero_pow (by omega:2 ≠ 0)]
    have he:P.expect (fun a => (v * Z a) ^ (2 * k)) =
        v ^ (2 * k) * P.expect (fun a => Z a ^ (2 * k)):=by
      simp only [expect,mul_pow,Z3]
      apply Z2 rfl
      intro a _
      ring
    rw [he]
    calc
      _ ≤ v ^ (2 * k):=by
        have hv:0 ≤ v ^ (2 * k):=by rw [pow_mul]; positivity
        nlinarith [mul_le_mul_of_nonneg_left hmoment hv]
      _ = (v ^ 2) ^ k:=pow_mul v 2 k
      _ ≤ _:=pow_le_pow_left₀ (sq_nonneg v) (by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg v)]) k
  · have hs:=Qpp P Z k hk hcenter ht (v / b)
    have hbpow:0 ≤ b ^ (2 * k):=by rw [pow_mul]; positivity
    have he:P.expect (fun a => (b + v * Z a) ^ (2 * k)) =
        b ^ (2 * k) * P.expect (fun a => (1 + v / b * Z a) ^ (2 * k)):=by
      unfold expect
      rw [Z3]
      apply Z2 rfl
      intro a _
      have h:b + v * Z a = b * (1 + v / b * Z a):=by field_simp [hb]
      dsimp only
      rw [h,mul_pow]
      ring
    rw [he]
    calc
      _ ≤ b ^ (2 * k) * (1 + (6 * (2 * k:ℕ):ℝ) ^ 2 * (v / b) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_left hs hbpow
      _ = _:=by
        rw [pow_mul,← mul_pow]
        congr 1
        field_simp [hb]
theorem Qri (P:FiniteLaw α) (k:ℕ) (hk:1 ≤ k)
    (f g:α → ℝ) (hf:∀ a,0 ≤ f a) (hg:∀ a,0 ≤ g a)
    (A B:ℝ) (hA:0 ≤ A) (hB:0 ≤ B)
    (hfa:P.expect (fun a => f a ^ k) ≤ A ^ k)
    (hgb:P.expect (fun a => g a ^ k) ≤ B ^ k) :
    P.expect (fun a => (f a + g a) ^ k) ≤ (A + B) ^ k:=by
  have hkR:(1:ℝ) ≤ k:=by exact_mod_cast hk
  have hk0:(k:ℝ) ≠ 0:=by positivity
  let w:α → ℝ:=fun a => P.mass a ^ (1 / (k:ℝ))
  have hw (a:α):0 ≤ w a:=Real.rpow_nonneg (P.nonneg a) _
  have hwk (a:α):w a ^ k = P.mass a:=by
    dsimp [w]
    rw [← Z77,← Real.rpow_mul (P.nonneg a),one_div_mul_cancel hk0,Real.rpow_one]
  have hsingle (F:α → ℝ) (hF:∀ a,0 ≤ F a) :
      (∑ a,|w a * F a| ^ (k:ℝ)) = P.expect (fun a => F a ^ k):=by
    apply Z2 rfl
    intro a _
    rw [abs_of_nonneg (mul_nonneg (hw a) (hF a)),Z77,mul_pow,hwk]
  have hsum:(∑ a,|w a * f a + w a * g a| ^ (k:ℝ)) =
      P.expect (fun a => (f a + g a) ^ k):=by
    simp_rw [← mul_add]
    exact hsingle _ (fun a => add_nonneg (hf a) (hg a))
  have hm:=Real.Lp_add_le Z16 (fun a => w a * f a) (fun a => w a * g a) hkR
  rw [hsum,hsingle f hf,hsingle g hg] at hm
  have hroots (F:α → ℝ) (hF:∀ a,0 ≤ F a) (C:ℝ) (hC:0 ≤ C)
      (hFC:P.expect (fun a => F a ^ k) ≤ C ^ k) :
      (P.expect (fun a => F a ^ k)) ^ (1 / (k:ℝ)) ≤ C:=by
    calc
      _ ≤ (C ^ k) ^ (1 / (k:ℝ)) :=
        Z92 (Z11 (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (hF a) k))) hFC (by positivity)
      _ = C:=by
        rw [← Z77,one_div,Real.rpow_rpow_inv hC hk0]
  have hroot:(P.expect (fun a => (f a + g a) ^ k)) ^ (1 / (k:ℝ)) ≤ A + B :=
    hm.trans (add_le_add (hroots f hf A hA hfa) (hroots g hg B hB hgb))
  have hexp:0 ≤ P.expect (fun a => (f a + g a) ^ k) :=
    Z11 (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (add_nonneg (hf a) (hg a)) k))
  have hp:=pow_le_pow_left₀ (Real.rpow_nonneg hexp _) hroot k
  rw [← Z77,← Real.rpow_mul hexp,one_div_mul_cancel hk0,Real.rpow_one] at hp
  exact hp
theorem Qim (P:FiniteLaw α) (n:ℕ) (f:(Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      (P.product n).expect (fun b => P.expect (fun a => f (Z15 a b))):=by
  rw [Qet]
  unfold expect
  simp_rw [Z3]
  rw [Z17]
  apply Z2 rfl
  intro b _
  apply Z2 rfl
  intro a _
  ring
end TraceReconstruction.FiniteLaw
namespace TraceReconstruction
variable {α:Type*}
def Qaj {n:ℕ} (A:(Fin n → Bool) → ℝ) (Z:α → ℝ) (x:Fin n → α):ℝ :=
  ∑ σ,A σ * ∏ j,if σ j then Z (x j) else 1
def QaK {n:ℕ} (A:(Fin n → Bool) → ℝ) (R:ℝ):ℝ :=
  ∑ σ,A σ ^ 2 * ∏ j,if σ j then R ^ 2 else 1
theorem Qfq {n:ℕ} (A:(Fin n → Bool) → ℝ) (R:ℝ) :
    0 ≤ QaK A R:=by
  apply Z11
  intro σ _
  apply mul_nonneg (sq_nonneg _)
  apply Z37
  intro j _
  split <;> positivity
theorem QhR {n:ℕ} (A:(Fin (n + 1) → Bool) → ℝ) (Z:α → ℝ)
    (x:Fin n → α) (a:α) :
    Qaj A Z (Z15 a x) =
      Qaj (fun σ => A (Z15 false σ)) Z x +
      Z a * Qaj (fun σ => A (Z15 true σ)) Z x:=by
  unfold Qaj
  rw [← (Z46 (fun _:Fin (n + 1) => Bool)).sum_comp,Z32]
  simp only [Z46,Equiv.coe_fn_mk,Z62,Z53,Z54,Z55,
    Bool.false_eq_true,↓reduceIte,one_mul]
  rw [Z3]
  rw [add_comm]
  congr 1
  apply Z2 rfl
  intro σ _
  ring
theorem QhO {n:ℕ} (A:(Fin (n + 1) → Bool) → ℝ) (R:ℝ) :
    QaK A R =
      QaK (fun σ => A (Z15 false σ)) R +
      R ^ 2 * QaK (fun σ => A (Z15 true σ)) R:=by
  unfold QaK
  rw [← (Z46 (fun _:Fin (n + 1) => Bool)).sum_comp,Z32]
  simp only [Z46,Equiv.coe_fn_mk,Z62,Z53,Z54,Z55,
    Bool.false_eq_true,↓reduceIte,one_mul]
  rw [Z3]
  rw [add_comm]
  congr 1
  apply Z2 rfl
  intro σ _
  ring
theorem QnB {α:Type*} [Fintype α] (P:FiniteLaw α)
    (Z:α → ℝ) (k:ℕ) (hk:1 ≤ k) (hcenter:P.expect Z = 0)
    (ht:P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1)
    (n:ℕ) (A:(Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => Qaj A Z x ^ (2 * k)) ≤
      (QaK A (6 * (2 * k:ℕ))) ^ k:=by
  induction n with
  | zero =>
    simp only [FiniteLaw.expect,FiniteLaw.product,Qaj,QaK,
      Fintype.prod_empty,mul_one,one_mul]
    simp only [Finset.univ_unique,Finset.sum_singleton]
    exact le_of_eq (pow_mul _ 2 k)
  | succ n ih =>
    let A0:(Fin n → Bool) → ℝ:=fun σ => A (Z15 false σ)
    let A1:(Fin n → Bool) → ℝ:=fun σ => A (Z15 true σ)
    let R:ℝ:=6 * (2 * k:ℕ)
    let F0:(Fin n → α) → ℝ:=fun x => Qaj A0 Z x
    let F1:(Fin n → α) → ℝ:=fun x => Qaj A1 Z x
    have h0:=ih A0
    have h1:=ih A1
    have hA0:=Qfq A0 R
    have hA1:=Qfq A1 R
    rw [FiniteLaw.Qim,QhO]
    calc
      _ ≤ (P.product n).expect (fun x => (F0 x ^ 2 + R ^ 2 * F1 x ^ 2) ^ k):=by
        apply FiniteLaw.QaZ
        intro x
        simp_rw [QhR]
        have hs:=FiniteLaw.Qpo P Z k hk hcenter ht (F0 x) (F1 x)
        simpa only [F0,F1,A0,A1,R,mul_comm] using hs
      _ ≤ (QaK A0 R + R ^ 2 * QaK A1 R) ^ k:=by
        apply FiniteLaw.Qri (P.product n) k hk
          (fun x => F0 x ^ 2) (fun x => R ^ 2 * F1 x ^ 2)
          (fun x => sq_nonneg _) (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (QaK A0 R) (R ^ 2 * QaK A1 R) hA0
          (mul_nonneg (sq_nonneg _) hA1)
        · simpa only [← pow_mul] using h0
        · have he:(P.product n).expect (fun x => (R ^ 2 * F1 x ^ 2) ^ k) =
              (R ^ 2) ^ k * (P.product n).expect (fun x => F1 x ^ (2 * k)):=by
            unfold FiniteLaw.expect
            simp only [mul_pow,← pow_mul,Z3]
            apply Z2 rfl
            intro x _
            ring
          rw [he,mul_pow (R ^ 2) (QaK A1 R)]
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (sq_nonneg R) k)
      _ = _:=rfl
def Qap {n:ℕ} (σ:Fin n → Bool):ℕ :=
  (Finset.univ.filter (fun j => σ j = true)).card
theorem Qni {n:ℕ} (σ:Fin n → Bool) (R:ℝ) :
    (∏ j,if σ j then R ^ 2 else 1) = R ^ (2 * Qap σ):=by
  rw [← Finset.prod_filter]
  simp only [Z78,← pow_mul,Qap]
def FiniteLaw.Qbh {α:Type*} [Fintype α] (P:FiniteLaw α)
    (f:α → ℝ) (k:ℕ):ℝ :=
  (P.expect (fun a => |f a| ^ (2 * k))) ^ (1 / (k:ℝ))
end TraceReconstruction
namespace TraceReconstruction.FiniteLaw
variable {α:Type*} [Fintype α]
def eventMass (P:FiniteLaw α) (A:Finset α):ℝ:=∑ a ∈ A,P.mass a
theorem QeY (P:FiniteLaw α) (A:Finset α):0 ≤ P.eventMass A :=
  Z11 (fun a _ => P.nonneg a)
theorem QgH (P:FiniteLaw α) (A:Finset α):P.eventMass A ≤ 1:=by
  rw [← P.total]
  exact Z40 (Z56 _)
    (fun a _ _ => P.nonneg a)
def condition (P:FiniteLaw α) (A:Finset α) (hA:0 < P.eventMass A):FiniteLaw α:=by
  classical
  exact {
    mass:=fun a => if a ∈ A then P.mass a / P.eventMass A else 0
    nonneg:=fun a => by split <;> positivity [P.nonneg a]
    total:=by
      rw [← Z27]
      simp only [Z93,Z94]
      rw [← Z61]
      exact div_self (ne_of_gt hA) }
theorem QnS (P:FiniteLaw α) (A:Finset α) (hA:0 < P.eventMass A) :
    overlap P (condition P A hA) = P.eventMass A:=by
  classical
  have he (a:α):min (P.mass a) ((condition P A hA).mass a) =
      if a ∈ A then P.mass a else 0:=by
    by_cases ha:a ∈ A
    · simp only [condition,ha,↓reduceIte]
      apply min_eq_left
      apply (le_div_iff₀ hA).mpr
      have h:=mul_le_mul_of_nonneg_left (P.QgH A) (P.nonneg a)
      simpa only [mul_one] using h
    · simp only [condition,ha,↓reduceIte,min_eq_right (P.nonneg a)]
  unfold overlap
  simp_rw [he]
  rw [← Z27]
  simp only [Z93,Z94,eventMass]
theorem QiY (P:FiniteLaw α) (A:Finset α) (hA:0 < P.eventMass A) :
    tv P (condition P A hA) = 1 - P.eventMass A:=by
  have he:=P.QnS A hA
  rw [QdN] at he
  linarith
def Qag (P:FiniteLaw α) (f:α → ℝ) (hf:∀ a,0 ≤ f a)
    (hmean:P.expect f = 1):FiniteLaw α where
  mass a:=P.mass a * f a
  nonneg a:=mul_nonneg (P.nonneg a) (hf a)
  total:=hmean
theorem QkU (P:FiniteLaw α) (f:α → ℝ) (A:Finset α) :
    (∑ a ∈ A,P.mass a * f a) ^ 2 ≤
      (P.eventMass A) * P.expect (fun a => f a ^ 2):=by
  have h:=Z104 A (fun a => Z0 (P.mass a))
    (fun a => Z0 (P.mass a) * f a)
  simp only [mul_pow,Z13 (P.nonneg _)] at h
  have he:(∑ a ∈ A,Z0 (P.mass a) * (Z0 (P.mass a) * f a)) =
      ∑ a ∈ A,P.mass a * f a:=by
    apply Z2 rfl
    intro a _
    rw [← mul_assoc,← pow_two,Z13 (P.nonneg a)]
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (P.QeY A)
  exact Z40 (Z56 _) (fun a _ _ =>
    mul_nonneg (P.nonneg a) (sq_nonneg _))
theorem Qnb (P:FiniteLaw α) (f:α → ℝ) (t:ℕ)
    (A:Finset α) (hA:∀ a ∈ A,f a < 1 / 2) :
    P.eventMass A ≤ (2:ℝ) ^ t * P.expect (fun a => |f a - 1| ^ t):=by
  have hlocal (a:α) (ha:a ∈ A):1 ≤ (2:ℝ) ^ t * |f a - 1| ^ t:=by
    rw [← mul_pow]
    apply one_le_pow₀
    have hh:=neg_le_abs (f a - 1)
    linarith [hA a ha]
  calc
    _ ≤ ∑ a ∈ A,(2:ℝ) ^ t * (P.mass a * |f a - 1| ^ t):=by
      apply Z7
      intro a ha
      nlinarith [mul_le_mul_of_nonneg_left (hlocal a ha) (P.nonneg a)]
    _ ≤ ∑ a,(2:ℝ) ^ t * (P.mass a * |f a - 1| ^ t):=by
      exact Z40 (Z56 _) (fun a _ _ => by positivity [P.nonneg a])
    _ = _:=by rw [← Z3]; rfl
theorem QkH (R:FiniteLaw α) (f g:α → ℝ)
    (hf:∀ a,0 ≤ f a) (hg:∀ a,0 ≤ g a)
    (hfm:R.expect f = 1) (hgm:R.expect g = 1)
    (A:Finset α) (hAf:∀ a ∈ A,0 < f a)
    (hP:0 < (R.Qag f hf hfm).eventMass A)
    (hQ:0 < (R.Qag g hg hgm).eventMass A) (a:α) :
    (condition (R.Qag g hg hgm) A hQ).mass a =
      (condition (R.Qag f hf hfm) A hP).mass a *
      ((R.Qag f hf hfm).eventMass A /
        (R.Qag g hg hgm).eventMass A * (g a / f a)):=by
  classical
  by_cases ha:a ∈ A
  · simp only [condition,ha,↓reduceIte]
    change R.mass a * g a / (R.Qag g hg hgm).eventMass A =
      R.mass a * f a / (R.Qag f hf hfm).eventMass A *
        ((R.Qag f hf hfm).eventMass A /
          (R.Qag g hg hgm).eventMass A * (g a / f a))
    field_simp [ne_of_gt hP,ne_of_gt hQ,ne_of_gt (hAf a ha)]
  · simp only [condition,ha,↓reduceIte,zero_mul]
theorem Qki (R:FiniteLaw α) (f g:α → ℝ)
    (hf:∀ a,0 ≤ f a) (hfm:R.expect f = 1)
    (A:Finset α) (hAf:∀ a ∈ A,1 / 2 ≤ f a)
    (hP:0 < (R.Qag f hf hfm).eventMass A) (k:ℕ) :
    (condition (R.Qag f hf hfm) A hP).expect
        (fun a => |g a / f a - 1| ^ (k + 1)) ≤
      (2:ℝ) ^ k / (R.Qag f hf hfm).eventMass A *
        R.expect (fun a => |g a - f a| ^ (k + 1)):=by
  classical
  have hpoint (a:α) (ha:a ∈ A) :
      f a * |g a / f a - 1| ^ (k + 1) ≤
        (2:ℝ) ^ k * |g a - f a| ^ (k + 1):=by
    have hp:0 < f a:=lt_of_lt_of_le (by norm_num) (hAf a ha)
    rw [div_sub_one (ne_of_gt hp),abs_div,abs_of_pos hp]
    have hi:0 ≤ 1 / f a:=by positivity
    have hi2:1 / f a ≤ 2:=(div_le_iff₀ hp).mpr (by linarith [hAf a ha])
    calc
      _ = |g a - f a| ^ (k + 1) * (1 / f a) ^ k:=by
        rw [div_pow,div_pow,one_pow,pow_succ (f a)]
        field_simp [ne_of_gt hp]
      _ ≤ _:=by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hi hi2 k) (show 0 ≤ |g a - f a| ^ (k + 1) by positivity)
  unfold expect
  calc
    _ = ∑ a ∈ A,(R.mass a * (f a * |g a / f a - 1| ^ (k + 1))) /
          (R.Qag f hf hfm).eventMass A:=by
      simp only [condition,Qag]
      simp_rw [ite_mul,zero_mul]
      rw [← Z27]
      simp only [Z93,Z94]
      apply Z2 rfl
      intro a _
      ring
    _ ≤ ∑ a ∈ A,((2:ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.Qag f hf hfm).eventMass A:=by
      apply Z7
      intro a ha
      apply div_le_div_of_nonneg_right _ hP.le
      nlinarith [mul_le_mul_of_nonneg_left (hpoint a ha) (R.nonneg a)]
    _ ≤ ∑ a,((2:ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.Qag f hf hfm).eventMass A:=by
      apply Z40 (Z56 _)
      intro a _ _
      positivity [R.nonneg a]
    _ = _:=by rw [← Z61,← Z3]; ring
theorem Qpq (P:FiniteLaw α) (u:α → ℝ)
    (c:ℝ) (hc:0 ≤ c) (k:ℕ) :
    P.expect (fun a => |c * u a - 1| ^ (k + 1)) ≤
      2 ^ k * (c ^ (k + 1) * P.expect (fun a => |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1)):=by
  have hb (a:α):|c * u a - 1| ^ (k + 1) ≤
      2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) + |c - 1| ^ (k + 1)):=by
    have he:c * u a - 1 = c * (u a - 1) + (c - 1):=by ring
    rw [he]
    calc
      _ ≤ (|c * (u a - 1)| + |c - 1|) ^ (k + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _
      _ ≤ _:=by
        have h:=add_pow_le (abs_nonneg (c * (u a - 1))) (abs_nonneg (c - 1)) (k + 1)
        simpa only [Nat.add_sub_cancel,abs_mul,abs_of_nonneg hc,mul_pow] using h
  unfold expect
  calc
    _ ≤ ∑ a,P.mass a * (2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) +
        |c - 1| ^ (k + 1))):=Z7 (fun a _ =>
          mul_le_mul_of_nonneg_left (hb a) (P.nonneg a))
    _ = 2 ^ k * (c ^ (k + 1) * (∑ a,P.mass a * |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1) * ∑ a,P.mass a):=by
      simp only [mul_add,Z14,Z3]
      congr 1 <;> apply Z2 rfl <;> intro a _ <;> ring
    _ = _:=by rw [P.total,mul_one]
end TraceReconstruction.FiniteLaw
namespace TraceReconstruction
namespace FiniteLaw
variable {α β:Type*} [Fintype α] [Fintype β]
def QaR {n:ℕ} (P:Fin n → FiniteLaw α):FiniteLaw (Fin n → α) where
  mass x:=∏ i,(P i).mass (x i)
  nonneg x:=Z37 (fun i _ => (P i).nonneg (x i))
  total:=by rw [← Z43]; simp only [FiniteLaw.total,Finset.prod_const_one]
def mixture (R:FiniteLaw β) (P:β → FiniteLaw α):FiniteLaw α where
  mass a:=∑ b,R.mass b * (P b).mass a
  nonneg a:=Z11 (fun b _ => mul_nonneg (R.nonneg b) ((P b).nonneg a))
  total:=by
    rw [Z17]
    simp_rw [← Z3,FiniteLaw.total,mul_one]
    exact R.total
end FiniteLaw
variable {α Ω:Type*} [Fintype Ω]
def Qdt {n:ℕ} (θ σ:Fin n → Bool):ℝ :=
  ∏ i,if σ i then (if θ i then 1 else 0) else 1
def Qce {n:ℕ} (θ:Fin n → Bool) (Z:α → ℝ) (x:Fin n → α):ℝ :=
  ∏ i,if θ i then 1 + Z (x i) else 1
def Qbm {n:ℕ} (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool)
    (σ:Fin n → Bool):ℝ:=R.expect (fun ω => Qdt (θ ω) σ)
def QaX {n:ℕ} (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool)
    (Z:α → ℝ) (x:Fin n → α):ℝ:=R.expect (fun ω => Qce (θ ω) Z x)
theorem Qpu {n:ℕ} (θ:Fin n → Bool) (Z:α → ℝ)
    (x:Fin n → α):Qce θ Z x = Qaj (Qdt θ) Z x:=by
  unfold Qce Qaj Qdt
  simp_rw [← Z30]
  rw [← Z43 (fun (i:Fin n) (b:Bool) =>
    (if b then (if θ i then (1:ℝ) else 0) else 1) * (if b then Z (x i) else 1))]
  apply Z71 rfl
  intro i _
  cases θ i <;> simp [add_comm]
theorem QfT {n:ℕ} (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool)
    (Z:α → ℝ) (x:Fin n → α) :
    QaX R θ Z x = Qaj (Qbm R θ) Z x:=by
  unfold QaX Qbm
  simp_rw [Qpu]
  unfold Qaj FiniteLaw.expect
  simp_rw [Z3,Z33]
  rw [Z17]
  apply Z2 rfl
  intro σ _
  apply Z2 rfl
  intro ω _
  ring
theorem QfS {n:ℕ} (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool) :
    Qbm R θ (fun _ => false) = 1:=by
  simp [Qbm,Qdt,FiniteLaw.expect,R.total]
theorem QmU [Fintype α] {n:ℕ} (P Q:FiniteLaw α) (Z:α → ℝ)
    (hscore:∀ a,Q.mass a = P.mass a * (1 + Z a))
    (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool) (x:Fin n → α) :
    (R.mixture (fun ω => FiniteLaw.QaR (fun i => if θ ω i then Q else P))).mass x =
      (∏ i,P.mass (x i)) * QaX R θ Z x:=by
  unfold FiniteLaw.mixture FiniteLaw.QaR QaX FiniteLaw.expect
  rw [Z3]
  apply Z2 rfl
  intro ω _
  have he:(∏ i,(if θ ω i then Q else P).mass (x i)) =
      (∏ i,P.mass (x i)) * Qce (θ ω) Z x:=by
    rw [Qce,← Z30]
    apply Z71 rfl
    intro i _
    cases θ ω i <;> simp only [Bool.false_eq_true,↓reduceIte,mul_one,hscore]
  change R.mass ω * (∏ i,(if θ ω i then Q else P).mass (x i)) =
    (∏ i,P.mass (x i)) * (R.mass ω * Qce (θ ω) Z x)
  rw [he]
  ring
end TraceReconstruction
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open scoped ENNReal
noncomputable section
namespace TraceReconstruction
abbrev Word (n:ℕ):=Fin n → Bool
abbrev Mask (n:ℕ):=Fin n → Bool
abbrev Trace:=List Bool
def traceOfMask {n:ℕ} (x:Word n) (a:Mask n):Trace :=
  ((List.finRange n).filter fun i => a i).map x
def maskWeight {n:ℕ} (q:ℝ) (a:Mask n):ℝ :=
  ∏ i,if a i then 1 - q else q
def traceMass {n:ℕ} (q:ℝ) (x:Word n) (w:Trace):ℝ :=
  ∑ a:Mask n,if traceOfMask x a = w then maskWeight q a else 0
def traceSpace (n:ℕ):Finset Trace :=
  Finset.univ.biUnion fun k:Fin (n + 1) =>
    Finset.univ.image fun x:Word k.val => Z20 x
def traceTV {n:ℕ} (q:ℝ) (x y:Word n):ℝ :=
  (1 / 2:ℝ) * ∑ w ∈ traceSpace n,|traceMass q x w - traceMass q y w|
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem QeA {n:ℕ} (x:Word n) (a:Mask n) :
    (traceOfMask x a).length ≤ n:=by
  simpa [traceOfMask] using List.length_filter_le (fun i => a i) (List.finRange n)
theorem QdM {n:ℕ} (w:Trace) (h:w.length ≤ n) :
    w ∈ traceSpace n:=by
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨w.length,Z72 h⟩,Z21 _,?_⟩
  exact Finset.mem_image.mpr ⟨w.get,Z21 _,List.ofFn_get w⟩
theorem Qhv {n:ℕ} {w:Trace} (h:w ∈ traceSpace n) :
    w.length ≤ n:=by
  obtain ⟨k,_,hk⟩:=Finset.mem_biUnion.mp h
  obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hk
  simpa using Z63 k.isLt
@[simp] theorem Qrr {n:ℕ} {w:Trace} :
    w ∈ traceSpace n ↔ w.length ≤ n :=
  ⟨Qhv,QdM w⟩
theorem QqG {n:ℕ} (x:Word n) (a:Mask n) :
    traceOfMask x a ∈ traceSpace n :=
  QdM _ (QeA x a)
theorem QhD {n:ℕ} {q:ℝ} (hq:q ∈ Z6 0 1) (a:Mask n) :
    0 ≤ maskWeight q a:=by
  apply Z37
  intro i _
  split <;> linarith [hq.1,hq.2]
@[simp] theorem Qqx {n:ℕ} (q:ℝ) :
    ∑ a:Mask n,maskWeight q a = 1:=by
  unfold maskWeight
  change (∑ a:Fin n → Bool,∏ i,(fun (_:Fin n) (b:Bool) =>
    if b then 1 - q else q) i (a i)) = 1
  rw [← Z43 (fun (_:Fin n) (b:Bool) => if b then 1 - q else q)]
  simp
theorem QqF {n:ℕ} {q:ℝ} (hq:q ∈ Z6 0 1)
    (x:Word n) (w:Trace):0 ≤ traceMass q x w:=by
  apply Z11
  intro a _
  split
  · exact QhD hq a
  · exact le_rfl
@[simp] theorem QqC {n:ℕ} (q:ℝ) (x:Word n) :
    ∑ w ∈ traceSpace n,traceMass q x w = 1:=by
  unfold traceMass
  rw [Z17]
  simp [QeA]
end TraceReconstruction
namespace TraceReconstruction
namespace FiniteLaw
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]
theorem ext {P Q:FiniteLaw α} (h:P.mass = Q.mass):P = Q:=by
  cases P with
  | mk pm pn pt => cases Q with
    | mk qm qn qt => cases h; rfl
noncomputable def pure (a:α):FiniteLaw α:=by
  classical
  exact ⟨(fun b => if a = b then 1 else 0),
    (fun b => by split_ifs <;> norm_num),by simp⟩
noncomputable def map (P:FiniteLaw α) (f:α → β):FiniteLaw β :=
  P.bind (fun a => pure (f a))
theorem map_mass [DecidableEq β] (P:FiniteLaw α) (f:α → β) (b:β) :
    (P.map f).mass b = ∑ a,if f a = b then P.mass a else 0:=by
  classical
  unfold map bind pure
  simp only
  apply Z2 rfl
  intro a _
  split_ifs <;> simp
theorem Qln (P:FiniteLaw α) (f:α → β) (F:β → ℝ) :
    (∑ b,(P.map f).mass b * F b) = ∑ a,P.mass a * F (f a):=by
  classical
  simp_rw [map_mass,Z33]
  rw [Z17]
  apply Z2 rfl
  intro a _
  simp
end FiniteLaw
abbrev BoundedTrace (n:ℕ):=↥(traceSpace n)
def maskLaw {n:ℕ} (q:ℝ) (hq:q ∈ Z6 0 1):FiniteLaw (Mask n) :=
  ⟨maskWeight q,QhD hq,Qqx q⟩
def completeTraceLaw {n:ℕ} (q:ℝ) (hq:q ∈ Z6 0 1) (x:Word n) :
    FiniteLaw (BoundedTrace n) where
  mass w:=traceMass q x w
  nonneg w:=QqF hq x w
  total:=by rw [Finset.sum_coe_sort]; exact QqC q x
theorem QkD {n:ℕ} (q:ℝ) (hq:q ∈ Z6 0 1) (x:Word n) :
    completeTraceLaw q hq x =
      (maskLaw q hq).map (fun a:Mask n => ⟨traceOfMask x a,QqG x a⟩):=by
  apply FiniteLaw.ext
  funext w
  rw [FiniteLaw.map_mass]
  unfold completeTraceLaw traceMass maskLaw
  simp only
  apply Z2 rfl
  intro a _
  rcases w with ⟨w,hw⟩
  simp only [Subtype.mk.injEq]
theorem QiU {n:ℕ} (x:Word n) (a:Mask n) :
    traceOfMask x a = (Z20 fun i => if a i then some (x i) else none).filterMap id:=by
  have hlist (l:List (Fin n)) :
      (l.filter fun i => a i).map x = l.filterMap (fun i => if a i then some (x i) else none):=by
    induction l with
    | nil => rfl
    | cons i l ih => cases hai:a i <;> simp [hai,ih]
  unfold traceOfMask
  rw [hlist]
  have heq:(Z20 fun i => if a i then some (x i) else none) =
      (List.finRange n).map (fun i => if a i then some (x i) else none):=by
    rw [← List.ofFn_id,List.map_ofFn]
    rfl
  rw [heq,List.filterMap_map]
  rfl
end TraceReconstruction
namespace TraceReconstruction
abbrev Qai:=Fin 4
def QdS:Qai → List Bool:=![[],[false],[true],[false,true]]
def Qck (q:ℝ):Qai → ℝ :=
  ![q ^ 2,q * (1 - q),q * (1 - q),(1 - q) ^ 2]
def QcC (q:ℝ):Qai → ℝ:=![q,0,1 - q,0]
def Qaq (q:ℝ):ℝ:=q ^ 2 / 2
def Qbe (q:ℝ) (isDefect:Bool) (z:Qai):ℝ :=
  ((if isDefect then QcC q z else Qck q z) -
    if z = 0 then Qaq q else 0) / (1 - Qaq q)
theorem Qcw {q:ℝ} (hq:q ∈ Z4 0 1) :
    0 < 1 - Qaq q:=by
  unfold Qaq
  nlinarith [hq.1,hq.2]
theorem QoM {q:ℝ} (hq:q ∈ Z4 0 1)
    (b:Bool) (z:Qai):0 ≤ Qbe q b z:=by
  apply div_nonneg _ (Qcw hq).le
  cases b <;> fin_cases z <;>
    simp [Qck,QcC,Qaq] <;>
    nlinarith [hq.1,hq.2]
theorem Qfy {q:ℝ} (hq:q ∈ Z4 0 1) (b:Bool) :
    ∑ z:Qai,Qbe q b z = 1:=by
  have hd:=ne_of_gt (Qcw hq)
  unfold Qbe
  rw [← Z61]
  apply (div_eq_one_iff_eq hd).mpr
  cases b <;> simp [Qck,QcC,Qaq,Z64]
  all_goals ring
def Qav (q:ℝ) (hq:q ∈ Z4 0 1) (b:Bool):FiniteLaw Qai :=
  ⟨Qbe q b,QoM hq b,Qfy hq b⟩
theorem QoN {q:ℝ} (hq:q ∈ Z4 0 1)
    (b:Bool) (z:Qai) :
    (if z = 0 then Qaq q else 0) +
      (1 - Qaq q) * Qbe q b z =
        if b then QcC q z else Qck q z:=by
  unfold Qbe
  rw [mul_div_cancel₀ _ (ne_of_gt (Qcw hq))]
  ring
def QaA (q:ℝ):Qai → ℝ:=![2 / q - 2,-1,1 / q - 1,-1]
theorem Qik {q:ℝ} (hq:q ∈ Z4 0 1) (z:Qai) :
    Qbe q true z = Qbe q false z * (1 + QaA q z):=by
  have hq0:=ne_of_gt hq.1
  have hd:=ne_of_gt (Qcw hq)
  fin_cases z <;>
    simp [Qbe,Qck,QcC,QaA,Qaq] <;>
    field_simp
  all_goals ring
theorem Qes {q:ℝ} (hq:q ∈ Z4 0 1) :
    ∑ z:Qai,Qbe q false z * QaA q z = 0:=by
  have hi:=Qfy hq true
  simp_rw [Qik hq,mul_add,mul_one,Z14,
    Qfy hq false] at hi
  linarith
theorem QoS {q:ℝ} (hq:q ∈ Z4 0 1) (z:Qai) :
    |QaA q z| ≤ 2 / q:=by
  have hi:1 ≤ 1 / q:=(le_div_iff₀ hq.1).mpr (by linarith [hq.2])
  simp only [one_div] at hi
  have he:2 / q = 2 * (1 / q):=by ring
  fin_cases z <;> simp [QaA,abs_le,he] <;> (try constructor) <;> linarith
theorem QoT {q:ℝ} (hq:q ∈ Z4 0 1) :
    (∑ z:Qai,Qbe q false z * QaA q z ^ 2) =
      (1 / q - 2 * q + q ^ 2) / (1 - q ^ 2 / 2):=by
  have hq0:=ne_of_gt hq.1
  have hd:=ne_of_gt (Qcw hq)
  simp only [Qbe,QaA,Qck,Qaq,
    Bool.false_eq_true,↓reduceIte]
  simp [Z64]
  field_simp
  ring
theorem QoU {q:ℝ} (hq:q ∈ Z4 0 1) :
    (∑ z:Qai,Qbe q false z * QaA q z ^ 2) ≤ 2 / q:=by
  rw [QoT hq]
  have hd:0 < 1 - q ^ 2 / 2:=Qcw hq
  apply (div_le_div_iff₀ hd hq.1).mpr
  rw [add_mul,sub_mul,one_div_mul_cancel (ne_of_gt hq.1)]
  have hpow:q ^ 3 ≤ q ^ 2:=by
    calc
      _ = q ^ 2 * q:=by ring
      _ ≤ q ^ 2 * 1:=mul_le_mul_of_nonneg_left hq.2.le (sq_nonneg _)
      _ = _:=mul_one _
  nlinarith only [hpow,sq_nonneg q]
end TraceReconstruction
namespace TraceReconstruction
def Qbq:ℕ → List Bool
  | 0 => []
  | m + 1 => false :: true :: Qbq m
@[simp] theorem QnQ (m:ℕ):(Qbq m).length = 2 * m:=by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Qbq,List.length_cons,ih]; omega
theorem QnP (a b:ℕ):Qbq (a + b) = Qbq a ++ Qbq b:=by
  induction a with
  | zero => simp [Qbq]
  | succ a ih => simp [Nat.succ_add,Qbq,ih]
def Qam (m d:ℕ):List Bool :=
  Qbq d ++ [true] ++ Qbq (m - 1 - d)
theorem Qml {m d:ℕ} (hd:d < m) :
    (Qam m d).length = 2 * m - 1:=by
  simp only [Qam,List.length_append,QnQ,List.length_singleton]
  omega
theorem Qhl {m d e:ℕ} (hde:d < e) (he:e < m)
    (u v:List Bool):Qam m d ++ u ≠ Qam m e ++ v:=by
  obtain ⟨a,ha⟩:=Nat.exists_eq_add_of_le (show d + 1 ≤ e by omega)
  subst e
  unfold Qam
  rw [Nat.add_assoc d 1 a,QnP d (1 + a)]
  simp only [Nat.add_assoc] at *
  simp only [Nat.one_add,Qbq,List.append_assoc,List.cons_append,List.nil_append]
  intro h
  have hh:=List.append_cancel_left h
  have hf:=congrArg List.head? hh
  simp only [List.head?_cons,Option.some.injEq] at hf
  cases hf
def Qbn (m P:ℕ) (d:Fin P → Fin m):List Bool :=
  (Z20 (fun i => Qam m (d i))).flatten
theorem Qfu (m P:ℕ) (d:Fin (P + 1) → Fin m) :
    Qbn m (P + 1) d = Qam m (d 0) ++
      Qbn m P (fun i => d i.succ):=by
  simp only [Qbn,Z65,List.flatten_cons]
theorem Qol (m P:ℕ) (d:Fin P → Fin m) :
    (Qbn m P d).length = P * (2 * m - 1):=by
  induction P with
  | zero => simp [Qbn]
  | succ P ih =>
    rw [Qfu,List.length_append,Qml (d 0).isLt,ih]
    rw [Nat.add_mul,one_mul,Nat.add_comm]
theorem Qok (m P:ℕ):Z28 (Qbn m P):=by
  induction P with
  | zero => intro d e _; exact Subsingleton.elim _ _
  | succ P ih =>
    intro d e h
    rw [Qfu,Qfu] at h
    have hz:d 0 = e 0:=by
      by_contra hne
      have hv:(d 0).val ≠ (e 0).val:=fun hv => hne (Z34 hv)
      rcases lt_or_gt_of_ne hv with hlt | hgt
      · exact Qhl hlt (e 0).isLt _ _ h
      · exact Qhl hgt (d 0).isLt _ _ h.symm
    rw [hz] at h
    have ht:=ih (List.append_cancel_left h)
    funext i
    refine Z38 hz (fun j => congrFun ht j) i
end TraceReconstruction
namespace TraceReconstruction
end TraceReconstruction
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
namespace TraceReconstruction
end TraceReconstruction
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QcT (χ σ:ℝ):Prop :=
  (χ=0 ∧ σ=0) ∨ (χ=1 ∧ (σ=1 ∨ σ= -1))
def IsTypeSign (τ:ℝ):Prop:=τ=1 ∨ τ= -1
theorem QpI {τ:ℝ} (ht:IsTypeSign τ) (n:ℕ) :
    τ^n = if Odd n then τ else 1:=by
  rcases ht with rfl | rfl
  · simp
  · split_ifs with hn
    · exact hn.neg_one_pow
    · exact (Nat.not_odd_iff_even.mp hn).neg_one_pow
namespace CoefficientShape
end CoefficientShape
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
namespace OccupiedParityTree
end OccupiedParityTree
end TraceReconstruction
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
namespace TraceReconstruction
def Qah (n k:ℕ):ℝ:=(n.choose k:ℝ) / 2 ^ n
theorem Qek (n k:ℕ):0 ≤ Qah n k:=by
  unfold Qah
  positivity
theorem Qgq (n:ℕ) :
    ((n:ℝ) + 1) * (n.centralBinom:ℝ) ^ 2 ≤ (16:ℝ) ^ n:=by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn:(0:ℝ) < n + 1:=by positivity
    have hr:((n:ℝ) + 1) * ((n + 1).centralBinom:ℝ) =
        2 * (2 * n + 1) * (n.centralBinom:ℝ):=by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hc:4 * (2 * (n:ℝ) + 1) ^ 2 * (n + 2) ≤
        16 * (n + 1) ^ 3:=by nlinarith [sq_nonneg (n:ℝ)]
    have hh:((n:ℝ) + 1) ^ 2 *
        ((n + 2) * ((n + 1).centralBinom:ℝ) ^ 2) ≤
        ((n:ℝ) + 1) ^ 2 * (16 * 16 ^ n):=by
      calc
        _ = (n + 2) * (((n:ℝ) + 1) * ((n + 1).centralBinom:ℝ)) ^ 2:=by ring
        _ = (4 * (2 * (n:ℝ) + 1) ^ 2 * (n + 2)) *
            (n.centralBinom:ℝ) ^ 2:=by rw [hr]; ring
        _ ≤ (16 * ((n:ℝ) + 1) ^ 3) * (n.centralBinom:ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ = (16 * ((n:ℝ) + 1) ^ 2) *
            (((n:ℝ) + 1) * (n.centralBinom:ℝ) ^ 2):=by ring
        _ ≤ (16 * ((n:ℝ) + 1) ^ 2) * 16 ^ n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _:=by ring
    have:=(mul_le_mul_iff_right₀ (sq_pos_of_pos hn)).mp hh
    rw [pow_succ (16:ℝ) n]
    convert this using 1 <;> push_cast <;> first | rfl | ring
theorem Qke (n k:ℕ) :
    (2 * n + 1).choose k ≤ 2 * n.centralBinom:=by
  cases k with
  | zero => simp only [Nat.choose_zero_right]; have:=Nat.centralBinom_pos n; omega
  | succ k =>
    rw [Nat.choose_succ_succ]
    have h₁:=Nat.choose_le_centralBinom k n
    have h₂:=Nat.choose_le_centralBinom (k + 1) n
    simpa [Nat.succ_eq_add_one,two_mul] using Nat.add_le_add h₁ h₂
theorem Qlp (n k:ℕ) :
    ((n:ℝ) + 1) * Qah n k ^ 2 ≤ 2:=by
  have hcases:n % 2 = 0 ∨ n % 2 = 1:=Nat.mod_two_eq_zero_or_one n
  rcases hcases with he | ho
  · obtain ⟨m,rfl⟩:∃ m,n = 2 * m:=⟨n / 2,by omega⟩
    have hc:((2 * m).choose k:ℝ) ≤ (m.centralBinom:ℝ) :=
      by exact_mod_cast Nat.choose_le_centralBinom k m
    have hcs:((2 * m).choose k:ℝ) ^ 2 ≤ (m.centralBinom:ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc 2
    have ht:=Qgq m
    have hp:((2:ℝ) ^ (2 * m)) ^ 2 = 16 ^ m:=by
      rw [← pow_mul,show 2 * m * 2 = 4 * m by omega,pow_mul]
      norm_num
    unfold Qah
    rw [div_pow,← mul_div_assoc,div_le_iff₀ (by positivity:(0:ℝ) < (2 ^ (2 * m)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0:ℝ) ≤ m + 1 by positivity),
      sq_nonneg ((2 * m).choose k:ℝ)]
  · obtain ⟨m,rfl⟩:∃ m,n = 2 * m + 1:=⟨n / 2,by omega⟩
    have hc:((2 * m + 1).choose k:ℝ) ≤ 2 * (m.centralBinom:ℝ) :=
      by exact_mod_cast Qke m k
    have hcs:((2 * m + 1).choose k:ℝ) ^ 2 ≤ 4 * (m.centralBinom:ℝ) ^ 2:=by
      have:=pow_le_pow_left₀ (by positivity:(0:ℝ) ≤ ((2 * m + 1).choose k:ℝ)) hc 2
      nlinarith
    have ht:=Qgq m
    have hp:((2:ℝ) ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m:=by
      rw [pow_add,mul_pow,← pow_mul,show 2 * m * 2 = 4 * m by omega,pow_mul]
      norm_num
      ring
    unfold Qah
    rw [div_pow,← mul_div_assoc,div_le_iff₀ (by positivity:(0:ℝ) < (2 ^ (2 * m + 1)) ^ 2)]
    rw [hp]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcs (show (0:ℝ) ≤ m + 1 by positivity)]
abbrev IntSeries:=AddMonoidAlgebra ℝ ℤ
def seriesL1 (f:IntSeries):ℝ:=∑' z:ℤ,|f.coeff z|
def seriesL2Sq (f:IntSeries):ℝ:=∑' z:ℤ,f.coeff z ^ 2
theorem QbU (f:IntSeries) (φ:ℝ → ℝ) (hφ:φ 0 = 0) :
    Summable (fun z:ℤ => φ (f.coeff z)) :=
  summable_of_hasFiniteSupport (f.coeff.hasFiniteSupport.fun_comp hφ)
theorem QbT (f:IntSeries):0 ≤ seriesL1 f :=
  tsum_nonneg fun _ => abs_nonneg _
theorem Qcn (f:IntSeries):0 ≤ seriesL2Sq f :=
  tsum_nonneg fun _ => sq_nonneg _
theorem Qev (f:IntSeries) :
    seriesL1 f = ∑ z ∈ f.coeff.support,|f.coeff z|:=by
  apply tsum_eq_sum
  intro z hz
  simp [Finsupp.notMem_support_iff.mp hz]
theorem QpA (f:IntSeries) :
    seriesL2Sq f = ∑ z ∈ f.coeff.support,f.coeff z ^ 2:=by
  apply tsum_eq_sum
  intro z hz
  simp [Finsupp.notMem_support_iff.mp hz]
theorem QiD (f:IntSeries) (φ:ℝ → ℝ)
    (hφ:φ 0 = 0) (a:ℤ) :
    Summable (fun z:ℤ => φ (f.coeff (a + z))):=by
  exact (Equiv.addLeft a).summable_iff.mpr (QbU f φ hφ)
theorem QiC (f:IntSeries) (φ:ℝ → ℝ) (a:ℤ) :
    (∑' z:ℤ,φ (f.coeff (a + z))) = ∑' z:ℤ,φ (f.coeff z) :=
  (Equiv.addLeft a).tsum_eq (fun z => φ (f.coeff z))
theorem QiB (f g:IntSeries) (z:ℤ) :
    |(f * g).coeff z| ≤ ∑ a ∈ f.coeff.support,|f.coeff a| * |g.coeff (-a + z)|:=by
  rw [Z79,Finsupp.sum]
  simpa only [abs_mul] using Z70
    (fun a => f.coeff a * g.coeff (-a + z)) f.coeff.support
theorem Qiv (f g:IntSeries) :
    seriesL1 (f * g) ≤ seriesL1 f * seriesL1 g:=by
  have hh (a:ℤ):Summable (fun z:ℤ => |f.coeff a| * |g.coeff (-a + z)|) :=
    (QiD g abs (by simp) (-a)).mul_left _
  calc
    seriesL1 (f * g) ≤ ∑' z:ℤ,∑ a ∈ f.coeff.support,
        |f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_le_tsum (QiB f g) (QbU (f * g) abs (by simp))
        (summable_sum fun a _ => hh a)
    _ = ∑ a ∈ f.coeff.support,∑' z:ℤ,|f.coeff a| * |g.coeff (-a + z)| :=
      Summable.tsum_finsetSum fun a _ => hh a
    _ = (∑ a ∈ f.coeff.support,|f.coeff a|) * seriesL1 g:=by
      simp_rw [tsum_mul_left,QiC]
      exact (Z33 _ _ _).symm
    _ = seriesL1 f * seriesL1 g:=by rw [Qev f]
theorem QpC (f g:IntSeries) (z:ℤ) :
    (f * g).coeff z ^ 2 ≤ seriesL1 f *
      ∑ a ∈ f.coeff.support,|f.coeff a| * (g.coeff (-a + z)) ^ 2:=by
  rw [Z79,Finsupp.sum,Qev]
  apply Z84
  · intro a _; exact abs_nonneg _
  · intro a _; positivity
  · intro a _
    rw [mul_pow,← mul_assoc,← sq,sq_abs]
theorem Qdu (f g:IntSeries) :
    seriesL2Sq (f * g) ≤ seriesL1 f ^ 2 * seriesL2Sq g:=by
  have hh (a:ℤ):Summable (fun z:ℤ => |f.coeff a| * (g.coeff (-a + z)) ^ 2) :=
    (QiD g (fun x => x ^ 2) (by simp) (-a)).mul_left _
  calc
    seriesL2Sq (f * g) ≤ ∑' z:ℤ,seriesL1 f *
        ∑ a ∈ f.coeff.support,|f.coeff a| * (g.coeff (-a + z)) ^ 2 :=
      Summable.tsum_le_tsum (QpC f g)
        (QbU (f * g) (fun x => x ^ 2) (by simp))
        ((summable_sum fun a _ => hh a).mul_left _)
    _ = seriesL1 f * ∑ a ∈ f.coeff.support,
        ∑' z:ℤ,|f.coeff a| * (g.coeff (-a + z)) ^ 2:=by
      rw [tsum_mul_left,Summable.tsum_finsetSum fun a _ => hh a]
    _ = seriesL1 f ^ 2 * seriesL2Sq g:=by
      simp_rw [tsum_mul_left,QiC g (fun x => x ^ 2)]
      rw [← Z33,← Qev]
      unfold seriesL2Sq
      ring
theorem QdX (f g:IntSeries) (M:ℝ)
    (hg:∀ z,|g.coeff z| ≤ M) (z:ℤ) :
    |(f * g).coeff z| ≤ seriesL1 f * M:=by
  calc
    _ ≤ ∑ a ∈ f.coeff.support,|f.coeff a| * |g.coeff (-a + z)| :=
      QiB f g z
    _ ≤ ∑ a ∈ f.coeff.support,|f.coeff a| * M :=
      Z7 fun a _ => mul_le_mul_of_nonneg_left (hg _) (abs_nonneg _)
    _ = seriesL1 f * M:=by rw [← Z33,← Qev]
def fairSeries (n:ℕ):IntSeries :=
  (Z29 1 (1 / 2) + Z29 0 (1 / 2)) ^ n
theorem QgQ (m n:ℕ):fairSeries (m + n) = fairSeries m * fairSeries n :=
  pow_add _ m n
theorem Qel (n:ℕ) :
    fairSeries n = ∑ k ∈ Z5 (n + 1),
      Z29 (k:ℤ) (Qah n k):=by
  unfold fairSeries
  rw [add_pow]
  apply Z2 rfl
  intro k hk
  have hkn:k ≤ n:=by simpa only [Z57,Nat.lt_succ_iff] using hk
  rw [Z80,Z80,
    AddMonoidAlgebra.natCast_def,Z85,
    Z85]
  simp only [nsmul_eq_mul,mul_one,mul_zero,add_zero]
  congr 1
  rw [← pow_add,Nat.add_sub_of_le hkn]
  unfold Qah
  rw [div_pow]
  simp [div_eq_mul_inv,mul_comm]
theorem Qct (n k:ℕ) :
    (fairSeries n).coeff (k:ℤ) = Qah n k:=by
  rw [Qel,Z58,Z73]
  by_cases hk:k ≤ n
  · rw [Z86 k]
    · simp only [Z41,Z42,ite_true]
    · intro b _ hb
      simp only [Z41,Z42,Nat.cast_inj,if_neg hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [Z81]
    · simp [Qah,Z44 (by omega:n < k)]
    · intro b hb
      have hbk:b ≠ k:=by simp only [Z57] at hb; omega
      simp only [Z41,Z42,Nat.cast_inj,if_neg hbk]
theorem QcD (n:ℕ) (z:ℤ) (hz:z < 0) :
    (fairSeries n).coeff z = 0:=by
  rw [Qel,Z58,Z73]
  apply Z81
  intro b _
  have h:(b:ℤ) ≠ z:=by omega
  simp only [Z41,Z42,if_neg h]
theorem QfE (f:IntSeries) (n:ℕ)
    (hneg:∀ z < 0,f.coeff z = 0)
    (hhigh:∀ k:ℕ,n < k → f.coeff k = 0) :
    seriesL1 f = ∑ k ∈ Z5 (n + 1),|f.coeff (k:ℤ)|:=by
  let e:ℕ ↪ ℤ:=⟨Nat.cast,Nat.cast_injective⟩
  calc
    seriesL1 f = ∑ z ∈ (Z5 (n + 1)).map e,|f.coeff z|:=by
      apply tsum_eq_sum
      intro z hz
      by_cases h:0 ≤ z
      · have heq:((z.toNat:ℕ):ℤ) = z:=Z95 h
        have hh:n < z.toNat:=by
          by_contra hn
          apply hz
          exact Finset.mem_map.mpr ⟨z.toNat,Finset.mem_range.mpr (by omega),heq⟩
        rw [← heq,hhigh _ hh,abs_zero]
      · rw [hneg z (by omega),abs_zero]
    _ = _:=Finset.sum_map _ e _
def Qas:IntSeries :=
  Z29 0 1 - Z29 1 1
theorem QdF (f:IntSeries) (z:ℤ) :
    (Qas * f).coeff z = f.coeff z - f.coeff (z - 1):=by
  rw [Qas,sub_mul,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
    mul_comm _ f,Z105,
    mul_comm _ f,Z105]
  simp only [neg_zero,add_zero,mul_one,sub_eq_add_neg]
theorem Qlv (n:ℕ) :
    (Qas * fairSeries n).coeff 0 = Qah n 0:=by
  rw [QdF]
  norm_num only [zero_sub]
  rw [QcD n (-1) (by norm_num),sub_zero]
  exact Qct n 0
theorem QgR (n k:ℕ) :
    (Qas * fairSeries n).coeff (↑(k + 1):ℤ) =
      Qah n (k + 1) - Qah n k:=by
  rw [QdF,Qct]
  simp only [Z23,Z25,add_sub_cancel_right,Qct]
theorem Qlq (n k:ℕ) (hk:k < n / 2) :
    Qah n k ≤ Qah n (k + 1):=by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_succ_of_lt_half_left hk
theorem Qlr (n k:ℕ) (hk:n / 2 ≤ k) :
    Qah n (k + 1) ≤ Qah n k:=by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hnk:n - k ≤ k + 1:=by omega
  have hmul:=Nat.mul_le_mul_left (n.choose k) hnk
  rw [← Nat.choose_succ_right_eq] at hmul
  exact_mod_cast Nat.le_of_mul_le_mul_right hmul (by omega:0 < k + 1)
theorem Qls (n:ℕ) :
    (∑ k ∈ Z5 (n + 1),|Qah n (k + 1) - Qah n k|) =
      2 * Qah n (n / 2) - Qah n 0:=by
  have hmid:n / 2 ≤ n + 1:=by omega
  rw [← Finset.sum_range_add_sum_Ico _ hmid]
  have hl:(∑ k ∈ Z5 (n / 2),
      |Qah n (k + 1) - Qah n k|) =
      Qah n (n / 2) - Qah n 0:=by
    rw [← Finset.sum_range_sub (Qah n) (n / 2)]
    apply Z2 rfl
    intro k hk
    exact abs_of_nonneg (sub_nonneg.mpr
      (Qlq n k (Finset.mem_range.mp hk)))
  have hr:(∑ k ∈ Finset.Ico (n / 2) (n + 1),
      |Qah n (k + 1) - Qah n k|) =
      Qah n (n / 2) - Qah n (n + 1):=by
    calc
      _ = ∑ k ∈ Finset.Ico (n / 2) (n + 1),
          -(Qah n (k + 1) - Qah n k):=by
        apply Z2 rfl
        intro k hk
        exact abs_of_nonpos (sub_nonpos.mpr
          (Qlr n k (Finset.mem_Ico.mp hk).1))
      _ = _:=by rw [Finset.sum_neg_distrib,Finset.sum_Ico_sub _ hmid]; ring
  rw [hl,hr]
  have hzero:Qah n (n + 1) = 0:=by simp [Qah]
  rw [hzero]
  ring
theorem Qlu (n:ℕ) :
    seriesL1 (Qas * fairSeries n) = 2 * Qah n (n / 2):=by
  rw [QfE _ (n + 1)]
  · rw [Finset.sum_range_succ',Nat.cast_zero,Qlv,
      abs_of_nonneg (Qek n 0)]
    simp_rw [QgR]
    rw [Qls]
    ring
  · intro z hz
    rw [QdF,QcD n z hz,
      QcD n (z - 1) (by omega),sub_zero]
  · intro k hk
    have hkpos:0 < k:=by omega
    obtain ⟨v,rfl⟩:=Z106 (Nat.ne_of_gt hkpos)
    rw [QgR]
    simp [Qah,Z44 (by omega:n < v),
      Z44 (by omega:n < v + 1)]
def Qar (n:ℕ):ℝ:=Z0 (2 / ((n:ℝ) + 1))
theorem QeO (n:ℕ):0 ≤ Qar n:=Z36 _
theorem QgO (n k:ℕ):Qah n k ≤ Qar n:=by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity:(0:ℝ) < n + 1)).mpr
  simpa only [mul_comm] using Qlp n k
theorem Qlw (n:ℕ) (z:ℤ):0 ≤ (fairSeries n).coeff z:=by
  by_cases hz:0 ≤ z
  · rw [← Z95 hz,Qct]
    exact Qek _ _
  · rw [QcD n z (by omega)]
theorem Qfb (n:ℕ) (z:ℤ) :
    |(fairSeries n).coeff z| ≤ Qar n:=by
  by_cases hz:0 ≤ z
  · rw [← Z95 hz,Qct,
      abs_of_nonneg (Qek _ _)]
    exact QgO _ _
  · rw [QcD n z (by omega),abs_zero]
    exact QeO n
theorem Qfa (n:ℕ):seriesL1 (fairSeries n) = 1:=by
  rw [QfE _ n (QcD n)]
  · simp_rw [Qct,abs_of_nonneg (Qek _ _)]
    unfold Qah
    rw [← Z61]
    have hsum:(∑ k ∈ Z5 (n + 1),(n.choose k:ℝ)) = (2:ℝ) ^ n:=by
      exact_mod_cast Nat.sum_range_choose n
    rw [hsum,div_self (by positivity)]
  · intro k hk
    rw [Qct]
    simp [Qah,Z44 hk]
theorem Qiz (f:IntSeries) (M:ℝ)
    (hf:∀ z,|f.coeff z| ≤ M):seriesL2Sq f ≤ seriesL1 f * M:=by
  calc
    _ ≤ ∑' z:ℤ,|f.coeff z| * M:=by
      apply Summable.tsum_le_tsum
      · intro z
        calc
          f.coeff z ^ 2 = |f.coeff z| * |f.coeff z|:=by rw [← sq,sq_abs]
          _ ≤ _:=mul_le_mul_of_nonneg_left (hf z) (abs_nonneg _)
      · exact QbU f (fun x => x ^ 2) (by simp)
      · exact (QbU f abs (by simp)).mul_right M
    _ = _:=tsum_mul_right
theorem QgP (n:ℕ):seriesL2Sq (fairSeries n) ≤ Qar n:=by
  simpa only [Qfa,one_mul] using Qiz (fairSeries n) (Qar n) (Qfb n)
theorem Qfc (n:ℕ) :
    seriesL1 (Qas * fairSeries n) ≤ 2 * Qar n:=by
  rw [Qlu]
  exact mul_le_mul_of_nonneg_left (QgO n (n / 2)) (by norm_num)
theorem Qix (z:ℤ) (r:ℝ) :
    seriesL1 (Z29 z r) = |r|:=by
  unfold seriesL1
  simp only [Z41,Z42]
  simp only [apply_ite abs,abs_zero]
  exact tsum_ite_eq' z (fun _:ℤ => |r|)
theorem Qiw:seriesL1 (1:IntSeries) = 1:=by
  change seriesL1 (Z29 0 1) = 1
  rw [Qix,abs_one]
theorem Qew (f:IntSeries) (s:ℕ):seriesL1 (f ^ s) ≤ seriesL1 f ^ s:=by
  induction s with
  | zero => simp only [pow_zero,Qiw,le_refl]
  | succ s ih =>
    rw [pow_succ,pow_succ]
    exact (Qiv _ _).trans
      (mul_le_mul_of_nonneg_right ih (QbT f))
theorem QgS (n s:ℕ) :
    Qas ^ s * fairSeries ((s + 1) * n) =
      (Qas * fairSeries n) ^ s * fairSeries n:=by
  simp only [fairSeries,add_mul,one_mul,pow_add,pow_mul,mul_pow]
  ring
theorem QjU (n s:ℕ) (z:ℤ) :
    |(Qas ^ s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2 * Qar n) ^ s * Qar n:=by
  rw [QgS]
  apply (QdX _ _ _ (Qfb n) z).trans
  apply mul_le_mul_of_nonneg_right _ (QeO n)
  exact (Qew _ _).trans
    (pow_le_pow_left₀ (QbT _) (Qfc n) s)
theorem QjT (n s:ℕ) :
    seriesL2Sq (Qas ^ s * fairSeries ((s + 1) * n)) ≤
      ((2 * Qar n) ^ s) ^ 2 * Qar n:=by
  rw [QgS]
  apply (Qdu _ _).trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (QbT _)
    exact (Qew _ _).trans
      (pow_le_pow_left₀ (QbT _) (Qfc n) s)
  · exact QgP n
  · exact Qcn _
  · positivity
theorem Qpw (f g:IntSeries) :
    seriesL1 (f + g) ≤ seriesL1 f + seriesL1 g:=by
  calc
    _ ≤ ∑' z:ℤ,(|f.coeff z| + |g.coeff z|):=by
      apply Summable.tsum_le_tsum
      · intro z
        simpa only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply] using abs_add_le (f.coeff z) (g.coeff z)
      · exact QbU (f + g) abs (by simp)
      · exact (QbU f abs (by simp)).add (QbU g abs (by simp))
    _ = _:=(QbU f abs (by simp)).tsum_add (QbU g abs (by simp))
theorem Qpz:seriesL1 (0:IntSeries) = 0:=by
  simp [seriesL1]
theorem Qiy {ι:Type*} (A:Finset ι) (f:ι → IntSeries) :
    seriesL1 (∑ i ∈ A,f i) ≤ ∑ i ∈ A,seriesL1 (f i):=by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Qpz,le_refl]
  | @insert a A ha ih =>
    rw [Z87 ha,Z87 ha]
    exact (Qpw _ _).trans (add_le_add le_rfl ih)
theorem Qpx {ι:Type*} (A:Finset ι) (f:ι → IntSeries) :
    seriesL1 (∏ i ∈ A,f i) ≤ ∏ i ∈ A,seriesL1 (f i):=by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Qiw,le_refl]
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha]
    exact (Qiv _ _).trans (mul_le_mul_of_nonneg_left ih (QbT _))
def geomSeries (k:ℕ):IntSeries:=∑ a ∈ Z5 k,(Z29 1 1) ^ a
def Qak (s:ℕ):IntSeries :=
  ∏ v ∈ Z5 s,(1 - (Z29 1 1) ^ (2 ^ v))
def QfA (s:ℕ):IntSeries :=
  ∏ v ∈ Z5 s,geomSeries (2 ^ v)
theorem QlU (k:ℕ) :
    geomSeries k * Qas = 1 - (Z29 1 1:IntSeries) ^ k:=by
  exact geom_sum_mul_neg _ _
theorem Qhd (k:ℕ):seriesL1 (geomSeries k) ≤ k:=by
  apply (Qiy _ _).trans
  simp only [Z80,one_pow,Qix,abs_one,
    Z59,Finset.card_range,nsmul_eq_mul,mul_one,le_refl]
theorem Qip (s:ℕ) :
    Qak s = QfA s * Qas ^ s:=by
  unfold Qak QfA
  simp_rw [← QlU]
  rw [Z30]
  simp only [Z78,Finset.card_range]
theorem Qio (s:ℕ) :
    seriesL1 (QfA s) ≤ (2:ℝ) ^ (s * s):=by
  calc
    _ ≤ ∏ v ∈ Z5 s,seriesL1 (geomSeries (2 ^ v)):=Qpx _ _
    _ ≤ ∏ _v ∈ Z5 s,((2:ℝ) ^ s):=by
      apply Z45
      · intro v _; exact QbT _
      · intro v hv
        apply (Qhd _).trans
        push_cast
        apply pow_le_pow_right₀ (by norm_num:(1:ℝ) ≤ 2)
        exact (Finset.mem_range.mp hv).le
    _ = _:=by simp only [Z78,Finset.card_range,← pow_mul]
theorem Qpc (n s:ℕ) (z:ℤ) :
    |(Qak s * fairSeries ((s + 1) * n)).coeff z| ≤
      (2:ℝ) ^ (s * s) * ((2 * Qar n) ^ s * Qar n):=by
  rw [Qip,mul_assoc]
  apply (QdX _ _ _ (QjU n s) z).trans
  exact mul_le_mul_of_nonneg_right (Qio s)
    (by positivity [QeO n])
theorem Qpa (n s:ℕ) :
    seriesL2Sq (Qak s * fairSeries ((s + 1) * n)) ≤
      ((2:ℝ) ^ (s * s)) ^ 2 * (((2 * Qar n) ^ s) ^ 2 * Qar n):=by
  rw [Qip,mul_assoc]
  apply (Qdu _ _).trans
  apply mul_le_mul
  · exact pow_le_pow_left₀ (QbT _) (Qio s) 2
  · exact QjT n s
  · exact Qcn _
  · positivity
theorem Qpd (n s r:ℕ) (z:ℤ) :
    |(Qak s * fairSeries ((s + 1) * n + r)).coeff z| ≤
      (2:ℝ) ^ (s * s) * ((2 * Qar n) ^ s * Qar n):=by
  rw [QgQ,← mul_assoc,mul_comm (Qak s * _)]
  simpa only [Qfa,one_mul] using QdX (fairSeries r) (Qak s * fairSeries ((s + 1) * n))
      _ (Qpc n s) z
theorem Qpb (n s r:ℕ) :
    seriesL2Sq (Qak s * fairSeries ((s + 1) * n + r)) ≤
      ((2:ℝ) ^ (s * s)) ^ 2 * (((2 * Qar n) ^ s) ^ 2 * Qar n):=by
  rw [QgQ,← mul_assoc,mul_comm (Qak s * _)]
  calc
    _ ≤ seriesL1 (fairSeries r) ^ 2 *
        seriesL2Sq (Qak s * fairSeries ((s + 1) * n)):=Qdu _ _
    _ ≤ _:=by simpa only [Qfa,one_pow,one_mul] using Qpa n s
theorem QpT (g s:ℕ) :
    (∀ z:ℤ,|(Qak s * fairSeries g).coeff z| ≤
      (2:ℝ) ^ (s * s) * ((2 * Qar (g / (s + 1))) ^ s *
        Qar (g / (s + 1)))) ∧
    (seriesL2Sq (Qak s * fairSeries g) ≤
      ((2:ℝ) ^ (s * s)) ^ 2 * (((2 * Qar (g / (s + 1))) ^ s) ^ 2 *
        Qar (g / (s + 1)))):=by
  have hg:(s + 1) * (g / (s + 1)) + g % (s + 1) = g:=Nat.div_add_mod g (s + 1)
  constructor
  · intro z
    simpa only [hg] using Qpd (g / (s + 1)) s
      (g % (s + 1)) z
  · simpa only [hg] using Qpb (g / (s + 1)) s
      (g % (s + 1))
theorem QjD (g s:ℕ) :
    Qar (g / (s + 1)) ≤
      Z0 (2 * ((s:ℝ) + 1) / ((g:ℝ) + 1)):=by
  apply Z24
  have hn:g + 1 ≤ (g / (s + 1) + 1) * (s + 1):=by
    have hmod:=Nat.mod_lt g (by omega:0 < s + 1)
    have hdiv:=Nat.div_add_mod g (s + 1)
    nlinarith
  have hnr:(g:ℝ) + 1 ≤ ((g / (s + 1):ℕ) + (1:ℝ)) * ((s:ℝ) + 1):=by
    exact_mod_cast hn
  apply (div_le_div_iff₀ (by positivity:(0:ℝ) < (g / (s + 1):ℕ) + 1)
    (by positivity:(0:ℝ) < g + 1)).mpr
  nlinarith
theorem QfB (s:ℕ) (z:ℤ) :
    (Qak (s + 1)).coeff z =
    (Qak s).coeff z - (Qak s).coeff (z - (2 ^ s:ℕ)):=by
  rw [Qak,Finset.prod_range_succ,mul_sub,mul_one]
  change (Qak s - Qak s *
    (Z29 1 1:IntSeries) ^ (2 ^ s)).coeff z = _
  rw [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply]
  simp only [Z80,one_pow,nsmul_eq_mul,mul_one,
    Z105,sub_eq_add_neg]
theorem QdT (s:ℕ) :
    (∀ z:ℤ,(z < 0 ∨ (2 ^ s:ℕ) ≤ z) → (Qak s).coeff z = 0) ∧
    (∀ z:ℤ,0 ≤ z → z < (2 ^ s:ℕ) → |(Qak s).coeff z| = 1):=by
  induction s with
  | zero =>
    have hcoeff (z:ℤ):(Qak 0).coeff z = if 0 = z then 1 else 0:=by
      change (Z29 0 (1:ℝ)).coeff z = _
      exact Z42
    constructor
    · intro z hz
      rw [hcoeff,if_neg]
      norm_num only [pow_zero,Z25] at hz
      omega
    · intro z h0 h1
      have hz:z = 0:=by norm_num only [pow_zero,Z25] at h1; omega
      subst hz
      rw [hcoeff,if_pos rfl,abs_one]
  | succ s ih =>
    have hp:(0:ℤ) < (2 ^ s:ℕ):=by positivity
    have hd:((2 ^ (s + 1):ℕ):ℤ) = 2 * (2 ^ s:ℕ):=by push_cast; ring
    constructor
    · intro z hz
      rw [QfB]
      rcases hz with hz | hz
      · rw [ih.1 z (Or.inl hz),ih.1 _ (Or.inl (by omega)),sub_zero]
      · rw [hd] at hz
        rw [ih.1 z (Or.inr (by omega)),ih.1 _ (Or.inr (by omega)),sub_zero]
    · intro z h0 h1
      rw [hd] at h1
      rw [QfB]
      by_cases hz:z < (2 ^ s:ℕ)
      · rw [ih.1 (z - (2 ^ s:ℕ)) (Or.inl (by omega)),sub_zero]
        exact ih.2 z h0 hz
      · rw [ih.1 z (Or.inr (by omega)),zero_sub,abs_neg]
        exact ih.2 _ (by omega) (by omega)
def Qaa (n:ℕ) (p:ℝ) (k:ℕ):ℝ :=
  (n.choose k:ℝ) * p ^ k * (1 - p) ^ (n - k)
theorem QaF (n k:ℕ) {p:ℝ} (hp:p ∈ Z6 0 1) :
    0 ≤ Qaa n p k:=by
  unfold Qaa
  positivity [hp.1,sub_nonneg.mpr hp.2]
theorem Qcg (n:ℕ) (p:ℝ) :
    ∑ k ∈ Z5 (n + 1),Qaa n p k = 1:=by
  have h:=add_pow p (1 - p) n
  rw [show p + (1 - p) = 1 by ring,one_pow] at h
  rw [h]
  apply Z2 rfl
  intro k _
  unfold Qaa
  ring
theorem Qgf (n k:ℕ) (p:ℝ) :
    ((n:ℝ) + 1) * p * (Qaa n p k / ((k:ℝ) + 1)) =
      Qaa (n + 1) p (k + 1):=by
  have hc:((n:ℝ) + 1) * (n.choose k:ℝ) =
      ((n + 1).choose (k + 1):ℝ) * ((k:ℝ) + 1):=by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  unfold Qaa
  rw [Nat.add_sub_add_right,pow_succ]
  field_simp
  nlinarith [congrArg (fun x:ℝ => x * p ^ k * (1 - p) ^ (n - k) * p) hc]
theorem QjH (n:ℕ) (p:ℝ) :
    ((n:ℝ) + 1) * p *
      (∑ k ∈ Z5 (n + 1),Qaa n p k / ((k:ℝ) + 1)) =
    1 - (1 - p) ^ (n + 1):=by
  rw [Z3]
  simp_rw [Qgf]
  have h:=Qcg (n + 1) p
  rw [Finset.sum_range_succ'] at h
  simp only [Qaa,Nat.choose_zero_right,Z25,pow_zero,
    mul_one,one_mul,Nat.sub_zero] at h ⊢
  linarith
theorem QjI (n:ℕ) {p:ℝ} (hp:p ∈ Z12 0 1) :
    (∑ k ∈ Z5 (n + 1),Qaa n p k / ((k:ℝ) + 1)) ≤
      1 / (((n:ℝ) + 1) * p):=by
  apply (le_div_iff₀ (mul_pos (by positivity) hp.1)).mpr
  rw [mul_comm,QjH]
  have h:=pow_nonneg (sub_nonneg.mpr hp.2) (n + 1)
  linarith
theorem Qjf {ι:Type*} (S:Finset ι) (w f:ι → ℝ)
    (hw:∀ i,0 ≤ w i) :
    (∑ i ∈ S,w i * f i) ^ 2 ≤ (∑ i ∈ S,w i) * ∑ i ∈ S,w i * f i ^ 2:=by
  have heq (i:ι):w i * f i = Z0 (w i) * (Z0 (w i) * f i):=by
    rw [← mul_assoc,← sq,Z13 (hw i)]
  simp_rw [heq]
  apply (Z104 S (fun i => Z0 (w i))
    (fun i => Z0 (w i) * f i)).trans_eq
  simp only [mul_pow,Z13 (hw _)]
theorem QhI (n:ℕ) {p:ℝ} (hp:p ∈ Z12 0 1) :
    (∑ k ∈ Z5 (n + 1),Qaa n p k * Qar k) ≤
      Z0 (2 / (((n:ℝ) + 1) * p)):=by
  have hw (k:ℕ):=QaF n k (show p ∈ Z6 0 1 from ⟨hp.1.le,hp.2⟩)
  have hs:=Qjf (Z5 (n + 1)) (Qaa n p)
    Qar hw
  rw [Qcg,one_mul] at hs
  have hb (k:ℕ):Qar k ^ 2 = 2 / ((k:ℝ) + 1) :=
    Z13 (by positivity)
  simp_rw [hb] at hs
  have heq:(∑ k ∈ Z5 (n + 1),Qaa n p k * (2 / ((k:ℝ) + 1))) =
      2 * ∑ k ∈ Z5 (n + 1),Qaa n p k / ((k:ℝ) + 1):=by
    rw [Z3]
    apply Z2 rfl
    intro k _
    ring
  rw [heq] at hs
  have hh:=QjI n hp
  have hp0:=hp.1
  have hbound:(∑ k ∈ Z5 (n + 1),Qaa n p k * Qar k) ^ 2 ≤
      2 / (((n:ℝ) + 1) * p):=by
    calc
      _ ≤ 2 * ∑ k ∈ Z5 (n + 1),Qaa n p k / ((k:ℝ) + 1):=hs
      _ ≤ 2 * (1 / (((n:ℝ) + 1) * p)):=mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _:=by ring
  have hsr:=Z13 (show (0:ℝ) ≤ 2 / (((n:ℝ) + 1) * p) by positivity)
  have hpos:=Z36 (2 / (((n:ℝ) + 1) * p))
  nlinarith only [hbound,hsr,hpos]
def Qdo (n:ℕ) (p:ℝ):IntSeries :=
  (p • fairSeries 1 + (1 - p) • (1:IntSeries)) ^ n
def Qaf (n:ℕ) (p:ℝ):IntSeries :=
  (Z29 1 p + Z29 0 (1 - p)) ^ n
theorem QhF (n:ℕ) (p:ℝ) :
    Qdo n p =
      ∑ k ∈ Z5 (n + 1),Qaa n p k • fairSeries k:=by
  rw [Qdo,add_pow]
  apply Z2 rfl
  intro k _
  simp only [smul_pow,one_pow,smul_mul_smul,mul_one,fairSeries,pow_one]
  rw [mul_comm,← nsmul_eq_mul,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  congr 1
  unfold Qaa
  ring
theorem QhE (n:ℕ) (p:ℝ) :
    Qdo n p = Qaf n (p / 2):=by
  unfold Qdo Qaf
  congr 1
  ext z
  simp only [fairSeries,pow_one,smul_add,AddMonoidAlgebra.one_def,AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply,Z88,Z89,
    smul_eq_mul,Z41,Z42]
  split_ifs <;> first | omega | ring
theorem Qnd (n:ℕ) {p:ℝ} (hp:p ∈ Z12 0 1) (z:ℤ) :
    |(Qdo n p).coeff z| ≤ Z0 (2 / (((n:ℝ) + 1) * p)):=by
  rw [QhF,Z58,Z73]
  simp only [Z88,Z89,smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Z5 (n + 1),|Qaa n p k * (fairSeries k).coeff z| :=
      Z70 _ _
    _ ≤ ∑ k ∈ Z5 (n + 1),Qaa n p k * Qar k:=by
      apply Z7
      intro k _
      have hw:=QaF n k (show p ∈ Z6 0 1 from ⟨hp.1.le,hp.2⟩)
      rw [abs_mul,abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (Qfb k z) hw
    _ ≤ _:=QhI n hp
theorem QfX (n:ℕ) {p:ℝ}
    (hp:p ∈ Z12 0 (1 / 2)) (z:ℤ) :
    |(Qaf n p).coeff z| ≤ Z0 (1 / (((n:ℝ) + 1) * p)):=by
  have h2p:2 * p ∈ Z12 0 1:=⟨by linarith [hp.1],by linarith [hp.2]⟩
  have h:=Qnd n h2p z
  rw [QhE,show 2 * p / 2 = p by ring] at h
  have heq:2 / (((n:ℝ) + 1) * (2 * p)) = 1 / (((n:ℝ) + 1) * p):=by
    field_simp
  rwa [heq] at h
theorem QeN (n:ℕ) (p:ℝ) :
    Qaf n p = ∑ k ∈ Z5 (n + 1),
      Z29 (k:ℤ) (Qaa n p k):=by
  rw [Qaf,add_pow]
  apply Z2 rfl
  intro k _
  rw [Z80,Z80,
    AddMonoidAlgebra.natCast_def,Z85,
    Z85]
  simp only [nsmul_eq_mul,mul_one,mul_zero,add_zero]
  congr 1
  unfold Qaa
  ring
theorem QcV (n k:ℕ) (p:ℝ) :
    (Qaf n p).coeff (k:ℤ) = Qaa n p k:=by
  rw [QeN,Z58,Z73]
  by_cases hk:k ≤ n
  · rw [Z86 k]
    · simp only [Z41,Z42,ite_true]
    · intro b _ hb
      simp only [Z41,Z42,Nat.cast_inj,if_neg hb]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [Z81]
    · simp [Qaa,Z44 (by omega:n < k)]
    · intro b hb
      have hbk:b ≠ k:=by simp only [Z57] at hb; omega
      simp only [Z41,Z42,Nat.cast_inj,if_neg hbk]
theorem QeL (n:ℕ) (p:ℝ) (z:ℤ) (hz:z < 0) :
    (Qaf n p).coeff z = 0:=by
  rw [QeN,Z58,Z73]
  apply Z81
  intro b _
  have h:(b:ℤ) ≠ z:=by omega
  simp only [Z41,Z42,if_neg h]
theorem QeK (n:ℕ) (p:ℝ) (z:ℤ) (hz:(n:ℤ) < z) :
    (Qaf n p).coeff z = 0:=by
  rw [QeN,Z58,Z73]
  apply Z81
  intro b hb
  have h:(b:ℤ) ≠ z:=by simp only [Z57] at hb; omega
  simp only [Z41,Z42,if_neg h]
theorem QjQ (n k:ℕ) (p:ℝ) (hk:k ≤ n) :
    Qaa n (1 - p) (n - k) = Qaa n p k:=by
  unfold Qaa
  rw [Nat.choose_symm hk,Nat.sub_sub_self hk,show 1 - (1 - p) = p by ring]
  ring
theorem QeM (n:ℕ) (p:ℝ) (z:ℤ) :
    (Qaf n (1 - p)).coeff ((n:ℤ) - z) = (Qaf n p).coeff z:=by
  by_cases hz:z < 0
  · rw [QeL n p z hz,
      QeK n (1 - p) _ (by omega)]
  by_cases hz':(n:ℤ) < z
  · rw [QeK n p z hz',
      QeL n (1 - p) _ (by omega)]
  have h0:0 ≤ z:=by omega
  have hk:z.toNat ≤ n:=by omega
  have hzN:(z.toNat:ℤ) = z:=Z95 h0
  have hsub:(n:ℤ) - z = ((n - z.toNat:ℕ):ℤ):=by omega
  rw [hsub,← hzN,QcV,QcV]
  exact QjQ n z.toNat p hk
theorem Qed (n:ℕ) {p:ℝ}
    (hp:p ∈ Z4 0 1) (z:ℤ) :
    |(Qaf n p).coeff z| ≤
      Z0 (1 / (((n:ℝ) + 1) * p * (1 - p))):=by
  by_cases hlow:p ≤ 1 / 2
  · apply (QfX n ⟨hp.1,hlow⟩ z).trans
    apply Z24
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · have hn:(0:ℝ) ≤ n + 1:=by positivity
      nlinarith [mul_nonneg hn (sq_nonneg p)]
  · have hq:1 - p ∈ Z12 0 (1 / 2):=⟨by linarith [hp.2],by linarith⟩
    rw [← QeM n p z]
    apply (QfX n hq ((n:ℤ) - z)).trans
    apply Z24
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ n + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hp.2.le) (sub_nonneg.mpr hp.2.le))]
theorem QjN (n k:ℕ) (p:ℝ) :
    Qaa (n + 1) p (k + 1) * ((k:ℝ) + 1) =
      ((n:ℝ) + 1) * p * Qaa n p k:=by
  have h:=Qgf n k p
  have hk:((k:ℝ) + 1) ≠ 0:=by positivity
  rw [← h]
  field_simp
theorem Qgg (n:ℕ) (p:ℝ) (F:ℕ → ℝ) :
    (∑ k ∈ Z5 (n + 2),Qaa (n + 1) p k * (k:ℝ) * F k) =
      ((n:ℝ) + 1) * p *
        ∑ k ∈ Z5 (n + 1),Qaa n p k * F (k + 1):=by
  rw [show n + 2 = (n + 1) + 1 by omega,Finset.sum_range_succ']
  simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero,Z23,Z25]
  simp_rw [QjN]
  rw [Z3]
  apply Z2 rfl
  intro k _
  ring
theorem Qgi (n:ℕ) (p:ℝ) :
    ∑ k ∈ Z5 (n + 1),Qaa n p k * (k:ℝ) = (n:ℝ) * p:=by
  cases n with
  | zero => simp
  | succ n =>
    simpa only [mul_one,Qcg,Z23,Z25] using Qgg n p (fun _ => 1)
theorem QjP (n:ℕ) (p:ℝ) :
    ∑ k ∈ Z5 (n + 1),Qaa n p k * (k:ℝ) ^ 2 =
      (n:ℝ) * ((n:ℝ) - 1) * p ^ 2 + (n:ℝ) * p:=by
  cases n with
  | zero => simp
  | succ n =>
    have h:=Qgg n p (fun k => k)
    simp only [Z23,Z25] at h ⊢
    simp_rw [mul_add,mul_one,Z14,Qgi,
      Qcg] at h
    calc
      _ = ∑ k ∈ Z5 (n + 2),Qaa (n + 1) p k * (k:ℝ) * (k:ℝ):=by
        apply Z2 rfl
        intro k _
        ring
      _ = _:=by rw [h]; ring
theorem QjS (n:ℕ) (p:ℝ) :
    (∑ k ∈ Z5 (n + 1),Qaa n p k * ((k:ℝ) - (n:ℝ) * p) ^ 2) =
      (n:ℝ) * p * (1 - p):=by
  calc
    _ = (∑ k ∈ Z5 (n + 1),Qaa n p k * (k:ℝ) ^ 2) -
        2 * (n:ℝ) * p * (∑ k ∈ Z5 (n + 1),Qaa n p k * (k:ℝ)) +
        ((n:ℝ) * p) ^ 2 * (∑ k ∈ Z5 (n + 1),Qaa n p k):=by
      rw [Z3,Z3,← Z39,← Z14]
      apply Z2 rfl
      intro k _
      ring
    _ = _:=by rw [QjP,Qgi,Qcg]; ring
theorem Qgc (n k:ℕ) (p:ℝ) (hk:k < n) :
    ((k:ℝ) + 1) * (1 - p) * Qaa n p (k + 1) =
      ((n:ℝ) - k) * p * Qaa n p k:=by
  have hc:(n.choose (k + 1):ℝ) * ((k:ℝ) + 1) =
      (n.choose k:ℝ) * ((n:ℝ) - (k:ℝ)):=by
    simpa only [Z35,Z23,Z25,Z47 hk.le] using congrArg (fun t:ℕ => (t:ℝ)) (Nat.choose_succ_right_eq n k)
  have hnk:n - k = (n - (k + 1)) + 1:=by omega
  unfold Qaa
  rw [hnk,pow_succ,pow_succ]
  linear_combination p ^ k * p * (1 - p) ^ (n - (k + 1)) * (1 - p) * hc
theorem QjJ (n l k:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1)
    (hl:l ≤ n) (hmean:(n:ℝ) * p = l) :
    Qaa n p k ≤ Qaa n p l:=by
  have h0 (j:ℕ):=QaF n j ⟨hp.1.le,hp.2.le⟩
  have hleft (j:ℕ) (hj:j < l):Qaa n p j ≤ Qaa n p (j + 1):=by
    have hrec:=Qgc n j p (by omega)
    have hjr:(j:ℝ) + 1 ≤ l:=by exact_mod_cast hj
    have hcoef:(0:ℝ) < ((j:ℝ) + 1) * (1 - p):=by
      exact mul_pos (by positivity) (sub_pos.mpr hp.2)
    have hdiff:((j:ℝ) + 1) * (1 - p) ≤ ((n:ℝ) - j) * p:=by
      nlinarith [hp.1]
    have:=mul_le_mul_of_nonneg_right hdiff (h0 j)
    nlinarith only [hrec,this,hcoef]
  have hright (j:ℕ) (hj:l ≤ j):Qaa n p (j + 1) ≤ Qaa n p j:=by
    by_cases hjn:j < n
    · have hrec:=Qgc n j p hjn
      have hjr:(l:ℝ) ≤ j:=by exact_mod_cast hj
      have hcoef:(0:ℝ) < ((j:ℝ) + 1) * (1 - p):=by
        exact mul_pos (by positivity) (sub_pos.mpr hp.2)
      have hdiff:((n:ℝ) - j) * p ≤ ((j:ℝ) + 1) * (1 - p):=by
        nlinarith [hp.2]
      have:=mul_le_mul_of_nonneg_right hdiff (h0 j)
      nlinarith only [hrec,this,hcoef]
    · have hjn':n < j + 1:=by omega
      simp only [Qaa,Z44 hjn',Nat.cast_zero,zero_mul]
      exact h0 j
  rcases le_total k l with hk | hk
  · have haux:∀ b:ℕ,k ≤ b → b ≤ l → Qaa n p k ≤ Qaa n p b:=by
      intro b hkb
      induction b,hkb using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hb ih =>
        intro hbl
        exact (ih (by omega)).trans (hleft b (by omega))
    exact haux l hk le_rfl
  · induction k,hk using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hright j hj).trans ih
theorem QkX (n l:ℕ) (f:ℕ → ℝ) (M v:ℝ)
    (hf:∀ k,0 ≤ f k) (hsum:∑ k ∈ Z5 (n + 1),f k = 1)
    (hmax:∀ k,f k ≤ M)
    (hvar:∑ k ∈ Z5 (n + 1),f k * ((k:ℝ) - l) ^ 2 = v)
    (hv:1 ≤ v):1 / (12 * Z0 v) ≤ M:=by
  classical
  let r:ℕ:=⌈2 * Z0 v⌉₊
  have hv0:0 ≤ v:=by linarith
  have hs:1 ≤ Z0 v:=Real.one_le_sqrt.mpr hv
  have hs2:=Z13 hv0
  have hrlo:2 * Z0 v ≤ (r:ℝ):=Nat.le_ceil _
  have hrhi:(r:ℝ) < 2 * Z0 v + 1:=Nat.ceil_lt_add_one (by positivity)
  have hrpos:(0:ℝ) < r:=by linarith
  have hM:0 ≤ M:=(hf 0).trans (hmax 0)
  let S:=(Z5 (n + 1)).filter (fun k => l - r ≤ k ∧ k ≤ l + r)
  have hcard:S.card ≤ 2 * r + 1:=by
    have hsub:S ⊆ Finset.Icc (l - r) (l + r):=by
      intro k hk
      exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
    have:=Finset.card_le_card hsub
    rw [Nat.card_Icc] at this
    omega
  have hout (k:ℕ) (hk:¬(l - r ≤ k ∧ k ≤ l + r)) :
      (r:ℝ) ^ 2 ≤ ((k:ℝ) - l) ^ 2:=by
    by_cases hleft:k < l - r
    · have hnat:k + r < l:=by omega
      have hreal:(k:ℝ) + r < l:=by exact_mod_cast hnat
      nlinarith [sq_nonneg ((l:ℝ) - k - r)]
    · have hnat:l + r < k:=by omega
      have hreal:(l:ℝ) + r < k:=by exact_mod_cast hnat
      nlinarith [sq_nonneg ((k:ℝ) - l - r)]
  have hpoint (k:ℕ):(r:ℝ) ^ 2 * f k ≤
      (if l - r ≤ k ∧ k ≤ l + r then (r:ℝ) ^ 2 * M else 0) +
        f k * ((k:ℝ) - l) ^ 2:=by
    split_ifs with hk
    · have:=mul_le_mul_of_nonneg_left (hmax k) (sq_nonneg (r:ℝ))
      have:=mul_nonneg (hf k) (sq_nonneg ((k:ℝ) - l))
      linarith
    · simpa only [zero_add,mul_comm] using mul_le_mul_of_nonneg_left (hout k hk) (hf k)
  have htotal:=Z7 (fun k (_:k ∈ Z5 (n + 1)) => hpoint k)
  rw [← Z3,hsum,mul_one,Z14,hvar,
    ← Z27] at htotal
  change (r:ℝ) ^ 2 ≤ ∑ k ∈ S,(r:ℝ) ^ 2 * M + v at htotal
  rw [Z59,nsmul_eq_mul] at htotal
  have hcardR:(S.card:ℝ) ≤ 2 * r + 1:=by exact_mod_cast hcard
  have hbound:=mul_le_mul_of_nonneg_right hcardR (mul_nonneg (sq_nonneg (r:ℝ)) hM)
  have htotal':(r:ℝ) ^ 2 ≤ (2 * r + 1) * ((r:ℝ) ^ 2 * M) + v:=by
    linarith
  have hrv:4 * v ≤ (r:ℝ) ^ 2:=by nlinarith [sq_nonneg ((r:ℝ) - 2 * Z0 v)]
  have hcancel:(3:ℝ) / 4 ≤ (2 * r + 1) * M:=by
    have hrr:(0:ℝ) < (r:ℝ) ^ 2:=sq_pos_of_pos hrpos
    nlinarith only [htotal',hrv,hrr]
  have hsize:2 * (r:ℝ) + 1 ≤ 7 * Z0 v:=by linarith
  have hfinal:=mul_le_mul_of_nonneg_right hsize hM
  apply (div_le_iff₀ (by positivity:0 < 12 * Z0 v)).mpr
  nlinarith only [hcancel,hfinal]
theorem Qgj (n l:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1)
    (hl:l ≤ n) (hmean:(n:ℝ) * p = l) (hv:1 ≤ (n:ℝ) * p * (1 - p)) :
    1 / (12 * Z0 ((n:ℝ) * p * (1 - p))) ≤ Qaa n p l:=by
  apply QkX n l (Qaa n p)
    (Qaa n p l) ((n:ℝ) * p * (1 - p))
  · intro k; exact QaF n k ⟨hp.1.le,hp.2.le⟩
  · exact Qcg n p
  · intro k; exact QjJ n l k hp hl hmean
  · rw [← hmean]; exact QjS n p
  · exact hv
theorem QeP (n l:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1)
    (hl:l ≤ n) (hmean:(n:ℝ) * p = l) (hv:1 ≤ (n:ℝ) * p * (1 - p)) :
    (Qaa n p l)⁻¹ ^ 2 ≤ 144 * ((n:ℝ) * p * (1 - p)):=by
  have hs:0 < Z0 ((n:ℝ) * p * (1 - p)) :=
    Real.sqrt_pos.mpr (by linarith)
  have hlow:=Qgj n l hp hl hmean hv
  have hpos:0 < Qaa n p l:=lt_of_lt_of_le (by positivity) hlow
  have hi:(Qaa n p l)⁻¹ ≤ 12 * Z0 ((n:ℝ) * p * (1 - p)):=by
    rw [← one_div]
    apply (div_le_iff₀ hpos).mpr
    have:=(div_le_iff₀ (by positivity)).mp hlow
    nlinarith only [this]
  have his:=sq_le_sq₀ (by positivity) (by positivity) |>.mpr hi
  have hs2:=Z13 (show 0 ≤ (n:ℝ) * p * (1 - p) by linarith)
  nlinarith only [his,hs2]
theorem Qpy (a:ℝ) (f:IntSeries) :
    seriesL1 (a • f) = |a| * seriesL1 f:=by
  unfold seriesL1
  simp only [Z88,Z89,smul_eq_mul,abs_mul]
  exact tsum_mul_left
theorem Qne (n:ℕ) {p:ℝ} (hp:p ∈ Z12 0 1) :
    seriesL1 (Qas * Qdo n p) ≤
      2 * Z0 (2 / (((n:ℝ) + 1) * p)):=by
  rw [QhF,Z3]
  simp_rw [mul_smul_comm]
  calc
    _ ≤ ∑ k ∈ Z5 (n + 1),
        seriesL1 (Qaa n p k • (Qas * fairSeries k)):=Qiy _ _
    _ ≤ ∑ k ∈ Z5 (n + 1),Qaa n p k * (2 * Qar k):=by
      apply Z7
      intro k _
      have hw:=QaF n k ⟨hp.1.le,hp.2⟩
      rw [Qpy,abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (Qfc k) hw
    _ = 2 * ∑ k ∈ Z5 (n + 1),Qaa n p k * Qar k:=by
      rw [Z3]
      apply Z2 rfl
      intro k _; ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (QhI n hp) (by norm_num)
theorem QfZ (n:ℕ) {p:ℝ}
    (hp:p ∈ Z12 0 (1 / 2)) :
    seriesL1 (Qas * Qaf n p) ≤
      2 * Z0 (1 / (((n:ℝ) + 1) * p)):=by
  have h:=Qne n
    (show 2 * p ∈ Z12 0 1 from ⟨by linarith [hp.1],by linarith [hp.2]⟩)
  rw [QhE] at h
  have hp2:2 * p / 2 = p:=by ring
  have heq:2 / (((n:ℝ) + 1) * (2 * p)) = 1 / (((n:ℝ) + 1) * p):=by
    have hp0:p ≠ 0:=ne_of_gt hp.1
    have hn0:((n:ℝ) + 1) ≠ 0:=by positivity
    field_simp
  rwa [hp2,heq] at h
theorem Qjw (n:ℕ) (p:ℝ) (z:ℤ) :
    (Qas * Qaf n (1 - p)).coeff z =
      -(Qas * Qaf n p).coeff ((n:ℤ) + 1 - z):=by
  rw [QdF,QdF]
  have h1:=QeM n p ((n:ℤ) - z)
  have h2:=QeM n p ((n:ℤ) - (z - 1))
  have hz1:(n:ℤ) - ((n:ℤ) - z) = z:=by ring
  have hz2:(n:ℤ) - ((n:ℤ) - (z - 1)) = z - 1:=by ring
  rw [hz1] at h1
  rw [hz2] at h2
  rw [h1,h2]
  have he1:(n:ℤ) - (z - 1) = n + 1 - z:=by ring
  have he2:(n:ℤ) + 1 - z - 1 = n - z:=by ring
  rw [he1,he2]
  ring
theorem Qjv (n:ℕ) (p:ℝ) :
    seriesL1 (Qas * Qaf n (1 - p)) =
      seriesL1 (Qas * Qaf n p):=by
  unfold seriesL1
  simp_rw [Qjw,abs_neg]
  exact (Equiv.subLeft ((n:ℤ) + 1)).tsum_eq
    (fun z:ℤ => |(Qas * Qaf n p).coeff z|)
theorem QfY (n:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    seriesL1 (Qas * Qaf n p) ≤
      2 * Z0 (1 / (((n:ℝ) + 1) * p * (1 - p))):=by
  by_cases hlow:p ≤ 1 / 2
  · apply (QfZ n ⟨hp.1,hlow⟩).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Z24
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ n + 1 by positivity) (sq_nonneg p)]
  · have hq:1 - p ∈ Z12 0 (1 / 2):=⟨by linarith [hp.2],by linarith⟩
    rw [← Qjv n p]
    apply (QfZ n hq).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Z24
    apply one_div_le_one_div_of_le
    · exact mul_pos (mul_pos (by positivity) hp.1) (sub_pos.mpr hp.2)
    · nlinarith [mul_nonneg (show (0:ℝ) ≤ n + 1 by positivity)
        (mul_nonneg (sub_nonneg.mpr hp.2.le) (sub_nonneg.mpr hp.2.le))]
def Qaz (n:ℕ) (p:ℝ):ℝ :=
  Z0 (1 / (((n:ℝ) + 1) * p * (1 - p)))
theorem QeJ (n:ℕ) {p:ℝ} (hp:p ∈ Z6 0 1) :
    seriesL1 (Qaf n p) = 1:=by
  rw [QfE _ n (QeL n p)]
  · simp_rw [QcV,abs_of_nonneg (QaF _ _ hp)]
    exact Qcg n p
  · intro k hk
    exact QeK n p k (by exact_mod_cast hk)
theorem Qju (n:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    seriesL2Sq (Qaf n p) ≤ Qaz n p:=by
  have:=Qiz (Qaf n p) _ (Qed n hp)
  simpa only [QeJ n ⟨hp.1.le,hp.2.le⟩,one_mul,Qaz] using this
theorem QfW (m n:ℕ) (p:ℝ) :
    Qaf (m + n) p = Qaf m p * Qaf n p:=by
  exact pow_add _ _ _
theorem Qga (n s:ℕ) (p:ℝ) :
    Qas ^ s * Qaf ((s + 1) * n) p =
      (Qas * Qaf n p) ^ s * Qaf n p:=by
  simp only [Qaf,add_mul,one_mul,pow_add,pow_mul,mul_pow]
  ring
theorem QjA (n s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) (z:ℤ) :
    |(Qas ^ s * Qaf ((s + 1) * n) p).coeff z| ≤
      (2 * Qaz n p) ^ s * Qaz n p:=by
  rw [Qga]
  apply (QdX _ _ _ (Qed n hp) z).trans
  apply mul_le_mul_of_nonneg_right _ (Z36 _)
  exact (Qew _ _).trans
    (pow_le_pow_left₀ (QbT _) (QfY n hp) s)
theorem Qjy (n s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    seriesL2Sq (Qas ^ s * Qaf ((s + 1) * n) p) ≤
      ((2 * Qaz n p) ^ s) ^ 2 * Qaz n p:=by
  rw [Qga]
  apply (Qdu _ _).trans
  apply mul_le_mul
  · apply pow_le_pow_left₀ (QbT _)
    exact (Qew _ _).trans
      (pow_le_pow_left₀ (QbT _) (QfY n hp) s)
  · exact Qju n hp
  · exact Qcn _
  · exact sq_nonneg _
theorem QjB (n s r:ℕ) {p:ℝ}
    (hp:p ∈ Z4 0 1) (z:ℤ) :
    |(Qas ^ s * Qaf ((s + 1) * n + r) p).coeff z| ≤
      (2 * Qaz n p) ^ s * Qaz n p:=by
  rw [QfW,← mul_assoc,mul_comm (Qas ^ s * _)]
  simpa only [QeJ r ⟨hp.1.le,hp.2.le⟩,one_mul] using QdX (Qaf r p) (Qas ^ s * Qaf ((s + 1) * n) p)
      _ (QjA n s hp) z
theorem Qjz (n s r:ℕ) {p:ℝ}
    (hp:p ∈ Z4 0 1) :
    seriesL2Sq (Qas ^ s * Qaf ((s + 1) * n + r) p) ≤
      ((2 * Qaz n p) ^ s) ^ 2 * Qaz n p:=by
  rw [QfW,← mul_assoc,mul_comm (Qas ^ s * _)]
  calc
    _ ≤ seriesL1 (Qaf r p) ^ 2 *
        seriesL2Sq (Qas ^ s * Qaf ((s + 1) * n) p):=Qdu _ _
    _ ≤ _:=by simpa only [QeJ r ⟨hp.1.le,hp.2.le⟩,one_pow,one_mul] using Qjy n s hp
theorem QjC (g s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    (∀ z:ℤ,|(Qas ^ s * Qaf g p).coeff z| ≤
      (2 * Qaz (g / (s + 1)) p) ^ s *
        Qaz (g / (s + 1)) p) ∧
    (seriesL2Sq (Qas ^ s * Qaf g p) ≤
      ((2 * Qaz (g / (s + 1)) p) ^ s) ^ 2 *
        Qaz (g / (s + 1)) p):=by
  have hg:(s + 1) * (g / (s + 1)) + g % (s + 1) = g:=Nat.div_add_mod g (s + 1)
  constructor
  · intro z
    simpa only [hg] using QjB (g / (s + 1)) s
      (g % (s + 1)) hp z
  · simpa only [hg] using Qjz (g / (s + 1)) s
      (g % (s + 1)) hp
theorem Qjt (g s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    Qaz (g / (s + 1)) p ≤
      Z0 (((s:ℝ) + 1) / (((g:ℝ) + 1) * p * (1 - p))):=by
  unfold Qaz
  apply Z24
  have hpq:0 < p * (1 - p):=mul_pos hp.1 (sub_pos.mpr hp.2)
  have hnat:g + 1 ≤ (s + 1) * (g / (s + 1) + 1):=by
    have hdiv:=Nat.div_add_mod g (s + 1)
    have hmod:g % (s + 1) < s + 1:=Nat.mod_lt g (by omega)
    calc
      g + 1 = (s + 1) * (g / (s + 1)) + g % (s + 1) + 1:=by omega
      _ ≤ (s + 1) * (g / (s + 1)) + (s + 1):=by omega
      _ = _:=by ring
  have hreal:(g:ℝ) + 1 ≤ ((s:ℝ) + 1) * ((g / (s + 1):ℕ) + 1:ℝ):=by
    exact_mod_cast hnat
  have hp0:=hp.1
  have hq0:=sub_pos.mpr hp.2
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hreal hpq.le]
theorem Qgl (n k:ℕ) {p a:ℝ} (hp:p ∈ Z4 0 1)
    (ha:0 < a) :
    Qaa n p k * a ^ k =
      (1 - p + p * a) ^ n * Qaa n (p * a / (1 - p + p * a)) k:=by
  by_cases hk:k ≤ n
  · have hA:0 < 1 - p + p * a:=by positivity [sub_pos.mpr hp.2,hp.1]
    have hsub:1 - p * a / (1 - p + p * a) = (1 - p) / (1 - p + p * a):=by
      field_simp; ring
    unfold Qaa
    rw [hsub,div_pow,div_pow,mul_pow]
    have hpow:(1 - p + p * a) ^ n =
        (1 - p + p * a) ^ k * (1 - p + p * a) ^ (n - k):=by
      rw [← pow_add,Nat.add_sub_of_le hk]
    rw [hpow]
    field_simp
  · simp [Qaa,Z44 (by omega:n < k)]
theorem QjR (g h k:ℕ) {p a:ℝ} (hp:p ∈ Z4 0 1)
    (ha:0 < a) :
    Qaa g p k * Qaa h p k =
      ((1 - p + p * a) ^ g * (1 - p + p / a) ^ h) *
        (Qaa g (p * a / (1 - p + p * a)) k *
          Qaa h ((p / a) / (1 - p + p / a)) k):=by
  have h1:=Qgl g k hp ha
  have h2:=Qgl h k hp (inv_pos.mpr ha)
  have hid:=congrArg₂ (· * ·) h1 h2
  simp only [inv_pow,← div_eq_mul_inv] at hid
  have ha0:a ^ k ≠ 0:=pow_ne_zero _ ha.ne'
  calc
    _ = (Qaa g p k * a ^ k) * (Qaa h p k / a ^ k):=by field_simp
    _ = _:=by convert hid using 1; ring
theorem QjX (g h:ℕ) {p a:ℝ}
    (hp:p ∈ Z4 0 1) (ha:0 < a) :
    (∑ k ∈ Z5 (h + 1),Qaa g p k * Qaa h p k) ≤
      ((1 - p + p * a) ^ g * (1 - p + p / a) ^ h) *
        Qaz g (p * a / (1 - p + p * a)):=by
  have hA:0 < 1 - p + p * a:=by positivity [sub_pos.mpr hp.2,hp.1]
  have hB:0 < 1 - p + p / a:=by positivity [sub_pos.mpr hp.2,hp.1]
  have hpA:p * a / (1 - p + p * a) ∈ Z4 (0:ℝ) 1:=by
    constructor
    · positivity [hp.1]
    · apply (div_lt_one hA).mpr; linarith [hp.2]
  have hpB:(p / a) / (1 - p + p / a) ∈ Z4 (0:ℝ) 1:=by
    constructor
    · positivity [hp.1]
    · apply (div_lt_one hB).mpr; linarith [hp.2]
  simp_rw [QjR g h _ hp ha,← Z3]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ k ∈ Z5 (h + 1),
        Qaz g (p * a / (1 - p + p * a)) *
          Qaa h ((p / a) / (1 - p + p / a)) k:=by
      apply Z7
      intro k _
      apply mul_le_mul_of_nonneg_right _ (QaF _ _ ⟨hpB.1.le,hpB.2.le⟩)
      have hb:=Qed g hpA (k:ℤ)
      rw [QcV,abs_of_nonneg (QaF _ _ ⟨hpA.1.le,hpA.2.le⟩)] at hb
      exact hb
    _ = _:=by rw [← Z3,Qcg,mul_one]
theorem Qkb {p t:ℝ} (hp:p ∈ Z4 0 1)
    (ht:t ∈ Z6 0 (1 / 4:ℝ)) :
    p * (1 - p) / 2 ≤
      (p * (1 - t) / (1 - p + p * (1 - t))) *
        (1 - p * (1 - t) / (1 - p + p * (1 - t))):=by
  have hA:0 < 1 - p + p * (1 - t):=by
    have:=hp.1; have:=hp.2; have:=ht.2
    positivity [sub_pos.mpr hp.2,show (0:ℝ) < 1 - t by linarith]
  have hA1:1 - p + p * (1 - t) ≤ 1:=by nlinarith [mul_nonneg hp.1.le ht.1]
  have hAsq:(1 - p + p * (1 - t)) ^ 2 ≤ 1:=by nlinarith
  have hpq:0 < p * (1 - p):=mul_pos hp.1 (sub_pos.mpr hp.2)
  have heq:(p * (1 - t) / (1 - p + p * (1 - t))) *
        (1 - p * (1 - t) / (1 - p + p * (1 - t))) =
      p * (1 - p) * (1 - t) / (1 - p + p * (1 - t)) ^ 2:=by
    field_simp; ring
  rw [heq]
  apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
  have hh:=mul_le_mul_of_nonneg_left hAsq hpq.le
  nlinarith [ht.2]
theorem Qka (g h:ℕ) {p:ℝ}
    (hp:p ∈ Set.Ico (1 / 2:ℝ) 1) (hhg:h ≤ g) (hS:0 < g + h) :
    let t:ℝ:=((g:ℝ) - h) / (4 * ((g:ℝ) + h))
    ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤
      Z1 (-((g:ℝ) - h) ^ 2 / (16 * ((g:ℝ) + h))):=by
  dsimp only
  set t:ℝ:=((g:ℝ) - h) / (4 * ((g:ℝ) + h)) with htdef
  have hSr:(0:ℝ) < (g:ℝ) + h:=by exact_mod_cast hS
  have hgr:(h:ℝ) ≤ g:=by exact_mod_cast hhg
  have hd:(0:ℝ) ≤ (g:ℝ) - h:=sub_nonneg.mpr hgr
  have ht0:0 ≤ t:=div_nonneg hd (by positivity)
  have ht1:t ≤ 1 / 4:=by
    apply (div_le_iff₀ (by positivity:(0:ℝ) < 4 * ((g:ℝ) + h))).mpr
    nlinarith [show (0:ℝ) ≤ h by positivity]
  have htlt:0 < 1 - t:=by linarith
  have hp0:0 < p:=by linarith [hp.1]
  have hA:0 < 1 - p + p * (1 - t):=by positivity [sub_pos.mpr hp.2]
  have hB:0 < 1 - p + p / (1 - t):=by positivity [sub_pos.mpr hp.2]
  have hlogA:Z8 (1 - p + p * (1 - t)) ≤ -p * t:=by
    have:=Z96 hA
    nlinarith only [this]
  have hlogB:Z8 (1 - p + p / (1 - t)) ≤ p * t / (1 - t):=by
    have:=Z96 hB
    have heq:1 - p + p / (1 - t) - 1 = p * t / (1 - t):=by field_simp; ring
    rwa [heq] at this
  have hlog:Z8 ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤
      -(p * ((g:ℝ) - h) * t) + 2 * p * h * t ^ 2:=by
    rw [Real.log_mul (pow_pos hA _).ne' (pow_pos hB _).ne',Real.log_pow,Real.log_pow]
    have hb:(h:ℝ) * (p * t / (1 - t)) ≤ (h:ℝ) * (p * t + 2 * p * t ^ 2):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (div_le_iff₀ htlt).mpr
      have hh:=mul_nonneg (mul_nonneg hp0.le (sq_nonneg t)) (show 0 ≤ 1 - 2 * t by linarith)
      nlinarith only [hh]
    have ha:=mul_le_mul_of_nonneg_left hlogA (show (0:ℝ) ≤ g by positivity)
    have hb':=mul_le_mul_of_nonneg_left hlogB (show (0:ℝ) ≤ h by positivity)
    linarith
  have hht:4 * (h:ℝ) * t ≤ (g:ℝ) - h:=by
    rw [htdef,← mul_div_assoc]
    apply (div_le_iff₀ (by positivity:(0:ℝ) < 4 * ((g:ℝ) + h))).mpr
    have hm:=mul_nonneg (show (0:ℝ) ≤ g by positivity) hd
    nlinarith only [hm]
  have hhalf:-(p * ((g:ℝ) - h) * t) + 2 * p * h * t ^ 2 ≤
      -(p * ((g:ℝ) - h) * t) / 2:=by
    have hm:=mul_le_mul_of_nonneg_right hht (mul_nonneg hp0.le ht0)
    nlinarith only [hm]
  have hlast:-(p * ((g:ℝ) - h) * t) / 2 ≤
      -((g:ℝ) - h) ^ 2 / (16 * ((g:ℝ) + h)):=by
    rw [htdef]
    apply (div_le_div_iff₀ (by norm_num:(0:ℝ) < 2) (by positivity)).mpr
    field_simp
    have hm:=mul_nonneg (show 0 ≤ 2 * p - 1 by linarith [hp.1]) (sq_nonneg ((g:ℝ) - h))
    nlinarith only [hm]
  have hexp:=Real.exp_le_exp.mpr (hlog.trans (hhalf.trans hlast))
  rwa [Real.exp_log (mul_pos (pow_pos hA _) (pow_pos hB _))] at hexp
theorem QeQ (g h:ℕ) {p:ℝ}
    (hp:p ∈ Set.Ico (1 / 2:ℝ) 1) (hhg:h ≤ g) (hS:0 < g + h) :
    (∑ k ∈ Z5 (h + 1),Qaa g p k * Qaa h p k) ≤
      Z0 (2 / (((g:ℝ) + 1) * p * (1 - p))) *
        Z1 (-((g:ℝ) - h) ^ 2 / (16 * ((g:ℝ) + h))):=by
  let t:ℝ:=((g:ℝ) - h) / (4 * ((g:ℝ) + h))
  have hSr:(0:ℝ) < (g:ℝ) + h:=by exact_mod_cast hS
  have hgr:(h:ℝ) ≤ g:=by exact_mod_cast hhg
  have ht0:0 ≤ t:=div_nonneg (sub_nonneg.mpr hgr) (by positivity)
  have ht1:t ≤ 1 / 4:=by
    apply (div_le_iff₀ (by positivity:(0:ℝ) < 4 * ((g:ℝ) + h))).mpr
    nlinarith [show (0:ℝ) ≤ h by positivity]
  have htlt:0 < 1 - t:=by linarith
  have hp0:0 < p:=by linarith [hp.1]
  have hp':p ∈ Z4 (0:ℝ) 1:=⟨hp0,hp.2⟩
  have hA:0 < 1 - p + p * (1 - t):=by positivity [sub_pos.mpr hp.2]
  have hB:0 < 1 - p + p / (1 - t):=by positivity [sub_pos.mpr hp.2]
  have hv:=Qkb hp' ⟨ht0,ht1⟩
  have hpq:0 < p * (1 - p):=mul_pos hp0 (sub_pos.mpr hp.2)
  have hx:0 < (p * (1 - t) / (1 - p + p * (1 - t))) *
      (1 - p * (1 - t) / (1 - p + p * (1 - t))):=lt_of_lt_of_le (by positivity) hv
  have hb:Qaz g (p * (1 - t) / (1 - p + p * (1 - t))) ≤
      Z0 (2 / (((g:ℝ) + 1) * p * (1 - p))):=by
    apply Z24
    have hg:(0:ℝ) < (g:ℝ) + 1:=by positivity
    apply (div_le_div_iff₀ (by nlinarith only [mul_pos hg hx]) (by nlinarith only [mul_pos hg hpq])).mpr
    have hm:=mul_le_mul_of_nonneg_left hv hg.le
    nlinarith only [hm]
  have hn:=Qka g h hp hhg hS
  change ((1 - p + p * (1 - t)) ^ g * (1 - p + p / (1 - t)) ^ h) ≤ _ at hn
  have he:=QjX g h hp' htlt
  apply he.trans
  have hbound:=mul_le_mul hn hb (Z36 _) (Z49 _)
  simpa only [mul_comm] using hbound
theorem Qqn {x:ℝ} (hx:0 ≤ x) :
    Z0 (x + 1) * Z1 (-x / 96) ≤ 16:=by
  have he:Z1 (-x / 96) ^ 2 = 1 / Z1 (x / 48):=by
    rw [pow_two,← Z50]
    rw [show -x / 96 + -x / 96 = -(x / 48) by ring,Real.exp_neg,one_div]
  have hs:(Z0 (x + 1) * Z1 (-x / 96)) ^ 2 ≤ 256:=by
    rw [mul_pow,Z13 (by linarith),he,mul_one_div]
    apply (div_le_iff₀ (Z74 _)).mpr
    have hh:=Real.add_one_le_exp (x / 48)
    nlinarith only [hh,hx]
  nlinarith only [hs]
theorem Qql {a b:ℝ} (ha:0 < a) (hb:0 < b) (hab:a ≤ 2 * b) :
    Z0 (1 / a) * Z0 (1 / b) ≤ 2 / a:=by
  rw [← Real.sqrt_mul (by positivity),Real.sqrt_le_iff]
  refine ⟨by positivity,?_⟩
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  field_simp
  nlinarith
theorem Qgh (n k:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    Qaa n p k ≤ Qaz n p:=by
  have h:=Qed n hp (k:ℤ)
  rw [QcV,abs_of_nonneg (QaF _ _ ⟨hp.1.le,hp.2.le⟩)] at h
  exact h
theorem QjY (g h k:ℕ) {p:ℝ}
    (hp:p ∈ Set.Ico (1 / 2:ℝ) 1) :
    Qaa g p k * Qaa h p k ≤
      32 / (((g:ℝ) + 1) * p * (1 - p)):=by
  have hp0:0 < p:=by linarith [hp.1]
  have hp':p ∈ Z4 (0:ℝ) 1:=⟨hp0,hp.2⟩
  have hpq:0 < p * (1 - p):=mul_pos hp0 (sub_pos.mpr hp.2)
  have hpq1:p * (1 - p) ≤ 1:=by nlinarith only [sq_nonneg (p - 1 / 2)]
  have hden:0 < ((g:ℝ) + 1) * p * (1 - p):=by nlinarith only [mul_pos (show (0:ℝ) < (g:ℝ) + 1 by positivity) hpq]
  by_cases hnear:g ≤ 2 * h
  · have hdenh:0 < ((h:ℝ) + 1) * p * (1 - p):=by nlinarith only [mul_pos (show (0:ℝ) < (h:ℝ) + 1 by positivity) hpq]
    have hgh:((g:ℝ) + 1) * p * (1 - p) ≤ 2 * (((h:ℝ) + 1) * p * (1 - p)):=by
      have hcast:(g:ℝ) ≤ 2 * h:=by exact_mod_cast hnear
      have hm:=mul_le_mul_of_nonneg_right (show (g:ℝ) + 1 ≤ 2 * ((h:ℝ) + 1) by linarith) hpq.le
      nlinarith only [hm]
    calc
      _ ≤ Qaz g p * Qaz h p :=
        mul_le_mul (Qgh g k hp') (Qgh h k hp')
          (QaF _ _ ⟨hp0.le,hp.2.le⟩) (Z36 _)
      _ ≤ 2 / (((g:ℝ) + 1) * p * (1 - p)):=Qql hden hdenh hgh
      _ ≤ _:=div_le_div_of_nonneg_right (by norm_num) hden.le
  · by_cases hk:k ≤ h
    · have hhg:h ≤ g:=by omega
      have hS:0 < g + h:=by omega
      have hsum:Qaa g p k * Qaa h p k ≤
          ∑ j ∈ Z5 (h + 1),Qaa g p j * Qaa h p j:=by
        exact Z82 (s:=Z5 (h + 1)) (a:=k) (fun j _ => mul_nonneg
          (QaF g j ⟨hp0.le,hp.2.le⟩)
          (QaF h j ⟨hp0.le,hp.2.le⟩)) (Finset.mem_range.mpr (by omega))
      have hgauss:=QeQ g h hp hhg hS
      have hSr:(0:ℝ) < (g:ℝ) + h:=by exact_mod_cast hS
      have hfar:2 * (h:ℝ) < g:=by exact_mod_cast (show 2 * h < g by omega)
      have hexp:Z1 (-((g:ℝ) - h) ^ 2 / (16 * ((g:ℝ) + h))) ≤ Z1 (-(g:ℝ) / 96):=by
        apply Real.exp_le_exp.mpr
        apply (div_le_div_iff₀ (by positivity:(0:ℝ) < 16 * ((g:ℝ) + h)) (by norm_num:(0:ℝ) < 96)).mpr
        have hn:=mul_nonneg (show 0 ≤ (g:ℝ) - 2 * h by linarith) (show 0 ≤ 5 * (g:ℝ) - 3 * h by linarith)
        nlinarith only [hn,sq_nonneg (h:ℝ)]
      have hcoeff:Z0 (2 / (((g:ℝ) + 1) * p * (1 - p))) ≤
          (2 / (((g:ℝ) + 1) * p * (1 - p))) * Z0 ((g:ℝ) + 1):=by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity,?_⟩
        rw [mul_pow,Z13 (by positivity),div_pow]
        have hgpos:(0:ℝ) < (g:ℝ) + 1:=by positivity
        have hqpos:0 < 1 - p:=sub_pos.mpr hp.2
        field_simp
        have hm:=mul_le_mul_of_nonneg_left hpq1 (show (0:ℝ) ≤ (g:ℝ) + 1 by positivity)
        nlinarith only [hm,hpq1]
      calc
        _ ≤ Z0 (2 / (((g:ℝ) + 1) * p * (1 - p))) *
            Z1 (-((g:ℝ) - h) ^ 2 / (16 * ((g:ℝ) + h))):=hsum.trans hgauss
        _ ≤ ((2 / (((g:ℝ) + 1) * p * (1 - p))) * Z0 ((g:ℝ) + 1)) *
            Z1 (-(g:ℝ) / 96):=mul_le_mul hcoeff hexp (Z49 _) (by positivity)
        _ ≤ (2 / (((g:ℝ) + 1) * p * (1 - p))) * 16:=by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (Qqn (by positivity)) (by positivity)
        _ = _:=by ring
    · simp [Qaa,Z44 (by omega:h < k)]
      positivity
end TraceReconstruction
namespace TraceReconstruction
theorem QjL (n:ℕ) (p t:ℝ) :
    (∑ k ∈ Z5 (n + 1),Qaa n p k * Z1 (t * k)) =
      (1 - p + p * Z1 t) ^ n:=by
  rw [add_comm (1 - p),add_pow]
  apply Z2 rfl
  intro k _
  rw [show t * (k:ℝ) = (k:ℝ) * t by ring,Z75,mul_pow]
  unfold Qaa
  ring
theorem QjM (n:ℕ) {p:ℝ} (hp:p ∈ Z6 0 1) (t:ℝ) :
    (∑ k ∈ Z5 (n + 1),Qaa n p k * Z1 (t * k)) ≤
      Z1 ((n:ℝ) * p * (Z1 t - 1)):=by
  rw [QjL]
  have hn:0 ≤ 1 - p + p * Z1 t:=by positivity [sub_nonneg.mpr hp.2,hp.1]
  have he:1 - p + p * Z1 t ≤ Z1 (p * (Z1 t - 1)):=by
    nlinarith only [Real.add_one_le_exp (p * (Z1 t - 1))]
  calc
    _ ≤ Z1 (p * (Z1 t - 1)) ^ n:=pow_le_pow_left₀ hn he n
    _ = _:=by rw [← Z75]; congr 1; ring
theorem QgU {α:Type*} (S:Finset α) (w X:α → ℝ)
    (hw:∀ a ∈ S,0 ≤ w a) (a t:ℝ) (ht:0 ≤ t) :
    (∑ z ∈ S with a ≤ X z,w z) ≤
      Z1 (-t * a) * ∑ z ∈ S,w z * Z1 (t * X z):=by
  classical
  calc
    _ = ∑ z ∈ S with a ≤ X z,Z1 (-t * a) * (w z * Z1 (t * a)):=by
      apply Z2 rfl
      intro z _
      rw [mul_left_comm,← Z50]
      simp
    _ ≤ ∑ z ∈ S with a ≤ X z,Z1 (-t * a) * (w z * Z1 (t * X z)):=by
      apply Z7
      intro z hz
      have h:=Finset.mem_filter.mp hz
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.2 ht)) (hw z h.1))
        (Z49 _)
    _ ≤ ∑ z ∈ S,Z1 (-t * a) * (w z * Z1 (t * X z)):=by
      apply Z40 (Finset.filter_subset _ _)
      intro z hz _
      positivity [hw z hz]
    _ = _:=by rw [Z3]
end TraceReconstruction
namespace TraceReconstruction
end TraceReconstruction
namespace TraceReconstruction
end TraceReconstruction
namespace TraceReconstruction
end TraceReconstruction
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
noncomputable section
namespace TraceReconstruction
theorem Qee (r L:ℕ)
    (f:Fin (r + 1) → Fin (L + 1) → ℝ)
    (hf:∀ i k,0 ≤ f i k) (M:ℝ) (hM:0 ≤ M)
    (hbound:∀ k,f 0 k ≤ M) :
    (∑ z:Fin (r + 1) → Fin (L + 1),
      if ∑ j,(z j).val = L then ∏ j,f j (z j) else 0) ≤
        M * ∏ i:Fin r,∑ k,f i.succ k:=by
  classical
  rw [← (Z46 (fun _:Fin (r + 1) => Fin (L + 1))).sum_comp]
  rw [Z32,Z17]
  have hpoint (z:Fin r → Fin (L + 1)) :
      (∑ k:Fin (L + 1),
        if k.val + ∑ i,(z i).val = L then f 0 k * ∏ i,f i.succ (z i) else 0) ≤
          M * ∏ i,f i.succ (z i):=by
    by_cases hz:∑ i,(z i).val ≤ L
    · let k₀:Fin (L + 1):=⟨L - ∑ i,(z i).val,by omega⟩
      have heq (k:Fin (L + 1)):k.val + ∑ i,(z i).val = L ↔ k = k₀:=by
        change _ ↔ k = ⟨L - ∑ i,(z i).val,_⟩
        rw [Fin.ext_iff]
        simp only
        omega
      simp_rw [heq]
      rw [Fintype.sum_ite_eq']
      exact mul_le_mul_of_nonneg_right (hbound k₀) (Z37 fun i _ => hf _ _)
    · have heq (k:Fin (L + 1)):¬ (k.val + ∑ i,(z i).val = L):=by omega
      simp_rw [if_neg (heq _),Z102]
      exact mul_nonneg hM (Z37 fun i _ => hf _ _)
  calc
    _ ≤ ∑ z:Fin r → Fin (L + 1),M * ∏ i,f i.succ (z i):=by
      apply Z7
      intro z _
      simpa only [Fin.consEquiv_apply,Z64,Z53,
        Z54,Z55] using hpoint z
    _ = _:=by
      rw [← Z3,← Z43 (fun (i:Fin r) (k:Fin (L + 1)) => f i.succ k)]
theorem QkJ (r L:ℕ)
    (f g:Fin (r + 1) → Fin (L + 1) → ℝ)
    (hf:∀ i k,0 ≤ f i k) (hg:∀ i k,0 ≤ g i k)
    (M:ℝ) (hM:0 ≤ M) (hbound:∀ k,f 0 k * g 0 k ≤ M) :
    (∑ z:Fin (r + 1) → Fin (L + 1),
      if ∑ j,(z j).val = L then (∏ j,f j (z j)) * (∏ j,g j (z j)) else 0) ≤
        M * ∏ i:Fin r,∑ k,f i.succ k * g i.succ k:=by
  simp_rw [← Z30]
  exact Qee r L (fun i k => f i k * g i k)
    (fun i k => mul_nonneg (hf i k) (hg i k)) M hM hbound
end TraceReconstruction
namespace TraceReconstruction
section CorrelatedAnchors
variable {Ω I J:Type*} [Fintype Ω] [Fintype I] [Fintype J]
end CorrelatedAnchors
end TraceReconstruction
namespace TraceReconstruction
theorem Qgm (g h L:ℕ) {p:ℝ}
    (hp:p ∈ Z6 0 1) :
    (∑ k:Fin (L + 1),Qaa g p k * Qaa h p k) ≤
      ∑ k ∈ Z5 (h + 1),Qaa g p k * Qaa h p k:=by
  rw [Z76 (fun k => Qaa g p k * Qaa h p k) (L + 1)]
  by_cases hL:L ≤ h
  · apply Z40 (Z90 (by omega))
    intro k _ _
    exact mul_nonneg (QaF g k hp) (QaF h k hp)
  · apply le_of_eq
    symm
    apply Z97 (Z90 (by omega))
    intro k _ hk
    have hhk:h < k:=by
      simp only [Z57,not_lt] at hk
      omega
    simp [Qaa,Z44 hhk]
theorem QjV (g h L:ℕ) {p:ℝ}
    (hp:p ∈ Set.Ico (1 / 2:ℝ) 1) (hS:0 < g + h) :
    (∑ k:Fin (L + 1),Qaa g p k * Qaa h p k) ≤
      Z0 (2 / (((g:ℝ) + 1) * p * (1 - p))) *
        Z1 (-((g:ℝ) - h) ^ 2 / (16 * ((g:ℝ) + h))):=by
  have hp0:0 < p:=by linarith [hp.1]
  have hpq:0 < p * (1 - p):=mul_pos hp0 (sub_pos.mpr hp.2)
  by_cases hhg:h ≤ g
  · exact (Qgm g h L ⟨hp0.le,hp.2.le⟩).trans
      (QeQ g h hp hhg hS)
  · have hgh:g ≤ h:=by omega
    have ho:=(Qgm h g L ⟨hp0.le,hp.2.le⟩).trans
      (QeQ h g hp hgh (by omega))
    have hb:Z0 (2 / (((h:ℝ) + 1) * p * (1 - p))) ≤
        Z0 (2 / (((g:ℝ) + 1) * p * (1 - p))):=by
      apply Z24
      apply div_le_div_of_nonneg_left (by norm_num)
        (by nlinarith only [mul_pos (show (0:ℝ) < (g:ℝ) + 1 by positivity) hpq])
      have hcast:(g:ℝ) ≤ h:=by exact_mod_cast hgh
      have ht:=mul_le_mul_of_nonneg_right (show (g:ℝ) + 1 ≤ (h:ℝ) + 1 by linarith) hpq.le
      nlinarith only [ht]
    have heq:-((h:ℝ) - g) ^ 2 / (16 * ((h:ℝ) + g)) =
        -((g:ℝ) - h) ^ 2 / (16 * ((g:ℝ) + h)):=by ring
    rw [heq] at ho
    exact (by simpa only [mul_comm] using ho :
      (∑ k:Fin (L + 1),Qaa g p k * Qaa h p k) ≤ _).trans
        (mul_le_mul_of_nonneg_right hb (Z49 _))
end TraceReconstruction
namespace TraceReconstruction
end TraceReconstruction
open Filter
open scoped Topology
namespace TraceReconstruction
theorem QiN (N:ℕ) :
    (∑ k ∈ Z5 N,(Z0 (k+1:ℝ))⁻¹) ≤ 2*Z0 N:=by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn:0 ≤ (N:ℝ):=by positivity
    have hp:0 < Z0 (N+1:ℝ):=Real.sqrt_pos.2 (by positivity)
    have hs:Z0 (N:ℝ) ≤ Z0 (N+1:ℝ):=Z24 (by linarith)
    have h1:=Z13 hn
    have h2:=Z13 (show 0 ≤ (N+1:ℝ) by positivity)
    have hstep:(Z0 (N+1:ℝ))⁻¹ ≤ 2*(Z0 (N+1:ℝ)-Z0 N):=by
      apply (inv_le_iff_one_le_mul₀ hp).2
      nlinarith [sq_nonneg (Z0 (N+1:ℝ)-Z0 N)]
    push_cast
    linarith
theorem Qlg {h:ℝ} (hh:0 < h) (h1:h ≤ 1) :
    h/2 ≤ 1-Z1 (-h):=by
  have he:=Real.add_one_le_exp h
  have hp:0 < Z1 h:=Z74 h
  have hp':0 < 1+h:=by linarith
  have hinv:(Z1 h)⁻¹ ≤ (1+h)⁻¹:=inv_anti₀ hp' (by simpa [add_comm] using he)
  rw [Real.exp_neg]
  have hi:(1+h)⁻¹*(1+h)=1:=inv_mul_cancel₀ (ne_of_gt hp')
  nlinarith [mul_nonneg hh.le (sub_nonneg.mpr h1)]
theorem Qqv {h:ℝ} (hh:0 < h) (h1:h ≤ 1) (M:ℕ) :
    (∑ k ∈ Z5 M,Z1 (-h*(k:ℝ))) ≤ 2/h:=by
  have he:0 ≤ Z1 (-h):=(Z74 _).le
  have he1:Z1 (-h) < 1:=Real.exp_lt_one_iff.mpr (by linarith)
  have hf:(∑ k ∈ Z5 M,(Z1 (-h))^k) ≤ (1-Z1 (-h))⁻¹:=by
    rw [inv_eq_one_div,le_div_iff₀ (by linarith:0 < 1-Z1 (-h)),geom_sum_mul_neg]
    exact sub_le_self _ (pow_nonneg he M)
  have hi:(1-Z1 (-h))⁻¹ ≤ 2/h:=by
    rw [inv_le_iff_one_le_mul₀ (by linarith:0<1-Z1 (-h))]
    have hb:=Qlg hh h1
    have:=mul_le_mul_of_nonneg_right hb (show 0 ≤ 2/h by positivity)
    nlinarith [div_mul_cancel₀ (2:ℝ) hh.ne']
  calc
    _ = ∑ k ∈ Z5 M,(Z1 (-h))^k:=by
      apply Z2 rfl
      intro k _
      rw [← Z75]
      congr 1
      ring
    _ ≤ _:=hf.trans hi
theorem Qks {h:ℝ} (hh:0 < h) (h1:h ≤ 1) (M:ℕ) :
    (∑ k ∈ Z5 M,(Z0 (k+1:ℝ))⁻¹ *
      Z1 (-h*(k+1:ℝ))) ≤ 6/Z0 h:=by
  let N:=⌈1/h⌉₊
  have hN:1/h ≤ (N:ℝ):=Nat.le_ceil _
  have hNup:(N:ℝ) < 1/h+1:=Nat.ceil_lt_add_one (by positivity)
  have hs:0 < Z0 h:=Real.sqrt_pos.2 hh
  have hNsqrt:Z0 N ≤ 2/Z0 h:=by
    have hn:(N:ℝ)*h ≤ 2:=by
      have hx:=mul_le_mul_of_nonneg_right hNup.le hh.le
      have hc:(1/h)*h=1:=div_mul_cancel₀ _ hh.ne'
      nlinarith
    have hprod:Z0 N * Z0 h ≤ 2:=by
      have hsqh:=Z13 hh.le
      have hsqN:=Z13 (show 0≤(N:ℝ) by positivity)
      have hnon:0≤Z0 N*Z0 h:=by positivity
      nlinarith [sq_nonneg (Z0 N*Z0 h)]
    exact (le_div_iff₀ hs).2 hprod
  let low:=(Z5 M).filter (fun k => k<N)
  let high:=(Z5 M).filter (fun k => ¬k<N)
  have hlo:(∑ k ∈ low,(Z0 (k+1:ℝ))⁻¹ * Z1 (-h*(k+1:ℝ))) ≤
      2*Z0 N:=by
    calc
      _ ≤ ∑ k ∈ low,(Z0 (k+1:ℝ))⁻¹:=by
        apply Z7
        intro k hk
        exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [show (0:ℝ)≤k by positivity]))
      _ ≤ ∑ k ∈ Z5 N,(Z0 (k+1:ℝ))⁻¹:=by
        apply Z40
        · intro k hk
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
        · intros; positivity
      _ ≤ _:=QiN N
  have hhi:(∑ k ∈ high,(Z0 (k+1:ℝ))⁻¹ * Z1 (-h*(k+1:ℝ))) ≤
      Z0 h * (2/h):=by
    calc
      _ ≤ ∑ k ∈ high,Z0 h * Z1 (-h*(k:ℝ)):=by
        apply Z7
        intro k hk
        have hkN:N ≤ k:=Nat.le_of_not_gt (Finset.mem_filter.mp hk).2
        have hkR:1/h ≤ (k+1:ℝ):=hN.trans (by exact_mod_cast (by omega:N≤k+1))
        have hinv:(Z0 (k+1:ℝ))⁻¹ ≤ Z0 h:=by
          apply (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.2 (by positivity))).2
          have hmul:1 ≤ h*(k+1:ℝ):=by simpa [mul_comm] using (div_le_iff₀ hh).mp hkR
          have hsqh:=Z13 hh.le
          have hsqk:=Z13 (show 0≤(k+1:ℝ) by positivity)
          nlinarith [mul_nonneg (Z36 h) (Z36 (k+1:ℝ))]
        apply mul_le_mul hinv _ (Z74 _).le (Z36 _)
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ ∑ k ∈ Z5 M,Z0 h * Z1 (-h*(k:ℝ)):=by
        apply Z40 (Finset.filter_subset _ _)
        intros; positivity
      _ = Z0 h * ∑ k ∈ Z5 M,Z1 (-h*(k:ℝ)):=by rw [Z3]
      _ ≤ _:=mul_le_mul_of_nonneg_left (Qqv hh h1 M) (Z36 h)
  have hsum:(∑ k ∈ low,(Z0 (k+1:ℝ))⁻¹ * Z1 (-h*(k+1:ℝ))) +
      (∑ k ∈ high,(Z0 (k+1:ℝ))⁻¹ * Z1 (-h*(k+1:ℝ))) =
      ∑ k ∈ Z5 M,(Z0 (k+1:ℝ))⁻¹ * Z1 (-h*(k+1:ℝ)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hcancel:Z0 h*(2/h)=2/Z0 h:=by
    have hsq:=Z13 hh.le
    field_simp
    nlinarith
  rw [← hsum]
  rw [hcancel] at hhi
  have heq:2*(2/Z0 h)+2/Z0 h=6/Z0 h:=by ring
  linarith
end TraceReconstruction
namespace TraceReconstruction
theorem QkR (a:ℝ) (N:ℕ) :
    (∑ r ∈ Z5 N,a^r / (Z0 (r:ℝ))^r)^2 ≤
      2 * Z1 (2*a^2):=by
  let u (r:ℕ):ℝ:=(Z0 ((1/2:ℝ)^r))
  let v (r:ℕ):ℝ:=(Z0 ((2:ℝ)^r))*a^r/(Z0 (r:ℝ))^r
  have huv (r:ℕ):u r * v r = a^r/(Z0 (r:ℝ))^r:=by
    unfold u v
    have he:Z0 ((1/2:ℝ)^r) * Z0 ((2:ℝ)^r)=1:=by
      rw [← Real.sqrt_mul (by positivity),← mul_pow]
      norm_num
    calc
      _ = (Z0 ((1/2:ℝ)^r) * Z0 ((2:ℝ)^r)) * (a^r/(Z0 (r:ℝ))^r):=by ring
      _ = _:=by rw [he,one_mul]
  have hu:(∑ r ∈ Z5 N,(u r)^2) ≤ 2:=by
    simp only [u,Z13 (by positivity:0 ≤ (1/2:ℝ)^_)]
    have hg:=geom_sum_mul_neg (1/2:ℝ) N
    have hp:0≤(1/2:ℝ)^N:=by positivity
    linarith
  have hv:(∑ r ∈ Z5 N,(v r)^2) ≤ Z1 (2*a^2):=by
    apply le_trans _ (Real.sum_le_exp_of_nonneg (by positivity) N)
    apply Z7
    intro r _
    have hr:0 < ((r.factorial):ℝ):=by exact_mod_cast Nat.factorial_pos r
    have hrpow:0 < (r:ℝ)^r:=by
      cases r with
      | zero => norm_num
      | succ r => positivity
    have hfac:(r.factorial:ℝ) ≤ (r:ℝ)^r:=by exact_mod_cast Nat.factorial_le_pow r
    have hveq:(v r)^2 = (2*a^2)^r / (r:ℝ)^r:=by
      unfold v
      rw [div_pow,mul_pow,Z13 (by positivity)]
      have hd:((Z0 (r:ℝ))^r)^2=(r:ℝ)^r:=by
        rw [← pow_mul,mul_comm r 2,pow_mul,Z13 (by positivity)]
      rw [hd]
      rw [← pow_mul,mul_comm r 2,pow_mul]
      ring
    rw [hveq]
    exact div_le_div_of_nonneg_left (by positivity) hr hfac
  have hCS:=Z104 (Z5 N) u v
  simp only [huv] at hCS
  exact hCS.trans (mul_le_mul hu hv (by positivity) (by norm_num))
end TraceReconstruction
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
namespace TraceReconstruction
theorem QnF (n:ℕ):n+1 ≤ 2^n:=by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega
end TraceReconstruction
open Filter
open scoped Topology
open Filter
open scoped Topology
namespace TraceReconstruction
end TraceReconstruction
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
open Filter
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology
def PowerRate (N f:ℕ → ℝ) (a:ℝ):Prop :=
  (∀ᶠ t in Z9,0 < f t) ∧ Tendsto (fun t => Z8 (f t) / Z8 (N t)) Z9 (𝓝 a)
def PowerUpper (N f:ℕ → ℝ) (a:ℝ):Prop :=
  ∀ b,a < b → ∀ᶠ t in Z9,|f t| ≤ (N t)^b
variable {N f g:ℕ → ℝ} {a b:ℝ}
theorem PowerRate.congr (h:PowerRate N f a) (he:f =ᶠ[Z9] g):PowerRate N g a:=by
  constructor
  · filter_upwards [h.1,he] with t ht he; simpa [←he] using ht
  · exact h.2.congr' (he.mono fun t ht => by simp [ht])
theorem PowerRate.const (hN:Tendsto N Z9 Z9) {c:ℝ} (hc:0<c) :
    PowerRate N (fun _ => c) 0:=by
  exact ⟨Eventually.of_forall (fun _ => hc),(Real.tendsto_log_atTop.comp hN).const_div_atTop _⟩
theorem PowerRate.base (hN:Tendsto N Z9 Z9):PowerRate N N 1:=by
  have hn:=hN.eventually_gt_atTop 1
  refine ⟨hn.mono fun _ h => by linarith,?_⟩
  apply tendsto_congr' _ |>.mpr tendsto_const_nhds
  filter_upwards [hn] with t ht
  exact div_self (ne_of_gt (Z66 ht))
theorem PowerRate.mul (hf:PowerRate N f a) (hg:PowerRate N g b) :
    PowerRate N (fun t => f t*g t) (a+b):=by
  refine ⟨by filter_upwards [hf.1,hg.1] with t h ht; positivity,?_⟩
  apply (hf.2.add hg.2).congr'
  filter_upwards [hf.1,hg.1] with t h ht
  rw [Real.log_mul h.ne' ht.ne',add_div]
theorem PowerRate.div (hf:PowerRate N f a) (hg:PowerRate N g b) :
    PowerRate N (fun t => f t/g t) (a-b):=by
  refine ⟨by filter_upwards [hf.1,hg.1] with t h ht; positivity,?_⟩
  apply (hf.2.sub hg.2).congr'
  filter_upwards [hf.1,hg.1] with t h ht
  rw [Real.log_div h.ne' ht.ne',sub_div]
theorem PowerRate.rpow (hf:PowerRate N f a) (c:ℝ) :
    PowerRate N (fun t => (f t)^c) (a*c):=by
  refine ⟨by filter_upwards [hf.1] with t h; positivity,?_⟩
  apply (hf.2.mul_const c).congr'
  filter_upwards [hf.1] with t h
  rw [Real.log_rpow h]
  ring
theorem PowerRate.pow (hf:PowerRate N f a) (c:ℕ) :
    PowerRate N (fun t => (f t)^c) (a*c):=by
  simpa only [Z77] using hf.rpow (c:ℝ)
theorem PowerRate.sqrt (hf:PowerRate N f a) :
    PowerRate N (fun t => Z0 (f t)) (a/2):=by
  simpa only [Real.sqrt_eq_rpow,div_eq_mul_inv,one_mul] using hf.rpow (1/2:ℝ)
theorem PowerRate.inv (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a) :
    PowerRate N (fun t=>(f t)⁻¹) (-a):=by
  simpa only [one_div,zero_sub] using (PowerRate.const hN (by norm_num:(0:ℝ)<1)).div hf
theorem PowerRate.const_mul (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a)
    {c:ℝ} (hc:0<c):PowerRate N (fun t=>c*f t) a:=by
  simpa only [zero_add] using (PowerRate.const hN hc).mul hf
theorem PowerRate.mul_const (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a)
    {c:ℝ} (hc:0<c):PowerRate N (fun t=>f t*c) a:=by
  simpa only [add_zero] using hf.mul (PowerRate.const hN hc)
theorem PowerRate.div_const (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a)
    {c:ℝ} (hc:0<c):PowerRate N (fun t=>f t/c) a:=by
  simpa only [sub_zero] using hf.div (PowerRate.const hN hc)
theorem PowerRate.upper (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a) :
    PowerUpper N f a:=by
  intro b hb
  filter_upwards [hN.eventually_gt_atTop 1,hf.1,hf.2.eventually_lt_const hb] with t hn hp hab
  rw [abs_of_pos hp,←Real.log_le_log_iff hp (Real.rpow_pos_of_pos (by linarith) b),Real.log_rpow (by linarith:0<N t)]
  exact (div_lt_iff₀ (Z66 hn)).mp hab |>.le
theorem PowerRate.lower (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a) {c:ℝ}
    (hc:c<a):∀ᶠ t in Z9,(N t)^c ≤ f t:=by
  filter_upwards [hN.eventually_gt_atTop 1,hf.1,hf.2.eventually_const_lt hc] with t hn hp hac
  rw [←Real.log_le_log_iff (Real.rpow_pos_of_pos (by linarith) c) hp,Real.log_rpow (by linarith:0<N t)]
  exact (lt_div_iff₀ (Z66 hn)).mp hac |>.le
theorem PowerRate.Qdx (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a) (ha:0<a) :
    Tendsto f Z9 Z9:=by
  exact tendsto_atTop_mono' Z9 (hf.lower hN (show a/2<a by linarith))
    ((tendsto_rpow_atTop (show 0<a/2 by linarith)).comp hN)
theorem PowerUpper.mono (hf:PowerUpper N f a) (hab:a≤b):PowerUpper N f b :=
  fun c hc => hf c (lt_of_le_of_lt hab hc)
theorem PowerUpper.congr (hf:PowerUpper N f a) (he:f =ᶠ[Z9] g):PowerUpper N g a:=by
  intro b hb
  filter_upwards [hf b hb,he] with t h he
  simpa [←he] using h
theorem PowerUpper.of_abs_le (hg:PowerUpper N g a) (h:∀ᶠ t in Z9,|f t|≤|g t|) :
    PowerUpper N f a:=by
  intro b hb
  filter_upwards [hg b hb,h] with t ht hh
  exact hh.trans ht
theorem PowerUpper.zero (hN:Tendsto N Z9 Z9) (a:ℝ):PowerUpper N (fun _=>0) a:=by
  intro b hb
  filter_upwards [hN.eventually_gt_atTop 0] with t ht
  simpa using (Real.rpow_pos_of_pos ht b).le
theorem PowerUpper.mul (hN:Tendsto N Z9 Z9) (hf:PowerUpper N f a)
    (hg:PowerUpper N g b):PowerUpper N (fun t=>f t*g t) (a+b):=by
  intro c hc
  let δ:=(c-(a+b))/2
  have hd:0<δ:=by dsimp [δ]; linarith
  filter_upwards [hN.eventually_gt_atTop 0,hf (a+δ) (by linarith),hg (b+δ) (by linarith)] with t hn ht hs
  calc |f t*g t|=|f t| * |g t|:=abs_mul _ _
       _ ≤ (N t)^(a+δ)*(N t)^(b+δ):=mul_le_mul ht hs (abs_nonneg _) (by positivity)
       _ = (N t)^c:=by rw [←Real.rpow_add hn]; congr 1; dsimp [δ]; ring
theorem PowerUpper.pow (hN:Tendsto N Z9 Z9) (hf:PowerUpper N f a)
    (r:ℕ):PowerUpper N (fun t=>(f t)^r) (a*r):=by
  induction r with
  | zero => simpa using (PowerRate.const hN (by norm_num:(0:ℝ)<1)).upper hN
  | succ r ih =>
    have H:=ih.mul hN hf
    convert H using 1
    · ext t; exact pow_succ _ _
    · push_cast; ring
theorem PowerUpper.add (hN:Tendsto N Z9 Z9) (hf:PowerUpper N f a)
    (hg:PowerUpper N g a):PowerUpper N (fun t=>f t+g t) a:=by
  intro c hc
  let d:=(a+c)/2
  have had:a<d:=by dsimp [d]; linarith
  have hdc:d<c:=by dsimp [d]; linarith
  have hpow:=((tendsto_rpow_atTop (sub_pos.mpr hdc)).comp hN).eventually_ge_atTop 2
  filter_upwards [hN.eventually_gt_atTop 0,hf d had,hg d had,hpow] with t hn hf hg hp
  calc |f t+g t| ≤ |f t|+|g t|:=abs_add_le _ _
       _ ≤ 2*(N t)^d:=by linarith
       _ ≤ (N t)^(c-d)*(N t)^d:=mul_le_mul_of_nonneg_right hp (by positivity)
       _ = (N t)^c:=by rw [←Real.rpow_add hn]; congr 1; ring
theorem PowerUpper.sum {ι:Type*} (hN:Tendsto N Z9 Z9) (S:Finset ι)
    (f:ι→ℕ→ℝ) (h:∀i∈S,PowerUpper N (f i) a) :
    PowerUpper N (fun t=>∑i∈S,f i t) a:=by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using PowerUpper.zero hN a
  | @insert i S hi ih =>
    have hh:=(h i (Finset.mem_insert_self _ _)).add hN
      (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
    simpa only [Z87 hi] using hh
theorem PowerRate.add_const (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a)
    (ha:0<a) {c:ℝ} (hc:0≤c):PowerRate N (fun t=>f t+c) a:=by
  have ht:=hf.Qdx hN ha
  have hratio:Tendsto (fun t=>1+c/f t) Z9 (𝓝 1):=by
    simpa using (tendsto_const_nhds.add (ht.const_div_atTop c))
  have hl:Tendsto (fun t=>Z8 (1+c/f t)/Z8 (N t)) Z9 (𝓝 0) :=
    (hratio.log one_ne_zero).div_atTop (Real.tendsto_log_atTop.comp hN)
  refine ⟨by filter_upwards [hf.1] with t h; positivity,?_⟩
  have H:=hf.2.add hl
  simp only [add_zero] at H
  apply H.congr'
  filter_upwards [hf.1] with t hp
  have hh:0<1+c/f t:=by positivity
  rw [←add_div,←Real.log_mul hp.ne' hh.ne']
  congr 2
  field_simp
theorem PowerRate.of_tendsto (hN:Tendsto N Z9 Z9)
    {c:ℝ} (hc:0<c) (hf:Tendsto f Z9 (𝓝 c)):PowerRate N f 0:=by
  exact ⟨hf.eventually_const_lt hc,(hf.log hc.ne').div_atTop (Real.tendsto_log_atTop.comp hN)⟩
theorem PowerUpper.Qey (hN:Tendsto N Z9 Z9)
    (hf:PowerUpper N f a) (ha:a<0):Tendsto f Z9 (𝓝 0):=by
  have H:=(tendsto_rpow_neg_atTop (show 0< -(a/2) by linarith)).comp hN
  simp only [neg_neg] at H
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs,Z67] using hf (a/2) (by linarith)) H
theorem PowerRate.of_ratio (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a)
    {c:ℝ} (hc:0<c) (hr:Tendsto (fun t=>g t/f t) Z9 (𝓝 c)):PowerRate N g a:=by
  have hp:∀ᶠ t in Z9,0<g t:=by
    filter_upwards [hf.1,hr.eventually_const_lt hc] with t ht hgt
    exact (div_pos_iff.mp hgt).resolve_right (by intro h; linarith [h.2]) |>.1
  refine ⟨hp,?_⟩
  have hh:=(hr.log hc.ne').div_atTop (Real.tendsto_log_atTop.comp hN)
  have H:=hf.2.add hh
  simp only [add_zero] at H
  apply H.congr'
  filter_upwards [hf.1,hp] with t hf hg
  simp only [Z67]
  rw [Real.log_div hg.ne' hf.ne']
  ring
theorem PowerRate.nat_floor (hN:Tendsto N Z9 Z9) (hf:PowerRate N f a)
    (ha:0<a):PowerRate N (fun t=>(⌊f t⌋₊:ℝ)) a:=by
  exact hf.of_ratio hN (by norm_num:(0:ℝ)<1)
    (tendsto_nat_floor_div_atTop.comp (hf.Qdx hN ha))
theorem PowerRate.Qli (hN:Tendsto N Z9 Z9)
    (hf:PowerRate N f a) (ha:0<a) (c:ℝ) :
    PowerUpper N (fun t=>Z1 (-f t)) c:=by
  intro b hb
  have hh:=((isLittleO_log_rpow_atTop (show 0<a/2 by linarith)).tendsto_div_nhds_zero).comp hN
  have hsmall:=(hh.const_mul (-b)).eventually_lt_const (show (-b)*0<1 by simp)
  filter_upwards [hN.eventually_gt_atTop 0,hf.lower hN (show a/2<a by linarith),hsmall] with t hn hl hs
  rw [abs_of_pos (Z74 _),Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  have hpos:=Real.rpow_pos_of_pos hn (a/2)
  have hle:-b*Z8 (N t) ≤ (N t)^(a/2):=by
    have H:=(div_lt_iff₀ hpos).mp (show (-b*Z8 (N t))/(N t)^(a/2)<1 by simpa only [mul_div_assoc,Z67] using hs)
    linarith
  linarith
end TraceReconstruction
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
namespace TraceReconstruction
variable {α:Type*} [Fintype α]
def QbL (p:ℝ) (S:Finset α):ℝ :=
  p^S.card * (1-p)^(Z10 α-S.card)
abbrev QaG (α:Type*) [Fintype α] (l:ℕ):={S:Finset α // S.card=l}
theorem Qgo (l:ℕ) :
    Z10 (QaG α l)=(Z10 α).choose l:=by
  classical
  rw [Z98]
  have hset:(Finset.univ.filter (fun S:Finset α => S.card=l)) =
      (Z16:Finset α).powersetCard l:=by ext; simp
  rw [hset,Finset.card_powersetCard,Z48]
def QaO (l:ℕ) (hl:l ≤ Z10 α):FiniteLaw (QaG α l) where
  mass _:=1 / ((Z10 α).choose l:ℝ)
  nonneg _:=by positivity
  total:=by
    classical
    simp only [Z59,Z48,Qgo,nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast (Nat.choose_pos hl).ne')
def slotAtRank {n l:ℕ} (S:QaG (Fin n) l) (v:Fin l):Fin n :=
  (S.val.orderIsoOfFin S.property v).val
theorem Qqa {n l:ℕ} (S:QaG (Fin n) l) (v:Fin l) :
    slotAtRank S v ∈ S.val:=(S.val.orderIsoOfFin S.property v).property
theorem Qqc {n l:ℕ} (S:QaG (Fin n) l) :
    StrictMono (slotAtRank S):=by
  classical
  intro a b hab
  exact (S.val.orderIsoOfFin S.property).strictMono hab
def QaY {n l:ℕ} (D:Finset (Fin n)) (S:QaG (Fin n) l)
    (v:Fin l):Bool:=decide (slotAtRank S v ∈ D)
def Qcq {n l r:ℕ} (p:Fin r → Fin n) (v:Fin r → Fin l)
    (S:QaG (Fin n) l):Prop:=∀ i,slotAtRank S (v i)=p i
def Qaw {n l r:ℕ} (hl:l≤n) (p:Fin r → Fin n) (v:Fin r → Fin l):ℝ:=by
  classical
  exact ∑ S:QaG (Fin n) l,if Qcq p v S then
    (QaO l (by simpa using hl)).mass S else 0
theorem Qdw {n l r:ℕ} (hl:l≤n)
    (p:Fin r → Fin n) (v:Fin r → Fin l):0 ≤ Qaw hl p v:=by
  classical
  unfold Qaw
  apply Z11
  intro S _
  split_ifs
  · exact (QaO l (by simpa using hl)).nonneg S
  · rfl
abbrev QaU (r d:ℕ) (g:Fin d → ℕ):=Fin r ⊕ ((i:Fin d) × Fin (g i))
def gapDecode {r d:ℕ} {g:Fin d → ℕ} (S:Finset (QaU r d g))
    (i:Fin d):Finset (Fin (g i)) :=
  Finset.univ.filter fun a => Sum.inr ⟨i,a⟩ ∈ S
def gapEncode {r d:ℕ} {g:Fin d → ℕ} (A:(i:Fin d) → Finset (Fin (g i))) :
    Finset (QaU r d g):=by
  classical
  exact Finset.univ.filter fun x => match x with
    | Sum.inl _ => True
    | Sum.inr a => a.2 ∈ A a.1
@[simp] theorem Qrp {r d:ℕ} {g:Fin d → ℕ}
    (A:(i:Fin d) → Finset (Fin (g i))) (a:Fin r) :
    Sum.inl a ∈ gapEncode A:=by simp [gapEncode]
@[simp] theorem Qrq {r d:ℕ} {g:Fin d → ℕ}
    (A:(i:Fin d) → Finset (Fin (g i))) (i:Fin d) (a:Fin (g i)) :
    Sum.inr ⟨i,a⟩ ∈ gapEncode (r:=r) A ↔ a ∈ A i:=by simp [gapEncode]
@[simp] theorem QgY {r d:ℕ} {g:Fin d → ℕ}
    (A:(i:Fin d) → Finset (Fin (g i))) (i:Fin d) :
    gapDecode (gapEncode (r:=r) A) i=A i:=by ext; simp [gapDecode]
theorem Qen {r d:ℕ} {g:Fin d → ℕ}
    (S:Finset (QaU r d g)) (hS:∀ a,Sum.inl a∈S) :
    gapEncode (gapDecode S)=S:=by
  ext x
  cases x with
  | inl a => simp [hS]
  | inr a => rcases a with ⟨i,a⟩; simp [gapDecode]
def gapEvent {r d:ℕ} {g:Fin d → ℕ} (z:Fin d → ℕ)
    (S:Finset (QaU r d g)):Prop :=
  (∀ a,Sum.inl a∈S) ∧ ∀ i,(gapDecode S i).card=z i
instance Qrm {r d:ℕ} {g:Fin d → ℕ} (z:Fin d → ℕ)
    (S:Finset (QaU r d g)):Decidable (gapEvent z S):=by
  unfold gapEvent
  infer_instance
def QlI {r d:ℕ} {g z:Fin d → ℕ} :
    {S:Finset (QaU r d g) // gapEvent z S} ≃
      ((i:Fin d) → QaG (Fin (g i)) (z i)) where
  toFun S i:=⟨gapDecode S.val i,S.property.2 i⟩
  invFun A:=⟨gapEncode (fun i => (A i).val),by
    constructor
    · intro a; simp
    · intro i; simp only [QgY,(A i).property]⟩
  left_inv S:=by
    apply Subtype.ext
    exact Qen S.val S.property.1
  right_inv A:=by
    funext i
    apply Subtype.ext
    change gapDecode (gapEncode (fun i => (A i).val)) i = (A i).val
    exact QgY _ _
theorem QeR {r d:ℕ} (g z:Fin d → ℕ) :
    Z10 {S:Finset (QaU r d g) // gapEvent z S} =
      ∏ i,(g i).choose (z i):=by
  classical
  rw [Fintype.card_congr QlI,Fintype.card_pi]
  simp only [Qgo,Z26]
theorem Qgp {r d:ℕ} {g:Fin d → ℕ}
    (A:(i:Fin d) → Finset (Fin (g i))) :
    (gapEncode (r:=r) A).card = r + ∑ i,(A i).card:=by
  classical
  rw [Finset.card_eq_sum_ones]
  simp only [gapEncode,Z27]
  rw [Fintype.sum_sum_type,Z83]
  simp
  apply Z2 rfl
  intro i _
  calc
    _ = ∑ x:Fin (g i),if x ∈ A i then (1:ℕ) else 0:=by
      apply Z2 rfl
      intro x _
      split_ifs <;> rfl
    _ = _:=(Finset.card_eq_sum_ite (Z56 (A i))).symm
theorem QeS {r d:ℕ} {g z:Fin d → ℕ}
    (S:Finset (QaU r d g)) (hS:gapEvent z S) :
    S.card = r+∑ i,z i:=by
  rw [← Qen S hS.1,Qgp]
  simp only [hS.2]
theorem QlJ {r d:ℕ} (g z:Fin d → ℕ)
    (hz:∀ i,z i≤g i) (p:ℝ) :
    (∑ S:Finset (QaU r d g),if gapEvent z S then QbL p S else 0) =
      p^r * ∏ i,Qaa (g i) p (z i):=by
  classical
  have hcount:(∑ S:Finset (QaU r d g),
      if gapEvent z S then (1:ℝ) else 0) = ∏ i,((g i).choose (z i):ℝ):=by
    rw [Finset.sum_boole,← Z98,QeR,Nat.cast_prod]
  have hnum:(∑ S:Finset (QaU r d g),if gapEvent z S then QbL p S else 0) =
      (∏ i,((g i).choose (z i):ℝ)) *
        (p^(r+∑ i,z i)*(1-p)^(r+∑ i,g i-(r+∑ i,z i))):=by
    rw [← hcount,Z33]
    apply Z2 rfl
    intro S _
    split_ifs with hS
    · simp only [one_mul,QbL,QeS S hS,
        Fintype.card_sum,Z26,Fintype.card_sigma]
    · exact (zero_mul _).symm
  have hsub:(∑ i,g i)-(∑ i,z i)=∑ i,(g i-z i):=by
    exact (Finset.sum_tsub_distrib Z16 (fun i _ => hz i)).symm
  rw [hnum,Nat.add_sub_add_left,hsub,pow_add]
  simp only [Qaa,Z30,Z99]
  ring
theorem QlL {r d:ℕ} (g z:Fin d → ℕ)
    (hz:∀ i,z i≤g i) (p:ℝ) :
    (∑ S:Finset (QaU r d g),if gapEvent z S then QbL p S else 0) /
      Qaa (r+∑ i,g i) p (r+∑ i,z i) =
    p^r / Qaa (r+∑ i,g i) p (r+∑ i,z i) *
      ∏ i,Qaa (g i) p (z i):=by
  rw [QlJ g z hz]
  ring
end TraceReconstruction
namespace TraceReconstruction
theorem QiG {n l:ℕ} (S:QaG (Fin n) l) (v:Fin l) :
    (S.val.filter fun j => j < slotAtRank S v).card = v.val:=by
  classical
  let e:=S.val.orderEmbOfFin S.property
  have hslot (i:Fin l):e i = slotAtRank S i:=rfl
  have hmap:(Finset.Iio v).map e.toEmbedding = S.val.filter (fun j => j<e v):=by
    ext j
    simp only [Finset.mem_map,Finset.mem_Iio,Finset.mem_filter,RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨S.val.orderEmbOfFin_mem S.property i,e.strictMono hi⟩
    · rintro ⟨hj,hv⟩
      obtain ⟨i,hi⟩:=(S.val.orderIsoOfFin S.property).surjective ⟨j,hj⟩
      have hei:e i=j:=congrArg Subtype.val hi
      refine ⟨i,?_,hei⟩
      exact e.lt_iff_lt.mp (hei.symm ▸ hv)
  rw [← hslot,← hmap,Finset.card_map,Fin.card_Iio]
theorem QfH {n l:ℕ} (S:QaG (Fin n) l) (v:Fin l) (p:Fin n) :
    slotAtRank S v=p ↔ p∈S.val ∧ (S.val.filter fun j => j<p).card=v.val:=by
  classical
  constructor
  · intro h
    rw [← h]
    exact ⟨Qqa S v,QiG S v⟩
  · rintro ⟨hp,hcard⟩
    obtain ⟨i,hi⟩:=(S.val.orderIsoOfFin S.property).surjective ⟨p,hp⟩
    have he:slotAtRank S i=p:=congrArg Subtype.val hi
    have hcv:=QiG S i
    rw [he,hcard] at hcv
    have hiv:i=v:=Z34 hcv.symm
    simpa [hiv] using he
def tupleLower {n r:ℕ} (p:Fin r → Fin n):Fin (r+1) → ℕ :=
  Z15 0 (fun i => (p i).val + 1)
def tupleUpper {n r:ℕ} (p:Fin r → Fin n):Fin (r+1) → ℕ :=
  Fin.snoc (fun i => (p i).val) n
def tupleGap {n r:ℕ} (p:Fin r → Fin n) (j:Fin (r+1)):ℕ :=
  tupleUpper p j - tupleLower p j
@[simp] theorem QqS {n r:ℕ} (p:Fin r → Fin n):tupleLower p 0 = 0 :=
  Z54 _ _
@[simp] theorem Qea {n r:ℕ} (p:Fin r → Fin n) (i:Fin r) :
    tupleLower p i.succ = (p i).val + 1:=Z55 _ _ _
@[simp] theorem QeF {n r:ℕ} (p:Fin r → Fin n) (i:Fin r) :
    tupleUpper p i.castSucc = (p i).val:=Fin.snoc_castSucc _ _ _
@[simp] theorem QqU {n r:ℕ} (p:Fin r → Fin n) :
    tupleUpper p (Z22 r) = n:=Fin.snoc_last _ _
theorem QqP {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (i:Fin r) (j:Fin (r+1)) (hji:j ≤ i.castSucc) :
    tupleLower p j ≤ (p i).val:=by
  induction j using Z38 with
  | zero => simp
  | succ a =>
    simp only [Qea]
    have hai:a < i:=by
      change a.val < i.val
      have hh:a.val + 1 ≤ i.val:=hji
      omega
    exact hp hai
theorem QiO {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (i:Fin r) (j:Fin (r+1)) (hij:i.castSucc < j) :
    (p i).val < tupleLower p j:=by
  induction j using Z38 with
  | zero => exact False.elim (by simp at hij)
  | succ a =>
    simp only [Qea]
    have hia:i ≤ a:=by
      change i.val ≤ a.val
      have hh:i.val < a.val + 1:=hij
      omega
    exact Z72 (hp.monotone hia)
theorem QqV {n r:ℕ} (p:Fin r → Fin n) (j:Fin (r+1)) :
    tupleUpper p j ≤ n:=by
  induction j using Z60 with
  | last => simp
  | cast i => simpa only [QeF] using (p i).isLt.le
theorem QqQ {n r:ℕ} (p:Fin r → Fin n) (j:Fin (r+1)) :
    tupleLower p j ≤ n:=by
  induction j using Z38 with
  | zero => simp
  | succ i => simpa only [Qea] using Z68 (p i).isLt
theorem QqR {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (j:Fin (r+1)):tupleLower p j ≤ tupleUpper p j:=by
  induction j using Z60 with
  | last => simpa using QqQ p (Z22 r)
  | cast i => simpa using QqP p hp i i.castSucc le_rfl
theorem QcA {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p) :
    r + ∑ j,tupleGap p j = n:=by
  have hrs:r ≤ n:=by simpa using Fintype.card_le_of_injective p hp.injective
  have ha:(∑ j,tupleLower p j) = (∑ i,(p i).val) + r:=by
    rw [Z64]
    simp [Z14]
  have hb:(∑ j,tupleUpper p j) = (∑ i,(p i).val) + n:=by
    rw [Fin.sum_univ_castSucc]
    simp
  simp only [tupleGap]
  rw [Finset.sum_tsub_distrib _ (fun j _ => QqR p hp j),ha,hb]
  omega
def Qbz {n r:ℕ} (p:Fin r → Fin n) :
    QaU r (r+1) (tupleGap p) → Fin n
  | .inl i => p i
  | .inr ⟨j,a⟩ => ⟨tupleLower p j + a.val,by
      have hx:=a.isLt
      have hu:=QqV p j
      simp only [tupleGap] at hx
      omega⟩
theorem Qdz {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (i:Fin r) (j:Fin (r+1)) (a:Fin (tupleGap p j)) :
    Qbz p (.inr ⟨j,a⟩) < p i ↔ j ≤ i.castSucc:=by
  constructor
  · intro h
    by_contra hn
    have hx:=QiO p hp i j (lt_of_not_ge hn)
    change tupleLower p j + a.val < (p i).val at h
    omega
  · intro h
    have hji:j.val < r:=lt_of_le_of_lt (show j.val ≤ i.val from h) i.isLt
    let k:Fin r:=⟨j.val,hji⟩
    have hjk:j = k.castSucc:=Z34 rfl
    have ht:tupleUpper p j ≤ (p i).val:=by
      rw [hjk,QeF]
      exact hp.monotone (show k ≤ i from h)
    have hx:=a.isLt
    change tupleLower p j + a.val < (p i).val
    unfold tupleGap at hx
    omega
theorem QeB {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (i:Fin r) (j:Fin (r+1)) (a:Fin (tupleGap p j)) :
    p i < Qbz p (.inr ⟨j,a⟩) ↔ i.castSucc < j:=by
  constructor
  · intro h
    by_contra hn
    have hx:=(Qdz p hp i j a).2 (le_of_not_gt hn)
    exact (lt_asymm h hx)
  · intro h
    have hx:=QiO p hp i j h
    change (p i).val < tupleLower p j + a.val
    omega
theorem QqM {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p) :
    Z28 (Qbz p):=by
  rintro (i | ⟨j,a⟩) (i' | ⟨j',a'⟩) h
  · exact congrArg Sum.inl (hp.injective h)
  · have hn:p i ≠ Qbz p (.inr ⟨j',a'⟩):=by
      rcases le_or_gt j' i.castSucc with hj | hj
      · exact ne_of_gt ((Qdz p hp i j' a').2 hj)
      · exact ne_of_lt ((QeB p hp i j' a').2 hj)
    exact False.elim (hn h)
  · have hn:p i' ≠ Qbz p (.inr ⟨j,a⟩):=by
      rcases le_or_gt j i'.castSucc with hj | hj
      · exact ne_of_gt ((Qdz p hp i' j a).2 hj)
      · exact ne_of_lt ((QeB p hp i' j a).2 hj)
    exact False.elim (hn h.symm)
  · have hj:j=j':=by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hj | hj
      · let i:Fin r:=⟨j.val,lt_of_lt_of_le hj (Z63 j'.isLt)⟩
        have hji:j=i.castSucc:=Z34 rfl
        have h1:=(Qdz p hp i j a).2 (by rw [hji])
        have h2:=(QeB p hp i j' a').2 (by rwa [← hji])
        rw [h] at h1
        exact (lt_asymm h1 h2)
      · let i:Fin r:=⟨j'.val,lt_of_lt_of_le hj (Z63 j.isLt)⟩
        have hji:j'=i.castSucc:=Z34 rfl
        have h1:=(Qdz p hp i j' a').2 (by rw [hji])
        have h2:=(QeB p hp i j a).2 (by rwa [← hji])
        rw [h] at h2
        exact (lt_asymm h1 h2)
    subst j'
    have ha:a=a':=by
      apply Z34
      have hh:=congrArg Fin.val h
      change tupleLower p j + a.val = tupleLower p j + a'.val at hh
      omega
    subst a'
    rfl
def Qcr {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p) :
    QaU r (r+1) (tupleGap p) ≃ Fin n :=
  Equiv.ofBijective (Qbz p) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨QqM p hp,by
      simp only [Fintype.card_sum,Fintype.card_sigma,Z26]
      exact QcA p hp⟩)
theorem QgZ {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (A:(j:Fin (r+1)) → Finset (Fin (tupleGap p j))) (i:Fin r) :
    (((gapEncode A).map (Qcr p hp).toEmbedding).filter
      fun x => x < p i).card = i.val + ∑ j ∈ Z31 i.castSucc,(A j).card:=by
  classical
  have hmap:(((gapEncode A).map (Qcr p hp).toEmbedding).filter
      fun x => x < p i) =
      ((gapEncode A).filter fun x => Qbz p x < p i).map
        (Qcr p hp).toEmbedding:=by
    rw [Finset.filter_map]
    rfl
  rw [hmap,Finset.card_map,Finset.card_eq_sum_ones]
  simp only [Z27,gapEncode]
  rw [Fintype.sum_sum_type,Z83]
  simp only
  simp only [↓reduceIte]
  have hleft:(∑ a:Fin r,if Qbz p (.inl a) < p i then (1:ℕ) else 0) = i.val:=by
    simp only [Qbz,hp.lt_iff_lt]
    have hx:(Finset.univ.filter fun a:Fin r => a < i) = Finset.Iio i:=by ext; simp
    rw [← Z27,hx,Z59,Fin.card_Iio,smul_eq_mul,mul_one]
  rw [hleft]
  congr 1
  simp_rw [Qdz p hp]
  have hr (j:Fin (r+1)) :
      (∑ a:Fin (tupleGap p j),if a ∈ A j then
        (if j ≤ i.castSucc then (1:ℕ) else 0) else 0) =
      if j ≤ i.castSucc then (A j).card else 0:=by
    by_cases hj:j ≤ i.castSucc
    · simp only [hj,ite_true]
      exact (Finset.card_eq_sum_ite (Z56 (A j))).symm
    · simp [hj]
  rw [Z2 rfl (fun j _ => hr j),← Z27]
  congr 1
  ext j
  simp
@[simp] theorem QlH {r d:ℕ} {g:Fin d → ℕ} :
    gapEncode (r:=r) (fun i => (Z16:Finset (Fin (g i)))) = Z16:=by
  ext x
  cases x with
  | inl i => simp
  | inr p => rcases p with ⟨j,a⟩; simp
theorem QcQ {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (i:Fin r):i.val + ∑ j ∈ Z31 i.castSucc,tupleGap p j = (p i).val:=by
  have h:=QgZ p hp (fun _ => Z16) i
  have hset:(Finset.univ.filter fun x:Fin n => x < p i) = Finset.Iio (p i):=by
    ext; simp
  simpa only [QlH,Finset.map_univ_equiv,
    hset,Fin.card_Iio,Z48,Z26] using h.symm
theorem QlB {d:ℕ} (f g:Fin d → ℕ)
    (h:∀ i,(∑ j ∈ Z31 i,f j) = ∑ j ∈ Z31 i,g j):f=g:=by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hset:Z31 i = insert i (Finset.Iio i):=by ext; simp
    have hprev:(∑ j ∈ Finset.Iio i,f j) = ∑ j ∈ Finset.Iio i,g j:=by
      apply Z2 rfl
      intro j hj
      exact ih j (Finset.mem_Iio.mp hj)
    have hh:=h i
    rw [hset,Z87 (by simp),Z87 (by simp),hprev] at hh
    omega
def pullGapSet {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (S:Finset (Fin n)):Finset (QaU r (r+1) (tupleGap p)) :=
  S.map (Qcr p hp).symm.toEmbedding
@[simp] theorem Qer {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (S:Finset (Fin n)) (x:QaU r (r+1) (tupleGap p)) :
    x ∈ pullGapSet p hp S ↔ Qbz p x ∈ S:=by
  simp [pullGapSet,Qcr]
@[simp] theorem QhB {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (S:Finset (Fin n)) :
    (pullGapSet p hp S).map (Qcr p hp).toEmbedding = S:=by
  ext x
  simp only [pullGapSet,Finset.mem_map_equiv,Equiv.symm_symm,Z103]
@[simp] theorem Qir {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (T:Finset (QaU r (r+1) (tupleGap p))) :
    pullGapSet p hp (T.map (Qcr p hp).toEmbedding) = T:=by
  ext x
  simp only [pullGapSet,Finset.mem_map_equiv,Equiv.symm_symm,Equiv.symm_apply_apply]
theorem Qiq {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (S:Finset (Fin n)) (hS:∀ i,p i ∈ S) (i:Fin r) :
    (S.filter fun x => x < p i).card =
      i.val + ∑ j ∈ Z31 i.castSucc,(gapDecode (pullGapSet p hp S) j).card:=by
  have hT:∀ a,Sum.inl a ∈ pullGapSet p hp S:=by
    intro a
    simpa only [Qer,Qbz] using hS a
  have h:=QgZ p hp (gapDecode (pullGapSet p hp S)) i
  rwa [Qen _ hT,QhB] at h
theorem Qpf {n r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (S:Finset (Fin n)) (hS:∀ i,p i ∈ S) :
    S.card = r + ∑ j,(gapDecode (pullGapSet p hp S) j).card:=by
  have hT:∀ a,Sum.inl a ∈ pullGapSet p hp S:=by
    intro a
    simpa only [Qer,Qbz] using hS a
  have h:=Qgp (r:=r) (gapDecode (pullGapSet p hp S))
  rw [Qen _ hT] at h
  simpa only [pullGapSet,Finset.card_map] using h
theorem QiP {n l r:ℕ} (p:Fin r → Fin n)
    (hp:StrictMono p) (v:Fin r → Fin l) (hv:StrictMono v)
    (S:QaG (Fin n) l) :
    Qcq p v S ↔ gapEvent (tupleGap v) (pullGapSet p hp S.val):=by
  constructor
  · intro h
    have hS:∀ i,p i ∈ S.val:=fun i => (QfH S (v i) (p i)).mp (h i) |>.1
    have hbefore:∀ i,(S.val.filter fun x => x < p i).card = (v i).val :=
      fun i => (QfH S (v i) (p i)).mp (h i) |>.2
    refine ⟨?_,?_⟩
    · intro i
      simpa only [Qer,Qbz] using hS i
    · have heq:(fun j => (gapDecode (pullGapSet p hp S.val) j).card) = tupleGap v:=by
        apply QlB
        intro j
        induction j using Z60 with
        | last =>
          have htot:=Qpf p hp S.val hS
          have hvtot:=QcA v hv
          have hset:Z31 (Z22 r) = Z16:=by ext; simp [Fin.le_last]
          rw [hset]
          rw [S.property] at htot
          omega
        | cast i =>
          have hpre:=Qiq p hp S.val hS i
          rw [hbefore i] at hpre
          have hvpre:=QcQ v hv i
          omega
      intro j
      exact congrFun heq j
  · intro h
    have hS:∀ i,p i ∈ S.val:=by
      intro i
      simpa only [Qer,Qbz] using h.1 i
    intro i
    apply (QfH S (v i) (p i)).2
    refine ⟨hS i,?_⟩
    rw [Qiq p hp S.val hS i]
    simp_rw [h.2]
    exact QcQ v hv i
instance Qrs {n l r:ℕ} (p:Fin r → Fin n)
    (v:Fin r → Fin l) (S:QaG (Fin n) l):Decidable (Qcq p v S):=by
  unfold Qcq
  infer_instance
def Qpi {n l r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (v:Fin r → Fin l) (hv:StrictMono v) :
    {S:QaG (Fin n) l // Qcq p v S} ≃
      {T:Finset (QaU r (r+1) (tupleGap p)) // gapEvent (tupleGap v) T} where
  toFun S:=⟨pullGapSet p hp S.val.val,(QiP p hp v hv S.val).mp S.property⟩
  invFun T :=
    let S:QaG (Fin n) l:=⟨T.val.map (Qcr p hp).toEmbedding,by
      rw [Finset.card_map,QeS T.val T.property,QcA v hv]⟩
    ⟨S,(QiP p hp v hv S).mpr (by
      change gapEvent (tupleGap v) (pullGapSet p hp (T.val.map (Qcr p hp).toEmbedding))
      rw [Qir]
      exact T.property)⟩
  left_inv S:=by
    apply Subtype.ext
    apply Subtype.ext
    exact QhB p hp S.val.val
  right_inv T:=by
    apply Subtype.ext
    exact Qir p hp T.val
theorem Qkc {n l r:ℕ} (p:Fin r → Fin n) (hp:StrictMono p)
    (v:Fin r → Fin l) (hv:StrictMono v) :
    Z10 {S:QaG (Fin n) l // Qcq p v S} =
      ∏ j,(tupleGap p j).choose (tupleGap v j):=by
  classical
  rw [Fintype.card_congr (Qpi p hp v hv),QeR]
theorem QiM {n l r:ℕ} (hl:l ≤ n)
    (p:Fin r → Fin n) (hp:StrictMono p) (v:Fin r → Fin l) (hv:StrictMono v) :
    Qaw hl p v =
      (∏ j,((tupleGap p j).choose (tupleGap v j):ℝ)) / (n.choose l:ℝ):=by
  classical
  unfold Qaw
  simp only [QaO,Z26]
  rw [← Z27,Z59,nsmul_eq_mul,
    ← Z98,Qkc p hp v hv,Nat.cast_prod]
  ring
theorem QlK {r d:ℕ} (g z:Fin d → ℕ)
    (p:ℝ) (hp:p ∈ Z4 0 1) :
    (∑ S:Finset (QaU r d g),if gapEvent z S then QbL p S else 0) /
      Qaa (r+∑ i,g i) p (r+∑ i,z i) =
    (∏ i,((g i).choose (z i):ℝ)) /
      ((r+∑ i,g i).choose (r+∑ i,z i):ℝ):=by
  classical
  have hcount:(∑ S:Finset (QaU r d g),
      if gapEvent z S then (1:ℝ) else 0) = ∏ i,((g i).choose (z i):ℝ):=by
    rw [Finset.sum_boole,← Z98,QeR,Nat.cast_prod]
  have hnum:(∑ S:Finset (QaU r d g),if gapEvent z S then QbL p S else 0) =
      (∏ i,((g i).choose (z i):ℝ)) *
        (p^(r+∑ i,z i)*(1-p)^(r+∑ i,g i-(r+∑ i,z i))):=by
    rw [← hcount,Z33]
    apply Z2 rfl
    intro S _
    split_ifs with hS
    · simp only [one_mul,QbL,QeS S hS,
        Fintype.card_sum,Z26,Fintype.card_sigma]
    · exact (zero_mul _).symm
  rw [hnum,Qaa]
  have hp0:p ≠ 0:=hp.1.ne'
  have hq0:1-p ≠ 0:=by linarith [hp.2]
  rw [mul_assoc,mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hq0))]
theorem Qex {n l r:ℕ} (hl:l ≤ n)
    (p:Fin r → Fin n) (hp:StrictMono p) (v:Fin r → Fin l) (hv:StrictMono v)
    (θ:ℝ) (hθ:θ ∈ Z4 0 1) :
    Qaw hl p v = θ^r / Qaa n θ l *
      ∏ j,Qaa (tupleGap p j) θ (tupleGap v j):=by
  classical
  by_cases hz:∀ j,tupleGap v j ≤ tupleGap p j
  · have h1:=QlK (r:=r) (tupleGap p) (tupleGap v) θ hθ
    have h2:=QlL (r:=r) (tupleGap p) (tupleGap v) hz θ
    rw [QcA p hp,QcA v hv] at h1 h2
    rw [QiM hl p hp v hv,← h1,h2]
  · push Not at hz
    obtain ⟨j,hj⟩:=hz
    have hc:(tupleGap p j).choose (tupleGap v j) = 0:=Z44 hj
    have hz1:(∏ j,((tupleGap p j).choose (tupleGap v j):ℝ))=0 :=
      Z69 (Z21 j) (by simp [hc])
    have hz2:(∏ j,Qaa (tupleGap p j) θ (tupleGap v j))=0 :=
      Z69 (Z21 j) (by simp [Qaa,hc])
    rw [QiM hl p hp v hv,hz1,hz2]
    simp
end TraceReconstruction
namespace TraceReconstruction
def Qad {u r:ℕ} (j:Fin r → Fin u) (i:Fin (r+1)):ℕ :=
  2 * tupleGap j i + if i = 0 ∨ i = Z22 r then 1 else 2
theorem QcB {u r:ℕ} (j:Fin r → Fin u) (i:Fin (r+1)) :
    1 ≤ Qad j i:=by
  unfold Qad
  split_ifs <;> omega
theorem Qda {u r:ℕ} (hr:0 < r) (j:Fin r → Fin u)
    (hj:StrictMono j):∑ i,Qad j i = 2*u:=by
  classical
  have hc:(∑ i:Fin (r+1),if i = 0 ∨ i = Z22 r then 1 else 2) = 2*r:=by
    obtain ⟨d,rfl⟩:=Z106 (Nat.ne_of_gt hr)
    rw [Z64]
    simp only [true_or,↓reduceIte,Fin.succ_ne_zero,false_or]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_last,↓reduceIte]
    have hx (i:Fin d):i.castSucc.succ ≠ Z22 (d+1):=by
      intro h
      have hv:=congrArg Fin.val h
      simp only [Fin.val_succ,Fin.val_castSucc,Fin.val_last] at hv
      omega
    simp only [hx,↓reduceIte,Z59,Z48,Z26,
      smul_eq_mul]
    omega
  simp only [Qad,Z14,← Z3]
  have ht:=QcA j hj
  omega
theorem QcZ {u r:ℕ} (hr:0 < r) (j:Fin r → Fin u)
    (hj:StrictMono j) (i:Fin (r+1)):Qad j i ≤ 2*u:=by
  rw [← Qda hr j hj]
  exact Z82 (fun _ _ => Nat.zero_le _) (Z21 i)
theorem QqN {n r:ℕ} {p q:Fin r → Fin n}
    (hp:StrictMono p) (hq:StrictMono q) (h:tupleGap p = tupleGap q):p=q:=by
  funext i
  apply Z34
  have hp':=QcQ p hp i
  have hq':=QcQ q hq i
  rw [h] at hp'
  omega
theorem QeT {u r:ℕ} {j k:Fin r → Fin u}
    (hj:StrictMono j) (hk:StrictMono k) (h:Qad j = Qad k) :
    j=k:=by
  apply QqN hj hk
  funext i
  have hi:=congrFun h i
  unfold Qad at hi
  omega
def periodSlot {u m:ℕ} (off:Fin u → Fin m) (j:Fin u):Fin (u*m) :=
  ⟨j.val*m + (off j).val,by
    have h:=(off j).isLt
    have h':=Z51 m (Z68 j.isLt)
    nlinarith⟩
theorem QdO {u m:ℕ} (off:Fin u → Fin m) :
    StrictMono (periodSlot off):=by
  intro j k hjk
  change j.val*m + (off j).val < k.val*m + (off k).val
  have hjk':j.val+1 ≤ k.val:=hjk
  have ho:=(off j).isLt
  have hm:=Z51 m hjk'
  nlinarith
theorem QeD {n r:ℕ} (p:Fin (r+1) → Fin n) :
    tupleGap p 0 = (p 0).val:=by
  have he:(0:Fin (r+2)) = (0:Fin (r+1)).castSucc:=rfl
  unfold tupleGap
  rw [QqS,Nat.sub_zero,he,QeF]
theorem QeC {n r:ℕ} (p:Fin (r+1) → Fin n) :
    tupleGap p (Z22 (r+1)) = n - ((p (Z22 r)).val+1):=by
  unfold tupleGap
  rw [QqU,← Fin.succ_last,Qea]
theorem QdZ {n r:ℕ} (p:Fin (r+1) → Fin n) (i:Fin r) :
    tupleGap p i.castSucc.succ = (p i.succ).val - ((p i.castSucc).val+1):=by
  unfold tupleGap
  rw [Qea,Z100,QeF]
theorem Qkp {u r:ℕ} (j:Fin (r+1) → Fin u) :
    Qad j 0 = 2*(j 0).val+1:=by
  simp only [Qad,QeD,true_or,↓reduceIte]
theorem Qkn {u r:ℕ} (j:Fin (r+1) → Fin u) :
    Qad j (Z22 (r+1)) = 2*(u-((j (Z22 r)).val+1))+1:=by
  simp only [Qad,QeC,or_true,↓reduceIte]
theorem Qgr {u r:ℕ} (j:Fin (r+1) → Fin u) (i:Fin r) :
    Qad j i.castSucc.succ = 2*((j i.succ).val-((j i.castSucc).val+1))+2:=by
  have hn:i.castSucc.succ ≠ Z22 (r+1):=by
    intro h
    have hv:=congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_castSucc,Fin.val_last] at hv
    omega
  simp only [Qad,QdZ,Fin.succ_ne_zero,hn,or_self,↓reduceIte]
theorem Qfx {u m r:ℕ} (hr:0 < r)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j:Fin r → Fin u) (hj:StrictMono j) (i:Fin (r+1)) :
    |(tupleGap (periodSlot off ∘ j) i:ℝ) - (m:ℝ)*Qad j i/2| ≤ 4:=by
  obtain ⟨d,rfl⟩:=Z106 (Nat.ne_of_gt hr)
  have hp:=(QdO off).comp hj
  induction i using Z38 with
  | zero =>
    rw [QeD,Qkp]
    simp only [Z67,periodSlot,Z23,Z35,Z52,
      Z25]
    have offset_bound:=abs_le.mp (hoff (j 0))
    apply abs_le.mpr
    constructor <;> linarith
  | succ i =>
    induction i using Z60 with
    | last =>
      rw [Fin.succ_last,QeC,Qkn]
      have hcut:(j (Z22 d)).val+1 ≤ u:=Z68 (j _).isLt
      have hslot:((periodSlot off ∘ j) (Z22 d)).val+1 ≤ u*m :=
        Z68 (((periodSlot off ∘ j) (Z22 d))).isLt
      simp only [Z23,Z35,Z52]
      rw [Z47 hslot,Z47 hcut]
      simp only [Z67,periodSlot,Z23,Z35,Z25]
      have h:=abs_le.mp (hoff (j (Z22 d)))
      apply abs_le.mpr
      constructor <;> linarith
    | cast i =>
      rw [QdZ,Qgr]
      have hcut:(j i.castSucc).val+1 ≤ (j i.succ).val:=hj (Fin.castSucc_lt_succ (i:=i))
      have hslot:((periodSlot off ∘ j) i.castSucc).val+1 ≤
          ((periodSlot off ∘ j) i.succ).val:=hp (Fin.castSucc_lt_succ (i:=i))
      simp only [Z23,Z35,Z52]
      rw [Z47 hslot,Z47 hcut]
      simp only [Z67,periodSlot,Z23,Z35,Z25]
      have h:=abs_le.mp (hdiff (j i.succ) (j i.castSucc))
      apply abs_le.mpr
      constructor <;> linarith
end TraceReconstruction
namespace TraceReconstruction
abbrev Qab (n r:ℕ):={v:Fin r → Fin n // StrictMono v}
noncomputable instance Qrn (n r:ℕ):Fintype (Qab n r) :=
  Fintype.ofFinite _
theorem QiW {n r:ℕ} (v:Qab n r) (i:Fin (r+1)) :
    tupleGap v.val i ≤ n-r:=by
  have ht:=QcA v.val v.property
  have hle:tupleGap v.val i ≤ ∑ j,tupleGap v.val j :=
    Z82 (fun _ _ => Nat.zero_le _) (Z21 i)
  omega
def QbS {n r:ℕ} (σ:Equiv.Perm (Fin (r+1))) (v:Qab n r) :
    Fin (r+1) → Fin (n-r+1) :=
  fun i => ⟨tupleGap v.val (σ i),Z72 (QiW v (σ i))⟩
theorem Qis {n r:ℕ} (σ:Equiv.Perm (Fin (r+1)))
    (v:Qab n r):∑ i,(QbS σ v i).val = n-r:=by
  change (∑ i,tupleGap v.val (σ i)) = _
  rw [Equiv.sum_comp σ]
  have ht:=QcA v.val v.property
  omega
theorem QfD {n r:ℕ} (σ:Equiv.Perm (Fin (r+1))) :
    Z28 (QbS (n:=n) σ):=by
  intro v w h
  apply Subtype.ext
  funext i
  apply Z34
  have he:tupleGap v.val = tupleGap w.val:=by
    funext j
    have hh:=congrArg Fin.val (congrFun h (σ.symm j))
    simpa only [QbS,Z103] using hh
  have hv:=QcQ v.val v.property i
  have hw:=QcQ w.val w.property i
  rw [he] at hv
  omega
theorem QcP {α β:Type*} [Fintype α] [Fintype β]
    (profile:α → β) (hinj:Z28 profile)
    (P:β → Prop) [DecidablePred P] (hp:∀ a,P (profile a))
    (f:β → ℝ) (hf:∀ b,0 ≤ f b) :
    (∑ a,f (profile a)) ≤ ∑ b,if P b then f b else 0:=by
  classical
  let S:=Finset.univ.image profile
  have hs:∀ b ∈ S,P b:=by
    intro b hb
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hb
    exact hp a
  calc
    _ = ∑ b ∈ S,f b:=by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => hinj h)
    _ = ∑ b ∈ S,if P b then f b else 0:=by
      apply Z2 rfl
      intro b hb
      rw [if_pos (hs b hb)]
    _ ≤ _:=Z40 (Z56 _) (by
      intro b _ _
      split_ifs
      · exact hf b
      · rfl)
theorem Qqo {n l r:ℕ} (hl:l ≤ n)
    (p q:Fin r → Fin n) (hp:StrictMono p) (hq:StrictMono q)
    (θ:ℝ) (hθ:θ ∈ Z4 0 1) (e:Fin (r+1))
    (M:ℝ) (hM:0 ≤ M)
    (hbound:∀ k:Fin (l-r+1),
      Qaa (tupleGap p e) θ k * Qaa (tupleGap q e) θ k ≤ M) :
    (∑ v:Qab l r,
      Qaw hl p v.val * Qaw hl q v.val) ≤
      (θ^r / Qaa n θ l)^2 * M *
        ∏ i:Fin r,∑ k:Fin (l-r+1),
          Qaa (tupleGap p (Z18 0 e i.succ)) θ k *
          Qaa (tupleGap q (Z18 0 e i.succ)) θ k:=by
  classical
  let σ:Equiv.Perm (Fin (r+1)):=Z18 0 e
  let f:Fin (r+1) → Fin (l-r+1) → ℝ:=fun i k => Qaa (tupleGap p (σ i)) θ k
  let g:Fin (r+1) → Fin (l-r+1) → ℝ:=fun i k => Qaa (tupleGap q (σ i)) θ k
  have hf:∀ i k,0 ≤ f i k:=by
    intro i k
    dsimp [f,Qaa]
    positivity [hθ.1.le,sub_nonneg.mpr hθ.2.le]
  have hg:∀ i k,0 ≤ g i k:=by
    intro i k
    dsimp [g,Qaa]
    positivity [hθ.1.le,sub_nonneg.mpr hθ.2.le]
  let F (z:Fin (r+1) → Fin (l-r+1)):=(∏ i,f i (z i)) * (∏ i,g i (z i))
  have hF:∀ z,0 ≤ F z:=by
    intro z
    exact mul_nonneg (Z37 fun i _ => hf i _) (Z37 fun i _ => hg i _)
  have hpoint (v:Qab l r) :
      Qaw hl p v.val * Qaw hl q v.val =
        (θ^r / Qaa n θ l)^2 * F (QbS σ v):=by
    rw [Qex hl p hp v.val v.property θ hθ,
      Qex hl q hq v.val v.property θ hθ]
    dsimp only [F,f,g,QbS]
    rw [Equiv.prod_comp σ (fun j => Qaa (tupleGap p j) θ (tupleGap v.val j)),
      Equiv.prod_comp σ (fun j => Qaa (tupleGap q j) θ (tupleGap v.val j))]
    ring
  simp_rw [hpoint]
  rw [← Z3]
  calc
    _ ≤ (θ^r / Qaa n θ l)^2 *
        ∑ z:Fin (r+1) → Fin (l-r+1),if ∑ i,(z i).val = l-r then F z else 0:=by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact QcP (QbS σ) (QfD σ)
        (fun z => ∑ i,(z i).val = l-r) (Qis σ) F hF
    _ ≤ (θ^r / Qaa n θ l)^2 * (M * ∏ i:Fin r,∑ k,f i.succ k * g i.succ k):=by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact QkJ r (l-r) f g hf hg M hM (by
        intro k
        simpa only [f,g,σ,Equiv.swap_apply_left] using hbound k)
    _ = _:=by dsimp [f,g,σ]; ring
end TraceReconstruction
namespace TraceReconstruction
theorem QlC (S:Finset ℤ) (a:ℤ) {ρ:ℝ}
    (hρ:ρ∈Set.Ico 0 1) :
    (∑ z ∈ S,ρ^(z-a).natAbs) ≤ 2/(1-ρ):=by
  have hs:Summable (fun n:ℕ => ρ^n):=summable_geometric_of_lt_one hρ.1 hρ.2
  have hnat:Summable (fun n:ℕ => ρ^((n:ℤ).natAbs)):=by simpa using hs
  have hneg:Summable (fun n:ℕ => ρ^((-(n:ℤ)).natAbs)):=by simpa using hs
  have hz:Summable (fun z:ℤ => ρ^z.natAbs):=hnat.of_nat_of_neg hneg
  have ht:(∑' z:ℤ,ρ^z.natAbs)=2/(1-ρ)-1:=by
    rw [Summable.tsum_of_nat_of_neg (f:=fun z:ℤ => ρ^z.natAbs) hnat hneg]
    simp only [Int.natAbs_natCast,Int.natAbs_neg,Int.natAbs_zero,pow_zero]
    rw [tsum_geometric_of_lt_one hρ.1 hρ.2]
    ring
  have hshift:Summable (fun z:ℤ => ρ^(z-a).natAbs) :=
    hz.comp_injective (sub_left_injective)
  have hts:(∑' z:ℤ,ρ^(z-a).natAbs)=(∑' z:ℤ,ρ^z.natAbs) :=
    (Equiv.subRight a).tsum_eq (fun z:ℤ => ρ^z.natAbs)
  have hbound:=hshift.sum_le_tsum S (fun z _ => pow_nonneg hρ.1 _)
  rw [hts,ht] at hbound
  linarith
end TraceReconstruction
namespace TraceReconstruction
theorem QlA (N:ℕ) (a:ℤ) {ρ:ℝ} (hρ:ρ∈Set.Ico 0 1) :
    (∑ z:Fin N,ρ^((z.val:ℤ)-a).natAbs) ≤ 2/(1-ρ):=by
  let e:ℕ ↪ ℤ:=⟨Int.ofNat,Nat.cast_injective⟩
  have h:=QlC ((Z5 N).map e) a hρ
  rw [Finset.sum_map] at h
  rw [Z76 (fun z:ℕ => ρ^((z:ℤ)-a).natAbs) N]
  exact h
theorem Qkt {h:ℝ} (hh:0<h) (h1:h≤1) (M:ℕ) :
    (∑ k:Fin (M+1),(Z0 (k.val:ℝ))⁻¹ * Z1 (-h*(k.val:ℝ))) ≤
      6/Z0 h:=by
  rw [Z64]
  simp only [Fin.val_zero,Nat.cast_zero,Real.sqrt_zero,inv_zero,zero_mul,zero_add]
  have hc:=Qks hh h1 M
  rw [← Z76 (fun k:ℕ =>
    (Z0 (k+1:ℝ))⁻¹ * Z1 (-h*(k+1:ℝ))) M] at hc
  simpa only [Fin.val_succ,Z23,Z25] using hc
theorem Qkr (r U:ℕ) {h:ℝ} (hh:0<h) (h1:h≤1) :
    (∑ γ:Fin (r+1) → Fin (U+1),
      if ∑ i,(γ i).val=U then ∏ i:Fin r,(Z0 ((γ i.succ).val:ℝ))⁻¹ else 0) ≤
      Z1 (h*U) * (6/Z0 h)^r:=by
  classical
  let f:Fin (r+1) → Fin (U+1) → ℝ:=Z38
    (fun k => Z1 (-h*(k.val:ℝ)))
    (fun _ k => (Z0 (k.val:ℝ))⁻¹ * Z1 (-h*(k.val:ℝ)))
  have hf:∀ i k,0≤f i k:=by
    intro i k
    refine Z38 ?_ (fun _ => ?_) i <;> dsimp [f] <;> positivity
  have hf0:∀ k,f 0 k≤1:=by
    intro k
    change Z1 (-h*(k.val:ℝ))≤1
    apply Real.exp_le_one_iff.mpr
    nlinarith [show (0:ℝ)≤k.val by positivity]
  have hid (γ:Fin (r+1) → Fin (U+1)) (hγ:∑ i,(γ i).val=U) :
      ∏ i:Fin r,(Z0 ((γ i.succ).val:ℝ))⁻¹ =
        Z1 (h*U) * ∏ i,f i (γ i):=by
    have hγr:((γ 0).val:ℝ) + ∑ i:Fin r,((γ i.succ).val:ℝ)=(U:ℝ):=by
      exact_mod_cast (show (γ 0).val+∑ i:Fin r,(γ i.succ).val=U by
        simpa only [Z64] using hγ)
    simp only [Z53,f,Fin.cases_zero,Fin.cases_succ,
      Z30,← Real.exp_sum]
    have he:Z1 (h*U) * Z1 (-h*((γ 0).val:ℝ)) *
        Z1 (∑ i:Fin r,-h*((γ i.succ).val:ℝ))=1:=by
      rw [← Z50,← Z50,← Z3]
      rw [show h*(U:ℝ)+ -h*((γ 0).val:ℝ)+ -h*∑ i:Fin r,((γ i.succ).val:ℝ)=0 by
        rw [← hγr]
        ring]
      exact Real.exp_zero
    calc
      _ = (Z1 (h*U) * Z1 (-h*((γ 0).val:ℝ)) *
        Z1 (∑ i:Fin r,-h*((γ i.succ).val:ℝ))) *
          (∏ i:Fin r,(Z0 ((γ i.succ).val:ℝ))⁻¹):=by rw [he,one_mul]
      _ = _:=by ring
  have hrew:(∑ γ:Fin (r+1) → Fin (U+1),
      if ∑ i,(γ i).val=U then ∏ i:Fin r,(Z0 ((γ i.succ).val:ℝ))⁻¹ else 0) =
      Z1 (h*U) * ∑ γ:Fin (r+1) → Fin (U+1),
        if ∑ i,(γ i).val=U then ∏ i,f i (γ i) else 0:=by
    rw [Z3]
    apply Z2 rfl
    intro γ _
    split_ifs with hγ
    · exact hid γ hγ
    · simp
  rw [hrew]
  apply mul_le_mul_of_nonneg_left _ (Z49 _)
  apply (Qee r U f hf 1 (by norm_num) hf0).trans
  simp only [one_mul]
  calc
    _ ≤ ∏ _i:Fin r,(6/Z0 h):=by
      apply Z45
      · intro i _; exact Z11 (fun k _ => hf i.succ k)
      · intro i _; exact Qkt hh h1 U
    _ = _:=by simp [div_pow]
theorem Qqz {α β:Type*} [Fintype β] (S:Finset α) (K:α → β → ℝ) :
    (∑ z,(∑ a ∈ S,K a z)^2) =
      ∑ a ∈ S,∑ b ∈ S,∑ z,K a z*K b z:=by
  simp_rw [pow_two,Z33,Z3]
  rw [Z17]
  apply Z2 rfl
  intro a _
  exact Z17
end TraceReconstruction
namespace TraceReconstruction
theorem Qgs (m U a b g k:ℕ) (hm:32 ≤ m) (hUm:U  ≤  2*m)
    (ha:1 ≤ a) (hb:1 ≤ b) (haU:a ≤ U) (hbU:b ≤ U)
    (hg:|(g:ℝ)-(m:ℝ)*a/2| ≤ 4) (hk:|(k:ℝ)-(m:ℝ)*b/2| ≤ 4) :
    (m:ℝ)*a/4  ≤  (g:ℝ)+1 ∧ 0<(g:ℝ)+k ∧
      ((a:ℝ)-b)^2/1024  ≤  ((g:ℝ)-k)^2/(16*((g:ℝ)+k)):=by
  have hmR:(32:ℝ) ≤ m:=by exact_mod_cast hm
  have hUmR:(U:ℝ)  ≤  2*m:=by exact_mod_cast hUm
  have haR:(1:ℝ) ≤ a:=by exact_mod_cast ha
  have hbR:(1:ℝ) ≤ b:=by exact_mod_cast hb
  have haUR:(a:ℝ) ≤ U:=by exact_mod_cast haU
  have hbUR:(b:ℝ) ≤ U:=by exact_mod_cast hbU
  have hga:=abs_le.mp hg
  have hkb:=abs_le.mp hk
  have hma:(32:ℝ) ≤ (m:ℝ)*a:=by nlinarith
  have hmb:(32:ℝ) ≤ (m:ℝ)*b:=by nlinarith
  have hlo:(m:ℝ)*a/4 ≤ (g:ℝ)+1:=by nlinarith only [hga.1,hma]
  have hsum0:0<(g:ℝ)+k:=by nlinarith only [hga.1,hkb.1,hma,hmb]
  refine ⟨hlo,hsum0,?_⟩
  by_cases hab:a=b
  · simp only [hab,sub_self,zero_pow (by decide:2 ≠ 0),zero_div]
    exact div_nonneg (sq_nonneg _) (by positivity)
  have hd1:1 ≤ |(a:ℝ)-b|:=by
    rcases lt_or_gt_of_ne hab with hab | hab
    · rw [abs_of_neg (sub_neg.mpr (by exact_mod_cast hab:(a:ℝ) < b))]
      have hx:(a:ℝ)+1 ≤ b:=by exact_mod_cast hab
      linarith
    · rw [abs_of_pos (sub_pos.mpr (by exact_mod_cast hab:(b:ℝ) < a))]
      have hx:(b:ℝ)+1 ≤ a:=by exact_mod_cast hab
      linarith
  have herr:|((g:ℝ)-k)-(m:ℝ)/2*((a:ℝ)-b)| ≤ 8:=by
    calc
      _ = |((g:ℝ)-(m:ℝ)*a/2)-((k:ℝ)-(m:ℝ)*b/2)|:=by congr 1; ring
      _  ≤  |(g:ℝ)-(m:ℝ)*a/2|+|(k:ℝ)-(m:ℝ)*b/2|:=abs_sub _ _
      _  ≤  _:=by linarith
  have hd:(m:ℝ)/4*|(a:ℝ)-b|  ≤  |(g:ℝ)-k|:=by
    have ht:=abs_sub_abs_le_abs_sub ((m:ℝ)/2*((a:ℝ)-b)) ((g:ℝ)-k)
    rw [abs_sub_comm ((m:ℝ)/2*((a:ℝ)-b)) ((g:ℝ)-k)] at ht
    rw [abs_mul,abs_of_nonneg (by positivity:0 ≤ (m:ℝ)/2)] at ht
    have hmabs:(32:ℝ) ≤ (m:ℝ)*|(a:ℝ)-b|:=by nlinarith only [hmR,hd1]
    nlinarith only [ht,herr,hmabs]
  have hsq:(m:ℝ)^2*((a:ℝ)-b)^2/16 ≤ ((g:ℝ)-k)^2:=by
    have hx:=mul_self_le_mul_self (by positivity:0 ≤ (m:ℝ)/4*|(a:ℝ)-b|) hd
    nlinarith only [hx,sq_abs ((a:ℝ)-b),sq_abs ((g:ℝ)-k)]
  have hsum:(g:ℝ)+k  ≤  4*(m:ℝ)^2:=by
    have hu1:(1:ℝ) ≤ U:=by linarith
    have hmu:(32:ℝ) ≤ (m:ℝ)*U:=by nlinarith only [hmR,hu1]
    have hmaU:=mul_le_mul_of_nonneg_left haUR (show (0:ℝ) ≤ m by positivity)
    have hmbU:=mul_le_mul_of_nonneg_left hbUR (show (0:ℝ) ≤ m by positivity)
    have hUmM:=mul_le_mul_of_nonneg_left hUmR (show (0:ℝ) ≤ m by positivity)
    nlinarith only [hga.2,hkb.2,hmaU,hmbU,hmu,hUmM]
  apply (le_div_iff₀ (by positivity:0<16*((g:ℝ)+k))).mpr
  have hx:=mul_le_mul_of_nonneg_right hsum (sq_nonneg ((a:ℝ)-b))
  nlinarith only [hx,hsq]
theorem Qlh (a b:ℕ) {c:ℝ} (hc:0 ≤ c) :
    Z1 (-c * ((a:ℝ)-b)^2) ≤
      (Z1 (-c)) ^ ((a:ℤ)-b).natAbs:=by
  rw [← Z75]
  apply Real.exp_le_exp.mpr
  have hd:(((a:ℤ)-b).natAbs:ℝ) = |(a:ℝ)-b|:=by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,Int.cast_sub]
    simp only [Int.cast_natCast]
  have hsq:(((a:ℤ)-b).natAbs:ℝ) ≤ (((a:ℤ)-b).natAbs:ℝ)^2:=by
    exact_mod_cast (show ((a:ℤ)-b).natAbs ≤ ((a:ℤ)-b).natAbs^2 by
      simpa only [pow_two] using Nat.le_mul_self ((a:ℤ)-b).natAbs)
  rw [hd,sq_abs] at hsq
  have hmul:=mul_le_mul_of_nonneg_left hsq hc
  rw [hd]
  nlinarith only [hmul]
theorem Qkq (m U a b g k L:ℕ)
    (hm:32 ≤ m) (hUm:U ≤ 2*m)
    (ha:1 ≤ a) (hb:1 ≤ b) (haU:a ≤ U) (hbU:b ≤ U)
    (hg:|(g:ℝ)-(m:ℝ)*a/2| ≤ 4) (hk:|(k:ℝ)-(m:ℝ)*b/2| ≤ 4)
    {θ:ℝ} (hθ:θ ∈ Set.Ico (1/2:ℝ) 1) :
    (∑ z:Fin (L+1),Qaa g θ z * Qaa k θ z) ≤
      Z0 (8 / ((m:ℝ)*θ*(1-θ))) * (Z0 (a:ℝ))⁻¹ *
        (Z1 (-(1/1024:ℝ))) ^ ((a:ℤ)-b).natAbs:=by
  have geo:=Qgs m U a b g k hm hUm ha hb haU hbU hg hk
  have hsum:0 < g+k:=by exact_mod_cast geo.2.1
  have hθ0:0 < θ:=by linarith [hθ.1]
  have hθ1:0 < 1-θ:=sub_pos.mpr hθ.2
  have varpos:0 < θ*(1-θ):=mul_pos hθ0 hθ1
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have ha0:(0:ℝ) < a:=by exact_mod_cast ha
  have hpref:Z0 (2 / (((g:ℝ)+1)*θ*(1-θ))) ≤
      Z0 (8 / ((m:ℝ)*θ*(1-θ))) * (Z0 (a:ℝ))⁻¹:=by
    rw [← Real.sqrt_inv,← Real.sqrt_mul (by positivity:0 ≤ 8/((m:ℝ)*θ*(1-θ)))]
    apply Z24
    have hdg:0 < ((g:ℝ)+1)*θ*(1-θ):=by nlinarith
    have hdm:0 < (m:ℝ)*θ*(1-θ):=by nlinarith
    apply (div_le_iff₀ hdg).mpr
    have hdiv:0 < (m:ℝ)*θ*(1-θ)*(a:ℝ):=by positivity
    have heq:(8 / ((m:ℝ)*θ*(1-θ)) * (a:ℝ)⁻¹) * (((g:ℝ)+1)*θ*(1-θ)) =
        (8*((g:ℝ)+1)) / ((m:ℝ)*a):=by
      field_simp [ne_of_gt hθ0,ne_of_gt hθ1,ne_of_gt hm0,ne_of_gt ha0]
    rw [heq]
    apply (le_div_iff₀ (mul_pos hm0 ha0)).mpr
    linarith [geo.1]
  have hexp:Z1 (-((g:ℝ)-k)^2/(16*((g:ℝ)+k))) ≤
      (Z1 (-(1/1024:ℝ))) ^ ((a:ℤ)-b).natAbs:=by
    apply le_trans _ (Qlh a b (by norm_num:(0:ℝ)≤1/1024))
    apply Real.exp_le_exp.mpr
    convert neg_le_neg geo.2.2 using 2 <;> first | rfl | ring
  exact (QjV g k L hθ hsum).trans
    (mul_le_mul hpref hexp (Z49 _) (by positivity))
end TraceReconstruction
namespace TraceReconstruction
theorem QmS (a b:ℤ):(a-b).natAbs = (b-a).natAbs:=by
  rw [← Int.natAbs_neg (a-b),neg_sub]
theorem Qqp {n l r:ℕ} (hl:l  ≤  n)
    (p q:Fin r → Fin n) (hp:StrictMono p) (hq:StrictMono q)
    {θ:ℝ} (hθ:θ  ∈  Set.Ico (1/2:ℝ) 1)
    (hmean:(n:ℝ)*θ=l) (hv:1 ≤ (n:ℝ)*θ*(1-θ)) (e:Fin (r+1)) :
    (∑ v:Qab l r,
      Qaw hl p v.val * Qaw hl q v.val)  ≤ 
      (4608*n/((tupleGap p e:ℝ)+1))*
        ∏ i:Fin r,∑ k:Fin (l-r+1),
          Qaa (tupleGap p (Z18 0 e i.succ)) θ k *
          Qaa (tupleGap q (Z18 0 e i.succ)) θ k:=by
  have hθ0:0 < θ:=by linarith [hθ.1]
  have hqpos:0 < 1-θ:=sub_pos.mpr hθ.2
  have hc:(θ^r/Qaa n θ l)^2  ≤  144*((n:ℝ)*θ*(1-θ)):=by
    rw [div_eq_mul_inv,mul_pow]
    apply (mul_le_mul_of_nonneg_right
      (show (θ^r)^2  ≤  (1:ℝ) by
        exact pow_le_one₀ (pow_nonneg hθ0.le _) (pow_le_one₀ hθ0.le hθ.2.le))
      (sq_nonneg _)).trans
    simpa only [one_mul] using QeP n l ⟨hθ0,hθ.2⟩ hl hmean hv
  have hprod:0  ≤  ∏ i:Fin r,∑ k:Fin (l-r+1),
      Qaa (tupleGap p (Z18 0 e i.succ)) θ k *
      Qaa (tupleGap q (Z18 0 e i.succ)) θ k:=by
    apply Z37
    intro i _
    exact Z11 fun k _ => mul_nonneg
      (QaF _ _ ⟨hθ0.le,hθ.2.le⟩)
      (QaF _ _ ⟨hθ0.le,hθ.2.le⟩)
  apply (Qqo hl p q hp hq θ ⟨hθ0,hθ.2⟩ e
    (32/(((tupleGap p e:ℝ)+1)*θ*(1-θ))) (by positivity)
    (fun k => QjY _ _ k hθ)).trans
  calc
    _  ≤  (144*((n:ℝ)*θ*(1-θ)))*(32/(((tupleGap p e:ℝ)+1)*θ*(1-θ)))*_:=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hprod
    _ = _:=by
      have hq0:1-θ ≠ 0:=ne_of_gt (sub_pos.mpr hθ.2)
      field_simp
      ring
def Qbt {u r:ℕ} (hr:0 < r) (σ:Equiv.Perm (Fin (r+1)))
    (j:Qab u r):Fin (r+1) → Fin (2*u+1) :=
  fun i => ⟨Qad j.val (σ i),
    Z72 (QcZ hr j.val j.property (σ i))⟩
theorem QhZ {u r:ℕ} (hr:0 < r) (σ:Equiv.Perm (Fin (r+1)))
    (j:Qab u r):∑ i,(Qbt hr σ j i).val = 2*u:=by
  change (∑ i,Qad j.val (σ i)) = _
  rw [Equiv.sum_comp σ]
  exact Qda hr j.val j.property
theorem QhY {u r:ℕ} (hr:0 < r) (σ:Equiv.Perm (Fin (r+1))) :
    Z28 (Qbt (u:=u) hr σ):=by
  intro j k h
  apply Subtype.ext
  apply QeT j.property k.property
  funext i
  have he:=congrArg Fin.val (congrFun h (σ.symm i))
  simpa only [Qbt,Z103] using he
theorem Qor {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hm:32 ≤ m) (hum:u ≤ m) {θ:ℝ} (hθ:θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j k:Qab u r) (e:Fin (r+1))
    (he:2*u  ≤  (r+1)*Qad j.val e) :
    (∑ v:Qab l r,
      Qaw hl (periodSlot off ∘ j.val) v.val *
      Qaw hl (periodSlot off ∘ k.val) v.val)  ≤ 
      (9216*(r+1:ℕ):ℝ)* (Z0 (8/((m:ℝ)*θ*(1-θ))))^r *
        ∏ i:Fin r,(Z0 ((Qbt hr (Z18 0 e) j i.succ).val:ℝ))⁻¹ *
          (Z1 (-(1/1024:ℝ)))^(((Qbt hr (Z18 0 e) k i.succ).val:ℤ)-
            (Qbt hr (Z18 0 e) j i.succ).val).natAbs:=by
  classical
  have hθ0:0 < θ:=by linarith [hθ.1]
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hUm:2*u ≤ 2*m:=Nat.mul_le_mul_left 2 hum
  have hg (v:Qab u r) (i:Fin (r+1)) :=
    Qfx hr off hoff hdiff v.val v.property i
  have hgeo:=Qgs m (2*u) (Qad j.val e)
    (Qad k.val e) (tupleGap (periodSlot off ∘ j.val) e)
    (tupleGap (periodSlot off ∘ k.val) e) hm hUm
    (QcB j.val e) (QcB k.val e)
    (QcZ hr j.val j.property e) (QcZ hr k.val k.property e)
    (hg j e) (hg k e)
  have hlarge:(4608 * (u*m:ℕ):ℝ)/((tupleGap (periodSlot off ∘ j.val) e:ℝ)+1)  ≤ 
      9216*(r+1:ℕ):=by
    have heR:2*(u:ℝ)  ≤  (r+1:ℕ)* (Qad j.val e:ℝ):=by exact_mod_cast he
    apply (div_le_iff₀ (by positivity:0 < (tupleGap (periodSlot off ∘ j.val) e:ℝ)+1)).mpr
    have hx:=mul_le_mul_of_nonneg_right hgeo.1
      (show (0:ℝ) ≤ (r+1:ℕ) by positivity)
    have hy:=mul_le_mul_of_nonneg_left heR hm0.le
    simp only [Z35]
    nlinarith only [hx,hy]
  have hover (i:Fin r) :
      (∑ z:Fin (l-r+1),
        Qaa (tupleGap (periodSlot off ∘ j.val) (Z18 0 e i.succ)) θ z *
        Qaa (tupleGap (periodSlot off ∘ k.val) (Z18 0 e i.succ)) θ z)  ≤ 
      Z0 (8/((m:ℝ)*θ*(1-θ))) *
        ((Z0 ((Qbt hr (Z18 0 e) j i.succ).val:ℝ))⁻¹ *
          (Z1 (-(1/1024:ℝ)))^(((Qbt hr (Z18 0 e) k i.succ).val:ℤ)-
            (Qbt hr (Z18 0 e) j i.succ).val).natAbs):=by
    have ho:=Qkq m (2*u) _ _ _ _ (l-r) hm hUm
      (QcB j.val _) (QcB k.val _)
      (QcZ hr j.val j.property _) (QcZ hr k.val k.property _)
      (hg j (Z18 0 e i.succ)) (hg k (Z18 0 e i.succ)) hθ
    rw [QmS] at ho
    simpa only [Qbt,mul_assoc] using ho
  have hn (i:Fin r):0 ≤  ∑ z:Fin (l-r+1),
      Qaa (tupleGap (periodSlot off ∘ j.val) (Z18 0 e i.succ)) θ z *
      Qaa (tupleGap (periodSlot off ∘ k.val) (Z18 0 e i.succ)) θ z:=by
    exact Z11 fun z _ => mul_nonneg
      (QaF _ _ ⟨hθ0.le,hθ.2.le⟩) (QaF _ _ ⟨hθ0.le,hθ.2.le⟩)
  apply (Qqp hl _ _
    ((QdO off).comp j.property) ((QdO off).comp k.property)
    hθ hmean hv e).trans
  calc
    _  ≤  (9216*(r+1:ℕ):ℝ)*
        ∏ i:Fin r,(Z0 (8/((m:ℝ)*θ*(1-θ))) *
        ((Z0 ((Qbt hr (Z18 0 e) j i.succ).val:ℝ))⁻¹ *
          (Z1 (-(1/1024:ℝ)))^(((Qbt hr (Z18 0 e) k i.succ).val:ℤ)-
            (Qbt hr (Z18 0 e) j i.succ).val).natAbs)):=by
      apply mul_le_mul hlarge (Z45 (fun i _ => hn i) (fun i _ => hover i))
        (Z37 (fun i _ => hn i)) (by positivity)
    _ = _:=by rw [Z30]; simp only [Z78,Z48,Z26]; ring
end TraceReconstruction
namespace TraceReconstruction
theorem Qkw {α:Type*} [Fintype α] (r U:ℕ)
    (profile:α → Fin (r+1) → Fin (U+1)) (hinj:Z28 profile)
    (htotal:∀ a,∑ i,(profile a i).val=U)
    (γ:Fin (r+1) → Fin (U+1)) {ρ:ℝ} (hρ:ρ∈Set.Ico 0 1) :
    (∑ a,∏ i:Fin r,ρ^(((profile a i.succ).val:ℤ)-(γ i.succ).val).natAbs) ≤
      (2/(1-ρ))^r:=by
  classical
  let f:Fin (r+1) → Fin (U+1) → ℝ:=Z38 (fun _ => 1)
    (fun i k => ρ^((k.val:ℤ)-(γ i.succ).val).natAbs)
  have hf:∀ i k,0≤f i k:=by
    intro i k
    refine Z38 ?_ (fun _ => ?_) i
    · norm_num [f]
    · exact pow_nonneg hρ.1 _
  have hid (δ:Fin (r+1) → Fin (U+1)) :
      (∏ i:Fin r,ρ^(((δ i.succ).val:ℤ)-(γ i.succ).val).natAbs) = ∏ i,f i (δ i):=by
    simp only [Z53,f,Fin.cases_zero,Fin.cases_succ,one_mul]
  simp_rw [hid]
  apply (QcP profile hinj (fun δ => ∑ i,(δ i).val=U)
    htotal (fun δ => ∏ i,f i (δ i)) (fun δ => Z37 (fun i _ => hf i _))).trans
  apply (Qee r U f hf 1 (by norm_num) (by intro k; rfl)).trans
  simp only [one_mul]
  calc
    _ ≤ ∏ _i:Fin r,(2/(1-ρ)):=by
      apply Z45
      · exact fun i _ => Z11 (fun k _ => hf i.succ k)
      · exact fun i _ => QlA (U+1) ((γ i.succ).val:ℤ) hρ
    _ = _:=by simp [div_pow]
theorem Qkx {α:Type*} [Fintype α] (r U:ℕ)
    (profile:α → Fin (r+1) → Fin (U+1)) (hinj:Z28 profile)
    (htotal:∀ a,∑ i,(profile a i).val=U)
    {h:ℝ} (hh:0<h) (h1:h≤1) :
    (∑ a,∏ i:Fin r,(Z0 ((profile a i.succ).val:ℝ))⁻¹) ≤
      Z1 (h*U)*(6/Z0 h)^r:=by
  classical
  apply le_trans _ (Qkr r U hh h1)
  exact QcP profile hinj (fun δ => ∑ i,(δ i).val=U)
    htotal (fun δ => ∏ i:Fin r,(Z0 ((δ i.succ).val:ℝ))⁻¹) (fun δ => by positivity)
theorem Qkv {α β:Type*} [Fintype α] [Fintype β]
    (r U:ℕ) (p:α → Fin (r+1) → Fin (U+1)) (q:β → Fin (r+1) → Fin (U+1))
    (hp:Z28 p) (hq:Z28 q)
    (hpt:∀ a,∑ i,(p a i).val=U) (hqt:∀ b,∑ i,(q b i).val=U)
    (K:α → β → ℝ) {M ρ h:ℝ}
    (hM:0≤M) (hρ:ρ∈Set.Ico 0 1) (hh:0<h) (h1:h≤1)
    (hcross:∀ a b,K a b ≤ M * ∏ i:Fin r,
      (Z0 ((p a i.succ).val:ℝ))⁻¹ *
        ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs) :
    (∑ a,∑ b,K a b) ≤ M*(2/(1-ρ))^r * Z1 (h*U)*(6/Z0 h)^r:=by
  classical
  let A (a:α):=∏ i:Fin r,(Z0 ((p a i.succ).val:ℝ))⁻¹
  have hA (a):0≤A a:=by dsimp [A]; positivity
  have hinner (a):=Qkw r U q hq hqt (p a) hρ
  have houter:=Qkx r U p hp hpt hh h1
  calc
    _ ≤ ∑ a,∑ b,M * ∏ i:Fin r,
        (Z0 ((p a i.succ).val:ℝ))⁻¹ *
          ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs :=
      Z7 (fun a _ => Z7 (fun b _ => hcross a b))
    _ = ∑ a,M*A a * ∑ b,∏ i:Fin r,ρ^(((q b i.succ).val:ℤ)-(p a i.succ).val).natAbs:=by
      simp only [Z30,A,Z3,mul_assoc]
    _ ≤ ∑ a,M*A a*(2/(1-ρ))^r :=
      Z7 (fun a _ => mul_le_mul_of_nonneg_left (hinner a) (mul_nonneg hM (hA a)))
    _ = M*(2/(1-ρ))^r * ∑ a,A a:=by
      rw [Z3]
      apply Z2 rfl
      intros
      ring
    _ ≤ M*(2/(1-ρ))^r * (Z1 (h*U)*(6/Z0 h)^r):=by
      apply mul_le_mul_of_nonneg_left houter
      exact mul_nonneg hM (pow_nonneg (div_nonneg (by norm_num) (by linarith [hρ.2])) _)
    _ = _:=by ring
end TraceReconstruction
namespace TraceReconstruction
def QcU (u r:ℕ) (e:Fin (r+1)) :=
  {j:Qab u r // 2*u ≤ (r+1)*Qad j.val e}
noncomputable instance Qro (u r:ℕ) (e:Fin (r+1)) :
    Fintype (QcU u r e):=by
  unfold QcU
  exact Fintype.ofFinite _
theorem QgI {u r:ℕ} (hr:0 < r) (j:Qab u r) :
    ∃ e:Fin (r+1),2*u ≤ (r+1)*Qad j.val e:=by
  obtain ⟨e,_,he⟩:=Finset.exists_max_image Z16 (Qad j.val)
    Finset.univ_nonempty
  refine ⟨e,?_⟩
  calc
    _ = ∑ i,Qad j.val i:=(Qda hr j.val j.property).symm
    _ ≤ ∑ _i:Fin (r+1),Qad j.val e:=Z7 (fun i hi => he i hi)
    _ = _:=by simp
theorem Qow {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hm:32 ≤ m) (hum:u ≤ m) {θ h:ℝ} (hθ:θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh:0 < h) (h1:h ≤ 1)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v:Qab l r,
      (∑ j:Qab u r,Qaw hl (periodSlot off ∘ j.val) v.val)^2) ≤
      9216*(r+1:ℕ)^2 * (Z0 (8/((m:ℝ)*θ*(1-θ))))^r *
        (2/(1-Z1 (-(1/1024:ℝ))))^r * Z1 (h*(2*u:ℕ)) * (6/Z0 h)^r:=by
  classical
  let K (j:Qab u r) (v:Qab l r) :=
    Qaw hl (periodSlot off ∘ j.val) v.val
  let C (j k:Qab u r):=∑ v:Qab l r,K j v*K k v
  have hC (j k):0 ≤ C j k:=by
    exact Z11 (fun v _ => mul_nonneg
      (Qdw hl _ _) (Qdw hl _ _))
  have hρ:Z1 (-(1/1024:ℝ)) ∈ Set.Ico 0 1:=by
    refine ⟨(Z74 _).le,?_⟩
    rw [Real.exp_lt_one_iff]
    norm_num
  have hschur (e:Fin (r+1)) :
      (∑ j:QcU u r e,∑ k:Qab u r,C j.val k) ≤
        ((9216*(r+1:ℕ):ℝ)*(Z0 (8/((m:ℝ)*θ*(1-θ))))^r) *
          (2/(1-Z1 (-(1/1024:ℝ))))^r * Z1 (h*(2*u:ℕ)) * (6/Z0 h)^r:=by
    apply Qkv r (2*u)
      (fun j:QcU u r e => Qbt hr (Z18 0 e) j.val)
      (Qbt hr (Z18 0 e))
      ((QhY hr (Z18 0 e)).comp Subtype.val_injective)
      (QhY hr (Z18 0 e))
      (fun j => QhZ hr _ j.val) (QhZ hr _)
      (fun j k => C j.val k) (by positivity) hρ hh h1
    intro j k
    exact Qor hl hr hm hum hθ hmean hv off hoff hdiff j.val k e j.property
  have hcover (j:Qab u r) :
      (∑ k:Qab u r,C j k) ≤ ∑ e:Fin (r+1),
        if 2*u ≤ (r+1)*Qad j.val e then ∑ k:Qab u r,C j k else 0:=by
    obtain ⟨e,he⟩:=QgI hr j
    have hn:∀ e':Fin (r+1),0 ≤
        if 2*u ≤ (r+1)*Qad j.val e' then ∑ k:Qab u r,C j k else 0:=by
      intro e'
      split_ifs
      · exact Z11 (fun k _ => hC j k)
      · rfl
    simpa only [if_pos he] using Z82 (fun e' _ => hn e') (Z21 e)
  have heq (e:Fin (r+1)) :
      (∑ j:Qab u r,
        if 2*u ≤ (r+1)*Qad j.val e then ∑ k:Qab u r,C j k else 0) =
      ∑ j:QcU u r e,∑ k:Qab u r,C j.val k:=by
    rw [← Z27]
    exact Finset.sum_subtype _ (by intro j; simp) _
  calc
    _ = ∑ j:Qab u r,∑ k:Qab u r,C j k:=by
      exact Qqz Z16 K
    _ ≤ ∑ j:Qab u r,∑ e:Fin (r+1),
        if 2*u ≤ (r+1)*Qad j.val e then ∑ k:Qab u r,C j k else 0 :=
      Z7 (fun j _ => hcover j)
    _ = ∑ e:Fin (r+1),∑ j:QcU u r e,
        ∑ k:Qab u r,C j.val k:=by
      rw [Z17]
      exact Z2 rfl (fun e _ => heq e)
    _ ≤ ∑ _e:Fin (r+1),
        ((9216*(r+1:ℕ):ℝ)*(Z0 (8/((m:ℝ)*θ*(1-θ))))^r) *
          (2/(1-Z1 (-(1/1024:ℝ))))^r * Z1 (h*(2*u:ℕ)) * (6/Z0 h)^r :=
      Z7 (fun e _ => hschur e)
    _ = _:=by simp only [Z59,Z48,Z26,nsmul_eq_mul]; ring
end TraceReconstruction
namespace TraceReconstruction
theorem Qpl {r:ℕ} (hr:0 < r) :
    (9216:ℝ)*(r+1:ℕ)^2 ≤ (36864:ℝ)^r:=by
  have h1:(9216:ℝ) ≤ (9216:ℝ)^r:=le_self_pow₀ (by norm_num) (Nat.ne_of_gt hr)
  have h2:((r+1:ℕ):ℝ) ≤ (2:ℝ)^r:=by exact_mod_cast QnF r
  have h3:=pow_le_pow_left₀ (by positivity:(0:ℝ) ≤ (r+1:ℕ)) h2 2
  have h4:((2:ℝ)^r)^2 = (4:ℝ)^r:=by
    rw [← pow_mul,Nat.mul_comm r 2,pow_mul]
    norm_num
  calc
    _ ≤ (9216:ℝ)^r*((2:ℝ)^r)^2:=mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = _:=by rw [h4,← mul_pow]; norm_num
noncomputable def Qau:ℝ :=
  884736 * (2/(1-Z1 (-(1/1024:ℝ)))) * Z1 1
theorem Qcd:0 < Qau:=by
  have hρ:Z1 (-(1/1024:ℝ)) < 1:=by rw [Real.exp_lt_one_iff]; norm_num
  unfold Qau
  positivity
theorem Qou {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hru:r ≤ u) (hm:32 ≤ m) (hum:u ≤ m) {θ:ℝ} (hθ:θ ∈ Set.Ico (1/2:ℝ) 1)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v:Qab l r,
      (∑ j:Qab u r,Qaw hl (periodSlot off ∘ j.val) v.val)^2) ≤
      (Qau * Z0 ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))))^r:=by
  have hr0:(0:ℝ) < r:=by exact_mod_cast hr
  have hu0:(0:ℝ) < u:=by exact_mod_cast (show 0 < u by omega)
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hθ0:0 < θ:=by linarith [hθ.1]
  have hq0:0 < 1-θ:=sub_pos.mpr hθ.2
  let h:ℝ:=(r:ℝ)/(2*u)
  have hh:0 < h:=div_pos hr0 (by positivity)
  have h1:h ≤ 1:=by
    apply (div_le_one (by positivity:(0:ℝ) < 2*u)).mpr
    have hruR:(r:ℝ) ≤ u:=by exact_mod_cast hru
    linarith
  have hx:h*(2*u:ℕ) = r:=by
    dsimp [h]
    simp only [Z35,Z52]
    field_simp
  have he:Z1 (h*(2*u:ℕ)) = (Z1 1)^r:=by
    rw [hx,← Z75]
    simp
  have hρ:0 ≤ 2/(1-Z1 (-(1/1024:ℝ))):=by
    have hn:Z1 (-(1/1024:ℝ)) < 1:=by rw [Real.exp_lt_one_iff]; norm_num
    positivity
  have hp:0 ≤ (u:ℝ)/((m:ℝ)*r*θ*(1-θ)):=by positivity
  have hs:Z0 (8/((m:ℝ)*θ*(1-θ))) * (6/Z0 h) ≤
      24 * Z0 ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))):=by
    have hsq:(Z0 (8/((m:ℝ)*θ*(1-θ))) * (6/Z0 h))^2 =
        576 * ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))):=by
      rw [mul_pow,div_pow,Z13 (by positivity:(0:ℝ) ≤ 8/((m:ℝ)*θ*(1-θ))),
        Z13 hh.le]
      dsimp [h]
      field_simp
      ring
    nlinarith [Z13 hp,Z36 ((u:ℝ)/((m:ℝ)*r*θ*(1-θ)))]
  apply (Qow hl hr hm hum hθ hmean hv hh h1 off hoff hdiff).trans
  rw [he]
  calc
    _ ≤ (36864:ℝ)^r * (Z0 (8/((m:ℝ)*θ*(1-θ))))^r *
        (2/(1-Z1 (-(1/1024:ℝ))))^r * (Z1 1)^r * (6/Z0 h)^r:=by
      gcongr
      exact Qpl hr
    _ = ((36864:ℝ)*(2/(1-Z1 (-(1/1024:ℝ))))*Z1 1 *
        (Z0 (8/((m:ℝ)*θ*(1-θ)))*(6/Z0 h)))^r:=by
      simp only [mul_pow]
      ring
    _ ≤ ((36864:ℝ)*(2/(1-Z1 (-(1/1024:ℝ))))*Z1 1 *
        (24 * Z0 ((u:ℝ)/((m:ℝ)*r*θ*(1-θ)))))^r:=by
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _:=by congr 1; unfold Qau; ring
end TraceReconstruction
namespace TraceReconstruction
theorem Qov {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hru:r ≤ u) (hm:32 ≤ m) (hum:u ≤ m) {δ θ:ℝ}
    (hδ:δ ∈ Z12 0 (1/2:ℝ))
    (hθ:θ ∈ Z6 (1-δ^2) (1-δ^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ v:Qab l r,
      (∑ j:Qab u r,Qaw hl (periodSlot off ∘ j.val) v.val)^2) ≤
      ((3*Qau/δ) * Z0 ((u:ℝ)/((m:ℝ)*r)))^r:=by
  have hd0:0 < δ:=hδ.1
  have hd2:0 < δ^2:=sq_pos_of_pos hδ.1
  have hd2b:δ^2 ≤ 1/4:=by nlinarith [hδ.1,hδ.2]
  have ht:θ ∈ Set.Ico (1/2:ℝ) 1:=by
    constructor <;> nlinarith [hθ.1,hθ.2]
  have ht0:0 < θ:=by linarith [ht.1]
  have hq0:0 < 1-θ:=sub_pos.mpr ht.2
  have hr0:(0:ℝ) < r:=by exact_mod_cast hr
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hu0:(0:ℝ) ≤ u:=Z19 u
  have hvar:δ^2/8 ≤ θ*(1-θ):=by
    have hq:δ^2/4 ≤ 1-θ:=by linarith [hθ.2]
    nlinarith [mul_le_mul ht.1 hq (by positivity) ht0.le]
  have hdiv:(u:ℝ)/((m:ℝ)*r*θ*(1-θ)) ≤
      (3/δ)^2*((u:ℝ)/((m:ℝ)*r)):=by
    have hden:(0:ℝ) < (m:ℝ)*r*θ*(1-θ):=by positivity
    apply (div_le_iff₀ hden).mpr
    have he:(3/δ)^2 * ((u:ℝ)/((m:ℝ)*r)) * ((m:ℝ)*r*θ*(1-θ)) =
        ((u:ℝ)*9*θ*(1-θ))/δ^2:=by field_simp; ring
    rw [he]
    apply (le_div_iff₀ hd2).mpr
    nlinarith [mul_le_mul_of_nonneg_left hvar (by positivity:(0:ℝ) ≤ 9*(u:ℝ))]
  have hs:Z0 ((u:ℝ)/((m:ℝ)*r*θ*(1-θ))) ≤
      (3/δ)*Z0 ((u:ℝ)/((m:ℝ)*r)):=by
    calc
      _ ≤ Z0 ((3/δ)^2*((u:ℝ)/((m:ℝ)*r))):=Z24 hdiv
      _ = _:=by
        rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  apply (Qou hl hr hru hm hum ht hmean hv off hoff hdiff).trans
  apply pow_le_pow_left₀ (by positivity [Qcd])
  calc
    _ ≤ Qau*((3/δ)*Z0 ((u:ℝ)/((m:ℝ)*r))) :=
      mul_le_mul_of_nonneg_left hs Qcd.le
    _ = _:=by ring
end TraceReconstruction
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
namespace TraceReconstruction
def Qbv (g s:ℕ) (p:ℝ):IntSeries :=
  (Qaf 1 p - 1)^s * Qaf g p
theorem Qjx (p:ℝ) :
    Qaf 1 p - 1 = (-p) • Qas:=by
  unfold Qaf Qas
  rw [pow_one,smul_sub,AddMonoidAlgebra.smul_single,AddMonoidAlgebra.smul_single]
  simp only [smul_eq_mul,mul_one]
  have h1:(1:IntSeries) = Z29 0 1:=rfl
  rw [h1]
  simp only [AddMonoidAlgebra.single_sub]
  ext z
  simp only [AddMonoidAlgebra.coeff_sub,AddMonoidAlgebra.coeff_add,
    Finsupp.sub_apply,Finsupp.add_apply,Z41,Z42]
  split_ifs <;> ring
theorem QjF (g s:ℕ) (p:ℝ) :
    Qbv g s p =
      (-p)^s • (Qas^s * Qaf g p):=by
  unfold Qbv
  rw [Qjx,smul_pow,smul_mul_assoc]
theorem QpB (c:ℝ) (f:IntSeries) :
    seriesL2Sq (c • f) = c^2 * seriesL2Sq f:=by
  unfold seriesL2Sq
  simp only [Z88,Z89,smul_eq_mul,mul_pow]
  exact tsum_mul_left
theorem QjE (g s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    (∀ z:ℤ,|(Qbv g s p).coeff z| ≤
      (2*Qaz (g/(s+1)) p)^s * Qaz (g/(s+1)) p) ∧
    (seriesL2Sq (Qbv g s p) ≤
      ((2*Qaz (g/(s+1)) p)^s)^2 * Qaz (g/(s+1)) p):=by
  have hpow:|(-p)^s| ≤ 1:=by
    rw [abs_pow,abs_neg,abs_of_pos hp.1]
    exact pow_le_one₀ hp.1.le hp.2.le
  have hs:=QjC g s hp
  rw [QjF]
  constructor
  · intro z
    simp only [Z88,Z89,smul_eq_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)).trans (by simpa using hs.1 z)
  · rw [QpB]
    have h:((-p)^s) ^ 2 ≤ 1:=by nlinarith [sq_abs ((-p)^s),abs_nonneg ((-p)^s)]
    exact (mul_le_mul_of_nonneg_right h (Qcn _)).trans (by simpa using hs.2)
def QaJ (s:ℕ) (p:ℝ):ℝ :=
  2 * Z0 (((s:ℝ)+1)/(p*(1-p)))
theorem QcI (s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    0 < QaJ s p:=by
  unfold QaJ
  positivity [hp.1,sub_pos.mpr hp.2]
theorem Qjs (g s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    2*Qaz (g/(s+1)) p ≤
      QaJ s p / Z0 ((g:ℝ)+1):=by
  calc
    _ ≤ 2*Z0 (((s:ℝ)+1)/(((g:ℝ)+1)*p*(1-p))) :=
      mul_le_mul_of_nonneg_left (Qjt g s hp) (by norm_num)
    _ = _:=by
      unfold QaJ
      rw [show ((s:ℝ)+1)/(((g:ℝ)+1)*p*(1-p)) =
        (((s:ℝ)+1)/(p*(1-p)))/((g:ℝ)+1) by field_simp]
      rw [Real.sqrt_div (by positivity [hp.1,sub_pos.mpr hp.2])]
      ring
theorem QjG (g s:ℕ) {p:ℝ} (hp:p ∈ Z4 0 1) :
    (∀ z:ℤ,(Qbv g s p).coeff z ^ 2 ≤
      (QaJ s p)^(2*s+2) / ((g:ℝ)+1)^(s+1)) ∧
    (seriesL2Sq (Qbv g s p) ≤
      (QaJ s p)^(2*s+1) /
        (((g:ℝ)+1)^s * Z0 ((g:ℝ)+1))):=by
  have hb:=QjE g s hp
  have hc:=Qjs g s hp
  have hB:0 ≤ Qaz (g/(s+1)) p:=Z36 _
  have hC:0 < QaJ s p:=QcI s hp
  have hg:0 < Z0 ((g:ℝ)+1):=Real.sqrt_pos.mpr (by positivity)
  have hB':Qaz (g/(s+1)) p ≤
      QaJ s p / Z0 ((g:ℝ)+1):=by linarith
  have hs:=pow_le_pow_left₀ (by positivity:0 ≤ 2*Qaz (g/(s+1)) p) hc s
  constructor
  · intro z
    have h:=(hb.1 z).trans (mul_le_mul hs hB' hB (by positivity))
    rw [← pow_succ] at h
    have hsq:=pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at hsq
    refine hsq.trans_eq ?_
    rw [← pow_mul,div_pow]
    have he:(s+1)*2=2*s+2:=by omega
    rw [he]
    congr 1
    rw [show 2*s+2=2*(s+1) by omega,pow_mul,Z13 (by positivity)]
  · have hsq:=pow_le_pow_left₀ (by positivity :
        0 ≤ (2*Qaz (g/(s+1)) p)^s) hs 2
    refine hb.2.trans ((mul_le_mul hsq hB' hB (by positivity)).trans_eq ?_)
    rw [← pow_mul,← pow_succ,div_pow]
    congr 1
    · congr 1; omega
    · rw [pow_succ,show s*2=2*s by omega,pow_mul,Z13 (by positivity)]
end TraceReconstruction
namespace TraceReconstruction
theorem QpD {α:Type*} [Fintype α]
    (f:IntSeries) (z:α → ℤ) (hz:Z28 z) :
    (∑ a,f.coeff (z a)^2) ≤ seriesL2Sq f:=by
  simpa only [tsum_fintype,seriesL2Sq] using Summable.tsum_le_tsum_of_inj z hz (fun _ _ => sq_nonneg _)
      (fun _ => le_rfl) (hasSum_fintype _).summable (QbU f (fun x => x^2) (by simp))
def QcM {l r:ℕ} (f:Fin (r+1) → IntSeries)
    (shift:Fin (r+1) → ℤ) (v:Qab l r):ℝ :=
  ∏ i,(f i).coeff ((tupleGap v.val i:ℤ)-shift i)
theorem QpQ {l r:ℕ}
    (f:Fin (r+1) → IntSeries) (shift:Fin (r+1) → ℤ)
    (e:Fin (r+1)) (M:ℝ) (hM:0 ≤ M)
    (hbound:∀ z:ℤ,(f e).coeff z ^ 2 ≤ M) :
    (∑ v:Qab l r,QcM f shift v ^ 2) ≤
      M * ∏ i:Fin r,seriesL2Sq (f (Z18 0 e i.succ)):=by
  classical
  let σ:Equiv.Perm (Fin (r+1)):=Z18 0 e
  let F:Fin (r+1) → Fin (l-r+1) → ℝ :=
    fun i k => (f (σ i)).coeff ((k.val:ℤ)-shift (σ i)) ^ 2
  have hF:∀ i k,0 ≤ F i k:=fun _ _ => sq_nonneg _
  have hpoint (v:Qab l r) :
      QcM f shift v ^ 2 = ∏ i,F i (QbS σ v i):=by
    unfold QcM
    rw [← Finset.prod_pow]
    dsimp [F,QbS]
    exact (Equiv.prod_comp σ _).symm
  simp_rw [hpoint]
  calc
    _ ≤ ∑ z:Fin (r+1) → Fin (l-r+1),
        if ∑ i,(z i).val = l-r then ∏ i,F i (z i) else 0:=by
      exact QcP (QbS σ) (QfD σ)
        (fun z => ∑ i,(z i).val = l-r) (Qis σ)
        (fun z => ∏ i,F i (z i)) (fun _ => Z37 (fun _ _ => hF _ _))
    _ ≤ M * ∏ i:Fin r,∑ k:Fin (l-r+1),F i.succ k :=
      Qee r (l-r) F hF M hM (by
        intro k
        simpa only [F,σ,Equiv.swap_apply_left] using hbound ((k.val:ℤ)-shift e))
    _ ≤ _:=by
      apply mul_le_mul_of_nonneg_left _ hM
      apply Z45 (fun _ _ => Z11 (fun _ _ => hF _ _))
      intro i _
      dsimp only [F]
      apply QpD
      intro a b h
      exact Z34 (Int.ofNat_inj.mp (sub_left_injective h))
theorem Qpk {α V:Type*} [Fintype α] [Fintype V]
    (c:α → ℝ) (F:α → V → ℝ) (B:α → ℝ)
    (hB:∀ a,(∑ v,F a v ^ 2) ≤ B a) :
    (∑ v,(∑ a,c a * F a v)^2) ≤ (∑ a,|c a|) * ∑ a,|c a| * B a:=by
  have hp (v:V):(∑ a,c a*F a v)^2 ≤
      (∑ a,|c a|) * ∑ a,|c a| * F a v^2:=by
    apply Z84 Z16
      (fun _ _ => abs_nonneg _) (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    intro a _
    rw [mul_pow,← mul_assoc,← sq,sq_abs]
  calc
    _ ≤ ∑ v,(∑ a,|c a|) * ∑ a,|c a| * F a v^2 :=
      Z7 (fun v _ => hp v)
    _ = (∑ a,|c a|) * ∑ a,|c a| * ∑ v,F a v^2:=by
      rw [← Z3,Z17]
      simp_rw [← Z3]
    _ ≤ _:=by
      apply mul_le_mul_of_nonneg_left _ (Z11 (fun _ _ => abs_nonneg _))
      apply Z7
      intro a _
      exact mul_le_mul_of_nonneg_left (hB a) (abs_nonneg _)
end TraceReconstruction
namespace TraceReconstruction
def Qbf {ι:Type*} [Fintype ι] (f:ι → IntSeries) :
    AddMonoidAlgebra ℝ (ι → ℤ) :=
by
  classical
  exact AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (Fintype.piFinset (fun i => (f i).coeff.support))
    (fun z => ∏ i,(f i).coeff (z i)) (by
      classical
      intro z hz
      simp only [Fintype.mem_piFinset,Finsupp.mem_support_iff]
      exact fun i => (Finset.prod_ne_zero_iff.mp hz) i (Z21 i)))
theorem Qdy {ι:Type*} [Fintype ι] (f:ι → IntSeries) (z:ι → ℤ) :
    (Qbf f).coeff z = ∏ i,(f i).coeff (z i):=rfl
theorem QqE {ι:Type*} [Fintype ι] [DecidableEq ι]
    (f:ι → IntSeries) :
    (Qbf f).coeff.support = Fintype.piFinset (fun i => (f i).coeff.support):=by
  classical
  ext z
  simp [Qdy,Finset.prod_ne_zero_iff]
theorem Qez {ι:Type*} [Fintype ι] (f g:ι → IntSeries) :
    Qbf (fun i => f i*g i) = Qbf f * Qbf g:=by
  classical
  ext z
  rw [Qdy,Z79,Finsupp.sum,QqE]
  simp_rw [Qdy,← Z30]
  simp only [Pi.add_apply,Pi.neg_apply]
  rw [← Finset.prod_univ_sum (fun i => (f i).coeff.support)
    (fun i j => (f i).coeff j * (g i).coeff (-j + z i))]
  apply Z71 rfl
  intro i _
  rw [Z79,Finsupp.sum]
theorem QqD {ι:Type*} [Fintype ι] :
    Qbf (fun _:ι => (1:IntSeries)) = 1:=by
  classical
  ext z
  rw [Qdy]
  change (∏ i,Finsupp.single 0 (1:ℝ) (z i)) = Finsupp.single 0 (1:ℝ) z
  simp only [Z42]
  by_cases hz:z = 0
  · subst z; simp
  · have he:∃ i,z i ≠ 0:=by simpa [funext_iff] using hz
    obtain ⟨i,hi⟩:=he
    rw [if_neg (Ne.symm hz)]
    exact Z69 (Z21 i) (by simp [Ne.symm hi])
def QbO {ι:Type*} [DecidableEq ι] (i:ι):ℤ →+ (ι → ℤ) where
  toFun:=fun a => Pi.single (M:=fun _ => ℤ) i a
  map_zero':=Pi.single_zero i
  map_add':=fun a b => by
    ext j
    by_cases h:j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
def QbA {ι:Type*} [DecidableEq ι] (i:ι) :
    IntSeries →+* AddMonoidAlgebra ℝ (ι → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom ℝ (QbO i)
theorem QkK {ι:Type*} [DecidableEq ι] (i:ι) :
    Z28 (QbO i):=by
  intro a b h
  simpa only [QbO,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Pi.single_eq_same]
    using congrFun h i
theorem QiQ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (i:ι) (f:IntSeries) :
    Qbf (fun j => if j=i then f else 1) = QbA i f:=by
  classical
  ext z
  rw [Qdy]
  change (∏ j,(if j=i then f else (1:IntSeries)).coeff (z j)) =
    (Finsupp.mapDomain (QbO i) f.coeff) z
  by_cases hz:∀ j,j ≠ i → z j = 0
  · have he:QbO i (z i) = z:=by
      funext j
      by_cases hj:j=i
      · subst j; simp [QbO]
      · simp [QbO,Pi.single_eq_of_ne hj,hz j hj]
    rw [← he,Finsupp.mapDomain_apply (QkK i)]
    rw [Finset.prod_eq_single i]
    · simp [QbO]
    · intro j _ hj
      simp [hj,QbO]
    · simp
  · push Not at hz
    obtain ⟨j,hji,hj⟩:=hz
    have hn:z ∉ Set.range (QbO i):=by
      rintro ⟨a,ha⟩
      have h:=congrFun ha j
      simp [QbO,Pi.single_eq_of_ne hji] at h
      exact hj h.symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn]
    apply Z69 (Z21 j)
    simp only [if_neg hji]
    change Finsupp.single 0 (1:ℝ) (z j) = 0
    simp [Ne.symm hj]
theorem QiR {ι α:Type*} [Fintype ι]
    (s:Finset α) (f:α → ι → IntSeries) :
    Qbf (fun i => ∏ a ∈ s,f a i) = ∏ a ∈ s,Qbf (f a):=by
  classical
  induction s using Finset.induction_on with
  | empty => simp [QqD]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [Qez,ih]
end TraceReconstruction
namespace TraceReconstruction
theorem QmV {s t:ℕ} (hst:s ≤ t)
    {p:ℝ} (hp:p ∈ Z4 0 1) :
    QaJ s p ≤ QaJ t p:=by
  unfold QaJ
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Z24
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hst)
    (mul_pos hp.1 (sub_pos.mpr hp.2)).le
end TraceReconstruction
namespace TraceReconstruction
inductive Qac
  | unchanged | first | second
  deriving DecidableEq
def Qac.order:Qac → ℕ
  | .unchanged => 0 | .first => 1 | .second => 2
def Qch {r:ℕ} (h:Fin r) (b:Bool):Fin (r+1) :=
  if b then h.succ else h.castSucc
def Qci (k:Qac) (a:Bool × Bool):ℝ :=
  match k with
  | .unchanged => 1/4
  | .first => (if a.1 then -1 else 1)/2
  | .second => (if a.1 then -1 else 1)*(if a.2 then -1 else 1)/2
def QbC {r:ℕ} (h:Fin r) (k:Qac) (a:Bool × Bool)
    (i:Fin (r+1)):ℕ :=
  match k with
  | .unchanged => 0
  | .first => if i = Qch h a.1 then 1 else 0
  | .second => (if i = Qch h a.1 then 1 else 0) +
      (if i = Qch h a.2 then 1 else 0)
def QcE {r:ℕ} (h:Fin r) (k:Qac) (a:Bool × Bool)
    (i:Fin (r+1)):ℕ :=
  match k with
  | .unchanged => (if i = h.castSucc then 1 else 0) + (if i = h.succ then 1 else 0)
  | .first => if i = Qch h a.2 then 1 else 0
  | .second => 0
def Qde {r:ℕ} (h:Fin r) (k:Qac) (p:ℝ) :
    AddMonoidAlgebra ℝ (Fin (r+1) → ℤ) :=
  let L:=QbA h.castSucc (Qaf 1 p)
  let R:=QbA h.succ (Qaf 1 p)
  match k with
  | .unchanged => L*R
  | .first => (1/2:ℝ) • (L^2-R^2)
  | .second => (1/2:ℝ) • (L^2+R^2-2*L*R)
theorem QiS {ι:Type*} [Fintype ι] [DecidableEq ι]
    (a b:ι) (f g:IntSeries) :
    Qbf (fun i => f^(if i=a then 1 else 0) * g^(if i=b then 1 else 0)) =
      QbA a f * QbA b g:=by
  rw [Qez]
  have h (c:ι) (u:IntSeries) :
      (fun i => u^(if i=c then 1 else 0)) = (fun i => if i=c then u else 1):=by
    funext i
    split <;> simp
  rw [h,h,QiQ,QiQ]
theorem QlM {r:ℕ} (h:Fin r) (k:Qac)
    (a:Bool × Bool) (p:ℝ) :
    Qbf (fun i => (Qaf 1 p-1)^QbC h k a i *
      (Qaf 1 p)^QcE h k a i) =
      match k with
      | .unchanged => QbA h.castSucc (Qaf 1 p) *
          QbA h.succ (Qaf 1 p)
      | .first => (QbA (Qch h a.1) (Qaf 1 p)-1) *
          QbA (Qch h a.2) (Qaf 1 p)
      | .second => (QbA (Qch h a.1) (Qaf 1 p)-1) *
          (QbA (Qch h a.2) (Qaf 1 p)-1):=by
  cases k <;> simp only [QbC,QcE,pow_zero,pow_add,one_mul,mul_one]
  all_goals rw [QiS]
  all_goals simp only [map_sub,map_one]
theorem QlN {r:ℕ} (h:Fin r) (k:Qac) (p:ℝ) :
    Qde h k p = ∑ a:Bool × Bool,Qci k a •
      Qbf (fun i => (Qaf 1 p-1)^QbC h k a i *
        (Qaf 1 p)^QcE h k a i):=by
  simp_rw [QlM]
  cases k <;> simp only [Qde,Qci,Z32,
    Z62,Qch,Bool.false_eq_true,ite_false,ite_true]
  · module
  all_goals simp only [Algebra.smul_def]
  all_goals norm_num
  all_goals ring
theorem QlT (k:Qac) :
    (∑ a:Bool × Bool,|Qci k a|) ≤ 2:=by
  cases k <;> norm_num [Qci,Z32,Z62]
theorem QlS {r:ℕ} (h:Fin r) (k:Qac) (a:Bool × Bool) :
    (∑ i,QbC h k a i) = k.order:=by
  cases k <;> simp [QbC,Qac.order,Z14]
theorem QlP {r:ℕ} (g:Fin (r+1) → ℕ)
    (k:Fin r → Qac) (p:ℝ) :
    Qbf (fun i => Qaf (g i) p) * (∏ h,Qde h (k h) p) =
      ∑ a:Fin r → Bool × Bool,(∏ h,Qci (k h) (a h)) •
        Qbf (fun i => Qbv
          (g i + ∑ h,QcE h (k h) (a h) i)
          (∑ h,QbC h (k h) (a h) i) p):=by
  classical
  simp_rw [QlN]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rw [Z3]
  apply Z2 rfl
  intro a _
  rw [Finset.prod_smul,mul_smul_comm,← QiR,← Qez]
  congr 2
  funext i
  simp only [Qbv,Qaf,
    Z30,Z99]
  ring
theorem QlQ {r:ℕ} (k:Fin r → Qac) :
    (∑ a:Fin r → Bool × Bool,|∏ h,Qci (k h) (a h)|) ≤ (2:ℝ)^r:=by
  simp_rw [Finset.abs_prod]
  rw [← Z43 (fun h a => |Qci (k h) a|)]
  calc
    _ ≤ ∏ _h:Fin r,(2:ℝ):=by
      apply Z45 (fun _ _ => Z11 fun _ _ => abs_nonneg _)
      intro h _
      exact QlT (k h)
    _ = _:=by simp
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem QoV {α:Type*} [CommMonoid α] {r:ℕ}
    (f:Fin (r+1) → α) (e:Fin (r+1)) :
    f e * (∏ i:Fin r,f (Z18 0 e i.succ)) = ∏ i,f i:=by
  calc
    _ = ∏ i:Fin (r+1),f (Z18 0 e i):=by
      rw [Z53,Equiv.swap_apply_left]
    _ = _:=Equiv.prod_comp (Z18 0 e) f
theorem QmW (g b s:ℕ) {p C G:ℝ}
    (hp:p ∈ Z4 0 1) (hC:QaJ s p ≤ C)
    (hG:0 < G) (hb:b ≤ g) (hGg:G ≤ (g:ℝ)+1) :
    (∀ z:ℤ,(Qbv g s p).coeff z^2 ≤
      (C/Z0 ((b:ℝ)+1)) * (C^(2*s+1)/(G^s*Z0 ((b:ℝ)+1)))) ∧
    seriesL2Sq (Qbv g s p) ≤
      C^(2*s+1)/(G^s*Z0 ((b:ℝ)+1)):=by
  have hC0:0 < C:=(QcI s hp).trans_le hC
  have hb0:0 < (b:ℝ)+1:=by positivity
  have hg0:0 < (g:ℝ)+1:=by positivity
  have hb':(b:ℝ)+1 ≤ (g:ℝ)+1:=by exact_mod_cast Nat.add_le_add_right hb 1
  have hpow:G^s ≤ ((g:ℝ)+1)^s:=pow_le_pow_left₀ hG.le hGg s
  have hx:=QjG g s hp
  constructor
  · intro z
    refine (hx.1 z).trans ?_
    have hc:=pow_le_pow_left₀ (QcI s hp).le hC (2*s+2)
    have hd:G^s*((b:ℝ)+1) ≤ ((g:ℝ)+1)^(s+1):=by
      rw [pow_succ]
      exact mul_le_mul hpow hb' hb0.le (by positivity)
    calc
      _ ≤ C^(2*s+2)/(G^s*((b:ℝ)+1)):=by
        apply div_le_div₀ (by positivity) hc (by positivity) hd
      _ = _:=by
        have hsq:=Z13 hb0.le
        have hs:Z0 ((b:ℝ)+1) ≠ 0:=(Real.sqrt_pos.mpr hb0).ne'
        rw [show 2*s+2=(2*s+1)+1 by omega,pow_succ]
        field_simp
        nlinarith only [hsq]
  · refine hx.2.trans ?_
    apply div_le_div₀ (by positivity)
      (pow_le_pow_left₀ (QcI s hp).le hC (2*s+1))
      (by positivity)
    exact mul_le_mul hpow (Z24 hb') (Z36 _) (by positivity)
theorem Qpj {l r:ℕ}
    (g b s:Fin (r+1) → ℕ) (shift:Fin (r+1) → ℤ)
    {p C G:ℝ} (hp:p ∈ Z4 0 1)
    (hC:∀ i,QaJ (s i) p ≤ C) (hG:0 < G)
    (hb:∀ i,b i ≤ g i) (hGg:∀ i,G ≤ (g i:ℝ)+1) (e:Fin (r+1)) :
    (∑ v:Qab l r,
      QcM (fun i => Qbv (g i) (s i) p) shift v ^ 2) ≤
      C^(2*(∑ i,s i)+r+2) /
        (G^(∑ i,s i) * Z0 ((b e:ℝ)+1) * ∏ i,Z0 ((b i:ℝ)+1)):=by
  let F (i:Fin (r+1)):ℝ:=C^(2*s i+1)/(G^(s i)*Z0 ((b i:ℝ)+1))
  have hC0:0 < C:=(QcI (s e) hp).trans_le (hC e)
  have hF:∀ i,0 ≤ F i:=fun i => by dsimp [F]; positivity
  have hbound (i:Fin (r+1)):=QmW (g i) (b i) (s i) hp (hC i) hG (hb i) (hGg i)
  calc
    _ ≤ (C/Z0 ((b e:ℝ)+1)*F e) *
        ∏ i:Fin r,seriesL2Sq (Qbv (g (Z18 0 e i.succ))
          (s (Z18 0 e i.succ)) p):=by
      apply QpQ _ shift e _ (by positivity [hF e])
      exact (hbound e).1
    _ ≤ (C/Z0 ((b e:ℝ)+1)*F e) * ∏ i:Fin r,F (Z18 0 e i.succ):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity [hF e])
      apply Z45 (fun _ _ => Qcn _)
      intro i _
      exact (hbound _).2
    _ = (C/Z0 ((b e:ℝ)+1))*∏ i,F i:=by
      rw [mul_assoc,QoV]
    _ = _:=by
      simp only [F,Finset.prod_div_distrib,Z30,
        Z99,Z14,← Z3,
        Z59,Z48,Z26,smul_eq_mul,mul_one]
      rw [show 2*(∑ i,s i)+r+2=(2*(∑ i,s i)+(r+1))+1 by omega,pow_succ]
      ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
def Qae {n r:ℕ} (p:Fin r → Fin n):Prop :=
  (∀ i,1 ≤ (p i).val ∧ (p i).val+1 < n) ∧
  ∀ i j,i < j → (p i).val+3 ≤ (p j).val
def shiftedTag {n r:ℕ} (p:Fin r → Fin n) (hp:Qae p)
    (a:Fin r → Fin 3) (i:Fin r):Fin n :=
  ⟨(p i).val+(a i).val-1,by
    have h:=hp.1 i
    have ha:=(a i).isLt
    omega⟩
theorem QfF {n r:ℕ} (p:Fin r → Fin n) (hp:Qae p)
    (a:Fin r → Fin 3):StrictMono (shiftedTag p hp a):=by
  intro i j hij
  change (p i).val+(a i).val-1 < (p j).val+(a j).val-1
  have h:=hp.2 i j hij
  have hi:=hp.1 i
  have hj:=hp.1 j
  have hai:=(a i).isLt
  omega
def QaH (r:ℕ) (i:Fin (r+1)):ℕ :=
  Z15 (α:=fun _ => ℕ) 0 (fun _:Fin r => 1) i + Fin.snoc (α:=fun _ => ℕ) (fun _:Fin r => 1) 0 i
def QbV {r:ℕ} (a:Fin r → Fin 3) (i:Fin (r+1)):ℕ :=
  Z15 (α:=fun _ => ℕ) 0 (fun h => 2-(a h).val) i + Fin.snoc (α:=fun _ => ℕ) (fun h => (a h).val) 0 i
def Qdn {r:ℕ} (h:Fin r) (a:Fin 3) (i:Fin (r+1)):ℕ :=
  (if i=h.castSucc then a.val else 0) + (if i=h.succ then 2-a.val else 0)
theorem Qqu {r:ℕ} (f:Fin r → ℕ) (i:Fin (r+1)) :
    (∑ h,if i=h.castSucc then f h else 0) = Fin.snoc (α:=fun _ => ℕ) f 0 i:=by
  induction i using Z60 with
  | last => simp [eq_comm]
  | cast h => simp
theorem QqB {r:ℕ} (f:Fin r → ℕ) (i:Fin (r+1)) :
    (∑ h,if i=h.succ then f h else 0) = Z15 (α:=fun _ => ℕ) 0 f i:=by
  induction i using Z38 with
  | zero => simp [eq_comm]
  | succ h => simp
theorem QpE {r:ℕ} (a:Fin r → Fin 3) (i:Fin (r+1)) :
    QbV a i = ∑ h,Qdn h (a h) i:=by
  simp only [Qdn,Z14,Qqu,
    QqB,QbV]
  omega
theorem Qha {n r:ℕ} (p:Fin r → Fin n) (hp:Qae p)
    (i:Fin (r+1)):QaH r i ≤ tupleGap p i:=by
  cases r with
  | zero =>
    have hi:i=0:=Fin.eq_zero i
    subst i
    simp [QaH,Fin.snoc_zero]
  | succ r =>
    induction i using Z38 with
    | zero => simpa only [QaH,Z54,zero_add,Fin.snoc_apply_zero,
        QeD] using (hp.1 0).1
    | succ i =>
      induction i using Z60 with
      | last =>
        simp only [QaH,Fin.succ_last,Fin.cons_last,Fin.snoc_last,add_zero,
          QeC]
        have h:=(hp.1 (Z22 r)).2
        omega
      | cast i =>
        simp only [QaH,Z55]
        rw [Z100,Fin.snoc_castSucc]
        rw [← Z100,QdZ]
        have h:=hp.2 i.castSucc i.succ (by simp)
        omega
theorem QiX {n r:ℕ} (p:Fin r → Fin n) (hp:Qae p)
    (a:Fin r → Fin 3) (i:Fin (r+1)) :
    tupleGap (shiftedTag p hp a) i =
      tupleGap p i - QaH r i + QbV a i:=by
  cases r with
  | zero =>
    have hi:i=0:=Fin.eq_zero i
    subst i
    simp [tupleGap,tupleLower,tupleUpper,QaH,QbV,Fin.snoc_zero]
  | succ r =>
    induction i using Z38 with
    | zero =>
      simp only [QeD,QaH,QbV,Z54,zero_add,
        Fin.snoc_apply_zero,shiftedTag]
      have h:=(hp.1 0).1
      omega
    | succ i =>
      induction i using Z60 with
      | last =>
        simp only [QaH,QbV,Fin.succ_last,Fin.cons_last,
          Fin.snoc_last,add_zero,QeC,shiftedTag]
        have h:=hp.1 (Z22 r)
        have ha:=(a (Z22 r)).isLt
        omega
      | cast i =>
        simp only [QaH,QbV,Z55]
        rw [Z100,Fin.snoc_castSucc,Fin.snoc_castSucc]
        rw [← Z100,QdZ,QdZ]
        change (p i.succ).val+(a i.succ).val-1-((p i.castSucc).val+(a i.castSucc).val-1+1) = _
        have hi:=hp.1 i.castSucc
        have hj:=hp.1 i.succ
        have hij:=hp.2 i.castSucc i.succ (by simp)
        have hai:=(a i.castSucc).isLt
        have haj:=(a i.succ).isLt
        omega
def Qbx (k:Qac) (a:Fin 3):ℝ :=
  match k with
  | .unchanged => if a=1 then 1 else 0
  | .first => if a=0 then -1/2 else if a=2 then 1/2 else 0
  | .second => if a=1 then -1 else 1/2
theorem Qna {r:ℕ} (h:Fin r) (a:Fin 3) (p:ℝ) :
    Qbf (fun i => (Qaf 1 p)^Qdn h a i) =
      QbA h.castSucc (Qaf 1 p)^a.val *
        QbA h.succ (Qaf 1 p)^(2-a.val):=by
  have hpow (u:IntSeries) (t:ℕ) (c i:Fin (r+1)) :
      u^(if i=c then t else 0) = (u^t)^(if i=c then 1 else 0):=by
    split <;> simp
  have he:(fun i => (Qaf 1 p)^Qdn h a i) =
      (fun i => ((Qaf 1 p)^a.val)^(if i=h.castSucc then 1 else 0) *
        ((Qaf 1 p)^(2-a.val))^(if i=h.succ then 1 else 0)):=by
    funext i
    rw [Qdn,pow_add,hpow _ _ h.castSucc i,hpow _ _ h.succ i]
  rw [he,QiS,map_pow,map_pow]
theorem QlO {r:ℕ} (h:Fin r) (k:Qac)
    (p:ℝ) :
    Qde h k p = ∑ a:Fin 3,Qbx k a •
      Qbf (fun i => (Qaf 1 p)^Qdn h a i):=by
  simp_rw [Qna]
  rw [Fin.sum_univ_three]
  cases k <;> norm_num [Qbx,Qde,Fin.ext_iff]
  all_goals try simp only [two_mul,add_mul]
  all_goals module
theorem QpH {n r:ℕ} (p:Fin r → Fin n)
    (hp:Qae p) (k:Fin r → Qac) (θ:ℝ) :
    (∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h)) •
      Qbf (fun i => Qaf (tupleGap (shiftedTag p hp a) i) θ)) =
    Qbf (fun i => Qaf (tupleGap p i-QaH r i) θ) *
      ∏ h,Qde h (k h) θ:=by
  classical
  simp_rw [QlO]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  rw [Z3]
  apply Z2 rfl
  intro a _
  rw [Finset.prod_smul,mul_smul_comm,← QiR,← Qez]
  congr 2
  funext i
  rw [QiX,QpE]
  simp only [Qaf,pow_one,Z99,pow_add]
def QbF {n l r:ℕ} (hl:l ≤ n) (p:Fin r → Fin n)
    (hp:Qae p) (k:Fin r → Qac) (v:Qab l r):ℝ :=
  ∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h)) *
    Qaw hl (shiftedTag p hp a) v.val
theorem Qoz {n l r:ℕ} (hl:l ≤ n)
    (p:Fin r → Fin n) (hp:Qae p) (k:Fin r → Qac)
    {θ:ℝ} (hθ:θ ∈ Z4 0 1) (v:Qab l r) :
    QbF hl p hp k v = θ^r / Qaa n θ l *
      ∑ a:Fin r → Bool × Bool,(∏ h,Qci (k h) (a h)) *
        QcM (fun i => Qbv
          (tupleGap p i-QaH r i + ∑ h,QcE h (k h) (a h) i)
          (∑ h,QbC h (k h) (a h) i) θ) (fun _ => 0) v:=by
  have h:=QpH p hp k θ
  rw [QlP] at h
  have hh:=congrArg (fun f:AddMonoidAlgebra ℝ (Fin (r+1) → ℤ) =>
    f.coeff (fun i => (tupleGap v.val i:ℤ))) h
  simp only [Z58,Z73,
    Z88,Z89,smul_eq_mul,Qdy,
    QcV] at hh
  unfold QbF
  simp_rw [Qex hl _ (QfF p hp _) _ v.property θ hθ]
  calc
    _ = θ^r / Qaa n θ l *
        ∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h)) *
          ∏ i,Qaa (tupleGap (shiftedTag p hp a) i) θ (tupleGap v.val i):=by
      rw [Z3]
      apply Z2 rfl
      intro a _
      ring
    _ = _:=by
      exact congrArg (fun t => θ^r / Qaa n θ l * t) (by
        simpa only [QcM,sub_zero] using hh)
theorem Qhc {r:ℕ} (k:Fin r → Qac) (a:Fin r → Bool × Bool) :
    (∑ i:Fin (r+1),∑ h,QbC h (k h) (a h) i) = ∑ h,(k h).order:=by
  rw [Z17]
  simp_rw [QlS]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem QlR {r:ℕ} (k:Fin r → Qac)
    (a:Fin r → Bool × Bool) (i:Fin (r+1)) :
    (∑ h,QbC h (k h) (a h) i) ≤ ∑ h,(k h).order:=by
  rw [← Qhc k a]
  exact Z82 (f:=fun j:Fin (r+1) => ∑ h,QbC h (k h) (a h) j)
    (fun _ _ => Nat.zero_le _) (Z21 i)
theorem QoB {n l r:ℕ} (hl:l ≤ n)
    (p:Fin r → Fin n) (hp:Qae p) (k:Fin r → Qac)
    {θ G:ℝ} (hθ:θ ∈ Z4 0 1) (hG:0 < G)
    (hgap:∀ i,G ≤ (tupleGap p i-QaH r i:ℕ)+1)
    (e:Fin (r+1)) :
    (∑ v:Qab l r,QbF hl p hp k v ^ 2) ≤
      (θ^r / Qaa n θ l)^2 * (2:ℝ)^(2*r) *
        (QaJ (∑ h,(k h).order) θ)^(2*(∑ h,(k h).order)+r+2) /
      (G^(∑ h,(k h).order) * Z0 ((tupleGap p e-QaH r e:ℕ)+1) *
        ∏ i,Z0 ((tupleGap p i-QaH r i:ℕ)+1)):=by
  let d:=∑ h,(k h).order
  let C:=QaJ d θ
  let b (i:Fin (r+1)):=tupleGap p i-QaH r i
  let B:=C^(2*d+r+2) / (G^d*Z0 ((b e:ℝ)+1)*∏ i,Z0 ((b i:ℝ)+1))
  let c (a:Fin r → Bool × Bool):=∏ h,Qci (k h) (a h)
  let F (a:Fin r → Bool × Bool) (v:Qab l r) :=
    QcM (fun i => Qbv
      (b i+∑ h,QcE h (k h) (a h) i)
      (∑ h,QbC h (k h) (a h) i) θ) (fun _ => 0) v
  have hC:0 < C:=QcI d hθ
  have hB0:0 ≤ B:=by dsimp [B]; positivity
  have hB (a:Fin r → Bool × Bool):(∑ v,F a v^2) ≤ B:=by
    have hd (i:Fin (r+1)):QaJ (∑ h,QbC h (k h) (a h) i) θ ≤ C :=
      QmV (QlR k a i) hθ
    have h:=Qpj (l:=l)
      (fun i => b i+∑ h,QcE h (k h) (a h) i) b
      (fun i => ∑ h,QbC h (k h) (a h) i) (fun _ => 0)
      hθ hd hG (fun _ => Nat.le_add_right _ _) (by
        intro i
        exact (hgap i).trans (by exact_mod_cast Nat.add_le_add_right (Nat.le_add_right (b i) _) 1)) e
    simpa only [F,B,d,Qhc] using h
  have hmix:=Qpk c F (fun _ => B) hB
  have hM:(∑ a,|c a|) ≤ (2:ℝ)^r:=QlQ k
  have hM0:0 ≤ ∑ a,|c a|:=Z11 fun _ _ => abs_nonneg _
  have hmix':(∑ v,(∑ a,c a*F a v)^2) ≤ (2:ℝ)^(2*r)*B:=by
    refine hmix.trans ?_
    rw [← Z33,← mul_assoc]
    have hs:(∑ a,|c a|)^2 ≤ ((2:ℝ)^r)^2:=(sq_le_sq₀ hM0 (by positivity)).mpr hM
    calc
      _ = (∑ a,|c a|)^2*B:=by ring
      _ ≤ ((2:ℝ)^r)^2*B:=mul_le_mul_of_nonneg_right hs hB0
      _ = _:=by rw [← pow_mul,Nat.mul_comm r 2]
  simp_rw [Qoz hl p hp k hθ,mul_pow]
  rw [← Z3]
  calc
    _ ≤ (θ^r / Qaa n θ l)^2 * ((2:ℝ)^(2*r)*B) :=
      mul_le_mul_of_nonneg_left hmix' (sq_nonneg _)
    _ = _:=by dsimp [B,C,d,b]; ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem Qhb (r:ℕ) (i:Fin (r+1)):QaH r i ≤ 2:=by
  have h₁:Z15 (α:=fun _ => ℕ) 0 (fun _:Fin r => 1) i ≤ 1:=by
    induction i using Z38 <;> simp
  have h₂:Fin.snoc (α:=fun _ => ℕ) (fun _:Fin r => 1) 0 i ≤ 1:=by
    induction i using Z60 <;> simp
  exact Nat.add_le_add h₁ h₂
theorem QkI {u m r:ℕ} (off:Fin m)
    (hoff₁:1 ≤ off.val) (hoff₂:off.val+1 < m) (hm:3 ≤ m)
    (j:Fin r → Fin u) (hj:StrictMono j) :
    Qae (periodSlot (fun _ => off) ∘ j):=by
  constructor
  · intro i
    change 1 ≤ (j i).val*m+off.val ∧ (j i).val*m+off.val+1 < u*m
    constructor
    · omega
    · have h:=Z51 m (Z68 (j i).isLt)
      rw [Nat.succ_mul] at h
      omega
  · intro i h hih
    change (j i).val*m+off.val+3 ≤ (j h).val*m+off.val
    have h:=Z51 m (Nat.succ_le_iff.mpr (hj hih))
    rw [Nat.succ_mul] at h
    omega
theorem Qfw {u m r:ℕ} (hm:32 ≤ m) (hr:0 < r)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j:Fin r → Fin u) (hj:StrictMono j)
    (hsafe:Qae (periodSlot off ∘ j)) (i:Fin (r+1)) :
    (m:ℝ)*Qad j i/4 ≤
      ((tupleGap (periodSlot off ∘ j) i-QaH r i:ℕ):ℝ)+1:=by
  have he:=abs_le.mp (Qfx hr off hoff hdiff j hj i)
  have hs:=Qha (periodSlot off ∘ j) hsafe i
  have hs₂:(QaH r i:ℝ) ≤ 2:=by exact_mod_cast Qhb r i
  have hc:1 ≤ (Qad j i:ℝ):=by exact_mod_cast QcB j i
  have hm':(32:ℝ) ≤ m:=by exact_mod_cast hm
  rw [Z47 hs]
  nlinarith
theorem Qop {u m r:ℕ} (hm:32 ≤ m) (hr:0 < r)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j:Fin r → Fin u) (hj:StrictMono j)
    (hsafe:Qae (periodSlot off ∘ j)) (i:Fin (r+1)) :
    (m:ℝ)/4 ≤ ((tupleGap (periodSlot off ∘ j) i-QaH r i:ℕ):ℝ)+1:=by
  refine le_trans ?_ (Qfw hm hr off hoff hdiff j hj hsafe i)
  have hc:1 ≤ (Qad j i:ℝ):=by exact_mod_cast QcB j i
  nlinarith [show (0:ℝ) ≤ m by positivity]
theorem Qoq {u m r:ℕ} (hm:32 ≤ m) (hr:0 < r)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j:Fin r → Fin u) (hj:StrictMono j)
    (hsafe:Qae (periodSlot off ∘ j)) (e:Fin (r+1))
    (he:2*u ≤ (r+1)*Qad j e) :
    (u:ℝ)*m/(2*(r+1:ℝ)) ≤
      ((tupleGap (periodSlot off ∘ j) e-QaH r e:ℕ):ℝ)+1:=by
  refine le_trans ?_ (Qfw hm hr off hoff hdiff j hj hsafe e)
  have he':2*(u:ℝ) ≤ (r+1:ℝ)*Qad j e:=by exact_mod_cast he
  apply (div_le_iff₀ (by positivity)).mpr
  have hh:=mul_le_mul_of_nonneg_right he' (show (0:ℝ) ≤ m by positivity)
  nlinarith only [hh]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem QjZ {n l r:ℕ} {θ:ℝ}
    (hθ:θ ∈ Z4 0 1) (hl:l ≤ n)
    (hmean:(n:ℝ)*θ=l) (hv:1 ≤ (n:ℝ)*θ*(1-θ)) :
    (θ^r/Qaa n θ l)^2 ≤ 144*(n:ℝ):=by
  have hpow:(θ^r)^2 ≤ 1:=pow_le_one₀ (pow_nonneg hθ.1.le r) (pow_le_one₀ hθ.1.le hθ.2.le) 
  calc
    _ = (θ^r)^2*(Qaa n θ l)⁻¹^2:=by rw [div_eq_mul_inv,mul_pow]
    _ ≤ (Qaa n θ l)⁻¹^2:=mul_le_of_le_one_left (sq_nonneg _) hpow
    _ ≤ 144*((n:ℝ)*θ*(1-θ)):=QeP n l hθ hl hmean hv
    _ ≤ _:=by
      have h:θ*(1-θ) ≤ 1:=by nlinarith [sq_nonneg θ]
      have hh:=mul_le_mul_of_nonneg_left h (show 0 ≤ (n:ℝ) by positivity)
      nlinarith only [hh]
theorem QoA {n l r:ℕ} (hl:l ≤ n)
    (p:Fin r → Fin n) (hp:Qae p) (k:Fin r → Qac)
    {θ G H:ℝ} (hθ:θ ∈ Z4 0 1) (hG:0 < G) (hH:0 < H)
    (hmean:(n:ℝ)*θ=l) (hv:1 ≤ (n:ℝ)*θ*(1-θ))
    (B:Fin (r+1) → ℝ) (hB:∀ i,0 < B i)
    (hgap:∀ i,G ≤ (tupleGap p i-QaH r i:ℕ)+1)
    (hscale:∀ i,B i ≤ (tupleGap p i-QaH r i:ℕ)+1)
    (e:Fin (r+1)) (hlarge:H ≤ Z0 ((tupleGap p e-QaH r e:ℕ)+1)) :
    (∑ v:Qab l r,QbF hl p hp k v ^ 2) ≤
      144*(n:ℝ)*(2:ℝ)^(2*r)*
        (QaJ (∑ h,(k h).order) θ)^(2*(∑ h,(k h).order)+r+2) /
      (G^(∑ h,(k h).order)*H*∏ i,Z0 (B i)):=by
  refine (QoB hl p hp k hθ hG hgap e).trans ?_
  have hC:=(QcI (∑ h,(k h).order) hθ).le
  apply div_le_div₀ (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (QjZ hθ hl hmean hv) (by positivity))
      (pow_nonneg hC _)
  · exact mul_pos (mul_pos (pow_pos hG _) hH)
      (Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (hB i)))
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hlarge (by positivity)
    · exact Z45 (fun i _ => (Z36 (B i)))
        (fun i _ => Z24 (hscale i))
    · exact Z37 (fun _ _ => Z36 _)
    · positivity
def QaW (u m r d:ℕ) (θ:ℝ):ℝ :=
  144*((u*m:ℕ):ℝ)*(2:ℝ)^(2*r)*(QaJ d θ)^(2*d+r+2) /
    (((m:ℝ)/4)^d*Z0 ((u:ℝ)*m/(2*(r+1:ℝ)))*
      (Z0 ((m:ℝ)/4))^(r+1))
theorem Qic {u m l r:ℕ}
    (hm:32 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j:Qab u r) (hsafe:Qae (periodSlot off ∘ j.val))
    (k:Fin r → Qac) {θ:ℝ} (hθ:θ ∈ Z4 0 1)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑ v:Qab l r,
      QbF hl (periodSlot off ∘ j.val) hsafe k v ^ 2) ≤
      QaW u m r (∑ h,(k h).order) θ *
        ∏ i,(Z0 (Qad j.val i))⁻¹:=by
  have hu:0 < u:=lt_of_le_of_lt (Nat.zero_le (j.val ⟨0,hr⟩).val) (j.val ⟨0,hr⟩).isLt
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hu0:(0:ℝ) < u:=by exact_mod_cast hu
  obtain ⟨e,he⟩:=QgI hr j
  have hb (i:Fin (r+1)):=Qfw hm hr off hoff hdiff j.val j.property hsafe i
  have hg (i:Fin (r+1)):=Qop hm hr off hoff hdiff j.val j.property hsafe i
  have hc (i:Fin (r+1)):(0:ℝ) < Qad j.val i:=by exact_mod_cast QcB j.val i
  have h:=QoA hl (periodSlot off ∘ j.val) hsafe k hθ
    (G:=(m:ℝ)/4) (H:=Z0 ((u:ℝ)*m/(2*(r+1:ℝ)))) (by positivity) (by positivity)
    hmean hv (fun i => (m:ℝ)*Qad j.val i/4) (fun i => by positivity [hc i]) hg hb e
    (Z24 (Qoq hm hr off hoff hdiff j.val j.property hsafe e he))
  refine h.trans_eq ?_
  have hs (i:Fin (r+1)):Z0 ((m:ℝ)*Qad j.val i/4) =
      Z0 ((m:ℝ)/4)*Z0 (Qad j.val i):=by
    rw [show (m:ℝ)*Qad j.val i/4=((m:ℝ)/4)*Qad j.val i by ring,
      Real.sqrt_mul (by positivity)]
  simp_rw [hs]
  rw [Z30]
  simp only [Z78,Z48,Z26]
  rw [QaW,Finset.prod_inv_distrib]
  ring
end TraceReconstruction
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
theorem Qrf {ι:Type*} [Fintype ι] [DecidableEq ι]
    (A:Finset ι) {e d:ι} (he:e∈A) (hd:d∉A)
    (x y:ι → ℕ) (hA:∑ i∈A,x i = ∑ i∈A,y i)
    (ht:∑ i,x i = ∑ i,y i)
    (hxy:∀ i,i≠e → i≠d → x i=y i):x=y:=by
  have hs:(∑ i∈A.erase e,x i) = ∑ i∈A.erase e,y i:=by
    apply Z2 rfl
    intro i hi
    have hi':=Finset.mem_erase.mp hi
    apply hxy i hi'.1
    intro hid
    exact hd (hid ▸ hi'.2)
  have hxe:x e=y e:=by
    have hx:=Z101 A x he
    have hy:=Z101 A y he
    omega
  have hs':(∑ i∈Finset.univ.erase d,x i) = ∑ i∈Finset.univ.erase d,y i:=by
    apply Z2 rfl
    intro i hi
    by_cases hie:i=e
    · simpa only [hie] using hxe
    · exact hxy i hie (Finset.mem_erase.mp hi).1
  have hxd:x d=y d:=by
    have hx:=Z101 Z16 x (Z21 d)
    have hy:=Z101 Z16 y (Z21 d)
    omega
  funext i
  by_cases hie:i=e
  · simpa only [hie] using hxe
  by_cases hid:i=d
  · simpa only [hid] using hxd
  exact hxy i hie hid
abbrev Qbc {ι:Type*} (e d:ι):={i:ι // i≠e ∧ i≠d}
theorem Qrg {α ι:Type*} [Fintype ι] [DecidableEq ι]
    {U L V:ℕ} (A:Finset ι) {e d:ι} (he:e∈A) (hd:d∉A)
    (p:α → ι → Fin (U+1)) (hp:Z28 p)
    (hA:∀ a,∑ i∈A,(p a i).val=L) (ht:∀ a,∑ i,(p a i).val=V) :
    Z28 (fun a => fun i:Qbc e d => p a i.val):=by
  intro a b hab
  apply hp
  have hv:(fun i => (p a i).val) = (fun i => (p b i).val):=by
    apply Qrf A he hd
    · rw [hA,hA]
    · rw [ht,ht]
    · intro i hie hid
      exact congrArg Fin.val (congrFun hab ⟨i,hie,hid⟩)
  funext i
  exact Z34 (congrFun hv i)
theorem Qjd {α ι:Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V:ℕ} (A:Finset ι) {e d:ι} (he:e∈A) (hd:d∉A)
    (p:α → ι → Fin (U+1)) (hp:Z28 p)
    (hA:∀ a,∑ i∈A,(p a i).val=L) (ht:∀ a,∑ i,(p a i).val=V)
    (w:ι → Fin (U+1) → ℝ) (hw:∀ i k,0≤w i k) :
    (∑ a,∏ i:Qbc e d,w i.val (p a i.val)) ≤
      ∏ i:Qbc e d,∑ k,w i.val k:=by
  classical
  have hh:=QcP
    (fun a => fun i:Qbc e d => p a i.val)
    (Qrg A he hd p hp hA ht)
    (fun _ => True) (fun _ => trivial)
    (fun δ => ∏ i:Qbc e d,w i.val (δ i))
    (fun δ => Z37 (fun i _ => hw i.val (δ i)))
  simp only [ite_true] at hh
  exact hh.trans_eq (by rw [Finset.prod_univ_sum]; simp only [Fintype.piFinset_univ])
theorem Qko {u r:ℕ} (j:Fin r → Fin u) (hj:StrictMono j)
    (i:Fin r):(∑ g∈Z31 i.castSucc,Qad j g) = 2*(j i).val+1:=by
  classical
  have hg:=QcQ j hj i
  have hz:(0:Fin (r+1)) ∈ Z31 i.castSucc:=by simp
  have hl:∀ g∈Z31 i.castSucc,g≠Z22 r:=by
    intro g hg he
    have hle:=Finset.mem_Iic.mp hg
    have hval:g.val ≤ i.val:=hle
    have he':=congrArg Fin.val he
    simp only [Fin.val_last] at he'
    omega
  have hc:(∑ g∈Z31 i.castSucc,
      if g=0 ∨ g=Z22 r then 1 else 2) = 2*i.val+1:=by
    have hsub:(∑ g∈(Z31 i.castSucc).erase 0,
        if g=0 ∨ g=Z22 r then 1 else 2) = 2*i.val:=by
      have hc:((Z31 i.castSucc).erase 0).card = i.val:=by
        rw [Finset.card_erase_of_mem hz,Fin.card_Iic]
        simp
      calc
        _ = ∑ _g∈(Z31 i.castSucc).erase 0,2:=by
          apply Z2 rfl
          intro g hg
          rw [if_neg (not_or.mpr ⟨(Finset.mem_erase.mp hg).1,
            hl g (Finset.mem_erase.mp hg).2⟩)]
        _ = _:=by simp [hc,Nat.mul_comm]
    have hsum:=Z101 (Z31 i.castSucc)
      (fun g => if g=0 ∨ g=Z22 r then 1 else 2) hz
    rw [hsub] at hsum
    simpa using hsum.symm
  simp only [Qad,Z14,← Z3]
  omega
theorem QgT (U:ℕ) :
    (∑ k:Fin (U+1),(Z0 (k.val:ℝ))⁻¹) ≤ 2*Z0 U:=by
  rw [Z64]
  simp only [Fin.val_zero,Nat.cast_zero,Real.sqrt_zero,inv_zero,zero_add,Fin.val_succ]
  have h:=QiN U
  rw [Finset.sum_range] at h
  simpa only [Z23,Z25] using h
theorem Qil {ι:Type*} [Fintype ι] [DecidableEq ι]
    {e d:ι} (hed:e≠d) (f:ι → ℝ) :
    (∏ i,f i) = f e*f d*∏ i:Qbc e d,f i.val:=by
  have hd:d∈Finset.univ.erase e:=by simp [hed.symm]
  have h1:=Finset.prod_erase_mul Z16 f (Z21 e)
  have h2:=Finset.prod_erase_mul (Finset.univ.erase e) f hd
  have hrem:(∏ i∈(Finset.univ.erase e).erase d,f i) =
      ∏ i:Qbc e d,f i.val :=
    Finset.prod_subtype _ (by intro i; simp [and_comm]) f
  rw [← h1,← h2,hrem]
  ring
theorem Qhu {x y R:ℝ} (hR:0<R) (hx:R≤x) (hy:R≤y) :
    (Z0 x)⁻¹*(Z0 y)⁻¹ ≤ R⁻¹:=by
  have hs:0<Z0 R:=Real.sqrt_pos.mpr hR
  have hix:=(inv_le_inv₀ (hs.trans_le (Z24 hx)) hs).mpr (Z24 hx)
  have hiy:=(inv_le_inv₀ (hs.trans_le (Z24 hy)) hs).mpr (Z24 hy)
  calc
    _ ≤ (Z0 R)⁻¹*(Z0 R)⁻¹:=mul_le_mul hix hiy (by positivity) (by positivity)
    _ = _:=by rw [← mul_inv,Real.mul_self_sqrt hR.le]
theorem Qrc {α ι:Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V:ℕ} (A:Finset ι) {e d:ι} (he:e∈A) (hd:d∉A)
    (p:α → ι → Fin (U+1)) (hp:Z28 p)
    (hA:∀ a,∑ i∈A,(p a i).val=L) (ht:∀ a,∑ i,(p a i).val=V)
    {R:ℝ} (hR:0<R) (heR:∀ a,R≤(p a e).val) (hdR:∀ a,R≤(p a d).val) :
    (∑ a,∏ i,(Z0 ((p a i).val:ℝ))⁻¹) ≤
      R⁻¹*(2*Z0 U)^Z10 (Qbc e d):=by
  classical
  have hed:e≠d:=by intro h; exact hd (h ▸ he)
  have hpoint (a):=Qhu hR (heR a) (hdR a)
  calc
    _ ≤ ∑ a,R⁻¹*∏ i:Qbc e d,(Z0 ((p a i.val).val:ℝ))⁻¹:=by
      apply Z7
      intro a _
      rw [Qil hed]
      exact mul_le_mul_of_nonneg_right (hpoint a) (by positivity)
    _ = R⁻¹*∑ a,∏ i:Qbc e d,(Z0 ((p a i.val).val:ℝ))⁻¹:=by
      rw [Z3]
    _ ≤ R⁻¹*∏ _i:Qbc e d,∑ k:Fin (U+1),(Z0 (k.val:ℝ))⁻¹:=by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact Qjd A he hd p hp hA ht
        (fun _ k => (Z0 (k.val:ℝ))⁻¹) (fun _ _ => by positivity)
    _ ≤ R⁻¹*∏ _i:Qbc e d,(2*Z0 U):=by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact Z45 (fun _ _ => by positivity) (fun _ _ => QgT U)
    _ = _:=by simp
def Qbl (u r:ℕ) (a:Fin r) (h:Fin u) :=
  {j:Qab u r // j.val a=h}
noncomputable instance Qrl (u r:ℕ) (a:Fin r) (h:Fin u) :
    Fintype (Qbl u r a h):=by
  unfold Qbl
  exact Fintype.ofFinite _
def Qcc {u r:ℕ} (a:Fin r) (h:Fin u) (j:Qbl u r a h) :
    Fin (r+1) → Fin (2*u+1):=fun i =>
  ⟨Qad j.val.val i,Z72
    (QcZ (Z91 a.isLt) j.val.val j.val.property i)⟩
theorem QgW {u r:ℕ} (a:Fin r) (h:Fin u) :
    Z28 (Qcc a h):=by
  intro j k hjk
  apply Subtype.ext
  apply Subtype.ext
  apply QeT j.val.property k.val.property
  funext i
  exact congrArg Fin.val (congrFun hjk i)
theorem Qdd {u r:ℕ} (a:Fin r) (h:Fin u)
    (j:Qbl u r a h) :
    (∑ i∈Z31 a.castSucc,(Qcc a h j i).val)=2*h.val+1:=by
  change (∑ i∈Z31 a.castSucc,Qad j.val.val i)=_
  rw [Qko _ j.val.property,j.property]
theorem Qem {u r:ℕ} (a:Fin r) (h:Fin u)
    (j:Qbl u r a h) :
    (∑ i,(Qcc a h j i).val)=2*u :=
  Qda (Z91 a.isLt) j.val.val j.val.property
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem Qgd (n:ℕ) {p t:ℝ}
    (hp:p∈Z6 0 1) (ht:|t|≤1) :
    (∑ k∈Z5 (n+1),Qaa n p k*Z1 (t*((k:ℝ)-n*p))) ≤
      Z1 ((n:ℝ)*t^2):=by
  have he:=(abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  have hn:0≤(n:ℝ)*p:=mul_nonneg (Z19 _) hp.1
  have hn':(n:ℝ)*p≤n:=mul_le_of_le_one_right (Z19 _) hp.2
  calc
    _ = Z1 (-t*(n:ℝ)*p)*
        ∑ k∈Z5 (n+1),Qaa n p k*Z1 (t*k):=by
      rw [Z3]
      apply Z2 rfl
      intro k _
      rw [mul_left_comm,← Z50]
      congr 2
      ring
    _ ≤ Z1 (-t*(n:ℝ)*p)*Z1 ((n:ℝ)*p*(Z1 t-1)) :=
      mul_le_mul_of_nonneg_left (QjM n hp t) (Z49 _)
    _ ≤ Z1 ((n:ℝ)*t^2):=by
      rw [← Z50]
      apply Real.exp_le_exp.mpr
      have he':=mul_le_mul_of_nonneg_left he hn
      have hs:=mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      nlinarith only [he',hs]
theorem Qgk (n:ℕ) {p t a ε:ℝ}
    (hp:p∈Z6 0 1) (ht:t∈Z6 0 1) (hε:ε=1 ∨ ε= -1) :
    (∑ k∈(Z5 (n+1)).filter (fun k:ℕ => a≤ε*((k:ℝ)-n*p)),Qaa n p k) ≤
      Z1 (-t*a+(n:ℝ)*t^2):=by
  have heps:|t*ε|≤1:=by rcases hε with rfl | rfl <;> simpa [abs_of_nonneg ht.1] using ht.2
  have hm:=QgU (Z5 (n+1)) (Qaa n p)
    (fun k:ℕ => ε*((k:ℝ)-n*p)) (fun k _ => QaF n k hp) a t ht.1
  calc
    _ ≤ Z1 (-t*a)*∑ k∈Z5 (n+1),
        Qaa n p k*Z1 ((t*ε)*((k:ℝ)-n*p)):=by
      simpa only [mul_assoc] using hm
    _ ≤ Z1 (-t*a)*Z1 ((n:ℝ)*(t*ε)^2) :=
      mul_le_mul_of_nonneg_left (Qgd n hp heps) (Z49 _)
    _ = _:=by rcases hε with rfl | rfl <;> simp [Z50]
theorem Qgb (n:ℕ) {p t a:ℝ}
    (hp:p∈Z6 0 1) (ht:t∈Z6 0 1) :
    (∑ k∈(Z5 (n+1)).filter (fun k:ℕ => a≤|(k:ℝ)-n*p|),Qaa n p k) ≤
      2*Z1 (-t*a+(n:ℝ)*t^2):=by
  have hpoint (k:ℕ):(if a≤|(k:ℝ)-n*p| then Qaa n p k else 0) ≤
      (if a≤(k:ℝ)-n*p then Qaa n p k else 0)+
      (if a≤-((k:ℝ)-n*p) then Qaa n p k else 0):=by
    have hn:=QaF n k hp
    by_cases h:a≤|(k:ℝ)-n*p|
    · rw [if_pos h]
      have hh:=le_abs.mp h
      rcases hh with h1 | h2
      · rw [if_pos h1]
        split_ifs <;> linarith
      · rw [if_pos h2]
        split_ifs <;> linarith
    · rw [if_neg h]
      split_ifs <;> linarith
  have hh:=Z7 (s:=Z5 (n+1)) (fun k _ => hpoint k)
  rw [Z14,← Z27,← Z27,← Z27] at hh
  have h1:=Qgk n (a:=a) hp ht (Or.inl rfl:(1:ℝ)=1 ∨ (1:ℝ)= -1)
  have h2:=Qgk n (a:=a) hp ht (Or.inr rfl:(-1:ℝ)=1 ∨ (-1:ℝ)= -1)
  simp only [one_mul,neg_one_mul] at h1 h2
  linarith
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem Qiu {ι:Type*} [Fintype ι] [DecidableEq ι]
    {e d:ι} (hed:e≠d) :
    Z10 (Qbc e d)=Z10 ι-2:=by
  classical
  have hset:(Finset.univ.filter (fun i:ι => i≠e ∧ i≠d)) = (Finset.univ.erase e).erase d:=by
    ext i
    simp [and_comm]
  rw [Z98,hset]
  rw [Finset.card_erase_of_mem (by simp [hed.symm]),
    Finset.card_erase_of_mem (Z21 e)]
  simp only [Z48]
  omega
theorem Qeg {ι:Type*} [Fintype ι] [DecidableEq ι]
    (A:Finset ι) (hA:A.Nonempty) (x:ι → ℝ) (hx:∀ i,0≤x i)
    {R:ℝ} (hR:R*Z10 ι ≤ ∑ i∈A,x i) :
    ∃ e∈A,R≤x e:=by
  obtain ⟨e,he,hm⟩:=A.exists_max_image x hA
  refine ⟨e,he,?_⟩
  have hc:(A.card:ℝ)≤Z10 ι:=by exact_mod_cast Finset.card_le_univ A
  have hcard:(0:ℝ)<Z10 ι:=by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨e⟩
  have hs:(∑ i∈A,x i) ≤ (Z10 ι:ℝ)*x e:=by
    calc
      _ ≤ ∑ _i∈A,x e:=Z7 (fun i hi => hm i hi)
      _ = (A.card:ℝ)*x e:=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right hc (hx e)
  nlinarith
theorem Qre {α ι:Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V:ℕ} (A:Finset ι)
    (p:α → ι → Fin (U+1)) (hp:Z28 p)
    (hA:∀ a,∑ i∈A,(p a i).val=L) (ht:∀ a,∑ i,(p a i).val=V)
    {R:ℝ} (hR:0<R)
    (hleft:∀ a,∃ e∈A,R≤(p a e).val)
    (hright:∀ a,∃ d∉A,R≤(p a d).val) :
    (∑ a,∏ i,(Z0 ((p a i).val:ℝ))⁻¹) ≤
      (Z10 ι:ℝ)^2*R⁻¹*(2*Z0 U)^(Z10 ι-2):=by
  classical
  choose e he heR using hleft
  choose d hd hdR using hright
  let f (a:α):=(e a,d a)
  let W (a:α):=∏ i,(Z0 ((p a i).val:ℝ))⁻¹
  have hfiber (z:ι × ι) :
      (∑ a:{a // f a=z},W a.val) ≤ R⁻¹*(2*Z0 U)^(Z10 ι-2):=by
    by_cases hne:Nonempty {a // f a=z}
    · obtain ⟨a⟩:=hne
      have ha:=congrArg Prod.fst a.property
      have ha':=congrArg Prod.snd a.property
      have hz1:z.1∈A:=by simpa only [f] using ha ▸ he a.val
      have hz2:z.2∉A:=by simpa only [f] using ha' ▸ hd a.val
      have hzd:z.1≠z.2:=by intro h; exact hz2 (h ▸ hz1)
      have hh:=Qrc A hz1 hz2
        (fun a:{a // f a=z} => p a.val) (hp.comp Subtype.val_injective)
        (fun a => hA a.val) (fun a => ht a.val) hR
        (fun a => by have h:=congrArg Prod.fst a.property; simpa only [f] using h ▸ heR a.val)
        (fun a => by have h:=congrArg Prod.snd a.property; simpa only [f] using h ▸ hdR a.val)
      simpa only [W,Qiu hzd] using hh
    · have:IsEmpty {a // f a=z}:=not_nonempty_iff.mp hne
      simp only [Fintype.sum_empty]
      positivity
  calc
    _ = ∑ z:ι × ι,∑ a:{a // f a=z},W a.val:=by
      exact (Fintype.sum_fiberwise f W).symm
    _ ≤ ∑ _z:ι × ι,R⁻¹*(2*Z0 U)^(Z10 ι-2) :=
      Z7 (fun z _ => hfiber z)
    _ = _:=by simp [pow_two,mul_assoc]
theorem QlG {u r:ℕ} (a:Fin r) (h:Fin u)
    (hleft:(u:ℝ)/3≤2*h.val+1)
    (hright:(u:ℝ)/3≤2*u-(2*h.val+1)) :
    (∑ j:Qbl u r a h,
      ∏ i,(Z0 (Qad j.val.val i))⁻¹) ≤
      ((r+1:ℕ):ℝ)^2 * ((u:ℝ)/(3*(r+1:ℝ)))⁻¹ *
        (2*Z0 (2*u:ℕ))^(r-1):=by
  classical
  have hu:(0:ℝ)<u:=by exact_mod_cast (Z91 h.isLt)
  let A:=Z31 a.castSucc
  let p:=Qcc a h
  have hR:0<(u:ℝ)/(3*(r+1:ℝ)):=by positivity
  have hL (j:Qbl u r a h) :
      ∃ e∈A,(u:ℝ)/(3*(r+1:ℝ))≤(p j e).val:=by
    apply Qeg A ⟨0,by simp [A]⟩ (fun i => (p j i).val)
      (fun _ => Z19 _)
    have hs:=Qdd a h j
    have hs':(∑ i∈A,((p j i).val:ℝ))=2*h.val+1:=by exact_mod_cast hs
    rw [hs']
    simp only [Z26,Z23,Z25]
    convert hleft using 1; field_simp
  have hD (j:Qbl u r a h) :
      ∃ d∉A,(u:ℝ)/(3*(r+1:ℝ))≤(p j d).val:=by
    have ha:a.val<r:=a.isLt
    have hlast:Z22 r∈Aᶜ:=by simp [A]
    obtain ⟨d,hd,hdR⟩:=Qeg Aᶜ ⟨Z22 r,hlast⟩
      (fun i => ((p j i).val:ℝ)) (fun _ => Z19 _) (R:=(u:ℝ)/(3*(r+1:ℝ))) (by
        have hs:=Qdd a h j
        have ht:=Qem a h j
        have hs':(∑ i∈A,((p j i).val:ℝ))=2*h.val+1:=by exact_mod_cast hs
        have ht':(∑ i,((p j i).val:ℝ))=2*u:=by exact_mod_cast ht
        have hc:=Finset.sum_compl_add_sum A (fun i => ((p j i).val:ℝ))
        have hsum:(∑ i∈Aᶜ,((p j i).val:ℝ))=2*u-(2*h.val+1):=by linarith
        rw [hsum]
        simp only [Z26,Z23,Z25]
        convert hright using 1; field_simp)
    exact ⟨d,Finset.mem_compl.mp hd,hdR⟩
  have hh:=Qre A p (QgW a h)
    (Qdd a h) (Qem a h) hR hL hD
  simpa only [p,Qcc,Fin.val_mk,Z26,show r+1-2=r-1 by omega] using hh
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem Qge (n U:ℕ) {p:ℝ} (hp:p∈Z6 0 1)
    (P:ℕ → Prop) [DecidablePred P] :
    (∑ k:Fin (U+1),if P k.val then Qaa n p k.val else 0) ≤
      ∑ k∈(Z5 (n+1)).filter P,Qaa n p k:=by
  rw [Z76 (fun k:ℕ => if P k then Qaa n p k else 0) (U+1),Z27]
  by_cases hU:U≤n
  · apply Z40 (Z90 (by omega))
    intro k _ _
    split_ifs
    · exact QaF n k hp
    · rfl
  · apply le_of_eq
    symm
    apply Z97 (Z90 (by omega))
    intro k _ hk
    have hnk:n<k:=by simp only [Z57] at hk; omega
    simp [Qaa,Z44 hnk]
theorem QoY {α ι κ:Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p:α → ι → κ) (hp:Z28 p)
    (w:ι → κ → ℝ) (hw:∀ i k,0≤w i k)
    (hs:∀ i,∑ k,w i k≤1) (e:ι) (P:κ → Prop) [DecidablePred P]
    {T:ℝ} (_hT:0≤T) (ht:(∑ k,if P k then w e k else 0)≤T) :
    (∑ a,if P (p a e) then ∏ i,w i (p a i) else 0) ≤ T:=by
  classical
  let w' (i:ι) (k:κ):=if i=e then (if P k then w i k else 0) else w i k
  have hw' (i k):0≤w' i k:=by
    dsimp [w']
    split_ifs
    · exact hw i k
    · exact le_rfl
    · exact hw i k
  have hprod (δ:ι → κ):(∏ i,w' i (δ i)) =
      if P (δ e) then ∏ i,w i (δ i) else 0:=by
    by_cases h:P (δ e)
    · rw [if_pos h]
      apply Z71 rfl
      intro i _
      by_cases hi:i=e
      · subst i; simp [w',h]
      · simp [w',hi]
    · rw [if_neg h]
      exact Z69 (Z21 e) (by simp [w',h])
  have hsum (i):(∑ k,w' i k)≤ if i=e then T else 1:=by
    by_cases hi:i=e
    · subst i; simpa only [w',ite_true] using ht
    · simpa only [w',if_neg hi] using hs i
  calc
    _ = ∑ a,∏ i,w' i (p a i):=by simp_rw [hprod]
    _ ≤ ∑ δ:ι → κ,∏ i,w' i (δ i):=by
      have hh:=QcP p hp (fun _ => True) (fun _ => trivial)
        (fun δ => ∏ i,w' i (δ i)) (fun δ => Z37 (fun i _ => hw' i (δ i)))
      simpa only [ite_true] using hh
    _ = ∏ i,∑ k,w' i k:=(Z43 _).symm
    _ ≤ ∏ i:ι,if i=e then T else 1 :=
      Z45 (fun i _ => Z11 (fun k _ => hw' i k)) (fun i _ => hsum i)
    _ = T:=by simp
theorem Qqq {n l r:ℕ} (hl:l≤n)
    (p:Fin r → Fin n) (hp:StrictMono p) (e:Fin (r+1))
    {θ t a:ℝ} (hθ:θ∈Z4 0 1) (ht:t∈Z6 0 1) :
    (∑ v:Qab l r,
      if a≤|(tupleGap v.val e:ℝ)-(tupleGap p e:ℝ)*θ|
      then Qaw hl p v.val else 0) ≤
      θ^r / Qaa n θ l *
        (2*Z1 (-t*a+(tupleGap p e:ℝ)*t^2)):=by
  classical
  have hθ':θ∈Z6 0 1:=⟨hθ.1.le,hθ.2.le⟩
  let prof:=QbS (n:=l) (r:=r) (Equiv.refl _)
  let w (i:Fin (r+1)) (k:Fin (l-r+1)):=Qaa (tupleGap p i) θ k.val
  have hw (i k):0≤w i k:=QaF _ _ hθ'
  have hs (i):(∑ k,w i k)≤1:=by
    have hh:=Qge (tupleGap p i) (l-r) hθ' (fun _ => True)
    simpa only [ite_true,Finset.filter_true,Qcg] using hh
  have ht':(∑ k:Fin (l-r+1),
      if a≤|(k.val:ℝ)-(tupleGap p e:ℝ)*θ| then w e k else 0) ≤
      2*Z1 (-t*a+(tupleGap p e:ℝ)*t^2):=by
    exact (Qge (tupleGap p e) (l-r) hθ'
      (fun k:ℕ => a≤|(k:ℝ)-(tupleGap p e:ℝ)*θ|)).trans
        (Qgb _ hθ' ht)
  have hh:=QoY prof (QfD _) w hw hs e
    (fun k => a≤|(k.val:ℝ)-(tupleGap p e:ℝ)*θ|) (by positivity) ht'
  have hfac:0≤θ^r / Qaa n θ l :=
    div_nonneg (pow_nonneg hθ.1.le _) (QaF _ _ hθ')
  calc
    _ = θ^r / Qaa n θ l *
        ∑ v:Qab l r,
          if a≤|(tupleGap v.val e:ℝ)-(tupleGap p e:ℝ)*θ|
          then ∏ i,Qaa (tupleGap p i) θ (tupleGap v.val i) else 0:=by
      rw [Z3]
      apply Z2 rfl
      intro v _
      split_ifs
      · exact Qex hl p hp v.val v.property θ hθ
      · simp
    _ ≤ _:=mul_le_mul_of_nonneg_left (by
      simpa only [prof,QbS,Equiv.refl_apply,w] using hh) hfac
theorem Qqr {n l r:ℕ} (hl:l≤n)
    (p:Fin r → Fin n) (hp:StrictMono p)
    {θ t a:ℝ} (hθ:θ∈Z4 0 1) (ht:t∈Z6 0 1) :
    (∑ v:Qab l r,
      if ∃ i,a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then Qaw hl p v.val else 0) ≤
      ((r+1:ℕ):ℝ)*θ^r / Qaa n θ l *
        (2*Z1 (-t*a+(n:ℝ)*t^2)):=by
  classical
  have hθ':θ∈Z6 0 1:=⟨hθ.1.le,hθ.2.le⟩
  have hpoint (v:Qab l r) :
      (if ∃ i,a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then Qaw hl p v.val else 0) ≤
      ∑ i,if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then Qaw hl p v.val else 0:=by
    have hn (i):0≤(if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then Qaw hl p v.val else 0):=by
      split_ifs
      · exact Qdw hl p v.val
      · rfl
    split_ifs with h
    · obtain ⟨e,he⟩:=h
      have hh:=Z82 (fun i _ => hn i) (Z21 e)
      simpa only [if_pos he] using hh
    · exact Z11 (fun i _ => hn i)
  calc
    _ ≤ ∑ v:Qab l r,∑ i,
        if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then Qaw hl p v.val else 0:=Z7 (fun v _ => hpoint v)
    _ = ∑ i,∑ v:Qab l r,
        if a≤|(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
        then Qaw hl p v.val else 0:=Z17
    _ ≤ ∑ _i:Fin (r+1),θ^r / Qaa n θ l *
        (2*Z1 (-t*a+(n:ℝ)*t^2)):=by
      apply Z7
      intro i _
      apply (Qqq hl p hp i hθ ht).trans
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (pow_nonneg hθ.1.le _) (QaF _ _ hθ'))
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hgap:tupleGap p i≤n:=(QiW ⟨p,hp⟩ i).trans (Nat.sub_le _ _)
      have hg:(tupleGap p i:ℝ)≤n:=by exact_mod_cast hgap
      have hh:=mul_le_mul_of_nonneg_right hg (sq_nonneg t)
      linarith
    _ = _:=by simp; ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem QmT (k:ℕ):(Z0 (k:ℝ))⁻¹≤1:=by
  by_cases hk:k=0
  · simp [hk]
  have hk':(1:ℝ)≤k:=by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
  have hs:1≤Z0 (k:ℝ):=by simpa using Z24 hk'
  exact (inv_le_one₀ (by positivity:0<Z0 (k:ℝ))).mpr hs
theorem Qlz (U M:ℕ) :
    (∑ k:Fin (U+1),if k.val≤M then (Z0 (k.val:ℝ))⁻¹ else 0) ≤ M+1:=by
  classical
  calc
    _ ≤ ∑ k:Fin (U+1),if k.val≤M then (1:ℝ) else 0:=by
      apply Z7
      intro k _
      split_ifs
      · exact QmT k.val
      · rfl
    _ = ((Finset.univ.filter (fun k:Fin (U+1) => k.val≤M)).card:ℝ):=by simp
    _ ≤ M+1:=by
      have hh:(Finset.univ.filter (fun k:Fin (U+1) => k.val≤M)).card≤M+1:=by
        rw [← Finset.card_range (M+1)]
        apply Finset.card_le_card_of_injOn Fin.val
          (fun k hk => by
            have hh:=(Finset.mem_filter.mp hk).2
            exact Finset.mem_range.mpr (Z72 hh))
        intro k _ j _ hkj; exact Z34 hkj
      exact_mod_cast hh
theorem QoW {ι:Type*} [Fintype ι] [DecidableEq ι]
    (e:ι) (A B:ℝ) :
    (∏ i:ι,if i=e then A else B)=A*B^(Z10 ι-1):=by
  rw [← Finset.mul_prod_erase Z16 (fun i => if i=e then A else B) (Z21 e)]
  simp only [ite_true]
  have hh:(∏ i∈Finset.univ.erase e,if i=e then A else B)=
      ∏ _i∈Finset.univ.erase e,B:=by
    apply Z71 rfl
    intro i hi
    exact if_neg (Finset.mem_erase.mp hi).1
  rw [hh]
  simp
theorem Qrb {α ι:Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V M:ℕ} (A:Finset ι) {e d c:ι} (he:e∈A) (hd:d∉A)
    (hce:c≠e) (hcd:c≠d)
    (p:α → ι → Fin (U+1)) (hp:Z28 p)
    (hA:∀ a,∑ i∈A,(p a i).val=L) (ht:∀ a,∑ i,(p a i).val=V)
    {R:ℝ} (hR:0<R) (heR:∀ a,R≤(p a e).val) (hdR:∀ a,R≤(p a d).val)
    (hcM:∀ a,(p a c).val≤M) :
    (∑ a,∏ i,(Z0 ((p a i).val:ℝ))⁻¹) ≤
      R⁻¹*(M+1)*(2*Z0 U)^(Z10 ι-3):=by
  classical
  have hed:e≠d:=by intro h; exact hd (h ▸ he)
  let c':Qbc e d:=⟨c,hce,hcd⟩
  let w (i:ι) (k:Fin (U+1)) :=
    if i=c then (if k.val≤M then (Z0 (k.val:ℝ))⁻¹ else 0)
    else (Z0 (k.val:ℝ))⁻¹
  have hw (i k):0≤w i k:=by dsimp [w]; split_ifs <;> positivity
  have hwP (a i):w i (p a i)=(Z0 ((p a i).val:ℝ))⁻¹:=by
    by_cases hi:i=c
    · subst i; simp only [w,ite_true,if_pos (hcM a)]
    · simp only [w,if_neg hi]
  have hwS (i:Qbc e d):(∑ k,w i.val k)≤
      if i=c' then (M+1:ℝ) else 2*Z0 U:=by
    by_cases hi:i=c'
    · subst i
      simpa only [c',w,ite_true] using Qlz U M
    · have hic:i.val≠c:=by intro h; apply hi; exact Subtype.ext h
      simpa only [w,if_neg hi,if_neg hic] using QgT U
  calc
    _ ≤ ∑ a,R⁻¹*∏ i:Qbc e d,w i.val (p a i.val):=by
      apply Z7
      intro a _
      simp_rw [hwP]
      rw [Qil hed]
      exact mul_le_mul_of_nonneg_right (Qhu hR (heR a) (hdR a)) (by positivity)
    _ = R⁻¹*∑ a,∏ i:Qbc e d,w i.val (p a i.val):=by rw [Z3]
    _ ≤ R⁻¹*∏ i:Qbc e d,∑ k,w i.val k :=
      mul_le_mul_of_nonneg_left (Qjd A he hd p hp hA ht w hw) (inv_nonneg.mpr hR.le)
    _ ≤ R⁻¹*∏ i:Qbc e d,if i=c' then (M+1:ℝ) else 2*Z0 U:=by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      exact Z45 (fun i _ => Z11 (fun k _ => hw i.val k)) (fun i _ => hwS i)
    _ = _:=by
      rw [QoW,Qiu hed]
      simp only [Nat.sub_sub]
      ring
theorem Qrd {α ι:Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {U L V M:ℕ} (A:Finset ι) (c:ι)
    (p:α → ι → Fin (U+1)) (hp:Z28 p)
    (hA:∀ a,∑ i∈A,(p a i).val=L) (ht:∀ a,∑ i,(p a i).val=V)
    {R:ℝ} (hR:0<R) (hMR:(M:ℝ)<R)
    (hleft:∀ a,∃ e∈A,R≤(p a e).val)
    (hright:∀ a,∃ d∉A,R≤(p a d).val)
    (hcM:∀ a,(p a c).val≤M) :
    (∑ a,∏ i,(Z0 ((p a i).val:ℝ))⁻¹) ≤
      (Z10 ι:ℝ)^2*R⁻¹*(M+1)*(2*Z0 U)^(Z10 ι-3):=by
  classical
  choose e he heR using hleft
  choose d hd hdR using hright
  let f (a:α):=(e a,d a)
  let W (a:α):=∏ i,(Z0 ((p a i).val:ℝ))⁻¹
  have hfiber (z:ι × ι) :
      (∑ a:{a // f a=z},W a.val) ≤ R⁻¹*(M+1)*(2*Z0 U)^(Z10 ι-3):=by
    by_cases hne:Nonempty {a // f a=z}
    · obtain ⟨a⟩:=hne
      have ha:=congrArg Prod.fst a.property
      have ha':=congrArg Prod.snd a.property
      have hz1:z.1∈A:=by simpa only [f] using ha ▸ he a.val
      have hz2:z.2∉A:=by simpa only [f] using ha' ▸ hd a.val
      have hzR:R≤(p a.val z.1).val:=by simpa only [f] using ha ▸ heR a.val
      have hzR':R≤(p a.val z.2).val:=by simpa only [f] using ha' ▸ hdR a.val
      have hc:((p a.val c).val:ℝ)≤M:=by exact_mod_cast hcM a.val
      have hce:c≠z.1:=by intro h; rw [h] at hc; linarith
      have hcd:c≠z.2:=by intro h; rw [h] at hc; linarith
      exact Qrb A hz1 hz2 hce hcd
        (fun a:{a // f a=z} => p a.val) (hp.comp Subtype.val_injective)
        (fun a => hA a.val) (fun a => ht a.val) hR
        (fun a => by have h:=congrArg Prod.fst a.property; simpa only [f] using h ▸ heR a.val)
        (fun a => by have h:=congrArg Prod.snd a.property; simpa only [f] using h ▸ hdR a.val)
        (fun a => hcM a.val)
    · have:IsEmpty {a // f a=z}:=not_nonempty_iff.mp hne
      simp only [Fintype.sum_empty]
      positivity
  calc
    _ = ∑ z:ι × ι,∑ a:{a // f a=z},W a.val:=(Fintype.sum_fiberwise f W).symm
    _ ≤ ∑ _z:ι × ι,R⁻¹*(M+1)*(2*Z0 U)^(Z10 ι-3) :=
      Z7 (fun z _ => hfiber z)
    _ = _:=by simp [pow_two,mul_assoc]
end TraceReconstruction
noncomputable section
open scoped Classical
namespace TraceReconstruction
def QaQ {u l r:ℕ} (m:ℕ) (θ:ℝ)
    (j:Qab u r) (v:Qab l r):Prop :=
  ∀ i:Fin r,|(tupleGap v.val i.castSucc:ℝ)-
    θ*m*(Qad j.val i.castSucc:ℝ)/2| < (m:ℝ)/8
theorem QnH {x y:ℕ} {z θ m:ℝ}
    (hθ:1 / 2 ≤ θ) (hm:0 < m)
    (hx:|z - θ * m * x / 2| < m / 8) (hy:|z - θ * m * y / 2| < m / 8):x = y:=by
  have hx':=abs_lt.mp hx
  have hy':=abs_lt.mp hy
  have hscale:m / 4 ≤ θ * m / 2:=by nlinarith
  by_contra hxy
  obtain h | h:=lt_or_gt_of_ne hxy
  · have h':(x:ℝ)+1≤y:=by exact_mod_cast h
    have hh:=mul_le_mul_of_nonneg_left h' (by positivity:0 ≤ θ * m / 2)
    nlinarith
  · have h':(y:ℝ)+1≤x:=by exact_mod_cast h
    have hh:=mul_le_mul_of_nonneg_left h' (by positivity:0 ≤ θ * m / 2)
    nlinarith
theorem Qoi {u l r m:ℕ} (hm:0 < m) {θ:ℝ} (hθ:1 / 2 ≤ θ)
    {j k:Qab u r} {v:Qab l r}
    (hj:QaQ m θ j v) (hk:QaQ m θ k v):j=k:=by
  apply Subtype.ext
  by_cases hr:r=0
  · subst r; exact Subsingleton.elim _ _
  have hg (i:Fin r):Qad j.val i.castSucc=Qad k.val i.castSucc :=
    QnH hθ (by exact_mod_cast hm) (hj i) (hk i)
  have hsum:=Qda (Nat.pos_of_ne_zero hr) j.val j.property
  have hsum':=Qda (Nat.pos_of_ne_zero hr) k.val k.property
  have hgSum:(∑ i:Fin r,Qad j.val i.castSucc)=
      ∑ i:Fin r,Qad k.val i.castSucc:=Z2 rfl (fun i _ => hg i)
  rw [Fin.sum_univ_castSucc] at hsum hsum'
  have hlast:Qad j.val (Z22 r)=Qad k.val (Z22 r):=by omega
  apply QeT j.property k.property
  funext i
  refine Z60 hlast (fun i => hg i) i
theorem QkY {α β:Type*} [Fintype α] [Fintype β]
    (f:α → β → ℝ) (hf:∀ a b,a≠b → ∀ v,f a v*f b v=0) :
    (∑ v,(∑ a,f a v)^2) = ∑ a,∑ v,f a v^2:=by
  classical
  have hp (v):(∑ a,f a v)^2=∑ a,f a v^2:=by
    rw [pow_two,Z33]
    apply Z2 rfl
    intro a _
    rw [Z3]
    rw [Z86 a]
    · ring
    · intro b _ hba
      exact hf a b hba.symm v
    · intro ha
      exact False.elim (ha (Z21 a))
  simp_rw [hp]
  exact Z17
theorem Qia {u l r m:ℕ} (hm:0 < m) {θ:ℝ} (hθ:1 / 2 ≤ θ)
    (W:Qab u r → Qab l r → ℝ)
    (a:Qab u r → ℝ) :
    (∑ v,(∑ j,if QaQ m θ j v then a j*W j v else 0)^2) ≤
      ∑ j,a j^2*∑ v,W j v^2:=by
  classical
  rw [QkY _ (by
    intro j k hjk v
    by_cases hj:QaQ m θ j v
    · have hk:¬QaQ m θ k v:=fun hk => hjk (Qoi hm hθ hj hk)
      simp only [if_pos hj,if_neg hk,mul_zero]
    · simp only [if_neg hj,zero_mul])]
  apply Z7
  intro j _
  rw [Z3]
  apply Z7
  intro v _
  split_ifs
  · exact le_of_eq (mul_pow _ _ _)
  · simp only [zero_pow (by norm_num:2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
instance:Fintype Qac :=
  ⟨{.unchanged,.first,.second},by intro k; cases k <;> simp⟩
theorem Qqw (f:Qac → ℝ) :
    (∑ k,f k)=f .unchanged+f .first+f .second:=by
  change (∑ k ∈ ({.unchanged,.first,.second}:Finset Qac),f k)=_
  simp [Z87]; ring
def motifShift (χ β τ:ℝ):Fin 3 :=
  if χ=0 then 1 else if β*τ=1 then 2 else 0
def Qbb (χ β τ:ℝ):Qac → ℝ
  | .unchanged => 1 | .first => τ*β | .second => χ
theorem Qnv {χ β τ:ℝ} (hβ:QcT χ β)
    (hτ:IsTypeSign τ) (a:Fin 3) :
    (∑ k,Qbb χ β τ k * Qbx k a)=
      if a=motifShift χ β τ then 1 else 0:=by
  rw [Qqw]
  rcases hβ with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;>
  rcases hτ with rfl | rfl <;> fin_cases a <;>
    norm_num [Qbb,motifShift,Qbx,Fin.ext_iff]
theorem QoX {ι κ:Type*} [Fintype ι] [DecidableEq κ]
    (a b:ι → κ) :
    (∏ i,if a i=b i then (1:ℝ) else 0)=if a=b then 1 else 0:=by
  classical
  by_cases h:a=b
  · subst a; simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩:=Function.ne_iff.mp h
    exact Z69 (Z21 i) (if_neg hi)
theorem QhM {r:ℕ} (χ β:Fin r → ℝ) (τ:ℝ)
    (hβ:∀ h,QcT (χ h) (β h)) (hτ:IsTypeSign τ)
    (W:(Fin r → Fin 3) → ℝ) :
    W (fun h => motifShift (χ h) (β h) τ)=
      ∑ k:Fin r → Qac,
        (∏ h,Qbb (χ h) (β h) τ (k h))*
        (∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h))*W a):=by
  classical
  symm
  simp_rw [Z3]
  rw [Z17]
  calc
    _ = ∑ a,(∑ k:Fin r → Qac,
        ∏ h,Qbb (χ h) (β h) τ (k h)*Qbx (k h) (a h))*W a:=by
      apply Z2 rfl
      intro a _
      rw [Z33]
      apply Z2 rfl
      intro k _
      rw [Z30]
      ring
    _ = ∑ a,(∏ h,if a h=motifShift (χ h) (β h) τ then (1:ℝ) else 0)*W a:=by
      apply Z2 rfl
      intro a _
      rw [← Z43 (fun h k => Qbb (χ h) (β h) τ k * Qbx k (a h))]
      simp_rw [Qnv (hβ _) hτ]
    _ = _:=by simp_rw [QoX]; simp
def Qax {r:ℕ} (k:Fin r → Qac):ℕ :=
  (Finset.univ.filter fun h => k h = .first).card
def QdV {r:ℕ} (k:Fin r → Qac):ℕ :=
  (Finset.univ.filter fun h => k h = .second).card
theorem QhJ {r:ℕ} (χ β:Fin r → ℝ) (τ:ℝ)
    (k:Fin r → Qac) :
    (∏ h,Qbb (χ h) (β h) τ (k h))=
      τ^Qax k *∏ h,Qbb (χ h) (β h) 1 (k h):=by
  classical
  have hw (h):Qbb (χ h) (β h) τ (k h)=
      (if k h=.first then τ else 1)*Qbb (χ h) (β h) 1 (k h):=by
    cases k h <;> simp [Qbb]
  simp_rw [hw]
  rw [Z30]
  congr 1
  rw [← Finset.prod_filter]
  simp [Qax]
theorem Qnw {r:ℕ} (χ β:Fin r → ℝ)
    (hβ:∀ h,QcT (χ h) (β h)) (W:(Fin r → Fin 3) → ℝ) :
    W (fun h => motifShift (χ h) (β h) 1)-
      W (fun h => motifShift (χ h) (β h) (-1))=
      ∑ k:Fin r → Qac,
        (if Odd (Qax k) then
          2*∏ h,Qbb (χ h) (β h) 1 (k h) else 0)*
        (∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h))*W a):=by
  rw [QhM χ β 1 hβ (Or.inl rfl) W,
    QhM χ β (-1) hβ (Or.inr rfl) W,← Z39]
  apply Z2 rfl
  intro k _
  rw [QhJ χ β 1 k,QhJ χ β (-1) k]
  rw [QpI (Or.inr rfl:IsTypeSign (-1))]
  simp only [one_pow,one_mul]
  split_ifs <;> ring
theorem QgF {r:ℕ} (k:Fin r → Qac) :
    (∑ h,(k h).order)=Qax k+2*QdV k:=by
  classical
  have hd (h):(k h).order=(if k h=.first then 1 else 0)+
      2*(if k h=.second then 1 else 0):=by cases k h <;> simp [Qac.order]
  simp_rw [hd]
  rw [Z14,← Z3]
  simp [Qax,QdV]
theorem QnN {r:ℕ} (k:Fin r → Qac)
    (hk:Odd (Qax k)) :
    (Qax k=1 ∧ QdV k=0) ∨
      3≤∑ h,(k h).order:=by
  rw [QgF]
  obtain ⟨n,hn⟩:=hk
  omega
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem QpF {r:ℕ} (a:Fin r → Fin 3) (i:Fin (r+1)) :
    QbV a i  ≤  2*QaH r i:=by
  have hl:Z15 (α:=fun _ =>  ℕ) 0 (fun h =>  2-(a h).val) i  ≤ 
      2*Z15 (α:=fun _ =>  ℕ) 0 (fun _:Fin r =>  1) i:=by
    induction i using Z38 with
    | zero =>  simp
    | succ i =>  simp
  have hr:Fin.snoc (α:=fun _ =>  ℕ) (fun h =>  (a h).val) 0 i  ≤ 
      2*Fin.snoc (α:=fun _ =>  ℕ) (fun _:Fin r =>  1) 0 i:=by
    induction i using Z60 with
    | last =>  simp
    | cast i =>  simpa using Z63 (a i).isLt
  dsimp [QbV,QaH]
  omega
theorem QqO {n r:ℕ} (p:Fin r → Fin n)
    (hp:Qae p) (a:Fin r → Fin 3) (i:Fin (r+1)) :
    |(tupleGap (shiftedTag p hp a) i:ℝ)-(tupleGap p i:ℝ)| ≤ 2:=by
  rw [QiX,Z23,Z47 (Qha p hp i)]
  have hi:(QaH r i:ℝ) ≤ 2:=by exact_mod_cast Qhb r i
  have he:(QbV a i:ℝ) ≤ 2*(QaH r i:ℝ):=by exact_mod_cast QpF a i
  have h0:(0:ℝ) ≤ QbV a i:=by positivity
  apply abs_le.mpr
  constructor  <;>  linarith
theorem Qox {u m r:ℕ} (hr:0 < r)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j:Qab u r) (hsafe:Qae (periodSlot off ∘ j.val))
    (a:Fin r → Fin 3) (i:Fin (r+1)) :
    |(tupleGap (shiftedTag (periodSlot off ∘ j.val) hsafe a) i:ℝ)-
      (m:ℝ)*Qad j.val i/2| ≤ 6:=by
  have ht:=abs_sub_le (tupleGap (shiftedTag (periodSlot off ∘ j.val) hsafe a) i:ℝ)
    (tupleGap (periodSlot off ∘ j.val) i:ℝ) ((m:ℝ)*Qad j.val i/2)
  have h1:=QqO (periodSlot off ∘ j.val) hsafe a i
  have h2:=Qfx hr off hoff hdiff j.val j.property i
  linarith
theorem Qku {z g c θ m:ℝ}
    (hθ:θ ∈ Z6 0 1) (hm:128 ≤ m) (hg:|g-m*c/2| ≤ 6)
    (hz:m/8 ≤ |z-θ*m*c/2|):m/16 ≤ |z-g*θ|:=by
  have he:|g*θ-θ*m*c/2| ≤ 6:=by
    have h:=mul_le_mul_of_nonneg_right hg hθ.1
    rw [show g*θ-θ*m*c/2=(g-m*c/2)*θ by ring,abs_mul,abs_of_nonneg hθ.1]
    exact h.trans (by nlinarith [hθ.2])
  have ht:=abs_sub_le z (g*θ) (θ*m*c/2)
  linarith
theorem Qoy {u m l r:ℕ}
    (hu:0 < u) (hm:128 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (j:Qab u r) (hsafe:Qae (periodSlot off ∘ j.val))
    (a:Fin r → Fin 3) {θ:ℝ} (hθ:θ ∈ Z4 0 1) :
    (∑ v:Qab l r,
      if QaQ m θ j v then 0 else
        Qaw hl (shiftedTag (periodSlot off ∘ j.val) hsafe a) v.val)  ≤ 
      ((r+1:ℕ):ℝ)*θ^r /Qaa (u*m) θ l *
        (2*Z1 (-(m:ℝ)/(1024*u))):=by
  let p:=shiftedTag (periodSlot off ∘ j.val) hsafe a
  have hu':(0:ℝ) < u:=by exact_mod_cast hu
  have ht:(1/(32*(u:ℝ))) ∈ Z6 0 1:=by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      have:(1:ℝ) ≤ u:=by exact_mod_cast hu
      linarith
  have hx:-(1/(32*(u:ℝ)))*((m:ℝ)/16)+((u*m:ℕ):ℝ)*(1/(32*(u:ℝ)))^2 =
      -(m:ℝ)/(1024*u):=by push_cast; field_simp; ring
  calc
    _  ≤  ∑ v:Qab l r,
      if ∃ i,(m:ℝ)/16 ≤ |(tupleGap v.val i:ℝ)-(tupleGap p i:ℝ)*θ|
      then Qaw hl p v.val else 0:=by
      apply Z7
      intro v _
      by_cases hv:QaQ m θ j v
      · simp only [if_pos hv]
        split_ifs
        · exact Qdw hl p v.val
        · rfl
      · simp only [QaQ,not_forall,not_lt] at hv
        obtain ⟨i,hi⟩:=hv
        have he:∃ i',(m:ℝ)/16 ≤ |(tupleGap v.val i':ℝ)-(tupleGap p i':ℝ)*θ| :=
          ⟨i.castSucc,Qku ⟨hθ.1.le,hθ.2.le⟩
            (by exact_mod_cast hm) (Qox hr off hoff hdiff j hsafe a i.castSucc) hi⟩
        rw [if_pos he]
        split_ifs
        · exact Qdw hl p v.val
        · rfl
    _  ≤  _:=by
      have hh:=Qqr hl p (QfF _ hsafe a) hθ ht (a:=(m:ℝ)/16)
      simpa only [hx] using hh
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QaT (s:ℕ) (z:ℤ):ℝ :=
  if 0 ≤ z ∧ z < (2^s:ℕ) then 1 else 0
theorem Qeu (s:ℕ) (z:ℤ) :
    QcT (QaT s z) ((Qak s).coeff z):=by
  by_cases hz:0 ≤ z ∧ z < (2^s:ℕ)
  · right
    refine ⟨by simp only [QaT,if_pos hz],?_⟩
    have hv:=(QdT s).2 z hz.1 hz.2
    exact (abs_eq (by norm_num:(0:ℝ) ≤ 1)).mp hv
  · left
    refine ⟨by simp only [QaT,if_neg hz],?_⟩
    apply (QdT s).1 z
    omega
theorem Qny (χ β:ℝ) (h:QcT χ β) (k:Qac) :
    |Qbb χ β 1 k| ≤ 1:=by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;> cases k <;>
    norm_num [Qbb]
theorem QhN (χ β:ℝ) (h:QcT χ β)
    (k:Qac) (hk:k ≠ .unchanged) :
    |Qbb χ β 1 k| ≤ χ:=by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl | rfl⟩ <;> cases k <;>
    norm_num [Qbb] at *
def Qbo {r:ℕ} (π:IntSeries) (s:ℕ)
    (j:Fin r → ℤ) (k:Fin r → Qac):ℝ :=
  ∑ X ∈ π.coeff.support,π.coeff X *
    ∏ h,Qbb (QaT s (j h-X))
      ((Qak s).coeff (j h-X)) 1 (k h)
def QaM {r:ℕ} (h:Fin r) (a:Fin r):Qac :=
  if a=h then .first else .unchanged
theorem Qnq {r:ℕ} (π:IntSeries) (s:ℕ)
    (j:Fin r → ℤ) (h:Fin r) :
    Qbo π s j (QaM h)=
      (Qak s * π).coeff (j h):=by
  classical
  rw [mul_comm,Z79,Finsupp.sum]
  apply Z2 rfl
  intro X _
  congr 1
  have hw (a:Fin r):Qbb (QaT s (j a-X))
      ((Qak s).coeff (j a-X)) 1 (QaM h a)=
      if a=h then (Qak s).coeff (j h-X) else 1:=by
    by_cases ha:a=h <;> simp [QaM,ha,Qbb]
  simp_rw [hw]
  simp [sub_eq_neg_add]
theorem Qnk {r:ℕ} (π:IntSeries)
    (hπ:∀ X,0 ≤ π.coeff X) (s:ℕ) (j:Fin r → ℤ)
    (k:Fin r → Qac) (h:Fin r) (hk:k h ≠ .unchanged) :
    |Qbo π s j k| ≤
      ∑ X ∈ π.coeff.support,π.coeff X*QaT s (j h-X):=by
  classical
  apply (Z70 _ _).trans
  apply Z7
  intro X _
  rw [abs_mul,abs_of_nonneg (hπ X),Finset.abs_prod]
  apply mul_le_mul_of_nonneg_left _ (hπ X)
  have hi (a):=Qny _ _ (Qeu s (j a-X)) (k a)
  have hh:=QhN _ _ (Qeu s (j h-X)) (k h) hk
  calc
    _ ≤ ∏ a:Fin r,if a=h then QaT s (j h-X) else 1:=by
      apply Z45
      · intro a _; positivity
      · intro a _
        by_cases ha:a=h
        · subst a; simpa using hh
        · simpa [ha] using hi a
    _ = _:=by simp
theorem Qns {r:ℕ} (π:IntSeries) (s:ℕ)
    (j:Fin r → ℤ) (k:Fin r → Qac)
    (hm:Qbo π s j k ≠ 0) :
    ∃ X ∈ π.coeff.support,∀ h,k h ≠ .unchanged →
      0 ≤ j h-X ∧ j h-X < (2^s:ℕ):=by
  classical
  obtain ⟨X,hX,hv⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨X,hX,?_⟩
  intro h hk
  by_contra hh
  apply hv
  apply mul_eq_zero_of_right
  apply Z69 (Z21 h)
  have hi:QaT s (j h-X)=0:=by simp only [QaT,if_neg hh]
  have hw:=QhN _ _ (Qeu s (j h-X)) (k h) hk
  exact abs_nonpos_iff.mp (hw.trans_eq hi)
theorem Qnr {r:ℕ} (π:IntSeries) (s:ℕ)
    (j:Fin r → ℤ) (k:Fin r → Qac)
    (hm:Qbo π s j k ≠ 0)
    (a b:Fin r) (ha:k a ≠ .unchanged) (hb:k b ≠ .unchanged) :
    |j a-j b| < (2^s:ℕ):=by
  obtain ⟨X,_,hX⟩:=Qns π s j k hm
  have h1:=hX a ha
  have h2:=hX b hb
  exact abs_lt.mpr ⟨by omega,by omega⟩
theorem Qnh {r:ℕ} (π:IntSeries) (s:ℕ)
    (j:Fin r → ℤ) (W:(Fin r → Fin 3) → ℝ) :
    (∑ X ∈ π.coeff.support,π.coeff X *
      (W (fun h => motifShift (QaT s (j h-X)) ((Qak s).coeff (j h-X)) 1)-
       W (fun h => motifShift (QaT s (j h-X)) ((Qak s).coeff (j h-X)) (-1))))=
      ∑ k:Fin r → Qac,
        (if Odd (Qax k) then 2*Qbo π s j k else 0)*
        (∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h))*W a):=by
  calc
    _ = ∑ X ∈ π.coeff.support,∑ k:Fin r → Qac,
        π.coeff X*((if Odd (Qax k) then
          2*∏ h,Qbb (QaT s (j h-X))
            ((Qak s).coeff (j h-X)) 1 (k h) else 0)*
          (∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h))*W a)):=by
      apply Z2 rfl
      intro X _
      rw [Qnw _ _ (fun h => Qeu s (j h-X)) W,
        Z3]
    _ = _:=by
      rw [Z17]
      apply Z2 rfl
      intro k _
      by_cases hk:Odd (Qax k)
      · simp only [if_pos hk,Qbo]
        calc
          _ = (∑ X ∈ π.coeff.support,2*(π.coeff X *
                ∏ h,Qbb (QaT s (j h-X))
                  ((Qak s).coeff (j h-X)) 1 (k h))) *
              (∑ a:Fin r → Fin 3,(∏ h,Qbx (k h) (a h))*W a):=by
            rw [Z33]
            apply Z2 rfl
            intro X _; ring
          _ = _:=by rw [← Z3]
      · simp only [if_neg hk,zero_mul,mul_zero,Z102]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qje {α β:Type*} [Fintype α] [Fintype β]
    (f:α → β) (a:α → ℝ) (w:β → ℝ) (P:α → ℝ) (C:ℝ)
    (hP:∀ x,0 ≤ P x) (ha:∀ x,a x^2 ≤ w (f x)^2)
    (hC:∀ y,w y ≠ 0 → (∑ x:{x // f x=y},P x.val) ≤ C) :
    (∑ x,a x^2*P x) ≤ C*∑ y,w y^2:=by
  classical
  calc
    _ ≤ ∑ x,w (f x)^2*P x :=
      Z7 fun x _ => mul_le_mul_of_nonneg_right (ha x) (hP x)
    _ = ∑ y,w y^2*∑ x:{x // f x=y},P x.val:=by
      rw [← Fintype.sum_fiberwise f (fun x => w (f x)^2*P x)]
      apply Z2 rfl
      intro y _
      rw [Z3]
      apply Z2 rfl
      intro x _
      rw [x.property]
    _ ≤ ∑ y,w y^2*C:=by
      apply Z7
      intro y _
      by_cases hy:w y=0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (hC y hy) (sq_nonneg _)
    _ = _:=by rw [← Z33]; ring
def Qbs (u r:ℕ):ℝ :=
  ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(2*Z0 (2*u:ℕ))^(r-1)
theorem Qrk {u r:ℕ} (a:Fin r)
    (A:Qab u r → ℝ) (w:Fin u → ℝ)
    (hA:∀ j,A j^2 ≤ w (j.val a)^2)
    (hw:∀ h,w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) :
    (∑ j:Qab u r,A j^2*∏ i,(Z0 (Qad j.val i))⁻¹) ≤
      Qbs u r *∑ h,w h^2:=by
  apply Qje (fun j:Qab u r => j.val a) A w
    (fun j => ∏ i,(Z0 (Qad j.val i))⁻¹)
    (Qbs u r) (fun _ => by positivity) hA
  intro h hh
  calc
    _ = ∑ j:Qbl u r a h,
        ∏ i,(Z0 (Qad j.val.val i))⁻¹ :=
      by
        congr 1
        exact congrArg (fun i:Fintype (Qbl u r a h) => @Z16 _ i)
          (Subsingleton.elim _ _)
    _ ≤ _:=QlG a h (hw h hh).1 (hw h hh).2
theorem QgX {u r:ℕ} (a:Fin r) (h:Fin u)
    (hleft:(u:ℝ)/3 ≤ 2*h.val+1)
    (hright:(u:ℝ)/3 ≤ 2*u-(2*h.val+1)) (j:Qbl u r a h) :
    (∃ e ∈ Z31 a.castSucc,(u:ℝ)/(3*(r+1:ℝ)) ≤ (Qcc a h j e).val) ∧
    (∃ d ∉ Z31 a.castSucc,(u:ℝ)/(3*(r+1:ℝ)) ≤ (Qcc a h j d).val):=by
  classical
  let A:=Z31 a.castSucc
  let p:=Qcc a h
  have hL:∃ e∈A,(u:ℝ)/(3*(r+1:ℝ)) ≤ (p j e).val:=by
    apply Qeg A ⟨0,by simp [A]⟩ (fun i => (p j i).val)
      (fun _ => Z19 _)
    have hs:=Qdd a h j
    have hs':(∑ i∈A,((p j i).val:ℝ))=2*h.val+1:=by exact_mod_cast hs
    rw [hs']
    simp only [Z26,Z23,Z25]
    convert hleft using 1; field_simp
  have hD:∃ d∉A,(u:ℝ)/(3*(r+1:ℝ)) ≤ (p j d).val:=by
    have ha:a.val<r:=a.isLt
    have hlast:Z22 r∈Aᶜ:=by simp [A]
    obtain ⟨d,hd,hdR⟩:=Qeg Aᶜ ⟨Z22 r,hlast⟩
      (fun i => ((p j i).val:ℝ)) (fun _ => Z19 _) (R:=(u:ℝ)/(3*(r+1:ℝ))) (by
        have hs:=Qdd a h j
        have ht:=Qem a h j
        have hs':(∑ i∈A,((p j i).val:ℝ))=2*h.val+1:=by exact_mod_cast hs
        have ht':(∑ i,((p j i).val:ℝ))=2*u:=by exact_mod_cast ht
        have hc:=Finset.sum_compl_add_sum A (fun i => ((p j i).val:ℝ))
        have hsum:(∑ i∈Aᶜ,((p j i).val:ℝ))=2*u-(2*h.val+1):=by linarith
        rw [hsum]
        simp only [Z26,Z23,Z25]
        convert hright using 1; field_simp)
    exact ⟨d,Finset.mem_compl.mp hd,hdR⟩
  exact ⟨hL,hD⟩
theorem QlF {u r M:ℕ} (a:Fin r) (h:Fin u)
    (c:Fin (r+1)) (hleft:(u:ℝ)/3 ≤ 2*h.val+1)
    (hright:(u:ℝ)/3 ≤ 2*u-(2*h.val+1)) (hM:(M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ j:Qbl u r a h,
      if Qad j.val.val c ≤ M then ∏ i,(Z0 (Qad j.val.val i))⁻¹ else 0) ≤
      ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(M+1)*(2*Z0 (2*u:ℕ))^(r-2):=by
  classical
  let α:={j:Qbl u r a h // Qad j.val.val c ≤ M}
  let p (j:α):=Qcc a h j.val
  have hu:(0:ℝ) < u:=by exact_mod_cast (Z91 h.isLt)
  have hR:0 < (u:ℝ)/(3*(r+1:ℝ)):=by positivity
  have hs:=Qrd (Z31 a.castSucc) c p
    ((QgW a h).comp Subtype.val_injective)
    (fun j => Qdd a h j.val)
    (fun j => Qem a h j.val) hR hM
    (fun j => (QgX a h hleft hright j.val).1)
    (fun j => (QgX a h hleft hright j.val).2)
    (fun j => j.property)
  have he:(∑ j:Qbl u r a h,
      if Qad j.val.val c ≤ M then ∏ i,(Z0 (Qad j.val.val i))⁻¹ else 0)=
      ∑ j:α,∏ i,(Z0 (Qad j.val.val.val i))⁻¹:=by
    rw [← Z27]
    exact Finset.sum_subtype _ (by intro j; simp) _
  rw [he]
  simpa only [α,p,Qcc,Fin.val_mk,Z26,
    show r+1-3=r-2 by omega] using hs
def QbE (u r M:ℕ):ℝ :=
  ((r+1:ℕ):ℝ)^2*((u:ℝ)/(3*(r+1:ℝ)))⁻¹*(M+1)*(2*Z0 (2*u:ℕ))^(r-2)
theorem Qrj {u r M:ℕ} (a:Fin r) (c:Fin (r+1))
    (A:Qab u r → ℝ) (w:Fin u → ℝ)
    (hA:∀ j,A j^2 ≤ w (j.val a)^2)
    (hsupport:∀ j,A j ≠ 0 → Qad j.val c ≤ M)
    (hw:∀ h,w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1))
    (hM:(M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ j:Qab u r,A j^2*∏ i,(Z0 (Qad j.val i))⁻¹) ≤
      QbE u r M *∑ h,w h^2:=by
  have hp (j:Qab u r) :
      A j^2*(∏ i,(Z0 (Qad j.val i))⁻¹)=
      A j^2*(if Qad j.val c ≤ M then ∏ i,(Z0 (Qad j.val i))⁻¹ else 0):=by
    by_cases hj:A j=0
    · simp [hj]
    · rw [if_pos (hsupport j hj)]
  simp_rw [hp]
  apply Qje (fun j:Qab u r => j.val a) A w
    (fun j => if Qad j.val c ≤ M then ∏ i,(Z0 (Qad j.val i))⁻¹ else 0)
    (QbE u r M) (fun _ => by split_ifs <;> positivity) hA
  intro h hh
  calc
    _ = ∑ j:Qbl u r a h,
        if Qad j.val.val c ≤ M then ∏ i,(Z0 (Qad j.val.val i))⁻¹ else 0 :=
      by
        congr 1
        exact congrArg (fun i:Fintype (Qbl u r a h) => @Z16 _ i)
          (Subsingleton.elim _ _)
    _ ≤ _:=QlF a h c (hw h hh).1 (hw h hh).2 hM
end TraceReconstruction
namespace TraceReconstruction
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open FiniteLaw
theorem Qlf {n l u r:ℕ}
    (d:Fin u → Fin n) (hd:StrictMono d) (v:Qab l r)
    (S:QaG (Fin n) l)
    (h:∀ i,slotAtRank S (v.val i) ∈ Set.range d) :
    ∃! j:Qab u r,Qcq (d ∘ j.val) v.val S:=by
  classical
  choose j hj using h
  have hm:StrictMono j:=by
    intro a b hab
    apply hd.lt_iff_lt.mp
    rw [hj a,hj b]
    exact Qqc S (v.property hab)
  refine ⟨⟨j,hm⟩,?_,?_⟩
  · intro i
    exact (hj i).symm
  · intro k hk
    apply Subtype.ext
    funext i
    apply hd.injective
    exact (hk i).symm.trans (hj i).symm
theorem QkQ {n l u r:ℕ}
    (d:Fin u → Fin n) (hd:StrictMono d) (v:Qab l r)
    (S:QaG (Fin n) l) :
    (if ∀ i,slotAtRank S (v.val i) ∈ Set.range d then (1:ℝ) else 0) =
      ∑ j:Qab u r,if Qcq (d ∘ j.val) v.val S then 1 else 0:=by
  classical
  by_cases h:∀ i,slotAtRank S (v.val i) ∈ Set.range d
  · obtain ⟨j,hj,hu⟩:=Qlf d hd v S h
    rw [if_pos h]
    symm
    rw [Z86 j]
    · exact if_pos hj
    · intro k _ hkj
      have hk:¬Qcq (d ∘ k.val) v.val S:=by
        intro hk
        exact hkj (hu k hk)
      exact if_neg hk
    · simp
  · rw [if_neg h]
    symm
    apply Z81
    intro j _
    apply if_neg
    intro hj
    apply h
    intro i
    exact ⟨j.val i,(hj i).symm⟩
def Qdr {n l u r:ℕ} (hl:l ≤ n) (d:Fin u → Fin n)
    (v:Qab l r):ℝ:=by
  classical
  exact (QaO l (by simpa using hl)).expect (fun S =>
    if ∀ i,slotAtRank S (v.val i) ∈ Set.range d then 1 else 0)
theorem QfC {n l u r:ℕ} (hl:l ≤ n)
    (d:Fin u → Fin n) (hd:StrictMono d) (v:Qab l r) :
    Qdr hl d v =
      ∑ j:Qab u r,Qaw hl (d ∘ j.val) v.val:=by
  classical
  unfold Qdr FiniteLaw.expect Qaw
  simp_rw [QkQ d hd v,Z3]
  rw [Z17]
  apply Z2 rfl
  intro j _
  apply Z2 rfl
  intro S _
  split_ifs <;> simp
theorem Qps {n l:ℕ} (D:Finset (Fin n))
    (S:QaG (Fin n) l) (σ:Fin l → Bool) :
    Qdt (QaY D S) σ =
      if ∀ i,σ i = true → slotAtRank S i ∈ D then (1:ℝ) else 0:=by
  classical
  unfold Qdt QaY
  by_cases h:∀ i,σ i = true → slotAtRank S i ∈ D
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i _
    cases hs:σ i
    · simp
    · simp [h i hs]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i,hi,hni⟩:=h
    apply Z69 (Z21 i)
    simp [hi,hni]
def rankMask {l r:ℕ} (v:Qab l r):Fin l → Bool :=
  fun i => decide (i ∈ Set.range v.val)
theorem QeI {n l u r:ℕ} (hl:l ≤ n)
    (d:Fin u → Fin n) (v:Qab l r) :
    Qbm (QaO l (by simpa using hl))
      (QaY (Finset.univ.image d)) (rankMask v) =
      Qdr hl d v:=by
  classical
  unfold Qbm Qdr FiniteLaw.expect
  apply Z2 rfl
  intro S _
  congr 1
  dsimp only
  rw [Qps]
  congr 1
  simp only [rankMask,decide_eq_true_eq,Finset.mem_image,Z21,true_and,
    Set.mem_range]
  apply propext
  constructor
  · intro h i
    exact h (v.val i) ⟨i,rfl⟩
  · rintro h i ⟨j,rfl⟩
    exact h j
end TraceReconstruction
namespace TraceReconstruction
open FiniteLaw
def QeE {l r:ℕ} (σ:Fin l → Bool) (hσ:Qap σ = r) :
    Qab l r:=by
  classical
  let S:Finset (Fin l):=Finset.univ.filter (fun i => σ i = true)
  have hS:S.card = r:=hσ
  exact ⟨fun i => ((S.orderIsoOfFin hS) i).val,(S.orderIsoOfFin hS).strictMono⟩
theorem Qit {l r:ℕ} (σ:Fin l → Bool) (hσ:Qap σ = r) :
    rankMask (QeE σ hσ) = σ:=by
  classical
  funext i
  have he:i ∈ Set.range (QeE σ hσ).val ↔ σ i = true:=by
    constructor
    · rintro ⟨j,rfl⟩
      exact (Finset.mem_filter.mp (((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ) j).property).2
    · intro hi
      let z:↥(Finset.univ.filter (fun k => σ k = true)):=⟨i,by simp [hi]⟩
      refine ⟨((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ).symm z,?_⟩
      exact congrArg Subtype.val (((Finset.univ.filter (fun k => σ k = true)).orderIsoOfFin hσ).apply_symm_apply z)
  simp only [rankMask,he]
  exact Bool.decide_eq_true
theorem QqT {l r:ℕ}:Z28
    (fun σ:{σ:Fin l → Bool // Qap σ = r} => QeE σ.val σ.property):=by
  intro σ τ h
  apply Subtype.ext
  have he:=congrArg rankMask h
  simpa only [Qit] using he
theorem QfL {l r:ℕ} (A:(Fin l → Bool) → ℝ) :
    (∑ σ:Fin l → Bool,if Qap σ = r then A σ ^ 2 else 0) ≤
      ∑ v:Qab l r,A (rankMask v)^2:=by
  classical
  rw [← Z27]
  have he:(∑ σ ∈ Finset.univ.filter (fun σ:Fin l → Bool => Qap σ = r),A σ ^ 2) =
      ∑ σ:{σ:Fin l → Bool // Qap σ = r},A σ.val ^ 2:=by
    exact Finset.sum_subtype _ (by intro σ; simp) _
  rw [he]
  have h:=QcP
    (fun σ:{σ:Fin l → Bool // Qap σ = r} => QeE σ.val σ.property)
    QqT (fun _ => True) (fun _ => True.intro)
    (fun v => A (rankMask v)^2) (fun _ => sq_nonneg _)
  simpa only [Qit,ite_true] using h
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open FiniteLaw
theorem QnE {α:Type*} [Fintype α] (P:FiniteLaw α)
    (Z:α → ℝ) (hcenter:P.expect Z = 0) (R:ℝ)
    (hvar:P.expect (fun a => Z a^2) = R^2) (n:ℕ)
    (A:(Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => Qaj A Z x ^ 2) =
      QaK A R:=by
  induction n with
  | zero => simp [FiniteLaw.expect,FiniteLaw.product,Qaj,QaK]
  | succ n ih =>
    rw [Qim]
    simp_rw [QhR]
    have he (x:Fin n → α) :
        P.expect (fun a => (Qaj (fun σ => A (Z15 false σ)) Z x +
            Z a * Qaj (fun σ => A (Z15 true σ)) Z x)^2) =
          Qaj (fun σ => A (Z15 false σ)) Z x ^ 2 +
            R^2 * Qaj (fun σ => A (Z15 true σ)) Z x ^ 2:=by
      have hp (a:α) :
          P.mass a * (Qaj (fun σ => A (Z15 false σ)) Z x +
            Z a * Qaj (fun σ => A (Z15 true σ)) Z x)^2 =
          P.mass a * (Qaj (fun σ => A (Z15 false σ)) Z x)^2 +
            2 * Qaj (fun σ => A (Z15 false σ)) Z x *
              Qaj (fun σ => A (Z15 true σ)) Z x * (P.mass a * Z a) +
            (Qaj (fun σ => A (Z15 true σ)) Z x)^2 * (P.mass a * Z a^2):=by ring
      unfold FiniteLaw.expect
      simp_rw [hp,Z14,← Z33,← Z3]
      simp only [FiniteLaw.expect] at hcenter hvar
      rw [P.total,hcenter,hvar]
      ring
    simp_rw [he]
    rw [QhO]
    have hadd (f g:(Fin n → α) → ℝ) :
        (P.product n).expect (fun x => f x + R^2*g x) =
          (P.product n).expect f + R^2*(P.product n).expect g:=by
      unfold FiniteLaw.expect
      simp_rw [mul_add,Z14]
      rw [Z3]
      congr 1
      apply Z2 rfl
      intro x _
      ring
    rw [hadd,ih,ih]
theorem FiniteLaw.Qjo {α:Type*} [Fintype α] [Preorder α]
    (P:FiniteLaw α) (htotal:∀ a b:α,a ≤ b ∨ b ≤ a):P.Associated:=by
  intro f g hf hg
  have hn (a b:α):0 ≤ (f a - f b) * (g a - g b):=by
    rcases htotal a b with hab | hba
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hab))
        (sub_nonpos.mpr (hg hab))
    · exact mul_nonneg (sub_nonneg.mpr (hf hba)) (sub_nonneg.mpr (hg hba))
  have h:=Z11 (s:=Z16) (fun a _ =>
    Z11 (s:=Z16) (fun b _ => mul_nonneg (mul_nonneg (P.nonneg a)
      (P.nonneg b)) (hn a b)))
  have hid:(∑ a,∑ b,P.mass a * P.mass b * ((f a - f b) * (g a - g b))) =
      2 * (P.expect (fun a => f a * g a) - P.expect f * P.expect g):=by
    have hp (a b:α):P.mass a * P.mass b * ((f a - f b) * (g a - g b)) =
        (P.mass a * (f a * g a)) * P.mass b + P.mass a * (P.mass b * (f b * g b)) -
        (P.mass a * f a) * (P.mass b * g b) - (P.mass a * g a) * (P.mass b * f b):=by ring
    simp_rw [hp,Z39,Z14,
      ← Z3,← Z33,P.total,one_mul,mul_one]
    unfold FiniteLaw.expect
    ring
  rw [hid] at h
  linarith
theorem Qec {α Ω:Type*} [Fintype Ω] {n:ℕ}
    (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool) (Z:α → ℝ)
    (hZ:∀ a,0 ≤ 1+Z a) (x:Fin n → α) :
    0 ≤ QaX R θ Z x:=by
  apply Z11
  intro ω _
  apply mul_nonneg (R.nonneg ω)
  apply Z37
  intro i _
  split_ifs
  · exact hZ _
  · norm_num
theorem QfV {α Ω:Type*} [Preorder α] [Fintype Ω] {n:ℕ}
    (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool) (Z:α → ℝ)
    (hZ:∀ a,0 ≤ 1+Z a) (hZm:Monotone Z) :
    Monotone (QaX R θ Z):=by
  intro x y hxy
  apply R.QaZ
  intro ω
  apply Z45
  · intro i _
    split_ifs
    · exact hZ _
    · norm_num
  · intro i _
    split_ifs
    · linarith [hZm (hxy i)]
    · rfl
theorem Qpv {α:Type*} [Fintype α] (P:FiniteLaw α)
    (Z:α → ℝ) (hZ:P.expect Z = 0) {n:ℕ} (θ:Fin n → Bool) :
    (P.product n).expect (Qce θ Z) = 1:=by
  unfold FiniteLaw.expect FiniteLaw.product Qce
  simp_rw [← Z30]
  rw [← Z43 (fun (i:Fin n) (a:α) => P.mass a * (if θ i then 1+Z a else 1))]
  apply Finset.prod_eq_one
  intro i _
  cases θ i
  · simp only [Bool.false_eq_true,↓reduceIte,mul_one,P.total]
  · simp only [↓reduceIte,mul_add,mul_one,Z14,P.total]
    exact add_eq_left.mpr hZ
theorem QfU {α Ω:Type*} [Fintype α] [Fintype Ω]
    (P:FiniteLaw α) (R:FiniteLaw Ω) (Z:α → ℝ) (hZ:P.expect Z = 0)
    {n:ℕ} (θ:Ω → Fin n → Bool) :
    (P.product n).expect (QaX R θ Z) = 1:=by
  unfold QaX FiniteLaw.expect
  simp_rw [Z3]
  rw [Z17]
  have he (ω:Ω):(∑ x:Fin n → α,(P.product n).mass x * (R.mass ω * Qce (θ ω) Z x)) =
      R.mass ω * (P.product n).expect (Qce (θ ω) Z):=by
    rw [FiniteLaw.expect,Z3]
    apply Z2 rfl
    intro x _
    ring
  simp_rw [he,Qpv P Z hZ,mul_one]
  exact R.total
end TraceReconstruction
namespace TraceReconstruction
open FiniteLaw
theorem QhP {n:ℕ} (A:(Fin n → Bool) → ℝ) (R:ℝ) :
    QaK A R = ∑ r ∈ Z5 (n+1),
      R^(2*r) * ∑ σ:Fin n → Bool,if Qap σ = r then A σ^2 else 0:=by
  classical
  unfold QaK
  simp_rw [Qni]
  simp_rw [Z3]
  rw [Z17]
  apply Z2 rfl
  intro σ _
  have hd:Qap σ < n+1:=by
    have h:=Finset.card_filter_le (s:=Z16) (p:=fun i:Fin n => σ i = true)
    simpa [Qap] using Z72 h
  rw [Z86 (Qap σ)]
  · simp [mul_comm]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp [Z57,hd]
theorem Qfp {n:ℕ} (σ:Fin n → Bool) :
    Qap σ = 0 ↔ σ = fun _ => false:=by
  classical
  constructor
  · intro h
    have he:Finset.univ.filter (fun i => σ i = true) = ∅:=Finset.card_eq_zero.mp h
    funext i
    have hn:σ i ≠ true:=by
      intro hi
      have:i ∈ Finset.univ.filter (fun j => σ j = true):=by simp [hi]
      rw [he] at this
      exact Finset.notMem_empty i this
    exact Bool.eq_false_iff.mpr hn
  · rintro rfl
    simp [Qap]
theorem Qjq {Ω:Type*} [Fintype Ω] {n:ℕ}
    (R:FiniteLaw Ω) (θ:Ω → Fin n → Bool) :
    (∑ σ:Fin n → Bool,if Qap σ = 0 then Qbm R θ σ ^ 2 else 0) = 1:=by
  classical
  simp_rw [Qfp]
  simp [QfS]
theorem Qmd {n r:ℕ} (h:n < r):IsEmpty (Qab n r):=by
  refine ⟨fun v => ?_⟩
  have hc:=Fintype.card_le_of_injective v.val v.property.injective
  simp only [Z26] at hc
  omega
theorem QgB {n l u r:ℕ} (hl:l ≤ n)
    (d:Fin u → Fin n) (hd:StrictMono d) (hru:u < r) :
    (∑ σ:Fin l → Bool,if Qap σ = r then
      Qbm (QaO l (by simpa using hl))
        (QaY (Finset.univ.image d)) σ ^ 2 else 0) = 0:=by
  classical
  apply le_antisymm
  · refine (QfL (r:=r) (Qbm (QaO l (by simpa using hl))
        (QaY (Finset.univ.image d)))).trans ?_
    simp_rw [QeI hl d,QfC hl d hd]
    have:=Qmd hru
    simp
  · apply Z11
    intro σ _
    split_ifs <;> positivity
theorem Qib {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hru:r ≤ u) (hm:32 ≤ m) (hum:u ≤ m) {δ θ:ℝ}
    (hδ:δ ∈ Z12 0 (1/2:ℝ))
    (hθ:θ ∈ Z6 (1-δ^2) (1-δ^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2) :
    (∑ σ:Fin l → Bool,if Qap σ = r then
      Qbm (QaO l (by simpa using hl))
        (QaY (Finset.univ.image (periodSlot off))) σ ^ 2 else 0) ≤
      ((3*Qau/δ)*Z0 ((u:ℝ)/((m:ℝ)*r)))^r:=by
  refine (QfL (r:=r) (Qbm (QaO l (by simpa using hl))
    (QaY (Finset.univ.image (periodSlot off))))).trans ?_
  simp_rw [QeI hl (periodSlot off),
    QfC hl (periodSlot off) (QdO off)]
  exact Qov hl hr hru hm hum hδ hθ hmean hv off hoff hdiff
theorem Qon {u m l:ℕ} (hl:l ≤ u*m)
    (hm:32 ≤ m) (hum:u ≤ m) {δ θ:ℝ}
    (hδ:δ ∈ Z12 0 (1/2:ℝ))
    (hθ:θ ∈ Z6 (1-δ^2) (1-δ^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2) (R:ℝ) :
    QaK
      (Qbm (QaO l (by simpa using hl))
        (QaY (Finset.univ.image (periodSlot off)))) R ≤
      ∑ r ∈ Z5 (l+1),
        (R^2*(3*Qau/δ)*Z0 ((u:ℝ)/m))^r / (Z0 (r:ℝ))^r:=by
  rw [QhP]
  apply Z7
  intro r _
  by_cases hr:r = 0
  · subst r
    rw [Qjq]
    norm_num
  · by_cases hru:r ≤ u
    · have hr0:0 < r:=Nat.pos_of_ne_zero hr
      have hb:=Qib hl hr0 hru hm hum hδ hθ hmean hv off hoff hdiff
      calc
        _ ≤ R^(2*r)*((3*Qau/δ)*Z0 ((u:ℝ)/((m:ℝ)*r)))^r :=
          mul_le_mul_of_nonneg_left hb (by rw [pow_mul]; positivity)
        _ = _:=by
          have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
          have hr0:(0:ℝ) < r:=by exact_mod_cast hr0
          rw [show (u:ℝ)/((m:ℝ)*r)=((u:ℝ)/m)/r by field_simp]
          rw [Real.sqrt_div (by positivity),pow_mul,← mul_pow,← div_pow]
          congr 1
          ring
    · rw [QgB hl (periodSlot off) (QdO off) (by omega),mul_zero]
      have:=hδ.1
      positivity [Qcd]
theorem QkS (a:ℝ) (N:ℕ) :
    (∑ r ∈ Z5 N,a^r / (Z0 (r:ℝ))^r) ≤ 2*Z1 (a^2):=by
  have hb:=QkR a N
  have hp:=Z74 (a^2)
  have he:Z1 (2*a^2) = (Z1 (a^2))^2:=by
    rw [show 2*a^2=a^2+a^2 by ring,Z50]
    ring
  rw [he] at hb
  nlinarith [sq_nonneg ((∑ r ∈ Z5 N,a^r / (Z0 (r:ℝ))^r)+2*Z1 (a^2))]
theorem Qoo {α:Type*} [Fintype α]
    (P:FiniteLaw α) (Z:α → ℝ) (hZ:P.expect Z = 0)
    {u m l:ℕ} (hl:l ≤ u*m)
    (hm:32 ≤ m) (hum:u ≤ m) {δ θ:ℝ}
    (hδ:δ ∈ Z12 0 (1/2:ℝ))
    (hθ:θ ∈ Z6 (1-δ^2) (1-δ^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2) :
    (P.product l).expect (fun x =>
      QaX (QaO l (by simpa using hl))
        (QaY (Finset.univ.image (periodSlot off))) Z x ^ 2) ≤
      2*Z1 ((P.expect (fun a => Z a^2))^2 * (3*Qau/δ)^2 * ((u:ℝ)/m)):=by
  have hv0:0 ≤ P.expect (fun a => Z a^2) :=
    Z11 (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  simp_rw [QfT]
  rw [QnE P Z hZ (Z0 (P.expect (fun a => Z a^2)))
    (Z13 hv0).symm]
  refine (Qon hl hm hum hδ hθ hmean hv off hoff hdiff _).trans ?_
  apply (QkS _ (l+1)).trans
  rw [Z13 hv0]
  have he:(P.expect (fun a => Z a^2)*(3*Qau/δ)*Z0 ((u:ℝ)/m))^2 =
      (P.expect (fun a => Z a^2))^2*(3*Qau/δ)^2*((u:ℝ)/m):=by
    rw [mul_pow,mul_pow,Z13 (by positivity)]
  rw [he]
theorem Qjp {α Ω Ψ:Type*}
    [Fintype α] [Fintype Ω] [Fintype Ψ]
    (P:FiniteLaw α) (R:FiniteLaw Ω) (S:FiniteLaw Ψ)
    (Z:α → ℝ) (hZ:P.expect Z = 0) (hZpos:∀ a,0 ≤ 1+Z a)
    {l:ℕ} (f:Ω → Fin l → Bool) (g:Ψ → Fin l → Bool) :
    (1:ℝ)/32 ≤
      (P.product l).expect (fun x => min (QaX R f Z x) (QaX S g Z x)) *
      (P.product l).expect (fun x => QaX R f Z x ^ 2) *
      (P.product l).expect (fun x => QaX S g Z x ^ 2):=by
  let:Preorder α:=Preorder.lift Z
  have htotal:∀ a b:α,a ≤ b ∨ b ≤ a:=fun a b => le_total (Z a) (Z b)
  have hm:Monotone Z:=fun _ _ h => h
  exact Qme (P.product l)
    (Qjn P (P.Qjo htotal) l)
    (QaX R f Z) (QaX S g Z)
    (Qec R f Z hZpos) (Qec S g Z hZpos)
    (QfV R f Z hZpos hm) (QfV S g Z hZpos hm)
    (QfU P R Z hZ f) (QfU P S Z hZ g)
end TraceReconstruction
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem QiA {α:Type*} [Fintype α] (f:IntSeries)
    (j:α → ℤ) (hj:Z28 j) :
    (∑ a,f.coeff (j a)^2) ≤ seriesL2Sq f:=by
  classical
  let A:=Finset.univ.image j
  have he:(∑ a,f.coeff (j a)^2)=∑ z∈A,f.coeff z^2:=by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => hj h
  rw [he]
  calc
    _ ≤ ∑ z∈f.coeff.support ∪ A,f.coeff z^2 :=
      Z40 Finset.subset_union_right (fun _ _ _ => sq_nonneg _)
    _ = _:=by
      rw [QpA]
      symm
      apply Z97 Finset.subset_union_left
      intro z _ hz
      simp [Finsupp.notMem_support_iff.mp hz]
theorem Qot {u m l r:ℕ}
    (hm:32 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (hsafe:∀ j:Qab u r,Qae (periodSlot off ∘ j.val))
    (k:Fin r → Qac) {θ:ℝ} (hθ:θ ∈ Z4 0 1)
    (hhalf:1/2 ≤ θ) (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (a:Fin r) (A:Qab u r → ℝ) (w:Fin u → ℝ)
    (hA:∀ j,A j^2 ≤ w (j.val a)^2)
    (hw:∀ h,w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1)) :
    (∑ v,(∑ j,if QaQ m θ j v then
      A j*QbF hl (periodSlot off ∘ j.val) (hsafe j) k v else 0)^2) ≤
      QaW u m r (∑ h,(k h).order) θ *
        Qbs u r * ∑ h,w h^2:=by
  have hC:0 ≤ QaW u m r (∑ h,(k h).order) θ:=by
    unfold QaW QaJ
    positivity
  calc
    _ ≤ ∑ j,A j^2*∑ v,QbF hl (periodSlot off ∘ j.val) (hsafe j) k v^2 :=
      Qia (by omega) hhalf _ A
    _ ≤ ∑ j,A j^2*(QaW u m r (∑ h,(k h).order) θ *
        ∏ i,(Z0 (Qad j.val i))⁻¹):=by
      apply Z7
      intro j _
      exact mul_le_mul_of_nonneg_left
        (Qic hm hr hl off hoff hdiff j (hsafe j) k hθ hmean hv)
        (sq_nonneg _)
    _ = QaW u m r (∑ h,(k h).order) θ *
        ∑ j,A j^2*∏ i,(Z0 (Qad j.val i))⁻¹:=by
      rw [Z3]; congr 1; funext j; ring
    _ ≤ _:=by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Qrk a A w hA hw) hC
theorem Qos {u m l r M:ℕ}
    (hm:32 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (hsafe:∀ j:Qab u r,Qae (periodSlot off ∘ j.val))
    (k:Fin r → Qac) {θ:ℝ} (hθ:θ ∈ Z4 0 1)
    (hhalf:1/2 ≤ θ) (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (a:Fin r) (c:Fin (r+1)) (A:Qab u r → ℝ) (w:Fin u → ℝ)
    (hA:∀ j,A j^2 ≤ w (j.val a)^2)
    (hsupport:∀ j,A j ≠ 0 → Qad j.val c ≤ M)
    (hw:∀ h,w h ≠ 0 → (u:ℝ)/3 ≤ 2*h.val+1 ∧ (u:ℝ)/3 ≤ 2*u-(2*h.val+1))
    (hM:(M:ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑ v,(∑ j,if QaQ m θ j v then
      A j*QbF hl (periodSlot off ∘ j.val) (hsafe j) k v else 0)^2) ≤
      QaW u m r (∑ h,(k h).order) θ *
        QbE u r M * ∑ h,w h^2:=by
  have hC:0 ≤ QaW u m r (∑ h,(k h).order) θ:=by
    unfold QaW QaJ
    positivity
  calc
    _ ≤ ∑ j,A j^2*∑ v,QbF hl (periodSlot off ∘ j.val) (hsafe j) k v^2 :=
      Qia (by omega) hhalf _ A
    _ ≤ ∑ j,A j^2*(QaW u m r (∑ h,(k h).order) θ *
        ∏ i,(Z0 (Qad j.val i))⁻¹):=by
      apply Z7
      intro j _
      exact mul_le_mul_of_nonneg_left
        (Qic hm hr hl off hoff hdiff j (hsafe j) k hθ hmean hv)
        (sq_nonneg _)
    _ = QaW u m r (∑ h,(k h).order) θ *
        ∑ j,A j^2*∏ i,(Z0 (Qad j.val i))⁻¹:=by
      rw [Z3]; congr 1; funext j; ring
    _ ≤ _:=by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Qrj a c A w hA hsupport hw hM) hC
theorem Qnt {u r:ℕ} (π:IntSeries) (s:ℕ)
    (j:Qab u (r+1)) (k:Fin (r+1) → Qac)
    (i:Fin r) (b:Fin (r+1)) (hib:i.castSucc < b)
    (hi:k i.castSucc ≠ .unchanged) (hb:k b ≠ .unchanged)
    (hA:Qbo π s (fun a => (j.val a).val) k ≠ 0) :
    Qad j.val i.castSucc.succ ≤ 2*(2^s):=by
  have hs:=Qnr π s (fun a => (j.val a).val) k hA i.castSucc b hi hb
  have hj1:=j.property (show i.castSucc < i.succ by exact Fin.castSucc_lt_succ)
  have hj2:=j.property.monotone (show i.succ ≤ b by simpa only [Fin.le_iff_val_le_val,Fin.lt_def,
    Fin.val_succ,Fin.val_castSucc] using (Z68 hib))
  have h1:(j.val i.castSucc).val < (j.val i.succ).val:=hj1
  have h2:(j.val i.succ).val ≤ (j.val b).val:=hj2
  have hh:=(abs_lt.mp hs).1
  rw [Qgr]
  omega
end TraceReconstruction
namespace TraceReconstruction
def Qal (w:List Bool) (n:ℕ):List Bool :=
  (List.replicate n w).flatten
theorem Qpg (w:List Bool) (n m:ℕ) :
    Qal w (n+m)=Qal w n ++ Qal w m:=by
  simp only [Qal,List.replicate_add,List.flatten_append]
theorem Qph (w:List Bool) (ns:List ℕ) :
    (ns.map (Qal w)).flatten=Qal w ns.sum:=by
  induction ns with
  | nil => simp [Qal]
  | cons n ns ih => simp [ih,Qpg]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α:Type*} [Fintype α]
def Qba (d:Option Bool):FiniteLaw Bool where
  mass b:=match d with
    | none => 1/2
    | some c => if b=c then 1 else 0
  nonneg:=by
    intro b
    cases d with
    | none => norm_num
    | some c => dsimp; split_ifs <;> norm_num
  total:=by cases d with
    | none => norm_num [Z62]
    | some c => simp
def QbR (P Q H:FiniteLaw α) (ω:ℝ)
    (z:Option Bool × (α × α)):ℝ :=
  ∑ b:Bool,(1/2:ℝ)*Qbr P Q H ω b z
theorem QnW (P Q H:FiniteLaw α) (ω:ℝ)
    (z:Option Bool × (α × α)) (b:Bool) :
    (1/2:ℝ)*Qbr P Q H ω b z =
      QbR P Q H ω z * (Qba z.1).mass b:=by
  rcases z with ⟨d,z⟩
  cases d with
  | none => simp [QbR,Qbr,Qba]; ring
  | some c => cases b <;> cases c <;>
      simp [QbR,Qbr,Qba]
theorem Qob (P Q H:FiniteLaw α) {ω:ℝ} (hω:0 ≤ ω)
    (hP:∀ a,ω*H.mass a ≤ P.mass a) (hQ:∀ a,ω*H.mass a ≤ Q.mass a)
    (z:Option Bool × (α × α)):0 ≤ QbR P Q H ω z:=by
  apply Z11
  intro b _
  exact mul_nonneg (by norm_num) (QhW P Q H hω hP hQ b z)
theorem Qoc (P Q H:FiniteLaw α) (ω:ℝ) :
    (∑ z,QbR P Q H ω z)=1:=by
  unfold QbR
  rw [Z17]
  simp_rw [← Z3,QhX]
  norm_num [Z62]
def Qdp (P Q H:FiniteLaw α) {ω:ℝ} (hω:0 ≤ ω)
    (hP:∀ a,ω*H.mass a ≤ P.mass a) (hQ:∀ a,ω*H.mass a ≤ Q.mass a) :
    FiniteLaw (Option Bool × (α × α)) :=
  ⟨QbR P Q H ω,Qob P Q H hω hP hQ,
    Qoc P Q H ω⟩
theorem QnY {ι:Type*} [Fintype ι]
    (P Q H:ι → FiniteLaw α) (ω:ι → ℝ)
    (z:ι → Option Bool × (α × α)) (b:ι → Bool) :
    (∏ i,(1/2:ℝ)*Qbr (P i) (Q i) (H i) (ω i) (b i) (z i)) =
      (∏ i,QbR (P i) (Q i) (H i) (ω i) (z i)) *
        ∏ i,(Qba (z i).1).mass (b i):=by
  simp_rw [QnW]
  exact Z30
end TraceReconstruction.FiniteLaw
noncomputable section
namespace TraceReconstruction
open scoped Classical
def bitIndex (b:Bool):ℕ:=if b then 1 else 0
def QdR (d:Option Bool):IntSeries :=
  ∑ b:Bool,Z29 (bitIndex b:ℤ) ((FiniteLaw.Qba d).mass b)
def QbM (d:Option Bool):ℕ:=if d=some true then 1 else 0
def Qat (d:Option Bool):ℕ:=if d=none then 1 else 0
theorem QoG (d:Option Bool) :
    QdR d = Z29 (QbM d:ℤ) 1 * fairSeries (Qat d):=by
  cases d with
  | none => simp [QdR,FiniteLaw.Qba,bitIndex,QbM,Qat,fairSeries,
      add_comm]
  | some b => cases b <;> simp [QdR,FiniteLaw.Qba,bitIndex,QbM,Qat,
      fairSeries]
theorem QoJ {ι:Type*} [Fintype ι] (d:ι → Option Bool) :
    (∑ b:ι → Bool,Z29 (∑ i,(bitIndex (b i):ℤ))
      (∏ i,(FiniteLaw.Qba (d i)).mass (b i))) =
      Z29 (∑ i,(QbM (d i):ℤ)) 1 *
        fairSeries (∑ i,Qat (d i)):=by
  have he:(∑ b:ι → Bool,Z29 (∑ i,(bitIndex (b i):ℤ))
      (∏ i,(FiniteLaw.Qba (d i)).mass (b i))) = ∏ i,QdR (d i):=by
    rw [show (∏ i,QdR (d i)) =
      ∏ i,∑ b:Bool,Z29 (bitIndex b:ℤ) ((FiniteLaw.Qba (d i)).mass b) from rfl]
    rw [Z43]
    apply Z2 rfl
    intro b _
    rw [AddMonoidAlgebra.prod_single]
  rw [he]
  simp_rw [QoG]
  rw [Z30,AddMonoidAlgebra.prod_single]
  simp only [Finset.prod_const_one]
  congr 1
  unfold fairSeries
  exact Z99 _ _ _
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qhe (k:ℕ) (z:ℤ) :
    (geomSeries k).coeff z = if 0 ≤ z ∧ z < k then 1 else 0:=by
  unfold geomSeries
  simp only [Z80,one_pow,nsmul_eq_mul,mul_one,
    Z58,Z73,Z41,Z42]
  by_cases hz:0 ≤ z ∧ z < k
  · obtain ⟨a,rfl⟩:=Int.eq_ofNat_of_zero_le hz.1
    rw [if_pos hz,Z86 a]
    · simp
    · intro b _ hb
      exact if_neg (by exact_mod_cast hb)
    · intro ha
      have ha':a < k:=by exact_mod_cast hz.2
      exact (ha (Finset.mem_range.mpr ha')).elim
  · rw [if_neg hz]
    apply Z81
    intro a ha
    apply if_neg
    intro haz
    subst z
    exact hz ⟨by positivity,by exact_mod_cast Finset.mem_range.mp ha⟩
theorem Qnx (π:IntSeries) (s:ℕ) (z:ℤ) :
    (∑ X ∈ π.coeff.support,π.coeff X*QaT s (z-X)) =
      (geomSeries (2^s)*π).coeff z:=by
  rw [mul_comm,Z79,Finsupp.sum]
  apply Z2 rfl
  intro X _
  rw [Qhe]
  simp only [QaT,sub_eq_neg_add]
theorem Qnl {r:ℕ} (π:IntSeries)
    (hπ:∀ X,0 ≤ π.coeff X) (s:ℕ) (j:Fin r → ℤ)
    (k:Fin r → Qac) (h:Fin r) (hk:k h ≠ .unchanged) :
    (Qbo π s j k)^2 ≤ ((geomSeries (2^s)*π).coeff (j h))^2:=by
  have ha:=Qnk π hπ s j k h hk
  rw [Qnx] at ha
  have hh:=pow_le_pow_left₀ (abs_nonneg (Qbo π s j k)) ha 2
  simpa only [sq_abs] using hh
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
theorem Qjr {t p:ℝ} (ht:t ∈ Z4 0 1) (hp:p ∈ Z4 0 1) :
    t*Z8 (t/p)+(1-t)*Z8 ((1-t)/(1-p)) ≤
      (t-p)^2/(p*(1-p)):=by
  have h1:=mul_le_mul_of_nonneg_left (Z96 (div_pos ht.1 hp.1)) ht.1.le
  have h2:=mul_le_mul_of_nonneg_left
    (Z96 (div_pos (sub_pos.mpr ht.2) (sub_pos.mpr hp.2)))
    (sub_nonneg.mpr ht.2.le)
  have hid:t*(t/p-1)+(1-t)*((1-t)/(1-p)-1)=(t-p)^2/(p*(1-p)):=by
    field_simp [hp.1.ne',(sub_pos.mpr hp.2).ne']
    ring
  linarith
theorem QjK (n l:ℕ) {t p:ℝ}
    (ht:t ∈ Z4 0 1) (hp:p ∈ Z4 0 1) :
    Qaa n p l = Qaa n t l *
      Z1 (-((l:ℝ)*Z8 (t/p)+((n-l:ℕ):ℝ)*Z8 ((1-t)/(1-p)))):=by
  have h1:Z1 (-((l:ℝ)*Z8 (t/p)))=(p/t)^l:=by
    rw [show -((l:ℝ)*Z8 (t/p))=(l:ℝ)*Z8 (p/t) by
      rw [Real.log_div ht.1.ne' hp.1.ne',Real.log_div hp.1.ne' ht.1.ne']; ring,
      Z75,Real.exp_log (div_pos hp.1 ht.1)]
  have h2:Z1 (-(((n-l:ℕ):ℝ)*Z8 ((1-t)/(1-p))))=((1-p)/(1-t))^(n-l):=by
    rw [show -(((n-l:ℕ):ℝ)*Z8 ((1-t)/(1-p)))=
      ((n-l:ℕ):ℝ)*Z8 ((1-p)/(1-t)) by
      rw [Real.log_div (sub_pos.mpr ht.2).ne' (sub_pos.mpr hp.2).ne',
        Real.log_div (sub_pos.mpr hp.2).ne' (sub_pos.mpr ht.2).ne']; ring,
      Z75,Real.exp_log (div_pos (sub_pos.mpr hp.2) (sub_pos.mpr ht.2))]
  rw [neg_add,Z50,h1,h2]
  unfold Qaa
  rw [div_pow,div_pow]
  field_simp [ht.1.ne',(sub_pos.mpr ht.2).ne']
theorem QjO (n l:ℕ) {t p:ℝ}
    (ht:t ∈ Z4 0 1) (hp:p ∈ Z4 0 1)
    (hl:l ≤ n) (hmean:(n:ℝ)*t=l) (hv:1 ≤ (n:ℝ)*t*(1-t)) :
    Z1 (-((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p))) /
      (12*Z0 ((n:ℝ)*t*(1-t))) ≤ Qaa n p l:=by
  have hn:(0:ℝ)<n:=by nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hnl:((n-l:ℕ):ℝ)=(n:ℝ)-(l:ℝ):=by exact Z47 hl
  have he:(l:ℝ)*Z8 (t/p)+((n-l:ℕ):ℝ)*Z8 ((1-t)/(1-p)) ≤
      ((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p)):=by
    have H:=mul_le_mul_of_nonneg_left (Qjr ht hp) hn.le
    calc
      _ = (n:ℝ)*(t*Z8 (t/p)+(1-t)*Z8 ((1-t)/(1-p))):=by
        rw [hnl,← hmean]; ring
      _ ≤ (n:ℝ)*((t-p)^2/(p*(1-p))):=H
      _ = _:=by
        rw [← hmean]
        field_simp [hn.ne',hp.1.ne',(sub_pos.mpr hp.2).ne']
  rw [QjK n l ht hp]
  calc
    _ = (1/(12*Z0 ((n:ℝ)*t*(1-t)))) *
      Z1 (-((l:ℝ)-(n:ℝ)*p)^2/((n:ℝ)*p*(1-p))):=by ring
    _ ≤ (1/(12*Z0 ((n:ℝ)*t*(1-t)))) *
      Z1 (-((l:ℝ)*Z8 (t/p)+((n-l:ℕ):ℝ)*Z8 ((1-t)/(1-p)))):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg he
    _ ≤ _:=mul_le_mul_of_nonneg_right (Qgj n l ht hl hmean hv)
      (Z49 _)
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QaN {u m:ℕ} (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (s:ℕ) (X:ℤ) (τ:ℝ):Fin u → Fin (u*m) :=
  shiftedTag (periodSlot (fun _ => off)) hsafe
    (fun j => motifShift (QaT s ((j.val:ℤ)-X)) ((Qak s).coeff ((j.val:ℤ)-X)) τ)
theorem QiF {u m:ℕ} (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (s:ℕ) (X:ℤ) (τ:ℝ):StrictMono (QaN off hsafe s X τ) :=
  QfF _ _ _
theorem Qae.comp {n u r:ℕ} {p:Fin u → Fin n}
    (hp:Qae p) (j:Fin r → Fin u) (hj:StrictMono j) :
    Qae (p ∘ j) :=
  ⟨fun i => hp.1 (j i),fun i k hik => hp.2 (j i) (j k) (hj hik)⟩
def QcL {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (v:Qab l r):ℝ :=
  ∑ X ∈ π.coeff.support,π.coeff X *
    (Qdr hl (QaN off hsafe s X 1) v -
     Qdr hl (QaN off hsafe s X (-1)) v)
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def Qby (c:ℤ) (f:IntSeries):IntSeries :=
  Z29 c 1*f
theorem QfM (c:ℤ) (f:IntSeries) (z:ℤ) :
    (Qby c f).coeff z = f.coeff (z-c):=by
  rw [Qby,AddMonoidAlgebra.coeff_single_mul_apply,one_mul]
  congr 1; omega
theorem QiV (c:ℤ) (f:IntSeries) :
    seriesL2Sq (Qby c f)=seriesL2Sq f:=by
  unfold seriesL2Sq
  simp_rw [QfM]
  exact (Equiv.subRight c).tsum_eq (fun z => f.coeff z^2)
theorem Qnz (c:ℤ) (f g:IntSeries) :
    f*Qby c g=Qby c (f*g):=by
  unfold Qby
  ring
theorem Qlx (g:ℕ) (z:ℤ) (hz:(fairSeries g).coeff z ≠ 0) :
    0≤z ∧ z≤g:=by
  have h0:0≤z:=by
    by_contra h
    exact hz (QcD g z (by omega))
  obtain ⟨k,rfl⟩:=Int.eq_ofNat_of_zero_le h0
  refine ⟨by positivity,?_⟩
  by_contra hk
  rw [Qct,Qah,Z44 (by omega)] at hz
  simp at hz
theorem QqI (g:ℕ) (c z:ℤ) :
    0≤(Qby c (fairSeries g)).coeff z:=by
  rw [QfM]
  exact Qlw _ _
theorem QqK (g:ℕ) (c z:ℤ)
    (hz:(Qby c (fairSeries g)).coeff z ≠ 0) :
    c≤z ∧ z≤c+g:=by
  rw [QfM] at hz
  have h:=Qlx g (z-c) hz
  omega
theorem QqJ (g s:ℕ) (c:ℤ) :
    seriesL2Sq (Qak s*Qby c (fairSeries g)) ≤
      ((2:ℝ)^(s*s))^2*(((2*Qar (g/(s+1)))^s)^2*Qar (g/(s+1))):=by
  rw [Qnz,QiV]
  exact (QpT g s).2
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem QmX {r:ℕ} (a:Fin r) :
    (∑ h,((QaM a) h).order)=1:=by
  classical
  have he (h:Fin r):((QaM a) h).order=if h=a then 1 else 0:=by
    by_cases hh:h=a <;> simp [QaM,hh,Qac.order]
  simp_rw [he]
  simp
theorem QgV {r:ℕ} (k:Fin r → Qac)
    (h1:Qax k=1) (h2:QdV k=0) :
    ∃ a:Fin r,k=QaM a:=by
  classical
  obtain ⟨a,ha⟩:=Finset.card_eq_one.mp h1
  refine ⟨a,funext fun b => ?_⟩
  have hfirst:k b = .first ↔ b=a:=by
    have hh:=congrArg (fun A:Finset (Fin r) => b∈A) ha
    simpa only [Finset.mem_filter,Z21,true_and,Finset.mem_singleton] using (iff_of_eq hh)
  have hsecond:k b ≠ .second:=by
    have hh:=Finset.card_eq_zero.mp h2
    intro hb
    have hmem:b∈(Finset.univ.filter fun b => k b=.second):=by simp [hb]
    rw [hh] at hmem
    exact Finset.notMem_empty _ hmem
  by_cases hb:b=a
  · have hf:=hfirst.mpr hb
    simpa [QaM,hb] using hf
  · have hf:=mt hfirst.mp hb
    cases hk:k b <;> simp_all [QaM]
theorem QhU {r:ℕ} (k:Fin r → Qac)
    (hk:Odd (Qax k)) (hnl:¬∃a,k=QaM a) :
    ∃ a b:Fin r,a<b ∧ k a≠.unchanged ∧ k b≠.unchanged:=by
  classical
  have hp:0<Qax k:=hk.pos
  obtain ⟨a,ha⟩:=Finset.card_pos.mp hp
  have ha':k a=.first:=(Finset.mem_filter.mp ha).2
  by_contra hh
  push Not at hh
  apply hnl
  refine ⟨a,funext fun b => ?_⟩
  by_cases hb:b=a
  · subst b; simp [QaM,ha']
  · have hba:k b=.unchanged:=by
      rcases lt_or_gt_of_ne hb with hba|hab
      · by_contra hb'
        exact (show k a≠.unchanged by simp [ha']) (hh b a hba hb')
      · exact hh a b hab (by simp [ha'])
    simp [QaM,hb,hba]
theorem QnM {r:ℕ} (k:Fin r → Qac)
    (hk:Odd (Qax k)) (hnl:¬∃a,k=QaM a) :
    3≤∑ h,(k h).order:=by
  rcases QnN k hk with h|h
  · exact (hnl (QgV k h.1 h.2)).elim
  · exact h
theorem Qnp (f π:IntSeries) (L:ℕ)
    (hf:∀z,f.coeff z≠0 → 0≤z ∧ z<L) (z:ℤ) (hz:(f*π).coeff z≠0) :
    ∃X∈π.coeff.support,X≤z ∧ z<X+L:=by
  rw [mul_comm,Z79,Finsupp.sum] at hz
  obtain ⟨X,hX,hv⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
  have hh:=hf (-X+z) (mul_ne_zero_iff.mp hv).2
  exact ⟨X,hX,by omega,by omega⟩
def QbI (u s:ℕ) (π:IntSeries):Prop :=
  ∀X∈π.coeff.support,
    (u:ℝ)/3≤2*(X:ℝ)+1 ∧ (u:ℝ)/3≤2*u-(2*((X:ℝ)+(2:ℝ)^s)+1)
theorem QhL {u s:ℕ} (π f:IntSeries)
    (hπ:QbI u s π)
    (hf:∀z,f.coeff z≠0 → 0≤z ∧ z<(2^s:ℕ))
    (h:Fin u) (hh:(f*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1):=by
  obtain ⟨X,hX,hL,hR⟩:=Qnp f π (2^s) hf h.val hh
  have hL':(X:ℝ)≤h.val:=by exact_mod_cast hL
  have hR':(h.val:ℝ)<(X:ℝ)+(2:ℝ)^s:=by exact_mod_cast hR
  have hs:=hπ X hX
  constructor <;> linarith
theorem Qpe {u s:ℕ} (π:IntSeries)
    (hπ:QbI u s π) (h:Fin u)
    (hh:(Qak s*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1):=by
  apply QhL π _ hπ _ h hh
  intro z hz
  constructor
  · by_contra h; exact hz ((QdT s).1 z (Or.inl (by omega)))
  · by_contra h; exact hz ((QdT s).1 z (Or.inr (by omega)))
theorem Qrh {u s:ℕ} (π:IntSeries)
    (hπ:QbI u s π) (h:Fin u)
    (hh:(geomSeries (2^s)*π).coeff (h.val:ℤ)≠0) :
    (u:ℝ)/3≤2*h.val+1 ∧ (u:ℝ)/3≤2*u-(2*h.val+1):=by
  apply QhL π _ hπ _ h hh
  intro z hz
  by_contra hs
  rw [Qhe,if_neg hs] at hz
  exact hz rfl
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem QiE {u m r:ℕ} (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (s:ℕ) (X:ℤ) (τ:ℝ) (j:Qab u r) :
    QaN off hsafe s X τ ∘ j.val =
      shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property)
        (fun i => motifShift (QaT s ((j.val i).val-X))
          ((Qak s).coeff ((j.val i).val-X)) τ):=by
  funext i; apply Z34; rfl
def Qco {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (j:Qab u r) (v:Qab l r):ℝ :=
  ∑X∈π.coeff.support,π.coeff X*
    (Qaw hl (QaN off hsafe s X 1 ∘ j.val) v.val -
     Qaw hl (QaN off hsafe s X (-1) ∘ j.val) v.val)
theorem QpP {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off))) (π:IntSeries) (s:ℕ)
    (v:Qab l r) :
    QcL hl off hsafe π s v=∑j,Qco hl off hsafe π s j v:=by
  unfold QcL Qco
  simp_rw [QfC _ _ (QiF _ _ _ _ _),
    ← Z39,Z3]
  exact Z17
theorem QpR {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off))) (π:IntSeries) (s:ℕ)
    (j:Qab u r) (v:Qab l r) :
    Qco hl off hsafe π s j v = ∑k:Fin r → Qac,
      if Odd (Qax k) then
        2*Qbo π s (fun i => (j.val i).val) k *
          QbF hl (periodSlot (fun _ => off) ∘ j.val)
            (hsafe.comp j.val j.property) k v else 0:=by
  unfold Qco
  simp_rw [QiE]
  have H:=Qnh π s (fun i => (j.val i).val)
    (fun a => Qaw hl
      (shiftedTag (periodSlot (fun _ => off) ∘ j.val) (hsafe.comp j.val j.property) a) v.val)
  simpa only [ite_mul,zero_mul,QbF] using H
def QcY {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (θ:ℝ) (v:Qab l r):ℝ :=
  ∑j,if QaQ m θ j v then Qco hl off hsafe π s j v else 0
def QcX {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (θ:ℝ) (k:Fin r → Qac) (v:Qab l r):ℝ :=
  ∑j,if QaQ m θ j v then
    Qbo π s (fun i => (j.val i).val) k *
      QbF hl (periodSlot (fun _ => off) ∘ j.val)
        (hsafe.comp j.val j.property) k v else 0
theorem Qkf {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (θ:ℝ) (v:Qab l r) :
    QcY hl off hsafe π s θ v =
      2*∑k:Fin r → Qac,if Odd (Qax k) then
        QcX hl off hsafe π s θ k v else 0:=by
  unfold QcY QcX
  have he (j:Qab u r) :
      (if QaQ m θ j v then Qco hl off hsafe π s j v else 0) =
      ∑k:Fin r → Qac,if Odd (Qax k) then
        (if QaQ m θ j v then
          2*Qbo π s (fun i => (j.val i).val) k *
            QbF hl (periodSlot (fun _ => off) ∘ j.val)
              (hsafe.comp j.val j.property) k v else 0) else 0:=by
    by_cases hv:QaQ m θ j v
    · simp only [if_pos hv,QpR]
    · simp [hv]
  simp_rw [he]
  rw [Z17,Z3]
  apply Z2 rfl
  intro k _
  by_cases hk:Odd (Qax k)
  · simp only [if_pos hk,Z3]
    apply Z2 rfl
    intro j _
    split_ifs <;> ring
  · simp [hk]
theorem QpS {u m l r:ℕ}
    (hu:0 < u) (hm:128 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin m) (hoff:|(off.val:ℝ)-(m:ℝ)/2|≤3)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0≤π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (j:Qab u r) {θ:ℝ} (hθ:θ∈Z4 0 1) :
    (∑v:Qab l r,if QaQ m θ j v then 0 else
      |Qco hl off hsafe π s j v|) ≤
      2*(((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l * (2*Z1 (-(m:ℝ)/(1024*u)))):=by
  let K (X:ℤ) (τ:ℝ) (v:Qab l r) :=
    Qaw hl (QaN off hsafe s X τ ∘ j.val) v.val
  let B:=((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l * (2*Z1 (-(m:ℝ)/(1024*u)))
  have hK (X:ℤ) (τ:ℝ):(∑v:Qab l r,
      if QaQ m θ j v then 0 else K X τ v)≤B:=by
    simp_rw [K,QiE]
    exact Qoy hu hm hr hl (fun _ => off) (fun _ => hoff)
      (by intro _ _; simp) j (hsafe.comp j.val j.property) _ hθ
  have hnon (X:ℤ) (τ:ℝ) (v:Qab l r):0≤K X τ v :=
    Qdw _ _ _
  calc
    _ ≤ ∑v:Qab l r,∑X∈π.coeff.support,π.coeff X*
        (if QaQ m θ j v then 0 else K X 1 v+K X (-1) v):=by
      apply Z7
      intro v _
      by_cases hv:QaQ m θ j v
      · simp [hv]
      · simp only [if_neg hv]
        refine (Z70 _ _).trans ?_
        apply Z7
        intro X _
        rw [abs_mul,abs_of_nonneg (hπ X)]
        apply mul_le_mul_of_nonneg_left _ (hπ X)
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hnon X 1 v),abs_of_nonneg (hnon X (-1) v)])
    _ = ∑X∈π.coeff.support,π.coeff X*((∑v:Qab l r,
        if QaQ m θ j v then 0 else K X 1 v)+
        (∑v:Qab l r,if QaQ m θ j v then 0 else K X (-1) v)):=by
      rw [Z17]
      apply Z2 rfl
      intro X _
      rw [← Z3,← Z14]
      congr 1; apply Z2 rfl
      intro v _; split_ifs <;> ring
    _ ≤ ∑X∈π.coeff.support,π.coeff X*(B+B):=by
      apply Z7
      intro X _
      exact mul_le_mul_of_nonneg_left (add_le_add (hK X 1) (hK X (-1))) (hπ X)
    _ = _:=by rw [← Z33,hπsum]; dsimp [B]; ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qnu {r:ℕ} (k:Fin r → Qac)
    (hk:Odd (Qax k)) (hnl:¬∃a,k=QaM a) :
    ∃ a:Fin r,k a≠.unchanged ∧ ∃c:Fin (r+1),∀ {u s:ℕ} (π:IntSeries)
      (j:Qab u r),
      Qbo π s (fun h => (j.val h).val) k≠0 →
        Qad j.val c ≤ 2*(2^s):=by
  obtain ⟨a,b,hab,ha,hb⟩:=QhU k hk hnl
  cases r with
  | zero => exact Fin.elim0 a
  | succ r =>
    have har:a.val < r:=by have:=b.isLt; exact lt_of_lt_of_le hab (Z63 b.isLt)
    let i:Fin r:=⟨a.val,har⟩
    have hi:i.castSucc=a:=by ext; rfl
    refine ⟨a,ha,i.castSucc.succ,?_⟩
    intro u s π j hj
    apply Qnt π s j k i b
    · simpa only [hi] using hab
    · simpa only [hi] using ha
    · exact hb
    · exact hj
theorem Qkg {u m l r:ℕ}
    (hm:32 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (hcentral:QbI u s π)
    {θ:ℝ} (hθ:θ∈Z4 0 1) (hhalf:1/2 ≤ θ)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (a:Fin r) :
    (∑v,(QcX hl off hsafe π s θ (QaM a) v)^2)  ≤ 
      QaW u m r 1 θ * Qbs u r *
        seriesL2Sq (Qak s*π):=by
  have hb:=Qot hm hr hl (fun _ => off) (fun _ => hoff)
    (by intro _ _; simp) (fun j => hsafe.comp j.val j.property) (QaM a)
    hθ hhalf hmean hv a
    (fun j => Qbo π s (fun i => (j.val i).val) (QaM a))
    (fun h => (Qak s*π).coeff h.val)
    (by intro j; rw [Qnq])
    (Qpe π hcentral)
  rw [QmX] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (QiA _ (fun h:Fin u => (h.val:ℤ)) (by intro a b h; apply Z34; change (a.val:ℤ)=b.val at h; exact_mod_cast h))
  unfold QaW QaJ Qbs
  positivity
theorem Qkh {u m l r:ℕ}
    (hm:32 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (s:ℕ) (hcentral:QbI u s π)
    {θ:ℝ} (hθ:θ∈Z4 0 1) (hhalf:1/2 ≤ θ)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (k:Fin r → Qac) (hk:Odd (Qax k)) (hnl:¬∃a,k=QaM a)
    (hM:((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v,(QcX hl off hsafe π s θ k v)^2)  ≤ 
      QaW u m r (∑h,(k h).order) θ *
        QbE u r (2*(2^s)) * seriesL2Sq (geomSeries (2^s)*π):=by
  obtain ⟨a,ha,c,hc⟩:=Qnu k hk hnl
  have hb:=Qos hm hr hl (fun _ => off) (fun _ => hoff)
    (by intro _ _; simp) (fun j => hsafe.comp j.val j.property) k
    hθ hhalf hmean hv a c
    (fun j => Qbo π s (fun i => (j.val i).val) k)
    (fun h => (geomSeries (2^s)*π).coeff h.val)
    (fun j => Qnl π hπ s _ k a ha)
    (fun j hj => hc π j hj) (Qrh π hcentral) hM
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
    (QiA _ (fun h:Fin u => (h.val:ℤ)) (by intro a b h; apply Z34; change (a.val:ℤ)=b.val at h; exact_mod_cast h))
  unfold QaW QaJ QbE
  positivity
def Qcy (u m r s:ℕ) (π:IntSeries) (θ:ℝ)
    (k:Fin r → Qac):ℝ :=
  if ∃a,k=QaM a then
    QaW u m r 1 θ * Qbs u r * seriesL2Sq (Qak s*π)
  else QaW u m r (∑h,(k h).order) θ *
    QbE u r (2*(2^s)) * seriesL2Sq (geomSeries (2^s)*π)
theorem QqA {α β:Type*} [Fintype α] [Fintype β] (f:α → β → ℝ) :
    (∑ b,(∑a,f a b)^2)  ≤  (Z10 α:ℝ)*∑a,∑b,f a b^2:=by
  calc
    _  ≤  ∑b,(Z10 α:ℝ)*∑a,f a b^2:=by
      apply Z7
      intro b _
      have h:=Z84 Z16
        (r:=fun a => f a b) (f:=fun _ => (1:ℝ)) (g:=fun a => f a b^2)
        (by intro _ _; norm_num) (by intro _ _; positivity) (by intro _ _; simp)
      simpa using h
    _ = _:=by rw [← Z3,Z17]
theorem Qkl {u m l r:ℕ}
    (hm:32 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (s:ℕ) (hcentral:QbI u s π)
    {θ:ℝ} (hθ:θ∈Z4 0 1) (hhalf:1/2 ≤ θ)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM:((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v:Qab l r,(QcY hl off hsafe π s θ v)^2)  ≤ 
      4*(Z10 (Fin r → Qac):ℝ)*
        ∑k:Fin r → Qac,if Odd (Qax k) then
          Qcy u m r s π θ k else 0:=by
  simp_rw [Qkf,mul_pow,show (2:ℝ)^2=4 by norm_num]
  rw [← Z3]
  calc
    _  ≤  4*((Z10 (Fin r → Qac):ℝ)*∑k:Fin r → Qac,∑v:Qab l r,
        (if Odd (Qax k) then QcX hl off hsafe π s θ k v else 0)^2):=by
      exact mul_le_mul_of_nonneg_left (QqA (fun (k:Fin r → Qac) (v:Qab l r) =>
        if Odd (Qax k) then QcX hl off hsafe π s θ k v else 0)) (by norm_num)
    _  ≤  _:=by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Z7
      intro k _
      by_cases hk:Odd (Qax k)
      · simp only [if_pos hk]
        unfold Qcy
        split_ifs with hlin
        · obtain ⟨a,rfl⟩:=hlin
          exact Qkg hm hr hl off hoff hsafe π s hcentral hθ hhalf hmean hv a
        · exact Qkh hm hr hl off hoff hsafe π hπ s hcentral
            hθ hhalf hmean hv k hk hlin hM
      · simp [hk]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem QpO {u m l r:ℕ}
    (hu:0 < u) (hm:128 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) {θ:ℝ} (hθ:θ∈Z4 0 1) :
    (∑v:Qab l r,|QcL hl off hsafe π s v-
        QcY hl off hsafe π s θ v|) ≤
      (Z10 (Qab u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l * (2*Z1 (-(m:ℝ)/(1024*u))))):=by
  simp_rw [QpP,QcY,← Z39]
  calc
    _ ≤ ∑v:Qab l r,∑j:Qab u r,
        if QaQ m θ j v then 0 else |Qco hl off hsafe π s j v|:=by
      apply Z7
      intro v _
      refine (Z70 _ _).trans_eq ?_
      apply Z2 rfl
      intro j _
      split_ifs <;> simp
    _ = ∑j:Qab u r,∑v:Qab l r,
        if QaQ m θ j v then 0 else |Qco hl off hsafe π s j v|:=Z17
    _ ≤ _:=by
      calc
        _ ≤ ∑j:Qab u r,
            2*(((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l * (2*Z1 (-(m:ℝ)/(1024*u)))) :=
          Z7 (fun j _ => QpS hu hm hr hl off hoff hsafe π hπ hπsum s j hθ)
        _ = _:=by simp
theorem QlE {α:Type*} [Fintype α] (f:α → ℝ) :
    (∑a,f a^2) ≤ (∑a,|f a|)^2:=by
  have h:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Z16) (f:=fun a => |f a|)
    (by intro a _; exact abs_nonneg _)
  simpa only [sq_abs] using h
theorem QmO {u m l r:ℕ}
    (hu:0 < u) (hm:128 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (hcentral:QbI u s π)
    {θ:ℝ} (hθ:θ∈Z4 0 1) (hhalf:1/2 ≤ θ)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM:((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ))) :
    (∑v:Qab l r,(QcL hl off hsafe π s v)^2) ≤
      8*(Z10 (Fin r → Qac):ℝ)*
        (∑k:Fin r → Qac,if Odd (Qax k) then
          Qcy u m r s π θ k else 0) +
      2*((Z10 (Qab u r):ℝ)*
        (2*(((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l * (2*Z1 (-(m:ℝ)/(1024*u))))))^2:=by
  let A:Qab l r → ℝ:=QcL hl off hsafe π s
  let C:Qab l r → ℝ:=QcY hl off hsafe π s θ
  have hn:=Qkl (by omega) hr hl off hoff hsafe π hπ s hcentral hθ hhalf hmean hv hM
  have ht:=QpO hu hm hr hl off hoff hsafe π hπ hπsum s hθ
  have hE:=(QlE (fun v:Qab l r => A v-C v)).trans
    (pow_le_pow_left₀ (Z11 (fun v _ => abs_nonneg (A v-C v))) ht 2)
  have hsum:(∑v:Qab l r,A v^2) ≤
      2*(∑v:Qab l r,C v^2)+2*(∑v:Qab l r,(A v-C v)^2):=by
    simp only [Z3,← Z14]
    apply Z7
    intro v _
    nlinarith [sq_nonneg (A v-2*C v)]
  calc
    _ ≤ 2*(∑v:Qab l r,C v^2)+2*(∑v:Qab l r,(A v-C v)^2):=hsum
    _ ≤ _:=by dsimp [C] at *; linarith
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def Qay (q:ℝ):List Bool → (List Bool → ℝ) → ℝ
  | [],F => F []
  | b::w,F => q*Qay q w F +
      (1-q)*Qay q w (fun t => F (b::t))
theorem QiT {n:ℕ} (x:Word (n+1)) (b:Bool) (a:Mask n) :
    traceOfMask x (Z15 b a)=
      if b then x 0::traceOfMask (fun i => x i.succ) a
      else traceOfMask (fun i => x i.succ) a:=by
  rw [QiU,Z65,QiU]
  cases b <;> simp
theorem QhC {n:ℕ} (q:ℝ) (b:Bool) (a:Mask n) :
    maskWeight q (Z15 b a)=(if b then 1-q else q)*maskWeight q a:=by
  simp [maskWeight,Z53]
theorem Qhy {n:ℕ} (q:ℝ) (x:Word n) (F:List Bool → ℝ) :
    Qay q (Z20 x) F =
      ∑a:Mask n,maskWeight q a*F (traceOfMask x a):=by
  induction n generalizing F with
  | zero => simp [Qay,maskWeight,traceOfMask]
  | succ n ih =>
    rw [Z65,Qay,ih,ih]
    symm
    rw [← (Z46 (fun _:Fin (n+1) => Bool)).sum_comp,Z32]
    change (∑b:Bool,∑a:Mask n,maskWeight q (Z15 b a)*F (traceOfMask x (Z15 b a)))=_
    simp_rw [QhC,QiT]
    simp only [Bool.false_eq_true,ite_false,ite_true,Z62]
    simp only [mul_assoc,← Z3]
    ring
theorem Qep (q:ℝ) (x y:List Bool) (F:List Bool → ℝ) :
    Qay q (x++y) F =
      Qay q x (fun t => Qay q y (fun u => F (t++u))):=by
  induction x generalizing F with
  | nil => simp [Qay]
  | cons b x ih => simp only [List.cons_append,Qay,ih]
def QbG (b:Bool):List Bool:=if b then [true] else [false,true]
theorem QoL (q:ℝ) (b:Bool) (F:List Bool → ℝ) :
    Qay q (QbG b) F =
      ∑z:Qai,(if b then QcC q z else Qck q z)*F (QdS z):=by
  cases b <;> simp [QbG,Qay,QdS,
    QcC,Qck,Z64]
  ring
theorem QoK {q:ℝ} (hq:q∈Z4 0 1)
    (b:Bool) (F:List Bool → ℝ) :
    Qay q (QbG b) F =
      Qaq q * F []+(1-Qaq q)*
        (Qav q hq b).expect (fun z => F (QdS z)):=by
  rw [QoL]
  simp_rw [← QoN hq]
  simp only [add_mul,Z14]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Z21,ite_true,
    QdS,Matrix.cons_val_zero]
  simp only [FiniteLaw.expect,Qav,mul_assoc,← Z3]
def Qcf (q:ℝ):List Bool → (List Qai → ℝ) → ℝ
  | [],F => F []
  | b::bs,F => Qaq q*Qcf q bs F +
      (1-Qaq q)*∑z:Qai,Qbe q b z*
        Qcf q bs (fun ys => F (z::ys))
def Qfl (ys:List Qai):List Bool:=(ys.map QdS).flatten
theorem QoR {q:ℝ} (hq:q∈Z4 0 1)
    (bs:List Bool) (F:List Bool → ℝ) :
    Qay q ((bs.map QbG).flatten) F =
      Qcf q bs (fun ys => F (Qfl ys)):=by
  induction bs generalizing F with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,List.flatten_cons]
    rw [Qep,QoK hq]
    simp only [List.nil_append,ih,FiniteLaw.expect,Qav]
    simp only [Qcf]
    rfl
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QbP (q:ℝ):List Bool → (List Qai → ℝ) → ℝ
  | [],F => F []
  | b::bs,F => ∑z:Qai,Qbe q b z*
      QbP q bs (fun ys => F (z::ys))
theorem Qla {n:ℕ} (q:ℝ) (θ:Fin n → Bool)
    (F:List Qai → ℝ) :
    QbP q (Z20 θ) F=
      ∑x:Fin n → Qai,(∏i,Qbe q (θ i) (x i))*F (Z20 x):=by
  induction n generalizing F with
  | zero => simp [QbP]
  | succ n ih =>
    rw [Z65,QbP]
    simp_rw [ih,Z3]
    rw [← (Z46 (fun _:Fin (n+1) => Qai)).sum_comp,Z32]
    apply Z2 rfl
    intro z _
    apply Z2 rfl
    intro x _
    simp [Z46,Z53,Z65,mul_assoc]
theorem QpX {n:ℕ} (q:ℝ) (θ:Fin n → Bool)
    (F:List Qai → ℝ) :
    Qcf q (Z20 θ) F=
      ∑a:Mask n,maskWeight (Qaq q) a*
        QbP q (traceOfMask θ a) F:=by
  induction n generalizing F with
  | zero => simp [Qcf,QbP,maskWeight,traceOfMask]
  | succ n ih =>
    rw [Z65,Qcf]
    simp_rw [ih]
    symm
    rw [← (Z46 (fun _:Fin (n+1) => Bool)).sum_comp,Z32]
    change (∑b:Bool,∑a:Mask n,maskWeight (Qaq q) (Z15 b a)*
      QbP q (traceOfMask θ (Z15 b a)) F)=_
    simp_rw [QhC,QiT]
    simp only [Z62,ite_true,Bool.false_eq_true,ite_false,QbP]
    simp_rw [mul_assoc,Z3]
    rw [Z17,add_comm]
    congr 1
    apply Z2 rfl
    intro z _
    apply Z2 rfl
    intro a _
    ring
def maskSubset {n:ℕ} (a:Mask n):Finset (Fin n):=Finset.univ.filter fun i => a i
def QdL (n:ℕ):Mask n ≃ Finset (Fin n) where
  toFun:=maskSubset
  invFun S i:=decide (i∈S)
  left_inv a:=by funext i; simp [maskSubset]
  right_inv S:=by ext i; simp [maskSubset]
theorem Qnc {n:ℕ} (q:ℝ) (a:Mask n) :
    maskWeight q a = (1-q)^(maskSubset a).card*q^(n-(maskSubset a).card):=by
  unfold maskWeight maskSubset
  rw [Finset.prod_ite]
  simp only [Z78]
  congr 1
  have h:=Finset.card_filter_add_card_filter_not (s:=(Z16:Finset (Fin n))) (p:=fun i => a i)
  rw [Z48,Z26] at h
  rw [show (Finset.univ.filter fun i:Fin n => ¬a i=true).card=
      n-(Finset.univ.filter fun i:Fin n => a i=true).card by omega]
theorem Qqb {n l:ℕ} (S:QaG (Fin n) l) :
    Z20 (slotAtRank S)=S.val.sort:=by
  apply List.ext_getElem
  · simp [S.property]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    rfl
theorem Qly {n:ℕ} (S:Finset (Fin n)) :
    ((List.finRange n).filter fun i => decide (i∈S))=S.sort:=by
  apply ((List.sortedLT_finRange n).pairwise.filter _).eq_of_mem_iff S.sortedLT_sort.pairwise
  intro a
  simp
theorem Qpt {n l:ℕ} (θ:Fin n → Bool) (S:QaG (Fin n) l) :
    traceOfMask θ (fun i => decide (i∈S.val))=Z20 (fun v => θ (slotAtRank S v)):=by
  rw [traceOfMask,Qly,← Qqb S,List.map_ofFn]
  rfl
theorem QpY {n:ℕ} (q:ℝ) (θ:Fin n → Bool)
    (F:List Qai → ℝ) :
    Qcf q (Z20 θ) F=
      ∑S:Finset (Fin n),QbL (1-Qaq q) S*
        QbP q (traceOfMask θ (fun i => decide (i∈S))) F:=by
  rw [QpX,← (QdL n).symm.sum_comp]
  apply Z2 rfl
  intro S _
  rw [Qnc]
  change (1-Qaq q)^(QdL n ((QdL n).symm S)).card *
      (Qaq q)^(n-(QdL n ((QdL n).symm S)).card)*
      QbP q (traceOfMask θ (fun i => decide (i∈S))) F=_
  rw [Z103]
  simp [QbL]
def Qkd (n:ℕ):Finset (Fin n) ≃ Σl:Fin (n+1),QaG (Fin n) l.val where
  toFun S:=⟨⟨S.card,by have:=Finset.card_le_univ S; simpa using Z72 this⟩,⟨S,rfl⟩⟩
  invFun x:=x.2.val
  left_inv _:=rfl
  right_inv x:=by
    rcases x with ⟨⟨l,hl⟩,⟨S,hS⟩⟩
    dsimp
    change S.card=l at hS
    subst l
    rfl
theorem Qqs {n l:ℕ} (hl:l ≤ n) (p:ℝ) (S:QaG (Fin n) l) :
    QbL p S.val=Qaa n p l*(QaO l (by simpa using hl)).mass S:=by
  have hc:(n.choose l:ℝ)≠0:=by exact_mod_cast (Nat.choose_pos hl).ne'
  simp only [QbL,Qaa,QaO,S.property,Z26]
  field_simp
def Qbg {n l:ℕ} (hl:l ≤ n) (q:ℝ) (hq:q∈Z4 0 1)
    (θ:Fin n → Bool):FiniteLaw (Fin l → Qai) :=
  (QaO l (by simpa using hl)).mixture fun S =>
    FiniteLaw.QaR (fun v => Qav q hq (θ (slotAtRank S v)))
theorem QpW {n:ℕ} (q:ℝ) (hq:q∈Z4 0 1)
    (θ:Fin n → Bool) (F:List Qai → ℝ) :
    Qcf q (Z20 θ) F=
      ∑l:Fin (n+1),Qaa n (1-Qaq q) l.val*
        (Qbg (Z63 l.isLt) q hq θ).expect (fun x => F (Z20 x)):=by
  rw [QpY,← (Qkd n).symm.sum_comp,Z83]
  apply Z2 rfl
  intro l _
  change (∑S:QaG (Fin n) l.val,QbL (1-Qaq q) S.val*
      QbP q (traceOfMask θ (fun i => decide (i∈S.val))) F)=_
  calc
    _ = ∑S:QaG (Fin n) l.val,Qaa n (1-Qaq q) l.val*
        (QaO l.val (by simpa using Z63 l.isLt)).mass S*
        (∑x:Fin l.val → Qai,(∏v,Qbe q (θ (slotAtRank S v)) (x v))*F (Z20 x)):=by
      apply Z2 rfl
      intro S _
      rw [Qqs (Z63 l.isLt),Qpt θ S,Qla]
    _ = _:=by
      unfold Qbg FiniteLaw.expect FiniteLaw.mixture FiniteLaw.QaR Qav
      simp_rw [Z33,Z3]
      rw [Z17]
      apply Z2 rfl
      intro x _
      apply Z2 rfl
      intro S _
      ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qgw {n l:ℕ} (hl:l ≤ n)
    {q:ℝ} (hq:q∈Z4 0 1) (θ:Fin n → Bool) (x:Fin l → Qai) :
    (Qbg hl q hq θ).mass x =
      ((Qav q hq false).product l).mass x *
        QaX (QaO l (by simpa using hl))
          (fun S v => θ (slotAtRank S v)) (QaA q) x:=by
  have he:(fun S:QaG (Fin n) l =>
      FiniteLaw.QaR (fun v => Qav q hq (θ (slotAtRank S v)))) =
      (fun S:QaG (Fin n) l =>
      FiniteLaw.QaR (fun v => if θ (slotAtRank S v) then
        Qav q hq true else Qav q hq false)):=by
    funext S
    congr 1
    funext v
    cases θ (slotAtRank S v) <;> rfl
  unfold Qbg
  rw [he]
  exact QmU (Qav q hq false) (Qav q hq true)
    (QaA q) (Qik hq)
    (QaO l (by simpa using hl)) (fun S v => θ (slotAtRank S v)) x
def QaC {n u:ℕ} (d:Fin u → Fin n) (i:Fin n):Bool:=decide (i∈Set.range d)
theorem QgA {n l u:ℕ} (d:Fin u → Fin n) (S:QaG (Fin n) l) :
    (fun v => QaC d (slotAtRank S v))=QaY (Finset.univ.image d) S:=by
  funext v
  simp [QaC,QaY,Set.mem_range]
theorem QkE {n l u:ℕ} (hl:l ≤ n)
    {q:ℝ} (hq:q∈Z4 0 1) (d:Fin u → Fin n) (x:Fin l → Qai) :
    (Qbg hl q hq (QaC d)).mass x =
      ((Qav q hq false).product l).mass x *
        Qaj (Qbm (QaO l (by simpa using hl))
          (QaY (Finset.univ.image d))) (QaA q) x:=by
  rw [Qgw,show (fun S v => QaC d (slotAtRank S v))=
      QaY (Finset.univ.image d) by funext S; exact QgA d S,
      QfT]
def QdW (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X)
    (hπsum:∑X∈π.coeff.support,π.coeff X=1):FiniteLaw ↥π.coeff.support where
  mass X:=π.coeff X.val
  nonneg X:=hπ X.val
  total:=by simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hπsum
def QaD {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (τ:ℝ) (σ:Fin l → Bool):ℝ :=
  ∑X∈π.coeff.support,π.coeff X*
    Qbm (QaO l (by simpa using hl))
      (QaY (Finset.univ.image (QaN off hsafe s X τ))) σ
def Qca {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X)
    (hπsum:∑X∈π.coeff.support,π.coeff X=1) (s:ℕ) (τ:ℝ) :
    FiniteLaw (Fin l → Qai) :=
  (QdW π hπ hπsum).mixture fun X =>
    Qbg hl q hq (QaC (QaN off hsafe s X.val τ))
theorem QeU {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X)
    (hπsum:∑X∈π.coeff.support,π.coeff X=1) (s:ℕ) (τ:ℝ) (x:Fin l → Qai) :
    (Qca hl off hsafe hq π hπ hπsum s τ).mass x=
      ((Qav q hq false).product l).mass x *
        Qaj (QaD hl off hsafe π s τ) (QaA q) x:=by
  unfold Qca FiniteLaw.mixture QdW
  simp_rw [QkE]
  let F:ℤ → ℝ:=fun X => π.coeff X *
    (((Qav q hq false).product l).mass x *
      Qaj (Qbm (QaO l (by simpa using hl))
        (QaY (Finset.univ.image (QaN off hsafe s X τ))))
        (QaA q) x)
  change (∑ X:↥π.coeff.support,F X.val) = _
  rw [Finset.sum_coe_sort]
  dsimp only [F]
  unfold QaD Qaj
  simp_rw [Z3,Z33]
  rw [Z17]
  apply Z2 rfl
  intro σ _
  rw [Z3]
  apply Z2 rfl
  intro X _
  ring
theorem Qnf {u m l r:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (v:Qab l r) :
    QaD hl off hsafe π s 1 (rankMask v)-
      QaD hl off hsafe π s (-1) (rankMask v)=
        QcL hl off hsafe π s v:=by
  unfold QaD QcL
  simp_rw [QeI hl _ v]
  rw [← Z39]
  apply Z2 rfl
  intro X _
  ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QcR (r:ℕ):Fin r → Qac:=fun _ => .unchanged
theorem Qof {r:ℕ} (k:Fin r → Qac)
    (hk:(∑h,(k h).order)=0):k=QcR r:=by
  funext h
  have hh:=Z82 (fun i (_:i∈(Z16:Finset (Fin r))) =>
    Nat.zero_le (k i).order) (Z21 h)
  rw [hk] at hh
  have hz:(k h).order=0:=by omega
  cases he:k h <;> simp_all [Qac.order,QcR]
theorem QnL {r:ℕ} (k:Fin r → Qac)
    (hk:k≠QcR r):(∃h,k=QaM h) ∨ 2≤∑h,(k h).order:=by
  by_cases hlin:∃h,k=QaM h
  · exact Or.inl hlin
  right
  by_contra hsmall
  have horder:(∑h,(k h).order)=1:=by
    have hn:(∑h,(k h).order)≠0:=fun he => hk (Qof k he)
    omega
  have hc:=QgF k
  have hfirst:Qax k=1:=by omega
  have hsecond:QdV k=0:=by omega
  exact hlin (QgV k hfirst hsecond)
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QdU {n:ℕ} (A:(Fin n → Bool) → ℝ) (L:ℝ) (σ:Fin n → Bool):ℝ :=
  A σ * ∏ i,if σ i then L else 1
theorem QnD {α:Type*} {n:ℕ} (A:(Fin n → Bool) → ℝ)
    (Z:α → ℝ) {L:ℝ} (hL:L≠0) (x:Fin n → α) :
    Qaj (QdU A L) (fun a => Z a/L) x=Qaj A Z x:=by
  unfold Qaj QdU
  apply Z2 rfl
  intro σ _
  rw [mul_assoc,← Z30]
  congr 1
  apply Z71 rfl
  intro i _
  cases σ i <;> simp
  exact mul_div_cancel₀ _ hL
theorem QnA {n:ℕ} (A:(Fin n → Bool) → ℝ) (L R:ℝ) :
    QaK (QdU A L) R=QaK A (R*L):=by
  unfold QaK QdU
  apply Z2 rfl
  intro σ _
  rw [mul_pow,← Finset.prod_pow,mul_assoc,← Z30]
  congr 1
  apply Z71 rfl
  intro i _
  cases σ i <;> simp
  ring
theorem QnC {α:Type*} [Fintype α] (P:FiniteLaw α)
    (Z:α → ℝ) (k:ℕ) (hk:1 ≤ k) (hcenter:P.expect Z=0)
    {L:ℝ} (hL:0<L) (hMoment:P.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (n:ℕ) (A:(Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => |Qaj A Z x|^(2*k)) ≤
      (QaK A ((6*(2*k:ℕ):ℝ)*L))^k:=by
  have hcenter':P.expect (fun a => Z a/L)=0:=by
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Z61]
    change P.expect Z / L = 0
    rw [hcenter,zero_div]
  have hmoment':P.expect (fun a => |Z a/L|^(2*k))≤1:=by
    simp_rw [abs_div,abs_of_pos hL,div_pow]
    unfold FiniteLaw.expect
    simp_rw [← mul_div_assoc]
    rw [← Z61]
    apply (div_le_one (by positivity)).mpr hMoment
  have H:=QnB P (fun a => Z a/L) k hk hcenter' hmoment' n (QdU A L)
  simp_rw [QnD A Z hL.ne',QnA] at H
  simpa only [pow_mul,sq_abs] using H
theorem QhS {α:Type*} [Fintype α] (P:FiniteLaw α)
    (Z:α → ℝ) (k:ℕ) (hk:1 ≤ k) (hcenter:P.expect Z=0)
    {L:ℝ} (hL:0<L) (hMoment:P.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (n:ℕ) (A:(Fin n → Bool) → ℝ) :
    (P.product n).Qbh (Qaj A Z) k ≤
      QaK A ((6*(2*k:ℕ):ℝ)*L):=by
  have H:=QnC P Z k hk hcenter hL hMoment n A
  have hn:0≤(P.product n).expect (fun x => |Qaj A Z x|^(2*k)):=by
    exact Z11 (fun x _ => mul_nonneg ((P.product n).nonneg x) (by positivity))
  unfold FiniteLaw.Qbh
  calc
    _ ≤ (QaK A ((6*(2*k:ℕ):ℝ)*L)^k)^(1/(k:ℝ)) :=
      Z92 hn H (by positivity)
    _ = _:=by
      rw [← Z77,one_div,Real.rpow_rpow_inv (Qfq _ _) (by positivity)]
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]
theorem tv_le_one (P Q:FiniteLaw α):P.tv Q≤1:=by
  unfold tv
  have h:(∑a,|P.mass a-Q.mass a|)≤2:=by
    calc
      _ ≤ ∑a,(P.mass a+Q.mass a):=Z7 (fun a _ =>
        (abs_sub (P.mass a) (Q.mass a)).trans_eq (by rw [abs_of_nonneg (P.nonneg a),abs_of_nonneg (Q.nonneg a)]))
      _ = 2:=by rw [Z14,P.total,Q.total]; norm_num
  linarith
end TraceReconstruction.FiniteLaw
noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α:Type*} [Fintype α]
theorem Qeh {n:ℕ} (P:Fin (n+1) → FiniteLaw α)
    (F:(Fin (n+1) → α) → ℝ) :
    (QaR P).expect F =
      (P 0).expect (fun a => (QaR (fun i => P i.succ)).expect
        (fun x => F (Z15 a x))):=by
  change (∑x:Fin (n+1) → α,(∏i,(P i).mass (x i))*F x)=
    ∑a:α,(P 0).mass a*(∑x:Fin n → α,(∏i,(P i.succ).mass (x i))*F (Z15 a x))
  rw [← (Z46 (fun _:Fin (n+1) => α)).sum_comp,Z32]
  simp only [Z46,Equiv.coe_fn_mk,Z53,Z54,Z55]
  simp_rw [Z3,mul_assoc]
end TraceReconstruction.FiniteLaw
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem FiniteLaw.expect_sub {α:Type*} [Fintype α] (P:FiniteLaw α)
    (F G:α → ℝ):P.expect (fun a => F a-G a)=P.expect F-P.expect G:=by
  simp only [FiniteLaw.expect,mul_sub,Z39]
theorem FiniteLaw.Qjg {α:Type*} [Fintype α] (P:FiniteLaw α) (F:α → ℝ) :
    |P.expect F|≤P.expect (fun a => |F a|):=by
  simpa only [FiniteLaw.expect,abs_mul,abs_of_nonneg (P.nonneg _)] using Z70 (fun a => P.mass a*F a) Z16
def QaE {α:Type*} [Fintype α] (q:ℝ) (P:FiniteLaw α)
    (decode:α → List Bool) (w:List Bool):Prop :=
  ∀ F:List Bool → ℝ,P.expect (fun a => F (decode a))=Qay q w F
def Qbk {α:Type*} [Fintype α] (q:ℝ) (P:FiniteLaw α)
    (decode:α → List Bool) (w:List Bool) (E:ℝ):Prop :=
  ∀ F:List Bool → ℝ,(∀t,F t∈Z6 0 1) →
    |P.expect (fun a => F (decode a))-Qay q w F|≤E
theorem Qhw (q c:ℝ) (w:List Bool) :
    Qay q w (fun _ => c)=c:=by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [Qay,ih]; ring
theorem Qhx {q:ℝ} (hq:q∈Z6 0 1)
    (w:List Bool) {F G:List Bool → ℝ} (h:∀t,F t≤G t) :
    Qay q w F≤Qay q w G:=by
  induction w generalizing F G with
  | nil => exact h []
  | cons b w ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (ih h) hq.1)
      (mul_le_mul_of_nonneg_left (ih (fun t => h (b::t))) (sub_nonneg.mpr hq.2))
theorem QmY {q:ℝ} (hq:q∈Z6 0 1)
    (w:List Bool) (F:List Bool → ℝ) (hF:∀t,F t∈Z6 0 1) :
    Qay q w F∈Z6 0 1:=by
  constructor
  · simpa only [Qhw] using Qhx hq w (fun t => (hF t).1)
  · simpa only [Qhw] using Qhx hq w (fun t => (hF t).2)
theorem QaE.append {α β:Type*} [Fintype α] [Fintype β]
    {q:ℝ} {P:FiniteLaw α} {Q:FiniteLaw β} {f:α → List Bool} {g:β → List Bool}
    {x y:List Bool} (hP:QaE q P f x) (hQ:QaE q Q g y) :
    QaE q (P.prod Q) (fun a => f a.1++g a.2) (x++y):=by
  intro F
  rw [FiniteLaw.QbB,Qep]
  change P.expect (fun a => Q.expect (fun b => F (f a++g b)))=_
  unfold QaE at hP hQ
  calc
    _ = P.expect (fun a => Qay q y (fun t => F (f a++t))) :=
      congrArg P.expect (funext fun a => hQ (fun t => F (f a++t)))
    _ = _:=hP (fun t => Qay q y (fun u => F (t++u)))
theorem QaE.QbY {α:Type*} [Fintype α]
    {q:ℝ} {P:FiniteLaw α} {f:α → List Bool} {w:List Bool}
    (h:QaE q P f w):Qbk q P f w 0:=by
  intro F _
  rw [h,sub_self,abs_zero]
theorem Qbk.append {α β:Type*} [Fintype α] [Fintype β]
    {q:ℝ} (hq:q∈Z6 0 1) {P:FiniteLaw α} {Q:FiniteLaw β}
    {f:α → List Bool} {g:β → List Bool} {x y:List Bool} {E D:ℝ}
    (hP:Qbk q P f x E) (hQ:Qbk q Q g y D) :
    Qbk q (P.prod Q) (fun a => f a.1++g a.2) (x++y) (E+D):=by
  intro F hF
  rw [FiniteLaw.QbB,Qep]
  let H:List Bool → ℝ:=fun t => Qay q y (fun u => F (t++u))
  have hH:∀t,H t∈Z6 0 1:=fun t => QmY hq y _ (fun u => hF (t++u))
  have h1:=hP H hH
  have h2:|P.expect (fun a => Q.expect (fun b => F (f a++g b)))-P.expect (fun a => H (f a))|≤D:=by
    rw [← FiniteLaw.expect_sub]
    calc
      _ ≤ P.expect (fun a => |Q.expect (fun b => F (f a++g b))-H (f a)|):=FiniteLaw.Qjg _ _
      _ ≤ P.expect (fun _ => D):=FiniteLaw.QaZ _ (fun a => hQ _ (fun t => hF (f a++t)))
      _ = D:=FiniteLaw.Qbi _ _
  exact (abs_sub_le _ _ _).trans (by linarith only [h1,h2])
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {α β:Type*} [Fintype α] [Fintype β]
end TraceReconstruction
namespace TraceReconstruction
open scoped Classical
variable {α β:Type*} [Fintype α] [Fintype β]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]
theorem ext_expect {P Q:FiniteLaw α} (h:∀f:α→ℝ,P.expect f=Q.expect f):P=Q:=by
  apply ext
  funext a
  have H:=h (fun b => if b=a then 1 else 0)
  simpa only [expect,mul_ite,mul_one,mul_zero,Fintype.sum_ite_eq'] using H
theorem expect_map (P:FiniteLaw α) (f:α→β) (G:β→ℝ) :
    (P.map f).expect G=P.expect (G∘f):=Qln P f G
end FiniteLaw
variable {α β:Type*} [Fintype α] [Fintype β]
end TraceReconstruction
namespace TraceReconstruction
open scoped Classical
variable {α:Type*} [Fintype α]
end TraceReconstruction
namespace TraceReconstruction
open scoped Classical
variable {α:Type*} [Fintype α]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι:Type*} [Fintype ι] {β:ι → Type*} [∀i,Fintype (β i)]
def sigma (P:FiniteLaw ι) (K:∀i,FiniteLaw (β i)):FiniteLaw (Σi,β i) where
  mass a:=P.mass a.1*(K a.1).mass a.2
  nonneg a:=mul_nonneg (P.nonneg _) ((K _).nonneg _)
  total:=by
    rw [Z83]
    simp_rw [←Z3,(K _).total,mul_one]
    exact P.total
theorem Qej (P:FiniteLaw ι) (K:∀i,FiniteLaw (β i)) (F:(Σi,β i)→ℝ) :
    (P.sigma K).expect F=P.expect (fun i => (K i).expect (fun b => F ⟨i,b⟩)):=by
  simp only [expect,sigma,Z83,Z3,mul_assoc]
theorem QnU (P Q:FiniteLaw ι) (K L:∀i,FiniteLaw (β i)) :
    (∑i,min (P.mass i) (Q.mass i)*overlap (K i) (L i))≤overlap (P.sigma K) (Q.sigma L):=by
  simp only [overlap,sigma,Z83,Z3]
  apply Z7
  intro i _
  apply Z7
  intro b _
  apply le_min
  · exact mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min ((K i).nonneg b) ((L i).nonneg b)) (P.nonneg i)
  · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min ((K i).nonneg b) ((L i).nonneg b)) (Q.nonneg i)
end FiniteLaw
theorem Qqt {n N:ℕ} (hn:n≤N) (p:ℝ) :
    ∑l:Fin (N+1),Qaa n p l.val=1:=by
  rw [Z76 (fun k => Qaa n p k) (N+1)]
  rw [←Qcg n p]
  symm
  apply Z97 (Z90 (by omega))
  intro k _ hk
  have hn':n<k:=by simp only [Z57] at hk; omega
  simp [Qaa,Z44 hn']
def Qcs {n N:ℕ} (hn:n≤N) (p:ℝ) (hp:p∈Z6 0 1):FiniteLaw (Fin (N+1)) where
  mass l:=Qaa n p l.val
  nonneg l:=QaF n l.val hp
  total:=Qqt hn p
abbrev Qeb (N:ℕ):=Σl:Fin (N+1),Fin l.val→Qai
def QbZ {n N:ℕ} {q:ℝ} (hq:q∈Z4 0 1)
    (θ:Fin n→Bool) (l:Fin (N+1)):FiniteLaw (Fin l.val→Qai) :=
  if h:l.val≤n then Qbg h q hq θ else (Qav q hq false).product l.val
theorem Qdq {q:ℝ} (hq:q∈Z4 0 1) :
    1-Qaq q∈Z6 0 1:=by
  constructor
  · exact (Qcw hq).le
  · unfold Qaq; nlinarith [sq_nonneg q]
def Qcb {n N:ℕ} (hn:n≤N) {q:ℝ} (hq:q∈Z4 0 1)
    (θ:Fin n→Bool):FiniteLaw (Qeb N) :=
  (Qcs hn (1-Qaq q) (Qdq hq)).sigma
    (QbZ hq θ)
def Qdb {N:ℕ} (a:Qeb N):List Bool:=Qfl (Z20 a.2)
theorem QkP {n N:ℕ} (hn:n≤N) {q:ℝ} (hq:q∈Z4 0 1)
    (θ:Fin n→Bool) (F:List Qai→ℝ) :
    (Qcb hn hq θ).expect (fun a => F (Z20 a.2))=
      Qcf q (Z20 θ) F:=by
  rw [Qcb,FiniteLaw.Qej,QpW q hq θ F]
  change (∑l:Fin (N+1),Qaa n (1-Qaq q) l.val*
    (QbZ hq θ l).expect (fun x => F (Z20 x)))=_
  let f:ℕ→ℝ:=fun l => if hl:l≤n then Qaa n (1-Qaq q) l*
    (Qbg hl q hq θ).expect (fun x => F (Z20 x)) else 0
  have hleft:(∑l:Fin (N+1),Qaa n (1-Qaq q) l.val*
    (QbZ hq θ l).expect (fun x => F (Z20 x)))=
      ∑l:Fin (N+1),f l.val:=by
    apply Z2 rfl
    intro l _
    by_cases hl:l.val≤n
    · simp only [QbZ,hl,dif_pos,f]
    · simp [QbZ,hl,f,Qaa,Z44 (Nat.lt_of_not_ge hl)]
  rw [hleft,Z76 f (N+1)]
  have he:(∑l∈Z5 (n+1),f l)=∑l∈Z5 (N+1),f l:=by
    apply Z97 (Z90 (by omega))
    intro l _ hl
    simp only [Z57] at hl
    simp [f,show ¬l≤n by omega]
  rw [←he,←Z76 f (n+1)]
  apply Z2 rfl
  intro l _
  simp only [f,dif_pos (Z63 l.isLt)]
theorem QeW {n N:ℕ} (hn:n≤N) {q:ℝ} (hq:q∈Z4 0 1)
    (θ:Fin n→Bool) :
    QaE q (Qcb hn hq θ) Qdb
      (((Z20 θ).map QbG).flatten):=by
  intro F
  rw [QoR hq]
  exact QkP hn hq θ (fun a => F (Qfl a))
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {α:Type*} [Fintype α]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]
theorem QgJ (P:FiniteLaw α) (Q:FiniteLaw β) (F:α→β→ℝ) :
    P.expect (fun a => Q.expect (F a))=Q.expect (fun b => P.expect (fun a => F a b)):=by
  simp only [expect,Z3]
  rw [Z17]
  apply Z2 rfl
  intro b _
  apply Z2 rfl
  intro a _
  ring
end FiniteLaw
variable {α:Type*} [Fintype α]
end TraceReconstruction
namespace TraceReconstruction
open scoped Classical
variable {α:Type*} [Fintype α]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QaS {n:ℕ} (w:Fin n→List Bool):List Bool:=(Z20 w).flatten
theorem Qgz {n:ℕ} (w:Fin (n+1)→List Bool) :
    QaS w=w 0++QaS (fun i => w i.succ):=by
  simp only [QaS,Z65,List.flatten_cons]
theorem Qgx {α:Type*} [Fintype α]
    {n:ℕ} {q:ℝ} (P:Fin n→FiniteLaw α) (f:α→List Bool) (w:Fin n→List Bool)
    (h:∀i,QaE q (P i) f (w i)) :
    QaE q (FiniteLaw.QaR P) (fun a => QaS (fun i => f (a i)))
      (QaS w):=by
  induction n with
  | zero =>
    intro F
    change (FiniteLaw.QaR P).expect (fun _ => F [])=F []
    exact FiniteLaw.Qbi _ _
  | succ n ih =>
    intro F
    rw [FiniteLaw.Qeh,Qgz,Qep]
    have hj (a:α) (x:Fin n→α) :
        QaS (fun i => f ((Z15 a x:Fin (n+1)→α) i))=f a++QaS (fun i => f (x i)):=by
      rw [Qgz]
      simp only [Z54,Z55]
    simp_rw [hj]
    have ht:=ih (fun i => P i.succ) (fun i => w i.succ) (fun i => h i.succ)
    calc
      _=(P 0).expect (fun a => Qay q (QaS (fun i => w i.succ))
          (fun t => F (f a++t))):=by
        congr 1
        funext a
        exact ht (fun t => F (f a++t))
      _=_:=h 0 (fun t => Qay q (QaS (fun i => w i.succ)) (fun u => F (t++u)))
theorem Qgy {n:ℕ} (w:List Bool) (k:Fin n→ℕ) :
    QaS (fun i => Qal w (k i))=Qal w (∑i,k i):=by
  change (Z20 (Qal w ∘ k)).flatten=_
  rw [←List.map_ofFn,Qph,List.sum_ofFn]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
end TraceReconstruction
universe u
namespace TraceReconstruction
open scoped Classical
variable {α:Type u} [Fintype α]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α:Type*} [Fintype α]
theorem QqW (P Q:FiniteLaw α) :
    P.tv Q = P.expect (fun a => if Q.mass a ≤ P.mass a then 1 else 0) -
      Q.expect (fun a => if Q.mass a ≤ P.mass a then 1 else 0):=by
  have hz:(∑ a,(P.mass a - Q.mass a)) = 0:=by
    rw [Z39,P.total,Q.total,sub_self]
  have he (a:α) :
      |P.mass a-Q.mass a|+(P.mass a-Q.mass a) =
        2*((P.mass a-Q.mass a)*(if Q.mass a ≤ P.mass a then 1 else 0)):=by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
  have hs:=congrArg (fun f:α → ℝ => ∑ a,f a) (funext he)
  simp only [Z14,hz,add_zero,← Z3] at hs
  simp only [tv,expect]
  rw [← Z39]
  simp_rw [← sub_mul]
  linarith only [hs]
theorem QiZ (P Q:FiniteLaw α) {E:ℝ}
    (h:∀ f:α → ℝ,(∀ a,f a ∈ Z6 0 1) →
      P.expect f-Q.expect f ≤ E):P.tv Q ≤ E:=by
  rw [QqW]
  exact h _ (fun a => by split_ifs <;> norm_num)
theorem QfP (P Q:FiniteLaw α) (f:α → ℝ)
    (hf:∀ a,f a ∈ Z6 0 1):|P.expect f-Q.expect f| ≤ P.tv Q:=by
  apply abs_le.mpr
  constructor
  · have h:=QgN Q P f hf
    rw [tv_symm Q P] at h
    change Q.expect f-P.expect f ≤ P.tv Q at h
    linarith
  · exact QgN P Q f hf
end FiniteLaw
def listTraceLaw (q:ℝ) (hq:q ∈ Z6 0 1) (w:List Bool)
    (M:ℕ) (hw:w.length ≤ M):FiniteLaw (BoundedTrace M) :=
  (maskLaw (n:=w.length) q hq).map (fun a =>
    ⟨traceOfMask w.get a,QdM _
      ((QeA w.get a).trans hw)⟩)
theorem Qeq (q:ℝ) (hq:q ∈ Z6 0 1) (w:List Bool)
    (M:ℕ) (hw:w.length ≤ M) (F:List Bool → ℝ) :
    (listTraceLaw q hq w M hw).expect (fun a => F a.val) =
      Qay q w F:=by
  rw [listTraceLaw,FiniteLaw.expect_map]
  have h:=Qhy q w.get F
  rw [List.ofFn_get] at h
  exact h.symm
theorem Qcv (q:ℝ) (hq:q ∈ Z6 0 1) (w:List Bool)
    (M:ℕ) (hw:w.length ≤ M) :
    QaE q (listTraceLaw q hq w M hw) Subtype.val w :=
  Qeq q hq w M hw
def QcJ (q:ℝ) (hq:q ∈ Z6 0 1) (x y:List Bool):ℝ :=
  let M:=max x.length y.length
  FiniteLaw.overlap (listTraceLaw q hq x M (le_max_left _ _))
    (listTraceLaw q hq y M (le_max_right _ _))
theorem QfR {α:Type*} [Fintype α]
    {q:ℝ} (hq:q ∈ Z6 0 1) (P Q:FiniteLaw α) (decode:α → List Bool)
    (x y:List Bool) (Ex Ey:ℝ) (M:ℕ) (hx:x.length ≤ M) (hy:y.length ≤ M)
    (hP:Qbk q P decode x Ex)
    (hQ:Qbk q Q decode y Ey) :
    (listTraceLaw q hq x M hx).tv (listTraceLaw q hq y M hy) ≤ P.tv Q+Ex+Ey:=by
  apply FiniteLaw.QiZ
  intro f hf
  let F:List Bool → ℝ:=fun t => if h:t ∈ traceSpace M then f ⟨t,h⟩ else 0
  have hF:∀ t,F t ∈ Z6 0 1:=by
    intro t
    dsimp [F]
    split_ifs with h
    · exact hf ⟨t,h⟩
    · norm_num
  have hFx:(listTraceLaw q hq x M hx).expect f = Qay q x F:=by
    rw [← Qeq q hq x M hx F]
    congr 1
    funext t
    simp only [F,dif_pos t.property]
  have hFy:(listTraceLaw q hq y M hy).expect f = Qay q y F:=by
    rw [← Qeq q hq y M hy F]
    congr 1
    funext t
    simp only [F,dif_pos t.property]
  rw [hFx,hFy]
  have hp:=hP F hF
  have hq':=hQ F hF
  have ht:=FiniteLaw.QfP P Q (fun a => F (decode a)) (fun a => hF _)
  linarith [le_abs_self (P.expect (fun a => F (decode a))-Q.expect (fun a => F (decode a))),
    (abs_le.mp hp).1,(abs_le.mp hp).2,(abs_le.mp hq').1,(abs_le.mp hq').2]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ:Type*} [Fintype α] [Fintype β] [Fintype γ]
def joint (P:FiniteLaw α) (K:α → FiniteLaw β):FiniteLaw (α × β) where
  mass z:=P.mass z.1 * (K z.1).mass z.2
  nonneg z:=mul_nonneg (P.nonneg _) ((K _).nonneg _)
  total:=by
    rw [Z32]
    simp_rw [← Z3,(K _).total,mul_one]
    exact P.total
theorem Qlk (P:FiniteLaw α) (K:α → FiniteLaw β) (F:α × β → ℝ) :
    (P.joint K).expect F = P.expect (fun a => (K a).expect (fun b => F (a,b))):=by
  simp only [expect,joint,Z32,Z3,mul_assoc]
theorem Qll (P:FiniteLaw α) (K:α → FiniteLaw β) (F:β → ℝ) :
    (P.mixture K).expect F = P.expect (fun a => (K a).expect F):=by
  simp only [expect,mixture,Z33,Z3,mul_assoc]
  exact Z17
theorem QkN {n:ℕ} (P:Fin n → FiniteLaw α)
    (f:Fin n → α → β) :
    (QaR P).map (fun a i => f i (a i)) =
      QaR (fun i => (P i).map (f i)):=by
  apply FiniteLaw.ext
  funext b
  rw [map_mass]
  change (∑ a:Fin n → α,if (fun i => f i (a i)) = b then ∏ i,(P i).mass (a i) else 0) =
    ∏ i,((P i).map (f i)).mass (b i)
  simp_rw [map_mass]
  rw [Z43]
  apply Z2 rfl
  intro a _
  by_cases hab:(fun i => f i (a i)) = b
  · rw [if_pos hab]
    apply Z71 rfl
    intro i _
    rw [if_pos (congrFun hab i)]
  · rw [if_neg hab]
    symm
    have hi:∃ i,f i (a i) ≠ b i:=by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i,hi⟩:=hi
    exact Z69 (Z21 i) (if_neg hi)
theorem QnV (P Q H:FiniteLaw α) {ω:ℝ} (hω:0 ≤ ω)
    (hP:∀ a,ω*H.mass a ≤ P.mass a) (hQ:∀ a,ω*H.mass a ≤ Q.mass a)
    (b:Bool) :
    (Qft P Q H hω hP hQ b).map Prod.snd = Qcl P Q b:=by
  apply FiniteLaw.ext
  funext z
  rw [map_mass,Z32]
  simp only [Qft]
  simp_rw [Finset.sum_ite_eq']
  simp only [Z21,ite_true]
  exact QnX P Q H ω b z
end FiniteLaw
variable {Side Leaf:Type*} [Fintype Side] [Fintype Leaf] {m n:ℕ}
structure QaB (Side:Type*) [Fintype Side] (m:ℕ) where
  first:Fin m → FiniteLaw Side
  second:Fin m → FiniteLaw Side
  common:Fin m → FiniteLaw Side
  hiddenWeight:Fin m → ℝ
  weight_nonneg:∀ i,0 ≤ hiddenWeight i
  common_first:∀ i a,hiddenWeight i*(common i).mass a ≤ (first i).mass a
  common_second:∀ i a,hiddenWeight i*(common i).mass a ≤ (second i).mass a
abbrev Reports (Side:Type*) (m:ℕ):=Fin m → Option Bool × (Side × Side)
namespace QaB
variable (M:QaB Side m)
def reports:FiniteLaw (Reports Side m) :=
  FiniteLaw.QaR (fun i => FiniteLaw.Qdp (M.first i) (M.second i)
    (M.common i) (M.weight_nonneg i) (M.common_first i) (M.common_second i))
def Qds (b:Fin m → Bool):FiniteLaw (Reports Side m) :=
  FiniteLaw.QaR (fun i => FiniteLaw.Qft (M.first i) (M.second i)
    (M.common i) (M.weight_nonneg i) (M.common_first i) (M.common_second i) (b i))
def Qlt (m:ℕ):FiniteLaw (Fin m → Bool) :=
  (FiniteLaw.Qba none).product m
def QhV (z:Reports Side m):FiniteLaw (Fin m → Bool) :=
  FiniteLaw.QaR (fun i => FiniteLaw.Qba (z i).1)
theorem Qpm (b:Fin m → Bool) :
    (M.Qds b).map (fun z i => (z i).2) =
      FiniteLaw.QaR (fun i => FiniteLaw.Qcl (M.first i) (M.second i) (b i)):=by
  rw [Qds,FiniteLaw.QkN]
  congr 1
  funext i
  exact FiniteLaw.QnV _ _ _ _ _ _ _
end QaB
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qfz {q:ℝ} (hq:q ∈ Z4 0 1)
    (a:Qai):0 ≤ 1 + QaA q a:=by
  have hq1:1 ≤ 1/q:=(le_div_iff₀ hq.1).mpr (by simpa using hq.2.le)
  have hq0:=hq.1
  fin_cases a <;> norm_num [QaA] <;> linarith [show 2/q=2*(1/q) by ring]
theorem Qgu {u m l:ℕ} (hl:l ≤ u*m)
    {q:ℝ} (hq:q ∈ Z4 0 1) (off:Fin u → Fin m) (x:Fin l → Qai) :
    (Qbg hl q hq (QaC (periodSlot off))).mass x =
      ((Qav q hq false).product l).mass x *
        QaX (QaO l (by simpa using hl))
          (QaY (Finset.univ.image (periodSlot off))) (QaA q) x:=by
  rw [Qgw]
  congr 2
  funext S
  exact QgA (periodSlot off) S
def Qbj:ℝ:=36*Qau^2
theorem Qif:0 ≤ Qbj:=by
  unfold Qbj
  positivity
theorem Qgv {u m l:ℕ} (hl:l ≤ u*m)
    (hm:32 ≤ m) (hum:u ≤ m) {q θ:ℝ}
    (hq:q ∈ Z12 0 (1/2:ℝ))
    (hθ:θ ∈ Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (off:Fin u → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2) :
    ((Qav q ⟨hq.1,by linarith [hq.2]⟩ false).product l).expect (fun x =>
      QaX (QaO l (by simpa using hl))
        (QaY (Finset.univ.image (periodSlot off))) (QaA q) x ^ 2) ≤
      2*Z1 (Qbj/q^4 * ((u:ℝ)/m)):=by
  have hqi:q ∈ Z4 0 1:=⟨hq.1,by linarith [hq.2]⟩
  let P:=Qav q hqi false
  have hZ:P.expect (QaA q) = 0:=Qes hqi
  have h:=Qoo P (QaA q) hZ hl hm hum hq hθ hmean hv off hoff hdiff
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hv0:0 ≤ P.expect (fun a => QaA q a ^ 2) :=
    Z11 (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hv1:P.expect (fun a => QaA q a ^ 2) ≤ 2/q :=
    QoU hqi
  have hsq:(P.expect (fun a => QaA q a ^ 2))^2 ≤ (2/q)^2 :=
    pow_le_pow_left₀ hv0 hv1 2
  calc
    _ ≤ (2/q)^2*(3*Qau/q)^2*((u:ℝ)/m) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (by positivity)
    _ = _:=by unfold Qbj; field_simp; ring
theorem QkG {u v m l:ℕ}
    (hl:l ≤ u*m) (hl':l ≤ v*m) (hm:32 ≤ m) (hum:u ≤ m) (hvm:v ≤ m)
    {q θ θ':ℝ} (hq:q ∈ Z12 0 (1/2:ℝ))
    (hθ:θ ∈ Z6 (1-q^2) (1-q^2/4))
    (hθ':θ' ∈ Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hmean':((v*m:ℕ):ℝ)*θ'=l)
    (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (hv':1 ≤ ((v*m:ℕ):ℝ)*θ'*(1-θ'))
    (off:Fin u → Fin m) (off':Fin v → Fin m)
    (hoff:∀ j,|((off j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hoff':∀ j,|((off' j).val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hdiff:∀ j k,|((off j).val:ℝ)-(off k).val| ≤ 2)
    (hdiff':∀ j k,|((off' j).val:ℝ)-(off' k).val| ≤ 2) :
    Z1 (-(Qbj/q^4*((u:ℝ)/m+(v:ℝ)/m)))/128 ≤
      FiniteLaw.overlap
        (Qbg hl q ⟨hq.1,by linarith [hq.2]⟩ (QaC (periodSlot off)))
        (Qbg hl' q ⟨hq.1,by linarith [hq.2]⟩ (QaC (periodSlot off'))):=by
  have hqi:q ∈ Z4 0 1:=⟨hq.1,by linarith [hq.2]⟩
  let P:=Qav q hqi false
  let R:=QaO l (show l≤Z10 (Fin (u*m)) by simpa using hl)
  let S:=QaO l (show l≤Z10 (Fin (v*m)) by simpa using hl')
  let f:=QaY (l:=l) (Finset.univ.image (periodSlot off))
  let g:=QaY (l:=l) (Finset.univ.image (periodSlot off'))
  let G:=QaX R f (QaA q)
  let H:=QaX S g (QaA q)
  let A:=Qbj/q^4*((u:ℝ)/m)
  let B:=Qbj/q^4*((v:ℝ)/m)
  have h1:=Qgv hl hm hum hq hθ hmean hv off hoff hdiff
  have h2:=Qgv hl' hm hvm hq hθ' hmean' hv' off' hoff' hdiff'
  change (P.product l).expect (fun x => G x^2) ≤ 2*Z1 A at h1
  change (P.product l).expect (fun x => H x^2) ≤ 2*Z1 B at h2
  have ha:=Qjp P R S (QaA q)
    (Qes hqi) (Qfz hqi) f g
  change 1/32 ≤ (P.product l).expect (fun x => min (G x) (H x)) *
    (P.product l).expect (fun x => G x^2) * (P.product l).expect (fun x => H x^2) at ha
  have hG:∀x,0 ≤ G x:=Qec R f _ (Qfz hqi)
  have hH:∀x,0 ≤ H x:=Qec S g _ (Qfz hqi)
  have ho:0 ≤ (P.product l).expect (fun x => min (G x) (H x)) :=
    Z11 (fun x _ => mul_nonneg ((P.product l).nonneg _) (le_min (hG x) (hH x)))
  have hm2:0 ≤ (P.product l).expect (fun x => H x^2) :=
    Z11 (fun x _ => mul_nonneg ((P.product l).nonneg _) (sq_nonneg _))
  have hb:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ho) hm2
  have hc:=mul_le_mul_of_nonneg_left h2 (mul_nonneg ho (by positivity:0≤2*Z1 A))
  have he:(P.product l).expect (fun x => min (G x) (H x)) =
      FiniteLaw.overlap
        (Qbg hl q hqi (QaC (periodSlot off)))
        (Qbg hl' q hqi (QaC (periodSlot off'))):=by
    unfold FiniteLaw.expect FiniteLaw.overlap
    apply Z2 rfl
    intro x _
    rw [Qgu,Qgu]
    exact mul_min_of_nonneg _ _ ((P.product l).nonneg x)
  rw [← he]
  have hd:Z1 (-(A+B))/128 ≤ (P.product l).expect (fun x => min (G x) (H x)):=by
    have hx:(1:ℝ)/32 ≤ (P.product l).expect (fun x => min (G x) (H x)) * (4*Z1 (A+B)):=by
      calc
        _ ≤ _:=ha.trans (hb.trans hc)
        _ = _:=by rw [Z50]; ring
    have hp:0 < 4*Z1 (A+B):=by positivity
    calc
      _ = ((1:ℝ)/32)/(4*Z1 (A+B)):=by rw [Real.exp_neg]; ring
      _ ≤ _:=(div_le_iff₀ hp).2 hx
  convert hd using 1
  congr 2
  dsimp [A,B]
  ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qii {q θ:ℝ} {m n l:ℕ}
    (hq:q ∈ Z12 0 (1/2:ℝ)) (hm:32 ≤ m)
    (hscale:16 ≤ q^3*(m:ℝ))
    (hnlo:q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi:(n:ℝ) ≤ (m:ℝ)^2)
    (hmean:(n:ℝ)*θ=l)
    (hdev:|(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    θ ∈ Z6 (1-q^2) (1-q^2/4) ∧
    1 ≤ (n:ℝ)*θ*(1-θ) ∧
    Z0 ((n:ℝ)*θ*(1-θ)) ≤ (m:ℝ) ∧
    ((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 / ((n:ℝ)*(1-q^2/2)*(q^2/2)) ≤ 32/q^3:=by
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hq0:=hq.1
  have hq2:q^2 ≤ 1/4:=by nlinarith [hq.2]
  have hq2p:0 < q^2:=sq_pos_of_pos hq0
  have hq3:0 < q^3:=pow_pos hq0 3
  have hn0:(0:ℝ) < n:=lt_of_lt_of_le (by have hq0:=hq.1; positivity) hnlo
  have hsize:8*(m:ℝ) ≤ (n:ℝ)*q^2:=by
    have ha:=mul_le_mul_of_nonneg_right hnlo hq2p.le
    have hb:=mul_le_mul_of_nonneg_right hscale hm0.le
    nlinarith
  have hθ:θ ∈ Z6 (1-q^2) (1-q^2/4):=by
    have hl:=(abs_le.mp hdev).1
    have hr:=(abs_le.mp hdev).2
    rw [←hmean] at hl hr
    constructor
    · nlinarith
    · nlinarith
  have ht0:0 < θ:=by nlinarith [hθ.1]
  have ht1:θ < 1:=by nlinarith [hθ.2]
  have hvlo:(n:ℝ)*q^2/8 ≤ (n:ℝ)*θ*(1-θ):=by
    have hlow:(1:ℝ)/2 ≤ θ:=by linarith [hθ.1]
    have hhigh:q^2/4 ≤ 1-θ:=by linarith [hθ.2]
    have hp:=mul_le_mul hlow hhigh (by positivity:(0:ℝ)≤q^2/4) ht0.le
    have hp':=mul_le_mul_of_nonneg_left hp hn0.le
    nlinarith
  have hv:1 ≤ (n:ℝ)*θ*(1-θ):=by
    have hm32:(32:ℝ) ≤ m:=by exact_mod_cast hm
    linarith
  have hvhi:(n:ℝ)*θ*(1-θ) ≤ (m:ℝ)^2:=by
    have hprod:θ*(1-θ) ≤ 1:=by nlinarith [sq_nonneg θ]
    have hh:=mul_le_mul_of_nonneg_left hprod hn0.le
    nlinarith
  have hsqrt:Z0 ((n:ℝ)*θ*(1-θ)) ≤ (m:ℝ):=by
    exact (Real.sqrt_le_iff).mpr ⟨hm0.le,hvhi⟩
  have hp0:0 < 1-q^2/2:=by linarith
  have hden0:0 < (n:ℝ)*(1-q^2/2)*(q^2/2):=by positivity
  have hden:q^3*(m:ℝ)^2/8 ≤ (n:ℝ)*(1-q^2/2)*(q^2/2):=by
    have ha:=mul_le_mul_of_nonneg_right hnlo hq2p.le
    have hb:=mul_le_mul_of_nonneg_right (show (1:ℝ)/2≤1-q^2/2 by linarith)
      (mul_nonneg hn0.le (by positivity:(0:ℝ)≤q^2/2))
    nlinarith
  have hdev2:((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 ≤ 4*(m:ℝ)^2:=by
    have h:=pow_le_pow_left₀ (abs_nonneg _) hdev 2
    rw [sq_abs] at h
    nlinarith
  have hquot:((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
      ((n:ℝ)*(1-q^2/2)*(q^2/2)) ≤ 32/q^3:=by
    apply (div_le_div_iff₀ hden0 hq3).mpr
    have hh:=mul_le_mul_of_nonneg_right hdev2 hq3.le
    nlinarith
  exact ⟨hθ,hv,hsqrt,hquot⟩
theorem Qih {q:ℝ} {m n l:ℕ}
    (hq:q ∈ Z12 0 (1/2:ℝ)) (hm:32 ≤ m)
    (hscale:16 ≤ q^3*(m:ℝ))
    (hnlo:q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi:(n:ℝ) ≤ (m:ℝ)^2)
    (hdev:|(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    Z1 (-32/q^3)/(12*(m:ℝ)) ≤ Qaa n (1-Qaq q) l:=by
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hn0:(0:ℝ) < n:=lt_of_lt_of_le (by have hq0:=hq.1; positivity) hnlo
  let θ:ℝ:=(l:ℝ)/n
  have hmean:(n:ℝ)*θ=l:=by dsimp [θ]; field_simp
  obtain ⟨ht,hv,hsqrt,hquot⟩:=Qii hq hm hscale hnlo hnhi hmean hdev
  have hq2:q^2 ≤ 1/4:=by nlinarith [hq.1,hq.2]
  have hq2p:0 < q^2:=sq_pos_of_pos hq.1
  have ht':θ ∈ Z4 0 1:=⟨by nlinarith [ht.1],by nlinarith [ht.2]⟩
  have hp:1-q^2/2 ∈ Z4 0 1:=⟨by linarith,by linarith⟩
  have hl:l ≤ n:=by
    have h:=mul_le_mul_of_nonneg_left ht'.2.le hn0.le
    rw [hmean,mul_one] at h
    exact_mod_cast h
  have hmass:=QjO n l ht' hp hl hmean hv
  have hden:0 < 12*Z0 ((n:ℝ)*θ*(1-θ)):=by positivity
  have hexp:Z1 (-32/q^3) ≤ Z1 (-((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
      ((n:ℝ)*(1-q^2/2)*(1-(1-q^2/2)))):=by
    apply Real.exp_le_exp.mpr
    have he:1-(1-q^2/2)=q^2/2:=by ring
    rw [he]
    simpa only [neg_div] using neg_le_neg hquot
  calc
    _ ≤ Z1 (-((l:ℝ)-(n:ℝ)*(1-q^2/2))^2 /
        ((n:ℝ)*(1-q^2/2)*(1-(1-q^2/2)))) / (12*Z0 ((n:ℝ)*θ*(1-θ))):=by
      exact div_le_div₀ (Z49 _) hexp hden (by nlinarith)
    _ ≤ _:=by simpa only [Qaq] using hmass
def QaI (q:ℝ) (m:ℕ):ℕ:=⌊q*(m:ℝ)⌋₊
theorem Qmp {q:ℝ} {m:ℕ}
    (hq:q ∈ Z12 0 (1/2:ℝ)) (hm:32 ≤ m)
    (hscale:16 ≤ q^3*(m:ℝ)) :
    q*(m:ℝ)/2 ≤ (QaI q m:ℝ) ∧
    (QaI q m:ℝ) ≤ q*(m:ℝ) ∧ QaI q m+1 ≤ m:=by
  have hm0:(0:ℝ) ≤ m:=Z19 _
  have hm32:(32:ℝ) ≤ m:=by exact_mod_cast hm
  have hq0:=hq.1
  have hq2:q^2 ≤ 1:=by nlinarith [hq.2]
  have hqm:2 ≤ q*(m:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right hq2 (mul_nonneg hq0.le hm0)
    nlinarith
  have hlow:=Nat.lt_floor_add_one (q*(m:ℝ))
  have hhigh:=Nat.floor_le (mul_nonneg hq0.le hm0)
  change q*(m:ℝ) < (QaI q m:ℝ)+1 at hlow
  change (QaI q m:ℝ) ≤ q*(m:ℝ) at hhigh
  refine ⟨by linarith,hhigh,?_⟩
  have hh:=mul_le_mul_of_nonneg_right hq.2 hm0
  have:(QaI q m:ℝ)+1 ≤ (m:ℝ):=by linarith
  exact_mod_cast this
def QdB {m:ℕ} (k:ℕ) (p:ℝ) (hp:p ∈ Z6 0 1) (j:Fin m) :
    Fin ((k+1)*m+1) :=
  ⟨⌊p*((k*m:ℕ):ℝ)⌋₊+j.val,by
    have ha:(⌊p*((k*m:ℕ):ℝ)⌋₊:ℝ) ≤ ((k*m:ℕ):ℝ):=by
      exact (Nat.floor_le (mul_nonneg hp.1 (Z19 _))).trans
        (mul_le_of_le_one_left (Z19 _) hp.2)
    have ha':⌊p*((k*m:ℕ):ℝ)⌋₊ ≤ k*m:=by exact_mod_cast ha
    have hj:=j.isLt
    rw [Nat.add_mul,one_mul]
    omega⟩
theorem QkA {m:ℕ} (k:ℕ) (p:ℝ) (hp:p ∈ Z6 0 1) :
    Z28 (QdB (m:=m) k p hp):=by
  intro a b h
  have hv:=congrArg Fin.val h
  simp only [QdB,Nat.add_left_cancel_iff] at hv
  exact Z34 hv
theorem Qkz {m:ℕ} (k:ℕ) (p:ℝ) (hp:p ∈ Z6 0 1)
    (j:Fin m) :
    |((QdB k p hp j).val:ℝ)-((k*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) ∧
    |((QdB k p hp j).val:ℝ)-(((k+1)*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ):=by
  have hm:(1:ℝ) ≤ m:=by exact_mod_cast (Z68 (Z91 j.isLt))
  have hj:(j.val:ℝ) < m:=by exact_mod_cast j.isLt
  have hj0:(0:ℝ) ≤ j.val:=Z19 _
  have ha:=Nat.floor_le (mul_nonneg hp.1 (Z19 (k*m)))
  have hb:=Nat.lt_floor_add_one (p*((k*m:ℕ):ℝ))
  have hp0:=hp.1
  have hp1:=hp.2
  have hmp:0 ≤ (m:ℝ)*p:=mul_nonneg (Z19 _) hp0
  have hmp':(m:ℝ)*p ≤ m:=mul_le_of_le_one_right (Z19 _) hp1
  change |((⌊p*((k*m:ℕ):ℝ)⌋₊+j.val:ℕ):ℝ)-((k*m:ℕ):ℝ)*p| ≤ _ ∧
    |((⌊p*((k*m:ℕ):ℝ)⌋₊+j.val:ℕ):ℝ)-(((k+1)*m:ℕ):ℝ)*p| ≤ _
  have hn:(((k+1)*m:ℕ):ℝ)=((k*m:ℕ):ℝ)+(m:ℝ):=by push_cast; ring
  rw [hn]
  push_cast
  constructor <;> apply abs_le.mpr <;> constructor <;> push_cast at ha hb <;> nlinarith
end TraceReconstruction
namespace TraceReconstruction
open scoped Classical
theorem QnR (n:ℕ) :
    (List.replicate n [false,true]).flatten = Qbq n:=by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,Qbq,ih]
theorem QoO {m:ℕ} (off:Fin m) :
    (Z20 (fun j:Fin m => QbG (decide (j=off)))).flatten =
      Qam m off.val:=by
  induction m with
  | zero => exact Fin.elim0 off
  | succ m ih =>
    refine Z38 ?_ (fun d => ?_) off
    · simp [Z65,QbG,Qam,Qbq,QnR]
    · rw [Z65,List.flatten_cons]
      have hf:QbG (decide ((0:Fin (m+1))=d.succ))=[false,true]:=by
        simp [QbG,Ne.symm (Fin.succ_ne_zero d)]
      rw [hf]
      simp only [Fin.succ_inj]
      rw [ih d]
      simp [Qam,Qbq,Nat.sub_sub,Nat.add_comm]
theorem Qoj {u m:ℕ} (off:Fin u → Fin m) (i:Fin u) (j:Fin m) :
    (⟨i.val*m+j.val,by
      have hi:=Z51 m (Z68 i.isLt)
      have hj:=j.isLt
      nlinarith⟩:Fin (u*m)) ∈ Set.range (periodSlot off) ↔ j=off i:=by
  constructor
  · rintro ⟨a,ha⟩
    have hval:=congrArg Fin.val ha
    change a.val*m+(off a).val=i.val*m+j.val at hval
    have hm:0 < m:=Z91 j.isLt
    have hdiv:=congrArg (fun k:ℕ => k/m) hval
    simp only [Nat.mul_comm _ m,Nat.mul_add_div hm,Nat.div_eq_of_lt (off a).isLt,
      Nat.div_eq_of_lt j.isLt,add_zero] at hdiv
    have hai:a=i:=Z34 hdiv
    subst a
    apply Z34
    omega
  · intro h
    refine ⟨i,?_⟩
    apply Z34
    simp only [periodSlot]
    exact congrArg (fun k:Fin m => i.val*m+k.val) h.symm
theorem Qid {u m:ℕ} (off:Fin u → Fin m) :
    (((Z20 (QaC (periodSlot off))).map QbG).flatten) =
      Qbn m u off:=by
  rw [List.map_ofFn,List.ofFn_mul]
  rw [List.flatten_flatten,List.map_ofFn]
  unfold Qbn
  congr 1
  apply congrArg Z20
  funext i
  simp only [Z67]
  have he:(fun j:Fin m => QbG (QaC (periodSlot off)
      ⟨i.val*m+j.val,by
        have hi:=Z51 m (Z68 i.isLt)
        have hj:=j.isLt
        nlinarith⟩)) = fun j:Fin m => QbG (decide (j=off i)):=by
    funext j
    simp only [QaC,Qoj]
  rw [he]
  exact QoO (off i)
theorem Qfv {u m:ℕ} (off:Fin m) :
    Qbn m u (fun _ => off) = Qal (Qam m off.val) u:=by
  simp only [Qbn,List.ofFn_const,Qal]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qig {q:ℝ} {m n l:ℕ}
    (hq:q ∈ Z12 0 (1/2:ℝ)) (hm:32 ≤ m)
    (hscale:16 ≤ q^3*(m:ℝ))
    (hnlo:q*(m:ℝ)^2/2 ≤ (n:ℝ)) (hnhi:(n:ℝ) ≤ (m:ℝ)^2)
    (hdev:|(l:ℝ)-(n:ℝ)*(1-q^2/2)| ≤ 2*(m:ℝ)) :
    ∃ θ:ℝ,l ≤ n ∧ θ ∈ Z6 (1-q^2) (1-q^2/4) ∧
      (n:ℝ)*θ=l ∧ 1 ≤ (n:ℝ)*θ*(1-θ):=by
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hq0:=hq.1
  have hn0:(0:ℝ) < n:=lt_of_lt_of_le (by positivity) hnlo
  let θ:ℝ:=(l:ℝ)/n
  have hmean:(n:ℝ)*θ=l:=by dsimp [θ]; field_simp
  obtain ⟨ht,hv,_,_⟩:=Qii hq hm hscale hnlo hnhi hmean hdev
  have hl:l ≤ n:=by
    have ht1:θ ≤ 1:=by nlinarith [ht.2,sq_nonneg q]
    have hh:=mul_le_mul_of_nonneg_left ht1 hn0.le
    rw [hmean,mul_one] at hh
    exact_mod_cast hh
  exact ⟨θ,hl,ht,hmean,hv⟩
def QaV (q:ℝ):ℝ :=
  Z1 (-(32+3*Qbj)/q^3)/1536
theorem Qhj (q:ℝ):0 < QaV q:=by
  unfold QaV
  positivity
theorem Qmj {q:ℝ} (hq:0 < q) :
    QaV q < 1/8:=by
  have hx:-(32+3*Qbj)/q^3 ≤ 0:=by
    have hc:=Qif
    apply div_nonpos_of_nonpos_of_nonneg <;> nlinarith [pow_pos hq 3]
  have he:Z1 (-(32+3*Qbj)/q^3) ≤ 1:=by
    simpa using Real.exp_le_exp.mpr hx
  unfold QaV
  linarith
theorem QmA {q:ℝ} {m:ℕ}
    (hq:q ∈ Z12 0 (1/2:ℝ)) (hm:32 ≤ m)
    (hscale:16 ≤ q^3*(m:ℝ)) (off:Fin m)
    (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3) :
    let k:=QaI q m
    QaV q ≤ FiniteLaw.overlap
      (Qcb (N:=(k+1)*m) (Z51 m (Nat.le_succ k))
        ⟨hq.1,by linarith [hq.2]⟩ (QaC (periodSlot (u:=k) (fun _ => off))))
      (Qcb (N:=(k+1)*m) le_rfl
        ⟨hq.1,by linarith [hq.2]⟩ (QaC (periodSlot (u:=k+1) (fun _ => off)))):=by
  let k:=QaI q m
  let N:=(k+1)*m
  have hq0:=hq.1
  have hqi:q ∈ Z4 0 1:=⟨hq.1,by linarith [hq.2]⟩
  have hm0:(0:ℝ) < m:=by exact_mod_cast (show 0 < m by omega)
  have hq2:q^2 ≤ 1/4:=by nlinarith [hq.2]
  let p:=1-Qaq q
  have hp:p ∈ Z6 0 1:=Qdq hqi
  have hp':p=1-q^2/2:=rfl
  obtain ⟨hklo,hkhi,hk1⟩:=Qmp hq hm hscale
  change q*(m:ℝ)/2 ≤ (k:ℝ) at hklo
  change (k:ℝ) ≤ q*(m:ℝ) at hkhi
  change k+1 ≤ m at hk1
  have hk:k ≤ m:=by omega
  have hnlo:q*(m:ℝ)^2/2 ≤ ((k*m:ℕ):ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right hklo hm0.le
    push_cast
    nlinarith
  have hnhi:((k*m:ℕ):ℝ) ≤ (m:ℝ)^2:=by
    exact_mod_cast (show k*m ≤ m^2 by simpa [pow_two] using Z51 m hk)
  have hNlo:q*(m:ℝ)^2/2 ≤ (N:ℝ):=by
    exact hnlo.trans (by exact_mod_cast Z51 m (Nat.le_succ k))
  have hNhi:(N:ℝ) ≤ (m:ℝ)^2:=by
    exact_mod_cast (show N ≤ m^2 by simpa [N,pow_two] using Z51 m hk1)
  have hqm:1 ≤ q*(m:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right (show q^2≤1 by linarith) (mul_nonneg hq0.le hm0.le)
    nlinarith
  have hrate:(k:ℝ)/(m:ℝ)+((k+1:ℕ):ℝ)/(m:ℝ) ≤ 3*q:=by
    rw [←add_div]
    apply (div_le_iff₀ hm0).mpr
    push_cast
    nlinarith
  have harg:Qbj/q^4*((k:ℝ)/m+((k+1:ℕ):ℝ)/m) ≤
      3*Qbj/q^3:=by
    calc
      _ ≤ Qbj/q^4*(3*q) :=
        mul_le_mul_of_nonneg_left hrate (div_nonneg Qif (by positivity))
      _ = _:=by field_simp
  let C₁:=Qcs (N:=N) (Z51 m (Nat.le_succ k)) p hp
  let C₂:=Qcs (N:=N) le_rfl p hp
  let K:=QbZ hqi (QaC (periodSlot (u:=k) (fun _ => off))) (N:=N)
  let L:=QbZ hqi (QaC (periodSlot (u:=k+1) (fun _ => off))) (N:=N)
  let f:Fin (N+1) → ℝ:=fun l => min (C₁.mass l) (C₂.mass l) * FiniteLaw.overlap (K l) (L l)
  let a:ℝ:=Z1 (-32/q^3)/(12*(m:ℝ))
  let b:ℝ:=Z1 (-(3*Qbj)/q^3)/128
  have ha0:0 ≤ a:=by dsimp [a]; positivity
  have hb0:0 ≤ b:=by dsimp [b]; positivity
  have hf0:∀l,0 ≤ f l:=fun l =>
    mul_nonneg (le_min (C₁.nonneg l) (C₂.nonneg l)) (FiniteLaw.QnT _ _)
  let ix:Fin m → Fin (N+1):=QdB k p hp
  have hterm:∀j:Fin m,a*b ≤ f (ix j):=by
    intro j
    let l:=(ix j).val
    have hd:=Qkz k p hp j
    change |(l:ℝ)-((k*m:ℕ):ℝ)*p| ≤ 2*(m:ℝ) ∧ |(l:ℝ)-(N:ℝ)*p| ≤ 2*(m:ℝ) at hd
    rw [hp'] at hd
    obtain ⟨θ,hl,hθ,hmean,hv⟩:=Qig hq hm hscale hnlo hnhi hd.1
    obtain ⟨θ',hl',hθ',hmean',hv'⟩:=Qig hq hm hscale hNlo hNhi hd.2
    have hm1:=Qih hq hm hscale hnlo hnhi hd.1
    have hm2:=Qih hq hm hscale hNlo hNhi hd.2
    have hmin:a ≤ min (C₁.mass (ix j)) (C₂.mass (ix j)):=le_min hm1 hm2
    have hc:=QkG hl hl' hm hk hk1 hq hθ hθ' hmean hmean' hv hv'
      (fun _ => off) (fun _ => off) (fun _ => hoff) (fun _ => hoff)
      (fun _ _ => by simp) (fun _ _ => by simp)
    have hb:b ≤ FiniteLaw.overlap (K (ix j)) (L (ix j)):=by
      dsimp only [K,L,QbZ]
      rw [dif_pos hl,dif_pos hl']
      refine le_trans ?_ hc
      apply div_le_div_of_nonneg_right _ (by norm_num:(0:ℝ)≤128)
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg harg
    exact mul_le_mul hmin hb hb0 (le_min (C₁.nonneg _) (C₂.nonneg _))
  have hsub:(∑j:Fin m,f (ix j)) ≤ ∑l:Fin (N+1),f l:=by
    have hi:=QkA (m:=m) k p hp
    calc
      _ = ∑l ∈ Finset.univ.image ix,f l:=by
        rw [Finset.sum_image]
        exact fun a _ b _ hab => hi hab
      _ ≤ _:=Z40 (Z56 _)
        (fun l _ _ => hf0 l)
  have hsum:(m:ℝ)*(a*b) ≤ ∑l:Fin (N+1),f l:=by
    calc
      _ = ∑_j:Fin m,a*b:=by simp
      _ ≤ ∑j:Fin m,f (ix j):=Z7 (fun j _ => hterm j)
      _ ≤ _:=hsub
  have he:(m:ℝ)*(a*b)=QaV q:=by
    dsimp [a,b,QaV]
    rw [div_mul_div_comm,←Z50]
    have hx:-32/q^3 + -(3*Qbj)/q^3 = -(32+3*Qbj)/q^3:=by ring
    rw [hx]
    field_simp
    ring
  rw [he] at hsum
  exact hsum.trans (FiniteLaw.QnU C₁ C₂ K L)
theorem QpZ {α:Type*} [Fintype α] {q:ℝ}
    (hq:q ∈ Z6 0 1) (P Q:FiniteLaw α) (decode:α → List Bool)
    (x y:List Bool) (hP:QaE q P decode x)
    (hQ:QaE q Q decode y) :
    P.overlap Q ≤ QcJ q hq x y:=by
  have h:=QfR hq P Q decode x y 0 0
    (max x.length y.length) (le_max_left _ _) (le_max_right _ _)
    hP.QbY hQ.QbY
  simp only [add_zero] at h
  unfold QcJ
  rw [FiniteLaw.QdN,FiniteLaw.QdN]
  linarith
theorem QmH {q:ℝ} {m:ℕ}
    (hq:q ∈ Z12 0 (1/2:ℝ)) (hm:32 ≤ m)
    (hscale:16 ≤ q^3*(m:ℝ)) (off:Fin m)
    (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3) :
    let k:=QaI q m
    QaV q ≤ QcJ q ⟨hq.1.le,by linarith [hq.2]⟩
      (Qal (Qam m off.val) k)
      (Qal (Qam m off.val) (k+1)):=by
  let k:=QaI q m
  have hqi:q ∈ Z4 0 1:=⟨hq.1,by linarith [hq.2]⟩
  have hca:=QeW (N:=(k+1)*m)
    (Z51 m (Nat.le_succ k)) hqi
    (QaC (periodSlot (u:=k) (fun _ => off)))
  have hcb:=QeW (N:=(k+1)*m) le_rfl hqi
    (QaC (periodSlot (u:=k+1) (fun _ => off)))
  rw [Qid,Qfv] at hca hcb
  exact (QmA hq hm hscale off hoff).trans
    (QpZ ⟨hq.1.le,by linarith [hq.2]⟩ _ _ _ _ _ hca hcb)
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QcK {m:ℕ} (off:Fin m)
    (hi:1  ≤  off.val ∧ off.val + 1 < m) (a:Fin 3):Fin m :=
  ⟨off.val+a.val-1,by have ha:=a.isLt; omega⟩
theorem QnO {m:ℕ} (off:Fin m)
    (hi:1  ≤  off.val ∧ off.val + 1 < m) (a:Fin 3) :
    (QcK off hi a).val+1=off.val+a.val:=by
  dsimp [QcK]
  omega
theorem Qfs {m:ℕ} (off:Fin m)
    (hi:1  ≤  off.val ∧ off.val + 1 < m) (a:Fin 3) :
    |((QcK off hi a).val:ℝ)-(off.val:ℝ)|  ≤  1:=by
  have he:=QnO off hi a
  have ha:(a.val:ℝ)  ≤  2:=by exact_mod_cast (show a.val ≤ 2 by omega)
  have ha0:(0:ℝ)  ≤  a.val:=Z19 _
  have he':((QcK off hi a).val:ℝ)+1=(off.val:ℝ)+a.val:=by exact_mod_cast he
  rw [abs_le]
  constructor <;> linarith
theorem QpG {u m:ℕ} (off:Fin m)
    (hi:1  ≤  off.val ∧ off.val + 1 < m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (a:Fin u → Fin 3) :
    shiftedTag (periodSlot (fun _ => off)) hsafe a =
      periodSlot (fun i => QcK off hi (a i)):=by
  funext i
  apply Z34
  change i.val*m+off.val+(a i).val-1=i.val*m+(off.val+(a i).val-1)
  omega
theorem QpN {u m:ℕ} (off:Fin m)
    (hi:1  ≤  off.val ∧ off.val + 1 < m)
    (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (s:ℕ) (X:ℤ) (τ:ℝ) :
    ∃ off':Fin u → Fin m,
      QaN off hsafe s X τ = periodSlot off' ∧
      (∀j,|((off' j).val:ℝ)-(m:ℝ)/2| ≤ 3) ∧
      (∀j k,|((off' j).val:ℝ)-(off' k).val| ≤ 2):=by
  let a:Fin u → Fin 3:=fun j =>
    motifShift (QaT s ((j.val:ℤ)-X)) ((Qak s).coeff ((j.val:ℤ)-X)) τ
  refine ⟨fun j => QcK off hi (a j),QpG off hi hsafe a,?_,?_⟩
  · intro j
    have h:=Qfs off hi (a j)
    have ht:=abs_add_le (((QcK off hi (a j)).val:ℝ)-(off.val:ℝ))
      ((off.val:ℝ)-(m:ℝ)/2)
    rw [sub_add_sub_cancel] at ht
    linarith
  · intro j k
    have hj:=Qfs off hi (a j)
    have hk:=Qfs off hi (a k)
    rw [abs_le] at hj hk ⊢
    constructor <;> linarith
theorem Qij {q:ℝ} (hq:q∈Z4 0 1) (k:ℕ) :
    (Qav q hq false).expect (fun z => |QaA q z|^(2*k))  ≤ 
      (2/q)^(2*k):=by
  calc
    _  ≤  (Qav q hq false).expect (fun _ => (2/q)^(2*k)):=by
      apply Z7
      intro z _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (QoS hq z) _) ((Qav q hq false).nonneg z)
    _ = _:=(Qav q hq false).Qbi _
theorem QgC {Ω:Type*} [Fintype Ω] {n:ℕ}
    (P:FiniteLaw Ω) (A:Ω → (Fin n → Bool) → ℝ) (r:ℕ) :
    (∑σ:Fin n → Bool,if Qap σ=r then
      (P.expect (fun ω => A ω σ))^2 else 0)  ≤ 
    P.expect (fun ω => ∑σ:Fin n → Bool,
      if Qap σ=r then (A ω σ)^2 else 0):=by
  unfold FiniteLaw.expect
  simp_rw [Z3]
  rw [Z17]
  apply Z7
  intro σ _
  by_cases h:Qap σ=r
  · simp only [if_pos h]
    have H:=Qjf Z16 P.mass (fun ω => A ω σ) (fun ω => P.nonneg ω)
    simpa only [P.total,one_mul] using H
  · simp only [if_neg h,mul_zero,Z102,le_refl]
theorem QkT {n:ℕ} (A B:(Fin n → Bool) → ℝ) (r:ℕ) :
    (∑σ:Fin n → Bool,if Qap σ=r then (A σ-B σ)^2 else 0)  ≤ 
    2*(∑σ:Fin n → Bool,if Qap σ=r then A σ^2 else 0)+
    2*(∑σ:Fin n → Bool,if Qap σ=r then B σ^2 else 0):=by
  simp only [Z3,←Z14]
  apply Z7
  intro σ _
  split_ifs <;> nlinarith [sq_nonneg (A σ+B σ)]
theorem QhH {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) (σ:Fin l → Bool) :
    QaD hl off hsafe π s τ σ =
      (QdW π hπ hπsum).expect (fun X =>
        Qbm (QaO l (by simpa using hl))
          (QaY (Finset.univ.image (QaN off hsafe s X.val τ))) σ):=by
  unfold QaD FiniteLaw.expect QdW
  exact (Finset.sum_coe_sort _ _).symm
theorem QhG {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπsum:∑X∈π.coeff.support,π.coeff X=1) (s:ℕ) (τ:ℝ) :
    QaD hl off hsafe π s τ (fun _ => false)=1:=by
  simp only [QaD,QfS,mul_one,hπsum]
theorem Qfn {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hru:r ≤ u) (hm:32 ≤ m) (hum:u ≤ m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) {q θ:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) :
    (∑σ:Fin l → Bool,if Qap σ=r then
      (QaD hl off hsafe π s τ σ)^2 else 0)  ≤ 
      ((3*Qau/q)*Z0 ((u:ℝ)/((m:ℝ)*r)))^r:=by
  simp_rw [QhH hl off hsafe π hπ hπsum]
  refine (QgC _ _ r).trans ?_
  calc
    _  ≤  (QdW π hπ hπsum).expect (fun _ =>
        ((3*Qau/q)*Z0 ((u:ℝ)/((m:ℝ)*r)))^r):=by
      apply FiniteLaw.QaZ
      intro X
      obtain ⟨d,hd,hnear,hclose⟩:=QpN off hi hoff hsafe s X.val τ
      rw [hd]
      exact Qib hl hr hru hm hum hq hθ hmean hv d hnear hclose
    _ = _:=FiniteLaw.Qbi _ _
theorem Qfo {u m l r:ℕ} (hl:l ≤ u*m) (hru:u < r) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) :
    (∑σ:Fin l → Bool,if Qap σ=r then
      (QaD hl off hsafe π s τ σ)^2 else 0)=0:=by
  apply le_antisymm
  · simp_rw [QhH hl off hsafe π hπ hπsum]
    refine (QgC _ _ r).trans ?_
    simp_rw [QgB hl _ (QiF off hsafe s _ τ) hru]
    rw [FiniteLaw.Qbi]
  · exact Z11 (fun σ _ => by split_ifs <;> positivity)
theorem QpL {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπsum:∑X∈π.coeff.support,π.coeff X=1) (s:ℕ) :
    (∑σ:Fin l → Bool,if Qap σ=0 then
      (QaD hl off hsafe π s 1 σ-
        QaD hl off hsafe π s (-1) σ)^2 else 0)=0:=by
  simp_rw [Qfp]
  simp [QhG hl off hsafe π hπsum]
theorem QpJ {u m l r:ℕ}
    (hu:0 < u) (hm:128 ≤ m) (hr:0 < r) (hl:l ≤ u*m)
    (off:Fin m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 3)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (hcentral:QbI u s π)
    {θ:ℝ} (hθ:θ∈Z4 0 1) (hhalf:1/2 ≤ θ)
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM:((2*(2^s):ℕ):ℝ)<(u:ℝ)/(3*(r+1:ℝ))) :
    (∑σ:Fin l → Bool,if Qap σ=r then
      (QaD hl off hsafe π s 1 σ-
        QaD hl off hsafe π s (-1) σ)^2 else 0)  ≤ 
      8*(Z10 (Fin r → Qac):ℝ)*
        (∑k:Fin r → Qac,if Odd (Qax k) then
          Qcy u m r s π θ k else 0) +
      2*((Z10 (Qab u r):ℝ)*
        (2*(((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l * (2*Z1 (-(m:ℝ)/(1024*u))))))^2:=by
  refine (QfL _).trans ?_
  simp_rw [Qnf]
  exact QmO hu hm hr hl off hoff hsafe π hπ hπsum s hcentral
    hθ hhalf hmean hv hM
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
theorem QlD {a:ℝ} (ha:0 ≤ a) (ha1:a < 1) (N R:ℕ) :
    (∑r ∈ Z5 N,if R ≤ r then a^r else 0) ≤ a^R/(1-a):=by
  have ht:HasSum (fun n:ℕ => a^(n+R)) (a^R/(1-a)):=by
    simpa only [pow_add,mul_comm,div_eq_mul_inv] using (hasSum_geometric_of_lt_one ha ha1).mul_left (a^R)
  have hsum:(∑r ∈ Z5 N,if R ≤ r then a^r else 0) =
      ∑r ∈ (Z5 N).filter (R ≤ ·),a^r:=by
    rw [Z27]
  rw [hsum]
  calc
    _ = ∑r ∈ ((Z5 N).filter (R ≤ ·)).image (fun r => r-R),a^(r+R):=by
      rw [Finset.sum_image]
      · apply Z2 rfl
        intro r hr
        rw [Nat.sub_add_cancel (Finset.mem_filter.mp hr).2]
      · intro r hr s hs h
        dsimp only at h
        have hrR:=(Finset.mem_filter.mp hr).2
        have hsR:=(Finset.mem_filter.mp hs).2
        omega
    _ ≤ _:=by
      rw [←ht.tsum_eq]
      exact ht.summable.sum_le_tsum _ (fun _ _ => by positivity)
theorem QhQ {n R:ℕ} (A:(Fin n → Bool) → ℝ)
    (w a K:ℝ) (hw:0 ≤ w) (ha:0 ≤ a) (ha1:a < 1) (hK:0 ≤ K)
    (L:ℕ → ℝ)
    (hlow:∀r < R,(∑σ:Fin n → Bool,if Qap σ=r then A σ^2 else 0) ≤ L r)
    (hhigh:∀r,R ≤ r → w^(2*r)*(∑σ:Fin n → Bool,
      if Qap σ=r then A σ^2 else 0) ≤ K*a^r)
    (hL:∀r,0 ≤ L r) :
    QaK A w ≤ (∑r ∈ Z5 R,w^(2*r)*L r)+K*a^R/(1-a):=by
  rw [QhP]
  calc
    _ ≤ ∑r ∈ Z5 (n+1),
        ((if r < R then w^(2*r)*L r else 0)+(if R ≤ r then K*a^r else 0)):=by
      apply Z7
      intro r _
      by_cases h:r < R
      · simp only [if_pos h,if_neg (show ¬R ≤ r by omega),add_zero]
        exact mul_le_mul_of_nonneg_left (hlow r h) (by positivity)
      · simp only [if_neg h,if_pos (show R ≤ r by omega),zero_add]
        exact hhigh r (by omega)
    _ ≤ _:=by
      rw [Z14]
      apply add_le_add
      · rw [←Z27]
        exact Z40
          (by intro r hr; exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2)
          (fun r _ _ => mul_nonneg (by positivity) (hL r))
      · have he:(∑r ∈ Z5 (n+1),if R ≤ r then K*a^r else 0)=
            K*∑r ∈ Z5 (n+1),if R ≤ r then a^r else 0:=by
          rw [Z3]
          apply Z2 rfl
          intro r _
          split_ifs <;> ring
        rw [he,mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (QlD ha ha1 _ _) hK
theorem QpK {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hm:32 ≤ m) (hum:u ≤ m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) {q θ:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w:ℝ) :
    w^(2*r)*(∑σ:Fin l → Bool,if Qap σ=r then
      (QaD hl off hsafe π s 1 σ-
        QaD hl off hsafe π s (-1) σ)^2 else 0) ≤
      4*(w^2*(3*Qau/q)*Z0 ((u:ℝ)/m))^r:=by
  have hw0:0 ≤ w^(2*r):=by rw [pow_mul]; positivity
  have hp:0 ≤ 3*Qau/q:=by positivity [Qcd,hq.1]
  have hb:=QkT (QaD hl off hsafe π s 1)
    (QaD hl off hsafe π s (-1)) r
  by_cases hru:r ≤ u
  · have hplus:=Qfn hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s 1 hq hθ hmean hv
    have hminus:=Qfn hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s (-1) hq hθ hmean hv
    have hsqrt:Z0 ((u:ℝ)/((m:ℝ)*r)) ≤ Z0 ((u:ℝ)/m):=by
      apply Z24
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < m by omega))
      have hr1:(1:ℝ) ≤ r:=by exact_mod_cast hr
      nlinarith
    calc
      _ ≤ w^(2*r)*(4*((3*Qau/q)*Z0 ((u:ℝ)/((m:ℝ)*r)))^r) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [pow_mul]; positivity)
      _ ≤ w^(2*r)*(4*((3*Qau/q)*Z0 ((u:ℝ)/m))^r):=by
        gcongr
      _ = _:=by rw [pow_mul,mul_pow,mul_pow]; ring
  · rw [Qfo hl (by omega) off hsafe π hπ hπsum s 1,
      Qfo hl (by omega) off hsafe π hπ hπsum s (-1)] at hb
    have hz:(∑σ:Fin l → Bool,if Qap σ=r then
        (QaD hl off hsafe π s 1 σ-
          QaD hl off hsafe π s (-1) σ)^2 else 0)=0:=by
      apply le_antisymm (by linarith)
      exact Z11 (fun σ _ => by split_ifs <;> positivity)
    rw [hz,mul_zero]
    positivity
def Qcx (u m r s:ℕ) (π:IntSeries) (θ:ℝ) (l:ℕ):ℝ :=
  if r=0 then 0 else
    8*(Z10 (Fin r → Qac):ℝ)*
      (∑k:Fin r → Qac,if Odd (Qax k) then
        Qcy u m r s π θ k else 0) +
    2*((Z10 (Qab u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l * (2*Z1 (-(m:ℝ)/(1024*u))))))^2
theorem QfG (u m r s:ℕ) (π:IntSeries) (θ:ℝ) (l:ℕ) :
    0 ≤ Qcx u m r s π θ l:=by
  unfold Qcx
  split_ifs
  · exact le_rfl
  · apply add_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    apply Z11
    intro k _
    split_ifs
    · unfold Qcy
      split_ifs <;> apply mul_nonneg _ (Qcn _)
      all_goals dsimp only [QaW,QaJ,Qbs,QbE]
      all_goals positivity
    · exact le_rfl
theorem QpU {u m l R:ℕ} (hu:0 < u) (hm:128 ≤ m)
    (hum:u ≤ m) (hR:0 < R) (hl:l ≤ u*m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (hcentral:QbI u s π)
    {q θ w:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM:((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw:0 ≤ w) (ha:w^2*(3*Qau/q)*Z0 ((u:ℝ)/m) < 1) :
    QaK (fun σ => QaD hl off hsafe π s 1 σ-
        QaD hl off hsafe π s (-1) σ) w ≤
      (∑r ∈ Z5 R,w^(2*r)*Qcx u m r s π θ l)+
        4*(w^2*(3*Qau/q)*Z0 ((u:ℝ)/m))^R /
          (1-w^2*(3*Qau/q)*Z0 ((u:ℝ)/m)):=by
  have hq2:q^2 ≤ (1/4:ℝ):=by
    calc q^2 ≤ (1/2:ℝ)^2:=pow_le_pow_left₀ hq.1.le hq.2 2
         _ = _:=by norm_num
  have hθ0:θ∈Z4 0 1:=by constructor <;> nlinarith [hq.1,hθ.1,hθ.2]
  have hhalf:1/2 ≤ θ:=by nlinarith [hθ.1]
  apply QhQ _ w _ 4 hw (by positivity [Qcd,hq.1]) ha
    (by norm_num) (Qcx u m · s π θ l) _ _
    (fun r => QfG _ _ _ _ _ _ _)
  · intro r hr
    by_cases hr0:r=0
    · subst r
      rw [QpL hl off hsafe π hπsum s]
      exact QfG _ _ _ _ _ _ _
    · have hMr:((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(r+1:ℝ)):=by
        apply hM.trans_le
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show r+1 ≤ R+1 by omega)) (by norm_num)
      simpa only [Qcx,if_neg hr0] using QpJ hu hm (Nat.pos_of_ne_zero hr0) hl off
          (hoff.trans (by norm_num)) hsafe π hπ hπsum s hcentral hθ0 hhalf hmean hv hMr
  · intro r hr
    exact QpK hl (by omega) (by omega) hum off hi hoff hsafe π hπ
      hπsum s hq hθ hmean hv w
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
theorem QoQ {q:ℝ} (hq:q∈Z4 0 1) (z:Qai) :
    0 < (Qav q hq false).mass z:=by
  change 0 < Qbe q false z
  apply div_pos _ (Qcw hq)
  fin_cases z <;> simp [Qck,Qaq] <;> nlinarith [hq.1,hq.2]
theorem QoP {q:ℝ} (hq:q∈Z4 0 1) {l:ℕ}
    (x:Fin l → Qai):0 < ((Qav q hq false).product l).mass x :=
by
  change 0 < ∏ i,(Qav q hq false).mass (x i)
  exact Finset.prod_pos (fun _ _ => QoQ hq _)
def QbD {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (s:ℕ) (τ q:ℝ):(Fin l → Qai) → ℝ :=
  Qaj (QaD hl off hsafe π s τ) (QaA q)
theorem Qfh {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) {q:ℝ} (hq:q∈Z4 0 1) (x:Fin l → Qai) :
    0 ≤ QbD hl off hsafe π s τ q x:=by
  have h:=(Qca hl off hsafe hq π hπ hπsum s τ).nonneg x
  rw [QeU] at h
  exact nonneg_of_mul_nonneg_right h (QoP hq x)
theorem Qfg {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) {q:ℝ} (hq:q∈Z4 0 1) :
    ((Qav q hq false).product l).expect (QbD hl off hsafe π s τ q)=1:=by
  have h:=(Qca hl off hsafe hq π hπ hπsum s τ).total
  simpa only [QeU,FiniteLaw.expect,QbD] using h
theorem Qhi {u m l:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) {q:ℝ} (hq:q∈Z4 0 1) :
    Qca hl off hsafe hq π hπ hπsum s τ =
      ((Qav q hq false).product l).Qag
        (QbD hl off hsafe π s τ q)
        (Qfh hl off hsafe π hπ hπsum s τ hq)
        (Qfg hl off hsafe π hπ hπsum s τ hq):=by
  apply FiniteLaw.ext
  funext x
  exact QeU hl off hsafe hq π hπ hπsum s τ x
theorem QhT {α:Type*} {l:ℕ} (A B:(Fin l → Bool) → ℝ)
    (Z:α → ℝ) (x:Fin l → α) :
    Qaj (fun σ => A σ-B σ) Z x = Qaj A Z x-Qaj B Z x:=by
  simp only [Qaj,sub_mul,Z39]
def QbQ {l:ℕ} (A:(Fin l → Bool) → ℝ) (σ:Fin l → Bool):ℝ :=
  if σ=(fun _ => false) then 0 else A σ
theorem QnK {α:Type*} {l:ℕ} (A:(Fin l → Bool) → ℝ)
    (Z:α → ℝ) (x:Fin l → α) :
    Qaj (QbQ A) Z x=Qaj A Z x-A (fun _ => false):=by
  have he:∀σ,QbQ A σ=A σ-(if σ=(fun _ => false) then A σ else 0):=by
    intro σ
    by_cases h:σ=(fun _ => false) <;> simp [QbQ,h]
  rw [show QbQ A = (fun σ => A σ-(if σ=(fun _ => false) then A σ else 0)) from funext he,QhT]
  congr 1
  simp [Qaj,ite_mul]
theorem QnJ {l:ℕ} (A:(Fin l → Bool) → ℝ) :
    (∑σ:Fin l → Bool,if Qap σ=0 then (QbQ A σ)^2 else 0)=0:=by
  simp [Qfp,QbQ]
theorem QnI {l r:ℕ} (A:(Fin l → Bool) → ℝ) (hr:0 < r) :
    (∑σ:Fin l → Bool,if Qap σ=r then (QbQ A σ)^2 else 0)=
      ∑σ:Fin l → Bool,if Qap σ=r then (A σ)^2 else 0:=by
  apply Z2 rfl
  intro σ _
  by_cases h:σ=(fun _ => false)
  · subst σ
    simp [Qap,Ne.symm (Nat.ne_of_gt hr)]
  · simp [QbQ,h]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
theorem Qng {u m l r:ℕ} (hl:l ≤ u*m) (hr:0 < r)
    (hm:32 ≤ m) (hum:u ≤ m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) {q θ:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ)) (w:ℝ) :
    w^(2*r)*(∑σ:Fin l → Bool,if Qap σ=r then
      QaD hl off hsafe π s τ σ^2 else 0) ≤
      (w^2*(3*Qau/q)*Z0 ((u:ℝ)/m))^r:=by
  have hw:0 ≤ w^(2*r):=by rw [pow_mul]; positivity
  have hp:0 ≤ 3*Qau/q:=by positivity [Qcd,hq.1]
  by_cases hru:r ≤ u
  · have hb:=Qfn hl hr hru hm hum off hi hoff hsafe π hπ hπsum
      s τ hq hθ hmean hv
    have hsqrt:Z0 ((u:ℝ)/((m:ℝ)*r)) ≤ Z0 ((u:ℝ)/m):=by
      apply Z24
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < m by omega))
      have hr1:(1:ℝ) ≤ r:=by exact_mod_cast hr
      nlinarith
    calc
      _ ≤ w^(2*r)*((3*Qau/q)*Z0 ((u:ℝ)/((m:ℝ)*r)))^r :=
        mul_le_mul_of_nonneg_left hb hw
      _ ≤ w^(2*r)*((3*Qau/q)*Z0 ((u:ℝ)/m))^r:=by gcongr
      _ = _:=by rw [pow_mul,mul_pow,mul_pow]; ring
  · rw [Qfo hl (by omega) off hsafe π hπ hπsum s τ,mul_zero]
    positivity
theorem Qmv {u m l:ℕ} (hl:l ≤ u*m)
    (hm:32 ≤ m) (hum:u ≤ m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s:ℕ) (τ:ℝ) {q θ w:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw:0 ≤ w) (ha:w^2*(3*Qau/q)*Z0 ((u:ℝ)/m) < 1) :
    QaK (QbQ (QaD hl off hsafe π s τ)) w ≤
      (w^2*(3*Qau/q)*Z0 ((u:ℝ)/m)) /
        (1-w^2*(3*Qau/q)*Z0 ((u:ℝ)/m)):=by
  have H:=QhQ (R:=1)
    (QbQ (QaD hl off hsafe π s τ)) w _ 1 hw
    (by positivity [Qcd,hq.1]) ha (by norm_num) (fun _ => 0)
    (fun r hr => by
      have he:r=0:=by omega
      subst r
      rw [QnJ])
    (fun r hr => by
      rw [QnI _ (by omega)]
      simpa only [one_mul] using Qng hl (by omega) hm hum off
        hi hoff hsafe π hπ hπsum s τ hq hθ hmean hv w)
    (fun _ => le_rfl)
  simpa using H
theorem Qmw {u m l:ℕ} (hl:l ≤ u*m)
    (hm:32 ≤ m) (hum:u ≤ m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s k:ℕ) (hk:1 ≤ k) (τ:ℝ) {q θ w:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hw:w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (ha:w^2*(3*Qau/q)*Z0 ((u:ℝ)/m) < 1) :
    ((Qav q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).Qbh
      (fun x => QbD hl off hsafe π s τ q x-1) k ≤
      (w^2*(3*Qau/q)*Z0 ((u:ℝ)/m)) /
        (1-w^2*(3*Qau/q)*Z0 ((u:ℝ)/m)):=by
  have hq':q∈Z4 0 1:=⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he:(fun x => QbD hl off hsafe π s τ q x-1) =
      Qaj (QbQ (QaD hl off hsafe π s τ))
        (QaA q):=by
    funext x
    rw [QnK,QhG hl off hsafe π hπsum]
    rfl
  rw [he]
  apply (QhS (Qav q hq' false) (QaA q) k hk (Qes hq')
    (div_pos (by norm_num) hq.1) (Qij hq' k) l _).trans
  rw [←hw]
  apply Qmv hl hm hum off hi hoff hsafe π hπ hπsum s τ hq hθ hmean hv _ ha
  rw [hw]; positivity [hq.1]
end TraceReconstruction
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
theorem QoH {ι:Type*} [Fintype ι]
    (d:ι → Option Bool) (F:ℤ → ℝ) :
    (∑ b:ι → Bool,(∏i,(Qba (d i)).mass (b i)) *
      F (∑i,(bitIndex (b i):ℤ))) =
    ∑k∈Z5 ((∑i,Qat (d i))+1),
      Qah (∑i,Qat (d i)) k * F ((∑i,(QbM (d i):ℤ))+k):=by
  have H:=congrArg (fun p:IntSeries => Finsupp.linearCombination ℝ F p.coeff)
    (QoJ d)
  rw [Qel,Z3] at H
  simp only [Z85,one_mul,
    Z58,Z41,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H
theorem Qlo (n k:ℕ) (hk:k ≤ n) :
    Qah n (n-k) = Qah n k:=by
  simp only [Qah,Nat.choose_symm hk]
theorem QoI {ι:Type*} [Fintype ι]
    (d:ι → Option Bool) (F:ℤ → ℝ) :
    (∑ b:ι → Bool,(∏i,(Qba (d i)).mass (b i)) *
      F (∑i,(bitIndex (b i):ℤ))) =
    ∑k∈Z5 ((∑i,Qat (d i))+1),
      Qah (∑i,Qat (d i)) k *
        F ((∑i,(QbM (d i):ℤ))+(∑i,Qat (d i))-k):=by
  rw [QoH]
  rw [←Finset.sum_range_reflect]
  apply Z2 rfl
  intro k hk
  have hk':k ≤ ∑i,Qat (d i):=by simpa only [Z57,Nat.lt_succ_iff] using hk
  simp only [Nat.add_sub_cancel,Qlo _ _ hk',Z47 hk']
  congr 2
  ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
namespace FiniteLaw
variable {α β:Type*} [Fintype α] [Fintype β]
theorem QgK (P:FiniteLaw α) (f:α → ℝ) (c:ℝ) :
    P.expect (fun a => c*f a) = c*P.expect f:=by
  unfold expect
  simp only [mul_left_comm (P.mass _) c,Z3]
theorem QkM {n:ℕ} (P:Fin n → FiniteLaw α)
    (f:Fin n → α → ℝ) :
    (QaR P).expect (fun x => ∏i,f i (x i)) = ∏i,(P i).expect (f i):=by
  unfold expect QaR
  simp only [←Z30]
  exact (Z43 (fun (i:Fin n) (a:α) => (P i).mass a*f i a)).symm
end FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
namespace FiniteLaw
end FiniteLaw
end TraceReconstruction
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K:Type*} [Fintype K]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K:Type*} [Fintype K]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι κ α:Type*} [Fintype ι] [Fintype κ] [Fintype α]
def Qmf (P:ι → FiniteLaw α):FiniteLaw (ι → α) where
  mass x:=∏i,(P i).mass (x i)
  nonneg x:=Z37 (fun i _ => (P i).nonneg _)
  total:=by
    rw [←Z43]
    simp only [(P _).total,Finset.prod_const_one]
end FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α:Type*} [Fintype α]
theorem Qoa (P Q H:FiniteLaw α) (ω:ℝ) (z:α × α) :
    QbR P Q H ω (none,z)=Qcm H ω z:=by
  simp only [QbR,Z62,Qbr]
  ring
theorem Qod (P Q H:FiniteLaw α) {ω:ℝ} (hω:0≤ω)
    (hP:∀a,ω*H.mass a≤P.mass a) (hQ:∀a,ω*H.mass a≤Q.mass a) (F:ℕ → ℝ) :
    (Qdp P Q H hω hP hQ).expect (fun z => F (Qat z.1))=
      ω^2*F 1+(1-ω^2)*F 0:=by
  let R:=Qdp P Q H hω hP hQ
  have hp:R.expect (fun z => if z.1=none then (1:ℝ) else 0)=ω^2:=by
    simp only [expect,R,Qdp,Z32,Fintype.sum_option]
    simp only [reduceCtorEq,ite_false,mul_zero,Z102,add_zero]
    simpa only [Qoa,Z32,ite_true,mul_one] using Qqy H ω
  have he (z:Option Bool × (α × α)):F (Qat z.1)=
      F 0+(F 1-F 0)*(if z.1=none then 1 else 0):=by
    rcases z with ⟨d,z⟩; cases d <;> simp [Qat]
  simp_rw [he]
  have hadd:R.expect (fun z => F 0+(F 1-F 0)*(if z.1=none then 1 else 0))=
      R.expect (fun _ => F 0)+R.expect (fun z => (F 1-F 0)*(if z.1=none then 1 else 0)):=by
    simp only [expect,mul_add,Z14]
  rw [hadd,Qbi,QgK,hp]
  ring
theorem Qoe (P Q H:FiniteLaw α) {ω t:ℝ} (hω:0≤ω)
    (hP:∀a,ω*H.mass a≤P.mass a) (hQ:∀a,ω*H.mass a≤Q.mass a)
    (hp:ω^2∈Z6 0 1) (ht:|t|≤1) :
    (Qdp P Q H hω hP hQ).expect (fun z =>
      Z1 (t*((Qat z.1:ℕ)-ω^2)))≤Z1 (t^2):=by
  rw [Qod P Q H hω hP hQ (fun k => Z1 (t*((k:ℝ)-ω^2)))]
  have H:=Qgd 1 hp ht
  norm_num [Finset.sum_range_succ,Qaa] at H ⊢
  convert H using 1 ; ring
end FiniteLaw
namespace QaB
variable {Side:Type*} [Fintype Side] {m:ℕ} (M:QaB Side m)
def QbJ (z:Reports Side m):ℕ:=∑i,Qat (z i).1
theorem QlY {ω t:ℝ} (hw:∀i,M.hiddenWeight i=ω)
    (hp:ω^2∈Z6 0 1) (ht:|t|≤1) :
    M.reports.expect (fun z => Z1 (t*((QbJ z:ℕ)-(m:ℝ)*ω^2)))≤
      Z1 ((m:ℝ)*t^2):=by
  have he (z:Reports Side m) :
      Z1 (t*((QbJ z:ℕ)-(m:ℝ)*ω^2))=
        ∏i:Fin m,Z1 (t*((Qat (z i).1:ℕ)-ω^2)):=by
    rw [←Real.exp_sum]
    congr 1
    simp only [mul_sub,Z3,Z39,Z59,Z48,Z26,
      nsmul_eq_mul,QbJ,Nat.cast_sum]
    ring
  simp_rw [he]
  rw [reports,FiniteLaw.QkM _
    (fun (_:Fin m) (z:Option Bool × (Side × Side)) => Z1 (t*((Qat z.1:ℕ)-ω^2))) ]
  calc
    _ ≤ ∏i:Fin m,Z1 (t^2):=by
      apply Z45
      · intro i _
        exact Z11 (fun z _ => mul_nonneg
          ((FiniteLaw.Qdp (M.first i) (M.second i) (M.common i) (M.weight_nonneg i)
            (M.common_first i) (M.common_second i)).nonneg z) (Z49 _))
      · intro i _
        have h:=FiniteLaw.Qoe (M.first i) (M.second i) (M.common i)
          (M.weight_nonneg i) (M.common_first i) (M.common_second i) (by simpa [hw i] using hp) ht
        simpa only [hw i] using h
    _ = _:=by simp only [Z78,Z48,Z26,Z75]
theorem QlZ {ω:ℝ} (hw:∀i,M.hiddenWeight i=ω) (hp:ω^2∈Z6 0 1) :
    M.reports.expect (fun z => if (QbJ z:ℝ)<(m:ℝ)*ω^2/2 then 1 else 0)≤
      Z1 (-(m:ℝ)*ω^4/16):=by
  have ht:0≤ω^2/4:=by positivity
  have ht':|-(ω^2/4)|≤1:=by rw [abs_neg,abs_of_nonneg ht]; linarith [hp.2]
  have H:=QgU Z16 M.reports.mass
    (fun z => -((QbJ z:ℕ)-(m:ℝ)*ω^2)) (fun z _ => M.reports.nonneg z)
    ((m:ℝ)*ω^2/2) (ω^2/4) ht
  have hm:=M.QlY hw hp ht'
  have hsub:M.reports.expect (fun z => if (QbJ z:ℝ)<(m:ℝ)*ω^2/2 then 1 else 0)≤
      ∑z∈Finset.univ.filter (fun z => (m:ℝ)*ω^2/2≤-((QbJ z:ℕ)-(m:ℝ)*ω^2)),M.reports.mass z:=by
    rw [Z27]
    apply Z7
    intro z _
    dsimp only
    by_cases hz:(QbJ z:ℝ)<(m:ℝ)*ω^2/2
    · rw [if_pos hz,if_pos (by linarith:(m:ℝ)*ω^2/2≤-((QbJ z:ℕ)-(m:ℝ)*ω^2)),mul_one]
    · rw [if_neg hz,mul_zero]; split_ifs <;> positivity [M.reports.nonneg z]
  calc
    _ ≤ _:=hsub.trans H
    _ ≤ Z1 (-(ω^2/4)*((m:ℝ)*ω^2/2))*Z1 ((m:ℝ)*(-(ω^2/4))^2):=by
      apply mul_le_mul_of_nonneg_left _ (Z49 _)
      simpa only [FiniteLaw.expect,neg_mul,mul_neg,neg_neg] using hm
    _ = _:=by rw [←Z50]; congr 1; ring
end QaB
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι α:Type*} [Fintype ι] [Fintype α]
end FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι:Type*} [Fintype ι] [DecidableEq ι] {A:ι → Type*} [∀i,Fintype (A i)]
end FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α ι:Type*} [Fintype α] [Fintype ι]
theorem expect_add (P:FiniteLaw α) (f g:α → ℝ) :
    P.expect (fun a => f a+g a)=P.expect f+P.expect g:=by
  simp only [expect,mul_add,Z14]
end FiniteLaw
end TraceReconstruction
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qfm {q:ℝ} (hq:q∈Z6 0 1)
    (x y:List Bool) (M:ℕ) (hx:x.length≤M) (hy:y.length≤M) :
    QcJ q hq x y≤
      (listTraceLaw q hq x M hx).overlap (listTraceLaw q hq y M hy):=by
  let M₀:=max x.length y.length
  have H:=QfR hq
    (listTraceLaw q hq x M₀ (le_max_left _ _))
    (listTraceLaw q hq y M₀ (le_max_right _ _)) Subtype.val x y 0 0 M hx hy
    (Qcv q hq x M₀ _).QbY
    (Qcv q hq y M₀ _).QbY
  simp only [add_zero] at H
  unfold QcJ
  rw [FiniteLaw.QdN,FiniteLaw.QdN]
  linarith
namespace FiniteLaw
variable {α:Type*} [Fintype α]
theorem QkC (P Q:FiniteLaw α) (h:0<P.overlap Q)
    {ω:ℝ} (hω:ω≤P.overlap Q) (a:α) :
    ω*(commonPart P Q h).mass a≤Q.mass a:=by
  change ω*(min (P.mass a) (Q.mass a)/P.overlap Q)≤_
  calc
    _ ≤ P.overlap Q*(min (P.mass a) (Q.mass a)/P.overlap Q) :=
      mul_le_mul_of_nonneg_right hω (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
    _ = min (P.mass a) (Q.mass a):=by field_simp
    _ ≤ _:=min_le_right _ _
end FiniteLaw
def QqH {m:ℕ} {q ω:ℝ} (hq:q∈Z6 0 1) (hω:0<ω)
    (U V:Fin m → List Bool) (M:ℕ) (hU:∀j,(U j).length≤M) (hV:∀j,(V j).length≤M)
    (hov:∀j,ω≤QcJ q hq (U j) (V j)):QaB (BoundedTrace M) m where
  first j:=listTraceLaw q hq (U j) M (hU j)
  second j:=listTraceLaw q hq (V j) M (hV j)
  common j:=FiniteLaw.commonPart _ _ (hω.trans_le ((hov j).trans (Qfm hq _ _ M _ _)))
  hiddenWeight _:=ω
  weight_nonneg _:=hω.le
  common_first j:=FiniteLaw.QkB _ _ _
    ((hov j).trans (Qfm hq _ _ M _ _))
  common_second j:=FiniteLaw.QkC _ _ _
    ((hov j).trans (Qfm hq _ _ M _ _))
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace QaB
variable {Side:Type*} [Fintype Side] {m:ℕ} (M:QaB Side m)
end QaB
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def Qfe (m:ℕ) (ω:ℝ):ℝ:=Z0 (4/((m:ℝ)*ω^2+2))
theorem Qma (m G:ℕ) (ω:ℝ)
    (h:(m:ℝ)*ω^2/2≤G):Qar G≤Qfe m ω:=by
  apply Z24
  apply (div_le_div_iff₀ (by positivity:(0:ℝ)<G+1)
    (by positivity:(0:ℝ)<(m:ℝ)*ω^2+2)).mpr
  nlinarith
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α:Type*} [Fintype α]
theorem QfO (P:FiniteLaw α) (F:α → ℝ) (t:ℕ) :
    |P.expect F|^t ≤ P.expect (fun a => |F a|^t):=by
  have habs:|P.expect F| ≤ P.expect (fun a => |F a|):=by
    calc
      _ ≤ ∑a,|P.mass a*F a|:=Z70 _ _
      _ = _:=by simp only [abs_mul,abs_of_nonneg (P.nonneg _)]; rfl
  apply (pow_le_pow_left₀ (abs_nonneg _) habs t).trans
  simpa only [smul_eq_mul,expect] using (convexOn_pow (𝕜:=ℝ) t).map_sum_le (t:=Z16)
      (w:=P.mass) (p:=fun a => |F a|) (fun a _ => P.nonneg a) P.total (fun a _ => (show |F a| ∈ Set.Ici (0:ℝ) from abs_nonneg (F a)))
theorem QkV (P Q:FiniteLaw α) (Z:α → ℝ)
    (hZ:∀a,Q.mass a=P.mass a*(1+Z a)):P.expect Z=0:=by
  have h:=Q.total
  simp_rw [hZ,mul_add,mul_one,Z14,P.total] at h
  change _+P.expect Z=1 at h
  linarith
theorem Qkm (R:FiniteLaw α) (f g:α → ℝ)
    (hf:∀a,0 ≤ f a) (hg:∀a,0 ≤ g a) (hfm:R.expect f=1) (hgm:R.expect g=1)
    (A:Finset α) (t:ℕ) :
    |(R.Qag f hf hfm).eventMass A-(R.Qag g hg hgm).eventMass A|^t ≤
      R.expect (fun a => |if a∈A then g a-f a else 0|^t):=by
  have he:(R.Qag f hf hfm).eventMass A-(R.Qag g hg hgm).eventMass A=
      -(R.expect (fun a => if a∈A then g a-f a else 0)):=by
    simp only [expect,mul_ite,mul_zero,←Z27,
      Z93,Z94,eventMass,Qag,mul_sub,
      Z39]
    ring
  rw [he,abs_neg]
  exact R.QfO _ t
theorem Qkj (R:FiniteLaw α) (f g:α → ℝ)
    (hf:∀a,0 ≤ f a) (hfm:R.expect f=1)
    (A:Finset α) (hAf:∀a∈A,1/2 ≤ f a)
    (hP:0<(R.Qag f hf hfm).eventMass A) (k:ℕ) :
    (condition (R.Qag f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1)) ≤
      2^k/(R.Qag f hf hfm).eventMass A *
        R.expect (fun a => |if a∈A then g a-f a else 0|^(k+1)):=by
  let g':α → ℝ:=fun a => if a∈A then g a else f a
  have H:=Qki R f g' hf hfm A hAf hP k
  have he:(condition (R.Qag f hf hfm) A hP).expect (fun a => |g a/f a-1|^(k+1))=
      (condition (R.Qag f hf hfm) A hP).expect (fun a => |g' a/f a-1|^(k+1)):=by
    apply Z2 rfl
    intro a _
    by_cases ha:a∈A <;> simp [condition,g',ha]
  rw [he]
  convert H using 1
  congr 2
  funext a
  by_cases ha:a∈A <;> simp [g',ha]
theorem Qkk (R:FiniteLaw α) (f g:α → ℝ)
    (hf:∀a,0 ≤ f a) (hg:∀a,0 ≤ g a) (hfm:R.expect f=1) (hgm:R.expect g=1)
    (A:Finset α) (hAf:∀a∈A,1/2 ≤ f a)
    (hp:1/2 ≤ (R.Qag f hf hfm).eventMass A)
    (hq:1/2 ≤ (R.Qag g hg hgm).eventMass A)
    (k:ℕ) (hk:1 ≤ k) (V:ℝ) (hV:0 ≤ V)
    (hM:R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k) :
    let p:=(R.Qag f hf hfm).eventMass A
    let q:=(R.Qag g hg hgm).eventMass A
    let hP:0 < p:=lt_of_lt_of_le (by norm_num) hp
    (condition (R.Qag f hf hfm) A hP).Qbh (fun a => p/q*(g a/f a)-1) k ≤64*V:=by
  dsimp only
  let p:=(R.Qag f hf hfm).eventMass A
  let q:=(R.Qag g hg hgm).eventMass A
  have hp0:0<p:=lt_of_lt_of_le (by norm_num) hp
  have hq0:0<q:=lt_of_lt_of_le (by norm_num) hq
  have hp1:p ≤ 1:=QgH _ _
  have hratio:p/q ≤ 2:=(div_le_iff₀ hq0).mpr (by linarith)
  have hden:(1:ℝ)/p ≤ 2:=(div_le_iff₀ hp0).mpr (by linarith)
  have ht:2*k-1+1=2*k:=by omega
  have hraw:=Qkj R f g hf hfm A hAf hp0 (2*k-1)
  rw [ht] at hraw
  have hraw':(condition (R.Qag f hf hfm) A hp0).expect (fun a => |g a/f a-1|^(2*k)) ≤
      2^(2*k)*V^k:=by
    apply hraw.trans
    calc
      _ ≤ (2^(2*k-1)/p)*V^k:=mul_le_mul_of_nonneg_left hM (by positivity)
      _ ≤ (2^(2*k-1)*2)*V^k:=by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hV _)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hden (by positivity:0 ≤ (2:ℝ)^(2*k-1))
      _ = _:=by rw [←pow_succ,ht]
  have hnorm:|p/q-1|^(2*k) ≤ 2^(2*k)*V^k:=by
    rw [div_sub_one hq0.ne',abs_div,abs_of_pos hq0,div_pow]
    apply (div_le_iff₀ (pow_pos hq0 _)).mpr
    have hd:=(Qkm R f g hf hg hfm hgm A (2*k)).trans hM
    have hqpow:1 ≤ (2*q)^(2*k):=one_le_pow₀ (by linarith)
    calc
      _ ≤ V^k:=hd
      _ ≤ (2*q)^(2*k)*V^k:=by nlinarith [pow_nonneg hV k]
      _ = _:=by rw [mul_pow]; ring
  have hs:=Qpq (condition (R.Qag f hf hfm) A hp0)
    (fun a => g a/f a) (p/q) (div_nonneg hp0.le hq0.le) (2*k-1)
  rw [ht] at hs
  have hpower:(p/q)^(2*k) ≤ (2:ℝ)^(2*k) :=
    pow_le_pow_left₀ (div_nonneg hp0.le hq0.le) hratio _
  have hs':(condition (R.Qag f hf hfm) A hp0).expect (fun a => |p/q*(g a/f a)-1|^(2*k)) ≤
      (64*V)^k:=by
    apply hs.trans
    calc
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*V^k):=by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (mul_le_mul hpower hraw' (by
          apply Z11; intro a _; positivity [(condition (R.Qag f hf hfm) A hp0).nonneg a]) (by positivity)) hnorm
      _ ≤ 2^(2*k-1)*(2^(2*k)*(2^(2*k)*V^k)+2^(2*k)*(2^(2*k)*V^k)):=by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        have htwo:(1:ℝ) ≤ 2^(2*k):=one_le_pow₀ (by norm_num)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo
          (by positivity:0 ≤ (2:ℝ)^(2*k)*V^k)
      _ = (64*V)^k:=by
        have hm:2^(2*k-1)*2= (2:ℝ)^(2*k):=by rw [←pow_succ,ht]
        calc
          _ = (2^(2*k-1)*2)*(2:ℝ)^(2*k)*(2:ℝ)^(2*k)*V^k:=by ring
          _ = _:=by rw [hm,←pow_add,←pow_add,mul_pow]; congr 1; rw [show 2*k+2*k+2*k=6*k by omega,pow_mul]; norm_num
  unfold Qbh
  calc
    _ ≤ ((64*V)^k)^(1/(k:ℝ)):=Z92
      (by apply Z11; intro a _; positivity [(condition (R.Qag f hf hfm) A hp0).nonneg a]) hs' (by positivity)
    _ = _:=by rw [←Z77,one_div,Real.rpow_rpow_inv (by positivity) (by positivity)]
end TraceReconstruction.FiniteLaw
noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α:Type*} [Fintype α]
theorem QdE (P:FiniteLaw α) (A:Finset α) :
    P.eventMass A=P.expect (fun a => if a∈A then 1 else 0):=by
  simp only [expect,mul_ite,mul_one,mul_zero,←Z27,
    Z93,Z94,eventMass]
theorem Qld (P:FiniteLaw α) (A:Finset α) :
    P.eventMass Aᶜ=1-P.eventMass A:=by
  rw [QdE,QdE]
  have he:P.expect (fun a => (if a∈Aᶜ then (1:ℝ) else 0)+(if a∈A then 1 else 0))=1:=by
    convert P.Qbi 1 using 1
    congr 1; funext a
    by_cases ha:a∈A <;> simp [ha]
  rw [expect_add] at he
  linarith
theorem QkW (R:FiniteLaw α) (f:α → ℝ) (k:ℕ) (hk:1 ≤ k)
    (hM:R.expect (fun a => |f a-1|^(2*k)) ≤ 1) :
    R.expect (fun a => f a^2) ≤ 6:=by
  have h:=R.QgL (fun a => f a-1) (2*k) hM 2 (by omega)
  calc
    _ ≤ R.expect (fun a => 2*(f a-1)^2+2):=R.QaZ (fun a => by nlinarith [sq_nonneg (f a-2)])
    _ = 2*R.expect (fun a => (f a-1)^2)+2:=by rw [expect_add,QgK,Qbi]
    _ ≤ _:=by linarith [le_abs_self (R.expect (fun a => (f a-1)^2))]
theorem QgD (R:FiniteLaw α) (f g:α → ℝ)
    (hg:∀a,0 ≤ g a) (hgm:R.expect g=1) (k:ℕ) (hk:1 ≤ k) (U:ℝ)
    (hU:0 ≤ U) (hU1:U ≤ 1)
    (hfM:R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM:R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    (R.Qag g hg hgm).eventMass (Finset.univ.filter (fun a => f a<1/2)) ≤
      Z0 (6*(4*U)^k):=by
  let A:=Finset.univ.filter (fun a => f a<1/2)
  have hR:R.eventMass A ≤ (4*U)^k:=by
    calc
      _ ≤ 2^(2*k)*R.expect (fun a => |f a-1|^(2*k)) :=
        R.Qnb f (2*k) A (fun a ha => (Finset.mem_filter.mp ha).2)
      _ ≤ 2^(2*k)*U^k:=mul_le_mul_of_nonneg_left hfM (by positivity)
      _ = _:=by rw [pow_mul,mul_pow]; norm_num
  have hsecond:=R.QkW g k hk (hgM.trans (pow_le_one₀ hU hU1))
  have hsq:((R.Qag g hg hgm).eventMass A)^2 ≤ 6*(4*U)^k:=by
    apply (R.QkU g A).trans
    calc
      _ ≤ R.eventMass A*6:=mul_le_mul_of_nonneg_left hsecond (R.QeY A)
      _ ≤ _:=by nlinarith
  exact (Real.le_sqrt ((R.Qag g hg hgm).QeY A) (by positivity)).mpr hsq
def QdA (B:Finset α) (f:α → ℝ):Finset α :=
  B.filter (fun a => 1/2 ≤ f a)
theorem Qgt (P:FiniteLaw α) (B:Finset α) (f:α → ℝ) :
    1-P.eventMass (QdA B f) ≤
      P.eventMass Bᶜ+P.eventMass (Finset.univ.filter (fun a => f a<1/2)):=by
  rw [←Qld,QdE,QdE,QdE,←expect_add]
  apply P.QaZ
  intro a
  simp only [QdA,Finset.mem_compl,Finset.mem_filter,Z21,true_and]
  split_ifs <;> simp_all
theorem Qky (R:FiniteLaw α) (f g:α → ℝ)
    (hf:∀a,0 ≤ f a) (hg:∀a,0 ≤ g a) (hfm:R.expect f=1) (hgm:R.expect g=1)
    (B:Finset α) (e:ℝ) (hfB:(R.Qag f hf hfm).eventMass Bᶜ ≤ e)
    (hgB:(R.Qag g hg hgm).eventMass Bᶜ ≤ e)
    (k:ℕ) (hk:1 ≤ k) (U:ℝ) (hU:0 ≤ U) (hU1:U ≤ 1)
    (hfM:R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM:R.expect (fun a => |g a-1|^(2*k)) ≤ U^k) :
    1-(R.Qag f hf hfm).eventMass (QdA B f) ≤ e+Z0 (6*(4*U)^k) ∧
    1-(R.Qag g hg hgm).eventMass (QdA B f) ≤ e+Z0 (6*(4*U)^k):=by
  constructor
  · exact (Qgt _ B f).trans (add_le_add hfB
      (QgD R f f hf hfm k hk U hU hU1 hfM hfM))
  · exact (Qgt _ B f).trans (add_le_add hgB
      (QgD R f g hg hgm k hk U hU hU1 hfM hgM))
end TraceReconstruction.FiniteLaw
noncomputable section
namespace TraceReconstruction
open scoped Classical
structure Qbd {α:Type*} [Fintype α] (P Q:FiniteLaw α) (k:ℕ) (e V:ℝ) where
  first:FiniteLaw α
  second:FiniteLaw α
  score:α → ℝ
  density:∀a,second.mass a=first.mass a*(1+score a)
  likelihood_nonneg:∀a,0 ≤ 1+score a
  centered:first.expect score=0
  moment:first.Qbh score k ≤ V
  first_tv:first.tv P ≤ e
  second_tv:second.tv Q ≤ e
namespace FiniteLaw
variable {α:Type*} [Fintype α]
theorem Qle (R:FiniteLaw α) (f g:α → ℝ)
    (hf:∀a,0 ≤ f a) (hg:∀a,0 ≤ g a) (hfm:R.expect f=1) (hgm:R.expect g=1)
    (B:Finset α) (e:ℝ) (hfB:(R.Qag f hf hfm).eventMass Bᶜ ≤ e)
    (hgB:(R.Qag g hg hgm).eventMass Bᶜ ≤ e)
    (k:ℕ) (hk:1 ≤ k) (U:ℝ) (hU:0 ≤ U) (hU1:U ≤ 1)
    (hfM:R.expect (fun a => |f a-1|^(2*k)) ≤ U^k)
    (hgM:R.expect (fun a => |g a-1|^(2*k)) ≤ U^k)
    (V:ℝ) (hV:0 ≤ V)
    (hM:R.expect (fun a => |if a∈B then g a-f a else 0|^(2*k)) ≤ V^k)
    (hsmall:e+Z0 (6*(4*U)^k) ≤ 1/2) :
    Nonempty (Qbd (R.Qag f hf hfm) (R.Qag g hg hgm)
      k (e+Z0 (6*(4*U)^k)) (64*V)):=by
  let A:=QdA B f
  let P:=R.Qag f hf hfm
  let Q:=R.Qag g hg hgm
  have hA (a:α) (ha:a∈A):1/2 ≤ f a:=(Finset.mem_filter.mp ha).2
  have hloss:=Qky R f g hf hg hfm hgm B e hfB hgB k hk U hU hU1 hfM hgM
  have hp:1/2 ≤ P.eventMass A:=by linarith [hloss.1]
  have hq:1/2 ≤ Q.eventMass A:=by linarith [hloss.2]
  have hp0:0<P.eventMass A:=lt_of_lt_of_le (by norm_num) hp
  have hq0:0<Q.eventMass A:=lt_of_lt_of_le (by norm_num) hq
  let Z:α → ℝ:=fun a => P.eventMass A/Q.eventMass A*(g a/f a)-1
  have hden (a:α):(Q.condition A hq0).mass a=(P.condition A hp0).mass a*(1+Z a):=by
    dsimp only [Z]
    rw [show 1+(P.eventMass A/Q.eventMass A*(g a/f a)-1)=P.eventMass A/Q.eventMass A*(g a/f a) by ring]
    exact QkH R f g hf hg hfm hgm A
      (fun a ha => lt_of_lt_of_le (by norm_num) (hA a ha)) hp0 hq0 a
  have hAM:R.expect (fun a => |if a∈A then g a-f a else 0|^(2*k)) ≤ V^k:=by
    apply le_trans (R.QaZ _) hM
    intro a
    by_cases ha:a∈A
    · have hb:=(Finset.mem_filter.mp ha).1
      simp only [if_pos ha,if_pos hb,le_refl]
    · rw [if_neg ha]
      simp only [abs_zero,zero_pow (by omega:2*k≠0)]
      exact pow_nonneg (abs_nonneg _) _
  exact ⟨{
    first:=P.condition A hp0
    second:=Q.condition A hq0
    score:=Z
    density:=hden
    likelihood_nonneg:=fun a => by
      dsimp only [Z]
      have hh:=mul_nonneg (div_nonneg hp0.le hq0.le) (div_nonneg (hg a) (hf a))
      linarith
    centered:=QkV _ _ Z hden
    moment:=Qkk R f g hf hg hfm hgm A hA hp hq k hk V hV hAM
    first_tv:=by rw [tv_symm,QiY]; exact hloss.1
    second_tv:=by rw [tv_symm,QiY]; exact hloss.2
  }⟩
end FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
local instance (priority:=10000) {α β:Type*}:DecidableEq (α × β):=Classical.decEq _
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace Qbd
variable {α β:Type*} [Fintype α] [Fintype β]
    {P Q:FiniteLaw α} {k:ℕ} {e V:ℝ}
end Qbd
theorem Qbk.of_tv {α:Type*} [Fintype α]
    {q E e:ℝ} {P Q:FiniteLaw α} {f:α → List Bool} {w:List Bool}
    (hP:Qbk q P f w E) (htv:Q.tv P ≤ e) :
    Qbk q Q f w (e+E):=by
  intro F hF
  exact (abs_sub_le (Q.expect (fun a => F (f a))) (P.expect (fun a => F (f a)))
    (Qay q w F)).trans (add_le_add
      ((FiniteLaw.QfP Q P _ (fun a => hF _)).trans htv) (hP F hF))
structure QbN (q:ℝ) (x y:List Bool) (k:ℕ) (E V:ℝ) where
  Outcome:Type
  finiteOutcome:Fintype Outcome
  first:@FiniteLaw Outcome finiteOutcome
  second:@FiniteLaw Outcome finiteOutcome
  decode:Outcome → List Bool
  first_simulation:@Qbk Outcome finiteOutcome q first decode x E
  second_simulation:@Qbk Outcome finiteOutcome q second decode y E
  score:Outcome → ℝ
  density:∀a,second.mass a=first.mass a*(1+score a)
  likelihood_nonneg:∀a,0≤1+score a
  centered:first.expect score=0
  moment:@FiniteLaw.Qbh Outcome finiteOutcome first score k ≤ V
end TraceReconstruction
noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α:Type*} [Fintype α]
theorem Qei (P:FiniteLaw α) (F:α → ℝ) (hF:∀a,0≤F a):0≤P.expect F :=
  Z11 (fun a _ => mul_nonneg (P.nonneg a) (hF a))
theorem Qlb (P:FiniteLaw α) (F:α → ℝ) (k:ℕ) :
    0≤P.Qbh F k:=Real.rpow_nonneg (P.Qei _ (fun _ => by positivity)) _
theorem Qlc (P:FiniteLaw α) (F:α → ℝ) (k:ℕ) (hk:1≤k) :
    (P.Qbh F k)^k=P.expect (fun a => |F a|^(2*k)):=by
  unfold Qbh
  rw [one_div,Real.rpow_inv_natCast_pow (P.Qei _ (fun _ => by positivity)) (by omega)]
theorem QeZ (P:FiniteLaw α) (F:α → ℝ) (k:ℕ) (hk:1≤k)
    {V:ℝ} (h:P.Qbh F k≤V) :
    P.expect (fun a => |F a|^(2*k))≤V^k:=by
  rw [←P.Qlc F k hk]
  exact pow_le_pow_left₀ (P.Qlb F k) h k
theorem Qpr (P:FiniteLaw α) (F:α → ℝ) (k:ℕ) (hk:1≤k) :
    P.expect (fun a => F a^2)≤P.Qbh F k:=by
  have hn:0≤P.expect (fun a => F a^2):=P.Qei _ (fun _ => sq_nonneg _)
  have hj:=P.QfO (fun a => F a^2) k
  simp only [abs_of_nonneg hn,abs_pow,←pow_mul] at hj
  have hr:=Z92 (pow_nonneg hn k) hj (by positivity:0≤(k:ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hn (by omega)] at hr
  simpa only [Qbh,one_div] using hr
end TraceReconstruction.FiniteLaw
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
def Qao (u m:ℕ) (q w:ℝ):ℝ :=
  w^2*(3*Qau/q)*Z0 ((u:ℝ)/m)
def Qcu (u m l R s:ℕ) (π:IntSeries) (θ q w:ℝ):ℝ :=
  (∑r∈Z5 R,w^(2*r)*Qcx u m r s π θ l)+
    4*(Qao u m q w)^R/(1-Qao u m q w)
theorem Qmr (u m l R s:ℕ) (π:IntSeries) (θ q w:ℝ)
    (hq:0 ≤ q) (ha:Qao u m q w < 1) :
    0 ≤ Qcu u m l R s π θ q w:=by
  apply add_nonneg
  · exact Z11 (fun r _ => mul_nonneg (by rw [pow_mul]; positivity)
      (QfG _ _ _ _ _ _ _))
  · apply div_nonneg _ (sub_nonneg.mpr ha.le)
    exact mul_nonneg (by norm_num) (pow_nonneg (by unfold Qao; positivity [Qcd]) _)
theorem QmP {u m l R:ℕ} (hu:0 < u) (hm:128 ≤ m)
    (hum:u ≤ m) (hR:0 < R) (hl:l ≤ u*m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s k:ℕ) (hcentral:QbI u s π) (hk:1 ≤ k)
    {q θ w:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM:((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw:w=((6*(2*k:ℕ):ℝ)*(2/q))) (ha:Qao u m q w < 1) :
    ((Qav q ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ false).product l).Qbh
      (fun x => QbD hl off hsafe π s 1 q x-QbD hl off hsafe π s (-1) q x) k  ≤ 
        Qcu u m l R s π θ q w:=by
  have hq':q∈Z4 0 1:=⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  have he:(fun x => QbD hl off hsafe π s 1 q x-QbD hl off hsafe π s (-1) q x)=
      Qaj (fun σ => QaD hl off hsafe π s 1 σ-QaD hl off hsafe π s (-1) σ)
        (QaA q):=by funext x; exact (QhT _ _ _ _).symm
  rw [he]
  apply (QhS (Qav q hq' false) (QaA q) k hk
    (Qes hq') (div_pos (by norm_num) hq.1) (Qij hq' k) l _).trans
  rw [←hw]
  exact QpU hu hm hum hR hl off hi hoff hsafe π hπ hπsum s hcentral hq hθ hmean hv hM
    (by rw [hw]; positivity [hq.1]) ha
theorem Qmy {u m l R:ℕ} (hu:0 < u) (hm:128 ≤ m)
    (hum:u ≤ m) (hR:0 < R) (hl:l ≤ u*m) (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m) (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X) (hπsum:∑X∈π.coeff.support,π.coeff X=1)
    (s k:ℕ) (hcentral:QbI u s π) (hk:1 ≤ k)
    {q θ w:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1 ≤ ((u*m:ℕ):ℝ)*θ*(1-θ))
    (hM:((2*(2^s):ℕ):ℝ) < (u:ℝ)/(3*(R+1:ℝ)))
    (hw:w=((6*(2*k:ℕ):ℝ)*(2/q))) (hscale:Qao u m q w ≤ 1/2)
    (hclip:Z0 (6*(4*(Qao u m q w/(1-Qao u m q w)))^k) ≤ 1/2) :
    Nonempty (Qbd
      (Qca hl off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ π hπ hπsum s (-1))
      (Qca hl off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ π hπ hπsum s 1) k
      (Z0 (6*(4*(Qao u m q w/(1-Qao u m q w)))^k))
      (64*Qcu u m l R s π θ q w)):=by
  have hq':q∈Z4 0 1:=⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩
  let A:=(Qav q hq' false).product l
  let f:=QbD hl off hsafe π s (-1) q
  let g:=QbD hl off hsafe π s 1 q
  let U:=Qao u m q w/(1-Qao u m q w)
  have ha:Qao u m q w < 1:=by linarith
  have hz:0 ≤ Qao u m q w:=by unfold Qao; positivity [Qcd,hq.1]
  have hU:0 ≤ U:=div_nonneg hz (sub_nonneg.mpr ha.le)
  have hU1:U ≤ 1:=(div_le_iff₀ (sub_pos.mpr ha)).mpr (by linarith)
  have hmom (τ:ℝ):A.expect (fun x => |QbD hl off hsafe π s τ q x-1|^(2*k)) ≤ U^k :=
    A.QeZ _ k hk (Qmw hl (by omega) hum off hi hoff hsafe π hπ hπsum s k hk τ hq hθ hmean hv hw ha)
  have hV:=Qmr u m l R s π θ q w hq.1.le ha
  have hsig:=A.QeZ _ k hk
    (QmP hu hm hum hR hl off hi hoff hsafe π hπ hπsum s k hcentral hk hq hθ hmean hv hM hw ha)
  rw [Qhi hl off hsafe π hπ hπsum s (-1) hq',
    Qhi hl off hsafe π hπ hπsum s 1 hq']
  have H:=A.Qle f g
    (Qfh hl off hsafe π hπ hπsum s (-1) hq')
    (Qfh hl off hsafe π hπ hπsum s 1 hq')
    (Qfg hl off hsafe π hπ hπsum s (-1) hq')
    (Qfg hl off hsafe π hπ hπsum s 1 hq')
    Z16 0 (by simp [eventMass]) (by simp [eventMass]) k hk U hU hU1 (hmom (-1)) (hmom 1)
    (Qcu u m l R s π θ q w) hV (by simpa only [Z21,ite_true] using hsig)
    (by simpa only [zero_add] using hclip)
  simpa only [zero_add] using H
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α:Type*} [Fintype α]
theorem QgG (P:FiniteLaw α) (F:α → ℝ) (k:ℕ) (hk:1≤k)
    {V:ℝ} (hV:0≤V) (h:P.expect (fun a => |F a|^(2*k))≤V^k) :
    P.Qbh F k≤V:=by
  have H:=Z92 (P.Qei _ (fun _ => by positivity)) h (by positivity:0≤(k:ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hV (by omega)] at H
  simpa only [FiniteLaw.Qbh,one_div] using H
theorem Qjb {ι:Type*} [Fintype ι] {β:ι → Type*} [∀i,Fintype (β i)]
    (M:FiniteLaw ι) (P Q:∀i,FiniteLaw (β i)) :
    (M.sigma P).tv (M.sigma Q)=M.expect (fun i => (P i).tv (Q i)):=by
  simp only [tv,sigma,expect,Z83,←mul_sub,abs_mul,abs_of_nonneg (M.nonneg _)]
  rw [Z3]
  apply Z2 rfl
  intro i _
  rw [←Z3]
  ring
end FiniteLaw
namespace Qbd
variable {α:Type*} [Fintype α] {P Q:FiniteLaw α} {k:ℕ} {e V E W:ℝ}
def weaken (C:Qbd P Q k e V) (he:e≤E) (hV:V≤W):Qbd P Q k E W where
  first:=C.first
  second:=C.second
  score:=C.score
  density:=C.density
  likelihood_nonneg:=C.likelihood_nonneg
  centered:=C.centered
  moment:=C.moment.trans hV
  first_tv:=C.first_tv.trans he
  second_tv:=C.second_tv.trans he
def trivial (P Q:FiniteLaw α) (k:ℕ) (hk:1≤k):Qbd P Q k 1 0 where
  first:=P
  second:=P
  score:=fun _ => 0
  density:=fun _ => by ring
  likelihood_nonneg:=fun _ => by norm_num
  centered:=by simp [FiniteLaw.expect]
  moment:=by
    apply P.QgG _ k hk (by norm_num)
    simp [FiniteLaw.expect,zero_pow (by omega:2*k≠0)]
  first_tv:=by simp [FiniteLaw.tv]
  second_tv:=FiniteLaw.tv_le_one _ _
def sigma {ι:Type*} [Fintype ι] {β:ι → Type*} [∀i,Fintype (β i)]
    (M:FiniteLaw ι) (P Q:∀i,FiniteLaw (β i)) (e:ι → ℝ)
    (k:ℕ) (hk:1≤k) (V:ℝ) (hV:0≤V)
    (C:∀i,Qbd (P i) (Q i) k (e i) V) :
    Qbd (M.sigma P) (M.sigma Q) k (M.expect e) V where
  first:=M.sigma (fun i => (C i).first)
  second:=M.sigma (fun i => (C i).second)
  score:=fun a => (C a.1).score a.2
  density:=fun a => by dsimp only [FiniteLaw.sigma]; rw [(C a.1).density]; ring
  likelihood_nonneg:=fun a => (C a.1).likelihood_nonneg a.2
  centered:=by
    rw [FiniteLaw.Qej]
    simp_rw [(C _).centered]
    simp [FiniteLaw.expect]
  moment:=by
    apply FiniteLaw.QgG _ _ k hk hV
    rw [FiniteLaw.Qej]
    calc
      _ ≤ M.expect (fun _ => V^k):=M.QaZ (fun i =>
        (C i).first.QeZ _ k hk (C i).moment)
      _ = _:=M.Qbi _
  first_tv:=by
    rw [FiniteLaw.Qjb]
    exact M.QaZ (fun i => (C i).first_tv)
  second_tv:=by
    rw [FiniteLaw.Qjb]
    exact M.QaZ (fun i => (C i).second_tv)
theorem Qjm {ι:Type*} [Fintype ι] {β:ι → Type*} [∀i,Fintype (β i)]
    (M:FiniteLaw ι) (P Q:∀i,FiniteLaw (β i)) (Good:ι → Prop)
    (k:ℕ) (hk:1≤k) (e V:ℝ) (he:0≤e) (hV:0≤V)
    (C:∀i,Good i → Nonempty (Qbd (P i) (Q i) k e V)) :
    Nonempty (Qbd (M.sigma P) (M.sigma Q) k
      (e+M.expect (fun i => if Good i then 0 else 1)) V):=by
  let err:=fun i => if Good i then e else 1
  have hi (i):Nonempty (Qbd (P i) (Q i) k (err i) V):=by
    by_cases h:Good i
    · simpa only [err,if_pos h] using C i h
    · exact ⟨(trivial (P i) (Q i) k hk).weaken (by simp [err,h]) hV⟩
  let D:=sigma M P Q err k hk V hV (fun i => Classical.choice (hi i))
  refine ⟨D.weaken ?_ le_rfl⟩
  calc
    M.expect err ≤ M.expect (fun i => e+(if Good i then 0 else 1)):=M.QaZ (fun i => by
      dsimp only [err]; split_ifs <;> linarith)
    _ = _:=by rw [M.expect_add,M.Qbi]
end Qbd
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
theorem QqL (g:ℕ) (c:ℤ) (F:ℤ → ℝ) :
    (∑X∈(Qby c (fairSeries g)).coeff.support,
      (Qby c (fairSeries g)).coeff X*F X)=
    ∑k∈Z5 (g+1),Qah g k*F (c+k):=by
  have H:=congrArg (fun p:IntSeries => Finsupp.linearCombination ℝ F p.coeff)
    (congrArg (Qby c) (Qel g))
  simp only [Qby,Z3,Z85,one_mul,
    Z58,Z41,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H
def QaP {ι:Type*} [Fintype ι] (c:ℤ) (d:ι → Option Bool):IntSeries :=
  Qby (c-(∑i,(QbM (d i):ℤ))-(∑i,Qat (d i)))
    (fairSeries (∑i,Qat (d i)))
theorem Qie {ι:Type*} [Fintype ι]
    (c:ℤ) (d:ι → Option Bool) (F:ℤ → ℝ) :
    (∑b:ι → Bool,(∏i,(Qba (d i)).mass (b i))*
      F (c-∑i,(bitIndex (b i):ℤ)))=
    ∑X∈(QaP c d).coeff.support,(QaP c d).coeff X*F X:=by
  rw [QoI d (fun z => F (c-z)),QaP,QqL]
  apply Z2 rfl
  intro k _
  congr 2
  ring
theorem QdP {ι:Type*} [Fintype ι]
    (c:ℤ) (d:ι → Option Bool) (X:ℤ):0 ≤ (QaP c d).coeff X :=
  QqI _ _ _
theorem QdQ {ι:Type*} [Fintype ι]
    (c:ℤ) (d:ι → Option Bool) :
    ∑X∈(QaP c d).coeff.support,(QaP c d).coeff X=1:=by
  have H:=Qie c d (fun _ => 1)
  simp only [mul_one] at H
  rw [←H]
  exact (FiniteLaw.Qmf (fun i => Qba (d i))).total
theorem QoE {ι:Type*} [Fintype ι]
    (c:ℤ) (d:ι → Option Bool) (X:ℤ) (hX:X∈(QaP c d).coeff.support) :
    c-Z10 ι ≤ X ∧ X ≤ c:=by
  have H:=QqK (∑i,Qat (d i))
    (c-(∑i,(QbM (d i):ℤ))-(∑i,Qat (d i))) X
    (Finsupp.mem_support_iff.mp hX)
  have hz:0 ≤ ∑i,(QbM (d i):ℤ):=Z11 (fun _ _ => by positivity)
  have hh:(∑i,(QbM (d i):ℤ))+(∑i,Qat (d i)) ≤ Z10 ι:=by
    rw [Nat.cast_sum,←Z14]
    calc
      _ ≤ ∑_i:ι,(1:ℤ):=Z7 (fun i _ => by
        cases h:d i with
        | none => simp [QbM,Qat]
        | some b => cases b <;> simp [QbM,Qat])
      _ = _:=by simp
  omega
theorem QoC {ι:Type*} [Fintype ι]
    (u s:ℕ) (c:ℤ) (d:ι → Option Bool)
    (hleft:(u:ℝ)/3 ≤ 2*((c:ℝ)-Z10 ι)+1)
    (hright:(u:ℝ)/3 ≤ 2*u-(2*((c:ℝ)+(2:ℝ)^s)+1)) :
    QbI u s (QaP c d):=by
  intro X hX
  have H:=QoE c d X hX
  have H₁:(c:ℝ)-Z10 ι ≤ X:=by exact_mod_cast H.1
  have H₂:(X:ℝ) ≤ c:=by exact_mod_cast H.2
  constructor <;> linarith
namespace QaB
variable {Side α:Type*} [Fintype Side] [Fintype α] {J:ℕ}
def Qef (M:QaB Side J) (K:(Fin J → Bool) → FiniteLaw α) :
    FiniteLaw (Reports Side J × α) :=
  M.reports.joint (fun z => (QhV z).mixture K)
theorem QkZ (M:QaB Side J) (K:(Fin J → Bool) → FiniteLaw α) :
    (Qlt J).mixture (fun b => (M.Qds b).prod (K b))=M.Qef K:=by
  apply FiniteLaw.ext
  funext zx
  rcases zx with ⟨z,x⟩
  change (∑b,(∏i:Fin J,(1/2:ℝ))*
    ((∏i,FiniteLaw.Qbr (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (b i) (z i))*(K b).mass x))=
    (∏i,FiniteLaw.QbR (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (z i))*(∑b,(∏i,(Qba (z i).1).mass (b i))*(K b).mass x)
  rw [Z3]
  apply Z2 rfl
  intro b _
  rw [←mul_assoc,←Z30,FiniteLaw.QnY,mul_assoc]
end QaB
theorem QkF {u m l J:ℕ} (hl:l ≤ u*m) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (c:ℤ) (d:Fin J → Option Bool) (s:ℕ) (τ:ℝ) :
    (FiniteLaw.QaR (fun i => Qba (d i))).mixture
      (fun b => Qbg hl q hq
        (QaC (QaN off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
    Qca hl off hsafe hq (QaP c d)
      (QdP c d) (QdQ c d) s τ:=by
  apply FiniteLaw.ext
  funext x
  change (∑b:Fin J → Bool,(∏i:Fin J,(Qba (d i)).mass (b i))*
    (Qbg hl q hq (QaC (QaN off hsafe s
      (c-∑i,(bitIndex (b i):ℤ)) τ))).mass x)=_
  classical
  have H:=Qie c d (fun X =>
    (Qbg hl q hq (QaC (QaN off hsafe s X τ))).mass x)
  calc
    _ = ∑X∈(QaP c d).coeff.support,
        (QaP c d).coeff X*
          (Qbg hl q hq (QaC (QaN off hsafe s X τ))).mass x:=by
      convert H using 1
      congr 1
      ext b
      simp
    _ = _:=(Finset.sum_coe_sort _ _).symm
def QeV {u m:ℕ} (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (π:IntSeries) (hπ:∀X,0 ≤ π.coeff X)
    (hπsum:∑X∈π.coeff.support,π.coeff X=1) (s:ℕ) (τ:ℝ) :
    FiniteLaw (Qeb (u*m)) :=
  (Qcs (le_refl (u*m)) (1-Qaq q) (Qdq hq)).sigma
    (fun l => Qca (by omega) off hsafe hq π hπ hπsum s τ)
theorem QkO {u m J:ℕ} (off:Fin m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (c:ℤ) (d:Fin J → Option Bool) (s:ℕ) (τ:ℝ) :
    (FiniteLaw.QaR (fun i => Qba (d i))).mixture
      (fun b => Qcb (le_refl (u*m)) hq
        (QaC (QaN off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
    QeV off hsafe hq (QaP c d)
      (QdP c d) (QdQ c d) s τ:=by
  apply FiniteLaw.ext
  funext x
  rcases x with ⟨l,x⟩
  have hl:l.val ≤ u*m:=by omega
  have H:=congrArg (fun P:FiniteLaw (Fin l.val → Qai) => P.mass x)
    (QkF hl off hsafe hq c d s τ)
  change (∑b,_ * ((Qcs _ _ _).mass l *
    (QbZ hq _ l).mass x))=_
  simp only [QbZ,dif_pos hl]
  change _ = (Qcs _ _ _).mass l * _
  rw [←H]
  simp only [FiniteLaw.mixture,Z3]
  apply Z2 rfl
  intro b _
  ring
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def Qcj {m:ℕ} (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (s:ℕ) (X:ℤ) (τ:ℝ) (j:ℤ):Fin m :=
  ⟨off.val+(motifShift (QaT s (j-X)) ((Qak s).coeff (j-X)) τ).val-1,by
    have H:=(motifShift (QaT s (j-X)) ((Qak s).coeff (j-X)) τ).isLt
    omega⟩
theorem QpM {u m:ℕ} (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (s:ℕ) (X:ℤ) (τ:ℝ) :
    QaN off hsafe s X τ =
      periodSlot (fun j => Qcj off hi s X τ j.val):=by
  funext j
  apply Z34
  simp only [QaN,shiftedTag,periodSlot,Qcj]
  omega
def Qbp {m:ℕ} (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (u s:ℕ) (X:ℤ) (τ:ℝ):List Bool :=
  Qbn m u (fun j => Qcj off hi s X τ j.val)
theorem QpV {u m:ℕ} (off:Fin m)
    (hi:1 ≤ off.val ∧ off.val+1 < m)
    (hsafe:Qae (periodSlot (u:=u) (fun _ => off)))
    (s:ℕ) (X:ℤ) (τ:ℝ) :
    (((Z20 (QaC (QaN off hsafe s X τ))).map QbG).flatten)=
    Qbp off hi u s X τ:=by
  rw [QpM off hi,Qid]
  rfl
theorem QhK {m:ℕ} (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (s:ℕ) (X:ℤ) (τ:ℝ) (j:ℤ) (hj:j<X ∨ X+(2^s:ℕ) ≤ j) :
    Qcj off hi s X τ j=off:=by
  apply Z34
  have h:¬(0 ≤ j-X ∧ j-X<(2^s:ℕ)):=by omega
  simp only [Qcj,QaT,if_neg h,motifShift,ite_true]
  norm_num
theorem Qnj {m:ℕ} (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (s:ℕ) (X t:ℤ) (τ:ℝ) (j:ℤ) :
    Qcj off hi s X τ (t+j)=Qcj off hi s (X-t) τ j:=by
  have h:t+j-X=j-(X-t):=by ring
  simp only [Qcj,h]
theorem Qom {m:ℕ} (n k z:ℕ) (off:Fin (n+k+z) → Fin m) :
    Qbn m (n+k+z) off =
      Qbn m n (fun i => off ⟨i.val,by omega⟩) ++
      Qbn m k (fun i => off ⟨n+i.val,by omega⟩) ++
      Qbn m z (fun i => off ⟨n+k+i.val,by omega⟩):=by
  simp only [Qbn,List.ofFn_add,List.flatten_append]
  rfl
theorem Qno {m:ℕ} (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (t K z s:ℕ) (a:ℤ) (τ:ℝ) (hleft:(t:ℤ) ≤ a) (hright:a+(2^s:ℕ) ≤ t+K) :
    Qbp off hi (t+K+z) s a τ =
      Qal (Qam m off.val) t ++ Qbp off hi K s (a-t) τ ++
      Qal (Qam m off.val) z:=by
  unfold Qbp
  rw [Qom]
  congr 2
  · rw [←Qfv off]
    congr 1
    funext i
    exact QhK off hi s a τ i.val (Or.inl (by have H:=i.isLt; omega))
  · congr 1
    funext i
    rw [Z23,Qnj]
  · rw [←Qfv off]
    congr 1
    funext i
    exact QhK off hi s a τ (t+K+i.val) (Or.inr (by
      have H:(0:ℤ) ≤ i.val:=by positivity
      omega))
theorem Qnm {m:ℕ} (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (u s:ℕ) (X:ℤ) (τ:ℝ) :
    (Qbp off hi u s X τ).length=u*(2*m-1):=Qol _ _ _
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β:Type*} [Fintype α] [Fintype β]
theorem QkL {n:ℕ} (P:Fin n → FiniteLaw α)
    (Q:Fin n → FiniteLaw β) (F:(Fin n → α×β) → ℝ) :
    (QaR (fun i => (P i).prod (Q i))).expect F=
      (QaR P).expect (fun a =>
        (QaR Q).expect (fun b => F (fun i => (a i,b i)))):=by
  induction n with
  | zero =>
    have H (a:Fin 0 → α×β):a = fun i => Fin.elim0 i:=by funext i; exact Fin.elim0 i
    have hF:F=fun _ => F (fun i => Fin.elim0 i):=by
      funext a
      exact congrArg F (H a)
    rw [hF]
    simp only [Qbi]
  | succ n ih =>
    rw [Qeh,QbB,Qeh]
    congr 1
    funext a
    simp_rw [ih,Qeh Q]
    rw [QgJ]
    congr 1
    funext x
    congr 1
    funext b
    congr 1
    funext y
    congr 1
    funext i
    refine Z38 ?_ (fun j => ?_) i <;> simp
end FiniteLaw
def QdC {Side α:Type*} {J:ℕ}
    (side:Side → List Bool) (central:α → List Bool) (z:Reports Side J × α):List Bool :=
  QaS (fun i => side (z.1 i).2.1) ++ central z.2 ++
    QaS (fun i => side (z.1 i).2.2)
namespace QaB
variable {Side α:Type*} [Fintype Side] [Fintype α] {J:ℕ}
theorem Qpn (M:QaB Side J) (b:Fin J → Bool)
    {q:ℝ} (side:Side → List Bool) (central:α → List Bool) (K:FiniteLaw α)
    (U V:Fin J → List Bool) (w:List Bool)
    (hfirst:∀i,QaE q (M.first i) side (U i))
    (hsecond:∀i,QaE q (M.second i) side (V i))
    (hK:QaE q K central w) :
    QaE q ((M.Qds b).prod K) (QdC side central)
      (QaS (fun i => if b i then V i else U i) ++ w ++
        QaS (fun i => if b i then U i else V i)):=by
  let P:Fin J → FiniteLaw Side:=fun i => if b i then M.second i else M.first i
  let Q:Fin J → FiniteLaw Side:=fun i => if b i then M.first i else M.second i
  have HP:∀i,QaE q (P i) side (if b i then V i else U i):=by
    intro i
    dsimp [P]
    cases h:b i
    · exact hfirst i
    · exact hsecond i
  have HQ:∀i,QaE q (Q i) side (if b i then U i else V i):=by
    intro i
    dsimp [Q]
    cases h:b i
    · exact hsecond i
    · exact hfirst i
  have H:=((Qgx P side _ HP).append hK).append
    (Qgx Q side _ HQ)
  intro F
  rw [←H F,FiniteLaw.QbB,FiniteLaw.QbB]
  change (M.Qds b).expect (fun z => K.expect (fun x =>
    F (QaS (fun i => side (z i).2.1) ++ central x ++
      QaS (fun i => side (z i).2.2))))=_
  have hf:=congrArg (fun L:FiniteLaw (Fin J → Side×Side) => L.expect (fun z =>
    K.expect (fun x => F (QaS (fun i => side (z i).1) ++ central x ++
      QaS (fun i => side (z i).2))))) (M.Qpm b)
  rw [FiniteLaw.expect_map] at hf
  simp only [Function.comp_def] at hf
  rw [hf]
  have he:(fun i => FiniteLaw.Qcl (M.first i) (M.second i) (b i))=
      fun i => (P i).prod (Q i):=by
    funext i
    cases h:b i <;> simp [FiniteLaw.Qcl,P,Q,h]
  rw [he,FiniteLaw.QkL]
  simp only [FiniteLaw.QbB]
  congr 1
  funext a
  rw [FiniteLaw.QgJ]
end QaB
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QcF {J:ℕ} (k:ℕ) (b:Fin J → Bool):ℕ :=
  ∑ i:Fin J,(k+bitIndex (b i))
def Qfj {J:ℕ} (k:ℕ) (b:Fin J → Bool):ℕ :=
  ∑ i:Fin J,(k+(1-bitIndex (b i)))
theorem Qho {J:ℕ} (k:ℕ) (b:Fin J → Bool) :
    QcF k b=J*k+∑i,bitIndex (b i):=by
  simp [QcF,Z14]
theorem Qmk {J:ℕ} (k:ℕ) (b:Fin J → Bool) :
    QcF k b+Qfj k b=J*(2*k+1):=by
  unfold QcF Qfj
  rw [←Z14]
  have H (i:Fin J):(k+bitIndex (b i))+(k+(1-bitIndex (b i)))=2*k+1:=by
    cases h:b i <;> simp [bitIndex] <;> omega
  simp only [H,Z59,Z48,Z26,nsmul_eq_mul,Nat.cast_id]
theorem Qmm {J:ℕ} (k:ℕ) (b:Fin J → Bool) :
    J*k ≤ QcF k b ∧ QcF k b ≤ J*k+J:=by
  rw [Qho]
  have H:(∑i,bitIndex (b i)) ≤ J:=by
    calc
      _ ≤ ∑_i:Fin J,1:=Z7 (fun i _ => by cases b i <;> simp [bitIndex])
      _ = _:=by simp
  omega
theorem QmE {Side:Type*} [Fintype Side] {J K m:ℕ}
    (M:QaB Side J) (k s:ℕ) (a:ℤ) (τ:ℝ)
    (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (hsafe:Qae (periodSlot (u:=K) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (side:Side → List Bool)
    (hfirst:∀i,QaE q (M.first i) side (Qal (Qam m off.val) k))
    (hsecond:∀i,QaE q (M.second i) side (Qal (Qam m off.val) (k+1)))
    (ha:(J*k+J:ℕ) ≤ a) (ha':a+(2^s:ℕ) ≤ (J*k+K:ℕ)) :
    QaE q
      (M.Qef (fun b => Qcb (le_refl (K*m)) hq
        (QaC (QaN off hsafe s
          (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ))))
      (QdC side Qdb)
      (Qbp off hi (J*(2*k+1)+K) s a τ):=by
  rw [←M.QkZ]
  intro F
  rw [FiniteLaw.Qll]
  have H (b:Fin J → Bool) :
      ((M.Qds b).prod (Qcb (le_refl (K*m)) hq
        (QaC (QaN off hsafe s
          (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ)))).expect
        (fun z => F (QdC side Qdb z))=
      Qay q (Qbp off hi (J*(2*k+1)+K) s a τ) F:=by
    let t:=QcF k b
    let z:=Qfj k b
    have ht:=Qmm k b
    have htot:t+K+z=J*(2*k+1)+K:=by
      have H:=Qmk k b
      dsimp [t,z]
      omega
    have hanchor:a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)=a-t:=by
      dsimp [t]
      rw [Qho]
      push_cast
      ring
    have hleft:(t:ℤ) ≤ a:=by
      have H:(t:ℤ) ≤ (J*k+J:ℕ):=by exact_mod_cast ht.2
      omega
    have hright:a+(2^s:ℕ) ≤ (t:ℤ)+K:=by
      have H:((J*k:ℕ):ℤ) ≤ t:=by exact_mod_cast ht.1
      simp only [Z23] at ha'
      omega
    have hp:QaS (fun i => if b i then
        Qal (Qam m off.val) (k+1) else Qal (Qam m off.val) k)=
        Qal (Qam m off.val) t:=by
      have h (i:Fin J):(if b i then Qal (Qam m off.val) (k+1) else
          Qal (Qam m off.val) k)=Qal (Qam m off.val) (k+bitIndex (b i)):=by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact Qgy _ _
    have hz:QaS (fun i => if b i then
        Qal (Qam m off.val) k else Qal (Qam m off.val) (k+1))=
        Qal (Qam m off.val) z:=by
      have h (i:Fin J):(if b i then Qal (Qam m off.val) k else
          Qal (Qam m off.val) (k+1))=Qal (Qam m off.val) (k+(1-bitIndex (b i))):=by
        cases b i <;> simp [bitIndex]
      simp_rw [h]
      exact Qgy _ _
    have hc:=QeW (le_refl (K*m)) hq
      (QaC (QaN off hsafe s (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ))
    rw [QpV off hi] at hc
    have hs:=M.Qpn b side Qdb _
      (fun _ => Qal (Qam m off.val) k)
      (fun _ => Qal (Qam m off.val) (k+1)) _ hfirst hsecond hc
    have hword:QaS (fun i => if b i then
        Qal (Qam m off.val) (k+1) else Qal (Qam m off.val) k) ++
        Qbp off hi K s (a-(J*k:ℕ)-∑i,(bitIndex (b i):ℤ)) τ ++
        QaS (fun i => if b i then Qal (Qam m off.val) k else
          Qal (Qam m off.val) (k+1))=
        Qbp off hi (J*(2*k+1)+K) s a τ:=by
      rw [hp,hz,hanchor,←Qno off hi t K z s a τ hleft hright,htot]
    rw [hword] at hs
    exact hs F
  simp only [H,FiniteLaw.Qbi]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
abbrev QcS (Side:Type*) (J N:ℕ):=Reports Side J × Fin (N+1)
abbrev QfN (Side:Type*) (J N:ℕ) :=
  Σz:QcS Side J N,Fin z.2.val → Qai
def Qdk {Side:Type*} [Fintype Side] {J:ℕ}
    (M:QaB Side J) (N:ℕ) {q:ℝ} (hq:q∈Z4 0 1) :
    FiniteLaw (QcS Side J N) :=
  M.reports.prod (Qcs (le_refl N) (1-Qaq q) (Qdq hq))
def Qhh {Side:Type*} [Fintype Side] {J K m:ℕ}
    (off:Fin m) (hsafe:Qae (periodSlot (u:=K) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (c:ℤ) (s:ℕ) (τ:ℝ)
    (z:QcS Side J (K*m)):FiniteLaw (Fin z.2.val → Qai) :=
  Qca (by have H:=z.2.isLt; omega) off hsafe hq
    (QaP c (fun i => (z.1 i).1))
    (QdP c _) (QdQ c _) s τ
def QdK {Side:Type*} [Fintype Side] {J K m:ℕ}
    (M:QaB Side J) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=K) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (c:ℤ) (s:ℕ) (τ:ℝ) :
    FiniteLaw (QfN Side J (K*m)) :=
  (Qdk M (K*m) hq).sigma (Qhh off hsafe hq c s τ)
def QeX {Side:Type*} {J N:ℕ} (side:Side → List Bool)
    (z:QfN Side J N):List Bool :=
  QdC side Qdb (z.1.1,⟨z.1.2,z.2⟩)
theorem Qmq {Side:Type*} [Fintype Side] {J K m:ℕ}
    (M:QaB Side J) (off:Fin m)
    (hsafe:Qae (periodSlot (u:=K) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (c:ℤ) (s:ℕ) (τ:ℝ)
    (F:Reports Side J × Qeb (K*m) → ℝ) :
    (QdK M off hsafe hq c s τ).expect (fun z => F (z.1.1,⟨z.1.2,z.2⟩))=
    (M.Qef (fun b => Qcb (le_refl (K*m)) hq
      (QaC (QaN off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))).expect F:=by
  unfold QaB.Qef
  rw [FiniteLaw.Qlk]
  have H (z:Reports Side J):(QaB.QhV z).mixture
      (fun b => Qcb (le_refl (K*m)) hq
        (QaC (QaN off hsafe s (c-∑i,(bitIndex (b i):ℤ)) τ)))=
      QeV off hsafe hq (QaP c (fun i => (z i).1))
        (QdP c _) (QdQ c _) s τ :=
    QkO off hsafe hq c (fun i => (z i).1) s τ
  simp_rw [H]
  simp only [QdK,Qdk,FiniteLaw.Qej,FiniteLaw.QbB,
    QeV,Qhh]
theorem QmL {Side:Type*} [Fintype Side] {J K m:ℕ}
    (M:QaB Side J) (k s:ℕ) (a:ℤ) (τ:ℝ)
    (off:Fin m) (hi:1  ≤  off.val ∧ off.val+1  <  m)
    (hsafe:Qae (periodSlot (u:=K) (fun _ => off)))
    {q:ℝ} (hq:q∈Z4 0 1) (side:Side → List Bool)
    (hfirst:∀i,QaE q (M.first i) side (Qal (Qam m off.val) k))
    (hsecond:∀i,QaE q (M.second i) side (Qal (Qam m off.val) (k+1)))
    (ha:(J*k+J:ℕ)  ≤  a) (ha':a+(2^s:ℕ)  ≤  (J*k+K:ℕ)) :
    QaE q (QdK M off hsafe hq (a-(J*k:ℕ)) s τ)
      (QeX side) (Qbp off hi (J*(2*k+1)+K) s a τ):=by
  intro F
  unfold QeX
  rw [Qmq M off hsafe hq (a-(J*k:ℕ)) s τ (fun z => F (QdC side Qdb z))]
  exact QmE M k s a τ off hi hsafe hq side hfirst hsecond ha ha' F
def Qdg (N:ℕ) (q:ℝ) (l:Fin (N+1)):Prop :=
  (l.val:ℝ)/(N:ℝ)∈Z6 (1-q^2) (1-q^2/4) ∧
    1  ≤  (N:ℝ)*((l.val:ℝ)/(N:ℝ))*(1-(l.val:ℝ)/(N:ℝ))
def Qdj {Side:Type*} {J N:ℕ} (q ω:ℝ)
    (z:QcS Side J N):Prop :=
  Qdg N q z.2 ∧ (J:ℝ)*ω^2/2  ≤  ∑i,(Qat (z.1 i).1:ℝ)
theorem QmK {Side:Type*} [Fintype Side] {J K m R:ℕ}
    (M:QaB Side J) (hK:0 < K) (hm:128 ≤ m) (hKm:K ≤ m)
    (hR:0 < R) (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=K) (fun _ => off)))
    (c:ℤ) (s k:ℕ) (hk:1 ≤ k)
    (hleft:(K:ℝ)/3 ≤ 2*((c:ℝ)-J)+1)
    (hright:(K:ℝ)/3 ≤ 2*K-(2*((c:ℝ)+(2:ℝ)^s)+1))
    {q ω w V:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hM:((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw:w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale:Qao K m q w ≤ 1/2)
    (hclip:Z0 (6*(4*(Qao K m q w/(1-Qao K m q w)))^k) ≤ 1/2)
    (hV:0 ≤ V)
    (hbudget:∀z:QcS Side J (K*m),Qdj q ω z →
      64*Qcu K m z.2.val R s (QaP c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V) :
    Nonempty (Qbd
      (QdK M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s (-1))
      (QdK M off hsafe ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩ c s 1) k
      (Z0 (6*(4*(Qao K m q w/(1-Qao K m q w)))^k)+
        (Qdk M (K*m) ⟨hq.1,lt_of_le_of_lt hq.2 (by norm_num)⟩).expect
          (fun z => if Qdj q ω z then 0 else 1)) V):=by
  apply Qbd.Qjm _ _ _ (Qdj q ω) k hk _ V (Z36 _) hV
  intro z hz
  have hmean:((K*m:ℕ):ℝ)*((z.2.val:ℝ)/(K*m:ℕ))=z.2.val:=by
    exact mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega:K≠0) (by omega:m≠0)))
  have H:=Qmy hK hm hKm hR (by have H:=z.2.isLt; omega) off hi hoff hsafe
    (QaP c (fun i => (z.1 i).1)) (QdP c _)
    (QdQ c _) s k
    (QoC K s c _ (by simpa using hleft) hright) hk hq hz.1.1 hmean hz.1.2 hM hw hscale hclip
  exact ⟨(Classical.choice H).weaken le_rfl (hbudget z hz)⟩
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qbd.tracePair {α:Type} [Fintype α] {P Q:FiniteLaw α}
    {q e V:ℝ} {x y:List Bool} {k:ℕ} (f:α → List Bool)
    (C:Qbd P Q k e V) (hP:QaE q P f x)
    (hQ:QaE q Q f y):Nonempty (QbN q x y k e V):=by
  refine ⟨{
    Outcome:=α
    finiteOutcome:=inferInstance
    first:=C.first
    second:=C.second
    decode:=f
    score:=C.score
    density:=C.density
    likelihood_nonneg:=C.likelihood_nonneg
    centered:=C.centered
    moment:=C.moment
    first_simulation:=?_
    second_simulation:=?_
  }⟩
  · simpa using hP.QbY.of_tv C.first_tv
  · simpa using hQ.QbY.of_tv C.second_tv
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QdH (J s:ℕ) (ω:ℝ):ℝ :=
  ((2:ℝ)^(s*s))^2*((2*Z0 (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2)))^s)^2*
    Z0 (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2))
def Qeo (J s:ℕ) (ω:ℝ):ℝ :=
  ((2:ℝ)^s)^2*Qfe J ω
theorem Qmb (J G s:ℕ) (ω:ℝ) (h:(J:ℝ)*ω^2/2≤G) :
    Qar (G/(s+1))≤Z0 (4*((s:ℝ)+1)/((J:ℝ)*ω^2+2)):=by
  apply (QjD G s).trans
  apply Z24
  apply (div_le_div_iff₀ (by positivity:(0:ℝ)<(G:ℝ)+1)
    (by positivity:(0:ℝ)<(J:ℝ)*ω^2+2)).mpr
  have hh:=mul_le_mul_of_nonneg_left h (by positivity:(0:ℝ)≤4*((s:ℝ)+1))
  nlinarith
theorem QoD {J:ℕ} (d:Fin J→Option Bool) (c:ℤ) (s:ℕ) (ω:ℝ)
    (h:(J:ℝ)*ω^2/2≤∑i,(Qat (d i):ℝ)) :
    seriesL2Sq (Qak s*QaP c d)≤QdH J s ω:=by
  have hn:(J:ℝ)*ω^2/2≤((∑i,Qat (d i):ℕ):ℝ):=by simpa only [Nat.cast_sum] using h
  have hb:=Qmb J (∑i,Qat (d i)) s ω hn
  apply (QqJ (∑i,Qat (d i)) s _).trans
  unfold QdH
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul
  · apply pow_le_pow_left₀ (by unfold Qar; positivity)
    exact pow_le_pow_left₀ (by unfold Qar; positivity) (mul_le_mul_of_nonneg_left hb (by norm_num)) _
  · exact hb
  · exact Z36 _
  · positivity
theorem QoF {J:ℕ} (d:Fin J→Option Bool) (c:ℤ) (s:ℕ) (ω:ℝ)
    (h:(J:ℝ)*ω^2/2≤∑i,(Qat (d i):ℝ)) :
    seriesL2Sq (geomSeries (2^s)*QaP c d)≤Qeo J s ω:=by
  have hn:(J:ℝ)*ω^2/2≤((∑i,Qat (d i):ℕ):ℝ):=by simpa only [Nat.cast_sum] using h
  calc
    _ ≤ seriesL1 (geomSeries (2^s))^2*seriesL2Sq (QaP c d):=Qdu _ _
    _ ≤ ((2:ℝ)^s)^2*Qfe J ω:=by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (QbT _) (by exact_mod_cast Qhd (2^s)) _
      · rw [QaP,QiV]
        exact (QgP _).trans (Qma J _ ω hn)
      · exact Qcn _
      · positivity
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def Qdh (d:ℕ) (q:ℝ):ℝ :=
  2*Z0 (8*((d:ℝ)+1)/q^2)
theorem Qht {q θ:ℝ} (hq:q∈Z12 0 (1/2:ℝ))
    (hθ:θ∈Z6 (1-q^2) (1-q^2/4)) :
    θ∈Z4 0 1 ∧ 1/2≤θ ∧ q^2/8≤θ*(1-θ):=by
  have hq2:q^2≤1/4:=by nlinarith [hq.1,hq.2]
  have hs:0<q^2:=sq_pos_of_pos hq.1
  have hh:1/2≤θ:=by linarith [hθ.1]
  refine ⟨⟨by linarith,by linarith [hθ.2]⟩,hh,?_⟩
  have H:=mul_le_mul hh (show q^2/4≤1-θ by linarith [hθ.2])
    (by positivity:(0:ℝ)≤q^2/4) (by linarith:0≤θ)
  nlinarith
theorem Qmi (d:ℕ) {q θ:ℝ}
    (hq:q∈Z12 0 (1/2:ℝ)) (hθ:θ∈Z6 (1-q^2) (1-q^2/4)) :
    QaJ d θ≤ Qdh d q:=by
  have ht:=Qht hq hθ
  unfold QaJ Qdh
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Z24
  apply (div_le_div_iff₀ (mul_pos ht.1.1 (sub_pos.mpr ht.1.2)) (sq_pos_of_pos hq.1)).mpr
  have H:=mul_le_mul_of_nonneg_left ht.2.2 (by positivity:(0:ℝ)≤8*((d:ℝ)+1))
  nlinarith
def QbK (u m r d:ℕ) (q:ℝ):ℝ :=
  144*((u*m:ℕ):ℝ)*(2:ℝ)^(2*r)*(Qdh d q)^(2*d+r+2) /
    (((m:ℝ)/4)^d*Z0 ((u:ℝ)*m/(2*(r+1:ℝ)))*
      (Z0 ((m:ℝ)/4))^(r+1))
theorem Qhm (u m r d:ℕ) (q:ℝ):0≤ QbK u m r d q:=by
  unfold QbK Qdh
  positivity
theorem Qhs (u m r d:ℕ) {q θ:ℝ}
    (hq:q∈Z12 0 (1/2:ℝ)) (hθ:θ∈Z6 (1-q^2) (1-q^2/4)) :
    QaW u m r d θ≤ QbK u m r d q:=by
  unfold QaW QbK
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by unfold QaJ; positivity) (Qmi d hq hθ) _
theorem QjW {n l:ℕ} {θ:ℝ}
    (hθ:θ∈Z4 0 1) (hl:l≤n) (hmean:(n:ℝ)*θ=l)
    (hv:1≤(n:ℝ)*θ*(1-θ)) :
    (Qaa n θ l)⁻¹≤12*Z0 (n:ℝ):=by
  have h0:0≤(Qaa n θ l)⁻¹:=inv_nonneg.mpr (QaF n l ⟨hθ.1.le,hθ.2.le⟩)
  have hi:=QeP n l hθ hl hmean hv
  have hv':(n:ℝ)*θ*(1-θ)≤n:=by
    have h:=mul_le_mul_of_nonneg_left (show θ*(1-θ)≤1 by nlinarith [sq_nonneg θ]) (Z19 (α:=ℝ) n)
    nlinarith
  have hs:=Z13 (Z19 (α:=ℝ) n)
  nlinarith [Z36 (n:ℝ)]
def Qdl (u m r:ℕ):ℝ :=
  2*((Z10 (Qab u r):ℝ)*
    (48*((r+1:ℕ):ℝ)*Z0 (u*m:ℕ)*Z1 (-(m:ℝ)/(1024*u))))^2
theorem QmI {u m l:ℕ} (r:ℕ) {θ:ℝ}
    (hθ:θ∈Z4 0 1) (hl:l≤u*m) (hmean:((u*m:ℕ):ℝ)*θ=l)
    (hv:1≤((u*m:ℕ):ℝ)*θ*(1-θ)) :
    2*((Z10 (Qab u r):ℝ)*
      (2*(((r+1:ℕ):ℝ)*θ^r/Qaa (u*m) θ l*(2*Z1 (-(m:ℝ)/(1024*u))))))^2 ≤
    Qdl u m r:=by
  have hp:θ^r≤1:=pow_le_one₀ hθ.1.le hθ.2.le
  have hi:=QjW hθ hl hmean hv
  have hn:0≤(Qaa (u*m) θ l)⁻¹:=inv_nonneg.mpr (QaF _ _ ⟨hθ.1.le,hθ.2.le⟩)
  unfold Qdl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hb:=QaF (u*m) l ⟨hθ.1.le,hθ.2.le⟩
  apply pow_le_pow_left₀ (by
    exact mul_nonneg (Z19 _) (mul_nonneg (by norm_num)
      (mul_nonneg (div_nonneg (mul_nonneg (Z19 _) (pow_nonneg hθ.1.le _)) hb)
        (by positivity))))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have H:=mul_le_mul hp hi hn (by norm_num:(0:ℝ)≤1)
  have HH:=mul_le_mul_of_nonneg_left H (by positivity:(0:ℝ)≤4*((r+1:ℕ):ℝ)*Z1 (-(m:ℝ)/(1024*u)))
  simp only [div_eq_mul_inv,one_mul] at *
  nlinarith only [HH]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
theorem Qmh {N:ℕ} {q:ℝ}
    (hq:q∈Z12 0 (1/2:ℝ)) (hscale:8≤(N:ℝ)*q^2) (l:Fin (N+1))
    (hnear:|(l.val:ℝ)-(N:ℝ)*(1-q^2/2)|<(N:ℝ)*q^2/4) :
    Qdg N q l:=by
  have hN:(0:ℝ)<N:=by
    have h0:(0:ℝ)≤N:=Z19 N
    by_contra H
    have hn:(N:ℝ)=0:=le_antisymm (le_of_not_gt H) h0
    rw [hn,zero_mul] at hscale
    norm_num at hscale
  have hq2:q^2≤1/4:=by nlinarith [hq.1,hq.2]
  let θ:ℝ:=(l.val:ℝ)/(N:ℝ)
  have he:(N:ℝ)*θ=l.val:=mul_div_cancel₀ _ hN.ne'
  have hθ:θ∈Z6 (1-q^2) (1-q^2/4):=by
    have hn:=abs_lt.mp hnear
    constructor
    · apply le_of_lt
      apply (mul_lt_mul_iff_right₀ hN).mp
      nlinarith [sq_nonneg q]
    · apply le_of_lt
      apply (mul_lt_mul_iff_right₀ hN).mp
      nlinarith
  have hhalf:3/4≤θ:=by linarith [hθ.1]
  have hlow:q^2/4≤1-θ:=by linarith [hθ.2]
  have hp:=mul_le_mul ((mul_le_mul_iff_right₀ hN).mpr hhalf) hlow
    (by positivity:(0:ℝ)≤q^2/4) (mul_nonneg hN.le (by linarith:0≤θ))
  refine ⟨hθ,?_⟩
  change 1≤(N:ℝ)*θ*(1-θ)
  nlinarith
theorem Qmz {N:ℕ} {q:ℝ}
    (hq:q∈Z12 0 (1/2:ℝ)) (hscale:8≤(N:ℝ)*q^2) :
    (Qcs (le_refl N) (1-Qaq q)
      (Qdq ⟨hq.1,by linarith [hq.2]⟩)).expect
      (fun l => if Qdg N q l then 0 else 1) ≤
    2*Z1 (-(N:ℝ)*q^4/64):=by
  let p:=1-Qaq q
  have hp:p∈Z6 0 1:=Qdq ⟨hq.1,by linarith [hq.2]⟩
  have ht:q^2/8∈Z6 (0:ℝ) 1:=⟨by positivity,by nlinarith [hq.1,hq.2]⟩
  have H:=Qgb N (a:=(N:ℝ)*q^2/4) hp ht
  have he:-(q^2/8)*((N:ℝ)*q^2/4)+(N:ℝ)*(q^2/8)^2= -(N:ℝ)*q^4/64:=by ring
  rw [he] at H
  apply le_trans _ H
  rw [Z27,←Z76]
  apply Z7
  intro l _
  change Qaa N p l.val*(if Qdg N q l then 0 else 1)≤_
  have hn:=QaF N l.val hp
  by_cases hl:Qdg N q l
  · rw [if_pos hl,mul_zero]
    split_ifs <;> positivity
  · rw [if_neg hl,mul_one,if_pos]
    exact le_of_not_gt (fun h => hl (Qmh hq hscale l (by simpa [p,Qaq] using h)))
theorem QmC {Side:Type*} [Fintype Side] {J N:ℕ}
    (M:QaB Side J) {q ω:ℝ}
    (hq:q∈Z12 0 (1/2:ℝ)) (hscale:8≤(N:ℝ)*q^2)
    (hw:∀i,M.hiddenWeight i=ω) (hp:ω^2∈Z6 0 1) :
    (Qdk M N ⟨hq.1,by linarith [hq.2]⟩).expect
      (fun z => if Qdj q ω z then 0 else 1) ≤
    2*Z1 (-(N:ℝ)*q^4/64)+Z1 (-(J:ℝ)*ω^4/16):=by
  calc
    _ ≤ (Qdk M N ⟨hq.1,by linarith [hq.2]⟩).expect
        (fun z => (if Qdg N q z.2 then 0 else 1)+
          (if (QaB.QbJ z.1:ℝ)<(J:ℝ)*ω^2/2 then 1 else 0)):=by
      apply FiniteLaw.QaZ
      intro z
      have he:(QaB.QbJ z.1:ℝ)=∑i,(Qat (z.1 i).1:ℝ):=by
        simp only [QaB.QbJ,Nat.cast_sum]
      unfold Qdj
      rw [←he]
      split_ifs <;> simp_all
    _ ≤ _:=by
      simp only [FiniteLaw.expect_add,Qdk,FiniteLaw.QbB]
      apply add_le_add
      · exact (M.reports.QaZ (fun _ => Qmz hq hscale)).trans (by rw [FiniteLaw.Qbi])
      · convert M.QlZ hw hp using 1
        all_goals try rfl
        apply congrArg M.reports.expect
        funext a
        split_ifs <;> simp_all [FiniteLaw.Qbi]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QcH (J u m r s:ℕ) (q ω:ℝ) (k:Fin r → Qac):ℝ :=
  if ∃a,k=QaM a then
    QbK u m r 1 q*Qbs u r*QdH J s ω
  else QbK u m r (∑h,(k h).order) q*
    QbE u r (2*(2^s))*Qeo J s ω
def QdJ (J u m r s:ℕ) (q ω:ℝ) (k:Fin r → Qac):ℝ :=
  if ∃a,k=QaM a then
    QbK u m r 1 q*Qbs u r*QdH J s ω
  else QbK u m r (∑h,(k h).order) q*
    Qbs u r*Qeo J s ω
theorem QmQ {J:ℕ} (d:Fin J → Option Bool) (c:ℤ)
    (u m r s:ℕ) (k:Fin r → Qac) {q θ ω:ℝ}
    (hq:q∈Z12 0 (1/2:ℝ)) (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hh:(J:ℝ)*ω^2/2≤∑i,(Qat (d i):ℝ)) :
    Qcy u m r s (QaP c d) θ k ≤
      QcH J u m r s q ω k:=by
  unfold Qcy QcH
  split_ifs
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (Qhs u m r 1 hq hθ)
        (by unfold Qbs; positivity)
    · exact QoD d c s ω hh
    · exact Qcn _
    · exact mul_nonneg (Qhm _ _ _ _ _) (by unfold Qbs; positivity)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (Qhs u m r _ hq hθ)
        (by unfold QbE; positivity)
    · exact QoF d c s ω hh
    · exact Qcn _
    · exact mul_nonneg (Qhm _ _ _ _ _) (by unfold QbE; positivity)
def QcG (J u m r s:ℕ) (q ω:ℝ):ℝ :=
  if r=0 then 0 else
    8*(Z10 (Fin r → Qac):ℝ)*
      (∑k:Fin r → Qac,if Odd (Qax k) then
        QcH J u m r s q ω k else 0)+Qdl u m r
def QdI (J u m r s:ℕ) (q ω:ℝ):ℝ :=
  if r=0 then 0 else
    2*(Z10 (Fin r → Qac):ℝ)*
      (∑k:Fin r → Qac,if k=QcR r then 0 else
        QdJ J u m r s q ω k)+Qdl u m r
theorem QmN {J u m l:ℕ} (d:Fin J → Option Bool) (c:ℤ) (r s:ℕ)
    {q θ ω:ℝ} (hq:q∈Z12 0 (1/2:ℝ)) (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hl:l≤u*m) (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh:(J:ℝ)*ω^2/2≤∑i,(Qat (d i):ℝ)) :
    Qcx u m r s (QaP c d) θ l ≤
      QcG J u m r s q ω:=by
  unfold Qcx QcG
  split_ifs
  · exact le_rfl
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Z7
      intro k _
      split_ifs
      · exact QmQ d c u m r s k hq hθ hh
      · exact le_rfl
    · exact QmI r (Qht hq hθ).1 hl hmean hv
def Qdm (J u m R s:ℕ) (q ω w:ℝ):ℝ :=
  (∑r∈Z5 R,w^(2*r)*QcG J u m r s q ω)+
    4*(Qao u m q w)^R/(1-Qao u m q w)
def Qfi (J u m R s:ℕ) (q ω w:ℝ):ℝ :=
  (∑r∈Z5 R,w^(2*r)*QdI J u m r s q ω)+
    4*(Qao u m q w)^R/(1-Qao u m q w)
theorem QmM {J u m l:ℕ} (d:Fin J → Option Bool) (c:ℤ) (R s:ℕ)
    {q θ ω w:ℝ} (hq:q∈Z12 0 (1/2:ℝ)) (hθ:θ∈Z6 (1-q^2) (1-q^2/4))
    (hl:l≤u*m) (hmean:((u*m:ℕ):ℝ)*θ=l) (hv:1≤((u*m:ℕ):ℝ)*θ*(1-θ))
    (hh:(J:ℝ)*ω^2/2≤∑i,(Qat (d i):ℝ)) :
    Qcu u m l R s (QaP c d) θ q w ≤
      Qdm J u m R s q ω w:=by
  unfold Qcu Qdm
  apply add_le_add _ le_rfl
  apply Z7
  intro r _
  exact mul_le_mul_of_nonneg_left (QmN d c r s hq hθ hl hmean hv hh)
    (by rw [pow_mul]; positivity)
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QbN.weaken {q E V E' V':ℝ} {x y:List Bool} {k:ℕ}
    (C:QbN q x y k E V) (hE:E ≤ E') (hV:V ≤ V') :
    QbN q x y k E' V' :=
  { C with
    first_simulation:=fun F hF => (C.first_simulation F hF).trans hE
    second_simulation:=fun F hF => (C.second_simulation F hF).trans hE
    moment:=C.moment.trans hV }
def Qdi (J K m k:ℕ) (q ω w:ℝ):ℝ :=
  Z0 (6*(4*(Qao K m q w/(1-Qao K m q w)))^k)+
    (2*Z1 (-((K*m:ℕ):ℝ)*q^4/64)+Z1 (-(J:ℝ)*ω^4/16))
theorem Qjh {J K m R:ℕ}
    (hK:0 < K) (hm:128 ≤ m) (hKm:K ≤ m) (hR:0 < R)
    (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (hoff:|(off.val:ℝ)-(m:ℝ)/2| ≤ 2)
    (hsafe:Qae (periodSlot (u:=K) (fun _ => off)))
    (a:ℤ) (s k:ℕ) (hk:1 ≤ k) {q w V:ℝ}
    (hq:q∈Z12 0 (1/2:ℝ))
    (hseed:16 ≤ q^3*(m:ℝ)) (hcount:8 ≤ ((K*m:ℕ):ℝ)*q^2)
    (ha:(J*QaI q m+J:ℕ) ≤ a)
    (ha':a+(2^s:ℕ) ≤ (J*QaI q m+K:ℕ))
    (hleft:(K:ℝ)/3 ≤ 2*((a-(J*QaI q m:ℕ):ℤ)-J)+1)
    (hright:(K:ℝ)/3 ≤ 2*K-(2*((a-(J*QaI q m:ℕ):ℤ)+(2:ℝ)^s)+1))
    (hM:((2*(2^s):ℕ):ℝ) < (K:ℝ)/(3*(R+1:ℝ)))
    (hw:w=((6*(2*k:ℕ):ℝ)*(2/q)))
    (hscale:Qao K m q w ≤ 1/2)
    (hclip:Z0 (6*(4*(Qao K m q w/(1-Qao K m q w)))^k) ≤ 1/2)
    (hV:0 ≤ V)
    (hSV:64*Qdm J K m R s q (QaV q) w ≤ V)
    :
    Nonempty (QbN q
      (Qbp off hi (J*(2*QaI q m+1)+K) s a (-1))
      (Qbp off hi (J*(2*QaI q m+1)+K) s a 1) k
      (Qdi J K m k q (QaV q) w) V):=by
  let t:=QaI q m
  let ω:=QaV q
  let c:ℤ:=a-(J*t:ℕ)
  have hω:0 < ω:=Qhj q
  have hω1:ω < 1/8:=Qmj hq.1
  have hqi:q∈Z4 0 1:=⟨hq.1,by linarith [hq.2]⟩
  have hqc:q∈Z6 0 1:=⟨hq.1.le,hqi.2.le⟩
  let u:=Qal (Qam m off.val) t
  let v:=Qal (Qam m off.val) (t+1)
  let N:=max u.length v.length
  have hu:u.length ≤ N:=le_max_left _ _
  have hv:v.length ≤ N:=le_max_right _ _
  have hov:ω ≤ QcJ q hqc u v:=QmH hq (by omega)
    hseed off (by linarith)
  let M:QaB (BoundedTrace N) J:=QqH hqc hω
    (fun _ => u) (fun _ => v) N (fun _ => hu) (fun _ => hv) (fun _ => hov)
  have hfirst (i:Fin J):QaE q (M.first i) Subtype.val u :=
    Qcv q hqc u N hu
  have hsecond (i:Fin J):QaE q (M.second i) Subtype.val v :=
    Qcv q hqc v N hv
  have htail:=QmC M hq hcount (fun _ => rfl)
    (show ω^2∈Z6 (0:ℝ) 1 from ⟨sq_nonneg _,by nlinarith⟩)
  have hsigned (z:QcS (BoundedTrace N) J (K*m))
      (hz:Qdj q ω z) :
      64*Qcu K m z.2.val R s (QaP c (fun i => (z.1 i).1))
        ((z.2.val:ℝ)/(K*m:ℕ)) q w ≤ V:=by
    apply le_trans _ hSV
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact QmM _ c R s hq hz.1.1 (by have H:=z.2.isLt; omega)
      (mul_div_cancel₀ _ (by exact_mod_cast (Nat.mul_ne_zero (by omega:K≠0) (by omega:m≠0))))
      hz.1.2 hz.2
  have hsim (τ:ℝ):=QmL M t s a τ off hi hsafe hqi
    Subtype.val hfirst hsecond ha ha'
  obtain ⟨S⟩:=QmK M hK hm hKm hR off hi hoff hsafe c s k hk
    hleft hright hq hM hw hscale hclip hV hsigned
  obtain ⟨O⟩:=S.tracePair (QeX Subtype.val) (hsim (-1)) (hsim 1)
  exact ⟨O.weaken (add_le_add le_rfl htail) le_rfl⟩
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α:Type*} [Fintype α]
end FiniteLaw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def QbN.pad {q E V:ℝ} {x y:List Bool} {k:ℕ}
    (C:QbN q x y k E V) (hq:q∈Z6 0 1) (u v:List Bool) :
    QbN q (u++x++v) (u++y++v) k E V:=by
  let:=C.finiteOutcome
  let P:=listTraceLaw q hq u u.length le_rfl
  let Q:=listTraceLaw q hq v v.length le_rfl
  refine {
    Outcome:=(BoundedTrace u.length × C.Outcome) × BoundedTrace v.length
    finiteOutcome:=inferInstance
    first:=(P.prod C.first).prod Q
    second:=(P.prod C.second).prod Q
    decode:=fun z => z.1.1.val++C.decode z.1.2++z.2.val
    score:=fun z => C.score z.1.2
    density:=by
      intro z
      change (P.mass z.1.1*C.second.mass z.1.2)*Q.mass z.2=_
      rw [C.density]
      change _=(P.mass z.1.1*C.first.mass z.1.2)*Q.mass z.2*(1+C.score z.1.2)
      ring
    likelihood_nonneg:=fun z => C.likelihood_nonneg z.1.2
    centered:=by
      simp only [FiniteLaw.QbB,FiniteLaw.Qbi,C.centered]
    moment:=by
      simpa only [FiniteLaw.Qbh,FiniteLaw.QbB,FiniteLaw.Qbi] using C.moment
    first_simulation:=by
      have H:=((Qcv q hq u u.length le_rfl).QbY.append hq
        C.first_simulation).append hq (Qcv q hq v v.length le_rfl).QbY
      simpa only [zero_add,add_zero] using H
    second_simulation:=by
      have H:=((Qcv q hq u u.length le_rfl).QbY.append hq
        C.second_simulation).append hq (Qcv q hq v v.length le_rfl).QbY
      simpa only [zero_add,add_zero] using H }
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
structure QeG (q:ℝ) (x y:List Bool) (E V:ℝ) where
  Outcome:Type
  finiteOutcome:Fintype Outcome
  first:@FiniteLaw Outcome finiteOutcome
  second:@FiniteLaw Outcome finiteOutcome
  decode:Outcome → List Bool
  first_simulation:@Qbk Outcome finiteOutcome q first decode x E
  second_simulation:@Qbk Outcome finiteOutcome q second decode y E
  bound:@FiniteLaw.Qbw Outcome finiteOutcome first second ≤ V
def QbN.hellinger {q E V:ℝ} {x y:List Bool} {k:ℕ}
    (C:QbN q x y k E V) (hk:1 ≤ k):QeG q x y E V:=by
  let:=C.finiteOutcome
  exact {
    Outcome:=C.Outcome
    finiteOutcome:=C.finiteOutcome
    first:=C.first
    second:=C.second
    decode:=C.decode
    first_simulation:=C.first_simulation
    second_simulation:=C.second_simulation
    bound:=(C.first.QlW C.second C.score C.density).trans
      ((C.first.Qpr C.score k hk).trans C.moment) }
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
variable {N q ω w:ℕ → ℝ} {J u m:ℕ → ℕ}
theorem Qhn (hN:Tendsto N atTop atTop)
    {α β:ℝ} (hu:PowerRate N (fun t=>(u t:ℝ)) α)
    (hm:PowerRate N (fun t=>(m t:ℝ)) β) (hq:PowerRate N q 0) (r d:ℕ) :
    PowerRate N (fun t=>QbK (u t) (m t) r d (q t))
      (α/2-β*((d:ℝ)+(r:ℝ)/2)):=by
  have hd:PowerRate N (fun t=>Qdh d (q t)) 0:=by
    have H:=((PowerRate.const hN (by positivity:(0:ℝ)<8*((d:ℝ)+1))).div (hq.pow 2)).sqrt.const_mul hN (by norm_num:(0:ℝ)<2)
    simpa only [Qdh,zero_mul,zero_sub,neg_zero,zero_div] using H
  have hnum:=(((hu.mul hm).const_mul hN (by norm_num:(0:ℝ)<144)).mul_const hN
    (by positivity:(0:ℝ)<(2:ℝ)^(2*r))).mul (hd.pow (2*d+r+2))
  have hden:=((hm.div_const hN (by norm_num:(0:ℝ)<4)).pow d).mul
    (((hu.mul hm).div_const hN (by positivity:(0:ℝ)<2*(r+1:ℝ))).sqrt)
  have H:=hnum.div (hden.mul ((hm.div_const hN (by norm_num:(0:ℝ)<4)).sqrt.pow (r+1)))
  convert H using 1
  · ext t; simp only [QbK,Z35]
  · push_cast; ring
theorem Qoh (hN:Tendsto N atTop atTop) {α:ℝ}
    (hu:PowerRate N (fun t=>(u t:ℝ)) α) {r:ℕ} (hr:0<r) :
    PowerRate N (fun t=>Qbs (u t) r) (α*((r:ℝ)-3)/2):=by
  have H:=((hu.div_const hN (by positivity:(0:ℝ)<3*(r+1:ℝ))).inv hN).const_mul hN
    (by positivity:(0:ℝ)<((r+1:ℕ):ℝ)^2)
  have H':=H.mul (((hu.const_mul hN (by norm_num:(0:ℝ)<2)).sqrt.const_mul hN
    (by norm_num:(0:ℝ)<2)).pow (r-1))
  convert H' using 1
  · ext t; simp only [Qbs,Z35,Z52]
  · rw [Z47 (by omega:1≤r)]; norm_num; ring
theorem Qog (hN:Tendsto N atTop atTop) {α:ℝ}
    (hu:PowerRate N (fun t=>(u t:ℝ)) α) {r:ℕ} (hr:2≤r) (M:ℕ) :
    PowerRate N (fun t=>QbE (u t) r M) (α*((r:ℝ)-4)/2):=by
  have H:=(((hu.div_const hN (by positivity:(0:ℝ)<3*(r+1:ℝ))).inv hN).const_mul hN
    (by positivity:(0:ℝ)<((r+1:ℕ):ℝ)^2)).mul_const hN (by positivity:(0:ℝ)<(M:ℝ)+1)
  have H':=H.mul (((hu.const_mul hN (by norm_num:(0:ℝ)<2)).sqrt.const_mul hN
    (by norm_num:(0:ℝ)<2)).pow (r-2))
  convert H' using 1
  · ext t; simp only [QbE,Z35,Z52]
  · rw [Z47 hr]; norm_num; ring
theorem Qhf (hN:Tendsto N atTop atTop) {γ:ℝ} (hγ:0<γ)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) γ) (hω:PowerRate N ω 0) (s:ℕ) :
    PowerRate N (fun t=>QdH (J t) s (ω t)) (-γ*((s:ℝ)+1/2)):=by
  have hden:=(hJ.mul (hω.pow 2)).add_const hN (by simpa using hγ) (by norm_num:(0:ℝ)≤2)
  have hroot:=((PowerRate.const hN (by positivity:(0:ℝ)<4*((s:ℝ)+1))).div hden).sqrt
  have hp:=((hroot.const_mul hN (by norm_num:(0:ℝ)<2)).pow s).pow 2
  have H:=(hp.const_mul hN (by positivity:(0:ℝ)<((2:ℝ)^(s*s))^2)).mul hroot
  convert H using 1
  · rfl
  · push_cast; ring
theorem Qhg (hN:Tendsto N atTop atTop) {γ:ℝ} (hγ:0<γ)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) γ) (hω:PowerRate N ω 0) (s:ℕ) :
    PowerRate N (fun t=>Qeo (J t) s (ω t)) (-γ/2):=by
  have hden:=(hJ.mul (hω.pow 2)).add_const hN (by simpa using hγ) (by norm_num:(0:ℝ)≤2)
  have H:=(((PowerRate.const hN (by norm_num:(0:ℝ)<4)).div hden).sqrt).const_mul hN
    (by positivity:(0:ℝ)<((2:ℝ)^s)^2)
  convert H using 1
  · rfl
  · ring
theorem Qfk (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    {r:ℕ} (hr:0<r) (d:ℕ) :
    PowerRate N (fun t=>QbK (u t) (m t) r d (q t)*Qbs (u t) r)
      (-123/250-(62/125)*(d:ℝ)-(1/500)*(r:ℝ)):=by
  convert (Qhn hN hu hm hq r d).mul (Qoh hN hu hr) using 1; ring
theorem Qmu (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    {r:ℕ} (hr:2≤r) (d M:ℕ) :
    PowerRate N (fun t=>QbK (u t) (m t) r d (q t)*QbE (u t) r M)
      (-369/500-(62/125)*(d:ℝ)-(1/500)*(r:ℝ)):=by
  convert (Qhn hN hu hm hq r d).mul (Qog hN hu hr M) using 1; ring
theorem QmR (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω:PowerRate N ω 0)
    {r:ℕ} (hr:0<r) (k:Fin r→Qac) (hk:Odd (Qax k)) :
    PowerUpper N (fun t=>QcH (J t) (u t) (m t) r 300 (q t) (ω t) k) (-223/100):=by
  by_cases hlin:∃a,k=QaM a
  · have H:=(Qfk hN hu hm hq hr 1).mul
      (Qhf hN (by norm_num) hJ hω 300)
    have hb:-123/250-(62/125)*(1:ℝ)-(1/500)*(r:ℝ)+(-(1/125)*((300:ℝ)+1/2)) ≤ -223/100:=by
      have hh:(0:ℝ)≤r:=Z19 r
      linarith
    simpa only [QcH,if_pos hlin] using (H.upper hN).mono (by simpa using hb)
  · have hd:3≤∑h,(k h).order:=QnM k hk hlin
    obtain ⟨a,b,hab,_,_⟩:=QhU k hk hlin
    have hr2:2≤r:=by have:=a.isLt; have:=b.isLt; have:=hab; omega
    have H:=(Qmu hN hu hm hq hr2 (∑h,(k h).order) (2*(2^300))).mul
      (Qhg hN (by norm_num) hJ hω 300)
    have hb:-369/500-(62/125)*(∑h,(k h).order:ℕ)-(1/500)*(r:ℝ)+(-(1/125)/2) ≤ -223/100:=by
      have hd':(3:ℝ)≤(∑h,(k h).order:ℕ):=by exact_mod_cast hd
      have hr':(2:ℝ)≤r:=by exact_mod_cast hr2
      linarith
    simpa only [QcH,if_neg hlin] using (H.upper hN).mono (by simpa using hb)
theorem QmG (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω:PowerRate N ω 0)
    {r:ℕ} (hr:0<r) (k:Fin r→Qac) (hk:k≠QcR r) :
    PowerUpper N (fun t=>QdJ (J t) (u t) (m t) r 300 (q t) (ω t) k) (-37/25):=by
  by_cases hlin:∃a,k=QaM a
  · have H:=(Qfk hN hu hm hq hr 1).mul
      (Qhf hN (by norm_num) hJ hω 300)
    have hb:-123/250-(62/125)*(1:ℝ)-(1/500)*(r:ℝ)+(-(1/125)*((300:ℝ)+1/2)) ≤ -37/25:=by
      have hh:(0:ℝ)≤r:=Z19 r
      linarith
    simpa only [QdJ,if_pos hlin] using (H.upper hN).mono (by simpa using hb)
  · have hd:=(QnL k hk).resolve_left hlin
    have H:=(Qfk hN hu hm hq hr (∑h,(k h).order)).mul
      (Qhg hN (by norm_num) hJ hω 300)
    have hb:-123/250-(62/125)*(∑h,(k h).order:ℕ)-(1/500)*(r:ℝ)+(-(1/125)/2) ≤ -37/25:=by
      have hd':(2:ℝ)≤(∑h,(k h).order:ℕ):=by exact_mod_cast hd
      have hr':(0:ℝ)≤r:=Z19 r
      linarith
    simpa only [QdJ,if_neg hlin] using (H.upper hN).mono (by simpa using hb)
theorem Qmc (u r:ℕ):Z10 (Qab u r) ≤ u^r:=by
  simpa only [Fintype.card_fun,Z26] using Fintype.card_subtype_le (fun v:Fin r→Fin u => StrictMono v)
theorem Qhp (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (r:ℕ) (a:ℝ) :
    PowerUpper N (fun t=>Qdl (u t) (m t) r) a:=by
  have hcard:PowerUpper N (fun t=>(Z10 (Qab (u t) r):ℝ)) ((123/250)*(r:ℝ)):=by
    apply (hu.pow r).upper hN |>.of_abs_le
    exact Eventually.of_forall fun t=>by
      rw [abs_of_nonneg (Z19 _),abs_of_nonneg (by positivity)]
      exact_mod_cast Qmc (u t) r
  have hpoly:=hcard.mul hN (((hu.mul hm).sqrt.const_mul hN
    (by positivity:(0:ℝ)<48*((r+1:ℕ):ℝ))).upper hN)
  have hexpr:PowerRate N (fun t=>(m t:ℝ)/(1024*(u t:ℝ))) (1/250):=by
    convert hm.div (hu.const_mul hN (by norm_num:(0:ℝ)<1024)) using 1; norm_num
  have hexp:=hexpr.Qli hN (by norm_num) (a/2-((123/250)*(r:ℝ)+(123/250+62/125)/2))
  have H:=((PowerRate.const hN (by norm_num:(0:ℝ)<2)).upper hN).mul hN
    ((hpoly.mul hN hexp).pow hN 2)
  convert H using 1
  · ext t
    simp only [Qdl,Z35,neg_div]
    ring
  · push_cast; ring
theorem Qff (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hw:PowerRate N w 0) :
    PowerRate N (fun t=>Qao (u t) (m t) (q t) (w t)) (-1/500):=by
  have H:=((hw.pow 2).mul ((PowerRate.const hN
    (by positivity [Qcd]:(0:ℝ)<3*Qau)).div hq)).mul (hu.div hm).sqrt
  convert H using 1
  · rfl
  · norm_num
theorem Qhr (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hw:PowerRate N w 0) :
    PowerRate N (fun t=>4*(Qao (u t) (m t) (q t) (w t))^3000/
      (1-Qao (u t) (m t) (q t) (w t))) (-6):=by
  have hρ:=Qff hN hu hm hq hw
  have hz:=(hρ.upper hN).Qey hN (by norm_num)
  have hden:PowerRate N (fun t=>1-Qao (u t) (m t) (q t) (w t)) 0:=by
    apply PowerRate.of_tendsto hN (by norm_num:(0:ℝ)<1)
    simpa using tendsto_const_nhds.sub hz
  convert ((hρ.pow 3000).const_mul hN (by norm_num:(0:ℝ)<4)).div hden using 1
  norm_num
theorem Qmt (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω:PowerRate N ω 0) (r:ℕ) :
    PowerUpper N (fun t=>QcG (J t) (u t) (m t) r 300 (q t) (ω t)) (-223/100):=by
  by_cases hr:r=0
  · simpa only [QcG,if_pos hr] using PowerUpper.zero hN (-223/100)
  have hs:PowerUpper N (fun t=>∑k:Fin r→Qac,
      if Odd (Qax k) then QcH (J t) (u t) (m t) r 300 (q t) (ω t) k else 0) (-223/100):=by
    apply PowerUpper.sum hN Z16
    intro k _
    by_cases hk:Odd (Qax k)
    · simpa only [if_pos hk] using QmR hN hu hm hq hJ hω (by omega) k hk
    · simpa only [if_neg hk] using PowerUpper.zero hN (-223/100)
  have hc:(0:ℝ)<8*(Z10 (Fin r→Qac):ℝ):=by
    have hp:0<Z10 (Fin r→Qac):=Fintype.card_pos_iff.mpr ⟨fun _=>.unchanged⟩
    positivity
  have H:=(((PowerRate.const hN hc).upper hN).mul hN hs)
  simp only [zero_add] at H
  simpa only [QcG,if_neg hr] using H.add hN (Qhp hN hu hm r (-223/100))
theorem Qmo (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω:PowerRate N ω 0) (r:ℕ) :
    PowerUpper N (fun t=>QdI (J t) (u t) (m t) r 300 (q t) (ω t)) (-37/25):=by
  by_cases hr:r=0
  · simpa only [QdI,if_pos hr] using PowerUpper.zero hN (-37/25)
  have hs:PowerUpper N (fun t=>∑k:Fin r→Qac,
      if k=QcR r then 0 else QdJ (J t) (u t) (m t) r 300 (q t) (ω t) k) (-37/25):=by
    apply PowerUpper.sum hN Z16
    intro k _
    by_cases hk:k=QcR r
    · simpa only [if_pos hk] using PowerUpper.zero hN (-37/25)
    · simpa only [if_neg hk] using QmG hN hu hm hq hJ hω (by omega) k hk
  have hc:(0:ℝ)<2*(Z10 (Fin r→Qac):ℝ):=by
    have hp:0<Z10 (Fin r→Qac):=Fintype.card_pos_iff.mpr ⟨fun _=>.unchanged⟩
    positivity
  have H:=(((PowerRate.const hN hc).upper hN).mul hN hs)
  simp only [zero_add] at H
  simpa only [QdI,if_neg hr] using H.add hN (Qhp hN hu hm r (-37/25))
theorem Qms (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω:PowerRate N ω 0) (hw:PowerRate N w 0) :
    PowerUpper N (fun t=>Qdm (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t)) (-223/100):=by
  have hs:PowerUpper N (fun t=>∑r∈Z5 3000,(w t)^(2*r)*
      QcG (J t) (u t) (m t) r 300 (q t) (ω t)) (-223/100):=by
    apply PowerUpper.sum hN (Z5 3000)
    intro r _
    simpa only [zero_mul,zero_add] using ((hw.pow (2*r)).upper hN).mul hN (Qmt hN hu hm hq hJ hω r)
  exact hs.add hN ((Qhr hN hu hm hq hw).upper hN |>.mono (by norm_num))
theorem Qmn (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω:PowerRate N ω 0) (hw:PowerRate N w 0) :
    PowerUpper N (fun t=>Qfi (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t)) (-37/25):=by
  have hs:PowerUpper N (fun t=>∑r∈Z5 3000,(w t)^(2*r)*
      QdI (J t) (u t) (m t) r 300 (q t) (ω t)) (-37/25):=by
    apply PowerUpper.sum hN (Z5 3000)
    intro r _
    simpa only [zero_mul,zero_add] using ((hw.pow (2*r)).upper hN).mul hN (Qmo hN hu hm hq hJ hω r)
  exact hs.add hN ((Qhr hN hu hm hq hw).upper hN |>.mono (by norm_num))
theorem QmJ (hN:Tendsto N atTop atTop)
    (hu:PowerRate N (fun t=>(u t:ℝ)) (123/250))
    (hm:PowerRate N (fun t=>(m t:ℝ)) (62/125)) (hq:PowerRate N q 0)
    (hJ:PowerRate N (fun t=>(J t:ℝ)) (1/125)) (hω:PowerRate N ω 0) (hw:PowerRate N w 0) :
    ∀ᶠt in atTop,
      64*Qdm (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t) ≤ (N t)^(-11/5:ℝ) ∧
      64*Qfi (J t) (u t) (m t) 3000 300 (q t) (ω t) (w t) ≤ (N t)^(-7/5:ℝ):=by
  have hc:=(PowerRate.const hN (by norm_num:(0:ℝ)<64)).upper hN
  have hs:=hc.mul hN (Qms hN hu hm hq hJ hω hw)
  have hp:=hc.mul hN (Qmn hN hu hm hq hJ hω hw)
  filter_upwards [hs (-11/5) (by norm_num),hp (-7/5) (by norm_num)] with t hs hp
  exact ⟨(le_abs_self _).trans hs,(le_abs_self _).trans hp⟩
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
variable {N f g:ℕ→ℝ} {α β:ℝ}
theorem PowerRate.sub_lower (hN:Tendsto N atTop atTop)
    (hf:PowerRate N f α) (hg:PowerRate N g β) (hβα:β<α) :
    PowerRate N (fun t=>f t-g t) α:=by
  have hz:=((hg.div hf).upper hN).Qey hN (sub_neg.mpr hβα)
  apply hf.of_ratio hN (by norm_num:(0:ℝ)<1)
  have H:Tendsto (fun t=>1-g t/f t) atTop (𝓝 1):=by
    simpa using tendsto_const_nhds.sub hz
  apply H.congr'
  filter_upwards [hf.1] with t ht
  field_simp [ht.ne']
theorem PowerRate.QnG (hN:Tendsto N atTop atTop) {f g:ℕ→ℕ}
    (hf:PowerRate N (fun t=>(f t:ℝ)) α)
    (hg:PowerRate N (fun t=>(g t:ℝ)) β) (hβα:β<α) :
    PowerRate N (fun t=>(f t-g t:ℕ)) α:=by
  have H:=hf.sub_lower hN hg hβα
  apply H.congr
  filter_upwards [H.1] with t ht
  have hg:g t≤f t:=by exact_mod_cast (sub_pos.mp ht).le
  rw [Z47 hg]
def Qan (N:ℝ):ℕ:=⌊N^(62/125:ℝ)⌋₊
def QaL (N:ℝ):ℕ:=⌊N^(123/250:ℝ)⌋₊
def QbW (N:ℝ):ℕ:=2*Qan N-1
def QfI (N:ℝ):ℕ:=⌊N/(QbW N:ℝ)⌋₊
def Qbu (q N:ℝ):ℕ :=
  ⌊((QfI N:ℝ)-QaL N)/
    (2*(QaI q (Qan N):ℝ)+1)⌋₊
def QbH (q N:ℝ):ℕ :=
  Qbu q N*(2*QaI q (Qan N)+1)+QaL N
def QcN (q N:ℝ):ℤ:=((QbH q N/2:ℕ):ℤ)-1
theorem QcO (hN:Tendsto N atTop atTop) :
    PowerRate N (fun t=>(Qan (N t):ℝ)) (62/125):=by
  have H:=((PowerRate.base hN).rpow (62/125)).nat_floor hN (by norm_num)
  simpa only [Qan,one_mul] using H
theorem Qdv (hN:Tendsto N atTop atTop) :
    PowerRate N (fun t=>(QaL (N t):ℝ)) (123/250):=by
  have H:=((PowerRate.base hN).rpow (123/250)).nat_floor hN (by norm_num)
  simpa only [QaL,one_mul] using H
theorem QiI (hN:Tendsto N atTop atTop) :
    PowerRate N (fun t=>(QbW (N t):ℝ)) (62/125):=by
  have hh:PowerRate N (fun t=>(2*Qan (N t):ℕ)) (62/125):=by
    simpa only [Z35,Z52] using (QcO hN).const_mul hN (by norm_num:(0:ℝ)<2)
  exact hh.QnG hN (PowerRate.const hN (by norm_num:(0:ℝ)<(1:ℕ))) (by norm_num)
theorem QiH (hN:Tendsto N atTop atTop) :
    PowerRate N (fun t=>(QfI (N t):ℝ)) (63/125):=by
  have H:=((PowerRate.base hN).div (QiI hN)).nat_floor hN (by norm_num)
  convert H using 1
  · rfl
  · norm_num
theorem QiJ (hN:Tendsto N atTop atTop) {q:ℕ→ℝ}
    (hq:PowerRate N q 0) :
    PowerRate N (fun t=>(QaI (q t) (Qan (N t)):ℝ)) (62/125):=by
  have H:=(hq.mul (QcO hN)).nat_floor hN (by norm_num)
  simpa only [QaI,zero_add] using H
theorem QfJ (hN:Tendsto N atTop atTop) {q:ℕ→ℝ}
    (hq:PowerRate N q 0) :
    PowerRate N (fun t=>(Qbu (q t) (N t):ℝ)) (1/125):=by
  have hn:=(QiH hN).sub_lower hN (Qdv hN) (by norm_num)
  have hd:=((QiJ hN hq).const_mul hN (by norm_num:(0:ℝ)<2)).add_const hN
    (by norm_num) (by norm_num:(0:ℝ)≤1)
  have H:=(hn.div hd).nat_floor hN (by norm_num)
  convert H using 1
  · rfl
  · norm_num
theorem Qhk (hN:Tendsto N atTop atTop) {q:ℕ→ℝ}
    (_hq:∀t,0<q t)
    (hΛ:Tendsto (fun t=>(q t)^(-3:ℤ)/Z8 (N t)) atTop (𝓝 0)) :
    PowerRate N (fun t=>QaV (q t)) 0:=by
  refine ⟨Eventually.of_forall (fun t=>Qhj _),?_⟩
  have H:=(hΛ.const_mul (-(32+3*Qbj))).sub
    ((Real.tendsto_log_atTop.comp hN).const_div_atTop (Z8 1536))
  simp only [mul_zero,sub_zero] at H
  apply H.congr'
  filter_upwards [] with t
  rw [QaV,Real.log_div (Z74 _).ne' (by norm_num),Real.log_exp]
  simp only [zpow_neg,zpow_ofNat,Z67]
  ring
theorem QdD (hN:Tendsto N atTop atTop) {q:ℕ→ℝ}
    (hq:∀t,q t∈Z12 0 1)
    (hΛ:Tendsto (fun t=>(q t)^(-3:ℤ)/Z8 (N t)) atTop (𝓝 0)) :
    PowerRate N q 0:=by
  refine ⟨Eventually.of_forall (fun t=>(hq t).1),?_⟩
  apply squeeze_zero_norm' _ hΛ
  filter_upwards [hN.eventually_gt_atTop 1] with t hNt
  have hp:=(hq t).1
  have hle:=(hq t).2
  have hqinv:1≤(q t)⁻¹:=(one_le_inv₀ hp).mpr hle
  have hlog:|Z8 (q t)| ≤ (q t)^(-3:ℤ):=by
    rw [abs_of_nonpos (Real.log_nonpos hp.le hle),←Real.log_inv,zpow_neg,zpow_ofNat]
    have hh:=Z96 (inv_pos.mpr hp)
    have hcube:(q t)⁻¹ ≤ ((q t)⁻¹)^3:=by nlinarith [sq_nonneg ((q t)⁻¹-1)]
    rw [←inv_pow]
    linarith
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (Z66 hNt)]
  exact div_le_div_of_nonneg_right hlog (Z66 hNt).le
theorem Qqk {q w:ℕ→ℝ} (hN:Tendsto N atTop atTop)
    (hq:∀t,q t∈Z12 0 1)
    (hΛ:Tendsto (fun t=>(q t)^(-3:ℤ)/Z8 (N t)) atTop (𝓝 0))
    (hw:PowerRate N w 0) :
    ∀ᶠt in atTop,
      64*Qdm (Qbu (q t) (N t)) (QaL (N t))
        (Qan (N t)) 3000 300 (q t) (QaV (q t)) (w t) ≤ (N t)^(-11/5:ℝ) ∧
      64*Qfi (Qbu (q t) (N t)) (QaL (N t))
        (Qan (N t)) 3000 300 (q t) (QaV (q t)) (w t) ≤ (N t)^(-7/5:ℝ):=by
  exact QmJ hN (Qdv hN) (QcO hN)
    (QdD hN hq hΛ) (QfJ hN (QdD hN hq hΛ))
    (Qhk hN (fun t=>(hq t).1) hΛ) hw
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
def Qcz (m:ℕ) (hm:4 ≤ m):Fin m :=
  ⟨m/2-1,by omega⟩
theorem QfK (m:ℕ) (hm:4 ≤ m) :
    1 ≤ (Qcz m hm).val ∧ (Qcz m hm).val+1 < m:=by
  simp only [Qcz]; omega
theorem Qqf (m:ℕ) (hm:4 ≤ m) :
    |((Qcz m hm).val:ℝ)-(m:ℝ)/2| ≤ 2:=by
  have h1:2*(m/2) ≤ m:=Nat.mul_div_le m 2
  have h2:m<2*(m/2+1):=by omega
  have h3:1 ≤ m/2:=by omega
  simp only [Qcz,Z47 h3,Z25]
  rw [abs_le]
  have hh1:(2:ℝ)*(m/2:ℕ) ≤ m:=by exact_mod_cast h1
  have hh2:(m:ℝ)<2*((m/2:ℕ)+1):=by exact_mod_cast h2
  constructor <;> linarith
theorem Qqg (u m:ℕ) (hm:4 ≤ m) :
    Qae (periodSlot (u:=u) (fun _=>Qcz m hm)):=by
  have hi:=QfK m hm
  exact QkI _ hi.1 hi.2 (by omega) id strictMono_id
theorem Qhq (J K t s:ℕ) (hK:12*(J+2^s+1) ≤ K) :
    let a:ℤ:=(((J*(2*t+1)+K)/2:ℕ):ℤ)-1
    (J*t+J:ℕ) ≤ a ∧ a+(2^s:ℕ) ≤ (J*t+K:ℕ) ∧
    (K:ℝ)/3 ≤ 2*((a-(J*t:ℕ):ℤ)-J)+1 ∧
    (K:ℝ)/3 ≤ 2*K-(2*((a-(J*t:ℕ):ℤ)+(2:ℝ)^s)+1):=by
  have he:(J*(2*t+1)+K)/2=J*t+(J+K)/2:=by
    rw [show J*(2*t+1)+K=2*(J*t)+(J+K) by ring,Nat.mul_add_div (by norm_num)]
  have hlo:2*((J+K)/2) ≤ J+K:=Nat.mul_div_le _ 2
  have hhi:J+K<2*((J+K)/2+1):=by omega
  have hK1:12*(J+1) ≤ K:=by nlinarith [Nat.zero_le (2^s)]
  dsimp only
  rw [he]
  have hi1:J+1 ≤ (J+K)/2:=by omega
  have hi2:(J+K)/2+(2^s:ℕ) ≤ K+1:=by omega
  constructor
  · apply (le_sub_iff_add_le).mpr
    exact_mod_cast (show J*t+J+1 ≤ J*t+(J+K)/2 from by omega)
  constructor
  · push_cast only [Z23]
    omega
  have hl:(2:ℝ)*((J+K)/2:ℕ) ≤ J+K:=by exact_mod_cast hlo
  have hh:(J:ℝ)+K<2*(((J+K)/2:ℕ)+1):=by exact_mod_cast hhi
  have hk:(12:ℝ)*((J:ℝ)+(2:ℝ)^s+1) ≤ K:=by exact_mod_cast hK
  simp only [Z23,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one,Int.cast_mul,Z35]
  constructor <;> nlinarith [show (0:ℝ) ≤ (2:ℝ)^s by positivity]
theorem QoZ (s:ℕ):(Qak s).coeff 0=1:=by
  induction s with
  | zero => simp [Qak]
  | succ s ih =>
    have hp:(0:ℤ)<(2^s:ℕ):=by positivity
    rw [QfB,ih,(QdT s).1 _ (Or.inl (by omega)),sub_zero]
theorem Qnn {m:ℕ} (off:Fin m) (hi:1 ≤ off.val ∧ off.val+1 < m)
    (u s:ℕ) (a:ℤ) (ha:0 ≤ a) (hau:a<u) :
    Qbp off hi u s a (-1) ≠ Qbp off hi u s a 1:=by
  intro he
  have H:=Qok m u he
  have hj:a.toNat<u:=by omega
  have h:=congrArg (fun f=>((f ⟨a.toNat,hj⟩):Fin m).val) H
  have ha':(a.toNat:ℤ)=a:=Z95 ha
  simp only [Qcj,ha',sub_self,QoZ] at h
  have hpos:(0:ℤ)<(2^s:ℕ):=by positivity
  norm_num [QaT,hpos,motifShift] at h
theorem QmF {N:ℝ} {m K t:ℕ}
    (hL:0<2*m-1) (hN:0 ≤ N) (hK:(K:ℝ) ≤ ⌊N/(2*m-1:ℕ)⌋₊) :
    let F:ℕ:=⌊N/(2*m-1:ℕ)⌋₊
    let J:ℕ:=⌊((F:ℝ)-K)/(2*t+1:ℕ)⌋₊
    let P:ℕ:=J*(2*t+1)+K
    (P:ℝ)*(2*m-1:ℕ) ≤ N ∧ N<((P:ℝ)+(2*t+1:ℕ)+1)*(2*m-1:ℕ):=by
  dsimp only
  set F:ℕ:=⌊N/(2*m-1:ℕ)⌋₊
  set J:ℕ:=⌊((F:ℝ)-K)/(2*t+1:ℕ)⌋₊
  have hd:(0:ℝ)<(2*t+1:ℕ):=by positivity
  have hl:(0:ℝ)<(2*m-1:ℕ):=by exact_mod_cast hL
  have hjlo:=Nat.floor_le (div_nonneg (sub_nonneg.mpr hK) hd.le)
  have hjhi:=Nat.lt_floor_add_one (((F:ℝ)-K)/(2*t+1:ℕ))
  change (J:ℝ) ≤ _ at hjlo
  change _<(J:ℝ)+1 at hjhi
  have hflo:=Nat.floor_le (div_nonneg hN hl.le)
  have hfhi:=Nat.lt_floor_add_one (N/(2*m-1:ℕ))
  change (F:ℝ) ≤ _ at hflo
  change _<(F:ℝ)+1 at hfhi
  have hp:(J:ℝ)*(2*t+1:ℕ)+K ≤ F:=by
    have H:=(le_div_iff₀ hd).mp hjlo
    linarith
  have hp':(F:ℝ)<(J:ℝ)*(2*t+1:ℕ)+K+(2*t+1:ℕ):=by
    have H:=(div_lt_iff₀ hd).mp hjhi
    nlinarith
  constructor
  · push_cast
    simpa only [Z23,Z35,Z52,Z25] using (mul_le_mul_of_nonneg_right hp hl.le).trans ((le_div_iff₀ hl).mp hflo)
  · have H:=(div_lt_iff₀ hl).mp hfhi
    push_cast at hp' ⊢
    nlinarith
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
variable {N f g:ℕ→ℝ} {α β:ℝ}
theorem PowerRate.Qdc (hN:Tendsto N atTop atTop)
    (hf:PowerRate N f α) (hg:PowerRate N g β) (hab:α<β) :
    ∀ᶠt in atTop,f t<g t:=by
  have hz:=((hf.div hg).upper hN).Qey hN (sub_neg.mpr hab)
  filter_upwards [hz.eventually_lt_const (by norm_num:(0:ℝ)<1),hg.1] with t ht hp
  exact (div_lt_one hp).mp ht
theorem PowerRate.log_base (hN:Tendsto N atTop atTop) :
    PowerRate N (fun t=>Z8 (N t)) 0:=by
  refine ⟨(hN.eventually_gt_atTop 1).mono (fun _ ht=>Z66 ht),?_⟩
  convert
    (isLittleO_log_rpow_atTop (by norm_num:(0:ℝ)<1)).tendsto_div_nhds_zero.comp
      (Real.tendsto_log_atTop.comp hN) using 1
  ext t
  simp only [Z67,Real.rpow_one]
structure QeH (q N:ℝ):Prop where
  m_large:128 ≤ Qan N
  K_pos:0 < QaL N
  K_le_m:QaL N ≤ Qan N
  seed:16 ≤ q^3*(Qan N:ℝ)
  count:8 ≤ ((QaL N*Qan N:ℕ):ℝ)*q^2
  anchor_margin:12*(Qbu q N+2^300+1) ≤ QaL N
  smoothing_margin:((2*(2^300):ℕ):ℝ) < (QaL N:ℝ)/(3*(3000+1:ℝ))
  length_lower:N/2 ≤ (QbH q N:ℝ)*(QbW N:ℝ)
  length_upper:(QbH q N:ℝ)*(QbW N:ℝ) ≤ N
theorem Qqi {q:ℕ→ℝ} (hN:Tendsto N atTop atTop)
    (hq:∀t,q t∈Z12 0 1)
    (hΛ:Tendsto (fun t=>(q t)^(-3:ℤ)/Z8 (N t)) atTop (𝓝 0)) :
    ∀ᶠt in atTop,QeH (q t) (N t):=by
  have hm:=QcO hN
  have hK:=Qdv hN
  have hqrate:=QdD hN hq hΛ
  have hJ:=QfJ hN hqrate
  have hL:=QiI hN
  have hF:=QiH hN
  have ht:=QiJ hN hqrate
  have hm128:=(hm.Qdx hN (by norm_num)).eventually_ge_atTop 128
  have hKm:=hK.Qdc hN hm (by norm_num)
  have hKF:=hK.Qdc hN hF (by norm_num)
  have hseed:=((hqrate.pow 3).mul hm).Qdx hN (by norm_num)
  have hcount:=((hK.mul hm).mul (hqrate.pow 2)).Qdx hN (by norm_num)
  have hanchor:=((hJ.add_const hN (by norm_num) (by positivity:(0:ℝ)≤2^300+1)).const_mul
    hN (by norm_num:(0:ℝ)<12)).Qdc hN hK (by norm_num)
  have hsm:=(hK.Qdx hN (by norm_num)).eventually_gt_atTop ((2*(2^300):ℝ)*(3*3001))
  have hloss:PowerRate N (fun t=>(2*(QaI (q t) (Qan (N t)):ℝ)+2)*
      (QbW (N t):ℝ)) (124/125):=by
    convert ((ht.const_mul hN (by norm_num:(0:ℝ)<2)).add_const hN
      (by norm_num) (by norm_num:(0:ℝ)≤2)).mul hL using 1
    norm_num
  have hloss':=hloss.Qdc hN ((PowerRate.base hN).div_const hN (by norm_num:(0:ℝ)<2)) (by norm_num)
  filter_upwards [hN.eventually_gt_atTop 0,hm128,hK.1,hKm,hKF,
    hseed.eventually_ge_atTop 16,hcount.eventually_ge_atTop 8,hanchor,hsm,hloss'] with t hNt hm128 hKpos hKm hKF hs hc ha hsm hloss
  have hmn:128 ≤ Qan (N t):=by exact_mod_cast hm128
  have hKn:0 < QaL (N t):=by exact_mod_cast hKpos
  have hLpos:0 < QbW (N t):=by unfold QbW; omega
  have hcnt:=QmF (m:=Qan (N t))
    (K:=QaL (N t)) (t:=QaI (q t) (Qan (N t)))
    (N:=N t) hLpos hNt.le hKF.le
  have hcnt':(QbH (q t) (N t):ℝ)*(QbW (N t):ℝ) ≤ N t ∧
      N t<((QbH (q t) (N t):ℝ)+(2*QaI (q t) (Qan (N t))+1:ℕ)+1)*
        (QbW (N t):ℝ):=by
    simpa only [QbH,Qbu,QfI,QbW,
      Z23,Z35,Z52,Z25] using hcnt
  refine ⟨hmn,hKn,?_,hs,?_,?_,?_,?_,hcnt'.1⟩
  · exact_mod_cast hKm.le
  · simpa only [Z35] using hc
  · apply (Nat.cast_le (α:=ℝ)).mp
    simp only [Z35,Z23,Nat.cast_pow,Z52,Z25]
    simpa only [add_assoc] using ha.le
  · apply (lt_div_iff₀ (by norm_num:(0:ℝ)<3*(3000+1))).mpr
    simpa only [Z35,Nat.cast_pow,Z52,show (3000+1:ℝ)=3001 by norm_num] using hsm
  · have H:=hcnt'.2
    push_cast at H
    nlinarith only [H,hloss]
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
def Qcp (q:ℝ) (k:ℕ):ℝ:=(6*(2*k:ℕ):ℝ)*(2/q)
theorem QiK {N q:ℕ→ℝ} {k:ℕ→ℕ}
    (hN:Tendsto N atTop atTop) (hq:PowerRate N q 0)
    (hk:PowerRate N (fun t=>(k t:ℝ)) 0) :
    PowerRate N (fun t=>Qcp (q t) (k t)) 0:=by
  have H:=(hk.const_mul hN (by norm_num:(0:ℝ)<24)).div hq
  convert H using 1
  · ext t
    simp only [Qcp,Z35,Z52]
    ring
  · norm_num
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
variable {N q w:ℕ→ℝ} {k:ℕ→ℕ}
def Qdf (N q w:ℝ):ℝ :=
  4*(Qao (QaL N) (Qan N) q w/
    (1-Qao (QaL N) (Qan N) q w))
theorem Qmg (hN:Tendsto N atTop atTop)
    (hq:PowerRate N q 0) (hw:PowerRate N w 0) :
    PowerRate N (fun t=>Qdf (N t) (q t) (w t)) (-1/500):=by
  have hρ:=Qff hN (Qdv hN) (QcO hN) hq hw
  have hden:=(PowerRate.const hN (by norm_num:(0:ℝ)<1)).sub_lower hN hρ (by norm_num)
  simpa only [Qdf,sub_zero] using (hρ.div hden).const_mul hN (by norm_num:(0:ℝ)<4)
theorem Qmx (hN:Tendsto N atTop atTop)
    (hq:PowerRate N q 0) (hw:PowerRate N w 0) (hk:∀ᶠt in atTop,1 ≤ k t) :
    ∀ᶠt in atTop,
      Z0 (6*(Qdf (N t) (q t) (w t))^(k t)) ≤
        Z1 (-(k t:ℝ)*Z8 (N t)/2000):=by
  have hfac:=Qmg hN hq hw
  have hu:=hfac.upper hN (-3/2000) (by norm_num)
  filter_upwards [hk,hfac.1,hu,hN.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hN).eventually_ge_atTop (2000*Z8 6)] with t hk hp hu hn hlog
  rw [abs_of_pos hp] at hu
  have hh:=Real.log_le_log hp hu
  rw [Real.log_rpow (by linarith:0<N t)] at hh
  have hk':(1:ℝ) ≤ k t:=by exact_mod_cast hk
  have hmul:=mul_le_mul_of_nonneg_left hh (by positivity:(0:ℝ) ≤ k t)
  have hl:0 ≤ Z8 (N t):=(Z66 hn).le
  have hg:Z8 6 ≤ (k t:ℝ)*Z8 (N t)/2000:=by
    change 2000*Z8 6 ≤ Z8 (N t) at hlog
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') hl]
  have hexp:Z0 (6*Qdf (N t) (q t) (w t)^(k t)) =
      Z1 ((Z8 6+(k t:ℝ)*Z8 (Qdf (N t) (q t) (w t)))/2):=by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity),Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow]
    congr 1
    ring
  rw [hexp]
  exact Real.exp_le_exp.mpr (by nlinarith)
theorem QmD (hN:Tendsto N atTop atTop)
    (hq:PowerRate N q 0) (hω:PowerRate N (fun t=>QaV (q t)) 0)
    (hk:PowerRate N (fun t=>(k t:ℝ)) 0) :
    ∀ᶠt in atTop,
      2*Z1 (-((QaL (N t)*Qan (N t):ℕ):ℝ)*(q t)^4/64)+
        Z1 (-(Qbu (q t) (N t):ℝ)*(QaV (q t))^4/16) ≤
        3*Z1 (-(k t:ℝ)*Z8 (N t)):=by
  have hlow:PowerRate N (fun t=>(k t:ℝ)*Z8 (N t)) 0:=by
    simpa using hk.mul (PowerRate.log_base hN)
  have hfirst:=(((Qdv hN).mul (QcO hN)).mul
    (hq.pow 4)).div_const hN (by norm_num:(0:ℝ)<64)
  have hsecond:=((QfJ hN hq).mul (hω.pow 4)).div_const hN (by norm_num:(0:ℝ)<16)
  filter_upwards [hlow.Qdc hN hfirst (by norm_num),hlow.Qdc hN hsecond (by norm_num)] with t h1 h2
  have he1:=Real.exp_le_exp.mpr (neg_le_neg h1.le)
  have he2:=Real.exp_le_exp.mpr (neg_le_neg h2.le)
  push_cast
  simp only [neg_div,neg_mul] at he1 he2 ⊢
  linarith
theorem QmB {n A:ℕ→ℝ} (hN:Tendsto N atTop atTop)
    (hn:Tendsto n atTop atTop) (hA:∀ᶠt in atTop,1 ≤ A t)
    (hq:∀t,q t∈Z12 0 1)
    (hΛ:Tendsto (fun t=>(q t)^(-3:ℤ)/Z8 (N t)) atTop (𝓝 0))
    (hk:PowerRate N (fun t=>(k t:ℝ)) 0) (hk1:∀ᶠt in atTop,1 ≤ k t)
    (hmoment:∀ᶠt in atTop,10^6*A t*Z8 (n t) ≤ (k t:ℝ)*Z8 (N t)) :
    ∀ᶠt in atTop,
      Qdi (Qbu (q t) (N t)) (QaL (N t))
        (Qan (N t)) (k t) (q t) (QaV (q t))
        (Qcp (q t) (k t)) ≤ (n t)^(-100*A t):=by
  have hqrate:=QdD hN hq hΛ
  have hω:=Qhk hN (fun t=>(hq t).1) hΛ
  have hw:=QiK hN hqrate hk
  have hclip:=Qmx hN hqrate hw hk1
  have hmeta:=QmD hN hqrate hω hk
  filter_upwards [hclip,hmeta,hmoment,hA,hn.eventually_gt_atTop 1,
    (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop (Z8 4)] with t hc hm hmom hA hn hlog
  have hAn:0 ≤ A t*Z8 (n t):=mul_nonneg (by linarith) (Z66 hn).le
  have he1:Z1 (-(k t:ℝ)*Z8 (N t)/2000) ≤ Z1 (-500*(A t*Z8 (n t))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2:Z1 (-(k t:ℝ)*Z8 (N t)) ≤ Z1 (-500*(A t*Z8 (n t))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have herr:Qdi (Qbu (q t) (N t)) (QaL (N t))
      (Qan (N t)) (k t) (q t) (QaV (q t))
      (Qcp (q t) (k t)) ≤ 4*Z1 (-500*(A t*Z8 (n t))):=by
    unfold Qdi
    change Z0 (6*Qdf (N t) (q t) (Qcp (q t) (k t))^(k t))+_ ≤ _
    nlinarith only [hc,hm,he1,he2]
  apply herr.trans
  rw [Real.rpow_def_of_pos (by linarith:0<n t)]
  calc
    4*Z1 (-500*(A t*Z8 (n t))) =
        Z1 (Z8 4-500*(A t*Z8 (n t))):=by
      rw [Real.exp_sub,Real.exp_log (by norm_num)]
      rw [show -500*(A t*Z8 (n t)) = -(500*(A t*Z8 (n t))) by ring,Real.exp_neg]
      rfl
    _ ≤ Z1 (Z8 (n t)*(-100*A t)):=by
      apply Real.exp_le_exp.mpr
      have hAL:Z8 4 ≤ A t*Z8 (n t):=hlog.trans (le_mul_of_one_le_left (Z66 hn).le hA)
      nlinarith
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
variable {N f g:ℕ→ℝ} {α β:ℝ}
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
def QbX (q N:ℝ) (τ:ℝ):List Bool :=
  if hm:4 ≤ Qan N then
    Qbp (Qcz (Qan N) hm)
      (QfK _ hm) (QbH q N) 300 (QcN q N) τ
  else []
def QdY (q N:ℝ) (k:ℕ):ℝ :=
  Qdi (Qbu q N) (QaL N) (Qan N) k q
    (QaV q) (Qcp q k)
theorem QiL {q N:ℝ} (hm:4 ≤ Qan N) (τ:ℝ) :
    (QbX q N τ).length=QbH q N*QbW N:=by
  rw [QbX,dif_pos hm,Qnm]
  rfl
theorem Qqh {q N:ℝ} (H:QeH q N) :
    QbX q N (-1) ≠ QbX q N 1:=by
  have hm:4 ≤ Qan N:=(by norm_num:4 ≤ 128).trans H.m_large
  have ha:=Qhq (Qbu q N) (QaL N)
    (QaI q (Qan N)) 300 H.anchor_margin
  have hap:(0:ℤ) ≤ QcN q N:=(Int.natCast_nonneg _).trans ha.1
  have hau:QcN q N<(QbH q N:ℤ):=by
    have h1:=ha.2.1
    have he:(Qbu q N*QaI q (Qan N)+QaL N:ℕ) ≤ QbH q N:=by
      unfold QbH
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      omega
    have hp:(0:ℤ)<(2^300:ℕ):=by positivity
    have hh:((Qbu q N*QaI q (Qan N)+QaL N:ℕ):ℤ) ≤ QbH q N:=Int.ofNat_le.mpr he
    exact (lt_add_of_pos_right (QcN q N) hp).trans_le (h1.trans hh)
  simp only [QbX,dif_pos hm]
  exact Qnn _ _ _ _ _ hap hau
theorem Qqj {N q n A:ℕ→ℝ} {k:ℕ→ℕ}
    (hN:Tendsto N atTop atTop) (hn:Tendsto n atTop atTop)
    (hA:∀ᶠt in atTop,1 ≤ A t) (hq:∀t,q t∈Z12 0 (1/2:ℝ))
    (hΛ:Tendsto (fun t=>(q t)^(-3:ℤ)/Z8 (N t)) atTop (𝓝 0))
    (hk:PowerRate N (fun t=>(k t:ℝ)) 0) (hk1:∀ᶠt in atTop,1 ≤ k t)
    (hmoment:∀ᶠt in atTop,10^6*A t*Z8 (n t) ≤ (k t:ℝ)*Z8 (N t)) :
    ∀ᶠt in atTop,
      QeH (q t) (N t) ∧
      QdY (q t) (N t) (k t) ≤ (n t)^(-100*A t) ∧
      Nonempty (QbN (q t) (QbX (q t) (N t) (-1))
        (QbX (q t) (N t) 1) (k t) (QdY (q t) (N t) (k t)) ((N t)^(-11/5:ℝ))):=by
  have hq' (t):q t ∈ Z12 0 1:=⟨(hq t).1,by linarith [(hq t).2]⟩
  have hqr:=QdD hN hq' hΛ
  have hw:=QiK hN hqr hk
  have herr:=QmB hN hn hA hq' hΛ hk hk1 hmoment
  have hgeo:=Qqi hN hq' hΛ
  have hcap:=Qqk hN hq' hΛ hw
  have hρ:=(Qff hN (Qdv hN) (QcO hN) hqr hw).upper hN |>.Qey hN (by norm_num)
  have hsmall:=((tendsto_rpow_neg_atTop (by norm_num:(0:ℝ)<100)).comp hn).eventually_le_const (by norm_num:(0:ℝ)<1/2)
  filter_upwards [hgeo,hcap,herr,hk1,hA,hn.eventually_gt_atTop 1,hN.eventually_gt_atTop 0,
    hρ.eventually_le_const (by norm_num:(0:ℝ)<1/2),hsmall] with t hg hcap he hk1 ha hnt hNt hρ hsmall
  have hm:4 ≤ Qan (N t):=(by norm_num:4 ≤ 128).trans hg.m_large
  let off:=Qcz (Qan (N t)) hm
  have hi:=QfK _ hm
  have hanchor:=Qhq (Qbu (q t) (N t)) (QaL (N t))
    (QaI (q t) (Qan (N t))) 300 hg.anchor_margin
  change _ ≤ QcN (q t) (N t) ∧ QcN (q t) (N t)+(2^300:ℕ) ≤ _ ∧ _ at hanchor
  have he':QdY (q t) (N t) (k t) ≤ 1/2:=by
    exact he.trans ((Real.rpow_le_rpow_of_exponent_le hnt.le (by linarith:-100*A t ≤ -100)).trans hsmall)
  have hc:Z0 (6*(4*(Qao (QaL (N t)) (Qan (N t)) (q t)
      (Qcp (q t) (k t))/(1-Qao (QaL (N t))
      (Qan (N t)) (q t) (Qcp (q t) (k t)))))^(k t)) ≤ 1/2:=by
    have ht:0 ≤ 2*Z1 (-((QaL (N t)*Qan (N t):ℕ):ℝ)*(q t)^4/64)+
      Z1 (-(Qbu (q t) (N t):ℝ)*(QaV (q t))^4/16):=by positivity
    unfold QdY Qdi at he'
    linarith only [he',ht]
  have HH:=Qjh hg.K_pos hg.m_large hg.K_le_m (by norm_num:0<3000)
    off hi (Qqf _ hm) (Qqg _ _ hm)
    (QcN (q t) (N t)) 300 (k t) hk1 (hq t) hg.seed hg.count
    hanchor.1 hanchor.2.1 hanchor.2.2.1 hanchor.2.2.2 hg.smoothing_margin
    (rfl:Qcp (q t) (k t)=_) hρ hc
    (Real.rpow_nonneg hNt.le _) hcap.1
  refine ⟨hg,he,?_⟩
  simpa only [QbX,dif_pos hm,QbH,QdY,off] using HH
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open Filter
open scoped Topology Classical
end TraceReconstruction
end
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
open scoped ENNReal
noncomputable section
open Filter
open scoped Topology
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β:Type*} [Fintype α] [Fintype β]
theorem Qjl (P Q:FiniteLaw α) (K:α→FiniteLaw β)
    (R S:FiniteLaw β) {E V:ℝ} (hH:P.Qbw Q ≤ V)
    (hR:R.tv (P.bind K) ≤ E) (hS:S.tv (Q.bind K) ≤ E) (m:ℕ) :
    (R.product m).tv (S.product m) ≤ Z0 ((m:ℝ)*V)+2*m*E:=by
  have hmid:=(QqX ((P.bind K).product m) ((Q.bind K).product m)).trans
    (Z24 ((QlX _ _ m).trans
      (mul_le_mul_of_nonneg_left ((QlV P Q K).trans hH) (Z19 m))))
  have hr:=(Qja R (P.bind K) m).trans (mul_le_mul_of_nonneg_left hR (Z19 m))
  have hs:=(Qja S (Q.bind K) m).trans (mul_le_mul_of_nonneg_left hS (Z19 m))
  rw [tv_symm (S.product m)] at hs
  linarith only [hr,hs,hmid,Qjc (R.product m) ((P.bind K).product m) (S.product m),
    Qjc ((P.bind K).product m) ((Q.bind K).product m) (S.product m)]
end FiniteLaw
def QcW (n:ℕ) (w:List Bool):BoundedTrace n :=
  if h:w∈traceSpace n then ⟨w,h⟩ else ⟨[],QdM [] (by simp)⟩
theorem Qgn {n:ℕ} {w:List Bool} (hw:w.length ≤ n) :
    (QcW n w).val=w:=by
  simp only [QcW,dif_pos (QdM w hw)]
theorem Qhz (q:ℝ) (hq:q∈Z6 0 1) (w:List Bool)
    (n:ℕ) (hw:w.length≤n) (f:BoundedTrace n→ℝ) :
    (listTraceLaw q hq w n hw).expect f=
      Qay q w (fun z=>f (QcW n z)):=by
  rw [←Qeq q hq w n hw]
  congr 1
  funext t
  congr 1
  apply Subtype.ext
  exact (Qgn (Qhv t.property)).symm
theorem Qbk.Qin {α:Type*} [Fintype α] {q E:ℝ}
    {P:FiniteLaw α} {decode:α→List Bool} {w:List Bool}
    (H:Qbk q P decode w E) (hq:q∈Z6 0 1)
    (n:ℕ) (hw:w.length≤n) :
    (listTraceLaw q hq w n hw).tv (P.map (fun a=>QcW n (decode a))) ≤ E:=by
  apply FiniteLaw.QiZ
  intro f hf
  rw [Qhz,FiniteLaw.expect_map]
  simp only [Function.comp_def]
  have hh:=H (fun z=>f (QcW n z)) (fun z=>hf _)
  linarith only [(abs_le.mp hh).1]
theorem QeG.sample_tv {q E V:ℝ} {x y:List Bool}
    (C:QeG q x y E V) (hq:q∈Z6 0 1)
    (m n:ℕ) (hx:x.length≤n) (hy:y.length≤n) :
    ((listTraceLaw q hq x n hx).product m).tv ((listTraceLaw q hq y n hy).product m) ≤
      Z0 ((m:ℝ)*V)+2*m*E:=by
  let:=C.finiteOutcome
  exact FiniteLaw.Qjl C.first C.second
    (fun a=>FiniteLaw.pure (QcW n (C.decode a))) _ _ C.bound
    (C.first_simulation.Qin hq n hx) (C.second_simulation.Qin hq n hy) m
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
end TraceReconstruction
noncomputable section
namespace TraceReconstruction
open scoped Classical
def wordOfLength {n:ℕ} (w:List Bool) (h:w.length=n):Word n:=h ▸ w.get
theorem Qfr {n:ℕ} (w:List Bool) (h:w.length=n) :
    Z20 (wordOfLength w h)=w:=by
  subst n
  exact List.ofFn_get w
theorem QmZ {n:ℕ} (q:ℝ) (hq:q∈Z6 0 1) (x:Word n) :
    listTraceLaw q hq (Z20 x) n (by simp)=completeTraceLaw q hq x:=by
  apply FiniteLaw.ext_expect
  intro f
  rw [Qhz,Qhy,QkD,FiniteLaw.expect_map]
  unfold FiniteLaw.expect maskLaw
  apply Z2 rfl
  intro a _
  congr 2
  apply Subtype.ext
  exact Qgn (QeA x a)
theorem QhA {n:ℕ} (q:ℝ) (hq:q∈Z6 0 1)
    (w:List Bool) (hw:w.length=n) :
    listTraceLaw q hq w n hw.le=completeTraceLaw q hq (wordOfLength w hw):=by
  have hh:=QmZ q hq (wordOfLength w hw)
  simpa only [Qfr] using hh
end TraceReconstruction
end
end
end
end
end OAI
namespace OAI.TraceReconstruction
open Filter
open scoped Topology Classical
noncomputable section
theorem fixedInitialProduct:∀ᶠ n:ℕ in atTop,∃ x y:Word n,x ≠ y ∧ ∀ m:ℕ,
    ((completeTraceLaw (1/2) (by constructor <;> norm_num) x).product m).tv
    ((completeTraceLaw (1/2) (by constructor <;> norm_num) y).product m) ≤
    Z0 ((m:ℝ)*(n:ℝ)^(-11/5:ℝ)) + 2*m*(n:ℝ)^(-100:ℝ):=by
  let N:ℕ → ℝ:=fun n => n
  let q:ℕ → ℝ:=fun _ => 1/2
  let k:ℕ → ℕ:=fun _ => 10^6
  have hN:Tendsto N atTop atTop:=tendsto_natCast_atTop_atTop
  have hq (t):q t ∈ Z12 0 (1/2:ℝ):=by constructor <;> norm_num [q]
  have hqc:(1/2:ℝ) ∈ Z6 0 1:=by constructor <;> norm_num
  have hor:=Qqj (A:=fun _=>1) (k:=k) hN hN
    (Eventually.of_forall fun _=>le_rfl) hq
    ((Real.tendsto_log_atTop.comp hN).const_div_atTop ((1/2:ℝ)^(-3:ℤ)))
    (PowerRate.const hN (by norm_num [k]:0 < (k 0:ℝ)))
    (Eventually.of_forall fun _=>by norm_num [k])
    (Eventually.of_forall fun _=>by norm_num [k])
  filter_upwards [hor] with n hn
  obtain ⟨G,hE,⟨C⟩⟩:=hn
  let u:=QbX (q n) (N n) (-1)
  let v:=QbX (q n) (N n) 1
  have hm:4 ≤ Qan (N n):=(by norm_num:4 ≤ 128).trans G.m_large
  have hu:=QiL (q:=q n) hm (-1)
  have hv:=QiL (q:=q n) hm 1
  have huv:u.length = v.length:=hu.trans hv.symm
  have hlen:u.length ≤ n:=by
    apply Nat.cast_le (α:=ℝ) |>.mp
    change ((QbX (q n) (N n) (-1)).length:ℝ) ≤ N n
    rw [hu,Z35]; exact G.length_upper
  let tail:=List.replicate (n-u.length) false
  have hx:(u++tail).length = n:=by simp only [tail,List.length_append,List.length_replicate]; omega
  have hy:(v++tail).length = n:=by simp only [tail,List.length_append,List.length_replicate]; omega
  refine ⟨wordOfLength _ hx,wordOfLength _ hy,?_,?_⟩
  · intro e
    have h:=congrArg Z20 e
    rw [Qfr,Qfr] at h
    exact Qqh G (List.append_cancel_right h)
  · intro m
    have H:=((C.pad hqc [] tail).hellinger (by norm_num [k])).sample_tv hqc m n
      (by simpa only [List.nil_append] using hx.le) (by simpa only [List.nil_append] using hy.le)
    change ((listTraceLaw (1/2) hqc (u++tail) n hx.le).product m).tv
      ((listTraceLaw (1/2) hqc (v++tail) n hy.le).product m) ≤ _ at H
    rw [QhA _ _ _ hx,QhA _ _ _ hy] at H
    apply H.trans (add_le_add le_rfl _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [mul_one] using hE
end

end OAI.TraceReconstruction
namespace ChasePort
open Finset Filter Real
open scoped Classical
private lemma joint {α β:Type} [Fintype α] [Fintype β] [DecidableEq β] (m:ℕ)
    (f:α→β) (T:Finset (Fin m→β)) :
    ((univ.filter (fun a:Fin m→α => (fun j => f (a j))∈T)).card:ℝ)/Fintype.card (Fin m→α) =
    ∑ w∈T,∏ j,(((univ.filter (fun a => f a=w j)).card:ℝ)/Fintype.card α) := by
  classical
  have ff (w:Fin m→β) : univ.filter (fun a:Fin m→α => (fun j => f (a j))=w) =
      Fintype.piFinset (fun j => univ.filter (fun a => f a=w j)) := by
    ext a; simp [funext_iff]
  have h := sum_card_fiberwise_eq_card_filter (univ:Finset (Fin m→α)) T (fun a j => f (a j))
  simp_rw [ff,Fintype.card_piFinset] at h
  rw [←h,Nat.cast_sum,Finset.sum_div]
  apply sum_congr rfl
  intro w _
  rw [Nat.cast_prod,Finset.prod_div_distrib]
  simp

open OAI.TraceReconstruction
private def masks (n : ℕ) : Finset (Fin n) ≃ Mask n where
  toFun S i := decide (i ∈ S)
  invFun a := univ.filter (fun i => a i = true)
  left_inv S := by ext i; simp
  right_inv a := by funext i; simp

private lemma mass {n} (x : Word n) (w : Trace) : traceMass (1/2) x w =
    ((univ.filter (fun S => Green92.trace x S = w)).card:ℝ)/Fintype.card (Finset (Fin n)) := by
  classical
  unfold traceMass
  rw [← Equiv.sum_comp (masks n)]
  have wt (S : Finset (Fin n)) : maskWeight (1/2) (masks n S) = 1 / (2:ℝ)^n := by
    unfold maskWeight
    norm_num [show (1:ℝ)-1/2=1/2 by norm_num, div_pow]
  simp_rw [wt]
  change (∑ S : Finset (Fin n), if Green92.trace x S = w then 1 / (2:ℝ)^n else 0) = _
  rw [← Finset.sum_filter]; simp [div_eq_mul_inv]

private lemma separated {n} (x y : Word n) (m : ℕ) (D : (Fin m → Trace) → Prop)
    (a : (9/10:ℝ) ≤ ((univ.filter fun S : Fin m → Finset (Fin n) => D (fun j => Green92.trace x (S j))).card : ℝ) / Fintype.card (Fin m → Finset (Fin n)))
    (b : (9/10:ℝ) ≤ ((univ.filter fun S : Fin m → Finset (Fin n) => ¬ D (fun j => Green92.trace y (S j))).card : ℝ) / Fintype.card (Fin m → Finset (Fin n))) :
    2/5 ≤ ((completeTraceLaw (1/2) (by constructor <;> norm_num) x).product m).tv ((completeTraceLaw (1/2) (by constructor <;> norm_num) y).product m) := by
  classical
  let f (z : Word n) (S : Finset (Fin n)) : BoundedTrace n := ⟨Green92.trace z S,by
    apply QdM; simp only [Green92.trace,List.length_map]; exact (List.length_filter_le ..).trans (by simp)⟩
  let event := univ.filter (fun w : Fin m → BoundedTrace n => D (fun j => (w j).val))
  let P (z : Word n) := (completeTraceLaw (1/2) (by constructor <;> norm_num) z).product m
  have J (z : Word n) (T : Finset (Fin m → BoundedTrace n)) :
      ((univ.filter (fun S : Fin m → Finset (Fin n) => (fun j => f z (S j)) ∈ T)).card : ℝ) / Fintype.card (Fin m → Finset (Fin n)) = ∑ w∈T,(P z).mass w := by
    rw [joint]; apply sum_congr rfl; intro w _; apply prod_congr rfl; intro j _
    change _ = traceMass _ z _
    rw [mass]; congr 3; ext S; simp [f,Subtype.ext_iff]
  have A : 9/10 ≤ ∑ w∈event,(P x).mass w := by rw [← J]; simpa [event,f] using a
  have B : 9/10 ≤ ∑ w∈eventᶜ,(P y).mass w := by rw [← J]; simpa [event,f] using b
  have total := sum_add_sum_compl event (P y).mass
  rw [(P y).total] at total
  let d w := (P x).mass w - (P y).mass w
  have bd : ∑ w∈event,d w ≤ ∑ w,|d w| := (sum_le_sum (fun w _ => le_abs_self (d w))).trans
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => abs_nonneg _)
  simp only [d,sum_sub_distrib] at bd
  change _ ≤ (1/2:ℝ) * ∑ w,|(P x).mass w - (P y).mass w|
  linarith only [A,B,total,bd]

theorem bridge : OMA.R_Green92_green_92_variants_chase_lower_R1.H1 := by
  classical
  refine ⟨1/16,by norm_num,?_⟩
  filter_upwards [fixedInitialProduct, eventually_ge_atTop 4] with n pair hn
  intro _
  obtain ⟨x,y,ne,h⟩ := pair
  refine ⟨x,y,ne,?_⟩
  intro m D a b
  have tv := (separated x y m D a b).trans (h m)
  have n1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have log1 : 1 ≤ log (n:ℝ) := by
    apply (le_log_iff_exp_le (by positivity : 0<(n:ℝ))).mpr
    have : (4:ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  apply le_trans (div_le_self (by positivity) (one_le_pow₀ (n:=7) log1))
  by_contra! lt
  have rate (s:ℝ) (hs:s ≤ -(3/2:ℝ)) : (m:ℝ)*(n:ℝ)^s ≤ 1/16 := by
    calc _ ≤ ((1/16:ℝ)*(n:ℝ)^(3/2:ℝ))*(n:ℝ)^s := mul_le_mul_of_nonneg_right lt.le (by positivity)
         _ = (1/16:ℝ)*(n:ℝ)^(3/2+s) := by rw [mul_assoc,← Real.rpow_add (by positivity : 0<(n:ℝ))]
         _ ≤ (1/16:ℝ)* (n:ℝ)^(0:ℝ) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith)) (by norm_num)
         _ = _ := by simp
  have sq : sqrt ((m:ℝ)*(n:ℝ)^(-11/5:ℝ)) ≤ 1/4 := (sqrt_le_iff).mpr ⟨by norm_num,by convert rate _ (by norm_num : (-11/5:ℝ) ≤ -(3/2:ℝ)) using 1 <;> norm_num⟩
  nlinarith only [sq,tv,rate (-100) (by norm_num)]
end ChasePort

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1.H1 := ChasePort.bridge
