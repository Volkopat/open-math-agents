import OMAStatements.S_oeis_a047800

/-! The Landau–Ramanujan proof and its analytic dependencies are adapted from
facebookresearch/atlas-lean, revision bb1037a201f548338e370c8c65ad77d82d91d596.
Modified for Lean 4.33.1 and combined with the lattice counting argument.
https://github.com/facebookresearch/atlas-lean/tree/bb1037a201f548338e370c8c65ad77d82d91d596
-/

/-
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

/- Grid -/
section
/-! A reduction of the square-grid limit to the Landau--Ramanujan asymptotic
and the density-one existence of representatives in fixed sectors about the diagonal. -/

namespace SquareGrid

open Filter Topology Real
open OMA.S_oeis_a047800

/-- Represented natural numbers through a real cutoff, including zero. -/
noncomputable def represented (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊x⌋₊ + 1)).filter fun m => ∃ i j : ℕ, m = i^2 + j^2

/-- A representation in the sector where both squared coordinates are at most m/c. -/
noncomputable def sector (x c : ℝ) : Finset ℕ := by
  classical
  exact (represented x).filter fun m =>
    ∃ i j : ℕ, m = i^2 + j^2 ∧ c * (i:ℝ)^2 ≤ m ∧ c * (j:ℝ)^2 ≤ m

private abbrev grid (n : ℕ) : Finset ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image fun p => p.1 ^ 2 + p.2 ^ 2)

theorem upper_count (n : ℕ) : a n ≤ (represented (2 * (n:ℝ)^2)).card := by
  apply Finset.card_le_card (s := grid n)
  intro m hm
  obtain ⟨⟨i,j⟩, hij, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_)), i,j,rfl⟩
  push_cast
  have hi₂ : (i:ℝ)^2 ≤ (n:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hi' 2
  have hj₂ : (j:ℝ)^2 ≤ (n:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left hj' 2
  change (i:ℝ)^2 + (j:ℝ)^2 ≤ _
  linarith

theorem lower_count (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (sector (c * (n:ℝ)^2) c).card ≤ a n := by
  classical
  apply Finset.card_le_card (t := grid n)
  intro m hm
  obtain ⟨hr, i, j, heq, hi, hj⟩ := Finset.mem_filter.mp hm
  have hmle : (m:ℝ) ≤ c*(n:ℝ)^2 := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ c*(n:ℝ)^2)).mp
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
  have bound (k : ℕ) (hk : c*(k:ℝ)^2 ≤ m) : k ≤ n := by
    have hs : (k:ℝ)^2 ≤ (n:ℝ)^2 := (mul_le_mul_iff_right₀ hc).mp (hk.trans hmle)
    by_contra! h
    have h' : (n:ℝ) < k := by exact_mod_cast h
    nlinarith [sq_nonneg ((k:ℝ)-n), Nat.cast_nonneg (α:=ℝ) n]
  exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (bound i hi)),
     Finset.mem_range.mpr (Nat.lt_succ_of_le (bound j hj))⟩, heq.symm⟩

noncomputable abbrev scale (n : ℕ) : ℝ := (n:ℝ)^2 / √(log n)

private theorem cutoff_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c * (n:ℝ)^2) atTop atTop := by
  exact (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    |>.const_mul_atTop hc

/-- Rescale the real-variable Landau asymptotic to cutoffs c n². -/
theorem rescale {F : ℝ → ℝ} {K c : ℝ} (hc : 0 < c)
    (hF : Tendsto (fun x : ℝ => F x / (x / √(log x))) atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => F (c * (n:ℝ)^2) / scale n) atTop (𝓝 (K*c/√2)) := by
  have logN : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => log (c*(n:ℝ)^2) / log (n:ℝ)) atTop (𝓝 2) := by
    have h0 : Tendsto (fun n : ℕ => log c / log (n:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logN
    have h2 := h0.add (tendsto_const_nhds (x:=(2:ℝ)))
    rw [zero_add] at h2
    apply h2.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have h1 : 1 < (n:ℝ) := by exact_mod_cast hn
    have hn' : (n:ℝ) ≠ 0 := by linarith
    rw [Real.log_mul hc.ne' (pow_ne_zero 2 hn'), Real.log_pow]
    have hl := Real.log_pos h1
    field_simp
    norm_num
  have hmain := hF.comp (cutoff_tendsto hc)
  have hfac := ((hlog.sqrt).inv₀ (by positivity : (√2:ℝ) ≠ 0)).const_mul c
  have hp := hmain.mul hfac
  convert hp.congr' ?_ using 1
  · simp [div_eq_mul_inv, mul_assoc]
  filter_upwards [eventually_gt_atTop 1,
    (cutoff_tendsto hc).eventually (eventually_gt_atTop (1:ℝ))] with n hn hx
  change 1 < c*(n:ℝ)^2 at hx
  have h1 : 1 < (n:ℝ) := by exact_mod_cast hn
  have hln := Real.log_pos h1
  have hlx := Real.log_pos hx
  change (F (c*(n:ℝ)^2) / (c*(n:ℝ)^2 / √(log (c*(n:ℝ)^2)))) *
    (c * (√(log (c*(n:ℝ)^2)/log (n:ℝ)))⁻¹) = F (c*(n:ℝ)^2) / _
  rw [Real.sqrt_div hlx.le]
  simp [scale,div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hc.ne',
        ne_of_gt (Real.sqrt_pos.2 hlx)]

/-- The two analytic number-theory inputs suffice for the precise leading constant. -/
theorem limit_of_scaled_inputs {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K))
    (angular : ∀ c : ℝ, 0 < c → c < 2 →
      Tendsto (fun n : ℕ => ((sector (c*(n:ℝ)^2) c).card : ℝ) / (represented (c*(n:ℝ)^2)).card)
        atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (a n : ℝ) / scale n) atTop (𝓝 (K*2/√2)) := by
  have scaled (c : ℝ) (hc : 0 < c) := rescale hc landau
  have sector_scaled (c : ℝ) (hc : 0 < c) (hc2 : c < 2) :
      Tendsto (fun n : ℕ => ((sector (c*(n:ℝ)^2) c).card:ℝ) / scale n)
        atTop (𝓝 (K*c/√2)) := by
    have hg := (angular c hc hc2).mul (scaled c hc)
    rw [one_mul] at hg
    apply hg.congr
    intro n
    have hnz : (0:ℝ) < (represented (c*(n:ℝ)^2)).card := by
      have hm : 0 ∈ represented (c*(n:ℝ)^2) := by
        unfold represented
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), 0,0,by norm_num⟩
      exact_mod_cast Finset.card_pos.mpr ⟨0,hm⟩
    change _ / _ * (_ / _) = _ / _
    field_simp
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hd : 0 < K/√2 := by positivity
    have hlt : max 0 (b/(K/√2)) < 2 := by
      apply max_lt (by norm_num)
      apply (div_lt_iff₀ hd).mpr
      calc b < K*2/√2 := hb
           _ = 2*(K/√2) := by ring
    obtain ⟨c,hc,hc2⟩ := exists_between hlt
    have hc0 := (le_max_left 0 (b/(K/√2))).trans_lt hc
    have hb' : b < K*c/√2 := by
      have := (div_lt_iff₀ hd).mp ((le_max_right 0 (b/(K/√2))).trans_lt hc)
      calc b < c*(K/√2) := this
           _ = K*c/√2 := by ring
    filter_upwards [(tendsto_order.mp (sector_scaled c hc0 hc2)).1 b hb'] with n hn
    exact hn.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast lower_count n hc0)
      (by positivity : 0 ≤ scale n))
  · intro b hb
    filter_upwards [(tendsto_order.mp (scaled 2 (by norm_num))).2 b hb] with n hn
    exact (div_le_div_of_nonneg_right (by exact_mod_cast upper_count n)
      (by positivity : 0 ≤ scale n)).trans_lt hn

/-- The two analytic number-theory inputs suffice for the precise leading constant. -/
theorem limit_of_classical_inputs {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K))
    (angular : ∀ c : ℝ, 0 < c → c < 2 →
      Tendsto (fun x : ℝ => ((sector x c).card : ℝ) / (represented x).card)
        atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (a n : ℝ) / scale n) atTop (𝓝 (K*2/√2)) := by
  apply limit_of_scaled_inputs hK landau
  exact fun c hc hc2 => (angular c hc hc2).comp (cutoff_tendsto hc)
/-- Conditional form of the exact competition declaration. -/
theorem target_of_classical_inputs {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K))
    (angular : ∀ c : ℝ, 0 < c → c < 2 →
      Tendsto (fun x : ℝ => ((sector x c).card : ℝ) / (represented x).card)
        atTop (𝓝 1)) : type_of% @OMA.S_oeis_a047800.main := by
  exact ⟨_, by positivity, limit_of_classical_inputs hK landau angular⟩

end SquareGrid
end

/- GridSieve -/
section
/-! Divisibility among sums of two squares. Once the Landau asymptotic holds,
every fixed representable divisor has relative density 1/d among the
represented integers. Finite divisor weights follow by linearity. -/
namespace SquareGrid
open Filter Topology Real

abbrev TwoSquares (m : ℕ) := ∃ i j : ℕ, m = i^2 + j^2

theorem twoSquares_iff_inert_even (m : ℕ) :
    TwoSquares m ↔ ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (m.factorization p) := by
  rw [TwoSquares, Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp h3
    by_cases hpm : p ∣ m
    · obtain rfl | hm := m.eq_zero_or_pos
      · simp
      rw [Nat.factorization_def m hp]
      exact h p (Nat.mem_primeFactors.mpr ⟨hp,hpm,hm.ne'⟩) h3
    · simp [Nat.factorization_eq_zero_of_not_dvd hpm]
  · intro h p hp h3
    have hprime := Nat.prime_of_mem_primeFactors hp
    simpa [Nat.factorization_def m hprime] using h p hprime h3

theorem twoSquares_mul_iff {d : ℕ} (hd : 0 < d) (hrep : TwoSquares d) (m : ℕ) :
    TwoSquares (d*m) ↔ TwoSquares m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  rw [twoSquares_iff_inert_even] at hrep ⊢
  rw [twoSquares_iff_inert_even]
  simp only [Nat.factorization_mul hd.ne' hm.ne', Finsupp.add_apply, Nat.even_add]
  constructor
  · intro h p hp hp3
    exact (h p hp hp3).mp (hrep p hp hp3)
  · intro h p hp hp3
    exact iff_of_true (hrep p hp hp3) (h p hp hp3)

/-- Integers represented below x and divisible by d. -/
noncomputable def multiples (x : ℝ) (d : ℕ) : Finset ℕ :=
  (represented x).filter fun m => d ∣ m

private theorem mem_represented {x : ℝ} (hx : 0 ≤ x) {m : ℕ} :
    m ∈ represented x ↔ (m:ℝ) ≤ x ∧ TwoSquares m := by
  classical
  unfold represented
  simp [Nat.le_floor_iff hx, TwoSquares]

theorem multiples_eq_image {d : ℕ} (hd : 0 < d) (hrep : TwoSquares d)
    {x : ℝ} (hx : 0 ≤ x) :
    multiples x d = (represented (x/d)).image (fun r => d*r) := by
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  ext m
  rw [multiples, Finset.mem_filter, mem_represented hx, Finset.mem_image]
  constructor
  · rintro ⟨⟨hm,hr⟩,t,rfl⟩
    refine ⟨t,(mem_represented (div_nonneg hx hd'.le)).mpr ⟨?_,(twoSquares_mul_iff hd hrep t).mp hr⟩,rfl⟩
    apply (le_div_iff₀ hd').mpr
    simpa [mul_comm] using hm
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨ht,hr⟩ := (mem_represented (div_nonneg hx hd'.le)).mp ht
    exact ⟨⟨by simpa [mul_comm] using (le_div_iff₀ hd').mp ht,
        (twoSquares_mul_iff hd hrep t).mpr hr⟩, dvd_mul_right d t⟩
 
theorem count_multiples {d : ℕ} (hd : 0 < d) (hrep : TwoSquares d)
    {x : ℝ} (hx : 0 ≤ x) :
    (multiples x d).card = (represented (x/d)).card := by
  rw [multiples_eq_image hd hrep hx, Finset.card_image_of_injective]
  exact fun i j h => mul_left_cancel₀ hd.ne' h

theorem multiples_density {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K)) {c : ℝ} (hc : 0 < c) {d : ℕ} (hd : 0 < d) (hrep : TwoSquares d) :
    Tendsto (fun n : ℕ => ((multiples (c*(n:ℝ)^2) d).card:ℝ) /
        (represented (c*(n:ℝ)^2)).card) atTop (𝓝 (1/(d:ℝ))) := by
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hnum := rescale (div_pos hc hd') landau
  have hden := rescale hc landau
  have h := hnum.div hden (by positivity)
  have he : (K*(c/d)/√2) / (K*c/√2) = 1/d := by field_simp
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn' : 1 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 < scale n := div_pos (by positivity) (Real.sqrt_pos.mpr (Real.log_pos hn'))
  rw [count_multiples hd hrep (by positivity)]
  rw [show c*(n:ℝ)^2/(d:ℝ) = c/(d:ℝ)*(n:ℝ)^2 by ring]
  simp [div_div_div_cancel_right₀ hs.ne']

/-- A finite linear combination of divisibility indicators has the expected limiting mean.
The weights may have either sign, so this also applies to inclusion-exclusion. -/
theorem finite_divisor_mean {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K)) {c : ℝ} (hc : 0 < c) (D : Finset ℕ) (w : ℕ → ℝ)
    (hs : ∀ d ∈ D, 0 < d ∧ TwoSquares d) :
    Tendsto (fun n : ℕ =>
      (∑ m ∈ represented (c*(n:ℝ)^2), ∑ d ∈ D, if d ∣ m then w d else 0) /
      (represented (c*(n:ℝ)^2)).card) atTop (𝓝 (∑ d ∈ D, w d / d)) := by
  classical
  have h := tendsto_finsetSum D (fun d hd => (multiples_density hK landau hc
    (hs d hd).1 (hs d hd).2).const_mul (w d))
  simp only [mul_one_div] at h
  apply h.congr
  intro n
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp [multiples, div_eq_mul_inv, mul_comm, mul_left_comm]

end SquareGrid
end

/- GridLocalFactors -/
section
namespace SquareGrid
open Filter Topology Real

/-- The factor contributed by a prime occurring exactly once. -/
noncomputable def localWeight (p m : ℕ) (w : ℝ) : ℝ :=
  if p ∣ m ∧ ¬ p^2 ∣ m then w else 1

noncomputable def sieveWeight (P : Finset ℕ) (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ p ∈ P, localWeight p m (w p)

noncomputable def sieveSum (P : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ m ∈ represented x, sieveWeight P w m

private theorem sum_multiples {d : ℕ} (hd : 0 < d) (hr : TwoSquares d) {x : ℝ}
    (hx : 0 ≤ x) (f : ℕ → ℝ) (hf : ∀ m, f (d*m) = f m) :
    (∑ m ∈ represented x, if d ∣ m then f m else 0) = ∑ m ∈ represented (x/d), f m := by
  rw [← Finset.sum_filter]
  change (∑ m ∈ multiples x d, f m) = _
  rw [multiples_eq_image hd hr hx, Finset.sum_image]
  · simp [hf]
  · exact fun i _ j _ h => mul_left_cancel₀ hd.ne' h

private theorem weight_mul_invariant {d : ℕ} {P : Finset ℕ} (w : ℕ → ℝ)
    (hcop : ∀ q ∈ P, q.Coprime d) (m : ℕ) :
    sieveWeight P w (d*m) = sieveWeight P w m := by
  apply Finset.prod_congr rfl
  intro q hq
  have h := hcop q hq
  simp only [localWeight, h.dvd_mul_left, (h.pow_left 2).dvd_mul_left]

private theorem sieve_step {p : ℕ} {P : Finset ℕ} (w : ℕ → ℝ) (hp : p ∉ P)
    (hP : 0 < p) (hr : TwoSquares p) (hc : ∀ q ∈ P, q.Coprime p) {x : ℝ} (hx : 0 ≤ x) :
    sieveSum (insert p P) w x = sieveSum P w x -
      (1-w p) * (sieveSum P w (x/p) - sieveSum P w (x/(p:ℝ)^2)) := by
  have hr2 : TwoSquares (p^2) := ⟨p,0,by simp⟩
  have h1 := sum_multiples hP hr hx (sieveWeight P w) (weight_mul_invariant w hc)
  have h2 := sum_multiples (pow_pos hP 2) hr2 hx (sieveWeight P w)
    (weight_mul_invariant w (fun q hq => (hc q hq).pow_right 2))
  push_cast at h2
  unfold sieveSum
  rw [← h1, ← h2, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  simp only [sieveWeight, Finset.prod_insert hp]
  by_cases h : p ∣ m
  · by_cases h' : p^2 ∣ m <;> simp [localWeight, h, h'] <;> ring
  · have h' : ¬p^2 ∣ m := fun hm => h (dvd_trans (by simp [sq] : p ∣ p^2) hm)
    simp [localWeight, h, h']

/-- Each prime has its exact-first-power density 1/p − 1/p². The finite family
is asymptotically independent inside the represented integers. -/
theorem finite_prime_local_factors {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K)) (P : Finset ℕ) (w : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ TwoSquares p) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => sieveSum P w (c*(n:ℝ)^2) / (represented (c*(n:ℝ)^2)).card)
      atTop (𝓝 (∏ p ∈ P, (1-(1-w p)*((1:ℝ)/p-1/(p:ℝ)^2)))) := by
  have hsum (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ TwoSquares p) :
      ∀ a : ℝ, 0 < a → Tendsto (fun n : ℕ => sieveSum T w (a*(n:ℝ)^2) / scale n)
        atTop (𝓝 ((K*a/√2) * ∏ p ∈ T, (1-(1-w p)*((1:ℝ)/p-1/(p:ℝ)^2)))) := by
    induction T using Finset.induction_on with
    | empty =>
      intro a ha
      simpa [sieveSum,sieveWeight] using rescale ha landau
    | @insert p T hp ih =>
      intro a ha
      obtain ⟨hpp,hpr⟩ := hT p (Finset.mem_insert_self ..)
      have hp' : 0 < (p:ℝ) := by exact_mod_cast hpp.pos
      have hT' := fun q hq => hT q (Finset.mem_insert_of_mem hq)
      have hc' : ∀ q ∈ T, q.Coprime p := by
        intro q hq
        exact (Nat.coprime_primes (hT' q hq).1 hpp).mpr (fun h => hp (h ▸ hq))
      have hsub := (ih hT' (a/p) (by positivity)).sub
        (ih hT' (a/(p:ℝ)^2) (by positivity))
      have h := (ih hT' a ha).sub (hsub.const_mul (1-w p))
      rw [Finset.prod_insert hp]
      convert h.congr ?_ using 1
      · ring
      intro n
      rw [sieve_step w hp hpp.pos hpr hc' (by positivity)]
      rw [show a*(n:ℝ)^2/p = a/p*(n:ℝ)^2 by ring,
        show a*(n:ℝ)^2/(p:ℝ)^2 = a/(p:ℝ)^2*(n:ℝ)^2 by ring]
      ring
  have h := (hsum P hP c hc).div (rescale hc landau) (by positivity)
  rw [mul_div_cancel_left₀ _ (by positivity : K*c/√2 ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn' : 1 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 < scale n := div_pos (by positivity) (Real.sqrt_pos.mpr (Real.log_pos hn'))
  exact div_div_div_cancel_right₀ hs.ne' _ _

end SquareGrid
end

/- GridDensity -/
section
/-! A fixed finite family of Fourier majorants converts the pointwise cost of
a missed sector into a bound for the relative count of its exceptional set. -/
namespace SquareGrid
open Filter Topology Real

noncomputable def primeFactorMean (P : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∏ p ∈ P, (1-(1-w p)*((1:ℝ)/p-1/(p:ℝ)^2))

private theorem sieveWeight_nonneg (P : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ p, 0 ≤ w p) (m : ℕ) :
    0 ≤ sieveWeight P w m := by
  apply Finset.prod_nonneg
  intro p _
  unfold localWeight
  split
  · exact hw p
  · norm_num

/-- A small limiting Euler product for each of finitely many harmonics forces
the exceptional set to have relative density zero. -/
theorem scaled_sector_density {K c D : ℝ} (hK : 0 < K) (hc : 0 < c) (hD : 0 < D)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K)) (H : Finset ℕ) (w : ℕ → ℕ → ℝ) (hw : ∀ h p, 0 ≤ w h p)
    (allow : ℕ → Prop) (hrep : ∀ p, allow p → p.Prime ∧ TwoSquares p)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ P : Finset ℕ, (∀ p ∈ P, allow p) ∧
      (∑ h ∈ H, primeFactorMean P (w h)) < ε)
    (hmiss : ∀ (x : ℝ) (m : ℕ), m ∈ represented x → m ∉ sector x c →
      ∀ P : Finset ℕ, (∀ p ∈ P, allow p) → 1 ≤ D * ∑ h ∈ H, sieveWeight P (w h) m) :
    Tendsto (fun n : ℕ => ((sector (c*(n:ℝ)^2) c).card:ℝ) /
      (represented (c*(n:ℝ)^2)).card) atTop (𝓝 1) := by
  classical
  have hsub (x : ℝ) : sector x c ⊆ represented x := Finset.filter_subset _ _
  have hcard (x : ℝ) : (0:ℝ) < (represented x).card := by
    have hz : 0 ∈ represented x := by
      unfold represented
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),0,0,by norm_num⟩
    exact_mod_cast Finset.card_pos.mpr ⟨0,hz⟩
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨P,hP,hε⟩ := hsmall ((1-b)/D) (div_pos (sub_pos.mpr hb) hD)
    have hv := (tendsto_finsetSum H (fun h _ => finite_prime_local_factors hK landau P (w h)
      (fun p hp => hrep p (hP p hp)) hc)).const_mul D
    have hlim : D * (∑ h ∈ H, primeFactorMean P (w h)) < 1-b := by
      simpa [mul_comm] using (lt_div_iff₀ hD).mp hε
    filter_upwards [(tendsto_order.mp hv).2 (1-b) hlim] with n hn
    let x := c*(n:ℝ)^2
    change D * (∑ h ∈ H, sieveSum P (w h) x / (represented x).card) < 1-b at hn
    change b < ((sector x c).card:ℝ) / (represented x).card
    rw [← Finset.sum_div, ← mul_div_assoc] at hn
    have hge : (((represented x).card:ℝ)-(sector x c).card) ≤ D * ∑ h ∈ H, sieveSum P (w h) x := by
      let bad := represented x \ sector x c
      have hbcard : ((bad.card:ℝ)) = ((represented x).card:ℝ) - (sector x c).card := by
        rw [show bad.card = (represented x).card - (sector x c).card from Finset.card_sdiff_of_subset (hsub x)]
        exact Nat.cast_sub (Finset.card_le_card <| hsub x)
      rw [← hbcard]
      calc
        _ = ∑ _m ∈ bad, (1:ℝ) := by simp
        _ ≤ ∑ m ∈ bad, D * ∑ h ∈ H, sieveWeight P (w h) m := by
          apply Finset.sum_le_sum
          intro m hm
          exact hmiss x m (Finset.mem_sdiff.mp hm).1 (Finset.mem_sdiff.mp hm).2 P hP
        _ ≤ ∑ m ∈ represented x, D * ∑ h ∈ H, sieveWeight P (w h) m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          intro m _ _
          exact mul_nonneg hD.le (Finset.sum_nonneg fun h _ => sieveWeight_nonneg P (hw h) m)
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]; rfl
    apply (lt_div_iff₀ (hcard x)).mpr
    have := (div_lt_iff₀ (hcard x)).mp hn
    linarith
  · intro b hb
    filter_upwards with n
    refine lt_of_le_of_lt ?_ hb
    apply div_le_one_of_le₀ _ (by positivity)
    exact_mod_cast Finset.card_le_card (hsub _)

end SquareGrid
end

/- Angles -/
section
/-! From angular discrepancy of Gaussian representations to density-one sector hits. -/
namespace SquareGrid

open Filter Topology Real

/-- Signed lattice representatives, including all four quadrants and both axes. -/
noncomputable def circlePoints (m : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(m:ℤ)) m) ×ˢ (Finset.Icc (-(m:ℤ)) m)).filter
    (fun z => m = z.1.natAbs^2 + z.2.natAbs^2)

private def latticeComplex (p : ℤ × ℤ) : ℂ := ⟨p.1,p.2⟩

/-- Lattice points whose principal arguments belong to the open interval (l,u). -/
noncomputable def arcPoints (m : ℕ) (l u : ℝ) := by
  classical
  exact (circlePoints m).filter fun z => (latticeComplex z).arg ∈ Set.Ioo l u

/-- Error of the normalized angular counting measure on one arc. -/
noncomputable def arcError (m : ℕ) (l u : ℝ) : ℝ :=
  |((arcPoints m l u).card:ℝ) / (circlePoints m).card - (u-l)/(2*π)|

theorem mem_circlePoints_iff {m : ℕ} {p : ℤ × ℤ} :
    p ∈ circlePoints m ↔ m = p.1.natAbs^2 + p.2.natAbs^2 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hm
    have h1 : p.1.natAbs ≤ m := hm ▸ (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans (Nat.le_add_right _ _)
    have h2 : p.2.natAbs ≤ m := hm ▸ (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans (Nat.le_add_left _ _)
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hm⟩
    all_goals
      apply Finset.mem_Icc.mpr
      apply abs_le.mp
      rw [← Int.natCast_natAbs]
      first | exact_mod_cast h1 | exact_mod_cast h2

private theorem diagonalArc {c : ℝ} (hc : c < 2) :
    ∃ l u : ℝ, -π ≤ l ∧ u ≤ π ∧ l < u ∧
      ∀ θ ∈ Set.Ioo l u, c*(cos θ)^2 < 1 ∧ c*(sin θ)^2 < 1 := by
  have hc' : c * (cos (π/4))^2 < 1 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    linarith
  have hs' : c * (sin (π/4))^2 < 1 := by simpa [Real.sin_pi_div_four, Real.cos_pi_div_four] using hc'
  have hs : ∀ᶠ θ in 𝓝 (π/4), c*(cos θ)^2 < 1 ∧ c*(sin θ)^2 < 1 :=
    (ContinuousAt.eventually_lt (f := fun θ => c*(cos θ)^2) (g := fun _ => (1:ℝ))
      (by fun_prop) continuousAt_const hc').and
    (ContinuousAt.eventually_lt (f := fun θ => c*(sin θ)^2) (g := fun _ => (1:ℝ))
      (by fun_prop) continuousAt_const hs')
  obtain ⟨l,u,⟨hl,hu⟩, hin⟩ := hs.exists_Ioo_subset
  refine ⟨max l (-π), min u π, le_max_right _ _, min_le_right _ _, ?_, ?_⟩
  · exact (max_lt hl (by linarith [pi_pos])).trans (lt_min hu (by linarith [pi_pos]))
  · intro θ hθ
    exact hin ⟨(le_max_left _ _).trans_lt hθ.1, hθ.2.trans_le (min_le_left _ _)⟩

private theorem sector_of_arc {x c l u : ℝ} {m : ℕ}
    (hr : m ∈ represented x)
    (harc : ∀ θ ∈ Set.Ioo l u, c*(cos θ)^2 < 1 ∧ c*(sin θ)^2 < 1)
    (hit : (arcPoints m l u).Nonempty) : m ∈ sector x c := by
  classical
  obtain ⟨p,hp⟩ := hit
  obtain ⟨hp, hθ⟩ := Finset.mem_filter.mp hp
  have hm := mem_circlePoints_iff.mp hp
  obtain ⟨hcos,hsin⟩ := harc _ hθ
  let z := latticeComplex p
  have h_i : (p.1.natAbs:ℝ)^2 = z.re^2 := by simp [z, latticeComplex, Nat.cast_natAbs]
  have h_j : (p.2.natAbs:ℝ)^2 = z.im^2 := by simp [z, latticeComplex, Nat.cast_natAbs]
  have hnorm : (m:ℝ) = ‖z‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq, ← h_i, ← h_j]
    exact_mod_cast hm
  refine Finset.mem_filter.mpr ⟨hr, p.1.natAbs, p.2.natAbs, hm, ?_, ?_⟩
  · rw [h_i, hnorm, ← Complex.norm_mul_cos_arg z, mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hcos.le (sq_nonneg ‖z‖)]
  · rw [h_j, hnorm, ← Complex.norm_mul_sin_arg z, mul_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hsin.le (sq_nonneg ‖z‖)]

/-- A normalized angular discrepancy majorant whose mean over represented integers tends
to zero implies the density-one sector hypothesis used by the grid sandwich. -/
theorem angular_of_mean_discrepancy (D : ℕ → ℝ)
    (dom : ∀ m l u, -π ≤ l → u ≤ π → l < u → arcError m l u ≤ D m)
    (hD : Tendsto (fun x : ℝ => (∑ m ∈ represented x, D m) / (represented x).card)
      atTop (𝓝 0)) (c : ℝ) (_hc : 0 < c) (hc2 : c < 2) :
    Tendsto (fun x : ℝ => ((sector x c).card:ℝ) / (represented x).card) atTop (𝓝 1) := by
  classical
  obtain ⟨l,u,hl,hu,hlu,harc⟩ := diagonalArc hc2
  let d := (u-l)/(2*π)
  have hd : 0 < d := div_pos (sub_pos.mpr hlu) (by positivity)
  have Dpos (m : ℕ) : 0 ≤ D m := (abs_nonneg _).trans (dom m l u hl hu hlu)
  have hU (x : ℝ) : (sector x c) ⊆ represented x := Finset.filter_subset _ _
  have hR (x : ℝ) : (0:ℝ) < (represented x).card := by
    have h0 : 0 ∈ represented x :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), 0,0,by norm_num⟩
    exact_mod_cast Finset.card_pos.mpr ⟨0,h0⟩
  have hcount (x : ℝ) :
      ((represented x \ sector x c).card:ℝ) * d ≤ ∑ m ∈ represented x, D m := by
    calc
      _ = ∑ _m ∈ represented x \ sector x c, d := by simp
      _ ≤ ∑ m ∈ represented x \ sector x c, D m := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hm
        have he : arcPoints m l u = ∅ := Finset.not_nonempty_iff_eq_empty.mp
          (fun h => hn (sector_of_arc hr harc h))
        have herr := dom m l u hl hu hlu
        simpa [arcError, he, d, abs_of_pos hd] using herr
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun m _ _ => Dpos m)
  have hh : Tendsto (fun x : ℝ => ((represented x \ sector x c).card:ℝ) / (represented x).card)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => by positivity) (g := fun x : ℝ =>
      ((∑ m ∈ represented x, D m) / (represented x).card) / d)
    · intro x
      apply (le_div_iff₀ hd).mpr
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (hcount x) (hR x).le
    · simpa using hD.div_const d
  have ht := (tendsto_const_nhds (x:=(1:ℝ))).sub hh
  rw [sub_zero] at ht
  apply ht.congr
  intro x
  have hc : ((represented x \ sector x c).card:ℝ) + (sector x c).card = (represented x).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (hU x)
  change 1 - _ / _ = _ / _
  field_simp [(hR x).ne']
  linarith

/-- The normalized discrepancy of the signed lattice-point angles. -/
noncomputable def angularDiscrepancy (m : ℕ) : ℝ :=
  sSup {e | ∃ l u : ℝ, -π ≤ l ∧ u ≤ π ∧ l < u ∧ e = arcError m l u}

private theorem arcError_le_one (m : ℕ) {l u : ℝ}
    (hl : -π ≤ l) (hu : u ≤ π) (hlu : l < u) : arcError m l u ≤ 1 := by
  classical
  let p : ℝ := ((arcPoints m l u).card:ℝ) / (circlePoints m).card
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hsub : arcPoints m l u ⊆ circlePoints m := Finset.filter_subset _ _
  have hp1 : p ≤ 1 := by
    exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
  have hd0 := div_nonneg (sub_nonneg.mpr hlu.le) (by positivity : (0:ℝ) ≤ 2*π)
  have hd1 : (u-l)/(2*π) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  change |p - _| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem arcError_le_discrepancy (m : ℕ) (l u : ℝ) (hl : -π ≤ l) (hu : u ≤ π)
    (hlu : l < u) : arcError m l u ≤ angularDiscrepancy m := by
  apply le_csSup (a := arcError m l u) (s := {e | ∃ l u : ℝ,
    -π ≤ l ∧ u ≤ π ∧ l < u ∧ e = arcError m l u})
  · refine ⟨1, ?_⟩
    rintro _ ⟨a,b,ha,hb,hab,rfl⟩
    exact arcError_le_one m ha hb hab
  · exact ⟨l,u,hl,hu,hlu,rfl⟩

/-- The exceptional sets in the qualitative Erdős–Hall angular equidistribution
input, with relative density measured inside the sums of two squares. -/
noncomputable def exceptional (x ε : ℝ) : Finset ℕ := by
  classical
  exact (represented x).filter fun m => ε ≤ angularDiscrepancy m

/-- Convergence of normalized angular discrepancy to zero in relative density
is sufficient. A rate and an estimate of the mean discrepancy are unnecessary. -/
theorem angular_of_discrepancy_in_density
    (hdensity : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun x : ℝ => ((exceptional x ε).card:ℝ) / (represented x).card) atTop (𝓝 0))
    (c : ℝ) (_hc : 0 < c) (hc2 : c < 2) :
    Tendsto (fun x : ℝ => ((sector x c).card:ℝ) / (represented x).card) atTop (𝓝 1) := by
  classical
  obtain ⟨l,u,hl,hu,hlu,harc⟩ := diagonalArc hc2
  let d := (u-l)/(2*π)
  have hd : 0 < d := div_pos (sub_pos.mpr hlu) (by positivity)
  have hU (x : ℝ) : sector x c ⊆ represented x := Finset.filter_subset _ _
  have hR (x : ℝ) : (0:ℝ) < (represented x).card := by
    have h0 : 0 ∈ represented x :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), 0,0,by norm_num⟩
    exact_mod_cast Finset.card_pos.mpr ⟨0,h0⟩
  have hbad (x : ℝ) : represented x \ sector x c ⊆ exceptional x d := by
    intro m hm
    obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hm
    have he : arcPoints m l u = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (fun h => hn (sector_of_arc hr harc h))
    refine Finset.mem_filter.mpr ⟨hr,?_⟩
    have h := arcError_le_discrepancy m l u hl hu hlu
    simpa [arcError, he, d, abs_of_pos hd] using h
  have hh : Tendsto (fun x : ℝ => ((represented x \ sector x c).card:ℝ) / (represented x).card)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity) (fun x => div_le_div_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (hbad x)) (hR x).le) (hdensity d hd)
  have ht := (tendsto_const_nhds (x:=(1:ℝ))).sub hh
  rw [sub_zero] at ht
  apply ht.congr
  intro x
  have hc : ((represented x \ sector x c).card:ℝ) + (sector x c).card = (represented x).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (hU x)
  change 1 - _ / _ = _ / _
  field_simp [(hR x).ne']
  linarith

end SquareGrid
end

/- AnglesFactors -/
section
/-! Independent conjugations of Gaussian factors give a family of lattice points on one
circle. The norm of each angular Fourier coefficient of its uniform sign distribution
is a product of absolute cosines. -/
namespace SquareGrid

open Complex
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι]

private def signedFactor (s : Bool) (z : GaussianInt) : GaussianInt := if s then z else star z

/-- The lattice point determined by a family of conjugation choices. -/
def candidate (base : GaussianInt) (factors : ι → GaussianInt) (s : ι → Bool) : GaussianInt :=
  base * ∏ i, signedFactor (s i) (factors i)

private def squareRadius : GaussianInt →* ℕ :=
  Int.natAbsHom.toMonoidHom.comp Zsqrtd.normMonoidHom

@[simp] private theorem squareRadius_signed (z : GaussianInt) (s : Bool) :
    squareRadius (signedFactor s z) = squareRadius z := by
  cases s
  · change (star z).norm.natAbs = z.norm.natAbs
    rw [Zsqrtd.norm_conj]
  · rfl

theorem candidate_mem_circlePoints (base : GaussianInt) (factors : ι → GaussianInt) (s : ι → Bool) :
    ((candidate base factors s).re, (candidate base factors s).im) ∈
      circlePoints (base.norm.natAbs * ∏ i, (factors i).norm.natAbs) := by
  rw [mem_circlePoints_iff]
  have h : squareRadius (candidate base factors s) = squareRadius base * ∏ i, squareRadius (factors i) := by
    simp [candidate, map_prod]
  rw [← show (candidate base factors s).norm.natAbs =
      base.norm.natAbs * ∏ i, (factors i).norm.natAbs from h]
  simpa [sq] using GaussianInt.natAbs_norm_eq (candidate base factors s)

/-- The kth angular harmonic, extended multiplicatively at zero. -/
noncomputable def harmonic (k : ℕ) : GaussianInt →* ℂ where
  toFun z := ((z:ℂ) / (‖(z:ℂ)‖:ℂ))^k
  map_one' := by simp [GaussianInt.toComplex_one]
  map_mul' := by
    intro a b
    rw [GaussianInt.toComplex_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_pow]

theorem harmonic_star (k : ℕ) (z : GaussianInt) :
    harmonic k (star z) = conj (harmonic k z) := by
  simp [harmonic, GaussianInt.toComplex_star]

theorem harmonic_norm (k : ℕ) {z : GaussianInt} (hz : z ≠ 0) : ‖harmonic k z‖ = 1 := by
  have hz' : (z:ℂ) ≠ 0 := by simpa using hz
  simp [harmonic, norm_pow, norm_ne_zero_iff.mpr hz']

theorem harmonic_re (k : ℕ) {z : GaussianInt} (hz : z ≠ 0) :
    (harmonic k z).re = Real.cos ((k:ℝ)*(z:ℂ).arg) := by
  have hz' : (z:ℂ) ≠ 0 := by simpa using hz
  have hphase : (z:ℂ) / (‖(z:ℂ)‖:ℂ) = Complex.exp ((z:ℂ).arg * I) := by
    exact (div_eq_iff (by exact_mod_cast norm_ne_zero_iff.mpr hz')).mpr
      ((mul_comm _ _).trans (Complex.norm_mul_exp_arg_mul_I (z:ℂ))).symm
  change (((z:ℂ) / (‖(z:ℂ)‖:ℂ))^k).re = _
  rw [hphase, ← Complex.exp_nat_mul]
  rw [show (k:ℂ) * ((z:ℂ).arg * I) = (((k:ℝ)*(z:ℂ).arg:ℝ):ℂ)*I by push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

variable [DecidableEq ι]

/-- Averaging over signs factors the angular character without a uniqueness assumption on
the family of representations. -/
theorem candidate_mean (k : ℕ) (base : GaussianInt) (factors : ι → GaussianInt) :
    (∑ s : ι → Bool, harmonic k (candidate base factors s)) / (2:ℂ)^(Fintype.card ι) =
      harmonic k base * ∏ i, ((harmonic k (factors i)).re : ℂ) := by
  classical
  let f (i : ι) (s : Bool) := harmonic k (signedFactor s (factors i))
  have hs (i : ι) : (∑ b : Bool, f i b) = 2 * ((harmonic k (factors i)).re : ℂ) := by
    rw [Fintype.sum_bool]
    simp [f, signedFactor, harmonic_star, Complex.add_conj]
  simp only [candidate, map_mul, map_prod]
  rw [← Finset.mul_sum]
  change harmonic k base * (∑ s : ι → Bool, ∏ i, f i (s i)) / _ = _
  rw [← Fintype.prod_sum, ← Finset.prod_congr rfl (fun i _ => (hs i).symm)]
  simp [Finset.prod_mul_distrib]
  field_simp

/-- The exact norm of the kth angular Fourier coefficient on this candidate family. -/
theorem candidate_fourier_norm (k : ℕ) {base : GaussianInt} (hb : base ≠ 0)
    (factors : ι → GaussianInt) (hf : ∀ i, factors i ≠ 0) :
    ‖(∑ s : ι → Bool, harmonic k (candidate base factors s)) / (2:ℂ)^(Fintype.card ι)‖ =
      ∏ i, |Real.cos ((k:ℝ)*(factors i:ℂ).arg)| := by
  rw [candidate_mean, norm_mul, harmonic_norm k hb, one_mul, Complex.norm_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs, harmonic_re k (hf i)]

/-- The phase with the diagonal mapped to 1, as used in a finite Fourier hitting test. -/
noncomputable def diagonalPhase (v : GaussianInt) : ℂ := -harmonic 4 v

theorem diagonalPhase_fourier_norm (h : ℕ) {base : GaussianInt} (hb : base ≠ 0)
    (factors : ι → GaussianInt) (hf : ∀ i, factors i ≠ 0) :
    ‖(∑ s : ι → Bool, (diagonalPhase (candidate base factors s))^h) / (2:ℂ)^(Fintype.card ι)‖ =
      ∏ i, |Real.cos (((4*h:ℕ):ℝ)*(factors i:ℂ).arg)| := by
  have hm (v : GaussianInt) : (diagonalPhase v)^h = (-1:ℂ)^h * harmonic (4*h) v := by
    rw [diagonalPhase, ← neg_one_mul (harmonic 4 v), mul_pow]
    congr 1
    exact (pow_mul _ 4 h).symm
  simp_rw [hm]
  rw [← Finset.mul_sum, mul_div_assoc, norm_mul, candidate_fourier_norm _ hb factors hf]
  simp

end SquareGrid
end

/- GridPhase -/
section
namespace SquareGrid
open Complex
open scoped ComplexConjugate

theorem diagonalPhase_dist {v : GaussianInt} {m : ℕ} (hm : 0 < m)
    (hv : v.norm.natAbs = m) :
    ‖1-diagonalPhase v‖ = 2 * |(v.re:ℝ)^2 - (v.im:ℝ)^2| / m := by
  let u := (v:ℂ) / (‖(v:ℂ)‖ : ℂ)
  let w := u^2
  have hn : ‖(v:ℂ)‖^2 = (m:ℝ) := by
    rw [Complex.sq_norm, ← GaussianInt.intCast_real_norm, ← GaussianInt.natCast_natAbs_norm, hv]
  have hv0 : ‖(v:ℂ)‖ ≠ 0 := fun e ↦ by simp [e] at hn; exact hm.ne' (by exact_mod_cast hn.symm)
  have hu : ‖u‖ = 1 := by simp [u,Complex.norm_real,hv0]
  have hw : ‖w‖ = 1 := by simp [w,hu]
  have hwc : w * conj w = 1 := by rw [Complex.mul_conj',hw]; norm_num
  have hphase : 1-diagonalPhase v = w * (w+conj w) := by
    calc
      1-diagonalPhase v = w*w+1 := by dsimp [diagonalPhase,harmonic,w,u]; ring
      _ = _ := by rw [mul_add,hwc]
  rw [hphase,norm_mul,hw,one_mul,Complex.add_conj,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  have hwre : w.re = ((v.re:ℝ)^2 - (v.im:ℝ)^2)/m := by
    change (u^2).re = _
    rw [sq,Complex.mul_re]
    simp only [u,Complex.div_ofReal_re,Complex.div_ofReal_im,← GaussianInt.intCast_re,
      ← GaussianInt.intCast_im,← hn]
    ring
  rw [hwre,abs_div]
  simp [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) m), mul_div_assoc]

/-- The radius of the accepted phase arc is explicit for each cutoff below the diagonal. -/
theorem mem_sector_of_diagonalPhase {c x : ℝ} (hc : 0 < c) (_hc2 : c < 2)
    {m : ℕ} (hm : 0 < m) (hmx : (m:ℝ) ≤ x) {v : GaussianInt} (hv : v.norm.natAbs = m)
    (hphase : ‖1-diagonalPhase v‖ < 2*(2-c)/c) : m ∈ sector x c := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hsum : m = v.re.natAbs^2 + v.im.natAbs^2 := by
    rw [←hv,GaussianInt.natAbs_norm_eq]; ring
  have hsum' : (m:ℝ) = (v.re.natAbs:ℝ)^2 + (v.im.natAbs:ℝ)^2 := by exact_mod_cast hsum
  have abssq (k : ℤ) : (k.natAbs : ℝ)^2 = (k:ℝ)^2 := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  rw [diagonalPhase_dist hm hv,←abssq,←abssq] at hphase
  have hlt := (div_lt_div_iff₀ hm' hc).mp hphase
  have h1 := le_abs_self ((v.re.natAbs:ℝ)^2-(v.im.natAbs:ℝ)^2)
  have h2 := neg_le_abs ((v.re.natAbs:ℝ)^2-(v.im.natAbs:ℝ)^2)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le <| Nat.le_floor hmx), _,_,hsum⟩,
    _,_,hsum, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h1 hc.le, congrArg (c*·) hsum']
  · nlinarith [mul_le_mul_of_nonneg_left h2 hc.le, congrArg (c*·) hsum']

end SquareGrid
end

/- GridFejer -/
section
/-! Quantitative arc detection for a finite sample of phases on the unit circle.
The proof uses the squared modulus of the geometric sum, the Fejér kernel. -/
namespace SquareGrid
open scoped ComplexConjugate
open Complex

noncomputable def phaseMoment {ι : Type*} [Fintype ι] (z : ι → ℂ) (h : ℕ) : ℂ :=
  (∑ s, z s ^ h) / (Fintype.card ι : ℂ)

private theorem cross_re {z : ℂ} (hz : ‖z‖ = 1) {a b : ℕ} (hab : b ≤ a) :
    (z^a * conj (z^b)).re = (z^(a-b)).re := by
  rw [show a = (a-b)+b by omega, pow_add, mul_assoc, Complex.mul_conj', norm_pow, hz]
  simp

/-- Off a δ-neighborhood of 1, the squared modulus of a geometric sum is
bounded independently of its length. -/
private theorem geometric_cap {z : ℂ} (hz : ‖z‖ = 1) {δ : ℝ} (hd : 0 < δ)
    (hfar : δ ≤ ‖1-z‖) (N : ℕ) :
    ‖∑ i ∈ Finset.range N, z^i‖^2 ≤ (2/δ)^2 := by
  have hgeom := congrArg norm (geom_sum_mul z N)
  rw [norm_mul] at hgeom
  have hle : ‖z^N - 1‖ ≤ 2 := calc
    _ ≤ ‖z^N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz]; simp; norm_num
  have ha : ‖∑ i ∈ Finset.range N, z^i‖ ≤ 2/δ := by
    apply (le_div_iff₀ hd).mpr
    calc
      _ ≤ ‖∑ i ∈ Finset.range N, z^i‖ * ‖z-1‖ := by
        gcongr
        simpa [norm_sub_rev] using hfar
      _ = _ := hgeom
      _ ≤ _ := hle
  gcongr

/-- If every sample misses the ball of radius δ about 1, its first N−1
nonzero Fourier moments cannot all be small. -/
theorem finite_arc_detection {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℂ)
    (hz : ∀ s, ‖z s‖ = 1) (N : ℕ) {B δ : ℝ} (hd : 0 < δ) (hB : 0 ≤ B)
    (hfar : ∀ s, δ ≤ ‖1-z s‖)
    (hmom : ∀ h : ℕ, 0 < h → h < N → ‖phaseMoment z h‖ ≤ B) :
    (N:ℝ) ≤ (2/δ)^2 + (N:ℝ)^2*B := by
  classical
  let S := Finset.range N
  let C : ℝ := Fintype.card ι
  have hC : 0 < C := by
    change 0 < (Fintype.card ι:ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  let T (a b : ℕ) : ℝ := ∑ s, ((z s)^a * conj ((z s)^b)).re
  have symmT (a b : ℕ) : T a b = T b a := by
    apply Finset.sum_congr rfl
    intro s _
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have diag (a : ℕ) : T a a = C := by
    unfold T
    simp only [fun s => cross_re (hz s) (le_refl a), Nat.sub_self, pow_zero, Complex.one_re]
    simp [C]
  have off {a b : ℕ} (ha : a < N) (hab : b < a) : -(C*B) ≤ T a b := by
    have h := hmom (a-b) (by omega) (by omega)
    rw [phaseMoment,norm_div] at h
    have normC : ‖(Fintype.card ι:ℂ)‖ = C := by simp [C]
    rw [normC] at h
    have hu := (div_le_iff₀ hC).mp h
    have hl := (abs_le.mp (Complex.abs_re_le_norm (∑ s, z s^(a-b)))).1
    simp only [Complex.re_sum] at hl
    simp only [T, fun s => cross_re (hz s) hab.le]
    linarith
  have ht {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) :
      (if b=a then C else 0) - C*B ≤ T a b := by
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    rcases lt_trichotomy b a with h|h|h
    · simpa [h.ne] using off ha' h
    · simp [h,diag, mul_nonneg hC.le hB]
    · rw [symmT]; simpa [h.ne'] using off hb' h
  have low : (N:ℝ)*C-(N:ℝ)^2*(C*B) ≤ ∑ a ∈ S, ∑ b ∈ S, T a b := by
    calc
      _ = ∑ a ∈ S, ∑ b ∈ S, ((if b=a then C else 0) - C*B) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul]
        simp [S, Finset.sum_ite, Finset.filter_true_of_mem]; ring
      _ ≤ _ := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ht ha hb
  have high : (∑ a ∈ S, ∑ b ∈ S, T a b) ≤ C*(2/δ)^2 := by
    calc
      _ = ∑ s, ‖∑ a ∈ S, z s^a‖^2 := by
        unfold T
        calc
          _ = ∑ a ∈ S, ∑ s, ∑ b ∈ S, ((z s)^a * conj ((z s)^b)).re :=
            Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
          _ = ∑ s, ∑ a ∈ S, ∑ b ∈ S, ((z s)^a * conj ((z s)^b)).re := Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro s _
            simp only [← Complex.re_sum, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
            rw [Complex.mul_conj']
            rw [← Complex.ofReal_pow, Complex.ofReal_re]
      _ ≤ ∑ _s : ι, (2/δ)^2 := Finset.sum_le_sum fun s _ => geometric_cap (hz s) hd (hfar s) N
      _ = _ := by simp [C]
  have h := low.trans high
  apply (mul_le_mul_iff_right₀ hC).mp
  nlinarith only [h]

end SquareGrid
end

/- AnglesDivisors -/
section
/-! Realization of the finite sieve weights as Fourier norms of measures supported
on representations of one fixed positive integer. -/
namespace SquareGrid

private theorem represented_gaussian (m : ℕ) :
    TwoSquares m ↔ ∃ z : GaussianInt, z.norm.natAbs = m := by
  constructor
  · rintro ⟨i,j,rfl⟩
    refine ⟨⟨i,j⟩, ?_⟩
    simp [GaussianInt.natAbs_norm_eq, sq]
  · rintro ⟨z,rfl⟩
    exact ⟨z.re.natAbs,z.im.natAbs, by simp [GaussianInt.natAbs_norm_eq,sq]⟩

theorem sieve_candidate_family (P : Finset ℕ) (f : ℕ → GaussianInt)
    (hp : ∀ p ∈ P, p.Prime ∧ (f p).norm.natAbs = p) {m : ℕ} (hm : m ≠ 0) (hs : TwoSquares m) :
    ∃ v : (↥P → Bool) → GaussianInt,
      (∀ s, (v s).norm.natAbs = m ∧ v s ≠ 0) ∧
      ∀ h : ℕ, ‖(∑ s, (diagonalPhase (v s))^h) / (2:ℂ)^P.card‖ =
        sieveWeight P (fun p => |Real.cos (((4*h:ℕ):ℝ)*(f p:ℂ).arg)|) m := by
  classical
  let active (p : ℕ) := p ∣ m ∧ ¬ p^2 ∣ m
  let fac (p : ℕ) : GaussianInt := if active p then f p else 1
  let rad := ∏ p : P, (fac p).norm.natAbs
  have hnorm (p : ℕ) (h : p ∈ P) : (fac p).norm.natAbs = if active p then p else 1 := by
    by_cases h' : active p <;> simp [fac, h', (hp p h).2, Zsqrtd.norm_one]
  have hf (p : P) : fac p ≠ 0 := by
    intro h
    have hz := hnorm p p.prop
    rw [h] at hz
    by_cases ha : active (p:ℕ) <;> simp [ha, Zsqrtd.norm_zero] at hz
    exact (hp p p.prop).1.ne_zero hz.symm
  have hrad : rad = ∏ p ∈ P.filter active, p := by
    dsimp only [rad]
    simp_rw [fun p : P => hnorm p p.prop]
    rw [Finset.prod_coe_sort P (fun p : ℕ => if active p then p else 1), Finset.prod_filter]
  have hdiv : rad ∣ m := by
    rw [hrad]
    exact Finset.prod_primes_dvd m (fun p hp' => (hp p (Finset.mem_filter.mp hp').1).1.prime)
      (fun _ hp' => (Finset.mem_filter.mp hp').2.1)
  have hradRep : TwoSquares rad := by
    apply (represented_gaussian _).mpr
    refine ⟨∏ p : P, fac p, ?_⟩
    exact map_prod (Int.natAbsHom.toMonoidHom.comp
      (Zsqrtd.normMonoidHom : GaussianInt →* ℤ)) _ _
  obtain ⟨b,hmb⟩ := hdiv
  have hr0 : rad ≠ 0 := fun hr => hm (by simp [hmb, hr])
  have hb : TwoSquares b := (twoSquares_mul_iff hr0.bot_lt hradRep _).mp (hmb ▸ hs)
  obtain ⟨base,hbase⟩ := (represented_gaussian _).mp hb
  have hb0 : base ≠ 0 := by
    rintro rfl
    simp [Zsqrtd.norm_zero] at hbase
    exact hm (by simp [hmb, ← hbase])
  refine ⟨candidate base (fun p : P => fac p), ?_, ?_⟩
  · intro s
    have hc := mem_circlePoints_iff.mp (candidate_mem_circlePoints base (fun p : P => fac p) s)
    have hn : (candidate base (fun p : P => fac p) s).norm.natAbs = m := by
      rw [GaussianInt.natAbs_norm_eq, ← sq, ← sq, ← hc, hbase, hmb]
      exact mul_comm _ _
    exact ⟨hn, fun hz => hm (by simpa [hz, Zsqrtd.norm_zero] using hn.symm)⟩
  · intro h
    rw [← Fintype.card_coe, diagonalPhase_fourier_norm h hb0 (fun p : P => fac p) hf]
    rw [Finset.prod_coe_sort P (fun p => |Real.cos (((4*h:ℕ):ℝ)*(fac p:ℂ).arg)|)]
    apply Finset.prod_congr rfl
    intro p _
    by_cases h' : active p
    · simp [fac, h', localWeight, show p ∣ m ∧ ¬p^2 ∣ m from h']
    · simp [fac, h', localWeight, GaussianInt.toComplex_one, show ¬ (p ∣ m ∧ ¬p^2 ∣ m) from h']

end SquareGrid
end

/- GridPrimeReduction -/
section
/-! A reduction using finite divisibility statistics and Gaussian prime angles
in place of a density-one theorem about complete angular measures. -/
namespace SquareGrid
open Filter Topology Real

noncomputable def primeCosWeight (f : ℕ → GaussianInt) (h p : ℕ) : ℝ :=
  |Real.cos (((4*h:ℕ):ℝ)*(f p:ℂ).arg)|

/-- The remaining input on angles is a statement solely about split prime
representatives. The finite-prime estimate implies the full grid asymptotic. -/
theorem target_of_prime_products {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K)) (f : ℕ → GaussianInt)
    (small : ∀ H : Finset ℕ, (∀ h ∈ H, 0 < h) → ∀ ε : ℝ, 0 < ε →
      ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (f p).norm.natAbs = p) ∧
        (∑ h ∈ H, primeFactorMean P (primeCosWeight f h)) < ε) :
    type_of% @OMA.S_oeis_a047800.main := by
  classical
  refine ⟨K*2/√2, by positivity, limit_of_scaled_inputs hK landau ?_⟩
  intro c hc hc2
  let δ := 2*(2-c)/c
  have hd : 0 < δ := div_pos (mul_pos (by norm_num) (sub_pos.mpr hc2)) hc
  obtain ⟨N,hN⟩ := exists_nat_gt ((2/δ)^2)
  let H := Finset.Ico 1 N
  let D := (N:ℝ)^2 / ((N:ℝ)-(2/δ)^2)
  have hn0 : 0 < (N:ℝ) := (sq_nonneg _).trans_lt hN
  have hden : 0 < (N:ℝ)-(2/δ)^2 := sub_pos.mpr hN
  have hD : 0 < D := div_pos (sq_pos_of_pos hn0) hden
  apply scaled_sector_density hK hc hD landau H (primeCosWeight f) (fun _ _ => abs_nonneg _)
    (fun p => p.Prime ∧ (f p).norm.natAbs = p)
  · rintro p ⟨hp,hv⟩
    refine ⟨hp,(f p).re.natAbs,(f p).im.natAbs,?_⟩
    calc p = (f p).norm.natAbs := hv.symm
         _ = _ := by rw [GaussianInt.natAbs_norm_eq]; ring
  · exact small H (fun _ h => (Finset.mem_Ico.mp h).1)
  intro x m hm hmiss P hP
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hmiss
    exact Finset.mem_filter.mpr ⟨hm,0,0,by norm_num,by simp,by simp⟩
  obtain ⟨hle,hs⟩ := Finset.mem_filter.mp hm
  have hmx : (m:ℝ) ≤ x :=
    (Nat.le_floor_iff' hm0).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hle))
  obtain ⟨v,hv,hcoeff⟩ := sieve_candidate_family P f hP hm0 hs
  let z (s : ↥P → Bool) := diagonalPhase (v s)
  have hz : ∀ s, ‖z s‖ = 1 := by
    intro s
    have hz' : (v s : ℂ) ≠ 0 := by simpa using (hv s).2
    simp [z,diagonalPhase,harmonic,norm_pow,norm_ne_zero_iff.mpr hz']
  have hfar : ∀ s, δ ≤ ‖1-z s‖ := by
    intro s
    exact le_of_not_gt fun h => hmiss (mem_sector_of_diagonalPhase hc hc2
      (Nat.pos_of_ne_zero hm0) hmx (hv s).1 h)
  have hs0 (h : ℕ) : 0 ≤ sieveWeight P (primeCosWeight f h) m := by
    change 0 ≤ sieveWeight P (fun p => |Real.cos (((4*h:ℕ):ℝ)*(f p:ℂ).arg)|) m
    rw [← hcoeff]
    exact norm_nonneg _
  have h := finite_arc_detection z hz N hd (Finset.sum_nonneg (fun i _ => hs0 i)) hfar
    (B := ∑ h ∈ H, sieveWeight P (primeCosWeight f h) m) (by
      intro i hi hiN
      have hmom : ‖phaseMoment z i‖ = sieveWeight P (primeCosWeight f i) m := by
        change ‖phaseMoment z i‖ = sieveWeight P (fun p => |Real.cos (((4*i:ℕ):ℝ)*(f p:ℂ).arg)|) m
        simpa [phaseMoment,z,Fintype.card_fun] using hcoeff i
      rw [hmom]
      exact Finset.single_le_sum (fun i _ => hs0 i) (Finset.mem_Ico.mpr ⟨hi,hiN⟩))
  unfold D
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  linarith only [h]

end SquareGrid
end

/- GridPrimeDivergence -/
section
namespace SquareGrid
open Filter Topology Real

/-- The split primes for which the chosen Gaussian integer represents p. -/
def chosenPrimes (f : ℕ → GaussianInt) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun p => p.Prime ∧ (f p).norm.natAbs = p

noncomputable def angularPrimeSum (f : ℕ → GaussianInt) (h n : ℕ) : ℝ :=
  ∑ p ∈ chosenPrimes f n, (1-cos (((8*h:ℕ):ℝ)*(f p:ℂ).arg))/(p:ℝ)

private theorem local_factor_exp {p : ℝ} (hp : 2 ≤ p) (t : ℝ) :
    let g := 1 - (1-|cos t|)*(1/p-1/p^2)
    0 ≤ g ∧ g ≤ exp (-(1-cos (2*t))/(8*p)) := by
  dsimp only
  have hp0 : 0 < p := by linarith
  let u := 1/p
  let a := |cos t|
  have hu : 0 ≤ u := by positivity
  have ha : 0 ≤ a := abs_nonneg _
  have ha1 : a ≤ 1 := abs_le.mpr ⟨neg_one_le_cos t,cos_le_one t⟩
  have hu2 : u ≤ 1/2 := (div_le_div_iff₀ hp0 (by norm_num : (0:ℝ) < 2)).mpr (by linarith)
  have hv : 0 ≤ u-u^2 := by nlinarith [mul_nonneg hu (show 0 ≤ 1-u by linarith)]
  have hv1 : u-u^2 ≤ 1 := by nlinarith [sq_nonneg u]
  have hv2 : u/2 ≤ u-u^2 := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hu2)]
  have he : 1/p^2 = u^2 := by dsimp [u]; ring
  rw [he]
  change 0 ≤ 1-(1-a)*(u-u^2) ∧ 1-(1-a)*(u-u^2) ≤ _
  constructor
  · have := mul_le_mul (show 1-a ≤ 1 by linarith) hv1 hv (by norm_num : (0:ℝ) ≤ 1)
    linarith
  · have h2 : (1-cos (2*t))/(8*p) ≤ (1-a)*(u-u^2) := by
      calc
        _ = (1-a)*(1+a)*u/4 := by
          rw [cos_two_mul]
          have heq : a^2 = cos t ^ 2 := sq_abs _
          dsimp only [u]
          field_simp
          nlinarith
        _ ≤ (1-a)*(u/2) := by
          have h' := mul_le_mul_of_nonneg_left ha1 (mul_nonneg (sub_nonneg.mpr ha1) hu)
          nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hv2 (sub_nonneg.mpr ha1)
    calc
      1-(1-a)*(u-u^2) ≤ 1 + (-(1-cos (2*t))/(8*p)) := by rw [neg_div]; linarith
      _ ≤ _ := by linarith [Real.add_one_le_exp (-(1-cos (2*t))/(8*p))]

/-- Divergence of the positive reciprocal-prime angular sum suffices. -/
theorem target_of_prime_divergence {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K)) (f : ℕ → GaussianInt)
    (diverges : ∀ h : ℕ, 0 < h → Tendsto (angularPrimeSum f h) atTop atTop) :
    type_of% @OMA.S_oeis_a047800.main := by
  apply target_of_prime_products hK landau f
  intro H hH ε hε
  have single (h : ℕ) (hh : 0 < h) :
      Tendsto (fun n => primeFactorMean (chosenPrimes f n) (primeCosWeight f h)) atTop (𝓝 0) := by
    have upper := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp ((diverges h hh).const_mul_atTop (by norm_num : 0 < (1/8:ℝ))))
    apply squeeze_zero _ _ upper
    · intro n
      apply Finset.prod_nonneg
      intro p hp
      exact (local_factor_exp (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le)
        (((4*h:ℕ):ℝ)*(f p:ℂ).arg)).1
    · intro n
      unfold primeFactorMean
      change _ ≤ exp (-(1/8*angularPrimeSum f h n))
      rw [angularPrimeSum, Finset.mul_sum, ← Finset.sum_neg_distrib, exp_sum]
      apply Finset.prod_le_prod
      · intro p hp
        exact (local_factor_exp (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le)
          (((4*h:ℕ):ℝ)*(f p:ℂ).arg)).1
      · intro p hp
        have hl := (local_factor_exp (p := (p:ℝ))
          (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le) (((4*h:ℕ):ℝ)*(f p:ℂ).arg)).2
        have ha : ((8*h:ℕ):ℝ)*(f p:ℂ).arg = 2*(((4*h:ℕ):ℝ)*(f p:ℂ).arg) := by
          push_cast
          ring
        rw [ha]
        apply hl.trans_eq
        congr 1
        ring
  have hall := tendsto_finsetSum H (fun h hh => single h (hH h hh))
  simp only [Finset.sum_const_zero] at hall
  obtain ⟨n,hn⟩ := ((tendsto_order.mp hall).2 ε hε).exists
  exact ⟨chosenPrimes f n, fun _ hp => (Finset.mem_filter.mp hp).2,hn⟩

/-- A bound-independent finite set can be enlarged to every sufficiently late prime cutoff. -/
theorem angularPrimeSum_tendsto_of_unbounded (f : ℕ → GaussianInt) (h : ℕ)
    (unbounded : ∀ b : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (f p).norm.natAbs = p) ∧
      b < ∑ p ∈ P, (1-cos (((8*h:ℕ):ℝ)*(f p:ℂ).arg))/(p:ℝ)) :
    Tendsto (angularPrimeSum f h) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨P,hP,hb⟩ := unbounded b
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range P
  filter_upwards [eventually_ge_atTop N] with n hn
  apply hb.le.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun p hp => Finset.mem_filter.mpr ⟨Finset.range_mono hn (hN hp),hP p hp⟩
  · intro p _ _
    exact div_nonneg (sub_nonneg.mpr (cos_le_one _)) (Nat.cast_nonneg _)

/-- Cofinal unbounded finite sums of 1−|cos| suffice, with no prescribed sequence
of finite prime sets and no compatibility requirement between harmonics. -/
theorem target_of_finite_prime_sums {K : ℝ} (hK : 0 < K)
    (landau : Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x)))
      atTop (𝓝 K)) (f : ℕ → GaussianInt)
    (unbounded : ∀ h : ℕ, 0 < h → ∀ b : ℝ, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ (f p).norm.natAbs = p) ∧
      b < ∑ p ∈ P, (1-primeCosWeight f h p)/(p:ℝ)) :
    type_of% @OMA.S_oeis_a047800.main := by
  apply target_of_prime_divergence hK landau f
  intro h hh
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨P,hP,hb⟩ := unbounded h hh b
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range P
  filter_upwards [eventually_ge_atTop N] with n hn
  apply hb.le.trans
  apply le_trans (Finset.sum_le_sum (s:=P) (g:=fun p : ℕ =>
    (1-cos (((8*h:ℕ):ℝ)*(f p:ℂ).arg))/(p:ℝ)) ?_)
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact fun p hp => Finset.mem_filter.mpr ⟨Finset.range_mono hn (hN hp),hP p hp⟩
    · intro p _ _
      exact div_nonneg (sub_nonneg.mpr (cos_le_one _)) (Nat.cast_nonneg _)
  · intro p _
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    let t := ((4*h:ℕ):ℝ)*(f p:ℂ).arg
    have he : ((8*h:ℕ):ℝ)*(f p:ℂ).arg = 2*t := by dsimp [t]; push_cast; ring
    rw [he,cos_two_mul]
    change 1 - |cos t| ≤ _
    have ha : |cos t| ≤ 1 := abs_le.mpr ⟨neg_one_le_cos _,cos_le_one _⟩
    nlinarith [mul_nonneg (abs_nonneg (cos t)) (sub_nonneg.mpr ha),sq_abs (cos t)]

end SquareGrid
end

/- AnglesPrimes -/
section
/-! Prime factors in the Gaussian integers above rational primes. -/
namespace SquareGrid

open Complex
open scoped ComplexConjugate

private theorem split_exists {p : ℕ} (hp : p.Prime) (h4 : p % 4 ≠ 3) :
    ∃ z : GaussianInt, z.norm.natAbs = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,b,h⟩ := Nat.Prime.sq_add_sq h4
  exact ⟨⟨a,b⟩,by simpa [GaussianInt.natAbs_norm_eq,sq] using h⟩

/-- One Gaussian factor of each split or ramified rational prime. -/
noncomputable def splitFactor (p : ℕ) : GaussianInt := by
  classical
  exact if h : ∃ z : GaussianInt, z.norm.natAbs = p then h.choose else 1

theorem splitFactor_norm {p : ℕ} (hp : p.Prime) (h4 : p%4 ≠ 3) :
    (splitFactor p).norm.natAbs = p := by
  rw [splitFactor, dif_pos (split_exists hp h4)]
  exact (split_exists hp h4).choose_spec

private theorem gauss_irreducible_of_norm_prime {z : GaussianInt} (h : z.norm.natAbs.Prime) :
    Irreducible z := by
  rw [irreducible_iff]
  refine ⟨fun hu => h.ne_one (Zsqrtd.norm_eq_one_iff.mpr hu), ?_⟩
  intro a b hz
  have hn : z.norm.natAbs = a.norm.natAbs*b.norm.natAbs := by rw [hz,Zsqrtd.norm_mul,Int.natAbs_mul]
  simpa only [Nat.isUnit_iff, Zsqrtd.norm_eq_one_iff] using h.prime.irreducible.isUnit_or_isUnit hn

private theorem above_rational_prime {z : GaussianInt} (hz : Prime z) :
    ∃ p : ℕ, p.Prime ∧ z ∣ (p:GaussianInt) := by
  have aux (n : ℕ) : n ≠ 0 → z ∣ (n:GaussianInt) → ∃ p : ℕ, p.Prime ∧ z ∣ (p:GaussianInt) := by
    induction n using induction_on_primes with
    | zero => simp
    | one => exact fun _ h => False.elim (hz.not_isUnit (isUnit_of_dvd_one (by simpa using h)))
    | prime_mul p n hp ih =>
      intro hn h
      rw [Nat.cast_mul] at h
      exact (hz.dvd_or_dvd h).elim (fun H => ⟨p,hp,H⟩) (ih (right_ne_zero_of_mul hn))
  apply aux z.norm.natAbs
  · simpa using hz.ne_zero
  · rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _

/-- Above an inert prime there is one possible Gaussian prime class. Above a
split or ramified prime the two possible classes are interchanged by conjugation. -/
theorem gaussian_prime_cover {z : GaussianInt} (hz : Prime z) :
    (∃ p : ℕ, p.Prime ∧ p%4 = 3 ∧ Associated z (p:GaussianInt)) ∨
    (∃ p : ℕ, p.Prime ∧ p%4 ≠ 3 ∧
      (Associated z (splitFactor p) ∨ Associated z (star (splitFactor p)))) := by
  obtain ⟨p,hp,hd⟩ := above_rational_prime hz
  let _ : Fact p.Prime := ⟨hp⟩
  by_cases h4 : p%4 = 3
  · exact Or.inl ⟨p,hp,h4,hz.associated_of_dvd
      ((GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr h4) hd⟩
  · have hN := splitFactor_norm hp h4
    have hcast : (p:GaussianInt) = (splitFactor p) * star (splitFactor p) := by
      calc
        _ = ((splitFactor p).norm.natAbs:GaussianInt) := by rw [hN]
        _ = _ := by rw [GaussianInt.natCast_natAbs_norm,Zsqrtd.norm_eq_mul_conj]
    rw [hcast] at hd
    refine Or.inr ⟨p,hp,h4,(hz.dvd_or_dvd hd).imp ?_ ?_⟩
    · exact hz.irreducible.associated_of_dvd (gauss_irreducible_of_norm_prime (by rwa [hN]))
    · apply hz.irreducible.associated_of_dvd
      apply gauss_irreducible_of_norm_prime
      rwa [Zsqrtd.norm_conj, hN]

theorem gaussian_unit_four {z : GaussianInt} (h : IsUnit z) : z^4 = 1 := by
  rcases z with ⟨a,b⟩
  have he := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ) ≤ 0) ⟨a,b⟩).mpr h
  change a*a-(-1)*b*b=1 at he
  have h1 : -1 ≤ a := by nlinarith [sq_nonneg b]
  have h2 : a ≤ 1 := by nlinarith [sq_nonneg b]
  have h3 : -1 ≤ b := by nlinarith [sq_nonneg a]
  have h4 : b ≤ 1 := by nlinarith [sq_nonneg a]
  interval_cases a <;> interval_cases b <;> first | decide | norm_num at he

theorem harmonic_of_unit (k : ℕ) {z : GaussianInt} (h : IsUnit z) : harmonic (4*k) z = 1 := by
  have hpow : harmonic (4*k) z = (harmonic k z)^4 := by
    change ((z:ℂ) / (‖(z:ℂ)‖:ℂ))^(4*k) = (((z:ℂ) / (‖(z:ℂ)‖:ℂ))^k)^4
    rw [← pow_mul, Nat.mul_comm k 4]
  rw [hpow, ← map_pow, gaussian_unit_four h, map_one]

theorem harmonic_of_associated (k : ℕ) {z w : GaussianInt} (h : Associated z w) :
    harmonic (4*k) z = harmonic (4*k) w := by
  obtain ⟨u,rfl⟩ := h
  rw [map_mul,harmonic_of_unit k u.isUnit,mul_one]

/-- Every nonnegative prime-class weight that vanishes on inert primes and agrees on
conjugate split classes has its finite sums dominated by twice a rational-prime sum. -/
theorem split_sum_upper (S : Finset (Associates GaussianInt))
    (hS : ∀ a ∈ S, Irreducible a) (g : Associates GaussianInt → ℝ) (hg : ∀ a, 0 ≤ g a)
    (hinert : ∀ p : ℕ, p.Prime → p%4 = 3 → g (Associates.mk (p:GaussianInt)) = 0)
    (hstar : ∀ p : ℕ, p.Prime → p%4 ≠ 3 →
      g (Associates.mk (star (splitFactor p))) = g (Associates.mk (splitFactor p))) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p%4 ≠ 3) ∧
      ∑ a ∈ S, g a ≤ 2 * ∑ p ∈ P, g (Associates.mk (splitFactor p)) := by
  classical
  let T := S.filter fun a => g a ≠ 0
  let A (p : ℕ) := Associates.mk (splitFactor p)
  let B (p : ℕ) := Associates.mk (star (splitFactor p))
  have exh (a : T) : ∃ p : ℕ, p.Prime ∧ p%4 ≠ 3 ∧ ((a:Associates GaussianInt) = A p ∨ a.val = B p) := by
    obtain ⟨ha,hn⟩ := Finset.mem_filter.mp a.prop
    obtain ⟨z,hz⟩ := Associates.mk_surjective a.val
    have hi : Irreducible z := Associates.irreducible_mk.mp (hz.symm ▸ hS a.val ha)
    rcases gaussian_prime_cover hi.prime with ⟨p,hp,h4,h⟩ | ⟨p,hp,h4,h|h⟩
    · exact (hn (by rw [← hz, Associates.mk_eq_mk_iff_associated.mpr h, hinert p hp h4])).elim
    · exact ⟨p,hp,h4,Or.inl (hz.symm.trans (Associates.mk_eq_mk_iff_associated.mpr h))⟩
    · exact ⟨p,hp,h4,Or.inr (hz.symm.trans (Associates.mk_eq_mk_iff_associated.mpr h))⟩
  let pp (a : T) := (exh a).choose
  let P := Finset.univ.image pp
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p%4 ≠ 3 := by
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(exh a).choose_spec.1,(exh a).choose_spec.2.1⟩
  let w (p : ℕ) (a : Associates GaussianInt) :=
    (if a=A p then g (A p) else 0) + (if a=B p then g (B p) else 0)
  have hnn (p a) : 0 ≤ w p a := add_nonneg
    (ite_nonneg (hg _) (by rfl)) (ite_nonneg (hg _) (by rfl))
  refine ⟨P, hP, ?_⟩
  calc
    _ = ∑ a ∈ T, g a := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ a ∈ T, ∑ p ∈ P, w p a := by
      apply Finset.sum_le_sum
      intro a ha
      let i : T := ⟨a,ha⟩
      apply le_trans _ (Finset.single_le_sum (f := fun p => w p a) (fun p _ => hnn p a)
        (Finset.mem_image_of_mem pp (Finset.mem_univ i)))
      rcases (exh i).choose_spec.2.2 with h|h
      · change a = A (pp i) at h
        simp [w,h,ite_nonneg (hg _) (le_refl 0)]
      · change a = B (pp i) at h
        simp [w,h,ite_nonneg (hg _) (le_refl 0)]
    _ = ∑ p ∈ P, ∑ a ∈ T, w p a := Finset.sum_comm
    _ ≤ ∑ p ∈ P, 2*g (A p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hb : g (B p) = g (A p) := hstar p (hP p hp).1 (hP p hp).2
      simp only [w, Finset.sum_add_distrib, Finset.sum_ite_eq', hb]
      split_ifs <;> linarith [hg (A p)]
    _ = _ := (Finset.mul_sum ..).symm

end SquareGrid
end

/- PrimeAnglesEuler -/
section
/-! Euler products over irreducible classes in the Gaussian integers. -/
namespace GaussianEuler
open Filter Topology
open scoped Classical

abbrev A := Associates GaussianInt
abbrev P := {p : A // Irreducible p}

private noncomputable def removed (f : A →*₀ ℂ) (S : Finset P) (n : A) : ℂ :=
  if ∀ p ∈ S, ¬ p.val ∣ n then f n else 0

private lemma norm_removed (f : A →*₀ ℂ) (S : Finset P) (n : A) :
    ‖removed f S n‖ ≤ ‖f n‖ := by unfold removed; split <;> simp

private lemma removed_mul (f : A →*₀ ℂ) (S : Finset P) {p : P} (hp : p ∉ S) (n : A) :
    removed f S (p.val*n) = f p.val * removed f S n := by
  have h (q : P) (hq : q ∈ S) : q.val ∣ p.val*n ↔ q.val ∣ n := by
    rw [q.prop.prime.dvd_mul]
    have hn : ¬q.val ∣ p.val := fun hd ↦ hp <| (show q = p from
      Subtype.ext (associated_iff_eq.mp (q.prop.associated_of_dvd p.prop hd))) ▸ hq
    simp [hn]
  by_cases hn : ∀ q ∈ S, ¬q.val ∣ n
  · have hm : ∀ q ∈ S, ¬q.val ∣ p.val*n := fun q hq ↦ mt (h q hq).1 (hn q hq)
    simp only [removed,if_pos hm,if_pos hn,map_mul]
  · have hm : ¬ ∀ q ∈ S, ¬q.val ∣ p.val*n := fun H ↦ hn fun q hq ↦ mt (h q hq).2 (H q hq)
    simp only [removed,if_neg hm,if_neg hn,mul_zero]

private lemma finite_removal (f : A →*₀ ℂ) (hf : Summable fun n ↦ ‖f n‖) (S : Finset P) :
    (∏ p ∈ S, (1-f p.val)) * (∑' n, f n) = ∑' n, removed f S n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [removed]
  | @insert p S hp ih =>
    let g : A → ℂ := fun n ↦ if p.val ∣ n then removed f S n else 0
    have hRs : Summable (removed f S) := hf.of_norm_bounded (norm_removed f S)
    have hg : Summable g := hf.of_norm_bounded fun n ↦ by
      dsimp [g]; split
      · exact norm_removed f S n
      · simp
    have hrem : ∀ n, removed f (insert p S) n = removed f S n - g n := by
      intro n
      by_cases h : p.val ∣ n <;> simp [removed,g,h]
    have hj : Function.Injective (fun n : A ↦ p.val*n) := mul_right_injective₀ p.prop.ne_zero
    have hg' : (∑' n, g n) = f p.val * ∑' n, removed f S n := by
      rw [←hj.tsum_eq (f := g) (by
        intro n hn
        by_contra h
        have hn' : ¬p.val ∣ n := fun ⟨k,hk⟩ ↦ h ⟨k,hk.symm⟩
        exact hn (by simp [g,hn'])), ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp [g,removed_mul f S hp]
    simp_rw [hrem]
    rw [Finset.prod_insert hp, mul_assoc, ih, hRs.tsum_sub hg, hg']
    ring

/-- Removing a finite set of Gaussian primes leaves precisely the terms coprime to that set.
As the set increases, only the unit contributes to the limiting series. -/
theorem reciprocal_product_limit (f : A →*₀ ℂ) (hf : Summable fun n ↦ ‖f n‖) :
    Tendsto (fun S : Finset P ↦ (∏ p ∈ S, (1-f p.val)) * (∑' n, f n)) atTop (𝓝 1) := by
  classical
  let g : A → ℂ := fun n ↦ if n = 1 then 1 else 0
  have hg : ∑' n, g n = 1 := by simp [g]
  simp_rw [finite_removal f hf]
  rw [←hg]
  apply tendsto_tsum_of_dominated_convergence hf
  · intro n
    by_cases h1 : n = 1
    · subst n
      have hc (S : Finset P) : removed f S 1 = 1 := by
        have h (p : P) : ¬p.val ∣ 1 := fun hh ↦ p.prop.not_isUnit (isUnit_iff_dvd_one.mpr hh)
        simp [removed,h]
      simp [g,hc]
    · by_cases h0 : n = 0
      · subst n
        simp [g,h1,removed]
      obtain ⟨q,hq,hqn⟩ := WfDvdMonoid.exists_irreducible_factor
        (mt (Associates.isUnit_iff_eq_one n).mp h1) h0
      have he : ∀ᶠ S : Finset P in atTop, removed f S n = g n := by
        filter_upwards [eventually_ge_atTop ({⟨q,hq⟩} : Finset P)] with S hS
        have hh : (⟨q,hq⟩ : P) ∈ S := hS (Finset.mem_singleton_self _)
        have hn : ¬ ∀ p ∈ S, ¬p.val ∣ n := fun H ↦ H ⟨q,hq⟩ hh hqn
        simp only [removed,g,if_neg hn,if_neg h1]
      exact tendsto_const_nhds.congr' (he.mono fun _ h ↦ h.symm)
  · exact .of_forall fun S n ↦ norm_removed f S n

theorem series_ne_zero (f : A →*₀ ℂ) (hf : Summable fun n ↦ ‖f n‖) :
    ∑' n, f n ≠ 0 := by
  intro h
  have ht := reciprocal_product_limit f hf
  simp [h] at ht

theorem reciprocal_product (f : A →*₀ ℂ) (hf : Summable fun n ↦ ‖f n‖) :
    HasProd (fun p : P ↦ 1-f p.val) (∑' n, f n)⁻¹ := by
  have ht := (reciprocal_product_limit f hf).mul_const (∑' n, f n)⁻¹
  simpa [HasProd, mul_assoc,series_ne_zero f hf] using ht

end GaussianEuler
end

/- AnglesDefectTransfer -/
section
/-! Transfer of unbounded Gaussian prime harmonic defects to rational primes. -/
namespace SquareGrid
open Complex
open scoped ComplexConjugate

private noncomputable def defect (k : ℕ) (a : Associates GaussianInt) : ℝ :=
  (1-(harmonic (4*k) (Quot.out a)).re) / ((Quot.out a).norm.natAbs:ℝ)

private theorem defect_mk (k : ℕ) (z : GaussianInt) :
    defect k (Associates.mk z) = (1-(harmonic (4*k) z).re) / (z.norm.natAbs:ℝ) := by
  have h := Associates.mk_quot_out z
  have hn {v w : GaussianInt} (ha : Associated v w) : v.norm.natAbs = w.norm.natAbs := by
    obtain ⟨u,rfl⟩ := ha
    rw [Zsqrtd.norm_mul,Int.natAbs_mul,Zsqrtd.norm_eq_one_iff.mpr u.isUnit,mul_one]
  rw [defect,harmonic_of_associated k h,hn h]

private theorem defect_nonneg (k : ℕ) (a : Associates GaussianInt) : 0 ≤ defect k a := by
  obtain ⟨z,rfl⟩ := Associates.mk_surjective a
  rw [defect_mk]
  apply div_nonneg _ (by positivity)
  apply sub_nonneg.mpr ((Complex.re_le_norm _).trans ?_)
  change ‖((z:ℂ) / (‖(z:ℂ)‖:ℂ))^(4*k)‖ ≤ 1
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact pow_le_one₀ (by positivity) (div_self_le_one _)

private theorem defect_natCast (k p : ℕ) (hp : p.Prime) :
    defect k (Associates.mk (p:GaussianInt)) = 0 := by
  rw [defect_mk]
  have h : ((p:GaussianInt):ℂ) = (p:ℂ) := map_natCast GaussianInt.toComplex p
  simp [harmonic, h, hp.ne_zero]

private theorem defect_star (k : ℕ) (z : GaussianInt) :
    defect k (Associates.mk (star z)) = defect k (Associates.mk z) := by
  rw [defect_mk,defect_mk,harmonic_star,Zsqrtd.norm_conj,Complex.conj_re]

/-- The Gaussian Euler argument supplies unbounded finite sums over all Gaussian
prime classes. This transfers the conclusion to finite sets of split or ramified
rational primes for the arbitrarily chosen representative above each prime. -/
theorem rational_angular_defect_unbounded
    (hu : ∀ k : ℕ, 0 < k → ∀ B : ℝ, ∃ S : Finset GaussianEuler.P,
      B < ∑ p ∈ S, (1-(harmonic (4*k) (Quot.out p.val)).re) /
        ((Quot.out p.val).norm.natAbs:ℝ))
    (h : ℕ) (hh : 0 < h) (B : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (splitFactor p).norm.natAbs = p) ∧
      B < ∑ p ∈ P, (1-Real.cos (((8*h:ℕ):ℝ)*(splitFactor p:ℂ).arg)) / (p:ℝ) := by
  classical
  obtain ⟨S,hs⟩ := hu (2*h) (by omega) (2*B)
  let e : GaussianEuler.P ↪ Associates GaussianInt := ⟨Subtype.val, Subtype.val_injective⟩
  have hS (a) (ha : a ∈ S.map e) : Irreducible a := by
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp ha
    exact p.prop
  obtain ⟨P,hP,hbound⟩ := split_sum_upper (S.map e) hS (defect (2*h)) (defect_nonneg _) 
    (fun p hp _ => defect_natCast _ p hp) (fun p _ _ => defect_star _ (splitFactor p))
  rw [Finset.sum_map] at hbound
  have hl : 2*B < ∑ a ∈ S, defect (2*h) (e a) := hs
  have hr (p : ℕ) (hp : p ∈ P) : defect (2*h) (Associates.mk (splitFactor p)) =
      (1-Real.cos (((8*h:ℕ):ℝ)*(splitFactor p:ℂ).arg)) / (p:ℝ) := by
    have hn := splitFactor_norm (hP p hp).1 (hP p hp).2
    have hz : splitFactor p ≠ 0 := by
      intro h0
      have := (hP p hp).1.ne_zero
      simp [h0,Zsqrtd.norm_zero] at hn
      exact this hn.symm
    rw [defect_mk,hn,harmonic_re _ hz, show 4*(2*h) = 8*h by omega]
  refine ⟨P,fun p hp => ⟨(hP p hp).1, splitFactor_norm (hP p hp).1 (hP p hp).2⟩, ?_⟩
  rw [Finset.sum_congr rfl hr] at hbound
  linarith

/-- The same unboundedness in the absolute-cosine contraction weights themselves. -/
theorem rational_absolute_defect_unbounded
    (hu : ∀ k : ℕ, 0 < k → ∀ B : ℝ, ∃ S : Finset GaussianEuler.P,
      B < ∑ p ∈ S, (1-(harmonic (4*k) (Quot.out p.val)).re) /
        ((Quot.out p.val).norm.natAbs:ℝ))
    (h : ℕ) (hh : 0 < h) (B : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (splitFactor p).norm.natAbs = p) ∧
      B < ∑ p ∈ P, (1-primeCosWeight splitFactor h p)/(p:ℝ) := by
  obtain ⟨P,hP,hs⟩ := rational_angular_defect_unbounded hu h hh (4*B)
  refine ⟨P,hP,?_⟩
  have he (p : ℕ) : (1-Real.cos (((8*h:ℕ):ℝ)*(splitFactor p:ℂ).arg))/(p:ℝ) ≤
      4*((1-primeCosWeight splitFactor h p)/(p:ℝ)) := by
    let t := ((4*h:ℕ):ℝ)*(splitFactor p:ℂ).arg
    have h2 : ((8*h:ℕ):ℝ)*(splitFactor p:ℂ).arg = 2*t := by dsimp [t]; push_cast; ring
    rw [h2, Real.cos_two_mul, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    change 1-(2*(Real.cos t)^2-1) ≤ 4*(1-|Real.cos t|)
    nlinarith [sq_nonneg (1-|Real.cos t|),sq_abs (Real.cos t)]
  have hr := Finset.sum_le_sum (s := P) (fun p _ => he p)
  rw [← Finset.mul_sum] at hr
  linarith

end SquareGrid
end

/- PrimeAnglesDefect -/
section
namespace GaussianEuler
open Filter Topology Real Complex

/-- A twisted local Euler factor differs multiplicatively from the untwisted factor
by at most the exponential of eight times the weighted angular defect. -/
theorem local_defect {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1/2) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖1 - (r:ℂ)*w‖ ≤ (1-r)*Real.exp (8*(r*(1-w.re))) := by
  let d := r*(1-w.re)
  have hd : 0 ≤ d := mul_nonneg hr <| sub_nonneg.mpr (w.re_le_norm.trans_eq hw)
  have ha : 0 ≤ 1-r := by linarith
  have hw' : w.re*w.re + w.im*w.im = 1 := by
    change Complex.normSq w = 1
    rw [Complex.normSq_eq_norm_sq,hw,one_pow]
  have hq : ‖1-(r:ℂ)*w‖^2 = (1-r)^2 + 2*d := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, zero_sub]
    dsimp [d]
    linear_combination r^2 * hw'
  have h1 : 1 ≤ 4*(1-r)^2 := by nlinarith [sq_nonneg (1/2-r)]
  have h2 : (1-r)^2+2*d ≤ (1-r)^2*(1+8*d) := by nlinarith [mul_nonneg (sub_nonneg.mpr h1) hd]
  have h3 : 1+8*d ≤ (1+8*d)^2 := by nlinarith [sq_nonneg d]
  have h4 := h2.trans <| mul_le_mul_of_nonneg_left h3 (sq_nonneg (1-r))
  have hs : ‖1-(r:ℂ)*w‖ ≤ (1-r)*(1+8*d) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (by positivity))).mp
    rwa [hq,mul_pow]
  exact hs.trans <| mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (8*d)]) ha

/-- A uniform upper bound on the prime defect sums gives a nonzero lower bound for
the modulus of the normalized twisted series. -/
theorem ratio_lower (f g : A →*₀ ℂ) (hf : Summable fun n ↦ ‖f n‖) (hg : Summable fun n ↦ ‖g n‖)
    (r : P → ℝ) (w : P → ℂ) (hr : ∀ p, 0 ≤ r p) (hr' : ∀ p, r p ≤ 1/2)
    (hw : ∀ p, ‖w p‖ = 1) (hfv : ∀ p, f p.val = r p * w p)
    (hgv : ∀ p, g p.val = (r p : ℂ)) {M : ℝ}
    (hM : ∀ S : Finset P, ∑ p ∈ S, r p * (1-(w p).re) ≤ M) :
    (Real.exp (8*M))⁻¹ ≤ ‖(∑' n, f n) / (∑' n, g n)‖ := by
  classical
  have hl (p : P) : ‖1-f p.val‖ ≤ Real.exp (8*(r p*(1-(w p).re))) * ‖1-g p.val‖ := by
    rw [hfv,hgv,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hr' p] : 0 ≤ 1-r p)]
    simpa only [Complex.ofReal_one,mul_comm] using local_defect (hr p) (hr' p) (hw p)
  have hS (S : Finset P) : ∏ p ∈ S, ‖1-f p.val‖ ≤ Real.exp (8*M) * ∏ p ∈ S, ‖1-g p.val‖ := by
    calc
      _ ≤ ∏ p ∈ S, (Real.exp (8*(r p*(1-(w p).re))) * ‖1-g p.val‖) :=
        Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun p _ ↦ hl p)
      _ = Real.exp (8*(∑ p ∈ S, r p*(1-(w p).re))) * ∏ p ∈ S, ‖1-g p.val‖ := by
        rw [Finset.prod_mul_distrib,←Real.exp_sum,Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr <| by linarith [hM S])
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  have hf' := (reciprocal_product f hf).norm
  have hg' := (reciprocal_product g hg).norm
  have hi := le_of_tendsto_of_tendsto hf' ((tendsto_const_nhds (x:=Real.exp (8*M))).mul hg')
    (.of_forall hS)
  rw [norm_inv,norm_inv] at hi
  have hn1 := norm_pos_iff.mpr (series_ne_zero f hf)
  have hn2 := norm_pos_iff.mpr (series_ne_zero g hg)
  rw [norm_div]
  have he := Real.exp_pos (8*M)
  rw [inv_eq_one_div,div_le_div_iff₀ he hn2]
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div,div_le_div_iff₀ hn1 hn2] at hi
  linarith

end GaussianEuler
end

/- GaussianRotation -/
section
/-! Rotation by the Gaussian integer 2+i and its five residue classes. -/
namespace GaussianRotation
open Complex
open scoped ComplexConjugate

def d : GaussianInt := ⟨2,1⟩

private def residue (z : GaussianInt) : Fin 5 :=
  ⟨((z.re - 2*z.im) % 5).toNat, by omega⟩

private def quotient (z : GaussianInt) : GaussianInt :=
  let v := -((z.re - 2*z.im) / 5)
  ⟨z.im - 2*v, v⟩

def cosets : Fin 5 × GaussianInt ≃ GaussianInt where
  toFun a := d*a.2 + (a.1.val : GaussianInt)
  invFun z := (residue z,quotient z)
  left_inv := by
    rintro ⟨⟨r,hr⟩,x,y⟩
    apply Prod.ext
    · apply Fin.ext
      simp [residue,d,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> omega
    · apply Zsqrtd.ext <;> simp [quotient,d,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> omega
  right_inv := by
    rintro ⟨x,y⟩
    apply Zsqrtd.ext <;> simp [quotient,residue,d,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> omega

private def modFive : GaussianInt →+* ZMod 5 := Zsqrtd.lift ⟨3, by decide⟩

theorem phase_pow_ne_one (k : ℕ) (h : k ≠ 0) :
    ((d : ℂ) / (‖(d : ℂ)‖ : ℂ))^k ≠ 1 := by
  intro he
  have hd : (d : ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr (by decide)
  have hn : (‖(d : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hd)
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hn)] at he
  have he' := congrArg (conj : ℂ → ℂ) he
  simp only [map_pow, Complex.conj_ofReal] at he'
  have eq : d^k = (star d)^k := by
    apply GaussianInt.toComplex_injective
    simp only [map_pow]
    simpa only [← GaussianInt.toComplex_star] using he.trans he'.symm
  have eq' := congrArg modFive eq
  simp only [map_pow] at eq'
  have a : modFive d = 0 := by decide
  have b : modFive (star d) = 4 := by decide
  rw [a,b,zero_pow h] at eq'
  have h4 : (4 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact (pow_ne_zero k h4) eq'.symm

end GaussianRotation
end

/- GaussianMean -/
section
namespace GaussianRotation
open Filter Topology Complex

noncomputable def term (k : ℕ) (s : ℝ) (z : ℂ) : ℂ :=
  (z / (‖z‖ : ℂ))^k * ((‖z‖ ^ (-2*s) : ℝ) : ℂ)

theorem term_mul (k : ℕ) (s : ℝ) (z w : ℂ) :
    term k s (z*w) = term k s z * term k s w := by
  simp only [term,norm_mul, Complex.ofReal_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [mul_div_mul_comm, mul_pow]
  ring

theorem norm_term_le (k : ℕ) (s : ℝ) (z : ℂ) :
    ‖term k s z‖ ≤ ‖z‖ ^ (-2*s) := by
  rw [term,norm_mul,norm_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
    Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) (div_self_le_one _))

theorem gaussian_mass_le_one {s : ℝ} (hs : 1 < s) (z : GaussianInt) :
    ‖(z:ℂ)‖ ^ (-2*s) ≤ 1 := by
  by_cases hz : z = 0
  · subst z
    rw [GaussianInt.toComplex_zero, norm_zero, Real.zero_rpow (by linarith : -2*s ≠ 0)]
    norm_num
  have hn := GaussianInt.norm_pos.mpr hz
  have hn' : (1:ℝ) ≤ Complex.normSq (z:ℂ) := by
    rw [← GaussianInt.intCast_real_norm]
    exact_mod_cast (show (1:ℤ) ≤ z.norm by omega)
  have hs' : 1 ≤ ‖(z:ℂ)‖ := by nlinarith [Complex.sq_norm (z:ℂ), norm_nonneg (z:ℂ)]
  exact Real.rpow_le_one_of_one_le_of_nonpos hs' (by linarith)

private theorem term_one_limit (k : ℕ) {ι : Type*} {f : Filter ι} {s : ι → ℝ} {w : ι → ℂ}
    (hs : Tendsto s f (𝓝 1)) (hw : Tendsto w f (𝓝 1)) :
    Tendsto (fun a => term k (s a) (w a)) f (𝓝 1) := by
  have hn : Tendsto (fun a => ‖w a‖) f (𝓝 1) := by simpa using hw.norm
  have ht := (hw.div (Complex.continuous_ofReal.continuousAt.tendsto.comp hn)
    (by simp : ((1:ℝ):ℂ) ≠ 0)).pow k
  have hp := hn.rpow (tendsto_const_nhds.mul hs : Tendsto (fun a => -2*s a) f (𝓝 (-2*1))) (Or.inl one_ne_zero)
  simpa [term] using ht.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hp)

theorem translate_relative {k : ℕ} (r : Fin 5)
    (grow : Tendsto (fun z : GaussianInt => ‖(z:ℂ)‖) cofinite atTop)
    {ε : ℝ} (he : 0 < ε) :
    ∃ F : Finset GaussianInt, ∀ᶠ s in 𝓝[>] (1:ℝ), ∀ z ∉ F,
      ‖term k s (cosets (r,z) : GaussianInt) - term k s (d*z : GaussianInt)‖ ≤
        ε * ‖(z:ℂ)‖ ^ (-2*s) := by
  classical
  let l := (𝓝[>] (1:ℝ)) ×ˢ (cofinite : Filter GaussianInt)
  have hd : (d : ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr (by decide)
  have g := grow.const_mul_atTop (norm_pos_iff.mpr hd)
  have gi : Tendsto (fun z : GaussianInt => ((d:ℂ)*(z:ℂ))⁻¹) cofinite (𝓝 0) := by
    apply tendsto_inv₀_cobounded.comp
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa only [norm_mul] using g
  have w : Tendsto (fun u : ℝ × GaussianInt => 1+(r.val:ℂ)*((d:ℂ)*(u.2:ℂ))⁻¹) l (𝓝 1) := by
    simpa using (tendsto_const_nhds.add ((gi.comp tendsto_snd).const_mul (r.val:ℂ)) :
      Tendsto _ l (𝓝 ((1:ℂ) + r.val*0)))
  have rel := (term_one_limit k (tendsto_fst.mono_right nhdsWithin_le_nhds) w).sub_const (1:ℂ)
  have err : ∀ᶠ u : ℝ × GaussianInt in l,
      ‖term k u.1 (1+(r.val:ℂ)*((d:ℂ)*(u.2:ℂ))⁻¹)-1‖ < ε := by
    apply rel.norm.eventually_lt_const
    simpa using he
  obtain ⟨S,hS,T,hT,hST⟩ := eventually_prod_iff.mp err
  have hT' := Filter.mem_cofinite.mp hT
  refine ⟨insert 0 hT'.toFinset, ?_⟩
  filter_upwards [hS,self_mem_nhdsWithin] with s hs hs1
  intro z hz
  have z0 : (z:ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr (by aesop)
  have hdz := mul_ne_zero hd z0
  have zT : T z := by
    by_contra h
    apply hz
    exact Finset.mem_insert_of_mem (hT'.mem_toFinset.mpr h)
  have h := (hST hs zT).le
  have eq : ((cosets (r,z) : GaussianInt):ℂ) = (d:ℂ)*(z:ℂ) *
      (1+(r.val:ℂ)*((d:ℂ)*(z:ℂ))⁻¹) := by
    change GaussianInt.toComplex (d*z+r.val) = _
    simp only [map_add,map_mul,map_natCast]
    field_simp
  rw [eq,GaussianInt.toComplex_mul,term_mul,← mul_sub_one,norm_mul]
  have cap : ‖term k s ((d:ℂ)*(z:ℂ))‖ ≤ ‖(z:ℂ)‖ ^ (-2*s) := by
    rw [term_mul,norm_mul]
    exact (mul_le_mul (norm_term_le ..) (norm_term_le ..) (norm_nonneg _)
      (Real.rpow_nonneg (norm_nonneg _) _)).trans (mul_le_of_le_one_left (by positivity)
      (gaussian_mass_le_one hs1 d))
  exact (mul_le_mul cap h (norm_nonneg _) (by positivity)).trans_eq (mul_comm ..)

end GaussianRotation
end

/- PrimeAnglesWeights -/
section
namespace GaussianEuler
open Filter Topology
open SquareGrid

noncomputable abbrev generator (p : P) : GaussianInt := Quot.out p.val
noncomputable abbrev primeNorm (p : P) : ℝ := ((generator p).norm.natAbs : ℝ)

theorem generator_irreducible (p : P) : Irreducible (generator p) :=
  Associates.irreducible_mk.mp ((Associates.quot_out p.val).symm ▸ p.prop)

private lemma norm_ge_two (p : P) : 2 ≤ primeNorm p := by
  have h0 : (generator p).norm.natAbs ≠ 0 := by
    simpa using (generator_irreducible p).ne_zero
  have h1 : (generator p).norm.natAbs ≠ 1 := fun h ↦
    (generator_irreducible p).not_isUnit (Zsqrtd.norm_eq_one_iff.mp h)
  exact_mod_cast (show 2 ≤ (generator p).norm.natAbs by omega)

theorem harmonic_unit_norm (k : ℕ) (p : P) : ‖harmonic k (generator p)‖ = 1 := by
  have hz : ((generator p):ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr (generator_irreducible p).ne_zero
  simp [SquareGrid.harmonic, norm_pow, norm_ne_zero_iff.mpr hz]

theorem angular_term_formula (k : ℕ) (s : ℝ) (p : P) :
    GaussianRotation.term k s (generator p : ℂ) =
      ((primeNorm p ^ (-s) : ℝ) : ℂ) * harmonic k (generator p) := by
  have hn : primeNorm p = ‖(generator p : ℂ)‖^2 := by
    rw [primeNorm,GaussianInt.natCast_natAbs_norm,GaussianInt.intCast_real_norm,Complex.normSq_eq_norm_sq]
  rw [hn,←Real.rpow_natCast_mul (norm_nonneg _)]
  simp [GaussianRotation.term, SquareGrid.harmonic, mul_comm]

theorem ratio_lower_gaussian (k : ℕ) (s : ℝ) (hs : 1 < s)
    (f g : A →*₀ ℂ) (hf : Summable fun n ↦ ‖f n‖) (hg : Summable fun n ↦ ‖g n‖)
    (hfv : ∀ p : P, f p.val = GaussianRotation.term k s (generator p : ℂ))
    (hgv : ∀ p : P, g p.val = GaussianRotation.term 0 s (generator p : ℂ))
    {B : ℝ} (hB : ∀ S : Finset P, ∑ p ∈ S, (1 - (harmonic k (generator p)).re) / primeNorm p ≤ B) :
    (Real.exp (8*B))⁻¹ ≤ ‖(∑' n, f n) / (∑' n, g n)‖ := by
  let r (p : P) := primeNorm p ^ (-s)
  have hr (p : P) : r p ≤ (primeNorm p)⁻¹ := by
    dsimp [r]
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_ge_two p]) (by linarith)
  apply ratio_lower f g hf hg r (fun p ↦ harmonic k (generator p))
  · exact fun p ↦ Real.rpow_nonneg (by linarith [norm_ge_two p]) _
  · intro p
    exact (hr p).trans <| by rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) (norm_ge_two p)
  · exact harmonic_unit_norm k
  · intro p
    exact (hfv p).trans (angular_term_formula k s p)
  · intro p
    simpa only [angular_term_formula,SquareGrid.harmonic,MonoidHom.coe_mk,OneHom.coe_mk,pow_zero,mul_one] using hgv p
  · intro S
    apply le_trans _ (hB S)
    apply Finset.sum_le_sum
    intro p _
    rw [div_eq_mul_inv,mul_comm]
    exact mul_le_mul_of_nonneg_left (hr p) (sub_nonneg.mpr <|
      (harmonic k (generator p)).re_le_norm.trans_eq (harmonic_unit_norm k p))

end GaussianEuler
end

/- GaussianAverage -/
section
namespace GaussianRotation
open Filter Topology

/-- A normalized sum tends to zero when the summands are negligible outside a finite set
and uniformly bounded on that set. -/
theorem negligible_average {α : Type*} (w : ℝ → α → ℝ) (f : ℝ → α → ℂ)
    (hw : ∀ s x, 0 ≤ w s x) (hsum : ∀ s > 1, Summable (w s))
    (hinf : Tendsto (fun s => ∑' x, w s x) (𝓝[>] 1) atTop)
    (hb : ∀ s > 1, ∀ x, ‖f s x‖ ≤ 2)
    (small : ∀ ε > (0:ℝ), ∃ T : Finset α, ∀ᶠ s in 𝓝[>] 1, ∀ x ∉ T,
      ‖f s x‖ ≤ ε*w s x) :
    Tendsto (fun s => (∑' x, f s x) / ((∑' x, w s x : ℝ):ℂ)) (𝓝[>] 1) (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨T,hT⟩ := small (ε/2) (half_pos he)
  let b (x : α) : ℝ := if x ∈ T then 2 else 0
  have sb : Summable b := summable_of_ne_finset_zero (s := T) (by simp [b])
  let B := ∑' x, b x
  have hlim : Tendsto (fun s => B / ∑' x, w s x) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hinf
  filter_upwards [hT,self_mem_nhdsWithin,hinf.eventually (eventually_gt_atTop (0:ℝ)),
    hlim.eventually_lt_const (half_pos he)] with s hs hs1 hM hB
  have hau (x : α) : ‖f s x‖ ≤ ε/2*w s x + b x := by
    by_cases hx : x ∈ T
    · rw [show b x = 2 by simp [b,hx]]
      linarith [hb s hs1 x, mul_nonneg (half_pos he).le (hw s x)]
    · simpa [b,hx] using hs x hx
  have hsw := ((hsum s hs1).mul_left (ε/2)).add sb
  have hsf := hsw.of_nonneg_of_le (fun x => norm_nonneg (f s x)) hau
  have hcap := (norm_tsum_le_tsum_norm hsf).trans (hsf.tsum_le_tsum hau hsw)
  rw [Summable.tsum_add ((hsum s hs1).mul_left (ε/2)) sb, tsum_mul_left] at hcap
  rw [dist_zero_right,norm_div,Complex.norm_real,Real.norm_of_nonneg hM.le,div_lt_iff₀ hM]
  have hBB := (div_lt_iff₀ hM).mp hB
  dsimp only [B] at hBB
  linarith

end GaussianRotation
end

/- GaussianMass -/
section
namespace SquareGrid.Gaussian

open Filter Topology

noncomputable def mass (s : ℝ) (z : GaussianInt) : ℝ := ‖(z : ℂ)‖ ^ (-2*s)

theorem mass_nonneg (s : ℝ) (z : GaussianInt) : 0 ≤ mass s z :=
  Real.rpow_nonneg (norm_nonneg _) _

private def coords (z : GaussianInt) : Fin 2 → ℤ := ![z.re, z.im]

private theorem coords_injective : Function.Injective coords := by
  intro x y h
  exact Zsqrtd.ext (by simpa [coords] using congrFun h 0) (by simpa [coords] using congrFun h 1)

private theorem coords_norm_le (z : GaussianInt) : ‖coords z‖ ≤ ‖(z : ℂ)‖ := by
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [coords, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_max]
  have eqabs (i : ℤ) : (i.natAbs : ℝ) = |(i : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [eqabs, eqabs, GaussianInt.intCast_re, GaussianInt.intCast_im]
  exact max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

theorem summable_mass {s : ℝ} (hs : 1 < s) : Summable (mass s) := by
  have sum := (EisensteinSeries.summable_one_div_norm_rpow (k := 2*s) (by linarith)).comp_injective coords_injective
  apply sum.of_nonneg_of_le (mass_nonneg s)
  intro z
  by_cases h : coords z = 0
  · have hz : z = 0 := Zsqrtd.ext (by simpa [coords] using congrFun h 0)
                                  (by simpa [coords] using congrFun h 1)
    rw [hz, mass, GaussianInt.toComplex_zero, norm_zero, Real.zero_rpow (by linarith)]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · simpa only [mass, neg_mul, Function.comp_apply] using
      (Real.rpow_le_rpow_of_nonpos (norm_pos_iff.2 h) (coords_norm_le z)
        (show -(2*s) ≤ 0 by linarith))

private def triangle (p : Σ n : ℕ, Fin (n+1)) : GaussianInt := ⟨(p.1 : ℤ)+1, p.2.val⟩

private theorem triangle_injective : Function.Injective triangle := by
  rintro ⟨n,i⟩ ⟨m,j⟩ h
  have he := congrArg Zsqrtd.re h
  simp only [triangle] at he
  have : n = m := by exact_mod_cast add_right_cancel he
  subst m
  have hi := congrArg Zsqrtd.im h
  simp only [triangle, Int.natCast_inj] at hi
  exact congrArg (Sigma.mk n) (Fin.ext hi)

private theorem triangle_estimate (p : Σ n : ℕ, Fin (n+1)) :
    1 / (2 * ((p.1:ℝ)+1))^2 ≤ mass 1 (triangle p) := by
  have hn : 0 < (p.1 : ℝ)+1 := by positivity
  have hp : (p.2.val : ℝ) ≤ (p.1 : ℝ)+1 := by exact_mod_cast p.2.isLt.le
  have hp' : 0 < ‖((triangle p : GaussianInt) : ℂ)‖ := by
    apply norm_pos_iff.2
    rw [ne_eq, GaussianInt.toComplex_eq_zero]
    intro h
    have := congrArg Zsqrtd.re h
    simp [triangle] at this
    omega
  have hz : ‖((triangle p : GaussianInt) : ℂ)‖ ≤ 2*((p.1:ℝ)+1) := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp [triangle, abs_of_nonneg hn.le]
    linarith
  rw [mass]
  norm_num [Real.rpow_neg (norm_nonneg _)] 
  simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hp') (pow_le_pow_left₀ (norm_nonneg _) hz 2)

theorem not_summable_mass_one : ¬Summable (mass 1) := by
  intro h
  let low (p : Σ n : ℕ, Fin (n+1)) : ℝ := 1 / (2 * ((p.1:ℝ)+1))^2
  have hn (p) : 0 ≤ low p := by dsimp [low]; positivity
  have hlow : Summable low := (h.comp_injective triangle_injective).of_nonneg_of_le hn triangle_estimate
  have hs := ((summable_sigma_of_nonneg hn).mp hlow).2
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n:ℝ)) 1).mp
  apply (hs.mul_left 4).congr
  intro n
  simp [low, tsum_fintype]
  field_simp
  ring

theorem tendsto_tsum_mass : Tendsto (fun s : ℝ => ∑' z, mass s z) (𝓝[>] 1) atTop := by
  apply tendsto_atTop.2
  intro B
  have exists_big : ∃ T : Finset GaussianInt, B < ∑ z ∈ T, mass 1 z := by
    by_contra! h
    exact not_summable_mass_one (summable_of_sum_le (mass_nonneg 1) h)
  obtain ⟨T,hT⟩ := exists_big
  have hc (z : GaussianInt) : ContinuousAt (fun s : ℝ => mass s z) 1 := by
    apply (Real.continuousAt_const_rpow' (by norm_num : (-2:ℝ)*1 ≠ 0)).comp
    fun_prop
  have hcT : ContinuousAt (fun s : ℝ => ∑ z ∈ T, mass s z) 1 :=
    tendsto_finsetSum _ (fun z _ => (hc z).tendsto)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (hcT.tendsto.eventually (eventually_gt_nhds hT))] with s hs hb
  exact hb.le.trans ((summable_mass hs).sum_le_tsum T (fun z _ => mass_nonneg s z))

theorem finite_norm_le (B : ℝ) : {z : GaussianInt | ‖(z : ℂ)‖ ≤ B}.Finite := by
  have h : (Metric.closedBall (0 : Fin 2 → ℤ) B).Finite :=
    (isCompact_closedBall _ _).finite_of_discrete
  apply (Set.Finite.preimage coords_injective.injOn h).subset
  intro z hz
  simpa [Metric.mem_closedBall, dist_zero_right] using (coords_norm_le z).trans hz

theorem tendsto_norm_cofinite : Tendsto (fun z : GaussianInt => ‖(z : ℂ)‖) cofinite atTop := by
  apply tendsto_atTop.2
  intro B
  apply Filter.mem_cofinite.2
  apply (finite_norm_le B).subset
  intro z hz
  change ¬ B ≤ ‖(z : ℂ)‖ at hz
  change ‖(z : ℂ)‖ ≤ B
  exact (lt_of_not_ge hz).le

end SquareGrid.Gaussian
end

/- GaussianTwist -/
section
namespace GaussianRotation
open Filter Topology Complex SquareGrid.Gaussian

noncomputable abbrev totalMass (s : ℝ) : ℝ := ∑' z, mass s z
noncomputable abbrev angularSum (k : ℕ) (s : ℝ) : ℂ := ∑' z : GaussianInt, term k s z

theorem summable_term (k : ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun z : GaussianInt => term k s z) :=
  (summable_mass hs).of_norm_bounded (fun z => norm_term_le k s z)

private noncomputable def changeOnCoset (k : ℕ) (r : Fin 5) (s : ℝ) (z : GaussianInt) : ℂ :=
  term k s (cosets (r,z) : GaussianInt) - term k s (d*z : GaussianInt)

private theorem coset_limit (k : ℕ) (r : Fin 5) :
    Tendsto (fun s : ℝ => (∑' z, changeOnCoset k r s z) / (totalMass s : ℂ)) (𝓝[>] 1) (𝓝 0) := by
  apply negligible_average mass _ mass_nonneg (fun _ => summable_mass) tendsto_tsum_mass
  · intro s hs z
    exact (norm_sub_le ..).trans (by
      linarith [(norm_term_le k s (cosets (r,z) : GaussianInt)).trans (gaussian_mass_le_one hs _),
        (norm_term_le k s (d*z : GaussianInt)).trans (gaussian_mass_le_one hs _)])
  · exact fun _ he => translate_relative r tendsto_norm_cofinite he

private theorem identity_sum (k : ℕ) {s : ℝ} (hs : 1 < s) :
    (∑ r : Fin 5, (∑' z, changeOnCoset k r s z) / (totalMass s:ℂ)) =
      (1-5*term k s d) * (angularSum k s / (totalMass s:ℂ)) := by
  have hall := summable_term k hs
  have hsC : Summable (fun p : Fin 5 × GaussianInt => term k s (cosets p : GaussianInt)) :=
    cosets.summable_iff.mpr hall
  have hsum : (∑ r : Fin 5, ∑' z, term k s (cosets (r,z) : GaussianInt)) = angularSum k s := by
    simpa only [tsum_fintype] using hsC.tsum_prod.symm.trans (cosets.tsum_eq (fun z : GaussianInt => term k s z))
  have hbase : Summable (fun z : GaussianInt => term k s (d*z : GaussianInt)) := by
    simpa only [GaussianInt.toComplex_mul,term_mul] using hall.mul_left (term k s d)
  unfold changeOnCoset
  rw [← Finset.sum_div]
  simp_rw [fun r : Fin 5 => (hsC.prod_factor r).tsum_sub hbase]
  rw [Finset.sum_sub_distrib,hsum]
  simp only [GaussianInt.toComplex_mul,term_mul,tsum_mul_left,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (_ - (5:ℂ) * (term k s d * angularSum k s)) / _ = _
  ring

/-- Every nonconstant angular Fourier coefficient of the norm-weighted lattice
measure tends to zero as its Dirichlet exponent decreases to one. -/
theorem normalized_angular_sum {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun s : ℝ => angularSum k s / (totalMass s:ℂ)) (𝓝[>] 1) (𝓝 0) := by
  let D (s : ℝ) : ℂ := 1-5*term k s d
  have step : Tendsto (fun s => D s * (angularSum k s / (totalMass s:ℂ))) (𝓝[>] 1) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin 5)) (fun r _ => coset_limit k r)
    simp only [Finset.sum_const_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact identity_sum k hs
  have hd : (d:ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr (by decide)
  have hdcont : ContinuousAt D 1 := by
    dsimp [D,term]
    fun_prop (disch := positivity)
  have dsq : ‖(d:ℂ)‖^2 = 5 := by
    rw [Complex.sq_norm, ← GaussianInt.intCast_real_norm]
    norm_num [d,Zsqrtd.norm]
  have coeff : ((‖(d:ℂ)‖^(-2*(1:ℝ)) : ℝ) : ℂ) = 1/5 := by
    rw [show -2*(1:ℝ) = -(2:ℕ) by norm_num, Real.rpow_neg (norm_nonneg _),Real.rpow_natCast,dsq]
    norm_num
  have dn : D 1 ≠ 0 := by
    dsimp only [D,term]
    rw [coeff]
    intro heq
    exact phase_pow_ne_one k hk (by linear_combination -heq)
  have hh := step.div (hdcont.tendsto.mono_left nhdsWithin_le_nhds) dn
  rw [zero_div] at hh
  apply hh.congr'
  filter_upwards [(hdcont.tendsto.mono_left nhdsWithin_le_nhds).eventually_ne dn] with s hs
  exact mul_div_cancel_left₀ _ hs

end GaussianRotation
end

/- GaussianAssociates -/
section
namespace GaussianEuler
open Filter Topology

private def gu (i : Fin 4) : GaussianInt :=
  ![⟨1,0⟩, ⟨-1,0⟩, ⟨0,1⟩, ⟨0,-1⟩] i

private lemma gu_unit (i : Fin 4) : IsUnit (gu i) :=
  (Zsqrtd.norm_eq_one_iff' (by decide) _).mp (by fin_cases i <;> decide)

private lemma gu_inj : Function.Injective gu := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private lemma eq_gu {z : GaussianInt} (h : IsUnit z) : ∃ i : Fin 4, gu i = z := by
  obtain ⟨a,b⟩ := z
  have hs := (Zsqrtd.norm_eq_one_iff' (by decide) _).mpr h
  simp [Zsqrtd.norm_def] at hs
  have ha1 : -1 ≤ a := by nlinarith [sq_nonneg (a+1), sq_nonneg b]
  have ha2 : a ≤ 1 := by nlinarith [sq_nonneg (a-1), sq_nonneg b]
  have hb1 : -1 ≤ b := by nlinarith [sq_nonneg (b+1), sq_nonneg a]
  have hb2 : b ≤ 1 := by nlinarith [sq_nonneg (b-1), sq_nonneg a]
  interval_cases a <;> interval_cases b <;>
    first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩ | exact ⟨3,rfl⟩ | norm_num at hs

private noncomputable def fiberEquiv (x : GaussianInt) (hx : x ≠ 0) :
    Fin 4 ≃ {z : GaussianInt // Associates.mk z = Associates.mk x} :=
  Equiv.ofBijective (fun i => ⟨x * gu i, by
    rw [←Associates.mk_mul_mk, Associates.mk_eq_one.mpr (gu_unit i), mul_one]⟩) <| by
    constructor
    · intro i j hij
      exact gu_inj (mul_left_cancel₀ hx (congrArg Subtype.val hij))
    · rintro ⟨z,hz⟩
      obtain ⟨u,hu⟩ := Associates.mk_eq_mk_iff_associated.mp hz.symm
      obtain ⟨i,hi⟩ := eq_gu u.isUnit
      exact ⟨i, Subtype.ext (by simpa [hi] using hu)⟩

theorem summable_mk_descend {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : Associates GaussianInt → E}
    (h : Summable fun z : GaussianInt => f (Associates.mk z)) : Summable f := by
  have hi : Function.Injective (fun a : Associates GaussianInt => Quot.out a) :=
    (show Function.LeftInverse Associates.mk (fun a : Associates GaussianInt => Quot.out a)
      from Associates.quot_out).injective
  simpa only [Function.comp_def, Associates.quot_out] using h.comp_injective hi

theorem tsum_mk_eq_four_mul {𝕜 : Type*} [RCLike 𝕜] {f : Associates GaussianInt → 𝕜}
    (h0 : f 0 = 0) (h : Summable fun z : GaussianInt => f (Associates.mk z)) :
    (∑' z : GaussianInt, f (Associates.mk z)) = 4 * ∑' a, f a := by
  have hsum := h.hasSum.tsum_fiberwise Associates.mk
  have inner (a : Associates GaussianInt) :
      (∑' z : Associates.mk ⁻¹' {a}, f (Associates.mk z.val)) = 4*f a := by
    obtain ⟨x,rfl⟩ := Associates.mk_surjective a
    by_cases hx : x = 0
    · subst x
      have hz (z : Associates.mk ⁻¹' {Associates.mk (0:GaussianInt)}) :
          f (Associates.mk z.val) = 0 := by
        rw [show Associates.mk z.val = 0 from z.prop, h0]
      simp_rw [hz]
      simp [h0]
    · change (∑' z : {z : GaussianInt // Associates.mk z = Associates.mk x}, f (Associates.mk z.val)) = _
      rw [← (fiberEquiv x hx).tsum_eq]
      simp only [show ∀ i, Associates.mk ((fiberEquiv x hx) i).val = Associates.mk x
        from fun i => ((fiberEquiv x hx) i).prop, tsum_fintype, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  simp_rw [inner] at hsum
  simpa [tsum_mul_left] using hsum.tsum_eq.symm

private theorem gu_term (i : Fin 4) (k : ℕ) (s : ℝ) :
    GaussianRotation.term (4*k) s (gu i : ℂ) = 1 := by
  have h4 : ((gu i : GaussianInt) : ℂ)^4 = 1 := by
    fin_cases i <;> norm_num [gu,GaussianInt.toComplex_def',Complex.I_sq, pow_succ]
  have hu : ‖((gu i : GaussianInt):ℂ)‖ = 1 := by
    fin_cases i <;> norm_num [gu, GaussianInt.toComplex_def']
  simp [GaussianRotation.term, hu, pow_mul, h4]

noncomputable def angularHom (k : ℕ) (s : ℝ) (hs : 1 < s) : Associates GaussianInt →*₀ ℂ where
  toFun := Quotient.lift (fun z : GaussianInt => GaussianRotation.term (4*k) s (z:ℂ)) <| by
    rintro x y ⟨u,rfl⟩
    obtain ⟨i,hi⟩ := eq_gu u.isUnit
    rw [GaussianInt.toComplex_mul, GaussianRotation.term_mul, ←hi, gu_term, mul_one]
  map_one' := by
    change GaussianRotation.term (4*k) s ((1:GaussianInt):ℂ) = 1
    simp [GaussianRotation.term, GaussianInt.toComplex_one]
  map_mul' := by
    intro a b
    obtain ⟨x,rfl⟩ := Associates.mk_surjective a
    obtain ⟨y,rfl⟩ := Associates.mk_surjective b
    exact (congrArg _ (GaussianInt.toComplex_mul x y)).trans (GaussianRotation.term_mul ..)
  map_zero' := by
    change GaussianRotation.term (4*k) s ((0:GaussianInt):ℂ) = 0
    simp [GaussianRotation.term, GaussianInt.toComplex_zero, Real.zero_rpow (by linarith : -(2*s) ≠ 0)]

theorem angularHom_mk (k : ℕ) (s : ℝ) (hs : 1 < s) (z : GaussianInt) :
    angularHom k s hs (Associates.mk z) = GaussianRotation.term (4*k) s (z:ℂ) := rfl

theorem norm_angularHom_mk (k : ℕ) (s : ℝ) (hs : 1 < s) (z : GaussianInt) :
    ‖angularHom k s hs (Associates.mk z)‖ = (z.norm.natAbs : ℝ)^(-s) := by
  have hn : (z.norm.natAbs : ℝ) = ‖(z:ℂ)‖^2 := by
    rw [← Int.cast_natCast, GaussianInt.abs_natCast_norm, GaussianInt.intCast_real_norm, Complex.sq_norm]
  rw [hn, angularHom_mk]
  by_cases hz : z = 0
  · subst z
    simp [GaussianRotation.term, GaussianInt.toComplex_zero, Real.zero_rpow (by linarith : -(2*s) ≠ 0),
      Real.zero_rpow (by linarith : -s ≠ 0)]
  have hzn : ‖(z:ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 (GaussianInt.toComplex_eq_zero.not.2 hz)
  rw [GaussianRotation.term, norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self hzn, one_pow, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← Real.rpow_natCast_mul (norm_nonneg _)]
  congr 1
  norm_num

theorem angularHom_summable_norm (k : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun a => ‖angularHom k s hs a‖) := by
  apply summable_mk_descend
  exact (SquareGrid.Gaussian.summable_mass hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun z => GaussianRotation.norm_term_le (4*k) s (z:ℂ))

theorem angular_sum_classes (k : ℕ) (s : ℝ) (hs : 1 < s) :
    GaussianRotation.angularSum (4*k) s = 4*∑' a, angularHom k s hs a :=
  tsum_mk_eq_four_mul (f := (angularHom k s hs : Associates GaussianInt → ℂ))
    (angularHom k s hs).map_zero (GaussianRotation.summable_term (4*k) hs)

theorem untwisted_sum_classes (s : ℝ) (hs : 1 < s) :
    (GaussianRotation.totalMass s : ℂ) = 4*∑' a, angularHom 0 s hs a := by
  convert angular_sum_classes 0 s hs using 1
  simp only [GaussianRotation.totalMass, GaussianRotation.angularSum, GaussianRotation.term,
    Nat.mul_zero, pow_zero, one_mul, SquareGrid.Gaussian.mass, Complex.ofReal_tsum]

theorem angular_ratio (k : ℕ) (s : ℝ) (hs : 1 < s) :
    (∑' a, angularHom k s hs a) / (∑' a, angularHom 0 s hs a) =
      GaussianRotation.angularSum (4*k) s / (GaussianRotation.totalMass s : ℂ) := by
  rw [angular_sum_classes k s hs, untwisted_sum_classes s hs]
  exact (mul_div_mul_left _ _ (by norm_num : (4:ℂ) ≠ 0)).symm

theorem normalized_angularHom {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun s : ℝ => if hs : 1 < s then
      (∑' a, angularHom k s hs a) / (∑' a, angularHom 0 s hs a) else 0) (𝓝[>] 1) (𝓝 0) := by
  apply (GaussianRotation.normalized_angular_sum (k := 4*k) (by positivity)).congr'
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [dif_pos hs, angular_ratio k s hs]

end GaussianEuler
end

/- PrimeAngles -/
section
namespace GaussianEuler
open Filter Topology

/-- The angular defects of the Gaussian prime classes have divergent harmonic weight. -/
theorem unbounded_defect (k : ℕ) (hk : 0 < k) (B : ℝ) :
    ∃ S : Finset P, B < ∑ p ∈ S,
      (1-(SquareGrid.harmonic (4*k) (Quot.out p.val)).re) / ((Quot.out p.val).norm.natAbs : ℝ) := by
  classical
  by_contra! hB
  have hlim := (normalized_angularHom hk.ne').norm
  have he : (0:ℝ) < (Real.exp (8*B))⁻¹ := inv_pos.mpr (Real.exp_pos _)
  have hev := hlim.eventually_lt_const (show ‖(0:ℂ)‖ < (Real.exp (8*B))⁻¹ by rwa [norm_zero])
  have hs1 : ∀ᶠ s in 𝓝[>] (1 : ℝ), 1 < s := self_mem_nhdsWithin
  obtain ⟨s,hs,hl⟩ := (hs1.and hev).exists
  change 1 < s at hs
  simp only [dif_pos hs] at hl
  apply (not_lt_of_ge ?_) hl
  apply ratio_lower_gaussian (4*k) s hs (angularHom k s hs) (angularHom 0 s hs)
    (angularHom_summable_norm k s hs) (angularHom_summable_norm 0 s hs) _ _ hB
  · intro p
    simpa only [Associates.quot_out] using angularHom_mk k s hs (Quot.out p.val)
  · intro p
    simpa only [Associates.quot_out,Nat.mul_zero] using angularHom_mk 0 s hs (Quot.out p.val)

end GaussianEuler
end

/- TauberianPort.MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi -/
section
/-!
# The Chebyshev psi function in a residue class

This file defines the von Mangoldt sum over one residue class, using the same
inclusive real cutoff convention as `Chebyshev.psi`.
-/

section
namespace Chebyshev

/-- The von Mangoldt sum over positive integers at most `x` in the residue class `a`. -/
noncomputable def psiResidueClass {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt.residueClass a n

/-- The residue-class von Mangoldt sum vanishes below one. -/
theorem psiResidueClass_of_lt_one {q : ℕ} (a : ZMod q) {x : ℝ}
    (hx : x < 1) : psiResidueClass a x = 0 := by
  simp [psiResidueClass, Nat.floor_eq_zero.mpr hx]

end Chebyshev
end
end

/- TauberianPort.MathlibExt.Analysis.Asymptotics.MonotoneIntegralCriterion -/
section
/-!
# Integral criterion for asymptotic equivalence to the identity

This file proves a Tauberian-style criterion (ATLAS `NumberTheoryI` Lemma 16.8):
if `f : ℝ → ℝ` is nondecreasing on `[1, ∞)` and the integral
`x ↦ ∫ t in Set.Ioc 1 x, (f t - t) / t ^ 2` converges to a finite limit as
`x → ∞`, then `f x ~ x`.

The proof argues by contradiction on both sides. If `f x ≥ lam * x` for
arbitrarily large `x` (with `lam > 1`), monotonicity forces the integrand to
stay above an explicit positive constant on the whole interval
`[b, lam' * b]`, whose length is proportional to `b`; the resulting integral
lower bound contradicts the Cauchy property of the convergent integral.
The lower estimate is symmetric, using the interval `[mu * b, b]`.
-/

section
namespace Asymptotics

open _root_.Filter MeasureTheory Set Topology

/-- Cauchy-tail reformulation of convergence, used to control integral tails. -/
private lemma cauchy_of_tendsto {F : ℝ → ℝ} {L : ℝ}
    (hF : Tendsto F atTop (𝓝 L)) :
    ∀ c > 0, ∀ᶠ x in atTop, ∀ y, x ≤ y → |F y - F x| < c := by
  intro c hc
  rw [Metric.tendsto_atTop] at hF
  obtain ⟨N, hN⟩ := hF (c / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with x hx y hxy
  have h1 := hN x hx
  have h2 := hN y (le_trans hx hxy)
  rw [Real.dist_eq] at h1 h2
  linarith [abs_sub_le (F y) L (F x), abs_sub_comm L (F x), abs_sub_comm L (F y)]

/-- The integrand `(f t - t) / t ^ 2` is integrable over `Ioc a b` whenever
`1 ≤ a`, using monotonicity of `f` restricted to `[1, ∞)`. -/
private lemma integrableOn_g_Ioc (f : ℝ → ℝ) (hf : MonotoneOn f (Ici 1))
    (a b : ℝ) (ha : 1 ≤ a) :
    IntegrableOn (fun t => (f t - t) / t ^ 2) (Ioc a b) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hsub : Icc a b ⊆ Ici 1 := fun x hx => mem_Ici.mpr (le_trans ha hx.1)
  have h1 : IntegrableOn f (Icc a b) :=
    (hf.mono hsub).integrableOn_isCompact isCompact_Icc
  have h2 : (fun t => (f t - t) / t ^ 2) = fun t => (f t - t) * (1 / t ^ 2) := by
    ext t
    ring
  rw [h2]
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  exact (h1.sub
    (continuousOn_id.integrableOn_compact isCompact_Icc)).mul_continuousOn
    (ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      (fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha0 hx.1))))
    isCompact_Icc

/-- Splitting a set integral over adjacent `Ioc` intervals. -/
private lemma integral_Ioc_split' {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (hg1 : IntegrableOn g (Ioc a b))
    (hg2 : IntegrableOn g (Ioc b c)) :
    ∫ x in Ioc a c, g x = (∫ x in Ioc a b, g x) + (∫ x in Ioc b c, g x) := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc]
  exact setIntegral_union
    (by rw [disjoint_left]; intro x hx1 hx2; exact lt_irrefl b (lt_of_lt_of_le hx2.1 hx1.2))
    measurableSet_Ioc hg1 hg2

/-- Integral of a constant over an `Ioc` interval. -/
private lemma integral_const_Ioc {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∫ _ in Ioc a b, c = c * (b - a) := by
  simp only [setIntegral_const, smul_eq_mul, mul_comm]
  congr 1
  simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ b - a)]

/-- Upper one-sided bound: eventually `f x < lam * x` for every `lam > 1`. -/
private lemma upper_bound_of_convergent_integral (f : ℝ → ℝ)
    (hf : MonotoneOn f (Ici 1)) {L : ℝ}
    (hL : Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L))
    {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ x in atTop, f x < lam * x := by
  set c₀ := (lam - 1) ^ 2 / (lam + 1) ^ 2 with hc₀_def
  have hlam_sub_pos : 0 < lam - 1 := by linarith
  have hlam_add_pos : 0 < lam + 1 := by linarith
  have hc₀_pos : 0 < c₀ :=
    div_pos (sq_pos_of_pos hlam_sub_pos) (sq_pos_of_pos hlam_add_pos)
  set lam' := (lam + 1) / 2 with hlam'_def
  have hlam'_gt1 : 1 < lam' := by linarith
  have hlam'_lt_lam : lam' < lam := by linarith
  set g := fun t => (f t - t) / t ^ 2 with hg_def
  set F := fun x => ∫ t in Ioc 1 x, g t with hF_def
  have hcauchy := cauchy_of_tendsto hL c₀ hc₀_pos
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ x in atTop, lam * x ≤ f x :=
    hcon.mono (fun x hx => not_lt.mp hx)
  have h_combined := (hcauchy.and (eventually_ge_atTop 1)).and_frequently hfreq
  obtain ⟨_, ⟨⟨hb_cauchy, hb1⟩, hb_large⟩⟩ :=
    h_combined.forall_exists_of_atTop 0 |>.choose_spec
  set b := (h_combined.forall_exists_of_atTop 0).choose with hb_def
  have hb_pos : 0 < b := by linarith
  have hlam'b_ge_b : b ≤ lam' * b :=
    le_mul_of_one_le_left (le_of_lt hb_pos) (le_of_lt hlam'_gt1)
  have hint : IntegrableOn g (Ioc b (lam' * b)) :=
    integrableOn_g_Ioc f hf b (lam' * b) hb1
  have hconst_int :
      IntegrableOn (fun _ => (lam - 1) / (2 * lam' ^ 2 * b)) (Ioc b (lam' * b)) := by
    apply integrableOn_const (hs := ?_)
    exact ((measure_mono Ioc_subset_Icc_self).trans_lt
      isCompact_Icc.measure_lt_top).ne
  have hpw : ∀ t ∈ Ioc b (lam' * b), (lam - 1) / (2 * lam' ^ 2 * b) ≤ g t := by
    intro t ht
    have htb : b < t := ht.1
    have htub : t ≤ lam' * b := ht.2
    have ht_pos : 0 < t := lt_trans hb_pos htb
    have hb_mem : b ∈ Ici (1 : ℝ) := mem_Ici.mpr hb1
    have ht_mem : t ∈ Ici (1 : ℝ) := mem_Ici.mpr (le_trans hb1 (le_of_lt htb))
    have hft : lam * b ≤ f t := le_trans hb_large (hf hb_mem ht_mem (le_of_lt htb))
    have h_num : (lam - 1) / 2 * b ≤ f t - t := by
      have hcalc : (lam - lam') * b = (lam - 1) / 2 * b := by rw [hlam'_def]; ring
      nlinarith
    have h_denom : t ^ 2 ≤ (lam' * b) ^ 2 := sq_le_sq' (by linarith) htub
    change (lam - 1) / (2 * lam' ^ 2 * b) ≤ (f t - t) / t ^ 2
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * lam' ^ 2 * b) (by positivity : 0 < t ^ 2)]
    calc (lam - 1) * t ^ 2 ≤ (lam - 1) * (lam' * b) ^ 2 :=
            mul_le_mul_of_nonneg_left h_denom (by linarith)
      _ = 2 * lam' ^ 2 * b * ((lam - 1) / 2 * b) := by ring
      _ ≤ 2 * lam' ^ 2 * b * (f t - t) :=
            mul_le_mul_of_nonneg_left h_num (by positivity)
      _ = (f t - t) * (2 * lam' ^ 2 * b) := by ring
  have h_lower :
      (lam - 1) / (2 * lam' ^ 2 * b) * ((lam' - 1) * b) ≤
        ∫ t in Ioc b (lam' * b), g t := by
    calc (lam - 1) / (2 * lam' ^ 2 * b) * ((lam' - 1) * b)
        = ∫ _ in Ioc b (lam' * b), (lam - 1) / (2 * lam' ^ 2 * b) := by
            rw [integral_const_Ioc hlam'b_ge_b]; ring
      _ ≤ ∫ t in Ioc b (lam' * b), g t :=
            setIntegral_mono_on hconst_int hint measurableSet_Ioc hpw
  have h_product : (lam - 1) / (2 * lam' ^ 2 * b) * ((lam' - 1) * b) = c₀ := by
    rw [hlam'_def, hc₀_def]; field_simp; ring
  have h_integral_ge_c₀ : c₀ ≤ ∫ t in Ioc b (lam' * b), g t := by linarith
  have h_split : F (lam' * b) = F b + ∫ t in Ioc b (lam' * b), g t := by
    change ∫ t in Ioc 1 (lam' * b), g t =
      (∫ t in Ioc 1 b, g t) + ∫ t in Ioc b (lam' * b), g t
    exact integral_Ioc_split' hb1 hlam'b_ge_b
      (integrableOn_g_Ioc f hf 1 b le_rfl) hint
  have hcauchy_b := hb_cauchy (lam' * b) hlam'b_ge_b
  have h_tail_small : |∫ t in Ioc b (lam' * b), g t| < c₀ := by
    have heq : ∫ t in Ioc b (lam' * b), g t = F (lam' * b) - F b := by linarith
    rw [heq]; exact hcauchy_b
  have h_integral_nonneg : 0 ≤ ∫ t in Ioc b (lam' * b), g t :=
    le_trans (le_of_lt hc₀_pos) h_integral_ge_c₀
  linarith [abs_of_nonneg h_integral_nonneg]

/-- Lower one-sided bound: eventually `x / lam < f x` for every `lam > 1`. -/
private lemma lower_bound_of_convergent_integral (f : ℝ → ℝ)
    (hf : MonotoneOn f (Ici 1)) {L : ℝ}
    (hL : Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L))
    {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ x in atTop, x / lam < f x := by
  set c₀ := (lam - 1) ^ 2 / (4 * lam ^ 2) with hc₀_def
  set mu := (lam + 1) / (2 * lam) with hmu_def
  have hlam_pos : 0 < lam := by linarith
  have hc₀_pos : 0 < c₀ := div_pos (sq_pos_of_pos (by linarith)) (by positivity)
  have hmu_pos : 0 < mu := by positivity
  have hmu_lt1 : mu < 1 := by
    rw [hmu_def]; rw [div_lt_one (by positivity)]; linarith
  set g := fun t => (f t - t) / t ^ 2 with hg_def
  set F := fun x => ∫ t in Ioc 1 x, g t with hF_def
  have hcauchy := cauchy_of_tendsto hL c₀ hc₀_pos
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ x in atTop, f x ≤ x / lam :=
    hcon.mono (fun x hx => not_lt.mp hx)
  have hcauchy_mu : ∀ᶠ b in atTop, ∀ y, mu * b ≤ y → |F y - F (mu * b)| < c₀ := by
    have htend : Tendsto (fun b => mu * b) atTop atTop :=
      Filter.tendsto_atTop_atTop_of_monotone
        (fun a b hab => mul_le_mul_of_nonneg_left hab (le_of_lt hmu_pos))
        (fun b => ⟨b / mu, by
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hmu_pos)]⟩)
    exact htend.eventually hcauchy
  have h_combined := (hcauchy_mu.and (eventually_ge_atTop lam)).and_frequently hfreq
  obtain ⟨_, ⟨⟨hb_cauchy_mu, hb_lam⟩, hb_small⟩⟩ :=
    h_combined.forall_exists_of_atTop 0 |>.choose_spec
  set b := (h_combined.forall_exists_of_atTop 0).choose with hb_def_eq
  have hb_pos : 0 < b := by linarith
  have hmub_pos : 0 < mu * b := mul_pos hmu_pos hb_pos
  have hmub_le_b : mu * b ≤ b :=
    mul_le_of_le_one_left (le_of_lt hb_pos) (le_of_lt hmu_lt1)
  have hmub_ge1 : 1 ≤ mu * b := by
    have h1 : (1 : ℝ) ≤ (lam + 1) / 2 := by linarith
    have h2 : (lam + 1) / 2 = mu * lam := by rw [hmu_def]; field_simp
    calc (1 : ℝ) ≤ mu * lam := by linarith
      _ ≤ mu * b := mul_le_mul_of_nonneg_left hb_lam (le_of_lt hmu_pos)
  have hint : IntegrableOn g (Ioc (mu * b) b) :=
    integrableOn_g_Ioc f hf (mu * b) b hmub_ge1
  have hconst_int :
      IntegrableOn (fun _ => -((lam - 1) / (2 * lam * b))) (Ioc (mu * b) b) := by
    apply integrableOn_const (hs := ?_)
    exact ((measure_mono Ioc_subset_Icc_self).trans_lt
      isCompact_Icc.measure_lt_top).ne
  have hpw : ∀ t ∈ Ioc (mu * b) b, g t ≤ -((lam - 1) / (2 * lam * b)) := by
    intro t ht
    have htl : mu * b < t := ht.1
    have htu : t ≤ b := ht.2
    have ht_pos : 0 < t := lt_trans hmub_pos htl
    have ht_mem : t ∈ Ici (1 : ℝ) := mem_Ici.mpr (le_trans hmub_ge1 (le_of_lt htl))
    have hb_mem : b ∈ Ici (1 : ℝ) := mem_Ici.mpr (le_trans hmub_ge1 hmub_le_b)
    have hft : f t ≤ b / lam := le_trans (hf ht_mem hb_mem htu) hb_small
    change (f t - t) / t ^ 2 ≤ -((lam - 1) / (2 * lam * b))
    rw [show -((lam - 1) / (2 * lam * b)) = -(lam - 1) / (2 * lam * b) from by ring]
    rw [div_le_div_iff₀ (sq_pos_of_pos ht_pos)
      (mul_pos (mul_pos two_pos hlam_pos) hb_pos)]
    have h1 : (f t - t) * (2 * lam) ≤ -(b * (lam - 1)) := by
      have hft_sub : f t - t ≤ b / lam - mu * b := by linarith
      have heq : (b / lam - mu * b) * (2 * lam) = -(b * (lam - 1)) := by
        rw [hmu_def]; field_simp; ring
      nlinarith
    have h2 : (f t - t) * (2 * lam * b) ≤ -(lam - 1) * b ^ 2 := by
      nlinarith [sq_nonneg b]
    linarith [mul_le_mul_of_nonpos_left (sq_le_sq' (show -b ≤ t by linarith) htu)
              (show -(lam - 1) ≤ 0 by linarith)]
  have h_upper : ∫ t in Ioc (mu * b) b, g t ≤ -c₀ := by
    have h1 : ∫ t in Ioc (mu * b) b, g t ≤
        ∫ _ in Ioc (mu * b) b, -((lam - 1) / (2 * lam * b)) :=
      setIntegral_mono_on hint hconst_int measurableSet_Ioc hpw
    have h2 : ∫ _ in Ioc (mu * b) b, -((lam - 1) / (2 * lam * b)) =
        -((lam - 1) / (2 * lam * b)) * (b - mu * b) :=
      integral_const_Ioc hmub_le_b _
    have h3 : -((lam - 1) / (2 * lam * b)) * (b - mu * b) = -c₀ := by
      rw [hmu_def, hc₀_def]; field_simp; ring
    linarith
  have h_split : F b = F (mu * b) + ∫ t in Ioc (mu * b) b, g t := by
    change ∫ t in Ioc 1 b, g t =
      (∫ t in Ioc 1 (mu * b), g t) + ∫ t in Ioc (mu * b) b, g t
    exact integral_Ioc_split' hmub_ge1 hmub_le_b
      (integrableOn_g_Ioc f hf 1 (mu * b) le_rfl) hint
  have hcauchy_b := hb_cauchy_mu b hmub_le_b
  have h_eq : ∫ t in Ioc (mu * b) b, g t = F b - F (mu * b) := by linarith
  have h_tail : |∫ t in Ioc (mu * b) b, g t| < c₀ := by rw [h_eq]; exact hcauchy_b
  have h_nonpos : ∫ t in Ioc (mu * b) b, g t ≤ 0 := le_trans h_upper (by linarith)
  rw [abs_of_nonpos h_nonpos] at h_tail
  linarith

/-- Integral criterion for asymptotic equivalence to the identity (ATLAS
`NumberTheoryI` Lemma 16.8): a function nondecreasing on `[1, ∞)` whose
normalized deviation `(f t - t) / t ^ 2` has convergent integral over
`[1, x]` satisfies `f x ~ x`. Monotonicity below `1` is not needed. -/
theorem isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq
    (f : ℝ → ℝ) (hf : MonotoneOn f (Ici 1))
    (hconv : ∃ L : ℝ,
      Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2)
        atTop (𝓝 L)) :
    f ~[atTop] (fun x : ℝ => x) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx; exact ne_of_gt hx)]
  obtain ⟨L, hL⟩ := hconv
  rw [tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a ≤ 0
    · have h := lower_bound_of_convergent_integral f hf hL
        (show (1 : ℝ) < 2 by norm_num)
      filter_upwards [h, eventually_gt_atTop 0] with x hfx hx
      have hfx_pos : 0 < f x := by linarith [show (0 : ℝ) < x / 2 by linarith]
      change a < f x / x
      calc a ≤ 0 := ha0
        _ < f x / x := div_pos hfx_pos hx
    · push Not at ha0
      have hlam : 1 < 1 / a := by rw [lt_div_iff₀ ha0]; linarith
      have h := lower_bound_of_convergent_integral f hf hL hlam
      filter_upwards [h, eventually_gt_atTop 0] with x hfx hx
      change a < f x / x
      rw [lt_div_iff₀ hx]
      have hxx : x / (1 / a) = a * x := by field_simp
      linarith
  · intro a ha
    have h := upper_bound_of_convergent_integral f hf hL ha
    filter_upwards [h, eventually_gt_atTop 0] with x hfx hx
    change f x / x < a
    rw [div_lt_iff₀ hx]
    linarith

end Asymptotics
end
end

/- TauberianPort.MathlibExt.Analysis.LaplaceTransform.Basic -/
section
/-!
# One-sided Laplace transform

This file defines the convergence predicate, the one-sided Laplace transform, and the
packaged `HasLaplace` relation, following Mathlib's `MellinConvergent` / `mellin` /
`HasMellin` pattern with the domain restricted to the open ray `Set.Ioi 0`.

This stage provides only the basic definitions; further API is out of scope.

## Main definitions

* `LaplaceConvergent`
* `laplace`
* `HasLaplace`
-/

section
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Laplace convergence: the one-sided Laplace integrand is integrable on `Set.Ioi 0`.

ATLAS `NumberTheoryI` Definition 16.9 introduces the Laplace transform for real-valued
functions; here functions are complex-valued (or complex Banach-valued), and the source's
real-valued case is covered by coercion. -/
def LaplaceConvergent (f : ℝ → E) (s : ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t) (Set.Ioi 0)

/-- One-sided Laplace transform, defined unconditionally as the set integral over
`Set.Ioi 0`; no convergence hypothesis is imposed here (see `LaplaceConvergent`). -/
noncomputable def laplace (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Set.Ioi 0, Complex.exp (-s * (t : ℂ)) • f t

/-- `HasLaplace f s v` packages Laplace convergence at `s` with the value
`laplace f s`. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (v : E) : Prop :=
  LaplaceConvergent f s ∧ laplace f s = v
end
end

/- TauberianPort.MathlibExt.Analysis.LaplaceTransform.ExponentialBound -/
section
/-!
# Laplace convergence and holomorphy from exponential bounds

Let `f : ℝ → E` satisfy `‖f t‖ ≤ C * Real.exp (a * t)` for `t ≥ 0`.
This file shows Laplace convergence for `s.re > a` and holomorphy on
`{s | a < s.re}`. Measurability on `volume.restrict (Set.Ioi 0)` is an
explicit hypothesis: Lean's totalized integral would otherwise make the
Laplace integral vanish on the nonmeasurable branch, giving vacuous
holomorphy. Only the genuine measurable branch is proved here.

## ATLAS source correspondence

ATLAS item `NumberTheoryI:N320` (ATLAS Definition 16.9), defined in
`Atlas/NumberTheoryI/targets.yaml` (lines 2242--2248), with implementation/proof
context in `Atlas/NumberTheoryI/code/LaplaceTransform.lean` (lines 15--16) and
`Atlas/NumberTheoryI/code/PNT.lean` (lines 314--444). Authored by Muse Spark 1.3.

The motivating source is Andrew V. Sutherland, *18.785 Number Theory I*, Lecture 16,
[Lemma 16.10](https://math.mit.edu/classes/18.785/2021fa/LectureNotes16.pdf#page=6).
It invokes Definition 16.9: if a real-valued function has exponential growth
`h(t) = O(exp(c t))`, then its positive-ray Laplace transform is holomorphic on
`Re(s) > c`.  For `h(t) = ϑ(exp t)`, Lemma 16.7 supplies `h(t) = O(exp t)`,
giving holomorphy on `Re(s) > 1`.

Source-to-API map: ATLAS N320 is implemented by
`laplaceConvergent_of_isBigO_exp` (convergence for `a < s.re`) and
`differentiableOn_laplace_of_isBigO_exp` (holomorphy on `{s | a < s.re}`).
These two APIs together are not a literal full target; they are a corrected,
strengthened-premise formalization of N320's intended convergence/holomorphy
claim. Both carry the strengthened assumption `LocallyIntegrableOn f (Set.Ici 0)`,
which explicitly repairs the missing endpoint condition, since the source's
open-positive-ray (piecewise continuity on `ℝ_{>0}`) wording does not control the
singularity at zero. This is not a literal proof of the under-specified source
wording.

The public theorems below isolate and strengthen precisely that analytic step.

* `laplaceConvergent_of_norm_le_exp` replaces big-O notation by an explicit bound
  `‖f t‖ ≤ C exp(a t)` for `t ≥ 0` and proves convergence whenever `a < s.re`.
* `differentiableOn_laplace_of_norm_le_exp` proves holomorphy on the full half-plane
  `{s | a < s.re}` by dominated differentiation.
* `laplaceConvergent_of_isBigO_exp` and `differentiableOn_laplace_of_isBigO_exp`
  are the source-shaped endpoints: from `LocallyIntegrableOn f (Set.Ici 0)` and an
  eventual bound `f =O[atTop] exp (a * t)` they prove convergence and holomorphy.
  The `Ici 0` hypothesis does not restate the source: ATLAS's piecewise continuity
  on `ℝ_{>0}` does not supply near-zero integrability. The counterexample
  `f(t) = 1/t` is piecewise continuous (indeed continuous) on `ℝ_{>0}`, locally
  integrable on `(0, ∞)`, and `O(1)` at infinity, but not integrable at `0`, so
  the open-ray wording alone would be insufficient.

The Lean result allows Banach-space-valued functions `f : ℝ → E`, a genuine
generalization of the source's real-valued statement.  It explicitly assumes
`AEStronglyMeasurable f` on `Set.Ioi 0`, whereas the source's piecewise continuity
implies this measurability.  The positive ray and strict half-plane are unchanged.
The separate prime-sum identity in Lemma 16.10 is handled in `LaplaceTheta`; this module
provides its exponential-bound/holomorphy input.
-/

section
open MeasureTheory Set Real Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma integrableOn_mul_exp_neg_Ioi' {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-r * t))
      (Set.Ioi (0 : ℝ)) := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  apply integrable_of_isBigO_exp_neg hr2
  · exact (continuous_id.mul
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).continuousOn
  · rw [Asymptotics.isBigO_iff]
    use 2 / r
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht (Real.exp_nonneg _))]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hle : t ≤ (2 / r) * Real.exp (r / 2 * t) :=
      calc t = (2 / r) * (r / 2 * t) := by field_simp
        _ ≤ (2 / r) * Real.exp (r / 2 * t) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [Real.add_one_le_exp (r / 2 * t)]
    calc t * Real.exp (-r * t)
        = t * (Real.exp (-(r / 2) * t) *
          Real.exp (-(r / 2) * t)) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
      _ ≤ (2 / r) * Real.exp (r / 2 * t) *
            (Real.exp (-(r / 2) * t) *
              Real.exp (-(r / 2) * t)) := by
          apply mul_le_mul_of_nonneg_right hle
          exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = (2 / r) * (Real.exp (r / 2 * t) *
            Real.exp (-(r / 2) * t)) *
            Real.exp (-(r / 2) * t) := by ring
      _ = 2 / r * Real.exp (-(r / 2) * t) := by
          rw [← Real.exp_add]
          simp only [neg_mul, add_neg_cancel, Real.exp_zero]
          ring

/-- Laplace convergence from an exponential norm bound. -/
theorem laplaceConvergent_of_norm_le_exp
    (f : ℝ → E) (a C : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t))
    {s : ℂ} (hs : a < s.re) :
    LaplaceConvergent f s := by
  unfold LaplaceConvergent
  have hpos : 0 < s.re - a := sub_pos.mpr hs
  have hbound_int :
      IntegrableOn (fun t : ℝ => C * Real.exp (-(s.re - a) * t))
        (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 hpos).const_mul C
  have hexp : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hexp.smul hf
  apply Integrable.mono hbound_int hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  apply ae_of_all
  intro t ht
  simp only [Set.mem_Ioi] at ht
  rw [norm_smul, Complex.norm_exp]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
  rw [hre]
  calc Real.exp (-s.re * t) * ‖f t‖
      ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
        mul_le_mul_of_nonneg_left (hbound t (le_of_lt ht))
          (Real.exp_nonneg _)
    _ = C * Real.exp (-(s.re - a) * t) := by
        rw [show -(s.re - a) * t = -s.re * t + a * t from by ring]
        rw [Real.exp_add]
        ring
    _ ≤ ‖C * Real.exp (-(s.re - a) * t)‖ := by
        rw [Real.norm_of_nonneg
          (mul_nonneg hC (Real.exp_nonneg _))]

/-- Laplace convergence from a source-shaped eventual exponential Big-O bound.

This is the first half of a corrected, strengthened-premise formalization of the
ATLAS N320 intended convergence claim: a locally integrable function with
`f =O[atTop] exp (a * t)` has a convergent Laplace transform for `a < s.re`.
The `LocallyIntegrableOn f (Set.Ici 0)` premise explicitly repairs the missing
endpoint condition: ATLAS's piecewise continuity on `ℝ_{>0}` does not supply
near-zero integrability (counterexample `f(t) = 1/t`); the tail is handled by the
asymptotic integrability API. This is not a literal proof of the under-specified
source wording. -/
theorem laplaceConvergent_of_isBigO_exp
    (f : ℝ → E) (a : ℝ)
    (hloc : LocallyIntegrableOn f (Set.Ici 0))
    (ho : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t)))
    {s : ℂ} (hs : a < s.re) :
    LaplaceConvergent f s := by
  unfold LaplaceConvergent
  set r : ℝ := s.re - a with hr_def
  have hr : 0 < r := sub_pos.mpr hs
  have hcont_exp : Continuous (fun t : ℝ => Complex.exp (-s * (t : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hF_loc : LocallyIntegrableOn
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t) (Set.Ici 0) :=
    hloc.continuousOn_smul isClosed_Ici.isLocallyClosed hcont_exp.continuousOn
  have hg_ioi : IntegrableOn (fun t : ℝ => Real.exp (-r * t))
      (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 hr
  have htail : IntegrableAtFilter (fun t : ℝ => Real.exp (-r * t))
      Filter.atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp hg_ioi).1
  have hbig : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
      =O[Filter.atTop] (fun t : ℝ => Real.exp (-r * t)) := by
    rw [Asymptotics.isBigO_iff] at ho ⊢
    obtain ⟨C, hC⟩ := ho
    refine ⟨C, ?_⟩
    filter_upwards [hC] with t ht
    rw [norm_smul, Complex.norm_exp]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-s.re * t) * ‖f t‖
        ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
          mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
      _ = C * Real.exp (-r * t) := by
          rw [hr_def, show -((s.re - a)) * t = -s.re * t + a * t from by ring]
          rw [Real.exp_add]
          ring
  have hIci : IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t)
      (Set.Ici (0 : ℝ)) :=
    hF_loc.integrableOn_of_isBigO_atTop hbig htail
  exact hIci.mono_set Set.Ioi_subset_Ici_self

/-- Holomorphy of the Laplace transform from an exponential bound. -/
theorem differentiableOn_laplace_of_norm_le_exp
    (f : ℝ → E) (a C : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t))
    [CompleteSpace E] :
    DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
  intro s₀ hs₀
  simp only [Set.mem_ofPred_eq] at hs₀
  set μ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ_def
  set δ := (s₀.re - a) / 2 with hδ_def
  set b := (s₀.re + a) / 2 with hb_def
  have hδ : 0 < δ := by
    simp only [hδ_def]
    linarith
  have hba : 0 < b - a := by
    simp only [hb_def]
    linarith
  have hball_re : ∀ z ∈ Metric.ball s₀ δ, b ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have habs_re : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hlt : |z.re - s₀.re| < δ := lt_of_le_of_lt habs_re hz
    have hmem := abs_lt.mp hlt
    simp only [hb_def, hδ_def] at hmem ⊢
    linarith [hmem.1, hmem.2]
  have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t) μ := by
    intro z
    have hexp : AEStronglyMeasurable
        (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hexp.smul hf
  have hF_int : Integrable
      (fun t : ℝ => Complex.exp (-s₀ * (t : ℂ)) • f t) μ := by
    have hconv := laplaceConvergent_of_norm_le_exp f a C hf hC hbound
      (show a < s₀.re from hs₀)
    unfold LaplaceConvergent at hconv
    rw [hμ_def]
    exact hconv
  have hmeas_deriv : AEStronglyMeasurable
      (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) • f t)
      μ := by
    have hcont : Continuous
        (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) :
          ℝ → ℂ) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.neg
      · exact Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hcont.aestronglyMeasurable.smul hf
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * (t : ℂ)) • f t)
    (F' := fun (s : ℂ) (t : ℝ) =>
      (-(t : ℂ) * Complex.exp (-s * (t : ℂ))) • f t)
    (bound := fun t : ℝ => C * |t| * Real.exp (-(b - a) * t))
    (s := Metric.ball s₀ δ)
    (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hδ)
    (Filter.Eventually.of_forall (fun z => hmeas_F z))
    hF_int
    hmeas_deriv
    ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht z hz
    simp only [Set.mem_Ioi] at ht
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    have hht : ‖f t‖ ≤ C * Real.exp (a * t) := hbound t (le_of_lt ht)
    have hb : b ≤ z.re := hball_re z hz
    calc |t| * Real.exp (-z.re * t) * ‖f t‖
        ≤ |t| * Real.exp (-b * t) * ‖f t‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp_of_le
              (mul_le_mul_of_nonneg_right (neg_le_neg hb)
                (le_of_lt ht)))
            (abs_nonneg t)
      _ ≤ |t| * Real.exp (-b * t) * (C * Real.exp (a * t)) := by
          apply mul_le_mul_of_nonneg_left hht
          exact mul_nonneg (abs_nonneg t) (Real.exp_nonneg _)
      _ = C * |t| * Real.exp (-(b - a) * t) := by
          rw [show -(b - a) * t = -b * t + a * t from by ring]
          rw [Real.exp_add]
          ring
  · rw [hμ_def]
    change IntegrableOn
      (fun t : ℝ => C * |t| * Real.exp (-(b - a) * t))
      (Set.Ioi (0 : ℝ))
    have h1 : IntegrableOn
        (fun t : ℝ => C * (t * Real.exp (-(b - a) * t)))
        (Set.Ioi (0 : ℝ)) :=
      (integrableOn_mul_exp_neg_Ioi' hba).const_mul C
    apply h1.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [Set.mem_Ioi] at ht
    change C * (t * Real.exp (-(b - a) * t)) =
      C * |t| * Real.exp (-(b - a) * t)
    rw [abs_of_pos ht]
    ring
  · apply ae_of_all
    intro t z _
    have h1 : HasDerivAt (fun s : ℂ => -s * (t : ℂ)) (-(t : ℂ)) z := by
      have hder := (hasDerivAt_neg (𝕜 := ℂ) z).mul_const (t : ℂ)
      simp only [neg_one_mul] at hder
      exact hder
    have h2 := h1.cexp.smul_const (f t)
    have heq : Complex.exp (-z * (t : ℂ)) * (-(t : ℂ)) =
        -(t : ℂ) * Complex.exp (-z * (t : ℂ)) := mul_comm _ _
    rw [heq] at h2
    exact h2

/-- Holomorphy of the Laplace transform from an eventual exponential Big-O bound.

This completes the source-shaped endpoint as a corrected, strengthened-premise
formalization of the ATLAS N320 intended holomorphy claim: with
`LocallyIntegrableOn f (Set.Ici 0)` explicitly repairing the missing endpoint
condition, an eventual bound `f =O[atTop] exp (a * t)` gives holomorphy on
`{s | a < s.re}`. ATLAS's piecewise continuity on `ℝ_{>0}` does not supply
near-zero integrability (counterexample `f(t) = 1/t`). The `Ici 0` hypothesis is
load-bearing: local integrability on the open ray plus an `atTop` bound would not
suffice. This is not a literal proof of the under-specified source wording. -/
theorem differentiableOn_laplace_of_isBigO_exp
    (f : ℝ → E) (a : ℝ)
    (hf : LocallyIntegrableOn f (Set.Ici 0))
    (hO : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t)))
    [CompleteSpace E] :
    DifferentiableOn ℂ (laplace f) {s | a < s.re} := by
  intro s₀ hs₀
  simp only [Set.mem_ofPred_eq] at hs₀
  set μ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ_def
  set δ := (s₀.re - a) / 2 with hδ_def
  set b := (s₀.re + a) / 2 with hb_def
  have hδ : 0 < δ := by
    simp only [hδ_def]
    linarith
  have hab : a < b := by
    simp only [hb_def]
    linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  have hball_re : ∀ z ∈ Metric.ball s₀ δ, b ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have habs_re : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
      rw [← Complex.sub_re]
      exact Complex.abs_re_le_norm _
    have hlt : |z.re - s₀.re| < δ := lt_of_le_of_lt habs_re hz
    have hmem := abs_lt.mp hlt
    simp only [hb_def, hδ_def] at hmem ⊢
    linarith [hmem.1, hmem.2]
  have hfIoi : LocallyIntegrableOn f (Set.Ioi (0 : ℝ)) :=
    hf.mono_set Set.Ioi_subset_Ici_self
  have hmeas_F : ∀ z : ℂ, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t) μ := by
    intro z
    have hexp : AEStronglyMeasurable
        (fun t : ℝ => Complex.exp (-z * (t : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hexp.smul hfIoi.aestronglyMeasurable
  have hF_int : Integrable
      (fun t : ℝ => Complex.exp (-s₀ * (t : ℂ)) • f t) μ := by
    have hconv := laplaceConvergent_of_isBigO_exp f a hf hO
      (show a < s₀.re from hs₀)
    unfold LaplaceConvergent at hconv
    rw [hμ_def]
    exact hconv
  have hmeas_deriv : AEStronglyMeasurable
      (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) • f t)
      μ := by
    have hcont : Continuous
        (fun t : ℝ => (-(t : ℂ) * Complex.exp (-s₀ * (t : ℂ))) :
          ℝ → ℂ) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.neg
      · exact Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)
    rw [hμ_def]
    exact hcont.aestronglyMeasurable.smul hfIoi.aestronglyMeasurable
  have hB_loc : LocallyIntegrableOn
      (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖) (Set.Ici 0) := by
    have hcont : ContinuousOn (fun t : ℝ => |t| * Real.exp (-b * t))
        (Set.Ici (0 : ℝ)) :=
      (continuous_abs.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).continuousOn
    exact hf.norm.continuousOn_mul hcont isClosed_Ici.isLocallyClosed
  have hcomp_int : IntegrableAtFilter
      (fun t : ℝ => t * Real.exp (-(b - a) * t)) Filter.atTop volume :=
    (integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp
      (integrableOn_mul_exp_neg_Ioi' hba)).1
  have hbig : (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖)
      =O[Filter.atTop]
      (fun t : ℝ => t * Real.exp (-(b - a) * t)) := by
    rw [Asymptotics.isBigO_iff] at hO ⊢
    obtain ⟨C, hC⟩ := hO
    refine ⟨C, ?_⟩
    filter_upwards [hC, Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at ht
    show ‖|t| * Real.exp (-b * t) * ‖f t‖‖ ≤
      C * ‖t * Real.exp (-(b - a) * t)‖
    have hnn : 0 ≤ |t| * Real.exp (-b * t) * ‖f t‖ :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
        (norm_nonneg _)
    have hnn2 : 0 ≤ t * Real.exp (-(b - a) * t) :=
      mul_nonneg ht0 (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn,
      Real.norm_eq_abs, abs_of_nonneg hnn2, abs_of_nonneg ht0]
    calc t * Real.exp (-b * t) * ‖f t‖
        ≤ t * Real.exp (-b * t) * (C * Real.exp (a * t)) :=
          mul_le_mul_of_nonneg_left ht
            (mul_nonneg ht0 (Real.exp_nonneg _))
      _ = C * (t * Real.exp (-(b - a) * t)) := by
          rw [show -(b - a) * t = -b * t + a * t from by ring]
          rw [Real.exp_add]
          ring
  have hbound_int : Integrable
      (fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖) μ := by
    rw [hμ_def]
    exact (hB_loc.integrableOn_of_isBigO_atTop hbig hcomp_int).mono_set
      Set.Ioi_subset_Ici_self
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (-s * (t : ℂ)) • f t)
    (F' := fun (s : ℂ) (t : ℝ) =>
      (-(t : ℂ) * Complex.exp (-s * (t : ℂ))) • f t)
    (bound := fun t : ℝ => |t| * Real.exp (-b * t) * ‖f t‖)
    (s := Metric.ball s₀ δ)
    (x₀ := s₀)
    (Metric.ball_mem_nhds s₀ hδ)
    (Filter.Eventually.of_forall (fun z => hmeas_F z))
    hF_int
    hmeas_deriv
    ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply ae_of_all
    intro t ht z hz
    simp only [Set.mem_Ioi] at ht
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (t : ℂ)).re = -z.re * t := by
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [hre]
    have hb : b ≤ z.re := hball_re z hz
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp_of_le
          (mul_le_mul_of_nonneg_right (neg_le_neg hb) (le_of_lt ht)))
        (abs_nonneg t))
      (norm_nonneg _)
  · exact hbound_int
  · apply ae_of_all
    intro t z _
    have h1 : HasDerivAt (fun s : ℂ => -s * (t : ℂ)) (-(t : ℂ)) z := by
      have hder := (hasDerivAt_neg (𝕜 := ℂ) z).mul_const (t : ℂ)
      simp only [neg_one_mul] at hder
      exact hder
    have h2 := h1.cexp.smul_const (f t)
    have heq : Complex.exp (-z * (t : ℂ)) * (-(t : ℂ)) =
        -(t : ℂ) * Complex.exp (-z * (t : ℂ)) := mul_comm _ _
    rw [heq] at h2
    exact h2
end
end

/- TauberianPort.MathlibExt.Analysis.PerronKernel -/
section
/-
  Author: Muse Code powered by Meta Muse Spark
-/

/-!
# Truncated Perron kernel

The truncated Perron kernel
`perronKernel y c T = (1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt`, i.e.
`(1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds` with `ds = i dt`, with the explicit
error bound toward the step function:
`‖K - ind‖ ≤ y^c/(π T |log y|)`. Proved by closing the contour left
(`y > 1`) or right (`y < 1`): the entire averaging operator `E1`
splits off the pole, Cauchy kills the entire part, and the `1/s`
rectangle gives the residue; side estimates plus the `U → ∞` limit
give the bound.

Mathematical and proof source: the Apache-2.0 file
`proofs/Cathedral/White/Infrastructure/PerronKernel.lean` in `jrgochan/prime`,
commit `dd04f61337fb020855c12a97558f66608ab2f969`. The exact source results are
`perron_kernel_gt_one` (lines 703–740), `perron_kernel_lt_one` (lines 845–884),
and the unified `perron_kernel_bound` (lines 894–905); the pinned source file's
SHA-256 is
`a6191587cf9ef800679d06dd7016af6173b30ff19cce866fe707e3b195b64391`.
The contour architecture was adapted from that source. This module is a
substantial original rewrite for MathlibExt; no external Lean source was copied
verbatim. “Schoenfeld shape” in the PR title describes the bound's later
analytic-number-theory use, not a claim that Schoenfeld's paper contains this
exact theorem.
-/

section
namespace PerronKernel

open Complex Filter MeasureTheory Set intervalIntegral
open scoped Topology

/-- Truncated Perron kernel as a real integral over the segment. -/
noncomputable def perronKernel (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ in (-T)..T,
    (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)

/-- The kernel integrand is continuous when `0 < y` and `c ≠ 0`. -/
theorem continuous_perronKernel_integrand {y c : ℝ} (hy : 0 < y) (hc : c ≠ 0) :
    Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I)) := by
  have hbase : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
  have hexp : Continuous (fun t : ℝ => (c : ℂ) + t * Complex.I) :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hnum : Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + t * Complex.I)) :=
    hexp.const_cpow (Or.inl hbase)
  have hden : ∀ t : ℝ, (c : ℂ) + t * Complex.I ≠ 0 := by
    intro t h
    apply hc
    have := congrArg Complex.re h
    simpa using this
  exact hnum.div hexp hden

open Real in
/-- Scaled Real.arctan integral, via FTC on `Real.arctan (x / d)`. -/
theorem integral_div_add_sq {d a b : ℝ} (hc : d ≠ 0) :
    ∫ x : ℝ in a..b, d / (x ^ 2 + d ^ 2) = Real.arctan (b / d) - Real.arctan (a / d) := by
  have hsq : (0 : ℝ) < d ^ 2 := sq_pos_iff.mpr hc
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => Real.arctan (x / d)) (d / (x ^ 2 + d ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x / d) (1 / d) x := by
      have h := (hasDerivAt_id (x : ℝ)).mul_const (d⁻¹ : ℝ)
      simpa [div_eq_mul_inv, one_mul] using h
    have h2 := h1.arctan
    have hval : 1 / (1 + (x / d) ^ 2) * (1 / d) = d / (x ^ 2 + d ^ 2) := by
      field_simp
      ring
    rw [hval] at h2
    exact h2
  have hderivfun : deriv (fun x => Real.arctan (x / d)) = fun x => d / (x ^ 2 + d ^ 2) :=
    funext fun x => (hderiv x).deriv
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ (fun x => Real.arctan (x / d)) x :=
    fun x _ => (hderiv x).differentiableAt
  have hcont : ContinuousOn (fun x => d / (x ^ 2 + d ^ 2)) (uIcc a b) := by
    apply Continuous.continuousOn
    apply Continuous.div continuous_const (continuous_id.pow 2 |>.add continuous_const)
    intro x
    exact ne_of_gt (lt_of_lt_of_le hsq (le_add_of_nonneg_left (sq_nonneg x)))
  exact integral_deriv_eq_sub' _ hderivfun hdiff hcont

/-- Integral of an odd real function over a symmetric interval vanishes. -/
theorem odd_integral_eq_zero {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (T : ℝ) :
    ∫ x : ℝ in (-T)..T, f x = 0 := by
  have hcomp : ∫ x : ℝ in (-T)..T, f (-x) = ∫ x : ℝ in (-T)..T, f x := by
    have h := integral_comp_neg (a := -T) (b := T) (f := f)
    simp only [neg_neg] at h
    exact h
  have hodd' : ∫ x : ℝ in (-T)..T, f (-x) = -∫ x : ℝ in (-T)..T, f x := by
    simp only [hodd, intervalIntegral.integral_neg]
  linarith [hcomp, hodd']

open Real in
/-- Vertical side integral of `1/s`: `2 * Real.arctan (T / c)`. -/
theorem vertical_side_one_div {c T : ℝ} (hc : c ≠ 0) (hT : 0 ≤ T) :
    ∫ y : ℝ in (-T)..T, (1 : ℂ) / (c + y * Complex.I) = 2 * Real.arctan (T / c) := by
  have hab : -T ≤ T := by linarith
  have hcont : Continuous (fun y : ℝ => (1 : ℂ) / (c + y * Complex.I)) := by
    apply Continuous.div continuous_const
      (continuous_const.add (continuous_ofReal.mul continuous_const))
    intro y h
    apply hc
    have := congrArg Complex.re h
    simpa using this
  have hf : IntegrableOn (fun y : ℝ => (1 : ℂ) / (c + y * Complex.I)) (Ioc (-T) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcont.intervalIntegrable _ _)
  have hfi : IntervalIntegrable (fun y : ℝ => (1 : ℂ) / (c + y * Complex.I)) volume (-T) T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hf
  have hre_integral :
      (∫ y : ℝ in (-T)..T, (1 : ℂ) / (c + y * Complex.I)).re =
        ∫ y : ℝ in (-T)..T, ((1 : ℂ) / (c + y * Complex.I)).re := by
    simpa using (intervalIntegral.intervalIntegral_re hfi).symm
  have him_integral :
      (∫ y : ℝ in (-T)..T, (1 : ℂ) / (c + y * Complex.I)).im =
        ∫ y : ℝ in (-T)..T, ((1 : ℂ) / (c + y * Complex.I)).im := by
    simpa using (intervalIntegral.intervalIntegral_im hfi).symm
  have hre : ∀ y : ℝ, ((1 : ℂ) / (c + y * Complex.I)).re = c / (y ^ 2 + c ^ 2) := by
    intro y
    rw [Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_add_mul_I]
    field_simp
    ring
  have him : ∀ y : ℝ, ((1 : ℂ) / (c + y * Complex.I)).im = -y / (y ^ 2 + c ^ 2) := by
    intro y
    rw [Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.normSq_add_mul_I]
    field_simp
    ring
  apply Complex.ext
  · rw [hre_integral]
    simp only [hre, integral_div_add_sq hc]
    rw [show (-T) / c = -(T / c) by ring, arctan_neg]
    have h2re : (2 : ℂ).re = 2 := rfl
    have h2im : (2 : ℂ).im = 0 := rfl
    rw [Complex.mul_re, h2re, h2im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [him_integral]
    simp_rw [him]
    have hodd : ∀ y : ℝ, -(-y) / ((-y) ^ 2 + c ^ 2) = -(-y / (y ^ 2 + c ^ 2)) := by
      intro y
      rw [show (-y) ^ 2 = y ^ 2 by ring]
      ring
    have h0 := odd_integral_eq_zero (f := fun y => -y / (y ^ 2 + c ^ 2)) hodd T
    simp only [h0, Complex.mul_im, Complex.ofReal_im, show (2 : ℂ).im = 0 by rfl,
      mul_zero, zero_mul, add_zero]

open Real in
/-- Bottom-minus-top of `1/s`: `2i·Δarctan` (log parts cancel). -/
theorem horiz_diff_one_div {a b T : ℝ} (hT : T ≠ 0) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      = 2 * Complex.I * (Real.arctan (b / T) - Real.arctan (a / T)) := by
  have hcb : ∀ x : ℝ, ((x : ℂ) + -T * Complex.I) ≠ 0 := by
    intro x h
    apply hT
    have := congrArg Complex.im h
    simpa using this
  have hct : ∀ x : ℝ, ((x : ℂ) + T * Complex.I) ≠ 0 := by
    intro x h
    apply hT
    have := congrArg Complex.im h
    simpa using this
  have hcontb : Continuous (fun x : ℝ => (1 : ℂ) / (x + -T * Complex.I)) :=
    Continuous.div continuous_const
      (continuous_ofReal.add (continuous_const.mul continuous_const)) hcb
  have hcontt : Continuous (fun x : ℝ => (1 : ℂ) / (x + T * Complex.I)) :=
    Continuous.div continuous_const
      (continuous_ofReal.add (continuous_const.mul continuous_const)) hct
  have hfb : IntegrableOn (fun x : ℝ => (1 : ℂ) / (x + -T * Complex.I)) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcontb.intervalIntegrable _ _)
  have hft : IntegrableOn (fun x : ℝ => (1 : ℂ) / (x + T * Complex.I)) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcontt.intervalIntegrable _ _)
  have hreb : ∀ x : ℝ, ((1 : ℂ) / (x + -T * Complex.I)).re = x / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.normSq_apply, Complex.add_im,
      Complex.mul_im, one_mul, mul_one, mul_zero, zero_mul, sub_zero, add_zero,
      zero_add, neg_zero]
    field_simp
    ring
  have hret : ∀ x : ℝ, ((1 : ℂ) / (x + T * Complex.I)).re = x / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply, Complex.add_im, Complex.mul_im, one_mul, mul_one,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    field_simp
    ring
  have himb : ∀ x : ℝ, ((1 : ℂ) / (x + -T * Complex.I)).im = T / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.normSq_apply, one_mul, mul_one, mul_zero, zero_mul,
      add_zero, zero_add]
    field_simp
    ring
  have himt : ∀ x : ℝ, ((1 : ℂ) / (x + T * Complex.I)).im = -T / (x ^ 2 + T ^ 2) := by
    intro x
    rw [Complex.div_im]
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.normSq_apply, one_mul, mul_one,
      mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    field_simp
    ring
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  have hifb : IntervalIntegrable (fun x : ℝ => (1 : ℂ) / (x + -T * Complex.I))
      volume a b := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hfb
  have hift : IntervalIntegrable (fun x : ℝ => (1 : ℂ) / (x + T * Complex.I))
      volume a b := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hft
  have hreb_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I)).re =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + -T * Complex.I)).re := by
    simpa using (intervalIntegral.intervalIntegral_re hifb).symm
  have hret_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I)).re =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + T * Complex.I)).re := by
    simpa using (intervalIntegral.intervalIntegral_re hift).symm
  have himb_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I)).im =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + -T * Complex.I)).im := by
    simpa using (intervalIntegral.intervalIntegral_im hifb).symm
  have himt_integral :
      (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I)).im =
        ∫ x : ℝ in a..b, ((1 : ℂ) / (x + T * Complex.I)).im := by
    simpa using (intervalIntegral.intervalIntegral_im hift).symm
  apply Complex.ext
  · simp only [Complex.sub_re]
    rw [hreb_integral, hret_integral]
    simp_rw [hreb, hret, sub_self]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      h2re, h2im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, mul_zero, zero_mul, sub_self]
  · simp only [Complex.sub_im]
    rw [himb_integral, himt_integral]
    simp_rw [himb, himt]
    have hneg : ∀ x : ℝ, -T / (x ^ 2 + T ^ 2) = -(T / (x ^ 2 + T ^ 2)) := by
      intro x
      ring
    simp_rw [hneg, intervalIntegral.integral_neg, integral_div_add_sq hT]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      h2re, h2im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, mul_zero, sub_self, mul_one]
    ring

open Real in
/-- Boundary integral of `1/s` over a rectangle containing `0`: `2πi`. -/
theorem boundary_rect_one_div {a b T : ℝ} (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      + Complex.I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * Complex.I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * Complex.I)))
      = 2 * Real.pi * Complex.I := by
  have hab : a ≤ b := le_of_lt (lt_trans ha hb)
  have hbt : 0 < b / T := div_pos hb hT
  have hat : a / T < 0 := div_neg_of_neg_of_pos ha hT
  rw [horiz_diff_one_div (ne_of_gt hT) hab,
    vertical_side_one_div (ne_of_gt hb) hT.le,
    vertical_side_one_div (ne_of_lt ha) hT.le,
    show T / b = (b / T)⁻¹ by rw [inv_div],
    show T / a = (a / T)⁻¹ by rw [inv_div],
    arctan_inv_of_pos hbt, arctan_inv_of_neg hat]
  push_cast
  ring

/-- `exp w - 1 = w * ∫_0^1 exp (t * w)`, by FTC. -/
theorem exp_sub_one_eq (w : ℂ) :
    Complex.exp w - 1 = w * ∫ t : ℝ in (0:ℝ)..1, Complex.exp (t * w) := by
  have hF : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (t * w))
      (w * Complex.exp (t * w)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * w) w t := by
      have h := (hasDerivAt_id (t : ℝ)).ofReal_comp.mul_const w
      simpa using h
    have h2 := h1.cexp
    simpa [mul_comm] using h2
  have hderivfun : deriv (fun t : ℝ => Complex.exp (t * w))
      = fun t : ℝ => w * Complex.exp (t * w) :=
    funext fun t => (hF t).deriv
  have hdiff : ∀ t ∈ uIcc (0:ℝ) 1,
      DifferentiableAt ℝ (fun t : ℝ => Complex.exp (t * w)) t :=
    fun t _ => (hF t).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => w * Complex.exp (t * w)) (uIcc (0:ℝ) 1) := by
    apply Continuous.continuousOn
    apply Continuous.mul continuous_const
    apply Complex.continuous_exp.comp
    exact continuous_ofReal.mul_const w
  have hftc := integral_deriv_eq_sub' (fun t : ℝ => Complex.exp (t * w))
    hderivfun hdiff hcont
  rw [intervalIntegral.integral_const_mul] at hftc
  simpa using hftc.symm

/-- Averaging operator: `E1 u = ∫_0^1 exp (t * u)`. -/
noncomputable def E1 (u : ℂ) : ℂ := ∫ t : ℝ in (0:ℝ)..1, Complex.exp (t * u)

/-- `E1 0 = 1`. -/
theorem E1_zero : E1 0 = 1 := by
  simp only [E1]
  simp

/-- `E1` agrees with the difference quotient off `0`. -/
theorem E1_eq_div (u : ℂ) (hu : u ≠ 0) : E1 u = (Complex.exp u - 1) / u := by
  have h := exp_sub_one_eq u
  simp only [E1]
  rw [eq_div_iff hu, mul_comm]
  exact h.symm

/-- `‖E1 v - 1‖ ≤ ‖v‖` for `‖v‖ ≤ 1`. -/
theorem E1_sub_one_le (v : ℂ) (hv : ‖v‖ ≤ 1) : ‖E1 v - 1‖ ≤ ‖v‖ := by
  by_cases h0 : v = 0
  · simp [h0, E1_zero]
  · have h1 : E1 v - 1 = (Complex.exp v - 1 - v) / v := by
      rw [E1_eq_div v h0, eq_div_iff h0, sub_mul, div_mul_cancel₀ _ h0, one_mul]
    rw [h1, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr h0)]
    calc ‖Complex.exp v - 1 - v‖ ≤ ‖v‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hv
      _ = ‖v‖ * ‖v‖ := by ring

/-- `E1` is continuous at `0`. -/
theorem E1_continuousAt_zero : ContinuousAt E1 0 := by
  rw [ContinuousAt, E1_zero]
  have hbound : ∀ᶠ v : ℂ in 𝓝 0, ‖E1 v - 1‖ ≤ ‖v‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with v hv
    apply E1_sub_one_le
    rw [Metric.mem_ball, dist_zero_right] at hv
    exact le_of_lt hv
  have hnorm : Tendsto (fun v : ℂ => ‖v‖) (𝓝 0) (𝓝 0) := by
    have h := continuous_norm.continuousAt (x := (0 : ℂ))
    rw [ContinuousAt] at h
    simpa using h
  have h := squeeze_zero_norm' hbound hnorm
  simpa using h.add_const (1 : ℂ)

/-- `E1` is continuous everywhere. -/
theorem E1_continuous : Continuous E1 := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · rw [hu]
    exact E1_continuousAt_zero
  · have heq : E1 =ᶠ[𝓝 u] fun v => (Complex.exp v - 1) / v := by
      filter_upwards [eventually_ne_nhds hu] with v hv using E1_eq_div v hv
    exact ContinuousAt.congr
      ((Complex.continuous_exp.sub continuous_const).continuousAt.div continuousAt_id hu)
      heq.symm

/-- Derivative of `E1` under the integral sign. -/
theorem E1_hasDerivAt (x₀ : ℂ) :
    HasDerivAt E1 (∫ t in (0:ℝ)..1, (t : ℂ) * Complex.exp ((t : ℂ) * x₀)) x₀ := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume)
    (F := fun x t => Complex.exp ((t : ℂ) * x))
    (F' := fun x t => (t : ℂ) * Complex.exp ((t : ℂ) * x))
    (x₀ := x₀) (s := Metric.ball x₀ 1) (a := (0:ℝ)) (b := (1:ℝ))
    (bound := fun _ => Real.exp (‖x₀‖ + 1))
    (Metric.ball_mem_nhds x₀ (by norm_num))
    (Filter.Eventually.of_forall fun x =>
      (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).aestronglyMeasurable)
    ((Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)).intervalIntegrable 0 1)
    ((Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht x hx => by
      have ht01 : 0 ≤ t ∧ t ≤ 1 := by
        rw [Set.mem_uIoc] at ht
        rcases ht with ⟨h0, h1⟩ | ⟨h1, h0⟩ <;> constructor <;> linarith
      have hx0 : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have hdist : dist x x₀ < 1 := Metric.mem_ball.mp hx
        have hle : ‖x‖ ≤ ‖x₀‖ + dist x x₀ := by
          rw [dist_eq_norm]
          calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by congr 1; abel
            _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
        linarith
      have htn : ‖((t : ℝ) : ℂ)‖ ≤ 1 := by
        have h : ‖((t : ℝ) : ℂ)‖ = |t| := RCLike.norm_ofReal t
        rw [h, abs_of_nonneg ht01.1]
        exact ht01.2
      have hxt : ‖(t : ℂ) * x‖ ≤ ‖x‖ := by
        rw [norm_mul]
        calc ‖(t : ℂ)‖ * ‖x‖ ≤ 1 * ‖x‖ :=
              mul_le_mul_of_nonneg_right htn (norm_nonneg _)
          _ = ‖x‖ := one_mul _
      calc ‖(t : ℂ) * Complex.exp ((t : ℂ) * x)‖
          = ‖(t : ℂ)‖ * ‖Complex.exp ((t : ℂ) * x)‖ := norm_mul _ _
        _ ≤ 1 * Real.exp (‖x₀‖ + 1) := by
            apply mul_le_mul htn _ (norm_nonneg _) zero_le_one
            calc ‖Complex.exp ((t : ℂ) * x)‖ ≤ Real.exp ‖(t : ℂ) * x‖ :=
                  Complex.norm_exp_le_exp_norm _
              _ ≤ Real.exp (‖x₀‖ + 1) := by
                  apply Real.exp_le_exp.mpr
                  calc ‖(t : ℂ) * x‖ ≤ ‖x‖ := hxt
                    _ ≤ ‖x₀‖ + 1 := hx0
        _ = Real.exp (‖x₀‖ + 1) := one_mul _)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => by
      have h1 : HasDerivAt (fun x : ℂ => (t : ℂ) * x) (t : ℂ) x := by
        simpa using (hasDerivAt_id x).const_mul (t : ℂ)
      have h2 := h1.cexp
      rwa [mul_comm (t : ℂ) (Complex.exp ((t : ℂ) * x))] )
  have hE1 : E1 = fun x => ∫ t in (0:ℝ)..1, Complex.exp ((t : ℂ) * x) := rfl
  rw [hE1]
  exact key.2

/-- `E1` is differentiable everywhere. -/
theorem E1_differentiable : Differentiable ℂ E1 :=
  fun x₀ => (E1_hasDerivAt x₀).differentiableAt

/-- Entire extension of `(y^s - 1)/s` via the averaging operator. -/
noncomputable def perronRemainder (y : ℝ) (s : ℂ) : ℂ :=
  Real.log y * E1 (s * Real.log y)

/-- The remainder is entire in `s`: constant times `E1` of a linear map. -/
theorem perronRemainder_differentiable (y : ℝ) :
    Differentiable ℂ (perronRemainder y) := by
  have hEq : perronRemainder y
      = fun s => (Real.log y : ℂ) * E1 (s * (Real.log y : ℂ)) := rfl
  rw [hEq]
  intro s
  have hlin : DifferentiableAt ℂ (fun s : ℂ => s * (Real.log y : ℂ)) s :=
    differentiableAt_id.mul_const _
  exact (differentiableAt_const _).mul ((E1_differentiable _).comp s hlin)

/-- Agreement with the quotient off `0`. -/
theorem perronRemainder_eq_div {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    perronRemainder y s = ((y : ℂ) ^ s - 1) / s := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
  have hcpow : (y : ℂ) ^ s = Complex.exp (s * Real.log y) := by
    rw [Complex.cpow_def_of_ne_zero hy' s, Complex.ofReal_log hy.le]
    congr 1
    ring
  by_cases hL : Real.log y = 0
  · have hy1 : y = 1 := by
      have h := Real.exp_log hy
      rw [hL, Real.exp_zero] at h
      exact h.symm
    simp only [perronRemainder, hL, Complex.ofReal_zero, zero_mul]
    rw [hy1]
    simp [Complex.one_cpow]
  · have hLc : (Real.log y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hL
    have hsL : s * Real.log y ≠ 0 := mul_ne_zero hs hLc
    simp only [perronRemainder, E1_eq_div _ hsL]
    rw [hcpow]
    field_simp

/-- Slope of the remainder at `0`, in integral form. -/
theorem perronRemainder_slope {y : ℝ} {h : ℂ} (hh : h ≠ 0) :
    (perronRemainder y h - perronRemainder y 0) / h
      = (Real.log y : ℂ) ^ 2 * ∫ t : ℝ in (0:ℝ)..1, t * E1 (t * h * Real.log y) := by
  have hg0 : perronRemainder y 0 = Real.log y := by
    simp [perronRemainder, E1_zero]
  have hexp1 : ∀ t : ℝ, Complex.exp (t * h * Real.log y) - 1
      = (t * h * Real.log y) * E1 (t * h * Real.log y) := by
    intro t
    by_cases hv : (t : ℂ) * h * Real.log y = 0
    · simp [hv]
    · rw [E1_eq_div _ hv, mul_div_cancel₀ _ hv]
  have h1 : (1 : ℂ) = ∫ t : ℝ in (0:ℝ)..1, 1 := by simp
  have hcont : Continuous (fun t : ℝ => Complex.exp (t * h * Real.log y)) :=
    Complex.continuous_exp.comp ((continuous_ofReal.mul_const h).mul_const _)
  have hdiff : perronRemainder y h - perronRemainder y 0
      = (Real.log y : ℂ) * ∫ t : ℝ in (0:ℝ)..1,
        (Complex.exp (t * h * Real.log y) - 1) := by
    have e0 : perronRemainder y 0 = (Real.log y : ℂ) * ∫ t : ℝ in (0:ℝ)..1, 1 := by
      rw [hg0, ← h1]
      ring
    rw [e0]
    simp only [perronRemainder, E1, ← mul_assoc]
    rw [← mul_sub, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
  rw [hdiff]
  simp_rw [hexp1]
  have hfac : ∀ t : ℝ, ((t : ℂ) * h * Real.log y) * E1 (t * h * Real.log y)
      = (h * Real.log y) * ((t : ℂ) * E1 (t * h * Real.log y)) := fun t => by ring
  simp_rw [hfac, intervalIntegral.integral_const_mul]
  field_simp

open Real in
/-- Rectangle boundary of `1/s` with the pole outside (`0 < a`): vanishes. -/
theorem boundary_rect_one_div_outside {a b T : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hT : 0 < T) :
    (∫ x : ℝ in a..b, (1 : ℂ) / (x + -T * Complex.I))
      - (∫ x : ℝ in a..b, (1 : ℂ) / (x + T * Complex.I))
      + Complex.I * ((∫ y : ℝ in (-T)..T, (1 : ℂ) / (b + y * Complex.I))
        - (∫ y : ℝ in (-T)..T, (1 : ℂ) / (a + y * Complex.I)))
      = 0 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hbt : 0 < b / T := div_pos hb hT
  have hat : 0 < a / T := div_pos ha hT
  rw [horiz_diff_one_div (ne_of_gt hT) hab,
    vertical_side_one_div (ne_of_gt hb) hT.le,
    vertical_side_one_div (ne_of_gt ha) hT.le,
    show T / b = (b / T)⁻¹ by rw [inv_div],
    show T / a = (a / T)⁻¹ by rw [inv_div],
    arctan_inv_of_pos hbt, arctan_inv_of_pos hat]
  push_cast
  ring

/-- Norm of a positive real base to a complex power. -/
theorem norm_cpow_ofReal {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖(y : ℂ) ^ s‖ = Real.exp (s.re * Real.log y) := by
  have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
  rw [Complex.cpow_def_of_ne_zero hy' s, ← Complex.ofReal_log hy.le, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- The kernel quotient as remainder plus pole part. -/
theorem cpow_div_eq_remainder_add {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    (y : ℂ) ^ s / s = perronRemainder y s + 1 / s := by
  rw [perronRemainder_eq_div hy hs, ← add_div, sub_add_cancel]

/-- Integral of `exp (L * x)` over `[a, b]`. -/
theorem integral_exp_mul {L a b : ℝ} (hL : L ≠ 0) :
    ∫ x : ℝ in a..b, Real.exp (L * x)
      = (Real.exp (L * b) - Real.exp (L * a)) / L := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => Real.exp (L * x) / L)
      (Real.exp (L * x)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => L * x) L x := by
      simpa using (hasDerivAt_id (x : ℝ)).const_mul L
    have h3 := h1.exp.div_const L
    have hval : Real.exp (L * x) * L / L = Real.exp (L * x) :=
      mul_div_cancel_right₀ _ hL
    rwa [hval] at h3
  have hderivfun : deriv (fun x => Real.exp (L * x) / L)
      = fun x => Real.exp (L * x) :=
    funext fun x => (hderiv x).deriv
  have hdiff : ∀ x ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun x => Real.exp (L * x) / L) x :=
    fun x _ => (hderiv x).differentiableAt
  have hcont : ContinuousOn (fun x => Real.exp (L * x)) (Set.uIcc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have h := integral_deriv_eq_sub' (fun x => Real.exp (L * x) / L)
    hderivfun hdiff hcont
  rw [h]
  exact (sub_div _ _ _).symm

/-- Horizontal side bound for `y > 1`, uniform in the left endpoint. -/
theorem horiz_side_bound_gt_one {y U c T e : ℝ} (hy : 0 < y) (hy1 : 1 < y)
    (hU : 0 < U) (hc : 0 < c) (hT : 0 < T) (he : e = T ∨ e = -T) :
    ‖∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * c) / Real.log y / T := by
  have hL : 0 < Real.log y := Real.log_pos hy1
  have hab : -U ≤ c := le_of_lt ((neg_lt_zero.mpr hU).trans hc)
  have hpt : ∀ x : ℝ, ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * x) / T := by
    intro x
    have hre : ((x : ℂ) + (e : ℂ) * Complex.I).re = x := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have him : |(((x : ℂ) + (e : ℂ) * Complex.I).im)| = T := by
      have him' : ((x : ℂ) + (e : ℂ) * Complex.I).im = e := by
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      rw [him']
      rcases he with rfl | rfl
      · exact abs_of_pos hT
      · rw [abs_neg]; exact abs_of_pos hT
    have hTs : T ≤ ‖(x : ℂ) + (e : ℂ) * Complex.I‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [him] at h
    have hnorm : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) := by
      have h := norm_cpow_ofReal hy ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [hre, mul_comm x _] at h
    have e1 : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
        / ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) * (1 / ‖(x : ℂ) + (e : ℂ) * Complex.I‖) := by
      rw [norm_div, hnorm, div_eq_mul_one_div]
    have e2 : Real.exp (Real.log y * x) / T
        = Real.exp (Real.log y * x) * (1 / T) := div_eq_mul_one_div _ _
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact one_div_le_one_div_of_le hT hTs
  have hInt := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (g := fun x => Real.exp (Real.log y * x) / T)
    hab (Filter.Eventually.of_forall fun x _ => hpt x)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const T
      |>.intervalIntegrable _ _)
  have hval : ∫ x : ℝ in (-U)..c, Real.exp (Real.log y * x) / T
      = (Real.exp (Real.log y * c) - Real.exp (Real.log y * (-U)))
        / Real.log y / T := by
    have hfun : (fun x => Real.exp (Real.log y * x) / T)
        = fun x => (1 / T) * Real.exp (Real.log y * x) := by
      funext x; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_exp_mul (ne_of_gt hL)]
    ring
  rw [hval] at hInt
  apply hInt.trans
  apply div_le_div_of_nonneg_right _ hT.le
  apply div_le_div_of_nonneg_right _ hL.le
  exact sub_le_self _ (Real.exp_nonneg _)

/-- Vertical side bound at real part `d ≠ 0`. -/
theorem vert_side_bound {y d T : ℝ} (hy : 0 < y) (hd : d ≠ 0) (hT : 0 < T) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)
      / ((d : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * T * (Real.exp (Real.log y * d) / |d|) := by
  have hab : -T ≤ T := le_of_lt (neg_lt_self hT)
  have hpt : ∀ t : ℝ, ‖(y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)
      / ((d : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * d) / |d| := by
    intro t
    have hre : ((d : ℂ) + (t : ℂ) * Complex.I).re = d := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have hds : |d| ≤ ‖(d : ℂ) + (t : ℂ) * Complex.I‖ := by
      have h := Complex.abs_re_le_norm ((d : ℂ) + (t : ℂ) * Complex.I)
      rwa [hre] at h
    have hnorm : ‖(y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * d) := by
      have h := norm_cpow_ofReal hy ((d : ℂ) + (t : ℂ) * Complex.I)
      rwa [hre, mul_comm d _] at h
    have e1 : ‖(y : ℂ) ^ ((d : ℂ) + (t : ℂ) * Complex.I)
        / ((d : ℂ) + (t : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * d) * (1 / ‖(d : ℂ) + (t : ℂ) * Complex.I‖) := by
      rw [norm_div, hnorm, div_eq_mul_one_div]
    have e2 : Real.exp (Real.log y * d) / |d|
        = Real.exp (Real.log y * d) * (1 / |d|) := div_eq_mul_one_div _ _
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact one_div_le_one_div_of_le (abs_pos.mpr hd) hds
  have hInt := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (g := fun _ => Real.exp (Real.log y * d) / |d|)
    hab (Filter.Eventually.of_forall fun t _ => hpt t)
    (continuous_const.intervalIntegrable _ _)
  have hval : ∫ t : ℝ in (-T)..T, Real.exp (Real.log y * d) / |d|
      = 2 * T * (Real.exp (Real.log y * d) / |d|) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hval] at hInt
  exact hInt

/-- Left-side corollary: `d = -U`. -/
theorem vert_side_bound_left {y U T : ℝ} (hy : 0 < y) (hU : 0 < U) (hT : 0 < T) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * T * (Real.exp (Real.log y * (-U)) / U) := by
  have h := vert_side_bound (d := -U) hy (ne_of_lt (neg_lt_zero.mpr hU)) hT
  rwa [abs_neg, abs_of_pos hU] at h

/-- Right-side corollary: `d = U`. -/
theorem vert_side_bound_right {y U T : ℝ} (hy : 0 < y) (hU : 0 < U) (hT : 0 < T) :
    ‖∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * T * (Real.exp (Real.log y * U) / U) := by
  have h := vert_side_bound (d := U) hy (ne_of_gt hU) hT
  rwa [abs_of_pos hU] at h

/-- Rectangle identity for `y^s/s` with the pole inside (`y > 1` case). -/
theorem rect_identity_gt_one {y U c T : ℝ} (hy : 0 < y) (hU : 0 < U) (hc : 0 < c)
    (hT : 0 < T) :
    (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      - (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      + Complex.I * ((∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I))
        - (∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      = 2 * Real.pi * Complex.I := by
  have hbot : ∀ x : ℝ, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have htop : ∀ x : ℝ, ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have hright : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hc]
  have hleft : ∀ t : ℝ, (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hU]
  have hRcont : Continuous (perronRemainder y) :=
    (perronRemainder_differentiable y).continuous
  have hsplit_b : (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in (-U)..c, perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in (-U)..c, (1 : ℂ) / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (hbot x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => hbot x)).intervalIntegrable _ _
  have hsplit_t : (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in (-U)..c, perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in (-U)..c, (1 : ℂ) / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (htop x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => htop x)).intervalIntegrable _ _
  have hsplit_r : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I)
          + 1 / ((c : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hright t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hright t)).intervalIntegrable _ _
  have hsplit_l : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          + 1 / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hleft t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hleft t)).intervalIntegrable _ _
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronRemainder y) (Complex.mk (-U) (-T)) (Complex.mk c T)
    ((perronRemainder_differentiable y).differentiableOn)
  have hR' : (∫ x : ℝ in (-U)..c,
          perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in (-U)..c,
          perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        - Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        = 0 := hR
  have h1 := boundary_rect_one_div (a := -U) (b := c)
    (neg_lt_zero.mpr hU) hc hT
  rw [← Complex.ofReal_neg] at h1
  rw [hsplit_b, hsplit_t, hsplit_r, hsplit_l]
  simp only [smul_eq_mul] at hR'
  linear_combination hR' + h1

/-- Horizontal side bound over `[c, U]`, exact value (no sign hypothesis on `L`). -/
theorem horiz_side_bound_exact {y U c T e : ℝ} (hy : 0 < y)
    (hcU : c ≤ U) (hT : 0 < T) (he : e = T ∨ e = -T) (hL : Real.log y ≠ 0) :
    ‖∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T := by
  have hpt : ∀ x : ℝ, ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
      / ((x : ℂ) + (e : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log y * x) / T := by
    intro x
    have hre : ((x : ℂ) + (e : ℂ) * Complex.I).re = x := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have him : |(((x : ℂ) + (e : ℂ) * Complex.I).im)| = T := by
      have him' : ((x : ℂ) + (e : ℂ) * Complex.I).im = e := by
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      rw [him']
      rcases he with rfl | rfl
      · exact abs_of_pos hT
      · rw [abs_neg]; exact abs_of_pos hT
    have hTs : T ≤ ‖(x : ℂ) + (e : ℂ) * Complex.I‖ := by
      have h := Complex.abs_im_le_norm ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [him] at h
    have hnorm : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) := by
      have h := norm_cpow_ofReal hy ((x : ℂ) + (e : ℂ) * Complex.I)
      rwa [hre, mul_comm x _] at h
    have e1 : ‖(y : ℂ) ^ ((x : ℂ) + (e : ℂ) * Complex.I)
        / ((x : ℂ) + (e : ℂ) * Complex.I)‖
        = Real.exp (Real.log y * x) * (1 / ‖(x : ℂ) + (e : ℂ) * Complex.I‖) := by
      rw [norm_div, hnorm, div_eq_mul_one_div]
    have e2 : Real.exp (Real.log y * x) / T
        = Real.exp (Real.log y * x) * (1 / T) := div_eq_mul_one_div _ _
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact one_div_le_one_div_of_le hT hTs
  have hInt := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (g := fun x => Real.exp (Real.log y * x) / T)
    hcU (Filter.Eventually.of_forall fun x _ => hpt x)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const T
      |>.intervalIntegrable _ _)
  have hval : ∫ x : ℝ in c..U, Real.exp (Real.log y * x) / T
      = (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T := by
    have hfun : (fun x => Real.exp (Real.log y * x) / T)
        = fun x => (1 / T) * Real.exp (Real.log y * x) := by
      funext x; ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_exp_mul hL]
    ring
  rw [hval] at hInt
  exact hInt

/-- Rectangle identity for `y^s/s` with the pole outside (`y < 1` case). -/
theorem rect_identity_lt_one {y U c T : ℝ} (hy : 0 < y) (hcU : c < U) (hc : 0 < c)
    (hT : 0 < T) :
    (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      - (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      + Complex.I * ((∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        - (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I)))
      = 0 := by
  have hU : 0 < U := lt_trans hc hcU
  have hbot : ∀ x : ℝ, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have htop : ∀ x : ℝ, ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro x h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.zero_im] at h2
    linarith [hT]
  have hright : ∀ t : ℝ, (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hU]
  have hleft : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at h2
    linarith [hc]
  have hRcont : Continuous (perronRemainder y) :=
    (perronRemainder_differentiable y).continuous
  have hsplit_b : (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in c..U, perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in c..U, (1 : ℂ) / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (hbot x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => hbot x)).intervalIntegrable _ _
  have hsplit_t : (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in c..U, perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + (∫ x : ℝ in c..U, (1 : ℂ) / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) := by
    have hfun : (fun (x : ℝ) => (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        = fun (x : ℝ) => perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          + 1 / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) :=
      funext fun x => cpow_div_eq_remainder_add hy (htop x)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (Complex.continuous_ofReal.add
        (continuous_const.mul continuous_const)) (fun x => htop x)).intervalIntegrable _ _
  have hsplit_r : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          + 1 / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hright t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hright t)).intervalIntegrable _ _
  have hsplit_l : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = (∫ t : ℝ in (-T)..T, perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        + (∫ t : ℝ in (-T)..T, (1 : ℂ) / ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    have hfun : (fun (t : ℝ) => (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I))
        = fun (t : ℝ) => perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I)
          + 1 / ((c : ℂ) + (t : ℂ) * Complex.I) :=
      funext fun t => cpow_div_eq_remainder_add hy (hleft t)
    rw [hfun, intervalIntegral.integral_add]
    · exact (hRcont.comp (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))).intervalIntegrable _ _
    · exact (Continuous.div continuous_const (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const))
        (fun t => hleft t)).intervalIntegrable _ _
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronRemainder y) (Complex.mk c (-T)) (Complex.mk U T)
    ((perronRemainder_differentiable y).differentiableOn)
  have hR' : (∫ x : ℝ in c..U,
          perronRemainder y ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in c..U,
          perronRemainder y ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        - Complex.I • (∫ t : ℝ in (-T)..T,
          perronRemainder y ((c : ℂ) + (t : ℂ) * Complex.I))
        = 0 := hR
  have h1 := boundary_rect_one_div_outside (a := c) (b := U) hc hcU.le hT
  rw [← Complex.ofReal_neg] at h1
  rw [hsplit_b, hsplit_t, hsplit_r, hsplit_l]
  simp only [smul_eq_mul] at hR'
  linear_combination hR' + h1

/-- Truncated Perron bound for `y > 1`. -/
theorem perron_bound_gt_one {y c T : ℝ} (hy : 0 < y) (hy1 : 1 < y)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T - 1‖ ≤ Real.exp (Real.log y * c) / Real.log y / T / Real.pi := by
  have hL : 0 < Real.log y := Real.log_pos hy1
  have h2pi : 0 < 2 * Real.pi := by positivity
  have h2 : ‖(2:ℂ)‖ = 2 := by
    have hcast : (2:ℂ) = ((2:ℝ):ℂ) := by exact_mod_cast rfl
    rw [hcast]
    calc ‖((2:ℝ):ℂ)‖ = |(2:ℝ)| := RCLike.norm_ofReal 2
      _ = 2 := by norm_num
  have hpiN : ‖((Real.pi:ℝ):ℂ)‖ = Real.pi := by
    calc ‖((Real.pi:ℝ):ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
      _ = Real.pi := abs_of_pos Real.pi_pos
  have h2piN : ‖((2:ℂ) * Real.pi)‖ = 2 * Real.pi := by
    rw [norm_mul, h2, hpiN]
  have h2piI : ‖((2:ℂ) * Real.pi) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, h2piN, Complex.norm_I, mul_one]
  have hR : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = 2 * Real.pi * perronKernel y c T := by
    have hKdef : perronKernel y c T = (1 / (2 * Real.pi))
        * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I)) := rfl
    have hpi : ((2:ℂ) * Real.pi) ≠ 0 := mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [hKdef, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have heqU : ∀ U : ℝ,
      (Real.exp (Real.log y * c) / Real.log y / T
        + Real.exp (Real.log y * c) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * (-U)) / U)) / (2 * Real.pi)
      = Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi) := by
    intro U; ring
  have hperU : ∀ U : ℝ, 1 ≤ U → ‖perronKernel y c T - 1‖
      ≤ Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi) := by
    intro U hU1
    have hU : 0 < U := lt_of_lt_of_le zero_lt_one hU1
    have hrect := rect_identity_gt_one hy hU hc hT
    have hRsmul : Complex.I
          * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / ((c : ℂ) + (t : ℂ) * Complex.I))
        = Complex.I * (2 * Real.pi * perronKernel y c T) := by rw [hR]
    have hKey : ((2:ℂ) * Real.pi * Complex.I) * (perronKernel y c T - 1)
        = ((∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))
          + Complex.I * (∫ t : ℝ in (-T)..T,
            (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      linear_combination hrect - hRsmul
    have hnorm : 2 * Real.pi * ‖perronKernel y c T - 1‖
        ≤ ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) hKey
      rw [norm_mul, h2piI] at h
      rw [h]
      have a : ‖((∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
            - (∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))‖
          ≤ ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
            + ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖ :=
        norm_sub_le _ _
      have b : ‖Complex.I * (∫ t : ℝ in (-T)..T,
              (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      exact (norm_add_le _ _).trans (add_le_add a b)
    have hTle : ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
        ≤ Real.exp (Real.log y * c) / Real.log y / T :=
      horiz_side_bound_gt_one hy hy1 hU hc hT (Or.inl rfl)
    have hBle : ‖(∫ x : ℝ in (-U)..c, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
        ≤ Real.exp (Real.log y * c) / Real.log y / T :=
      horiz_side_bound_gt_one hy hy1 hU hc hT (Or.inr rfl)
    have hVle : ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((-U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ 2 * T * (Real.exp (Real.log y * (-U)) / U) :=
      vert_side_bound_left hy hU hT
    have hdiv : ‖perronKernel y c T - 1‖
        ≤ (Real.exp (Real.log y * c) / Real.log y / T
          + Real.exp (Real.log y * c) / Real.log y / T
          + 2 * T * (Real.exp (Real.log y * (-U)) / U)) / (2 * Real.pi) := by
      rw [le_div_iff₀ h2pi, mul_comm]
      refine hnorm.trans ?_
      exact add_le_add (add_le_add hTle hBle) hVle
    rw [heqU U] at hdiv
    exact hdiv
  have hUL : Filter.Tendsto (fun U : ℝ => U * Real.log y) Filter.atTop
      Filter.atTop := by
    have h := Filter.Tendsto.const_mul_atTop hL (tendsto_id (x := Filter.atTop))
    have hform2 : (fun U : ℝ => U * Real.log y)
        = fun U => Real.log y * id U := by
      funext U; simp [mul_comm]
    rw [hform2]; exact h
  have hexp2 : Filter.Tendsto (fun U : ℝ => Real.exp (Real.log y * (-U)))
      Filter.atTop (𝓝 0) := by
    have hexp : Filter.Tendsto (fun U : ℝ => Real.exp (-(U * Real.log y)))
        Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hUL
    have hcongr : (fun U : ℝ => Real.exp (Real.log y * (-U)))
        = fun U => Real.exp (-(U * Real.log y)) := by
      funext U; congr 1; ring
    rw [hcongr]; exact hexp
  have hB2 : Filter.Tendsto (fun U : ℝ => T * Real.exp (Real.log y * (-U)) / Real.pi)
      Filter.atTop (𝓝 0) := by
    have hform : (fun U : ℝ => T * Real.exp (Real.log y * (-U)) / Real.pi)
        = fun U => (T / Real.pi) * Real.exp (Real.log y * (-U)) := by
      funext U; ring
    rw [hform]
    have hmul := Filter.Tendsto.const_mul (T / Real.pi) hexp2
    simpa using hmul
  have he0 : Filter.Tendsto
      (fun U : ℝ => T * Real.exp (Real.log y * (-U)) / (U * Real.pi))
      Filter.atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hB2
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with U hU1
    have hU : 0 < U := lt_of_lt_of_le zero_lt_one hU1
    have hnn : 0 ≤ T * Real.exp (Real.log y * (-U)) / (U * Real.pi) := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hform3 : T * Real.exp (Real.log y * (-U)) / (U * Real.pi)
        = (T * Real.exp (Real.log y * (-U)) / Real.pi) / U := by ring
    rw [hform3]
    apply div_le_self _ hU1
    positivity
  have hCg : Filter.Tendsto
      (fun U : ℝ => Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi))
      Filter.atTop
      (𝓝 (Real.exp (Real.log y * c) / Real.log y / T / Real.pi)) := by
    have h := (tendsto_const_nhds (x := Real.exp (Real.log y * c) / Real.log y / T
      / Real.pi)).add he0
    simpa using h
  have hCf : Filter.Tendsto (fun _ : ℝ => ‖perronKernel y c T - 1‖) Filter.atTop
      (𝓝 ‖perronKernel y c T - 1‖) := tendsto_const_nhds
  have hle : (fun _ : ℝ => ‖perronKernel y c T - 1‖) ≤ᶠ[Filter.atTop]
      (fun U : ℝ => Real.exp (Real.log y * c) / Real.log y / T / Real.pi
        + T * Real.exp (Real.log y * (-U)) / (U * Real.pi)) := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with U hU1
    exact hperU U hU1
  exact le_of_tendsto_of_tendsto hCf hCg hle

/-- Truncated Perron bound for `y < 1`. -/
theorem perron_bound_lt_one {y c T : ℝ} (hy : 0 < y) (hylt : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T‖ ≤ Real.exp (Real.log y * c) / |Real.log y| / T / Real.pi := by
  have hL : Real.log y < 0 := Real.log_neg hy hylt
  have hLne : Real.log y ≠ 0 := ne_of_lt hL
  have h2pi : 0 < 2 * Real.pi := by positivity
  have h2 : ‖(2:ℂ)‖ = 2 := by
    have hcast : (2:ℂ) = ((2:ℝ):ℂ) := by exact_mod_cast rfl
    rw [hcast]
    calc ‖((2:ℝ):ℂ)‖ = |(2:ℝ)| := RCLike.norm_ofReal 2
      _ = 2 := by norm_num
  have hpiN : ‖((Real.pi:ℝ):ℂ)‖ = Real.pi := by
    calc ‖((Real.pi:ℝ):ℂ)‖ = |Real.pi| := RCLike.norm_ofReal Real.pi
      _ = Real.pi := abs_of_pos Real.pi_pos
  have h2piN : ‖((2:ℂ) * Real.pi)‖ = 2 * Real.pi := by
    rw [norm_mul, h2, hpiN]
  have h2piI : ‖((2:ℂ) * Real.pi) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, h2piN, Complex.norm_I, mul_one]
  have hR : (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
        / ((c : ℂ) + (t : ℂ) * Complex.I))
      = 2 * Real.pi * perronKernel y c T := by
    have hKdef : perronKernel y c T = (1 / (2 * Real.pi))
        * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
          / ((c : ℂ) + (t : ℂ) * Complex.I)) := rfl
    have hpi : ((2:ℂ) * Real.pi) ≠ 0 := mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [hKdef, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  have hperU : ∀ U : ℝ, max c 1 < U → ‖perronKernel y c T‖
      ≤ ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi) := by
    intro U hmaxU
    have hcU : c < U := lt_of_le_of_lt (le_max_left _ _) hmaxU
    have hU : 0 < U := lt_trans hc hcU
    have hrect := rect_identity_lt_one hy hcU hc hT
    have hRsmul : Complex.I
          * (∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / ((c : ℂ) + (t : ℂ) * Complex.I))
        = Complex.I * (2 * Real.pi * perronKernel y c T) := by rw [hR]
    have hKey : ((2:ℂ) * Real.pi * Complex.I) * perronKernel y c T
        = ((∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
          - (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)))
          + Complex.I * (∫ t : ℝ in (-T)..T,
            (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      linear_combination -hrect - hRsmul
    have hnorm : 2 * Real.pi * ‖perronKernel y c T‖
        ≤ ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
          + ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) hKey
      rw [norm_mul, h2piI] at h
      rw [h]
      have a : ‖((∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
            - (∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)))‖
          ≤ ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
            + ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖ :=
        norm_sub_le _ _
      have b : ‖Complex.I * (∫ t : ℝ in (-T)..T,
              (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
              / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      exact (norm_add_le _ _).trans (add_le_add a b)
    have hBle : ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))‖
        ≤ (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
          / Real.log y / T :=
      horiz_side_bound_exact hy hcU.le hT (Or.inr rfl) hLne
    have hTle : ‖(∫ x : ℝ in c..U, (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))‖
        ≤ (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
          / Real.log y / T :=
      horiz_side_bound_exact hy hcU.le hT (Or.inl rfl) hLne
    have hVle : ‖(∫ t : ℝ in (-T)..T, (y : ℂ) ^ (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((U : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ 2 * T * (Real.exp (Real.log y * U) / U) :=
      vert_side_bound_right hy hU hT
    have hdiv : ‖perronKernel y c T‖
        ≤ ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
          + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
          + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi) := by
      rw [le_div_iff₀ h2pi, mul_comm]
      refine hnorm.trans ?_
      exact add_le_add (add_le_add hBle hTle) hVle
    exact hdiv
  have hUL' : Filter.Tendsto (fun U : ℝ => (-Real.log y) * U) Filter.atTop
      Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (neg_pos.mpr hL) (tendsto_id (x := Filter.atTop))
  have hexpU : Filter.Tendsto (fun U : ℝ => Real.exp (Real.log y * U))
      Filter.atTop (𝓝 0) := by
    have hexp : Filter.Tendsto
        (fun U : ℝ => Real.exp (-((-Real.log y) * U))) Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hUL'
    have hcongr : (fun U : ℝ => Real.exp (Real.log y * U))
        = fun U => Real.exp (-((-Real.log y) * U)) := by
      funext U; congr 1; ring
    rw [hcongr]; exact hexp
  have hB : Filter.Tendsto
      (fun U : ℝ => (Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T) Filter.atTop
      (𝓝 ((0 - Real.exp (Real.log y * c)) / Real.log y / T)) :=
    ((hexpU.sub_const _).div_const _).div_const _
  have hbU : Filter.Tendsto (fun U : ℝ => 2 * T * Real.exp (Real.log y * U))
      Filter.atTop (𝓝 0) := by
    have hmul := Filter.Tendsto.const_mul (2 * T) hexpU
    simpa using hmul
  have hV : Filter.Tendsto (fun U : ℝ => 2 * T * (Real.exp (Real.log y * U) / U))
      Filter.atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbU
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with U hU1
    have hU : 0 < U := lt_of_lt_of_le zero_lt_one hU1
    have hnn : 0 ≤ 2 * T * (Real.exp (Real.log y * U) / U) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hle : Real.exp (Real.log y * U) / U ≤ Real.exp (Real.log y * U) :=
      div_le_self (Real.exp_nonneg _) hU1
    apply mul_le_mul_of_nonneg_left hle
    positivity
  have hg : Filter.Tendsto
      (fun U : ℝ => ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T
        + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi)) Filter.atTop
      (𝓝 (((0 - Real.exp (Real.log y * c)) / Real.log y / T
        + (0 - Real.exp (Real.log y * c)) / Real.log y / T + 0) / (2 * Real.pi))) :=
    (((hB.add hB).add hV).div_const _)
  have hC0 : (((0 - Real.exp (Real.log y * c)) / Real.log y / T
        + (0 - Real.exp (Real.log y * c)) / Real.log y / T + 0) / (2 * Real.pi))
      = Real.exp (Real.log y * c) / |Real.log y| / T / Real.pi := by
    rw [abs_of_neg hL]
    ring
  rw [hC0] at hg
  have hCf : Filter.Tendsto (fun _ : ℝ => ‖perronKernel y c T‖) Filter.atTop
      (𝓝 ‖perronKernel y c T‖) := tendsto_const_nhds
  have hle : (fun _ : ℝ => ‖perronKernel y c T‖) ≤ᶠ[Filter.atTop]
      (fun U : ℝ => ((Real.exp (Real.log y * U) - Real.exp (Real.log y * c))
        / Real.log y / T
        + (Real.exp (Real.log y * U) - Real.exp (Real.log y * c)) / Real.log y / T
        + 2 * T * (Real.exp (Real.log y * U) / U)) / (2 * Real.pi)) := by
    filter_upwards [Filter.eventually_ge_atTop (max c 1 + 1)] with U hU
    have hmax : max c 1 < U := lt_of_lt_of_le (lt_add_one _) hU
    exact hperU U hmax
  exact le_of_tendsto_of_tendsto hCf hg hle

/-- Truncated Perron formula with explicit Schoenfeld-shape error bound. -/
theorem perron_bound {y c T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel y c T - (if 1 < y then (1:ℂ) else 0)‖
      ≤ Real.exp (Real.log y * c) / |Real.log y| / T / Real.pi := by
  rcases lt_or_gt_of_ne hy1 with h | h
  · rw [if_neg (not_lt.mpr h.le), sub_zero]
    exact perron_bound_lt_one hy h hc hT
  · rw [if_pos h, abs_of_pos (Real.log_pos h)]
    exact perron_bound_gt_one hy h hc hT

end PerronKernel
end
end

/- TauberianPort.MathlibExt.Analysis.LaplaceTransform.NewmanTauberian -/
section
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

/-!
# Newman's Tauberian theorem

Newman's analytic (Tauberian) theorem for a bounded measurable function whose Laplace
transform extends analytically to the closed right half-plane. Following D. J. Newman,
"Simple analytic proof of the prime number theorem", Amer. Math. Monthly 87 (1980)
693–696, in the form of D. Zagier, "Newman's short proof of the prime number theorem",
Amer. Math. Monthly 104 (1997) 705–708.
-/

section
open Filter MeasureTheory Set Topology

/-- Newman kernel `k_R(z) = (1 + z^2 / R^2) / z`. At `z = 0` this is junk (0). -/
private noncomputable def newman_kernel (R : ℝ) (z : ℂ) : ℂ :=
  (1 + z ^ 2 / (R : ℂ) ^ 2) / z

/-- Partial Laplace transform `g_T(z) = ∫ t in 0..T, exp(-z t) * f t`. -/
private noncomputable def newman_partial (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..T, Complex.exp (-z * (t : ℂ)) * f t

/-- Rectangle boundary expression in Mathlib Cauchy-Goursat shape. -/
private noncomputable def newman_rect (Φ : ℂ → ℂ) (a b R : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in a..b, Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    + Complex.I • (∫ y : ℝ in (-R)..R, Φ ((b : ℂ) + (y : ℂ) * Complex.I))
    - Complex.I • (∫ y : ℝ in (-R)..R, Φ ((a : ℂ) + (y : ℂ) * Complex.I))

/-- Right part of the split rectangle. -/
private noncomputable def newman_JR (Φ : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..R, Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in (0 : ℝ)..R, Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    + Complex.I • (∫ y : ℝ in (-R)..R, Φ ((R : ℂ) + (y : ℂ) * Complex.I))

/-- Left part of the split rectangle (at `Re z = -δ`). -/
private noncomputable def newman_JL (Φ : ℂ → ℂ) (δ R : ℝ) : ℂ :=
  (∫ x : ℝ in (-δ)..(0 : ℝ), Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in (-δ)..(0 : ℝ), Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    - Complex.I • (∫ y : ℝ in (-R)..R, Φ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))

/-- Far-left part (at `Re z = -R`). -/
private noncomputable def newman_JF (Φ : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x : ℝ in (-R)..(0 : ℝ), Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in (-R)..(0 : ℝ), Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    - Complex.I • (∫ y : ℝ in (-R)..R, Φ (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))

/-- Kernel bound on horizontal sides. -/
private lemma newman_kernel_norm_horizontal (R x : ℝ) (hR : 0 < R) (s : ℝ)
    (hs : s = R ∨ s = -R) :
    ‖newman_kernel R ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ 2 * |x| / R ^ 2 := by
  have hss : s ^ 2 = R ^ 2 := by
    rcases hs with rfl | rfl
    · ring
    · ring
  have hRc : ((R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hs0 : s ≠ 0 := by
    rcases hs with rfl | rfl
    · exact ne_of_gt hR
    · exact ne_of_lt (by linarith)
  set z : ℂ := (x : ℂ) + (s : ℂ) * Complex.I with hz
  have hsim : z.im = s := by simp [hz]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hs0
    have hcon := congrArg Complex.im h0
    simpa [hsim] using hcon
  have hnormz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  -- Key identity: `R^2 + z^2 = x * (x + 2 * s * I)`, since `s^2 = R^2`.
  have hcast2 : ((s : ℂ)) ^ 2 = ((R : ℂ)) ^ 2 := by
    have h : ((s ^ 2 : ℝ) : ℂ) = ((R ^ 2 : ℝ) : ℂ) := by rw [hss]
    push_cast at h
    exact h
  have h2 : ((R : ℝ) : ℂ) ^ 2 + z ^ 2
      = (x : ℂ) * ((x : ℂ) + 2 * (s : ℂ) * Complex.I) := by
    simp only [hz]
    linear_combination ((R : ℝ) : ℂ) ^ 2 * Complex.I_mul_I
      + (Complex.I * Complex.I) * hcast2
  have key : 1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2
      = (x : ℂ) * ((x : ℂ) + 2 * (s : ℂ) * Complex.I) / ((R : ℝ) : ℂ) ^ 2 := by
    have hR2 : ((R : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hRc
    field_simp
    linear_combination h2
  -- `‖x + 2 s I‖ ≤ 2 ‖z‖`, by comparing squares.
  have hsq : ‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖ ^ 2 ≤ (2 * ‖z‖) ^ 2 := by
    have e1 : ‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + (2 * s) ^ 2 := by
      have hshape : (x : ℂ) + 2 * (s : ℂ) * Complex.I
          = (x : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hshape, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    have e2 : (2 * ‖z‖) ^ 2 = 4 * (x ^ 2 + s ^ 2) := by
      have hzshape : z = (x : ℂ) + ((s : ℝ) : ℂ) * Complex.I := rfl
      rw [hzshape, Complex.norm_add_mul_I]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [e1, e2, hss]
    nlinarith [sq_nonneg x]
  have hle : ‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖ ≤ 2 * ‖z‖ := by
    have hnn : 0 ≤ (2 : ℝ) * ‖z‖ := by positivity
    have habs : |‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖| ≤ 2 * ‖z‖ := by
      rw [← Real.norm_eq_abs]
      exact abs_le_of_sq_le_sq hsq hnn
    rwa [abs_of_nonneg (norm_nonneg _)] at habs
  -- Divide through by `‖z‖`.
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hnormR2 : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow]
    simp [Complex.norm_real, abs_of_pos hR]
  unfold newman_kernel
  rw [key, norm_div, norm_div, hnormR2, norm_mul, Complex.norm_real,
    div_div, div_le_iff₀ (mul_pos hR2pos hnormz)]
  have hrw : 2 * |x| / R ^ 2 * (R ^ 2 * ‖z‖) = |x| * (2 * ‖z‖) := by
    field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg x)

/-- Kernel bound on vertical sides. -/
private lemma newman_kernel_norm_vertical (R : ℝ) (hR : 0 < R) (z : ℂ)
    (hlo : R ≤ ‖z‖) (hhi : ‖z‖ ≤ 2 * R) :
    ‖newman_kernel R z‖ ≤ 3 / R := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlo
    linarith
  have hRc : ((R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hRne
  have hR2 : ((R : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hRc
  have hnormR2 : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow]
    simp [Complex.norm_real, abs_of_pos hR]
  have hsplit : newman_kernel R z = 1 / z + z / ((R : ℝ) : ℂ) ^ 2 := by
    unfold newman_kernel
    field_simp
  have e1 : ‖(1 : ℂ) / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
  have e2 : ‖z / ((R : ℝ) : ℂ) ^ 2‖ = ‖z‖ / R ^ 2 := by
    rw [norm_div, hnormR2]
  have g1 : 1 / ‖z‖ ≤ 1 / R := one_div_le_one_div_of_le hR hlo
  have g2 : ‖z‖ / R ^ 2 ≤ 2 / R := by
    have hle : ‖z‖ / R ^ 2 ≤ (2 * R) / R ^ 2 :=
      (div_le_div_iff_of_pos_right hR2pos).mpr hhi
    have heq : (2 * R) / R ^ 2 = 2 / R := by
      field_simp
    rwa [heq] at hle
  calc ‖newman_kernel R z‖ = ‖(1 : ℂ) / z + z / ((R : ℝ) : ℂ) ^ 2‖ := by rw [hsplit]
    _ ≤ ‖(1 : ℂ) / z‖ + ‖z / ((R : ℝ) : ℂ) ^ 2‖ := norm_add_le _ _
    _ = 1 / ‖z‖ + ‖z‖ / R ^ 2 := by rw [e1, e2]
    _ ≤ 1 / R + 2 / R := add_le_add g1 g2
    _ = 3 / R := by ring

/-- The partial transform is entire. -/
private lemma newman_partial_differentiable (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (T : ℝ) (hT : 0 ≤ T) :
    Differentiable ℂ (newman_partial f T) := by
  set fT : ℝ → ℂ := Set.indicator (Set.Ioc 0 T) f with hfT
  have hfTmeas : AEStronglyMeasurable fT (volume.restrict (Set.Ioi 0)) :=
    hfmeas.indicator measurableSet_Ioc
  -- Exponential bound for the truncated function, for every half-plane.
  have hbnd : ∀ a : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖fT t‖ ≤ (B * Real.exp (|a| * T)) * Real.exp (a * t) := by
    intro a t ht
    by_cases hmem : t ∈ Set.Ioc (0 : ℝ) T
    · have hft : ‖f t‖ ≤ B := hbound t ht
      have habs : |a * t| ≤ |a| * T := by
        rw [abs_mul, abs_of_pos hmem.1]
        exact mul_le_mul_of_nonneg_left hmem.2 (abs_nonneg a)
      have hge : (0 : ℝ) ≤ |a| * T + a * t := by
        have hneg := neg_le_of_abs_le habs
        linarith
      have hexp_ge : (1 : ℝ) ≤ Real.exp (|a| * T + a * t) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hge
      have hrewrite : fT t = f t := by
        simp only [hfT]
        exact Set.indicator_of_mem hmem f
      rw [hrewrite]
      calc ‖f t‖ ≤ B := hft
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * Real.exp (|a| * T + a * t) :=
            mul_le_mul_of_nonneg_left hexp_ge hB
        _ = (B * Real.exp (|a| * T)) * Real.exp (a * t) := by
            rw [Real.exp_add]
            ring
    · have hzero : fT t = 0 := by
        simp only [hfT]
        exact Set.indicator_of_notMem hmem f
      rw [hzero, norm_zero]
      exact mul_nonneg (mul_nonneg hB (Real.exp_nonneg _)) (Real.exp_nonneg _)
  -- The Laplace transform of the truncation is the partial transform.
  have heq : laplace fT = newman_partial f T := by
    funext z
    unfold laplace newman_partial
    have hpt : ∀ t : ℝ, Complex.exp (-z * (t : ℂ)) • fT t
        = Set.indicator (Set.Ioc 0 T)
          (fun t => Complex.exp (-z * (t : ℂ)) • f t) t := by
      intro t
      by_cases hmem : t ∈ Set.Ioc (0 : ℝ) T
      · simp only [hfT, Set.indicator_of_mem hmem]
      · simp only [hfT, Set.indicator_of_notMem hmem, smul_zero]
    rw [show (∫ t : ℝ in Set.Ioi 0, Complex.exp (-z * (t : ℂ)) • fT t)
          = ∫ t : ℝ in Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 T,
            Complex.exp (-z * (t : ℂ)) • f t from by
          simp_rw [hpt]
          exact MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self,
      ← intervalIntegral.integral_of_le hT]
    simp_rw [smul_eq_mul]
  rw [← heq]
  intro z
  have hkey := differentiableOn_laplace_of_norm_le_exp fT (z.re - 1)
    (B * Real.exp (|z.re - 1| * T)) hfTmeas
    (mul_nonneg hB (Real.exp_nonneg _)) (hbnd (z.re - 1))
  have hopen : IsOpen {s : ℂ | z.re - 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : z ∈ {s : ℂ | z.re - 1 < s.re} := by
    change z.re - 1 < z.re
    linarith
  exact hkey.differentiableAt (hopen.mem_nhds hmem)

/-- Laplace minus partial equals the tail integral. -/
private lemma newman_laplace_sub_partial_eq_tail (f : ℝ → ℂ)
    (G : ℂ → ℂ)
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (T : ℝ) (hT : 0 ≤ T) (z : ℂ) (hz : 0 < z.re) :
    G z - newman_partial f T z
      = ∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) * f t ∧
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * f t) (Set.Ioi T) := by
  obtain ⟨hconv, hval⟩ := hG z hz
  have hIoc : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t)
      (Set.Ioc 0 T) :=
    hconv.mono_set Set.Ioc_subset_Ioi_self
  have hIoi : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t)
      (Set.Ioi T) :=
    hconv.mono_set (Set.Ioi_subset_Ioi hT)
  have hsplit : (∫ t : ℝ in Set.Ioc 0 T ∪ Set.Ioi T,
        Complex.exp (-z * (t : ℂ)) • f t)
      = (∫ t : ℝ in Set.Ioc 0 T, Complex.exp (-z * (t : ℂ)) • f t)
        + (∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) • f t) :=
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      hIoc hIoi
  have hlap : laplace f z
      = ∫ t : ℝ in Set.Ioi 0, Complex.exp (-z * (t : ℂ)) • f t := rfl
  have hGval : G z
      = (∫ t : ℝ in Set.Ioc 0 T, Complex.exp (-z * (t : ℂ)) • f t)
        + (∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) • f t) := by
    rw [← hval, hlap, ← Set.Ioc_union_Ioi_eq_Ioi hT]
    exact hsplit
  have hpart : (∫ t : ℝ in Set.Ioc 0 T, Complex.exp (-z * (t : ℂ)) • f t)
      = newman_partial f T z := by
    unfold newman_partial
    rw [intervalIntegral.integral_of_le hT]
    simp_rw [smul_eq_mul]
  constructor
  · rw [hGval, hpart, add_sub_cancel_left]
    simp_rw [smul_eq_mul]
  · simpa only [smul_eq_mul] using hIoi

/-- Tail bound for `Re z > 0`. -/
private lemma newman_tail_bound (f : ℝ → ℂ) (B : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (T : ℝ) (hT : 0 ≤ T) (z : ℂ) (hz : 0 < z.re) :
    ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖ ≤ B / z.re := by
  obtain ⟨htail_eq, _⟩ := newman_laplace_sub_partial_eq_tail f G hG T hT z hz
  have hneg : -z.re < 0 := by linarith
  have hg_int : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Set.Ioi T) :=
    (integrableOn_exp_mul_Ioi hneg T).const_mul B
  -- Pointwise bound on the tail integrand.
  have hpt : ∀ t : ℝ, t ∈ Set.Ioi T →
      ‖Complex.exp (-z * (t : ℂ)) * f t‖ ≤ B * Real.exp (-z.re * t) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_trans hT (le_of_lt ht)
    have h1 : ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp (-z.re * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [norm_mul, h1]
    calc Real.exp (-z.re * t) * ‖f t‖
        ≤ Real.exp (-z.re * t) * B :=
          mul_le_mul_of_nonneg_left (hbound t ht0) (Real.exp_nonneg _)
      _ = B * Real.exp (-z.re * t) := mul_comm _ _
  have hnorm_tail : ‖∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) * f t‖
      ≤ B * Real.exp (-z.re * T) / z.re := by
    have hle := MeasureTheory.norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi T))
      (f := fun t : ℝ => Complex.exp (-z * (t : ℂ)) * f t)
      (g := fun t : ℝ => B * Real.exp (-z.re * t))
      hg_int ((ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ (fun t ht => hpt t ht)))
    have hval : (∫ t : ℝ in Set.Ioi T, B * Real.exp (-z.re * t))
        = B * Real.exp (-z.re * T) / z.re := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hneg T]
      field_simp
    rw [hval] at hle
    exact hle
  -- Multiply by `‖exp (z * T)‖ = exp (z.re * T)`; the exponentials cancel.
  have hexpT : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [htail_eq, norm_mul, hexpT]
  calc ‖∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) * f t‖ * Real.exp (z.re * T)
      ≤ (B * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) :=
        mul_le_mul_of_nonneg_right hnorm_tail (Real.exp_nonneg _)
    _ = B / z.re := by
        have hcancel : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
          rw [← Real.exp_add]
          simp [add_comm]
        have hrw : (B * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T)
            = (B / z.re) * (Real.exp (-z.re * T) * Real.exp (z.re * T)) := by
          ring
        rw [hrw, hcancel, mul_one]

/-- Partial bound for `Re z < 0`. -/
private lemma newman_partial_bound_left (f : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (T : ℝ) (hT : 0 ≤ T) (z : ℂ) (hz : z.re < 0) :
    ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖ ≤ B / (-z.re) := by
  have hneg : (0 : ℝ) < -z.re := neg_pos.mpr hz
  have hcont : Continuous (fun t : ℝ => B * Real.exp (-z.re * t)) :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id'))
  have hbound_int : IntervalIntegrable (fun t : ℝ => B * Real.exp (-z.re * t))
      volume 0 T :=
    hcont.intervalIntegrable 0 T
  -- Pointwise bound on the partial integrand.
  have hpt : ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioc 0 T →
      ‖Complex.exp (-z * (t : ℂ)) * f t‖ ≤ B * Real.exp (-z.re * t) := by
    apply ae_of_all
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht.1
    have h1 : ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp (-z.re * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [norm_mul, h1]
    calc Real.exp (-z.re * t) * ‖f t‖
        ≤ Real.exp (-z.re * t) * B :=
          mul_le_mul_of_nonneg_left (hbound t ht0) (Real.exp_nonneg _)
      _ = B * Real.exp (-z.re * t) := mul_comm _ _
  have h1 : ‖newman_partial f T z‖
      ≤ ∫ t : ℝ in (0 : ℝ)..T, B * Real.exp (-z.re * t) := by
    unfold newman_partial
    exact intervalIntegral.norm_integral_le_of_norm_le hT hpt hbound_int
  -- Evaluate the exponential integral by substitution.
  have hval : (∫ t : ℝ in (0 : ℝ)..T, B * Real.exp (-z.re * t))
      = B * (Real.exp (-z.re * T) - 1) / (-z.re) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left _ (ne_of_gt hneg)]
    simp only [mul_zero, integral_exp, smul_eq_mul]
    rw [Real.exp_zero]
    ring
  rw [hval] at h1
  -- Multiply by `‖exp (z * T)‖ = exp (z.re * T)` and simplify.
  have hexpT : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hcancel : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
    rw [← Real.exp_add]
    simp [add_comm]
  rw [norm_mul, hexpT]
  calc ‖newman_partial f T z‖ * Real.exp (z.re * T)
      ≤ (B * (Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = B * (1 - Real.exp (z.re * T)) / (-z.re) := by
        linear_combination B * hcancel / (-z.re)
    _ ≤ B / (-z.re) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hneg)
        calc B * (1 - Real.exp (z.re * T))
            ≤ B * 1 :=
              mul_le_mul_of_nonneg_left
                (sub_le_self 1 (le_of_lt (Real.exp_pos _))) hB
          _ = B := mul_one B

/-- A good `δ` from compactness. -/
private lemma newman_exists_delta (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G {s | 0 ≤ s.re}) (R : ℝ) (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → AnalyticAt ℂ G z := by
  have hU : IsOpen {z : ℂ | AnalyticAt ℂ G z} := isOpen_analyticAt ℂ G
  set K0 : Set ℂ := Set.Icc 0 R ×ℂ Set.Icc (-R) R with hK0
  have hK0c : IsCompact K0 := isCompact_Icc.reProdIm isCompact_Icc
  have hK0U : K0 ⊆ {z | AnalyticAt ℂ G z} := by
    intro z hz
    rw [hK0, Complex.mem_reProdIm] at hz
    obtain ⟨hre, -⟩ := hz
    apply hG
    change (0 : ℝ) ≤ z.re
    exact (Set.mem_Icc.mp hre).1
  obtain ⟨δ0, hδ0, hsub⟩ := hK0c.exists_thickening_subset_open hU hK0U
  have hK0ne : K0.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hK0, Complex.mem_reProdIm]
    refine ⟨Set.mem_Icc.mpr ⟨le_rfl, hR.le⟩,
      Set.mem_Icc.mpr ⟨neg_nonpos.mpr hR.le, hR.le⟩⟩
  refine ⟨min (δ0 / 2) (R / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  intro z hz1 hz2 hz3
  apply hsub
  rw [Metric.mem_thickening_iff_infDist_lt hK0ne]
  -- The witness in `K0` closest in real part.
  set w : ℂ := ((max z.re 0 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I with hw
  have hwK : w ∈ K0 := by
    rw [hK0, Complex.mem_reProdIm]
    constructor
    · have hre_w : w.re = max z.re 0 := by simp [hw]
      rw [hre_w]
      exact Set.mem_Icc.mpr ⟨le_max_right _ _,
        max_le hz2 hR.le⟩
    · have him_w : w.im = z.im := by simp [hw]
      rw [him_w]
      exact Set.mem_Icc.mpr ⟨by linarith [abs_le.mp hz3], by linarith [abs_le.mp hz3]⟩
  have hsub_eq : z - w = ((z.re - max z.re 0 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hw]
    · simp [hw]
  have hmax : |z.re - max z.re 0| ≤ min (δ0 / 2) (R / 2) := by
    rcases le_total 0 z.re with h | h
    · rw [max_eq_left h, sub_self, abs_zero]
      exact le_min (by linarith) (by linarith)
    · rw [max_eq_right h, sub_zero, abs_of_nonpos h]
      linarith
  have hdist : dist z w < δ0 := by
    rw [Complex.dist_eq, hsub_eq, Complex.norm_real]
    calc |z.re - max z.re 0| ≤ min (δ0 / 2) (R / 2) := hmax
      _ ≤ δ0 / 2 := min_le_left _ _
      _ < δ0 := by linarith
  calc Metric.infDist z K0 ≤ dist z w := Metric.infDist_le_dist_of_mem hwK
    _ < δ0 := hdist

/-- Helper: a continuous function on an open set is interval-integrable
along a segment landing in that set. -/
private lemma newman_comp_line_integrable (Ψ : ℂ → ℂ) (U : Set ℂ)
    (hΨ : ContinuousOn Ψ U) (L : ℝ → ℂ) (hL : Continuous L)
    (p q : ℝ) (hLU : ∀ t ∈ Set.uIcc p q, L t ∈ U) :
    IntervalIntegrable (fun t => Ψ (L t)) volume p q :=
  (hΨ.comp (hL.continuousOn.mono (Set.subset_univ _))
    (fun t ht => hLU t ht)).intervalIntegrable

/-- Helper: `c * (1 / L t)` is interval-integrable along a never-vanishing line. -/
private lemma newman_const_mul_line_integrable (c : ℂ) (L : ℝ → ℂ) (hL : Continuous L)
    (hL0 : ∀ t, L t ≠ 0) (p q : ℝ) :
    IntervalIntegrable (fun t => c * ((1 : ℂ) / L t)) volume p q :=
  ((continuous_const.mul (continuous_const.div hL hL0))).intervalIntegrable p q

/-- Rectangle Cauchy formula at the origin. -/
private lemma newman_rect_cauchy_zero (Φ : ℂ → ℂ) (a b R : ℝ)
    (ha : a < 0) (hb : 0 < b) (hR : 0 < R)
    (U : Set ℂ) (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U)
    (hmem : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ≤ R → z ∈ U) :
    newman_rect (fun z => Φ z / z) a b R = 2 * Real.pi * Complex.I * Φ 0 := by
  have hab : a ≤ b := le_of_lt (lt_trans ha hb)
  have hRle : -R ≤ R := by linarith
  -- The origin lies in `U`.
  have h0U : (0 : ℂ) ∈ U :=
    hmem 0 (le_of_lt ha) (le_of_lt hb) (by simp [hR.le])
  have h0n : U ∈ 𝓝 (0 : ℂ) := hU.mem_nhds h0U
  have hΨ : DifferentiableOn ℂ (dslope Φ 0) U :=
    (Complex.differentiableOn_dslope h0n).mpr hΦ
  have hΨcont : ContinuousOn (dslope Φ 0) U := hΨ.continuousOn
  -- Cauchy-Goursat for `dslope Φ 0` on the closed rectangle.
  have hsub : (Set.Icc a b ×ℂ Set.Icc (-R) R) ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨hre, him⟩ := hz
    rw [Set.mem_Icc] at hre him
    exact hmem z hre.1 hre.2 (abs_le.mpr ⟨him.1, him.2⟩)
  have hH : DifferentiableOn ℂ (dslope Φ 0) (Set.Icc a b ×ℂ Set.Icc (-R) R) :=
    hΨ.mono hsub
  set zc : ℂ := ⟨a, -R⟩ with hzc
  set wc : ℂ := ⟨b, R⟩ with hwc
  have hre_zc : zc.re = a := rfl
  have him_zc : zc.im = -R := rfl
  have hre_wc : wc.re = b := rfl
  have him_wc : wc.im = R := rfl
  have H' : DifferentiableOn ℂ (dslope Φ 0)
      (Set.uIcc zc.re wc.re ×ℂ Set.uIcc zc.im wc.im) := by
    rw [hre_zc, hre_wc, him_zc, him_wc,
      Set.uIcc_of_le hab, Set.uIcc_of_le hRle]
    exact hH
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dslope Φ 0) zc wc H'
  rw [hre_zc, hre_wc, him_zc, him_wc] at hCG
  have hrect0 : newman_rect (dslope Φ 0) a b R = 0 := by
    unfold newman_rect
    exact hCG
  -- Splitting `Φ z / z` off the origin.
  have hdecomp : ∀ w : ℂ, w ≠ 0 →
      Φ w / w = dslope Φ 0 w + Φ 0 * (1 / w) := by
    intro w hw
    have hw0 : w - 0 ≠ 0 := by simpa using hw
    rw [dslope_of_ne Φ hw, slope_def_field, sub_zero]
    field_simp
    ring
  -- The four paths: continuity, nonvanishing, landing in `U`.
  have hhor_cont : ∀ s : ℝ,
      Continuous (fun t : ℝ => (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I) := by
    intro s
    apply Continuous.add Complex.continuous_ofReal
    exact continuous_const.mul continuous_const
  have hver_cont : ∀ c : ℝ,
      Continuous (fun t : ℝ => (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I) := by
    intro c
    apply Continuous.add continuous_const
    exact Complex.continuous_ofReal.mul continuous_const
  have hhor0 : ∀ s : ℝ, s ≠ 0 → ∀ t : ℝ,
      (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro s hs t ht
    apply hs
    have hcon := congrArg Complex.im ht
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
      Complex.zero_im] at hcon
    exact hcon
  have hver0 : ∀ c : ℝ, c ≠ 0 → ∀ t : ℝ,
      (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro c hc t ht
    apply hc
    have hcon := congrArg Complex.re ht
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      sub_self, add_zero, Complex.zero_re] at hcon
    exact hcon
  have hhorU : ∀ s : ℝ, |s| ≤ R → ∀ t ∈ Set.uIcc a b,
      ((t : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ∈ U := by
    intro s hs t ht
    apply hmem
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      have htI : t ∈ Set.Icc a b := by
        rw [← Set.uIcc_of_le hab]
        exact ht
      exact (Set.mem_Icc.mp htI).1
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      have htI : t ∈ Set.Icc a b := by
        rw [← Set.uIcc_of_le hab]
        exact ht
      exact (Set.mem_Icc.mp htI).2
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
      exact hs
  have hverU : ∀ c : ℝ, a ≤ c → c ≤ b → ∀ t ∈ Set.uIcc (-R) R,
      ((c : ℂ) + ((t : ℝ) : ℂ) * Complex.I) ∈ U := by
    intro c hc1 hc2 t ht
    apply hmem
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      exact hc1
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      exact hc2
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
      have htI : t ∈ Set.Icc (-R) R := by
        rw [← Set.uIcc_of_le hRle]
        exact ht
      have hmem' := Set.mem_Icc.mp htI
      exact abs_le.mpr ⟨hmem'.1, hmem'.2⟩
  -- The four split integral equations.
  have hRne : (-R : ℝ) ≠ 0 := neg_ne_zero.mpr hR.ne'
  have hRne' : (R : ℝ) ≠ 0 := hR.ne'
  have hane : a ≠ 0 := ne_of_lt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have habsR : |(-R : ℝ)| ≤ R := by rw [abs_neg, abs_of_pos hR]
  have habsR' : |(R : ℝ)| ≤ R := by rw [abs_of_pos hR]
  have hintΨlo : IntervalIntegrable
      (fun x : ℝ => dslope Φ 0 ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume a b :=
    newman_comp_line_integrable _ _ hΨcont _ (hhor_cont (-R)) a b
      (hhorU (-R) habsR)
  have hintklo : IntervalIntegrable
      (fun x : ℝ => Φ 0 * ((1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)))
      volume a b :=
    newman_const_mul_line_integrable _ _ (hhor_cont (-R)) (hhor0 (-R) hRne) a b
  have eLo : (∫ x : ℝ in a..b,
        (fun z => Φ z / z) ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in a..b, dslope Φ 0 ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨlo hintklo]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    exact hdecomp _ (hhor0 (-R) hRne x)
  have hintΨhi : IntervalIntegrable
      (fun x : ℝ => dslope Φ 0 ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume a b :=
    newman_comp_line_integrable _ _ hΨcont _ (hhor_cont R) a b
      (hhorU R habsR')
  have hintkhi : IntervalIntegrable
      (fun x : ℝ => Φ 0 * ((1 : ℂ) / ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)))
      volume a b :=
    newman_const_mul_line_integrable _ _ (hhor_cont R) (hhor0 R hRne') a b
  have eHi : (∫ x : ℝ in a..b,
        (fun z => Φ z / z) ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in a..b, dslope Φ 0 ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨhi hintkhi]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    exact hdecomp _ (hhor0 R hRne' x)
  have hintΨrt : IntervalIntegrable
      (fun y : ℝ => dslope Φ 0 ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hΨcont _ (hver_cont b) (-R) R
      (hverU b hab le_rfl)
  have hintkrt : IntervalIntegrable
      (fun y : ℝ => Φ 0 * ((1 : ℂ) / ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I)))
      volume (-R) R :=
    newman_const_mul_line_integrable _ _ (hver_cont b) (hver0 b hbne) (-R) R
  have eRt : (∫ y : ℝ in (-R)..R,
        (fun z => Φ z / z) ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      = (∫ y : ℝ in (-R)..R, dslope Φ 0 ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨrt hintkrt]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y _
    exact hdecomp _ (hver0 b hbne y)
  have hintΨlf : IntervalIntegrable
      (fun y : ℝ => dslope Φ 0 ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hΨcont _ (hver_cont a) (-R) R
      (hverU a le_rfl hab)
  have hintklf : IntervalIntegrable
      (fun y : ℝ => Φ 0 * ((1 : ℂ) / ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I)))
      volume (-R) R :=
    newman_const_mul_line_integrable _ _ (hver_cont a) (hver0 a hane) (-R) R
  have eLf : (∫ y : ℝ in (-R)..R,
        (fun z => Φ z / z) ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      = (∫ y : ℝ in (-R)..R, dslope Φ 0 ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨlf hintklf]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y _
    exact hdecomp _ (hver0 a hane y)
  -- The `1 / z` rectangle is `2πi` (bridge to `PerronKernel`).
  have hperron := PerronKernel.boundary_rect_one_div ha hb hR
  rw [mul_sub] at hperron
  have hE : (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        + Complex.I * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        - Complex.I * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        = 2 * Real.pi * Complex.I := by
    simp only [Complex.ofReal_neg]
    linear_combination hperron
  -- Assembly.
  have hΨeq : (∫ x : ℝ in a..b,
          dslope Φ 0 ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in a..b,
          dslope Φ 0 ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        + Complex.I * (∫ y : ℝ in (-R)..R,
          dslope Φ 0 ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        - Complex.I * (∫ y : ℝ in (-R)..R,
          dslope Φ 0 ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        = 0 := by
    unfold newman_rect at hrect0
    simpa only [smul_eq_mul] using hrect0
  unfold newman_rect
  rw [eLo, eHi, eRt, eLf]
  simp only [smul_eq_mul]
  linear_combination hΨeq + Φ 0 * hE

/-- Helper: continuity of horizontal lines. -/
private lemma newman_hor_cont (s : ℝ) :
    Continuous (fun t : ℝ => (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I) := by
  apply Continuous.add Complex.continuous_ofReal
  exact continuous_const.mul continuous_const

/-- Helper: continuity of vertical lines. -/
private lemma newman_ver_cont (c : ℝ) :
    Continuous (fun t : ℝ => (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I) := by
  apply Continuous.add continuous_const
  exact Complex.continuous_ofReal.mul continuous_const

/-- Helper: horizontal lines with nonzero imaginary part avoid `0`. -/
private lemma newman_hor_ne (s : ℝ) (hs : s ≠ 0) (t : ℝ) :
    (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro ht
  apply hs
  have hcon := congrArg Complex.im ht
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
    Complex.zero_im] at hcon
  exact hcon

/-- Helper: vertical lines with nonzero real part avoid `0`. -/
private lemma newman_ver_ne (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro ht
  apply hc
  have hcon := congrArg Complex.re ht
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    sub_self, add_zero, Complex.zero_re] at hcon
  exact hcon

/-- Splitting the rectangle at `Re z = 0`. -/
private lemma newman_rect_split (Φ : ℂ → ℂ) (δ R : ℝ)
    (hlo : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (-δ) 0)
    (hhi : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (-δ) 0)
    (rlo : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume 0 R)
    (rhi : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume 0 R) :
    newman_rect Φ (-δ) R R = newman_JR Φ R + newman_JL Φ δ R := by
  unfold newman_rect newman_JR newman_JL
  rw [← intervalIntegral.integral_add_adjacent_intervals hlo rlo,
    ← intervalIntegral.integral_add_adjacent_intervals hhi rhi]
  abel

/-- Newman's integrand `F(z) = (G z - g_T z) * exp (z * T) * k_R z`. -/
private noncomputable def newman_F (f : ℝ → ℂ) (G : ℂ → ℂ) (T R : ℝ) (z : ℂ) : ℂ :=
  (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) * newman_kernel R z

/-- The `G`-part `F_G(z) = G z * exp (z * T) * k_R z`. -/
private noncomputable def newman_FG (G : ℂ → ℂ) (T R : ℝ) (z : ℂ) : ℂ :=
  G z * Complex.exp (z * (T : ℂ)) * newman_kernel R z

/-- The `g_T`-part `F_T(z) = g_T z * exp (z * T) * k_R z`. -/
private noncomputable def newman_FT (f : ℝ → ℂ) (T R : ℝ) (z : ℂ) : ℂ :=
  newman_partial f T z * Complex.exp (z * (T : ℂ)) * newman_kernel R z

/-- Shifting the left side out to `-R`. -/
private lemma newman_left_shift (Ψ : ℂ → ℂ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ < R)
    (hΨ : DifferentiableOn ℂ Ψ {z | z ≠ 0}) :
    newman_JL Ψ δ R = newman_JF Ψ R := by
  have hR : (0 : ℝ) < R := lt_trans hδ hδR
  have hRne : (-R : ℝ) ≠ 0 := neg_ne_zero.mpr hR.ne'
  have hRne' : (R : ℝ) ≠ 0 := hR.ne'
  have hΨcont : ContinuousOn Ψ {z | z ≠ 0} := hΨ.continuousOn
  -- Cauchy-Goursat on `[-R, -δ] × [-R, R]`, which avoids `0`.
  have hsub : (Set.uIcc (-R) (-δ) ×ℂ Set.uIcc (-R) R) ⊆ {z | z ≠ 0} := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨hre, -⟩ := hz
    rw [Set.uIcc_of_le (show -R ≤ -δ by linarith)] at hre
    have hle : z.re ≤ -δ := (Set.mem_Icc.mp hre).2
    intro h0
    rw [h0, Complex.zero_re] at hle
    linarith
  have H : DifferentiableOn ℂ Ψ (Set.uIcc (-R) (-δ) ×ℂ Set.uIcc (-R) R) :=
    hΨ.mono hsub
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn Ψ
    ((⟨-R, -R⟩ : ℂ)) ((⟨-δ, R⟩ : ℂ)) H
  -- Integrability for splitting the far-left horizontals at `-δ`.
  have i1 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-R) (-δ) :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-R) (-δ) (fun t _ => newman_hor_ne _ hRne t)
  have i2 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-δ) 0 (fun t _ => newman_hor_ne _ hRne t)
  have j1 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-R) (-δ) :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-R) (-δ) (fun t _ => newman_hor_ne _ hRne' t)
  have j2 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-δ) 0 (fun t _ => newman_hor_ne _ hRne' t)
  simp only [smul_eq_mul] at hCG
  unfold newman_JL newman_JF
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    ← intervalIntegral.integral_add_adjacent_intervals j1 j2]
  linear_combination -hCG

/-- The contour identity. -/
private lemma newman_contour_identity (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (R δ T : ℝ) (hδ : 0 < δ) (hδR : δ < R) (hT : 0 ≤ T)
    (hmem : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → AnalyticAt ℂ G z) :
    2 * Real.pi * Complex.I * (G 0 - newman_partial f T 0)
      = newman_JR (newman_F f G T R) R + newman_JL (newman_FG G T R) δ R
        - newman_JF (newman_FT f T R) R := by
  have hR0 : (0 : ℝ) < R := lt_trans hδ hδR
  have hnegδ : -δ ≤ (0 : ℝ) := by linarith
  have hleδR : -δ ≤ R := by linarith
  have hR2ne : ((R : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast hR0.ne')
  set U : Set ℂ := {z | AnalyticAt ℂ G z} with hUdef
  have hUopen : IsOpen U := isOpen_analyticAt ℂ G
  have hmemU : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → z ∈ U :=
    fun z h1 h2 h3 => hmem z h1 h2 h3
  -- Differentiability of the pieces.
  have hgT : Differentiable ℂ (newman_partial f T) :=
    newman_partial_differentiable f B hfmeas hB hbound T hT
  have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (z * (T : ℂ))) :=
    Complex.differentiable_exp.comp (differentiable_id.mul_const _)
  have hpoly : Differentiable ℂ (fun z : ℂ => 1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2) :=
    Differentiable.add (differentiable_const _)
      ((differentiable_id.pow 2).div (differentiable_const _) (fun _ => hR2ne))
  have hk : DifferentiableOn ℂ (newman_kernel R) {z | z ≠ 0} := by
    unfold newman_kernel
    apply DifferentiableOn.div
    · exact (Differentiable.add (differentiable_const _)
        ((differentiable_id.pow 2).div (differentiable_const _)
          (fun _ => hR2ne))).differentiableOn
    · exact differentiable_id.differentiableOn
    · intro z hz
      exact hz
  have hk_cont : ContinuousOn (newman_kernel R) {z | z ≠ 0} := hk.continuousOn
  have hGdiff : DifferentiableOn ℂ G U := by
    intro z hz
    have hza : AnalyticAt ℂ G z := hz
    exact hza.differentiableAt.differentiableWithinAt
  -- Continuity of the three integrands.
  have hFcont : ContinuousOn (newman_F f G T R) (U ∩ {z | z ≠ 0}) := by
    unfold newman_F
    exact (((hGdiff.continuousOn.mono Set.inter_subset_left).sub
      (hgT.continuous.continuousOn.mono (Set.subset_univ _))).mul
      (hexp.continuous.continuousOn.mono (Set.subset_univ _))).mul
      (hk_cont.mono Set.inter_subset_right)
  have hFGcont : ContinuousOn (newman_FG G T R) (U ∩ {z | z ≠ 0}) := by
    unfold newman_FG
    exact ((hGdiff.continuousOn.mono Set.inter_subset_left).mul
      (hexp.continuous.continuousOn.mono (Set.subset_univ _))).mul
      (hk_cont.mono Set.inter_subset_right)
  have hFTcont : ContinuousOn (newman_FT f T R) {z | z ≠ 0} := by
    unfold newman_FT
    exact ((hgT.continuous.continuousOn).mul hexp.continuous.continuousOn).mul
      hk_cont
  -- `Φ` is differentiable on `U`; identify `Φ z / z` with `F z`.
  have hΦdiff : DifferentiableOn ℂ
      (fun z => (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) *
        (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2)) U :=
    ((hGdiff.sub hgT.differentiableOn).mul hexp.differentiableOn).mul
      hpoly.differentiableOn
  have hΦF : (fun z => (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) *
        (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2) / z)
      = newman_F f G T R := by
    funext z
    unfold newman_F newman_kernel
    rw [mul_div_assoc]
  have hΦ0 : (G 0 - newman_partial f T 0) * Complex.exp ((0 : ℂ) * (T : ℂ)) *
        (1 + (0 : ℂ) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
      = G 0 - newman_partial f T 0 := by
    rw [zero_mul, Complex.exp_zero]
    simp
  have hN8 := newman_rect_cauchy_zero
    (fun z => (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) *
      (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2)) (-δ) R R
    (by linarith) hR0 hR0 U hUopen hΦdiff hmemU
  rw [hΦF, hΦ0] at hN8
  -- Segment membership.
  have hhor_seg : ∀ x s : ℝ, -δ ≤ x → x ≤ R → |s| = R →
      ((x : ℂ) + (s : ℂ) * Complex.I) ∈ U ∩ {z | z ≠ 0} := by
    intro x s h1 h2 hs
    have hre : ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hs
      linarith
    constructor
    · have e1 : -δ ≤ ((x : ℂ) + (s : ℂ) * Complex.I).re := by
        rw [hre]
        exact h1
      have e2 : ((x : ℂ) + (s : ℂ) * Complex.I).re ≤ R := by
        rw [hre]
        exact h2
      have e3 : |((x : ℂ) + (s : ℂ) * Complex.I).im| ≤ R := by
        rw [him, hs]
      exact hmemU _ e1 e2 e3
    · change ((x : ℂ) + (s : ℂ) * Complex.I) ≠ 0
      exact newman_hor_ne s hs0 x
  have hver_seg : ∀ y : ℝ, |y| ≤ R →
      (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ U ∩ {z | z ≠ 0} := by
    intro y hy
    have hre : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = -δ := by simp
    have him : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    have hδ0 : (-δ : ℝ) ≠ 0 := ne_of_lt (by linarith)
    constructor
    · have e1 : -δ ≤ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re := by
        rw [hre]
      have e2 : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re ≤ R := by
        rw [hre]
        linarith
      have e3 : |(((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).im| ≤ R := by
        rw [him]
        exact hy
      exact hmemU _ e1 e2 e3
    · change (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0
      exact newman_ver_ne (-δ) hδ0 y
  have hu_lo1 : ∀ t ∈ Set.uIcc (-δ) (0 : ℝ), -δ ≤ t ∧ t ≤ R := by
    intro t ht
    rw [Set.uIcc_of_le hnegδ] at ht
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
    exact ⟨h1, le_trans h2 hR0.le⟩
  have hu_lo2 : ∀ t ∈ Set.uIcc (0 : ℝ) R, -δ ≤ t ∧ t ≤ R := by
    intro t ht
    rw [Set.uIcc_of_le hR0.le] at ht
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
    exact ⟨le_trans hnegδ h1, h2⟩
  have hu_v : ∀ t ∈ Set.uIcc (-R) R, |t| ≤ R := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -R ≤ R)] at ht
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
    exact abs_le.mpr ⟨h1, h2⟩
  have habsRm : |(-R : ℝ)| = R := by rw [abs_neg, abs_of_pos hR0]
  have habsRp : |(R : ℝ)| = R := by rw [abs_of_pos hR0]
  -- Integrability battery.
  have intFlo1 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t (-R) h1 h2 habsRm)
  have intFlo2 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume 0 R :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      0 R (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo2 t ht
        exact hhor_seg t (-R) h1 h2 habsRm)
  have intFhi1 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t R h1 h2 habsRp)
  have intFhi2 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume 0 R :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      0 R (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo2 t ht
        exact hhor_seg t R h1 h2 habsRp)
  have intFGlo : IntervalIntegrable
      (fun x => newman_FG G T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFGcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t (-R) h1 h2 habsRm)
  have intFGhi : IntervalIntegrable
      (fun x => newman_FG G T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFGcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t R h1 h2 habsRp)
  have intFGv : IntervalIntegrable
      (fun y => newman_FG G T R (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hFGcont _ (newman_ver_cont _)
      (-R) R (fun t ht => hver_seg t (hu_v t ht))
  have intFTlo : IntervalIntegrable
      (fun x => newman_FT f T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFTcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact (hhor_seg t (-R) h1 h2 habsRm).2)
  have intFThi : IntervalIntegrable
      (fun x => newman_FT f T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFTcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact (hhor_seg t R h1 h2 habsRp).2)
  have intFTv : IntervalIntegrable
      (fun y => newman_FT f T R (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hFTcont _ (newman_ver_cont _)
      (-R) R (fun t ht => (hver_seg t (hu_v t ht)).2)
  -- Split the rectangle, then `F = F_G - F_T` on the left part.
  have hN9 := newman_rect_split (newman_F f G T R) δ R
    intFlo1 intFhi1 intFlo2 intFhi2
  rw [hN9] at hN8
  have hFsub : newman_F f G T R = newman_FG G T R - newman_FT f T R := by
    funext z
    change (G z - newman_partial f T z) * Complex.exp (z * ((T : ℝ) : ℂ)) * newman_kernel R z
      = (G z * Complex.exp (z * ((T : ℝ) : ℂ)) * newman_kernel R z
        - newman_partial f T z * Complex.exp (z * ((T : ℝ) : ℂ)) * newman_kernel R z)
    ring
  have hJL : newman_JL (newman_F f G T R) δ R
      = newman_JL (newman_FG G T R) δ R - newman_JL (newman_FT f T R) δ R := by
    unfold newman_JL
    simp only [hFsub, Pi.sub_apply]
    rw [intervalIntegral.integral_sub intFGlo intFTlo,
      intervalIntegral.integral_sub intFGhi intFThi,
      intervalIntegral.integral_sub intFGv intFTv,
      smul_sub]
    abel
  rw [hJL] at hN8
  -- Move the `g_T` piece out to `-R`.
  have hFTdiff : DifferentiableOn ℂ (newman_FT f T R) {z | z ≠ 0} := by
    unfold newman_FT
    exact (hgT.mul hexp).differentiableOn.mul hk
  have hN10 := newman_left_shift (newman_FT f T R) δ R hδ hδR hFTdiff
  rw [hN10] at hN8
  linear_combination -hN8

/-- Bound for the right part `J_R(F)`. -/
private lemma newman_right_part_bound (f : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    ‖newman_JR (newman_F f G T R) R‖ ≤ 10 * B / R := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  -- Pointwise bound on the horizontal sides.
  have hhor : ∀ s : ℝ, s = R ∨ s = -R → ∀ x ∈ Set.uIoc (0 : ℝ) R,
      ‖newman_F f G T R ((x : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * B / R ^ 2 := by
    intro s hs x hx
    rw [Set.uIoc_of_le hR.le] at hx
    have hx0 : (0 : ℝ) < x := (Set.mem_Ioc.mp hx).1
    have hx0' : x ≠ 0 := ne_of_gt hx0
    set z : ℂ := (x : ℂ) + ((s : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = x := by simp [hz]
    have hN5 := newman_tail_bound f B hbound G hG T hT z (by rw [hre]; exact hx0)
    rw [hre] at hN5
    have hN1 := newman_kernel_norm_horizontal R x hR s hs
    have hxabs : |x| = x := abs_of_pos hx0
    have hprod : B / x * (2 * |x| / R ^ 2) = 2 * B / R ^ 2 := by
      rw [hxabs]
      field_simp
    have hF : ‖newman_F f G T R z‖
        = ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_F
      rw [norm_mul]
    rw [hF]
    calc ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
        ≤ (B / x) * (2 * |x| / R ^ 2) :=
          mul_le_mul hN5 hN1 (norm_nonneg _) (div_nonneg hB hx0.le)
      _ = 2 * B / R ^ 2 := hprod
  -- Pointwise bound on the right side.
  have hver : ∀ y ∈ Set.uIoc (-R) R,
      ‖newman_F f G T R (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 3 * B / R ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith : -R ≤ R)] at hy
    have hyR : |y| ≤ R := abs_le.mpr ⟨(Set.mem_Ioc.mp hy).1.le, (Set.mem_Ioc.mp hy).2⟩
    set z : ℂ := ((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = R := by simp [hz]
    have hN5 := newman_tail_bound f B hbound G hG T hT z (by rw [hre]; exact hR)
    rw [hre] at hN5
    have hlo : R ≤ ‖z‖ := by
      calc R = |R| := (abs_of_pos hR).symm
        _ = |z.re| := by rw [hre]
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hhi : ‖z‖ ≤ 2 * R := by
      calc ‖z‖ ≤ ‖((R : ℝ) : ℂ)‖ + ‖((y : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |R| + |y| := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
              mul_one]
        _ ≤ R + R := by
            rw [abs_of_pos hR]
            exact add_le_add le_rfl hyR
        _ = 2 * R := by ring
    have hN2 := newman_kernel_norm_vertical R hR z hlo hhi
    have hprod : B / R * (3 / R) = 3 * B / R ^ 2 := by
      field_simp
    have hF : ‖newman_F f G T R z‖
        = ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_F
      rw [norm_mul]
    rw [hF]
    calc ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
        ≤ (B / R) * (3 / R) :=
          mul_le_mul hN5 hN2 (norm_nonneg _) (div_nonneg hB hR.le)
      _ = 3 * B / R ^ 2 := hprod
  -- The three integral bounds.
  have hlo_int : ‖∫ x : ℝ in (0 : ℝ)..R,
        newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor (-R) (Or.inr rfl))
    rw [sub_zero, abs_of_pos hR] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hhi_int : ‖∫ x : ℝ in (0 : ℝ)..R,
        newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor R (Or.inl rfl))
    rw [sub_zero, abs_of_pos hR] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hv_int : ‖∫ y : ℝ in (-R)..R,
        newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 6 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hver
    have hlen : |R - -R| = 2 * R := by
      rw [show (R - -R : ℝ) = 2 * R from by ring]
      exact abs_of_pos (by positivity)
    rw [hlen] at h
    have hfin : 3 * B / R ^ 2 * (2 * R) = 6 * B / R := by
      field_simp
      ring
    rwa [hfin] at h
  -- Assembly.
  have hJR : newman_JR (newman_F f G T R) R
      = (∫ x : ℝ in (0 : ℝ)..R,
          newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
        - (∫ x : ℝ in (0 : ℝ)..R,
          newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
        + Complex.I • (∫ y : ℝ in (-R)..R,
          newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := rfl
  have hsmul : ∀ X : ℂ, ‖Complex.I • X‖ = ‖X‖ := fun X => by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hJR]
  calc ‖(∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
          + Complex.I • (∫ y : ℝ in (-R)..R,
            newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ ‖(∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))‖
          + ‖Complex.I • (∫ y : ℝ in (-R)..R,
            newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖ :=
          norm_add_le _ _
      _ ≤ ((2 * B / R) + (2 * B / R)) + (6 * B / R) := by
          rw [hsmul]
          exact (add_le_add (norm_sub_le _ _) le_rfl).trans
            (add_le_add (add_le_add hlo_int hhi_int) hv_int)
      _ = 10 * B / R := by ring

/-- Bound for the far-left part `J_F(F_T)`. -/
private lemma newman_far_left_bound (f : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    ‖newman_JF (newman_FT f T R) R‖ ≤ 10 * B / R := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hC : (0 : ℝ) ≤ 2 * B / R ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) hB) (sq_nonneg R)
  -- Pointwise bound on the horizontal sides; the endpoint `x = 0` uses
  -- `k_R(±R·I) = 0` since it is not covered by N6.
  have hhor : ∀ s : ℝ, s = R ∨ s = -R → ∀ x ∈ Set.uIoc (-R) 0,
      ‖newman_FT f T R ((x : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * B / R ^ 2 := by
    intro s hs x hx
    rw [Set.uIoc_of_le (by linarith : -R ≤ (0 : ℝ))] at hx
    obtain ⟨hxlo, hxhi⟩ := Set.mem_Ioc.mp hx
    set z : ℂ := (x : ℂ) + ((s : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = x := by simp [hz]
    have hF : ‖newman_FT f T R z‖
        = ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_FT
      rw [norm_mul]
    have hN1 := newman_kernel_norm_horizontal R x hR s hs
    by_cases hx0 : x = 0
    · subst hx0
      rw [abs_zero] at hN1
      have hk0 : ‖newman_kernel R z‖ = 0 := by
        have hle : ‖newman_kernel R z‖ ≤ 2 * 0 / R ^ 2 := hN1
        rw [show (2 : ℝ) * 0 / R ^ 2 = 0 from by ring] at hle
        exact le_antisymm hle (norm_nonneg _)
      rw [hF, hk0, mul_zero]
      exact hC
    · have hxneg : x < 0 := lt_of_le_of_ne hxhi hx0
      have hx0' : x ≠ 0 := ne_of_lt hxneg
      have hN6 := newman_partial_bound_left f B hB hbound T hT z
        (by rw [hre]; exact hxneg)
      rw [hre] at hN6
      have hxabs : |x| = -x := abs_of_neg hxneg
      have hprod : B / -x * (2 * |x| / R ^ 2) = 2 * B / R ^ 2 := by
        rw [hxabs]
        field_simp
      rw [hF]
      calc ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
          ≤ (B / -x) * (2 * |x| / R ^ 2) :=
            mul_le_mul hN6 hN1 (norm_nonneg _) (div_nonneg hB (neg_nonneg.mpr hxneg.le))
        _ = 2 * B / R ^ 2 := hprod
  -- Pointwise bound on the left side.
  have hver : ∀ y ∈ Set.uIoc (-R) R,
      ‖newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 3 * B / R ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith : -R ≤ R)] at hy
    have hyR : |y| ≤ R := abs_le.mpr ⟨(Set.mem_Ioc.mp hy).1.le, (Set.mem_Ioc.mp hy).2⟩
    set z : ℂ := (((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = -R := by simp [hz]
    have hnegR : z.re < 0 := by rw [hre]; linarith
    have hN6 := newman_partial_bound_left f B hB hbound T hT z hnegR
    have hRneg : -z.re = R := by rw [hre]; ring
    rw [hRneg] at hN6
    have hlo : R ≤ ‖z‖ := by
      calc R = |R| := (abs_of_pos hR).symm
        _ = |(-R : ℝ)| := by rw [abs_neg, abs_of_pos hR]
        _ = |z.re| := by rw [hre]
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hhi : ‖z‖ ≤ 2 * R := by
      calc ‖z‖ ≤ ‖(((-R : ℝ)) : ℂ)‖ + ‖((y : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |(-R : ℝ)| + |y| := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
              mul_one]
        _ ≤ R + R := by
            rw [abs_neg, abs_of_pos hR]
            exact add_le_add le_rfl hyR
        _ = 2 * R := by ring
    have hN2 := newman_kernel_norm_vertical R hR z hlo hhi
    have hprod : B / R * (3 / R) = 3 * B / R ^ 2 := by
      field_simp
    have hF : ‖newman_FT f T R z‖
        = ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_FT
      rw [norm_mul]
    rw [hF]
    calc ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
        ≤ (B / R) * (3 / R) :=
          mul_le_mul hN6 hN2 (norm_nonneg _) (div_nonneg hB hR.le)
      _ = 3 * B / R ^ 2 := hprod
  -- The three integral bounds.
  have hlo_int : ‖∫ x : ℝ in (-R)..(0 : ℝ),
        newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor (-R) (Or.inr rfl))
    have hlen : |(0 : ℝ) - -R| = R := by
      have hrr : ((0 : ℝ) - -R) = R := by ring
      rw [hrr]
      exact abs_of_pos hR
    rw [hlen] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hhi_int : ‖∫ x : ℝ in (-R)..(0 : ℝ),
        newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor R (Or.inl rfl))
    have hlen : |(0 : ℝ) - -R| = R := by
      have hrr : ((0 : ℝ) - -R) = R := by ring
      rw [hrr]
      exact abs_of_pos hR
    rw [hlen] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hv_int : ‖∫ y : ℝ in (-R)..R,
        newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 6 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hver
    have hlen : |R - -R| = 2 * R := by
      rw [show (R - -R : ℝ) = 2 * R from by ring]
      exact abs_of_pos (by positivity)
    rw [hlen] at h
    have hfin : 3 * B / R ^ 2 * (2 * R) = 6 * B / R := by
      field_simp
      ring
    rwa [hfin] at h
  -- Assembly.
  have hJF : newman_JF (newman_FT f T R) R
      = (∫ x : ℝ in (-R)..(0 : ℝ),
          newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
        - (∫ x : ℝ in (-R)..(0 : ℝ),
          newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
        - Complex.I • (∫ y : ℝ in (-R)..R,
          newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := rfl
  have hsmul : ∀ X : ℂ, ‖Complex.I • X‖ = ‖X‖ := fun X => by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hJF]
  calc ‖(∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
          - Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ ‖(∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))‖
          + ‖Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖ :=
          norm_sub_le _ _
      _ ≤ ((2 * B / R) + (2 * B / R)) + (6 * B / R) := by
          rw [hsmul]
          exact (add_le_add (norm_sub_le _ _) le_rfl).trans
            (add_le_add (add_le_add hlo_int hhi_int) hv_int)
      _ = 10 * B / R := by ring

/-- Auxiliary: the `J_L(F_G)` estimate for fixed `T`, given a uniform
bound `M` for `‖G * k_R‖` on the three short segments. -/
private lemma newman_JL_FG_bound_aux (G : ℂ → ℂ) (R δ M T : ℝ)
    (hδ : 0 < δ) (hδR : δ < R) (hT : 0 < T) (hM0 : 0 ≤ M)
    (hseg1 : ∀ x ∈ Set.Icc (-δ) 0,
      ‖G (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)‖ ≤ M)
    (hseg2 : ∀ x ∈ Set.Icc (-δ) 0,
      ‖G (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)‖ ≤ M)
    (hseg3 : ∀ y ∈ Set.Icc (-R) R,
      ‖G ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
        * newman_kernel R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤ M) :
    ‖newman_JL (newman_FG G T R) δ R‖
      ≤ 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by
  have hR : (0 : ℝ) < R := lt_trans hδ hδR
  have hnegδ : -δ ≤ (0 : ℝ) := neg_nonpos.mpr hδ.le
  have hRle : -R ≤ R := by linarith
  -- Norm of `F_G` in terms of `‖G * k_R‖`.
  have hFGnorm : ∀ z : ℂ, ‖newman_FG G T R z‖
      = ‖G z * newman_kernel R z‖ * Real.exp (z.re * T) := by
    intro z
    have e1 : ‖Complex.exp (z * ((T : ℝ) : ℂ))‖ = Real.exp (z.re * T) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp only [newman_FG, norm_mul, e1]
    ring
  -- The exponential majorant is interval-integrable.
  have hg_cont : Continuous (fun x : ℝ => M * Real.exp (T * x)) :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id'))
  have hg_int : IntervalIntegrable (fun x : ℝ => M * Real.exp (T * x))
      volume (-δ) 0 :=
    hg_cont.intervalIntegrable _ _
  -- Exact value of the majorant integral.
  have hval : (∫ x : ℝ in (-δ)..(0 : ℝ), M * Real.exp (T * x))
      = M * (T⁻¹ * (1 - Real.exp (T * -δ))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left _ hT.ne', smul_eq_mul]
    simp only [mul_zero, integral_exp, Real.exp_zero]
  have hTδ : T * -δ = -δ * T := by ring
  have hfin : M * (T⁻¹ * (1 - Real.exp (-δ * T))) ≤ M / T := by
    have h1 : T⁻¹ * (1 - Real.exp (-δ * T)) ≤ T⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (sub_le_self 1 (Real.exp_nonneg _))
        (inv_nonneg.mpr hT.le)
    rw [mul_one] at h1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h1 hM0
  -- Estimate on one horizontal side.
  have hside : ∀ s : ℝ, s = R ∨ s = -R →
      (∀ x ∈ Set.Icc (-δ) 0,
        ‖G (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
          * newman_kernel R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ M) →
      ‖∫ x : ℝ in (-δ)..(0 : ℝ),
        newman_FG G T R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ M / T := by
    intro s hs hseg
    have hpt : ∀ᵐ x : ℝ ∂volume, x ∈ Set.Ioc (-δ) 0 →
        ‖newman_FG G T R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖
          ≤ M * Real.exp (T * x) := by
      apply ae_of_all
      intro x hx
      have hxI : x ∈ Set.Icc (-δ) 0 := Set.Ioc_subset_Icc_self hx
      have hre : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re = x := by simp
      have h1 : ‖G (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
          * newman_kernel R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ M :=
        hseg x hxI
      rw [hFGnorm, hre, mul_comm x T]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    have h := intervalIntegral.norm_integral_le_of_norm_le hnegδ hpt hg_int
    rw [hval, hTδ] at h
    exact le_trans h hfin
  -- Estimate on the left side.
  have hleft : ‖∫ y : ℝ in (-R)..R,
        newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 2 * R * M * Real.exp (-δ * T) := by
    have hpt : ∀ y ∈ Set.uIoc (-R) R,
        ‖newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
          ≤ M * Real.exp (-δ * T) := by
      intro y hy
      rw [Set.uIoc_of_le hRle] at hy
      have hyI : y ∈ Set.Icc (-R) R := Set.Ioc_subset_Icc_self hy
      have hre : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re = -δ := by
        simp
      have h1 : ‖G ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
          * newman_kernel R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤ M :=
        hseg3 y hyI
      rw [hFGnorm, hre]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have hlen : |R - -R| = 2 * R := by
      rw [show (R - -R : ℝ) = 2 * R from by ring]
      exact abs_of_pos (by positivity)
    rw [hlen] at h
    calc ‖∫ y : ℝ in (-R)..R,
            newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
          ≤ M * Real.exp (-δ * T) * (2 * R) := h
        _ = 2 * R * M * Real.exp (-δ * T) := by ring
  -- Assembly.
  have hJL : newman_JL (newman_FG G T R) δ R
      = (∫ x : ℝ in (-δ)..(0 : ℝ),
          newman_FG G T R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
        - (∫ x : ℝ in (-δ)..(0 : ℝ),
          newman_FG G T R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
        - Complex.I • (∫ y : ℝ in (-R)..R,
          newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := rfl
  have hsmul : ∀ X : ℂ, ‖Complex.I • X‖ = ‖X‖ := fun X => by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hJL]
  calc ‖(∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
          - Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ ‖(∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))‖
          + ‖Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖ :=
          norm_sub_le _ _
      _ ≤ (M / T + M / T) + (2 * R * M * Real.exp (-δ * T)) := by
          rw [hsmul]
          exact (add_le_add (norm_sub_le _ _) le_rfl).trans
            (add_le_add
              (add_le_add (hside (-R) (Or.inr rfl) hseg1)
                (hside R (Or.inl rfl) hseg2))
              hleft)
      _ = 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by ring

/-- The uniform bound `M` for the left part, from compactness. -/
private lemma newman_left_part_bound (G : ℂ → ℂ) (R δ : ℝ) (hδ : 0 < δ) (hδR : δ < R)
    (hmem : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → AnalyticAt ℂ G z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖newman_JL (newman_FG G T R) δ R‖
        ≤ 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by
  have hR : (0 : ℝ) < R := lt_trans hδ hδR
  have hRne : (-R : ℝ) ≠ 0 := neg_ne_zero.mpr hR.ne'
  have hδne : (-δ : ℝ) ≠ 0 := ne_of_lt (by linarith : -δ < 0)
  have habsRm : |(-R : ℝ)| = R := by rw [abs_neg, abs_of_pos hR]
  have habsRp : |(R : ℝ)| = R := abs_of_pos hR
  -- `G` is continuous on its analyticity set; `k_R` is continuous off `0`.
  have hGcont : ContinuousOn G {z | AnalyticAt ℂ G z} := by
    intro z hz
    exact hz.continuousAt.continuousWithinAt
  have hR2ne : ((R : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast hR.ne')
  have hk : DifferentiableOn ℂ (newman_kernel R) {z | z ≠ 0} := by
    unfold newman_kernel
    apply DifferentiableOn.div
    · exact (Differentiable.add (differentiable_const _)
        ((differentiable_id.pow 2).div (differentiable_const _)
          (fun _ => hR2ne))).differentiableOn
    · exact differentiable_id.differentiableOn
    · intro z hz
      exact hz
  have hk_cont : ContinuousOn (newman_kernel R) {z | z ≠ 0} := hk.continuousOn
  -- The three segments land in the analyticity set.
  have hsegU : ∀ x ∈ Set.Icc (-δ) 0, ∀ s : ℝ, |s| = R →
      (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ∈ {z | AnalyticAt ℂ G z} := by
    intro x hx s hs
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have hre : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re = x := by simp
    have him : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).im = s := by simp
    have e1 : -δ ≤ ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re := by
      rw [hre]; exact hx1
    have e2 : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re ≤ R := by
      rw [hre]; exact le_trans hx2 hR.le
    have e3 : |((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).im| ≤ R := by
      rw [him, hs]
    exact hmem _ e1 e2 e3
  have hvsegU : ∀ y ∈ Set.Icc (-R) R,
      ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
        ∈ {z | AnalyticAt ℂ G z} := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hre : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re = -δ := by simp
    have him : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).im = y := by simp
    have e1 : -δ ≤ (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re := by
      rw [hre]
    have e2 : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re ≤ R := by
      rw [hre]; linarith
    have e3 : |(((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).im| ≤ R := by
      rw [him]; exact abs_le.mpr ⟨hy1, hy2⟩
    exact hmem _ e1 e2 e3
  -- Continuity of `G * k_R` along the three segments.
  have hc1 : ContinuousOn (fun x : ℝ =>
      G (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
      (Set.Icc (-δ) 0) := by
    exact ((hGcont.comp ((newman_hor_cont (-R)).continuousOn.mono (Set.subset_univ _))
      (fun x hx => hsegU x hx (-R) habsRm)).mul
      (hk_cont.comp ((newman_hor_cont (-R)).continuousOn.mono (Set.subset_univ _))
        (fun x _ => newman_hor_ne (-R) hRne x)))
  have hc2 : ContinuousOn (fun x : ℝ =>
      G (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
      (Set.Icc (-δ) 0) := by
    exact ((hGcont.comp ((newman_hor_cont R).continuousOn.mono (Set.subset_univ _))
      (fun x hx => hsegU x hx R habsRp)).mul
      (hk_cont.comp ((newman_hor_cont R).continuousOn.mono (Set.subset_univ _))
        (fun x _ => newman_hor_ne R hR.ne' x)))
  have hc3 : ContinuousOn (fun y : ℝ =>
      G ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
        * newman_kernel R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      (Set.Icc (-R) R) := by
    exact ((hGcont.comp ((newman_ver_cont (-δ)).continuousOn.mono (Set.subset_univ _))
      (fun y hy => hvsegU y hy)).mul
      (hk_cont.comp ((newman_ver_cont (-δ)).continuousOn.mono (Set.subset_univ _))
        (fun y _ => newman_ver_ne (-δ) hδne y)))
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  obtain ⟨C₃, hC₃⟩ := isCompact_Icc.exists_bound_of_continuousOn hc3
  have hM0 : (0 : ℝ) ≤ max C₁ (max C₂ (max C₃ 0)) := by
    have e1 : (0 : ℝ) ≤ max C₃ 0 := le_max_right _ _
    have e2 : max C₃ (0 : ℝ) ≤ max C₂ (max C₃ 0) := le_max_right _ _
    have e3 : max C₂ (max C₃ (0 : ℝ)) ≤ max C₁ (max C₂ (max C₃ 0)) :=
      le_max_right _ _
    exact le_trans e1 (le_trans e2 e3)
  have hC₁M : C₁ ≤ max C₁ (max C₂ (max C₃ 0)) := le_max_left _ _
  have hC₂M : C₂ ≤ max C₁ (max C₂ (max C₃ 0)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₃M : C₃ ≤ max C₁ (max C₂ (max C₃ 0)) :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨max C₁ (max C₂ (max C₃ 0)), hM0, fun T hT => ?_⟩
  exact newman_JL_FG_bound_aux G R δ _ T hδ hδR hT hM0
    (fun x hx => le_trans (hC₁ x hx) hC₁M)
    (fun x hx => le_trans (hC₂ x hx) hC₂M)
    (fun y hy => le_trans (hC₃ y hy) hC₃M)

/-- The Newman estimate. -/
private lemma newman_newman_estimate (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG_analytic : AnalyticOnNhd ℂ G {s | 0 ≤ s.re})
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (R : ℝ) (hR : 0 < R) :
    ∃ δ M : ℝ, 0 < δ ∧ δ < R ∧ 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      2 * Real.pi * ‖G 0 - newman_partial f T 0‖
        ≤ 20 * B / R + 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by
  obtain ⟨δ, hδ, hδR, hmem⟩ := newman_exists_delta G hG_analytic R hR
  obtain ⟨M, hM0, hM⟩ := newman_left_part_bound G R δ hδ hδR hmem
  refine ⟨δ, M, hδ, hδR, hM0, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hN11 := newman_contour_identity f B hfmeas hB hbound G R δ T hδ hδR hT0 hmem
  have h12 := newman_right_part_bound f B hB hbound G hG R T hR hT0
  have h13 := newman_far_left_bound f B hB hbound R T hR hT0
  have h14 := hM T hT
  have h2 : ‖(2 : ℂ)‖ = 2 := RCLike.norm_two
  have hnorm : ‖2 * Real.pi * Complex.I * (G 0 - newman_partial f T 0)‖
      = 2 * Real.pi * ‖G 0 - newman_partial f T 0‖ := by
    rw [norm_mul, norm_mul, norm_mul, h2, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [← hnorm, hN11]
  calc ‖newman_JR (newman_F f G T R) R + newman_JL (newman_FG G T R) δ R
          - newman_JF (newman_FT f T R) R‖
        ≤ ‖newman_JR (newman_F f G T R) R‖ + ‖newman_JL (newman_FG G T R) δ R‖
          + ‖newman_JF (newman_FT f T R) R‖ := by
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (10 * B / R) + (2 * M / T + 2 * R * M * Real.exp (-δ * T))
          + (10 * B / R) :=
          add_le_add (add_le_add h12 h14) h13
      _ = 20 * B / R + 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by ring

/-- Newman's Tauberian theorem: a bounded measurable function on the positive ray
whose Laplace transform extends analytically to the closed right half-plane has
convergent partial integrals tending to the value at zero. -/
theorem newman_tauberian (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG_analytic : AnalyticOnNhd ℂ G {s | 0 ≤ s.re})
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s)) :
    Filter.Tendsto (fun T : ℝ => ∫ t : ℝ in (0 : ℝ)..T, f t)
      Filter.atTop (𝓝 (G 0)) := by
  -- The partial transform at `0` is the ordinary integral.
  have hpart0 : ∀ T : ℝ, newman_partial f T 0 = ∫ t : ℝ in (0 : ℝ)..T, f t := by
    intro T
    have heq : (fun t : ℝ => Complex.exp (-(0 : ℂ) * (t : ℂ)) * f t) = f := by
      funext t
      simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul]
    unfold newman_partial
    rw [heq]
  suffices hsuff : Filter.Tendsto (fun T : ℝ => newman_partial f T 0)
      Filter.atTop (𝓝 (G 0)) by
    exact Filter.Tendsto.congr hpart0 hsuff
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hπε : (0 : ℝ) < Real.pi * ε := mul_pos Real.pi_pos hε
  -- Choice of `R` making `20 * B / R < π * ε`.
  set R : ℝ := max 1 (20 * B / (Real.pi * ε) + 1) with hR
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBR : 20 * B / R < Real.pi * ε := by
    have hRge : 20 * B / (Real.pi * ε) + 1 ≤ R := le_max_right _ _
    rw [div_lt_iff₀ hR0]
    have h1 : Real.pi * ε * (20 * B / (Real.pi * ε) + 1)
        = 20 * B + Real.pi * ε := by
      rw [mul_add, mul_div_cancel₀ _ hπε.ne', mul_one]
    have h2 : Real.pi * ε * (20 * B / (Real.pi * ε) + 1) ≤ Real.pi * ε * R :=
      mul_le_mul_of_nonneg_left hRge hπε.le
    linarith
  obtain ⟨δ, M, hδ, hδR, hM0, hest⟩ :=
    newman_newman_estimate f B hfmeas hB hbound G hG_analytic hG R hR0
  -- The `M`-terms tend to `0`.
  have hlim1 : Filter.Tendsto (fun T : ℝ => 2 * M / T) Filter.atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun T : ℝ => (2 * M) * T⁻¹) Filter.atTop
        (𝓝 ((2 * M) * 0)) :=
      tendsto_const_nhds.mul tendsto_inv_atTop_zero
    rw [mul_zero] at h
    have e : (fun T : ℝ => 2 * M / T) = fun T => (2 * M) * T⁻¹ :=
      funext fun T => div_eq_mul_inv _ _
    rw [e]
    exact h
  have hδT : Filter.Tendsto (fun T : ℝ => δ * T) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  have hexp0 : Filter.Tendsto (fun T : ℝ => Real.exp (-(δ * T))) Filter.atTop
      (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hδT
  have hlim2 : Filter.Tendsto (fun T : ℝ => 2 * R * M * Real.exp (-δ * T))
      Filter.atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun T : ℝ => (2 * R * M) * Real.exp (-(δ * T)))
        Filter.atTop (𝓝 ((2 * R * M) * 0)) :=
      tendsto_const_nhds.mul hexp0
    rw [mul_zero] at h
    have e : (fun T : ℝ => 2 * R * M * Real.exp (-δ * T))
        = fun T => (2 * R * M) * Real.exp (-(δ * T)) := by
      funext T
      rw [neg_mul]
    rw [e]
    exact h
  have hlim : Filter.Tendsto
      (fun T : ℝ => 2 * M / T + 2 * R * M * Real.exp (-δ * T))
      Filter.atTop (𝓝 (0 + 0)) :=
    hlim1.add hlim2
  rw [add_zero] at hlim
  have hev := hlim.eventually_lt_const hπε
  have hev0 : ∀ᶠ T : ℝ in Filter.atTop, 0 < T := Filter.eventually_gt_atTop 0
  have hev2 := hev.and hev0
  rw [Filter.eventually_atTop] at hev2
  obtain ⟨N', hN'⟩ := hev2
  refine ⟨max N' 1, fun T hT => ?_⟩
  have hTN : T ≥ N' := le_trans (le_max_left _ _) hT
  have hTpos : (0 : ℝ) < T :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hT)
  obtain ⟨hlt, -⟩ := hN' T hTN
  have hestT := hest T hTpos
  have h3 : 2 * Real.pi * ‖G 0 - newman_partial f T 0‖ < 2 * (Real.pi * ε) := by
    have h2 : 20 * B / R + (2 * M / T + 2 * R * M * Real.exp (-δ * T))
        < 2 * (Real.pi * ε) := by
      linarith [hBR, hlt]
    linarith [hestT, h2]
  have h4 : ‖G 0 - newman_partial f T 0‖ < ε := by
    by_contra hcon
    push Not at hcon
    have hle : 2 * Real.pi * ε ≤ 2 * Real.pi * ‖G 0 - newman_partial f T 0‖ :=
      mul_le_mul_of_nonneg_left hcon (by linarith [Real.pi_pos])
    linarith [h3, hle]
  rw [dist_eq_norm, norm_sub_rev]
  exact h4
end
end

/- TauberianPort.MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression -/
section
/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

open Filter MeasureTheory Set Topology
open scoped Asymptotics

namespace Chebyshev

/-- Nonnegativity of the residue-class psi function. -/
private lemma wpa_psiResidueClass_nonneg {q : ℕ} (b : ZMod q) (x : ℝ) :
    0 ≤ psiResidueClass b x := by
  unfold psiResidueClass
  exact Finset.sum_nonneg fun n _ =>
    ArithmeticFunction.vonMangoldt.residueClass_nonneg b n

/-- The residue-class psi function is bounded by the full psi function. -/
private lemma wpa_psiResidueClass_le_psi {q : ℕ} (b : ZMod q) (x : ℝ) :
    psiResidueClass b x ≤ psi x := by
  simp only [psiResidueClass, psi]
  exact Finset.sum_le_sum fun n _ =>
    ArithmeticFunction.vonMangoldt.residueClass_le b n

/-- Monotonicity of the residue-class psi function. -/
private lemma wpa_psiResidueClass_mono {q : ℕ} (b : ZMod q) :
    Monotone (psiResidueClass b) := by
  intro x y hxy
  simp only [psiResidueClass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc (by rfl) (by gcongr)
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt.residueClass_nonneg b n

/-- Linear upper bound for the residue-class psi function. -/
private lemma wpa_psiResidueClass_le_mul_self {q : ℕ} (b : ZMod q) {x : ℝ}
    (hx : 0 ≤ x) :
    psiResidueClass b x ≤ (Real.log 4 + 4) * x :=
  le_trans (wpa_psiResidueClass_le_psi b x) (psi_le_const_mul_self hx)

/-- The residue-class psi function at a natural number is a sum over `Icc 1 n`. -/
private lemma wpa_psiResidueClass_natCast_eq {q : ℕ} (b : ZMod q) (n : ℕ) :
    psiResidueClass b (n : ℝ)
      = ∑ k ∈ Finset.Icc 1 n,
        ArithmeticFunction.vonMangoldt.residueClass b k := by
  simp only [psiResidueClass, Nat.floor_natCast,
    ← Finset.Icc_add_one_left_eq_Ioc]
  rfl

/-- The `Finset.range` sum in the Wanted statement equals `psiResidueClass`. -/
private lemma wpa_sum_range_ite_mod_eq {q a : ℕ} (ha_lt : a < q) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1),
      if n % q = a then ArithmeticFunction.vonMangoldt n else 0)
      = psiResidueClass (a : ZMod q) (M : ℝ) := by
  have key : ∀ n : ℕ, (if n % q = a then ArithmeticFunction.vonMangoldt n else 0)
      = ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n := by
    intro n
    have hiff : ((n : ZMod q) = (a : ZMod q)) ↔ (n % q = a) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha_lt]
    by_cases h : n % q = a
    · have hmem : n ∈ {n : ℕ | ((n : ZMod q) = (a : ZMod q))} := hiff.mpr h
      rw [if_pos h]
      exact (Set.indicator_of_mem hmem _).symm
    · have hmem : n ∉ {n : ℕ | ((n : ZMod q) = (a : ZMod q))} :=
        fun hm => h (hiff.mp hm)
      rw [if_neg h]
      exact (Set.indicator_of_notMem hmem _).symm
  have h0 : (if 0 % q = a then ArithmeticFunction.vonMangoldt 0 else 0) = 0 := by
    split_ifs with h
    · exact ArithmeticFunction.map_zero
    · rfl
  calc (∑ n ∈ Finset.range (M + 1),
          if n % q = a then ArithmeticFunction.vonMangoldt n else 0)
      = ∑ n ∈ Finset.Icc 0 M,
          (if n % q = a then ArithmeticFunction.vonMangoldt n else 0) := by
        rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
    _ = (if 0 % q = a then ArithmeticFunction.vonMangoldt 0 else 0)
          + ∑ n ∈ Finset.Ioc 0 M,
            (if n % q = a then ArithmeticFunction.vonMangoldt n else 0) := by
        rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le M), Finset.sum_cons]
    _ = ∑ n ∈ Finset.Ioc 0 M,
          ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n := by
        rw [h0, zero_add]
        exact Finset.sum_congr rfl (fun n _ => key n)
    _ = psiResidueClass (a : ZMod q) (M : ℝ) := by
        rw [psiResidueClass, Nat.floor_natCast]

/-- `LFunctionTrivChar₁` does not vanish on `re s ≥ 1`. -/
private lemma wpa_LFunctionTrivChar₁_ne_zero {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 1 ≤ s.re) :
    DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
  · unfold DirichletCharacter.LFunctionTrivChar₁
    rw [Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero_of_ne hs1)
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (.inr hs1) hs)

/-- Laplace transform of a partial-sum function in exponential time. -/
private lemma wpa_hasLaplace_partialSum_exp (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, f k ≤ C * (n : ℝ))
    (s : ℂ) (hs : 1 < s.re) :
    HasLaplace (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ))
      s (LSeries (fun n => (f n : ℂ)) s / s) := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    norm_num at hs
  have hmono : Monotone (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k) := by
    intro t₁ t₂ h
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc le_rfl
        (Nat.floor_mono (Real.exp_le_exp.mpr h))
    · intro k _ _
      exact hf k
  have hb : ∀ t : ℝ, 0 ≤ t →
      ‖(((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ)) : ℂ)‖
        ≤ C * Real.exp (1 * t) := by
    intro t _
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => hf k)]
    calc (∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k)
        ≤ C * (⌊Real.exp t⌋₊ : ℝ) := hbound _
      _ ≤ C * Real.exp t := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact Nat.floor_le (le_of_lt (Real.exp_pos t))
      _ = C * Real.exp (1 * t) := by rw [one_mul]
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.comp
      hmono.measurable).aestronglyMeasurable
  have hconv : LaplaceConvergent
      (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ)) s :=
    laplaceConvergent_of_norm_le_exp _ 1 C hmeas hC hb hs
  have hO : (fun n => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards with n
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => hf k),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
      Real.rpow_one]
    exact hbound n
  have hL := LSeries_eq_mul_integral_of_nonneg f zero_le_one hs hO hf
  have hchange := MeasureTheory.integral_comp_exp_Ioi
    (fun y : ℝ => (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (f k : ℂ)) *
      ((y : ℝ) : ℂ) ^ (-(s + 1))) 0
  rw [Real.exp_zero] at hchange
  have hpt : ∀ u : ℝ, Complex.exp (-s * (u : ℂ))
        • ((((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, f k : ℝ))) : ℂ)
      = Real.exp u •
        ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (f k : ℂ)) *
          (((Real.exp u : ℝ)) : ℂ) ^ (-(s + 1))) := by
    intro u
    have he : ((((Real.exp u : ℝ))) : ℂ) ≠ 0 := by
      exact_mod_cast Real.exp_ne_zero u
    have hlog : Complex.log ((((Real.exp u : ℝ))) : ℂ) = (u : ℂ) := by
      rw [← Complex.ofReal_log (le_of_lt (Real.exp_pos u)), Real.log_exp]
    have hcpow : ((((Real.exp u : ℝ))) : ℂ) ^ (-(s + 1))
        = Complex.exp (-(s + 1) * (u : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero he, hlog]
      congr 1
      ring
    have hexp : ((((Real.exp u : ℝ))) : ℂ) = Complex.exp (u : ℂ) :=
      Complex.ofReal_exp u
    have e : Complex.exp (u : ℂ) * Complex.exp (-(s + 1) * (u : ℂ))
        = Complex.exp (-s * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [Complex.ofReal_sum, RCLike.real_smul_eq_coe_mul, smul_eq_mul, hcpow,
      RCLike.ofReal_eq_complex_ofReal, hexp]
    linear_combination
      -(∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (f k : ℂ)) * e
  have hval : laplace
      (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ)) s
      = LSeries (fun n => (f n : ℂ)) s / s := by
    have hlap : laplace
          (fun t : ℝ => ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, f k : ℝ) : ℂ)) s
        = ∫ u : ℝ in Set.Ioi 0, Real.exp u •
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (f k : ℂ)) *
            (((Real.exp u : ℝ)) : ℂ) ^ (-(s + 1))) := by
      unfold laplace
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u _ => hpt u)
    rw [hlap, hchange, hL, mul_div_cancel_left₀ _ hs0]
  exact ⟨hconv, hval⟩

/-- The residue-class auxiliary function is analytic on `re s ≥ 1`. -/
private lemma wpa_analyticOnNhd_LFunctionResidueClassAux {q : ℕ} [NeZero q]
    (b : ZMod q) :
    AnalyticOnNhd ℂ (ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b)
      {s | 1 ≤ s.re} := by
  classical
  have hT : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ q)
      Set.univ :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn.analyticOnNhd
      isOpen_univ
  have hT' : AnalyticOnNhd ℂ (DirichletCharacter.LFunctionTrivChar₁ q)
      {s | 1 ≤ s.re} := hT.mono (Set.subset_univ _)
  have hTd : AnalyticOnNhd ℂ
      (deriv (DirichletCharacter.LFunctionTrivChar₁ q)) {s | 1 ≤ s.re} :=
    hT.deriv.mono (Set.subset_univ _)
  have hdivT : AnalyticOnNhd ℂ
      (fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
        DirichletCharacter.LFunctionTrivChar₁ q s) {s | 1 ≤ s.re} :=
    hTd.div hT' (fun x hx => wpa_LFunctionTrivChar₁_ne_zero hx)
  have hnegT : AnalyticOnNhd ℂ
      (fun s => -(deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
        DirichletCharacter.LFunctionTrivChar₁ q s)) {s | 1 ≤ s.re} :=
    hdivT.neg
  have hsum : AnalyticOnNhd ℂ
      (∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
        fun s => ((χ b⁻¹ : ℂ) *
          deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s))
      {s | 1 ≤ s.re} := by
    apply Finset.analyticOnNhd_sum _ _
    intro χ hχ
    have hne : χ ≠ 1 := by
      simpa only [Finset.mem_compl, Finset.mem_singleton] using hχ
    have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
      (DirichletCharacter.differentiable_LFunction hne).differentiableOn.analyticOnNhd
        isOpen_univ
    have hL' : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
        {s | 1 ≤ s.re} := hL.mono (Set.subset_univ _)
    have hLd : AnalyticOnNhd ℂ
        (deriv (DirichletCharacter.LFunction χ)) {s | 1 ≤ s.re} :=
      hL.deriv.mono (Set.subset_univ _)
    have hdiv : AnalyticOnNhd ℂ
        (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s) {s | 1 ≤ s.re} :=
      hLd.div hL'
        (fun x hx =>
          DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hne) hx)
    have hmul : AnalyticOnNhd ℂ
        (fun s => (χ b⁻¹ : ℂ) *
          (deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)) {s | 1 ≤ s.re} :=
      analyticOnNhd_const.mul hdiv
    simpa only [mul_div_assoc] using hmul
  have hcomb : AnalyticOnNhd ℂ
      ((fun _ => (q.totient : ℂ)⁻¹) *
        ((-(fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
          DirichletCharacter.LFunctionTrivChar₁ q s)) -
        ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
          fun s => ((χ b⁻¹ : ℂ) *
            deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)))
      {s | 1 ≤ s.re} :=
    analyticOnNhd_const.mul (hnegT.sub hsum)
  have hEq : ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b =
      ((fun _ => (q.totient : ℂ)⁻¹) *
        ((-(fun s => deriv (DirichletCharacter.LFunctionTrivChar₁ q) s /
          DirichletCharacter.LFunctionTrivChar₁ q s)) -
        ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
          fun s => ((χ b⁻¹ : ℂ) *
            deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s))) := by
    unfold ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux
    funext s
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply,
      neg_div, mul_div_assoc]
    congr 3 <;> ext <;> simp
  rw [hEq]
  exact hcomb

/-- The continuation of the Laplace transform of the error function. -/
private noncomputable def wpaPsiErrorCont {q : ℕ} [NeZero q] (b : ZMod q)
    (s : ℂ) : ℂ :=
  ((q.totient : ℂ) *
      ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b (s + 1) - 1) /
    (s + 1)

/-- Analyticity of the error continuation on `re s ≥ 0`. -/
private lemma wpa_analyticOnNhd_psiErrorCont {q : ℕ} [NeZero q] (b : ZMod q) :
    AnalyticOnNhd ℂ (wpaPsiErrorCont b) {s | 0 ≤ s.re} := by
  have hbase := wpa_analyticOnNhd_LFunctionResidueClassAux (q := q) b
  have hAnalytic : AnalyticOnNhd ℂ (fun s : ℂ => s + 1) {s | 0 ≤ s.re} :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hMaps : Set.MapsTo (fun s : ℂ => s + 1) {s | 0 ≤ s.re}
      {s | 1 ≤ s.re} := by
    intro x hx
    change (1 : ℝ) ≤ ((fun s : ℂ => s + 1) x).re
    have hx' : (0 : ℝ) ≤ x.re := hx
    have hAdd : ((fun s : ℂ => s + 1) x).re = x.re + 1 := by simp
    linarith
  have hComp : AnalyticOnNhd ℂ
      (fun s : ℂ => (q.totient : ℂ) *
        ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b (s + 1))
      {s | 0 ≤ s.re} :=
    analyticOnNhd_const.mul (hbase.comp hAnalytic hMaps)
  have hSub : AnalyticOnNhd ℂ
      (fun s : ℂ => (q.totient : ℂ) *
        ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b (s + 1) - 1)
      {s | 0 ≤ s.re} :=
    hComp.sub analyticOnNhd_const
  have hNe : ∀ s ∈ {s : ℂ | 0 ≤ s.re}, (s + 1 : ℂ) ≠ 0 := by
    intro s hs h0
    simp only [Set.mem_ofPred_eq] at hs
    have hZero : (s + 1).re = 0 := by simp [h0]
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hDiv := hSub.div hAnalytic hNe
  exact hDiv

/-- The normalized residue-class psi error function. -/
private noncomputable def wpaPsiError {q : ℕ} (b : ZMod q) (t : ℝ) : ℝ :=
  (q.totient : ℝ) * psiResidueClass b (Real.exp t) * Real.exp (-t) - 1

/-- Measurability of the normalized error function. -/
private lemma wpa_measurable_psiError {q : ℕ} (b : ZMod q) :
    Measurable (wpaPsiError b) := by
  unfold wpaPsiError
  exact ((measurable_const.mul ((wpa_psiResidueClass_mono b).measurable.comp
    Real.measurable_exp)).mul
    (Real.measurable_exp.comp measurable_neg)).sub_const 1

/-- Uniform bound for the normalized error function. -/
private lemma wpa_abs_psiError_le {q : ℕ} (b : ZMod q) (t : ℝ) :
    |wpaPsiError b t| ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
  have hnn : (0 : ℝ) ≤ psiResidueClass b (Real.exp t) :=
    wpa_psiResidueClass_nonneg b _
  have hle : psiResidueClass b (Real.exp t)
      ≤ (Real.log 4 + 4) * Real.exp t :=
    wpa_psiResidueClass_le_mul_self b (le_of_lt (Real.exp_pos t))
  have hphi_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hexp_pos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hprod_nn : (0 : ℝ) ≤ (q.totient : ℝ) *
      psiResidueClass b (Real.exp t) * Real.exp (-t) :=
    mul_nonneg (mul_nonneg hphi_nn hnn) (le_of_lt hexp_pos)
  have hprod_le : (q.totient : ℝ) * psiResidueClass b (Real.exp t) *
      Real.exp (-t) ≤ (q.totient : ℝ) * (Real.log 4 + 4) := by
    calc (q.totient : ℝ) * psiResidueClass b (Real.exp t) * Real.exp (-t)
        ≤ ((q.totient : ℝ) * ((Real.log 4 + 4) * Real.exp t)) *
          Real.exp (-t) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hexp_pos)
          exact mul_le_mul_of_nonneg_left hle hphi_nn
      _ = (q.totient : ℝ) * (Real.log 4 + 4) *
          (Real.exp t * Real.exp (-t)) := by ring
      _ = (q.totient : ℝ) * (Real.log 4 + 4) := by rw [hexp, mul_one]
  have hB_nn : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) :=
    mul_nonneg hphi_nn (by
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith)
  rw [abs_le]
  unfold wpaPsiError
  constructor <;> linarith

/-- Laplace transform of the normalized error function. -/
private lemma wpa_hasLaplace_psiError {q : ℕ} [NeZero q] (b : ZMod q)
    (hb : IsUnit b) (s : ℂ) (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      (wpaPsiErrorCont b s) := by
  have hs1 : (1 : ℝ) < (s + 1).re := by
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log 4 :=
    Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have hS := wpa_hasLaplace_partialSum_exp
    (ArithmeticFunction.vonMangoldt.residueClass b)
    (fun n => ArithmeticFunction.vonMangoldt.residueClass_nonneg b n)
    (Real.log 4 + 4) (by
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith)
    (fun n => by
      rw [← wpa_psiResidueClass_natCast_eq b n]
      exact wpa_psiResidueClass_le_mul_self b (Nat.cast_nonneg n))
    (s + 1) hs1
  obtain ⟨hSconv, hSval⟩ := hS
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    norm_num at hs
  have hs1ne : s + 1 ≠ 0 := by
    intro h0
    have hZero : (s + 1).re = 0 := by simp [h0]
    have hAdd : (s + 1).re = s.re + 1 := by simp
    linarith
  have hphi : (q.totient : ℂ) ≠ 0 := by
    have hpos : 0 < q.totient :=
      Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast hpos.ne'
  have hNeg : (-s).re < 0 := by
    have hEq : (-s).re = -s.re := by simp
    linarith
  have hBaseInt := integrableOn_exp_mul_complex_Ioi hNeg 0
  have hEqFun2 : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
      = (fun t : ℝ => Complex.exp ((-s) * (t : ℂ))) := by
    funext t
    simp only [smul_eq_mul, mul_one, neg_mul]
  have h2 : IntegrableOn
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
      (Set.Ioi 0) := by
    rw [hEqFun2]
    exact hBaseInt
  have hExpEq : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) *
      ((Real.exp (-t) : ℝ) : ℂ)
      = Complex.exp (-(s + 1) * (t : ℂ)) := by
    intro t
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpsi : ∀ t : ℝ, psiResidueClass b (Real.exp t)
      = ∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b k := by
    intro t
    have e : Finset.Icc 1 ⌊Real.exp t⌋₊
        = Finset.Ioc 0 ⌊Real.exp t⌋₊ := by
      rw [← Finset.Icc_add_one_left_eq_Ioc]
      rfl
    rw [e, psiResidueClass]
  have hpsiC : ∀ t : ℝ, ((psiResidueClass b (Real.exp t) : ℝ) : ℂ)
      = ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ) :=
    fun t => congrArg _ (hpsi t)
  have hPoint : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) •
        ((wpaPsiError b t : ℝ) : ℂ)
      = (Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
        - (Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) := by
    intro t
    have hE := hExpEq t
    simp only [wpaPsiError, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_natCast, hpsiC]
    linear_combination
      ((q.totient : ℂ) *
        ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)) * hE
  have hEqFun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) •
        ((wpaPsiError b t : ℝ) : ℂ))
      = (fun t : ℝ => (Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
        - (Complex.exp (-s * (t : ℂ)) • (1 : ℂ))) := by
    funext t
    exact hPoint t
  have h1e : (fun t : ℝ => Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
      = (fun t : ℝ => (q.totient : ℂ) *
        (Complex.exp (-(s + 1) * (t : ℂ)) •
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ))) := by
    funext t
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have h1 : IntegrableOn (fun t : ℝ =>
      Complex.exp (-(s + 1) * (t : ℂ)) •
        ((q.totient : ℂ) *
          ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
      (Set.Ioi 0) := by
    rw [h1e]
    exact hSconv.const_mul _
  have hB : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
    have hphi_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    have hle : (0 : ℝ) ≤ Real.log 4 + 4 := by linarith
    have := mul_nonneg hphi_nn hle
    linarith
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖(((wpaPsiError b t : ℝ)) : ℂ)‖
        ≤ ((q.totient : ℝ) * (Real.log 4 + 4) + 1) * Real.exp (0 * t) := by
    intro t _
    rw [Complex.norm_real, Real.norm_eq_abs, zero_mul, Real.exp_zero, mul_one]
    exact wpa_abs_psiError_le b t
  have hmeasC : AEStronglyMeasurable
      (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Complex.measurable_ofReal.comp
      (wpa_measurable_psiError b)).aestronglyMeasurable
  have hconv0 : LaplaceConvergent
      (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s :=
    laplaceConvergent_of_norm_le_exp _ 0 _ hmeasC hB hbound hs
  have hIntEq : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-s * (t : ℂ)) • ((wpaPsiError b t : ℝ) : ℂ))
      = (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-(s + 1) * (t : ℂ)) •
            ((q.totient : ℂ) *
              ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
                ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
        - (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) := by
    rw [hEqFun]
    exact MeasureTheory.integral_sub h1 h2
  have hLap : laplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      = (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-s * (t : ℂ)) • ((wpaPsiError b t : ℝ) : ℂ)) := rfl
  have hThetaInt : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-(s + 1) * (t : ℂ)) •
          ((q.totient : ℂ) *
            ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
              ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ)))
      = (q.totient : ℂ) *
        (LSeries (fun n =>
          (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ))
          (s + 1) / (s + 1)) := by
    have hSint : (∫ t : ℝ in Set.Ioi 0,
          Complex.exp (-(s + 1) * (t : ℂ)) •
            ((∑ k ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
              ArithmeticFunction.vonMangoldt.residueClass b k : ℝ) : ℂ))
        = LSeries (fun n =>
          (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ)) (s + 1) /
          (s + 1) := hSval
    rw [h1e, MeasureTheory.integral_const_mul, hSint]
  have hRw : (∫ t : ℝ in Set.Ioi 0,
      Complex.exp (-s * (t : ℂ)) • (1 : ℂ)) = 1 / s := by
    have hEqInt : (∫ t : ℝ in Set.Ioi 0,
        Complex.exp (-s * (t : ℂ)) • (1 : ℂ))
        = (∫ t : ℝ in Set.Ioi 0, Complex.exp ((-s) * (t : ℂ))) := by
      congr 1
    have hConstBase := integral_exp_mul_complex_Ioi hNeg 0
    have hField : (-1 : ℂ) / (-s) = 1 / s := by field_simp
    have hRw0 : (∫ t : ℝ in Set.Ioi 0, Complex.exp ((-s) * (t : ℂ)))
        = (-1 : ℂ) / (-s) := by
      simpa using hConstBase
    rw [hEqInt, hRw0, hField]
  have hVal : laplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      = (q.totient : ℂ) *
        (LSeries (fun n =>
          (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ))
          (s + 1) / (s + 1)) - 1 / s := by
    rw [hLap, hIntEq, hThetaInt, hRw]
  have hmem : s + 1 ∈ {s : ℂ | 1 < s.re} := hs1
  have hAuxEq := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
    (a := b) hb hmem
  have hAuxEq' : ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux b
        (s + 1)
      = LSeries (fun n =>
        (ArithmeticFunction.vonMangoldt.residueClass b n : ℂ)) (s + 1)
        - (q.totient : ℂ)⁻¹ / ((s + 1) - 1) := hAuxEq
  have hFinal : laplace (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) s
      = wpaPsiErrorCont b s := by
    rw [hVal]
    unfold wpaPsiErrorCont
    rw [hAuxEq']
    have hsub : s + 1 - 1 = s := by ring
    rw [hsub]
    field_simp
    ring
  exact ⟨hconv0, hFinal⟩

/-- Convergence of the integral of the error function. -/
private lemma wpa_tendsto_integral_psiError {q : ℕ} [NeZero q] (b : ZMod q)
    (hb : IsUnit b) :
    ∃ L : ℝ, Filter.Tendsto
      (fun U : ℝ => ∫ u : ℝ in (0 : ℝ)..U, wpaPsiError b u)
      Filter.atTop (nhds L) := by
  have hmeas : Measurable (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (wpa_measurable_psiError b)
  have hfmeas : AEStronglyMeasurable
      (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hmeas.aestronglyMeasurable
  have hB : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
    have hphi_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    have hle : (0 : ℝ) ≤ Real.log 4 + 4 := by
      have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith
    have := mul_nonneg hphi_nn hle
    linarith
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖(((wpaPsiError b t : ℝ)) : ℂ)‖
        ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
    intro t _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact wpa_abs_psiError_le b t
  have hmain := newman_tauberian (fun t : ℝ => ((wpaPsiError b t : ℝ) : ℂ))
    ((q.totient : ℝ) * (Real.log 4 + 4) + 1) hfmeas hB hbound
    (wpaPsiErrorCont b)
    (wpa_analyticOnNhd_psiErrorCont b)
    (fun s hs => wpa_hasLaplace_psiError b hb s hs)
  refine ⟨(wpaPsiErrorCont b 0).re, ?_⟩
  have hcast : ∀ U : ℝ,
      ((∫ u : ℝ in (0 : ℝ)..U, ((wpaPsiError b u : ℝ) : ℂ)).re)
        = ∫ u : ℝ in (0 : ℝ)..U, wpaPsiError b u := by
    intro U
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have h2 := (Complex.continuous_re.tendsto
    (wpaPsiErrorCont b 0)).comp hmain
  have e : (fun U : ℝ => ∫ u : ℝ in (0 : ℝ)..U, wpaPsiError b u)
      = Complex.re ∘ (fun T : ℝ => ∫ u : ℝ in (0 : ℝ)..T,
        ((wpaPsiError b u : ℝ) : ℂ)) :=
    funext fun U => (hcast U).symm
  rw [e]
  exact h2

/-- Substitution `t = e^u` turns the Chebyshev-style integral into `∫ H`. -/
private lemma wpa_integral_psi_sub_div_sq_eq {q : ℕ} (b : ZMod q) (x : ℝ)
    (hx : 1 ≤ x) :
    ∫ t : ℝ in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2
      = ∫ u : ℝ in (0 : ℝ)..Real.log x, wpaPsiError b u := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have himg : Set.Ioc 1 x = Real.exp '' Set.Ioc 0 (Real.log x) := by
    rw [Real.image_exp_Ioc, Real.exp_zero, Real.exp_log hx0]
  have hpt : ∀ u : ℝ, |Real.exp u| • (((q.totient : ℝ) *
      psiResidueClass b (Real.exp u) - Real.exp u) / (Real.exp u) ^ 2)
      = wpaPsiError b u := by
    intro u
    have hne : Real.exp u ≠ 0 := Real.exp_ne_zero u
    have hexp : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [abs_of_pos (Real.exp_pos u), smul_eq_mul]
    unfold wpaPsiError
    field_simp
    linear_combination
      (-((q.totient : ℝ) * psiResidueClass b (Real.exp u))) * hexp
  have hchange : (∫ t : ℝ in Real.exp '' Set.Ioc 0 (Real.log x),
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • (((q.totient : ℝ) * psiResidueClass b (Real.exp u) -
          Real.exp u) / (Real.exp u) ^ 2) :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioc
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      (Real.exp_injective.injOn) _
  have step1 : (∫ t : ℝ in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • (((q.totient : ℝ) * psiResidueClass b (Real.exp u) -
          Real.exp u) / (Real.exp u) ^ 2) := by
    rw [himg]
    exact hchange
  have step2 : (∫ u : ℝ in Set.Ioc 0 (Real.log x),
        |Real.exp u| • (((q.totient : ℝ) * psiResidueClass b (Real.exp u) -
          Real.exp u) / (Real.exp u) ^ 2))
      = ∫ u : ℝ in Set.Ioc 0 (Real.log x), wpaPsiError b u :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u _ => hpt u)
  have step3 : (∫ u : ℝ in Set.Ioc 0 (Real.log x), wpaPsiError b u)
      = ∫ u : ℝ in (0 : ℝ)..Real.log x, wpaPsiError b u :=
    (intervalIntegral.integral_of_le hlog).symm
  exact step1.trans (step2.trans step3)

/-- Convergence of the Chebyshev-style integral. -/
private lemma wpa_tendsto_integral_psi_sub_div_sq {q : ℕ} [NeZero q]
    (b : ZMod q) (hb : IsUnit b) :
    ∃ L : ℝ, Filter.Tendsto
      (fun x => ∫ t : ℝ in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      Filter.atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := wpa_tendsto_integral_psiError b hb
  refine ⟨L, ?_⟩
  have hcomp : Filter.Tendsto
      (fun x : ℝ => ∫ u : ℝ in (0 : ℝ)..Real.log x, wpaPsiError b u)
      Filter.atTop (𝓝 L) :=
    hL.comp Real.tendsto_log_atTop
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x := Filter.eventually_ge_atTop 1
  have hev := h1.mono
    (fun x hx => (wpa_integral_psi_sub_div_sq_eq b x hx).symm)
  exact Filter.Tendsto.congr' hev hcomp

/-- The real-variable prime number theorem in a residue class for `ψ`. -/
lemma tendsto_psiResidueClass_div_self {q : ℕ} [NeZero q]
    (b : ZMod q) (hb : IsUnit b) :
    Filter.Tendsto (fun x : ℝ => psiResidueClass b x / x) Filter.atTop
      (nhds ((q.totient : ℝ)⁻¹)) := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) :=
    Nat.cast_pos.mpr
      (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hphi_ne : (q.totient : ℝ) ≠ 0 := ne_of_gt hphi_pos
  obtain ⟨L, hL⟩ := wpa_tendsto_integral_psi_sub_div_sq b hb
  have hmono : MonotoneOn (fun x : ℝ => (q.totient : ℝ) * psiResidueClass b x)
      (Set.Ici 1) := by
    intro x _ y _ hxy
    exact mul_le_mul_of_nonneg_left
      (wpa_psiResidueClass_mono b hxy) (le_of_lt hphi_pos)
  have hisEq : (fun x : ℝ => (q.totient : ℝ) * psiResidueClass b x)
      ~[Filter.atTop] (fun x : ℝ => x) :=
    Asymptotics.isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq _
      hmono ⟨L, hL⟩
  have hlim1 : Filter.Tendsto
      (fun x : ℝ => ((q.totient : ℝ) * psiResidueClass b x) / x)
      Filter.atTop (nhds 1) := by
    have hz : ∀ᶠ x : ℝ in Filter.atTop, (fun x : ℝ => x) x ≠ 0 := by
      filter_upwards [Filter.eventually_gt_atTop 0] with x hx
      exact ne_of_gt hx
    exact (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hisEq
  have e : (fun x : ℝ => psiResidueClass b x / x)
      = (fun x : ℝ => (q.totient : ℝ)⁻¹ *
        (((q.totient : ℝ) * psiResidueClass b x) / x)) := by
    funext x
    field_simp
  rw [e]
  have hmul := hlim1.const_mul ((q.totient : ℝ)⁻¹)
  simpa using hmul

/-- Mertens' theorem in arithmetic progressions: the reciprocal sum of the
von Mangoldt function over a reduced residue class equals `(log x) / φ(q)` up to
a bounded error. -/
lemma exists_abs_sum_residueClass_div_sub_log_le {q : ℕ} [NeZero q]
    (b : ZMod q) (hb : IsUnit b) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
        Real.log x / (q.totient : ℝ)| ≤ C := by
  have hc0 : ArithmeticFunction.vonMangoldt.residueClass b 0 = 0 :=
    ArithmeticFunction.vonMangoldt.residueClass_apply_zero b
  have hφ : (0 : ℝ) < (q.totient : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hS : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass b k = psiResidueClass b t := by
    intro t
    rw [psiResidueClass, Finset.Icc_eq_cons_Ioc (Nat.zero_le _),
      Finset.sum_cons, hc0, zero_add]
  have hdiff : ∀ x : ℝ, ∀ t ∈ Set.Icc 1 x,
      DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro x t ht
    rw [Set.mem_Icc] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    exact (hasDerivAt_inv ht0).differentiableAt
  have hint : ∀ x : ℝ,
      IntegrableOn (deriv fun t : ℝ => t⁻¹) (Set.Icc 1 x) := by
    intro x
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuous_pow 2).continuousOn
    intro t ht
    rw [Set.mem_Icc] at ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hLHS : ∀ N : ℕ, ∑ k ∈ Finset.Icc 0 N, ((k : ℝ))⁻¹ *
      ArithmeticFunction.vonMangoldt.residueClass b k
      = ∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ) := by
    intro N
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, hc0]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro k _
    exact inv_mul_eq_div _ _
  have hmain : ∀ x : ℝ, x⁻¹ * psiResidueClass b x = psiResidueClass b x / x := by
    intro x
    exact inv_mul_eq_div _ _
  have hint2 : ∀ x : ℝ, (∫ t in Set.Ioc 1 x,
      deriv (fun t : ℝ => t⁻¹) t * psiResidueClass b t)
      = - ∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2 := by
    intro x
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t _
    change deriv (fun t : ℝ => t⁻¹) t * psiResidueClass b t =
      -(psiResidueClass b t / t ^ 2)
    rw [deriv_inv, neg_mul, inv_mul_eq_div]
  have habel : ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))
      = psiResidueClass b x / x
        + ∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2 := by
    intro x hx
    have hA := sum_mul_eq_sub_integral_mul₀ (f := fun t : ℝ => t⁻¹)
      (ArithmeticFunction.vonMangoldt.residueClass b) hc0 x (hdiff x) (hint x)
    simp only [hS] at hA
    rw [hLHS, hmain, hint2, sub_neg_eq_add] at hA
    exact hA
  have he_int : ∀ x : ℝ, IntegrableOn
      (fun t => ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      (Set.Ioc 1 x) volume := by
    intro x
    have hfin : volume (Set.Ioc (1 : ℝ) x) < ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_
      ((q.totient : ℝ) * (Real.log 4 + 4) + 1) ?_
    · have hψ : Measurable (fun t : ℝ => psiResidueClass b t) :=
        (wpa_psiResidueClass_mono b).measurable
      exact (((measurable_const.mul hψ).sub measurable_id).div
        (measurable_id.pow_const 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Set.mem_Ioc] at ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht.1
      have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht1)
      have htnn : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
      have hψnn : 0 ≤ psiResidueClass b t := wpa_psiResidueClass_nonneg b t
      have hψle : psiResidueClass b t ≤ (Real.log 4 + 4) * t :=
        wpa_psiResidueClass_le_mul_self b htnn
      have hKnn : (0 : ℝ) ≤ Real.log 4 + 4 := by
        have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
        linarith
      have hφnn : (0 : ℝ) ≤ (q.totient : ℝ) := le_of_lt hφ
      have hCnn : (0 : ℝ) ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 :=
        add_nonneg (mul_nonneg hφnn hKnn) zero_le_one
      have h2 : ((q.totient : ℝ) * (Real.log 4 + 4)) * t
          ≥ (q.totient : ℝ) * psiResidueClass b t := by
        have h := mul_le_mul_of_nonneg_left hψle hφnn
        rwa [mul_assoc]
      have h3 : (0 : ℝ) ≤ ((q.totient : ℝ) * (Real.log 4 + 4)) * t :=
        mul_nonneg (mul_nonneg hφnn hKnn) htnn
      have hnum : ‖(q.totient : ℝ) * psiResidueClass b t - t‖
          ≤ ((q.totient : ℝ) * (Real.log 4 + 4) + 1) * t := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [h2, h3, mul_nonneg hφnn hψnn, htnn]
      have ht2nn : (0 : ℝ) ≤ t ^ 2 := pow_nonneg htnn 2
      have ht2pos : (0 : ℝ) < t ^ 2 := pow_pos (lt_of_lt_of_le zero_lt_one ht1) 2
      have ht2le : t ≤ t ^ 2 := by
        calc t = t * 1 := (mul_one t).symm
          _ ≤ t * t := mul_le_mul_of_nonneg_left ht1 htnn
          _ = t ^ 2 := (sq t).symm
      calc ‖((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2‖
          = ‖(q.totient : ℝ) * psiResidueClass b t - t‖ / t ^ 2 := by
            simp only [norm_div, Real.norm_eq_abs, abs_of_nonneg ht2nn]
        _ ≤ (((q.totient : ℝ) * (Real.log 4 + 4) + 1) * t) / t ^ 2 :=
            div_le_div_of_nonneg_right hnum ht2nn
        _ ≤ (q.totient : ℝ) * (Real.log 4 + 4) + 1 := by
            rw [div_le_iff₀ ht2pos]
            exact mul_le_mul_of_nonneg_left ht2le hCnn
  have hg_int : ∀ x : ℝ, IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) volume := by
    intro x
    have hIcc : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) volume := by
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.inv₀ continuous_id.continuousOn
      intro t ht
      rw [Set.mem_Icc] at ht
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hlog : ∀ x : ℝ, 1 ≤ x →
      (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ * t⁻¹)
        = ((q.totient : ℝ))⁻¹ * Real.log x := by
    intro x hx
    have hbase : (∫ t in Set.Ioc 1 x, t⁻¹) = Real.log x := by
      rw [(intervalIntegral.integral_of_le hx).symm,
        integral_inv_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hx), div_one]
    calc (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ * t⁻¹)
        = ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x, t⁻¹ := by
          simp only [← smul_eq_mul]
          exact MeasureTheory.integral_const_mul _ _
      _ = ((q.totient : ℝ))⁻¹ * Real.log x := by rw [hbase]
  have hsplit : ∀ x : ℝ, 1 ≤ x →
      (∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2)
      = ((q.totient : ℝ))⁻¹ *
          (∫ t in Set.Ioc 1 x,
            ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
        + ((q.totient : ℝ))⁻¹ * Real.log x := by
    intro x hx
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
    have hpt : ∀ t : ℝ, psiResidueClass b t / t ^ 2
        = ((q.totient : ℝ))⁻¹ *
            (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
          + ((q.totient : ℝ))⁻¹ * t⁻¹ := by
      intro t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp
        ring
    have h1 : IntegrableOn
        (fun t => ((q.totient : ℝ))⁻¹ *
          (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2))
        (Set.Ioc 1 x) volume := (he_int x).const_mul _
    have h2 : IntegrableOn (fun t : ℝ => ((q.totient : ℝ))⁻¹ * t⁻¹)
        (Set.Ioc 1 x) volume := (hg_int x).const_mul _
    have hval : (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ *
          (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2))
        = ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x,
          (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2) := by
      simp only [← smul_eq_mul]
      exact MeasureTheory.integral_const_mul _ _
    calc (∫ t in Set.Ioc 1 x, psiResidueClass b t / t ^ 2)
        = ∫ t in Set.Ioc 1 x, (((q.totient : ℝ))⁻¹ *
            (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
            + ((q.totient : ℝ))⁻¹ * t⁻¹) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpt t)
      _ = (∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ *
            (((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2))
          + ∫ t in Set.Ioc 1 x, ((q.totient : ℝ))⁻¹ * t⁻¹ :=
          MeasureTheory.integral_add h1 h2
      _ = ((q.totient : ℝ))⁻¹ *
            (∫ t in Set.Ioc 1 x,
              ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
          + ((q.totient : ℝ))⁻¹ * Real.log x := by
          rw [hval, hlog x hx]
  obtain ⟨L, hL⟩ := wpa_tendsto_integral_psi_sub_div_sq b hb
  have hPNT := tendsto_psiResidueClass_div_self b hb
  have hI : Filter.Tendsto
      (fun x => ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x,
        ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2)
      Filter.atTop (nhds (((q.totient : ℝ))⁻¹ * L)) :=
    hL.const_mul _
  have hE : Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))
        - Real.log x / (q.totient : ℝ))
      Filter.atTop
      (nhds (((q.totient : ℝ))⁻¹ + ((q.totient : ℝ))⁻¹ * L)) := by
    have hev : (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))
        - Real.log x / (q.totient : ℝ))
        =ᶠ[Filter.atTop] (fun x => psiResidueClass b x / x
          + ((q.totient : ℝ))⁻¹ * ∫ t in Set.Ioc 1 x,
            ((q.totient : ℝ) * psiResidueClass b t - t) / t ^ 2) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      rw [habel x hx, hsplit x hx]
      ring
    exact Filter.Tendsto.congr' hev.symm (hPNT.add hI)
  -- Uniform bound extraction: the error is convergent, hence bounded at infinity;
  -- on the compact head it is a finite sum plus a bounded log term.
  set M : ℝ := ((q.totient : ℝ))⁻¹ + ((q.totient : ℝ))⁻¹ * L with hM
  obtain ⟨X₀, hX₀⟩ := (Metric.tendsto_atTop.mp hE) 1 one_pos
  set X₁ : ℝ := max X₀ 1 with hX₁
  have hX₁ge : 1 ≤ X₁ := le_max_right _ _
  set S : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊X₁⌋₊,
    |ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)| with hS
  have hlogX₁ : 0 ≤ Real.log X₁ := Real.log_nonneg hX₁ge
  refine ⟨max (|M| + 1) (S + Real.log X₁ / (q.totient : ℝ)), fun x hx => ?_⟩
  have hφnn : 0 ≤ (q.totient : ℝ) := le_of_lt hφ
  by_cases hle : x ≤ X₁
  · -- Compact head: the finite sum grows monotonically and log is monotone.
    have hsub : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 ⌊X₁⌋₊ :=
      Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hle)
    have hsum : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))| ≤ S :=
      calc |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))|
          ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            |ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => abs_nonneg _)
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hlog : |Real.log x| ≤ Real.log X₁ := by
      rw [abs_of_nonneg (Real.log_nonneg hx)]
      exact Real.log_le_log hxpos hle
    have hdiv : |Real.log x / (q.totient : ℝ)| ≤ Real.log X₁ / (q.totient : ℝ) := by
      rw [abs_div, abs_of_nonneg hφnn]
      exact div_le_div_of_nonneg_right hlog hφnn
    calc |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
            Real.log x / (q.totient : ℝ)|
        ≤ |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ))| +
          |Real.log x / (q.totient : ℝ)| := abs_sub _ _
      _ ≤ S + Real.log X₁ / (q.totient : ℝ) := add_le_add hsum hdiv
      _ ≤ max (|M| + 1) (S + Real.log X₁ / (q.totient : ℝ)) := le_max_right _ _
  · -- Tail: within distance 1 of the limit.
    have hlt : X₁ < x := lt_of_not_ge hle
    have hx₀ : x ≥ X₀ := le_trans (le_max_left _ _) (le_of_lt hlt)
    have h := hX₀ x hx₀
    rw [Real.dist_eq] at h
    calc |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
            Real.log x / (q.totient : ℝ)|
        ≤ |M| + 1 := by
          have htri : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
              ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
              Real.log x / (q.totient : ℝ)| - |M|
              ≤ |((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
                ArithmeticFunction.vonMangoldt.residueClass b n / (n : ℝ)) -
                Real.log x / (q.totient : ℝ)) - M| :=
            abs_sub_abs_le_abs_sub _ _
          linarith [h]
      _ ≤ max (|M| + 1) (S + Real.log X₁ / (q.totient : ℝ)) := le_max_left _ _

end Chebyshev

section
namespace Chebyshev

/--
For a reduced residue class `a` modulo `q`, the average of the von Mangoldt function over
`n ≡ a (mod q)` tends to `1 / φ(q)`. Source: the proved theorem
`PrimeNumberTheoremAnd.WeakPNT_AP` in
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), revision
`be5e07e04cde20c5ceabf63759bd097a9c88173f`, and its use in
[arXiv:2608.24035](https://arxiv.org/abs/2608.24035). Lean preserves the source's natural
representative and half-open `Finset.range` normalization, while omitting the redundant assumption
`1 ≤ q`, which follows from `a < q`.

Proves `Wanted` entry `weakPNT_arithmeticProgression`.
-/
theorem weakPNT_arithmeticProgression {q a : ℕ}
    (ha : Nat.Coprime a q) (ha_lt : a < q) :
    Filter.Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N,
            if n % q = a then ArithmeticFunction.vonMangoldt n else 0) / (N : ℝ))
      Filter.atTop (nhds (1 / (Nat.totient q : ℝ))) := by
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le a) ha_lt
  have : NeZero q := ⟨by omega⟩
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hqpos)
  have hb : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hpsi_div := tendsto_psiResidueClass_div_self (q := q) (a : ZMod q) hb
  have hseq : Filter.Tendsto
      (fun M : ℕ => psiResidueClass (a : ZMod q) (M : ℝ) / (M : ℝ))
      Filter.atTop (nhds (((Nat.totient q : ℝ))⁻¹)) :=
    hpsi_div.comp tendsto_natCast_atTop_atTop
  have hfrac : Filter.Tendsto (fun M : ℕ => ((M : ℝ) / ((M : ℝ) + 1)))
      Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hmul := hseq.mul hfrac
  have hlim : Filter.Tendsto
      (fun M : ℕ => (psiResidueClass (a : ZMod q) (M : ℝ) / (M : ℝ)) *
        ((M : ℝ) / ((M : ℝ) + 1)))
      Filter.atTop (nhds (1 / (Nat.totient q : ℝ))) := by
    rw [one_div]
    simpa using hmul
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM
  show (psiResidueClass (a : ZMod q) ↑M / ↑M) * (↑M / (↑M + 1))
    = (∑ n ∈ Finset.range (M + 1),
      if n % q = a then ArithmeticFunction.vonMangoldt n else 0) / (↑(M + 1))
  rw [wpa_sum_range_ite_mod_eq ha_lt M]
  have hM0 : ((M : ℝ)) ≠ 0 := by
    exact_mod_cast (by omega : M ≠ 0)
  have hM1 : ((M : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    exact ne_of_gt this
  push_cast
  field_simp

end Chebyshev
end
end

/- TauberianPort.MathlibExt.NumberTheory.PrimeCounting.LandauRamanujan -/
section
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset Nat Chebyshev ArithmeticFunction
open scoped Topology

open scoped Classical

/-- Indicator of positive integers with no prime factor `≡ 3 mod 4`. -/
private noncomputable def lrH (n : ℕ) : ℝ :=
  if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 then 1 else 0

/-- Indicator of positive integers all of whose prime factors are `≡ 3 mod 4`. -/
private noncomputable def lrG (k : ℕ) : ℝ :=
  if k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 then 1 else 0

private lemma lrH_zero : lrH 0 = 0 := by simp [lrH]

private lemma lrG_zero : lrG 0 = 0 := by simp [lrG]

private lemma lrH_one : lrH 1 = 1 := by simp [lrH]

private lemma lrG_one : lrG 1 = 1 := by simp [lrG]

private lemma lrH_nonneg (n : ℕ) : 0 ≤ lrH n := by
  unfold lrH
  split_ifs <;> norm_num

private lemma lrH_le_one (n : ℕ) : lrH n ≤ 1 := by
  unfold lrH
  split_ifs <;> norm_num

private lemma lrG_nonneg (k : ℕ) : 0 ≤ lrG k := by
  unfold lrG
  split_ifs <;> norm_num

private lemma lrG_le_one (k : ℕ) : lrG k ≤ 1 := by
  unfold lrG
  split_ifs <;> norm_num

private lemma lrH_mul (m n : ℕ) : lrH (m * n) = lrH m * lrH n := by
  by_cases hm : m = 0
  · subst hm
    simp [lrH_zero]
  · by_cases hn : n = 0
    · subst hn
      simp [lrH_zero]
    · have hU : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors :=
        Nat.primeFactors_mul hm hn
      have hIff : (m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, p % 4 ≠ 3) ↔
          (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p % 4 ≠ 3) ∧
          (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3) := by
        rw [hU]
        constructor
        · rintro ⟨_, hH⟩
          exact ⟨⟨hm, fun p hp => hH p (Finset.mem_union.mpr (Or.inl hp))⟩,
            ⟨hn, fun p hp => hH p (Finset.mem_union.mpr (Or.inr hp))⟩⟩
        · rintro ⟨⟨hm', hHm⟩, ⟨hn', hHn⟩⟩
          refine ⟨mul_ne_zero hm' hn', fun p hp => ?_⟩
          rcases Finset.mem_union.mp hp with h | h
          · exact hHm p h
          · exact hHn p h
      simp only [lrH, hIff]
      split_ifs with h1 h2 h3 <;> simp_all

private lemma lrH_log_eq {n : ℕ} (hn : 1 ≤ n) :
    lrH n * Real.log n
      = ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d) := by
  have hn0 : n ≠ 0 := by omega
  have hterm : ∀ d ∈ n.divisors,
      ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d)
        = ArithmeticFunction.vonMangoldt d * lrH n := by
    intro d hd
    have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
    have hmul : lrH d * lrH (n / d) = lrH n := by
      rw [← lrH_mul, hdeq]
    calc ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d)
        = ArithmeticFunction.vonMangoldt d * (lrH d * lrH (n / d)) := by ring
      _ = ArithmeticFunction.vonMangoldt d * lrH n := by rw [hmul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    ArithmeticFunction.vonMangoldt_sum, mul_comm]

private lemma lrH_log_div_eq {n : ℕ} (hn : 1 ≤ n) :
    lrH n * Real.log n / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
        (lrH (n / d) / ((n / d : ℕ) : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  rw [lrH_log_eq hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
  have hcast : (d : ℝ) * (((n / d : ℕ)) : ℝ) = (n : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdeq
    rwa [Nat.cast_mul] at h
  have e : (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
      (lrH (n / d) / (((n / d : ℕ)) : ℝ))
      = (ArithmeticFunction.vonMangoldt d * lrH d * lrH (n / d)) /
        ((d : ℝ) * (((n / d : ℕ)) : ℝ)) := by
    ring
  rw [e, hcast]

private lemma lr_sum_swap (F G : ℕ → ℝ) (hF : F 0 = 0) (hG : G 0 = 0)
    (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, F d * G (n / d)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, G m * ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, F d := by
  classical
  let F' : ArithmeticFunction ℝ := ⟨F, hF⟩
  let G' : ArithmeticFunction ℝ := ⟨G, hG⟩
  have hFG : ∀ n : ℕ, (F' * G') n = ∑ d ∈ n.divisors, F d * G (n / d) := by
    intro n
    calc (F' * G') n = ∑ x ∈ n.divisorsAntidiagonal, F x.1 * G x.2 := by
          rw [ArithmeticFunction.mul_apply]
          apply Finset.sum_congr rfl
          intro x _
          rfl
      _ = ∑ d ∈ n.divisors, F d * G (n / d) :=
          Nat.sum_divisorsAntidiagonal (fun a b => F a * G b)
  have hGF : ∀ n : ℕ, (G' * F') n = ∑ d ∈ n.divisors, F d * G (n / d) := by
    intro n
    have hcomm : G' * F' = F' * G' := mul_comm _ _
    rw [hcomm]
    exact hFG n
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, F d * G (n / d)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (G' * F') n := by
        apply Finset.sum_congr rfl
        intro n _
        exact (hGF n).symm
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, G' n * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / n), F' m :=
        ArithmeticFunction.sum_Ioc_mul_eq_sum_sum G' F' ⌊x⌋₊
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, G m * ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, F d := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← Nat.floor_div_natCast]
        rfl

/-- `H(x)`: count of `n ≤ x` with `lrH n = 1`. -/
private noncomputable def lrCount (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n

/-- `A(x)`: reciprocal sum of `lrH` over `n ≤ x`. -/
private noncomputable def lrA (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ)

/-- `ψ_h(y)`: von Mangoldt sum restricted by `lrH`. -/
private noncomputable def lrPsi (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * lrH d

/-- `M(y)`: reciprocal Mertens sum restricted by `lrH`. -/
private noncomputable def lrMert (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)

/-- `J(x)`: log-weighted reciprocal sum. -/
private noncomputable def lrJ (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ))

private lemma lr_L_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * lrPsi (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * lrH d) 0 = 0 := by
    simp [lrH_zero]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d) * lrH (n / d) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [lrH_zero]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact lrH_log_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d) * lrH (n / d) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, ArithmeticFunction.vonMangoldt d * lrH d :=
        lr_sum_swap _ _ hF lrH_zero x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * lrPsi (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [lrPsi]

private lemma lr_logA_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) 0 = 0 := by
    simp [lrH_zero]
  have hG : (fun m : ℕ => lrH m / (m : ℝ)) 0 = 0 := by
    simp [lrH_zero]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
        (lrH (n / d) / (((n / d : ℕ)) : ℝ)) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [lrH_zero]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact lrH_log_div_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) *
        (lrH (n / d) / (((n / d : ℕ)) : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊,
          ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ) :=
        lr_sum_swap (fun d : ℕ => ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ))
          (fun m : ℕ => lrH m / (m : ℝ)) hF hG x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [lrMert]

private lemma lrCount_nonneg (x : ℝ) : 0 ≤ lrCount x :=
  Finset.sum_nonneg fun n _ => lrH_nonneg n

private lemma lrA_nonneg (x : ℝ) : 0 ≤ lrA x := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)

private lemma lrPsi_nonneg (y : ℝ) : 0 ≤ lrPsi y := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (lrH_nonneg d)

private lemma lrA_mono : Monotone lrA := by
  intro x y hxy
  simp only [lrA]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
  · intro n _ _
    exact div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)

private lemma lrA_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ lrA x := by
  have h1 : 1 ∈ Finset.Ioc 0 ⌊x⌋₊ := by
    rw [Finset.mem_Ioc]
    exact ⟨by omega, (Nat.one_le_floor_iff x).mpr hx⟩
  have h := Finset.single_le_sum
    (fun n _ => div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)) h1
  simpa [lrH_one, lrA] using h

private lemma lrCount_le {y : ℝ} (hy : 0 ≤ y) : lrCount y ≤ y := by
  calc lrCount y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, lrH n := rfl
    _ ≤ ∑ _n ∈ Finset.Ioc 0 ⌊y⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => lrH_le_one n
    _ = (⌊y⌋₊ : ℝ) := by simp [Finset.sum_const, Nat.card_Ioc]
    _ ≤ y := Nat.floor_le hy

private lemma lrPsi_le_psi (y : ℝ) : lrPsi y ≤ Chebyshev.psi y := by
  simp only [lrPsi, Chebyshev.psi]
  apply Finset.sum_le_sum
  intro d _
  calc ArithmeticFunction.vonMangoldt d * lrH d
      ≤ ArithmeticFunction.vonMangoldt d * 1 :=
        mul_le_mul_of_nonneg_left (lrH_le_one d)
          ArithmeticFunction.vonMangoldt_nonneg
    _ = ArithmeticFunction.vonMangoldt d := mul_one _

private lemma lrPsi_le_mul_self {y : ℝ} (hy : 0 ≤ y) :
    lrPsi y ≤ (Real.log 4 + 4) * y :=
  le_trans (lrPsi_le_psi y) (Chebyshev.psi_le_const_mul_self hy)

/-- `lrH` on a prime is determined by the residue of the prime mod 4. -/
private lemma lrH_prime_eq {p : ℕ} (hp : p.Prime) :
    lrH p = if p % 4 = 3 then 0 else 1 := by
  have hmem : ∀ q : ℕ, q ∈ p.primeFactors ↔ q = p := by
    intro q
    constructor
    · intro hq
      have hqP := Nat.prime_of_mem_primeFactors hq
      have hqdvd := Nat.dvd_of_mem_primeFactors hq
      exact (Nat.prime_dvd_prime_iff_eq hqP hp).mp hqdvd
    · intro hq
      rw [hq]
      exact hp.mem_primeFactors_self
  unfold lrH
  by_cases h : p % 4 = 3
  · rw [if_pos h, if_neg]
    intro hc
    exact hc.2 p ((hmem p).mpr rfl) h
  · rw [if_neg h, if_pos]
    exact ⟨hp.ne_zero, fun q hq => by rw [(hmem q).mp hq]; exact h⟩

/-- The residue-class von Mangoldt function as an `if`. -/
private lemma lr_residueClass_eq (d : ℕ) :
    ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d
      = if (d : ZMod 4) = 1 then ArithmeticFunction.vonMangoldt d else 0 := by
  change Set.indicator {n : ℕ | (n : ZMod 4) = (1 : ZMod 4)} _ _ = _
  split_ifs with h
  · have hm : d ∈ {n : ℕ | (n : ZMod 4) = (1 : ZMod 4)} := h
    exact Set.indicator_of_mem hm _
  · have hm : d ∉ {n : ℕ | (n : ZMod 4) = (1 : ZMod 4)} := h
    exact Set.indicator_of_notMem hm _

/-- Pointwise comparison of `Λ · lrH ·` with the residue class of `1 mod 4`. -/
private lemma lr_resid_diff_le (d : ℕ) :
    |ArithmeticFunction.vonMangoldt d * lrH d -
      ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d|
      ≤ (if d = 2 then Real.log 2 else 0) +
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d) := by
  by_cases h2 : d = 2
  · subst h2
    have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hH : lrH 2 = 1 := by
      rw [lrH_prime_eq Nat.prime_two, if_neg (by decide)]
    have hr : ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) 2 = 0 := by
      rw [lr_residueClass_eq, if_neg (by decide)]
    rw [hΛ, hH, hr, if_pos rfl, if_pos Nat.prime_two, mul_one, sub_zero,
      abs_of_nonneg (Real.log_nonneg (by norm_num))]
    exact le_add_of_nonneg_right le_rfl
  · by_cases hp : d.Prime
    · -- `d` is an odd prime: both sides agree.
      obtain rfl | hodd := hp.eq_two_or_odd'
      · exact absurd rfl h2
      · have hmod : d % 4 = 1 ∨ d % 4 = 3 := by
          have hlt : d % 4 < 4 := Nat.mod_lt d (by norm_num)
          have h2mod : d % 2 = 1 := Nat.odd_iff.mp hodd
          omega
        have hcast : (d : ZMod 4) = ((d % 4 : ℕ) : ZMod 4) :=
          (ZMod.natCast_mod d 4).symm
        have hΛr : ArithmeticFunction.vonMangoldt d * lrH d
            = ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d := by
          rw [lr_residueClass_eq, lrH_prime_eq hp]
          rcases hmod with h1 | h3
          · have hc : (d : ZMod 4) = 1 := by
              rw [hcast, h1]
              simp
            rw [if_neg (by omega : d % 4 ≠ 3), if_pos hc, mul_one]
          · have hc : (d : ZMod 4) ≠ 1 := by
              rw [hcast, h3]
              decide
            rw [if_pos h3, if_neg hc, mul_zero]
        rw [hΛr, sub_self, abs_zero, if_neg h2, if_pos hp]
        norm_num
    · -- `d` is not prime: both terms lie in `[0, Λ d]`.
      rw [if_neg h2, if_neg hp]
      have ha0 : 0 ≤ ArithmeticFunction.vonMangoldt d * lrH d :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (lrH_nonneg d)
      have ha1 : ArithmeticFunction.vonMangoldt d * lrH d
          ≤ ArithmeticFunction.vonMangoldt d := by
        calc ArithmeticFunction.vonMangoldt d * lrH d
            ≤ ArithmeticFunction.vonMangoldt d * 1 :=
              mul_le_mul_of_nonneg_left (lrH_le_one d)
                ArithmeticFunction.vonMangoldt_nonneg
          _ = ArithmeticFunction.vonMangoldt d := mul_one _
      have hb0 : 0 ≤ ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d :=
        ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _
      have hb1 : ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d
          ≤ ArithmeticFunction.vonMangoldt d :=
        ArithmeticFunction.vonMangoldt.residueClass_le _ _
      rw [abs_le]
      constructor <;> linarith

/-- For `t ≥ 1`, `log t` is at most four times `t ^ (1/4 : ℝ)`. -/
private lemma lr_log_le_four_rpow (t : ℝ) (ht : 1 ≤ t) :
    Real.log t ≤ 4 * t ^ (1/4 : ℝ) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : Real.log (t ^ (1/4 : ℝ)) ≤ t ^ (1/4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htpos (1/4 : ℝ))
    linarith
  have h2 : Real.log t = 4 * Real.log (t ^ (1/4 : ℝ)) := by
    have hlog := Real.log_rpow htpos (1/4 : ℝ)
    linarith
  linarith

/-- For `t ≥ 1`, `2 * √t * log t` is at most `8 * t ^ (3/4 : ℝ)`. -/
private lemma lr_two_sqrt_mul_log_le (t : ℝ) (ht : 1 ≤ t) :
    2 * Real.sqrt t * Real.log t ≤ 8 * t ^ (3/4 : ℝ) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog := lr_log_le_four_rpow t ht
  have h2nn : (0 : ℝ) ≤ 2 * t ^ (1/2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg htpos.le _)
  have hmul := mul_le_mul_of_nonneg_left hlog h2nn
  have e_add : t ^ (1/2 : ℝ) * t ^ (1/4 : ℝ) = t ^ (3/4 : ℝ) := by
    rw [← Real.rpow_add htpos]
    congr 1
    norm_num
  rw [Real.sqrt_eq_rpow]
  calc 2 * t ^ (1/2 : ℝ) * Real.log t
      ≤ 2 * t ^ (1/2 : ℝ) * (4 * t ^ (1/4 : ℝ)) := hmul
    _ = 8 * t ^ (3/4 : ℝ) := by rw [← e_add]; ring

/-- Pointwise bound for the non-prime Abel integrand. -/
private lemma lr_psi_sub_theta_div_le (t : ℝ) (ht : 1 ≤ t) :
    (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 ≤ 8 * t ^ (-5/4 : ℝ) := by
  have hnn : 0 ≤ Chebyshev.psi t - Chebyshev.theta t := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  have hle := Chebyshev.psi_sub_theta_le ht
  have hnum := lr_two_sqrt_mul_log_le t ht
  calc (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2
      ≤ (8 * t ^ (3/4 : ℝ)) / t ^ 2 :=
        div_le_div_of_nonneg_right (le_trans hle hnum) (sq_nonneg t)
    _ = 8 * t ^ (-5/4 : ℝ) := by
      rw [← Real.rpow_natCast t 2, mul_div_assoc,
        ← Real.rpow_sub (lt_of_lt_of_le zero_lt_one ht)]
      congr 1
      norm_num

/-- Monotonicity of `ψ - θ` (a sum of nonnegative terms over a growing set). -/
private lemma lr_psi_sub_theta_mono :
    Monotone (fun t => Chebyshev.psi t - Chebyshev.theta t) := by
  intro a b hab
  dsimp only
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hab) hn.1, hn.2⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The reciprocal sum of `Λ` over non-primes is uniformly bounded. -/
private lemma lr_sum_not_prime_le :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n / (n : ℝ))
        ≤ C := by
  refine ⟨40, fun y hy => ?_⟩
  set c : ℕ → ℝ := fun n =>
    if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n with hc
  have hcn : ∀ n : ℕ, c n =
      (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n) :=
    fun n => rfl
  have hc0 : c 0 = 0 := by
    rw [hcn, if_neg Nat.not_prime_zero,
      ArithmeticFunction.vonMangoldt_apply, if_neg not_isPrimePow_zero]
  have hpart : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
      = Chebyshev.psi t - Chebyshev.theta t := by
    intro t
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hc0, zero_add,
      Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcn]
    by_cases h : n.Prime
    · rw [if_pos h, if_neg (show ¬¬n.Prime from fun hn => hn h)]
    · rw [if_neg h, if_pos h]
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) y,
      DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    exact (hasDerivAt_inv
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).differentiableAt
  have hint : MeasureTheory.IntegrableOn (deriv fun t : ℝ => t⁻¹)
      (Set.Icc 1 y) MeasureTheory.volume := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuous_pow 2).continuousOn
    intro t ht
    rw [Set.mem_Icc] at ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hA := sum_mul_eq_sub_integral_mul₀ (f := fun t : ℝ => t⁻¹) c hc0 y hdiff hint
  beta_reduce at hA
  simp only [hpart] at hA
  have hLHS : (∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (k : ℝ)⁻¹ * c k)
      = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcn, div_eq_mul_inv]
    by_cases h : n.Prime
    · rw [if_pos h, if_pos h, mul_zero]
    · rw [if_neg h, if_neg h, mul_comm]
  have hderiv : ∀ t ∈ Set.Ioc (1 : ℝ) y,
      deriv (fun t : ℝ => t⁻¹) t * (Chebyshev.psi t - Chebyshev.theta t)
      = -((Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) := by
    intro t _
    rw [deriv_inv, neg_mul, inv_mul_eq_div]
  have hint2 : (∫ t in Set.Ioc (1 : ℝ) y,
      deriv (fun t : ℝ => t⁻¹) t * (Chebyshev.psi t - Chebyshev.theta t))
      = - ∫ t in Set.Ioc (1 : ℝ) y,
        (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    rw [Set.mem_Ioc] at ht
    exact hderiv t ht
  rw [hLHS, hint2, sub_neg_eq_add] at hA
  have hB : y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y) ≤ 8 := by
    have hle := Chebyshev.psi_sub_theta_le hy
    have hnum := lr_two_sqrt_mul_log_le y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
    have hle1 : y ^ (3/4 : ℝ) ≤ y := by
      calc y ^ (3/4 : ℝ) ≤ y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
        _ = y := Real.rpow_one y
    have hle2 : y ^ (3/4 : ℝ) / y ≤ 1 := (div_le_one hypos).mpr hle1
    calc y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y)
        ≤ y⁻¹ * (8 * y ^ (3/4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans hle hnum) (inv_nonneg.mpr hypos.le)
      _ = 8 * (y ^ (3/4 : ℝ) / y) := by ring
      _ ≤ 8 * 1 :=
          mul_le_mul_of_nonneg_left hle2 (by norm_num)
      _ = 8 := mul_one 8
  have h_int : MeasureTheory.IntegrableOn
      (fun t => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      (Set.Ioc 1 y) MeasureTheory.volume := by
    have hfin : MeasureTheory.volume (Set.Ioc (1 : ℝ) y) < ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ 8 ?_
    · exact ((lr_psi_sub_theta_mono.measurable.div
        (measurable_id.pow_const 2)).aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Set.mem_Ioc] at ht
      have ht1 : 1 ≤ t := le_of_lt ht.1
      have hnn : 0 ≤ (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
        apply div_nonneg _ (sq_nonneg t)
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
        exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
      have hle := lr_psi_sub_theta_div_le t ht1
      have h54 : t ^ (-5/4 : ℝ) ≤ 1 := by
        calc t ^ (-5/4 : ℝ) ≤ t ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
          _ = 1 := Real.rpow_zero t
      calc ‖(Chebyshev.psi t - Chebyshev.theta t) / t ^ 2‖
          = (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ 8 * t ^ (-5/4 : ℝ) := hle
        _ ≤ 8 := by
            calc 8 * t ^ (-5/4 : ℝ) ≤ 8 * 1 :=
                  mul_le_mul_of_nonneg_left h54 (by norm_num)
              _ = 8 := mul_one 8
  have h_major : MeasureTheory.IntegrableOn (fun t => 8 * t ^ (-5/4 : ℝ))
      (Set.Ioc 1 y) MeasureTheory.volume :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).mono_set
      Set.Ioc_subset_Ioi_self).const_mul 8
  have hIval : (∫ t in Set.Ioc (1 : ℝ) y,
      (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      ≤ ∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ) :=
    MeasureTheory.setIntegral_mono_on h_int h_major measurableSet_Ioc
      (fun t ht => lr_psi_sub_theta_div_le t (le_of_lt (Set.mem_Ioc.mp ht).1))
  have hIoi_val : (∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ)) = 32 := by
    have e : (-5/4 : ℝ) + 1 = -1/4 := by norm_num
    have hval : (∫ t in Set.Ioi (1 : ℝ), t ^ (-5/4 : ℝ)) = 4 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one, e]
      simp only [Real.one_rpow]
      norm_num
    calc (∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ))
        = 8 * ∫ t in Set.Ioi (1 : ℝ), t ^ (-5/4 : ℝ) := by
          simp only [← smul_eq_mul]
          exact MeasureTheory.integral_const_mul _ _
      _ = 32 := by rw [hval]; norm_num
  have hImono : (∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ)) ≤ 32 := by
    calc (∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ))
        ≤ ∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ) := by
          have hIoi_int : MeasureTheory.IntegrableOn
              (fun t : ℝ => 8 * t ^ (-5/4 : ℝ))
              (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
            (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 8
          apply MeasureTheory.setIntegral_mono_set hIoi_int _ _
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
              with t ht
            exact mul_nonneg (by norm_num)
              (Real.rpow_nonneg
                (le_trans zero_le_one (le_of_lt (Set.mem_Ioi.mp ht))) _)
          · exact MeasureTheory.ae_of_all _ fun t ht =>
              Set.Ioc_subset_Ioi_self ht
      _ = 32 := hIoi_val
  have hfinal : y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y) +
      (∫ t in Set.Ioc (1 : ℝ) y, (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      ≤ 40 := by
    calc _ ≤ 8 + ∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ) :=
          add_le_add hB hIval
      _ ≤ 8 + 32 := add_le_add (le_refl 8) hImono
      _ = 40 := by norm_num
  rw [hA]
  exact hfinal

/-- Mertens bound for the `lrH`-restricted reciprocal sum. -/
private lemma lr_mertens :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → |lrMert y - 1 / 2 * Real.log y| ≤ C := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  obtain ⟨C₁, hC₁⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le
    (q := 4) (1 : ZMod 4) isUnit_one
  obtain ⟨C₂, hC₂⟩ := lr_sum_not_prime_le
  have hφ : Nat.totient 4 = 2 := by decide
  refine ⟨C₁ + (Real.log 2 / 2 + C₂), fun y hy => ?_⟩
  have hmain : ∀ d ∈ Finset.Ioc 0 ⌊y⌋₊,
      |(ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ)|
      ≤ (if d = 2 then Real.log 2 / 2 else 0) +
        (if d.Prime then (0 : ℝ)
          else ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Ioc.mp hd).1
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have h := lr_resid_diff_le d
    have hdiv : |(ArithmeticFunction.vonMangoldt d * lrH d -
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ)|
        = |ArithmeticFunction.vonMangoldt d * lrH d -
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d| / (d : ℝ) := by
      rw [abs_div, abs_of_nonneg hdpos.le]
    have e : ((if d = 2 then Real.log 2 else 0) +
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) / (d : ℝ)
        = (if d = 2 then Real.log 2 / 2 else 0) +
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
      by_cases h : d.Prime
      · rw [if_pos h, if_pos h]
        by_cases h2 : d = 2
        · subst h2
          rw [if_pos rfl, if_pos rfl]
          ring
        · rw [if_neg h2, if_neg h2, zero_add, zero_div]
      · rw [if_neg h, if_neg h]
        by_cases h2 : d = 2
        · subst h2
          rw [if_pos rfl, if_pos rfl]
          ring
        · rw [if_neg h2, if_neg h2, zero_add, zero_add]
    rw [hdiv]
    exact le_trans (div_le_div_of_nonneg_right h hdpos.le) (le_of_eq e)
  have hsum : ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
      |(ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ)|
      ≤ Real.log 2 / 2 + C₂ := by
    calc _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
          ((if d = 2 then Real.log 2 / 2 else 0) +
           (if d.Prime then (0 : ℝ)
             else ArithmeticFunction.vonMangoldt d / (d : ℝ))) :=
          Finset.sum_le_sum fun d hd => hmain d hd
      _ = (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 / 2 else 0)) +
          (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
            (if d.Prime then (0 : ℝ)
              else ArithmeticFunction.vonMangoldt d / (d : ℝ))) :=
          Finset.sum_add_distrib
      _ ≤ Real.log 2 / 2 + C₂ := by
          apply add_le_add _ (hC₂ y hy)
          simp only [Finset.sum_ite_eq']
          split_ifs with hmem
          · exact le_refl _
          · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hrfl : lrMert y =
      ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ) := rfl
  have hdiff_sum : (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * lrH d / (d : ℝ)) -
      (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        (ArithmeticFunction.vonMangoldt d * lrH d -
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) / (d : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [sub_div]
  have hM : |lrMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))|
      ≤ Real.log 2 / 2 + C₂ := by
    rw [hrfl, hdiff_sum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) hsum
  have hN5a : |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ)) -
      1 / 2 * Real.log y| ≤ C₁ := by
    have h := hC₁ y hy
    rw [hφ, Nat.cast_two] at h
    rwa [show Real.log y / 2 = 1 / 2 * Real.log y from by ring] at h
  calc |lrMert y - 1 / 2 * Real.log y|
      = |(lrMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))) +
        ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ)) -
          1 / 2 * Real.log y)| := by
        congr 1
        ring
    _ ≤ |lrMert y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ))| +
        |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) n / (n : ℝ)) -
          1 / 2 * Real.log y| := abs_add_le _ _
    _ ≤ (Real.log 2 / 2 + C₂) + C₁ := add_le_add hM hN5a
    _ = C₁ + (Real.log 2 / 2 + C₂) := by ring

/-- The difference between `lrPsi` and the residue-class psi is at most
`log 2 + (ψ - θ)`. -/
private lemma lr_psi_diff_le (y : ℝ) :
    |lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y|
      ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) := by
  have e : lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d) := by
    unfold lrPsi Chebyshev.psiResidueClass
    rw [← Finset.sum_sub_distrib]
  have hnp : ∀ z : ℝ, ∑ d ∈ Finset.Ioc 0 ⌊z⌋₊,
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)
      = Chebyshev.psi z - Chebyshev.theta z := by
    intro z
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d.Prime
    · rw [if_pos h, if_neg (show ¬¬d.Prime from fun hn => hn h)]
    · rw [if_neg h, if_pos h]
  have h2part : ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 else 0)
      ≤ Real.log 2 := by
    simp only [Finset.sum_ite_eq']
    split_ifs with hmem
    · exact le_refl _
    · exact Real.log_nonneg (by norm_num)
  rw [e]
  calc |∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d)|
      ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, |ArithmeticFunction.vonMangoldt d * lrH d -
        ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ((if d = 2 then Real.log 2 else 0) +
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_le_sum fun d _ => lr_resid_diff_le d
    _ = (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 else 0)) +
        (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_add_distrib
    _ ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) :=
        add_le_add h2part (le_of_eq (hnp y))

/-- The normalized error between `lrPsi` and the residue-class psi tends to zero. -/
private lemma lr_psi_err_tendsto :
    Filter.Tendsto (fun y => (lrPsi y -
      Chebyshev.psiResidueClass (1 : ZMod 4) y) / y)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ y in Filter.atTop,
      ‖(lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y) / y‖
        ≤ Real.log 2 / y + 8 * y ^ (-1/4 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
    have h1 := lr_psi_diff_le y
    have h2 := Chebyshev.psi_sub_theta_le hy
    have h3 := lr_two_sqrt_mul_log_le y hy
    have e1 : y ^ (3/4 : ℝ) / y = y ^ (-1/4 : ℝ) := by
      have h3 : (3/4 : ℝ) - 1 = -1/4 := by norm_num
      rw [← h3, Real.rpow_sub hypos, Real.rpow_one]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hypos.le]
    calc |lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y| / y
        ≤ (Real.log 2 + 8 * y ^ (3/4 : ℝ)) / y := by
          apply div_le_div_of_nonneg_right _ hypos.le
          linarith [h1, h2, h3]
      _ = Real.log 2 / y + 8 * y ^ (-1/4 : ℝ) := by
          rw [add_div, mul_div_assoc, e1]
  have hg : Filter.Tendsto (fun y : ℝ => Real.log 2 / y + 8 * y ^ (-1/4 : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => Real.log 2 / y) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero.const_mul (Real.log 2))
    have h2 : Filter.Tendsto (fun y : ℝ => 8 * y ^ (-1/4 : ℝ))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_rpow_neg_atTop
        (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul 8
      have e : ((-1/4 : ℝ)) = -((1/4 : ℝ)) := by norm_num
      rw [e]
      simpa using h
    simpa using h1.add h2
  exact squeeze_zero_norm' hbound hg

/-- `lrPsi y / y` tends to `1 / 2`. -/
private lemma lr_psi_tendsto :
    Filter.Tendsto (fun y => lrPsi y / y) Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  have hPNT := Chebyshev.tendsto_psiResidueClass_div_self (1 : ZMod 4) isUnit_one
  have hφ : Nat.totient 4 = 2 := by decide
  have eφ : ((Nat.totient 4 : ℝ))⁻¹ = 1 / 2 := by
    rw [hφ]
    norm_num
  rw [eφ] at hPNT
  have heq : (fun y => lrPsi y / y) =ᶠ[Filter.atTop]
      (fun y => (lrPsi y - Chebyshev.psiResidueClass (1 : ZMod 4) y) / y +
        Chebyshev.psiResidueClass (1 : ZMod 4) y / y) := by
    filter_upwards with y
    rw [sub_div]
    ring
  have hlim := lr_psi_err_tendsto.add hPNT
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 from by ring] at hlim
  exact Filter.Tendsto.congr' heq.symm hlim

/-- `J` is close to `(2/3) A log`: the Mertens error propagates. -/
private lemma lr_J_near :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |lrJ x - 2 / 3 * lrA x * Real.log x| ≤ 2 / 3 * C * lrA x := by
  obtain ⟨C, hC⟩ := lr_mertens
  refine ⟨C, fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hm : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      |lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| ≤ C := by
    intro m hmem
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmem).1
    have hmx : (m : ℝ) ≤ x := by
      have h1 : m ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ x))
    have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hge : 1 ≤ x / (m : ℝ) := by
      rw [le_div_iff₀ hpos]
      simpa using hmx
    exact hC _ hge
  have hR : |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
      (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| ≤ C * lrA x := by
    calc _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          |(lrH m / (m : ℝ)) *
            (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          (lrH m / (m : ℝ)) * C := by
          apply Finset.sum_le_sum
          intro m hmem
          calc |(lrH m / (m : ℝ)) *
              (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))|
              = (lrH m / (m : ℝ)) *
                |lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| := by
                rw [abs_mul, abs_of_nonneg
                  (div_nonneg (lrH_nonneg m) (Nat.cast_nonneg m))]
            _ ≤ (lrH m / (m : ℝ)) * C :=
                mul_le_mul_of_nonneg_left (hm m hmem)
                  (div_nonneg (lrH_nonneg m) (Nat.cast_nonneg m))
      _ = C * lrA x := by
          have hrfl : lrA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m / (m : ℝ) := rfl
          rw [← Finset.sum_mul, ← hrfl]
          ring
  have hsplit : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)))
      = 1 / 2 * lrJ x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
        (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have hJ2 : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
        (lrH m / (m : ℝ)) * (1 / 2 * Real.log (x / (m : ℝ)))) = 1 / 2 * lrJ x := by
      have hJ : lrJ x =
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * Real.log (x / (m : ℝ)) := rfl
      rw [hJ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    calc (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) * lrMert (x / (m : ℝ)))
        = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ((lrH m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ))) + (lrH m / (m : ℝ)) *
          (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))) :=
          Finset.sum_congr rfl fun m _ => by ring
      _ = (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ)))) +
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
          (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) :=
          Finset.sum_add_distrib
      _ = 1 / 2 * lrJ x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
          (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
          rw [hJ2]
  have hAJ : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ) / (n : ℝ))
      = lrA x * Real.log x - lrJ x := by
    have hJ : lrJ x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
    have hA : lrA x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ) := rfl
    rw [hJ, hA, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hmem
    by_cases hn : n = 0
    · subst hn
      simp [lrH_zero]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
      ring
  have hRe : (lrA x * Real.log x - lrJ x) - 1 / 2 * lrJ x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m / (m : ℝ)) *
        (lrMert (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have h1 := lr_logA_eq x
    rw [hAJ] at h1
    rw [h1, hsplit]
    ring
  rw [← hRe] at hR
  have hRw : lrJ x - 2 / 3 * lrA x * Real.log x
      = -((2 / 3) * ((lrA x * Real.log x - lrJ x) - 1 / 2 * lrJ x)) := by
    ring
  rw [hRw, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  calc 2 / 3 * |(lrA x * Real.log x - lrJ x) - 1 / 2 * lrJ x|
      ≤ 2 / 3 * (C * lrA x) :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
    _ = 2 / 3 * C * lrA x := by ring

/-- Increment bounds for `J`: splitting the sum at `⌊x⌋₊`. -/
private lemma lr_J_increment {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    lrA x * Real.log (y / x) ≤ lrJ y - lrJ x ∧
      lrJ y - lrJ x ≤ lrA y * Real.log (y / x) := by
  have hy : 1 ≤ y := le_trans hx hxy
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have hle : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hJx : lrJ x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
  have hJy : lrJ y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) := rfl
  have hAx : lrA x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ) := rfl
  have hAy : lrA y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, lrH n / (n : ℝ) := rfl
  have hsplitJ : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ))) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hsplitA : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, lrH n / (n : ℝ))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n / (n : ℝ)) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hlogyx : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hypos) (ne_of_gt hxpos)
  have hmain : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
        (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ))
      = (lrH n / (n : ℝ)) * Real.log (y / x) := by
    intro n hmem
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hmem).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [Real.log_div (ne_of_gt hypos) (ne_of_gt hnpos),
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos), hlogyx]
    ring
  have hRnn : 0 ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
    apply Finset.sum_nonneg
    intro n hmem
    have hn1 : 1 ≤ n := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have h2 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
      omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hny : (n : ℝ) ≤ y := by
      have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
    have hlog : 0 ≤ Real.log (y / (n : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hnpos]
      simpa using hny
    exact mul_nonneg (div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n)) hlog
  have hRle : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ)) * Real.log (y / x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hmem
    have hn1 : 1 ≤ n := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have h2 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
      omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnx : x < (n : ℝ) := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have hN : ⌊x⌋₊ + 1 ≤ n := h1
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hN
      have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    have hny : (n : ℝ) ≤ y := by
      have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
    have hfrac : y / (n : ℝ) ≤ y / x :=
      (div_le_div_iff_of_pos_left hypos hnpos hxpos).mpr hnx.le
    have hlog : Real.log (y / (n : ℝ)) ≤ Real.log (y / x) :=
      Real.log_le_log (div_pos hypos hnpos) hfrac
    exact mul_le_mul_of_nonneg_left hlog
      (div_nonneg (lrH_nonneg n) (Nat.cast_nonneg n))
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ))) -
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ)))
      = lrA x * Real.log (y / x) := by
    rw [← Finset.sum_sub_distrib]
    have hcongr : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
          (lrH n / (n : ℝ)) * Real.log (x / (n : ℝ))))
        = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH n / (n : ℝ)) * Real.log (y / x) :=
      Finset.sum_congr rfl fun n hmem => hmain n hmem
    rw [hcongr, ← Finset.sum_mul, hAx]
  have hR_eq : lrA y - lrA x
      = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ) := by
    rw [hAy, hAx, hsplitA, add_sub_cancel_left]
  have hJyJx : lrJ y - lrJ x = lrA x * Real.log (y / x) +
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
    rw [hJy, hJx, hsplitJ]
    linear_combination hdiff
  rw [hJyJx]
  constructor
  · exact le_add_of_nonneg_right hRnn
  · have hRR : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ (lrA y - lrA x) * Real.log (y / x) := by
      rw [hR_eq]
      calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
          ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ)) * Real.log (y / x) :=
            hRle
        _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, lrH n / (n : ℝ)) * Real.log (y / x) :=
            rfl
    calc lrA x * Real.log (y / x) +
        (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (lrH n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ lrA x * Real.log (y / x) + (lrA y - lrA x) * Real.log (y / x) :=
          add_le_add (le_refl _) hRR
      _ = lrA y * Real.log (y / x) := by ring

/-- For `|t| ≤ 1/2`, `|log (1 + t) - t| ≤ 2 t²`. -/
private lemma lr_log_one_add_le (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |(-t)| < 1 := by
    rw [abs_neg]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one,
    sub_neg_eq_add] at h
  have h2 : |-t + Real.log (1 + t)| = |Real.log (1 + t) - t| := by
    congr 1
    ring
  rw [h2] at h
  have ht2 : |-t| ^ 2 = t ^ 2 := by rw [abs_neg, sq_abs]
  have hden : (1 : ℝ) / 2 ≤ 1 - |-t| := by
    rw [abs_neg]
    have := abs_nonneg t
    linarith
  have hpos : (0 : ℝ) < 1 - |-t| := by linarith
  have hle : t ^ 2 / (1 - |-t|) ≤ t ^ 2 / (1 / 2) := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)
    simpa using one_div_le_one_div_of_le (by norm_num) hden
  have hexp : |-t| ^ (1 + 1) = t ^ 2 := ht2
  rw [hexp] at h
  calc |Real.log (1 + t) - t| ≤ t ^ 2 / (1 - |-t|) := h
    _ ≤ t ^ 2 / (1 / 2) := hle
    _ = 2 * t ^ 2 := by ring

/-- From a uniform increment bound, the log-scale sequence is Cauchy and
`u k / k ^ (3/2 : ℝ)` converges to a positive limit. -/
private lemma lr_growth_limit (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
    (K : ℝ) (hK : 0 ≤ K) (k₂ : ℕ)
    (hincr : ∀ k : ℕ, k₂ ≤ k →
      |Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))|
      ≤ (4 * K ^ 2 + K + 12) / (k : ℝ) ^ 2) :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ))
        Filter.atTop (nhds L) := by
  -- The log-scale sequence `v` is Cauchy via summable increments.
  set v : ℕ → ℝ := fun k => Real.log (u k) - 3 / 2 * Real.log (k : ℝ) with hvdef
  have hK' : (0 : ℝ) ≤ 4 * K ^ 2 + K + 12 := by nlinarith [sq_nonneg K, hK]
  have hF : Summable (fun n : ℕ => (4 * K ^ 2 + K + 12 : ℝ) / (n : ℝ) ^ 2) := by
    have hS : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hM := hS.mul_left (4 * K ^ 2 + K + 12)
    refine hM.congr fun n => ?_
    rw [mul_one_div]
  have hG : Summable (fun j : ℕ => (4 * K ^ 2 + K + 12 : ℝ) / (((j + k₂ : ℕ)) : ℝ) ^ 2) :=
    (summable_nat_add_iff k₂).mpr hF
  have hdist : Summable (fun j : ℕ => dist (v (j + k₂)) (v (j + k₂ + 1))) := by
    refine hG.of_nonneg_of_le (fun j => dist_nonneg) fun j => ?_
    have hk : k₂ ≤ j + k₂ := Nat.le_add_left _ _
    have h := hincr (j + k₂) hk
    rw [dist_eq_norm, Real.norm_eq_abs]
    have e : v (j + k₂) - v (j + k₂ + 1)
        = -(Real.log (u (j + k₂ + 1)) - Real.log (u (j + k₂))
          - 3 / 2 * (Real.log (((j + k₂ + 1 : ℕ)) : ℝ)
            - Real.log (((j + k₂ : ℕ)) : ℝ))) := by
      simp only [hvdef]
      ring
    rw [e, abs_neg]
    have hcast2 : ((j + k₂ + 1 : ℕ)) = (j + k₂) + 1 := rfl
    rw [hcast2]
    exact h
  have hshift : CauchySeq (fun j : ℕ => v (j + k₂)) := by
    have hD : Summable (fun j : ℕ => dist ((fun j => v (j + k₂)) j)
        ((fun j => v (j + k₂)) j.succ)) := by
      have e : (fun j : ℕ => dist ((fun j => v (j + k₂)) j)
            ((fun j => v (j + k₂)) j.succ))
            = (fun j : ℕ => dist (v (j + k₂)) (v (j + k₂ + 1))) := by
        funext j
        simp only [Nat.succ_eq_add_one]
        rw [Nat.add_right_comm j 1 k₂]
      rw [e]
      exact hdist
    exact cauchySeq_of_summable_dist hD
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hshift
  have hv_lim : Filter.Tendsto v Filter.atTop (nhds ℓ) := by
    have hiff := tendsto_add_atTop_iff_nat (l := nhds ℓ) (f := v) k₂
    exact hiff.mp hℓ
  -- Exponentiate back.
  have hexp_lim : Filter.Tendsto (fun k : ℕ => Real.exp (v k))
      Filter.atTop (nhds (Real.exp ℓ)) :=
    (Real.continuous_exp.tendsto ℓ).comp hv_lim
  have heq : (fun k : ℕ => Real.exp (v k)) =ᶠ[Filter.atTop]
      (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have huk : 0 < u k := hpos k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have eexp : Real.exp (3 / 2 * Real.log (k : ℝ)) = (k : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hsk]
      congr 1
      ring
    simp only [hvdef]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log huk, Real.exp_neg, eexp]
    simp only [div_eq_mul_inv]
  refine ⟨Real.exp ℓ, Real.exp_pos ℓ, ?_⟩
  exact hexp_lim.congr' heq

/-- Abstract growth lemma: ratios `1 + 3/(2k)` up to `K/k²` force
`u k / k ^ (3/2 : ℝ)` to converge to a positive limit. -/
private lemma lr_growth (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
    (K : ℝ) (hK : 0 ≤ K) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hstep : ∀ k : ℕ, k₀ ≤ k →
      |u (k + 1) / u k - (1 + 3 / (2 * (k : ℝ)))| ≤ K / (k : ℝ) ^ 2) :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ))
        Filter.atTop (nhds L) := by
  have hbase1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) ^ (-1 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hbase2 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) ^ (-2 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun k : ℕ => 3 / (2 * (k : ℝ)))
      Filter.atTop (nhds 0) := by
    have e : (fun k : ℕ => 3 / (2 * (k : ℝ)))
        = (fun k : ℕ => (3 / 2 : ℝ) * (k : ℝ) ^ (-1 : ℝ)) := by
      funext k
      rw [Real.rpow_neg_one]
      ring
    rw [e]
    simpa using hbase1.const_mul (3 / 2 : ℝ)
  have h2 : Filter.Tendsto (fun k : ℕ => K / (k : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    have e : (fun k : ℕ => K / (k : ℝ) ^ 2)
        = (fun k : ℕ => K * (k : ℝ) ^ (-2 : ℝ)) := by
      funext k
      rw [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_two, div_eq_mul_inv]
    rw [e]
    simpa using hbase2.const_mul K
  have hzev : Filter.Tendsto (fun k : ℕ => 3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using h1.add h2
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp
    (hzev.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  set k₂ := max k₁ (max k₀ 2) with hk₂
  have hk₂₀ : k₀ ≤ k₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hk₂₁ : k₁ ≤ k₂ := le_max_left _ _
  have hk₂pos : 1 ≤ k₂ := le_trans hk₀ hk₂₀
  have hk₂two : 2 ≤ k₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsmall : ∀ k : ℕ, k₂ ≤ k →
      3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2 < 1 / 2 :=
    fun k hk => hk₁ k (le_trans hk₂₁ hk)
  have hkr : ∀ k : ℕ, k₂ ≤ k → (0 : ℝ) < (k : ℝ) := by
    intro k hk
    have h1k : 1 ≤ k := le_trans hk₂pos hk
    exact_mod_cast lt_of_lt_of_le zero_lt_one h1k
  have h1k : ∀ k : ℕ, k₂ ≤ k → (1 : ℝ) ≤ (k : ℝ) := by
    intro k hk
    exact_mod_cast le_trans hk₂pos hk
  have hudev : ∀ k : ℕ, k₂ ≤ k →
      |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| ≤ K / (k : ℝ) ^ 2 := by
    intro k hk
    have h := hstep k (le_trans hk₂₀ hk)
    have e : u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))
        = u (k + 1) / u k - (1 + 3 / (2 * (k : ℝ))) := by ring
    rw [e]
    exact h
  have htnn : ∀ k : ℕ, k₂ ≤ k → 0 ≤ 3 / (2 * (k : ℝ)) := by
    intro k hk
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (le_of_lt (hkr k hk)))
  have htbound : ∀ k : ℕ, k₂ ≤ k → |u (k + 1) / u k - 1| ≤ 1 / 2 := by
    intro k hk
    have e : u (k + 1) / u k - 1
        = (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) + 3 / (2 * (k : ℝ)) := by
      ring
    calc |u (k + 1) / u k - 1|
        = |(u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) + 3 / (2 * (k : ℝ))| := by
          rw [← e]
      _ ≤ |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| + |3 / (2 * (k : ℝ))| :=
          abs_add_le _ _
      _ = |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| + 3 / (2 * (k : ℝ)) := by
          rw [abs_of_nonneg (htnn k hk)]
      _ ≤ K / (k : ℝ) ^ 2 + 3 / (2 * (k : ℝ)) := by
          exact add_le_add (hudev k hk) le_rfl
      _ = 3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2 := by ring
      _ ≤ 1 / 2 := le_of_lt (hsmall k hk)
  have hinvbound : ∀ k : ℕ, k₂ ≤ k → |1 / (k : ℝ)| ≤ 1 / 2 := by
    intro k hk
    have hsk := hkr k hk
    have h2k : (2 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast le_trans hk₂two hk
    rw [abs_of_nonneg (le_of_lt (div_pos one_pos hsk))]
    calc 1 / (k : ℝ) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) h2k
      _ = 1 / 2 := rfl
  have hsq2 : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    intro a b
    nlinarith [sq_nonneg (a - b)]
  have htsq : ∀ k : ℕ, k₂ ≤ k →
      (u (k + 1) / u k - 1) ^ 2 ≤ (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by
    intro k hk
    have hB := hudev k hk
    have hsk := hkr k hk
    have hs1 := h1k k hk
    have hsq : (u (k + 1) / u k - 1) ^ 2
        ≤ 2 * (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) ^ 2
          + 2 * (3 / (2 * (k : ℝ))) ^ 2 := by
      have h := hsq2 (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
        (3 / (2 * (k : ℝ)))
      have e : (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          + 3 / (2 * (k : ℝ)) = u (k + 1) / u k - 1 := by ring
      rwa [e] at h
    have hKnn : 0 ≤ K / (k : ℝ) ^ 2 := div_nonneg hK (sq_nonneg _)
    have hB2 : (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) ^ 2
        ≤ (K / (k : ℝ) ^ 2) ^ 2 := by
      have h2 : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
          ≤ |K / (k : ℝ) ^ 2| := by
        rw [abs_of_nonneg hKnn]
        exact hB
      exact sq_le_sq.mpr h2
    have h44 : (K / (k : ℝ) ^ 2) ^ 2 ≤ K ^ 2 / (k : ℝ) ^ 2 := by
      have h1sq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((k : ℝ) - 1), hs1]
      have hKs : K / (k : ℝ) ^ 2 ≤ K := div_le_self hK h1sq
      calc (K / (k : ℝ) ^ 2) ^ 2
          = (K / (k : ℝ) ^ 2) * (K / (k : ℝ) ^ 2) := pow_two _
        _ ≤ (K / (k : ℝ) ^ 2) * K :=
            mul_le_mul_of_nonneg_left hKs hKnn
        _ = K ^ 2 / (k : ℝ) ^ 2 := by ring
    have h32 : (3 / (2 * (k : ℝ))) ^ 2 = (9 / 4) / (k : ℝ) ^ 2 := by
      rw [div_pow, show (3 : ℝ) ^ 2 = 9 by norm_num,
        show (2 * (k : ℝ)) ^ 2 = 4 * (k : ℝ) ^ 2 by ring]
      ring
    have hfin : 2 * ((K / (k : ℝ) ^ 2) ^ 2) + 2 * ((9 / 4) / (k : ℝ) ^ 2)
        ≤ (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by
      have h2a := mul_le_mul_of_nonneg_left h44 (show (0 : ℝ) ≤ 2 by norm_num)
      have e : 2 * (K ^ 2 / (k : ℝ) ^ 2) + 2 * ((9 / 4) / (k : ℝ) ^ 2)
          = (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by ring
      linarith
    linarith [hsq, hB2, h32, hfin]
  have htri : ∀ a b c : ℝ, |a + b - c| ≤ |a| + |b| + |c| := by
    intro a b c
    calc |a + b - c| = |(a + b) + (-c)| := by rw [sub_eq_add_neg]
      _ ≤ |a + b| + |-c| := abs_add_le _ _
      _ = |a + b| + |c| := by rw [abs_neg]
      _ ≤ (|a| + |b|) + |c| := by
          have h := abs_add_le a b
          linarith
      _ = |a| + |b| + |c| := by ring
  have hincr : ∀ k : ℕ, k₂ ≤ k →
      |Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))|
      ≤ (4 * K ^ 2 + K + 12) / (k : ℝ) ^ 2 := by
    intro k hk
    have huk : 0 < u k := hpos k (le_trans hk₂pos hk)
    have huk1 : 0 < u (k + 1) :=
      hpos (k + 1) (by omega)
    have hsk := hkr k hk
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have e1 : Real.log (u (k + 1)) - Real.log (u k)
        = Real.log (u (k + 1) / u k) :=
      (Real.log_div (ne_of_gt huk1) (ne_of_gt huk)).symm
    have e2 : Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ)
        = Real.log (1 + 1 / (k : ℝ)) := by
      have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith [hsk]
      rw [hcast, ← Real.log_div (ne_of_gt hpos1) (ne_of_gt hsk)]
      congr 1
      rw [add_div, div_self (ne_of_gt hsk)]
    have e3 : Real.log (u (k + 1) / u k)
        = Real.log (1 + (u (k + 1) / u k - 1)) := by
      congr 1
      ring
    have key : Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))
        = (Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)) := by
      rw [e1, e2, e3]
      ring
    have hA : |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
        ≤ 2 * (u (k + 1) / u k - 1) ^ 2 :=
      lr_log_one_add_le _ (htbound k hk)
    have hB : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| ≤ K / (k : ℝ) ^ 2 :=
      hudev k hk
    have hC : |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|
        ≤ 2 * (1 / (k : ℝ)) ^ 2 :=
      lr_log_one_add_le _ (hinvbound k hk)
    have hC2 : (1 / (k : ℝ)) ^ 2 = 1 / (k : ℝ) ^ 2 := by
      rw [div_pow, one_pow]
    have htsqk := htsq k hk
    rw [key]
    have hmul : |3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))|
        = 3 / 2 * |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hle : |(Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))|
        ≤ |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
          + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
          + |3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))| :=
      htri _ _ _
    rw [hmul] at hle
    -- Clear denominators by multiplying with `S = (k:ℝ)^2 > 0`.
    have hS : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hsk 2
    have hSne : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hS
    have gA : |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
          * (k : ℝ) ^ 2
        ≤ 2 * ((u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hA hS.le
      linarith [h]
    have gB : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| * (k : ℝ) ^ 2 ≤ K := by
      have h := mul_le_mul_of_nonneg_right hB hS.le
      rwa [div_mul_cancel₀ _ hSne] at h
    have gC : |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)| * (k : ℝ) ^ 2 ≤ 2 := by
      have h := mul_le_mul_of_nonneg_right hC hS.le
      have e : (2 * (1 / (k : ℝ)) ^ 2) * (k : ℝ) ^ 2 = 2 := by
        rw [hC2, mul_assoc, div_mul_cancel₀ _ hSne, mul_one]
      rwa [e] at h
    have gt : (u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2 ≤ 2 * K ^ 2 + 9 / 2 := by
      have h := mul_le_mul_of_nonneg_right htsqk hS.le
      rwa [div_mul_cancel₀ _ hSne] at h
    have gV : |(Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))| * (k : ℝ) ^ 2
        ≤ 4 * K ^ 2 + K + 12 := by
      have hstep := mul_le_mul_of_nonneg_right hle hS.le
      have e : (|Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
            + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
            + 3 / 2 * |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|) * (k : ℝ) ^ 2
          = |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
            * (k : ℝ) ^ 2
            + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| * (k : ℝ) ^ 2
            + 3 / 2 * (|Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|
              * (k : ℝ) ^ 2) := by
        ring
      have h2 : 2 * ((u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2)
          ≤ 2 * (2 * K ^ 2 + 9 / 2) := by
        linarith [gt]
      linarith [hstep, e, gA, gB, gC, h2]
    exact (le_div_iff₀ hS).mpr gV
  exact lr_growth_limit u hpos K hK k₂ hincr

/-- `B(x)`: the `k`-sum in the two-squares decomposition. -/
private noncomputable def lrB (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2)

/-- `lrH n = 1` unfolds to the defining condition. -/
private lemma lrH_eq_one {n : ℕ} :
    lrH n = 1 ↔ n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 := by
  unfold lrH
  by_cases h : n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p % 4 ≠ 3 <;> simp [h]

/-- `lrG k = 1` unfolds to the defining condition. -/
private lemma lrG_eq_one {k : ℕ} :
    lrG k = 1 ↔ k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 := by
  unfold lrG
  by_cases h : k ≠ 0 ∧ ∀ p ∈ k.primeFactors, p % 4 = 3 <;> simp [h]

/-- `lrH` takes only the values `0` and `1`. -/
private lemma lrH_01 (n : ℕ) : lrH n = 0 ∨ lrH n = 1 := by
  unfold lrH
  split_ifs <;> simp

/-- `lrG` takes only the values `0` and `1`. -/
private lemma lrG_01 (k : ℕ) : lrG k = 0 ∨ lrG k = 1 := by
  unfold lrG
  split_ifs <;> simp

/-- A product `k ^ 2 * m` with `lrH m = 1` is a sum of two squares
(the `k ^ 2` part always contributes even valuations). -/
private lemma lr_sq_mul_mem {k m : ℕ} (hk0 : k ≠ 0) (hm0 : m ≠ 0)
    (hm : lrH m = 1) :
    ∃ a b : ℕ, k ^ 2 * m = a ^ 2 + b ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq3
  have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqP⟩
  have hqm : ¬ q ∣ m := by
    intro hdvd
    have hmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hqP, hdvd, hm0⟩
    exact (lrH_eq_one.mp hm).2 q hmem hq3
  have h1 : padicValNat q m = 0 := padicValNat.eq_zero_of_not_dvd hqm
  have h2 : padicValNat q (k ^ 2 * m) = 2 * padicValNat q k := by
    rw [padicValNat.mul (pow_ne_zero 2 hk0) hm0, padicValNat.pow, h1, add_zero]
  rw [h2]
  exact ⟨padicValNat q k, by ring⟩

/-- Uniqueness of the `k ^ 2 * m` decomposition. -/
private lemma lr_sq_mul_inj {k m k' m' : ℕ} (hk0 : k ≠ 0) (hm0 : m ≠ 0)
    (hk0' : k' ≠ 0) (hm0' : m' ≠ 0)
    (hk : lrG k = 1) (hm : lrH m = 1) (hk' : lrG k' = 1) (hm' : lrH m' = 1)
    (h : k ^ 2 * m = k' ^ 2 * m') : k = k' ∧ m = m' := by
  have hkk : k = k' := by
    apply Nat.eq_of_factorization_eq hk0 hk0'
    intro p
    by_cases hpP : p.Prime
    · have : Fact p.Prime := ⟨hpP⟩
      have hval : padicValNat p (k ^ 2 * m) = padicValNat p (k' ^ 2 * m') := by
        rw [h]
      rw [padicValNat.mul (pow_ne_zero 2 hk0) hm0, padicValNat.pow,
        padicValNat.mul (pow_ne_zero 2 hk0') hm0', padicValNat.pow] at hval
      by_cases hp3 : p % 4 = 3
      · have hvm : padicValNat p m = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ m.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hm0⟩
          exact (lrH_eq_one.mp hm).2 p hmem hp3
        have hvm' : padicValNat p m' = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ m'.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hm0'⟩
          exact (lrH_eq_one.mp hm').2 p hmem hp3
        have hkk2 : padicValNat p k = padicValNat p k' := by omega
        rw [Nat.factorization_def _ hpP, Nat.factorization_def _ hpP, hkk2]
      · have hvk : padicValNat p k = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ k.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hk0⟩
          exact hp3 ((lrG_eq_one.mp hk).2 p hmem)
        have hvk' : padicValNat p k' = 0 := by
          apply padicValNat.eq_zero_of_not_dvd
          intro hdvd
          have hmem : p ∈ k'.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpP, hdvd, hk0'⟩
          exact hp3 ((lrG_eq_one.mp hk').2 p hmem)
        rw [Nat.factorization_def _ hpP, Nat.factorization_def _ hpP, hvk, hvk']
    · rw [Nat.factorization_eq_zero_of_not_prime _ hpP,
        Nat.factorization_eq_zero_of_not_prime _ hpP]
  refine ⟨hkk, ?_⟩
  rw [hkk] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hk0') h

/-- Every positive sum of two squares splits as `k ^ 2 * m` with `lrG k = lrH m = 1`. -/
private lemma lr_exists_sq_mul {n : ℕ} (hn1 : 1 ≤ n)
    (hsq : ∃ a b : ℕ, n = a ^ 2 + b ^ 2) :
    ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧ lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m = n := by
  have hn0 : n ≠ 0 := by omega
  have hchar := Nat.eq_sq_add_sq_iff.mp hsq
  set S : Finset ℕ := n.primeFactors.filter (fun p => p % 4 = 3) with hSdef
  set k : ℕ := ∏ p ∈ S, p ^ (n.factorization p / 2) with hkdef
  have hmemS : ∀ p ∈ S, p.Prime ∧ p % 4 = 3 := by
    intro p hp
    have hpf : p ∈ n.primeFactors := Finset.mem_of_mem_filter p hp
    exact ⟨Nat.prime_of_mem_primeFactors hpf, (Finset.mem_filter.mp hp).2⟩
  have heven : ∀ p ∈ S, Even (n.factorization p) := by
    intro p hp
    have hpf : p ∈ n.primeFactors := Finset.mem_of_mem_filter p hp
    have hpp := (hmemS p hp).1
    rw [Nat.factorization_def n hpp]
    exact hchar p hpf (hmemS p hp).2
  have hksq : k ^ 2 = ∏ p ∈ S, p ^ (n.factorization p) := by
    rw [hkdef, pow_two, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨t, ht⟩ := heven p hp
    have hv2 : n.factorization p / 2 = t := by omega
    rw [hv2, ← pow_add, ← ht]
  have hprod_eq : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at h
  have hdvd : k ^ 2 ∣ n := by
    have hsub : S ⊆ n.primeFactors := Finset.filter_subset _ _
    have h := Finset.prod_sdiff hsub (f := fun p => p ^ (n.factorization p))
    rw [mul_comm] at h
    have h2 : k ^ 2 ∣ ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      rw [hksq]
      exact ⟨∏ x ∈ n.primeFactors \ S, x ^ (n.factorization x), h.symm⟩
    rwa [hprod_eq] at h2
  obtain ⟨m, hm⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rw [hkdef]
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpp := (hmemS p hp).1
    exact pow_ne_zero _ (ne_of_gt hpp.pos)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hkm_eq : k ^ 2 * m = n := hm.symm
  have hm0 : m ≠ 0 := by
    intro hcon
    apply hn0
    calc n = k ^ 2 * m := hm
      _ = 0 := by rw [hcon, mul_zero]
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  have hGk : lrG k = 1 := by
    rw [lrG_eq_one]
    refine ⟨hk0, fun q hq => ?_⟩
    have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ k := Nat.dvd_of_mem_primeFactors hq
    rw [hkdef] at hqdvd
    obtain ⟨p, hpS, hqp⟩ :=
      (Nat.prime_iff.mp hqP).dvd_finsetProd_iff _ |>.mp hqdvd
    have hqp2 : q ∣ p := hqP.dvd_of_dvd_pow hqp
    have hpP : p.Prime := (hmemS p hpS).1
    have hqp3 : q = p := (Nat.prime_dvd_prime_iff_eq hqP hpP).mp hqp2
    rw [hqp3]
    exact (hmemS p hpS).2
  have hHm : lrH m = 1 := by
    rw [lrH_eq_one]
    refine ⟨hm0, fun q hq => ?_⟩
    have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    intro hq3
    have hmn : m ∣ n := by
      have h := dvd_mul_left m (k ^ 2)
      rwa [hkm_eq] at h
    have hqn : q ∣ n := dvd_trans hqdvd hmn
    have hmem_n : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqP, hqn, hn0⟩
    have hqS : q ∈ S := Finset.mem_filter.mpr ⟨hmem_n, hq3⟩
    have hpow_dvd_k2 : q ^ (n.factorization q) ∣ k ^ 2 := by
      rw [hksq]
      exact Finset.dvd_prod_of_mem _ hqS
    have hpow_dvd_m : q ^ (m.factorization q) ∣ m := Nat.ordProj_dvd m q
    have hmul_dvd : q ^ (n.factorization q) * q ^ (m.factorization q) ∣ k ^ 2 * m :=
      mul_dvd_mul hpow_dvd_k2 hpow_dvd_m
    rw [hkm_eq] at hmul_dvd
    rw [← pow_add] at hmul_dvd
    have hle : n.factorization q + m.factorization q ≤ n.factorization q :=
      (Nat.Prime.pow_dvd_iff_le_factorization hqP hn0).mp hmul_dvd
    have hposv : 1 ≤ m.factorization q := by
      have hqdvd1 : q ^ 1 ∣ m := by rwa [pow_one]
      exact (Nat.Prime.pow_dvd_iff_le_factorization hqP hm0).mp hqdvd1
    omega
  exact ⟨k, m, hk1, hm1, hGk, hHm, hkm_eq⟩

/-- Decomposition of the two-squares count: the number of `n ≤ x`, `n ≥ 1`,
that are a sum of two squares equals `B(x)`. -/
private lemma lr_twoSq_count_eq {x : ℝ} (hx : 0 ≤ x) :
    ((Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
      (Finset.Ioc 0 ⌊x⌋₊)).card : ℝ) = lrB x := by
  classical
  set T : Finset (Σ _ : ℕ, ℕ) := (Finset.Ioc 0 ⌊x⌋₊).sigma
    (fun k => (Finset.Ioc 0 ⌊x⌋₊).filter
      (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)) with hTdef
  have himg : Finset.image (fun p : Σ _ : ℕ, ℕ => p.1 ^ 2 * p.2) T
      = Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨k, m⟩, hkm, rfl⟩
      obtain ⟨hkI, hmF⟩ := Finset.mem_sigma.mp hkm
      obtain ⟨hmI, hGk, hHm, hle⟩ := Finset.mem_filter.mp hmF
      obtain ⟨hk0, hkN⟩ := Finset.mem_Ioc.mp hkI
      obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hmI
      have hk0k : 0 < k := hk0
      have hm0m : 0 < m := hm0
      have hpos : 0 < k ^ 2 * m :=
        Nat.mul_pos (pow_pos hk0k 2) hm0m
      refine ⟨Finset.mem_Ioc.mpr ⟨hpos, hle⟩,
        lr_sq_mul_mem (ne_of_gt hk0k) (ne_of_gt hm0m) hHm⟩
    · rintro ⟨hnI, hsq⟩
      obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hnI
      obtain ⟨k, m, hk1, hm1, hGk, hHm, hkm⟩ := lr_exists_sq_mul hn0 hsq
      have hpos : 0 < k ^ 2 * m := by
        rw [hkm]
        omega
      have hk_le : k ≤ k ^ 2 * m :=
        Nat.le_of_dvd hpos ⟨k * m, by ring⟩
      have hm_le : m ≤ k ^ 2 * m :=
        Nat.le_of_dvd hpos ⟨k ^ 2, by ring⟩
      refine ⟨⟨k, m⟩, ?_, hkm⟩
      rw [hTdef]
      refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨hk1, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hm1, ?_⟩, hGk, hHm, ?_⟩⟩
      · exact le_trans hk_le (hkm ▸ hnN)
      · exact le_trans hm_le (hkm ▸ hnN)
      · rw [hkm]
        exact hnN
  have hinj : Set.InjOn (fun p : Σ _ : ℕ, ℕ => p.1 ^ 2 * p.2) (↑T) := by
    intro a ha b hb hab
    obtain ⟨k, m⟩ := a
    obtain ⟨k', m'⟩ := b
    have ha' := Finset.mem_coe.mp ha
    have hb' := Finset.mem_coe.mp hb
    obtain ⟨hkI, hmF⟩ := Finset.mem_sigma.mp ha'
    obtain ⟨hmI, hGk, hHm, -⟩ := Finset.mem_filter.mp hmF
    obtain ⟨hkI', hmF'⟩ := Finset.mem_sigma.mp hb'
    obtain ⟨hmI', hGk', hHm', -⟩ := Finset.mem_filter.mp hmF'
    have hk0k : 0 < k := (Finset.mem_Ioc.mp hkI).1
    have hm0m : 0 < m := (Finset.mem_Ioc.mp hmI).1
    have hk0k' : 0 < k' := (Finset.mem_Ioc.mp hkI').1
    have hm0m' : 0 < m' := (Finset.mem_Ioc.mp hmI').1
    have hab' : k ^ 2 * m = k' ^ 2 * m' := hab
    have hk0n : k ≠ 0 := ne_of_gt hk0k
    have hm0n : m ≠ 0 := ne_of_gt hm0m
    have hk0n' : k' ≠ 0 := ne_of_gt hk0k'
    have hm0n' : m' ≠ 0 := ne_of_gt hm0m'
    obtain ⟨hkk, hmm⟩ :=
      lr_sq_mul_inj hk0n hm0n hk0n' hm0n' hGk hHm hGk' hHm' hab'
    subst hkk
    subst hmm
    rfl
  have hcardT : (T.card : ℝ) = lrB x := by
    have hsigma : T.card = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)).card := by
      rw [hTdef]
      exact Finset.card_sigma _ _
    have hlrB : lrB x
        = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2) := rfl
    rw [hsigma, Nat.cast_sum, hlrB]
    apply Finset.sum_congr rfl
    intro k hkI
    have hk1 : 1 ≤ k := (Finset.mem_Ioc.mp hkI).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hcast : ∀ m : ℕ, ((k ^ 2 * m : ℕ) : ℝ) = (k : ℝ) ^ 2 * (m : ℝ) := by
      intro m
      push_cast
      ring
    by_cases hGk : lrG k = 1
    · have hfib : (Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊)
          = (Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊).filter (fun m => lrH m = 1) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hm0, hmN⟩, -, hHm, hle⟩
          have hleR : (k : ℝ) ^ 2 * (m : ℝ) ≤ x := by
            have h1 : ((k ^ 2 * m : ℕ) : ℝ) ≤ x :=
              le_trans (by exact_mod_cast hle) (Nat.floor_le hx)
            rwa [hcast] at h1
          have hmk : (m : ℝ) ≤ x / (k : ℝ) ^ 2 := by
            rw [le_div_iff₀ (pow_pos hkpos 2)]
            linear_combination hleR
          exact ⟨⟨hm0, Nat.le_floor hmk⟩, hHm⟩
        · rintro ⟨⟨hm0, hmN'⟩, hHm⟩
          have hmk : (m : ℝ) ≤ x / (k : ℝ) ^ 2 :=
            le_trans (by exact_mod_cast hmN')
              (Nat.floor_le (by positivity))
          have hleR : (k : ℝ) ^ 2 * (m : ℝ) ≤ x := by
            have h2 := (le_div_iff₀ (pow_pos hkpos 2)).mp hmk
            linear_combination h2
          have hle : k ^ 2 * m ≤ ⌊x⌋₊ := by
            apply Nat.le_floor
            rw [hcast]
            exact hleR
          have hkk2 : x / (k : ℝ) ^ 2 ≤ x := by
            apply div_le_self hx
            calc (1 : ℝ) = 1 ^ 2 := by norm_num
              _ ≤ (k : ℝ) ^ 2 :=
                pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hk1) 2
          have hmN : m ≤ ⌊x⌋₊ := Nat.le_floor (le_trans hmk hkk2)
          exact ⟨⟨hm0, hmN⟩, hGk, hHm, hle⟩
      rw [hfib]
      have hcard : (((Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊).filter
          (fun m => lrH m = 1)).card : ℝ) = lrCount (x / (k : ℝ) ^ 2) := by
        have hlrC : lrCount (x / (k : ℝ) ^ 2)
            = ∑ m ∈ Finset.Ioc 0 ⌊x / (k : ℝ) ^ 2⌋₊, lrH m := rfl
        rw [hlrC, ← Finset.sum_boole]
        apply Finset.sum_congr rfl
        intro m _
        rcases lrH_01 m with h0 | h1
        · simp [h0]
        · simp [h1]
      rw [hcard, hGk, one_mul]
    · have hGk0 : lrG k = 0 := by
        rcases lrG_01 k with h | h
        · exact h
        · exact absurd h hGk
      have hfib_empty : (Finset.Ioc 0 ⌊x⌋₊).filter
          (fun m => lrG k = 1 ∧ lrH m = 1 ∧ k ^ 2 * m ≤ ⌊x⌋₊) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m _
        simp [hGk0]
      rw [hfib_empty, Finset.card_empty, Nat.cast_zero, hGk0, zero_mul]
  have h1 : (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
      (Finset.Ioc 0 ⌊x⌋₊)).card = T.card := by
    rw [← himg]
    exact Finset.card_image_of_injOn hinj
  rw [h1]
  exact hcardT

/-- The `Set.ncard` of the Wanted set is one plus the positive count. -/
private lemma lr_ncard_eq {x : ℝ} (hx : 0 ≤ x) :
    Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2}
      = (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.Ioc 0 ⌊x⌋₊)).card + 1 := by
  have hset : {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2}
      = ↑(Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.range (⌊x⌋₊ + 1))) := by
    ext m
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨hmx, hsq⟩
      have hle : m ≤ ⌊x⌋₊ := Nat.le_floor hmx
      exact ⟨by omega, hsq⟩
    · rintro ⟨hm, hsq⟩
      have hle : m ≤ ⌊x⌋₊ := by omega
      have hcast : (m : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hle
      exact ⟨le_trans hcast (Nat.floor_le hx), hsq⟩
  have hsplit : Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.range (⌊x⌋₊ + 1))
      = Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
          (Finset.Ioc 0 ⌊x⌋₊) ∪ {0} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hsq⟩
      by_cases hm0 : m = 0
      · exact Or.inr hm0
      · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
        exact Or.inl ⟨⟨hpos, by omega⟩, hsq⟩
    · rintro (⟨⟨hm0, hmN⟩, hsq⟩ | rfl)
      · exact ⟨by omega, hsq⟩
      · exact ⟨Nat.zero_lt_succ _, 0, 0, by simp⟩
  have hdisj : Disjoint
      (Finset.filter (fun n : ℕ => ∃ a b : ℕ, n = a ^ 2 + b ^ 2)
        (Finset.Ioc 0 ⌊x⌋₊)) {0} := by
    rw [Finset.disjoint_left]
    intro m hmI hm0
    rw [Finset.mem_filter, Finset.mem_Ioc] at hmI
    rw [Finset.mem_singleton] at hm0
    omega
  rw [hset, Set.ncard_coe_finset, hsplit,
    Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

/-- Ratio bounds for `J` at exponential points: the input for `lr_growth`. -/
private lemma lr_J_ratio :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      |lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))| ≤ K / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := lr_J_near
  obtain ⟨D, hD, hCD⟩ : ∃ D : ℝ, 0 ≤ D ∧ C ≤ D :=
    ⟨|C|, abs_nonneg _, le_abs_self _⟩
  have hC' : ∀ x : ℝ, 1 ≤ x →
      |lrJ x - 2 / 3 * lrA x * Real.log x| ≤ 2 / 3 * D * lrA x := by
    intro x hx
    have h := hC x hx
    have hA := lrA_nonneg x
    have h3 : C * lrA x ≤ D * lrA x :=
      mul_le_mul_of_nonneg_right hCD hA
    calc |lrJ x - 2 / 3 * lrA x * Real.log x| ≤ 2 / 3 * C * lrA x := h
      _ ≤ 2 / 3 * D * lrA x := by linarith [h3]
  have hE : ∀ k : ℕ, (1 : ℝ) ≤ Real.exp (k : ℝ) := by
    intro k
    have h := Real.add_one_le_exp (k : ℝ)
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA1 : lrA 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrA
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
  have hJ1zero : lrJ 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrJ
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
  have hlogR : ∀ k : ℕ,
      Real.log (Real.exp (((k + 1 : ℕ)) : ℝ) / Real.exp (k : ℝ)) = 1 := by
    intro k
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp, Real.log_exp, hcast]
    ring
  have hEmono : ∀ k : ℕ,
      Real.exp (k : ℝ) ≤ Real.exp (((k + 1 : ℕ)) : ℝ) := by
    intro k
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    apply Real.exp_le_exp_of_le
    linarith
  have hJ1 : 1 ≤ lrJ (Real.exp 1) := by
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := lr_J_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
    have hlog : Real.log (Real.exp 1 / 1) = 1 := by
      rw [div_one, Real.log_exp]
    rw [hA1, hJ1zero, hlog] at lo
    linarith
  have hJk : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ lrJ (Real.exp (k : ℝ)) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1k : Real.exp 1 ≤ Real.exp (k : ℝ) :=
      Real.exp_le_exp_of_le hkR
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := lr_J_increment h1e h1k
    have hnn : 0 ≤ lrA (Real.exp 1)
        * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
      apply mul_nonneg (lrA_nonneg _)
      apply Real.log_nonneg
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa using h1k
    linarith [lo, hnn, hJ1]
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * D + 2)
  have hk₀R : 2 * D + 2 < (k₀ : ℝ) := hk₀
  have hk₀pos : 1 ≤ k₀ := by
    have hle : (1 : ℝ) ≤ (k₀ : ℝ) := by linarith [hk₀R, hD]
    exact_mod_cast hle
  refine ⟨3 * (2 * D + 1) / 2, by linarith [hD], k₀, hk₀pos, fun k hk => ?_⟩
  have hs1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hk₀pos hk
  have hsk : (0 : ℝ) < (k : ℝ) := by linarith
  have hsk2 : 2 * D + 2 ≤ (k : ℝ) := le_trans hk₀R.le (by exact_mod_cast hk)
  have hJpos : 0 < lrJ (Real.exp (k : ℝ)) := by
    have h := hJk k (le_trans hk₀pos hk)
    linarith
  have hN6k := hC' (Real.exp (k : ℝ)) (hE k)
  rw [Real.log_exp] at hN6k
  have hN6k1 := hC' (Real.exp (((k + 1 : ℕ)) : ℝ)) (hE (k + 1))
  have hlogk1 : Real.log (Real.exp (((k + 1 : ℕ)) : ℝ)) = ((k + 1 : ℕ) : ℝ) :=
    Real.log_exp _
  rw [hlogk1] at hN6k1
  obtain ⟨hN7lo, hN7hi⟩ := lr_J_increment (hE k) (hEmono k)
  rw [hlogR k, mul_one] at hN7lo hN7hi
  have hposSD : (0 : ℝ) < (k : ℝ) + D := add_pos_of_pos_of_nonneg hsk hD
  have hposT : (0 : ℝ) < ((k : ℝ) + 1) - D := by linarith [hsk2, hD]
  have hSDne : (k : ℝ) + D ≠ 0 := ne_of_gt hposSD
  have hTne : ((k : ℝ) + 1) - D ≠ 0 := ne_of_gt hposT
  have hsne : (k : ℝ) ≠ 0 := ne_of_gt hsk
  have hs2ne : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hsne
  have hAlo : (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ lrA (Real.exp (k : ℝ)) := by
    have hhi := (abs_le.mp hN6k).2
    have hle : lrJ (Real.exp (k : ℝ))
        ≤ (2 / 3) * ((k : ℝ) + D) * lrA (Real.exp (k : ℝ)) := by
      linarith [hhi]
    have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + D) :=
      div_nonneg (by norm_num) hposSD.le
    have h := mul_le_mul_of_nonneg_right hle hpos
    have e1 : ((2 / 3) * ((k : ℝ) + D) * lrA (Real.exp (k : ℝ)))
          * ((3 / 2) / ((k : ℝ) + D))
        = lrA (Real.exp (k : ℝ)) := by
      field_simp
    have e0 : lrJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + D))
        = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e0, e1] at h
    exact h
  have hA'hi : lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) := by
    have hlo := (abs_le.mp hN6k1).1
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hle' : (2 / 3) * (((k : ℝ) + 1) - D)
          * lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
        ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      have e : (2 / 3) * (((k : ℝ) + 1) - D)
            * lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
          = (2 / 3) * lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) * (((k + 1 : ℕ)) : ℝ)
            - (2 / 3) * D * lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
        rw [hcast]
        ring
      rw [e]
      linarith [hlo]
    have hpos : (0 : ℝ) ≤ 3 / (2 * (((k : ℝ) + 1) - D)) :=
      div_nonneg (by norm_num) (mul_nonneg (by norm_num) hposT.le)
    have h := mul_le_mul_of_nonneg_right hle' hpos
    have e1 : ((2 / 3) * (((k : ℝ) + 1) - D)
          * lrA (Real.exp (((k + 1 : ℕ)) : ℝ)))
          * (3 / (2 * (((k : ℝ) + 1) - D)))
        = lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      field_simp
    rw [e1] at h
    exact h
  have h1 : (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ)) :=
    le_trans hAlo hN7lo
  have h2 : (3 / 2) / ((k : ℝ) + D)
      ≤ (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ)))
        / lrJ (Real.exp (k : ℝ)) := by
    rw [le_div_iff₀ hJpos]
    have e : ((3 / 2) / ((k : ℝ) + D)) * lrJ (Real.exp (k : ℝ))
        = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e]
    exact h1
  have eJJ : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)) - 1
      = (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ)))
        / lrJ (Real.exp (k : ℝ)) := by
    rw [← div_self (ne_of_gt hJpos), ← sub_div]
  have h3 : 1 + (3 / 2) / ((k : ℝ) + D)
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)) := by
    linarith [h2, eJJ]
  have e' : (3 / 2) / ((k : ℝ) + D) - 3 / (2 * (k : ℝ))
      = 3 * D ^ 2 / (2 * (k : ℝ) ^ 2 * ((k : ℝ) + D))
        - (3 * D / 2) / (k : ℝ) ^ 2 := by
    field_simp
    ring
  have hdenpos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 * ((k : ℝ) + D) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hsk 2)) hposSD
  have hnn : (0 : ℝ) ≤ 3 * D ^ 2 / (2 * (k : ℝ) ^ 2 * ((k : ℝ) + D)) :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg D)) hdenpos.le
  have h4 : -((3 * D / 2) / (k : ℝ) ^ 2)
      ≤ (3 / 2) / ((k : ℝ) + D) - 3 / (2 * (k : ℝ)) := by
    rw [e']
    linarith [hnn]
  have hlow : -((3 * D / 2) / (k : ℝ) ^ 2)
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ))) := by
    linarith [h3, h4]
  have h5 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) - lrJ (Real.exp (k : ℝ))
      ≤ lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) :=
    le_trans hN7hi hA'hi
  have h6 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
      ≤ lrJ (Real.exp (k : ℝ)) := by
    linarith [h5]
  have hTs : (k : ℝ) ≤ 2 * (((k : ℝ) + 1) - D) - 3 := by linarith [hsk2]
  have h2T3pos : (0 : ℝ) < 2 * (((k : ℝ) + 1) - D) - 3 := by
    linarith [hTs, hsk]
  have h2T3ne : 2 * (((k : ℝ) + 1) - D) - 3 ≠ 0 := ne_of_gt h2T3pos
  have h2Tne : 2 * (((k : ℝ) + 1) - D) ≠ 0 :=
    mul_ne_zero (by norm_num) hTne
  have h2sne : 2 * (k : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hsne
  have hδ : 3 / (2 * (((k : ℝ) + 1) - D)) < 1 := by
    have hT32 : (3 : ℝ) / 2 < ((k : ℝ) + 1) - D := by linarith [hsk2, hD]
    rw [div_lt_one (by linarith [hposT] : (0 : ℝ) < 2 * (((k : ℝ) + 1) - D))]
    linarith [hT32]
  have h1δ : (0 : ℝ) < 1 - 3 / (2 * (((k : ℝ) + 1) - D)) := by linarith [hδ]
  have h1δne : (1 - 3 / (2 * (((k : ℝ) + 1) - D))) ≠ 0 := ne_of_gt h1δ
  have h7 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
      ≤ 1 / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    rw [le_div_iff₀ h1δ]
    have e : (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)))
          * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
        = (lrJ (Real.exp (((k + 1 : ℕ)) : ℝ))
            * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))) / lrJ (Real.exp (k : ℝ)) := by
      ring
    rw [e, div_le_one hJpos]
    exact h6
  have hfrac : 1 / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) - 1
      = (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    field_simp
    ring
  have hfrac2 : (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
      = 3 / (2 * (((k : ℝ) + 1) - D) - 3) := by
    field_simp
  have h10 : 3 / (2 * (((k : ℝ) + 1) - D) - 3) - 3 / (2 * (k : ℝ))
      = 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3)) := by
    field_simp
    ring
  have hden_ge : 2 * (k : ℝ) ^ 2
      ≤ 2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3) := by
    have h := mul_le_mul_of_nonneg_left hTs (show (0 : ℝ) ≤ 2 * (k : ℝ) by
      linarith [hsk])
    linarith [h]
  have hnum_nn : (0 : ℝ) ≤ 3 * (2 * D + 1) := by linarith [hD]
  have hden_pos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by
    have h := pow_pos hsk 2
    linarith [h]
  have h11 : 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
      ≤ 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2) := by
    have h1 : (1 : ℝ) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
        ≤ 1 / (2 * (k : ℝ) ^ 2) :=
      one_div_le_one_div_of_le hden_pos hden_ge
    have e1 : 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
        = 3 * (2 * D + 1) * (1 / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))) := by
      rw [div_eq_mul_inv, inv_eq_one_div]
    have e2 : 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2)
        = 3 * (2 * D + 1) * (1 / (2 * (k : ℝ) ^ 2)) := by
      rw [div_eq_mul_inv, inv_eq_one_div]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1 hnum_nn
  have h8 : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ)) - 1
      ≤ (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    linarith [h7, hfrac]
  have hup : lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))
      ≤ (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2 := by
    have efin : (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2
        = 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2) := by ring
    linarith [h8, hfrac2, h10, h11, efin]
  have hfin : |lrJ (Real.exp (((k + 1 : ℕ)) : ℝ)) / lrJ (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))| ≤ (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2 := by
    rw [abs_le]
    constructor
    · have hKlo : -((3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2)
          ≤ -((3 * D / 2) / (k : ℝ) ^ 2) := by
        have h : (3 * D / 2) ≤ 3 * (2 * D + 1) / 2 := by linarith [hD]
        have h2 : -(3 * (2 * D + 1) / 2) ≤ -(3 * D / 2) := by linarith [h]
        have e1 : -((3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2)
            = (-(3 * (2 * D + 1) / 2)) / (k : ℝ) ^ 2 := by ring
        have e2 : -((3 * D / 2) / (k : ℝ) ^ 2)
            = (-(3 * D / 2)) / (k : ℝ) ^ 2 := by ring
        rw [e1, e2, div_le_div_iff_of_pos_right (pow_pos hsk 2)]
        exact h2
      linarith [hlow, hKlo]
    · exact hup
  exact hfin

/-- `J` at exponential points is positive. -/
private lemma lr_J_exp_pos : ∀ k : ℕ, 1 ≤ k → 0 < lrJ (Real.exp (k : ℝ)) := by
  have hA1 : lrA 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrA
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
  have hJ1zero : lrJ 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold lrJ
    rw [hfl, hIoc, Finset.sum_singleton]
    simp [lrH_one]
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hJ1 : 1 ≤ lrJ (Real.exp 1) := by
    obtain ⟨lo, _⟩ := lr_J_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
    have hlog : Real.log (Real.exp 1 / 1) = 1 := by
      rw [div_one, Real.log_exp]
    rw [hA1, hJ1zero, hlog] at lo
    linarith
  intro k hk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1k : Real.exp 1 ≤ Real.exp (k : ℝ) :=
    Real.exp_le_exp_of_le hkR
  have hEk : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
    have h := Real.add_one_le_exp (k : ℝ)
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨lo, _⟩ := lr_J_increment h1e h1k
  have hnn : 0 ≤ lrA (Real.exp 1)
      * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
    apply mul_nonneg (lrA_nonneg _)
    apply Real.log_nonneg
    rw [le_div_iff₀ (Real.exp_pos _)]
    simpa using h1k
  linarith [lo, hnn, hJ1]

/-- `k / (k + c) → 1` along naturals. -/
private lemma lr_nat_div_add_tendsto (c : ℝ) :
    Filter.Tendsto (fun k : ℕ => (k : ℝ) / ((k : ℝ) + c))
      Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto (fun k : ℕ => c / (k : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have h1 : Filter.Tendsto (fun k : ℕ => 1 + c / (k : ℝ))
      Filter.atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add h0
  rw [add_zero] at h1
  have h2 : Filter.Tendsto (fun k : ℕ => 1 / (1 + c / (k : ℝ)))
      Filter.atTop (nhds (1 / 1)) :=
    tendsto_const_nhds.div h1 one_ne_zero
  rw [div_one] at h2
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hsk : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have e : (1 : ℝ) + c / (k : ℝ) = ((k : ℝ) + c) / (k : ℝ) := by
    rw [add_div, div_self hsk]
  rw [e, one_div_div]

/-- Sequential version: `A(e^k) / √k → α` for some `α > 0`. -/
private lemma lr_A_seq_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
        Filter.atTop (nhds α) := by
  obtain ⟨K, hK, k₀, hk₀, hstep⟩ := lr_J_ratio
  obtain ⟨C, hC⟩ := lr_J_near
  have hpos : ∀ k : ℕ, 1 ≤ k → 0 < (fun k => lrJ (Real.exp (k : ℝ))) k :=
    fun k hk => lr_J_exp_pos k hk
  obtain ⟨L, hLpos, hL⟩ := lr_growth _ hpos K hK k₀ hk₀ hstep
  have hrpow : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ^ (3 / 2 : ℝ)
      = (k : ℝ) * Real.sqrt (k : ℝ) := by
    intro k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [e, Real.rpow_add hsk, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hconv : ∀ k : ℕ, 1 ≤ k → |C| < (k : ℝ) →
      (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + C)
        ≤ lrA (Real.exp (k : ℝ)) ∧
      lrA (Real.exp (k : ℝ))
        ≤ (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by
    intro k hk hCk
    have hEk : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
      have h := Real.add_one_le_exp (k : ℝ)
      have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hN6 := hC (Real.exp (k : ℝ)) hEk
    rw [Real.log_exp] at hN6
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have hCab : -(k : ℝ) < C ∧ C < (k : ℝ) := abs_lt.mp hCk
    have hposPC : (0 : ℝ) < (k : ℝ) + C := by linarith [hCab.1]
    have hposMC : (0 : ℝ) < (k : ℝ) - C := by linarith [hCab.2]
    have hSDne : (k : ℝ) + C ≠ 0 := ne_of_gt hposPC
    have hMDne : (k : ℝ) - C ≠ 0 := ne_of_gt hposMC
    have hhi := (abs_le.mp hN6).2
    have hlo := (abs_le.mp hN6).1
    constructor
    · have hle : lrJ (Real.exp (k : ℝ))
          ≤ (2 / 3) * ((k : ℝ) + C) * lrA (Real.exp (k : ℝ)) := by
        linarith [hhi]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + C) :=
        div_nonneg (by norm_num) hposPC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) + C) * lrA (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) + C))
          = lrA (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : lrJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + C))
          = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + C) := by ring
      rw [e0, e1] at h
      exact h
    · have hle : (2 / 3) * ((k : ℝ) - C) * lrA (Real.exp (k : ℝ))
          ≤ lrJ (Real.exp (k : ℝ)) := by
        linarith [hlo]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) - C) :=
        div_nonneg (by norm_num) hposMC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) - C) * lrA (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) - C))
          = lrA (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : lrJ (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) - C))
          = (3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by ring
      rw [e0, e1] at h
      exact h
  have hLo : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) + C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (lr_nat_div_add_tendsto C)
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + C))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    simpa [mul_one] using hmul2
  have hHi : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) - C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (lr_nat_div_add_tendsto (-C))
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    have heq : (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        = (fun k : ℕ => (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) - C)))) := by
      funext k
      have hsub : ((k : ℝ) - C) = ((k : ℝ) + (-C)) := by ring
      rw [hsub]
    rw [heq] at hmul2
    simpa [mul_one] using hmul2
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt (|C| + 1)
  have hk₁R : |C| + 1 < (k₁ : ℝ) := hk₁
  have hk₁pos : 1 ≤ k₁ := by
    have hle : (1 : ℝ) ≤ (k₁ : ℝ) := by
      have hCnn : (0 : ℝ) ≤ |C| := abs_nonneg _
      linarith
    exact_mod_cast hle
  refine ⟨(3 / 2) * L, by linarith [hLpos], ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hHi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop k₁] with k hk
    have hk1 : 1 ≤ k := le_trans hk₁pos hk
    have hCk : |C| < (k : ℝ) := by
      have hle : (k₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hconvk := hconv k hk1 hCk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hsqrt : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hsk
    have hsqne : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt hsqrt
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hsk
    have hPCne : (k : ℝ) + C ≠ 0 := ne_of_gt (by
      have hCab : -(k : ℝ) < C := (abs_lt.mp hCk).1
      linarith)
    have e : ((3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) + C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + C))) := by
      rw [hrpow k hk1]
      field_simp
    rw [← e]
    exact div_le_div_of_nonneg_right hconvk.1 (Real.sqrt_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop k₁] with k hk
    have hk1 : 1 ≤ k := le_trans hk₁pos hk
    have hCk : |C| < (k : ℝ) := by
      have hle : (k₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hconvk := hconv k hk1 hCk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hsqrt : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hsk
    have hsqne : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt hsqrt
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hsk
    have hMCne : (k : ℝ) - C ≠ 0 := ne_of_gt (by
      have hCab : C < (k : ℝ) := (abs_lt.mp hCk).2
      linarith)
    have e : lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)
        ≤ ((3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ) :=
      div_le_div_of_nonneg_right hconvk.2 (Real.sqrt_nonneg _)
    have e2 : ((3 / 2) * lrJ (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((lrJ (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) - C))) := by
      rw [hrpow k hk1]
      field_simp
    rw [e2] at e
    exact e

/-- Shifted end: `A(e^k) / √(k+1) → α`. -/
private lemma lr_A_seq_low (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
  have hratio : Filter.Tendsto
      (fun k : ℕ => Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (((k + 1 : ℕ)) : ℝ))
        Filter.atTop (nhds 1) := by
      have h := lr_nat_div_add_tendsto (1 : ℝ)
      refine h.congr' ?_
      filter_upwards with k
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
    have h2 := (Real.continuous_sqrt.tendsto 1).comp hbase
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards with k
    exact Real.sqrt_div (Nat.cast_nonneg k) _
  have hmul := hAseq.mul hratio
  have heq : (fun k : ℕ => (lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
          * (Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have hsq : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsk)
    have hsq1 : Real.sqrt (((k + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.succ_pos k))
    field_simp
  have h2 := hmul.congr' heq
  simpa [mul_one] using h2

/-- Shifted end: `A(e^{k+1}) / √k → α`. -/
private lemma lr_A_seq_high (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α) := by
  have hshift : Filter.Tendsto
      (fun k : ℕ => lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
        / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
    have hiff := tendsto_add_atTop_iff_nat (l := nhds α)
      (f := fun k : ℕ => lrA (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)) 1
    exact hiff.mpr hAseq
  have hratio : Filter.Tendsto
      (fun k : ℕ => Real.sqrt (((k + 1 : ℕ)) : ℝ) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ)) : ℝ) / (k : ℝ))
        Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ))
          Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 1
      have h1 : Filter.Tendsto (fun k : ℕ => 1 + (1 : ℝ) / (k : ℝ))
          Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add h0
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hsk : (k : ℝ) ≠ 0 := by
        have : k ≠ 0 := by omega
        exact_mod_cast this
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, add_div, div_self hsk]
    have h2 := (Real.continuous_sqrt.tendsto 1).comp hbase
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards with k
    exact Real.sqrt_div (Nat.cast_nonneg _) _
  have hmul := hshift.mul hratio
  have heq : (fun k : ℕ => (lrA (Real.exp (((k + 1 : ℕ)) : ℝ))
          / Real.sqrt (((k + 1 : ℕ)) : ℝ))
          * (Real.sqrt (((k + 1 : ℕ)) : ℝ) / Real.sqrt (k : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => lrA (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ)) := by
    filter_upwards with k
    have hS : Real.sqrt (((k + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.succ_pos k))
    field_simp
  have h2 := hmul.congr' heq
  simpa [mul_one] using h2

/-- `A(x) / √(log x)` converges to a positive limit. -/
private lemma lr_A_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun x => lrA x / Real.sqrt (Real.log x))
        Filter.atTop (nhds α) := by
  obtain ⟨α, hαpos, hAseq⟩ := lr_A_seq_tendsto
  have hlow := lr_A_seq_low α hAseq
  have hhigh := lr_A_seq_high α hAseq
  have hk_tend : Filter.Tendsto (fun x : ℝ => ⌊Real.log x⌋₊)
      Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_log_atTop
  have hlowx : Filter.Tendsto
      (fun x : ℝ => lrA (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
        Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := hlow.comp hk_tend
  have hhighx : Filter.Tendsto
      (fun x : ℝ => lrA (Real.exp (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)) /
        Real.sqrt ((⌊Real.log x⌋₊ : ℕ) : ℝ))
      Filter.atTop (nhds α) := hhigh.comp hk_tend
  refine ⟨α, hαpos, ?_⟩
  have key_lo : ∀ᶠ x : ℝ in Filter.atTop,
      lrA (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)
        ≤ lrA x / Real.sqrt (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at h
    have hlognn : (0 : ℝ) ≤ Real.log x := by linarith
    have hkd : ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Nat.floor_le hlognn
    have hku : Real.log x < ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hexpk : Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ x := by
      have h := Real.exp_le_exp.mpr hkd
      rwa [Real.exp_log hxpos] at h
    have hcast1 : ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        = ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    have hAle1 : lrA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) ≤ lrA x :=
      lrA_mono hexpk
    have hsq2 : Real.sqrt (Real.log x)
        ≤ Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ) := by
      rw [hcast1]
      exact Real.sqrt_le_sqrt hku.le
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc lrA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) /
            Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        ≤ lrA (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_left (lrA_nonneg _) hsqrt_log hsq2
      _ ≤ lrA x / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle1 hsqrt_log.le
  have key_hi : ∀ᶠ x : ℝ in Filter.atTop,
      lrA x / Real.sqrt (Real.log x)
        ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at h
    have hlognn : (0 : ℝ) ≤ Real.log x := by linarith
    have hk1 : 1 ≤ ⌊Real.log x⌋₊ := (Nat.one_le_floor_iff _).mpr hlog1
    have hkd : ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Nat.floor_le hlognn
    have hku : Real.log x < ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hsk : (0 : ℝ) < ((⌊Real.log x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hcast1 : ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        = ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    have hxexp : x < Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ) := by
      have h := Real.exp_lt_exp.mpr hku
      rw [Real.exp_log hxpos, ← hcast1] at h
      exact h
    have hAle2 : lrA x ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) :=
      lrA_mono hxexp.le
    have hsq1 : Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ)
        ≤ Real.sqrt (Real.log x) :=
      Real.sqrt_le_sqrt hkd
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc lrA x / Real.sqrt (Real.log x)
        ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle2 hsqrt_log.le
      _ ≤ lrA (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_left (lrA_nonneg _)
            (Real.sqrt_pos.mpr hsk) hsq1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowx hhighx key_lo key_hi

/-- `A(x)` tends to infinity. -/
private lemma lr_A_atTop (α : ℝ) (hα : 0 < α)
    (hA : Filter.Tendsto (fun x => lrA x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto lrA Filter.atTop Filter.atTop := by
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x))
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun y : ℝ => y ^ (1/2 : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    have h2 := h1.comp Real.tendsto_log_atTop
    refine h2.congr' ?_
    filter_upwards with x
    exact (Real.sqrt_eq_rpow _).symm
  have hAev : ∀ᶠ x : ℝ in Filter.atTop, α / 2 ≤ lrA x / Real.sqrt (Real.log x) := by
    have hmem : Set.Ioi (α / 2) ∈ nhds α := Ioi_mem_nhds (by linarith)
    filter_upwards [hA.eventually hmem] with x hx
    exact le_of_lt (Set.mem_Ioi.mp hx)
  have hlogev : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.sqrt (Real.log x) * (α / 2) ≤ lrA x := by
    filter_upwards [hAev, hlogev] with x hx1 hx2
    have hpos : (0:ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    have h := (le_div_iff₀ hpos).mp hx1
    linarith [h]
  exact Filter.tendsto_atTop_mono' _ hev
    (hsqrt.atTop_mul_const (by linarith))

/-- The log-weighted sum over the natural density:
`(Σ_{n ≤ x} lrH n · log n) / (x · A(x)) → 1 / 2`. -/
private lemma lr_L_tendsto :
    Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n : ℝ))
        / (x * lrA x))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  obtain ⟨α, hαpos, hA⟩ := lr_A_tendsto
  have hAinf := lr_A_atTop α hαpos hA
  have hKpos : (0:ℝ) < Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK1 : (1/2 : ℝ) ≤ Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK : ∀ y : ℝ, 0 ≤ y → |lrPsi y - y / 2| ≤ (Real.log 4 + 4) * y := by
    intro y hy
    have h1 : 0 ≤ lrPsi y := lrPsi_nonneg y
    have h2 : lrPsi y ≤ (Real.log 4 + 4) * y := lrPsi_le_mul_self hy
    have h3 : (0:ℝ) ≤ y / 2 := by linarith
    have h4 : y / 2 ≤ (Real.log 4 + 4) * y := by
      have hnn := mul_nonneg (sub_nonneg.mpr hK1) hy
      linarith
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevY : ∀ᶠ y : ℝ in Filter.atTop, dist (lrPsi y / y) (1/2) ≤ ε/4 :=
    lr_psi_tendsto.eventually
      (Metric.closedBall_mem_nhds (1/2 : ℝ) (show (0:ℝ) < ε/4 by linarith))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hevY
  set Y : ℝ := max Y₀ 1 with hYdef
  have hY1 : (1:ℝ) ≤ Y := le_max_right _ _
  have hYpos : (0:ℝ) < Y := by linarith
  have hYrel : ∀ y : ℝ, Y ≤ y → |lrPsi y - y/2| ≤ (ε/4) * y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hYpos hy
    have h := hY₀ y (le_trans (le_max_left _ _) hy)
    rw [Real.dist_eq] at h
    have hyne : y ≠ 0 := ne_of_gt hy0
    have e : lrPsi y - y/2 = y * (lrPsi y / y - 1/2) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg hy0.le]
    calc y * |lrPsi y / y - 1 / 2| ≤ y * (ε/4) :=
        mul_le_mul_of_nonneg_left h hy0.le
      _ = (ε/4) * y := by ring
  have hBpos : (0:ℝ) < 4 * ((Real.log 4 + 4) * Y) / ε :=
    div_pos (mul_pos (by norm_num) (mul_pos hKpos hYpos)) hε
  have hB : ∀ᶠ x : ℝ in Filter.atTop, 4 * ((Real.log 4 + 4) * Y) / ε ≤ lrA x :=
    hAinf.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [Filter.eventually_ge_atTop 1, hB] with x hx1 hBA
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hApos : (0:ℝ) < lrA x := lt_of_lt_of_le hBpos hBA
  have hxA : (0:ℝ) < x * lrA x := mul_pos hxpos hApos
  have hhalf : x / 2 * lrA x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * (x / (2 * (m:ℝ))) := by
    have hlrA : lrA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m / (m:ℝ) := rfl
    rw [hlrA, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) - x/2 * lrA x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ))) := by
    rw [lr_L_eq, hhalf, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hbig : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, Y ≤ x/(m:ℝ) →
      |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (ε/4) * (x * (lrH m/(m:ℝ))) := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have h1 := hYrel _ hYm
    have hnn : (0:ℝ) ≤ lrH m := lrH_nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [abs_mul, abs_of_nonneg hnn]
    calc lrH m * |lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ))|
        = lrH m * |lrPsi (x/(m:ℝ)) - (x/(m:ℝ))/2| := by rw [e]
      _ ≤ lrH m * ((ε/4) * (x/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ = (ε/4) * (x * (lrH m/(m:ℝ))) := by ring
  have hsmall : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, ¬ Y ≤ x/(m:ℝ) →
      |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (Real.log 4 + 4) * Y := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have hlt : x/(m:ℝ) < Y := lt_of_not_ge hYm
    have hxm0 : (0:ℝ) ≤ x/(m:ℝ) := div_nonneg hx0 hmpos.le
    have h1 := hK _ hxm0
    have hle1 : lrH m ≤ 1 := lrH_le_one m
    have hnn : (0:ℝ) ≤ lrH m := lrH_nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [← e] at h1
    calc |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        = lrH m * |lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ))| := by
          rw [abs_mul, abs_of_nonneg hnn]
      _ ≤ 1 * ((Real.log 4 + 4) * (x/(m:ℝ))) :=
          mul_le_mul hle1 h1 (abs_nonneg _) (by norm_num)
      _ = (Real.log 4 + 4) * (x/(m:ℝ)) := one_mul _
      _ ≤ (Real.log 4 + 4) * Y :=
          mul_le_mul_of_nonneg_left hlt.le hKpos.le
  have hbig_sum : ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
        |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (lrH m/(m:ℝ))) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hbig m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun m _ _ => mul_nonneg (show (0:ℝ) ≤ ε/4 by linarith)
          (mul_nonneg hx0
            (div_nonneg (lrH_nonneg m) (Nat.cast_nonneg m)))))
  have hcardx : (((Finset.Ioc 0 ⌊x⌋₊).filter
      (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ))).card : ℝ) ≤ x := by
    calc (((Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ))).card : ℝ)
        ≤ (((Finset.Ioc 0 ⌊x⌋₊).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_filter_le _ _
      _ = (⌊x⌋₊ : ℝ) := by rw [Nat.card_Ioc, Nat.sub_zero]
      _ ≤ x := Nat.floor_le hx0
  have hsmall_sum : ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ)),
        |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ x * ((Real.log 4 + 4) * Y) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hsmall m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (le_trans
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
        (mul_le_mul_of_nonneg_right hcardx
          (mul_nonneg hKpos.le hYpos.le)))
  have hsum_le : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) - x/2 * lrA x|
      ≤ (ε/4) * (x * lrA x) + x * ((Real.log 4 + 4) * Y) := by
    rw [hdiff]
    calc |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
            |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
              |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|)
          + (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ)),
              |lrH m * (lrPsi (x/(m:ℝ)) - x/(2*(m:ℝ)))|) :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (lrH m/(m:ℝ))))
          + x * ((Real.log 4 + 4) * Y) :=
          _root_.add_le_add hbig_sum hsmall_sum
      _ = (ε/4) * (x * lrA x) + x * ((Real.log 4 + 4) * Y) := by
          congr 1
          calc ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (lrH m/(m:ℝ)))
              = (ε/4) * x * ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (lrH m/(m:ℝ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro m _
                ring
            _ = (ε/4) * (x * lrA x) := by
                have hlrA : lrA x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, lrH m/(m:ℝ) := rfl
                rw [hlrA]
                ring
  have e : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x) - 1/2
      = ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) - x/2 * lrA x)
        / (x * lrA x) := by
    have hxAne : x * lrA x ≠ 0 := ne_of_gt hxA
    field_simp
  have hBY : (Real.log 4 + 4) * Y / lrA x ≤ ε/4 := by
    rw [div_le_iff₀ hApos]
    have h2 : 4 * ((Real.log 4 + 4) * Y) ≤ lrA x * ε := by
      rwa [div_le_iff₀ hε] at hBA
    linarith [h2]
  have hfin : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x)
      - 1/2| ≤ ε/2 := by
    rw [e, abs_div, abs_of_nonneg hxA.le, div_le_iff₀ hxA]
    have h1 : x * ((Real.log 4 + 4) * Y) ≤ (ε/4) * (x * lrA x) := by
      have e2 : x * ((Real.log 4 + 4) * Y)
          = (x * lrA x) * ((Real.log 4 + 4) * Y / lrA x) := by
        have hAne : lrA x ≠ 0 := ne_of_gt hApos
        field_simp
      rw [e2]
      calc (x * lrA x) * ((Real.log 4 + 4) * Y / lrA x)
          ≤ (x * lrA x) * (ε/4) :=
            mul_le_mul_of_nonneg_left hBY hxA.le
        _ = (ε/4) * (x * lrA x) := by ring
    linarith [hsum_le, h1]
  change dist ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x))
    (1/2 : ℝ) < ε
  rw [Real.dist_eq]
  linarith [hfin, hε]

/-- For `x ≥ 1`: `∑_{n ≤ x} log (x / n) ≤ x`, via `N!`. -/
private lemma lr_log_sum_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log (x / (n:ℝ)) ≤ x := by
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hNpos : (0:ℝ) < (N:ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hNnn : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hlogne : ∀ i ∈ Finset.Ico 1 (N+1), ((i : ℕ):ℝ) ≠ 0 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hi1)
  have hlogfact : ∑ n ∈ Finset.Ico 1 (N+1), Real.log ((n:ℕ):ℝ)
      = Real.log (((Nat.factorial N : ℕ)):ℝ) := by
    have hprod : (∏ i ∈ Finset.Ico 1 (N+1), ((i:ℕ):ℝ)) = (((Nat.factorial N : ℕ)):ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Finset.prod_Ico_id_eq_factorial N
    rw [← hprod]
    exact (Real.log_prod hlogne).symm
  have hS : ∑ n ∈ Finset.Ioc 0 N, Real.log (x/(n:ℝ))
      = (N:ℝ) * Real.log x - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
    rw [hIoc]
    calc ∑ n ∈ Finset.Ico 1 (N+1), Real.log (x/((n:ℕ):ℝ))
        = ∑ n ∈ Finset.Ico 1 (N+1),
            (Real.log x - Real.log ((n:ℕ):ℝ)) :=
          Finset.sum_congr rfl (fun i hi =>
            Real.log_div (ne_of_gt hxpos) (hlogne i hi))
      _ = (Finset.Ico 1 (N+1)).card • Real.log x
          - ∑ n ∈ Finset.Ico 1 (N+1), Real.log ((n:ℕ):ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const]
      _ = (N:ℝ) * Real.log x - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
          have hcard : (Finset.Ico 1 (N+1)).card = N := by simp [Nat.card_Ico]
          rw [hlogfact, hcard, nsmul_eq_mul]
  have hfact : (N:ℝ) * Real.log (N:ℝ) - Real.log (((Nat.factorial N : ℕ)):ℝ) ≤ (N:ℝ) := by
    have hexp : HasSum (fun n : ℕ => (N:ℝ)^n / (((Nat.factorial n : ℕ)):ℝ))
        (Real.exp (N:ℝ)) := by
      have h : HasSum (fun n : ℕ => (N:ℝ)^n / (((Nat.factorial n : ℕ)):ℝ))
          (NormedSpace.exp (N:ℝ)) :=
        NormedSpace.expSeries_div_hasSum_exp _
      rwa [← Real.exp_eq_exp_ℝ] at h
    have hfact_le : (N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ) ≤ Real.exp (N:ℝ) := by
      have hle := hexp.summable.sum_le_tsum {N} (fun i _ =>
        div_nonneg (pow_nonneg hNnn _) (Nat.cast_nonneg _))
      rw [Finset.sum_singleton, hexp.tsum_eq] at hle
      exact hle
    have hpos1 : (0:ℝ) < (N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ) :=
      div_pos (pow_pos hNpos _)
        (Nat.cast_pos.mpr (Nat.factorial_pos _))
    have h2 := Real.log_le_log hpos1 hfact_le
    rw [Real.log_exp] at h2
    have e : Real.log ((N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ))
        = (N:ℝ) * Real.log (N:ℝ) - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
      rw [Real.log_div (ne_of_gt (pow_pos hNpos _))
        (ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))), Real.log_pow]
    rwa [e] at h2
  have hxd : (N:ℝ) * Real.log (x/(N:ℝ)) ≤ x - (N:ℝ) := by
    have h1 : Real.log (x/(N:ℝ)) ≤ x/(N:ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hxpos hNpos)
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    have h2 := mul_le_mul_of_nonneg_left h1 hNnn
    have e : (N:ℝ) * (x/(N:ℝ) - 1) = x - (N:ℝ) := by
      rw [mul_sub, mul_one]
      congr 1
      rw [mul_comm]
      exact div_mul_cancel₀ _ hNne
    rwa [e] at h2
  have hsplit : (N:ℝ) * Real.log x
      = (N:ℝ) * Real.log (x/(N:ℝ)) + (N:ℝ) * Real.log (N:ℝ) := by
    have e : Real.log (x/(N:ℝ)) = Real.log x - Real.log (N:ℝ) :=
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hNpos)
    rw [e]
    ring
  linarith [hS, hfact, hxd, hsplit]

/-- Natural density: `H(x) · √(log x) / x → α / 2`. -/
private lemma lr_count_tendsto (α : ℝ)
    (hA : Filter.Tendsto (fun x => lrA x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2)) := by
  obtain ⟨α', hα'pos, hA'⟩ := lr_A_tendsto
  have hAinf := lr_A_atTop α' hα'pos hA'
  -- The `J₂` sum and its bounds.
  have hJ2eq : ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
      = lrCount x * Real.log x
        - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) := by
    intro x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hlrC : lrCount x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n := rfl
    rw [hlrC, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
    ring
  have hJ2nn : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
        / (x * lrA x) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < lrA x :=
      lt_of_lt_of_le (by norm_num) (lrA_ge_one hx)
    apply div_nonneg _ (mul_nonneg hxpos.le hApos.le)
    apply Finset.sum_nonneg
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    have hnx : (n:ℝ) ≤ x := by
      have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hn).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
    have hlog : 0 ≤ Real.log (x/(n:ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hnpos]
      simpa using hnx
    exact mul_nonneg (lrH_nonneg n) hlog
  have hJ2le : ∀ᶠ x : ℝ in Filter.atTop,
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
        / (x * lrA x) ≤ 1 / lrA x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < lrA x :=
      lt_of_lt_of_le (by norm_num) (lrA_ge_one hx)
    have hxA : (0:ℝ) < x * lrA x := mul_pos hxpos hApos
    have hJle : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ))) ≤ x := by
      calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ))
          ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log (x/(n:ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
            have hnpos : (0:ℝ) < (n:ℝ) := by
              exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
            have hnx : (n:ℝ) ≤ x := by
              have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hn).2
              exact le_trans (by exact_mod_cast h1)
                (Nat.floor_le (by linarith))
            have hlog : 0 ≤ Real.log (x/(n:ℝ)) := by
              apply Real.log_nonneg
              rw [le_div_iff₀ hnpos]
              simpa using hnx
            calc lrH n * Real.log (x/(n:ℝ))
                ≤ 1 * Real.log (x/(n:ℝ)) :=
                  mul_le_mul_of_nonneg_right (lrH_le_one n) hlog
              _ = Real.log (x/(n:ℝ)) := one_mul _
        _ ≤ x := lr_log_sum_le hx
    calc (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ))) / (x * lrA x)
        ≤ x / (x * lrA x) :=
          div_le_div_of_nonneg_right hJle hxA.le
      _ = 1 / lrA x := by
          have hxne : x ≠ 0 := ne_of_gt hxpos
          have hAne : lrA x ≠ 0 := ne_of_gt hApos
          field_simp
  have h1A : Filter.Tendsto (fun x => 1 / lrA x) Filter.atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hAinf
    refine h.congr' ?_
    filter_upwards with x
    exact (one_div _).symm
  have hJ2 : Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
        / (x * lrA x))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1A
      hJ2nn hJ2le
  have hHlog : Filter.Tendsto
      (fun x => lrCount x * Real.log x / (x * lrA x))
      Filter.atTop (nhds (1 / 2)) := by
    have heq : (fun x => lrCount x * Real.log x / (x * lrA x)) =ᶠ[Filter.atTop]
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
          / (x * lrA x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      rw [hJ2eq x hx]
      ring
    have hsum := hJ2.add lr_L_tendsto
    rw [show (0:ℝ) + 1/2 = 1/2 by ring] at hsum
    have hsum' : Filter.Tendsto
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (x/(n:ℝ)))
          / (x * lrA x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, lrH n * Real.log (n:ℝ)) / (x * lrA x))
        Filter.atTop (nhds (1/2)) := hsum
    exact hsum'.congr' heq.symm
  have heq2 : (fun x => (lrCount x * Real.log x / (x * lrA x))
        * (lrA x / Real.sqrt (Real.log x)))
      =ᶠ[Filter.atTop]
      (fun x => lrCount x * Real.sqrt (Real.log x) / x) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsq : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlog)
    have hApos : (0:ℝ) < lrA x :=
      lt_of_lt_of_le (by norm_num) (lrA_ge_one (le_of_lt hx))
    have hxne : x ≠ 0 := ne_of_gt (by linarith)
    have hAne : lrA x ≠ 0 := ne_of_gt hApos
    have hdiv : Real.log x / Real.sqrt (Real.log x)
        = Real.sqrt (Real.log x) := by
      rw [div_eq_iff hsq, Real.mul_self_sqrt hlog.le]
    calc (lrCount x * Real.log x / (x * lrA x))
            * (lrA x / Real.sqrt (Real.log x))
        = (lrCount x / x) * (Real.log x / Real.sqrt (Real.log x)) := by
          field_simp
      _ = (lrCount x / x) * Real.sqrt (Real.log x) := by rw [hdiv]
      _ = lrCount x * Real.sqrt (Real.log x) / x := by ring
  have hprod := hHlog.mul hA
  have eα : (1/2 : ℝ) * α = α / 2 := by ring
  rw [eα] at hprod
  have hprod' : Filter.Tendsto
      (fun x => (lrCount x * Real.log x / (x * lrA x))
        * (lrA x / Real.sqrt (Real.log x)))
      Filter.atTop (nhds (α/2)) := hprod
  exact hprod'.congr' heq2

/-- `lrCount` vanishes below `1`. -/
private lemma lrCount_eq_zero_of_lt_one {y : ℝ} (hy : y < 1) : lrCount y = 0 := by
  have hfl : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr hy
  simp [lrCount, hfl]

/-- The square-root log ratio `√(log x) / √(log (x / c))` tends to `1`. -/
private lemma lr_sqrt_ratio_tendsto (c : ℝ) (hc : 1 ≤ c) :
    Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c)))
      Filter.atTop (nhds 1) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hx : Filter.Tendsto (fun x : ℝ => x / c) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hc0 tendsto_id
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log c / Real.log x)
      Filter.atTop (nhds 0) := by
    have hloginv : Filter.Tendsto (fun x : ℝ => (Real.log x)⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have h := Filter.Tendsto.const_mul (Real.log c) hloginv
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with x
    rw [div_eq_mul_inv]
  have hratio : Filter.Tendsto (fun x : ℝ => Real.log (x / c) / Real.log x)
      Filter.atTop (nhds 1) := by
    have heq : (fun x : ℝ => Real.log (x / c) / Real.log x) =ᶠ[Filter.atTop]
        (fun x : ℝ => 1 - Real.log c / Real.log x) := by
      filter_upwards [Filter.eventually_gt_atTop 1] with x hx1
      have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx1
      have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hc0),
        sub_div, div_self hlogx]
    have h1 : Filter.Tendsto (fun x : ℝ => 1 - Real.log c / Real.log x)
        Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h1
    exact h1.congr' heq.symm
  have hsqrt : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (Real.log (x / c) / Real.log x))
      Filter.atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hratio
    rw [Real.sqrt_one] at h
    exact h
  have hinv : Filter.Tendsto
      (fun x : ℝ => (Real.sqrt (Real.log (x / c) / Real.log x))⁻¹)
      Filter.atTop (nhds 1) := by
    have h := Filter.Tendsto.inv₀ hsqrt one_ne_zero
    rwa [inv_one] at h
  refine hinv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 1 c)] with x hxc
  have hx1 : (1 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hxc
  have hxc' : c < x := lt_of_le_of_lt (le_max_right _ _) hxc
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hy1 : (1 : ℝ) < x / c := by
    rw [lt_div_iff₀ hc0]
    linarith
  have hlogy : (0 : ℝ) < Real.log (x / c) := Real.log_pos hy1
  rw [Real.sqrt_div hlogy.le, inv_div]

/-- Pointwise limit of the `k`-th summand in the `B`-sum. -/
private lemma lr_f_tendsto (k : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (hH : Filter.Tendsto
      (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    Filter.Tendsto
      (fun x => lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (lrG k * (α / 2) / (k : ℝ) ^ 2)) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  set c : ℝ := (k : ℝ) ^ 2 with hc
  have hcc : (0 : ℝ) < c := pow_pos hkpos 2
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hkR 2
  have h1 : Filter.Tendsto
      (fun x : ℝ => lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c))
      Filter.atTop (nhds (α / 2)) :=
    hH.comp (Filter.Tendsto.atTop_div_const hcc tendsto_id)
  have h2 := lr_sqrt_ratio_tendsto c hc1
  have hmul : Filter.Tendsto
      (fun x : ℝ => (lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c)) *
        (Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c))))
      Filter.atTop (nhds ((α / 2) * 1)) :=
    h1.mul h2
  rw [mul_one] at hmul
  have hscale : Filter.Tendsto
      (fun x : ℝ => (lrG k / c) *
        ((lrCount (x / c) * Real.sqrt (Real.log (x / c)) / (x / c)) *
        (Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / c)))))
      Filter.atTop (nhds ((lrG k / c) * (α / 2))) :=
    Filter.Tendsto.const_mul _ hmul
  have e : (lrG k / c) * (α / 2) = lrG k * (α / 2) / c := by ring
  rw [e] at hscale
  refine hscale.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (max 1 c)] with x hxc
  have hx1 : (1 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hxc
  have hxc' : c < x := lt_of_le_of_lt (le_max_right _ _) hxc
  have hxpos : (0 : ℝ) < x := by linarith
  have hypos : (0 : ℝ) < x / c := div_pos hxpos hcc
  have hy1 : (1 : ℝ) < x / c := by
    rw [lt_div_iff₀ hcc]
    linarith
  have hlogy : (0 : ℝ) < Real.log (x / c) := Real.log_pos hy1
  have hs2 : Real.sqrt (Real.log (x / c)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hlogy)
  have hyc : (x / c) ≠ 0 := ne_of_gt hypos
  have hxc0 : x ≠ 0 := ne_of_gt hxpos
  have hc0n : c ≠ 0 := ne_of_gt hcc
  field_simp

/-- Uniform bound for `lrCount y · √(log y) / y` over `y ≥ 2`. -/
private lemma lr_count_uniform_bound (α : ℝ) (hα : 0 < α)
    (hH : Filter.Tendsto
      (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    ∃ D : ℝ, 0 < D ∧
      ∀ y : ℝ, 2 ≤ y → lrCount y * Real.sqrt (Real.log y) / y ≤ D := by
  have h1 : ∀ᶠ y : ℝ in Filter.atTop,
      lrCount y * Real.sqrt (Real.log y) / y < α / 2 + 1 :=
    hH.eventually (Iio_mem_nhds (by linarith))
  rw [Filter.eventually_atTop] at h1
  obtain ⟨Y₁, hY₁⟩ := h1
  set Y₀ : ℝ := max Y₁ 2 with hY₀
  have hY₀ge : (2 : ℝ) ≤ Y₀ := le_max_right _ _
  refine ⟨max (α / 2 + 1) (Real.sqrt (Real.log Y₀)),
    lt_max_of_lt_left (show (0 : ℝ) < α / 2 + 1 by linarith),
    fun y hy => ?_⟩
  rcases le_total y Y₀ with hle | hle
  · have hypos : (0 : ℝ) < y := by linarith
    have hYpos : (0 : ℝ) < Y₀ := by linarith
    have hlog_le : Real.log y ≤ Real.log Y₀ :=
      Real.log_le_log hypos hle
    have hsq_le : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log Y₀) :=
      Real.sqrt_le_sqrt hlog_le
    have h1 : lrCount y * Real.sqrt (Real.log y)
        ≤ Real.sqrt (Real.log Y₀) * y := by
      calc lrCount y * Real.sqrt (Real.log y)
          ≤ y * Real.sqrt (Real.log y) :=
            mul_le_mul_of_nonneg_right (lrCount_le hypos.le)
              (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (Real.log Y₀) * y := by
            calc y * Real.sqrt (Real.log y)
                ≤ y * Real.sqrt (Real.log Y₀) :=
                  mul_le_mul_of_nonneg_left hsq_le hypos.le
              _ = Real.sqrt (Real.log Y₀) * y := mul_comm _ _
    have h2 : lrCount y * Real.sqrt (Real.log y) / y
        ≤ Real.sqrt (Real.log Y₀) := by
      rw [div_le_iff₀ hypos]
      linarith [h1]
    exact le_trans h2 (le_max_right _ _)
  · have hY₁le : Y₁ ≤ y := le_trans (le_max_left _ _) hle
    have hlt := hY₁ y hY₁le
    have hle2 : lrCount y * Real.sqrt (Real.log y) / y ≤ α / 2 + 1 := le_of_lt hlt
    exact le_trans hle2 (le_max_left _ _)

/-- Dominating bound for the `k`-th summand in the `B`-sum. -/
private noncomputable def lrBnd (D : ℝ) (k : ℕ) : ℝ :=
  (Real.sqrt 2 * D + 2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2

/-- The dominating bound is summable. -/
private lemma lr_bnd_summable (D : ℝ) : Summable (lrBnd D) := by
  have h1 : Summable (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2) := by
    have hs : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have he : (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2)
        = (fun k : ℕ => (Real.sqrt 2 * D) * ((1 : ℝ) / (k : ℝ) ^ 2)) := by
      funext k
      ring
    rw [he]
    exact hs.mul_left _
  have h2 : Summable
      (fun k : ℕ => (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) := by
    have hs : Summable
        (fun k : ℕ => (2 : ℝ) * (((k : ℝ) ^ ((3 / 2 : ℝ)))⁻¹)) :=
      ((Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).mpr
        (by norm_num)).mul_left 2
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hs
    · apply div_nonneg _ (sq_nonneg _)
      apply mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    · by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hkpos : (0 : ℝ) < (k : ℝ) :=
          by exact_mod_cast Nat.pos_of_ne_zero hk0
        have hK : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
        have hR : (0 : ℝ) < (k : ℝ) ^ ((3 / 2 : ℝ)) :=
          Real.rpow_pos_of_pos hkpos _
        have hsqrt_le : Real.sqrt (Real.log k) ≤ Real.sqrt (k : ℝ) :=
          Real.sqrt_le_sqrt (Real.log_le_self hkpos.le)
        have hkey : Real.sqrt (Real.log k) * (k : ℝ) ^ ((3 / 2 : ℝ))
            ≤ (k : ℝ) ^ 2 := by
          have hle := mul_le_mul_of_nonneg_right hsqrt_le hR.le
          have eR : Real.sqrt (k : ℝ) * (k : ℝ) ^ ((3 / 2 : ℝ))
              = (k : ℝ) ^ 2 := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add hkpos]
            norm_num [Real.rpow_two]
          rwa [eR] at hle
        have eR2 : (2 : ℝ) * (((k : ℝ) ^ ((3 / 2 : ℝ)))⁻¹)
            = 2 / (k : ℝ) ^ ((3 / 2 : ℝ)) :=
          (div_eq_mul_inv _ _).symm
        rw [eR2, div_le_div_iff₀ hK hR]
        have h2x := mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 2 by norm_num)
        linarith [h2x]
  have hsum : Summable (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2 +
      (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) := h1.add h2
  have heq : (fun k : ℕ => (Real.sqrt 2 * D) / (k : ℝ) ^ 2 +
      (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2) = lrBnd D := by
    funext k
    unfold lrBnd
    rw [add_div]
  rw [← heq]
  exact hsum

/-- Domination of the `B`-summands by the summable bound. -/
private lemma lr_B_dominated (D : ℝ)
    (hDb : ∀ y : ℝ, 2 ≤ y → lrCount y * Real.sqrt (Real.log y) / y ≤ D) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ k : ℕ,
      ‖lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x‖
        ≤ lrBnd D k := by
  have hDnn : (0 : ℝ) ≤ D := by
    have h2 := hDb 2 le_rfl
    have hnn : (0 : ℝ) ≤ lrCount 2 * Real.sqrt (Real.log 2) / 2 := by
      apply div_nonneg _ (by norm_num)
      exact mul_nonneg (lrCount_nonneg _) (Real.sqrt_nonneg _)
    linarith
  filter_upwards [Filter.eventually_ge_atTop 16] with x hx
  intro k
  rcases eq_or_ne k 0 with rfl | hk0
  · have hb0 : lrBnd D 0 = 0 := by
      unfold lrBnd
      norm_num
    rw [lrG_zero, hb0]
    simp
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hc0 : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
    have hxpos : (0 : ℝ) < x := by linarith
    have hnn : (0 : ℝ)
        ≤ lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x := by
      apply div_nonneg _ hxpos.le
      apply mul_nonneg _ (Real.sqrt_nonneg _)
      exact mul_nonneg (lrG_nonneg k) (lrCount_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hlogk_nn : (0 : ℝ) ≤ Real.log k := Real.log_nonneg hkR
    have hb_extra : (0 : ℝ) ≤ 2 * Real.sqrt (Real.log k) :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hb_main : (0 : ℝ) ≤ Real.sqrt 2 * D :=
      mul_nonneg (Real.sqrt_nonneg _) hDnn
    by_cases hcase : (k : ℝ) ^ 2 ≤ Real.sqrt x
    · have hsqrt4 : (4 : ℝ) ≤ Real.sqrt x := by
        have h16 : Real.sqrt 16 ≤ Real.sqrt x :=
          Real.sqrt_le_sqrt (by linarith)
        have e16 : Real.sqrt (16 : ℝ) = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rwa [e16] at h16
      have hsqrtx_nn : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
      have hy_ge : Real.sqrt x ≤ x / (k : ℝ) ^ 2 := by
        rw [le_div_iff₀ hc0]
        calc Real.sqrt x * (k : ℝ) ^ 2
            ≤ Real.sqrt x * Real.sqrt x :=
              mul_le_mul_of_nonneg_left hcase hsqrtx_nn
          _ = x := Real.mul_self_sqrt (by linarith)
      have hy2 : (2 : ℝ) ≤ x / (k : ℝ) ^ 2 := by linarith
      have hypos : (0 : ℝ) < x / (k : ℝ) ^ 2 := by linarith
      have hD := hDb _ hy2
      have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have hlogc : Real.log ((k : ℝ) ^ 2) ≤ (1 / 2) * Real.log x := by
        have h1 : Real.log ((k : ℝ) ^ 2) ≤ Real.log (Real.sqrt x) :=
          Real.log_le_log (pow_pos hkpos 2) hcase
        have h2 : Real.log (Real.sqrt x) = (1 / 2) * Real.log x := by
          rw [Real.log_sqrt (by linarith)]
          ring
        linarith
      have hlogy : Real.log (x / (k : ℝ) ^ 2)
          = Real.log x - Real.log ((k : ℝ) ^ 2) :=
        Real.log_div (ne_of_gt hxpos) (ne_of_gt hc0)
      have hlogy_ge : (1 / 2) * Real.log x ≤ Real.log (x / (k : ℝ) ^ 2) := by
        linarith
      have hlogy_pos : (0 : ℝ) < Real.log (x / (k : ℝ) ^ 2) := by linarith
      have hratio : Real.sqrt (Real.log x)
          / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) ≤ Real.sqrt 2 := by
        have h1 : Real.log x / Real.log (x / (k : ℝ) ^ 2) ≤ 2 := by
          rw [div_le_iff₀ hlogy_pos]
          linarith
        calc Real.sqrt (Real.log x) / Real.sqrt (Real.log (x / (k : ℝ) ^ 2))
            = Real.sqrt (Real.log x / Real.log (x / (k : ℝ) ^ 2)) := by
              rw [Real.sqrt_div hlogx_pos.le]
          _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
      have hHle : lrCount (x / (k : ℝ) ^ 2)
          ≤ D * (x / (k : ℝ) ^ 2)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) := by
        have hspos : (0 : ℝ) < Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) :=
          Real.sqrt_pos.mpr hlogy_pos
        have hD' : lrCount (x / (k : ℝ) ^ 2)
              * Real.sqrt (Real.log (x / (k : ℝ) ^ 2))
            ≤ D * (x / (k : ℝ) ^ 2) :=
          (div_le_iff₀ hypos).mp hD
        rw [le_div_iff₀ hspos]
        exact hD'
      have g1 : lrG k * lrCount (x / (k : ℝ) ^ 2)
          ≤ D * (x / (k : ℝ) ^ 2)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) := by
        calc lrG k * lrCount (x / (k : ℝ) ^ 2)
            ≤ 1 * lrCount (x / (k : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right (lrG_le_one k) (lrCount_nonneg _)
          _ = lrCount (x / (k : ℝ) ^ 2) := one_mul _
          _ ≤ _ := hHle
      have hspos : (0 : ℝ) < Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) :=
        Real.sqrt_pos.mpr hlogy_pos
      have hxc0 : x ≠ 0 := ne_of_gt hxpos
      have hc0n : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hc0
      have hs2n : Real.sqrt (Real.log (x / (k : ℝ) ^ 2)) ≠ 0 := ne_of_gt hspos
      calc lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x
          ≤ (D * (x / (k : ℝ) ^ 2)
              / Real.sqrt (Real.log (x / (k : ℝ) ^ 2)))
              * Real.sqrt (Real.log x) / x := by
              apply div_le_div_of_nonneg_right _ hxpos.le
              exact mul_le_mul_of_nonneg_right g1 (Real.sqrt_nonneg _)
        _ = D * (Real.sqrt (Real.log x)
            / Real.sqrt (Real.log (x / (k : ℝ) ^ 2))) / (k : ℝ) ^ 2 := by
              field_simp
        _ ≤ D * Real.sqrt 2 / (k : ℝ) ^ 2 := by
              apply div_le_div_of_nonneg_right _ hc0.le
              exact mul_le_mul_of_nonneg_left hratio hDnn
        _ ≤ lrBnd D k := by
              unfold lrBnd
              apply div_le_div_of_nonneg_right _ hc0.le
              linarith [mul_comm D (Real.sqrt 2)]
    · have hlt : Real.sqrt x < (k : ℝ) ^ 2 := lt_of_not_ge hcase
      have hlogx_pos : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
      have hlog_lt : Real.log x < 4 * Real.log k := by
        have h1 : Real.log (Real.sqrt x) < Real.log ((k : ℝ) ^ 2) :=
          Real.log_lt_log (Real.sqrt_pos.mpr (by linarith)) hlt
        have h2 : Real.log (Real.sqrt x) = Real.log x / 2 :=
          Real.log_sqrt (by linarith)
        have h3 : Real.log ((k : ℝ) ^ 2) = 2 * Real.log (k : ℝ) := by
          rw [Real.log_pow]
          norm_num
        linarith
      have hy_nn : (0 : ℝ) ≤ x / (k : ℝ) ^ 2 := div_nonneg hxpos.le hc0.le
      have hHle : lrCount (x / (k : ℝ) ^ 2) ≤ x / (k : ℝ) ^ 2 :=
        lrCount_le hy_nn
      have hsq_le : Real.sqrt (Real.log x)
          ≤ 2 * Real.sqrt (Real.log k) := by
        have h1 : Real.log x ≤ 4 * Real.log k := le_of_lt hlog_lt
        calc Real.sqrt (Real.log x)
            ≤ Real.sqrt (4 * Real.log k) := Real.sqrt_le_sqrt h1
          _ = 2 * Real.sqrt (Real.log k) := by
              have e4 : Real.sqrt (4 : ℝ) = 2 := by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                  Real.sqrt_sq (by norm_num)]
              rw [Real.sqrt_mul (by norm_num), e4]
      have hxc0 : x ≠ 0 := ne_of_gt hxpos
      have hc0n : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hc0
      calc lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x
          ≤ 1 * (x / (k : ℝ) ^ 2) * (2 * Real.sqrt (Real.log k)) / x := by
            apply div_le_div_of_nonneg_right _ hxpos.le
            have g1 : lrG k * lrCount (x / (k : ℝ) ^ 2)
                ≤ 1 * (x / (k : ℝ) ^ 2) := by
              calc lrG k * lrCount (x / (k : ℝ) ^ 2)
                  ≤ 1 * lrCount (x / (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_right (lrG_le_one k) (lrCount_nonneg _)
                _ ≤ 1 * (x / (k : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_left hHle (by norm_num)
            exact mul_le_mul g1 hsq_le (Real.sqrt_nonneg _)
              (by simpa using hy_nn)
        _ = (2 * Real.sqrt (Real.log k)) / (k : ℝ) ^ 2 := by
              field_simp
        _ ≤ lrBnd D k := by
              unfold lrBnd
              apply div_le_div_of_nonneg_right _ hc0.le
              linarith [hb_main]

/-- `B(x) · √(log x) / x` as a topological sum over `k`. -/
private lemma lr_B_tsum (x : ℝ) :
    lrB x * Real.sqrt (Real.log x) / x
      = ∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x := by
  have hvan : ∀ k : ℕ, k ∉ Finset.Ioc 0 ⌊x⌋₊ →
      lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x = 0 := by
    intro k hk
    rw [Finset.mem_Ioc, not_and] at hk
    by_cases hk0 : k = 0
    · subst hk0
      simp [lrG_zero]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hk1pos : 0 < k := hk1
      have hkN : ⌊x⌋₊ < k := lt_of_not_ge (hk hk1pos)
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1pos
      have hc0 : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkpos 2
      have hkk : (⌊x⌋₊ : ℝ) + 1 ≤ (k : ℝ) := by
        have h : ⌊x⌋₊ + 1 ≤ k := by omega
        calc (⌊x⌋₊ : ℝ) + 1 = ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_add, Nat.cast_one]
          _ ≤ (k : ℝ) := by exact_mod_cast h
      have hkx : x < (k : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) hkk
      have hkk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr h1k)]
      have hlt : x / (k : ℝ) ^ 2 < 1 := by
        rw [div_lt_one hc0]
        exact lt_of_lt_of_le hkx hkk2
      have h0 : lrCount (x / (k : ℝ) ^ 2) = 0 := lrCount_eq_zero_of_lt_one hlt
      simp [h0]
  have e : (∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
      * Real.sqrt (Real.log x) / x)
      = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x :=
    tsum_eq_sum hvan
  rw [e]
  unfold lrB
  rw [Finset.sum_mul, Finset.sum_div]

/-- Summability of `lrG k / k ^ 2`. -/
private lemma lr_G_div_sq_summable :
    Summable (fun k : ℕ => lrG k / (k : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  · apply div_nonneg (lrG_nonneg k)
    positivity
  · apply div_le_div_of_nonneg_right (lrG_le_one k) (by positivity)

/-- The `G`-series has positive sum. -/
private lemma lr_G_div_sq_tsum_pos :
    0 < ∑' k : ℕ, lrG k / (k : ℝ) ^ 2 := by
  refine Summable.tsum_pos lr_G_div_sq_summable (fun k => ?_) 1 ?_
  · apply div_nonneg (lrG_nonneg k)
    positivity
  · rw [lrG_one]
    norm_num

/-- Dominated convergence for the `k`-sum: `B(x) · √(log x) / x → c₀ > 0`. -/
private lemma lr_B_tendsto (α : ℝ) (hα : 0 < α)
    (hH : Filter.Tendsto (fun x => lrCount x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2))) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      Filter.Tendsto (fun x => lrB x * Real.sqrt (Real.log x) / x)
        Filter.atTop (nhds c₀) := by
  obtain ⟨D, hDpos, hDb⟩ := lr_count_uniform_bound α hα hH
  have hBsum := lr_bnd_summable D
  have hpt : ∀ k : ℕ, Filter.Tendsto
      (fun x => lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (lrG k * (α / 2) / (k : ℝ) ^ 2)) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk0
    · simp only [lrG_zero, zero_mul, zero_div]
      exact tendsto_const_nhds
    · exact lr_f_tendsto k (Nat.one_le_iff_ne_zero.mpr hk0) α hH
  have hdom : ∀ᶠ x : ℝ in Filter.atTop, ∀ k : ℕ,
      ‖lrG k * lrCount (x / (k : ℝ) ^ 2) * Real.sqrt (Real.log x) / x‖
        ≤ lrBnd D k :=
    lr_B_dominated D hDb
  have hlim := tendsto_tsum_of_dominated_convergence hBsum hpt hdom
  have heq : (fun x : ℝ => ∑' k : ℕ, lrG k * lrCount (x / (k : ℝ) ^ 2)
        * Real.sqrt (Real.log x) / x)
      =ᶠ[Filter.atTop] (fun x => lrB x * Real.sqrt (Real.log x) / x) := by
    filter_upwards [Filter.eventually_ge_atTop 0] with x _
    exact (lr_B_tsum x).symm
  have hlimB : Filter.Tendsto (fun x => lrB x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (∑' k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2)) :=
    hlim.congr' heq
  have hS := lr_G_div_sq_tsum_pos
  have htsum_eq : (∑' k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2)
      = (α / 2) * (∑' k : ℕ, lrG k / (k : ℝ) ^ 2) := by
    have e : ∀ k : ℕ, lrG k * (α / 2) / (k : ℝ) ^ 2
        = (α / 2) * (lrG k / (k : ℝ) ^ 2) := fun k => by ring
    simp_rw [e]
    exact tsum_mul_left
  refine ⟨(α / 2) * (∑' k : ℕ, lrG k / (k : ℝ) ^ 2),
    mul_pos (by linarith) hS, ?_⟩
  rw [← htsum_eq]
  exact hlimB

/-- `√(log x) / x` tends to `0`. -/
private lemma lr_sqrt_log_div_tendsto :
    Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.sqrt (Real.log x) / x‖ ≤ x ^ ((-1 / 2 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hle : Real.sqrt (Real.log x) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (Real.log_le_self hxpos.le)
    have e : Real.sqrt x / x = x ^ ((-1 / 2 : ℝ)) := by
      have esub : ((1 / 2 : ℝ) - 1) = -1 / 2 := by norm_num
      rw [Real.sqrt_eq_rpow, ← esub, Real.rpow_sub hxpos, Real.rpow_one]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hxpos.le)]
    calc Real.sqrt (Real.log x) / x ≤ Real.sqrt x / x :=
          div_le_div_of_nonneg_right hle hxpos.le
      _ = x ^ ((-1 / 2 : ℝ)) := e
  have hg : Filter.Tendsto (fun x : ℝ => x ^ ((-1 / 2 : ℝ)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    have e : ((-1 / 2 : ℝ)) = -((1 / 2 : ℝ)) := by norm_num
    rw [e]
    simpa using h
  exact squeeze_zero_norm' hbound hg

section
/-- Landau–Ramanujan theorem: the count of distinct naturals `m ≤ x` of the form
    `m = a ^ 2 + b ^ 2` is asymptotically equivalent to
    `c₀ * x / Real.sqrt (Real.log x)` for some constant `c₀ > 0`.

    Scope note: this statement asserts only the existence of an unspecified
    positive constant `c₀`; it does not identify `c₀` with the
    Landau–Ramanujan constant (the Euler product over the primes
    `p ≡ 3 (mod 4)` in the cited result). That identification is an
    intentional omission relative to the source.

    Controlling source: Labib Haddad and Charles Helou,
    "Representation of Integers by Near Quadratic Sequences,"
    Journal of Integer Sequences 15 (2012),
    `https://cs.uwaterloo.ca/journals/JIS/VOL15/Helou/helou3.tex`,
    lines 483–486. Complete-source SHA-256
    `5441e9d5677d97ca6a836146d5725a10a21bb1e60efa374e366cd803626cd1b1`;
    exact cited span (CRLF-preserving) SHA-256
    `ce727da79eee9763f20dcbafc1b04c02d719c74c58648eddb71f0e34524e91bf`.
    Proof-method source (distinct from the statement source above): the proof
    adapts Wirsing's mean-value method as presented in Gérald Tenenbaum,
    *Introduction to Analytic and Probabilistic Number Theory*, Chapter III.4.
    Concept ID: jis_dep_8a097e6d8b6de10033dfb175;
    grounded candidate: jis_grounded_b8d7333e5ca6cb47b348367c;
    corrected mentions/papers/proof-uses: 2/1/1.

Proves `Wanted` entry `landau_ramanujan_asymptotic`. -/
theorem landau_ramanujan_asymptotic :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      Asymptotics.IsEquivalent (Filter.atTop : Filter ℝ)
        (fun x : ℝ =>
          ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ))
        (fun x : ℝ => c₀ * x / Real.sqrt (Real.log x)) := by
  obtain ⟨α, hαpos, hA⟩ := lr_A_tendsto
  have hH := lr_count_tendsto α hA
  obtain ⟨c₀, hc₀pos, hB⟩ := lr_B_tendsto α hαpos hH
  have hcount : ∀ᶠ x : ℝ in Filter.atTop,
      ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
        = lrB x + 1 := by
    filter_upwards [Filter.eventually_ge_atTop 0] with x hx
    have h1 := lr_ncard_eq hx
    have h2 := lr_twoSq_count_eq hx
    rw [h1, Nat.cast_add, Nat.cast_one, h2]
  have hratio : Filter.Tendsto
      (fun x : ℝ => ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧
        ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
        / (c₀ * x / Real.sqrt (Real.log x)))
      Filter.atTop (nhds 1) := by
    have heq : (fun x : ℝ => ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧
          ∃ a b : ℕ, m = a ^ 2 + b ^ 2} : ℕ) : ℝ)
          / (c₀ * x / Real.sqrt (Real.log x)))
        =ᶠ[Filter.atTop]
        (fun x : ℝ => (lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x) / c₀) := by
      filter_upwards [Filter.eventually_gt_atTop 1, hcount] with x hx1 hcx
      have hlog : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have hsq : Real.sqrt (Real.log x) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hlog)
      have hxx : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
      have hc : c₀ ≠ 0 := ne_of_gt hc₀pos
      rw [hcx]
      field_simp
    have hB' : Filter.Tendsto
        (fun x : ℝ => lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x)
        Filter.atTop (nhds (c₀ + 0)) :=
      hB.add lr_sqrt_log_div_tendsto
    rw [add_zero] at hB'
    have hdiv : Filter.Tendsto
        (fun x : ℝ => (lrB x * Real.sqrt (Real.log x) / x
          + Real.sqrt (Real.log x) / x) / c₀)
        Filter.atTop (nhds (c₀ / c₀)) :=
      hB'.div_const c₀
    have hc0 : c₀ ≠ 0 := ne_of_gt hc₀pos
    rw [div_self hc0] at hdiv
    exact hdiv.congr' heq.symm
  refine ⟨c₀, hc₀pos, ?_⟩
  exact Asymptotics.isEquivalent_of_tendsto_one hratio

end

end MetaMathlibExt
end

/- TauberianBridge -/
section
namespace SquareGrid

open Filter Topology Real

/-- Compare the real-cutoff set used in the ATLAS Landau theorem with
the finite count used for the grid. -/
theorem represented_ncard {x : ℝ} (hx : 0 ≤ x) :
    Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a^2 + b^2} = (represented x).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext m
  simp [represented, Nat.le_floor_iff hx]

theorem landau_normalize {K : ℝ} (hK : 0 < K)
    (h : Asymptotics.IsEquivalent (atTop : Filter ℝ)
      (fun x : ℝ => ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a^2 + b^2}:ℕ):ℝ))
      (fun x : ℝ => K*x/√(log x))) :
    Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x))) atTop (𝓝 K) := by
  have hn : ∀ᶠ x : ℝ in atTop, K*x/√(log x) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact ne_of_gt (div_pos (mul_pos hK (by linarith)) (Real.sqrt_pos.2 (Real.log_pos hx)))
  have hh := ((Asymptotics.isEquivalent_iff_tendsto_one hn).mp h).mul_const K
  rw [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  change ((Set.ncard {m : ℕ | (m : ℝ) ≤ x ∧ ∃ a b : ℕ, m = a^2 + b^2}:ℕ):ℝ) / (K*x/√(log x)) * K = _
  rw [represented_ncard (by linarith : 0 ≤ x)]
  simp [div_eq_mul_inv, mul_comm, mul_assoc, hK.ne']

/-- Landau's counting asymptotic in the normalization used by the grid proof. -/
theorem represented_landau :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun x : ℝ => ((represented x).card : ℝ) / (x / √(log x))) atTop (𝓝 K) := by
  obtain ⟨K, hK, asymptotic⟩ := MetaMathlibExt.landau_ramanujan_asymptotic
  exact ⟨K, hK, landau_normalize hK asymptotic⟩

end SquareGrid
end

/- GridFinal -/
section
theorem OMA.solution : type_of% @OMA.S_oeis_a047800.main := by
  obtain ⟨K, hK, landau⟩ := SquareGrid.represented_landau
  exact SquareGrid.target_of_prime_divergence hK landau SquareGrid.splitFactor
    fun h hh => SquareGrid.angularPrimeSum_tendsto_of_unbounded _ _
      (SquareGrid.rational_angular_defect_unbounded GaussianEuler.unbounded_defect h hh)
end
