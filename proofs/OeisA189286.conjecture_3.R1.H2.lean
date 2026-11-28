import OMAReductions.R_OeisA189286_conjecture_3_R1
import Mathlib

/-
Copyright 2026 The Formal Conjectures Authors and Yuto Nakahara.

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
-- The factorial identities and rational-to-natural conversion are adapted from
-- Yuto Nakahara, github.com/YutoNakahara/oeis-a189286-lean, commit 259c8073.

/-! The power-of-two step of ihateSAS's reduction #3393. The natural-number
convolution setup and factorial form come from Yuto Nakahara via JamesSlash
(#586). The digit-sum valuation lemmas are adapted from PastaPastaPasta
(#3184) and the direct-convolution proof (#4960). Full valuation proofs
also appear in #424 and #3184. Here we compute the next binary digit at
every power of two by isolating the midpoint modulo 32. -/

namespace OeisA189286

private def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

private def sNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

private lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

private lemma denom_pos {n : ℕ} (hn : 0 < n) : 0 < (2 * n - 1) * (3 * n).choose n :=
  Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

private lemma a_eq_div_nat {n : ℕ} (hn : 0 < n) :
    a n = (sNat n : ℚ) / (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
  unfold a sNat tTerm
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp only [tNat, Nat.cast_sum, Nat.cast_mul, hsub]

private lemma tNat_mul_factorials (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
    rwa [show 6 * k - 3 * k = 3 * k by omega] at this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
    rwa [show 3 * k - k = 2 * k by omega] at this
  calc
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
            unfold tNat; ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

private def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private lemma padicValNat_two_fac (n : ℕ) : padicValNat 2 n.factorial = n - s2 n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s2] using this

private lemma s2_le_self (n : ℕ) : s2 n ≤ n := by
  exact Nat.digit_sum_le 2 n

private lemma s2_mul_two (n : ℕ) : s2 (2 * n) = s2 n := by
  by_cases hn : n = 0
  · subst hn; simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [h1, h2]

private lemma s2_pow_two (k : ℕ) : s2 (2 ^ k) = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ', s2_mul_two, ih]

private lemma s2_eq_zero_iff (n : ℕ) : s2 n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne
    have hpos : 0 < (Nat.digits 2 n).sum := by
      have hlast : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hne
      have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
      exact List.sum_pos_iff_exists_pos_nat.mpr ⟨_, hmem, Nat.pos_of_ne_zero hlast⟩
    unfold s2 at h
    omega
  · rintro rfl; simp [s2]

private lemma padicValNat_two_T (k : ℕ) : padicValNat 2 (tNat k) = 2 * s2 k := by
  have hfac := tNat_mul_factorials k
  have hT_pos : 0 < tNat k := mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hT_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac] at hv
  have h6 : s2 (6 * k) = s2 (3 * k) := by rw [show 6 * k = 2 * (3 * k) by ring, s2_mul_two]
  have h2 : s2 (2 * k) = s2 k := s2_mul_two k
  have hle6 := s2_le_self (6 * k)
  have hle3 := s2_le_self (3 * k)
  have hle2 := s2_le_self (2 * k)
  have hle1 := s2_le_self k
  omega

private lemma padicValNat_two_choose3 (n : ℕ) :
    padicValNat 2 ((3 * n).choose n) = 2 * s2 n - s2 (3 * n) := by
  have hfac : (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    simpa [show 3 * n - n = 2 * n by omega] using this
  have hc_pos : 0 < (3 * n).choose n := Nat.choose_pos (by omega)
  have hv := congrArg (padicValNat 2) hfac
  simp only [padicValNat.mul, hc_pos.ne', Nat.factorial_ne_zero, mul_ne_zero_iff, ne_eq,
    not_false_eq_true, and_self, padicValNat_two_fac, s2_mul_two] at hv
  have hle3 := s2_le_self (3 * n)
  have hle2 := s2_le_self (2 * n)
  have hle1 := s2_le_self n
  omega


private def oddProduct : ℕ → ℕ
  | 0 => 1
  | n+1 => oddProduct n * (2*n+1)

private lemma split_factorial (n : ℕ) :
    (2*n).factorial = 2^n * n.factorial * oddProduct n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ, ih,
      Nat.factorial_succ, pow_succ, oddProduct]
    ring

private lemma central_factorial (n : ℕ) :
    n.centralBinom * n.factorial ^ 2 = (2*n).factorial := by
  simpa [Nat.centralBinom, pow_two, Nat.mul_assoc, show 2*n-n = n by omega] using
    Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)

/-- Doubling a central binomial coefficient separates out the odd factorial factors. -/
private lemma double_central (n : ℕ) :
    (2*n).centralBinom * oddProduct n ^ 2 = n.centralBinom * oddProduct (2*n) := by
  apply Nat.eq_of_mul_eq_mul_right (show 0 < (2^n * n.factorial)^2 by positivity)
  calc
    _ = (2*n).centralBinom * ((2*n).factorial)^2 := by rw [split_factorial n]; ring
    _ = (2*(2*n)).factorial := central_factorial _
    _ = 2^(2*n) * (2*n).factorial * oddProduct (2*n) := split_factorial _
    _ = _ := by rw [← central_factorial n, two_mul n, pow_add]; ring

private lemma oddProduct_four (n : ℕ) : oddProduct (4*n) % 4 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 4*(n+1) = 4*n+1+1+1+1 by omega]
    simp only [oddProduct]
    have h0 : oddProduct (4*n) ≡ 1 [MOD 4] := ih
    have h1 : 2*(4*n)+1 ≡ 1 [MOD 4] := by unfold Nat.ModEq; omega
    have h2 : 2*(4*n+1)+1 ≡ 3 [MOD 4] := by unfold Nat.ModEq; omega
    have h3 : 2*(4*n+1+1)+1 ≡ 1 [MOD 4] := by unfold Nat.ModEq; omega
    have h4 : 2*(4*n+1+1+1)+1 ≡ 3 [MOD 4] := by unfold Nat.ModEq; omega
    exact ((((h0.mul h1).mul h2).mul h3).mul h4)

private lemma oddProduct_odd (n : ℕ) : oddProduct n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (oddProduct n * (2*n+1)) % 2 = 1
    rw [Nat.mul_mod, ih, show (2*n+1)%2 = 1 by omega]


/-- The base coefficient is 924. Doubling preserves its residue modulo sixteen. -/
private lemma central_residue (k : ℕ) :
    (3 * 2^(k+1)).centralBinom % 16 = 12 := by
  induction k with
  | zero => decide
  | succ k ih =>
    let n := 3 * 2^(k+1)
    change n.centralBinom % 16 = 12 at ih
    rw [show 3*2^(k+1+1) = 2*n by dsimp [n]; ring]
    have h := congrArg (· % 16) (double_central n)
    have h1 := oddProduct_odd n
    have h2 : oddProduct (2*n) % 4 = 1 := by
      rw [show 2*n = 4*(3*2^k) by dsimp [n]; ring]; exact oddProduct_four _
    rw [Nat.mul_mod, Nat.pow_mod, Nat.mul_mod n.centralBinom, ih] at h
    have cert : ∀ x y z : Fin 16, y.val % 2 = 1 → z.val % 4 = 1 →
        x.val * (y.val^2 % 16) % 16 = 12 * z.val % 16 → x.val = 12 := by decide
    apply cert ⟨_,Nat.mod_lt _ (by decide)⟩ ⟨oddProduct n % 16,Nat.mod_lt _ (by decide)⟩
      ⟨oddProduct (2*n) % 16,Nat.mod_lt _ (by decide)⟩ <;> dsimp <;> omega

private lemma four_dvd_factor {j : ℕ} (hj : 0 < j) : 4 ∣ tNat j := by
  have hs : s2 j ≠ 0 := fun h => hj.ne' ((s2_eq_zero_iff j).mp h)
  apply (padicValNat_dvd_iff_le (tNat_pos j).ne' (p := 2) (n := 2)).2
  rw [padicValNat_two_T]; omega

private lemma factor_pow_residue (k : ℕ) : tNat (2^k) % 8 = 4 := by
  have hv := padicValNat_two_T (2^k)
  rw [s2_pow_two] at hv
  have hd := four_dvd_factor (show 0 < 2^k by positivity)
  have hnd : ¬ 8 ∣ tNat (2^k) := by
    intro h
    have := (padicValNat_dvd_iff_le (tNat_pos _).ne' (p := 2) (n := 3)).1 h
    omega
  omega

/-- Opposite interior terms occur twice and each product is divisible by sixteen. -/
private lemma convolution_midpoint {h : ℕ} (hh : 0 < h) :
    sNat (2*h) % 32 = (2 * tNat (2*h) + (tNat h)^2) % 32 := by
  let F := fun i => tNat i * tNat (2*h-i)
  have hr : ∑ i ∈ Finset.range h, F (h+1+i) = ∑ i ∈ Finset.range h, F i := by
    rw [← Finset.sum_range_reflect F h]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    dsimp [F]
    rw [show 2*h-(h+1+i) = h-1-i by omega, show 2*h-(h-1-i) = h+1+i by omega, mul_comm]
  have hsum : sNat (2*h) = F h + 2*(∑ i ∈ Finset.range h, F i) := by
    change (∑ i ∈ Finset.range (2*h+1), F i) = _
    rw [show 2*h+1 = h+1+h by omega, Finset.sum_range_add, hr, Finset.sum_range_succ]
    ring
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  rw [hsum, Finset.sum_range_succ']
  have hd : 16 ∣ ∑ i ∈ Finset.range l, F (i+1) := by
    apply Finset.dvd_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Nat.mul_dvd_mul (four_dvd_factor (Nat.succ_pos i)) (four_dvd_factor (by omega))
  have hmid : F (l+1) = (tNat (l+1))^2 := by
    simp [F, show 2*(l+1)-(l+1) = l+1 by omega, pow_two]
  have hend : F 0 = tNat (2*(l+1)) := by simp [F, show tNat 0 = 1 by decide]
  rw [hmid, hend]
  simp only [Nat.succ_eq_add_one] at *
  omega

private lemma choose_odd (k : ℕ) : (3*2^k).choose (2^k) % 2 = 1 := by
  have hs : s2 (3*2^k) = 2 := by
    induction k with
    | zero => decide
    | succ k ih => rw [show 3*2^(k+1) = 2*(3*2^k) by ring, s2_mul_two, ih]
  have h := padicValNat_two_choose3 (2^k)
  rw [s2_pow_two, hs] at h
  by_contra! he
  have hd : 2^1 ∣ (3*2^k).choose (2^k) := by omega
  have := (padicValNat_dvd_iff_le (p := 2) (Nat.choose_pos (show 2^k ≤ 3*2^k by omega)).ne').1 hd
  omega

/-- At positive powers of two beyond one, the quotient by eight is three modulo four. -/
private lemma power_two_quotient (k : ℕ) (m : ℤ) (hm : a (2^(k+1)) = 8*m) :
    m % 4 = 3 := by
  let h := 2^k
  let n := 2^(k+1)
  let B := (3*n).choose n
  let C := (3*n).centralBinom
  have hh : 0 < h := by dsimp [h]; positivity
  have hn : n = 2*h := by dsimp [n,h]; ring
  have hn0 : 0 < n := by omega
  change a n = 8*m at hm
  rw [a_eq_div_nat hn0] at hm
  have hnum := (div_eq_iff (Nat.cast_ne_zero.mpr (denom_pos hn0).ne')).1 hm
  have heq : (sNat n : ℤ) = 8*m*((2*n-1 : ℕ)*B : ℕ) := by exact_mod_cast hnum
  have hpair := convolution_midpoint hh
  rw [← hn] at hpair
  have ht : tNat n = C*B := by dsimp [tNat, C, Nat.centralBinom, B]; rw [show 2*(3*n) = 6*n by ring]
  rw [ht] at hpair
  obtain ⟨b, hb⟩ : ∃ b, B = 2*b+1 := ⟨B/2, by have := choose_odd (k+1); change B%2 = 1 at this; omega⟩
  obtain ⟨c, hc⟩ : ∃ c, C = 16*c+12 := ⟨C/16, by have := central_residue k; change C%16 = 12 at this; omega⟩
  obtain ⟨f, hf⟩ : ∃ f, tNat h = 8*f+4 := ⟨tNat h/8, by have := factor_pow_residue k; change tNat h%8 = 4 at this; omega⟩
  have hd : 2*n-1 = 4*(h-1)+3 := by omega
  have hz := congrArg (fun z : ℤ => (z : ZMod 32)) heq
  have hp := (ZMod.natCast_eq_natCast_iff' _ _ _).2 hpair
  rw [hd, hb] at hz
  rw [hc, hb, hf] at hp
  push_cast at hz hp
  have hm32 : 8 * (m : ZMod 32) = 24 := by
    have zero32 (r : ℕ) : ((32*r : ℕ) : ZMod 32) = 0 := by
      push_cast
      rw [show (32 : ZMod 32) = 0 by decide, zero_mul]
    have z64 : (64 : ZMod 32) = 0 := zero32 2
    have z96 : (96 : ZMod 32) = 0 := zero32 3
    have z192 : (192 : ZMod 32) = 0 := zero32 6
    have z288 : (288 : ZMod 32) = 0 := zero32 9
    have z384 : (384 : ZMod 32) = 0 := zero32 12
    -- Multiplication by three times the odd binomial factor cancels the denominator
    -- after the multiple of eight has been taken into account.
    linear_combination (norm := (ring_nf; simp [z64, z96, z192, z288, z384])) (3 * (2*(b : ZMod 32)+1)) * (hp - hz)
  have hmod : (8*m)%32 = 24 := by
    apply (ZMod.intCast_eq_intCast_iff' (8*m) 24 32).1
    push_cast
    exact hm32
  omega

end OeisA189286

theorem OMA.solution : OMA.R_OeisA189286_conjecture_3_R1.H2 := by
  rintro n _ m hm ⟨k,rfl⟩
  rw [Int.odd_iff]
  cases k with
  | zero =>
    rw [pow_zero, OeisA189286.a_1] at hm
    have h : m = 5 := by exact_mod_cast (show (m : ℚ) = 5 by linarith)
    omega
  | succ k => have := OeisA189286.power_two_quotient k m hm; omega

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
