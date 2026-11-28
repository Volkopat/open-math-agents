import OMAReductions.R_Erdos101_erdos_101_R2_H2_R1
import Mathlib

-- Extracted from @ubuwaits's accepted proof of Erdős 101 R2.H2 (PR #23304).

/-!
# Bounded triangle ratios in the four-point line problem

This file proves the bounded-ratio implication in @ubuwaits' reduction R2
of Erdős 101. It uses graph triangle removal, homogeneous coordinates and
additive energy, together with previously formalized results of
Balog–Szemerédi–Gowers and Freiman. Credits and source notices accompany
the included formalizations.

The additive-energy result uses Adam McKenna's Apache-2.0 BSG formalization
in mysticflounder/lean-formalizations, commit
db02244c25aecd74eb96d9186c922387824c1258, including the symmetric theorem.
The finite integer Freiman proof
is extracted from the public Erdős 245 proof in open-math-agents, adapted
there from Boris Alexeev's Apache-2.0 plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e. The bounded-order integer model,
coordinate-fiber estimate and tripartite two-anchor argument below connect
these results to the given triangle-ratio hypothesis.
-/


section UniformEnergySparsity

/-! # Sparse additive energy for sets with a line cap

The integer progression theorem below is an extraction of the proof of
Erdős 245 on Left to Solve and includes the full Apache-2.0 license.
The full Balog–Szemerédi–Gowers formalization is by Adam McKenna,
from mysticflounder/lean-formalizations, commit
db02244c25aecd74eb96d9186c922387824c1258, also Apache-2.0.
Both original notices are retained below. The remaining geometry and
adaptations are from this proof. -/

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


/- This extract retains only the dependencies of the integer GAP covering theorem.
   Original artifact: Left to Solve, proofs/Erdos245.erdos_245.lean.
   Extracted 2026-11-27. -/
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

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


/-!
# Balog–Szemerédi–Gowers theorem

The Balog–Szemerédi–Gowers theorem over `Finset.addEnergy` for an arbitrary
additive commutative group, proved via Gowers' graph-theoretic argument.

## Main statements

* `Finset.balog_szemeredi_gowers_symmetric` — equal-sets form
  `E[X,X] ≥ η|X|³ ⇒ ∃ X' ⊆ X, c|X| ≤ |X'| ∧ |X'-X'| ≤ C|X|`.
* `Finset.balog_szemeredi_gowers_asymmetric` — equal-cardinality two-sets form
  `E[X,Y] ≥ η|X|³ ⇒ ∃ X' ⊆ X, Y' ⊆ Y, c·n ≤ |X'|,|Y'| ∧ |X'-Y'| ≤ C·n`.
* `Finset.balog_szemeredi_gowers_asymmetric_explicit` — the asymmetric form with
  the existential constants exposed as explicit polynomials in `η`
  (`c = η/16` and an explicit `C(η)`).

The first two statements are qualitative: the constants `c, C : ℝ` are
existential, with no polynomial dependence on `η` exposed.

## References

* Tao–Vu, *Additive Combinatorics* §6.4 (Gowers' graph-theoretic proof).
* Reiher–Schoen, "Note on the Theorem of Balog, Szemerédi, and Gowers",
  *Combinatorica* (2024), arXiv:2308.10245 (the `K⁴` difference-set refinement).
-/

namespace Finset

open scoped Pointwise

/--
Sum of fiber counts over the sumset equals the total pair count.
Helper for the popular-sum lemma: gives `Σ_s r(s) = |X|·|Y|`, the
denominator in the Markov / Cauchy-Schwarz step.
-/
lemma sum_addConvolution_eq_card_product {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) :
    ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card := by
  simp_rw [Finset.addConvolution]
  rw [Finset.sum_card_fiberwise_eq_card_filter, Finset.filter_eq_self.mpr,
    Finset.card_product]
  rintro ⟨a, b⟩ hab
  rw [Finset.mem_product] at hab
  exact Finset.add_mem_add hab.1 hab.2


/--
Additive energy as a sum of squared fiber counts. Restatement of
Mathlib `Finset.addEnergy_eq_sum_sq` in terms of the convolution
`X.addConvolution Y`; the energy equals `Σ_{s ∈ X+Y} r(s)²` where
`r(s)` is the number of pairs `(x,y)` summing to `s`.
-/
lemma addEnergy_eq_sum_addConvolution_sq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) :
    Finset.addEnergy X Y = ∑ s ∈ X + Y, (X.addConvolution Y s) ^ 2 := by
  simp_rw [Finset.addConvolution]
  exact Finset.addEnergy_eq_sum_sq' X Y


/--
Split the energy sum into rare-fiber and popular-fiber parts at
threshold `θ`. The two filters partition `X + Y` (over `<` vs `≥`),
so combining them recovers the full `Σ r(s)²` form of
`Finset.addEnergy`.
-/
lemma addEnergy_split_by_threshold {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (θ : ℕ) :
    (Finset.addEnergy X Y : ℕ) =
      (∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
        (X.addConvolution Y s) ^ 2) +
      (∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        (X.addConvolution Y s) ^ 2) := by
  rw [addEnergy_eq_sum_addConvolution_sq,
    ← Finset.sum_filter_add_sum_filter_not (X + Y) (fun s ↦ X.addConvolution Y s < θ)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  apply Finset.filter_congr
  intros
  omega


/--
Popular-difference lemma (sum form). The rare part of `Σ r(s)²`
(over fibers with `r(s) < θ`) is bounded by `θ · |X| · |Y|`, because
`r(s)² ≤ θ · r(s)` on the rare set and `Σ r(s) = |X|·|Y|`
(`sum_addConvolution_eq_card_product`). Therefore
`E[X,Y] ≤ θ·|X|·|Y| + (popular part)`, giving the popular-sum set
its energy bound for the random-restriction step.
-/
lemma addEnergy_le_popular_part {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (θ : ℕ) :
    (Finset.addEnergy X Y : ℕ) ≤ θ * (X.card * Y.card) +
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        (X.addConvolution Y s) ^ 2 := by
  rw [addEnergy_split_by_threshold X Y θ]
  refine Nat.add_le_add_right ?_ _
  calc ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          (X.addConvolution Y s) ^ 2
      ≤ ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          θ * X.addConvolution Y s := by
        refine Finset.sum_le_sum fun s hs ↦ ?_
        rw [Finset.mem_filter] at hs
        have hle : X.addConvolution Y s ≤ θ := Nat.le_of_lt hs.2
        rw [pow_two]
        exact Nat.mul_le_mul_right _ hle
    _ = θ * ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          X.addConvolution Y s := by rw [Finset.mul_sum]
    _ ≤ θ * ∑ s ∈ X + Y, X.addConvolution Y s :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    _ = θ * (X.card * Y.card) := by rw [sum_addConvolution_eq_card_product]


/--
**Popular-pair cardinality lower bound.** Given an additive-energy lower
bound `E[X,Y] ≥ η·|X|³` with equal cardinalities `|X|=|Y|`, the popular
bipartite graph
  `G(θ) := { (x,y) ∈ X × Y : X.addConvolution Y (x+y) ≥ θ }`
satisfies `|G(θ)| ≥ (η/2)·|X|·|Y|` whenever the threshold `θ` satisfies
`2θ ≤ η·|X|`. Proof outline: `addEnergy_le_popular_part` bounds the rare
part by `θ·|X|·|Y|`, leaving the popular-fiber sum-of-squares to carry
the residual `≥ η·|X|³/2` (using `|Y|=|X|` and `2θ ≤ η·|X|`); the trivial
fiber-size bound `r(s) ≤ |X|` (Mathlib `Finset.addConvolution_le_card_left`)
converts that to `|X|·|popular pair count|`; the popular pair count then
equals `∑_{s popular} r(s)` by fiber-rewriting. Consumed by the
random-restriction step in the Balog-Szemerédi-Gowers proof.
-/
lemma popular_pairs_card_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (_hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    η / 2 * (X.card : ℝ) * Y.card ≤
      (((X ×ˢ Y).filter
        (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hYcard : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
  have hsplit_nat := addEnergy_le_popular_part X Y θ
  have hsplit : (Finset.addEnergy X Y : ℝ) ≤
      θ * ((X.card : ℝ) * Y.card) +
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hsplit_nat
    push_cast at h
    exact h
  have hθBd : (θ : ℝ) * ((X.card : ℝ) * Y.card) ≤ η / 2 * (X.card : ℝ) ^ 3 := by
    rw [hYcard]
    have hθ' : (θ : ℝ) ≤ η / 2 * X.card := by linarith
    have hsq_nn : (0 : ℝ) ≤ (X.card : ℝ) ^ 2 := sq_nonneg _
    have hmul : (θ : ℝ) * (X.card : ℝ) ^ 2 ≤ (η / 2 * X.card) * (X.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hθ' hsq_nn
    nlinarith [hmul]
  have hpopSqLB : η / 2 * (X.card : ℝ) ^ 3 ≤
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 := by linarith
  have hsqLE : ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 ≤
      (X.card : ℝ) * ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun s _ ↦ ?_)
    have hrLE : X.addConvolution Y s ≤ X.card :=
      Finset.addConvolution_le_card_left
    have hrLE' : ((X.addConvolution Y s : ℝ)) ≤ (X.card : ℝ) := by exact_mod_cast hrLE
    have hr_nn : (0 : ℝ) ≤ ((X.addConvolution Y s : ℝ)) := by positivity
    nlinarith
  have hfiber_nat : ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        X.addConvolution Y s =
      ((X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card := by
    simp only [Finset.addConvolution]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_congr
    rintro ⟨a, b⟩ hp
    rw [Finset.mem_product] at hp
    constructor
    · intro h
      have h' : a + b ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s) := h
      exact (Finset.mem_filter.mp h').2
    · intro h
      have h' : a + b ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s) :=
        Finset.mem_filter.mpr ⟨Finset.add_mem_add hp.1 hp.2, h⟩
      exact h'
  have hcombined : η / 2 * (X.card : ℝ) ^ 3 ≤
      (X.card : ℝ) *
      (((X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
    calc η / 2 * (X.card : ℝ) ^ 3
        ≤ ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
            ((X.addConvolution Y s : ℝ)) ^ 2 := hpopSqLB
      _ ≤ (X.card : ℝ) * ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
            ((X.addConvolution Y s : ℝ)) := hsqLE
      _ = (X.card : ℝ) *
            (((X ×ˢ Y).filter
              (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
          congr 1
          exact_mod_cast hfiber_nat
  have hdiv : η / 2 * (X.card : ℝ) ^ 2 ≤
      (((X ×ˢ Y).filter
        (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
    have heq : η / 2 * (X.card : ℝ) ^ 3 =
        (X.card : ℝ) * (η / 2 * (X.card : ℝ) ^ 2) := by ring
    rw [heq] at hcombined
    exact le_of_mul_le_mul_left hcombined hXpos
  have hgoal : η / 2 * (X.card : ℝ) * Y.card = η / 2 * (X.card : ℝ) ^ 2 := by
    rw [hYcard]; ring
  linarith


/--
**Double Markov refinement (rectangle mass concentration).**

Given finite nonempty sets `X, Y`, a nonnegative function `f : X × Y → ℝ`
pointwise bounded by `M`, and assuming `∑_{(x,y)} f x y ≥ θ · M · |X| · |Y|`
for some `θ ∈ [0, 1]`, there exist subsets `X ⊆ X`, `Y ⊆ Y` of size
≥ (θ/2)·|X| and (θ/4)·|Y| respectively whose rectangle mass is
≥ (θ/4) · M · |X| · |Y|.

Proof: iterated Markov. First refine to rows with row-sum ≥ (θ/2)·M·|Y|
(size ≥ (θ/2)·|X|), then refine to columns with column-sum ≥ (θ/4)·M·|X|
restricted to `X` (size ≥ (θ/4)·|Y|).

NOTE: currently unused by the BSG proof (the live path uses the
dependent-random-choice track, not this rectangle refinement). Retained as a
self-contained, fully general result over arbitrary types — a potential mathlib
contribution. Safe to delete if no longer wanted.
-/
lemma double_markov_refinement {α β : Type*}
    (X : Finset α) (Y : Finset β) (f : α → β → ℝ) (M θ : ℝ) :
    0 ≤ M → 0 ≤ θ → θ ≤ 1 → X.Nonempty → Y.Nonempty →
    (∀ x ∈ X, ∀ y ∈ Y, 0 ≤ f x y) →
    (∀ x ∈ X, ∀ y ∈ Y, f x y ≤ M) →
    θ * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ x ∈ X, ∑ y ∈ Y, f x y →
    ∃ Xs : Finset α, ∃ Ys : Finset β, Xs ⊆ X ∧ Ys ⊆ Y ∧
      (θ / 2) * (X.card : ℝ) ≤ (Xs.card : ℝ) ∧
      (θ / 4) * (Y.card : ℝ) ≤ (Ys.card : ℝ) ∧
      (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
        ∑ x ∈ Xs, ∑ y ∈ Ys, f x y := by
  classical
  intro hM hθ hθ1 hX hY hf_nn hf_ub hlower
  -- Total mass shorthand: TotalMass := ∑_{x ∈ X} ∑_{y ∈ Y} f x y
  -- Step 1: X' := { x ∈ X : ∑_y f x y ≥ (θ/2)·M·|Y| }.
  set rowSum : α → ℝ := fun x ↦ ∑ y ∈ Y, f x y with hrowSum_def
  set X' : Finset α := X.filter (fun x ↦ (θ / 2) * M * (Y.card : ℝ) ≤ rowSum x)
    with hX'_def
  have hX'_sub : X' ⊆ X := Finset.filter_subset _ _
  -- Pointwise: each row sum is ≤ M·|Y|.
  have hrowSum_le : ∀ x ∈ X, rowSum x ≤ M * (Y.card : ℝ) := by
    intro x hx
    have : ∑ y ∈ Y, f x y ≤ ∑ _y ∈ Y, M := by
      refine Finset.sum_le_sum fun y hy ↦ hf_ub x hx y hy
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at this
    exact this
  -- Cards as reals.
  have hXR_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hYR_pos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hXR_nn : (0 : ℝ) ≤ (X.card : ℝ) := le_of_lt hXR_pos
  have hYR_nn : (0 : ℝ) ≤ (Y.card : ℝ) := le_of_lt hYR_pos
  -- Split total sum X = X' ⊔ (X \ X').
  have hSplit_X :
      ∑ x ∈ X, rowSum x = (∑ x ∈ X', rowSum x) + ∑ x ∈ X \ X', rowSum x := by
    rw [← Finset.sum_sdiff hX'_sub]; ring
  -- Rare part: each x ∈ X \ X' has rowSum x < (θ/2)·M·|Y|.
  have hRare_X : ∑ x ∈ X \ X', rowSum x ≤
      ((X \ X').card : ℝ) * ((θ / 2) * M * (Y.card : ℝ)) := by
    rw [show ((X \ X').card : ℝ) * ((θ / 2) * M * (Y.card : ℝ)) =
              ∑ _x ∈ X \ X', ((θ / 2) * M * (Y.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun x hx ↦ ?_
    rw [Finset.mem_sdiff, hX'_def, Finset.mem_filter] at hx
    by_contra hgt
    push Not at hgt
    exact hx.2 ⟨hx.1, le_of_lt hgt⟩
  -- Popular part of X: each x has rowSum x ≤ M·|Y|.
  have hPop_X_le : ∑ x ∈ X', rowSum x ≤ (X'.card : ℝ) * (M * (Y.card : ℝ)) := by
    rw [show (X'.card : ℝ) * (M * (Y.card : ℝ)) =
              ∑ _x ∈ X', (M * (Y.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun x hx ↦ hrowSum_le x (hX'_sub hx)
  -- Lower bound on total sum.
  have hTotal_lb : θ * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ x ∈ X, rowSum x := by
    simpa [rowSum] using hlower
  -- Mass on X' rows: ≥ (θ/2)·M·|X|·|Y|.
  have hMass_X' :
      (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ x ∈ X', rowSum x := by
    have hsdiff_le_X : ((X \ X').card : ℝ) ≤ (X.card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have h_θM_nn : (0 : ℝ) ≤ (θ / 2) * M * (Y.card : ℝ) := by
      have : 0 ≤ θ / 2 := by linarith
      have : 0 ≤ θ / 2 * M := mul_nonneg this hM
      nlinarith [this, hYR_nn]
    have hRare_X' : ∑ x ∈ X \ X', rowSum x ≤ (X.card : ℝ) * ((θ / 2) * M * (Y.card : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hsdiff_le_X h_θM_nn
      linarith [hRare_X]
    nlinarith [hSplit_X, hTotal_lb, hRare_X']
  -- |X'| ≥ (θ/2)·|X|.
  -- From hMass_X' and hPop_X_le: (X'.card)·M·|Y| ≥ (θ/2)·M·|X|·|Y|,
  -- and on the bounded-M side we use that θ ≤ 1 was given...
  -- But we need to derive |X'|·M·|Y| ≥ (θ/2)·M·|X|·|Y|, then divide by M·|Y|.
  -- If M = 0, hPop_X_le forces ∑_{x∈X'} rowSum x = 0, but hMass_X' = (θ/2)*0*|X|*|Y| = 0 ≤ 0 ✓.
  -- In that case the size claim |X'| ≥ (θ/2)|X| can't be derived this way — need a special case.
  by_cases hM0 : M = 0
  · -- Then f ≡ 0 on X×Y; take X' = X, Y' = Y; rectangle mass is 0 = (θ/4)·0·|X|·|Y|.
    refine ⟨X, Y, Finset.Subset.refl _, Finset.Subset.refl _, ?_, ?_, ?_⟩
    · -- (θ/2) * |X| ≤ |X|
      nlinarith [hXR_nn, hθ, hθ1]
    · -- (θ/4) * |Y| ≤ |Y|
      nlinarith [hYR_nn, hθ, hθ1]
    · -- (θ/4) * M * |X| * |Y| ≤ ∑ ∑ f. Both sides are 0.
      have hzero : ∑ x ∈ X, ∑ y ∈ Y, f x y = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        refine Finset.sum_eq_zero ?_
        intro y hy
        have h1 := hf_nn x hx y hy
        have h2 := hf_ub x hx y hy
        rw [hM0] at h2
        linarith
      rw [hzero, hM0]
      ring_nf
      exact le_refl 0
  · -- M > 0 case.
    have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hMY_pos : 0 < M * (Y.card : ℝ) := mul_pos hMpos hYR_pos
    -- |X'| ≥ (θ/2)·|X| from hMass_X' and hPop_X_le.
    have hX'_card_lb : (θ / 2) * (X.card : ℝ) ≤ (X'.card : ℝ) := by
      have h1 : (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
                (X'.card : ℝ) * (M * (Y.card : ℝ)) := le_trans hMass_X' hPop_X_le
      have hMY_ne : M * (Y.card : ℝ) ≠ 0 := ne_of_gt hMY_pos
      -- Divide both sides by M * |Y| > 0.
      have heq : (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) =
                 ((θ / 2) * (X.card : ℝ)) * (M * (Y.card : ℝ)) := by ring
      rw [heq] at h1
      exact le_of_mul_le_mul_right h1 hMY_pos
    -- Step 2: Y' := { y ∈ Y : ∑_{x ∈ X'} f x y ≥ (θ/4)·M·|X| }.
    set colSum : β → ℝ := fun y ↦ ∑ x ∈ X', f x y with hcolSum_def
    set Y' : Finset β := Y.filter (fun y ↦ (θ / 4) * M * (X.card : ℝ) ≤ colSum y)
      with hY'_def
    have hY'_sub : Y' ⊆ Y := Finset.filter_subset _ _
    -- Pointwise: colSum y ≤ M·|X'|  (since x ∈ X' ⊆ X, f x y ≤ M).
    have hcolSum_le : ∀ y ∈ Y, colSum y ≤ M * (X.card : ℝ) := by
      intro y hy
      have : ∑ x ∈ X', f x y ≤ ∑ _x ∈ X', M := by
        refine Finset.sum_le_sum fun x hx ↦ hf_ub x (hX'_sub hx) y hy
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at this
      have hX'_le_X : (X'.card : ℝ) ≤ (X.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hX'_sub
      have hMnn : 0 ≤ M := hM
      have hbound : M * (X'.card : ℝ) ≤ M * (X.card : ℝ) :=
        mul_le_mul_of_nonneg_left hX'_le_X hMnn
      linarith [this]
    -- We need a reverse bound for the rare-part argument:
    -- For y ∈ Y \ Y', colSum y < (θ/4)·M·|X|.
    -- And a bound for the popular-part argument:
    -- For y ∈ Y', colSum y ≤ M·|X'| ≤ M·|X|.
    -- Now derive the column total: ∑_{y∈Y} colSum y = ∑_{y} ∑_{x∈X'} f x y
    -- = ∑_{x∈X'} ∑_y f x y = ∑_{x∈X'} rowSum x.
    have hSumCol : ∑ y ∈ Y, colSum y = ∑ x ∈ X', rowSum x := by
      simp only [colSum, rowSum]
      rw [Finset.sum_comm]
    -- Total column mass ≥ (θ/2)·M·|X|·|Y|.
    have hCol_total_lb :
        (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ y ∈ Y, colSum y := by
      rw [hSumCol]; exact hMass_X'
    -- Split column sum across Y' ⊔ (Y \ Y').
    have hSplit_Y :
        ∑ y ∈ Y, colSum y = (∑ y ∈ Y', colSum y) + ∑ y ∈ Y \ Y', colSum y := by
      rw [← Finset.sum_sdiff hY'_sub]; ring
    -- Rare-Y bound.
    have hRare_Y : ∑ y ∈ Y \ Y', colSum y ≤
        ((Y \ Y').card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) := by
      rw [show ((Y \ Y').card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) =
                ∑ _y ∈ Y \ Y', ((θ / 4) * M * (X.card : ℝ)) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun y hy ↦ ?_
      rw [Finset.mem_sdiff, hY'_def, Finset.mem_filter] at hy
      by_contra hgt
      push Not at hgt
      exact hy.2 ⟨hy.1, le_of_lt hgt⟩
    -- Popular-Y bound.
    have hPop_Y_le : ∑ y ∈ Y', colSum y ≤ (Y'.card : ℝ) * (M * (X.card : ℝ)) := by
      rw [show (Y'.card : ℝ) * (M * (X.card : ℝ)) =
                ∑ _y ∈ Y', (M * (X.card : ℝ)) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun y hy ↦ hcolSum_le y (hY'_sub hy)
    -- |Y'| ≥ (θ/4)·|Y|.
    have hMX_pos : 0 < M * (X.card : ℝ) := mul_pos hMpos hXR_pos
    have hY'_card_lb : (θ / 4) * (Y.card : ℝ) ≤ (Y'.card : ℝ) := by
      have hsdiff_le_Y : ((Y \ Y').card : ℝ) ≤ (Y.card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
      have h_θM_nn : (0 : ℝ) ≤ (θ / 4) * M * (X.card : ℝ) := by
        have h1 : 0 ≤ θ / 4 := by linarith
        nlinarith [h1, hM, hXR_nn]
      have hRare_Y' : ∑ y ∈ Y \ Y', colSum y ≤ (Y.card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hsdiff_le_Y h_θM_nn
        linarith [hRare_Y]
      -- (Y'.card)·M·|X| + (θ/4)·M·|X|·|Y| ≥ (θ/2)·M·|X|·|Y|
      -- ⇒ (Y'.card)·M·|X| ≥ (θ/4)·M·|X|·|Y|
      -- ⇒ |Y'| ≥ (θ/4)·|Y|.
      have hcombined : (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
                       (Y'.card : ℝ) * (M * (X.card : ℝ)) := by
        nlinarith [hSplit_Y, hCol_total_lb, hPop_Y_le, hRare_Y']
      have heq : (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) =
                 ((θ / 4) * (Y.card : ℝ)) * (M * (X.card : ℝ)) := by ring
      rw [heq] at hcombined
      exact le_of_mul_le_mul_right hcombined hMX_pos
    -- Mass on (X', Y'): ≥ (θ/4)·M·|X|·|Y|.
    have hMass_rect :
        (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
          ∑ x ∈ X', ∑ y ∈ Y', f x y := by
      -- Rewrite ∑ x ∈ X', ∑ y ∈ Y', f x y = ∑ y ∈ Y', colSum y.
      have hSwap : ∑ x ∈ X', ∑ y ∈ Y', f x y = ∑ y ∈ Y', colSum y :=
        Finset.sum_comm
      -- ∑ y ∈ Y', colSum y = ∑ y ∈ Y, colSum y - ∑ y ∈ Y\Y', colSum y.
      have hY'_eq : ∑ y ∈ Y', colSum y =
                    (∑ y ∈ Y, colSum y) - ∑ y ∈ Y \ Y', colSum y := by
        rw [hSplit_Y]; ring
      -- Bound on rare-Y' contribution.
      have hRare_Y'' : ∑ y ∈ Y \ Y', colSum y ≤
          (Y.card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) := by
        have hsdiff_le_Y : ((Y \ Y').card : ℝ) ≤ (Y.card : ℝ) := by
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset
        have h_θ4_nn : (0 : ℝ) ≤ θ / 4 := by linarith
        have h_θ4M_nn : (0 : ℝ) ≤ (θ / 4) * M := mul_nonneg h_θ4_nn hM
        have h_θMnX_nn : (0 : ℝ) ≤ (θ / 4) * M * (X.card : ℝ) :=
          mul_nonneg h_θ4M_nn hXR_nn
        have := mul_le_mul_of_nonneg_right hsdiff_le_Y h_θMnX_nn
        linarith [hRare_Y]
      rw [hSwap, hY'_eq]
      linarith [hCol_total_lb, hRare_Y'']
    -- Assemble the witnesses.
    refine ⟨X', Y', hX'_sub, hY'_sub, hX'_card_lb, hY'_card_lb, hMass_rect⟩


/--
**Length-3 path count is dominated by a triple-rep count in `S × S × S`.**

For a bipartite graph `E ⊆ A ×ˢ B` over an additive commutative group, fix a
restricted sumset `S` containing all sums `p.1 + p.2` for `p ∈ E`. For any
`a, b ∈ G`, the number of length-3 paths `a — b₁ — a₁ — b` in `E` is at most
the number of triples `(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`.

Proof: the map `(b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b)` sends each path to a
triple in `S × S × S` (because each edge `(x, y) ∈ E` has `x + y ∈ S`) summing
to `a + b` under `s₁ - s₂ + s₃`. It is injective: `b₁` is recovered from
`(a + b₁) - a` (or equivalently from the first coordinate minus the constant `a`),
and `a₁` is recovered from the third coordinate as `(a₁ + b) - b`.

Used by `graph_balogSzemerediGowers_restricted_sumset` to bridge the pointwise
length-3 path count (supplied by `dense_bipartite_has_path3_rectangle` via
dependent random choice) to the triple-rep multiplicity hypothesis of
`restricted_sumset_via_multiplicity`. Tao-Vu, *Additive Combinatorics*, §6.4
(Cor. 6.20).
-/
lemma path3_count_le_triple_rep_count {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (E : Finset (G × G)) (hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S)
    (a b : G) :
    (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
    ≤ ((S ×ˢ S ×ˢ S).filter
        fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card := by
  -- Define the map (b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b).
  set f : G × G → G × G × G := fun q ↦ (a + q.1, q.2 + q.1, q.2 + b) with hf_def
  set src : Finset (G × G) :=
    (B ×ˢ A).filter (fun q : G × G ↦
      (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E) with hsrc_def
  set tgt : Finset (G × G × G) :=
    (S ×ˢ S ×ˢ S).filter (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)
    with htgt_def
  apply Finset.card_le_card_of_injOn f
  · -- MapsTo: f sends src into tgt.
    intro q hq
    simp only [hsrc_def, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_product] at hq
    obtain ⟨⟨_hq1B, _hq2A⟩, hEab1, hEa1b1, hEa1b⟩ := hq
    have hs1 : a + q.1 ∈ S := hSdef (a, q.1) hEab1
    have hs2 : q.2 + q.1 ∈ S := hSdef (q.2, q.1) hEa1b1
    have hs3 : q.2 + b ∈ S := hSdef (q.2, b) hEa1b
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_product.mpr ⟨hs1, Finset.mem_product.mpr ⟨hs2, hs3⟩⟩
    · -- (a + b₁) - (a₁ + b₁) + (a₁ + b) = a + b.
      show (a + q.1) - (q.2 + q.1) + (q.2 + b) = a + b
      abel
  · -- InjOn: f is injective on src.
    intro q₁ _hq₁ q₂ _hq₂ hfeq
    -- f q₁ = f q₂ means (a + q₁.1, q₁.2 + q₁.1, q₁.2 + b) = (a + q₂.1, …, q₂.2 + b).
    -- Project out the first and third coordinates of the triple equality.
    have h1 : a + q₁.1 = a + q₂.1 := by
      have := congrArg Prod.fst hfeq
      simpa [hf_def] using this
    have h3 : q₁.2 + b = q₂.2 + b := by
      have := congrArg (fun p : G × G × G ↦ p.2.2) hfeq
      simpa [hf_def] using this
    have hq1eq : q₁.1 = q₂.1 := add_left_cancel h1
    have hq2eq : q₁.2 = q₂.2 := add_right_cancel h3
    exact Prod.ext hq1eq hq2eq

/--
**Restricted sumset upper bound via difference-set multiplicity.**

Let `A, B, S ⊆ G`. If every `(a, b) ∈ A × B` admits at least `M` triples
`(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`, then
`M · |A + B| ≤ |S|³`.

Proof: the disjoint fibers `T_v := { (s₁, s₂, s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }`
indexed by `v ∈ A + B` each contain ≥ M triples and embed into `S × S × S`,
so `M · |A + B| ≤ ∑_{v ∈ A + B} |T_v| ≤ |S|³`.

This is the standard sumset bound used in the Tao-Vu / Petridis path-counting
proof of Balog-Szemerédi-Gowers: the triple-counting step inside the proof of
Tao-Vu, *Additive Combinatorics*, Theorem 2.29 (§6.4) — `#triples ≤ |A+B|³` —
not a separately numbered lemma.
-/
lemma restricted_sumset_via_multiplicity {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (M : ℕ) :
    (∀ a ∈ A, ∀ b ∈ B,
        M ≤ ((S ×ˢ S ×ˢ S).filter
          (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card) →
    M * (A + B).card ≤ S.card ^ 3 := by
  intro hcover
  -- Build the disjoint sets T_v = { (s₁,s₂,s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }.
  set T : G → Finset (G × G × G) :=
    fun v ↦ (S ×ˢ S ×ˢ S).filter (fun p ↦ p.1 - p.2.1 + p.2.2 = v) with hT_def
  -- Each fiber T_v contributes at least M to the sum over A + B.
  have hMle : ∀ v ∈ A + B, M ≤ (T v).card := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hv
    -- Substitute a + b = v in the multiplicity hypothesis.
    have hM_at := hcover a ha b hb
    -- The triple subset T(a,b) has card ≥ M, and lies inside T v.
    set T_ab : Finset (G × G × G) :=
      (S ×ˢ S ×ˢ S).filter
        (fun p ↦ p.1 - p.2.1 + p.2.2 = a + b) with hTab_def
    have hT_ab_eq : T_ab = T v := by
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h; rw [h, hab]
      · intro h; rw [h, ← hab]
    have : M ≤ T_ab.card := hM_at
    rw [hT_ab_eq] at this
    exact this
  -- The fibers cover disjointly inside S × S × S.
  -- Sum over v ∈ A + B of |T_v| ≤ |S × S × S| = |S|^3.
  have hdisj : ((A + B : Finset G) : Set G).PairwiseDisjoint T := by
    intro v _ w _ hvw
    refine Finset.disjoint_filter.mpr ?_
    intro p _ hpv hpw
    exact hvw (hpv ▸ hpw)
  have hSubset : ∀ v ∈ A + B, T v ⊆ S ×ˢ S ×ˢ S := by
    intro v _ p hp
    exact (Finset.mem_filter.mp hp).1
  -- Σ_v |T_v| = | ⋃_v T_v | ≤ |S × S × S|.
  have hSumCard :
      ∑ v ∈ A + B, (T v).card = ((A + B).biUnion T).card := by
    rw [Finset.card_biUnion]
    intro v hv w hw hvw
    have hpw : ((A + B : Finset G) : Set G).PairwiseDisjoint T := hdisj
    have hv' : v ∈ ((A + B : Finset G) : Set G) := hv
    have hw' : w ∈ ((A + B : Finset G) : Set G) := hw
    exact hpw hv' hw' hvw
  have hSumLeS3 : ∑ v ∈ A + B, (T v).card ≤ (S ×ˢ S ×ˢ S).card := by
    rw [hSumCard]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, hv, hpv⟩ := hp
    exact hSubset v hv hpv
  -- Σ_v M ≤ Σ_v |T_v|.
  have hML : M * (A + B).card ≤ ∑ v ∈ A + B, (T v).card := by
    have hsum_le : ∑ _v ∈ A + B, M ≤ ∑ v ∈ A + B, (T v).card :=
      Finset.sum_le_sum (fun v hv ↦ hMle v hv)
    have hconst : ∑ _v ∈ A + B, M = (A + B).card * M := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [hconst, mul_comm] at hsum_le
    exact hsum_le
  -- Combine.
  have hCard_S3 : (S ×ˢ S ×ˢ S).card = S.card ^ 3 := by
    rw [Finset.card_product, Finset.card_product, pow_succ, pow_succ, pow_one]
    ring
  calc M * (A + B).card
      ≤ ∑ v ∈ A + B, (T v).card := hML
    _ ≤ (S ×ˢ S ×ˢ S).card := hSumLeS3
    _ = S.card ^ 3 := hCard_S3


/--
**Ruzsa sumset-to-difference adapter.** Given finite nonempty `A`, `B` in an
additive commutative group with `|A + B| ≤ K · |A|` and a balance assumption
`c · |A| ≤ |B|`, the difference set is bounded by
`|A − B| ≤ (K^3 / c) · |A|`.

Pipeline:
1. Plünnecke-Ruzsa (`Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add`)
   on `(A, B)` with `m = 2`, `n = 0` gives `|B + B| ≤ K^2 · |A|`.
2. Ruzsa triangle (`Finset.ruzsa_triangle_inequality_sub_add_add`) with
   second argument `B` yields `|A − B| · |B| ≤ |A + B| · |B + B|`.
3. Substituting `|A + B| ≤ K |A|` and `|B + B| ≤ K^2 |A|` gives
   `|A − B| · |B| ≤ K^3 · |A|^2`; the balance `c · |A| ≤ |B|` divides through
   to the linear conclusion.

The `c · |A| ≤ |B|` assumption is unavoidable in this generality (Ruzsa
triangle has `|B|` on the LHS). It is automatically satisfied where this is
applied below, because the subsets `A'`, `B'` produced by
`graph_balogSzemerediGowers_restricted_sumset` are both bounded below by a common `c · n` factor.
-/
lemma ruzsa_sumset_to_difference {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ K c : ℝ, 0 < K → 0 < c → ∀ A B : Finset G, A.Nonempty → B.Nonempty →
      ((A + B).card : ℝ) ≤ K * A.card →
      c * (A.card : ℝ) ≤ (B.card : ℝ) →
      ((A - B).card : ℝ) ≤ K ^ 3 / c * A.card := by
  intro K c hK hc A B hA hB hAB hcB
  -- Positivity facts
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hAne : (A.card : ℝ) ≠ 0 := ne_of_gt hApos
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  -- Step 1: Plünnecke-Ruzsa gives |B + B| ≤ K² · |A|.
  have hPR : ((2 • B).card : ℚ≥0)
      ≤ (((A + B).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) :=
    Finset.pluennecke_ruzsa_inequality_nsmul_add hA B 2
  have h2B : (2 : ℕ) • B = B + B := two_nsmul B
  rw [h2B] at hPR
  -- Cast hPR from ℚ≥0 to ℝ by first going to ℚ then to ℝ via NNRat.cast_divNat.
  have hPR_real : ((B + B).card : ℝ)
      ≤ (((A + B).card : ℝ) / (A.card : ℝ)) ^ 2 * (A.card : ℝ) := by
    have hQ : ((B + B).card : ℝ)
        ≤ ((((A + B).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) : ℝ) := by
      exact_mod_cast hPR
    simpa using hQ
  have hAB_div : ((A + B).card : ℝ) / (A.card : ℝ) ≤ K :=
    (div_le_iff₀ hApos).mpr hAB
  have hAB_div_nn : 0 ≤ ((A + B).card : ℝ) / (A.card : ℝ) :=
    div_nonneg (by positivity) (le_of_lt hApos)
  have hBB_le : ((B + B).card : ℝ) ≤ K ^ 2 * (A.card : ℝ) := by
    refine hPR_real.trans ?_
    have hsq : (((A + B).card : ℝ) / (A.card : ℝ)) ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ hAB_div_nn hAB_div 2
    exact mul_le_mul_of_nonneg_right hsq (le_of_lt hApos)
  -- Step 2: Ruzsa triangle: |A - B| · |B| ≤ |A + B| · |B + B|
  have hRTℕ : (A - B).card * B.card ≤ (A + B).card * (B + B).card :=
    Finset.ruzsa_triangle_inequality_sub_add_add A B B
  have hRT : ((A - B).card : ℝ) * (B.card : ℝ)
      ≤ ((A + B).card : ℝ) * ((B + B).card : ℝ) := by exact_mod_cast hRTℕ
  -- Step 3: chain bounds → |A-B| · |B| ≤ K³ · |A|²
  have hBBnn : 0 ≤ ((B + B).card : ℝ) := by positivity
  have hKA_nn : 0 ≤ K * (A.card : ℝ) := mul_nonneg (le_of_lt hK) (le_of_lt hApos)
  have hChain : ((A + B).card : ℝ) * ((B + B).card : ℝ)
      ≤ (K * A.card) * (K ^ 2 * A.card) :=
    mul_le_mul hAB hBB_le hBBnn hKA_nn
  have hKcube : (K * (A.card : ℝ)) * (K ^ 2 * A.card) = K ^ 3 * (A.card : ℝ) ^ 2 := by
    ring
  have hdiff_mul_B : ((A - B).card : ℝ) * (B.card : ℝ)
      ≤ K ^ 3 * (A.card : ℝ) ^ 2 := by
    rw [← hKcube]; exact hRT.trans hChain
  -- Step 4: use c · |A| ≤ |B| to replace |B| on the LHS
  have hdiff_nn : 0 ≤ ((A - B).card : ℝ) := by positivity
  have hdiff_mul_cA : ((A - B).card : ℝ) * (c * A.card)
      ≤ K ^ 3 * (A.card : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left hcB hdiff_nn).trans hdiff_mul_B
  -- Step 5: divide both sides by c · |A| > 0
  have hcA_pos : (0 : ℝ) < c * A.card := mul_pos hc hApos
  rw [show K ^ 3 / c * (A.card : ℝ) = K ^ 3 * (A.card : ℝ) ^ 2 / (c * A.card) by
        field_simp]
  rw [le_div_iff₀ hcA_pos]
  linarith [hdiff_mul_cA]


/-- **Length-3 path count lower bound (Cauchy-Schwarz on the bipartite graph).** For a bipartite
graph `E ⊆ A ×ˢ B` and `(a, b) ∈ A × B`, let
`P(a, b) := #{(b₁, a₁) ∈ B × A : (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E ∧ (a₁, b) ∈ E}` count length-3 paths
`a — b₁ — a₁ — b` in `E`. Then `Σ_{(a,b) ∈ A × B} P(a, b) ≥ |E|⁴ / (|A| · |B|)²`. The proof uses
Cauchy-Schwarz twice: once on row-degrees to get `Σ_a rowDeg(a)² ≥ |E|²/|A|`, then a sandwich
`S(b)² ≤ |B| · colDeg(b) · S(b)` (where `S(b) := Σ_{a:(a,b)∈E} rowDeg(a)`) followed by
Cauchy-Schwarz on `(Σ S)² ≤ |B| · Σ S²`. Reference: Tao–Vu, *Additive Combinatorics*, §6.4
(quantitative form of Corollary 6.20, "Paths of length three"). NOTE: currently unused by the BSG
proof (the live path obtains its pointwise — not averaged — path-3 bound from
`dense_bipartite_has_path3_rectangle` via dependent random choice). Retained as a self-contained,
general bipartite path-counting inequality — a potential mathlib contribution. Safe to delete if no
longer wanted. -/
lemma length_three_path_count_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B) :
    (E.card : ℝ) ^ 4 ≤ ((A.card : ℝ) * B.card) ^ 2 *
      ∑ p ∈ A ×ˢ B,
        (((B ×ˢ A).filter fun q : G × G ↦
          (p.1, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, p.2) ∈ E).card : ℝ) := by
  -- Trivial empty case.
  by_cases hAB : A = ∅ ∨ B = ∅
  · have hE0 : E = ∅ := by
      rcases hAB with hA | hB
      · subst hA
        refine Finset.subset_empty.mp ?_
        intro p hp; have := hE_sub hp; simp at this
      · subst hB
        refine Finset.subset_empty.mp ?_
        intro p hp; have := hE_sub hp; simp at this
    subst hE0
    simp
  push Not at hAB
  obtain ⟨hA_ne, hB_ne⟩ := hAB
  have hA_pos : 0 < A.card := Finset.card_pos.mpr hA_ne
  have hB_pos : 0 < B.card := Finset.card_pos.mpr hB_ne
  have hA_real : (0 : ℝ) < A.card := by exact_mod_cast hA_pos
  have hB_real : (0 : ℝ) < B.card := by exact_mod_cast hB_pos
  -- Real-valued edge indicator.
  set M : G → G → ℝ := fun a b ↦ if (a, b) ∈ E then 1 else 0 with hM_def
  have hM_nn : ∀ a b, 0 ≤ M a b := fun a b ↦ by
    simp only [M]; split_ifs <;> norm_num
  have hM_le_one : ∀ a b, M a b ≤ 1 := fun a b ↦ by
    simp only [M]; split_ifs <;> norm_num
  -- Row and column degrees as real sums of M.
  set r : G → ℝ := fun a ↦ ∑ b ∈ B, M a b with hr_def
  set c : G → ℝ := fun b ↦ ∑ a ∈ A, M a b with hc_def
  have hr_nn : ∀ a, 0 ≤ r a := fun a ↦ Finset.sum_nonneg fun b _ ↦ hM_nn a b
  have hc_nn : ∀ b, 0 ≤ c b := fun b ↦ Finset.sum_nonneg fun a _ ↦ hM_nn a b
  have hr_le_B : ∀ a, r a ≤ (B.card : ℝ) := fun a ↦ by
    simp only [r]
    calc ∑ b ∈ B, M a b ≤ ∑ _b ∈ B, (1 : ℝ) := Finset.sum_le_sum fun b _ ↦ hM_le_one a b
      _ = (B.card : ℝ) := by simp
  -- Σ_a r(a) = |E|.
  have hSum_AB_M : ∑ p ∈ A ×ˢ B, M p.1 p.2 = (E.card : ℝ) := by
    simp only [M]
    rw [← Finset.sum_filter]
    have heq : (A ×ˢ B).filter (fun p ↦ p ∈ E) = E := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hE_sub h, h⟩⟩
    rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hSum_r : ∑ a ∈ A, r a = (E.card : ℝ) := by
    simp only [r]
    rw [← Finset.sum_product']
    exact hSum_AB_M
  -- Cauchy-Schwarz: |E|² ≤ |A| · Σ_a r(a)².
  have hCS_row : (E.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ∑ a ∈ A, r a ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ : G ↦ (1 : ℝ)) r
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hSum_r] at h; exact h
  -- S(b) := Σ_a M(a, b) · r(a).
  set S : G → ℝ := fun b ↦ ∑ a ∈ A, M a b * r a with hS_def
  have hS_nn : ∀ b, 0 ≤ S b := fun b ↦
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (hM_nn a b) (hr_nn a)
  -- Σ_b S(b) = Σ_a r(a)².
  have hSumS_eq : ∑ b ∈ B, S b = ∑ a ∈ A, r a ^ 2 := by
    simp only [S]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_mul]
    have : ∑ b ∈ B, M a b = r a := rfl
    rw [this, sq]
  -- S(b) ≤ |B| · c(b).
  have hS_le : ∀ b, S b ≤ (B.card : ℝ) * c b := fun b ↦ by
    simp only [S]
    calc ∑ a ∈ A, M a b * r a
        ≤ ∑ a ∈ A, M a b * (B.card : ℝ) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hr_le_B a) (hM_nn a b)
      _ = (∑ a ∈ A, M a b) * (B.card : ℝ) := by rw [Finset.sum_mul]
      _ = c b * (B.card : ℝ) := rfl
      _ = (B.card : ℝ) * c b := mul_comm _ _
  -- T := Σ_{(a,b) ∈ A×B} P(a,b).
  set T : ℝ := ∑ p ∈ A ×ˢ B,
        (((B ×ˢ A).filter fun q : G × G ↦
          (p.1, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, p.2) ∈ E).card : ℝ) with hT_def
  -- T = Σ_b c(b) · S(b).
  -- We unfold T as a 4-fold sum over A × B × B × A, with summand
  --   M(a, b₁) · M(a₁, b₁) · M(a₁, b)
  -- and similarly for the RHS Σ_b c(b) · S(b).
  have hT_eq : T = ∑ b ∈ B, c b * S b := by
    -- Express T as a sum over A × B × (B × A) of indicator.
    -- Each P(a, b) = Σ_{(b₁, a₁) ∈ B × A} M(a, b₁) · M(a₁, b₁) · M(a₁, b).
    have hP : ∀ a b, (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) =
        ∑ q ∈ B ×ˢ A, M a q.1 * M q.2 q.1 * M q.2 b := by
      intro a b
      have hcard :
        ((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card =
          ∑ q ∈ B ×ˢ A,
            (if (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E then 1 else 0) := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      have hh : ((((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ) : ℝ) =
            ((∑ q ∈ B ×ˢ A,
              (if (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E then 1 else 0) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      push_cast at hh
      rw [hh]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp only [M]
      by_cases h1 : (a, q.1) ∈ E <;> by_cases h2 : (q.2, q.1) ∈ E <;>
        by_cases h3 : (q.2, b) ∈ E <;> simp [h1, h2, h3]
    -- T = Σ_{p ∈ A × B} Σ_{q ∈ B × A} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    --   = Σ_{p, q ∈ (A × B) × (B × A)} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    have hT_pair : T = ∑ p ∈ A ×ˢ B, ∑ q ∈ B ×ˢ A,
        M p.1 q.1 * M q.2 q.1 * M q.2 p.2 := by
      rw [hT_def]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      exact hP p.1 p.2
    -- Reorder: pull q outside.
    rw [hT_pair]
    rw [Finset.sum_comm]
    -- Now: Σ_{q ∈ B × A} Σ_{p ∈ A × B} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    -- Split inner: Σ_{p ∈ A × B} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    --   = M(q.2, q.1) · (Σ_{a ∈ A} M(a, q.1)) · (Σ_{b ∈ B} M(q.2, b))
    --   = M(q.2, q.1) · c(q.1) · r(q.2).
    have hinner : ∀ q : G × G, ∑ p ∈ A ×ˢ B, M p.1 q.1 * M q.2 q.1 * M q.2 p.2 =
        M q.2 q.1 * c q.1 * r q.2 := by
      intro q
      rw [Finset.sum_product]
      -- Σ_a Σ_b M(a, q.1) · M(q.2, q.1) · M(q.2, b)
      --   = M(q.2, q.1) · (Σ_a M(a, q.1)) · (Σ_b M(q.2, b))
      calc ∑ a ∈ A, ∑ b ∈ B, M a q.1 * M q.2 q.1 * M q.2 b
          = ∑ a ∈ A, M a q.1 * M q.2 q.1 * ∑ b ∈ B, M q.2 b := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← Finset.mul_sum]
        _ = ∑ a ∈ A, M a q.1 * M q.2 q.1 * r q.2 := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rfl
        _ = (∑ a ∈ A, M a q.1) * (M q.2 q.1 * r q.2) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            ring
        _ = c q.1 * (M q.2 q.1 * r q.2) := rfl
        _ = M q.2 q.1 * c q.1 * r q.2 := by ring
    simp_rw [hinner]
    -- Now: Σ_{q ∈ B × A} M(q.2, q.1) · c(q.1) · r(q.2).
    -- Split: Σ_{b₁ ∈ B} Σ_{a₁ ∈ A} M(a₁, b₁) · c(b₁) · r(a₁)
    --      = Σ_{b₁ ∈ B} c(b₁) · Σ_{a₁ ∈ A} M(a₁, b₁) · r(a₁)
    --      = Σ_{b₁ ∈ B} c(b₁) · S(b₁).
    rw [Finset.sum_product]
    -- Σ_{b₁ ∈ B} Σ_{a₁ ∈ A} M(a₁, b₁) · c(b₁) · r(a₁)
    refine Finset.sum_congr rfl fun b₁ _ ↦ ?_
    calc ∑ a₁ ∈ A, M a₁ b₁ * c b₁ * r a₁
        = c b₁ * ∑ a₁ ∈ A, M a₁ b₁ * r a₁ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a₁ _ ↦ ?_
          ring
      _ = c b₁ * S b₁ := rfl
  -- Now the inequality chain.
  -- Step A: T ≥ (1/|B|) · Σ_b S(b)².
  have hStepA : (1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2 ≤ T := by
    rw [hT_eq]
    rw [show (1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2 =
        ∑ b ∈ B, S b ^ 2 / (B.card : ℝ) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ ↦ ?_; ring]
    refine Finset.sum_le_sum fun b _ ↦ ?_
    have h1 : S b * S b ≤ (B.card : ℝ) * c b * S b :=
      mul_le_mul_of_nonneg_right (hS_le b) (hS_nn b)
    rw [div_le_iff₀ hB_real]
    calc S b ^ 2 = S b * S b := sq (S b)
      _ ≤ (B.card : ℝ) * c b * S b := h1
      _ = c b * S b * (B.card : ℝ) := by ring
  -- Step B: (Σ S)² ≤ |B| · Σ S².
  have hStepB : (∑ b ∈ B, S b) ^ 2 ≤ (B.card : ℝ) * ∑ b ∈ B, S b ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ : G ↦ (1 : ℝ)) S
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  -- Step C: |E|² ≤ |A| · Σ_b S(b).
  have hSumS_lb : (E.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ∑ b ∈ B, S b := by
    rw [hSumS_eq]; exact hCS_row
  -- Σ_b S² ≤ |B| · T from Step A.
  have hStepA_mul : ∑ b ∈ B, S b ^ 2 ≤ (B.card : ℝ) * T := by
    have h := hStepA
    have : (B.card : ℝ) * ((1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2) ≤ (B.card : ℝ) * T :=
      mul_le_mul_of_nonneg_left h (le_of_lt hB_real)
    rw [show (B.card : ℝ) * ((1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2) =
        ∑ b ∈ B, S b ^ 2 from by field_simp] at this
    exact this
  -- |E|⁴ ≤ |A|² · (Σ S)² ≤ |A|² · |B| · Σ S² ≤ |A|² · |B|² · T = (|A| · |B|)² · T.
  have hE2_nn : (0 : ℝ) ≤ (E.card : ℝ) ^ 2 := sq_nonneg _
  have hD : (E.card : ℝ) ^ 4 ≤ (A.card : ℝ) ^ 2 * (∑ b ∈ B, S b) ^ 2 := by
    have h := mul_self_le_mul_self hE2_nn hSumS_lb
    have heq1 : (E.card : ℝ) ^ 2 * (E.card : ℝ) ^ 2 = (E.card : ℝ) ^ 4 := by ring
    have heq2 : ((A.card : ℝ) * ∑ b ∈ B, S b) * ((A.card : ℝ) * ∑ b ∈ B, S b) =
        (A.card : ℝ) ^ 2 * (∑ b ∈ B, S b) ^ 2 := by ring
    rw [heq1, heq2] at h; exact h
  have hE_chain : (A.card : ℝ) ^ 2 * (∑ b ∈ B, S b) ^ 2 ≤
      (A.card : ℝ) ^ 2 * ((B.card : ℝ) * ∑ b ∈ B, S b ^ 2) :=
    mul_le_mul_of_nonneg_left hStepB (sq_nonneg _)
  have hF_chain : (A.card : ℝ) ^ 2 * ((B.card : ℝ) * ∑ b ∈ B, S b ^ 2) ≤
      ((A.card : ℝ) * (B.card : ℝ)) ^ 2 * T := by
    have hAB_sq_nn : (0 : ℝ) ≤ (A.card : ℝ) ^ 2 * (B.card : ℝ) :=
      mul_nonneg (sq_nonneg _) (le_of_lt hB_real)
    calc (A.card : ℝ) ^ 2 * ((B.card : ℝ) * ∑ b ∈ B, S b ^ 2)
        = ((A.card : ℝ) ^ 2 * (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2 := by ring
      _ ≤ ((A.card : ℝ) ^ 2 * (B.card : ℝ)) * ((B.card : ℝ) * T) :=
          mul_le_mul_of_nonneg_left hStepA_mul hAB_sq_nn
      _ = ((A.card : ℝ) * (B.card : ℝ)) ^ 2 * T := by ring
  linarith


/--
**DRC step (Fox-Sudakov Lemma 5.1, "pair DRC").** For a bipartite graph
`F ⊆ X × Y` of density `c := |F| / (|X| · |Y|)` and any `0 < ε ≤ 1`, there
exists `U ⊆ X` such that
* `(c / 2) |X| ≤ |U|`, AND
* the number of ordered pairs `(x, x') ∈ U × U` with codegree
  `|N(x) ∩ N(x')| < (ε c² / 2) |Y|` is at most `ε |U|²`.

Proof (random choice): pick `v ∈ Y` uniformly and set `U := N(v) ⊆ X`. The
indicator `|U|² = (Σ_x [v ∈ N(x)])²` has expectation `≥ (E|U|)² = c² |X|²` by
Cauchy-Schwarz. For "bad" ordered pairs `(x, x')` with codegree
`< (ε c² / 2) |Y|`, the probability `P(v ∈ N(x) ∩ N(x'))` is `< ε c² / 2`, so
the expected number `Z` of bad pairs inside `U² ` is `< (ε c² / 2) |X|²`.
Hence `E[|U|² − Z/ε] ≥ (c² / 2) |X|²`, and there is a choice of `v` realizing
`|U|² ≥ (c² / 2) |X|²` (so `|U| ≥ (c / √2) |X| ≥ (c/2)|X|`) and
`Z ≤ ε |U|²`. Reference: Fox-Sudakov 2011, Lemma 5.1.
-/
lemma graph_pair_dependentRandomChoice {G : Type*} [DecidableEq G]
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty)
    (F : Finset (G × G)) (hF_sub : F ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (_hc_le : c ≤ 1)
    (hF_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (F.card : ℝ))
    (ε : ℝ) (hε_pos : 0 < ε) (_hε_le : ε ≤ 1) :
    ∃ U : Finset G, U ⊆ X ∧
      (c / 2) * (X.card : ℝ) ≤ (U.card : ℝ) ∧
      (((U ×ˢ U).filter fun p : G × G ↦
        (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
          (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
        (ε * c ^ 2 / 2) * (Y.card : ℝ)).card : ℝ) ≤
      ε * (U.card : ℝ) ^ 2 := by
  have hX_real_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hY_real_pos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hX_nn : (0 : ℝ) ≤ (X.card : ℝ) := le_of_lt hX_real_pos
  have hY_nn : (0 : ℝ) ≤ (Y.card : ℝ) := le_of_lt hY_real_pos
  -- `U(v) := { x ∈ X : (x, v) ∈ F }`.
  set U : G → Finset G := fun v ↦ X.filter (fun x ↦ (x, v) ∈ F) with hU_def
  -- "Bad" ordered pairs in `X × X` (independent of `v`).
  set Bad : Finset (G × G) := (X ×ˢ X).filter fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
    (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBad_def
  -- The bad-in-U(v) finset is the restriction of `Bad` to `U(v) × U(v)`.
  set BadInV : G → Finset (G × G) := fun v ↦
    (U v ×ˢ U v).filter fun p : G × G ↦
      (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
        (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
      (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBadInV_def
  -- Step 1: Σ_v |U(v)| = |F|.
  have hSum_U_card : ∑ v ∈ Y, ((U v).card : ℝ) = (F.card : ℝ) := by
    have hF_filter : F = (X ×ˢ Y).filter (fun p : G × G ↦ p ∈ F) := by
      ext p
      refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
      · exact Finset.mem_filter.mpr ⟨hF_sub hp, hp⟩
      · exact (Finset.mem_filter.mp hp).2
    have hF_card_eq : (F.card : ℝ) = ∑ v ∈ Y, ((U v).card : ℝ) := by
      conv_lhs => rw [hF_filter]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
      push_cast
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [U, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    linarith
  -- Step 2: Σ_v |U(v)|² = Σ_{(x,x') ∈ X × X} codeg(x, x').
  set codeg : G × G → ℝ := fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) with hcodeg_def
  have hcodeg_nn : ∀ p, 0 ≤ codeg p := fun p ↦ Nat.cast_nonneg _
  have hSum_U_sq : ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 = ∑ p ∈ X ×ˢ X, codeg p := by
    have hStep : ∀ v ∈ Y,
        ((U v).card : ℝ) ^ 2 = ((U v ×ˢ U v).card : ℝ) := by
      intro v _
      rw [Finset.card_product]
      push_cast; ring
    rw [Finset.sum_congr rfl hStep]
    -- Σ_v |U(v) × U(v)| = Σ_v #{(x, x') ∈ X × X : (x, v) ∈ F ∧ (x', v) ∈ F}.
    have hStep2 : ∀ v ∈ Y, ((U v ×ˢ U v).card : ℝ) =
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ) := by
      intro v _
      have hSet : U v ×ˢ U v =
          (X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
        ext p
        simp only [Finset.mem_product, Finset.mem_filter, U]
        tauto
      rw [hSet]
    rw [Finset.sum_congr rfl hStep2]
    -- Swap sums: Σ_v #{(x,x'): (x,v)∈F ∧ (x',v)∈F} = Σ_{(x,x')} codeg(x,x').
    rw [show (∑ v ∈ Y,
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ)) =
        ∑ v ∈ Y, ∑ p ∈ X ×ˢ X,
          (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    -- codeg(p) = #{v ∈ Y : (p.1, v) ∈ F ∧ (p.2, v) ∈ F}.
    have hcodeg_eq : codeg p =
        ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
      simp only [codeg]
      rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
          = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
        ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl
    rw [hcodeg_eq]
  -- Step 3: Cauchy-Schwarz: |F|² ≤ |Y| · Σ_v |U(v)|².
  have hCS : (F.card : ℝ) ^ 2 ≤ (Y.card : ℝ) * ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ : G ↦ (1 : ℝ))
      (fun v ↦ ((U v).card : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hSum_U_card] at h
    exact h
  -- Step 4: c²|X|²|Y| ≤ Σ_v |U(v)|².
  have hSum_U_sq_lb : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤
      ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have hF_dense_nn : 0 ≤ c * (X.card : ℝ) * (Y.card : ℝ) :=
      mul_nonneg (mul_nonneg hc_nn hX_nn) hY_nn
    have hF_sq : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 ≤ (F.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ hF_dense_nn hF_dense 2
    have hY_pos : 0 < (Y.card : ℝ) := hY_real_pos
    have h := le_trans hF_sq hCS
    have hrw : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 =
        (Y.card : ℝ) * (c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) := by ring
    rw [hrw] at h
    exact le_of_mul_le_mul_left h hY_pos
  -- Step 5: Σ_v |BadInV(v)| ≤ (ε c² / 2) |X|² |Y|.
  -- For each bad pair (x, x'), the number of v ∈ Y with x, x' ∈ U(v) equals
  -- codeg(x, x') ≤ (ε c² / 2)|Y|.
  have hSum_BadInV_le : ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
      (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
    -- Σ_v |BadInV(v)| = Σ_{p ∈ Bad} codeg(p).
    have hSwap : ∑ v ∈ Y, ((BadInV v).card : ℝ) = ∑ p ∈ Bad, codeg p := by
      -- Σ_v #{(x,x') ∈ U(v)² : p ∈ Bad}.
      have hStep : ∀ v ∈ Y, ((BadInV v).card : ℝ) =
          ∑ p ∈ Bad, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        intro v _
        -- BadInV(v) = Bad.filter (p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F).
        have hBadInV_eq : BadInV v =
            Bad.filter (fun p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
          ext p
          simp only [BadInV, Bad, Finset.mem_filter, Finset.mem_product, U,
            Finset.mem_filter]
          tauto
        rw [hBadInV_eq, Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [Finset.sum_congr rfl hStep]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hcodeg_eq : codeg p =
          ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        simp only [codeg]
        rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
            = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
          ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [hcodeg_eq]
    rw [hSwap]
    -- Σ_{p ∈ Bad} codeg(p) ≤ |Bad| · (εc²/2)|Y| ≤ |X|² · (εc²/2)|Y|.
    have hBad_sub : Bad ⊆ X ×ˢ X := Finset.filter_subset _ _
    have hBad_card_le : (Bad.card : ℝ) ≤ ((X ×ˢ X).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hBad_sub
    have hXX_card : ((X ×ˢ X).card : ℝ) = (X.card : ℝ) ^ 2 := by
      rw [Finset.card_product]; push_cast; ring
    have hBad_card_le_X_sq : (Bad.card : ℝ) ≤ (X.card : ℝ) ^ 2 := by
      rw [← hXX_card]; exact hBad_card_le
    have hτ_nn : 0 ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by positivity
    have hPointwise : ∀ p ∈ Bad, codeg p ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by
      intro p hp
      simp only [Bad, Finset.mem_filter] at hp
      exact le_of_lt hp.2
    calc ∑ p ∈ Bad, codeg p
        ≤ ∑ _p ∈ Bad, (ε * c ^ 2 / 2) * (Y.card : ℝ) :=
          Finset.sum_le_sum hPointwise
      _ = (Bad.card : ℝ) * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X.card : ℝ) ^ 2 * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hBad_card_le_X_sq hτ_nn
      _ = (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by ring
  -- Step 6: Σ_v Φ(v) ≥ (c² / 2) |X|² |Y|, where Φ(v) = |U(v)|² − (1/ε) |BadInV(v)|.
  set Φ : G → ℝ := fun v ↦
    ((U v).card : ℝ) ^ 2 - (1 / ε) * ((BadInV v).card : ℝ) with hΦ_def
  have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε_pos
  have hε_inv_nn : (0 : ℝ) ≤ 1 / ε := le_of_lt hε_inv_pos
  have hSum_Φ_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, Φ v := by
    have hSplit : ∑ v ∈ Y, Φ v =
        (∑ v ∈ Y, ((U v).card : ℝ) ^ 2) - (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) := by
      simp only [Φ]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hSplit]
    have h1 : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 :=
      hSum_U_sq_lb
    have h2 : (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
        (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hSum_BadInV_le hε_inv_nn
    have h2' : (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) =
        (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
      field_simp
    rw [h2'] at h2
    linarith
  -- Step 7: Extract a `v` with Φ(v) ≥ (c²/2)|X|².
  have hSum_Φ_const : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) =
      ∑ _v ∈ Y, (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hSum_Φ_const] at hSum_Φ_lb
  obtain ⟨v, _hvY, hΦv⟩ := Finset.exists_le_of_sum_le hY hSum_Φ_lb
  -- Step 8: For this `v`, derive |U(v)| ≥ (c/2)|X| and |BadInV(v)| ≤ ε|U(v)|².
  -- From hΦv : (c²/2)|X|² ≤ |U(v)|² - (1/ε)|BadInV(v)|.
  -- Since |BadInV(v)| ≥ 0, |U(v)|² ≥ (c²/2)|X|² ≥ (c/2)²|X|² (because c ≤ 1).
  have hU_card_nn : (0 : ℝ) ≤ ((U v).card : ℝ) := Nat.cast_nonneg _
  have hBadInV_nn : (0 : ℝ) ≤ ((BadInV v).card : ℝ) := Nat.cast_nonneg _
  have hU_sq_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≥ 0 :=
      mul_nonneg hε_inv_nn hBadInV_nn
    linarith
  have hc_sq_half_ge_c_half_sq : (c / 2) ^ 2 ≤ c ^ 2 / 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have : (c / 2) ^ 2 = c ^ 2 / 4 := by ring
    rw [this]
    -- c²/4 ≤ c²/2 ↔ c² ≥ 0.
    nlinarith [sq_nonneg c]
  have hU_card_lb : (c / 2) * (X.card : ℝ) ≤ ((U v).card : ℝ) := by
    have hc_half_X_nn : (0 : ℝ) ≤ (c / 2) * (X.card : ℝ) :=
      mul_nonneg (by linarith) hX_nn
    have hsq_chain : ((c / 2) * (X.card : ℝ)) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
      calc ((c / 2) * (X.card : ℝ)) ^ 2
          = (c / 2) ^ 2 * (X.card : ℝ) ^ 2 := by ring
        _ ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hc_sq_half_ge_c_half_sq (sq_nonneg _)
        _ ≤ ((U v).card : ℝ) ^ 2 := hU_sq_lb
    have hsqrt := Real.sqrt_le_sqrt hsq_chain
    rwa [Real.sqrt_sq hc_half_X_nn, Real.sqrt_sq hU_card_nn] at hsqrt
  -- |BadInV(v)| ≤ ε |U(v)|².
  have hBadInV_le : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
    -- From hΦv: (c²/2)|X|² ≤ |U(v)|² − (1/ε)|BadInV(v)|.
    -- So (1/ε)|BadInV(v)| ≤ |U(v)|² − (c²/2)|X|² ≤ |U(v)|².
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≤ ((U v).card : ℝ) ^ 2 := by
      have hX_sq_nn : 0 ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by positivity
      linarith
    have h2 : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hε_pos)
      have heq : ε * ((1 / ε) * ((BadInV v).card : ℝ)) = ((BadInV v).card : ℝ) := by
        field_simp
      rw [heq] at this
      exact this
    exact h2
  -- Step 9: Package the witness.
  refine ⟨U v, ?_, hU_card_lb, ?_⟩
  · simp only [U]; exact Finset.filter_subset _ _
  · exact hBadInV_le


/--
**High-degree subset density.** For `E ⊆ A ×ˢ B` with `|A| = |B| = n` and
`δ n² ≤ |E|`, the subset `A₁ := { a ∈ A : (δ/2) n ≤ |Nb(a)| }` has
`(δ/2) n ≤ |A₁|` and `e(A₁, B) ≥ (δ/2) n²` (where `e(A₁, B) := |E ∩ (A₁ ×ˢ B)|`).

Standard rare/popular split: rows with `|Nb(a)| < (δ/2) n` contribute
`< (δ/2) n²` edges, so the popular rows in `A₁` contribute `≥ (δ/2) n²`.
Combined with the pointwise bound `|Nb(a)| ≤ n` on `A₁`, this gives
`|A₁| · n ≥ (δ/2) n²`, i.e. `|A₁| ≥ (δ/2) n`.
-/
lemma graph_high_degree_subset_lb {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    (δ / 2) * (A.card : ℝ) ≤
      ((A.filter (fun a ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ))).card : ℝ) ∧
    (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤
      ((E.filter (fun p : G × G ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))).card : ℝ) := by
  classical
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  set Apop : Finset G := A.filter (fun a ↦ (δ / 2) * (B.card : ℝ) ≤ (rowDeg a : ℝ))
    with hApop_def
  set Epop : Finset (G × G) := E.filter (fun p : G × G ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))
    with hEpop_def
  have hApop_sub : Apop ⊆ A := Finset.filter_subset _ _
  have hEpop_sub : Epop ⊆ E := Finset.filter_subset _ _
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_pos
  have hBcard_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hAB.symm
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hBcard_eq]; exact hA_pos
  have hB_nn : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_pos
  have hrowDeg_le : ∀ a, rowDeg a ≤ B.card := fun a ↦
    Finset.card_le_card (Finset.filter_subset _ _)
  have hrowDeg_le_R : ∀ a, (rowDeg a : ℝ) ≤ (B.card : ℝ) := fun a ↦ by
    exact_mod_cast hrowDeg_le a
  have hSumRow : ∑ a ∈ A, (rowDeg a : ℕ) = E.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ A, rowDeg a = ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 :
        ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) = ((A ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (A ×ˢ B).filter (· ∈ E) = E := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hE_sub h, h⟩⟩
    rw [step2, step3, step4]
  have hSumRow_real : ∑ a ∈ A, (rowDeg a : ℝ) = (E.card : ℝ) := by
    have h := hSumRow
    have hcast : ((∑ a ∈ A, rowDeg a : ℕ) : ℝ) = (E.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hsplit_A : ∑ a ∈ A, (rowDeg a : ℝ) =
      (∑ a ∈ Apop, (rowDeg a : ℝ)) + ∑ a ∈ A \ Apop, (rowDeg a : ℝ) := by
    rw [← Finset.sum_sdiff hApop_sub]; ring
  have hrare : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤
      ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    rw [show ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) =
              ∑ _a ∈ A \ Apop, ((δ / 2) * (B.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hApop_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨ha.1, le_of_lt hgt⟩
  have hAdiff_le_A : ((A \ Apop).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := A) (t := Apop))
  have hδ2B_nn : 0 ≤ (δ / 2) * (B.card : ℝ) := by positivity
  have hrare' : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤ (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hAdiff_le_A hδ2B_nn
    linarith [hrare]
  have hSumApop : ∑ a ∈ Apop, (rowDeg a : ℕ) = Epop.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ Apop, rowDeg a = ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 : ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) =
        ((Apop ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (Apop ×ˢ B).filter (· ∈ E) = Epop := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, hEpop_def, hApop_def, hrowDeg_def]
      constructor
      · rintro ⟨⟨⟨hp1A, hp1pop⟩, _hp2⟩, hpE⟩
        exact ⟨hpE, hp1pop⟩
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨⟨⟨hpAB.1, hpop⟩, hpAB.2⟩, hpE⟩
    rw [step2, step3, step4]
  have hSumApop_real : ∑ a ∈ Apop, (rowDeg a : ℝ) = (Epop.card : ℝ) := by
    have h := hSumApop
    have hcast : ((∑ a ∈ Apop, rowDeg a : ℕ) : ℝ) = (Epop.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hE_dense' : δ * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ A, (rowDeg a : ℝ) := by
    rw [hSumRow_real]; exact hE_dense
  have hEpop_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Epop.card : ℝ) := by
    have : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ Apop, (rowDeg a : ℝ) := by
      have hδ_split : δ * (A.card : ℝ) * (B.card : ℝ) =
          (δ / 2) * (A.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
        ring
      linarith [hE_dense', hsplit_A, hrare', hδ_split]
    linarith [this, hSumApop_real]
  have hApop_sum_ub : ∑ a ∈ Apop, (rowDeg a : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
    rw [show (Apop.card : ℝ) * (B.card : ℝ) = ∑ _a ∈ Apop, (B.card : ℝ) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a _ ↦ hrowDeg_le_R a
  have hApop_lb : (δ / 2) * (A.card : ℝ) ≤ (Apop.card : ℝ) := by
    have h1 : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
      calc (δ / 2) * (A.card : ℝ) * (B.card : ℝ)
          ≤ (Epop.card : ℝ) := hEpop_lb
        _ = ∑ a ∈ Apop, (rowDeg a : ℝ) := hSumApop_real.symm
        _ ≤ (Apop.card : ℝ) * (B.card : ℝ) := hApop_sum_ub
    exact le_of_mul_le_mul_right h1 hB_pos
  exact ⟨hApop_lb, hEpop_lb⟩


/--
**Markov refinement helper.** Given `U` and a bad-pair count bound
`#{(a, a') ∈ U×U : codeg_E(a, a') < τ} ≤ κ · |U|²`, produce
`A' ⊆ U` with `|A'| ≥ |U|/2` (when `κ ≤ 1/4`) such that for every
`a ∈ A'` the bad-partner count `#{a' ∈ U : codeg_E(a, a') < τ}` is
`≤ 2κ · |U|`.  Used inside `graph_dependentRandomChoice_payoff_pointwise_witness` with
`κ := δ/16`, giving `2κ = δ/8`.
-/
private lemma graph_dependentRandomChoice_markov_refinement {G : Type*} [DecidableEq G]
    (B U : Finset G) (E : Finset (G × G)) (τ : ℝ) (κ : ℝ)
    (hκ_pos : 0 < κ) (hUpos : (0 : ℝ) < (U.card : ℝ))
    (hbadCount : (((U ×ˢ U).filter fun p : G × G ↦
        ((B.filter fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
      ≤ κ * (U.card : ℝ) ^ 2) :
    ∃ A' : Finset G, A' ⊆ U ∧
      (1 - 1 / 2) * (U.card : ℝ) ≤ (A'.card : ℝ) ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ 2 * κ * (U.card : ℝ)) := by
  classical
  -- Bad partners of `a` in U.
  set badPartner : G → Finset G := fun a ↦
    U.filter (fun a₁ ↦
      ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPartner_def
  set A' : Finset G := U.filter (fun a ↦
    ((badPartner a).card : ℝ) ≤ 2 * κ * (U.card : ℝ)) with hA'_def
  have hA'_sub : A' ⊆ U := Finset.filter_subset _ _
  -- Sum of bad-partner cards equals bad-pair count (fiber over first coord).
  set badPairs : Finset (G × G) := (U ×ˢ U).filter (fun p : G × G ↦
    ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPairs_def
  have hbadSum : (badPairs.card : ℝ) = ∑ a ∈ U, ((badPartner a).card : ℝ) := by
    have hN : badPairs.card = ∑ a ∈ U, (badPartner a).card := by
      rw [hbadPairs_def, hbadPartner_def]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcast : ((∑ a ∈ U, (badPartner a).card : ℕ) : ℝ) = (badPairs.card : ℝ) := by
      exact_mod_cast hN.symm
    push_cast at hcast; linarith
  -- Markov lower bound on Σ over U \ A'.
  have hsum_split :
      ∑ a ∈ U, ((badPartner a).card : ℝ) =
        (∑ a ∈ A', ((badPartner a).card : ℝ)) +
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [← Finset.sum_sdiff hA'_sub]; ring
  have hsum_diff_ge :
      ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [show ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) =
            ∑ _a ∈ U \ A', (2 * κ * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hA'_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hge
    push Not at hge
    exact hnot ⟨ha.1, le_of_lt hge⟩
  have hpartner_nn : ∀ a, 0 ≤ ((badPartner a).card : ℝ) := fun a ↦ Nat.cast_nonneg _
  have hsum_A'_nn : 0 ≤ ∑ a ∈ A', ((badPartner a).card : ℝ) :=
    Finset.sum_nonneg fun a _ ↦ hpartner_nn a
  -- Combine: |U\A'| · 2κ|U| ≤ Σ over U ≤ |badPairs| ≤ κ|U|².  Hence |U\A'| ≤ |U|/2.
  have hdiff_card_le : ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
      κ * (U.card : ℝ) ^ 2 := by
    calc ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ))
        ≤ ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := hsum_diff_ge
      _ ≤ ∑ a ∈ U, ((badPartner a).card : ℝ) := by linarith
      _ = (badPairs.card : ℝ) := hbadSum.symm
      _ ≤ κ * (U.card : ℝ) ^ 2 := hbadCount
  have hcoeff_pos : 0 < 2 * κ * (U.card : ℝ) := by positivity
  have hdiff_le_half : ((U \ A').card : ℝ) ≤ (U.card : ℝ) / 2 := by
    have heq : κ * (U.card : ℝ) ^ 2 = ((U.card : ℝ) / 2) * (2 * κ * (U.card : ℝ)) := by ring
    rw [heq] at hdiff_card_le
    exact le_of_mul_le_mul_right hdiff_card_le hcoeff_pos
  have hA'_card_real : ((U \ A').card : ℝ) + (A'.card : ℝ) = (U.card : ℝ) := by
    have h : (U \ A').card + A'.card = U.card := Finset.card_sdiff_add_card_eq_card hA'_sub
    exact_mod_cast h
  have hA'_lb : (U.card : ℝ) / 2 ≤ (A'.card : ℝ) := by linarith
  refine ⟨A', hA'_sub, ?_, ?_⟩
  · linarith
  · intro a ha
    rw [hA'_def, Finset.mem_filter] at ha
    exact ha.2

/--
**Popular columns helper.** For `U ⊆ A` with row degree `≥ ρ · |B|` for every
`a ∈ U` (in the sense of `|{b ∈ B : (a, b) ∈ E}| ≥ ρ · |B|`), the rare/popular
split on columns produces `B' ⊆ B` of cardinality `≥ (ρ/2) · |B|` such that
every `b ∈ B'` has `|{a ∈ U : (a, b) ∈ E}| ≥ (ρ/2) · |U|`.
-/
private lemma graph_dependentRandomChoice_popular_columns {G : Type*} [DecidableEq G]
    (A B : Finset G) (hAB : A.card = B.card)
    (E : Finset (G × G)) (_hE_sub : E ⊆ A ×ˢ B)
    (U : Finset G) (hU_sub : U ⊆ A)
    (hU_pos : (0 : ℝ) < (U.card : ℝ))
    (ρ : ℝ) (hρ_pos : 0 < ρ) (_hρ_le_one : ρ ≤ 1)
    (hrowDeg_lb : ∀ a ∈ U, ρ * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) :
    ∃ B' : Finset G, B' ⊆ B ∧
      (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
      (∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤
        ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ)) := by
  classical
  -- |B| > 0 since |B| = |A| and U ⊆ A nonempty.
  have hBcard_nat : B.card = A.card := hAB.symm
  have hUcard_le_A : (U.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hU_sub
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le hU_pos hUcard_le_A
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
    have : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
    rw [this]; exact hA_pos
  -- Column count.
  set colCount : G → ℕ := fun b ↦ (U.filter (fun a ↦ (a, b) ∈ E)).card with hcolCount_def
  set B' : Finset G := B.filter (fun b ↦ (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ)) with hB'_def
  have hB'_sub : B' ⊆ B := Finset.filter_subset _ _
  -- Edge count from U: Σ_a∈U rowDeg(a) ≥ ρ|U||B|.  Also = Σ_b colCount b.
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  -- Σ over U of rowDeg = Σ over B of colCount: both count {(a, b) ∈ U × B : (a, b) ∈ E}.
  have hSwap : ∑ a ∈ U, (rowDeg a : ℕ) = ∑ b ∈ B, (colCount b : ℕ) := by
    have hrowDeg_eq : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcolCount_eq : ∀ b, colCount b = ∑ a ∈ U, (if (a, b) ∈ E then 1 else 0) := fun b ↦ by
      simp only [colCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [hrowDeg_eq, hcolCount_eq]
    rw [Finset.sum_comm]
  have hSwap_real :
      ∑ a ∈ U, (rowDeg a : ℝ) = ∑ b ∈ B, (colCount b : ℝ) := by
    have : ((∑ a ∈ U, rowDeg a : ℕ) : ℝ) = ((∑ b ∈ B, colCount b : ℕ) : ℝ) := by
      exact_mod_cast hSwap
    push_cast at this; exact this
  -- Σ_{a ∈ U} rowDeg(a) ≥ ρ|U||B|.
  have hrow_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) := by
    have hsum : ∑ _a ∈ U, ρ * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) :=
      Finset.sum_le_sum fun a haU ↦ hrowDeg_lb a haU
    have hconst : ∑ _a ∈ U, ρ * (B.card : ℝ) = (U.card : ℝ) * (ρ * (B.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst] at hsum
    linarith
  have hcol_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ b ∈ B, (colCount b : ℝ) := by
    rw [← hSwap_real]; exact hrow_sum_lb
  -- Rare columns contribute < (ρ/2)|U| each.
  have hrare_col : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    rw [show ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) =
            ∑ _b ∈ B \ B', ((ρ / 2) * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun b hb ↦ ?_
    rw [Finset.mem_sdiff, hB'_def, Finset.mem_filter] at hb
    have hnot := hb.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨hb.1, le_of_lt hgt⟩
  have hrare_col' : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      (B.card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    have h : ((B \ B').card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := B) (t := B'))
    have hnn : 0 ≤ (ρ / 2) * (U.card : ℝ) := by
      have : 0 ≤ ρ / 2 := by linarith
      exact mul_nonneg this (le_of_lt hU_pos)
    have := mul_le_mul_of_nonneg_right h hnn
    linarith
  -- Split column-sum.
  have hcol_split : ∑ b ∈ B, (colCount b : ℝ) =
      (∑ b ∈ B', (colCount b : ℝ)) + ∑ b ∈ B \ B', (colCount b : ℝ) := by
    rw [← Finset.sum_sdiff hB'_sub]; ring
  have hpop_col_lb : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
      ∑ b ∈ B', (colCount b : ℝ) := by
    nlinarith [hcol_split, hcol_sum_lb, hrare_col']
  -- Σ over B' of colCount ≤ |B'| · |U|.
  have hcolCount_le : ∀ b, (colCount b : ℝ) ≤ (U.card : ℝ) := fun b ↦ by
    have h : (colCount b : ℕ) ≤ U.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast h
  have hpop_col_ub : ∑ b ∈ B', (colCount b : ℝ) ≤ (B'.card : ℝ) * (U.card : ℝ) := by
    rw [show (B'.card : ℝ) * (U.card : ℝ) = ∑ _b ∈ B', (U.card : ℝ) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum fun b _ ↦ hcolCount_le b
  -- Divide through by |U|.
  have hB'_lb : (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) := by
    have hchain : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
        (B'.card : ℝ) * (U.card : ℝ) := le_trans hpop_col_lb hpop_col_ub
    have hrew : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) =
        ((ρ / 2) * (B.card : ℝ)) * (U.card : ℝ) := by ring
    rw [hrew] at hchain
    exact le_of_mul_le_mul_right hchain hU_pos
  have hpop_col_prop : ∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ) := by
    intro b hb
    rw [hB'_def, Finset.mem_filter] at hb
    exact hb.2
  exact ⟨B', hB'_sub, hB'_lb, hpop_col_prop⟩

/--
**Witness for the DRC pointwise payoff (steps 1-4).** Internal helper.
Composes `graph_high_degree_subset_lb` (rare/popular row split) with
`graph_pair_dependentRandomChoice` (Fox-Sudakov 5.1 pair-DRC) and a Markov + rare/popular
column split.  Returns the four pieces needed by the pointwise count
step: a "core" set `U ⊆ A`, the "non-bad" refinement `A' ⊆ U`, the
"popular column" refinement `B' ⊆ B`, and the codegree threshold
`τ ≥ 0` that interpolates the bad-partner bound for `a ∈ A'` and the
final `(δ⁵/2¹²)|A|²` count.

The arithmetic identity `(δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ` is established
here (using `m := |Apop|`-relative density and `|U| · τ`-style
cancellation) so the count helper need not redo it.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_witness {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ U A' B' : Finset G, ∃ τ : ℝ,
      U ⊆ A ∧ A' ⊆ U ∧ B' ⊆ B ∧
      0 ≤ τ ∧
      (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ (δ / 8) * (U.card : ℝ)) ∧
      (∀ b ∈ B',
        (δ / 4) * (U.card : ℝ) ≤
          ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ)) := by
  classical
  -- Cardinality positivity.
  have hApos : 0 < A.card := hA.card_pos
  have hA_real_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hApos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_real_pos
  have hBcard_nat : B.card = A.card := hAB.symm
  have hB_real_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
  have hB_real_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hB_real_eq]; exact hA_real_pos
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; rw [hBcard_nat]; exact hApos
  -- δ bounds.
  have hδ_nn : 0 ≤ δ := le_of_lt hδ_pos
  -- Step 1: apply rare/popular row split.
  obtain ⟨hApop_lb, hEpop_lb⟩ :=
    graph_high_degree_subset_lb δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  -- Define A₁ (popular rows) and E₁ (edges with popular first coord).
  set A₁ : Finset G := A.filter (fun a ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) with hA₁_def
  have hA₁_sub : A₁ ⊆ A := Finset.filter_subset _ _
  -- |A₁| ≥ (δ/2)|A| > 0, so A₁ is nonempty.
  have hA₁_card_pos : (0 : ℝ) < (A₁.card : ℝ) := by
    have : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    linarith
  have hA₁_card_pos_nat : 0 < A₁.card := by exact_mod_cast hA₁_card_pos
  have hA₁_ne : A₁.Nonempty := Finset.card_pos.mp hA₁_card_pos_nat
  set E₁ : Finset (G × G) := E.filter (fun p ↦ p.1 ∈ A₁) with hE₁_def
  have hE₁_sub_E : E₁ ⊆ E := Finset.filter_subset _ _
  -- E₁ characterisation: edges with first coord in A₁.
  have hE₁_iff : ∀ p, p ∈ E₁ ↔ p ∈ E ∧ p.1 ∈ A₁ := fun p ↦ by
    simp [E₁, Finset.mem_filter]
  -- E₁ ⊆ A₁ ×ˢ B.
  have hE₁_sub : E₁ ⊆ A₁ ×ˢ B := by
    intro p hp
    rw [hE₁_iff] at hp
    obtain ⟨hpE, hpA₁⟩ := hp
    have hpAB := hE_sub hpE
    rw [Finset.mem_product] at hpAB ⊢
    exact ⟨hpA₁, hpAB.2⟩
  -- The edge count for E₁: this matches the popular-edge form of `graph_high_degree_subset_lb`.
  -- |E₁| = |E.filter (popular first coord)| ≥ (δ/2)·|A|·|B|.
  have hE₁_card_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    -- The popular-edge filter from `graph_high_degree_subset_lb` matches E₁:
    --   E.filter (popular p.1) = E.filter (p.1 ∈ A₁)
    have hfilter_eq :
        E.filter (fun p : G × G ↦
          (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ)) = E₁ := by
      ext p
      simp only [E₁, Finset.mem_filter, hA₁_def]
      constructor
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨hpE, hpAB.1, hpop⟩
      · rintro ⟨hpE, _, hpop⟩
        exact ⟨hpE, hpop⟩
    rw [← hfilter_eq]; exact hEpop_lb
  -- Step 2: invoke graph_pair_dependentRandomChoice on (A₁, B, E₁) with density c₀ = (δ/2)|A|/|A₁|.
  set m : ℝ := (A₁.card : ℝ) with hm_def
  have hm_pos : 0 < m := hA₁_card_pos
  have hm_le_A : m ≤ (A.card : ℝ) := by
    have : (A₁.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA₁_sub
    exact this
  -- Density c₀ for pair-DRC: c₀ * m * |B| = (δ/2) * |A| * |B|.
  set c₀ : ℝ := (δ / 2) * (A.card : ℝ) / m with hc₀_def
  have hc₀_pos : 0 < c₀ := by
    have hnum : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    exact div_pos hnum hm_pos
  -- c₀ ≤ 1, because (δ/2)|A| ≤ m (= |A₁|).
  have hc₀_le_one : c₀ ≤ 1 := by
    rw [hc₀_def]
    rw [div_le_one hm_pos]
    exact hApop_lb
  -- c₀ * |A₁| = (δ/2) * |A|.
  have hc₀_mul_m : c₀ * m = (δ / 2) * (A.card : ℝ) := by
    rw [hc₀_def]; field_simp
  -- Density hypothesis for graph_pair_dependentRandomChoice.
  have hF_dense_drc : c₀ * (A₁.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    have : c₀ * (A₁.card : ℝ) * (B.card : ℝ) = (δ / 2) * (A.card : ℝ) * (B.card : ℝ) := by
      rw [show (A₁.card : ℝ) = m from rfl]; rw [hc₀_mul_m]
    rw [this]; exact hE₁_card_lb
  -- ε = δ/16.
  set ε : ℝ := δ / 16 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_le_one : ε ≤ 1 := by
    rw [hε_def]; linarith
  -- Invoke graph_pair_dependentRandomChoice.
  obtain ⟨U, hU_sub_A₁, hU_card_lb_drc, hbad_card_le⟩ :=
    graph_pair_dependentRandomChoice A₁ B hA₁_ne hB E₁ hE₁_sub c₀ hc₀_pos hc₀_le_one hF_dense_drc
      ε hε_pos hε_le_one
  have hU_sub : U ⊆ A := hU_sub_A₁.trans hA₁_sub
  -- (c₀/2) * |A₁| = (δ/4) * |A|.
  have hU_card_lb : (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) := by
    have heq : c₀ / 2 * (A₁.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      have := hc₀_mul_m
      rw [show (A₁.card : ℝ) = m from rfl]
      linarith
    linarith [hU_card_lb_drc, heq]
  have hU_card_pos : (0 : ℝ) < (U.card : ℝ) := by
    have : 0 < (δ / 4) * (A.card : ℝ) := by positivity
    linarith
  have hU_card_pos_nat : 0 < U.card := by exact_mod_cast hU_card_pos
  have hU_ne : U.Nonempty := Finset.card_pos.mp hU_card_pos_nat
  -- τ_drc = (ε * c₀²/2) * |B|.  Goal `τ := τ_drc`.
  set τ : ℝ := (ε * c₀ ^ 2 / 2) * (B.card : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by
    rw [hτ_def]
    have h1 : 0 ≤ ε * c₀ ^ 2 / 2 := by positivity
    have h2 : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_real_pos
    exact mul_nonneg h1 h2
  -- The arithmetic identity: (δ⁵/2¹²)|A|² ≤ (δ/8) · |U| · τ.
  -- We use: (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A|, and τ ≥ ?
  -- Key: τ = (δ/16)·c₀²/2·|B| = (δ/32)·c₀²·|A|.
  -- And c₀² · |A₁|² = (δ/2)² · |A|², so c₀² = δ²|A|²/(4·m²).
  -- Hence τ · m² = (δ/32) · (δ²/4) · |A|³ = δ³|A|³/128.
  -- Want: (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  -- Using |U| ≥ (δ/4)|A| and τ ≥ (δ³/2⁷)|A| (since m ≤ |A|, so |A|³/m² ≥ |A|).
  have hτ_lb : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) ≤ τ := by
    -- τ = (δ/16) · c₀² / 2 · |B| = (δ/32) · c₀² · |A|.
    -- c₀ · m = (δ/2)|A|, so c₀² · m² = δ²|A|²/4.
    -- τ · m² = (δ/32) · δ²|A|²/4 · |A| = δ³|A|³/128.
    -- τ = δ³|A|³ / (128 m²).  Since m ≤ |A|: τ ≥ δ³|A|/128.
    have hc₀sq : c₀ ^ 2 * m ^ 2 = ((δ / 2) * (A.card : ℝ)) ^ 2 := by
      have h := hc₀_mul_m
      calc c₀ ^ 2 * m ^ 2 = (c₀ * m) ^ 2 := by ring
        _ = ((δ / 2) * (A.card : ℝ)) ^ 2 := by rw [h]
    have hm_sq_pos : 0 < m ^ 2 := by positivity
    have hm_sq_le : m ^ 2 ≤ (A.card : ℝ) ^ 2 := by
      have hm_nn : 0 ≤ m := le_of_lt hm_pos
      exact pow_le_pow_left₀ hm_nn hm_le_A 2
    -- τ * m² = (ε * c₀²/2) * |B| * m² = (ε / 2) * (c₀² · m²) * |B|
    --        = (δ / 32) * ((δ/2)|A|)² * |A| = δ³|A|³/128.
    have hτ_m_sq : τ * m ^ 2 = δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by
      have : τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ) := hτ_def
      rw [this, hB_real_eq, hε_def]
      have : (δ / 16 * c₀ ^ 2 / 2) * (A.card : ℝ) * m ^ 2
          = (δ / 32) * (c₀ ^ 2 * m ^ 2) * (A.card : ℝ) := by ring
      rw [this, hc₀sq]
      ring
    -- (δ³/2⁷)|A| · m² ≤ τ · m² ↔ (δ³/2⁷)|A| ≤ τ if m² > 0.
    -- Use (δ³/2⁷)|A| · m² ≤ (δ³/2⁷)|A| · |A|² = (δ³/128)|A|³ = τ · m².
    have hineq : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤ τ * m ^ 2 := by
      rw [hτ_m_sq]
      have : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤
            (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 := by
        have hLcoeff_nn : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hm_sq_le hLcoeff_nn
      have heq2 : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 =
          δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by ring
      linarith
    exact le_of_mul_le_mul_right hineq hm_sq_pos
  -- Now establish the bound (δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ via
  -- (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A| and τ ≥ δ³/128 · |A|, product ≥ δ⁵|A|²/2¹².
  have hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ := by
    have h1 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) ≤ (δ / 8) * (U.card : ℝ) := by
      have h8 : (0 : ℝ) ≤ δ / 8 := by linarith
      exact mul_le_mul_of_nonneg_left hU_card_lb h8
    have h2 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) ≤
        (δ / 8) * (U.card : ℝ) * τ := by
      have hLHS_nn : 0 ≤ (δ / 8) * ((δ / 4) * (A.card : ℝ)) := by positivity
      have hLHS_nn' : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
      exact mul_le_mul h1 hτ_lb hLHS_nn' (le_trans hLHS_nn h1)
    have hrew : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) =
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 := by ring
    linarith
  -- Bad-pair count in U using the E-codegree.  It is bounded by the E₁-bad count from
  -- graph_pair_dependentRandomChoice, since codeg_E ≥ codeg_{E₁}.
  have hbadCountE : (((U ×ˢ U).filter fun p : G × G ↦
      ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ)
    ≤ ε * (U.card : ℝ) ^ 2 := by
    -- Pointwise: codeg_E(p) < τ ⟹ codeg_{E₁}(p) ≤ codeg_E(p) < τ.
    have hbadE_sub : ((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ) ⊆
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have hsub : (B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
                  (B.filter (fun y ↦ (p.2, y) ∈ E₁)) ⊆
                  B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E) := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_filter] at hy
        simp only [Finset.mem_filter]
        exact ⟨hy.1.1, hE₁_sub_E hy.1.2, hE₁_sub_E hy.2.2⟩
      have hcard : (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
          (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) ≤
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [hp.2]
    have h := Finset.card_le_card hbadE_sub
    have hreal : (((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ) ≤
        (((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ).card : ℝ) := by
      exact_mod_cast h
    -- `τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ)` by definition; substitute.
    have hfilter_eq :
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) =
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) <
          (ε * c₀ ^ 2 / 2) * (B.card : ℝ)) := by rfl
    rw [hfilter_eq] at hreal
    linarith
  -- Apply Markov refinement helper.
  obtain ⟨A', hA'_sub_U, hA'_half, hA'_prop⟩ :=
    graph_dependentRandomChoice_markov_refinement (G := G) B U E τ ε hε_pos hU_card_pos hbadCountE
  -- `hA'_half`: (1 - 1/2) * |U| ≤ |A'|, i.e. |U|/2 ≤ |A'|.
  -- `hA'_prop`: ∀ a ∈ A', ((badPartner a).card : ℝ) ≤ 2ε|U| = (δ/8)|U|.
  -- So we get the (δ/8)|U| bound directly: 2 * (δ/16) = δ/8.
  have htwo_eps : (2 : ℝ) * ε = δ / 8 := by rw [hε_def]; ring
  have hA'_prop_clean : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ) := by
    intro a ha
    have h := hA'_prop a ha
    have hrew : (2 * ε * (U.card : ℝ)) = (δ / 8) * (U.card : ℝ) := by
      rw [show (2 * ε * (U.card : ℝ)) = 2 * ε * (U.card : ℝ) from rfl, htwo_eps]
    linarith [hrew]
  -- |A'| ≥ |U|/2 ≥ (δ/8)|A|.
  have hA'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) := by
    have h1 : (δ / 8) * (A.card : ℝ) ≤ (U.card : ℝ) / 2 := by linarith [hU_card_lb]
    have : (1 - 1 / 2) * (U.card : ℝ) = (U.card : ℝ) / 2 := by ring
    linarith [hA'_half, this]
  -- Step 4: popular columns via `graph_dependentRandomChoice_popular_columns`.
  -- Row-degree lower bound for a ∈ U (which is ⊆ A₁): rowDeg_E(a) ≥ (δ/2)|B|.
  have hrowDeg_lb : ∀ a ∈ U, (δ / 2) * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ) := by
    intro a haU
    have haA₁ : a ∈ A₁ := hU_sub_A₁ haU
    rw [hA₁_def, Finset.mem_filter] at haA₁
    exact haA₁.2
  -- δ/2 > 0 and ≤ 1 since δ ≤ 1.
  have hρ_pos : (0 : ℝ) < δ / 2 := by positivity
  have hρ_le : δ / 2 ≤ 1 := by linarith
  obtain ⟨B', hB'_sub, hB'_lb_drc, hpopCol⟩ :=
    graph_dependentRandomChoice_popular_columns (G := G) A B hAB E hE_sub U hU_sub hU_card_pos
      (δ / 2) hρ_pos hρ_le hrowDeg_lb
  -- (δ/2)/2 = δ/4. So |B'| ≥ (δ/4)|B| = (δ/4)|A| ≥ (δ/8)|A|.
  have hB'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) := by
    have h3 : (δ / 8) * (A.card : ℝ) ≤ (δ / 4) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hA_nn
    have hquarter_eq : (δ / 2) / 2 * (B.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      rw [hB_real_eq]; ring
    linarith [hB'_lb_drc, hquarter_eq]
  -- Popular-column property: for b ∈ B', (δ/4)|U| ≤ |{a ∈ U : (a, b) ∈ E}|.
  have hpopCol_clean : ∀ b ∈ B', (δ / 4) * (U.card : ℝ) ≤
      ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ) := by
    intro b hb
    have h := hpopCol b hb
    have hrew : (δ / 2) / 2 * (U.card : ℝ) = (δ / 4) * (U.card : ℝ) := by ring
    linarith [hrew]
  refine ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, hU_card_lb,
    hA'_card_lb, hB'_card_lb, hUτ_bound, hA'_prop_clean, hpopCol_clean⟩

/--
**Pointwise count helper (step 5).** Given the witness from
`graph_dependentRandomChoice_payoff_pointwise_witness`, partition the path-3 Finset
`(B ×ˢ A).filter ((a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E)` by the
second coordinate `q.2 = a₁ ∈ U`. For `a₁` that is a popular neighbour of
`b` and a non-bad partner of `a`, the corresponding fiber has cardinality
`≥ τ`. There are at least `(δ/8)|U|` such `a₁`, giving the final bound
`(δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|²`.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_count {G : Type*} [DecidableEq G]
    (δ : ℝ) (A B : Finset G) (E : Finset (G × G)) (U A' B' : Finset G) (τ : ℝ)
    (hU_sub : U ⊆ A) (_hA'_sub_U : A' ⊆ U) (_hB'_sub : B' ⊆ B)
    (hτ_nn : 0 ≤ τ)
    (hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ)
    (hbadPartner : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ))
    (hpopCol : ∀ b ∈ B',
      (δ / 4) * (U.card : ℝ) ≤
        ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ))
    (a : G) (ha : a ∈ A') (b : G) (hb : b ∈ B') :
    (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
      (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- "Popular neighbours of b in U" and "non-bad partners of a in U".
  set Nb : Finset G := U.filter (fun a₁ ↦ (a₁, b) ∈ E) with hNb_def
  set Bad : Finset G := U.filter (fun a₁ ↦
    ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ) with hBad_def
  have hNb_lb : (δ / 4) * (U.card : ℝ) ≤ (Nb.card : ℝ) := hpopCol b hb
  have hBad_ub : (Bad.card : ℝ) ≤ (δ / 8) * (U.card : ℝ) := hbadPartner a ha
  -- Good := Nb \ Bad.  |Good| ≥ |Nb| - |Bad| ≥ (δ/8)|U|.
  set Good : Finset G := Nb \ Bad with hGood_def
  have hGood_sub_Nb : Good ⊆ Nb := Finset.sdiff_subset
  have hNb_sub_U : Nb ⊆ U := Finset.filter_subset _ _
  have hGood_sub_U : Good ⊆ U := hGood_sub_Nb.trans hNb_sub_U
  have hGood_card_lb : (δ / 8) * (U.card : ℝ) ≤ (Good.card : ℝ) := by
    -- |Nb \ Bad| ≥ |Nb| - |Bad|, via Nb ⊆ (Nb \ Bad) ∪ Bad.
    have hUnion : Nb ⊆ (Nb \ Bad) ∪ Bad := by
      intro x hx
      by_cases hxBad : x ∈ Bad
      · exact Finset.mem_union_right _ hxBad
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxBad⟩)
    have h1 : Nb.card ≤ ((Nb \ Bad) ∪ Bad).card := Finset.card_le_card hUnion
    have h2 : ((Nb \ Bad) ∪ Bad).card ≤ (Nb \ Bad).card + Bad.card :=
      Finset.card_union_le _ _
    have hreal : (Nb.card : ℝ) ≤ ((Nb \ Bad).card : ℝ) + (Bad.card : ℝ) := by
      have : (Nb.card : ℕ) ≤ (Nb \ Bad).card + Bad.card := le_trans h1 h2
      exact_mod_cast this
    have hGood_card_eq : ((Nb \ Bad).card : ℝ) = (Good.card : ℝ) := by
      rw [hGood_def]
    linarith [hreal, hNb_lb, hBad_ub, hGood_card_eq]
  -- For each a₁ ∈ Good: (a₁, b) ∈ E and codeg_E(a, a₁) ≥ τ.
  have hGood_codeg : ∀ a₁ ∈ Good,
      τ ≤ ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) ∧ (a₁, b) ∈ E := by
    intro a₁ ha₁
    rw [hGood_def, Finset.mem_sdiff, hNb_def, Finset.mem_filter, hBad_def,
      Finset.mem_filter] at ha₁
    obtain ⟨⟨ha₁U, ha₁bE⟩, hnotBad⟩ := ha₁
    refine ⟨?_, ha₁bE⟩
    by_contra hlt
    push Not at hlt
    exact hnotBad ⟨ha₁U, hlt⟩
  -- Path Finset of interest.
  set paths : Finset (G × G) := (B ×ˢ A).filter fun q : G × G ↦
    (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E with hpaths_def
  -- Fiber over the second coordinate: for each a₁, witness pairs (b₁, a₁).
  set fiber : G → Finset (G × G) := fun a₁ ↦
    (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).image (fun b₁ ↦ (b₁, a₁))
    with hfiber_def
  -- fiber a₁ has the same cardinality as the inner filter (image of an injection).
  have hfiber_card : ∀ a₁,
      (fiber a₁).card = (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card := by
    intro a₁
    rw [hfiber_def]
    apply Finset.card_image_of_injective
    intro x y hxy
    exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
  -- For a₁ ∈ Good, fiber a₁ ⊆ paths.
  have hfiber_sub : ∀ a₁ ∈ Good, fiber a₁ ⊆ paths := by
    intro a₁ ha₁ p hp
    rw [hfiber_def, Finset.mem_image] at hp
    obtain ⟨b₁, hb₁, hpeq⟩ := hp
    rw [Finset.mem_filter] at hb₁
    obtain ⟨hb₁B, habE, ha₁b₁E⟩ := hb₁
    have ha₁U : a₁ ∈ U := hGood_sub_U ha₁
    have ha₁A : a₁ ∈ A := hU_sub ha₁U
    obtain ⟨_, ha₁bE⟩ := hGood_codeg a₁ ha₁
    rw [hpaths_def, Finset.mem_filter, Finset.mem_product]
    rw [← hpeq]
    exact ⟨⟨hb₁B, ha₁A⟩, habE, ha₁b₁E, ha₁bE⟩
  -- Pairwise disjointness of fibers (different a₁ → different second coord).
  have hfiber_disjoint : (Good : Set G).PairwiseDisjoint fiber := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    intro p hpx hpy
    rw [hfiber_def, Finset.mem_image] at hpx hpy
    obtain ⟨bx, _, hpx_eq⟩ := hpx
    obtain ⟨by_, _, hpy_eq⟩ := hpy
    have hsnd : p.2 = x := by rw [← hpx_eq]
    have hsnd' : p.2 = y := by rw [← hpy_eq]
    exact hxy (hsnd.symm.trans hsnd')
  -- |⋃_{a₁ ∈ Good} fiber a₁| = Σ_{a₁ ∈ Good} |fiber a₁|.
  have hbiUnion_card : (Good.biUnion fiber).card = ∑ a₁ ∈ Good, (fiber a₁).card := by
    exact Finset.card_biUnion (fun x hx y hy hxy ↦ hfiber_disjoint hx hy hxy)
  -- The biUnion is contained in paths.
  have hbiUnion_sub : Good.biUnion fiber ⊆ paths := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨a₁, ha₁, hp⟩ := hp
    exact hfiber_sub a₁ ha₁ hp
  have hcard_path_lb : (∑ a₁ ∈ Good, (fiber a₁).card : ℕ) ≤ paths.card := by
    calc (∑ a₁ ∈ Good, (fiber a₁).card : ℕ)
        = (Good.biUnion fiber).card := hbiUnion_card.symm
      _ ≤ paths.card := Finset.card_le_card hbiUnion_sub
  have hcard_path_lb_real : (∑ a₁ ∈ Good, ((fiber a₁).card : ℝ)) ≤ (paths.card : ℝ) := by
    have h : ((∑ a₁ ∈ Good, (fiber a₁).card : ℕ) : ℝ) ≤ (paths.card : ℝ) := by
      exact_mod_cast hcard_path_lb
    push_cast at h; exact h
  -- Σ_{a₁ ∈ Good} |fiber a₁| ≥ |Good| · τ.
  have hsum_lb : (Good.card : ℝ) * τ ≤ ∑ a₁ ∈ Good, ((fiber a₁).card : ℝ) := by
    rw [show (Good.card : ℝ) * τ = ∑ _a₁ ∈ Good, τ from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a₁ ha₁ ↦ ?_
    have hcard := hfiber_card a₁
    have hcodeg := (hGood_codeg a₁ ha₁).1
    have : ((fiber a₁).card : ℝ) =
        ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) := by
      exact_mod_cast hcard
    rw [this]
    exact hcodeg
  -- Combine: paths ≥ |Good| · τ ≥ (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  have hGood_τ : (δ / 8) * (U.card : ℝ) * τ ≤ (Good.card : ℝ) * τ :=
    mul_le_mul_of_nonneg_right hGood_card_lb hτ_nn
  linarith [hUτ_bound, hGood_τ, hsum_lb, hcard_path_lb_real]

/--
**DRC payoff: pointwise path-3 count.** Given the pair-DRC witness `U ⊆ A`
(from `graph_pair_dependentRandomChoice`), define the "non-bad" set
`A' := { a ∈ U : few a' ∈ U with codegree < (δ³/2⁷) n }` and the "popular"
set `B' := { b ∈ B : (δ/4) |U| ≤ |N_U(b)| }`. For `a ∈ A'`, `b ∈ B'`, the
length-3 path count `P(a, b) ≥ (δ⁵ / 2¹²) n²`.

Proof: of the `(δ/4)|U|` vertices in `U ∩ N(b)`, at most `(δ/8)|U|` are bad
partners of `a`, leaving `≥ (δ/8)|U|` non-bad partners `a₁`. Each non-bad
partner has `|N(a) ∩ N(a₁)| ≥ (δ³/2⁷) n` choices of `b₁`. Total:
`P(a, b) ≥ (δ/8)|U| · (δ³/2⁷) n ≥ (δ/8)(δ/4)n · (δ³/128) n = (δ⁵/2¹²) n²`.
-/
lemma graph_dependentRandomChoice_payoff_pointwise {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  obtain ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, _hU_card, hA'_card,
    hB'_card, hUτ_bound, hbadPartner, hpopCol⟩ :=
    graph_dependentRandomChoice_payoff_pointwise_witness δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  refine ⟨A', B', hA'_sub_U.trans hU_sub, hB'_sub, hA'_card, hB'_card, ?_⟩
  intro a ha b hb
  exact graph_dependentRandomChoice_payoff_pointwise_count δ A B E U A' B' τ hU_sub hA'_sub_U hB'_sub
    hτ_nn hUτ_bound hbadPartner hpopCol a ha b hb

/--
**Dense bipartite graph has a pointwise length-3 path rectangle (Fox-Sudakov
Lemma 5.2 / Tao-Vu Cor. 6.20).** Given a bipartite graph `E ⊆ A ×ˢ B` of density
`≥ δ` (with `|A| = |B|`), there exist subsets `A' ⊆ A`, `B' ⊆ B` of cardinality
`≥ (δ / 8) · |A|` such that *every* pair `(a, b) ∈ A' × B'` admits at least
`(δ^5 / 2^12) · |A|^2` length-3 paths `a — b₁ — a₁ — b` in `E`. The path
multiplicity is **pointwise**, not averaged — this is what makes the bound
linear when fed into the triple-rep count.

Proof: dependent random choice (as implemented). (1) Restrict to the popular
rows `A₁ := {a : deg_E(a) ≥ (δ/2)|B|}` and edges `E₁` out of them; `E₁` still
has density `≥ δ/2`. (2) Pair-DRC (Fox-Sudakov 5.1): pick a *column* vertex
`v ∈ B` uniformly and set the core `U := N_{E₁}(v) ⊆ A₁ ⊆ A`; by Cauchy-Schwarz
a positive fraction of `v` give both `|U| ≥ (δ/4)|A|` and few "bad" ordered
pairs `(a, a') ∈ U × U` of low codegree `|N(a) ∩ N(a')| < τ`. (3) `A' ⊆ U` is
the Markov refinement to vertices with `≤ (δ/8)|U|` bad partners in `U`; (4)
`B' ⊆ B` is the popular columns, those with `≥ (δ/4)|U|` neighbors inside `U`.
The high pointwise codegree on `A'` combined with `B'`'s density in `U` forces
`≥ (δ⁵/2¹²)|A|²` length-3 paths through every `(a, b) ∈ A' × B'`. References:
Fox-Sudakov, *Dependent Random Choice* (2011), Lemma 5.2; Tao-Vu, *Additive
Combinatorics*, §6.4, Cor. 6.20.
-/
lemma dense_bipartite_has_path3_rectangle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ^5 / 2^12) * (A.card : ℝ)^2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- The Fox-Sudakov DRC payload is packaged in `graph_dependentRandomChoice_payoff_pointwise`,
  -- which assembles `graph_pair_dependentRandomChoice`, `graph_high_degree_subset_lb`, and the
  -- final pointwise path-3 count step (see those lemmas for the breakdown).
  exact graph_dependentRandomChoice_payoff_pointwise δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense

/--
**Graph-BSG step C (length-3 path multiplicity).** Substantive content of the
Balog-Szemerédi-Gowers reduction. Given finite sets `A`, `B` of equal
cardinality `n`, a dense bipartite graph `E ⊆ A ×ˢ B` with `|E| ≥ δ · n²`,
and the *restricted sumset* `S := {a+b : (a,b) ∈ E}` of size `|S| ≤ K · n`,
there exist subsets `A' ⊆ A`, `B' ⊆ B` of size `≥ c(δ,K) · n` each whose
ordinary sumset is small: `|A' + B'| ≤ C(δ,K) · n`.

The mechanism is the length-3 path argument with multiplicity denominator: for
`a ∈ A'`, `b ∈ B'`, length-3 paths `a — b₁ — a₁ — b` in `E` give
representations `a + b = (a + b₁) − (a₁ + b₁) + (a₁ + b)` with all three
terms in `S`. Each pair `(a, b)` admits `Ω(δ^O(1) · n²)` such paths by
Cauchy-Schwarz on `E`. The cubic support count `|S − S + S| ≤ |S|³ ≤ K³ n³`
divided by the path-multiplicity lower bound yields the linear bound.

The key ingredient is to count length-3 paths *with multiplicity*: counting
only the support of the representation set (rather than multiplicity) is
insufficient. Tao–Vu §6.4 (proof of Theorem 2.29) / Petridis 2012.
-/
lemma graph_balogSzemerediGowers_restricted_sumset {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ δ K : ℝ, 0 < δ → 0 < K → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ A B : Finset G, A.Nonempty → B.Nonempty → A.card = B.card →
        ∀ E : Finset (G × G), E ⊆ A ×ˢ B →
          δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ) →
          ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ) →
          ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
            c * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            c * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
            ((A' + B').card : ℝ) ≤ C * (A.card : ℝ) := by
  -- ## High-level proof structure (length-3 path multiplicity argument).
  --
  -- Constants:
  -- * c := δ / 8 (from `dense_bipartite_has_path3_rectangle`, Fox-Sudakov DRC).
  -- * C := 2^13 K³ / δ^5 + 2^12 / δ^5, the path-multiplicity bound,
  --   absorbing both the M ≥ 1 and M = 0 sub-cases (triple-counting step in
  --   the proof of Tao-Vu Theorem 2.29, §6.4).
  intro δ K hδ hK
  refine ⟨δ / 8, 2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5,
    by positivity, by positivity, ?_⟩
  intro A B hA hB hAB E hE_sub hE_lb hS_ub
  -- Local abbreviations.
  set n : ℕ := A.card with hn_def
  have hn_pos : 0 < n := hA.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hBcard_nat : B.card = n := hAB.symm
  have hBcard : (B.card : ℝ) = (n : ℝ) := by exact_mod_cast hBcard_nat
  -- Compose the three sub-lemmas: `dense_bipartite_has_path3_rectangle` for
  -- the pointwise path-3 lower bound, `path3_count_le_triple_rep_count` for
  -- the path-to-triple-rep bridge, `restricted_sumset_via_multiplicity` for
  -- the cubic divisor. The Apop/Bpop scaffolding that previously prefixed
  -- this proof has been deleted; DRC supplies its own A', B' refinement.
  -- We must first handle the degenerate case `δ > 1`, which is vacuous
  -- since `δ · n² ≤ |E| ≤ n²`.
  by_cases hδ_le : δ ≤ 1
  · -- ### Substantive case: δ ≤ 1. Compose the three sub-lemmas.
    -- Restricted sumset image S.
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S := by
      intro p hp; exact Finset.mem_image_of_mem _ hp
    -- Convert hE_lb : δ · n² ≤ |E| to the rectangle form δ · |A| · |B| ≤ |E|.
    have hE_lb_rect : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) := by
      have hsq : δ * (A.card : ℝ) ^ 2 = δ * (A.card : ℝ) * (B.card : ℝ) := by
        rw [hBcard, hn_def]; ring
      linarith [hE_lb, hsq.le, hsq.symm.le]
    -- Apply DRC pointwise path-3 rectangle.
    obtain ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, hP_lb⟩ :=
      dense_bipartite_has_path3_rectangle δ hδ hδ_le A B hA hAB E hE_sub hE_lb_rect
    -- Set the integer floor multiplicity M.
    set M : ℕ := Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) with hM_def
    have hM_arg_nn : 0 ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 := by positivity
    have hM_floor_le : (M : ℝ) ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 :=
      Nat.floor_le hM_arg_nn
    have hM_floor_ge : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 - 1 < (M : ℝ) := by
      have h : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 <
          (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) + 1 :=
        Nat.lt_floor_add_one ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2)
      have hMeq : (M : ℝ) = (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) := by
        rfl
      rw [hMeq]; linarith
    -- Pointwise lower bound on the triple-rep count via the path-3 bridge.
    have hM_cover : ∀ a ∈ A', ∀ b ∈ B',
        M ≤ ((S ×ˢ S ×ˢ S).filter
              (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card := by
      intro a ha b hb
      have hP : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) :=
        hP_lb a ha b hb
      have hP_n : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
        rw [hn_def]; exact hP
      have hbridge : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
          ≤ ((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card :=
        path3_count_le_triple_rep_count A B S E hSdef a b
      have hbridge_R : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ)
          ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) := by
        exact_mod_cast hbridge
      have hMR : (M : ℝ) ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) :=
        le_trans hM_floor_le (le_trans hP_n hbridge_R)
      exact_mod_cast hMR
    -- Apply restricted-sumset-via-multiplicity to obtain M · |A'+B'| ≤ |S|^3.
    have hMS3 : M * (A' + B').card ≤ S.card ^ 3 :=
      restricted_sumset_via_multiplicity A' B' S M hM_cover
    have hMS3_R : (M : ℝ) * ((A' + B').card : ℝ) ≤ ((S.card : ℝ)) ^ 3 := by
      have h := hMS3
      have hh : ((M * (A' + B').card : ℕ) : ℝ) ≤ ((S.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at hh; exact hh
    -- Bound |S|^3 ≤ K^3 · n^3.
    have hS_card_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hSn_ub : (S.card : ℝ) ≤ K * (n : ℝ) := by
      have := hS_ub; rw [hn_def]; exact this
    have hSn_cube_ub : (S.card : ℝ) ^ 3 ≤ K ^ 3 * (n : ℝ) ^ 3 := by
      have h2 : (S.card : ℝ) ^ 3 ≤ (K * (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hS_card_nn hSn_ub 3
      have heq : (K * (n : ℝ)) ^ 3 = K ^ 3 * (n : ℝ) ^ 3 := by ring
      rw [heq] at h2; exact h2
    -- Combine: M · |A' + B'| ≤ K^3 · n^3.
    have hMSc : (M : ℝ) * ((A' + B').card : ℝ) ≤ K ^ 3 * (n : ℝ) ^ 3 :=
      le_trans hMS3_R hSn_cube_ub
    -- Refine to existential. The c · n bounds are exactly hA'_card, hB'_card
    -- since c = δ / 8 matches what DRC gave us; the |A' + B'| ≤ C · n bound
    -- requires case-splitting on M.
    refine ⟨A', B', hA'_sub, hB'_sub, ?_, ?_, ?_⟩
    · -- (δ/8) · |A| ≤ |A'|
      have h := hA'_card
      rw [hn_def]; exact h
    · -- (δ/8) · |A| ≤ |B'|
      have h := hB'_card
      rw [hn_def]; exact h
    · -- |A' + B'| ≤ C · n
      -- Two sub-cases: M = 0 or M ≥ 1.
      -- Constants we'll absorb into the final C = 2^13 K^3 / δ^5 + 2^12 / δ^5.
      have hδ5_pos : (0 : ℝ) < δ ^ 5 := by positivity
      have h2pow12_pos : (0 : ℝ) < (2 : ℝ) ^ 12 := by positivity
      have h2pow13_pos : (0 : ℝ) < (2 : ℝ) ^ 13 := by positivity
      have hK3_pos : (0 : ℝ) < K ^ 3 := by positivity
      have h_AplusB_nn : (0 : ℝ) ≤ ((A' + B').card : ℝ) := Nat.cast_nonneg _
      have hConstC_nn : (0 : ℝ) ≤ 2 ^ 12 / δ ^ 5 := by positivity
      have hConstC1_nn : (0 : ℝ) ≤ 2 ^ 13 * K ^ 3 / δ ^ 5 := by positivity
      by_cases hM_zero : M = 0
      · -- M = 0 ⇒ (δ^5 / 2^12) · n² < 1 ⇒ n² < 2^12 / δ^5.
        have hM0R : (M : ℝ) = 0 := by exact_mod_cast hM_zero
        have hsmall : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 < 1 := by
          have h := hM_floor_ge; rw [hM0R] at h; linarith
        have hn2_ub : (n : ℝ) ^ 2 < 2 ^ 12 / δ ^ 5 := by
          have hpow_inv : (0 : ℝ) < 2 ^ 12 / δ ^ 5 := by positivity
          have hh : (n : ℝ) ^ 2 = ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) := by
            field_simp
          rw [hh]
          have h_ineq : ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) <
              1 * (2 ^ 12 / δ ^ 5) :=
            mul_lt_mul_of_pos_right hsmall hpow_inv
          linarith
        -- Crude bound: |A'+B'| ≤ |A'|·|B'| ≤ n·n = n².
        have hAplusB_le_prod : (A' + B').card ≤ A'.card * B'.card :=
          Finset.card_add_le
        have hA'_le_n : A'.card ≤ n := by
          have := Finset.card_le_card hA'_sub
          rw [← hn_def] at this; exact this
        have hB'_le_n : B'.card ≤ n := by
          have := Finset.card_le_card hB'_sub
          rw [hBcard_nat] at this; exact this
        have hA'B'_le_n2_nat : A'.card * B'.card ≤ n * n := by
          exact Nat.mul_le_mul hA'_le_n hB'_le_n
        have hAplusB_le_n2 : (A' + B').card ≤ n * n :=
          le_trans hAplusB_le_prod hA'B'_le_n2_nat
        have hAplusB_le_n2R : ((A' + B').card : ℝ) ≤ (n : ℝ) ^ 2 := by
          have h : ((A' + B').card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hAplusB_le_n2
          push_cast at h
          have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
          linarith
        have hAplusB_lt_const : ((A' + B').card : ℝ) < 2 ^ 12 / δ ^ 5 :=
          lt_of_le_of_lt hAplusB_le_n2R hn2_ub
        -- Now 2^12/δ^5 ≤ (2^12/δ^5) · n since 1 ≤ n.
        have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hconst_le : 2 ^ 12 / δ ^ 5 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hn_ge_one hConstC_nn
          simpa using this
        have hAplusB_le_constn : ((A' + B').card : ℝ) ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) :=
          le_trans (le_of_lt hAplusB_lt_const) hconst_le
        -- Combine: 2^12/δ^5 · n ≤ (2^13 K^3 / δ^5 + 2^12 / δ^5) · n.
        have hsum_expand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
        have hC1n_nn : 0 ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          mul_nonneg hConstC1_nn hn_nn
        have hcomb : (2 ^ 12 / δ ^ 5) * (n : ℝ) ≤
            (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          rw [hsum_expand]; linarith
        linarith
      · -- M ≥ 1. Then M + 1 ≤ 2M, hence 2M > (δ^5/2^12)·n², so M > (δ^5/2^13)·n².
        have hM_ge_one : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM_zero
        have hM_geR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_one
        have hM_pos_R : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM_geR
        have h_two_M : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤ 2 * (M : ℝ) := by
          have h1 := hM_floor_ge -- (δ^5/2^12)·n² - 1 < M
          linarith
        have h_M_lower : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 ≤ (M : ℝ) := by
          have h_div : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 =
              ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) / 2 := by ring
          rw [h_div]; linarith
        -- Multiply the lower bound on M by |A'+B'|:
        -- (δ^5/2^13)·n² · |A'+B'| ≤ M · |A'+B'| ≤ K^3 · n^3.
        have h_mul1 : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            (M : ℝ) * ((A' + B').card : ℝ) := by
          exact mul_le_mul_of_nonneg_right h_M_lower h_AplusB_nn
        have h_chain : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            K ^ 3 * (n : ℝ) ^ 3 := le_trans h_mul1 hMSc
        -- Divide by (δ^5/2^13)·n² > 0 to get |A'+B'| ≤ (2^13 K^3 / δ^5) · n.
        have h_div_pos : (0 : ℝ) < (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 := by positivity
        have hδ5_ne : (δ ^ 5 : ℝ) ≠ 0 := ne_of_gt hδ5_pos
        have h_target_eq : K ^ 3 * (n : ℝ) ^ 3 =
            ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) := by
          rw [show ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) =
              (δ ^ 5 / δ ^ 5) * (K ^ 3 * (n : ℝ) ^ 3) by ring]
          rw [div_self hδ5_ne, one_mul]
        rw [h_target_eq] at h_chain
        have h_AplusB_le_lin : ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          le_of_mul_le_mul_left h_chain h_div_pos
        -- Absorb into C.
        have hC2n_nn : 0 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := mul_nonneg hConstC_nn hn_nn
        have h_final_const_ineq :
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) ≤
              (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have hexpand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
              (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
          rw [hexpand]; linarith
        linarith
  · -- ### Vacuous case: δ > 1. Then |E| ≤ n² but δ·n² ≤ |E|, contradiction.
    exfalso
    push Not at hδ_le  -- 1 < δ
    have hE_le_AB : E.card ≤ (A ×ˢ B).card := Finset.card_le_card hE_sub
    have hAB_card : (A ×ˢ B).card = n * n := by
      rw [Finset.card_product, ← hn_def, hBcard_nat]
    have hE_le_n2_nat : E.card ≤ n * n := by rw [← hAB_card]; exact hE_le_AB
    have hE_le_n2 : (E.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : ((E.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hE_le_n2_nat
      push_cast at h
      have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      linarith
    have hδn2 : δ * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have h := hE_lb; rw [hn_def]; exact h
    -- So δ · n² ≤ n², hence δ ≤ 1 (since n² > 0), contradicting 1 < δ.
    have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hδ_le_one : δ ≤ 1 := by
      have h1 : δ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_trans hδn2 hE_le_n2
      have h2 : δ * (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ 2 := by linarith
      exact le_of_mul_le_mul_right h2 hn2_pos
    linarith


/--
**Graph-BSG step C (length-3 path multiplicity), explicit-constant
form.** Sibling of `graph_balogSzemerediGowers_restricted_sumset` that exposes the
witnesses `c = δ/8` and `C = 2^13 K^3/δ^5 + 2^12/δ^5` in the theorem
type rather than under an existential. Required by downstream
consumers (e.g. `popular_lambda_to_polylog_doubling`) that need to
read off the polynomial-in-`δ`-and-`K` scaling. Same proof body as the
qualitative form; the only change is moving the witnesses from the
`refine ⟨…⟩` line into the signature.
-/
lemma graph_balogSzemerediGowers_restricted_sumset_explicit {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (A B : Finset G) (hA : A.Nonempty) (_hB : B.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_lb : δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ))
    (hS_ub : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (A.card : ℝ) := by
  -- Local abbreviations.
  set n : ℕ := A.card with hn_def
  have hn_pos : 0 < n := hA.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hBcard_nat : B.card = n := hAB.symm
  have hBcard : (B.card : ℝ) = (n : ℝ) := by exact_mod_cast hBcard_nat
  by_cases hδ_le : δ ≤ 1
  · -- ### Substantive case: δ ≤ 1.
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S := by
      intro p hp; exact Finset.mem_image_of_mem _ hp
    have hE_lb_rect : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) := by
      have hsq : δ * (A.card : ℝ) ^ 2 = δ * (A.card : ℝ) * (B.card : ℝ) := by
        rw [hBcard, hn_def]; ring
      linarith [hE_lb, hsq.le, hsq.symm.le]
    obtain ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, hP_lb⟩ :=
      dense_bipartite_has_path3_rectangle δ hδ hδ_le A B hA hAB E hE_sub hE_lb_rect
    set M : ℕ := Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) with hM_def
    have hM_arg_nn : 0 ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 := by positivity
    have hM_floor_le : (M : ℝ) ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 :=
      Nat.floor_le hM_arg_nn
    have hM_floor_ge : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 - 1 < (M : ℝ) := by
      have h : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 <
          (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) + 1 :=
        Nat.lt_floor_add_one ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2)
      have hMeq : (M : ℝ) = (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) := by
        rfl
      rw [hMeq]; linarith
    have hM_cover : ∀ a ∈ A', ∀ b ∈ B',
        M ≤ ((S ×ˢ S ×ˢ S).filter
              (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card := by
      intro a ha b hb
      have hP : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) :=
        hP_lb a ha b hb
      have hP_n : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
        rw [hn_def]; exact hP
      have hbridge : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
          ≤ ((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card :=
        path3_count_le_triple_rep_count A B S E hSdef a b
      have hbridge_R : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ)
          ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) := by
        exact_mod_cast hbridge
      have hMR : (M : ℝ) ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) :=
        le_trans hM_floor_le (le_trans hP_n hbridge_R)
      exact_mod_cast hMR
    have hMS3 : M * (A' + B').card ≤ S.card ^ 3 :=
      restricted_sumset_via_multiplicity A' B' S M hM_cover
    have hMS3_R : (M : ℝ) * ((A' + B').card : ℝ) ≤ ((S.card : ℝ)) ^ 3 := by
      have h := hMS3
      have hh : ((M * (A' + B').card : ℕ) : ℝ) ≤ ((S.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at hh; exact hh
    have hS_card_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hSn_ub : (S.card : ℝ) ≤ K * (n : ℝ) := by
      have := hS_ub; rw [hn_def]; exact this
    have hSn_cube_ub : (S.card : ℝ) ^ 3 ≤ K ^ 3 * (n : ℝ) ^ 3 := by
      have h2 : (S.card : ℝ) ^ 3 ≤ (K * (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hS_card_nn hSn_ub 3
      have heq : (K * (n : ℝ)) ^ 3 = K ^ 3 * (n : ℝ) ^ 3 := by ring
      rw [heq] at h2; exact h2
    have hMSc : (M : ℝ) * ((A' + B').card : ℝ) ≤ K ^ 3 * (n : ℝ) ^ 3 :=
      le_trans hMS3_R hSn_cube_ub
    refine ⟨A', B', hA'_sub, hB'_sub, ?_, ?_, ?_⟩
    · -- (δ/8) · |A| ≤ |A'|
      have h := hA'_card
      rw [hn_def]; exact h
    · -- (δ/8) · |A| ≤ |B'|
      have h := hB'_card
      rw [hn_def]; exact h
    · -- |A' + B'| ≤ C · n
      have hδ5_pos : (0 : ℝ) < δ ^ 5 := by positivity
      have h_AplusB_nn : (0 : ℝ) ≤ ((A' + B').card : ℝ) := Nat.cast_nonneg _
      have hConstC_nn : (0 : ℝ) ≤ 2 ^ 12 / δ ^ 5 := by positivity
      have hConstC1_nn : (0 : ℝ) ≤ 2 ^ 13 * K ^ 3 / δ ^ 5 := by positivity
      by_cases hM_zero : M = 0
      · have hM0R : (M : ℝ) = 0 := by exact_mod_cast hM_zero
        have hsmall : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 < 1 := by
          have h := hM_floor_ge; rw [hM0R] at h; linarith
        have hn2_ub : (n : ℝ) ^ 2 < 2 ^ 12 / δ ^ 5 := by
          have hpow_inv : (0 : ℝ) < 2 ^ 12 / δ ^ 5 := by positivity
          have hh : (n : ℝ) ^ 2 = ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) := by
            field_simp
          rw [hh]
          have h_ineq : ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) <
              1 * (2 ^ 12 / δ ^ 5) :=
            mul_lt_mul_of_pos_right hsmall hpow_inv
          linarith
        have hAplusB_le_prod : (A' + B').card ≤ A'.card * B'.card :=
          Finset.card_add_le
        have hA'_le_n : A'.card ≤ n := by
          have := Finset.card_le_card hA'_sub
          rw [← hn_def] at this; exact this
        have hB'_le_n : B'.card ≤ n := by
          have := Finset.card_le_card hB'_sub
          rw [hBcard_nat] at this; exact this
        have hA'B'_le_n2_nat : A'.card * B'.card ≤ n * n := by
          exact Nat.mul_le_mul hA'_le_n hB'_le_n
        have hAplusB_le_n2 : (A' + B').card ≤ n * n :=
          le_trans hAplusB_le_prod hA'B'_le_n2_nat
        have hAplusB_le_n2R : ((A' + B').card : ℝ) ≤ (n : ℝ) ^ 2 := by
          have h : ((A' + B').card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hAplusB_le_n2
          push_cast at h
          have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
          linarith
        have hAplusB_lt_const : ((A' + B').card : ℝ) < 2 ^ 12 / δ ^ 5 :=
          lt_of_le_of_lt hAplusB_le_n2R hn2_ub
        have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hconst_le : 2 ^ 12 / δ ^ 5 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hn_ge_one hConstC_nn
          simpa using this
        have hAplusB_le_constn : ((A' + B').card : ℝ) ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) :=
          le_trans (le_of_lt hAplusB_lt_const) hconst_le
        have hsum_expand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
        have hC1n_nn : 0 ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          mul_nonneg hConstC1_nn hn_nn
        have hcomb : (2 ^ 12 / δ ^ 5) * (n : ℝ) ≤
            (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          rw [hsum_expand]; linarith
        linarith
      · have hM_ge_one : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM_zero
        have hM_geR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_one
        have h_two_M : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤ 2 * (M : ℝ) := by
          have h1 := hM_floor_ge; linarith
        have h_M_lower : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 ≤ (M : ℝ) := by
          have h_div : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 =
              ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) / 2 := by ring
          rw [h_div]; linarith
        have h_mul1 : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            (M : ℝ) * ((A' + B').card : ℝ) := by
          exact mul_le_mul_of_nonneg_right h_M_lower h_AplusB_nn
        have h_chain : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            K ^ 3 * (n : ℝ) ^ 3 := le_trans h_mul1 hMSc
        have h_div_pos : (0 : ℝ) < (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 := by positivity
        have hδ5_ne : (δ ^ 5 : ℝ) ≠ 0 := ne_of_gt hδ5_pos
        have h_target_eq : K ^ 3 * (n : ℝ) ^ 3 =
            ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) := by
          rw [show ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) =
              (δ ^ 5 / δ ^ 5) * (K ^ 3 * (n : ℝ) ^ 3) by ring]
          rw [div_self hδ5_ne, one_mul]
        rw [h_target_eq] at h_chain
        have h_AplusB_le_lin : ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          le_of_mul_le_mul_left h_chain h_div_pos
        have hC2n_nn : 0 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := mul_nonneg hConstC_nn hn_nn
        have h_final_const_ineq :
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) ≤
              (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have hexpand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
              (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
          rw [hexpand]; linarith
        linarith
  · -- ### Vacuous case: δ > 1. Then |E| ≤ n² but δ·n² ≤ |E|, contradiction.
    exfalso
    push Not at hδ_le
    have hE_le_AB : E.card ≤ (A ×ˢ B).card := Finset.card_le_card hE_sub
    have hAB_card : (A ×ˢ B).card = n * n := by
      rw [Finset.card_product, ← hn_def, hBcard_nat]
    have hE_le_n2_nat : E.card ≤ n * n := by rw [← hAB_card]; exact hE_le_AB
    have hE_le_n2 : (E.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : ((E.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hE_le_n2_nat
      push_cast at h
      have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      linarith
    have hδn2 : δ * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have h := hE_lb; rw [hn_def]; exact h
    have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hδ_le_one : δ ≤ 1 := by
      have h1 : δ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_trans hδn2 hE_le_n2
      have h2 : δ * (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ 2 := by linarith
      exact le_of_mul_le_mul_right h2 hn2_pos
    linarith

/--
**Balog-Szemerédi-Gowers (asymmetric, equal-cardinality, qualitative
form).** For every `η > 0` there exist positive `c, C` such that whenever
`X`, `Y` are finite subsets of an additive commutative group with
`|X| = |Y| =: n` and mixed additive energy `E[X,Y] ≥ η · n³`, there are
subsets `X' ⊆ X` and `Y' ⊆ Y` of size `≥ c · n` each whose difference set is
bounded: `|X' - Y'| ≤ C · n`. This is the two-set form with `|X| = |Y|`; the
general asymmetric form with `|X| ≠ |Y|` is not treated here.
-/
theorem balog_szemeredi_gowers_asymmetric {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ X Y : Finset G, X.Nonempty → Y.Nonempty → X.card = Y.card →
        η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ) →
        ∃ X' Y' : Finset G, X' ⊆ X ∧ Y' ⊆ Y ∧
          c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          c * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
          ((X' - Y').card : ℝ) ≤ C * (X.card : ℝ) := by
  intro η hη
  -- Outer constants: graph_balogSzemerediGowers_restricted_sumset with (δ := η/2, K := 4/η), then
  -- Ruzsa adapter.
  obtain ⟨c₀, C₀, hc₀, hC₀, hGraphBSG⟩ :=
    graph_balogSzemerediGowers_restricted_sumset (G := G) (η / 2) (4 / η) (by linarith) (by positivity)
  -- Final constants
  refine ⟨min c₀ (η / 4), (C₀ / c₀) ^ 3 / c₀ + 1, ?_, ?_, ?_⟩
  · exact lt_min hc₀ (by linarith)
  · have hpos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
    linarith
  intro X Y hX hY hXY hE
  set n : ℕ := X.card with hn_def
  have hYcard : Y.card = n := hXY.symm
  have hnpos : 0 < n := hX.card_pos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  -- Case split on whether n is "large" or "small"
  by_cases hLarge : 2 ≤ (η / 2) * n
  · -- Substantive case: n ≥ 4/η, so floor((η/2)*n) ≥ 1 and ≥ (η/4)*n.
    set θ : ℕ := Nat.floor ((η / 2) * (n : ℝ)) with hθ_def
    have hηn_nn : 0 ≤ (η / 2) * (n : ℝ) := by positivity
    have hθ_floor_le : (θ : ℝ) ≤ (η / 2) * n := Nat.floor_le hηn_nn
    have hθ_floor_ge : (η / 2) * (n : ℝ) - 1 < θ := by
      have := Nat.lt_floor_add_one ((η / 2) * (n : ℝ))
      linarith
    have hθ_pos : 1 ≤ θ := by
      have : (1 : ℝ) ≤ θ := by linarith
      exact_mod_cast this
    have hθ_posR : (0 : ℝ) < θ := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hθ_pos)
    have h_2θ_le : 2 * (θ : ℝ) ≤ η * n := by
      have := hθ_floor_le
      linarith
    -- θ ≥ (η/4) * n
    have hθ_ge_quarter : (η / 4) * (n : ℝ) ≤ θ := by
      have h1 : (η / 2) * (n : ℝ) - 1 ≤ θ := le_of_lt hθ_floor_ge
      have h2 : (1 : ℝ) ≤ (η / 4) * n := by linarith
      linarith
    -- Define the popular bipartite graph E
    set E : Finset (G × G) :=
      (X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2)) with hE_def
    have hE_sub : E ⊆ X ×ˢ Y := Finset.filter_subset _ _
    -- |E| ≥ (η/2) * n²
    have hPP := popular_pairs_card_lower_bound hη hXY hX hE θ h_2θ_le
    have hE_lb : (η / 2) * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have : (η / 2) * (n : ℝ) * Y.card = (η / 2) * (n : ℝ) ^ 2 := by
        rw [hYcard]; ring
      linarith
    -- S := image of E under (x,y) ↦ x + y
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    -- For each s ∈ S, X.addConvolution Y s ≥ θ.
    have hS_popular : ∀ s ∈ S, θ ≤ X.addConvolution Y s := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter] at hpE
      rw [← hps]; exact hpE.2
    -- S ⊆ X + Y.
    have hS_sub : S ⊆ X + Y := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter, Finset.mem_product] at hpE
      rw [← hps]
      exact Finset.add_mem_add hpE.1.1 hpE.1.2
    -- |S| * θ ≤ ∑_{s ∈ S} addConv s ≤ ∑_{s ∈ X+Y} addConv s = n²
    have hSum_eq : ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card :=
      sum_addConvolution_eq_card_product X Y
    have hSum_S_le : (S.card : ℕ) * θ ≤ X.card * Y.card := by
      calc (S.card : ℕ) * θ
          = ∑ _s ∈ S, θ := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ s ∈ S, X.addConvolution Y s :=
            Finset.sum_le_sum hS_popular
        _ ≤ ∑ s ∈ X + Y, X.addConvolution Y s :=
            Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun _ _ _ ↦ Nat.zero_le _)
        _ = X.card * Y.card := hSum_eq
    -- Convert to reals: |S| * θ ≤ n²
    have hSum_S_le_R : (S.card : ℝ) * θ ≤ (n : ℝ) ^ 2 := by
      have h : ((S.card * θ : ℕ) : ℝ) ≤ ((X.card * Y.card : ℕ) : ℝ) := by
        exact_mod_cast hSum_S_le
      push_cast at h
      rw [hYcard] at h
      have hgoal : (n : ℝ) ^ 2 = (n : ℝ) * n := by ring
      rw [hgoal]; exact h
    -- |S| ≤ n²/θ ≤ (4/η) * n
    have hS_le : (S.card : ℝ) ≤ (4 / η) * n := by
      have hS_le_nθ : (S.card : ℝ) ≤ (n : ℝ) ^ 2 / θ := by
        rw [le_div_iff₀ hθ_posR]; exact hSum_S_le_R
      have hbnd : (n : ℝ) ^ 2 / θ ≤ (4 / η) * n := by
        rw [div_le_iff₀ hθ_posR]
        have hηpos : 0 < η := hη
        have h_θ_pos_q : (0 : ℝ) < (η / 4) * n := by positivity
        have h1 : (n : ℝ) ^ 2 = n * n := by ring
        rw [h1]
        have h_4η_pos : (0 : ℝ) < 4 / η := by positivity
        have hθ_ge' : (η / 4) * (n : ℝ) ≤ θ := hθ_ge_quarter
        -- (4/η * n) * θ ≥ (4/η * n) * (η/4 * n) = n * n
        have : (4 / η) * (n : ℝ) * ((η / 4) * n) = n * n := by
          field_simp
        have hmul : (4 / η) * (n : ℝ) * ((η / 4) * n) ≤ (4 / η) * n * θ :=
          mul_le_mul_of_nonneg_left hθ_ge'
            (by positivity)
        linarith
      linarith
    -- Apply graph_balogSzemerediGowers_restricted_sumset
    have hδ : (η / 2) * (X.card : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      rw [← hn_def]; exact hE_lb
    have hK : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ (4 / η) * (X.card : ℝ) := by
      rw [← hn_def, ← hS_def]; exact hS_le
    obtain ⟨A', B', hA'sub, hB'sub, hA'lb, hB'lb, hAB'sumset⟩ :=
      hGraphBSG X Y hX hY hXY E hE_sub hδ hK
    -- Apply Ruzsa to get |A' - B'| ≤ (C₀/c₀)^3/c₀ * n
    have hA'pos : 0 < A'.card := by
      have : (0 : ℝ) < (A'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hA'ne : A'.Nonempty := Finset.card_pos.mp hA'pos
    have hB'pos : 0 < B'.card := by
      have : (0 : ℝ) < (B'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hB'ne : B'.Nonempty := Finset.card_pos.mp hB'pos
    -- Bound the sumset in terms of |A'|: |A' + B'| ≤ (C₀/c₀) * |A'|
    have hSumK : ((A' + B').card : ℝ) ≤ (C₀ / c₀) * A'.card := by
      have hC₀n_le : (C₀ : ℝ) * X.card ≤ (C₀ / c₀) * (c₀ * X.card) := by
        rw [show (C₀ / c₀) * (c₀ * (X.card : ℝ)) = C₀ * X.card by field_simp]
      have hcalc : (C₀ / c₀) * (c₀ * (X.card : ℝ)) ≤ (C₀ / c₀) * A'.card := by
        have hC₀c₀_pos : (0 : ℝ) < C₀ / c₀ := by positivity
        exact mul_le_mul_of_nonneg_left hA'lb (le_of_lt hC₀c₀_pos)
      linarith
    -- Balance: c₀ * |A'| ≤ |B'|, since |A'| ≤ |X| = n, so c₀ * |A'| ≤ c₀ * n ≤ |B'|.
    have hA'le_n : (A'.card : ℝ) ≤ n := by
      have : A'.card ≤ X.card := Finset.card_le_card hA'sub
      exact_mod_cast this
    have hBal : c₀ * (A'.card : ℝ) ≤ (B'.card : ℝ) := by
      have hc₀A'_le_c₀n : c₀ * (A'.card : ℝ) ≤ c₀ * X.card :=
        mul_le_mul_of_nonneg_left hA'le_n (le_of_lt hc₀)
      linarith
    obtain hRuzsa := ruzsa_sumset_to_difference (G := G)
      (C₀ / c₀) c₀ (by positivity) hc₀ A' B' hA'ne hB'ne hSumK hBal
    -- |A' - B'| ≤ (C₀/c₀)^3 / c₀ * |A'| ≤ (C₀/c₀)^3 / c₀ * n
    have hAmB'_le : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * n := by
      have h1 : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * A'.card := hRuzsa
      have hcoef_nn : (0 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) := by positivity
      have h2 : ((C₀ / c₀) ^ 3 / c₀) * A'.card ≤ ((C₀ / c₀) ^ 3 / c₀) * n :=
        mul_le_mul_of_nonneg_left hA'le_n hcoef_nn
      linarith
    refine ⟨A', B', hA'sub, hB'sub, ?_, ?_, ?_⟩
    · -- min c₀ (η/4) * n ≤ |A'|
      have hmin_le : min c₀ (η / 4) ≤ c₀ := min_le_left _ _
      calc min c₀ (η / 4) * (X.card : ℝ)
          ≤ c₀ * X.card :=
            mul_le_mul_of_nonneg_right hmin_le (Nat.cast_nonneg _)
        _ ≤ (A'.card : ℝ) := hA'lb
    · -- min c₀ (η/4) * Y.card ≤ |B'|
      have hmin_le : min c₀ (η / 4) ≤ c₀ := min_le_left _ _
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      calc min c₀ (η / 4) * (Y.card : ℝ)
          = min c₀ (η / 4) * X.card := by rw [hYn]
        _ ≤ c₀ * X.card :=
            mul_le_mul_of_nonneg_right hmin_le (Nat.cast_nonneg _)
        _ ≤ (B'.card : ℝ) := hB'lb
    · -- |A' - B'| ≤ ((C₀/c₀)^3/c₀ + 1) * n
      have hone_n_nn : (0 : ℝ) ≤ 1 * (X.card : ℝ) := by positivity
      have hexp : ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) =
          ((C₀ / c₀) ^ 3 / c₀) * X.card + (X.card : ℝ) := by ring
      rw [hexp]
      linarith
  · -- Small case: (η/2) * n < 2. Use singletons.
    push Not at hLarge
    obtain ⟨x, hxX⟩ := hX
    obtain ⟨y, hyY⟩ := hY
    refine ⟨{x}, {y}, Finset.singleton_subset_iff.mpr hxX,
        Finset.singleton_subset_iff.mpr hyY, ?_, ?_, ?_⟩
    · -- min c₀ (η/4) * n ≤ 1
      have hmin_le_q : min c₀ (η / 4) ≤ η / 4 := min_le_right _ _
      have hbnd : min c₀ (η / 4) * (X.card : ℝ) ≤ (η / 4) * n :=
        mul_le_mul_of_nonneg_right hmin_le_q (Nat.cast_nonneg _)
      have h_q_n : (η / 4) * (n : ℝ) < 1 := by linarith
      have hcard : (({x} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; linarith
    · -- min c₀ (η/4) * Y.card ≤ 1
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      rw [hYn]
      have hmin_le_q : min c₀ (η / 4) ≤ η / 4 := min_le_right _ _
      have hbnd : min c₀ (η / 4) * (X.card : ℝ) ≤ (η / 4) * n :=
        mul_le_mul_of_nonneg_right hmin_le_q (Nat.cast_nonneg _)
      have h_q_n : (η / 4) * (n : ℝ) < 1 := by linarith
      have hcard : (({y} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; linarith
    · -- |{x} - {y}| ≤ ((C₀/c₀)^3/c₀ + 1) * n
      have hsub_card : (({x} - {y} : Finset G)).card = 1 := by
        rw [Finset.singleton_sub_singleton]; simp
      have hcard1 : ((({x} - {y} : Finset G)).card : ℝ) = 1 := by
        rw [hsub_card]; simp
      rw [hcard1]
      have hpos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
      have hone_le : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) * X.card := by
        have h1 : (1 : ℝ) ≤ (X.card : ℝ) := hn_ge_one
        have h2 : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) := by linarith
        nlinarith
      exact hone_le


/--
**Balog-Szemerédi-Gowers (symmetric, qualitative form).** For every
`η > 0` there exist positive `c, C` such that whenever `X` is a finite
subset of an additive commutative group with additive energy
`E[X,X] ≥ η · |X|³`, there is a subset `X' ⊆ X` of size `≥ c · |X|`
whose difference set is bounded: `|X' - X'| ≤ C · |X|`. Qualitative
existentials only; for explicit polynomial-in-`η` constants see
`balog_szemeredi_gowers_asymmetric_explicit`.
-/
theorem balog_szemeredi_gowers_symmetric {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ X : Finset G, X.Nonempty →
        η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X X : ℝ) →
        ∃ X' : Finset G, X' ⊆ X ∧
          c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          ((X' - X').card : ℝ) ≤ C * (X.card : ℝ) := by
  intro η hη
  obtain ⟨c, C, hc, hC, hAsym⟩ := balog_szemeredi_gowers_asymmetric (G := G) η hη
  refine ⟨c, C ^ 2 / c, hc, by positivity, ?_⟩
  intro X hX hE
  -- Apply asymmetric with Y := X
  obtain ⟨X', Y', hX'sub, hY'sub, hX'lb, hY'lb, hXmY'⟩ :=
    hAsym X X hX hX rfl hE
  refine ⟨X', hX'sub, hX'lb, ?_⟩
  -- Ruzsa triangle: #(X' - X') * #Y' ≤ #(X' - Y') * #(X' - Y')
  have hRuzsaℕ : (X' - X').card * Y'.card ≤ (X' - Y').card * (X' - Y').card :=
    Finset.ruzsa_triangle_inequality_sub_sub_sub X' Y' X'
  have hRuzsa : ((X' - X').card : ℝ) * (Y'.card : ℝ) ≤
      ((X' - Y').card : ℝ) * ((X' - Y').card : ℝ) := by exact_mod_cast hRuzsaℕ
  -- Numeric bookkeeping
  have hXne : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hcX_pos : (0 : ℝ) < c * X.card := mul_pos hc hXne
  have hY'pos : (0 : ℝ) < (Y'.card : ℝ) := by linarith
  have hXmY_nn : (0 : ℝ) ≤ ((X' - Y').card : ℝ) := Nat.cast_nonneg _
  have hCXnn : (0 : ℝ) ≤ C * X.card := by positivity
  have hsq : ((X' - Y').card : ℝ) * ((X' - Y').card : ℝ) ≤ (C * X.card) * (C * X.card) :=
    mul_le_mul hXmY' hXmY' hXmY_nn hCXnn
  have hchain : ((X' - X').card : ℝ) * Y'.card ≤ (C * X.card) ^ 2 := by
    rw [sq]; linarith
  -- (X'-X').card · (c|X|) ≤ (X'-X').card · |Y'| ≤ (C|X|)²
  have hX'diff_nn : (0 : ℝ) ≤ ((X' - X').card : ℝ) := Nat.cast_nonneg _
  have step : ((X' - X').card : ℝ) * (c * X.card) ≤ (C * X.card) ^ 2 :=
    calc ((X' - X').card : ℝ) * (c * X.card)
        ≤ ((X' - X').card : ℝ) * (Y'.card : ℝ) :=
            mul_le_mul_of_nonneg_left hY'lb hX'diff_nn
      _ ≤ (C * X.card) ^ 2 := hchain
  have final : ((X' - X').card : ℝ) ≤ (C * X.card) ^ 2 / (c * X.card) :=
    (le_div_iff₀ hcX_pos).mpr (by linarith)
  have hrw : (C * X.card) ^ 2 / (c * X.card) = C ^ 2 / c * X.card := by
    have hc_ne : (c : ℝ) ≠ 0 := hc.ne'
    have hX_ne : (X.card : ℝ) ≠ 0 := hXne.ne'
    field_simp
  rw [hrw] at final
  exact final

/--
**Balog-Szemerédi-Gowers (asymmetric, equal-cardinality, explicit-constant
form).**  Sibling of `balog_szemeredi_gowers_asymmetric` whose theorem
type exposes the polynomial-in-`η` witnesses `c = η/16` and
`C = (C₀/c₀)^3 / c₀ + 1` (with the internal `c₀ = η/16` and
`C₀ = 2^13·(4/η)^3 / (η/2)^5 + 2^12 / (η/2)^5`) rather than hiding them
under an existential.

This form is needed whenever one must track how the output doubling constant
depends polynomially on `η` — for instance to substitute a varying
`η = η(n)` and read off the resulting exponent. The qualitative form
(`balog_szemeredi_gowers_asymmetric`) returns arbitrary witnesses via
`Classical.choose`, which hides that dependence.

The hypothesis `η ≤ 1` is added so that `min c₀ (η/4) = c₀ = η/16`
(else the `c` value would be `min (η/16) (η/4)`, which equals `η/16`
for all `η > 0` anyway but with a less convenient definitional form).
-/
theorem balog_szemeredi_gowers_asymmetric_explicit {G : Type*} [AddCommGroup G] [DecidableEq G]
    (η : ℝ) (hη : 0 < η) (_hη_le : η ≤ 1)
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : X.card = Y.card)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ)) :
    ∃ X' Y' : Finset G, X' ⊆ X ∧ Y' ⊆ Y ∧
      (η / 16) * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
      (η / 16) * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
      ((X' - Y').card : ℝ) ≤
        (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
            / (η / 16) + 1) * (X.card : ℝ) := by
  -- Mirror the qualitative proof but with `graph_balogSzemerediGowers_restricted_sumset_explicit`
  -- in place of `graph_balogSzemerediGowers_restricted_sumset`, so the inner constants `c₀, C₀`
  -- are definitionally `η/16` and `2^13·(4/η)^3/(η/2)^5 + 2^12/(η/2)^5`.
  -- Introduce local names matching the qualitative proof.
  set c₀ : ℝ := η / 16 with hc₀_def
  set C₀ : ℝ := 2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5 with hC₀_def
  have hδ_pos : (0 : ℝ) < η / 2 := by linarith
  have hK_pos : (0 : ℝ) < 4 / η := by positivity
  -- c₀ = η/16 = (η/2)/8 — this is the c from graph_balogSzemerediGowers_restricted_sumset_explicit.
  have hc₀_eq : c₀ = (η / 2) / 8 := by rw [hc₀_def]; ring
  have hc₀ : (0 : ℝ) < c₀ := by rw [hc₀_def]; linarith
  have hC₀ : (0 : ℝ) < C₀ := by rw [hC₀_def]; positivity
  set n : ℕ := X.card with hn_def
  have hYcard : Y.card = n := hXY.symm
  have hnpos : 0 < n := hX.card_pos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  -- Case split on whether n is "large" or "small".
  by_cases hLarge : 2 ≤ (η / 2) * n
  · -- Substantive case: n ≥ 4/η, so floor((η/2)*n) ≥ 1 and ≥ (η/4)*n.
    set θ : ℕ := Nat.floor ((η / 2) * (n : ℝ)) with hθ_def
    have hηn_nn : 0 ≤ (η / 2) * (n : ℝ) := by positivity
    have hθ_floor_le : (θ : ℝ) ≤ (η / 2) * n := Nat.floor_le hηn_nn
    have hθ_floor_ge : (η / 2) * (n : ℝ) - 1 < θ := by
      have := Nat.lt_floor_add_one ((η / 2) * (n : ℝ))
      linarith
    have hθ_pos : 1 ≤ θ := by
      have : (1 : ℝ) ≤ θ := by linarith
      exact_mod_cast this
    have hθ_posR : (0 : ℝ) < θ := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hθ_pos)
    have h_2θ_le : 2 * (θ : ℝ) ≤ η * n := by
      have := hθ_floor_le
      linarith
    have hθ_ge_quarter : (η / 4) * (n : ℝ) ≤ θ := by
      have h1 : (η / 2) * (n : ℝ) - 1 ≤ θ := le_of_lt hθ_floor_ge
      have h2 : (1 : ℝ) ≤ (η / 4) * n := by linarith
      linarith
    set E : Finset (G × G) :=
      (X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2)) with hE_def
    have hE_sub : E ⊆ X ×ˢ Y := Finset.filter_subset _ _
    have hPP := popular_pairs_card_lower_bound hη hXY hX hE θ h_2θ_le
    have hE_lb : (η / 2) * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have : (η / 2) * (n : ℝ) * Y.card = (η / 2) * (n : ℝ) ^ 2 := by
        rw [hYcard]; ring
      linarith
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hS_popular : ∀ s ∈ S, θ ≤ X.addConvolution Y s := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter] at hpE
      rw [← hps]; exact hpE.2
    have hS_sub : S ⊆ X + Y := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter, Finset.mem_product] at hpE
      rw [← hps]
      exact Finset.add_mem_add hpE.1.1 hpE.1.2
    have hSum_eq : ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card :=
      sum_addConvolution_eq_card_product X Y
    have hSum_S_le : (S.card : ℕ) * θ ≤ X.card * Y.card := by
      calc (S.card : ℕ) * θ
          = ∑ _s ∈ S, θ := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ s ∈ S, X.addConvolution Y s :=
            Finset.sum_le_sum hS_popular
        _ ≤ ∑ s ∈ X + Y, X.addConvolution Y s :=
            Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun _ _ _ ↦ Nat.zero_le _)
        _ = X.card * Y.card := hSum_eq
    have hSum_S_le_R : (S.card : ℝ) * θ ≤ (n : ℝ) ^ 2 := by
      have h : ((S.card * θ : ℕ) : ℝ) ≤ ((X.card * Y.card : ℕ) : ℝ) := by
        exact_mod_cast hSum_S_le
      push_cast at h
      rw [hYcard] at h
      have hgoal : (n : ℝ) ^ 2 = (n : ℝ) * n := by ring
      rw [hgoal]; exact h
    have hS_le : (S.card : ℝ) ≤ (4 / η) * n := by
      have hS_le_nθ : (S.card : ℝ) ≤ (n : ℝ) ^ 2 / θ := by
        rw [le_div_iff₀ hθ_posR]; exact hSum_S_le_R
      have hbnd : (n : ℝ) ^ 2 / θ ≤ (4 / η) * n := by
        rw [div_le_iff₀ hθ_posR]
        have hηpos : 0 < η := hη
        have h_θ_pos_q : (0 : ℝ) < (η / 4) * n := by positivity
        have h1 : (n : ℝ) ^ 2 = n * n := by ring
        rw [h1]
        have h_4η_pos : (0 : ℝ) < 4 / η := by positivity
        have hθ_ge' : (η / 4) * (n : ℝ) ≤ θ := hθ_ge_quarter
        have : (4 / η) * (n : ℝ) * ((η / 4) * n) = n * n := by
          field_simp
        have hmul : (4 / η) * (n : ℝ) * ((η / 4) * n) ≤ (4 / η) * n * θ :=
          mul_le_mul_of_nonneg_left hθ_ge'
            (by positivity)
        linarith
      linarith
    have hδ : (η / 2) * (X.card : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      rw [← hn_def]; exact hE_lb
    have hK : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ (4 / η) * (X.card : ℝ) := by
      rw [← hn_def, ← hS_def]; exact hS_le
    -- Use the explicit graph-BSG. The c₀ = (η/2)/8 from the explicit version
    -- equals η/16 = c₀ by `ring`.
    obtain ⟨A', B', hA'sub, hB'sub, hA'lb_raw, hB'lb_raw, hAB'sumset_raw⟩ :=
      graph_balogSzemerediGowers_restricted_sumset_explicit (η / 2) (4 / η) hδ_pos hK_pos
        X Y hX hY hXY E hE_sub hδ hK
    -- Rewrite (η/2)/8 to η/16 and the explicit C₀ form.
    have hA'lb : c₀ * (X.card : ℝ) ≤ (A'.card : ℝ) := by
      rw [hc₀_eq]; exact hA'lb_raw
    have hB'lb : c₀ * (X.card : ℝ) ≤ (B'.card : ℝ) := by
      rw [hc₀_eq]; exact hB'lb_raw
    have hAB'sumset : ((A' + B').card : ℝ) ≤ C₀ * (X.card : ℝ) := by
      rw [hC₀_def]; exact hAB'sumset_raw
    -- Now mirror the rest of the qualitative proof.
    have hA'pos : 0 < A'.card := by
      have : (0 : ℝ) < (A'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hA'ne : A'.Nonempty := Finset.card_pos.mp hA'pos
    have hB'pos : 0 < B'.card := by
      have : (0 : ℝ) < (B'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hB'ne : B'.Nonempty := Finset.card_pos.mp hB'pos
    have hSumK : ((A' + B').card : ℝ) ≤ (C₀ / c₀) * A'.card := by
      have hC₀n_le : (C₀ : ℝ) * X.card ≤ (C₀ / c₀) * (c₀ * X.card) := by
        rw [show (C₀ / c₀) * (c₀ * (X.card : ℝ)) = C₀ * X.card by
          field_simp]
      have hcalc : (C₀ / c₀) * (c₀ * (X.card : ℝ)) ≤ (C₀ / c₀) * A'.card := by
        have hC₀c₀_pos : (0 : ℝ) < C₀ / c₀ := by positivity
        exact mul_le_mul_of_nonneg_left hA'lb (le_of_lt hC₀c₀_pos)
      linarith
    have hA'le_n : (A'.card : ℝ) ≤ n := by
      have : A'.card ≤ X.card := Finset.card_le_card hA'sub
      exact_mod_cast this
    have hBal : c₀ * (A'.card : ℝ) ≤ (B'.card : ℝ) := by
      have hc₀A'_le_c₀n : c₀ * (A'.card : ℝ) ≤ c₀ * X.card :=
        mul_le_mul_of_nonneg_left hA'le_n (le_of_lt hc₀)
      linarith
    obtain hRuzsa := ruzsa_sumset_to_difference (G := G)
      (C₀ / c₀) c₀ (by positivity) hc₀ A' B' hA'ne hB'ne hSumK hBal
    have hAmB'_le : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * n := by
      have h1 : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * A'.card := hRuzsa
      have hcoef_nn : (0 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) := by positivity
      have h2 : ((C₀ / c₀) ^ 3 / c₀) * A'.card ≤ ((C₀ / c₀) ^ 3 / c₀) * n :=
        mul_le_mul_of_nonneg_left hA'le_n hcoef_nn
      linarith
    refine ⟨A', B', hA'sub, hB'sub, ?_, ?_, ?_⟩
    · -- η/16 * X.card ≤ |A'|
      have : (η / 16) * (X.card : ℝ) = c₀ * X.card := by rw [hc₀_def]
      rw [this]; exact hA'lb
    · -- η/16 * Y.card ≤ |B'|
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      have h1 : (η / 16) * (Y.card : ℝ) = c₀ * X.card := by
        rw [hc₀_def, hYn]
      rw [h1]; exact hB'lb
    · -- |A' - B'| ≤ ((C₀/c₀)^3/c₀ + 1) * n, then rewrite to match the explicit form.
      have hone_n_nn : (0 : ℝ) ≤ 1 * (X.card : ℝ) := by positivity
      have hexp : ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) =
          ((C₀ / c₀) ^ 3 / c₀) * X.card + (X.card : ℝ) := by ring
      have hAmB'_total : ((A' - B').card : ℝ) ≤
          ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) := by
        rw [hexp]; linarith
      -- Unfold c₀ and C₀ definitions to match the explicit signature.
      have hunfold : ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) =
          (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
              / (η / 16) + 1) * (X.card : ℝ) := by
        rw [hC₀_def, hc₀_def]
      rw [← hunfold]
      exact hAmB'_total
  · -- Small case: (η/2) * n < 2. Use singletons.
    push Not at hLarge
    obtain ⟨x, hxX⟩ := hX
    obtain ⟨y, hyY⟩ := hY
    refine ⟨{x}, {y}, Finset.singleton_subset_iff.mpr hxX,
        Finset.singleton_subset_iff.mpr hyY, ?_, ?_, ?_⟩
    · -- η/16 * n ≤ 1, since (η/2) * n < 2 ⇒ η * n < 4 ⇒ (η/16) * n < 1/4 ≤ 1.
      have h_half : η * (n : ℝ) < 4 := by linarith
      have h_q_n : (η / 16) * (n : ℝ) ≤ 1 := by nlinarith
      have hcard : (({x} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; exact h_q_n
    · -- η/16 * Y.card ≤ 1
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      rw [hYn]
      have h_half : η * (n : ℝ) < 4 := by linarith
      have h_q_n : (η / 16) * (n : ℝ) ≤ 1 := by nlinarith
      have hcard : (({y} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; exact h_q_n
    · -- |{x} - {y}| = 1 ≤ (C(η) + 1) * n. The bracket is C₀/c₀-cubed-over-c₀ + 1 ≥ 1.
      have hsub_card : (({x} - {y} : Finset G)).card = 1 := by
        rw [Finset.singleton_sub_singleton]; simp
      have hcard1 : ((({x} - {y} : Finset G)).card : ℝ) = 1 := by
        rw [hsub_card]; simp
      rw [hcard1]
      -- The big bracket equals (C₀/c₀)^3/c₀ + 1 by definition; show it's ≥ 1.
      have hC_div_pos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
      have h_bracket_eq :
          (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
              / (η / 16) + 1)
            = ((C₀ / c₀) ^ 3 / c₀ + 1) := by
        show (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
              / (η / 16) + 1) = ((C₀ / c₀) ^ 3 / c₀ + 1)
        congr 1
      rw [h_bracket_eq]
      have hbracket_ge_one : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) := by linarith
      have hX_ge_one : (1 : ℝ) ≤ (X.card : ℝ) := hn_ge_one
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) * X.card :=
            mul_le_mul hbracket_ge_one hX_ge_one (by norm_num) (by linarith)

end Finset

open scoped Pointwise

namespace Erdos101TriangleRatios

/-- A real-valued doubling bound from a bound on the difference set. -/
theorem doubling_of_small_difference {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (hA : A.Nonempty) (K : ℝ)
    (hK : ((A - A).card : ℝ) ≤ K * A.card) :
    ((A + A).card : ℝ) ≤ K ^ 2 * A.card := by
  have hpos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hPR : ((2 • A).card : ℚ≥0) ≤
      (((A - A).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) :=
    Finset.pluennecke_ruzsa_inequality_nsmul_sub hA A 2
  rw [two_nsmul] at hPR
  have hreal : ((A + A).card : ℝ) ≤
      (((A - A).card : ℝ) / (A.card : ℝ)) ^ 2 * (A.card : ℝ) := by
    have hcast : ((A + A).card : ℝ) ≤
        ((((A - A).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) : ℝ) := by
      exact_mod_cast hPR
    simpa using hcast
  have hr := (div_le_iff₀ hpos).mpr hK
  exact hreal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hpos.le) hr 2) hpos.le)

/-- The conclusion uses the subset itself as the denominator of its doubling constant. -/
theorem energy_doubling_of_symmetric_bsg {G : Type*} [AddCommGroup G] [DecidableEq G]
    (η : ℝ) (hη : 0 < η)
    (bsg : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Q : Finset G, Q.Nonempty →
      η * (Q.card : ℝ) ^ 3 ≤ (Q.addEnergy Q : ℝ) →
      ∃ A ⊆ Q, c * (Q.card : ℝ) ≤ (A.card : ℝ) ∧
        ((A - A).card : ℝ) ≤ C * (Q.card : ℝ)) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ Q : Finset G, Q.Nonempty →
      η * (Q.card : ℝ) ^ 3 ≤ (Q.addEnergy Q : ℝ) →
      ∃ A ⊆ Q, c * (Q.card : ℝ) ≤ (A.card : ℝ) ∧
        ((A + A).card : ℝ) ≤ K * (A.card : ℝ) := by
  obtain ⟨c, C, hc, hC, large⟩ := bsg
  refine ⟨c, (C / c)^2, hc, by positivity, ?_⟩
  intro Q hQ henergy
  obtain ⟨A, hAQ, hsize, hdiff⟩ := large Q hQ henergy
  have hQpos : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hApos := (mul_pos hc hQpos).trans_le hsize
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hd : ((A - A).card : ℝ) ≤ C / c * A.card := by
    calc
      _ ≤ C * Q.card := hdiff
      _ = C / c * (c * Q.card) := by field_simp [ne_of_gt hc]
      _ ≤ C / c * A.card := mul_le_mul_of_nonneg_left hsize (div_nonneg hC.le hc.le)
  exact ⟨A, hAQ, hsize, doubling_of_small_difference A hA _ hd⟩

end Erdos101TriangleRatios

/-! Finite integer models reflecting bounded three-point affine relations. -/

open scoped Pointwise
namespace OMA.IntegerModel

private lemma integral_functional {V : Type*} [AddCommGroup V] [Module ℚ V]
    [DecidableEq V] (A D : Finset V) :
    ∃ F : V →ₗ[ℚ] ℚ, (∀ x ∈ A, ∃ z : ℤ, F x = z) ∧
      ∀ x ∈ D, F x = 0 → x = 0 := by
  classical
  let E := D.erase 0
  obtain ⟨L, hL⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ)
    (fun x : E => (x : V)) (fun x => (Finset.mem_erase.mp x.property).1)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) A (fun x => L x)
  have hs0 : (s : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  refine ⟨((s : ℤ) : ℚ) • L, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz⟩ := hs x hx
    exact ⟨z, by simpa [zsmul_eq_mul] using hz.symm⟩
  · intro x hx h
    by_contra hne
    have hLx := hL ⟨x, Finset.mem_erase.mpr ⟨hne, hx⟩⟩
    have sQ : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hs0
    exact (mul_ne_zero sQ hLx) h

/-- A finite real-vector configuration admits an integer model with small sumset
and a prescribed bound on the coefficients of all reflected affine relations. -/
theorem exists_relation_model {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq V] (Q : Finset V) (M : ℕ) :
    ∃ f : V → ℤ, Set.InjOn f (Q : Set V) ∧
      (Q.image f + Q.image f).card ≤ (Q + Q).card ∧
      ∀ u ∈ Q, ∀ v ∈ Q, ∀ w ∈ Q, ∀ a b : ℤ,
        |a| ≤ (M : ℤ) → |b| ≤ (M : ℤ) →
        a * (f u - f w) = b * (f v - f w) →
        (a : ℝ) • (u - w) = (b : ℝ) • (v - w) := by
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
  let B := Q ∪ (Q + Q)
  let I := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let E := (I ×ˢ (Q - Q)).image (fun p : ℤ × V => p.1 • p.2)
  let D := (Q - Q) ∪ (E - E)
  obtain ⟨L, hint, hzero⟩ := integral_functional B D
  let f : V → ℤ := fun x => ⌊L x⌋
  have heq {x : V} (hx : x ∈ B) : L x = (f x : ℚ) := by
    obtain ⟨z, hz⟩ := hint x hx
    simp [f, hz]
  have hQ {x : V} (hx : x ∈ Q) : L x = (f x : ℚ) :=
    heq (Finset.mem_union_left _ hx)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    apply sub_eq_zero.mp
    apply hzero _ (Finset.mem_union_left _ (Finset.sub_mem_sub hx hy))
    rw [map_sub, hQ hx, hQ hy, hxy, sub_self]
  · apply (Finset.card_le_card (t := (Q + Q).image f) ?_).trans Finset.card_image_le
    intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_image.mpr ⟨x + y, Finset.add_mem_add hx hy, ?_⟩
    have hsum := heq (Finset.mem_union_right Q (Finset.add_mem_add hx hy))
    rw [map_add, hQ hx, hQ hy] at hsum
    exact_mod_cast hsum.symm
  · intro u hu v hv w hw a b ha hb hab
    have hmem (i : ℤ) (hi : |i| ≤ (M : ℤ)) (x : V) (hx : x ∈ Q) :
        i • (x - w) ∈ E :=
      Finset.mem_image.mpr ⟨(i, x - w), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr (abs_le.mp hi), Finset.sub_mem_sub hx hw⟩, rfl⟩
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    apply sub_eq_zero.mp
    apply hzero _ (Finset.mem_union_right _ (Finset.sub_mem_sub (hmem a ha u hu) (hmem b hb v hv)))
    simp only [map_sub, map_zsmul, zsmul_eq_mul, hQ hu, hQ hv, hQ hw]
    exact sub_eq_zero.mpr (by exact_mod_cast hab)

end OMA.IntegerModel

namespace OMA.GapFiber

/-- A bounded-order integer model transports any single arithmetic-progression
fiber of the covering generalized progression to a real affine line. -/
theorem collinear_of_integer_fiber {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q A : Finset V) (hA : A ⊆ Q) (f : V → ℤ) (hf : Set.InjOn f (Q : Set V))
    (M : ℕ)
    (model : ∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, ∀ a b : ℤ,
      |a| ≤ (M : ℤ) → |b| ≤ (M : ℤ) →
      a * (f x - f z) = b * (f y - f z) →
      (a : ℝ) • (x-z) = (b : ℝ) • (y-z))
    (c d : ℤ) (t : V → ℤ) (ht : ∀ x ∈ A, 0 ≤ t x ∧ t x ≤ (M:ℤ) ∧ f x = c + t x * d) :
    Collinear ℝ (A : Set V) := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨z,hz⟩ := hne
    rw [collinear_iff_of_mem (k := ℝ) (show z ∈ (A : Set V) from hz)]
    by_cases hs : ∃ y ∈ A, y ≠ z
    · obtain ⟨y,hy,hyz⟩ := hs
      obtain ⟨hy₀,hyM,hyf⟩ := ht y hy
      obtain ⟨hz₀,hzM,hzf⟩ := ht z hz
      have hne : t y - t z ≠ 0 := by
        intro he
        apply hyz
        apply hf (hA hy) (hA hz)
        rw [hyf,hzf,sub_eq_zero.mp he]
      have hneR : ((t y - t z : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
      refine ⟨y-z,?_⟩
      intro x hx
      obtain ⟨hx₀,hxM,hxf⟩ := ht x hx
      have eqn := model x (hA hx) y (hA hy) z (hA hz) (t y-t z) (t x-t z)
        (abs_le.mpr (by omega)) (abs_le.mpr (by omega)) (by rw [hyf,hzf,hxf]; ring)
      refine ⟨((t y - t z : ℤ) : ℝ)⁻¹ * ((t x - t z : ℤ) : ℝ),?_⟩
      have h := congrArg (fun v : V => ((t y - t z : ℤ) : ℝ)⁻¹ • v) eqn
      simp only [←mul_smul,inv_mul_cancel₀ hneR,one_smul] at h
      change x = _ + z
      exact sub_eq_iff_eq_add.mp h
    · refine ⟨0,?_⟩
      intro x hx
      have hxz : x = z := by by_contra hn; exact hs ⟨x,hx,hn⟩
      exact ⟨0,by simp [hxz]⟩
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hne] using (collinear_empty ℝ V)

/-- A capped set with an integer model in a rank-r box of size at most C times
its own cardinality has at most (k*C)^r points. The box may be improper.
Every coordinate fiber has at most k points, so each side has length at most k*C. -/
theorem card_le_of_integer_box {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : Finset V) (hQ : Q.Nonempty) (f : V → ℤ) (hf : Set.InjOn f (Q : Set V))
    (k C r : ℕ) (length : Fin r → ℕ) (base : ℤ) (step : Fin r → ℤ)
    (enc : V → (i : Fin r) → Fin (length i + 1))
    (cover : ∀ x ∈ Q, f x = base + ∑ i, ((enc x i : ℕ) : ℤ) * step i)
    (hbox : (∏ i, (length i + 1)) ≤ C * Q.card)
    (cap : ∀ A : Finset V, A ⊆ Q → Collinear ℝ (A : Set V) → A.card ≤ k)
    (model : ∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, ∀ a b : ℤ,
      |a| ≤ ((C * Q.card : ℕ) : ℤ) → |b| ≤ ((C * Q.card : ℕ) : ℤ) →
      a * (f x - f z) = b * (f y - f z) →
      (a : ℝ) • (x-z) = (b : ℝ) • (y-z)) :
    Q.card ≤ (k*C)^r := by
  classical
  let volume := ∏ i, (length i + 1)
  have hfull : Q.card ≤ volume := by
    calc
      _ = (Q.image enc).card := (Finset.card_image_of_injOn (by
        intro x hx y hy e
        apply hf hx hy
        rw [cover x hx,cover y hy,e])).symm
      _ ≤ (Finset.univ : Finset ((i : Fin r) → Fin (length i + 1))).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = _ := by simp [volume,Fintype.card_pi]
  have side (i : Fin r) : length i+1 ≤ k*C := by
    let Off := (j : {j : Fin r // j ≠ i}) → Fin (length j + 1)
    let dropOff (x : V) : Off := fun j => enc x j
    let fiber (e : Off) := Q.filter fun x => dropOff x = e
    have hp : volume = (length i + 1) * Fintype.card Off := by
      simp only [volume,Off,Fintype.card_pi,Fintype.card_fin]
      exact Fintype.prod_eq_mul_prod_subtype_ne _ i
    have hparam : length i ≤ C * Q.card := by
      have hside := Finset.single_le_prod' (s := Finset.univ)
        (f := fun j => length j + 1) (fun j _ => by omega) (Finset.mem_univ i)
      exact (Nat.le_succ _).trans (hside.trans hbox)
    have bound (e : Off) : (fiber e).card ≤ k := by
      have hsub : fiber e ⊆ Q := Finset.filter_subset _ _
      apply cap _ hsub
      apply collinear_of_integer_fiber Q (fiber e) hsub f hf (C*Q.card) model
        (base + ∑ j, ((e j : ℕ) : ℤ) * step j) (step i) (fun x => ((enc x i : ℕ) : ℤ))
      intro x hx
      have hd := (Finset.mem_filter.mp hx).2
      refine ⟨by positivity,by exact_mod_cast (Nat.le_trans (Nat.le_of_lt_succ (enc x i).isLt) hparam),?_⟩
      rw [cover x (hsub hx),Fintype.sum_eq_add_sum_subtype_ne _ i]
      have hsum : (∑ j : {j : Fin r // j ≠ i}, ((enc x j : ℕ) : ℤ) * step j) =
          ∑ j, ((e j : ℕ) : ℤ) * step j := by
        apply Finset.sum_congr rfl
        intro j _
        have he : enc x j = e j := congrFun hd j
        rw [he]
      rw [hsum]
      abel
    have hpop : Q.card ≤ Fintype.card Off * k := by
      calc
        _ = ∑ e : Off, (fiber e).card :=
          Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (dropOff x))
        _ ≤ ∑ _e : Off, k := Finset.sum_le_sum fun e _ => bound e
        _ = _ := by simp
    have hh : (length i+1)*Q.card ≤ (k*C)*Q.card := calc
      _ ≤ (length i+1)*(Fintype.card Off*k) := Nat.mul_le_mul_left _ hpop
      _ = volume*k := by rw [hp]; ring
      _ ≤ (C*Q.card)*k := Nat.mul_le_mul_right _ hbox
      _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right hh (Finset.card_pos.mpr hQ)
  calc
    Q.card ≤ volume := hfull
    _ ≤ ∏ _i : Fin r, (k*C) := Finset.prod_le_prod' fun i _ => side i
    _ = _ := by simp

end OMA.GapFiber

open scoped Pointwise

namespace OMA.CappedDoubling

/-- Independently of the ambient dimension, a small-doubling real-vector set with
at most k points on a line has bounded cardinality. -/
theorem card_le {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V]
    (A : Finset V) (hA : A.Nonempty) (k K : ℕ) (hK : 1 ≤ K)
    (hd : (A + A).card ≤ K * A.card)
    (cap : ∀ T : Finset V, T ⊆ A → Collinear ℝ (T : Set V) → T.card ≤ k) :
    A.card ≤ (k * Erdos587.freimanSizeFactor K + 1) ^ Erdos587.freimanRank K := by
  classical
  let C := Erdos587.freimanSizeFactor K
  obtain ⟨f, hf, hsum, model⟩ := OMA.IntegerModel.exists_relation_model A (C * A.card)
  have hcard : (A.image f).card = A.card := Finset.card_image_of_injOn hf
  obtain ⟨P, hrank, hcover, hvol⟩ := Erdos587.exists_GAP_cover_of_small_doubling
    (A.image f) (hA.image _) K hK (by rw [hcard]; exact hsum.trans hd)
  have hrepr {x : V} (hx : x ∈ A) : ∃ p : P.Param, P.eval p = f x :=
    (P.mem_carrier_iff).mp (hcover (Finset.mem_image_of_mem _ hx))
  let enc (x : V) : P.Param := if hx : x ∈ A then (hrepr hx).choose else fun _ => 0
  have henc (x : V) (hx : x ∈ A) :
      f x = P.base + ∑ i, ((enc x i : ℕ) : ℤ) * P.step i := by
    simpa only [enc, dif_pos hx, Erdos587.GeneralizedAP.eval] using (hrepr hx).choose_spec.symm
  rw [hcard] at hvol
  have hb := OMA.GapFiber.card_le_of_integer_box A hA f hf k C P.rank
    P.length P.base P.step enc henc hvol cap model
  exact (hb.trans (Nat.pow_le_pow_left (Nat.le_succ _) _)).trans
    (Nat.pow_le_pow_right (by omega) hrank)

end OMA.CappedDoubling

open scoped Pointwise

namespace OMA.CappedEnergy

/-- A finite subset of a real vector space with at most k collinear points
has o(n^3) additive energy, uniformly even in the ambient dimension. -/
theorem sparse {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V] (k : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ Q : Finset V, N ≤ Q.card →
      (∀ T : Finset V, T ⊆ Q → Collinear ℝ (T : Set V) → T.card ≤ k) →
      (Q.addEnergy Q : ℝ) < η * (Q.card : ℝ)^3 := by
  classical
  obtain ⟨c, D, hc, _, dense⟩ :=
    Erdos101TriangleRatios.energy_doubling_of_symmetric_bsg (G := V) η hη
      (Finset.balog_szemeredi_gowers_symmetric η hη)
  let K := ⌈D⌉₊ + 1
  let B := (k * Erdos587.freimanSizeFactor K + 1) ^ Erdos587.freimanRank K
  obtain ⟨N, hN⟩ := exists_nat_gt ((B : ℝ) / c)
  refine ⟨N + 1, ?_⟩
  intro Q hn hcap
  by_contra! hE
  have hQ : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hAQ, hlarge, hd⟩ := dense Q hQ hE
  have hQpos : 0 < (Q.card : ℝ) := by exact_mod_cast hQ.card_pos
  have hApos := (mul_pos hc hQpos).trans_le hlarge
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hDK : D ≤ (K : ℝ) := (Nat.le_ceil _).trans (by dsimp [K]; push_cast; linarith)
  have hd' : (A+A).card ≤ K * A.card := by
    exact_mod_cast hd.trans (mul_le_mul_of_nonneg_right hDK (Nat.cast_nonneg _))
  have hB : A.card ≤ B := OMA.CappedDoubling.card_le A hA k K (by dsimp [K]; omega)
    hd' (fun T hT hcT => hcap T (hT.trans hAQ) hcT)
  have hB' : (A.card : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hn' : (N : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast (show N ≤ Q.card by omega)
  have hContra := (div_lt_iff₀ hc).mp hN
  linarith [mul_le_mul_of_nonneg_left hn' hc.le]

end OMA.CappedEnergy

end UniformEnergySparsity

section LiftEnergy

open EuclideanGeometry
open scoped Classical

namespace OMA.HomogeneousProgression

/-- Dehomogenizing an affine line in the lifted vector space produces a collinear set.
The assumptions include the nonvanishing of each homogeneous weight. -/
theorem collinear_of_parametrization
    {n : ℕ} [NeZero n] (x : Fin n → ℝ²) (w : Fin n → ℝˣ)
    (t : Fin n → ℝ) (p v : ℝ × ℝ²)
    (h : ∀ i, p + t i • v = (w i : ℝ) • ((1 : ℝ), x i)) :
    Collinear ℝ (Set.range x) := by
  let q := p + t 0 • v
  let u := fun i => t i - t 0
  have shifted (i : Fin n) : q + u i • v = (w i : ℝ) • ((1 : ℝ), x i) := by
    rw [← h i]
    dsimp only [q,u]
    module
  have hscale (i : Fin n) :
      q.1 + u i * v.1 = (w i : ℝ) := by
    simpa using congrArg Prod.fst (shifted i)
  have hvec (i : Fin n) :
      q.2 + u i • v.2 = (w i : ℝ) • x i := by
    exact congrArg Prod.snd (shifted i)
  have hbase : q.2 = q.1 • x 0 := by
    have ha := hscale 0
    have hb := hvec 0
    simp [u] at ha hb
    rw [ha, hb]
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨x 0, v.2 - v.1 • x 0, ?_⟩
  rintro _ ⟨i, rfl⟩
  refine ⟨u i / (w i : ℝ), ?_⟩
  change x i = _ • (v.2 - v.1 • x 0) + x 0
  apply smul_right_injective ℝ² (Units.ne_zero (w i))
  dsimp only
  rw [smul_add, smul_smul, mul_div_cancel₀ _ (Units.ne_zero _), ← hvec i, hbase, ← hscale i]
  module

/-- A single nonzero lift over each point of a cap-four configuration contains
no five distinct points of one parametrized affine line. -/
theorem no_five_collinear_parameters
    (S : Finset ℝ²) (hS : NonCollinearFor 5 (S : Set ℝ²)) (w : S → ℝˣ)
    (p v : ℝ × ℝ²) (hv : v ≠ 0) :
    ∀ (t : Fin 5 → ℝ), Function.Injective t → ¬ ∀ i : Fin 5, p + t i • v ∈
      (Finset.univ : Finset S).image (fun x => (w x : ℝ) • ((1 : ℝ), (x : ℝ²))) := by
  classical
  intro t ht hp
  have hx (i : Fin 5) : ∃ x : S, p + t i • v =
      (w x : ℝ) • ((1 : ℝ), (x : ℝ²)) := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (hp i)
    exact ⟨x, hx.symm⟩
  choose x hx using hx
  let f : Fin 5 → ℝ² := fun i => x i
  have hinj : Function.Injective f := by
    intro i j hij
    have he : x i = x j := Subtype.ext hij
    have hlin : t i • v = t j • v :=
      add_left_cancel ((hx i).trans (by rw [he, ← hx j]))
    have hsc : t i = t j := smul_left_injective ℝ hv hlin
    exact ht hsc
  apply hS (Set.range f) (by rintro _ ⟨i,rfl⟩; exact (x i).property) (Set.finite_range f)
  · simpa using Set.ncard_range_of_injective hinj
  · exact collinear_of_parametrization f (fun i => w (x i)) t p v hx

/-- The corresponding five-term arithmetic progression statement. -/
theorem no_five_term_progression
    (S : Finset ℝ²) (hS : NonCollinearFor 5 (S : Set ℝ²)) (w : S → ℝˣ)
    (p v : ℝ × ℝ²) (hv : v ≠ 0) :
    ¬ ∀ i : Fin 5, p + (i.val : ℝ) • v ∈
      (Finset.univ : Finset S).image (fun x => (w x : ℝ) • ((1 : ℝ), (x : ℝ²))) := by
  apply no_five_collinear_parameters S hS w p v hv
  intro i j hij
  change (i.val : ℝ) = (j.val : ℝ) at hij
  exact Fin.ext (by exact_mod_cast hij)

/-- Five distinct homogeneous lifts from one role cannot form any collinear
configuration, irrespective of their spacing along the affine line. -/
theorem no_five_collinear_lifts
    (S : Finset ℝ²) (hS : NonCollinearFor 5 (S : Set ℝ²)) (w : S → ℝˣ)
    (z : Fin 5 → ℝ × ℝ²) (hz : Function.Injective z)
    (hmem : ∀ i, z i ∈ (Finset.univ : Finset S).image
      (fun x => (w x : ℝ) • ((1 : ℝ), (x : ℝ²)))) :
    ¬ Collinear ℝ (Set.range z) := by
  intro hc
  obtain ⟨p,v,hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hc
  have he (i : Fin 5) : ∃ t : ℝ, z i = p + t • v := by
    obtain ⟨t,ht⟩ := hv (z i) ⟨i,rfl⟩
    exact ⟨t, by simpa [vadd_eq_add,add_comm] using ht⟩
  choose t ht using he
  have hn : v ≠ 0 := by
    intro hzero
    have heq : z 0 = z 1 := by simp [ht,hzero]
    have := hz heq
    exact (by decide : (0 : Fin 5) ≠ 1) this
  have hinj : Function.Injective t := fun i j hij =>
    hz (by rw [ht i, ht j, hij])
  exact no_five_collinear_parameters S hS w p v hn t hinj fun i =>
    ht i ▸ hmem i

end OMA.HomogeneousProgression


open EuclideanGeometry
open scoped Classical

namespace OMA.HomogeneousProgression

/-- Any collinear subset in one rescaled copy has at most four lifts. -/
theorem collinear_lift_card_le_four
    (S : Finset ℝ²) (hS : NonCollinearFor 5 (S : Set ℝ²)) (w : S → ℝˣ)
    (A : Finset (ℝ × ℝ²))
    (hA : A ⊆ (Finset.univ : Finset S).image
      (fun x => (w x : ℝ) • ((1 : ℝ), (x : ℝ²))))
    (hc : Collinear ℝ (A : Set (ℝ × ℝ²))) : A.card ≤ 4 := by
  classical
  by_contra! hn
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq (show 5 ≤ A.card from hn)
  let e : Fin 5 ≃ T := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let z : Fin 5 → ℝ × ℝ² := fun i => e i
  have hz : Function.Injective z := Subtype.val_injective.comp e.injective
  have hsub : Set.range z ⊆ (A : Set (ℝ × ℝ²)) := by
    rintro _ ⟨i,rfl⟩
    exact hT (e i).property
  exact no_five_collinear_lifts S hS w z hz
    (fun i => hA (hT (e i).property)) (Collinear.subset hsub hc)

/-- A collinear set in the union of two rescaled copies has at most eight lifts. -/
theorem collinear_two_lifts_card_le_eight
    (S : Finset ℝ²) (hS : NonCollinearFor 5 (S : Set ℝ²)) (u w : S → ℝˣ)
    (A : Finset (ℝ × ℝ²))
    (hA : A ⊆ ((Finset.univ : Finset S).image
      (fun x => (u x : ℝ) • ((1 : ℝ), (x : ℝ²)))) ∪
      ((Finset.univ : Finset S).image (fun x => (w x : ℝ) • ((1 : ℝ), (x : ℝ²)))))
    (hc : Collinear ℝ (A : Set (ℝ × ℝ²))) : A.card ≤ 8 := by
  classical
  let X := (Finset.univ : Finset S).image (fun x => (u x : ℝ) • ((1 : ℝ), (x : ℝ²)))
  let Y := (Finset.univ : Finset S).image (fun x => (w x : ℝ) • ((1 : ℝ), (x : ℝ²)))
  have split : A ⊆ (A ∩ X) ∪ (A ∩ Y) := by
    intro a ha
    rcases Finset.mem_union.mp (hA ha) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha,h⟩)
  have hx := collinear_lift_card_le_four S hS u (A ∩ X) (Finset.inter_subset_right)
    (Collinear.subset (by exact_mod_cast (Finset.inter_subset_left : A ∩ X ⊆ A)) hc)
  have hy := collinear_lift_card_le_four S hS w (A ∩ Y) (Finset.inter_subset_right)
    (Collinear.subset (by exact_mod_cast (Finset.inter_subset_left : A ∩ Y ⊆ A)) hc)
  exact (Finset.card_le_card split).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hx hy))

end OMA.HomogeneousProgression

namespace TriangleGauge


/-- A separate nonzero rescaling of every homogeneous point remains injective. -/
theorem homogeneous_injective {P V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : P → V) (hp : Function.Injective p) (s : P → ℝˣ) :
    Function.Injective (fun x => ((s x : ℝ) • ((1 : ℝ),p x))) := by
  intro x y h
  have he : (s x : ℝ) = s y := by simpa using congrArg Prod.fst h
  have hh : (s x : ℝ) • p x = (s y : ℝ) • p y := congrArg Prod.snd h
  rw [←he] at hh
  apply hp
  simpa [←mul_smul, (s x).ne_zero] using congrArg (fun v : V => (s x : ℝ)⁻¹ • v) hh


end TriangleGauge


namespace LiftedEnergy

open Finset

/-- Three injective point representations with many additive records yield
large self-energy of the union of the first two image sets. -/
theorem records_sq_le_self_energy {P G : Type*} [Fintype P] [AddCommGroup G]
    [DecidableEq G] (f g h : P → G) (hf : Function.Injective f)
    (hg : Function.Injective g) (hh : Function.Injective h)
    (U : Finset (P × P × P)) (hu : ∀ t ∈ U, f t.1 + g t.2.1 = h t.2.2) :
    let A := univ.image f ∪ univ.image g
    U.card^2 ≤ Fintype.card P * A.addEnergy A := by
  classical
  let X := univ.image f
  let Y := univ.image g
  let Z := univ.image h
  let R := (X ×ˢ Y).filter fun p => p.1 + p.2 ∈ Z
  have hU : U.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn (fun t => (f t.1,g t.2.1))
    · intro t ht
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_image_of_mem _ (mem_univ _),mem_image_of_mem _ (mem_univ _)⟩,?_⟩
      change f t.1 + g t.2.1 ∈ Z
      rw [hu t ht]
      exact mem_image_of_mem _ (mem_univ _)
    · rintro ⟨x,y,z⟩ ht ⟨x',y',z'⟩ ht' he
      have hx := hf (congrArg Prod.fst he)
      have hy := hg (congrArg Prod.snd he)
      change x = x' at hx
      change y = y' at hy
      subst x'
      subst y'
      have hz : z = z' := hh ((hu (x,y,z) ht).symm.trans (hu (x,y,z') ht'))
      exact Prod.ext rfl (Prod.ext rfl hz)
  have hz : Z.card = Fintype.card P := by
    dsimp [Z]
    rw [card_image_of_injOn hh.injOn, card_univ]
  have hcs : R.card ^ 2 ≤ Z.card * X.addEnergy Y := card_sq_le_card_mul_addEnergy X Y Z
  rw [hz] at hcs
  exact ((Nat.pow_le_pow_left hU 2).trans hcs).trans
    (Nat.mul_le_mul_left _ (addEnergy_mono subset_union_left subset_union_right))

end LiftedEnergy

namespace OMA.BoundedRatioEnergy

open EuclideanGeometry
open scoped Classical

/-- The fixed line-cap consequence of Mansfield–Passant, Theorem 5.4.
A generic projection of a finite spatial set to the plane preserves distinct
points and noncollinear triples and transports all additive quadruples. -/
def sparse_energy_of_line_cap : Prop :=
  ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ Q : Finset (ℝ × ℝ²), N ≤ Q.card →
    (∀ A : Finset (ℝ × ℝ²), A ⊆ Q → Collinear ℝ (A : Set (ℝ × ℝ²)) → A.card ≤ 8) →
    (Q.addEnergy Q : ℝ) < c * (Q.card : ℝ)^3

theorem additive_sparsity (hE : sparse_energy_of_line_cap) :
    OMA.R_Erdos101_erdos_101_R2_H2_R1.H2 := by
  classical
  intro ε he
  let c := ε^2/8
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N,hN⟩ := hE c hc
  refine ⟨max N 1,?_⟩
  intro S hs hcap u v w U hU
  let lift (s : S → ℝˣ) (p : S) := (s p : ℝ) • ((1 : ℝ),(p : ℝ²))
  have hi (s : S → ℝˣ) : Function.Injective (lift s) :=
    TriangleGauge.homogeneous_injective (fun p : S => (p : ℝ²)) Subtype.val_injective s
  let X := Finset.univ.image (lift u)
  let Y := Finset.univ.image (lift v)
  let Q := X ∪ Y
  have hx : X.card = S.card := by simp [X,Finset.card_image_of_injective _ (hi u)]
  have hy : Y.card = S.card := by simp [Y,Finset.card_image_of_injective _ (hi v)]
  have hlow : S.card ≤ Q.card := hx ▸ Finset.card_le_card Finset.subset_union_left
  have hupp : Q.card ≤ S.card + S.card := by simpa [Q,hx,hy] using Finset.card_union_le X Y
  have small := hN Q (((le_max_left N 1).trans hs).trans hlow)
    (fun A hA hcol => OMA.HomogeneousProgression.collinear_two_lifts_card_le_eight
      S hcap u v A hA hcol)
  have recN := LiftedEnergy.records_sq_le_self_energy (lift u) (lift v) (lift w)
    (hi u) (hi v) (hi w) U hU
  have recordBound : (U.card : ℝ)^2 ≤ S.card * (Q.addEnergy Q : ℝ) := by
    exact_mod_cast (show U.card^2 ≤ S.card * Q.addEnergy Q by simpa [Q,X,Y] using recN)
  have bnd : (Q.card : ℝ) ≤ (S.card : ℝ) + S.card := by exact_mod_cast hupp
  have hp : (0 : ℝ) < S.card := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) ((le_max_right N 1).trans hs))
  by_contra! hmany
  have bad : (U.card : ℝ)^2 < (U.card : ℝ)^2 := calc
    _ ≤ S.card * (Q.addEnergy Q : ℝ) := recordBound
    _ < S.card * (c * (Q.card : ℝ)^3) := mul_lt_mul_of_pos_left small hp
    _ ≤ S.card * (c * ((S.card : ℝ)+S.card)^3) := by gcongr
    _ = (ε * (S.card : ℝ)^2)^2 := by dsimp [c]; ring
    _ ≤ (U.card : ℝ)^2 := by gcongr
  exact lt_irrefl _ bad

end OMA.BoundedRatioEnergy

end LiftEnergy

theorem OMA.solution : OMA.R_Erdos101_erdos_101_R2_H2_R1.H2 := by
  exact OMA.BoundedRatioEnergy.additive_sparsity (OMA.CappedEnergy.sparse 8)
