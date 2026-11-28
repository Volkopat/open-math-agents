import OMAReductions.R_RiemannHypothesis_li_criterion_R1
import Mathlib
/-!
Under the Riemann hypothesis, 1 − 1/ρ has norm one. Twice the real part of
1 − (1 − 1/ρ)^n is the square of the distance to one. Its series converges
by the logarithmic count in unit height intervals. The Riemann–von Mangoldt
estimate gives infinitely many positive-height zeros, whereas only finitely
many phases can be nth roots of unity.

Conversely, positivity forces the first two defining series to converge. Their
summands give square summability of the gaps 1/ρ. If one phase has modulus r > 1,
choose b strictly between 1 and r. Only finitely many phases have modulus ≥ b.
Compactness gives powers for which all these phases point within a fixed arc of
the positive real axis. The contribution at modulus r is then negative of order
r^n, while a second-order bound makes the rest O(n² b^n). This contradicts
positivity. The real points of the open strip are excluded using Euler–Maclaurin.

The local count, gamma estimates, and Riemann–von Mangoldt formula below are
adapted from the indicated modules of
https://github.com/anthropics/zeta-23-lean/tree/3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
Their dependencies have been combined and adapted to the pinned Mathlib.
The unit-window summation estimates are adapted from @green-notes in open-math-agents PR 1912.

Zeta23 — a Lean 4 formalization of critical-line zero-proportion theorems
Copyright 2026 Anthropic, PBC

This product is licensed under the Apache License, Version 2.0 (see LICENSE).

This product includes software derived from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, licensed under the Apache License, Version 2.0.
The derived files are the ones under Zeta23/FromPNTPlus/; each carries its upstream notice
(source file, upstream commit, original copyright line) and a description of the local modifications.
Some of those files in turn derive from mathlib (https://github.com/leanprover-community/mathlib4),
Copyright the mathlib contributors, Apache License, Version 2.0; their original headers are preserved.

This product depends on, but does not include, Lean 4 (https://github.com/leanprover/lean4) and
mathlib4 with its standard dependency set — fetched by the build tool from their public repositories at the
revisions pinned in lake-manifest.json: batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient and
plausible are released under the Apache License, Version 2.0; Cli (leanprover/lean4-cli) is released under the
MIT License (Copyright (c) 2021 Marc Huisinga). None of these dependencies is included in this repository.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      “License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      “Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      “Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      “control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      “You” (or “Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      “Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      “Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      “Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      “Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      “Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, “submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as “Not a Contribution.”

      “Contributor” shall mean Licensor and any individual or Legal Entity
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

      (d) If the Work includes a “NOTICE” text file as part of its
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
      Contributor provides its Contributions) on an “AS IS” BASIS,
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
      boilerplate notice, with the fields enclosed by brackets “[]”
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same “printed page” as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the “License”);
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an “AS IS” BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.Defs -/
section
open scoped BigOperators ArithmeticFunction

open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

def l (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi))

def ell1 (T : ℝ) : ℝ := l T + 2 * Real.log 2 - 1

def D0 (T : ℝ) : ℝ := Real.sqrt T

def mu (τ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (Complex.digamma (1 / 4 + Complex.I * τ / 2)).re
    - Real.log Real.pi / (2 * Real.pi)

def reflect (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

structure ZeroConfig where
  
  carrier : Set ℂ
  
  mult : ℂ → ℕ
  one_le_mult : ∀ ρ ∈ carrier, 1 ≤ mult ρ
  strip : ∀ ρ ∈ carrier, 0 ≤ ρ.re ∧ ρ.re ≤ 1
  reflect_mem : ∀ ρ ∈ carrier, reflect ρ ∈ carrier
  mult_reflect : ∀ ρ ∈ carrier, mult (reflect ρ) = mult ρ
  
  finite_window : ∀ T₁ T₂ : ℝ, (carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

namespace ZeroConfig

variable (Z : ZeroConfig)

def window (T₁ T₂ : ℝ) : Set ℂ := Z.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}

def onLine : Set ℂ := {ρ | ρ.re = 1 / 2}

def simple : Set ℂ := {ρ | Z.mult ρ = 1}

def N (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ

end ZeroConfig

namespace Params

end Params

namespace ZeroConfig

def ZIprime (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.window (T - D0 T) (2 * T + D0 T)

def S1 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ Z.simple

def S2 (Z : ZeroConfig) (T : ℝ) : Set ℂ := Z.ZIprime T ∩ onLine ∩ {ρ | 2 ≤ Z.mult ρ}

def s1 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S1 T).ncard

def s2 (Z : ZeroConfig) (T : ℝ) : ℕ := (Z.S2 T).ncard

end ZeroConfig

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.Hypotheses -/
section
open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff

open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

structure GammaFacts : Prop where
  even : ∀ τ : ℝ, mu (-τ) = mu τ
  smooth : ContDiff ℝ ∞ mu
  monotoneOn : MonotoneOn mu (Ici 0)
  mu_zero_le : ∀ τ : ℝ, mu 0 ≤ mu τ
  neg_one_lt_mu_zero : -1 < mu 0
  stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2
  deriv_bound : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv mu τ| ≤ C / |τ|
  int_mu : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T
  int_mu_sq : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(∫ τ in T..(2 * T), mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.Defs.Counting -/
section
open Set

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma window_finite : (Z.window T₁ T₂).Finite := Z.finite_window T₁ T₂

lemma finsum_mult_mono {s t : Set ℂ} (hst : s ⊆ t) (ht : t ⊆ Z.window T₁ T₂) :
    ∑ᶠ ρ ∈ s, Z.mult ρ ≤ ∑ᶠ ρ ∈ t, Z.mult ρ := by
  have htf : t.Finite := (Z.window_finite T₁ T₂).subset ht
  have hsf : s.Finite := htf.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hsf, finsum_mem_eq_finite_toFinset_sum _ htf]
  apply Finset.sum_le_sum_of_subset
  exact Set.Finite.toFinset_subset_toFinset.mpr hst

end Zeta23.ZeroConfig

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.Statement -/
section
open scoped BigOperators ComplexConjugate

open Complex Set

noncomputable section

namespace Zeta23

def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

structure ZetaSeam : Prop where
  
  one_le_mult : ∀ ρ, IsNontrivialZero ρ → 1 ≤ zeroMult ρ
  
  reflect_zero : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ)
  
  mult_reflect : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ
  
  finite_window : ∀ T₁ T₂ : ℝ, ({ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

def zetaZeros (hs : ZetaSeam) : ZeroConfig where
  carrier := {ρ | IsNontrivialZero ρ}
  mult := zeroMult
  one_le_mult := hs.one_le_mult
  strip := fun _ h => ⟨h.2.1.le, h.2.2.le⟩
  reflect_mem := hs.reflect_zero
  mult_reflect := hs.mult_reflect
  finite_window := hs.finite_window

section seam_rfl

variable (hs : ZetaSeam) (T₁ T₂ : ℝ)

@[simp] lemma zetaZeros_carrier : (zetaZeros hs).carrier = {ρ | IsNontrivialZero ρ} := rfl

@[simp] lemma zetaZeros_mult : (zetaZeros hs).mult = zeroMult := rfl

lemma zetaZeros_window : (zetaZeros hs).window T₁ T₂ = zerosIn T₁ T₂ := by
  ext ρ; simp [ZeroConfig.window, zerosIn]

@[simp] lemma zetaZeros_N : (zetaZeros hs).N T₁ T₂ = Ncount T₁ T₂ := by
  simp [ZeroConfig.N, Ncount, zetaZeros_window]

end seam_rfl

lemma IsNontrivialZero.not_trivial {ρ : ℂ} (h : IsNontrivialZero ρ) :
    (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, rfl⟩
    have := h.2.1
    simp at this
    linarith
  · rintro rfl
    simpa using h.2.2

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.Statement.Seam -/
section
open Complex Set Filter Topology

noncomputable section

namespace Zeta23

lemma riemannZeta_analyticOnNhd_compl_one : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

lemma isConnected_compl_one : IsConnected ({1}ᶜ : Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1

lemma analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine riemannZeta_analyticOnNhd_compl_one.analyticOrderAt_ne_top_of_isPreconnected
    isConnected_compl_one.isPreconnected h2 hs ?_
  rw [(riemannZeta_analyticOnNhd_compl_one 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top

theorem ZetaSeam.one_le_mult_holds : ∀ ρ, IsNontrivialZero ρ → 1 ≤ zeroMult ρ := by
  intro ρ h
  have hρ1 : ρ ≠ 1 := h.not_trivial.2
  have han : AnalyticAt ℂ riemannZeta ρ := riemannZeta_analyticOnNhd_compl_one ρ hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr h.1
  have hnetop := analyticOrderAt_riemannZeta_ne_top hρ1
  unfold zeroMult
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega

lemma riemannZeta_zeros_locallyFinite (z : ℂ) :
    ∃ t ∈ 𝓝 z, (t ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  by_cases hz : z = 1
  · 
    subst hz
    have hres := riemannZeta_residue_one
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
      have : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
        hres.eventually_ne one_ne_zero
      exact this.mono fun s hs h => hs (by simp [h])
    rw [eventually_nhdsWithin_iff] at hev
    refine ⟨{s | s ∈ ({1}ᶜ : Set ℂ) → riemannZeta s ≠ 0}, hev, ?_⟩
    refine (Set.finite_empty).subset ?_
    rintro s ⟨hs, hs1, hz⟩
    exact hs hs1 hz
  · have hcod := (riemannZeta_analyticOnNhd_compl_one).eqOn_zero_or_eventually_ne_zero_of_preconnected
      isConnected_compl_one.isPreconnected
    rcases hcod with hzero | hcod
    · exfalso
      have : riemannZeta 2 = 0 := hzero (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) this
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
      obtain ⟨t, ht, hfin⟩ := hcod z hz
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs1, hs0⟩
      exact ⟨hst, hs1, by simpa using hs0⟩

theorem ZetaSeam.finite_window_holds (T₁ T₂ : ℝ) :
    ({ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  set K : Set ℂ := (Icc 0 1) ×ℂ (Icc T₁ T₂) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro ρ ⟨hρ, hT₁, hT₂⟩
  have hρK : ρ ∈ K := by
    refine ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, ⟨hT₁.le, hT₂⟩⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ.not_trivial.2, hρ.1⟩

theorem ZetaSeam.of_reflect
    (h₁ : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ))
    (h₂ : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ) : ZetaSeam :=
  ⟨ZetaSeam.one_le_mult_holds, h₁, h₂, ZetaSeam.finite_window_holds⟩

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.ZetaReflect -/
section
open Complex

open scoped ComplexConjugate

namespace Zeta23

private lemma zeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  have hs' : (1 : ℝ) < (conj s).re := by rwa [Complex.conj_re]
  rw [zeta_eq_tsum_one_div_nat_cpow hs', zeta_eq_tsum_one_div_nat_cpow hs]
  have hstar : star (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := tsum_star
  calc conj (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := hstar
    _ = ∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ s := by
        congr 1
        funext n
        have harg : ((n : ℂ)).arg ≠ Real.pi := by
          rw [Complex.natCast_arg]
          exact Ne.symm Real.pi_ne_zero
        have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
          have h := Complex.cpow_conj (n : ℂ) s harg
          rwa [Complex.conj_natCast] at h
        show star ((1 : ℂ) / (n : ℂ) ^ (conj s)) = 1 / (n : ℂ) ^ s
        rw [star_div₀, star_one, hpow]
        simp

theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hU_conn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 1).isConnected.isPreconnected
  have hζ : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have hζt : AnalyticOnNhd ℂ (fun z => conj (riemannZeta (conj z))) ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hz1 : conj z ≠ 1 := by
      intro h
      have h2 := congrArg (starRingEnd ℂ) h
      simp only [Complex.conj_conj, map_one] at h2
      exact (by simpa using hz : z ≠ 1) h2
    have hd : DifferentiableAt ℂ riemannZeta (conj z) := differentiableAt_riemannZeta hz1
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hagree : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact zeta_conj_of_one_lt_re hz
  have heq := hζt.eqOn_of_preconnected_of_eventuallyEq hζ hU_conn h2mem hagree
  have h3 : conj (riemannZeta (conj s)) = riemannZeta s := heq (by simpa using hs)
  calc riemannZeta (conj s) = conj (conj (riemannZeta (conj s))) := (Complex.conj_conj _).symm
    _ = conj (riemannZeta s) := by rw [h3]

private lemma tendsto_conj_nhds (w : ℂ) :
    Filter.Tendsto (fun z => conj z) (nhds (conj w)) (nhds w) := by
  have h := (Complex.continuous_conj).tendsto (conj w)
  rwa [Complex.conj_conj] at h

private lemma analyticAt_conj_conj {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(tendsto_conj_nhds w).eventually hf] with z hz
  have h2 := hz.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2

theorem analyticOrderAt_conj_conj (f : ℂ → ℂ) (w : ℂ) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj w) = analyticOrderAt f w := by
  by_cases hf : AnalyticAt ℂ f w
  · by_cases htop : analyticOrderAt f w = ⊤
    · rw [htop, analyticOrderAt_eq_top]
      filter_upwards [(tendsto_conj_nhds w).eventually (analyticOrderAt_eq_top.mp htop)] with z hz
      simp [hz]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hn
      obtain ⟨g, hg, hgne, hfg⟩ := hn
      rw [(analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z => conj (g (conj z)), analyticAt_conj_conj hg, by simpa using hgne, ?_⟩
      filter_upwards [(tendsto_conj_nhds w).eventually hfg] with z hz
      have : conj (f (conj z)) = conj ((conj z - w) ^ n * g (conj z)) := by rw [hz]; rfl
      rw [this]
      simp only [map_mul, map_pow, map_sub, Complex.conj_conj]
      rfl
  · have hf' : ¬ AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
      intro hcon
      apply hf
      have h2 := analyticAt_conj_conj hcon
      rw [Complex.conj_conj] at h2
      exact h2.congr (Filter.Eventually.of_forall fun u => by
        simp only [Complex.conj_conj])
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hf']

theorem analyticOrderAt_zeta_conj {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta (conj w) = analyticOrderAt riemannZeta w := by
  have hne : conj w ≠ 1 := by
    intro h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [Complex.conj_conj, map_one] at h2
    exact hw h2
  have hcong : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (conj w)] riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne :
      conj w ∈ ({(1 : ℂ)}ᶜ))] with z hz
    rw [riemannZeta_conj (by simpa using hz), Complex.conj_conj]
  calc analyticOrderAt riemannZeta (conj w)
      = analyticOrderAt (fun z => conj (riemannZeta (conj z))) (conj w) :=
        (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt riemannZeta w := analyticOrderAt_conj_conj _ _

private noncomputable def Efac (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

private lemma two_pi_ne_zero' : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩

private lemma Efac_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : Efac s ≠ 0 := by
  have hsne : ∀ m : ℕ, s ≠ -m := by
    intro m h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) h0
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero two_pi_ne_zero']
    exact Complex.exp_ne_zero _
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hπ : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination (2 : ℂ) * hk
    have hs_eq : s = ((2 * k + 1 : ℤ) : ℂ) := by
      have h3 := mul_left_cancel₀ hπ h2
      rw [h3]
      push_cast
      ring
    rw [hs_eq, Complex.intCast_re] at h0 h1
    have h0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast h0
    have h1' : (2 * k + 1 : ℤ) < 1 := by exact_mod_cast h1
    omega
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsne
  unfold Efac
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow) hΓ) hcos

private lemma analyticAt_Efac {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ Efac s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards with z
    exact (differentiableAt_id.neg).const_cpow (Or.inl two_pi_ne_zero')
  have h2 : AnalyticAt ℂ Complex.Gamma s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h0] with z hz
    refine Complex.differentiableAt_Gamma z fun m => ?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz
  have h3 : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s := by
    have hlin : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) s := by
      apply AnalyticAt.div_const
      exact analyticAt_const.mul analyticAt_id
    exact Complex.analyticAt_cos.comp hlin
  have h4 : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    analyticAt_const.mul h1
  exact (h4.mul h2).mul h3

theorem analyticOrderAt_zeta_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta (1 - w) = analyticOrderAt riemannZeta w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[nhds w]
      (Efac * riemannZeta) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with z hz
    have hzne : ∀ n : ℕ, z ≠ -n := by
      intro n h
      rw [h] at hz
      simp only [Complex.neg_re, Complex.natCast_re] at hz
      exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz.1
    have hzne1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp only [Complex.one_re] at hz
      exact lt_irrefl 1 hz.2
    show riemannZeta (1 - z) = Efac z * riemannZeta z
    rw [riemannZeta_one_sub hzne hzne1]
    unfold Efac
    ring
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    have : deriv (fun z : ℂ => 1 - z) w = -1 := by
      rw [deriv_const_sub]
      simp
    rw [this]
    simp
  have hEfac := analyticAt_Efac h0
  have hEord : analyticOrderAt Efac w = 0 :=
    hEfac.analyticOrderAt_eq_zero.mpr (Efac_ne_zero h0 h1)
  calc analyticOrderAt riemannZeta (1 - w)
      = analyticOrderAt (riemannZeta ∘ (fun z : ℂ => 1 - z)) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt (Efac * riemannZeta) w := analyticOrderAt_congr hev
    _ = analyticOrderAt Efac w + analyticOrderAt riemannZeta w := by
        by_cases hζw : AnalyticAt ℂ riemannZeta w
        · exact analyticOrderAt_mul hEfac hζw
        · exfalso
          exact hζw (by
            rw [analyticAt_iff_eventually_differentiableAt]
            have hne1 : w ≠ 1 := by
              intro h
              rw [h] at h1
              simp at h1
            filter_upwards [isOpen_compl_singleton.mem_nhds
              (by simpa using hne1 : w ∈ ({(1 : ℂ)}ᶜ))] with z hz
            exact differentiableAt_riemannZeta (by simpa using hz))
    _ = analyticOrderAt riemannZeta w := by rw [hEord, zero_add]

theorem zeta_reflect_zero : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ) := by
  rintro ρ ⟨hzero, h0, h1⟩
  have hρne : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) h0
  have hρne1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have h1subne : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [this] at h0
    simp at h0
  have hrefl_eq : reflect ρ = conj (1 - ρ) := by
    unfold reflect
    rw [map_sub, map_one]
  constructor
  · 
    rw [hrefl_eq, riemannZeta_conj h1subne, riemannZeta_one_sub hρne hρne1, hzero]
    simp
  constructor
  · 
    unfold reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · 
    unfold reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

theorem zeta_mult_reflect : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ := by
  rintro ρ ⟨_, h0, h1⟩
  have h1subne : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have hρ0 : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [hρ0] at h0
    simp at h0
  have hrefl_eq : reflect ρ = conj (1 - ρ) := by
    unfold reflect
    rw [map_sub, map_one]
  unfold zeroMult
  rw [hrefl_eq, analyticOrderAt_zeta_conj h1subne, analyticOrderAt_zeta_one_sub h0 h1]

end Zeta23

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.Statement.SeamClosed -/
section
noncomputable section

namespace Zeta23

theorem zetaSeam : ZetaSeam := ZetaSeam.of_reflect zeta_reflect_zero zeta_mult_reflect

def zetaZeroConfig : ZeroConfig := zetaZeros zetaSeam

@[simp] lemma zetaZeroConfig_carrier : zetaZeroConfig.carrier = {ρ | IsNontrivialZero ρ} := rfl

@[simp] lemma zetaZeroConfig_mult : zetaZeroConfig.mult = zeroMult := rfl

@[simp] lemma zetaZeroConfig_N (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N _ _ _

theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite := by
  simpa [zetaZeros_window] using (zetaZeros zetaSeam).window_finite T₁ T₂

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.RvM.Defs -/
section
open Complex

noncomputable section

namespace Zeta23.RvM

def GoodHeight (T : ℝ) : Prop := ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.im ≠ T

def halfContour (F : ℂ → ℂ) (T₁ T₂ : ℝ) : ℂ :=
  (∫ σ in (1/2:ℝ)..2, F (σ + T₁ * I)) + (∫ t in T₁..T₂, F (2 + t * I)) * I
    - ∫ σ in (1/2:ℝ)..2, F (σ + T₂ * I)

end Zeta23.RvM

end
end

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/- Module Zeta23.FromPNTPlus.StrongPNTPrefix -/
section
open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS

def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}

lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite := by
  apply Set.Finite.subset finiteZeros
  unfold SetOfZeros
  refine setOf_subset_setOf.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩

open Classical

noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0

lemma ZeroFactorization {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (RleOne : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ h_ρ : ℂ → ℂ, AnalyticAt ℂ h_ρ ρ ∧ h_ρ ρ ≠ 0 ∧ ZeroFactor f ρ = h_ρ ρ ∧
      f =ᶠ[nhds ρ] fun z ↦ (z - ρ) ^ analyticOrderNatAt f ρ * h_ρ z := by
  have zero_mem_closedBall : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero, norm_zero]
    exact zero_le_one
  have ρ_mem_closedBall : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw[mem_closedBall_iff_norm, sub_zero]
    linarith[hρ.1]
  have orderAtZeroIsZero : analyticOrderAt f 0 = 0 := by
    rw[analyticOrderAt_eq_zero]
    exact Or.symm (Decidable.not_or_of_imp fun a a_1 ↦ hf_neq_zero_at_zero a)
  have finiteOrder : analyticOrderAt f ρ ≠ ⊤ := by
    refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hfAnalytic (Metric.isPreconnected_closedBall) zero_mem_closedBall ρ_mem_closedBall (lt_top_iff_ne_top.mp ?_)
    rw[orderAtZeroIsZero]
    exact ENat.top_pos
  have AnalyticAt_ρ : AnalyticAt ℂ f ρ := by exact (hfAnalytic ρ ρ_mem_closedBall)
  obtain ⟨h_ρ, h_ρ_neq_zero_at_zero, f_eq⟩ := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose_spec
  set g := (AnalyticAt_ρ.analyticOrderAt_ne_top.mp finiteOrder).choose
  refine ⟨g, h_ρ, h_ρ_neq_zero_at_zero, ?_, f_eq⟩
  simp only [ZeroFactor, AnalyticAt_ρ, ↓reduceDIte, ne_eq, finiteOrder, not_false_eq_true,
    smul_eq_mul, g]

noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1

lemma analyticAt_finset_prod_sub_pow (s : Finset ℂ) (g : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ g ρ) w := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | @insert a s' hne ih =>
    have : (fun z => ∏ ρ ∈ insert a s', (z - ρ) ^ g ρ) = fun z => (z - a) ^ g a * ∏ ρ ∈ s', (z - ρ) ^ g ρ :=
      funext fun z => Finset.prod_insert hne
    rw [this]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih

lemma CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold Cf
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    by_cases w_in_zeros : w ∈ SetOfZeros r f
    · obtain ⟨h_w, hh_w_analytic, hh_w_w_ne_zero, hh_w_eq⟩ := ZeroFactorization (by linarith) (hfAnalytic.mono (Metric.closedBall_subset_closedBall (by linarith))) hf_neq_zero_at_zero w_in_zeros;
      have h_eq : ∀ᶠ z in nhds w, (if h : z ∈ SetOfZeros r f then ZeroFactor f z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ else f z / ∏ ρ ∈ finite_zeros_mono.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) = h_w z / ∏ ρ ∈ finite_zeros_mono.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [ hh_w_eq.2, hh_w_analytic.continuousAt.eventually_ne hh_w_w_ne_zero ] with z hz hz';
        by_cases h : z = w
        · subst h
          rw [dif_pos w_in_zeros]
          congr 1
          exact hh_w_eq.1
        · have z_not_in : z ∉ SetOfZeros r f := by
            intro hmem
            have hfz : f z = 0 := hmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne h)) hz')
          rw [dif_neg z_not_in, hz]
          have hw_mem : w ∈ finite_zeros_mono.toFinset := finite_zeros_mono.mem_toFinset.mpr w_in_zeros
          rw [Finset.prod_eq_prod_sdiff_singleton_mul hw_mem (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (h_w z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne h))]
      apply hh_w_analytic.div _ _ |> fun h => h.congr _;
      · use fun z => ∏ ρ ∈ finite_zeros_mono.toFinset \ { w }, ( z - ρ ) ^ analyticOrderNatAt f ρ;
      · exact analyticAt_finset_prod_sub_pow _ _ _
      · simp only [Finset.prod_eq_zero_iff, ne_eq, pow_eq_zero_iff', Finset.mem_sdiff, Finite.mem_toFinset, Finset.mem_singleton, not_exists, not_and,
          Decidable.not_not, and_imp]
        intro x _ h_ne_w
        exact fun h_eq_w => absurd (sub_eq_zero.mp h_eq_w).symm h_ne_w
      · filter_upwards [ h_eq ] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ finite_zeros_mono.toFinset, ( z - ρ ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact hfAnalytic w ( Metric.mem_closedBall.mpr <| le_trans hw.out <| by linarith )
        · exact analyticAt_finset_prod_sub_pow _ _ _
        · simp only [ ne_eq, Finset.prod_eq_zero_iff, Finite.mem_toFinset, pow_eq_zero_iff',
          sub_eq_zero, ↓existsAndEq, true_and, not_and, Decidable.not_not]
          exact fun h => absurd h w_in_zeros
      · filter_upwards [ IsOpen.mem_nhds ( isOpen_compl_iff.mpr finite_zeros_mono.isClosed ) w_in_zeros ] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticAt_const

noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1

lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const

lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]

lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)

theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))

end

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Auxiliary.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none besides this header (upstream has no blueprint annotations
or intra-project imports in this file).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/- Module Zeta23.FromPNTPlus.Auxiliary -/
section
namespace Complex

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma Differentiable.comp_ofReal {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ (fun x : ℝ ↦ e x) :=
  fun _ ↦ h.differentiableAt.comp_ofReal

end

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Rectangle.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
@[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

/- Module Zeta23.FromPNTPlus.Rectangle -/
section
open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]

lemma symm_re : Rectangle (w.re + z.im * I) (z.re + w.im * I) = Rectangle z w := by
  simp [Rectangle, uIcc_comm]

end Rectangle

def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)

lemma Square_apply (p : ℂ) (cpos : c > 0) :
    Square p c = Icc (-c + p.re) (c + p.re) ×ℂ Icc (-c + p.im) (c + p.im) := by
  rw [Square, Rectangle, uIcc_of_le (by simp; linarith), uIcc_of_le (by simp; linarith)]
  simp

@[simp] theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp] theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl

lemma segment_reProdIm_segment_eq_convexHull (z w : ℂ) :
    [[z.re, w.re]] ×ℂ [[z.im, w.im]] =
      convexHull ℝ {z, z.re + w.im * I, w.re + z.im * I, w} := by
  simp_rw [← segment_eq_uIcc, ← convexHull_pair, ← convexHull_reProdIm, reProdIm]
  exact congrArg _ <| Set.ext <| by simpa [Complex.ext_iff] using by tauto

lemma rectangle_in_convex {U : Set ℂ} (U_convex : Convex ℝ U) {z w : ℂ} (hz : z ∈ U)
    (hw : w ∈ U) (hzw : (z.re + w.im * I) ∈ U) (hwz : (w.re + z.im * I) ∈ U) :
    Rectangle z w ⊆ U := by
  rw [Rectangle, segment_reProdIm_segment_eq_convexHull]
  exact convexHull_min (by simp_all [insert_subset_iff]) U_convex

lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

lemma square_neg (p : ℂ) (c : ℝ) : Square p (-c) = Square p c := by
  simpa [Square] using! Rectangle.symm

theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩

lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x
    ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · exact (le_sup_iff.mp hxre_le).casesOn (fun h ↦ h.trans hz're_le)
      (fun h ↦ h.trans hw're_le)
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  · exact (le_sup_iff.mp hxim_le).casesOn (fun h ↦ h.trans hz'im_le)
      (fun h ↦ h.trans hw'im_le)

lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁)
    (x₁_le_x₂ : x₁ ≤ x₂) (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁)
    (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆
      Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith

lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re)
    (x₁_le_x₂ : z₁.re ≤ z₂.re) (x₂_le_x₃ : z₂.re ≤ z₃.re)
    (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  exact RectSubRect x₀_le_x₁ x₁_le_x₂ x₂_le_x₃ y₀_le_y₁ y₁_le_y₂ y₂_le_y₃

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
  obtain h | h | h | h := h
  · exact Or.inl (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inl (notMem_uIcc_of_gt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_gt h.1 h.2)

lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨by apply RectSubRect' <;> tauto, rectangle_disjoint_singleton hp⟩

lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨
    (rectangleBorder_subset_rectangle _ _).trans (by apply RectSubRect' <;> tauto),
    rectangleBorder_disjoint_singleton hp⟩

lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

lemma mapsTo_rectangle_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp, by simp [hx]⟩

lemma mapsTo_rectangle_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangle_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w) :=
  fun _ hx ↦ ⟨by simp [hx], by simp⟩

lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangle_left_re_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_re z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_re_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_re z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_left_im_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_left_im z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

lemma mapsTo_rectangle_right_im_NoP (z w : ℂ) {p : ℂ}
    (pNotOnBorder : p ∉ RectangleBorder z w) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (Rectangle z w \ {p}) := by
  refine (mapsTo_rectangleBorder_right_im z w).mono_right (Set.subset_sdiff.mpr ?_)
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

theorem Complex.nhds_hasBasis_square (p : ℂ) : (𝓝 p).HasBasis (0 < ·) (Square p ·) := by
  suffices
      (𝓝 p.re ×ˢ 𝓝 p.im).HasBasis (0 < ·)
        (equivRealProdCLM.symm.toHomeomorph ⁻¹' Square p ·)
    by simpa only [← nhds_prod_eq, Homeomorph.map_nhds_eq, Homeomorph.image_preimage]
      using! this.map equivRealProdCLM.symm.toHomeomorph
  apply ((nhds_basis_Icc_pos p.re).prod_same_index_mono (nhds_basis_Icc_pos p.im) ?_ ?_).congr
  · intro; rfl
  · intros
    rw [← uIcc_of_lt (by linarith), ← uIcc_of_lt (by linarith)]
    simpa [Square, Rectangle] using by ring_nf
  all_goals exact (antitone_const_tsub.Icc (monotone_id.const_add _)).monotoneOn _

lemma square_mem_nhds (p : ℂ) {c : ℝ} (hc : c ≠ 0) :
    Square p c ∈ 𝓝 p := by
  wlog hc_pos : 0 < c generalizing c with h
  · rw [← square_neg]
    exact h (neg_ne_zero.mpr hc) <| neg_pos.mpr <| hc.lt_of_le <| not_lt.mp hc_pos
  exact (nhds_hasBasis_square p).mem_of_mem hc_pos

lemma square_subset_square {p : ℂ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c₂) :
    Square p c₁ ⊆ Square p c₂ := by
  apply RectSubRect' <;> simpa using by linarith

lemma SmallSquareInRectangle {z w p : ℂ} (pInRectInterior : Rectangle z w ∈ nhds p) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, Square p c ⊆ Rectangle z w := by
  obtain ⟨ε, hε0, hε⟩ := ((Complex.nhds_hasBasis_square p).1 _).mp pInRectInterior
  filter_upwards [Ioo_mem_nhdsGT (hε0)] with _ ⟨hε'0, hε'⟩
  exact subset_trans (square_subset_square hε'0 hε'.le) hε

end

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes) and redirected intra-project
imports to Zeta23.FromPNTPlus.*.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

/- Module Zeta23.FromPNTPlus.ResidueCalcOnRectangles -/
section
open Complex BigOperators Nat Classical Real Topology Filter

open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def HIntegral' (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    (1 / (2 * π * I)) • HIntegral f x₁ x₂ y

noncomputable def VIntegral' (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    (1 / (2 * π * I)) • VIntegral f x y₁ y₂

set_option maxHeartbeats 1600000 in
lemma HIntegral_symm :
    HIntegral f x₁ x₂ y = -HIntegral f x₂ x₁ y := integral_symm _ _

set_option maxHeartbeats 1600000 in
lemma VIntegral_symm :
    VIntegral f x y₁ y₂ = -VIntegral f x y₂ y₁ := by
  simp_rw [VIntegral, integral_symm y₁ y₂, smul_neg, neg_neg]

noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

noncomputable def UpperUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' T +
    I • (∫ y : ℝ in Ici T, f (σ' + y * I)) -
    I • (∫ y : ℝ in Ici T, f (σ + y * I))

noncomputable def LowerUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    HIntegral f σ σ' (-T) -
    I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) +
    I • (∫ y : ℝ in Iic (-T), f (σ + y * I))

noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

set_option maxHeartbeats 1600000 in
lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ =
      I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b +
      I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]

set_option maxHeartbeats 1600000 in
lemma DiffVertRect_eq_UpperLowerUs {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
    VerticalIntegral f σ' - VerticalIntegral f σ -
      RectangleIntegral f (σ - I * T) (σ' + I * T) =
    UpperUIntegral f σ σ' T - LowerUIntegral f σ σ' T := by
  rw [verticalIntegral_split_three (-T) T f_int_σ, verticalIntegral_split_three (-T) T f_int_σ']
  simp only [RectangleIntegral, UpperUIntegral, LowerUIntegral]
  simp only [sub_re, mul_re, I_re, add_re, ofReal_re, I_im, ofReal_im, sub_im, mul_im, add_im]
  ring_nf
  abel

abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

set_option maxHeartbeats 1600000 in
theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

set_option maxHeartbeats 1600000 in
theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

set_option maxHeartbeats 1600000 in
theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

set_option maxHeartbeats 1600000 in
theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

set_option maxHeartbeats 1600000 in
theorem rectangleIntegral_symm (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f z w = RectangleIntegral f w z := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, intervalIntegral.integral_symm w.re,
    intervalIntegral.integral_symm w.im, sub_neg_eq_add, smul_neg, sub_neg_eq_add,
    ← sub_eq_add_neg, neg_add_eq_sub, sub_add_eq_add_sub]

set_option maxHeartbeats 1600000 in
theorem rectangleIntegral_symm_re (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f (w.re + z.im * I) (z.re + w.im * I) = -RectangleIntegral f z w := by
  simp only [RectangleIntegral, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, add_im, mul_im, zero_add, neg_sub, ← sub_eq_zero, sub_zero]
  rw [HIntegral_symm (y := z.im), HIntegral_symm (y := w.im)]
  abel

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

set_option maxHeartbeats 1600000 in
theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in

set_option maxHeartbeats 1600000 in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in

set_option maxHeartbeats 1600000 in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in

set_option maxHeartbeats 1600000 in
theorem ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

set_option maxHeartbeats 1600000 in
theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

set_option maxHeartbeats 1600000 in
theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

set_option maxHeartbeats 1600000 in
lemma RectangleIntegralHSplit {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot
  have h₂ := integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top
  have h₁' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₀ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₀ * I) := by
    simpa [add_comm] using h₁
  have h₂' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₁ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₁ * I) := by
    simpa [add_comm] using h₂
  rw [← h₁', ← h₂']
  have hcomm₁ :
      ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₀ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  have hcomm₂ :
      ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₁ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  rw [hcomm₁, hcomm₂]
  abel

set_option maxHeartbeats 1600000 in
lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ}
    (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)

set_option maxHeartbeats 1600000 in
lemma RectangleIntegralVSplit {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left
  have h₂ := integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right
  rw [← h₁, ← h₂]
  module

set_option maxHeartbeats 1600000 in
lemma RectangleIntegralVSplit' {b x₀ x₁ y₀ y₁ : ℝ}
    (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)

set_option maxHeartbeats 1600000 in
lemma RectanglePullToNhdOfPole' [CompleteSpace E] {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧
      z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ :=
    (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rectangle_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show
      p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show
      z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have fCont := fHolo.continuousOn
  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine ContinuousOn.rectangleBorder_integrable
      (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_))
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try {
    rw [Set.uIcc_of_le]
    constructor
    all_goals assumption
  }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }
  have h₁ := RectangleIntegralVSplit' hbot' hbot
  have h₂ := fHolo.vanishesOnRectangle hbot''
  have h₃ := RectangleIntegralVSplit' htop' htop
  have h₄ := fHolo.vanishesOnRectangle htop''
  have h₅ := RectangleIntegralHSplit' hleft' hleft
  have h₆ := fHolo.vanishesOnRectangle hleft''
  have h₇ := RectangleIntegralHSplit' hright' hright
  have h₈ := fHolo.vanishesOnRectangle hright''
  simp only [re_add_im] at *
  linear_combination (norm := abel) h₁ + h₂ + h₃ + h₄ + h₅ + h₆ + h₇ + h₈

set_option maxHeartbeats 1600000 in
lemma RectanglePullToNhdOfPole [CompleteSpace E] {z w p : ℂ}
    (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
      RectangleIntegral f z w = RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one, SmallSquareInRectangle hp]
  intro c ⟨cpos, _⟩ hc
  simp_rw [mul_comm I]
  exact RectanglePullToNhdOfPole' (by simp_all [cpos.le])
    (square_mem_nhds p (ne_of_gt cpos)) hc fHolo

set_option maxHeartbeats 1600000 in
lemma RectanglePullToNhdOfPole'' [CompleteSpace E] {z w p : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
      RectangleIntegral' f z w = RectangleIntegral' f (-c - I * c + p) (c + I * c + p) := by
  filter_upwards [RectanglePullToNhdOfPole zRe_le_wRe zIm_le_wIm pInRectInterior fHolo] with c h
  simp_rw [RectangleIntegral', h]

set_option maxHeartbeats 1600000 in
theorem ResidueTheoremAtOrigin_aux1c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y + I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

set_option maxHeartbeats 1600000 in
theorem ResidueTheoremAtOrigin_aux1c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y - I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

set_option maxHeartbeats 1600000 in
theorem ResidueTheoremAtOrigin_aux2c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (1 + y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

set_option maxHeartbeats 1600000 in
theorem ResidueTheoremAtOrigin_aux2c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (-1 + y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop)
    (by simp [Complex.ext_iff])).intervalIntegrable

set_option maxHeartbeats 1600000 in
theorem RectangleIntegral.const_smul (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral (fun s => c • f s) z w = c • RectangleIntegral f z w := by
  simp [RectangleIntegral, HIntegral, VIntegral, smul_add, smul_sub, smul_smul, mul_comm]

set_option maxHeartbeats 1600000 in
theorem RectangleIntegral.const_mul' (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral' (fun s => c • f s) z w = c • RectangleIntegral' f z w := by
  simp [RectangleIntegral', RectangleIntegral.const_smul, smul_smul]
  ring_nf

set_option maxHeartbeats 1600000 in
theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

set_option maxHeartbeats 1600000 in
theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

set_option maxHeartbeats 1600000 in
lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

set_option maxHeartbeats 1600000 in
lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

set_option maxHeartbeats 1600000 in
lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

set_option maxHeartbeats 1600000 in
lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

set_option maxHeartbeats 1600000 in
lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

set_option maxHeartbeats 1600000 in
lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

set_option maxHeartbeats 1600000 in
lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

set_option maxHeartbeats 1600000 in
lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

set_option maxHeartbeats 1600000 in
theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

set_option maxHeartbeats 1600000 in
lemma ResidueTheoremAtOrigin :
    RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  rw [RectangleIntegral', ResidueTheoremAtOrigin']
  all_goals simp [field]

set_option maxHeartbeats 1600000 in
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

set_option maxHeartbeats 1600000 in
lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U

set_option maxHeartbeats 1600000 in
theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply Set.sdiff_subset_sdiff_right
      simpa
  · exact V_prop.mono
      (image_mono <| Set.sdiff_subset_sdiff_left <| subset_trans inter_subset_right W_subset)

set_option maxHeartbeats 1600000 in
theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  set g := f - (fun s ↦ A / (s - p))
  have gHolo : HolomorphicOn g (Rectangle z w \ {p}) := by
    apply DifferentiableOn.sub fHolo
    intro s hs
    have : s - p ≠ 0 := sub_ne_zero.mpr hs.2
    exact  DifferentiableWithinAt.div (by fun_prop) (by fun_prop) this
  have := BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p
  obtain ⟨h, ⟨hHolo, hEq⟩⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo this
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq

def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z

set_option maxHeartbeats 1600000 in
lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)

noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)

noncomputable def sumResiduesIn (f : ℂ → ℂ) (S : Set ℂ) : ℂ :=
  ∑' z : S, residue f z

set_option maxHeartbeats 1600000 in
lemma residue_eq_of_tendsto {f : ℂ → ℂ} {p c : ℂ}
    (h : Filter.Tendsto (fun z ↦ (z - p) * f z) (nhdsWithin p {p}ᶜ) (nhds c)) :
    residue f p = c := by
  unfold residue
  exact h.limUnder_eq

set_option maxHeartbeats 1600000 in
lemma residue_analyticAt_eq_zero {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 := by
  apply residue_eq_of_tendsto
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - p) (nhdsWithin p {p}ᶜ) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hf' : Filter.Tendsto f (nhdsWithin p {p}ᶜ) (nhds (f p)) :=
    hf.continuousAt.continuousWithinAt.tendsto
  simpa using hsub.mul hf'

set_option maxHeartbeats 1600000 in
lemma simplePole_sub_residue_isBigO_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = (-1 : ℤ)) :
    (f - (fun z ↦ residue f p / (z - p))) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg_analytic, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hres : residue f p = g p :=
    residue_eq_of_tendsto (hg_analytic.continuousAt.continuousWithinAt.tendsto.congr'
      (show (fun z ↦ (z - p) * f z) =ᶠ[nhdsWithin p {p}ᶜ] g from by
        filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
        simp [hz, sub_ne_zero.mpr hz_ne]).symm)
  have hdslope : (fun z ↦ (z - p)⁻¹ * (g z - g p)) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
    have hcont : ContinuousAt (dslope g p) p :=
      continuousAt_dslope_same.2 hg_analytic.differentiableAt
    have hbig : dslope g p =O[nhds p] (1 : ℂ → ℂ) :=
      hcont.norm.isBoundedUnder_le.isBigO_one ℂ
    have hbig_ne : dslope g p =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) :=
      IsBigO.mono hbig inf_le_left
    simpa [slope] using! hbig_ne.congr' (dslope_eventuallyEq_slope_nhdsNE (f := g) (a := p)) .rfl
  refine hdslope.congr' ?_ .rfl
  filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz_ne
  simp [hz, hres, div_eq_mul_inv, sub_eq_add_neg]; ring

set_option maxHeartbeats 1600000 in
private lemma intervalIntegral_congr_ae_of_codiscreteWithin_along_path
    {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    {a b : ℝ} {p : ℝ → ℂ}
    (hp_an : AnalyticOnNhd ℝ p (Set.uIcc a b))
    (hp_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst p (nhds x))
    (hp_maps : Set.MapsTo p (Set.uIcc a b) R) :
    ∫ x in a..b, f (p x) = ∫ x in a..b, g (p x) := by
  refine intervalIntegral.integral_congr_ae_restrict (μ := volume) ?_
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change {x : ℝ | f (p x) = g (p x)} ∈ Filter.codiscreteWithin (Set.uIoc a b)
  simpa [Set.preimage] using Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
    (hp_an.preimage_mem_codiscreteWithin hp_nonconst
      (Filter.codiscreteWithin_mono
        (by intro s hs; rcases hs with ⟨x, hx, rfl⟩; exact hp_maps hx) heq))

set_option maxHeartbeats 1600000 in
private lemma meromorphicOrderAt_eq_neg_one_of_simplePole
    {f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hpU : p ∈ U)
    (hf_simple : HasSimplePolesOn f U)
    (hpneg : meromorphicOrderAt f p < 0) :
    meromorphicOrderAt f p = (-1 : ℤ) := by
  lift meromorphicOrderAt f p to ℤ using hpneg.ne_top with n hn
  have hsimple : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp (hn ▸ hf_simple p hpU)
  have hneg : n < 0 := by exact_mod_cast hpneg
  have hn1 : n = -1 := by omega
  simp [hn1]

set_option maxHeartbeats 1600000 in
private lemma residue_toMeromorphicNFOn_eq_residue
    {f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hpU : p ∈ U)
    (hf_mero : MeromorphicOn f U)
    (hf_simple : HasSimplePolesOn f U)
    (hpneg : meromorphicOrderAt f p < 0) :
    residue (toMeromorphicNFOn f U) p = residue f p := by
  have hmero : MeromorphicAt f p := hf_mero p hpU
  have h_exists : ∃ c, Filter.Tendsto (fun z : ℂ ↦ (z - p) * f z) (nhdsWithin p ({p}ᶜ)) (nhds c) := by
    have hmul_mero : MeromorphicAt (fun z : ℂ ↦ (z - p) * f z) p :=
      (by fun_prop : MeromorphicAt (fun z : ℂ ↦ z - p) p).mul hmero
    have hmul_nonneg : 0 ≤ meromorphicOrderAt (fun z : ℂ ↦ (z - p) * f z) p := by
      change 0 ≤ meromorphicOrderAt ((fun z ↦ z - p) * f) p
      rw [meromorphicOrderAt_mul (by fun_prop : MeromorphicAt (fun z : ℂ ↦ z - p) p) hmero,
        meromorphicOrderAt_id_sub_const,
        meromorphicOrderAt_eq_neg_one_of_simplePole hpU hf_simple hpneg]
      norm_num
    exact tendsto_nhds_of_meromorphicOrderAt_nonneg hmul_mero hmul_nonneg
  have h_tendsto : Filter.Tendsto (fun z : ℂ ↦ (z - p) * f z) (nhdsWithin p ({p}ᶜ)) (nhds (residue f p)) := by
    simpa [residue] using tendsto_nhds_limUnder h_exists
  have h_eq :
      (fun z ↦ (z - p) * toMeromorphicNFOn f U z) =ᶠ[nhdsWithin p ({p}ᶜ)]
        (fun z ↦ (z - p) * f z) := by
    filter_upwards [hf_mero.toMeromorphicNFOn_eq_self_on_nhdsNE hpU] with z hz
    simp [hz]
  exact residue_eq_of_tendsto
    (h_tendsto.congr' h_eq.symm)

set_option maxHeartbeats 1600000 in
private lemma horizontalPath_not_eventuallyConst (h : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * Complex.I)
  have hconst : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact one_ne_zero (hpath.unique hconst)

set_option maxHeartbeats 1600000 in
lemma verticalPath_not_eventuallyConst (r : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) Complex.I x := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I).const_add (r : ℂ)
  have hconst : HasDerivAt (fun y : ℝ ↦ (r : ℂ) + (y : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact Complex.I_ne_zero (hpath.unique hconst)

set_option maxHeartbeats 1600000 in
private lemma HIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {a b c : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ x ∈ Set.uIcc a b, (↑x + ↑c * Complex.I) ∈ R) :
    HIntegral f a b c = HIntegral g a b c := by
  unfold HIntegral
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
    (fun x _ ↦ horizontalPath_not_eventuallyConst c x) hmaps

set_option maxHeartbeats 1600000 in
private lemma VIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {c a b : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ y ∈ Set.uIcc a b, (↑c + ↑y * Complex.I) ∈ R) :
    VIntegral f c a b = VIntegral g c a b := by
  unfold VIntegral; simp only [smul_eq_mul]; congr 1
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
    (fun x _ ↦ verticalPath_not_eventuallyConst c x) hmaps

set_option maxHeartbeats 1600000 in
private lemma rectangleIntegral'_toMeromorphicNFOn_eq {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w)) :
    RectangleIntegral' f z w = RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w := by
  classical
  let R : Set ℂ := Rectangle z w
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  have h_eq : {s : ℂ | f s = fNF s} ∈ Filter.codiscreteWithin R := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) f_mero)
  have hbot := HIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_left_im z w)
  have htop := HIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_right_im z w)
  have hright := VIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_right_re z w)
  have hleft := VIntegral_congr_codiscreteWithin h_eq (by simpa [R] using! mapsTo_rectangle_left_re z w)
  unfold RectangleIntegral'; congr 1; unfold RectangleIntegral
  rw [hbot, htop, hright, hleft]

set_option maxHeartbeats 1600000 in
private lemma principalPart_meromorphicOn {R : Set ℂ} {polesFin : Finset ℂ} {c : ℂ → ℂ} :
    MeromorphicOn (fun s ↦ ∑ p ∈ polesFin, c p / (s - p)) R := by
  intro x _
  refine MeromorphicAt.fun_sum (G := fun p s ↦ c p / (s - p)) ?_
  intro p _
  exact (analyticAt_const.meromorphicAt.div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt))

set_option maxHeartbeats 1600000 in
private lemma sub_principalPart_analyticAt_of_not_mem_poles
    {f : ℂ → ℂ} {polesFin : Finset ℂ} {x : ℂ}
    (h_nf : MeromorphicNFAt f x)
    (hxnp : x ∉ polesFin)
    (hxneg : 0 ≤ meromorphicOrderAt f x) :
    AnalyticAt ℂ (f - fun s ↦ ∑ p ∈ polesFin, residue f p / (s - p)) x := by
  have h_f_analytic : AnalyticAt ℂ f x :=
    h_nf.meromorphicOrderAt_nonneg_iff_analyticAt.1 hxneg
  have h_principal_analytic : AnalyticAt ℂ (fun s ↦ ∑ p ∈ polesFin, residue f p / (s - p)) x := by
    refine Finset.analyticAt_fun_sum polesFin ?_
    intro p hp
    have hxp : x ≠ p := by
      intro heq
      subst heq
      exact hxnp hp
    have : AnalyticAt ℂ (fun z : ℂ ↦ residue f p / (z - p)) x := by
      fun_prop (disch := exact sub_ne_zero.mpr hxp)
    simpa using this
  exact h_f_analytic.sub h_principal_analytic

set_option maxHeartbeats 1600000 in
private lemma meromorphicOrderAt_sub_principalPart_nonneg
    {f : ℂ → ℂ} {polesFin : Finset ℂ} {p : ℂ}
    (hpFin : p ∈ polesFin)
    (h_mero : MeromorphicAt f p)
    (h_ord : meromorphicOrderAt f p = -1) :
    0 ≤ meromorphicOrderAt (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) p := by
  have hcore : (f - fun z ↦ residue f p / (z - p)) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    exact simplePole_sub_residue_isBigO_one h_mero h_ord
  let rest : ℂ → ℂ := fun z ↦ ∑ q ∈ polesFin.erase p, residue f q / (z - q)
  have hrest_cont : ContinuousAt rest p := by
    dsimp [rest]
    refine tendsto_finsetSum _ (fun q hq ↦ ?_)
    have hpq : p - q ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hq).1.symm
    have h_cont : ContinuousAt (fun z : ℂ ↦ residue f q / (z - q)) p := by
      fun_prop (disch := exact hpq)
    exact h_cont
  have hrest : rest =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    have hbig : rest =O[nhds p] (1 : ℂ → ℂ) :=
      hrest_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono hbig inf_le_left
  have hraw_big : (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) := by
    have htmp : (fun z : ℂ ↦ (f z - residue f p / (z - p)) - rest z) =O[nhdsWithin p ({p}ᶜ)] (1 : ℂ → ℂ) :=
      hcore.sub hrest
    have hdecomp : (f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) =
        (fun z : ℂ ↦ (f z - residue f p / (z - p)) - rest z) := by
      funext z
      dsimp [rest]
      rw [← Finset.add_sum_erase (s := polesFin) (f := fun q ↦ residue f q / (z - q)) hpFin]
      simp [sub_eq_add_neg, add_assoc, add_comm]
    simpa [hdecomp, rest] using htmp
  by_contra hneg
  have hnorm : Filter.Tendsto (fun z : ℂ ↦ ‖(f - fun s ↦ ∑ q ∈ polesFin, residue f q / (s - q)) z‖) (nhdsWithin p ({p}ᶜ)) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg (not_le.mp hneg)
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm) hraw_big.isBoundedUnder_le

set_option maxHeartbeats 1600000 in
private lemma holoPart_holomorphicOn {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w))
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite) :
    HolomorphicOn (toMeromorphicNFOn (toMeromorphicNFOn f (Rectangle z w) -
      fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) (Rectangle z w)) (Rectangle z w) := by
  classical
  let R := Rectangle z w
  let poles := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin := f_poles_finite.toFinset
  let fNF := toMeromorphicNFOn f R
  let principalPart := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart := toMeromorphicNFOn (fNF - principalPart) R
  have h_fNF_mero : MeromorphicOn fNF R := by
    simpa [fNF] using
      (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R)).meromorphicOn
  have h_principalPart_mero : MeromorphicOn principalPart R := principalPart_meromorphicOn
  have h_raw_mero : MeromorphicOn (fNF - principalPart) R := h_fNF_mero.sub h_principalPart_mero
  intro x hx
  have h_raw_nonneg : 0 ≤ meromorphicOrderAt (fNF - principalPart) x := by
    by_cases hxp : x ∈ poles
    · have hpFin : x ∈ polesFin := by simpa [polesFin, poles] using hxp
      have hord : meromorphicOrderAt f x = (-1 : ℤ) :=
        meromorphicOrderAt_eq_neg_one_of_simplePole hxp.1 f_simple_poles hxp.2
      have hordNF : meromorphicOrderAt fNF x = (-1 : ℤ) := by
        rw [show meromorphicOrderAt fNF x = meromorphicOrderAt f x by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hxp.1)]
        exact hord
      exact meromorphicOrderAt_sub_principalPart_nonneg hpFin (h_fNF_mero x hxp.1) hordNF
    · have hxnp : x ∉ polesFin := by
        intro h
        exact hxp (by simpa [polesFin, poles] using h)
      have h_fNF_nonneg : 0 ≤ meromorphicOrderAt fNF x := by
        rw [show meromorphicOrderAt fNF x = meromorphicOrderAt f x by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hx)]
        exact le_of_not_gt fun hxneg => hxp ⟨hx, hxneg⟩
      have h_fNF_nf : MeromorphicNFAt fNF x := by
        simpa [fNF] using
          (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R) hx)
      exact (sub_principalPart_analyticAt_of_not_mem_poles h_fNF_nf hxnp h_fNF_nonneg).meromorphicOrderAt_nonneg
  have h_nf : MeromorphicNFAt holoPart x := by
    simpa [holoPart] using
      (meromorphicNFOn_toMeromorphicNFOn (f := fNF - principalPart) (U := R) hx)
  have h_ord :
      meromorphicOrderAt holoPart x = meromorphicOrderAt (fNF - principalPart) x := by
    simpa [holoPart] using
      (meromorphicOrderAt_toMeromorphicNFOn (f := fNF - principalPart) (U := R) h_raw_mero hx)
  exact (h_nf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (h_ord.symm ▸ h_raw_nonneg)).differentiableAt.differentiableWithinAt

set_option maxHeartbeats 1600000 in
private lemma principalPart_borderIntegrable {f : ℂ → ℂ} {z w : ℂ}
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite) :
    RectangleBorderIntegrable (fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) z w := by
  classical
  let R := Rectangle z w
  let poles := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin := f_poles_finite.toFinset
  let fNF := toMeromorphicNFOn f R
  let principalPart := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  refine ContinuousOn.rectangleBorder_integrable ?_
  refine continuousOn_finsetSum _ ?_
  intro p hp s hs
  have hsp : s ≠ p := fun hsp => Set.disjoint_right.mp f_no_poles_boundary
    ((by simpa [polesFin, poles] using hp : p ∈ poles).2) (hsp ▸ hs)
  have : ContinuousAt (fun z : ℂ ↦ residue fNF p / (z - p)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hsp)
  exact this.continuousWithinAt

set_option maxHeartbeats 1600000 in
private lemma rectangle_mem_nhds_of_interior {z w p : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (hpR : p ∈ Rectangle z w) (hpnot : p ∉ RectangleBorder z w) :
    Rectangle z w ∈ nhds p := by
  rw [mem_Rect zRe_le_wRe zIm_le_wIm] at hpR
  have hp_re_left : z.re < p.re :=
    lt_of_le_of_ne hpR.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.2.2.1, hpR.2.2.2, zIm_le_wIm, mem_reProdIm])
  have hp_re_right : p.re < w.re :=
    lt_of_le_of_ne hpR.2.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.2.2.1, hpR.2.2.2, zIm_le_wIm, mem_reProdIm])
  have hp_im_left : z.im < p.im :=
    lt_of_le_of_ne hpR.2.2.1 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.1, hpR.2.1, zRe_le_wRe, mem_reProdIm])
  have hp_im_right : p.im < w.im :=
    lt_of_le_of_ne hpR.2.2.2 fun hEq => hpnot
      (by simp [RectangleBorder, hEq, hpR.1, hpR.2.1, zRe_le_wRe, mem_reProdIm])
  rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le zRe_le_wRe, Set.uIoo_of_le zIm_le_wIm]
  exact ⟨⟨hp_re_left, hp_re_right⟩, ⟨hp_im_left, hp_im_right⟩⟩

set_option maxHeartbeats 1600000 in
private lemma sum_div_rectangleBorderIntegrable {z w : ℂ} {S : Finset ℂ}
    (hS_disjoint : Disjoint (RectangleBorder z w) S) (c : ℂ → ℂ) :
    RectangleBorderIntegrable (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w := by
  refine ContinuousOn.rectangleBorder_integrable ?_
  refine continuousOn_finsetSum _ ?_
  intro p hp s hs
  have hsp : s ≠ p := fun hsp => Set.disjoint_right.mp hS_disjoint hp (hsp ▸ hs)
  have : ContinuousAt (fun z : ℂ ↦ c p / (z - p)) s := by
    fun_prop (disch := exact sub_ne_zero.mpr hsp)
  exact this.continuousWithinAt

set_option maxHeartbeats 1600000 in
private lemma rectangleIntegral'_sum_div_sub {z w : ℂ} (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    {S : Finset ℂ} (hS_subset : (S : Set ℂ) ⊆ Rectangle z w)
    (hS_disjoint : Disjoint (RectangleBorder z w) S)
    (c : ℂ → ℂ) :
    RectangleIntegral' (fun s ↦ ∑ p ∈ S, c p / (s - p)) z w = ∑ p ∈ S, c p := by
  classical
  have h_partial_border : ∀ (S' : Finset ℂ), S' ⊆ S → RectangleBorderIntegrable (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w := by
    intro S' hS'
    exact sum_div_rectangleBorderIntegrable (Disjoint.mono_right hS' hS_disjoint) c
  have h_term_integral : ∀ {p : ℂ}, p ∈ S → RectangleIntegral' (fun s ↦ c p / (s - p)) z w = c p :=
    fun {p} hp => ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm
      (rectangle_mem_nhds_of_interior zRe_le_wRe zIm_le_wIm
        (hS_subset hp) (Set.disjoint_right.mp hS_disjoint hp))
  have h_partial_integral :
      ∀ (S' : Finset ℂ), S' ⊆ S →
        RectangleIntegral' (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w =
          ∑ p ∈ S', c p := by
    intro S' hS'
    revert hS'
    refine Finset.induction_on S' ?_ ?_
    · intro _
      simp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral]
    · intro a S' ha ih hS'
      obtain ⟨haFin, hSsub⟩ := Finset.insert_subset_iff.mp hS'
      have hterm_border :
          RectangleBorderIntegrable (fun s ↦ c a / (s - a)) z w :=
        by simpa using h_partial_border ({a} : Finset ℂ) (Finset.singleton_subset_iff.mpr haFin)
      have hfun :
          (fun s ↦ ∑ p ∈ insert a S', c p / (s - p)) =
            (fun s ↦ c a / (s - a)) +
              (fun s ↦ ∑ p ∈ S', c p / (s - p)) := by
        funext s; simp [Finset.sum_insert, ha]
      have h_add_primed :
          RectangleIntegral' ((fun s ↦ c a / (s - a)) + (fun s ↦ ∑ p ∈ S', c p / (s - p))) z w =
            RectangleIntegral' (fun s ↦ c a / (s - a)) z w +
              RectangleIntegral' (fun s ↦ ∑ p ∈ S', c p / (s - p)) z w := by
        unfold RectangleIntegral'
        rw [RectangleBorderIntegrable.add hterm_border (h_partial_border S' hSsub), smul_add]
      rw [hfun, h_add_primed, h_term_integral haFin, ih hSsub, Finset.sum_insert ha]
  exact h_partial_integral S (by intro p hp; exact hp)

set_option maxHeartbeats 1600000 in
private lemma toMeromorphicNFOn_add_integral {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite)
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w)) :
    RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w =
      RectangleIntegral' (toMeromorphicNFOn (toMeromorphicNFOn f (Rectangle z w) -
        fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) (Rectangle z w)) z w +
      RectangleIntegral' (fun s ↦ ∑ p ∈ f_poles_finite.toFinset, residue (toMeromorphicNFOn f (Rectangle z w)) p / (s - p)) z w := by
  let R : Set ℂ := Rectangle z w
  let poles : Set ℂ := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin : Finset ℂ := f_poles_finite.toFinset
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  let principalPart : ℂ → ℂ := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart : ℂ → ℂ := toMeromorphicNFOn (fNF - principalPart) R
  have h_holoPart_border : RectangleBorderIntegrable holoPart z w :=
    (holoPart_holomorphicOn f_mero f_simple_poles f_poles_finite).rectangleBorderIntegrable
  have h_fNF_eq :
      Set.EqOn fNF (holoPart + principalPart) (RectangleBorder z w) := by
    intro s hs
    have hsR : s ∈ R := rectangleBorder_subset_rectangle z w hs
    have hsnp : s ∉ poles := fun hsp => Set.disjoint_right.mp f_no_poles_boundary hsp.2 hs
    have hraw_analytic : AnalyticAt ℂ (fNF - principalPart) s := by
      have h_fNF_nonneg : 0 ≤ meromorphicOrderAt fNF s := by
        rw [show meromorphicOrderAt fNF s = meromorphicOrderAt f s by
          simpa [fNF] using
            (meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) f_mero hsR)]
        exact le_of_not_gt fun hsneg => hsnp ⟨hsR, hsneg⟩
      exact sub_principalPart_analyticAt_of_not_mem_poles
        (by simpa [fNF] using meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R) hsR)
        (fun h => hsnp (by simpa [polesFin, poles] using h))
        h_fNF_nonneg
    have hs_eq : holoPart s = (fNF - principalPart) s := by
      rw [show holoPart = toMeromorphicNFOn (fNF - principalPart) R by rfl]
      have h_fNF_mero : MeromorphicOn fNF R := by
        simpa [fNF] using (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R)).meromorphicOn
      have hf_sub_mero : MeromorphicOn (fNF - principalPart) R :=
        h_fNF_mero.sub principalPart_meromorphicOn
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (f := fNF - principalPart) (U := R) hf_sub_mero hsR]
      exact congr_fun (toMeromorphicNFAt_eq_self.2 hraw_analytic.meromorphicNFAt) s
    calc
      fNF s = (fNF - principalPart) s + principalPart s := by simp
      _ = holoPart s + principalPart s := by rw [← hs_eq]
  rw [RectangleIntegral'_congr h_fNF_eq, RectangleIntegral',
    RectangleBorderIntegrable.add h_holoPart_border
      (principalPart_borderIntegrable f_no_poles_boundary f_poles_finite), smul_add]

set_option maxHeartbeats 1600000 in
lemma RectangleIntegral'_eq_sumResiduesIn {f : ℂ → ℂ} {z w : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (f_mero : MeromorphicOn f (Rectangle z w))
    (f_no_poles_boundary : Disjoint (RectangleBorder z w) {z | meromorphicOrderAt f z < 0})
    (f_poles_finite : (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}).Finite)
    (f_simple_poles : HasSimplePolesOn f (Rectangle z w)) :
    RectangleIntegral' f z w = sumResiduesIn f (Rectangle z w ∩ {z | meromorphicOrderAt f z < 0}) := by
  let R : Set ℂ := Rectangle z w
  let poles : Set ℂ := R ∩ {u | meromorphicOrderAt f u < 0}
  let polesFin : Finset ℂ := f_poles_finite.toFinset
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  let principalPart : ℂ → ℂ := fun s ↦ ∑ p ∈ polesFin, residue fNF p / (s - p)
  let holoPart : ℂ → ℂ := toMeromorphicNFOn (fNF - principalPart) R
  have h_residue_congr : sumResiduesIn f poles = sumResiduesIn fNF poles := by
    rw [sumResiduesIn, sumResiduesIn]
    apply tsum_congr
    intro p
    exact (residue_toMeromorphicNFOn_eq_residue p.2.1 f_mero f_simple_poles p.2.2).symm
  have h_principalPart_integral : RectangleIntegral' principalPart z w = sumResiduesIn fNF poles := by
    have h_sum : RectangleIntegral' principalPart z w = ∑ p ∈ polesFin, residue fNF p := by
      apply rectangleIntegral'_sum_div_sub zRe_le_wRe zIm_le_wIm
      · intro p hp
        dsimp [polesFin, poles, R] at hp
        simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hp
        exact hp.1
      · exact Disjoint.mono_right (by rw [f_poles_finite.coe_toFinset]; exact Set.inter_subset_right) f_no_poles_boundary
    rw [h_sum]
    have h_eq_poles : poles = ↑polesFin := by
      dsimp [poles, polesFin, R]
      exact f_poles_finite.coe_toFinset.symm
    rw [sumResiduesIn, h_eq_poles,
      tsum_fintype (f := fun p : (polesFin : Set ℂ) => residue fNF p),
      ← Finset.sum_coe_sort polesFin]; rfl
  calc
    RectangleIntegral' f z w = RectangleIntegral' fNF z w := rectangleIntegral'_toMeromorphicNFOn_eq f_mero
    _ = RectangleIntegral' holoPart z w + RectangleIntegral' principalPart z w :=
      toMeromorphicNFOn_add_integral f_mero f_no_poles_boundary f_poles_finite f_simple_poles
    _ = 0 + sumResiduesIn fNF poles := by
      rw [h_principalPart_integral]
      rw [RectangleIntegral',
        (holoPart_holomorphicOn f_mero f_simple_poles f_poles_finite).vanishesOnRectangle subset_rfl]
      simp
    _ = sumResiduesIn fNF poles := by simp
    _ = sumResiduesIn f poles := h_residue_congr.symm

set_option maxHeartbeats 1600000 in
lemma residue_eq_zero_of_not_pole_of_meromorphicAt {F : ℂ → ℂ} {s : ℂ}
    (hs_mero : MeromorphicAt F s) (hs_not_pole : 0 ≤ meromorphicOrderAt F s) :
    residue F s = 0 := by
  apply residue_eq_of_tendsto
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hs_mero hs_not_pole
  have hsub : Filter.Tendsto (fun z : ℂ ↦ z - s) (nhdsWithin s {s}ᶜ) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  simpa using hsub.mul hc

set_option maxHeartbeats 1600000 in
lemma sumResiduesIn_inter_eq_of_set_eq {F : ℂ → ℂ} {Rn S2 P : Set ℂ}
    (h_set_eq : Rn ∩ P = S2 ∩ P)
    (h_residue_zero : ∀ s ∈ S2, s ∉ P → residue F s = 0) :
    sumResiduesIn F (Rn ∩ P) = sumResiduesIn F S2 := by
  rw [sumResiduesIn, sumResiduesIn, tsum_subtype, tsum_subtype]
  apply tsum_congr
  intro s
  by_cases hs_S2 : s ∈ S2
  · by_cases hs_pole : s ∈ P
    · have hs_rect_pole : s ∈ Rn ∩ P := h_set_eq.symm ▸ ⟨hs_S2, hs_pole⟩
      simp [hs_S2, hs_rect_pole]
    · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_pole hs.2
      have hres0 : residue F s = 0 := h_residue_zero s hs_S2 hs_pole
      simp [hs_S2, hs_not_rect_pole, hres0]
  · have hs_not_rect_pole : s ∉ Rn ∩ P := fun hs => hs_S2 (h_set_eq ▸ hs).1
    simp [hs_S2, hs_not_rect_pole]

end

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/EulerMaclaurin.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: none (verbatim copy).
New in the v4.32.2 port set: upstream split this file's content (the first-order
Euler–Maclaurin section: B1 ... sum_eq_integral_add_integral_deriv) out of
PrimeNumberTheoremAnd/Mertens.lean, where our original v4.29.0 port carried it
inside Zeta23/FromPNTPlus/Mertens.lean; that file now imports this one instead.
Added when the project moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

/- Module Zeta23.FromPNTPlus.EulerMaclaurin -/
section
open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by unfold B1; fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to Zeta23.FromPNTPlus.*, and added a (name := ...) tag to the local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/- Module Zeta23.FromPNTPlus.ZetaBounds -/
section
open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]

theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : riemannZeta0 N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf

lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1

lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1

lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp

lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s

lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)

lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]

open MeasureTheory

lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

open MeasureTheory

lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub

lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num

lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos

lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h

lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop

open MeasureTheory

lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]

lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)

open MeasureTheory

lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

open MeasureTheory

lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp

open MeasureTheory

lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf

noncomputable def riemannZeta0' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (riemannZeta0 N) (riemannZeta0' N s) s := by
  unfold riemannZeta0 riemannZeta0'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1

lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (riemannZeta0 N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

lemma HolomorphicOn_riemannZeta :
    HolomorphicOn riemannZeta {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_setOf_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_setOf_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_setOf_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_setOf_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity

lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    riemannZeta0 N s = riemannZeta s := by
  let f := riemannZeta
  let g := riemannZeta0 N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, setOf_subset_setOf, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [setOf_subset_setOf, imp_self, forall_const, mem_setOf_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast

open MeasureTheory

open MeasureTheory

open MeasureTheory

open MeasureTheory

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.RvM.ZetaGrowth -/
section
open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23

namespace RvM

set_option maxHeartbeats 1600000 in
theorem analyticOnNhd_riemannZeta {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S := by
  have h : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)

set_option maxHeartbeats 1600000 in
theorem norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hint := ZetaBnd_aux1b 1 le_rfl (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one, Real.one_rpow] at hint
  rw [← Zeta0EqZeta (N := 1) one_pos hσ hs]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  calc ‖(1 : ℂ) + -1 / (1 - s) + -1 / 2 + s * J‖
      = ‖(1 / 2 : ℂ) + -(1 / (1 - s)) + s * J‖ := by ring_nf
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖-(1 / (1 - s))‖ + ‖s * J‖ := norm_add₃_le
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * ‖J‖ := by
        simp [norm_neg]
    _ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * (1 / s.re) := by gcongr
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by ring

set_option maxHeartbeats 1600000 in
theorem zeta_growth_right_at (s : ℂ) (hσ : (0.15 : ℝ) ≤ s.re) (h1 : 1 ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ 20 / 3 * (|s.im| + 3) ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  have hσpos : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at h1
  have h := norm_riemannZeta_le_of_re_pos hσpos hs1
  have h1' : 1 / ‖1 - s‖ ≤ 1 := by
    rw [norm_sub_rev] at h1
    rw [div_le_one (by linarith)]
    exact h1
  have hσ' : (3 : ℝ) / 20 ≤ s.re := by
    have := hσ; norm_num at this ⊢; linarith
  have h2 : ‖s‖ / s.re ≤ 1 + 20 / 3 * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hσpos] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / (3 / 20) := by gcongr
      _ = 1 + 20 / 3 * |s.im| := by ring
  have ht : 0 ≤ |s.im| := abs_nonneg _
  linarith [h, h1', h2, ht]

set_option maxHeartbeats 1600000 in
theorem zeta_growth_right :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A :=
  ⟨1, 20 / 3, by norm_num, zeta_growth_right_at⟩

set_option maxHeartbeats 1600000 in
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hsum : Summable f := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs1
    have := (summable_nat_add_iff 1).mpr h0
    simpa [f] using this
  have hzeta : riemannZeta s = ∑' n, f n := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hf0 : f 0 = 1 := by simp [f]
  have hsplit : riemannZeta s - 1 = ∑' n, f (n + 1) := by
    rw [hzeta, hsum.tsum_eq_zero_add, hf0]; ring
  
  have hle : ∀ n : ℕ, ‖f (n + 1)‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have hpos : 0 < n + 2 := by omega
    have hf1 : f (n + 1) = 1 / ((n + 2 : ℕ) : ℂ) ^ s := by
      simp only [f]
      congr 2
      push_cast
      ring
    rw [hf1, norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hpos]
    have hbase : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
    calc 1 / ((n + 2 : ℕ) : ℝ) ^ s.re ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ 2 :=
          one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((n : ℝ) + 2) ^ 2 := by push_cast; ring
  have htwo : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n => by ring
  rw [hsplit]
  have hsum' : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).mpr hsum
  calc ‖∑' n, f (n + 1)‖ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := hsum'.norm.tsum_le_tsum hle htwo.summable
    _ = Real.pi ^ 2 / 6 - 1 := htwo.tsum_eq

set_option maxHeartbeats 1600000 in
lemma pi_sq_div_six_sub_one_lt_one : Real.pi ^ 2 / 6 - 1 < 1 := by
  have := Real.pi_lt_d2  
  nlinarith [Real.pi_pos]

set_option maxHeartbeats 1600000 in
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith

set_option maxHeartbeats 1600000 in
lemma one_third_lt_two_sub_pi_sq_div_six : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

set_option maxHeartbeats 1600000 in
theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := by
  intro t
  have h := norm_riemannZeta_ge_of_two_le_re (s := 2 + t * I) (by simp)
  linarith [one_third_lt_two_sub_pi_sq_div_six]

end RvM

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.RvM.Halving -/
section
open Set

noncomputable section

namespace Zeta23

set_option maxHeartbeats 1600000 in
@[simp] lemma reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]

set_option maxHeartbeats 1600000 in
@[simp] lemma reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

set_option maxHeartbeats 1600000 in
@[simp] lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  simp [reflect]

set_option maxHeartbeats 1600000 in
lemma reflect_injective : Function.Injective reflect :=
  Function.LeftInverse.injective reflect_reflect

namespace ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

set_option maxHeartbeats 1600000 in
lemma reflect_mem_window {ρ : ℂ} (h : ρ ∈ Z.window T₁ T₂) : reflect ρ ∈ Z.window T₁ T₂ :=
  ⟨Z.reflect_mem ρ h.1, by simpa [reflect_im] using h.2⟩

set_option maxHeartbeats 1600000 in
theorem N_le_two_mul_half :
    (Z.N T₁ T₂ : ℝ) ≤ 2 * ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re}, (Z.mult ρ : ℝ) := by
  have hW : (Z.window T₁ T₂).Finite := Z.window_finite T₁ T₂
  set A := Z.window T₁ T₂ ∩ {ρ | ρ.re < 1 / 2} with hAdef
  set B := Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re} with hBdef
  have hA : A.Finite := hW.subset inter_subset_left
  have hB : B.Finite := hW.subset inter_subset_left
  have hWAB : Z.window T₁ T₂ = A ∪ B := by
    ext ρ
    simp only [hAdef, hBdef, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      rcases lt_or_ge ρ.re (1 / 2) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    simp only [mem_setOf_eq] at h1 h2
    linarith
  have hN : Z.N T₁ T₂ = ∑ᶠ ρ ∈ A, Z.mult ρ + ∑ᶠ ρ ∈ B, Z.mult ρ := by
    unfold ZeroConfig.N
    rw [hWAB, finsum_mem_union hdisj hA hB]
  have himage : reflect '' A ⊆ B := by
    rintro _ ⟨ρ, ⟨hρW, hlt⟩, rfl⟩
    refine ⟨Z.reflect_mem_window T₁ T₂ hρW, ?_⟩
    simp only [mem_setOf_eq, reflect_re] at hlt ⊢
    linarith
  have hAB : ∑ᶠ ρ ∈ A, Z.mult ρ ≤ ∑ᶠ ρ ∈ B, Z.mult ρ := by
    calc ∑ᶠ ρ ∈ A, Z.mult ρ = ∑ᶠ ρ ∈ A, Z.mult (reflect ρ) :=
          finsum_mem_congr rfl (fun ρ hρ => (Z.mult_reflect ρ hρ.1.1).symm)
      _ = ∑ᶠ σ ∈ reflect '' A, Z.mult σ := (finsum_mem_image reflect_injective.injOn).symm
      _ ≤ ∑ᶠ σ ∈ B, Z.mult σ := Z.finsum_mult_mono T₁ T₂ himage inter_subset_left
  have hcast : (∑ᶠ ρ ∈ B, (Z.mult ρ : ℝ)) = ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
      Nat.cast_sum]
  rw [hcast, hN]
  have hAB' : ((∑ᶠ ρ ∈ A, Z.mult ρ : ℕ) : ℝ) ≤ ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    exact_mod_cast hAB
  push_cast
  linarith

end ZeroConfig

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.RvM.LocalCount -/
section
open Complex Set Filter Topology Metric

noncomputable section

namespace Zeta23.RvM

set_option maxHeartbeats 1600000 in
theorem riemannZeta_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hK.elim_nhds_subcover t (fun z _ => ht z)
  refine (I.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro ρ ⟨hρK, hρ⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ⟩

def gfun (s₀ c u : ℂ) (z : ℂ) : ℂ := riemannZeta (s₀ + c * z) * u

set_option maxHeartbeats 1600000 in
lemma comp_affine_analyticAt {s₀ c z : ℂ} (h : s₀ + c * z ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (s₀ + c * z)) z := by
  have hζ : AnalyticAt ℂ riemannZeta (s₀ + c * z) := riemannZeta_analyticOnNhd_compl_one _ h
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) z := by fun_prop
  exact hζ.comp_of_eq haff rfl

set_option maxHeartbeats 1600000 in
lemma gfun_analyticAt {s₀ c u z : ℂ} (h : s₀ + c * z ≠ 1) : AnalyticAt ℂ (gfun s₀ c u) z := by
  have h1 := comp_affine_analyticAt h
  have h2 : AnalyticAt ℂ (fun _ : ℂ => u) z := analyticAt_const
  have := h1.mul h2
  exact this

set_option maxHeartbeats 1600000 in
lemma analyticOrderNatAt_gfun {s₀ c u w : ℂ} (hc : c ≠ 0) (hu : u ≠ 0) (h : s₀ + c * w ≠ 1) :
    analyticOrderNatAt (gfun s₀ c u) w = zeroMult (s₀ + c * w) := by
  unfold analyticOrderNatAt zeroMult gfun
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) w := by fun_prop
  have hcomp : AnalyticAt ℂ (fun z => riemannZeta (s₀ + c * z)) w := comp_affine_analyticAt h
  have hmul : (fun z ↦ riemannZeta (s₀ + c * z) * u) =
      (fun z => riemannZeta (s₀ + c * z)) * fun _ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    (analyticAt_const).analyticOrderAt_eq_zero.mpr hu
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => s₀ + c * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']; simpa using hc
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) haff hderiv
  simpa [Function.comp_def] using this

def NhalfR (t : ℝ) : ℝ := ∑ᶠ ρ ∈ zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re}, (zeroMult ρ : ℝ)

set_option maxHeartbeats 1600000 in
theorem half_count_large :
    ∃ A₁ : ℝ, ∀ t : ℝ, 4 ≤ |t| → NhalfR t ≤ A₁ * Real.log (|t| + 3) := by
  obtain ⟨A, C, hC, hgrowth⟩ := zeta_growth_right
  have hL := zeta_lower_bound_two
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  refine ⟨1 / Real.log (R / r) * (|Real.log (3 * C)| + 2 * A'), fun t ht => ?_⟩
  
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hζc₀ : (1/3 : ℝ) ≤ ‖riemannZeta c₀‖ := by simpa [hc₀] using hL (t + 1/2)
  have hζc₀ne : riemannZeta c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζc₀; norm_num at hζc₀
  set u : ℂ := (riemannZeta c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hζc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g : ℂ → ℂ := gfun c₀ κ u with hg
  
  have hc₀1 : |t + 1/2| ≤ ‖c₀ - 1‖ := by
    have : (c₀ - 1).im = t + 1/2 := by simp [hc₀]
    rw [← this]; exact Complex.abs_im_le_norm _
  have ht' : 3.5 ≤ |t + 1/2| := by
    rcases le_abs'.mp ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hdist : ∀ z : ℂ, ‖z‖ ≤ 1 → |t + 1/2| - 1.9 * ‖z‖ ≤ ‖c₀ + κ * z - 1‖ := by
    intro z hz
    have h1 : ‖c₀ - 1‖ - ‖κ * z‖ ≤ ‖c₀ + κ * z - 1‖ := by
      have := norm_sub_norm_le (c₀ - 1) (-(κ * z))
      rw [norm_neg] at this
      have e : c₀ - 1 - -(κ * z) = c₀ + κ * z - 1 := by ring
      rw [e] at this; linarith
    rw [norm_mul, hnormκ] at h1; linarith
  have hne1 : ∀ z : ℂ, ‖z‖ ≤ 1 → c₀ + κ * z ≠ 1 := by
    intro z hz h
    have := hdist z hz
    rw [h, sub_self, norm_zero] at this
    nlinarith
  
  have hfAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact gfun_analyticAt (hne1 z hz)
  have hg0 : g 0 = 1 := by simp [hg, gfun, hu, hζc₀ne]
  have hfin : (SetOfZeros 1 g).Finite := by
    have hK := riemannZeta_zeros_finite_of_isCompact (isCompact_closedBall c₀ (1.9 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    refine ⟨c₀ + κ * z, ⟨?_, hne1 z hz, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormκ]; nlinarith [norm_nonneg z]
    · simpa [hg, gfun, hu0] using hgz
    · show (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ0]
  set B : ℝ := 3 * C * (|t| + 6) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num [hR])
    set s : ℂ := c₀ + κ * z with hs
    have hsre : (0.15:ℝ) ≤ s.re := by
      have : s.re = 2 + 1.9 * z.re := by norm_num [hs, hc₀, hκ]
      rw [this]
      obtain ⟨h1, -⟩ := abs_le.mp ((abs_re_le_norm z).trans hz)
      rw [hR] at h1; nlinarith
    have hs1 : 1 ≤ ‖s - 1‖ := by have := hdist z hz1; rw [hR] at hz; nlinarith
    have hsim : |s.im| + 3 ≤ |t| + 6 := by
      have : s.im = t + 1/2 + 1.9 * z.im := by norm_num [hs, hc₀, hκ]
      rw [this]
      have hzi := (abs_im_le_norm z).trans hz; rw [hR] at hzi
      have h1 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h2 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]; nlinarith
      have h3 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have h1 : ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A := hgrowth s hsre hs1
    have hbase : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have h2 : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' := Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have h3 : (|s.im| + 3) ^ A' ≤ (|t| + 6) ^ A' := Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) hsim hA'0
    calc ‖g z‖ = ‖riemannZeta s‖ * ‖u‖ := by simp [hg, gfun, hs]
      _ ≤ (C * (|t| + 6) ^ A') * 3 := by
          apply mul_le_mul (h1.trans ((mul_le_mul_of_nonneg_left (h2.trans h3) hC.le))) hnu (norm_nonneg _)
          positivity
      _ = B := by rw [hB]; ring
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hg0 hfin hfz
  
  set W : Set ℂ := zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := (zetaZeroConfig.window_finite t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ : IsNontrivialZero ρ := hρZ
    refine ⟨?_, ?_⟩
    · 
      simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ) = 0
      simp only [hg, gfun, hφinv]; rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, (zeroMult ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    have hρ : IsNontrivialZero ρ := hρZ
    rw [analyticOrderNatAt_gfun hκ0 hu0 (by rw [hφinv]; exact hρ.not_trivial.2), hφinv]
  
  have hsum : NhalfR t ≤ ((∑ ρ' ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold NhalfR
    rw [← hW, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have hlogB : Real.log B ≤ (|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    have h1 := le_abs_self (Real.log (3 * C))
    have h2 : |Real.log (3 * C)| ≤ |Real.log (3 * C)| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3
    have h3 : A' * Real.log (|t| + 6) ≤ A' * (2 * Real.log (|t| + 3)) :=
      mul_le_mul_of_nonneg_left hlog6 hA'0
    linarith
  calc NhalfR t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem count_small (t : ℝ) (ht : |t| ≤ 4) : (Ncount t (t + 1) : ℝ) ≤ Ncount (-4) 5 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have hsub : zetaZeroConfig.window t (t + 1) ⊆ zetaZeroConfig.window (-4) 5 := by
    rintro ρ ⟨hρ, ha, hb⟩; exact ⟨hρ, by linarith, by linarith⟩
  have h' : zetaZeroConfig.N t (t + 1) ≤ zetaZeroConfig.N (-4) 5 :=
    zetaZeroConfig.finsum_mult_mono (-4) 5 hsub subset_rfl
  rw [zetaZeroConfig_N, zetaZeroConfig_N] at h'
  exact_mod_cast h'

set_option maxHeartbeats 1600000 in
theorem zeta_local_zero_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₁, hA₁⟩ := half_count_large
  set K : ℝ := (Ncount (-4) 5 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max 1 (max (2 * A₁) K), le_max_left _ _, fun t => ?_⟩
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hhalf : (Ncount t (t + 1) : ℝ) ≤ 2 * NhalfR t := by
    have := zetaZeroConfig.N_le_two_mul_half t (t + 1)
    simpa [NhalfR, zetaZeroConfig_N] using this
  rcases le_or_gt 4 |t| with ht | ht
  · calc (Ncount t (t + 1) : ℝ) ≤ 2 * NhalfR t := hhalf
      _ ≤ 2 * (A₁ * Real.log (|t| + 3)) := by
          have := hA₁ t ht; nlinarith
      _ = (2 * A₁) * Real.log (|t| + 3) := by ring
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_left _ _) (le_max_right _ _)
  · calc (Ncount t (t + 1) : ℝ) ≤ K := count_small t ht.le
      _ ≤ K * Real.log (|t| + 3) := le_mul_of_one_le_right hK0 hlog3
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_right _ _) (le_max_right _ _)

end Zeta23.RvM

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.WeilEF.XiLogDeriv -/
section
noncomputable section

namespace Zeta23

namespace WeilEF

open Complex Filter Topology

lemma differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun u : ℂ => Gamma (u / 2)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp s (differentiableAt_id.div_const _)
    have := congrArg Complex.re hm
    simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have : Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Gamma (u / 2) := funext Gammaℝ_def
  rw [this]
  exact h1.mul h2

lemma analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (fun u hu => (differentiableAt_Gammaℝ hu).differentiableWithinAt)
    (hopen.mem_nhds hs)

lemma completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hΓ := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    (fun _ hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

theorem logDeriv_completedZeta (s : ℂ) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hstrip : 0 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hev := completedZeta_eventuallyEq_mul hstrip
  have heq : logDeriv completedRiemannZeta s = logDeriv (fun u => Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos hstrip) hζ (differentiableAt_Gammaℝ hstrip)
    (differentiableAt_riemannZeta hs1)

theorem logDeriv_completedZeta_one_sub (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have hcomp : completedRiemannZeta = completedRiemannZeta ∘ (fun u : ℂ => 1 - u) := by
    funext u; simp [completedRiemannZeta_one_sub]
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta (sub_ne_zero.mpr (Ne.symm hs1)) (by
      intro h; apply hs0; linear_combination -h)
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s := (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring

end WeilEF

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.Analytic.RectangleLogDeriv -/
section
open Complex Set Topology Filter Asymptotics Real

noncomputable section

namespace Zeta23

namespace Analytic

set_option maxHeartbeats 1600000 in
theorem residueTheorem_finset {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (S : Finset ℂ) (A : ℂ → ℂ)
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ (S : Set ℂ)))
    (near : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = ∑ p ∈ S, A p := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.coe_empty, sdiff_empty] at fHolo
    rw [Finset.sum_empty]
    show (1 / (2 * π * I)) • RectangleIntegral f z w = 0
    rw [fHolo.vanishesOnRectangle subset_rfl, smul_zero]
  | @insert p S hpS ih =>
    have hp : Rectangle z w ∈ 𝓝 p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, Rectangle z w ∈ 𝓝 q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    
    set P : ℂ → ℂ := fun s => A p / (s - p) with hP
    set f₁ : ℂ → ℂ := f - P with hf₁
    set f₂ : ℂ → ℂ := Function.update f₁ p (limUnder (𝓝[≠] p) f₁) with hf₂
    have hPdiff : ∀ s, s ≠ p → DifferentiableAt ℂ P s := by
      intro s hs
      have : s - p ≠ 0 := sub_ne_zero.mpr hs
      simp only [hP]
      fun_prop (disch := assumption)
    have hf₁holo : HolomorphicOn f₁ (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) := by
      refine fHolo.sub ?_
      intro s hs
      apply (hPdiff s ?_).differentiableWithinAt
      intro h
      apply hs.2
      simp [h]
    have hSclosed : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
    have hRS : Rectangle z w \ (S : Set ℂ) ∈ 𝓝 p := by
      apply Filter.inter_mem hp
      exact hSclosed.isOpen_compl.mem_nhds (by simpa using hpS)
    obtain ⟨U, hU, hbdd⟩ := IsBigO_to_BddAbove (near p (Finset.mem_insert_self p S))
    have hV : U ∩ (Rectangle z w \ (S : Set ℂ)) ∈ 𝓝 p := Filter.inter_mem hU hRS
    have hf₁V : DifferentiableOn ℂ f₁ ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p}) := by
      apply hf₁holo.mono
      rintro s ⟨⟨_, hsR, hsS⟩, hsp⟩
      refine ⟨hsR, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨by simpa using hsp, by simpa using hsS⟩
    have hbddV : BddAbove (norm ∘ f₁ '' ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p})) :=
      hbdd.mono (image_mono (Set.sdiff_subset_sdiff_left inter_subset_left))
    have hf₂V : DifferentiableOn ℂ f₂ (U ∩ (Rectangle z w \ (S : Set ℂ))) :=
      differentiableOn_update_limUnder_of_bddAbove hV hf₁V hbddV
    have hf₂eq : ∀ s, s ≠ p → f₂ s = f₁ s := fun s hs => Function.update_of_ne hs _ _
    
    have hf₂holo : HolomorphicOn f₂ (Rectangle z w \ (S : Set ℂ)) := by
      intro s hs
      by_cases hsp : s = p
      · rw [hsp]
        exact (hf₂V.differentiableAt hV).differentiableWithinAt
      · have h1 : DifferentiableWithinAt ℂ f₁
            (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) s :=
          hf₁holo s ⟨hs.1, by
            simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
            exact ⟨hsp, by simpa using hs.2⟩⟩
        have hset : (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ))
            = (Rectangle z w \ (S : Set ℂ)) ∩ {p}ᶜ := by
          ext x
          simp only [Finset.coe_insert, Set.mem_sdiff, mem_insert_iff, Finset.mem_coe, not_or,
            mem_inter_iff, mem_compl_iff, mem_singleton_iff]
          tauto
        rw [hset] at h1
        have hpc : {p}ᶜ ∈ 𝓝[Rectangle z w \ (S : Set ℂ)] s :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
        rw [differentiableWithinAt_inter' hpc] at h1
        refine h1.congr_of_eventuallyEq ?_ (hf₂eq s hsp)
        filter_upwards [hpc] with x hx
        exact hf₂eq x hx
    
    have near₂ : ∀ q ∈ S, (f₂ - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
      intro q hq
      have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      have hev : ((f - fun s => A q / (s - q)) - P)
          =ᶠ[𝓝[≠] q] (f₂ - fun s => A q / (s - q)) := by
        have : {p}ᶜ ∈ 𝓝[≠] q :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hqp)
        filter_upwards [this] with s hs
        simp only [Pi.sub_apply, hf₂eq s hs, hf₁]
        ring
      have hPO : P =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
        have hc : ContinuousAt P q := (hPdiff q hqp).continuousAt
        exact (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      exact ((near q (Finset.mem_insert_of_mem hq)).sub hPO).congr' hev EventuallyEq.rfl
    have ih' := ih hS' hf₂holo near₂
    
    have hborder : EqOn f (f₂ + P) (RectangleBorder z w) := by
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      simp only [Pi.add_apply, hf₂eq s hsp, hf₁, Pi.sub_apply, sub_add_cancel]
    have hbS : ∀ s ∈ RectangleBorder z w, s ∈ Rectangle z w \ (S : Set ℂ) := fun s hs =>
      ⟨rectangleBorder_subset_rectangle z w hs,
        fun hsS => not_mem_rectangleBorder_of_rectangle_mem_nhds (hS' s hsS) hs⟩
    have hi₂ : RectangleBorderIntegrable f₂ z w :=
      ContinuousOn.rectangleBorder_integrable (hf₂holo.continuousOn.mono hbS)
    have hiP : RectangleBorderIntegrable P z w := by
      apply ContinuousOn.rectangleBorder_integrable
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      exact (hPdiff s hsp).continuousAt.continuousWithinAt
    rw [RectangleIntegral'_congr hborder, Finset.sum_insert hpS]
    show (1 / (2 * π * I)) • RectangleIntegral (f₂ + P) z w = _
    rw [RectangleBorderIntegrable.add hi₂ hiP, smul_add]
    show RectangleIntegral' f₂ z w + RectangleIntegral' P z w = _
    rw [ih', ResidueTheoremInRectangle hre him hp, add_comm]

set_option maxHeartbeats 1600000 in
theorem rectangleIntegral'_mul_logDeriv_of_poles {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (Z P : Finset ℂ) (hZP : Disjoint Z P)
    (hPint : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w \ (P : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (hZ : ∀ s ∈ Rectangle z w \ (P : Set ℂ), f s = 0 ↔ s ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w)
    (m : ℂ → ℕ)
    (hpole : ∀ p ∈ P, ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun s => (s - p) ^ m p * f s) (𝓝[≠] p) (𝓝 c)) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ - ∑ p ∈ P, (m p : ℂ) * g p := by
  classical
  have hZnotP : ∀ ρ ∈ Z, ρ ∉ P := fun ρ hρ hρP => Finset.disjoint_left.mp hZP hρ hρP
  have hZmem : ∀ ρ ∈ Z, ρ ∈ Rectangle z w \ (P : Set ℂ) := fun ρ hρ =>
    ⟨hZsub hρ, by simpa using hZnotP ρ hρ⟩
  
  have hZint : ∀ ρ ∈ Z, Rectangle z w ∈ 𝓝 ρ := by
    intro ρ hρ
    have hρR : ρ ∈ Rectangle z w := hZsub hρ
    have hρB : ρ ∉ RectangleBorder z w := fun h => hborder ρ h ((hZ ρ (hZmem ρ hρ)).mpr hρ)
    obtain ⟨h1, h2⟩ := hρR
    have h1' : z.re ≤ ρ.re ∧ ρ.re ≤ w.re := by simpa [uIcc_of_le hre] using h1
    have h2' : z.im ≤ ρ.im ∧ ρ.im ≤ w.im := by simpa [uIcc_of_le him] using h2
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, not_or] at hρB
    obtain ⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩ := hρB
    rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hre, uIoo_of_le him]
    refine ⟨⟨lt_of_le_of_ne h1'.1 (fun h => hb2 ⟨h.symm, h2⟩),
      lt_of_le_of_ne h1'.2 (fun h => hb4 ⟨h, h2⟩)⟩,
      ⟨lt_of_le_of_ne h2'.1 (fun h => hb1 ⟨h1, h.symm⟩),
      lt_of_le_of_ne h2'.2 (fun h => hb3 ⟨h1, h⟩)⟩⟩
  
  let A : ℂ → ℂ := fun q => if q ∈ P then -((m q : ℂ) * g q) else (analyticOrderNatAt f q : ℂ) * g q
  have hint : ∀ q ∈ Z ∪ P, Rectangle z w ∈ 𝓝 q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    exacts [hZint q hq, hPint q hq]
  have key := residueTheorem_finset (f := fun s => g s * logDeriv f s) hre him (Z ∪ P) A hint
    ?holo ?near
  · rw [key, Finset.sum_union hZP]
    have hZsum : ∑ q ∈ Z, A q = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ :=
      Finset.sum_congr rfl (fun q hq => by simp [A, hZnotP q hq])
    have hPsum : ∑ q ∈ P, A q = -∑ p ∈ P, (m p : ℂ) * g p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun q hq => by simp [A, hq])
    rw [hZsum, hPsum, sub_eq_add_neg]
  case holo =>
    intro s hs
    have hsP : s ∉ P := fun h => hs.2 (by simp [h])
    have hsZ : s ∉ Z := fun h => hs.2 (by simp [h])
    have hsRP : s ∈ Rectangle z w \ (P : Set ℂ) := ⟨hs.1, by simpa using hsP⟩
    have hfs : f s ≠ 0 := fun h => hsZ ((hZ s hsRP).mp h)
    have hfa := hf s hsRP
    have hga := hg s hs.1
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun s => g s * (deriv f s / f s)) s
    exact hga.differentiableAt.mul (hfa.deriv.differentiableAt.div hfa.differentiableAt hfs)
  case near =>
    intro q hq
    rcases Finset.mem_union.mp hq with hρ | hp
    · 
      have hρRP := hZmem q hρ
      have hga := hg q (hZsub hρ)
      have hA : A q = (analyticOrderNatAt f q : ℂ) * g q := by simp [A, hZnotP q hρ]
      by_cases htop : analyticOrderAt f q = ⊤
      · 
        have h0 : ∀ᶠ s in 𝓝 q, f s = 0 := analyticOrderAt_eq_top.mp htop
        have hO : (fun _ : ℂ => (0 : ℂ)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := isBigO_zero _ _
        refine hO.congr' ?_ EventuallyEq.rfl
        filter_upwards [mem_nhdsWithin_of_mem_nhds (h0.eventually_nhds)] with s hs
        have hs' : f =ᶠ[𝓝 s] fun _ => (0 : ℂ) := hs
        have hds : deriv f s = 0 := by
          rw [hs'.deriv_eq]; simp
        simp [hA, logDeriv_apply, hds, analyticOrderNatAt, htop]
      obtain ⟨h, hh, hh0, hfh⟩ := (hf q hρRP).analyticOrderAt_ne_top.mp htop
      have hh_ne : ∀ᶠ s in 𝓝 q, h s ≠ 0 := hh.continuousAt.eventually_ne hh0
      have h2 : ∀ᶠ s in 𝓝 q, f =ᶠ[𝓝 s] (fun s => (s - q) ^ analyticOrderNatAt f q • h s) :=
        hfh.eventually_nhds
      have h3 : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ h s := hh.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q)) + g s * logDeriv h s
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h2,
          mem_nhdsWithin_of_mem_nhds hh_ne, mem_nhdsWithin_of_mem_nhds h3]
          with s hs hfs hhs hhas
        have hsq : s - q ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
        have hld : logDeriv f s = (analyticOrderNatAt f q : ℂ) / (s - q) + logDeriv h s := by
          have e1 : logDeriv f s
              = logDeriv (fun s => (s - q) ^ analyticOrderNatAt f q * h s) s := by
            simp only [logDeriv_apply, hfs.deriv_eq, hfs.self_of_nhds, smul_eq_mul]
          rw [e1, logDeriv_mul (f := fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) (g := h) s
            (pow_ne_zero _ hsq) hhs (by fun_prop) hhas.differentiableAt]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) s
              = (analyticOrderNatAt f q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q)
                = (fun x : ℂ => x ^ analyticOrderNatAt f q) ∘ (fun s => s - q) from rfl,
              logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        simp only [Pi.sub_apply, hld, hA]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv h s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv h q)) := by
        have : ContinuousAt (fun s => g s * logDeriv h s) q := by
          show ContinuousAt (fun s => g s * (deriv h s / h s)) q
          exact hga.continuousAt.mul (hh.deriv.continuousAt.div hh.continuousAt hh0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q))
          + g s * logDeriv h s) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        ((hslope.const_mul (analyticOrderNatAt f q : ℂ)).add hcont).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl
    · 
      obtain ⟨c, hc, hT⟩ := hpole q hp
      have hqR : q ∈ Rectangle z w := mem_of_mem_nhds (hPint q hp)
      have hga := hg q hqR
      have hA : A q = -((m q : ℂ) * g q) := by simp [A, hp]
      
      set F : ℂ → ℂ := fun s => (s - q) ^ m q * f s with hF
      set G : ℂ → ℂ := Function.update F q c with hG
      have hGq : G q = c := Function.update_self _ _ _
      have hGF : ∀ s, s ≠ q → G s = F s := fun s hs => Function.update_of_ne hs _ _
      have hPc : ((P : Set ℂ) \ {q})ᶜ ∈ 𝓝 q :=
        (P.finite_toSet.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
      have hnear : ∀ᶠ s in 𝓝[≠] q, s ≠ q ∧ s ∈ Rectangle z w \ (P : Set ℂ) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hPint q hp),
          mem_nhdsWithin_of_mem_nhds hPc, self_mem_nhdsWithin] with s h1 h2 h3
        have h3' : s ≠ q := by simpa using h3
        exact ⟨h3', h1, fun hsP => h2 ⟨hsP, by simpa using h3'⟩⟩
      have hGdiff : ∀ᶠ s in 𝓝[≠] q, DifferentiableAt ℂ G s := by
        filter_upwards [hnear] with s ⟨hsq, hsRP⟩
        have hFs : DifferentiableAt ℂ F s :=
          ((differentiableAt_id.sub_const q).pow _).mul (hf s hsRP).differentiableAt
        refine hFs.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
        exact hGF x hx
      have hGcont : ContinuousAt G q := by
        rw [hG, continuousAt_update_same]
        exact hT
      have hGan : AnalyticAt ℂ G q :=
        analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hGdiff hGcont
      have hG0 : G q ≠ 0 := by rwa [hGq]
      have hFne : ∀ᶠ s in 𝓝[≠] q, F s ≠ 0 := hT.eventually_ne hc
      have hGan' : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ G s := hGan.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q))
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [hnear, hFne, mem_nhdsWithin_of_mem_nhds hGan'] with s ⟨hsq, hsRP⟩ hFs hGs
        have hsq' : s - q ≠ 0 := sub_ne_zero.mpr hsq
        have hfs : f s ≠ 0 := fun h => hFs (by simp [hF, h])
        have hfd : DifferentiableAt ℂ f s := (hf s hsRP).differentiableAt
        have hldF : logDeriv F s = (m q : ℂ) / (s - q) + logDeriv f s := by
          rw [hF, logDeriv_mul (f := fun s : ℂ => (s - q) ^ m q) (g := f) s
            (pow_ne_zero _ hsq') hfs (by fun_prop) hfd]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ m q) s = (m q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ m q) = (fun x : ℂ => x ^ m q) ∘ (fun s => s - q)
                from rfl, logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        have hGFs : G =ᶠ[𝓝 s] F := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
          exact hGF x hx
        have hldG : logDeriv G s = logDeriv F s := by
          simp only [logDeriv_apply, hGFs.deriv_eq, hGFs.self_of_nhds]
        simp only [Pi.sub_apply, hA, hldG, hldF]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv G s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv G q)) := by
        have : ContinuousAt (fun s => g s * logDeriv G s) q := by
          show ContinuousAt (fun s => g s * (deriv G s / G s)) q
          exact hga.continuousAt.mul (hGan.deriv.continuousAt.div hGan.continuousAt hG0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q)))
          =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        (hcont.sub (hslope.const_mul (m q : ℂ))).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl

set_option maxHeartbeats 1600000 in
theorem rectangleIntegral'_mul_logDeriv {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w)) (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s ∈ Rectangle z w, f s = 0 ↔ s ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ := by
  have h := rectangleIntegral'_mul_logDeriv_of_poles hre him Z ∅ (Finset.disjoint_empty_right _)
    (by simp) (by simpa using hf) hg hborder (by simpa using hZ) hZsub (fun _ => 0) (by simp)
  simpa using h

end Analytic

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.RvM.GammaSide -/
section
open Complex MeasureTheory Set

open scoped Interval

noncomputable section

namespace Zeta23.RvM

def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

set_option maxHeartbeats 1600000 in
lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

set_option maxHeartbeats 1600000 in
lemma Gamma_half_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
  apply Complex.differentiableAt_Gamma
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

set_option maxHeartbeats 1600000 in
lemma Gammaℝ_differentiableOn : DifferentiableOn ℂ Complex.Gammaℝ rightHalfPlane := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s := by
    apply DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    (Gamma_half_differentiableAt hs).comp s (by fun_prop)
  have : Complex.Gammaℝ = fun s => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  rw [this]
  exact h1.mul h2

set_option maxHeartbeats 1600000 in
lemma Gammaℝ_analyticOnNhd : AnalyticOnNhd ℂ Complex.Gammaℝ rightHalfPlane :=
  Gammaℝ_differentiableOn.analyticOnNhd isOpen_rightHalfPlane

set_option maxHeartbeats 1600000 in
lemma logDeriv_Gammaℝ_differentiableOn : DifferentiableOn ℂ (logDeriv Complex.Gammaℝ) rightHalfPlane := by
  have hA := Gammaℝ_analyticOnNhd
  have hd : DifferentiableOn ℂ (deriv Complex.Gammaℝ) rightHalfPlane := hA.deriv.differentiableOn
  have : logDeriv Complex.Gammaℝ = fun s => deriv Complex.Gammaℝ s / Complex.Gammaℝ s := by
    funext s; rfl
  rw [this]
  exact hd.div hA.differentiableOn fun s hs => Complex.Gammaℝ_ne_zero_of_re_pos hs

set_option maxHeartbeats 1600000 in
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hf : (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s ≠ 0 := by
    simp only [ne_eq, cpow_eq_zero_iff, hπ, false_and, not_false_eq_true]
  have hg : (fun s : ℂ => Complex.Gamma (s / 2)) s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hdf : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ)
  have hdg : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    (Gamma_half_differentiableAt hs).comp s (by fun_prop)
  rw [e, logDeriv_mul (f := fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) (g := fun s : ℂ => Complex.Gamma (s / 2)) s hf hg hdf hdg]
  
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    have hder : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
      have : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2 : ℂ) s := by
        simpa using ((hasDerivAt_id s).neg.div_const (2:ℂ))
      exact this.const_cpow (Or.inl hπ)
    rw [logDeriv_apply, hder.deriv]
    have hne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := hf
    rw [Complex.ofReal_log Real.pi_pos.le]
    field_simp
  
  have h2 : logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) s = (1/2 : ℂ) * Complex.digamma (s / 2) := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun s : ℂ => s / 2) (x := s)
      (Gamma_half_differentiableAt hs) (by fun_prop)
    rw [show (Complex.Gamma ∘ fun s : ℂ => s / 2) = fun s => Complex.Gamma (s / 2) from rfl] at this
    rw [this, Complex.digamma_def]
    have : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
      rw [deriv_div_const, deriv_id'']
    rw [this]; ring
  rw [h1, h2]

set_option maxHeartbeats 1600000 in
theorem re_logDeriv_Gammaℝ_half (t : ℝ) :
    (logDeriv Complex.Gammaℝ (1/2 + t * I)).re = Real.pi * mu t := by
  rw [logDeriv_Gammaℝ (by simp)]
  have : ((1:ℂ)/2 + t * I) / 2 = 1 / 4 + Complex.I * t / 2 := by ring
  rw [this, mu]
  simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.mul_re,
    Complex.one_re]
  have hπ := Real.pi_ne_zero
  field_simp
  simp
  ring

set_option maxHeartbeats 1600000 in
theorem gamma_side {T₁ T₂ : ℝ} (_h0 : 0 < T₁) (_h0' : 0 < T₂) :
    (1 / Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im = ∫ t in T₁..T₂, mu t := by
  set F := logDeriv Complex.Gammaℝ with hF
  
  have hrect : (Set.uIcc (1/2:ℝ) 2 ×ℂ Set.uIcc T₁ T₂) ⊆ rightHalfPlane := by
    rintro s ⟨hre, -⟩
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hre
    show 0 < s.re
    have := hre.1
    linarith [this]
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (1/2 + T₁ * I) (2 + T₂ * I)
    (logDeriv_Gammaℝ_differentiableOn.mono (by simpa using hrect))
  simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, one_im, mul_im, zero_add, div_ofNat_re, div_ofNat_im, zero_div,
    re_ofNat, im_ofNat] at hCG
  have hhc : halfContour F T₁ T₂ = I * ∫ y : ℝ in T₁..T₂, F (1/2 + y * I) := by
    unfold halfContour
    have hthis := hCG
    simp only [smul_eq_mul] at hthis
    have hc : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by norm_num
    simp only [hc] at hthis
    
    linear_combination hthis
  rw [hhc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  
  have hcont : Continuous fun y : ℝ => F (1/2 + y * I) := by
    have hd := logDeriv_Gammaℝ_differentiableOn
    have : Continuous fun y : ℝ => ((1:ℂ)/2 + y * I) := by fun_prop
    refine (hd.continuousOn.comp_continuous this fun y => ?_)
    show 0 < ((1:ℂ)/2 + y * I).re
    simp
  rw [show ((∫ y : ℝ in T₁..T₂, F (1/2 + y * I)).re) = ∫ y : ℝ in T₁..T₂, (F (1/2 + y * I)).re from
    (Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)).symm]
  simp_rw [hF, re_logDeriv_Gammaℝ_half]
  rw [intervalIntegral.integral_const_mul]
  field_simp

set_option maxHeartbeats 1600000 in
theorem mu_continuous (hΓ : Zeta23.GammaFacts) : Continuous mu :=
  hΓ.smooth.continuous

set_option maxHeartbeats 1600000 in
theorem mu_le_log (hΓ : Zeta23.GammaFacts) : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 1 ≤ τ →
    |mu τ| ≤ C * Real.log (τ + 3) := by
  obtain ⟨C₀, hC₀⟩ := hΓ.stirling
  have hlog2π : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨1 + |C₀| + Real.log (2 * Real.pi),
    by linarith [abs_nonneg C₀], fun τ hτ => ?_⟩
  have hτ0 : (0:ℝ) < τ := by linarith
  have h1 := hC₀ τ (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at h1
  obtain ⟨hl, hr⟩ := abs_le.mp h1
  have hlog3 : 1 ≤ Real.log (τ + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlogτ0 : 0 ≤ Real.log τ := Real.log_nonneg hτ
  have hlogτ : Real.log τ ≤ Real.log (τ + 3) := Real.log_le_log hτ0 (by linarith)
  have hdiv : Real.log (τ / (2 * Real.pi)) = Real.log τ - Real.log (2 * Real.pi) :=
    Real.log_div (by linarith) (by positivity)
  rw [hdiv] at hl hr
  have hC₀τ : |C₀ / τ ^ 2| ≤ |C₀| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < τ ^ 2)]
    apply div_le_self (abs_nonneg _) (by nlinarith)
  obtain ⟨hCl, hCr⟩ := abs_le.mp hC₀τ
  have h2π : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have h2π0 : 0 < 1 / (2 * Real.pi) := by positivity
  rw [abs_le]
  constructor
  · 
    have e1 : -(Real.log (2 * Real.pi)) ≤ 1 / (2 * Real.pi) * (Real.log τ - Real.log (2 * Real.pi)) := by
      nlinarith
    nlinarith
  · have e2 : 1 / (2 * Real.pi) * (Real.log τ - Real.log (2 * Real.pi)) ≤ Real.log (τ + 3) := by
      nlinarith
    nlinarith

end Zeta23.RvM

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.RvM.BacklundDefs -/
section
open Complex

noncomputable section

namespace Zeta23

namespace RvM

def reZeroSet (T : ℝ) : Set ℝ :=
  {σ | σ ∈ Set.Icc (1/2 : ℝ) 2 ∧ (riemannZeta (σ + T * I)).re = 0}

end RvM

end Zeta23

end

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.RvM.ReZeroCount -/
section
open Complex Set Metric

noncomputable section

namespace Zeta23.RvM

set_option maxHeartbeats 1600000 in
lemma finite_zeros_closedBall {f : ℂ → ℂ} {R r : ℝ} (hrR : r < R)
    (hA : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball 0 R)
    (hfz₀ : f z₀ ≠ 0) : {z : ℂ | ‖z‖ ≤ r ∧ f z = 0}.Finite := by
  have hU : IsPreconnected (Metric.ball (0:ℂ) R) := (convex_ball 0 R).isPreconnected
  rcases hA.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h0 | hcod
  · exact absurd (h0 hz₀) hfz₀
  rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
  have hsub : Metric.closedBall (0:ℂ) r ⊆ Metric.ball 0 R := Metric.closedBall_subset_ball hrR
  
  have hloc : ∀ z ∈ Metric.closedBall (0:ℂ) r, ∃ t ∈ nhds z,
      (t ∩ {x : ℂ | x ∈ Metric.ball (0:ℂ) R ∧ f x = 0}).Finite := by
    intro z hz
    obtain ⟨t, ht, hfin⟩ := hcod z (hsub hz)
    refine ⟨t, ht, hfin.subset ?_⟩
    rintro x ⟨hxt, hxU, hx0⟩
    exact ⟨hxt, hxU, by simpa using hx0⟩
  choose t ht hfin using hloc
  obtain ⟨I, hcover⟩ := (isCompact_closedBall (0:ℂ) r).elim_nhds_subcover' t ht
  refine ((I.finite_toSet.biUnion fun z _ => hfin z z.2).subset ?_)
  rintro x ⟨hxr, hx0⟩
  have hxball : x ∈ Metric.closedBall (0:ℂ) r := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨z, hzI, hxz⟩ := Set.mem_iUnion₂.mp (hcover hxball)
  exact Set.mem_iUnion₂.mpr ⟨z, hzI, hxz, hsub hxball, hx0⟩

def symZeta (T : ℝ) (z : ℂ) : ℂ := (riemannZeta (z + T * I) + riemannZeta (z - T * I)) / 2

set_option maxHeartbeats 1600000 in
lemma ne_one_of_im_large {T : ℝ} {z : ℂ} (hT : 4 ≤ T) (hz : ‖z‖ ≤ 2) :
    z + 2 + T * I ≠ 1 ∧ z + 2 - T * I ≠ 1 := by
  constructor <;> intro h
  · have h1 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, Complex.one_im, Complex.im_ofNat] at h1
    have := Complex.abs_im_le_norm z
    have := abs_le.mp (this.trans hz)
    linarith [this.1, this.2]
  · have h1 := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, Complex.one_im, Complex.im_ofNat] at h1
    have := Complex.abs_im_le_norm z
    have := abs_le.mp (this.trans hz)
    linarith [this.1, this.2]

set_option maxHeartbeats 1600000 in
lemma symZeta_analyticAt {T : ℝ} {z : ℂ} (h1 : z + T * I ≠ 1) (h2 : z - T * I ≠ 1) :
    AnalyticAt ℂ (symZeta T) z := by
  unfold symZeta
  have ha : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z + T * I)) z := by
    have hζ : AnalyticAt ℂ riemannZeta ((fun z : ℂ => z + T * I) z) :=
      riemannZeta_analyticOnNhd_compl_one _ h1
    exact hζ.comp_of_eq (by fun_prop) rfl
  have hb : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z - T * I)) z := by
    have hζ : AnalyticAt ℂ riemannZeta ((fun z : ℂ => z - T * I) z) :=
      riemannZeta_analyticOnNhd_compl_one _ h2
    exact hζ.comp_of_eq (by fun_prop) rfl
  exact (ha.add hb).div_const

set_option maxHeartbeats 1600000 in
lemma symZeta_ofReal {T : ℝ} (σ : ℝ) (h1 : (σ:ℂ) + T * I ≠ 1) :
    symZeta T σ = (((riemannZeta ((σ:ℂ) + T * I)).re : ℝ) : ℂ) := by
  unfold symZeta
  have hconj : riemannZeta ((σ:ℂ) - T * I) = (starRingEnd ℂ) (riemannZeta ((σ:ℂ) + T * I)) := by
    have h := riemannZeta_conj (s := (σ:ℂ) + T * I) h1
    have e : (starRingEnd ℂ) ((σ:ℂ) + T * I) = (σ:ℂ) - T * I := by
      simp [Complex.ext_iff]
    rw [e] at h
    exact h
  rw [hconj, Complex.add_conj]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem reZeroSet_card_le_of_growth {A C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A) :
    ∀ T : ℝ, 4 ≤ T → (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ)
      ≤ (1 / Real.log ((0.9 : ℝ) / 0.8) * (|Real.log (6 * C)| + 2 * max A 0)) * Real.log T := by
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set r : ℝ := 0.8 with hr
  set R : ℝ := 0.9 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  intro T hT
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  
  have hne2 : (2:ℂ) + T * I ≠ 1 := by
    have := ne_one_of_im_large (T := T) (z := 0) hT (by norm_num)
    simpa using this.1
  have hsub1 := norm_riemannZeta_sub_one_le (s := 2 + T * I) (by simp)
  have hre2 : 2 - Real.pi ^ 2 / 6 ≤ (riemannZeta (2 + T * I)).re := by
    have h2 : |(riemannZeta (2 + T * I) - 1).re| ≤ Real.pi ^ 2 / 6 - 1 :=
      (Complex.abs_re_le_norm _).trans hsub1
    have h3 : (riemannZeta (2 + T * I) - 1).re = (riemannZeta (2 + T * I)).re - 1 := by simp
    rw [h3] at h2
    linarith [(abs_le.mp h2).1]
  have hthird := one_third_lt_two_sub_pi_sq_div_six
  have hg2 : symZeta T 2 = (((riemannZeta ((2:ℂ) + T * I)).re : ℝ) : ℂ) := by
    have h := symZeta_ofReal (T := T) 2 (by push_cast; exact hne2)
    push_cast at h ⊢
    exact h
  have hg2ne : symZeta T 2 ≠ 0 := by
    rw [hg2]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  set u : ℂ := (symZeta T 2)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hg2ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv, inv_le_comm₀ (by positivity) (by norm_num)]
    rw [hg2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  set G : ℂ → ℂ := fun w => symZeta T (2 + κ * w) * u with hG
  have hGanalytic : ∀ w : ℂ, ‖w‖ ≤ 1.05 → AnalyticAt ℂ G w := by
    intro w hw
    have hκw : ‖κ * w‖ ≤ 2 := by
      rw [norm_mul, hnormκ]; nlinarith [norm_nonneg w]
    obtain ⟨h1, h2⟩ := ne_one_of_im_large (z := κ * w) hT hκw
    have hs : AnalyticAt ℂ (symZeta T) (2 + κ * w) := by
      apply symZeta_analyticAt
      · rw [show (2:ℂ) + κ * w + T * I = κ * w + 2 + T * I by ring]; exact h1
      · rw [show (2:ℂ) + κ * w - T * I = κ * w + 2 - T * I by ring]; exact h2
    exact ((hs.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 + κ * w) w) rfl).mul
      analyticAt_const)
  have hG0 : G 0 = 1 := by
    simp only [hG, mul_zero, add_zero, hu]
    exact mul_inv_cancel₀ hg2ne
  
  have hball : AnalyticOnNhd ℂ G (Metric.ball 0 1.05) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hGanalytic w hw.le
  have hfin : (SetOfZeros 1 G).Finite := by
    have h := finite_zeros_closedBall (f := G) (R := 1.05) (r := 1) (by norm_num) hball
      (z₀ := 0) (by simp; norm_num) (by rw [hG0]; exact one_ne_zero)
    exact h.subset (by intro z hz; exact hz)
  
  set B : ℝ := 6 * C * (T + 5) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hκre : κ.re = 1.9 := by rw [hκ]; norm_num [Complex.ofReal_re]
  have hκim : κ.im = 0 := by rw [hκ]; simp
  have hfz : ∀ w : ℂ, ‖w‖ ≤ R → ‖G w‖ ≤ B := by
    intro w hw
    have hwre := abs_le.mp ((Complex.abs_re_le_norm w).trans hw)
    have hwim := abs_le.mp ((Complex.abs_im_le_norm w).trans hw)
    rw [hR] at hwre hwim
    have hκwre : (κ * w).re = 1.9 * w.re := by
      rw [Complex.mul_re, hκre, hκim]; ring
    have hκwim : (κ * w).im = 1.9 * w.im := by
      rw [Complex.mul_im, hκre, hκim]; ring
    have hzeta : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
        ‖riemannZeta (2 + κ * w + ε * T * I)‖ ≤ C * (T + 5) ^ A' := by
      intro ε hε
      set s : ℂ := 2 + κ * w + ε * T * I with hs
      have hsre : s.re = 2 + 1.9 * w.re := by
        rw [hs]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.mul_im, hκre, hκim]
        ring
      have hsim : s.im = 1.9 * w.im + ε * T := by
        rw [hs]
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.im_ofNat, Complex.mul_re, hκre, hκim]
        ring
      have hεT : T - 1.71 ≤ |1.9 * w.im + ε * T| := by
        rcases hε with rfl | rfl
        · rw [abs_of_pos (by nlinarith)]; nlinarith
        · rw [abs_of_neg (by nlinarith)]; nlinarith
      have h1 : (0.15:ℝ) ≤ s.re := by rw [hsre]; nlinarith
      have h2 : 1 ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        have : |(s - 1).im| ≤ ‖s - 1‖ := this
        have him : (s - 1).im = s.im := by simp
        rw [him, hsim] at this
        linarith [hεT.trans this]
      have h3 := hgrowth s h1 h2
      have hbase1 : (1:ℝ) ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
      have hA'A : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' :=
        Real.rpow_le_rpow_of_exponent_le hbase1 (le_max_left _ _)
      have hbase : |s.im| + 3 ≤ T + 5 := by
        rw [hsim]
        have h4 := abs_add_le (1.9 * w.im) (ε * T)
        have h5 : |1.9 * w.im| ≤ 1.71 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]
          have : |w.im| ≤ 0.9 := abs_le.mpr ⟨hwim.1, hwim.2⟩
          nlinarith
        have h6 : |ε * T| = T := by
          rcases hε with rfl | rfl <;> rw [abs_mul] <;>
            simp [abs_of_pos (by linarith : (0:ℝ) < T)]
        linarith
      have hmono : (|s.im| + 3) ^ A' ≤ (T + 5) ^ A' :=
        Real.rpow_le_rpow (by positivity) hbase hA'0
      calc ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A := h3
        _ ≤ C * (T + 5) ^ A' := by
            exact mul_le_mul_of_nonneg_left (hA'A.trans hmono) hC.le
    have hgb : ‖symZeta T (2 + κ * w)‖ ≤ C * (T + 5) ^ A' := by
      have e1 : (2:ℂ) + κ * w + (1:ℝ) * T * I = 2 + κ * w + T * I := by push_cast; ring
      have e2 : (2:ℂ) + κ * w + (-1:ℝ) * T * I = 2 + κ * w - T * I := by push_cast; ring
      have ha := hzeta 1 (Or.inl rfl)
      have hb := hzeta (-1) (Or.inr rfl)
      rw [e1] at ha
      rw [e2] at hb
      unfold symZeta
      calc ‖(riemannZeta (2 + κ * w + T * I) + riemannZeta (2 + κ * w - T * I)) / 2‖
          = ‖riemannZeta (2 + κ * w + T * I) + riemannZeta (2 + κ * w - T * I)‖ / 2 := by
            rw [norm_div]; norm_num
        _ ≤ (‖riemannZeta (2 + κ * w + T * I)‖ + ‖riemannZeta (2 + κ * w - T * I)‖) / 2 := by
            gcongr
            exact norm_add_le _ _
        _ ≤ C * (T + 5) ^ A' := by linarith
    calc ‖G w‖ = ‖symZeta T (2 + κ * w)‖ * ‖u‖ := by rw [hG]; exact norm_mul _ _
      _ ≤ (C * (T + 5) ^ A') * 3 := by
          apply mul_le_mul hgb hnu (norm_nonneg _) (by positivity)
      _ ≤ B := by
          rw [hB]
          nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ T + 5) A']
  
  have hfAnalytic : AnalyticOnNhd ℂ G (Metric.closedBall (0:ℂ) 1) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact hGanalytic w (hw.trans (by norm_num))
  have hrlt1 : r < 1 := by norm_num [hr]
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) hrlt1
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hG0 hfin hfz
  set Z : Finset ℂ := (finiteSetOfZeros_mono hrlt1 hfin).toFinset with hZdef
  have horder : ∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt G ρ := by
    intro ρ hρ
    rw [hZdef, Set.Finite.mem_toFinset] at hρ
    obtain ⟨hρr, hρ0⟩ := hρ
    have hρr' : ‖ρ‖ ≤ r := hρr
    have han : AnalyticAt ℂ G ρ := hGanalytic ρ (by rw [hr] at hρr'; linarith)
    have hne0 : analyticOrderAt G ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr hρ0
    have hnetop : analyticOrderAt G ρ ≠ ⊤ := by
      refine hball.analyticOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected
        (x := 0) ?_ ?_ ?_
      · rw [Metric.mem_ball, dist_zero_right]; simp; norm_num
      · rw [Metric.mem_ball, dist_zero_right]; rw [hr] at hρr'; linarith
      · rw [(hGanalytic 0 (by norm_num)).analyticOrderAt_eq_zero.mpr
          (by rw [hG0]; exact one_ne_zero)]
        exact ENat.zero_ne_top
    unfold analyticOrderNatAt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hn] at hne0 ⊢
    simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
    omega
  
  set φ : ℝ → ℂ := fun σ => ((σ - 2 : ℝ) : ℂ) / κ with hφ
  have hφinj : Set.InjOn φ (reZeroSet T) := by
    intro a _ b _ h
    simp only [hφ] at h
    have h' : ((a - 2 : ℝ) : ℂ) = ((b - 2 : ℝ) : ℂ) := by
      have := congrArg (fun z => z * κ) h
      simpa [div_mul_cancel₀ _ hκ0] using this
    have := Complex.ofReal_inj.mp h'
    linarith
  have hmem : ∀ σ ∈ reZeroSet T, φ σ ∈ SetOfZeros r G := by
    rintro σ ⟨hσI, hσ0⟩
    have hσ1 : (1/2:ℝ) ≤ σ := hσI.1
    have hσ2 : σ ≤ 2 := hσI.2
    constructor
    · show ‖((σ - 2 : ℝ) : ℂ) / κ‖ ≤ r
      rw [norm_div, hnormκ, Complex.norm_real, Real.norm_eq_abs, hr]
      rw [abs_of_nonpos (by linarith)]
      rw [div_le_iff₀ (by norm_num)]
      linarith
    · show G (φ σ) = 0
      have hfix : (2:ℂ) + κ * φ σ = (σ:ℂ) := by
        simp only [hφ]
        field_simp
        push_cast
        ring
      have hne1 : (σ:ℂ) + T * I ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      simp only [hG, hfix]
      rw [symZeta_ofReal σ hne1, hσ0]
      simp
  have himg : φ '' (reZeroSet T) ⊆ (↑Z : Set ℂ) := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hZdef]
    simp only [Set.Finite.coe_toFinset]
    exact hmem σ hσ
  have hfinRe : (reZeroSet T).Finite :=
    Set.Finite.of_finite_image (Z.finite_toSet.subset himg) hφinj
  refine ⟨hfinRe, ?_⟩
  have hcard : ((reZeroSet T).ncard : ℝ) ≤ (Z.card : ℝ) := by
    have h1 : (reZeroSet T).ncard = (φ '' reZeroSet T).ncard :=
      (hφinj.ncard_image).symm
    have h2 : (φ '' reZeroSet T).ncard ≤ (↑Z : Set ℂ).ncard :=
      Set.ncard_le_ncard himg Z.finite_toSet
    rw [Set.ncard_coe_finset] at h2
    exact_mod_cast h1 ▸ h2
  have hsum : (Z.card : ℝ) ≤ ((∑ ρ ∈ Z, analyticOrderNatAt G ρ : ℕ) : ℝ) := by
    have h := (Finset.card_eq_sum_ones Z).le.trans (Finset.sum_le_sum horder)
    exact_mod_cast h
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlog5 : Real.log (T + 5) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith : (0:ℝ) < T), Real.rpow_two]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlogB : Real.log B ≤ (|Real.log (6 * C)| + 2 * A') * Real.log T := by
    rw [hB, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by linarith : (0:ℝ) < T + 5)]
    have h1 := le_abs_self (Real.log (6 * C))
    have h2 : |Real.log (6 * C)| ≤ |Real.log (6 * C)| * Real.log T :=
      le_mul_of_one_le_right (abs_nonneg _) hlogT
    have h3 : A' * Real.log (T + 5) ≤ A' * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlog5 hA'0
    linarith
  calc ((reZeroSet T).ncard : ℝ) ≤ (Z.card : ℝ) := hcard
    _ ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (6 * C)| + 2 * A') * Real.log T) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem reZeroSet_card_le : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T := by
  obtain ⟨A, C, hC, hgrowth⟩ := zeta_growth_right
  exact ⟨_, 4, reZeroSet_card_le_of_growth hC hgrowth⟩

end Zeta23.RvM

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.RvM.Backlund -/
section
open Complex Set MeasureTheory Real intervalIntegral

noncomputable section

namespace Zeta23

namespace RvM

section Variation

variable {T : ℝ}

set_option maxHeartbeats 1600000 in
lemma ofReal_add_mul_I_ne_one (hT : T ≠ 0) (σ : ℝ) : (σ : ℂ) + T * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hT this

set_option maxHeartbeats 1600000 in
lemma hasDerivAt_riemannZeta_horizontal (hT : T ≠ 0) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => riemannZeta (σ + T * I)) (deriv riemannZeta (σ + T * I)) σ := by
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (σ + T * I)) (σ + T * I) :=
    (differentiableAt_riemannZeta (ofReal_add_mul_I_ne_one hT σ)).hasDerivAt
  have hγ : HasDerivAt (fun σ : ℝ => (σ : ℂ) + T * I) 1 σ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 σ := Complex.ofRealCLM.hasDerivAt
    simpa using h1.add_const ((T : ℂ) * I)
  exact (hζ.comp σ hγ).congr_deriv (mul_one _)

set_option maxHeartbeats 1600000 in
lemma continuous_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => riemannZeta (σ + T * I)) :=
  continuous_iff_continuousAt.mpr fun σ => (hasDerivAt_riemannZeta_horizontal hT σ).continuousAt

set_option maxHeartbeats 1600000 in
lemma continuous_deriv_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => deriv riemannZeta (σ + T * I)) := by
  have hγ : Continuous (fun σ : ℝ => (σ : ℂ) + T * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  exact hA.deriv.continuousOn.comp_continuous hγ (fun σ => ofReal_add_mul_I_ne_one hT σ)

set_option maxHeartbeats 1600000 in
lemma continuousOn_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) :
    ContinuousOn (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) (Set.Icc (1/2 : ℝ) 2) := by
  have h : ContinuousOn (fun σ : ℝ => deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I))
      (Set.Icc (1/2 : ℝ) 2) :=
    (continuous_deriv_riemannZeta_horizontal hT).continuousOn.div
      (continuous_riemannZeta_horizontal hT).continuousOn hnz
  exact h.congr (fun σ _ => by rw [logDeriv_apply])

set_option maxHeartbeats 1600000 in
lemma intervalIntegrable_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : u ∈ Set.Icc (1/2 : ℝ) 2) (hv : v ∈ Set.Icc (1/2 : ℝ) 2) :
    IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) volume u v :=
  ((continuousOn_logDeriv_horizontal hT hnz).mono
    (Set.uIcc_subset_Icc hu hv)).intervalIntegrable

set_option maxHeartbeats 1600000 in
lemma im_integral_le_two_pi (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : 1/2 ≤ u) (huv : u < v) (hv : v ≤ 2)
    (hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0) :
    |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im| ≤ 2 * Real.pi := by
  set w : ℝ → ℂ := fun σ => riemannZeta (σ + T * I) with hwdef
  have hwc : Continuous w := continuous_riemannZeta_horizontal hT
  have huI : u ∈ Set.Icc (1/2 : ℝ) 2 := ⟨hu, by linarith⟩
  have hvI : v ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, hv⟩
  have hsub : Set.Icc u v ⊆ Set.Icc (1/2 : ℝ) 2 := Set.Icc_subset_Icc hu hv
  
  set m : ℝ := (u + v) / 2 with hmdef
  have hm : m ∈ Set.Ioo u v := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  set ε : ℝ := if 0 < (w m).re then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by by_cases h : 0 < (w m).re <;> simp [hεdef, h]
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hεm : 0 < ε * (w m).re := by
    by_cases h : 0 < (w m).re
    · simp [hεdef, h]
    · have h' : (w m).re < 0 := lt_of_le_of_ne (not_lt.mp h) (hno m hm)
      simp only [hεdef, if_neg h]; linarith
  
  set g : ℝ → ℝ := fun x => ε * (w x).re with hgdef
  have hg : Continuous g := continuous_const.mul (Complex.continuous_re.comp hwc)
  have hpos : ∀ σ ∈ Set.Ioo u v, 0 < g σ := by
    intro σ hσ
    by_contra hneg
    have hσne : g σ ≠ 0 := mul_ne_zero hε0 (hno σ hσ)
    have hσneg : g σ < 0 := lt_of_le_of_ne (not_lt.mp hneg) hσne
    have hIcc : Set.uIcc σ m ⊆ Set.Ioo u v := Set.ordConnected_Ioo.uIcc_subset hσ hm
    have h0 : (0 : ℝ) ∈ Set.uIcc (g σ) (g m) :=
      Set.mem_uIcc.mpr (Or.inl ⟨hσneg.le, hεm.le⟩)
    obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hg.continuousOn h0
    exact mul_ne_zero hε0 (hno x (hIcc hx)) hx0
  
  have hnonneg : ∀ σ ∈ Set.Icc u v, 0 ≤ g σ := by
    have hcl : IsClosed {x | 0 ≤ g x} := isClosed_le continuous_const hg
    have : Set.Icc u v ⊆ {x | 0 ≤ g x} := by
      rw [← closure_Ioo huv.ne]
      exact hcl.closure_subset_iff.mpr (fun x hx => (hpos x hx).le)
    exact fun σ hσ => this hσ
  
  have hslit : ∀ σ ∈ Set.Icc u v, (ε : ℂ) * w σ ∈ Complex.slitPlane := by
    intro σ hσ
    rw [Complex.mem_slitPlane_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    rcases (hnonneg σ hσ).lt_or_eq with h | h
    · exact Or.inl h
    · right
      intro him
      have hre : (w σ).re = 0 := by
        rcases mul_eq_zero.mp h.symm with h1 | h1
        · exact absurd h1 hε0
        · exact h1
      have him' : (w σ).im = 0 := by
        rcases mul_eq_zero.mp him with h1 | h1
        · exact absurd h1 hε0
        · exact h1
      exact hnz σ (hsub hσ) (Complex.ext hre him')
  
  have hderiv : ∀ σ ∈ Set.uIcc u v, HasDerivAt (fun x : ℝ => Complex.log ((ε : ℂ) * w x))
      (logDeriv riemannZeta (σ + T * I)) σ := by
    intro σ hσ
    rw [Set.uIcc_of_le huv.le] at hσ
    have hwσ : w σ ≠ 0 := hnz σ (hsub hσ)
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0
    have h1 := (hasDerivAt_riemannZeta_horizontal hT σ).const_mul (ε : ℂ)
    have h2 := (Complex.hasDerivAt_log (hslit σ hσ)).comp σ h1
    have e : ((ε : ℂ) * w σ)⁻¹ * ((ε : ℂ) * deriv riemannZeta (σ + T * I))
        = logDeriv riemannZeta (σ + T * I) := by
      rw [logDeriv_apply, show riemannZeta ((σ : ℂ) + T * I) = w σ from rfl]
      field_simp
    rw [e] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_logDeriv_horizontal hT hnz huI hvI),
    Complex.sub_im, Complex.log_im, Complex.log_im]
  calc |((ε : ℂ) * w v).arg - ((ε : ℂ) * w u).arg|
      ≤ |((ε : ℂ) * w v).arg| + |((ε : ℂ) * w u).arg| := abs_sub _ _
    _ ≤ Real.pi + Real.pi := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
    _ = 2 * Real.pi := by ring

set_option maxHeartbeats 1600000 in
lemma im_integral_logDeriv_le_aux (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    (P : Finset ℝ) (hP : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ P) :
    ∀ n : ℕ, ∀ u v : ℝ, 1/2 ≤ u → u < v → v ≤ 2 →
      (P.filter (fun x => u < x ∧ x < v)).card ≤ n →
      |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ 2 * Real.pi * ((P.filter (fun x => u < x ∧ x < v)).card + 1) := by
  
  have base : ∀ u v : ℝ, 1/2 ≤ u → u < v → v ≤ 2 →
      (P.filter (fun x => u < x ∧ x < v)).card = 0 →
      |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ 2 * Real.pi * ((P.filter (fun x => u < x ∧ x < v)).card + 1) := by
    intro u v hu huv hv hc
    have hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0 := by
      intro σ hσ hre
      have hσP : σ ∈ P.filter (fun x => u < x ∧ x < v) :=
        Finset.mem_filter.mpr ⟨hP σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ hre, hσ.1, hσ.2⟩
      rw [Finset.card_eq_zero] at hc
      simp [hc] at hσP
    rw [hc]
    have := im_integral_le_two_pi hT hnz hu huv hv hno
    simpa using this
  intro n
  induction n with
  | zero =>
    intro u v hu huv hv hc
    exact base u v hu huv hv (Nat.le_zero.mp hc)
  | succ n ih =>
    intro u v hu huv hv hc
    by_cases hc0 : (P.filter (fun x => u < x ∧ x < v)).card = 0
    · exact base u v hu huv hv hc0
    obtain ⟨m, hm⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
    obtain ⟨-, hum, hmv⟩ := Finset.mem_filter.mp hm
    
    set S := P.filter (fun x => u < x ∧ x < v) with hSdef
    set S₁ := P.filter (fun x => u < x ∧ x < m) with hS₁def
    set S₂ := P.filter (fun x => m < x ∧ x < v) with hS₂def
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have := (Finset.mem_filter.mp hx1).2.2
      have := (Finset.mem_filter.mp hx2).2.1
      linarith
    have hsubS : S₁ ∪ S₂ ⊆ S.erase m := by
      intro x hx
      rw [Finset.mem_erase]
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxP, hux, hxm⟩ := Finset.mem_filter.mp hx
        exact ⟨hxm.ne, Finset.mem_filter.mpr ⟨hxP, hux, by linarith⟩⟩
      · obtain ⟨hxP, hmx, hxv⟩ := Finset.mem_filter.mp hx
        exact ⟨hmx.ne', Finset.mem_filter.mpr ⟨hxP, by linarith, hxv⟩⟩
    have hcard : S₁.card + S₂.card + 1 ≤ S.card := by
      have h1 : S₁.card + S₂.card = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
      have h2 : (S₁ ∪ S₂).card ≤ (S.erase m).card := Finset.card_le_card hsubS
      have h3 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hm
      have h4 : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hm⟩
      omega
    have hc1 : S₁.card ≤ n := by omega
    have hc2 : S₂.card ≤ n := by omega
    have e1 := ih u m hu hum (by linarith) hc1
    have e2 := ih m v (by linarith) hmv hv hc2
    
    have hmI : m ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, by linarith⟩
    have huI : u ∈ Set.Icc (1/2 : ℝ) 2 := ⟨hu, by linarith⟩
    have hvI : v ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, hv⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_logDeriv_horizontal hT hnz huI hmI)
      (intervalIntegrable_logDeriv_horizontal hT hnz hmI hvI), Complex.add_im]
    have hcast : ((S₁.card : ℝ) + 1) + ((S₂.card : ℝ) + 1) ≤ (S.card : ℝ) + 1 := by
      have : ((S₁.card + S₂.card + 1 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
      push_cast at this; linarith
    calc |(∫ σ in u..m, logDeriv riemannZeta (σ + T * I)).im
          + (∫ σ in m..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ |(∫ σ in u..m, logDeriv riemannZeta (σ + T * I)).im|
          + |(∫ σ in m..v, logDeriv riemannZeta (σ + T * I)).im| := abs_add_le _ _
      _ ≤ 2 * Real.pi * ((S₁.card : ℝ) + 1) + 2 * Real.pi * ((S₂.card : ℝ) + 1) := add_le_add e1 e2
      _ ≤ 2 * Real.pi * ((S.card : ℝ) + 1) := by nlinarith [Real.pi_pos]

set_option maxHeartbeats 1600000 in
theorem im_integral_logDeriv_le (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    (hfin : (reZeroSet T).Finite) :
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im|
      ≤ 2 * Real.pi * ((reZeroSet T).ncard + 1) := by
  set P := hfin.toFinset with hPdef
  have hP : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ P :=
    fun σ hσ h => hfin.mem_toFinset.mpr ⟨hσ, h⟩
  have h := im_integral_logDeriv_le_aux hT hnz P hP P.card (1/2) 2 le_rfl (by norm_num) le_rfl
    (Finset.card_filter_le _ _)
  have hc : ((P.filter (fun x => (1/2 : ℝ) < x ∧ x < 2)).card : ℝ) ≤ (reZeroSet T).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast Finset.card_filter_le _ _
  refine h.trans ?_
  nlinarith [Real.pi_pos]

end Variation

set_option maxHeartbeats 1600000 in
lemma riemannZeta_ne_zero_on_segment {T : ℝ} (hord : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) :
    ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0 := by
  intro σ hσ hz
  rcases lt_or_ge σ 1 with h | h
  · refine hord (σ + T * I) ⟨hz, ?_, ?_⟩ (by simp)
    · simp; linarith [hσ.1]
    · simpa using h
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h) hz

set_option maxHeartbeats 1600000 in
theorem backlund_horizontal_of_count_at {C T₀ : ℝ}
    (hJ : ∀ T : ℝ, T₀ ≤ T →
      (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T) :
    ∀ T : ℝ, max T₀ 3 ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im|
      ≤ 2 * Real.pi * (C + 1) * Real.log T := by
  intro T hT hord
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hT3 : (3 : ℝ) ≤ T := (le_max_right _ _).trans hT
  have hTne : T ≠ 0 := by linarith
  obtain ⟨hfin, hcount⟩ := hJ T hT₀
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)])
  have h := im_integral_logDeriv_le hTne (riemannZeta_ne_zero_on_segment hord) hfin
  refine h.trans ?_
  have hπ := Real.pi_pos
  nlinarith [hcount, hlog, mul_nonneg hπ.le (sub_nonneg.mpr hlog)]

set_option maxHeartbeats 1600000 in
theorem backlund_horizontal_of_count
    (hJ : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T := by
  obtain ⟨C, T₀, hJ⟩ := hJ
  exact ⟨_, _, backlund_horizontal_of_count_at hJ⟩

set_option maxHeartbeats 1600000 in
theorem backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T :=
  backlund_horizontal_of_count reZeroSet_card_le

set_option maxHeartbeats 1600000 in
lemma re_riemannZeta_two_pos (t : ℝ) : 0 < (riemannZeta (2 + t * I)).re := by
  have h := norm_riemannZeta_sub_one_le (s := 2 + t * I) (by simp)
  have h2 : |(riemannZeta (2 + t * I) - 1).re| ≤ ‖riemannZeta (2 + t * I) - 1‖ :=
    Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at h2
  have h3 := (abs_le.mp (h2.trans h)).1
  linarith [pi_sq_div_six_sub_one_lt_one]

set_option maxHeartbeats 1600000 in
lemma two_add_mul_I_ne_one (t : ℝ) : (2 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this

set_option maxHeartbeats 1600000 in
lemma hasDerivAt_log_riemannZeta_two (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.log (riemannZeta (2 + t * I)))
      (logDeriv riemannZeta (2 + t * I) * I) t := by
  have hs := two_add_mul_I_ne_one t
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (2 + t * I)) (2 + t * I) :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  have hγ : HasDerivAt (fun t : ℝ => (2 : ℂ) + t * I) I t := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa using (h1.mul_const I).const_add (2 : ℂ)
  have hcomp : HasDerivAt (fun t : ℝ => riemannZeta (2 + t * I)) (deriv riemannZeta (2 + t * I) * I) t :=
    hζ.comp t hγ
  have hlog : HasDerivAt Complex.log (riemannZeta (2 + t * I))⁻¹ (riemannZeta (2 + t * I)) :=
    Complex.hasDerivAt_log (Or.inl (re_riemannZeta_two_pos t))
  have h := hlog.comp t hcomp
  have e : (riemannZeta (2 + t * I))⁻¹ * (deriv riemannZeta (2 + t * I) * I)
      = logDeriv riemannZeta (2 + t * I) * I := by
    rw [logDeriv_apply]; ring
  rw [e] at h
  exact h

set_option maxHeartbeats 1600000 in
lemma continuous_logDeriv_riemannZeta_two :
    Continuous (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I) := by
  have hγ : Continuous (fun t : ℝ => (2 : ℂ) + t * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  have hd : Continuous (fun t : ℝ => deriv riemannZeta (2 + t * I)) :=
    hA.deriv.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hz : Continuous (fun t : ℝ => riemannZeta (2 + t * I)) :=
    hA.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hne : ∀ t : ℝ, riemannZeta (2 + t * I) ≠ 0 := fun t h => by
    have := re_riemannZeta_two_pos t; rw [h] at this; simp at this
  simp only [logDeriv_apply]
  exact ((hd.div hz hne).mul continuous_const)

set_option maxHeartbeats 1600000 in
theorem vertical_two : ∀ T₁ T₂ : ℝ,
    |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi := by
  intro T₁ T₂
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_log_riemannZeta_two t)
    (continuous_logDeriv_riemannZeta_two.intervalIntegrable _ _)]
  rw [Complex.sub_im, Complex.log_im, Complex.log_im]
  have h1 : |(riemannZeta (2 + T₂ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₂).le
  have h2 : |(riemannZeta (2 + T₁ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₁).le
  calc |(riemannZeta (2 + T₂ * I)).arg - (riemannZeta (2 + T₁ * I)).arg|
      ≤ |(riemannZeta (2 + T₂ * I)).arg| + |(riemannZeta (2 + T₁ * I)).arg| := abs_sub _ _
    _ ≤ π / 2 + π / 2 := add_le_add h1 h2
    _ = π := by ring

end RvM

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.RvM.CountByIntegral -/
section
open Complex Set Topology Filter Real

noncomputable section

namespace Zeta23

namespace RvM

set_option maxHeartbeats 1600000 in
lemma analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ completedRiemannZeta (({0, 1} : Set ℂ)ᶜ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds (by simp [h0, h1]))

set_option maxHeartbeats 1600000 in
lemma completedRiemannZeta_eq_Gammaℝ_mul {s : ℂ} (hs : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

set_option maxHeartbeats 1600000 in
lemma completedRiemannZeta_eq_zero_iff_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [completedRiemannZeta_eq_Gammaℝ_mul h0 hG, mul_eq_zero]
  simp [hG]

set_option maxHeartbeats 1600000 in
lemma completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  rw [Ne, completedRiemannZeta_eq_zero_iff_of_re_pos (by linarith)]
  exact riemannZeta_ne_zero_of_one_le_re hs

set_option maxHeartbeats 1600000 in
lemma completedRiemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  exact completedRiemannZeta_ne_zero_of_one_le_re (by simp; linarith)

set_option maxHeartbeats 1600000 in
lemma completedRiemannZeta_eq_zero_iff {s : ℂ} :
    completedRiemannZeta s = 0 ↔ IsNontrivialZero s := by
  constructor
  · intro h
    have h1 : 0 < s.re := by
      by_contra hle
      exact completedRiemannZeta_ne_zero_of_re_nonpos (not_lt.mp hle) h
    have h2 : s.re < 1 := by
      by_contra hle
      exact completedRiemannZeta_ne_zero_of_one_le_re (not_lt.mp hle) h
    exact ⟨(completedRiemannZeta_eq_zero_iff_of_re_pos h1).mp h, h1, h2⟩
  · rintro ⟨hz, h1, _⟩
    exact (completedRiemannZeta_eq_zero_iff_of_re_pos h1).mpr hz

set_option maxHeartbeats 1600000 in
lemma analyticOrderNatAt_completedRiemannZeta {ρ : ℂ} (h : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderNatAt completedRiemannZeta ρ = zeroMult ρ := by
  have h0 : ρ ≠ 0 := fun h' => by simp [h'] at h
  have hev : riemannZeta =ᶠ[𝓝 ρ] (completedRiemannZeta * fun s => (Gammaℝ s)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
    rw [Pi.mul_apply, riemannZeta_def_of_ne_zero hs, div_eq_mul_inv]
  have hΛ := analyticAt_completedRiemannZeta h0 h1
  have hGinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
  have hG0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 :=
    hGinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h))
  unfold zeroMult analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hΛ hGinv, hG0, add_zero]

set_option maxHeartbeats 1600000 in
theorem rectangleIntegral'_logDeriv_completedZeta_eq_Ncount {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    (hT : T₁ ≤ T₂) (hgood₁ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T₂) :
    RectangleIntegral' (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = (Ncount T₁ T₂ : ℂ) := by
  classical
  set z : ℂ := -1 + T₁ * I with hzdef
  set w : ℂ := 2 + T₂ * I with hwdef
  have hzre : z.re = -1 := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = 2 := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; norm_num
  have him : z.im ≤ w.im := by rw [hzim, hwim]; exact hT
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (-1 ≤ s.re ∧ s.re ≤ 2) ∧ (T₁ ≤ s.im ∧ s.im ≤ T₂) := by
    intro s
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim,
      uIcc_of_le (show (-1 : ℝ) ≤ 2 by norm_num), uIcc_of_le hT, mem_Icc]
  have hf : AnalyticOnNhd ℂ completedRiemannZeta (Rectangle z w) := by
    intro s hs
    have hi : 0 < s.im := by linarith [((hmem s).mp hs).2.1]
    exact analyticAt_completedRiemannZeta (fun h => by simp [h] at hi) (fun h => by simp [h] at hi)
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Rectangle z w) := fun _ _ => analyticAt_const
  have hfin := zetaSeam.finite_window T₁ T₂
  have hZ : ∀ s ∈ Rectangle z w, completedRiemannZeta s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hs
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hs
    rw [completedRiemannZeta_eq_zero_iff]
    constructor
    · intro hnz
      exact ⟨hnz, lt_of_le_of_ne hi1 (fun h' => hgood₁ s hnz h'.symm), hi2⟩
    · rintro ⟨hnz, _⟩
      exact hnz
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨_, h1, h2⟩, hi1, hi2⟩ := hs
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w, completedRiemannZeta s ≠ 0 := by
    intro s hs h0
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp (rectangleBorder_subset_rectangle z w hs)
    have hnz := completedRiemannZeta_eq_zero_iff.mp h0
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, hzre, hzim, hwre,
      hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood₁ s hnz h'
    · linarith [hnz.2.1]
    · exact hgood₂ s hnz h'
    · linarith [hnz.2.2]
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder
    hfin.toFinset hZ hZsub
  simp only [one_mul, mul_one] at key
  rw [show (fun s => logDeriv completedRiemannZeta s) = logDeriv completedRiemannZeta from rfl]
    at key
  rw [key]
  unfold Ncount
  have hset : zerosIn T₁ T₂ = {ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
    ext ρ; simp [zerosIn]
  rw [hset, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [Set.Finite.mem_toFinset] at hρ
  obtain ⟨⟨_, h1, h2⟩, _⟩ := hρ
  rw [analyticOrderNatAt_completedRiemannZeta h1 (fun h' => by simp [h'] at h2)]

end RvM

end Zeta23

end
end

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaConj.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
/- Module Zeta23.FromPNTPlus.ZetaConj -/
section
open scoped Complex ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s

theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.RvM.Fold -/
section
open Complex MeasureTheory Set intervalIntegral

noncomputable section

namespace Zeta23.RvM

section ConjSymmetry

set_option maxHeartbeats 1600000 in
lemma cpow_ofReal_conj {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ (starRingEnd ℂ w) = starRingEnd ℂ ((x : ℂ) ^ w) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hx0, ← Complex.exp_conj, map_mul,
    ← Complex.ofReal_log hx.le, Complex.conj_ofReal]

set_option maxHeartbeats 1600000 in
lemma Gammaℝ_conj (s : ℂ) : Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Complex.Gammaℝ s) := by
  have h1 : -(starRingEnd ℂ s) / 2 = starRingEnd ℂ (-s / 2) := by
    simp [map_div₀, map_neg, map_ofNat]
  have h2 : starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) := by
    simp [map_div₀, map_ofNat]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, h1, h2, cpow_ofReal_conj Real.pi_pos,
    Complex.Gamma_conj, map_mul]

set_option maxHeartbeats 1600000 in
lemma deriv_Gammaℝ_conj (s : ℂ) :
    deriv Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (deriv Complex.Gammaℝ s) := by
  have h : ∀ z : ℂ, starRingEnd ℂ (Complex.Gammaℝ (starRingEnd ℂ z)) = Complex.Gammaℝ z := by
    intro z
    rw [Gammaℝ_conj, Complex.conj_conj]
  simp [← deriv_conj_conj' Complex.Gammaℝ, h]

set_option maxHeartbeats 1600000 in
lemma logDeriv_Gammaℝ_conj (s : ℂ) :
    logDeriv Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv Complex.Gammaℝ s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_Gammaℝ_conj, Gammaℝ_conj, ← map_div₀]

set_option maxHeartbeats 1600000 in
lemma logDeriv_completedZeta_conj {s : ℂ} (hre : 0 < s.re) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (starRingEnd ℂ s)
      = starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hcre : 0 < (starRingEnd ℂ s).re := by rwa [Complex.conj_re]
  have hc0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
  have hc1 : starRingEnd ℂ s ≠ 1 := fun h => hs1 (by rw [← Complex.conj_conj s, h, map_one])
  have hζc : riemannZeta (starRingEnd ℂ s) ≠ 0 := by
    rw [_root_.riemannZeta_conj]
    exact (map_ne_zero _).mpr hζs
  rw [Zeta23.WeilEF.logDeriv_completedZeta _ hc1 hζc hcre,
    Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζs hre, map_add, logDeriv_Gammaℝ_conj,
    logDerivZeta_conj']

set_option maxHeartbeats 1600000 in
lemma logDeriv_completedZeta_one_sub_conj {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (1 - starRingEnd ℂ s)
      = -starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hre
  have hc0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
  have hc1 : starRingEnd ℂ s ≠ 1 := fun h => hs1 (by rw [← Complex.conj_conj s, h, map_one])
  rw [Zeta23.WeilEF.logDeriv_completedZeta_one_sub _ hc0 hc1,
    logDeriv_completedZeta_conj hre hs0 hs1 hζs]

end ConjSymmetry

set_option maxHeartbeats 1600000 in
lemma path_point_facts {s : ℂ} (hre : 0 < s.re) (him : 1 ≤ s.im)
    (hgood : GoodHeight s.im) : s ≠ 1 ∧ riemannZeta s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro hh; rw [hh] at him; simp at him; linarith
  refine ⟨hs1, fun hz => ?_⟩
  rcases lt_or_ge s.re 1 with hlt | hge
  · exact hgood s ⟨hz, hre, hlt⟩ rfl
  · exact riemannZeta_ne_zero_of_one_le_re hge hz

set_option maxHeartbeats 1600000 in
lemma continuousAt_logDeriv_completedZeta {s : ℂ} (him : 1 ≤ s.im) (hgood : GoodHeight s.im) :
    ContinuousAt (logDeriv completedRiemannZeta) s := by
  have hs0 : s ≠ 0 := by intro hh; rw [hh] at him; simp at him; linarith
  have hs1 : s ≠ 1 := by intro hh; rw [hh] at him; simp at him; linarith
  have hΛ := analyticAt_completedRiemannZeta hs0 hs1
  have hne : completedRiemannZeta s ≠ 0 := fun h =>
    hgood s (completedRiemannZeta_eq_zero_iff.mp h) rfl
  exact hΛ.deriv.continuousAt.div hΛ.continuousAt hne

set_option maxHeartbeats 1600000 in
lemma horizontal_fold {T : ℝ} (hT : 1 ≤ T) (hgood : GoodHeight T) :
    ∫ σ in (-1 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)
      = 2 * I * ((∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)).im : ℂ) := by
  set F := logDeriv completedRiemannZeta with hF
  have hcont : Continuous fun σ : ℝ => F (σ + T * I) := by
    refine continuous_iff_continuousAt.mpr fun σ => ?_
    have h := continuousAt_logDeriv_completedZeta (s := σ + T * I) (by simpa using hT)
      (by simpa using hgood)
    exact ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) h (by fun_prop)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-1) (1 / 2))
    (hcont.intervalIntegrable (μ := volume) (1 / 2) 2)
  rw [← hsplit]
  set A := ∫ σ in (1 / 2 : ℝ)..2, F (σ + T * I) with hA
  
  have hleft : ∫ σ in (-1 : ℝ)..(1 / 2), F (σ + T * I) = -starRingEnd ℂ A := by
    have hsub := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => F (x + T * I))
      (a := (1 / 2 : ℝ)) (b := 2) (1 : ℝ)
    norm_num at hsub
    
    rw [← hsub, hA, ← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hxpos : 0 < x := by linarith [hx.1]
    obtain ⟨hs1, hζ⟩ := path_point_facts (s := x + T * I) (by simpa using hxpos)
      (by simpa using hT) (by simpa using hgood)
    have key := logDeriv_completedZeta_one_sub_conj (s := x + T * I) (by simpa using hxpos) hs1 hζ
    have e : (1 : ℂ) - starRingEnd ℂ (x + T * I) = 1 - (x : ℂ) + T * I := by
      simp [Complex.ext_iff]
    simp only [hF] at key ⊢
    rw [← e, key]
  rw [hleft, neg_add_eq_sub, Complex.sub_conj]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
lemma vertical_fold {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, logDeriv completedRiemannZeta (-1 + t * I)
      = -starRingEnd ℂ (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) := by
  rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le h12] at ht
  have ht1 : 1 ≤ t := le_trans h1 ht.1
  have hs1 : (2 : ℂ) + t * I ≠ 1 := by
    intro hh; have := congrArg Complex.re hh; simp at this
  have hζ : riemannZeta (2 + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have key := logDeriv_completedZeta_one_sub_conj (s := 2 + t * I) (by simp) hs1 hζ
  have e : (1 : ℂ) - starRingEnd ℂ (2 + t * I) = -1 + t * I := by
    simp [Complex.ext_iff]; norm_num
  show logDeriv completedRiemannZeta (-1 + t * I)
    = -starRingEnd ℂ (logDeriv completedRiemannZeta (2 + t * I))
  rw [← e, key]

set_option maxHeartbeats 1600000 in
theorem rectangleIntegral_logDeriv_completedZeta_eq_halfContour {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁)
    (h12 : T₁ < T₂) (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    RectangleIntegral (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = 2 * I * ((halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℂ) := by
  have hre1 : (-1 + T₁ * I).re = -1 := by simp
  have him1 : (-1 + T₁ * I).im = T₁ := by simp
  have hre2 : (2 + T₂ * I : ℂ).re = 2 := by simp
  have him2 : (2 + T₂ * I : ℂ).im = T₂ := by simp
  simp only [RectangleIntegral, HIntegral, VIntegral, hre1, him1, hre2, him2, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [horizontal_fold h1 hg1, horizontal_fold (by linarith) hg2, vertical_fold h1 h12.le]
  simp only [halfContour, Complex.add_im, Complex.sub_im, Complex.mul_I_im]
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T₁ * I)) = A₁
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T₂ * I)) = A₂
  generalize (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) = B
  have e1 : 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * B - I * -starRingEnd ℂ B
      = 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * (B + starRingEnd ℂ B) := by ring
  rw [e1, Complex.add_conj]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem Ncount_eq_im_halfContour {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ)
      = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im := by
  have h := rectangleIntegral'_logDeriv_completedZeta_eq_Ncount (by linarith) h12.le hg1 hg2
  change (1 / (2 * Real.pi * I)) • RectangleIntegral _ _ _ = _ at h
  rw [rectangleIntegral_logDeriv_completedZeta_eq_halfContour h1 h12 hg1 hg2, smul_eq_mul] at h
  have h' : ((Ncount T₁ T₂ : ℝ) : ℂ)
      = (((1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    field_simp
  exact_mod_cast h'

end Zeta23.RvM

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.RvM.NcountWindow -/
section
noncomputable section

namespace Zeta23

set_option maxHeartbeats 1600000 in
theorem zerosIn_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    zerosIn a c = zerosIn a b ∪ zerosIn b c := by
  ext ρ
  simp only [zerosIn, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hρ, ha, hb⟩
    rcases le_or_gt ρ.im b with hle | hgt
    · exact Or.inl ⟨hρ, ha, hle⟩
    · exact Or.inr ⟨hρ, hgt, hb⟩
  · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, ha, hb⟩)
    · exact ⟨hρ, ha, le_trans hb h2⟩
    · exact ⟨hρ, lt_of_le_of_lt h1 ha, hb⟩

set_option maxHeartbeats 1600000 in
theorem Ncount_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Ncount a c = Ncount a b + Ncount b c := by
  unfold Ncount
  rw [zerosIn_union h1 h2]
  refine finsum_mem_union ?_ (zerosIn_finite a b) (zerosIn_finite b c)
  rw [Set.disjoint_left]
  rintro ρ ⟨_, _, hb⟩ ⟨_, ha, _⟩
  exact absurd hb (not_le.2 ha)

set_option maxHeartbeats 1600000 in
theorem Ncount_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Ncount a b ≤ Ncount c d := by
  unfold Ncount
  have hsub : zerosIn a b ⊆ zerosIn c d := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite a b),
    finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite c d)]
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ

end Zeta23

end

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.RvM.MainTerm -/
section
open Complex MeasureTheory

noncomputable section

namespace Zeta23.RvM

set_option maxHeartbeats 1600000 in
theorem N_eq_halfContour_completedZeta {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ) = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im :=
  Ncount_eq_im_halfContour h1 h12 hg1 hg2

set_option maxHeartbeats 1600000 in
private lemma contour_point_facts {s : ℂ} (hre1 : 1/2 ≤ s.re) (_hre2 : s.re ≤ 2)
    (him : 1 ≤ s.im) (hgood : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ s.im) :
    s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 ∧ 0 < s.re := by
  have hs0 : s ≠ 0 := by
    intro hh
    rw [hh] at him
    simp only [Complex.zero_im] at him
    linarith
  have hs1 : s ≠ 1 := by
    intro hh
    rw [hh] at him
    simp only [Complex.one_im] at him
    linarith
  refine ⟨hs0, hs1, ?_, by linarith⟩
  intro hz
  rcases lt_or_ge s.re 1 with hlt | hge
  · exact hgood s ⟨hz, by linarith, hlt⟩ rfl
  · exact riemannZeta_ne_zero_of_one_le_re hge hz

set_option maxHeartbeats 1600000 in
private lemma continuousAt_logDeriv_zeta {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    ContinuousAt (logDeriv riemannZeta) s := by
  have ha := Zeta23.WeilEF.analyticAt_riemannZeta hs1
  exact (ha.deriv.continuousAt).div ha.continuousAt hζ

set_option maxHeartbeats 1600000 in
private lemma continuousAt_logDeriv_Gammaℝ {s : ℂ} (hre : 0 < s.re) :
    ContinuousAt (logDeriv Complex.Gammaℝ) s := by
  have ha := Zeta23.WeilEF.analyticAt_Gammaℝ hre
  exact (ha.deriv.continuousAt).div ha.continuousAt (Gammaℝ_ne_zero_of_re_pos hre)

set_option maxHeartbeats 1600000 in
theorem halfContour_completedZeta_split {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    halfContour (logDeriv completedRiemannZeta) T₁ T₂ =
      halfContour (logDeriv riemannZeta) T₁ T₂ + halfContour (logDeriv Complex.Gammaℝ) T₁ T₂ := by
  have hmem : ∀ σ : ℝ, σ ∈ Set.uIcc (1/2:ℝ) 2 → 1/2 ≤ σ ∧ σ ≤ 2 := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
    exact ⟨hσ.1, hσ.2⟩
  
  have hseg : ∀ (T : ℝ), 1 ≤ T → GoodHeight T → ∀ σ ∈ Set.uIcc (1/2:ℝ) 2,
      ((σ:ℂ) + T*I ≠ 0 ∧ (σ:ℂ) + T*I ≠ 1 ∧ riemannZeta ((σ:ℂ) + T*I) ≠ 0
        ∧ 0 < ((σ:ℂ) + T*I).re) := by
    intro T hT hg σ hσ
    obtain ⟨ha, hb'⟩ := hmem σ hσ
    have hre : ((σ:ℂ) + T*I).re = σ := by simp
    have him : ((σ:ℂ) + T*I).im = T := by simp
    refine contour_point_facts ?_ ?_ ?_ ?_
    · rw [hre]; exact ha
    · rw [hre]; exact hb'
    · rw [him]; exact hT
    · rw [him]; exact fun ρ hρ => hg ρ hρ
  
  have hvert : ∀ t : ℝ, t ∈ Set.uIcc T₁ T₂ →
      ((2:ℂ) + t*I ≠ 0 ∧ (2:ℂ) + t*I ≠ 1 ∧ riemannZeta ((2:ℂ) + t*I) ≠ 0
        ∧ 0 < ((2:ℂ) + t*I).re) := by
    intro t _
    have hre : ((2:ℂ) + t*I).re = 2 := by simp
    refine ⟨?_, ?_, riemannZeta_ne_zero_of_one_le_re (by rw [hre]; norm_num), by rw [hre]; norm_num⟩
    · intro hh
      have := congrArg Complex.re hh
      rw [hre] at this
      simp at this
    · intro hh
      have := congrArg Complex.re hh
      rw [hre] at this
      simp at this
  
  have keyb : Set.EqOn (fun σ : ℝ => logDeriv completedRiemannZeta ((σ:ℂ) + T₁*I))
      (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T₁*I)
        + logDeriv Complex.Gammaℝ ((σ:ℂ) + T₁*I)) (Set.uIcc (1/2:ℝ) 2) := by
    intro σ hσ
    obtain ⟨hs0, hs1, hζ, hre⟩ := hseg T₁ h1 hg1 σ hσ
    simp only
    rw [Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζ hre]
    ring
  have keyt : Set.EqOn (fun σ : ℝ => logDeriv completedRiemannZeta ((σ:ℂ) + T₂*I))
      (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T₂*I)
        + logDeriv Complex.Gammaℝ ((σ:ℂ) + T₂*I)) (Set.uIcc (1/2:ℝ) 2) := by
    intro σ hσ
    obtain ⟨hs0, hs1, hζ, hre⟩ := hseg T₂ (by linarith) hg2 σ hσ
    simp only
    rw [Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζ hre]
    ring
  have keyr : Set.EqOn (fun t : ℝ => logDeriv completedRiemannZeta ((2:ℂ) + t*I))
      (fun t : ℝ => logDeriv riemannZeta ((2:ℂ) + t*I)
        + logDeriv Complex.Gammaℝ ((2:ℂ) + t*I)) (Set.uIcc T₁ T₂) := by
    intro t ht
    obtain ⟨hs0, hs1, hζ, hre⟩ := hvert t ht
    simp only
    rw [Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζ hre]
    ring
  
  have hintb : ∀ (T : ℝ), 1 ≤ T → GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T*I))
        MeasureTheory.volume (1/2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨_, hs1, hζ, _⟩ := hseg T hT hg σ hσ
    have hparam : ContinuousAt (fun σ : ℝ => (σ:ℂ) + T*I) σ := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun σ : ℝ => (σ:ℂ) + T*I)
        (continuousAt_logDeriv_zeta hs1 hζ) hparam)
  have hintbΓ : ∀ (T : ℝ), 1 ≤ T → GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ:ℂ) + T*I))
        MeasureTheory.volume (1/2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨_, _, _, hre⟩ := hseg T hT hg σ hσ
    have hparam : ContinuousAt (fun σ : ℝ => (σ:ℂ) + T*I) σ := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv Complex.Gammaℝ) (f := fun σ : ℝ => (σ:ℂ) + T*I)
        (continuousAt_logDeriv_Gammaℝ hre) hparam)
  have hintr : IntervalIntegrable (fun t : ℝ => logDeriv riemannZeta ((2:ℂ) + t*I))
      MeasureTheory.volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    obtain ⟨_, hs1, hζ, _⟩ := hvert t ht
    have hparam : ContinuousAt (fun t : ℝ => (2:ℂ) + t*I) t := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun t : ℝ => (2:ℂ) + t*I)
        (continuousAt_logDeriv_zeta hs1 hζ) hparam)
  have hintrΓ : IntervalIntegrable (fun t : ℝ => logDeriv Complex.Gammaℝ ((2:ℂ) + t*I))
      MeasureTheory.volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    obtain ⟨_, _, _, hre⟩ := hvert t ht
    have hparam : ContinuousAt (fun t : ℝ => (2:ℂ) + t*I) t := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv Complex.Gammaℝ) (f := fun t : ℝ => (2:ℂ) + t*I)
        (continuousAt_logDeriv_Gammaℝ hre) hparam)
  
  unfold halfContour
  rw [intervalIntegral.integral_congr keyb, intervalIntegral.integral_congr keyt,
    intervalIntegral.integral_congr keyr,
    intervalIntegral.integral_add (hintb T₁ h1 hg1) (hintbΓ T₁ h1 hg1),
    intervalIntegral.integral_add (hintb T₂ (by linarith) hg2) (hintbΓ T₂ (by linarith) hg2),
    intervalIntegral.integral_add hintr hintrΓ]
  ring

set_option maxHeartbeats 1600000 in
theorem exists_goodHeight (a : ℝ) : ∃ T ∈ Set.Icc a (a + 1), GoodHeight T := by
  have hfin : ((fun ρ : ℂ => ρ.im) '' zerosIn a (a + 1)).Finite :=
    (zerosIn_finite a (a + 1)).image _
  have hinf : (Set.Ioo a (a + 1)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨T, hT⟩ := (hinf.sdiff hfin).nonempty
  obtain ⟨hT, hTnot⟩ := hT
  refine ⟨T, ⟨hT.1.le, hT.2.le⟩, ?_⟩
  intro ρ hρ him
  apply hTnot
  refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
  · rw [him]; exact hT.1
  · rw [him]; exact hT.2.le

set_option maxHeartbeats 1600000 in
theorem rvM_main_param {CB TB A₀ Cμ Tμ CM : ℝ}
    (hB : ∀ T : ℝ, TB ≤ T → (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ CB * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi)
    (hA₀1 : 1 ≤ A₀) (hA₀ : ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hCμ : ∀ T : ℝ, Tμ ≤ T →
      |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T)
    (hCM0 : 0 < CM) (hCM : ∀ τ : ℝ, 1 ≤ τ → |mu τ| ≤ CM * Real.log (τ + 3))
    (hμc : Continuous mu) :
    ∀ T : ℝ, max (max (TB + 1) (Tμ + 1)) 4 ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T|
        ≤ (3 * |CB| + 4 * A₀ + 4 * CM + |Cμ| + 1) * Real.log T := by
  have hA₀0 : 0 ≤ A₀ := by linarith
  intro T hT
  have hT4 : 4 ≤ T := le_trans (le_max_right _ _) hT
  have hTB : TB + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTμ : Tμ + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans (by linarith [Real.exp_one_lt_d9]) le_rfl)
  have hlogT0 : 0 < Real.log T := by linarith
  
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight (T - 1)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight (2 * T)
  have hT₁a : T - 1 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ T := by have := hT₁mem.2; linarith
  have hT₂a : 2 * T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ 2 * T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ < T₂ := by linarith
  
  have hN := N_eq_halfContour_completedZeta h1T₁ h12 hg1 hg2
  have hsplit := halfContour_completedZeta_split h1T₁ h12 hg1 hg2
  have hgam := gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  
  have hadd : (Ncount T₁ T₂ : ℝ)
      = (Ncount T₁ T : ℝ) + (Ncount T (2*T) : ℝ) + (Ncount (2*T) T₂ : ℝ) := by
    have e1 := Zeta23.Ncount_add (a := T₁) (b := T) (c := T₂) hT₁b (by linarith)
    have e2 := Zeta23.Ncount_add (a := T) (b := 2*T) (c := T₂) (by linarith) hT₂a
    rw [e1, e2]
    push_cast
    ring
  
  have hlogsq : ∀ x : ℝ, 0 < x → x + 3 ≤ T ^ 2 → Real.log (x + 3) ≤ 2 * Real.log T := by
    intro x hx hxT
    calc Real.log (x + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hxT
      _ = 2 * Real.log T := by
          rw [Real.log_pow]
          push_cast
          ring
  have hw1 : (Ncount T₁ T : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Ncount T₁ T ≤ Ncount T₁ (T₁ + 1) :=
      Zeta23.Ncount_mono le_rfl (by linarith)
    calc (Ncount T₁ T : ℝ) ≤ (Ncount T₁ (T₁ + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|T₁| + 3) := hA₀ T₁
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < T₁)]
          exact hlogsq T₁ (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  have hw2 : (Ncount (2*T) T₂ : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Ncount (2*T) T₂ ≤ Ncount (2*T) (2*T + 1) :=
      Zeta23.Ncount_mono le_rfl hT₂b
    calc (Ncount (2*T) T₂ : ℝ) ≤ (Ncount (2*T) (2*T+1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|2*T| + 3) := hA₀ (2*T)
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < 2*T)]
          exact hlogsq (2*T) (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  
  have hbk1 := hB T₁ (by linarith) hg1
  have hbk2 := hB T₂ (by linarith) hg2
  have hvert := vertical_two T₁ T₂
  have hζbound : |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
    have hlog₁0 : 0 ≤ Real.log T₁ := Real.log_nonneg h1T₁
    have hlog₂0 : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
    unfold halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [eim]
    have hmulI : ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
        = (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))).symm
    have h1 : |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im| ≤ |CB| * Real.log T₁ :=
      hbk1.trans (by
        have : CB * Real.log T₁ ≤ |CB| * Real.log T₁ :=
          mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₁0
        linarith)
    have h2 : |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| ≤ |CB| * Real.log T₂ :=
      hbk2.trans (by
        have : CB * Real.log T₂ ≤ |CB| * Real.log T₂ :=
          mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₂0
        linarith)
    calc |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im|
        ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im|
          + |((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
          rw [hmulI]
          have := hvert
          linarith
  
  have hμint : ∀ a b : ℝ, IntervalIntegrable mu MeasureTheory.volume a b :=
    fun a b => hμc.intervalIntegrable a b
  have hμsplit : (∫ t in T₁..T₂, mu t)
      = (∫ t in T₁..T, mu t) + (∫ t in T..(2*T), mu t) + ∫ t in (2*T)..T₂, mu t := by
    have e1 : (∫ t in T₁..(2*T), mu t) = (∫ t in T₁..T, mu t) + ∫ t in T..(2*T), mu t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ T) (hμint T (2*T))).symm
    have e2 : (∫ t in T₁..T₂, mu t) = (∫ t in T₁..(2*T), mu t) + ∫ t in (2*T)..T₂, mu t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ (2*T)) (hμint (2*T) T₂)).symm
    rw [e2, e1]
  have hμwin : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2*T + 1 → |b - a| ≤ 1 →
      |∫ t in a..b, mu t| ≤ 2 * CM * Real.log T := by
    intro a b ha hab hb hba
    have hbound : ∀ t ∈ Set.uIoc a b, ‖mu t‖ ≤ CM * Real.log (2*T + 4) := by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht1 : 1 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2*T + 1 := le_trans ht.2 hb
      rw [Real.norm_eq_abs]
      refine (hCM t ht1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCM0.le
      exact Real.log_le_log (by linarith) (by linarith)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at this
    have hlog24 : Real.log (2*T + 4) ≤ 2 * Real.log T := by
      calc Real.log (2*T + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
    calc |∫ t in a..b, mu t| ≤ CM * Real.log (2*T+4) * |b - a| := this
      _ ≤ CM * (2 * Real.log T) * 1 := by
          refine mul_le_mul ?_ hba (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog24 hCM0.le
      _ = 2 * CM * Real.log T := by ring
  have hμ1 : |∫ t in T₁..T, mu t| ≤ 2 * CM * Real.log T :=
    hμwin T₁ T h1T₁ hT₁b (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hμ2 : |∫ t in (2*T)..T₂, mu t| ≤ 2 * CM * Real.log T :=
    hμwin (2*T) T₂ (by linarith) hT₂a (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hintmu := hCμ T (by linarith)
  have hT0 : (0:ℝ) < T := by linarith
  have hCμT : Cμ / T ≤ |Cμ| := by
    calc Cμ / T ≤ |Cμ| / T := by gcongr; exact le_abs_self _
      _ ≤ |Cμ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          linarith
      _ = |Cμ| := div_one _
  
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hkey : (Ncount T (2*T) : ℝ) - T * ell1 T / (2 * Real.pi)
      = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)) := by
    have hΛim : (1/Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im
        = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
          + (1/Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im := by
      rw [hsplit, Complex.add_im]
      ring
    have h5 : (Ncount T₁ T₂ : ℝ)
        = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
          + ∫ t in T₁..T₂, mu t := by
      rw [hN, hΛim, hgam]
    rw [hμsplit] at h5
    have h6 := hadd
    linarith
  have hlogT₁ : Real.log T₁ ≤ Real.log T := Real.log_le_log (by linarith) hT₁b
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log T := by
    calc Real.log T₂ ≤ Real.log (T^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  
  have hNc1 : (0:ℝ) ≤ (Ncount T₁ T : ℝ) := Nat.cast_nonneg _
  have hNc2 : (0:ℝ) ≤ (Ncount (2*T) T₂ : ℝ) := Nat.cast_nonneg _
  have hA : |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ 3 * |CB| * Real.log T + 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/Real.pi)]
    have step1 : (1/Real.pi) * |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1/Real.pi) * (|CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂) := by
      exact mul_le_mul_of_nonneg_left hζbound (by positivity)
    have hfrac : (1:ℝ)/Real.pi ≤ 1 := by
      rw [div_le_one hπ]
      exact hπ1
    have e1 : (1/Real.pi) * (|CB| * Real.log T₁) ≤ |CB| * Real.log T := by
      calc (1/Real.pi) * (|CB| * Real.log T₁) ≤ 1 * (|CB| * Real.log T₁) := by
            apply mul_le_mul_of_nonneg_right hfrac
            exact mul_nonneg (abs_nonneg _) (Real.log_nonneg h1T₁)
        _ = |CB| * Real.log T₁ := one_mul _
        _ ≤ |CB| * Real.log T := mul_le_mul_of_nonneg_left hlogT₁ (abs_nonneg _)
    have e2 : (1/Real.pi) * Real.pi = 1 := by field_simp
    have e3 : (1/Real.pi) * (|CB| * Real.log T₂) ≤ 2 * |CB| * Real.log T := by
      calc (1/Real.pi) * (|CB| * Real.log T₂) ≤ 1 * (|CB| * Real.log T₂) := by
            apply mul_le_mul_of_nonneg_right hfrac
            exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))
        _ = |CB| * Real.log T₂ := one_mul _
        _ ≤ |CB| * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlogT₂ (abs_nonneg _)
        _ = 2 * |CB| * Real.log T := by ring
    calc (1/Real.pi) * |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1/Real.pi) * (|CB| * Real.log T₁) + (1/Real.pi) * Real.pi
          + (1/Real.pi) * (|CB| * Real.log T₂) := by
          rw [← mul_add, ← mul_add]
          exact step1
      _ ≤ |CB| * Real.log T + 1 + 2 * |CB| * Real.log T := by
          rw [e2]
          linarith
      _ = 3 * |CB| * Real.log T + 1 := by ring
  have hD : |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ |Cμ| * Real.log T := by
    calc |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T := hintmu
      _ ≤ |Cμ| := hCμT
      _ = |Cμ| * 1 := (mul_one _).symm
      _ ≤ |Cμ| * Real.log T := mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
  
  simp only [zetaZeroConfig_N]
  rw [show T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) by ring, hkey]
  have htri : |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ))|
      ≤ |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im|
        + (|∫ t in T₁..T, mu t| + |∫ t in (2*T)..T₂, mu t|
        + |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)|)
        + ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)) := by
    have t1 := abs_sub (((1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))))
      (((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)))
    have t2 := abs_add_le ((1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im)
      ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
    have t3 := abs_add_le ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t))
      ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi))
    have t4 := abs_add_le (∫ t in T₁..T, mu t) (∫ t in (2*T)..T₂, mu t)
    have t5 : |(Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)|
        = (Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ) := abs_of_nonneg (by positivity)
    linarith
  refine htri.trans ?_
  linarith [hA, hμ1, hμ2, hD, hw1, hw2]

set_option maxHeartbeats 1600000 in
theorem rvM_main_aux (hΓ : GammaFacts)
    (backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by
  obtain ⟨CB, TB, hB⟩ := backlund_horizontal
  obtain ⟨A₀, hA₀1, hA₀⟩ := zeta_local_zero_count
  obtain ⟨Cμ, Tμ, hCμ⟩ := hΓ.int_mu
  obtain ⟨CM, hCM0, hCM⟩ := mu_le_log hΓ
  exact ⟨_, _, rvM_main_param hB vertical_two hA₀1 hA₀ hCμ hCM0 hCM (mu_continuous hΓ)⟩

set_option maxHeartbeats 1600000 in
theorem rvM_main (hΓ : GammaFacts) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T :=
  rvM_main_aux hΓ backlund_horizontal vertical_two

end Zeta23.RvM

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.GammaFacts -/
section
namespace Zeta23

open Complex

open scoped ContDiff

set_option maxHeartbeats 1600000 in
theorem digamma_conj (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by
  have hG : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext w
    simp only [Function.comp_apply]
    rw [Complex.Gamma_conj]
    exact Complex.conj_conj _
  have hd : deriv Complex.Gamma ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hG, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply]
  rw [hd, Complex.Gamma_conj, ← map_div₀]

set_option maxHeartbeats 1600000 in
theorem mu_even (τ : ℝ) : mu (-τ) = mu τ := by
  unfold mu
  have harg : (1 / 4 + Complex.I * ((-τ : ℝ) : ℂ) / 2 : ℂ)
      = (starRingEnd ℂ) (1 / 4 + Complex.I * (τ : ℂ) / 2) := by
    apply Complex.ext <;> simp [map_ofNat]
  rw [show ((-τ : ℝ) : ℂ) = -(τ : ℂ) by push_cast; ring] at harg ⊢
  rw [harg, digamma_conj]
  simp

set_option maxHeartbeats 1600000 in
private lemma gamma_ne_neg_nat {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz

set_option maxHeartbeats 1600000 in
private lemma analyticAt_digamma {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGamD : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (gamma_ne_neg_nat hw)).differentiableWithinAt
  have hGamA := hGamD.analyticOnNhd hU
  have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := (hGamA z hz).deriv
  have h2 : AnalyticAt ℂ Complex.Gamma z := hGamA z hz
  have h3 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (gamma_ne_neg_nat hz)
  have h4 := h1.div h2 h3
  exact h4.congr (by
    filter_upwards with w
    rw [Complex.digamma_def, logDeriv_apply]
    rfl)

set_option maxHeartbeats 1600000 in
theorem mu_smooth : ContDiff ℝ ∞ mu := by
  have hc : ContDiff ℝ ∞ (fun τ : ℝ => (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)) := by
    have h1 : ContDiff ℝ ∞ (fun τ : ℝ => (τ : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ)) := contDiff_const.mul h1
    have h3 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ) / 2) := by
      simpa [div_eq_mul_inv] using h2.mul contDiff_const
    exact contDiff_const.add h3
  refine contDiff_iff_contDiffAt.mpr fun τ => ?_
  have hz : (0 : ℝ) < (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ).re := by
    simp
  have h4' : AnalyticAt ℝ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    AnalyticAt.restrictScalars (analyticAt_digamma hz)
  have h4 : ContDiffAt ℝ ∞ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    h4'.contDiffAt
  have h5 : ContDiffAt ℝ ∞
      (fun τ : ℝ => Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)) τ :=
    h4.comp τ hc.contDiffAt
  have h6 : ContDiffAt ℝ ∞
      (fun τ : ℝ => (Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)).re) τ :=
    (Complex.reCLM.contDiff.contDiffAt).comp τ h5
  have h7 : ContDiffAt ℝ ∞ mu τ := by
    have := (contDiffAt_const (c := (1 / (2 * Real.pi) : ℝ))).mul h6
    exact (this.sub contDiffAt_const)
  exact h7

end Zeta23

end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.GammaFacts.Series -/
section
noncomputable section

namespace Zeta23

namespace DigammaSeries

open Complex Filter Topology

def wTerm (n : ℕ) (z : ℂ) : ℂ := (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1

set_option maxHeartbeats 1600000 in
lemma one_add_wTerm (n : ℕ) (z : ℂ) :
    1 + wTerm n z = (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  unfold wTerm
  ring

set_option maxHeartbeats 1600000 in
lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]

set_option maxHeartbeats 1600000 in
lemma norm_wTerm_le {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖wTerm n z‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by
  set w : ℂ := z / ((n : ℂ) + 1) with hwdef
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hwnorm : ‖w‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [hwdef, norm_div, norm_natCast_add_one]
  have hwn : ‖w‖ ≤ 1 := by
    rw [hwnorm, div_le_one hn1]
    exact h
  have hr : ‖Complex.exp (-w) - 1 + w‖ ≤ ‖w‖ ^ 2 := by
    have hx : ‖(-w : ℂ)‖ ≤ 1 := by rwa [norm_neg]
    have h2 := norm_exp_sub_one_sub_id_le hx
    rw [norm_neg] at h2
    calc ‖Complex.exp (-w) - 1 + w‖ = ‖Complex.exp (-w) - 1 - (-w)‖ := by ring_nf
      _ ≤ ‖w‖ ^ 2 := h2
  have hident : wTerm n z = (Complex.exp (-w) - 1 + w) - w ^ 2
      + w * (Complex.exp (-w) - 1 + w) := by
    unfold wTerm
    ring
  have hnw2 : ‖(w : ℂ) ^ 2‖ = ‖w‖ ^ 2 := norm_pow _ _
  calc ‖wTerm n z‖
      ≤ ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ + ‖w * (Complex.exp (-w) - 1 + w)‖ := by
        rw [hident]
        exact norm_add_le _ _
    _ ≤ (‖w‖ ^ 2 + ‖w‖ ^ 2) + ‖w‖ * ‖w‖ ^ 2 := by
        have h1 : ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
          calc ‖(Complex.exp (-w) - 1 + w) - w ^ 2‖
              ≤ ‖Complex.exp (-w) - 1 + w‖ + ‖(w : ℂ) ^ 2‖ := norm_sub_le _ _
            _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
                rw [hnw2]
                exact add_le_add hr le_rfl

        have h2 : ‖w * (Complex.exp (-w) - 1 + w)‖ ≤ ‖w‖ * ‖w‖ ^ 2 := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
        linarith
    _ ≤ 3 * ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hwn, sq_nonneg ‖w‖]
    _ = 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by rw [hwnorm]

set_option maxHeartbeats 1600000 in
lemma summable_wBound (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _

set_option maxHeartbeats 1600000 in
lemma summable_norm_wTerm (z : ℂ) : Summable (fun n => ‖wTerm n z‖) := by
  refine (summable_wBound ‖z‖).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine norm_wTerm_le ?_
  calc ‖z‖ ≤ (⌈‖z‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith

set_option maxHeartbeats 1600000 in
lemma multipliable_one_add_wTerm (z : ℂ) : Multipliable fun n => 1 + wTerm n z :=
  Complex.multipliable_one_add_of_summable ((summable_norm_wTerm z).of_norm)

set_option maxHeartbeats 1600000 in
lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

set_option maxHeartbeats 1600000 in
lemma inv_gammaSeq_eq {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  
  have hprod : ∏ n ∈ Finset.range N, (1 + wTerm n z)
      = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
          * Complex.exp (-(∑ m ∈ Finset.range N, z / ((m : ℂ) + 1))) := by
    calc ∏ n ∈ Finset.range N, (1 + wTerm n z)
        = ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
            * Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_congr rfl fun n _ => one_add_wTerm n z
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * ∏ n ∈ Finset.range N, Complex.exp (-(z / ((n : ℂ) + 1))) :=
          Finset.prod_mul_distrib
      _ = (∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1)))
            * Complex.exp (∑ n ∈ Finset.range N, -(z / ((n : ℂ) + 1))) := by
          rw [Complex.exp_sum]
      _ = _ := by rw [← Finset.sum_neg_distrib]
  
  have hfact_ne : ((N.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hNz : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcpow : (N : ℂ) ^ z = Complex.exp (((Real.log N : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hNz]
    congr 2
    rw [show ((N : ℂ)) = (((N : ℝ) : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log hNR.le).symm
  have hdenom : ∏ j ∈ Finset.range (N + 1), (z + (j : ℂ))
      = z * ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    rw [Nat.cast_zero, add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun n _ => ?_
    push_cast
    ring
  have hfactprod : ((N.factorial : ℕ) : ℂ) = ∏ n ∈ Finset.range N, ((n : ℂ) + 1) := by
    rw [show N.factorial = ∏ n ∈ Finset.range N, (n + 1) from
      (Finset.prod_range_add_one_eq_factorial N).symm]
    push_cast
    rfl
  have hfrac : ∏ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
      = (∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1))) / ((N.factorial : ℕ) : ℂ) := by
    have h1 : ∀ n ∈ Finset.range N, (1 + z / ((n : ℂ) + 1))
        = (z + ((n : ℂ) + 1)) / ((n : ℂ) + 1) := by
      intro n _
      have hne : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_div_distrib, hfactprod]
  have hsumcast : (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    push_cast
    rfl
  have hzsum : ∑ m ∈ Finset.range N, z / ((m : ℂ) + 1)
      = z * ∑ m ∈ Finset.range N, 1 / ((m : ℂ) + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  
  rw [Complex.GammaSeq, hprod, hfrac, hdenom, hcpow, hzsum, ← hsumcast]
  rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub]
  set A : ℂ := ∏ n ∈ Finset.range N, (z + ((n : ℂ) + 1)) with hA
  set E1 : ℂ := Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) * z)
    with hE1
  set E2 : ℂ := Complex.exp (((Real.log N : ℝ) : ℂ) * z) with hE2
  have hE1ne : E1 ≠ 0 := Complex.exp_ne_zero _
  have hE2ne : E2 ≠ 0 := Complex.exp_ne_zero _
  have hexpneg : Complex.exp (-(z * (((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ)))
      = E1⁻¹ := by
    rw [hE1, ← Complex.exp_neg]
    congr 1
    ring
  rw [hexpneg]
  field_simp

set_option maxHeartbeats 1600000 in
theorem inv_gamma_eq_prod {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + wTerm n z) := by
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hL : Tendsto (fun N => (Complex.GammaSeq z N)⁻¹) atTop (𝓝 ((Complex.Gamma z)⁻¹)) :=
    (Complex.GammaSeq_tendsto_Gamma z).inv₀ (Complex.Gamma_ne_zero hzero)
  have hhar : Tendsto (fun N : ℕ =>
      ((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    refine Real.tendsto_harmonic_sub_log.congr fun n => ?_
    rw [harmonic_cast_eq]
  have hexp : Tendsto (fun N : ℕ => Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z))
      atTop (𝓝 (Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))) := by
    have h2 : Tendsto (fun N : ℕ =>
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ)))
        atTop (𝓝 ((Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hhar
    exact (Complex.continuous_exp.tendsto _).comp (h2.mul_const z)
  have hP : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (∏' n : ℕ, (1 + wTerm n z))) :=
    (multipliable_one_add_wTerm z).hasProd.tendsto_prod_nat
  have hRHS : Tendsto (fun N : ℕ => z * Complex.exp
      ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z)) atTop
      (𝓝 (z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * ∏' n : ℕ, (1 + wTerm n z))) :=
    (tendsto_const_nhds.mul hexp).mul hP
  have heq : ∀ᶠ N in atTop, (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp
        ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1)) - Real.log N : ℝ) : ℂ) * z)
      * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact inv_gammaSeq_eq hz hN
  exact tendsto_nhds_unique (hL.congr' heq) hRHS

set_option maxHeartbeats 1600000 in
lemma logDeriv_one_add_wTerm {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + wTerm n s) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
    have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
    push_cast at this ⊢
    convert this using 2
  have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
    rw [add_assoc]
    exact hzn
  have hfun : (fun s => 1 + wTerm n s)
      = fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))) := by
    funext s
    exact one_add_wTerm n s
  rw [hfun]
  have h1z : (1 + z / ((n : ℂ) + 1)) ≠ 0 := by
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hd1 : HasDerivAt (fun s : ℂ => 1 + s / ((n : ℂ) + 1)) (1 / ((n : ℂ) + 1)) z := by
    have h3 := ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).const_add 1
    simpa [one_div] using h3
  have hd2 : HasDerivAt (fun s : ℂ => Complex.exp (-(s / ((n : ℂ) + 1))))
      (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1)))) z := by
    have hlin : HasDerivAt (fun s : ℂ => -(s / ((n : ℂ) + 1))) (-(1 / ((n : ℂ) + 1))) z := by
      exact ((hasDerivAt_id z).div_const ((n : ℂ) + 1)).neg
    have h5 := hlin.cexp
    simpa [mul_comm] using h5
  have hprod : HasDerivAt
      (fun s : ℂ => (1 + s / ((n : ℂ) + 1)) * Complex.exp (-(s / ((n : ℂ) + 1))))
      (1 / ((n : ℂ) + 1) * Complex.exp (-(z / ((n : ℂ) + 1)))
        + (1 + z / ((n : ℂ) + 1)) * (-(1 / ((n : ℂ) + 1)) * Complex.exp (-(z / ((n : ℂ) + 1))))) z :=
    hd1.mul hd2
  unfold logDeriv
  rw [Pi.div_apply, hprod.deriv]
  have hexpne : Complex.exp (-(z / ((n : ℂ) + 1))) ≠ 0 := Complex.exp_ne_zero _
  have h3 : (1 : ℂ) + (n : ℂ) + z ≠ 0 := by
    intro h
    apply hzn'
    linear_combination h
  field_simp [h3]
  have h4 : ((1 : ℂ) + (n : ℂ) + z) * ((1 + (n : ℂ) + z)⁻¹) = 1 := mul_inv_cancel₀ h3
  linear_combination (-z) * h4

set_option maxHeartbeats 1600000 in
theorem summable_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  refine Summable.of_norm ?_
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
  · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
      have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
        have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
        have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
          funext n
          rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rwa [heq] at h3
      have h4 := (summable_nat_add_iff 1).mpr h2
      simpa [add_comm] using h4
    exact h1.mul_left _
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    have hzn' : z + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hzn
    have hident : 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)
        = z / (((n : ℂ) + 1) * (z + n + 1)) := by
      field_simp
      ring
    have h2n : 2 * ‖z‖ ≤ (n : ℝ) := by
      calc 2 * ‖z‖ ≤ (⌈2 * ‖z‖⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖z + (n : ℂ) + 1‖ := by
      have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + (n : ℂ) + 1‖ := by
        have h2 := norm_sub_le (z + (n : ℂ) + 1) z
        have h3 : (z + (n : ℂ) + 1) - z = ((n : ℂ) + 1) := by ring
        rw [h3] at h2
        linarith
      rw [norm_natCast_add_one] at h1
      linarith [norm_nonneg z]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hident, norm_div, norm_mul,
      norm_natCast_add_one]
    calc ‖z‖ / (((n : ℝ) + 1) * ‖z + (n : ℂ) + 1‖)
        ≤ ‖z‖ / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
          gcongr
      _ = 2 * ‖z‖ * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
          field_simp

set_option maxHeartbeats 1600000 in
theorem hasSum_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  set γc : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with hγc
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  set U : Set ℂ := Metric.ball (0 : ℂ) (‖z‖ + 1) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hU, Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg z]
  have htend : MultipliableLocallyUniformlyOn (fun n (s : ℂ) => 1 + wTerm n s) U := by
    refine Summable.multipliableLocallyUniformlyOn_nat_one_add hUopen
      (summable_wBound (‖z‖ + 1)) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖ + 1⌉₊] with n hn x hx
      have hx1 : ‖x‖ ≤ ‖z‖ + 1 := by
        rw [hU, Metric.mem_ball, dist_zero_right] at hx
        linarith
      have hn1 : ‖z‖ + 1 ≤ (n : ℝ) + 1 := by
        calc ‖z‖ + 1 ≤ (⌈‖z‖ + 1⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
          _ ≤ (n : ℝ) + 1 := by linarith
      calc ‖wTerm n x‖ ≤ 3 * (‖x‖ / ((n : ℝ) + 1)) ^ 2 :=
            norm_wTerm_le (le_trans hx1 hn1)
        _ ≤ 3 * ((‖z‖ + 1) / ((n : ℝ) + 1)) ^ 2 := by
            gcongr
    · intro n
      have hc : Continuous (wTerm n) := by
        unfold wTerm
        fun_prop
      exact hc.continuousOn
  have hfne : ∀ n : ℕ, (fun s : ℂ => 1 + wTerm n s) z ≠ 0 := by
    intro n
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hzn : z + ((n : ℂ) + 1) ≠ 0 := by
      have := Complex.integerComplement_add_ne_zero hz ((n : ℤ) + 1)
      push_cast at this ⊢
      convert this using 2
    simp only [one_add_wTerm]
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    intro h
    apply hzn
    have h2 := congrArg (fun t => t * ((n : ℂ) + 1)) h
    simp only [add_mul, one_mul, zero_mul] at h2
    rw [div_mul_cancel₀ _ hn1] at h2
    rw [← h2]
    ring
  have hgne : z * Complex.exp (γc * z) ≠ 0 := mul_ne_zero hz0 (Complex.exp_ne_zero _)
  have hPne : (∏' n : ℕ, (1 + wTerm n z)) ≠ 0 := by
    intro h
    have h2 := inv_gamma_eq_prod hz
    rw [← hγc, h, mul_zero] at h2
    exact inv_ne_zero hΓne h2
  have hsummable : Summable fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z := by
    have hcongr : (fun n : ℕ => logDeriv (fun s => 1 + wTerm n s) z)
        = fun n : ℕ => -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [hcongr]
    exact (summable_digamma_series hz).neg
  have hlogP : logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z
      = ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    refine logDeriv_tprod_eq_tsum hUopen hzU hfne ?_ hsummable htend hPne
    intro n
    have hd : Differentiable ℂ fun s : ℂ => 1 + wTerm n s := by
      unfold wTerm
      fun_prop
    exact hd.differentiableOn
  have hgdiff : Differentiable ℂ fun s : ℂ => s * Complex.exp (γc * s) := by
    fun_prop
  have hPdiff : DifferentiableAt ℂ (fun s => ∏' n : ℕ, (1 + wTerm n s)) z := by
    have hev : (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s)))
        =ᶠ[nhds z] (fun s => ∏' n : ℕ, (1 + wTerm n s)) := by
      filter_upwards [hopenZ.mem_nhds hz] with s hs
      have h2 := inv_gamma_eq_prod hs
      rw [← hγc] at h2
      have hsne : s * Complex.exp (γc * s) ≠ 0 :=
        mul_ne_zero (Complex.integerComplement.ne_zero hs) (Complex.exp_ne_zero _)
      rw [h2]
      exact mul_div_cancel_left₀ _ hsne
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (Complex.Gamma s)⁻¹ / (s * Complex.exp (γc * s))) z := by
      refine DifferentiableAt.div ?_ (hgdiff z) hgne
      exact Complex.differentiable_one_div_Gamma z
    exact hd.congr_of_eventuallyEq hev.symm
  have hldinv : logDeriv (fun s => (Complex.Gamma s)⁻¹) z = -Complex.digamma z := by
    have h1 : logDeriv ((·⁻¹) ∘ Complex.Gamma) z
        = logDeriv (·⁻¹) (Complex.Gamma z) * deriv Complex.Gamma z := by
      refine logDeriv_comp ?_ (Complex.differentiableAt_Gamma z hzero)
      exact differentiableAt_inv hΓne
    rw [show (fun s => (Complex.Gamma s)⁻¹) = (·⁻¹) ∘ Complex.Gamma from rfl, h1, logDeriv_inv]
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp
  have hev2 : (fun s => (Complex.Gamma s)⁻¹)
      =ᶠ[nhds z] fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s) := by
    filter_upwards [hopenZ.mem_nhds hz] with s hs
    have h2 := inv_gamma_eq_prod hs
    rw [← hγc] at h2
    rw [h2]
  have hlogeq : logDeriv (fun s => (Complex.Gamma s)⁻¹) z
      = logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z := by
    unfold logDeriv
    rw [Pi.div_apply, Pi.div_apply, hev2.deriv_eq, hev2.eq_of_nhds]
  have hmul : logDeriv (fun s => (s * Complex.exp (γc * s)) * ∏' n : ℕ, (1 + wTerm n s)) z
      = logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z
        + logDeriv (fun s => ∏' n : ℕ, (1 + wTerm n s)) z :=
    logDeriv_mul z hgne hPne (hgdiff z) hPdiff
  have hldg : logDeriv (fun s : ℂ => s * Complex.exp (γc * s)) z = 1 / z + γc := by
    have hder : HasDerivAt (fun s : ℂ => s * Complex.exp (γc * s))
        (1 * Complex.exp (γc * z) + z * (γc * Complex.exp (γc * z))) z := by
      have h1 : HasDerivAt (fun s : ℂ => Complex.exp (γc * s)) (γc * Complex.exp (γc * z)) z := by
        have hlin : HasDerivAt (fun s : ℂ => γc * s) γc z := by
          simpa using (hasDerivAt_id z).const_mul γc
        have h5 := hlin.cexp
        simpa [mul_comm] using h5
      exact (hasDerivAt_id z).mul h1
    unfold logDeriv
    rw [Pi.div_apply, hder.deriv]
    have he : Complex.exp (γc * z) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hmain : -Complex.digamma z
      = (1 / z + γc) + ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z := by
    rw [← hldinv, hlogeq, hmul, hldg, hlogP]
  have htsum : ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      = Complex.digamma z + γc + 1 / z := by
    have h1 : ∑' n : ℕ, logDeriv (fun s => 1 + wTerm n s) z
        = ∑' n : ℕ, -(1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
      congr 1
      funext n
      rw [logDeriv_one_add_wTerm hz n]
      ring
    rw [h1, tsum_neg] at hmain
    linear_combination hmain
  have h := (summable_digamma_series hz).hasSum
  rwa [htsum] at h

set_option maxHeartbeats 1600000 in
theorem digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  rw [(hasSum_digamma_series hz).tsum_eq]
  ring

end DigammaSeries

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.Analytic.Stirling -/
section
noncomputable section

namespace Zeta23

namespace Stirling

open Complex Filter Topology

theorem differentiableAt_digamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ Complex.digamma z := by
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  have hΓan : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopenZ.mem_nhds hz] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    exact hw ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hψan : AnalyticAt ℂ Complex.digamma z := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := hΓan.deriv
    have h2 := h1.div hΓan hΓne
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact hψan.differentiableAt

theorem hasSum_trigamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / (z + n) ^ 2) (deriv Complex.digamma z) := by
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.mp hopenZ z hz
  have hr0 : 0 < ε / 2 := by positivity
  set U : Set ℂ := Metric.ball z (ε / 2) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := Metric.mem_ball_self hr0
  have hUsub : U ⊆ Complex.integerComplement :=
    subset_trans (Metric.ball_subset_ball (by linarith)) hball
  have hδ : ∀ n : ℕ, ε / 2 < ‖z + ((n : ℂ) + 1)‖ := by
    intro n
    by_contra hle
    push Not at hle
    have hmem : (-(((n : ℂ)) + 1)) ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖-((n : ℂ) + 1) - z‖ = ‖z + ((n : ℂ) + 1)‖ := by
            rw [show -((n : ℂ) + 1) - z = -(z + ((n : ℂ) + 1)) by ring, norm_neg]
        _ ≤ ε / 2 := hle
        _ < ε := by linarith
    exact (hball hmem) ⟨-((n : ℤ) + 1), by push_cast; ring⟩
  set F : ℕ → ℂ → ℂ := fun n w => 1 / ((n : ℂ) + 1) - 1 / (w + n + 1) with hF
  set u : ℕ → ℝ := fun n =>
    (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (‖z + ((n : ℂ) + 1)‖ - ε / 2)) with hu
  have hnormn1 : ∀ n : ℕ, ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    intro n
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hterm_ne : ∀ (n : ℕ) (w : ℂ), w ∈ U → w + ((n : ℂ) + 1) ≠ 0 := by
    intro n w hw h0
    have hwz : ‖w - z‖ < ε / 2 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have h1 : ‖z + ((n : ℂ) + 1)‖ = ‖z - w‖ := by
      rw [show z + ((n : ℂ) + 1) = (z - w) + (w + ((n : ℂ) + 1)) by ring, h0, add_zero]
    rw [norm_sub_rev] at h1
    have := hδ n
    linarith
  have hlow : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖z + ((n : ℂ) + 1)‖ - ε / 2 ≤ ‖w + ((n : ℂ) + 1)‖ := by
    intro n w hw
    have hwz : ‖z - w‖ < ε / 2 := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have h1 : ‖z + ((n : ℂ) + 1)‖ ≤ ‖w + ((n : ℂ) + 1)‖ + ‖z - w‖ := by
      calc ‖z + ((n : ℂ) + 1)‖ = ‖(w + ((n : ℂ) + 1)) + (z - w)‖ := by ring_nf
        _ ≤ ‖w + ((n : ℂ) + 1)‖ + ‖z - w‖ := norm_add_le _ _
    linarith
  have hFle : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖F n w‖ ≤ u n := by
    intro n w hw
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hw0 := hterm_ne n w hw
    have hw0' : w + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hw0
    have hident : F n w = w / (((n : ℂ) + 1) * (w + ((n : ℂ) + 1))) := by
      rw [hF]
      simp only
      rw [show w + ((n : ℂ) + 1) = w + (n : ℂ) + 1 by ring]
      field_simp
      ring
    have hwb : ‖w‖ ≤ ‖z‖ + ε / 2 := by
      have hwz : ‖w - z‖ < ε / 2 := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hw
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε / 2 := by linarith
    have hdl := hlow n w hw
    have hdpos : (0 : ℝ) < ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
      have := hδ n
      linarith
    rw [hident, norm_div, norm_mul, hnormn1 n, hu]
    simp only
    gcongr
  have husum : Summable u := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℕ => 2 * (‖z‖ + ε / 2) * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
    · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
        have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
          have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
          have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
            funext n
            rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rwa [heq] at h3
        have h4 := (summable_nat_add_iff 1).mpr h2
        simpa [add_comm] using h4
      exact h1.mul_left _
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop ⌈2 * (‖z‖ + ε / 2 + 1)⌉₊] with n hn
      have hn2 : 2 * (‖z‖ + ε / 2 + 1) ≤ (n : ℝ) := by
        calc 2 * (‖z‖ + ε / 2 + 1) ≤ (⌈2 * (‖z‖ + ε / 2 + 1)⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
      have hzn : ((n : ℝ) + 1) / 2 ≤ ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
        have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + ((n : ℂ) + 1)‖ := by
          have h2 := norm_sub_le (z + ((n : ℂ) + 1)) z
          have h3 : (z + ((n : ℂ) + 1)) - z = ((n : ℂ) + 1) := by ring
          rw [h3] at h2
          linarith
        rw [hnormn1 n] at h1
        have hz0 := norm_nonneg z
        linarith
      have hdpos : (0 : ℝ) < ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
        have h0 : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
        linarith
      rw [hu, Real.norm_eq_abs]
      simp only
      rw [abs_of_nonneg (by positivity)]
      calc (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (‖z + ((n : ℂ) + 1)‖ - ε / 2))
          ≤ (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
            gcongr
        _ = 2 * (‖z‖ + ε / 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
            field_simp
  have hFdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) U := by
    intro n
    rw [hF]
    simp only
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub (differentiableAt_const _) ?_
    have hne : w + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hterm_ne n w hw
    have h1 : DifferentiableAt ℂ (fun v : ℂ => v + (n : ℂ) + 1) w := by
      fun_prop
    exact (differentiableAt_const (1 : ℂ)).div h1 hne
  have hkey := hasSum_deriv_of_summable_norm husum hFdiff hUopen hFle hzU
  have hFalt : ∀ n : ℕ, F n = fun w => 1 / ((n : ℂ) + 1) - 1 / (w + ((n : ℂ) + 1)) := by
    intro n
    funext w
    rw [hF]
    simp only
    rw [add_assoc]
  have hderiv_term : ∀ n : ℕ, deriv (F n) z = 1 / (z + ((n : ℂ) + 1)) ^ 2 := by
    intro n
    rw [hFalt n]
    have hne : z + ((n : ℂ) + 1) ≠ 0 := hterm_ne n z hzU
    have h1 : HasDerivAt (fun w : ℂ => w + ((n : ℂ) + 1)) 1 z := (hasDerivAt_id z).add_const _
    have h2 := h1.inv hne
    have h3 : HasDerivAt (fun w : ℂ => (w + ((n : ℂ) + 1))⁻¹)
        (-1 / (z + ((n : ℂ) + 1)) ^ 2) z := h2
    have h5 := h3.const_sub (1 / ((n : ℂ) + 1))
    have h6 : (fun w : ℂ => 1 / ((n : ℂ) + 1) - (w + ((n : ℂ) + 1))⁻¹)
        = fun w : ℂ => 1 / ((n : ℂ) + 1) - 1 / (w + ((n : ℂ) + 1)) := by
      funext w
      simp [one_div]
    rw [← h6]
    have h7 : HasDerivAt (fun w : ℂ => 1 / ((n : ℂ) + 1) - (w + ((n : ℂ) + 1))⁻¹)
        (1 / (z + ((n : ℂ) + 1)) ^ 2) z := by
      have heq : 1 / (z + ((n : ℂ) + 1)) ^ 2 = -(-1 / (z + ((n : ℂ) + 1)) ^ 2) := by
        ring
      rw [heq]
      exact h5
    exact h7.deriv
  have hγc : ∀ w : ℂ, w ∈ U → (∑' n : ℕ, F n w)
      = Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w := by
    intro w hw
    exact (Zeta23.DigammaSeries.hasSum_digamma_series (hUsub hw)).tsum_eq
  have hsum_eq : (fun w : ℂ => ∑' n : ℕ, F n w)
      =ᶠ[nhds z] fun w => Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact hγc w hw
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓan : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    exact (hUsub hw) ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hψan : AnalyticAt ℂ Complex.digamma z := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := hΓan.deriv
    have h2 := h1.div hΓan hΓne
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  have hψd : DifferentiableAt ℂ Complex.digamma z := hψan.differentiableAt
  have hinvd : HasDerivAt (fun w : ℂ => 1 / w) (-1 / z ^ 2) z := by
    have h1 := (hasDerivAt_id z).inv hz0
    have h2 : HasDerivAt (fun w : ℂ => w⁻¹) (-1 / z ^ 2) z := h1
    have h3 : (fun w : ℂ => 1 / w) = fun w : ℂ => w⁻¹ := by
      funext w
      rw [one_div]
    rw [h3]
    exact h2
  have hRHSd : HasDerivAt
      (fun w => Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w)
      (deriv Complex.digamma z + (-1 / z ^ 2)) z := by
    exact (hψd.hasDerivAt.add_const ((Real.eulerMascheroniConstant : ℝ) : ℂ)).add hinvd
  have hderiv_sum : deriv (fun w : ℂ => ∑' n : ℕ, F n w) z
      = deriv Complex.digamma z + (-1 / z ^ 2) := by
    rw [hsum_eq.deriv_eq]
    exact hRHSd.deriv
  rw [hderiv_sum] at hkey
  have hfun : (fun n : ℕ => deriv (F n) z)
      = fun n : ℕ => 1 / (z + ((n : ℂ) + 1)) ^ 2 := funext hderiv_term
  rw [hfun] at hkey
  
  have hshift : (fun n : ℕ => 1 / (z + ((n : ℂ) + 1)) ^ 2)
      = fun n : ℕ => (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) (n + 1) := by
    funext n
    simp only
    push_cast
    ring_nf
  rw [hshift] at hkey
  have h0 : (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) 0 = 1 / z ^ 2 := by
    simp
  have hfin := (hasSum_nat_add_iff (f := fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) 1).mp hkey
  have hval : deriv Complex.digamma z + -1 / z ^ 2
      + ∑ i ∈ Finset.range 1, (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) i
      = deriv Complex.digamma z := by
    rw [Finset.sum_range_one]
    have h00 : (1 : ℂ) / (z + ((0 : ℕ) : ℂ)) ^ 2 = 1 / z ^ 2 := by
      norm_num
    rw [h00]
    ring
  rwa [hval] at hfin

end Stirling

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- Module Zeta23.GammaFacts.Mu -/
section
noncomputable section

namespace Zeta23

namespace MuFields

open Complex Filter Topology

variable {a : ℝ}

set_option maxHeartbeats 1600000 in
lemma abscissa_mem (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ((a : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; exact ha0
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; exact ha1
    exact_mod_cast h
  omega

set_option maxHeartbeats 1600000 in
lemma re_term_eq (t : ℝ) (n : ℕ) :
    ((1 : ℂ) / ((n : ℂ) + 1) - 1 / (((a : ℂ) + Complex.I * t) + n + 1)).re
      = 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2) := by
  rw [Complex.sub_re]
  congr 1
  · rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) / ((((n : ℝ) + 1 : ℝ)) : ℂ) = ((((1 : ℝ) / ((n : ℝ) + 1)) : ℝ) : ℂ) by
        push_cast
        ring]
    exact Complex.ofReal_re _
  · rw [one_div, Complex.inv_re]
    have hre : (((a : ℂ) + Complex.I * t) + n + 1).re = (n : ℝ) + 1 + a := by
      simp
      ring
    have him : (((a : ℂ) + Complex.I * t) + n + 1).im = t := by simp
    rw [hre, Complex.normSq_apply, hre, him]
    ring

set_option maxHeartbeats 1600000 in
lemma re_inv_eq (t : ℝ) :
    ((1 : ℂ) / ((a : ℂ) + Complex.I * t)).re = a / (a ^ 2 + t ^ 2) := by
  rw [one_div, Complex.inv_re]
  have hre : ((a : ℂ) + Complex.I * t).re = a := by simp
  have him : ((a : ℂ) + Complex.I * t).im = t := by simp
  rw [hre, Complex.normSq_apply, hre, him]
  ring

set_option maxHeartbeats 1600000 in
lemma summable_re_terms (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hs := Zeta23.DigammaSeries.summable_digamma_series (abscissa_mem ha0 ha1 t)
  have hmap := hs.map Complex.reCLM Complex.continuous_re
  refine hmap.congr fun n => ?_
  exact re_term_eq t n

set_option maxHeartbeats 1600000 in
theorem re_digamma_vertical (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re
      = -Real.eulerMascheroniConstant - a / (a ^ 2 + t ^ 2)
        + ∑' n : ℕ,
          (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hmem := abscissa_mem ha0 ha1 t
  have h := Zeta23.DigammaSeries.digamma_series hmem
  have hre := congrArg Complex.re h
  rw [hre]
  rw [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  congr 1
  · congr 1
    exact re_inv_eq t
  · 
    have hs := Zeta23.DigammaSeries.summable_digamma_series hmem
    have hmap := Complex.reCLM.map_tsum hs
    rw [show (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))).re
      = Complex.reCLM (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))) from rfl, hmap]
    congr 1
    funext n
    exact re_term_eq t n

set_option maxHeartbeats 1600000 in
theorem re_digamma_mono (ha0 : 0 < a) (ha1 : a < 1) :
    MonotoneOn (fun t : ℝ => (Complex.digamma ((a : ℂ) + Complex.I * t)).re)
      (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  simp only
  rw [re_digamma_vertical ha0 ha1, re_digamma_vertical ha0 ha1]
  have ht1 : (0 : ℝ) ≤ t₁ := h₁
  have hsq : t₁ ^ 2 ≤ t₂ ^ 2 := by nlinarith
  have hmono1 : a / (a ^ 2 + t₂ ^ 2) ≤ a / (a ^ 2 + t₁ ^ 2) :=
    div_le_div_of_nonneg_left ha0.le (by positivity) (by linarith)
  have hterm : ∀ n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2))
        ≤ 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2) := by
    intro n
    have hna : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
    have h2 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2)
        ≤ ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2) :=
      div_le_div_of_nonneg_left hna.le (by positivity) (by linarith)
    linarith
  have hsum := (summable_re_terms ha0 ha1 t₁).tsum_le_tsum hterm
    (summable_re_terms ha0 ha1 t₂)
  linarith

set_option maxHeartbeats 1600000 in
lemma mu_eq (τ : ℝ) :
    Zeta23.mu τ = (1 / (2 * Real.pi))
        * (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
      - Real.log Real.pi / (2 * Real.pi) := by
  unfold Zeta23.mu
  congr 3
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem mu_monotoneOn : MonotoneOn Zeta23.mu (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  rw [mu_eq, mu_eq]
  have hmono := re_digamma_mono (a := 1 / 4) (by norm_num) (by norm_num)
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₁] : (0 : ℝ) ≤ t₁ / 2))
    (Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp h₂] : (0 : ℝ) ≤ t₂ / 2))
    (by linarith)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2π : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hmono h2π
  linarith

set_option maxHeartbeats 1600000 in
theorem mu_zero_le (τ : ℝ) : Zeta23.mu 0 ≤ Zeta23.mu τ := by
  have heven := Zeta23.mu_even
  rcases le_total 0 τ with h | h
  · exact mu_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
  · have h1 : Zeta23.mu τ = Zeta23.mu (-τ) := (heven τ).symm
    rw [h1]
    exact mu_monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)

set_option maxHeartbeats 1600000 in
theorem neg_one_lt_mu_zero : (-1 : ℝ) < Zeta23.mu 0 := by
  rw [mu_eq]
  rw [show ((0 : ℝ) / 2 : ℝ) = (0 : ℝ) by norm_num]
  have hre := re_digamma_vertical (a := 1 / 4) (by norm_num) (by norm_num) 0
  rw [hre]
  have hS : (0 : ℝ) ≤ ∑' n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)) := by
    refine tsum_nonneg fun n => ?_
    have hna : (0 : ℝ) < (n : ℝ) + 1 + 1 / 4 := by positivity
    have h1 : ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2)
        = 1 / ((n : ℝ) + 1 + 1 / 4) := by
      rw [show (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2) = ((n : ℝ) + 1 + 1 / 4) ^ 2 by ring]
      rw [sq]
      rw [div_mul_eq_div_div]
      rw [div_self hna.ne']
    rw [h1]
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : 1 / ((n : ℝ) + 1 + 1 / 4) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le h2 (by linarith)
    linarith
  have hγ : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ3 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have hlogπ : Real.log Real.pi < 1.4 := by
    have h1 : Real.log Real.pi < Real.log 4 := Real.log_lt_log Real.pi_pos hπ4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h3 := Real.log_two_lt_d9
    nlinarith
  have hquarter : (1 / 4 : ℝ) / ((1 / 4 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = 4 := by norm_num
  rw [hquarter]
  set S : ℝ := ∑' n : ℕ,
    (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + 1 / 4) / (((n : ℝ) + 1 + 1 / 4) ^ 2 + (0 : ℝ) ^ 2))
    with hSdef
  have hform : 1 / (2 * Real.pi) * (-Real.eulerMascheroniConstant - 4 + S)
        - Real.log Real.pi / (2 * Real.pi)
      = (-Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi) * (1 / (2 * Real.pi)) := by
    ring
  rw [hform]
  have hX : -(2 * Real.pi)
      < -Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi := by
    have hnorm : (1.4 : ℝ) = 14 / 10 := by norm_num
    linarith
  calc (-1 : ℝ) = -(2 * Real.pi) * (1 / (2 * Real.pi)) := by
        field_simp
    _ < (-Real.eulerMascheroniConstant - 4 + S - Real.log Real.pi) * (1 / (2 * Real.pi)) :=
        mul_lt_mul_of_pos_right hX (by positivity)

set_option maxHeartbeats 1600000 in
lemma trigamma_tail_le {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹ ≤ 12 / |t| := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htsq : (0 : ℝ) < t ^ 2 := by
    have := sq_abs t
    nlinarith
  set N : ℕ := ⌈|t|⌉₊ + 2 with hN
  have hNt : |t| ≤ (N : ℝ) := by
    calc |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (N : ℝ) := by
          rw [hN]
          push_cast
          linarith
  have hNle : (N : ℝ) ≤ |t| + 3 := by
    rw [hN]
    push_cast
    have := Nat.ceil_lt_add_one (abs_nonneg t)
    linarith
  have hsummable : Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ?_ ?_
    · have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at h3
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      nlinarith
  rw [← hsummable.sum_add_tsum_nat_add N]
  have hhead : ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ := by
    have h1 : ∀ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
      intro i _
      gcongr
      nlinarith [sq_nonneg ((1 / 4 : ℝ) + i)]
    calc ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ _i ∈ Finset.range N, (t ^ 2)⁻¹ := Finset.sum_le_sum h1
      _ = (N : ℝ) * (t ^ 2)⁻¹ := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
  have htail : ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ ((N : ℝ) - 1)⁻¹ := by
    have hN2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    push_cast
    refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun K => ?_
    have hterm : ∀ i : ℕ, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹ := by
      intro i
      have hiN1 : (1 : ℝ) ≤ (i : ℝ) + N - 1 := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        have := Nat.cast_nonneg (α := ℝ) i
        linarith
      have hpos1 : (0 : ℝ) < (i : ℝ) + N - 1 := by linarith
      have hpos2 : (0 : ℝ) < (i : ℝ) + N := by linarith
      have hsub : ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹
          = (((i : ℝ) + N - 1) * ((i : ℝ) + N))⁻¹ := by
        rw [inv_sub_inv hpos1.ne' hpos2.ne']
        ring_nf
      rw [hsub]
      have hd1 : (0 : ℝ) < ((i : ℝ) + N - 1) * ((i : ℝ) + N) := mul_pos hpos1 hpos2
      have hd2 : ((i : ℝ) + N - 1) * ((i : ℝ) + N)
          ≤ ((1 / 4 : ℝ) + ((i : ℝ) + (N : ℝ))) ^ 2 + t ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg t]
      have h3 := one_div_le_one_div_of_le hd1 hd2
      simpa [one_div] using h3
    calc ∑ i ∈ Finset.range K, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ i ∈ Finset.range K, (((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((N : ℝ) - 1)⁻¹ - ((K : ℝ) + N - 1)⁻¹ := by
          have htel := Finset.sum_range_sub' (f := fun i : ℕ => ((i : ℝ) + N - 1)⁻¹) K
          simp only [Nat.cast_zero, zero_add] at htel
          rw [← htel]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hx : (((i + 1 : ℕ) : ℝ) + N - 1)⁻¹ = ((i : ℝ) + N)⁻¹ := by
            push_cast
            ring_nf
          rw [hx]
      _ ≤ ((N : ℝ) - 1)⁻¹ := by
          have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          have : (0 : ℝ) < (K : ℝ) + N - 1 := by
            have := Nat.cast_nonneg (α := ℝ) K
            linarith
          have : (0 : ℝ) ≤ ((K : ℝ) + N - 1)⁻¹ := by positivity
          linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have h2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hNm1 : |t| ≤ (N : ℝ) - 1 := by
    rw [hN]
    push_cast
    have := Nat.le_ceil |t|
    linarith
  have htail2 : ((N : ℝ) - 1)⁻¹ ≤ |t|⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le ht0 hNm1
  have hhead2 : (N : ℝ) * (t ^ 2)⁻¹ ≤ 10 / |t| := by
    have hts : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [hts]
    rw [div_eq_mul_inv]
    have h1 : (N : ℝ) ≤ 7 * |t| := by linarith
    calc (N : ℝ) * ((|t| ^ 2)⁻¹) ≤ 7 * |t| * ((|t| ^ 2)⁻¹) := by
          gcongr
      _ = 7 * |t|⁻¹ := by
          field_simp
      _ ≤ 10 * |t|⁻¹ := by
          have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
          linarith
  calc (∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹)
        + ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ + ((N : ℝ) - 1)⁻¹ := add_le_add hhead htail
    _ ≤ 10 / |t| + |t|⁻¹ := add_le_add hhead2 htail2
    _ ≤ 12 / |t| := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
        linarith

set_option maxHeartbeats 1600000 in
lemma summable_quarter_line (t : ℝ) :
    Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ?_ ?_
  · have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
    have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
      funext n
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [heq] at h3
  · rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    nlinarith

set_option maxHeartbeats 1600000 in
theorem mu_deriv_bound : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv Zeta23.mu τ| ≤ C / |τ| := by
  refine ⟨24 / Real.pi, fun τ hτ => ?_⟩
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  set zA : ℂ := (1 / 4 : ℂ) + (Complex.I / 2) * (τ : ℂ) with hzA
  have hzA_eq : zA = ((1 / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ) := by
    rw [hzA]
    push_cast
    ring
  have hmem : zA ∈ Complex.integerComplement := by
    rw [hzA_eq]
    exact abscissa_mem (by norm_num) (by norm_num) (τ / 2)
  have hψd : DifferentiableAt ℂ Complex.digamma zA :=
    Zeta23.Stirling.differentiableAt_digamma hmem
  
  have hginner : HasDerivAt (fun x : ℝ => (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))
      (Complex.I / 2) τ := by
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 τ := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.const_mul (Complex.I / 2)).const_add ((1 / 4 : ℂ))
    simpa using h2
  have hcompd : HasDerivAt
      (fun x : ℝ => Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ)))
      ((Complex.I / 2) • deriv Complex.digamma zA) τ := by
    have h3 := HasDerivAt.scomp τ hψd.hasDerivAt hginner
    exact h3
  have hre : HasDerivAt
      (fun x : ℝ => (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re)
      (((Complex.I / 2) • deriv Complex.digamma zA).re) τ :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hcompd)
  have hmuD : HasDerivAt Zeta23.mu
      (1 / (2 * Real.pi) * (((Complex.I / 2) • deriv Complex.digamma zA).re)) τ := by
    have h4 := (hre.const_mul (1 / (2 * Real.pi))).sub_const (Real.log Real.pi / (2 * Real.pi))
    have h5 : Zeta23.mu = fun x : ℝ =>
        1 / (2 * Real.pi) * (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re
          - Real.log Real.pi / (2 * Real.pi) := by
      funext x
      unfold Zeta23.mu
      rw [show ((1 / 4 : ℂ) + Complex.I * (x : ℂ) / 2)
          = (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ) from by ring]
    rw [h5]
    exact h4
  rw [hmuD.deriv]
  
  have htri := Zeta23.Stirling.hasSum_trigamma hmem
  have hnorm_term : ∀ n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖
      = (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
    intro n
    have hre2 : (zA + n).re = (1 / 4 : ℝ) + n := by
      rw [hzA_eq]
      simp
    have him2 : (zA + n).im = τ / 2 := by
      rw [hzA_eq]
      simp
    rw [norm_div, norm_one, norm_pow, one_div]
    congr 1
    rw [show ‖zA + (n : ℂ)‖ ^ 2 = Complex.normSq (zA + n) from Complex.sq_norm _,
      Complex.normSq_apply, hre2, him2]
    ring
  have hsummable_norm : Summable (fun n : ℕ => ‖(1 : ℂ) / (zA + n) ^ 2‖) := by
    refine (summable_quarter_line (τ / 2)).congr fun n => ?_
    exact (hnorm_term n).symm
  have hψ'bound : ‖deriv Complex.digamma zA‖ ≤ 24 / |τ| := by
    have h6 : deriv Complex.digamma zA = ∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2 := htri.tsum_eq.symm
    rw [h6]
    calc ‖∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsummable_norm
      _ = ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
          congr 1
          funext n
          exact hnorm_term n
      _ ≤ 12 / |τ / 2| := trigamma_tail_le (by
          rw [abs_div]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          linarith)
      _ = 24 / |τ| := by
          rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
          field_simp
          norm_num
  
  have hval : |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ ‖deriv Complex.digamma zA‖ / 2 := by
    calc |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
        ≤ ‖(Complex.I / 2) • deriv Complex.digamma zA‖ := Complex.abs_re_le_norm _
      _ = ‖Complex.I / 2‖ * ‖deriv Complex.digamma zA‖ := norm_smul _ _
      _ = ‖deriv Complex.digamma zA‖ / 2 := by
          rw [norm_div, Complex.norm_I]
          rw [show ‖(2 : ℂ)‖ = 2 from by
            rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (by norm_num)]]
          ring
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ 1 / (2 * Real.pi) * (‖deriv Complex.digamma zA‖ / 2) := by
        gcongr
    _ ≤ 1 / (2 * Real.pi) * ((24 / |τ|) / 2) := by
        gcongr
    _ ≤ (24 / Real.pi) / |τ| := by
        rw [div_div, div_mul_eq_mul_div, one_mul]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        have e1 : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ hπ.ne'
        have e2 : |τ| * |τ|⁻¹ = 1 := mul_inv_cancel₀ hτ0.ne'
        nlinarith [e1, e2]

end MuFields

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.GammaFacts.IntMu -/
section
noncomputable section

namespace Zeta23

namespace MuInts

open MeasureTheory intervalIntegral

def StirlingHyp : Prop := ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
  |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2

set_option maxHeartbeats 1600000 in
lemma integral_main_eq {T : ℝ} (hT : 0 < T) :
    ∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))
      = T * ell1 T / (2 * Real.pi) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hftc : ∀ τ ∈ Set.uIcc T (2 * T),
      HasDerivAt (fun x : ℝ => (1 / (2 * Real.pi)) * (x * Real.log (x / (2 * Real.pi)) - x))
        ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith)] at hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) τ :=
      (hasDerivAt_id τ).div_const _
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)))
        (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) τ := by
      have h3 := (Real.hasDerivAt_log (by positivity : τ / (2 * Real.pi) ≠ 0)).comp τ h1
      have heq : 1 / (2 * Real.pi) / (τ / (2 * Real.pi))
          = (τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) := by ring
      rw [heq]
      exact h3
    have h4 : HasDerivAt (fun x : ℝ => x * Real.log (x / (2 * Real.pi)))
        (Real.log (τ / (2 * Real.pi)) + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi)))) τ := by
      have h4a := (hasDerivAt_id τ).mul h2
      have heq : Real.log (τ / (2 * Real.pi)) + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi)))
          = 1 * Real.log (τ / (2 * Real.pi))
            + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) := by ring
      rw [heq]
      exact h4a
    have h5 := (h4.sub (hasDerivAt_id τ)).const_mul (1 / (2 * Real.pi))
    have hτne : τ ≠ 0 := hτ0.ne'
    have heq : (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))
        = 1 / (2 * Real.pi) * (Real.log (τ / (2 * Real.pi))
            + τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) - 1) := by
      have hmul : τ * (1 / (2 * Real.pi) / (τ / (2 * Real.pi))) = 1 := by
        field_simp
      rw [hmul]
      ring
    rw [heq]
    exact h5
  have hcont : IntervalIntegrable
      (fun τ : ℝ => (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    refine ContinuousOn.mul continuousOn_const ?_
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    exact ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hftc hcont]
  have h2T : Real.log (2 * T / (2 * Real.pi)) = Real.log 2 + Real.log (T / (2 * Real.pi)) := by
    rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [h2T]
  unfold ell1 l
  field_simp
  ring

set_option maxHeartbeats 1600000 in
theorem int_mu_of_stirling (hst : StirlingHyp) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T := by
  obtain ⟨C, hC⟩ := hst
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hμcont : Continuous Zeta23.mu := Zeta23.mu_smooth.continuous
  refine ⟨C, 1, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  
  have hint_mu : IntervalIntegrable Zeta23.mu volume T (2 * T) :=
    hμcont.intervalIntegrable _ _
  have hint_main : IntervalIntegrable
      (fun τ : ℝ => (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    refine ContinuousOn.mul continuousOn_const ?_
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).continuousWithinAt
  have hsplit : (∫ τ in T..(2 * T), Zeta23.mu τ)
      = (∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
        + ∫ τ in T..(2 * T),
            (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
    rw [← intervalIntegral.integral_add hint_main (hint_mu.sub hint_main)]
    congr 1
    funext τ
    ring
  rw [hsplit, integral_main_eq hT0]
  rw [add_sub_cancel_left]
  
  have herr_int : IntervalIntegrable
      (fun τ : ℝ => Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      volume T (2 * T) := hint_mu.sub hint_main
  have hbound : ∀ τ ∈ Set.Icc T (2 * T),
      |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C / τ ^ 2 := by
    intro τ hτ
    have hτ1 : (1 : ℝ) ≤ τ := le_trans hT hτ.1
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have h := hC τ (by rwa [habs])
    rwa [habs] at h
  have hCtau : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact (continuousAt_const.div (continuousAt_pow _ _) (by positivity)).continuousWithinAt
  have hCint : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have hftc2 : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ := (hasDerivAt_id τ).inv hτ0.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : C / τ ^ 2 = -C * (-1 / τ ^ 2) := by ring
      rw [heq]
      exact h1
    rw [integral_eq_sub_of_hasDerivAt hftc2 hCtau]
    field_simp
    ring
  calc |∫ τ in T..(2 * T),
        (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))|
      ≤ ∫ τ in T..(2 * T),
          |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith) herr_int.abs hCtau ?_
        intro τ hτ
        exact hbound τ hτ
    _ = C / (2 * T) := hCint
    _ ≤ C / T := by
        have h2 : (0 : ℝ) < 2 * T := by linarith
        rw [div_le_div_iff₀ h2 hT0]
        nlinarith

set_option maxHeartbeats 1600000 in
lemma integral_main_sq_eq {T : ℝ} (hT : 0 < T) :
    ∫ τ in T..(2 * T), Real.log (τ / (2 * Real.pi)) ^ 2
      = T * (ell1 T ^ 2 + 1 - 2 * Real.log 2 ^ 2) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hftc : ∀ τ ∈ Set.uIcc T (2 * T),
      HasDerivAt (fun x : ℝ =>
          x * (Real.log (x / (2 * Real.pi)) ^ 2 - 2 * Real.log (x / (2 * Real.pi)) + 2))
        (Real.log (τ / (2 * Real.pi)) ^ 2) τ := by
    intro τ hτ
    rw [Set.uIcc_of_le (by linarith)] at hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) τ :=
      (hasDerivAt_id τ).div_const _
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi))) (1 / τ) τ := by
      have h3 := (Real.hasDerivAt_log (by positivity : τ / (2 * Real.pi) ≠ 0)).comp τ h1
      have heq : 1 / τ = (τ / (2 * Real.pi))⁻¹ * (1 / (2 * Real.pi)) := by
        rw [inv_div]
        field_simp
      rw [heq]
      exact h3
    have h4 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
        (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ)) τ := by
      have h5 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)) ^ 2)
          ((2 : ℕ) * Real.log (τ / (2 * Real.pi)) ^ (2 - 1) * (1 / τ)) τ := h2.pow 2
      convert h5 using 1
      norm_num
    have h6 : HasDerivAt (fun x : ℝ =>
        Real.log (x / (2 * Real.pi)) ^ 2 - 2 * Real.log (x / (2 * Real.pi)) + 2)
        (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ) - 2 * (1 / τ)) τ := by
      have h7 := (h4.sub (h2.const_mul 2)).add_const 2
      exact h7
    have h8 := (hasDerivAt_id τ).mul h6
    have hτne : τ ≠ 0 := hτ0.ne'
    have heq : Real.log (τ / (2 * Real.pi)) ^ 2
        = 1 * (Real.log (τ / (2 * Real.pi)) ^ 2 - 2 * Real.log (τ / (2 * Real.pi)) + 2)
          + τ * (2 * Real.log (τ / (2 * Real.pi)) * (1 / τ) - 2 * (1 / τ)) := by
      field_simp
      ring
    rw [heq]
    exact h8
  have hcont : IntervalIntegrable
      (fun τ : ℝ => Real.log (τ / (2 * Real.pi)) ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT hτ.1
    exact (((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).pow 2).continuousWithinAt
  rw [integral_eq_sub_of_hasDerivAt hftc hcont]
  have h2T : Real.log (2 * T / (2 * Real.pi)) = Real.log 2 + Real.log (T / (2 * Real.pi)) := by
    rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [h2T]
  unfold ell1 l
  ring

set_option maxHeartbeats 1600000 in
theorem int_mu_sq_of_stirling (hst : StirlingHyp) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by
  obtain ⟨C, hC⟩ := hst
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hμcont : Continuous Zeta23.mu := Zeta23.mu_smooth.continuous
  set C₂ : ℝ := C * (1 + C) + 1 with hC₂
  have hC₂0 : (0 : ℝ) < C₂ := by nlinarith
  refine ⟨8 * (1 + 2 * Real.log 2 ^ 2) + 1,
    max (2 * Real.pi * Real.exp 4) (32 * Real.pi ^ 2 * C₂), fun T hT => ?_⟩
  set m : ℝ := Real.log 2 with hm
  have hm0 : (0 : ℝ) < m := Real.log_pos (by norm_num)
  have hm1 : m < 1 := by
    rw [hm]
    have := Real.log_two_lt_d9
    linarith
  have hT1 : 2 * Real.pi * Real.exp 4 ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : 32 * Real.pi ^ 2 * C₂ ≤ T := le_trans (le_max_right _ _) hT
  have hexp1 : (1 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hT0 : (0 : ℝ) < T := by nlinarith [Real.exp_pos (4 : ℝ)]
  have hL4 : (4 : ℝ) ≤ l T := by
    unfold l
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    apply Real.log_le_log (Real.exp_pos 4)
    rw [le_div_iff₀ (by positivity)]
    linarith
  set L : ℝ := l T with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hL_le_T : L ≤ T := by
    rw [hLdef]
    unfold l
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / (2 * Real.pi))
    have h2 : T / (2 * Real.pi) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    linarith
  have hell : ell1 T = L + 2 * m - 1 := by
    unfold ell1
    rw [← hLdef, ← hm]
  have hell_pos : (0 : ℝ) < ell1 T := by
    rw [hell]
    nlinarith
  have hell_ge : L / 2 ≤ ell1 T := by
    rw [hell]
    nlinarith
  have hell2 : L ^ 2 / 4 ≤ ell1 T ^ 2 := by
    nlinarith [hell_ge, hL0, hell_pos]
  have hmain_bound : ∀ τ ∈ Set.Icc T (2 * T),
      |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ (L + m) / (2 * Real.pi) := by
    intro τ hτ
    have hτT : T ≤ τ := hτ.1
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτT
    have hlog_nonneg : (0 : ℝ) ≤ Real.log (τ / (2 * Real.pi)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hlog_le : Real.log (τ / (2 * Real.pi)) ≤ L + m := by
      have h1 : Real.log (τ / (2 * Real.pi)) ≤ Real.log (2 * T / (2 * Real.pi)) := by
        apply Real.log_le_log (by positivity)
        gcongr
        exact hτ.2
      have h2 : Real.log (2 * T / (2 * Real.pi)) = m + L := by
        rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
          Real.log_mul (by norm_num) (by positivity), hm, hLdef]
        rfl
      linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)),
      abs_of_nonneg hlog_nonneg]
    rw [one_div, div_eq_mul_inv (L + m), mul_comm (L + m)]
    exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
  have herr_bound : ∀ τ ∈ Set.Icc T (2 * T),
      |Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2|
        ≤ C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    intro τ hτ
    have hτT : T ≤ τ := hτ.1
    have hτ1 : (1 : ℝ) ≤ τ := by nlinarith
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have herr := hC τ (by rwa [habs])
    rw [habs] at herr
    have hmb := hmain_bound τ hτ
    have hsq : Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
        = (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
          * (Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
      ring
    rw [hsq, abs_mul]
    have hτ2 : (0 : ℝ) < τ ^ 2 := by positivity
    have hCτ : C / τ ^ 2 ≤ C := by
      rw [div_le_iff₀ hτ2]
      have hτsq1 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith
      nlinarith
    have hsum_bound : |Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
        ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by
      have h4 := abs_sub_abs_le_abs_sub (Zeta23.mu τ)
        ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      have h5 : |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C :=
        le_trans herr hCτ
      have h3 : |Zeta23.mu τ| ≤ (L + m) / (2 * Real.pi) + C := by linarith
      calc |Zeta23.mu τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
          ≤ |Zeta23.mu τ| + |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
            abs_add_le _ _
        _ ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by linarith
    exact mul_le_mul herr hsum_bound (abs_nonneg _) (by positivity)
  have hint_mu2 : IntervalIntegrable (fun τ : ℝ => Zeta23.mu τ ^ 2) volume T (2 * T) :=
    (hμcont.pow 2).intervalIntegrable _ _
  have hint_main2 : IntervalIntegrable
      (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
      volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.mul ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _))).pow 2).continuousWithinAt
  have hCtau2 : IntervalIntegrable
      (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.div (continuousAt_pow _ _) (by positivity)).mul
      continuousAt_const).continuousWithinAt
  have hmain2 : ∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
      = (1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2)) := by
    rw [show (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        = fun τ : ℝ => (1 / (4 * Real.pi ^ 2)) * Real.log (τ / (2 * Real.pi)) ^ 2
      from funext fun τ => by field_simp; ring]
    rw [intervalIntegral.integral_const_mul, integral_main_sq_eq hT0, hm]
  have hsplit : (∫ τ in T..(2 * T), Zeta23.mu τ ^ 2)
      = (∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        + ∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2) := by
    rw [← intervalIntegral.integral_add hint_main2 (hint_mu2.sub hint_main2)]
    congr 1
    funext τ
    ring
  have hCint : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have hftc2 : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ :=
        (hasDerivAt_id τ).inv hτ0.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : C / τ ^ 2 = -C * (-1 / τ ^ 2) := by ring
      rw [heq]
      exact h1
    have hCtau : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      intro τ hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      exact (continuousAt_const.div (continuousAt_pow _ _)
        (by positivity)).continuousWithinAt
    rw [integral_eq_sub_of_hasDerivAt hftc2 hCtau]
    field_simp
    ring
  have herrI : |∫ τ in T..(2 * T),
      (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
      ≤ (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    have hCint2 : ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)
        = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
      rw [show (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C))
          = fun τ : ℝ => (2 * ((L + m) / (2 * Real.pi)) + C) * (C / τ ^ 2)
        from funext fun τ => by ring]
      rw [intervalIntegral.integral_const_mul, hCint]
      ring
    calc |∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
        ≤ ∫ τ in T..(2 * T),
            |Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs (by linarith)
      _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hint_mu2.sub hint_main2).abs hCtau2 ?_
          intro τ hτ
          exact herr_bound τ hτ
      _ = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := hCint2
  rw [hsplit, hmain2]
  set X : ℝ := T * ell1 T ^ 2 / (4 * Real.pi ^ 2) / L ^ 2 with hX
  have hX1 : T / (16 * Real.pi ^ 2) ≤ X := by
    rw [hX, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hell2, hT0.le, sq_nonneg L, mul_pos hT0 (mul_pos hπ hπ)]
  have hX0 : (0 : ℝ) < X := by
    rw [hX]
    positivity
  have htri : |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
          - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
    have h1 := abs_add_le
      ((1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2))
      (∫ τ in T..(2 * T),
        (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
    calc |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        + (∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        = |((1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
            - T * ell1 T ^ 2 / (4 * Real.pi ^ 2))
          + ∫ τ in T..(2 * T),
              (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
          congr 1
          ring
      _ ≤ _ := h1
  have hmain_dev : |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ 8 * (1 + 2 * m ^ 2) * X := by
    have h1 : (1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2) = T * (1 - 2 * m ^ 2) / (4 * Real.pi ^ 2) := by
      ring
    rw [h1, abs_div, abs_mul, abs_of_pos hT0,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2)]
    have habs1 : |1 - 2 * m ^ 2| ≤ 1 + 2 * m ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg m]
    calc T * |1 - 2 * m ^ 2| / (4 * Real.pi ^ 2)
        ≤ T * (1 + 2 * m ^ 2) / (4 * Real.pi ^ 2) := by gcongr
      _ = 4 * (1 + 2 * m ^ 2) * (T / (16 * Real.pi ^ 2)) := by ring
      _ ≤ 4 * (1 + 2 * m ^ 2) * X := by
          gcongr
      _ ≤ 8 * (1 + 2 * m ^ 2) * X := by nlinarith [hX0, sq_nonneg m]
  have herr_final : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ 1 * X := by
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hb1 : 2 * ((L + m) / (2 * Real.pi)) ≤ L := by
      have h2a : (L + m) / (2 * Real.pi) ≤ (L + 1) / (2 * Real.pi) := by
        gcongr
      have h2b : (L + 1) / (2 * Real.pi) ≤ (L + 1) / 6 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)
      have h3 : (L + 1) / 6 ≤ L / 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
    have hb2 : 2 * ((L + m) / (2 * Real.pi)) + C ≤ (1 + C) * L := by
      have h4 : C ≤ C * L := by nlinarith
      nlinarith
    have hb3 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ C₂ * L / T := by
      have h5 : (0 : ℝ) ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by positivity
      have h6 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := by
        apply mul_le_mul_of_nonneg_left hb2 (by positivity)
      calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := h6
        _ = (C * (1 + C)) * L / (2 * T) := by ring
        _ ≤ C₂ * L / T := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            have h7 : (0 : ℝ) ≤ C * (1 + C) := by nlinarith
            nlinarith [mul_nonneg (mul_nonneg h7 hL0.le) hT0.le, hL0.le, hT0.le]
    have hb4 : C₂ * L / T ≤ C₂ := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have hb5 : C₂ ≤ T / (32 * Real.pi ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hb6 : T / (32 * Real.pi ^ 2) ≤ T / (16 * Real.pi ^ 2) := by
      apply div_le_div_of_nonneg_left hT0.le (by positivity)
      nlinarith
    rw [one_mul]
    calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
        ≤ C₂ * L / T := hb3
      _ ≤ C₂ := hb4
      _ ≤ T / (32 * Real.pi ^ 2) := hb5
      _ ≤ T / (16 * Real.pi ^ 2) := hb6
      _ ≤ X := hX1
  calc |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
          - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (Zeta23.mu τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := htri
    _ ≤ 8 * (1 + 2 * m ^ 2) * X + 1 * X := by
        have := le_trans herrI herr_final
        linarith [hmain_dev]
    _ = (8 * (1 + 2 * m ^ 2) + 1) * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / L ^ 2 := by
        rw [hX]
        ring

end MuInts

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.GammaFacts.StirlingVert -/
section
noncomputable section

namespace Zeta23

namespace StirlingVert

open Complex Filter Topology MeasureTheory intervalIntegral Set

set_option maxHeartbeats 1600000 in
theorem intervalIntegral_mul_const_C (c : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
  intervalIntegral.integral_mul_const c f

set_option maxHeartbeats 1600000 in
theorem abs_im_le_norm_add {w : ℂ} (x : ℝ) : |w.im| ≤ ‖(x : ℂ) + w‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + w)
  simpa using this

set_option maxHeartbeats 1600000 in
theorem re_add_pos {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ((x : ℂ) + w).re := by
  simp; linarith

set_option maxHeartbeats 1600000 in
theorem add_mem_slitPlane {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_add_pos hw hx))

set_option maxHeartbeats 1600000 in
theorem add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
  fun h => by have := re_add_pos hw hx; rw [h] at this; simp at this

set_option maxHeartbeats 1600000 in
theorem hasDerivAt_log_add {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.log (z + w)) (((x : ℂ) + w)⁻¹) (x : ℂ) := by
    have := (Complex.hasDerivAt_log (add_mem_slitPlane hw hx)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const w)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal

set_option maxHeartbeats 1600000 in
theorem integral_inv_add_eq_log_sub {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = Complex.log (((m + 1 : ℝ) : ℂ) + w) - Complex.log ((m : ℂ) + w) := by
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + w)⁻¹) (uIcc m (m + 1)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact add_ne_zero hw (by linarith [hx.1])
  rw [integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Complex.log ((y : ℂ) + w))
    (fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx
      exact hasDerivAt_log_add hw (by linarith [hx.1]))
    (hcont.intervalIntegrable)]

set_option maxHeartbeats 1600000 in
theorem inv_add_expand {w : ℂ} {x m : ℝ} (hxw : (x : ℂ) + w ≠ 0) (hmw : (m : ℂ) + w ≠ 0) :
    ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w)) := by
  field_simp
  push_cast
  ring

def eps (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))

set_option maxHeartbeats 1600000 in
theorem integral_inv_add_eq {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = ((m : ℂ) + w)⁻¹ - (1 / 2 : ℂ) / ((m : ℂ) + w) ^ 2 + eps w m := by
  have hmw := add_ne_zero hw hm
  have hcongr : ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹ = ∫ x in m..(m + 1),
      (((m : ℂ) + w)⁻¹ - ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
        + ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) := by
    apply integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact inv_add_expand (add_ne_zero hw (by linarith [hx.1])) hmw
  rw [hcongr]
  have hI : ∀ {f : ℝ → ℂ}, Continuous f → IntervalIntegrable f volume m (m + 1) :=
    fun hf => hf.intervalIntegrable _ _
  have hR : IntervalIntegrable (fun x : ℝ =>
      ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))) volume m (m + 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
  have hmid : ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2
      = ((1 / 2 : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
    have e : (fun x : ℝ => ((x - m : ℝ) : ℂ) / ((m : ℂ) + w) ^ 2)
        = fun x : ℝ => ((x - m : ℝ) : ℂ) * ((((m : ℂ) + w) ^ 2)⁻¹) := by
      funext x; rw [div_eq_mul_inv]
    rw [e, intervalIntegral_mul_const_C, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_comp_sub_right (fun u : ℝ => u) m]
    simp only [sub_self, add_sub_cancel_left, integral_id]
    norm_num
  rw [integral_add ((hI (by fun_prop)).sub (hI (by fun_prop))) hR,
    integral_sub (hI (by fun_prop)) (hI (by fun_prop)), intervalIntegral.integral_const, hmid,
    show m + 1 - m = (1 : ℝ) by ring, one_smul]
  unfold eps
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem norm_eps_le {w : ℂ} (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
  have hmw := add_ne_zero hw hm
  have hM : 0 < ‖(m : ℂ) + w‖ := norm_pos_iff.mpr hmw
  have ht0 : 0 < |w.im| := by linarith
  unfold eps
  calc ‖∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..(m + 1), ‖((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..(m + 1), (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop : Continuous fun x : ℝ => (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|))
            |>.intervalIntegrable _ _
        · intro x hx
          have hx0 : 0 ≤ x := by linarith [hx.1]
          have hxw : |w.im| ≤ ‖(x : ℂ) + w‖ := abs_im_le_norm_add x
          rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _ = 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
        simp only [sub_self, add_sub_cancel_left, integral_pow]
        norm_num
        field_simp

section Seq

variable {w : ℂ}

set_option maxHeartbeats 1600000 in
theorem natp1_re_pos (hw : 0 < w.re) (n : ℕ) : 0 < ((n : ℂ) + 1 + w).re := by
  simp; positivity

set_option maxHeartbeats 1600000 in
theorem natp1_ne_zero (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := fun h => by
  have := natp1_re_pos hw n; rw [h] at this; simp at this

set_option maxHeartbeats 1600000 in
theorem natp1_le_norm (hw : 0 < w.re) (n : ℕ) : (n : ℝ) + 1 ≤ ‖(n : ℂ) + 1 + w‖ := by
  have h := Complex.re_le_norm ((n : ℂ) + 1 + w)
  simp at h; linarith

set_option maxHeartbeats 1600000 in
theorem inv_natp1_eq (hw : 0 < w.re) (n : ℕ) :
    ((n : ℂ) + 1 + w)⁻¹
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) / ((n : ℂ) + 1 + w) ^ 2 - eps w ((n : ℝ) + 1) := by
  have hm : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h1 := integral_inv_add_eq hw hm
  have h2 := integral_inv_add_eq_log_sub hw hm
  rw [h2] at h1
  have e1 : ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w := by push_cast; ring
  have e2 : ((((n : ℝ) + 1 + 1 : ℝ)) : ℂ) + w = ((n + 1 : ℕ) : ℂ) + 1 + w := by push_cast; ring
  rw [e1, e2] at h1
  linear_combination (-1 : ℂ) * h1

def rho (w : ℂ) (n : ℕ) : ℂ := 1 / (((n : ℂ) + 1 + w) ^ 2 * ((n : ℂ) + 2 + w))

set_option maxHeartbeats 1600000 in
theorem inv_natp1_sq_eq (hw : 0 < w.re) (n : ℕ) :
    1 / ((n : ℂ) + 1 + w) ^ 2
      = (((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n := by
  have h1 := natp1_ne_zero hw n
  have h2 := natp1_ne_zero hw (n + 1)
  have e : ((n + 1 : ℕ) : ℂ) + 1 + w = (n : ℂ) + 2 + w := by push_cast; ring
  rw [e] at h2 ⊢
  unfold rho
  field_simp
  ring

set_option maxHeartbeats 1600000 in
theorem norm_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖rho w n‖ ≤ 1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have h1 := natp1_ne_zero hw n
  have hn2 : |w.im| ≤ ‖(n : ℂ) + 2 + w‖ := by
    have := Complex.abs_im_le_norm ((n : ℂ) + 2 + w); simpa using this
  have ht0 : 0 < |w.im| := by linarith
  unfold rho
  rw [norm_div, norm_one, norm_mul, norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  exact mul_le_mul_of_nonneg_left hn2 (by positivity)

set_option maxHeartbeats 1600000 in
theorem norm_eps_natp1_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have := norm_eps_le hw ht (m := (n : ℝ) + 1) (by positivity)
  rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w by push_cast; ring] at this
  exact this

set_option maxHeartbeats 1600000 in
theorem partial_sum_eq (hw : 0 < w.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
      = (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
        - (Complex.log ((N : ℂ) + 1 + w) - Complex.log ((0 : ℕ) + 1 + w : ℂ))
        - (1 / 2 : ℂ) * (((0 : ℕ) + 1 + w : ℂ)⁻¹ - ((N : ℂ) + 1 + w)⁻¹
            + ∑ n ∈ Finset.range N, rho w n)
        + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
  rw [Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.range N, (1 : ℂ) / (w + n + 1)
      = (Complex.log (((n + 1 : ℕ) : ℂ) + 1 + w) - Complex.log ((n : ℂ) + 1 + w))
        + (1 / 2 : ℂ) * ((((n : ℂ) + 1 + w)⁻¹ - (((n + 1 : ℕ) : ℂ) + 1 + w)⁻¹) + rho w n)
        - eps w ((n : ℝ) + 1) := by
    intro n _
    have A := inv_natp1_eq hw n
    have B := inv_natp1_sq_eq hw n
    rw [show (1 : ℂ) / (w + n + 1) = ((n : ℂ) + 1 + w)⁻¹ by rw [one_div]; ring_nf]
    linear_combination A + (1 / 2 : ℂ) * B
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_range_sub (fun n => Complex.log ((n : ℂ) + 1 + w)) N, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_range_sub' (fun n => ((n : ℂ) + 1 + w)⁻¹) N]
  push_cast
  ring

set_option maxHeartbeats 1600000 in
theorem norm_sq_natp1_ge (hw : 0 < w.re) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 + w.im ^ 2 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((n : ℂ) + 1 + w).re = (n : ℝ) + 1 + w.re := by simp
  have him : ((n : ℂ) + 1 + w).im = w.im := by simp
  rw [hre, him]
  nlinarith

set_option maxHeartbeats 1600000 in
theorem inv_norm_sq_le_telescope (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) := by
  have h1 := norm_sq_natp1_ge hw n
  have ht0 : 0 < |w.im| := by linarith
  have hpos : 0 < ((n : ℝ) + 1) ^ 2 + w.im ^ 2 := by positivity
  have htele : 1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)
      = 1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|)) := by
    field_simp; ring
  rw [htele]
  have hsq : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  calc 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / (((n : ℝ) + 1) ^ 2 + w.im ^ 2) :=
        div_le_div_of_nonneg_left zero_le_one hpos h1
    _ ≤ 2 * (1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|))) := by
        rw [hsq, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ) + 1 - |w.im|)]

set_option maxHeartbeats 1600000 in
theorem sum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| := by
  have ht0 : 0 < |w.im| := by linarith
  calc ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2
      ≤ ∑ n ∈ Finset.range N, 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) :=
        Finset.sum_le_sum fun n _ => inv_norm_sq_le_telescope hw ht n
    _ = 2 * (1 / |w.im| - 1 / ((N : ℝ) + |w.im|)) := by
        rw [← Finset.mul_sum, Finset.sum_congr rfl (fun (i : ℕ) _ => by
          rw [show ((i : ℝ) + 1 + |w.im|) = (((i + 1 : ℕ) : ℝ) + |w.im|) by push_cast; ring]),
          Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + |w.im|)) N]
        push_cast
        ring
    _ ≤ 2 / |w.im| := by
        have : 0 ≤ 1 / ((N : ℝ) + |w.im|) := by positivity
        rw [div_eq_mul_one_div 2]
        linarith

set_option maxHeartbeats 1600000 in
theorem summable_inv_norm_sq (hw : 0 < w.re) :
    Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_left₀ (by positivity) (natp1_le_norm hw n) 2)

set_option maxHeartbeats 1600000 in
theorem summable_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (rho w) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / |w.im|)) fun n => ?_
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem summable_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => eps w ((n : ℝ) + 1)) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
    fun n => ?_
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem summable_norm_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (fun n => ‖rho w n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / |w.im|))
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem summable_norm_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp

set_option maxHeartbeats 1600000 in
theorem tsum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_inv_norm_sq_le hw ht)

set_option maxHeartbeats 1600000 in
theorem norm_tsum_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n, rho w n‖ ≤ 2 / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ := norm_tsum_le_tsum_norm (summable_norm_rho hw ht)
    _ ≤ ∑' n : ℕ, (1 / |w.im|) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_rho hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / |w.im|) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / |w.im|) * (2 / |w.im|) := by gcongr
    _ = 2 / w.im ^ 2 := by rw [← sq_abs]; field_simp

set_option maxHeartbeats 1600000 in
theorem norm_tsum_eps_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (2 / 3) / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
        norm_tsum_le_tsum_norm (summable_norm_eps hw ht)
    _ ≤ ∑' n : ℕ, (1 / (3 * |w.im|)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eps hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / (3 * |w.im|)) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * |w.im|)) * (2 / |w.im|) := by gcongr
    _ = (2 / 3) / w.im ^ 2 := by rw [← sq_abs]; field_simp

set_option maxHeartbeats 1600000 in
theorem tendsto_harmonic_sub_clog (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  
  have hdecomp : ∀ N : ℕ, (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)
      = (((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ)
        - Complex.log (1 + w / ((N : ℂ) + 1)) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN1 : (N : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have hq' : 1 + w / ((N : ℂ) + 1) = ((N : ℂ) + 1 + w) / ((N : ℂ) + 1) := by
      field_simp
    have hq : 1 + w / ((N : ℂ) + 1) ≠ 0 := by
      rw [hq']; exact div_ne_zero (natp1_ne_zero hw N) hN1
    have hlog : Complex.log ((N : ℂ) + 1 + w)
        = Real.log ((N : ℝ) + 1) + Complex.log (1 + w / ((N : ℂ) + 1)) := by
      rw [← Complex.log_ofReal_mul hN hq, hq']
      congr 1
      push_cast
      field_simp
    rw [hlog, Zeta23.DigammaSeries.harmonic_cast_eq]
    push_cast
    ring
  simp_rw [hdecomp]
  have h1 : Tendsto (fun N : ℕ => ((((harmonic N : ℚ) : ℝ) - Real.log ((N : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log_add_one
  have h2 : Tendsto (fun N : ℕ => Complex.log (1 + w / ((N : ℂ) + 1))) atTop (𝓝 0) := by
    have hq : Tendsto (fun N : ℕ => w / ((N : ℂ) + 1)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun N : ℕ => ‖w / ((N : ℂ) + 1)‖) = fun N : ℕ => ‖w‖ * (1 / ((N : ℝ) + 1)) := by
        funext N
        rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring
      rw [this]
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖w‖
    have hcont : ContinuousAt Complex.log 1 := continuousAt_clog (by simp)
    have := hcont.tendsto.comp (by simpa using hq.const_add 1)
    simpa [Function.comp_def] using this
  simpa using h1.sub h2

set_option maxHeartbeats 1600000 in
theorem tendsto_inv_natp1 (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1 + w)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N => norm_nonneg _) (fun N => ?_)
  rw [norm_inv]
  have h := natp1_le_norm hw N
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h

set_option maxHeartbeats 1600000 in
theorem digamma_eq (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hk
    simp at this
    rw [← this] at ht; simp at ht; linarith
  have hL := (Zeta23.DigammaSeries.hasSum_digamma_series hmem).tendsto_sum_nat
  
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)))
      atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
        - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
        = ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + w))
          + Complex.log (1 + w)
          - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹ + ∑ n ∈ Finset.range N, rho w n)
          + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
      intro N
      rw [partial_sum_eq hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((tendsto_harmonic_sub_clog hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (tendsto_inv_natp1 hw)).add
        (summable_rho hw ht).hasSum.tendsto_sum_nat).const_mul _)).add
      (summable_eps hw ht).hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique hL hR
  rw [sub_zero] at this
  linear_combination this

set_option maxHeartbeats 1600000 in
theorem log_one_add_sub_log (hw : 0 < w.re) :
    Complex.log (1 + w) - Complex.log w = w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0 := by
  have h1 := integral_inv_add_eq hw (m := 0) le_rfl
  have h2 := integral_inv_add_eq_log_sub hw (m := 0) le_rfl
  rw [h2] at h1
  simpa [add_comm] using h1

set_option maxHeartbeats 1600000 in
theorem norm_eps_zero_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : ‖eps w 0‖ ≤ (1 / 3) / |w.im| ^ 3 := by
  have h := norm_eps_le hw ht (m := 0) le_rfl
  have ht0 : 0 < |w.im| := by linarith
  have hw' : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  simp only [Complex.ofReal_zero, zero_add] at h
  calc ‖eps w 0‖ ≤ 1 / (3 * ‖w‖ ^ 2 * |w.im|) := h
    _ ≤ 1 / (3 * |w.im| ^ 2 * |w.im|) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        gcongr
    _ = (1 / 3) / |w.im| ^ 3 := by field_simp

set_option maxHeartbeats 1600000 in
theorem digamma_stirling (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1w : 1 + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ht0 : 0 < |w.im| := by linarith
  have hwn : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h1wn : |w.im| ≤ ‖1 + w‖ := by have := Complex.abs_im_le_norm (1 + w); simpa using this
  have hid := digamma_eq hw ht
  have hlog := log_one_add_sub_log hw
  
  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
      = -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hid, show Complex.log (1 + w) = Complex.log w + (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by
      rw [← hlog]; ring]
    field_simp
    ring
  rw [key]
  have hsq : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤ (1 / 2) / w.im ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, ← hsq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : 1 ≤ ‖1 + w‖ := le_trans (by simp; linarith) (Complex.re_le_norm (1 + w))
    calc |w.im| ^ 2 = |w.im| ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖w‖ ^ 2 * ‖1 + w‖ := by gcongr
  have b2 : ‖eps w 0‖ ≤ (2 / 3) / w.im ^ 2 := by
    refine le_trans (norm_eps_zero_le hw ht) ?_
    rw [← hsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |w.im| ^ 3 = |w.im| ^ 2 * |w.im| := by ring
    rw [h3]
    have : 0 < |w.im| ^ 2 := by positivity
    nlinarith
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ 1 / w.im ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := mul_le_mul_of_nonneg_left (norm_tsum_rho_le hw ht) (by norm_num : (0:ℝ) ≤ 1 / 2)
    calc 1 / 2 * ‖∑' n, rho w n‖ ≤ 1 / 2 * (2 / w.im ^ 2) := h
      _ = 1 / w.im ^ 2 := by ring
  have b4 := norm_tsum_eps_le hw ht
  calc ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n
        + ∑' n : ℕ, eps w ((n : ℝ) + 1)‖
      ≤ ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ + ‖(1 / 2 : ℂ) * ∑' n, rho w n‖
        + ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
        have s1 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n)
          (∑' n : ℕ, eps w ((n : ℝ) + 1))
        have s2 := norm_sub_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0) ((1 / 2 : ℂ) * ∑' n, rho w n)
        have s3 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
        linarith
    _ ≤ (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2 := by
        gcongr
    _ ≤ 3 / w.im ^ 2 := by
        have hpos : 0 < w.im ^ 2 := by rw [← hsq]; positivity
        rw [show (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2
          = (17 / 6) / w.im ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ hpos.le
        norm_num

end Seq

section RePart

set_option maxHeartbeats 1600000 in
theorem re_digamma_stirling {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
      ≤ 4 / t ^ 2 := by
  set w : ℂ := (a : ℂ) + Complex.I * t with hwdef
  have hre : w.re = a := by simp [hwdef]
  have him : w.im = t := by simp [hwdef]
  have hw : 0 < w.re := by rw [hre]; exact ha0
  have ht' : 1 / 2 ≤ |w.im| := by rw [him]; exact ht
  have hmain := digamma_stirling hw ht'
  rw [him] at hmain
  have ht0 : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  
  have hlogre : (Complex.log w).re = (1 / 2) * Real.log (a ^ 2 + t ^ 2) := by
    rw [Complex.log_re, show ‖w‖ = Real.sqrt (a ^ 2 + t ^ 2) by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him], Real.log_sqrt (by positivity)]
    ring
  have hinvre : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring, Complex.re_ofReal_mul,
      Complex.inv_re, Complex.normSq_apply, hre, him]
    field_simp
  have hdiff : (Complex.digamma w).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)
      = (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re - a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [Complex.add_re, Complex.sub_re, hlogre, hinvre]; ring
  rw [hdiff]
  have h1 : |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re| ≤ 3 / t ^ 2 :=
    le_trans (Complex.abs_re_le_norm _) hmain
  have h2 : |a / (2 * (a ^ 2 + t ^ 2))| ≤ 1 / t ^ 2 := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) ht2]
    nlinarith
  calc |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re - a / (2 * (a ^ 2 + t ^ 2))|
      ≤ |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re| + |a / (2 * (a ^ 2 + t ^ 2))| :=
        abs_sub _ _
    _ ≤ 3 / t ^ 2 + 1 / t ^ 2 := add_le_add h1 h2
    _ = 4 / t ^ 2 := by ring

set_option maxHeartbeats 1600000 in
theorem re_digamma_stirling' {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤ 5 / t ^ 2 := by
  have h := re_digamma_stirling ha0 ha1 ht
  have ht0 : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  
  have hl : (1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)
      = (1 / 2) * Real.log (1 + a ^ 2 / t ^ 2) := by
    have htne : t ≠ 0 := fun h0 => by rw [h0] at ht0; simp at ht0
    have : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by field_simp; ring
    rw [this, Real.log_mul ht2.ne' (by positivity), ← sq_abs, Real.log_pow]
    push_cast; ring
  have hb : |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| ≤ 1 / t ^ 2 := by
    have hx0 : 0 ≤ a ^ 2 / t ^ 2 := by positivity
    have hlog0 : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) := Real.log_nonneg (by linarith)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + a ^ 2 / t ^ 2)
    have ha2 : a ^ 2 / t ^ 2 ≤ 1 / t ^ 2 := by
      apply div_le_div_of_nonneg_right _ ht2.le; nlinarith
    rw [hl, abs_of_nonneg (by positivity)]
    linarith
  calc |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)|
      ≤ |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
        + |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| := abs_sub_le _ _ _
    _ ≤ 4 / t ^ 2 + 1 / t ^ 2 := add_le_add h hb
    _ = 5 / t ^ 2 := by ring

set_option maxHeartbeats 1600000 in
theorem mu_stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2 := by
  refine ⟨20 / (2 * Real.pi), fun τ hτ => ?_⟩
  have hπ := Real.pi_pos
  have ht : 1 / 2 ≤ |τ / 2| := by rw [abs_div, abs_two]; linarith
  have h := re_digamma_stirling' (a := 1 / 4) (by norm_num) (by norm_num) ht
  have hτ0 : 0 < |τ| := by linarith
  set D : ℝ := (Complex.digamma ((((1:ℝ) / 4 : ℝ)) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
    - Real.log |τ / 2| with hD
  have hD5 : |D| ≤ 5 / (τ / 2) ^ 2 := h
  
  have hlogs : Real.log (|τ| / (2 * Real.pi)) = Real.log |τ / 2| - Real.log Real.pi := by
    rw [abs_div, abs_two, Real.log_div hτ0.ne' (by positivity), Real.log_div hτ0.ne' two_ne_zero,
      Real.log_mul two_ne_zero hπ.ne']
    ring
  have key : Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))
      = (1 / (2 * Real.pi)) * D := by
    rw [Zeta23.MuFields.mu_eq τ, hlogs, hD]
    ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |D| ≤ 1 / (2 * Real.pi) * (5 / (τ / 2) ^ 2) := by gcongr
    _ = 20 / (2 * Real.pi) / τ ^ 2 := by field_simp; ring

end RePart

end StirlingVert

end Zeta23

end
end

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/- Module Zeta23.GammaFacts.Complete -/
section
noncomputable section

namespace Zeta23

set_option maxHeartbeats 1600000 in
theorem gammaFacts_of_stirling (hst : MuInts.StirlingHyp) : GammaFacts :=
  ⟨mu_even, mu_smooth, MuFields.mu_monotoneOn, MuFields.mu_zero_le, MuFields.neg_one_lt_mu_zero,
    hst, MuFields.mu_deriv_bound, MuInts.int_mu_of_stirling hst, MuInts.int_mu_sq_of_stirling hst⟩

set_option maxHeartbeats 1600000 in
theorem gammaFacts : GammaFacts := gammaFacts_of_stirling StirlingVert.mu_stirling

end Zeta23

end
end

open Zeta23 Set Filter
namespace Density233
private abbrev Zero := {ρ : ℂ // IsNontrivialZero ρ}
private noncomputable def win (t : ℝ) : ℂ → ℝ :=
  (zerosIn t (t+1)).indicator (fun z => (zeroMult z : ℝ))

private lemma wsum (t : ℝ) : Summable (fun z : Zero => win t z) ∧
    (∑' z : Zero, win t z) = (Ncount t (t+1):ℝ) := by
  classical
  have fin := zerosIn_finite t (t+1)
  have hsup : Function.support (win t) ⊆ zerosIn t (t+1) := Set.support_indicator_subset
  have hsum : Summable (win t) := summable_of_hasFiniteSupport (fin.subset hsup)
  refine ⟨hsum.subtype _,?_⟩
  trans ∑' z : ℂ, {z : ℂ | IsNontrivialZero z}.indicator (win t) z
  · exact tsum_subtype {z : ℂ | IsNontrivialZero z} (win t)
  have he : {z : ℂ | IsNontrivialZero z}.indicator (win t) = win t := by
    funext z
    by_cases hz : z ∈ {w : ℂ | IsNontrivialZero w}
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      exact (Set.indicator_of_notMem (show z ∉ zerosIn t (t+1) from fun h => hz h.1) (fun w : ℂ => (zeroMult w:ℝ))).symm
  rw [he,tsum_eq_sum' (s:=fin.toFinset) (by simpa using hsup)]
  rw [Ncount,finsum_mem_eq_finite_toFinset_sum _ fin,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  exact Set.indicator_of_mem (fin.mem_toFinset.mp hz) _

private lemma pos (t : ℝ) (z : ℂ) : 0 ≤ win t z := by
  classical
  exact Set.indicator_nonneg (fun i _ => Nat.cast_nonneg _) _

private lemma total :
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
    Summable (fun ρ : Zero => if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T+1 then (analyticOrderNatAt riemannZeta (ρ:ℂ) : ℝ) else 0) ∧
    (∑' ρ : Zero, if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T+1 then (analyticOrderNatAt riemannZeta (ρ:ℂ) : ℝ) else 0) ≤ C*Real.log (T+2) := by
  classical
  obtain ⟨A,hA,hbound⟩ := RvM.zeta_local_zero_count
  refine ⟨6*A,by linarith,fun T hT => ?_⟩
  let u := fun z : Zero => if T ≤ |z.1.im| ∧ |z.1.im| < T+1 then (zeroMult z:ℝ) else 0
  let v := fun z : Zero => win (T-1) z + win T z + win (-T-1) z
  have hv : Summable v := ((wsum _).1.add (wsum _).1).add (wsum _).1
  have hu (z : Zero) : 0 ≤ u z := by dsimp [u]; split <;> positivity
  have le (z : Zero) : u z ≤ v z := by
    have p := pos (T-1) z
    have q := pos T z
    have r := pos (-T-1) z
    simp only [u,v]
    split_ifs with hz
    · have hm : (z:ℂ) ∈ zerosIn (T-1) (T-1+1) ∨ (z:ℂ) ∈ zerosIn T (T+1) ∨ (z:ℂ) ∈ zerosIn (-T-1) (-T-1+1) := by
        by_cases h : 0 ≤ z.1.im
        · rw [abs_of_nonneg h] at hz
          by_cases he : z.1.im ≤ T
          · exact Or.inl ⟨z.property,by linarith [hz.1],by linarith⟩
          · exact Or.inr (Or.inl ⟨z.property,lt_of_not_ge he,hz.2.le⟩)
        · rw [abs_of_neg (lt_of_not_ge h)] at hz
          exact Or.inr (Or.inr ⟨z.property,by linarith [hz.2],by linarith [hz.1]⟩)
      rcases hm with h|h|h
      · rw [show win (T-1) z = (zeroMult z:ℝ) from Set.indicator_of_mem h _]; linarith
      · rw [show win T z = (zeroMult z:ℝ) from Set.indicator_of_mem h _]; linarith
      · rw [show win (-T-1) z = (zeroMult z:ℝ) from Set.indicator_of_mem h _]; linarith
    · linarith
  change Summable u ∧ (∑' z, u z) ≤ _
  have hs := Summable.of_nonneg_of_le hu le hv
  refine ⟨hs,(hs.tsum_le_tsum le hv).trans ?_⟩
  change (∑' z : Zero, (win (T-1) z + win T z + win (-T-1) z)) ≤ _
  rw [((wsum _).1.add (wsum _).1).tsum_add (wsum _).1, (wsum _).1.tsum_add (wsum _).1,
    (wsum _).2,(wsum _).2,(wsum _).2]
  have hlog (x : ℝ) (hx : |x| ≤ T+1) : (Ncount x (x+1):ℝ) ≤ A*(2*Real.log (T+2)) := by
    apply (hbound x).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    change _ ≤ ((2:ℕ):ℝ) * Real.log (T+2)
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    nlinarith [sq_nonneg T]
  have p := hlog (T-1) (abs_le.mpr ⟨by linarith,by linarith⟩)
  have q := hlog T (by rw [abs_of_nonneg hT]; linarith)
  have r := hlog (-T-1) (abs_le.mpr ⟨by linarith,by linarith⟩)
  linarith
end Density233

namespace PositiveLi
open Complex MeasureTheory Filter
open scoped Real
lemma rh_re_eq_half (hRH : RiemannHypothesis) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  refine hRH ρ hζ ?_ ?_
  · rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h
    rw [h] at h1
    simp at h1

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h1
  linarith

lemma summable_log_tail (C₁ : ℝ) (hC₁ : 0 ≤ C₁) {δ : ℝ} (hδ0 : 0 < δ) :
    Summable (fun k : ℕ ↦ C₁ * Real.log ((k : ℝ) + 2) *
      min (δ ^ 2) (13 / max (3 / 4) ((k : ℝ) ^ 2))) := by
  have hp : Summable (fun k : ℕ ↦ (C₁ * (13 * (2 * Real.sqrt 3))) * (((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    ((Real.summable_nat_rpow.mpr (by norm_num)).comp_injective (add_left_injective 2)).mul_left _
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg
      (mul_nonneg hC₁ (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])))
      (le_min (sq_nonneg δ) (by positivity)))
    (fun k ↦ ?_) hp
  have hk2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 2)
  have hk0 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by linarith
  have hlog : Real.log (((k + 2 : ℕ) : ℝ) + 2) ≤ 2 * Real.sqrt 3 * ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
    calc Real.log (((k + 2 : ℕ) : ℝ) + 2) ≤ 2 * Real.sqrt (((k + 2 : ℕ) : ℝ) + 2) :=
          log_le_two_sqrt (by linarith)
      _ ≤ 2 * Real.sqrt (3 * ((k + 2 : ℕ) : ℝ)) := by gcongr; linarith
      _ = 2 * (Real.sqrt 3 * Real.sqrt ((k + 2 : ℕ) : ℝ)) := by rw [Real.sqrt_mul (by norm_num)]
      _ = 2 * Real.sqrt 3 * ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]; ring
  have hmin : min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + 2 : ℕ) : ℝ) ^ 2)) ≤
      13 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
    refine (min_le_right _ _).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hk0) (le_max_right _ _)
  have hlog_nn : 0 ≤ Real.log (((k + 2 : ℕ) : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hrpow : ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 =
      ((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast ((k + 2 : ℕ) : ℝ) 2, ← Real.rpow_sub hk0]
    norm_num
  calc C₁ * Real.log (((k + 2 : ℕ) : ℝ) + 2) *
        min (δ ^ 2) (13 / max (3 / 4 : ℝ) (((k + 2 : ℕ) : ℝ) ^ 2))
      ≤ C₁ * (2 * Real.sqrt 3 * ((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) * (13 / ((k + 2 : ℕ) : ℝ) ^ 2) := by
        gcongr
    _ = C₁ * (13 * (2 * Real.sqrt 3)) * (((k + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) := by ring
    _ = (C₁ * (13 * (2 * Real.sqrt 3))) * (((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by rw [hrpow]

lemma summable_zero_weighted {C₁ : ℝ}
    (h1 : ∀ T : ℝ, 0 ≤ T →
      Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} =>
        if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T + 1 then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
        else 0) ∧
      (∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        if T ≤ |ρ.1.im| ∧ |ρ.1.im| < T + 1 then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
        else 0) ≤ C₁ * Real.log (T + 2))
    (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hw_sum : Summable (fun k : ℕ ↦ C₁ * Real.log ((k : ℝ) + 2) * w k))
    (g : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1} → ℝ)
    (hg0 : ∀ ρ, 0 ≤ g ρ)
    (hg_le : ∀ ρ, g ρ ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * w ⌊|ρ.1.im|⌋₊) :
    Summable g := by
  refine summable_of_sum_le (c := ∑' k : ℕ, C₁ * Real.log ((k : ℝ) + 2) * w k) hg0 fun u ↦ ?_
  let M : ℕ := u.sup fun ρ ↦ ⌊|ρ.1.im|⌋₊
  have hmap : ∀ ρ ∈ u, ⌊|ρ.1.im|⌋₊ ∈ Finset.range (M + 1) := fun ρ hρ ↦
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := fun ρ ↦ ⌊|ρ.1.im|⌋₊) hρ))
  rw [← Finset.sum_fiberwise_of_maps_to hmap g]
  have hterm : ∀ k ∈ Finset.range (M + 1),
      ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ ≤ C₁ * Real.log ((k : ℝ) + 2) * w k := by
    intro k _
    obtain ⟨hsum_k, hbd_k⟩ := h1 k (Nat.cast_nonneg k)
    have h1' : ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ ≤
        w k * ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k,
          (if (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 then
            (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
          else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ ↦ ?_
      have hk_eq : ⌊|ρ.1.im|⌋₊ = k := (Finset.mem_filter.mp hρ).2
      have hcond : (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 :=
        (Nat.floor_eq_iff (abs_nonneg _)).mp hk_eq
      rw [if_pos hcond, mul_comm]
      simpa [hk_eq] using hg_le ρ
    have h2' : ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k,
        (if (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 then
          (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
        else 0) ≤ C₁ * Real.log ((k : ℝ) + 2) := by
      refine (hsum_k.sum_le_tsum _ fun ρ _ ↦ ?_).trans hbd_k
      split_ifs <;> positivity
    calc ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ
        ≤ w k * ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k,
            (if (k : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (k : ℝ) + 1 then
              (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
            else 0) := h1'
      _ ≤ w k * (C₁ * Real.log ((k : ℝ) + 2)) := mul_le_mul_of_nonneg_left h2' (hw k)
      _ = C₁ * Real.log ((k : ℝ) + 2) * w k := by ring
  calc ∑ k ∈ Finset.range (M + 1), ∑ ρ ∈ u with ⌊|ρ.1.im|⌋₊ = k, g ρ
      ≤ ∑ k ∈ Finset.range (M + 1), C₁ * Real.log ((k : ℝ) + 2) * w k := Finset.sum_le_sum hterm
    _ ≤ ∑' k : ℕ, C₁ * Real.log ((k : ℝ) + 2) * w k := by
        refine hw_sum.sum_le_tsum (Finset.range (M + 1)) fun k _ ↦ ?_
        have hC₁ : 0 ≤ C₁ := by
          have := (h1 0 le_rfl).2
          have hnn : 0 ≤ ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
              (if (0 : ℝ) ≤ |ρ.1.im| ∧ |ρ.1.im| < (0 : ℝ) + 1 then
                (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ)
              else 0) := tsum_nonneg fun _ ↦ by split_ifs <;> positivity
          have hl2 : 0 < Real.log ((0 : ℝ) + 2) := Real.log_pos (by norm_num)
          nlinarith [this, hnn, hl2]
        have hl : 0 ≤ Real.log ((k : ℝ) + 2) :=
          Real.log_nonneg (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
        exact mul_nonneg (mul_nonneg hC₁ hl) (hw k)

end PositiveLi
open Complex Set
namespace PositiveLi
private abbrev Zero := {z : ℂ // Zeta23.IsNontrivialZero z}
private abbrev PosZero := RiemannHypothesis.nontrivialPosZeros
private noncomputable def W (z : ℂ) : ℂ := 1 - 1/z

private noncomputable def weight (k : ℕ) : ℝ := min ((2:ℝ)^2) (13 / max (3/4) ((k:ℝ)^2))
private lemma weight_pos (k : ℕ) : 0 ≤ weight k := le_min (sq_nonneg _) (by positivity)

private lemma bound_z (hRH : RiemannHypothesis) (z : Zero) :
    1/‖(z:ℂ)‖^2 ≤ (analyticOrderNatAt riemannZeta (z:ℂ) : ℝ) * weight ⌊|z.1.im|⌋₊ := by
  have hr := rh_re_eq_half hRH z.2.1 z.2.2.1 z.2.2.2
  have half : (1/2:ℝ) ≤ ‖(z:ℂ)‖ := hr ▸ Complex.re_le_norm (z:ℂ)
  have pos : 0 < ‖(z:ℂ)‖^2 := sq_pos_of_pos (by linarith)
  have flo : (⌊|z.1.im|⌋₊ : ℝ) ≤ ‖(z:ℂ)‖ := (Nat.floor_le (abs_nonneg _)).trans (Complex.abs_im_le_norm _)
  have fk := pow_le_pow_left₀ (Nat.cast_nonneg ⌊|z.1.im|⌋₊) flo 2
  have h4 : 1 ≤ 4 * ‖(z:ℂ)‖^2 := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) half]
  have den : 0 < max (3/4:ℝ) ((⌊|z.1.im|⌋₊:ℝ)^2) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/4) (le_max_left _ _)
  have bd : 1/‖(z:ℂ)‖^2 ≤ weight ⌊|z.1.im|⌋₊ := by
    apply le_min
    · exact (div_le_iff₀ pos).mpr (by linarith)
    · apply (div_le_div_iff₀ pos den).mpr
      rw [one_mul]
      exact max_le (by linarith) (by nlinarith)
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta (z:ℂ) := by
    exact_mod_cast Zeta23.ZetaSeam.one_le_mult_holds _ z.2
  exact bd.trans (le_mul_of_one_le_left (weight_pos _) hm)

private lemma sum_all (hRH : RiemannHypothesis) : Summable (fun z : Zero => 1 / ‖(z:ℂ)‖^2) := by
  obtain ⟨C,hC,hwin⟩ := Density233.total
  have hws : Summable (fun k : ℕ => C * Real.log ((k:ℝ)+2) * weight k) :=
    summable_log_tail C hC.le (δ:=2) (by norm_num)
  apply summable_zero_weighted hwin weight weight_pos hws _ (fun _ => by positivity)
  exact bound_z hRH

private lemma reciprocal_sum (hRH : RiemannHypothesis) :
    Summable (fun z : PosZero => 1 / ‖(z:ℂ)‖^2) := by
  let inc (z : PosZero) : Zero := ⟨z, z.2.2.2.2, z.2.1, z.2.2.1⟩
  have hi : Function.Injective inc := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : Zero => (x:ℂ)) hab)
  have hs := (sum_all hRH).comp_injective hi
  simpa only [Function.comp_def,inc] using hs

private lemma norm_w (z : ℂ) (hr : z.re = 1/2) : ‖W z‖ = 1 := by
  have h0 : z ≠ 0 := by rintro rfl; norm_num at hr
  have he : W z = (z-1)/z := by unfold W; field_simp
  have heq : ‖z-1‖ = ‖z‖ := by
    have hh : ‖z-1‖^2 = ‖z‖^2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero, hr]
      ring
    nlinarith [norm_nonneg (z-1),norm_nonneg z]
  rw [he,norm_div,heq,div_self (norm_ne_zero_iff.mpr h0)]

private lemma gap_le (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) : ‖1-w^n‖ ≤ n*‖1-w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖1-w^(n+1)‖ = ‖(1-w^n) + w^n*(1-w)‖ := by congr 1; ring
         _ ≤ ‖1-w^n‖ + ‖w^n*(1-w)‖ := norm_add_le _ _
         _ ≤ (n+1:ℕ)*‖1-w‖ := by rw [norm_mul,norm_pow,hw,one_pow,one_mul,Nat.cast_add_one]; linarith

private lemma summand_eq (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    2*(1-w^n).re = ‖1-w^n‖^2 := by
  have hn : ‖w^n‖^2 = 1 := by rw [norm_pow,hw,one_pow,one_pow]
  simp only [Complex.sq_norm,Complex.normSq_apply] at hn ⊢
  simp only [sub_re,sub_im,one_re,one_im] 
  nlinarith

private lemma main_of_infinite (hInf : (RiemannHypothesis.nontrivialPosZeros).Infinite)
    (hRH : RiemannHypothesis) (n : ℕ) (hn : 0<n) : 0<RiemannHypothesis.lambda n := by
  let f (z : PosZero) := 2*(1-(W z)^n).re
  have hw (z : PosZero) : ‖W z‖=1 := norm_w _ (rh_re_eq_half hRH z.2.2.2.2 z.2.1 z.2.2.1)
  have he (z : PosZero) : f z = ‖1-(W z)^n‖^2 := summand_eq _ (hw z) _
  have hs : Summable f := by
    apply Summable.of_nonneg_of_le (fun z => (he z) ▸ sq_nonneg _) _ ((reciprocal_sum hRH).mul_left ((n:ℝ)^2))
    intro z
    rw [he]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (gap_le _ (hw z) n) 2
    simpa [W,norm_div,mul_pow,div_pow] using hh
  classical
  let P := Polynomial.X ^ n - Polynomial.C (1:ℂ)
  have hp : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn _
  have hi : Function.Injective W := by
    intro a b h; simpa [W,one_div] using h
  obtain ⟨w,⟨z,hz,rfl⟩,hm⟩ := (hInf.image hi.injOn).exists_notMem_finite (Polynomial.finite_setOfPred_isRoot hp)
  let a : PosZero := ⟨z,hz⟩
  have hne : 1-(W z)^n ≠ 0 := by
    intro hh
    exact hm (by simpa [P, Polynomial.IsRoot] using (sub_eq_zero.mpr (sub_eq_zero.mp hh).symm : (W z)^n - 1 = 0))
  exact hs.tsum_pos (fun i => (he i) ▸ sq_nonneg _) a ((he a) ▸ sq_pos_of_pos (norm_pos_iff.mpr hne))
end PositiveLi
open Zeta23 Set Filter
namespace PositiveLi
private lemma zeros_infinite : (RiemannHypothesis.nontrivialPosZeros).Infinite := by
  intro hfinite
  obtain ⟨M,hM⟩ := (hfinite.image Complex.im).bddAbove
  obtain ⟨C,T₀,hN⟩ := RvM.rvM_main gammaFacts
  have hpi := Real.pi_pos
  have huge : ∀ᶠ T : ℝ in atTop, M < T ∧ T₀ ≤ T ∧ 4*Real.pi*C < T ∧ 1 < T ∧
      2*(Real.log (2*Real.pi)+1) < Real.log T := by
    filter_upwards [eventually_gt_atTop M,eventually_ge_atTop T₀,
      eventually_gt_atTop (4*Real.pi*C),eventually_gt_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop (2*(Real.log (2*Real.pi)+1))] with T h1 h2 h3 h4 h5
    exact ⟨h1,h2,h3,h4,h5⟩
  obtain ⟨T,hm,ht,hb,hone,hlog⟩ := huge.exists
  have hT : 0 < T := by linarith
  have empty : zerosIn T (2*T) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz,hgt,-⟩
    exact (not_lt_of_ge (hM (show z.im ∈ Complex.im '' RiemannHypothesis.nontrivialPosZeros from
      ⟨z,⟨hz.2.1,hz.2.2,hT.trans hgt,hz.1⟩,rfl⟩))) (hm.trans hgt)
  have nh : zetaZeroConfig.N T (2*T) = 0 := by simp [zetaZeroConfig_N,Ncount,empty]
  have bd := hN T ht
  rw [nh,Nat.cast_zero,zero_sub,abs_neg] at bd
  have hl : 0 < Real.log T := Real.log_pos hone
  have hel : Real.log T/2 < ell1 T := by
    rw [ell1,l,Real.log_div hT.ne' (by positivity)]
    linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  have hc : C*2 < T/(2*Real.pi) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have strict : C*Real.log T < T/(2*Real.pi)*ell1 T := calc
    C*Real.log T = (C*2)*(Real.log T/2) := by ring
    _ < (T/(2*Real.pi))*(Real.log T/2) := mul_lt_mul_of_pos_right hc (by positivity)
    _ < _ := mul_lt_mul_of_pos_left hel (by positivity)
  exact strict.not_ge ((le_abs_self _).trans bd)
end PositiveLi

open Complex Zeta23 MeasureTheory Set
namespace ReverseLi
abbrev Index := RiemannHypothesis.nontrivialPosZeros
noncomputable def w (z : Index) : ℂ := 1 - 1/(z:ℂ)
lemma real_nonzero {r : ℝ} (hr : 1/2 ≤ r) (hr' : r < 1) : riemannZeta (r:ℂ) ≠ 0 := by
  intro hz
  have hp : 0 < r := by linarith
  have hs : (r:ℂ) ≠ 1 := by exact_mod_cast hr'.ne
  have hs0 : (r:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hint := ZetaBnd_aux1b 1 le_rfl (σ := r) (t := 0) hp
  simp only [Nat.cast_one,Real.one_rpow,Complex.ofReal_zero,zero_mul,add_zero] at hint
  rw [← Zeta0EqZeta (N:=1) one_pos (by simpa) hs] at hz
  simp only [riemannZeta0,Finset.sum_range_succ,Finset.sum_range_zero,Nat.cast_zero,
    Complex.zero_cpow hs0,Nat.cast_one,Complex.one_cpow,div_one,div_zero,zero_add] at hz
  let J := ∫ x in Ioi (1:ℝ), ((⌊x⌋:ℂ)+1/2-x)/(x:ℂ)^((r:ℂ)+1)
  have hj : ‖J‖ ≤ 1/r := hint
  have hterm : ((r:ℂ)*J).re ≤ 1 := calc
    _ ≤ ‖(r:ℂ)*J‖ := Complex.re_le_norm _
    _ = r*‖J‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    _ ≤ r*(1/r) := mul_le_mul_of_nonneg_left hj hp.le
    _ = _ := by field_simp
  change (1:ℂ) + -1/(1-(r:ℂ)) + -1/2 + (r:ℂ)*J = 0 at hz
  have eq : (1:ℂ) + -1/(1-(r:ℂ)) + -1/2 = ((1-1/(1-r)-1/2:ℝ):ℂ) := by push_cast; ring
  rw [eq] at hz
  have hh := congrArg Complex.re hz
  simp only [add_re,ofReal_re,zero_re] at hh
  have hd : 2 ≤ 1/(1-r) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  linarith

lemma strip {s : ℂ} (hz : riemannZeta s=0) (hnt : ¬∃ n : ℕ, s = -2*(n+1)) :
    IsNontrivialZero s := by
  have hn : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  have hr : s.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz
  refine ⟨hz,?_,hr⟩
  by_contra! he
  have hg : Gammaℝ s ≠ 0 := by
    intro h
    obtain ⟨n,hn'⟩ := Gammaℝ_eq_zero_iff.mp h
    cases n with
    | zero => exact hn (by simpa using hn')
    | succ k => exact hnt ⟨k,by simpa [Nat.cast_add_one] using hn'⟩
  have hc : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hn,div_eq_zero_iff] at hz
    exact hz.resolve_right hg
  have h1 : 1 ≤ (1-s).re := by simp; linarith
  have hne : 1-s ≠ 0 := by intro h; have := h1; rw [h] at this; norm_num at this
  apply riemannZeta_ne_zero_of_one_le_re h1
  rw [riemannZeta_def_of_ne_zero hne,completedRiemannZeta_one_sub,hc,zero_div]

lemma nonreal {s : ℂ} (hs : IsNontrivialZero s) : s.im ≠ 0 := by
  intro hi
  have right (z : ℂ) (hz : IsNontrivialZero z) (hh : 1/2 ≤ z.re) (hzi : z.im = 0) : False := by
    have eq : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hzi]
    exact real_nonzero hh hz.2.2 (by rw [← eq]; exact hz.1)
  by_cases h : 1/2 ≤ s.re
  · exact right _ hs h hi
  · exact right _ (zeta_reflect_zero s hs) (by rw [reflect_re]; linarith) (by rwa [reflect_im])

lemma bad (h : ¬ RiemannHypothesis) : ∃ z : Index, 1 < ‖w z‖ := by
  unfold RiemannHypothesis at h
  push Not at h
  obtain ⟨s,hz,hnt,-,hoff⟩ := h
  have hs := strip hz (fun ⟨n,he⟩ => hnt n he)
  have left : ∃ t, IsNontrivialZero t ∧ t.re < 1/2 := by
    rcases lt_or_gt_of_ne hoff with hl|hg
    · exact ⟨s,hs,hl⟩
    · exact ⟨reflect s,zeta_reflect_zero _ hs,by rw [reflect_re]; linarith⟩
  obtain ⟨t,ht,hl⟩ := left
  have pos : ∃ z : Index, (z:ℂ).re < 1/2 := by
    rcases lt_or_gt_of_ne (nonreal ht) with hn|hp
    · refine ⟨⟨starRingEnd ℂ t,?_,?_,?_,?_⟩,?_⟩
      · simpa using ht.2.1
      · simpa using ht.2.2
      · simpa using hn
      · have ht1 : t ≠ 1 := fun e => (nonreal ht) (by simp [e])
        rw [riemannZeta_conj ht1,ht.1,map_zero]
      · simpa using hl
    · exact ⟨⟨t,ht.2.1,ht.2.2,hp,ht.1⟩,hl⟩
  obtain ⟨z,hz'⟩ := pos
  have hn : (z:ℂ) ≠ 0 := fun e => (ne_of_gt z.2.1) (by simp [e])
  have he : w z = ((z:ℂ)-1)/z := by unfold w; field_simp
  refine ⟨z,?_⟩
  rw [he,norm_div,one_lt_div (norm_pos_iff.mpr hn)]
  have hh : ‖(z:ℂ)‖^2 < ‖(z:ℂ)-1‖^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,sub_re,sub_im,one_re,one_im,sub_zero]
    nlinarith
  nlinarith [norm_nonneg (z:ℂ),norm_nonneg ((z:ℂ)-1)]
end ReverseLi

open Complex Filter Set
open scoped Topology
namespace ReverseLi
lemma phase_times {ι : Type*} [Fintype ι] (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧
      ∀ᶠ k : ℕ in atTop, ∀ i, ‖a i‖^(N k)/2 ≤ ((a i)^(N k)).re := by
  let u (i : ι) : Circle := ⟨a i / (‖a i‖:ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self (norm_ne_zero_iff.mpr (ha i))])⟩
  obtain ⟨v,φ,hφ,hv⟩ := CompactSpace.tendsto_subseq (fun n : ℕ => u^n)
  let j (k : ℕ) := φ k + k
  let N (k : ℕ) := φ (j k) - φ k
  have hj : Tendsto j atTop atTop := tendsto_atTop_mono (fun k => Nat.le_add_left k (φ k)) tendsto_id
  have hbig (k : ℕ) : φ k+k ≤ φ (j k) := hφ.id_le _
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono (fun k => (show k ≤ N k by dsimp [N]; have := hbig k; omega)) tendsto_id
  have hlim : Tendsto (fun k => u^(N k)) atTop (𝓝 1) := by
    have h := (hv.comp hj).mul hv.inv
    rw [mul_inv_cancel] at h
    apply h.congr'
    filter_upwards with k
    exact (pow_sub u (show φ k ≤ φ (j k) by have := hbig k; omega)).symm
  have hc (i : ι) : Tendsto (fun k => (((u i)^(N k) : Circle):ℂ).re) atTop (𝓝 1) := by
    have hh := (Complex.continuous_re.comp (continuous_subtype_val (p:=fun z : ℂ => z ∈ Submonoid.unitSphere ℂ))).continuousAt (x := (1 : Circle))
    exact hh.tendsto.comp (tendsto_pi_nhds.mp hlim i)
  have hevent : ∀ᶠ k : ℕ in atTop, ∀ i, (1/2:ℝ) ≤ (((u i)^(N k):Circle):ℂ).re :=
    Filter.eventually_all.mpr fun i => (hc i).eventually (le_mem_nhds (by norm_num : (1/2:ℝ)<1))
  refine ⟨N,hN,?_⟩
  filter_upwards [hevent] with k hk i
  have he : a i = (‖a i‖:ℂ) * (u i:ℂ) := by
    have h : (‖a i‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (ha i)
    dsimp [u]; field_simp
  have eq : ((a i)^(N k)).re = ‖a i‖^(N k) * (((u i)^(N k):Circle):ℂ).re := by
    conv_lhs => rw [he,mul_pow]
    simp [← Complex.ofReal_pow]
  rw [eq]
  nlinarith [mul_le_mul_of_nonneg_left (hk i) (pow_nonneg (norm_nonneg (a i)) (N k))]
end ReverseLi

open Complex Filter Finset
open scoped Topology
namespace ReverseLi
noncomputable def f (n : ℕ) (z : Index) : ℝ := 2*(1-(w z)^n).re
noncomputable def g (z : Index) : ℝ := ‖1-w z‖^2
lemma g_nonneg (z : Index) : 0 ≤ g z := sq_nonneg _
lemma f_sum (h : ∀ n > 0, 0 < RiemannHypothesis.lambda n) {n : ℕ} (hn : 0 < n) : Summable (f n) := by
  by_contra h'
  exact (h n hn).ne' (tsum_eq_zero_of_not_summable h')
lemma real_gap (z : Index) : (1-w z).re ≤ g z := by
  have h0 : 0 ≤ ((z:ℂ).normSq)⁻¹ := inv_nonneg.mpr (Complex.normSq_nonneg _)
  simpa [g,w,one_div,inv_re,← normSq_eq_norm_sq,div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right z.2.2.1.le h0)
lemma summable_g (h : ∀ n > 0, 0 < RiemannHypothesis.lambda n) : Summable g := by
  let p (z : Index) := (1-w z).re
  have hp : Summable p := by
    apply ((f_sum h (n:=1) (by decide)).mul_left (1/2:ℝ)).congr
    intro z; simp [f,p]
  have hp0 (z : Index) : 0 ≤ p z := by
    simp only [p,w,sub_sub_cancel,one_div,inv_re]
    exact div_nonneg z.2.1.le (Complex.normSq_nonneg _)
  have sqsum := (hp.mul_of_nonneg hp hp0 hp0).comp_injective (show Function.Injective (fun z : Index => (z,z)) from fun _ _ he => congrArg Prod.fst he)
  have hint := ((sqsum.mul_left 2).sub (hp.mul_left 2)).add ((f_sum h (n:=2) (by decide)).mul_left (1/2:ℝ))
  apply hint.congr
  intro z
  unfold g
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [p,f,Function.comp_apply,sub_re,sub_im,one_re,one_im,pow_two,mul_re]
  ring

lemma first_gap {a : ℂ} {b : ℝ} (hb : 1 ≤ b) (ha : ‖a‖ ≤ b) (n : ℕ) :
    ‖1-a^n‖ ≤ n*b^n*‖1-a‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : 0 ≤ b := by linarith
    have hh : ‖a‖^n ≤ b^n := pow_le_pow_left₀ (norm_nonneg _) ha n
    calc ‖1-a^(n+1)‖ = ‖(1-a^n)+a^n*(1-a)‖ := by congr 1; ring
         _ ≤ ‖1-a^n‖+‖a^n*(1-a)‖ := norm_add_le _ _
         _ ≤ n*b^n*‖1-a‖+b^n*‖1-a‖ := by rw [norm_mul,norm_pow]; gcongr
         _ = (n+1:ℕ)*b^n*‖1-a‖ := by push_cast; ring
         _ ≤ (n+1:ℕ)*b^(n+1)*‖1-a‖ := by gcongr; exact Nat.le_succ n

lemma second_gap {a : ℂ} {b : ℝ} (hb : 1 ≤ b) (ha : ‖a‖ ≤ b) (n : ℕ) :
    ‖1-a^n-(n:ℂ)*(1-a)‖ ≤ (n:ℝ)^2*b^n*‖1-a‖^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb0 : 0 ≤ b := by linarith
    calc ‖1-a^(n+1)-((n+1:ℕ):ℂ)*(1-a)‖ =
          ‖(1-a^n-(n:ℂ)*(1-a)) + (a^n-1)*(1-a)‖ := by congr 1; push_cast; ring
         _ ≤ ‖1-a^n-(n:ℂ)*(1-a)‖+‖(a^n-1)*(1-a)‖ := norm_add_le _ _
         _ ≤ (n:ℝ)^2*b^n*‖1-a‖^2 + ((n:ℝ)*b^n*‖1-a‖)*‖1-a‖ := by
           rw [norm_mul,norm_sub_rev (a^n) 1]
           exact add_le_add ih (mul_le_mul_of_nonneg_right (first_gap hb ha n) (norm_nonneg _))
         _ = ((n:ℝ)^2+n)*b^n*‖1-a‖^2 := by ring
         _ ≤ ((n+1:ℕ):ℝ)^2*b^(n+1)*‖1-a‖^2 := by
           gcongr
           · push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
           · exact Nat.le_succ n

lemma tail_bd (z : Index) {b : ℝ} (hb : 1 ≤ b) (ha : ‖w z‖ ≤ b) (n : ℕ) :
    f n z ≤ 2*((n:ℝ)+(n:ℝ)^2*b^n)*g z := by
  have he := (Complex.re_le_norm _).trans (second_gap hb ha n)
  simp only [sub_re,mul_re,natCast_re,natCast_im,zero_mul,sub_zero] at he
  have hh := mul_le_mul_of_nonneg_left (real_gap z) (Nat.cast_nonneg (α:=ℝ) n)
  change _ ≤ (n:ℝ) * ‖1-w z‖^2 at hh
  simp only [f,g,sub_re] at hh ⊢
  linarith
end ReverseLi

open Complex Filter Set
open scoped Topology
namespace ReverseLi
lemma finite_peaks (hg : Summable g) {b : ℝ} (hb : 1 < b) : {z : Index | b ≤ ‖w z‖}.Finite := by
  have he := hg.tendsto_cofinite_zero.eventually_lt_const (sq_pos_of_pos (sub_pos.mpr hb))
  have hn : ∀ᶠ z : Index in cofinite, ‖w z‖ < b := by
    filter_upwards [he] with z hz
    change ‖1-w z‖^2 < (b-1)^2 at hz
    have h1 := norm_sub_le (1:ℂ) (1-w z)
    simp only [sub_sub_cancel,norm_one] at h1
    nlinarith [norm_nonneg (1-w z)]
  simpa [Filter.Eventually,Filter.mem_cofinite,Set.compl_ofPred,not_lt] using hn

lemma eventual_domination (H G : ℝ) {b r : ℝ} (hb : 1 < b) (hr : b < r) :
    ∀ᶠ n : ℕ in atTop, H+2*((n:ℝ)+(n:ℝ)^2*b^n)*G < r^n := by
  have hr1 := hb.trans hr
  have hb0 : 0 < b := by linarith
  have hr0 : 0 < r := by linarith
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hr1
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr1
  have h2 := tendsto_pow_const_div_const_pow_of_one_lt 2 ((one_lt_div hb0).mpr hr)
  have lim : Tendsto (fun n : ℕ => H*(1/r^n)+2*((n:ℝ)/r^n+(n:ℝ)^2/(r/b)^n)*G) atTop (𝓝 0) := by
    simpa using (h0.const_mul H).add (((h1.add h2).const_mul 2).mul_const G)
  filter_upwards [lim.eventually_lt_const zero_lt_one] with n hn
  have he : H+2*((n:ℝ)+(n:ℝ)^2*b^n)*G =
      (H*(1/r^n)+2*((n:ℝ)/r^n+(n:ℝ)^2/(r/b)^n)*G)*r^n := by
    rw [div_pow]; field_simp
  rw [he]
  simpa using mul_lt_mul_of_pos_right hn (pow_pos hr0 n)

lemma reverse_direction (h : ∀ n > 0, 0 < RiemannHypothesis.lambda n) : RiemannHypothesis := by
  classical
  by_contra no
  obtain ⟨z₀,hr⟩ := bad no
  let r := ‖w z₀‖
  let b := (1+r)/2
  have hb : 1 < b := by dsimp [b,r]; linarith
  have hbr : b < r := by dsimp [b,r]; linarith
  have hb0 : 0 ≤ b := by linarith
  have hg := summable_g h
  let S := (finite_peaks hg hb).toFinset
  have hmem (z : Index) : z ∈ S ↔ b ≤ ‖w z‖ := Set.Finite.mem_toFinset _
  have h0 : z₀ ∈ S := (hmem z₀).mpr hbr.le
  let a (i : S) := w i
  have ha (i : S) : a i ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by linarith : 0<b) ((hmem i).mp i.2)))
  obtain ⟨N,hN,hphase⟩ := phase_times a ha
  let v (z : Index) : ℝ := if z∈S then 2 else 0
  have hv : Summable v := summable_of_hasFiniteSupport (S.finite_toSet.subset (by
    intro z hz; change z ∈ S; by_contra he; exact hz (by simp [v,he])))
  let H := ∑' z, v z
  let G := ∑' z, g z
  have hev := hN.eventually (eventual_domination H G hb hbr)
  obtain ⟨k,hnear,hdom,hpos⟩ : ∃ k, (∀ i, ‖a i‖^(N k)/2 ≤ ((a i)^(N k)).re) ∧
      H+2*((N k:ℝ)+(N k:ℝ)^2*b^(N k))*G < r^(N k) ∧ 0 < N k :=
    (hphase.and (hev.and (hN.eventually_gt_atTop 0))).exists
  let n := N k
  let B := 2*((n:ℝ)+(n:ℝ)^2*b^n)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let d (z : Index) : ℝ := if z=z₀ then r^n else 0
  have hd : Summable d := summable_of_ne_finset_zero (s:={z₀}) (fun i hi => by
    have hn : i ≠ z₀ := by simpa using hi
    simp [d,hn])
  have hs := ((hv.sub hd).add (hg.mul_left B))
  have bnd (z : Index) : f n z ≤ (v z-d z) + B*g z := by
    have nn := mul_nonneg hB (g_nonneg z)
    by_cases hz : z∈S
    · have ht := hnear (⟨z,hz⟩ : S)
      change ‖w z‖^n/2 ≤ ((w z)^n).re at ht
      by_cases he : z=z₀
      · subst z
        simp only [v,h0,if_true,d,ite_true,f,sub_re,one_re]
        change 2*(1-(w z₀^n).re) ≤ (2-‖w z₀‖^n)+B*g z₀
        linarith
      · simp only [v,hz,if_true,d,he,if_false,sub_zero,f,sub_re,one_re]
        linarith [pow_nonneg (norm_nonneg (w z)) n]
    · have hn : z ≠ z₀ := fun e => hz (e ▸ h0)
      have hb' : ‖w z‖ ≤ b := le_of_not_ge (fun ht => hz ((hmem z).mpr ht))
      simpa only [v,hz,if_false,d,hn,sub_zero,zero_add] using tail_bd z hb.le hb' n
  have ht := (f_sum h hpos).tsum_le_tsum bnd hs
  rw [(hv.sub hd).tsum_add (hg.mul_left B),hv.tsum_sub hd,tsum_mul_left] at ht
  have de : (∑' z, d z) = r^n := by simp [d]
  rw [de] at ht
  change RiemannHypothesis.lambda n ≤ H-r^n+B*G at ht
  have hh := h n hpos
  change H+B*G < r^n at hdom
  linarith
end ReverseLi

theorem OMA.solution : OMA.R_RiemannHypothesis_li_criterion_R1.H2 :=
  ReverseLi.reverse_direction
