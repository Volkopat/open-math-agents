import OMAStatements.S_oeis_a376388
import Mathlib

/-!
Adapted from the Lean proof by the-omega-institute/trureturing at commit
37f55f0e4bc22e4060eceaa6157ffa7641a3fefe, module
D5/S1/Recurrence/Algebraic/PeriodicBoundarySchroder.lean.
Mikhail Kurkov stated the conjecture. The adaptation replaces the project-specific
imports with the needed formal power series facts from Mathlib.
The original formalization is licensed under Apache-2.0.
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

open PowerSeries

namespace OMA.A376388

open OMA.S_oeis_a376388 (P f2 f3)

private noncomputable def S : PowerSeries ℚ :=
  largeSchroderSeries.map (Nat.castRingHom ℚ)

private theorem R_eq : S = 1 + X * S + X * S ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
    largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  simpa only [map_add, map_one, map_mul, map_X, map_pow, S] using h

private theorem R_zero : constantCoeff S = 1 := by
  simp [S, ← coeff_zero_eq_constantCoeff, coeff_map]

private def C (f : ℕ → ℕ) (n d : ℕ) : ℕ := P f n (n + d)

private theorem C_zero (f : ℕ → ℕ) (d : ℕ) : C f 0 d = 1 := by
  simp [C, P]

private theorem C_boundary (f : ℕ → ℕ) (n : ℕ) : C f (n + 1) 0 = C f n 1 := by
  simp [C, P]

private theorem C_step (f : ℕ → ℕ) (n d : ℕ) :
    C f (n + 1) (d + 1) = C f (n + 1) d + C f n (d + 2 + f (d + 1)) := by
  have hm : ¬ n + 1 + (d + 1) ≤ n + 1 := by omega
  unfold C
  rw [P, if_neg hm]
  rw [show n + 1 + (d + 1) - (n + 1) = d + 1 by omega]
  congr 2 <;> omega

/-- Coefficient degree is the outer induction; its hypothesis covers every column. -/
private theorem coefficient_identification (f : ℕ → ℕ) (H : ℕ → PowerSeries ℚ)
    (h0 : ∀ d, constantCoeff (H d) = 1)
    (hb : H 0 = 1 + X * H 1)
    (hs : ∀ d, H (d + 1) = H d + X * H (d + 2 + f (d + 1))) :
    ∀ n d, (C f n d : ℚ) = coeff n (H d) := by
  intro n
  induction n with
  | zero => intro d; simp [C_zero, coeff_zero_eq_constantCoeff, h0]
  | succ n ih =>
    intro d
    induction d with
    | zero =>
      rw [C_boundary, hb]
      simpa using ih 1
    | succ d hd =>
      rw [C_step, Nat.cast_add, hs d, map_add, coeff_succ_X_mul, ← hd, ← ih]

private noncomputable def H2 (d : ℕ) : PowerSeries ℚ :=
  if d % 2 = 0 then (1 + X * S) * S ^ (d / 2) else S ^ (d / 2 + 1)

private theorem H2_even (j : ℕ) : H2 (2 * j) = (1 + X * S) * S ^ j := by
  simp [H2]

private theorem H2_odd (j : ℕ) : H2 (2 * j + 1) = S ^ (j + 1) := by
  have hd : (2 * j + 1) / 2 = j := by omega
  simp [H2, hd]

private theorem H2_system :
    (∀ d, constantCoeff (H2 d) = 1) ∧
    H2 0 = 1 + X * H2 1 ∧
    ∀ d, H2 (d + 1) = H2 d + X * H2 (d + 2 + f2 (d + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    unfold H2
    split_ifs <;> simp [R_zero]
  · simp [H2]
  · intro d
    have hr := Nat.mod_lt d (by decide : 0 < 2)
    have he := Nat.mod_add_div d 2
    rcases (show d % 2 = 0 ∨ d % 2 = 1 by omega) with h | h
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j := ⟨d / 2, by omega⟩
      have hf : f2 (2 * j + 1) = 1 := by simp [f2]
      rw [hf, H2_odd, H2_even]
      rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by omega, H2_odd]
      rw [pow_succ, pow_succ]
      linear_combination S ^ j * R_eq
    · obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 1 := ⟨d / 2, by omega⟩
      have hf : f2 (2 * j + 1 + 1) = 0 := by simp [f2, Nat.add_mod]
      rw [hf, show 2 * j + 1 + 1 = 2 * (j + 1) by omega, H2_even, H2_odd]
      rw [show 2 * j + 1 + 2 + 0 = 2 * (j + 1) + 1 by omega, H2_odd]
      rw [pow_succ]
      ring

private noncomputable def R : PowerSeries ℚ :=
  (PowerSeries.C (1 / 2 : ℚ)) * (S ^ 2 + S)

private theorem R_equations : R - S = X * S * R ∧ S ^ 2 - R = X * S * R := by
  have hc : (2 : PowerSeries ℚ) * PowerSeries.C (1 / 2 : ℚ) = 1 := by
    change PowerSeries.C (2 : ℚ) * PowerSeries.C (1 / 2 : ℚ) = 1
    rw [← map_mul]
    norm_num
  constructor <;> dsimp [R]
  · linear_combination (PowerSeries.C (1 / 2 : ℚ)) * S * R_eq +
      S * hc
  · linear_combination (PowerSeries.C (1 / 2 : ℚ)) * S * R_eq -
      S ^ 2 * hc

private theorem R_constant : constantCoeff R = 1 := by
  norm_num [R, R_zero]

private noncomputable def H3 (d : ℕ) : PowerSeries ℚ :=
  if d = 0 then 1 + X * S else
    if (d - 1) % 3 = 0 then S * R ^ ((d - 1) / 3) else
    if (d - 1) % 3 = 1 then R ^ ((d - 1) / 3 + 1) else S ^ 2 * R ^ ((d - 1) / 3)

private theorem H3_one (j : ℕ) : H3 (3 * j + 1) = S * R ^ j := by
  simp [H3]
private theorem H3_two (j : ℕ) : H3 (3 * j + 2) = R ^ (j + 1) := by
  have hd : (3 * j + 1) / 3 = j := by omega
  simp [H3, show 3 * j + 2 - 1 = 3 * j + 1 by omega, hd]
private theorem H3_three (j : ℕ) : H3 (3 * j + 3) = S ^ 2 * R ^ j := by
  have hd : (3 * j + 2) / 3 = j := by omega
  simp [H3, show 3 * j + 3 - 1 = 3 * j + 2 by omega, hd]

private theorem H3_system :
    (∀ d, constantCoeff (H3 d) = 1) ∧
    H3 0 = 1 + X * H3 1 ∧
    ∀ d, H3 (d + 1) = H3 d + X * H3 (d + 2 + f3 (d + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    unfold H3
    split_ifs <;> simp [R_zero, R_constant]
  · simp [H3]
  · intro d
    cases d with
    | zero => simpa [H3, f3] using R_eq
    | succ d =>
      have hr := Nat.mod_lt d (by decide : 0 < 3)
      have he := Nat.mod_add_div d 3
      rcases (show d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 by omega) with h | h | h
      · obtain ⟨j, rfl⟩ : ∃ j, d = 3 * j := ⟨d / 3, by omega⟩
        have hf : f3 (3 * j + 1 + 1) = 1 := by simp [f3, Nat.add_mod]
        change H3 (3 * j + 1 + 1) = H3 (3 * j + 1) + X * H3 (3 * j + 1 + 2 + f3 (3 * j + 1 + 1))
        rw [hf, show 3 * j + 1 + 1 = 3 * j + 2 by omega, H3_two, H3_one]
        rw [show 3 * j + 1 + 2 + 1 = 3 * (j + 1) + 1 by omega, H3_one, pow_succ]
        linear_combination R ^ j * R_equations.1
      · obtain ⟨j, rfl⟩ : ∃ j, d = 3 * j + 1 := ⟨d / 3, by omega⟩
        have hf : f3 (3 * j + 2 + 1) = 0 := by simp [f3, Nat.add_mod]
        change H3 (3 * j + 2 + 1) = H3 (3 * j + 2) + X * H3 (3 * j + 2 + 2 + f3 (3 * j + 2 + 1))
        rw [hf, show 3 * j + 2 + 1 = 3 * j + 3 by omega, H3_three, H3_two]
        rw [show 3 * j + 2 + 2 + 0 = 3 * (j + 1) + 1 by omega, H3_one, pow_succ]
        linear_combination R ^ j * R_equations.2
      · obtain ⟨j, rfl⟩ : ∃ j, d = 3 * j + 2 := ⟨d / 3, by omega⟩
        have hf : f3 (3 * j + 3 + 1) = 1 := by simp [f3, Nat.add_mod]
        change H3 (3 * j + 3 + 1) = H3 (3 * j + 3) + X * H3 (3 * j + 3 + 2 + f3 (3 * j + 3 + 1))
        rw [hf, show 3 * j + 3 + 1 = 3 * (j + 1) + 1 by omega, H3_one, H3_three]
        rw [show 3 * j + 3 + 2 + 1 = 3 * (j + 1) + 3 by omega, H3_three, pow_succ]
        linear_combination S * R ^ j * R_equations.1

/-- Both periodic shifts in Kurkov's conjecture give A006318, without an index shift. -/
theorem result (n : ℕ) :
    P f2 (n + 1) (n + 1) = Nat.largeSchroder n ∧
    P f3 (n + 1) (n + 1) = Nat.largeSchroder n := by
  have diagonal (f : ℕ → ℕ) (H : ℕ → PowerSeries ℚ)
      (h0 : ∀ d, constantCoeff (H d) = 1)
      (hb : H 0 = 1 + X * H 1)
      (hs : ∀ d, H (d + 1) = H d + X * H (d + 2 + f (d + 1)))
      (h1 : H 1 = S) : P f (n + 1) (n + 1) = Nat.largeSchroder n := by
    have h := coefficient_identification f H h0 hb hs n 1
    rw [h1] at h
    have hp : P f (n + 1) (n + 1) = C f n 1 := by simp [P, C]
    rw [hp]
    exact_mod_cast (show (C f n 1 : ℚ) = (Nat.largeSchroder n : ℚ) by
      simpa [S] using h)
  exact ⟨diagonal f2 H2 H2_system.1 H2_system.2.1 H2_system.2.2 (by simp [H2]),
    diagonal f3 H3 H3_system.1 H3_system.2.1 H3_system.2.2 (by simp [H3])⟩

end OMA.A376388

theorem OMA.solution : type_of% @OMA.S_oeis_a376388.main := by
  intro n
  exact OMA.A376388.result n
