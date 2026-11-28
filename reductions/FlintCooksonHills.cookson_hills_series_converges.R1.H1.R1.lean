import OMAReductions.R_FlintCooksonHills_cookson_hills_series_converges_R1

/-!
The determinant parameters and selection arguments are adapted from OpenAI,
*The irrationality exponent of pi is 2* (2026), under Apache License 2.0.
Source: https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/NumberTheory/PiExponent.
This version exposes the finite exceptional approximation configuration
in the statements and specializes the constants. The three steps choose
admissible parameters, select finitely many approximations with separated
logarithmic weights, and exclude the resulting finite configuration.
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

namespace OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1

def H1 : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ (θ A B C σ : ℚ) (η ε F : ℝ) (m : ℕ),
    let K : ℕ := ⌊(C : ℝ) ^ m⌋₊
    let w : ℝ := ((B : ℝ) ^ m)⁻¹
    let v : ℝ := 2 * K * (θ : ℝ) ^ m * w
    0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
    1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧ (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 ∧
    0 < η ∧ η < 1 ∧ 0 < ε ∧ ε ≤ 1/2 ∧
    ε < ν * ((A : ℝ) * (1-η) - θ) - (1 - θ) ∧ 2 / (θ : ℝ) < F ∧
    ν / F < ε / 3 ∧ 1 ≤ m ∧
    ((Real.log 4 + 4) * F * m + 2 * Real.log 2) / v + 100 * K / w < ε / 3 ∧
    2 < Real.log 2 / 4 * (η^2 * (K : ℝ) * (θ : ℝ)^m / ((m+1 : ℝ) * v * (A : ℝ)^m)) ∧
    0 < (σ : ℝ) ∧ (1 + 3 * (σ : ℝ))^(m+1) * (1/2 : ℝ) < 1 ∧
    (1 + 3 * (σ : ℝ))^m * (K * (θ : ℝ)^m) < 1 ∧ (1 + (σ : ℝ)) * θ < 1

def H2 : Prop :=
  ∀ ν : ℝ, 0 < ν →
    (∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν)) →
    ∀ (m : ℕ) (X D : ℝ), ∃ (p : ℕ → ℤ) (q : ℕ → ℕ), ∀ n < m,
      let w := fun i : ℕ => (Nat.ceil (Real.log (q i)) : ℝ)
      2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-ν) ∧
        X < w n ∧ D * ((List.range n).reverse.map w).prod < w n

def H3 : Prop :=
  ∀ ν : ℝ, 2 < ν → ∀ (θ A B C σ : ℚ) (η ε F : ℝ) (m : ℕ),
    let K : ℕ := ⌊(C : ℝ) ^ m⌋₊
    let w : ℝ := ((B : ℝ) ^ m)⁻¹
    let v : ℝ := 2 * K * (θ : ℝ) ^ m * w
    (0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
    1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧ (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 ∧
    0 < η ∧ η < 1 ∧ 0 < ε ∧ ε ≤ 1/2 ∧
    ε < ν * ((A : ℝ) * (1-η) - θ) - (1 - θ) ∧ 2 / (θ : ℝ) < F ∧
    ν / F < ε / 3 ∧ 1 ≤ m ∧
    ((Real.log 4 + 4) * F * m + 2 * Real.log 2) / v + 100 * K / w < ε / 3 ∧
    2 < Real.log 2 / 4 * (η^2 * (K : ℝ) * (θ : ℝ)^m / ((m+1 : ℝ) * v * (A : ℝ)^m)) ∧
    0 < (σ : ℝ) ∧ (1 + 3 * (σ : ℝ))^(m+1) * (1/2 : ℝ) < 1 ∧
    (1 + 3 * (σ : ℝ))^m * (K * (θ : ℝ)^m) < 1 ∧ (1 + (σ : ℝ)) * θ < 1) →
    let S := (θ : ℝ) + Real.log 4 + Real.log (2*K) + ν + Real.log (200*K)
    let X := max 1 (((Real.log 4 + 4) * m + S) / (ε/3))
    let D := 2 * (m+2 : ℝ)^(m+2) * (1 + (m+2 : ℝ) / σ)^(m+2) *
      (max 1 (max v (1 / θ) / min w 1))^(m+1)
    ∀ (p : ℕ → ℤ) (q : ℕ → ℕ),
      let wt := fun i : ℕ => (Nat.ceil (Real.log (q i)) : ℝ)
      (∀ i < m, 2 ≤ q i ∧ p i ≠ 0 ∧ X < wt i ∧
        D * ((List.range i).reverse.map wt).prod < wt i) →
      ∃ i < m, (q i : ℝ) ^ (-ν) < |Real.pi - (p i : ℝ) / q i|

theorem main : H1 → H2 → H3 → OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1.H1 := by
  intro hpar hselect hexcl ν hν
  by_contra h
  push Not at h
  have hbad (Q : ℕ) : ∃ p : ℤ, ∃ q : ℕ, Q ≤ q ∧
      |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν) := by
    obtain ⟨p, q, hq, he⟩ := h (max Q 2) (le_max_right _ _)
    exact ⟨p, q, le_trans (le_max_left _ _) hq, he.le⟩
  obtain ⟨θ, A, B, C, σ, η, ε, F, m, hm⟩ := hpar ν hν
  have noBlock := hexcl ν hν θ A B C σ η ε F m hm
  let K : ℕ := ⌊(C : ℝ) ^ m⌋₊
  let w : ℝ := ((B : ℝ) ^ m)⁻¹
  let v : ℝ := 2 * K * (θ : ℝ)^m * w
  let S : ℝ := (θ : ℝ) + Real.log 4 + Real.log (2*K) + ν + Real.log (200*K)
  let X : ℝ := max 1 (((Real.log 4 + 4) * m + S) / (ε/3))
  let D : ℝ := 2 * (m+2 : ℝ)^(m+2) * (1 + (m+2 : ℝ) / σ)^(m+2) *
    (max 1 (max v (1 / θ) / min w 1))^(m+1)
  obtain ⟨p, q, hq⟩ := hselect ν (by linarith) hbad m X D
  obtain ⟨i, hi, hlarge⟩ := noBlock p q (fun i hi => by
    obtain ⟨hden, hnum, _, hx, hd⟩ := hq i hi
    exact ⟨hden, hnum, hx, hd⟩)
  exact (not_lt_of_ge (hq i hi).2.2.1) hlarge

end OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1
