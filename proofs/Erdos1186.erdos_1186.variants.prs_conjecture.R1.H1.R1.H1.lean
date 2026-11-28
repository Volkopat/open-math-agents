import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Erdős 1186: the low-mass G24 certificate and its discrete transfer -/

/-
The grid and bathtub code include material from Chandler Snively, erdos-1186 v1.0.0,
commit 0b0155ead09841892690b9f9c469d1ff0edaff4c, Copyright 2026 Chandler Snively.
The source is https://github.com/dreadpiratechan/erdos-1186/tree/v1.0.0.
The underlying mathematical argument is due to Carlos Toledo.
The adapted portions are distributed under the Apache License, Version 2.0, copied below.
The exact P1186ExData, P1186ExBathLib and P1186ExBathTab sources are credited
at their respective declarations. This version combines the grid transfer and
bathtub profile and adapts their elaboration to the project's pinned Lean.

Upstream NOTICE credits the Formal Conjectures contributors (Google DeepMind)
and Mathlib, each under Apache-2.0. This file uses the merged project ancestor
and pinned Mathlib as imports. The source solver witness is not needed here.


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

namespace OMA.Erdos1186Region2

def digit (word width i : Nat) : Nat :=
  (word >>> (width * i)) &&& ((1 <<< width) - 1)

end OMA.Erdos1186Region2

end

section

/-
Exact G24 data from Chandler Snively, erdos-1186 v1.0.0.
Copyright 2026 Chandler Snively. Apache License 2.0. Mathematics due to Carlos Toledo.
Source SHA-256 a49afc2ec986661afe149e6ccb0c2335b7dd8c0c7678539ae6464371d1597ec0.
Generated by the independent encode_grid24.py.
-/

namespace OMA.Erdos1186Region2

def g24EndpointWord : Nat := 0x8922087210821f87c1e0761c8701b06a198641805e16858150521445013c4e1344c12046108400f03a0d8340ce328c6308c02f8b82a0a024088210801f0781d0701805813048110400f0380d0300a01804000
def g24AlphaWord : Nat := 0x3090789c3642128f8373812140606616908361e0480c03000000606120a8d8362a088480a010080000008060c1c0f0d0240601800000303090280c0100000020000004081005070
def g24BetaWord : Nat := 0x120928890482412030600c30060c01812091202448090120904824120948090480c18060c01800c180c0600c061b600c0c03009048241209048c03036030180c03030180c1810060c0

end OMA.Erdos1186Region2

end

section

namespace OMA.Erdos1186Region2

def g24Endpoint (i : Nat) : Nat :=
  if i ≤ 65 then digit g24EndpointWord 10 i else 1096 - digit g24EndpointWord 10 (130 - i)

def g24Length (i : Nat) : Nat := g24Endpoint (i+1) - g24Endpoint i


def g24Sign (i : Nat) : Bool :=
  let b := g24Endpoint i / 2
  b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
    (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)

def unitArea4 (m : Int) : Nat :=
  if 1 ≤ m ∧ m ≤ 1094 then 4
  else if m = 0 ∨ m = 1095 then 3
  else if m = -1 ∨ m = 1096 then 1
  else 0

def g24Area4 (i j : Nat) : Nat :=
  let p₀ := g24Endpoint i
  let p₁ := g24Endpoint (i+1)
  let q₀ := g24Endpoint j
  let q₁ := g24Endpoint (j+1)
  let m₀ : Int := 2 * (q₀ + 1 : Nat) - p₁ - 1
  let m₁ : Int := 2 * (q₁ : Int) - (p₀ + 1 : Nat) - 1
  if 1 ≤ m₀ ∧ m₁ ≤ 1094 then 4 * g24Length i * g24Length j
  else if m₁ ≤ -2 ∨ 1097 ≤ m₀ then 0
  else ((List.range' (p₀+1) (p₁-p₀)).map fun p : Nat =>
    ((List.range' (q₀+1) (q₁-q₀)).map fun q : Nat => unitArea4 (2 * (q : Int) - p - 1)).sum).sum

end OMA.Erdos1186Region2

end

section

/- Correctness of the corner shortcuts in the exact G24 area calculation. -/

namespace OMA.Erdos1186Region2

def unitGridArea (p₀ p₁ q₀ q₁ : Nat) : Nat :=
  ((List.range' (p₀+1) (p₁-p₀)).map fun p : Nat =>
    ((List.range' (q₀+1) (q₁-q₀)).map fun q : Nat => unitArea4 (2 * (q : Int) - p - 1)).sum).sum

private theorem range_bounds {a b p : Nat} (hp : p ∈ List.range' (a+1) (b-a)) :
    a+1 ≤ p ∧ p ≤ b := by
  have h := List.mem_range'_1.mp hp
  omega

private theorem unitGridArea_const (p₀ p₁ q₀ q₁ c : Nat)
    (h : ∀ p q : Nat, p₀+1 ≤ p → p ≤ p₁ → q₀+1 ≤ q → q ≤ q₁ →
      unitArea4 (2 * (q : Int) - p - 1) = c) :
    unitGridArea p₀ p₁ q₀ q₁ = c * (p₁-p₀) * (q₁-q₀) := by
  unfold unitGridArea
  have inner (p : Nat) (hp : p ∈ List.range' (p₀+1) (p₁-p₀)) :
      ((List.range' (q₀+1) (q₁-q₀)).map fun q : Nat => unitArea4 (2 * (q : Int) - p - 1)).sum =
        (q₁-q₀)*c := by
    obtain ⟨hp₀, hp₁⟩ := range_bounds hp
    have hm : (List.range' (q₀+1) (q₁-q₀)).map (fun q : Nat => unitArea4 (2 * (q : Int) - p - 1)) =
        (List.range' (q₀+1) (q₁-q₀)).map (fun _ => c) := by
      apply List.map_congr_left
      intro q hq
      exact h p q hp₀ hp₁ (range_bounds hq).1 (range_bounds hq).2
    rw [hm, List.map_const', List.sum_replicate_nat, List.length_range']
  have outer := List.map_congr_left (l := List.range' (p₀+1) (p₁-p₀)) inner
  rw [outer, List.map_const', List.sum_replicate_nat, List.length_range']
  ac_rfl

private theorem unitArea4_zero_of_outside (m : Int) (h : m ≤ -2 ∨ 1097 ≤ m) :
    unitArea4 m = 0 := by
  have h₁ : ¬ (1 ≤ m ∧ m ≤ 1094) := by omega
  have h₂ : ¬ (m = 0 ∨ m = 1095) := by omega
  have h₃ : ¬ (m = -1 ∨ m = 1096) := by omega
  simp [unitArea4, h₁, h₂, h₃]

private theorem grid_shortcuts (p₀ p₁ q₀ q₁ : Nat) :
    (let m₀ : Int := 2 * (q₀+1 : Nat) - p₁ - 1
     let m₁ : Int := 2 * (q₁ : Int) - (p₀+1 : Nat) - 1
     if 1 ≤ m₀ ∧ m₁ ≤ 1094 then 4 * (p₁-p₀) * (q₁-q₀)
     else if m₁ ≤ -2 ∨ 1097 ≤ m₀ then 0
     else unitGridArea p₀ p₁ q₀ q₁) = unitGridArea p₀ p₁ q₀ q₁ := by
  dsimp only
  split
  · rename_i h
    symm
    apply unitGridArea_const
    intro p q hp₀ hp₁ hq₀ hq₁
    have h' : 1 ≤ 2 * (q : Int) - p - 1 ∧ 2 * (q : Int) - p - 1 ≤ 1094 := by omega
    simp [unitArea4, h']
  · split
    · rename_i h
      have h' : unitGridArea p₀ p₁ q₀ q₁ = 0 * (p₁-p₀) * (q₁-q₀) := by
        apply unitGridArea_const
        intro p q hp₀ hp₁ hq₀ hq₁
        apply unitArea4_zero_of_outside
        omega
      simpa using h'.symm
    · rfl

theorem g24Area4_eq_unitGridArea (i j : Nat) :
    g24Area4 i j = unitGridArea (g24Endpoint i) (g24Endpoint (i+1))
      (g24Endpoint j) (g24Endpoint (j+1)) :=
  grid_shortcuts (g24Endpoint i) (g24Endpoint (i+1)) (g24Endpoint j) (g24Endpoint (j+1))

end OMA.Erdos1186Region2

end

section

namespace OMA.Erdos1186Region2

open Finset
open scoped BigOperators

def cellCount : ℕ := 130

noncomputable def g24Mass (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range cellCount, (g24Length i : ℝ) / 1096 * y i

end OMA.Erdos1186Region2

end

section

namespace OMA.Erdos1186Region2

open Finset
open scoped BigOperators

noncomputable def g24RealAlpha (i : ℕ) : ℝ := (digit g24AlphaWord 9 (min i (129-i)) : ℝ) / 300304
noncomputable def g24RealBeta (i : ℕ) : ℝ := (digit g24BetaWord 9 (min i (129-i)) : ℝ) / 1801824

noncomputable def pairObjective (i j : ℕ) (u v : ℝ) : ℝ :=
  let p := (g24Length i : ℝ) * (g24Length j : ℝ) / 1096^2 * (u*v)
  let inside := (g24Area4 i j : ℝ) / (4 * 1096^2)
  let outside := (g24Length i : ℝ) * (g24Length j : ℝ) / 1096^2 - inside
  if g24Sign i = g24Sign j then max 0 (p-outside) else max (-inside) (-p)

noncomputable def g24Objective (y : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range cellCount, (g24RealAlpha i * y i + g24RealBeta i * (y i)^2)) +
      ∑ i ∈ range cellCount, ∑ j ∈ range cellCount, pairObjective i j (y i) (y j)

end OMA.Erdos1186Region2

end

section

/-
Numerical G24 bathtub tables from Chandler Snively, erdos-1186 v1.0.0.
Copyright 2026 Chandler Snively. Apache License, Version 2.0.
See the license and attribution above.
Source: lean/Erdos/Proofs/P1186ExBathTab.lean
Pinned SHA-256: 5338fdc2a0465f2824a677ab60438edfd1275b2712a413837992c93b692499a8
The arguments underlying these data are due to Carlos Toledo.
-/

namespace OMA.Erdos1186G24Profile

def nuTab24 : List Int := [56, 40, 32, 16, 8, 0, 0, 8, 0, 0, 8, 16, 40, 36, 24, 12, 0, 0, 12, 24, 36, 52, 60, 28, 16, 12, 8, 0, 0, 8, 16, 20, 36, 68, 84, 108, 108, 84, 36, 24, 12, 0, 0, 12, 24, 36, 60, 108, 132, 180, 204, 192, 160, 144, 112, 110, 124, 148, 132, 108, 78, 60, 24, 12, 0, 0, 12, 24, 60, 78, 108, 132, 148, 124, 110, 112, 144, 160, 192, 204, 180, 132, 108, 60, 36, 24, 12, 0, 0, 12, 24, 36, 84, 108, 108, 84, 68, 36, 20, 16, 8, 0, 0, 8, 12, 16, 28, 60, 52, 36, 24, 12, 0, 0, 12, 24, 36, 40, 16, 8, 0, 0, 8, 0, 0, 8, 16, 32, 40, 56]
def tTab24 : List Nat := [3, 3, 9, 3, 3, 3, 3, 6, 3, 3, 3, 3, 3, 6, 2, 2, 2, 2, 2, 2, 3, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 8, 3, 3, 3, 3, 6, 6, 6, 8, 2, 8, 2, 2, 2, 2, 2, 2, 2, 2, 8, 2, 8, 6, 6, 6, 3, 3, 3, 3, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 8, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 3, 2, 2, 2, 2, 2, 2, 6, 3, 3, 3, 3, 3, 6, 3, 3, 3, 3, 9, 3, 3]

end OMA.Erdos1186G24Profile

end

section

/-
Pure integer implementation of the PRS profile and the G24 bathtub checks.
The formulas are from Snively's Apache-licensed `P1186ExBathFU.lean`,
`P1186ExBathH2.lean`, and `P1186ExBathChk.lean` in release v1.0.0,
formalizing Carlos Toledo's argument. The grid uses the audited packed G24 data.
-/

namespace OMA.Erdos1186G24Profile

open OMA.Erdos1186Region2

def unitSign (k : Nat) : Int :=
  let b := k / 2
  if b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
    (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
  then 1 else -1

private def segment (a b k : Nat) : Nat := min b k - min a k

def signPrefix (k : Nat) : Int :=
  (segment 0 56 k : Int) - segment 56 68 k + segment 68 124 k - segment 124 198 k +
  segment 198 316 k - segment 316 548 k + segment 548 780 k - segment 780 898 k +
  segment 898 972 k - segment 972 1028 k + segment 1028 1040 k - segment 1040 1096 k

def midpointSignDiff (k : Nat) : Int := (unitSign (k/2+548) - unitSign (k/2)) / 2
def columnIntercept (k : Nat) : Int := if k < 548 then signPrefix (2*k) else -signPrefix (2*(k-548))
def columnSlope (k : Nat) : Int := if k < 548 then unitSign (2*k) else -unitSign (2*(k-548))

def profileA (k : Nat) : Int := -unitSign k *
  (signPrefix (k/2+548) - signPrefix (k/2) + (k%2 : Nat)*midpointSignDiff k + columnIntercept k)

def profileB (k : Nat) : Int := -unitSign k * (midpointSignDiff k + 2*columnSlope k)

def profileMin (k : Nat) : Int := min (profileA k) (profileA k + profileB k)
def profileAbsSlope (k : Nat) : Nat := (profileB k).natAbs

def threshold (i : Nat) : Int := nuTab24[i]?.getD 0
def slopeCap (i : Nat) : Nat := tTab24[i]?.getD 0

def levelPieces (i : Nat) : List (Nat × Nat) :=
  (List.range' (g24Endpoint i) (g24Length i)).map fun k =>
    ((profileMin k - threshold i).toNat, profileAbsSlope k)

def slopeNumerator (pieces : List (Nat × Nat)) (c : Nat) : Nat :=
  (pieces.map fun (d,s) => if d ≤ c ∧ c < d+s then 6/s else 0).sum

def cellCheck (i : Nat) : Bool :=
  let lo := g24Endpoint i
  let L := g24Length i
  let ν := threshold i
  let T := slopeCap i
  let pieces := levelPieces i
  decide (0 < L ∧ g24Endpoint (i+1) ≤ 1096 ∧ 0 < T) &&
  decide ((digit g24AlphaWord 9 (min i (129-i)) : Int)*(1096*2192) ≤ (L : Int)*ν*300304) &&
  decide (digit g24BetaWord 9 (min i (129-i))*(4*1096^2)*T ≤ 6*L^2*1801824) &&
  (List.range' lo L).all (fun k => decide (ν ≤ profileMin k)) &&
  pieces.all (fun (d,s) => decide (0 < s ∧ 6 % s = 0 ∧ d+s ≤ 3*L)) &&
  (List.range (3*L)).all (fun c => decide (slopeNumerator pieces c ≤ T))

def cellCheckRange (a b : Nat) : Bool := (List.range' a (b-a)).all cellCheck

def prefixStepCheck (k : Nat) : Bool := decide (signPrefix (k+1) = signPrefix k + unitSign k)

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk0 : (List.range' 0 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk8 : (List.range' 8 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk16 : (List.range' 16 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk24 : (List.range' 24 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk32 : (List.range' 32 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk40 : (List.range' 40 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk48 : (List.range' 48 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk56 : (List.range' 56 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk64 : (List.range' 64 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk72 : (List.range' 72 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk80 : (List.range' 80 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk88 : (List.range' 88 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk96 : (List.range' 96 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk104 : (List.range' 104 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk112 : (List.range' 112 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk120 : (List.range' 120 8).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem cellChunk128 : (List.range' 128 2).all cellCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk0 : (List.range' 0 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk128 : (List.range' 128 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk256 : (List.range' 256 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk384 : (List.range' 384 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk512 : (List.range' 512 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk640 : (List.range' 640 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk768 : (List.range' 768 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk896 : (List.range' 896 128).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

set_option maxRecDepth 10000 in
theorem prefixStepChunk1024 : (List.range' 1024 72).all prefixStepCheck = true := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

namespace OMA.Erdos1186G24Profile

private theorem fromChunk {check : Nat → Bool} {a k i : Nat}
    (h : (List.range' a k).all check = true) (ha : a ≤ i) (hk : i < a+k) :
    check i = true := List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨ha, hk⟩)

theorem cellChecks (i : Nat) (hi : i < 130) : cellCheck i = true := by
  by_cases h8 : i < 8
  · exact fromChunk cellChunk0 (Nat.zero_le i) h8
  by_cases h16 : i < 16
  · exact fromChunk cellChunk8 (Nat.le_of_not_gt h8) h16
  by_cases h24 : i < 24
  · exact fromChunk cellChunk16 (Nat.le_of_not_gt h16) h24
  by_cases h32 : i < 32
  · exact fromChunk cellChunk24 (Nat.le_of_not_gt h24) h32
  by_cases h40 : i < 40
  · exact fromChunk cellChunk32 (Nat.le_of_not_gt h32) h40
  by_cases h48 : i < 48
  · exact fromChunk cellChunk40 (Nat.le_of_not_gt h40) h48
  by_cases h56 : i < 56
  · exact fromChunk cellChunk48 (Nat.le_of_not_gt h48) h56
  by_cases h64 : i < 64
  · exact fromChunk cellChunk56 (Nat.le_of_not_gt h56) h64
  by_cases h72 : i < 72
  · exact fromChunk cellChunk64 (Nat.le_of_not_gt h64) h72
  by_cases h80 : i < 80
  · exact fromChunk cellChunk72 (Nat.le_of_not_gt h72) h80
  by_cases h88 : i < 88
  · exact fromChunk cellChunk80 (Nat.le_of_not_gt h80) h88
  by_cases h96 : i < 96
  · exact fromChunk cellChunk88 (Nat.le_of_not_gt h88) h96
  by_cases h104 : i < 104
  · exact fromChunk cellChunk96 (Nat.le_of_not_gt h96) h104
  by_cases h112 : i < 112
  · exact fromChunk cellChunk104 (Nat.le_of_not_gt h104) h112
  by_cases h120 : i < 120
  · exact fromChunk cellChunk112 (Nat.le_of_not_gt h112) h120
  by_cases h128 : i < 128
  · exact fromChunk cellChunk120 (Nat.le_of_not_gt h120) h128
  exact fromChunk cellChunk128 (Nat.le_of_not_gt h128) hi

theorem prefixStepChecks (i : Nat) (hi : i < 1096) : prefixStepCheck i = true := by
  by_cases h128 : i < 128
  · exact fromChunk prefixStepChunk0 (Nat.zero_le i) h128
  by_cases h256 : i < 256
  · exact fromChunk prefixStepChunk128 (Nat.le_of_not_gt h128) h256
  by_cases h384 : i < 384
  · exact fromChunk prefixStepChunk256 (Nat.le_of_not_gt h256) h384
  by_cases h512 : i < 512
  · exact fromChunk prefixStepChunk384 (Nat.le_of_not_gt h384) h512
  by_cases h640 : i < 640
  · exact fromChunk prefixStepChunk512 (Nat.le_of_not_gt h512) h640
  by_cases h768 : i < 768
  · exact fromChunk prefixStepChunk640 (Nat.le_of_not_gt h640) h768
  by_cases h896 : i < 896
  · exact fromChunk prefixStepChunk768 (Nat.le_of_not_gt h768) h896
  by_cases h1024 : i < 1024
  · exact fromChunk prefixStepChunk896 (Nat.le_of_not_gt h896) h1024
  exact fromChunk prefixStepChunk1024 (Nat.le_of_not_gt h1024) hi

theorem signPrefix_succ (k : Nat) (hk : k < 1096) :
    signPrefix (k+1) = signPrefix k + unitSign k := of_decide_eq_true (prefixStepChecks k hk)

theorem signPrefix_zero : signPrefix 0 = 0 := by decide +kernel

theorem signPrefix_total : signPrefix 1096 = 0 := by decide +kernel

end OMA.Erdos1186G24Profile

end

section

/-
Copyright 2026 Chandler Snively.
Apache License, Version 2.0. See the license and attribution above.

Adapted from dreadpiratechan/erdos-1186 v1.0.0,
commit 0b0155ead09841892690b9f9c469d1ff0edaff4c.
Source: lean/Erdos/Proofs/P1186ExBathLib.lean
Source SHA-256: 08829d4f0ce2292f21a9567f81d57d4248f392229eab0cd8c6b8f0d0cf9c7550
The underlying argument is due to Carlos Toledo.
Changes: narrow imports, separate namespace, pinned Lean compatibility.
-/

/-
# Erdos 1186 - bathtub library for `BathOK` (generic lemmas, no numbers)

Formalises the proof claimed on erdosproblems.com/1186 (Proof claims, 2026-10-05, unrefereed); the mathematics is its
author's.  This module holds the number-free tools for Lemma 2 (the bathtub inequality): a discrete layer-cake lemma, an
arithmetic-progression counting lemma, and an interpolation lemma for the piecewise-linear level-count function.
-/

namespace OMA.Erdos1186BathtubLib

open Finset

/-- Discrete bathtub (layer cake): if `#{x ∈ I : g x < t} ≤ ρ t + κ` for all `t ≥ 0` and `g ≥ 0` on `I`, then every
`S ⊆ I` has `∑_S g ≥ (|S| - κ)₊² / (2ρ)`. -/
theorem bathtub {ι : Type*} [DecidableEq ι] (I : Finset ι) (g : ι → ℝ) (hg : ∀ x ∈ I, 0 ≤ g x)
    (ρ κ : ℝ) (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hcount : ∀ t : ℝ, 0 ≤ t → ((I.filter fun x => g x < t).card : ℝ) ≤ ρ * t + κ) :
    ∀ S : Finset ι, S ⊆ I → (max ((S.card : ℝ) - κ) 0) ^ 2 / (2 * ρ) ≤ ∑ x ∈ S, g x := by
  intro S
  induction' hk : S.card with k ih generalizing S
  · intro _
    have hS : S = ∅ := Finset.card_eq_zero.mp hk
    subst hS
    simp only [Nat.cast_zero, zero_sub, Finset.sum_empty]
    have : max (-κ) 0 = 0 := max_eq_right (by linarith)
    rw [this]; simp
  · intro hSI
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hk]; exact Nat.succ_pos k
    obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image S g hne
    have hcard' : (S.erase xs).card = k := by
      rw [Finset.card_erase_of_mem hxs, hk]; rfl
    have hsub' : S.erase xs ⊆ I := (Finset.erase_subset _ _).trans hSI
    have ih' := ih (S.erase xs) hcard' hsub'
    have hgx : 0 ≤ g xs := hg xs (hSI hxs)
    -- ρ g(xs) + κ ≥ k + 1
    have hlow : ((k + 1 : ℕ) : ℝ) ≤ ρ * g xs + κ := by
      by_contra hcon
      push Not at hcon
      set η : ℝ := (((k + 1 : ℕ) : ℝ) - (ρ * g xs + κ)) / (2 * ρ) with hη
      have hηpos : 0 < η := by
        rw [hη]; apply div_pos; linarith; linarith
      have ht0 : 0 ≤ g xs + η := by linarith
      have hc := hcount (g xs + η) ht0
      have hsubf : S ⊆ I.filter fun x => g x < g xs + η := by
        intro x hx
        rw [Finset.mem_filter]
        exact ⟨hSI hx, by have := hmax x hx; linarith⟩
      have h1 : ((S.card : ℕ) : ℝ) ≤ ((I.filter fun x => g x < g xs + η).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubf
      rw [hk] at h1
      have h2 : ρ * (g xs + η) + κ < ((k + 1 : ℕ) : ℝ) := by
        have : ρ * η = (((k + 1 : ℕ) : ℝ) - (ρ * g xs + κ)) / 2 := by
          rw [hη]; field_simp
        nlinarith
      linarith
    rw [← Finset.add_sum_erase S g hxs]
    set A := max (((k + 1 : ℕ) : ℝ) - κ) 0 with hA
    set B := max ((k : ℝ) - κ) 0 with hB
    have hAle : A ≤ ρ * g xs := by
      rw [hA]; apply max_le; linarith; positivity
    have hAB : A ^ 2 ≤ B ^ 2 + 2 * A := by
      rcases le_total ((k : ℝ) - κ) 0 with h | h
      · have hB0 : B = 0 := by rw [hB]; exact max_eq_right h
        rw [hB0]
        rcases le_total ((k : ℝ) + 1 - κ) 0 with h' | h'
        · have : A = 0 := by rw [hA]; push_cast; exact max_eq_right h'
          rw [this]; norm_num
        · have : A = (k : ℝ) + 1 - κ := by rw [hA]; push_cast; exact max_eq_left h'
          rw [this]; nlinarith
      · have hB' : B = (k : ℝ) - κ := by rw [hB]; exact max_eq_left h
        have hA' : A = (k : ℝ) + 1 - κ := by rw [hA]; push_cast; exact max_eq_left (by linarith)
        rw [hB', hA']; nlinarith
    have hfin : A ^ 2 / (2 * ρ) ≤ B ^ 2 / (2 * ρ) + g xs := by
      have h3 : A ^ 2 / (2 * ρ) ≤ (B ^ 2 + 2 * A) / (2 * ρ) :=
        div_le_div_of_nonneg_right hAB (by positivity)
      have h4 : (B ^ 2 + 2 * A) / (2 * ρ) = B ^ 2 / (2 * ρ) + A / ρ := by field_simp
      have h5 : A / ρ ≤ g xs := by rw [div_le_iff₀ hρ]; linarith
      linarith
    linarith

/-- Counting the points of an arithmetic progression `j ↦ u j` (`|u j - u j'| = s |j - j'|`) in a window `[lo, hi)`. -/
theorem card_ap_le (w : ℕ) (u : ℕ → ℝ) (s lo hi : ℝ) (hs : 0 < s)
    (hu : ∀ j j', |u j - u j'| = s * |(j : ℝ) - j'|) :
    (((Icc 1 w).filter (fun j => lo ≤ u j ∧ u j < hi)).card : ℝ) ≤ max 0 ((hi - lo) / s) + 1 := by
  set T := (Icc 1 w).filter (fun j => lo ≤ u j ∧ u j < hi) with hT
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h]; simp only [Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ max 0 ((hi - lo) / s) := le_max_left _ _
    linarith
  · have ha := T.min'_mem h
    have hb := T.max'_mem h
    set a := T.min' h with ha_def
    set b := T.max' h with hb_def
    have hab : a ≤ b := T.min'_le _ hb
    have hsub : T ⊆ Icc a b := fun x hx => mem_Icc.2 ⟨T.min'_le x hx, T.le_max' x hx⟩
    have hcard : T.card ≤ b + 1 - a := by
      have := Finset.card_le_card hsub
      simpa using this
    have hcardR : (T.card : ℝ) ≤ (b : ℝ) + 1 - a := by
      have : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - a := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this]; exact_mod_cast hcard
    have hmb := (Finset.mem_filter.mp hb).2
    have hma := (Finset.mem_filter.mp ha).2
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hd : s * ((b : ℝ) - a) = |u b - u a| := by
      rw [hu b a, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b : ℝ) - a)]
    have hlt : |u b - u a| < hi - lo := by
      rw [abs_lt]; constructor <;> linarith [hmb.1, hmb.2, hma.1, hma.2]
    have hpos : 0 < hi - lo := by
      have := abs_nonneg (u b - u a); linarith
    have : ((b : ℝ) - a) < (hi - lo) / s := by
      rw [lt_div_iff₀ hs]; linarith
    have h2 : (hi - lo) / s ≤ max 0 ((hi - lo) / s) := le_max_right _ _
    linarith

/-- The clamp `min 1 (max 0 ((z - d) / s))`. -/
noncomputable def ramp (d s z : ℝ) : ℝ := min 1 (max 0 ((z - d) / s))

/-- `ramp` with integer break-points is affine between consecutive integers. -/
theorem ramp_interp (d s : ℤ) (hs : 0 < s) (c : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ramp d s ((c : ℝ) + θ) = (1 - θ) * ramp d s (c : ℝ) + θ * ramp d s ((c : ℝ) + 1) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold ramp
  by_cases ha : (c : ℤ) + 1 ≤ d
  · have haR : (c : ℝ) + 1 ≤ d := by exact_mod_cast ha
    have e1 : max 0 (((c : ℝ) + θ - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    have e2 : max 0 (((c : ℝ) - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    have e3 : max 0 (((c : ℝ) + 1 - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    rw [e1, e2, e3]; simp
  · by_cases hb : d + s ≤ (c : ℤ)
    · have hbR : (d : ℝ) + s ≤ c := by exact_mod_cast hb
      have e1 : min 1 (max 0 (((c : ℝ) + θ - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      have e2 : min 1 (max 0 (((c : ℝ) - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      have e3 : min 1 (max 0 (((c : ℝ) + 1 - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      rw [e1, e2, e3]; ring
    · have hd : d ≤ (c : ℤ) := by omega
      have hcs : (c : ℤ) + 1 ≤ d + s := by omega
      have hdR : (d : ℝ) ≤ c := by exact_mod_cast hd
      have hcsR : (c : ℝ) + 1 ≤ d + s := by exact_mod_cast hcs
      have key : ∀ z : ℝ, (c : ℝ) ≤ z → z ≤ (c : ℝ) + 1 →
          min 1 (max 0 ((z - d) / s)) = (z - d) / s := by
        intro z hz1 hz2
        have hnn : 0 ≤ (z - d) / s := div_nonneg (by linarith) hsR.le
        have hle : (z - d) / s ≤ 1 := by rw [div_le_iff₀ hsR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [key _ (by linarith) (by linarith), key _ le_rfl (by linarith), key _ (by linarith) le_rfl]
      field_simp
      ring

/-- Level-count inequality between integers extends to all reals `τ ≥ 0`. -/
theorem ramp_sum_le {ι : Type*} (I : Finset ι) (d s : ι → ℤ) (hs : ∀ p ∈ I, 0 < s p) (ρ : ℝ)
    (h : ∀ c : ℕ, ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∑ p ∈ I, ramp (d p) (s p) τ ≤ ρ * τ := by
  set c := ⌊τ⌋₊ with hc
  set θ := τ - c with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; have := Nat.floor_le hτ; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; have := Nat.lt_floor_add_one τ; linarith
  have hτ' : τ = (c : ℝ) + θ := by rw [hθ]; ring
  have e : ∑ p ∈ I, ramp (d p) (s p) τ
      = (1 - θ) * ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) + θ * ∑ p ∈ I, ramp (d p) (s p) ((c : ℝ) + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hτ']; exact ramp_interp (d p) (s p) (hs p hp) c θ hθ0 hθ1
  rw [e]
  have h1 := h c
  have h2 := h (c + 1)
  push_cast at h2
  nlinarith

theorem ramp_nonneg (d s z : ℝ) : 0 ≤ ramp d s z := by
  unfold ramp; exact le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (d s z : ℝ) : ramp d s z ≤ 1 := by
  unfold ramp; exact min_le_left _ _

theorem ramp_zero_of (d s : ℤ) (hs : 0 < s) (hd : 0 ≤ d) : ramp d s 0 = 0 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  unfold ramp
  have : max 0 (((0 : ℝ) - d) / s) = 0 :=
    max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
  rw [this]; norm_num

theorem ramp_one_of (d s : ℤ) (hs : 0 < s) (z : ℝ) (h : (d : ℝ) + s ≤ z) : ramp d s z = 1 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold ramp
  apply min_eq_left
  apply le_max_of_le_right
  rw [le_div_iff₀ hsR]; linarith

/-- one step of the level-count function: it rises by `1/s` while the level is inside the ramp. -/
theorem ramp_succ (d s : ℤ) (hs : 0 < s) (c : ℕ) :
    ramp d s ((c : ℝ) + 1) = ramp d s (c : ℝ) + (if d ≤ (c : ℤ) ∧ (c : ℤ) < d + s then 1 / (s : ℝ) else 0) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases ha : (c : ℤ) + 1 ≤ d
  · have haR : (c : ℝ) + 1 ≤ d := by exact_mod_cast ha
    have e1 : ramp d s ((c : ℝ) + 1) = 0 := by
      unfold ramp
      have : max 0 ((((c : ℝ) + 1) - d) / s) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
      rw [this]; norm_num
    have e2 : ramp d s (c : ℝ) = 0 := by
      unfold ramp
      have : max 0 (((c : ℝ) - d) / s) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
      rw [this]; norm_num
    have e3 : ¬ (d ≤ (c : ℤ) ∧ (c : ℤ) < d + s) := by omega
    rw [e1, e2, if_neg e3]; ring
  · by_cases hb : d + s ≤ (c : ℤ)
    · have hbR : (d : ℝ) + s ≤ c := by exact_mod_cast hb
      rw [ramp_one_of d s hs _ (by linarith), ramp_one_of d s hs _ hbR]
      have e3 : ¬ (d ≤ (c : ℤ) ∧ (c : ℤ) < d + s) := by omega
      rw [if_neg e3]; ring
    · have hd : d ≤ (c : ℤ) := by omega
      have hcs : (c : ℤ) + 1 ≤ d + s := by omega
      have hdR : (d : ℝ) ≤ c := by exact_mod_cast hd
      have hcsR : (c : ℝ) + 1 ≤ d + s := by exact_mod_cast hcs
      have key : ∀ z : ℝ, (c : ℝ) ≤ z → z ≤ (c : ℝ) + 1 →
          ramp d s z = (z - d) / s := by
        intro z hz1 hz2
        unfold ramp
        have hnn : 0 ≤ (z - d) / s := div_nonneg (by linarith) hsR.le
        have hle : (z - d) / s ≤ 1 := by rw [div_le_iff₀ hsR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [key _ (by linarith) le_rfl, key _ le_rfl (by linarith), if_pos ⟨hd, by omega⟩]
      field_simp
      ring

/-- the slope bound at integer levels gives the level-count bound `∑ ramp ≤ ρ c` at every integer `c`. -/
theorem level_count {ι : Type*} (I : Finset ι) (d s : ι → ℤ) (hs : ∀ p ∈ I, 0 < s p) (hd : ∀ p ∈ I, 0 ≤ d p)
    (K : ℕ) (hK : ∀ p ∈ I, d p + s p ≤ (K : ℤ)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hinc : ∀ c : ℕ, c < K →
      ∑ p ∈ I, (if d p ≤ (c : ℤ) ∧ (c : ℤ) < d p + s p then 1 / (s p : ℝ) else 0) ≤ ρ) :
    ∀ c : ℕ, ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c := by
  have step : ∀ c : ℕ, c ≤ K → ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c := by
    intro c
    induction c with
    | zero =>
      intro _
      have : ∑ p ∈ I, ramp (d p) (s p) ((0 : ℕ) : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        push_cast
        exact ramp_zero_of _ _ (hs p hp) (hd p hp)
      rw [this]; simp
    | succ c ih =>
      intro hc
      have h1 := ih (by omega)
      have h2 := hinc c (by omega)
      have e : ∑ p ∈ I, ramp (d p) (s p) (((c + 1 : ℕ)) : ℝ)
          = ∑ p ∈ I, ramp (d p) (s p) (c : ℝ)
            + ∑ p ∈ I, (if d p ≤ (c : ℤ) ∧ (c : ℤ) < d p + s p then 1 / (s p : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        push_cast
        exact ramp_succ (d p) (s p) (hs p hp) c
      rw [e]; push_cast; nlinarith
  intro c
  by_cases hc : c ≤ K
  · exact step c hc
  · push Not at hc
    have hall : ∀ c' : ℕ, K ≤ c' → ∑ p ∈ I, ramp (d p) (s p) (c' : ℝ) = (I.card : ℝ) := by
      intro c' hc'
      have : ∀ p ∈ I, ramp (d p) (s p) (c' : ℝ) = 1 := by
        intro p hp
        apply ramp_one_of _ _ (hs p hp)
        have h1 := hK p hp
        have h2 : ((d p + s p : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1
        have h3 : (K : ℝ) ≤ c' := by exact_mod_cast hc'
        push_cast at h2
        linarith
      rw [Finset.sum_congr rfl this]; simp
    rw [hall c hc.le]
    have := step K le_rfl
    rw [hall K le_rfl] at this
    have hKc : (K : ℝ) ≤ c := by exact_mod_cast hc.le
    nlinarith

/-- number of points of an arithmetic progression below `t`, compared with the ramp. -/
theorem piece_count (w : ℕ) (hw : 1 ≤ w) (u : ℕ → ℝ) (d s : ℤ) (hs : 0 < s)
    (hu : ∀ j j', |u j - u j'| = (s : ℝ) * |(j : ℝ) - j'|)
    (hlo : ∀ j ∈ Icc 1 w, (d : ℝ) * w ≤ u j) (t : ℝ) :
    (((Icc 1 w).filter (fun j => u j < t)).card : ℝ) ≤ (w : ℝ) * ramp d s (t / w) + 1 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  set F := (Icc 1 w).filter (fun j => u j < t) with hF
  have h1 : (F.card : ℝ) ≤ w := by
    have : F.card ≤ (Icc 1 w).card := Finset.card_filter_le _ _
    have h' : F.card ≤ w := by simpa using this
    exact_mod_cast h'
  have h2 : (F.card : ℝ) ≤ max 0 ((t - d * w) / s) + 1 := by
    have hsub : F ⊆ (Icc 1 w).filter (fun j => (d : ℝ) * w ≤ u j ∧ u j < t) := by
      intro j hj
      rw [hF, Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨hj.1, hlo j hj.1, hj.2⟩
    have hc : (F.card : ℝ) ≤ (((Icc 1 w).filter (fun j => (d : ℝ) * w ≤ u j ∧ u j < t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have := card_ap_le w u (s : ℝ) ((d : ℝ) * w) t hsR hu
    linarith
  have hr0 : 0 ≤ ramp d s (t / w) := ramp_nonneg _ _ _
  have hY : ((t / w) - d) / s = ((t - d * w) / s) / w := by field_simp
  rcases le_or_gt ((t - d * w) / s) 0 with hY0 | hY0
  · have : max 0 ((t - d * w) / s) = 0 := max_eq_left hY0
    rw [this] at h2
    nlinarith
  · rw [max_eq_right hY0.le] at h2
    by_cases hYw : (t - d * w) / s ≤ w
    · have hr : ramp d s (t / w) = ((t - d * w) / s) / w := by
        unfold ramp
        rw [hY]
        have hnn : 0 ≤ ((t - d * w) / s) / w := div_nonneg hY0.le hwR.le
        have hle : ((t - d * w) / s) / w ≤ 1 := by rw [div_le_iff₀ hwR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [hr]
      have : (w : ℝ) * (((t - d * w) / s) / w) = (t - d * w) / s := by field_simp
      rw [this]; exact h2
    · push Not at hYw
      have hr : ramp d s (t / w) = 1 := by
        unfold ramp
        rw [hY]
        have : 1 ≤ ((t - d * w) / s) / w := by rw [le_div_iff₀ hwR]; linarith
        rw [max_eq_right (by linarith)]
        exact min_eq_left this
      rw [hr]; linarith

end OMA.Erdos1186BathtubLib

end

section

/-
The threshold-count and error-budget steps in the discrete Erdős 1186 bathtub
estimate. These interfaces isolate the arithmetic of the PRS profile and grid.
The constants come from Snively's `P1186ExBathCell.lean`, particularly
`cell_count`, `cell_core`, and `cell_sound` in `erdos-1186` v1.0.0.
-/

namespace OMA.Erdos1186BathtubTransfer

open Finset
open scoped BigOperators
open OMA.Erdos1186BathtubLib

theorem sum_piece_counts {ι : Type*} (P : Finset ι) (w : ℕ) (hw : 1 ≤ w)
    (u : ι → ℕ → ℝ) (d s : ι → ℤ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hs : ∀ p ∈ P, 0 < s p) (hd : ∀ p ∈ P, 0 ≤ d p)
    (K : ℕ) (hK : ∀ p ∈ P, d p + s p ≤ (K : ℤ))
    (hstep : ∀ c : ℕ, c < K →
      (∑ p ∈ P, if d p ≤ (c : ℤ) ∧ (c : ℤ) < d p + s p then 1 / (s p : ℝ) else 0) ≤ ρ)
    (hu : ∀ p ∈ P, ∀ j j', |u p j - u p j'| = (s p : ℝ) * |(j : ℝ) - j'|)
    (hlo : ∀ p ∈ P, ∀ j ∈ Icc 1 w, (d p : ℝ) * w ≤ u p j)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ p ∈ P, (((Icc 1 w).filter (fun j => u p j < t)).card : ℝ)) ≤ ρ*t + P.card := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hr := ramp_sum_le P d s hs ρ (level_count P d s hs hd K hK ρ hρ hstep)
    (t/w) (div_nonneg ht hwR.le)
  have hsum := sum_le_sum (fun p hp => piece_count w hw (u p) (d p) (s p)
    (hs p hp) (hu p hp) (hlo p hp) t)
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one] at hsum
  have hscale := mul_le_mul_of_nonneg_left hr hwR.le
  have heq : (w : ℝ) * (ρ * (t/w)) = ρ*t := by field_simp
  rw [heq] at hscale
  exact hsum.trans (add_le_add_left hscale _)

theorem cell_lower_bound {ι : Type*} [DecidableEq ι] (I S : Finset ι) (hSI : S ⊆ I)
    (approx value : ι → ℝ) (ν w L T : ℝ) (hL : 0 ≤ L) (hT : 1 ≤ T)
    (hcard : (S.card : ℝ) ≤ L*w)
    (hbase : ∀ x ∈ I, ν*w ≤ approx x)
    (herror : ∀ x ∈ S, approx x - 2 ≤ value x)
    (hcount : ∀ t : ℝ, 0 ≤ t → ((I.filter fun x => approx x - ν*w < t).card : ℝ) ≤ (T/6)*t+L) :
    ν*w*(S.card : ℝ) + 3*(S.card : ℝ)^2/T - (6*L^2+2*L)*w ≤ ∑ x ∈ S, value x := by
  let m : ℝ := S.card
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hT0 : 0 < T := by linarith
  have hshift : ∀ x ∈ I, 0 ≤ approx x - ν*w := fun x hx => sub_nonneg.mpr (hbase x hx)
  have hbat := bathtub I (fun x => approx x - ν*w) hshift (T/6) L (by positivity) hL hcount S hSI
  have hprofile : (∑ x ∈ S, (approx x - ν*w)) + (ν*w - 2)*m ≤ ∑ x ∈ S, value x := by
    have hsum : ∑ x ∈ S, (approx x - ν*w + (ν*w - 2)) ≤ ∑ x ∈ S, value x :=
      sum_le_sum (fun x hx => by linarith [herror x hx])
    rwa [sum_add_distrib, sum_const, nsmul_eq_mul, mul_comm (S.card : ℝ)] at hsum
  have hcard' : m ≤ L*w := hcard
  have hmax : m^2 - 2*L*m ≤ (max (m-L) 0)^2 := by
    rcases le_total (m-L) 0 with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg hm (show 0 ≤ L-m by linarith)]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg L]
  have hInv0 : 0 ≤ 1/T := by positivity
  have hInv1 : 1/T ≤ 1 := (div_le_one hT0).mpr hT
  have hgap : 6*L*m*(1/T) ≤ 6*L^2*w := by
    calc
      _ ≤ 6*L*m*1 := mul_le_mul_of_nonneg_left hInv1 (by positivity)
      _ = 6*L*m := mul_one _
      _ ≤ 6*L*(L*w) := mul_le_mul_of_nonneg_left hcard' (by positivity)
      _ = _ := by ring
  have hscale := mul_le_mul_of_nonneg_right hmax (mul_nonneg (by norm_num : 0 ≤ (3:ℝ)) hInv0)
  have hbat' : (max (m-L) 0)^2*(3*(1/T)) ≤ ∑ x ∈ S, (approx x - ν*w) := by
    have he : (max (m-L) 0)^2*(3*(1/T)) = (max (m-L) 0)^2/(2*(T/6)) := by ring
    rw [he]
    exact hbat
  have hcost := hscale.trans hbat'
  have hcost' : 3*m^2/T - 6*L*m*(1/T) ≤ ∑ x ∈ S, (approx x - ν*w) := by
    have he : 3*m^2/T - 6*L*m*(1/T) = (m^2 - 2*L*m)*(3*(1/T)) := by ring
    rwa [he]
  have hcard2 : 2*m ≤ 2*L*w := by nlinarith only [hcard']
  change ν*w*m+3*m^2/T-(6*L^2+2*L)*w ≤ _
  calc
    _ ≤ (3*m^2/T - 6*L*m*(1/T)) + (ν*w - 2)*m := by nlinarith only [hgap, hcard2]
    _ ≤ (∑ x ∈ S, (approx x - ν*w)) + (ν*w - 2)*m := add_le_add_left hcost' _
    _ ≤ _ := hprofile

theorem scaled_cell_coefficients (a b ν L T w m : ℝ)
    (hL : 0 < L) (hT : 0 < T) (hw : 0 < w) (hm : 0 ≤ m)
    (ha : a * (1096 * 2192) ≤ L*ν) (hb : b * (4 * 1096^2) * T ≤ 6*L^2) :
    2*(1096*w)^2*(a*(m/(L*w)) + b*(m/(L*w))^2) ≤ ν*w*m + 3*m^2/T := by
  have hlin := mul_le_mul_of_nonneg_right ha (show 0 ≤ w*m/L by positivity)
  have hquad := mul_le_mul_of_nonneg_right hb (show 0 ≤ m^2/(2*L^2*T) by positivity)
  have hL0 := ne_of_gt hL
  have hT0 := ne_of_gt hT
  have hw0 := ne_of_gt hw
  calc
    _ = (a*(1096*2192))*(w*m/L) + (b*(4*1096^2)*T)*(m^2/(2*L^2*T)) := by
      field_simp
      ring
    _ ≤ (L*ν)*(w*m/L) + (6*L^2)*(m^2/(2*L^2*T)) := add_le_add hlin hquad
    _ = _ := by
      field_simp
      ring

end OMA.Erdos1186BathtubTransfer

end

section

/-
Unit-block partition and reciprocal slope conversion for the G24 bathtub proof.
This isolates the counting steps of Snively's `P1186ExBathCell.cell_count`,
from `erdos-1186` v1.0.0, in a form independent of the PRS profile.
-/

namespace OMA.Erdos1186UnitBlockCounts

open Finset
open scoped BigOperators

private theorem sum_shifted_block {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a w : ℕ) :
    (∑ j ∈ Icc 1 w, f (a+j)) = ∑ x ∈ Ioc a (a+w), f x := by
  have h₁ : Icc 1 w = Ico 1 (w+1) := by
    ext j
    simp only [mem_Icc, mem_Ico]
    omega
  have h₂ : Ioc a (a+w) = Ico (a+1) (a+w+1) := by
    ext x
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [h₁, h₂, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
  have he : a+w+1-(a+1) = w := by omega
  rw [he, Nat.add_sub_cancel]
  exact sum_congr rfl (fun j _ => congrArg f (by omega))

theorem sum_unit_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (lo L w : ℕ) :
    (∑ p ∈ Ico lo (lo+L), ∑ j ∈ Icc 1 w, f (p*w+j)) =
      ∑ x ∈ Ioc (lo*w) ((lo+L)*w), f x := by
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih, sum_shifted_block]
    have he : (lo+(L+1))*w = (lo+L)*w+w := by
      rw [← Nat.add_assoc, Nat.add_mul, one_mul]
    rw [he]
    exact sum_Ioc_consecutive f (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
      (Nat.le_add_right _ _)

theorem card_filter_unit_blocks (pred : ℕ → Prop) [DecidablePred pred] (lo L w : ℕ) :
    ((Ioc (lo*w) ((lo+L)*w)).filter pred).card =
      ∑ p ∈ Ico lo (lo+L), ((Icc 1 w).filter fun j => pred (p*w+j)).card := by
  simp only [Finset.card_filter]
  exact (sum_unit_blocks (fun x => if pred x then (1:ℕ) else 0) lo L w).symm

theorem slope_real_of_six_count {ι : Type*} (P : Finset ι) (s : ι → ℕ)
    (hs : ∀ p ∈ P, 0 < s p ∧ 6 % s p = 0)
    (active : ι → Prop) [DecidablePred active] (T : ℕ)
    (hT : (∑ p ∈ P, if active p then (6 / s p : ℕ) else 0) ≤ T) :
    (∑ p ∈ P, if active p then (1 : ℝ) / s p else 0) ≤ (T : ℝ) / 6 := by
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 6)).mpr
  have hscale : (∑ p ∈ P, if active p then (1 : ℝ) / s p else 0) * 6 =
      ((∑ p ∈ P, if active p then (6 / s p : ℕ) else 0 : ℕ) : ℝ) := by
    rw [sum_mul, Nat.cast_sum]
    apply sum_congr rfl
    intro p hp
    by_cases h : active p
    · rw [if_pos h, if_pos h]
      have hpos : (0:ℝ) < s p := by exact_mod_cast (hs p hp).1
      have hdiv : (((6 / s p : ℕ) : ℝ)) = 6 / (s p : ℝ) := by
        apply (eq_div_iff hpos.ne').mpr
        exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (hs p hp).2)
      rw [hdiv]
      ring
    · simp [h]
  rw [hscale]
  exact_mod_cast hT

end OMA.Erdos1186UnitBlockCounts

end

section

/- Extract the finite G24 bathtub inputs into inequalities on unit blocks. -/

namespace OMA.Erdos1186G24Profile

open Finset
open scoped BigOperators
open OMA.Erdos1186Region2 OMA.Erdos1186UnitBlockCounts

def cellUnits (i : ℕ) : Finset ℕ := Ico (g24Endpoint i) (g24Endpoint i + g24Length i)

def offset (i p : ℕ) : ℕ := (profileMin p - threshold i).toNat

structure CellFacts (i : ℕ) : Prop where
  length_pos : 0 < g24Length i
  right_bound : g24Endpoint (i+1) ≤ 1096
  cap_pos : 0 < slopeCap i
  alpha_num : (digit g24AlphaWord 9 (min i (129-i)) : ℤ)*(1096*2192) ≤
    (g24Length i : ℤ) * threshold i * 300304
  beta_num : digit g24BetaWord 9 (min i (129-i))*(4*1096^2)*slopeCap i ≤ 6*g24Length i^2*1801824
  lower : ∀ p ∈ cellUnits i, threshold i ≤ profileMin p
  piece : ∀ p ∈ cellUnits i, 0 < profileAbsSlope p ∧ 6 % profileAbsSlope p = 0 ∧
    offset i p + profileAbsSlope p ≤ 3*g24Length i
  levels : ∀ c < 3*g24Length i,
    (∑ p ∈ cellUnits i, if offset i p ≤ c ∧ c < offset i p + profileAbsSlope p
      then 6 / profileAbsSlope p else 0) ≤ slopeCap i

private theorem sum_list_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

private theorem sum_list_range' (f : ℕ → ℕ) (a n : ℕ) :
    ((List.range' a n).map f).sum = ∑ k ∈ Ico a (a+n), f k := by
  rw [List.range'_eq_map_range, List.map_map, sum_list_range, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]
  rfl

theorem cellFacts (i : ℕ) (hi : i < 130) : CellFacts i := by
  have hh := cellChecks i hi
  simp only [cellCheck, Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨⟨⟨⟨⟨hgeo, ha⟩, hb⟩, hlo⟩, hpiece⟩, hlevel⟩ := hh
  refine ⟨hgeo.1, hgeo.2.1, hgeo.2.2, ha, hb, ?_, ?_, ?_⟩
  · intro p hp
    have hmem : p ∈ List.range' (g24Endpoint i) (g24Length i) :=
      List.mem_range'_1.mpr (mem_Ico.mp hp)
    exact of_decide_eq_true (List.all_eq_true.mp hlo p hmem)
  · intro p hp
    have hmem : p ∈ List.range' (g24Endpoint i) (g24Length i) :=
      List.mem_range'_1.mpr (mem_Ico.mp hp)
    have hmap : (offset i p, profileAbsSlope p) ∈ levelPieces i := List.mem_map_of_mem hmem
    exact of_decide_eq_true (List.all_eq_true.mp hpiece _ hmap)
  · intro c hc
    have hl : slopeNumerator (levelPieces i) c ≤ slopeCap i :=
      of_decide_eq_true (List.all_eq_true.mp hlevel c (List.mem_range.mpr hc))
    unfold slopeNumerator levelPieces at hl
    rw [List.map_map, sum_list_range'] at hl
    exact hl

theorem cast_offset (i p : ℕ) (hi : i < 130) (hp : p ∈ cellUnits i) :
    (offset i p : ℤ) = profileMin p - threshold i := by
  unfold offset
  exact Int.toNat_of_nonneg (sub_nonneg.mpr ((cellFacts i hi).lower p hp))

theorem cellSlopeBound (i : ℕ) (hi : i < 130) (c : ℕ) (hc : c < 3*g24Length i) :
    (∑ p ∈ cellUnits i,
        if profileMin p - threshold i ≤ (c : ℤ) ∧
            (c : ℤ) < profileMin p - threshold i + profileAbsSlope p
        then (1 : ℝ) / profileAbsSlope p else 0) ≤ (slopeCap i : ℝ) / 6 := by
  have hf := cellFacts i hi
  have hrs := slope_real_of_six_count (cellUnits i) profileAbsSlope
    (fun p hp => ⟨(hf.piece p hp).1, (hf.piece p hp).2.1⟩)
    (fun p => offset i p ≤ c ∧ c < offset i p + profileAbsSlope p) (slopeCap i) (hf.levels c hc)
  refine le_trans ?_ hrs
  apply le_of_eq
  apply sum_congr rfl
  intro p hp
  rw [← cast_offset i p hi hp]
  have hiff : ((offset i p : ℤ) ≤ (c : ℤ) ∧
      (c : ℤ) < (offset i p : ℤ) + profileAbsSlope p) ↔
      offset i p ≤ c ∧ c < offset i p + profileAbsSlope p := by omega
  by_cases h : offset i p ≤ c ∧ c < offset i p + profileAbsSlope p
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

end OMA.Erdos1186G24Profile

end

section

/-
The G24 bathtub estimate conditional on only the pointwise comparison with
the actual signed energy. The numerical profile and all slope bounds are
discharged by the exact checked G24 inputs.
-/

namespace OMA.Erdos1186G24Profile

open Finset
open scoped BigOperators
open OMA.Erdos1186Region2 OMA.Erdos1186UnitBlockCounts OMA.Erdos1186BathtubTransfer

def scaledCell (i w : ℕ) : Finset ℕ :=
  Ioc (g24Endpoint i * w) ((g24Endpoint i + g24Length i) * w)

noncomputable def affineValue (w x : ℕ) : ℝ :=
  (profileA ((x-1)/w) : ℝ) * w + (profileB ((x-1)/w) : ℝ) * ((x-1)%w+1 : ℕ)

noncomputable def shiftedPiece (i w p j : ℕ) : ℝ :=
  (profileA p : ℝ)*w + (profileB p : ℝ)*j - (threshold i : ℝ)*w

theorem affineValue_at_block (w p j : ℕ) (hj₀ : 1 ≤ j) (hj₁ : j ≤ w) :
    affineValue w (p*w+j) = (profileA p : ℝ)*w + (profileB p : ℝ)*j := by
  have hd : (p*w+j-1)/w = p :=
    Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
  have hm : (p*w+j-1)%w+1 = j := by
    rw [show p*w+j-1 = p*w+(j-1) by omega, Nat.mul_add_mod_of_lt (by omega : j-1 < w)]
    omega
  rw [affineValue, hd, hm]

private theorem shiftedPiece_dist (i w p j j' : ℕ) :
    |shiftedPiece i w p j - shiftedPiece i w p j'| =
      (profileAbsSlope p : ℝ) * |(j : ℝ)-j'| := by
  have he : shiftedPiece i w p j - shiftedPiece i w p j' =
      (profileB p : ℝ)*((j : ℝ)-j') := by unfold shiftedPiece; ring
  have hs : (profileAbsSlope p : ℝ) = |(profileB p : ℝ)| := by
    unfold profileAbsSlope
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [he, abs_mul, hs]

private theorem shiftedPiece_lower (i w p j : ℕ) (hj : j ≤ w) :
    ((profileMin p : ℝ) - (threshold i : ℝ))*w ≤ shiftedPiece i w p j := by
  unfold shiftedPiece
  by_cases hb : (0 : ℝ) ≤ profileB p
  · have h : (profileMin p : ℝ) ≤ (profileA p : ℝ) := by
      exact_mod_cast min_le_left (profileA p) (profileA p + profileB p)
    have hmul := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg w : (0:ℝ) ≤ w)
    nlinarith only [hmul, mul_nonneg hb (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  · have h : (profileMin p : ℝ) ≤ (profileA p : ℝ) + (profileB p : ℝ) := by
      exact_mod_cast min_le_right (profileA p) (profileA p + profileB p)
    have hmul := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg w : (0:ℝ) ≤ w)
    have hj' : (j : ℝ) ≤ w := by exact_mod_cast hj
    have hmul' := mul_le_mul_of_nonpos_left hj' (le_of_lt (lt_of_not_ge hb))
    nlinarith only [hmul, hmul']

theorem g24_threshold_count (i : ℕ) (hi : i < 130) (w : ℕ) (hw : 1 ≤ w) (t : ℝ) (ht : 0 ≤ t) :
    (((scaledCell i w).filter (fun x => affineValue w x - (threshold i : ℝ)*w < t)).card : ℝ) ≤
      ((slopeCap i : ℝ)/6)*t + g24Length i := by
  have hf := cellFacts i hi
  have hc : (cellUnits i).card = g24Length i := by simp [cellUnits, Nat.card_Ico]
  have hnonneg : ∀ p ∈ cellUnits i, 0 ≤ profileMin p-threshold i :=
    fun p hp => sub_nonneg.mpr (hf.lower p hp)
  have hcap : ∀ p ∈ cellUnits i,
      profileMin p-threshold i + (profileAbsSlope p : ℤ) ≤ (3*g24Length i : ℕ) := by
    intro p hp
    rw [← cast_offset i p hi hp]
    exact_mod_cast (hf.piece p hp).2.2
  have hsum := sum_piece_counts (cellUnits i) w hw (shiftedPiece i w)
    (fun p => profileMin p-threshold i) (fun p => (profileAbsSlope p : ℤ))
    ((slopeCap i : ℝ)/6) (by positivity)
    (fun p hp => by exact_mod_cast (hf.piece p hp).1) hnonneg (3*g24Length i) hcap
    (cellSlopeBound i hi)
    (fun p _ j j' => by push_cast; exact shiftedPiece_dist i w p j j')
    (fun p _ j hj => by push_cast; exact shiftedPiece_lower i w p j (mem_Icc.mp hj).2)
    t ht
  rw [hc] at hsum
  apply le_trans ?_ hsum
  unfold scaledCell
  rw [card_filter_unit_blocks, Nat.cast_sum]
  apply le_of_eq
  apply sum_congr rfl
  intro p _
  have he : (Icc 1 w).filter (fun j => affineValue w (p*w+j) - (threshold i : ℝ)*w < t) =
      (Icc 1 w).filter (fun j => shiftedPiece i w p j < t) := by
    apply filter_congr
    intro j hj
    obtain ⟨hj₀, hj₁⟩ := mem_Icc.mp hj
    rw [affineValue_at_block w p j hj₀ hj₁]
    rfl
  rw [he]

theorem affine_ge_threshold (i : ℕ) (hi : i < 130) {w x : ℕ} (hw : 0 < w) (hx : x ∈ scaledCell i w) :
    (threshold i : ℝ)*w ≤ affineValue w x := by
  have hxb := mem_Ioc.mp hx
  have hp : (x-1)/w ∈ cellUnits i := by
    rw [cellUnits, mem_Ico]
    constructor
    · exact (Nat.le_div_iff_mul_le hw).mpr (by omega)
    · exact (Nat.div_lt_iff_lt_mul hw).mpr (by omega)
  have hj : (x-1)%w+1 ≤ w := Nat.succ_le_of_lt (Nat.mod_lt _ hw)
  have hmin := (cellFacts i hi).lower _ hp
  have hc : ((threshold i : ℤ) : ℝ) ≤ (profileMin ((x-1)/w) : ℝ) := by exact_mod_cast hmin
  have hm := mul_nonneg (sub_nonneg.mpr hc) (Nat.cast_nonneg w : (0:ℝ) ≤ w)
  have hu := shiftedPiece_lower i w ((x-1)/w) ((x-1)%w+1) hj
  exact sub_nonneg.mp (hm.trans hu)

theorem g24_cell_lower (i : ℕ) (hi : i < 130) (w : ℕ) (hw : 1 ≤ w)
    (S : Finset ℕ) (hS : S ⊆ scaledCell i w) (value : ℕ → ℝ)
    (herror : ∀ x ∈ S, affineValue w x - 2 ≤ value x) :
    (threshold i : ℝ)*w*(S.card : ℝ) + 3*(S.card : ℝ)^2/slopeCap i -
      (6*(g24Length i : ℝ)^2+2*g24Length i)*w ≤ ∑ x ∈ S, value x := by
  have hc : (scaledCell i w).card = g24Length i*w := by
    rw [scaledCell, Nat.card_Ioc, Nat.add_mul]
    omega
  have hcard : (S.card : ℝ) ≤ (g24Length i : ℝ)*w := by
    exact_mod_cast (Finset.card_le_card hS).trans_eq hc
  have ht : (1 : ℝ) ≤ slopeCap i := by exact_mod_cast (cellFacts i hi).cap_pos
  exact cell_lower_bound (scaledCell i w) S hS (affineValue w) value (threshold i) w
    (g24Length i) (slopeCap i) (Nat.cast_nonneg _) ht hcard
    (fun _ hx => affine_ge_threshold i hi hw hx) herror (g24_threshold_count i hi w hw)

end OMA.Erdos1186G24Profile

end

section

/- Rescale the checked G24 cell bound to the coefficients in the finite objective. -/

namespace OMA.Erdos1186G24Profile

open Finset
open scoped BigOperators
open OMA.Erdos1186Region2 OMA.Erdos1186BathtubTransfer

noncomputable def bathAlpha (i : ℕ) : ℝ := (digit g24AlphaWord 9 (min i (129-i)) : ℝ)/300304
noncomputable def bathBeta (i : ℕ) : ℝ := (digit g24BetaWord 9 (min i (129-i)) : ℝ)/1801824

private theorem alpha_scale (i : ℕ) (hi : i < 130) :
    bathAlpha i * (1096*2192) ≤ (g24Length i : ℝ)*(threshold i : ℝ) := by
  have h : (digit g24AlphaWord 9 (min i (129-i)) : ℝ)*(1096*2192) ≤
      (g24Length i : ℝ)*(threshold i : ℝ)*300304 := by exact_mod_cast (cellFacts i hi).alpha_num
  have he : bathAlpha i*(1096*2192) = (digit g24AlphaWord 9 (min i (129-i)) : ℝ)*(1096*2192)/300304 := by
    unfold bathAlpha
    ring
  rw [he]
  exact (div_le_iff₀ (by norm_num)).mpr h

private theorem beta_scale (i : ℕ) (hi : i < 130) :
    bathBeta i * (4*1096^2) * (slopeCap i : ℝ) ≤ 6*(g24Length i : ℝ)^2 := by
  have h : (digit g24BetaWord 9 (min i (129-i)) : ℝ)*(4*1096^2)*(slopeCap i : ℝ) ≤
      6*(g24Length i : ℝ)^2*1801824 := by exact_mod_cast (cellFacts i hi).beta_num
  have he : bathBeta i*(4*1096^2)*(slopeCap i : ℝ) =
      (digit g24BetaWord 9 (min i (129-i)) : ℝ)*(4*1096^2)*(slopeCap i : ℝ)/1801824 := by
    unfold bathBeta
    ring
  rw [he]
  exact (div_le_iff₀ (by norm_num)).mpr h

theorem g24_cell_normalized (i : ℕ) (hi : i < 130) (w : ℕ) (hw : 1 ≤ w)
    (S : Finset ℕ) (hS : S ⊆ scaledCell i w) (value : ℕ → ℝ)
    (herror : ∀ x ∈ S, affineValue w x - 2 ≤ value x) :
    let y := (S.card : ℝ)/((g24Length i : ℝ)*w)
    2*(1096*(w : ℝ))^2*(bathAlpha i*y+bathBeta i*y^2) -
      (6*(g24Length i : ℝ)^2+2*g24Length i)*w ≤ ∑ x ∈ S, value x := by
  have hL : (0:ℝ) < g24Length i := by exact_mod_cast (cellFacts i hi).length_pos
  have hT : (0:ℝ) < slopeCap i := by exact_mod_cast (cellFacts i hi).cap_pos
  have hw' : (0:ℝ) < w := by exact_mod_cast hw
  have hscale := scaled_cell_coefficients (bathAlpha i) (bathBeta i) (threshold i)
    (g24Length i) (slopeCap i) w (S.card : ℝ) hL hT hw' (Nat.cast_nonneg _)
    (alpha_scale i hi) (beta_scale i hi)
  exact (sub_le_sub_right hscale _).trans (g24_cell_lower i hi w hw S hS value herror)

theorem g24_bath_indicator (i : ℕ) (hi : i < 130) (w : ℕ) (hw : 1 ≤ w)
    (d : ℕ → Bool) (value : ℕ → ℝ)
    (herror : ∀ x ∈ scaledCell i w, affineValue w x - 2 ≤ value x) :
    let S := (scaledCell i w).filter (fun x => d x = true)
    let y := (S.card : ℝ)/((g24Length i : ℝ)*w)
    2*(1096*(w : ℝ))^2*(bathAlpha i*y+bathBeta i*y^2) -
      (6*(g24Length i : ℝ)^2+2*g24Length i)*w ≤
      ∑ x ∈ scaledCell i w, value x * ((d x).toNat : ℝ) := by
  intro S y
  have hS : S ⊆ scaledCell i w := filter_subset _ _
  have h := g24_cell_normalized i hi w hw S hS value (fun x hx => herror x (hS hx))
  have hsum : (∑ x ∈ S, value x) = ∑ x ∈ scaledCell i w, value x * ((d x).toNat : ℝ) := by
    dsimp [S]
    rw [sum_filter]
    exact sum_congr rfl (fun x _ => by cases d x <;> simp)
  exact h.trans_eq hsum

end OMA.Erdos1186G24Profile

end

section

/-
Prefix formulas for the signed linear energy of an interval colouring.
These number-free forms isolate the row and column sums in Snively's
`P1186ExBathH2.lean` and work with arbitrary integer weights.
-/

namespace OMA.Erdos1186ProfilePrefix

open Finset
open scoped BigOperators

def prefixSum (f : ℕ → ℤ) (r : ℕ) : ℤ := ∑ x ∈ Ioc 0 r, f x

def window (n x y : ℕ) : ℤ :=
  if 1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n then 1 else 0

theorem prefix_sub (f : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    ∑ x ∈ Ioc a b, f x = prefixSum f b - prefixSum f a := by
  have h := sum_Ioc_consecutive f (Nat.zero_le a) hab
  unfold prefixSum
  rw [add_comm] at h
  exact eq_sub_iff_add_eq.mpr h

theorem row_sum (f : ℕ → ℤ) {n x : ℕ} (hx₀ : 1 ≤ x) (hx₁ : x ≤ n) :
    (∑ y ∈ Icc 1 n, window n x y * f y) = prefixSum f ((x+n)/2) - prefixSum f (x/2) := by
  have hterm (y : ℕ) : window n x y * f y = if x/2 < y ∧ y ≤ (x+n)/2 then f y else 0 := by
    have he : (1 ≤ 2*(y : ℤ)-x ∧ 2*(y : ℤ)-x ≤ n) ↔ x/2 < y ∧ y ≤ (x+n)/2 := by omega
    unfold window
    by_cases hy : x/2 < y ∧ y ≤ (x+n)/2
    · rw [if_pos (he.mpr hy), if_pos hy, one_mul]
    · rw [if_neg (fun hn => hy (he.mp hn)), if_neg hy, zero_mul]
  have hset : (Icc 1 n).filter (fun y => x/2 < y ∧ y ≤ (x+n)/2) = Ioc (x/2) ((x+n)/2) := by
    ext y
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [sum_congr rfl (fun y _ => hterm y), ← sum_filter, hset]
  exact prefix_sub f (by omega)

theorem column_sum (f : ℕ → ℤ) {n y : ℕ} (hy₀ : 1 ≤ y) (hy₁ : y ≤ n) :
    (∑ x ∈ Icc 1 n, window n x y * f x) =
      prefixSum f (min n (2*y-1)) - prefixSum f (2*y-n-1) := by
  have hterm (x : ℕ) (hx : x ∈ Icc 1 n) : window n x y * f x =
      if 2*y-n-1 < x ∧ x ≤ min n (2*y-1) then f x else 0 := by
    have hb := mem_Icc.mp hx
    have he : (1 ≤ 2*(y : ℤ)-x ∧ 2*(y : ℤ)-x ≤ n) ↔
        2*y-n-1 < x ∧ x ≤ min n (2*y-1) := by omega
    unfold window
    by_cases h : 2*y-n-1 < x ∧ x ≤ min n (2*y-1)
    · rw [if_pos (he.mpr h), if_pos h, one_mul]
    · rw [if_neg (fun hn => h (he.mp hn)), if_neg h, zero_mul]
  have hset : (Icc 1 n).filter (fun x => 2*y-n-1 < x ∧ x ≤ min n (2*y-1)) =
      Ioc (2*y-n-1) (min n (2*y-1)) := by
    ext x
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [sum_congr rfl hterm, ← sum_filter, hset]
  exact prefix_sub f (by omega)

private theorem sum_partial_block (f : ℕ → ℤ) {w k r : ℕ} (hr : r ≤ w) :
    (∑ x ∈ Ioc (k*w) (k*w+r), f ((x-1)/w)) = (r : ℤ) * f k := by
  have hindex (x : ℕ) (hx : x ∈ Ioc (k*w) (k*w+r)) : (x-1)/w = k := by
    have hb := mem_Ioc.mp hx
    exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
  have hcard : (Ioc (k*w) (k*w+r)).card = r := by rw [Nat.card_Ioc]; omega
  rw [sum_congr rfl (fun x hx => congrArg f (hindex x hx)), sum_const, hcard, nsmul_eq_mul]

theorem prefix_repeated (f : ℕ → ℤ) {w k r : ℕ} (hr : r ≤ w) :
    prefixSum (fun x => f ((x-1)/w)) (k*w+r) =
      (w : ℤ) * (∑ j ∈ range k, f j) + (r : ℤ) * f k := by
  let F : ℕ → ℤ := fun x => f ((x-1)/w)
  have full (k : ℕ) : prefixSum F (k*w) = (w : ℤ) * ∑ j ∈ range k, f j := by
    induction k with
    | zero => simp [prefixSum]
    | succ k ih =>
      rw [Nat.succ_mul, sum_range_succ, mul_add]
      have h := sum_Ioc_consecutive F (Nat.zero_le (k*w)) (Nat.le_add_right (k*w) w)
      change prefixSum F (k*w) + (∑ x ∈ Ioc (k*w) (k*w+w), f ((x-1)/w)) = prefixSum F (k*w+w) at h
      rw [← h, ih, sum_partial_block f le_rfl]
  have h := sum_Ioc_consecutive F (Nat.zero_le (k*w)) (Nat.le_add_right (k*w) r)
  change prefixSum F (k*w) + (∑ x ∈ Ioc (k*w) (k*w+r), f ((x-1)/w)) = prefixSum F (k*w+r) at h
  change prefixSum F (k*w+r) = _
  rw [← h, full k, sum_partial_block f hr]

end OMA.Erdos1186ProfilePrefix

end

section

/- The audited integer prefix function equals the sum of PRS unit signs. -/

namespace OMA.Erdos1186G24Profile

open Finset
open scoped BigOperators

theorem signPrefix_eq_sum (k : ℕ) (hk : k ≤ 1096) :
    signPrefix k = ∑ j ∈ range k, unitSign j := by
  induction k with
  | zero => simpa using signPrefix_zero
  | succ k ih =>
    have hlt : k < 1096 := by omega
    rw [signPrefix_succ k hlt, sum_range_succ, ih (Nat.le_of_lt hlt)]

theorem repeated_sign_prefix {w k r : ℕ} (hk : k ≤ 1096) (hr : r ≤ w) :
    OMA.Erdos1186ProfilePrefix.prefixSum (fun x => unitSign ((x-1)/w)) (k*w+r) =
        (w : ℤ)*signPrefix k + (r : ℤ)*unitSign k := by
  rw [OMA.Erdos1186ProfilePrefix.prefix_repeated unitSign hr, signPrefix_eq_sum k hk]

theorem unitSign_pm (k : ℕ) : unitSign k = 1 ∨ unitSign k = -1 := by
  unfold unitSign
  dsimp only
  split <;> simp

theorem unitSign_pair (k : ℕ) : unitSign (2*k+1) = unitSign (2*k) := by
  have h : (2*k+1)/2 = (2*k)/2 := by omega
  unfold unitSign
  rw [h]

end OMA.Erdos1186G24Profile

end

section

/-
The two-unit rounding error in the PRS unit-cell profile. The exact closed
form uses a halved integer and an odd endpoint. This isolates its comparison
with the affine profile in Snively's `P1186ExBathH2.H2_lin`.
-/

namespace OMA.Erdos1186ProfileRounding

theorem rounded_linear_error (w j e : ℕ) (s A D B : ℤ)
    (hs : s = 1 ∨ s = -1) (hD : |D| ≤ 1) (hB : |B| ≤ 1) :
    |(-s * (A*(w : ℤ) + 2*D*((e*w+j)/2 : ℕ) + (2*(j : ℤ)-1)*B)) -
      (-s * ((A + (e : ℤ)*D)*(w : ℤ) + (D+2*B)*(j : ℤ)))| ≤ 2 := by
  let r : ℤ := ((e*w+j)%2 : ℕ)
  have hr : 2 * (((e*w+j)/2 : ℕ) : ℤ) + r = (e : ℤ)*w + j := by
    have h (n : ℕ) : 2 * ((n/2 : ℕ) : ℤ) + (n%2 : ℕ) = (n : ℤ) := by omega
    simpa only [r, Nat.cast_add, Nat.cast_mul] using h (e*w+j)
  have hrem : r = 0 ∨ r = 1 := by
    dsimp [r]
    omega
  have hunit : |s| = 1 := by rcases hs with h | h <;> simp [h]
  have hRD : |r*D| ≤ 1 := by rcases hrem with h | h <;> simp [h, hD]
  have heq : (-s * (A*(w : ℤ) + 2*D*((e*w+j)/2 : ℕ) + (2*(j : ℤ)-1)*B)) -
      (-s * ((A + (e : ℤ)*D)*(w : ℤ) + (D+2*B)*(j : ℤ))) = s*(r*D+B) := by
    calc
      _ = s * (D * ((e : ℤ)*w + j - 2 * (((e*w+j)/2 : ℕ) : ℤ)) + B) := by ring
      _ = _ := by rw [← hr]; ring
  rw [heq, abs_mul, hunit, one_mul]
  exact (abs_add_le _ _).trans (add_le_add hRD hB)

end OMA.Erdos1186ProfileRounding

end

section

/-
The signed window profile is the certified PRS affine profile up to an error
of two. This adapts the row and column arithmetic of Chandler Snively's
Apache-licensed `P1186ExBathH2` from `erdos-1186` v1.0.0, with the weighted
prefix and profile rounding treated separately. The argument is due to
Carlos Toledo.
-/

namespace OMA.Erdos1186G24Profile

open Finset
open scoped BigOperators
open OMA.Erdos1186Region2 OMA.Erdos1186ProfilePrefix OMA.Erdos1186ProfileRounding

def signedColor (w x : ℕ) : ℤ := unitSign ((x-1)/w)

def linearProfile (w x : ℕ) : ℤ :=
  -signedColor w x *
    ((∑ y ∈ Icc 1 (1096*w), window (1096*w) x y * signedColor w y) +
      (∑ y ∈ Icc 1 (1096*w), window (1096*w) y x * signedColor w y))

theorem signedColor_eq_reference (w x : ℕ) :
    signedColor w x = (let b := (x-1)/(2*w)
      if b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
        (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)
      then 1 else -1) := by
  unfold signedColor unitSign
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm w 2]

private theorem signed_prefix_repeated {w k r : ℕ} (hk : k ≤ 1096) (hr : r ≤ w) :
    prefixSum (signedColor w) (k*w+r) = (w : ℤ)*signPrefix k+(r : ℤ)*unitSign k :=
  repeated_sign_prefix hk hr

private theorem prefix_even_span (w p r : ℕ) (hp : p ≤ 547) (hr : r ≤ 2*w) :
    prefixSum (signedColor w) ((2*p)*w+r) = (w : ℤ)*signPrefix (2*p) + (r : ℤ)*unitSign (2*p) := by
  by_cases h : r ≤ w
  · exact signed_prefix_repeated (by omega) h
  · have hr' : r-w ≤ w := by omega
    have he : (2*p)*w+r = (2*p+1)*w+(r-w) := by
      rw [Nat.add_mul, one_mul]
      omega
    rw [he, signed_prefix_repeated (by omega : 2*p+1 ≤ 1096) hr',
      signPrefix_succ (2*p) (by omega), unitSign_pair]
    rw [Nat.cast_sub (by omega : w ≤ r)]
    ring

private theorem row_prefix_profile (w p j : ℕ) (hp : p < 1096) (hj : j ≤ w) :
    prefixSum (signedColor w) ((p*w+j+1096*w)/2) - prefixSum (signedColor w) ((p*w+j)/2) =
      (w : ℤ)*(signPrefix (p/2+548)-signPrefix (p/2)) +
        ((((p%2)*w+j)/2 : ℕ) : ℤ)*(unitSign (p/2+548)-unitSign (p/2)) := by
  let a := p/2
  let e := p%2
  let r := (e*w+j)/2
  have hp' : p = 2*a+e := by dsimp [a,e]; omega
  have hE : e ≤ 1 := by dsimp [e]; omega
  have hEw : e*w ≤ w := by simpa using Nat.mul_le_mul_right w hE
  have hr : r ≤ w := by dsimp [r]; omega
  have ha : a+548 ≤ 1096 := by dsimp [a]; omega
  have hleft : p*w+j+1096*w = 2*((a+548)*w)+(e*w+j) := by rw [hp']; ring
  have hright : p*w+j = 2*(a*w)+(e*w+j) := by rw [hp']; ring
  have hl : (p*w+j+1096*w)/2 = (a+548)*w+r := by rw [hleft]; dsimp [r]; omega
  have hh : (p*w+j)/2 = a*w+r := by rw [hright]; dsimp [r]; omega
  rw [hl, hh, signed_prefix_repeated ha hr, signed_prefix_repeated (by omega : a ≤ 1096) hr]
  change _ = (w : ℤ)*(signPrefix (a+548)-signPrefix a) + (r : ℤ)*(unitSign (a+548)-unitSign a)
  ring

private theorem column_prefix_profile (w p j : ℕ) (hp : p < 1096) (hj₀ : 1 ≤ j) (hj₁ : j ≤ w) :
    prefixSum (signedColor w) (min (1096*w) (2*(p*w+j)-1)) -
        prefixSum (signedColor w) (2*(p*w+j)-1096*w-1) =
      (w : ℤ)*columnIntercept p + (2*(j : ℤ)-1)*columnSlope p := by
  have hjR : (((2*j-1 : ℕ) : ℤ)) = 2*(j : ℤ)-1 := by omega
  have hr : 2*j-1 ≤ 2*w := by omega
  by_cases h : p < 548
  · have hpw : p*w ≤ 547*w := Nat.mul_le_mul_right _ (by omega)
    have ht : 2*(p*w+j) ≤ 1096*w := by omega
    have he : (2*p)*w = 2*(p*w) := by ring
    have ha : min (1096*w) (2*(p*w+j)-1) = (2*p)*w+(2*j-1) := by
      rw [min_eq_right (by omega), he]
      omega
    have hb : 2*(p*w+j)-1096*w-1 = 0 := by omega
    rw [ha, hb, prefix_even_span w p (2*j-1) (by omega) hr, hjR]
    simp [prefixSum, columnIntercept, columnSlope, h]
  · let q := p-548
    have hpq : p = 548+q := by dsimp [q]; omega
    have hq : q ≤ 547 := by dsimp [q]; omega
    have hpoint : p*w+j = 548*w+(q*w+j) := by rw [hpq]; ring
    have ha : min (1096*w) (2*(p*w+j)-1) = 1096*w := by
      rw [hpoint]
      exact min_eq_left (by omega)
    have he : (2*q)*w = 2*(q*w) := by ring
    have hb : 2*(p*w+j)-1096*w-1 = (2*q)*w+(2*j-1) := by
      rw [hpoint, he]
      omega
    have htotal : prefixSum (signedColor w) (1096*w) = 0 := by
      have hx := signed_prefix_repeated (w := w) (k := 1096) (r := 0) le_rfl (Nat.zero_le _)
      simpa [signPrefix_total] using hx
    rw [ha, hb, htotal, prefix_even_span w q (2*j-1) hq hr, hjR]
    simp only [columnIntercept, columnSlope, if_neg h]
    change _ = (w : ℤ)*(-signPrefix (2*q)) + (2*(j : ℤ)-1)*(-unitSign (2*q))
    ring

theorem linearProfile_at_block (w p j : ℕ) (hp : p < 1096) (hj₀ : 1 ≤ j) (hj₁ : j ≤ w) :
    linearProfile w (p*w+j) = -unitSign p *
      ((w : ℤ)*(signPrefix (p/2+548)-signPrefix (p/2)) +
        ((((p%2)*w+j)/2 : ℕ) : ℤ)*(unitSign (p/2+548)-unitSign (p/2)) +
        ((w : ℤ)*columnIntercept p+(2*(j : ℤ)-1)*columnSlope p)) := by
  have hx₀ : 1 ≤ p*w+j := by omega
  have hpw : p*w ≤ 1095*w := Nat.mul_le_mul_right _ (by omega)
  have hx₁ : p*w+j ≤ 1096*w := by omega
  have hd : (p*w+j-1)/w = p :=
    Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
  have hc : signedColor w (p*w+j) = unitSign p := by rw [signedColor, hd]
  rw [linearProfile, row_sum _ hx₀ hx₁, column_sum _ hx₀ hx₁, hc,
    row_prefix_profile w p j hp hj₁, column_prefix_profile w p j hp hj₀ hj₁]

private theorem midpoint_twice (p : ℕ) :
    unitSign (p/2+548)-unitSign (p/2) = 2*midpointSignDiff p := by
  unfold midpointSignDiff
  rcases unitSign_pm (p/2+548) with h | h <;>
    rcases unitSign_pm (p/2) with h' | h' <;> rw [h,h'] <;> decide

private theorem midpoint_abs (p : ℕ) : |midpointSignDiff p| ≤ 1 := by
  unfold midpointSignDiff
  rcases unitSign_pm (p/2+548) with h | h <;>
    rcases unitSign_pm (p/2) with h' | h' <;> rw [h,h'] <;> decide

private theorem column_abs (p : ℕ) : |columnSlope p| ≤ 1 := by
  unfold columnSlope
  split
  · rcases unitSign_pm (2*p) with h | h <;> rw [h] <;> decide
  · rcases unitSign_pm (2*(p-548)) with h | h <;> rw [h] <;> decide

theorem linearProfile_error (w p j : ℕ) (hp : p < 1096) (hj₀ : 1 ≤ j) (hj₁ : j ≤ w) :
    |linearProfile w (p*w+j)-(profileA p*(w : ℤ)+profileB p*(j : ℤ))| ≤ 2 := by
  rw [linearProfile_at_block w p j hp hj₀ hj₁, midpoint_twice p]
  have h := rounded_linear_error w j (p%2) (unitSign p)
    (signPrefix (p/2+548)-signPrefix (p/2)+columnIntercept p)
    (midpointSignDiff p) (columnSlope p) (unitSign_pm p) (midpoint_abs p) (column_abs p)
  have he : -unitSign p *
      ((w : ℤ)*(signPrefix (p/2+548)-signPrefix (p/2)) +
        ((((p%2)*w+j)/2 : ℕ) : ℤ)*(2*midpointSignDiff p) +
        ((w : ℤ)*columnIntercept p+(2*(j : ℤ)-1)*columnSlope p)) -
      (profileA p*(w : ℤ)+profileB p*(j : ℤ)) =
      -unitSign p * ((signPrefix (p/2+548)-signPrefix (p/2)+columnIntercept p)*(w : ℤ) +
        2*midpointSignDiff p*(((p%2)*w+j)/2 : ℕ)+(2*(j : ℤ)-1)*columnSlope p) -
      (-unitSign p * ((signPrefix (p/2+548)-signPrefix (p/2)+columnIntercept p+
        ((p%2 : ℕ) : ℤ)*midpointSignDiff p)*(w : ℤ) +
        (midpointSignDiff p+2*columnSlope p)*(j : ℤ))) := by
    unfold profileA profileB
    ring
  rw [he]
  exact h

end OMA.Erdos1186G24Profile

end

section

/- The exact G24 bathtub estimate for the actual PRS signed window energy. -/

namespace OMA.Erdos1186G24Profile

open Finset
open scoped BigOperators
open OMA.Erdos1186Region2

theorem cell_endpoint (i : ℕ) (hi : i < 130) :
    g24Endpoint i + g24Length i = g24Endpoint (i+1) := by
  have h := (cellFacts i hi).length_pos
  unfold g24Length at h ⊢
  omega

theorem scaledCell_eq_endpoints (i : ℕ) (hi : i < 130) (w : ℕ) :
    scaledCell i w = Ioc (g24Endpoint i*w) (g24Endpoint (i+1)*w) := by
  rw [scaledCell, cell_endpoint i hi]

theorem affineValue_le_linearProfile (i : ℕ) (hi : i < 130) (w : ℕ) (hw : 1 ≤ w)
    (x : ℕ) (hx : x ∈ scaledCell i w) : affineValue w x - 2 ≤ (linearProfile w x : ℝ) := by
  have hw' : 0 < w := hw
  rw [scaledCell_eq_endpoints i hi w] at hx
  have hxb := mem_Ioc.mp hx
  have hx₀ : 1 ≤ x := by omega
  have hx₁ : x ≤ 1096*w := hxb.2.trans (Nat.mul_le_mul_right _ (cellFacts i hi).right_bound)
  let p := (x-1)/w
  let j := (x-1)%w+1
  have hp : p < 1096 := (Nat.div_lt_iff_lt_mul hw').mpr (by omega)
  have hj₀ : 1 ≤ j := by dsimp [j]; omega
  have hj₁ : j ≤ w := Nat.succ_le_of_lt (Nat.mod_lt _ hw')
  have hdecomp : x = p*w+j := by
    dsimp [p,j]
    rw [Nat.mul_comm ((x-1)/w) w]
    have hh := Nat.mod_add_div (x-1) w
    omega
  have hz : |(linearProfile w (p*w+j) : ℝ)-((profileA p : ℝ)*w+(profileB p : ℝ)*j)| ≤ 2 := by
    exact_mod_cast linearProfile_error w p j hp hj₀ hj₁
  rw [hdecomp, affineValue_at_block w p j hj₀ hj₁]
  linarith only [(abs_le.mp hz).1]

theorem exact_g24_bathtub (i : ℕ) (hi : i < 130) (w : ℕ) (hw : 1 ≤ w) (d : ℕ → Bool) :
    let I := scaledCell i w
    let y := (((I.filter (fun x => d x = true)).card : ℝ)/((g24Length i : ℝ)*w))
    2*(1096*(w : ℝ))^2*(bathAlpha i*y+bathBeta i*y^2) -
      (6*(g24Length i : ℝ)^2+2*g24Length i)*w ≤
      ∑ x ∈ I, (linearProfile w x : ℝ) * ((d x).toNat : ℝ) :=
  g24_bath_indicator i hi w hw d (fun x => (linearProfile w x : ℝ))
    (affineValue_le_linearProfile i hi w hw)

noncomputable def cellDensity (w : ℕ) (d : ℕ → Bool) (i : ℕ) : ℝ :=
  ((scaledCell i w).filter (fun x => d x = true)).card / ((g24Length i : ℝ)*w)

set_option maxRecDepth 10000 in
theorem g24_bath_error_total : (∑ i ∈ range 130, (6*g24Length i^2+2*g24Length i : ℕ)) = 76880 := by
  decide +kernel

theorem exact_g24_bathtub_sum (w : ℕ) (hw : 1 ≤ w) (d : ℕ → Bool) :
    2*(1096*(w : ℝ))^2 *
        (∑ i ∈ range 130, (bathAlpha i*cellDensity w d i+bathBeta i*(cellDensity w d i)^2)) -
      76880*(w : ℝ) ≤
      ∑ i ∈ range 130, ∑ x ∈ scaledCell i w, (linearProfile w x : ℝ) * ((d x).toNat : ℝ) := by
  have hsum := sum_le_sum (s := range 130) (fun i hi => exact_g24_bathtub i (mem_range.mp hi) w hw d)
  change (∑ i ∈ range 130,
      (2*(1096*(w : ℝ))^2*(bathAlpha i*cellDensity w d i+bathBeta i*(cellDensity w d i)^2) -
        (6*(g24Length i : ℝ)^2+2*g24Length i)*w)) ≤ _ at hsum
  have hE : (∑ i ∈ range 130, (6*(g24Length i : ℝ)^2+2*g24Length i)) = 76880 := by
    exact_mod_cast g24_bath_error_total
  rwa [sum_sub_distrib, ← mul_sum, ← sum_mul, hE] at hsum

end OMA.Erdos1186G24Profile

end

section

/-
The exact quadratic energy expansion for a flip of the PRS reference colouring.
The window is directed, so its two mixed terms give the row and column sums
in the verified linear profile.
-/

namespace OMA.Erdos1186G24Energy

open Finset
open scoped BigOperators
open OMA.Erdos1186ProfilePrefix OMA.Erdos1186G24Profile

def quadraticEnergy (n : ℕ) (u : ℕ → ℤ) : ℤ :=
  ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, window n x y * u x * u y

def linearProfileFor (n : ℕ) (r : ℕ → ℤ) (x : ℕ) : ℤ :=
  -r x * ((∑ y ∈ Icc 1 n, window n x y * r y) +
    (∑ y ∈ Icc 1 n, window n y x * r y))

theorem quadraticEnergy_expand (n : ℕ) (r m : ℕ → ℤ) :
    quadraticEnergy n (fun x => r x * (1 - 2*m x)) - quadraticEnergy n r =
      2 * ((∑ x ∈ Icc 1 n, linearProfileFor n r x * m x) +
        2 * quadraticEnergy n (fun x => r x * m x)) := by
  let I := Icc 1 n
  let A := ∑ x ∈ I, ∑ y ∈ I, window n x y * (r x*m x) * r y
  let B := ∑ x ∈ I, ∑ y ∈ I, window n x y * r x * (r y*m y)
  have hterm (x y : ℕ) :
      window n x y * (r x*(1-2*m x)) * (r y*(1-2*m y)) - window n x y * r x * r y =
        (-2) * (window n x y * (r x*m x) * r y) +
          (-2) * (window n x y * r x * (r y*m y)) +
          4 * (window n x y * (r x*m x) * (r y*m y)) := by ring
  have henergy : quadraticEnergy n (fun x => r x*(1-2*m x)) - quadraticEnergy n r =
      -2*A-2*B+4*quadraticEnergy n (fun x => r x*m x) := by
    unfold quadraticEnergy
    simp_rw [← sum_sub_distrib, hterm, sum_add_distrib, ← mul_sum]
    dsimp only [A,B,I]
    ring
  have hlocal (x : ℕ) : linearProfileFor n r x*m x =
      -(∑ y ∈ I, window n x y * (r x*m x) * r y) -
        ∑ y ∈ I, window n y x * r y * (r x*m x) := by
    have h₁ : (∑ y ∈ I, window n x y * (r x*m x) * r y) =
        (r x*m x) * ∑ y ∈ I, window n x y * r y := by
      rw [mul_sum]
      exact sum_congr rfl (fun y _ => by ring)
    have h₂ : (∑ y ∈ I, window n y x * r y * (r x*m x)) =
        (r x*m x) * ∑ y ∈ I, window n y x * r y := by
      rw [mul_sum]
      exact sum_congr rfl (fun y _ => by ring)
    rw [h₁, h₂]
    unfold linearProfileFor
    dsimp only [I]
    ring
  have hswap : (∑ x ∈ I, ∑ y ∈ I, window n y x * r y * (r x*m x)) = B := by
    unfold B
    rw [sum_comm]
  have hlinear : (∑ x ∈ I, linearProfileFor n r x*m x) = -A-B := by
    simp_rw [hlocal, sum_sub_distrib, sum_neg_distrib]
    rw [hswap]
  rw [henergy]
  change _ = 2*((∑ x ∈ I, linearProfileFor n r x*m x)+2*quadraticEnergy n (fun x => r x*m x))
  rw [hlinear]
  ring

def bothFlippedEnergy (w : ℕ) (d : ℕ → Bool) : ℤ :=
  quadraticEnergy (1096*w) (fun x => signedColor w x * ((d x).toNat : ℤ))

theorem g24_energy_expansion (w : ℕ) (d : ℕ → Bool) :
    quadraticEnergy (1096*w) (fun x => signedColor w x * (1-2*((d x).toNat : ℤ))) -
        quadraticEnergy (1096*w) (signedColor w) =
      2 * ((∑ x ∈ Icc 1 (1096*w), linearProfile w x * ((d x).toNat : ℤ)) +
        2 * bothFlippedEnergy w d) :=
  quadraticEnergy_expand (1096*w) (signedColor w) (fun x => ((d x).toNat : ℤ))

end OMA.Erdos1186G24Energy

end

section

/-
The PRS signs are constant on the checked G24 cells. This uses the audited
G24 endpoints from the Snively certificate and checks every unit cell.
-/

namespace OMA.Erdos1186G24Profile

open Finset OMA.Erdos1186Region2

def cellSignCheck (i : ℕ) : Bool :=
  (List.range' (g24Endpoint i) (g24Length i)).all (fun p =>
    decide (unitSign p = if g24Sign i then (1 : ℤ) else -1))

set_option maxRecDepth 10000 in
theorem g24_cell_sign_checks : (List.range 130).all cellSignCheck = true := by
  decide +kernel

theorem unitSign_on_g24_cell (i : ℕ) (hi : i < 130) (p : ℕ) (hp : p ∈ cellUnits i) :
    unitSign p = if g24Sign i then (1 : ℤ) else -1 := by
  have hc : cellSignCheck i = true :=
    List.all_eq_true.mp g24_cell_sign_checks i (List.mem_range.mpr hi)
  have h : p ∈ List.range' (g24Endpoint i) (g24Length i) :=
    List.mem_range'_1.mpr (mem_Ico.mp hp)
  exact of_decide_eq_true (List.all_eq_true.mp hc p h)

theorem signedColor_on_g24_cell (w : ℕ) (hw : 0 < w) (i : ℕ) (hi : i < 130)
    {x : ℕ} (hx : x ∈ scaledCell i w) :
    signedColor w x = if g24Sign i then (1 : ℤ) else -1 := by
  have hb := mem_Ioc.mp hx
  have hp : (x-1)/w ∈ cellUnits i := by
    rw [cellUnits, mem_Ico]
    exact ⟨(Nat.le_div_iff_mul_le hw).mpr (by omega), (Nat.div_lt_iff_lt_mul hw).mpr (by omega)⟩
  exact unitSign_on_g24_cell i hi _ hp

theorem signedColor_product_on_g24_cells (w : ℕ) (hw : 0 < w)
    (i j : ℕ) (hi : i < 130) (hj : j < 130) {x y : ℕ}
    (hx : x ∈ scaledCell i w) (hy : y ∈ scaledCell j w) :
    signedColor w x * signedColor w y = if g24Sign i = g24Sign j then (1 : ℤ) else -1 := by
  rw [signedColor_on_g24_cell w hw i hi hx, signedColor_on_g24_cell w hw j hj hy]
  cases g24Sign i <;> cases g24Sign j <;> decide

end OMA.Erdos1186G24Profile

end

section

/- Boundary cells in the discrete-to-continuum comparison for Erdős 1186. -/

namespace OMA.Erdos1186GridBoundary

open Finset

/-- The signed difference between twice a midpoint index and an endpoint index. -/
def signedOffset (a b : ℕ) : ℤ := 2 * (b : ℤ) - (a : ℤ)

/-- The four offsets of cells on the two boundaries of the endpoint–midpoint region. -/
def boundaryOffsets (n : ℕ) : Finset ℤ := {0, 1, (n : ℤ), (n : ℤ) + 1}

/-- The ordered pairs of cell indices in the (n)-by-(n) grid. -/
def gridPairs (n : ℕ) : Finset (ℕ × ℕ) := Icc 1 n ×ˢ Icc 1 n

/-- The cells on which continuum membership may differ from the discrete count. -/
def boundaryPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (gridPairs n).filter (fun p => signedOffset p.1 p.2 ∈ boundaryOffsets n)

private theorem boundaryOffsets_card_le (n : ℕ) : (boundaryOffsets n).card ≤ 4 := by
  have h₀ := card_insert_le (0 : ℤ) {1, (n : ℤ), (n : ℤ) + 1}
  have h₁ := card_insert_le (1 : ℤ) {(n : ℤ), (n : ℤ) + 1}
  have h₂ := card_insert_le (n : ℤ) {(n : ℤ) + 1}
  rw [card_singleton] at h₂
  unfold boundaryOffsets
  omega

/-- A midpoint index and a boundary offset determine the endpoint index. -/
theorem boundaryPairs_card_le (n : ℕ) : (boundaryPairs n).card ≤ 4 * n := by
  calc
    _ ≤ (Icc 1 n ×ˢ boundaryOffsets n).card := by
      apply card_le_card_of_injOn (fun p => (p.2, signedOffset p.1 p.2))
      · intro p hp
        simp only [mem_coe, boundaryPairs, gridPairs, mem_filter, mem_product] at hp ⊢
        exact ⟨hp.1.2, hp.2⟩
      · intro p _ q _ hpq
        have hb : p.2 = q.2 := congrArg Prod.fst hpq
        have ho : signedOffset p.1 p.2 = signedOffset q.1 q.2 := congrArg Prod.snd hpq
        apply Prod.ext _ hb
        unfold signedOffset at ho
        omega
    _ = n * (boundaryOffsets n).card := by simp
    _ ≤ 4 * n := (Nat.mul_le_mul_left n (boundaryOffsets_card_le n)).trans_eq (Nat.mul_comm n 4)

/-- On cells open on the left and closed on the right, the normalized offset
lies strictly between the integer offset minus two and that offset plus one. -/
theorem scaled_offset_bounds {n a b : ℕ} (hn : 0 < n) {x y : ℝ}
    (hx : x ∈ Set.Ioc (((a : ℝ) - 1) / n) ((a : ℝ) / n))
    (hy : y ∈ Set.Ioc (((b : ℝ) - 1) / n) ((b : ℝ) / n)) :
    ((signedOffset a b : ℤ) : ℝ) - 2 < (2 * y - x) * n ∧
      (2 * y - x) * n < ((signedOffset a b : ℤ) : ℝ) + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hxl := (div_lt_iff₀ hnR).mp hx.1
  have hxu := (le_div_iff₀ hnR).mp hx.2
  have hyl := (div_lt_iff₀ hnR).mp hy.1
  have hyu := (le_div_iff₀ hnR).mp hy.2
  push_cast [signedOffset]
  exact ⟨by linarith only [hxu, hyl], by linarith only [hxl, hyu]⟩

/-- Off the four boundary offsets, membership in the normalized continuum strip
agrees with the discrete endpoint–midpoint test throughout each half-open cell. -/
theorem strip_iff_of_not_boundary {n a b : ℕ} (hn : 0 < n)
    (hbad : signedOffset a b ∉ boundaryOffsets n) {x y : ℝ}
    (hx : x ∈ Set.Ioc (((a : ℝ) - 1) / n) ((a : ℝ) / n))
    (hy : y ∈ Set.Ioc (((b : ℝ) - 1) / n) ((b : ℝ) / n)) :
    (0 ≤ 2 * y - x ∧ 2 * y - x ≤ 1) ↔ a + 1 ≤ 2 * b ∧ 2 * b ≤ a + n := by
  let d := signedOffset a b
  change d ∉ boundaryOffsets n at hbad
  have hne : d ≠ 0 ∧ d ≠ 1 ∧ d ≠ (n : ℤ) ∧ d ≠ (n : ℤ) + 1 := by
    simpa only [boundaryOffsets, mem_insert, mem_singleton, not_or] using hbad
  obtain ⟨hlo, hhi⟩ := scaled_offset_bounds hn hx hy
  change (d : ℝ) - 2 < (2 * y - x) * n at hlo
  change (2 * y - x) * n < (d : ℝ) + 1 at hhi
  have hdisc : (1 ≤ d ∧ d ≤ (n : ℤ)) ↔ a + 1 ≤ 2 * b ∧ 2 * b ≤ a + n := by
    dsimp [d, signedOffset]
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : (0 ≤ 2 * y - x ∧ 2 * y - x ≤ 1) ↔
      (0 ≤ (2 * y - x) * n ∧ (2 * y - x) * n ≤ n) := by
    rw [← le_div_iff₀ hnR, div_self hnR.ne']
    simp [mul_nonneg_iff_of_pos_right hnR]
  rw [← hdisc, hscale]
  constructor
  · intro ⟨hL, hU⟩
    have hd₀ : 0 ≤ d := by
      by_contra! h
      have hR : (d : ℝ) ≤ -1 := by exact_mod_cast (show d ≤ -1 by omega)
      linarith only [hR, hL, hhi]
    have hd₁ : d ≤ (n : ℤ) + 1 := by
      by_contra! h
      have hR : (n : ℝ) + 2 ≤ (d : ℝ) := by
        exact_mod_cast (show (n : ℤ) + 2 ≤ d by omega)
      linarith only [hR, hU, hlo]
    omega
  · intro ⟨hL, hU⟩
    have hL' : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    have hU' : (d : ℝ) + 1 ≤ n := by
      exact_mod_cast (show d + 1 ≤ (n : ℤ) by omega)
    exact ⟨by linarith only [hL', hlo], by linarith only [hU', hhi]⟩

/-- A unit error supported on the boundary cells changes a sum by at most their count. -/
theorem abs_sum_sub_le_boundary_card (n : ℕ) (u v : ℕ × ℕ → ℤ)
    (hagree : ∀ p ∈ gridPairs n, p ∉ boundaryPairs n → u p = v p)
    (herror : ∀ p ∈ boundaryPairs n, |u p - v p| ≤ 1) :
    |(∑ p ∈ gridPairs n, u p) - (∑ p ∈ gridPairs n, v p)| ≤
      ((boundaryPairs n).card : ℤ) := by
  rw [← sum_sub_distrib]
  have hsub : (boundaryPairs n) ⊆ gridPairs n := filter_subset _ _
  rw [← sum_subset hsub (fun p hp hb => sub_eq_zero.mpr (hagree p hp hb))]
  calc
    _ ≤ ∑ p ∈ boundaryPairs n, |u p - v p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ boundaryPairs n, (1 : ℤ) := sum_le_sum herror
    _ = _ := by simp

end OMA.Erdos1186GridBoundary

end

section

/- The grid quarter-area kernel differs from the discrete strip only at boundary offsets. -/

namespace OMA.Erdos1186QuarterKernel

open Finset OMA.Erdos1186GridBoundary

def quarter (n : ℕ) (p : ℕ × ℕ) : ℤ :=
  let r := signedOffset p.1 p.2
  if 2 ≤ r ∧ r ≤ (n : ℤ) - 1 then 4 else
  if r = 1 ∨ r = n then 3 else
  if r = 0 ∨ r = (n : ℤ) + 1 then 1 else 0

def discrete4 (n : ℕ) (p : ℕ × ℕ) : ℤ :=
  if 1 ≤ signedOffset p.1 p.2 ∧ signedOffset p.1 p.2 ≤ n then 4 else 0

theorem unit_error {n : ℕ} (hn : 0 < n) (p : ℕ × ℕ) :
    |quarter n p - discrete4 n p| ≤ 1 := by
  unfold quarter discrete4
  dsimp only
  split_ifs <;> norm_num at * <;> omega

theorem agrees_off_boundary {n : ℕ} (p : ℕ × ℕ)
    (hp : signedOffset p.1 p.2 ∉ boundaryOffsets n) : quarter n p = discrete4 n p := by
  let r := signedOffset p.1 p.2
  have hne : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ (n : ℤ) ∧ r ≠ (n : ℤ) + 1 := by
    simpa only [boundaryOffsets, mem_insert, mem_singleton, not_or] using hp
  change (if 2 ≤ r ∧ r ≤ (n : ℤ) - 1 then 4 else
    if r = 1 ∨ r = n then 3 else
    if r = 0 ∨ r = (n : ℤ) + 1 then 1 else 0) = (if 1 ≤ r ∧ r ≤ n then 4 else 0)
  have he : (2 ≤ r ∧ r ≤ (n : ℤ) - 1) ↔ 1 ≤ r ∧ r ≤ (n : ℤ) := by omega
  simp only [he, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2, or_self, if_false]

theorem error_on_subgrid {n : ℕ} (hn : 0 < n) (s : Finset (ℕ × ℕ))
    (hs : s ⊆ gridPairs n) :
    |(∑ p ∈ s, quarter n p) - (∑ p ∈ s, discrete4 n p)| ≤ 4 * (n : ℤ) := by
  classical
  let u (p : ℕ × ℕ) := if p ∈ s then quarter n p else 0
  let v (p : ℕ × ℕ) := if p ∈ s then discrete4 n p else 0
  have hs' : (gridPairs n).filter (fun p => p ∈ s) = s := by
    ext p
    simp only [mem_filter]
    exact ⟨And.right, fun hp => ⟨hs hp, hp⟩⟩
  have hu : (∑ p ∈ gridPairs n, u p) = ∑ p ∈ s, quarter n p := by
    rw [← hs', sum_filter]
  have hv : (∑ p ∈ gridPairs n, v p) = ∑ p ∈ s, discrete4 n p := by
    rw [← hs', sum_filter]
  rw [← hu, ← hv]
  refine (abs_sum_sub_le_boundary_card n u v ?_ ?_).trans ?_
  · intro p hp houtside
    by_cases hp' : p ∈ s
    · simp only [u, v, if_pos hp']
      apply agrees_off_boundary
      intro h
      exact houtside (mem_filter.mpr ⟨hp, h⟩)
    · simp only [u, v, if_neg hp']
  · intro p _
    by_cases hp : p ∈ s
    · simpa only [u, v, if_pos hp] using unit_error hn p
    · simp [u, v, hp]
  · exact_mod_cast boundaryPairs_card_le n

end OMA.Erdos1186QuarterKernel

end

section

/- Exact quarter-area sums under subdivision of a grid cell. -/

namespace OMA.Erdos1186QuarterSubdivision

open Finset OMA.Erdos1186QuarterKernel OMA.Erdos1186GridBoundary

private def primitive (q x y : ℤ) : ℤ := max (q + x - 2*y) 0 ^ 2

private def rectangle (q x₀ x₁ y₀ y₁ : ℤ) : ℤ :=
  primitive q x₁ y₀ - primitive q x₀ y₀ - primitive q x₁ y₁ + primitive q x₀ y₁

private theorem sum_rectangle_row (q x₀ x₁ y₀ : ℤ) (m : ℕ) :
    (∑ j ∈ range m, rectangle q x₀ x₁ (y₀ + j) (y₀ + j + 1)) =
      rectangle q x₀ x₁ y₀ (y₀ + m) := by
  induction m with
  | zero => simp [rectangle]
  | succ m ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.cast_succ, ← add_assoc, rectangle]
    ring

private theorem sum_rectangle_grid (q x₀ y₀ : ℤ) (n m : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range m,
      rectangle q (x₀ + i) (x₀ + i + 1) (y₀ + j) (y₀ + j + 1)) =
      rectangle q x₀ (x₀ + n) y₀ (y₀ + m) := by
  simp_rw [sum_rectangle_row]
  induction n with
  | zero => simp [rectangle]
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.cast_succ, ← add_assoc, rectangle]
    ring

private theorem scale_primitive (w q x y : ℤ) (hw : 0 ≤ w) :
    primitive (w*q) (w*x) (w*y) = w^2 * primitive q x y := by
  unfold primitive
  rw [show w*q + w*x - 2*(w*y) = w*(q+x-2*y) by ring]
  by_cases hx : 0 ≤ q+x-2*y
  · rw [max_eq_left (mul_nonneg hw hx), max_eq_left hx]
    ring
  · have hx' := le_of_not_ge hx
    rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hw hx'), max_eq_right hx']
    simp

private theorem scale_rectangle (w q a b c d : ℤ) (hw : 0 ≤ w) :
    rectangle (w*q) (w*a) (w*b) (w*c) (w*d) = w^2 * rectangle q a b c d := by
  simp only [rectangle, scale_primitive w _ _ _ hw]
  ring

private theorem rectangle_value (q a b : ℤ) :
    rectangle q (a-1) a (b-1) b =
      if 2*b-a ≤ q-1 then 4 else if 2*b-a = q then 3 else
      if 2*b-a = q+1 then 1 else 0 := by
  let h := q + a - 2*b
  have h1 : q + a - 2*(b-1) = h+2 := by dsimp [h]; ring
  have h2 : q + (a-1) - 2*(b-1) = h+1 := by dsimp [h]; ring
  have h3 : q + (a-1) - 2*b = h-1 := by dsimp [h]; ring
  unfold rectangle primitive
  rw [h1,h2,h3]
  change max (h+2) 0 ^ 2 - max (h+1) 0 ^ 2 - max h 0 ^ 2 + max (h-1) 0 ^ 2 = _
  by_cases hl : 2*b-a ≤ q-1
  · have hh : 1 ≤ h := by dsimp [h]; omega
    rw [if_pos hl, max_eq_left (by omega), max_eq_left (by omega), max_eq_left (by omega), max_eq_left (by omega)]
    ring
  · by_cases he : 2*b-a = q
    · have hz : h = 0 := by dsimp [h]; omega
      norm_num [hl, he, hz]
    · by_cases he' : 2*b-a = q+1
      · have hm : h = -1 := by dsimp [h]; omega
        simpa only [if_neg hl, if_neg he, if_pos he', hm] using
          (show max ((-1 : ℤ)+2) 0^2 - max ((-1 : ℤ)+1) 0^2 -
            max (-1 : ℤ) 0^2 + max ((-1 : ℤ)-1) 0^2 = 1 by decide)
      · have hm : h ≤ -2 := by dsimp [h]; omega
        rw [if_neg hl, if_neg he, if_neg he', max_eq_right (by omega), max_eq_right (by omega),
          max_eq_right (by omega), max_eq_right (by omega)]
        norm_num

private theorem rectangle_strip_eq_quarter {n : ℕ} (hn : 2 ≤ n) (a b : ℕ) :
    rectangle n ((a:ℤ)-1) a ((b:ℤ)-1) b - rectangle 0 ((a:ℤ)-1) a ((b:ℤ)-1) b =
      quarter n (a,b) := by
  rw [rectangle_value, rectangle_value]
  simp only [quarter, signedOffset]
  split_ifs <;> norm_num at * <;> omega

theorem quarter_subdivision (n w a b : ℕ) (hn : 2 ≤ n) (hw : 0 < w)
    (ha : 0 < a) (hb : 0 < b) :
    (∑ i ∈ range w, ∑ j ∈ range w,
      quarter (n*w) ((a-1)*w+i+1, (b-1)*w+j+1)) = (w : ℤ)^2 * quarter n (a,b) := by
  have hn' : 2 ≤ n*w := hn.trans (Nat.le_mul_of_pos_right _ hw)
  have left (c : ℕ) (hc : 0 < c) (i : ℕ) :
      ((↑((c-1)*w+i+1) : ℤ)-1) = (w:ℤ)*((c:ℤ)-1)+i := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ c)]
    ring
  have right (c : ℕ) (hc : 0 < c) (i : ℕ) :
      (↑((c-1)*w+i+1) : ℤ) = (w:ℤ)*((c:ℤ)-1)+i+1 := by
    have h := left c hc i
    omega
  simp_rw [← rectangle_strip_eq_quarter hn', left a ha, left b hb, right a ha, right b hb,
    sum_sub_distrib, sum_rectangle_grid]
  have ax : (w:ℤ)*((a:ℤ)-1)+w = (w:ℤ)*a := by ring
  have bx : (w:ℤ)*((b:ℤ)-1)+w = (w:ℤ)*b := by ring
  rw [ax, bx, Nat.cast_mul, mul_comm (n:ℤ) (w:ℤ)]
  have scale0 := scale_rectangle (w:ℤ) 0 ((a:ℤ)-1) a ((b:ℤ)-1) b (Int.natCast_nonneg _)
  simp only [mul_zero] at scale0
  rw [scale_rectangle _ _ _ _ _ _ (Int.natCast_nonneg _), scale0, ← rectangle_strip_eq_quarter hn]
  ring

end OMA.Erdos1186QuarterSubdivision

end

section

/- Exact area sums for coarse rectangles and their fine grid subdivisions. -/

namespace OMA.Erdos1186BlockRefinement

open Finset OMA.Erdos1186QuarterKernel OMA.Erdos1186QuarterSubdivision

private theorem sum_Ioc_length (a w : ℕ) (f : ℕ → ℤ) :
    (∑ x ∈ Ioc a (a+w), f x) = ∑ i ∈ range w, f (a+i+1) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Nat.add_succ, Finset.sum_Ioc_succ_top (Nat.le_add_right _ _) f,
      sum_range_succ, ih]

private theorem sum_scaled_Ioc (a b w : ℕ) (hab : a ≤ b) (f : ℕ → ℤ) :
    (∑ x ∈ Ioc (a*w) (b*w), f x) =
      ∑ r ∈ Ioc a b, ∑ i ∈ range w, f ((r-1)*w+i+1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hstep : b*w ≤ (b+1)*w := Nat.mul_le_mul_right w (Nat.le_succ b)
    rw [← Finset.sum_Ioc_consecutive f (Nat.mul_le_mul_right w hab) hstep,
      Finset.sum_Ioc_succ_top hab, ih]
    simp only [Nat.add_mul, one_mul, Nat.add_sub_cancel_right]
    rw [sum_Ioc_length]

theorem rectangle_quarter_subdivision (n w a₀ a₁ b₀ b₁ : ℕ)
    (hn : 2 ≤ n) (hw : 0 < w) (ha : a₀ ≤ a₁) (hb : b₀ ≤ b₁) :
    (∑ x ∈ Ioc (a₀*w) (a₁*w), ∑ y ∈ Ioc (b₀*w) (b₁*w), quarter (n*w) (x,y)) =
      (w:ℤ)^2 * ∑ a ∈ Ioc a₀ a₁, ∑ b ∈ Ioc b₀ b₁, quarter n (a,b) := by
  rw [sum_scaled_Ioc a₀ a₁ w ha]
  simp_rw [sum_scaled_Ioc b₀ b₁ w hb]
  calc
    _ = ∑ a ∈ Ioc a₀ a₁, ∑ b ∈ Ioc b₀ b₁, ∑ i ∈ range w, ∑ j ∈ range w,
        quarter (n*w) ((a-1)*w+i+1,(b-1)*w+j+1) := by
      apply sum_congr rfl
      intro a _
      exact sum_comm
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro a hma
      apply sum_congr rfl
      intro b hmb
      exact quarter_subdivision n w a b hn hw ((Nat.zero_le _).trans_lt (mem_Ioc.mp hma).1)
        ((Nat.zero_le _).trans_lt (mem_Ioc.mp hmb).1)

end OMA.Erdos1186BlockRefinement

end

section

/- Comparing a refined rectangle's strip count with its quarter-area sum. -/
namespace OMA.Erdos1186StripCount
open Finset OMA.Erdos1186GridBoundary OMA.Erdos1186QuarterKernel OMA.Erdos1186BlockRefinement

theorem rectangle_strip_error (n w a₀ a₁ b₀ b₁ : ℕ)
    (hn : 2 ≤ n) (hw : 0 < w) (ha : a₀ ≤ a₁) (hb : b₀ ≤ b₁)
    (hai : a₁ ≤ n) (hbi : b₁ ≤ n) :
    let F := Ioc (a₀*w) (a₁*w) ×ˢ Ioc (b₀*w) (b₁*w)
    let inside := F.filter (fun p => 1 ≤ signedOffset p.1 p.2 ∧ signedOffset p.1 p.2 ≤ n*w)
    |(w:ℤ)^2 * (∑ a ∈ Ioc a₀ a₁, ∑ b ∈ Ioc b₀ b₁, quarter n (a,b)) - 4*inside.card| ≤
      4 * ((n*w : ℕ):ℤ) := by
  intro F inside
  have hF : F ⊆ gridPairs (n*w) := by
    rintro ⟨a,b⟩ hp
    simp only [F, gridPairs, mem_product, mem_Ioc, mem_Icc] at hp ⊢
    exact ⟨⟨by omega, hp.1.2.trans (Nat.mul_le_mul_right _ hai)⟩,
      ⟨by omega, hp.2.2.trans (Nat.mul_le_mul_right _ hbi)⟩⟩
  have hArea : (∑ p ∈ F, quarter (n*w) p) =
      (w:ℤ)^2 * (∑ a ∈ Ioc a₀ a₁, ∑ b ∈ Ioc b₀ b₁, quarter n (a,b)) := by
    dsimp only [F]
    rw [sum_product]
    exact rectangle_quarter_subdivision n w a₀ a₁ b₀ b₁ hn hw ha hb
  have hCount : (∑ p ∈ F, discrete4 (n*w) p) = 4 * (inside.card : ℤ) := by
    dsimp only [discrete4, inside]
    rw [← sum_filter]
    simp [mul_comm]
  rw [← hArea, ← hCount]
  exact error_on_subgrid (Nat.mul_pos (by omega) hw) F hF

end OMA.Erdos1186StripCount

end

section

/- Bounds on a selected part of one grid-cell pair. -/

namespace OMA.Erdos1186PairCell

open Finset

theorem cell_bounds {α : Type*} (full chosen : Finset α) (strip : α → Prop)
    [DecidablePred strip] (sub : chosen ⊆ full) :
    max 0 ((chosen.card : ℝ) - ((full.filter (fun x => ¬ strip x)).card : ℝ)) ≤
      ((chosen.filter strip).card : ℝ) ∧
    max (-((full.filter strip).card : ℝ)) (-(chosen.card : ℝ)) ≤
      -((chosen.filter strip).card : ℝ) := by
  have hsplit := card_filter_add_card_filter_not (s := chosen) strip
  have hsplit' : ((chosen.filter strip).card : ℝ) +
       ((chosen.filter (fun x => ¬ strip x)).card : ℝ) = chosen.card := by exact_mod_cast hsplit
  have hout : ((chosen.filter (fun x => ¬ strip x)).card : ℝ) ≤
      (full.filter (fun x => ¬ strip x)).card := by
    exact_mod_cast card_le_card (filter_subset_filter _ sub)
  have hin : ((chosen.filter strip).card : ℝ) ≤ (full.filter strip).card := by
    exact_mod_cast card_le_card (filter_subset_filter _ sub)
  have hchosen : ((chosen.filter strip).card : ℝ) ≤ chosen.card := by
    exact_mod_cast card_le_card (filter_subset strip chosen)
  exact ⟨max_le (Nat.cast_nonneg _) (by linarith only [hsplit', hout]),
    max_le (neg_le_neg hin) (neg_le_neg hchosen)⟩

theorem approximate_cell_bounds {α : Type*} (full chosen : Finset α) (strip : α → Prop)
    [DecidablePred strip] (sub : chosen ⊆ full) (inside outside error : ℝ) (he : 0 ≤ error)
    (hin : ((full.filter strip).card : ℝ) ≤ inside + error)
    (hout : ((full.filter (fun x => ¬ strip x)).card : ℝ) ≤ outside + error) :
    max 0 ((chosen.card : ℝ) - outside) - error ≤ ((chosen.filter strip).card : ℝ) ∧
    max (-inside) (-(chosen.card : ℝ)) - error ≤ -((chosen.filter strip).card : ℝ) := by
  obtain ⟨hp, hn⟩ := cell_bounds full chosen strip sub
  have hp' := max_le_iff.mp hp
  have hn' := max_le_iff.mp hn
  constructor <;> apply sub_le_iff_le_add.mpr
  · exact max_le (by linarith only [hp'.1, he]) (by linarith only [hp'.2, hout])
  · exact max_le (by linarith only [hn'.1, hin]) (by linarith only [hn'.2, he])

end OMA.Erdos1186PairCell

end

section

/- A lower bound on a signed cut in one pair of cells. -/
namespace OMA.Erdos1186RectangleCut

open Finset OMA.Erdos1186GridBoundary OMA.Erdos1186QuarterKernel
open OMA.Erdos1186StripCount OMA.Erdos1186PairCell

private def strip (N : ℕ) (p : ℕ × ℕ) : Prop :=
  1 ≤ signedOffset p.1 p.2 ∧ signedOffset p.1 p.2 ≤ N

private instance (N : ℕ) : DecidablePred (strip N) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem signed_rectangle_cut_bound (n w a₀ a₁ b₀ b₁ : ℕ)
    (hn : 2 ≤ n) (hw : 0 < w) (ha : a₀ ≤ a₁) (hb : b₀ ≤ b₁)
    (hai : a₁ ≤ n) (hbi : b₁ ≤ n) (d : ℕ → Bool) :
    let X := Ioc (a₀*w) (a₁*w)
    let Y := Ioc (b₀*w) (b₁*w)
    let A := X.filter fun x => d x = true
    let B := Y.filter fun y => d y = true
    let C := (A.card : ℝ) * (B.card : ℝ)
    let I := (w : ℝ)^2 / 4 * ((∑ a ∈ Ioc a₀ a₁, ∑ b ∈ Ioc b₀ b₁, quarter n (a,b)) : ℤ)
    let J := (w : ℝ)^2 * (a₁-a₀ : ℕ) * (b₁-b₀ : ℕ) - I
    let W := (((A ×ˢ B).filter (strip (n*w))).card : ℝ)
    max 0 (C - J) - (n*w : ℕ) ≤ W ∧ max (-I) (-C) - (n*w : ℕ) ≤ -W := by
  intro X Y A B C I J W
  let F := X ×ˢ Y
  let D := A ×ˢ B
  let S := F.filter (strip (n*w))
  let T := F.filter (fun p => ¬ strip (n*w) p)
  have hD : (D.card : ℝ) = C := by simp [D, C]
  have hW : ((D.filter (strip (n*w))).card : ℝ) = W := rfl
  have hF : (F.card : ℝ) = (w : ℝ)^2 * (a₁-a₀ : ℕ) * (b₁-b₀ : ℕ) := by
    dsimp only [F, X, Y]
    rw [card_product, Nat.card_Ioc, Nat.card_Ioc, ← Nat.sub_mul, ← Nat.sub_mul]
    push_cast
    ring
  have hsum : (S.card : ℝ) + T.card = F.card := by
    exact_mod_cast card_filter_add_card_filter_not (s := F) (strip (n*w))
  have herr := rectangle_strip_error n w a₀ a₁ b₀ b₁ hn hw ha hb hai hbi
  have herr' : |(w:ℤ)^2 * (∑ a ∈ Ioc a₀ a₁, ∑ b ∈ Ioc b₀ b₁, quarter n (a,b)) -
      4 * (S.card : ℤ)| ≤ 4 * ((n*w : ℕ) : ℤ) := herr
  have hcast : |(w:ℝ)^2 * ((∑ a ∈ Ioc a₀ a₁, ∑ b ∈ Ioc b₀ b₁, quarter n (a,b)) : ℤ) -
      4 * (S.card : ℝ)| ≤ 4 * ((n*w : ℕ) : ℝ) := by exact_mod_cast herr'
  obtain ⟨hl, hu⟩ := abs_le.mp hcast
  have hin : (S.card : ℝ) ≤ I + (n*w : ℕ) := by dsimp only [I]; linarith only [hl]
  have hout : (T.card : ℝ) ≤ J + (n*w : ℕ) := by dsimp only [J, I]; linarith only [hu, hsum, hF]
  have hDF : D ⊆ F := product_subset_product (filter_subset _ _) (filter_subset _ _)
  have h := approximate_cell_bounds F D (strip (n*w)) hDF I J
    ((n*w : ℕ) : ℝ) (by positivity) hin hout
  simpa only [hD, hW] using h

end OMA.Erdos1186RectangleCut

end

section

/- The mass of grid-cell densities is the normalized discrete mass. -/

namespace OMA.Erdos1186GridMass

open Finset

theorem sum_cells {A : Type*} [AddCommMonoid A] {p : ℕ → ℕ} {k : ℕ}
    (hp : MonotoneOn p (Set.Iic k)) (f : ℕ → A) :
    (∑ i ∈ range k, ∑ x ∈ Ioc (p i) (p (i + 1)), f x) = ∑ x ∈ Ioc (p 0) (p k), f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmon : MonotoneOn p (Set.Iic k) := hp.mono (Set.Iic_subset_Iic.mpr (Nat.le_succ k))
    rw [sum_range_succ, ih hmon]
    exact sum_Ioc_consecutive f
      (hp (Nat.zero_le _) (Nat.le_succ _) (Nat.zero_le _))
      (hp (Nat.le_succ _) (Set.mem_Iic.mpr le_rfl) (Nat.le_succ _))

theorem weighted_cell_average {p : ℕ → ℕ} {k L w : ℕ}
    (hp : StrictMonoOn p (Set.Iic k)) (hzero : p 0 = 0) (hend : p k = L)
    (hL : 0 < L) (hw : 0 < w) (f : ℕ → ℝ) :
    (∑ i ∈ range k,
      (↑(p (i + 1) - p i) : ℝ) / L *
        ((∑ x ∈ Ioc (p i * w) (p (i + 1) * w), f x) / ↑((p (i + 1) - p i) * w))) =
      (∑ x ∈ Ioc 0 (L * w), f x) / ↑(L * w) := by
  let pw (i : ℕ) := p i * w
  have hpw : MonotoneOn pw (Set.Iic k) :=
    fun _ ha _ hb hab => Nat.mul_le_mul_right w (hp.monotoneOn ha hb hab)
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have cells := sum_cells hpw f
  have cancel (i : ℕ) (hi : i ∈ range k) :
      (↑(p (i + 1) - p i) : ℝ) / L *
        ((∑ x ∈ Ioc (pw i) (pw (i + 1)), f x) / ↑((p (i + 1) - p i) * w)) =
      (∑ x ∈ Ioc (pw i) (pw (i + 1)), f x) / ↑(L * w) := by
    have hi' := mem_range.mp hi
    have hstrict : p i < p (i + 1) := hp hi'.le (Nat.succ_le_of_lt hi') (Nat.lt_succ_self i)
    have hlen : (↑(p (i + 1) - p i) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hstrict))
    push_cast
    field_simp
  calc
    _ = ∑ i ∈ range k, (∑ x ∈ Ioc (pw i) (pw (i + 1)), f x) / ↑(L * w) :=
      sum_congr rfl cancel
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← sum_mul, cells]
      simp only [pw, hzero, hend, zero_mul]

theorem weighted_cut_average {p : ℕ → ℕ} {k L w : ℕ}
    (hp : StrictMonoOn p (Set.Iic k)) (hzero : p 0 = 0) (hend : p k = L)
    (hL : 0 < L) (hw : 0 < w) (d : ℕ → Bool) :
    (∑ i ∈ range k,
      (↑(p (i + 1) - p i) : ℝ) / L *
        ((∑ x ∈ Ioc (p i * w) (p (i + 1) * w), ((d x).toNat : ℝ)) /
          ↑((p (i + 1) - p i) * w))) =
      (((Icc 1 (L * w)).filter fun x => d x = true).card : ℝ) / ↑(L * w) := by
  rw [weighted_cell_average hp hzero hend hL hw]
  have hI : Ioc 0 (L * w) = Icc 1 (L * w) := by
    ext i
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hI]
  have hsign (x : ℕ) : ((d x).toNat : ℝ) = if d x = true then 1 else 0 := by
    cases d x <;> simp
  simp only [hsign, Finset.sum_boole]

end OMA.Erdos1186GridMass

end

section

/- Identify the checked G24 area and mass with the grid counts. -/
namespace OMA.Erdos1186G24Cut

open Finset OMA.Erdos1186GridBoundary OMA.Erdos1186QuarterKernel
open OMA.Erdos1186RectangleCut OMA.Erdos1186Region2

private theorem endpoint_steps :
    (List.range 130).all (fun i => decide (g24Endpoint i < g24Endpoint (i+1))) = true := by
  decide +kernel

theorem endpoint_mono : StrictMonoOn g24Endpoint (Set.Iic 130) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.mp endpoint_steps i (List.mem_range.mpr hi))

theorem endpoint_first : g24Endpoint 0 = 0 := by decide +kernel
theorem endpoint_last : g24Endpoint 130 = 1096 := by decide +kernel

private theorem end_bounds {i : ℕ} (hi : i < 130) :
    g24Endpoint i < g24Endpoint (i+1) ∧ g24Endpoint (i+1) ≤ 1096 := by
  constructor
  · exact endpoint_mono hi.le hi (Nat.lt_succ_self i)
  · rw [← endpoint_last]
    exact endpoint_mono.monotoneOn hi (Set.mem_Iic.mpr le_rfl) hi

private theorem quarter_eq (a b : ℕ) :
    (unitArea4 (2 * (b : ℤ) - a - 1) : ℤ) = quarter 1096 (a,b) := by
  unfold unitArea4 quarter signedOffset
  dsimp only [Prod.fst, Prod.snd]
  have h4 : (1 ≤ 2 * (b : ℤ) - a - 1 ∧ 2 * (b : ℤ) - a - 1 ≤ 1094) ↔
      (2 ≤ 2 * (b : ℤ) - a ∧ 2 * (b : ℤ) - a ≤ 1096 - 1) := by omega
  have h3 : (2 * (b : ℤ) - a - 1 = 0 ∨ 2 * (b : ℤ) - a - 1 = 1095) ↔
      (2 * (b : ℤ) - a = 1 ∨ 2 * (b : ℤ) - a = 1096) := by omega
  have h1 : (2 * (b : ℤ) - a - 1 = -1 ∨ 2 * (b : ℤ) - a - 1 = 1096) ↔
      (2 * (b : ℤ) - a = 0 ∨ 2 * (b : ℤ) - a = 1096 + 1) := by omega
  simp only [h4, h3, h1]
  split_ifs <;> simp_all <;> omega

private theorem sum_range'_Ioc (a b : ℕ) (f : ℕ → ℕ) :
    ((List.range' (a+1) (b-a)).map f).sum = ∑ i ∈ Ioc a b, f i := by
  rw [Nat.Ioc_eq_range']
  rfl

theorem grid_area (i j : ℕ) :
    (g24Area4 i j : ℤ) =
      ∑ a ∈ Ioc (g24Endpoint i) (g24Endpoint (i+1)),
        ∑ b ∈ Ioc (g24Endpoint j) (g24Endpoint (j+1)), quarter 1096 (a,b) := by
  rw [g24Area4_eq_unitGridArea]
  unfold unitGridArea
  simp_rw [sum_range'_Ioc, Nat.cast_sum, quarter_eq]

def cell (w i : ℕ) : Finset ℕ :=
  Ioc (g24Endpoint i * w) (g24Endpoint (i+1) * w)

def selected (w : ℕ) (d : ℕ → Bool) (i : ℕ) : Finset ℕ :=
  (cell w i).filter fun x => d x = true

noncomputable def density (w : ℕ) (d : ℕ → Bool) (i : ℕ) : ℝ :=
  ((selected w d i).card : ℝ) / ↑(g24Length i * w)

private theorem cell_card (w i : ℕ) : (cell w i).card = g24Length i * w := by
  rw [cell, Nat.card_Ioc, ← Nat.sub_mul, g24Length]

private theorem positive_cell (w i : ℕ) (hw : 0 < w) (hi : i < 130) :
    (0 : ℝ) < ↑(g24Length i * w) := by
  exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt (end_bounds hi).1) hw

theorem density_bounds (w : ℕ) (d : ℕ → Bool) (hw : 0 < w) {i : ℕ} (hi : i < 130) :
    0 ≤ density w d i ∧ density w d i ≤ 1 := by
  unfold density
  refine ⟨div_nonneg (Nat.cast_nonneg _) (positive_cell w i hw hi).le, ?_⟩
  apply (div_le_one (positive_cell w i hw hi)).mpr
  rw [← cell_card]
  exact_mod_cast card_le_card (filter_subset (fun x => d x = true) (cell w i))

theorem density_mass (w : ℕ) (hw : 0 < w) (d : ℕ → Bool) :
    g24Mass (density w d) =
      (((Icc 1 (1096*w)).filter fun x => d x = true).card : ℝ) / ↑(1096*w : ℕ) := by
  have hdensity (i : ℕ) :
      density w d i = (∑ x ∈ cell w i, ((d x).toNat : ℝ)) / ↑(g24Length i * w) := by
    unfold density selected
    congr 1
    have hsign (x : ℕ) : ((d x).toNat : ℝ) = if d x = true then 1 else 0 := by
      cases d x <;> simp
    simp only [hsign, Finset.sum_boole]
  unfold g24Mass cellCount
  simp_rw [hdensity]
  exact OMA.Erdos1186GridMass.weighted_cut_average endpoint_mono endpoint_first endpoint_last
    (by decide) hw d

def pairCount (w : ℕ) (d : ℕ → Bool) (i j : ℕ) : ℕ :=
  (((selected w d i) ×ˢ (selected w d j)).filter fun p =>
    1 ≤ signedOffset p.1 p.2 ∧ signedOffset p.1 p.2 ≤ 1096*w).card

private theorem length_density {w i : ℕ} (hw : 0 < w) (hi : i < 130) (d : ℕ → Bool) :
    (g24Length i : ℝ) * w * density w d i = (selected w d i).card := by
  have h := (positive_cell w i hw hi).ne'
  push_cast at h
  obtain ⟨hL, hw'⟩ := mul_ne_zero_iff.mp h
  unfold density
  push_cast
  field_simp [hL, hw']

theorem scale_pair_lower (w : ℕ) (hw : 0 < w) (d : ℕ → Bool) {i j : ℕ}
    (hi : i < 130) (hj : j < 130) :
    ((1096 : ℝ)*w)^2 * pairObjective i j (density w d i) (density w d j) -
        ((1096*w : ℕ) : ℝ) ≤
      if g24Sign i = g24Sign j then (pairCount w d i j : ℝ) else - (pairCount w d i j : ℝ) := by
  let C : ℝ := (selected w d i).card * (selected w d j).card
  let A : ℝ := (w : ℝ)^2 / 4 * g24Area4 i j
  let B : ℝ := (w : ℝ)^2 * g24Length i * g24Length j - A
  let W : ℝ := pairCount w d i j
  let D : ℝ := ((1096 : ℝ)*w)^2
  obtain ⟨hilo, hiup⟩ := end_bounds hi
  obtain ⟨hjlo, hjup⟩ := end_bounds hj
  have harea := signed_rectangle_cut_bound 1096 w _ _ _ _ (by decide) hw hilo.le hjlo.le hiup hjup d
  dsimp only at harea
  rw [← grid_area i j, Int.cast_natCast] at harea
  have hrect : max 0 (C-B) - ((1096*w : ℕ) : ℝ) ≤ W ∧
      max (-A) (-C) - ((1096*w : ℕ) : ℝ) ≤ -W := harea
  let u := density w d i
  let v := density w d j
  let P := (g24Length i : ℝ) * (g24Length j : ℝ) / 1096^2 * (u*v)
  let I := (g24Area4 i j : ℝ) / (4 * 1096^2)
  let J := (g24Length i : ℝ) * (g24Length j : ℝ) / 1096^2 - I
  have hP : D*P = C := calc
    _ = ((g24Length i : ℝ) * w * u) * ((g24Length j : ℝ) * w * v) := by
      dsimp only [D, P]
      ring
    _ = _ := by rw [length_density hw hi, length_density hw hj]
  have hI : D*I = A := by dsimp only [D, I, A]; ring
  have hJ : D*J = B := by
    dsimp only [J, B]
    rw [mul_sub, hI]
    dsimp only [D]
    ring
  change D * (if g24Sign i = g24Sign j then max 0 (P-J) else max (-I) (-P)) -
      ((1096*w : ℕ) : ℝ) ≤ if g24Sign i = g24Sign j then W else -W
  have hD : 0 ≤ D := sq_nonneg _
  by_cases hs : g24Sign i = g24Sign j
  · rw [if_pos hs, if_pos hs, mul_max_of_nonneg _ _ hD, mul_zero, mul_sub, hP, hJ]
    exact hrect.1
  · rw [if_neg hs, if_neg hs, mul_max_of_nonneg _ _ hD, mul_neg, mul_neg, hI, hP]
    exact hrect.2

theorem sum_cells {A : Type*} [AddCommMonoid A] (w : ℕ) (f : ℕ → A) :
    (∑ i ∈ range 130, ∑ x ∈ cell w i, f x) = ∑ x ∈ Icc 1 (1096*w), f x := by
  have hp : MonotoneOn (fun i => g24Endpoint i*w) (Set.Iic 130) := by
    intro i hi j hj hij
    exact Nat.mul_le_mul_right w (endpoint_mono.monotoneOn hi hj hij)
  have hs := OMA.Erdos1186GridMass.sum_cells hp f
  have he : Ioc 0 (1096*w) = Icc 1 (1096*w) := by
    ext x
    simp only [mem_Ioc, mem_Icc]
    omega
  simpa only [cell, endpoint_first, zero_mul, endpoint_last, he] using hs

theorem sum_pair_lower (w : ℕ) (hw : 0 < w) (d : ℕ → Bool) :
    ((1096 : ℝ)*w)^2 *
      (∑ i ∈ range 130, ∑ j ∈ range 130, pairObjective i j (density w d i) (density w d j)) -
        (130 : ℝ)^2 * (1096*w : ℕ) ≤
      ∑ i ∈ range 130, ∑ j ∈ range 130,
        if g24Sign i = g24Sign j then (pairCount w d i j : ℝ) else - (pairCount w d i j : ℝ) := by
  have h := sum_le_sum (s := range 130) fun i hi =>
    sum_le_sum (s := range 130) fun j hj => scale_pair_lower w hw d (mem_range.mp hi) (mem_range.mp hj)
  simp_rw [sum_sub_distrib, ← mul_sum] at h
  have herr : (∑ _i ∈ range 130, ∑ _j ∈ range 130, ((1096*w : ℕ) : ℝ)) =
      (130 : ℝ)^2 * (1096*w : ℕ) := by
    simp only [sum_const, card_range, nsmul_eq_mul]
    ring
  rwa [herr] at h

end OMA.Erdos1186G24Cut

end

section

/- The signed cut weight is minus half the change in the pair correlation. -/

namespace OMA.Erdos1186SignedCutEnergy

private def sign (b : Bool) : ℤ := if b then 1 else -1

private theorem correlation_change (r s x y : Bool) :
    sign (r ^^ x) * sign (s ^^ y) - sign r * sign s =
      -2 * (if x = y then 0 else if r = s then 1 else -1) := by
  cases r <;> cases s <;> cases x <;> cases y <;> decide

theorem signed_cut_energy_change {α : Type*} (R : Finset (α × α)) (ref d : α → Bool) :
    (∑ p ∈ R, sign (ref p.1 ^^ d p.1) * sign (ref p.2 ^^ d p.2)) -
        (∑ p ∈ R, sign (ref p.1) * sign (ref p.2)) =
      -2 * (∑ p ∈ R, (if d p.1 = d p.2 then 0 else
        if ref p.1 = ref p.2 then 1 else -1 : ℤ)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => correlation_change _ _ _ _

private theorem sign_multiplication (r d : Bool) :
    sign (r ^^ d) = sign r * (1 - 2 * (d.toNat : ℤ)) := by
  cases r <;> cases d <;> decide

theorem window_weighted_energy_change (n : ℕ) (ref d : ℕ → Bool) :
    let R := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p : ℕ × ℕ =>
      p.1 + 1 ≤ 2 * p.2 ∧ 2 * p.2 ≤ p.1 + n)
    let Q (u : ℕ → ℤ) := ∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.Icc 1 n,
      (if 1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n then 1 else 0) * u x * u y
    Q (fun x => sign (ref x) * (1 - 2 * ((d x).toNat : ℤ))) - Q (fun x => sign (ref x)) =
      -2 * (∑ p ∈ R, (if d p.1 = d p.2 then 0 else
        if ref p.1 = ref p.2 then 1 else -1 : ℤ)) := by
  classical
  intro R Q
  have Q_filter (u : ℕ → ℤ) : Q u = ∑ p ∈ R, u p.1 * u p.2 := by
    dsimp only [Q, R]
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have h : (x + 1 ≤ 2 * y ∧ 2 * y ≤ x + n) ↔
        (1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n) := by omega
    by_cases hx : x + 1 ≤ 2 * y ∧ 2 * y ≤ x + n
    · simp only [if_pos hx, if_pos (h.mp hx), one_mul]
    · have hy : ¬ (1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n) := fun hy => hx (h.mpr hy)
      simp only [if_neg hx, if_neg hy, zero_mul]
  rw [Q_filter, Q_filter]
  simp only [← sign_multiplication]
  exact signed_cut_energy_change R ref d

end OMA.Erdos1186SignedCutEnergy

end

section

/- Identify the exact published signed cut with the expanded G24 energy. -/

namespace OMA.Erdos1186G24Energy

open Finset
open scoped BigOperators
open OMA.Erdos1186G24Profile

def referenceShade (w x : ℕ) : Bool :=
  let b := (x-1)/(2*w)
  b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
    (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)

theorem signedColor_eq_shade (w x : ℕ) :
    signedColor w x = if referenceShade w x then (1 : ℤ) else -1 :=
  signedColor_eq_reference w x

def signedCutWeight (w : ℕ) (d : ℕ → Bool) : ℤ :=
  let n := 1096*w
  let R := (Icc 1 n ×ˢ Icc 1 n).filter (fun p : ℕ × ℕ => p.1+1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1+n)
  ∑ p ∈ R, if d p.1 = d p.2 then 0 else
    if referenceShade w p.1 = referenceShade w p.2 then 1 else -1

theorem g24_energy_change_eq_cut (w : ℕ) (d : ℕ → Bool) :
    quadraticEnergy (1096*w) (fun x => signedColor w x*(1-2*((d x).toNat : ℤ))) -
      quadraticEnergy (1096*w) (signedColor w) = -2*signedCutWeight w d := by
  have h := OMA.Erdos1186SignedCutEnergy.window_weighted_energy_change (1096*w) (referenceShade w) d
  change quadraticEnergy (1096*w)
      (fun x => (if referenceShade w x then (1 : ℤ) else -1)*(1-2*((d x).toNat : ℤ))) -
      quadraticEnergy (1096*w) (fun x => if referenceShade w x then (1 : ℤ) else -1) =
        -2*signedCutWeight w d at h
  simpa only [← signedColor_eq_shade] using h

theorem g24_cut_eq_negative_profile_and_pairs (w : ℕ) (d : ℕ → Bool) :
    signedCutWeight w d = -((∑ x ∈ Icc 1 (1096*w), linearProfile w x*((d x).toNat : ℤ)) +
      2*bothFlippedEnergy w d) := by
  have h := g24_energy_expansion w d
  rw [g24_energy_change_eq_cut w d] at h
  omega

end OMA.Erdos1186G24Energy

end

section

/- Assemble the signed-rectangle and linear-profile estimates. -/

namespace OMA.Erdos1186G24NearCut

open Finset OMA.Erdos1186G24Cut OMA.Erdos1186Region2 OMA.Erdos1186G24Profile
open OMA.Erdos1186ProfilePrefix OMA.Erdos1186GridBoundary OMA.Erdos1186G24Energy

private theorem signed_pair_count (w : ℕ) (d : ℕ → Bool) (r : ℕ → ℤ) (i j : ℕ)
    (hri : ∀ x ∈ cell w i, r x = if g24Sign i then 1 else -1)
    (hrj : ∀ y ∈ cell w j, r y = if g24Sign j then 1 else -1) :
    (∑ x ∈ cell w i, ∑ y ∈ cell w j,
      window (1096*w) x y * (r x * ((d x).toNat : ℤ)) * (r y * ((d y).toNat : ℤ))) =
      if g24Sign i = g24Sign j then (pairCount w d i j : ℤ) else - (pairCount w d i j : ℤ) := by
  let F := cell w i ×ˢ cell w j
  let strip (p : ℕ × ℕ) := 1 ≤ signedOffset p.1 p.2 ∧ signedOffset p.1 p.2 ≤ 1096*w
  let included (p : ℕ × ℕ) := d p.1 = true ∧ d p.2 = true ∧ strip p
  let sign : ℤ := if g24Sign i = g24Sign j then 1 else -1
  have hset : ((selected w d i ×ˢ selected w d j).filter strip) = F.filter included := by
    ext p
    simp only [selected, F, included, mem_filter, mem_product]
    tauto
  have hcard : pairCount w d i j = (F.filter included).card := congrArg Finset.card hset
  have hsign : (if g24Sign i then (1 : ℤ) else -1) * (if g24Sign j then 1 else -1) = sign := by
    cases hi : g24Sign i <;> cases hj : g24Sign j <;> simp [sign, hi, hj]
  have hproduct : (∑ p ∈ F, window (1096*w) p.1 p.2 *
      (r p.1 * ((d p.1).toNat : ℤ)) * (r p.2 * ((d p.2).toNat : ℤ))) =
      ∑ x ∈ cell w i, ∑ y ∈ cell w j,
        window (1096*w) x y * (r x * ((d x).toNat : ℤ)) * (r y * ((d y).toNat : ℤ)) := by
    dsimp only [F]
    rw [sum_product]
  rw [← hproduct]
  calc
    _ = ∑ p ∈ F, sign * (if included p then 1 else 0) := by
      apply sum_congr rfl
      intro p hp
      have hp' : p.1 ∈ cell w i ∧ p.2 ∈ cell w j := mem_product.mp hp
      rw [hri p.1 hp'.1, hrj p.2 hp'.2]
      have hm : window (1096*w) p.1 p.2 = if strip p then 1 else 0 := rfl
      rw [hm]
      by_cases hx : d p.1 = true <;> by_cases hy : d p.2 = true <;>
        by_cases ht : strip p <;> simp_all [included]
    _ = sign * (pairCount w d i j : ℤ) := by rw [← mul_sum, sum_boole, hcard]
    _ = _ := by split <;> simp [sign, *]

theorem both_flipped_partition (w : ℕ) (d : ℕ → Bool)
    (hsign : ∀ i < 130, ∀ x ∈ cell w i,
      signedColor w x = if g24Sign i then 1 else -1) :
    bothFlippedEnergy w d =
      ∑ i ∈ range 130, ∑ j ∈ range 130,
        if g24Sign i = g24Sign j then (pairCount w d i j : ℤ) else - (pairCount w d i j : ℤ) := by
  let f (x y : ℕ) :=
    window (1096*w) x y * (signedColor w x * ((d x).toNat : ℤ)) *
      (signedColor w y * ((d y).toNat : ℤ))
  change (∑ x ∈ Icc 1 (1096*w), ∑ y ∈ Icc 1 (1096*w), f x y) = _
  rw [← sum_cells w (fun x => ∑ y ∈ Icc 1 (1096*w), f x y)]
  simp_rw [← sum_cells w (f _)]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  exact signed_pair_count w d (signedColor w) i j
    (hsign i (mem_range.mp hi)) (hsign j (mem_range.mp hj))

end OMA.Erdos1186G24NearCut

end

section

/- Checked discrete transfer of the signed cut to the explicit G24 objective. -/

namespace OMA.Erdos1186G24NearCut

open Finset OMA.Erdos1186G24Cut OMA.Erdos1186Region2 OMA.Erdos1186G24Profile
open OMA.Erdos1186ProfilePrefix OMA.Erdos1186GridBoundary OMA.Erdos1186G24Energy

private theorem transfer (w : ℕ) (hw : 1 ≤ w) (d : ℕ → Bool) :
    (signedCutWeight w d : ℝ) + 2 * ((1096*w : ℕ) : ℝ)^2 * g24Objective (density w d) ≤
      110680 * ((1096*w : ℕ) : ℝ) := by
  have hw' : 0 < w := hw
  let y := density w d
  have hs (i : ℕ) (hi : i < 130) (x : ℕ) (hx : x ∈ cell w i) :
      signedColor w x = if g24Sign i then 1 else -1 := by
    apply signedColor_on_g24_cell w hw i hi
    rwa [scaledCell_eq_endpoints i hi w]
  have hQuad := congrArg (fun z : ℤ => (z : ℝ)) (both_flipped_partition w d hs)
  push_cast at hQuad
  have hP := sum_pair_lower w hw' d
  rw [← hQuad] at hP
  have hLin := exact_g24_bathtub_sum w hw d
  have hCoeff : (∑ i ∈ range 130, (bathAlpha i * cellDensity w d i +
        bathBeta i * (cellDensity w d i)^2)) =
      ∑ i ∈ range 130, (g24RealAlpha i * y i + g24RealBeta i * (y i)^2) := by
    apply sum_congr rfl
    intro i hi
    have h : cellDensity w d i = y i := by
      unfold cellDensity y density selected cell
      rw [scaledCell_eq_endpoints i (mem_range.mp hi) w]
      push_cast
      rfl
    rw [h]
    rfl
  have hLinear : (∑ i ∈ range 130, ∑ x ∈ scaledCell i w,
        (linearProfile w x : ℝ) * ((d x).toNat : ℝ)) =
      ∑ x ∈ Icc 1 (1096*w), (linearProfile w x : ℝ) * ((d x).toNat : ℝ) := by
    rw [← sum_cells w (fun x => (linearProfile w x : ℝ) * ((d x).toNat : ℝ))]
    apply sum_congr rfl
    intro i hi
    rw [scaledCell_eq_endpoints i (mem_range.mp hi) w]
    rfl
  rw [hCoeff, hLinear] at hLin
  change (signedCutWeight w d : ℝ) + 2 * ((1096*w : ℕ) : ℝ)^2 * g24Objective y ≤ _
  unfold g24Objective cellCount
  rw [g24_cut_eq_negative_profile_and_pairs]
  push_cast
  push_cast at hP
  have hw0 : 0 ≤ (w : ℝ) := Nat.cast_nonneg w
  have hwN : (w : ℝ) ≤ 1096 * (w : ℝ) := by linarith only [hw0]
  nlinarith only [hP, hLin, hwN]

/-- Transfer a low-mass G24 box estimate to the exact discrete near-cut target. -/
theorem low_cut_of_box
    (box : ∀ y : ℕ → ℝ, (∀ i < 130, 0 ≤ y i ∧ y i ≤ 1) →
      0 ≤ g24Mass y → g24Mass y ≤ (1/5 : ℝ) → 0 ≤ g24Objective y) :
    OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1.H1 := by
  refine ⟨110680, by norm_num, ?_⟩
  intro w hw d
  dsimp only
  intro hsmall
  let n := 1096*w
  let t := ((Icc 1 n).filter (fun x => d x = true)).card
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 1096) (show 0 < w from hw)
  have hsmallReal : 5 * (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsmall
  have hMass := density_mass w hw d
  have hMassLower : 0 ≤ g24Mass (density w d) := by
    rw [hMass]
    exact div_nonneg (Nat.cast_nonneg _) hn.le
  have hMassUpper : g24Mass (density w d) ≤ (1/5 : ℝ) := by
    rw [hMass]
    exact (div_le_iff₀ hn).2 (by linarith only [hsmallReal])
  have hObj := box (density w d) (fun _ hi => density_bounds w d hw hi) hMassLower hMassUpper
  have hTerm : 0 ≤ 2 * (n : ℝ)^2 * g24Objective (density w d) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hObj
  change (signedCutWeight w d : ℝ) ≤ 110680 * (n : ℝ)
  exact (le_add_of_nonneg_right hTerm).trans (transfer w hw d)

end OMA.Erdos1186G24NearCut

end

section

namespace OMA.Erdos1186Low

open OMA.Erdos1186Region2

private def firstOffset (i j : ℕ) : ℤ :=
  2 * (g24Endpoint j + 1 : ℕ) - g24Endpoint (i+1) - 1

private def lastOffset (i j : ℕ) : ℤ :=
  2 * (g24Endpoint (j+1) : ℤ) - (g24Endpoint i + 1 : ℕ) - 1

def lowPairTag (i j : ℕ) : ℤ :=
  if g24Sign i = g24Sign j then
    if 1 ≤ firstOffset i j ∧ lastOffset i j ≤ 1094 then 1 else 0
  else if lastOffset i j ≤ -2 ∨ 1097 ≤ firstOffset i j then 0 else -1

private theorem area_full (i j : ℕ) (h : 1 ≤ firstOffset i j ∧ lastOffset i j ≤ 1094) :
    g24Area4 i j = 4 * g24Length i * g24Length j := by
  unfold firstOffset lastOffset at h
  simp only [g24Area4, if_pos h]

private theorem area_empty (i j : ℕ) (h : lastOffset i j ≤ -2 ∨ 1097 ≤ firstOffset i j) :
    g24Area4 i j = 0 := by
  by_cases hFull : 1 ≤ firstOffset i j ∧ lastOffset i j ≤ 1094
  · rw [area_full i j hFull]
    have hZero : g24Length i = 0 ∨ g24Length j = 0 := by
      by_contra! hLen
      have hp : g24Endpoint i < g24Endpoint (i+1) := by
        have hpos := hLen.1
        unfold g24Length at hpos
        omega
      have hq : g24Endpoint j < g24Endpoint (j+1) := by
        have hpos := hLen.2
        unfold g24Length at hpos
        omega
      unfold firstOffset lastOffset at hFull h
      omega
    rcases hZero with hz | hz <;> simp [hz]
  · unfold firstOffset lastOffset at h hFull
    simp only [g24Area4, if_neg hFull, if_pos h]

theorem lowPairTag_mul_le (i j : ℕ) (u v : ℝ) :
    (lowPairTag i j : ℝ) * ((g24Length i : ℝ) * (g24Length j : ℝ) / 1096^2 * (u*v)) ≤
      pairObjective i j u v := by
  by_cases hSign : g24Sign i = g24Sign j
  · by_cases hFull : 1 ≤ firstOffset i j ∧ lastOffset i j ≤ 1094
    · have hArea : (g24Area4 i j : ℝ) / (4 * 1096^2) =
          (g24Length i : ℝ) * (g24Length j : ℝ) / 1096^2 := by
        rw [area_full i j hFull]
        push_cast
        ring
      simp only [lowPairTag, pairObjective, if_pos hSign, if_pos hFull, Int.cast_one,
        one_mul, hArea, sub_self, sub_zero]
      exact le_max_right _ _
    · simp only [lowPairTag, pairObjective, if_pos hSign, if_neg hFull, Int.cast_zero, zero_mul]
      exact le_max_left _ _
  · by_cases hEmpty : lastOffset i j ≤ -2 ∨ 1097 ≤ firstOffset i j
    · rw [show pairObjective i j u v =
        max 0 (-((g24Length i : ℝ) * (g24Length j : ℝ) / 1096^2 * (u*v))) by
          simp [pairObjective, hSign, area_empty i j hEmpty]]
      simp only [lowPairTag, if_neg hSign, if_pos hEmpty, Int.cast_zero, zero_mul]
      exact le_max_left _ _
    · simp only [lowPairTag, pairObjective, if_neg hSign, if_neg hEmpty, Int.cast_neg,
        Int.cast_one, neg_one_mul]
      exact le_max_right _ _

end OMA.Erdos1186Low

end

section

/- Pure kernel decoders for the low-slab packed witness. -/

namespace OMA.Erdos1186Low

/-- A signed row, with entries translated by half the base. -/
structure SignedRow where
  length : Nat
  width : Nat
  word : Nat

/-- Sorted stored column entries. A field contains a column byte and an unsigned value. -/
structure SparseRow where
  length : Nat
  width : Nat
  word : Nat

def digit (word width index : Nat) : Nat :=
  (word >>> (width*index)) &&& ((1 <<< width)-1)

def SignedRow.entry (row : SignedRow) (index : Nat) : Int :=
  if index < row.length then
    (digit row.word row.width index : Int) - (1 <<< (row.width-1) : Nat)
  else 0

private def findColumn (row : SparseRow) (column : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      let field := digit row.word (row.width+8) mid
      let found := field &&& 255
      if column = found then field >>> 8
      else if column < found then findColumn row column fuel lo mid
      else findColumn row column fuel (mid+1) hi
    else 0

def SparseRow.entry (row : SparseRow) (column : Nat) : Nat :=
  findColumn row column row.length 0 row.length

/-- Read a symmetric matrix from lower-triangular rows scaled by `scale`. -/
def lowerEntry (scale : Int) (rows : List SignedRow) (i j : Nat) : Int :=
  scale * ((rows[max i j]?.map fun row => row.entry (min i j)).getD 0)

theorem lowerEntry_comm (scale : Int) (rows : List SignedRow) (i j : Nat) :
    lowerEntry scale rows i j = lowerEntry scale rows j i := by
  simp only [lowerEntry, Nat.max_comm i j, Nat.min_comm i j]

end OMA.Erdos1186Low

end

section

/-
Low G24 certificate for 0 ≤ m ≤ 1/5. The mathematics is due to Carlos Toledo.
Certificate data from Chandler Snively, erdos-1186 v1.0.0 (commit
0b0155ead09841892690b9f9c469d1ff0edaff4c), Copyright 2026 Chandler Snively.
Source: https://github.com/dreadpiratechan/erdos-1186/blob/v1.0.0/computation/theorem-c/data/cert_region1.json
Source SHA-256: 74849e6750a25b8ad5e2db3871079841ca146391d9ea4ce23ef24f2c2e0b2cec.
The release's JSON data are licensed under CC BY 4.0,
https://creativecommons.org/licenses/by/4.0/. The Apache-2.0 license above
applies to the adapted Lean code from the release.
Changes: the lower triangle of N is divided exactly by 800, packed in bit fields
and rescaled when read. The entries of C are unchanged. The multiplier data
are reduced and re-encoded as upper-mass weights and one short share and a
direction per unordered pair, from which the linear and quadratic terms are
reconstructed. The Lean proof checks the resulting numerical bounds.
-/

namespace OMA.Erdos1186Low

def lowD : Nat := 396225287841172684800
def lowQ : Nat := 1099511627776

def lowN : List SignedRow := [
  ⟨1, 47, 0x7d81ce557a30⟩,
  ⟨2, 47, 0x32b585b018ec5a736ac7e740⟩,
  ⟨3, 48, 0xf28ed511560899f453fd41bcb37beb96d718⟩,
  ⟨4, 47, 0xc910f2715fd1af1c68905e125edc5aedb1459432e2da9f8⟩,
  ⟨5, 45, 0x1941ddabae14e0c2839820a713d6abd6722cb040dc91d1cab334d72ca⟩,
  ⟨6, 45, 0x3200000000017d64ef303cae0be73d3d4a715750a0cb62cab5fed5309c8db206718a⟩,
  ⟨7, 46, 0x29000000000067f955e3d6c19fff99d04aa52de7beb3480dbb5c0444f4665d2e8d7fc136f495e2732⟩,
  ⟨8, 45, 0xbc24b1451d4580170584dd144bc7af4d80a2a22fc797629d2276abf604a4c9ac76b13b7df39a8302b026ec2d6e⟩,
  ⟨9, 45, 0x190000000000b004f8ec6a057f000ae4d5140000000000a026b7846fa37cb296b9521324b42949014945584b2784257aabc096⟩,
  ⟨10, 45, 0x3200000000009f3bc4962444ffcb8f5bda280000000002bce80acced95f38ffd248ecbe30ca096071335c7bcd22c90acaab1c1c8f3ecdbdfa⟩,
  ⟨11, 45, 0x65492d892cf2f3e084292e4a0009a32a9e5000b15a8e528330e45ae8abe7ce08105d5d92d68baf4c9fd51cb53c7143aad29b32c66d34ab911c8f2fe5714a⟩,
  ⟨12, 48, 0xd31498c1818c9658d80ff5ec958c7d344c726e1761b7e6826f048102cd9a6f72363698a29056a92184aa8ff8a1f727e892c87bc6a81ca53c82f7eb2c93274688d7aca5f7b86b7522⟩,
  ⟨13, 47, 0x6541984f09a8c9e30fc58a7d3105f8f84f2a622e654e13934e9487c70566b41fa9bf7ccdced85cd67aa45650f36463490823e20bce9967492b61d1515276b60952532bd8ada8a557052dc2508⟩,
  ⟨14, 48, 0xfb11a9061fb0b8b23a769af0c9597ac426b2985590df3cbe9809fe1616aa6e0d5f7ad59a6dac01f24f266f8df69c801e8c55943518868c5812a81c6a9911443b386cb29d503f91d894a8a229a064ac454c2ac018⟩,
  ⟨15, 46, 0x2af4bf9ddbc4e169c49620cac41a5be5f82c71dd7a18a126005f54073097f5f28e8eb9a90ac3f2a626a0d678b4229a38281b7ba28eb16fefbdfa321ec6d97209861e634a192c4fa3de2ae897d67df0ab42bf54bd3a0c6⟩,
  ⟨16, 46, 0xa9eb359a44128568ee3fe84e497be7919eac8dae580ef6c85e3f85f8525fdbf3bf95c97fff8508c599fe1a413bb6680897153169a000ee654928c90e51e78ca33272acd9209c59d1f4bf72dbe549500689798d03c7092caca0d25026⟩,
  ⟨17, 46, 0x2a8000000000a01a474b6c4a718755a2042e1877983123ac3e9640940ec3d692b5758a52fb66f9882954710d46611a00000000006bd989ff5d61c518bfc2c348c00000000023033fed9852984fdde450d2c559d2ee2a4969bd3c86032c7fa0623122⟩,
  ⟨18, 46, 0xaa00000000018afc13a35b467fe376514d99f716bd625a20fb4696e35943fd8ed41be3b3f105cd9f9a5a6259a77e6800000000024a56137912c8d4b32da49323000000000073f084750371cfa95bfb312684e52c72b31449fe6e84e868ed4dddddc145552651b26⟩,
  ⟨19, 46, 0x2ae6e4e6daa4a2c729cdf0b99ba51dddcee686958a09161a1b70a7891021b2b6bc598953ec8d365a63a5a2929a891a000e3d714c68723f54caca30f461211f68cd08e61e71a309176d4c92741055039359d0009962f4c68615de4299144f6b6abdc868ba0d5d3b9148f27da5a86⟩,
  ⟨20, 46, 0xabd57b5a02928d70e9762b49f95978dcab99f837aad5aa6805f7a01e819ff392572182111857d8d794420b70bac63a2d164706a1a04c012b078696e33bb65aa30ffa8b3f168d5d01d2251a38911c56d0e73faf00e2939d001e96b9586861ee635dd144fc018bbd069560af9b81148f6f6aaf02⟩,
  ⟨21, 47, 0x65b623ddf9b0a116405619954159ec11f2fa77b9081d5fb3390cb6f9ede6633a3e9cfbccd446b449a08871d5326746289cbd45eb5039380aacec44d1d708598cd9a4e2703c6694788fc6332568f8d45a996ed1ea157eee3b9ccde594616939b5c8cdf82268940d3dded8a346085bfb31a6209fe7d4829507be25b10⟩,
  ⟨22, 49, 0x3230d5207f691354e221bf7808c47ca17b5f346370364cbeda311ab7cf23ace892a1f7665e743844d88ff33a2749bec3e394856a77e1410d224130aec185ffee67ceaf73b22c9da0a629df0c8def14450fb0ca6a089687e556932015435f353bee729e89aa102b98cf45b150cbbd674bf6e4313ae34de216136351d4e5e7c061a8d47724800010⟩,
  ⟨23, 47, 0x196c00411a7a3bf02b207fb6591ba12ba28c98b42cdaabb131692ccd9ec262c9679c51c34892bf8223c69502785bd98d3951d4adb60b8087c0137e2941e2ae3dd048342f710678e03a6b7299b1b96a5975f9e475174f22adc8ec38025d829197752adaa71d25b83601003a426aebfa9069c88c74cb78a817c3f948e1aaf2377d0362a7be4c1d704⟩,
  ⟨24, 49, 0xcb29406d19a04c8ff660e9142c7c45d700d3930fc263ac1b08c33debae9404627e6accba0230bd0020c058ea834b7ff13c7592a68f08dc3afcbaa6603514620f3d2b530d1d00b4b557c5d19a9ce40ea3b7c7eb04b591d9b240e9dfd10e29de36fa288663857762524320dc7f37a31e8b210c4f4c8f462e19cb668749491ac876c34b222cd81b41d435f56e66c8d3c36cb4f588⟩,
  ⟨25, 47, 0x5502131c46e2cd382b5c18454a7b8c1d376b2befd52f88fd16a2b2501b792009709f8af241b26c7ca764793d6e273d378acc90b9e27014ef4fa57adce87a878d9ceb1f52dfcefae982cf6026f614ca613c00ae8a29f6efd55ceb3814983944801222fa5e896726ef42d11256dacb05b9e16e996511d3bf20614e68f6e4980ee1ab4b9de2b35dbb1bc0255f02f32ed73686a7c3⟩,
  ⟨26, 45, 0x2553eb8d8f694c3833fffc9e39ad3890fb58b3fa69220b88ae96994d35cfed91788195ff2616b11cbe6a014ceb655a65cea380d45d2942168692290b5aa2b617853b4a9ce6c1f066452b8e80f698b15405b19d46eb9696f35aae5c70b4ba38e918004f08eb88c4286234fd460773432b81dec038e20d0ebc3a6027a76d87c93fecb2d07abd75891ab586d9cfbcaacc89b9049⟩,
  ⟨27, 45, 0x4923d8468a7a2e077d1fd5b44b41a669bcde7c1dca20b56f6aea54e9b6efa8622cc3580218b5c7d95a377526d2cb82ef6c727e58549f3a9dcd3f005467aa6d5c97b144fb74191541c74ff8886922b2bdf22a9a1d5521b66c5cabb8effb1d1acdc6efcf6f73517e42eb780a8ca4c1ebf80450a77df7bd9cfd2a2f196ce8b3a8b8d9568b71ead9eb2b87ff0c6721a8b53ba53f4a5dd7ace199⟩,
  ⟨28, 46, 0xa400000000022fdbe2301268ca208143c82a24aff2d796e2354fb59a82c53e4647b78e26a94c9a6babe15ab900c29781ec21f72a5d400ff6e2a972803268f21a00000000006c732748d499ad173cad0a63a694d41f649826e5a8d9a65220996b3dc9c87fa0428167148bafb3612300000000008c60943b02a22fc6e55307c740000000001d070c8afbea6851d2a1784145dc39611c4694d18ea714148e93fd168a⟩,
  ⟨29, 46, 0x29000000000065cbd00ed5d1d00b53f033e73ca9e7897c16ffef048dbe216c5888dda14537c00a6f827db517a793951451b0745669f31bfc68a9a421d4ecf76680000000002561dc9720f8946740e9313a532874d2df6b15d945b3a0a6408877a1aea4605894f20a2f886b4c20a8c0000000001cff5369b360748f273d4e61d00000000008a20b72fb0b225c6b516e4698455fbad482c40eda94ff098c3c14289c2c6d28c39da2⟩,
  ⟨30, 46, 0xa5592661a0e277677efd1a0672d62b2c371cfc8a27fd4e73a539570941700372842be22370c08dd214a7979a5a142972b2abc789520bc8662d269ffddfda0e9a005a9352326a7373f6e9625352d26d0c894d2c4a3eb8a520ac6df71ab160f40373da641cae733aea613a4219d1a3003f2d20e28bffa5339f41d07ad016c5073ebd015c711cfea2434c248ac59fa442d22a9917b3b8a98617b2f4e92c4d6e8431f498f103528292c7ad646fa76⟩,
  ⟨31, 45, 0x4ac0a13b9dda606e9d3b2d5311086fc5ea67f3a07e2c13a7ee8549b49d001ae900f2bb1c37776802736a86a6eb29c46706ceb8ccc7f06df5aa91805449716ac96f71b34b3fb93e69ccda4ec2d9c5f528b44807eda9280e2a705fc894110dbfc6f3de638dac33dbf758dc09a9caa64f7c1c61a9c852cde3b57b5fe76ce808f19d96e73f5a25c6003a00366d831a2da40060cad17ecf059f3998626c4bf61589fa47a9bf25a64c418b155b77f68723d⟩,
  ⟨32, 47, 0xcca28028b81119a49d1818d677868b88b014f23afe9755e63a97d6696bce7a9ab5e64f5cd5f159d826ad9ad51a6a03219ce9566970a2e03407fde08b7010da2e82851e579202c6a7870390234d0b7500a6a39a47e6318a4f4a6eb668958a939fb7e6c86527f3c02a802ac5c41ae97464c88ae7ed16ca57953a3e74d17f8caae656a30f03ef546d3a4e8152045e744343e1a594e78dc174cb6a2e28ea9e3c5456fb3f93722986962df80a1629a5d58bb126575c96e848584065955fec⟩,
  ⟨33, 49, 0x19893b21e8d189bde70a9e20c431d5c0224a2239ae039612311c5297b61f9c7389becca46e3d057495eb291e681b9afced8dc98972f0e8051a59e799cf8348e5742e38d147cd0bbd8af8d3f0a462c6c87569d19314343a26ff915f2b1d3a2066b7139132b25adcf1089dba75d2db243f9450a9edb266292f283e8119d23d1cc67892d1572945f2430fb455df8e218fde67e5a00f4622ce4ff8c7a2a74230a163d1093fa5b3c21415458cdaf10b5db3afa9608c95be9281764cb4584014e9233e32d1502b133d0dbeb0b14⟩,
  ⟨34, 47, 0x3ca3e7ec2bac7bf621fbad00b15c0dcb25f9183235f00f166344e7c15014c598025d38a65e857548174e8fd032e9b45d3c0f8cb018ae80101d57a32435189577e0a577edd6bd409397476dc1c2bfda64efbe06a560294caacd1861ade33e9a2e562eb9094a6e66747cf68d6a88d8beed195713858efaf2474d839a04d2cd919d60ca64f6184ab75191d8d8868da32e2ec2d5833a4db20fa20674f7a0a89b74f3c49434479a2ba5ba2b9bb45e980810b8299b507e06e216034d81a5e8259de4f2c94059b838f67ec8⟩,
  ⟨35, 49, 0x73373a94e6be264f7502f876163edf8fa74f4989697ffc18e42e9452a9e5c63140773ce325189cd4bae9627491b33123e13d3af6d805655eb01762f22e2dfa8c99e96a3552f423bc55234a31e87d86514ad78d609c90d706b2a876b4767e59fc924b3adb3576fcbb9d9999de9a5250d384574aafe868c78055e974333ab46ceeba6c389358b8c91a2aca7c4f58945a1adbfab5431b2610bd3aa197a6bdd36d4f4d8ad6b939e7a4959aa82513d21e1797c4aa195ce7dcaeed0c9cc2c4b9468cc31c0aa3b44ce1b4eadf4a234f4a42f91513484e746c13c⟩,
  ⟨36, 48, 0xc27303833378b637b62b9890998bea96b968b28f08a549bc98e611a1345c859ea3f5b3a88c5559037d7c8b9018d2dac874abc045837c7aab6d7eb4b07ab90be5e4646fde08769ba8551843d156d46995ae80bf805303233d3e406a757e077650758237a0620075ff0680312c7802eff46f1886b33819c40c869c90b205848675a421c73c9af2f5d8a4948d64da54473c937a492d4424866319c40dfc8669731374ec7aa1cb9756f87a24220b5e6879ef407b4684866ef85abcf0866cda68ad0c8d112464e1f89a61f27002048d8ca1e7bad09ac64b8d23e0⟩,
  ⟨37, 49, 0x1b0fdd52914989dc6b012594859b56006a117264e8f759a51163d6c7c8682498934ab8318042ab2e22b59ea2ec23de428e9171880e194f474ef20e7cbae3d468f35e3039ea6ef3988c7ce11c521ba93a527f8ceb072634a18c94e34d148f5754ae220d73aee5d66fc74a2ab5bfeb43baeec34d8591dff6394bb3b90e6b431fb36486d036f587c6432ad8fdeb0d2673ce71b52711a243e92a1a09450100d6450430228eea14e217422a2613e8f489906d891c7a4383023ebc3d24cd2226322190adf335f710c8f3ef2813c8cbfceff38184cde808a6670234e76f0391e93479210a41d0⟩,
  ⟨38, 47, 0x375d31c7686c7480c5e57fbcbd35381d1251cd14f689e7d2cc592270efc728cf1f73c9cb1c56ac811a11680a4848946615795dbaa14b368d86e7fe6ad7b63ca02cea0af4cfa905d48030f13bab0b6ec62e17f25df48adf6a0a6537f7a09a09702ab169f4294b724bbc0c702f98b60274d8e24b3a6d29b71687b25a54679adf070da8d0405bcd80d19d314b9cb5ad3973e2979e4d6401d77f3ca6f2c51760ad19c27c80dc9a3389d83bbab3a6ef47e758a74cf91608084e9c4bd4aa1da33599b80987467094c5a2fe9a236c72bfa969833fdc57626c5e1d44cfa5add26d97604⟩,
  ⟨39, 49, 0x6a9d477622762835e9b3012117972c89dffc89b22e40c25ac58d9fcbf7b93263c4f06561b162b1f9e02714984b5e7991f642bcf6e12d41e304d219deff517ffc3f49a3e74636e1c22b33d345a19c34fde94979d6e04edcaa9a8d3a595154abbe803e347d7f2a0801146b14a0ad170e2d12a51c07c788aeeb18b873c52d9ecd72f9df9eb4952e650d8791e9fcda862efbb4d67d43122566381fa64faf16fb41919945b0589ec92925214113542ec0ae1d0bba1878b030007cf446594c9f3e7a215a4a898f3d12066f1783a188b9348d9c50c47a24f8d2a8c77e78130a64c969933e4a8233c7d12dd219335983e057d8⟩,
  ⟨40, 47, 0x95b8cb5342298fd9daaca48a75d12b335255c1537b351b09747b36087496001f5b03b6a6223baf993557f11e179c7c977c12643b250a6c0ea6dc4e2c1c59a2a0f45485f8e6f467582d730596cf5e02de296edea63c0fad42b7ce28543add5330eff7a260d5150cdba0914ee8f9c9723396c81e0781a7a005ec079b8f3ba17eb44e1e6d5adccfff430e848d8b42860f0badb0490c05aa0356f262c3ccdee5f46419b9c89a2922810afc7c90b5e6b4bdf9215da67237f93d00a9b5edb279efe923e62cf3fe34c17aea1800c639f51430062d192608c30f103f201313e87486e123280e67b7444c8f6a23347e⟩,
  ⟨41, 47, 0x4a7ceca7b85090d4ff2a65358a7eca41052a75e426d738f5c9bd257c03c990cceff10f9632d3cd25ada6348be9a2cb586e6dff2328980627277d7d0b65e15c7cb22c26ec6eb5645c185e51aa473fe8c8603e8f54bc3725ff1e896891832537ce0033c514525e2d316bc0d3f11b4c85614e0d428f2b338252eadb9aa7962a0b720ecf33c87bd2b19e29e7597fb4433bead4ef548604548176ad0c38de05a0ea64dfa86eb1b4641fc23693292277ceecfad0ad9efd0f6ea180135c5eda3d005592d8cc7a028f7e9aa0f402880dd0d21806d3ed6d443016460fb568c6772f6dc41315f665b704232ef01f31304c9a35c7d4a2⟩,
  ⟨42, 47, 0x2540000000004946bfb28e4090c76b08ca8d8a6d450ea42a78e876a99455c45986fecf498babf241b8961c5426c1ffa6191f28c09358406d9ade9c97ce4f5232050b5b630733ca2bfa86c63bc45bb1a8364ac740000000000f5b524901859e8e9e403d9c37b2f4f67b9a543f2cc3af98d31a7c7867b1522ab6ab29537e84cf9ea16794c7547a36cf2a2cf3a3659e2a5f546c84430000000000860c39f34d7d0c8e719c2bfa63d6fb2202946289e262d0a923f317b74550b6eed70809a180000000003d00000000007a3296f253d8f3866f1e62c2180000000004306541d82728c17237706d931e01f6809f2328d236b6fc4c929079c5ca⟩,
  ⟨43, 46, 0x2a800000000062a70c66c8e18bfda382b88646534a4ebe833d7cad066a4e71f2228a48894f41c649851f0f29c81608a3822110de51b5b178c538875899788ec52d0c3877ba9cfdeddb04266849d05c6501a000000000094c90bd22bd227f29004ba68a0c2bbbf2127a2edf370fad8907faf20a28e0ccd79708b7cda9cf955a67db1bc05f68c977c227b7a325c8b3d8ee8c0000000001c98b9ed3c487364ad67fe89cf9933df396512f03ecc749a09cbd1e7c25c38ef29c6a9d13bf26f41e7400000000022fc1a1b4ae48ce759f8cce230000000000730ad80be621cd6c609ed8a67046de737d1413fa2bf510679f6ff1072149207658fe6⟩,
  ⟨44, 46, 0xa9f34a1d3f92926f4125b2661ed9e27f4e988efee83676631b89ac03502cb6381426a4e26bc1238c885ef2a5315c5075e9f8c14088cc04bcd125157062b9da886d9ff6d91c50eb8f5faa69cfc330d76f56862322ff049a2893e1052a9496b2e5edfa2690735b24589e20d1a1afe7ee8075be13d97cdcb5e0527fa1ae36f84b7bfa78fe79a61c5238e5be8c05308881c230cfc2ee09c8c608cb39849ce2392ff8b673f37551d301d001571c664515970fff279a4199ef535a5c54e2980031d0188d8f21473f4cdcd5eaa2fed562e3fa8bf5850c5d2a2febce6567a737b4d158cd9cea4279d464686146f48fd14500409ce1c695740473cb14a2510964f2⟩,
  ⟨45, 46, 0x2aecfc44334ca18ffc6247f28737b13fa2e64433922fb4992b3254a6426583c378cc1036e988740065128e28183b8881627bf3704f75745e6f708747ad70be25100764a5e88861aa0fe28052d8ff6494c9d2bd14ae75b680fbfc36d19a51b3c975fa93e2b0881bea263ec895d4b8972846873567d7811646b5cfb9e6c352626de7b4b8034b53362c07cea6418616be968c40c752e192377e34b9b608d3316f2b709c981ca955aa7394a5502981d001f0e951051610bcb63d9a681468ce5e5c51e3c8d401d0614369f9473ffc054baba3036b65e0668c23c397676a30dc69a2da6739e5f5fe4e9cfb6deaaa206782c4bacad144fe684fd3869ea9cf4ca6149024f23b1a⟩,
  ⟨46, 47, 0x37da3642b05451bbf3933e6aa3af21b4953546487c3abb39947add6d1693240e9fddd4a6592dd90ee7c2863b76226e14682af904f011206d86fc6c51c2945eecb0449c20663151455760ea77e10cc4aaa0da050a7b8328cc8e895f3c8ab75a0c233c3031348a5aeda1e29467bb46387513c64ce119862838633d6b4cf40ced31343e10d3ab5981932d2bbed13b2c8fd4c294fe4c9dc57e46388c645f415675188fabbbfe8a313b6592b93389cc465cf2670533a0c3154e4012831c4491aad888a17c32f66bd5e5b05c519ed9f12ce841a305b669cffd8e006ad46474e6b120e8c8e4d6a88f51be1a62e4979d03eb4722533a02bfc4dcde686291c54a08a285d84fc831a55f86976b029209be0d478⟩,
  ⟨47, 49, 0x6af57111dc2028acf67fce0311eb2698af2fc8f1f48d16f8a476cfca34abc1cf9edc0d03a8e7a0203b8ea07439950c84e227fad6772bd41a54fbe9f4940a40836ab5d3c6954ce23179e290557df65e11a4736f0d76b0a36e049cb1606890b73b31ba3d37f3e848431d406980f0a68eba2db4d277c88f5b34b8a0042273357c25621073112d1701174823819ee499ab5615f906469342f1bcfc2680d571bae911918ab6624bc86acaff1696c4344d32d774021b67fee05e90efbdd6387b2c785f9506b1be3cb2a2fcbcb51a656df624810e9eb9e3ac9b86eda08b6ffd23d1cc8b364ed1e8e1a227d2f10d84780c153886f1cc25b21e4316cf04d1bf1e8d503620700f46a927905b474a368fa0eba34c21ba87fdb1d4761a457190d4078b5cc7fc⟩,
  ⟨48, 48, 0xb8e84e4e02a0c7c241563afc9f7426e6efd88e75a6603ed08d868a3019d48d5224ba5a4c73d3dd57463c73d8030d34ec742e4f790d9850216aa490a869c171774cc852fcec08e1c069d1390c3e705303803b0224699966e654e452b4196a74906ac9c2bc3b587ab44700a5c475a01b3ac79875f28adfa49c8871bba052808434b71b1c1884767bbe9c848d45001a20ac9aa4342142408da2f4b9dd609afc32afce088d08b71b09008678058ebbf886858eed5aa0867516142e2079326645bd74782be0d77f14794a490fee486a8e8c3445cc757226f1446c6f8ed243bfc47a77b26f46447a7656e697d8865e504bff308677e275205886801db8fa3c7a7913de39ac7a77a2a16494751fd3677cdc6a7e7ac728f07599f6f9d8086aff400eacd8⟩,
  ⟨49, 49, 0x1e90180787660a0095749d0ec60aa895012eb2730279fe16c91b6ee48a09648cf0630bb884465ba8c850d91ce7f7fca3260e7d14cf4ab307447a3c8b60e28d63f44d46d1a5c037906450a478f07aa2cc6970ebd79e682921800162e41a4e5dcc298c8ab87c7816f3c6d6e522e95463d8cdeb2ece81d9fde1f91178ed78da62494488ee57a6a3c441f21de6ea2c20f316d3eaac112d703734f6899e3e3ca097246a150af9d30268eedf36a3b919512c86037c864887be2210432995f1380821917dc38a7d0f286bb613e8c79bbf95a86e23d23e15b00a51a7389ccfd668ea239ed031646effb391ce6a3d2501dff26d1e9265753ac790c3cad3ebdf8861fdefbf7d44316874479cb1e8c66ed9d638f48f7ccfc06c74bf86cf3b9634de9fdb6bd61d4e64ee89620d478028bada8⟩,
  ⟨50, 48, 0xd62a8ce33c78c3703e2ac9c8a333b5781ff8c24de788f1749cf32326085c8d04d63a9a348cab09fd8f9c8c99945f10ec74515d177f9c7483a8141664748955f673ec5242ba72d01869f3602a566c534309aa357069f43e2b9af053499d1be13469be58ef3f4059b6bddbbff86bead70bbb287b09ab3d4312767e3dfde0cc76a56a7ff5188901be3f152883d9038ef682836db3008976893a4147dbca9aea3d72d9448dc5f2ef527c9b4235064eac8d2bb06d880c86941b8834fc868931d714088687e508b70078b3041585647a17b8e7840c7a3fb8cad8f46ad497c05b1875951e962cdc6fc2be5ecc887a8930a576547a8c45f6d67886408995378485f7e491fc2085d47082a2487a732d03b4e07a894bc62b0c7542d8edf3446ac326b5067c75bce63e3f386b42a4fd3e1c⟩,
  ⟨51, 49, 0x738b0f6216e626b86b5c851516f54b09f439c99ff97b14d5c5b1403a4d52627525ce941449196c849da4928c76df02cd7946465bd53a709d24a728a5414e939552e6492746b9d10033528f70c347d861a6436b671748a4fd35fe08dc6991b8e559ba2a94fec086b91a56a383592f0b42648706d306faebab84e943db62df472565dad71bbf595cedfddaadf9aa86983612140b41beed4297d460d526fd9f973130836e8fa379a2529cdf87646b1b64e808f269f49a625bd11c3a17042fb086584d98c6d34320a2f7aa86a195369504c3cf4dc6db3bc727a37063b53133d2c059c32919ab521ae39fe0ea6533717ae86f84b4c1cde73d2a01d89dc59e95ef3fec9a50c4b21d9ee228612d711a75d42fb462b34ed9e93aff20365cf4afc3d1f7f274e053e58e6634ff05a525a51d56983266300d4fb354f70e0⟩,
  ⟨52, 48, 0xd621f442f408c42e8ae85bf49a3d29d2490cb8da6dd3f9c09a345390c10cb88d0c0c2fbc9d0603b9887c8c955e3a9e128c9550ab4b028c8706cf91c27494352fd0de74969ed65e8674956e295c6a52e3a66e22c46a0ba252eaac53737cb7c3286a0c80655e2c537a118b6a0069d4743a0288562bc7fbe2d06e88c076e4ac7b54b745a27d75fc5eb5c9f675a7a29e43368698ef0e1ea2839993536c558368982a3b1589e03149c54b9b1ab7faa5d88dde3465314c9b72b6a81fcc8e985f5b28b88695712f0be286954d42cbc686871f453faa7a9457e3b3ca7a67a61fa27e7a956fcbc2de6b051b7dbc5475ad60d35fe46fe711d3d1ae7a9551a6d9927a9505c07d1e85acea21257a85ea5acb4c52854cfd996c927a86015a45d27a93ef8f666e755b1b2446b46af3b85e451475d5286db3106b73287cc300⟩,
  ⟨53, 49, 0x1e84bd5263f189dec67739a5c5c8b86713759266b65f818511658a680d004c9a284282a9b859a25520425926268e74b4641189972c322208c566aa6115a45fc2606b7cb1d2888536ae08e903995e049074c46b89993428e08a5a0ac61a5e963a3f190aa990550d1f8697b36f800182a99d79c77931a51160685610b65827a4aff46f42805e20e43d94d0964cc49d98f147b1b68f0457bf862c086cd28b68bee41cb35089921a0ddd050524bd130382cde14299f82612335e46a675f87e3f269872441f8091b57958fa400864ce781e3c0432b3693b852217b68020a498f4a558040dc07a3fcc78cbbe3d26655eb8811aa17f718cce0ea383103121c71b040ed3de63d7eb8f83cff1e93d8642a6b90c9237f1af1085ac8704d52042eea3049d3c1e91676d04a00f4b379e368b074c9d21c4aa234e883c4af401d50f7c1cd250d4a12e04940c⟩,
  ⟨54, 48, 0xdbcbe96b05d8b61b05b14b1c9a2d8418505cb36577ac3ec89a1579eacd14b324185d8e7499f23accde14b2eba16745f098f167fbd6b88b45f1ee6d948adb574fed4c8aa0d611fafc749a9dbc0494749aacdc4ee47481abf6cd4452949e532bd069e41dd5bdcc54e337a0f33469e4fc52bb0053307830efe869bc49a6df0c5d48094452b06c2a31d3c6307c25a9a15f28792f7df09e1c79bdc1fa665c869a0178c0f4835f8f6622948333d94e74e489c2935405d49b361c8336a88db6b4dc29789b24de0e38988f6318f2ab588682613d13a485a49773975c85c29d0f1d987a9829d9d0f07af9b7bc7af87a8907cca4946bf8f90d471c7585dd0c5840701edb64f6007a2e40f1e8d47a835e07aa6c85cc6d99acec859cc8122474851d26dbdd947a8584c9fd047a810dc843a4753397565f786aa49151b25475ada4b0fad06b2420f59350⟩,
  ⟨55, 49, 0x7be42b22b3f0280c8e59986c9659d0867529899ac071cee70593175f66ba426650f599ef0164417e89241c99709b18718a58f430f1773e262097d3f8979167da568ad688ab3375f31ec455138d9f27d1d2f25781fe60ea297c071b3075c012fbef762b51522213931a85b4126d1f0b352461440cc6a8b874fcb9c2a9fad49fbb31a4c8d3be8320ad447d4938947485730871363e18ef7976ec9e4e6aa9e0460f1f1c77261a886af07b759c841b6508205fea0ded30e1a21514036844fbd699e0bbea94be469a8b046bd0269d9526d29591a236b5472cc864c3b7a1d0242f8f953ac08218ca2846d7b8f4a7e46ceae87a38405145063da06d1b2a8b1a6db24e20488ea0884bdef486eef17733ce83cea10816f931e880d89559490c3f4bd2b96485ef8ec6b32c429f28a420a41e9c2e906a540f47a8c40639474b1f746e05034d0a911a2e61d4b01119a428d441c33bd270⟩,
  ⟨56, 48, 0xd4d2cd0324c8b5177b57119c99f4c8164570b31604d8fe689a1c4bc1ceb4b34307de9e449a0414e00fd4b30171743fc499e1041d1370b2c9325d89d898ee38bfd6a88c1e34f0894e8bc7874adb6a8c6811a6665e748cf00a7c4a747f6dbe82267619da5ee55656168ac218246bfed3c1d3f45666f7b8df2469d3cba6955c530b707fdc88699bdfe6df2c52f064bf106073e01c832e107bafdf2d0b5577422fa626be77932c20f3c286a0a2ecad9a83b252ca255983826d7708398a9d11b774579aab2e3459c08da581f5858c9b015550a2e08d0b367f7298867917c718da8605717df6f686711f81d76a7a8f93dd2a927a6545fe2ed67a964f6a56326a9452703f287574aa6de0106f91f9a94d5e7a4165d9eec67a5ffb0558928661539abac285ea127e8d228597a176face7a79903e11d67a78e9d66fba75225fe990006a82224ed5d4759c6d58ca206b01b1a03bb0⟩,
  ⟨57, 49, 0x1ed18d9dc6e389996a082920a59266ff829982669e3a2b9ff964f725fce1a899cf139a243c597fef833fcc266db7515342164ce24bc6c709993c9f8c70859175f76ba1e262c171a203591892fad6ec8a8bfe9ae106fd4621376dd0a09d6610e9ff8aceb4962687432761e57eab0ef2c34c4664a071ab3304e14920a9782d71997c69868b33086c2937aa71f07b1a53a1f81dbb0a4271d3d82d07305dc0601cc3de3ddfba99bddfe5d856f00cf1d75eceb5ba866288cd497941c747205ea7e0d41b64e1b8f13e32f64554d9a0eff84ced246ac1fd902042699b35003579197bf9eb9a188652789f662f42f864f4c499a162b40a0227cf4bcec57828e7a5ea5291e513d7302e92b619a7e4c7aad1c0ea4ed805f8b46f1e227a964d3d036f889c6f9e7e443f3e5450cb0b101661285b516bf781b42a6cd1cb9579eb152082e7b4f53b2b6d0e3274d526144eec34f3d78926961d53ccbccc650d4ce7d01d29c⟩,
  ⟨58, 48, 0xc3f1db0d6f00bad8dfc935e099e8d1818414b2f0d1b6c93099fa08c885c8b32086c3872c9a218c853e08b34d8a529ee89a094a7b97f4b30bf0485740999883a91fecb2d13d15012498f3f19c0cd48ae09b6b3d5e8bb17d940c2e8ac77365e4227593d801e11674f2c45847667533bd621cb6542cf4c39ca469da2e437f6c530ceca52e5469d90002806053131ade15a869a0f58b9af069d455db5a146f18bfc5c0f47bf1d6e5ddd578035683db22779be1c9c89e86d2a3b125828369e1a6a625835c03435de189cb78ff73879ab3c36c51688da94172ea5c9b0b885c85008d10789a8d9c85db77b783ba84d03f48540a853bdbc74d927a7fdbaf20ce7a7fdac49ab27a7bb701abf26a9e26de38e87570b5a386fc6f99da992f827a7b950cbc567a778edf86d2861cad03a51285fcbfa743da85f7635c461e7a74c0ae999a7a854f27ae527522ed28417c6a8ca42f0f3475a1ade53cb46b0c00d9c374⟩,
  ⟨59, 49, 0x737ec4be11ec281bf3c37e851689896fec888998cc6b5afbe591c5e70a68526677f965efd964d0e50df3f899c5823f71c6594abb223b7d266b50d37d38164a7b89a2c68998a3ac763de590dd0410b352626ffa512bf917e8fdf4d1388ac4fa3950404577e112dee91d3f1e864c480e9c416efb134759010306c4628e270d9ada61a5f075cde448a4a8d7a5a83c697cfbabba56292d8350c43c1d511675fdc88d19434da2de872d9aded45263e0af59c2dab9e0ed43416c08f11fbd627734867d4baabb1c41b00e624a46a0cef166f207d12e91de6d45299fbaf6878de46a7141f074b2694ea18564991968c90feb448620b14e82c642837c5b3174214bdc9e55388f4d78a7eec207a43390fd6403d26d662d77a1a7984d360640ea3bb98b23cc6f0fcb8ab3ca3d1c26f150211e909a61b99890c356344ecc086283af9ceb042efd8aa2d091e989f40e0138f4fc13a09c3474cb96bed5e434ea484c98151d5168ded6a50d4a83fe2eb3c⟩,
  ⟨60, 48, 0xc081c3f41588b34c0d459cac9c0360f0ea80b34d853f720099f358a2d8d0b305dfc275e89a048ff429e8b33595a0d7809a2c13cfd054b362993a3ea09a13d1997ce4b320ff4495c099288639be88b2e8c2f8b5949902903948548a300b6cd3ec8af734c72c488b30e21f9ddc74c488a063c0749f6aaa9edc74bd059817cc52935e9478ec69e2aea02d8453218e950ed069e38d80d4d4532829733a4075ab66dc49c063d263a7a77c706b8622f4d07c2dfaaf7fd0789f44bc01fc7923436fe21886b6d84963188379b2deba648340762954bc89c17f59ca409ac8d2f8e7608bdf4cad24909b20cb760ef88cd06b5a34b084dd27ea921c8470f78a3dd4845eb5f8dfd87ab97af482d87a6a1a9795847a81cbc7f8d06ab3362982bc753ee02b1d646fa9a5def5e07a80d87b08bc7a712933c21885d3896bcb6c860c47c9f1f085dcc9ff1d107a8de1dc7ebc7a949cc931a07532284d7c8c6aa1b3133f2075ac35635bf46b2142dcede0⟩,
  ⟨61, 49, 0x1971c6f2a7a209fda06e11c145f7de28ff9c62726b6e7e53c1697b2b77492c9a997d1bad8a58f76c69eadd265e4308a8c99643d1d18d31c99a09020a78a5925c91e13ae265d16be0b06963d10fc7375c98a40fabe4be58e8de24d4d2261dc2f1fcc1116c00c162aee8aecaba196f74588b5a7f90d9d6ad18d1d274eb3729959ca6762784f34b4f28c6052dfd481a63d44f79a40b1ecc9e1b9006a14992b0d962a69e017a33b1c7e6eb7861c8c778adf4e5d472b61d8842c63e07354c790fde123eaff449cf1055d5e638a86e6f8c161c341b345ca58a6e0cb3d20b4b8712b9ac1f210599b1cfc5aeba4694620bf0d9268272c2fd0b1191effb2a024863b39aae9bd429885d37177a166521096f0cf4954b38441e7a389f8185033d1dc98675a59a670bc621258e9f1d4fb14346ed86624e0f13d1d900802df9e8ac34e1a6550c78aecaec4e86173986e2494312e555a3f79e8f2281c0044f480a93794fa74a6a74513a434c555d99ad31d491b02a0d40d89e599ab234⟩,
  ⟨62, 47, 0x367ff98c99ec7245fc15e2b4b333a2734c89cb988e8af732cd302d9bd3872799cf850ecb31411143c61c9b1d4bdc4f2ccda02f03c872fea0e4bb30b38588e15579ca3fe4ff1882cd5412e5aa27156e67a2dc8a90a50eedf21a216a3174d92adda2e5b9a24973805e60aa928d99ccd9bd25c05f8499a9ae332633a5535709037217e6b4134a2fb64473461610351660b0db857619db2872c7a058248cf13a18a9564410be61815de1e5540216da015bad46447928a6438f36365409005ca01485534f391c9b89f69e8d60d3432afd0c5db60570c61a64e5b81a6c973004e2687b3ec636fe459352fc206abc2d27194236044a910bf4c73c8a3ea70a585d114f08eb79fa26b2ae6ce8b3a50f67fffba747ca6631a8ce932a7a4db094f04ae3f82a351b1f011a405e175a48bd8ce930c7127cd9d247837eba3463bdd425ca28be5f1df3e5d190aa90a17d9d22cea32b013a4cb03cf4ce6991b16eb468a73c4bd9a2a1aa1762ee3242a77728344c4⟩,
  ⟨63, 48, 0xded79a00bc6caf5121ff52d2cc07a4c15c9ea5b84ee827e4cfcdc2b77a0ca6b47aba0cc2ca3c5dbfbe22a56ac5a9fe02c98451eb1570a584995864fcc9ddc610ced8a4b574d17fd2ca0f67e60ddea55f5e50e058c684004dbc7ca31eef1af8acc371c79931d0a35bf66e0d4e8e94b9df63308ee707c4bf308ef5d6f7c2466fed6c147e36703edaedc0366e28ece19e9438e4befca38e5f5a405bc40646e8a2f9f87c6f4521ff977c5db7c9a4a8ea698f2f0496a25542ee76b6606a5f792908d27a83f2eada6f753648b0025e7602caf5e11a898e4ec76f9a84e4bd3bbea784e5b5ae4eed8d91805c94d1a528bd1608a0930d9f535bc4a5acb871c7c6915e8d7d13ba88a8cdc4ce0c8886d03cf36488cbbad19cae773bf03f9ef2770131ed664c77009bd5eaac5d08532c4df66ec466ffad96653b192b749c76a5d5384a9c76fdd16d0cd28901df11d87a88f61443e3aa88fc1bf887da7701e2ec2e2e77013b5022546e48fd67cff45cee0df041b06f0019b4bbd85dafe960e342⟩,
  ⟨64, 46, 0xaa06d40952637a9563c3316ba4e1c721dcb87828bdda5ab25c01fc2b3397ff47bc240b26bd182f0cb931b6a993d6b1ea69ccbb2b84708237f74b20b84c3d0d38eea4bc7aecb1999d50dbcb9118d937db2adfdb87433837eb3c0e57e8af2964f22cf368000d50630ad8c1a406aaa4ffb952698694235964d3ba4f550a28a70689528f1ea51a05e7277b1c6a9da5f69d689bf2f45308256d8d30e7d58d1938ba0dfc646f56815e71476061769d2637e34465b391e9febd40706711bc20f689e35243adb62732d333223f1cdf1ded40548bfda60f65921b28e4c18fe8658848cd74248a260b350eb205220b1b526544c908c24b23df13b196a5c91ea1ca468b68a82a123a2932ffe3b768b8e213b4331d208f3d7de07414702f6ad9d3d333330da517ae4c1b5b9a46959d0aca5c5583469189d05dce79b0a73fbdfe0bdb22feecebc6988c0dd11dd5a23016c9ad7b0741c7d08c491d5b98971d5a689fc7e54b1144fe4a4b400697f6252b4414e0a44638da⟩,
  ⟨65, 46, 0x2a8000000000a514e5d3eef37f56eb8831eba18ff9c9ccb8839d8c1102b2f77aa821139ebe16f7150b39c1092127b9d85ea7af3aafa0c3eb24fb8bd277505acb24f6893f37392265237eb4b1867963d3eb921afdf5d66ad631a174f737bcd7953a48b0a2ba2ff34368ee3729ae8ade562c75a6a52f03881cde94da4a56f7aa54fc381d710680000000001a201aa914f86a3932e4ac5895071e5c27654d32f959e58ce2b44480246483268f32e13ed36d9708662644bc234991e23bdf5d80676051708cb9e247ef5a57272deca043cc1cc49ade81448c00000000021cfb6515e6e86b0161893c24c1d9be5e3ab23fc77b378266ec80c707cb2af2b4c1d0a5db532bebde8b1eecf21cfa2abe41e5e2a8ba486111b41d00000000007484f09fdc69d72faa0b4b251a81a969dc9a22070584925c9abee65049d024ba29112740000000002300000000008c16207887622fc1949a748740000000001d12d428af5668742e2edcd1483c61c537c69555ef281d14acb78400b6⟩,
  ⟨66, 46, 0xaa000000000185632b085c461e8bc1cf1e0b67d2a22b9a4d8d89c936b881fcf42246e51b42cefb5c076863150e244f6aa79556a888b0bbdf13e5179557752187d9944297e84e3ddf912cf0653a58c6550520e4a71518891ac3ea287a545bb1665500a7a8245d90052453ea4363093e6c589d94500b5950bdd9a98da6cf48e68d3c6c26019a000000000093005b9337924b4113f5ca091c37a16f3eb21cb4913346a30cece54acaca0cccd95a49a0525ba1e72cacedd316129a0633d49abac9762825618983e211160fa209752857c68c2a9d58f6a23000000000073fd045a6291e80a5bd9dda79fddaa95dc1b437ca478e24c68ada27d119e0fd612b2053a7ca90c529a73c04d884a7532c26ccf29d25a225a04e7400000000022eb2e7caf9c8afaa20e46ba280cfe0e0b2b10bb1777a9a6225f768a62a3f5a241553a30618a02efa8c0000000001cff17679f5874ac1331b2e1d00000000008b12fc4d35c22db57ac6c1296972640b4d2b5dffc30d1891f4a06f26f2715a7ff358e⟩,
  ⟨67, 46, 0x2a81b5025498a514e5d3eef187a2f073c7861df38f57160bae2975ffd64db8b64699987f2fe627f8a520b40f5c9e06a1ca24fe3053781dc1a39898e3b20d7be51e589cabe7878e8475b76c4d61b61ac8806fc4bd6eb0052187343fc989451b4112ba5287a78380d09aaa89ca9a451e2db9904f087cb7a1aa88507c4de9c719ad213156b966861d4ed83b9a4b3fed3e7c9301865221124a3ee5bb894917b8790a40b23b53f50d0ea2246bcfa5daca1fc80a43099c071f086a2cc3c8319f429af2ecc4b3aacc251285eec98e48096ea2a217cc1eb1868c6c15dd28f2300e95d997073ff417f9431e7c9a55b28e79fcac3706e1b2854e9408e4de303d73dd1a50e4f8600851856b7c10a9a6f4255091a74e06322fbb9d163a7a4b7a73f99b734c022ff98c19e988bacd4cfd1ca2a55d6422ceb111b48cca1a642f4a0f30aa44f6f254afa31856b2eda28bffce674031cf8c62bc9c4740ba8ef3891cfeb44bbf608bae22fbf9722e49f3c287297668ce2f5e2b815af787308f0a34da7342756f51918c6⟩,
  ⟨68, 48, 0xded79a00bc6c97a9563c331697f56eb8831e6b67d2a22b9a6bae2975ffd6490313307a105ce173cab4d63962671968b65d827333e2683a58dd9631545ee20171c3f63d6ef314235e5d74f743f0be3984524ebf8c5d849985125839cbe2662cb45e5640b3ecea40b7badb63b25f558611c1f03e99402458e85da64d377dc83bea343d96345c79b977b19a6e17a640cd3470d71ab1dd707080416f0a868ce6a3f52fe68cbf98948c628bde1c9fe5e0b4f377628d769351c869ea5aa5add8bac2109353158abf4ca5b7c0d2be5e92fefcb24992a52fd60165d492064d3a2d96856c2957a2b389004d2ada9e8909399b344276d0893a13aa7b7970c091cb7b80283e900970fde0bb66ed5d0809f78e106f0da2b1f8c85dacbec7e7e66e60629b1fca7710924d585478416e0ce338778397c00fba8835b8af1a5e8900d7dff8dc8900529aaeb8a24cdcae268292c46672c5ea9b3b40bb6e0089101cf0e0f889cabc29100676fe34bdce1a772470b768ea774e435a5af288fec44df1e28905d4b50b748be709a9b22080f1f3af2908856f48528f588edbe3496eaa⟩,
  ⟨69, 47, 0x6cfff31933d8dea243fea5a53a4e1c721dca7431ff39399336362724dae66dc5b234ccc7385cf2ad359464af9c525a121c9956355c5333a401f4f84999fd3c7e814c7a4ddc38212799ddb2384531413aef4f848cd0326f8b1472bed0929e1262f59f7f68569784da4a585e1041b69fd14f821903d6012758a1f5b9853d9d68665f04991f01d5b2148bee1a051834ab4d0bf90e68a2bda2618cd3e3a46f099a48f0f0b30c1493f4d72b36291e66df0c72596638aac3ef269a97e7151c5a4eefcc743c9af47d2631116956297c10926a116ce6ab459facc35f0689938c9edd3210cbedb45b6263262c7af3034659901cffa2748bc139b644f4a79df32fc5e61fad2c5f2b7635513fb774688cfdf1f10d528a990c83152717e3aabc34b1bf95f6687498c1b7ec34e930b5fdfe59d2422a65a5b460fffea21368c85ca017255186b4bda8d9ab2ffb0fed3c482b570c53d0a6176c01316d193350d3159a2f48edc73e13c04c5d24cc6785ca8b8fa34f481d6bf187a064ee117e0540a06e666d027d214e213f91073d3373b2521cdda75831e48b170780318⟩,
  ⟨70, 49, 0x32e38de54f4413245fc15e2b4a603d260ae4f461e0a2f7696a31073b182204e81fcf42246e73f97f313fc52e5899c65a2d9a43932ac6ab8a3b063810e7469779d2257b8294de4f4c3651a5fe2b67a1b8a78daa8240046967d4a9cc6428f76c811d7e1a5e430baa9c0a43d1d1c42e86a9a155f87ee2c0c5735c6961a7d35a7b6100b017d5b557386bb50d57516a2ac699ddf06b1a4526c934870f18928d6cce67864d9cd1a1b3c1f3aa5e3bba1b795ac9728d0e28c9285426867248a00c0b4cbd5c6e1a662355cae1a0f913415101e80e08d580993cfb24d0891621728232b28319bd91336d2d3d1bac8c7b8e3e2cca419ce835421de19f413639fcd0ce1166f729e7a2dd50207b13e8ee0e2bc8cdf34cc76f5de6ee685140178569b1d05ce5ca3a94baeaf0291a8272f3f6260e9dc131403f47b4471d8a0993df4cc78baed9ed2fbb132f350c326aec468a85aee14405b142a142ff7029a47fadee97d091301bc8e92f880ffab32029540ab0337fbe5a059b34cf7f54f8ec5eb155be7dec734ee0253f64c31a6539a00cfadec0b3d00766aea826680a6a8cb249640c83c8fad0920cbc611b8b510db1b4718688⟩,
  ⟨71, 48, 0xc081c3f41588bfb40dc238289999d139a644a5b84ee827e48c97007f0acc8cbddeaa0844746d0b3bed707482d03d72785d827333e2686999d200fa7c52ef3a44af706a031ea9e91c53391ee95dd069f736025978534c3de35b3469f358eb048c5305e0419e646a049019f7ac5335959d67b46a2c13ad725c5362991b50746a13d20096cc53227cc1798c69f1a065f9dc58016f6410286ceda48c0c7c78c62fa207b078b7b5027b8078ff860a1c7c86a647a8720c86282896b14c87fe41b61b689a91c0a510148de2affb49009b218f4ea3d88de38db0f1fc9b2829eb83248dab7c9f307c9acdb6b5915c8d071208d3f4839012d767d887de570522d487111140105c7a6034b8ece07d4589699a6c7d1fcfcf290077c339169e6c6ae92db0ab8475b540ab948c6bed41558a60751c2554a8007a81087c11d07ac0f30908407a84678f568885fcfa32d48084bf94b1644085e7c5bc4794841d3c11b3148184867c930882f1bf3be2048077be26e464809ca08505447c7b3a7305b47fd6270ab1207eab99ca18a080181fe762247fe55c64f2348132282e8e6082a1b3057ff081ac4220cb308321426ef460⟩,
  ⟨72, 49, 0xe6fd897c23d84cd30351672b2fbef147fce3132e623a2bdcca7e6e15bbd06465ffd1ef090233d7c2dee2a0e76863150e247350e5127f182e9637658c551a4ccfe9e3f40a53793d30d94699c8f74aee82935fdc3aa481a647f6f60958a4fe33fa038c698cc6cc066c291c5e8c24e51a677f9960d00a4d0e50a842c69c58231b2962ac1b5a4cd171a6b512062ac8a4a9de04d350698a3fda77162cf8bb7979481acc5045d7428efa2d62fa3a077e83e4226043be103f188ab22602b623ed711445763f6bac86a9c77124744e54cc8bc423235f07710f13134a8dc0606048d7cfbb979864d2d87899c5a23513acb700693401678c1a508c9f300248524193716923bfa1a2d38154e210cf4baff23787a5d6cd32ca23e9bce0d3d309f47190e0fdc4f7af911ca2366b0a3f896d983aa757577a321b268db830848e968dfb914647aae42ce91243d91fa61c0181ef377ee0cc39012f8dda47748042fc542d3040290b1b56d22108cd01fb2a9023bb90bfb5081be5cee0b264024bb4b1fa9201e0848098b100c748b6171c80933c7afa004025b8a42de020146667782710097b1b5396480cb96a19f9e40eaf3769a3d20516a1a95fb904a83f67328c⟩,
  ⟨73, 48, 0xc3f1db0d6f00c0df9e1bf4289c0360f0ea80b935b73f29e099a605b37a70a6b47aba0cc28c9af460bc328ce70424849e73daa9e555aa74de077068e65ee20171c3f6698f49bb870452ff15b3d0dc69f7360259785323fb7b04ac69da167691785336779002c869e750ace2dc52f0d141f01869fa08d9b4c4532086cdd6906a218c88add4534d8a44dfb86a094a66f92c530bf04bc70c69e971302fe05bd29eefee8c6a9e216aa4bc76907dc93c7a75c4651b1ec274e272e5b03289f30c67836687b2809f6cb688354e0fd44e9d4dfb52fed88dd81b3642a49b0c802c97948dd90651c0e89b131aadf8808da0f5814b8c9ab85dced1448cfb26f6a8e082f27a4f3b75867b984a831e86850fd9d41a7a6b498232127d7d9edf1b0d7d913f14769578b574a1ac3b6af75c4635c475aab82f24546eef84c2dd7876cb377b19247e59cd917a6e7e340d5ced9a7fb8bd4202e28094f6df1672808cf85987ea807bb225957a82b1018c418c8179e6d461688199da5ec2f67f5dc4c9f01e7ea59496602280682d77cec67f7f71496e16806c233ab3ca8084fa1dccf6807b634edc26812619cdd984828ca4e1c4a481a1adde5d1c830c338754a8⟩,
  ⟨74, 49, 0x3da31b3b8dc713ad8dfc935e0b44c4b7f64444cd3614fdc802d2f656ee925932799cf850eca51e2edfdf11464c6daa64f5a33b0bd4f5e74e88b0bbdf13e74c71d906bdf2f5bbcc508d79a4f33bb64708a78daa82400469a61ef1ad9a293f8cfe80e31a66cef200590a52470c66fcc6996564225862925edc0f7db1a69e36771808aa009c9410d86a7d7d5a9b522d13183b0d3f1a6db815a5a78a4d1eab814606996d72873162b57b6c6c2e31a4b1d4a64d18eb8107acc766756a0f0292153a8f0ed048d1a1abd88f0dd7d0dfdd9051b82875d4378b3234ed47b85684123616b572e57934cf168a34cc8d868b3150864d37129cc9d323539eaaafb3134274adb70988ca8dbe0799c41662126f16be192cf79de5850cf6ee452fc67abc652b47cb3eb19de8ea06df67b863863aef372edadf58d6a0ecdb858503aac1e7706f01ace2b8f99251017bfa1847747fb9385e6c353f7da7f34876a012f1633b0fd01f8f1f52b3280aca6dcb97340293a7ff37ea07e4c7819431024ed82f3644811e22394a293fc49363e2e19f8b338aced0cffde1514a3467f946e7821853ff6998f7749a04544986445501c86bf80d8280d5262735ce40f3d81cedda2053cd41f886104ce96d97b98⟩,
  ⟨75, 48, 0xd4d2cd0324c8b32d4105241499e8d1818414b3198d6b5f7c99f358a2d8d0b532fa375b14998a088a1e30a56ac5a9fe028c7a9a732eca8be830fac93e745e555dd48674796272af9e5d74f743f0be698a09d77a7c52cfa95398c869f358eb048c53198d980cd869e750ace2dc532cac844b0c69e2c332aacc52e64f53f78869f4c7ed07e05316044537246a1c4bcf8de45343d302dc946a0419e563dc530217b0fc7869e117679f8c52c9323b2be069cf4b11556875c4a7bea16276bd12b230de79819fcda46a866170b2129686792aae81b68679121212029a722f8abbdc8d76f79a11fc9affe44aeaa48ce0f9c732109b06a8179ac08b5458d567509aaddac7095c8cf5e2d80c5482d92182d949866af876ffb682cb83e9cfb27a7ecc357f1e7dacc231b8917da5564203b577aff6cb297f7cee22ab70648197dce55a44806a989e1b107c48efb707407e4737d9410e7d9d5155caae80799fb897a2809315a65a62806b72dd4f0a8046160870827d7b5cbbe9707c8181672acc7bb106bc44ca8049ada0c4ee807d59d2c3567f92e2444dae7f8887d3de6e7e68d2109aa682edabfedf0a8313a03081a681226079e778828221d68cf0819c6d366c288301b259d0b8⟩,
  ⟨76, 49, 0xf7c8564567e04d45ded5c4672c9337fc14cc132f0d1b6c930b238bce14d0a4cc177f09d7a2c7bb634f56e9326c752f713ca4c228f58ab84611c208dfdd2317a4eea0b58e7d9944297e873c7423adbb62e611493afe31a46681937c58a3ddb20475f86982f020cf32291c5e8c24e51a5e1a283e030a497b703df6c697327a9fbc42902bf60a6cc1a6117b415d98a46aec6b6da469ac2d96884829fe391146781a651ea173bb0a443ebb18d8469cbdba36aa62c274187fb7c1bbc749ed73c0f092562e6adc7a3aa167747e3d29fa0335042181a288b37710b07e417844c861636b63f9c4cc8afa5468623030eaa2fba134425bd0330c8d5f105946624d13d16da558234ad2e625101039a24581dbc8085794f1a4040897f862120a0275a771603100c4bbc5f7347fb12e8235b43fd021ab9d39a001c3b7d6fdcfffb7bfea0da806f5e67f43c3f878eb1f20a203c2b69f3a410130dc0440688040dee6fdf84028faa2396a2011964d1cf10fe459757bd887e3544c399d63f82483d6278206c4fb0a9e1900bd3a42fec080e95ccf0c5040498cf18486201fab8c8cc88fe0274ae9cdc7fc07dd2f10a4021c792280b2031f2938985100bdced2916c80b1f78304c240d1e12f5858204b010d4e83904426cd72c28⟩,
  ⟨77, 48, 0xdbcbe96b05d8c06472ccc36499f4c8164570b34f1d15cffc99fa08c885c8b33bfcb2f7ec9a048ff429e8b2f21845464c999b405e0790a584995864fc8c82e130f4348c93da24fcdc738f77e44b3c73586d86b2205d849985125868e57da1253c52f2185d54e06a049019f7ac533bfccb068069fa08d9b4c4534f1b3b8c0469f4c7ed07e05308bda0aecc6a05fe581694533873d18b846a2d844f4d1c5365c5e95ef86a1583e0d65c5715ad812cac6a565904f14058ad7fe5b16c6ea1f663571c7a3e913d65187a7c41d85aa87a87250f6284856d26c8a8a484f7e45ed16484fa3fbca3e898958f6e4f5c8caa4e8cfc209b246d485b1c8de4fcdfa2ac832b07a75e1081aceae79ec882d059e961e881071784557081061a5621648103ffd10e408094de9bf7d47fce643118547f9af3d6959c7fabed78bc807f2e660e271c820b0843125c7f3709dfd3b8814894bddc6c811c6fa0b8448081afe2bf208084afcd9c4c808d825e25d88005a76f3db8806156455e088022ced988d082b5a611ab6c80ef4a46c268818a0eb9694080be6a5a91c0808849197fbc7e87537488307ef22db82ed07ec4ce227dec80f4e96976b0808326266ffc80fcab61b15c82a4910cf66481ada4a33ba0832420a31830⟩,
  ⟨78, 49, 0x3d097aa4c7e31361b05b14b1cb2ce8433a94c4cc581363f9a2c9ee4bf9c351332086c3872cb2687286f9fc4ccd656835e02c87a3a31a63932fea0e4bb30a4eee308676c463ba92f1ebb23244ca46fd68e653a58c6550737e25eb75802e72f8998b2d1a4c5eb3efed0a43d1d1c42e8699acaceb3da29343942a10b1a6410d9bad20aa009c9410d8698b02229b92291abb1adb691a670e7a31708b5545cd1d1486dd245e544762fe93cd6e4c81acb03b939290b8aa3f5a2e0c6a14d7c1e5042d308aade4f81d268e6ffaab8f4ac8b3204647a435f101cb23d2bf8da8872215912d4394a90a3ee0b70370856a4214432a4ce08a5f3278235e9648da3c104a2162dc088817b371f85c2412bc3028f782050d447ae28905b1e3470cb4809d5071b4884071b19a313fa02c574e48dc100a66e292d34803905763bbe3fea816638d29ff90e87db83d008228d910c281f82649301e3fe56b670f00209408b6c67d90165529d17f88096343d96fa4083ccc332052013a87643a09006738aee358805287843b0c4026652897b42078a2896854902382ffa71c0810d2489ffaa407eec4754a7205b55a9962e8fc470f5a8b407e71e014d2743f621c8a5e9c2024d1757e38900e1dd8c70dc80c9d224e22040eb120ee3582050f7c1cd25104a12e4cbfc8⟩,
  ⟨79, 48, 0xd621f442f408bbd8cee734b89a2d8418505cb3580e39dce09a1c4bc1ceb4b39e273448789a218c853e08b38b047ee38c9a2c13cfd054b34120414f1499c2c470aabca4b574d17fd28c66675436f28c619e58f4fa7483929c546274861cd0ff265e5640b3ecea6b4bc26d252c55342abf0fdc6a2c13ad725c538b0463652c6a218c88add454fafab536a46a1c4bcf8de453585b2d10906a2d844f4d1c5ba48bca88ec6a550706d4cc5fb6efd32d706a3cd8368bd855336a66219c6a1b8b48cae0549787f0a5b87322706d0d6c7a955e787a6a7a654d3f759e7a72cfe55e2e8481434b9b1a84a35384c2a284c8bcee6cf68563cd156954820ba23e4be483737de9a114820c8061ee60837a134a2f9881d475cc1ac4844a286e76e0812e96e0afe8810af7d86ea980a42330ea3e8095c7d4f48a8087a9d37f36800744f4f5997ff382b6cc5580e031352683831ab804f53c81de334b61f48372b5b78e048143f2de48088095714a8a4281403f6c40c68068b64c4042808616d500d280ac3ba0580a809570d4633a83051b925b1c81ad60e7feac81e9dc6bb55680cbd9d27d8281671393b5fe7e1cecf618fe7d4bb16edbbe7ee88a2922d680a8a27f8d6280a175a036ba815b1b2e961882f3d3b6d75081d5286db3108373288df1fc⟩,
  ⟨80, 49, 0xe7161ec42dcc510ba2ba16fd2e45c3389bac9336577ac3ec8b262ebecd7484cd0c1f7a7912cbff7c19fe61334d8a529ee8b295764476fa4cd8a64e8fa82c92e48f09d71328ff93fc620a507b3f306ef46446364df6ca32435fbebacce91ac3ea287a74a28da0895d302deeb6d8ec9af0820db4fe8b0315cd71a5869b14c8da83a2ac1b5a4cd171a69b1489bf70b44c60ec34fc69a1e9816e4a29fe391146781a6cb8bd2bdf0bfa4f35b93206fdb77e996b8335969c835f71a708d2032778b2328aca04bc69d31005db162c140d169c6a1d05bb3f355f8f4c3ea6699ea7a4e0d1498eb3d4eba8919b5a0c798cb2809d0587651119c282213f2a517f4308ff8902ff206436aeb5e990507db5064a88191b8d272d8414251f05c60205671a4d7be105fb6d91c48080b3d065dc064074d425e11e602bc2f82e4d500ddb66aeeba80987c336eeb4008b4f67f596004bb08ceaab010836ca0c0b83c87b555c7640b1b64e808f209f49bb327e9019255ff825880580e87211b40525401d775a01592900b075016ae22708e2806594cf81db40310b189c2ea0aa970304ea90265337f3a18812f150bf3e540564bcaf1f6a0214841bd9f4fcc830b7ec067f11b11a51213fb2694b0136a01612cd9ca6d00b21d008f9a80e053e58e6641009226da3220569832d429904fb351f53b8⟩,
  ⟨81, 48, 0xd62a8ce33c78b5c35ae428a89a3d29d2490cb35b2fc0c2889a1579eacd14b3287accf7809a0414e00fd4b36dba8a9a109a094a7b97f4b35a869be9c09a13d1997ce4b2e8b5f0583499aa825cb544a55f5e50e0588b7f6e1d0ce08b58c685d3dc7516ec59954074a1e9e0e0345f558611c1f069f043207ac053e9ad3db0806a13d20096cc535a890315646a094a66f92c536dc0ad2d3c6a0419e563dc5328f50b9dd86a1583e0d65c56581dc9c9486a3cd8368bd85384690193bc6a24a932b5f053450aaae1cc6a07ece922886b0a33507eb471b70ad8257c7add60ceaf707bd1ba620bbc7b91d75ee8248247080951a8821e41e561e481af7c7c4b2084fe6a6981f881f35fe90a488343113c82e081f43e1ddbc08349a3b6bd4481bd3dba7c60838657e2b8bc7fed3ece5d9080b691baff8a80a719ff3894808aa63409408088037e9a1c80103a81324a8028301ffb9281937463e94682ea8190b29c81c5f284c8c8834235253cd87f81c3d3174c8089525a67bc80a37e3a39dc808a602abcf4812de1409b38823cf7c3e2a48220fbdccc3882d4a522c09481951ea3ec0c81c302f17ef881bdc9fa6fb88144b9c2fecc7d84f7a9df0c7d223baab5cc7db30500e150814c5877f31c80e1b75c1d508142d8f1631082c38e21699c81bce641af048342a3e36ec4⟩,
  ⟨82, 49, 0x3d20300f0ecc143703e2ac9c8b7aa584fa1ce4e369b74fe702cb14d01a00993324185d8e74b220bf44920e4cc05c5d0ff12c99c4978d8e1330bf0485740b253dc4d16344cc83fd125702c7a21f8e6eb93156e67a2dc8a3420026de3e45facf0395fa22f79af2a7490ea7a8245d90074d5544e54d22fa65009163a1a4eb143eb730b017d5b5573869913e60bcc6292a778134d41a617e0978e18a4d1eab8146069810bd87e3c2910faec63611ae2b5b025958b8aa3f5a2e0c6a99b53310ce2c8ca2b2812f1a68a1555c398a479e8b0142c757e360d6ff43501c08791b41d406c98b58a8f80f407e33e87c1f13f6b8e23df1cea4981a2095e5dc7698904bff8bd3d60820a0beee60a432760b40753205c04654c4e1047beca648508170ebc9df384121f76170a7204e59240e02103d2a71df9447f9a9ad783ee40590e3a02862018cade3baf9009228380bd48050e225161c400f9f08e7a9200b2ce4c476101d64be38f0081e3bfca822040a14ff00483208ee394212c0ff115dbc6cfc8047a89252d040447170847f1ffcca26a1b0102c66d4a964c80edc225269a409076686df8207383d8cf7c90223996e12d880fdde5a0a0a405049a4651120266f7da9748fbe9a1bcbdec7e951a218fe03f7fda10dfda2012628e78ae10092ff1818b880bf86d4634840de4c1ef6d4204e64efd34e90478014f8058⟩,
  ⟨83, 48, 0xb8e84e4e02a0c012ae93a1d8a333b5781ff8b3ff2f629ab89a345390c10cb4508505537099f23accde14b2e13630e31499e1041d1370b32793f18e10999883a91fecb314758ec7bc99288639be88b1481f57c97c948528776f90a31eef1af8ac8bca593c8b3c8c28ae8bfcd074914fa90d8c7478b6e6413c5da64d377dc869eceb4332f8576a1aaea2d469f1a065f9dc53147fb4ee2c69e971302fe0532dae50e62c69e117679f8c5397b746d54c6a565904f1405429af83ca086a1b8b48cae053a6200bb62c6a07ece922886afc6c1adfe87c02017741b470ae4d50b2bc7356342478707acb0ab362087bb10bbd3ea07b771d2cc0f882ec9b5c0a30827319181ef881faa0808ca4826f657a680481d5196523d88303945bf60481d1426b10a88307ff612860819b2c08ec9c82a8e5b9d2e87ce21b8293b0808d55f9dcc48077b202d480800f0937374c80cecb8c510080266edde22080238b6fb5ec80b448c4f02c82a42afcdc9480ac64c39ab482fc30e349407efc28af09548077cdf7551c80899d74f8e0806363e53f448076a8f3be58806ef9be3fc08078693af9d4828e8d2167c881721965a1607f532a4e37dc80a2f6785160807c5b376db07e08c65737b07f4d80c80e147f05d3cd76988074b16bc1288077e4de1a5c811fd37c1ba4827d09e1e69c8199e10a43f082fc9985c798⟩,
  ⟨84, 49, 0xd5eae223b84051f090558ebf305544a809759424de788f174b6280749aa4c4e2343030bef2cd12a90212c932eba16745f0b1e861e2ee7c4cb24c9762762c8bafbb5d0f132d13d150124b21ba082166a4cba30be2d652c746f126a6912885a8c5d364a1b8e3cc98e845a00035418c22d1dc6e535d0e93e6c589d94743e5bd0d5442efa8d0f658d1a4c8f80ead90ab1a6777c1ac6c00b7b208142cf8bb7979481b7a53ddfdd18ad5edb1b0b8c6964991d95f02c274187fb7c1b15affcb62d8b4c22ab793e06a4bc3f852dc2c140d169c6a1d61466a0fd68d407021e46d0785726a8595e382fd7148b851d7da981f57c0fa50011935f07d49dda3f8c03e7c94713d2d204ef2306da8101f389b664788082d7ae18f640be1b3a6b982055001c5b139040860c1707081948cd23d704160ee3b848320472f5e1c019035fb7bdb1287e40eb26d9de40422e00ce78200b1206827c900756376dca08039a4ee417c40030e5459ad2006d558b06c100d356e9f81481ab5472b1ce40933fac0a7f2080d3607a310fa0ea44e23a87e0f8a5dad603fb2aaab5fa71ff201db39dc1006a5087cb58802f5893d78e401cd4f6b81420656e06e583901eb5e1d13d8802c77ee95d4402a7db3cb0c200e830eed9c0ffde04a356487ff5505cdf003fd6bd0d3410200d9c6501ba900730614b4a880a3691ab4cc40c21ab8ca0620475d79ac24904078985f3d0⟩,
  ⟨85, 48, 0xafb46c8560a8c567b3fe70189f7426e6efd8b9813cff0b649cf32326085cba92e74a0a249d0603b9887cb13473a5a32098f167fbd6b8b104be9fc4bc98ee38bfd6a8b160b8d101ac98f3f19c0cd4b137fd2895fc990290394854b0ee178fe60895bb45cb7344a35bf66e0d4e8b6306901aaa8b7958b1d69a7402d6542f76741f137a71c65c79b977b19a6917dc340a3052293649a4386ceda48c0c7c5662822eba146a9e216aa4bc5258ea53268c69cf4b1155685de3a4f6b9e06ea1f663571c6934737fd55c7322706d0d6c682dd9f9aafc71b70ad8257c6a0364c5ac547356342478706bed4c0fabe0761ecac3df8c7c8861dc6ef27d9142fe4aa67cf9eb198ff680d88dc54d7a80ddc033ca368097d1d122ea818264e3a0b48336a247dca883199346e7e88160d765124c825d5d84c65880ab35f6a19880ccf0ac5dc87ed37aef2b50804c7d9267d5800093d6612e7fe36057067a800151675c327ff57bce18ed80035ba73a6580219517bd0b80c8ac202b2480b4aefb44ec81201effc8707ef4dfbb1c7c7f226f133caa7ffed923c37a7ffecfd7278a8018ca8d612e800202e6aa8e800294907cce80b2e7ed7a788083dd43b77c802947a81d6680009317d49e7ff7c342c0367ffb72cc3bc67ffc1a2d10ca800280d05d5e7ffc12371faa8000954a928a803197836f5080a090f23cfc80aba48eff54812021078744⟩,
  ⟨86, 46, 0xabb3f110cd331bbf3933e6afac9a62bcbf2e75a6603ed0edbb92282592d04d63a9a34e5b21276924ac955e3a9e12e265cb0c8882b45f1ee6d94d9f695a2b5a2c1e34f0894ee24beb5bb22aae09b6b3d5edfa3f7d344e2a300b6cd3ecdb003058abba973805e60aaba52e77d8cc24ffb952698694bc0e207379a98da6cf48e6b484c55ae58e17a640cd3452ad342fe43918928d6cce66318be881ec0fa2d62fa3a05a41f724f1e8b8107acc76657129efa8589092562e6adc68fa44f594614ac8b3204646a5579e1e9a94c3ea6699ea6b75833abdc180f407e33e86b2c2acd8821a50011935f072218771bbc9f4d1b46b7287d84c99aae81f5a33e2f1c28039ce50918a00e3d9a6caa8044a92569e205106694c8681c35667c6ca08f83d895fc7e35d47799b1f98c98db99681544c17e10a00780abc99c7e989ebf10ea0001838a7177ff872fbb8c9ff1bf1158fa80455e8ddad9ffec525cc838000901b3d160487c9e19b9818c474b50b2059f46c5bbc823c3988acca0086d99f53a7fcd4835aea1ffdd4a37d348005d53675ea002bd63494e8011b0162e02003636286c881610b4fab2a02186f901ba7e7c843a0e120001778172c7fe5c8816569ffb164a63f2800f4522fe49ffd5ccc86267ffcaa5f2b6a000bf0007e48061a396d72204f81d9207480dcd048904206c88adeb32⟩,
  ⟨87, 46, 0x2a7cd2874fe4a18ffc6247f31d790da4a9af8fa468b7c52d868a3019d4e783185dc422cab09fd8f9ce3b6f8166bcac9550ab4b02e2b355308ad2adb574fed4cd599baf98f62bc7874adb6adff4d70837eabb17d940c2ed627d1ca8202af734c72c48d7655d0cb7ba946cce66cdebb9c1f12fcc2508d65934ee94da4a56f7a9a34f1b098066861d4ed83b90d71ab1dd7051457b44c3190c9b39a343662ded409ee00fd07c844c085711946c7b08ad41e05242a5af44ac8c37947542cee8fc69f107616aa1486be203964699534fdd67949c1a2931d66f46e9882ef183e27ed71c46ec42ef4fa81a93bb47f18076450bf92a99f613266aba07e7c86ccb2d1f90bc42028a8010460e3b4a007752a9e2a80062f68f6e20492a3b29e281d510d747da0b6a4683f488117a1581d11ec23ee666e68157201b553a0657a425f6c7e437e4398e9ff220eb28197fde033f3959fefe360f666803816bc8c39ff7304b530d8050b378afae002c89b031b81953f7d57a202149a0a66c80c8564f9c89fe7b2de9d9e7ef915cc61d2000b6e99a707ffaa91e80da00d89f3034280046b62304200203ed6c7c8164e0c0675a041cd076e42803b44ed96b2002252d64b08007bb133df9ff9d72c50527ffdf83d826a001476e437280ac502f3bca000cabf060c806476f5551204f4fcc95448154dcd020a209914f8cf0e⟩,
  ⟨88, 46, 0xaa0000000002926f4125b26a1cdec4fe8bb1921f0eaecef6cfca34abc2d5224ba5a4ce5ba8c850d92c99945f10ece465bd53a70ac8706cf91c2dfc2606b7cb2aa0d611fafcd5138d9f27d2c6811a6665ee21376dd0a0aac77365e422d77e112dee92b30e21f9ddcd88b5a7f90da97017e1266abbd75bdf091a4f550a28a70953f0e075c41a0000000000692cffb4f9f1080416f0a8653e3a46f099907cea978eee63fe182871f0f840fc622ac5389cb96c0c8a3c3b41234666067f3691a94a7e80cd4106a1c943d8a114afe36a21c869cb3f9578b953aea2466d66e475d7ba0917c73a9260686ddc74b303e19f251c4f4b473e7ac663fd9f5a33e2f1c27e42f1080a29fa246ea49bc80000000000202d46bda6d07ff4a0736c2a03bedd3082e819c2571567a0831094206c7ff6b1b90201f28117f886e80c8295a4e9a021c155a9787e36ad855349ffccde239627fb7b98795f1ff282c7f9d8800000000001ffd1cf5e7de802f357f9702013127219a681ed0156e69205fce896474824215886739fdecfe208767ec7a267e539ffda3b024067fe984b2aa22000000000008038693fcce9ffc082557ca817cb08c41ba0160daad1ba7fa7c06abffa0014db8b2fa80000000000200000000000809dc3b7fa11fb6960c4ee080000000000200699363cf68007f6c8c27207192f4f40c81410e90df9209625ea4c3a⟩,
  ⟨89, 46, 0x2a800000000062a70c66c8e187b6789fd3a64433922fb4928f5bada2d21f3db81a07513d3dd57463c1cfeff9464c14515d177f9c2494e514a829494352fd0de25110a6d5c1149a9dbc049425e4af03fcc148cf00a7c4a2cc21d3ff159593d801e11627e3d0c989014c488a063c02d5a31a3a4e95c664c674aa3fb5b051f8d9a254a3c7a946800000000024c016e4cde4930186522112ce6a3f52fe6a4787859860adbcad64b9469a991ea1c8333015b11f6b8a7cc319e0d9ad5ec4786ebe9985c2c84a5ac0d14459bb895b49b22a292ac896a1ca5492050d2e6c6a63cc659404e891c202546a24af2ee3b4c48bb26d7028c227791836d408362371535ea00e739424628010460e3b4a000000000007f564c29ba81fc49f8172b47f6ce53324a9f28498354367b6f0701a06a07ac7cb89807f1c8d55ea5207f6b8ceba28176f3c1574a0c130a0cad8801822a6c11a0002410fcf28008727ff122000000000007ff1d16355f2000b07e6b267ff761789051fcc73e110327ee98c26e5a201f06177bcc82ba3127d42a038f814436e80028103ed8a0088288c96e800000000001ff9bf5a9b007f83b9617b99fdf3450b646810ec5396b3a02e7c4594c68031a27439a9ffd3a361016800000000001fffb0e37d0480c24b7afec2000000000007fbc96af7c61fdd6e7510627f001589b6c1fb5f55bc8a07e43ede49702088a6bff386⟩,
  ⟨90, 46, 0xa9f3b29ee142946bfb28e4062ff68e0ae2188efee8367664acc9529909240e9fddd4a1e8080ee3a813d8030d34ec1f4533d2acc1483a814166424e554b992494969ed65e86240e6578124149aacdc4ee428a5f01c6cc147f6dbe82262d2589a1d0c94f2c458476627105bbec4d149f6aaa9edc2cdca65672995709037217e40fb6bb700d9a05e7277b1c68806aa453e24b4113f5ca0928fb96ee252cbf98948c62a4fd35cacd8ae28c928542698a0a25ac533445763f6bac9eca027db2dadfdd9051b8299e4aaba06dab07e417844c93df917b4592a3ee0b70370928d4e130a8a587651119c28879079587924bff8bd3d6089cc64607be21f389b66478837700cf28da00e3d9a6caa801dd4aa78aa02d46bda6d07f127e05cad1fc4d27197907f91afba9579e8c4a4a9d0a7bece3757d0a08cdd9f6308808ece62ecb20a4369384ee81cc01f65f9a0b24db3f76c8217a9c6af1a001e30ac5a880496d859ae1ffde70f53e87f8ce4d6c312005dde238c880002e74f619fe8e855d0308177599616f2053e1b0d3888116efec730a013e53c165a802fabc7e26a015b5bf86ee7ff010cf77a20012abadf948002e5e99cba0001a92e2a68132f778774a044623c1d7280540b992ba9ffe3f3b3a3e7ff9bf367b81ff92a775f6080045fe040f1ffe89608bec800635a869a1fff0cc10c1e805a1543f8f2033a8415ba88078ade4fa3208de46a157a⟩,
  ⟨91, 46, 0x2adc65a9a114a1a9fe54ca6a863b5846546646534a4ebe98c6e26b00d46583c378cc112c96ec8773e21cca864271142e4f790d98223d1e45b07148955f673ec235ce88019a94956e295c6a26235c4cc9a1481abf6cd442e0097df7bb1619da5ee55630f2bf558779533bd621cb62c80818362314bd059817cc313c279a5a795a09a517db238a3b3867a51aa7697da75a6a3932e4ac5a470de85bcfa917b8790a40abde1c9fe5e0a3ccdbe18e4ace4914018169ff906d86da2d538ee248e8a0d5383f513aeba86f1664699e44848480ac2c6d6c7f3893e8fef28fa2ad4842886549322f3b9b3da4427e54a2fe86bdf1f12c8241417ddcc1487ea82023292105af5c31ec825f47448baa0112a495a7880062f68f6e1ffd281cdb0a7f6ce53324a9fe46beea55e7f11e0276d81e52cc88d7ca81ae9379a76a08f90b7221881a1deb76f62092ddd8e46281548ca10e3a07ff9f74c0c800997dd361a0049e1cbb2b80088985aaf9ffe680fe1f67ffd7f41352a00c0342915f7fe19d619166000426edfed80e0978e8b7205a0468d944823cbc89e9ea00ce9dc9696800d17eb09b201763b42b548055261a3839fde93ed197e8002461247120002d5f842881618e7a25da0419b734c12804fab8f06320033cc735f07ffa57e5ad1a00086ac1fda803d813acbfa00979696b36800774ea42da0004628340c7e8d61a4ed52053ef0b252c82089677bdf209f0addde66⟩,
  ⟨92, 49, 0xd53a8eec44ec48fd9daaca48a453f65208295229b5143a90a719ebe56833538b2d8e0509a9c6dd310e800cca18edd889b84ff5acee57a834085aa9242a146b1fa26a368d242ba72d01851ee1868fb0c34b8e99b88b11470452d05630d2949e532bd056a2a44427263585a2b08609161a623325038d42cf4c39ca451c4e1b35b4c34a4d7a51e3b14630296fea40d1cd185840d45c725f7e51c73a6fcbd14c209d2a0e3cb84ed121cb4913346891da9fa86874d3cddd8a35da4b31c5561f7932f571b869988d48e052880a4e54cc8bc42323a9bf6a5fdb13b51ee15a1048d3917c55dee4cc8afa546862312b1edc9eb93382297cc9e082b1e68ab4aa4308ff8902ff209fcd4d303f10c9d82d01d4c8137b2bd340240be1b3a6b9820304c9c74169005106694c868024951d94f1400efb74c20b9fe509306a86cfe8c4a4a9d0a7f2966446be53f2f7cbb909c2048c3e0e9021035a1c74b87481294ca1a20c40d9d4795cf3203c3a716f85902b1d758f184804b77ebd8f040028455db15e009bd49c68850040ddf1111e8020c135cc37400871b28b36e003e10116ac7002eda39bded8154514d68b2407d7f104187206b1287b0d4100c185c765408023de174b174011d9ea756da007c194c85a4ff79bcb91d727fca07f9a9eb3f980408310e9faedf0b3b4b900416b7f84f4809246887fe540120d846cc6a00801e6e72150049fbaab21280231bd787834010b76458f4a0094f7877fb50047a1e503768077e77a510e4096b8ca76b4203c87d3aa6d90359852db424⟩,
  ⟨93, 48, 0xaeba638ed0d8c1af4d9809088eba25666a4a8ebc84dae71e8f1d0ed5328a739c7c88a2927389af048e32744a38a060ee68d055f209e052a7df4fa4a069c171774cc852e01bc8322869f3602a566c5321b5b38ba46a0ba252eaac52f4b1d1f8c869e41dd5bdcc542da09368f86bfed3c1d3f455998270a49069da2e437f6c52f83ae6f22469e2aea02d84531ea27bcd206cc161b70aec5f5a405bc40675b634c39f567534cbe5679688c33b3952b288891af3e9769351c869ea5a8d352fce2a389aae570d07c88de2affb49009af83b8878988dd81b3642a49b0b5ab972bc8d76f79a11fc981875517dd08caa4e8cfc209af4b246d1e0820ba23e4be48321b575af4c81f35fe90a4882e0232a627081d5196523d882a800e2d89c8336a247dca88070d599f1b280754435d1f68067095c559e7edbc1c0681a7efb38dd5f42806ba4de69da82461f0748107fc10bceb76882d3078969307e2a2285ac0882de0925cc247d403fd8434c828bfcc73a7c80e53a3acbe87fe3ca3929f58070a22de0c68069094bb3a6806929684dc6803ca047273980385a6c7db9801e169f77e7826c2edc5e34818e6d640f6882d9abb4a42880fa8d9a06708070c01f0352803f21e1764a805ecb3fed367f49028ac2e67fa0a932d4e27f0bc07d8e9e7d3832ab3a347f59395fbae48162b24bfb96802f5c6fa8268045baf5789a8053f203d2e67fcac99d19fa7fdcfb4a762e8072a313ef868071276c380e8100117725d882612f88ffcc818bd53b401082e064f2c5fc⟩,
  ⟨94, 49, 0x361fbaa5229313480c5e57fbcbcb9644effe447054decd46c23937a4af80791c45986fecf4744a7a0e324c3a17bca94c571d102c4f7e6e0d1206d86fc6c52041b55ae9e34bf3b023870148f1e0f54598d34309aa3570527e9aff046e34dcdf2df0ca155320aa1a3f0d4e337a0f33459a9230a20663599bdee37c9152f05ae332f8d30ceca52e5452546bd2d41e34c863a543b4163d993c37200d9db2872c7a06374517cfc3e3b464e2e837f1d9c5688900490ca0cccd95a48650fe405218496b762eb0842349ddf98e8793415101e80e08d90c7a751ec4d2a370181812361900592f2934cf168a34cc8d7ff22575524d1096f40cc323648da90b63904a2162dc08881b9bef4d08a4141f6d4192a20686227905c1047beca648508181ca2dfb02410218305c1c20633268dcfd1008f83d895fc805b52341fa44020c425081b200f58f971301008cdd9f63088047c85b910c40d6871d2e1d205a60f12d2610479b98693d88164183bc2ae412094234482204e48e3b218103d1770c6518809350ac5f6a400f9cbcec87a01261bd564f900845608341080372a69db62400b623f9267a0012b9385b3500d71f71350281e3a37dd7d640a0aa923703208ee48db2cd101514bb03d748047cad0e90c400adb450eff200f1f0678008ffe94cd2e4288046d06529d83ff8e7c3215c206edaea51d59022429d17ba880fe200bed2a4014efdd44be20110009cfe80ffe0c5d49a847f9305a7a3323fe4cb4694c3201229948bde90098503dbe4880bfceefc10240deaf2af0ef204e78bd99d99047c1b704224⟩,
  ⟨95, 48, 0xc27303833378bb8d6024b2909e9a9c0e8928b645c8184b588ba3d9b043a48c86677f887c8c5d5f920dc4747c3ca72058741d7a7e305073dd5d179bdc68e14a2f765852a99c462f3c69d1390c3e7052e1d7af3cd069f43e2b9af0532371cab3746a0c80655e2c52f66df0003069e4fc52bb0055170e9f973869d3cba6955c530d166610d869d90002806052f9f75774ac69e38d80d4d4542932561b2c6c1246789d0c6f4521ff977c791bd5a0579c7920c9a3ccb88681496e879c86701c7c21a89353158abf4c8d7a3e9318889ab013279f648de38db0f1fc9af9f772f30c8dd90651c0e89b0d1662a10c8ce0f9c732109abe20b28cc48de4fcdfa2ac82f66e3f0b84820c8061ee60832371a4e5b081f43e1ddbc082e1d793be7081d1426b10a8832919a47ae08160d765124c7f8d751de66c8045e85607447ffdac6e40807fc723557a948023b398bb2c806877addbd88252994344187e2a2285ac0882c83077855c7ea859f49ef08270633832e08160c2241ce0828d850cb25c80e610763608804645d88bb8807111f9470c8066aa3a56dc7f9ccb1d9f608013d706084c7fe28d12cf307f7a5edd179c8289aa49bf188123a2ac8abc81c611bf8ac480fa5ef3ebe47fda2da6fab4802e2aa80c687f7beb02bd7c804da9a844648040ddf66c307f0c8e531600819fc8386b448164dada4f50817a48997ce07f4af5a25df0805a0169e2dc800a401304d47fcc26e746c47f12e82703b48071e98e98688117734899088112950fb7c082628ba04428818ca1d31c0882e21af519d0⟩,
  ⟨96, 49, 0xe66e7529cd7c4d8ded8ae6242cdab003508b933453da279f4b1b3f97ef72646001f5b03b6a31969e692d6d1871509b07fe7451c110886f3a233012f3449d0e8f5ae17c4d12708198c54520aafbecbc234c0e00ec0891490c000b1720d3499d1be1345529fd810d7234de8462da80154cebce3bc98d3307830efe8553f5a93f76634c2dc1ff722149bd538f83d8d3131ade15a8525b06a1887834ca0a5cce901534f00bd19d8ea5591042f986edbe4d254753d1d8185da749e7da6db2e10d0cacedd316128661e418cfa1496df034af97a34ab14be0849342245885ca08d9414f5c1924d2d87899c5a23626355bf10134dc4a73274c8d83540bcd604d13d16da558206560f4ebc2104af0c0a3de081bd09a517cc414251f05c6020693476d7a890487dd85c29c8183ffb094304160ee3b8483204babb098cb0ff98c98db9967f611f7333733fca045fe21ba00fed719d74500a4369384ee80496eec723140d9d4795cf3205bc124b98490482508d12088138319c1970412290afeb8c204ef7b074af103de341f9da880ffcf1e9492401c45cfe1526012552077dfd007a0e7e030e802d3c1a1165401045721f8d6006276c8d82300d8d51d6f5b81eabaa50abe40a29b5f38ed208fe236cb9d10156793470f07fb8bb169cf74019a97fff5b9fd76f946286d005f111303d6806d519b49954023e195e4cca075479759851022ac4677b5c810313f8fd2540238bba8b2da02d098d0b5ed000006ae9d4a7f6d8b3539693f7881dd1c62a015566d2d9b500cb23e7a7a280c31c3908f640e1dc5bea82204f4a3ead56104865ae23a88⟩,
  ⟨97, 47, 0x7947cfd85758e4f7502f8761662faa5ae5a393a3dd66944598b244e1df8e3c4f06561b13111dd7cc9aa6348be9a2cb4c323e51812668dad8bc629cd157062b9da9a200ec94bd128aaec1d4efc24736f0d76b0a6659b9953909397730a63229be58ef3f40256a383592f0a751d0e80a20944581a158429bc49a6df0c24c8d3be8320a66f7f9b7cb094e87e076ec29a0f58b9af05511675fdc88d6ad9b7127011f9bade1872302bbc3caa80531e5e092d44e37e34465b39c4c8978469346818cf526ae8d79766259d54bfbf2c9264a6a116ce6ab45959418cdec89b56f93e60f96a27596e00d26d07ac0a5c65a9cf5557d9896a8b1aacea1695a5cc4a2020d67573cf644286a23d714483a8eb9835890ace349af7c20de9edd3e304272c920701083365811d93908e5ebc380320559afb50cc40551305f84280ab900daa9d00c8295a4e9a02ede782ae94073007d97e680aa4650871d07874e2df0b1ea01fec21a64272471d90c082c1844839c109def60e95e20a9ebbf034a421e2d42a9a8815c0185ffa1009d85775dd602a84be36cb40404323b38a8074140c992cff033414a2360033f745762c07946898a8381b087d83c60fd24943d3221d95be6794e23e91157e6b987ea92bd2a77cffc71921c1e9f99726899dd402e594f9ea280bcf343b58d0150432da83a0ff058c37e8412cca1799247effd8b3e3ad013dcaad1c7a025434c3c0f3f8a06c2d1ba7efe9c9e41ecfe999cef52ca02847ffe87d40553e57c52e81b508b5818907c9ab966f5200d9f7b77064271faa4fb30⟩,
  ⟨98, 49, 0x33127643d1a313bf621fbad00b1f6fc7d3a7a4ca3c229526f2c7ad8f90d049328cf1f73c9cb158fcf0138a45fc4785e71f230dcdbfe465118406d9ade9c743ac4cbc4763a1b67fdb6471d0c3541fc500d0cc4aaa0da051b7024e58b034ad065a9d241570f8f02de78d9b6bddbbff85a1324383698358af1fef8b416cb04f495fe8dd48094452b056a23ea49c4a34bc192fc4181484e3a7b05a0e9d455db5a1468ca1a6d16f438f498e9e9df18ef15be9cba8e16da015bad46aa1773b5b303c7a7faf501c1e3c477bebb010c9762825618866128942f76494bf5805975233f5986be0d1336d2d3d1bac8d66db5ac8ae4d0059e3069423570bb9da28934274adb70988d56ed6384ae40e68916076f205a0b3d2c3d105b1e3470cb4822514373b70417edb6471202070cafc5717903d2a71df944815472dce97440d7edef6c4a20199e158bb91000780abc99c8032bd212fb6400870556a5e20182614195b100b24db3f76c803ffcfba60640ac75d63c6120517f98e74f903d1770c65188146c286592e40f78d07e76a2043c5a85535103293703b1608069391b54d8400cb3a8038b200ca96e03cc10055a853a71c8029836b7abe3ff88e9788da200349db6f411009855e9ca1880f6b5f60be43fdf2cad92271faa9680dbb28fb7abb6347907f834d6c510c3feca15932621fe1a0d15d6410049c2bbc944804478691d80401962a06dd0205e985f8fb6101be3921703c7fba8f3e9924400c6d6aa50a200ae6303d3f8ff056786eb7c7f9882a8ddd43fec05b1f5372011fd7820a910073feae105c8095bdd054f040b4b9f7026a201d4030a28a103d0dc96e0ec⟩,
  ⟨99, 47, 0x1994500517023bde70a9e20c58ae06e592fce25a5fff063963984684d1738934ab8318058e2b56408d0e12d79e647d92ef824c8764a60189c9df5f4be727a91902696861c3bdd4d0eb8f5faa69a5b1fec92992853dc1946642242dcecc6e8ab270af0ed60d6e522e95462bead70bbb283ebaeae13a50ba2301db92b0f42805e20e42c2a31d3c6305215cc21c4d8cf80720cb841305dc0601cc2f18bfc5c0f44b66b7b51498c1ae188bd3412b61d8842c63223c945321c54bef25211a4e711bc20f689cec0a2e1197460f8844583e8c72404b7515481934e8b65a64e327b74c858f71c7c59949a0e2411a7e964f98012429267d937b54705951b7c0f33899ebc5b018a9042bca78d2020838bc22ab8413aa0e36910825d2dc15fd1059e832ee031ff69f672ec83f3535af07dc79c437052760f2075936cef1f69bd7795a83fa627afc43a7f21bf21cc74fe36ad85534a0030454d8234085ea71abc68004cbee9b0d025bbf5ec7820729d1d65f44126a158bed481cc20ec6c1107fe78f4a49205700617fe840d27236a9b080007e7e67b100501b2e3c560010c97f66d3ff1f0657cf67ff08bc82d04ff82557152a60008e563ad8c00fc59c07c3819bb1e2d1f102df02459042092e8bab8144003c5cd1284800474f199a4ffdc1b4b6b89ffc705bcfef3ffc0f90d696801adc01893d0009f5b726ca05c1e2079404086f1f727807ec4e3dfbfbd00086d1a15b9ffa26f1a1b53fd8074c38d28009ad14e36cfff269d4043a000efff66c140024648d9da80695912b4e9029ae8bf7dd1fbd9c7c74c43cd15896d5dc⟩,
  ⟨100, 45, 0x958142773bb59a49d1818d78eae011251160c8d7c03c5dd28a553cb8d67a8fd6cea35597115acf55a029212251d79edc25a83ca6c0ea6dc4e5b2f0ae3e592d6d8c1ccf267ef6ed821333f0cc35dbd5a57a295ceb6a257cf22add26fe7d090862ad11c029710c66f5976740b09ab3d431236c5be8e4acad52dd1689f4ca684b26624c25a9a15f28431def2edd92ebf7cb42d54f1eefdd4cdebf1d6e5ddd5415eb385b5730b7eabdff41039aa63c87ecd8d9502401541f9756d37b8d490eb6d89c48fdeb4ae5209752857c690be60f58c355b0a55e8ace65f6da2db13673a0d508779c8096bb3ec593716923bfa5e4f49e76eb598849bc5af96c90c16ca4c897f862120a20c34ac42c91c6c668c4fe8857bec3754c74d425e11e616d2375ff1516438e80a18846aafcee624422e00ce782098fb24cfab0001838a7177f91075940cbff33788e58a0004821f9e5001e30ac5a88024f0e5d95c028455db15dfc7947253eb03e72f3b21e82322ec45dc41c45cfe152604ec2bbaeeb032cea00e2c80a0365c78ac025ec9ea7ca0002b6b3cb500bba2c1d7e7fcbc617ae3400d3ba456f9ff1331789330002b0d10fc7f5426cdfa340663cabd42a0139b77e963006710e8dad805dc80d09abff7900e9cddffe0b701334ffecc9fb97e7fcdcdfecbbc0006f22e355fab7d2175daff246196dd180500267815c010e3ea435dffbbfe52d2d0000b2d558a7fed74552443ffd4da10879ff686daf39d00679dd5be98062248e339409f7eff5311fdb720b011cfa76a7d1661⟩,
  ⟨101, 46, 0x2956499868388c0dd3a765aaef0d1711602f35c072c2462c689cf82a02e280ee79c64ac5559037d7cdd847bc851d2c2af2bb7542e09a433bdfea5838b34541e961376375ab257f50d8c7786849d05c6501a188c8bfc12680fbfc36d1941846786062280d301e14d15a01b3ac79833fbc3f222f167e3dfde0cc35ae377eb2b95fc5eb5c9f6331e28f636d192f7df09e1c49cd553c08c17422fa626be3fcbb0ade0198035683db2241da8682d81189f44bc01fc4247d5fe8939940290aa69e54d922c00979ccb4ccc88fc72deca043cc230aa7563da88c6c15dd28f29004d2ada9e993163d7981acfa09b1cfe69f795c148b52d169c0aa71099ee612a0c7ac967bcef2c299abe1dbfeda13ad3b8b018840fff443902162ba7246e082908cc3a8fa15e17c1726a829c67fce2520c656f1dd7c81dec80b5202058903413e480024f5984b9ffe1cbeee327fde033f3959fedee61e57c8008727ff1220125b6166b880088985aafa04dea4e344281c288b7831a0930deab27c81c447e51c32092a903befe815425f1b65a0654b701e60800864bfb36a00015b59e5a8000543608a1ff6ceeb044880035e8306f1ff9ed0f194280003876f0320003cc15e0a818bfb6cf4d2059ea7bb728823bee0a8b3a00aa08ec44a80008d167b3a000116265a27fda490228d201cb1ebe2f0802b8800f02a00026e4e0fe8160bf1114fa041829ff94e804f0cfe670a00012c7f09e7fe90d397b41ff9bdd6a2487ffa0c63e1f1ffb6f39d4cc80000c4d87420001fced31a80617dc3279204f6e35b3a48155985cdfe208ff8e36fc6⟩,
  ⟨102, 46, 0xa4000000000277677efd1a08c4421bf17aaf23afe9755ef14a5ed87e72c598025d38ae27352eba58ab9018d2dac8dc62038653d2b368d86e7fedfff0fd268fa5485f8e6f46970617946a925bb1a8364ac680000000001a2893e1052a6946cf25d7e948a5aeda1e22e8b6d349df15f28adfa49c35e3698925116a56a7ff51837f76ab7e6a95a7a29e43364115efe18b019bdc1fa665c47c71dc986a17932c20f3c2475d7b3ad6e979be1c9c89e447ef589dcd1923436fe218441575798e2991c9b89f69e580b2bd78469cdf1ded405473126b7a0512300000000008c03a57665c2909399b344299664073fe8ace1166f729e9c4445004172cf4baff23789a143f67506acf6ee452fc68b2e0fa73eca0c4bbc5f73482537a6fdf520a66e292d3482571f53d22a0ddb66aeeba822a98d0250209228380bd4803c24dcdd320756376dca07f8d815c19e9ff1bf1158fa7fbf8d83d999ff282c7f9d8800000000001ffde70f53e87ff9a03f87da040ddf1111e81a4252ece9a08456083410819aa8e95b7207a0e7e030e81010c8ece2a055a853a71c7fc7c195f3da00bba2c1d7e7fdb3bac1121fec1050f6a4800000000001ffdac414fb68010eb6de40200fa914485a81d74843d5e203d12b3f0b48266039c0149ffb13d40b127f60b7102ad9feed49236867fe5ac4bd8e200000000000803462137f5a000e3710bc6817e87dc266a03be9cf882e804f072d3ada0006aca9c9a7fe511dbf9a20000000000080268570f801fe87c15bdec8000000000020018471fe8e8027ae9817820649d8aa71480d12476399200fa1bd61ea⟩,
  ⟨103, 46, 0x29000000000065cbd00ed5d19cb58acb0dc73f9d03f16091d4beb34b5e1c4df66523712f42baa40ba248d99891f094abc045837c2779073e5d7156bdb1e5016231b70e11599ac16b982cb667fd190c07d1a000000000094c90bd22bd2525acb97b7e93e2b0881beaa33dda31c3ac7ad9a5c5002871bba05280c772bd351e22901be3f1528b4c1b090a05a698ef0e1ea2b66945b45f7269a0178c0f4b5783dbace426a0a2ecad9ab314466a4bca6d2a3b12582b3ea5d55d8e26b6d8496318b737c60b0e1a6b069a1957ea6393b1dbe6a2ff6983d9648c0000000001cff411698a473ff417f94316d0893a13aa691782736c8945baa040f626980d2e3b3814bad9a6594469ad2608c849578ca568f9669fb30d5fc79f625d046b687f3990c461520720aec777c821ea74dfcda130f866ddd682200dfa68720a1c44a2c38833b2e31440207349dc82f88005459d70ca01157a376b6803816bc8c3a000000000007ff1d16355f1fe33935b0c47ffd7f41352a041826b986e81a4a5a1371a06e54d3b6c47e732c767d8205a783422ca80e82819325a05306d6f57c7fe117905a09ff978c2f5c680035e8306f2000000000007fe596c35eb1fffa27880ce7ffcc480ce81fee59480076797fe6bd8891fe8382ab74c8212dd745d1a0087c13ee82800094de441a010356e8c3e800000000001ff54e1602bc7ff8d01117a9ffd3d956dc27ea75c6bc8a9fd3077e620680553fb6da89ff43d862b3e800000000001ffcb74bb0807ffe4c0c5772000000000007ffc0065ffe200040bcb0827f0984f3b3b1fd059f35038814e7d5020b20875333552a⟩,
  ⟨104, 45, 0x9247b08d14f4bf6f88c0499a016a7e067ccfc8a27fd4e74fdd0a936927a9ab5e64f482ba4af5948a3f40cba6d1275edb00acaaaadb5fad2c0a3479af181ca82bd33ea41268b433869fb5e02de296edaa5e1b92ff8d6d4924061693f948025d349a41cd6c9164c7d912ba974f193384661c4e66af84ac50d2dc6c7062f90ef3751613d9038ef682b7dda852fa8ce664d4db156e59a844c90d35f8f662294b6ca1040bfd4ec94b289566e3a3902f53f369e1a6a625b601cc4948d4de6cb7ae992d9a2e52c5373176d815c31a725e9ddf53c6ca393063fa39f6ca2bcdce80a5bd9dda73e4d2ad9472de5c302472da53cef997e2a3b838af2336a2c4b4cd3629bce0d3d309afb3dbe361aac677a3a81b6d66118dc48bd021ab9d399f35e7ad2b38faa0598e34a803a27a7accc08b4f67f5960207502649503e7c239ea4813376ef1104030e5459ad1feaf79c31daffec525cc837fb9825a986bff473d79f7a00160fcd64d005dde238c880601a148afc0871b28b36e079408e4e7302d88fe499e809eb83042641045721f8d5f819a0a511afe23a5e23687f04aae2a54c00d3ba456f9ff3da1e3284ffdac414fb67ffd13c40673fe15fb10c69ff27546894afefb19546f87dacf2364593eb24fa91029f0f9aa4ed6afe74562862d7fc0cd139d2bf996999196dffbaa5fa8c5000d48689f67fe4119ac41bffc2c53c80601560aedfaafe90e1d2029809fa342b25c02474142dedffd74da0fa5000a171deda80062142a023ffbc4942f8a001cf2d530d00720604f7180535bc296140c4a0ce2c9203af01c8d4d003dae86585⟩,
  ⟨105, 45, 0x12a9f5c6c7b48b81df47f56cca208143c819e54f3c4be0ce94e55c25074006ba403ca6af8acec134681b9afced8a781f1960312c05d8bc8b8aae42f979190a6ef3988c7ca90061e27752525e75b813b531e07d6a15a25a2460c94d1d3c807b3894185777e4249e20d1a1afe4b9423439ab5070c67ad69c1cc44b45c051d9eefa7212f316d3eaac136db3008976b549bf67e5ccda260a8ec56ddd050524bd333d94e74e4b7b4c3868854e09b5dc20e6d41b64e1b8f35c03435de1b3bc59bc81f4d01d8a552f2cb3d20b4b8734c9cb7034da72dad72776c658848cd7423580b0c49e0e7f76aa577073f9586e0dc2e00a0fa4025987eb4b17ca9a663b7aef368fe7e7948028e321c1fb89b227e28ed2ab3dc31c31d76d2ab2101dac03876fadfb9f57daf17900fc8743edc1e7f9c15b662ac0976119d556050603ff725059672623b0811c5b7daf640daab160d82006b74e74cb0002406cf4580a166f15f5c02f357f9701ffbb0bc48290000b9d3d867fc33ac322cc07c2022d58e070b4d8fb730095c9c2d9a7f14689679840c4ed91b04600cfdd15d8b01a4edb7a088008e563ad8bfe2662f12660001c3b78190043adb79007ff989019d03fe4ea8d129600013548e70ff328a0d1097d4d586f42f3f4256aecffa0191d71c9caffa35f573317fb61daac89c000356c762600255954108fff7695b8a8800106ae9d2c0005a7b870dfe9c8525f12fe1f53c5291804f96b2e24c059fbacbb56005a7f3fe4900009621b7c802a2c2ac494004eb7f34b200012bd5761000ccde27ab802e33cdc673f15f16502820247c59e49d035916e92c5⟩,
  ⟨106, 47, 0x2a81098e237144c3833fffc98896834cd3792892bfcb5e59b7ff78246df3700372842be776386eeed00b66b5469a80ce4c4b9787402e80101d57a33f51933d2d46bf7821da6ea108e290dd49d30b6ec62e17f3955351a74b2df38a150eb75be70019e28a37b2f4f67b9a8f45dbe6e1f51fba01d6f84e3ebc08b235acf40ced31343ae9047033dc93514006882b296b81b9a7b4493a4147dbcaa6106dd1f46f2780c527152e981c166f0a149c2935405d4a806d089f7ad2a7446ddd15e9f197b22aa6c9cb78ff7387a5d23bcda8a52705fd67290295cd60f9082c973004e26879b2300b929a31228982cd43a260ecdf2f1d3b437ca478e27650a9d2811cc3f782ed9bb5bb1aa89fdbbae68514017856f86722d3cd8debe447288d9c5aba50d61db372edadf58d6f5fed9652feffedeffa8369f973307138e408228d910c281c0626a4d070420db28302e0c9ba31f4a341d64be38f0081689189e059034d5ba7e052010ca8bde85c0487c9e19b9800591360637004c49c86699fe639f088193fe8e855d030800084ddbfdb00bb68e6f7b600f0b4fbbf3c0d71f7135027ef4bdba2f3903635475bd6e03ca344c541c09855e9ca18801f8b380f870000ac3443f20001e60af05400fa914485a7fdcb29000ecffbec6551be1ff994506884c0003e35a9167e381dc77a9501856fabd0da06b6e0fa2bdc011c797fc0b800097e5ebaeffb9cf7d62660014c74501b3ffa65371a2e7ff0cf2594f2ffef1cd8a69df8bf8dd271bbf58d008e74b803bdfb2c9f30000d0f56415ffcad3d97093fff48d9000680024d28f5810008439d684a00014e0128940004835a63f8042ec2a4e7d01de901c25020402dea79a940d82ff4a9b3⟩,
  ⟨107, 49, 0x6594a0368cd024d382b5c18450c735a7121f685e7c1dca20b462354fb59a81d0b62c446ed0e88dc30237487a736a86a6eb34339d2acd2e1469679e673e0d21a8c4abbf0552f423bc552354610f455b5149fe33ac1c98d2efa456fb505154abbe803e3a661dfef44c1d25e2d316bc0ea1f9661d7cc8b120ff5e4144597cdcb5e05227dcf361a93130869d5acc0c99ab5615f90646a90d0850902678f8f2825c91aea3d72d9449a2529cdf87646c6adfea976267e09848cd791b361c8336a899e0bbea94be46aacb8d16702683bfe133b491ab3c36c516899fbaf6878de46b234be39d8266c73f16bae919f631b7f22c92945e8b045043205220b1b52191fe3bd9bc0f31a2b689f4479bc607ae7ba3742027de3841c688cfdf1f10d363a0b9cb94757496d855c235851fc4b6cc1d5eeb88c6b88d41d9b70b0a07e771155b8324037af33fa1e20416108624b903f04c92603c818d5c027a9e41e43daaae3b205d50321653903c77f9504408152157e6e4a40d5aa3958e72019158405649006311d2d42c8032a7efaaf4401ed0156e691ff74c61372d1005dd66585bc801c12f1d16e40aa28a6b459204d85db8bc6903c746fbafac8144d524df8c40f55d52855f201b087d83c6101ed6bec17c88066ec78b47c3ffaa1366fd1a00c5fdb67a690075d210f5787f2ffcd7b1123fed6791b22c9ff53561bd0bcff1c0ee3bd4a7c6c8103fa483ff34afc789e1f589ab4e9b1100ee6e66126080319ba6db26400264482f2e200b89497a158ffce9166be607fcaeec335603ff50fb762ba1f9806e2e3d70fd8d4c5d472480b12958fa1440075d0749ab20088ae20c5d0ffe658efb1507fcc50ade7e43fe465f17600200c20d305359006385459a1c806b04036b5e40b2237353e720435f5376a0903c7f5c6d5a8⟩,
  ⟨108, 47, 0xcb600208d3d1c8ff660e914294f7183a6ed462cfe9a48828b7b5752a74d314f9191ede1a29be00537c34a7979a5a1474e23383675ca2e03407fde091cae85c71a295dfb75af502518f43ec328a656ba02fe009431929c69a2994dfde826823ebf9504008d5150cdba091a7e236990ac34c69f1e19ec91c199af2e111fe86b8dbe1236f3da5c01a4cb4aefb44ecb49a178de7e1368bd2e77582d42a15f3a604dc5f2ef527cb58db27404793778d194c532d4cebf0fc7e4db6b4dc2978b4d458235e81369607d61632d583fb204084da94172ea5cb538a0f83a592f7d32b49242d28c417e1b24d4bf081aaf0a61b3ea6b7891951324230923376406383e39e0fd612b2074a1c9f0c010bc368ac7e321aa5153219062a52ebabc0a46b6a81572918aa757577a321ad55c17922a2ab079dc1bc0832fb9cab488f878eb1f20a1f9b84efe9dc3f95ad9c3c0083bc6696c3e90b1b64e808f20e2f942646442853fc0120c8158c98735690933fac0a7f205a577da2764059f46c5bbc804293414cd9017f3a2591d200f830bbde64053e1b0d38880b408d1b28907d7f10418720c736b207b44282aa48dc0c8247455915790a29b5f38ed1fa49287a6443f7cb2b6489c816f8122c82100663cabd42a02cf53ddb94403d12b3f0b47fd070556e98feb24fa91029fe84ad5d9ff40615beaf4367f9a57e3c4f0f579aa3675b1ec34aa53e643e6f0b20325c804e0e2652d0fecd79f9690201c887850a44045eb62965480cb7587e59101678f4c55f202c4e1675723f33bc59ea188250e9bc4409016733aa3ad202a708236883fe5ba44bb307e12b4d0e7d100634086d47202a6f9a3c3e405f0dd1d07881c88c0db191080d0a5e1002085d3efc8184282efd55518⟩,
  ⟨109, 49, 0x19186a903fb489bf02b207fb658f88bae01a724afbf54be23f0c4574b4ca6985bbea188b30c626a94c9a6b9d3eda8bd3c9cea5cacaaf1e27b331fc1b7d6b45b8086d174147cd0bbd8af8d272e8edb83852b5e358272434c0c8cf4f90148f5754ae220d2e05562d3e851ac5282b45c3a7747ce4b919d38350a3caccea4556d5652a86f9b539f2ab437bfa78fe79a1a99b1603e75191fa98529fc9a0355c6eba446bf0cabf382268eedf36a3b91b4235064eac9a7d269896f446dcadaa07f3269872441f8091b24de0e38989a76549b4a5646c0555428b82699b350035791b0b885c85009a53a861592646c832dd83be268272c2fd0b11a4e32846c0892d65c38e3e34323df13b196a195795a60e84f4e9f2a4314a7a30ad6f8215376b2fb1f9f99d49c5f8eaaf0d413979fb13075f6a0aac530364d1b7061091dddf0985baf0d6715c7cc92880354c4f0d88407856d3e74820291297bb8d904a045b633ec81b95adbc702413e937664fd206846a4a79b104771ca10960817e1871a4a04101a6c0f462202403dff90e1008f0e622b3280190ac9f391402421588673a015d1893ea150045bbfb1cc2804797913d3d40d6250f61a8205b3576948510477246d966880e308dfc562411fc46d973a1f656f99e5388fd54b406dd948092e8bab8144002736efd2c6011df705459d009980e7005280425bae8ba33fe1f3549dad600191d71c9cb00d6dc1f457b7d626ad3a6c43f61a5529f32203f1721bf8a900fd296957e48044fc341c293ff7f99f90bea00aff5a45a050079c16d4f3e802149ef9ce14023c04b380f9fd675cf61ed8fbddac6dbf0880f88eeb2e4f4012c326f533a01014b1dd52cff3449c4117a7fa5b238f7813fe7a6c8e972a00f664b9c1ed00981aa3bd3a80bf6d3393ba40de21dceee5204e5e7c061a90477da82de18⟩,
  ⟨110, 47, 0x32db11eefcd8754e221bf780b23742574519c3f098eb06c28b5159280dbc5cfed9178818b004316b8fb2f856ae40309a8a28d83a2b3520bc8662d2752300a892e2a14795e480b09f8523163642bfda64efbe02e0d6550ed68a9d5f81dd940b9d772eb37e294b724bbc0c45a254a380f8e5b20781e069c129756dcd537e84cf9ea168cfb63780bed187148e396fa320c30b5f4b4c9dc57e4638b23156cc49793422dc6c2402ca8964301be4d2bb06d880cb8742e085f613a617d6ca2e2dabcac7d2004f6318f2ab58b446d6a8e599342cd9fdca62cbdfcf5cd0c4d10789a8d9cb2d1921fd6893341ad68d2c2c8f7fd950124a910bf4c73ca2bd1afa277517247a87291a2eda995f5ef3a73c04d884a74de84aa1234b9818a6c7f29a58dfcafb3429dc131403f46a384aa95000a5a37ee45191b659bbd8c92417bfa1847747891df6e0e8104c3701101a208e37d05c224165529d17f88287e5bc9011064957fe0961fc0e1e98ba63f115dbc6cfc7df8515e12a8e83a91388ea1f7a6fdd8e3e40086d99f53a7fcf65bd3b3cff7b3f8821da01c7c0a21b74013e53c165a8019d3b92d2d0306171d950207d46cd033841514bb03d7481f4bde7d7c90559e4d1c3c1f488abf35cc3b7abb63479080078b9a25090019c43a36b6005504762253ffb13d40b128010f827dd04ff9d158a18b5ffd1afab998c011c797fc0b81dcdccc24c0f9bc2c80c97207e94b4abf23fb88fbc5a447f42b1b9c74cff6cf8418f89ff40114a137400b310469ce8016e4f8ce7d003397f7c14a06cbe1b9c023fb221dc04347ef2aca97445003320a0496a004e7548dbf3ffa9738887a7fca463e7b6cff568f4801ca00573b109f9400d20235e4e80940df773e10345d211f0a206209fe7d484150ff0e6a54⟩,
  ⟨111, 46, 0x2af55ed680a4c22c80ac332b88f942f6be6b16859b55763867bd75d280a4012e13f15e2bfe4c2d6238ad1bba936965e07b087dca69f31bfc68a9a7ff77f683a7564b7b8d9a553c381c811a2b4e8c98a1a152b014a655633f2cfe4925958237a0620025155adff5a1817cc5b013a4457758c5c39d002f603cdc72c5416e41d9ca63aa3d1b68c977c227b7a3014c2220708c40c752e1926322fa0ab3ab5657f8b4b62678058ebbf8b2443df110826941b8834fcb2c26cc6369a695712f0be2b2673c0f1e02682613d13a4b261dbd0e81267917c718dab293c4fb317a5db77b783bab1058a7416324dd27ea921cb1d9cd574dea51f53852c2ea2a3371338322da2a0a848e8b1eecf21cf9d4cb09b33ca74e06322fbb9710924d58546931836fd869688e3b141326a0421f0474155c859d224879673645e9b9f7270bcd86a791cdf65043a081bdcdfbf08206bf8afc8212c687b2df48255c52a290a0b01d0e4236822549699ef208f5124a5a081df37dd5471c1f14bb5ac07c89bc4cf2a9ff3520d6ba87ef915cc61d1fb1e899f94e80028103ed8a00beaf1f89a800d17eb09b2047bc2e962e81c3007c0d4a08f95a1d2187f68b69bead1f71762d39ee7d5257a54ef9f069ad8a2188008e9e3334a00bb901a13580008d167b39fd82dc40ab6800094de4419ff819a273a57fdb0ed5644e0004bf2f5d7818cdd36d932027071329688227e1a0e149fa158dce3a67fc40c817c81feffc743dbc7fe7a808270a003086af05a8007f91745620003855cce48161a4c67e0a01998f3ca1a7f187d98d7d1fff5944bb5c7fda73d0f049ff7012eaf8a7fbc9e236f59ffcc765510a8028a693fd1a000c5975a788033acd7018204fb13fbc78813ee28c9db208f977d40ae⟩,
  ⟨112, 46, 0xab9b939b6a928d70e9762b4c159ec11f2fb8dc0d932fb6b1692ccd9ec389f9ab32e80a41b26c7ca762f9a80533ad8b82ef6c727e5d400ff6e2a6908753b3dd9a005a93523273fb93e69ccd42dd4029a8e226ff915f2b146186b78cfa2db3576fcbb95ff0680312c3aeec34d859163892ce9b4a452d9ecd72f9cee85fad138733c87bd2b19ca8b3ce8d968c9722cf63ba30cfc2ee09c8ddf8d2e6d82623eaeeffa2b44d32d774026858eed5aa0b2995f13808268931d71408b20a2f7aa86a6954d42cbc6b2b3693b85225a49773975caf8f953ac082605717df6f6af864f4c499a4d03f48540aa837c5b31742470f78a3dd4a9885d37177a453c23ade7ea21b40f3cd922932ffe3b768aaf907978a9d25a225a04e7458e9e92de98416e0ce3386930b5fdfe597d331e2ebb66b03cc242101647e987006078d03573b669df69fcd21da767545572aba0a3ea88e5a88212bf36713220f330cc8148500fdb1031a14950075dd6828df8e8e772111c5c211fc822675d3e381ecaaaad7e9c7ffb648f0de9ffdd4a37d348002dba669c1ffda3b0240680220a2325ba015b5bf86ee805d8ed0ad5204767a9d5b680fc8785d92a02b6d143bfc80b8aaa031a2066a5fffd6e7fc71921c1e9fb28564c9887fdc1b4b6b89ffde403a737800045899689feed49236868040d5ba30f9fe65a66465b8000356c7625fee73df589980264482f2e1fb35e7e5a407f7f99f90be9fdb3e1063e27fbff1d0f6f1feaa11164087f7e36657a1a018278bc28a7ff79441f361fe69294f5f081608617329a0163e385bba804edff3e0320000f49817480025253d0a9ffdd42d86567fef303de399ffff8bc3a3e80084deaca8a0004380230480616198b18204f613a47f4803c77ac2d0208ff4a54fda⟩,
  ⟨113, 46, 0x2a8000000000a2c729cdf0ba7e565e372aebbdc840eafdb88d5be791d6b164b3ce28e385e8010602ca3c9eb7139ea2ad32e751c08b0a93e753ba5ca00c9a3c8680000000001a9cdcfdba58749d85b38be948fcc63149e27440cd6e27145cac5d721233333bd34a49802eff46f183fec729767716e2d0f64b4a3f3d692a5cc9cdab5b99ffe714f3acbfda1c54bea8d9088c0000000002318232ce6128d3316f2b70a6276cb25726b6cffdc0bd2267516142e20b22fb8714fa2687e508b700b2a6d2a0987a6871f453faaaf6d004149325c29d0f1d98b194508daf726711f81d76aac56814044fa53bdbc74d92a97b93caa71245eb5f8dfd8acca4212de1a4d655cd9d16a32eeb4672ba2e3884ed0cc8ba486111b41d000000000073f99b734c0178397c00fba69211532d2d9697dd89979a6a119e3d5a2179bbf70661c7ee2f5080b8a0978b19d87e81e67ee25e8a08cb268e78882360978976209d43b21d0481a2d931010a0ac9480583a822980aaf3d1fe651350d80818d8f94fd11f900ed9cee07ffb3f5c9e2a001754d9d7a7ffaa91e80d9ffa612caa88800000000001ffc0433dde88055261a383a03e0ca642d2817b2cffb4da078f833c0047defac0af5f1ebb7ca314367ccb9344cee9f0d068aeb207fe382de7f79fff05b8099a7fda490228d1ff96b12f638800000000001ffdd52fd4628004ab2a821200298e8a0368171292f42b203910f0a148815feb48b409fe80229426e7fe7a8082709fdf8d995e867fa5c23e6b42000000000007ff93e865059fffac6b6dc68164f19accc9f7b3c6643667fcd9a7ac5e9ffd499bf71a800000000002000000000007ff7191d4471fff4ae3645c80000000000200211fea0ce805d829b216205bd4bda1288120ed81c3020586170c312⟩,
  ⟨114, 46, 0xaa00000000018afc13a35b466e9477773b99f837aad5aa4e432dbe7b78892a1f7665e5224afe088f0a834b7ff13c5e2b3242e789d45d294216874fc01519ea9a00000000009587725c83e25352d26d0c88a2d1201fb6aa6eb668958accac96b73c42a6e66747cf6b4e115d2abfa6b33819c40cb9ad0c7ecd92679adf070dab61e47a7f36a30e848d8b428cefab53bd52300000000007262e7b4f121ce2392ff8b6726072a556a989cc465cf263ef758e1ecb19326645bd744a1aed84fa318b3041585645371b6cef1c9a9457e3b3ca529560103701a9829d9d0f0529f91b3aba1a8f93dd2a9252f3b15e0a39a7fdbaf20ce535e29fbb081ab97af482d852552ce11079a50f67fffba5cefc0fe7bc9d208f3d7de07400000000022eb2e7caf9c8bfe63067a62835b8af1a5e983fffa884dac326aec468a97f3e8cb520212f8dda47748253db7c59ca1f8f1f52b32824c56996989e459757bd8880169dbcf6e206738aee35882185b54034a16ae22708e284b785026ce22c66d4a964c81daa3cef96206a5087cb5880632a3584ba002bd63494e803627cc0d0a000000000007fe6fd6a6c020012abadf947f7a4fb465f9f79bcb91d727d240a2b0b99fe94cd2e4288136a6a1119205f111303d680b9653e7a8a049c2bbc9447ff03e435a59ffecc9fb97e8072c7af8bc2000000000007fd538580af2000d48689f67ffdda56e2a1ffa65371a2e7f3a459af982045eb62965481e705b53cfa00b310469ce800c21abc16a018278bc28a800000000001ffab75c52787ffa26ee93d9ffe3744bbd67e5b229623ea0394856465a804e98e13fba000606a099e800000000001ff96b12f6388062437bc572000000000007fff2c5202e20002341ae927f6747b74781f90ee5159c47f3c468c2b92055ee4144de⟩,
  ⟨115, 46, 0x2a7acd669104a01a474b6c499ff8dd94536686958a09161a017de807a04c6747d39f7887089b11fe652a04f0b7b30b254d1e11b86029de9f4af5d245216b54576ae4bd8a27db1cc9d23526946740e9313a534b128fae28940715382fe9cfdbf36432cedd3ae96d926b5446c5f76b463c02af4ba69c90b20584b681b7ac3e3268202de6c06b177dda6b3ea30785d6d8248c08a902ed5a3061cf9a6be7364ad67fe89cfcdd5474c07394a55029818299d0618aa42fca8358df182be0d77f144ddfcad43711a17b8e7840c51b831da9899a67a61fa27e51fe63c65df1af9b7bc7af851c2028a2831a6545fe2ed652f52948f289a7fdac49ab25219c87eb201a6a1a97958451c4fc0c2819a3e53318d465c04c7b59931d051c0bdab67484f09fdc6a2bea88391ae8bacd4cfd1ca900d7dff8dc990b9402e4aab5dc2880b6292fe52c59102085f8a85a608233e1661faa1594db972e681adcb753c29c6a898733ac8185591578220a50f08761882b0ee81602a0cb299f03b688f3df0f8a921db844a4d3481bbe6f8ff0205eb127af1c80080b9aaa3a0046c058b8080046b62304200e1a4ff33a7f83b9617b9a000b97a672e800246124711f940ff353d67e82a4cb538a08da0ca53b0810377d9b0c20daa336932a8179e6876b1a088f0d23b008035b8031279ff9b9bfd977802b8800f02a00d1884dfd67ff8d01117a9ffc82335883800083574e95ff86792ca797e577619ab02065bac3f2c8810a4f7ce70a00b727c673e8007f9174561ffde5107cd87ff93e865059ffe89bba4f68004f972abe1fffb8ea96b47e9632831c1a04297cf829a8051a6b61231ffd544e9b407ffcf2c98469ffba5075c6280079a7c1f69fff271f97867ffe6bb27d7a0013c6f16287fa048033f01faf551f620880a0916ca15207752de39de⟩,
  ⟨116, 46, 0xabd2fe776f128568ee3fe849c61d56881099f716bd625a686dc29e24419ff392572184d446b449a0889d26fb0f8e53951d4adb60bf2ea9980d45ce87a878d9dd85e14ed2a7774191541c75ad173cad0a694ca1d34b7da520ac6df71a8894110dbfc69fcf00aa00abf9450a9edb2655c4e163beb33ab46ceeba675a421c73cb2ad8fdeb0d2674c52e72d6b122566381fa3016a80d5bc8c38de05a0ea3239c670afe73e64cf7ce59d001571c66474007c3a54419004a0c71124b2a2fcbcb5194a490fee48523e15b00a51a3fb8cad8f452c059c32919a956fcbc2de526655eb8811a8907cca4945a06d1b2a8b1a964f6a563257302e92b619a7bb701abf2526d662d77a1a81cbc7f8d051dc98675a59a4ca9e936c25c026f57aab1d3d333330da75cbea82d2ca280cfe0e0b28a9575908b3a900529aaeb8986b4bda8d9aa850bfdc0a6979f16f11e520a42c6d5b4881eec89655ea0a4e9ffcdfa81185821c209e0920f589e0808b3b66234209994a25ed08255c3518cea0c42c6270ba8883ef7330e2241d9a1b7e081e1a4ebe75207353dae050800a5241f33a003636286c880080fb5b1f1ffc082557ca7f7cd142d91a0001a92e2a68000b57e10a1e601020c43a7c2f01f63a79fe39f0c85707c32394c580208f865793328150432da83a0658a81b7408009f5b726ca0001bc8b8d580009b9383fa000e3710bc67ff4f655b709fff0b14f20180005a7b870dffbc73629a77f50fb762ba2059e3d3157c823c04b380fa00ce5fdf0528000e1573391fe69294f5f07ffeb1adb719ffe3744bbd67ffee3aa5ad1ffe182a3f987e665ce093ea0419d425fe2804fab82e201ff7b08ec76880004b65ffba0001064951a800b57d5a67a000140b5dda7fffd542fb3a0008054bb6c8061e928b4e204fb26efe84815708f2fd3208fefb81daa⟩,
  ⟨117, 48, 0xfb11a9061fb0985a712588329925ef9e467a9861de60c48e683ed1a5b8d6686cadaf16626844615f635e50e3aa64ce8c242b53bf0a0857010f8026fc231079e95a985d63ea5bf9df77360f83322977fc443491596e9a53507d928c576516ce828c583d00dcf6879ef31c6d6198b8835d2e8cb31497941f409e48e9b07340b61c49ac5c649af2f5d8a494b39e738da9389a72e7c52f3cb27d78b7da0c8c58799bdcbe8c9bf50dd6368c7adf644052744bc0fb31d274565c3ffc9e745842f2d8f66355b11142f8532b6fb124086a8e8c3445cc539c4e67eb346ad497c05b1855a90d71cff06b051b7dbc54550bfb8c66706bf8f90d471c536d927102446a9452703f2853f263d568e06a9e26de38e853cc269b03206ab3362982bc53385e31092c69e095c7f0545d08532c4df6745eb9306d6e746a06a5a7728c42ec5ddea68c446d233286a24cdcae2682965ff61fda78a3fd6f74be84841d3c11b3148846680fd95482b1018c418c83f263c0ca187d7b5cbbe97083627d854f0c82b5a611ab6c83c5144b42a483051b925b1c8554b818275482d4a522c094839c1ec67be4828e8d2167c8832b70372c1c80b2e7ed7a78805842d3eaca8059383019d6805f2c23106e8043b14e5ace804cbdde1dd28058639e89767d76f859da5c7d3832ab3a348376d7528eac819fc8386b4483aa3cbacc2881fe0b186fd082f4c2fc7db080b83c40f2807fd5be90baed80582fc4453e805fa1f7099a7fa9d71af22a800ab0576fd57ff4e4292f897f17f1ba4e377cc037171eb880589c2ceae47eb3ae7b0f6c80d97c373804805869319f8280582185cca680593c66b3327f96c8a588fa7fa58ca0c7067f99973824fa805cc34ba0fc8121f6e89274814d96e42eda800aa484d22a80026fc8ca2280596751d9ce802eb867b18a7fef9ecf7ea280569bb8356280591cebbfa280ec0df67428829d50089518800ebd3912e880a475e4a534⟩,
  ⟨118, 47, 0x32a0cc2784d478b23a769af098834b7cbf053236b9603bda61f4b204a07343fd8ed41be6a7d91a6cb4cd1082dc2eb1944e5ea2f5a81224130aec185283c55c7ba047402d2d55f174c167b0137bb8e80f698b177be455343aae09b96a3669a320443bd0d74641cae733ae87b7eeb1b8133222b9fb45b2ce91e8e633c4d2cd919d60cb45594f89eb1359369511cf2d121f4950d04d6401d77f3cb328b60b13d919066e72268a320fe11b49946289e262d0a741397a3cf84e90667bd4d69d340a34672f32f66bd5e5b053d73c759370d5c89bc511b1511cf6818b235951e962cdc54ca66e2f5d0d6b5834d7f9151c1881890e3585dd0c58405411097bde90d5d2a9b780415276c02fc5a3570b5a386fc547773164798d4fb80ac75914f8ea7d8a1a351b1f011a405d88cdff5b2ce91a56742b29d110382c24946225f768a628c85e941e6154b1199cb17aa415ab8629e85301bc8e92f883090cf9261108eee42fed420bcf36a30b4424ed82f3644790302ce559902f4e90bfb02077a523613442382ffa71c0835ac1cffd590994cdfce8620ca8f51f6064223996e12d882e432cb42c107ad78744f62041eea1dbbe402186f901ba80839a0edc85005836ab46ea0173e22ca634044623c1d72808336e698250105adfe13d1fac9cafdd72422429d17ba882c9b5b49ea108ab119ded72096650bcc9241be3921703c810de3ee4f00ffc91865b746020c14ffca7403be9cf882e7fa60efcc40cffa4387480a5ff0fa9e2948bf58d008e74b7b1a98ba8e48fccef167a861deed636df843fb221dc0434803331e794350058f8e16ee9fbd9e3321b340394856465a80852f9f0535010675097f8a090fb74493a410592d2154081d6664940a50105fcff523a014dbf22b073f92c9af57b28003503af2c4fe74b985955a01b913113c94040be8fe73e8166eb24b08106884c6cfaf1f7e18c34f9c3f346ff441b4⟩,
  ⟨119, 48, 0xd31498c1818ca4f187e2c53ec9597ac426b291c775e8628492178fe17e1490f5a4ad5d626ecfc417367e6e968a4a6a246e8b4591c1a85c9c055676223ffdccf9d5ee641a17b8833c3a33539c81d470a65309e0057a80b633a8dd7a436cd8b9577488265acf72891816253c828984e9086746853954c9ef8392bca9d1f3a6a5a2ae528be49327b0c255baa8b435b7f56a937a492d4424a8a0201ac8a09379628bb056a524a428226a89140857e3e48913be7767d6891f98bdba2a770e3bca71aa771538a6000c771478f235006e28cf6cf8965db4116dffa46f8ed243bfc45dff67239cd46fc2be5ecc885f0969839bce6fe711d3d1ae636081da7bcc701edb64f6005dde2ee679d06f91f9a94d5e5e3c44f52c9a6f99da992f825e1f971567946fa9a5def5e05db0cc49c1e26f0bad245ec6653b192b749c771560d1a4627726afb9941288fd6890554e8913dbc952be9b3b40bb6e00930bb60098b681ff5664052a82f1bf3be204837cb9dc164c8199da5ec2f6823c447294527bb106bc44ca81d2b99e18a0818a0eb96940821a4913ff5481e9dc6bb556825e2a17e7ca81c302f17ef881fbbcb414147f532a4e37dc8058efdd2ba8802947a81d667f9f210e8384800ed13b65ac7fe9f01aaffe800c689d0e6a801502e64aea8013eae3c18c81248d10ffca8162b24bfb9681fc4017da54817a48997ce0820627f1fa4a7f7fec59f1d67f751e7d32487f6271efdfde800a004cf02b8013c33f99c28013c1cb4eb680154fedb6a28013f468564b8009f2d65c49801defd964f9816252b1f428812874de220481f11dd65c9e7f795654ba227fc61f6635f48013b7fcf80c7ff3669eb17a8013a6384fee801469ad848c8013eae0b880814d96e42eda80eb3324a0528072f85f73b88013bd99e3787ff6739918ae8011fb736946800b3037239a7faf5657dc1e801413828a4a801483369c387fc49235f464813c7795976c812743d2a0b481fbce09a822⟩,
  ⟨120, 46, 0xa5492d892cf3658d80ff5ecb105f8f84f2b85590df3cbe98017d501cc25fdbf3bf95c94bed9be6209a5a6259a77e680038f5c531a04c012b07851d708598cd8c8b2768298a603a6b7299b0df1fac12d6468a29f6efd55e5a5bcd6ab978effb1d1acdc87fa0428168be21ad3082a3003f2d20e2861a9c852cde5fe32ab995ab0fb455df8e264763621a36b1b2610bd3aa66319c40dfcb0228eea14e26709f203726aec0ae1d0bba2d79ad2f7e48ad9efd0f6ea2dbbb5c2026744efc9bd079d0188d8f214741850da7e51a1068c16d9a51cc8b364ed1a77b26f464452501dff26d1a8930a5765452a01d89dc59a9551a6d99257eb8f83cff1a2e40f1e8d44ea10816f931a4165d9eec65036f889c6f9a7b950cbc5651c26f150211a80d87b08bc51d900802df9a4c31c49f365a9754e12a71d05dce79b0a74092e8a444a30618a02efa8c615acbb68a9101cf0e0f8993350d3159a2ac0cdfef9681def89b9192092ed2c7ea47d771327c079f124d8f8b868126b68313ba12633c6121882f9a96a47021fbb11d529c832f6749f60a1592f2bc7da86f727e9bee214126919444828bd9e145820a9f6cf2c3080024c5f527a0001778172c800894b592c20014db8b2fa7ff4e8d84059ffe3f3b3a3e800cf31cd7c20483611b31a80bd71bea09a053bf7512f87d2bd68977c208e2eea2cb6813dcaad1c7a031b5aa942880086d1a15ba00438fa90d780004b1fc27a0006aca9c9a7fd0f618acfa0091d050b7b8059fbacbb56000343d59058075d0749ab2059ccea8eb4812c326f533a00cc828125a7ffd6512ed720000f4981747ff5266fdc6a000606a099e7ff5513a6d01ff7b08ec768802a921348aa0417f3fd48e804ef6678de200010c71b047ffe7f30b039fff0872be167fda6bc41e69ff9ab4f36ba800d8566dc1a0005768e5e4806170950fb204f729671c081558b2108d20995b33934a⟩,
  ⟨121, 46, 0x2900000000009e7c108525cb58c7d344c72b11732a709cb809fe1616aa97f5f28e8eba5fffe142316954710d46611a000000000068723f54cac9a5b8ceed96a5271381e3348f8646f78a225cb52cbafcf0cd92074efe86759c0a4c1c9e385a5d1c7478ddf9edee69c522ebecd848c00000000022ffe94ce7d0876af6bfceda61e07dea8dab1fbccfcb40265c5d85ab06b2f4d7ba6daa669731374ecae84544c27d26713b077756b0f1606000fa2bb4ce46ff28c009ae2f6d230000000000740000000001cfd337357aa73ffc054bab99ffb1c00d5a51c3444fa5e1a7656e697d8524caea758f1a8c45f6d67852bde7fd9349a9505c07d1e527b0c854d71a835e07aa6c5101b12ab291a5ffb0558924fc887e7ca89a778edf86d252134c373311a712933c218515869c34ca9a48f06fd7465bf745b43349cfef7f82f6c740000000002300000000008bffce6740329cabc29100697a476e39f0a2cd9a67bfaa8272821415120f042404c587a9652598089c599c56768681f5674b0d5a0fd5c64664482212465fef22daad4cb174859c4e4ed7fa10a420decfa8512e70bfb321337bed4ba481f16cddb6c207418776ce07fdf0d0b00d9ff97220595a8007bb133dfa00000000000800000000001ffe6fcd9ee07ffa57e5ad1a0400f37390a8116ebd5e26a088004e7f40816805a78b721684c685af6812a1a61e07a0573181e9fc7fd1378d0da9ffddff296967fe90d397b41ff94476fe68800000000001ffeba6d07d2800b4fe7fc91ff95a7b2e1281115c418ba2054e1046d108202963baa5a009cea91b7e7fda73d0f04a0009494f42a800000000002000000000007ffcf2c9846a00012d97fee8009bf23288a029b7e4560e7fd9ce6462b9fff9fcc2c0e800000000002000000000007ff9720040920000000000080000000000200055c972028062bb7c1d6205319ac5b708155e009e0920911ed77ea2⟩,
  ⟨122, 46, 0xa400000000019f3bc4962446800268caa78e1761b7e68253a521f1c158e0d5f7ad59a6a42b0fca9899fe1a413bb66800000000024a56137912c8c3d184847da30ffa8b3f169e23f18cc95afb0ca6a08969d45d3c8ab72e29de36fa289200488be97a18004f08eb885f90bade02a3000000000073fd4da6cd81d07ad016c507a023c6765b9a4e8152045e5188b393fe31a4db20fa2065362b5ae4e79aa1cb9756f8522641b62471a6ef47e758a511965327cf9d00a9b5edb27401564b6331d00000000008bf0686d2b922fed562e3fa8c0dad97819a6474e6b120eb611e03054e265e504bff30b0f2b4faf7e264089953784b12c8767b88a5acea21257ab248dfc6bc425cc6d99acecb0fd2f4ae592661539abac2b2c2c405984a61cad03a512b0d58d13b3025d3896bcb6cb1e2bb2bb13a63bdd425ca2a4077c4761ea2feecebc6988c0000000001cff17679f5873e318af27116fe34bdce1a7013174933198ec5eb155be71ece9cc16d20c748b6171c81a0b5df3b19fde1514a3467e4b891136b9e0274ae9cdc7a1d4dd220c1c470f5a8b407873b3d863f9cc830b7ec067613dea77c31be9a1bcbdec7823195cdec1fde04a356487fedcb30ef19ffb164a63f27fe75cb1414a000000000007ffec38df411ff92a775f6080021ab07f6a049fbaab212814fc80f4b99fe0c5d49a848029004c135200006ae9d4a7e281b0b46e9f056786eb7c7f601d30e34a0000b2d558a7fe6f75a8922000000000007ff2dd2ec202000a171deda800025886df1fff48d900067f9963bec541fe5ba44bb307cd1271045e9ffa9738887a7fdc04babe29ffdd42d8656800000000001ff96b12f6387fee941d718a0001064951a81659d476739f92c9af57b28047edcda519fff0872be16800000000001fd8dc22683c7ffc68706cd2000000000007ffd78578791ffff76cd5c68048e1084ba204f54ece0d07fcd789f7fe1f0bea089bca⟩,
  ⟨123, 46, 0x27849628a3a898027c7635019ff971eb7b4680058ad4728f048102cd9a5683f537ef98dac01f24f266a0d678b4229a0225c54c5a6bd989ff5d62352ccb6924c8cd08e61e71a357407489469f1a8b532ddafcaad26402a9d87004bb052cc70aeec4a492ce4dde85a218850c469fa865260f5fc02318250ec0a8748f273d4e61cfaf40571c479fad12e3001a21a1f0d2ca5153a11850b1a7bd0544dba524acd541289a24220b5e68521c1811f5e1a67c8b04042510ad2544c79cf7f491f31674051efd3541d194b7929ec8ce759f8cce22fd6143174a8c23c397676a64726b5447ab78e612d90f2677e2752058b0fef7dfbea25f7e491fc20b096b88d3aea5ea5acb4c52ad643826a90259cc8122474af7c763599625ea127e8d22ada8b5fbc0da5fcbfa743dab141d7ce758260c47c9f1f0b0b9cc37124a5f2f8ef9f2ea3d8510f8eaa303744775688c1620788761d2b04cc6cb8740ba8ef389172470b768ea70b95171f469bd8e69dc04a7f589c2ac48212678f5f4007dfdc525b859f28dcf0430a7e221f4f79b9f80fba5e2147bc8b6e0bb41ce3c029a4e8752ec5bb6ef9e236234a2427488eeaad731d2a34431fc07d3603203851feaa0b9be007ff068b4432a003d148bf927ffdf83d826a02770edfe8480c24b7afec200117f8103c803d813acbfa04637af0f067f2b267467e9f260b4f46647f309b9d1b11edb166a72d27dfd393c83d9f310551bba880135a29c6d9ffdae8aa4887ffa0c63e1f2009a15c3e007ffe4c0c5772000c428540480151615624a00126947ac07e62856f3f21f095a6873e87d2d91c7bc09fe5231f3db67fbc9e236f59ffbcc0f78e67ff7191d447201890def15c80079a7c1f6a002d5f5699e80bae19ec62a001a81d7962802cc0dc8e69ff69af1079a7ff972004091fff1a1c1b347ffed2a4b611ffeeb8d9ba480029ec66dd200232273f02805c829fe8e203e66c13f487ebbae0352c1f84a5d6c432⟩,
  ⟨124, 46, 0xa400000000026005c16137497f000ae4d51a000000000068330e45ae88f72363698a25ced85cd67a8f8df69c801e68e0a06dee89a000ee6549271462ff0b0d2300000000008c245db5324a38911c56d0e9ea157eee3bad7cd4efb9ca997752adaa72c8371fcde8c9256dacb05ba181dcd0cae0850a77df7bda2fc6e55307c740000000001cfea2434c247a00366d83199e3705d32da51093fa5b3c1cf1250d11e6521e1797c4a99ef407b4684524cd2226321a712f52a876512066f17839cff8d305eba7402880dd0d1ce19bc798b08c00000000022febce6567a8c371a68b69a6f8698b925eb16cf04d1bf26801db8fa3cb16874479cb25d47082a248afb462b34eda54cfd996c92aeea3049d3c251d26dbdd94a9f28a420a42597a176faceaa6cd1cb957a5f7635c461eaefd8aa2d0925dcc9ff1d10b12e555a3f7a642aa4285f6a3f06fe21f6a3016c9ad7b08bf065269d21d000000000073fad12efd8174e435a5af27481d6bf1879d930c6994e67aae67286282096e290b78081b08ceacf29fda663ddd2679a348426a9a0871e48a02c7b133889f7b1d8872297a707ba228a48b59ec9a52c04da76cc14038541dff68437f687c174f35da61f5af434d040800a03417579ffd5ccc862680051db90dc9fb6960c4ee0800000000001ffe89608bec8025e5a5acda042dd9163d27f73ed29d8b9f932d1a530c7c4ba09c0ed1de20774718a7e999cef52c9fb016c7d4dc7ff269d40439fff5368421e7fedbce75331fe87c15bdec800000000001ffef1250be28004eb7f34b200210e75a127e465f176002018d021b51c7e7a6c8e9729fd5a3d200727ff31d954429ffff8bc3a3e7ffd2b8d9172000000000007ffc9c7e5e1a000140b5dda7fbe7b3dfa89f9d2e6165567ebd595f7079ff9ab4f36ba800000000002000000000007ffbae366e91ffaf6671898800000000002000f15a00328062f0453eb20509aff0b1c7edf8d9761e1f9cdabb2d52⟩,
  ⟨125, 46, 0x29000000000067f955e3d6c1a25e3d7a6c06800000000025e74056676c97cf9c1020bb056a92184aaa2b2879b231ac55943518868eb16fefbdfa32439479e328c0000000001cfc211d40dc741055039359cfebc038a4e666f2ca30b4944d50815cc6692dc1b0080145908627a6470b74cb288e9ef601c7106879fa545e32d9d00000000008a20b72fb0b22b167e910b485b4800c195a5c51d53c78aa82a8b19b5e2574b7457376b2b9cfb95dda66ef85abcf0b215be66bee266b3370130eb1172691b38a30018c73ea28c0369f6b6a230000000000730ad80be621cded3456336739e5f5fe4e9a07d68e44a651aa06c40e01a7913de39ac518cddb3ac71a732d03b4e05275fe406cb9a86015a45d2522ceda09401a8584c9fd045385d20d4a81a79903e11d6562a4105cf69a74c0ae999a5313e81c0271a8de1dc7ebc51e450380089a459d4656025c078bb0b8b9d071f4231247400000000022c4bf134d708bae22fbf9728fec44df1e28327708bf02a067d6f6059e80607f9d88920a3333bc1388213e87733da22a24c3222a8bb6affb7c2a18f949c4c2883d3a5a5dac21268babf1c482a289fe358a0b0966ce536853161dfcc720931473c57081d2c5af04a206ce3280dd47ff048dc7ea9fff2a97cada80ac502f3bca000000000007fbc96af7c620018d6a1a68800774ea42da04a7bc3bfda81ca8c4fbe1a0914ca45ef481c7a63a61a20aab3696cda81423fff43ea08febc1054880077ffb3609ffb436d79ce80000c4d8742000000000007ffc0065ffe2000e796a9868000257aaec200029c0251281841a60a6b2054df34787c81ecc97383da00ae76213f28028a693fd1a002137ab2a2800000000001fffcb1480b87ffe6bb27d79ffff550bece815a6ee0d58a0372262279280504e0a292a0036159b706800000000001fff5e15e1e480029ec66dd2000000000007ffdbc7c4081ffff962981e7fa44278dcd201cfbc5af90811ef856a212079ad6994da⟩,
  ⟨126, 45, 0x3283bb575c297d64ef303ca4fffcce825528a88bf1e5d9404d6f08df55f38ffd248eaec96b45d7a7fe287dc9fa321047c4179dc5812a81c6a990f636cb904cc9cab364826067fdb30a4cfa95bfb31268004cb17a634007a5ae56136b919bf04445b150cbbd65213575fd48118b8672d9a17e40c29cd1eebc3a6027a77459d45c6cab41c322befaa4b8d6a2dc8d2a9917b3b8a8bf6782cf9cd5becfe4dc8b6bb675f52c15e980810b82e4e61625ca359b369a2b43391e7de5027967094c5a2fee23d127c6954c018b464982602c8c1f6ad306541d827266b6304f6c533a909e751919f6dbd55440a02bfc4dcde235493c82da29de8a85925091ef99f80d8a894bc62b0c257e1e8fbf92a4fbe3d99b8966f3c6d160a810dc843a423d462031ca29e3a759bee8a7656da1c64a854f27ae5227e09d04e1a2a527324c680901526f29f4a4cb03cf4ce3809da8112a356e625c7569a25a8515ead2db57ac6c129724f9e1439641752d42dd2140dcccda050766aea82667f2ae32791a425ec6d4e5920f6c69db84d1c86bf80d82989d01840d342f73b4a45b21064c4cdff90e1dd8c70dc850bad01b5d42c874023e6a1c36eb83aa1092ff1818b883bf26f0d2e41cc1852d2a20012a952515000bf0007e4800655f8306401a64d8f3d9fbadcea20c4fff0cc10c1e80023141a06411e87940dda0e24ed8701d098503dbe4888bb9a44c84432c8f9e9e8a0aa7caf8a5d073feae105c80123246ced4019e7756fa60003f9da6350018471fe8e800205e5841401c81813dc600199bc4f570004835a63f831c2a2cd0e417c374741e213035477a7500d20235e4e80062cbad3c40010e008c1200423fd419d0002341ae928009e378b1440020152edb20b239d77f45040be8fe73e80a419b4e1c40015da39792000ab92e404ffff76cd5c680119139f814003c56800c9ffff2c5303d0000fcb59147ffdf89979040ad231cb7720ab9d7abfd108feaa3b616⟩,
  ⟨127, 47, 0x19221e4e2bfa260c2839820a4c17ce7a7a94696f3df59a40d4e913b55fb1b7cb296b952497c619412c0927f5472d4f14b21ef1aa072659d24ad8745911443b386c8c30f31a50c91c59d1f4bf72309fbbc8a1a3a1394b1cacc7430aef214c8e861ee635dd1a25034f77b6297edc86275c69c88c74cb78a4a48d643b61b92603b86ad3db0f927fd967a2dc7ab67ace851d2a17842308abf75a9046185ecbd3a486189b12fd8530d2c5bf0142c95be9281764cda83f03710b30c702a8ed13444919387e2cbfceff38184d11b6395fd4b1df9e04c2991861e207e402319dcbdb710460b91bb836c738236f39be8e86146f48fd1cf05897595a343148e2a504528da3e83ae8d47f4d9df3714bf86cf3b963542d8edf34453814f963998d56c6c911ad14c9d21c4aa2353397565f7852c7dd1b8140d4897fa640014d526144eec3522ed28417c532e5afb5790d4c8a135f2314a6a74513a434c8d8b75a345c91facf9fe8e89fc7e54b11d0e85c5db9a45a5c9902d348bb346717af12f9c26a6c881f4853884fe4414d5196492c8264505d1cc1065cb50cfcf20930ce6ecc241aa4c4e6b9c8244c0f3cef1058fbc18261207e55b0d8ae4193a449c44082b6365d2c3107029f2c73320a16c78b188417f0da8c690823fa6f83749051b48d5a662018cbc1b7a8401868e5b5c880323b7aaa890007f6c8c271fe002b136d840168550fe3c7f46b0d276a903bf3bd2887208008bb92ec417f9ddf820482252a1f6f810618e1c847b206d422d6062412b7ba0a9e080695912b4e90031124719ca00c2fb864f24009eba605e07f84c279d9d90029ade14b0a002e33cdc6740217615273e81ac100dad790391181b63220bf6d3393ba404a06fbb9f08019d66b80c100616198b18200bb053642c3fd9d1edd1e07fd024019f810061e928b4e207606fb3a1440b3759258407f89246be8c9006170950fb200c576f83ac4012384212e8802e414ff4710062f0453eb1ff4884f1b9a3fffbf132f20809b18f0478103ff110916c1fe34cca470a3ec51d68c554⟩,
  ⟨128, 48, 0xf28ed5115608abc71a2417848c4f5aaf59c88c55d42832d86dbb5c0444f47129326b1dac74c92d0a52408c4cd71ef3488c50eab4a6cca53c82f7eb2c94549dad8254b29d503f91d88c4fa3de2ae88dbe549500688c559d2ee2a47449fe6e84e8744f6b6abdc8744fc018bbd068d18216fecc53788584d8d46a05f0fe523852c88b3606d06e778acd76ec7b41eaf5d6247ae1ffc319c8745dc39611c48c40eda94ff08c4d6e8431f48627e91ea6fc98a697562ec4b2d1610053a4980d360697a0b386d3ab7d289a61f2700204b37a022999c09a60cff715d8b25a64cf92a08c4fa1d21b848c57d996dc108c7807da027c7413fa2bf51074500409ce1c744fe684fd3868a17613f20c53086ea1ff6c6a7e7ac728f0537a7f6daf586ac326b5067c53fc169496946af3b85e451453a20f12bd006aa49151b2545342a4468b986a82224ed5d453cf5e249a586a8ca42f0f3453a9213260546aa1b3133f20531557666b4c69cf12f668a85cee0df041b0744fe4a4b4007483c61c537c8b5dffc30d188b815af7873080f1f3af290881cf4cdcec948320f23eb42482a1b3057ff083abcdda68f4828ca4e1c4a483cf6073b768828221d68cf0834784bd616082a4910cf66483ac483b8d6082f3d3b6d7508402489b68c882c38e21699c8379307bdb50827d09e1e69c83086ae3281880a090f23cfc804f81d92074804f4fcc9544807192f4f40c7fb5f55bc8a08033a8415ba88053ef0b252c825ae329dad082612f88ffcc837abcabc3bc82628ba044288387716faa0881f26ae59bd482d2e7dc09a880a6ba2fdf748027dfbfd4c4804f6e35b3a480649d8aa7147fd059f35038803128338b247fc57c5940a08077a407094082c88dcd4f9c82034297840083788773bb9480d174847c28804fb13fbc78804f613a47f4805bd4bda1287f90ee5159c47faf551f6208804fb26efe84829d5008951881a2131b3ebc813c7795976c804f729671c0805319ac5b70804f54ece0d0803e66c13f4880509aff0b1c801cfbc5af90802b48c72ddc80ffc44245b0827813237ccc81f3f0c48f08837969cfa5b0⟩,
  ⟨129, 47, 0x656b0b6031d8b3e8a7fa83792f6e2d76d8a232c103724744655aff6a984732e9746bfe0e76fbe735061d2515612c9e4648565558e08c66d34ab9114c9d1a235eb2532bd8ada8a54a8a229a0648beb3ef855a11798d03c70922d37a790c063a3b53777770745d06ae9dc8e9560af9b811a6209fe7d482a72f3e030d46abc8ddf40d8a86beadccd91bc0255f02f33d5ac36ce7de7a8b53ba53f4e94d18ea714231878285138463c40d4a0a485a64c418b1532bae4b74242cf8cb4540ac4b3bc9e59280b4f4a42f91513632879eeb42d39dbc0e47a4d8bc3a899f4b3c7d12dd2191940733dba2232ef01f31304651a46d6df873cfb7f88390e95740473cb1d3d539e994c34abf0d2ed6054761a457190d667dbe7602153993ba258835bce63e3f38556983266300d754a1b6cc41543df07349435ada4b0fad054b01119a428d671b563288154f32f3319435a1ade53cb455168ded6a50d6b0d58d6fd15246c0a83503542ec5dc6485e00336977b0e97f6252b441d2aabde503a447d281bc9bc87851a6d39a115bd214a3d621cdda75831e465e308dc5a88358844196610a2d4352bf720d0d6ef2e8e429e6a0fc4308338da6cd851096021a9d0720d6d2519dd04287be0e692883aa50db66210ad3065a85320de7320d7824273277e9a748333c21487e108ebaf358492055d2477faa40373412241080aa6e68105101410e90df91fc87dbc92e0401e2b793e8c81044b3bdef90790fa754db20c5ea9da0084273c5eccecc831943a6381109e947d5aac200d9f7b770640ea018514507ef671f1d310ffb6e416023a02ab30b9bfc4034491d8e6480a73ea810590075e0391a9a0091f16792740805bd4f3528435f5376a09042e9f7e40c213979f0186a40c413fcfa90809f71464ed9003c77ac2d020241db038603fcf11a30ae4805048b650a9015708f2fd320075e9c89743efc31869f38824e87a5416901558b2108d202abc013c123ff35e27dff87f5dd701a960fedf8d9761e2023df0ad4424055cebd5fe87f8d33291c2907cfc3123c220aaa4a8fc8642736adff5d4⟩,
  ⟨130, 47, 0x3ec0e72abd185a736ac7e740e6f7d72dae31650cb8b6a7e265599a6b9654c8db206718a66de92bc4e64cac09bb0b5b9a12bd55e04b4c8f3ecdbdfa991e5fcae29597dee1add48aab8296e12846c454c2ac01897ea97a7418d32b28349409a63fd0311891345552651b26691e4fb4b50cd23dbdaabc094a83df12d8814772480001054f7c983ae084f0db2d3d62176b9b4353e1baacc89b904974bbaf59c332d23a4ff45a2a6369461ced14c7ad646fa768b6efed0e47b610196557fb39e86df5858a59b838f67ec8e909ce8d82796b192e348f83a3c908520e85add26d97604e6b307c0afb1323da88cd1fa64d1ae3ea514c929079c5ca69240ecb1fccd289442593c9a4812791d8d29209be0d478280f16b98ff8abfd003ab360a3c0145d6d42b42a4fd3e1c29f66a9ee1c0adcca1f30c00a5097024a062b2420f5935028838677a4e0ac06c680eec0a673e80e94e2b0c00d9c37429507fc5d678ac850b73b780c4f2ccd591a2a77728344c43b5fd2c1c684d3829118e369a565bc2005b4715a7ff358e8eadea32318d3b6f8d25baaa458b83c018c4db1b4718688864284dde8c112a0fd9cca3218619c3aa5444ce96d97b98860364b3a1711109b35cb0a219210518c1844a12e4cbfc886e6511be3f913ecd47d4ee21a151f1b7624478014f805885f9330b8f31101e2617cf420901083c3a2406c88adeb32813229f19e1d025897a930ea044535ff9c3408de46a157a813e15bbbccd0d6614b6d092170327962fe447c1b70422485c435ea33a112196b88ea22138fd527d9843d0dc96e0ec79a2b12dabb8fe9da9f45986047fc71b7e3400fa1bd61ea810ea666aa55000f6ba1961601ac8b74962c0d82ff4a9b3878feb8dab510a0bbf55546223bed416f0c4150ff0e6a54811f2efa815d023fd2953f6a02c30b861894055ee4144de80eea5bc73bd023fbee076aa0523af2529a3f346ff441b483f79c13504502656cce4d2a0488f6bbf513f0bea089bca7f094bad8864fe736aecb54a03cd6b4ca6d408feaa3b6167d8a3ad18aa90de5a73e96c2139b56ffaea447c63b8b730⟩
]

def lowMatrix : Nat → Nat → Int := lowerEntry 800 lowN

private def lowC0 : List Int := [231879581]
private def lowC1 : List Int := [100338339, 150038417]
private def lowC2 : List Int := [195299047, 21552850, 248648242]
private def lowC3 : List Int := [95830183, 5429341, 79126836, 127776600]
private def lowC4 : List Int := [48057495, 5055023, 5362747, 43683379, 59470054]
private def lowC5 : List Int := [47620292, 5291540, 5775112, 43732210, 44342001, 37076714]
private def lowC6 : List Int := [-47665012, -5697139, -26692702, -25150200, -28863087, -12124534, 54340783]
private def lowC7 : List Int := [-50497229, -2231180, -12638090, -28363614, -23340032, -10320060, 18581674, 41989144]
private def lowC8 : List Int := [-44965297, -3406305, -4057866, -25752485, -32696895, -13994692, 22668584, 21221160, 51382568]
private def lowC9 : List Int := [47643258, 4970455, 5660698, 25852094, 29603397, 11370978, -21803588, -20097603, -8252269, 51326567]
private def lowC10 : List Int := [47642396, 4491847, 5759193, 24179395, 29340128, 14885270, -21128966, -20764867, -7525076, 34599003, 41757360]
private def lowC11 : List Int := [144026071, 15970508, 17217480, 9944738, 109625237, 54834954, -56426764, -70413604, -34465167, 94688429, 51753069, 123901786]
private def lowC12 : List Int := [81325559, 6563032, 7475090, 21537618, 50816353, 13059507, -26359870, -59186529, -34870672, 50343379, 20043358, 11196361, 118456612]
private def lowC13 : List Int := [167935933, 8805702, 46384702, 17516079, 29072171, 13016062, -68735632, -105943770, -51132405, 142738533, 63490572, 43706609, 126381605, 123751747]
private def lowC14 : List Int := [45362052, 4601806, 7523099, 3086896, 6338467, 15833154, -41275405, -30114284, -11902950, 19317115, 7235614, 1979731, 16756080, 7373937, 57882183]
private def lowC15 : List Int := [48078652, 2431958, 10644599, 6038326, 2832919, 262784, -45103877, -38683284, -18988422, 14693013, 6383709, 5950245, 14218371, 4935262, 19906985, 40031261]
private def lowC16 : List Int := [47411820, 1429517, 6270648, 2338766, 3841954, 1743569, -11261960, -37419508, -36117826, 17298412, 4314195, 8410210, 14920162, 11510264, 21408354, 25382715, 43720931]
private def lowC17 : List Int := [-44256367, -4220270, -6301615, -3504090, -5420975, -2488987, 1146921, 7776588, 30426319, -46773761, -11723506, -8933769, -17198421, -3542934, -20477120, -15530007, -18027349, 46383689]
private def lowC18 : List Int := [-43399390, -5086800, -6824634, -3658081, -5564536, -2294120, 2021671, 5571752, 4330266, -50085877, -22460178, -12377196, -15282129, -6736228, -22355762, -23473093, -12360521, 29925554, 40641052]
private def lowC19 : List Int := [-43395248, -4196499, -6900488, -3648250, -5639201, -2832653, 10018176, 4768530, 1048696, -43238675, -24543189, -14585385, -24507663, -2052463, -19205665, -19680074, -12737987, 22316021, 17693942, 46480193]
private def lowC20 : List Int := [-86055327, -8310831, -13694499, -7243409, -16229800, -9830594, 26704375, 26689872, 12612169, -73981892, -32662602, -27928305, -41300119, -9454633, -39595266, -39725924, -15360511, 41668820, 33701550, 30779300, 82834639]
private def lowC21 : List Int := [-165143642, -15903871, -26435498, -14018774, -24742151, -12904603, 36305188, 80943828, 45211731, -46023867, -81065009, -83851614, -106983776, -66729755, -69147103, -43941715, -12726993, 76223447, 30406047, 13093860, 61872488, 198320267]
private def lowC22 : List Int := [-81618698, -7746577, -12966010, -6898087, -12057026, -4843198, 13604066, 33595120, 19990759, -39614487, 2634712, -26992720, -59995482, -11182247, -35572574, -29596105, -11004583, 35086081, 21249173, 14558385, 17535836, 55949216, 101846187]
private def lowC23 : List Int := [-167806688, -16137600, -26755335, -14118684, -22017454, -11455893, 19743166, 23622070, 49758478, -119952085, -25615391, -130353817, -113425792, -48179613, -38873684, -43114720, -5880834, 23412012, 15137574, 6593441, 27361298, 54732555, 44234175, 203387956]
private def lowC24 : List Int := [-65091981, -6294752, -10352585, -5471154, -1882709, 4168656, 8771321, 9157611, 8385524, -31857012, -6768718, 7903255, -59279856, -38419650, -35096564, -15090635, -12523745, 15281485, 7891688, 5694055, 5803446, 25217608, 10790754, 27647761, 62215924]
private def lowC25 : List Int := [-20200036, -2000350, -737563, -201584, -1998247, 4322196, 5917362, 4678577, 3073220, -6340777, -222313, -4166341, -10866191, -6037220, -9022589, -13361203, -3906382, 6520381, 8175376, 1047147, 4929278, 10731126, 4991623, 10440580, 4596554, 24803852]
private def lowC26 : List Int := [-21369779, -1701282, -1170183, -3212474, -1658772, -2072662, -1928874, 4217659, 2534853, -6156400, -2023289, -5086776, -8428155, -4215272, -8466039, -10330455, -8657662, 7065285, 5090012, 1658037, 4327209, 9138907, 4523440, 9541988, 3050009, 1903312, 21315839]
private def lowC27 : List Int := [-43407949, -4239220, -6693160, -3873590, -5078117, -3130494, 1339086, 3576603, 4466850, -13345888, -919511, -8822898, -14528481, -20399465, -26491775, -17969218, -23866009, 13131044, 5513007, 9716798, 12563881, 20805893, 11247680, 18407461, 13937801, 5585936, 1043035, 38627959]
private def lowC28 : List Int := [47138173, 4772391, 5909975, 2554766, -5986088, 2069159, -5345536, 77535, -9006393, 4562034, 1389161, 3543612, 8990069, -1006637, 30930666, 22536762, 14063190, -26380663, -7185390, -5693595, -6477233, -16790081, -11437525, -27208281, -9478296, -3053384, -4805869, -5281683, 35238764]
private def lowC29 : List Int := [47340850, 4895960, 5912852, 2584684, -1725203, 480247, -3317277, -1912267, -6041647, 2794236, 1370583, 5216733, 8148496, 858956, 31229979, 26388468, 9075901, -17953255, -19179848, -5717518, -5067709, -15388465, -9453044, -26837554, -11817573, -1985622, -6137342, -5676, 13325682, 38805967]
private def lowC30 : List Int := [21685996, 2058033, 4565392, 1803996, 2681263, -355331, -617001, -1070446, -2938423, 7418134, -3771126, 2817694, 7609542, 4172845, 8109358, 10064715, 6508723, -10232501, -8584389, -749164, -3368208, -3386257, -5458096, -8840888, -4895976, -4724204, -2770342, -3514558, 3932709, 1138280, 27561445]
private def lowC31 : List Int := [91995547, 12829888, 13834253, 5917321, -618024, 8504389, -5784960, 846919, -7923080, 8765697, 770810, 7434637, 18825510, 5065650, 59609832, 48889323, 29506511, -48074026, -24922221, -5338236, -33783050, -39607594, -16506900, -51442424, -22029074, -7715639, -6448680, -24744036, 21635175, 16031098, 9155958, 80139779]
private def lowC32 : List Int := [196557663, 20648401, 23596907, 10363764, -2220544, -30417998, -7053347, 1562521, -25656445, 23384352, 7822344, 16755892, 35394163, 2045713, 61453075, 114103820, 25415938, -95145617, -58635930, -12615770, -42440988, -91570473, -32596883, -92900938, -48661429, -19522583, -23606493, -19759430, 39339151, 36141297, 20440276, -8254088, 182630992]
private def lowC33 : List Int := [97564504, 611006, 8399788, 10084277, 386711, -9625150, 42993857, -10030088, -23580642, 24834891, 8983935, 9026266, 14035345, 33937794, 23206759, 21428397, 35681441, -41899413, -27566316, -21422461, -9013332, -45959037, -21654228, -40583034, -14384462, -5289932, -4284217, -18517704, 11223050, 13155453, 16438603, -4282300, 49426899, 149839724]
private def lowC34 : List Int := [199225547, 21995514, 23892027, 10562682, 13770438, 9187462, 17371649, 17936310, -11760452, 25836682, 3863838, 27604857, 41084498, 34690634, 21994791, 25514839, -10905125, -97344647, -65732769, -23936045, -63160685, -101173924, -54998568, -60823141, -40352853, -7516712, -45832960, -32721108, 57034254, 37070308, 33426286, -3181677, 923791, 13999236, 293693531]
private def lowC35 : List Int := [101566419, 11511215, 12557744, 5513839, 6797509, 3947001, 5326950, 9919339, 460006, 11755386, 4287073, 6198151, 23914059, 14672947, 9490806, 12778873, 1314700, -19405759, -47071860, -36161159, -41560037, -54802944, -24522006, -34233335, -14550295, -1591072, -13014764, -9474243, 20143608, 21509668, 16638323, 8362872, 9985836, 7748939, 8163745, 183668619]
private def lowC36 : List Int := [199051075, 21960959, 23854927, 10540447, 13153197, 6385555, 16972129, 15887986, -17353524, 6102483, 11414915, 38073692, 44957321, 24625982, 23823955, 35787439, 6624816, -37647911, -42537819, -131330493, -60845691, -118037117, -53328954, -85213146, -15441663, -17863959, -30233433, 7956002, 22944988, 16289434, 31566000, 29679244, 26759593, 9754734, 16573948, 29268797, 230243084]
private def lowC37 : List Int := [101905107, 11264836, 12297401, 5446836, 6832842, 3275187, 13523854, 11952927, -7330408, 15202463, 6227849, 5395526, 22587474, 10586312, 14250812, 14847029, -9489490, -34351209, -26383060, 13440095, -71449801, -46566720, -29290908, -40002885, -4000405, -9122454, -18465063, 745769, 5370749, 26335212, 16902179, 2657096, 7229468, 14445029, -831725, 23241484, 16370295, 117856462]
private def lowC38 : List Int := [194789234, 21517770, 23266341, 10252991, 12761584, 6923268, 7928323, 8693910, -18939438, 13897856, -5521842, 11044872, 39965928, 25218346, 12613032, 6717477, 11382864, -58909091, -5867955, -17032443, -13301378, -170716356, -72195332, -114644290, -68247728, -33870237, -41314979, -17091360, 23678837, 36708495, 31173822, 3650299, -370635, 8081122, -5602769, 22625224, 76879332, 109361806, 162114992]
private def lowC39 : List Int := [47645767, 5146837, 5682017, 2490989, 3112737, 1705780, -279133, -264382, -4900876, -2976086, 1244875, 4016169, 10163323, 7924323, 1650031, -1094913, -1420414, -6772707, -4402012, -478599, -6390967, -40173596, -18337652, -29220808, -15235713, -8902428, -7411750, -2245967, 1725736, 7881805, 11705993, 8295199, 6608777, 5187516, 1157152, -1805447, 14513678, 18462242, 23168992, 43963101]
private def lowC40 : List Int := [47805733, 5355050, 5651884, 3113698, 2569209, 1460970, -118530, 680322, -5332913, 1890450, -5131683, 3773012, 9615987, 8665251, 2127722, -1784182, 1397240, -12329183, 141758, -3855420, -15974506, -37639150, -17211822, -28324141, -12304762, -15802282, -10203440, -12880285, 6734591, 5345596, 12688770, 1190426, 3832511, 3146468, -890080, 700152, 14224312, 13322816, 16650167, 10998546, 40347378]
private def lowC41 : List Int := [47692440, 5150657, 6203279, 1786100, 3888804, 1458409, -1844269, 3264074, -5556526, 2095276, -1947517, 2256947, 8968655, 8074120, 3273885, -1515067, -2168407, -12857107, -2045557, -2824316, -17321677, -34731096, -21202042, -24646927, -16055447, -15228138, -8700863, -15287104, 7477409, 5224782, 12489476, 296654, 3301540, 3704969, -2502373, -23998, 15200539, 15693783, 17351097, 11124220, 23340348, 32609152]
private def lowC42 : List Int := [-43356815, -6733287, -7536768, -5524830, -6407644, -4850895, -920528, 4731446, 2396705, -283733, 1646169, -459203, -6616068, -7321357, -3103678, -4069942, -5203859, 2390922, 6527734, 4103707, 4378640, 8918993, 20957414, 40335128, 17531498, 11232911, 12687436, 8711237, -25126295, -12152578, -18618383, -907288, -7923374, -3156961, -3471992, -1876107, -6265487, -11836735, -12902092, -5360573, -10236348, -7903634, 44554808]
private def lowC43 : List Int := [-43115466, -4376687, -7100955, -3730681, -7034334, -4326401, 287046, 788930, 4720015, -2287060, -497804, 650243, -5344247, -7871849, -3432685, -2439876, -1318441, 3872181, 3317801, 2219906, 2438960, 11024360, 15001785, 42987883, 22330350, 11078077, 11890351, 9730386, -21545518, -14206082, -21109836, -7232138, -8312628, -4296508, -4048313, -4251869, -7501375, -11626815, -11394459, -8346065, -11624560, -8259590, 25855154, 33223462]
private def lowC44 : List Int := [-43384741, -3352938, -6979787, -5143105, -4885187, -4237313, 1676241, 1149664, 4790576, -1771554, -199556, -695124, -4414850, -7998270, -2724389, -2941255, -6607813, 6392177, 9617537, -1280448, 719015, 6590882, 6104828, 34812117, 27102708, 10275977, 14102879, 9654859, -22537023, -18503100, -15189825, -4941258, -10827938, -6174856, -6775087, -7942690, -14214918, -9439828, -16977817, -3502682, -8549499, -6935223, 20540829, 3849946, 44856867]
private def lowC45 : List Int := [-86764736, -8389174, -13794450, -7311443, -11144130, -4881972, 18675042, 1972376, 8768099, 1333531, 1469000, 240260, -22374835, -39913862, -5884437, -19763379, -5200524, 1800580, 2223780, 1391878, -126219, -4116479, 6516771, 102639212, 16744130, 20716988, 32198493, 21954022, -42960448, -33875285, -35307328, -22011967, -25090391, -15249486, -20241580, -13033383, -23174022, -19230295, -29346758, -10817379, -21247484, -10620580, 40527929, 15917457, 22431357, 82527384]
private def lowC46 : List Int := [-166797295, -16078164, -26670460, -14132632, -22391249, -10691201, 18099579, 48847709, 29862402, 15246574, 6334221, 11876561, -4961878, -28523740, -15889436, -36407693, -38403319, 44258999, 27941936, 30409524, -8541793, 14631792, 10944219, 43567290, 49145298, 45438835, 68464106, 58152371, -99282793, -96370301, -89665790, -92939432, -83455722, -30038103, -50192171, -34242000, -65964608, -74005790, -36986062, -26762645, -44154830, -19405026, 72212703, 30725320, 20578285, 80712876, 141641927]
private def lowC47 : List Int := [-79672265, -7681371, -12834803, -6840532, -10614852, -4936136, 18322445, 15571298, 11733222, 7639486, 2935554, 4178066, -4921749, -13369668, -10722653, -24542595, 1437262, 25224464, 16344235, 11519989, 1931031, 11440525, 8415362, 23595324, 47245329, 25723043, 30673659, 14758110, -40382697, -26711233, -36585509, -24239097, -33112787, -23749391, -21874318, -17110481, -33156408, -31457935, -18360206, -16026219, -23346708, -7196665, 19491006, 3239451, 15378118, 40153188, 50528917, 143595060]
private def lowC48 : List Int := [-165130789, -15907852, -26417939, -14033960, -21714829, -14496194, 19188339, 15606011, 22124550, 2560396, 1047905, 4404283, -16047979, -27276020, 699951, -11139864, -31061719, 33525195, 34850515, 19779601, 13448152, 27933190, 19906835, 34908339, -7150605, 47072585, 57411292, 93356663, -98316238, -79283955, -66403381, -18387655, -75799760, -42868774, -50946250, -36231324, -81563407, -62805926, -41378103, -52116621, -34058416, -30421136, 27096053, 21084082, 33037482, 31458725, 54301498, 49901658, 307763242]
private def lowC49 : List Int := [-78673622, -7549189, -12681691, -6748181, -10494354, -7061446, 8064885, 10498165, 16801530, 2976982, 883281, 3521072, -5378746, -13481508, -3333131, 998924, -28498651, 19944169, 24660495, 16232677, 10723260, 17724230, 11391071, 24443365, -10295816, 6902499, 21276728, 40881441, -44181120, -35683256, -36622567, -22148982, -20538519, -19365523, -23896330, -14458776, -33540461, -30601812, -23761965, -23536323, -11902259, -12989693, 21973791, 12149922, 13976567, 29282109, 42087536, 47719475, 18498764, 215474640]
private def lowC50 : List Int := [-163186703, -15705634, -26171677, -13889008, -21566832, -12007222, 14843630, 18610850, 26345822, 1903840, -54853, 10082440, -14165314, -16469986, -2068968, 6481750, 5494533, 55195846, 40120617, 30678586, 46431168, 22253086, 21626009, 42435999, 3067447, 16103376, 35418904, 3929860, -99330678, -71017613, -65107977, 5376867, -42574050, -65706235, -32998697, -34935516, -76730845, -43142346, -67760700, -56137418, -30079258, -11711745, 55332676, 24695590, 20975157, 93643156, -21014143, 11937837, 24724003, 10336397, 283460390]
private def lowC51 : List Int := [-77954751, -7474400, -12581651, -6700125, -10511219, -6302551, 370586, 13903559, 9780001, -369523, 60396, 2723703, -5705068, -12598010, -2965663, -453233, 5733252, 34051624, 21775496, 17851935, 24823015, 12041298, 12146795, 24185601, 4130430, 6651368, 16858632, -4073974, -78652960, -36123380, -28715969, 1821643, -29917149, -21458794, -14356931, -10980111, -29389065, -17687525, -31020858, -29198191, -17091139, -6776735, 13230724, 12451180, 6008844, 44124969, 2823384, 1836604, 14092593, 1934753, 35445179, 217924065]
private def lowC52 : List Int := [-164520738, -15844340, -26355925, -13978960, -20179904, -13490699, 10736241, 2362401, 38864383, -4463383, 26370300, 28131502, -23769290, -32897742, -7796484, -1093430, 9206660, 28577980, 62543057, 37640592, 40499522, 35751422, 10007277, 39224718, -21929416, 18291742, 42403559, 9344482, -49217965, -98894887, -81772577, -10742945, -36381578, -64309408, -36060964, -28122863, -46241071, -41389546, -83643318, -33745087, -42015300, -16419243, 50346666, 40753482, 23656319, -7867599, 9633719, 44936172, 3532617, 3901041, 50667761, 41907677, 324047045]
private def lowC53 : List Int := [-79125802, -7596167, -12745080, -6778051, -10573503, -4634340, -3471436, 8114730, 15303018, -3739795, -8589166, 7678794, -5867182, -2385028, -7032126, 8944220, 1028091, 11475215, 13197385, 26031548, 44250857, 16467912, 15926366, 25278617, 4790326, 5852033, 10711682, -4856855, 15322446, -4819806, -27061305, -60486778, -33214628, -34909237, -41059455, -17958959, -16804660, -22171138, -54242078, -12546811, -26656573, -15171683, 24192950, 4580283, 19228312, 28603242, 12230104, 18809273, 23241196, 9543455, 20094550, 18545803, 19303257, 225782397]
private def lowC54 : List Int := [-165934622, -15991370, -26551189, -14074341, -22226302, -1072985, -9077340, 22183916, 34643834, -12287317, -18282841, 12731154, -8046218, -17677719, 16701478, -13086505, 15095765, 31693155, 18593697, 34178648, 32348846, 33891410, 26196095, 34031363, 25927128, 32705108, 31614512, 12379055, -21372542, -751181, -37848341, 54097674, -107959447, -53276231, -63464439, -45826101, -32758606, -69932235, -39456876, -33526845, -53247780, -41103075, 34884305, 21810743, 40452455, 76796823, 48633222, 18405486, 22167147, 27254782, 32627341, 22310157, 49650262, 69856971, 328012584]
private def lowC55 : List Int := [-79636056, -7649196, -12815533, -6812448, -10595367, -5001641, 3675699, 10513244, 20529408, -695274, -3021738, 5985980, -3700769, -11316199, 549875, 4503992, 8197146, 28788293, 16240141, 22656809, 13432606, 17172641, 13952095, 23715842, 17130145, 13562885, 25322281, -1978077, -31272574, -25340763, -26394367, 39916173, -56419199, -17023051, -25398252, -18753766, -20826591, -12360501, -17269854, -7541206, -33465396, -14857395, 31219552, 2906322, 7890909, 20045760, 16046527, 10856382, 10020508, 14248395, 10218708, 5032361, 16358431, 21506264, -185302, 221584871]
private def lowC56 : List Int := [-163849359, -15774497, -26263203, -13933638, -12930130, 560825, 216196, 16772132, 48654654, -21229750, -7624445, 11325249, -6043360, -9703571, 9553818, 5759334, 15418473, -399090, 48062817, 44165298, 30056262, 48762016, 25923356, 33131376, 26241355, 20778746, 51106702, 5507021, -35493599, -50741990, -66110036, 26213881, -145217443, -35462310, -69035904, -35098735, -46156572, -44638090, -9720399, -6379500, -30393972, -18611535, 85087961, 27780233, 32964676, 34108631, -10920843, 33625978, 16415767, 25867937, 27568258, 22218348, 22377958, 22883200, -5522094, -6940973, 325035178]
private def lowC57 : List Int := [-79483291, -7631080, -12791895, -6927590, -9921725, -6319773, 9888371, 9456707, 13782898, 1839153, 952082, 2773415, -6622893, -12348594, 1377756, 9018877, -620041, 10707093, 7597340, 23736452, 27454635, 21785492, 16832326, 23010183, 6586558, 12606367, 17647583, 2803457, -43962041, -18596278, -25066677, -17498669, 40136100, -56593699, -28756342, -19406793, -34873296, -27664637, -13025878, -18132957, -13919284, 11064395, 14371327, 28283800, 8644139, 31279234, 25786117, 13707928, 16184541, 5530929, 10798066, 9657559, 17488039, 14524959, 29207178, 27479424, 63065576, 164905249]
private def lowC58 : List Int := [-164415978, -15833449, -26341444, -13971868, -16077393, -13192525, 13391167, 23922158, 25370132, -1335233, -2147733, 6176633, -12572559, -21223736, 570768, 13580870, 6940281, 10660134, 18002186, 51230918, 38942964, 38755919, 28955589, 38487396, 6865930, 23330769, 38424285, 3962466, -52657711, -44844031, -51834677, 24518277, 58518205, 27241613, -79848237, -55380456, -90117192, -83238957, -47683506, -28572624, -41661448, -14218409, 41032837, 17235587, 66065075, 65944730, 62847237, 32506319, 26229576, 11880530, 34724625, 26014647, 38875962, 34403873, 29243434, 33049285, 67807651, 41928623, 261359736]
private def lowC59 : List Int := [-79168294, -7600608, -12750954, -6780911, -9406129, -5195899, 9098618, 12131837, 9124262, 453786, 1408035, 2603304, -8343475, -9361079, 1511690, 6817622, 3248517, -3506083, 8990760, 9983633, 35271036, 26082461, 3313256, 25929577, 9711087, 9582940, 24117065, 7985326, -16079399, -19176559, -26036650, -12935159, 3061959, 19073903, -39771296, -24270486, -42840780, -30897043, -26854999, -21117226, -18245197, -7677024, 26341078, 1352261, -10058952, 34991374, 27691373, 15222811, 19483104, 10032422, 25425252, 16674303, 24791121, 9956332, 21926898, 21318588, 28718875, 10138795, -16075137, 173097460]
private def lowC60 : List Int := [-149389116, -27404039, -39183479, -18783980, -29674806, -13936848, 18300018, 21566526, 28779187, -3732402, 706470, 4143834, -15144055, -29365292, -3546117, 9087127, -91167, 24207269, 13650826, 49811259, 29837620, 34407225, 26384447, 36999358, 3179549, 22382817, 44577511, 22163145, -55997086, -47411352, -49121869, 24590104, 6094694, 3888711, -66823736, -53250725, -45277391, -94512893, -72823419, -6497035, -20021709, -4573410, 45871404, 26145569, 38191176, 56456191, 46367311, 29008686, 25290385, 14807509, 38344999, 26114891, 35707310, 35338522, 27199252, 38859134, 62280476, 27601693, 47772275, 69854123, 175521639]
private def lowC61 : List Int := [-81684583, -8328935, -13621972, -7155266, -11112814, -5938977, 11583316, 4250111, 14464541, 428966, 146689, 1915047, -8199684, -13272992, 326537, 5589552, -1041635, -3064496, -847281, 12547337, 8794038, 27838841, 17778619, 17707437, 2216395, 16021656, 10453153, 7939302, -18338994, -10577442, -7052319, -7565639, -18674818, -8302415, 22395778, -23062171, -25399501, -26791739, -43726980, -6390828, -12518138, 4307523, 9347341, 409279, 6669408, 32508585, 10095273, 10602777, 33647592, 24885006, 36523397, 21956539, 35845448, 18662625, 24818327, 25932296, 37845931, 10668046, 18095713, 12990383, 14645035, 117217393]
private def lowC62 : List Int := [-130161947, -12615299, -20734457, -10953401, -16874859, -8033951, 3931964, 3783746, 16101589, -7283578, -10408385, 3468446, -14443897, -17536817, -8285585, -1193564, 5657999, 6259168, 4162632, 6596222, 4950452, 19613516, 18287630, 13354316, -7198385, 26871956, 26006038, 10395016, -18372743, -30231149, -29821007, -19175620, -9441350, -8604572, 28827788, 24872750, -56657026, -73809932, -71934941, -48832852, -9965575, -4170875, 24945489, 8648629, 7985779, 63026902, 9094193, 28682331, 22399709, 19818791, 30687010, 19636979, 36289297, 25498359, 36871497, 42086681, 57664800, 11764394, 30017514, 14134251, 23411321, 56879949, 140239449]
private def lowC63 : List Int := [-42191937, -4764530, -7794411, -3557214, -1264369, -8720013, 3050378, 3189052, 5805466, -3065679, -213897, -46311, -5308527, -4523304, 3406889, -574094, 1100743, 4001823, -1148952, 4921836, 3531022, 8133296, 5493314, 5177123, 1210196, 8895754, 11935166, -113075, -2063092, -4922190, -10543030, 551550, -4706926, -2051942, 8475960, 1069930, -16978599, -20420216, -17505390, -10314444, -23748413, -7857929, 7409240, 4994941, 6449062, 18126796, 9408750, 8114548, 10054667, 4440410, 14652488, 8233183, 13143870, 7551942, 5742374, 9170340, 17238412, 5478732, 3848196, 4477523, 5858773, 14248866, 16481450, 47122198]
private def lowC64 : List Int := [-42961355, -4490513, -6496909, -4088407, -4596959, -4020855, 1737352, 2363566, 5137807, -2291804, -700358, 382933, -6117908, -4987258, 4697904, -473868, -2913916, 3762733, 538359, 2379969, 4864614, 8129065, 6140128, 5162427, 2683823, 9465638, 14209602, -3134404, -4072048, -4267734, -10338701, 2922474, -2017020, -2727766, 8276252, 1975860, -17694137, -22068447, -16187415, -10703931, -19587757, -12290867, 11816872, 4180830, 5825600, 16745682, 9024880, 10210834, 8789632, 2964894, 13778260, 7814613, 13154548, 8625591, 6562236, 6359638, 18128805, 5923672, 3742279, 4555690, 4702076, 15534010, 17326607, 31868305, 32782201]
private def lowC65 : List Int := [26874619, 8343981, 18380410, 6985644, 13039196, 3276280, -4194346, -6401414, -8709226, 6177812, 3232670, 1362439, 8255920, 9697658, -3021147, -12679, 4354534, -7409920, -4667462, -506837, -1174351, -1738116, -9024202, -9988576, -5804241, -7355329, -8239286, -2893841, 9396558, 6647590, 17327014, 1308141, 2873700, 778417, -1101234, 1233271, 2550864, 18576821, 13501189, 9253490, 14075347, 6601388, -29158160, -10605123, -6865994, -13744924, -6593872, -9298614, -6646958, -2706511, -11352697, -7255434, -17926935, -11253402, -10505685, -7415845, -12632314, -7351572, -8338576, -5185069, -4139027, -13325919, -14675462, -23254992, -8838626, 43811608]
private def lowC66 : List Int := [27842247, 3423506, 18535475, 7767268, 12623526, 5881310, -3145012, -8261373, -7456857, 4923533, 3919497, 1065935, 8666259, 8719292, -1560494, 2423518, 3125555, -7505117, -4654037, -826081, 486165, -2954149, -3379639, -9188174, -7446297, -7247101, -7883379, -2747426, 8411339, 6579345, 19583179, 1982842, 2803449, 1928680, -450850, 1097456, 2625083, 17952849, 15144292, 7411294, 14110521, 8960842, -24369995, -17166557, -2612051, -14069487, -9678184, -8049835, -8853832, -4395705, -11307390, -7059574, -15755763, -11902526, -10917576, -7260928, -10831533, -1871463, -13108790, -5496072, -5767496, -13517585, -13095689, -23892881, -6843927, 30791206, 32335425]
private def lowC67 : List Int := [56365718, -5833387, -40422986, 64943185, 44342514, 18503923, -54021786, -33272694, -5061985, 21335720, -5026549, 22411275, 30192204, 39960553, 6987416, 3274446, 16950522, -42274147, -3856273, -23627565, -6470847, -8439076, -10807957, -23261273, -43130323, -17282652, -31350538, -11815115, 41599103, 28002002, 42767218, 9563157, 22200775, 13059766, 7859241, 13533387, 19092938, 31921100, 69214721, 18672191, 31825406, 20012357, -59772845, -20387843, -64636927, -42839157, -18978767, -18816960, -25199883, -13448029, -20617429, -19616402, -47454869, -26795684, -40949076, -26889699, -44491802, -9921786, -23822033, -30101078, -22457338, -29921720, -38880000, -67469193, -29200454, 75311952, 27190169, 90261249]
private def lowC68 : List Int := [32976389, -899530, -19420939, -22545037, 1009164, 4891318, -36024121, -43761836, -16249980, 47550661, 26146579, 5388025, -17383184, 7471176, 2238021, -2377891, 11608395, -7695164, -5222797, -9127345, -3850519, -20714014, -19093001, -49366963, -24174079, -18773346, -18619060, -8989625, 26401733, 19508641, 25129878, 13679424, 16066608, 8407526, 15209020, 12879353, 17190093, 20608747, 42905433, 17675061, 25941279, 9989215, -39183344, -26931963, -20049301, -10482912, -24852861, -13392949, -24271256, -9084330, -17826384, -10206409, -31810971, -14720026, -25140525, -17209593, -27913435, -7174634, -15846154, -11502587, -22506703, -23021264, -28339493, -34074577, -16837811, 40523833, 19487972, 21895095, 73673069]
private def lowC69 : List Int := [51947265, 2592581, -29958380, -11554587, -24168104, -10267617, -28616855, -44498349, -70842872, -16064311, -7860744, -57987741, 85002210, 77727145, 44603810, 43658185, 14066669, -34391231, -33627111, -45928179, -51276912, -16211088, -10778707, -74597869, 49121918, -11888598, -32921339, -12846795, 35221907, 30355129, 41051945, 1230655, 25696067, 6803503, 33265618, 19651795, 21522684, 29335368, 41629661, 29097224, 35324303, 20328486, -45389023, -24445390, -21506690, -103271512, -88839450, -27941788, -34969508, -19567789, -42960631, -28453561, -68609044, -39257542, -55663726, -45269752, -80053163, -13009822, -26623415, -22007439, -49108185, -49421642, -58767135, -57714958, -22942635, 40960261, 15075934, 13759595, 17910250, 102077388]
private def lowC70 : List Int := [11873002, 1867302, -177835, -641051, -10805442, 426450, -16941516, 12062795, -54324013, -5444054, -3910953, 6131063, -3607496, 3924934, 67075836, 26821035, 22756718, -18655659, -31863958, -31015303, -18093459, -20178133, -8305274, -35439006, -13919649, 4999381, -3448805, 21572540, -10862709, 10100967, 31974767, -16608093, 4980079, 12429358, 26156750, 16771179, 12494226, 27012227, 17875193, 48101898, 5991032, 16552891, -26972637, -14801072, -16562186, -59087801, -59287118, -19634990, -46305196, -11411447, -40004589, -19350806, -36705367, -9858116, -19017914, -19640643, -38788455, -3570354, -4734794, -5364555, -22970775, -25484748, -29085640, -18287546, -9199742, 34690452, 6810397, 9937517, -2354581, 12733472, 121492940]
private def lowC71 : List Int := [17666634, 3100960, -1158138, -1715058, -4411331, -529952, 21537894, 31887121, 2418093, 25061811, 2465914, 16677009, 15410787, 24851753, 12099676, 20577116, -2939990, -102484922, -57431763, -70350232, -84407539, -57164254, -45903795, -71712668, 54759540, -45360951, -48169834, -39298646, 57432593, 54031258, 37636448, -11157572, 9329985, 7172741, -10920398, -3467119, -5633311, -6037122, 66178895, 33921768, 127215275, 35745606, -44804520, -27917838, -59061074, -113972319, -79141861, -71896373, -60999497, -13884454, -44265513, -17886257, -61301581, -33308742, -54062814, -33468365, -94616486, -9055997, -28521869, -36078960, -42983335, -44555292, -50483551, -41032833, -7439260, 51402089, 22430208, 18991928, 3276998, 81976189, -62750919, 144992832]
private def lowC72 : List Int := [11560963, 1833710, -220789, -703196, -1832866, 268803, 15823039, -5015377, 10832737, -26223785, 4085828, 24983830, 16117430, 15733872, 9947944, 9164694, -6605839, -9549310, -25895738, -8266609, -68342739, -14801470, -39970137, -42552998, -33902235, -1529257, -14209659, -13461207, 44657759, 16975178, 19846510, -2090590, 14019034, 13981777, -911427, -748635, 6908707, -7419422, 32417466, 24444843, -652528, 53345290, -47757832, -12667447, -8157187, -38682046, -25121314, -31338806, -38321805, -14184006, -29780762, -6918089, -39453167, -14858046, -29835779, -18595445, -38895124, -7995152, -27397109, -11248832, -36582569, -19626669, -22295206, -27144289, -22368866, 18802933, 2996342, -2271786, 8967503, 40656431, -7784676, -19034013, 137219318]
private def lowC73 : List Int := [18234777, 3158383, -1117795, -1654398, 12682584, 14440318, 22591782, 3639986, 13514509, -76145531, 25119143, 40758716, 32865891, 47468212, 16242161, 34764504, 6422788, -4610205, -38018106, 17941391, 42568672, -124882559, -84329198, -104883056, -14232319, -1429369, -35741346, -30057930, 84301749, 26180353, 52991069, 24082545, 32202715, 14542200, 15019498, 17666716, 17425734, 47561908, -46970529, -14048472, -931548, -8764441, -126736692, -56405020, -76973286, -79345606, -66662195, -62487514, -78884723, -26720974, -63896968, -47128342, -92715247, -69688780, -68298954, -53001319, -68810175, -12451509, -45250948, -42609847, -36908634, -32856703, -63172564, -65182357, -36029855, 1372481, -1809768, 3485397, 20946668, 21493772, -20800689, -51023391, -45204603, 188259962]
private def lowC74 : List Int := [11405306, 1817518, -242386, -672533, 36651081, 11563600, 6065669, 24040099, 16315991, -11093658, -9441248, -48152529, -21708997, 44362096, 15318658, 38073005, 11845063, 6599448, -44194166, -21402494, -16384775, 3817088, 19582626, -35262791, -67187373, -24209482, -37586289, -22686817, -22417111, 45199236, 23664352, 27543667, 38251646, 5091221, 31621305, 9818445, 33592253, 31165080, 15491395, 6326804, 16229449, -1197206, 17324149, -38484698, -25483516, -32049057, -17958115, -5873250, -32023801, -21251185, -53889508, -26135992, -30255645, -10842544, -28153013, -28277515, -32263395, -21370831, -28913731, -12361727, -32339732, -22668758, -31578627, -28796037, -22879422, 27882283, 8136235, -5680686, 20939520, 35996849, -21778619, -2681331, -7099923, -7471196, 152991164]
private def lowC75 : List Int := [16157836, 2935560, -1344534, -1838983, -868102, 19275027, 25352143, 582740, -27494798, 5560448, 4002430, -15338014, -10852053, 12115878, -35157887, -62231578, -14257877, 2696260, -25637012, -18269980, -8800546, -1195960, -30514181, 2991366, -10599027, -24740562, -43200237, -26432765, 42406087, 36241477, 57015081, 3390054, 4298381, 118336301, 100535608, 79648473, 128966705, 82268508, 66153380, 40966160, 19884349, 24912951, -17004165, 3431272, -48450398, -96058286, -56539888, -51947549, -44676980, -18958398, -42086201, -36882982, -68102998, -22981317, -42008190, -49961586, -73139091, 27889677, -8256056, -19582997, -43433468, -65249566, -59845623, -72732656, -20739349, 83856093, 25093114, 3058743, 18627724, 76561087, -9951484, -3043755, 4548961, 42641842, -12357269, 243250636]
private def lowC76 : List Int := [11915499, 1870595, -171878, -2115057, -641428, 10414177, -8362414, -3226958, -8260337, -9115123, 86872, -8022286, -3108230, 8031673, -16222535, -9481415, -6963788, 4192066, -6875150, -691140, 6162939, 5837132, -13007172, 7201865, -15557477, -15329586, -21057202, -7165821, 17919119, 17801280, 24025366, 4324023, 2166000, 2149466, -8710012, 54126644, 83008629, 57737467, 14841244, 9201420, 12388826, 7752708, -16965374, -2187901, 6241522, -70257258, -24319236, -24662627, -23995889, -19027950, -37222072, -22155336, -52141378, -29420474, -26719356, -28635477, -45589626, 2571748, 4400364, 6020630, -21735757, -267427, -3047334, -26879866, -6723711, 42853082, 18001774, 29002849, 33874920, 48474800, 5027500, 31695603, 17796933, 24438265, -11469124, -29795421, 189227129]
private def lowC77 : List Int := [17561919, 3089157, -1068261, -1786738, 4199, 6568058, -24088916, -33124211, -23030657, 4967342, -16683386, -41532705, -20133957, -10488082, -36589245, -43026812, -4429412, 2262373, -1110565, -15420161, -5513994, 575385, -15685479, -7730765, -7715309, -24789494, -34166671, -11878015, 29716069, 41872191, 51387867, 9304232, 14954853, -1691882, -12991557, -8295946, -8872726, 175684898, 102667770, 28601227, 35939432, 18743736, -33901346, -22256852, -26227748, -28133237, -138801876, -86595315, -37122706, -28648906, -64188197, -46243152, -50370119, -59813820, -79162685, -77817704, -112103776, -22908420, -28556487, -31290024, -23936049, -28408509, -5617587, -52406205, -38896242, 36066652, 9786178, 33657384, 10692172, 83258369, 22156499, 4087122, 35376160, 64047371, 17198472, -38047095, -47139170, 215847062]
private def lowC78 : List Int := [13086574, 1992352, -6975, -561184, -1003143, 398067, -6689698, -38687911, -2601337, -5937585, -15655180, -15806865, -11069643, -2302761, -18967842, -26383404, -4675822, -7650534, 258471, -12631335, 5313991, 11929546, 10053132, -6483111, -781388, -16329932, -12737191, -7898203, 28860999, 20320099, 30584265, 14324838, 18183116, -1646034, -912165, 846782, 756676, 10757707, 800602, 66037834, 44331108, 24073621, -25615927, -6180552, -13841924, -23588418, -88777498, -31101377, -32548216, -14252592, -27616131, -28761992, -30038615, -32232559, -34842552, -28693362, -54915947, -10970131, -21410451, -14717905, -34558555, -17154378, -26226656, -9169234, -7916757, 25490657, 7328096, 15249668, 2290291, 7705754, 958840, -23644822, 3695556, 17625041, 20028445, 915878, 3227430, -28286963, 186672509]
private def lowC79 : List Int := [18895927, 3227882, -939652, -1662318, -3947542, -1537200, -6381436, -17259085, -32233175, -11121329, 2505433, -15362347, -6918175, 6090723, -17364416, -27512866, -2148265, 21152546, -6655655, -10274353, 5026056, 22774879, 7502525, 20564570, -4599896, -21951852, -22133910, -3532977, 61172479, 42192103, 60355654, 24467734, 29294328, -751476, -850227, -503550, 1961769, 13956711, 41577342, 29649704, 57561444, 45592035, -90109696, -59574100, -44744184, -44117321, -175382188, -90969185, -63527863, -40848203, -30627958, -35605703, -42917698, -74630312, -84759565, -72816350, -81171970, -44999210, -45315742, -57428500, -32764744, -43190815, -50120839, -57331875, -24403059, 39344323, 3438465, 27887510, 21535451, 29434721, 12224007, -27185560, -5623555, -25154237, 35113334, 19919537, 22768888, -45308904, -27660900, 200857726]
private def lowC80 : List Int := [12367634, 1917609, -102860, -611768, 3342519, 11380925, -22210961, -31028565, -3989003, -16283539, 2432301, -27477320, -11931253, 217694, -4232747, -6895348, -4444845, 124436, -5215482, -1760664, -4707988, 21928255, 5654503, -11325762, 18542605, -764285, -7310725, -5246394, 14636786, 10167565, 23465837, -6777992, 16109104, 8404106, 7724333, 5503299, 10963899, 6352954, 23702487, 11490677, 19964966, 14499284, -29904252, -12972061, -28955642, -45508366, 17911809, -80147990, -61459022, -27636546, -54827083, -30558730, -40282809, -25836813, -41443802, -33572983, -47484950, -22019043, -30544968, -24112503, -30827351, -3452163, -11706967, -23607524, -1984855, 6728405, 9860211, 27400974, 29660685, 24656854, 16588863, 1234255, -3443709, 69386, 1960589, 3206919, -14786836, -23434669, -16193185, -22100677, 184579217]
private def lowC81 : List Int := [16951780, 3025707, -1289563, -1743038, -4066277, -1454163, -21149245, -33668438, -35659261, -19657503, -6260381, -22501501, -14104421, -2790774, -5499854, -32457381, 14129898, 4260554, -10834160, -11676266, -14157174, 30835595, 11752093, -6662733, 16324351, -1025737, -4458790, -3142610, 20250584, 19297552, 45478802, -12023354, 20361585, 2486630, 9860282, 6548795, 9493556, 11995256, 62631636, 35649588, 45425375, 23059293, -70224405, -29233251, -25895134, -71954790, -31648589, -24005565, -163024743, -86334226, -104135700, -71663460, -74521913, -49619702, -101675960, -81581884, -127894035, -41602686, -71523564, -47236873, -23453573, -5816749, -35494140, -41456243, -8388507, 41215120, 16348376, 9725786, 33496499, 23063290, -22793210, -16563676, -12373849, 1599066, -1526843, 15205218, -5659117, -41034544, -29673170, -52567290, -38170299, 237761242]
private def lowC82 : List Int := [11329780, 1809686, -252771, -677716, -1861704, -930494, -7325083, 559422, -22413289, -7214264, 865345, -20148460, 772496, 4749596, -8729432, -13243084, -5576905, 12031079, -10252102, -3324533, -17980384, 17283735, -2737576, 4418248, 11070916, -3107047, -6221501, 3881623, 16550469, 16186972, 18460717, -30614967, 12397265, 4072296, 1257508, -1788, 6246463, -4176575, 15943824, 29256936, 27685322, 22899253, -43630309, -23238647, -38605849, -48599048, 20045850, 17956150, -15853451, -59448776, -60093454, -33369093, -57027063, -40260721, -35813527, -31434826, -48384840, -33861353, -37345578, -35959456, -22318959, -11877704, -33408973, -24831240, -8616429, 12502201, 7789561, 5455409, -3578678, 16084273, 9588748, 13177023, -378409, 23689983, 10004298, 16619174, 5193417, 25852974, 3074124, 7834492, 15034120, -9695518, 92855132]
private def lowC83 : List Int := [15285239, 2852433, -1523921, -1852782, -4450351, -2203074, -1190813, 12586619, 2139061, 2229941, 5628677, -7245700, 11624062, -79449, -2388630, -1123929, 2548051, 8221323, -11755179, -52338885, -26043529, 39676493, 21517907, 17466025, 17284893, -1688153, -4961064, 6853982, 24505568, 6051861, 29389044, -39389572, 14981795, 5020836, 9237192, 152672, -9289761, 14582483, 45440507, 27896989, 32117375, 26635574, -75208996, -38750437, -35247047, -108339429, -13734158, -14047358, -54641692, -21590988, -131817817, -82771896, -103757023, -66571391, -71104949, -94040375, -117224534, -20664449, -43961286, -50621278, -85543108, -54238753, -63743885, -67305940, -13512933, 7460334, 6263990, 8943924, 10922865, 22170557, -8423629, -29053264, -12449885, 9989380, 5773776, 23197780, 16048767, 21973284, 13446819, 8972635, 20971740, 10319390, 3884453, 128223039]
private def lowC84 : List Int := [4269474, 1075513, -1227852, -1153822, -2549614, -1399772, 1212310, 1426056, -299545, -1096238, 365175, 1146205, 3559342, -725597, -1507211, -1979909, 127343, 2576991, 221041, -14734230, -4625804, 9734261, 5840840, 4331612, 1007507, -3401832, -4306888, -1372101, 821783, 2686590, 9708673, -11198863, 4501488, 1209129, 5582523, 3365344, 4371037, 22264833, -3649618, 8661558, 9569825, 3061054, -45504506, -10864114, -33397221, -55335227, -32373165, -27171664, -22985150, -19880668, -27082847, -20852766, -27748251, -32804946, -27821420, -51594226, -75976319, -24143120, -28598214, -24891574, -60936607, -41650282, -40868635, -38191358, -18560680, 4943293, 7637961, 12334928, 7870937, -7444645, -10129536, -11690887, -1621720, -32126951, 1555194, 7899137, 9022327, 769201, 960115, -8967332, -3462779, -11365208, 17357095, 14013479, 73591456]
private def lowC85 : List Int := [1608247, 188676, -180861, -445784, -928791, -505002, 362522, 1100146, -489209, -551693, 367501, -2551622, 1304297, 1614906, -414695, -72552, -704718, 764073, -328047, -802034, 641586, 2818471, 1899778, 573484, 5563186, -1847976, -2022519, -1351058, 767600, 1636338, 307283, -2226949, 1262492, 1683869, -959310, -2098334, 2820280, 3065323, 1554014, 839025, -170173, -158687, -11256530, -6506468, -6540872, -23303665, -8578796, -18500979, -9615585, -6924550, -19167694, -9835372, -17368755, -9692833, -20416124, -29269922, -40806138, -9067048, -11708889, -5635526, -5872094, -25134846, -27516472, -13900958, -11339435, 7468371, 2270180, 1409329, 5777648, 4013617, -7835082, 2549548, -958942, 241535, 3797784, 1338991, -93141, 4188697, 2568510, 793886, -2913559, -1325552, 7758579, 4830701, 15383181, 38829627]
private def lowC86 : List Int := [2268356, 434526, -723352, -596362, -1320943, 3412594, 1544591, 1509930, 29813, -380108, -448811, -427301, 2056544, 557179, -931240, 849550, -188473, 1705619, 770956, -4101672, 1085788, 1658623, 1801262, 2813668, 964976, 1057191, -1776536, 810235, 13253, 370528, -1060312, -2769959, 3495290, 977350, -3635791, 854921, 945236, 3966923, 92051, 304670, 926274, -55747, -8507870, -4220125, -7751756, -18553506, -13761735, -13046135, -11910918, -5616102, -23961186, -11731085, -19650174, -9255478, -9552894, -25460276, -43297766, -16894144, -11905947, -7732542, -10615777, -26761915, -14662209, -29770808, -11463023, 6510596, 1541852, 1236811, 4112780, 2392068, -2939960, -3252531, 4316823, -795429, 995729, 347176, -1622415, 1309077, 1759919, -1905165, -2690391, -6481777, 1695677, -438555, 13633562, 3128075, 31995147]
private def lowC87 : List Int := [2224883, 350208, -208439, -1500887, -325185, -715881, -3783178, 6162680, -76543, -180354, 198576, -676293, 1919015, 1568696, -1872591, 674143, 1619422, 1228616, 926849, -3892140, 905779, 2635225, 2429757, 2723838, 2322381, 456298, -2724469, -932078, 336335, 341323, -109249, -2993681, 1622264, 1873923, -2345796, -361620, 1051285, 4180290, 664518, 592142, 3770082, -3531119, -7414824, -6202529, -8213406, -21841676, -14942139, -12590318, -11535381, -5222284, -20433763, -11379186, -18917713, -9196906, -8986869, -14612063, -45425009, -20385493, -11831211, -6766341, -11955859, -23602246, -18968391, -25760905, -19670318, 8186884, -679644, 470472, 5506213, 2159214, -2205560, -5068336, 268100, 2551937, 3382808, 281862, -1478236, -329461, 839534, -1212595, -1397721, -6125855, 226343, 718241, 13627646, 7531384, 12997354, 29369840]
private def lowC88 : List Int := [2024889, -3896521, -2275836, -1664157, -1874724, 953059, -1303619, 4162854, -1598310, 1276357, 200627, 447576, 2020095, -779218, -2939119, -1810471, 1284202, 2066270, -19034, 687643, 1588088, 1428282, -655189, 39602, -2957244, -1217985, -749782, -1244791, 1055602, 1390972, -364860, 1520435, 4018772, 875516, 934035, -1821136, 1357711, -8624415, -1227471, -1785246, -3936828, -185324, -196875, 1487807, 3611752, 9708768, 9115731, 11433318, 8706933, 2267833, 14356307, 12428707, 22469584, 12240583, 17265255, 18880749, 30756030, 22704834, 28019220, 11269731, 8053264, 17536608, 14832312, 24779586, 11311254, -34849861, -12234651, -7013600, -8745825, -7867200, -4538264, -6939706, -2161590, -2812789, -1534220, -7459007, -589082, 3932251, 908988, 2749259, 5610576, 6201901, 2781966, 5494562, 2198104, -2818792, -6814178, -1551702, 31882781]
private def lowC89 : List Int := [2102548, -715174, -875609, -398662, -1321374, -267610, 300567, 1113946, -439808, -375132, -153149, 670293, 1919762, -695585, -874049, -923859, -696838, 827168, 1919813, 963132, 241876, 1794903, 2421882, 2311566, -1981667, -1702476, -540085, -4484265, 1301792, 3498213, 81733, 5583264, 3468735, 1739507, 1254613, 74135, 1846917, -8565797, -3370490, 889506, -3667333, -1561014, 1761672, -527472, 2293423, 10222667, 11822055, 9338869, 10918112, 2626489, 13157333, 13690236, 22173024, 11086915, 14119849, 18395612, 32153448, 12253640, 34210026, 10483531, 10905520, 18010405, 14231930, 22675043, 11331396, -34277436, -16307367, -4137667, -10265957, -7973348, -3007938, -6008223, -4115149, -1497990, -3322063, -4325477, -646733, 3448460, 344393, 1485718, 4399775, 8404683, 1098433, 5636216, 244650, -739950, -5859458, -1692337, 15122315, 28368480]
private def lowC90 : List Int := [2356679, 1404415, -812924, -3815259, 867817, 534344, 1228515, 1415237, -214465, 15731, 221290, -1753597, 1560018, 440553, -792538, 515116, -3904569, 2208902, 1421423, -476253, 40706, 2448655, 1822081, 852577, 323907, -2637367, -244172, -2886686, 2547016, 1492429, 635770, 825330, 2622216, 1677837, 916711, 1104975, 1107675, 1555466, -10628474, -752254, -273210, -1706407, 188730, 2014578, 1462442, 8647922, 6761297, 9456761, 10476716, 1934037, 9848918, 15538370, 24197619, 10416755, 21439642, 20653450, 36624236, 13896074, 13855644, 18012598, 10384141, 16170057, 11024246, 22665568, 11988912, -31426588, -11880849, -23761080, -6126790, -6744875, -5332801, -1810378, -4041700, -3552323, -158555, -2864463, -1616256, 2967600, -1052147, -1267368, 5336667, 9586471, 1845084, 10607699, -1337058, 490772, -3916339, 2158314, 5687596, 7077948, 36715331]
private def lowC91 : List Int := [12706669, 2591907, -1873965, -2030875, -4689094, -1492215, 10961304, 11405117, 2136494, 5972931, 3080470, 4457335, 979551, -27509280, -18701724, 9845590, -2392030, 12368087, 8164243, 7344835, 837899, 1963124, 9483039, 12565017, -22618672, -6478388, -1101218, -11454350, 17074632, 10781369, 1589864, 6520480, 4014347, 11682691, 4878346, 7361470, 11167392, 8954172, -38528525, -27086468, -23068429, 893328, 4015285, 8557069, 15359782, 1808347, 36400154, 9420181, 32818814, 6791567, 31550951, 10794138, 120671100, 65058422, 90257768, 80546970, 152467739, 39733166, 73601374, 53648121, 47961676, 86387162, 75485122, 91195050, 41859095, -121832003, -46810283, -75226975, -57260368, -66611715, -12256209, -3451581, -3545184, 2540204, 7909914, -5805135, -7775280, 4229981, 13030561, 15413899, 21031137, 53763556, 25352258, 42079387, 4065707, -28313685, -10727324, -4779529, 16225068, 15729965, 17397021, 90975782]
private def lowC92 : List Int := [10911835, 1767522, -305733, -1183661, -1533381, -365861, 5948315, 4396212, 9147000, 1682296, -1356954, 5613221, -6297312, -19964615, -10627661, 3011415, -3914947, 3749742, 4246711, 7197715, 3472787, 1715904, 6231010, 7391910, -21522792, -241035, 4203002, -3045706, 16135077, 8221262, -3503619, 8280386, 5309005, -15316786, 5119889, -10548879, 13425034, -1085725, 1916726, -835389, -28934816, -21469655, 10109051, 9042189, 16585544, 18630917, 12257456, 4842445, 2810959, -988032, 1491829, 5387082, 62160239, 31828874, 31580977, 36912195, 61643503, 18089122, 35013703, 38976593, 32165426, 15239334, 23338335, 50028210, 29961314, -54896926, -14106622, -27916809, -12234339, -24460538, -12754550, -3840112, -15969037, -20626522, -12761822, -18696419, -9864531, -14879718, -3853620, -10866577, -1698093, -7461182, 40065314, 25906803, 4605884, -9101551, -6267353, 2053545, 3409624, -2738643, -8165924, -4506738, 86167320]
private def lowC93 : List Int := [17012564, 2999230, -1313625, -1757451, -3793192, -1999305, 4436576, -3361961, 8486821, -1384240, -5015560, 4120156, 9157468, -379130, -12523835, 1930669, -12122627, 11393743, 2846044, 12985753, 12649993, 21781886, 13957424, 19012220, 804919, -14684685, -9092748, -18658868, 42650432, 21842063, 4260645, 20354494, 20116355, 12776639, 7824753, 10648853, 21478973, 16301275, 4988312, -2477321, -2259361, -6377852, 47920126, 34803400, 41299582, 56355329, 68689945, 9833617, 30298958, 4102652, 20623664, 16947244, 17637172, 86751451, 95957653, 89931587, 136312042, 34949160, 63184040, 70808865, 69553430, 43889543, 40691548, 45366604, 17384315, -125963234, -44571504, -49401460, -52499929, -46941209, -15047808, -54139601, -49780624, -63875233, -41232886, -41317648, -20536108, 891107, -3032017, -2789431, -14176426, -1463386, 24155381, 3164759, 41675575, 2395625, -5649219, -5544211, -18653622, -8188797, -19258350, 11207660, -77356053, 142069102]
private def lowC94 : List Int := [10937188, 1768869, -306974, -704113, 7701906, -12076178, -4292669, 11649343, 8691329, -1541334, -21758213, 13527193, 11400786, 3951744, -16871065, 8467508, 8684985, -7735494, 12837460, 2535591, 14268914, 8135168, 14916782, 20776934, -10805499, -5543299, -691704, -10604404, 21181786, 16232070, -1799298, 9650744, 5301059, 6572057, 2034184, -6691429, 13857174, -7813473, 9960392, 4780453, -6716723, -12316401, 6550495, 13645078, 10904042, 28835867, 45938874, 4268959, 14455561, 1350610, 13900098, 8173140, 9981127, 39410774, 42442244, 40115965, 65855258, 19882205, 29074149, 31878838, 35938384, 24813734, 27363847, 18979654, 13340686, -16594471, -3909705, 11926879, -66510403, -60571987, -10414877, -25975734, -14233200, -31821937, -19442013, -28584564, -9676331, 3232466, -3175608, -1249648, -1371155, -2224268, 1288844, -2494494, 9513322, -6556769, -8069159, 3465719, -18050358, -12683121, 1173162, 2328962, 37207455, -11360041, 143901053]
private def lowC95 : List Int := [17164416, 3047609, -1261508, -1728087, -1009687, -3218935, -21567569, 3480274, 20817205, 5744620, -15371110, -3367425, 8865848, -3169548, -15258339, -6735488, 12951051, -21336126, 32813287, 1794507, 24652494, 18357550, 19672403, 13942196, 11906240, -10037082, -4685179, -9060596, 23075937, 32144474, 11365696, 26692399, 21871427, 14625714, 13236590, 14907762, 20774473, 24951304, -8733812, 2133762, -893452, 225538, 8775196, 5657215, 33186183, 76925942, 103181205, -1628036, 31491073, 6185767, 26398733, 11897557, 28426082, -3923020, 109776142, 99626247, 152104945, 32110868, 64754066, 64042968, 82242589, 34436053, 39213170, 52251445, 28042600, -18286684, 11000080, 24795104, 26308364, -171474677, -28592376, -35075944, -5444169, -86082503, -48119756, -60807358, -51128741, 5781770, -15201641, -115812, -40314931, -27875301, 12086123, 18415337, -19586295, 8611848, 9713961, 2130011, 22889152, 9662315, 7031927, -7087080, -6996250, -94121101, -77275767, 115250010]
private def lowC96 : List Int := [9275710, -5579191, 85502, -896474, -1445558, -878420, 549337, -1514656, -1360023, -2188699, -516201, -10987720, 4561425, 2955804, -2602461, -2133196, -5105953, -12375120, 8787600, -8736579, -6645753, -11166179, 9408558, 7717324, 22303075, 3369286, -6330883, 7527922, 367188, 7542393, 5254177, 2243400, 2352772, 752297, -1323441, -788605, -5451094, -33999829, 24133644, 657308, -272678, 4213513, -2872740, 2027308, 2499649, 8716493, 10379848, 961796, 7401678, 6753254, 16828683, 10210908, 17120494, 9071832, 60884328, 45649537, 72048008, 20629268, 43064543, 39590565, 37881523, 23829228, 17999304, 41223433, 11166678, -25031148, -4730861, -16888387, -22325472, -15871165, 32074004, 38690386, -35295435, -35339868, -12234695, -42871541, -24967633, -27099004, -16092031, -43516069, -32666104, -34350263, -11117178, 6739364, 7482701, -3017574, 2904910, -5245646, 4551707, 9170933, 4745886, 25057889, 283961, -13029856, -391910, -44090204, 94778652]
private def lowC97 : List Int := [14475061, -4321329, -1005210, -1996698, -3070828, 1547068, 4487190, -4722429, -7018758, -5707278, -5672730, -13649737, 6066546, 6561939, -5034590, -2861532, -12211710, -14853610, 700846, -15093774, -34424997, 12248124, 9645677, 12820695, 21440781, 4909345, -2621042, 7863755, 6405756, 7920573, 1711295, 137531, 7429130, 4454531, -1364720, -146228, -3531772, -7228206, 27487874, 3281961, -375319, 1563597, 6841085, 5540112, 1307606, 16412075, 31055790, 8260264, 16127962, 13085318, 39169078, 24668733, 29490780, 14390946, -508405, 106639396, 143363152, 63750182, 99997431, 92488629, 95607240, 56584126, 55013854, 69036365, 30874145, -57565875, -23317091, -31844659, -36787296, -48537304, 4310888, 54798240, 59920630, -72064636, -50150486, -83459763, -40773678, -42487665, -23423400, -19113549, -25963027, -44466738, -36571861, -22444407, 18418925, -20001741, 925023, 7094444, -6113279, 1900566, 13185226, 35749482, 33476599, 26259781, -215553, -16317478, -40429808, 63353901]
private def lowC98 : List Int := [-12071480, 5032127, 11349215, 3227898, 6064134, 2132339, 489824, -4579680, -4274124, 815101, 1474305, -3938185, 4122378, 4848773, 1268519, 2854636, -1798382, -2267483, -2370720, -1466777, 571158, 5927176, 3080197, -1530476, -127142, -4442217, -11114876, -6003040, 6447065, 4072696, 1406610, 2011296, 7975788, 4136788, 7567994, 6029983, 7580949, 8374014, 1619062, 321322, 10201851, -8882860, 3109244, 2983224, 7194864, 6441029, 5420910, -9871196, 9889876, 5703143, 10875217, 7595391, 9015878, 3626167, 2570874, 54466677, 74077651, 32114463, 51655022, 49276778, 51278331, 25554528, 22639929, 37392244, 14192255, -30232806, -13071144, -27206145, -17467534, -18332761, -21551946, -9146514, -14368069, -3993675, 6364475, -1081338, -33327642, -22666016, -14986590, -10432890, -23157725, -17514008, -5751380, -38277660, 740833, -17191081, -11504352, -4713013, 4792048, -188315, -2547761, 2577678, 16316116, 1891331, 8634802, 19666471, -1546541, -5100845, 51666966]
private def lowC99 : List Int := [-1312631, 459263, 1542192, 339807, 1007185, -664154, 155736, -722484, -133522, 18471, 595442, 265569, -539701, -674120, 711595, -324488, 408589, -427959, -265626, 739250, -140536, -32849, 404063, -1150515, -799984, -1131162, 481549, -506134, 863636, -545160, 885871, 47254, 638368, 651235, 1457741, 1515610, 1186701, -1105980, 165371, 105749, -490232, -348858, 1099073, -112413, 1544854, 4108882, 5439910, 1100569, 3039544, 1102820, 4844415, 2748264, 3348810, 1949342, 2261922, 9830890, 14010098, 5675635, 10416375, 11541160, 10552951, 5510083, 9805487, 14310959, 5807351, -5259880, -317327, -157655, 1207720, -3459540, -1361228, -1381328, -1172212, -3046139, -1645991, -1738869, -2592262, -5013092, -2247360, -1883936, -4923779, -4944251, -1425246, -2123429, 87783, -2655313, -2482783, -2106222, 837520, 328121, -1088656, 1305612, 493834, -288538, 2981474, 1812941, 1351574, 3028698, 111458, 25478652]
private def lowC100 : List Int := [2133369, 528993, -623874, -580730, -1278923, -502742, 271366, 937387, -314458, -773473, 202898, 562537, 1832668, -273787, -980910, -212024, 1017596, 1052261, 727699, 1098063, 750484, 3510540, 2074800, 2103414, -502124, -1570185, -2105490, -1650685, 662738, 1395645, -276529, 1195346, 2676181, 1669868, 2034504, 2370693, 2768022, 2808903, 317386, -778858, 862784, -1475083, 701903, 1945858, 4282624, 4024022, 9014017, 2104247, 3707053, 1476696, 5563395, 1804396, 3972619, 2613044, 732557, 24662853, 35285786, 14439948, 24905527, 30152549, 21369835, 14271858, 12177311, 16958388, 7316094, -12618971, -2579016, -9993483, -4283139, -16855115, -2417769, 2628151, 1017449, -4005564, -5208166, -1646620, -3789699, -10882776, -7928261, -6662525, -7120681, -9324854, -5861120, -11202910, -3859936, -12283651, -5001982, -6168701, -6551703, -4962583, -1184511, 5929224, 7401089, 1525305, 1444415, 2140381, -2481334, -501084, 3386088, -1816271, 35562646]
private def lowC101 : List Int := [231631, 1042470, 1118071, -643623, 183824, -81119, -843545, 1479305, -106397, -450048, 438664, 501457, 2087372, 643251, -782377, 587467, -264531, 116552, -598172, -1344008, 1704581, 3705695, 1150756, 2310977, 338914, -1100523, -2549887, -2403572, 507497, 1026828, 1248601, 1149993, 2972758, 1567425, 1733873, 2026382, 2023390, 3823374, 908974, -440510, -143059, -581130, 1019595, 623742, 2409471, 3320510, 10814320, -504661, 3778036, 1748635, 4728084, 2047431, 2995467, 1376657, 311188, 10623349, 36831982, 16690385, 26277893, 27354030, 25972142, 17332813, 15580406, 15527796, 6848883, -15086694, -2660450, -6046320, -7081581, -15980876, -341988, 2769329, -2330491, -780285, -4685329, -5538498, -4140869, -4611483, -9310946, -6491030, -9967746, -10710364, -9052043, -9038058, -1204556, -13043108, -10339476, -7918683, 516122, -1993488, -3030075, 8848675, 3615996, 1377086, -1549937, 5063255, -2897507, 3874401, 11970307, 678896, 5571996, 27264231]
private def lowC102 : List Int := [2005235, 574002, -2283191, -1771390, -147551, -128564, -229352, 511314, 266231, -513730, -1215253, -6603, -1461896, -867880, -323818, -179273, -680544, -659654, 922951, -939708, -44783, 1623793, -1856795, -7467114, 1001713, 2650753, 2661410, 1864970, -6018950, -3024615, -1485903, -1958727, 93218, 478493, 1362918, -2093716, -157865, 2068074, -2013063, -2622694, -3318952, 1492812, 320933, 1448748, -858141, 987548, -6886511, 4000593, -1421543, 625609, -57794, -418058, -1380369, -315020, -588965, -22208766, -30267588, -15312695, -24487925, -22358353, -25267472, -18262144, -20551055, -20010088, -9759083, 13470357, 5797828, 8863379, 7916275, 12481899, 4743889, 7243673, 1802877, 5148523, -3798860, 3373031, 5241874, 55605, -301603, -2654676, 10658287, 14435055, 5707037, 7439734, -3972862, 5575305, 3647331, 5596661, -12210588, -5616510, 1789167, -2177192, 468297, 1693292, -2973046, -1105916, -12237094, -1012693, -3817433, -2185823, 1505093, -1385261, 33687119]
private def lowC103 : List Int := [57125, 636656, 579228, -148394, 368233, -435977, 364109, 175731, -11896, -83181, 857345, 171314, -820090, 718062, 268666, -49879, 30317, 38622, -1624956, 249670, -317888, -1430888, -1937856, -249778, 338746, 698842, 325995, 1935242, -1700446, -2014425, -325, -1799508, -1420097, -1841699, 273780, -105902, -215482, 893365, -1113756, 133410, 137776, -669001, -1222936, -2050581, -1818921, -2331618, -2321108, 1058884, -366456, 96749, 219548, -111520, -1645203, -1296203, -332389, -8719328, -13908609, -5543399, -10264652, -9914905, -11676876, -9113409, -9386311, -9346754, -3614867, 10656830, 1594446, 2305050, 900346, 5960641, 1431906, 885254, 440384, 3160934, 1203799, 1261197, 2371541, 2752517, 1400824, 642391, 3967123, 4683188, 398491, 802847, -659338, 2385956, 39190, 2170603, 2910619, -405204, -392988, -2302852, -1125435, 571012, -643091, -1920440, -2607995, -1000725, -403963, -1280630, -1479729, -1019217, 2375742, 20658241]
private def lowC104 : List Int := [793768, -113060, -1422245, 445531, -784604, -365592, -228559, 828014, -39423, 150229, 1741880, -101233, -1022225, -106384, 43929, -6165, 128718, 707801, 666672, -339016, -201572, 152654, -2451625, -1080800, -247377, 680512, -179205, 1102817, -1342606, -991495, -721296, -114579, 71590, -233237, 524673, -810925, -805272, 1248964, -869078, -1752672, 37993, -492159, 1147494, 1188504, -1476604, -890118, -1386240, 660408, -184817, -9671, -826762, -877207, -1737298, -683732, 1159522, -9288627, -12966765, -6600158, -13063004, -12086167, -15198556, -11255609, -8310428, -9372606, -4729889, 10145034, 1965116, 1682292, 2548692, 3263147, 2567135, 3535968, 1214972, 4031394, -586371, 1852471, 2324954, 2033608, 1274434, 956978, 1249882, 4285910, 3559799, -1352498, -1295169, 1730111, -704182, 1460948, -1752047, -401288, -806053, -1513661, -663951, 96715, -651327, -689369, 1232250, -2229859, 1260863, -3199756, -2286024, 994473, 373073, 714004, 23666176]
private def lowC105 : List Int := [3203447, 797187, -931957, -959490, -1851329, -722088, 977811, 1421164, -139197, -732418, 301701, 815736, -4916054, -2726296, 1105326, 21510, -265949, 551659, -1383205, -74864, 487164, 2211731, 805386, -5645148, -1894159, -316104, -307736, 535746, -5837004, -5383890, -1300208, -2074203, 193898, 1558860, 2595101, -2777169, 1888696, 81162, -1335157, -2307026, -3048220, -4399782, 1081865, -816155, 5107498, -124938, -2308825, 3230089, 1627722, 3801684, -189745, 898441, -1898085, -3696688, 528745, -33596323, -35541737, -20301267, -13206178, -32286030, -51378101, -34104308, -41619328, -35935038, -14916323, 23924350, 5594549, 6081669, 5725586, 11483735, 7934926, 18134927, 6912864, 22493080, 29319, -465276, 4814824, 1586476, 3669842, 5818585, 3660781, 8753038, 18785392, -8417718, 5075632, 15491393, 10810051, -802010, -11863828, -5926708, -6665960, -19960980, -2356691, 984468, -5228715, -10029261, -12429413, -1543137, 3323327, -2539567, -8307362, 582165, 10477945, 698744, 370005, 54263351]
private def lowC106 : List Int := [14343158, 2750955, -1657681, -4092065, -2919238, -1246900, 1351522, 3146519, 4743942, -2232562, -4189907, 3671555, -21359285, -10091312, -773868, -8259811, 3904796, 3273712, -5723401, 2270523, 3564904, -33694244, 8858314, -30368341, -4542281, 9059515, 12539753, -10006326, -31406349, -18682899, -9514502, -18710037, -15241182, -6811568, 1607256, 2573700, -4035719, 4550088, -34775901, -17271746, -13957897, -18147662, -3024489, -90999, -8729520, -13708631, -31023545, 9551892, -6039464, 6374736, 964443, -4972887, -9563608, 1009856, 5063265, -16604271, -124047408, -60673019, -87653488, -85232675, -107640839, -131043780, -80244230, -90784770, -47310190, 60125240, 24632307, 41120052, 19886221, 40832531, 8635519, 22778033, 16472354, -2499550, -12022253, 13818857, 35593122, 31488435, 16767172, 15298911, 28826698, 30743773, -18108941, -79548573, 84309649, 1573216, -2389424, -15410406, 21468481, 388285, 1040575, 14980634, 5746356, -35310620, -15046703, -16717704, -17876593, -3006754, 24497355, -7642543, -5278851, 13935625, 17030123, 14610948, 5460328, 17888346, 102228692]
private def lowC107 : List Int := [9526989, -241699, -341777, -784769, -1579016, -1469148, 8202603, -14240281, 7001546, -2434445, -971771, -807545, -13401973, 2849954, 2908427, 568173, -5547435, 2228652, -5714796, 1955172, -14564362, -3095653, -17017045, 4014133, 7422462, 1499332, -2760915, 8763695, -3219724, -3845746, -1659795, -884239, -11159325, -7869042, -257336, -1359494, 51044, -4330974, 4318953, -3228208, -3409957, -8024024, 9532032, -9899716, -4415951, -6953236, 3861834, -685064, 2418082, 5514777, 11323200, 8293496, -3198660, -1467137, -6293104, 3949374, -61160965, -25549503, -43863293, -42318931, -49690416, -40502432, -36296594, -41982429, -27997306, 43331730, 15890313, 17435458, 19246471, 39142101, 16293979, 6055565, -1409007, 33565251, 5562878, 1561648, 9642410, 6644785, 11890153, 20243276, 9519168, 23349918, -11610667, -10498929, -31338710, -10408624, 1969094, 10837361, -7570845, -892637, -2133556, -154921, 7994700, 3902783, -5562397, -4371045, -5398997, -6572195, 1813545, -13845701, -7913244, 6825628, 12329844, 3780718, 6834655, 19818896, 13598236, 67223772]
private def lowC108 : List Int := [16949534, 3022591, -1296653, -1742214, -3769064, -4019455, 4683916, -957472, -4728971, -2474495, -5127326, 3433605, -39276970, 13809362, 9568702, -3111106, -3946137, 10157807, -7481852, -44810, 5569392, 2826965, -31831494, -21191820, 14232059, 13172530, -5365401, 32204820, -12101040, -16655724, -4379120, 7015726, -21573546, -32505507, 10235817, 4167749, 389905, 12162245, -7942154, -7237208, -239395, 13447977, 27835595, -425838, -3990106, 6444050, -12209364, 8330672, -3242643, 6568482, -1118143, 6577656, 2125842, 5399249, -1404529, -6221230, -124942494, -43392136, -72849653, -78698187, -110319374, -86906223, -87691075, -80565799, -16997600, 94109156, 37635191, 54987288, 23775248, 74278568, 20391656, 28657921, 22595491, 75715663, 3428574, -1460040, 5016807, -9338290, 8613736, 36045178, 21469127, 37047012, -6248829, -11571395, -69742336, -25881432, -56346384, -49099717, -12699507, -12275099, -14890714, -8130661, -11866529, 421577, -6121992, -22496053, -11628639, 8243723, 4242649, 9307731, -9146794, 8484614, 14498152, 13525344, 8582794, 22891381, 24127828, -25041539, 99370445]
private def lowC109 : List Int := [4993586, 1150846, -1127553, -1105124, -2461329, -1144624, -805719, 1489579, 1303832, -1285352, -203524, -4848119, -2308836, 7481340, -1647102, -1344877, -79179, -2353028, -1400028, -6182649, 463631, 6614655, -15661576, 5400344, 5756642, -406415, -3477346, 4135098, -2451464, 327333, -1747004, 2198068, -21242646, -3735012, 1640250, 3265900, 1620599, 5050619, -1122268, 1496284, 824071, 1918278, -1761448, -4016487, -3634527, -12629207, -31301530, 7035574, 2629928, 5645307, 8022007, 6574712, 3991020, 6117277, 4781508, -15793885, -3628401, -31654526, -48263713, -48414732, -51570495, -59156653, -47300604, -36470403, -14288620, 26391302, 6906892, 18577963, 2988692, 26351341, 16767388, 21129727, 17087619, 42516686, 13282641, 3516432, 25547885, 15144767, 12178957, 15056217, 30454725, 49267121, -3683178, -3563616, -17615781, 269917, -12249108, -5500193, 10209927, 12597579, 17204534, 17197744, -29686226, -18575631, -7431812, -12728639, -4848959, -1765630, -6995337, -6604780, 1057607, 4123394, 13237727, 3724048, 2712518, 10917971, 5919742, -851068, 10336393, 40083141]
private def lowC110 : List Int := [2127732, 402744, -604884, -890902, -1000098, 492629, 574151, -270989, 149276, -1497518, 25341, -2025005, 694121, 1943798, -1169132, -648415, -660401, -1168452, -1552684, -785301, -3034506, 4856764, 331030, 775345, 853298, -1831383, -1542066, -332731, -3756256, 1187162, 630501, 318600, -4336679, -2734671, -2033165, -945712, 2569199, 1373771, 1813860, -50658, -198932, -2065353, -6381330, -2789455, 2110437, -5313955, -17224666, 11112404, 4017956, 4484881, 3780988, 3009839, 3566657, 2467408, 2120068, -6579612, -3849706, -3107165, -27995999, -25460933, -21244323, -32010300, -24379644, -19499834, -6169346, 9964157, 930110, 12227004, 1515456, 13909296, 660960, 10132441, 5050939, 23505642, 5130548, 3062772, 9729774, 5702804, 3485687, 3816135, 18994407, 23872400, 341778, 3170944, -7071752, -1159528, -2826318, -396692, 10631010, 11929634, 4247859, -3827404, 8452626, -15860442, -9945903, -9164601, -11627778, -3963676, 1176837, -2017492, -5394417, -2010667, 4525599, 854794, 752749, 8891461, 3077860, 2290505, 3708559, 10420213, 32654643]
private def lowC111 : List Int := [2133124, -1080343, -484884, -598974, -1133006, -256102, 581674, 663325, -9893, -265950, -168784, 350610, 460744, 874580, -2195222, -191584, 1394226, -1340045, 8677, 333971, -394221, 950183, -1853654, 1896440, 28255, 622764, -2868150, 2812116, -2556152, 204089, -1094437, 430505, -1995192, -511216, 328556, 421303, -326139, 220423, 307757, 1037416, 1280159, -616412, -1090283, -620170, -384988, -796416, -7052465, 6021356, 3052374, 2472522, 3623056, 4361687, 4471639, 1462304, 1080013, -9970785, -7666143, -4796009, -28057439, -27091770, -17802411, -32362386, -19794190, -26150700, -9540065, 9345571, -2361731, 10432746, -5336652, 11273841, 3253571, 4984602, 804171, 18268720, 6198237, 4198432, 12825266, 12809361, 8790355, 9740891, 19953762, 28383958, -612838, 788982, -6080430, 6880229, -8086489, -3627376, 10486129, 12022585, 5551093, -3208113, -4440609, 1643266, -9266600, -11265785, -7470950, -6829942, 203712, -7717385, -5303281, 416416, 2847930, 3395553, 3550212, 8281571, 2724549, -394072, 4706908, 7181800, 11009095, 33585279]
private def lowC112 : List Int := [1309617, 778349, 172880, -493687, -657797, -451048, 592004, 414295, -9836, -169973, -271478, -429215, -3887862, 5988941, 195202, 90525, -1090725, -2157598, -1006258, -429799, -145895, 2940229, 305065, 855246, 375099, -132908, -744780, 1252684, -627062, -1219571, -913435, 252768, -4271467, -4257837, -4012285, -1808094, 3168076, 3252563, -28543, 2225382, -809638, -886222, -1565697, -608482, -380695, 97030, -3262455, 3306609, -929210, 2093487, 1858898, 1499874, 620580, 630620, -129870, 687271, -1353416, -568386, -25453070, -29401085, -26865567, -32241311, -23034159, -27102837, -10835819, 11404401, 415901, 8381959, -2872632, 16548141, 152798, 1570744, -1386402, 9681367, 2418937, 4425908, 10782219, 12496539, 9039349, 11663204, 16227302, 26253974, 209287, 1536770, -9708983, 8094647, -55690, -6654331, 3069964, 3719417, 5745529, -8335504, -692637, 1360387, -1273685, -9598438, -8815520, -6596943, -6433403, -5491710, 2256156, -4983632, 2385142, 2605582, -3533316, 6914846, 9117648, -1936606, 136476, 904476, 3260749, 12083165, 32099061]
private def lowC113 : List Int := [1273314, -1972083, -2363996, -433919, -321466, -108626, -646896, 2513007, -847376, 270748, 177546, 631559, 1931995, -4632037, 16849, 135039, 174811, 1711340, 1909952, 626311, -193702, 906187, 1699109, -687680, -1697974, -686876, -365662, -2530614, -1035337, 2834310, 100201, -1138483, 509078, 1680729, 1298239, 1500619, -149185, -6170500, 494750, -687483, 1164940, 101278, -304438, 2635004, 1994559, 1584097, 257138, 1947686, 7293079, 2909960, 2577260, 84815, 89039, -1629606, -6441295, 1877057, 4323850, -104692, -304498, 28215015, 43430759, 31662757, 21605551, 23859198, 8848102, -14684651, -1249501, -6322533, -3785160, -10505505, 186379, -2758116, 1569780, -4279443, 4867673, 4614415, -3198400, -8169980, -3148043, -7333185, -12519893, -24864030, -12278182, -15116483, 11835149, -7359818, 3982213, -4495780, -5968138, 3103453, -1169769, -1025200, -4684494, -1673604, -932958, -4220291, 11817436, 2034385, 3660430, 4680059, 5152822, 2093893, -13374578, -9268834, -2680420, 3059319, -12914867, -3469890, -7467949, 600886, 6827730, 1089181, -6087229, 30731864]
private def lowC114 : List Int := [1768129, -263161, -2480667, -422188, -801221, -427379, -465093, 891545, 41832, -465548, -305565, 611239, 1902486, -4612164, -481382, -599674, 365562, 540015, -517870, 1239603, 607340, 651355, 3711898, -2179661, -1017378, 490960, -113701, -1729909, -788047, -520732, -1077389, -667814, 1297267, 2250272, 2636661, 1048234, 2142560, -3534165, -1383537, 935105, 402192, -2396394, 469844, 184467, 1975199, 1331556, 1287501, 2147409, 5091244, 7806368, 1592268, 1558783, 627058, -91255, -11323782, 820856, 2725008, 2422226, -1552097, 22966606, 42910490, 34607482, 28415093, 20677438, 4673236, -12964516, -7907697, -10476318, -4367276, -13327634, -2364762, -2337478, 1924949, -8114435, 2249737, 3397030, -1322534, -8689481, -3505289, -8638734, -6662850, -23110491, -18585364, -10324469, 4522894, 3257013, 7236905, 371489, -2531681, -4878660, -2332285, -9576369, -952773, -157476, -1264026, -1756869, -10368080, 2160834, 3429892, 3616731, 11263794, 1048983, -743031, -925117, -8177401, 1797675, -6752296, -9048603, -9765119, -4693740, 1410846, 4679573, 9211441, 4149526, 30862128]
private def lowC115 : List Int := [2132839, 537591, -620520, -579954, -1258313, -534355, 571332, 1163487, -112124, -141978, -713952, 783312, 1935035, -5565200, -183478, -418609, -54837, 1497422, -2327474, 1903497, 1172583, 1734678, 3102839, -784587, -1648178, 21304, -108582, -2637885, -1508598, -1514819, -770539, -641402, 961345, 2285221, 1927829, -4576845, 1117088, -6308797, -3486577, 4298898, 2840092, -1700570, -2227727, 360116, 596419, -379405, 1063854, 2232655, 5628850, 7007455, 1118005, 956027, -39131, -1262257, -6690809, 310143, 1100635, 1323593, -1914172, 28035463, 34400229, 32677844, 31451291, 17844047, 3879726, -10969579, -9246262, -12353873, -4800770, -16672965, -4470956, -6485635, -2036362, -7001605, 2203088, 11214760, -409370, -4779761, -6076977, -11010671, -6792714, -21710905, -15023168, -9016054, 202700, 2053334, -265187, -1807744, 3261071, -3491415, -4212388, -10089306, 738383, 6888, -816472, 1274653, -5062086, -6252308, 11017178, 2409601, 13940976, 7787897, -8727951, 131515, -1819070, -12213593, -4425035, -7247718, -13814333, -1620055, -976351, -417092, 8151246, -10183663, 2898084, 37562983]
private def lowC116 : List Int := [2436963, -1292186, 7446883, -36705, 2644611, 801144, 6190848, 7829090, 4531518, 1944591, 1315833, 9351855, 9813567, -8360738, -2850296, 560206, -2936421, 10623601, 7998214, 8279741, 4090420, -8587941, 6257172, -4853169, -9905992, 10929, 5351581, -5846481, 9860300, 4702568, -6835768, 2909917, 9051322, 8278760, 7382046, 4397916, 8523606, -27426816, -14788785, 8354619, 3604966, 3743331, 12851382, 13687861, 11742567, 6551183, 7682436, 10656143, 7309586, 3008596, 10010032, 8293700, -1701802, 1191202, 288949, -13335470, 5474786, 5422225, 6449863, 13326402, 139853392, 132224278, 108408489, 104931182, 42495456, -41262646, -17204828, -29005684, -5537899, -30526078, -3050880, -31425916, -12490865, -55107380, 3731420, 10381999, -5823682, -7383985, -14049879, -33207833, -23825428, -80314570, -13769959, 32111111, -21325857, 21723536, 38311573, 35816756, 1245131, -3295446, -1823602, -20430706, -12488103, 1562130, 18521346, 23947495, 34607764, -4159769, -34088622, 7201434, 2388082, -22410989, -36864894, -12206941, -10638305, -75240635, -59362759, -5777172, -47994297, -10515808, -8927897, -16620685, -1013417, -1451774, 6507695, -11715672, 51841738]
private def lowC117 : List Int := [-3016376, -3932528, 8487275, 1999247, 4278616, 747667, -1772696, 3550609, -6289189, 1023157, 2540365, 2697301, 5467596, -1687350, 1859496, 1321669, -715736, -2575252, 9399338, 5600480, -1729465, -13587064, 3376695, -1842733, 135668, 1713274, 2404055, 4115278, -1594197, 3181634, -2377327, -507059, 2636556, 4534512, 4007221, 5512734, 3815570, -13000561, -5142500, 806609, 429898, 617831, -3443082, 7669169, 2083575, 3656304, 2636219, 5360907, 2200754, 2140507, 5400943, 3994151, 2344881, 1371933, -1774165, -14145176, 4943495, 5029842, -210814, 5242325, 82429432, 44636937, 72791698, 55126346, 20224253, -28316990, -7368380, -12577519, 903022, -20576472, -8799427, -16397789, -435547, -28798416, 10984738, 11521091, 1009950, -5132577, -2228426, -20333441, -9672221, -40016417, -1103425, 21161933, -911975, 5228372, 9755397, 15387472, -8552607, -910640, -448807, -16708587, -10865108, 5826549, 11979940, 13597671, 4468632, -6476546, -19930263, -624478, 1787722, -13160799, 3626210, -9728826, -3127615, -33081425, -30051045, -18377917, -9716532, -8622806, -7777178, 5631779, -5785718, -110902, -13329444, -2937967, -24370024, 52305447]
private def lowC118 : List Int := [7524613, 1729660, -1686946, -6270235, -284601, -51844, -2212150, 6121479, 2878709, -2351408, 1326864, -254059, 7147323, 543259, -3564564, -1330783, 1763944, 2077910, 4806150, -247703, -3142344, 13524919, 6439354, 7053387, 1488537, -4444719, -2262766, -3744193, 9494868, 6887100, 547622, -4905687, -487209, 356626, 5546103, 6985307, 9218505, 7478520, 4645514, 2202623, -1924740, -4053437, 5906977, 6438346, 2705341, 14093289, 13594769, -4340995, 15019708, 8608769, 13130526, 8588793, 9897606, 404940, -7772, -17760303, 5083695, 8624554, 11067214, 13785344, 2374993, 129409738, 113291019, 78366453, 27511088, -34160234, -17127902, -43105695, -13299679, -51063506, 2329255, -8058087, -6453981, -14527198, 898298, -405384, -21589479, -24787273, -18968901, -22714956, -34504518, -61176896, -6240027, -696315, -1818236, 43131831, 36577508, 20968305, -24531086, -15297168, -15529402, -58514662, -11211418, 8694887, 5277169, 21057114, 4280815, -23232799, -24704408, 4939701, 1682643, -12255830, -19490982, -13412890, -6103262, 12954893, -59666159, -4295261, -37432072, -12411221, -293634, -2480262, -11230785, 6459155, -7495547, 7923335, -11550677, 9001596, 58886132]
private def lowC119 : List Int := [2272421, 435706, -724769, -618919, -1333662, -229654, 236557, 448571, 384562, -626976, -225319, 324674, 1735146, -2496158, -1449620, -1090443, 192801, 256087, -117729, 793463, 677812, 1508630, 2996946, 430519, -743172, 2183783, 630993, -3561508, 450723, 661782, 679402, -169213, 706127, 1665395, 1267118, -3710755, 2295523, 1844583, 327481, -1285077, -1115860, -1029972, 811309, 810796, 1924090, 1022589, 6723551, 2241960, 3784973, 6003669, 4764272, 2296453, 4464931, 671056, -156086, -643083, -3512872, -4195368, -788162, 80346, 10240190, 41172970, 37694707, 26973427, 8913542, -12357650, -4870581, -15900468, -1778467, -12992085, 1687466, -4256898, -2760757, -11507753, -1637849, 1306005, -5421740, -6144084, -3638777, -7821043, -11153110, -22938654, -4654499, 6112, -1516529, 10927982, 6020864, 4296351, -6149677, -8624263, -3734574, -17479608, -2551105, -2042934, 3709541, 2920439, 186921, -3351337, -2426236, -5573646, 144839, -997631, -357611, -1689484, 2829141, -3094985, 3177041, 3432651, -9433989, -5216237, -8431082, -7721445, -2719804, -1963289, -2831723, -2141852, 2236353, 6992519, 3346624, 30282093]
private def lowC120 : List Int := [2150384, 519217, -585679, -608384, -1262790, -516939, 585309, 804356, 30284, -264003, -115258, -373088, 1159299, -1893087, -470968, -661752, -331394, 988707, 61964, -127902, 657554, 2110514, 2263034, 813162, -991559, -740961, -1131585, -1788048, -387371, -124627, -329564, 55128, 1802704, 1493099, 4294701, 1425510, 1703873, 1713690, 241231, -1093206, -756767, -298951, 1160565, 1422157, 2207332, 1721644, 6799545, 2375754, 4110092, 3879546, 3991784, 4844212, 7062438, 714658, 700601, 1025511, -9493473, -6259420, 2798541, 2539437, 12095315, 38408509, 41512262, 24623293, 10064859, -11821528, -4255343, -12084548, -3786253, -15698268, -484848, -3621535, -845955, -7916843, -1179064, 1243147, -5708914, -13188856, -4918018, -8155030, -11301175, -23999598, -2182000, 3576427, -3735297, 10105743, 1442611, -90663, -2454555, -3676464, -5847067, -13836621, -5077681, -3437316, 4738751, 1331549, -1230717, -1685806, -2375406, 2140300, -1912133, -4513534, -2457176, -1073484, 493548, -5472388, -1787545, -3365582, 3521782, -3987070, 247956, -7892874, -4239644, -3139943, -314752, 7346, 3030475, 4237383, 2350221, 8685377, 26997633]
private def lowC121 : List Int := [-3616845, 2129483, 3752497, 788256, 1822421, 589069, 358238, -1648874, -3106791, 165610, 17712, 198561, -3780394, 6324992, 761584, 18886, -2178583, -1350751, -1593178, -3319106, -174103, -2847846, -255341, -622134, 402138, 432983, -243514, 1881390, 1264101, -870569, 276769, -1190293, -4357991, -2612430, -653152, -31048, -1750858, 3685279, -1039722, -150316, -967931, 123530, -424709, -1414858, -2537827, -1328415, -2428200, -11600517, -10764499, -6308811, -8625108, -4968699, -6392650, -2450824, -641116, 950519, 2648419, 6946991, 10319327, -11663251, -22340475, -17378587, -38428714, -25333111, -10266329, 11367932, 5692121, 10734727, 9629884, 18325056, -2798217, 31346, 424453, 2323146, -862140, -4659237, -743400, 8675714, 3901024, 8818572, 3263888, 14634677, 10639307, 2687293, -7053084, -6431230, -237571, -863317, 664324, 578893, 3129480, 19543318, 8270118, 4409131, 3260318, 4666982, 5481598, 6966675, -1804432, 4202809, -75606, 766359, -4786394, -171549, -1863490, -11171596, 5786238, 483214, -1229428, -6971473, -9321590, -3339214, 10829540, -7431958, 2898978, 4583930, 4889098, -7997462, -10082659, -7457216, -2716926, 29551851]
private def lowC122 : List Int := [-1827823, -634426, 2352944, 562621, 1032407, 234032, 278693, -659670, -363650, 259827, -546340, 808109, 149620, 1576242, 628909, 427317, 1446230, 309319, -284216, -1308138, -467045, -2550188, -6399621, 788036, 2403611, 2518109, 2079456, 3214775, 480776, -800708, -527660, 334064, -3478507, -2678988, -3521308, -1175260, -4325985, -742624, 3017628, 1024432, 674853, 5236567, 2646906, -4949158, -5403808, -4908516, -5868893, -4713205, -8737305, -9181397, -5272111, -8979545, -6348707, -111531, 2745774, -729570, -1990881, 1844311, 11069070, 4225537, -16255871, -16805290, -38692847, -23835164, -6639292, 17014843, 8118140, 11575319, 8564769, 17939237, -1176647, 237790, 372822, 5030733, 2285247, -2189885, -327189, 6273745, 4410054, 9426636, 6821327, 15795079, 9847002, 9728909, 459591, -8494847, -2539564, 3364281, 2697660, 82073, 1488625, 14682364, 4444277, 4757561, 281242, 5114155, 2921447, 4438354, 1044647, 1487281, -3683291, 2980665, 805057, 2930325, 3072615, -2731881, 36899, 3426897, 5299141, 1790858, -3539912, -2553135, -6827902, -2367683, -3292991, 440075, 2039013, -5357629, 789976, -6514086, -6313399, 1230407, 23801605]
private def lowC123 : List Int := [-1469132, -668921, 2325757, 355126, 827947, 211058, 116349, -490215, -232862, 288856, -422373, -1955272, -2564531, 3189627, 878924, 879869, -2908, -1049908, -165647, -1630369, -2031213, -1851423, 1231993, -3362264, 2259238, 1655979, 1165422, 2887735, -4169098, -945313, 313082, -861034, -1719704, -2399857, -5722036, -4228289, -1766764, -687302, 2945731, 20743, -310179, 655348, -8327490, 2779055, -1371213, 755291, -10811965, -5579890, -7034678, -7081281, -5145498, -4520764, -4269663, -1398108, 4233594, -4378983, 474255, 3516235, 6192187, -2015757, -6915924, -12820137, -40844093, -27444776, -11350467, 13624961, 8467420, 14723025, 12391167, 20710912, 341534, 2360717, 2924356, 2961810, 1013889, -2231050, -1082337, 4366093, 1858499, 4231956, 5647588, 15243071, 16715570, 8426874, 9129524, -11645650, -4754286, -1850764, -3743318, 5086343, 1858118, 18941415, 1695598, 1140594, 276183, 2643899, 17071283, 4628393, -2331600, 1356348, -1158894, -1238624, -3963555, -4882495, 2734593, -2158688, -7193854, 5500594, 25788, 3923524, 462590, -4606513, -8788005, 6104365, -9486864, -4972524, -3935010, -2499472, -2833865, -4523402, -4559017, 6132793, -1445950, 30584199]
private def lowC124 : List Int := [1803006, 437186, -1053543, -1335119, -419948, -189451, 226581, 645939, 126595, -273577, 140356, -230557, 1372184, 284043, -972404, -700411, -524516, 637927, 341585, 1237315, 305358, 2767160, 1817914, 1617525, -431360, -1533803, -1453725, -2328707, 2193890, 1334712, -855268, 930015, 3348330, 1336751, 1722290, 2010050, 2673242, 2405371, -97822, -968821, -1139654, -3030228, 1939835, 6026766, 3033760, 2277606, 8057741, 2325040, 2964811, 4065383, 3389765, 2634904, 2516742, 2071878, 1789002, 10837892, 6393933, -4399573, -4574500, -4425815, -3457999, -617568, 49814197, 28379597, 8590155, -17079339, -7406729, -12595520, -6955495, -18664211, 1505294, -331359, -2831435, -1416360, -1664655, 200921, -2092480, -8770918, -4231986, -4278309, -8699990, -13263204, -3299884, -3273120, -4789898, 11085521, -3557578, -5509026, -5150429, -2599850, -3503214, -18966700, -4582681, -4492124, 2233087, -231228, -1318551, -9654940, -1098188, -5051295, -2788619, -824616, -96426, -2536023, 4685991, 6718448, 5658754, 1729818, 3788267, 271210, 1504355, -3284604, -2920755, -1544568, -12697356, 309989, -6149237, 11049349, 7493909, 14147339, 8932851, -7466228, -6127036, -2369819, 27168328]
private def lowC125 : List Int := [2132545, 538906, -1123576, -933304, -978671, -371995, 399986, 991916, 32982, -204769, -76071, 225349, 1758411, -150969, -891210, -660776, -723372, 1244131, 182379, 774052, 715023, 3237198, 2171002, 1988161, -585923, -1653892, -632535, -2615281, 2676452, 1359221, 581003, 1050533, 2832801, 1560781, 2117385, 4997239, 2212918, 2151879, 186334, -642175, -1157019, -4587257, 2661747, 1650956, 3809914, 3362684, 9223407, 2123905, 3281626, 2449123, 3947764, 2651174, 2666137, 325666, -92024, 11519627, 5885846, -2946488, -4219971, -5154120, -1747209, -1345840, 49881580, 27458776, 10919744, -16321750, -1555024, -15895293, -8554016, -18547787, 1577523, 1002673, -1449294, -2419300, -2272818, -2693255, -3416272, -8726988, -3382583, -3953055, -8118123, -13233200, -4693460, -3157095, -3366791, 12288692, -2536790, -2714557, -2931852, -1471023, -3742749, -17312234, -4307160, -3289943, 1716054, -4051616, -826406, -5551901, -6686439, -3692008, -3522441, -5536861, 3036212, -1122446, -1165665, 4062406, 8120472, 2936146, 7736737, 3938574, 1975543, -2925472, -3685223, 1006569, -10696461, -4915362, -9347726, 14900271, 8801428, 13854958, 10656666, -5068013, -5651382, -2287794, 6049463, 27436163]
private def lowC126 : List Int := [-4665944, 1805857, 7042642, 1146744, 2124968, -1381286, 2471205, -980450, -1323509, 3987761, 1717894, -2361531, 4804709, 34122, 2254652, -1756128, -3524864, 4455424, 1783243, 483504, 1919906, 5123685, 4002444, 1795651, 704323, -6463367, -6121543, -14059655, 11104477, 8319003, 1494037, 4056721, 9452936, 3747685, 4893759, 5504711, 8460625, 7584659, 333484, -9659381, -1237731, -11277926, 10071858, 9173565, 12030148, 12137434, 25688286, 3125671, 9529079, 2278706, 6986324, 5149115, 4784289, -2058365, -3746473, 2477501, 6463261, -2098983, -8295784, -1790023, -337779, -19101957, 73314785, 69276135, 23422575, -41629432, -18836346, -21161134, -19202956, -46189672, 7558804, -1142911, -415117, -17325499, -9410628, -6164805, -2850593, -16262482, -6433911, -10320269, -17379700, -26904965, -8433450, -17075106, -28597670, -1798963, -6602787, -1187581, -2152649, 1703035, 1659007, -14347046, -8407751, -7611591, 1964404, -22046346, 2492329, 14188535, 7210374, -10113389, 1433533, -3004, 5244655, -88093, 2389896, -1599462, 9683897, 12500706, 13854129, 8764449, 2318962, -3791265, 11800954, 831208, 9731414, -12432067, 19623555, -4186414, -52334418, 28137165, 14541852, -17951586, -18525853, -8106110, 14916547, 8527669, 49679749]
private def lowC127 : List Int := [13179258, 2635309, -1845590, -1975601, -6755697, -3920021, 10649317, 9774677, 1775256, 7674515, 2970012, 5036790, 10274571, -4149000, 3844131, -8422279, -13115952, 21882789, 10378822, 9100764, 4651491, 14602517, 9285719, 20469351, 802877, -28008007, -8472433, -25237734, 35747554, 19355977, 4656064, 13074211, 19355170, 8476067, 6106431, 8652962, 15006104, 10670430, 1863804, -3972120, -13618875, -25082963, 32156772, 17875897, 26482247, 20907044, 60369865, 8142167, 25173540, 4413131, 21758854, 15173002, 10534446, -4602459, -8222617, 2876064, 13084860, 250886, -18066778, -3891447, -5938821, 1192563, 3798064, 175032050, 73358515, -71044335, -36216509, -46620287, -43705521, -91963949, 16171700, -683382, -753663, -31298146, -16626405, -25082373, -2897052, -6917458, -19383363, -19867598, -24350410, -46991156, -53959809, -57350127, -57808837, -30707504, 17997998, 11486777, 10697860, -3218558, 969314, 6439940, 3197769, 7475214, 1302444, -11771947, 358788, 8339581, 20165199, 8138363, -2480089, 2442758, -10108913, 3265103, -10168038, -32767341, -11958182, -9965285, -10473687, -26933851, -3227221, 11874413, 12396894, -839037, 26347928, -1343757, 29368367, -4433183, -36218171, -22719585, -9151464, -1839799, -2769226, -24615718, -10729111, -11353241, 20344826, 68448158]
private def lowC128 : List Int := [9297024, 1598279, -532338, -8254376, 3420131, 208271, 1544077, 163927, 4702266, 610594, -173289, -3496562, -12053067, 4091209, 2814369, 154607, -7331521, 5118217, 1830052, 3232391, 5865836, 6817237, 744520, 4409982, 121932, -3591971, -1983966, 1319726, 11314204, 5991511, -1960229, -3409718, 4677048, 241090, 6239512, 7171668, 10555869, 8985152, 371363, 4776769, -3213292, -19290360, 16048625, 10209336, 10612522, 10765753, 23652313, 7520199, 9700946, 1749871, 13386750, 9158329, 5457803, -1912296, 586172, 5164438, 6847220, 2150589, -531724, 1339798, 20790590, 13525770, 17625408, 37480184, 34918639, -44467753, -16212204, -20679979, -22952189, -33000086, 3695585, 7231275, 10066181, -9324945, -8369226, -13285090, -8728428, -15015413, -3602351, -24418, -9939848, -17627430, -14996588, -6278118, -6232951, -5805928, -6531498, -7944630, 3575114, 658965, 451115, -1226535, 2211646, 555791, 5592316, 19066813, 8428082, 793738, 8372568, -1024047, 6256379, -2861850, 2431481, 424600, -2839079, -3573468, 7068089, 6848040, -6265792, 3067990, 1132017, -4461913, 5203623, -6965906, -4773339, 3762728, -13682103, -7190348, 21069496, 1826353, 1643288, 6743166, 11449958, 4346608, 554625, -4213399, -11026553, -35063047, 129437846]
private def lowC129 : List Int := [17016748, 2988287, -1334254, -20530397, 9510631, 2043057, 4320612, 136492, -6981587, -1053923, -587184, -12415475, -17545836, 5670537, 1561681, 1158360, -10042351, 14493225, 7311733, -92654, 7422096, 12527480, 7699283, 6351548, 971470, -5037853, -12737564, 189944, 13555892, 14376370, -8495894, -27656624, 20022110, 9137490, 12901239, 13617146, 17806686, 16083509, 1082680, 4632090, 1501679, -3395108, 35772571, 20252222, 23649898, 21548142, 39969550, 15467717, 23245800, 4396428, 26076996, 17285466, 14655406, -3286364, 13408835, 19215878, 22239550, -9106037, -5058473, -2446498, 47784869, 30655178, 45049959, 71895729, 26352735, -92920447, -31404107, -41878362, -43213527, -47558462, -1781911, -3683624, 1702753, -17129816, -27487579, -31789130, -13266429, -38082843, -10322375, -12858856, -22629486, -42186008, -37096430, -13250854, -9956437, -7404540, -17640886, -10303403, 4221271, -866294, -5018218, -2420761, 16022799, -19410375, 5905271, 19413741, 12237509, -721762, -15075534, 220103, 14976695, 10271565, -6767895, -468362, -1351032, 4876018, 2498310, 10365701, -189579, 9332490, -10767551, -1728684, 3929116, 2517501, -673388, 6645763, -1012209, -5279160, 23153809, -3837488, -11547252, 9891256, -1957380, 12652624, -1620644, 83651, -8031945, -12566191, -9353608, 53035229]

def lowCholesky : List (List Int) := [
  lowC0, lowC1, lowC2, lowC3, lowC4, lowC5, lowC6, lowC7, lowC8, lowC9, lowC10, lowC11, lowC12, lowC13,
  lowC14, lowC15, lowC16, lowC17, lowC18, lowC19, lowC20, lowC21, lowC22, lowC23, lowC24, lowC25, lowC26, lowC27,
  lowC28, lowC29, lowC30, lowC31, lowC32, lowC33, lowC34, lowC35, lowC36, lowC37, lowC38, lowC39, lowC40, lowC41,
  lowC42, lowC43, lowC44, lowC45, lowC46, lowC47, lowC48, lowC49, lowC50, lowC51, lowC52, lowC53, lowC54, lowC55,
  lowC56, lowC57, lowC58, lowC59, lowC60, lowC61, lowC62, lowC63, lowC64, lowC65, lowC66, lowC67, lowC68, lowC69,
  lowC70, lowC71, lowC72, lowC73, lowC74, lowC75, lowC76, lowC77, lowC78, lowC79, lowC80, lowC81, lowC82, lowC83,
  lowC84, lowC85, lowC86, lowC87, lowC88, lowC89, lowC90, lowC91, lowC92, lowC93, lowC94, lowC95, lowC96, lowC97,
  lowC98, lowC99, lowC100, lowC101, lowC102, lowC103, lowC104, lowC105, lowC106, lowC107, lowC108, lowC109, lowC110, lowC111,
  lowC112, lowC113, lowC114, lowC115, lowC116, lowC117, lowC118, lowC119, lowC120, lowC121, lowC122, lowC123, lowC124, lowC125,
  lowC126, lowC127, lowC128, lowC129
]

def lowYhm : SparseRow := ⟨108, 59, 0x77a11b50f779a01028eaf6df78f9780201093118bccbba003f8a285b233c27a007e0001457956d4600fa0001337751cd801e800188e610446803b8837296905d85007636b6924eaf2da00ea933cd77786dd401d0004a00b80de7803980006fe6d4179007200046bcfe551200de0026d8bd237dc01b82a86b0c41ca68036bbb73a66046ad006c4b1efbbb2463c00d6a54e3e40fa8a801a800818a94fec1803480039336c89ca006800004d9f2506600ce000eb530c9c90019000304ba096db803180d9e1064a2f100625493ef0ae233800c28e15d174e48740181ea0f574e80d6802faf3dad15f4ea0005e77c0ea700851400babc3d0ba921fe40170ee847cdea5a1802d800922d160255005a00014e6b94f7400b200023aa6e099c0158002ddbf81748802a80354b331433500546001f70bfe94800a6c80a71a4a73300149de13c3d245040028b954c779ffd42005092f24a835052a009ef99c15522bd24013a008151679b910026b6244ecefc784004c6c2dec9530fa40096ca2b6e3b43734012a2662daf0aca98024b3a4111ee9af50048819a817d8c01c008ed75e78396828001198ad7d92720eb80229fd3a3edafa850044000a422f0854a00860002972d4da00010800052e5a9b40001f80052117842a5003e3fa747db5f50a007ac56bec939075c00f1aebcf072d050001dc0cd40bec600e003a6748223dd35ea007313316d785654c00e19456dc7686e6801bb616f64a987d200366c489d9df8f08006b0040a8b3cdc8800d1f3382aa457a48019c9792541a8295003272a98ef3ffa840062ef09e1e92282000c19014e3494e660017b000fb85ff4a4002e006a96662866a005a0016edfc0ba4400b00004754dc13380158000a735ca7ba0028001245a2c04aa004e77423e6f52d0c0099787a175243fc8012bbe075380428a00245e7b5a2be9d400046f507aba7406b400891c2ba2e9c90e8010aa49f7857119c002001b3c20c945e2003e001825d04b6dc0078001d6a619392000e800026cf92833001a0007266d9139400320040c54a7f60c00614a9c7c81f515000ba58f7ddd9231e0016776e74cc08d5a002a154358620e5340050004db17a46fb8009800235e7f2a8900120000dfcda82f2001e0025005c06f3c00392679aeef0dba80069b5b49275796d000c106e52d20bb0a0016000c4730822340028000266eea39b00038000a2bcab6a300041450b646784f4000684988c5e65dd000091d5edbef1f2f0000bbd08da87bbcd0000⟩

def lowHints : List SparseRow := [
  ⟨70, 44, 0xc0e7dcb060081003c692df00800104701b6007d043f653ae007700447734100760272ee321007303343ec51006f04d9c75af006e004070310006d095037150006c01eb5775a006a098df7eea00690111dcd040064003c692df00610016d266b006000b53b89d005f0031abd07005e18f8cfa7e005d00d014f39005c002af5760005b017e9a22f005a21e1a818f0056003dc0d9a00540033037c2005300345b27d00520016d266b0050000ec4609004e0039b9d69004d002efc791004c0070c455c004b002af5760004a014230f500049003f1885500480028461ea0047003c692df004501071f72c0044011f4985200431ff0f1f49003f0140d9495003e0127578b4003d003c692df003c0016d266b003b0028461ea003a0020381880038002af576000370035b2d3800360038622ae0035002596c74003400080e0620033000c1509300320040703100031002596c7400300049d5e2d002f008796bc7002e003c692df002d0361e3927002c54227bfa4002b0078d25be0028004070310002700243f1b900260038622ae0024001ad969c002000f1a4b7c0019003c692df0018003b1182400130038622ae00122a3ee2ca8000f003dc0d9a000a00fc621540004003c692df0001⟩,
  ⟨65, 42, 0x4070310008002139d94401f405df8f22007702540dc5401cc07e310aa006d01c31157001b0078d25be006a01bdb2a8401a407e310aa006400508c3d4017c05b499ac005e00e6e75a4017404070310005c002596c74016c038622ae005a006b65a7001500487e37200530090fc6e40148020381880050005b499ac013c00965b1d004e00d16c9f401340345b27d004c01071f72c012c07f88b65004a0370a7f30012403c692df004801e8a81e4011c0101c0c40045023e930a401100ae852f600430187ffd4c00fc0b3e3de2003e02540dc5400f400ec4609003c01e8a81e400e803c692df003901cdceb4800e0088ee682003701071f72c00d80345b27d003500d16c9f400d000965b1d0033005b499ac00c8020381880031003b1182400bc0487e372002e007b81b3400b40508c3d4002c00b13486c00ac0218fc4300280020381880098039b9d69002500e6e75a40090059f1ef1002300508c3d40088078d25be001fbd34153500068064af4c9001901d88c120006007f88b65001701c311570005407e310aa001401c311570004c0838fb960004⟩,
  ⟨4, 46, 0x3af5a7157c00a2fbf214eb000199c9a52aabc003e4f4d7fa320007⟩,
  ⟨73, 48, 0x51e3e8f0077000040703100750004c853a300730004c853a3006f000533b94a006d0004477341006c0004b2d8e8006b0004f349190064000533b94a006300045cedfc0062000508c3d40061000218fc43006000028461ea005f0004477341005e00049d5e2d005d0000d6cb4e005b0004ddce5e00560004c853a300550001d88c12005400047268b700530001173b7f0052000218fc4300500001173b7f004f000101c0c4004e000305424c004d00049d5e2d004b0003f18855004a000345b27d00490003c692df0047000040703100460001173b7f004505ff5bd4d9003f0003b11824003e00049d5e2d003d0001c31157003c0001173b7f003b0003c692df003a000345b27d00380003f188550037000299dca50036000345b27d0035000299dca500340000c1509300330001173b7f0032000203818800310000965b1d002f00041c7dcb002e0004ddce5e002b02f5bc9add0028000243f1b9002700012cb63a0026000203818800250002efc79100240000157abb00220002c4d21b002000045cedfc001f000533b94a001e0004f34919001d0489661326001a0005b499ac00190004f3491900180003dc0d9a00170004b2d8e8001600044773410015000533b94a0014000487e372001300035b2d38001204318d2059000f0004c853a3000e00064af4c9000cd47d8b2f89000b05cddaf9df00070004f349190004⟩,
  ⟨72, 47, 0x28f1f4780102003b676d2c020001193f008803e800cd659c3007a001956c89a00ee09cf69e06401d8009dbd4d4803a0041068c1d0073001956c89a00e4002ba14bd801bc005ca14670037000bbf1e44006d094e5e88ee00d80027f033b401ac07ed2231a8035000b7eae13006900cd9091a600d01e08f5ac28019c0055eaec00032000bea13ba006300134c440200c40036b49444018400843b8f3803000104701b6005f0017ff1cea00bc0074756de401740064af4c9002e0010dd5cd3005b0018d5e83800b400345b27d00158005ea4c7f802a801c311570005400b48fb3f800a600fe6596c801480076230480028800dc29fcc00500027f033b4009e0040c61bec013801db3b6960026801f4bd277004c051de8a4140096027f59262c0128058f02e4c002480108771e7004400675ea3f000865616e336c400fc043cb5e38001f0043b5e37d003d0dd9c81d9c007800ac81add800ec04e5308e4801d00105c7c7100390149be1abe0070001e3496f800dc0192bd324001a000ded95420031001ddeac0c0060003abb975400b40068b64fa0014000cc0df08002700640376b8004c0004b2d8e800940088ee682001107cc6938c6001ac1ed23970e0032002cf8f7880060001ad969c000b800cd659c300130002da4cd600243c2ac14088003c005493405000708f3c0c4060007⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨37, 45, 0x661c72fb0007310e36757980390015d0a5ec01a4c0ca53ef400d01aec3523a006700370a7f300311c3318f1880168658e25e4200b212818dbd3005536096a41d8023bc53b335000114a882b8ce200887edb88cc50043118b362c880210739ea296000fd32d8e8aa6005c6d2cbf5a1002d2cbde605c00160b00d2f34c00a0002da4cd6004424e2e361e0021241ee3778000f956ba0b48400689ed488c700032853d4ffc00018c2d084cea000b9d6126d738005983c87d8b4002a76184722800142ebab1335000997e6f2d7a000483b74d9e0e001e5ac35baf4000e2429a0d500006919ead660000316b8391c18001600a677294000a⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨47, 47, 0x11ff55af80204001a2d93e8040000055eaec007e000305424c00fa000c15093001dc0037b6550803780049d5e2d006d000bbf1e4400d2000762304801a02d23ecfe000338007623048006400038622ae00c6002698880401880008b9dbf802b000431f886005511f1be052a00a60a0877e11c014805452d01f0028800965b1d0005007f403818e009e0311ad401c01381dcbe0a8600268143f40657004c05a1ce486000974d4f50b46c0114001f8c42a802200068b64fa0043000a92680a008400070c455c00fc002efc791001e80039b9d69003906a008e9b20068000305424c00c406b2536cf00180000c15093002e3280ee2764005a0002596c7400b0000157abb0015800080e062002506e95dec20003c000cc0df080074a386b5d92800ac77264d45800140002596c740026000b6933580048002ba14bd8007375a34a1f2000b⟩,
  ⟨75, 49, 0xbbf1e44020400068b64fa0100027e6ce023007d0001ad969c003b8000c15093001cc00068b64fa00e4000305424c006f0001a2d93e80348001d32d63401a00f0a047a4a00ce000345b27d00640001b853f980318000e188ab8017c000533b94a00bc0003f18855005d0003b11824002d8000e188ab801680006e14fe600b20005b499ac0054000243f1b900288000e188ab80140000d6cb4e0009e0003dc0d9a004e0000157abb00268000b13486c012c000305424c0092000370a7f30048003a9b5f3b802380096b107ec0118430a638fec008a000d014f390044003f4e382380218000dc29fcc01080006e14fe6007e0001ee06cd003e00016d266b001e800055eaec000f000038622ae0076000218fc43003a0001b853f9801c800060a849800e00007b81b34006e01fa1bd6300036000a473a7b801a801255409b800d00000abd5d8006600068b64fa00320001c311570018800121f8dc800c0004c2f4f44005e0407d9db4e002e00066b2ce180168000c15093000b00006606f840056000370a7f300280001c31157001380011c9a2dc00980006e14fe6004a00279a48c8002400014cee5280118000f1a4b7c0088000838fb960042001d1d5b79002000014cee52800fa46b838b19c00781182515b1a003a51838116b1001700fc21a50f000b0315fa120bc005401be08932c00290897ece39d001305a1785d74000902003bd5830003c0701071e1e001a00049d5e2d000c⟩,
  ⟨67, 47, 0xcc0df0801f80014230f5003b80022e76fe0073052daec56800e4000965b1d00190000e188ab803100028461ea00600005b499ac00be00070c455c01780010c7e21802e8002af5760005a06f649c09e00b200090fc6e4015800157abb0002a0001ad969c005300055eaec000a40009bb9cbc01400007623048027800182a126004e000487e372009a0002af576001240014cee52802400012cb63a00470003dc0d9a008c00045cedfc010c1d8ecba49802102121af31a003f00022e76fe007c00080e062000f4001a2d93e801e00012cb63a003a000157abb0007000299dca5000dc002af5760001b00022e76fe0035000a1187a80068000407031000cc0004b2d8e8019000218fc4300310000d6cb4e006000090fc6e400bc002a49a0280175ef7ada1b4002c000487e37200560214496a1800a000157abb000138002efc79100260009bb9cbc004a001071f72c0090000e188ab8011800243f1b900220002af5760004208af74856c008013b3a2a5f000fb863edf157001e00111dcd04003a002540dc540064004273b28800c0004c853a300170c2d084cea002c00c7052cac0054003257a64800a0006b65a700013000cc0df080024058f02e4c0003c004fe06768007000e43802e000d⟩,
  ⟨58, 50, 0x411c06d801f40000c15093006f00003b1182401b80000ec460900640000157abb00188000101c0c400610000508c3d4017c00014230f5005a000035b2d3801580000abd5d800550087cc6f4380150000080e062005300006606f840148000243f1b9005100004b2d8e8014000016d266b004f00003b1182401380000ec4609004d00004b2d8e801200060a84980004700007623048011809153b0d7b003f00002596c7400f40001d88c12003c00007b81b3400ec00012cb63a00390004070310000dc056c1b74e0003600092ffefc800d400104701b6003400001ad969c00cc00016d266b003200004b2d8e800c4000243f1b9003000004b2d8e800bc000080e062002e00002af576000b006396b965500280000508c3d4009c0001ad969c0026000af86f024009400f7da31ce00240000157abb0008c000ded954200220004624caac00840077bb206100200000157abb0007c522c921c96001e0003f18855000740d53c97d0d0019a99db022a1800602a376b1f7d0017019b11073fc00582baef8fd110015005824205b8005003a8085d1c0012011cafa87b0003c01dca88fcb000e⟩,
  ⟨53, 47, 0x2b765662008100200d230a010000d61f782801f432c916739803d000c557961006e00033037c200da000863f10c01a00051e3e8f003200004070310063001728519c00c4003b118240018400035b2d3802c800dad2511005600307f1a3600aa0ec811a8240150011288a6180298190fa20e90052006b3ab18a00a20040c61bec01400330e397d80278000d6cb4e004e001651864e009201819f653c011c00467ab5980218f6914a7e9003f0116ba9e9e007c01e29d99a800f40425e37cd001d8001ad969c003a0022668f7e0072069f321e6400e02d711e0e0801b85e497e5d40036011969f5fe006a000407031000d000905098680180c93fb8b330028052951d76c004e04e1d56110009808f9a0532801280cc236b3b00240019d7a8fc0046039999e778008801b2f54ac001080239345b800200cefdb8110003462afd20b1000661b69d2835000c1245248f4000170015fb9b62002c2bddb505f0005417f9be3b400090a40ef86b7000f⟩,
  ⟨43, 45, 0xcc0df0801f442ac14b2e00f429b49cb6b00751ec4e79068039144449294401b8a07cc0b4400d6586c9e92a00641d1349f1580310917d4ea20018459c19aeb400c02e0575a98005f00121f8dc802d0604cffe54016424e592b9400ac5423d3a5f0055057225f97802a15ec2b2b9801446e602bee800a0459fe346f004f209d73a2680271dc3d2a2400134f03cf003c00921cd385963004800492a0cf80218dcfb695f400fc00d16c9f4007c15b5cc82400393b76318c9001c0d4fd7f4b800d4af8440cca00508e8c2f65500273f01b2e9500130ed72bf3a0009476d997b58004855ec43abb002330b8d40c9001110e56ad920008524753063e003291a8441800018baad03f3a000b9892c8afa000587bd79e2c000264d75873c10012⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨40, 45, 0x1bd06d268040800d16c9f401dc0028461ea00d000777ab03006402cf8f788002d0872b56c90016401ad969c000ac045cedfc0005201b5a4a2200288037b6550801400c3d4f4ea009e0305424c0004e0ad38410d8026822f78bec4013034506a72800961aed8ccf5004707cf9970880231728fd71d80114002596c7400884157185a400431ca890203002105bdff5dd000d001b853f98006206bd10ca700300c2ddf1838017a085f565e000b80dc29fcc0005a00a3c7d1e002c58f58cfac0015802c4d21b0008c0932ae53e004405efab2e400210e7683aa2001000233d5acc007c4aa4a017e00316794b8c3e001703359670c000b483a15d6dc00544a6c3ded000280384cb0250013⟩,
  ⟨40, 48, 0x51ce6e35008100022e76fe0073050802836d0072000305424c00690006f6caa10064243d180e78006300060a849800620002da4cd6005c01dbfcb9f3005a05c5618e180059000925419f0050016a6198e5004d0432e4cc090047bf6439c99c004500038622ae00430881e532c70042000863f10c00380002c4d21b0037045c2cab6d003600d990201b00350116d019590032000c2a83eb00310084e76510003009ddedd0c3002e4ce409ed6e002d00380c3ff4002c000b693358002b0000abd5d800270090fc6e400024000abd5d8000230049aaed5a0022005de37765002100f682861e00200007e310aa001f5cbce12a53001e00016d266b0018001b2f54ac00170007f88b6500160092aa04dc001553fc79cd590014⟩,
  ⟨35, 47, 0x60a8498020000055eaec003b8003f18855007305f057041800b200076230480134001cdceb480260009a62201004900210ee3ce009000060a8498011c0932ae53e002300033037c200430a9a20253400840006606f8400e40047d2614801c000299dca5003705ad8d66a4006c02b35e631000d409b9993a7801a00175347120033019a1f62880064000055eaec00c4019d7a8fc001859a95b5e25002c139cfb34b60056013a22eee0009404a9733630012000c6af41c00230090a68354004401071f72c00084041876c7f00100008cf56b3001fb94592224c003c007f88b650005c0b20b520e000b0cfa42f3a40015⟩,
  ⟨31, 46, 0x9af87b2d0081125f52232801f40d736b3a70054036ca0eff001240247f8bc1004804f247583c011c0e6a6ea0f0046000055eaec010c024aa8137003f000a67729400f8002596c7400380af3bc295800d8103aecacd0035041f830d4c00d0087eca75c0030c40fb0815400b18301ce498002b3b58a8cb7000a04a4eb52be002703ae12e1b40094138e0bdeb002401c00c14b4008c0ebdaa3590022038a29b11000841105a2f1a0020006505377c007e010284c4c001e3179ceb4a40074552af318b001854460f3ff8005c55ec43abb0016⟩,
  ⟨17, 44, 0x4fad63ebe0072008fa4c29004900101c0c4004800182a12600470051e3e8f0043001d88c12003e006f6caa1003d007cd95ef003800157abb00037d24b78942002c9517945f5002b2c3d05a3c00280de98e3ef00240c0644cf700210e4ce5dfd002002210a492001f38c2d3298001e⟩,
  ⟨42, 47, 0x11b4282100408001ee06cd008002149f550400fa001bdb2a840190004d311008031000d16c9f40056000487e37200aa0154a66db401500012cb63a0029800d573a250051001aae744a00a00104701b60013c004477341002480100691850048016416a41c008e0178e589440118c8333a91b001f8006cbd52b003e0001ad969c007a000fc6215400e800055eaec001c8096b107ec003801290521dc006e07e5c0016000d80423dffb4801a800d41bf6a003100218fc43000600090a6835400bca5f9a40b380143d9a00a7cb0027009a0c3524004c0122a4b25800940487379c28012000a270263002300b612551e00440123a6731c008402f67deb700100009bb9cbc001f963d943ee0003c4687cc61f4007427bf33b96800cc15d8e447f0018⟩,
  ⟨42, 47, 0x4e7dfe5a8040800cebd47e00800017ff1cea00f4000dc29fcc01dc001b853f980370005b499ac006c00012cb63a00c60022e76fe001880004070310030800b53b89d00567e90b128bc00aa3ebae248cc0150099ebfd0b802981458c2238005200e086eabc00a2003359670c01400a3dd4c9b00248010dd5cd3004801e8523354008e0138cb433001184d0cd0ec7001f84c0860d11003e020ae3b848007a161a7bced000f0000f70366801d001524d0140039041e814c880070061dfbd17800dc1a0c0423d001b0159c4ac4300340d32fb09700051c5bbfb8718009c331fad357001300fd2365d30025021daf1be8004800b59174bc008c06113af270011006d6928880021009ebf0e0c0041386a44fb940078003d1503c800e929be6468e0019⟩,
  ⟨39, 46, 0x5d37a18d007d17fd19687801e800b28c3270077000508c3d401d800675ea3f0073002e50a33801c80026ee72f006f002540dc54018800182a12600592b231acd60015800bbf1e44005525dc4034d4015000e2e05730051004477341001280a8d095b40049003dc0d9a00120008fa4c2900432b74feb65000fcf38551d82003e5891df6ef400f71b8a6c9c3003c0534bb0ac400e800dad251100390467ab598000e013da9118e003703e5734bd000d806280d5920034003b676d2c00cc012b5e8e500320031abd07000c486b12cc17002830ff4ec228009e707c9b89a002600706e6ad4009403821baaf0024002af57600008c00fb0a6990022003fc45b280084000d6cb4e001e⟩,
  ⟨36, 44, 0xcc7c057e6007f78a7666a0007d5abf54ac3007778ab6d6d10076620c0a393006358cbef307005c66e1ca911005a63437dd0b0059725c71a10004a73003972e00495b0bd9e6600486a8017517004764f6731b700466b89e61b900445dcca4fe5003f746d5fdde003ebd0a776ab003c74f4f69a5003b7aa182403003a596900a7e003975a37bc9b003869c01e6a2003780912d6e700366decb841600356e9c951c700345d99a18230033692f21fbe0032666a4fe0e00286fb528472002772256721d002665531461e002560a4427cf00245bfed649d002362d96fd5600225a4a8953600215ea8cefb1001e⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨49, 46, 0x153a4acf0081000863f10c020000157abb0007715f73e740401c8006357a0e006f0015d0a5ec01b800bff8e75006c0001ad969c01ac005f509dd006a002af5760001a4006a0dfb50064000c6af41c018c000abd5d800610009bb9cbc01780256bd1ca005d069edc3378016c485dff078005a1b51e630f40164000ec460900540002af576001480108771e70051003a65ac6801400144e04c6004f004421492401380dbbe9719004d012f6591600130252b61990004b0006b65a70012054f7ef9c9004702c984f3e801186fe6d41790045002947df640110070aedb0500432514e51d3c01080e19e263b0034004375734c00cc0863f10c00032003963eba400c400eaee5d500300522f167e800bca8e0b1c04002ed2d61492dc00b400b9428ce002c3331ccc33800ac0113347bf00220042c99d740084011b42821002002d74793b4007c00b693358001e⟩,
  ⟨40, 47, 0xabd5d800fc00243f1b9001dc001cdceb48039a4350a0858006e000863f10c00d2186422217c019c0041c7dcb00321d6fc042520063000eef560600c40008b9dbf80184010114ee2802f8008fa4c29005e09eff7e3d000b2001981be100155a5a41b1f9802a03600b065e0053002b4b60ec00a40059f1ef1001440049d5e2d002800ff26e75b004f00182a1260009c05427daa90013404481f16d8026018e354ece004b000533b94a008e01402d7378011af855cbac2802288d77a33db0044a8e7be059c00860773a3fff000d00090fc6e400198146ce532d003200121f8dc800620106739ce800c010ed78df40017a957e5f585002ed1df920cbe005a557a7d952c00b00055eaec0001000061fff53001f⟩,
  ⟨24, 47, 0x2af576000ee0e5f056d9801c8004c853a3003600022e76fe006a01316912e800be124e8a41100164000abd5d80025000574297b0049000055eaec00900ce3c677e00118000ec460900218619c9d8f2004201f10c0f4c006a0a93bfb5b000d0044a2298600198242192cee0032007373ad20006205b5f157b000c0f02b7c4bd0017c04a6f434a002c106a141b560056043904cb5c00a000162690d801182f3ce94100020⟩,
  ⟨42, 48, 0x80e062007e00026ee72f0073023dbc3ef200720005df8f220069000721c01700640003c692df006300059f1ef1006200163c0b930061000080e062005d0008796bc7005600115e3d35005201afda8db900510089daae2900500353cb07b8004f014662ed86004e03fb03818b004d0001d88c12004c0000c15093004a001c9c7b17004900031abd0700480005df8f2200470002da4cd6004400061fff530043034a4fdb2d00420021fb29d7003807f61c7dd100371c1d1d562600360462b81067003505e4ad608f00340198c7b6d80033059954dc990032013c5165de00310cb3f3338200301908d63965002f000c6af41c002e08f5d9c049002b05d9da8854002800e915d13e0025053c7325f8002400419ce73a0023145e6142710022c4460f2aac0021⟩,
  ⟨45, 45, 0x6b65a7008100121f8dc803f002495067c01f45938ac83200e40047268b70064001e3496f80310011c9a2dc018400838fb9600ba004b2d8e8005a00223b9a0802b0010c7e2180154006606f8400a80022e76fe00530138cb433002903d50154a401440093abc5a00a000c806ed7004f0028f1f478027001377397801340055eaec000920045cedfc0048001981be1002380101c0c400110006357a0e0086349790fdf00420024eaf16801c8072c7d74800e0013a22eee006f0a96d10d7003610571dc24001a8f682861e000d000a3c7d1e0066265410cff00320024eaf168018853510f5b000c00028461ea005e0055eaec0002e001ad969c001680111dcd0400ac7f0fe3f42005000080e0620026004070310001296c1f4b8d400900078d25be0046693b370510022⟩,
  ⟨51, 53, 0x1ee06cd002040000bea13ba01000000157abb0007e000047d2614803e80000101c0c401d8005b749036000e4000055eaec0006a0000182a126003200006f16bf24018c00123d1689200c40000157abb0005b000031abd07002d0006f4c71f7801640038a7f9bfc00a80000487e372005300049a02ffc8029000529fdad4401440000c6af41c00a00000299dca5004f000035b2d380027000010c7e218013400002da4cd600980000431f886004900001c31157002400002495067c011c0000080e062008c000012cb63a004500002cf8f7880220000127578b4010c0081a9c099200840000cab644d003e00005493405001e80000863f10c00f000006e14fe6007400004b2d8e80039001cf266030001c00002dfab84c00de62d5c41cc06006c002395f50f6003500198d27435801a00001ad969c000cc00519b6ab8e006400006357a0e00310002139d9440018000015d0a5ec00b8000055eaec0005a00882fc6e460028000a1995ae20013001d8769745000940132fbd01a40048002e40872bc0023⟩,
  ⟨20, 43, 0x508c3d40100008b9dbf801f401cdceb48032001ad969c006300762304800c4002af5760014c00b693358026008b9dbf800490038622ae0090013773978011c04a81b8a80220093abc5a0043007b81b34007a01071f72c00e8047d2614801c0033037c20037005b499ac005d99f46d12000a25a58ba090012f8517b7e00024⟩,
  ⟨50, 45, 0x327d3d0f401020090fc6e4008000bc9dba1803e800762304801b8008e4d16e00da01ff7a84f006400431f886003100243f1b900184002da4cd600ba005493405005a3df081eee802b00b032c5fc01541718358fc00a80049d5e2d0053a2e03eafe8029084c1ce48c01440127578b400a0335ec5bac004f004ddce5e0027000abd5d800134002596c740098002da4cd6004b00447734100248009bb9cbc01200119ead66008e008a4613d0044003dc0d9a002188c5f101300108b5aefd7d2007e00e58fae9003e00655b226801e8002596c7400f000157abb000740093abc5a0039372d669fe001c2f7cad9c2800dd85d40d196006c33f927dad0035251896356001a0026ee72f000cc64367a34200640093abc5a003104b98f427001800121f8dc800bc0093abc5a005c0012cb63a002d20aae0574801401ff7a84f0009c00431f886004c2c466b5590025⟩,
  ⟨36, 46, 0x243f1b900204008e4d16e00800003b1182401f400863f10c006e00060a849801b4000ec46090068000d6cb4e00190006606f840062233f08629c015805b749036005508aac1ac840150001ee06cd00531026c99d80014800aa7e2c5005100045cedfc0140000407031004f000157abb0013800305424c004d002139d9440124007f88b650047000157abb0011800925419f00431e20c9d39c00fc03afc0785003e001524d01400e800a92680a00390d58e7bb9c00e07c12afae400371c95c4bc9000d8001ee06cd00340002596c7400cc0014230f5003200080e062000c45b708932f00288bb593a774009c322b592650026⟩,
  ⟨51, 49, 0x17d427740204000a1187a801000000ec4609007e0005a9dc4e803e80014230f5001dc00154fc58a00ec0004c853a3006f00026ee72f003700014cee52801b400088ee68200d800049d5e2d006b00022e76fe0035006b4acd96401900008b9dbf800c40001d88c12006100014cee52802f800111dcd040178000965b1d000ba0004ddce5e0056002f276e86002ae4f03842b3401500dc249e11400a6038eb19482005200031abd07002880014cee5280140004d061a92009e00059f1ef1004e000157abb00026800127578b4012c0007b81b3400940099605f4c004900028f1f4780240099707b584011c00028461ea008c0ebc7d7f56003f0c3e1b5c90801f00f072a2d7400f415abbafa9800780093abc5a0003b0024cab94f801d0001478fa3c00e404494bcd12007003c840759c0037023e6814ca001b00008b9dbf800d400045cedfc006800014230f500330000b69335801900000abd5d800c01553f782860050f89349656a0027⟩,
  ⟨44, 48, 0x1bc5afc900810008b9dbf800800001ee06cd007d0704e32bb8007a0006a0dfb5007700084e7651007200508c3d40006f01d1d5b790006e0006cbd52b006d0005df8f22006c0006a0dfb5006b0666fae8fa0067047b4d886e00640006e14fe600630005f509dd0062000721c01700610001c31157005f0004070310005d000675ea3f00560c9f4f43d00055c543c8eb9c00542076c59fa9005303f58f5810005200199738cb005100080e06200050008adc6eed004f00088ee682004a00eedfe5a50049000d2c44af00480065b10d5400470e78f2914f003f06038dcd5f003e929042adbf003db80209819c003c00bb5b8923003b011ec8a4be003a0009a62201003902647fbc6c003801fdccee54003703e03f9286003601384a62ce0034007891ebaf00320008796bc700310a9770cdd40028⟩,
  ⟨40, 44, 0x3327bb3b9007a37ec07db80075006f6caa10073187a9e9d40072224a5e689006f5cdc57f24006e3004f02e7006d006f6caa1006862e42d32e00676dd0872bf00644ffdf0292006349dc992a7006210fc3d3fd00610080e062000601c1b9ab50005f26ce3ad7800565795d344a0055902c594c70054bebabd5e10053952501143005259421234f00512e6cd44d700504df7bf49c004f00863f10c004a739135e1200490510d1da200484791f1170003f7bab510a5003e4e296b1a3003df113bb51c003c778ed33f5003baa548e85b003a00762304800398d4b561c00038c5eb41d5a003781817a7a800365a60040e600353ae93c216003438ac00c2d0033330a327a70032⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨31, 45, 0x88931e85402040002af57600fc0049d5e2d007d0041c7dcb003b800ec4609001cc23f94cb0400e4007373ad2006f002efc7910035000a1187a801a559fd0e6de00d0002da4cd600613e1ccf109802ea35f96660801704cc2fb09a00b2efc2c5fc3004a633ac3f4b8024947eaed5ac0121a52a9cede008ea31545ad90046a10253ef28022b8c37eff580112644f68474008666f33e49000423f39693e5801a20020fc19400c88a868401000627edf8fcf600307eef0005c8017d3ae5c774800b9c74e0ce38005ac98028e43002c⟩,
  ⟨35, 48, 0x2af576007d01224ec76c007a00041c7dcb0077000bff8e75007305392d737b007200080e0620006c00049d5e2d006b00068b64fa006a3f536bdcca006900002af57600680006a0dfb5006300265817d3005d00655b2268005c0058445874005b0c943bfb64005a0570ce4dc800590078110b4d004f00ec460900004d0428a84eeb004b039bddd931004a0297ae2e020049000b7eae13004805df79a7450047026d241da900467fd4fb19ff0045abfc5b0d490044007e9c7047004308ae3254770042000101c0c400340099a0cf7d00320009a622010031001793b74300300e58cff38a002f4b2697b55f002ec899acef97002d⟩,
  ⟨46, 50, 0x1728519c020000012cb63a007e000518dfe0401f40006e14fe600770000305424c01d802224c7a15007400e9b6e9b8801cc00b5667f4600720032fe1d71401b0000675ea3f006b001336c947001a80fb889a9aa0069025be6188c801a00006b65a7000640d2b98d9280018c0006b65a7000610001e3496f8018001c99cbbfa005f000187ffd4c017800bddfeb0d005d008ce54f23c017193c568ee3f005b314e8e11158016808fbf9bf9c00590004375734c01300553dbe7c5004b013016c5e6c01280193e9e87a00490001bdb2a84012001d154d72e0047001336c9470011a10aece6fc400451729c97fc88011041529076ce004302e4bf05f180108000055eaec003b000162690d800e8004a2bcdbc003800011c9a2dc00d800006b65a700340001d88c12000cc0007373ad200320001bdb2a8400c40007f88b65003000feb62305400bc083ef09fdd002e⟩,
  ⟨39, 46, 0x4b2d8e8008001819f653c01f48f33fe3a4007700a778ea0401cc00990a746006c000fc6215401ac007373ad2006a04b6dfeb1001a435a96dce30063002af57600017c00990a746005e002a49a028017400a7ced4f005c1b70c69dc4016e0703a3aaf005a2f9832dbc0016400a7ced4f0050002af57600013c00ae852f6004e002a9f8b140134009fc0ced004c0617457708012c0041c7dcb004a028868ed10012400a677294004801763631e4011c02b60dba7004613fed0347001106e5975941004340f2690db001080055eaec0003a0021e5af1c00e0004f349190037002a9f8b1400d000ae852f60033002af5760000c800a7ced4f0031002dfab84c00c00a02c3477002f⟩,
  ⟨45, 45, 0xec4609008100365ea9580400002596c7401f806bbb91ec00fa27afc383000770c211e393003980f805274401bc00ae852f600dc004b2d8e8006c0026ee72f003504e937915801a400ae852f600c800e188ab8006300d014f39003080afdcdb10018013214e8c000be004c853a3005ea3072d22d802e8fffdb2a900170711a40ac000b63ea3b9f73005a4a4cb1aa5802c801ad969c0014400b69335800a008cca75ba004f0031abd0700270432a45bd80134118932ab000982ed58a9d1004b01381f6d5802506c82412dc012400b13486c009000925419f0047058afbe1b0023074c09b7280110611bbd2d200860059f1ef1004200218fc43001d000ec4609000e0008b9dbf8006e10343652600340031abd07001982c0752d0400c800b693358006207c4303d30030⟩,
  ⟨46, 44, 0x2efc7910080000ec4609007e0059f1ef1007d0a2b09661007702c37a6f5007357469eb31007202fbdc9a3006f002da4cd6006e00243f1b9006c00299dca5006b005ca1467006a0684ae9f9006900fc6215400631a84d67fb00610f2101d670060147243e19005f00243f1b9005e20ed5409d005d0111dcd04005c011df1d97005a58deba94100590020381880053796e15abc005102af576000050375b0b6d4004f0c313a457004e5e85e78b3004d1a8a352e7004c00b3e3de2004a025c1bcb600490031abd070048007f88b6500470070c455c004400a51f7d90043739bf33ea0042000d6cb4e003b001c31157003a0031abd070039014b96a6d003800721c0170037002af57600036002efc7910035ea412fcc5003410d29f75800337a4ceeffe003203430325a0031⟩,
  ⟨44, 43, 0xc15093001000121f8dc801f40157abb0003b806b65a7000736d73e5e5800e401377397801bc01ad969c00370061fff53006c00d16c9f400d601173b7f001a8026ee72f003480589a436006400305424c00c6205850988018402038188002f0026ee72f005d00431f88600b8000abd5d801697000b7d6002c801ee06cd00530492a0cf800a21e64eb1cc01400080e0620027802596c74004e00305424c009a001ad969c0130004b2d8e8025805f509dd004a0154fc58a009200d6cb4e001200279a48c8023806cbd52b00440121f8dc80087179169ec001080345b27d001e80533b94a003a007b81b3400720279a48c800e0031abd07001b800c1509300360012cb63a006a0060a849800d00162690d8019acda171b30032⟩,
  ⟨51, 55, 0x182a12600200000078d25be003e8003f564629a0077000006606f8400ec000183f8d1b001cc001ac093d7c8039000005f509dd006e00000c6af41c00da0000157abb0001b000002da4cd6003580003bd2d2d3006a0000080e062000d20003ea7c0fa4018c00002ba14bd803100034f182ed000610000208e036c00c000001b2f54ac017c00001e3496f802f000330f91293005d00000431f88600b800008a9bfebc016c000433fc078802d0004daf4112a00590000e63b846800aa000015d0a5ec014c0004456fbf78029000372400ee1005100000c95e99200a1f2d11ec5d940013c000038622ae00273f2d3798ace9004d00000838fb960098000014230f50012c00004c853a3002500001712d6e10049000007373ad200900000229184f4011c00000f70366802280000ff116ca0044000121f8dc800086001c514d8880010800002596c74001f000005b499ac003d000008b9dbf8007400000fc6215400e4000095af472801c000004f34919003700000a1187a8006c00000fc6215400d404a83663e9c001a00000f5abbad0033⟩,
  ⟨49, 50, 0x508c3d400800000407031001f8000990a746007d002ff8db25401dc00002af57600760001ddeac0c01cc040ee620aa0072000ab2a022801bc00039b9d69006e0001524d01401b40004477341006c00012cb63a001ac0003b11824006a00013214e8c01a4000ae852f600640001a2d93e8018c00047268b7006200502b94f68018400016d266b005f0001173b7f0017800049d5e2d005d0000f70366801700001ee06cd005b00013214e8c015400059f1ef1005300005b499ac014800bf628c3300510001bdb2a840140000305424c004f00007b81b3401380003dc0d9a004d00010c7e2180130000487e372004b0000fc621540128000d41bf6a00490000fc6215401200003c692df00470000a6772940114000bff8e7500440003608be6c010c0004b2d8e8003d00004b2d8e800f00003c692df003a0000f70366800e4000e188ab800380000fc6215400dc00049d5e2d003600010c7e21800d6943a96476f0034⟩,
  ⟨43, 54, 0x533b94a00800000d822f9b001f4003b4485bc2007700000c15093001cc0076bab748b00720005539b779401bc0016502ea25006e00001a2d93e801b400007cd95ef006c00000508c3d401a8000d6756314006400052e5a9b40018c00007e310aa0062000fd6e936180184000095037150060000023e930a4017c000035b2d38005e000020e3ee5801740000305424c005c00039af19328015400004ddce5e005300041fd8f8380148005e45775a30051000022e76fe00143f2d32d05946004f00002495067c013b3b0ed59937d004d0000035b2d38013000004070310004b00000d16c9f40128000252b6199004900000b13486c01200000182a1260047000013214e8c01100000721c01700430004fd5aa0a800f80007b41430f003d000006606f8400e8000028461ea003900001b2f54ac00e000006e14fe600370000101c0c4000d877b6c6225b60035⟩,
  ⟨33, 41, 0x4f3491900800cf691db803ecfb01343401dd0cd40c6c00de03f18855006e047268b7003691a40c14c019107f63e0e00c607f88b6500620452309e8030814cee52801780305424c00ba0bd498ff0054020e3ee58029a1e5af1c0014b49389fae00a208e4d16e00500487e372002781a837ed40138012cb63a009a059f1ef1004a035b2d38002480a6772940120090fc6e4008e074cb58d0043c765d4f5801f81d32d63400f8093abc5a007a03f18855003a01173b7f001c81b853f9800e00d41bf6a006e044773410036⟩,
  ⟨28, 50, 0x2e50a33802040004070310008000a2554cc6401f4024d16fa9f0064000239345b80188000990a746006100008b9dbf801740422de3a8400550153a4acf000150017fb15e6f005300ba19582e00148000b28c327005100027445ddc0140000a1187a8004f00029f3b53c01380009a62201004d00019d7a8fc012800068b64fa0049000090fc6e40120000305424c004700022e76fe00110000838fb960043000192bd32400f802dfebf4f1003d0000157abb000e800051e3e8f00390113b55c52000e37df9e3f0fb0037⟩,
  ⟨23, 44, 0x12cb63a00800989f0eb9007d00a270263006871ebad4b4006700e2e0573006200243f1b9005a00fc621540059ef535952200563949123a400554ba660dbe005402d3967b90052011085249005100fb0a699005000fc62154004f008796bc70049001981be100470070c455c00440da66eb69004300f2fc637004200f2fc637003f003c692df003e00080e062003a00bd498ff0038⟩,
  ⟨33, 44, 0x19ed23b7008101667010900800a865300d007d002038188007377918296b00720cf28ad87006c004c853a3006b13ed5c7c800690a016b9bc00680153a4acf0062025d73771006100101c0c4005d092ffefc8005b0e6916f54005a730c4e7c10059c5e9ea29f005628e5df6ed005518c31cd4600540991fef1b00531a8227285005202d645d2f0051016bcebf5005001f3657bc004f017534712004e02cce0212004d002596c740049001173b7f004410b10fb1500439692277f300429f414619b003f24b28f3d2003eed4fd7ca2003a015fb9b620039⟩,
  ⟨36, 43, 0x80e0620010000b13486c01cce3d75a96803900b28c327006d03837356a00d802139d94401ac04f34919003500b53b89d0069013f819da00d16ad25d3ac019c03d1503c8032007f88b65006200508c3d400c2017d427740178016d266b002e80055eaec005b01071f72c00b413067522401668d1bc5f8002b005ca146700550033037c200a801173b7f0014c006b65a700290012cb63a0050000abd5d8009e00a1187a80134014230f500260031abd07004b0012cb63a008a014cee5280110074cb58d0021a224c7a150042017a931fe007c02b4b60ec00f4004b2d8e801e006e14fe6003a⟩,
  ⟨38, 46, 0x38622ae0020007003052d007601702bad4c01d00594619380073069f321e6401bc42c037c23006e0038622ae001b41342de503006c0035b2d38001ac0aabe9c81006a03b57511fc01a45489da9e300640038b815cc018c00cebd47e006200380c3ff4018400eef5606005f0008b9dbf8017800f703668005d0007623048017026022ce70005b017dee4d180168d22b407ba005617620b729001541cb34d7db0054015ab0f24c014c00eef56060052003f188550014400e6e75a40050003a65ac68013c0031abd07004a001cdceb4801240020381880047001c311570011004cdb251c004331a51a159000fc1b9d69aa6003e03928da21c00f60a13a3547003b⟩,
  ⟨40, 44, 0x447734100800012cb63a007e022a6ffaf007600589a43600750f5964015006f00431f886006e122644227006d0e132c094006c003f18855006b059710eae006a04a00d84600690ae2f44740064334294a55006200447734100610022e76fe005f0039b9d69005e004070310005d0047268b7005c00218fc43005ba2d0ce7980056268b1b4f20055048e99cc7005402698880400530adc3decd005200589a43600510047268b70050001ee06cd004d003b11824004c003dc0d9a004b0033037c2004a0028461ea004900305424c0047000d6cb4e0045003dc0d9a0044002efc79100434f018e13e0042949abb006003f0df2f3f0c003e003dc0d9a003d00345b27d003c⟩,
  ⟨42, 50, 0x1c311570020400054934050080000192bd32401f8000508c3d4007d03c43413dd401e8534fa234950077086080640d001d805c5b77904006f2fd7f736e8001b800055eaec0006d0001173b7f001b0000487e372006a00014cee528019c06fa10537d006417c1ac9c9d4018c00047268b700620001524d014018400026ee72f005f00011c9a2dc017800049d5e2d005d00015d0a5ec0170141bed8fe900561ff41ccda34015610aac76cb4005400012cb63a0014c0005f509dd00520001b2f54ac0144000574297b005000016d266b0013c0006357a0e004e000090fc6e40134000370a7f3004c0000ec46090012c0003c692df004a0000b6933580124000549340500480000f1a4b7c011c00022e76fe00440000e188ab8010c00055eaec0003f0c1befde94c00f877d7e7d18d003d⟩,
  ⟨30, 48, 0x14f9da9e0081000ff116ca008000068b64fa007d000e188ab8007700157abb000076000863f10c006f000b9428ce006e000bd498ff006d000a1187a8006c06b07ae0de006700159035bb006408e1a1363e0063000abd5d80006200039b9d69005e00022e76fe005d0e3a1a7c300056abf0f1d9f100555cb0e19bde005405066a678c005301ddeac0c00052000f85b1230051000f2fc637005000159035bb004f0011c9a2dc004e0002af5760004b00068b64fa004a000b3e3de2004900055eaec0004706e556e910003f36dd9bb333003e⟩,
  ⟨33, 47, 0x1768c1cd0081002515e6de010000a3c7d1e001f43f1a88d18803d00121f8dc8007700eb9a332800ec0017d4277401cc008ef8ecb80390409f2d791006f00239345b800dc0048284c3401b40082380db0036001148c27a006b002414261a00d001ced075440192a343ae7bb00318010dd5cd300620023be3b2e00c20002596c74017898c1f628e002b008b3259d9005582bac69e1200a81bb6957d84014c18a8436aa00290013b7a9a900510024bffbf200a0026078b95c013c00a1187a8002700e3e217f4004a022c9e71ee0092005a47d9fc012002b00335d80238ca482fd1a003f⟩,
  ⟨25, 45, 0x2b8bd11d00081114cc97d1003d00380c3ff401dc75920811c00ea3d00e0b8b006f445f09fda0037155c307e1c01b529e14bd8c00c83996ef2020063312af00e000310d4dd47330018469babfbb600c0411d5e83b005f11b62ba28802e99dd5d95ac015917031cd5200aab9ac9adb5005482111f3d100299d03d9baf001448cc7c662a00a07191bb5c3004f002fa84ee802525c81d2584012444fd7320c00904f41fe44e0046⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨30, 45, 0x406014f3c010200c5579610080302f39ce9803f563dd1a9b401f438f5d6a5a00f400a1187a8007710b7c60bc003aa461ad14f401d1ee8fbb68200e636b08d40f007200bff8e750036643f89fb0401a9357d82ace00d2ae5ce941600682ea739f9d803396cb047fb80174f22da628200b8ec170c86f005b741774f1e002d11c398576801648fd2675d6009e56cf2402e004d0c4d6b5ae00260011c9a2dc01293fac9316000920f91c62c30048638092d478023a536cacc580118ed34fe6060088cb001ab2d0043⟩,
  ⟨24, 46, 0x6606f8400204012e0de5b008001ea55b4dc01f407d9aaf8300730047d2614801c80104701b6006c0007b81b3401ac4ccf1012d00693cb4b1696c01a073cef6bac0067004e32d0cc017c0150f5559005d011994eb7401718743e2dbc005b1841909c8801687b078938700590517de1f7c0134000407031004a09599cc6d00124013e29f1f0048070bef7114011c0e54f3e5f0046c1d6263ae801176eb48d8440044⟩,
  ⟨23, 48, 0x16fd5c26008100103186fb00800038622ae0007d0005b499ac0077006bbb91ec0073000a1187a8006c000a270263006b00f9c8389b0069161a25e3e400680011085249005f000d41bf6a005e00127578b4005d000c557961005c03bad3c0bc005b9284838f7b005a0222776f8b00590080e06200004d02e5e0fece004b0002038188004a00076230480049001148c27a004800ec460900004777dc852fba0045⟩,
  ⟨33, 48, 0x70c455c0081000533b94a008000064af4c9007e06e88720d2007d000549340500770006b65a70007600002af57600750004f34919007300051e3e8f006e00055eaec0006d00045cedfc006c000487e372006a058afbe1b0006931b474d13d00680bcc4a88af00670005df8f22005f00047268b7005e00051e3e8f005d000574297b005c0ad2575a9e005bb7fe027e8c005a0f0d09bc96005900047268b7005300012cb63a004f00012cb63a004e00022e76fe004d0002da4cd6004c00016d266b004b0003c692df004a0002da4cd60049000549340500480003c692df00470006a0dfb50046⟩,
  ⟨29, 46, 0xabd5d8008100111dcd040200002038188007e009b63e0d401f40045cedfc00770005b499ac01d80805f819e0073000e188ab801b00039b9d69006a0010c7e21801a400243f1b900681d2c75c47c019c0039b9d69005e000101c0c401700903b1dad005b02ddfdee240168774e630e50059000dc29fcc01500012cb63a005300080e06200140000c15093004f0002af57600138002038188004d000b13486c0130000d6cb4e004b000cc0df0801280028461ea00490011c9a2dc01220a6ae5ec20047⟩,
  ⟨17, 44, 0x20381880080095c4c1e3007d001c31157007300c6af41c006c0031abd07006a00ded954200691468de2fc00687a361c993006700182a126005e04f349190005b118932ab0005aa9f136e4d0059000c15093005300e6e75a40050002038188004aedf247f05004900dd81a870048⟩,
  ⟨20, 36, 0x431f8860080abd5d80007d533b94a0077abd5d8000737b81b34006d5493405006af1a4b7c0069838fb9600681173b7f005f35b2d38005d574297b005c055eaec005b4b2d8e8005a1ad969c00500abd5d8004f243f1b9004d218fc43004c3c692df004b7373ad2004acebd47e0049⟩,
  ⟨25, 44, 0x9ba45105007d19bf7ee9a00737660c559a00720138cb433006e014a3efb2006c015a5b076006b08c748ace006a204d933b000691111b7fad00685c7900516006702b8bd11d00610246a110600603965434fb005f6de1fae3e005d34cff328d005c21e457705005b25a83af7f005a8cc66eb6f0059042892d43005401bdb2a840051016bcebf5005001ad969c0004f00e83f05f004e4567811c1004b00080e062004a⟩,
  ⟨23, 50, 0x20381880080000167c7bc401f40011b4282100750005239d3dc01d005a6d70c3400730003c692df001b8000d97aa56006c0003abb975401ac008cca75ba006a0060174d11c01a40136b246ed006801fbbeaf6e801840010069185006000046d0a084017c000e58fae9005e02f62d5f32c017407ba74a074005c00f0b313084016c01f72c0e9f005a03160a2e1800164000e43802e00510003ec29a6401437df3181bd0004b⟩,
  ⟨27, 53, 0x137739780200003eb7dd06800ec0000ba9a3890075002b42a7100803a00177b3745b401cc008ad1b18f800dc002d1680492006d0015b5cc824003600002495067c01ac003e6a0020a00d40033be165890069000037b6550803100705e4ec7c0018402149746fde00c1316a918222f005f0000467ab59802f0030a3595190017400e402500c800b80047807d5f1005b001ed7b2f40802d00000407031001500001651864e00a200009d1177700500000508c3d40027800029f3b53c0138000134c4402009a00009fc0ced004c⟩,
  ⟨24, 51, 0xa92680a010000041c7dcb001d80010922f44803a0008740d1840073001a862e2b600dc0029f3b53c001b4007eb1eb020036000084e7651006b000fd38e08e00d4000229184f401a4036cc128088033800f2a678840062008baddb8c400c200819c53e440180011a4b7ea9802f80001c31157005e0067411b2ee00ba0168388095c01640000a1187a802980009e69232005100011c9a2dc00a000003b11824013c0002a49a02802777b71d64f31004d⟩,
  ⟨32, 50, 0x14cee5280200002cf8f788007d00d2b42ee3c01dc00453884a3007600006606f8401d4000cc0df0800740002139d94401cc0169f6333e006f00021e5af1c01b801322a637b006d00407aee5d801b000082380db006b00551ede0f801a4005d4d1c4800680037153c8d8019001d7e03c28006300a7c417928018805df642c8a006100f565ebf040180032cdc94c8005f00005b499ac0178049d892276005d00000abd5d801700133419efa005a01f8739e42c01580001c31157005500013773978014c00fe908c3e005203a802fe6d401440008b9dbf800502540810a654013e943f33a59c004e⟩,
  ⟨32, 42, 0x14230f50020000c15093007e0111dcd0401dc04ddce5e007300b69335801bc02efc791006e046d0a08401b404477341006c012cb63a001ac0370a7f3006a014230f5001a409d11777006802a49a02801900cab644d0063207de75fc018992d2acfb0061000abd5d801800218fc43005f01173b7f0017804b2d8e8005d01173b7f00170012cb63a005b003b11824016b867898ec0059013cd2464015803b11824005500cc0df0801500508c3d40053002af5760014909636479005101d88c12001400b53b89d004f⟩,
  ⟨28, 43, 0xc150930010000f1a4b7c01f40182a126003b00533b94a0073223e495f600dc321c94c5c01b402af57600036005b499ac006b002596c7400d4013214e8c01a4070c455c003408161426200642848cdf7600c68f13c621c018aca5101d88030a617a7a20006051152ba8200be012cb63a001798e604444002e8039b9d69005c0e869fb6600b5feeee730801584a56c332002a802c4d21b005400ae852f600a62b00335d8014bd0af24058028ad213da6a0050⟩,
  ⟨22, 43, 0x2fa84ee8040004ddce5e007d006e14fe600ee00f1a4b7c01bc012cb63a0037005f509dd006d00c3ffea600d801a2d93e801ac0223b9a08035004f34919006800a3c7d1e00c8004b2d8e8018c17e9a22f0031133c27f5c0061008b9dbf800bc0035b2d38017401d88c12002e001173b7f005a89bd2567e00ac00965b1d0015400b69335802982dba481b0051⟩,
  ⟨29, 44, 0x533b94a0081002efc7910080000abd5d8007e007373ad2007d0d014f39000770044773410075009fc0ced00730642e6c2e006f07cd95ef0006e02c37a6f5006d07ceed9ab006c00299dca5006b008e4d16e006a002efc7910069003b11824006403a253c37006316416a41c0062cabcfb2a7006114a1405aa0060045e45a7b005f00243f1b9005e09b63e0d4005d0033037c2005c002af5760005b002596c74005a7e859de0500560105c7c710055006f6caa100530741f82f80052⟩,
  ⟨26, 45, 0x104701b6010200574297b00800000abd5d803f00157abb0001f400b69335800f40059f1ef1007700f1a4b7c003b001bdb2a8401d42f7d5972000de00574297b006e002da4cd600368012cb63a001b000a3c7d1e00d601ac3ef05006a09ef4c0df8032085079d288018fbf234203200c591312b6830061003257a6480300001ad969c017c009e6923200bc00965b1d0005d7eaa88d1b802b39384a582801547e3e7754e00a80993569d60053⟩,
  ⟨22, 47, 0x37b65508040800a51f7d900800014a3efb200ee100d47df7001d8005bf5709803a881b9dca56006f13aec4d79200dc0029f3b53c01b4004c853a300360009e69232006b00134c440200d42a1e54c71401914a938e60500318009a62201006200246a110600c2002c4d21b0018000553f162802f80049d5e2d005e001524d01400ba53973425ac015a59010e590002a88397c76620054⟩,
  ⟨20, 48, 0x7a2a07900810006cbd52b0080000721c017007d06cd175bf5007a1946d7833600770008b9dbf8007600671e33bf006f4cdc51d23a006e0006f6caa1006d00060a8498006c000675ea3f006b34ad4c2921006468f6d54bbb006300061fff530062000080e0620061000055eaec00600001981be1005f0003f18855005d0e33cf87670056c890dd98e40055⟩,
  ⟨12, 47, 0x74f64e460102002a49a02802002c7b72533803d0008fa4c290077bdfa18a0e800ea00b63d4a9401bacda0c5dd28036b110c27a18006c1a5dbd174a00d65553e50d28018e02b57a0f800310c8f1dbcd50056⟩,
  ⟨11, 45, 0x151966e0a802040104701b6010000838fb96007759355155e8037800b69335801b93ae43f73000db83b45a7bf006c4ad04163b8035b354085d40019107ee3007e00c48fd516b4c0061⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨25, 45, 0xb7eae1300810039b9d6900403af5a7157c01fc5f5e0a84e00fc003f18855007d15d8b3f22003d02230dcaa801d4c796291a400e8c9ea36df800732ba4a705380393b87fb2f6c01b0598938c0600d74c7ee5d5f006a351719b440034a1c8d230b801a0cc0891d1400ce116a523e300622f0be946680308ff2c4609c018110f08a37000be66f5eda06005e20d529f77002e96fd5c2600017155c5b739200b6aa08094b8005a⟩,
  ⟨14, 48, 0x2af5760081000080e062007d0287672c4c007308df72bf40007200068b64fa006e04b217976d006c00064af4c9006b3da43d24e9006a717ad37ac500690c36837975006806f359f90d00670084fcdfcb005d22f84d3cd3005cf899d4ca64005b⟩,
  ⟨18, 46, 0x2af5760020400508c3d40080000508c3d401f802cb88757007d000508c3d401d813092479a00731f6f65bcb801c8004477341006c00127578b401ac048284c34006a19aa5a198c01a670341d52800681c77902598019c004f349190061051c3b0d78017c004477341005e001ad969c001743286a2c11005c⟩,
  ⟨19, 43, 0xe188ab8020004273b28803e8016d266b0077012a06e2a00ea0a2c6111c01d0890ea03880399563e8995007208944530c00da374590b2401b0035b2d38003583d2a7e83006a1e272a43200d204cdb251c01a326e78aeb00338f1e527f10061005df8f2200c1da03f5c88017e5f0b92f1002f2c99a6ea3005d⟩,
  ⟨19, 44, 0x574297b00800006b65a7007e002c4d21b007d02352d587007600a51f7d900750f43e946500740c51725df007308b8844c5006e08ffaad7c006d12fd0f707006c0d8e44a43006b08ab17977006a1090d798d0069032c30bef006800863f10c0062541d1d4b800615b51a8c62006099cd1c9eb005f78b223c78005e⟩,
  ⟨13, 43, 0x33037c2008000407031000e755a2cfc9401c800ec4609003780182a126006e00508c3d400da18a03564801b005946193803582327e0110069b71c23e8200ce02a9f8b1401882540dc540030adea9c3fc005f⟩,
  ⟨19, 45, 0x17d427740200018d5e83800fa006357a0e007a003a65ac6803a802c4d21b001d01bc0511a400e661267a8aa0072021fb29d70037810f8363cc01b8084bc6f9a00da0e17330c5006c002cf8f788035814e9be91c01a81760b3c6e00d2628e4246e0067005ffc73a803200157abb00018a8c8d78e1200c26978f7deb0060⟩,
  ⟨17, 48, 0x2af576007e024a27330e007a0006606f840075000f04d0c10074002efc791000730435134307007200591b23c2006f0057c37812006e003ba7dd5d006d00d822f9b0006c00b958079b006b00419ce73a006a00674929350069000b13486c0068000a67729400640003c692df0062c43f6e4af70061⟩,
  ⟨14, 42, 0x26ee72f001f813a22eee0076895f2c75c01d4745ff3290074061aa0a4401cdc41317c4006f3ad670bdc01b877fb9092006d405ab645001b0d93a352f006b14aead0f801a84578f4d4006901d32d6340192e7e480560062⟩,
  ⟨6, 43, 0x60a849804047a364cef007a4dd78731400ea027445ddc01b00ab2a02280358a97c6b8c0064⟩,
  ⟨13, 48, 0x37d7e4cc3007791b6c8085f00763869e2fb340075522facd99d00745cc79e87d3006e5cadc6ded7006d201e6bcc7a006c0397407b04006b4b29f2e297006a4e23e175fa006900039b9d69006805e32abf69006700002af5760064⟩,
  ⟨11, 45, 0x33037c2001dd193f0088000ec00eef5606007500990a746003a0028461ea001bc014a3efb200dc00a92680a006d63630a13580360025ecb22c01ae3598be17000d4005b499ac0069⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨9, 44, 0x5e3403a2400814b217976d0080c9b32c605007f60550deb6007e7d4e2a48d007d561489ca5007a5fdd933b30074681537258007359146d6790072⟩,
  ⟨12, 47, 0x26429d180102003201bb5c02017df90a758003f800c95e992007ec1da2d3df800fa0036b4944401d46ab8797c5003a18b71d45eb0073123761ef7400e400111dcd0401ac280dbc752003512a5f7ce360069⟩,
  ⟨12, 50, 0x90fc6e40200000182a126007d02132ccfea401e8000d6cb4e00075a99e8c4c9e401d0435f4cbb28007302442cca82401c8024b696403006f0000762304801b805619e8791006c0001fe22d9401ac4169785839006a⟩,
  ⟨14, 47, 0x14230f50040000bff8e75007e00090fc6e400fa61455af77001ea8bc0bf1ac803b000cebd47e00755466f32e5000e848e037153001ccba62823af8039166d8c6dfa006f004f099c1a00dc00b48fb3f801b4a9146112380360009fc0ced006b⟩,
  ⟨9, 43, 0x74f4f69a5007a3dc0d9a0000ed83b302d0401d73449826d803a0006b65a70073c36c3e9a600e41c91bdb9801bcabaae28a0036d4e67be4a006c⟩,
  ⟨8, 46, 0x518fab9a9c01dcc49cfbd77007600f2508d9801d6ba86d981700742b9d9abfdc01cd1ffab9a6c006f028813022401b8cea116ca9006d⟩,
  ⟨8, 47, 0x3b1182401001d5fcf2b8801ea3b449de70803b80d431715b0076001a58895e00ea058eacf9d401d0123f1a0aa8037d3f039ceb3006e⟩,
  ⟨8, 49, 0x157abb000400001173b7f001f40b9d638a5a00f4000afdcdb100778446edadfa803b0003608be6c01d407ac5c15bc00e4002d3967b9006f⟩,
  ⟨7, 44, 0x33037c2007d5f1c42a83007ab4c2b7742007600d16c9f400753aba3fa85007430a0a9fa300734cef482b50072⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨9, 46, 0x2a80aaa7300819c9a52aabc01fc437ad1fac007e3c4e54864001f41d5465f83007a201ce92b5401d8168489ca2007511d8673c9001d0a4bd7d9ad0073⟩,
  ⟨4, 43, 0xb48fb3f8000f403c13430401dc082380db003a9e02eb2790074⟩,
  ⟨4, 42, 0x5b499ac01f800ec4609007ddf954604401d8104701b60075⟩,
  ⟨3, 43, 0xbbf1e4401fa31dce895803d0028461ea0077⟩,
  ⟨4, 48, 0x345b27d0080d4782c80c9007e0b55bc1e88007a3752fd67200077⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨3, 46, 0x24f4d7fa32007f174d3c8d6801f88fa8c9931007d⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨2, 37, 0x27f033b40102eef56060080⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩
]

def lowDirections : List Nat := [
  0x150e46b08966bed3ffc0effa08300410a,
  0xe87201803f07fefe7fbffe5f01e2020d,
  0x1602014001000002000004001c0303c,
  0x892000018817e061987fc1f7068ca1c,
  0x14a1827000440010c04241180642d0d,
  0x0,
  0x0,
  0x3002022003800003000086041c0301,
  0x0,
  0x0,
  0x3e1c5477019e0003f7415f840c01ca,
  0x2900000e0880020191808220070068,
  0x200008103e020406fe8bb31de7,
  0x880400820241000602220c01bc57,
  0x1c8c042500c10c613283806001c0b,
  0x2444012006900009400002000c01,
  0x0,
  0x0,
  0x1e3a402a01600002c00101800608,
  0xb01e06543b07d85e1198848071a,
  0x1f04400001f80795f09c17e00384,
  0x7800008d036bf80edf63bff01e6,
  0xc008002819778792c3fff7d8c7,
  0x180004034c8ac6021fe1c43806b,
  0x5c60a81d00586000ee1681e035,
  0xfd2604c04b00002620000c012,
  0x2c04000002000046000004002,
  0x0,
  0x0,
  0x783fb356f6c50047800003000,
  0x1c09085740e40012c00004000,
  0xe4bc5f0b7f00ffbe00407d1e,
  0x1780e010f978a0fff008076be,
  0xb809000000c72e5180603955,
  0x5e2e80038143963ccfd03cae,
  0x3f060041c081ff1f23dffc57,
  0x78303008962e1cf3fe00f3f,
  0xac001864001ef8187f0fd0f,
  0x1e4000005402040c3087a07,
  0xbe79c891a0000001c02943,
  0x82100c000400200800001,
  0x0,
  0x0,
  0xf93e86430f00001600080,
  0x724f86a497802007000c0,
  0xfa1a855201c0080786140,
  0x783601cd21e04087c39c0,
  0x2e1b882481f0004ba0060,
  0x178ff43bdd787077f04f0,
  0xfc7ff18effc3ffff83ff,
  0x5e3fd0cf4ff5d3fff3ec,
  0x2f1f4c63bb80efb781b7,
  0x1f8fef21d2c5f5ff8ff7,
  0xec60700e78279ff84fb,
  0x3f383807251783fe2fe,
  0x3f10301e20c787af87e,
  0x783f1ff0fffe0f7efe,
  0xe41f8decfbbffe0f7f,
  0x5aef7ade2b9f0fdf3f,
  0x2c151b6bd88fcf025d,
  0x47e0e01c54781c28b,
  0x2f802028f8280b787,
  0x15ad30073e18070c3,
  0x460002000840401,
  0x0,
  0x0,
  0x1388c21000600284,
  0xf27a0dc00b009c0,
  0x707d07a00780eb2,
  0xc8c807003c43e0,
  0x5e0b403817e37f0,
  0x3f07a05c0f71efc,
  0xd06f13e0df81ff,
  0xfc9f99f03fc71d,
  0x7e0944f847e1df,
  0x3d05a77c7bf1c0,
  0x1e8bf3a63ff866,
  0xf87cadf7ffdfa,
  0x581e1cbff7c7d,
  0x2e07a67fffffe,
  0x1f0f8729ffa7f,
  0x38763d0fc33f,
  0x1b0a1087901f,
  0x2c651c03854f,
  0x5f20e019d07,
  0x2394700e003,
  0x180c2804201,
  0x0,
  0x0,
  0x2fd1802000,
  0x5e4fc83800,
  0x2e87e05c10,
  0xf4ef1be08,
  0xfa179ff00,
  0x204fdef83,
  0x735ff7f0,
  0x26aeffd9,
  0x905e7f8f,
  0x28ee3f87,
  0xc30101b,
  0x2100811,
  0x0,
  0x0,
  0x200,
  0x1e0304,
  0xff03b0,
  0x35cbd0,
  0xce7e7,
  0xe76d5,
  0x73f07,
  0x7de8b,
  0x2ff85,
  0x0,
  0x0,
  0x380,
  0xfe0,
  0x672,
  0x13d,
  0x19f,
  0x28f,
  0x0,
  0x0,
  0x3,
  0x0,
  0x0,
  0x3,
  0x0,
  0x0,
  0x1,
  0x0
]

def lowHint (i j : Nat) : Nat :=
  5480 * ((lowHints[i]?.map fun row => row.entry j).getD 0)

def lowPrefer (i j : Nat) : Bool :=
  digit (lowDirections[i]?.getD 0) 1 (j-i-1) == 1

end OMA.Erdos1186Low

end

section

/- Reconstruct the box multipliers from prescribed symmetric quadratic coefficients. -/

namespace OMA.Erdos1186Low

private def positivePart (a : ℤ) : ℤ := max a 0

private def negativePart (a : ℤ) : ℤ := max (-a) 0

private theorem positive_sub_negative (a : ℤ) : positivePart a - negativePart a = a := by
  rcases le_total a 0 with h | h
  · have hn : 0 ≤ -a := by omega
    simp [positivePart, negativePart, max_eq_right h, max_eq_left hn]
  · have hn : -a ≤ 0 := by omega
    simp [positivePart, negativePart, max_eq_left h, max_eq_right hn]

/-- One orientation of a negative pair. The certificate supplies its shorter
share and the direction which receives the complement. Clamping makes every
decoded hint valid for the prescribed pair total. -/
private def firstShare (total : ℤ) (hint : ℕ) (preferFirst : Bool) : ℤ :=
  let bound := negativePart total
  let share := min bound (hint : ℤ)
  if preferFirst then bound - share else share

private theorem firstShare_bounds (total : ℤ) (hint : ℕ) (preferFirst : Bool) :
    0 ≤ firstShare total hint preferFirst ∧ firstShare total hint preferFirst ≤ negativePart total := by
  have hb : 0 ≤ negativePart total := le_max_right _ _
  have hm : 0 ≤ min (negativePart total) (hint : ℤ) :=
    le_min hb (Int.natCast_nonneg _)
  have hu : min (negativePart total) (hint : ℤ) ≤ negativePart total := min_le_left _ _
  cases preferFirst <;> simp only [firstShare, Bool.false_eq_true, if_false, if_true] <;> omega

/-- The coefficient of `y i * y j` assigned directly to a nonnegative box term. -/
def yy (R : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  if i = j then positivePart (R i i)
  else if i < j then positivePart (R i j + R j i) else 0

/-- The coefficient of `y i * (1 - y j)`, directed by one hint per unordered pair. -/
def yo (R : ℕ → ℕ → ℤ) (hint : ℕ → ℕ → ℕ) (preferFirst : ℕ → ℕ → Bool) (i j : ℕ) : ℤ :=
  if i = j then negativePart (R i i)
  else if i < j then firstShare (R i j + R j i) (hint i j) (preferFirst i j)
  else negativePart (R j i + R i j) - firstShare (R j i + R i j) (hint j i) (preferFirst j i)

theorem yy_nonneg (R : ℕ → ℕ → ℤ) (i j : ℕ) : 0 ≤ yy R i j := by
  unfold yy
  split
  · exact le_max_right _ _
  · split
    · exact le_max_right _ _
    · exact le_rfl

theorem yo_nonneg (R : ℕ → ℕ → ℤ) (hint : ℕ → ℕ → ℕ) (preferFirst : ℕ → ℕ → Bool)
    (i j : ℕ) : 0 ≤ yo R hint preferFirst i j := by
  unfold yo
  split
  · exact le_max_right _ _
  · split
    · exact (firstShare_bounds _ _ _).1
    · exact sub_nonneg.mpr (firstShare_bounds _ _ _).2

private theorem coefficient_lt (R : ℕ → ℕ → ℤ) (hint : ℕ → ℕ → ℕ)
    (preferFirst : ℕ → ℕ → Bool) {i j : ℕ} (h : i < j) :
    (yy R i j - yo R hint preferFirst i j) + (yy R j i - yo R hint preferFirst j i) =
      R i j + R j i := by
  simp only [yy, yo, if_neg h.ne, if_neg h.ne.symm, if_pos h, if_neg (Nat.not_lt.mpr h.le)]
  have hc := positive_sub_negative (R i j + R j i)
  omega

/-- The directed coefficients realize the quadratic part by construction. -/
theorem coefficient_symmetric (R : ℕ → ℕ → ℤ) (hint : ℕ → ℕ → ℕ)
    (preferFirst : ℕ → ℕ → Bool) (i j : ℕ) :
    (yy R i j - yo R hint preferFirst i j) + (yy R j i - yo R hint preferFirst j i) =
      R i j + R j i := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact coefficient_lt R hint preferFirst h
  · simp [yy, yo, positive_sub_negative]
  · rw [add_comm (yy R i j - yo R hint preferFirst i j), add_comm (R i j)]
    exact coefficient_lt R hint preferFirst h

end OMA.Erdos1186Low

end

section

/- Integer coefficient reconstruction is sound for the corresponding real polynomial. -/

namespace OMA.Erdos1186Low

open Finset
open scoped BigOperators

def residual (B N : ℕ → ℕ → ℤ) (v L : ℕ → ℤ) (i j : ℕ) : ℤ :=
  5480 * (B i j - N i j) + 5 * v i * L j

def rowBudget (S : Finset ℕ) (A v : ℕ → ℤ) (R : ℕ → ℕ → ℤ)
    (hint : ℕ → ℕ → ℕ) (prefer : ℕ → ℕ → Bool) (i : ℕ) : ℤ :=
  5480 * A i - 1096 * v i - ∑ j ∈ S, yo R hint prefer i j

noncomputable def evalLinear (S : Finset ℕ) (A : ℕ → ℝ) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ S, A i * y i

noncomputable def evalQuad (S : Finset ℕ) (A : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, A i j * y i * y j

private theorem double_evalQuad (S : Finset ℕ) (A : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    2 * evalQuad S A y = evalQuad S (fun i j => A i j + A j i) y := by
  have hswap : evalQuad S (fun i j => A j i) y = evalQuad S A y := by
    unfold evalQuad
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  unfold evalQuad at hswap ⊢
  simp only [two_mul, add_mul, sum_add_distrib]
  rw [hswap]

private theorem evalQuad_eq_of_symmetric (S : Finset ℕ) (A B : ℕ → ℕ → ℝ)
    (h : ∀ i j, A i j + A j i = B i j + B j i) (y : ℕ → ℝ) :
    evalQuad S A y = evalQuad S B y := by
  apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
  rw [double_evalQuad, double_evalQuad]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ =>
    congrArg (fun x : ℝ => x * y i * y j) (h i j)

private theorem evalQuad_residual (S : Finset ℕ) (B N : ℕ → ℕ → ℤ) (v L : ℕ → ℤ)
    (y : ℕ → ℝ) :
    evalQuad S (fun i j => (residual B N v L i j : ℝ)) y =
      5480 * (evalQuad S (fun i j => (B i j : ℝ)) y - evalQuad S (fun i j => (N i j : ℝ)) y) +
        5 * evalLinear S (fun i => (v i : ℝ)) y * evalLinear S (fun i => (L i : ℝ)) y := by
  have product : (∑ i ∈ S, ∑ j ∈ S, 5 * (v i : ℝ) * L j * y i * y j) =
      5 * evalLinear S (fun i => (v i : ℝ)) y * evalLinear S (fun i => (L i : ℝ)) y := by
    calc
      _ = ∑ i ∈ S, (5 * ((v i : ℝ) * y i)) * evalLinear S (fun j => (L j : ℝ)) y := by
        apply sum_congr rfl
        intro i _
        unfold evalLinear
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring
      _ = _ := by
        rw [← sum_mul, ← mul_sum]
        rfl
  unfold evalQuad
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, (
        5480 * ((B i j : ℝ) * y i * y j - (N i j : ℝ) * y i * y j) +
          5 * (v i : ℝ) * L j * y i * y j) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      unfold residual
      push_cast
      ring
    _ = (∑ i ∈ S, ∑ j ∈ S, 5480 * ((B i j : ℝ) * y i * y j - (N i j : ℝ) * y i * y j)) +
          (∑ i ∈ S, ∑ j ∈ S, 5 * (v i : ℝ) * L j * y i * y j) := by
      simp only [sum_add_distrib]
    _ = _ := by
      rw [product]
      simp_rw [mul_sub, sum_sub_distrib, ← mul_sum]

/-- Evaluation of the reconstructed linear, box and mass terms, plus the Gram term. -/
theorem reconstructed_polynomial (S : Finset ℕ) (A v L : ℕ → ℤ) (B N : ℕ → ℕ → ℤ)
    (hint : ℕ → ℕ → ℕ) (prefer : ℕ → ℕ → Bool) (y : ℕ → ℝ) :
    let R := residual B N v L
    let Y := yy R
    let O := yo R hint prefer
    let budget := rowBudget S A v R hint prefer
    (5480 : ℝ) * (evalLinear S (fun i => (A i : ℝ)) y + evalQuad S (fun i j => (B i j : ℝ)) y) =
      5480 * evalQuad S (fun i j => (N i j : ℝ)) y + evalLinear S (fun i => (budget i : ℝ)) y +
      evalQuad S (fun i j => (Y i j : ℝ)) y +
      (∑ i ∈ S, ∑ j ∈ S, (O i j : ℝ) * y i * (1 - y j)) +
      5480 * evalLinear S (fun i => (v i : ℝ)) y * (1/5 - evalLinear S (fun i => (L i : ℝ)) y / 1096) := by
  let R := residual B N v L
  let Y := yy R
  let O := yo R hint prefer
  let budget := rowBudget S A v R hint prefer
  change _ = 5480 * evalQuad S (fun i j => (N i j : ℝ)) y + evalLinear S (fun i => (budget i : ℝ)) y +
      evalQuad S (fun i j => (Y i j : ℝ)) y +
      (∑ i ∈ S, ∑ j ∈ S, (O i j : ℝ) * y i * (1 - y j)) +
      5480 * evalLinear S (fun i => (v i : ℝ)) y * (1/5 - evalLinear S (fun i => (L i : ℝ)) y / 1096)
  have hquad : evalQuad S (fun i j => (R i j : ℝ)) y =
      evalQuad S (fun i j => (Y i j : ℝ)) y - evalQuad S (fun i j => (O i j : ℝ)) y := by
    calc
      _ = evalQuad S (fun i j => (Y i j : ℝ) - (O i j : ℝ)) y := by
        apply evalQuad_eq_of_symmetric
        intro i j
        exact_mod_cast (coefficient_symmetric R hint prefer i j).symm
      _ = _ := by simp only [evalQuad, sub_mul, sum_sub_distrib]
  have hBR := evalQuad_residual S B N v L y
  change evalQuad S (fun i j => (R i j : ℝ)) y = _ at hBR
  have hlin : evalLinear S (fun i => (budget i : ℝ)) y =
      5480 * evalLinear S (fun i => (A i : ℝ)) y - 1096 * evalLinear S (fun i => (v i : ℝ)) y -
        ∑ i ∈ S, ∑ j ∈ S, (O i j : ℝ) * y i := by
    unfold evalLinear
    calc
      _ = ∑ i ∈ S, (5480 * ((A i : ℝ) * y i) - 1096 * ((v i : ℝ) * y i) -
          ∑ j ∈ S, (O i j : ℝ) * y i) := by
        apply sum_congr rfl
        intro i hi
        dsimp only [budget, rowBudget, O]
        push_cast
        rw [← sum_mul]
        ring
      _ = _ := by simp only [sum_sub_distrib, mul_sum]
  have hbox : (∑ i ∈ S, ∑ j ∈ S, (O i j : ℝ) * y i * (1 - y j)) =
      (∑ i ∈ S, ∑ j ∈ S, (O i j : ℝ) * y i) - evalQuad S (fun i j => (O i j : ℝ)) y := by
    simp only [evalQuad, mul_sub, mul_one, sum_sub_distrib]
  rw [hlin, hbox]
  nlinarith only [hquad, hBR]

end OMA.Erdos1186Low

end

section

/-
An integer Gram witness and exact row dominance imply nonnegativity over the reals.

This is a finite-set version of the certificate principle used by Chandler Snively
in `erdos-1186` v1.0.0, `P1186Cert128Lib.psd_of_dom` and `P1186M2CertLib.Cert.psd`.
-/

namespace OMA.Erdos1186IntegerPSD

open Finset
open scoped BigOperators

variable {ι κ : Type*}

def quadratic (V : Finset ι) (A : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ V, ∑ j ∈ V, A i j * x i * x j

private theorem rowTerm_ge {a u v : ℝ} :
    0 ≤ 2 * a * u * v + |a| * (u ^ 2 + v ^ 2) := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    have heq : 2 * a * u * v + a * (u ^ 2 + v ^ 2) = a * (u + v)^2 := by ring
    rw [heq]
    exact mul_nonneg ha (sq_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge ha)]
    have heq : 2 * a * u * v + (-a) * (u ^ 2 + v ^ 2) = (-a) * (u - v)^2 := by ring
    rw [heq]
    exact mul_nonneg (neg_nonneg.mpr (le_of_lt (lt_of_not_ge ha))) (sq_nonneg _)

theorem quadratic_nonneg_of_dominance (V : Finset ι) (E : ι → ι → ℝ)
    (hsym : ∀ i ∈ V, ∀ j ∈ V, E i j = E j i)
    (hdom : ∀ i ∈ V, (∑ j ∈ V, |E i j|) ≤ 2 * E i i) (x : ι → ℝ) :
    0 ≤ quadratic V E x := by
  classical
  have hdiag (i) (hi : i ∈ V) : 0 ≤ E i i := by
    have hn : 0 ≤ ∑ j ∈ V, |E i j| := sum_nonneg (fun j _ => abs_nonneg _)
    exact nonneg_of_mul_nonneg_right (hn.trans (hdom i hi)) zero_lt_two
  have hpoint (i) (hi : i ∈ V) (j) :
      (if i = j then 4 * E i i * (x i)^2 else 0) ≤
        2 * (E i j * x i * x j) + (|E i j| * (x i)^2 + |E i j| * (x j)^2) := by
    by_cases h : i = j
    · subst j
      simp only [if_true, abs_of_nonneg (hdiag i hi)]
      exact le_of_eq (by ring)
    · rw [if_neg h]
      have h := rowTerm_ge (a := E i j) (u := x i) (v := x j)
      have heq : 2 * E i j * x i * x j = 2 * (E i j * x i * x j) := by ring
      rw [heq, mul_add] at h
      exact h
  have hsum : (∑ i ∈ V, ∑ j ∈ V, if i = j then 4 * E i i * (x i)^2 else 0) ≤
      ∑ i ∈ V, ∑ j ∈ V,
        (2 * (E i j * x i * x j) + (|E i j| * (x i)^2 + |E i j| * (x j)^2)) :=
    sum_le_sum (fun i hi => sum_le_sum (fun j _ => hpoint i hi j))
  have hleft : (∑ i ∈ V, ∑ j ∈ V, if i = j then 4 * E i i * (x i)^2 else 0) =
      ∑ i ∈ V, 4 * E i i * (x i)^2 := by
    apply sum_congr rfl
    intro i hi
    simp [hi]
  have hright : (∑ i ∈ V, ∑ j ∈ V, |E i j| * (x j)^2) =
      ∑ i ∈ V, ∑ j ∈ V, |E i j| * (x i)^2 := by
    rw [sum_comm]
    exact sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => by rw [hsym i hi j hj]))
  have hmass : (∑ i ∈ V, ∑ j ∈ V, |E i j| * (x i)^2) ≤
      ∑ i ∈ V, 2 * E i i * (x i)^2 := by
    simp_rw [← sum_mul]
    exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hdom i hi) (sq_nonneg _))
  rw [hleft] at hsum
  simp_rw [sum_add_distrib, ← mul_sum] at hsum
  rw [hright] at hsum
  have hfactor : (∑ i ∈ V, 4 * E i i * (x i)^2) = 2 * ∑ i ∈ V, 2 * E i i * (x i)^2 := by
    rw [mul_sum]
    exact sum_congr rfl (fun i _ => by ring)
  rw [hfactor] at hsum
  unfold quadratic
  apply nonneg_of_mul_nonneg_right _ zero_lt_two
  have ht := hsum.trans (add_le_add_right (add_le_add hmass hmass) _)
  let U := ∑ i ∈ V, ∑ j ∈ V, E i j * x i * x j
  let B := ∑ i ∈ V, 2 * E i i * (x i)^2
  have ht' : 0 ≤ 2 * U + (B + B) - 2 * B := sub_nonneg.mpr ht
  change 0 ≤ 2 * U
  rwa [← two_mul, add_sub_cancel_right] at ht'

theorem quadratic_gram (V : Finset ι) (K : Finset κ) (C : ι → κ → ℝ) (x : ι → ℝ) :
    quadratic V (fun i j => ∑ k ∈ K, C i k * C j k) x =
      ∑ k ∈ K, (∑ i ∈ V, C i k * x i)^2 := by
  unfold quadratic
  calc
    _ = ∑ i ∈ V, ∑ j ∈ V, ∑ k ∈ K, (C i k * x i) * (C j k * x j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      simp_rw [sum_mul]
      exact sum_congr rfl (fun k _ => by ring)
    _ = ∑ i ∈ V, ∑ k ∈ K, ∑ j ∈ V, (C i k * x i) * (C j k * x j) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ k ∈ K, ∑ i ∈ V, ∑ j ∈ V, (C i k * x i) * (C j k * x j) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k _
      simp_rw [← mul_sum]
      rw [← sum_mul, pow_two]

def intResidual (K : Finset κ) (S : ℤ) (N : ι → ι → ℤ) (C : ι → κ → ℤ) (i j : ι) : ℤ :=
  S * N i j - ∑ k ∈ K, C i k * C j k

theorem intQuadratic_nonneg (V : Finset ι) (K : Finset κ) (S : ℤ) (hS : 0 < S)
    (N : ι → ι → ℤ) (C : ι → κ → ℤ)
    (hN : ∀ i ∈ V, ∀ j ∈ V, N i j = N j i)
    (hdom : ∀ i ∈ V, (∑ j ∈ V, |intResidual K S N C i j|) ≤ 2 * intResidual K S N C i i)
    (x : ι → ℝ) : 0 ≤ quadratic V (fun i j => (N i j : ℝ)) x := by
  let E := intResidual K S N C
  have hE : ∀ i ∈ V, ∀ j ∈ V, (E i j : ℝ) = E j i := by
    intro i hi j hj
    congr 1
    dsimp [E, intResidual]
    rw [hN i hi j hj]
    congr 1
    exact sum_congr rfl (fun k _ => mul_comm _ _)
  have hR (i) (hi : i ∈ V) : (∑ j ∈ V, |(E i j : ℝ)|) ≤ 2 * E i i := by
    exact_mod_cast hdom i hi
  have hPSD := quadratic_nonneg_of_dominance V (fun i j => (E i j : ℝ)) hE hR x
  have hG : 0 ≤ quadratic V (fun i j => ∑ k ∈ K, (C i k : ℝ) * C j k) x := by
    rw [quadratic_gram]
    exact sum_nonneg (fun k _ => sq_nonneg _)
  have hsplit : (S : ℝ) * quadratic V (fun i j => (N i j : ℝ)) x =
      quadratic V (fun i j => (E i j : ℝ)) x +
        quadratic V (fun i j => ∑ k ∈ K, (C i k : ℝ) * C j k) x := by
    simp only [quadratic, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    dsimp [E, intResidual]
    push_cast
    ring
  exact nonneg_of_mul_nonneg_right (hsplit.symm ▸ add_nonneg hPSD hG)
    (show (0 : ℝ) < S by exact_mod_cast hS)

theorem scaledQuadratic_nonneg (V : Finset ι) (K : Finset κ) (S : ℤ) (hS : 0 < S)
    (N : ι → ι → ℤ) (C : ι → κ → ℤ)
    (hN : ∀ i ∈ V, ∀ j ∈ V, N i j = N j i)
    (hdom : ∀ i ∈ V, (∑ j ∈ V, |intResidual K S N C i j|) ≤ 2 * intResidual K S N C i i)
    (A : ι → ι → ℝ) (D : ℝ) (hD : 0 < D)
    (hscale : ∀ i ∈ V, ∀ j ∈ V, (N i j : ℝ) = D * A i j) (x : ι → ℝ) :
    0 ≤ quadratic V A x := by
  have h := intQuadratic_nonneg V K S hS N C hN hdom x
  have heq : D * quadratic V A x = quadratic V (fun i j => (N i j : ℝ)) x := by
    unfold quadratic
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    change D * (A i j * x i * x j) = (N i j : ℝ) * x i * x j
    rw [hscale i hi j hj]
    ring
  exact nonneg_of_mul_nonneg_right (heq.symm ▸ h) hD

end OMA.Erdos1186IntegerPSD

end

section

/- Connect kernel-friendly finite row comparisons to the real Gram lemma. -/

namespace OMA.Erdos1186Low

open Finset OMA.Erdos1186IntegerPSD
open scoped BigOperators

def rowDot : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a*b + rowDot as bs
  | _, _ => 0

private def absResidualSum (N : ℕ → ℕ → ℤ) (i : ℕ) (row : List ℤ) :
    ℕ → List (List ℤ) → ℕ
  | _, [] => 0
  | j, next :: rows =>
    (N i j - rowDot row next).natAbs + absResidualSum N i row (j+1) rows

def dominanceCheck (N : ℕ → ℕ → ℤ) (C : List (List ℤ)) (i : ℕ) : Bool :=
  match C[i]? with
  | none => false
  | some row => decide ((absResidualSum N i row 0 C : ℤ) ≤ 2*(N i i - rowDot row row))

private theorem rowDot_eq_sum (n : ℕ) (u v : List ℤ) (hu : u.length ≤ n) :
    rowDot u v = ∑ k ∈ range n, (u[k]?.getD 0) * (v[k]?.getD 0) := by
  induction n generalizing u v with
  | zero =>
    have he : u = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hu)
    subst u
    simp [rowDot]
  | succ n ih =>
    cases u with
    | nil => simp [rowDot]
    | cons a u =>
      cases v with
      | nil => simp [rowDot]
      | cons b v =>
        rw [sum_range_succ']
        have hu' : u.length ≤ n := Nat.le_of_succ_le_succ hu
        simp [rowDot, ih u v hu', add_comm]

private theorem absResidualSum_eq (N : ℕ → ℕ → ℤ) (i : ℕ) (r : List ℤ) (j : ℕ)
    (rows : List (List ℤ)) : (absResidualSum N i r j rows : ℤ) =
      ∑ k ∈ range rows.length, |N i (j+k) - rowDot r (rows[k]?.getD [])| := by
  induction rows generalizing j with
  | nil => simp [absResidualSum]
  | cons u rows ih =>
    rw [List.length_cons, sum_range_succ']
    simp [absResidualSum, ih, Nat.add_left_comm, add_comm]

private theorem residual_dominance (N : ℕ → ℕ → ℤ) (C : List (List ℤ)) (i : ℕ)
    (hi : i < C.length) (hlen : ∀ row ∈ C, row.length ≤ C.length)
    (hcheck : dominanceCheck N C i = true) :
    let c := fun a k => (C[a]?.getD [])[k]?.getD 0
    let E := intResidual (range C.length) 1 N c
    (∑ j ∈ range C.length, |E i j|) ≤ 2 * E i i := by
  let r := C[i]
  have hrow : C[i]? = some r := List.getElem?_eq_getElem hi
  have hrlen : r.length ≤ C.length := hlen r (List.getElem_mem hi)
  simp only [dominanceCheck, hrow, decide_eq_true_eq] at hcheck
  rw [absResidualSum_eq] at hcheck
  simp only [Nat.zero_add] at hcheck
  have hE (j : ℕ) :
      intResidual (range C.length) 1 N (fun a k => (C[a]?.getD [])[k]?.getD 0) i j =
        N i j - rowDot r (C[j]?.getD []) := by
    simp only [intResidual, one_mul, hrow, Option.getD_some, rowDot_eq_sum C.length r _ hrlen]
  dsimp only
  simp_rw [hE, hrow, Option.getD_some]
  exact hcheck

theorem quadratic_nonneg_of_rows (N : ℕ → ℕ → ℤ) (C : List (List ℤ))
    (hsym : ∀ i j, N i j = N j i) (hlen : ∀ row ∈ C, row.length ≤ C.length)
    (hcheck : ∀ i < C.length, dominanceCheck N C i = true) (x : ℕ → ℝ) :
    0 ≤ quadratic (range C.length) (fun i j => (N i j : ℝ)) x := by
  refine intQuadratic_nonneg (range C.length) (range C.length) 1 (by decide) N
    (fun a k => (C[a]?.getD [])[k]?.getD 0) (fun i _ j _ => hsym i j) ?_ x
  intro i hi
  exact residual_dominance N C i (mem_range.mp hi) hlen (hcheck i (mem_range.mp hi))

end OMA.Erdos1186Low

end

section

/- Exact integer row tests used by the low-slab proof. -/

namespace OMA.Erdos1186Low

open Finset
open scoped BigOperators
open OMA.Erdos1186Region2

def lowA (i : ℕ) : ℤ :=
  (lowD / 300304 : Nat) * (OMA.Erdos1186Region2.digit g24AlphaWord 9 (min i (129-i)) : ℤ)

def lowV (i : ℕ) : ℤ := lowYhm.entry i

def lowL (i : ℕ) : ℤ := g24Length i

def lowBeta (i : ℕ) : ℤ :=
  (lowD / 1801824 : Nat) * (OMA.Erdos1186Region2.digit g24BetaWord 9 (min i (129-i)) : ℤ)

def lowPairCoeff (i j : ℕ) : ℤ :=
  lowPairTag i j * (300 * (lowQ : ℤ) * lowL i * lowL j)

def lowB (i j : ℕ) : ℤ := lowPairCoeff i j + if i = j then lowBeta i else 0

def lowR : ℕ → ℕ → ℤ := residual lowB lowMatrix lowV lowL

def budgetCheck (i : ℕ) : Bool := decide
  (0 ≤ 5480 * lowA i - 1096 * lowV i - ((List.range 130).map (yo lowR lowHint lowPrefer i)).sum)

def lowDominanceCheck (i : ℕ) : Bool := dominanceCheck lowMatrix lowCholesky i

private theorem sum_map_range (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem budget_of_check (i : ℕ) (h : budgetCheck i = true) :
    0 ≤ rowBudget (range 130) lowA lowV lowR lowHint lowPrefer i := by
  simpa only [budgetCheck, rowBudget, decide_eq_true_eq, sum_map_range] using h

private theorem cholCount : lowCholesky.length = 130 := by decide +kernel

private theorem cholLength : ∀ row ∈ lowCholesky, row.length ≤ lowCholesky.length := by
  have h : lowCholesky.all (fun row => decide (row.length ≤ 130)) = true := by decide +kernel
  intro row hrow
  rw [cholCount]
  exact of_decide_eq_true (List.all_eq_true.mp h row hrow)

theorem low_matrix_nonneg (h : ∀ i < 130, lowDominanceCheck i = true) (y : ℕ → ℝ) :
    0 ≤ evalQuad (range 130) (fun i j => (lowMatrix i j : ℝ)) y := by
  change 0 ≤ OMA.Erdos1186IntegerPSD.quadratic (range 130) (fun i j => (lowMatrix i j : ℝ)) y
  rw [← cholCount]
  refine quadratic_nonneg_of_rows lowMatrix lowCholesky (lowerEntry_comm 800 lowN) cholLength ?_ y
  intro i hi
  exact h i (cholCount ▸ hi)

end OMA.Erdos1186Low

end

section

/- Soundness of the concrete low-slab witness given the two finite row-check families. -/

namespace OMA.Erdos1186Low

open Finset
open scoped BigOperators
open OMA.Erdos1186Region2

private theorem lowA_real (i : ℕ) : (lowA i : ℝ) = (lowD : ℝ) * g24RealAlpha i := by
  unfold lowA g24RealAlpha
  rw [show lowD / 300304 = 1319413953331200 by decide +kernel]
  push_cast
  norm_num [lowD]
  ring

private theorem lowBeta_real (i : ℕ) : (lowBeta i : ℝ) = (lowD : ℝ) * g24RealBeta i := by
  unfold lowBeta g24RealBeta
  rw [show lowD / 1801824 = 219902325555200 by decide +kernel]
  push_cast
  norm_num [lowD]
  ring

private theorem pairCoeff_le (i j : ℕ) (u v : ℝ) :
    (lowPairCoeff i j : ℝ) * u * v ≤ (lowD : ℝ) * pairObjective i j u v := by
  have he : (lowPairCoeff i j : ℝ) * u * v = (lowD : ℝ) *
      ((lowPairTag i j : ℝ) * ((g24Length i : ℝ) * g24Length j / 1096^2 * (u*v))) := by
    unfold lowPairCoeff lowL lowD lowQ
    push_cast
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (lowPairTag_mul_le i j u v) (Nat.cast_nonneg lowD : (0:ℝ) ≤ lowD)

private theorem evalQuad_lowB (y : ℕ → ℝ) :
    evalQuad (range 130) (fun i j => (lowB i j : ℝ)) y =
      evalQuad (range 130) (fun i j => (lowPairCoeff i j : ℝ)) y +
        ∑ i ∈ range 130, (lowBeta i : ℝ) * y i^2 := by
  have hc (i j : ℕ) : (lowB i j : ℝ) = (lowPairCoeff i j : ℝ) + if i=j then (lowBeta i : ℝ) else 0 := by
    by_cases h : i=j <;> simp [lowB,h]
  unfold evalQuad
  simp_rw [hc, add_mul, sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single i]
  · simp [pow_two, mul_assoc]
  · intro j _ hji
    simp [Ne.symm hji]
  · exact fun hn => False.elim (hn hi)

private theorem weighted_objective_le (y : ℕ → ℝ) :
    evalLinear (range 130) (fun i => (lowA i : ℝ)) y +
      evalQuad (range 130) (fun i j => (lowB i j : ℝ)) y ≤ (lowD : ℝ) * g24Objective y := by
  have hlin : evalLinear (range 130) (fun i => (lowA i : ℝ)) y +
        ∑ i ∈ range 130, (lowBeta i : ℝ) * y i^2 =
      (lowD : ℝ) * ∑ i ∈ range 130, (g24RealAlpha i * y i + g24RealBeta i * y i^2) := by
    unfold evalLinear
    rw [← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp only
    rw [lowA_real, lowBeta_real]
    ring
  have hpair : evalQuad (range 130) (fun i j => (lowPairCoeff i j : ℝ)) y ≤
      (lowD : ℝ) * ∑ i ∈ range 130, ∑ j ∈ range 130, pairObjective i j (y i) (y j) := by
    unfold evalQuad
    simp_rw [mul_sum]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => pairCoeff_le i j (y i) (y j)
  unfold g24Objective cellCount
  rw [evalQuad_lowB, mul_add]
  linarith only [hlin,hpair]

private theorem mass_eval (y : ℕ → ℝ) :
    evalLinear (range 130) (fun i => (lowL i : ℝ)) y / 1096 = g24Mass y := by
  unfold evalLinear g24Mass cellCount
  rw [div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro i _
  unfold lowL
  push_cast
  ring

theorem low_box_of_checks (hdom : ∀ i < 130, lowDominanceCheck i = true)
    (hbudget : ∀ i < 130, budgetCheck i = true) (y : ℕ → ℝ)
    (hy : ∀ i < 130, 0 ≤ y i ∧ y i ≤ 1) (_hm0 : 0 ≤ g24Mass y)
    (hm1 : g24Mass y ≤ (1/5 : ℝ)) : 0 ≤ g24Objective y := by
  have hMatrix := low_matrix_nonneg hdom y
  have hLin : 0 ≤ evalLinear (range 130) (fun i => (rowBudget (range 130) lowA lowV lowR lowHint lowPrefer i : ℝ)) y := by
    apply sum_nonneg
    intro i hi
    change 0 ≤ (rowBudget (range 130) lowA lowV lowR lowHint lowPrefer i : ℝ) * y i
    exact mul_nonneg (by exact_mod_cast budget_of_check i (hbudget i (mem_range.mp hi))) (hy i (mem_range.mp hi)).1
  have hYY : 0 ≤ evalQuad (range 130) (fun i j => (yy lowR i j : ℝ)) y := by
    apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    change 0 ≤ (yy lowR i j : ℝ) * y i * y j
    exact mul_nonneg (mul_nonneg (by exact_mod_cast yy_nonneg lowR i j) (hy i (mem_range.mp hi)).1)
      (hy j (mem_range.mp hj)).1
  have hYO : 0 ≤ ∑ i ∈ range 130, ∑ j ∈ range 130, (yo lowR lowHint lowPrefer i j : ℝ) * y i * (1-y j) := by
    apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (by exact_mod_cast yo_nonneg lowR lowHint lowPrefer i j)
      (hy i (mem_range.mp hi)).1) (sub_nonneg.mpr (hy j (mem_range.mp hj)).2)
  have hV : 0 ≤ evalLinear (range 130) (fun i => (lowV i : ℝ)) y := by
    apply sum_nonneg
    intro i hi
    exact mul_nonneg (by unfold lowV; positivity) (hy i (mem_range.mp hi)).1
  have hMass : 0 ≤ 5480 * evalLinear (range 130) (fun i => (lowV i : ℝ)) y *
      (1/5 - evalLinear (range 130) (fun i => (lowL i : ℝ)) y / 1096) := by
    rw [mass_eval]
    exact mul_nonneg (mul_nonneg (by norm_num) hV) (sub_nonneg.mpr hm1)
  have hDec := reconstructed_polynomial (range 130) lowA lowV lowL lowB lowMatrix lowHint lowPrefer y
  change (5480 : ℝ) * (evalLinear (range 130) (fun i => (lowA i : ℝ)) y +
      evalQuad (range 130) (fun i j => (lowB i j : ℝ)) y) = _ at hDec
  have hn : 0 ≤ evalLinear (range 130) (fun i => (lowA i : ℝ)) y +
      evalQuad (range 130) (fun i j => (lowB i j : ℝ)) y := by
    apply nonneg_of_mul_nonneg_right _ (show (0:ℝ) < 5480 by norm_num)
    rw [hDec]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num) hMatrix) hLin) hYY) hYO) hMass
  exact nonneg_of_mul_nonneg_right (hn.trans (weighted_objective_le y)) (by norm_num [lowD])

end OMA.Erdos1186Low

end

namespace OMA.Erdos1186Low

/-- All entries of the Boolean checker in a half-open interval. -/
private def RowsOK (check : Nat → Bool) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → check i = true

private theorem oneRow {check : Nat → Bool} {lo : Nat} (h : check lo = true) :
    RowsOK check lo (lo+1) := by
  intro i hlo hhi
  have e : i = lo := by omega
  simpa only [e] using h

private theorem joinRows {check : Nat → Bool} {a b c : Nat}
    (left : RowsOK check a b) (right : RowsOK check b c) : RowsOK check a c := by
  intro i ha hc
  by_cases hb : i < b
  · exact left i ha hb
  · exact right i (Nat.le_of_not_gt hb) hc

set_option maxRecDepth 10000 in
private theorem dLow0 : lowDominanceCheck 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow1 : lowDominanceCheck 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow2 : lowDominanceCheck 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow3 : lowDominanceCheck 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow4 : lowDominanceCheck 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow5 : lowDominanceCheck 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow6 : lowDominanceCheck 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow7 : lowDominanceCheck 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow8 : lowDominanceCheck 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow9 : lowDominanceCheck 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow10 : lowDominanceCheck 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow11 : lowDominanceCheck 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow12 : lowDominanceCheck 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow13 : lowDominanceCheck 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow14 : lowDominanceCheck 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow15 : lowDominanceCheck 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow16 : lowDominanceCheck 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow17 : lowDominanceCheck 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow18 : lowDominanceCheck 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow19 : lowDominanceCheck 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow20 : lowDominanceCheck 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow21 : lowDominanceCheck 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow22 : lowDominanceCheck 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow23 : lowDominanceCheck 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow24 : lowDominanceCheck 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow25 : lowDominanceCheck 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow26 : lowDominanceCheck 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow27 : lowDominanceCheck 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow28 : lowDominanceCheck 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow29 : lowDominanceCheck 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow30 : lowDominanceCheck 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow31 : lowDominanceCheck 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow32 : lowDominanceCheck 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow33 : lowDominanceCheck 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow34 : lowDominanceCheck 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow35 : lowDominanceCheck 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow36 : lowDominanceCheck 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow37 : lowDominanceCheck 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow38 : lowDominanceCheck 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow39 : lowDominanceCheck 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow40 : lowDominanceCheck 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow41 : lowDominanceCheck 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow42 : lowDominanceCheck 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow43 : lowDominanceCheck 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow44 : lowDominanceCheck 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow45 : lowDominanceCheck 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow46 : lowDominanceCheck 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow47 : lowDominanceCheck 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow48 : lowDominanceCheck 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow49 : lowDominanceCheck 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow50 : lowDominanceCheck 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow51 : lowDominanceCheck 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow52 : lowDominanceCheck 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow53 : lowDominanceCheck 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow54 : lowDominanceCheck 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow55 : lowDominanceCheck 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow56 : lowDominanceCheck 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow57 : lowDominanceCheck 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow58 : lowDominanceCheck 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow59 : lowDominanceCheck 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow60 : lowDominanceCheck 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow61 : lowDominanceCheck 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow62 : lowDominanceCheck 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow63 : lowDominanceCheck 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow64 : lowDominanceCheck 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow65 : lowDominanceCheck 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow66 : lowDominanceCheck 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow67 : lowDominanceCheck 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow68 : lowDominanceCheck 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow69 : lowDominanceCheck 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow70 : lowDominanceCheck 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow71 : lowDominanceCheck 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow72 : lowDominanceCheck 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow73 : lowDominanceCheck 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow74 : lowDominanceCheck 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow75 : lowDominanceCheck 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow76 : lowDominanceCheck 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow77 : lowDominanceCheck 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow78 : lowDominanceCheck 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow79 : lowDominanceCheck 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow80 : lowDominanceCheck 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow81 : lowDominanceCheck 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow82 : lowDominanceCheck 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow83 : lowDominanceCheck 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow84 : lowDominanceCheck 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow85 : lowDominanceCheck 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow86 : lowDominanceCheck 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow87 : lowDominanceCheck 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow88 : lowDominanceCheck 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow89 : lowDominanceCheck 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow90 : lowDominanceCheck 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow91 : lowDominanceCheck 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow92 : lowDominanceCheck 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow93 : lowDominanceCheck 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow94 : lowDominanceCheck 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow95 : lowDominanceCheck 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow96 : lowDominanceCheck 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow97 : lowDominanceCheck 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow98 : lowDominanceCheck 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow99 : lowDominanceCheck 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow100 : lowDominanceCheck 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow101 : lowDominanceCheck 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow102 : lowDominanceCheck 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow103 : lowDominanceCheck 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow104 : lowDominanceCheck 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow105 : lowDominanceCheck 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow106 : lowDominanceCheck 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow107 : lowDominanceCheck 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow108 : lowDominanceCheck 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow109 : lowDominanceCheck 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow110 : lowDominanceCheck 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow111 : lowDominanceCheck 111 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow112 : lowDominanceCheck 112 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow113 : lowDominanceCheck 113 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow114 : lowDominanceCheck 114 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow115 : lowDominanceCheck 115 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow116 : lowDominanceCheck 116 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow117 : lowDominanceCheck 117 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow118 : lowDominanceCheck 118 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow119 : lowDominanceCheck 119 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow120 : lowDominanceCheck 120 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow121 : lowDominanceCheck 121 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow122 : lowDominanceCheck 122 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow123 : lowDominanceCheck 123 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow124 : lowDominanceCheck 124 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow125 : lowDominanceCheck 125 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow126 : lowDominanceCheck 126 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow127 : lowDominanceCheck 127 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow128 : lowDominanceCheck 128 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem dLow129 : lowDominanceCheck 129 = true := by decide +kernel

private theorem dominanceRows : RowsOK lowDominanceCheck 0 130 :=
  joinRows (joinRows (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow dLow0) (oneRow dLow1)) (joinRows (oneRow dLow2) (oneRow dLow3))) (joinRows (joinRows (oneRow dLow4) (oneRow dLow5)) (joinRows (oneRow dLow6) (oneRow dLow7)))) (joinRows (joinRows (joinRows (oneRow dLow8) (oneRow dLow9)) (joinRows (oneRow dLow10) (oneRow dLow11))) (joinRows (joinRows (oneRow dLow12) (oneRow dLow13)) (joinRows (oneRow dLow14) (oneRow dLow15))))) (joinRows (joinRows (joinRows (joinRows (oneRow dLow16) (oneRow dLow17)) (joinRows (oneRow dLow18) (oneRow dLow19))) (joinRows (joinRows (oneRow dLow20) (oneRow dLow21)) (joinRows (oneRow dLow22) (oneRow dLow23)))) (joinRows (joinRows (joinRows (oneRow dLow24) (oneRow dLow25)) (joinRows (oneRow dLow26) (oneRow dLow27))) (joinRows (joinRows (oneRow dLow28) (oneRow dLow29)) (joinRows (oneRow dLow30) (oneRow dLow31)))))) (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow dLow32) (oneRow dLow33)) (joinRows (oneRow dLow34) (oneRow dLow35))) (joinRows (joinRows (oneRow dLow36) (oneRow dLow37)) (joinRows (oneRow dLow38) (oneRow dLow39)))) (joinRows (joinRows (joinRows (oneRow dLow40) (oneRow dLow41)) (joinRows (oneRow dLow42) (oneRow dLow43))) (joinRows (joinRows (oneRow dLow44) (oneRow dLow45)) (joinRows (oneRow dLow46) (oneRow dLow47))))) (joinRows (joinRows (joinRows (joinRows (oneRow dLow48) (oneRow dLow49)) (joinRows (oneRow dLow50) (oneRow dLow51))) (joinRows (joinRows (oneRow dLow52) (oneRow dLow53)) (joinRows (oneRow dLow54) (oneRow dLow55)))) (joinRows (joinRows (joinRows (oneRow dLow56) (oneRow dLow57)) (joinRows (oneRow dLow58) (oneRow dLow59))) (joinRows (joinRows (oneRow dLow60) (oneRow dLow61)) (joinRows (oneRow dLow62) (joinRows (oneRow dLow63) (oneRow dLow64)))))))) (joinRows (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow dLow65) (oneRow dLow66)) (joinRows (oneRow dLow67) (oneRow dLow68))) (joinRows (joinRows (oneRow dLow69) (oneRow dLow70)) (joinRows (oneRow dLow71) (oneRow dLow72)))) (joinRows (joinRows (joinRows (oneRow dLow73) (oneRow dLow74)) (joinRows (oneRow dLow75) (oneRow dLow76))) (joinRows (joinRows (oneRow dLow77) (oneRow dLow78)) (joinRows (oneRow dLow79) (oneRow dLow80))))) (joinRows (joinRows (joinRows (joinRows (oneRow dLow81) (oneRow dLow82)) (joinRows (oneRow dLow83) (oneRow dLow84))) (joinRows (joinRows (oneRow dLow85) (oneRow dLow86)) (joinRows (oneRow dLow87) (oneRow dLow88)))) (joinRows (joinRows (joinRows (oneRow dLow89) (oneRow dLow90)) (joinRows (oneRow dLow91) (oneRow dLow92))) (joinRows (joinRows (oneRow dLow93) (oneRow dLow94)) (joinRows (oneRow dLow95) (oneRow dLow96)))))) (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow dLow97) (oneRow dLow98)) (joinRows (oneRow dLow99) (oneRow dLow100))) (joinRows (joinRows (oneRow dLow101) (oneRow dLow102)) (joinRows (oneRow dLow103) (oneRow dLow104)))) (joinRows (joinRows (joinRows (oneRow dLow105) (oneRow dLow106)) (joinRows (oneRow dLow107) (oneRow dLow108))) (joinRows (joinRows (oneRow dLow109) (oneRow dLow110)) (joinRows (oneRow dLow111) (oneRow dLow112))))) (joinRows (joinRows (joinRows (joinRows (oneRow dLow113) (oneRow dLow114)) (joinRows (oneRow dLow115) (oneRow dLow116))) (joinRows (joinRows (oneRow dLow117) (oneRow dLow118)) (joinRows (oneRow dLow119) (oneRow dLow120)))) (joinRows (joinRows (joinRows (oneRow dLow121) (oneRow dLow122)) (joinRows (oneRow dLow123) (oneRow dLow124))) (joinRows (joinRows (oneRow dLow125) (oneRow dLow126)) (joinRows (oneRow dLow127) (joinRows (oneRow dLow128) (oneRow dLow129))))))))

theorem low_dominance_all (i : Nat) (hi : i < 130) : lowDominanceCheck i = true :=
  dominanceRows i (Nat.zero_le _) hi

set_option maxRecDepth 10000 in
private theorem bLow0 : budgetCheck 0 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow1 : budgetCheck 1 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow2 : budgetCheck 2 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow3 : budgetCheck 3 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow4 : budgetCheck 4 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow5 : budgetCheck 5 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow6 : budgetCheck 6 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow7 : budgetCheck 7 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow8 : budgetCheck 8 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow9 : budgetCheck 9 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow10 : budgetCheck 10 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow11 : budgetCheck 11 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow12 : budgetCheck 12 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow13 : budgetCheck 13 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow14 : budgetCheck 14 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow15 : budgetCheck 15 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow16 : budgetCheck 16 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow17 : budgetCheck 17 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow18 : budgetCheck 18 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow19 : budgetCheck 19 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow20 : budgetCheck 20 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow21 : budgetCheck 21 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow22 : budgetCheck 22 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow23 : budgetCheck 23 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow24 : budgetCheck 24 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow25 : budgetCheck 25 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow26 : budgetCheck 26 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow27 : budgetCheck 27 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow28 : budgetCheck 28 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow29 : budgetCheck 29 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow30 : budgetCheck 30 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow31 : budgetCheck 31 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow32 : budgetCheck 32 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow33 : budgetCheck 33 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow34 : budgetCheck 34 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow35 : budgetCheck 35 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow36 : budgetCheck 36 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow37 : budgetCheck 37 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow38 : budgetCheck 38 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow39 : budgetCheck 39 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow40 : budgetCheck 40 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow41 : budgetCheck 41 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow42 : budgetCheck 42 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow43 : budgetCheck 43 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow44 : budgetCheck 44 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow45 : budgetCheck 45 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow46 : budgetCheck 46 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow47 : budgetCheck 47 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow48 : budgetCheck 48 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow49 : budgetCheck 49 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow50 : budgetCheck 50 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow51 : budgetCheck 51 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow52 : budgetCheck 52 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow53 : budgetCheck 53 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow54 : budgetCheck 54 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow55 : budgetCheck 55 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow56 : budgetCheck 56 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow57 : budgetCheck 57 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow58 : budgetCheck 58 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow59 : budgetCheck 59 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow60 : budgetCheck 60 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow61 : budgetCheck 61 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow62 : budgetCheck 62 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow63 : budgetCheck 63 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow64 : budgetCheck 64 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow65 : budgetCheck 65 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow66 : budgetCheck 66 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow67 : budgetCheck 67 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow68 : budgetCheck 68 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow69 : budgetCheck 69 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow70 : budgetCheck 70 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow71 : budgetCheck 71 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow72 : budgetCheck 72 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow73 : budgetCheck 73 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow74 : budgetCheck 74 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow75 : budgetCheck 75 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow76 : budgetCheck 76 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow77 : budgetCheck 77 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow78 : budgetCheck 78 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow79 : budgetCheck 79 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow80 : budgetCheck 80 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow81 : budgetCheck 81 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow82 : budgetCheck 82 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow83 : budgetCheck 83 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow84 : budgetCheck 84 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow85 : budgetCheck 85 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow86 : budgetCheck 86 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow87 : budgetCheck 87 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow88 : budgetCheck 88 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow89 : budgetCheck 89 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow90 : budgetCheck 90 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow91 : budgetCheck 91 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow92 : budgetCheck 92 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow93 : budgetCheck 93 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow94 : budgetCheck 94 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow95 : budgetCheck 95 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow96 : budgetCheck 96 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow97 : budgetCheck 97 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow98 : budgetCheck 98 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow99 : budgetCheck 99 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow100 : budgetCheck 100 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow101 : budgetCheck 101 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow102 : budgetCheck 102 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow103 : budgetCheck 103 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow104 : budgetCheck 104 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow105 : budgetCheck 105 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow106 : budgetCheck 106 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow107 : budgetCheck 107 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow108 : budgetCheck 108 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow109 : budgetCheck 109 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow110 : budgetCheck 110 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow111 : budgetCheck 111 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow112 : budgetCheck 112 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow113 : budgetCheck 113 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow114 : budgetCheck 114 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow115 : budgetCheck 115 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow116 : budgetCheck 116 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow117 : budgetCheck 117 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow118 : budgetCheck 118 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow119 : budgetCheck 119 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow120 : budgetCheck 120 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow121 : budgetCheck 121 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow122 : budgetCheck 122 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow123 : budgetCheck 123 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow124 : budgetCheck 124 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow125 : budgetCheck 125 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow126 : budgetCheck 126 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow127 : budgetCheck 127 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow128 : budgetCheck 128 = true := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bLow129 : budgetCheck 129 = true := by decide +kernel

private theorem budgetRows : RowsOK budgetCheck 0 130 :=
  joinRows (joinRows (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow bLow0) (oneRow bLow1)) (joinRows (oneRow bLow2) (oneRow bLow3))) (joinRows (joinRows (oneRow bLow4) (oneRow bLow5)) (joinRows (oneRow bLow6) (oneRow bLow7)))) (joinRows (joinRows (joinRows (oneRow bLow8) (oneRow bLow9)) (joinRows (oneRow bLow10) (oneRow bLow11))) (joinRows (joinRows (oneRow bLow12) (oneRow bLow13)) (joinRows (oneRow bLow14) (oneRow bLow15))))) (joinRows (joinRows (joinRows (joinRows (oneRow bLow16) (oneRow bLow17)) (joinRows (oneRow bLow18) (oneRow bLow19))) (joinRows (joinRows (oneRow bLow20) (oneRow bLow21)) (joinRows (oneRow bLow22) (oneRow bLow23)))) (joinRows (joinRows (joinRows (oneRow bLow24) (oneRow bLow25)) (joinRows (oneRow bLow26) (oneRow bLow27))) (joinRows (joinRows (oneRow bLow28) (oneRow bLow29)) (joinRows (oneRow bLow30) (oneRow bLow31)))))) (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow bLow32) (oneRow bLow33)) (joinRows (oneRow bLow34) (oneRow bLow35))) (joinRows (joinRows (oneRow bLow36) (oneRow bLow37)) (joinRows (oneRow bLow38) (oneRow bLow39)))) (joinRows (joinRows (joinRows (oneRow bLow40) (oneRow bLow41)) (joinRows (oneRow bLow42) (oneRow bLow43))) (joinRows (joinRows (oneRow bLow44) (oneRow bLow45)) (joinRows (oneRow bLow46) (oneRow bLow47))))) (joinRows (joinRows (joinRows (joinRows (oneRow bLow48) (oneRow bLow49)) (joinRows (oneRow bLow50) (oneRow bLow51))) (joinRows (joinRows (oneRow bLow52) (oneRow bLow53)) (joinRows (oneRow bLow54) (oneRow bLow55)))) (joinRows (joinRows (joinRows (oneRow bLow56) (oneRow bLow57)) (joinRows (oneRow bLow58) (oneRow bLow59))) (joinRows (joinRows (oneRow bLow60) (oneRow bLow61)) (joinRows (oneRow bLow62) (joinRows (oneRow bLow63) (oneRow bLow64)))))))) (joinRows (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow bLow65) (oneRow bLow66)) (joinRows (oneRow bLow67) (oneRow bLow68))) (joinRows (joinRows (oneRow bLow69) (oneRow bLow70)) (joinRows (oneRow bLow71) (oneRow bLow72)))) (joinRows (joinRows (joinRows (oneRow bLow73) (oneRow bLow74)) (joinRows (oneRow bLow75) (oneRow bLow76))) (joinRows (joinRows (oneRow bLow77) (oneRow bLow78)) (joinRows (oneRow bLow79) (oneRow bLow80))))) (joinRows (joinRows (joinRows (joinRows (oneRow bLow81) (oneRow bLow82)) (joinRows (oneRow bLow83) (oneRow bLow84))) (joinRows (joinRows (oneRow bLow85) (oneRow bLow86)) (joinRows (oneRow bLow87) (oneRow bLow88)))) (joinRows (joinRows (joinRows (oneRow bLow89) (oneRow bLow90)) (joinRows (oneRow bLow91) (oneRow bLow92))) (joinRows (joinRows (oneRow bLow93) (oneRow bLow94)) (joinRows (oneRow bLow95) (oneRow bLow96)))))) (joinRows (joinRows (joinRows (joinRows (joinRows (oneRow bLow97) (oneRow bLow98)) (joinRows (oneRow bLow99) (oneRow bLow100))) (joinRows (joinRows (oneRow bLow101) (oneRow bLow102)) (joinRows (oneRow bLow103) (oneRow bLow104)))) (joinRows (joinRows (joinRows (oneRow bLow105) (oneRow bLow106)) (joinRows (oneRow bLow107) (oneRow bLow108))) (joinRows (joinRows (oneRow bLow109) (oneRow bLow110)) (joinRows (oneRow bLow111) (oneRow bLow112))))) (joinRows (joinRows (joinRows (joinRows (oneRow bLow113) (oneRow bLow114)) (joinRows (oneRow bLow115) (oneRow bLow116))) (joinRows (joinRows (oneRow bLow117) (oneRow bLow118)) (joinRows (oneRow bLow119) (oneRow bLow120)))) (joinRows (joinRows (joinRows (oneRow bLow121) (oneRow bLow122)) (joinRows (oneRow bLow123) (oneRow bLow124))) (joinRows (joinRows (oneRow bLow125) (oneRow bLow126)) (joinRows (oneRow bLow127) (joinRows (oneRow bLow128) (oneRow bLow129))))))))

theorem low_budget_all (i : Nat) (hi : i < 130) : budgetCheck i = true :=
  budgetRows i (Nat.zero_le _) hi

theorem g24_low_box (y : ℕ → ℝ) (hy : ∀ i < 130, 0 ≤ y i ∧ y i ≤ 1)
    (hm0 : 0 ≤ OMA.Erdos1186Region2.g24Mass y)
    (hm1 : OMA.Erdos1186Region2.g24Mass y ≤ (1/5 : ℝ)) :
    0 ≤ OMA.Erdos1186Region2.g24Objective y :=
  low_box_of_checks low_dominance_all low_budget_all y hy hm0 hm1

end OMA.Erdos1186Low

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1.H1 :=
  OMA.Erdos1186G24NearCut.low_cut_of_box OMA.Erdos1186Low.g24_low_box
