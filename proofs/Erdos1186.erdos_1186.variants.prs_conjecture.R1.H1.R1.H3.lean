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
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! # Erdős 1186: the high-mass G24 certificate and its discrete transfer -/

/- Discrete G24 transfer for the upper density interval of Erdős 1186. -/

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

/-  Correctness of the corner shortcuts in the exact G24 area calculation. -/

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

/-  Extract the finite G24 bathtub inputs into inequalities on unit blocks. -/

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

/-  Rescale the checked G24 cell bound to the coefficients in the finite objective. -/

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

/-  The audited integer prefix function equals the sum of PRS unit signs. -/

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

/-  The exact G24 bathtub estimate for the actual PRS signed window energy. -/

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

/-  Boundary cells in the discrete-to-continuum comparison for Erdős 1186. -/

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

/-  The grid quarter-area kernel differs from the discrete strip only at boundary offsets. -/

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

/-  Exact quarter-area sums under subdivision of a grid cell. -/

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

/-  Exact area sums for coarse rectangles and their fine grid subdivisions. -/

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

/-  Comparing a refined rectangle's strip count with its quarter-area sum. -/
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

/-  Bounds on a selected part of one grid-cell pair. -/

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

/-  A lower bound on a signed cut in one pair of cells. -/
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

/-  The mass of grid-cell densities is the normalized discrete mass. -/

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

/-  Identify the checked G24 area and mass with the grid counts. -/
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

/-  The signed cut weight is minus half the change in the pair correlation. -/

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

/-  Identify the exact published signed cut with the expanded G24 energy. -/

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

/-  Assemble the signed-rectangle and linear-profile estimates. -/

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

/-  Checked discrete transfer of the signed cut to the explicit G24 objective. -/

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

/-- Transfer a high-mass G24 box estimate to the exact discrete near-cut target. -/
theorem high_cut_of_box
    (box : ∀ y : ℕ → ℝ, (∀ i < 130, 0 ≤ y i ∧ y i ≤ 1) →
      (3/10 : ℝ) ≤ g24Mass y → g24Mass y ≤ (2/5 : ℝ) → 0 ≤ g24Objective y) :
    OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1.H3 := by
  refine ⟨110680, by norm_num, ?_⟩
  intro w hw d
  dsimp only
  intro hlo hhi
  let n := 1096*w
  let t := ((Icc 1 n).filter (fun x => d x = true)).card
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 1096) (show 0 < w from hw)
  have hloReal : 3 * (n : ℝ) ≤ 10 * (t : ℝ) := by exact_mod_cast hlo
  have hhiReal : 5 * (t : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hhi
  have hMass := density_mass w hw d
  have hMassLower : (3/10 : ℝ) ≤ g24Mass (density w d) := by
    rw [hMass]
    exact (le_div_iff₀ hn).2 (by linarith only [hloReal])
  have hMassUpper : g24Mass (density w d) ≤ (2/5 : ℝ) := by
    rw [hMass]
    exact (div_le_iff₀ hn).2 (by linarith only [hhiReal])
  have hObj := box (density w d) (fun _ hi => density_bounds w d hw hi) hMassLower hMassUpper
  have hTerm : 0 ≤ 2 * (n : ℝ)^2 * g24Objective (density w d) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hObj
  change (signedCutWeight w d : ℝ) ≤ 110680 * (n : ℝ)
  exact (le_add_of_nonneg_right hTerm).trans (transfer w hw d)

end OMA.Erdos1186G24NearCut

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

/-
Copyright 2026 Chandler Snively.
Released under the Apache License, Version 2.0. See LICENSE-Apache-2.0
and UPSTREAM-NOTICE in this audit directory.

Adapted from dreadpiratechan/erdos-1186 v1.0.0,
commit 0b0155ead09841892690b9f9c469d1ff0edaff4c.
Sources: lean/Erdos/Proofs/P1186ExCertLib.lean and P1186ExCertAlg.lean.
The underlying certificate argument is due to Carlos Toledo.
The general polynomial and affine-form declarations are extracted into a
separate namespace with narrower dependencies.
-/

namespace OMA.Erdos1186SnivelyForms

open Finset
open scoped BigOperators


/- ### Quadratic polynomials in `n` variables with integer coefficients -/

/-- `c0 + Σ l_i y_i + Σ_{ij} q_ij y_i y_j`. -/
noncomputable def evq (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) : ℝ :=
  (c0 : ℝ) + ∑ i ∈ range n, (l i : ℝ) * y i + ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)

theorem evq_add (n : ℕ) (c0 c0' : ℤ) (l l' : ℕ → ℤ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (c0 + c0') (fun i => l i + l' i) (fun i j => q i j + q' i j) y
      = evq n c0 l q y + evq n c0' l' q' y := by
  unfold evq
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem evq_neg (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (-c0) (fun i => -l i) (fun i j => -q i j) y = -evq n c0 l q y := by
  unfold evq
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem evq_smul (n : ℕ) (u c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    (u : ℝ) * evq n c0 l q y = evq n (u * c0) (fun i => u * l i) (fun i j => u * q i j) y := by
  unfold evq
  have h1 : (u : ℝ) * ∑ i ∈ range n, (l i : ℝ) * y i = ∑ i ∈ range n, ((u * l i : ℤ) : ℝ) * y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : (u : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, ((u * q i j : ℤ) : ℝ) * (y i * y j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [mul_add, mul_add, h1, h2]
  push_cast
  ring

/-- The quadratic part only sees `q i j + q j i`. -/
theorem sum_sym (n : ℕ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ)
    (hq : ∀ i < n, ∀ j < n, q i j + q j i = q' i j + q' j i) :
    ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q' i j : ℝ) * (y i * y j) := by
  have e1 : ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q j i : ℝ) * (y i * y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, (q' i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q' j i : ℝ) * (y i * y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e3 : ∑ i ∈ range n, ∑ j ∈ range n, ((q i j : ℝ) + (q j i : ℝ)) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, ((q' i j : ℝ) + (q' j i : ℝ)) * (y i * y j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have := hq i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
    have : ((q i j : ℝ) + (q j i : ℝ)) = ((q' i j : ℝ) + (q' j i : ℝ)) := by exact_mod_cast this
    rw [this]
  simp only [add_mul, Finset.sum_add_distrib] at e3
  linarith

theorem evq_congr (n : ℕ) (c0 c0' : ℤ) (l l' : ℕ → ℤ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ)
    (h0 : c0 = c0') (hl : ∀ i < n, l i = l' i) (hq : ∀ i < n, ∀ j < n, q i j + q j i = q' i j + q' j i) :
    evq n c0 l q y = evq n c0' l' q' y := by
  unfold evq
  rw [h0, sum_sym n q q' y hq]
  have : ∑ i ∈ range n, (l i : ℝ) * y i = ∑ i ∈ range n, (l' i : ℝ) * y i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hl i (Finset.mem_range.mp hi)]
  rw [this]

/- ### Affine functions and the double-sum expansion -/

/-- `c + Σ_k e_k y_k`. -/
noncomputable def afn (n : ℕ) (c : ℤ) (e : ℕ → ℤ) (y : ℕ → ℝ) : ℝ := (c : ℝ) + ∑ k ∈ range n, (e k : ℝ) * y k

theorem afn_mul (n : ℕ) (c d : ℤ) (e f : ℕ → ℤ) (y : ℕ → ℝ) :
    afn n c e y * afn n d f y = evq n (c * d) (fun i => c * f i + d * e i) (fun i j => e i * f j) y := by
  unfold afn evq
  have h1 : ∑ i ∈ range n, (((c * f i + d * e i : ℤ) : ℝ)) * y i
      = (c : ℝ) * ∑ i ∈ range n, (f i : ℝ) * y i + (d : ℝ) * ∑ i ∈ range n, (e i : ℝ) * y i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : (∑ i ∈ range n, (e i : ℝ) * y i) * ∑ j ∈ range n, (f j : ℝ) * y j
      = ∑ i ∈ range n, ∑ j ∈ range n, ((e i * f j : ℤ) : ℝ) * (y i * y j) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [h1, ← h2]
  push_cast
  ring

theorem sum2_aff (n : ℕ) (u t u' t' : ℤ) (C : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (C i j : ℝ) * (((u : ℝ) + t * y i) * ((u' : ℝ) + t' * y j))
      = evq n (u * u' * ∑ i ∈ range n, ∑ j ∈ range n, C i j)
          (fun a => u * t' * (∑ i ∈ range n, C i a) + t * u' * (∑ j ∈ range n, C a j))
          (fun i j => t * t' * C i j) y := by
  unfold evq
  have key : ∀ i j, (C i j : ℝ) * (((u : ℝ) + t * y i) * ((u' : ℝ) + t' * y j))
      = ((u * u' : ℤ) : ℝ) * (C i j : ℝ) + ((u * t' : ℤ) : ℝ) * (C i j : ℝ) * y j
        + ((t * u' : ℤ) : ℝ) * (C i j : ℝ) * y i + ((t * t' * C i j : ℤ) : ℝ) * (y i * y j) := by
    intro i j
    push_cast
    ring
  simp only [key, Finset.sum_add_distrib]
  have e1 : ∑ i ∈ range n, ∑ j ∈ range n, ((u * u' : ℤ) : ℝ) * (C i j : ℝ)
      = ((u * u' * ∑ i ∈ range n, ∑ j ∈ range n, C i j : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, ((u * t' : ℤ) : ℝ) * (C i j : ℝ) * y j
      = ∑ a ∈ range n, ((u * t' * ∑ i ∈ range n, C i a : ℤ) : ℝ) * y a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  have e3 : ∑ i ∈ range n, ∑ j ∈ range n, ((t * u' : ℤ) : ℝ) * (C i j : ℝ) * y i
      = ∑ a ∈ range n, ((t * u' * ∑ j ∈ range n, C a j : ℤ) : ℝ) * y a := by
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [e1, e2, e3]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/- ### The form side -/

/-- The form tables (already multiplied by the common factor), and the integer data of `R·m`, `R·lo`, `R·hi`. -/
structure FD where
  n : ℕ
  Yv : ℕ → ℤ
  Ov : ℕ → ℤ
  A1 : ℕ → ℤ
  A2 : ℕ → ℤ
  A3 : ℕ → ℤ
  A4 : ℕ → ℤ
  YY : ℕ → ℕ → ℤ
  OO : ℕ → ℕ → ℤ
  YO : ℕ → ℕ → ℤ
  pp : ℤ
  rr : ℤ
  ss : ℤ
  om : ℕ → ℤ
  Lo : ℤ
  Hi : ℤ

/-- `R = 20 · 1096`, `U = R²`. -/
def Rr : ℤ := 21920
def Uu : ℤ := 21920 * 21920

namespace FD

/-- The nonnegative combination of atom products (atoms `y_i`, `1 - y_i`, `m - lo`, `hi - m`). -/
noncomputable def FSr (d : FD) (m lo hi : ℝ) (y : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i)))
  + ((d.pp : ℝ) * (m - lo) + (d.rr : ℝ) * (hi - m))
  + ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
      + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
  + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
      + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m)))
  + (d.ss : ℝ) * ((m - lo) * (hi - m))

/-- all multipliers are `≥ 0`. -/
structure Nonneg (d : FD) : Prop where
  Yv : ∀ i < d.n, 0 ≤ d.Yv i
  Ov : ∀ i < d.n, 0 ≤ d.Ov i
  A1 : ∀ i < d.n, 0 ≤ d.A1 i
  A2 : ∀ i < d.n, 0 ≤ d.A2 i
  A3 : ∀ i < d.n, 0 ≤ d.A3 i
  A4 : ∀ i < d.n, 0 ≤ d.A4 i
  YY : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.YY i j
  OO : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.OO i j
  YO : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.YO i j
  pp : 0 ≤ d.pp
  rr : 0 ≤ d.rr
  ss : 0 ≤ d.ss

theorem FSr_nonneg (d : FD) (h : d.Nonneg) (m lo hi : ℝ) (y : ℕ → ℝ) (hy : ∀ i < d.n, 0 ≤ y i ∧ y i ≤ 1)
    (hl : lo ≤ m) (hh : m ≤ hi) : 0 ≤ d.FSr m lo hi y := by
  have ml : 0 ≤ m - lo := by linarith
  have hm : 0 ≤ hi - m := by linarith
  have c : ∀ z : ℤ, 0 ≤ z → (0 : ℝ) ≤ (z : ℝ) := fun z hz => by exact_mod_cast hz
  unfold FSr
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_nonneg fun i hi' => ?_
    have hi'' := Finset.mem_range.mp hi'
    obtain ⟨h0, h1⟩ := hy i hi''
    exact add_nonneg (mul_nonneg (c _ (h.Yv i hi'')) h0) (mul_nonneg (c _ (h.Ov i hi'')) (by linarith))
  · exact add_nonneg (mul_nonneg (c _ h.pp) ml) (mul_nonneg (c _ h.rr) hm)
  · refine Finset.sum_nonneg fun i hi' => Finset.sum_nonneg fun j hj' => ?_
    have hi'' := Finset.mem_range.mp hi'
    have hj'' := Finset.mem_range.mp hj'
    obtain ⟨a0, a1⟩ := hy i hi''
    obtain ⟨b0, b1⟩ := hy j hj''
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg (c _ (h.YY i hi'' j hj'')) (mul_nonneg a0 b0)
    · exact mul_nonneg (c _ (h.OO i hi'' j hj'')) (mul_nonneg (by linarith) (by linarith))
    · exact mul_nonneg (c _ (h.YO i hi'' j hj'')) (mul_nonneg a0 (by linarith))
  · refine Finset.sum_nonneg fun i hi' => ?_
    have hi'' := Finset.mem_range.mp hi'
    obtain ⟨a0, a1⟩ := hy i hi''
    refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
    · exact mul_nonneg (c _ (h.A1 i hi'')) (mul_nonneg a0 ml)
    · exact mul_nonneg (c _ (h.A2 i hi'')) (mul_nonneg (by linarith) ml)
    · exact mul_nonneg (c _ (h.A3 i hi'')) (mul_nonneg a0 hm)
    · exact mul_nonneg (c _ (h.A4 i hi'')) (mul_nonneg (by linarith) hm)
  · exact mul_nonneg (c _ h.ss) (mul_nonneg ml hm)

/- #### The integer coefficients of `U · FSr` -/

def u1 (d : FD) (i : ℕ) : ℤ := d.A1 i - d.A2 i
def u2 (d : FD) (i : ℕ) : ℤ := d.A3 i - d.A4 i
def u10 (d : FD) : ℤ := (∑ i ∈ range d.n, d.A2 i) + d.pp
def u20 (d : FD) : ℤ := (∑ i ∈ range d.n, d.A4 i) + d.rr

def cF (d : FD) : ℤ :=
  Uu * ((∑ i ∈ range d.n, d.Ov i) + ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.OO i j)
    + Rr * (-d.Lo * d.u10 + d.Hi * d.u20) - d.ss * d.Lo * d.Hi

def lF (d : FD) (a : ℕ) : ℤ :=
  Uu * (d.Yv a - d.Ov a - (∑ j ∈ range d.n, d.OO a j) - (∑ i ∈ range d.n, d.OO i a) + ∑ j ∈ range d.n, d.YO a j)
    + Rr * (d.om a * d.u10 - d.Lo * d.u1 a - d.om a * d.u20 + d.Hi * d.u2 a)
    + d.ss * d.om a * (d.Lo + d.Hi)

def qF (d : FD) (i j : ℕ) : ℤ :=
  Uu * (d.YY i j + d.OO i j - d.YO i j) + Rr * d.om j * (d.u1 i - d.u2 i) - d.ss * d.om i * d.om j

theorem evq_zero (n : ℕ) (y : ℕ → ℝ) : evq n 0 (fun _ => 0) (fun _ _ => 0) y = 0 := by
  simp [evq]

theorem evq_afn (n : ℕ) (c : ℤ) (e : ℕ → ℤ) (y : ℕ → ℝ) :
    afn n c e y = evq n c e (fun _ _ => 0) y := by
  simp [afn, evq]

/-- `U · FSr = evq cF lF qF`, where `R m = Σ om y`, `R lo = Lo`, `R hi = Hi`. -/
theorem FSr_evq (d : FD) (m lo hi : ℝ) (y : ℕ → ℝ)
    (hm : (Rr : ℝ) * m = ∑ k ∈ range d.n, (d.om k : ℝ) * y k)
    (hlo : (Rr : ℝ) * lo = d.Lo) (hhi : (Rr : ℝ) * hi = d.Hi) :
    (Uu : ℝ) * d.FSr m lo hi y = evq d.n d.cF d.lF d.qF y := by
  have hUR : (Uu : ℝ) = (Rr : ℝ) * (Rr : ℝ) := by norm_num [Uu, Rr]
  have hml : (Rr : ℝ) * (m - lo) = afn d.n (-d.Lo) d.om y := by
    unfold afn
    push_cast
    rw [mul_sub, hm, hlo]
    ring
  have hhm : (Rr : ℝ) * (hi - m) = afn d.n d.Hi (fun k => - d.om k) y := by
    unfold afn
    push_cast
    rw [mul_sub, hm, hhi]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  -- the four groups
  have g1 : ∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i))
      = evq d.n (∑ i ∈ range d.n, d.Ov i) (fun a => d.Yv a - d.Ov a) (fun _ _ => 0) y := by
    unfold evq
    simp only [Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ i, (d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i)
        = (d.Ov i : ℝ) + ((d.Yv i - d.Ov i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    rfl
  have hGml : afn d.n d.u10 d.u1 y
      = (d.pp : ℝ) + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)) := by
    unfold afn FD.u10 FD.u1
    have : ∀ i, (d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)
        = (d.A2 i : ℝ) + ((d.A1 i - d.A2 i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    ring
  have hGhm : afn d.n d.u20 d.u2 y
      = (d.rr : ℝ) + ∑ i ∈ range d.n, ((d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)) := by
    unfold afn FD.u20 FD.u2
    have : ∀ i, (d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)
        = (d.A4 i : ℝ) + ((d.A3 i - d.A4 i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    ring
  have g2 : (d.pp : ℝ) * (m - lo) + (d.rr : ℝ) * (hi - m)
      + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
        + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m)))
      = afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m) := by
    rw [hGml, hGhm]
    have e : ∀ i, (d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
        + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m))
        = ((d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)) * (m - lo)
          + ((d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)) * (hi - m) := by
      intro i
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have g3 : ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
      + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
      = evq d.n (0 * 0 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.YY i j)
          (fun a => 0 * 1 * (∑ i ∈ range d.n, d.YY i a) + 1 * 0 * (∑ j ∈ range d.n, d.YY a j))
          (fun i j => 1 * 1 * d.YY i j) y
        + evq d.n (1 * 1 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.OO i j)
          (fun a => 1 * (-1) * (∑ i ∈ range d.n, d.OO i a) + (-1) * 1 * (∑ j ∈ range d.n, d.OO a j))
          (fun i j => (-1) * (-1) * d.OO i j) y
        + evq d.n (0 * 1 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.YO i j)
          (fun a => 0 * (-1) * (∑ i ∈ range d.n, d.YO i a) + 1 * 1 * (∑ j ∈ range d.n, d.YO a j))
          (fun i j => 1 * (-1) * d.YO i j) y := by
    rw [← sum2_aff d.n 0 1 0 1 d.YY y, ← sum2_aff d.n 1 (-1) 1 (-1) d.OO y,
      ← sum2_aff d.n 0 1 1 (-1) d.YO y]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have g5 : (d.ss : ℝ) * ((m - lo) * (hi - m)) * (Uu : ℝ)
      = (d.ss : ℝ) * (afn d.n (-d.Lo) d.om y * afn d.n d.Hi (fun k => - d.om k) y) := by
    rw [← hml, ← hhm, hUR]
    ring
  -- assemble
  have hFS : d.FSr m lo hi y
      = ∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i))
        + ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
          + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
        + (afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m))
        + (d.ss : ℝ) * ((m - lo) * (hi - m)) := by
    rw [← g2]
    unfold FD.FSr
    ring
  have hG2 : (Uu : ℝ) * (afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m))
      = (Rr : ℝ) * (afn d.n d.u10 d.u1 y * afn d.n (-d.Lo) d.om y
          + afn d.n d.u20 d.u2 y * afn d.n d.Hi (fun k => - d.om k) y) := by
    rw [← hml, ← hhm, hUR]
    ring
  rw [hFS, mul_add, mul_add, mul_add, hG2, g1, g3, mul_comm (Uu : ℝ) ((d.ss : ℝ) * _), g5,
    afn_mul, afn_mul, afn_mul]
  simp only [mul_add, evq_smul, ← evq_add]
  apply evq_congr
  · unfold FD.cF FD.u10 FD.u20
    ring
  · intro a _
    unfold FD.lF FD.u10 FD.u20 FD.u1 FD.u2
    ring
  · intro i _ j _
    unfold FD.qF FD.u1 FD.u2
    ring

end FD

end OMA.Erdos1186SnivelyForms

end

section

/-
Algebraic bridges shared by the certificate's real quadratic objective and
its augmented integer matrix.
-/

namespace OMA.Erdos1186IntegerPSD

open Finset
open scoped BigOperators

def evalPolynomial (n : ℕ) (c : ℝ) (l : ℕ → ℝ) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) : ℝ :=
  c + (∑ i ∈ range n, l i * y i) + quadratic (range n) q y

theorem affine_product (n : ℕ) (a b : ℝ) (u v y : ℕ → ℝ) :
    (a + ∑ i ∈ range n, u i * y i) * (b + ∑ i ∈ range n, v i * y i) =
      evalPolynomial n (a*b) (fun i => a*v i + b*u i) (fun i j => u i*v j) y := by
  have linear : (∑ i ∈ range n, (a*v i + b*u i) * y i) =
      a * (∑ i ∈ range n, v i * y i) + b * (∑ i ∈ range n, u i * y i) := by
    simp only [add_mul, sum_add_distrib, mul_sum]
    apply congrArg₂ (· + ·)
    all_goals exact sum_congr rfl (fun i _ => by ring)
  have product : quadratic (range n) (fun i j => u i*v j) y =
      (∑ i ∈ range n, u i * y i) * (∑ j ∈ range n, v j * y j) := by
    unfold quadratic
    rw [sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    exact sum_congr rfl (fun j _ => by ring)
  rw [evalPolynomial, linear, product]
  ring

private theorem quadratic_symmetrization (n : ℕ) (A q : ℕ → ℕ → ℝ)
    (h : ∀ i < n, ∀ j < n, 2 * A i j = q i j + q j i) (y : ℕ → ℝ) :
    quadratic (range n) A y = quadratic (range n) q y := by
  apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
  have swap : (∑ i ∈ range n, ∑ j ∈ range n, q j i * y i * y j) =
      quadratic (range n) q y := by
    rw [sum_comm]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))
  calc
    _ = ∑ i ∈ range n, ∑ j ∈ range n, (q i j + q j i) * y i * y j := by
      simp only [quadratic, mul_sum]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [← h i (mem_range.mp hi) j (mem_range.mp hj)]
      ring
    _ = quadratic (range n) q y + quadratic (range n) q y := by
      simp_rw [add_mul, sum_add_distrib]
      rw [swap]
      rfl
    _ = _ := by ring

theorem augmented_matrix_polynomial (n : ℕ) (A : ℕ → ℕ → ℝ)
    (c : ℝ) (l : ℕ → ℝ) (q : ℕ → ℕ → ℝ)
    (hc : A 0 0 = c) (hl : ∀ i < n, A 0 (i+1) + A (i+1) 0 = l i)
    (hq : ∀ i < n, ∀ j < n, 2 * A (i+1) (j+1) = q i j + q j i) (y : ℕ → ℝ) :
    quadratic (range (n+1)) A (fun k => if k = 0 then 1 else y (k-1)) =
      evalPolynomial n c l q y := by
  have hsym := quadratic_symmetrization n (fun i j => A (i+1) (j+1)) q hq y
  have hlin : (∑ i ∈ range n, A 0 (i+1) * y i) + (∑ i ∈ range n, A (i+1) 0 * y i) =
      ∑ i ∈ range n, l i * y i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← add_mul, hl i (mem_range.mp hi)]
  unfold quadratic at hsym ⊢
  simp_rw [sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel, mul_one]
  rw [sum_add_distrib, hc, hsym, evalPolynomial]
  unfold quadratic
  rw [← hlin]
  ring

end OMA.Erdos1186IntegerPSD

end

section

/- Positive semidefiniteness from a triangular Gram factor and a certified residual. -/

namespace OMA.Erdos1186High

open Finset OMA.Erdos1186Low OMA.Erdos1186IntegerPSD
open scoped BigOperators

def rowDot : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a*b + rowDot as bs
  | _, _ => 0

private theorem rowDot_comm (u v : List ℤ) : rowDot u v = rowDot v u := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons a u ih => cases v <;> simp [rowDot, ih, mul_comm]

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

def gramResidual (E : ℕ → ℕ → ℤ) (C : List (List ℤ)) (i j : ℕ) : ℤ :=
  E i j + rowDot (C[i]?.getD []) (C[j]?.getD [])

def residualEntry (scale : ℤ) (diagonal : SignedRow) (offDiagonal : List SignedRow) (i j : ℕ) : ℤ :=
  if i = j then diagonal.entry i else lowerEntry scale offDiagonal i j

theorem residualEntry_symm (scale : ℤ) (diagonal : SignedRow) (offDiagonal : List SignedRow) (i j : ℕ) :
    residualEntry scale diagonal offDiagonal i j = residualEntry scale diagonal offDiagonal j i := by
  by_cases h : i = j
  · subst j
    rfl
  · rw [residualEntry, residualEntry, if_neg h, if_neg (Ne.symm h), lowerEntry_comm]

theorem gramResidual_symm (E : ℕ → ℕ → ℤ) (C : List (List ℤ))
    (hE : ∀ i j, E i j = E j i) (i j : ℕ) : gramResidual E C i j = gramResidual E C j i := by
  unfold gramResidual
  rw [hE i j, rowDot_comm]

def residualCheck (n : ℕ) (E : ℕ → ℕ → ℤ) (i : ℕ) : Bool :=
  decide ((((List.range n).map (fun j => (E i j).natAbs)).sum : ℤ) ≤ 2 * E i i)

theorem sum_map_range (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem gramResidual_nonneg (n : ℕ) (E : ℕ → ℕ → ℤ) (C : List (List ℤ))
    (hE : ∀ i j, E i j = E j i) (hC : ∀ row ∈ C, row.length ≤ n)
    (hCheck : ∀ i < n, residualCheck n E i = true) (x : ℕ → ℝ) :
    0 ≤ quadratic (range n) (fun i j => (gramResidual E C i j : ℝ)) x := by
  refine intQuadratic_nonneg (range n) (range n) 1 (by decide) (gramResidual E C)
    (fun a k => (C[a]?.getD [])[k]?.getD 0) (fun i _ j _ => gramResidual_symm E C hE i j) ?_ x
  intro i hi
  have hc : (C[i]?.getD []).length ≤ n := by
    cases hr : C[i]? with
    | none => simp
    | some r => exact hC r (List.mem_of_getElem? hr)
  have hR (j : ℕ) : intResidual (range n) 1 (gramResidual E C)
      (fun a k => (C[a]?.getD [])[k]?.getD 0) i j = E i j := by
    simp [intResidual, gramResidual, rowDot_eq_sum n _ _ hc]
  simp_rw [hR]
  have h := of_decide_eq_true (hCheck i (mem_range.mp hi))
  push_cast at h
  simpa only [List.map_map, Function.comp_apply, sum_map_range, Int.natCast_natAbs] using h

end OMA.Erdos1186High

end

section

/- The high-slab retained affine weights on the exact common integer scale. -/

namespace OMA.Erdos1186High

open Finset OMA.Erdos1186SnivelyForms
open scoped BigOperators

/-- The weights other than the reconstructed `y`, `yy` and `yo` and the triangles. -/
structure Retained where
  o : ℕ → ℤ
  oo : ℕ → ℕ → ℤ
  ml : ℤ
  hm : ℤ
  mhm : ℤ
  yhm : ℕ → ℤ
  ohm : ℕ → ℤ

def highWeightScale : ℤ := 360364800

def keptTable (n : ℕ) (L : ℕ → ℤ) (d : Retained) : FD where
  n := n
  Yv := fun _ => 0
  Ov := d.o
  A1 := fun _ => 0
  A2 := fun _ => 0
  A3 := d.yhm
  A4 := d.ohm
  YY := fun _ _ => 0
  OO := d.oo
  YO := fun _ _ => 0
  pp := d.ml
  rr := d.hm
  ss := d.mhm
  om := fun i => 20*L i
  Lo := 6576
  Hi := 8768

private def upperSum (n : ℕ) (d : Retained) : ℤ := ((List.range n).map d.ohm).sum + d.hm

def keptC (n : ℕ) (d : Retained) : ℤ :=
  highWeightScale * (((List.range n).map d.o).sum +
      ((List.range n).map fun i => ((List.range n).map (d.oo i)).sum).sum)
    + 32880 * (-3288*d.ml + 4384*upperSum n d) - 3*d.mhm*3288*4384

def keptL (n : ℕ) (L : ℕ → ℤ) (d : Retained) (i : ℕ) : ℤ :=
  highWeightScale * (-d.o i - ((List.range n).map (d.oo i)).sum -
      ((List.range n).map fun j => d.oo j i).sum)
    + 32880 * (10*L i*d.ml - 10*L i*upperSum n d + 4384*(d.yhm i - d.ohm i))
    + 3*d.mhm*(10*L i)*(3288+4384)

def keptQ (L : ℕ → ℤ) (d : Retained) (i j : ℕ) : ℤ :=
  highWeightScale * d.oo i j - 32880*(10*L j)*(d.yhm i-d.ohm i) - 3*d.mhm*(10*L i)*(10*L j)

theorem keptTable_nonneg (n : ℕ) (L : ℕ → ℤ) (d : Retained)
    (ho : ∀ i < n, 0 ≤ d.o i) (hoo : ∀ i < n, ∀ j < n, 0 ≤ d.oo i j)
    (hml : 0 ≤ d.ml) (hhm : 0 ≤ d.hm) (hmhm : 0 ≤ d.mhm)
    (hyhm : ∀ i < n, 0 ≤ d.yhm i) (hohm : ∀ i < n, 0 ≤ d.ohm i) :
    (keptTable n L d).Nonneg := by
  exact ⟨fun _ _ => le_rfl, ho, fun _ _ => le_rfl, fun _ _ => le_rfl, hyhm, hohm,
    fun _ _ _ _ => le_rfl, hoo, fun _ _ _ _ => le_rfl, hml, hhm, hmhm⟩

/-- On the high interval, the retained coefficients evaluate to `W · FSr`.
The factors use `10960`, half of the affine library's normalization `21920`. -/
theorem kept_evq (n : ℕ) (L : ℕ → ℤ) (d : Retained) (m : ℝ) (y : ℕ → ℝ)
    (hm : (Rr : ℝ)*m = ∑ i ∈ range n, ((20*L i : ℤ) : ℝ)*y i) :
    evq n (keptC n d) (keptL n L d) (keptQ L d) y =
      (highWeightScale : ℝ) * (keptTable n L d).FSr m (3/10) (2/5) y := by
  let K := keptTable n L d
  have hc : 4 * keptC n d = 3 * K.cF := by
    simp only [K, keptC, keptTable, FD.cF, FD.u10, FD.u20, upperSum, Rr, Uu,
      highWeightScale, sum_map_range, Finset.sum_const_zero, zero_add]
    ring
  have hl (i : ℕ) : 4 * keptL n L d i = 3 * K.lF i := by
    simp only [K, keptL, keptTable, FD.lF, FD.u10, FD.u20, FD.u1, FD.u2,
      upperSum, Rr, Uu, highWeightScale, sum_map_range, Finset.sum_const_zero, zero_add, sub_zero]
    ring
  have hq (i j : ℕ) : 4 * keptQ L d i j = 3 * K.qF i j := by
    simp only [K, keptQ, keptTable, FD.qF, FD.u1, FD.u2, Rr, Uu, highWeightScale,
      zero_sub, zero_add, sub_zero]
    ring
  have hscale : (4 : ℝ) * evq n (keptC n d) (keptL n L d) (keptQ L d) y =
      (3 : ℝ) * evq n K.cF K.lF K.qF y := by
    exact (evq_smul n 4 _ _ _ y).trans ((evq_congr n _ _ _ _ _ _ y hc
      (fun i _ => hl i) (fun i _ j _ => by rw [hq i j, hq j i])).trans (evq_smul n 3 _ _ _ y).symm)
  have hForms := FD.FSr_evq K m (3/10) (2/5) y hm
    (by norm_num [K, Rr, keptTable]) (by norm_num [K, Rr, keptTable])
  change (Uu : ℝ) * K.FSr m (3/10) (2/5) y = evq n K.cF K.lF K.qF y at hForms
  rw [← hForms] at hscale
  norm_num [Uu, highWeightScale] at hscale ⊢
  linarith only [hscale]

end OMA.Erdos1186High

end

section

/- Decompose the high-slab objective into the Gram, affine and box certificates. -/

namespace OMA.Erdos1186High

open Finset OMA.Erdos1186SnivelyForms OMA.Erdos1186Low OMA.Erdos1186IntegerPSD
open scoped BigOperators

structure Coefficients where
  constant : ℤ
  linear : ℕ → ℤ
  pair : ℕ → ℕ → ℤ

noncomputable def Coefficients.evaluate (c : Coefficients) (n : ℕ) (y : ℕ → ℝ) : ℝ :=
  evq n c.constant c.linear c.pair y

/-- The polynomial given by the quadratic form of `N` at `(1,y)`. -/
def matrixCoeffs (N : ℕ → ℕ → ℤ) : Coefficients where
  constant := N 0 0
  linear := fun i => N 0 (i+1) + N (i+1) 0
  pair := fun i j => N (i+1) (j+1)

theorem evaluate_matrixCoeffs (n : ℕ) (N : ℕ → ℕ → ℤ) (hsym : ∀ i j, N i j = N j i)
    (y : ℕ → ℝ) : (matrixCoeffs N).evaluate n y =
      quadratic (range (n+1)) (fun i j => (N i j : ℝ)) (fun k => if k=0 then 1 else y (k-1)) := by
  have h := augmented_matrix_polynomial n (fun i j => (N i j : ℝ)) (N 0 0 : ℝ)
    (fun i => ((N 0 (i+1) + N (i+1) 0 : ℤ) : ℝ)) (fun i j => (N (i+1) (j+1) : ℝ)) rfl
    (fun i _ => by push_cast; rfl)
    (fun i _ j _ => by rw [← hsym (i+1) (j+1), two_mul]) y
  rw [h]
  unfold Coefficients.evaluate matrixCoeffs evalPolynomial evq quadratic
  simp only [mul_assoc]

def surplus (f g t : Coefficients) (N : ℕ → ℕ → ℤ) : Coefficients where
  constant := f.constant - N 0 0 - g.constant - highWeightScale*t.constant
  linear := fun i => f.linear i - (N 0 (i+1) + N (i+1) 0) - g.linear i - highWeightScale*t.linear i
  pair := fun i j => f.pair i j - N (i+1) (j+1) - g.pair i j - highWeightScale*t.pair i j

def rowBudget (n : ℕ) (r : Coefficients) (hint : ℕ → ℕ → ℕ)
    (prefer : ℕ → ℕ → Bool) (i : ℕ) : ℤ :=
  r.linear i - ((List.range n).map (yo r.pair hint prefer i)).sum

private theorem evaluate_surplus (n : ℕ) (f g t : Coefficients) (N : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    f.evaluate n y = (matrixCoeffs N).evaluate n y + g.evaluate n y +
      (highWeightScale : ℝ) * t.evaluate n y + (surplus f g t N).evaluate n y := by
  unfold Coefficients.evaluate
  rw [evq_smul, ← evq_add, ← evq_add, ← evq_add]
  refine evq_congr n _ _ _ _ _ _ y ?_ ?_ ?_
  · unfold matrixCoeffs surplus
    ring
  · intro i _
    unfold matrixCoeffs surplus
    ring
  · intro i _ j _
    unfold matrixCoeffs surplus
    ring

private theorem evaluate_reconstructed (n : ℕ) (r : Coefficients) (hint : ℕ → ℕ → ℕ)
    (prefer : ℕ → ℕ → Bool) (hzero : r.constant = 0) (y : ℕ → ℝ) :
    r.evaluate n y = evq n 0 (rowBudget n r hint prefer) (yy r.pair) y +
      ∑ i ∈ range n, ∑ j ∈ range n, (yo r.pair hint prefer i j : ℝ) * (y i * (1-y j)) := by
  let O := yo r.pair hint prefer
  have ho : (∑ i ∈ range n, ∑ j ∈ range n, (O i j : ℝ) * (y i * (1-y j))) =
      evq n 0 (fun i => ∑ j ∈ range n, O i j) (fun i j => -O i j) y := by
    simpa [sub_eq_add_neg] using sum2_aff n 0 1 1 (-1) O y
  change evq n r.constant r.linear r.pair y = _ +
    ∑ i ∈ range n, ∑ j ∈ range n, (O i j : ℝ) * (y i * (1-y j))
  rw [ho, ← evq_add]
  refine evq_congr n _ _ _ _ _ _ y (hzero.trans (by decide)) ?_ ?_
  · intro i _
    simp only [rowBudget, sum_map_range, O]
    ring
  · intro i _ j _
    simpa only [sub_eq_add_neg] using (coefficient_symmetric r.pair hint prefer i j).symm

/-- With the constant term canceled, the signed pair surplus and linear budgets
realize the rest of the objective. Only the row budgets require a finite check. -/
theorem high_decomposition (n : ℕ) (f g t : Coefficients) (N : ℕ → ℕ → ℤ)
    (hsym : ∀ i j, N i j = N j i) (hint : ℕ → ℕ → ℕ) (prefer : ℕ → ℕ → Bool)
    (hzero : (surplus f g t N).constant = 0) (y : ℕ → ℝ) :
    let r := surplus f g t N
    f.evaluate n y =
      quadratic (range (n+1)) (fun i j => (N i j : ℝ)) (fun k => if k=0 then 1 else y (k-1)) +
      g.evaluate n y + (highWeightScale : ℝ) * t.evaluate n y +
      (evq n 0 (rowBudget n r hint prefer) (yy r.pair) y +
        ∑ i ∈ range n, ∑ j ∈ range n, (yo r.pair hint prefer i j : ℝ) * (y i * (1-y j))) := by
  rw [evaluate_surplus n f g t N y, evaluate_matrixCoeffs n N hsym y,
    evaluate_reconstructed n (surplus f g t N) hint prefer hzero y]

end OMA.Erdos1186High

end

section

/-
High G24 certificate for 3/10 ≤ m ≤ 2/5. The mathematics is due to Carlos Toledo.
Certificate data from Chandler Snively, erdos-1186 v1.0.0 (commit
0b0155ead09841892690b9f9c469d1ff0edaff4c), Copyright 2026 Chandler Snively.
Source: https://github.com/dreadpiratechan/erdos-1186/blob/v1.0.0/computation/theorem-c/data/cert_region3.json
Source SHA-256: 8e118f99b502a9222ba5fb859f0f6a05468a3f84369a509d2243ca0878d4f304.
The release's JSON data are licensed under CC BY 4.0,
https://creativecommons.org/licenses/by/4.0/. The Apache-2.0 license above
applies to the adapted Lean code from the release.
The residual N − CCᵀ keeps its original diagonal. Each off-diagonal entry is
rounded downward to a multiple of 2^29 and packed as one bit. The matrix used
in the proof is this revised residual plus the original exact Gram factor CCᵀ.
The retained weights, branch complements,
short shares and orientations are derived from the release data. The inequalities
certifying this representation are checked by the Lean kernel.
-/

namespace OMA.Erdos1186High

open OMA.Erdos1186Low

def highQ : Nat := 1099511627776
def highD : Nat := 396225287841172684800

def highResidualRows : List SignedRow := [
  ⟨1, 1, 0x1⟩,
  ⟨1, 1, 0x1⟩,
  ⟨2, 1, 0x2⟩,
  ⟨3, 1, 0x0⟩,
  ⟨4, 1, 0xb⟩,
  ⟨5, 1, 0x17⟩,
  ⟨6, 1, 0x22⟩,
  ⟨7, 1, 0x7f⟩,
  ⟨8, 1, 0x41⟩,
  ⟨9, 1, 0x5c⟩,
  ⟨10, 1, 0x3fe⟩,
  ⟨11, 1, 0x2bd⟩,
  ⟨12, 1, 0x3ec⟩,
  ⟨13, 1, 0x385⟩,
  ⟨14, 1, 0x6fa⟩,
  ⟨15, 1, 0x561f⟩,
  ⟨16, 1, 0xfe7e⟩,
  ⟨17, 1, 0x1e7e4⟩,
  ⟨18, 1, 0x313c⟩,
  ⟨19, 1, 0x21c5f⟩,
  ⟨20, 1, 0x3f95f⟩,
  ⟨21, 1, 0x77c5e⟩,
  ⟨22, 1, 0x2694e⟩,
  ⟨23, 1, 0xaf90e⟩,
  ⟨24, 1, 0xcc3348⟩,
  ⟨25, 1, 0x106f946⟩,
  ⟨26, 1, 0x43a48⟩,
  ⟨27, 1, 0x3a31dc1⟩,
  ⟨28, 1, 0xfe40101⟩,
  ⟨29, 1, 0x69afc7f⟩,
  ⟨30, 1, 0xefc8eb5⟩,
  ⟨31, 1, 0x3637f47e⟩,
  ⟨32, 1, 0xa4f98eba⟩,
  ⟨33, 1, 0x1a6ffdefe⟩,
  ⟨34, 1, 0x286f9dcfb⟩,
  ⟨35, 1, 0x18ffd8cb4⟩,
  ⟨36, 1, 0x8ff9b6b4⟩,
  ⟨37, 1, 0x1acc79dcf3⟩,
  ⟨38, 1, 0x19ffd8691⟩,
  ⟨39, 1, 0x786fbceb0⟩,
  ⟨40, 1, 0x85c051fe76⟩,
  ⟨41, 1, 0x19fae0ffe7e⟩,
  ⟨42, 1, 0x2bdd22ff6ba⟩,
  ⟨43, 1, 0x1ff6c08e34e⟩,
  ⟨44, 1, 0xdc0300afb01⟩,
  ⟨45, 1, 0x104543e42239⟩,
  ⟨46, 1, 0x5fb73033879⟩,
  ⟨47, 1, 0x32fa79073940⟩,
  ⟨48, 1, 0x7fff8023d7a⟩,
  ⟨49, 1, 0x34507007790b⟩,
  ⟨50, 1, 0x145f7302b94c⟩,
  ⟨51, 1, 0x15db51077f44⟩,
  ⟨52, 1, 0xbd4077237541⟩,
  ⟨53, 1, 0x1235d1f9077b4f⟩,
  ⟨54, 1, 0x15fa83c67c6b⟩,
  ⟨55, 1, 0x3239405dc621c0⟩,
  ⟨56, 1, 0x8274525901397f⟩,
  ⟨57, 1, 0x35de5302785e⟩,
  ⟨58, 1, 0x3fabd4f77073100⟩,
  ⟨59, 1, 0x40035fa7803f95f⟩,
  ⟨60, 1, 0x782b5d25dc40949⟩,
  ⟨61, 1, 0x40035ffd806755f⟩,
  ⟨62, 1, 0x3ffeb44551c403c0⟩,
  ⟨63, 1, 0x5480a95a74820359⟩,
  ⟨64, 1, 0xdc04d01ff1802079⟩,
  ⟨65, 1, 0x1518403ff5003fd43⟩,
  ⟨66, 1, 0xbb019a3ff603dc45⟩,
  ⟨67, 1, 0xa01bcbfbc4a3f67f⟩,
  ⟨68, 1, 0x413adcb9875f3d35e⟩,
  ⟨69, 1, 0x7befff3001f68c255⟩,
  ⟨70, 1, 0x16241dc5bf2232f6e6⟩,
  ⟨71, 1, 0x43aacd783027f80381⟩,
  ⟨72, 1, 0xd4000107bf7cba9cbe⟩,
  ⟨73, 1, 0x1dc800d64e91f2bfc7a⟩,
  ⟨74, 1, 0x3d7aa0d0aaf8453dcc4⟩,
  ⟨75, 1, 0x701120fc0bd0ff80381⟩,
  ⟨76, 1, 0x201ebdd63b80cfc019e⟩,
  ⟨77, 1, 0x3519149c0dff203f6a4⟩,
  ⟨78, 1, 0x2f542a4d42bfa3dbc7c6⟩,
  ⟨79, 1, 0x6b598201c31e4347de59⟩,
  ⟨80, 1, 0xa7508bcdc18f3392a7b1⟩,
  ⟨81, 1, 0x1c708abffd40515fd03a1⟩,
  ⟨82, 1, 0x3afdda20d22bf6021a1a8⟩,
  ⟨83, 1, 0x68b8dbf4f9e6061f20385⟩,
  ⟨84, 1, 0x7ab110bdfc880f0c9c81f⟩,
  ⟨85, 1, 0x17e7f422dc0a25b787fe6a⟩,
  ⟨86, 1, 0x70820c31fffe00b0a1b⟩,
  ⟨87, 1, 0x7feff880000b9ff557fc7e⟩,
  ⟨88, 1, 0x1f2f5da3fb971fe2461304⟩,
  ⟨89, 1, 0x497dbafcfad04539d605b5⟩,
  ⟨90, 1, 0xfff5f8ceeb8d0093f94381⟩,
  ⟨91, 1, 0x31d7c70404807bfd62bdcf2⟩,
  ⟨92, 1, 0x86dd98f50706f448bd8ae3e⟩,
  ⟨93, 1, 0x185c1503fee31c254fe403b1⟩,
  ⟨94, 1, 0x204bf9a45c107de58fa285be⟩,
  ⟨95, 1, 0x600939925b22ad7788e14e57⟩,
  ⟨96, 1, 0xf04d30aadf62f9009b8c8380⟩,
  ⟨97, 1, 0x60fd99bc180009a103d2e601⟩,
  ⟨98, 1, 0x204dfde4993751fe000afc4f⟩,
  ⟨99, 1, 0x557dadd320d47ff00afe43⟩,
  ⟨100, 1, 0x7ff5c40aefe9002afff26f⟩,
  ⟨101, 1, 0x41dffffd080007fffc0f7c5a⟩,
  ⟨102, 1, 0x25dfff5080087dbf601fc2f⟩,
  ⟨103, 1, 0x5fc7ba0058bcdfea0496fc400d⟩,
  ⟨104, 1, 0x7ec1b66ffcfa0616ffac116380⟩,
  ⟨105, 1, 0x19ffe800003ffffd9001ff617d6⟩,
  ⟨106, 1, 0xfbdfb222188dc91f8ff3077c7e⟩,
  ⟨107, 1, 0x4f6deb60250040103ffe0077c7f⟩,
  ⟨108, 1, 0x7ffec00000847f2bff6007fa3e⟩,
  ⟨109, 1, 0x4700fb7dff0000007ff6003fe7f⟩,
  ⟨110, 1, 0x2c1087f62f5805c004be600171c1⟩,
  ⟨111, 1, 0x7cd43fdf4e902586149fa44bfc73⟩,
  ⟨112, 1, 0xfcd009fffff5002418bffc2437d6⟩,
  ⟨113, 1, 0x17c375df203c47dc0467fa90bfb83⟩,
  ⟨114, 1, 0x21b0f4a9ff7fc6f40e3a2bf8f7682⟩,
  ⟨115, 1, 0x41885593cffb3f803930017f400c1⟩,
  ⟨116, 1, 0x81a8ffac0200d3fef8b009ef80305⟩,
  ⟨117, 1, 0x1309ba6cf80bfffff8001ffc0380⟩,
  ⟨118, 1, 0x23f80026c95f9803a0fbfd403f45a⟩,
  ⟨119, 1, 0x281301020fffebc3009d108666f7c7⟩,
  ⟨120, 1, 0x20166fd85e727c00034ef888d9ff47⟩,
  ⟨121, 1, 0x821b093a3bfd43aeb84b17c7e9d67a⟩,
  ⟨122, 1, 0x4760e3dabfe6562000358ff22bfde6⟩,
  ⟨123, 1, 0x2ff44fff1b757bc80000fff602df67a⟩,
  ⟨124, 1, 0xc07ad76e3ffffe41c0441e2c705d656⟩,
  ⟨125, 1, 0xd001e07f569f8814ffdff001ff863c2⟩,
  ⟨126, 1, 0x2df9961fde41904cfffc0604eb67710a⟩,
  ⟨127, 1, 0x6f80d64ffe00381867d11dbeb92dfeee⟩,
  ⟨128, 1, 0xad91fe00005ffeff14513406a776ee28⟩,
  ⟨129, 1, 0x187fc027ff8002403efefb420b6f88389⟩,
  ⟨130, 1, 0x2ef101a8bf81dff964000473bc34a841f⟩
]

def highResidualDiagonal : SignedRow := ⟨131, 51, 0x18930ce7a27b9712619e1318a9624c330608c83c4986778638878930cf0c8917f12619d30168f624c3415a5b32c49866a416f058930ce2582e8712619ba461bae24c33ce7c617c49868f34a56f8930cbac85a3712619fd483d8e24c33b4ed2e5c49866ef9041b8930ce7ef23af12619d155f29e24c342a39377c49867e9d87b38930d0dfdb8d71261a04ab79de24c332d21e1fc49866743cb478930cdfd7ecd312619bf1aac1e24c33d4ba9d5c498676637da38930ce29977df12619c395216624c33573cf46c4986828c33bf8930ce883411312619e7dbfd2e24c34bb2b2bcc4986758a34478930cfe4b2f2b1261a1262c88e24c33df896cfc49866d33845f8930cd351111b12619d4688a2624c33f00e719c49867fe7652b8930cec8fa33712619f4d4696e24c3402e0ce1c49867128a5f58930d4472734312619bed43ce624c3348988ebc498681ab576f8930d0021170b12619de21c25624c322198176c49867c9cd1798930d14a625cb1261a15faa44624c344182f1ec4986724b0ee18930d226a410712619655002c624c34dd1592fc498683efec5d8930d03173e1312619b66d524e24c33d24198fc4986867597a98930cfff0c1a71261960fd6fae24c33fb554acc49865b78300b8930cf1d3cd0f126198ebf5c2624c3403e8c8bc4986897a78758930cd2c2fe871261a4b0d44be24c336fdc6edc49864bdfb2bf8930cce5d338f12619efa03ba624c32218357ec498645b551018930cc20ce54712619f27f8f8e24c340bede6dc4986661630a78930cd91bb6f712619ff0e630e24c33e2f4a8dc49867abbff338930cb26f61531261a499f892e24c337da6c5dc4986714188218930cf52500cf1261a089e52fe24c33aab31c7c498674b339538930cdce9638f12619fab76d1624c33de0d061c49867431d8ef8930cdfe20d6712619b135635624c345e5d6f3c49867a72f7978930cea3a75af12619a140f8ae24c3359708dec49866ce9bccd8930cef8b2db312619de254cde24c338f96c72c49867a0f8c698930d1c8404ab126197c69a15624c336afeaffc49866e77a4c98930ce384a40312619ae97221e24c3396835c1c49866fb3cc1d8930cf63e6adf12619d65af8f624c33b413406c498680d5de258930cdf57193712619fa4b126624c32412caec⟩

def highResidual : Nat → Nat → Int := residualEntry 536870912 highResidualDiagonal highResidualRows

private def highC0 : List Int := [734868932]
private def highC1 : List Int := [-17424276, 230430534]
private def highC2 : List Int := [-2419827, 94814843, 155955879]
private def highC3 : List Int := [660243, 190041658, 25203191, 254136036]
private def highC4 : List Int := [-15535039, 93821281, 12886230, 97805838, 120590748]
private def highC5 : List Int := [-13399188, 53721367, 2222110, 37813288, 16967813, 75026870]
private def highC6 : List Int := [-15531543, 46323327, 6686515, 7808003, 43977792, 21978927, 66083914]
private def highC7 : List Int := [-14099475, -46357213, -4649973, -46399847, -13564900, -13955994, -29853113, 62220903]
private def highC8 : List Int := [-13420797, -49598771, -2698185, -44206973, -12980726, -10448285, -30097635, 27035066, 68186373]
private def highC9 : List Int := [-12198991, -45358272, -5296195, -47170076, -13491960, -11942753, -30653343, 11213185, 5127104, 86182832]
private def highC10 : List Int := [-18856487, 46071907, 6787777, 7991076, 43034997, 21324185, 33102674, -8933897, -11574139, -5475019, 55475546]
private def highC11 : List Int := [-17995345, 46142807, 6771857, 7937211, 12025296, 27838193, 41697116, -4365271, -7365607, -12321534, 22514984, 61522699]
private def highC12 : List Int := [-48527209, 138823847, 20118401, 23520276, 37427441, 76576857, 80048417, -44453900, -44661256, -46470624, 29584453, 13684191, 173026489]
private def highC13 : List Int := [-18406473, 93389826, 13101515, 15048719, 4454434, 50109353, 31330255, -25027220, -2512862, -5535295, 35981183, 34640773, 51991389, 120370731]
private def highC14 : List Int := [-38338344, 187091768, 26021552, 29880251, 4006960, 13054851, 119922219, -51684906, -32724243, -70979370, 35636219, 47310538, 92068116, 84209946, 167054789]
private def highC15 : List Int := [-12853752, 46525811, 6604961, 7653549, 613473, 9962544, 20784582, -18444746, -9155272, -5240970, 25964229, 13607882, 22269489, 33746530, 22546581, 80758009]
private def highC16 : List Int := [-14814443, 46187801, 6676829, 7904559, 1846011, 833380, 18621158, 4911676, -12412717, -26115206, 31061883, 14038116, 25273528, 21016343, 11118082, 6235005, 85113795]
private def highC17 : List Int := [-19801795, 44578418, 7510161, 9038354, 4215340, 5330062, 15220033, 4031139, -24176106, -10768012, 29899280, 15583709, 25019377, 18135494, 18493596, 27026703, -2046929, 97528159]
private def highC18 : List Int := [-8939640, -44792347, -5392072, -5948061, -10695012, 800378, -24045003, 6184788, -7103030, 25203104, -20436150, -18453091, -14309887, -25566240, -9567371, -30874018, -736611, -1772965, 100103902]
private def highC19 : List Int := [-10229320, -44889875, -5458916, -5865157, -15411367, 3044828, -21720976, 3869667, 16875650, 22527037, -5661589, -20201099, -19769795, -27834312, -13183811, -3331601, -20015229, -10866011, 5513255, 91153589]
private def highC20 : List Int := [-6794614, -44630156, -5563521, -6057923, -8315861, 1574452, -10063091, 2799663, 6383793, -1198862, -15541145, -18670818, -27808414, -26132030, -2184776, -7610700, -11375733, -9271622, 31102488, 6107939, 70396043]
private def highC21 : List Int := [-12198806, -89154557, -11169308, -12193791, -5848900, 1567960, -11220328, 3881069, 3589925, 2347072, -37430097, -32841235, -42407315, -54893886, -21160031, -14934272, -21659471, -18083455, 26397603, 22023954, 14729898, 120852268]
private def highC22 : List Int := [-12604901, -177417018, -22697719, -25049370, -9430864, -26670484, -12025503, 13193897, 7863054, 4777298, -41785812, -22416067, -153267335, -100034413, 17104146, -23388170, -35828488, -32200698, 75567762, 60434836, 49334581, 90228925, 124690470]
private def highC23 : List Int := [-2156042, -88393511, -11474949, -12757181, -15550, 1842078, -38850717, 11109556, 15695089, 17079658, -15645133, -19887600, -73300638, -46200083, -30908120, 5569158, -9865609, -13303516, 22203978, 10987295, 18915548, 47622006, 10426520, 101369930]
private def highC24 : List Int := [-29925835, -178726759, -22170201, -24077266, -11504582, 2620490, -23772108, 2908190, -5545466, 3881500, -19932966, -9662722, -103221929, -145225527, -139412937, -12004714, 3019699, -13243508, 46061780, 39445484, 48727740, 52151280, 79302302, 30760155, 163733765]
private def highC25 : List Int := [-13277923, -67178123, -8251236, -8913621, -3747938, 7175738, -8947321, -21985505, 7671485, 4507084, -11690212, -11253276, -14303661, -50097292, -34561247, -20140975, -20990488, -15666062, 17236001, 11175851, 20510448, 22318564, 25264825, 24217993, 20512610, 97997123]
private def highC26 : List Int := [-6859302, -18890297, -4917491, -5369057, -1687699, -191594, -3152027, -1689606, 1783251, 381091, -4933780, -3513221, -4823676, -3240239, -15488480, -11075477, -6617212, -6716553, 8161408, 8875342, 8916889, 8884636, 5647567, 12111630, 6410399, 4981894, 67143059]
private def highC27 : List Int := [-8578926, -16568859, -6355513, -6957937, 3353028, -720937, -6481413, -669271, -70501, -89432, -9008228, -2461265, -9751434, 1323262, -16866214, -10992759, -10019592, -6492328, 8237637, 9513551, 8651284, 11313762, 1393321, 5544252, 11929842, 2253532, -235007, 72313306]
private def highC28 : List Int := [-20310703, -45651882, -5151842, -5299314, -4399846, -994374, -6241737, -3704551, -3965821, -1276642, -7438664, -4698098, -8209167, -277963, -34572245, -23532340, -22562712, -16306058, 14522383, 15559638, 19653800, 20945475, -1950478, 6593442, 26281374, -332607, -2027070, -2003009, 112035572]
private def highC29 : List Int := [-13170994, 44628969, 7753002, 8958674, 866855, -2778924, -2489068, 8624110, 1361965, -984656, 8999361, 5456459, 8370434, 26305042, 3916948, 14466310, 19761581, 12089884, -16294385, -6697817, -14279446, -18602240, -23622084, -19761648, -11656978, 4025330, -3814812, -6124869, -5630997, 77232030]
private def highC30 : List Int := [-11896744, 46480425, 6647178, 7680539, 745377, -3172632, -2803675, 2829213, -803476, 4217081, 7775972, 5888359, 7391976, 4292298, 3510790, 25899091, 10069742, 9595696, -19668008, -24829722, -19183197, -22643022, -16877662, -15343648, -25710603, -3158164, -127239, -2345915, 1360836, -667429, 79882974]
private def highC31 : List Int := [-6155552, 23283117, 3294177, 3811502, 338947, -1631154, -516087, 1471913, 706304, 786371, 3940323, 2206601, 3521929, 5134310, 3976685, 3910675, 8246806, 7621706, -11108027, -10421597, -8698180, -11113464, -3198848, -8571170, -10818034, -1817100, -4964029, -1037571, 20395, 2052029, -2437025, 58350067]
private def highC32 : List Int := [-12079989, 93980858, 12856215, 14611628, 2861127, -4902662, -1048593, 3484812, 13924122, -4386322, 16135392, 9885388, 14547283, 30527696, 7155747, 14917711, 14410009, 40455908, -37608978, -40756947, -34119440, -42792391, -22300286, -35883161, -31660320, -14561420, -4319764, -7528325, -4345183, 20181741, 8378933, 9255177, 101939283]
private def highC33 : List Int := [-23418058, 188220945, 25567273, 29043019, 11769846, -14297167, 19082490, 3567818, 9967244, 578078, 13394266, 11216896, 20683914, 17882862, 6036306, 32816878, 47572281, 38317926, -90754913, -66248156, -86303294, -114662758, -99430674, -88767298, -42382558, -19748283, -13274119, -12652534, -18100453, 31819683, 60937507, 23528408, 41541893, 156374583]
private def highC34 : List Int := [-5357728, 94543412, 12529673, 14215749, 3655825, -6674921, -2938352, 17632899, -4665116, -2738358, 17203775, 387375, 17303670, 20090352, 11964518, -7152692, 5724342, 32580645, -44448501, -37979758, -39753135, -41563319, -26278775, -30998420, -38969476, -10424442, -6124866, -8001474, -6796785, 9094047, 33147951, 19089399, 35709763, 6802482, 91215456]
private def highC35 : List Int := [-12454136, 198132684, 26886776, 30242668, 7645611, -7963977, 23311231, 20347499, 18280871, 34811, 16182676, 2295926, 33530844, 38543284, -7304353, 1947991, 4282576, 8973259, -67523746, -66711573, -59478782, -96685214, -101808015, -49296251, -72015083, -28893624, -16452830, -25267666, -28203352, 16268575, 11228754, 11451730, 37056798, 48595034, 26624575, 141349095]
private def highC36 : List Int := [-6299376, 89400417, 19398054, 21874257, 5322959, -1189741, 15223494, 13985729, 10273782, 7234013, 1127968, 69465, 21796546, 10528830, 11532011, 2232824, 10684601, 11073957, -33982392, -33000547, -24703674, -53742567, -63818966, -34658391, -27844418, -13618206, -11545032, -8021758, -10825841, 10515976, 4769273, 5769866, 14439170, 14680649, 13369703, 55416895, 63458867]
private def highC37 : List Int := [21023229, 190576534, 24824606, 27239568, 11213396, -3823200, 24446317, 42151920, 9484035, 33732986, 16572607, 10621934, 54289320, 40880316, -641025, -1242370, 5370237, 8984579, -46111370, -50182653, -66258452, -95723830, -126698550, -21315089, -70046108, -32377724, -20185976, -25717432, -29388539, 935951, 10868551, 20172503, 30977115, 26332094, 42273872, 107939510, 21258441, 143862322]
private def highC38 : List Int := [7499535, 97686735, 10907470, 11983375, 4840747, -3124288, -2876403, 1240707, 4948283, 26707678, 17115502, 9895120, 22439084, 7229813, 11937652, -3696752, 2734743, 456744, -25330874, -20093650, -7944045, -65822225, -49745564, -6448920, -48672068, -26864475, -13268476, -11657341, -12464842, 15065639, -7460550, 4224470, 23958065, 8766226, 12536346, 29881250, 17726249, 22636260, 112378016]
private def highC39 : List Int := [-20036480, 188244953, 25140591, 29058276, 6299921, -8585435, 18083354, 3460115, 10371048, 560592, 10218788, -16395444, 71963208, 5113809, 42582924, -13821448, -209096, -6826551, -221525, -42659554, -63314377, -81815949, -101414986, -19079845, -96876849, -71979012, -32995250, -31164345, -39675398, 33209602, 37046511, 18017739, 54066330, 26897640, 33709491, 81037368, -6637564, -9052639, 65295293, 215814373]
private def highC40 : List Int := [-12258054, 44654478, 7096339, 9002644, 1565910, -2177346, 2984392, -2282360, 1431421, -1225119, 285956, -10829593, 5398337, 12953119, 24482804, -7203491, -860960, -647922, -1889781, -1256512, -7220381, -31848798, -18774969, -13585061, -17415965, -14851768, -2492826, -9844835, -11056519, 10153561, 10730771, 7875233, 16770731, 8514728, 7572867, 13661893, 13972795, 6305427, -1326332, 7451847, 106194212]
private def highC41 : List Int := [-16694833, 44449681, 6534230, 9223062, 671677, -3332641, 2906590, -3917048, 894618, -1957960, 630555, -2951274, 14728112, 1306191, 7790992, -2351776, -1826947, 2120487, -2682100, -2120840, -29447150, -14039860, -24891648, 1963428, -13074611, -26311321, -9366655, -13077382, -16817407, 16611391, 14003941, 8802412, -1999284, 12315373, 15733346, 14797053, 10940625, 8036324, 39240050, -4655929, 18175225, 100580364]
private def highC42 : List Int := [-22924583, 38383326, 9245518, 13506753, 878974, -2387690, -6569203, -8339492, -3735199, -5877417, 6664380, 1685854, 5252704, 5843124, 4744956, -1272352, -795880, 607564, -14505872, -18518339, -1531177, -7354273, -38389471, -25166850, -11404941, -9956844, -10372577, -15776184, -22882030, 7020359, 8852221, 5629823, 9363905, 4362962, 12449446, 12321022, 5706929, 20850038, 27153316, -2891005, 14741866, -5666957, 124816753]
private def highC43 : List Int := [-21986202, -38355827, -8895411, -10379939, -6147844, -3545334, -8738298, -3747546, -3347628, -1541863, -4631295, -5893130, -10865179, -7005738, -22993335, 4790461, 11640, -1238641, -973120, -2886161, 2077246, 32983583, 12128485, 28026003, 24327268, 13718479, 4559088, 4072186, 5071024, -16407840, -17472545, -11079204, -17432179, -8146466, -5709661, -13164679, -4576102, -42533429, 3972784, -923207, 6799656, -8109766, -6292938, 125197917]
private def highC44 : List Int := [-19394478, -37741208, -9293519, -10806518, -6466911, -6277290, -8161952, -3186680, -2997355, -1351511, -3467599, -3602344, -9233090, -3477004, -6696783, -3984331, -3221346, -3507603, 314729, 2257996, 9037408, 1896046, 3487883, 29307763, 47724913, 21680550, 6050806, 4902795, 4969652, -21168808, -14265182, -10410371, -18284697, -20352805, -8386306, -15550131, -13415457, -20801667, -8776017, -9225004, -1159717, -856860, -4712378, -5561839, 128849237]
private def highC45 : List Int := [-15267481, -41021958, -7231437, -8568413, -5506515, -11562009, -3021231, -1844356, -1715372, -37618, -1561204, -3370227, -5659458, -1738743, -8190779, -8690264, -3496873, -2269870, 649424, 2895814, 11564469, 4384046, 5042645, 10371799, 56114914, 23230674, 7270145, 3970163, 1174859, -21515794, -10338170, -9114765, -18033267, -23604308, -9173041, -15494580, -11183175, -24833569, -10568523, -1965539, -979290, 3958709, -4563399, -6167979, 4459644, 123004407]
private def highC46 : List Int := [-22092673, -73501620, -14429338, -23549971, -9708502, -7275155, -17595825, -2319921, -3532817, -309309, -10435364, -7146683, -16255084, -6844490, -10208285, -13714273, -3013690, -11114446, 3441109, 20114876, 10423350, 7440746, 9014087, 59702330, 82134901, -28394470, 20211301, 17555766, 19221256, -33070722, -26237358, -20502088, -41925424, -26524275, -23494976, -59689011, -1793655, -22011583, -54186643, -45356707, -10440261, -4518978, 2131363, -8350932, -16816191, -16895348, 152069942]
private def highC47 : List Int := [41853440, -157881460, -32909857, -38786736, -5545068, 6457678, -20958257, -23295238, -21547047, -9988673, -22176050, -11705425, -30222432, 4386620, -23432554, -28701054, -43553800, -33834830, 13633038, 20643073, 66116531, 11010191, 56913155, 37799348, 1428980, 81243344, 28108779, 39515024, 77947259, -47335686, -55390778, -54964013, -99973603, -66265898, -70077599, -76014195, -30915390, -55831511, -55806887, -54005302, -33301127, -4793905, 6881812, 34431396, 15524921, 10948422, 9550168, 206532696]
private def highC48 : List Int := [19612555, -80534015, -15632633, -18279760, -2741252, 3027956, -11987800, -3918692, -7376283, -429947, -6632204, -3930115, -10493449, 2200851, -8080401, -22732976, -12816329, -21395919, 3812167, 9276243, 15663869, 13636693, 20741362, 23709925, 4560791, 40083808, 1406309, 20440119, 23323633, -22894449, -39268967, -29546254, -53543221, -39333244, -36814043, -39906134, -15966665, -38370846, -40380182, -7357503, -19365765, -7479661, -6028449, 17190533, 6121938, 3982393, 3768629, 60319409, 85478219]
private def highC49 : List Int := [33890685, -173900695, -24113697, -27658771, -3925236, 1439582, -16123668, 14045827, 8706104, 14990305, -1101192, 1525191, -3042585, 24626827, -19167863, -14384434, -13573564, -6095603, 22712382, 23294100, 37759884, 36439424, 37395394, 13874938, 20170154, 6598292, 48959861, 33630926, 40271687, -71109165, -92805038, -53502668, -93994286, -94390173, -82978830, -77722937, -48957933, -85505577, -58689033, -21330895, -15560902, -8522553, -25339309, 33954179, 27964066, 31287448, 881912, 92445016, 81078355, 157693770]
private def highC50 : List Int := [-7629959, -82305834, -10457772, -11501037, -4332595, 1695121, -13993097, 13085495, 533421, 9188903, -1989104, -1270903, 68725, -5751040, 3120009, -6141362, -4411713, -15266843, 8733232, 9104408, 14540000, 18826734, 25332192, 11027591, 12093565, 2467566, -4598991, 5123381, 7473267, -31440572, -32422573, -31987308, -56992156, -22128726, -41028470, -54534294, -28794915, -26028584, -26023891, -15581941, -7806056, -1868724, -5252193, 17209711, 12020405, 13171526, 9852839, 46002281, 25705113, 14738819, 113072540]
private def highC51 : List Int := [-48564516, -151985717, -17920224, -18922549, -12449928, 3899838, -23129648, 20272248, 30945578, 22610726, -5468422, -6659053, 7645525, -16141706, 6212411, -5461705, -8650298, -15091457, 32638745, 25288220, 39890360, 54417969, 48528876, 46578913, 40169082, 20418455, 23756072, 8340085, 1708588, -29455376, -55215634, -42317341, -64366915, -53197469, -51108996, -86555522, -46033864, -58836388, -63299376, -49194075, -25462496, -4402888, -14512642, 30122694, 21146101, 23225371, 30523804, 116114915, 41504266, 71199269, 69023386, 102111067]
private def highC52 : List Int := [-35310188, -61258974, -16911014, -18216464, -9634999, -5927484, -16366793, 6458004, 4306292, 5643614, -9269650, -6713585, -10106951, 10744713, -11980779, -8366291, -8646718, -6525151, 18964342, 18988661, 24123704, 31429770, 37097390, 19671045, 16047155, 4509439, -5246511, -4988427, -6665608, -30678543, -28049018, -15015844, -29207027, -37093314, -4409304, -42854766, -34194607, -33742329, -38261612, -22872787, -14582992, -3196160, -11766878, 10451798, 9038794, 10165282, 17035754, 50453683, 19589346, 44291471, 17886249, 28737305, 91667352]
private def highC53 : List Int := [-50294382, -156611398, -18664913, -20356193, -11826298, -446779, -22266667, 27375435, -6746200, 15971068, -3021385, 7938667, -13516640, -12488874, 2430814, -7801997, -9904307, -16191278, 26736389, 28041330, 35659962, 46739180, 40667564, 28824064, 25691876, 7404089, 3257060, 7174087, -1621880, 30050975, -68030882, -43551846, -83896588, -102122644, -50108572, -95159145, -38418103, -80457784, -57795309, -45501813, -26187974, -14183950, -18991102, 25357547, 22718957, 22904803, 30979581, 90129875, 80753939, 66269421, 79825958, 78019792, 29459035, 130153496]
private def highC54 : List Int := [-25432077, -74361342, -13878221, -15048493, -7639904, -2575654, -13898674, 13690355, 4744476, 36870159, -4835563, -11197333, 2413547, -5607029, 9745536, 1225161, 1440260, -7728176, 4996048, 12036463, 20699942, 25412165, 28825783, 12491890, 20840756, 5316077, -2956287, 4795171, 2562562, -13958375, -28134089, -19137363, -43846433, -33118935, -23662987, -55411198, -15676892, -22796598, -23446469, -18920858, -14171978, -6799677, -8238589, 12001053, 7857386, 6076661, 6472643, 60482345, 30872096, 31280863, 37525827, 49037425, 10010939, 8989057, 63290795]
private def highC55 : List Int := [2679708, -150002546, -37070663, -44161722, -11767667, -1590683, -30721597, 11272575, 962692, 7123734, -19511038, -10925439, -18159213, -13948470, -7619556, 3156671, -418863, 1503254, 8532195, 17292315, 19555076, 26084469, 36336357, 10749762, 13746506, 31642810, 12604635, 12210201, 13348833, -22970812, -32184663, -26309438, -49582630, -61475688, -51283271, -166351368, -87189050, -8744592, -57079663, -36034310, -25285608, -1585000, -1613485, 26603367, 16265007, 19389686, 26949663, 116375004, 50661833, 62036611, 76725292, 58173063, 45857493, 12787877, 9013919, 106876421]
private def highC56 : List Int := [-4275701, -65502751, -20228939, -22711070, -6677070, -2725627, -15875673, 1145789, 1075756, 11934307, -8740844, -4480442, -8759145, 6291145, -10348449, -4762389, -1788613, -2065095, 14262088, 17020256, 21869461, 27106236, 28120907, 11452815, 12506597, 6345913, 2245862, 9947215, 14187663, -15390912, -9734043, -11885048, -25770362, -4915983, -22720159, -74516036, -16536466, -26460568, -25382623, -14889864, -15637565, -3864848, -6078744, 5455162, 6758276, 8746620, 17373218, 46685334, 9298349, 22502704, 26686189, 37565295, 12682313, 3748860, 9462596, -1753116, 91802526]
private def highC57 : List Int := [-22285095, -136731417, -31813078, -35302307, -12663821, -3581540, -27605891, 14578422, 23278847, 26642891, -8616501, 5361121, -8004481, -12236490, -2989326, -2610907, -2999374, -7122735, 34070339, 29964134, 43765705, 58985637, 52920291, 26582037, 30527264, 11952708, 5962029, 11741657, 8936979, -7494982, -31442727, -18592869, -28630800, -89398070, -75203792, -109507157, -17381250, -51623820, -52334379, -36823470, -18797564, 1883041, -3112555, 27284231, 25262804, 23662609, 6792720, 70040447, 27614485, 29404003, 35121401, 33177847, 35387216, 17784341, 18151945, 20230718, 68775503, 168855966]
private def highC58 : List Int := [-10234457, -62534693, -19967786, -23280431, -7516918, -3996807, -16614393, 17794694, 7774749, 10483779, -5425815, 871183, -18497878, -4079548, 2493266, -118751, -1999930, -4151635, 13580020, 12859260, 6273333, 15458443, 29924535, 14908443, 21598855, 14703827, 5712318, 6156255, 9546774, -6741897, -7452109, -4303778, -24878522, -20629926, -6894786, -71102594, -14654200, -13917200, -24000099, -15351989, -16282176, -6164559, -8694517, 14995461, 3280364, 6276941, 11592960, 35730195, 10764050, 7492293, 12594475, 16161601, 4719713, 15375277, 13008566, 18446566, 37307618, 49189300, 80979275]
private def highC59 : List Int := [26166550, -141450614, -14670438, -52841521, -10738601, -43003, -33614993, 16640886, 4607572, 9384135, -14291774, -11277161, -17452828, -18618594, -7721774, 3157701, -2367533, 3176062, 20191038, 19467789, 15970647, 34092020, 38650832, 10402873, 19387951, 22384865, 15913828, 16044025, 19007122, 3959005, -23106192, -18878243, -46636616, -48221758, -27873200, -162207603, -28330796, -56591918, -27857867, -33272939, -18385743, -13749465, -21834725, 31975711, -596210, 14752185, 24170267, 71593287, 23958905, 29300218, 40245096, 43065391, 18570059, 32119919, 15373521, 45290235, 30001408, 93127495, 93036395, 133884033]
private def highC60 : List Int := [5134598, -75429557, -11309448, -22487938, -5504685, 93692, -15400594, -698199, 4389904, 6047246, -5239060, -10023916, -9256899, -4454248, -4631516, -1804951, 966966, 1437179, 388523, -4807106, 14500896, 11642841, 30222541, 7292690, 6872420, 4262574, 5774266, 9457861, 9508586, -399253, -1738994, -8562896, -11445601, -40878485, 857964, -103312048, -22747969, -33482764, -5202981, -4003756, -14692836, -7131443, 2500319, 11661778, 14144834, 12544645, 6828436, 10660609, 17728116, 21399786, 24366531, 13894745, 27129414, 12825872, 21088082, 7867272, 15400440, 48960990, 8337651, 22749629, 94855497]
private def highC61 : List Int := [-20163892, -115489203, -1123478, -60286787, -32310838, -18676655, -27970040, 15023945, 6265745, 10039725, -34184194, -27962087, -36502309, -20403458, -29534680, 332558, -7322425, -6180471, -3423580, 5476159, 8716101, 33424355, 55400816, 12527460, 7362877, 15881759, 9957685, 11411684, 15485859, -10938819, -19864294, -22502288, -57688459, -23468853, -36448231, -120771364, -56100896, -59355174, -107212086, -84102387, -32781947, -9905004, -7513068, 34768972, 33935724, 37359951, -15851066, 68173151, 26485306, 36169013, 30644595, 50584287, 42030400, 22076548, 3414290, 49786783, 35362290, 70392604, 34480290, 35821368, 72459635, 216322175]
private def highC62 : List Int := [-21504085, -60208946, -29251630, -32021450, -10706543, -9049611, -19317125, 822441, -721280, -588618, -17503661, -11214117, -19093943, -7426125, -12375338, -670039, -56907, -3243239, 1712675, 3004328, 8551143, 11911272, 12204459, 2310435, 10056374, 7127806, 2606525, 778160, 2613801, -9755655, -13121187, -12431229, -14202758, -17378474, -40238647, -52438640, -29245672, -41350870, -1589705, -40055891, -9025636, -7204835, -11275046, 10536857, 9643523, 13618674, 5714350, 40214515, 6677159, 24382869, 21914410, 20468875, 29455142, 17333001, 17185467, 31522615, 22118570, 56210188, 11721802, 9332910, -15243245, -459048, 151593770]
private def highC63 : List Int := [-52841004, -136393926, -15799081, -16304646, -12075223, -1979191, -15118175, -6215991, -6946315, -665871, -21833699, -14517383, -21732576, -1112999, 6570793, -4567821, 1338369, -7053943, -1835690, 1203054, 843102, 5583598, 10998999, 1573684, 14511433, 4793332, 6380994, 5887188, -2713023, -10700167, -10453100, -9308414, -22986442, -4716502, -3139423, -76934289, -14934134, -38383223, -79500810, -73830400, -58918729, -27598604, -32904544, 11178949, 23854313, 27410270, 17298403, 75595969, 29503018, 35345925, 22442377, 34776972, 15598353, -10404823, -17156970, -25809475, 30042676, 72239340, 28598835, 8282157, 4798271, -1414541, -7681798, 240186693]
private def highC64 : List Int := [-21592854, -45885798, -5165296, -5119728, -4249146, -951344, 174284, -857994, 569993, 424409, -10720363, -7994156, -8426025, 1085584, 14679, -501763, -10623, -1504997, -896639, -1559930, -1429488, -2409561, -1698910, 5356304, 7425780, 1990994, 1486106, 1315599, -1817940, -6105998, -3895350, -4667433, -4931226, -3662014, 2741499, -19595146, -290339, -39972005, -23820438, -15338259, -18526024, -9135510, -8466356, 1598434, 2361605, 2580038, 4058393, 23341876, 9656918, 11646218, 12874643, 12443073, 3654931, -5457383, -148640, 10032423, 2518107, 21604943, 16920273, -2256161, 4161912, -7072504, -3119588, -11817401, 119826321]
private def highC65 : List Int := [-14437488, -30971358, -13986090, -15416748, -5589322, -4827552, -10257107, 12997257, 7166540, -3383233, -5628972, -5485338, -5901385, -3561820, -4880395, 1029471, -4030445, -3846496, 3890904, -9619371, -7667130, 6583710, 18571167, 2222323, 4315589, 5134347, 2605581, 2625737, 4152804, -4330903, -7850952, -5585968, -8486618, 1083599, -10885058, -24919531, -2239334, -19834086, -27251321, -21539429, -12745026, -6261948, -4755153, 5636794, 6817358, 6288030, 6604797, 20520268, 4947781, 13713510, 7619445, 16140295, 5521870, 3014944, -2140735, -6048112, -968149, 25285135, 9297317, -1033887, 4317346, 14224611, 2110550, 2502671, 11317476, 82326900]
private def highC66 : List Int := [-17525308, 21256510, 22063886, 25028574, 3698785, 4015304, 1910511, 4046925, -6709009, -3330420, 11623946, 8578543, 11943359, 7343160, 2695614, 1304525, -728583, -3115565, -5695509, -5404936, -2168950, -5414967, 4721081, -4407180, -13234704, -6580418, -4538237, -1617572, -6128009, 3850262, 2424747, 1230643, 6505469, 10756950, 3027946, 20926300, -1176138, -1933261, 22655666, -8573094, 1350754, 10190501, 13073540, -16943332, -12929332, -14382794, -15151990, -32649537, -9802366, -20308481, -17836645, -11630115, -5224841, -12283181, -38959, 9408979, -4903206, -10403594, -10198168, -10122500, -13056099, -8520375, -12425550, -6713742, -9220757, -9687195, 75588297]
private def highC67 : List Int := [-19585802, 11567702, 28075985, 31683212, 4713213, 5493978, 9349085, -13411270, -351151, -599526, 12373366, 16595050, 10298409, 5347082, 9991895, -2098743, 2871615, -280447, -6159697, -5763686, -4940226, -8164030, -6504246, -2015307, -10018349, -10514045, -3069659, 179339, -6710639, 6554498, 4432388, 2572562, 7294736, 6562084, 7893727, 12106622, 8870731, 3980335, 45455662, 2436240, 10010230, -747951, 3763259, -18993279, -12201777, -11468048, -13556100, -17992193, -4212607, -20545055, -16012414, -11648638, 3388207, -14959357, -7111820, 1051109, -5724298, -16861926, -4861227, -13612428, -16441844, -70124, -7839843, -6505779, -9454456, 6225149, 15543873, 104112506]
private def highC68 : List Int := [-52718837, 17174665, -6829604, 41578083, 80529916, 48347946, 26391345, -13447254, -31597431, -32014181, 7169960, 34829060, 33685692, 39700594, 59920805, 7096437, 16459915, 4462409, -18711683, -4417125, -30453618, -19344412, 10185186, -22666671, -31462485, -24953786, -9470764, -12225397, -16950756, 33707766, 37472106, 20473700, 47344846, 47701435, 27750241, 81920366, 18477820, 28660566, 29298231, 64140357, -10190869, 27972410, 26381308, -12601752, -23095932, -28252994, -43473549, -54518341, -55336602, -39496732, -82587711, -6178763, -11060367, 5360840, -2496344, -16884109, -36440406, -46194731, -37466407, -9332337, -30197744, -19833485, -12406287, -54207220, -44809342, -29546651, -739216, 24135807, 159405728]
private def highC69 : List Int := [-10263346, 4414782, 227369, -231261, -1647205, -1912902, 85570319, -39436137, -12054364, -9038997, 34412355, 8107398, 27886523, 11945186, 13070570, 1829131, 12110276, 12416652, -7512744, -8053814, -22151957, -31270258, -18356974, 7387789, -27480715, -28331264, -9227496, 534788, -11942243, 34560990, 27437410, 17591711, 31970460, 15729088, 22112092, 36916022, 9231110, 3404356, 7834371, 60895666, 11229768, -14583508, 12515784, -14058602, -19721750, -15447467, -21846336, -49619545, -36867269, -11625013, -18459452, -35473211, 240179, -13181795, 7759387, -13742573, -15329686, -39985597, -18793805, 2924711, 1121444, -12468209, -7075419, -22153258, -31887588, -8007603, 42029747, 8788414, -21628262, 126586707]
private def highC70 : List Int := [-28759235, 43218881, 1092307, -26220777, -14774092, -14364953, -11955588, 171909, 3925839, -63268617, 12989679, 20504113, 145764458, 39903474, 57377238, 29265397, 15676405, 15383104, -21763326, -19944669, -24805259, -33275939, 10621225, -51173413, 4361010, -24615034, -10913274, -7193927, -21791685, 36572238, 44801439, 26538922, 46825065, 57285204, 32957825, 102106608, 25074259, 28651487, 41258542, -16001138, 52656559, 31134164, 26585702, -40959263, -37296153, -38515792, -37262728, -133399026, -26418993, -84513291, -60492522, -56093916, -10215915, 1277057, -27419475, -28186177, -46125037, -39041121, -47765393, -18049069, -35024376, -42070245, -46144738, -46716267, -51714865, -60173504, 50084608, 6514484, 26367093, 9361691, 149124547]
private def highC71 : List Int := [5127542, 4529488, -47931, -329503, 457932, 1234498, 1653277, 8529538, 4448789, 4933066, 14586321, 805166, 1928449, 41054741, 10393970, 27415293, -19464947, 32852872, -25556210, -4410989, -6924925, -41217991, -34075324, -7917384, -18614972, -8661644, -7928315, -9760720, -14179650, 10958732, 15523142, 14663325, 18914986, 18547866, 14518276, 66850897, 28713310, 29772225, 19540123, 254095, 30480455, -146605, 6939654, -16465925, -6695274, -12621555, -8485375, -72935672, -27277775, -31540780, 6729105, -15541455, 807199, -11553808, -7516028, 5773648, -23809706, -35188396, -23148124, 2871143, -17117035, -470880, -21938569, -19724057, -21291083, -11403473, 18326449, 16204616, 18792908, 22755851, 31623571, 83294772]
private def highC72 : List Int := [30491073, 15438886, -3803556, -5115200, 13830616, -13193023, -24919519, 8557233, 8382336, 4182761, 5753125, 25751921, 20897631, 53129785, -21669109, 32256106, 46646371, -1484775, -39859994, -48920898, -58860169, -53422024, -46498711, -6280743, -23031666, -43505659, -22709798, -24421045, -31018375, 38227171, 34589174, 29338011, 51710172, 29343558, 38744399, 74488120, 47057842, 56176640, 58014409, 7692759, 11489194, 7308877, 17040434, -34932497, -34899753, -21797603, -13729226, -116165935, -64121307, -102145683, -43807066, -22206822, -4116044, -19439348, -11096666, -9857862, -30293918, -103619550, -46923664, -18244019, -28213871, -13530327, -39598586, -45749253, -38915198, -34847216, 29889709, 24554238, 24463789, 53754167, 41573851, 38522890, 97313810]
private def highC73 : List Int := [-10810568, 12476850, 1908740, 2365670, 7038165, -17262220, 571255, 18738111, 10896486, 10850054, 6164926, 7808330, 14197536, 2275036, 1662613, 2167581, 13469477, 10874724, -20200707, -27900058, -4642478, -42054991, -29181642, -28161729, -13324745, -5584915, -9621173, -6130886, -9584087, 14376715, 15314122, 10472856, 26023701, 7428877, 15775087, 63761464, 25240308, 25173270, 14208638, -17595, -765754, 368135, 16077666, -14304892, -16669211, -16039434, -14380721, -37760394, -30537004, -28429496, -23686827, -6750913, -7360742, -16927140, 3135568, -11408019, -16452305, -45996327, -25004613, -12665873, -14907069, -15740564, -17520467, -26930722, -24719726, -17579876, 23907731, 20649337, 17410353, 27540597, 7714395, 16945935, 16659080, 50899982]
private def highC74 : List Int := [-29562215, 26058236, 4599283, 5783415, -1198647, -4997358, 755866, 27311202, 12090597, 13127479, 6331939, 2724289, 12221217, 1627150, 7893883, 598278, -3949159, 17855568, -27811014, -3018428, -41814361, -22488395, -33549897, -83392928, -105241197, -10495274, -14379399, -11867538, -12383944, 27990966, 44880609, 29855230, 59088673, 63525146, 37642784, 91895152, 21757546, 25793345, 34872471, 12586665, 6111778, -471429, -3892559, -26081286, -10880149, -23532718, -18692191, -99476181, -54125454, -68031669, -48231293, -41956088, -19177810, -10613915, -10321587, -13651768, -68852073, -108385005, -48826511, -41021646, -36260103, -21351577, -31870574, -33910514, -40600202, -30132697, 39401437, 18394967, 23081918, 55826160, 26540611, 36985001, 42203385, 15642117, 88619654]
private def highC75 : List Int := [-10612994, 9619054, 1644344, 2067744, -3528944, 4302751, 3446821, 14519758, -1269243, -8508032, -1073229, -3131943, -11058740, -42449247, 4907570, 9448112, 7404893, 2939667, 1373294, -9217412, -6585803, -11227274, 2069989, -22734706, -5796812, -20592968, -7883615, -10040340, -14802606, 18780942, 18014023, 11448620, 24106380, 37879264, 15069548, 59760381, 32933002, 1988111, 24931111, 9558662, 8697349, -728341, 7645492, -5682798, -24842105, -18607945, -10208952, -43426915, -31852266, -35784936, -18598799, -20641366, -18756098, -2814277, -3676548, -29184415, -23736137, -49069021, -10846665, 2343092, -25900084, -10119001, -11487589, -29568540, -27269191, -13839087, 16038556, 17298284, 14972733, 31346193, 22143343, 24278633, 18147599, 14339954, 4596812, 55222507]
private def highC76 : List Int := [7673152, 7346974, 652911, 555739, -161777, 1042285, 2180078, -1314445, -5128595, -6832768, 108300, -1071176, -2002157, 1214793, -2558516, -16421843, -17494533, 207015, 6422787, 6624474, 664817, 4103941, 5426664, 9914049, 6695395, -3781953, -23576951, -12270854, -9421176, 22645550, 31222890, 30228319, 60383982, -9448836, 97405214, 135923473, 58458605, 47702806, 49147486, 33638364, 20198680, 8267070, 5884888, -26465910, -20142556, -22957294, -24796658, -137541639, -75136163, -123352672, -54959802, -46817777, -5151935, -14183369, -16478925, -20506304, -36235246, -81716775, -44943129, -8837576, -35067960, -33686191, -26365212, -33783585, -33716498, -30111537, 36801315, 31226246, 29447936, 50253474, 56649420, 50217379, 33656205, 16991335, 18834791, 15128955, 76278796]
private def highC77 : List Int := [-29850299, 10702750, 2605101, 3566210, -6098191, 1460043, -333399, 12799114, 8644032, 8422690, 135262, 1555864, 3753820, -12782301, 11288806, 851092, -3845462, -6086915, 10914295, 1809473, 4291811, 9882134, 4013834, 10851153, 13141233, 1245963, -311089, 20954, 688937, 17773038, 25135387, 21057431, 22062991, 27884830, 16508873, 46045699, 20087683, 24455634, 30178595, 22873179, 8292522, -4301262, 3643959, -17782664, -12295609, -11709653, -20448471, -66090730, -36116710, -45941763, -34287521, -18889422, -26257986, -17218174, 13972316, -10904405, -35254116, -58885015, -7931108, -16921285, -25131166, -9724142, -11240387, -11989208, -14713274, -15324194, 17572629, 14623266, 13527771, 33377463, 20398800, 27048063, 19159184, 18311880, 19970798, 11446727, -196604, 57721248]
private def highC78 : List Int := [-44670456, 25271301, 5786109, 7635028, -4311596, -6035679, 2419931, -26059717, -16639698, -8522516, -11053039, -5064498, -12995170, -28372305, 2206590, 7074405, 299491, -1296977, 18203891, 19705574, 11303164, 15615667, 13050809, 7931131, 4542392, 1445916, -488735, 45885, 1731863, 32375143, 26799895, 21128328, 48616452, 33680080, 21308666, 92616996, 63768270, 47294108, 89993015, 7956745, 10423117, -2581072, 26126560, -36311913, -20212048, -15889274, -13527315, -134701136, -98844522, -85776419, -65148366, -73351064, -34418642, -9211223, -7138072, -6832567, -80315289, -110013558, -59424957, -36544228, -44774126, -10422808, -32155825, -13281635, -26508179, -14573728, 30907076, 19376296, 45574250, 79271922, 43046359, 37371961, 28864194, 2279393, 48172525, -14285238, 2375021, 26672110, 105521385]
private def highC79 : List Int := [-36994350, -4851062, 16910178, 15809707, 3197778, 2798474, 5238110, -5967985, 7585874, -20880710, 4969142, -3347861, -6221596, -2476495, 9926935, 3445202, 179980, 521309, 16349343, 11777144, 871606, 21246173, -6151936, 8839616, 11964294, 1337502, -328887, -1165720, -4464681, 16626428, 27477630, 18944921, 36281779, 30197210, 20600774, 40782156, 13942039, 35234381, 16006509, -5999276, 38078170, 22278223, 20457052, -14059892, -11388181, -10539986, -15077367, -61891218, -32435234, -30495139, -19712339, -28081405, -3595705, -26208330, -22079792, -6801868, -48520925, -56927693, -25931114, -15406132, -18679774, -16851618, -9493720, -21114292, -16472407, -10910946, 17667657, 11166094, 14245759, 37896037, 12739178, 16916020, 9232074, 8648479, 10540907, 15606359, 3871065, 6562202, -8411891, 57667554]
private def highC80 : List Int := [-47763405, 30571423, 6819150, 5535929, -1330856, -5926857, -280633, -2357505, 14527648, -2718590, 9190038, 13582461, -4880689, -15667038, 6589259, -5701037, -4746788, -5203268, 29026565, 16546902, 7448145, 20247373, 37816315, 6023411, 26140893, -7089025, -2866046, -11715556, -13052873, 7234868, 38192535, 22997886, 47761492, 50551362, 41651865, 103542777, 18912434, 29404247, 53989906, 23009339, 291434, -7401028, -3329223, -39484044, -28155876, -28899198, -22928985, -133753962, -65409814, -85060898, -52400296, -51326230, -23432739, -31681211, -2896653, -34246388, -77927603, -112998784, -42445642, -39247681, -45168782, -21478071, -25224488, -30212556, -32670312, -32824137, 34677368, 30668399, 19647042, 55547752, 41738826, 21076026, 26442266, 11477032, 39749687, 14375497, 6299984, 24009740, 7142484, 12196561, 59414203]
private def highC81 : List Int := [-3520064, 9854816, 5851253, 1358809, -26244, -643834, 772747, 17642090, 7204131, 9883217, 7954593, 14551483, 1722036, -2229884, 6101975, -7181498, -620366, -456651, 9320440, 10084427, 6607538, 8495577, 15003888, 12444151, 11639942, -8077355, 5677605, 2576177, 4091329, 4732056, 16750556, 7793754, 18289706, 26003746, 22353664, 31463064, 6205633, 20629515, 39603431, 22310282, 14655435, -6158833, -1974169, -10343329, 4046730, 1520166, -18161369, -91047962, -46042759, -33189885, -30392950, -34097505, -26675349, -21749288, -17319851, -35345163, -26935487, -61407938, -47282483, -9800526, -292311, -13344901, -13829439, -7280690, -20920920, -7869432, 9845922, 16189786, 14430409, 23755001, 15291640, 20243068, 12107121, 9373429, 17469510, 13444574, 18437289, 16500009, -3447706, 6992035, 4226599, 69955359]
private def highC82 : List Int := [33368103, 8778997, 179093, -537209, 4347070, 4149028, 3428160, -51352632, -22671885, -34752141, 9435646, -12263936, -24506232, 582632, 7519016, -7466862, 129279, 5328222, 3805954, 7386528, -1778077, 16545373, -8857615, 3481649, 14670307, 2009624, 3081993, 1193674, 2878761, -8953907, 23110244, 15367438, 21499098, 31917364, 11957249, 102167734, 33629513, -9964398, 52981553, 38497421, 24399516, -2866558, 3556839, -24528045, 2857571, -13481384, -70754302, -159540752, -58884359, -69942412, -81972392, -115762120, -60549850, -43227153, -11609402, -65107905, -94221437, -107551122, -49703406, -70535242, -42110059, -26422944, -20612458, -30627464, -33932377, -21864176, 28606853, 24394143, 23251786, 63258102, 5961893, 29821174, 28896426, 9071927, 46506326, 5086741, 2949985, 8764345, 889870, 16631204, 32242598, -20236668, 97491051]
private def highC83 : List Int := [8666183, -2168035, 2841522, 4383080, 2203142, 2905403, 3411800, -10700754, -3508233, -16686523, -12692860, 2235498, -2862517, 3784211, -4217957, 12082667, 3099013, 3685413, -675167, 6069311, -148483, -3054721, 8637781, -19451510, 2965778, 23693681, 4438599, 2197933, 4477085, -1088075, 3123551, 2647098, 4226329, 1139088, 8546732, 52991091, 18511772, -364712, 3056735, 21384118, 13020188, 10135614, -579540, -21807241, -14211777, -12394364, -3262927, -55295880, -43738627, -44496619, -52879706, -61066122, -26419826, -33172449, -8274741, 1495384, -43063584, -64344666, -20810895, -33663939, -35123629, -27232655, -9193020, -6184029, -7696931, -20695864, 13395438, 20163762, 15476628, 5694678, 9266564, 14685823, 14968692, 8626256, 19286415, 3449748, 13183909, 5737919, 1234515, -3536162, -127617, 8328537, -5454678, 65319423]
private def highC84 : List Int := [43133347, 4461766, 2134889, 2471438, 6410167, 6943064, 6691609, -29475527, -41210395, -19670762, -4502146, -1342228, -15484851, 5007757, -10245090, 14979558, 3240997, 6224157, 13310201, 20887775, -6962930, 7525723, 2283985, -29350781, 6005953, 14535006, 9690683, 15737030, 26434312, 11575679, 14051412, 12134989, 17326489, 7052105, 10426481, 86820636, 39899921, 44143616, -7540386, 1848558, 3257222, 4795976, 13645846, -36983751, -47989651, -61387638, -388525, -123373646, -32020227, -93945316, -133400981, -78392415, -70795745, -3513641, -10183224, -48983555, -77637536, -133269274, -59690893, -51019884, -68434199, -56205817, -31050437, -33899418, -13936025, -34665055, 31137558, 25384560, 22853714, 20445515, 17538332, 24768609, 30300137, 31608764, 9866179, 40792246, 29007608, 1850720, -36870204, -7529617, -5171611, 16412688, 13993401, 32586325, 116745309]
private def highC85 : List Int := [-20180558, -5473033, 4704026, 6744330, -397879, -435582, 249210, -667547, 331911, 370496, -3243550, 478913, 1114915, 3828035, 2451703, 188815, 404181, -406994, -5888445, -766126, 1552140, 733087, 4311494, 1892167, 1849697, 16397477, -1787736, -1474428, -2932174, -1957278, 2778074, -8584300, -15192200, 13627674, 14408478, 51253635, 5352387, 8897941, 27113773, -13156082, -1438845, -16944787, -9715478, -5448510, -7060580, -8399063, 4720383, -37257476, -16138708, -60626793, -37984413, -8029288, -4765956, 3158536, -19191474, -6006534, -72667682, -93019029, -28204781, -804831, 19891066, -12435985, -36743365, -40171533, -43017701, -19470601, 29748914, 19437320, 25159237, 218634, -1290350, -16136616, 24416550, -15029476, 3048338, -8653809, -5235425, -17615616, -5547157, 29054300, 11243755, 20956296, -12219792, 17555748, -29150002, 116293611]
private def highC86 : List Int := [-14381400, -16169638, -1518160, 13812347, 1761094, 3128834, 1712626, -2062307, -1865699, -526282, 1050761, 2869886, 4809931, 5188016, 5859897, -161137, 1958844, -168091, -16082141, -2054558, -9048160, 195423, 7294033, 546474, 2688328, -1430500, 1013997, 4039060, 3723781, -8251986, 1110986, -35260, -6339292, 2959371, 7617029, 21363789, 1570560, 12314002, 9093344, 5743660, 2477012, -4014853, -2816656, -2048839, -1557367, -1298614, -788803, -46948108, 10307173, 627510, 1118166, -25024461, -5952341, -9968620, -4104046, -1132337, -33476053, -51321744, -5854452, -8414410, -1459112, -8419271, -2599650, -25185213, -14055069, -17464355, 12214127, 7512838, 9323398, 9546936, 5241665, -7676147, -13672822, 3861106, 4538569, 361105, 2388873, -3525750, 6872083, -5256697, 2983170, -2676567, 8146810, -4976715, -6099642, -15979372, 110035728]
private def highC87 : List Int := [-16292109, -8174781, -2251181, 7629778, 85080, 583957, -2181084, -3958491, 881863, -2097876, -611204, 1819914, 2242565, 3130725, 3109550, -236864, 1377728, 201287, -22384092, -1417178, -1046158, 2643467, 9454294, -3810901, 2423856, -1763962, 1004481, 517213, -1141731, -13371849, -1743601, -2340516, -306551, -591995, -356511, 22081330, -2778014, 8063640, 5844972, 7402046, 2079609, 483623, -3824506, -4025244, -3106765, -3788810, -7787304, -45247533, -4531739, 7834141, 3857754, -26243769, -12171666, -3562365, -1031728, -488702, -32483204, -45787075, -20833273, -3531510, -17311105, -13671007, -2079873, -21109244, -19207540, -15226085, 6701847, 12388469, 7649380, 12393555, 4392641, -13880713, -16329276, 7565291, -2006696, -1940377, -3260348, 2384531, 430189, -734259, -2556689, -4806814, 1769917, -6448586, -2933052, -3122105, -22822230, 111094759]
private def highC88 : List Int := [-24818315, -14477658, -10920087, 13242248, 275656, 6648272, -11483300, 1310831, -3249581, -7257323, 4091516, 5089149, 4570485, 4299629, 9584488, -617810, -601866, -1952979, -22363835, -4964025, 735448, 425257, -833615, -12138979, 6071748, 943492, 3319597, -173686, -3912495, -14204318, -5100484, -2873291, -1989634, 682796, 1817604, 12208538, 1273634, 15728981, 6998857, 15174991, 5569920, 241579, -10811578, -3019157, -4774805, -6273124, 2834280, -38000921, -13104740, 6669787, -3043137, -36117780, -12551702, -2412802, -3655778, -8072560, -1711898, -72576437, -17685704, 9475534, -6598798, -1539463, -5045715, -22743495, -13881309, -11269783, 18196725, 9385203, 3906176, 9592053, 3034322, -12120864, -5963981, -1149138, -819615, -1986572, -5852164, 2234959, 2107180, 4878808, 9983248, -12790585, 4084251, 947627, -1587832, -19003416, -30784131, -46955939, 114451940]
private def highC89 : List Int := [-21116827, 23356346, -12363973, -14436120, -6389539, -10851787, -3889689, -2708987, 1048883, -1486026, -7757158, -5938989, -10617426, -3167729, -10849765, -664316, -3959112, -2673967, 776274, -220145, 1767742, 1342356, 4411122, 6689184, -5243660, -6514441, -3520381, -5466637, -1449240, -1241122, -8516667, -4768071, -8364432, 386909, -3848203, -18645308, -11404105, 7400523, -8083521, -3132490, -1870834, -3322003, -2953336, -4301468, -4151020, -107469, -12646508, 8260428, 2258877, 18552340, 2968942, 2760006, 29426022, 44611050, -1022205, 7313085, 26045677, 30628071, 39849320, 2432129, 15411046, 3285271, -2731674, 20299676, 28512276, 6539661, -21249758, -7167369, 3413622, -13111807, -15358627, -4581151, -17707934, 3720041, -2657872, -8463025, 10378197, 11049800, -7399987, -446653, -8508910, 11373975, -7920799, 135585, 1511283, 4374187, 7113032, 3555834, 9784815, 109287825]
private def highC90 : List Int := [-13156533, 23802178, -12298310, -15012469, -5246458, -9554826, -6685799, -1821115, -1756167, -1187351, -5365704, -4373644, -9147942, -5049607, -8513488, -453528, -3201627, -2067192, 1577805, 1809064, 3731462, 4321427, 2982831, 4785452, -3359841, -184985, -2851853, -4486576, -481624, 731612, -5579318, 16369024, -6590115, 1960400, -7363366, -12832728, -4911301, 2489941, -7838243, -2707334, -2752925, -2475202, -1928726, -2065275, -1267237, 1595716, -5900127, 5052842, 21238534, 18519746, 11611987, 21811342, 29553278, 11452110, 9093367, 15352493, 14976132, 32653635, 11496538, 22211181, 24912150, 12931716, -2402427, 9885498, 27833755, 13580507, -17464197, -5171788, -4621465, -14707628, -14696466, -13203089, -12752910, 1933564, -1170518, -733851, -2955976, 7601048, 9772324, 8544291, -2831399, -11638199, -1614621, 3290379, -1798626, -909317, 2038680, 1326380, 5293928, -27411139, 94938657]
private def highC91 : List Int := [-14321069, 1645036, 14678674, -1115542, -2695470, -1700008, 5323944, 863217, -4036260, 548114, -4979598, -4639695, -5784798, -2970789, -1736955, 1223579, -2209880, -3416202, 1310948, -633396, -2484876, -3368839, -3559058, 1174661, -1860199, -95074, 60366, -164983, -1482195, -1170455, -3201978, 2754586, 794901, -4458769, -1125210, -15110468, -307772, 4097375, -2040153, 255514, -3802528, -1770173, -2954839, 3452777, -1166570, -295872, -5304467, 9508884, 2077254, 26840435, 5693621, 3287243, 39826623, -1415082, 22266150, 438404, 11585088, 37966665, 18968605, 2510625, 32061136, 25140496, 3958047, 18587327, 11260134, 24895814, -5585548, -18189608, -21771112, -26002195, -12350708, -7850734, 9616304, -1157848, -4472729, -3788410, 6509933, 3153902, 4440049, -11396972, -5436711, 4138931, 10953157, 8511490, -12403346, -3767408, 311358, 8207938, 8934486, -5379290, -14294039, 97455488]
private def highC92 : List Int := [-26906843, 27475579, -10179745, -13230079, -15181941, -9488100, 13609796, -8824861, 190676, 7672616, -11814161, -14832307, -15632018, -30030390, -4454587, 6946368, 3029942, 1374003, 3015058, -2429512, -3533169, 45907005, -36141230, -30904813, -4330421, 5010671, 5381730, -6080123, -2540710, -8169897, -11676844, -3142203, -38757, 10262974, 997175, -53400137, 1439422, 27888028, 9891000, 4572790, 1254720, -14213862, -22630881, 4736995, 17895683, 11730313, 13529413, 31915441, 65576461, 78312758, 77968940, 52561895, -31397335, -20087849, 32602603, 56148408, 110029628, 166453996, 51678048, 15362188, 28904828, 28627109, 60307558, 118659304, 70400486, 33439842, -44403914, -32985468, -57398998, -72098472, -75427895, -13472035, -9469639, -40522779, -3874067, -22602875, 13244582, -11398596, 16172522, 473763, -7187669, 11046478, 2328056, 3621762, -10066642, 8305152, 774931, -7690561, 21217431, 3326726, 8253300, 4316499, 147535080]
private def highC93 : List Int := [10037166, 18822946, -8294091, -10213218, -2138262, 2296801, -1705916, 9881168, 6727733, 5261201, -915359, -2285233, -296389, -5358801, 419362, 1227854, -1459762, 358234, 7238735, 4197627, 6347715, 16395975, -22819280, 2798610, -12267964, 14411844, 2293697, -8304360, -6465084, -4957473, -3276775, 3766549, -832722, -4241043, -4912034, -45589402, 9640650, 7496429, -2668658, 6840596, 703888, 1234555, -4313720, 4021649, 5427742, 7699904, 10532562, -3453482, 7269278, 25895016, 60015503, 17431070, -17042572, 32042370, 10797699, 6523930, 48283401, 77432056, 64715232, 20879633, 13958092, 16622783, 4438153, 10710387, 52566815, 32958081, -37270016, -23781992, -13966647, -39281727, -39173285, -8549980, -21011644, -4233134, 3855305, 3287190, -358451, -3463192, -2565398, -2335560, 3428041, -6395094, 1407913, 12524013, 10067991, -8435939, -6392304, 2288570, -5648090, -737819, 7989539, 5941373, 2972083, 62766392]
private def highC94 : List Int := [10112992, 31165103, -13596114, -15851122, -2640408, -5185767, 15169460, -8790306, 3314157, 18523508, 2139523, -15261229, -11416869, -24567810, -459558, -17741908, 7644230, 9176998, 1366075, -3097015, 9448126, 9709503, -32514999, 6076198, 21208244, 6322809, 2379099, 961597, 5490215, 3562382, 8634394, 5798207, 9288857, -24050883, 26034083, -78526559, -25856198, 31890464, 868133, 13339598, -10991634, 3881574, -3914786, 16619648, 18433989, 11284959, 17056129, 71220625, -26313707, 31550849, 22740945, 24602966, 4389035, 29642795, 37601128, 32399172, 66507685, 179758535, 87630714, 40958418, 63615029, 20248471, 60406223, 33703076, 33807426, 29976111, -49010389, -34155313, -40568201, -68996923, -88673475, -94740689, -73726819, -5596980, -20273076, -16925163, -6493524, -5623298, -7481142, -5795794, 7339782, 2955746, 10492824, 6768370, 976931, 971403, -3151849, -1839188, -2471396, 77290, 3981868, 2342040, 9320112, 12403608, 78643662]
private def highC95 : List Int := [-6776348, 7467355, 1250924, 1544357, -445160, 2641152, -762745, -5460643, 152309, 1791400, -1480358, -508207, -1451920, -237268, 1431627, -1017428, 1711665, 865199, 6950277, 7373240, -3367353, 4197501, -1005179, 4538876, 2904347, 5735346, 1129626, 224271, 836213, 5882758, 10099205, 6968583, 8902367, 5113026, -7384292, -55733399, -5921675, 17966742, 5758580, 11445777, -3370308, 456918, -1328085, 7037718, 4223634, 4484493, 8042235, 20481944, 14302213, 23878994, -11386296, 3987882, -2035865, 8110866, 12705592, 13727740, 45577476, 86931177, 53107764, 7903873, 26820051, 19437545, 14627916, 16096622, 19642297, 14220559, -25528350, -21320309, -15711566, -38818774, -37909004, -38604338, -24383749, -13744166, -10412751, -12486046, -32745524, 918437, -23620, 2796852, -2226926, -3907197, -3879773, 494710, -7318665, 5593147, 1718344, -267926, -584749, -840853, 2232402, 574980, 3882899, 5207228, 8153218, 47004441]
private def highC96 : List Int := [-5943837, 15221671, 2220590, 2606274, -2831, -1319206, 1853652, -19407344, 2537365, 1012260, -2415163, 276274, -2798419, -20429841, 8201893, 3983296, 7640863, -2484042, 13106843, 6734539, 2330972, 14355322, 2752416, 13676141, 11166019, 107605, 7627983, 4673897, 8105514, -2345917, 13917269, 4948632, 7443862, 17757236, -21800306, -82671801, -25475701, 37023974, 1101688, 17857807, 3392693, 15058986, 9062500, 8590638, 17900386, 9954904, -4757863, 33327374, 27494638, 40204412, 8593242, 10388460, -7352910, -2142134, 13881408, 26624327, 70037908, 195130565, 63761474, 34308910, 72884770, 32652353, 25705711, 39722821, 46608222, 35085940, -45762167, -39866152, -25239649, -90545379, -56398892, -78890520, -67221606, -33233948, -30867880, -34668640, -25449169, -18666850, -7585123, -6108779, -6650748, 1915665, 2447436, -3536170, -6691109, 2436178, -1410541, -5988461, 6212810, 2321536, -332390, 2678615, 18132377, 727942, 15719454, 5052230, 52789660]
private def highC97 : List Int := [-1270880, 1127580, 1441450, -1669826, 3403187, 1601950, 667382, 425435, 2809184, 1378106, -379884, 957248, 1404741, 987292, 2223021, 260193, 1089892, 716825, 3164263, 3106929, -849880, -13032140, -19038088, 14088201, 19070265, 3803578, 570204, -322474, -413433, -1315231, 3822561, 3964772, 4548147, -6221209, -4253282, -27317331, 6519802, 34038509, -2474762, 11352470, -1316311, 3746036, 2603430, 11027205, -3866514, -2745972, -12986089, 9751653, 10069944, 10621343, 21526577, 16658521, 19180422, -6294490, -5239555, 49256911, 40592249, 99163975, 31099534, 15916570, 19731525, 25147170, 11096869, 24925523, 20552001, 24717202, -5320950, -11736762, -11111896, -34050866, -23488330, -18733951, -21145840, -3179988, -45248543, -13036373, -14467077, -9483565, -54502, 209041, -17910445, -18338219, -14833876, -12560372, -5732528, 1243777, -2476786, -4467616, 1219646, 6731042, -173003, -2826513, -2822030, 1827810, 6026217, 3966167, 1089231, 61617193]
private def highC98 : List Int := [-19588983, 5251000, 1502182, 2107253, -2016590, -2715439, -545512, 5990763, 3445379, 3554439, 1812132, -894291, 1599401, 835111, -6819655, 1520589, -1730327, -11099010, 3606911, 399700, 4213469, 5125685, 10096454, 3125810, -2187899, -32599822, -17571330, -7409225, -12587477, 4824174, 3383758, 745304, 3509785, 7236702, 3549911, 5525749, 17263146, -5774186, -6802681, 878787, -4128884, 160260, 9053542, 3874760, 1208326, 4786928, 5503860, 37781960, 14573395, 14785047, 5709549, 26919900, 2532100, -5052215, 6563047, -20318493, 143443047, 208587678, 91793239, 81013597, 71100636, 45266528, 33382933, 19565950, 28006662, 21300366, -26094142, -15448335, -22447305, -91328889, -41327055, -62747663, -57703381, -16440761, -67106465, -21388752, -31102525, -28142917, -17538741, -19568248, -26030268, -6236633, -28681835, -8525169, -17896289, -1310146, 9106633, 10311743, 11664928, -56491, 5252600, -1484989, -3081535, -6706632, -1268996, 14313369, 13390983, -1010901, 72087010]
private def highC99 : List Int := [-14267100, 52891, 2235668, 2841242, -1059344, -1248281, 6682465, 4859099, 2526394, 2897918, -3666040, 5175545, -726950, 353730, -5089518, 1464726, 58066, -564598, 1783132, 967242, 1799852, 1220382, 2162620, 1968748, -14717199, 2568800, -363759, 848007, 1082192, -762262, -2731972, -1284209, 28042599, -2948235, -7586121, -12344125, 18766515, 5977714, -4927290, 1908260, -2573095, 6032549, 1527259, 3972456, 6516269, 7762106, -433991, 11164654, 7081392, 3879253, 8937525, 17584021, 16331655, 4832531, -3452126, 10006489, 47226720, 85064766, 57743774, 31573158, 32501247, 22796419, 17695835, 17183312, 15785640, 12968173, -12530085, -17599294, -18505811, -36516495, -19474058, -13511652, -13969188, -15442749, -6659032, -26501913, -14462567, -22172208, -13646290, -15853917, -16002276, -28144665, -6043942, -14819509, -24980836, -18881993, 256013, -1480606, -5034086, -2443818, -14786573, -9188755, -3113077, 6460558, -7867501, 535147, 15050025, 9162157, 63475, 75512425]
private def highC100 : List Int := [-5773891, -362294, 745677, 978134, -438887, -1301805, 2161887, 624104, 371123, 513071, -1612334, -929658, -290342, 1035682, -1168141, 212642, 48342, -91691, -76749, -132186, -98292, -235541, 859177, -1392592, -2165426, 723516, -80586, -96751, -338804, 12599760, -825720, 4748476, -3517585, -2886781, -614963, 1135986, 1010733, 922968, -95317, 1540560, 209903, -1843689, -1182129, 957708, 1896387, 1674763, 3877505, 3839181, 1288476, 2700704, 457723, 3883468, 1535069, -7408023, 5036461, 2656157, 12688890, 22161400, 14357788, 8716224, 9393192, 5997808, 4840394, 3654472, 3300903, 3990205, -3519380, -9273271, -3595064, -9158473, -1015396, -3998026, -6676420, 1151284, -2018261, -6963122, -1485980, -6990820, 478574, -3693052, -6669409, -5175314, -4318355, -2465555, -3227350, -3910723, -3434849, -831137, -1668752, 2750813, -1026180, -5991968, -3156286, 821748, -1689454, 729951, 3571533, -2303752, 2464887, -2655011, 52150444]
private def highC101 : List Int := [-11156050, -4246012, 3648054, 4374933, -357620, 113749, 3477673, 995422, 12789, 918117, -1489418, 1804118, -17121, 1826141, -2276959, 597432, 339826, -375739, -507842, -667824, -191314, -826389, 688081, -847042, -9079614, 868016, 5094, 691889, -314260, -1429475, -2330341, 17574814, -1631739, -824895, -1798192, 3212953, -672957, -1095845, 1186298, 802273, -881616, -1162356, -1570649, -14141, -1730939, 1765569, 6700153, 5403174, -1247485, 777873, 3913748, 8928911, 2406118, -648052, 513143, 7669109, 31231293, 53989679, 21796629, 12750551, 21645414, 10068847, 5998981, 5313612, 4867715, 7144718, -12922201, -7461320, -9580121, -11692910, -2966871, -6864569, -8551721, 2847317, -21491360, -6300166, -11895596, -3433688, -7695854, -8513727, -11192032, -12940628, -13338312, -7979769, -1199799, 407062, -275742, -909610, 553504, 3548985, -8006580, -748092, -7353, -1670964, -2060548, -2346949, -1236942, 13671528, 5650411, -4247336, -12030905, 66509797]
private def highC102 : List Int := [-12039310, -609390, -2540979, 2271539, -930431, -6001344, 1674852, -887856, -78622, -152357, -421317, 4567223, 291152, 945848, -8048097, 865078, 302839, -126977, 597944, 163694, 1145458, 238418, 1995109, -33235, -7355230, -1195456, -1393228, -1418379, -2311460, -1327091, -2156279, -1224211, -397807, 1615842, 1891535, -12488639, 15014092, 9157189, -381351, 5705931, 93675, -720932, -2284293, -1117019, -4281240, -4517248, -1622754, 6521906, 2650787, -12083691, 2314484, -668370, 3356246, 12873709, 3549901, 8600836, 13207195, 49952028, 21493970, 18501740, 14808914, 17498765, 11313789, 13741617, 12723398, 8274753, -10091519, -9560251, -8690037, -9630998, -9114555, -3819500, -81639, -6658766, 1826554, -18976336, -10587283, -1392162, 29995543, -10706382, -13522338, -6514816, -14184486, -4872402, -3210009, -11851491, -4755200, -1962283, -4332145, 533537, 818626, 196927, 8514834, -6908658, 560486, 3456060, 7463745, 8599306, 12186612, 6297868, -2467515, -7900511, 53883842]
private def highC103 : List Int := [-15847996, 736678, 728411, 950902, -1944233, 5155904, -2054498, -1671671, -663685, -306985, -4154988, -3107513, -4199158, -21854, -2094399, 1151138, 1657805, 258160, -2481515, -2543644, -1787269, -1833775, 2239628, -1570984, -3404862, -492791, -10655, -419034, -347191, -2649532, -4323418, -2984861, -2639048, -8133132, 1389147, 5038030, -1374329, 1463201, -173808, -109461, -922397, -923308, -2647713, -1980465, -788066, 2232364, -10903, 6539858, -2534030, -578847, 1294072, -13525839, 3919274, 6149118, -487710, -15151170, -27409135, -37828015, -18779497, -20930927, -20214868, -15896854, -15731877, -19471004, -15556615, -13792925, 10993729, 5225092, 4191763, 12392564, 11474709, 12049171, 2468244, -2967329, -9960677, 13968878, -2496143, -7107369, -8981167, 8548268, 4173370, 1462574, 7549959, 19308505, 14926464, 9803220, 2621762, 999996, 3117719, -9603283, -6197012, -3710855, 2164094, -5139655, -2829566, -1339719, 4361096, 407942, 2522640, -9713125, -3566525, -2235784, 9242845, 73383400]
private def highC104 : List Int := [-8436268, 462483, 393738, 403453, -1106556, 2589647, -413755, -682260, -350936, -34112, -2556796, -1955051, -2392072, -160975, 903736, 146947, 728148, -41313, -1356514, -1192117, -1181819, -997399, 459642, -591805, -237, 9578, 153814, -180244, -147423, -1090299, -1716667, -1294944, -981200, -6747271, 834144, 3662252, -1490497, 590230, -6407674, 1662773, -879441, 2224456, -402599, -466343, -1659738, 473697, -2519330, 2479985, -3795208, -277918, 918557, -7689572, 1241193, 3371893, -2126183, -4986306, -12711187, -17618616, -11185174, -9450600, -9621113, -10158788, -7405772, -10042042, -8590024, -6568915, 5486506, 4847591, -639422, 3514612, 4644164, 7485265, 4960137, -2955924, -4746379, 7265251, -3048039, -2029464, -1852739, 2634767, 3470102, 986865, 3133099, 8569435, 6338299, 6310053, 1824085, -312781, 1269139, -4383090, -2928000, -2250971, -33476, -1730594, -2910207, 86020, 1654957, -4658514, 993128, -465709, 954961, -195999, 3314964, -5585663, 60712055]
private def highC105 : List Int := [-7960732, 371158, 468175, 463128, -1012094, -1140602, -3048028, -3656507, -2004805, -931345, 223362, 85287, -1421744, -518619, -107371, -597560, -249287, -672727, -1001472, -767116, -353057, -234559, -521487, 36113, -822033, -920676, -316480, -609413, -1125474, -693880, -1463354, -971206, -584571, -7524418, 855147, 4095135, 44874, -1917990, -1121511, -930713, -650583, -655945, -1991405, -1273645, -2119259, -1569519, -1501394, 980483, 8835027, -5201904, 795959, -3135175, 287371, -2878226, -5205979, -2659239, -13877755, -19855393, -7179233, -10558075, -8006363, -8921963, -6601303, -10012730, -9623861, -6591321, 2558849, 476735, 4676111, 8980705, 2466859, 5497008, -542747, -1062218, -1547052, 5114232, -2518771, -2964704, -3706005, 2493717, 3026720, -5252984, 3767435, 11504407, 4471478, 1911560, 282109, 456816, 1830680, -575969, -821136, 2472702, -1833792, -2333078, -1551060, -1103489, 1943411, -4863654, 4110346, -3796261, -1131473, -1136116, 1490671, 2450311, -914974, 59239020]
private def highC106 : List Int := [-18097244, 1245469, 836268, 1332003, -2047069, 334791, 1388766, -727238, 251131, 744330, -4207399, 1652351, -3501707, -471483, -655530, -36356, 253170, -923018, -500257, -628142, -612017, -11964807, 8761942, 1324498, -1902041, -188710, 49061, 563815, 891651, -2838122, -3355534, -2931444, -1796883, -18227046, 3029273, 13434852, -5262623, -1595643, -5808016, -3920252, -4844554, 649478, 170313, 730153, -3085753, -2068835, 12471817, -3259042, 14248325, 442643, -8874732, 356224, 258179, -1057069, 5722671, 5444486, -41049572, -56689413, -28068922, 3612076, -41127982, -32635326, -28418873, -27305009, -26372074, -16926935, 11315112, 13297977, 17101163, 22777482, 15064437, 6144589, 11215998, -10933243, -3897179, 7546074, -1392462, -3042193, -9155850, -6337885, 12438251, 11627080, -10868614, 12302877, 29810070, 9331381, 8816555, 3084009, 12550272, -7231764, -14702713, 2146869, -6321385, 857441, -16110127, -1303602, 1211782, -11127636, 227877, -10904737, -6101856, -9341615, -12909915, 9587335, 3598171, -3782903, 66581445]
private def highC107 : List Int := [-33605425, 4222648, 1909677, 2871981, -3686246, -1663771, -2489403, 1588096, 1181092, 1373098, -2932576, -2482600, -2206346, 1907072, 969511, -1024482, -1224331, -2572499, 551648, -40602, 2136307, 3472052, 7238429, 5060348, 2069200, -723892, -2393660, -3677316, -3710032, 1555623, 1955111, -8665121, -20895553, 17819327, 16709100, 24005766, -19372728, -2415116, -11160691, -3930296, 76465, -4142091, -1756479, -4300567, -2739752, 1376856, 5112004, 17517190, 7367995, 12355332, 7657069, 25532684, 620230, -5478919, -13656987, -8465084, 7877294, -202377007, -64462211, -21017644, -73668045, -102166169, -62492618, -81918721, -67604729, -38688019, 54572602, 39934204, 45328713, 58947489, 74717262, 35234785, 3638936, -2945132, 15851837, -25824607, 16575187, -2074597, 25399252, 7145459, 10052245, 1481354, 23661627, 9849199, -43258436, 16650786, 31544012, 26288474, 13907497, -4229826, 2121599, -1673374, -33529821, -29478283, -25728550, -11650233, 7410418, -38412391, 22826774, -14427430, -7234370, -15275424, -2150798, 32163770, 26337536, 26651200, 8707290, 121069413]
private def highC108 : List Int := [-1144502, 3296991, 478177, 557445, 16637, -266192, 331973, 5825188, -352601, -14955149, -781700, 2744321, -2452602, 865620, -3997494, 1726241, -4617680, -2154694, 1789383, 3099596, 2315086, 2952769, 2241996, -15996101, 3551941, 1377298, 2171396, -1531104, -1675375, -1050693, -4634985, -4137433, 1963642, 3626554, -4307443, 10896998, -14624160, 5371453, 7918972, -5525652, 3055269, 4527902, -2098485, -6935469, -5209385, -1364513, 9940295, -1982745, 2209662, 9905087, 10243316, 9892486, 14820774, 9187677, 20573716, -8785992, -21899503, -75853330, -36175695, 11301774, -27111558, -87710564, -43728770, -26918391, -25484252, -13333985, 25826910, 25802434, 29922379, 30665629, 22955252, 17089331, 18576539, 4345026, 12484249, 8013284, 7369875, 11713944, 11905017, 3729916, 16008037, 153038, 7899689, 485371, 6940453, 10355310, -17028424, -6339257, 8450524, -15521995, 2327088, 7334378, 14524919, -163671, -1804210, -11916435, -5470368, -9902450, -12546719, -4287627, -4551371, 3918744, -6087456, 9123164, 1220609, -2487160, -413332, 9708591, 65168220]
private def highC109 : List Int := [-8775732, 6100168, 1153476, 1478462, -737288, -1354630, 206015, -2069448, 9572805, 6340444, 1878355, 1071178, 2963494, -1457826, 2339364, -823688, 1329811, 1007794, 1358211, 4264211, 8755742, 9783461, 9872051, 5912352, 4988318, -928668, -949777, -11682, 213237, 9194726, 10391312, 5516536, 10289035, 15062220, -23948508, 22918403, -16387313, -32085475, -21892348, -9175407, 4130918, 12565581, 13669601, -3835131, -273748, -1325210, 515041, 7878033, 4254898, 1951047, 14515724, 24682640, 19798127, 6456741, -12554558, -12135214, 1122788, -128663711, -108229464, -93719716, -67304462, -113451357, -55610056, -49603675, -57354732, -44820098, 52476388, 40783011, 54228796, 79592724, 63484545, 61805313, 41233345, 16347069, 21663582, 10623060, 26344238, 11603844, 23190714, -33103, -12613051, 9869956, 13528273, -10224297, -3656940, 4408518, -7999428, -4327927, -16264432, 848647, 7103606, 6398310, -6811059, -8588127, -25109373, -6488272, -19320316, -10461324, -11726177, -15155711, -1561206, -5393108, -13962872, -12292126, -11021615, -10320763, -5720894, -9807384, 12889495, 88775552]
private def highC110 : List Int := [-13280912, 2212782, 947666, 1351517, -1342583, -1765459, -500157, 1860943, 1160189, 1232759, 4875053, 12988676, -1866091, -3787266, -1290595, -1487722, -2850886, -2742245, 2256980, 1283360, 2604170, 3579038, -949272, 1523382, -2644651, -6766467, -107015, -379554, -1608622, 1789376, 539905, 837026, 2525993, 3986521, -7945577, 10336410, -3607053, -1654713, -1628925, -1201327, 1548901, 697322, -494075, 889026, 1841379, 3296649, 4076551, 11676167, 5922631, 5009875, -5604985, -2798374, 36249752, 7699740, 9418713, -6969448, -9951241, -47248014, -79787534, -32054375, -43677675, -50506134, -28265349, -42553008, -22050961, -27195338, 13745780, 16803357, 19117516, 36771550, 33842587, 30421569, 21766919, -1999687, 20374185, 16629841, 6902869, 20026590, 7665840, 4488787, 17964585, 6762829, 2229716, -1912255, -6761746, -4269842, -3981650, -9379299, 12317324, 3686106, 5306436, 259466, 15111130, -16656693, -7577906, -4286021, -7967856, -14730946, -16397919, -19542250, -3598098, -9352944, -9862788, 10143478, 5412873, 7344146, 6728736, 4815373, 19727180, 3276482, 61202210]
private def highC111 : List Int := [-8106436, 972040, 532551, 1425877, -1398899, -1509376, 97356, 4182045, 2453809, 3701785, 1079932, 6722780, 1331730, -1388407, -1662663, 19190, -517266, -912284, 661108, -29226, 1656930, 2008315, 2357953, 1040013, -2033246, 64569, -514143, -124988, -274762, -46750, -522043, -326790, 1311182, 3427183, -935362, 5104221, -9166681, -17694, 786912, -1169914, 2938359, 1080683, 803467, -2134768, -1864742, -1575485, 3321863, -2065078, 7170996, 7887973, -4301326, 1038815, 4370325, 7060782, 5299450, -404916, 4168703, -36166606, -4157345, -29665558, -24049885, -23208698, -23533615, -18906773, -13055890, -10968935, 3068067, 6235465, 13197425, 22873857, 9472996, 10531353, 12968311, -1085707, 10760524, 8790264, 10614539, 6855880, 6626598, 5663652, -427730, 4104168, 2514711, 8467354, 17381978, 4210590, 1268238, -6278619, -9173580, -1912896, 9519653, 688066, 6427611, 4089470, -8870974, -1004542, -3269062, -12974421, -2131621, -7298850, -3873309, -4234671, -1782603, 2273512, 2209684, 714162, 4573740, 3046130, 1161793, 10664015, -9084078, 51663681]
private def highC112 : List Int := [-10311232, 780676, 605313, 915564, -961421, -886047, -526716, -152345, 32575, 4354056, -1648943, -294496, 262761, 702868, 1107736, -613578, 586564, -589294, -1081999, -577892, 1353391, 1262693, 2262310, -321315, 1347670, 44350, -405769, -640915, -1025228, -329650, 172688, -299454, 1262071, 1809706, -1419418, 6383795, -7692897, -722489, 2836084, 5442210, 5538411, 3066374, 4651936, -1038306, -259418, -5868186, 4104039, 7473945, -1855837, -207633, 4993665, 4280977, 5535678, 7240302, 4107523, -3282093, -4699976, -24038110, -15666748, -21239805, -15220705, -25935256, -26153736, -20534993, -18423389, -13055780, 6172124, 8903374, 9376389, 17613032, 12791174, 15444736, 6692564, 1632710, 13157465, 8677152, 13709734, 1948112, 11595245, 8080247, 13568376, 7803008, 8108392, 1871843, 5076803, -5319926, -2218025, -3659447, -4908611, 3853607, 4677457, 13339099, 5368666, -587617, 5131561, -1674940, -2036772, -9080397, 6293579, -12636119, -5109582, -8743576, 3919471, 5892019, 4924362, 4746524, 3699075, 3888450, -971518, 5846967, -13096100, -2862219, 68253997]
private def highC113 : List Int := [-11336008, 632167, -138306, 1103026, -1100147, -1482203, -378126, -1689911, 3273633, -28864, -1053397, -540643, -437369, 403663, 2496192, -1099445, -318102, -346775, 65404, -535075, -1538541, 399269, -1850697, 1436302, 4186034, -113548, -425616, -897423, -1460905, -905069, 401591, 5546, 583885, -262117, 1244425, 4731366, -11769224, 1659470, 3116712, -3045801, 591239, -3425961, -576884, -9389390, -9311948, -5079366, -2573123, 1959532, -10076991, 12290953, 7971702, 6651283, 1098958, 6713216, 6652247, 3647519, -2199290, -29045175, -17702277, -20925294, -28599116, -23112282, -29707221, -21771992, -19653188, -12445636, 5854087, 6348679, 8870741, 15424138, 3239654, 12247917, 10399999, -2963959, 9487338, 7731805, 7656559, 2811745, 6188859, 3025839, 7596900, 14872104, 9505852, 8040261, -5184697, 6740553, -3743211, 11203362, -4378546, 529197, 5316628, 11874677, 18323620, 1018333, 1223664, 3068861, -10353978, -9872007, 1866229, -1574488, 607204, -2365755, -3305813, 4533258, 1621629, 5688648, 10233900, 7520580, -9907498, 3852819, 3213678, 2256195, -7120390, 65482359]
private def highC114 : List Int := [-19106846, 533373, 1114488, 1073111, -2388783, -2529645, -5422648, 9787267, -8734819, -3988829, 330519, 113667, -1105545, 2315780, 92996, -437513, -4820388, -5496288, -1555881, -1210708, -676752, -559858, 726811, 395224, 266422, 1567359, -1504240, -2582859, -4155779, -2898698, -2017494, -702882, 1214781, -838163, -1776711, 327952, 4924016, 1856044, 1600248, -379027, -2908529, -2979646, -5055405, -1206005, -1982545, -1251000, -351094, 7174476, 3462404, 2180734, -732947, 2096386, -2771629, -4355169, -10340057, -13401884, 1731642, 16887020, 13803052, 20393341, 17757106, 33440858, 28627342, 16976707, 17410017, 6885516, -12430031, -11606515, -17536996, -6155333, -10906876, -5230413, 5420040, 4024720, -1710591, -2170880, -8692851, -7638124, 4121140, 2887977, -7214122, -6974723, -2344574, -31427228, -16056463, 93465, -1313051, -832477, -5411428, 125954, -7134891, -15558722, -12440464, -286051, -8094257, 5039539, -1710447, 18615552, 6576159, 22269158, 2938493, 9746140, -845870, -8816562, -6515021, -5932109, -8360145, -678581, -5965953, -23165268, -5912397, -3852766, 3325182, 9342763, 70688132]
private def highC115 : List Int := [-16645347, 1757069, 289376, 233734, -2379769, -2520577, -1304773, -1645900, -1783732, -998159, -2572603, -1269142, -2831948, 864704, -2615569, -288647, -721808, -1149943, -1326878, -1279621, -479514, -756360, 1605779, -136971, -2416208, -690244, -1146148, -1628098, -2209084, -2065077, -2937448, -1700511, -1586204, -1191428, 473586, 2324567, 1930500, 1100929, 218119, -1202795, -1829527, -3303558, -4154723, -1142162, -370014, 170393, 2419460, 4625831, 1614910, 3904105, 2027984, -552232, -1459815, -748086, -11914374, -6118367, 4136055, 7649534, 15009137, 7035154, 32078005, 30868625, 32396283, 21580913, 18566205, 11987184, -8209474, -11533845, -9652527, -15119975, -4133305, -5603035, -231343, 9282938, -2223499, -3602088, -2440492, 1114917, -2510100, -486555, -8450999, -13473076, -15744043, -13181821, -2156870, -17368972, -4727707, 503495, -9250755, -5468804, -10527883, -16301315, -14029300, -3640579, -2137806, -337155, -3682226, 8466487, 10564442, 22013990, 5185782, -860046, 15380030, -6309334, -4899185, -9730549, -8044360, 4737853, -3240927, -20047467, -4488199, -4154679, -9690407, 11598141, -5432800, 66724697]
private def highC116 : List Int := [-10190518, 1057791, 625372, 706555, -1160051, -1391197, -1002554, -457274, 71629, -1016343, 800195, -781171, -1303284, -303320, -6087537, 1192834, -328216, -373111, 79983, -1059602, 162245, -42998, 4283735, -660647, -6221653, -1070795, -824395, -497314, -784699, -626813, -2516789, -1618837, -1227344, 1419415, 848769, 2743790, 1477297, -9475633, 1975983, -1586481, 637167, -1444685, -529819, -4680207, -15068, 566867, 2436630, 2385106, 5446072, -1984171, 27103, 10641221, 372465, -5491697, -4173806, -8515166, -1587333, 8863274, 7808297, 19053269, 15839502, 35034857, 30434814, 24661684, 19873817, 11412761, -13997071, -12870400, -12963896, -13717290, -7902249, -11288665, -6979219, 11937144, -1995774, -6922237, 1811544, 157892, 209192, -6620489, -3756361, -14585072, -3129567, -15802252, 9152061, -16178594, -7966107, -987048, -5866750, 1618808, -9670415, -11563165, -12347783, 133486, 591675, -13121966, 1757598, 1759470, -7780707, 9875122, -411953, 26189001, 577294, -10739726, -6132747, -9668267, -17995087, -12490392, -1590983, -5594817, -9705355, -1646163, 2886918, -10114049, -4227769, -7186493, 61664151]
private def highC117 : List Int := [-38709946, 3836008, 2065052, 3158367, -4292526, -5149557, -669380, 327103, 740197, 872613, -4027736, -3119801, -2888102, 2885170, -1257237, -6260617, -2869384, -1381507, 2685100, -806602, -154319, -4922043, 10503456, 8633506, -126203, -2508752, -6079856, -5164856, -6259495, -10700489, -965328, -2026541, 5644496, 7624206, 4085571, 18548376, 11512172, -3536629, -861265, -7919080, -7315392, -7516238, -4686780, -2997151, -1118728, 1988318, 2591600, 25111893, 25250797, 22431137, 10119871, 11038379, -133418, 2588863, -25591749, -4439412, -37953269, 45446337, 20221095, -15239061, 56616806, 142429020, 128880722, 94963206, 78546581, 34310989, -51699246, -52523050, -52586594, -54863527, -45016890, -40974774, -19377990, -6662933, -24628222, 7874974, -16854460, -6072368, -8907241, -1580527, -24265925, -6081250, -49272077, -19242031, 15163095, -5747762, -9228072, -8325000, -6956753, -4382357, -7828131, -13483876, -15946640, 16301684, -10541464, 13542914, -13889543, 19532223, -16561836, 8904985, 4176219, 8081198, -6188649, -43435308, -31240961, -29960760, -13556930, -90320911, -36923463, 9816526, -11878127, -1338810, -19964815, -19875400, 8658070, 1264447, 7360313, 71488338]
private def highC118 : List Int := [-23156700, 1633569, 1148707, 1792991, -2597648, -3056856, -1220474, -1370440, -381873, -333526, -4050381, 572252, -2216214, -21342039, 10218772, 5047729, 2823701, -1293544, -3583905, -4752922, -4776508, -4370838, -5529511, -6399794, -605383, -108052, 2920476, 4813612, 4823266, -2152589, -10183796, -5097426, -2789506, -9953452, 1166916, -6271273, 4950715, -5146616, 1066938, -299809, -1442079, -7255521, -3482127, -4915674, -4767910, -3701327, -6959907, 4128755, -2457039, 280287, 2283836, 731895, -7761969, -10935792, -2631578, -2076184, -55040923, 35950211, 22429820, 25782906, 33219151, 54905884, 35171889, 48630825, 36159587, 26448156, -32818586, -27357702, -35627462, -37647167, -32193472, -14395368, -5432254, 5878081, -8561607, 827831, -11912856, -11505791, -19897881, -6806205, -9842983, -10508592, -10258877, 2087459, 10405483, -19324715, -8209659, -6549242, -4712079, 4330516, -7229430, -6312533, -22690503, -9906941, 5005949, -5739577, 12083243, 6065386, -464534, 11009533, 2558255, 2733959, 15949714, -9399255, -1206340, -438550, -12158541, -20963846, -28510037, -29346244, -10397992, 2892137, -9770012, -1543580, -2355842, -737978, 9283226, 12890233, 65344012]
private def highC119 : List Int := [-48944281, 1353767, 2147616, 3500387, -5581006, -6381378, -2825743, -6707620, -2819008, -2749322, -6732637, -4277491, -6834410, 3866616, -3383711, -1834066, -1566379, -2845330, -3944343, -3853959, -2429821, -2207401, 3806858, 3122593, -4270260, -3285108, -3549330, -4519300, -6897175, -5285169, -5747270, -4728732, -2047799, -109845, 2823258, 9642782, 7925340, 4210289, 923240, -4921225, -6791267, -9712799, -11208411, -6825094, -4576479, -1279521, -3098790, 19403427, 7490340, 7990031, -3220924, 13466783, -2474193, 5050975, -10956024, 2306832, -3522061, 24960117, 5734078, -3245557, 6815796, 129511574, 88513929, 75805335, 56047073, 39824759, -51224783, -54125384, -59723514, -42478224, -24025078, -35037381, -31134850, -20627965, -14572133, 11567620, -9055214, -7096045, -19809458, 10130807, 26440228, 2993327, -30114936, -9896707, 7119999, 134001, 4700653, 1881487, -4221214, -10578405, -18045818, -20540299, -20050883, 993887, 12435022, -5483066, 3399958, -4901578, -26584428, -7669539, -5946310, -920866, -8808607, 5440501, 7866432, 4874685, 10299112, 19362526, -32113581, -74411573, 7682392, -2315587, -3310813, -9411997, 898033, -1270222, 2649345, 10120548, 12827415, 79653765]
private def highC120 : List Int := [-18751331, 7137429, -3380707, -3222111, -3378755, -4800354, -3277562, -3038267, 1656834, -1832687, -3817990, 1901639, -3611998, -645784, -4855288, -725205, -1548370, 913800, -18023, -687240, 1251676, 694695, 2581935, 2645146, -4129347, -819856, -2227056, -1314700, -2079681, -2889528, 5580870, -2658884, 2955427, -5930746, -5279571, 887308, 4989571, -1121423, -295237, -1694046, -2366845, -2729504, -3433085, -3155795, -1839540, -508232, -1275993, 8855028, 1918717, 4918901, 13037576, 8189714, -6844762, 605638, -11829842, -12908911, -2243151, 2337086, -1674249, 3473270, 3817103, 10332702, 30970457, 27054774, 21940522, 15597314, -12785877, -13280187, -13323177, -13891786, -11536500, -9254644, -10683614, 180157, -8910413, -9026275, -9304456, -9554966, -3182941, -1592840, -9950626, -2064771, -7573217, -4539719, -570169, 159630, -625589, 4412390, -2155150, -3966683, -5953254, -7237401, -24729394, -2913439, -7138509, 1445031, 3028846, -3222316, 412863, -2484915, -1301731, 3869369, -99245, -6332557, -4273478, -6001498, -7057794, 1186578, -9466359, -6149133, -6174872, -2436420, -13791929, -11973309, 3236611, 303910, -1400890, 17586245, 15755466, 7957905, 44948787]
private def highC121 : List Int := [-19639231, 3645585, -1271584, -254589, -3408641, -3557963, -942329, -2177565, -992326, -1051190, -831691, 492926, -5633893, -81753, -3109147, -582561, -914106, -1303519, -980185, -1623795, -836404, -412052, -185736, 614322, -3183264, -263836, -1281630, -1776740, -2288440, -4120832, -5052901, -3469493, -2751877, -1932156, 463310, -43591, 3296942, 6471580, -1635692, 260247, -1816293, -2306457, -4759676, -2592963, -2445556, -976080, -2816034, 5445409, 657916, 5979061, 10507843, 3925747, -2490778, -1401135, -13432765, -9578989, 702739, 7114762, 2176205, 625245, 4755341, -2666279, 31624863, 26384333, 20000853, 18763409, -15122336, -15524574, -15318121, -15915326, -13617429, -11832691, -4044370, 242178, -6698830, -2903745, -6371685, -7341034, 1071536, -3358258, -3593319, -5563112, -8216960, -8915508, -1955452, 2619222, -1216791, -1342739, -2003916, -5834469, -4612131, -6858872, -27054616, -5120705, -2936078, -4993369, 4001781, -1331877, -752280, -4728587, -2808764, -292829, -2864571, -3305026, -3519612, -4012074, 1338521, 1183863, -8549899, -9270414, 2600807, -3780893, -3435683, -9005495, 3308442, 2039438, 9413571, 4161054, 9678325, 17890661, 4177236, 51301737]
private def highC122 : List Int := [-11359972, 788763, 561877, 877740, -1274894, -5511588, -938187, 4701859, 11029958, -1911461, 3536310, 881466, 3658302, -126802, -480999, -593658, -2666695, -801468, 2123801, -1510694, 2511930, 1938126, -112178, -5834859, 3265946, 749858, -319362, -843299, -2149850, -2229702, -386073, -433696, -1714035, 517800, 960813, -6606201, -7739741, 8806314, 4788284, 1385388, 1129152, -1195213, -4005818, 424576, -1071892, -1975870, 1013371, -2139681, -36063340, -16165063, 12032632, 8071769, -11852362, -1565049, 16164987, -3452441, -9594761, 4944460, 5952135, 949142, 3504668, -19398961, -21662992, -27407173, -22413410, -23052633, 15613515, 17176010, 18104134, 20378843, 13291087, 11686020, 12913073, 4611702, 24889041, 632873, -3429638, -2408536, -7178745, -1443800, 14680307, 3625181, 22681436, 6103298, 4684415, -5152410, 6138882, 6532782, 7367064, 2651702, 10080579, 8687156, 18761543, 13908739, 18586183, 3633165, 607283, -4946838, 5113653, -141660, 2042423, 716413, -1585711, -211442, -339164, 3261348, 6979188, -1947574, -3658983, 6454976, -4045304, -9242467, 8890047, 8991063, -5124097, -6577710, -5422691, -4804167, 2283981, -6033252, -286767, 83367, 54830863]
private def highC123 : List Int := [-12727662, 246757, 546160, 890485, -1457092, -1163591, 868800, 6805478, 3529782, 7810768, 191456, -328846, 2434046, -3902, 2556289, -1073982, 301117, -598414, -168158, -2594062, 1430604, 1176842, 2374816, -2302520, 2438023, 712239, -679933, -997174, -1791420, -2133647, -2000208, -1670231, -121731, 1240430, 48814, -9117115, -9415867, 3945375, -6269153, 2535538, 1207257, 3947281, 1545781, 1718068, 7714133, -3906578, -4676359, -20644443, -5585125, -13501711, 4826464, -6619986, 2109149, -13607433, 17378479, 5808035, -779259, 3557106, 2350737, 4265843, -9007762, 770632, -25754014, -28490301, -24420549, -22706636, 20133454, 15289373, 21887278, 17897078, 7789605, 15248010, 16163738, 11828041, 14562248, 118233, 1567814, 11019478, -1434877, 894901, 1584174, 2955974, 15823070, 10442006, 6835979, 5055211, -1542979, -1742099, -1846037, 3092722, 1540290, 481337, 15158390, -2319720, 8009515, 3333643, 167673, -1125659, 1546278, 643604, 125420, -1997243, 923970, 1355668, 344182, 1807669, -2533386, 3683552, 12562553, -273631, 3803415, 3785058, -1004775, -4031136, 4677670, 2546293, -233219, -5645928, 2797545, -7841350, 5408786, 2624832, 1437666, 49693377]
private def highC124 : List Int := [-13523148, 651473, 631195, 1002980, -1530625, 1744877, -778579, 7107146, 5943711, 7961221, 2128341, 2630163, 1992003, -1916737, 4072189, -1262272, 9674160, 4503432, -2824050, 27468, 4348286, 4391148, -3788643, 1396287, 3664285, 2873900, -2774131, -505474, -2026621, -5292066, -1569899, -2018438, -88733, 49801, -4025278, -12792701, 2103629, 6053592, 798769, 311552, -4420944, 3885177, -279938, 5520914, -3687551, -3927059, -7614198, -18319894, -5478976, -8976961, 5329119, -10870776, 1203016, -10759978, 6745346, -206933, 1598966, 3535426, 3113538, 3115867, -5653120, -13300514, -16147097, -21096491, -21055682, -15104433, 18774274, 14574095, 23926016, 23675459, 16630326, 10915977, 19523737, 15145557, 11353984, 4235465, 6603422, 4834086, -1132860, 8558673, 1305306, -362912, 10359302, 8936176, -850376, 8026494, 1627980, 961613, 1649765, 2731282, 2499538, 1996004, 10011114, 8961288, 7984220, 3127194, -2887716, 9289235, 1652262, 5370698, 4679962, 1401983, 3696682, 2464495, 1378148, 2409641, -6783878, 6666461, 6544886, -4475891, 464427, -1725364, -1656519, 3758801, 4385268, 9891013, -256514, -8378424, -1956096, -5654768, 2268975, 3417812, 6755648, 16014929, 46274364]
private def highC125 : List Int := [-16519704, 473148, 705532, 1151983, -1890650, -2164775, -969936, -1812405, -850010, -416570, -1289266, -1665775, -2191890, 1126866, -630315, -435949, -790705, -2034087, -1107783, -1614256, -934865, -656808, 1078466, 956468, -954731, -875098, -986534, -1288028, -2179580, -1692713, 1544197, 1676839, 1195913, -2208397, -802802, 3417098, 2169194, 7477055, 288320, 5360863, -767496, -1486431, 1131907, -3885801, -3346062, -762093, -2511841, 12213615, 5341408, 6871969, 3889088, 4853304, -595075, 2380254, -8235662, -7763621, 3593731, 6646071, 2745951, -7820630, 5035797, 2290468, 28420726, 25621783, 15253781, 10934594, -17485313, -17180534, -13928903, -17477173, -10538128, -8079549, -12869359, -6153528, -9078208, -1500756, -10855386, -2792153, 256566, -4476617, -2772737, 159561, -7320305, -10552652, -3451418, 3880505, -2359270, -2438868, -4051519, -10620150, -6031972, -6954781, -21908598, -9679974, -2303364, -1308533, 2323903, -10980004, -6552357, -7851557, -3386141, -1513125, -7165593, -4458828, -3624823, -3472224, 2174058, -3273511, -8835870, -334041, 4030326, -1160861, -6911102, -10594889, -1042308, -1374358, -146951, 10067464, 9043259, 21593767, 7209915, 19266869, -489217, 661566, -4586615, 44796141]
private def highC126 : List Int := [-14166715, 619882, 653029, 1041590, -1606290, -1856529, -792945, -1533751, -600458, -577132, -1631383, -1392369, -1778379, 1108429, -822249, -552642, -527946, -891502, -897229, -953879, -435068, -265990, 1434077, 1118804, 2279514, -301347, -1397348, 6051207, 5805553, -5098190, -82010, -2069014, 2610049, 2818973, 2586194, 7005977, 4208918, 1354019, 1937031, -60762, -1718192, -1932133, -2706434, -534888, -1144590, -392099, -299692, 6253178, 4449752, 5042079, 5286712, 11275950, 543297, 1337094, 9191085, -3768598, 4550232, 5868831, 359098, -5325838, 1557929, -2602674, -5046405, 25628557, 18383312, 22672982, -23337989, -17780302, -23948820, -17230315, -20028431, -10415503, -12612124, -7289337, -7981055, 2137938, -11929564, -6640119, -1446131, 783568, 4679900, -8470858, -17780837, -9194052, -7614173, -7319746, -9289458, -6275885, -8804444, -965991, -6297983, -6537431, -14827407, -8724544, 574796, -1075131, 2817554, -3801174, -9637530, -5206682, -2224452, -1519693, 4456572, -1180503, 1304026, -3263091, -5428034, 1362099, -4383440, -18678246, -1796010, 4055570, 1441529, 2359015, -8463381, -6532933, -808257, 302075, 27139042, 22041554, 6446509, 606471, -7473179, -6003131, -5458690, 1737085, 50031666]
private def highC127 : List Int := [-15636129, 2199765, 919340, 1370552, -1796638, -2082513, -635982, 1094732, 807541, 858827, -937064, -921457, -508128, 1017988, -24551, -539401, -872856, -1474298, 878061, 583809, 1376866, 2126017, 3483563, 2756540, 1001511, -354249, -1370986, -1461486, -2011638, 1406417, 2162914, 1243733, 3507489, 4736641, 2380240, 10798189, 5363675, -2026145, -12101020, -3737814, -3238095, 767375, 295932, 959338, 1134383, 1710276, 1278477, 12030985, 5362842, 8071111, 8426875, 9476373, 2217235, 1174397, -24688422, -4308863, 3933909, 12251579, 24642490, -3337732, 7088183, -17623507, -5736796, 44190326, 33007084, 43219616, -42535116, -29596404, -45725296, -36776162, -51791412, -18875067, -23933597, -6284471, -17294393, -1949405, -22915982, 5475709, 11627577, -8151555, -898752, -1804289, -25009956, -32052639, -14792113, -8508476, -6537261, -7532070, -7887572, -11498010, -11494991, -6672899, -23965208, -23726951, -6811372, -7840239, 2323911, -2277717, -4278189, -11142156, -1836560, -4392388, -1923220, 3514112, -2221462, -2078607, 20371403, -8829712, 5465512, 1153267, 11788323, -8054071, 8266284, -3665109, -9210989, -1815014, -7854451, -19787409, -18736709, 24129330, -8391371, 34168895, -21342154, -19442198, -18841935, 23903112, 1118270, 74344201]
private def highC128 : List Int := [1348433, 6865715, 845140, 910262, 465133, -71125, 920097, 12833614, 6750090, 6861501, 14529913, 3906233, 4996124, -3575706, 4038263, -67633, -2796124, -3563805, 9181483, 5358785, 8908463, 12467832, 6646695, 5353565, 7964912, 2839101, -141969, 980028, 1174872, 11126202, 13662011, 8919793, 15322024, 19142705, -1567693, 30165116, 12335831, -11657096, 384994, -7702902, -1683318, -2033904, 3621712, 7788483, 12768978, 12157830, 26332871, 32970509, 20987098, 16452107, 23310010, 24175745, -2686936, 7217529, -5852771, -1986644, 5437946, 22430791, 13760855, -17613572, 15831936, -9270358, -7395000, 32465344, 78615286, 97594119, -79199151, -60009455, -95179546, -76622508, -100429483, -48969635, -61820491, -18554340, -33912539, -12293717, -32902840, 10315090, 13074529, -829679, -8410876, -15271348, -54402471, -38057655, -33624436, -31788450, -11448291, -14958475, -13912108, 10075391, -12728796, -3952760, -27334797, -21513520, -29439475, -4766267, 2229136, 18483512, 5971816, 2264235, 103230, 695107, 18705877, 8386229, 4726472, -3687992, 5284680, -11824152, 6143316, -5621919, -1554165, 8118549, 6755287, 15472546, -7006500, -10778304, -9191303, -21917782, -23872204, -17756110, -24150244, -32814298, -57509738, -52735158, -40770484, -18596882, 17679824, 35054137, 86293317]
private def highC129 : List Int := [-4643843, 6403589, -1464917, -1564000, -923038, -1776411, -1093371, 4391928, 2737165, 2348126, 581940, -8845, 1164462, -620591, 324167, 562535, -570312, -606018, 2738395, 2736679, 4327623, 5409415, 5284983, 3072600, 3192730, 1346008, -105155, -451872, 482177, 2733136, -4436420, 1272457, 6350590, 11476183, 5145566, 11953654, 7088212, -3937576, -315227, -1616893, 37885178, -6481680, -2487105, -17757926, -3050867, -12114319, 7667294, 25996880, 12932871, 12555973, 22093393, 10047656, 7602122, 613532, -10899063, -7850088, 2104674, 17514013, 10906263, -10794241, 11326895, 7406902, -933654, -5240074, 38229782, 47287767, -38029653, -37072933, -40396192, -39038098, 6603476, -39201403, -3171744, -13428734, -27580571, -32393116, -37099798, 7825114, 459928, -16509629, -13444214, 9656670, -3818592, -8805887, -3388530, -4023412, -3427506, -5147276, -4845464, 1588129, -3971626, -11938359, 11193303, -312764, 31121070, 7087777, -7410279, 14402082, -2489481, 11783143, 2909628, -2428532, -417167, -8070486, -4748682, -2177733, 3925753, -8325616, -3233377, -9983603, -6731156, 484959, -838562, -8688485, 769167, 1357253, 595142, -8381582, 3690135, -4297256, -1011906, -1212762, 16000942, 31276178, 21799803, 1326288, -16746260, -9521009, -23118688, 88189148]
private def highC130 : List Int := [-24796664, 17163686, -245942, -6613469, -4695242, -7121992, -5663939, 3024719, 3094764, 1763222, 12354550, 15795832, -7715208, -9294366, -5508670, -2655234, -5078772, -5570800, 6448354, 2182738, 6563049, 9845647, 2745649, 2770258, -3505555, 1320676, -772089, -1218115, -856893, -1819864, -13500559, -6128574, 1471820, 13868393, 2309591, 20174473, 11430695, 28216669, 5225968, 49040595, 7974381, 30181290, 11439501, 8635470, -10009854, -16344618, 18519598, 49070253, 19061298, 30908032, 22664681, 35647652, -17917029, 21774218, -14130845, -13898015, 12063970, 38482047, 17110801, -3610868, 24224255, 40423994, 6605851, 21772042, 34068896, 34058076, -53327055, -61840391, -29770175, -87837896, -49059210, -43686861, -35568035, -5399123, -25241202, -10557695, -21506033, -20242430, -5699690, -13421352, -24780353, -19561646, -25304337, -14528801, 6557575, -13301747, -4063579, -4584573, -6478031, -316104, -4180590, -1732720, 4643365, 7017366, 8842369, 311242, 6750334, 23518647, -11598581, 12542675, 6062092, 8089484, 10871451, -4109523, -3100688, 2122298, -16248004, -14929829, -3665271, -13830496, 8987250, -9838684, -12195406, -9102311, 5507390, -1264166, -2645444, 2849433, -2409341, 8363040, 2570988, 7388499, 1486953, 2979111, 1564739, 458662, -1168355, 10879792, 1299012, -3683871, 60025313]

def highCholesky : List (List Int) := [
  highC0, highC1, highC2, highC3, highC4, highC5, highC6, highC7, highC8, highC9, highC10, highC11, highC12, highC13, highC14,
  highC15, highC16, highC17, highC18, highC19, highC20, highC21, highC22, highC23, highC24, highC25, highC26, highC27, highC28, highC29,
  highC30, highC31, highC32, highC33, highC34, highC35, highC36, highC37, highC38, highC39, highC40, highC41, highC42, highC43, highC44,
  highC45, highC46, highC47, highC48, highC49, highC50, highC51, highC52, highC53, highC54, highC55, highC56, highC57, highC58, highC59,
  highC60, highC61, highC62, highC63, highC64, highC65, highC66, highC67, highC68, highC69, highC70, highC71, highC72, highC73, highC74,
  highC75, highC76, highC77, highC78, highC79, highC80, highC81, highC82, highC83, highC84, highC85, highC86, highC87, highC88, highC89,
  highC90, highC91, highC92, highC93, highC94, highC95, highC96, highC97, highC98, highC99, highC100, highC101, highC102, highC103, highC104,
  highC105, highC106, highC107, highC108, highC109, highC110, highC111, highC112, highC113, highC114, highC115, highC116, highC117, highC118, highC119,
  highC120, highC121, highC122, highC123, highC124, highC125, highC126, highC127, highC128, highC129, highC130
]

def highMatrix : Nat → Nat → Int := gramResidual highResidual highCholesky

def highCuts : List SparseRow := [
  ⟨3, 40, 0xd6486d42fff9788dd841195713ef9500⟩,
  ⟨2, 23, 0x312f98a1e1ec9000⟩,
  ⟨3, 39, 0x120379f24f10c05971945f0080001f7a4c00⟩,
  ⟨2, 24, 0x7fc63b4482867e01⟩,
  ⟨2, 40, 0x204f99444d85e5c4bf902⟩,
  ⟨2, 40, 0x9983a5c17b44000693980f02⟩,
  ⟨2, 40, 0x17ea5f145fffef92e7002⟩,
  ⟨2, 40, 0x2ff8e9f45fffe67f93a02⟩,
  ⟨2, 40, 0x83c2458c0345fffc7fc9bb02⟩,
  ⟨2, 27, 0x2147c40a2900ad2802⟩,
  ⟨2, 38, 0x89b213e7a914000b4c6d502⟩,
  ⟨3, 40, 0xfffe6341b745000203db6403000029c3c502⟩,
  ⟨2, 24, 0x87148a468addaa03⟩,
  ⟨4, 40, 0x1b6dd74700039fd62b46dafca61852050001031c6604⟩,
  ⟨2, 40, 0x897d5e47fffce4598d06⟩,
  ⟨2, 31, 0x54256ea3c1579fbc06⟩,
  ⟨2, 40, 0xd8b5ed47fffccce7ce07⟩,
  ⟨2, 40, 0xfffe642eb44700036dd1f107⟩,
  ⟨2, 40, 0xfffef6b87247ffead76f8308⟩,
  ⟨2, 40, 0xffff3f09824700036d962c08⟩,
  ⟨2, 40, 0xfff931cb0648ffecdd6b3109⟩,
  ⟨4, 40, 0x8cf4dc07f449ffffbf73a848ffffcc9eba0b00095d54c80a⟩,
  ⟨2, 40, 0xffff702ecf49ffff533dc90b⟩,
  ⟨3, 40, 0xffffdeade249ffffc2fa000c7664d16c6f0b⟩,
  ⟨2, 40, 0xfffd4b273c4afffdfe47870c⟩,
  ⟨2, 40, 0xfffc9bfa704a196aa892340c⟩,
  ⟨2, 40, 0xfffd5b02b34afffea510150d⟩,
  ⟨2, 40, 0xffff02b5264affff2ec4ff0d⟩,
  ⟨3, 40, 0x86d5d94bfff844ac854a00022e14ae0d⟩,
  ⟨2, 25, 0x13ee40e973f9cb70d⟩,
  ⟨2, 25, 0x2f5d54097e235ed0d⟩,
  ⟨2, 24, 0x88d7f34b5655be0d⟩,
  ⟨3, 27, 0x175a116d2cc640068701bc67e0d⟩,
  ⟨2, 25, 0xfc03b0997b79280f⟩,
  ⟨4, 40, 0x19463d4d00017aff714cffff8155df1100009ab24a10⟩,
  ⟨2, 40, 0x4babeb4dfffe85cb6a12⟩,
  ⟨3, 40, 0x5f01a64dffffc9f23814fffe83722f13⟩,
  ⟨2, 40, 0x935a544efffe82a0b214⟩,
  ⟨3, 40, 0x1f2fde4f000be146e44effffd988af15⟩,
  ⟨2, 40, 0xba22e54ffffec7d26515⟩,
  ⟨2, 40, 0xf6e4b24ffffdebc95215⟩,
  ⟨2, 40, 0x16eaa0f4ffff8f133b815⟩,
  ⟨2, 40, 0xffff75e3ac4f00009f45b915⟩,
  ⟨2, 40, 0xffff8b56b84f82c1a0713516⟩,
  ⟨2, 40, 0xffff9b00284f0002f7788c16⟩,
  ⟨2, 40, 0xfffe829045500000973ddb16⟩,
  ⟨3, 40, 0xfffe76f7b451ffffc9e0ae500000794a9d17⟩,
  ⟨2, 40, 0xffff8157ac51000052f79c17⟩,
  ⟨3, 40, 0xffffe06a1f5100018a10821800001acb3917⟩,
  ⟨3, 40, 0xfffe837e4e520005e7ea071900008a2b3618⟩,
  ⟨5, 40, 0xfffe7615b853ffffc9e87052ffff8354bf1c0000bebc0b1b0000d8d4171a⟩,
  ⟨3, 40, 0xffff80ef3d53ffff0883831dffc8f3ddb21c⟩,
  ⟨4, 40, 0xffffe06b0353ffffc9df3f1ffffe051b1c1efff9e0e5501d⟩,
  ⟨2, 40, 0xfffb7b6b0b54fffe8346671f⟩,
  ⟨3, 40, 0xa57e18155ffffaf9c9354ffffdff10120⟩,
  ⟨2, 40, 0xfffe09e42d56ffff7cbab220⟩,
  ⟨4, 40, 0x7eb5ea58ffff62e38257ffffc9e40521fffe2b165520⟩,
  ⟨2, 40, 0x17c682e59fffe8458f121⟩,
  ⟨3, 40, 0x193d9c5b00017bbb115affffd95e2022⟩,
  ⟨2, 40, 0x4bb8dd5bffff36c83322⟩,
  ⟨3, 40, 0x5ed7bc5bffffb46cb92300013d385222⟩,
  ⟨2, 40, 0x7e57255cacdf4290d323⟩,
  ⟨3, 40, 0x204b775d00017e712c5cffffa4a05524⟩,
  ⟨2, 40, 0x74d0005dfffc1aef5224⟩,
  ⟨2, 28, 0x89dce55dd18623824⟩,
  ⟨2, 29, 0x21e633eeba089f51124⟩,
  ⟨2, 40, 0xfffc52fa105d000074a29b24⟩,
  ⟨3, 40, 0xffffa6519d5d00017d74e2250000203ca924⟩,
  ⟨2, 40, 0xb0a851eb1b5e00007e6d8725⟩,
  ⟨3, 40, 0x12d4dbc5fffffb459105e00005ef43826⟩,
  ⟨2, 40, 0xffff35ac2d5f00004bcde126⟩,
  ⟨3, 40, 0xffffd937335f00017b0a8a27000019425126⟩,
  ⟨2, 40, 0xfffe8460a06000017bb37d28⟩,
  ⟨4, 40, 0xfffe346a8561ffffc9a93a60ffff62553e2a00007e86a129⟩,
  ⟨2, 40, 0xffff7d361261fffe02bf2e2b⟩,
  ⟨3, 40, 0xffffe0023461ffffb022f32d000bc27e612c⟩,
  ⟨2, 40, 0xfffe83beb462fffbb9f4ab2d⟩,
  ⟨4, 40, 0xfff9e694d464fffe05b75563ffffc9dd2e62ffffe061af2e⟩,
  ⟨3, 40, 0xffd22464e265ffff091b3164ffff8133d02e⟩,
  ⟨5, 40, 0xd7eae5670000bcf03f66ffff83525f65ffffc9e3682ffffe7667ea2e⟩,
  ⟨3, 40, 0x89e084690005e92ea768fffe818bce2f⟩,
  ⟨3, 40, 0x1acd836a000181a2fe69ffffe06a1f30⟩,
  ⟨2, 40, 0x52eb666affff815fdd30⟩,
  ⟨3, 40, 0x7a2cc86affffc9e48731fffe761f3630⟩,
  ⟨2, 40, 0x976e006bfffe83f52731⟩,
  ⟨2, 40, 0x2f928006bffff9afd2e32⟩,
  ⟨2, 40, 0x807cc1cd596bffff8b483632⟩,
  ⟨2, 40, 0xa1201c6cffff75f77c32⟩,
  ⟨2, 40, 0xfff8dcc1736c00016d9c4d32⟩,
  ⟨2, 40, 0xfffde9dc086c0000f66ab332⟩,
  ⟨2, 40, 0xfffec658026c0000b9e6fc32⟩,
  ⟨3, 40, 0xffffd980b76c000dd974d83300001f27ce32⟩,
  ⟨2, 40, 0xfffe81870f6d000094128633⟩,
  ⟨3, 40, 0xfffe84864b6effffc9eb936d00005ed1b734⟩,
  ⟨2, 40, 0xfffe85e9cb6f00004baba134⟩,
  ⟨4, 40, 0x9bcf7571ffff8136847000017b827535000019464634⟩,
  ⟨2, 25, 0x2f6852ee47e08dc35⟩,
  ⟨3, 28, 0x1bb0367418b07e97389ba82036⟩,
  ⟨2, 24, 0x55fc5d748a4b1836⟩,
  ⟨2, 25, 0x3c11208e97e1bff36⟩,
  ⟨2, 25, 0x278d716e8a0c31e36⟩,
  ⟨3, 40, 0x22e86a874fff7bf4f8137000087a49d36⟩,
  ⟨2, 40, 0xffff2e9fdf74ffff0352f037⟩,
  ⟨2, 40, 0xfffea542c674fffd5de97937⟩,
  ⟨2, 40, 0xb1cc6fc1375fffc9c109737⟩,
  ⟨2, 40, 0xfffdfd160d75fffd50ee0a37⟩,
  ⟨3, 40, 0x75c0da615d76ffffc2fc8b75ffffde8ea538⟩,
  ⟨2, 40, 0xffff5441c476ffff6fe4c738⟩,
  ⟨4, 40, 0x85478b277ffffcc54df76ffffbf9c8b398e70e601bc38⟩,
  ⟨2, 40, 0xffeaef9eff78fff975d8a539⟩,
  ⟨2, 40, 0x3688bae79ffff3c68bf3a⟩,
  ⟨2, 40, 0xffe97cb52379fffef0b4493a⟩,
  ⟨2, 40, 0x36356297afffe58c65c3a⟩,
  ⟨2, 40, 0xfffcc2bc957a0000d86a393a⟩,
  ⟨2, 30, 0xdccf57edec0a85c003a⟩,
  ⟨2, 40, 0xfffcda2fad7b0000896cb33a⟩,
  ⟨4, 40, 0x100cb107ddc448369bd7c00038b57563b00001b65283a⟩,
  ⟨2, 24, 0x8aee047e86c99f3b⟩,
  ⟨3, 40, 0x29d6a97f0002009c227efffe8064ed3c⟩,
  ⟨2, 38, 0x2d0e8c5fe861e2ab073c⟩,
  ⟨2, 27, 0x813ac6bfc41f3423c⟩,
  ⟨2, 40, 0xfffc82dff87f8736ac4f463c⟩,
  ⟨2, 40, 0xfffe68e9077f0002fa38ec3c⟩,
  ⟨2, 40, 0xfffefa63267f00017bd7ab3c⟩,
  ⟨2, 40, 0x6450fbb7f9540aaf2f03d⟩,
  ⟨2, 40, 0xda54dd1f227f000202b64b3d⟩,
  ⟨2, 24, 0x82ef1d807fb6ae3d⟩,
  ⟨3, 39, 0x7df20a0409543b1d0c0486fcc81c93e⟩,
  ⟨2, 23, 0x30e75740e277533e⟩,
  ⟨3, 40, 0x17e0647b4f81fff9d10fec400000d7e2c73f⟩
]

def highOO : List SparseRow := [
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨3, 17, 0x43378ae27105577731c⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨2, 17, 0x335065b448b1d⟩,
  ⟨3, 17, 0x70c00b7f7fa55929d1d⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨4, 17, 0xd3952cfab5963ccf257f8b02a⟩,
  ⟨9, 19, 0x3a0c05a7db9cb33c4e1613f48a1113d24153c825b1b488b2952395e68392a⟩,
  ⟨10, 20, 0x1ee575b439d55a4e884596a38d582e09b4212484412eefe2d56ee02c69be62b87bb12a⟩,
  ⟨10, 21, 0x47f54b65d43d5a3a927acaa85b560606ee84129e441243da16a62220b1c1468575ec102a⟩,
  ⟨6, 20, 0x967e857b661f567bb11555edf75412dc44023c193f⟩,
  ⟨5, 19, 0x63c0057f5630ad7a2bd562fff2a13fe140⟩,
  ⟨6, 19, 0x2f7502beeefa56abd04aaf85d1509f78201fca13f⟩,
  ⟨4, 19, 0x79ebcaf1224559bf792a9238740⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨2, 18, 0x9daad666f7d58⟩,
  ⟨3, 17, 0x548c96af118b3633158⟩,
  ⟨4, 17, 0x80b12bbf01d5a149eaaecbd54⟩,
  ⟨4, 18, 0x935755e1c99568165155cba354⟩,
  ⟨1, 17, 0x17ea857⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨5, 19, 0x1f76f6743a56ccbc741697f52accbedd58⟩,
  ⟨3, 19, 0x11bf616a48ba2ceb2cb58⟩,
  ⟨4, 20, 0x211ba5b4e5135a506aa5995c0358⟩,
  ⟨6, 19, 0xa9bbb92160e6645304b744de56aab122cfe99c58⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨3, 18, 0x171af72930a19dfbc466⟩,
  ⟨1, 18, 0x25c0972⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩
]

def highOnes : SparseRow := ⟨130, 10, 0x77e05af808b1fded7e999f6577cca9ef4e7ad59e67c78939dddc765d1d69174a45ce9172a49c69270a45be836e9fdb6816c635ae4e6aa59a69268a4d9e9366a61969264a458e8c6286d854e606097db85e99976855ca456e935aa4d669458a4d5e9356a49569154a354e70528e945b4506493d724e52d358a4c7352d7b4a615259f489851e6646a2d168e44a3d0e9242a39068f40a44fe8f3ea34f68b3c9b0ee673a670e584385e4ddcf36634d54b345cccd92326d0c635309b4be8c2ea48b6932ca4cae942aa4ca69328a489e8f26a18966d246e08d8022538861720a2c7e911ea4876981ca4c6e931aa40668f1893c5d90169ec567c14a0c4e8f12a44469110a383e8f0ea5835750c7642e4e0a9f0275708d201f29069601663047ac0e2d026b805de00⟩
def highYhm : SparseRow := ⟨71, 32, 0x1d1388100023ff3800000797c7f00008cdb7e00005af27d0003dda375000061c273000063557200007ae86c000274516b00007d306a0000e34b6100128803602e6db7ec5f180249445e0000bd095d0000785e5c000067d45b000063d55a000071a0530000a850520001127051240576cc50958d360d4f55313d024e79a6442d4d320354d34c00047f004b2474c7254a70654dfc4932a0613b480000c6af470000b90a4600006df545000066e04400006678430000706b3e00006c8e3d000070603c0000b2823b0000bb793a2e15d87b396f76804338243b2b60370003fdf4362ddf0b42357d28a5ac3451d1e3b83392fd8eef3221f4f9193100012d42300000a5262f00006d7e2e00006ef02600007a26250000afe42419eb60832332b7cb2e22000e2b5c210000e7db200000811517000234c01600008095150000673a1000006a480f00040bd80c000064e00400009bf403000073650200025a75010002164c00⟩
def highOhm : SparseRow := ⟨26, 26, 0x59dd65ee83dc797a0e662c5e400637e740018a21c00062216f0019011b8006acb650018cf19000636c6300187198800648d57001a0810400636c40001a93ca80064111f001a1607800685a1d001bc907000697813001a574480066f81100185a834a5f0e20817e1d101c2a307c06⟩

def highHints : List SparseRow := [
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨1, 17, 0x1205c1b⟩,
  ⟨3, 17, 0x548389e4d9e35947119⟩,
  ⟨2, 17, 0x3d68237eff61a⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨1, 17, 0x10f061b⟩,
  ⟨1, 18, 0x246f01a⟩,
  ⟨0, 1, 0x0⟩,
  ⟨2, 18, 0x98b20a6086d27⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨6, 18, 0x7449d59f27555a7071521e625382a98a273f127⟩,
  ⟨7, 20, 0x36fbd5740ffa563f9a8553b235542e4823f4fd5c29b47f428⟩,
  ⟨7, 20, 0x475955751905564976b5536b7554169ae402c3fd3f8276429⟩,
  ⟨6, 19, 0x341d7abd6aaf5688bceaac5c1150a6b0a0240483f⟩,
  ⟨8, 20, 0x3f18b5a3d6ed59695fa582500c4210faf412fd3a2d8a5a42cc6a0d2b⟩,
  ⟨8, 21, 0xf85cad91f78568888b0b25b9ca5814a1a21047d75048c7805bc6e1f2c⟩,
  ⟨6, 19, 0x108b0adcc3735a89becb33391d615849a1506172d⟩,
  ⟨6, 18, 0xacf656ff4915ac8df96743f158dc661090bb62e⟩,
  ⟨1, 17, 0x13a355b⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨1, 18, 0x3586f3f⟩,
  ⟨2, 18, 0xad405525b4c40⟩,
  ⟨2, 17, 0x25c02af475d56⟩,
  ⟨3, 17, 0x4f4c5662f00b1bbe742⟩,
  ⟨4, 18, 0xe113d6af28c59a603162ae1e43⟩,
  ⟨2, 18, 0xae3596dd7b65a⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨1, 17, 0x18ce254⟩,
  ⟨3, 19, 0xd77295e4197ab5b02c55⟩,
  ⟨2, 21, 0x1087aeaf33abe56⟩,
  ⟨1, 20, 0xb8f1957⟩,
  ⟨0, 1, 0x0⟩,
  ⟨3, 20, 0x3178266627d45a93f8a59⟩,
  ⟨2, 20, 0x262f15b9742f5a⟩,
  ⟨3, 18, 0x2570872cf4f19aeb005b⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨1, 18, 0x2b0c771⟩,
  ⟨3, 19, 0xa9309c9b82338c3d2c68⟩,
  ⟨1, 18, 0x362e372⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩
]

def highDirections : List Nat := [
  0x300601d80007e00001e0000000000,
  0x80700400001e0000000000000000,
  0x0,
  0x2800000000,
  0x0,
  0x0,
  0x3,
  0x1,
  0x0,
  0x200000200000e00000000,
  0x80000000,
  0x200,
  0x301,
  0x0,
  0x7001602,
  0x800f01,
  0x800000c00600,
  0x400,
  0x600,
  0x700000400000000300,
  0x300000200000000180,
  0x0,
  0x0,
  0x0,
  0x4000000000018004,
  0x3,
  0x1,
  0xe00000000001000,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x1000080001,
  0x400000000000000000180001,
  0x10000000c00000c0003f,
  0x7e0000300001f,
  0x3e0000780000f,
  0x1e00003000007,
  0xe00001000003,
  0x600000000001,
  0x0,
  0x0,
  0x100000000000,
  0x180000100000,
  0x1c0000080000,
  0x1e0000080000,
  0xf0000040000,
  0xf8000200000,
  0xbc000000000,
  0x80000000000,
  0x40001000000,
  0x800000740026200003,
  0x40400300028000001,
  0x20040001c000000,
  0x60000000,
  0xe000000,
  0x3f80001f,
  0x1e00001d,
  0xf80001e,
  0x7c0000f,
  0x3e00007,
  0x1e00003,
  0xf00000,
  0x600000,
  0xc00001,
  0xe00000,
  0x600000f00000,
  0x300600780000,
  0x1805003c0000,
  0x800801e0000,
  0x20040070000,
  0x700e01f8000,
  0x300700fc000,
  0x100400f8000,
  0x802003a000,
  0x20000,
  0x380009,
  0x200007c001b,
  0x1003e0007,
  0x801e007f,
  0x400e003f,
  0x1f,
  0xf,
  0x7,
  0x3,
  0x1,
  0x0,
  0x2000000,
  0x1000000,
  0x2800,
  0x401400,
  0x600a00,
  0x100100,
  0x100000,
  0x0,
  0x280e01,
  0x0,
  0x7,
  0x3,
  0x1,
  0x0,
  0x0,
  0x0,
  0x100,
  0x80,
  0x0,
  0x2001,
  0x0,
  0x7,
  0x3,
  0x1,
  0x0,
  0x0,
  0x1,
  0x0,
  0x0,
  0x38,
  0x14,
  0x1,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0,
  0x0
]

def highConstantRows : List Int := [
  -7366966293441600, -308746776000, -5956396479446400, -243762177600, -1115277221286000, -791603619120000, -1319611218507600, -3958349567108400, -3202162812465600, -975818727600,
  -1242120972968400, -11874750091519200, -258527980800, -4515265574438400, -306656374800, -1318217554954800, -312548372400, -563356904400, -1319259188958000, -434676909600,
  -2089011345600, -7648940703350400, -298758412800, -2837127550123200, -274099659300, -297223865912400, -331244326200, -349882111200, -330157141386000, -326362113600,
  -328454746500, -351029400000, -2136326376000, -238287283200, -504007396800, -237994200000, -358284753600, -259028937600, -1249066224000, -332876721600,
  -384023241600, -628126695600, -307361418000, -674032389078000, -298325390400, -262719033600, -395435203200, -250025203200, -369622296000, -358125198000,
  -629456073600, -1364406332400, -481241673600, -483594921600, -5277120895094400, -281832331200, -534504345600, -239094052800, -384385483200, -308993702400,
  -5277841781832000, -1713870771744000, -519925735200, -825136164000, -9234171439813200, -9233628331000800, -785289003600, -514210910400, -1635831837667200, -5277847097798400,
  -310169846400, -384829310400, -238862577600, -532425590400, -283624992000, -5277005417520000, -463774468800, -480805887600, -1178817032400, -627777832800,
  -358585069200, -367013332800, -249919982400, -396779793600, -262457976000, -298736733600, -662337995552400, -309480441600, -632370511200, -384443638800,
  -333487956000, -1407636278400, -260054030400, -357767020800, -237955094400, -505335868800, -238246094400, -3027757761600, -352760568000, -329529994500,
  -326305658400, -330155659825200, -349750941600, -330610235100, -315654705546000, -273429418500, -2850332195760000, -298072929600, -7618419887539200, -2222938963200,
  -436587678000, -1319238071940000, -570751957200, -314784710400, -1318421743417200, -308997938400, -4541659918670400, -258312081600, -11874769966046400, -1457088125853600,
  -995041191600, -3113134351519200, -3958350162735600, -1319610395965200, -769620768193200, -1125393413533200, -244090526400, -5997565012852800, -308711448000, -7246301043288000
]

def sparseAt (rows : List SparseRow) (i j : Nat) : Nat :=
  (rows[i]?.map fun row => row.entry j).getD 0

def highHint (i j : Nat) : Nat := highWeightScale.toNat * sparseAt highHints i j

def highPrefer (i j : Nat) : Bool := digit (highDirections[i]?.getD 0) 1 (j-i-1) == 1

def highRetained : Retained where
  o := fun i => highOnes.entry i
  oo := fun i j => sparseAt highOO i j
  ml := 4423
  hm := 12967
  mhm := 20288193324
  yhm := fun i => highYhm.entry i
  ohm := fun i => highOhm.entry i

end OMA.Erdos1186High

end

section

/- Real lower bound from the integer G24 branch weights. -/

namespace OMA.Erdos1186High

open Finset OMA.Erdos1186Region2 OMA.Erdos1186SnivelyForms
open scoped BigOperators

def highLength (i : ℕ) : ℤ := g24Length i

private def fullCorners (i j : ℕ) : Prop :=
  1 ≤ (2 * (g24Endpoint j + 1 : ℕ) - g24Endpoint (i+1) - 1 : ℤ) ∧
    (2 * (g24Endpoint (j+1) : ℤ) - (g24Endpoint i + 1 : ℕ) - 1) ≤ 1094

private instance (i j : ℕ) : Decidable (fullCorners i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

def branchComplement (i j : ℕ) : ℕ :=
  if fullCorners i j then highQ else min highQ (sparseAt highCuts i j)

private theorem branchComplement_le (i j : ℕ) : branchComplement i j ≤ highQ := by
  unfold branchComplement
  split
  · exact le_rfl
  · exact min_le_left _ _

def highA (i : ℕ) : ℤ :=
  (highD / 300304 : ℕ) * (digit g24AlphaWord 9 (min i (129-i)) : ℤ)

def highBeta (i : ℕ) : ℤ :=
  (highD / 1801824 : ℕ) * (digit g24BetaWord 9 (min i (129-i)) : ℤ)

def highPair (i j : ℕ) : ℤ := (if g24Sign i = g24Sign j then 1 else -1) *
    300 * (branchComplement i j : ℤ) * highLength i * highLength j

def highPairConstant (i j : ℕ) : ℤ :=
  if g24Sign i = g24Sign j then
    -75 * (branchComplement i j : ℤ) * (4 * highLength i * highLength j - g24Area4 i j)
  else -75 * ((highQ : ℤ) - branchComplement i j) * g24Area4 i j

def highObjectiveCoeffs : Coefficients where
  constant := highConstantRows.sum
  linear := highA
  pair := fun i j => highPair i j + if i = j then highBeta i else 0

def constantRowCheck (i : ℕ) : Bool := decide
  (((List.range 130).map (highPairConstant i)).sum = (highConstantRows[i]?.getD 0))

private theorem weighted_le_max (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1-t)*a + t*b ≤ max a b := by
  calc
    _ ≤ (1-t)*max a b + t*max a b := add_le_add
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0)
    _ = _ := by ring

private theorem highPair_le (i j : ℕ) (u v : ℝ) :
    (highPair i j : ℝ) * (u*v) + highPairConstant i j ≤ (highD : ℝ) * pairObjective i j u v := by
  let t := (branchComplement i j : ℝ) / (highQ : ℝ)
  let p := (g24Length i : ℝ) * g24Length j / 1096^2 * (u*v)
  let inside := (g24Area4 i j : ℝ) / (4 * 1096^2)
  let outside := (g24Length i : ℝ) * g24Length j / 1096^2 - inside
  have hQ : (0 : ℝ) < highQ := by norm_num [highQ]
  have hD : (0 : ℝ) ≤ highD := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hQ.le
  have ht1 : t ≤ 1 := (div_le_one hQ).mpr (by exact_mod_cast branchComplement_le i j)
  by_cases hs : g24Sign i = g24Sign j
  · have h : (highPair i j : ℝ) * (u*v) + highPairConstant i j =
        (highD : ℝ) * ((1-t)*0+t*(p-outside)) := by
      unfold highPair highPairConstant highLength
      rw [if_pos hs, if_pos hs]
      dsimp only [t,p,outside,inside]
      push_cast
      norm_num [highD,highQ]
      ring
    rw [h]
    change _ ≤ (highD : ℝ) * (if g24Sign i = g24Sign j then max 0 (p-outside) else max (-inside) (-p))
    rw [if_pos hs]
    exact mul_le_mul_of_nonneg_left (weighted_le_max _ _ t ht0 ht1) hD
  · have h : (highPair i j : ℝ) * (u*v) + highPairConstant i j =
        (highD : ℝ) * ((1-t)*(-inside)+t*(-p)) := by
      unfold highPair highPairConstant highLength
      rw [if_neg hs, if_neg hs]
      dsimp only [t,p,inside]
      push_cast
      norm_num [highD,highQ]
      ring
    rw [h]
    change _ ≤ (highD : ℝ) * (if g24Sign i = g24Sign j then max 0 (p-outside) else max (-inside) (-p))
    rw [if_neg hs]
    exact mul_le_mul_of_nonneg_left (weighted_le_max _ _ t ht0 ht1) hD

private theorem highA_real (i : ℕ) : (highA i : ℝ) = (highD : ℝ) * g24RealAlpha i := by
  unfold highA g24RealAlpha
  rw [show highD / 300304 = 1319413953331200 by decide +kernel]
  push_cast
  norm_num [highD]
  ring

private theorem highBeta_real (i : ℕ) : (highBeta i : ℝ) = (highD : ℝ) * g24RealBeta i := by
  unfold highBeta g24RealBeta
  rw [show highD / 1801824 = 219902325555200 by decide +kernel]
  push_cast
  norm_num [highD]
  ring

private theorem listSum_eq_sum_get (f : List ℤ) :
    f.sum = ∑ i ∈ range f.length, f[i]?.getD 0 := by
  induction f with
  | nil => simp
  | cons a f ih =>
    rw [List.length_cons, sum_range_succ']
    simp [ih, add_comm]

theorem highObjective_le (hConst : ∀ i < 130, constantRowCheck i = true) (y : ℕ → ℝ) :
    highObjectiveCoeffs.evaluate 130 y ≤ (highD : ℝ) * g24Objective y := by
  have hConstLen : highConstantRows.length = 130 := by decide +kernel
  have hc : ((highConstantRows.sum : ℤ) : ℝ) = ∑ i ∈ range 130, ∑ j ∈ range 130,
      (highPairConstant i j : ℝ) := by
    rw [listSum_eq_sum_get, hConstLen, Int.cast_sum]
    apply sum_congr rfl
    intro i hi
    have h := of_decide_eq_true (hConst i (mem_range.mp hi))
    rw [sum_map_range] at h
    rw [← h, Int.cast_sum]
  have hdiag (i j : ℕ) : (highObjectiveCoeffs.pair i j : ℝ) * (y i * y j) =
      (highPair i j : ℝ) * (y i * y j) +
      if i = j then (highBeta i : ℝ) * (y i)^2 else 0 := by
    by_cases hij : i = j
    · subst j
      simp [highObjectiveCoeffs, pow_two, add_mul]
    · simp [highObjectiveCoeffs, hij]
  have hdiagSum : (∑ i ∈ range 130, ∑ j ∈ range 130,
          if i = j then (highBeta i : ℝ) * (y i)^2 else 0) =
        ∑ i ∈ range 130, (highBeta i : ℝ) * (y i)^2 := by
    apply sum_congr rfl
    intro i hi
    simp [hi]
  have hp := sum_le_sum (s := range 130) (fun i _ =>
    sum_le_sum (s := range 130) (fun j _ => highPair_le i j (y i) (y j)))
  simp_rw [sum_add_distrib, ← mul_sum] at hp
  unfold Coefficients.evaluate evq g24Objective cellCount
  rw [show highObjectiveCoeffs.constant = highConstantRows.sum from rfl]
  simp_rw [hdiag, sum_add_distrib, hdiagSum, hc, show highObjectiveCoeffs.linear = highA from rfl,
    highA_real, highBeta_real, mul_add, mul_sum]
  have ha : (∑ x ∈ range 130, (highD : ℝ) * g24RealAlpha x * y x) =
      ∑ x ∈ range 130, (highD : ℝ) * (g24RealAlpha x * y x) :=
    sum_congr rfl (fun i _ => by ring)
  have hb : (∑ x ∈ range 130, (highD : ℝ) * g24RealBeta x * y x ^ 2) =
      ∑ x ∈ range 130, (highD : ℝ) * (g24RealBeta x * y x ^ 2) :=
    sum_congr rfl (fun i _ => by ring)
  rw [ha, hb]
  simp_rw [← mul_sum]
  linarith only [hp]

end OMA.Erdos1186High

end

section

/- Soundness of the high certificate once its finite row tests pass. -/

namespace OMA.Erdos1186High

open Finset OMA.Erdos1186Region2 OMA.Erdos1186SnivelyForms
open scoped BigOperators

def highKeptCoeffs : Coefficients where
  constant := keptC 130 highRetained
  linear := keptL 130 highLength highRetained
  pair := keptQ highLength highRetained

def highSurplus (t : Coefficients) : Coefficients :=
  surplus highObjectiveCoeffs highKeptCoeffs t highMatrix

def budgetCheck (t : Coefficients) (i : ℕ) : Bool :=
  decide (0 ≤ rowBudget 130 (highSurplus t) highHint highPrefer i)

def dominanceCheck (i : ℕ) : Bool := residualCheck 131 highResidual i

private theorem kept_nonneg (y : ℕ → ℝ) (hy : ∀ i < 130, 0 ≤ y i ∧ y i ≤ 1)
    (hm0 : (3/10 : ℝ) ≤ g24Mass y) (hm1 : g24Mass y ≤ (2/5 : ℝ)) :
    0 ≤ highKeptCoeffs.evaluate 130 y := by
  have hm : (Rr : ℝ) * g24Mass y = ∑ i ∈ range 130, ((20*highLength i : ℤ) : ℝ) * y i := by
    unfold g24Mass cellCount Rr
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    unfold highLength
    push_cast
    ring
  have hkeep := keptTable_nonneg 130 highLength highRetained
    (fun _ _ => by unfold highRetained; positivity)
    (fun _ _ _ _ => by unfold highRetained; positivity)
    (by decide) (by decide) (by decide)
    (fun _ _ => by unfold highRetained; positivity)
    (fun _ _ => by unfold highRetained; positivity)
  change 0 ≤ evq 130 (keptC 130 highRetained) (keptL 130 highLength highRetained)
    (keptQ highLength highRetained) y
  rw [kept_evq 130 highLength highRetained (g24Mass y) y hm]
  exact mul_nonneg (by norm_num [highWeightScale])
    (FD.FSr_nonneg _ hkeep _ _ _ _ hy hm0 hm1)

theorem high_box_of_checks (t : Coefficients)
    (ht : ∀ y : ℕ → ℝ, (∀ i < 130, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ t.evaluate 130 y)
    (hConst : ∀ i < 130, constantRowCheck i = true)
    (hDom : ∀ i < 131, dominanceCheck i = true)
    (hBudget : ∀ i < 130, budgetCheck t i = true) (hZero : (highSurplus t).constant = 0)
    (y : ℕ → ℝ) (hy : ∀ i < 130, 0 ≤ y i ∧ y i ≤ 1)
    (hm0 : (3/10 : ℝ) ≤ g24Mass y) (hm1 : g24Mass y ≤ (2/5 : ℝ)) :
    0 ≤ g24Objective y := by
  have hC : ∀ row ∈ highCholesky, row.length ≤ 131 := by
    have h : highCholesky.all (fun row => decide (row.length ≤ 131)) = true := by decide +kernel
    intro row hrow
    exact of_decide_eq_true (List.all_eq_true.mp h row hrow)
  have hSym : ∀ i j, highResidual i j = highResidual j i :=
    residualEntry_symm 536870912 highResidualDiagonal highResidualRows
  have hPSD := gramResidual_nonneg 131 highResidual highCholesky hSym hC hDom
    (fun k => if k=0 then 1 else y (k-1))
  have hMain := high_decomposition 130 highObjectiveCoeffs highKeptCoeffs t highMatrix
    (gramResidual_symm highResidual highCholesky hSym) highHint highPrefer hZero y
  change _ = _ + _ + _ + (evq 130 0 (rowBudget 130 (highSurplus t) highHint highPrefer)
    (OMA.Erdos1186Low.yy (highSurplus t).pair) y + _) at hMain
  have hYY : 0 ≤ evq 130 0 (rowBudget 130 (highSurplus t) highHint highPrefer)
      (OMA.Erdos1186Low.yy (highSurplus t).pair) y := by
    unfold evq
    rw [Int.cast_zero, zero_add]
    apply add_nonneg
    · apply sum_nonneg
      intro i hi
      exact mul_nonneg (by exact_mod_cast of_decide_eq_true (hBudget i (mem_range.mp hi)))
        (hy i (mem_range.mp hi)).1
    · exact sum_nonneg fun i hi => sum_nonneg fun j hj =>
        mul_nonneg (by exact_mod_cast OMA.Erdos1186Low.yy_nonneg (highSurplus t).pair i j)
          (mul_nonneg (hy i (mem_range.mp hi)).1 (hy j (mem_range.mp hj)).1)
  have hYO : 0 ≤ ∑ i ∈ range 130, ∑ j ∈ range 130,
      (OMA.Erdos1186Low.yo (highSurplus t).pair highHint highPrefer i j : ℝ) * (y i * (1-y j)) := by
    exact sum_nonneg fun i hi => sum_nonneg fun j hj =>
      mul_nonneg (by exact_mod_cast OMA.Erdos1186Low.yo_nonneg (highSurplus t).pair highHint highPrefer i j)
        (mul_nonneg (hy i (mem_range.mp hi)).1 (sub_nonneg.mpr (hy j (mem_range.mp hj)).2))
  have h : 0 ≤ highObjectiveCoeffs.evaluate 130 y := by
    rw [hMain]
    exact add_nonneg (add_nonneg (add_nonneg hPSD (kept_nonneg y hy hm0 hm1))
      (mul_nonneg (by norm_num [highWeightScale]) (ht y hy))) (add_nonneg hYY hYO)
  exact nonneg_of_mul_nonneg_right (h.trans (highObjective_le hConst y)) (by norm_num [highD])

end OMA.Erdos1186High

end

section

/-
Copyright 2026 Chandler Snively. Apache License, Version 2.0.
Adapted from P1186ExCertTri.lean and the quadratic polynomial operations in
P1186ExCertLib.lean, erdos-1186 v1.0.0 commit
0b0155ead09841892690b9f9c469d1ff0edaff4c.
https://github.com/dreadpiratechan/erdos-1186/tree/v1.0.0
The underlying mathematical argument is due to Carlos Toledo.
Changes isolate the triangle terms and exact coefficient semantics from the
upstream certificate loader. Numerical data are licensed separately under
CC BY 4.0 and do not appear in this module.
-/

namespace OMA.Erdos1186HighTriangles

open Finset
open scoped BigOperators

/-- `c0 + Σ l_i y_i + Σ_{ij} q_ij y_i y_j`. -/
noncomputable def evq (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) : ℝ :=
  (c0 : ℝ) + ∑ i ∈ range n, (l i : ℝ) * y i + ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)

theorem evq_add (n : ℕ) (c0 c0' : ℤ) (l l' : ℕ → ℤ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (c0 + c0') (fun i => l i + l' i) (fun i j => q i j + q' i j) y
      = evq n c0 l q y + evq n c0' l' q' y := by
  unfold evq
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem evq_neg (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (-c0) (fun i => -l i) (fun i j => -q i j) y = -evq n c0 l q y := by
  unfold evq
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem evq_smul (n : ℕ) (u c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    (u : ℝ) * evq n c0 l q y = evq n (u * c0) (fun i => u * l i) (fun i j => u * q i j) y := by
  unfold evq
  have h1 : (u : ℝ) * ∑ i ∈ range n, (l i : ℝ) * y i = ∑ i ∈ range n, ((u * l i : ℤ) : ℝ) * y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : (u : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, ((u * q i j : ℤ) : ℝ) * (y i * y j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [mul_add, mul_add, h1, h2]
  push_cast
  ring

/- ### One triangle -/

structure TriT where
  i : ℕ
  j : ℕ
  k : ℕ
  s1 : ℤ
  s2 : ℤ
  s3 : ℤ
  w : ℤ

def TriT.ok (n : ℕ) (t : TriT) : Bool :=
  decide (t.i < n ∧ t.j < n ∧ t.k < n ∧ (t.s1 = 1 ∨ t.s1 = -1) ∧ (t.s2 = 1 ∨ t.s2 = -1) ∧
    (t.s3 = 1 ∨ t.s3 = -1) ∧ t.s1 * t.s2 * t.s3 = 1 ∧ 0 ≤ t.w)

noncomputable def triv (t : TriT) (y : ℕ → ℝ) : ℝ :=
  1 + (t.s1 : ℝ) * ((1 - 2 * y t.i) * (1 - 2 * y t.j)) + (t.s2 : ℝ) * ((1 - 2 * y t.j) * (1 - 2 * y t.k))
    + (t.s3 : ℝ) * ((1 - 2 * y t.i) * (1 - 2 * y t.k))

theorem tri_ineq (u v w : ℝ) (s1 s2 s3 : ℤ) (hu1 : -1 ≤ u) (hu2 : u ≤ 1) (hv1 : -1 ≤ v) (hv2 : v ≤ 1)
    (hw1 : -1 ≤ w) (hw2 : w ≤ 1) (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1) (h3 : s3 = 1 ∨ s3 = -1)
    (hp : s1 * s2 * s3 = 1) :
    0 ≤ 1 + (s1 : ℝ) * (u * v) + (s2 : ℝ) * (v * w) + (s3 : ℝ) * (u * w) := by
  have pu : 0 ≤ 1 + u := by linarith
  have mu : 0 ≤ 1 - u := by linarith
  have pv : 0 ≤ 1 + v := by linarith
  have mv : 0 ≤ 1 - v := by linarith
  have pw : 0 ≤ 1 + w := by linarith
  have mw : 0 ≤ 1 - w := by linarith
  have A := mul_nonneg (mul_nonneg pu pv) pw
  have B := mul_nonneg (mul_nonneg mu mv) mw
  have C := mul_nonneg (mul_nonneg pu pv) mw
  have D := mul_nonneg (mul_nonneg mu mv) pw
  have E := mul_nonneg (mul_nonneg pu mv) mw
  have F := mul_nonneg (mul_nonneg mu pv) pw
  have G := mul_nonneg (mul_nonneg pu mv) pw
  have H := mul_nonneg (mul_nonneg mu pv) mw
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    first
    | (exfalso; norm_num at hp; done)
    | (push_cast; nlinarith [A, B, C, D, E, F, G, H])

theorem triv_nonneg (t : TriT) (n : ℕ) (ht : t.ok n = true) (y : ℕ → ℝ) (hy : ∀ i < n, 0 ≤ y i ∧ y i ≤ 1) :
    0 ≤ triv t y := by
  unfold TriT.ok at ht
  obtain ⟨hi, hj, hk, h1, h2, h3, hp, _⟩ := of_decide_eq_true ht
  obtain ⟨a0, a1⟩ := hy t.i hi
  obtain ⟨b0, b1⟩ := hy t.j hj
  obtain ⟨c0, c1⟩ := hy t.k hk
  unfold triv
  exact tri_ineq (1 - 2 * y t.i) (1 - 2 * y t.j) (1 - 2 * y t.k) t.s1 t.s2 t.s3 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) h1 h2 h3 hp

/- ### Coefficients of one triangle in `evq` -/

def tc (t : TriT) : ℤ := 1 + t.s1 + t.s2 + t.s3

def tl (t : TriT) (a : ℕ) : ℤ :=
  -2 * ((if a = t.i then t.s1 + t.s3 else 0) + (if a = t.j then t.s1 + t.s2 else 0)
    + (if a = t.k then t.s2 + t.s3 else 0))

def tq (t : TriT) (a b : ℕ) : ℤ :=
  4 * ((if a = t.i ∧ b = t.j then t.s1 else 0) + (if a = t.j ∧ b = t.k then t.s2 else 0)
    + (if a = t.i ∧ b = t.k then t.s3 else 0))

theorem sum_if_eq (n i : ℕ) (hi : i < n) (f : ℕ → ℝ) :
    ∑ a ∈ range n, (if a = i then f a else 0) = f i := by
  rw [Finset.sum_ite_eq']
  simp [hi]

theorem sum2_if (n i j : ℕ) (hi : i < n) (hj : j < n) (f : ℕ → ℕ → ℝ) :
    ∑ a ∈ range n, ∑ b ∈ range n, (if a = i ∧ b = j then f a b else 0) = f i j := by
  have : ∀ a b : ℕ, (if a = i ∧ b = j then f a b else 0) = if a = i then (if b = j then f a b else 0) else 0 := by
    intro a b
    by_cases h1 : a = i <;> by_cases h2 : b = j <;> simp [h1, h2]
  simp only [this]
  have e : ∀ a ∈ range n, ∑ b ∈ range n, (if a = i then (if b = j then f a b else 0) else 0)
      = if a = i then f a j else 0 := by
    intro a _
    by_cases h1 : a = i
    · simp only [h1, if_true]
      rw [Finset.sum_ite_eq']
      simp [hj]
    · simp [h1]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
  simp [hi]

theorem evq_tri (n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (hk : t.k < n) (y : ℕ → ℝ) :
    evq n (tc t) (tl t) (tq t) y = triv t y := by
  unfold evq
  have hl : ∑ a ∈ range n, ((tl t a : ℤ) : ℝ) * y a
      = (∑ a ∈ range n, (if a = t.i then -2 * ((t.s1 : ℝ) + t.s3) * y a else 0))
        + (∑ a ∈ range n, (if a = t.j then -2 * ((t.s1 : ℝ) + t.s2) * y a else 0))
        + (∑ a ∈ range n, (if a = t.k then -2 * ((t.s2 : ℝ) + t.s3) * y a else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    unfold tl
    push_cast
    split_ifs <;> ring
  have hq : ∑ a ∈ range n, ∑ b ∈ range n, ((tq t a b : ℤ) : ℝ) * (y a * y b)
      = (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.i ∧ b = t.j then 4 * (t.s1 : ℝ) * (y a * y b) else 0))
        + (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.j ∧ b = t.k then 4 * (t.s2 : ℝ) * (y a * y b) else 0))
        + (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.i ∧ b = t.k then 4 * (t.s3 : ℝ) * (y a * y b) else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    unfold tq
    push_cast
    split_ifs <;> ring
  rw [hl, hq, sum_if_eq n t.i hi, sum_if_eq n t.j hj, sum_if_eq n t.k hk,
    sum2_if n t.i t.j hi hj (fun a b => 4 * (t.s1 : ℝ) * (y a * y b)),
    sum2_if n t.j t.k hj hk (fun a b => 4 * (t.s2 : ℝ) * (y a * y b)),
    sum2_if n t.i t.k hi hk (fun a b => 4 * (t.s3 : ℝ) * (y a * y b))]
  unfold triv tc
  push_cast
  ring

/- ### Sums over a list of triangles -/

def cS (ts : List TriT) : ℤ := (ts.map (fun t => t.w * tc t)).sum
def lS (ts : List TriT) (a : ℕ) : ℤ := (ts.map (fun t => t.w * tl t a)).sum
def qS (ts : List TriT) (a b : ℕ) : ℤ := (ts.map (fun t => t.w * tq t a b)).sum

theorem evq_triS (n : ℕ) (y : ℕ → ℝ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) →
    evq n (cS ts) (lS ts) (qS ts) y = (ts.map (fun t => (t.w : ℝ) * triv t y)).sum
  | [], _ => by simp [cS, lS, qS, evq]
  | t :: ts, h => by
      have ht : t.ok n = true := h t (by simp)
      have hts : ∀ s ∈ ts, s.ok n = true := fun s hs => h s (by simp [hs])
      have ih := evq_triS n y ts hts
      unfold TriT.ok at ht
      obtain ⟨hi, hj, hk, _⟩ := of_decide_eq_true ht
      have e1 := evq_tri n t hi hj hk y
      have e2 := evq_smul n t.w (tc t) (tl t) (tq t) y
      have e3 := evq_add n (t.w * tc t) (cS ts) (fun a => t.w * tl t a) (lS ts) (fun a b => t.w * tq t a b)
        (qS ts) y
      have hc : cS (t :: ts) = t.w * tc t + cS ts := by simp [cS]
      have hl : lS (t :: ts) = fun a => t.w * tl t a + lS ts a := by funext a; simp [lS]
      have hq : qS (t :: ts) = fun a b => t.w * tq t a b + qS ts a b := by funext a b; simp [qS]
      rw [hc, hl, hq, e3, ← e2, e1, ih]
      simp

theorem list_sum_nonneg_of (n : ℕ) (y : ℕ → ℝ) (hy : ∀ i < n, 0 ≤ y i ∧ y i ≤ 1) :
    ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → 0 ≤ (ts.map (fun t => (t.w : ℝ) * triv t y)).sum
  | [], _ => by simp
  | t :: ts, h => by
      have ht : t.ok n = true := h t (by simp)
      have hts : ∀ s ∈ ts, s.ok n = true := fun s hs => h s (by simp [hs])
      have ih := list_sum_nonneg_of n y hy ts hts
      have hw : (0 : ℝ) ≤ t.w := by
        unfold TriT.ok at ht
        obtain ⟨_, _, _, _, _, _, _, hw⟩ := of_decide_eq_true ht
        exact_mod_cast hw
      have := mul_nonneg hw (triv_nonneg t n ht y hy)
      simp only [List.map_cons, List.sum_cons]
      linarith


/-- The aggregate certificate polynomial is nonnegative on the real box. -/
theorem aggregate_nonneg (n : ℕ) (y : ℕ → ℝ)
    (hy : ∀ i < n, 0 ≤ y i ∧ y i ≤ 1) (ts : List TriT)
    (h : ∀ t ∈ ts, t.ok n = true) :
    0 ≤ evq n (cS ts) (lS ts) (qS ts) y := by
  rw [evq_triS n y ts h]
  exact list_sum_nonneg_of n y hy ts h

end OMA.Erdos1186HighTriangles

end

section

/-
Check one packed word per row of triangle coefficients. The word for one
triangle contains at most two occupied columns in an ordered row. Exact
equality of signed words determines the coefficients when they fit the base.
-/

namespace OMA.Erdos1186HighTriangles

/-- Little-endian packing with signed integer coefficients. -/
def pack (base : ℤ) : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, f => f 0 + base * pack base n (fun i => f (i + 1))

private theorem pack_zero (base : ℤ) (n : ℕ) :
    pack base n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pack, ih]

private theorem pack_affine (base : ℤ) (n : ℕ) (c : ℤ) (f g : ℕ → ℤ) :
    pack base n (fun i => c * f i + g i) = c * pack base n f + pack base n g := by
  induction n generalizing f g with
  | zero => simp [pack]
  | succ n ih =>
      simp only [pack, ih]
      ring

private theorem pack_add (base : ℤ) (n : ℕ) (f g : ℕ → ℤ) :
    pack base n (fun i => f i + g i) = pack base n f + pack base n g := by
  simpa only [one_mul] using pack_affine base n 1 f g

private theorem pack_mul (base : ℤ) (n : ℕ) (c : ℤ) (f : ℕ → ℤ) :
    pack base n (fun i => c * f i) = c * pack base n f := by
  simpa only [add_zero, pack_zero] using pack_affine base n c f (fun _ => 0)

private theorem pack_single (base : ℤ) (n j : ℕ) (x : ℤ) (hj : j < n) :
    pack base n (fun i => if i = j then x else 0) = x * base ^ j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
        have he : (fun i : ℕ => if i + 1 = 0 then x else 0) = fun _ => 0 := by
          funext i
          simp
        simp only [pack, he, pack_zero, mul_zero, add_zero, pow_zero, mul_one, if_true]
    | succ j =>
        have he : (fun i : ℕ => if i + 1 = j + 1 then x else 0) =
            fun i => if i = j then x else 0 := by
          funext i
          simp
        have hj' : j < n := Nat.lt_of_succ_lt_succ hj
        change (if (0 : ℕ) = j + 1 then x else 0) +
          base * pack base n (fun i => if i + 1 = j + 1 then x else 0) = x * base ^ (j + 1)
        rw [he, ih j hj', pow_succ, if_neg (Ne.symm (Nat.succ_ne_zero j)), zero_add]
        ring

private theorem pack_masked_slot (base : ℤ) (n j : ℕ) (x : ℤ)
    (p : Prop) [Decidable p] (hj : j < n) :
    pack base n (fun i => if p ∧ i = j then x else 0) = if p then x * base ^ j else 0 := by
  by_cases hp : p
  · simpa only [hp, true_and, if_true] using pack_single base n j x hj
  · simp only [hp, false_and, if_false, pack_zero]

/-- A row contribution reads only the three edge positions in a triangle. -/
def trianglePairWord (base : ℤ) (row : ℕ) (t : TriT) : ℤ :=
  4 * ((if row = t.i then t.s1 * base ^ t.j else 0) +
    (if row = t.j then t.s2 * base ^ t.k else 0) +
    (if row = t.i then t.s3 * base ^ t.k else 0))

/-- Exactly one scan of the decoded triangle data per row. -/
def pairWord (base : ℤ) (row : ℕ) (ts : List TriT) : ℤ :=
  (ts.map fun t => t.w * trianglePairWord base row t).sum

/-- Keep the concrete kernel sums within the size of one decoding group. -/
def groupedSum (f : TriT → ℤ) (groups : List (List TriT)) : ℤ :=
  (groups.map fun ts => (ts.map f).sum).sum

theorem groupedSum_eq_flatten (f : TriT → ℤ) (groups : List (List TriT)) :
    groupedSum f groups = (groups.flatten.map f).sum := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      change (group.map f).sum + groupedSum f groups =
        ((group ++ groups.flatten).map f).sum
      rw [ih, List.map_append, List.sum_append]

theorem groupedPairWord_eq (base : ℤ) (row : ℕ) (groups : List (List TriT)) :
    groupedSum (fun t => t.w * trianglePairWord base row t) groups =
      pairWord base row groups.flatten :=
  groupedSum_eq_flatten _ _

theorem groupedLinear_eq (row : ℕ) (groups : List (List TriT)) :
    groupedSum (fun t => t.w * tl t row) groups = lS groups.flatten row :=
  groupedSum_eq_flatten _ _

theorem groupedConstant_eq (groups : List (List TriT)) :
    groupedSum (fun t => t.w * tc t) groups = cS groups.flatten :=
  groupedSum_eq_flatten _ _

private theorem trianglePairWord_eq (base : ℤ) (n row : ℕ) (t : TriT)
    (hj : t.j < n) (hk : t.k < n) :
    pack base n (tq t row) = trianglePairWord base row t := by
  unfold tq trianglePairWord
  rw [pack_mul, pack_add, pack_add,
    pack_masked_slot base n t.j t.s1 _ hj,
    pack_masked_slot base n t.k t.s2 _ hk,
    pack_masked_slot base n t.k t.s3 _ hk]

theorem pairWord_eq (base : ℤ) (n row : ℕ) (ts : List TriT)
    (h : ∀ t ∈ ts, t.ok n = true) :
    pairWord base row ts = pack base n (qS ts row) := by
  induction ts with
  | nil => exact (pack_zero base n).symm
  | cons t ts ih =>
      have ht := h t (by simp)
      have hts : ∀ u ∈ ts, u.ok n = true := fun u hu => h u (List.mem_cons_of_mem _ hu)
      unfold TriT.ok at ht
      obtain ⟨_, hj, hk, _⟩ := of_decide_eq_true ht
      unfold pairWord
      simp only [List.map_cons, List.sum_cons]
      rw [show qS (t :: ts) row = (fun j => t.w * tq t row j + qS ts row j) by
        funext j
        simp [qS], pack_affine, trianglePairWord_eq base n row t hj hk]
      exact congrArg (t.w * trianglePairWord base row t + ·) (ih hts)

private theorem first_slot (radius x tail : ℤ) (hx : -radius ≤ x ∧ x < radius) :
    (x + (2 * radius) * tail + radius) % (2 * radius) = x + radius := by
  calc
    _ = (x + radius + tail * (2 * radius)) % (2 * radius) := by
      congr 1
      ring
    _ = (x + radius) % (2 * radius) := Int.add_mul_emod_self_right _ _ _
    _ = x + radius := Int.emod_eq_of_lt (by omega) (by omega)

/-- Equality of signed words can be checked before decoding each coefficient. -/
theorem pack_entries_eq {radius : ℤ} (hr : 0 < radius) {n : ℕ}
    {f g : ℕ → ℤ}
    (hf : ∀ i < n, -radius ≤ f i ∧ f i < radius)
    (hg : ∀ i < n, -radius ≤ g i ∧ g i < radius)
    (h : pack (2 * radius) n f = pack (2 * radius) n g) :
    ∀ i < n, f i = g i := by
  induction n generalizing f g with
  | zero => omega
  | succ n ih =>
      let ft := pack (2 * radius) n (fun i => f (i + 1))
      let gt := pack (2 * radius) n (fun i => g (i + 1))
      change f 0 + (2 * radius) * ft = g 0 + (2 * radius) * gt at h
      have hzero : f 0 = g 0 := by
        have hz := congrArg (fun a : ℤ => (a + radius) % (2 * radius)) h
        rw [first_slot radius _ _ (hf 0 (Nat.zero_lt_succ n)),
          first_slot radius _ _ (hg 0 (Nat.zero_lt_succ n))] at hz
        omega
      rw [hzero] at h
      have htail : ft = gt := mul_left_cancel₀ (by omega : 2 * radius ≠ 0)
        (add_left_cancel h)
      intro i hi
      cases i with
      | zero => exact hzero
      | succ i =>
          exact ih
            (f := fun j => f (j + 1)) (g := fun j => g (j + 1))
            (fun j hj => hf (j + 1) (Nat.succ_lt_succ hj))
            (fun j hj => hg (j + 1) (Nat.succ_lt_succ hj))
            htail i (Nat.lt_of_succ_lt_succ hi)

def weightSum (ts : List TriT) : ℤ := (ts.map TriT.w).sum

private theorem tq_abs_le (n : ℕ) (t : TriT) (h : t.ok n = true) (i j : ℕ) :
    |tq t i j| ≤ 12 := by
  unfold TriT.ok at h
  obtain ⟨_, _, _, h1, h2, h3, _, _⟩ := of_decide_eq_true h
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    simp only [tq, h1, h2, h3] <;> split_ifs <;> norm_num

private theorem qS_abs_le (n : ℕ) (ts : List TriT)
    (h : ∀ t ∈ ts, t.ok n = true) (i j : ℕ) :
    |qS ts i j| ≤ 12 * weightSum ts := by
  induction ts with
  | nil => simp [qS, weightSum]
  | cons t ts ih =>
      have ht := h t (by simp)
      have hts : ∀ u ∈ ts, u.ok n = true := fun u hu => h u (List.mem_cons_of_mem _ hu)
      have hw : 0 ≤ t.w := by
        unfold TriT.ok at ht
        obtain ⟨_, _, _, _, _, _, _, hw⟩ := of_decide_eq_true ht
        exact hw
      change |t.w * tq t i j + qS ts i j| ≤ 12 * (t.w + weightSum ts)
      calc
        _ ≤ |t.w * tq t i j| + |qS ts i j| := abs_add_le _ _
        _ ≤ t.w * 12 + 12 * weightSum ts := by
          rw [abs_mul, abs_of_nonneg hw]
          exact add_le_add (mul_le_mul_of_nonneg_left (tq_abs_le n t (h t (by simp)) i j) hw) (ih hts)
        _ = _ := by ring

/-- The cached quadratic coefficients need just one checked word per row. -/
theorem quadratic_cache_eq (n : ℕ) (ts : List TriT) (cached : ℕ → ℕ → ℤ)
    (h : ∀ t ∈ ts, t.ok n = true) {radius : ℤ} (hr : 0 < radius)
    (hweight : 12 * weightSum ts < radius)
    (hcache : ∀ i < n, ∀ j < n, -radius ≤ cached i j ∧ cached i j < radius)
    (hrow : ∀ i < n, pairWord (2 * radius) i ts = pack (2 * radius) n (cached i)) :
    ∀ i < n, ∀ j < n, qS ts i j = cached i j := by
  intro i hi
  apply pack_entries_eq hr
  · intro j _
    have hj := (abs_lt.mp ((qS_abs_le n ts h i j).trans_lt hweight))
    exact ⟨hj.1.le, hj.2⟩
  · exact hcache i hi
  · rw [← pairWord_eq (2 * radius) n i ts h]
    exact hrow i hi

end OMA.Erdos1186HighTriangles

end

section

/-
High-region triangle data from Chandler Snively, Copyright 2026, CC BY 4.0.
https://github.com/dreadpiratechan/erdos-1186/blob/v1.0.0/computation/theorem-c/data/cert_region3.json
https://creativecommons.org/licenses/by/4.0/
Release 0b0155ead09841892690b9f9c469d1ff0edaff4c.
Source SHA-256 8e118f99b502a9222ba5fb859f0f6a05468a3f84369a509d2243ca0878d4f304.
The mathematical argument is due to Carlos Toledo. The adapted data are grouped
by the first vertex and indexed by the second, with two packed words per row.
The decoder is independently written.
-/

namespace OMA.Erdos1186HighBuckets

structure SourceRow where
  buckets : ℕ
  weightWidth : ℕ
  indexWord : ℕ
  triangleWord : ℕ

def sourceRows : List SourceRow := [
  ⟨63, 23, 0xb1ddc262b902c4700586be0b0974160ae04bf5b057cb412f16425d2c04b857096cac12d1542592a04b053095ca40ab5281562482ab4609528a0aa110153a182a6420d468212850024f9f829e3e0d367a5244f03471d888a3a051272320ce03401bbe613604c06a1178cc42d1788562e209c5a391cb0720158e392a1c645228b4a0315138428261c424a107c9010f11861b1f04343a4844701080d040e19041a20102c3c1050602090a04101010181c20203080004, 0x1853400050ee60027be2af001ac9a800027e8be1430db5dc12c96aee019ffd801657cabb808ddb6000b1c5b0201cb998003508cc0807b776000fd32d0201d6a28003608f408075fda000e280d0201e2e68003d21340808d1ba00b0d17502031a868018c76740808f77a00006a9af80018097c012536bc0b3d915e0062a3aee020fd58001160cc0006de26037f4c9c8a10f676440c5e3b212af916570d3d91a8a01bf968100765340003efaa000588350173e2195b5278c6ac80d7eea000f372ab708180959b53444ac032ca1d5c21367eac20652b550a540daa32836c50d617bd28402139680266842ac072e7bd5002ad7500f587535741359dab4381d1d54743276a803e9d95c010698ac818a8bd5c1072ceac0ae29f5502a94faa00252fdddda995aba4c91395c0015e3bb80ab615cc05abdae403c0bd7100c1eeb4809f7a5a00675dace031af9660b50f5b2959b1bd900c4926c60158d36245c95cae8570be570126b6ab61204055a021464ac80a1cb56003a706ae0187035600d9ffaa80fbb7d5017ffe6a63fcbbf52007d9ba881edc45180342d28a0611d54408ba14a183602f5080675ba8288c56d451530efb0399305d3809068b0202093d800265349e1af9af4e00b89ab0201ca25800337d69e14dcb84e00dafcb0201e391801641509e868a084f0a523427683ca3139020f909c007f4c4d81298630201d9898003ba809e016afb4ec272c3a721855693801acea9b0221fb60403dc8b0008a7693c03dfd09d8dcc624e46c071a7003aea536030170c08083036001bf4ea780eb4413b2042e89c8800e54e00992226c0b2fb28100f9ff40061d1a8f0382c247607c41a3918a34d1c00a8558d80c27e50201c2428003bee31e01d8008e405b40c6c01ff3a800e28011e00f97c8d803a0ed0002b33e36021582ad82c81fd500aad325a04ae8d2c03408095817295ca407ab0e500272c28008943d1b00ec01d4401d8c29402080e2f006e46148092ae0a408e20cb202477c5400adce2982ab578b407ffec5803f2ae2b01d9b11500cbb10a405e85850829e352e24666e9700d9e8ca40334a500017206800121bb1b010ee39200039ca6c03d14647079f792391a2f290c0d09cc880fcb464331f99ea382b5f4c68088956321a26ff10⟩,
  ⟨42, 23, 0x13db9027a7104f2b609e16813bac82765804eaae09d158139aa82725404e2a609c148137a8026e4704da8c09b114135a2026a4304d28409a0fc1339f02663d18c078694cecf221d143a390c6e6e50b4d82159788272e14445a2078b040d1588162a1422522830a0404138804260406220808401008782000a, 0x10776c080adef60404d4430202861181010436c080879a60405725d02026a46810127934080855fa040487c50202a4b6811a2e21b2805de8604031c6b020473f950015d3ec080b21f604030eb30201cb0e8100d81d40811fbea04077f85020edbc15b5a5f62ad3fbf90d5cbc6abeac9465b355023bfaad81d73d568118c12b205f31958040effab81a711d580fb506aa04997354022a39a980c996d48061c5a86017975420095eaa082b383dc005bd52b404143d5901b1baac015d57d5c096ffeac0446cf5501b4afaa010f19d4c11be86a527734945020c96a2009cc750c02824a84010f5141004d00b90023155c4011782b6009ce958004bcdab802539d58013466aa0097d354004c9aa200250050c00912ae2004efd5d002b98ae00957f5cc045a1ae402bed571013648b400916959c0452eacc0246855d0308a0ae00d86356c02996a8a0196e58101141a9d0094336040973b276032f613a004cca9c8092206048bf0c2780745e13b02418e9d0027804e404a29b0202fe393b01635c9d0025be4e40437ab0203204d3b01672a9d0025be4e403e31b020401193b0179129d0026024e404b6250210890e3c0272251d81064a8e8011eec72021aae8103e2791e00d9c68ec05f334740090e6390102bb4080cdb78ec05bc2c74008e163900c51540807f428ec0437d474007eb63900b366c08090ab8ec02bb7502002ebd81⟩,
  ⟨6, 23, 0x1032d8205580408ae080d58200a182003c, 0x907a5dc09498af005af167803080f3c0080c65dc1c0faadd1be8d943⟩,
  ⟨22, 21, 0x12aa484534820968e092914124a2024843048e840918b41229602442904865009089c12093043f208c382c086c5420c8804170f042c1880182c50082820004, 0x54d47ae0309d35d988ce6b606f32dc80b4bbb88101036701f48ecc297c4d6c1f3e5ad032e8d5505059aa8c706591c116ab23975e2e4703eae48e0ad8e91c1173723822f554704265a8e07a6251c05cdc988162f13e0846ca7a03d0adc8098b8b80188056f01285ada03428da00859ab28103556401cfb2c6056ba58809e1fae8105ff5c02bf06b605b91d680b531ac8174eb58036abaae066075580c032aa8137c15401f532a6011eb5480affda381dc334602ae968a02f08d100e7a7a181156f420164a68205ee950009f55978180ff2e028dc65a068c3cb00a89f9581153f2a005692de040694c54f32c9000e159311b829a40030eed1c1a338aa018617420345ae820762b500157169f86adb72c108efe560b086ca81b83c93c08a291a0e2ba232211b146022b678a38627b13f95c1e2538341c44014711f802ac63e0059d47a00b1d8f0011231d16fb690c⟩,
  ⟨39, 22, 0x114de41293b82516904a0ce093d981272d824d590498b0092d5c125260e434a08828618f90811e9f823c3304766418e0c021b1782352e10625a28b0b04141582272a084a4e108c982108d041f19043c2c08744460b880c110f04201c10383410686020c0b04161018201c60103040005, 0x165c227b0322467a00cf167805ceb66a017a196f0190096f03d8c26a03ab166a04b6b26a23966d5c02691f5e00bf036900885f6800965f5c00d40d5700e3a95600dce55500a56d5401132065015dd247022b4e69016e286504d94063017407650316635e014f335e1c21865e015d224a1cd386320275ce5e00e8e64a017d765e0a941a69024d4865014d364a02ff4647065d4269164e326720572266021a10650123fe4a04e0fe690c54926601bd0865010dd64a00991a4a02782b650174014a02f99f650193354a034bfd5d02af214c01eea365017e4d4a0096021708c19247042ee76503f44d5d1269a94c02891d4a046745470431414602441b6e085eab650841514c03f7294a040609470188ad460bf6094a2a638618c772871542386e0e038c6e220086f85e00b1105e00cd161a024e620e01411a7800b4ae6e011a3a1a0151f20f03f9da0e05511607009ef15701a8db0a⟩,
  ⟨59, 21, 0xb89e42703a02df680db8c623617016bad04d55905a8b013495c2682a82cf541594a62319482622402c34705848c2af51035d2102b9410570801ad4fc2599f02b23d09607812b8c41569784ab2e154c5a2288ac44f15049c2909344e12609844a128492240522461a3888c410f9a751e24d83ac150701298d82521a04a23009405c4260b044a1408902621104842008a0301038441e5060385098694090a140812080c2010103840006, 0x257009e83340cbc0082b57720109cd20cd2e5c41b828b383004d6601a59ae0049995bc0887cb20183ed630150e4b803a339c405b1f2e009b665c015c82e2028e057006812b880ad915c012e8ab8038f55c409fc2b4010c61670244cacc0230f5700192eb88035756800675ace00d375980346b2f804bea4af610acba1e277d1c2c3bdb9a3ca93711802dac89303c588084ed2e017dae710269dcb8a3ba0912025892207661d44330352b626098d5c090aaa200e7ed73021cd2e2033965cc3035bab80c29144034994be452f2928209e32e00ed7a5c02c4527e05b119cc0afd738816aba6702d9fccc0548f97006e9d3880dcf26701cb24cc02d52970056853880b0fe67017204cc023f797017fd91f8245ba3c0bf8347c11e468f45f2651f0805823d01be46ae0e7618f82c37f1ec798d63c01f1447a043038f00337d2880617a5000d5c47201f458d4bd2932d82a7225907a75cb02e71d15c22fe42b04e0cc550365148a0508c910125c5170153ce2d04e3205207a910a00c3b92d81676a5a02070cb2052679600dd4a2b8167005602c318aa0322a91405a712200e9f22e0186e45a041e80a4076841405a2725b1d96c0ae12b1215824cda2a811e4e4502133c8806a468b8130c0148270a82802083cd200a4a9740509b2e023a6a5b051bdcb4073449641a2cd2c03692c5705b180ac0a417154113cc2a00d0ca4501606c880493490c01943178148ca2e02147c5a069208b0113f5158607c62a0306a052060fa0a00c12613815db4240161283c078485105f4c10c805b3e3c1145ecc00b90693411c031a2ff0762100cc9e3e01353c780d27d21810428280d43f0ae05e3e9100d87f17050754290512148a096149101d5ef1731fab42902caa2d2312f356c9d3b8ad03c621591879d2b03b6e6d5c2830bab03f6bf5507436ea804435514075c6a201b21d2e024dfa5a07f414b015669948267f3282e3582b64902e5681972eac88d37d5811968eae15324d58249bfaa80fa654501b2ba8805ff34b808cba96820d412c05668e520b37eca01d89aad83262f5704999eac0833bd54060eea2037f1e3e023bca5c035194b40de45948469081d07e67c364ac47868db7f10c0540a20fd12b941c0fbfec7c06b458f00f4db1d02ac863895254c4cd2be3890a8b671102fb62200554a43c0abc287027bdf13ad03de24ee32bc44130d20681768e0a019bdcf6137439ec05c393d809eb67a⟩,
  ⟨50, 22, 0x1483d028f79051cee1231b8344b6028868050ebc12154c241a914795104f09611d90c23a2082734004e47e09c4f81381d826f3804dc6e09b4d02359804692f08ce5c0998ac1329502642404c64409888413090045f1f08ba3c116c7442b8e02561b0ca62c1144543270a064b130892240920441238804450f08861c11043441e86063a0b04721410dc2411b046c0007, 0x158497c0141f97c023ad378013fdd7101301f70075e2a7b1f56567a1661027903ddb7694a798e7100f60a6e0bbc0a570151a66e305d8657028cee7800d2c677040c78690d10906804656467038f5c6601019c5d028c785c6afa145b066ec45a0243e853012ab56eada8475d00f4856e32cc23420108ca6e0269de6e01781e6e14502e3d00e5be4d035e5f4f0106433805a6875e00b1eb4b2da514531daf2852ed9620531a0aac520236274b0148df4b85a7cf510789bf4f67840f38004c2b4c01cd375e23792b4b0279575e0f7c8f4b0a4d735e1ce6a74b008b016e0127875e369d4b300965b32f01211a6e082e5d7a07e05d794fa417492069f17b0286e179017e717000e0a96e0329614002b145700138296e126a8d403f0ff940040f1d3f0b8f69290163373b00e8a26e01854b3b0495dd1c46c9d5116e9e5f517ee423182928633853d1f3371b80cf3324a4eb22988a733206047f31003cdb22437a0d0d017d7c5129254d0d09845f3b00f3eb77043065720342dd71093fc370018b45690225556802873d67029c055b03c70d5a02a2095902bf6d5801b1035701c5fb5602095b5502221754018ccb5301ee4752029eeb51031f214302630d420191414103b6c3400417ef3f02b5b33e07e3d33d0264e73c061da33b03baab3a018d312f018d292e0208bd2d0222d52c025c292b01de892a01bb4b2902d2c72802418b27023bb3260123cf250a484f240160251c019f471b01e46b1a092af31901e6ed14034f9513045cfd1202d259110439871007f56f0f02b4570e02a7070d02b9490a015d6509⟩,
  ⟨60, 23, 0x4e0f609bde81373c826d7710d2dc09a1b0133b582666704cacc099190131af02625d08c0b2097d6012f2b825d5604b8aa19654c42aa9104d510498a011292c124a3844744048c86111104121a002423f0482760900e811f9c043d300c745e18dcb821a9684332c04645608c4a811811022f21045c4010b07c2150f04281d084c3808946c4108b041f1510362818604c30a89041311101e2018303c2050704080d10081810082c10085020009, 0x68d57c005b0abe002d045f0022136f000e12573007eb4b9004e2b5c401e276e00104ce7b09f0553d0040ff5b8026902dc00d04e6e00a88038009447d7801c642dc010f635e00f9bbaf00bf0717805f9b8bc0199605e00b1e1371508f41744001ccae01c5366e09367a2e82a9ac95c263274ac0087aa7700f8ea34818d9c1a0058508cc5aa98c5b0d0ada2d04115c164047e84a80ca6027700dbfb2d0083c7960034f0ebc07201f5e15ba6dae804a395b802ba32dc05b5335e007d3137012e68d4c01b9dcdc0169285e00659326805679d78016b2696030ab75e17878429818f4414807056ebd1506645303077a29009f91d78034d30a20199196e0134bbaf00c00fd78037d96bc304df74f03661d9c0022d6d7801c4f6bc53d9e34b007d33af02b49fd2c02c1b6bc0d2f2f4b007e39af0ae820cbc0dca60bc1436a97a1b81f2bc98c040d24013716902f579d7b0cf384bc8102ae5c00221dadc0a9d0f5e0882b6a0016e1d5c00a2f1ebc2e1cf540006053af0477b050007a92a7e01bc8b5e019cce9480507dcec08bd4a28062a1913161a8a8900766c450094fba2669a221120fddf7a90870c2445bec0cea200aab7360ca19d9c10f9aecdc814c36664f74572200a1b3af05aad2cc450f99a1a00fafc51⟩,
  ⟨60, 22, 0x4d0f4099de4431b702626c08c0d6097d8812f2f025d5d04b8b8096d6c22cac84575808aaae095158129aa845153089ea4193144125a5824a4704928c211510221a184414104808008fcfc11f1f023d3b08767408e8d411c9806362f10645c08c4b421796022e2b045a5408b09411592042923045044089c841131002251f04483c1088742100e041e1b10342c08645420b8a041513042824084c4450708060b0e100e1828082c10085020009, 0x223d57c0249497c00caa57300c601720104097100dd93700136427b430aba7b428e0e7a011c4e6e0147307001d5475e01d0335e00fbe35e00d2716e010a735e0103256e0211735e014c3e6e0374445e0297505e0166505e1f180e6f01118a6e078f0073019a766e006236770c90605b073f785a04067e5d0178f35e0353ff5e02c92d7000d9356e0425435e5b603b4b00f9656e026ac35e00e3b56e02055b5e00b70e6e01e2be6e0159ee6e00da926e02f4ca6e01a8cc5eccbba74f013b4f5e0231035e198ecc53309d84520255eb5eae934053672d305221b68f4b019c8b5e011f056e01a40b5e01f71f5e016acb5ec742c351cf8bdb5100850f500016673635422b4f04f427380070ff5e00c2975e00ee5f5e00bbed6e01375b5e0096256e00d3bb5e0116fa6e0286305e62d76b4900df3b334c25873200757f2200157f2200c0156e0267a75e00e0356e025b875e00b20f5e01101b5e02e03d411140891e38b81d1d1b351d1c0a046d115bf6fb5315858352025ea51105cd87600a1fab384806df33974fbb2200b56b5e0160534c0041873400387f22003a73210180f21324b4e50d⟩,
  ⟨58, 23, 0x48bad87145a1220b21c3560484ab8905560e04aa1bfd5057d2996ef5111d6a053853cb6b2702d54b05a8924b2d143642214be431572840ae10415ba004b53f05687c0accf06569d96a23a0542725a58d8d449a848734050c660a14c0d3c169a6b2c34bc56594ca85271490462828784e38d4982199282322408604608bc602168b9821160c3c2a10705020d09821912043022284c4030807840e0e0c161a281830102858a000a, 0x427a5fc0174c2f000d2b17701c70eb68032e05e001a85aee02a9b56d00990ebf8029fa5e00184f2ee02a2ed6d005d98bc00302e5dc08402ada0170ca7f005cf73c002dd29dc044e6cda01a0da7f0061ab3c002b0c9dc05de04da021f127f00609b3c002bc99dc03ee4cfe00c8e6780061073b8063fc56c035f1eae020313560130f9aa80a998d50072ec2e6028a0968009620ad8069b756802bc42b201525d5800a4afab8058b8d580374d6aa02897b541820ada900371856c0202e2b401001f5700b209aa005c125cc01a7aab600ebb15a00707cac803b5656001cef6ae00e01756006dabaa803e7fd5006ea96a40127697300e5dab880671dd88018012b600c8b95a0061b8ac8034c5560015f96ae00cf0b56006f85aa803a6ed500285e6be02b16e5d003becbb8044235b4017e6ac200de31530052a0a880242b54001befa9e009e214e3529afa3801edf5dc01fb8a9e00c9954e004daabc002c6a5dc07fafada01961961009ddeb000833854c0352daa201790d5000e63ca7805265538013a62f0009a91770092e4b080557053c018d5a9c056bbe43004daf2780578c9fc014e14ee02f0ce7f05cc874080355b56c02021ab2011a6f570091fdab005365d54015cc28a02109e75085d6b3580303156c01c6cab200eaa1580084a9ab804463d58024b1eaa01307f54004e90a2803b1acfc034e76ae00f811730068caad8036a15680183dab200b6ed580057dfab8029ced58016cbeaa00f6ab54003696a2803a2250c0195a2e600c9136200723cad8039f356801a29ab200e451580066e1ab803541d5801a6f6aa00fe675400482ea2802c1a510020b1a861f73df36079fd19a8096eccd80f041af60161c17f00531abc0024575dc03fa12da00cc196100c5faa9804118544019eb29e00c2a54e0070769d80346a4e80130a26c0096b93500bd68bf802bc25e0011f82ee00f06d61011746a98088ab54402e37aa000fbd54f00749ca70041334ec01fce27400dd8d360064b49a8074365fc016bdaf000926d770082feb080af2354c0574eaa201aa0550007bb4a78039055380253ea76011e513a0079809b0033414d404c502fe00c82978004e92bb81057454c09a262a2021689500078aaa780352353802d1c2760141113a008de49b0069179fc033954a20149c24f008b971d0032328d803c6c4fe00ccba78005f413b80afc09440369f49e014eae3a0082fd1b0038988d404c2acfe00ce5278005a773b80b1de94403d5c49e00d2be4e00b7b91d8057608e80228846c00d4b235007bf33c046aa59440939249e02904a4e01241b1d006ab18d8032cc46a09d0024f01f49f270e38c5a040632a49e00daa64e008ded1b02e3fa91c0454b48c019f247000e632378080ec19402f430c801c36863028a292e86fa4791c6d0f3c8c17021a4500b7e1220081b98bc051db45c023b086f01d98122009e288780c20362d26d38f1502e4d38b0bd6f3c5416c49e2a012f4d4f00e3e33f8027c69e001c65cee0126224f0081231d01a12ca040ec1c4fe0152227804e8853f805a5f9e007f8d4f8bc521a1525fdc90992a2b29740dc3bc8e02a3322f011deb1701b46784824280e1800cbb97d049c01ba848b70dac1afa369801c35739⟩,
  ⟨63, 22, 0x1355cc269b904d171099ede0b39b4166b482cc630596c40b2970363ad86c45a0d82b21af96045d2b88b6561164aa1abd505552782a94b21428a127d1084ba18a92420522820a41003469f868a3e05127a2214f02419d82823a10fc7259cce02389a02703308dc6029a4b4532160c5e2b10b454394ca47261410442720784c28dc9451912062f23085a4408b06c2150d0627190c483018845820f8a841d14083626305448408888a0c1010101e1814382018686000c, 0x22e457800b5057701747578011fd977027931780183397700989278009cf277016c576f18fb2d7700737677006aba77005ccd7700d4b178013c09770425896d00ef9d7801478577032b656d00b73178010c4977029dc96d00d46d780113197704c7296d01284e7f00b46a7800d492770191ee6d0151467f00c0c67800c99a77020cca6d0179ca7f00b6527800c3fa770200ca6d0171da7f00c0467800e04277343de7810103e95a00e8b55900fefd5801750b520030bb81009f957800c195771f55556e020bc56d12e5cd650b1349640217215320ddbb4600b85577025ac56d0095d17800ca217704af496e0244a56d033d51650387f96402332953016e5d4f00aca57800c8cd770237916d2a381d620174a94f0088297700879a7700a4d27800d02a7701d1466d030d9a7f00fa4a77011bee4f010e324f03babe8100ac027800c37677022c164f051c864f0116c94507a2be6b00ccc24a00dc373e147b373b018c233a01472d5a00e4b5590111b95801429357016fdb56017f4755016977540142f73f0116e73e00ca6b3d01075f3a0a1dc7363dad5335009d0b3612f34d7b00605d790241d17f00e1717800e4a5770466d56d01712d38013a097f00ad6d7800a4257701c4f96d01b1413801b1697f00c1b97800b351770282096d056215530289f13801a5dd7f00bef17800afc9770225f53802d4e27f00e4b278011902770af1326d0214b24f02169e3904ae323802378e7f00f49678011b0e770f8aaa6d0224f64f0288f6390386023802f2427f00f742780106da7707bfce6d32aac65002829a4f029c1a390473c2387daca68102f7b27f00fc1a78011ada770572366d03a1224f02b41239047f5a3816e7be81008fda780366424f0183e63903a7a2381da9768110db9e5003be4a4f030a5e39028a7e38016f024f014cf64e02640e35241abe3400af62330114f63800c9224f0140063800a49e4f0095ce3901555a3800f87678056dda7704c61a3802617e473826d246004b6f172db8564501b69a44a6a087164a9e0f150965e94a2f06971500df757f00a701770203895001c0654f0167f9390209293801c4d950019b994f0182b5390197b13800a3ea78012f22770119824f010c3e390157aa380144d67f00c76a78015c3e7701185e3800d7e278017eee7702533a3800fd761400efd613003dfe47004836140045e613⟩,
  ⟨13, 24, 0x21777042c8210508c3089102101e041e380838581068a040b130414240824441040690000c, 0x305bbde0009b956e00e3c8d4401aee33a007668e044c96e7500025ffcd802a609240015a74dc003ff317b140184989ec84528000edc4580bd42124268204490002e8e16007a4047c01bb411e0808bbc60004dd317009b084500238091200e256444016e5b0f⟩,
  ⟨32, 23, 0x4deb8b1651c629a304514504a088093d0c12721024d410498624110c01219682422c0482560900a821f14843c2810704e18d49811a1284322408604408bc841170f92251e08463a9840704060c020b140414220824407010784000e, 0x5784b7003a275e012bfd2ee06ebd37300fe45b90057c1dc40d9b1ed2034aeb680112e5b3809009d98024d2aca034079640346bdae0312ead6c070486b4030be7590164e7ac00bcf455c0543faac0320e155022080aa00725b54c02a6a2a4017db77101e8e7b400c252d9c0558f6cc01fffb5c87f6adadb482de91d6b6afc8cc228d24715aa8b238115e091c0b668c8e00463f4b016240b7802b205ba033d3eba29e3135a068715ac864df4d1c25ebb68c1d20474500c4ab2380530091c03afa48e2b8fba4700ee8ea380adc751803e62a8e02e9714600f8dca380d0a051853a5525e0995312e00adeaa38175c84bc9d58ba5c04ada147077d95a90073e24c0024c5ea0121f2b4f3ee501a7990d1d49000decadc024afd3f00d2029f00bd964f4048712780b37513b00e1ac940521124940760ba4800814d6e0e1a18920014715b8019376b400d61359006e77ac0043a054c0c0fe2a400a6f3420067fa9f8030404f801f00a7a0102853c0dc22c9d8052144e8015b625200c5c128006bd8938059ed4986d27a24a8c4fb524005392a3889dfe4bc86b3ea5c382dfd1f19631fa1803580870120f5c480089426e008496a38099004c005119a5e0223012e1f228912110cb64800b0784488838651f⟩,
  ⟨33, 23, 0x2516504a0c6093d88226b0844b5b0494a8092518223a284454308867e0908d412099024031047e5a08f89c31d93023a23106c3e20c8786160e022b1b085234109c643120c101c1624262a203c50405898409120410221814402018786000e, 0x8ebfa8e60675186619dd763303960d1c8068030d021bde86400dd8c308130b1d94129596b601402c61cdc4f5230097191900503248c1bd5db6e00cdd7b6808366d3c00f746980055cb4b037595230021b1ce8c4f15ec20084673b0053699d048bd7d3c2754da7ebeeb613e02b02c9e807c114f009e1b27e0557113e01320c9e819d2849c04bf1a7e030b553e00ee0e9e80f531cb40758824e8097d92600e144900094f94800301d23c3a5145200bb3648f0185014bc0ddc02401f56ab19006288b80035e65bc013ef2c6011d835d00196da4002a2bd1c02204e8c008cfb3005fbe9b98968f05c010e606847a278b418b5263956dddfe46d71061a34b36fa1197559fc8c2491834a27c35524ebf280d2601ad9e8c028d7549eafa7024c04b0a11925a8ad0a84281046032f39c2a04b3ae15002e619d801a3dce806503a400077a33a016fb49004d49147819f48a3851381511⟩,
  ⟨35, 22, 0x8edec11d3d0239790470a818d540219a782324c0c5e9608b924116a4042b46045488189ce81131c0225370846680888cc11099022031083c601070bc10d9704192604304a1058904091182111f04203c083c741070e040c1620082a10084c1008802000f, 0x1bfbd81011a89810136198101dfa17c09b51a530311e2520d5b565103b5425209a9a25000d69e780495e68101e422800148de780649675d11d6475d02b8b280665f6647010eba7c04b91b750152c75e05b09b4b0692134b01d6fb4c04c232361c49123503932a3603a10e360389463605b6547b0706787a04b4747940c2d2479ede36470d5b47500814a74f0956e74f108cbb50128ae74f00d8017a03b59a3a01242f34011957333652fe222c1f884a1950f44a229ef87401b21f2f3e9e8f1f0224fd540209a14002bea93f01c5913e50bf732d2c82372c0bcd032b01dadb2a00af7e7a00bf7a79c84ce520320e5520⟩,
  ⟨38, 23, 0x1233d82457a0488a6090d40220a782404d047e9818f12c11da4823a4804728c18d8ec5189d023039045e7010b4dc1161b022b34085266109cc81131882253004485e088cb811115022126083e4830648c20b9102162008283e084c701090c8410171c122c2014541020a080013, 0x6b9b6040300830203c4676102b0f32901594f944131564a0075e5e500074113c01891da040358950001656a78049d23ae002259a038d752c8e0205736b013631ae810d69d2c0284e6ea01c5bf6b00645daf0123dbd2c097d8e94031d674b010d4ba5807ce6d3005a1ba800334334c02158b1b009b5e94407a8e46c01ebb2780245a51b00cfdb8d81f2b48f60fe7f6483bd6c324006c2c184ad060af60b0f2f4f0207479a80817e5e80b2e669a05b701400121a59a0095e1ccc0691ee641b89e13e0cec529e82d4db1d0474ed4446ea3aa21019fb8248813fc48c01e49adb6bd5ab200096e4ab8045f9558022832aa00cc3b47006dc5a3004678cbc02777e5c1183432f02e359970177c5c78aa20a63a018cf2230052c93d002c449e401eaa09001b9ea23⟩,
  ⟨42, 22, 0x1263d824b7a0494ee09255012429824752088a9e091134121a604414b04809408fd2011f21023d4114707638c4e81181c822f35045c6810b0cc414190426310c465e1880b810f96821e2c043a560870a810d94821a28083048284c8c20891040f21081a400830701058c860817040e2c200c5420089820012, 0x1f12181029f85810859377c01718d7c33db6f61020fab61032ff65109b27e5002f6625100b82e780629d68101d8c28000479e80008ff68008e77c610354246101e6cb7503c48f6b012c775e0309cf5d085ffb4b0134437e015bf37502827b6b3b6b4b5f01147f5e0613af4b02e23f4a013a1d6e02b9da3602e606360182ae5101bf0e36014f9678077f96770aa25652029afe3602088e780288fe360039327c04ea3e491d0c0a4800d3c27cc61b824965a6a2484ace8e47054ac46104c0a06102f2ec610ef9f9471934e5471bac834f051b27352f93717b0495517a068a8f4d03138f3401eec733018d9e3601fd3623355df6244daf8a2208aa8e373594aa3604ee0049041e9b4a01fb616e00df1d6dd1675720011e072f6ae2b32f0676232e051d731e06f58b1d01095e79017db4480372544a⟩,
  ⟨34, 22, 0x11fbd023e6e0878da10e9b031bb5823669046ab808d16c119ad02324c0c5e9620ad24811a40421470440861078f430d9c821a2d0432580860ac10b95021629042a50104c9430811880c220416420828801048f820816080c2a08145040089820012, 0xedf137b0115fe7b018c267b02fd1e7a2269667402a0f6710137027e00dc487800f45a740221f36b0655436b16a90f6b0b2e136b2525cf52022d5381063c5f53070713529308f457a97668566c3e6055282df054070c6a5b0dda265a03bcc85703fd0056041db45502e3d454016edc53002f6852068bcb80d02a0f4801cecf4801b856790677f24701407e5e03151e5d04bfa24c21d64f48076c1f4804b4234803320f48123d88480228244801713e7c00af686c018bf07a01d4687901f6e2486b389b510397af3621548b2409817b233268c33605959f35026a9b4f015dda477f50c32500fd0b24231b7f23023f3b5101c9a548ab4fab2403a7c3230f134323⟩,
  ⟨36, 22, 0x480ea08fdb031e35823b690474b610e16811bac823658046aae08d158119aa82325404629628b120115a3822a4604528408a1041139784252e0c445a1080b030e95841b2a0832520860a020b138215250c244820388c803110205210408401008701008a820013, 0xac327e0028867e014a927e00ad3c78016ad6740183bb6b08c4976b0667876b05559f5d060e575d03df975d02f9245d02f5685d0310805d01d9205d00e10f5304232457041a985605206c5502e314540144d853a1554b48fd48834904d1c75d03d6375c0850c35f13a7275f1006574a0eabd75d2b9e674a50066f480488ef5d09832f4805faff5f04c38f5d07c0b74802d2375d0387ff480446c85d67fd3c480537a85d0b4fc05f047ed05d009dc06c028a4e370bbe32363022be350088687a0adc3f520ea7b7515ec8332416163f530a76635226e59b5105c633362ba957260477af250477fb240283a72334530751cf9b432402fb8d37460e8522215fe32501ec5548⟩,
  ⟨41, 23, 0x26e6e08d8ca09ad8c1352d82695a04d0ae099d54232a884634b0cc09261512022923845046049e8a113510126218649420c8c82091500122190442301c765e30d4b83191684302c085c5610b0a8414148824280c424e08809810f929c1123081e4410347c2058e84091c080e361810683008c820014, 0x35319e401568cf200571a75003b113a80dffcd780756bebc02022c5e00d6922f13ac42d4c20021ea401315c570099e22a840caa15c62a8c0ac48d7685500844339003d2d9c403b50cba0128e25c01052b2d80c9d8968075bb4b202357e5800e4742b807f43158041f48aa01b74c5403b76da48a41b4d20043f86929d6ca748008433a40024ed5e401c98e9001bacb4800670ebc8072f3544029c769005a1c977018f18a88060a4d2401e0bcf20093f65e0d0cb3af033ac3d20016712f60117097a008dc6bc814dbdd780441b6961ac5e74902ae7ba400403e5e801f6a2f2041b575e00dc03a5cf80f3d240625e69004919f5e137481a480d5ead20612a069202460b48147ebbaf809cdcd20099842a201e21b48015fdc2f00518f12c19b348920339b848006cdb3c80c89d17802c3e896013b884802ca102f0068eb12c02dc089000d7ec480154811c00bb8256404e8fab0030b3b5403ada1a98110fed48059e8a84034a714100cb1e96008f4e4ac08ebca540261bf2802bd3d9382be18c98b2c38e4a9296675106103f9b007ca15e403b38e9000e6e97a00770abc8073824dc021c6a46012c545e008d262580515a17802967896076228480097022f004ce112c02d2489000ed7348⟩,
  ⟨27, 23, 0x8d96c11aad02345104669c08c92c41725042c4904568e08a918114a2042743044c820894d42119786202e083c5a0874b010e15061929082e50085890e0411840622080842080c741010e040019, 0xa9dbd7804ddbed436c8a3524dcdcda7803d04154044aacb80509c85701e7502b00f49315495c4fcb9f4a17a5b991a4fa483d23dd240a87669243b0eb743adc03b4817ffe5440e8c82822c57735e01cc8fa50318a0d7803ebd6961852db4a02679daf099ab6d282d0392a25dcd3d510122fa2f00433212c14f4909401eea05e007e4225bd20c14a809d32ab20300bd5802906baa018695d4c07ad36a40416ff5101e3faa10123145040533925803a4d12b05251a9500fc56ca00f787e4e07692b2633edcfa887811dcd8091ff6a25a20f75009a6e69c01a4c44e0139b346e131c1e22⟩,
  ⟨25, 24, 0x4345c04669820bd20216a3842b460c5088089cdc21299042331044460187ca410f14041c27142e4c204c9410911860f22041c421030802050f86071e080a3a1808701008b820016, 0x1cb41c00082246f003bae97854249b5f009b4cd300078db4a075dd1d24a430535e6904dcd7405bd3b5d42d8b7d70085c2f6800de9bd98008cd75c001078d400276f74c0fd1ed9202bbca74c0040cacc804094f4c004b665cd31b3c94300a34b4a8c268514362037c50c4906394211f837d5cf12be1441430e1cfc086bf12f90574e4b802c32f3f00ef52cf854d2933d023e824bc00267f51001a83d403c67df4f004b50cd400311b4f005bebd3076053f320d3c4f4a4ac37e92812c6d7498022d45250030e649002bac92500338849000f8b1290046f04a0013195270016f0c6000350f49⟩,
  ⟨31, 24, 0xa4ddc1493182914905209091f91c53ca302784504ee8609d90813a9f82743104e65a09c8b01389582702a10d8523198a0a2e13a64926685e4a98709020d118418220c2a3c0850747068e020c1b0416341820644020c080017, 0x29e18de00c2e9678001b7dd283b2acf5e006acd5e00513997700fbafdc802d90f7109e404da401d32368008a72d9c01bc0f660ff7c5d740a82035b00e150d6802571b590096b1d60027d155600aabf5540348f55400603054c0129f9520122dfdc80389ff7100cac1d9c02043b661f3cc3d6e4975ee470126f591c032c62470037ea51c0031474b00cc7191c01bd664700d8dd91c1e865247010e9f51c1129ad460077645107d7a4d2f00877ed9003056d4701a695518018ee94402f6e94bcfa62b12e0090cbdc00443d76f0081e6d90015e1f630bb6dad5c02928947017623518017b4d440203bc4bc1de1e52e008791dc00522576f009efbd90013d9d5d06f8a956426baa9580cdb68d5c2c35b75603d483d540530575400514a51c01bf614600569051000a19930008ea94bc0860312e7b42f74b409c7392b00917a4a80201d370007e0cd900162ab630100aa5680a3a7959029d60560062fc3570150b6d5805c14355013b28d50174377530012a2d4801ad094700984b51800b9ad440139615080b094f40111c79cf81852773d0029364c003cc952f00b8094b8037c6d2d0de3604b00464552b0081ff4a8016e157300a69fd90016d576300a0e75680350d15900dcea56005468f5700f87fd5803980f5500e6cfd512a8f5753366741d48018eb9470091e84bc0281f92e00b6074b40d78212c00cfe14ac019fe92a0c0723d44009b833a0191b1d410ca7db4f001f1a5b80dbd3d29020df64a0696ee1250017a95b80139035a0058664a4018261280068ca49c0331d92600278d48c00dbe92f003a964bc00ece5470079914bc020b2d2e005d84dbc00a3914700de594bc09a79d2e00fcab4b0923cf71b096ea6c6808fb9319⟩,
  ⟨19, 23, 0x10b16c115a48a2648044a8e108d181111902213114385a1864b030b1584142a082452183ca010713840c26041646201c7c3020f080018, 0xeb0c8c61bd280624653c7af00f75dd742aeef6b6194f695608e8f0aa821571553764e7eb805525d56020c94aa82a418d7800be8e960c5c84633d5d0c312e65729201ff6b48c6db3064402817e3201666e920094cbc8c25794464104ed12408b4de9181e0204fa0e56864805bfa6beda16c251c07f5f2fa0738fb63923a56a38114175f4053006da2e6ffb64012143a7825c034fc189f927c37b4413d01a6929e00e13d4fc06e9427c039cb93d04a402be82242a5208278e25f2d03a12e⟩,
  ⟨27, 23, 0x8b16c115ac822a580452aa109d501132902255008469e088930110a5822049043e900878fc20e1d041a3704326c0860d010b998216320828601048bc10897060e2d041a560830a4b0091820021, 0x677967d02c0cc368c32d21b40bd152fa0545597d46ae09b082a5a6d8100f4e4a40d8f425106f2912800291c9e001c9450201b15b5d0036043a00668f5f00cd9e6ea2629a36b010ce1b4806b6cd30d384569e2893ee3600ece11b00806dd78027d20f600fa187a0327f5242399c28c87455cc90033c0861cb41e1253869c692403bb24fa7678976100dd1f298061a59480243ec7c0113aa3d00b12f1e0040288ec0188f47400ffba2900e7291301598889406c6f4480289fb2f⟩,
  ⟨40, 21, 0x474f608e57811c2b823754046ca608d54811a2784324b04629408c12441624022b4604548808a50c11421022741084a740890e41119c02223708406c087cd010f19821d320c3460185cbc4099706102d081c581030ac10595020a2904125008209c103920604230406440808781008e82001c, 0x54916040615f3681f2db610508e6c217921d84205c5b09cf91650062815020745ea002584cab84a20b5d036f2eba07c3a55c0eaacab01cb2155037afd00047d11840fb4030865cfc61060558c239d4edd434e57a58122574b0d2ede960a95ad0443d65a7859aa7480d45fc6c06ac28d8087b9af152b447b097ff0f59082c8c801ac53e070f5a5fab4a7c64029739f08c7072fbedbc24a273d7c90098aa1842021f2502598a4808c620c2107f5928287523084064e4a04bca8c20f4e7d849a473b0a23b336147afde6a0506c5e80fa45a408778a2605188682091f41d036d123a03d03074⟩,
  ⟨28, 21, 0x45af608b178115ad822a550452a620953c1122682234c08429608812820f1d881a3a0432720860e010b9a0216330828641844c020797820e2e0818581028ac20415040624040a3e0810783008e82001c, 0xabf2c080fa866d418564fa3e48d5f481b5bb0821454587460eca6126a79442147728031c76500120a4f008f96a040c0e54040eedf5c07d62ed60d380d2c15385ba8247e76b029386bc0a079d2c116eda595f2e34b062c746c038898d81c27baf01106236151ac0f6149401e9ff8691b80383a7c2eb44c9202e7f9f052d10308223cc4f118cc8c206c6d13c1a96830814efc4f1b27969e128bfcd41915c3a020f3474112cf4ee0da661d02d27e3501dc9474⟩,
  ⟨27, 22, 0x8a5781142d822755044ca6188d3c1112684204b043e9408792410e9e841b3b102e740858e410a9c0214340426661044c830718040c2f04165c1024b02039584052a0806480808801008f02001d, 0xfd0e6d1f97427d300c197d28b043618b3ba6530424aa510537de5005340650026e4e810186968021c9e35c61255b5c0430736c05b04f6b0299234b06fcdf7503392b6b0158ff5e0250bb4b023b474b139a9f4b06f7063601250e3607ba475e00fb26361bd5b87b087e7c7a4582fe370040767c5d0f2a4a0151de7c19e6f461024a484f10fd846101c72c4f04146061015bf44f160d734f04d4d33543965e37035420740a5bc474⟩,
  ⟨54, 22, 0x134bd82687a04cee60999c8132b882647004c6de1185ac13034025f6704bccc09757812e2d825b5a08b2b2115d6012b2b84545604a6aa094950128a7844f4d049c9809352c325251042491c769008e90c21c2102373f046c7c08d4e811a1c82333808626e10bcd0515198826320c46621084c011017841e2e10345a185cb030a1586112a081e520838a020613860926080e461014803010f84001d, 0x22e788102009c8100e9377d02b7df7d02aecb7d00e3747d00e1647d0175127e01ceb0780183ab7d01d0e77d01a9cb7d00e11b5f0125937d01606b7d0185d77d0b5989630159837d091c056301181c7d0123787d2642107401be3c7d0139e47d3ab36f5003d067500356974f00ac925e092237812ad53c571dc9205635108055035f7e5d08d96a5c0462925905f97e5805bc885705abfc5606569055036ce85402bf365902624a5803273057034b6c5603a67c5502062c540123a45300e64b7d00c5db7d0406a1630150087d0112747d013c72750127365e01170a5e2016c24c21b6d64b02f17f3602679b350097465e054f635021a6534f091eab364f8b6f3500a79a5ebc41db51c7f9a74f0d5e533605b6c3806f5c93370ab3cb36a41c7b5f1e387b495d8ef349bc91174a0eecbb4901563f7d032fd34904531f480a35e7460108d37d047a8349037ae74800f6ab7d0251474902c8d74800f4ab7d02f9cb49023a7b48010f347d0277344800f6607d00f8a87d0f80ba63011ebc7d0b5e5069311542630143107a013aee487ec9833879984f3602503f4f12b11b4e53ca1b350211fd7a01ff2b49⟩,
  ⟨35, 23, 0x8dde811b3b84346b0466bc08c974118ae02305b045eb408b964116a6842b4c104e961891281119f82223e08407a087cf020e9d021c3904366e1860d020b198613320424620844c010817820f2e041c5a08349c10613020b230c10441814843011004001f, 0xbd3c408059439f00283b4fc00ee407800c84daf88ecaadac064256d603096f6b0153b7b580c44fdac0c5716a0007f6f78004131af8128b0e040126c6f018165f5f00ae17a9812e3497805562cb803ea224b0224873b895fae9dc2c5704f804c3f2770349d53b805bd7978a1841c980155e65e009c1b26008204d410e79166c0b32d335047ad39b0b95a4cd401ddbef02756b3381b69319b0f5442e0009b9d694043c1b4a49bea3a501880fd28370fb09405446a770088ea3d008e2fcd803fbce4801544b231492c59ca9bc40cd4257f0e49458cdf386203539b8cf133cd80950869e481e1335⟩,
  ⟨33, 21, 0x2357a0468e408cdc4218b582305e045eba08b9702162d042a590452b0109d501132682254c08469618812810f9f821e3e043a7a106ce810d1c82193704306a1854d020999841132081e62202cc0105178209230c0c441010843009002001f, 0xc50a40823d237d0450e6fa07f309f80abba3c010ceb5f1fb75ed624eb3dac0b603be920fbd63bada7ac81a44b58c251f2b1812f947d5d8658d424488d4004ad7bc045cbf811b3086be0f7d99783e8ab2e39aa4e4b029a60fa03ed31f476b913e01083a5e72a47c9803ecc9780a289260113fa4e05ab3ea187fddcd882b219a8751cf367f45ee6a5c5a9ce0983b99b0562f78008748e927a42ed7c33105a512e8cf490ed896901b424d282da251a01ab473603a51e4806375c8e32a979c1806cf223436d671ae9ffcdc708779b3167d735⟩,
  ⟨47, 23, 0x92dac1252f02495a0490b2091d601232b8245560488aa110950120a9824052087c9e10f13421d2604384b10689408cd1c1192302314104608010b8f01169d022c3904567008a8dc1149b0228350c4a68108ccc210990220310c3a601868bc20c1702172d042c580854ac2099502122904225008409c10793040d2404184610288870190860020, 0xbb3d3f00339dd7c18b34ac409878d62026b64b1026dc09880e7064c45ef86a625b882235032540988038f44c400314262011c75a880ae09d40068e76a2044387500043f1bc0028cbd7c0297df0205cccb5f012e9d2f1387dc97405127cb943fac24b010533a50064b0d2803b88ac401eb626209339d3e0fc0279dc5daf2c9800925a5e02caa926804e42930735e449a1530cf36012651a86af2afcd819cd166a5ce727381bb9a99b261fb2ce02e037e6c31f197496396f7af8ee222d28da03ae92002f2d62044f59a501171cd1c02af72c42c02234a0a4836b102b0b05880ccd4ac40411796200806ca782006098817ef44c40b98f6621bb6f83500df3793c0f2acc6a020e6e3400f0379b004771c8c040746a0050e5b394f49099c02f5afcdc0903c66a39e47b2603e4cf91166742ce3a573a66e0dd04336⟩,
  ⟨32, 24, 0x496b6092968124ac8447581484ae20f95851caa843754046c9e08d53411a2604324a04628008c0fc1179f022e3d045a7808b0ec4141b0c22350840681078c820e1886192f14285c1844b410815060d2604184810288c90091020021, 0x4aaacdd0119fa768078de9da01cc6f76901828ada001c3747200a2d91c4029bb068013b3019c0517286600e9fc1c403f74468040f0019c1219906600a26c1c8041894710127d41a01a70f4670a710e198037710690089e71a001ec1b50004ad5d8400ddeb5f3a58a193004a7be4b019b8c1a0022488730063801a001b72868007e8e1d10031a6511f4f24cf60674d73c760fcbcee32cf673a168888564393f9d58026086cfc05a6e33e1cadbacf4376b1f3b00447fd8400889f5000f5acd7ce3f5974a2e4353d7c9ecaef4a005306dc4010f8768006d22d98084b2771015d94da018d0b367049aa8d9802b2fb4502780adc4c625636901ef38da0018a5f68005d0e1d005ab1a360176a08d4aad88b3e06ab8aced79d2ef3a01f375e059190f95b041287d5807bcc7550069a8d41c7340b3a0008ffce40223bb360050cac8dd94a2339⟩,
  ⟨17, 23, 0x21d6b043896086cfc10d1d82193a082e721054e03091b860f36081a6a0830d010599820a3204124a082090203118c0022, 0x87a2af8827bea4c02fdaf2901300c9401cba04a01d0b1b3b0207659d0047accec021f66750ae9295d0d77699f08c1aaced65b9be7b3946eb3cd0d8bb9d0035a8ddc26ee1edf1637574a8d9001a5a675cdd2c0dd9ec6c964c973d1c85759e0096f78d404d9bf0207a6315d0859baad84acd4d5803f76a8c166d2f3a⟩,
  ⟨42, 25, 0x1323482636204c4b60985681302b025f5508baa2116d4012d2782594d08ae9809592c12aa50c4f48049c8e093518126208a4740048c7e2904f81201e823f3c087a7208f0e081a1b04323504626808c0cc21719022d3008565e209cb8312168a1f2c0c3856285ca810b1404142710204c18349450412100023, 0x1c273730051bc50200c1679a401cfab34803958169005ea9ad2294256d9454d1fdb1002989f63006c0a6c4143d19d8499f14bb00025b7f5e008f31eba59a44e930510afd26904c81b5d00a8206b8036e31d6c075c65ad011f8e55600f4482aa07b9bfdc45691efae08438af5a003bcd8e201d61f16c1a3e162c84529245812382dca8025dd0944056fe62c0f6de825439d24cca659c19294810730b2884d32225104b8c150200561a5f043e201b600089036b00665b6f00386f2d940335b9b1004a6274000ba12e7e0e8d20cf806849f9e86ae0173c001df4ec6006aafd88026d65af053d5774b017b656ba009a7ed2c8b14fdae05c0ddb5b0192612ac0374e7d6c05a1f1ad01f2c715600fdf32aa00bdd892074b5512300297f62e004b8ecd202784d92010c8a62000681743e01822845c01435c92006d45e200070ab22e00571a4d2012900920051e7a20009a0443e01068b45c00c1dcd0001ac73a000291673e01e1a5e804468adcfc3cbeff9f0ead3133d00e0fae7c4e2286cf40722151b002147b40005dcb67e010ba2cf856be4d9ecb1b7833c0066796c8003efcd88009242a60025f5f3e06f01c67a93eabacf00096799d80142ff3a⟩,
  ⟨72, 24, 0x636f40c69e428c3b0516720a28e21c45c0287b7850d6e0a16da0c29a4284340506670a08cc1c059427fb206fc630df2c413dd8427aae06f25b09e0b423b164374ac06e65709c8ac1b855436f2a0ed7531da0a42b2d441652806c74f098a9a0b1130161a582c24a058292aab12134ca38e92460d1e8a222d10145218a85420d048239ed0043b9f86743e0ce27a19b8f04351d8a653a04c872098ce02309b92583514a668213ccc127190c4830088c5e1110b851f968c392c1c645630b0a84141488242820384e683c98803928e0024, 0x29001f400af487d004be5de8012ddf790034751e800cfcc79002fc41e800c0e079006a07dec013d7b7a0046bade4016d4f7a005018de4032a7f7a00db36de402767b7a00d119de403442c7a0046001e802a8a06e002d861e80170886e0034c81e801e8246e009d38dec01b59f7a0064c8de401bfe37a00619ade40119837b004707de80100ef7900397edec00e9f77a0039fede400afc77a002a12de4012c647a005b871e402a2407a009d1c1e40244c46e008fb91e802d2c06e00cb4e1e8359b846f00dcdc1b803ffdc6d00da051e802a1c46e0247261b40208fb7a00732ede40251b36e005d4dde80162db79007d81de801c50f79005fccdb80364577a010f26de40370576e00429b5f403532f7b0085a2de80285e77900a628dc00313bf6e0253ced90076a197d008ad3de802703f790c4630dc01119736e05e68dd940995e764012c515f4045bd37b004be7de80b9ad36e34473bdb000c9037400308cdd003bf6b6a14a5d6d8005edaf5f009e4bd780f666e4d59d7729340381ae4f004bfd5c0010ceb7200342bdc401c97d7000637d5bc01567f6700ac935940178e56300283758803173f5d01557dd700843135b0569d2d6806fa0f59013846d600541115700b8d3558030c05550614cc5501a63d15308e7a05484223d95100923adcc01c0c372003e22dc401597367006e8cd98043dfd640059c558c08b45b5b01580ad6803e3b35900f192d600332195700899f558021f3555016a8655003c3e95301073754801cc2d5100a4bf920010fd7711fda6ed6c46212d540de0af54c10648952006eb6544034e26480025ef1e800a000790026a5920009ad07a0027241e400b71a48007b9491c062682470057f01e83d6b195300cc5f54801afaa480368a491c00f2986e02199f54c03463d52011ab3de80921385a02301d164061348580505a2950316182530339cf9440111af7a0422e694c0feb9a5201f91c9440272a37a00ad12de4016e81480123ddde80908f77900bfe352002c4b37a02b7c8de404e485480036f8de800e36f7904cdd4dc000e5f948003d3bde8012a0379006ce3dc002140b6c0025c85206ac41b6b2718d3da80189cd6300482d588036fc37d006fb55b0012ba1650075c3d7c01d7ed570f286ed2801e65f460058444ec012ee13a00bb48d78121fff4c0fee43d2c0210e13b0058d94e801401b4c008a384ec0170393a014b198d40197235e0048251e86ea7a758027ce05500278e248007a4e8d00269de3200f3f85c0288ab15300cada1e80b31f5540065691e80180a079003d7c1b801ced248006a3491c01576c7a005e741e401622c6e00e3939200283024700b00d10001af847a0074bd1e40185186e00f27a920034fc247021395918036b0c4000c1481e803f3587900a1751b80de01e4802c5bc91c0965c44000b532de8037833790207d75200417f9470060adde801adff790069f35200374f1470091aede802a0af79010063db802356d4801252651c164d6f4000ce764d0017839330048a9de80149237900732fdc002b3336e0a46d2db4014725480061d551c0709e94201276e50420df1b4008d170cf802b511340059cd4cc02cab77a0149a6de402749b700195ec5200734554201c8675042bc2c73f05b7474bc019edb7a008596de405ea53700254675200556434085166fcf802122935⟩,
  ⟨52, 24, 0x500ee09fdd413f398a796b04f0d409dda413b3402756704e8cc09cd7c1392e02715b08deb409b964136ac026c5404d6a609a9442342804664c14c29621752842ca40c53472c908c1118fc2221f04423d04827818f8ec31d9d0c35391c5c7008b4dc2159b0e24350844681080cc10f99021e31043a600870bc30c9708152d1022581838ac40515060729080a50100c9c10113040025, 0x1dbba780beca65e004919681004fa5df8060c997800ce065dc018e43740039a0dc802c1066b00a3b49ac03028a8100d70aa04031c528125cfdf980019f0a6b005aa39ac02d1206f00a6639ac0273786f00a3561bc0523276f005140ddce937bf750031bfdf8d50f235f41520693b2a0aae4d2598e9a040283928027edf0941f889324f01ec50938c727028100140ea0083288260012cd79400dcd215521b0425515f737953012df15480304775b064787d683b9ec1570e736b5585ab3415509637754c0568cf7200ad8adc402361b5b035b96d6808ca0b5901f634d6011a7e95701df6755807077d553565fd5508b684d53008f25dbcbca1db40008698ddd6e6f97400e71b8dec12b02f400606d3ddc012e277b004a0cde403a5836c13b1f35f2064c876c042d15dac0dfaf77300ac305b8330e1f6a009726da06307674b27c9d2d2802ef6578011e18dcc05dc8b69065f4cda0034e3f4b02038cd280215553f0185555884068434c00b737d2406152f5f0514ebd300deccf4b0114ec4f852cb213d00dea44f0ea500a3655da4c8d80843223503d0af8d85735663522f7af8d802277a3601ebbd1ec0d197c7a0e362e1e807e3f24801b5df8d80177e46f0168299202c6dc2470223cb91801e2786f02a110920910cba471309129180203206f01f5bb920837af646008d521bc0543a24835358f91c15af5a4602a6ea5205fdadd4706317451856ecc547063af1518023b276f08d2735180278937701a71fddc0e3f0548⟩,
  ⟨37, 23, 0x24f7b049cf40935ac1262f824b540494a60925481242882474f048c9a11113022125863f4a047c9008f50811e20843a3d08707628cce86169c90253824386e086cd820c9a8417340c2866084cc810918821130081e5e1830b82051682092c0410561018a830194860028, 0x9234c080657e604026886fc0c6f2260008c6abe0054715f008a0b2f98f833f5f022febb46a06e7940010c94f12a3ee64f2166314080f4afa009d87dd020053d6800151752800dbcfd6c01d4c4f8063c8e813401fbbd0032d3db00fea06e956a78f6c020027bab1677eda80c46ded208675b5eceaafda59db6b2df802146adc01f79b5e01c67ba600bb7ad2c05f0ce9401e4377e03679eb787e2dcda482198ece027b996302c283a5814968d0406e5127e021d5d6f02e271b48164d0da008411ece0bb11b66012bf2b20090abd300c1c469403150b41021f85a41530ccd3005e14690137366360395e71a80cba494560811c9e03165a365ad74d1b00df598d835c5d8f60031ba7c06e6211b001f769f00ba2646c03825a3505d421244de77091cb9fcbc9032b742480052cb3e065a6192051b3ca9047fc6d47296d3ca3002d0f5f0f6943a8eca854d46⟩,
  ⟨34, 25, 0x12d3d82597a04b0c411597c12aaf02545c04a6a009493c327a6864c4c1c8a96190928120a4824048047e8c08f91421e21823b4104747a38ccec8159d1222391838701864dc20b9b021635042a682840cc605190408310c0a60100cbc2009702002b, 0x48396040087eac0802c7bb741287244c200a172980013ddf368027c3e81003e4febe00ed6bda70643bf28964f2be503e64c349e0037649e01cbfd729a03a5124f04f825d0200a9f0a000098913c00f1c6e53322c5eca4581f969401a075f2700c5482810009eb50000f01e9400170ef408007506800058bc50000f287a057c7dd94088c93fe7c055ac0d023f78b1db0028609ba05f353b6b00a4d7ed46826ead7c21e88baf001d46b5d03579fe96106d0edf8056f2dba80f4c8f6b00982f6d2168435d786d89d9a59621e934a0d147de88054e665dc024032b800246896e00d27cebc006ae3d744f6d43a600a7caf4b00d6d169400b2cdd0441e4c0b780e15cf69006e6d2c6016c13d2c0be771a080f53e93f045ca0ed2011eb1d301e1e16a000b3d4f4c017f7828003a5fbd300ccced1b002bfa65100953f4a00eb99b93c0470472700264fe360021074f000439a9dc0a1247280ae16ca4f07a5c9c9c00a1a68d8026ee1280045226360706b18f600f0ff1e800f7fe3c839f6747a006445c6c47562f8d80562dd1a892d7f249⟩,
  ⟨32, 23, 0x49cf61131e8125b8824a650492be092178123ae04454d10829830ed2c11d2502394904708e08dd1821aa282344310608210b9001169f8c273b203e743064e450a1c0412370c1e6c0838d030599880732040c62180cc01011784002e, 0x6be26040370fb020785d67b028ee53e00c0175f009bbbcc003b0126d02fe9b35e40d4e9451931b49e00cf92781201df29a5629c9480acd349e0a2ee2812123ff2981fedd948febb1ca005b0364f00c37b27012cfd940055e6502049b428003c61d4005d2efa06a5fd1d004d66ea8105887b409ff36a17c110598bc10c2604a022935af8140dbd282482daf802b2d76a03cdc1ae8364aad2c1059be8e093747460611a3a28268d5dd405cea6d6038573690c44e9af1f5342d7412a1ae961557e34a0ea421a30169a45c005e592dc0b2a7f5e032745ae83333dd300586d682303c016f0c0bf3b4816dacd2c386706820a703d3f010b5bb48053a4d300933b2f401c68b48053d19a381fa9b8d8045654a208861a4f00f0811b0046669dc544e849e02569e3600ab751a8146288d88f63e8f6030b107a00ef543c826e9d8d84a1c846c02c03a35⟩,
  ⟨35, 23, 0x93dec226bd024c720496e2092994124af84475e048cb809156c1222688404c18749608e52811c24823747046c8c08d51411a2184324104628008c0fc2171e082a3b2044743070e460b1c08123708206c083cd040599880732040c62180cc01011784002e, 0x9c32c0805c95604080d8cf604f5f27c01f9ed3e00c13b5f0349104c004565a6e020c5b3682061c9ac38a99cd74678424f0067a53c14ad0e9841fdee4a6476f065203a51d4083815f94c0cfaf4a47a260e5001f5d927805a7c9380dbbe4a0027a3e8102e2ef4001f85da01e59c7d0237cfe68104d10f4081b2f3178131496be085ae97c117543a389d4fbd180f8b36ba0c33bf4704b43fa305735bd146b76aeea02f7436b01bf6db482365dd780d0eee96276bc34a10caf5a386d090d18086b12dc031ff165039885af01d16bd741917969802c85f4115f5b2b783a0ceda406c3ce980411474b062c4ba081f6144fc036a16d2015d8164008f17a60076edd1c05ada2f40cdca74704136b1b00ac559441679a49e017c2a4e0105ff1b0049e09dc10e99c9e019efe4e00b6791a83b77a940096438f53b1c865100c93d270269f38d834a5cc6c03fc3635⟩,
  ⟨37, 23, 0x2527b08a0f4093dc812738824d700498de092db8125328249620490be111978122ae02445104869a20fd3061ca582384a046e9208d92011aa382344604668a08c90421820022f3f085a7820a4ec7111d061f391c30703048dc3079b080b33100e642808c01009782002e, 0x61a3604047c7b020308467b0223873e00e12d9f03bf0eaf808ba517c0180bcbe0105625f007573af831ee8260019cd93700a6899b42ce93cd62643075e5068f92780330c9e02863c4c29f0eee530274a12780e255a040a1414a6fae09651025d3f2800a02a93c0270349c061aee81017c934080258ea00097fd500060c968060a6fd4080fc4c1781ccedebe05c6334a03b368be085b62d1c479f168c060e035d081303a382dbdcd18f770ae8a04126775014131b580bb6bda409f65ebc03e25f4b0634a9a5101cc0d18054642dc038fab5d048bfba60f66325bc197ab6d203a1796302eda9a600d205d2c1531ce8207b2c93f00d5a2b7808608da4030d36ce01e0a96400c47da600b5ccd1c097b4af403315b48027cbda380a7999443a927c9e01b42a4e00ed2d1b0053f49dc085ec0ce2c45c24f01056d270172a494484d6e4a001694a4e86870d1b0658588d408274c6c06806a36⟩,
  ⟨38, 23, 0x12f3d825d7a04b8e4096dc422cb582586804aeca09598812aae82545c04a6b6094968128a802504d089c9811312c125a504494904909011191c122a30443450484840904f831f1e0a393b285e7420ace46129c121c37182c6c0854d0309198e0b320c10621018c03019786002e, 0x4e7c20403200102105f077c071463be00a2999f801e0bce402236b81036ce23e0381f51f036025ed6051b8f6b1de093b587a936dac044284be01889b4f005635bc00a9419780386ff02029abb53017c83a800f29fe0401414ef00090e38004a4dbc081724ee000e5c370007b997814eb6e5c000ca1652603031c92042a0a4902b17524047f38918069864d4079f3a5d0641bb238222bb91816d5048a0316667501a66d38809d519ac04d564bc10a8f65d00e9e52580d28e9281a879c8e0a89fa46210f5d228100061c004b56cd009d99a5d0ea1bd229491f61c0217b60dc0896ca69027ada31886cce9040e68687e01cafa7d0263b7348103c19a008e94cce05329266049c0a32818697190034ae498677a4a4400996c3700786a1b408bfbc92045aea481f9225238b2ece918194c866c02b2075100afc9a7806fe4cd804f80cbc1761eb5000af47a7805b73d38038cae6c0129633500f4db9a0e4db5d400932a66c0d18f3359af027a88055c9d380f4afaf60a420d7a0c149b9b11ea885ec3007eaf4367ba736⟩,
  ⟨40, 23, 0x4c0f6097de812f39025d7104b8ca11698822c2f82575e04acb809556c12a2982535004a49a11413022725824d4a089692112520223a382464608888a19050821fa0823e40047a7c08f0f431c9e0a343b285474388ce450f1c0e173714246c0844d0307198a09320c0c621010c02011784002e, 0x141308100d9be4083824bdf01282a6f805ef647c057c123e0094cc9d00d786eda57dc876100ea93b681984ddacbc33e6d609093e5f0107632f807466d3c0148d6f003533753011cf1c080b853d4c0a8d6ea0030e8f8100495fbc002520e0002258eeef3456381036153c0021784e002045e702392b778004a7f2af8207ec52804cbc2921387255f05106aa500dfde92810d0249207439a4a0142792481985e9202797cc8c03035e6a03dd992e82e12b91c0f87a48c07a8f245020c0d3a809e4b9ac04149cd20310c25e6891c32e80838a92c0f3b1c942275ca4709504b233426ed914076ed8e001f2686e010e1f3400e1bf19407aabcbc17fc665d1aecab228fc5b61c02ecb78dc076296690285e2318229560fc040ebcfa05f7c66902c44333909d76194166b30c801c3364c17ed73250047b61b804f3ac92048f7e4814a3bf2386f83a9180e16366c02170b5100c5cda7805f92cd8017c66ee018c634f00e457a700614dcd8039c5e682461bf5001f3df9b048d40cd65679f6a201fd074e06ec02bd034b3bcd8d98cf2f415f06336⟩,
  ⟨42, 23, 0x1343d84667a04cae40991c4131b582626804c2ca09818812faf825e5e08b8b8096d6c12d2982595004b09a095d3022aa584534a08a29219392022623824b4608928a1919082222082434004847a18fcf071c1d942e3a1c4e723084e070d1b8a153604286a084cd0407998a0a32100c62180cc01011784002e, 0x12c488100c69a4080c2f2dec0f357ef805cac77c00778539009060e040af170f803208a74165fd7b0805744db4196a77020715736b10b067b581f8f297c03fffcbe0215d34f0050abbc0077b7e0404587ea66c94675302cceda80237bce040150fef000989b80009c11bb80246e5d1e08af702058b6f80047c63c00d6b36e053c9f3700094f895f0522a0a5012b6e5241190babe075de94a02072d2501d22e928098004920963ea480d0b7f230074fa9d0061a44d40708765d03798d2381b8ca9180de4e48a09ef6e4401ce7d3a80bcfb9c404f1fcd601ca325e4493df2e80677392c0e3504940d374247085eef23200b9291406a6b0e001e7586e077e39350081499a03166ccba13435a471c1d912286c48d1c07039d0de16f1306e033b193481857e18c0cf2f87e02170e7d024c1134812cc799c94e7b0ca0a1e486400bf1526055d84928023a18dc046dc24902d1db24041fa191c3e99dc8c02e96e4803153b9b00798ad44037a3e9e01c23f4e00b2519b005d59d3c035e7e9c01391f360083539a805c43cd03876fea20c73635001900b9b067363cd4062192f5898c43510154fba702db4ecd8306c9e6c04a18735⟩,
  ⟨36, 25, 0x4baf6116de812d3902597108aeca09597c22a2f02535d08a2b8094148127a8824e4d109498390d2c121250440490c7a9008f11c21d230239450c6c8418cd0411920062f3d1056783094ec70f1d0c1839082c702844dc2079b080b330c10641814c44009802002f, 0xccc640802829881005c366f60a0028df00591d3be001e8b08101a95f8f8012487dbc01adf1b7005bbb76d00c234702017224e040cd857b5822394e6a071be54bc007af5d3c0074cbbc00315065e5e10616a200891bd3c01f2edc08614367531fa5e8ea5292317d44013a2da800206174f005a5269c00d9c1e04014139c0800a7fb780127f0f02002433e000052b0ba004ee578011eaaaf020120a5e0003a769c0812953d5f054b112940104355241c9e26af817ad595e06845a29401cb92928606da12e80656324a034eadc8e00b0e5924047cc9241fa819a4701f33448c0078f29d001e73335034211a5d097de648e026f039180872c722802cf62750046224d601df68978028f0d25805b48e4a2a1c5948e0351bd9180138b23800196f46e0105b5cd400964619403ef572f01a59ca5d0051c20e095ce33914011aa734802d37c640043c2498010d07928080a992380212b648006b34c8e005f6dd44013071a78026be74e0024bbe6c004563ddc0138c1a780329274e0131386a200dd99d4019a0539a801cbf57a00de5dea201274bd381c5bcd9b002576736⟩,
  ⟨41, 24, 0x26a7b08d0f4099dc41333288625f0cbebc09797412eae025c5b04b6b409695832ba986545208a49e09453832726884a4c108c9609151c1222302434504848809050c21fa1043d4104788008ecfc21c9e84373c14647630b0e86131c8424380c426e5858d8b059a820a340c0e661810c820118840030, 0x14b4c8100665d20403bb0b7b0313d5de400f118811a9cd7dc00c5f176f0abfcddb80c737f6d026561dbc0865836e01239bdb4ca853f6b008142dac0a82e1770675f45dc02e5ca7740168d1eca569787a205f3c1e430c7b47b03738a1e81818a8799792c5d4572455f506134f3d4679c26b53abf5b7d480453175000437ade0051cdb6e0aa164d4d6177b3500375c2e0401c6eb788da07cd4c0379b750021fa7e000642ff8000975457ca234c15f01d59f5784044715f015b0e5243378015f03a452578050dbe4a0093ad9dc6e43965d073c6291c0340fa4902c94d9187cadc25e0cda499745c9d124b28c48891c086e4e4600f5b19d40763525e02494d92c0321764a119f9691c0924fe46003dc01c000fc04650306719786756a65d2888d292c8fa0d247005a3c1c1a237164b079b87d5808ea4f551b6f1bd501b8d23700208d356c2873cd5a02c12c564046bdd5800e1d6d5c026e97565ccd24d51515cff530b4584d480b87df3e00dcdd5c4041f1b6f004bd5d880c56e55b0ec91456812f01d5923b12656007205356083e5fd500565ef531212bcd49b4bbcf5300e782d440741835002e94fcd814655d6710853c599ece2e75201456bd41a70461431819c1dba426bc750⟩,
  ⟨42, 24, 0x1313d84607a04bef20979d012eb8845b6008b2be215578229ae84515c04a0b619354c32529044850088c9e09153891e2608384b046e9208d92011aa382344604668a08c910118a1842f42045c8208b5001161e842a3c104c762884e840e9c821c3804366e5840d83069a820c340c1266101cc860098820030, 0x1131081005895204030b877b00557c2045bf91f79016bb0de41416457106f2a6d900c29bf70024ceedbc0128df7601f16edbc030df76e00b089db40626eb751d5248dac6747837b00100bdac0911e95f027e171ec17f7f87a2ac66e1e40aa8d47b02f0501e83a370879075d06dc095202d595d6839d44051f63500d06b7d44009d5b7800414cddc028e617312871ddc002eadb6e005dcf5a00469c5660094fc9782a6d875301d5e8e0400ce1378006c6c5a107429b53001d12de00160cd74037396e00028353802133c857c425de15f015ef45781effc95f00e17552426d9915e00648692811b59e47007a85924023842460304099782657da4b08f05491c025b96460084ef9d404be2e5e01ff3c92c1b4afa470099e091806ec065e016e2097477f84e4b0feec491c415c924b0098b693015746f7002e91b56c0c31c55a0106de564038f4158008456d580da3bf5429ef76d4d707b975202fe339200189cf3e442aa656c1d97155a025599cdae4e037530061b6de00914696804221dd44013337780de4955a0011def7807104c5cc70ee0d6900ee555a155f9ef520100f950c0b169b6e⟩,
  ⟨38, 25, 0x132bd84637804c4e80985b822fb0085b5f1ca8bc094d741292e02515704a0a83129442242806454f3c6c9c08d53411a2602334b04649408c52031723042c4404568408a9042142002273e044c7a0894f01121d84223a084072087ce020e9b041b352424682038ccd0099020031, 0x163604080167387b000f710f42f8f1cde801d1e5b803eeda76f00e2f0eda0ac444dc0086a67b7835abc76e009e77eda012efce04166155bb00891d76f00d8236dc00aab4db400147bb60255dff6b2c84f66f22b23fcde41c5331368016ee07a21c95dab20157a0560a3a63dab98d0ceb5633b81eeaa016362d500f7b31aa8057143541c5a20eca1c47d4d44196603a8002dcc9720035242e205649bd90017c8ead802cc955a0062ae2b200a692560012d8fab803d9df560066016aa006690d5001c1f5a980a69fb5200b6bdea20176ddd400234e7a8803db965e002205f020064d2e040082a4ba040ac0f7a02d291af0130a3c584872676af80285494e00c2d02bc027df65780174ab37004a50e6d0041e3cbc0f8f5e97800a6263d002574e5e0045444bc0030c392c3fec512f0013c964b0023964962ad8e3562219b83aa3061bab540017f749c00ee415c801031ab8802c63f62a809bf2b65ab8265680233bba8802721b500048a9e6c009089cd49a515ba990b339f520083496a200702ccd8040194b9001e811710e8cd82d202e33159c09b6c6b30027c0f6202b006ab605c81c568dc1b9da981ec81f5215d722ea216d892510011ccb9b0021edf36⟩,
  ⟨22, 24, 0x223b00a425f0482bc09015c21f2b023d550c74a228d54011a2788304e0c5a9a08b12821523842846044e7c1094f01121b8c1e3608386a484cd030819a00032, 0x84df7617d65bdb4007d717c1968a5dd800f24b75001c47db022fe2f6b00249ede41f86d67809af8e9e05fd10a7702381c9e071fd7958122592d514ede5f53017fdb56c3568075706fc65d580c70bf5501afdad4c5809ed5b015da0d9418627d5b06033c5681e7d5b5300659ed8c009baf610084c9d440049476c0fd7dd580424dd94e34545253c0623b14e00b9bd9e0059826800092b79e01e29035555483b575fef7755b18006a56821a42d590100ae560039b7b530047bcdddb55edb53007c505c801dd396600a32bd94030f6b64014c17d8c042387629d844d571440e115b00a8d7d4c23316f6e00ff20d8413339f5101fe9f5cc0315c57200bc765c40c94516901a17a5a002ff9967011de15980961c76502d2d2d8c0439a3620190acd867d361f5303e03fd4819803b5101005d51c062d9d46⟩,
  ⟨42, 24, 0x143390484710506e01205bc33f31027d6110f2c039c97c536af10655d08c6b811856c22fad025e5908b8b0295d5c5292b0a4d550498a8490d3cb1c2702374d14649808c52c51625022b4808528c109d14113220225430c448408850030f1f841c3e0834780864ec10c1d02173718226c2034d4b011a040033, 0x11f0977012a045e001c871770473b59dc025df278008b279dc029d1b7000dbc5d9403e3e36405b25e5f415e0db7b0149b9dd4002daf6c09f363dac009e157d08c8a6dec362eab7a0cb259de42186437510b91adb094d1a76b0221635e0022b15770c17d1dd0015a616f00d1afda802d0bd780312855dc21af1372011623dc4215c3f670fc994d9802f90d6200838397806d3bd780337bd5dc02cd1d7804febf5dc031511780208235dc04c0f57700de6a5dc01ddbe5e00512b9dc011388710081c319c0248346600460b9880110ee7700465f1c402374c6700a16919807d9395e004c669e00135867700569f1c4037e4467011db719801864a77297ed7d9411c6715b10756b5681631a95904e65656001f54b5700696ad5801d5275500aafdd50161f57650110815787def155c2190e156c1fb37d5a05b150564508fa558005cd9d5c01e4d35600b538d5403ac5b54021aa4578008cb97d0eab54dec6918077a0ed238de43b54bf75013e0bda00b52e77b028c49de8025c7379022bf3dd4417d7f6b1b62b753000beed780092979780207a17700f64c974069db25d0b5a2b53c0425ea5e02391953c0214314e0114ea938016c867702591093c03402a4e0087c89e002a60a77006f969e00214167756172c940013bf15e00eb6d578026bf95e7611025740a9ffd5a01220b564029f3754012ad6cf16a97055c6d1bce56c0eaf155a01f246560037f976500907657aea91415b259fbd56921e5c55918a9a85600185b757006a4dd580224c7550097acd5002ef2d420b631cdb8baaacb6d⟩,
  ⟨19, 23, 0x8a988114b006265e1840a2286d3c40ba704154d08269808491820821020f41041c7e0834f41061e020b3b0414744008d81009a820034, 0xfca54d940086e6d80e13d577007dbeb70046d85b404509ab201a1955800f17bab807403d58064306aa0340bf545af1c4ad80939d560059b96ae02759f5501246faa007d82578300282b60234cd59010a82ac0005a15f006ec9eca12f09d780073eaa880300e5e00a01ccbc02eea94f0228eca7826f3393c04e06ca20199167803d4812810c8b69422789c2ba2bfc615b01042aad00731f56402a21ab0023263540131099e0cc1d0cec0471eabc02d6d95e⟩,
  ⟨8, 24, 0x420d610397c4052f02094f080e961015243011b040035, 0xb720d7c0bafe95e0746b257700e74f5e001e75373009bd2dc8031c6b7100068c5f012ad2f7314a8ad58800a2d17b024d7c5887dccd15e01918452c08ca1b3c0e7cf157b0aaa115d⟩,
  ⟨28, 23, 0x484ee0905d812039023f70047cce08f59811e32043a610870be08dd7821aa802344f04669c08c934118a612284b0c4a9418892540724040c4704168c082914104a2020842040e800818e42021b880036, 0x34f60de00320def42c885e7d02c7bebe84ac0c9f42341ccfa0172a57d002887bd8087ebdb001d9f2f000dcf9770078f32f8059065f07d17b6d800eb657700a27baf0298d5d78054e2ade00e2b9780125e9b980c676dc8058ad6e216fa1b5d152a6dae0351c4d6c028742a26fa97a4c0e8b9fb4022da7d745bd11eb80f1f1d640187d8b180c43f5880204f2ee00a4577300a42db90078fbdc404d292e003da896f032dbcb28161b3590046b62c6023ff9620199fbae812e13d700a76beb609729b5a02dae3ac8159f1d6007530aac05d75554021206a9928efd5484fd122c62738d9620132d324003ec692001a87c900106924800922ca61b4e3193c03438ac4b2c70d613f5aa8b064c64a57c34aa2298027a3549⟩,
  ⟨28, 23, 0x4c6d009899c130b3045f6408bac6116d8812d3082595b08aeb41951642292c025157089ea6093948325a88847500c889e19053812026823f4c3c6092808120e0923920946080e8808190c1029e8a0037, 0xa99237005d7a1b8031f48dc22738b7b02fbb1bd037cd6dec0e1e76f441ae137b065ba3bd00383cdb0026070dc0540147a00b4303700d0601bc031768dc01e3d86d0093a637007b901b40e377ef60a6ccf7900c97db700bd90db800addaf8013a337b0054fdbd001257dd400a2dee80030976b003075b5003dccdf43c6686c002b3e35f0119a5b3c4706fd80d57d7ebe0b48935e042fa5ae81c0a0dcc0537bee40f677b6805038fb38cf14dd9804d656ba1bc68b5c0349dbad82efecd680a24aeb203ac775808313eaa57348154c59c1f2a4013f1951006443b980633bdc80467c6e2028b6170012770b79063e259407fd9ac60349bb5d038189ae010956d6c1065eeb404842b5900e7f8ab01a5135501d768aa6216be552043dfdb987f2e7dc851d25ee20492276702bc71b369e878d6c4255a6b409c0d3590216a7ac00bc5655c246c9aa80fdbd553297336a90030765440bcfaee407c1ff71020977b380e856d98168a16b62158af5a387d80a98ab50054805d6e490a6f90d53033d47238f684391cfff8f6f20e5fc37d02f33cb20a5ce158e7c194ac404ba2161⟩,
  ⟨30, 22, 0x12fbe025e6e0cb6d209699012cb106565b14a2b4113d643262c024b57188aac29015481c2a1030531456a4209d44411a804214f1c3498185d2c409a504114824108e081d041032002053f040876080ce82009c820038, 0x5195811084a6770e2b537303580f7203b8637105a7487100e2ba81033dbe6901e5166702eaa8640b99686f09404e6906b3ba67096e9a6609cbcc6427dbb0700e063e6909af546d084c5269050dc0640140b569026f997d086a2f6f03908b6d0668416903a0d96706262b6406e20f6f02e68f6d04ff1d690336b167041a0f640719d17d1a8a136f26212b6d3130f5690a3051680a5bd1670fbcc9662cdf3f64048dfb6f50cfdb6d29fa096927583d681390656771434d66c21397654f133f64066b69690495456708231b6435f577636fb683620be0797d02b5ed671c71ef63109333620196f57c00a2e36300c9bb62f454b761005e1362cb09c7610335675e21e0735c04919b5b0229db5a020c6d5601ed715501b49154b12aa35b19af515606520555008d0f5f2bfcf1560a2a9d550450e55404ab035d318e9f5c03a407715d7acf5b86d03f5a1b359b590da407583a99b95609c7095535bc9d54036c5d530231295200e70d4c5487c25502dc7f620156f36201da917c00fe036c004c8b6b⟩,
  ⟨19, 23, 0x20b5ac215ad022a580452ae109d58212aa8821540c3ca630614810ba8861450141e960839006041f82073e040c7a180cec2009d020039, 0x2ad6f77b1eac83bd2acf3fde4007f36d802bf166900ed083180dd8e1b80be2dad2cc7c3b7003363eb4902508db811b882d2b13513701bb7a5b70276815a4072736c67f314571a2f785b705b9ccd8c065dc2e227ff0b6e0323d4b39009be59924d436ca03a5a7634b65cfb108b406db404844ec61cff5b6200e707ae81228d55c0ad83aac049ce955044d0d260078d8db8070824ae0456e25602af432a8130dd9500bb3d4a602282e5202619b9fd3e81bdb508a856de0413e36e59d12fb68c1685dba2c3adeda1bfd636c⟩,
  ⟨33, 22, 0x264750cc2dc117db412f35825d6804b8ce096d9812d3104585e08acb809556c229ad0650591c92b041055c81cab1031551c54a830914c60f29081a5104329e20552c209a3841145081e820839001069f840b3e04147a1020f03029d8a003a, 0x3266d181018e74720201ac7101bf86700195eb7701538b6e00dc677a01d3f06e01f7bc6e02f49c6e012dcf6e023dc97000b6296d0440025e0af40a5d0342ea5d0173bc6e03083a5d01c21470012b946e012e825e0df138700bb5206f02fad06e033156680cf4525e17d2325d7877125c03ecfb700405b76f025a1f6e46ceed6a02632365054eed5e085ce95d18a72d5c03b35b70055cfb6f0212bb6e160ba16a027d876505b53d5e085b915d1879255c08c557700e25976f0241d36e0c30a16a03ab5365038ee55e0d4e355d6532555c0b2263700322ef6e908f556a03607168067f63650991855d1639095c04323777451dc9722a6f6d7102f1a76e152a696927261168113611725077a971160c0f6e19e2496917bc416812f5915d01cdd77808053f6e0b7d6168020ccd5e6fe91d6c08be9d570801a95609d1b555382dfe4c0dd16758119d295408172a5d0dbe195402c8f35804d9915300e78b6e01886f6e0427cf770217db6e0135776e012feb781058ef770e2e076e0363e95e04c0d95d0166f378e4f04370f7d7b36f769ad36e01e7e55e⟩,
  ⟨41, 24, 0x2817d0500f609fde813f3c827d7708f6ea09e9c813cb80a746b04e6d411c5a413834026f6704dccc09b5741362e06695b0cccb4417964a2a2c0850570c9aac212554820aa043f531076a408e93c11ca610314b18569438911c90da3061845042e8808590c309a1080f3f0c187c2020f45019e06003b, 0x10be1ea040145d18100577c6040171dd8102f1869e00387dd78000e4f5dc00f61a75008ec960401a9177e0631a95e0018d0d770034b2dd000c183720190d15e00389aa75009ff19ac00d71a6b005a639a40149fa6900a6e59ac01ad726b0080b69d401b45e6b00bed497802706275008e9c9ac0425125e008b549f80271e27500c5469ad98bc2a6a00cb399a40373ea5e0a1b3e9745b6a8e5c00b1419f802794a7502b3769c8031742710123369ad7b4f366a00b6869a406db425e1d905c9742b78f25c037c855d4095e4d6b00c66f5a40b5db15e0176f25d402d3016903765357801f8d575008b6a5ac02f7a96900f6a857802446d7528562e5c80592a97100cc2b5ac0451396900a0715784795e15d6cde92570e37dd9715147435a41513b9731f9e535c46ed20169066a3bd9002d9aa50010984d780332635b01164cd680391435900d584d600f8dc55703753755807a72155008ea655003202f5b00a2afd6802f99b590133a5d602bf7a5550114395500dd77359143d1455c9e7fb556082f445542d3dd55403f8ff54c22bf71520164efd680cf0fb5901f2dfd6020bd7d57027ca25580725e55503c98f5502daf795304b38654884938f59232ea2d60ce0b9154413b9954c02ed4246003b9d9ac01b386460083f891402a1297e009c515d401b9bd6b0062ea5a423ebfd7e0f2d015d403d73969017e6c5f95a5d1975009e9157802dd954b0480a35f838d9ef7801e37a5d6a734f16b0052de57824e5137c4271f55cc16ebab64⟩,
  ⟨25, 23, 0x24e7b049af40931e4523b582466a048ab8110d6c3202d083c59146eb018d15c318ab062e551054a808a54c1142782274c104696088924a0c23940e4618108a081d103021f88003c, 0x3d606040214830200ef618101273fbf033ae55e0218b1aee019c277400868fb90064e25e0053bbcd602aee26b0177e73506d5cd9d40d2a5cd63b471a5d0448113a824c2e9ac24d98cba6afe725c044dd93a80afad9d0e8a91cd61782f65d1380c32e0129205d01bef82d436d35d5d01cf6aba0281ab5a8844ddaba02f4897402e8eab527efd45740784c2e80636016a077d2db2828490574042f66f8044e6a50012b09af01d625a04f74ce2ae4093795611d1c4aa80115aa00085f96b614c66f5a0e16ebac83fbd5d602b1512ae191b7d561b4f8caa861f725500d2742a6030bc552016931ad832dc6d68224546b208d4e35806185cab81a6d75580dcdf2aa09cd855403e73ea980ad4e54833e8c6b2179e8358081a0aab07820a55415e322a809ea8d53e90c66aa0063a65d003571ad4013fd54711b3ddbe0176b3ddec7785aeb61736174⟩,
  ⟨21, 23, 0x22b7b0454f408a5c41143802276c044cd60895a4112340223620444b808853020fa5841d4a202a92204520406a39005460806800808fc1009f02003d, 0x1ab20c081325f60403d1ccf801e1cd810ce360bb806183df82be325020810568102470cbe009249a0401a8f4f0057fd68100d58140015a7da05d4ff42a80f20275a0490a7ac88ad3dd6013f98aae0ae321560678d6aabaf17e550050752a60d48515709c730ab09c7dd5543240eaa8a85676800cbf24ab966981558cc652aaa038a8b5b0f4905ad08b31ad64349e2eb0152fed57054102ab024bfa554276acaa9f4e94181061d53bd8244755f15cff66f69dafb37b⟩,
  ⟨18, 23, 0x10e3d821b7a0434f20865b020bb5821662042ab818496c2082d020f59041cac08354010627820b4b100e9428091c100a002003f, 0x2f87d81059c58c08209bf604042fdaee0133db7e00c2a8bc00a1645f001daacd6ec69426c00e1ff35d338a797403e254d627eb7e5d010c55358f27075a9572554a4055c82510377834089972a55c5e20baac30bf315501bf16aa0ccfd7a0011296eb60a7a135a05b669ac82feb6d608becfaf80c86d57c⟩,
  ⟨16, 23, 0x422f60841e8107bc820e6c0818d6082d78204ae02085b040eb4081964102ac02044c04069608091c100a1820041, 0x6612b020d1b7d8102c46ac0ab3626dd0057e5efc43f12578009c2f36b3bf1c9fc039aacd60fa6226b08548f35bb67219b28618e4d800dfba7800e0c54080482fa02ce9f450213adb281⟩,
  ⟨21, 22, 0x2197b082ef40859dc20a3802136d0424d80845ac10832820f64081abc102d701052d020958080ea008193c102a682044c04069608091c100a3020045, 0x1939581017871810d3a7a7b0143237c01f8458102180f745166ef761383eb74027bfb7e041c09810253698100f9226e00d60a6d42ff628109f1b66b72e1c26c02acec7cc6e44e53069d0252a3e05a527d035e4f00937678022582810158be8001658e809f009e81⟩,
  ⟨15, 21, 0x871e810dbb821a760432e20861b020b2f02155c0c24b0104130107a592064a0c069208091c100a3020044, 0x33fee7b04a7bef80926bdf81c9cb3ce7abe3740375b4dc05e8a9b41cffb3585a9547c32efdcf628fc19e803f333c0180426e05bd7d0207cff9b40cc39b48169236804ced6b8dae2bd6c2f272ab85e201560b179aaa0765455011513b409e2df5c636fe6b604016a00095754001399249⟩,
  ⟨23, 23, 0x87ddc10f3b041c6f0834dc1061b410bb602165e042aba085170308ad840f5a041cb20835601062b840a560412aa082150103a982064a040a8a08111020121840042, 0x56633e0063509f83870fcf607948e7a024b413d84324b9e81316dcf6394fca7a00d3dd3980764c9c8721466bc100d9b6b1e44fbaf871c55d7a242aa6ba0702a75e0389d3ae822dadd740af92eba03bd485e03b8f42f810159178058140bc0475405f1941c940821551158790bd6ba03bcd35d40a5fdae8283a4d1d7f0eaeba05910f47⟩,
  ⟨16, 22, 0x43cee0875d820db7821a6e0830da1855b010a32861163081ec4083978106ae840b5c0c10b6101930102a58a0049, 0x1931a7c0310e67e07bb1a7b03b1727a083b3e7b08e67e7b0e494a7a03845e7302ae4e720220f6710110b27520230675062a8e74051ff26a0c493674078dba6a02a921738cb5935e038a536c127bc76b4c2b936cfe8de35f2a33275e009bcb7809dcb76104cc0753022ada5d218d7e5b4feb525a0a5872590cb0da58⟩,
  ⟨14, 24, 0x10a3e02137a0424e610418c20731020d610816ba102570203ad82065a040aa808114c101a606004b, 0x2a697e06a191dec012b617c02115b9d00694d26a1527549d01060ee6a02e4509fb32ab875f37498cd78956e376c156f14d78114a017c1155c7d7809e2657c05bf47a044f616681011ddcd84f337276000f201d3c03b73b4e⟩,
  ⟨11, 24, 0x855f010a3982135e0822ba1839702062d820b5a0812a2101d3050125840046, 0xab35f80159997c1a712ad7ea0ee43613fe14fd800307597c01e9e9db0495e536b0312e25f162e0175f01ad535f0abf1f35347f974d48077aa76101ec609740a473761032c56d802bbd2f5f00cecad3c02d9374e00b3b75ec85db435f⟩,
  ⟨21, 24, 0x21f6a043cca08758c20db104195e0430ba10597010aad82145a0824b2104160107ab820e56041aaa102d501052982095204109830092c100a4820046, 0x17f05f0014d027500664d9a80179ea74006b5b9a8802cb7608f8e65d7e4dd75f5f189a635f0adb5af5f01613660416f05981014a8c60407f99d800206df60415ec91800a8434a0409d5ea810226ffa0407a2b2811df395a000b43aa81015d22a04203a0f4d5e152cd85579ed360266f8ad7c0632074f009a89d3810c1a34d09bba19742360ef5f⟩,
  ⟨23, 24, 0x881e810fbc841d720c34e208659410c3182175f082ab6085168109ac8212580422ae103d58206aa820c540416a6082948104a704074c0c0896080d2810124840048, 0x1186b7b004f2cdec01026b7b001ea5dd000f2ab7b008ddede8006c6b7401abfb9d40e457a75028f07d80025035800027fddd003ce5580010235600048d9d800165eca003787ae8101069aa001260368100e900a000827ea8002eb59a00036f6a800175499780070f37800c53dd8400aecb78aa46d5d84046ecb4e00a681d800272bf600523ef5d02ad3e760⟩,
  ⟨22, 24, 0x10d3d0219720430e2085d9410b2f86135e0822b6084168107ac820e58041aae083158105aa820a540412a6082148103a702064d040a98100d2c10124840048, 0x207db7b0023b2dd00079e374003a029d655c1d361007697dd80184236e3e7d4ad8402959d80002f21dd0034b198000d7fb600042a9d80012b24a0004ed9a80012476a000795c680016477a00031db28000782897801516a5e0088cc97b1c5fb76140ccf6d800443b36000849b5d004f43b60⟩,
  ⟨17, 23, 0x223710444de20798020e2f821b5d0832b8105d6c20aad0612590c1eb018315c4042b0406550c06a808094c100a9020049, 0x7f42bb805dbd9dc0d551eec0328c36439bd6bb155d1e3d840055aed60025b3613bb2fdba00d5225dc0212f6e8007f95800057e7ba0024056000b7d32ee06fedd8100473ec00110645dc0d547b02008eb98001650abb9525b6a04012c1d0002742e7711d38d408025ada0003d00cee00a3987413d86f408025dca00b71efd02009eea80011bf53b8028dda00012965000047ff61⟩,
  ⟨27, 23, 0x10b1d4115b98429720450e0089db8113340424650446c810858c30f30861b600832ba105d7020aad84135a0424b21041602072b840c560814aa102150103a9820652040aa218093c100a702004a, 0x82c52ef62457ab7a008728bc00970e6040155b2f007f76e8103d993b7817dc36040228d4f0208ee66d091fc1368039c09e003586cef732fef642fe36bb19e3eecd88d9bd66f6241f877a029eb1bc8027ad5e0246072ee068f55810ae7ccb700e11960433e43adc0e318d81006e7abc012aa460412f7930200d061780689b9408030309e0126f450200c4427804489540802de89e07ba10d0200c71a7838d0054082605ca0456437eca224e4364098351b1ac641ad88bf93eec400480b7b⟩,
  ⟨15, 23, 0x109dd4113368225670448cc18859470d308219600430ba085d7020aad8214590426a4104544e01a806004f, 0x1cdd4b7b1e37d1bd00a7325c81f7e4cd215545a69002b053b0119f09bc149434dc3bcc0d71017501b7844eb75990ad2f6cab3a917643702c5b1f57980d883f9b66ca0bfe016f013d68b000e2a96041167d2da020fc58106ead33010963559cece642cc05016573007e29b78068e05a4033f56ca01fef36400ce97b1804058d88035b62b4012c5d590101b6ac00ac0ad5c0544ceac022b0b5400e4a5a900e687d940bb90ab825b3d752⟩,
  ⟨25, 23, 0x27f7704fce809f5c873b308275601cdcbe09b578434ae84675c0cc8b6118968130ac82605808bcae11715822d2a82595424a0a6193548225a8983f50485a9ec05539201a686004c, 0xe5d40803d88de80a98cb020a594171035b50b38165fa5985dc6a6ca0cc8ef6406f8ddb181396bd8899086ee000ca9b7603af5fb8011ae5dbc032cdec800fc1b6300ac87b1011f0ed84002fdef209c7d98100e212bc01f9515bcba4de2be03019978010006b001258a60403584af003642d61041326c0806d8b5e00560d302031c7181055df74080595f9e010c5c5020174be7802dc4540804dbd9e0042a5d020c1ff681018d94ae123e4556ca94b9ab405dbd15903ebb4ac030c4ed5c571ac6ac0ed1075502a6334082514d5641280dab07acb1d580b672faa031d115cc2a7002e404857d711dfe77b2806a6e574050c62b8044a6d5b02ff1aad0159a7d5c0b33aeac03aae755015d67a88029cbde00b2b7ae60aea257201ba7cb8819e2259c08a752cc064907652b8bd7b20b42fdd8c12734ec4ac2c315d445b90ae0085dd56c046032b4020b3f5700e323ab005a28d540457cea200b94b780033b5bb81df715cc123702e402c9697100cc82b482b06a5a00da0b2ce0469c166034cafb28912bbd90316456c609bc9b625d8f1eae80c1f1570053c5ab602589d5a00f1feac80839b5600338b6ae02492b5601100faa82c6f1d4c0464fea2026043780832f3bb8437f95cc0c6472e4038aed710e8458b481e1a55a009a65ace0322a96601807db2a572f2d906f7dcec7dd3537627407e6ae9f218a570432db2b60905495a016e89a88b9cdbdb8132bc6c426bf455d⟩,
  ⟨25, 22, 0x23672046ae208d1bc119b70232650c5ec408b98421630022b5f104ebc1891742112e04205b043eb410756410e2c021b570832ac105d5410b2a0414511020a020313c2052714004d, 0x123897801924d7800c05e780271236f00ef6e783f22f36571be2f643686d76342c60b70215fef65974fbb640145876b274bdd81022279770884dd700146716d0266d371032cd56203e50e5e0153b1780905c96e011f65780941656100e9157800c63978025a6d6e00da797800c5127800d2b67805030d5e00ca9e780266e15e00b8aa78033e515e2b3bd1580a36cb571b2427561768eb559211875401a7e55a01b8d959016b8f5701475b554381c765045a255e07226f780f7d177702f5a57307eef972024d9365186bd764596913630843e95d06a2555c0270a351⟩,
  ⟨7, 17, 0x835d810635840a5f1c06bc080974100ad820051, 0x1cffbca13ed7c4821af0af705dd0e7ebc1a607732c07ee47769dc4e316b214665634474ac528b49797ad12f1cca95e⟩,
  ⟨6, 22, 0x5042f02075c040cb6081568201a8860050, 0xe2f17802a4cb7302b44f72033e4f7101c1216502cea25e0297325e0263725e5189a1682f8dd9671258696846b19967a3cdd166⟩,
  ⟨13, 22, 0x41c760436e21065a410c32021763082ac4085184109ad021258101ca6202948502a88a0050, 0x83d8e37b5876cf7a0ebb6a7d01f25f73023be37201ed496901c3e569091fc97d0271256971270f6c01672e690194fa692a6d716913b90968160e35670dda556633bae5690deda5680cd1d9670f4cc9660714957d398f896838d225676ab1cd66024e555e2064b17d00cd476c0d4ed168261c2d672dd0c166⟩,
  ⟨3, 17, 0x809d8100aa020051, 0x406ddecd18aafd5cc15f⟩,
  ⟨10, 20, 0x1053a820972080ed60819a4102b40204670406cc080994100ae02005b, 0x1769c5780e6039d409f7f74023cadcb4d0ee752cc989a4fa58669624319a6705e37b02bd99ac0beee6b⟩,
  ⟨17, 22, 0x21b7b0832f40861d410bb904156c1022d6103da4206b4020c670814cc102194103b102065c0c06b6080968100ac820054, 0x12951810183018103206e7b034c817801c8d2751c49eb721a58bf7101e6a77e0718e97801151f720117e771b4126a7504e5866b09574a81019c366b080fba810dfb0a810223a66b0898d37b05f56b7a01d6718105c69e6b05f3ae7550a8326c02f4d66b0b94e66b2799766ba2d4756a⟩,
  ⟨20, 23, 0x43cf61071e810dbc821a750830e4085dc410b3804146c0c22d6103da4206b4020c670416cc0829942043102075c0c08b6100968100ac820054, 0x51f3604032ad30203b3727b00b8a0c08099755e0031874f801c1867500a9373e006bfb5f00a91fee4040bb371011d91bf01aef35e0026b1ee40ee5427503224b3590541da0403a0ecd62fe2ce814025f3408053905f003e1630201d00d7c01157135954d939d79dd1d4d80d10da6b628bcb3a8d0f209ae77a864d607c0515f⟩,
  ⟨11, 23, 0x839ec2063d020b6c0414d0102194103b104055f0408bc080d74200ae02005b, 0x4bc06040436c3020209fa7b744231b980d3eca0408d6b302019c617c026421ba0682429b40d2c2cc201cd026d026b0940810319a040704e4d7e5c6066b⟩,
  ⟨9, 20, 0x20b7b0812f40821d8103b882066c040ad40811942012f04005c, 0x749e60426201810ffa69ed891577e182029e7089877314ac09ac3139d8106e709b824b4a6d14ec6a04e0e466b⟩,
  ⟨12, 22, 0x424f61041e820738820d700418d81029ac104b282085f080cbc0815743012e04005b, 0x18e3d8101b97d8105705e7b19270a7c0313f2790410cb7403222b7301876f7e00b9937202a985812049f26d02f0a66e0440da6d048bfa6b06f8d28102ebce6c027dfe6beb5c026c03959a6b⟩,
  ⟨11, 21, 0x839ec2063d020b760414e20825b410436020765080abe100d781012e84005c, 0x62716040f3b4c08411427b2d62befc0ae6a9e6847dfba0a89a373054c730234a349bcb2bc736838c726e05c7a4db9a1a59b43eb254082a9e26b⟩,
  ⟨19, 21, 0x865ec10c3b821773042ce40855c4209b802126f0422dc103da010733820d660816ca082990204318605620408be080d781012e84005c, 0xb8b04081f6767c0d9896f80a46edf010d83be065f687c01ee4cf413bd51f00c24a3e02bab3810f56d6f80f098df02dbcbbe0285148103e318f81fbe61f0164873a8288f6740480a8f80ef079d2b189d360f92036d23df66da14e71e041f0ddc08091537c⟩,
  ⟨15, 22, 0x861e810bbb821672042ae2104dc01093782116d0420d018359430531880662040abe180978100ae82005c, 0x34f9b7b0247ee7c02ba777c0217277c1205947c011be67a04dcc47c521612740281538102981081022f547c0108426c035bb67502ca227402acc26a0214647c037b2a74acfc8a6c031e0e6a0a406f6d026d997302e6976e0350036d039a2f81032b0781⟩,
  ⟨14, 22, 0x10a3d0213770424ec0845c0207b7020e6d041ace083198105b2860863080cc410117c300af02005c, 0x4bd7f7b020e667c03eae27e1892467498daae76107c2674da6f3e7407044d76071359760187926c0137b87c05c5ca7405dbae6a08b2ce7407aaca6a1cabe36f31a0236d0562a1730389bf6e04506f6d0a191b81⟩,
  ⟨14, 24, 0x1093d82117a0420ee083dc010737040c6d0416d4082994104b2040763080ac4081180101af86005e, 0x120748100f6a1dec018aaa7c0759269d1566d0a74a051379d8be12de74215360dc001ab7e75183a1a9d01be96a6c08b4129a806a6a6743ac0e19a8599d85710e5d91dbc0c42b573062b40db815163f6d⟩,
  ⟨8, 21, 0x41af60831e820536040865080cc808158c1022f88005e, 0x806c408cd7437b0d0ddee08609bdbc170e63e478f1e750f46b4d8f29e79ac59f313617218b6f2913f2e70ca0fdb80bb99b682841969⟩,
  ⟨10, 22, 0x10638020b6f0812dc0821b4103b2820664040ac6081188101af86005e, 0x88c38676b6743e764e5e4f703b904b6f4927777088363a7538bf8675147dc675b0606e7502ec3f6f3930f173c51ce36f0f30e35f⟩,
  ⟨7, 22, 0x831c0105b784096e080eda200d941013084005f, 0x16dce7630095b70018a0d72086cdf7001b431720331077001860276014a226f0162fe6e0158266d91545f6f0593877000f88364⟩,
  ⟨8, 21, 0x814ec181dd41033682056b0408ca080d88200b0820060, 0x41732fa00c78def651c9bddb7f637a8d5efef2251b1dbc03bfabec31b6a6f044342e602d835f429013b7b5d54971⟩,
  ⟨7, 21, 0x819d8102ba8204710406d60809a4100b2020063, 0xd9ede79f83bbce410067223f41af85d9ac5b40ba64b481cd8169⟩,
  ⟨7, 23, 0x1821c82033884046a0406d008099c100b3020062, 0x8354a9f8654cbcea5352ee73018fd33a17364b9cedbe96ee519eb27710385973a04300e9d050ade4e80569f975⟩,
  ⟨9, 21, 0x20c770416ea0829d02043982076c040cd61011a8300b4820066, 0x1d3377c0472f4ec02ea75ddeb9613a86f4567404d5aaef8b2a2dcd468fdb98206116f13b84cea0e4959d029f9f35150b1e74⟩,
  ⟨10, 20, 0x106bc020c770416ea0829cc2043882076f0c08d8080da8200b4820066, 0x7d06df008d9b7c06a6a9d863f46740d3259e4f0a6478080a0de0268097827417dc8bb1e771b38cbdcc26226740cd229a90fa9e74⟩,
  ⟨4, 21, 0x408e6080dc4200b6020069, 0x456f47c05430cf3ce623dc93f58db884671a74⟩,
  ⟨8, 21, 0x412f60821e8103bb820673040ae4100dc4200b7820069, 0x8c92c083b6ce7b02025ef90dc549d021cbe3c2c43367a1740b4f208ac0de06310fbbc58e6a74⟩,
  ⟨6, 23, 0x102bd0204770406e80809b0100b5020069, 0xa2fbef601629e7c02afcebe5c22699d06747ded66fc70775⟩,
  ⟨6, 22, 0x102bd0204770406e80809b0100b5020069, 0x386b37b012be67c0535097caed2ba7432a7376b21224f75⟩,
  ⟨7, 22, 0x819ec102bd0204770406ec0809b8100b602006a, 0xbac88103ea977b0144a27c069e667e03633a74cd23aa7460f26f6b⟩,
  ⟨7, 23, 0x81dd81033a8404740406de0809b4100b602006a, 0x440fbd3f01d870dd836a3baf86853837b26c1e93a0451819d3c15e2ce800655b6c⟩,
  ⟨2, 14, 0x1013a84006b, 0x45af769bad7d39ab76⟩,
  ⟨3, 22, 0x811d02013704006d, 0x2a2d76088ab77800353a7609c45378c3586777⟩,
  ⟨6, 23, 0x2053b840874040ee01015bc3013704006d, 0x110223e804c799e133782efaaa81ad780aa95aba00fb61de01387e2e81e572f7824dd19bb8e1d2a5d274c4aef010d15777⟩,
  ⟨9, 19, 0x20a7b0810f4081de41033b8205760408ea080dd0200b9020071, 0xd1286068fb9b022a6f67b57e16c0cae16df079376fc04b21770cb46bb89b389ed339a4f453a867a⟩,
  ⟨9, 21, 0x20a7b0412f40821e0103bb820676040aea100dd0200b9020071, 0x1989760411d473d9a03477c1b7396f91aa55df801f1ebbaf406978037972ee08d519ec6da793d399ee27a⟩,
  ⟨6, 21, 0x1033d8205780408ee1009d4100b9020071, 0x18df160692b45be01becb7c03c8f2f0098aa9d99beb73d140b867a⟩,
  ⟨8, 21, 0x412f60821e8103bc020677040aec0811d4300b9820071, 0xa9d0c0819589816d6de6f835604df27f065bf05d4d2769af93cf72d7ce9e83c37f3c81729e79⟩,
  ⟨3, 16, 0x809e8100bb820074, 0x33c677b4a8c9f16f917c⟩,
  ⟨5, 18, 0x2047b0406f40809dc100ba820074, 0xfb5081e8cd37b0f4b67c18973761db317c⟩,
  ⟨4, 21, 0x406f60809e8100ba820074, 0x19482fa04f555f677804bef2e6bd7c⟩,
  ⟨2, 21, 0x200bc020077, 0x161d019ec566533cb38b727b⟩,
  ⟨1, 18, 0x20076, 0xa0c7b78⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨4, 18, 0x406f80809e8100bc820078, 0x9073b7d0fd327b4709a7a120797c⟩,
  ⟨1, 16, 0x20079, 0x2b1827a⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨1, 15, 0x2007b, 0x16d357d⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨0, 1, 0x0, 0x0⟩,
  ⟨0, 1, 0x0, 0x0⟩
]

def expectedWeightByFirst : List ℕ := [
  106446704, 23734898, 5219944, 11638919, 11625825, 24806313, 41902199, 35184143, 34766412, 26031072, 22187299, 19332430,
  43945511, 66311007, 19399977, 25862800, 22042123, 25220797, 24963414, 23329445, 35945816, 59705896, 61710592, 41264033,
  25743046, 9908480, 7066993, 13697615, 33900053, 27896138, 16310904, 52345553, 91462665, 40235828, 126822864, 57054470,
  129498124, 69568844, 134384395, 37562413, 32096939, 32315666, 31675040, 35873557, 35168721, 82515002, 166462243, 76991328,
  146871550, 79017278, 88105338, 13533264, 20880043, 25809903, 49108601, 42032692, 46537338, 35009189, 95708131, 44247305,
  35193030, 19725889, 23774682, 16164602, 5154488, 17632107, 13310400, 30872691, 35686580, 46738432, 15211904, 32306825,
  14533171, 26471022, 23778788, 49931183, 17793791, 473272, 6569214, 15128116, 131170, 2832270, 10199666, 23626038,
  12854233, 1947836, 5643012, 4614423, 3303405, 5586230, 9331129, 31966075, 5286572, 19538728, 3633080, 6745543,
  4273789, 16059609, 4209956, 2001076, 2734285, 3563198, 8909738, 4399349, 5210219, 13943093, 18112, 3506611,
  13996911, 1295199, 3961326, 2721609, 5218507, 95625, 325725, 3209110, 2470662, 164638, 0, 255326,
  44128, 0, 23373, 0, 0, 0, 0, 0, 0, 0
]

end OMA.Erdos1186HighBuckets

end

section

/-
Filter a bucket by its first two vertices before expanding its triangle
records. By construction all records in that bucket have those vertices.
-/

namespace OMA.Erdos1186HighBuckets

open OMA.Erdos1186HighTriangles

private def digit (word width i : ℕ) : ℕ :=
  (word >>> (width * i)) &&& ((1 <<< width) - 1)

structure Bucket where
  i : ℕ
  j : ℕ
  start : ℕ
  count : ℕ
  source : SourceRow

private def bucketAt (i : ℕ) (r : SourceRow) (p : ℕ) : Bucket :=
  let key := digit r.indexWord 23 p
  ⟨i, key &&& 255, (key >>> 8) &&& 511, key >>> 17, r⟩

def bucketsFor (i : ℕ) : List Bucket :=
  let r := sourceRows.getD i ⟨0, 1, 0, 0⟩
  (List.range r.buckets).map (bucketAt i r)

def buckets : List Bucket := (List.range 130).flatMap bucketsFor

private def intSign (negative : Bool) : ℤ := if negative then -1 else 1

private def decode (b : Bucket) (i : ℕ) : TriT :=
  let v := digit b.source.triangleWord (10 + b.source.weightWidth) i
  let s := intSign (v.testBit 8)
  let t := intSign (v.testBit 9)
  ⟨b.i, b.j, v &&& 255, s, t, s*t, (v >>> 10 : ℕ)⟩

def trianglesOf (b : Bucket) : List TriT :=
  (List.range' b.start b.count).map (decode b)

def groups : List (List TriT) := buckets.map trianglesOf

private def relevant (row : ℕ) (b : Bucket) : Bool := (b.i == row) || (b.j == row)

def fastPairWord (base : ℤ) (row : ℕ) : ℤ :=
  groupedSum (fun t => t.w * trianglePairWord base row t)
    ((buckets.filter (relevant row)).map trianglesOf)

private theorem sum_map_zero {α : Type*} (xs : List α) (f : α → ℤ)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, h x (by simp), zero_add]
      exact ih (fun a ha => h a (List.mem_cons_of_mem _ ha))

private theorem irrelevant_zero (base : ℤ) (row : ℕ) (b : Bucket)
    (hb : relevant row b = false) :
    ((trianglesOf b).map (fun t => t.w * trianglePairWord base row t)).sum = 0 := by
  apply sum_map_zero
  intro t ht
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp ht
  have hn : b.i ≠ row ∧ b.j ≠ row := by
    simpa [relevant] using hb
  simp [trianglePairWord, decode, Ne.symm hn.1, Ne.symm hn.2]

private theorem filter_preserves_word (base : ℤ) (row : ℕ) (xs : List Bucket) :
    groupedSum (fun t => t.w * trianglePairWord base row t)
      ((xs.filter (relevant row)).map trianglesOf) =
    groupedSum (fun t => t.w * trianglePairWord base row t) (xs.map trianglesOf) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases h : relevant row b
      · simp only [List.filter_cons_of_neg (p := relevant row) (a := b) (by simp [h]), List.map_cons, groupedSum,
          List.sum_cons] at ih ⊢
        rw [irrelevant_zero base row b h, zero_add]
        exact ih
      · simp only [List.filter_cons_of_pos h, List.map_cons, groupedSum, List.sum_cons] at ih ⊢
        rw [ih]

theorem fastPairWord_eq (base : ℤ) (row : ℕ) :
    fastPairWord base row = pairWord base row groups.flatten :=
  (filter_preserves_word base row buckets).trans (groupedPairWord_eq base row groups)

end OMA.Erdos1186HighBuckets

end

section

/-
Triangle multiplier data from Chandler Snively, erdos-1186 v1.0.0,
Copyright 2026 Chandler Snively. The mathematical proof is due to Carlos Toledo.
Source: https://github.com/dreadpiratechan/erdos-1186/blob/v1.0.0/computation/theorem-c/data/cert_region3.json
The data are licensed under CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
The numerical adaptation encodes normalized integer polynomial coefficients
in sparse per-row tables and one dense linear row.
The decoder and checking code here is independently written.
-/

namespace OMA.Erdos1186HighTriangles

structure PackedRow where
  length : ℕ
  width : ℕ
  word : ℕ

private def digit (word width index : ℕ) : ℕ :=
  (word >>> (width * index)) &&& ((1 <<< width) - 1)

private def signed (value width : ℕ) : ℤ :=
  (value : ℤ) - ((1 <<< (width - 1) : ℕ) : ℤ)

private def entryLookup (r : PackedRow) (column : ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 0
  | fuel + 1, left, right =>
    if left < right then
      let mid := (left + right) / 2
      let v := digit r.word (r.width + 8) mid
      let j := v &&& 255
      if column = j then signed (v >>> 8) r.width
      else if column < j then entryLookup r column fuel left mid
      else entryLookup r column fuel (mid + 1) right
    else 0

private def rowEntry (r : PackedRow) (j : ℕ) : ℤ :=
  entryLookup r j r.length 0 r.length

/- Source release commit 0b0155ead09841892690b9f9c469d1ff0edaff4c. Source SHA-256 8e118f99b502a9222ba5fb859f0f6a05468a3f84369a509d2243ca0878d4f304. -/

private def quadraticData : List PackedRow := [
  ⟨82, 26, 0x7107c3605ef8d83807ff62ddf1ef380f787770455ddff549f737e80749c9ff0fd171801ac99c1ff9f09697fd8219a1ff3145677fce5099a05a87a658566c6d920189246380158d18a0a9877607ffb0317d8d974c5d6e478ed719234835b7ebc49169903d6b5963db0d56244fded578a55fe95a50fe7b5588bfd3d521a37b25387398654a012ace518e64c1539ffb7954a7ffe7f925fef11d48788fc911dfd7fa14651bfaf515f818c0446cbfb050dc9d358429e61e5905ba8bc740802ac38fe003efa3e5bd6dd4f4cf18703c70dc1a8ed5ed73b3a6a7ab0ce59e1515386c58d60dd7fe8c2367773a94d5bbd48433786ba50bdb4c8db2e6c41db8b5ebf1612c769cb64addc8f232a88ce224a60815ea2882235289e0120ec267d68e849604e6ce247fc4ffc8e007e0e1f8024ab87609229a1c788399c69ee040b1981bc14c4200ed5e0f8043b8c31fff8c70a803d144221572ae07816502819dcb25404⟩,
  ⟨52, 25, 0x76cc03c0bfdaa05cdfd9504e4fe6d22718159c1b83fd9371a1fedd2eceff75a366868b8832bfd6a8175fccbc8b8f995385b67cff22d3f11d5165f9f712b143f897578d9118ab4a370515605580ca902b52d5381d549a93c72fc941ff44308eff9c73465a5981a2bf8932511fb911e86feef84427fb89ba0c01cb0cfe00d81c7d011fbe3d1e08b29e3973448ed3e91ec74fd3eaa397fe2281bbe4dc78d9fe20745efd4b1a2e756b0496bf752ccb1fbaf4a56fda0cc2a838e2014c10d130a204543c4f018873267fd32688c0242ac4200aedc1efff4510a⟩,
  ⟨9, 24, 0x7be703787eeec0777c7e0b6e7f6f865b7ed6cf58816bc5578184075635030f433905ca3c⟩,
  ⟨66, 24, 0x80ac3c72805a5d717fb3a4707f932d6f7fdaf56d8034286880404067803e91667fbd33657fbf2b647fc60a637fa946628111835d82e8225c9601405b8155835a805a9859805d3a587f92a9577f99f9567ed444557e3fc1547fc15a537fee15527d595d496c2bf048642db44780770c468cc6374580ba5d44864b5e4381243c42809549417f2aec407f4a3d3f7f9c933e7eebed3d7ff4e33c7ff76f3a7f58d331804faa2f80603f2e80ff462d829fcb2c82662e2b80f5d52a7f742b297f7b35287ea980277fd1922670b482206fdd761a7e3a8c197dee4f18753cba167ff52e158115b3148e189e139f2b831293834111754601107c57570f7a10380c2221c00b8033d1057a412604⟩,
  ⟨61, 23, 0x3a68f87b7e6edef5197e65e5fbdfabc4033c5777e7af0df018f6db9dbed9353ba4056980442ed0e837b99da3889334781e765826ca0c6e7f1f179f17f72eb73ffc5c81ec60b703ab1566096d62c36bda6577f8e2cacff231d55feb52aa380f334c6ec72c954e674d1df48c2a3409c3c4384395a84fe8bfcfdf9d3419b87753329d291461035eb0be02fae97444b762da0204e59140068ae01323153f04f6277db9984cfc739489da8b90d3e139b196ace3e30ff6a005e012c00b71dca1158460c822c02a8c41c488487aae2550e3178801b5933d4320718d85c06a360a80437c10fe7b701e1b59b033f6e0e05⟩,
  ⟨91, 23, 0xf99c99edec0a9bd425700797ccbf4f0ff7d4dddf22a6ba40993c738bd13ce2ff2d35c1fdb33b7bb6392698749aad0f857019df139d333cbb67647a6b60c6db3f1189eeba1b03f7c995f426742baec8ab9713cba5adb5b2bd5a7a996cb2e3282162a15ff2bc67ad0568b42ecab05320951f643529bfcbea527fcc84a2ff9e8941fa37d26bb9a144a805a5e918292311df0ec4a33dc05f451443ec88fd36390e57423215012c4417c4cf280d74fecfdc9c2d1f3b01a33d56e23a78ffddbce9ff2a41cbfe0bb357ee3fe6912f090c607c2817bbedd52e805fca5afa513cb2025a315bf27c72aa56106530d05eca217eef93c4fa9226a7ef1a4b0362609200cdf11c0525b226807c64342431c7e216620f4aed351d96702638fcbd586dd6db88d3d05a019783cd031005b3c5e7b5f08b3fd31a14953726277facf04b013ff08a971591052b30e1e8e59143b4498886a9de0c0a37a6de1300cdec2209ba183c055c906⟩,
  ⟨91, 24, 0x7f59707c75dfde7b75a1157a777d73797f9b33787f7995777ef3e7726c40ef7181900a707bb70c6e8f455f6c8197ba6981c3626880778a6780e3d76697f6e35eabaa785d80a31e5c9a17845b80a9ee5a7f577e597f5025587165dd5780717e568082565580888554caef7d539ad5d052e272bc5182ba064f7fc6914d80130a4c95944a4b93e905497e5ec7444f90a9438c1a454272ab87416c06e940809cab3f810b733e7ce4e93d8099393c89b6a93b80eeaa3aa4a61a38941ce5377fbe703486e03333a6229c3281811f318c11373094cb2f2fc184e92e7f7dd12d7f774b2c7edb6d2b7f36272a7d8af82980b4b12880906227808eec268048f3256128202487560122661efd217fecf62076ae691f7b82881e7632fb1d6e15211c80b0171b80328c1a824abc199fb9081868134d167743cc157e24271479971d136e20fc126ab51b1180b594108181b50f6cd6b30e2a214c0d50b7ff0c584d0f0b6e732b0a75beb3097d9ee90854e24507⟩,
  ⟨91, 24, 0x7f8b427c72976e7b75cca77a6b984179804426787c3376777fc7b77380ccbf7280828c717bcfd3707b76da6e8041336c84f82a6b80df46698216f1688060d067806381668034136493df0b5ea3ed205d9751645b8709335a843d3e597faf375875a8e2577b876b567fe402557ee7ab54ef32ae539702ef52dc865c51832980508c137d4f7fcd374d9c160a4b98c040498026e2487bc66347735ac3446eda9d438098c3427e9fbe416b10a0407cd6783f7f52943e7e070c3d7f66c73c7f00503b7f6ba03a8836a53890f9ae37802aad369029863385aad2317f7c233097dbc52fc647f32e804c442d7f88122c7fd6fb2b8007f02a7ec2c7297f4b4f287f6f9e277f7114267fb70d257d6ded2487c998227e4cf2217fdd2a206ad0ea1f7d0cc81e7c5bff1d7530cd1c81517b1b7f53a11a7db54419544a3b166db0571576bc1f146fe42b135604741277064b1170f1ae1061f9ba0f6e5f960e3d34460d44aee90c7a04550b768f1f0a80961809⟩,
  ⟨80, 24, 0x7ee4b97c6ebc477b6ed3887a7f6dae797fe7737781b117737fce80727fbefe717fd6e5707839fd6f7980806e804d906ca166316b80471362817361608e96b65e7e89105d7f8bf45c82e5205b81cfde5a7f88c8597f3adb588130205780a5d45680599455d110a653ad9e6a52eac0295180214350c07f734f8058144ca047504b98b5da497ead73477f2b014667360a447f26f7437e8dae41802dc3408078af3f80567b3e7dd58d3b8127653a83c4f338800599364cd117358010613492398533930961327fb12d3091fed42fbc6cff2e7f98de2d7f4f3d2c7f82392b7fa54e2a4e2f50254c1d0a247fd9242398b441227ed193217fe3c1207fcf5b1f7b74471e7155281d78d8421c80e74a1b53eb98167ffaa1157f3612147ed0d6137fd37d127ca33611637b66106309390e76d2c70d442f100c7f4d760b80603c0a76d2c709⟩,
  ⟨88, 24, 0x6d3fcc817496a27f7fcd127d7f00e67c7e1f7d7b7c058f787c9cdd7781c9d9757e0384737f8d13718067c9708101db6f79b8fb6d805cbb6b7f5d7e688080ec65805e86648070da63809961627e709b617fb111608050bc5f6b6bdf5d7c58915b7d65e75a7d119a597d32d85883f8795783b18a568358c45583c7ce547a0f4e538ceda8526674bd517d2081507477084f7981924e835f464c7faf444b80ac5b498efe1f4771d383465da20d457dfa81447a1120437ee18342815aef418026d74080bc683f80bc333e82e6433c7d01cd3b7fc13d3a80070739840aa8367fbd1735745321347f6914337e1f7d307ed57b2f7ecd552e7ce6692d7c40f32c7bb7032b7aebc52a819aae2982c665288387e12787d62a26836e4f258e38c52480fcfd237f61d81e8046f618836e9017a244c416ab698d1534c717145f18c91365d28b1270d10211815c9b1083cdec0f82cea10ed721790d9bcc520c7b7aff0b74c5e40a⟩,
  ⟨90, 23, 0xfd49940b8e7de7f8065dcfaed0cb5edff3f4bcb94d5b7860f22ceef6c801d5fa39739bf5aed727e01cce302a1d5bdb7f6cb72bcbaa6d7317c2d6e704d5a5d3b9cb2bc5930648039bac6d6329d89ff466ae3e72705b7c2934b4f9d15965ee8142c41617057832c20ad06741d5608f7a2a3d94e95380ba84a4b8b14141446f527bfacc34e79417498ffcf492deb9ab253f582247745b748c6d80b915f66ca223b51564368531e84ff77d906010f32041224c3f838b727d01d898f60eac89e46203c3b851b1c74d51b38e585f6f9c42b5ec369da4a26a941a30d1fd67319bb2b16307b100e5af9fe30b1e4d7095beb15e2a8c4e9e531c05bca291dab13e4c080269004ac4b37d830920a40011c93287227e08043eff297879fe1650ebfaa701c808a7a370209246a051f80cc2cb19188025b62fe0dd645b522718a835ef2144fc9c626dcecbc49ddf3908c1b3871082eafe1f0601883adbc8406c033050c⟩,
  ⟨44, 25, 0x803b3440c0c16ede1f9f48aeeffd91b6e7fc0e6af40346715201c790a31325b9507fd3f6263fe79ed09fee0cc8300762b408055c59fc01aee0e9ffd4b26f0025ff367ff7cf9a3677590c9f1a81e62fe54932c7ef71095bfd3de8a9b09bde5100dc1e27275ff4133577dc891fd610046eb3d70227ff8b210bfe17007dfdcf5c3cffea591c8811450d40715d0661434d831002370177feac28b1343cb451944cea26dd517312628c3288c016e583e0017461af00eca0c⟩,
  ⟨76, 25, 0x7fe2ecbc3f6a019de0375e8e7007f2272805b9738bfd3b81bdfe6c62dd01b3636980e396b44052f119e02764eccffb65b657f97f1323fa327d825b89eabb01f79a5ca387202dc2e2f096a08780eb300e9ae587fa1862bbfd5e0559fe6f90aafeefc0547fa502a9c079fe94a009316a123fa4a4f8008c7a5bfbc47520db266a8e8ddab046b49c2722cc228d1122f0da887013f9c4280b668a0bfce510fdfecd7e7cff04693d7f973e9e3d94458edff5bd874ecdd30386d08eb1bb5bd240cdffdce2629d9f6e3075164897b6005acba00c4aa5b0053002c803afa15c2b8fb8a9fd5f0c52fe26992878d18813ba8b8fc99d81d244aa47f08245c2a3711382360085dde69440b7538b1f7a5e760f3e34a847586d7d638d04d82187ff6460bbcf5db051ffdd0e26fed99b12808beb08c0907ac41f88a141ecec4bc0e⟩,
  ⟨63, 26, 0x1ff00e67c85357a5ce03960d727d99731c1ffca1a6f81bd5d9ba0066eb6d8034019a20e8c016684c22999609069364805d5a18e0ceebb628770c3d860047605d82cc3c96dfecf4f546b2014146050f3d4f8007ba1320015724b80032d922002a2b47652cebd1a67328545804ddf50e021cc04287a278905f1e4eb3f738b23cf9fd97dd3d7fe0fbcf20038493b8020e28e9ffd553367fdf268d5ffe118327ffaa38c600233e307f9ebfcbe02affb2d916a4c4a9db6e7d286ad07e09d41322f267edd0a48ded28b32072619987df0295b1e763a5e47190b4911b730f70c69c55f9719610405c61fe7fcd16039c31c555b07a414697ac004e023663127b37b9845ff048c107f768583dc979670e⟩,
  ⟨67, 24, 0x7dd670817ed8cc807d8bbe7f7f446a7c80fda67b81191d7a80afb9797ee7cb787fa04577812e467588a7be748054b15e8607ea5d80ec4d5b7f3675577f6ccd567f7cc5557efed9546694fc5370fddd527ca92b518b982a508c55534f80ab654c8501624b9459a14a7e6da7497b8a6f482e7fe6479a460546807425447f7d98407f50563f7eaed53e7c237d3a7dc6ae387f8a42377c20163678edbc35888bdb34812b1f3380e8433280e25131832f333091ca582fa7ff062e9464f52d8b208d2c82f3402b8076b62a7f90de297aa406267daa472575d9292480280623726b412241693220bf4a7b1f8fdc731e876e7f1d8d0bc61c6febd6165b18ec15805bbd13af08e5114decc710737c6b0f⟩,
  ⟨79, 24, 0x7bb29e817f1614807dd6937f6dd90d7b7ef50e7a7fd3bc797e6b50787fa8f17780509c7582d4db747f12826e7fc36d6d80f2cb6b7de85665815d456180322e5e809b185d824e915c85c6b05b84902e5a80cb97598234df587d81bd577e66e3567e961b557f0ee7537ea787527e0b53517d1e3650867fc64f833d634d83944e4c85cccb4b822d7b4a7e814b495e7a4f480fc83647f247b246803e9945803657447dde0940791d883e7989d73d7d74d13b7c9a533a7f38a7397f3344387ecee3377aaf89368103a335819b973482265b33826ffb3281083131847e69308943782fa094af2e80465d2d8083502c806c2c2a7f532f297f4c82286a5f3f266ca74e2471cc542369bd852264571621ff82bd20a492c41f8177c51e9544141d80cfdc1c77ec041924ce03177e2a38166371ab1580d9a814822b6d139a688812⟩,
  ⟨80, 25, 0x7ea8b140bfbb56201ff1c1eff004d107e80bb573e3ce7b71edfc6596f4ffbda9797f5596bc3ee14edde01a15ceaff32a16e7fe41cb6c064705ae00b2a8d2fef4476589e4a0b0c3b6b497e012078bd01bf865d818979adc13a7716a01e310b3030f3a587e248d2bbfaf9ed59fe04a2aafebb3054798492a9bf34e0549fc2b80a2fd93615084c9ea27c0980ed360990ea99059d8e4b81a87c25339e84525bfad8090e45a77478086282340110d5160075c6890239df4280c68c20be879e0edda063a74ff6e6a397fd50b1c3f75574ddde2d6e6d01f53f3580bf321a405307cce0b063c650164cb3191c60517d34be1cba25fac45b01d1f22c80981415c02f2eca9f72c9c52f918cb28741a57923be4d308ddaeda44520c35f21c0a03c104165df87a1fd6d23b0808c71c7f7c2d0cb2bbe305dff70fe2ce0a50e15808bd48a408b1284e17d3b42502811b11⟩,
  ⟨62, 24, 0x80e5078181a2f2807fb2407e7fa3b17c830f3c7b7bebf17a8007057980371278772891747f57c37180457f6e8122506d896e706c8b557b6b7f7784697efcb95e7f3ab95d7e6ab05c7892a35b79bdf35aa5b16f57ab5cda569c1705558ac4715481eace538b1711529b5df45180713650814d5f4f7586a54c7c23d14bf43aeb49ce41ad48462cb5477f5dbe457f69ec447f8c4d43820c113d82a5fb398065ec388d801b36816567357f15092e778a6d2d7e24f92c7ed2f82b7f337d2a94c05029808a0928a05c5925d9ea5224912bcb2359966f227365d0217e9a99207f655a1f7fca801c805776165ebfa31577392114533fef137c3b3012⟩,
  ⟨63, 24, 0x8037dd7f7f782f7e80221a7a802b4f788029c077802b0c757fa54b748031916c85049c6b7f9f12698b50a85f7fa3545e91ed4d5d80f58d5c7dcedb5b7d10b85a7e7c6b597f081b58836f905781c40056820c3b55812f0d54860f08538554a7529a7814518080e2508070194f7fc7bd4b8fc5c34abf522049df6fa34857aaae4740ade0467fa1c2447ecb8f427f0a7341943bae4081f8ec3f8059fe3980824a387e9e8a377e82003673f751357debd02f76a8632e5d6bd72d7c7cfa2c7b60312b7e69742a9c52d629814dea2883f3a4278aea5526899d5325df46b0245eeb2b234d671f2272eb3f214c1930206dbd7c1c842810186e7102157f84eb13⟩,
  ⟨66, 25, 0x1ffa63cf6feeb037a7e7c583cbfa5e39ddff9964eaffbddf727fe169b8c0869b9c2017690dd00409765800ec431c28fd757e1cf376bcff895f5d7fdae42e3fa75bd6dfc96a2b4fe5908597f6ac12c4152f195e19a8b6ad1371fd55809850aa4560c494e0a2282a509fbbf5181c45ca5c0965e92b2948769346b43e4879f14b23b60739d19ff7bce8affa1e2447f940821bf9489d09f9398483105df7407faae01c3fe31f8de06103e6d0024fd327b1f72183d59f40bd5b8cd25cf44b6f2d7971d7963d251e4adfa6df255050654299518f994418561c9eb1d1e64d1702b1256a960b1236ae9cc8db0a49044ff0cee1f7fc5608ebfd23c47201235037027cb31a810f698cbfa71cc59ab26242affc4a414⟩,
  ⟨58, 25, 0x221d874e901624a70805635374026eddaa3adc02d30dd81e5e765f062e208b71d6dfec892b4fec59b597f9fe8ac40509c95e01e750ad0131975580a41aaa4061a554e1d4f9ca4efdabd518b441ea849b9b993db232349d013cd14b8b7423a5786453525ff894890b372d9477e16e1a33fabc511189e86c86ff0e03427dc5af20c142ecd01f30f9270fd8c9a3783c08e9b3f8b9c0d5e807ba5ef655302e7a98be16be6e470b1fe2d9856a8d9632a81b9a094c992288a2a2eb724fe2e46526616f9f9239450bc8db381ea44e853c5217ff3368fbffb2b479f6591a3afe5b3c1c839d368cc035b3c61a9a7b22ca3a39a15⟩,
  ⟨62, 26, 0x84fc18dee071b7a797f2da99ce0985a470802e875be02170b688037a6d9a1509265f8a341997a6a742a5d90ce4a57211f8375780224fd5200099f51800abed420f263d4f837087932001e364a81dac5125d30d9a485b7bc411dbbb7fb467d247ad15bf41c744483d5f90deba1b242785d87906008268408564558fe0160b63e854d290f5ffef88378012d40d62cf649327d34034c5fefdad307723418bd6c997e2e7af4090b5f4df732c7f43300adb93cce2a694a788a5a411022862dba449cf852cf266f61a4895ff5c50247ffd9848df07ad7227ffcee885e222c62071ed6dc7de91fa91e7a0714075ff2e7f1c9b777f86e2e20c31a8b36fa0663ac3ee187ffa4405dfff2bd16⟩,
  ⟨82, 25, 0x20e3282f50fb910797f93d33c3f07409ddff48f6e701e1847280cc6138c09f8e5c207841cdeffc93d6e801285b6c279011a6008140d101553367807808b34030ee59606d8cac904e9d963802b5d313f75d0d821d9566bd0dccdb5d7fdf40ae486158d6dfe64dcb4f5dfb359798841ac470a2795e1ac6baad062536558174dfaa5414ca14e6c82a0a50c07235180c8d8a850ca7d93dfe8df49b000c514b800dbea52e9e08525e2036a902f092c475c329c236311c8d15fb6c388900b322437fa62e213ff4db10606427880ffc8163f888e3c9f4185274f6004dc074ff71ff347fe41919bb3da7cc9ffe75e62ff8b26306afeda97ac8fac8b90745405aedc8832c7e14e515c178348a9ae129452b8aeb52872b7b1139325cd8994848484a704c7a2479d53811aec9be889e807c642f0585d1f7d31d08f396912075fb0898392458431b849a080d4041d3c65f862b030ce7e3717⟩,
  ⟨44, 26, 0x7d3ec5df6007ed86e8046969b6163b0e6481aede18e25a3266289737ed7a00f75d5d9bb273d720e28975b7e15e3d59fa853e557f7aa3d520090a14f8005f452ddcd61d496bc7fbd20eb1e4a477bcf4f919e4933f447f30b00fdfc0ee63e7c4af08f5ff15e83c7f56fa0c9ffe82f317bec390bdb4bf182e9be5ac0b604cd6f2c868ea5cae0755e12a68c25aca5b415d9287fbafa49df3be02267fdbd7c8d70b0c1207af3ec87dfd5a6d1e76dc30c6df6915a1a7f70470659fe2e118⟩,
  ⟨59, 25, 0x3ff1b6205fae270faff99717c8027d23dc00fa19e9ff318ef0fea48a7780cd9e3ac006c09d1ff44f8df0d93386d84c53435c0219c1a6838856c302a5a660804036af401b15976033bcab7016066598619692c3fa175955b6af4ca8ff9171536e6d0ca93f270c146394aa8a1214da24f804a4426400e4a12d34be2094c729e44979103ca44014ab51dff32e27effb7833e7fdd8b1ebfe9da4f1ff7fb076f4a93e3a7f673d1c3fc3890ddb55a2a6d0a24fb34803b3819b6f9744ca011c54614120ae2fb686029767b66e0b600eec856e221ed297fc636133fa99e095fe4e4449050d60237faec110c06ee00821c16fe3ef52ff619⟩,
  ⟨58, 23, 0x1f7336c0bf1c43807f9256f913d901ee06fc93d439d4e75867912e8ff3d45b5fc22c32d899c86173b14ebf0300317a0cb33aebddaea577f1554acfe34e155faf722a3e86df537dfa3ca4e306ed42499e827c51bdc4b56d48094fb5df925d76e324403b394780debe8d011f451203ed021c1973f42841a2a82eaee1ce9fc8fc1cbe04cf3879c6806ee99c90da47afd9ac1a8bf3480d58466452aa4cafc17d9857b4182fd7c32e5d08c06cb61105c9642453c2b812f2a54f8c4c4a5d96e394377134277bc43c4cdc2814924b22811ba95e9229d28a24119ae987a0db448ec0f40c1c⟩,
  ⟨53, 23, 0x3f1a71817f3f1d00cfab1df5fe1b9be424d5f7b829280f4ff6fb1e1eed313bc0a9c275853c0ce8ff057db60c65f35c1693f6a935504c3070ea17a0697faed03bb75c906158b702145561e0db9aaad6636537db2b2a2f8baa142adeeea7c0c71d4d819fb89922fbf92d7e224a53a29774983b1149101e12111f18dd9dbdd15c3a7ee91472e8cd1ce1801e61bbebdd13682517e6b031638d201c4499bf62db32a7d19861187cb4bf06b0617431f7b2c853c0c5704a1cca9db927924094f92081915c3f03901c7a234a18ec077251c⟩,
  ⟨46, 23, 0x1fb236c0bf9e5b80582e54fafe6db1f237ab73dc21f9f7a837e6eeb0dafe5d1fb8fe373fc0bd6d821838d908e975aeaf52330c52a005ec1779cb91f97416d9fe7d2a930507537dedaca2f59421436026027c14d014d8fe772968126f9293db5524bef3e43d7bdb4a76f22048e9fb8979cbad41c383b73546ef6e8ccda09a9a1ac1bdc13480928666f940e0cad3ae618578ae12f80a8ee5d1c313cb22589615c15c152a728ee0494558e482080968f4296f11d⟩,
  ⟨83, 24, 0x83545281816db0807fa2bc7e89087d7d808b9e7b804c6c7a8073ac787fb0e47593a373747fc5b3737f5209727f544e718038dd708038596f8074636e80d0f06b82968d697f9f16687f8bc7677f958e6669bb7763a93f645f7dff655e7f1dd75d7da1595c7f28025b7e83bd5a793aaf597a430d588e0e8f57943fb45690d7095582c7035480e370538181fc52af10765190f4cc50ad24d64f84ac464e7e36424d7825744c7549be4bce8ffc4ab365c049881c7e48828d79467fcbce457fd3f3447f7d3a437ea32642811fe23f8137b23e80b5083d8040a13c86e1163b80a1303a8049cd39a19ce638ad929537a76ea236a96f47357ea9bb34603de0331bc37332600e3a3141c372305b4e172f4cce5b2e7759262d7c57562c7cf52b2b7c06fd2a82d01d298234952886551627b0b0ec268da4f425a36b5a24810a99239183a12241e78d2065cd251f7efbb71d⟩,
  ⟨61, 25, 0x101874e8187aa21403febe29f9f437baf901614c7a801dc2bcc02efe9e1df3568ef0527e0748027a737431c5fdae02d27ed5068a555f7d41772f3dc4d5975fd19e2b8fdd5095b7fab12ad3fceec5660765b0af012b1256809336aac015c2d4e0419cca1012a104f7f3a8f26bad03f531d9abb49738b7544a7fc01b24bfee1b515ff7b32890112433f84afd71f41aef70f60349d479148c5a3a854f6d9cd803158e2629f6c6f3f408536a5130e1ab6b8898d1e459e666e83a05327855df18bfb2318c1fde1f45edab6692e7f3bf896c04ac38a60138545106e1f62780a88d1346c29a89618dfdc49009987237f4ea31131d29f484e153da40ecce6c1f⟩,
  ⟨67, 23, 0x105e6d2060ac5ec03f80d07e84a4d2faf128e1f203142bd407b487883d592e8fdc2e1c9fbaf238c03af36e8e3556d72ec32da945258b238aecd63969af0bef4ae3979e048aaebbbcf85c7f3c48b6eb1cd96935fc2acbe84a05880dd4aaf0167015a02c31aacbfcb05485f3dea0feec0939eddbc26b134c24c4d08d8977ead252a2e46224c1db12487f9bac8aff4b2112181bf1fc2dac03e8be7247b024388f2166ea1dce969d3a807d9873778738e2d9da19be3053836c13a806a852068d17216819b5787b327b316462c0b82cc1f25ee17bfc5842e7f9e485b0ec4dca615d0714419d2827a58dae4d16b18c9611d911241d08723897d9444a1a40884d85761033a60b1f⟩,
  ⟨70, 25, 0x200a5f702ffa2627e7db3193e401f285e60043f0f0f03fd9778064573a4017679ae773f1ad4c609ab6299cd8aafbf8cfbd79d8f048baff5db15c7d0b5badbf3a65d69f9e8aab2fdd5635882aa6eabc0b97f95a31ec9aab30e951548038f429c0031414a02c010a302d2fa507da5c5a7bed4ee939dc986a9af3b1164c47b330a5e0bb3812a4f79b492ff898f48804a41a3bfe6d4119ff26bc8affaf74447fc477a0c01eb61020e8d3c7f32ceca3e87a2931ec56a53cf2176bca7501682c39be654a9c5dfc994df2c68306cc9d48f35485e761a36ba58ccda83fbe64f3839b315208f7183f0cda8bde82d505cfa86f22d7ea7a8163f9995cadfd76d855101036299743399440b98f49e38a9344d1bd1ad2480658611baad108894cd8d04271763a20⟩,
  ⟨52, 26, 0x807cdd606085b23748022489ce0113497281dc34dc63998d96985cbbb9a2121a996785514199a008f54618bdc1e57dffc0eb5e65bc4596dfb98175a787a63d65e8fbd258810ee715e0e8fb8568573385560167ab546ffce5d460106d5507fe13e93dffb52b4d71403c131fed6114ba70cac12a00acbe458066e310202e9a83f8b37058fa3d73813da086f0cf2caa2853bd73d658ea765b87395c7f134e12c55aa3706ee5c0d9a9f8cb357fe6568d1a88ba0326a827c8c5fefbf72f7c45044b9ca0f662d7fe75a4aa033e74266858c38919b30852348234d08989ad7821⟩,
  ⟨36, 25, 0x804d9bc0bfbc2edf2006b50ef04ddc36f7f785db5aed70a975f7a646b704acd4567f4094a93c71d0545c85f1ea0e0813a4f6fb08326637731d2e8b1baa94ff81134680bf6b9fc1aeed0faa494b87b5c94743c88be141ddcb9a18e8ebb41072a9697f385569549b838d514d99ef1cc6aba722b345c9c0019b6628ccc9febb045ef186e22680dd9e92b2195f491e4a87a46d3275822⟩,
  ⟨64, 26, 0x7cb97ca05ffa9e67c80332d9e200709c73820c569c621f1006c8008901adfafe24698b325219600ccf26480388418e2e291162850f465864cf8a56080736457a4730bf5d9c88ed572890f2f5b8a1d4a96a0d1f0b5985008f161e6ed2e567e5bc19559dd8055461b57614da3a0d6524ad330d45e8e447505e6c2e93d8a81dd4d691753d326f34294b8a215f929aa580d487e119051d9adb4e467793b15065a8f2f40923d8e0ff51f08f3eb7c6ea0f7e482213c8012cf0ed88e8723a77654bce5ffddc0386dfdcb8d9feeed3357d70a7cd1eadecb337f1bae0c9ba7582307975f20bde879102e8eef9f4b610186a2c819c0dcae08db982a7fcf890a1fe856e2754f55c099b28ea42526dfda09156dad723⟩,
  ⟨85, 25, 0xfde7507d87abdc3dc6b8a49ea2c7ba6f2ff68a4768031663a40248e9ce0237a4e501163e7188ffc2b84315fe5be1fd51edd0c1f386d9a2e443646ac419ae50115ad500d10b6980781434404d68d9e023abacd037fab658105a2323f85fb58dfd454ec4ffa9fd618a52eb30407c4b97e037eb6bd00c5cf5d80fe0eae497bc956e149d26b516ec7559923fbeac3ef8d8d5dfc0f16acfd66a2556bed08aa2d2e6c94d96cbc2a49cfb4e517fd63ea838c6b353dfeec349c9d2cce4d847d60a65a716d52e2011b294ffb4034959f0d3a439258211d7654ac8d00749445807b992240626810de4373084fc57534196f686a04530cb8ff16c4627cedb4e13d2c6bf01e3c7ace4ed39d2c674e54efa396c73969c3fd5580ddfff4ce6cea3817357235f81a3f8142ccdfc5b0864e3d4593077990a97bf7f974ba03c1ea5b044d3b2c83b79415c3a9b34a9f63dfe52fc57e0287902db93b5c9a74999fc25c4a5bc84624⟩,
  ⟨80, 26, 0x63ddc4205feae5e808020591f9ec4e0d7c842a3f9ee1114d77a7ff11d9e5f15d6d788233359de2e6149758018e41d2061cbf738064f4dca00ad8a717fa15b1c2063fe46f7fd4f41ba827c816c7f8c95dae0d73c86a8086b59a607b714688035c299e00c714667fd658591ffa4ab637f9eaad89b966016097263c97e0067c25c806a5196e0b9eaf5a80e8e5166037674587ad72cd5deeb4af5678ce01955a6ba29544c3c20d4dc4ac04525c194a14599159d505a353e53dbcc1aa4e4d5f555372103ac4cbad1bd12e7da2234a802dcdd2574a68b484a6a64d1d44e4d946a3656e101cf077a3f3c7c190f986ff023d331a698f1fe810b3b59a375ce9ad2c24397c94248e1fdd818374b9fa98d9e6f2483595fac50d2199e083388bdebcca0089de318097e7cc203d8472f84a161cba0fbb642d8f70fd8b22425212b9e82168a9df30eb297902778a1f69ec4277fd877099fac92025⟩,
  ⟨75, 25, 0x34e910e05fdecb9011e7ccf7e7e9c02be419be85ee31d1a4f4feb65a797fdd3c3c3f96385de020026eb01fd40747f7133383f71369bdff7ae6dd5630006c7fd97835cc59df9aa15b9ded3027cc56888a5aa33c0bb11999fdd7f6c8ff0870637e721c3059bf25d7e052f78bd01e6905b8080552d40a3a7966053ac0b0fe3c48577f57a52b3fa3ec155f76d08a8f9dab2537f6ca4291a60b75452aa0bea082a4e64f7f82d8a75a81b9d36c2abfe997b1a004b8b5825a533ab5dd2105bb308eb9405a46801735a240d04390a0acc6882fd3dad4079c0f11fbad2b7cf8f5fd547aee19cb3c542c6e9d98a8100e9bd962472dff2be387a9f651bb033cb4d9cecf066b06a7cc3496d0ae99cb5ae98ca01beb26306e1f13086343617c0cb184baa60c825b264e9a2c87b39295c1c1714a99b427252ad69b628⟩,
  ⟨77, 27, 0x307623a817fbfec900ffd0851fe0836873f40047af7d7b9b602f908d97adee0770ff3d40029b7797fd7a8ef0fe0e031de015bcb3ac025200747fbca4ee0f77142dbdff60c9373f317b26d87ef162d906e81c5ae079295b54113411697fe8332cafcf141d91f96eeb31bff4e1262784a71ac2ffd7a39824729a1afc29bc625e8025ec8bb0027c3d72037c54acc09aeaa587c258c2aefd3ca4d59fe15beaabfeb3eb547dbb1f4a6e6e9d0d493be1c9a8b42751c5058617d29ef8352253b2c940a26cbecb334ca3352129717acc9d29ee013da4c00a5054880214288f00485411a007943a2c56ca83449c2c7d68700709e90a0941ba20be1f6f44074722f07ef57577cf9c1e8959eb64c61c3b64d36c074f25b45ce5e72b5c1c3e719033774db5b26cfdf317cd60389dd1a413bf3133882036c65009e99cc607d1639841365952f9e0441c5d1ed0bdcb61393e515c00917a2a⟩,
  ⟨68, 25, 0x6fbe1c40a9edac601fd5636ff0152417d7cb40e3e43e7c99ee00fbecf4ffcf7f797fad5c3c3fd2aa5de04d1aaeb014772717f02c8b83c94509bdfc85d6dcfd24096d7f9d43b5c02b2d5aa0eda04d2fea1df657fbf0d323ef212d8dfa3386c4f77134617f6444b04944dad7e1abda4bd23ed785d80bfa6ae3d124995dccda24a6d89e87524d5b0528b4943bd41989ac69eff69944ec399c226ccddfd9327ca26e9713335e4a8055e624c0569f9221122568f169c2546aecdb1a2c017b4d12eaba6c8712418e4298635620bdd03dd01f1a72c7efddca13e7f70dd1ebe3b000f1e2f8aa76c659723a7a66639cb86ddf0e1fe4d5e6eea89f9367f62861ac0b2444d207053c670bbb973280a31418c4c9bacc21dce065f13d1632e⟩,
  ⟨64, 25, 0x56e43fc0bf0967201fdf28aff013c567d7d8d543e3fac0d9ee017684f4ff5e14797fadedbc3fcfef5de1addaaeb013d7c72807e7b38bd4149dbdfbba10dcfb17296d7bd140b5c13b719a5fced92caff2122647f18e131bf4086189cd0172c2f96de060847a592fc2456697a0a2176bb02061c5c838a99adbe20b154dd909c2a4afdcca516e03c3a829e10893dfcf43a9d519e104d977db9a64a840092e1724d895009e8f4980a16f2467f93691ea06a788d4226ea458031dd224fa38350e0fc76c82fcdb92407df9991fba67edcf1e4b4d676d2f8603a7a0cbb1cba66758e1fcf9cc6eef8fc4367f368f9ac0826d4d208bb2467032a0e3281dbbd18d416118c20ac1b85f462c722e⟩,
  ⟨64, 25, 0x6418a3c0bf2a95201fdc362ff0323a07d77eb023e3fb7131edfc9bcef4ff21f4797fc9e43c3fd9731de020932eb004b66738088e1b940384b5c5f103c6e0ee00696f7ee437373f274adb5f606e2d70470c96980b6bf33bfbea7995ff0facc8ff17a2637e8a5cb137181f185e708c0c110157b5f87411c2f40de471760b3a4eb8d6f9c3535a9ad9a8bb8da1541856b5e9efe67e84e941a3e26cc97279328ab2509708b12d4a81fa5924cbf48292334d7a48f3d4fe746a7a0c9a2c01dd911298d9e48703a285417d7a4ca03ede6b8fdc7bfe278d06a783b73726c9d3e64b1ce5b0524870fd1d4d375ac61e9b3e69ea0d611bb10670cf3f232ae01d8184818df0be0340345d00a34b2a⟩,
  ⟨70, 24, 0x88dcc181ab4081808102177f7f5d677e7b8fd87d8cb0f37c6c7a957b7893c87a80fcd67980b5097880533b777f3a67757bac28727b7757719591fc70808d526f851d976e80786a6d9ee20c6b7f2cf46a7bfa3f697d7a21687eb698677e851c668404766581869764813d6d6384865362839a48617f77b05f7d52ae5e7002b75d7e95265c710fb75b7856ca5a81ac2253e7ff375195f262508238f44f80e65f4e7f9dda4d8014cb4c7e214a4b7e48eb4a3ad9d4496ad4bd481b7f9647645565463c02fd4566216e447f35ea427793324184e8ae4081cd0d3fc2c8743e8a61113c8fe0a03b9fca753a9ba56d39aee8be38a32eb137b83f7a36839094357d50dd347e8bb73378dd17326d45bb3132322430757bd12f58687c2e⟩,
  ⟨69, 24, 0xc5924a8192b3bb8080e0907f7ec91b7d8a0c817c80504c7b6231217a8074bd7980abb27880c5ac777ef9fa757f6b34747c7db5727d785e7190b391708080c86f86ff056e82c4d86d98807e6b7f3f296a7aee98697f78f1687e66a3677cb17866936a50658c2bb7648142f16384ec7e629f1d6b61529ff45f7c935a5e4298575d7e3a615c6879845b85d71753cc039d518b584e508256764f812a714e7f8b9a4d7e914c4c7da8224b684a4a4a55da34495f6ce348298ac2473fbd00462a24e9457b0aa342789602418524d0408229563f821a043e81d0e63d89566d3c8c6e763bfc068f3aa5302839a9077038a3344b37a0c1733684c081357eb0c5347eb7c6337e2659327160623134b18130793ec42f5d8f9e2e⟩,
  ⟨70, 24, 0xd37f7381abd17a8080ad367f7f38097d84b78e7c810e047b7f32047a805e747980a99178809b01777f18c2757e9e76747ddd8f727dd05471879963708e7fd86f8783f76e80c8826d89bb126b7b7d9c6a7b0dff697eee5768793fad6777ea38669481a86583c8516481857e638378d26296e7c0616dd12b5f7e32d15e54a4e05d7b0d565c77a7cd5b9e34bd53f0149651855fbc5082ac8e4f81c1294e7f7a8c4d7f78214c7e95c74b53c0cb4a6ce36749569c20480e5ed847554deb461b29ee457d84254479ef60427bf66f418a17f640819e5f3f81a05d3e81d22e3d8bebf93c8d14223bcfa7293aa3a6cd39a5cb26389dba28379baf463688ca22357ed1a6347e4d78337e4aa5326e98e1311c2e41307d24b22f75c5bc2e⟩,
  ⟨68, 26, 0x8c4b25e0602f95180803a391fdffaa717d8406f41f2011ecf7b7ff6a99ea006028798031931e200a2e3777fd30a1d5ff5db6747fe93bdcdf5ffd8727e99c89c6013fdd708060a01be017a316e80c1f91b605dfe76b7d1caa5a9cb444f697f84321a1ffa552677fe93059a04f68365802d37d920317216388f4a858a019ab2617af9c5d7de19bbf5e6dbec6d75f7cd225c862cf594e47da2452fe293e546017aaf5080bb80d3e0371da4e7fe142d3543597b4c1ecb0112d64ac774a6ea414925a7be0b4827ae66d1d8c9d524659092d915e4933f447bf016909debce3418072e4902438a5f3da75f8dcf23ec71e3b97acf34ea2d4bf039a5f5728e206dc093784436b0da0cf5d7357f88faccdfe53f4327bfbf38c5ee7b17307fda89cbdff5a032e⟩,
  ⟨68, 27, 0x80ce141030108bbe01ff7f98be45f74977b8b972c8f50a6e03de6005a9a3c3f59c35777fe149eeafe7f215c6110c0db840684ec6f84c7448dd01101e9b6199148b5bfea26c687e964facefab80719a003da3b2c00a1c36270a1b98bef2b901579c58eed2ebff43605c7e997aab6f774c3569fc4166acbdb33e358801c3acaf04a0f395a021b3caac83471b54e5f5c7ea75f010154a7cd79d28d4a933150617b7c89ee7b2c35395a427526b9b76004c57372aa96e148b6d29bc88d9a4bb27ad7486e140308efdd048919ff5df722bd772d044728d29286fba4f5909f7bed720c01436f40801d86e7f00b87dcfa1166a39ec0535763c8de771c7706a5370ea34f8231cc7dc4b9387b575966ead865d0d9cfd3b21ab92d10d347f4bd9e66dbca2d0c9ca7cbe98b574b4e30⟩,
  ⟨68, 26, 0x8113d1e060496b9807fee6e5f22218127b8825111ea5387a379805b7a9e200414c7780128ddda0104cb757a2a619d1f84c1c737e4eee5c6233fa570810f971be0443d96e802c225b61d62536b78f11f5a5edd9e0687f9e1b59a06f2a6648002f2d89f407c9606ec03c57ddc67735e77ed77975e519245c67e913d6df58dca5a766c45d65ff1c305880ea4615a0368ef54e2a25cd4edae816529ba443545d4a2c7506853fbd3df2f9494e77e6a61318146e34b789316929d960a7497ba059121c7255d477f6815d19decc38457bda22111fda013437dd7a6509f6499c418019219020062733e811b59cf6023b2f3c85884e0ee0baa613a8c457e0e62b50d33880262d8dd56d8a1366c867f0d546c7f3347e4dc4ccdb8cb8d32613fbb4c5fd3a5a30⟩,
  ⟨68, 27, 0x8051313031133595ee25c035bd48539a8797f5a71af102cc2a9d9e817c93a3fc59c3727fd344ee302eb4d9c20b6318b7bf2c3a96e7e8b552db00028f5b204abbfb5be2e650697fa399ecefec92759a1c5a20b2c05649b64802a124c4fb3d71185f73f5b3033c54a75f73ffacabcd9a39b575c7a8c32e2a9ce2e5b728a7aab4ee1917d65dbbf812c460937d578c87362ad1bfe75d56ec29c2aa4bc17755389a32d8a4674a50d45b23b57a839e50ea4f7d28bde9cffb963535fffa49263fe9b034b7db241094f61dce925fd0550a43f9b20c477a4d0508cfe2dfbd15d27970a23fe7a60427fb0414830078e61020041e39f40f8f5e3d800a62679002574cee005da59d420454d398008e5870f7a8c34dd3a7fc59b338e1353549f80e468dba4eb8cd799c96993ff784931⟩,
  ⟨58, 26, 0x7b1fd2201ffe0a47c8009279e5ea208f787a14de9de1989dc76800f249d60511ad737faf8fdc9ff438a71823316dba17d65b6d800ba61b208bf8b6b86459bda5ff4cdb687fd00699dfe6ad16681164f19600c3da64812121d8e0217496280adadd85d83091606bacc597dffdb625e6aadf1575627bb35c4468ea96de1fc5a5a7de5bd565e27ff458854eed95e28a035568337a2d5612259254daceee54dae61c4525ff8fa145c3c8cc506d6a4cd3dd8cacd4e7fbbab935f510d74c7fed3752dd3e8024a7c9d42925de9450477225d6d1a6ac21143802e6f4fa01f8c03c7727a70dcfc73a3365dd2618d50c1fbd347c59e78cd41b66c32⟩,
  ⟨69, 26, 0x1fa02ef7d87f03a5ee2a5df47a8706eb5e5f52e927878e4095de1aac6b758305f45d201fe9f7382ba8f5ca01925d718146bedc200cc0b6f82d8c71ba2eaab26d8431215b23f872b6b80346bdaa203ec4698431069a2140e7c678a265059a2e69e565803e3e191fd2d2e637eb491189f8bcf6617bcfd0d819d8d135f7785719795eb67e5d603c73970b1eb6c5b6fa93a969a9f68d5972fcb6162032b805780441cd5a04a1605580cdc7950f2a4ab535da31b1499ee1375167c1cdd412e430a4f5fdfb4d39fde55c4d67492e931d7b1aa4b6b9fcad29d4cb5c4880401751e01ee4346801d19116187ffe447d297550dfd8f8a4280453a90203843b3f804c528fa021f713c9585cb0edffb1043a72913e4e1ff149337446a7dcd931636f352e4d788d1c5f23233⟩,
  ⟨42, 25, 0x1fff4bef8fa4bd0787e3d85bbbae46a9b9a21cecdb0010dc6c81228d344429f9d95e06b58c4ff00e0617aab56b03e020f579761d90bac187b65b7fbef5ad3f9d66d65fc54f4b1012c2f57803a01ab405971d5603ddfca8b2d753535e998ca93a9ce5d45d1fca8a07a987a4f5d667b273fc733135f573bc98a442a34b7fe7f923402123d09fdd71483026f333f804e069ec03fb24f21e6c90771124c43a74631b9c1f344d4d971f02a6aff4a4a34⟩,
  ⟨41, 27, 0x3fd1cf17c7ffae98f6fcda321e1f1729bbbc05251f738040cc6e5005229dc5fe91beb5c00774e667fcf9e0caffcf09991ff59f4b1be74f67627ff7702c2f5cd5397de74fff2f33d557c5d93b089ab996eed496e402bf1ad4487971598315350b0ffe7a4d5dffcad9ab3ff76cf557fed0a8a8b63c0a54dff7311a8bfd76c0507fff2e89efede00531ea9620a5bba722b4a7fb13a093002ef2d0a0119431e40084383b800b1b274ffef9c0e1577b209b30568fb35⟩,
  ⟨63, 25, 0x3a4b4b1f5ff4df4f90014437b80320dbd40b6dd1e1f7010eeeff9be57680775eb9c30ea8dca040e64e2fe01cf707c3d0837c426a59b20e8b9ed104ac0c6782341cb33fad02995f4f3bac8f4789b6379c62a3134ac83d85c0a558c0988fb35f8918dcaf72d8eb976e3c65ab9b935e65b8e389bad473994d666b0cb0b100428b577e8c252b3ff2c8954690a92a89045cc536daf23a93febc6145e00808a0b0c4a74f7f9ceba73f59cad357d43a2990235514b6df4fca53e8460525aff18690ec37a647800fe92348a50e11600c25289004163438020d221407464105ff6dd480fd9f7a3f7fd59a1f3e01438f601bd4878f27d7d3b8025dc1d46d38c4e5a5cb986e31744d36⟩,
  ⟨67, 26, 0x203d5bc7d7ffa915f21e9ab77b82bd635ea229a51797fccd29e1fff50f77800495dd600145b74816428dce0bb7cc728395e99c5f31cc570800f2a1be04670f6e805b3c1b600383c6c8003095ae00183a6a80183dda60569456881bd5ed9e10ecdf66799b2c995ded08d647b766918d9af272627fa64f1866baa9360a008bc57e22e0565ecdd1739760fa7745cc0af48d6e4453295a8560c096631b7f4587efe8595dfde07b567fd95a95482432154357ecd94d54e946527fac8c945ffb4ef5076be4c13da053104e7bb085135f0c7034c80646112d723ad64972f02e9211e2b79476c4eead1a00d6d24576593551213ff6f4380d80bd0a00ceb741807559d01fe8bdb3f7b8b9d8f990b8383d4458cb0f17d2e653b42b7f28e99fdfe037⟩,
  ⟨53, 25, 0xffb2ed817ac9a03ebfc3ce9f1f77350ef038ad473806b01b940d4c41c613edd8e10f71926f821094b74871769b6007f00d90013226b62f02434bc4d531a1db8070ced92b6b66ab06ab32ccf7f7d923f03c8c7735b0362cedbf4b0c008d0d7e03718cbd7f4bf45d940aeeae51b447d6e5be0f2b51445e1598495ad2c3febf4d5da052faacd486db55518c6caa1bfe9114da27f90a4f1192051610cbc2833139d13dc81c9098c3474e4b6eaceaa53c9c665212e72c68ee6216e447f028d20c3e25fd022a43e07ef9444c3e7b439b9dbfea910e9fe93b872ffecde38⟩,
  ⟨48, 25, 0x7fc379bf42ad6f5ee1eac82f52acf3f79805decbc3fb87a1cdbecfeee38b864b70bc193f37e5ecda1bb9e1826db070f3e6c5d6fbdb5b639cb5a9b0737ed2f9a0b468771572b3bbfd9099a49350ccb0ef9226396795eb13fee8f97a00e706bb00fa765c80bc0a2d402f1e5660243f8b0faa4e557633562ab3a03255557f3744a88787a7535ec57229369346545def736a0fe2e744d7dc516a61bf23612dfbf8e8946a31cd4571c66a20bfe1ca1023154ae7efe897a3e55f2a59eac2d6eced5bb8ba74f900a839⟩,
  ⟨53, 25, 0xf3664c817124a73f40332f9f2006e32f501192b7885f04dbbbcd9931d5f90286e6eaf5277270f4ddb8d24c879c28d8a88df37ff6b6e7f8c0d36aeb5785b1ca2fc2d6af0b526a7a1e6a34ba809d1a200fbdecf00bd27668320ebb2bfed235898afc88bcadec865d5d4629ae403cea96e023dfab501070a5999c8e92c37b30c15dd699acacd59f02555bae97aa34824ed4da1d912a4fa28b151645bc427afe3a3d3144948896d597434a5fbe47a3b6f012516004c9a89002500437e00d120bff187901ff3bca7efe390a3e7fd9519ebee772cf1dc13787668ece13a⟩,
  ⟨60, 25, 0x76d6d940bfea94a01bda274fd10be1e7d8e759bbe3feba31edfed692f4ff5909798123643c409ffd1dcd322e8eb0034b2745c248eb9b559109c9478f18e2c314c17061050a37b561655b974f14ada7de7dd6c138b3bb58201369a90ff320d30035c668802d31b3c0149f99a184a4ac8ffaa44627892972fb276375789a0b08ba71d3eb5c81b8baadc1826316b6ae396b3b7d9f9584b9e552baaafc15594308f4aa0f09dc541214dc29aa58b4949d5d340a100b66a4f685dc2a610300ed2cfa3fd0950025c8480e1c6d23a9fdc0118d9df188aa5a1b74480ac0ba1c05f2fd0a0087a882fdaef23f7371191f29a5160f4828a9c78ae99dd3b⟩,
  ⟨54, 25, 0x1fadc2702ff69c1808049cfbf4009a59f1feee2ef6ff86787a7fa0a0bcbf180e5e1fa8aa0ee9b7682754f850fba509c7d5ce00868ee4fb322c706f757b37bec06a1b9a62ed2daa96cbd6c5caaacb5bc0c641aa077d2ccafa4516647fa470b125f64597d9ad3a0bc7885db5d6e13bd2e411ee356e4306f8b5380dfd59a82b372c30ff64d5d9bfa7aacb3c82055378a40aa3e147394dfb8c56a4bff3975152dd77283ff31e53dfed4f8989a6e774b8008ad24c00e5f920ee030a8ed7acf1465890b022a23f7c91201871687005e5d4280257aa0bfb8608fdf5d7ea7a44637c3c⟩,
  ⟨44, 25, 0x33a0db40b4d06b20209c44cfceeaa107caaa278bdbf9be21e9fa9070f2efb4db786defce3bd6b4a15d6b1b6cce9007a39717fc3c6b83e63941b352d772d7057c646981020ab43fb71e98a00a5bcbd0092495c83403badce270f16a9a02deb369db2458550aa82bb0e95e15953e0c6aa7a0f1e547faf8b29bfdd3ed3e006a3c9901cab54b635d4aa52a190d525c2d60a9064097c475786ce23400c29112f2fb44872c2f7a423fdb83a03f6ee2cfda8c0287cd894143d⟩,
  ⟨39, 25, 0x3de39de05e4fe470101cb627e70bf503e32590f5edc419f4f4db46d1797fcf563c3f92425dead2e8ceb003396737fd951b72b05f95b507502ad8fda2ee6b786c7cb5401b729a1febd38c4f10f335e2b8262aec00ed5573dbc352b70d15ad5a964ee0acc0bfad961ecd1acaee514e25679e81a2abfc81d551aa36aca4eac04b51957255284044e513e04e64c96d85cc84a805ff1a43b934711dd3acac80fcde4b3f⟩,
  ⟨40, 25, 0x4d7781c0bfde35e01958296ff09aaca7e8041b83eb4e4fbdedf838f2f4fdf0b97976c5223c3d09ecdde1e5a02eb2b362674801cfdb9c010e69c5fd8b10dcffb1e96d244fceb63973321ae01eb9cd3006380687fe5282f4d0c9c57207d310b7042a475a9db390acd4dec3d618490c0a88c5b6753531f37293df19ed45ff720a9f0037ee4c80383125af616652600b7409100482f47ace9f421c13adb10548c83680fecf333f⟩,
  ⟨47, 23, 0xcdc2e05f8aa2c03fa8747f828e90fd029d39f67a4c2be3c4c7d7b85582ef4fec7bde1ea82dbbd459bb768138a2eb172a8dd20449139befbec707ee1b6dedd5c05b954ac3b69e66966c7aa608d701ab8daa0317534be9bfd657ed64cc901cf297a99e22ae46606a5bb970e0b502aced61e5f322bbeea4856530cdeaafb3c8d503bf92a98f5ce252775228a3cd814d422777e27bf2ff64ebe81ae9b00937532044b025c0de0e4780b2c68d9f009d160242aa210d78a40⟩,
  ⟨42, 24, 0xfc82a1817f75308080926b7e937ceb7c75c3617b7d25877a7edf04797fe067787f4923777f6d957699eaf874815c80717d159e6e7dfb346d6615086c7f18036b80661c6982805d687f85286278eef95f80cd405eaef3a45c9bf2465b82484e5a8f4f28599d272c587e86c7577e8780567e9d0d555613af5473a7a0537cc631517fd9294f7eeb164e8102824c80b7af4b64a0344a7040604980401647804aba469a7b23458227eb44⟩,
  ⟨39, 25, 0x374092205ff3960fcffd4cf7c7ab4b33dbae5281ea036b5aef006350767fcb0939bfe26d1ca11e684df0688ca6e885b66b6c01a7b9b20806ccd70077116280cada30d5142917e65b7f6bd9bda045d7d8386ae294ef696db6d886b4fdd253597ef74fac403bd495e09e648ad00b02855808ea82a43fc39d4e02bbb2a502478a51808a3b27c5eb93129ff3eb893027b1647407a79a2bab01ad11b79cde86bbd7c342⟩,
  ⟨49, 24, 0x8061d681806de2807f3bc77e7fce8a7d7f60a27c79c8cc7b7bd9427a803387798079677880bd9d7780c4397677b313757b6310747e74a1737f546d727f18587182db226f820ecf6e8659d56d96025f6c8463546b7cd4966a7f752d69809fb6658d1358638f83c2628691bd61e0c1b05fac4bd25e2b31a05d7a31405c1a617c5b6c052c5a7d69e4597cd3ca58908dc75380cc5f528072f35183a75d4f80b6b74e7d61e14c7eccff4b8f2f5e4aa87aef497efee44878d4c5477f931f467f7c084575c46044⟩,
  ⟨39, 26, 0xadb9f8818022c1a01fd11167e7ff19b9f5d5ba767c81a8645edf95e6f7a8013125e200dfb87775f6c5dd1ffb528738160419ba0190886d8956e35b1fa42916a78a47fda601141c65805e45d9203b68f63864fe3d8a04e552618f472e182ccaae15f982a12978b04e845d714d57d71ea57b95b7f61d9d6a05bf4754853a16d4e006a5b51801790d420d1ae14f80500cd39fee2244c70549a12dff1d9b487697d011dfea44c46⟩,
  ⟨39, 26, 0x200ae9f818020fd601fff54d7e7e764b9f1ff4c497b8009ad1ea004c117980133d1ddfe47bc737dc3571c600b24b70800d935ba0096b16d807a7a5b21257946b7f7a3d5a1ff21656680c016d9209303c62ab3cf5d86430da560c711cb57de2bd7f5e4220bad75ea97025c690d4656dfe52ad5a9d218cd5295f6585391fe5d1498d0a105180438ed3e018a044e80036dd31d6f56d4b7f982c125ff63fa4873341011dddd57946⟩,
  ⟨43, 26, 0x12f972f814a2642201e74dad7c80097bdea0028007982d95d9e201958a777feb301d5ffa1867481f5555ba00c7146d7fc59a1aa050cb36580b13499200664d6380327558a5e9504619d7cb85839f84885f54199b97950b0f85d6efe0c971fe9eca5b7e90fa969d515125973d9eed620a84345781a09fd5a09a909559662c3d520608e15380574894a0029505180504a54201c4604f80308453a0c3eeb4d7dfc5f5311f3c244b826ee8525ff587c4844869ad1d5aa07e46⟩,
  ⟨40, 25, 0x650a2040b879bb202038c82f6f01cc17a7fd86a3cc1b7dd5e1f5854eeafb3dcd747dd4dd393ebd9d1c5fe171ad0fd6e32677ef5bf33406afed960722bcc7be164e618743983034c87b97dfa4642bcfe90b25d48af2a2e1d3a2ed6dce46e6b4ec934959791544ac4595db95e31c0faad0e186755aa1145aa57511614e2a15a0a5006eb6519a2a2927c10679d39fe3d0e985471c74b7f7a67a52eedc11258d48429072d70b47⟩,
  ⟨45, 26, 0x18528c5816b2147a020081f67b7fdf829ea00a4f47880e7381de007697767ff17f9d5ffecb0747ee4f51cdf58f34727ad77e9c60061086e7d1a265a5feb87e687f4c3dd9dfcf59f668020e9d9601df9d648294fa58e09ce3662e6c16ad8652f2cd605aa3e317d9581985e5a10529758f92d35c5bde7356dc302f55a798f0ed65edd76b588c95fb15e6476ef56931b479562da6125485bed994e209a5d528028e0546110b9e4e8015169360088cc4c3e06c752dff7d674a6c218dd2596f80f48⟩,
  ⟨36, 25, 0x5db323c0bf5c49201f2c7a0ef01aaa376928dc63a3fe9329cdfd8aa8e4fe49147180d7c4b84092e51be00156ad6ffaa61678953a9b2c08af8d9203d6b0c71d96ea62aaf6a7309fba23981d59108bef1354d5e4b284d2ebb2983571b8981cb6ecaa8d5a7b9202acbe71c59623c75aeaf1f4c8f56914e8caad34e0bd52c898b2a725308d5288447b28c6b1dad31ff9da094f8903049⟩,
  ⟨41, 25, 0xb50f2b817ff753404001809f257960ef7121dcb7a80a7ac3cbf40395e1f611caeee69171757efde639bfa5d15ca0493b0e101ecc96f791165373cd319db5f43bacd0fd7e3967798759b344cc50996db6e64c91e1c1663b2d39f311b3c59585b18700c0dcd61d5e75dfdcaeaf541a570ca0774b6e189975a7bccda2cbbca81d6260648caf3d5571569a34d9aad665ae952e87adaa70d989a527ac3aba8b191ab93dd01b069cffd2814a⟩,
  ⟨46, 25, 0x163d38102ffb140808006a9be411425dee191f3ef4ff68e4797ff53f3b39e034dd5fd7f4ee6ff58ce7278867eb8bf38091bdfadaf4dcfcaed56d7ff6d7b63be8285adeb78cad2f83dd26879acca33b8da65d9a5cbc66cb2d6a01648df456b1dd6e76188198882c2d287d6607fee5eafbf50a9579ce95fabad537aa5c773d13adbfbc79569fce524b2fe4b80588c8aababc8e625d5a531676ab3ed25654726d73a9c3552c149a39a06a2efdec95079aa7c27b5dea09358b4ebe989e72464b⟩,
  ⟨44, 26, 0x632161e05fac4fe80800f621ea0005fb797f0b3b1e2043a8177800ca99d9ffc278747c09f5dcdf20a7a727e49291c614f8bc707fc8651be0b9cdb6e7e15e4da5fa9c52687e72d559dfba2026687ac3959647e36e6488c6ad18e94a8af62053d5b98515b0276069ba2b97dfffa055e4fad5fd75b0b0c85c6c125816de1f81a5a7e8b95965da6342588bb0f315e2d24e95685f273d5606c7885430c19154d53ad24521da3375451e641d503f87fa53d97033b4e1ee28593541ee314c⟩,
  ⟨43, 26, 0x1f62d09818008cb9f5f154ac7b796e7fde9f12dc8797fc2455e203155b777c4ab45d5ffe62f737f6ed81ca003521717f024b9c20176246f7ba3351b9ffae646d8014585ae005dcf6880469c59a29d0676592179b99223fbf96370bd55d89cd0bb061747505d81ff2dc25f79bc0d57a02109c5d7cd23c571fc43685b7fb453169fec9a1597d3e9b9620319d95781900395a06405b558947ebd51a6cdfd536fde0c1493916d3515cfb2f9412fe50a4f6b2dc0138ffd5dc4d⟩,
  ⟨30, 26, 0x7fe0299f2000e7f797f21f4de1f757d2777ffc605da055ee37380f816dca015a24717fdec15ae07422c698078695a20134cb6780322a999fdcecb65750023991dafecc63620a72989ff8e40616cc1d6d81fd44e25f7d95ded7a3d3da15d883287d7209231e5b809054969618f665355029254813db9b514c79e3140c450474f⟩,
  ⟨31, 25, 0x3fe63c9e1ffcc4cef02d27d7381d592b94097c89c600cc82d2e9b7e86871cbb433b609bf199cc46f6caf188aa647ce9bb31b94dd0189771f22c0e550515f7dd2592f4bb1e3d7641e2bcb92fe5705b880238ad41eb6e9662c1038b0fe7958577ee524ab3f6fbf555fce7d8a8f4b8bf537eb2c1291be1179457ea65ea0d9191a4f⟩,
  ⟨40, 26, 0x7cbc21e05efed177d8001a31f220f6387b85876cde9ffd63578800eb65ddc8ec15767ff3dd1d2023e187380d2605ca048c18718e1dd6db1ff10266a790d551a5e4c6ca68784aa2d9dd3aa806666d508195e12b33647be29898dce51be62672dacd85e3cd5a607fd4c217dff6c6b5e8ac2c317623a4e95c9229f2d6e12411b5a819b42d6606df5b587f6deb15dfeed00567f829f555fe844d546d884e94db40147522abd959454eef0450⟩,
  ⟨40, 24, 0x7fce417e88192c7d80bec37c80406d7b7cd680777fbf93767feda9757fb96574845d6a73854e007281215f7178a2fa707fc0ec6f774bfa6d7029b96c7ff3db6b7fe7c66a8068e06987e9ce689b337167b467a4666381cb657f8044647e394d637775506242ead36146f3a45f806a6e5d80a18c5c82c98e5b822b555aa59322598080db586dd29557702b84566e61465558d2c4544a29cd5330c637527aa34851⟩,
  ⟨34, 25, 0x20bd328fb0015bb7c842dfc3dbfe266de9f21dbef0ff90d87758deb13ac009f7dd201cbb0e70109cd727d8bfeb732ee315b1feb186d701d9a46996f33e344c179a59e8003c8ccc233c3657c71c2b1aaefd3d893aecc2beea90fb5e802033aec033bdd726a0f96b70a5ab35aa442d92cd2056d5615ac39cae9bf00b564bac64aab93046150db3f56a69a43cb52⟩,
  ⟨37, 24, 0x64e957817da817808079a97e81da867d8114167c8fefe77b87bdbc7a93f7dd797d66a678503927758728ae738c177972bb70b47173b9d0706a4cfc6e5e2d4b6c6c11146b4ebc906adef4a0698c34b56887fc8a6797f1d26651db5f657527866471993a63639074627e79346179e4f1608958a15d8171a75c96642c5b82e5395a8c37aa5982501b58713ef3577b39b256574ae354⟩,
  ⟨39, 25, 0x1a2ac8a05f5816501008ec87e80214dbebf78d39f2810214f72f5a3c7aa3c6573cbf6de61e1fd4466eeb4a9627589dd41b95936079c5fddbbae0f7167f6f55e1aa373af3029b513e136d89b9c866bb87b1834ca697c1a22d46e2cf4022fa666793c5b2ba79d8d91f48c68c6fe9de96271329730be752ad7e2a11e8bb0174915ccf77222dd4df9e16aa0d800b301f5da5878cc4a2bbd26f9159f76686aafd665454⟩,
  ⟨36, 25, 0x650931c0b75a0ae01fe4b82ff03b2287d8059b43e3fcc709edfefc92f4fef0da797f9ee33c3fa9f85de012236eb0222a8749d108c39ca158b9ca02c954e2d0ea24707c0a59b7bc1fd79b9df0468dac5dee86c433d0735e1f6d39aa2169a0d304c20368814b7a33c0fbcc999efdde6caf4c831647f8d8d31beea2c189b4c4b6c30b9df05f8089d8af461e8d576e8ecb4b97971815b⟩,
  ⟨33, 23, 0x2648bc817aa7eb00fc6729fe3122abf51d14c7d7d1778f6ffa695e9f065dbcbc6f51787eabb0eee76eadda03f1abac0bd22749844c2e70289b1ca18967b8bdceab70757c30deb9f121b9f19acb6b3dd9f6c777a32d7172d75aa2790a34c127d4689092f4cf2e3b1599f2822b2bef97d645083ccc51542e17b603c0aede4a505c⟩,
  ⟨35, 23, 0x734b6a05e912b403f43797f80c3b6fd039311f5cdb1f3e3e405a7b8120d6f4fb8939e59d43cbc26369e7782ede4eb2e9545d20644539c02e6472907e32e22bbfa9c1e471bb7bebf296e697474da0e960db1e63ef35d72b9a6a899e9ed303f745a22c284b3c527cd667d6c7ccaf9d9d991f18fa3149eef65f989aecbd5203dd7649b77ae7bbc665b⟩,
  ⟨34, 24, 0x543e24817cd3c5807f59bb7f85ac577e8046077d7cd2507b8008387a7ede6879759c1e787eaed4777a53a976837c8575954d0f7482a268738070dd7281c1b5717f04c2707bb45f6f7d9ee26e3cd3b56d7d5d986c81ad1b6b9531ab6a8292f76980a6ec6881bcf36781d7d7667ebdaa657d4c35627f834a6188e0175f88d32c5eaa2bff5d91d8505c⟩,
  ⟨33, 24, 0x8cfa8481884857807f4ebf7e7fa9a07d8f21117c79fe5d7b7e0c7b7a81f7ce78828380777c887f757dbf0f747e4cee737ca81c727eb36f718551f17084cc736f8330746e9bfb986d19b0966c61c7a76b1ffe876a759f6b697b179b687f0f68677e921b66811da865833f566484c47a6398411c627c1b805f7517885e52f4e05d4c00045c⟩,
  ⟨32, 24, 0x8a423c81846f1c80804c877f7f74ac7e7f9e8b7d876bef7c80d3e67b7fb06f7a8089547883464c777c68937569e92a747f649a737f5163727f4004718f2fcf70900b506f8348526e9c131f6d1917ad6c22c8aa6b17737e6a7bb3386977d1c3688173e965975b4f6486af5263afcc6b627d6fe55f7c27e75e6cb1c45d4d6d715c⟩,
  ⟨32, 24, 0x8e79d68182783b807f05487e7f4ce57d83f0417c812f5f7b80b05f7a821318788af84277573e2476474836753b8272747ea75873862491708ac59a6faca3da6ec58d386d62e5ac6c5bd2566b7c02ac6a7bbe88697b9817687c91ff677bdf84668061e4658272f3648830be63872dce626c6d005f78632e5e6356fd5d7d4f9e5c⟩,
  ⟨33, 26, 0x2052d278180705620200427a7f7b808edf60702b87c804faf9edffb1ef7a8027471e601c9ed7885108b9dd5faec9767a127b5d5547561747f3bd4dcde9989f718a2b219c20e5d916f98c8121bad935606d3a094b1b13d280c6b6661629a9fe6f2a697fe1aed9e006adf6588590f9921184856390d7ca98a03982a617a6627d814c68ef5f72a53217967714b5d⟩,
  ⟨25, 24, 0x61044f814c40e47f99f0587c69a4267b7d15497a55378b7982ca4178867d3f776e1c39757fbda2747add827381f322708e931f6f98ab296e805dcc6d48623f6c2f07486b7f5efa69929c3a659156fb6483309363811eb7604eca335f516dd95e7d42fe5d⟩,
  ⟨25, 26, 0x1fd830e8169bd851e6014ce57886f3db9ddb0321076674052dd5e22682747c6cf11cdf7943c727f940a5c6481251709cdf0e5bddd845b6e75051f9b59a9ea66b7dea3c59df0366c668883639960e2fe1648147dc58e2da1936255f11c185c01eb1602e8e8b57d5037c65e⟩,
  ⟨24, 25, 0x8451fdc0bff559de607915af10498587779a8cabb3cfa0bdd22f226ce6fd19317275a9c3b8c50035dc1c128aadeda732b6e736eacb6bffd70db1ed5102d6ff2e516a80508334c074c6196015f56c900519963804474b1274b67d85bfe9a6c04f417c5f⟩,
  ⟨23, 25, 0x3fd647df60066a0f9126cb67b84aa173d413e619e618f6d4f11e01777772eaabbb2ceb50dd5feef30e6f28aae716a2bf33831e8d81bdcfaa84dcd09e306d77954fb634647e5ae218db4caff5c45647fe07d31bfc855588402d5ac2b2295760⟩,
  ⟨19, 24, 0x7b817d7c5f501e7b76f81f7a9bba63797e26887661ba2a7566fbff72c1e645716cdef3707044976f608a186d7fe3b96c718e1a6b7955c2696fb4996552120a647f8ca06363214b622a2e1d61⟩,
  ⟨21, 25, 0xf4e6667e82eff0bebffaef5edffa81ef4ffd5ee7978fdf5babbcbe09d1a7e9f4e788c6d672b8012838bbd39f9c1b350c0dee2f6166c2f04053540a4b45a20bbb6ccf0fca6d66697667329cc5e15919220f6c669b3ab62⟩,
  ⟨22, 24, 0x8015a2818247f27d8aedcd7c6f5afe7b7c97b27a7fc602797ea729777f71a27643fd0875566fb474b4894d737f58ba707f7e7c6f7f6d7a6e3e99db6c674d5e6b3020156a8547b669923182665f912b6562977d64725e4b63⟩,
  ⟨18, 22, 0x83b969f1c3cca7b77d4ade9eeca0797f9b31e1f54b0777e5659d8e0a22754cdb29d2cc89c7389d05dca84f65717dfd81bd03b7c6c1741a5aa24a04698370519e69c0066⟩,
  ⟨16, 23, 0x8129b5030172a5f6188d1be37631e7b7c2460f4fbd815e58e80fbaa6ac2074822b7ae773988dca6067cb8bfcbed6e76e040da5cd905b186b0cb5c1f24a69⟩,
  ⟨18, 23, 0x22f91040cd25897c648e40f6cfc895e9e4428bcc1182a7885b078eefe23f9d84884eba9dc01274c56892e704397dca6fc71b8aa29676f7a2976dcde18f9b5fae063651639a69⟩,
  ⟨15, 24, 0x5ba731817b2d557d7ce18d7c8145f77b7eeed17a8058a77781c4d6769bf1c1750eee86748064026f81e8396edc22696c8c60126b7317056a58427a69⟩,
  ⟨15, 23, 0xc4b15605d6fddbebd772d7c81c358f6fd2f69ea0257cbbc1c11376909126ea3b3809d202f4337c1788a6ed7695cd932a735ad9ab19b52f83e069⟩,
  ⟨14, 23, 0x1480d4c0be58677e7f3e2cfaf70ff9f2094abbdbf4b5b7a80a250ef069e65d850dbeba424cbb6ee691d4d95caeadad3e1b2b53839e869⟩,
  ⟨17, 25, 0xfa839c816efc113f3e4ae25f23429c0f700d10b7a831f65bbc8f8139d9314348ea3b3df1747dc3fcb9bfa6c15c9fe23d0e31360f46f851596b6de1146db1f610d6d6fc560c6a⟩,
  ⟨12, 24, 0x7fd9157d8017f07c81f5b378801fd5767fee95756a92b7732482d372398537715eaca0708081846f7fe6aa6c4c00476b⟩,
  ⟨16, 23, 0x7060a8fd0113a1f6477a33e2487957b35adf2f454c305e72dedcbc7638c5777fb37aecf8da01d13a6af39bdf608727f740ee2f7aa85b865c69b6bff01a6c⟩,
  ⟨15, 26, 0x1fff5df7e89bdc59f5fd99b37b7e0a9ade9fa67c0798b35b7de21f09cb7704c9619d1b506907375e55e9c9ea4f2c717e42661c1f433086f75f79fdb9ad33166d⟩,
  ⟨16, 25, 0x7ba82d40c03c9b9fa095c2cf8f8ea607b7248a63d3f1bf71e55decaef0c56997772531503b3ffb4e1d4d8fdc6e90416aa7280a750b8bb3a789c1faa674deffab1e6e⟩,
  ⟨16, 24, 0x7e67698191aa557e8b10c67c79d1877b69bcc57a7eef997963f69d7865831c774811b2767ff07175274ac974806af273853187728fc747716834aa706e92dd6f⟩,
  ⟨14, 23, 0x1f3907c0c038597db34ddcf8d5d4a9ed578793d3fafe8794ff990f0ed9e9ddc8e523bb401f8c755e2010e9337d6dca28170b8b3fdaa70⟩,
  ⟨15, 23, 0xfb34a205fca6d4053f8327e833978fb7c1c5df15f0f53dabeeb07a7af5c0f2c94911e1c1b23bb8806467682ea68ead93305d340c5a39c05ca771⟩,
  ⟨11, 23, 0x102b7be05d8dac3ea9f8bc7c8124def67c2319e998b11bcc5ef7c7882ba2eeefa8a85d1464dab9a6fbff72⟩,
  ⟨14, 22, 0x8ab2da06050ee805f2ad9f93a0aa7d1f1731f2278e57b2775d9ea033f3799b5b65e20cce577818971d90edef757d1b75d0b2b4573⟩,
  ⟨10, 23, 0x1f6dcdc0ab87cc7d469474f8b1b925ed66c6ebd3e1e4179819e4af100b505dce73a73a8f1d1774⟩,
  ⟨8, 24, 0x5990fb7da705ff7c42eb437b50335c7a664e9079d0dab5788e070177800a8b76⟩,
  ⟨9, 23, 0x4c99b4817fa9e8fd4ef009f46a392bd90ee567a22b008f35c477de2018533bb82a0576⟩,
  ⟨6, 24, 0x27363c7e8082e67d5ebce37b69324d7a7f986c797d7ce278⟩,
  ⟨8, 22, 0x7fe34a05ff3d7808b277df4963b67c4b7761edf23267a847099e52092378⟩,
  ⟨4, 23, 0x2e0dd2f8a8f335edfb9413d3df93779⟩,
  ⟨5, 20, 0xfc2a08182bd27d90fd47c219cc7b317e97a⟩,
  ⟨4, 23, 0xaf72d303007421f6086463e13d1517b⟩,
  ⟨3, 22, 0x322fb381823775f601a357c⟩,
  ⟨3, 19, 0x105196060aa6bf1be327d⟩,
  ⟨1, 22, 0xf41e281⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩,
  ⟨0, 1, 0x0⟩
]

private def linearData : PackedRow := ⟨130, 29, 0x289a710f0d922fa821007ec0d4aa6605465590287be27f3077a40c92efdf5c9227052a9618376afbc620bf263a1d7613210ba28259dbec0b76eb203fe9aefbe9d52803af4a4113bcd22347a7f30e2f6b8dcf509c7c8505e0cdc142ffbccd37febb1b3fb91e51f8d51f0fe66b33803079ac148f6ae3eedd1919495248dd224f487ab9deb37dde3166c15e8df89e6c0818d4dfb8201efd859297eb15423f7b9229facee9d0a80f4c84f4447471670cec9d9ff9356c30ab50a2f0c884fc467ccff7f30550d9c4571f044f146c21d1c74d1a2b763c103493ce95e1565958e3f095f9c384ddde1c0d0782a00f5da8fd76e5881bee944284a6622c7c53d26a3a889df51e9e10b7266432f9530903b05870fd04634e422e6499c433a6352d94286be5aa9f35a78641e15a5e20a866798542b89c8210e2572fd0b7fe7f97665bfbec07e010a7550123b297f93831c50869fa2b3ec434e642898f44da046c81fda3c9b65b23301068146684402bcbf9fe165c0fd788907f8264d3fde141dfee720f00dceb08dc6a27c72722b6693841110596378199769bfbf18bdeec024f01adfc281919c9c1d7778a63686871a3b2e88c026ebc19532220969c34fcb15f7800fa6ebfb52ef2032378d023b0da819cab4c132da7216d07113f108d2⟩

def triC : ℤ := 452835688
def triRadius : ℤ := 68719476736

def triQ (i j : ℕ) : ℤ :=
  4 * rowEntry (quadraticData.getD i ⟨0, 1, 0⟩) j

def triL (i : ℕ) : ℤ :=
  4 * signed (digit linearData.word linearData.width i) linearData.width

def quadraticRangeCheck (i : ℕ) : Bool :=
  (List.range 130).all fun j => decide (-triRadius ≤ triQ i j ∧ triQ i j < triRadius)

end OMA.Erdos1186HighTriangles

end

section

/-
The quadratic coefficients determine the linear coefficients of each
triangle, and its constant once its weight is given. This recovers the
other caches from the checked quadratic rows without rescanning triangles.
-/

namespace OMA.Erdos1186HighTriangles

open Finset
open scoped BigOperators

private theorem sum_slot_right (n j : ℕ) (hj : j < n) (x : ℤ)
    (p : Prop) [Decidable p] :
    (∑ i ∈ range n, if p ∧ i = j then x else 0) = if p then x else 0 := by
  by_cases hp : p <;> simp [hp, hj, sum_ite_eq']

private theorem sum_slot_left (n j : ℕ) (hj : j < n) (x : ℤ)
    (p : Prop) [Decidable p] :
    (∑ i ∈ range n, if i = j ∧ p then x else 0) = if p then x else 0 := by
  by_cases hp : p <;> simp [hp, hj, sum_ite_eq']

private theorem tq_row (n : ℕ) (t : TriT) (hj : t.j < n) (hk : t.k < n) (i : ℕ) :
    (∑ j ∈ range n, tq t i j) =
      4 * ((if i = t.i then t.s1 else 0) + (if i = t.j then t.s2 else 0) +
        (if i = t.i then t.s3 else 0)) := by
  simp only [tq, ← mul_sum, sum_add_distrib]
  rw [sum_slot_right n t.j hj, sum_slot_right n t.k hk, sum_slot_right n t.k hk]

private theorem tq_col (n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (i : ℕ) :
    (∑ j ∈ range n, tq t j i) =
      4 * ((if i = t.j then t.s1 else 0) + (if i = t.k then t.s2 else 0) +
        (if i = t.k then t.s3 else 0)) := by
  simp only [tq, ← mul_sum, sum_add_distrib]
  rw [sum_slot_left n t.i hi, sum_slot_left n t.j hj, sum_slot_left n t.i hi]

private theorem tq_row_col (n : ℕ) (t : TriT) (hi : t.i < n)
    (hj : t.j < n) (hk : t.k < n) (i : ℕ) :
    (∑ j ∈ range n, (tq t i j + tq t j i)) = -2 * tl t i := by
  rw [sum_add_distrib, tq_row n t hj hk, tq_col n t hi hj]
  unfold tl
  split_ifs <;> ring

private theorem tq_sum (n : ℕ) (t : TriT) (hi : t.i < n)
    (hj : t.j < n) (hk : t.k < n) :
    (∑ i ∈ range n, ∑ j ∈ range n, tq t i j) = 4 * (tc t - 1) := by
  simp_rw [tq_row n t hj hk]
  rw [← mul_sum, sum_add_distrib, sum_add_distrib]
  simp [sum_ite_eq', hi, hj, tc]
  ring

/-- An incident edge contributes twice its signed linear coefficient. -/
theorem aggregate_linear_of_pairs (n : ℕ) (ts : List TriT)
    (h : ∀ t ∈ ts, t.ok n = true) (i : ℕ) :
    (∑ j ∈ range n, (qS ts i j + qS ts j i)) = -2 * lS ts i := by
  induction ts with
  | nil => simp [qS, lS]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hts : ∀ u ∈ ts, u.ok n = true := fun u hu => h u (List.mem_cons_of_mem _ hu)
    unfold TriT.ok at ht
    obtain ⟨hI, hJ, hK, _⟩ := of_decide_eq_true ht
    have q_cons (j k : ℕ) : qS (t :: ts) j k = t.w * tq t j k + qS ts j k := by simp [qS]
    have lin_cons : lS (t :: ts) i = t.w * tl t i + lS ts i := by simp [lS]
    calc
      _ = ∑ j ∈ range n, (t.w * (tq t i j + tq t j i) + (qS ts i j + qS ts j i)) := by
        apply sum_congr rfl
        intro j _
        rw [q_cons, q_cons]
        ring
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, tq_row_col n t hI hJ hK, ih hts, lin_cons]
        ring

/-- Apart from the unit term, triangle constants sum the signed edge weights. -/
theorem aggregate_constant_of_pairs (n : ℕ) (ts : List TriT)
    (h : ∀ t ∈ ts, t.ok n = true) :
    (∑ i ∈ range n, ∑ j ∈ range n, qS ts i j) = 4 * (cS ts - weightSum ts) := by
  induction ts with
  | nil => simp [qS, cS, weightSum]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hts : ∀ u ∈ ts, u.ok n = true := fun u hu => h u (List.mem_cons_of_mem _ hu)
    unfold TriT.ok at ht
    obtain ⟨hI, hJ, hK, _⟩ := of_decide_eq_true ht
    have q_cons (j k : ℕ) : qS (t :: ts) j k = t.w * tq t j k + qS ts j k := by simp [qS]
    have const_cons : cS (t :: ts) = t.w * tc t + cS ts := by simp [cS]
    have weight_cons : weightSum (t :: ts) = t.w + weightSum ts := by simp [weightSum]
    simp_rw [q_cons, sum_add_distrib, ← mul_sum]
    rw [tq_sum n t hI hJ hK, ih hts, const_cons, weight_cons]
    ring

/-- The checked row totals identify the constant through the cheaper linear sum. -/
theorem aggregate_constant_of_linear (n : ℕ) (ts : List TriT)
    (h : ∀ t ∈ ts, t.ok n = true) :
    (∑ i ∈ range n, lS ts i) = 4 * (weightSum ts - cS ts) := by
  have hs := sum_congr (s₁ := range n) rfl (fun i _ => aggregate_linear_of_pairs n ts h i)
  have hswap : (∑ i ∈ range n, ∑ j ∈ range n, qS ts j i) =
      ∑ i ∈ range n, ∑ j ∈ range n, qS ts i j := by rw [sum_comm]
  simp only [sum_add_distrib, ← mul_sum] at hs
  rw [hswap, aggregate_constant_of_pairs n ts h] at hs
  linarith only [hs]

end OMA.Erdos1186HighTriangles

end

section

/- Verify the high-region cached triangle polynomial using indexed row checks. -/

namespace OMA.Erdos1186HighTriangles

open Finset OMA.Erdos1186HighBuckets
open scoped BigOperators

private def firstGroups (i : ℕ) : List (List TriT) := (bucketsFor i).map trianglesOf

private def expectedRowWeight (i : ℕ) : ℤ := expectedWeightByFirst.getD i 0

def expectedWeight : ℤ := ((List.range 130).map expectedRowWeight).sum

def indexedValidityCheck (i : ℕ) : Bool := (firstGroups i).all fun g =>
  g.all fun t => t.ok 130

def indexedWeightCheck (i : ℕ) : Bool :=
  decide (groupedSum TriT.w (firstGroups i) = expectedRowWeight i)

def indexedQuadraticCheck (i : ℕ) : Bool :=
  decide (fastPairWord (2 * triRadius) i = pack (2 * triRadius) 130 (triQ i))

def indexedLinearCheck (i : ℕ) : Bool :=
  decide (((List.range 130).map fun j => triQ i j + triQ j i).sum = -2 * triL i)

def indexedWeightBoundCheck : Bool := decide (12 * expectedWeight < triRadius)

def indexedConstantCheck : Bool :=
  decide (((List.range 130).map triL).sum = 4 * (expectedWeight - triC))

def indexedRowCheck (i : ℕ) : Bool :=
  indexedValidityCheck i && (indexedWeightCheck i &&
    (indexedQuadraticCheck i && (quadraticRangeCheck i && indexedLinearCheck i)))

private theorem first_partition (f : TriT → ℤ) (is : List ℕ) :
    groupedSum f ((is.flatMap bucketsFor).map trianglesOf) =
      (is.map fun i => groupedSum f (firstGroups i)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      have hadd (a b : List (List TriT)) :
          groupedSum f (a ++ b) = groupedSum f a + groupedSum f b := by
        simp [groupedSum]
      rw [List.flatMap_cons, List.map_append, hadd, ih, List.map_cons, List.sum_cons]
      rfl

private theorem valid_of_rows (h : ∀ i < 130, indexedValidityCheck i = true) :
    ∀ t ∈ groups.flatten, t.ok 130 = true := by
  intro t ht
  obtain ⟨g, hg, htg⟩ := List.mem_flatten.mp ht
  obtain ⟨bucket, hb, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, hi, hbi⟩ := List.mem_flatMap.mp hb
  have hg : trianglesOf bucket ∈ firstGroups i := List.mem_map.mpr ⟨bucket, hbi, rfl⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp (h i (List.mem_range.mp hi)) _ hg) t htg

private theorem weight_of_rows (h : ∀ i < 130, indexedWeightCheck i = true) :
    weightSum groups.flatten = expectedWeight := by
  unfold weightSum expectedWeight
  rw [← groupedSum_eq_flatten]
  change groupedSum TriT.w (((List.range 130).flatMap bucketsFor).map trianglesOf) = _
  rw [first_partition]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  exact of_decide_eq_true (h i (List.mem_range.mp hi))

private theorem sum_list_range (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

/-- The single-row numerical checks and two small scalar checks certify the
same cached triangle polynomial used by the residual reconstruction. -/
theorem indexed_triangles_nonneg
    (hRows : ∀ i < 130, indexedRowCheck i = true)
    (hBound : indexedWeightBoundCheck = true) (hConstant : indexedConstantCheck = true)
    (y : ℕ → ℝ) (hy : ∀ i < 130, 0 ≤ y i ∧ y i ≤ 1) :
    0 ≤ evq 130 triC triL triQ y := by
  have flags (i : ℕ) (hi : i < 130) :
      indexedValidityCheck i = true ∧ indexedWeightCheck i = true ∧
      indexedQuadraticCheck i = true ∧ quadraticRangeCheck i = true ∧
      indexedLinearCheck i = true := by
    simpa only [indexedRowCheck, Bool.and_eq_true] using hRows i hi
  have hv := valid_of_rows (fun i hi => (flags i hi).1)
  have hw := weight_of_rows (fun i hi => (flags i hi).2.1)
  have hb : 12 * weightSum groups.flatten < triRadius := by
    rw [hw]
    exact of_decide_eq_true hBound
  have hr (i : ℕ) (hi : i < 130) (j : ℕ) (hj : j < 130) : -triRadius ≤ triQ i j ∧ triQ i j < triRadius :=
    of_decide_eq_true (List.all_eq_true.mp (flags i hi).2.2.2.1 j (List.mem_range.mpr hj))
  have hrow (i : ℕ) (hi : i < 130) :
      pairWord (2 * triRadius) i groups.flatten = pack (2 * triRadius) 130 (triQ i) := by
    rw [← fastPairWord_eq]
    exact of_decide_eq_true (flags i hi).2.2.1
  have hq := quadratic_cache_eq 130 groups.flatten triQ hv
    (by norm_num [triRadius]) hb hr hrow
  have hl (i : ℕ) (hi : i < 130) : lS groups.flatten i = triL i := by
    have hg := aggregate_linear_of_pairs 130 groups.flatten hv i
    have hsum : (∑ j ∈ range 130, (qS groups.flatten i j + qS groups.flatten j i)) =
        ∑ j ∈ range 130, (triQ i j + triQ j i) := by
      apply sum_congr rfl
      intro j hj
      rw [hq i hi j (mem_range.mp hj), hq j (mem_range.mp hj) i hi]
    have hc : ((List.range 130).map fun j => triQ i j + triQ j i).sum = -2 * triL i :=
      of_decide_eq_true (flags i hi).2.2.2.2
    rw [sum_list_range] at hc
    linarith only [hg, hsum, hc]
  have hc : cS groups.flatten = triC := by
    have hg := aggregate_constant_of_linear 130 groups.flatten hv
    have hsum : (∑ i ∈ range 130, lS groups.flatten i) = ∑ i ∈ range 130, triL i :=
      sum_congr rfl (fun i hi => hl i (mem_range.mp hi))
    have hd : ((List.range 130).map triL).sum = 4 * (expectedWeight - triC) :=
      of_decide_eq_true hConstant
    rw [sum_list_range] at hd
    linarith only [hg, hsum, hd, hw]
  have hn := aggregate_nonneg 130 y hy groups.flatten hv
  unfold evq at hn ⊢
  rw [hc] at hn
  have hlin : (∑ i ∈ range 130, (lS groups.flatten i : ℝ) * y i) =
      ∑ i ∈ range 130, (triL i : ℝ) * y i := by
    apply sum_congr rfl
    intro i hi
    rw [hl i (mem_range.mp hi)]
  have hquad : (∑ i ∈ range 130, ∑ j ∈ range 130, (qS groups.flatten i j : ℝ) * (y i * y j)) =
      ∑ i ∈ range 130, ∑ j ∈ range 130, (triQ i j : ℝ) * (y i * y j) := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hq i (mem_range.mp hi) j (mem_range.mp hj)]
  rwa [hlin, hquad] at hn

end OMA.Erdos1186HighTriangles

end

section

/- The concrete row tests for the complete high-slab witness. -/

namespace OMA.Erdos1186High

open OMA.Erdos1186HighTriangles OMA.Erdos1186Region2

def highTriangles : Coefficients := ⟨triC, triL, triQ⟩

def highRow (i : ℕ) : Bool :=
  dominanceCheck i && (if i < 130 then constantRowCheck i && budgetCheck highTriangles i else true)

theorem high_box (hRows : ∀ i < 131, highRow i = true)
    (hTri : ∀ i < 130, indexedRowCheck i = true)
    (hTriBound : indexedWeightBoundCheck = true) (hTriConst : indexedConstantCheck = true)
    (hZero : (highSurplus highTriangles).constant = 0)
    (y : ℕ → ℝ) (hy : ∀ i < 130, 0 ≤ y i ∧ y i ≤ 1)
    (hm0 : (3/10 : ℝ) ≤ g24Mass y) (hm1 : g24Mass y ≤ (2/5 : ℝ)) :
    0 ≤ g24Objective y := by
  have hsplit (i : ℕ) (hi : i < 131) : dominanceCheck i = true ∧
      (if i < 130 then constantRowCheck i && budgetCheck highTriangles i else true) = true := by
    simpa only [highRow, Bool.and_eq_true] using hRows i hi
  have hflags (i : ℕ) (hi : i < 130) : constantRowCheck i = true ∧ budgetCheck highTriangles i = true := by
    simpa only [Bool.and_eq_true, if_pos hi] using (hsplit i (by omega)).2
  have hdom (i : ℕ) (hi : i < 131) : dominanceCheck i = true := (hsplit i hi).1
  have htri (z : ℕ → ℝ) (hz : ∀ i < 130, 0 ≤ z i ∧ z i ≤ 1) :
      0 ≤ highTriangles.evaluate 130 z :=
    indexed_triangles_nonneg hTri hTriBound hTriConst z hz
  exact high_box_of_checks highTriangles htri (fun i hi => (hflags i hi).1)
    hdom (fun i hi => (hflags i hi).2) hZero y hy hm0 hm1

end OMA.Erdos1186High

end

namespace OMA.Erdos1186High

open OMA.Erdos1186HighTriangles

private def Rows (f : ℕ → Bool) (a b : ℕ) : Prop :=
  ∀ i, a ≤ i → i < b → f i = true

private theorem rowsEnd (f : ℕ → Bool) (a : ℕ) : Rows f a a := by
  intro i hlo hhi
  omega

private theorem rowsCons {f : ℕ → Bool} {a b : ℕ} (h : f a = true)
    (ht : Rows f (a+1) b) : Rows f a b := by
  intro i hlo hhi
  obtain rfl | hlt := Nat.eq_or_lt_of_le hlo
  · exact h
  · exact ht i (by omega) hhi

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
section


private theorem d0 : highRow 0 = true := Eq.refl true
private theorem d1 : highRow 1 = true := Eq.refl true
private theorem d2 : highRow 2 = true := Eq.refl true
private theorem d3 : highRow 3 = true := Eq.refl true
private theorem d4 : highRow 4 = true := Eq.refl true
private theorem d5 : highRow 5 = true := Eq.refl true
private theorem d6 : highRow 6 = true := Eq.refl true
private theorem d7 : highRow 7 = true := Eq.refl true
private theorem d8 : highRow 8 = true := Eq.refl true
private theorem d9 : highRow 9 = true := Eq.refl true
private theorem d10 : highRow 10 = true := Eq.refl true
private theorem d11 : highRow 11 = true := Eq.refl true
private theorem d12 : highRow 12 = true := Eq.refl true
private theorem d13 : highRow 13 = true := Eq.refl true
private theorem d14 : highRow 14 = true := Eq.refl true
private theorem d15 : highRow 15 = true := Eq.refl true
private theorem d16 : highRow 16 = true := Eq.refl true
private theorem d17 : highRow 17 = true := Eq.refl true
private theorem d18 : highRow 18 = true := Eq.refl true
private theorem d19 : highRow 19 = true := Eq.refl true
private theorem d20 : highRow 20 = true := Eq.refl true
private theorem d21 : highRow 21 = true := Eq.refl true
private theorem d22 : highRow 22 = true := Eq.refl true
private theorem d23 : highRow 23 = true := Eq.refl true
private theorem d24 : highRow 24 = true := Eq.refl true
private theorem d25 : highRow 25 = true := Eq.refl true
private theorem d26 : highRow 26 = true := Eq.refl true
private theorem d27 : highRow 27 = true := Eq.refl true
private theorem d28 : highRow 28 = true := Eq.refl true
private theorem d29 : highRow 29 = true := Eq.refl true
private theorem d30 : highRow 30 = true := Eq.refl true
private theorem d31 : highRow 31 = true := Eq.refl true
private theorem d32 : highRow 32 = true := Eq.refl true
private theorem d33 : highRow 33 = true := Eq.refl true
private theorem d34 : highRow 34 = true := Eq.refl true
private theorem d35 : highRow 35 = true := Eq.refl true
private theorem d36 : highRow 36 = true := Eq.refl true
private theorem d37 : highRow 37 = true := Eq.refl true
private theorem d38 : highRow 38 = true := Eq.refl true
private theorem d39 : highRow 39 = true := Eq.refl true
private theorem d40 : highRow 40 = true := Eq.refl true
private theorem d41 : highRow 41 = true := Eq.refl true
private theorem d42 : highRow 42 = true := Eq.refl true
private theorem d43 : highRow 43 = true := Eq.refl true
private theorem d44 : highRow 44 = true := Eq.refl true
private theorem d45 : highRow 45 = true := Eq.refl true
private theorem d46 : highRow 46 = true := Eq.refl true
private theorem d47 : highRow 47 = true := Eq.refl true
private theorem d48 : highRow 48 = true := Eq.refl true
private theorem d49 : highRow 49 = true := Eq.refl true
private theorem d50 : highRow 50 = true := Eq.refl true
private theorem d51 : highRow 51 = true := Eq.refl true
private theorem d52 : highRow 52 = true := Eq.refl true
private theorem d53 : highRow 53 = true := Eq.refl true
private theorem d54 : highRow 54 = true := Eq.refl true
private theorem d55 : highRow 55 = true := Eq.refl true
private theorem d56 : highRow 56 = true := Eq.refl true
private theorem d57 : highRow 57 = true := Eq.refl true
private theorem d58 : highRow 58 = true := Eq.refl true
private theorem d59 : highRow 59 = true := Eq.refl true
private theorem d60 : highRow 60 = true := Eq.refl true
private theorem d61 : highRow 61 = true := Eq.refl true
private theorem d62 : highRow 62 = true := Eq.refl true
private theorem d63 : highRow 63 = true := Eq.refl true
private theorem d64 : highRow 64 = true := Eq.refl true
private theorem d65 : highRow 65 = true := Eq.refl true
private theorem d66 : highRow 66 = true := Eq.refl true
private theorem d67 : highRow 67 = true := Eq.refl true
private theorem d68 : highRow 68 = true := Eq.refl true
private theorem d69 : highRow 69 = true := Eq.refl true
private theorem d70 : highRow 70 = true := Eq.refl true
private theorem d71 : highRow 71 = true := Eq.refl true
private theorem d72 : highRow 72 = true := Eq.refl true
private theorem d73 : highRow 73 = true := Eq.refl true
private theorem d74 : highRow 74 = true := Eq.refl true
private theorem d75 : highRow 75 = true := Eq.refl true
private theorem d76 : highRow 76 = true := Eq.refl true
private theorem d77 : highRow 77 = true := Eq.refl true
private theorem d78 : highRow 78 = true := Eq.refl true
private theorem d79 : highRow 79 = true := Eq.refl true
private theorem d80 : highRow 80 = true := Eq.refl true
private theorem d81 : highRow 81 = true := Eq.refl true
private theorem d82 : highRow 82 = true := Eq.refl true
private theorem d83 : highRow 83 = true := Eq.refl true
private theorem d84 : highRow 84 = true := Eq.refl true
private theorem d85 : highRow 85 = true := Eq.refl true
private theorem d86 : highRow 86 = true := Eq.refl true
private theorem d87 : highRow 87 = true := Eq.refl true
private theorem d88 : highRow 88 = true := Eq.refl true
private theorem d89 : highRow 89 = true := Eq.refl true
private theorem d90 : highRow 90 = true := Eq.refl true
private theorem d91 : highRow 91 = true := Eq.refl true
private theorem d92 : highRow 92 = true := Eq.refl true
private theorem d93 : highRow 93 = true := Eq.refl true
private theorem d94 : highRow 94 = true := Eq.refl true
private theorem d95 : highRow 95 = true := Eq.refl true
private theorem d96 : highRow 96 = true := Eq.refl true
private theorem d97 : highRow 97 = true := Eq.refl true
private theorem d98 : highRow 98 = true := Eq.refl true
private theorem d99 : highRow 99 = true := Eq.refl true
private theorem d100 : highRow 100 = true := Eq.refl true
private theorem d101 : highRow 101 = true := Eq.refl true
private theorem d102 : highRow 102 = true := Eq.refl true
private theorem d103 : highRow 103 = true := Eq.refl true
private theorem d104 : highRow 104 = true := Eq.refl true
private theorem d105 : highRow 105 = true := Eq.refl true
private theorem d106 : highRow 106 = true := Eq.refl true
private theorem d107 : highRow 107 = true := Eq.refl true
private theorem d108 : highRow 108 = true := Eq.refl true
private theorem d109 : highRow 109 = true := Eq.refl true
private theorem d110 : highRow 110 = true := Eq.refl true
private theorem d111 : highRow 111 = true := Eq.refl true
private theorem d112 : highRow 112 = true := Eq.refl true
private theorem d113 : highRow 113 = true := Eq.refl true
private theorem d114 : highRow 114 = true := Eq.refl true
private theorem d115 : highRow 115 = true := Eq.refl true
private theorem d116 : highRow 116 = true := Eq.refl true
private theorem d117 : highRow 117 = true := Eq.refl true
private theorem d118 : highRow 118 = true := Eq.refl true
private theorem d119 : highRow 119 = true := Eq.refl true
private theorem d120 : highRow 120 = true := Eq.refl true
private theorem d121 : highRow 121 = true := Eq.refl true
private theorem d122 : highRow 122 = true := Eq.refl true
private theorem d123 : highRow 123 = true := Eq.refl true
private theorem d124 : highRow 124 = true := Eq.refl true
private theorem d125 : highRow 125 = true := Eq.refl true
private theorem d126 : highRow 126 = true := Eq.refl true
private theorem d127 : highRow 127 = true := Eq.refl true
private theorem d128 : highRow 128 = true := Eq.refl true
private theorem d129 : highRow 129 = true := Eq.refl true
private theorem d130 : highRow 130 = true := Eq.refl true
private theorem dAll : Rows highRow 0 131 :=
  rowsCons d0 <| rowsCons d1 <| rowsCons d2 <| rowsCons d3 <| rowsCons d4 <|
  rowsCons d5 <| rowsCons d6 <| rowsCons d7 <| rowsCons d8 <| rowsCons d9 <|
  rowsCons d10 <| rowsCons d11 <| rowsCons d12 <| rowsCons d13 <| rowsCons d14 <|
  rowsCons d15 <| rowsCons d16 <| rowsCons d17 <| rowsCons d18 <| rowsCons d19 <|
  rowsCons d20 <| rowsCons d21 <| rowsCons d22 <| rowsCons d23 <| rowsCons d24 <|
  rowsCons d25 <| rowsCons d26 <| rowsCons d27 <| rowsCons d28 <| rowsCons d29 <|
  rowsCons d30 <| rowsCons d31 <| rowsCons d32 <| rowsCons d33 <| rowsCons d34 <|
  rowsCons d35 <| rowsCons d36 <| rowsCons d37 <| rowsCons d38 <| rowsCons d39 <|
  rowsCons d40 <| rowsCons d41 <| rowsCons d42 <| rowsCons d43 <| rowsCons d44 <|
  rowsCons d45 <| rowsCons d46 <| rowsCons d47 <| rowsCons d48 <| rowsCons d49 <|
  rowsCons d50 <| rowsCons d51 <| rowsCons d52 <| rowsCons d53 <| rowsCons d54 <|
  rowsCons d55 <| rowsCons d56 <| rowsCons d57 <| rowsCons d58 <| rowsCons d59 <|
  rowsCons d60 <| rowsCons d61 <| rowsCons d62 <| rowsCons d63 <| rowsCons d64 <|
  rowsCons d65 <| rowsCons d66 <| rowsCons d67 <| rowsCons d68 <| rowsCons d69 <|
  rowsCons d70 <| rowsCons d71 <| rowsCons d72 <| rowsCons d73 <| rowsCons d74 <|
  rowsCons d75 <| rowsCons d76 <| rowsCons d77 <| rowsCons d78 <| rowsCons d79 <|
  rowsCons d80 <| rowsCons d81 <| rowsCons d82 <| rowsCons d83 <| rowsCons d84 <|
  rowsCons d85 <| rowsCons d86 <| rowsCons d87 <| rowsCons d88 <| rowsCons d89 <|
  rowsCons d90 <| rowsCons d91 <| rowsCons d92 <| rowsCons d93 <| rowsCons d94 <|
  rowsCons d95 <| rowsCons d96 <| rowsCons d97 <| rowsCons d98 <| rowsCons d99 <|
  rowsCons d100 <| rowsCons d101 <| rowsCons d102 <| rowsCons d103 <| rowsCons d104 <|
  rowsCons d105 <| rowsCons d106 <| rowsCons d107 <| rowsCons d108 <| rowsCons d109 <|
  rowsCons d110 <| rowsCons d111 <| rowsCons d112 <| rowsCons d113 <| rowsCons d114 <|
  rowsCons d115 <| rowsCons d116 <| rowsCons d117 <| rowsCons d118 <| rowsCons d119 <|
  rowsCons d120 <| rowsCons d121 <| rowsCons d122 <| rowsCons d123 <| rowsCons d124 <|
  rowsCons d125 <| rowsCons d126 <| rowsCons d127 <| rowsCons d128 <| rowsCons d129 <|
  rowsCons d130 <| rowsEnd highRow 131
private theorem t0 : indexedRowCheck 0 = true := Eq.refl true
private theorem t1 : indexedRowCheck 1 = true := Eq.refl true
private theorem t2 : indexedRowCheck 2 = true := Eq.refl true
private theorem t3 : indexedRowCheck 3 = true := Eq.refl true
private theorem t4 : indexedRowCheck 4 = true := Eq.refl true
private theorem t5 : indexedRowCheck 5 = true := Eq.refl true
private theorem t6 : indexedRowCheck 6 = true := Eq.refl true
private theorem t7 : indexedRowCheck 7 = true := Eq.refl true
private theorem t8 : indexedRowCheck 8 = true := Eq.refl true
private theorem t9 : indexedRowCheck 9 = true := Eq.refl true
private theorem t10 : indexedRowCheck 10 = true := Eq.refl true
private theorem t11 : indexedRowCheck 11 = true := Eq.refl true
private theorem t12 : indexedRowCheck 12 = true := Eq.refl true
private theorem t13 : indexedRowCheck 13 = true := Eq.refl true
private theorem t14 : indexedRowCheck 14 = true := Eq.refl true
private theorem t15 : indexedRowCheck 15 = true := Eq.refl true
private theorem t16 : indexedRowCheck 16 = true := Eq.refl true
private theorem t17 : indexedRowCheck 17 = true := Eq.refl true
private theorem t18 : indexedRowCheck 18 = true := Eq.refl true
private theorem t19 : indexedRowCheck 19 = true := Eq.refl true
private theorem t20 : indexedRowCheck 20 = true := Eq.refl true
private theorem t21 : indexedRowCheck 21 = true := Eq.refl true
private theorem t22 : indexedRowCheck 22 = true := Eq.refl true
private theorem t23 : indexedRowCheck 23 = true := Eq.refl true
private theorem t24 : indexedRowCheck 24 = true := Eq.refl true
private theorem t25 : indexedRowCheck 25 = true := Eq.refl true
private theorem t26 : indexedRowCheck 26 = true := Eq.refl true
private theorem t27 : indexedRowCheck 27 = true := Eq.refl true
private theorem t28 : indexedRowCheck 28 = true := Eq.refl true
private theorem t29 : indexedRowCheck 29 = true := Eq.refl true
private theorem t30 : indexedRowCheck 30 = true := Eq.refl true
private theorem t31 : indexedRowCheck 31 = true := Eq.refl true
private theorem t32 : indexedRowCheck 32 = true := Eq.refl true
private theorem t33 : indexedRowCheck 33 = true := Eq.refl true
private theorem t34 : indexedRowCheck 34 = true := Eq.refl true
private theorem t35 : indexedRowCheck 35 = true := Eq.refl true
private theorem t36 : indexedRowCheck 36 = true := Eq.refl true
private theorem t37 : indexedRowCheck 37 = true := Eq.refl true
private theorem t38 : indexedRowCheck 38 = true := Eq.refl true
private theorem t39 : indexedRowCheck 39 = true := Eq.refl true
private theorem t40 : indexedRowCheck 40 = true := Eq.refl true
private theorem t41 : indexedRowCheck 41 = true := Eq.refl true
private theorem t42 : indexedRowCheck 42 = true := Eq.refl true
private theorem t43 : indexedRowCheck 43 = true := Eq.refl true
private theorem t44 : indexedRowCheck 44 = true := Eq.refl true
private theorem t45 : indexedRowCheck 45 = true := Eq.refl true
private theorem t46 : indexedRowCheck 46 = true := Eq.refl true
private theorem t47 : indexedRowCheck 47 = true := Eq.refl true
private theorem t48 : indexedRowCheck 48 = true := Eq.refl true
private theorem t49 : indexedRowCheck 49 = true := Eq.refl true
private theorem t50 : indexedRowCheck 50 = true := Eq.refl true
private theorem t51 : indexedRowCheck 51 = true := Eq.refl true
private theorem t52 : indexedRowCheck 52 = true := Eq.refl true
private theorem t53 : indexedRowCheck 53 = true := Eq.refl true
private theorem t54 : indexedRowCheck 54 = true := Eq.refl true
private theorem t55 : indexedRowCheck 55 = true := Eq.refl true
private theorem t56 : indexedRowCheck 56 = true := Eq.refl true
private theorem t57 : indexedRowCheck 57 = true := Eq.refl true
private theorem t58 : indexedRowCheck 58 = true := Eq.refl true
private theorem t59 : indexedRowCheck 59 = true := Eq.refl true
private theorem t60 : indexedRowCheck 60 = true := Eq.refl true
private theorem t61 : indexedRowCheck 61 = true := Eq.refl true
private theorem t62 : indexedRowCheck 62 = true := Eq.refl true
private theorem t63 : indexedRowCheck 63 = true := Eq.refl true
private theorem t64 : indexedRowCheck 64 = true := Eq.refl true
private theorem t65 : indexedRowCheck 65 = true := Eq.refl true
private theorem t66 : indexedRowCheck 66 = true := Eq.refl true
private theorem t67 : indexedRowCheck 67 = true := Eq.refl true
private theorem t68 : indexedRowCheck 68 = true := Eq.refl true
private theorem t69 : indexedRowCheck 69 = true := Eq.refl true
private theorem t70 : indexedRowCheck 70 = true := Eq.refl true
private theorem t71 : indexedRowCheck 71 = true := Eq.refl true
private theorem t72 : indexedRowCheck 72 = true := Eq.refl true
private theorem t73 : indexedRowCheck 73 = true := Eq.refl true
private theorem t74 : indexedRowCheck 74 = true := Eq.refl true
private theorem t75 : indexedRowCheck 75 = true := Eq.refl true
private theorem t76 : indexedRowCheck 76 = true := Eq.refl true
private theorem t77 : indexedRowCheck 77 = true := Eq.refl true
private theorem t78 : indexedRowCheck 78 = true := Eq.refl true
private theorem t79 : indexedRowCheck 79 = true := Eq.refl true
private theorem t80 : indexedRowCheck 80 = true := Eq.refl true
private theorem t81 : indexedRowCheck 81 = true := Eq.refl true
private theorem t82 : indexedRowCheck 82 = true := Eq.refl true
private theorem t83 : indexedRowCheck 83 = true := Eq.refl true
private theorem t84 : indexedRowCheck 84 = true := Eq.refl true
private theorem t85 : indexedRowCheck 85 = true := Eq.refl true
private theorem t86 : indexedRowCheck 86 = true := Eq.refl true
private theorem t87 : indexedRowCheck 87 = true := Eq.refl true
private theorem t88 : indexedRowCheck 88 = true := Eq.refl true
private theorem t89 : indexedRowCheck 89 = true := Eq.refl true
private theorem t90 : indexedRowCheck 90 = true := Eq.refl true
private theorem t91 : indexedRowCheck 91 = true := Eq.refl true
private theorem t92 : indexedRowCheck 92 = true := Eq.refl true
private theorem t93 : indexedRowCheck 93 = true := Eq.refl true
private theorem t94 : indexedRowCheck 94 = true := Eq.refl true
private theorem t95 : indexedRowCheck 95 = true := Eq.refl true
private theorem t96 : indexedRowCheck 96 = true := Eq.refl true
private theorem t97 : indexedRowCheck 97 = true := Eq.refl true
private theorem t98 : indexedRowCheck 98 = true := Eq.refl true
private theorem t99 : indexedRowCheck 99 = true := Eq.refl true
private theorem t100 : indexedRowCheck 100 = true := Eq.refl true
private theorem t101 : indexedRowCheck 101 = true := Eq.refl true
private theorem t102 : indexedRowCheck 102 = true := Eq.refl true
private theorem t103 : indexedRowCheck 103 = true := Eq.refl true
private theorem t104 : indexedRowCheck 104 = true := Eq.refl true
private theorem t105 : indexedRowCheck 105 = true := Eq.refl true
private theorem t106 : indexedRowCheck 106 = true := Eq.refl true
private theorem t107 : indexedRowCheck 107 = true := Eq.refl true
private theorem t108 : indexedRowCheck 108 = true := Eq.refl true
private theorem t109 : indexedRowCheck 109 = true := Eq.refl true
private theorem t110 : indexedRowCheck 110 = true := Eq.refl true
private theorem t111 : indexedRowCheck 111 = true := Eq.refl true
private theorem t112 : indexedRowCheck 112 = true := Eq.refl true
private theorem t113 : indexedRowCheck 113 = true := Eq.refl true
private theorem t114 : indexedRowCheck 114 = true := Eq.refl true
private theorem t115 : indexedRowCheck 115 = true := Eq.refl true
private theorem t116 : indexedRowCheck 116 = true := Eq.refl true
private theorem t117 : indexedRowCheck 117 = true := Eq.refl true
private theorem t118 : indexedRowCheck 118 = true := Eq.refl true
private theorem t119 : indexedRowCheck 119 = true := Eq.refl true
private theorem t120 : indexedRowCheck 120 = true := Eq.refl true
private theorem t121 : indexedRowCheck 121 = true := Eq.refl true
private theorem t122 : indexedRowCheck 122 = true := Eq.refl true
private theorem t123 : indexedRowCheck 123 = true := Eq.refl true
private theorem t124 : indexedRowCheck 124 = true := Eq.refl true
private theorem t125 : indexedRowCheck 125 = true := Eq.refl true
private theorem t126 : indexedRowCheck 126 = true := Eq.refl true
private theorem t127 : indexedRowCheck 127 = true := Eq.refl true
private theorem t128 : indexedRowCheck 128 = true := Eq.refl true
private theorem t129 : indexedRowCheck 129 = true := Eq.refl true
private theorem tAll : Rows indexedRowCheck 0 130 :=
  rowsCons t0 <| rowsCons t1 <| rowsCons t2 <| rowsCons t3 <| rowsCons t4 <|
  rowsCons t5 <| rowsCons t6 <| rowsCons t7 <| rowsCons t8 <| rowsCons t9 <|
  rowsCons t10 <| rowsCons t11 <| rowsCons t12 <| rowsCons t13 <| rowsCons t14 <|
  rowsCons t15 <| rowsCons t16 <| rowsCons t17 <| rowsCons t18 <| rowsCons t19 <|
  rowsCons t20 <| rowsCons t21 <| rowsCons t22 <| rowsCons t23 <| rowsCons t24 <|
  rowsCons t25 <| rowsCons t26 <| rowsCons t27 <| rowsCons t28 <| rowsCons t29 <|
  rowsCons t30 <| rowsCons t31 <| rowsCons t32 <| rowsCons t33 <| rowsCons t34 <|
  rowsCons t35 <| rowsCons t36 <| rowsCons t37 <| rowsCons t38 <| rowsCons t39 <|
  rowsCons t40 <| rowsCons t41 <| rowsCons t42 <| rowsCons t43 <| rowsCons t44 <|
  rowsCons t45 <| rowsCons t46 <| rowsCons t47 <| rowsCons t48 <| rowsCons t49 <|
  rowsCons t50 <| rowsCons t51 <| rowsCons t52 <| rowsCons t53 <| rowsCons t54 <|
  rowsCons t55 <| rowsCons t56 <| rowsCons t57 <| rowsCons t58 <| rowsCons t59 <|
  rowsCons t60 <| rowsCons t61 <| rowsCons t62 <| rowsCons t63 <| rowsCons t64 <|
  rowsCons t65 <| rowsCons t66 <| rowsCons t67 <| rowsCons t68 <| rowsCons t69 <|
  rowsCons t70 <| rowsCons t71 <| rowsCons t72 <| rowsCons t73 <| rowsCons t74 <|
  rowsCons t75 <| rowsCons t76 <| rowsCons t77 <| rowsCons t78 <| rowsCons t79 <|
  rowsCons t80 <| rowsCons t81 <| rowsCons t82 <| rowsCons t83 <| rowsCons t84 <|
  rowsCons t85 <| rowsCons t86 <| rowsCons t87 <| rowsCons t88 <| rowsCons t89 <|
  rowsCons t90 <| rowsCons t91 <| rowsCons t92 <| rowsCons t93 <| rowsCons t94 <|
  rowsCons t95 <| rowsCons t96 <| rowsCons t97 <| rowsCons t98 <| rowsCons t99 <|
  rowsCons t100 <| rowsCons t101 <| rowsCons t102 <| rowsCons t103 <| rowsCons t104 <|
  rowsCons t105 <| rowsCons t106 <| rowsCons t107 <| rowsCons t108 <| rowsCons t109 <|
  rowsCons t110 <| rowsCons t111 <| rowsCons t112 <| rowsCons t113 <| rowsCons t114 <|
  rowsCons t115 <| rowsCons t116 <| rowsCons t117 <| rowsCons t118 <| rowsCons t119 <|
  rowsCons t120 <| rowsCons t121 <| rowsCons t122 <| rowsCons t123 <| rowsCons t124 <|
  rowsCons t125 <| rowsCons t126 <| rowsCons t127 <| rowsCons t128 <| rowsCons t129 <| rowsEnd indexedRowCheck 130
private theorem bound : indexedWeightBoundCheck = true := Eq.refl true
private theorem tc : indexedConstantCheck = true := Eq.refl true
private theorem cz : (highSurplus highTriangles).constant = 0 := Eq.refl (0:ℤ)

theorem g24_high_box (y : ℕ → ℝ) (hy : ∀ i < 130, 0 ≤ y i ∧ y i ≤ 1)
    (hm0 : (3/10 : ℝ) ≤ OMA.Erdos1186Region2.g24Mass y)
    (hm1 : OMA.Erdos1186Region2.g24Mass y ≤ (2/5 : ℝ)) :
    0 ≤ OMA.Erdos1186Region2.g24Objective y :=
  high_box (fun i hi => dAll i (Nat.zero_le _) hi)
    (fun i hi => tAll i (Nat.zero_le _) hi) bound tc cz y hy hm0 hm1

end

end OMA.Erdos1186High

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1.H3 :=
  OMA.Erdos1186G24NearCut.high_cut_of_box OMA.Erdos1186High.g24_high_box
