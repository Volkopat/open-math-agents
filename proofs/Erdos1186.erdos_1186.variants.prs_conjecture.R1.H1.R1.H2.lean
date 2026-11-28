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

end OMA.Erdos1186G24NearCut
end

/-
Adapted exact middle-interval certificate from Chandler Snively v1.0.0, commit
0b0155ead09841892690b9f9c469d1ff0edaff4c. The argument is due to Carlos Toledo.
The Lean adaptations are Apache-2.0, Copyright 2026 Chandler Snively.
Packed certificate data by Chandler Snively are reused under CC BY 4.0. The first-slab
transfer and sparse decoder are adapted from justusklocke-cloud, PR 31250.
-/
namespace OMA.Erdos1186Low

/-- Sorted stored column entries. A field contains a column byte and an unsigned value. -/
structure SparseRow where
  length : Nat
  width : Nat
  word : Nat

def digit (word width index : Nat) : Nat :=
  (word >>> (width*index)) &&& ((1 <<< width)-1)

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


end OMA.Erdos1186Low

namespace Erdos1186Ex
open Finset OMA.Erdos1186Region2
structure Grid where
  N : ℕ
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  ai : ℕ → ℚ
  bi : ℕ → ℚ
  sgn : ℕ → ℤ
  A4 : ℕ → ℕ → ℕ
def Grid.len (G : Grid) (i : ℕ) : ℕ := G.hi i - G.lo i
def Grid.wt (G : Grid) (i : ℕ) : ℚ := (G.len i : ℚ) / 1096
noncomputable def Grid.pterm (G : Grid) (i j : ℕ) (yi yj : ℝ) : ℝ :=
  let P : ℝ := (G.wt i : ℝ) * G.wt j * yi * yj
  let Ain : ℝ := (G.A4 i j : ℝ) / (4 * 1096 ^ 2)
  let Aout : ℝ := (G.wt i : ℝ) * G.wt j - Ain
  if G.sgn i * G.sgn j = 1 then max 0 (P - Aout) else max (-Ain) (-P)
noncomputable def Grid.Lval (G : Grid) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range G.N, ((G.ai i : ℝ) * y i + (G.bi i : ℝ) * y i ^ 2)
    + ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.pterm i j (y i) (y j)
noncomputable def Grid.mval (G : Grid) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range G.N, (G.wt i : ℝ) * y i
def RegionLB (G : Grid) (lo hi : ℚ) : Prop :=
  ∀ y : ℕ → ℝ, (∀ i < G.N, 0 ≤ y i ∧ y i ≤ 1) → (lo : ℝ) ≤ G.mval y →
    G.mval y ≤ hi → 0 ≤ G.Lval y
def G24 : Grid where
  N := 130
  lo := g24Endpoint
  hi := fun i => g24Endpoint (i+1)
  ai := fun i => (digit g24AlphaWord 9 (min i (129-i)) : ℚ) / 300304
  bi := fun i => (digit g24BetaWord 9 (min i (129-i)) : ℚ) / 1801824
  sgn := fun i => if g24Sign i then 1 else -1
  A4 := g24Area4
end Erdos1186Ex

namespace Erdos1186Night2

open Finset
def dotL : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

theorem dotL_comm : ∀ a b : List ℤ, dotL a b = dotL b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      simp only [dotL]
      rw [dotL_comm as bs, mul_comm]

theorem dotL_eq_sum : ∀ (a b : List ℤ) (n : ℕ), a.length ≤ n →
    dotL a b = ∑ k ∈ range n, a.getD k 0 * b.getD k 0
  | [], b, n, _ => by
      cases b <;> simp [dotL]
  | x :: as, b, n, h => by
      cases n with
      | zero => simp at h
      | succ m =>
        cases b with
        | nil => simp [dotL]
        | cons y bs =>
          have ih := dotL_eq_sum as bs m (by simpa using h)
          rw [Finset.sum_range_succ']
          simp [dotL, ih]
          ring
theorem psd_of_dom (L : ℕ) (E : ℕ → ℕ → ℝ) (hsym : ∀ i j, E i j = E j i)
    (hdom : ∀ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| ≤ 2 * E i i) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, E i j * x i * x j := by
  have key : ∀ i j, 0 ≤ E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
      ring_nf
      exact le_refl _
    · simp only [h, if_false, sub_zero]
      rcases abs_cases (E i j) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
        nlinarith [sq_nonneg (x i + x j), abs_nonneg (E i j)]
      · rw [h1]
        have := abs_nonneg (E i j)
        rw [h1] at this
        nlinarith [sq_nonneg (x i - x j)]
  have h1 : 0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => key i j

  have hA : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| / 2 * x i ^ 2 =
      ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_div]
  have hB : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| / 2 * x j ^ 2 =
      ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_div]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym]
  have hC : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) =
      ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_ite_eq]
    simp [hi]
  have hsplit : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)) =
      (∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, E i j * x i * x j)
      + (∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2) * 2
      - ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 := by
    have e1 : ∀ i j, E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
        - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)
        = E i j * x i * x j + (|E i j| / 2 * x i ^ 2 + |E i j| / 2 * x j ^ 2)
          - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) := fun i j => by ring
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC]
    ring
  rw [hsplit] at h1
  have h2 : ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 ≤
      ∑ i ∈ Icc 1 L, E i i * x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have := hdom i hi
    have hx := sq_nonneg (x i)
    nlinarith
  have h3 : 0 ≤ ∑ i ∈ Icc 1 L, (|E i i| - E i i) * x i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [le_abs_self (E i i)]) (sq_nonneg _)
  have h4 : ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 =
      ∑ i ∈ Icc 1 L, E i i * x i ^ 2 + ∑ i ∈ Icc 1 L, |E i i| * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h5 : ∑ i ∈ Icc 1 L, (|E i i| - E i i) * x i ^ 2 =
      ∑ i ∈ Icc 1 L, |E i i| * x i ^ 2 - ∑ i ∈ Icc 1 L, E i i * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

theorem gram_nonneg (L n : ℕ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range n, c i k * c j k) * x i * x j := by
  have e : ∀ i j, (∑ k ∈ range n, c i k * c j k) * x i * x j =
      ∑ k ∈ range n, (c i k * x i) * (c j k * x j) := by
    intro i j
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range n, c i k * c j k) * x i * x j =
      ∑ k ∈ range n, (∑ i ∈ Icc 1 L, c i k * x i) ^ 2 := by
    simp only [e, sq, Finset.sum_mul_sum]
    calc _ = ∑ i ∈ Icc 1 L, ∑ k ∈ range n, ∑ j ∈ Icc 1 L, (c i k * x i) * (c j k * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [this]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

end Erdos1186Night2
namespace Erdos1186Ex

open Finset Erdos1186Night2

/- ### Packed integer tables -/

/-- Signed digit `j` of the packed natural number `r` in base `2^W` (digit minus `2^(W-1)`). -/
def dec (W r j : ℕ) : ℤ := (((r / 2 ^ (W * j)) % 2 ^ W : ℕ) : ℤ) - ((2 ^ (W - 1) : ℕ) : ℤ)

/-- Entry `(i, j)` of a table given as a list of packed rows. -/
def tb (W : ℕ) (rows : List ℕ) (i j : ℕ) : ℤ := dec W (rows.getD i 0) j

/-- Entry `i` of a packed vector. -/
def vc (W : ℕ) (v : ℕ) (i : ℕ) : ℤ := dec W v i

/- ### Elementary sum lemmas -/

theorem sum_Icc_one {β : Type*} [AddCommMonoid β] (L : ℕ) (f : ℕ → β) :
    ∑ a ∈ Icc 1 L, f a = ∑ t ∈ range L, f (1 + t) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]

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

/-- sum over `Icc 1 (n+1)` = first term + the rest shifted by two. -/
theorem sum_Icc_split {β : Type*} [AddCommMonoid β] (n : ℕ) (F : ℕ → β) :
    ∑ a ∈ Icc 1 (n + 1), F a = F 1 + ∑ i ∈ range n, F (i + 2) := by
  rw [sum_Icc_one, Finset.sum_range_succ', add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + (i + 1) = i + 2 by omega]

/-- Gram expansion: indices `1` (the constant) and `i + 2` (the variable `y i`). -/
theorem gram_ev (n : ℕ) (M : ℕ → ℕ → ℤ) (x y : ℕ → ℝ) (h1 : x 1 = 1) (h2 : ∀ i, x (i + 2) = y i) :
    ∑ a ∈ Icc 1 (n + 1), ∑ b ∈ Icc 1 (n + 1), (M a b : ℝ) * x a * x b =
      evq n (M 1 1) (fun i => M 1 (i + 2) + M (i + 2) 1) (fun i j => M (i + 2) (j + 2)) y := by
  have hs : ∀ a : ℕ, ∑ b ∈ Icc 1 (n + 1), (M a b : ℝ) * x a * x b
      = (M a 1 : ℝ) * x a * x 1 + ∑ j ∈ range n, (M a (j + 2) : ℝ) * x a * x (j + 2) :=
    fun a => sum_Icc_split n (fun b => (M a b : ℝ) * x a * x b)
  simp only [hs]
  rw [sum_Icc_split n (fun a => (M a 1 : ℝ) * x a * x 1 + ∑ j ∈ range n, (M a (j + 2) : ℝ) * x a * x (j + 2))]
  simp only [h1, h2]
  unfold evq
  push_cast
  simp only [Finset.sum_add_distrib, add_mul, mul_one, mul_assoc]
  ring

/- ### The exact pair counts -/

def Qn : ℤ := 1099511627776
def Dz : ℤ := Qn * 360364800

def A4v (G : Grid) (i j : ℕ) : ℕ := G.A4 i j
theorem A4v_eq (G : Grid) (i j : ℕ) : A4v G i j = G.A4 i j := rfl

def sgnP (G : Grid) (i j : ℕ) : ℤ := if G.sgn i * G.sgn j = 1 then 1 else -1

/-- integer coefficient of `y_i y_j`:  `300 (Q - θ) len_i len_j`. -/
def Kp (G : Grid) (θ : ℤ) (i j : ℕ) : ℤ := 300 * (Qn - θ) * (G.len i : ℤ) * (G.len j : ℤ)

/-- integer constant of the pair bound. -/
def cp (G : Grid) (θ : ℤ) (i j : ℕ) : ℤ :=
  if G.sgn i * G.sgn j = 1 then 75 * (Qn - θ) * (4 * (G.len i : ℤ) * (G.len j : ℤ) - (A4v G i j : ℤ))
  else 75 * θ * (A4v G i j : ℤ)

theorem pterm_scaled (G : Grid) (i j : ℕ) (θ : ℤ) (h0 : 0 ≤ θ) (h1 : θ ≤ Qn) (yi yj : ℝ) :
    ((sgnP G i j * Kp G θ i j : ℤ) : ℝ) * (yi * yj) - (cp G θ i j : ℝ)
      ≤ (Dz : ℝ) * G.pterm i j yi yj := by
  have hA := A4v_eq G i j
  unfold Grid.pterm sgnP Kp cp Grid.wt
  rw [hA]
  simp only [Qn, Dz] at *
  have hθ0 : (0 : ℝ) ≤ (θ : ℝ) := by exact_mod_cast h0
  have hθ1 : (θ : ℝ) ≤ 1099511627776 := by exact_mod_cast h1
  push_cast
  set a : ℝ := (G.len i : ℝ) with ha
  set b : ℝ := (G.len j : ℝ) with hb
  set A : ℝ := (G.A4 i j : ℝ) with hAd
  by_cases hs : G.sgn i * G.sgn j = 1
  · simp only [hs, if_true]
    set u : ℝ := a / 1096 * (b / 1096) * yi * yj - (a / 1096 * (b / 1096) - A / (4 * 1096 ^ 2)) with hu
    have hm1 : u ≤ max 0 u := le_max_right _ _
    have hm2 : 0 ≤ max 0 u := le_max_left _ _
    have key : (1099511627776 * 360364800 : ℝ) * ((1 - (θ : ℝ) / 1099511627776) * u)
        = 1 * (300 * (1099511627776 - (θ : ℝ)) * a * b) * (yi * yj)
          - 75 * (1099511627776 - (θ : ℝ)) * (4 * a * b - A) := by
      rw [hu]
      field_simp
      ring
    have hq : 0 ≤ 1 - (θ : ℝ) / 1099511627776 := by
      rw [sub_nonneg, div_le_one (by norm_num)]; exact hθ1
    have ht : 0 ≤ (θ : ℝ) / 1099511627776 := by positivity
    have hle : (1 - (θ : ℝ) / 1099511627776) * u ≤ max 0 u := by
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hm1), mul_nonneg ht hm2]
    have hD : (0 : ℝ) ≤ 1099511627776 * 360364800 := by norm_num
    have hh := mul_le_mul_of_nonneg_left hle hD
    rw [← key]
    linarith
  · simp only [hs, if_false]
    set P : ℝ := a / 1096 * (b / 1096) * yi * yj with hP
    set Ain : ℝ := A / (4 * 1096 ^ 2) with hAin
    have hm1 : -Ain ≤ max (-Ain) (-P) := le_max_left _ _
    have hm2 : -P ≤ max (-Ain) (-P) := le_max_right _ _
    have key : (1099511627776 * 360364800 : ℝ) * ((θ : ℝ) / 1099511627776 * (-Ain)
          + (1 - (θ : ℝ) / 1099511627776) * (-P))
        = (-1 * (300 * (1099511627776 - (θ : ℝ)) * a * b)) * (yi * yj) - 75 * (θ : ℝ) * A := by
      rw [hP, hAin]
      field_simp
      ring
    have hq : 0 ≤ 1 - (θ : ℝ) / 1099511627776 := by
      rw [sub_nonneg, div_le_one (by norm_num)]; exact hθ1
    have ht : 0 ≤ (θ : ℝ) / 1099511627776 := by positivity
    have hle : (θ : ℝ) / 1099511627776 * (-Ain) + (1 - (θ : ℝ) / 1099511627776) * (-P)
        ≤ max (-Ain) (-P) := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hm1), mul_nonneg hq (sub_nonneg.mpr hm2)]
    have hD : (0 : ℝ) ≤ 1099511627776 * 360364800 := by norm_num
    have hh := mul_le_mul_of_nonneg_left hle hD
    rw [← key]
    linarith

end Erdos1186Ex

namespace Erdos1186Ex

open Finset Erdos1186Night2

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

/- ### The pair side -/

/-- The data of the pair part: integer accessors of the grid and the table `θ` (numerators over `Qn`). -/
structure PD where
  G : Grid
  lenz : ℕ → ℤ
  sgz : ℕ → ℤ
  alz : ℕ → ℤ
  btz : ℕ → ℤ
  a4z : ℕ → ℕ → ℤ
  th : ℕ → ℕ → ℤ

namespace PD

def sz (d : PD) (i j : ℕ) : ℤ := if d.sgz i * d.sgz j = 1 then 1 else -1

def Kz (d : PD) (i j : ℕ) : ℤ := 300 * (Qn - d.th i j) * d.lenz i * d.lenz j

def cz (d : PD) (i j : ℕ) : ℤ :=
  if d.sgz i * d.sgz j = 1 then 75 * (Qn - d.th i j) * (4 * d.lenz i * d.lenz j - d.a4z i j)
  else 75 * d.th i j * d.a4z i j

/-- the integer-coefficient lower bound of `Dz · Lval`. -/
noncomputable def PS (d : PD) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range d.G.N, ((d.alz i : ℝ) * y i + (d.btz i : ℝ) * y i ^ 2)
    + ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j) - (d.cz i j : ℝ))

/-- the accessors agree with the grid; `θ ∈ [0, Qn]`. -/
structure Ok (d : PD) : Prop where
  len : ∀ i < d.G.N, d.lenz i = (d.G.len i : ℤ)
  sg : ∀ i < d.G.N, d.sgz i = d.G.sgn i
  al : ∀ i < d.G.N, d.G.ai i * (Dz : ℚ) = (d.alz i : ℚ)
  bt : ∀ i < d.G.N, d.G.bi i * (Dz : ℚ) = (d.btz i : ℚ)
  a4 : ∀ i < d.G.N, ∀ j < d.G.N, d.a4z i j = (d.G.A4 i j : ℤ)
  th : ∀ i < d.G.N, ∀ j < d.G.N, 0 ≤ d.th i j ∧ d.th i j ≤ Qn

theorem PS_le (d : PD) (h : d.Ok) (y : ℕ → ℝ) : d.PS y ≤ (Dz : ℝ) * d.G.Lval y := by
  unfold PS Grid.Lval
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  apply add_le_add
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have ha : (d.G.ai i : ℝ) * (Dz : ℝ) = (d.alz i : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (h.al i hi')
      simpa using this
    have hb : (d.G.bi i : ℝ) * (Dz : ℝ) = (d.btz i : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (h.bt i hi')
      simpa using this
    rw [← ha, ← hb]
    ring
  · apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have key := pterm_scaled d.G i j (d.th i j) (h.th i hi' j hj').1 (h.th i hi' j hj').2 (y i) (y j)
    have e1 : sgnP d.G i j * Kp d.G (d.th i j) i j = d.sz i j * d.Kz i j := by
      unfold sgnP Kp sz Kz
      rw [h.len i hi', h.len j hj', h.sg i hi', h.sg j hj']
    have e2 : cp d.G (d.th i j) i j = d.cz i j := by
      unfold cp cz
      rw [A4v_eq, h.len i hi', h.len j hj', h.sg i hi', h.sg j hj', h.a4 i hi' j hj']
    rw [e1, e2] at key
    exact key

/-- the integer coefficients of `U · PS`. -/
def cP (d : PD) : ℤ := -Uu * ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, d.cz i j
def lP (d : PD) (a : ℕ) : ℤ := Uu * d.alz a
def qP (d : PD) (i j : ℕ) : ℤ := Uu * (d.sz i j * d.Kz i j + if i = j then d.btz i else 0)

theorem PS_evq (d : PD) (y : ℕ → ℝ) : (Uu : ℝ) * d.PS y = evq d.G.N d.cP d.lP d.qP y := by
  have e : d.PS y = evq d.G.N (-∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, d.cz i j) d.alz
      (fun i j => d.sz i j * d.Kz i j + if i = j then d.btz i else 0) y := by
    unfold PS evq
    have hb : ∀ i ∈ range d.G.N, (d.btz i : ℝ) * y i ^ 2
        = ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) := by
      intro i hi
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [sq]
      · intro j _ hji
        simp [Ne.symm hji]
    have hb' : ∑ i ∈ range d.G.N, (d.btz i : ℝ) * y i ^ 2
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) :=
      Finset.sum_congr rfl hb
    have hc : ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j) - (d.cz i j : ℝ))
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j))
          - ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (d.cz i j : ℝ) := by
      simp only [Finset.sum_sub_distrib]
    rw [hc, Finset.sum_add_distrib, hb']
    have hq : ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j + if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j)
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j))
          + ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hq]
    push_cast
    ring
  rw [e, evq_smul]
  apply evq_congr
  · unfold cP
    ring
  · intro i _
    rfl
  · intro i _ j _
    rfl

end PD

theorem evq_sub3 (n : ℕ) (c c' c'' : ℤ) (l l' l'' : ℕ → ℤ) (q q' q'' : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (c - c' - c'') (fun i => l i - l' i - l'' i) (fun i j => q i j - q' i j - q'' i j) y
      = evq n c l q y - evq n c' l' q' y - evq n c'' l'' q'' y := by
  unfold evq
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- The abstract certificate theorem: from the integer data to `RegionLB`. -/
theorem region_of_data (pd : PD) (fd : FD) (loN hiN : ℤ)
    (hok : pd.Ok) (hfn : fd.Nonneg) (hn : fd.n = pd.G.N)
    (hom : ∀ i < pd.G.N, fd.om i = 20 * pd.lenz i) (hLo : fd.Lo = 1096 * loN) (hHi : fd.Hi = 1096 * hiN)
    (cT : ℤ) (lT : ℕ → ℤ) (qT : ℕ → ℕ → ℤ)
    (hT : ∀ y : ℕ → ℝ, (∀ i < pd.G.N, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq pd.G.N cT lT qT y)
    (Nm : ℕ → ℕ → ℤ)
    (hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Icc 1 (pd.G.N + 1), ∑ b ∈ Icc 1 (pd.G.N + 1), (Nm a b : ℝ) * x a * x b)
    (h00 : Uu * Nm 1 1 = pd.cP - fd.cF - cT)
    (h0i : ∀ i < pd.G.N, 2 * Uu * Nm 1 (i + 2) = pd.lP i - fd.lF i - lT i)
    (hi0 : ∀ i < pd.G.N, 2 * Uu * Nm (i + 2) 1 = pd.lP i - fd.lF i - lT i)
    (hij : ∀ i < pd.G.N, ∀ j < pd.G.N, 2 * Uu * Nm (i + 2) (j + 2)
      = (pd.qP i j - fd.qF i j - qT i j) + (pd.qP j i - fd.qF j i - qT j i)) :
    RegionLB pd.G ((loN : ℚ) / 20) ((hiN : ℚ) / 20) := by
  intro y hy hlo hhi
  have hy' : ∀ i < fd.n, 0 ≤ y i ∧ y i ≤ 1 := by
    rw [hn]; exact hy
  -- R m
  have hRm : (Rr : ℝ) * pd.G.mval y = ∑ k ∈ range fd.n, (fd.om k : ℝ) * y k := by
    unfold Grid.mval
    rw [Finset.mul_sum, hn]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hom k hk', hok.len k hk']
    unfold Grid.wt Rr
    push_cast
    ring
  have hRlo : (Rr : ℝ) * (((loN : ℚ) / 20 : ℚ) : ℝ) = fd.Lo := by
    rw [hLo]; unfold Rr; push_cast; ring
  have hRhi : (Rr : ℝ) * (((hiN : ℚ) / 20 : ℚ) : ℝ) = fd.Hi := by
    rw [hHi]; unfold Rr; push_cast; ring
  have hFS := fd.FSr_nonneg hfn (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y hy' hlo hhi
  have hFSe := FD.FSr_evq fd (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y hRm hRlo hRhi
  have hFSe' : (Uu : ℝ) * fd.FSr (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y
      = evq pd.G.N fd.cF fd.lF fd.qF y := by
    rw [← hn]; exact hFSe
  have hPS := PD.PS_evq pd y
  have hPSle := PD.PS_le pd hok y
  have hTy := hT y hy
  -- the matrix
  set x : ℕ → ℝ := fun a => if a = 1 then 1 else y (a - 2) with hx
  have hx1 : x 1 = 1 := by simp [hx]
  have hx2 : ∀ i, x (i + 2) = y i := by
    intro i
    simp [hx]
  have hg := gram_ev pd.G.N Nm x y hx1 hx2
  have hpos := hpsd x
  rw [hg] at hpos
  have hmat : (Uu : ℝ) * evq pd.G.N (Nm 1 1) (fun i => Nm 1 (i + 2) + Nm (i + 2) 1) (fun i j => Nm (i + 2) (j + 2)) y
      = evq pd.G.N (pd.cP - fd.cF - cT) (fun i => pd.lP i - fd.lF i - lT i)
          (fun i j => pd.qP i j - fd.qF i j - qT i j) y := by
    rw [evq_smul]
    apply evq_congr
    · exact h00
    · intro i hi
      have a := h0i i hi
      have b := hi0 i hi
      linarith
    · intro i hi j hj
      have a := hij i hi j hj
      have b := hij j hj i hi
      linarith
  rw [evq_sub3, ← hPS, ← hFSe'] at hmat
  have hU : (0 : ℝ) < Uu := by norm_num [Uu]
  have hD : (0 : ℝ) < Dz := by norm_num [Dz, Qn]
  have hprod : 0 ≤ (Uu : ℝ) * evq pd.G.N (Nm 1 1) (fun i => Nm 1 (i + 2) + Nm (i + 2) 1)
      (fun i j => Nm (i + 2) (j + 2)) y := mul_nonneg hU.le hpos
  have h1 : 0 ≤ (Uu : ℝ) * pd.PS y := by
    have := mul_nonneg hU.le hFS
    linarith
  have h2 : 0 ≤ pd.PS y := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hU hneg
    linarith
  have h3 : 0 ≤ (Dz : ℝ) * pd.G.Lval y := le_trans h2 hPSle
  exact (mul_nonneg_iff_of_pos_left hD).mp h3

end Erdos1186Ex

namespace Erdos1186Ex

open Finset Erdos1186Night2

/- ### The tables of one region -/

structure Tabs where
  n : ℕ
  loN : ℤ
  hiN : ℤ
  Zn : ℤ
  ppn : ℤ
  rrn : ℤ
  ssn : ℤ
  Wg : ℕ
  vlo : ℕ
  vhi : ℕ
  vlen : ℕ
  vsg : ℕ
  Wa : ℕ
  vAl : ℕ
  vBt : ℕ
  Wf : ℕ
  vYv : ℕ
  vOv : ℕ
  vA1 : ℕ
  vA2 : ℕ
  vA3 : ℕ
  vA4 : ℕ
  YYT : ℕ → ℕ → ℤ
  OOT : ℕ → ℕ → ℤ
  YOT : ℕ → ℕ → ℤ
  Wt : ℕ
  thT : ℕ → ℕ → ℤ
  Wn : ℕ
  NT : ℕ → ℕ → ℤ
  crows : List (List ℤ)
  czr : List ℤ

def mkPD (T : Tabs) (G : Grid) : PD where
  G := G
  lenz := vc T.Wg T.vlen
  sgz := vc T.Wg T.vsg
  alz := vc T.Wa T.vAl
  btz := vc T.Wa T.vBt
  a4z := fun i j => G.A4 i j
  th := T.thT

def mkFD (T : Tabs) : FD where
  n := T.n
  Yv := fun i => T.Zn * vc T.Wf T.vYv i
  Ov := fun i => T.Zn * vc T.Wf T.vOv i
  A1 := fun i => T.Zn * vc T.Wf T.vA1 i
  A2 := fun i => T.Zn * vc T.Wf T.vA2 i
  A3 := fun i => T.Zn * vc T.Wf T.vA3 i
  A4 := fun i => T.Zn * vc T.Wf T.vA4 i
  YY := fun i j => T.Zn * T.YYT i j
  OO := fun i j => T.Zn * T.OOT i j
  YO := fun i j => T.Zn * T.YOT i j
  pp := T.Zn * T.ppn
  rr := T.Zn * T.rrn
  ss := T.Zn * T.ssn
  om := fun i => 20 * vc T.Wg T.vlen i
  Lo := 1096 * T.loN
  Hi := 1096 * T.hiN

/-- the matrix of the certificate, indices `1 .. n+1` (index `1` is the constant). -/
def Nmat (T : Tabs) (a b : ℕ) : ℤ := T.NT (a - 1) (b - 1)

/- ### Bool checks -/

/-- grid vectors agree with the grid; `α, β` are the integers `a_i Dz`, `b_i Dz`. -/
def gridChk (T : Tabs) (G : Grid) (i : ℕ) : Bool :=
  decide (vc T.Wg T.vlo i = (G.lo i : ℤ) ∧ vc T.Wg T.vhi i = (G.hi i : ℤ) ∧ vc T.Wg T.vlen i = (G.len i : ℤ) ∧
    vc T.Wg T.vsg i = G.sgn i ∧ G.ai i * (Dz : ℚ) = ((vc T.Wa T.vAl i : ℤ) : ℚ) ∧
    G.bi i * (Dz : ℚ) = ((vc T.Wa T.vBt i : ℤ) : ℚ))

/-- the multiplier vectors are `≥ 0`. -/
def vecChk (T : Tabs) (i : ℕ) : Bool :=
  decide (0 ≤ vc T.Wf T.vYv i ∧ 0 ≤ vc T.Wf T.vOv i ∧ 0 ≤ vc T.Wf T.vA1 i ∧ 0 ≤ vc T.Wf T.vA2 i ∧
    0 ≤ vc T.Wf T.vA3 i ∧ 0 ≤ vc T.Wf T.vA4 i)

def scalChk (T : Tabs) : Bool := decide (0 ≤ T.ppn ∧ 0 ≤ T.rrn ∧ 0 ≤ T.ssn ∧ 0 < T.Zn)

/-- the extra (triangle) term of the matrix identity. -/
structure Tri where
  cT : ℤ
  lT : ℕ → ℤ
  qT : ℕ → ℕ → ℤ

def Tri.zero : Tri := ⟨0, fun _ => 0, fun _ _ => 0⟩

/-- pair entry `(i, j)`: ranges of `θ` and the form multipliers, and the identity for `2U N_{ij}`. -/
def pairChk (T : Tabs) (G : Grid) (tr : Tri) (i j : ℕ) : Bool :=
  decide ((0 ≤ T.thT i j ∧ T.thT i j ≤ Qn) ∧ 0 ≤ T.YYT i j ∧ 0 ≤ T.OOT i j ∧
    0 ≤ T.YOT i j ∧
    2 * Uu * Nmat T (i + 2) (j + 2) =
      ((mkPD T G).qP i j - (mkFD T).qF i j - tr.qT i j) + ((mkPD T G).qP j i - (mkFD T).qF j i - tr.qT j i))

/-- constant and linear entries. -/
def linChk (T : Tabs) (G : Grid) (tr : Tri) (i : ℕ) : Bool :=
  decide (2 * Uu * Nmat T 1 (i + 2) = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i ∧
    2 * Uu * Nmat T (i + 2) 1 = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i)

/-- row sums of the constant coefficients `cz` (claimed in the tables, checked row by row). -/
def czRowChk (T : Tabs) (G : Grid) (i : ℕ) : Bool :=
  decide ((∑ j ∈ range G.N, (mkPD T G).cz i j) = T.czr.getD i 0)

def constChk (T : Tabs) (G : Grid) (tr : Tri) : Bool :=
  decide (Uu * Nmat T 1 1 = -Uu * (∑ i ∈ range G.N, T.czr.getD i 0) - (mkFD T).cF - tr.cT)

/- ### Diagonal dominance of `N - C Cᵀ` -/

def absSumRow (nr : ℕ → ℤ) (ri : List ℤ) : ℕ → List (List ℤ) → ℕ
  | _, [] => 0
  | j, rj :: rest => (nr j - dotL ri rj).natAbs + absSumRow nr ri (j + 1) rest

def domRow (T : Tabs) (a : ℕ) : Bool :=
  decide (((absSumRow (T.NT a) (T.crows.getD a []) 0 T.crows : ℕ) : ℤ)
    ≤ 2 * (T.NT a a - dotL (T.crows.getD a []) (T.crows.getD a [])))

def lenChk (T : Tabs) : Bool :=
  decide (T.crows.length = T.n + 1) && T.crows.all (fun r => decide (r.length ≤ T.n + 1))

theorem absSumRow_eq (nr : ℕ → ℤ) (ri : List ℤ) :
    ∀ (rows : List (List ℤ)) (j0 : ℕ),
      ((absSumRow nr ri j0 rows : ℕ) : ℤ) =
        ∑ t ∈ range rows.length, |nr (j0 + t) - dotL ri (rows.getD t [])|
  | [], j0 => by simp [absSumRow]
  | rj :: rest, j0 => by
      have ih := absSumRow_eq nr ri rest (j0 + 1)
      have hsum : ∑ t ∈ range rest.length, |nr (j0 + 1 + t) - dotL ri (rest.getD t [])| =
          ∑ t ∈ range rest.length, |nr (j0 + (t + 1)) - dotL ri (rest.getD t [])| := by
        apply Finset.sum_congr rfl
        intro t _
        rw [show j0 + 1 + t = j0 + (t + 1) by omega]
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [absSumRow, List.getD_cons_succ, List.getD_cons_zero, add_zero]
      push_cast
      rw [ih, hsum, add_comm]

theorem domRow_sound (T : Tabs) (hrows : T.crows.length = T.n + 1) (a : ℕ) (h : domRow T a = true) :
    ∑ b ∈ Icc 1 (T.n + 1), |Nmat T (a + 1) b - dotL (T.crows.getD a []) (T.crows.getD (b - 1) [])|
      ≤ 2 * (Nmat T (a + 1) (a + 1) - dotL (T.crows.getD a []) (T.crows.getD a [])) := by
  unfold domRow at h
  have h' := of_decide_eq_true h
  rw [absSumRow_eq, hrows] at h'
  have e : ∑ b ∈ Icc 1 (T.n + 1), |Nmat T (a + 1) b - dotL (T.crows.getD a []) (T.crows.getD (b - 1) [])|
      = ∑ t ∈ range (T.n + 1), |T.NT a (0 + t) - dotL (T.crows.getD a []) (T.crows.getD t [])| := by
    rw [sum_Icc_one]
    apply Finset.sum_congr rfl
    intro t _
    unfold Nmat
    simp
  rw [e]
  unfold Nmat
  simpa using h'

/- ### Positive semidefiniteness from the dominance rows -/

theorem psd_of_rows (L : ℕ) (Nm : ℕ → ℕ → ℤ) (crow : ℕ → List ℤ)
    (hlen : ∀ i ∈ Icc 1 L, (crow i).length ≤ L)
    (hsym : ∀ i ∈ Icc 1 L, ∀ j ∈ Icc 1 L, Nm i j = Nm j i)
    (hdom : ∀ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |Nm i j - dotL (crow i) (crow j)|
      ≤ 2 * (Nm i i - dotL (crow i) (crow i))) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Nm i j : ℝ) * x i * x j := by
  set c : ℕ → ℕ → ℝ := fun i k => (((crow i).getD k 0 : ℤ) : ℝ) with hc
  set Er : ℕ → ℕ → ℝ := fun i j =>
    if i ∈ Icc 1 L ∧ j ∈ Icc 1 L then ((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ) else 0 with hEr
  have hG := gram_nonneg L L c x
  have hEs : ∀ i j, Er i j = Er j i := by
    intro i j
    simp only [hEr]
    by_cases h : i ∈ Icc 1 L ∧ j ∈ Icc 1 L
    · have h' : j ∈ Icc 1 L ∧ i ∈ Icc 1 L := ⟨h.2, h.1⟩
      rw [if_pos h, if_pos h', hsym i h.1 j h.2, dotL_comm (crow i) (crow j)]
    · have h' : ¬ (j ∈ Icc 1 L ∧ i ∈ Icc 1 L) := fun hh => h ⟨hh.2, hh.1⟩
      rw [if_neg h, if_neg h']
  have hE := psd_of_dom L Er hEs
    (fun i hi => by
      have hd := hdom i hi
      have e : ∀ j ∈ Icc 1 L, |Er i j| = |((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ)| := by
        intro j hj
        simp only [hEr]
        rw [if_pos ⟨hi, hj⟩]
      have e2 : Er i i = ((Nm i i - dotL (crow i) (crow i) : ℤ) : ℝ) := by
        simp only [hEr]
        rw [if_pos ⟨hi, hi⟩]
      rw [Finset.sum_congr rfl e, e2]
      have hcast : (∑ j ∈ Icc 1 L, |((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ)|)
          = ((∑ j ∈ Icc 1 L, |Nm i j - dotL (crow i) (crow j)| : ℤ) : ℝ) := by
        push_cast
        rfl
      rw [hcast]
      exact_mod_cast hd) x
  have hsum : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Nm i j : ℝ) * x i * x j =
      (∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range L, c i k * c j k) * x i * x j)
      + ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, Er i j * x i * x j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hd : dotL (crow i) (crow j) = ∑ k ∈ range L, (crow i).getD k 0 * (crow j).getD k 0 :=
      dotL_eq_sum _ _ _ (hlen i hi)
    have e : (Nm i j : ℝ) = (∑ k ∈ range L, c i k * c j k) + Er i j := by
      simp only [hEr, hc]
      rw [if_pos ⟨hi, hj⟩]
      have : (Nm i j : ℤ) = (∑ k ∈ range L, (crow i).getD k 0 * (crow j).getD k 0) + (Nm i j - dotL (crow i) (crow j)) := by
        rw [← hd]; ring
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) this
      simp only [Int.cast_add, Int.cast_sum, Int.cast_mul] at h2
      exact h2
    rw [e]
    ring
  rw [hsum]
  exact add_nonneg hG hE

/- ### From the Bool checks to `RegionLB` -/

theorem gridChk_spec (T : Tabs) (G : Grid) (i : ℕ) (h : gridChk T G i = true) :
    vc T.Wg T.vlo i = (G.lo i : ℤ) ∧ vc T.Wg T.vhi i = (G.hi i : ℤ) ∧ vc T.Wg T.vlen i = (G.len i : ℤ) ∧
    vc T.Wg T.vsg i = G.sgn i ∧ G.ai i * (Dz : ℚ) = ((vc T.Wa T.vAl i : ℤ) : ℚ) ∧
    G.bi i * (Dz : ℚ) = ((vc T.Wa T.vBt i : ℤ) : ℚ) := of_decide_eq_true h

theorem vecChk_spec (T : Tabs) (i : ℕ) (h : vecChk T i = true) :
    0 ≤ vc T.Wf T.vYv i ∧ 0 ≤ vc T.Wf T.vOv i ∧ 0 ≤ vc T.Wf T.vA1 i ∧ 0 ≤ vc T.Wf T.vA2 i ∧
    0 ≤ vc T.Wf T.vA3 i ∧ 0 ≤ vc T.Wf T.vA4 i := of_decide_eq_true h

theorem scalChk_spec (T : Tabs) (h : scalChk T = true) : 0 ≤ T.ppn ∧ 0 ≤ T.rrn ∧ 0 ≤ T.ssn ∧ 0 < T.Zn :=
  of_decide_eq_true h

theorem pairChk_spec (T : Tabs) (G : Grid) (tr : Tri) (i j : ℕ) (h : pairChk T G tr i j = true) :
    (0 ≤ T.thT i j ∧ T.thT i j ≤ Qn) ∧ 0 ≤ T.YYT i j ∧ 0 ≤ T.OOT i j ∧
    0 ≤ T.YOT i j ∧
    2 * Uu * Nmat T (i + 2) (j + 2) =
      ((mkPD T G).qP i j - (mkFD T).qF i j - tr.qT i j) + ((mkPD T G).qP j i - (mkFD T).qF j i - tr.qT j i) :=
  of_decide_eq_true h

theorem linChk_spec (T : Tabs) (G : Grid) (tr : Tri) (i : ℕ) (h : linChk T G tr i = true) :
    2 * Uu * Nmat T 1 (i + 2) = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i ∧
    2 * Uu * Nmat T (i + 2) 1 = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i := of_decide_eq_true h

theorem cP_eq (T : Tabs) (G : Grid) (hcz : ∀ i < G.N, czRowChk T G i = true) :
    (mkPD T G).cP = -Uu * ∑ i ∈ range G.N, T.czr.getD i 0 := by
  unfold PD.cP
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact of_decide_eq_true (hcz i (Finset.mem_range.mp hi))

theorem constChk_spec (T : Tabs) (G : Grid) (tr : Tri) (hcz : ∀ i < G.N, czRowChk T G i = true)
    (h : constChk T G tr = true) :
    Uu * Nmat T 1 1 = (mkPD T G).cP - (mkFD T).cF - tr.cT := by
  rw [cP_eq T G hcz]
  exact of_decide_eq_true h

theorem two_Uu_ne : (2 * Uu : ℤ) ≠ 0 := by unfold Uu; norm_num

theorem Nsym (T : Tabs) (G : Grid) (tr : Tri)
    (hlin : ∀ i < G.N, linChk T G tr i = true)
    (hpair : ∀ i < G.N, ∀ j < G.N, pairChk T G tr i j = true) :
    ∀ a ∈ Icc 1 (G.N + 1), ∀ b ∈ Icc 1 (G.N + 1), Nmat T a b = Nmat T b a := by
  intro a ha b hb
  rw [Finset.mem_Icc] at ha hb
  by_cases h1 : a = 1
  · subst h1
    by_cases h2 : b = 1
    · subst h2; rfl
    · obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
      have hl := linChk_spec T G tr j (hlin j (by omega))
      exact mul_left_cancel₀ two_Uu_ne (hl.1.trans hl.2.symm)
  · obtain ⟨i, rfl⟩ : ∃ i, a = i + 2 := ⟨a - 2, by omega⟩
    by_cases h2 : b = 1
    · subst h2
      have hl := linChk_spec T G tr i (hlin i (by omega))
      exact mul_left_cancel₀ two_Uu_ne (hl.2.trans hl.1.symm)
    · obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
      have e1 := (pairChk_spec T G tr i j (hpair i (by omega) j (by omega))).2.2.2.2
      have e2 := (pairChk_spec T G tr j i (hpair j (by omega) i (by omega))).2.2.2.2
      refine mul_left_cancel₀ two_Uu_ne ?_
      rw [e1, e2]
      ring

theorem lenChk_spec (T : Tabs) (h : lenChk T = true) :
    T.crows.length = T.n + 1 ∧ ∀ r ∈ T.crows, r.length ≤ T.n + 1 := by
  unfold lenChk at h
  rw [Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1, ?_⟩
  intro r hr
  have := List.all_eq_true.mp h.2 r hr
  exact of_decide_eq_true this

theorem region_of_tabs_aux (T : Tabs) (G : Grid) (tr : Tri) (hn : T.n = G.N)
    (hgrid : ∀ i < G.N, gridChk T G i = true)
    (hvec : ∀ i < G.N, vecChk T i = true)
    (hscal : scalChk T = true)
    (hpair : ∀ i < G.N, ∀ j < G.N, pairChk T G tr i j = true)
    (hlin : ∀ i < G.N, linChk T G tr i = true)
    (hcz : ∀ i < G.N, czRowChk T G i = true)
    (hconst : constChk T G tr = true)
    (hlen : lenChk T = true)
    (hdom : ∀ a < G.N + 1, domRow T a = true)
    (hT : ∀ y : ℕ → ℝ, (∀ i < T.n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq T.n tr.cT tr.lT tr.qT y) :
    RegionLB G ((T.loN : ℚ) / 20) ((T.hiN : ℚ) / 20) := by
  have hT' : ∀ y : ℕ → ℝ, (∀ i < G.N, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq G.N tr.cT tr.lT tr.qT y := by
    intro y hy
    rw [← hn]
    rw [← hn] at hy
    exact hT y hy
  obtain ⟨hppn, hrrn, hssn, hZn⟩ := scalChk_spec T hscal
  have hok : (mkPD T G).Ok := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.2.2
    · intro i hi j hj; rfl
    · intro i hi j hj
      exact (pairChk_spec T G tr i j (hpair i hi j hj)).1
  have hfn : (mkFD T).Nonneg := by
    have hz : ∀ x : ℤ, 0 ≤ x → 0 ≤ T.Zn * x := fun x hx => mul_nonneg hZn.le hx
    have hn' : (mkFD T).n = G.N := hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.2.2
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.1
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.2.1
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.2.2.1
    · exact hz _ hppn
    · exact hz _ hrrn
    · exact hz _ hssn
  obtain ⟨hcl, hrl⟩ := lenChk_spec T hlen
  have hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Icc 1 (G.N + 1), ∑ b ∈ Icc 1 (G.N + 1), (Nmat T a b : ℝ) * x a * x b := by
    intro x
    refine psd_of_rows (G.N + 1) (Nmat T) (fun i => T.crows.getD (i - 1) []) ?_ (Nsym T G tr hlin hpair) ?_ x
    · intro i hi
      rw [Finset.mem_Icc] at hi
      have hlt : i - 1 < T.crows.length := by omega
      have hmem : T.crows.getD (i - 1) [] ∈ T.crows := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      show (T.crows.getD (i - 1) []).length ≤ G.N + 1
      rw [← hn]
      exact hrl _ hmem
    · intro i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
      have h := domRow_sound T (by omega) a (hdom a (by omega))
      simp only [Nat.add_sub_cancel]
      rw [hn] at h
      exact h
  exact region_of_data (mkPD T G) (mkFD T) T.loN T.hiN hok hfn hn (fun _ _ => rfl) rfl rfl tr.cT tr.lT tr.qT hT'
    (Nmat T) hpsd (constChk_spec T G tr hcz hconst)
    (fun i hi => (linChk_spec T G tr i (hlin i hi)).1)
    (fun i hi => (linChk_spec T G tr i (hlin i hi)).2)
    (fun i hi j hj => (pairChk_spec T G tr i j (hpair i hi j hj)).2.2.2.2)

/-- The same, with the cell count given as a literal `m` so that the hypotheses never unfold `G.N`. -/
theorem region_of_tabs (T : Tabs) (G : Grid) (tr : Tri) (m : ℕ) (hm : G.N = m) (hn : T.n = m)
    (hgrid : ∀ i < m, gridChk T G i = true)
    (hvec : ∀ i < m, vecChk T i = true)
    (hscal : scalChk T = true)
    (hpair : ∀ i < m, ∀ j < m, pairChk T G tr i j = true)
    (hlin : ∀ i < m, linChk T G tr i = true)
    (hcz : ∀ i < m, czRowChk T G i = true)
    (hconst : constChk T G tr = true)
    (hlen : lenChk T = true)
    (hdom : ∀ a < m + 1, domRow T a = true)
    (hT : ∀ y : ℕ → ℝ, (∀ i < T.n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq T.n tr.cT tr.lT tr.qT y) :
    RegionLB G ((T.loN : ℚ) / 20) ((T.hiN : ℚ) / 20) := by
  subst hm
  exact region_of_tabs_aux T G tr hn hgrid hvec hscal hpair hlin hcz hconst hlen hdom hT

/- ### Chunked `∀ i < n` from `List.all` over `range'` -/

theorem all_range_of {f : ℕ → Bool} {a k : ℕ} (h : (List.range' a k).all f = true) :
    ∀ i, a ≤ i → i < a + k → f i = true := by
  intro i h1 h2
  have := List.all_eq_true.mp h i (by rw [List.mem_range']; exact ⟨i - a, by omega, by omega⟩)
  exact this

theorem all_range0_of {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) : ∀ i, i < n → f i = true := by
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem all_range_of2 {f : ℕ → ℕ → Bool} {a k n : ℕ}
    (h : (List.range' a k).all (fun i => (List.range n).all (fun j => f i j)) = true) :
    ∀ i, a ≤ i → i < a + k → ∀ j, j < n → f i j = true := by
  intro i h1 h2 j hj
  have h3 := all_range_of h i h1 h2
  exact all_range0_of h3 j hj

theorem all_range_of2c {f : ℕ → ℕ → Bool} {g : ℕ → Bool} {a k n : ℕ}
    (h : (List.range' a k).all (fun i => (List.range n).all (fun j => f i j) && g i) = true) :
    ∀ i, a ≤ i → i < a + k → (∀ j, j < n → f i j = true) ∧ g i = true := by
  intro i h1 h2
  have h3 := all_range_of h i h1 h2
  rw [Bool.and_eq_true] at h3
  exact ⟨fun j hj => all_range0_of h3.1 j hj, h3.2⟩

theorem Tri.zero_ok (n : ℕ) :
    ∀ y : ℕ → ℝ, (∀ i < n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq n Tri.zero.cT Tri.zero.lT Tri.zero.qT y := by
  intro y _
  exact le_of_eq (FD.evq_zero n y).symm

end Erdos1186Ex

namespace Erdos1186Ex.R2


set_option maxRecDepth 100000 in
private def YYTSparse : List OMA.Erdos1186Low.SparseRow := [
  ⟨66, 26, 0x319f80000127d000004df00000777b0000111e800001d790000111e043030b75157257dd000009270000024dbc00028f6e00000b9ac134459650068f75900001ab630004115880003d761261c05581d64a805f1d0c3d97800005557000036148000455510725805412f41a44f20d0fd939f5ef754d0009cb9302abccf390000678e00058db372b1b0e8d85dd9b635d54f564d09e3728332d72a2cc8415fb831000018ca4000063280aada6090ec2ca72364475c888a8179e2100002448000002c1f000007c7800001c1d0000068700000341b00000d0680000391900000e06082eeb017000010c5800002214000013c39f064820d1ea5b04300000620900000bc200000340700000bc1800001f0500000e4100c9bb603⟩,
  ⟨58, 26, 0x3fdf40000d97c00003c5ec0000ef7a000025de40001fd7800014edd453f6c57400002d5cc0000ae710000665ac0000b96900002e5a00000c1670000305980001366500005c5900001436300004dd880011096100982e1809c6c435f0000309619a12944f6c95479394445744d004cd0d30001e224b106aba0e00009f1370005b64d8024db1356a3b40cccdac005310000f7c90cbd2ad2390537e8880052dd2103ba9c080000f411f0000db07800040a1d0000dec700000b11b00002c4680004301700009984c00016512000059444f507e80d21fb444300006910900002942000013c0700004ac1800006405000028c1040693603⟩,
  ⟨49, 26, 0x20760002401d400000c6d0000109b000000e629a0e315863fdabd6000039897c2677245e000001d5c00000756000001d540000075400000494c7b828d5246b66e14698445f50d99565d3818dc724d0fc728130000bca4a04a6065243e5c8948000001d000000073f000001cf80000073d0000024f07e851f3b4529728e8af9345395d30b40e07a9770372d1f670d89da9f1359b2fd70d09e131a335fd9144c822a11a31000001ca400000728000001c9c0000082600000e091551e122351b9bec88001a1b21000024c3000003e03⟩,
  ⟨29, 26, 0xe481000062dd0085637731254e59c8450c4f711194455a8000242690000b65740074ea517e025e540f479354f7dc50c5387376964c2cc86352c87174448000007d142f81a344a29b0e90c4d6e8c390001b9cd8926c33353782e94d157fd0732108319cc4c2f97b2333db1c88800e43f2109e948028c3494c09⟩,
  ⟨52, 24, 0x1281000036750000137300001372000013710000106900167d600000415d0000275c0000215b00001f5a00001d5900001d58039e954d24a0164846e1e34710ba084600003a45000011440000234300001e4200001e410ffc3e3900008a380000da370070c73502d7f13440485733d65f9d3242b5b3302f258b2f0001352e00002c2d00002c2c00002c2b0000272a2b596523143a7d2281dbb6219884bd2005c6501f00004d1e00003d1d00002b1c0000171515870f14000053130000241200002411b4e2ce0cd425f10b0000610a⟩,
  ⟨47, 25, 0x4e040001a30009ede9750004a530000015d7400004cb80000045b47f563278000351240f8ff290352c38473673eba3000001d14000006840000034100000f1d0f53e18e4000a8e7016943f370001701b00122d4d401b6d468652bf833490a569916cdbdcc0616ece5e00000a2e00000196800000cb0000006560000032a0000081211214a88ced12a84458e42321444b7b10000001c7c0000083c0000031d0000620b00001c45400000a280000031300000189000000c47463132183c1d550b⟩,
  ⟨33, 26, 0x7181000039a00000041750000069b000002e6b0012a91823d14325f11b0641780000175d000007d495482ce510c7e885414eb6034f287ddc139397d334d19fe3a93098b45a4b000476128187f7549122e7b1200000013c0000058ecfee0323a0b12cc8e59e2c4a3815909f8dd0c6a003637d0ac8d65f2e4f3442f4f1ccdbbdcb6326477b2cc400000325⟩,
  ⟨33, 26, 0x4281000036e00000051750000065b00000306b0012bad826d03a65f127b6a97800001b5d0000065488cb85d514f0594941e779794f1b2ab8d3a89afe04d2f8d8f130f7e48d4b0837f4128000218490e07031200000013c0000048ecbf9c703a277255ce4c2ceba380000b34dc0005d1360b12604d5a713473422c67bccd2cbc51322972308c400000325⟩,
  ⟨35, 26, 0x1e81000023e00000089750000045b00000426b000bc2d80e047bb5f0a425b97800001c5d00000514806505b5160d9f4d42b805f24f1404c0d3b62e91a4d667b96131619e954b1173c91280001ae490eb5e29200000013c0000038ec0001aa3a3bdea90e4c395e5380000368dc00020a3611082a8d48fdb3b3425e4b94ccea443e32066a418c40000022506becac8c01494322⟩,
  ⟨47, 26, 0x3c81000083200000006770000031d80000066e0000021b400000e6c00000258800000657000001d5800000755000001d5000000e53000012148000459510cacfcd40000edb4b00016752a4aa0c6490c25a252000000740000001cfc0000073e0000020f400000f3c0000130ec00004a3a1819b40e40002ce380000990dca2f43936000839cd44287ff341a3c350c8199f7d31000001ca400000728000001c9c00000b261112f349433264f2406078e48c0016432178c72c45c0001121660952f43456c2530c⟩,
  ⟨57, 24, 0x25810000057800000e770000127600001a7000001a6f00001d6e392be96d00000e6c00001d6500002464000030630000b2621ba6bb612a35ca5e000025570000285600002955000029540000925300013452000ac7512d6766508c52954f3be7694e0241354d0003a94ade8ec2490e0b1848000039400000393f00003d3e00003b3d0000183c1c993e3b0000e73a308afc397466c73800051037515d6136001f433501892e34000046290000462800003e2700002e26000028250000452400008b1b00008b1a0000bc190000b3180000bc170000cb100000cc0f2080640edcbaee0d⟩,
  ⟨50, 26, 0x81fc00000c78000004ddcd053dd76000004dc00000136f0000065b89fe4f26d0000599b000012d6b000005d9400001e64000008d8c00006b624f05779840000215d00000515c000014560000051540000145400001214c0000e9523829a894417cf13502795c6d3c0005ce4bb29ddd128000018400000060fc00001c3e0000058f40000623b009696ce919d3793904e942ce0027778342cce364cd0e11753203ffd38c4000014290000050a0000015270000030980000331b00000cc68000025190000090600000221000000883c0000210e⟩,
  ⟨41, 25, 0x3f1b12810002fcc00006029fc00006cfa00293c7c0000243d8000155e800012cf252faca74000024b98000145c80000a2e2359f0a6c13db4ab5eac9225a8000128d200008d6800002f33800017998d4417cbedd0ca65ea6d57eae916bc79700000bcb60000275a000012ac8000095613422ca9a0039c14c0005fb25c8d0e812acf1cec8a53632844000013a180000b1080000588200013b384cd59819c7353f0c800006c360000361a⟩,
  ⟨42, 26, 0x15117b60455acaf80000047df8425e747596abf11d0000163730e62cb9c835ede6710000069b14f08236bdd5c6fda80001236900003c5a0006023600049ef17d2e712d5ed5890c1740001815c045cbc16c00028a5115f193142a418724f5f1cc513b041ed84d36420b1324964614b6ddd5612b63306545187c9d510001e2a4300005d108000174410000128e8d51db93900008bcd87288663500de35cd073299d3348e3904c95edc62311978420b426750d2c⟩,
  ⟨52, 25, 0x3163f0000049f40000a6ea0000d0740000133980000c5c8000064e20000196b6bc83c350000095a4000048d000001a6700000d330005b91800031f4be1bef175e6f7fbcae9fc200972773b96b60000a85a0000352c80001a961a9f2329e47000a4e000665a6562bc792c0007269400462c467c22c5228000101100001a2860000ed42000076a0adbb9f4d1ce3b5464946035311fed5d980000224bc000ed25c100d1f2d001c639615e0924ac00b9225424dbee1f04aa7d8f0002edc740003003800000c150000610a0003acc4c1892cc240c37bb11⟩,
  ⟨48, 25, 0x3a0c183f0000049f40000b2ea722cf674000018398000105c8000082e20006ad6a000015b480000a9a0000038ce00001c6608e09aae942e38971672ca0b60000dc5a000053ac800029d601ce07ca00133f84cf9eaa4a5a49b88518e6b1da8a00004744000074218000399080001cc820020733501f05a9a36d0058c8a5ad6e627f6a8e30346e6b97c9400f4b80007205a0003a12c0001c0158001398a979437c401e99761f0003858f0000dbc740001c63800000d150000d70a01711644c0644e0240331ea11⟩,
  ⟨49, 25, 0x73f3467e0000093e8000165d4e3cd30e800003073000020b90000105c4000d6ed400002b690000153400000719c000038cc1104175d28b623ae2d2ee096c0001b6b40000a759000053ac00d5b5d340a7ff499eb02314b49cc95231c94fa514000090880000e843000072a10000395047065ce66daf5c73231a1a118a33aba8c0cd961c5f25f7472e0001bf968000e2cb00006e8560004d82a079f5311df84190857c81fc401d8c401f00035b0f0000d7c740001c43800000d150000d80a019ca104c045a7a2402342111⟩,
  ⟨55, 25, 0x282040001ff0000001b770000093b0000089c0000044de0000226e00008bb68000035b0000034ca00001e64000012b180000e1883c61bec00009e65f2293de2f00001395c0000d2ac00007255000039aa24efe4d4c928e76a49df2f75158180ca838b4ecd3c001ec2980001644a0001a0a4af72af52000017c800000be3f00032a1f01ee0a8f5b554e67915fbc63b0442459d16bc9b8e41c282470000312370dd4ef1b0877e44cca43c906409cef331000048148000240a00001624e0000b82610545c92eee8a1c9041cc4c460000501b0000280d0000380640001be3000004417⟩,
  ⟨52, 25, 0x504080003fe00000036ee00001276000011380000089bc000044dc0001176d000006b600000699400003cc80000256300001c31079d7b9800013c8be3c2f115e0000272b80001a5580000e4aa0000735449d95d29924db2d493c4d76a29ad8fe5086853f278003d9d300002c89400034149557bfb2400002f90000017c7e0006603e03deba1eb6ac150f22c2526760885bb3a195f631c8386adce00006246e1bac5a360f8ba0998000240a4000120500000b12700005c13082ab2c97770778480000501b0000280d0000380640001be3000004417⟩,
  ⟨54, 25, 0x6910200010e8000000fbb8000065d8000046e00000236f0000103710faea9b4000020d800001e65000015b200000c18c0000aec4000090610098c130000200d7c7234ecbc000044570000302b0000199540000d0a9c3482f536e0cbea92ec330d44508932a0ca07854f2d64dba700004f12a3774029361e68a4800005ea000002f4fc0027fc7c000fe63d36ca559e1d751d0ec000fa67414efce3900014c9c0000660dc0066b66a26bb18334632be190000190a40000c85000008c270000581300001ac94000052480000771b00003b0d00002fc640001903000001d17⟩,
  ⟨51, 27, 0x14a040000063f800000778069cd82ee281a945d800006c3800000d86f0793b68dc1f45999b400000f36000012a6501b9132c80019c6d8c00006ab1034130261048308ac01b4a7c97c000058ab80005d1560022c42aa0a29d31513ac929298f01d115230fb9c4a247e1e0d40b42efba78a340fa4e238aa76953cf25152400026f2000004db3f0a6ce547c0552284f40000209e000020f3b1a380287411dcec8e40000889c0109f6c3306f605464167fc6cc400187294800314f2806868ae4ee5777dc980000041280000aa1b0000154340000214640000418c000000917⟩,
  ⟨56, 27, 0x80fe0000069ec00000cbd000001179000001af00000039dc00007cbb0346896750000034e80000035c0000006b780000106e000003adb1e61c8db042a4413580000126a0000020ca000004d90000009b1800001a620000226c254a887980ed55cc2f8ef67bb5e0000018ae000002d58000005aa800000b540000078a413822e94540344928298d2294f3aa34689d6b57f5134cd764b261ac157b4b21d6de094000002d000000059f800000c3e00000147a00000a0ec0003079d0520fec3920fd3f86835811d4ccd1b90619042b76531000001652000002ca000000593800000726000001c360000038680000060c800000c18⟩,
  ⟨35, 26, 0x32810000646000000b77e000004df40000257c00000b9ec00002f7a00000fde400011c760b759a5d550deb6740000061cc000018720000061c47d7f406c3d30641ac016e8a6a0000065a40000196800000659c00001966215bf7180c39bc65f1e5cec978240cb9511726e414192651f4f45145713a8ff79b4d263300130dee82c4b000124d280000fe3a42e97a8d0627f2e31⟩,
  ⟨46, 26, 0x79600420e907e6b1b7d5d7641e45742d1a0bdcc8bef567223e48a9c40000136c00da431aeec06f96a00006fda40000a96700002a59904961e6023eee497817d7f25d00000f9700000345b000039d68000062590000189600001d6510a93dd1419ca1fb4f58139053a34f1034d88c1de5332f4d274ba41df51280000114500009f911978ae24321f31cd0887c5ac41000e77cd680d2933480e1710cda7177b32109ba1cc59aff762d26c55f0b00c85b02b000064ca80000071f0000040740000141c⟩,
  ⟨50, 26, 0x66df800000f7d0000241d40000c374000009dcc00002d7200000b5c400002469000008da000001867000006198001598600002ab57c1ca6e35e1e62d357463856a5c14c598d6c00009c5a00001d56400007558094737d40f186c84f313f77538606e3a4d1e535513112a5054b00002951c0000bd465f3070d140000544400002050c00009e420000279040acfbd39000043cd80038213500d49f0d013da11310002e04c0d4b9522fd103740b80004032d0001070b000045c2b0000548a80000f320000069c7c0000621e00001787400005d1c⟩,
  ⟨40, 25, 0x443a80002c1d0000058e400002c71000011b480057d180000f92be16d7325e0de618ae8a5dacd700029c8b600009b5a00003b2c80001d96084fcb4a0c807344f2d3f7026917f2153126d074960000b34700005e2322f7a11140000a68800007e4300004da1000026d0400ad486a59ea84320b431e98cd64ff4c09c1aca5f16a7e22e0001f7968001098b0000990560001622a0000fd0f8000194780000ba3a0000561c⟩,
  ⟨42, 25, 0xbcea00001c7300000f390000079c40001b4d4000018690014213000041997c54e384bc2815d85d1274992e00001f56c00008eb4000042590000212c0b65629380df4fe9a28e7534c000745a580004fd1c0001a68c2dd2b34500001422000010d0c00007e8400003f41001e441a8548444d07e2f6e668502803251cbee18e69333cc0e599d65f2f54202e0000541680002a4b0000158560000682a0000b38f80001247800007c3a0000381c⟩,
  ⟨43, 26, 0x5e750000071cc00001e720000079c40000d96a0000061a400001366000a231800010715f0cb56b9785041635d127340d7000007d5b000011d68000042590000109603726664e01d59253453d3c14c0003a112c00014047000034d185b9ee34500000a1100000434300000fd0800003f41000f40cd4201bb13414a47e4ccb3021a32483e5e8c7349d093039617fcbe5eaa712e00002a4b40000a92c00002b4ac0000682a00005a07c0000491e00000f8740000381c⟩,
  ⟨47, 26, 0x1d3d5881000054a0000001e770000059d8000019700000065bc00001d6e0000555b40000116c000006d940000216400000a58c0000346205a37ad780000325700000ed5800003e5500000fd509f1ffc530d2ce6148013ef6512cc87c5409f63d54f0ea61d138b07e284d04166f12463a00f48000013d0000004f3f0000564f88f4ec63d29a939cf0d174633b92b7dd4e8df10e4399f26930e0eb2731373679d70d8efc7fe358e0a92cd00000392900000e4a0000047270000218980000292500000dc900c9f9423⟩,
  ⟨46, 26, 0x771a0400017b8000000a5dc00001d760000075c000001d6f00000a9b80ce23f6d0000051b00000226500000a1900000306300000a18852b9625f14753597800003d5700001555800005b550000175505a83f353029f4214800149b5107b4b7d40632cd84f063aaf9384c2a844a31e9969242fe31a4800001790000005e3f20b39fcf89db9ef3d3c5665cf0e3de503b9b8e6b4e8edd29f39adc7bf0e1197e5d378360458d91ae7e3350000108a40000422800001489c00006f2600000689400002b24⟩,
  ⟨47, 25, 0x73a040002ad0000003377000010bb0000089c0000044de00002d6e015468b68000051b000004eca00002c6400001a3180000b9885a4766be30a20b5e0000212b800018d580000e0aa000074541845a829814a1d948000c44a2148db95037eb0fa789851f138628f94945aa857490b9f53a400001a9000000d47e4381093e2860059e9d12870f0dba912773a732a3a3084fc9cd5410d0e110e7ee6efd178f364070311a8000130a4000098500000622700004893000004c9400003e480628cb23⟩,
  ⟨46, 27, 0xd6d1c0800010f80000001cfe0000025e000005bbb800005c760000070e000000e1bc00002c3700000c66d0000032d800000e994000017320000033630000052c408dba717c2457222f00000535700000d8ac00001fd5400003faa10b48f0530f817daa4129c3154432484f2796e2b664a03cded692120f91d2000006fa000000df3f0b19f2a7c4901134f492253d9e15929233b8af1d56746a26988e6d7dfdf1c211e4103768235b66c0000180a40000301400000902700000de4c0000024940011689183cb9cc22⟩,
  ⟨24, 28, 0x6c1810001a908026117687f01efb6c7714419d676000007f6e041bf196d00001366c000031a6100091a160001993a5f05cc01a5e15b38175308dbfd4522b1cb174a06316634800000af4000000af3f000019e3e2b8e67e3d097c6323c23dbb4d3ba1666133a3c688a239⟩,
  ⟨39, 27, 0x336728604007aa84026574b77f0004008fa0002585f00b008d3d80047d67a0006e14f209a5d21d0000c24b98239ba770046c686de04f3c65b81091b3b694c8fb26c1613402d62f39761a80008e43480013e2680006654ce000cf819800cef7b081684b2602b36ec0be1a18fe178b8ebfb2e8002cab5c955c59c96553aff128b0cc94a487945ec48002ac3a8e1d3cc590039cf411f800c61f3e2abadd67a77e7874f0c3b1431dd37a7ec3a⟩,
  ⟨41, 28, 0x1cec89c8109e404280000178d7f0000d3d7e2377e757b289b7ed7a07534ce790eb8ec87503ef2d8740672e77730002c816d210ef616c068adb16b000083a6900006c1680000ca2670000cae6607157fd6403a99b86307cf2eb620418f4a6118b90786067d05b65f21a7edb5e50639595d21d4acc5c0001cda5a9842ed94b3ddf77b4a5ee2c4c490740cf3481c7b047440001e2b400001e583f36183fa3e245bdfa3d018aee23904320a0320000de72d00018382c0000a7a2b⟩,
  ⟨48, 27, 0x1252f79020c82fe1fc1a044f3d852f1ca7a08a6162f20acbd15dc64b016ba94000e974033cfd8e6100dd05c01d49853782095096e18e40f6d81f735f1ac4289703502471946903558ced009b403d9c180867b301681c5650b7a0e6c80d801e98c20328eb1080f7f561149cabcc0862fdb57c8ed12a2f25a983a5d13d9d7eb806540ad681c088e2c85e7c79585ac2ca2991b5c5252cb2bb6e251574cfb491084de090220a5051c1869602286bd91c4405cad0e800bdb284fd1eb27e9f02fef7d39194b2c264000f2e8bc073013170c7496c2d⟩,
  ⟨43, 28, 0x9de7e00000437d00000517c00000177b000001b7a000001d790000022761572a5e75359c408740e356117300007ec7200007bb7102063726a07088cd69018ada668022e42067045c5766616a35a2604e0975a5f22886375e45fade25d00000b15c00000315b05506585a09cb8ff5909c95375805262f74f4d56bb14c85a376b4b2eaed1e4a248caf849067b3f94811623384400000be43000029942000029a410281521330bbbaf131000040730018518a2d01730cc2c044f62e2b0be41c12a⟩,
  ⟨39, 26, 0x4a7e000009df40000257c0000011ec0000047a0000011e448654d750000359d09b3fd6730b12f7dc82ec1bc7100000eda86359ff690a4f451a027cb736713e57ad98003f9d60787f3c17cad01d15e0000345740000135b0000789680001eb5900007ad60673a374ff7291c5350281514cca582512cc9e95c4a00000611000007f43622fa050988c78b4100169d4d0aff0df320001ac4b40007932c00068dcac0006622a⟩,
  ⟨39, 28, 0x1f7d00000047c000005c75008e95d74163eb2a7308fc7957209699067100000376a053b3a06900019f66800000766700000766600000315d00000135c00000495b001627d5a000047c59000047d586e3d6b14d2af80574c59841be4b0091e18480000010460000012454cb2b1444804ce0a431f37928421f3c2df4100053cc3500195ea3404c355c330c2718d3201a533d3100000132f000002d2e188a5b32d0fe7d972c14fdf322b19bab482a⟩,
  ⟨38, 26, 0x75f4000027750000281cc0000f67200003d5c40000d26a0000249a40000916800001059c0000416600058757c3170c15e144d5e9740001a75c00081456c0005805a000073d640001cf5850397f5386dd9ec4d22dcff9311a42b54b49247751b4d7115455b14e19126340104312d1d41084b898c410006b54d424c146330bde108c4005b0730001913cbc00064c2e1433770b45fac3b2c151dbe8aca7bc3a2a⟩,
  ⟨40, 26, 0x6df40000257500001b9cc0000b97200002e5c40000616a00001c9a40000746800000f99c00003e660c01d8d788abf345d000053d7000045e5b00008656800011459000045160d4eb2d4e2acf6993401013c4c000b9f12e98948e473f3b6bd1b1fcb434545a6d751233b767430eefe7d083b50e14102dbec4e400197c3505d000cd033f69c330a7f240c546c0e8300e01ed4bc0003f52e4ec471cb475e8662c015ebb4ac5760992a⟩,
  ⟨40, 26, 0x6df40000257500001b9cc0000b97200002e5c40000616a00001c9a40000746800000f99c00003e661389c45788a86665d00005397000045e5b00008656800011459000045160f3f8704e2b669593400ffdd4c000b97d2d1f66f748a640ea11cfd2c7246c7fb531151691f2448cf92dd0c3b5448420ee2719040b82a2390006620d41a7f5d340f7c0e0c5468f94300dfb9a4bc0003f42e4e4a7f4b477c4442c015fd68ac5728bd2a⟩,
  ⟨40, 27, 0xb50200002c600000003bf800000678000004aee0000051d800002538000004a6f0000082dc00002f1b4000006360000032650000076c800001098c00002931000011f570000910ac000250d5400059eaa394d8495334b60b0a53ead441441e64e2a808a32a14f07a25949c00061c93000039220000071f3f00063927c37c5cccf40000aa9e05295263b11f5eac741184c9ce40004bb9c0004c58370604d986c0908ca4cc2ab0c399010213b31⟩,
  ⟨39, 27, 0x11604000003bf8000007780000052ee000004dd80000313800000626f00000aedc0000f9db4000005b600000396500000a4c800001898c000035b10000565570001a26ac00073ed540012ab2a3f1154e533a357dca508d973d441f36802808d996b4f08b9df29c0005249303dbbed2007c31c03f0bc0ed87c262784cf40000d11e00007133b156ee98742d6b884e400021e1c00002c7370000ae06c0008f48d40fcc77198449bbd32⟩,
  ⟨38, 26, 0x10a040000077f000001de000002a77000004dd80000697000001a5bc00005e6e0009ad9b400000b6c00000f9940000596400001c58c00007b6200035055c00270f56001b7255428a99754f7501c94dc1ec8552b7ef4e5466b367c502fa5cf13d11985a4e0005d313042a923401199980fd0dac6d3e1f18cdcf40001913c0000d44ecca24a43a303ada4e40002a8380000a18dc00049736021e068d03ff89832⟩,
  ⟨34, 27, 0x20c080000077f000000ef000000a9dc000009bb000006a7000000d4de0000181b80d8e4db6800000b6c000007eca000016d9000003ab1800007a620002692ae000ba5d582179eaaa8d72a5e54f3b6f26a6e05d0e14b1183342884c8c12503cdd8989e63cdb613839d280a006eca4c3f41441967c3cc25e4f40000c09e00003283b30f56e874441b974e40001469c000026d37⟩,
  ⟨30, 28, 0x127f000000e78000009f77000003f7608fdcb67008faf0b6f1e29e196e280f27c6d09cdc6e6505effcf6403513246311a15346217a199d6138e8c95573e39f83563dc508d55788aec354c276e555365f04ca5242afc7d514b2441b50019482b4001951203f168d3493e0339c053d00000123c00000513b338729d3a13d025d3915fa47d38⟩,
  ⟨33, 27, 0x7b5cd47f000003cf60000061e8000009bc80000527800002d0ee000031dd81f75ee3803ed1376f1caf52edc3b112d1b400001d36038f2946501d5570c801817058c422f75b10a377e86135bdd56ae74d7f4158e148dcaab80334354cc1124ea6ccab0d148dc49c5a8800013f40000027e7e1e79fc4f80000b49e822bdc13b3779340742464f7ce43a18a19c000005437⟩,
  ⟨36, 27, 0x873023f24badfc065a8abf17e41657b0c69468f400d64c9e44ebd2b3b00002947400001b2e622caa11c045c44bb78c2cbbe6e2ffd128da1e8cb71b024499fb580001f06a000659eca0008c0d9000033ab185cfab5629cffca2af0a8b43d597271e0aae438086549510194a68018ff1482c2999a400011ca40000239a7e3c57620f83540da1e80002b83c10d4f0e76f80432ce90e70109c800386838⟩,
  ⟨42, 27, 0xc4d8cc0a1afcad7f302f94efc1421699ecdb1a1dbd16bf64b7908d6886ee0565025d80046b8ba8709da87401670f8e42561905c05e8f8eb7866c4036e29818f2da868f1adb04a097c3582843676a033eef6d20bd22f1a05a6b64b280f0c62630bd7cd8ae0a2441d592f43442a8787b98548fe08b8a63cc9165241d7b38a400cd42b440278bec86040041d0807ee19209b71a7d4030ade687e59f4a54f856e2331ea23d3443c51b190e772973060e92afe581cba6f7cb38⟩,
  ⟨51, 27, 0x40463a604efff21c03106b0e7f37f797cfc0e5eaadf4302d2e3e0c5974c7b2a1b9d4f47fc8bfde443515ebb8743ad87650d9186e82033c05cc27682c389123ba77024e9888de46d4b55b8fd5aaf36a7c67fc6c3e76054d66d3c5cda86f43c4348a486746808f5d38ce15ccf519852da05b284dd9b0640b9eb4ac61f5d8518824cb74ae843f6db5c0ea2a2eae1d64139585a923baa9fb538f5448a04289225cac2d206d8c1aa305245364309d9c46841314e1504a7309ba01339cce3f3f3954a7c33a4dacf52bce551e309dc5b3bbfbe4ee74be6e098e656c3849c05de04b37⟩,
  ⟨45, 26, 0xb295b3816a130fe02462d017f60ace8df8d4f2dc7b3d55d2de8688ba2790fa929ddc00928e7551a3b69d02bf9b3731c9acb9b8c6d17b6d7080429b127aa836b536acdda8da60a169131cb9da01fdfa467097bdb59841d2316506ff8859025b468635b4c8bd68c8426b593896e4d6039c39c570ebb2b159053c7f5554c542d51127cc2492a4e9b52066d13647129cf8d14339a1a420cbd1e10480036840198ca7cfcf321ca3e11b9840f59534843c4f37ddceef6b5bb3a54fe5b4e5b745e238⟩,
  ⟨41, 28, 0x10f7b8a810d4d11f8002605b27f000e4037d12331927b1f66b077a3112fb779001d8a0770005feb7524cc9c57400153037100019316d545096d6c268af456b1ec73c46a076642e690547d4668001afc367001bcf1660a45cc965000ab446346fbfbc5c80934635b06510bf5a0aa5d5d590aa5f8a5804c7e844808cc2164700943874617ddc914501088d2440b32b4643015d69d42014fc0d4104658a63f22d27083e21e515f3c06e7a173b56069c23a1ef6691392b0831138⟩,
  ⟨48, 27, 0x6aa702004689a002bdd6abf87fe4727e08e4314f62aa24d5e8cd383fbc8003782751b1371ce80003f55cc00b7bab9018a46171000228ee00004559bcbcb6adb607b91646b47e4712d4163a0b5a41bede4b4029fdf7670a9a67eccbbee9317a641a2eae90a4c0a5c517f67cb61d559196800ebee2c801d67f580003b8eae00060e958000eba2a91e73d64907cf47a9048773b11c190884230faa8dd4511e63e4887d7cb210c2afa46a1058b562410003d60800007a80fc0018819f000144b3d0a68f4c788518a0ce875cb8e1c84e46f938⟩,
  ⟨38, 28, 0x27ff800001a0d7f0a8348d7e07431c77b14dd2367a14ed4c9790000a5c78000056976000125e7522baf2a74139cd5a731d0aeec721be51b47117ed1e06c0d4fe006b34de84e6a0ffcbc26908d92a9680000c21670000c19664848edc609d19eff5f49398ea5e861e8495d32604675c5d1a8e65b13110ef5a000237a59000237c580000713491f09d77480256ad6470e2579a460ccb98345053a096440a4ea7b4300021183a09df14439⟩,
  ⟨46, 26, 0x2d8dfc0001177d0001b59f0000ebd7b00145d5e870cdb879000120de000033177b63f3c1d910c00b757707c69d00003ac7300003adc80000ec710000551c00001546f00004adb914393f6d3b6040db00007a86b97ed7c9a800016b690000535a00001286700004a1985878d3640e3fc358d72675a62b7c0391854f964460f403aad7d793c865ec15ec1974d4811c5c00006bd6c0002325a00008456400021058000141129ccc2af49001e2a120730396472ac13b5100001d74300005910800016441⟩,
  ⟨40, 27, 0x7721b0fe0000235f4000051be015e4e97b0000488f400006ede52874983c0dd15e8770000a3ce0000146dbc865638b74cbbb386d00000c8d20000191a00000403380000806602fb0e4ca2fa49e9902a0e69b183d1d1962296df64c18ee95ed7cb918212f223baa65d0000152b200002a5605ec17ea81e12c464f1e807a69c37cbb7130000276a59d2d8874acc33d84929b9fe29221f74112396dffb6460983e168800002050c00003f21000007e41⟩,
  ⟨40, 26, 0x845de5fc0042ed7e05bd729f405c8d87c11512b5ec220a4f7a0dede39e42a1b77780320fe5dc001d7976313abd1c0ba548e6f639ba4db81324cd67056e6d9986aab1f650c227b590128f7c6319a9da9885d07af61207be2d808eec6e5f35196d1788471cd5d024b5e96d1b35e858106dc9544307bb2502e8e1a53c935c464e297d8e13447ba894c71638492c006ab44aa14bf492518d287488ced9611cf4e88b4606e594d100e219043⟩,
  ⟨30, 27, 0x24c3aa3e8360df17c0000028f6000004de800000b3c800007a7300000e2e400001c5c40000523480000b46800002e0ce00005c5980002e5b00c16b345e0000188b4a0c11c16541dc8aac05e37744e36c2c009a51c4cf1301c5fa225860506c4a938c2949293e809121d0a5e72397fd1ea46016728e8800002ad0c00003fa1000007f41⟩,
  ⟨24, 25, 0x78b4e3e9b94425f00004f8e6811b687241d0e53880002cda4000168d00000d46700006a3300000416e4922beb4f6438a597b28d62c3c828713c0d429a9a3d55fb4c6f0b9c25e3da76126473268917b408747000023220162dbd0c0001368400009b41⟩,
  ⟨26, 26, 0x81f80000357d000001df16d146d75d8bdf05d0e263a9731f122d5c877fc3a7160258e9a48c91ea680af50c59c57a878660cd3769780000125bd3b36156b1def8a59c77e61d6052e6d94e75a1ddd34f8fb224c3220e092c00000545000007510000096430ae3951082b91be41⟩,
  ⟨34, 27, 0x14f292bf00000117d0000006f816db6bdd4312a1f3a000003f7300000a4e40000149c401967cb500000516900000a0d000000999c00001333206cd065f12fd8c4bc468ba7d7400000c2e4bd3c8f5b2d990f2b443bf42564879f1f2c00fe9de500adde2c9811588452c55b2f02507d9ea44902e4b429000012b11c000020a3000001c4500000b68800001e50c0000dca100001b941⟩,
  ⟨31, 28, 0x24ae4a77e00000227d00000037c00000267500001657400000c273000013c72000013b711ccb9e66a000008069000007e68000003f67000003f6600000b05d00000665c82c05cf5b253e7965a22b15015922b51955801543b1500ea0f574d214cebb4c079749a4b00e75324800000b4470014ef446000009445000007244000027143000076a42000076a41⟩,
  ⟨27, 25, 0x71f4000006f800002c7500007639800048dc8000242e2a0fd936a00004d348000265a0000076ce00003b660001952edf8b05573a45060b652e0605a2082a9ac901efc560235e2ca03b88724e1fe9a8a691941113000014c8c3a728f450000d8a20003b710c0022fe8400118041⟩,
  ⟨27, 25, 0x71f4000006f800002c7500007639800048dc8000242e2a134b86a00004d348000265a0000076ce00003b66000195aedf81be573a4f452b6530b645a2030f1ac90263d560235ab4a03cc8bb4e1ded34a693795453000014c8c3a8ab1450000d8a20003b710c00230a8400118641⟩,
  ⟨28, 25, 0x1740800001de0000078ee00001776000063380000319bc00018edc02bbe36d000005b60000169940000d8c8000085630000773100002c584ef284ac00019515f15705aaf000213d5ceaff88ac51bcbe553a17cbaa044c3594c000238a400103951cf721b284df75013d00345c9c0017e74c⟩,
  ⟨30, 25, 0x5d020000077800001e3b800005dd800018ce00000c66f000063b700a8d11b4000016d800005a650000363200002158c0001dac40000b1613b309a3000065817c556536bc00084e573b16192b148398554e67d10a81142935300008e2900040d946cc2110a12a623c4f372203a70c44b4134002fc69800010b4b⟩,
  ⟨30, 26, 0xb2040000077f000001de000003f77000006dd8000371700000dd1bc0006196e15ddcd5b400000c6c000053d947ee01a641120a718c59c18562000069184418f8a60cc866dd7dfc0c5e5e001436d5c6a8fc3563a51d8d561a39fc5451f54614c76f236523a67a514561f79c50819c4e13cef2bcf4e7e1ab11340024834c⟩,
  ⟨29, 26, 0x77f0000021e000003b770000059d8000fd5700003f1dbc00f8a46e0673efdb400000a6c2381dcd9497b64c6413f85098d2477b562a774871856d95e2608470e397cd10a225728664c1588c338c553cc3bb550261d8d5300054dd486d8f3351307926d4111524b4f1164c5d380011234c00001c52422051c48⟩,
  ⟨26, 26, 0x25fc0000017b0000005e800000f780000065dceb1ec1703acebd1bc66b17d6e0000105b4a89462653c50221907239b6634a374b5888f46be617567d298000014b57000080d580002025500007bd50000012530000999457fdd7750ca80a5d3d2bcedc4ed637fbd3460287a4c⟩,
  ⟨29, 26, 0x7874077f0000059ec0000127a0000039e40000527808eb0e1dc0000597647de4e1c11fb02d6f19a1561b80001df6d000009db0d5762365394a6f1906c78c163562a9bd8a31d8b3616855485804f041757000110d58000358550000d0d500000565307d0ef9489ec8e751965a83942d3a5024f4cb7cfd38a39c294d⟩,
  ⟨31, 28, 0x126c33e7f1005cb37b0afca7e7a000018a7900006a4760000046740000b42700000b516f000045a6e0c4ea336d00004946c00000e76b2472ef66526c1fe16413c794c6345f3c7c62a0af81761566bed360077ba775709ea70d560c94c415517be6e15434aada7531c1e21b523f7e7f6514d5c1105062271194f30911d14e5d753bd4d231cd6c4c005a52d4b⟩,
  ⟨40, 26, 0x8bdba6049ccd7f7f14e5175f80e40b17d0f07b99f0368eee7b235b675e8fc70c07919aa701e031187e77438be41d8b05be7741676af9c02f37dd6f04f1fedb86254896d1359341b00a7fe36937ce05994efdd63641a2413d8d9f49a962e95ad318413bdfe5f0bb3481780a521e59029cd4160597a0e572e1236d58a7a9525534f97655172133d5332e60594a4fc920519048435431f26724f56b5e293a6143714d3ec0919308ffc6f4b⟩,
  ⟨32, 27, 0x295020e2bed200d89f91bf80000887d0000e9af85e4d0e5ec66d3d2bd0ec3ae77900589acf0168794ddc37a4cb3b000016a7505b20bce00b72f41bc00015337000013d6d5279dc4caafe13d990ab91f631dc392b7620001598ae0000cdd580001152a80002145409c4f36a605261bd480014dea8b1d05ce508b81b749e5e412313979703da68476e5d4c⟩,
  ⟨19, 26, 0x21d4810002f3e007ba46e7f00003a9f41a43137c1395b55ec0003387a0000349e40002f36f0000691b8f45d2065466941d908490a06385d22a588103195570000aa95800021e550000829506c69a14f⟩,
  ⟨20, 26, 0x275f026040016da803025d51fc0005ca7e0000be1f126301e7b0001b05e80001db792703b05e04f84f4770000905d06a5ad2701a91abdbc00010769350f25995f6379d643cab0658f36156062001a0755c00207e52⟩,
  ⟨28, 25, 0x3cc4dfc080941e601bc533efec360117e00541fbe800ced9f198411af6376ae97a30a4313c8007701e0003172ee825fa674001bd6b98006801c800549edc0036126a00116034800b7cda0007476ce003b36667176c932c7e79d5910790aac60032295b000cd62d000638d640031c4b0001b4056⟩,
  ⟨27, 26, 0x3b53c47812316a7a033459147f450e22df8066fcb7d005d329f22a89d77b6fec949e97449ea79057e665e002c73c77012fa09d80881d0742ca4a55cc084c9f7252257f1b15735936ba8e8bcda8072eb1690ae100d9c4bcd8466a575ab9940046655c01221156c1d2ab65907c89196011177f55⟩,
  ⟨27, 25, 0x25d4956065b9ca900dba1827f58c8c63f0eeee71f4fce5b6f92c20fe7b4348a2bd13352fde4ccc9beec8aeefe753de8f03a0f29419c4403be4e0247df76f14c47db706b9471b57f9ba8d9f18a336a20fdffb3953a24d98606092ba488ad65b11d5d52d0df6629644f8ba6ae22e32256⟩,
  ⟨28, 26, 0x6a372ce060aa9da7f56b1ee5f8e1734e7d1e73ebdf198769b7b4517101e8de41ec791f99615e11e8e50764e9e49dd4f6f6c97442d0ef5cce915747236195b1c479c29e702a5d5adb863c3cd6d6fdc705b1e2069f6a1a531f9a0879306672cf8fb5984748215f2d0672578e564c25c2f2ac096c6b38a857⟩,
  ⟨30, 25, 0x722bbb029ffecf8012cf853f99659d9f862616afb83b60b7b545b893d0612a95e434030cf014275a76283e0abad9242a9d14776eee65fae7472318458b882c03e5c070e7f6da4b89626c1450fdb597b5325a82ea7d6d21c0dc8684c7cacb3cdb9601997d30bcba2860ac5b166332ad094b2fd64774f10b011508057⟩,
  ⟨17, 26, 0x4660bd7d141a5a1f00001257b0000451e8000145790a32d9dcc9f1cc0722d11cfdc4000b65694d4f161a1978e1767cbe9c4d980004465d00008896c003d8c5a552f7d56554a80a58⟩,
  ⟨15, 24, 0x30f96b7d2f28047c00007a7374be0b726de55171daf1246950d4bd6873571067e6a31366000262600037cc5e0000135b002e245a3c378e593c0b9958⟩,
  ⟨14, 26, 0x449f400000a7c0000d1dcd3536da724e1683dc73f33c469453cba5a133980d6799cd2699814dba85e00000b56c0007295a000191d6400064658⟩,
  ⟨19, 25, 0xadf4000006f8326c787400614e398078fddc80843e4e3d0de7a6a00023ab4800120da000014ace0000a566000627afb6dd7ed780fd8ecba0004125cd69eeb2d9d418156a355864b31a6fe858⟩,
  ⟨18, 24, 0x2b7d0000037c0083cc74003867730ebd287205f19d71be6ba66a000491690004c5680000a5670000a5660012075f0688f15d0004425cf420175b3edda25a7880275978e78858⟩,
  ⟨16, 25, 0x15be800000df06d3dc2e6009efc72009536b882edc61a8000a32d200061168000053b380002a1987f204eba0006905c9f51e2ad9135ac5683ed068b21f197d58⟩,
  ⟨16, 25, 0x133e800000df0001488e6000b047200056638800064da8000274d200014e6800003133800018999921fb8ba0005c65ccc9eb3adad0986d68b6b5dab25b3e8258⟩,
  ⟨15, 14, 0x688102ba000077f001de0046770051d808e700239bc0636ed1f5b400b6c00ed940446401418c06662⟩,
  ⟨15, 14, 0x688102ba000077f001de0046770051d808e700239bc0636ed791b400b6c00ed940446401418c06662⟩,
  ⟨14, 22, 0xfe04000077f00001de00003f77000055d8000b1700002c5bc0008e6edef261b40000b6c000139940005b640001c98c0009562⟩,
  ⟨13, 26, 0x87f000002de0000030770000031d80000c0700000301bc0000b76ee39a519b40000076c00002959400007a6400002e58c00006462⟩,
  ⟨13, 23, 0x37b000006f4000009e616ac2bc000026774b030ce095c3d9bc00032b70000086d00004eca00006990000093180000962⟩,
  ⟨6, 25, 0x51eea7020003ff80155335bc6bde9ddc35e4f2cde00003365⟩,
  ⟨14, 25, 0x19d62cf02d44b51809197353fa99bd59f844a65cfa4d337f7c09f5e5bd8844d9de453feccf01122047113ca6eb80296cf194291866c6001c8362⟩,
  ⟨10, 26, 0x56e4796063d5f9380276db6dfc7995487e035a64df46b6f287c0001bb9ec0016e07a0024bade4328d2b62⟩,
  ⟨8, 25, 0x5de24dc080153f6000036fefe00971d7e48f6fa3e9a1c8e5f00031c2f14bdf1b71⟩,
  ⟨6, 24, 0x82810333868093f2727d8da9707cc1b46d72c613aa71⟩,
  ⟨9, 22, 0xa20487d00001df2582ac7373b969c9b6a9c710004fda400166680004b19c0012d66⟩,
  ⟨11, 20, 0x21810029180000567d000047ce9dd0730704272020367100077690007b6800052670005266⟩,
  ⟨11, 14, 0x353800101f40037ca8c1cc5eb721639c40106a01c9a407168010d9c04366⟩,
  ⟨10, 10, 0x6606e0800a9f579733e5c8f8711c9a469680e99c3a66⟩,
  ⟨10, 8, 0x3781ab80a577337634754d704d6f756ea46d0f6c⟩,
  ⟨10, 8, 0x3781ab80a577337634754d704d6f756ea46d0f6c⟩,
  ⟨9, 8, 0x3a819c80fe772476e570e56fd56e876d0c6c⟩,
  ⟨9, 8, 0x38819b80e9772476e270e26fe06e856d0c6c⟩,
  ⟨9, 26, 0xa460d68100013ce000000127f81cdde5e0000090770000125c00000486f0000075b80000096d⟩,
  ⟨2, 9, 0x18ef92a78⟩,
  ⟨8, 7, 0x30fbadf01bd837a06f231cc6b90d71⟩,
  ⟨5, 21, 0x16f4547d00002be0002ddcc0038ee4001c271⟩,
  ⟨5, 21, 0x4b7d00001be35f209cde22ece50fcf071⟩,
  ⟨5, 18, 0x217d0000df015d573a3ef5ca806e71⟩,
  ⟨5, 18, 0x217d0000df015e273a6c41ca848271⟩,
  ⟨4, 9, 0x18c0a520272ee2176⟩,
  ⟨4, 9, 0x18c0a520274ee2176⟩,
  ⟨4, 22, 0x126040009580807d1ddc0001f76⟩,
  ⟨5, 25, 0x1da7fe58178660c400000039fedda9d0f0e0ea9277⟩,
  ⟨6, 25, 0xd4f84d0280470980000043bfaaec28df736bc04f847a0bf78⟩,
  ⟨2, 24, 0xd8275b7d3bb4a87c⟩,
  ⟨2, 22, 0xb99a31f8000687d⟩,
  ⟨3, 24, 0x628100076c80b313e97e⟩,
  ⟨2, 8, 0x2f819e80⟩,
  ⟨2, 9, 0x6d032f80⟩,
  ⟨2, 9, 0x5d031780⟩,
  ⟨2, 7, 0xfc0e180⟩,
  ⟨2, 8, 0x3a819e80⟩,
  ⟨3, 23, 0x212e5e06cc019c000003f7f⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 1, 0⟩
]
set_option maxRecDepth 100000 in
def YYT (i j : ℕ) : ℤ := (((YYTSparse[i]?.map fun r => r.entry j).getD 0) : ℤ)
set_option maxRecDepth 100000 in
private def OOTSparse : List OMA.Erdos1186Low.SparseRow := [
  ⟨6, 3, 0x23dc7a8f342203c06⟩,
  ⟨4, 2, 0xdef7ac1f06⟩,
  ⟨2, 3, 0x3bdf7a⟩,
  ⟨4, 3, 0x8f71e983b06⟩,
  ⟨33, 6, 0x117d39f10734dc937141a5068459d1661d6e45a99666582112143850a141b8b6f2cbcaf32a147d01e5875f1c2053613e04b811802aa092c1cd06⟩,
  ⟨33, 6, 0xd7d19f0e7341c907141a5068359cd66316e45a91664581514844590e142850442e84b612c84adb2a2c7d61e6c7661c3453e13a44a9114428d09⟩,
  ⟨86, 24, 0x481000003800000077f0000047e0000277b0000227a00002f7900000778000035770000307600000475000011700000116f0000196e935a9f6d00002e6c0000056b00001c6500002064000027630000326200000461000003600000035f0000035e0000055d0000085c00001257000013560000145500001454000047530000085200000351000003500000034f0000034e0000034d0000034c0000034b0000034a00000349000003480000034700000346000011400000113f0000143e0000113d014f1f3c00000a3b0000043a000003390000033800000337000003360000033500000334000003330000033200000331000003300000032f00001129000011280000122700001a2600000425000003240000032300000322000003210000032000000b1b00000b1a00000c1900000c1800000417000003160000031500000d1000000d0f00000c0e0000030d0000030c0000030b⟩,
  ⟨87, 20, 0x4810000380000077f000047e000217b000227a0003e7900007780002577000447600004750000e700000e6f000136e0058d6d0004a6c000056b000096a000146500016640001c630002d6200005610000360000035f000035e000055d0000a5c0000f570000f560000f550000f540004d53000085200003510000350000034f000034e000034d000034c000034b000034a00003490000348000034700003460000d400000d3f0000f3e0000e3de8ece3c0000a3b000043a0000339000033800003370000336000033500003340000333000033200003310000330000032f0000e290000e280000e270001426000042500004240000323000032200003210000320000091b000091a0000a190000a180000317000031600003150000a100000a0f000090e000030d000030c000030b⟩,
  ⟨33, 21, 0x481000163d8000ede800018ee00052760000fba000075b621458d8000076b00006b200003d8c00038c4000095700004ab0000255400012a80001c53000052900002100000107e000093e000041e800048f00001a76000053a0000414800020a0000124e0000b26000021280001090000082e0000316⟩,
  ⟨30, 12, 0x77b0127801177030700306f01b6e0086d01a650126400f6300562059570c8560cf550ce541a1401a23f09c3e0143d44329448288c527010260381b0381a0401904218056100560f03e0e⟩,
  ⟨27, 6, 0x317b99e917839c0e6f31b866d3194a64258d0573d58f553d5124048fd03e54a55284c9dc1b70698195c61510543d40e⟩,
  ⟨3, 7, 0xbdee13d4b79⟩,
  ⟨2, 3, 0x23dc7a⟩,
  ⟨1, 6, 0x2379⟩,
  ⟨29, 6, 0xf7d35f0f734dc937149a5268499d2661d6e15a81660582511b43850a1418cb632c90aea2a107cd1e447581c1851c13d04b411⟩,
  ⟨29, 7, 0x137d1ef851ccdb91b7130d261a0bb3976610b6c969b2cb6581488950d7a12f41625ac4b1915c02a083e3878a0e9e1c0c28944f0896111⟩,
  ⟨29, 7, 0x127d1ef851ccdb91b7130d261a0bb3976610b6c569b2cb6581488950d7a12f41625ac4b1915c02a083e3878a0e9e1c0c28944f0896111⟩,
  ⟨28, 7, 0x24f63de96bc0e7746e08dbcb37076d24ca39905b1846274aed959c2ab854b48168fe59f0d3de653cca32138826bc37786b00cde18⟩,
  ⟨28, 7, 0x24f63de96bc0e7746e08dbcb37076d24ca39905b1846274aed959c2ab854b48168fe59f0d3de653cca32138826bc37786b00cde18⟩,
  ⟨28, 6, 0x65ed37a69e0c7759c166f3db866d3994c64298c462715dc567155c54910243f88f8b3d8ca63288c9c726ac6eb1a9066418⟩,
  ⟨28, 24, 0x94c9117b0296987a00001f790000087800000677000007700000076f0000066e0000036d0000066500000564000005630000026200000757000007560000075500000754000007400000073f0000063e0000043d0000072900000728000007270000071b0000071a0000061900000618⟩,
  ⟨3, 20, 0x2c7b000497afe5a179⟩,
  ⟨2, 3, 0x2bdd7a⟩,
  ⟨1, 4, 0x97a⟩,
  ⟨25, 7, 0x117d20f84dcccb9197130d261a0ab3956610b6e169dacbb581688990da2134417c5af8b2015ca2a083e347890e9c1c⟩,
  ⟨25, 7, 0x117d1ef84dcccb9197130d261a0ab3956610b6e169e2cbc581688990da2134417c5afcb2095cb2a083e347890e9b1c⟩,
  ⟨25, 7, 0x117d1af84dccc3918712cd259a0ab3956610b6e56a0acc15814889d0d8213041985b30b2815d22a083e387898e9d1c⟩,
  ⟨25, 7, 0x117d1af84dccc3918712cd259a0ab3956610b6e56a0acc15814889d0d8213041985b34b2815d22a083e387898e9d1c⟩,
  ⟨26, 5, 0x3af757a63cdde18ef1708b7b9b8cdad655b2258c8c5757b2b5956ca8253da06cffa7ca3dd14e8a364e726⟩,
  ⟨25, 6, 0x217b5de8e7945e0a7739c0e6f31b856d2d94964218c362415d0564555154490123f4cf883d48a5228489c626⟩,
  ⟨25, 6, 0x277b71e90793de09772dc0b6f29b856d29948641d8c362355cd563554d543500d3f38f873d38a4e28389c526⟩,
  ⟨23, 6, 0x347bb5e9c7915e047711c046f11b826d11943640d8c4571158455115044010fc43e0cf442910a0427⟩,
  ⟨2, 3, 0x23dd7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 3, 0x2bdd7a⟩,
  ⟨2, 4, 0x87ba7a⟩,
  ⟨19, 4, 0x77db7c77387287186986886786685a85985884384284182d82c82b82a⟩,
  ⟨21, 7, 0x247d46f885cd9b933716ed2dda1c33b86610b7856ba2cf4581a88ed0eda15b41945b2cb2695f22a⟩,
  ⟨21, 8, 0x257d237c21733672367139693a683d673d66085b705a865986580d444643764277415c2d5d2c612ba12a⟩,
  ⟨21, 8, 0x257d237c21733672367139693a683d673d66085b705a865986580d444643774277415c2d5d2c612ba12a⟩,
  ⟨20, 7, 0x24f63deac3c0f7776e0edbcdb7076d2eca41906318462a2af1d5a3aac754b88170fdd1f0c3d⟩,
  ⟨20, 8, 0x137b0f7ac8780f773870386f1b6e076d166510640c63046249573856385538544540453f2f3e0c3d⟩,
  ⟨21, 8, 0x147b107a0979d1780f773970396f1c6e076d176511640c63046249573856375537544340433f2e3e0c3d⟩,
  ⟨21, 8, 0x147b107a0979d2780f773970396f1c6e076d176511640d63046249573756375536544340433f2e3e0c3d⟩,
  ⟨3, 7, 0x121ee9bd1c79⟩,
  ⟨3, 4, 0x87b87aa79⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨1, 3, 0x57c⟩,
  ⟨15, 4, 0x87d87c973a72a71a69a68a67a66c5ad59d58a43c42c41⟩,
  ⟨17, 7, 0x207d2af86dcd2b9257148d291a12b3a56610b6e16a22cc4581488950d9213241⟩,
  ⟨17, 7, 0x217d40f889cd8b9317168d2d1a17b3af6610b7696bfacff581888d90e7a14f41⟩,
  ⟨17, 7, 0x217d40f889cd8b9317168d2d1a17b3af6610b7696bfacff581888d90e7a14f41⟩,
  ⟨16, 10, 0x45ec0e7ab39e01277175c05d6f08db8076d06d9412640358c046215d5c40560fd543f54⟩,
  ⟨16, 10, 0x45ec0e7ab3de01277175c05d6f08db8076d06d9412640358c046215d5c40560fd543f54⟩,
  ⟨17, 8, 0x147b0f7a0879a07810774f704f6f226e066d1d6513640d6304623b572f562e552e54⟩,
  ⟨15, 5, 0x45edef4879a3c35c1adeb6e236ad952c87636abb1598aac54⟩,
  ⟨3, 20, 0x9e4d17b8c4557a0001279⟩,
  ⟨3, 4, 0xb7bb7ad79⟩,
  ⟨2, 3, 0x23dc7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨3, 2, 0x37c9a266⟩,
  ⟨13, 7, 0x2f7d3ef88dcd8b9317174d2eda24b3c96610b7156ac2cd858⟩,
  ⟨13, 7, 0x2f7d40f88dcd8b9317176d2eda2533ca6610b7156acacd958⟩,
  ⟨13, 7, 0x2f7d40f88dcd939327178d2f5a2633cd6610b71d6ae2cdc58⟩,
  ⟨13, 8, 0x327d1a7c29733f723f71446946684e674e66085b685a9b599b58⟩,
  ⟨12, 11, 0x22f6039ea293c014770f6e01edbc11b70076d034ca0499006b180462⟩,
  ⟨12, 11, 0x22f6039ea2c3c014770f6e01edbc11b70076d034ca0499006b180462⟩,
  ⟨12, 16, 0x127b000e7a8d3d7800127700657000656f00236e00076d001b65001264000d63000462⟩,
  ⟨10, 5, 0x34f747a5bcc1e10e086f3b71d94cc8563⟩,
  ⟨3, 3, 0x11ee3d479⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨9, 4, 0x57dc7c473472471469468467466⟩,
  ⟨9, 5, 0x107db3e31cdce4e716b4b5a1ccee66⟩,
  ⟨9, 5, 0x177dd3e45ce6e5371934c9a26cf366⟩,
  ⟨9, 6, 0x207da5f187375c9d7175a5c68759dd66⟩,
  ⟨8, 7, 0x16f625e9cbc1b77c2e185bd5b7076d⟩,
  ⟨8, 7, 0x16f625e9cbc1b77c2e185bd5b7076d⟩,
  ⟨8, 7, 0x18f629ea23c1777c4e189bd237066d⟩,
  ⟨8, 7, 0x18f629ea33c1777c0e181bd237066d⟩,
  ⟨2, 3, 0x23db7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨5, 4, 0x87dd7c673672671⟩,
  ⟨5, 6, 0x367dfdf1c7391ca471⟩,
  ⟨5, 7, 0x387d52f8d9cf1b96371⟩,
  ⟨5, 7, 0x387d52f8d9cf1b96371⟩,
  ⟨4, 7, 0x1af62deaa3c1577⟩,
  ⟨4, 7, 0x1af62deaa3c1577⟩,
  ⟨4, 7, 0x18f625ea5bc1377⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨2, 2, 0xdef7a⟩,
  ⟨1, 2, 0x37a⟩,
  ⟨2, 6, 0x81f517c⟩,
  ⟨2, 6, 0xa9f4d7c⟩,
  ⟨0, 1, 0⟩,
  ⟨4, 4, 0x48138037eb7d⟩,
  ⟨4, 4, 0x48138037ed7d⟩,
  ⟨1, 1, 0x17f⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 1, 0⟩,
  ⟨0, 1, 0⟩
]
set_option maxRecDepth 100000 in
def OOT (i j : ℕ) : ℤ := (((OOTSparse[i]?.map fun r => r.entry j).getD 0) : ℤ)
set_option maxRecDepth 100000 in
private def YOTSparse : List OMA.Erdos1186Low.SparseRow := [
  ⟨37, 27, 0x13810000028ee0000041d800000a3600000116b00000b2d2000006d740000452e00000b25b0000192b40000189640000312c000001253000001aa400000611c159580236330640453b35ea888c6abcf10c41db80a1083e41a4100000247c0000060f41ca1229e000000e3b00000905e0000080b800007d1680000f22c00001a65600001cca800001093000000f25000001e2c0000080540000310513a5da700⟩,
  ⟨45, 26, 0xca810000309fc00012d770000255d80000d26d000030db00000846b00002d1740001c95c00005216c0000d85700003c9580000f95500003ed500000c05300002014800007a4700003951abaf6b945198e83d10000138430000485000001213f0000644f800027b3d2426244f00000973b00001a4e80000ad2f0000348b80000dd290000374a00000f92700005ac980000e22500001bc900000771600002a0540000670b0000348280000fe080352d7c140000bf0211f9d40040000f800⟩,
  ⟨10, 23, 0x73e0000072a00000c380000184c0000389000007110000c6100001301c000528347e6e102⟩,
  ⟨2, 23, 0x228447e6e503⟩,
  ⟨30, 24, 0x317b0000207a00000e7900004578000015700000156f00000f6e0000066d00000e6500000c6400000a630000165700001556000015550000155400001a4000001a3f0000183e00001b2900001b2800001a270000461b0000461a0000241900002318000022100000220f00001d0e7720ad05bede5e04⟩,
  ⟨6, 23, 0x243d80002f7a00003cf200000db800001a061498205⟩,
  ⟨5, 25, 0x37b000001bd0000bd421e085140f50ff6506⟩,
  ⟨6, 25, 0x6f60000037a0000023ca839da822fbe9c60e00006d06⟩,
  ⟨5, 25, 0x37b000001bd5f419e0200000400e00001806⟩,
  ⟨27, 24, 0x77d0000107c000006730000067200000671000006690000066800000767000007660000065a000006590000065800000642000006410000062c0000062b0000062a0000051e0000051d0000061c000006130000071200000711b976200900000b0800000f0700001206⟩,
  ⟨33, 25, 0x117d00000abe000003dcc00002ae400001571000009348000049a0000024ce000012660000042d80000b56800005eb200002f58000005a200000b90c0000568400002b41000026968000134b000009e560000932a0000020f800004c780000363a0000271c0000040a00000f84c00028a2400014611dd25fb0525c16a42400001c0e00001406⟩,
  ⟨37, 26, 0xf7d0000021f000000b730000031c800000c71000002da400000b68000002d9c00000b66000003d6c0000155a000005d640000175800000351400000b4400000490c00001342000004d0400000c2e0000064b40000192c0000064ac0000182a077ad3c7c4798a81e238b77c741489961c8e4b76c500001691300000c4480000311111f9ba02c0000570a000002c240000ab0812aa5e41c445d5906⟩,
  ⟨30, 26, 0x5de0000024700000091bc0000276500000759000001e630000075880000295700000791800002a4000000a8fc00001d2f00000a0b80000282500000a09007d7ae1f00000dc7800002e1d000009c7000009d1700000b058c348f31500005a0500000321393b022c3447e7220c33f6b4c2cce30b1071f520f81800001903⟩,
  ⟨9, 25, 0x6da3081b1b6d480d073f95864a91958300000720e23f37f06c4db66820b47f0c0e00005106⟩,
  ⟨33, 25, 0x127b0000073d000051de000001aee00002270000011378000055b800000cda00001265000006b200000298c000008c400003b5700001c2b00000e554000070a800006c400000361f8000170f800001c7a0000ad290000569400002949c6e2e32361b91331a10d8d18c91fff306047a90820237e170f993cc78700000242030e5e60a0000d404⟩,
  ⟨33, 25, 0x107b000006bd00004f9e000001cee00002c70000016378000059b800000cda00001265000006b2000002d8c000008c400004957000020ab000010954000084a80000bc4000005e1f80001e0f800001e7a0000b62900005b1400002f89c0000124c0004041b0002018d0000b34640005d631572ce010cd4f280780001c4380001b00a00007004⟩,
  ⟨33, 25, 0x107b000006bd00004f1e000001cee00002c70000016378000059b800000cda00001265000006b2000002d8c000008c400004957000020ab000010954000082a80000bd4000005e9f80001e0f800001e7a0000b62900005b1400002f89c0000124c0003f51b0001fa0d0000b38640005da319b00741004598a8780001c4380001ae0a00007004⟩,
  ⟨34, 25, 0x34fa0000187c00000a398000075c800003ae200001c6900000e3400000759c00003acc0000085b00001e2d000013164000098b000000b440000152180000ed08000076820000442d000022160000120ac0000f0540000041f0000088f000006474000054380000071400001e8987c3d4c4ada27762200001d0a092dcd848000024200000220e00001706⟩,
  ⟨34, 25, 0x34fa0000187c00000a398000075c800003ae200001c6900000e3400000759c00003acc0000085b00001e2d000013164000098b000000b440000152180000ed08000076820000442d000022160000120ac0000f0540000041f0000088f000006474000054380000071400001e89db49ea44adc715e2200001d0a092b23048000024200000220e00001706⟩,
  ⟨34, 25, 0x34fa0000187c000009b9800006dc8000036e20000196900000cb400000659c000032cc0000085b000018ad000010164000082b000000944000014a180000c1080000608200003e2d00001f160000104ac0000d2540000051f00000b0f0000094740000ae38000008148353f589b3cbf34499e88c4220000210a020bba84800002c200000280e00002106⟩,
  ⟨35, 25, 0xedf400001cf80000177300000fb9000007dc400003cd200001e6800001233800009198000014b60000495a0000322c80001956000001e880000434300001c2100000e1040000065c0000642d0000329600001c4ac00069c5400000a1f1077098f114a3187400039c38652332149fcced899ce907c48e742da2200004d0a438fd5048000058200000b80e4fc16f06⟩,
  ⟨48, 26, 0xdf800000a7d0000021cc000009720000025c40000036b000000da8000008690000021a0000008670000021980000035d00000117000000d5b00000316800000c5900000316000000447000002d1800001c45000002d1000000c43000002d0800000b410000024bc0000412e0000034b400000d2c0000034ac00000d2a0000014802f060b1f00000987800001e1d0000054700000051697b085054983aef14000004c4c00000e12000003845a3698f0b0000054289be14b08227befc1c126a780600000140800000300⟩,
  ⟨13, 26, 0x13460000048f00000162700000749800002125708a6585c47e6f41694660cc555774360d131fde82c8eecff0800004041c00004706⟩,
  ⟨29, 23, 0x2370000046de000055b8000053680001565000024c80000cd5c00017ab00002f5500005ea800013500000269f80002b3e0000367a000250a40004a1400005e270000584c0002306c000da0c800195188fcdce2e000174400002e878000c80e00003c1a0000f4200000f0380001506⟩,
  ⟨33, 25, 0x107b000006bd0b878f9e0000018ee00002470000012378000051b800000cda000011650000063200000298c000008c4000037570000182b00000c554000062a800006b400000359f80000fcf800001c7a00006a2900003514000018c9c0000104d27eb6d1b49c06e8d20db838675350c2300000b71000005b87800013438a534580a00005604⟩,
  ⟨29, 24, 0x107b00000d7a0000097916c4e678000024700000246f0000146e0000116500000c6400000a6300003657000030560000305500003054000068400000683f00003e3e000067290000672800006027587a631b2c96261ac9d3ad19001742180000b0100000af0f00004c0e1817170500005504⟩,
  ⟨28, 24, 0x137b0000107a08321c7800001d7000001d6f0000116e00000f6500000c640000096300002657000023560000235500002354000035400000353f0000283e000036290000362800003427992bee1bb6a6f71a0000801900007d1800004c1000004c0f00002f0e2707e2050000a904⟩,
  ⟨32, 25, 0x9bd8000041e820cf04f000000b7700000eb80000075bc000022dc0000066d000007b2800003190000012c6000003620000132b800008d58000046aa0000235400001aa000000d4fc0000507c00000c3d00001b1480000d8a00000684f4ee6211b14bf138d0000200640000fa3000004c100000260780000bc389c054e0a0000a904⟩,
  ⟨33, 24, 0x177d0000117c000011730000157200001571000015690000156800001467000014660000245a00002b5900002b580000094400001d43000021420000214100002b2d00002b2c00002a2b0000382a0000051f00001a1e0000321da9a6fc1c0000081400006b130000c1120000c11100001b0a0000df0900000d080000200700005d06⟩,
  ⟨34, 24, 0x1e7d0000107c000011730000167200001671000015690000156800001767000017660000085b0000255a00002f5900002f580000094400002143000023420000234100002f2d00002f2c00002e2b0000562a0000051f0000371e4b297f1d9101a01c00000a140000cd1300247d12002430110000230a06f64e0900000e0800002d0711f37406⟩,
  ⟨34, 23, 0x10be80000e7c000024e600005dc80000bb88000166900002ad00000619c0000c330000085b000054b40000d9640001b2c00000a44000048860000910800012208000342d000068580000d0ac00035950000061f8fce823da49f00764d7fd8e00000d140001d0260035b4480067f888000270a0252f61200003c2000019838f87d306⟩,
  ⟨34, 25, 0x4cfa00000b7c000009b9800005dc800002ee20000166900000b34000005d9c00002ecc00000a5b0000222d0000165640000b2b000000b440000142180000b90800005c820000032e000022968000118b000009e560000632a23f3780fa8f40307a8dc81c3bde32841c00001f0a1c6ede04c5a73e0242d50981100001305000008c240001a00e8bb27f06⟩,
  ⟨14, 27, 0x1197047e6e7209cc86563e3bf86c078efbf938e9f8bd361c0ebcc9a281ab97784c0000d18900001a211000002c16000015420417d6d839edfbc506⟩,
  ⟨18, 26, 0xc2b5180009f62f0ef535cb8002cde2511fdca0878a81e8202472c707c012fda1e150cbf074000c091c00126045c0009c3162a432285426bd28142fd835834000c1e0c00090902c00245206⟩,
  ⟨16, 26, 0x1a33ab1e0002039650003db14c121d2a52d453e58f0000be1370004c5c9047f4c8220000060800007291a000283460001066170aa5fcc504ec3e41300014a038000b820d⟩,
  ⟨29, 26, 0x1e75227d0507909940bef646403493798c51b90f5410fc5954c42943c524fcaca0f60afaf33c07bf9f8ec2081ce37019c410bc0aca6b2902d8034a0149ce4270d23934981d4b6f2525c28e09058b1ea2307e8d508812334e21020e4347c5e3c21180806a185c1a690b150a322144c22ba981008cd214384106a60d⟩,
  ⟨35, 27, 0x89dc00001c3800000386f0000058dc0000069b40001202b800023b5600004eeaa00009e15000000ca9800000c5237456c0806e97ce8fcc782fc9f1f90a5b3d54c4f00780000038ec64f562948c9d7402818895724f18585689919e03312847e6f62400000ce36000019c681599fd8c896e7ea180d2f0322e000002c5800000b8a8000626100000c7a1e00007443883246f0680000110b⟩,
  ⟨79, 27, 0xe040000014000000047f000001ef0000005ddc000001bb000002770000004ede0000055b8000008b680000036c0000004d6000004d94000009320000011630000016c40000009840000013000000025f0000004bc00000097400006d2b80001555600002c6aa00005c150000004a98000003520000004a20000009400000012780000024e00000049a0000009300000012580000024a0000004920000009200000012383676564006cc0627e106dd48f83cbe829e8fa02eb3c0000006760000008e80000011c80000023800000046e0000008d80000011a8000002340000004660000008c8000001188000002301d1caf6523a326cca09d740d93fa7b6612608fcdd64a000000c900000011180000022200000044200002786c00004e8d02bf243190db25963000000305c0000018b00000041500004202000008643c0000cb0700000130d000004a08000000c0c00000100800000200⟩,
  ⟨34, 27, 0x43d8000064780000038ee0000249c00000493780000226e0000010da000007d94000009b2000000e63000000ac4000040d5c000075ab00000eb5500001cea800000094c000c8ba000019a63f000013a7c0000070f40000029e41322e629824e0c4510db147c9c23f3789300000531b00000a6340000204640000428c00000661000000cc1e00000c03800000902800002804⟩,
  ⟨34, 25, 0x1ef600000d7a0000293c0000051dc0000b8e000005c6f00000fb7000001db4000032ca00001064000006b1800001188000162ae0000ba5600005baa80002cd50000004a6000182400000c11f80001e4f800001c7b381c4c299bf3b9142a375309c0000124c00004d1b0000268d000014c640000a8300000591000002c8780000c03800003e0a00002b04⟩,
  ⟨34, 25, 0x20f600000d7a0000273c000004ddc0000bce000005e6f000010b7000001db4000032ca00001164000006b1800001188000138ae000089560000442a800021950000004a60000b0400000581f800016cf800001c7b6392a1297ce8c61400006109c0000124c0000441b0000220d00001206400009030000047100000238780000ac380000360a00002904⟩,
  ⟨33, 24, 0x107b00000d7a00004e780000137700005e7000005e6f0000216e0000076d000019650000116400000d630000046200009c570000895600008855000086540000b0400000b03f00005b3e00000e3df99c3d2914c0c22800018327000009260000441b0000441a0000481900004818000047100000470f00002b0e00001b0500002904⟩,
  ⟨34, 26, 0x85f400001e7c000007dcc0000317200000c5c400002f6900000bda00000306700000c1980000095b000029d680001045900004116000000e4400001a10c00009742000025d040000d82d0000374b00000f42bb2ab384a80000041f0000040780000151d000007c700000071400000b84c00010212000040c4400001e0a0000698240000090800000341c00001106⟩,
  ⟨34, 25, 0x48fa00001a7c0000123980000e5c8000072e20000356900001ab400000d99c00006ccc0000095b000151ad000352d64001a92b000000e44000046a180004950800024a8200076b2d00049816785ed14af81b92c540000041f0000070f000004c7400003a38000007140000158980002f04800017a2200001d0a00003a848000020200000180e00000f06⟩,
  ⟨33, 25, 0x237d00000dbe0000095cc000076e400003b7100001bb480000dda000006cce00003766000004ad8000d7968060ea0b202f9775800000722000025d0c0002788400013c4100134496ee4b258b2c3c03e56f7254c2a0000020f800003c780000263a00001e1c0000038a00000a84c000166240000b41100000e8500001d4240000180e00000f06⟩,
  ⟨33, 26, 0x237d000006df00000257300000edc800003b7100000dda40000376800000dd9c0000376600000256c00034d5a0856f656421193558000003d100000994300004f90800013e41b0db920b6858fda2ca4943d0addecebe2a00000107c00000f1e000004c7400001e1c000001c5000002a1300002c8480000b3110000074280000750900000301c00000f06⟩,
  ⟨34, 27, 0x11be800000b7c0000038e600000a9c800001538800002b690000056d0000008d9c000011b300000165b0000292b411c679164237aa1ac000000945000004488000020d0c000043a100000874108fcdca5d17d4590b4eab745960f8db852b04893325400000407c0000528f00000981d0000b68380000174500000b68982763d01204eb82422000018c2800000f04800001108⟩,
  ⟨37, 28, 0x1d7d000002973000003c72000003c71000003169000003168000002167000002166000000a5c0625bbd5b00f460e5a03b129d5903afbca5800000844602a0beb4500000d144000013743000048842000048941047e7312f9c9fbc52e2a7b2382d117908f2c0a205412b056ad612a00008a61f00001611e00003bd1d00001dc1c000005815023ead214036184413073881a120738a9a1100000330b00000f40a000003006⟩,
  ⟨27, 28, 0x5e65b000215e5a0027e8959002884d5801a9ed4460b0c674450000370440001d9b420001d9841047e7b6306331dd12fcf42ebf2e419cdea2d187347b2c091efe52b1379e5c2a00005941f00013191e00004331d00002521c000048015000066f140000671130002ff6120002ff81100003580b0000f240a⟩,
  ⟨19, 25, 0x171d69901faa6ec60d011e5bdd8830a90ee2b6d4426222a8850ef7d319691939802bba00bd26c3445c09606a2810f29e8f8af144c78a40ca63a29463e1c0429488b0229ca8541dc6ec1608baf300⟩,
  ⟨34, 26, 0x10acb19f04fd74464112755d8c3988d4621a66f2984457d72601509591744f6b735913a4559604b63585320ff84d48be415451169a221313db0974b11be4c510a26631360ab7310d480ca7e329bb0d84c0226d802f3a1123cb8b53a3d2d19bc858b05a3773220f7f094858f1493203ca90e07c43e7d31e1acf9cc74aaaf241c0ca6a486c381def1a11965846430201004⟩,
  ⟨25, 24, 0x27d0b3641d953a6326d58e5b605b7c52a250654c9e10e64b134fcd446a3c0d361cfc3335643866331372fb32943dc9300c1a062f40d0de2e15dfea29184e7c282b6cdb2231a97d21a73a532047de8c1f36aebb1e6e12491d2e7f0d1c16704b1a164da904⟩,
  ⟨25, 27, 0xec78770015f1cc80473eed8c242b26b083f821f600053f04be43a4ed1740180a52988fd45552000268c991c69c38d9bfe7811a8497c7c343b8287060196a274bc007701170063f522200843ee42677a8c480e993500f88530dd1e17167563a00299945026303f89801082b0a⟩,
  ⟨21, 26, 0x10037d0006171d80016d56400120318c09652c6220103e184000e1858001304d4c00bc4652230e1d0dfa64a2c362a21ac0d40013de2e0006778893c00772052a24787c2d4ae6140004a384c002a1e0b00060a02800173809⟩,
  ⟨22, 26, 0xc433599400013d63000049189070363557023439500003d95305fb3e548d999ef3d0002130ecf8dfcf3711fadb8d8000a91290002a48a0002f2427000107098000d2a250025a1c93627c81200006760600004c0171d003ec380001e80d⟩,
  ⟨43, 26, 0x3e078100016c59400039a5600029e554000c195400008214c0000d45200001c944000195450000b85000002e03f0000768f80889093d0000228f00006193b000023ce80000fc389722548dc0000aa3600001a8d40002392900008e4a000052d270000904983dc745252d8b54c9000007c2200001b084b30ba72000007206c0001c71a08f59386476c8a5180000fec5c00017516000035c540001d71000007683cb2f9350e00002f0340000da0c00004442c00009f03⟩,
  ⟨52, 26, 0x6b8c4a040000527e0000121d8000058750000281d00000fb7300006e1c80001b8710000301b000009d6b00002b5a80000485c000030d6c0000af5700004c5580001795500006215000019a531d354d548000049510000219140000f54000003d4fc0000ce3e000027cf0710c1b3b26a0d78e800004439b085728e000007037000011cd800012d2900004b4a0000175270000350981b07be2500134dc9000004822000011484000083200000a606c00029a1a00012ac640003d018000032c5c000061160000138540000ec1000003b03c0003600e000015c3000005200⟩,
  ⟨33, 24, 0x1e6d9e810013887c0b7509751eb8677212033d6d6599fc6c0ce2136b18e9aa691e6c605b09f92a5a1e262c5735405156330da1553ca99a542b5f605333ea26520cdb1f3e0889063d1aeba43c640eb73b5fe3803a6b0bca3982d2d738123543291263db281ae6092711e40e261cfa86255aa19d241fce641b1b2d361a14bb9a192445fd0f⟩,
  ⟨41, 26, 0x1d8100007c1dc00005d760000095d00000bf7000002fdbc00008f6e00005ddb44013d96c0000061ac00001f6a0000129940000686400001a18c0000b762000005170e04a1a575fd7569590898ad556ad9f3951052ac2530199ded4800039e400000e78fc0000f63e000012cf40004ea3c9045c04ec47e7023a000062ca400018b2800006909c0000db260000090940000182400001906c0000641a00001a06400006618000015c400000570f⟩,
  ⟨54, 26, 0x160400000480000001dfc0000087800002fddc00001b7600008f5c000023d6f0000989b929ed836d0000099b00000066b2a72ac994ad3561641467f558cd27995620000019840000045f2b887115cb4b9bb56252173d54e3a2925415ecf0d4c00001652000001144000004490624859001864c33f1cf36d8f80001503db9253e8f047e71c3b0000014e8000004380000010dc27d8ba2909f3898a04995ad27000089498000009250000014900000231b000008c6800002f1900000bc60000007170000010580000371000000dc3c0000250e0000018340000240400000100c00000401⟩,
  ⟨46, 27, 0xc080000027f0217cb6f02b90b25dc0000013b00000fe7000001fcde00000b5b8000007b680000016c000003aca00000599000000a318000006620000002c2875641d5cdd5eb2ab16611f9554d7c30ea800000114c000000a90da2038401b414e47f3d7c2b8f8fe691a9eba31db33c0000002760000004e830d43094861aff22811c71e64e3daeac4980000009280000012400000ac360000158680000500c80000a71800000042e00002484000004907800002d0e00000041a00000341400001782000000103⟩,
  ⟨35, 27, 0x3dec000006bd000004678000002cee0000111c00000223780000166e000000eda000005994000007b2000000c630000008c400005955c0000962b0000105550000208a800000094c656b4e200cb09373f983346c7c11f9df0f40000021e0444e7129088fa6c50071ce209c0000069300001391b00002723405a32d0640dfc870c00001a110000033e1e000011c3800001602800003804⟩,
  ⟨35, 25, 0x45ec00001af400006a7800000cbb8000185c00000c2de0000226e000003b6800006994000024c800000d63000002310000d515c00027aac000148550000a32a00000094ed3ab5e8169e1ea3fb68a5e9f0000040f40000067800251529001247941b53fe89c0000124c00005f1b00002f8d00001a8640000d6300000a6100000530780000e43800006e0a00003504⟩,
  ⟨33, 26, 0xe7b0000031e8000063780000051dc00006d7000001b5bc0000216e0000019b40000186500000419000000c630000011880000d85700002b9580000a855000029551ad6352408624468fc0000933e0000038f400025e290000974a000036e2700000249800005b1b000016c6800006619000019c600000661000001983c00002c0e00000c41400002d04⟩,
  ⟨33, 26, 0xe7b0000031e8000063780000051dc00006d7000001b5bc0000216e0000019b40000186500000419000000c630000011880000d85700002b9580000a855000029552186a6340177ae34fc0000933e0000038f400025e290000978a000036e2700000249800005b1b000016c6800006619000019c600000661000001983c00002c0e00000c41400002d04⟩,
  ⟨34, 26, 0xb1f400002f7c00000bdcc0000687200001a1c400006369000018da0000056670000159980000095b0000f75680002d2590000b4d6000000f4400002b10c6d421d42821aa15040000b42d00002dcb00000bd2b0000390a80000041f0000030780000101d000005c700000061400000844c00006312000018c440000150a0000188240000080800000301c00000e06⟩,
  ⟨34, 26, 0xb1f400002f7c00000bdcc0000687200001a1c400006369000018da0000056670000159980000095b0000f75680002d2590000b4d6000000f4400002b10e08920f426f267b5040000b42d00002dcb00000bd2b0000390a80000041f0000030780000101d000005c700000061400000844c00006312000018c440000150a0000188240000080800000301c00000e06⟩,
  ⟨33, 25, 0x337d00001bbe00000f1cc00013ae400009d7100003434800019da00000b2ce00005966000004ad9b216496808eaa6b204c8f958000008225b533750ef3e0968579f2bb410000a0168000510b0000282560002762a0000020f8000034780000223a0000191c0000038a000008c4c0000b62400005b1100000c8500001b4240000180e00001006⟩,
  ⟨34, 27, 0x1abe800002a7c0000096e600003f5c800007eb881b38f66902c7874d000004059c00008133000000d5b02e4e8ab41088d016421031f2c047e7b2449b9756c862fde6d5085fb99ca080000022e000027e5a00004f8b00000ae15800017d2a00000083e0000030780000070e80000151c000000e2800000584c00001f89000003f11000002c1400001142400000683800000f06⟩,
  ⟨41, 27, 0x2e7d000001af80000009d0000018b980000ad72000015ae20000009a8000054b480000a16800000a2ce000014598000000ae0f9437c5b11ba406b416d8435642dbab22c00000014673ec4848a7ec1451126ed261218d5eac7421abed6a820000004bc00000217256787a2d2af25f8587145b90ad149a8c9500000061f00000283c00000587400000e0e000000115000001e2800000b44c00006c8900000d9110000004162a4fc542807474384800000202⟩,
  ⟨45, 26, 0x47e0000089f4000006740000095cc00003c7200000f5c40000076a00000b9a400002e6800000859c000021660000015740000095c000097d6c49184c5a077cd05641e06d25800000151c47e71f46b9385a5140001e34416e83e90c0be68a4202fa951040000172f1950058b8e313fe2d25678c4b0ad1f7c2b319d1bca800000620341eee07c5341e91e2b29d0074aaf2fd1c00000985520875e140000b004c000331120000cc44400001b0b00002882800000809000001c0800000500⟩,
  ⟨23, 26, 0x245c00002ed6c0001885a00006716400019b5811f9c091e495948460000f35140000e7430000a8d080002a3410001680bd081f712e643e460b50dbc7a2c677840cacf130922a00002707c45b763150000a1c500000c61200001682c0002770a⟩,
  ⟨30, 24, 0x20ca04721450fb681a3c39671f26f566357b595d1abf555c1213145b16b0a45a9197d149637cfd48521f1247640c6c46247843450874da440d0285433a7cf02f334d882e50052d2d43a47f2c4ad7d32b099d04271b4ddb261391b71813147d164232c9151028c814196d321018ece50f2155b50e27cc9700⟩,
  ⟨45, 26, 0x2be730000139b00000686b0000275a8000442690001351a00003d4670000f359800007161000011d7c0045175d01eb545700000fa5b00006216800015d5900005756000006e4aab7056d240000434829675191c88b44746000036d1400008b40000022cfc00008d3e00001d4f08c21192f000105cb800018a2d00005ecb000013d2b00001f09c0000a8260000318600000a41700002f0580000be150000650400001910f00003d8380000910d000013c3000004d0b00001640c150bfd00⟩,
  ⟨25, 26, 0x1237628dcf79cc0000db6c000075dac0002ed6a1a0011da41f55956800006ad98bb6ae76131b5d51744473b95c0000a056c0000ae4b9284905280001014900017411800008a450015e9d100001863c0000324bc0002762e0002bdcb40009622c0001070701a792100⟩,
  ⟨22, 26, 0x721d068b1df730001351a8001f8c69de020fd8400356c5d00021a9700004a65b00fbaf568000a495900029296047ebc84b35310e1280006344635355fd102c56eb2f0000e14b995733e2d39bd4c4b000011c1f00004ac784629191c⟩,
  ⟨24, 26, 0x4aede000157b7700078cdd8000fcf6e05a3efdb56575a6625301ecd8400147c5f0002e3978001def5d00061ed4c9a65444ce29b8d52c43a35e4a0387620bc0030b32e0003034a4661844200019b7c7c0169491e00055b4740020fa1c00052d02c000d6404⟩,
  ⟨24, 26, 0x78315dc63cc016e0048cf1b4939890641ddbd3d8d622dd66245582618404d0b66004246e97c022ab453155f64d492eda745112926f93758863e4cc7708b92cd0d1982f00b78f8b88586f024011cb9c882844b22101c23cc800dd7c91e008b31c74023c040a⟩,
  ⟨25, 24, 0x19c64b7d18c0b6673641926559df876431201063457ac162a18408612bfc97604719b25f1a7c725917f8d8583feba2530d91f052c7303b5113cdd44f636de44e200ef64c77a9484b16c7373d9f5c9a3693caa8355cdec42f251f6b26223a361e3ac0f91d⟩,
  ⟨30, 26, 0xf71639f458671f6812ea5799c426345662a07a15948b17c864129e8118d1925f9624ac4725844a551b6023382f57c5d08f7552c312c950d8cd2e530a6a8ed4a95f27a5126341913c361e044c435ed452c4e4fb13d424456cd8b1db072f19a60c8b85371ac2914be884a0618b5b2125829808055f7f61e17da0c0744932ad05⟩,
  ⟨21, 25, 0x9cf1d8104ae2b3602a3151ac60b4aeca493330641a59e93190a4e1588c86044c20ac7d15942bfd029830ff6d4a4f39b6a251fa125008dcbf1e90fe514c331fb6a5e1e49bd290fb68614038d47c981c47063c0b79c51d⟩,
  ⟨37, 28, 0x1158100018e67700003787600057997000058026f000051b6e00006696d00005276c00002706500003fa640000e2b63000070f6200001a4610f988a857099d5f65617e39b655404674954d4871d95366f812e52047e7a75100017b440000179f3f00007173e00002eb3d0cc10ae3c0213f963b00001273a0013739290012d9d280001c2c27000059f26000019225000011424000046b1a00003b319000050f18000047e0f⟩,
  ⟨40, 28, 0x68100000087f0000009780000180770000035760739117700738c566f031209e6e01cbf4c6d00000636c000068a650008b966400001a963000038d6207108c45709bafc456110e593552a050f7549d81e5e53047e73b5200005014000005033f00001383e00000a53d02d84573c00000833b0329f7029032b1852800c34cd2705a361e26000000a2500000221b00000221a00000321900000321800000081700000341000000340f00000280e000001d04⟩,
  ⟨36, 27, 0x4fe0000045e400000fbc0000067770000004ec132d945c0265a9db7800019d6e00000deda007bad99400004d3200000c7630000022c40ef9b995c7fc995ab1c2b4e75589b48aaa811f9b954c000045a0000008b3f00001167c0000084f40000049e03692c42906d77565000005b09c00000a9300000251b000004a3400000ac640000158c00000281000000501e00000703800000582800002704⟩,
  ⟨35, 26, 0xf7b0000031e8000078780000071dc0000c6700000319bc00002a6e000001db400001f65000004d9000000e63000001189d61c0e57a8a26295a7edc7e55afc0955500000025300005f50000017d3f000026cf800000e3d000000cf02bf4e2290af5e2ca0000592270000024980000391b00000e4680000391900000e46000003d1000000f43c0000240e00000701400002404⟩,
  ⟨34, 25, 0x1ef600000c7a00003c3c0000071dc000190e00000c76f00001537000001db400003eca0000136400000731800001189b1663caf6c88a256e1a8e5aa800b64950000004a600017b400000bd9f8000264f800001c7a049c6529025b529400016d89c0000124c0000381b00001c0d00000e4640000723000003d1000001e878000090380000380a00002404⟩,
  ⟨34, 25, 0x1ef600000d7a00003a3c0000071dc0001aee00000d76f000015b7000001db400003eca000013640000073180000118bc677b4afcb551256000574aa800233550000004a6000167400000b39f800023cf800001c7a000cc0290006621400010589c0000124c0000381b00001c0d00000dc6400006e3000003b1000001d87800008c380000380a00002404⟩,
  ⟨33, 26, 0x127b0000039e80001d2780000075dc000110700000441bc00002d6e000001db40000206500000599000000f6300000118aca15bf570000391580000d355000033d500000a6400000298fc00006a3e0000034f4000108290000420a00000b2270000024980000331b00000cc680000321900000c8600000331000000cc3c00001f0e000007c1400002204⟩,
  ⟨34, 24, 0x287d00001b7c00002c730000477200004771000045690000456800004167000041660000095b00013a5a1581a859ff21055800000e44000060430000a7420000a74100008f2d0000912c0000942b0000a02a0000041f00000d1e0000111d0000191c000007140000211300005a1200005a110000140a00004d090000080800000d0700001006⟩,
  ⟨34, 25, 0x50fa00001b7c00001639800011dc800008ee200004569000022b400001059c000082cc0000095b00009dad3fe275d66c87854b000000e4400003021800029d0800014e8200008f2d000048960000250ac000140540000041f0000068f0000044740000323800000714000010898000168480000b4220000140a0000268480000202000001a0e00001006⟩,
  ⟨33, 25, 0x2b7d00000f3e00000c9cc0000b6e400005b71000028b48000141a0000094ce00004a66000004ada9ded256a6a4df0b336082e580000072200002290c00033a8400019d41000064168000334b00001a4560000c12a0000020f8000034780000203a0000181c0000038a00000804c0000b2240000591100000a85000014c240000180e00000f06⟩,
  ⟨35, 27, 0x9df40000093e00000347300000d8e400001b1c4000042b4800008168000009ace00001359823f378adc3d4e155a82a72a8b30556d7560000002a2800001c4400001528600355f5080064c32080000022e00001f05a00003f0b00000761580001002a000000a3e000003c780000098e800001d1c00000102800000844c00004109000008211000003a14000018c2400000403800000806⟩,
  ⟨45, 27, 0x37e0000048fa000004dd00001f139800026c7200004e0e2000000dac000005b506e79e06905612d8d000002719c00004e3300000035d08fcdd6b9e70e1e16c9eb9712d0e0b456591c19d28b000000091c000001a310142a0450f488f6880f715250c1b4a6e21036ae7f4100000065e0000024b80000bb96800016e2c00002e45600002f8a800000110000000b1f00000223c0000044740000090e00000031500000202800000584c0000130900000261100000061600000582800000201000000200⟩,
  ⟨23, 27, 0x41e5249d00000d7b980008047200010d8e20000059b03841f03509b60126905bc3d2d011f9bd9751aa36d2e4622ea05b187e840b434849ed646900232c2b28442453e8bdf288664e81d0cddc960211bb7cb04100005165a0000a50b00001539580001b12a⟩,
  ⟨32, 26, 0xef3d9dd0317c2f73078e791c44643c96e0c089b9b41d64d96c07f1a79a8557b456905da7c18c0600ad620424771801b44fb5f17556bd785c03925d054f3c5704217705b057371568108c9a590401dcd600759da52092335d2820f97e4682e3e09150e7806441112dd8bc35d8be2e1328254b40e0d6f1e0325954741542931c0006e48141f873504⟩,
  ⟨23, 26, 0x85a76000497dd00004b7730008039bc55af096e10c0969b40008626c0004205a800095a69072e5e98447f41e5f00034c5740006915c2558dd52800081a4900016791c000a7746e3c17bd1401e2df2f00039a4b800077e1c1d5492024000b5f05⟩,
  ⟨17, 26, 0x1dcb7b000a50dd8c7b00a74108eea5b4b7daeb6c0002e29ac00378d6a00039a994629820640008c798c86fa1362dedd7098447f8c66000080a170000060530001f09480037d63b⟩,
  ⟨13, 27, 0x1dd409b7b141cb1ef40000145e40000e13800001c26f0e6c9f8dc1d94ef9b5006f66329dd56b4641db3eeec7380f1958823f373b0800002253⟩,
  ⟨34, 25, 0xfcc130f60000f17a000012bc0000095dc4316ece02173276f377c81b7000010db7bb87becb4e9c0d6452f22e3191f9bc1880000b2ae000049560000212a800010550000006a600002f400000179f80000a0f80000167a00005d2900002e9400001189c0000124c0000181b00000c0d00000586400002c300000161000000b07800004c380000160a00002804⟩,
  ⟨33, 23, 0x1219ba7b000068f4001669e0000143b80067b70000d08de0004bdb800006b6c7a11e65cc4648c91f9cd58c00003310000755700006eac0000dd540001baa0000274000004e7e0000a0f8000051e80003d2900007a500000b89c00004130000191b00003234000058640000b8c000018100000301e00004c38000078280002204⟩,
  ⟨33, 24, 0xee4d67b00002d7a0898e878000024770033c2700035b36f0000f36e00000a6d93536b654bed44640000306300000562000059570000305600002f5500003054000025400000253f0000223e0000093d000031290000312800002727000008260000171b0000171a0000161900001618000016100000160f0000110e0000110500001f04⟩,
  ⟨34, 24, 0x557b00001f7a00000d790000ac7800001b770000c5700000c56f0000746e0000086da906556500003164000018630000056200003a5700002c5600002c5500002c54000023400000233f00001e3e00000a3d00002d2900002d2800002627000008260000151b0000151a0000151900001518000015100000150f0000110e0000120500001804⟩,
  ⟨33, 25, 0xac7d263c9ebe00000bdcc00008ee400004771000039b480001d5a052b8eacf4d5c0e66000018ad00000d164000068b000000c44000013a180000c908000064820000222d00001116000008cac00004a540000031f0000050f000002c7400001c380000061400000889800006c480000362200000b0a07cca7048000028200000200e00001306⟩,
  ⟨30, 24, 0xac7d263ee07c00002f7300004772000047710000736900007568b5fa6f679909dc660000315a00003459000034580000274300003242000032410000222d0000222c0000222b0000252a00000a1e00000b1d00000e1c000006140000111300001b1200001b1107cc0d0900000a080000100700001306⟩,
  ⟨30, 24, 0x567d196b007c000050730000b9720000b9710015d169c72d1b682d32946759d3776600005b5a00006659000066580000414300006442000064410000312d0000312c0000302b0000352a00000a1e00000c1d0000101c0000061400001413000023120000231116ad1b090000090800000d0700001006⟩,
  ⟨33, 25, 0x577d2affdfbe0000149cc000182e40000c271d3e6a8b4a107ef1a125c984cf2699506600002f2d00001a1640000d2b000000f4400002121800019d080000ce820000312d0000189600000c4ac00006c540000041f0000050f000003074000020380000061400000a09800008c480000462200000c0a169e2f0480000242000001a0e00001006⟩,
  ⟨26, 23, 0xa3d80001e7a000070f2000071d000066b9800069720000d2e31f9b9da8000aeb4800177680000fccc00016d68000462c80008c5800005a860001390800027208000322d000064580000c8ac0001a150000121d00002c380000584c000120900002411⟩,
  ⟨9, 26, 0x487b0000405e88b6a75791437d49d95c5daa749370a59b047e6f46b6f3f245a80000225c⟩,
  ⟨81, 26, 0x381000000e000000057f0851b5dec8718537a27c4d15e4000005780000059dda27f30760000039c000000e6f000004db896939b6d976dfbdb00000056b00000559400001e6400000a18c322cd16200000158400000360000000d7c0000035e0000011740000095c00000355c00000d5600000355400000d5400001094c00000952000000d4400000350000000d3c0000034e000000d340000034b000000d2800000349000000d2000000347000002d0000000b3f0000030f800000b3d0000074f000000b3b0000010e800000339000000ce000000337000000cd800000335000000cd000000333000000cc800000331000000cc000000c290000030a000000c2700000349800000425000000c9000000323000000c880000081b0000020680000081900000206000000317000000c58000003150000024400000090f0000020380000030d00000281000000303000000c0400000300⟩,
  ⟨35, 25, 0x1586545ec0000c6f40000177942c173bc0000119dcd334fce0697a696fa244acb71994f65b4000472ca429aa5640fd92b31800002988000560ae00006c560000322a800018950000006a600003b4000001d9f8000134f800001c7a00006f290000371400001349c0000144c0000251b0000128d000007c6400003e3000001f1000000f87800005c3800001c0a00003c04⟩,
  ⟨33, 25, 0x217b00000a3d0005fd5e0000040eebd83eb705ea5f637c112989b8000010da00005d65000012b200000558c00000ac40000635700001fab00000f554000078a8000032400000191f80000a0f80000127a00003f2900001f9400000cc9c0000104c0000191b00000c8d0000064640000323000001a1000000d07800004c380000320a00001a04⟩,
  ⟨33, 25, 0x167b000008bd041dee1e0000038ef6d072a70bd031db780000e9b800000eda0000296500000cb200000418c000008c400006e57000022ab000010954000082a800003e4000001f1f80000a8f80000167a00004b290000259400000f89c0000104c00001e1b00000f0d00000746400003a3000001d1000000e878000050380000340a00001a04⟩,
  ⟨33, 25, 0x167b000008bd041d8b9e0000038ef79c358700efbabb780000e9b800000eda0000296500000cb200000418c000008c400006e57000022ab000010954000082a800003e4000001f1f80000a8f80000167a00004b290000259400000f89c0000104c00001e1b00000f0d00000746400003a3000001d1000000e878000050380000340a00001a04⟩,
  ⟨34, 25, 0xdafa0000bd7c00003db98104209cb1f2f90e20003ac690001bfb40000d059c000684cc0000095b000062ad00003156400018ab000000f44000040a1800030508000182820000432d00002196000010cac000094540000041f0000058f000003474000024380000061400000b8980000b0480000582200000f0a00010e0480000242000001a0e00001006⟩,
  ⟨34, 25, 0xdafa0000be7c00003db9e3a0ac9caa66b58e20003a4690001bcb40000cd19c00066acc0000095b0000622d00003156400018ab000000f44000040a1800030508000182820000432d00002196000010cac000094540000041f0000058f000003474000024380000061400000b8980000b0480000582200000f0a00010a8480000242000001a0e00001006⟩,
  ⟨34, 25, 0x186fa1963f67c000004bcccd0751cc6a6e30e4342cfa71245ba9b488cd9f5a036c3a8ce36b90f66000055ad00002cd64000166b000000f440000332180001cd080000e68200003b2d00001e1600000ecac000076540000041f0000050f000003074000022380000061400000a898000088480000442200000d0a0000910480000242000001a0e00001106⟩,
  ⟨9, 25, 0x477b2b25703d457de29e48fcdf4e8000087732b3201b48791541a070c4a2ce70bb6266⟩,
  ⟨28, 26, 0x61f87719a87b348e86de8d5ae027611f9c8dd63c3c197400000c1b800013a6d376c311b000002b6b00002a9a80000256500000b59000003863008b719880000275d00000997000002753000006d4800002a410000074ec00001e1f00000747800001d1d0000098700000241200000904400001709⟩,
  ⟨37, 26, 0x4116e37b106f0fde800008d79000002de000005f7711f9ba1d800002e7000000b9bc00016f6e8eb703db411d2b06522a5fad90480e7a6307bf5dd88000017570000065580000195500000655000000c53000004d000000133f0000048f800000a3d0000034f0000016290000058a00000152700000389800000b1b000002c6800000b19000002c6000000c1000000303c00000a0e00000201400000f04⟩,
  ⟨33, 25, 0x147b0000073d266f131e36d274aee0001e3700000f1378000111b8000010da00002b6500000eb2000004d8c000008c40000a05700002b2b0000151540000a8a800002e400000171f80000c8f80000167a000030290000181400000bc9c0000104c0000131b0000098d000004c64000026300000161000000b07800003c3800002c0a00001204⟩,
  ⟨22, 24, 0x127b00000f7aba548e78000007700000076f0000066e00000665000005640000065700000656000006400000063f00000629000006280000071b0000071a0000061900000618000006100000060e0000100500000604⟩,
  ⟨6, 25, 0x30f60000207abcdae63c8000010200000060e00000306⟩,
  ⟨6, 25, 0xccf77d512c7a51d3313c8000010200000060e00000306⟩,
  ⟨6, 25, 0x29b7772f6f40fce7a0001a63c8000010200000060e00000306⟩,
  ⟨7, 23, 0x186c059f0000073c800003410000062600008020000168380004106⟩,
  ⟨30, 24, 0xbe1eb47d72b5ea7c00001c730000207200002071000022690000226800004267000042660000195a00001a5900001a580000174300001842000018410000142d0000142c0000152b0000162a00000a1e00000c1d00000d1c0000061400000f1300001412000014110000470900000e080000200700003006⟩,
  ⟨2, 23, 0x23f372bf00004479⟩,
  ⟨8, 23, 0x8fcdc2fe000299ec000263d0000647900000ee000001dbc00003b280000757⟩,
  ⟨46, 26, 0x3960447e74d8000002f1fc0f23617c00003e9e40000d3770000189d80000876d000028db00000726b00001ad740000e35c00005a16c0000cc5700003b1580000ee5500003c1500000c953000026d480000664700002611890681f450000bf1100000db40000036cfc0001353e17f880cf6bd85b63c000033cec0000743a00001f8bc0000c52e0000308a40000c22800003489c00013d2600006e8940000a9240000338600000791700001fc580000c01500003bc400000ef0f00002442c0000cd00⟩,
  ⟨85, 27, 0x13ddae481000001d000000055fc000032bb800001276000005ce000000b9bc00000fb700000146d0000040d8000003dac00000bb2000001262000001cc2000003580000006af800000d5e0000018ba000003d70000010ad800007d5700001e8ac00004495400008d2a0000020530000096a4000003544000006a8000000d4f000001a9c000003534000006a6000000d4b000001894000003524000006a4000000d47000001c8c0d112cd1400000c220748127400e897547eca97130f8e63b2a9ee3e67713c05b831a760000064e80000069c800001038000001c6e0000034d80000069a800000d34000001a660000034c800000698800000d30000001a5e000004cb80000311480000622800001824e00003049800004512800001b24000001a4600000348800000690800004a1b00000943400001786400002f8c00000131700000222c000004c5400003b8800000760f00000821c00000343000000805800002e04000001a0600000500800000680800001300⟩
]
set_option maxRecDepth 100000 in
def YOT (i j : ℕ) : ℤ := (((YOTSparse[i]?.map fun r => r.entry j).getD 0) : ℤ)
set_option maxRecDepth 100000 in
private def thTSparse : List OMA.Erdos1186Low.SparseRow := [
  ⟨3, 40, 0xffffffd64442ffffff76ad41ffffffddab00⟩,
  ⟨2, 40, 0xffffffe7f043ffffffe7ec00⟩,
  ⟨3, 40, 0xffffff5aed43ffffff863101fffffff7e700⟩,
  ⟨2, 40, 0xffffffd80744ffffffd80701⟩,
  ⟨2, 40, 0xffffff558844857adc8a2c02⟩,
  ⟨2, 40, 0xa40577079a44fffffd6f5202⟩,
  ⟨2, 40, 0xffffff85924500000052de02⟩,
  ⟨2, 40, 0xffffff0096450000007d1502⟩,
  ⟨2, 40, 0xb614f2cefb45000001085302⟩,
  ⟨2, 40, 0xffffff5fe945ffffffb41a02⟩,
  ⟨2, 40, 0xfffffe1e7a45ffffffc85802⟩,
  ⟨3, 40, 0xa9d5d82b6245ffffff63d103fffffff47802⟩,
  ⟨2, 40, 0xffffffd75446ffffffd77d03⟩,
  ⟨4, 40, 0xfffffff7d847ffffff0a6c46fffff73a9305ffffffc22204⟩,
  ⟨2, 40, 0xffffffd433470000015cc106⟩,
  ⟨2, 40, 0xffffffca6147fffffcfea806⟩,
  ⟨2, 40, 0xffffffbaef47000001684407⟩,
  ⟨2, 40, 0x2d6147fffffe4a2607⟩,
  ⟨2, 18, 0x98a11e3e6208⟩,
  ⟨2, 40, 0x20e847fffffe66e008⟩,
  ⟨2, 19, 0x3bf5244550809⟩,
  ⟨4, 16, 0x7fe5491121480ca50bd2990a⟩,
  ⟨2, 14, 0xa18d26cd80b⟩,
  ⟨3, 19, 0x28292408ce0648a810b⟩,
  ⟨2, 16, 0xd6914a85940c⟩,
  ⟨2, 20, 0x112ea4a980690c⟩,
  ⟨2, 16, 0xd5b44a566e0d⟩,
  ⟨2, 15, 0x280ba531f80d⟩,
  ⟨3, 40, 0xffffffe17f4bfffff78b2d4affffff7a360d⟩,
  ⟨2, 40, 0xffffffddbc4bffffffa7f70d⟩,
  ⟨2, 40, 0xffffffb33b4bffffff74c20d⟩,
  ⟨2, 40, 0xffffffe8034bffffffe59e0d⟩,
  ⟨3, 40, 0xffffffe1d54bffffff86300efffffff7b50d⟩,
  ⟨2, 40, 0xffffffd8074cffffff88150f⟩,
  ⟨4, 40, 0xfffffff8014dffffff88004c00000027ff11ffffffd80510⟩,
  ⟨2, 40, 0xffffffe8044d00000077ea12⟩,
  ⟨3, 40, 0xffffffe2054d00000011b8140000007cca13⟩,
  ⟨2, 40, 0xffffffd8074e00000093b214⟩,
  ⟨3, 40, 0xfffffff8014fffffff88164e0000000aca15⟩,
  ⟨2, 40, 0xffffffd4654f0000004a7815⟩,
  ⟨2, 40, 0xffffffcab44f0000006bd915⟩,
  ⟨2, 40, 0xffffffbb7a4f000000c3f815⟩,
  ⟨2, 40, 0x2b9b4fffffffdc6215⟩,
  ⟨2, 40, 0x24e64ffffffdb5d716⟩,
  ⟨2, 40, 0x1ffa4fffffff55de16⟩,
  ⟨2, 40, 0x77ea50ffffffd6ca16⟩,
  ⟨3, 40, 0x77ea51000000112150ffffffdac317⟩,
  ⟨2, 40, 0x27f951ffffffe5ee17⟩,
  ⟨3, 40, 0xa0051ffffff87fc18fffffff7ff17⟩,
  ⟨3, 40, 0x77ea52fffffe205719ffffffd46518⟩,
  ⟨5, 40, 0x77ea530000001121520000001ffa1cffffffc40b1bffffffbb7a1a⟩,
  ⟨3, 17, 0x9fe54c890c3bdfa91c⟩,
  ⟨4, 17, 0x4ff29844847d3fc83ddfbd1d⟩,
  ⟨2, 15, 0x3bfc2a77f91f⟩,
  ⟨3, 15, 0x1e2b154894aa0a0420⟩,
  ⟨2, 15, 0x3c622b286620⟩,
  ⟨4, 40, 0xffffffd7e658000000282b570000001122210000007dab20⟩,
  ⟨2, 40, 0xffffff88165900000077ea21⟩,
  ⟨3, 40, 0xfffffff7ea5bffffff87145a00000009ff22⟩,
  ⟨2, 40, 0xffffffe7085b000000280522⟩,
  ⟨3, 40, 0xffffffdf1e5b00000011212300000078e822⟩,
  ⟨2, 40, 0xffffffd7215c00000077ea23⟩,
  ⟨3, 40, 0xfffffff5c55dffffff85285c0000000d4524⟩,
  ⟨2, 40, 0xffffffdb145d0000003b9624⟩,
  ⟨2, 40, 0xffffffd45c5d0000004f4924⟩,
  ⟨2, 40, 0x4f6f5dffffffd45b24⟩,
  ⟨2, 40, 0x3bac5dffffffdb1324⟩,
  ⟨3, 40, 0xd485dffffff85be25fffffff5c624⟩,
  ⟨2, 40, 0x77ea5effffffd71d25⟩,
  ⟨3, 40, 0x78f55f00000011215effffffdf1326⟩,
  ⟨2, 40, 0x28035fffffffe70826⟩,
  ⟨3, 40, 0x9ff5fffffff873727fffffff7eb26⟩,
  ⟨2, 40, 0x77ea60ffffff881628⟩,
  ⟨4, 40, 0x7cc561000000112260000000282b2affffffd7e729⟩,
  ⟨2, 15, 0x1432b0f8c02b⟩,
  ⟨3, 15, 0x28118489516f8b02c⟩,
  ⟨2, 15, 0x3bfdb177fb2d⟩,
  ⟨4, 17, 0xefdab227f918c2242c409fe2e⟩,
  ⟨3, 17, 0x77ea594890cc827f92e⟩,
  ⟨5, 40, 0xffffffbb7a67ffffffc40b660000001ffa6500000011212f00000077ea2e⟩,
  ⟨3, 40, 0xffffffd46569fffffe20576800000077ea2f⟩,
  ⟨3, 40, 0xfffffff7ff6affffff87fc690000000a0030⟩,
  ⟨2, 40, 0xffffffe5f36a00000027f930⟩,
  ⟨3, 40, 0xffffffdabc6a00000011213100000077ea30⟩,
  ⟨2, 40, 0xffffffd6c86b00000077ea31⟩,
  ⟨2, 40, 0xffffff55d06b0000001ffa32⟩,
  ⟨2, 40, 0xfffffdb5246b00000024e632⟩,
  ⟨2, 40, 0xffffffdc636c0000002b9b32⟩,
  ⟨2, 40, 0xc40b6cffffffbb7a32⟩,
  ⟨2, 40, 0x6bde6cffffffcab432⟩,
  ⟨2, 40, 0x4a806cffffffd46532⟩,
  ⟨3, 40, 0xacb6cffffff881633fffffff80132⟩,
  ⟨2, 40, 0x93ba6dffffffd80733⟩,
  ⟨3, 40, 0x7cf86e00000011ba6dffffffe20534⟩,
  ⟨2, 40, 0x77ea6fffffffe80434⟩,
  ⟨4, 40, 0xffffffd8067100000027ff70ffffff880335fffffff80134⟩,
  ⟨2, 40, 0xffffff881572ffffffd80735⟩,
  ⟨3, 40, 0xfffffff7b774ffffff864073ffffffe1d736⟩,
  ⟨2, 40, 0xffffffe59874ffffffe80336⟩,
  ⟨2, 40, 0xffffff750a74ffffffb33a36⟩,
  ⟨2, 40, 0xffffffa85d74ffffffddbc36⟩,
  ⟨3, 40, 0xffffff7b0274fffff7816237ffffffe17f36⟩,
  ⟨2, 15, 0x18f8ba501737⟩,
  ⟨2, 16, 0x566474d5b437⟩,
  ⟨2, 20, 0x99f8d75112dc37⟩,
  ⟨2, 16, 0x85dc75d67837⟩,
  ⟨3, 19, 0x124f31d808d0ba80a0b38⟩,
  ⟨2, 14, 0xb389da85538⟩,
  ⟨4, 16, 0xd38a770ca5761121397fc438⟩,
  ⟨2, 19, 0x229ac3c077ea39⟩,
  ⟨2, 40, 0xfffffe66f37900000020e43a⟩,
  ⟨2, 18, 0x8fa89e426283a⟩,
  ⟨2, 40, 0xfffffe49d07a0000002d5f3a⟩,
  ⟨2, 40, 0x1674f7affffffbae83a⟩,
  ⟨2, 40, 0xfffffcf8e37bffffffca5d3a⟩,
  ⟨2, 40, 0x15c7e7bffffffd42e3a⟩,
  ⟨4, 40, 0xffffffc23c7dfffff77e5a7cffffff0d533bfffffff7d93a⟩,
  ⟨2, 40, 0xffffffd77a7effffffd7533b⟩,
  ⟨3, 40, 0xfffffff4777fffffff64847eaa168790893c⟩,
  ⟨2, 40, 0xffffffc85d7ffffffe1f403c⟩,
  ⟨2, 40, 0xffffffb4277fffffff5fff3c⟩,
  ⟨2, 40, 0x107887fb69014f2513c⟩,
  ⟨2, 40, 0x7ce17fffffff02823c⟩,
  ⟨2, 40, 0x52c77fffffff85ae3c⟩,
  ⟨2, 40, 0xfffffd75487fa423140da43d⟩,
  ⟨2, 40, 0x85163662ba7fffffff55373d⟩,
  ⟨2, 40, 0xffffffd80780ffffffd8073d⟩,
  ⟨3, 40, 0xfffffff7e781ffffff861880ffffff5a953e⟩,
  ⟨2, 40, 0xffffffe7ec81ffffffe7ef3e⟩,
  ⟨3, 40, 0xffffffddb981ffffff76e540ffffffd6493f⟩
]
set_option maxRecDepth 100000 in
def thT (i j : ℕ) : ℤ := let value := (((thTSparse[i]?.map fun r => r.entry j).getD 0) : ℤ); if value = 0 ∧ OMA.Erdos1186Region2.g24Area4 i j = 0 then 2^40 else value
set_option maxRecDepth 100000 in
private def NLower : List ℕ := [0x17a9d91ddc335514, 0x216fcdad0baa5e00ff161ce49808940, 0x41e20c71f5ef040209db8a1e716cd00ff00c2b27013440, 0x8b5c7662c841380413b712ca09aae0213b0cd4c73fae010121e59e718c100, 0x10786a022d953a0084ce19788dba0804092e980dc9b8a0209c779906673f00fe20d17f18af140, 0x2059384aa15a4d8102670cc6ae4f98081caa0cc3c64080404edc27a6e4220204ec330671cf580fdc2766dbd99e60, 0x40930847ce31ef020306f972ea9618102670cc66590280813b0cc9671c1004051174effc51a0204ec33283641780fdbb3eb82f38160, 0x81c6f749bee82203fb6e1987e258601fdb70cb2c633b00fdb70cc2366a1807db70cfbfb71e403fb8dc0fb6841201fb8c3304ae45980fcdcdbfd258d9a0, 0x1037f49a507fb7c080ea65e6dcf24403fb6e19858acd901fdb70cb449c5a80fdb70cc10aa4b007db70cdd2278e403fb8dc0c9145e201fb8c32f948d5880fd2ff40d5e47860, 0x20792131e2f88c81019f876ef7429808099c43518ad6a03fb6e197c2f24801fdb70cbe6051b00fdb70cecb0f4e807db70ce0cfec3803fb8dc4fdd04d001fb8c32ebf032280fd083b725c7d0a0, 0x40b0a00267ef7301fdb70ccd24b2400fedb866b989ac407f6dc33718ff800404ce1969e3b070202670c8e4c24b8101e3f7b0283b780813b0cc70741200404edb28eb626e0204ec32cf6750280fd801f4d518aee0, 0x820da5656159760406639549722d901fdb70cbe6051b00fedb866aecc4ec07f6dc337c4d5580404ce195f2652f0202670c1980cbe81024c705c775c980813b0cc6ef88780404edc663e89100204ec33d686c2e80fd04466b3eb2b60, 0x110764017941dac081cd49b23591e6040e6a4cc59e9eb01f9252720b0a3a00fcc4b0b46562e407e603b4d101800040dc8e56ac37e10206185936f1de18103b12656300404083b126543378e8040ec94da4c4d46020ec499f8e51c980fab9ef33bdd6b20, 0x20f0d40f532b160107c0ab23d334e808133866412ab500408b342074546601fb6e197faeb1700fe41738539061007f059255f3fdb8040536f512562460203db445e6d25a01027619a171826008276195ef4c7bc04086e94d6b5536020933d47e14bba00fe25e99523ce5c0, 0x46123b3b1fbd58021651766c28ed9010e6a4ca815dd900821cf8274e7030040f2b20f2937ae01f84df38a687ea00fbaaad559ae1f807db70cde677f880409d86685675f20204ec331bdb3f00104ec331ab93e60084ec331ab93e600411252ce720c2002111669b94636c01009dd205672b700, 0x81d7fa65eb1f8e0413386767876580204ce19904aad401039a9313dee68c0808edab66f75460404ce18e6e575f01fdb70cca755ae00fedb865b7c8e8407f6dc32d6da4630402b7be5f23d0702013b0e0a36f0481013b0cc6ae4f980813b0cc6ae4f980404edc43012e440204ec32e8e90e380fe321a7170c23e0, 0x1043bc3e2936ecc080a5acc73489460413386635727cc0204ce19904aad401039a93133310b408099c2e6281a7a0404ce18a67544f01fdb70cbe6051b00fedb865ad0b8ac07fb8c32bd028240402761bd0bcd9502013b0d8aae39f81013b0cc6ae4f980813b0cc6ae4f980404edc43012e440204ec3352f709880fce385d5ed8d760, 0x208788f4541e7181021fb6ea39f784080a5c9c8b4d7c20413386635727cc0204ce19904aad401039a93133310b408099c2e67e05660404ce18a67544f01fdb70cbe6051b00fedb865ba3d08407fb8c32cb18cec0402761bce0d81f02013b0d8aae39f81013b0cc6ae4f980813b0cc6ae4f980404edc43012e440204ec3352f709880fce2c6c82c03260, 0x40ffa82a83e85701fdb416f1e960380fed9611fb3518407f69a968ec8d9203edb86635727cc01fb6e19904aad400fc92934ae965bc07f6dc3a8d0592a03fb9f63b92109f0202670cca755ae01009d866df0d4300804ec338c6961c03fdc61916a81bd01fee30c4b2c9c580fee30cc6ae4f9807ee30cc907bc0c03fb8dc0718e0b601fb8c3352f709880fce6532f1871b60, 0x81ff5db5a7a77e0408f8c5632e4df01fdb420320468f80fed96b831ee27407f69a37aeef5ee03edb86635727cc01fb6e19904aad400fc92934ae965bc07f6dc3a87a6e3e03fb9f5568342710202670cc7d440081009d866cf046740804ec338c6961c03fdc61916a81bd01fee30c4b2c9c580fee30cc6ae4f9807ee30cc907bc0c03fb8dc0718e0b601fb8c3352f709880fce650ca0b61fe0, 0x103752185f1925c080df4c45e7011e0406fa99721963d01fdae64d33998680fed7a751d2877c07f6dbe3959b71203edb86635727cc01fb6e19d36a35a00fc92941c5604fc07f6dc3518dc17a03fb7915f5f53a502013b0ccf0423c01009d866ef3c7fc0804ec33c21c35403fdc618de45f0f01fee30c0ec36e680fee30cc6ae4f9807ee30cc8b1d12003fb8dbdbf8754001fb8c3352f709880fdf54b7a495bde0, 0x20f5bbf12ca6f201033d938a0306200815a56029b36d4040ad2a8d84035e01fb6e17415ce0100fdb70ba2061bb807edb8620379f6c03db70cc6ae4f9801f6dc3503deca000faa33368b9d69007edb867fde282803f846ff46ac79a020276199a4964801013b0d00ceffd8080b84acc4dbe2403fb8c32e9421be01fda9331d8262600fdc6198d5c9f3007dc6198d5c9f3003f71b886025c8801f71866784945b00ff1a414d4509dc0, 0x46c5bccf1a5bc8021404c34c62ba60104ce199c49c34c082670ccc774b0a0413386663ba58501f6dc330d9e10980fb6e1986cf084c07db70cc3bd6f1203b6e198f88e44401eebe8fff6d41600f363d28a2da09c07db70ccfc782ca03f718663e239110205bd7663fecd78102d2afe3b64424081413b0472240603f718650c7804301fb8c3300315bb80fb8c331f11c88807b8c3320bf5f2403ee371294bf10a01ee30cd8c3ac7d010330b40c1ed98c0, 0x83c35022ea6a80042caa8ecf4507602099c332991b070102670cca646c1c08133866532360e04099c332991b0701fb6e1994c8d8380fdb70cca646c1c07edb866532360e03df0af2bc7ab0001f6dc336a7f4ed00f9587f6ce4fca407f71866532360e03fb8c3049e62bb020335f8e4601da81013b0d71426f0c0809d867aca6ac203fb8c311a2fcd301fdc61994c8d8380fdc61994c8d83807dc61994c8d83803f71b89bd584a401f718667dd017701005c62ae9f7b680, 0x11cf8ecce714050085652e7cb2a178044ce198fa33b3c0213386629c6cf70104ce1979ffbcb0082670cafe91464041338657f48a3201f6dc3397c74b400fb6e19cbe3a5a007db70d09db037403b6e19927fb9fc01edb86714fd72500f24a4cc852bd8007ee30c87a2f5c403f2074752f1ef40204ec33463b2ee01027619985631300813b0cc9fbb0c803f718663395dd201fb8c331aedec500fb8c331aedec5007b8c331aedec5003ee370582e066c01ed8107af6b34e00fff5e00c5836080, 0x20c81b8e32f4e761073527640bbff4081cd4997cb5115041cd4993cfd411820735259c200d98101cd48f6999892080e6a4601d779d0407352300ebbce81fc92980d3284240fe494c0541966207f3ccee5454ee503e5779bad42efa01f925265a45a0300fd7edca6de20b607f952486b5ffa103fca925a2d66808201d8931d907a88100ec498b94423a0807624c58eb54c03fd86ee40a374f81fe5493cc759d940fe54932a05776407e54932a05776403f954a6481c56601f9524cb144ffcc0fbc6d5105f460d0, 0x406054e431b7f8c2027dd967aad2b2102670deb63aef408099c332991b0704099c32fed9b008202670c0c14170810099c2994cf55e0804ce12d7022f3040267096b8117981fedb8b1380b86c0ff6dc58868b08607fc23098e5484703f72a0b88d1d8a01fdb70cd347d1ac0ff2a497c2cd37a07fdc6151af3e8303fee30c1ad877982009d865f3028d81004ec32a0d2f1e080276194803a6403ff23baf60009c81ff718705c74dfc0ff7186635727cc07f7186635727cc03fdc6e2180972201fdc6195cf64a940fe6e76b171bab70, 0x80b3cae67048618401ab3de2bc100c202934ed168c792102670cc6bb7b1408099c332991b0704099c32f97b0148202670bd9109ae810099c2c59a170e0804ce15e701d8b0402670af380ec581fedb8c17f0d3cc0ff6dc61609f18e07fc0222aad644b03f76f7a5d9748001fee30c7fa71f800ff2a4972c721aa07fdc6160c989ff03fee30c305332982009d865f3028d81004ec32ab904f6080276194d6255003ff4bd8403452e81ff7187a430711c0ff7186635727cc07f7186635727cc03fdc6e03cce08c01fdc61963aca5040fe4827bb1bd9ff0, 0x1038b1d5384697c0808e36b4bac74f0403549cc0cc89b820527d6b692f644104ce19eb6fe84808133866532360e04133866188cc9d0204ce189fbeea801013385f699d51c08099c2f745e77e0404ce17ba2f3bf01fdb7127c9fa7480fedb8948615b4c07f80407aa4da4603eedec42543ccc01fdc61947cc76200fe549307c9dd5c07fb8c2f99f53f203fdc618f70182302013b0cbe6051b01009d865b7c8e840804ec32d5d62c403fe978d4b1bdff01fee30e078798e80fee30cc6ae4f9807ee30cc6ae4f9803fb8dc254d77ae01fb8c330d2829c80fcc0854a8dde160, 0x2055a8dcc5092180fedb862a49271407fb6e17c4ec99703fdb70b9748be381fc9292879551340fb6e19800a414807edb866532360e03edb8667685bbf01fb6e1c0451d4500fedb86e58f357c07f6dc3808a3a8a03fb6e1c0451d450202670b6f029f981013385b6d579f408099c2a8bd2bc60409d8663a58c2802027619c4a5d510101e65c39055bf40804ec347d224be0402761bf435c8101fee30ccfd409a00ff71867701ce1c07fb8c35044d2a40402761926c428102013b0c6356aeb81013b0cc6ae4f980813b0cc8b1d1200404edbad7cdc920204ec33300f99a80fd8aa8052802460, 0x408b9b59392107020329b776f4d5f80fedb862cf87e7407fb6e17da6754703fdb70b9ca76cf81fc929293aa5a640fb6e1982b998a807edb866532360e03edb8668eafce501fbcaf19ddb9e300fedb8705c74dfc07f6dcf790c6a2e03fb6e7af9a60990202670825491f88101338407e7324408099bf3d73e7860409d86638abd1202027619ce0b86e01023802921bb68c0804ec3467a790e040288caf66c33501fee30cd12bb5500ff71867fbbaa1407fbec97fa6f1d8040276193c3ee3102013b0c5741a5881013b0cc6ae4f980813b0cc6ae4f980404edb957dbfa80204ec332d6042480fdedd6b5b8d4460, 0x80697454ea18d184038162ea8b3d382019672bac13d3c0ff6dc2f745e77e07fdb70af380ec583fedb8531423f0c1fe4948ffff4a620fdb70cc6bb7b1407f6dc332991b0703f6dc338518c0c81fde341e94165980ff6dc3dc29c03607fb6e6200d661b03fdb72fd913a598201337d4e31950c10099be6e0ac9ce08049bfccda16930404ec331d45f1002013b0d11fb39701011c585ba751720802761ac4d036b04013e2b8ab85f981ff7186735338280ffb8c352ff239607fe197f20e51f804013b0c8096b0682009d85e67dc8dc1009d86635727cc0809d86635727cc040276d8e80a75a020276197fddba740fee0ae66db486f0, 0x10786a0319db430080d0bd9ad9d87e040d09e0bbce3a80207500ff76fe0600fdb70bd25a407807f6dc2b7d7774203fb6e14340c8df01f9252416cf90380f6dc33163b136807db70cca646c1c03dbef0dc07c23401f6dc337b6187e00fe03640422821007eeab422059cbc03f755dde4c07ce0204a66ecd3ec4701025282b2ac4ea8081272788f730b40413b0cc6cd3a700204f6ba5d2cdc20103c53b7fd734700809d86716fb2840404ec3378b230801fdc6197cc0a3600fee30d4eabe5b807fa068d83898e40404ec32e9421be02026e58f2067dc010276198d5c9f3008276198d5c9f300409db5f6b81f920209d8666adc90d00fb45913b92b1cc0, 0x239f1d99b3d112010ce619b09db1a808184087436160c04183fd017216c6020c41cb1f7865800fb6e198d5c9f3007edb86635727cc03f6dc331ab93e601f24a4b61dde5800edb86635dbd8a007b6e1994c8d83803b6e19905faf9201ee56acd88140b00fbb5da641a488007db70d534dcfdc03edb86a97bf27802089cca6e30e5c01044f7bf1b710e00813b0cc73d0f5804276198d700ef80209d866412ab500107624cb6da3e200813b0cc6ae4f980409d86635727cc01fb8c336b9d48300fe1e047d9daab007f88d6ab275678040869aa767c4b002041f72f7f8bd70104ec331ab93e60084ec331ab93e6004138f0486779700213b0cc8933e7700f993efe6f2a2700, 0x41eae7f023d4700218432dc95be260105426ae696d2580809c77c87385cf040aa32e72ed0ff0204e09e9a026fe80fdc04738f0935c07f7011ce3c24d703fb808e71e126b81f940d5aad1ba140f7014e3a88553807dc04a835aeda403ddca55f968f8201f7351e4f5610f00fdc04738f0935c07ee0239c7849ae03f7011ce3c24d70202dfa6404715f81014447397d1ac0080a2239c7849ae04164649bf004000205112d2df0c830103cceded0e2c74080a2239c7849ae040510e11e5c2f501fdd88e61452ae80feec47334ce87407f762fcacac6860404227251d4dd90201da39f9fd879810287f53d2326900828885aef567d4040a247d76dcb8c02094091d7f76a900fe97b30a3ad7400, 0x8d2608a58e6a80042907856ac1ac8022873de66d588c0109f434bc8fdbf0081439ef234eb82041439ef234eb82020a1cf791a75c100fbae7bc8d3ae0807eeba15963ff4e03f75cf791a75c101f30b80d8a3a2080eeb9fa258cc81007bae7bd03fe71003bae7bcafff31c01eef31d4aab80300fbe35a6d91aa6807dd73de469d70403eeb9ef24c5aec02056cf79262c4a0102b67bc8d3ae080815b3f9f6d27e4042b67db73065f4020ad9ef2f06f06010823735a7b0a180815b3de469d704040ad9ef234eb8201fc0b3d6ad845600fe067bbf8fd9c007f033de0f3b24804099bac237db12020551cfa332a720104e1bcdd4301e0084ff40e3d1feac040fac1d5020d4002139963b16738800f8d31f987f7de80, 0x106f7f9af2211700855c812ee3f1280414c0b436f500e02144602c04e238010516ee4b7a3780080a01ee3a447f8040a2301602711c0205008e6981f7200fdd8c05809c47007f76301602711c03fbb180b01388e01fa08c2cb47af000f7788de9059ec007dd8c05bbfe0f403ddd2ee7a1d90c01f76301602711c00fdf4205a209da807eec602c4b255403fbbaac859fd980202d3a8d28165401015cc05809c470080ba30eaa3ded404167a9c89bb2f40205730166032de01041641081d4d50080ae602c04e2380405324009df5d601fde548008826800ff04c05266198807f826029c8ef780404bb08a05ade402027f4ed73c9c7010236a12cd4b2180824704ac255c480408c5e4fbb6a360209a8f4f8d67a000fbd180bedb27b40, 0x2312eff34ef43c010ae7080cadcb8008a7ba2a7fc7dc404287f0647bf3fc0227eb5f239b0380109fad7c8e6c0e00813f5aeeb565880413f5af1e59d4a0209fad77f10de100fb9d6c29966a5807ee75b1bae5d1003f7aed706598c001f3a2d99c88e0300eebc7ae4d3ffb807b9d6bef90b19c03b9d6bea7bb31e01ee75af92739ec00fb9d6bca129a4807e65dc358666e803f32e8efeebae202054ae009f05d00102a570146864e808152b68e4966e4042d16f55816cc4020a95afd3388d80107f043b8c354a808152b5db115e9c040a0c5a4e994b201fbead7a2501a800fdf56bda83b65007efab5eec38b7c040a95af649210402054ad7c8e6c0e01054ad7c8e6c0e00854ad7b61b5d400415319a3e454100214f208b9951fa00fa45335fa029a00, 0x422ca80b2332500216ea8076e1cbf0105252a8dddecf80850e7bca523ba0041382b247406de0213386638bd5bc0104ce198824d25808099c32b657b5a04099c32d68fce20204ce195724d7c00fdb70d3125a6c807f6dc36676fd9a03fbe417afcbf5101f9b83f7fa686f80f6dc3324a161f007db70cd6e2d12c03db70cc8d9a3da01f6dc331455a2c00fee30c7f454a3007f668fb3e9d49803fb34832e518980202761c530171f01013b0e2f8b3d900809d86ebce68040413b0cca47e33a0204ec3357ed9d80103b126554702680809d86561f20dc040434d461dc96001fdc619758555000fee30cbec4a93007f71865ff8374c0404ec331b3bb0202027619bfdb276010276199032d87808276198e2f56f00409db8ac79a7900209d866c00b58c00ff11d41dacbc580, 0x90d4766d859eb8043afe7bbda912e022dccc8a22b0f6010a4648545433b808a1cf791a75c10042704738f0935c022670cc6ae4f9801099c32d03785b8081338630ff818404133864fb4f8de02099c325d6fae700fb6e19c512f43807edb867f32525003f6dc34751445c01f24a4d655f6d800edb866536499c007b6e199e8474f403b6e198e75777a01f248323d34e5f00fdc6191286c1c807ee30c863e1e9803f7186431f0f4c0204ec33afbcafb01027619d7de57d80813b0cd6ca5bd804276198d5c9f300209d866412ab500107624ca007d7700813b0cb73e19300409d865ecf445a01fb8c32eabce6300fdc61978af979007ee30cbb800fa80409d8666380a600204ec33506c11e0104ec331ab93e60084ec331809e7000413b7148eec7620213b0cd782947d00fa01bc84a443900, 0x102f7382415100c083d11a2faaa078040ce9b377cbe50020b025b8ba2b31010296965c43d8d0082873de469d7040409c11ce3c24d702099c331ab93e60102670c6356aeb80804ce1733f02b30404ce1880de7db0202670c431e96380fedb86b9ede9a407fb6e1c4212adf03fdb70ea74867b81fc92941fb132340fb6e19cc8f7b7807edb866c94665603edb8662354f4f01fd8004608bd4900ff7185eddff92407fb8c2d4b4628a03fdc616a5a314502013b0e3d3a6c681009d871e9d36340804ec379280a420409d86635727cc02027619904aad40101d8931bececac0804ec3167c3f3a04027601eee7feb01fee30cb24b48800ff71865821614c07fb8c32b03f65004027619e006b4f02013b0d234f96081013b0cc6ae4f980813b0cc454e3240404edc6cc9ee0a0204ec3352f709880fdaa593bb84b560, 0x206c7cb6147781810204e38baa655c083c4e8b5f6c03c040c0d37d793260020b09ce8d327ce01029063013ca068082873de469d7040409c11ce3c24d702099c331ab93e60102670c838ec7380804ce17aa132fb0404ce18abd3f3b0202670c5741a5880fedb86b53b10bc07fb6e1c1c7be6b03fdb70e9c8b0a381fc929418fad7c40fb6e19f0ce970807edb866532360e03edb866248de2501fdc5d7520c42100ff718608b962e407fb8c2dabee72203fdc616d5f739102013b0e1a52fc881009d870d297e440804ec37a29cb060409d86635727cc02027619904aad40101d8931c98c2840804ec3132112020402760dfbe328901fee30cb3a2f4300ff71865821614c07fb8c32b59e13c04027619d54957702013b0d21f7ea581013b0cc6ae4f980813b0cc454e3240404edc681715220204ec32ce0fa4780fd4730c27e39b60, 0x40d8e78802942f02046040e2bfc4a8102050704c28974083c5249f9bf9ec040c0d826ec6890020b09e8c17cbf501028ffe910895b8082873de469d7040409c11ce3c24d702099c331ab93e60102670c838ec7380804ce17aa132fb0404ce18abd3f3b0202670c5741a5880fedb86b53b10bc07fb6e1c1c7be6b03fdb70e9c8b0a381fc929418fad7c40fb6e19f0ce970807edb866532360e03edb86627c804f01fdc5d7e05958f00ff718608b962e407fb8c2dabee72203fdc616d5f739102013b0e1a52fc881009d870d297e440804ec37a29cb060409d86635727cc02027619904aad40101d8931c98c2840804ec3132112020402760e094fdd701fee30cb3a2f4300ff71865821614c07fb8c32b59e13c04027619d54957702013b0d21f7ea581013b0cc6ae4f980813b0cc454e3240404edc681715220204ec32ce0fa4780fd47126933b8ae0, 0x82e9f9a8cfa6be03fa8413ca5c29f01fd41bee7f3b9b80fe6aef3ef0daac07d2ce31f0541d803f6dc21f932fb201f63b6e1696a1300fdd8c05809c47007dd73de469d70403f7011ce3c24d701f6dc331ab93e600fdb70d0bd1598007fb6e1c21da95703fb6e1aaca624501fdb70d3b79a8681013385e67dc8dc0804ce15a691a7b0402670846d8e3b82039a9100ed2824104ce187ef5532008133866532360e0409d8666258ea30202761e067bb0a01009d86c8b24a340804ec3b088745e0402761d86f2fa501fee305f01bc7180ff7182eea831bc07fb8a4127c298203f7186635727cc01fdc619904aad400fe54933a2183a407fb8c36d13011203fdc61e0a82b3b02013b0cca755ae01009d866a40ef140804ec336c3149403fdc6193c3ee3101fee30c4ddbf3b80fee30cc6ae4f9807ee30cc907bc0c03fb8dc43012e4401fb8c33ed5929980fc1cd04ac7d8860, 0x1049ae57525fe3c0813068a8c9f31e03fb5f55e60f2c101fdafb0e40a6ff80fea2d4286770e407d465370bf822003f6dbecb9d328401f6de43b16ac7400fdd8c05809c47007dd73a604aaa8c03f7011ce3c24d701f6dc331ab93e600fdb70cfe64a4a007fb6e1aefc5acb03fb6e1a3be1ce901fdb70d25feed681013385b984d1540804ce1444289a3040266ff41cf5d382039a8cf9ea1824104c5b1cb1ab9a80809d866689aa140409d866610b00f0202761a2e7519b01009d86abd55eec0804ec388ee2b960402761c4a20b4101fee307e0d1eb780ff7183e85aef9c07f9b649596b56a03f7186635727cc01fdc619904aad400fe54933acd597c07fb8c355eaaf7603fdc61ad79b9a502013b0cc91daf301009d866995193c0804ec336173ebc03fdc6192c22d6d01fee30c4c8448080fee30cc6ae4f9807ee30cc6ae4f9803fb8dc43012e4401fb8c346e398b980fc6cf16b537d1e0, 0x208c99200d001d81022114dcd7bd74080ecb5aa013bb203fa2c8800912bd01fd18c2d5df08880fe9b4e3a9018bc07d61a387742b0403f6dc1ec64be1c01f71bb5da08f0a00fdd8c05809c47007dd735c398536403f7011ce3c24d701f6dc331ab93e600fdb70cf85a200807fb6e1af5245b703fb6e1a3e9125f01fdb70d28ae44c81013385be37aa3c0804ce1469bf61704026700fa2356b82039a8d52845b841046600a7e8a9880809d866595e5fa0409d866610b00f0202761a1e590d701009d86a926078c0804ec384913d9a0402761c273944301fee307c3492a580ff7183d2e0349c07fb8b017bf382e03f6b124f75c2ce01fdc619904aad400fe54933acd597c07fb8c3553ed99e03fdc61ad79b9a502013b0cbe6051b01009d866995193c0804ec336173ebc03fdc6192c22d6d01fee30c4c8448080fee30cc6ae4f9807ee30cc6ae4f9803fb8dc43012e4401fb8c3497d755e80fcfed83e1f26c60, 0x4301f33036a22c020830f1f8c3244010420f3bd24eac0081d438b34ba21403f3935f930e1e001f9c720f2bdc6200fd80cf9398c18807aea5234cfe8cc03edb8544175b2601ee550a02b844e00fb2bbc2cb2b9c007bae771e5eb71403ee0239c7849ae01edb86635727cc00fb6e19be5c99c807f6dc348280faa03f6dc33cbedc5201fb6e19ef5c9460102670c223aa7e008099c2dfc7aaf60404ce0e572cc35020735209e199718108885325c732c00813b0cca94b7640413b0cc9f2e9200204ec33aa5e00f01013b0d0c7d2f580809d86b5e6e6940404ec35b1e68c001fdc6149a1386300fee30a41a08fc007f6c2341829af403ed1f42c0bede801fb8c3320955a800fca92664d2d0e007f718686ea6d8403fb8c3454dc2d4020276197cc0a3601013b0ccb1c2c580809d866725b9a403fb8c32b8edf7201fdc619148a43500fdc6198d5c9f3007dc6198d5c9f3003f71b886025c8801f71867f58bbcf00fa8b04698bdac40, 0x90d47665d1e75804322e15df5d188020c12650ab63e5010575240fe91418082733a83404c7c03edb85b98a764001f6dc2dcafc06500fb6e15536ca6c0076dc330bcc1a4403db70cc722f55001dceb5f244fa1000f7595b24d17b100775cf791d4837003dca518287bb4e01db70cc9a9610100f6dc3327a744c807edb869abd36d403edb867cde8ac801f6dc3ac2e58d8010336e2f0485e88080cdb91a35ff380406b00777dba30020a07ed72a629a0109d86637934340082761994df6be804276199a87caea0209d866b6ad2d80102761a827317d808148451055bd30040a4213b92770401fa018fa47ef7f00fd016da4493e6807ee30a4a0fcaa403dc6198d7332e001f718667737d7400f9524cb0679ec007ee30ce7f372b403f71866865908c0204ec331080d4d010276198632e0200813b0cc445357803f718660df008c01fb8c317c142a500fb8c331ae665c007b8c331ae665c003ee3712f4d5db401ee30cd778639a0103d7d5cf89dd900, 0x108b3b2a4aaf6f008817aeda17b404041a5b79adc3afe020645f0c89ddc08102d412271f7e3408150bfc267fc9a03f6471953bdd3101fb236ab413c1480fdb70df9119cb407b6ea294e1853403edba8a7052b1e01ee77d3c962d7e00fbb633da248ed807baf04d6b9039003ee0478bdaa47401edba8a6d07d2e00fb6ea8695d5ec807f6dd4c9e12e0303f6dd4f3ffd8b501fb6ea51a452ff8101cd411225c034080734cf03d87f30403fd1205649bd82061860f1fbc0b4104ed453732cbc00813b51515716e00413b515efe1e9c02051d7cec6d9fd01015fa0b2e207bc080c46edc5bb9260406237d993839301fd3ca39b3201180fe9cee31cac1f407f71a878d5c4e203ee3514da0fa5c01fb8d45634e78800fca9f40b1e891c07f71a8f8b4661e03fb8d453683e97020276a28aa5f8e81013b5147fd4f740809da8b4b096ae03fb0a78675f24101fd8757af874c280fdc6a29b41f4b807dc6a29b41f4b803f71dae68392a801f71a8b3e2bb2b0100388eb08082d00, 0x24583b034a71b8010e0cd271c3434008e3b6451db604c04328c5c8753e92020bef9b563cc868105532bf9e9b7a4082e130f4ad778603ead8108d6df2301f56bc60e15f3580fb90f9ba802484077226da86d8ad803dc89b6adaa98201de0443f257c3900f7a93beddb5e38077a3321f5ba88803dd1d5dc5da67a01dc89b6a1b62b600f7227166f263b807ee4541de1266703ee44e69726fdd01f72270c5d9e938102ca647426c8d4080b299afdeac870406a33bdb1810f8207cb950e6218b410a64db518f7af00829936dba2fe74042993797b39d80020a64e3f3e4a700102993b271339c40814cab82cc757e040a655c1bc25ab01fb1540671bbbf80fd93b03832b79c07edf2d3137d05203de936d436c56c01f7a4db5c934df00f9bba6bb375a8407ef4a07ef43fe603f7a4db50db15b0205326d873593381029936caf2f1240814c9b66a53dfa03f6aff3abd98c901fb78df785d0ec80fbd26da86d8ad807bd26da86d8ad803ef4ffaf71cc2e01ef49b782ad5800100c5466fb4c3840, 0x426b5e09cd6e940217368e432139e01054d54c54c2bd008576ebf039c350041515d518f469202054575463d1a48102a2baa31e8d240814bf37bb9b62e03f7249dc25517901fbb9ae309a5e280fdd2dda7ec2b7407bdc9f7aa19c0c03ef95d5219df6e01ef57191578ed700fc28dc68f403f807c25d781b4292003efdfa8ab0687401ef95d518f469200fbfc35b65146c007f8b5f4293aecd03f8a725841fc8b01fc1cde119acee8101e0c29b3b8c3408071c71d1c8c790402b0fb5cdd3c8020449896cdeada8105ae533a7e4d98081587716cb06ec0416cfc4e3abd7c020562196406c90010176baa31e8d24080bb5d518f46920405c094d55b04701fdb83396a3c6e80fee72004561fbc07f5d91373d23b603ee3da10672df801fc7aea925650b00fd5b7162f9712c07f8f5d518f469203fc361ecd37eab0202cb02890be858101077307fa148c080347d8dcd62ae03fc7aea8b5736d01fe3d75463d1a480fe111fd163f06007e31d6016cd25003f6ada34cf300001f8a9cac87c21000ff9fb9c92ef2800, 0x8dcf9db7ae8260042e6199bd33f9a022f03af9ca0707010ac1dcfffe974808af7a2e5fe196c042c8d511aa3b2c020ade0168d0b8d810526ca280f5ba40828dc403b4b39a03efd35dfb1810701f7e9aefd8c08380fbf4d77ec6041c077a86cdaaf783c03ddce588edd71001e1214eaee62ae00f7e8aa8815bcc0078723338af0e6c03e0e0cfe98e7e001e1be7c2c4176f00f88c8d5e512f7807f14002941158b03f0f34f2c2590901f8ced21fb360d8102a6a714ff0794080a5676be567df0405c525d2f5b618208f6867c520c5410ad75fe0d34588082fcd786323d24042b6749d7e3ba8020ba89b99dce5901029e9a6e0c377c0817e6bbf63020e040b16e2b0ca3d701fb73bcd73622680fdb9ac8ac3a38c07ed8dacfc4455603e1bea9a943d2601f7b4fda31587700fa313f3ac5f89c07f266bbf63020e03f8199be0f9b4f0204bf30509dbbf810232fa74f8e67c080e9742291098a03f7ab26a0c089101fbba8058e228480fbb2c9a21ab75007c1902db84838c03f26d004b96b8601f172b08ba434f00fcb41bae7002040, 0x108cb32d3a2e750085eaa5c4a92180041752f217072920216c8fa826c92e0105660958a597c80857321a1595b880415758333853cc02055d60cce14f30102997ada8f98c80814b375d27700003f8357cf6051c201fbd83ffdb059300fde60498dc568807be3cd264e066003eff5833c2eca801f07cfd5efdb0100fc40c7ef9838e007c4c560697e5ec03f0c4ad8f4364c01f0d6027fa7c6d00fc2d9e7d33915007f92064bd32c4a03f9224a3e687ce01fc3bcc3a858b381014b43ebfe50800805307343d1a5604030560cce14f3020488113351f6c8104b0b89ec65af008182b06a26c41c0415ec6776ac3340205f470da23e02010168b1130fd358080b6e8f2b879e00405afcf13f581001fe09eee8bd03600ff2ab06670a79807f9558333853cc03f175d26c6383a01fbdc76334ff9800fd07c484da72b007f9558333853cc03fcaac199c29e6020239e5441e5ef01012551dc3640080806775196e3f9803fb9b1e1235dba01fe1d05c670bd900fe5560cce14f3007e2053660fef3803f4e3c04b46a2601f8811da1cb2f900fcb3da0ab6774c0, 0x240ba0078f9740010b933e56d1136008b822bba9a7d38042d8d9d2622a64022d6ac7f5c74de010ab9fe7f8243e808a74ffb90818980429d2bf5f1ecd8020a69513ee5c3801053a57ebe3d9b00829d2bf5f1ecd803ef223ad9c408e01f795797c04b0500fbda57ebe3d9b0077b4279c979ba803ded1cc8c388b601e04d5217d4d7800f83b7e1d3586c0078378d109324a803df717f1233b7601e0fe69bec58a300f8ee40de43b51007f23496e2ab3c003f15948f3586fc01f969f2226d86d0102ccca9a873758080b17e9c9ff0c00405c4afd7c7b360208a292052603d0109db3bbbe1c798082888440393b00042b60e7e24189c020b8a3f107a4330103159c2d73efd8081712bf5f1ecd8040b895faf8f66c01fc64afd7c7b3600fe2fbd95c0a7f807edbc6e7cecf9c03e31c2c45e639601f8c95fbb479f000fa955fe707e7d007f1900a98f401403f816be0513be202050390802b9a30101c65c9a30ae80080a564622de14803f8c71290f01d801fc60de9bae42b00fbcfa49586972807b945aab11329003f19903b48565001ed194ed34259f00f8231a41759b000, 0x422c3702147794021aed00d1043a60105c517f8e61448085b77ca0d13bdc041666df1796956021515e54f7d41f010522e51aea7fc80852262b80cfa98041489703414a900205225c0d052a401029115fb50a1f0081489703414a9003f784738d5b89801fbc239d6c9d1000fde11c03d1b86807bc23fed63723003ef09703cbe36c01efc6b9906fae000fc05c32fbc13f007c02c6f6eefdc003ef5343c626c7201f0b1a8c11577d00fca039c022012807f980abd2e36f003f93d2340f83a601fcd876484301a01016505128a9b98080593730ec87e80402c9736d56f0c02042f3eb9ac1db0105949141f2a348081652e0a38b1a4041652e0798b7aa0205d185d45f74a01016518022d5728080b29703414a90040594b81a0a54801fe1a5c0d052a400ff0d183e96851807f869703414a9003ef9f5d472181c01fc34b81fe670a00fd27a658c03eb007f8694a0c50fac03fc349e1a1b39e02026ee687fb2b901014773e92d906008067a8fb2327b803fc33f4e25b8fe01fe19c4a6c1b4700fdb8137762703807de571f151361403f866631784ab601f7eb7300c400300fe195813df69ac0, 0x8fa525f2a18980043530b9598857202321b5a2f5441c010b9666b4f9aa8008b748633de978c042c7d0335a312e0229db0fa5706c0010a319b7772799808a30895bd4f5e80428c2256e9f3a2020a30833242c9b81051841077920c40827bf94553b79203eee12f1609da701f770978c5c98e80fbb8645240a1a4077708abcb9305803ddc248d2c7dca01df3d823b29edf00f7f757a115a1e8077f14dd295ec3803de55cc92c376601e24d5f5d11c8d00f9f1548117eec007f2f20181f8bfd03f2be21f156bad01fafc023c0a4b48102c044add3e744080b0112b74f9d1040580895ba7ce8820840ef4f6a02fc10b0115e7f0baf0082c044b540204c042c044b0002c58020b0112b74f9d10102c044add3e74408156d8b7faccaa040ab6cc6b7377d01fc20895ba7ce880fe1044add3e74407f2f111e17490603e1044a1e9d38a01f84112c307d5500fa30ce097bb5cc07eecd3ab58343603f68b8db43da8b020580867dabc208102c040bd1945a4081060cd11e16e603f8410afcee6d901fc20895ba7ce880fc2084b996c8a007be3f605a76ab803f0882c6be281401ef9aadab0b40e00fae54bd957a51c0, 0x109ae496cbc7830085b01ad2334620041713299212c380215fa9c95e2bc00105a1b00676248008579a519e4864804162711ff47be60214d618372e6af010512f19c749f280851268c70808300414499c986ede20205126563b6366010289328639cf58081448092758c0003f764d7859c1d601fbb26bc2ce0eb00fdd937dcda893807bb2698897f26c03ef6f81fc7d8ca01f07b7d5fdb71100fc0ba1c5b04a0007bf2cf28a1eb1403ef1377cfd0cca01efb9ffcde21e100fca6bace67b70007f9381601080dc03f921075eceeb201fcceb98f71c7d01015d35958da300080574db192b80404031aa11d8853c0204b713a92d573010574d43a13c9b80815d34e45e20a00415d3488a302e4020574d18de2e9001015d33519bea00080ae9929f11488040574c94f88a4401fe0a6b3f3e55500ff0535a1a2ac3007fbeab2d1d8bfc03f05348304fce801fc14d2b86739000fd0f9de1a93a1807f82987ec7126003fc14cb22b60780202ba6791ad44d01015d327c8f216008091a6f35df23803fbd83202d5eaa01fe0a67a24940a00fe0a6931ab45a807de143ff51794003f82caa95557c601f8292c433d08c00fd86d1193193540, 0x23da58b75a8118010af27134a6a0e808afe2825eb9ec4042b77300437b8c02296ceccc2ff9f010a6185ae744678089e564ec97fab4042393d2e50f8c4022abfe5b2488f0010a1ce5f22c42b0089f3cd7f4f294c0429a7405b61bcc020a69ce3c48dba810534e60ef6f4f40829a714617ba1603ef53a6c27b8a301f7a9d3613dc5180fbd4e9e0f3074c077a9d2144f729803deefda413e82a01e0224195d379700f830a01296ba880782a965c41173803df3aef134ba3401dea747edb4bdf00f888acb26c08d807f18c6e429b4f503f1694a33da8bd01f90334209a0ee8102dceaa4471bd4080b73b192a46dd0405b9de55a5c44820896bfd1fbe9bc10b73a422fdbc78082dce90e8eb008042dce8f5d7829c020b73a22bd3b7a0102dce72835f57c08169b8a31b5316040b4dd6efea29901fc59d309fb2d680fe2ce984fd96b407f16759543164a03e2ce8e694739401f8b3a273f51dd00fa798b0c7ef27407eef6381f6945603f8b39c128abf10204b340aa86eb181025a260cb3705c080e373a8f59cd603f8b3956cb5b7301fc59d113e65a480fc59d1cd28e72807bdcb70c632f6803f0bd3b7bbd45201f1674657e821000f842b40980c15c0, 0x41d63a80ae1b580217217beeee848010579f6b69057280854ad091bc373c0413af1d05b90520213ee88c3aa92b0104e0bb234f0ce0084bcc0493e67bc04106e7fa20161c02128cf8058f7ea0104d4792a0e8838084cb42cbc9e5cc0411fb28ccb0098020432aab16b86a810220e0ab46601408135e53530928203f7bd4aa13db7101fbdefd4b216cb80fdfce1de98558407bdba8a0948ac003efa46c2e3311601f08d92a1e707500fbf8e19c7e591007c0dc100ccc45803efa0718a6457401f3a514ad1de2000fd10a5aecfb52807fa523935fa4af03f9dcc59582ff101fd023241db9918101842d2cd9194c08064d3e2ee7a030403155202c931982043df7a50c31d4105bb4efa2bb1a00816ed3c233dd70041610e73cbb0ae02055b630b11935010160c612b3051c080a661f65805ee0404c71f5a46b8701fe2da77cfb81d80ff2f2ccb534f6407f8b69df3ee07603ef310867600a601fc5b4effd31fd00fc874f8ee827ac07f7b1f2dc8682603fb587a2aafc5b02019c297f13a94810104ea6e15d19c080a88c3fd7e79e03fbb6b1a335a9b01fe1831cd6ead380fdf9adf727bfb807df2ba7899ac3c03f8b9c01ea153201f87d3ec1908a600fd716169035af00, 0x8d256838d35450042ddc93a66ae34022da4985758bbc010af04acdd19dc808afbf720439d880426ab59d545e060225c8da130c86a010988f5506df2b80897256b63efda40420df08e6c125c022583ca4c3f0b501093edbb361eb9008952f95bea7c2404258315203d4680209584d517cc2c0104c0be12a2dba008269b1ec62a09803ef4f5c19e2d0201f7a7ae0cf168100fbd3d717409620077a7ac442b776403de9eb0574ab4401e01942c39c20800f82e7a401952e0078287071c8788003e3f0338d8e0dc01e3d3e941a41ff00f96d8f2addd83807f216cb33ce13803f228b6cf2493201f943d0fe2bb810102dbd640754820080b6f5a0e534200405b7ad11e6fe80208938280efa76010b6f57f5c05ae0082dbd5af82e2a0042dbd4fb3cdeea020a55c2ef099540102dbd0bcdb96b80816b0ec57ba97c040b58795c150de01fc57ac6f76d8500fe2bd637bb6c2807f15eafeaadfe003e2bd5f0eacba401f8af58010f37400fa81eda60e4b7807f15eab123e4ec03f8af572ea7bd40205b7a996d97a901025b3865c0e7200811860a6606e2003f8af57a284c6401fc57abfaab7f800fc57abfaab7f8007bfad31006054803f164f559ff6be01f15eb0cba52aa00f7f8c5a54bc6380, 0x10907921e3737d00861ffd0e2475f804168d26fa9cbfc0216154a0bbbdb601053ce5ba2fbea808542c04f710604041533539724abc0214fef3664d1cb0104b327afddc0780847a405cd0b2e8040ee4fd4de4d840213b9f9ef8fbea0104e1c9aee94590084f8924b07dee40413e2411f16b880204f88df2603d301027c44737688e8081226d4b73ecf003f79c2100ffbb801fbce024d1bbc000fdfdada53e8ae807b98931e616bfc03ee6249bc0577001ef1f930e5f42900fbf0c76ae719e007bd8f4a1f57a7003f3f1462fba21601f4c012ddca4b900fd08e3994acb5807f9935f1c1ebb003f97d556d90b1c01fcd762fcbd7ad010150494a8e8c780805412588332400402a092e451aa80203f0dbd84975201054124d128c6980815049381e182404150492d70180a0205412208c6d0701010131dc648a100804ad14165aa74040256c743188b801fdf092aff682b00fef84957fb415807f7c24a5f31c1403ef849341210b401fbe124d21d5be00fce8db5769132007f728b798236d003fbe12400334f40202a0923145888010150491ca4c2f0080a8248d90987c03fbe124cb1e42001fdf0929674c4a00fdf09268cff74007dc61c1884914c03f7c56d635fb2601f7c24a1bc979700fd6acca1afcb540, 0x2373cc6ecdefea010be23ef1080c2808a67ada18117c40429f58376522ec0229a7480b44457010a24d1eacf711008a30895bf3102804283346b6481040226fab4a4d06db0109aac50b4bbca0089e071bb6d792004246ccb455e834022789b2fc886b601099d4536cf2b100899c33152722c8042670c8625f98a02099c3100b09150104ce1874ef1550082670c544f33a403eebe9a67301b601f75f575bf21c600fbcd9065357c080772f018390fbc803de100f9ebb0a801e079c4e13d5db00f8c20bdd238a180787a0262abd77803e9bcb68dcc16601ed650c155857a00fac8013244513807f4a7f1122a63003f4906469dc16601faac7c66cbd4301027619c73c16900809d86803d7b480404ec34c89b1c00207624d88b7bfd0109d86637ca079008276199af8fda004276198fae85140209d865dec668501022c8bb62188b8080f1a78c15ca9004078d4c297effe01fb8c33df046a600fdc619ef82353007ee30cd5db6b7c03dc6198dd82aec01f7186641c138400f9524ca886c00007ee30cbeb319e003f718660dc2e160204ec32e04aca501026c53f8e233980813a9c4b248a8803f7186656aa74601fb8c335a1d05500fb8c331bb055d807b8c3317ff3db403efbb4b88aa14e01ee7dab7e1dd3100ff69af1bd5fd080, 0x422ca83b63e61c0215e3791ea49a30104f89347a94b6008533d6168192e40414ed8894cc73a0214d3a39a51ce501051823712c9118085614c797d459804148939b7e28fe0214e95faf8f66c01052dc9e6f3e1b00850f82fb0f4f7804134347bc5218e021335e01ad2adf0104cea1a8f16720084bcc76399cc440410abdcb627b7e0204271d22c5a020102009baba41a70080e8a6f28323b803f7939911d4d7001fbca0b523b29f00fdca25c00da42807b6e199b1f3efc03eefe963033f0a01f11baf26dc69500fc87bd2119471007d433ddce0079003f3cc695aa525c01f370d6018bdc200fd0216bdf26bb007f9da951b00f4e03f9e4b7378790c01fd05b6d88180301013b0da0d4cad00804ec39ab7ce720402b2a4d6ae8eb0203d6b3db2fe608104ec332d0d7a180813b0cca646c1c0413b0cc616db860204cfa07f7e15f01013b02136257400809aed5d278ae00404d7791ca078c01fdc61bd14e58300fee30de74f806807f71867fde282803ee30cc6ae4f9801fb8c3320955a800fca92645468e3807f71864f8a036803fb8c32cf8bafe02027619720345e01013b0cb9a874680809d865c685c2403fb8c338fb945201fdc619d88a2db00fdc6198d5c9f3007dc6198b0332bc03f71b8f091383a01f71866c6262b900ffc03a64290b040, 0x8a516a8f91f38e042999c5e60d5f602237d727f1034b0107c296bda0ef60087cdc14e905e68041f6471595fbfb021f3d767c06dd181079b9e689420b0087a46704bddae6041ecda4b657976021c721a9381eca010768de892262580875582cfde640e041bdaa6b81402d021c6342c8a67b08106e4202610b6bc086bc0d0f2c4b0404175ab89ef3bec0205cb1f34abbb381035b7589d2159c081cd38cc1ee2ee03f24ab12c6cf7901f92557e2529da80fcdbf33702076c07925268bc143d003e5450ab81ba6601e7c833f75f4b200fb8d5f9a4a96d807be73e9ab3569403f31142ba7713b01f2a497246414800fc6d89792e78b007f7e7cfba456a503f7f317a906c8d01fca9245df61ba8101d89384a33c4c0807624f7d0404d0403b128171c45c820589ba6248690c107624cc541cdc0081d8932f96a22a041d89329a329ab0206f2557781dc90101d885a7d5dc64080ec47581d480e0407623ae12258f01fca927d3fcbd680fe5493e9fe5eb407f2a49c704770e03e54932a05776401f9524cb0e007c00fafdb96b45028c07f2a497b2b12b603f9524af2713b70203b1262f0bebe0101d8931a83b1ac080ec498c75164803f9524d3a0d26901fca926bb6992b80fca926540aeec807ca92651b1825403f2a950c4e08a201f2a49a110f2ef80fc173349e2146a0, 0x104e4d8a6fd47ac08246bddf26c8ee040bbd56472e2b4020ac0e954a3d4601028ca8e1bc937808299ec3572a188040a6b4ef9f703b020a69d3161036981028936517f87400828c2256e9f3a2040a4465e036788020a163fe3c9df401026a1737e2a670082432e66142826040675503519d510209e255c2d25ee81026750778182340825e8d9b9b8ff0040872bbb495afc0202088a0b53de88100e0293b97ca9408099c0aef7408203fb6e21c0f986701fdb710df2517880fedb89b3c7024c07db715655af2ec03f76e31cef267401f98cb60e7145e00fee4eb2b19279807f0333b5596de403fa7aaf0eaaaeb01fb8c322fcae1100fee30c2e4fb11007fdc6170e5963f03fdc61860a665301fee30c386138b81009d86c3ff714c0802761c929eeb304013b0eefc69ed8201d89443f04dc41027619c12648200809d866532360e0409d866209acff02027612ff484dd01009d85cc5034f40804ec2d3b2a1c6040276169d950e301fee30e4d5678a80ff718725ff667c07fb8c364af100603f7186635727cc01fdc619c8acd8200fe549319e96b2407fb8c3187fc0c203fdc615184490d02013b0cb3a2f4301009d8658cd37240804ec32b59e13c03fdc61a105ad9b01fee30d25feed680fee30cc6ae4f9807ee30cc454e32403fb8dc7380487a01fb8c3352f709880fc5523b1bbb5fe0, 0x209c9495baad9b810292c934763ef408246b9c456948a040bbcce67f3842020ac1068f880e801028cc74e09e08008299ec3572a188040a6b4ef9f703b020a69d3161036981028936522b5d180828c2256e9f3a2040a4465b541028020a74afd7c7b36010258c331203fd80823a329f021d5a0405eff4985ccab0209e255c6d961f81026750778182340825e909d2cc3cc040865b320b528e02020d8f1a08b778100e0a6038302a408099c0ad49a9e603fb6e21c0f986701fdb710e07cc3380fedb89b3c7024c07db715355cb91803f76e6d43cc48201f98c7072f159100fee5a5d6c56f8807f0333c473b96003fa771ca140ab301fb8c322fcae1100fee30c2e4fb11007fdc6170e5963f03fdc61860a665301fee30c386138b81009d86c3ff714c0802761c929eeb304013b0eefc69ed8201d89443f04dc41027619c12648200809d866532360e0409d866209acff02027612fb414ac01009d85cc5034f40804ec2d3b2a1c6040276169d950e301fee30e4d5678a80ff718725ff667c07fb8c364af100603f7186635727cc01fdc619c8acd8200fe549319e96b2407fb8c3187fc0c203fdc6151af3e8302013b0cb3a2f4301009d8658cd37240804ec32b59e13c03fdc61a1868dfd01fee30d25feed680fee30cc6ae4f9807ee30cc454e32403fb8dc7380487a01fb8c3352f709880fc556ae742eeee0, 0x4133ca881e8e8f01fdb6f4d655c6280fedb7a6f31e62407e4947073b1fe203f6dc2e5a73a1801f6a1b59d2463600fdcc48cb05d62807de9ead40b54cc03f7ab4ef9f703b01f7a9d1240266880fdd933748359e007ddc2256e9f3a203f6968b112401c01f798840f92bb700fddc7c89e28a5807de0cdf985717203f7a0553884a3d01f7229562ee6b580fdb75458edcaf407db70cf4087be403f6dc3853d137201fdb70f6491f7a80fedb87a6dfc87c07f6dc3b0de5f4a04042e3d415b0d50202176b01a89b1810100d22c9099e4081bf52731c7ca404057d9d8f3e9cc02054ad44b9eae701015cc05809c4700815b3de469d7040405111ce3c24d70204ec331ab93e601013b0ce83e13c80802761a8f1d6330402761a164b07502013b0d11dbde180ff718618d56f2407fdc617394ed9f03fee30a9ae6a8f81fe5492101aa1040fd6af7198c110807f71866532360e03f718665bac52301fdc619e09833d00ff718699b5d12407fb8c366b2918e03fdc61b35948c702013b0b542935d81009d85a968c5140804ec2d70dcefe0409d8624ea78540202761955392b00101d89336c6566c0804ec347264ee60402761aa4981e301fee30cc91daf300ff71866995193c07fb8c335c153d0040276192c22d6d02013b0c721b0f481013b0cc6ae4f980813b0cc6ae4f980404edc43012e440200ed42685aee780fc55dc2d24e6c60, 0x8267af9a724b8e040a9d2c15ac88f01fdb6f4d7ad71d80fedb7a6fddbbfc07e4947073b1fe203f6dc2e5a73a1801f6a1ba32748a400fdcc48cb05d62807de9ead40b54cc03f7ab4ef9f703b01f7a9d1240266880fdd933748359e007ddc2256e9f3a203f69def7d4fb4a01f7975ea60e48700fddc0d5c50ffa807ddff8fcb1fbca03f79ff2545770f01f7229566f56e680fdb7545841f51c07db70cf4087be403f6dc3853d137201fdb70f6491f7a80fedb87a6dfc87c07f6dc3b0de5f4a04042ecce0beee9020216d658293a2810100fea1f86884081bf6b3084b75804057db5d42a66802054ad44cd6dba01015cc05809c4700815b3de469d7040405111ce3c24d70204ec331ab93e601013b0ce83e13c80802761a8f1d6330402761a164b07502013b0d11dbde180ff718618d56f2407fdc617394ed9f03fee30a9ae6a8f81fe5492101aa1040fd6af28cf5c62007f71866532360e03f718665bac52301fdc619e09833d00ff718699b5d12407fb8c366b2918e03fdc61b35948c702013b0b542935d81009d85a968c5140804ec2d70dcefe0409d8624ea78540202761955392b00101d89336c6566c0804ec347264ee60402761aa4981e301fee30cc91daf300ff71866995193c07fb8c335c153d0040276192c22d6d02013b0c721b0f481013b0cc6ae4f980813b0cc6ae4f980404edc43012e440200ed05dbdd26780fc55a9dbfd90d60, 0x114a32077a7dd1c0824c2169b1a56604126111d8f225301f9251218d18c680fc92890c68c63407adbdbe0dab4ce03e49497f07205001e4949887aee6e00f96122d45aef28079bdc0c29cb3fc03e6dbfc09c085101e6fd74ba4d31c80f98b9bee43be580795d0dd38a438203e14a7675a9fa801e62d88637798000f9fc113351f6c8079d3a6c41fdc6203e72ba8a693c7701e56748f948a0880f925f4b9a3b87c07925268024031403e4949e46242b801f92528d1b67e580fc92946021633407e494a8b5a4c5a04088048aedb03b020440612c0118d810200489fafd11c08484321f468230040ec49806d6f12020fe0865c32a5a01041641081d4d5008411b9ad3d850c040f3356ab46e85020ec499502bbb20103b1267193afe80807624daf355050407624d2e54ee50203b1269c8925e80fe5492e2deebf407f9524a6ee182103fca9249bb6f5481fafdb89ddf665c0f840be7503a9c807e54932f96a22a03e54932daa2cbb01f9524d0b6d7e700fe54935d08f38407f2a49c1a5c84e03f9524e0d2e4270203b124eaeb86d8101d8927575c36c080ec4945ce2a22041d88e1a355e080207624c7c84dff010589b98a256f5c080ec49acd6e3260407624dccbe11701fca9263b20f5100fe54932ca33f7407f2a49988a1f780407624c6b4fdeb0203b125f8c15408101fc90b8755bd80802d26564f45940400b94fd73d8ac0204df6fb7aea9d80fbfbfb85dbd5120, 0x21165426c1b9f2010a78a6d7f143d808173c9873c907c040b9e3ad0e9f1601fb6e1737f72e400fdb70b9bfb972007c92930067ad1403edb865411e6da01edb8660f1a8d100fb9892372426d007bd011ac0f0c4c03ef0c8c20c273401eeed72f5831dc00fb3f9da13d1b8807b9c339e24c0fc03ed88f84bfab0401ef532d476f10600fc0a573c81352807c0ca95d3f874803efa694b1f4c6e01ee44dfee3942b00fb6ea3278b8a1007b6e1999883c1003edb869b6367c001fb6e1b4b0f47700fdb70db9aab30807edb86e7e8a1f00406b0423b53d5c0203581478fbf85010172809e8d7c90083323e1f0ca0c00409d865f9cc7ae0209204bd906e340102711c93bc0d400821d8c16094694040a2239c7849ae0209d86635727cc01027619976e26d80804ec3390dc42e0404ec33587a18002027619b5a2bdd00fee30ca51e8b6807fb8c320e3b1ce03fdc61890fa89f01fca925d48238780fb8c316eaefc0007ee30cca646c1c03ee30cc99cfe3401fb8c333841ff800fee30cdb7d34c007f71867c2d100403fb8c33e168802020276191f47a0d01013b0c904fa6400809d864ad72a800412a9d154c94aa02047c41596d7700103b1265b6d1f100809d866e6a70380404ec33d3fbcb401fdc6197cc0a3600fee30ccbc8023007f71866725b9a40401eb596627e3c02001e196d5c64400fffe3646e74e400801e198d5c9f3004018e011277a720202f44e3d3fb8d00ffc4ce84ea59a40, 0x46e65834520ac00215e10e0ccf5bf0111ae6a3b370f54082aed808a2c5ba041576e04cda89101f68d9c04fb2c680fb46de355c3ce407925262298806203db70cc20e975e01db70cc668db0700f73124cc8dc278077a7abfaf8023803dead3be90e19a01dea747e9b985a00f764d29e08ba700772bd3e5288e7c03db71dfb2e5ef001dcd21cc12d59b00f7c8c800307a90077e9aefdd88af003df2baa331add201dd7707166c22000f6f97e4cd9d748076dc331f8fd67403e1b7a5fedba8201f8a96f760d22580fc9e3a5225e4ec07e70b710943d52040ad4a76179b1b02056a81619f4208102969ccc0dfdd4084ec33159593700413b0cc72acc2602152b5f24cd0e60105523bd1a802780856cf791f3dec804144473903b40a0213b0cc6c170460104ec331f0cc4280809d866a1712930409d866711d0470204ec33409c88580fd8899e360f20407f6225611bdd1f03fa14a939b773981f75325b1112a940f718662b0baab807dc61994ef199403dc619948cf3fe01f718664a2e91800fdc619abb7778407ee30d0f95925203f718687cac929020452b801306de810228accce3a794080e7b9db7f310e041e4941fe7e8fe0207f5b53e4ef750102b8251aa9203c08047da0a9e12aa04009f7bb016ad701fee1b52bf802081001e1983ebed5c0800f0cc3bd936604007866138d6e302003c32cd28db381003c330636dbf00803c331bb196f004084bbb6bea00402094353050f3d000ff9a22d41877580, 0x8483ca66489d70042f89d3a56897a0209f129fefd2cd0107b25eaa2d04c0081422366573330040a11255f1aab401fb9892dc70cbc00fdcc496e3865e007cb1fe6213c6f803ee624e3ea350201ee624eedbf02c00fbc30c940e209007b7d7f40dbd8b803ed6ef707c099001ee12353fbf71f00fbdce2f4def53007b96c810e3e1fc03ef2cec20c290c01f006d8b6eacfb00fc27dafacecfe007bd5c994ffc1f003f03fbdd0aa6be01ef1280b101e6300fb991d3139ef3007bba8eec99e3d803f0c3ff14bd50c01fc616f06789c900fe407e82bdcc9007f28bfb50e544c04074966c79ad700203a507a529d290101b7e80ace1c78082a093b625f660040a824ef0735e8020b3f9849838480102e3fade010990082e0f5f6c12eb8040acca5301aa98020a824ef53685a01032c84860a9b200807003c0c600c8040710b738e9b7c02038611f21b2cd00fef8495003cee807fbe123098a37803fdf091c285f5601fce8dc9b356ee00fbe12776c8edb007ef849e7bb9bf803ef849e6f42e1001fd647e564f1a600fef84bb63121f007f7c260105432403fbe130082a1920201da6e873bc500100edfffc6baf18080a80d61d19f680402449dec4d96002009127a57520c01006cddab0ebd98080122525313150040091278c0efac02004893aaae24101002449d80165080801224ec96953803ff6cc01fd74060200321f42cee2601004893bb4a1fe00804893bda38c54040125737eb4f4202015c42f4c100400fd8a7ca18009940, 0x11a4bef890008a008622e7dbfe216c04533fa83ae1e9a0214cfe78103af0010f9bee3bd0b92808299fdd2aae2240414cfee955711201f7a7f3c081d7800fbd3f9e040ebc0079bdf693f833b003de9fc276db29801de9fcf033464800f6fe548b2e13f80773b89ad11eab803dbf2b7c27a2a401dc2327d5e9b3c00f7e35ebb72ad900782fbb323c4e6003de37a03330aa001e144cb845d10e00f8817e9da6c3f0078b56fa354a15803e25aacc90b36c01dfb8b938d88fe00f7a909a2df61900780098916e450c03e2d4645473ef001f912102e4ee9600fce9c8e6af454807e3aef6558b078040dd663b78c3800206ebc7021edbe0102dbf9e15c02d8085b7f3c0a7b9f00416dfcf0dfbcac02185a61babd6800105e35cba4ec70808638b8376ff53004176fdf99947460216dfcf02075e00105b7f429382720080b6fe78103af0040b6fe78103af00205b7f3c081d7800fe2bf909759dc007f8afe0d007edc03fc57f1dfe7bf601fa83ecc3411ad00f8afe7816d0ae007e2bf9e7ad24c803e37acd1fb4d4e01f8afeae59698d00fe2bf9e08e0b8007f15fd32c0df4803f8afe782ad1c6020107f3c1c5973010083f9e0be986808041fcf053ca1c04083f9e054098002020fe78cbbe7401018beddd2bf13008041fdc3e6819404020fe78103af0020107f39f49dfe010083f9d6fd177808041fcecaa512404018123ae7e1680200a8cb8fbeea7010107f3c081d78008107f3c081d780040426149efd99402041fd00336a3200f7d4b4b1f681a00, 0x20ea8256ed143a010b737d14da1e60082d2f84ba2c0ec042a245f8328394020a4e4ba78a10b0107dd315c9748440814e13a29cea82040a709d14e754101fbd84e8a73aa080fdec274539d50407cdd60b9c9016e03ef23144847d4c01ef613a2a652b600fb3f0c78fa22d807b777be4b0416803ee0d7517265f201edb8c9319f1cd00fc1c4cc706e99807b7bcda8a8026803f00a84cbc542801f0ab82d3f66b600fbf5fe66c35d1007c2c50788252d003f0a0599434c3201ef771c8f95fd000fc0019e7f61a1007be9865cdc071803f038135d55e4001fc331d4dfe96580fe1e63f3e37e0c07ef613a29cea8204076cf5ac49c670202e04e8b8cb678101769b2ea6a464082e669169eefcc040b813a327835e020bb34bd7079ef0102cb0146f40938082f9bdfa69aadc040a8571b34f59c020afc34b7162310102afd098410b20080543caf290d4d0405400a49fe54502025a9045f29ab80ff18274539d50407fc609d14e754103fe304e8a73aa081fd62bb2ba7e9dc0fc609d151c020007f1e8e98c216c403f2343147bcfe001fc764e916b0e700ff569aa7a07e9407fe8b269ab77ba03ff13093ca21230200aa70e5dd226810054e254533f3c0802d43aec85f5e04044274539d5040201109d1ac37030100cc75cfad7f0c0801d5d108ec06204008e2885df51b02003950398451581001e7da4e483fc08009ab2807da320400fbb8c6acb9f020057237cdce8e81002da127b074a8080736096e421bc0402245c5481f3e020256a869a0c3400fd1864bbe4eb900, 0x47aaf5e08d18a402173a1a3b64a900116d47d9079b7300858bcff4333d1c04533749cc9e2460214cdd147dbcb3010f9a5d67aaeee808299ba3bf1d27c0414cdd1df8e93e01f7a6e9aa6182800fbd374d530c140079bd2ee327db7003dd4a5c24fbee401de9ba45d5ba5b00f6efc14ca49c70076e63a511036d803db13cbb253f0401d9410b3ac50f800f6fa40754c15e80783b3cd0e8f69403de3c9d1c4e56001e1fd96b356fbc00f80d38cfd3fc40077f165f671e15803dfc9affec220201dfb48df5ee59a00f8060a350aaf18077a6ea4f583c8403de9ba7e0f9a1801f7a6eaec9277800fbd3754cab717007de9ba3c20e4e0040b6dd1e1067e40205b6e8efc749f0102db74cb1f3998085b6e9282974d00416dba3cb119480215452653ebff40105574804d652880843a27856b19900413b9e82e9405a0216dba3bf1d27c0105a27b16ec40a8080987007a3330a040955c64fa19c20205a0f5bdb504b00fe2b7477e3a4f807f8add1df8e93e03fc56e8efc749f01fa825e7179b9080f8add24e6b0be007e2b74bec70b5803e2b749b1dd85801fb67dcf5101d700ffc5023810df2008041b92460689004020dc92303448020106eb0e223bb01008375850d9c5008041ba8e81914404083749038acce02020dd25554c7701018a5d9b5a40e007ff70899dee3a403fbe6c43394ffa020106e68d4cf0b0100837306d8147008039816b8c3be404020dcfa4143ce020106e8efc749f010106e92b84a20808100ab5f4f38e4040421e81483bf4020437e5cd8991500f8b1e573f16b180, 0x84cabbccb79420042bbe01bff1afe020af9339ec4e57010af08a4a5f68e00829e717381f00804289328061263a020a253f50209f901079b973b711bd008144993492d9f8040a24c9a496cfc01fbb264d24b67e00fdd9326925b3f007cc5cb9db88de803ecfd6265284b801eec9955553b0e00fbdcddab0f689007bf7ce2c1bace003f066ac8a31faa01edf2177994e7400fbf6b0ae03add007bfc8ff2c2aff403f01a9d47cfcbc01f07a8cc34a89800fc41ac11d017e007c3922c3b4cccc03f0a7022caf8be01ef5608649638700fbb2ee671ba40007bb265a5d21c5803eec9b0b9c4ad201fbb2716ae451400fdd93269b334f007f82993492d9f8040574c9a496cfc0202ba64d24b67e01015d326925b3f0082ba64d24b67e00408cb7529ed66c0207bc24047095e01020ddaf68cfbf0081ae876d14e3540407a00d35f09b202074b8d9078a2b0101c49bf618ebd008046c28b2a9ac40404a8498d580240200626a6a62bda80ff053269838ee407fc14c9a8808b803fe0a64d4cfbc501fd0f973e6371940ff0c253c96fed00803130e3da3af004003c4d4ffd3da01ff4714c220ce3010031319509bd500801898bd1829c80400c4c5e8c14e402006264d24b67e010031326925b3f00801898017c307403fe773cad8656001ff3dc6b8a88de00feb404a0bccdf00801897fa1a002c0400c4ba925959e020004ad6717f7501001b216d9d21880801893353f04180400c4c9a373d2002006264d24b67e01006264d24b67e00806260dd67e5a804018cb573e0eb40201ad1dc5fc87800fd89e8ab81de0c0, 0x11f49218bfc9a80085a3d338fd55700457d7a3e17d28002154805794aacf0115f4348d939628085429b96738d58045181f53b70e1402157e36185acf3010f485dfab266280828c0f502c62380414607d4e4332e01f7703ea72199700fbb81f5390ccb80796b6bd1aaf11c03dd06b0c28ed8601dcb3cbf0d32ce00f7301d518c6b9007828abf25b5fe003dc3ba709d216401e0f76ec96c56f00f7f8dd1a4b44100780494e810299803e0630e99cabe401e122ed90c039c00f8f8e6793a9980078e859b460347c03e17bd8638a3e801ded9e4d35797a00f78f13dba021c8077703fd5b2916c03e20195435f82801f8a64c128e9f200fe101f5390ccb807f080fa9c8665c040b0000cd7e864020580003fd0d03010202a8fd00eb000839f8e7e975248040d83dc3bf84f0020c451313d4dd301030e3f75331a38082cf63f7552d14040a0c7346af92c020340fa9ebc0c00100d03f663347000801a08396a90400401a07d4f8470602012e6ec5df8a5010068159544b9580801a02f364bd0a03ff4477a3c8cdb01ffc7aaaff39bb80ff7d3bba8502d80801d4fb6aac530040204959ae741a0201a07d4e4332e0100681f5390ccb8080340fa9c8665c0401a07d4e4332e01fe3d156b725cc00ff189e559c1a2007fc06136ff8ab404005e390c1b3020201a06d4b5be000101385a153f1a58080340fa9c8665c0401a0556b7c33c01fef585e43c14600ffc1ba8dcbd07808000cfa2cfbaa80401a07d4bfd3760200d03ea721997010058019be3f978080d03ea7219970040346ee0a66228020340fb7d7d92600fb1a2c16650f700, 0x2113dd5e1f1170010d3a3798bd90b8082ca48c377b2fc042b820ad916b020209c930dbbce3801099866692389f0082a6ace8128854042814cfa1b7e6e020a45a8430bf6e0107b436f1528a6c08148afe44360ba040a457f175da8501fb5a4d24f5cd480fdb23d77937a9c07c1f56256d299603ee221540fa1da01edbd3f13fa65c00fbc42cd0082de007bbad68a2a1d3803efe920366848201ef7b1e773c66300fc072edbcc654807c0d0ac2aed80c03f05c8887806c201f0bc91e2b22c000fcbf1a2b0b1e3007c67f53fada24403f0e8ed6c602c401ef97f3a446d8d00fbcce2346ff84007bc2effa6da6ac03ef0b7e8d4311001fe1ac05bc3c7b80ff0d620266f2cc07f86afb44526e604059330a60801f0202c9864e4fa2b810107d4d94593ac081e423203ab9c40408756d4e45c8402056b96b969003010126e7579f4050080b341dec7ded0040215521c671c60202548d84605aa01007324af1ae7200800ed5350dbb4b0400e5f8cb4233d0200730be74b39d8100012b5946882408000a19c90d37b03ffb6f7163cab1820009777dbb12340ff7690540ad2c80800627e17dd48003ff47affc14f620200e5bf446f1ff0100396fd11bc7fc0801cb2bd388b0a0400e595f9e064902006bd364e9961810038a1193296bc0801cb39d698ada04015046107e7b40200e571c1f89c60100ac5d58da93d40801cb7e88de3fe0400e5bf446f1ff01fe4c8e4daaefa80ffb9c2adc66e7407ff9d2d74095860400e5bf434c223020072f19c2e90b8100255ef8eeb3680805db136beec780401cb67b9e58d80201cb4a60712c900fe515f81a1cbf80, 0x482514bc15ada8021ad571e1f6c320118441174281e50085856b15ab1b8804527ce1a4c28ee02137b693ffb9e10112b04a88e8952808534b1017b63bc044b1557a65a10a0215047f42f14b6010e70cac6d9cf280829017a0deb1ac0415047f42f14b601f771e5dabf5a800fbb64858f4a1800798321d76bd21003df08fe85e296c01dc915376a4fe700f812be0ac47d18077fab12f729ed003e087d59da84f001e23f794fa139e00f84ade14a250500785695e26735d803e1ab128326ef401e26af17a1c6ac00f8e0ce208205b0078cfbb844b6f8803e2c3dc4ce66f801e021e8bcb3c8a00f84f7c2c5fa100077c3360e3430d803f1c8fe85e296c01fc723fa178a5b00fe391fd0bc52d807f1c8fe85e296c0409d262d59a3120204ec5d302661901029f637d1717b80838246bc6bf084040cea8fd7f7f220206b6d29949d800101a90de756e650081a482546051a4040588c3c22713c020492703b480ed0101223fa178a5b008028ed4decbc0204024a562b02b70020035503c4532301008c330cfdc84008021f0609d11a204002f46434af1b020131eb169272a8100c94a5d26cdb807fb4f8aca59afc03f9d3c8f8088340202447f42f14b60100911fd0bc52d8080488fe85e296c0402447f42f14b602011dc40a1a54e0100911fd0bc52d8080488fe85e296c0400f8e6be16348020175aaaccc1730101b35f7234f888080488e2a5596400402447f42f14b601fc9673c8b60e300fedd089956b99007fdf59a588fbac0402447f40ab4fe02011d63ba6b1840101223fa178a5b008119e79f3338980401289dcbc8b6c0201e72af10efbf00f88ec5d7afd1780, 0x8466d489b16598042e9150f0ffe3c020b92dd6ad90e5010ba2a549d0a970082d1b78fd788c0042a2fb248992c40209c112495b4a70109807059343d680825dd1497680ac0427d4286315fae020a60e0f89a14d01076e2bbb9b3b9008132c73087f5c004096655bb1f1e601fbad8a24545f400fdd79c0e782a3807cff5ae410369c03f039b7cdd888e01ef8d4485a6fe500fc299cb384498007c45416baa427003f00f203e0449a01f0503809dae2c00fc437314551e2007c7ecaf7e7b2dc03f2da68b3c666801f1ad88e51e0d400fc8e6b1a44f8d007c85e1cc29adbc03f1d9fe4e830fa01f089048669bc300fc3e034946a7b807bff23db348c1803f52cb2fc012a401fce7d93d4d6cf00fefcb65cf1555007f8149ae241bfc04037f3cbc0557a0201e94df5fc8ae0100ac2c3f4395f0080bb995b5119e40402bc8f75216f6020379d8c75c2840100f28afd773280080ef86163757a804030662fd134160202bc8f6b012340100af23dac048d008014997908d4920401b9212a53f4c0200607a4b35fd10100328d35c2e0580800697ffd009e20400af23dac048d01fffe418804464810071cd25ec23b807ffad55c71281c04008d9d7a06efa0200831e29e6e7c01001aa159b3af000802bc8f6b0123404015e47b58091a0200af23dac048d01005791ed60246808013f4cbe0e4fc04017ba4298f53002015e47bb5cadc010106b5c8206d3808017ae2813c36804015e47b58091a020043a49d5f39f01000ea0fc3c6af807ff56d2ac7a43404015e47b45d93e0200af23dac048d00ff5d7521bf7a7807f8b0ac30a5b9c03fe318aec6551c02020c57c43eae700fc3350322df8640, 0x11bcd573a0ee1e0085ee42c8d59acc045c9993b081d640216f60ab4aab8d011737457187ce68085767bada3a80004500a5861a19c80212d24b5c273df0112d3abc9569f180848e2f4bfbf894044cea5e130f67e0213eb5f4e43fa6010ea7ba34ee1df408247250d0acd8e041214f6aebdeef01f7ed25ef50d3780fbf692f7a869bc079f1dc737c9e9a03e086da53b557401dfb497be7054600f79fa0b1830138078b89ecf43149803e0fd0a49728cc01e0651d81d6bee00f875c4627a7e18078da7231af918403e256abba87a6601e3168ab17d21e00f90bb46e5a3378078faa1d2239d5003e36f75844726a01e0cd81f4147fc00f86599ea666a200780f949ffc15d003ed593d6c68dd601fb9d497c75aa180fdef8735666b8407ef8e7dae4781604037a5668a423b0201bc8ab8a1a968100a692f80e9d040814d25ef764ec804041f6f5420350020640909c495110101d3f434bea6d8081cdea663ef1280406ce25258cb940205fe0443f88fe010109a55499582808020f63d62d2a30402902dd68acff0200772c47a9ea08100a692f7a869bc08029a4bdea1a6f03ff3416554f73f8200af7b55ecfbb41018552fd7380080801f862866143004037030b8892ea0200b6844a2c10201001ef72f19688407ff8fe1c615cb60400394856436ed02014d25ef50d378100a692f7a869bc0800bcf5680b7d2040351eb1ec0b3002029a4bea59df30101897073dd476c08024314b82e18204029a4bdea1a6f01fda6c30c5e1f780ff5f5d97316a5c07fe2f3e270875e0401dc6bae2f23102014d25ef50d378100a90cc1ca75c00814d25ef50d3780400edd84166a1e02039d7c4a28cdc00fc26e332c0be840, 0x2135ee3f18f4e8010b9c715237e928082eb64c619e9d4042dc62c117eed8020b350aa75635a010b1f8a0a08af20082c50541df795c0424fcdeaf0c4f402085922218901d0108186d3fbbb7b0081ee449a5a447404262753a123dd80209873328f2a080106fb06cb56876c080d943bd587d220406318a759265d01fbce042047de280fde700e61d0c7407ce52c71dcee5a03ef9bd9c7dde4201ef96fcfbd72b600fc103817942ab807c4b7baec94a9803f0b3083ad652001f033d0c65becc00fc2a0e7864ff5807c2fea5f47721c03f0e806f9e2d4601f147f6755d92200fc75067e54da0807c6c7d30398ef403f1746bdec294801f07eb2a858b7800fcf8cf69e335b807caa3f5b806c2c03f82976fb0835201fd5679f791e0c810020f8ab0b1d04080110908d2f6e604017cd0b63e35f0200bfef6d5626481004adf9f6815040809a83ebc2789c040256fd03ea35e02031446579bad20100d926618713b8080d6217a4738e00402a0d08d52c64020256fcfb40a82010095bf3ed02a080801090c0ecbf790400f78bc65114501ffa544a215d9581004adf9f68150408012b7e7da054103ffe337796a3248200aecc4ba270bc1010f18138a74200802bcb00bd28c803fdf686d464a4201ffa97f17e9a9001002fd82a27e6ec07ff177aa45d45a03ff5271481ecbb020095bf3ed02a08100412e966bcab4080256fcfb40a820403c24edb3f1fc02012b7e837c7030100d0a3a925b8040801632d0777c7a0400a35c465843f01fe8dab41cddc280ff76b4a7b95aec08014a9e3ce575604012b7e7c7d565020095bf3ed02a080ff436be1d37ef007fb6cef8674c7404025a1f25f3f3e0202309d448b72c00ff2c62d96df7d80, 0x48aaa7c284c124021724af0309a3b0117977664bd9be0085c233cf642434045942831c47f5002150c5726381be0114e155eb9d0ee0085329af9a1dee004553a39e32fdda0212479f6b15de20112a6d78fe02570084e37f77e93bec044ee4f4dd09e880213262a7b7dd4b010e2e1f0b2e51b00827722698b3d500413b913444be4601f71cbf3b77b4200fb8e5f8fa34f580795579f031307c03dc72857b3ca6a01dd8470db5769a00f787e25cc4f9b0077e818ac5a237403defe7c386285e01dfa8f8d15749d00f7a53e29151130077b0f5aa54bc8803df1491a2dd0a001dfd47099d285800f83b2de86f8c6007869f59437f7a803e0cd3960d609601dd8b67dde0e3600faa5f6f194125807a668673d9676403f178674030f2801fca0eb74d002300fd7735c1daf48807e7357fb6a00580400fc826efc6d202007e34510867501003e629d9f77500807ca14c59b0f40401f281e8e453002036d11d0d3d540101036daed3ffc0080fd63e0544a1004028624c9bcedc0201f27da598b1801004aa7e72c1d280800f91de420a340400f9077fcef1a02007af337e291401003e4fb4b316300800f9568c1a63004007ca958066480200baf5e896c1e0100f93d97bb1a1008032366dd57aac04031377609538801feeb2f120b87600ffc0c1ef0112a807fea13dd0fe8b403ff5129e5264b202007c9f69662c601003e52b89db6800801f27da598b180403e4f479fd8940200f93ede849100100242427b1dfe00801f243c62b5a40400f933267978602007425623d2d300ffdfdaf92f527007facdfef0484740400f93ed0865d402007c9f69662c601007c50ef6ed4f00801db18f8b46c00401f8c1faff4900201f278b5c51cb0101764c926b81080, 0x8459a06cca8ba80438bc6cabe21f0020a9c9086689a3010ac9bdb5cca2d0082b447e6ca134c042af108be3bfd2020a465f87b7368010a30c91b1b6fb0082895a79f7b994042966d8b2d59f602095fec082629801093a9a2f09b04808271f3bfa2f66c0426734d79375ea02099cb6e3160220106e5c7608bb424081339a0c6f8cce04099cd0637c66701fb6e7066b2c6280fdb73834b10ec407c92cfabf6cf7a03edb9a87705fac01edf6c19532f1a00fb98e2ee77794007bd64c5b4e9e6c03efe3418e82ecc01eff1bc25a1f6e00fbb2b976e296a807bc09c72cf021803ef0caa3ac13a601f02bb629b955500fc3e5e87c4b71807c21741ccccc4003f43cadd0eee3601f4f63e3f2feff00fdf96dda21702007dfb045e0c2ff003f7100d8ab00ce01fdc2680a7e38080fed6a202903e6c07f7a13e699297e0400c4be82bc2ef0200627787a18ce810017664eaa73340803cb06f97fa20040079a6e234f8c020136f02879bb201008e81734e92c808064e038c500080400c37a4e14c8001ffbb5ba6602c200ffcb26191b698008002120af4ec87040020aa411cb9f01ffd7a9b626a9f81000f34ee52bbec08003cd414948a704001e6a353fbb382002d9ec9a088141003cd36394b1a00800f34db3671c00400f34ce84f01e01fefa7b63bbfe400ff7b77f616d2c407fef080ac5197a03ff781433fc91d02001e69f4cf8a381000f34fa67c51c080079a792cdf7e0400f34d780553c02003cd363dd71101002d9dea1b5e1c080079a046186ae04003cd29cb0c1f02001e69761e90081000f34bdb99b04080079a5d6f2eae04003cd35cde57302001e69d5ef1d681001e69af00aa7807ff4f5fefe6e7c04007cca3e61a5a020079a61bf91ba01004c643a9454680, 0x121a8eccba3ceb00881c34634b28d004728eed6bcd0e60215ca34830294e0115ebd2065a5a800857497bff029d8045417ce638d98002148b9f66708c30114607d4e9d81a00851264d261fb900452657089ea0360212f06a3226fdf01129a45995285d8084f8939e83c848044ce198a9431f00213053b0df04b9010d8e3f7868d4600826141d526dbec04130a3e4977c1401f6dc33d5809e500fb6e19eac04f280792526837f304c03db70ccc99289201db70cc7e3a55700f76c03224052a8077ff52d71b65b803df21afa8de10401dea7495bc132000f764d2eb1a6f20077708aa669dbf403de13aca9d1eba01ded6c81ea216600f7fac19aab24f007802fc2a714d9803e5d944a6ddb4001e908d25aadb3800fbf575e612e4e807c27f439a724c403ec7df35394cae01fb0c2a4ffff1600fd78c56835531007edb579b927c2404010aecb220710020085ad44aefbb01001e1a831eedb00803c33229e80f40400f0cc8a5967602026b5f45df6530100f09c5ff7ef58080bcfcbed77300040184738fbdd3401ff1eab679aaa300ff88ca1d612b4007ff73b95b53ef803ff855f37e6bb601ff669485cfbd201001e19a6491b1808007866fc7c0d404003c338e5a12e02005a4ce2136f301007866363627600801e1994df6be80401e198f9f77f401fd2b38f05d6d200feef2f5e3a303807fdd7ae570d1f803feebb4acccff602003c33509939401001e19a84c9ca00800f0cd01f4b400401e198d7332e002007866418503c01005a4c780573e00800f0c95b99ed804007866103604402003c32d417a6e01001e1952838e280800f0cac710e0404007866510f91202003c334f418d901003c331ae665c00803c3314dbe1280400f712c481b680200f0cd64bad600103be7d1c443dc80, 0x21803ba4e40014010c7fa81c42722808348d8af4fbef004323badd3403be020a8b7e7da0541010b23ccfb04e3a8082af91ed602468042a08fe85e296c020a45bf446f1ff010a303ea72199700828931b9f4aeb804299b9e2abb9440209542602f25be010968f33092d4a80827c48c567d02c042670c73b0d11c020855e708ffa030105cbdfe176e9580810cd8c9a462580408643f139b94201fb6e1c6a58cc900fdb70e352c664807c9293cb73dcd003edb869151e01801f0f8911fc13ce00fc315e23fb451007c6347aba1bda803eff97dcc96f7201ef53a5a890b3d00fbb270e5bf769807c4ecf2212f44403ef097038795e001f8c95faf8f66c00fd71c67fec66e807da2933239464803f7b258514199e01f89c36b80f37900fdc513beaef53007d96cda4f4d91c03fe36b1821e39401ffe782c4f947901000ef3917579c8080078285f1e21c0400b239adb39d6020058f5739b85e01000f10fc0202d00801e19dde8dc700400786a14caf5c020135b2e23d5c40100985b910628880805e7bc8d3ae080400c239c7849ae0200786635727cc01001e19356e31a808003c3066032fa04003c31f361b3202001e191b409dc01000f0d046f293808003c3508c00b604001e1aa74775902002d26e25805a81003c333a7a2ef80800f0cca646c1c0400f0cc5ebe6100200059fa6ccc4501000f0c6e140c38080078629f33c2804003c314f99e1402001e1a36831fd01000f0d1bed65c008007868237949c0400f0cc6ae4f9802003c3320955a801002d26469e39e80800786508bc42c04003c30ded58b802001e1970ab9a301000f0cb8fc9e9008007865b669b6004003c3364c3cf202001e19d9e1d9601001e198d5c9f300801e198b0332bc04007b8b021073a02007866a5ee13100fa7f1993d571ec0, 0x411c99ea0fbf17020827fc9bdc3a30105fca0e1e4b4780818f3112fb2c220417bb7e2728d70020545bf3ed02a081059505ab9a7d2408157c8f6b012340414d69b5fbb52c020522dfa2378ff8105181f5390ccb808144987eab7a500414cdcc101b7e20204573a3c377ba8104acdbca8b7fe80813e23cf8902d804133860d1fe137020411e265da9eb0102fdfd7eca700c0807e390987d8660403f2a37c88c5501fdb70fa50228a80fedb87d281145407e494a3671211e03f6dc35fd141a801f8bce553d12e300fe2ffaa4fb719807e42b87f96c15c03f83461f9ccd7101f7a9d3c744bd580fdd93b6b0b3d5807e3467d2e5fa7603fc346905b0dd001fc64afd7c7b3600fe7b56c5daf17007ee9a069b3175203face70825789901fc9fcf9f580b280fee0e197a4194407ec35b172d757403ff886f5479a5e02000e791ae8af981000772c9e215c408003bffe18a4ae04002a7c406f031020015615d924d88100078ab38444c40800f0d1892388804003c36d584d8002009adb17feefb010030c05809c4700802f3de469d7040400611ce3c24d702003c331ab93e601000f0c6ebfe21008001e16ee214b704001e186b63c2b02000f0c55e9f9d81000786a06c2b9408001e1b7604bd704000f0de09925f82001693b8528e441001e19ad0338d008007866532360e04007866209acff02001ca42338abb010007860c14901c08003c2f89d932e04001e17c4ec99702000f0d712c7be81000786b8963df408003c350e1eba20400786635727cc02001e19904aad4010016931c98c28408003c31ee0304604001e174ec994f02000f0cb24b4880100078657758b7408003c32a58207804001e19d7f8aed02000f0d133389c81000f0cc6ae4f980800f0cc454e32404003dc6cc9ee0a02003c3352f709880fd030f8a9689460, 0x823e94b60955160408a0f5ee3d305020857b00772580010579a6599ad1d808167daa6035b4e04155648835d2f0020545bf3ed02a081055692f7a869bc0814c13889f9adc0415047f42f14b6020522bb0d3113f8105181f5390ccb808144984faf01400414cdc93ddcae4020440e955aa4a78104c97bc3b727c80813e2380aa5c3404133860cf4ebc10203f528dd8431f0103530bffb1a9340807219fe4066ce0403929ee80f41b01fdb70f9236c5080fedb87c91b628407e494a2f64dbc203f6dc3665ca6a201f92e8fca3c2c700fe459839fe9cb807e6a94ca4b32d803f83a48c029a9101f7a9d3669c73d80fdd936cee66be007f082256e9f3a203fc34770e1f88c01fc64afd7c7b3600ff032316e9da7807efef6f35febae0400bdff823170f01faeb20403c8b880fed599e4a012dc07ec0e72a95ceac04003bb56fedaf202000ed80c35e1c8100077d7723898408003c19486ef1204001e3d38cc69902000f1ea1c4e38810007899e4c474c0800f0d1892388804003c36afee10c02009adac772b27010030c05809c4700802f3de469d7040400611ce3c24d702003c331ab93e601000f0c7b80c11808001e1733f02b304001e187e2f26502000f0c59f0fce81000786a06c2b9408001e1b7604bd704000f0ddb3a77382001693b44b8b341001e19ad0338d008007866532360e04007866209acff02001e11b50952b01000786101b932c08003c2fc4eab5204001e17e2755a902000f0d6d2578d81000786b692bc6c08003c3503615ca0400786635727cc02001e19904aad4010016931c98c28408003c31f361b3204001e176194f8902000f0cb24b4880100078657758b7408003c32aae0b6404001e19d7f8aed02000f0d133389c81000f0cc6ae4f980800f0cc454e32404003dc6b9d37d002003c3352f709880fc64ba2206f2060, 0x105d3286db5b01c0813bf1cfc33f0e040713ee67860090207453581f31620104f64ed2bd62f0081598a0f0b674e04165739b8a8afc02052e80c6a352081050e9a8ed4d3fc0814a6fc823d5b00415047f42f14b6020522dfa2378ff810517d97139d3400813f29e1d9f29c0414cdb4e26b3360204c02fffa66668104e39c4f99945808123a0109abcc404133862bd558910203b578b6df39e01039a5cbc97bed408099c04af3c9ca0404ce0254eef6f01fdb70ec78080380fedb8763c0401c07e494ad687dada03f6dc36fc2587201f9b2f0720a61d00fe412b3600e15007e35316bccf3d803f7fc41b45248301f7a9d2b8d38e080ff05346378ba4007f082256e9f3a203fc346826d788e01fc64afd7c7b3600ff03ea7cbecff807eff204dbca47e04002c89326818101f9ec4d938798280feeebbbf12531407edd748556ce1404003bfe8f3d49a02000efa99b3d2b81000782935e96fc08003c2b629e0a604001e1df507f8b02000f0efa83fc58100078751a0b2540800f0d20a03ea804003c3565af15a02009adace290ce010030c05809c4700802f3de469d7040400611ce3c24d702003c331ab93e601000f0c8c48a33008001e17e524b1f04001e18be9f57502000f0c64ae5a6810007869f147fe408001e1b6b475ff04000f0ddde9ce982001693b6fae2941001e19afb2903008007866532360e040078661deb78902001e18965938b0100078622e6f6cc08003c30406c68604001e18203634302000f0d6d2578d81000786b692bc6c08003c34fe02ade0400786635727cc02001e19c7552c7010016931c98c28408003c31fe1f10a04001e188e4b32902000f0cb24b4880100078657758b7408003c32b03f65004001e19e006b4f02000f0d11dbde181000f0cc6ae4f980800f0cc454e32404003dc674049d402003c32e0db08180fc1d3563768dfe0, 0x206d60d76fe64780fe9e470277c65407f6353125265da03fa297a046933d01f9f2efbc74b3300fb6e155773a9d007ec77377fe9f9203eaa69b9b1bef001fb95a9c5ad24880fbf692f7a869bc07f07d495f6e95403ef30e7a8c4a7201fbc2be3ab97e980fbb8263b970d2807eec993492d9f803ef4dd58898b1c01fbca47080df3080fbd3faf4213d8807ef038c076c59003eeadf5749883b01fbc6bc44c9b7700fc95c9a809677c07f6dc45c5e4c5e03fb6e22e2f262f02021053d95853d8101083d6694f94c08112e9cf35eda60406c3ee5b9165402056cf29cdac630101d6f2e3634ad0081c1dfd2160e84040772e8a6d8f4b0205b9d0eb0489d81015d33010facc008160166e2de55204058feeb1db2ce0204dff792eed680100eac0261114900806cca1a87e65e04012aea8c7a349020085d3fa61aec810036e8c2d27ecc08026dd5391f134040095128be083e0200130bc6758d18100078fb18abb4408003c3bea0ff1604001e15408aaf702000f0aa04557b81000784deb280440800f0b425f92fc04003c2df61218c01ffc8a2d8e36e100fff15445ed11580802f3de469d7040400611ce3c24d702003c331ab93e601000f0d051aff1008001e1af5245b704001e1a393277302000f0d21f7ea5810007860b68ba4408001e16cde932f04000f0ae8c38ed820016923dbf6e641001e194baf197808007866532360e040078665e5ba9902001e1a1e590d701000786a51f047c08003c36961e8ee04001e1b4b0f47702000f0b9dff18a81000785ceff8c5408003c3035af0ae0400786635727cc02001e195e9edcd010016933975adcc08003c348280faa04001e1a6c35f3502000f0cc91daf3010007866a40ef1408003c3366d29a804001e192c22d6d02000f0c6cbc60881000f0cc6ae4f980800f0cc6ae4f9804003dc22732ad802003c33d686c2e80fd42dce27d048e0, 0x40dae4dcca622702046227708a15f80fe9e33ef41c50c07f6338a7538f2603fa2a8f9500ef301f9f29eccdfd2500fb6e1556c7d3f807ec764b74f27b603eaa660c1fbd9e01fbc250505dcc680fbf692f7a869bc07ef5ee1b8e501403ef362fb0136d201fbc2be3961d2e80fbb8263aeb375007eec993492d9f803ef4dd58898b1c01fbca73984f2b680fbd3faf4cd136007ef0322f5d31e403eeadbed82e52101fbc6e335ebfed00fc95918247b56c07f6dc45c08617203fb6e22e0430b90202109dc765363810107e12f5c849c08112fe23f10e160406c49d6f0ddc202056d000588a320101d6fc5fe78180081c21c72a468a00405bb4efc291c90205b9d0ea488ff81015d330063d6e808160166ed9bb2a04058fc531999e00204dffa7eaf6470100fc44c0bc96500806d134e3ea32204012aea8c7a349020085c6de390c0810036f814d44fd408026e99ea3dfa0040095c578bb3d60200131e5d7e0548100078fb2e266f408003c3bea0ff1604001e15408aaf702000f0aa04557b81000784deb280440800f0b42b57de804003c2df61218c01ffc872cfec3c901000b1e14cb08d00802f3de469d7040400611ce3c24d702003c331ab93e601000f0d051aff1008001e1af5245b704001e1a393277302000f0d21f7ea5810007860b68ba4408001e16cde932f04000f0ae8c38ed820016923dbf6e641001e194baf197808007866532360e040078665e5ba9902001e1a1d0161c01000786a4732ea408003c36961e8ee04001e1b4b0f47702000f0b9dff18a81000785ceff8c5408003c3035af0ae0400786635727cc02001e195e9edcd010016933975adcc08003c348280faa04001e1a6c35f3502000f0cc91daf3010007866a40ef1408003c3366d29a804001e192c22d6d02000f0c6cbc60881000f0cc6ae4f980800f0cc6ae4f9804003dc43012e4402003c33d686c2e80fd42e859917ee60, 0x817aae7252567e04080c29f2d2075020407434e753f180fe629a2dcaaa4407f56a8a55eb74603fac54e9976e7901fad0ffa48ede500fb6e14bf150b4807edb8aef74b96e03ee38999316b0401fba9a3662f4d980fbf692f7a869bc07ef3d03b726d7c03ef847f42f14b601fbc2bd2b8c05b80fbbac314c47d3007eec993492d9f803ef4dd5fc0c5ee01fbf6c46dc6a6c80fbd3fae7605e8007efead13a6660803ef352d33a648501fb8d2ec4c119400fcdb6b65dfeb0407f6dc50834245e03fb6e2841a122f0201f790592c52f8100fbe50c30c8dc081054ac660bdca0405c8c87cddd9802052b65d45c5d90101b7e7b4cc9cc80816deabd70b7c00405d6160917b970205b9d1cd28e7281015d32ea3d4610080f9bfc4d8e14e040459ad87de30402053d02a0339b101008d8ed22834f0080526bbf961bb204012aea8c7a3490200829a73c045781001991db27bc2c0800f0d352482bc04003c3e1078e9402000f125f16e6281000788b5616b8408003c3aa7defc604001e12bed81cd02000f095f6c0e6810007827122fcf40800e95cb30eafc04003c2e0e3c2b2020028b3434d9c601001fc2a64159280802f34358dfa0c0400611ce3c24d702003c331ab93e601000f0cf702745808001e1ab4b42a704001e1a1ba9b6102000f0d173a8cd810007860d6c3bcc08001e16de053f304000f0a90294b7820016920d6b49a41001e18f269004008007866532360e040078665e5ba9902001e19f8c24630100078699b5d12408003c363ad4f4204001e1b1d6a7a102000f0b5ee693581000785ae1b9dfc08003c2ee36209a0400786635727cc02001e195bef85701001693381e021c08003c347d224be04001e1a7c51ff902000f0cbe6051b010007866995193c08003c336173ebc04001e192c22d6d02000f0c6cbc60881000f0cc6ae4f980800f0cc6ae4f9804003dc43012e4402003c3460ccd6b80fdaedd528ce7be0, 0x121a8ecdb0b3d70083d34ba88fbf40041e2ebfe4799aa020f178da31f36800fa5b67aace6e8807d4c1bfc24ec9c03eb28f0afcae8201eb78287192aa200edb8661798348807b6e69a8a03af403b8e4f5913908401ef60c860774de00ef5ba80ad2b34007be6cb2feaaf8803be05d1ce97a0a01ef0b3b324b60b00eee0806d073cf007bb265a96ca0cc03bd374a1d75a3401ef797dd8c621e00ef4fe7fe88e3c807b98948702257403b97eda12c730201edb8666c7cfbf00f24a4d1f908dc007db754701da32003edba8360feab6020729f88abf81b010395334b2c17f008477089dbc06940419b758d098aae0213b0cc56507b201054124c1f8ecc0085b7abfad166a004172646f36dcf00216e7483a6b63b010574d06c95e2580838c95459fde80040f7c5aa5e708c020c49068227a87010174d2b2420d1008149aefdb183880404ce94a1ac6f8020209be8cd4db801007f4aa71491e80803c3322f46be00400f0cf1cebb0e02003c34791b48d01001e1a31d046e80800f0d1f9e7de40400785a66382c802003c2d331c16401001e03d6e447180803c33023941140400f0cc3e773b602026b5ee1d326d0100c301602711c0080bcf791a75c10040184738f0935c0200f0cc6ae4f9801003c3324cac60808007866b0f4300040078667df0b3e02003c3341a7b1501001e19341685f8080078636b41b3004003bfaee4131e01ffeac1e59ffb00100786612f468c00801e1994c8d8380401e1991b75b42020078664d9c8f201001e19a8e1dec80800f0cf4fef2d004007867a7f796801ff49929f4d21800ffa58e1cf68cf007fa51fbebcde000401b2bf6f1f49002007865c2f9aa601005a4cb22765380800f0cd31943b4040078673f4146e02003c32f98146c01001e198b7afb300800f0cc6e943000400786608370b402003c32e5066ae01003c331ab93e600803c331ab93e600400f71430f38400200f0ce3ad186800f9f908e2d92a780, 0x2116540590a856010eb7e83b4aa4900819e10d83d6142040bf783c0ae0190205fbe51b0275680fdb708e7012cc407edb842fb5382a03f6dc27adc520901f6dc2da57e54f00f6dc331c844eb007db734d7e7cf7803dc727dac1055401f7cb7e7f3e3d000f7532c04f64eb807dff91edc79ea403df08418b4881a01f785bf460d08e00f770444e94cdd007df02ba6dbf6b803deb04080bb50e01f7d48561998e700f7a7f3dba17e8007dcc49e2138d3c03de23860ebb5b801f78056dcf164e00f94e9cb648901407eedd7e6f937ba03f76f040cf6bff0202cd3e013f7578101668617ec1f1c081d893093d04660409d865f9bd4840209d8663944d1e0102a09266ef9458082dbd604db0ea8040b769df729d94020b73a3fe35e9b01022bc507532d58081b1c1915da6c804085e7344c6912020594ac1c00d360100ad60ce0df3400808e082a9238b0040255d51c303b0020104db5416e7901001ea2a4cac5280801e19914769a40400786a27874c402001e1b798309481000f0dbf70dc040800786a34f401204003c2f9b9328102001e17cc71e8581000f0bab2771ec0801e1987cb2424040078663bf92da020135aea76b9ef00fff6e7ef4a213007fa8d13a8736700400c1c1dc9c8fa020078663b5da6001001e19958dc3f008003c3377a0c2104003c3349fbf4b02001e19a655a6080ffdd83303c504c07ff75fe4fcc45d03ffaec5dceb3b881ffa78bd5b1d69c1003c32f2ee0af00800f0ccacbe6580400f0cc958a29802003c3331d1e2501000f0cd5da2a640800786704bc3f204003c33825e1f901ffb0cadfbcb5d80ffd8ddda2fc12407fdce42873af120400f0c867aa35e01ffdea6c51fd4d01002d265744df0408007866aed153204003c331c5727502001e197d8f97d81000f0cbcbf460408007865fa15b8e04003c32b52d31502001e1959d06bd81001e198e2b93a80801e198f833f5804007b8d2e6494c02007867651bc9300ff1fa9de0a43840, 0x4625585a4d4ee00216eb7d89797760116e5df01aec590082c057ef8fd752041628a7c45009b020b143b70ef19680fb1632927fa60407db93eddd5ffde03ee6314bf700d301ee69fd56aceb700ee74a079869d5007b9d783fef1eec03bbd5d8e0c946001ef53594638ef500f09686225b78c007c1e062ae27ff803c102e61aac74c01efc7e0fbe44b000ef9cdb6dc0f3d007c242f5a3f25c403c028ea0d6f50601f065408ff0ba200f00c21c4bd80d007bc7a24de62af003c1107e821756c01f1145b4c3cecc00f3ea27f47c661407e6372d63a406203f31b5b761391302054a4bfca5d178102a525feeeff54083f7bbf28312a20412339d85fe18802152940f385a3a01059f41ee1e28a808615c91c88686804170215d5d55a80215806d51700c20103cbbf66c206d80830e7324b2da24040af46e952ab7c02073671459f5b20101b8debb9f8748081ab571e37b8840406241eb95c75e0203822b2929cf001009b625860d2580809a503cc34ea804026947c63bce402009a53b29cc9081004d29e60f438c0802694a077e2fe03ffc0b285d33e501ffe00d00cef78810016a58fc972b40809a502c24301c0402693ecd26b4801fe04b2c65325c00ff8ca3762d47b807f6b6756cf0cec03ff1be74e3d43202026940f2589d201009a503c962748080134a0792c4e9040134a0792c4e902009a503c9627481001749670b891c08005d5fdef31c904004fadc845ede8200444d331a06fc101249f50251c400804d2825b74cac0404d2820f8391a020134a0792c4e901004d281e4b13a408026940f2589d2040134a0792c4e9020083785856fa78100413d3b27f5ec07fdbbc98e06c4603fbdd33414758401ff74b0a54cf9e0100e77844baaa1408026940f2589d2040134a0792c4e902009a4ff5c768681004d28019005e40802694034b740a0401349f8d4fa1702009a4fe5538f981009a4e534233300809a503c96274804026f872b08a4202026941f78ee5500fa3691e3e1e13c0, 0x838022408ac380042b03c82642fbe020a41948f66228010a516e85a64f600814bf389ab0eb8040a51809fd568a0205280d8f5d1c800fdd9446a24963807eeca235124b1c03f76511a89258e01f63e73669593500f75711832b628007ddbd15550ccc403de95f7dcfd1b801f8545d0b796e900f7fd20d27cef6007e21c990d66b0803e12c78bd4700c01f80ead554a06100f7f91d34fab3f007e07ae5a6d56c403e0bf1df68191c01f7faa769af08900f830d24e5af20007df9929a6482b803e311ff74b597e01f8d029deecf7e00fbbac898af1d5807f744db8fcf63803fba1f200659200202ba88d4492c701015d446a2496380820be69f36e1540409523c1bd8bf0020aa5439a5f1120102e501ad0d2d20082df5b2db1f110040a4e15a35dece020a9469c8d8bff010201a182b572b00817b7f0d3798cc040458d7cb9d2d802033b1ccc227640100f1d013cddc70080e946c5b2915c0403679234a69e2020216986c8d4ab010090e956695b88080749b35373b48040257e0684e8ca02006288d4492c7010031446a24963808018a235124b1c03fff33c255deb80200220eb8aff7601001014ccb1de600806288d4492c7003ffb9a06d708a201ff61ae4c4bb3f00ffe635efd33b4007fee30c8a81b640400bbaefb900ae02010d9fba3941e010031bfb68b8f1008000b607058dbe04000b274a2e118020060cc032997f01000f25383c856807ffe126202f2b60400253589687bb02006d566d1c659810064974dea49a00800881900956a40400917d9ecf1900200c511a89258e01000af00a2014a8080046f59ec5d7004000b646c9e8e602006288d4492c7010031446a2496380800f423023dbe803ffe83db0a5a7a01ff9c517c98e0e010093cd3e6dc2a80800a779cec10e40400c511a89258e02002b719bc83b000ffffa4e2d3f1e008000e2ffde479c0400c55bada64fe02008cdc214987e01006288d4492c70080559ff8f86f4004018d457bd7fd80200ee283b704cf00fba76cbedda20c0, 0x11a31f05b85f6a008558cdfbdc653c0453a488f0640a202142ce7f1897af01142cdf1d9f4a60082859be3b3e94c04142cdf1d9f4a6020a166f8ecfa5300fbab37c767d29807dd59be3b3e94c03eeacaeb6af26c01eeacce97850f100eeacdf1df9992007bab87e90bdde003bcb6deebe499801f08b75e36d75c00f0fd7bd9b5043007c541edbede05003c2105d665b3fc01f00012f0ebf6c00efd4f63670008007c21a628d03d2403c109419e18a1601f03b32452e2d200f044642ec9669007bd5b578d0860403c4418467a095601f545aed086fec00f7e484c74f826007f01935f8ac4cc03f80c9b249c4500205666f8ecfa530102b337c767d2980840cd3ab1bbbe4041028ccf5eaa88021599be3c6b9b40105bb614306fdf008631e86ec1e6500417567075119ec021072202ca54a501035fe4e1ffa888082af295c7f8c4404057bd2414cb5002063f36a995d560101d4fe0dd90530081c3eb71a26f080406949c02426d80203f2a8720fc6a0100b8c5c8ea4768080b67465130f5c0402d9be3b3e94c0200b66f8ecfa5301005b37c767d2980802d9be3b3e94c04016cdf1d9f4a60200b66f8ecfa5301005b28ef900920080b66f8ecfa53003fdcba3fd6e97801fdc820cadd72e00ffd4f59a47439807f09bcddd6231803ffcd2c45cc6d00202d798dc157ee01009ea713ae859008007a7ab2c6da204008ec3639b77a0200b6799da7f5d01005b2cbe30ee4008016c870ef9a9e0400b65aa7c06ad02011199014391d81016cdf1e08a6400801991955f75180400b9081a0879c0200da52b44fce001005b3266b591100802d9891ec631c04016cc48a046a20200b66f8ecfa5301005b37c767d2980802d9381c65ed40405b06270095f00200de661df0160010111a7563777c80802d9be3b3e94c0402a7def7cc9d601ff8958e7ef74000feba5f8e3dcc4007f6d4646df727804016cfda32bdb80200b66f8ecfa530100b66f8ecfa530080b66abb12ced804013c06a564ce202006265e39f09600f92bec4c16f2300, 0x20f5d51e8a42ee010a3e605fd3d35008298d0410b309004288904366955a0209c44f188428f0109c423ebbd6c8008138847d77ad900409c423ebbd6c80204e211f5deb6400fdc108faef5b2007ee0847d77ad9003f70423ebbd6c801f70423ebbd6c800f704242c5ac4e007dc132d990154403dd1240e9a96a001f7f36f4ea482300f846fbb0e5476007e18515d33112403dfb5af87196d801f7adb015734e100f7982f7825c79007de32e9d66bf7803df3b67046f1dc01f7d88de81d9b100f8dfc00f1e749807e7635d566770c03e9e3a8ef53db201f9c95aeb7a6b200fc9b194be122f007f4ec9953889a003fa73148c424ba02028a11f5deb6401014508faef5b20081e78d786708b0040a2847d77ad90020a2847d8115c40102b4b04938e180082efcc741ff1ac040a69a166cf528020a06944d637a30101ed1f7cda2e3008150145281338404021951d793c3a0202ce8340b4ed50100c15935636640080d02252dbf4440402a5b6bafcc56020154bcf2e371f0100329b03c40bc80803211f5f549f00400c847d77ad9002003211f5deb6401001908faef5b200800c847d77ad9004006423ebbd6c802003211f5deb6401001908faef5b200803211f5deb6400400c79d141b30e01ff9f506cefc8a010006ca24d2e2a007fedb23ac6e6780400d5a5a054b660200c78457192f501003211f5deb64008006423ebbd6c804006423ebbd6c802003211f5deb64010018edc38ca9000800634bbe065f0040031d704948ec02004afdf3aab0e00ffb539f9227b2007fec40675740d403fe035b1dc0dd6020033af3243a610100183be9e66b70080024b61916a2804001314775e4fe02003211f5deb6401001908faef5b200800c7ccec22b6004018f8d9038bfe02006423f19988a01004b1af0ce11600800c847d77ad9004006423ebbd6c8020031d2bdf909e010018d6abbdf2f00800c6b6e4903a00400640af9d8cd0020031f3c54ec1501003211f5deb64007f70cde44f4e040400c507a4a357c01fffba3e02859e00fe6829c27a8d3c0, 0x473e3b3367a224021835087af26460114402700ac4b500851288d4492c70044fd281e4b13a40213386638ae4ea0113386635727cc0082670cc6ae4f980413386635727cc02099c331ab93e600fb6e198d5c9f3007db70cc6ae4f9803edb86635727cc01edb86635727cc00edb8664c9f323007b6e69af00aa7803b8e4ffb2dcbc801f01d7ca9d675800f0a30a9207e58807c3558e8fd503003c0fab9ef850e801f0c93b871d1bf00f134909cd9788807bf14b4ddac78c03bd3748bfe6bc601f3dc2566951fe00f1f2302ffa389807d340331d3bcdc03dae0e91986ef801f395307a1555800f9524b8e2b073007ee30c8b46e26c03f718645a371360204ec331ab93e6010276198d5c9f30083b126540aeec80413b0cc6ae4f980213b0cc6d69abb01054124d04842d0085b7abfaab7f800415f37488bbb420216e74734a39ca01038775fdb074a0080d0895c352eb80404eb3a87ddf700204b3db83aa91701015ac199c29e600816d20a1604a700404abaa31e8d24020209b6a1b62b600ffcf8b91dab5b007fbd4da1cc47040400f0cc6ae4f9802003c331ab93e601001e198d5c9f300800f0cc6ae4f980400786635727cc02003c331ab93e601001e198d5c9f300803c331ab93e600400f0cc76d966402026b5f239b03801006c7004600208080a6f6d4ab9fd80401801c2d60c320200f0c840fa79a01003c331ab93e600800786635727cc0400786635727cc02003c331ab93e601001e198d5c9f300800786635727cc04003c331ab93e602005a4ca815dd90100786635dbd8a00801e1994c8d8380401e19616336820200327dd14515601001e192cb455b00800f0cc6ae4f980400786635727cc02003c331ab93e601001e198d5c9f300800f0cc6ae4f980401e198d5c9f3002007866412ab5000ff862203e7b44008005c50ab2ad340400786635727cc02003c32f98146c01001e1982c11f380800f0cc2e23ff004007866332c81402003c331ab93e601003c331ab93e6007f6d62c557d6c40400f6e303541ea0200f0c82437e5500f986a5d8667b980, 0x83c35018ceda1804338838868cf26020a795781090a90109f48108fac1e80828b3e941350f00427e940f2589d202099c3310421e201099c32d799b60008133862ffdc0c004099c31fe1f10a0204ce18ff0f88500fdb70d051aff1007edb867d2ed0c803f6dc33d6ab22a01f6dc33775a84d00f6dc3328531aa007db73608937d3803dc7290994270201f824decb2296800f8a9dd26740a9007e16e371b6b85403e2bff06ad2abc01f9659fa3624ca00f9f86faa96b07007e518c13273e2403e1e1d565d0f2201fa331adfc1cce00f968af6bffa2e007e849cfd437b9c03eb13bd8dd6c8801fa0392922e0af00fc6ce713c5a63007f71861274ffa003fb8c3090f8a5a02027619d1d3d3401013b0ce8e9e9a0081d89338c9d7f40409d8665db89b60209d8663e1706201032dd96d672e98082dbd63ac0ae74040a62ffa51439a020b2198a15f1a20101c1c8554e5e900806845100c156c0401e2a9ea108d80202295faf8f66c0100ad60cce14f300808e0b630acd1c040255d518f4692020088090cf4d2400ffc5c8a19f577007fbf6da7c21ef004007864e3257b802001e18e2de72e01000f0c7c2c96f00800786467a3c8404003c341f2959c02001e1a0f94ace01000f0cf85a20080801e19920f78180400786656461ce020135af91cd81c010036475b3e1768080348c7791ef640400c239c7849ae0200786635727cc01001e1971d75f9808003c321399cba04003c32a74591402001e19422f10b01000f0cd8cddd6008003c339b99a0604001e19c86e21702002d2676f25ea81003c331aedec500800f0cca646c1c0400f0cc367842602003c31fa180d901000f0c89994bd008007864f34187c04003c3279a0c3e02001e19b0440f101000f0cd822078808007866b0f43000400f0cc6ae4f9802003c334783cd701002d260c388d8008007862799cfb404003c32f52277202001e195729dc201000f0ca4d98f400800786515513b804003c33371f01c02001e19c30f72b01001e198d5c9f300801e1988a9c64804007b851d22a2e02007850ce91cca00fb59e0e93c74e40, 0x100d2e899b82563080d17041e5b23e040c1a33255f7c0020271381fae89c0102859be3b3e94c080a3475b9d51ca0409fa503c962748202670caeebb774102670c472599480804ce16e363edf0402670bccfb91b82013385e67dc8dc0ff6dc38a45d74607fb6e1affe1b8f03fdb70d7ff0dc781fdb70d234f96080fdb70d4c4cd45807f6dcdc483171b03f71cc573a119801fe399fe61efb640fe2d4732dc7c3e07f9061354037da03f902ec1d04b9101fe5c8605ce468c0fe652bff23644407f94ceeec1d97c03f8bd9a6b909d701fe8bc7cb18d9b40fe418f8e69e1c007f99aad4f4881003fa59833f2942d81fe77d05b78aa680fefc4d139ae01a07fdc6167d5cf5b03fee30b3eae7ad82009d86a7ce5bdc1004ec353e72dee0807624dc4b00b504027619c86e21702027619a85ba9c0100deee8baa3cb0080b6f5a23cdfd00402abd2197e8f582026bfddecab184100885837c059280801a119605dc110400731d7dd042c0200a15b4679688010025e496b2befc080210a36a2cd1f040097907e63cd28200412e291f2dfc100039dc7070d5607ff5b653fc3f8804001e18305240702000785bb8852dc10003c2e7d5b11608001e17ea8360b04000f0d8d5d91582000786c6aec8ac10003c35945dcae08007866ab9581404001e19bbd424502004d6be47360700fffcf3599eca9808003f4219505e20400308e71e126b82001e198d5c9f3010007863f180c3c08000f0b89dc09584000f0c30533298200078620379f6c10003c3487dfa9608000f0d7d4185184000786b94213cc2000b49c14fdd621000f0cc6bb7b1408003c332991b0704003c32ec0e4c682000e8255a5099810003c30abd20f608001e188b9bdb304000f0c45cded9820007869253a0dc10003c34929d06e08001e1a29166af04003c331ab93e602000f0cf06b75401000b497d847f2a08001e185b47b6704000f0c9e6830f820007864b0d198810003c31df825ee08001e18b70738004000f0ceeabaec820007869e68aa0c1000786635727cc0800786635727cc04001edeb4ce34002001e176c4026340fee329ae4106ef0, 0x2045ee86a456518100de521c5a46c6081a3d344717c6404183a04cdf62c40205666de824ac401050b37c767d29808144a235124b1c0413f4a0792c4e90204ce196b4423c8104ce193771b33008099c30d168d6a0404ce18a67544f0202670c533aa2780fedb86add8e07407f6dc348280faa03fb6e1a3e9125f01fb6e19e74e8e400fb6e19f4d1d6d007edbc944a5f4e603ee3949800dcc801fc4803eba46b080fc53f00a65e27c07f1df2a7d6af2c03f110c81f24b2401fc98c16edf78880fcbf04a9ad3f4007f2412f4c3518403f14cebf1631da01fcee4c0d0554f80fc8bba9334d0e807f2f3bc7fe36a803f490a7b1ad17301fcfa6e82617dc00fdff697063e06c07fb8c30761f3be03fdc6183b0f9df02013b0d0dd4db081009d8686ea6d84080ec49a67673a20404ec335b296f60204ec33388d4120101c48c8a6a0ec80816deb21924fc0040538fc45e0bfd0204b9fbbcd6b54810121d1c75a3938080342257121b520400e4f567704760201159b84c63f001005e9fee23ccc80805316c5260e7e04013a6e7fea8c50200823ea7ed77c81000579044dd71c07fef2aa997909c04003c31f8c061e02000f0c386138b81000786218f4b1c08003c3187fc0c204001e1a3e9125f02000f0d1f4892f81000786884219340800f0ccfbe167c04003c334cb2d2a02009ad7c8e6c0e00fffb22495d64c80800933aa7e77c80400611ce3c24d702003c331ab93e601000f0ca5ca614008001e18762120304001e1909cce5d02000f0c8b9ccd5810007867ad5645408001e1a494e83704000f0d21f7ea58200169357aa44c41001e19998bff5808007866532360e040078660b2014f02000b98832f289010007863e6c366408003c322e7335604001e1917399ab02000f0cf5aac8a810007867ad5645408003c33bbd1b8e0400786635727cc02001e19b7392030100169315e2681408003c3223b5d7e04001e195d087a702000f0cacec99c0100078652c2b28c08003c326511d6804001e19ba6fedb02000f0d006826281000f0cc6ae4f980800f0cc6ae4f9804003dc05155f2e020039ffac46c2980fdeca2f49123f60, 0x40ab1bceaa524f02032cd49ad4fed8100c9d7b64f8776081d3dedb8a25fc0418996b26f15d40204e2254f8f6d201050b37c767d2980814128693557cc0413f49ff03de670204ce1959d06bd8104ce1919e8f21008099c30e6e391a0404ce18a9249c50202670c54924e280fedb869fc055bc07f6dc34ad7670a03fb6e1a56bb38501fb6e19f20bebc00fb6f659e440a7007edb9c9d9255d603ee39455e3152c01fc26a8b6f762d80fc676bca08c4e407f11fe873705d203f1f38241d9a8201fcea3b22e5b5980fd81a991e2e02807f30960a8dc07803f1c2487c5431201fd04a4b10c68e80fca4865bcc9e3007f3480d26ea1b403f553c679688f701fd076e42e44e900fe549235b1684407fb8c30a67360a03fdc6185339b0502013b0d15e2e1281009d868af17094080ec49a7ce1f520404ec3370a42a60204ec3341f2f2f0101c2416cdf70200816deb1780c81804049ce9599e4f1020599cece71f2c810031383f692dc008044989d0f24160400e4b81a0a548020038094b7ea6301002a82044989400801acee867f9ea03ff45606e445a302008229730157880ffe917b2e3297c07fda67a41bd80804003c3233d1e4202000f0c54924e2810007862e502a2408003c3192b969a04001e1a494e83702000f0d24a741b810007868da0c7f40800f0cd3c5198c04003c334f622a002009ad7c8e6c0e01002f25e0b8cee80802f48b4e8a5900400611ce3c24d702003c331ab93e601000f0c9d10854808001e18863d2c704001e19148a43502000f0c90fb7c1810007867b813a2c08001e1a4ead32304000f0d2cb547d820016935d08f3841001e199b8f80e008007866532360e04007866132e1b102001e17f540be30100078645ce66ac08003c322e7335604001e1917399ab02000f0cfb09776810007867d84bbb408003c33d6ab22a0400786635727cc02001e19c4a5d51010016931a9540fc08003c323e8f41a04001e19478dbf702000f0cbe6051b01000786541a5e3c08003c327a8c91804001e19bd1f45102000f0cf9b1cbb81000f0cc6ae4f980800f0cc6ae4f9804003dc0efbf16002002255d3d199580fd8b13e3a15e260, 0x81c48625e2e5b603fb6e18a3c5ed901fdb70c533aa2780ff6dc2f13b62e607edb85fcfa44a003edb86635727cc01fb8211f5deb6400fbab37c767d29807eeca235124b1c03ee74a0792c4e901fb6e1a5f9832e80fb6e19c10bf12807f6dc35af3734a03fb6e1ac77f8e101fdb70d63bfc7081013385ed34234c08099c2df71c00a0404ce170baa0c90204ce184ddb0190103312783650340080e632a0c3771a040b2b4713293ca0203a4613f45e208102b263382c9a34080a549d3044cb0040ad8f8de705de0202ca902527c8d8102c01f5390ccb8080ae99c3e1b19c040b6ddc13fdabc02030a20a1271978102dbf9e040ebc0080a824f9e5d0640409d8670f862790202761af7d3b2d0101d8937ff063640804ec35f5061460402761afa830a301fee30c386138b80ff71861c309c5c07f2a497372f78203fb8c3299d8dc601fb1685987085800fef848a4c3391007f15ea82d341b403fc20fa304a85701fc59d121530f280ff05339d275374080341e4782f296040000f8405fb3e0201125a8679d2b01003d39c869f2a00803527843b729e04012aea8c7a3490200826da86d8ad81000f5163c78b340800f0cd278b7b404003c3409ae9ec02000f0d3e28ffc810007869f147fe408003c34e32944204001e18431da4102000f0c218ed2081000786121f14b40800f0c9c64af7003ff6684a0ee98c02003d2d6cef2dc0100107cf73a5ac80802f39a3011a9c040060919bedb9702003c331ab93e601000f0cd822078808001e1a43efd4b04001e19e8a639f02000f0cf4531cf81000786487dbe0c08001e191c9849704000f0c8e4c24b82001692ed9c49741001e191c06ca9008007865cce450204007866539e4c102001e19c5beca1010007867f883d3c08003c34476f78604001e1a23b7bc302000f0c82371b881000786411b8dc408003c322e733560400786635727cc02001e191219a2a010016933167a7ac08003c33b6730a2040047fb5b6d02102000f0ccbcd069010007866c44709c08003c3376eea6c04001e1969e3b0702000f0cafdbe8e81000f0cc6ae4f980800f0cc6ae4f9804003dc229e204e02003c3352f709880fcc336f34c4bf60, 0x10166ae2ef31b430808e1ff677269f03fdb70bdd179df81fedb85efe37aac0ffb6e1586598f307f6dc2cba49ba603f6dc331ab93e601fdc108faef5b200fdd59be3b3e94c07f76511a89258e03f73a503c9627481fdb70d988269140fdb70cfa5da19007fb6e1c21da95703fdb70e00d13e781fedb8700689f3c10099c2bb888f660804ce14747cbef0402670a44fbbcf8202670b872cb1f8101989544ff7d78080731775a7328f0405965dff8e12c0201d582f16f34d410157125cf69426080530df5e7a7ce04055d69833d1f902016521a501566c101600fa9c8665c080574c9a496cfc0405b6f33701c570201935f8ddc4f341016dfcf02075e00805412827c8c680404ec33f48066782013b0e1fb1ab48100ec49eaeda7b20802761c67a975304013b0e33d4ba981ff7185d50a10ec0ffb8c2ea85087607f9524a8f199a903fdc6190c7c3d301fd8b42dafca3500ff7c240b3b111807f8af503d3bcb003fdfa41322909f81fe2ce83abe9b940ff82996b8a52d80801a0d195ea1650400019d2e1dfca020088144c0ec2a010015f330b42d6c08011271e35f13704009575463d1a482004136d436c56c10007a8bcf70e0608007866f1beafc04001e1a7c51ff902000786d97a2c4c10003c36cbd162608001e1b55cca4f04000f0b7c6f54782000785be37aa3c10003c2e07380ce0800786390d87a403ffb340ff81f6d02001e94d7352a700fffe52c623da90080179ab4d3322a0400300512b4b0f82001e198d5c9f30100078672c75e3408000f0d7d4185184000f0d21f7ea58200078690fbf52c10003c32393092e08000f0c55e9f9d840007862af4fcec2000b4958998dc21000f0c554b4f7c08003c32a3529fb04003c33348c83882000f0cff107a7810003c34ddca95608001e1aba12d9304000f0d5d096c9820007861edff3bc10003c30f6ff9de08001e18a11696304003c331ab93e602000f0c49f44c001000b499c64ebfa08001e19ee04e8b040023fc19a1a31820007866c9cddb810003c33b80e70e08001e19ee7acf804000f0ca37e204820007864c84c11c1000786635727cc0800786635727cc04001ee011d892c02001e19a97b84c40fe497ddcc883b70, 0x202fb893825ab061006b387172568b0806b0764b6df8303fdb70b6195eab81fedb85b37a4cbc0ffb6e13d8c2f3307f6dc2b82d622e03f6dc331ab93e601fdc108faef5b200fdd59be3b3e94c07f76511a89258e03f7b58125d80da81fdf0d343ab68140fdb70d1d45117007fb6e1d239b59703fdb70e91cdacb81fedb8748e6d65c10099c2227e1b060804cdf7b26ae0b040266ff59f96f98202670668ee22f8101ad272bf61c280807eac6626351304069e58edc5a36020151365a241d9010173f22845a1b608060e47b58091a0405d23fa178a5b0201653221b5dfec101600fa9c8665c08061d0c5df84580405b6f5e65925702018b6d65962a941016dfcf02075e0080541286d97a640404ec34cb4bb47820158e661e87578100ec4a05c711720802761db9f676704013b0edcfb3b381ff71855022abdc0ffb8c2a81155ee07f95249422b48103fdc6189bb7e7701fd0963c6e0a1200ff7c2420b5cc1807f8af542ec420003fe2da77cfb81d81fe2ce8605562d40ff829952d8401007fea8d8ec64c0503ffdc622bfa6fe020018eb6955f7900fff80796d02de407ff1fe409b861704001680f245efc82004136d436c56c10007a8c7b46b86080078671cb425c04001e1aa4981e302000786eef4e74c10003c37576f21e08001e1ba658e2304000f0af380ec58200078579c0762c10003c2ab6c8326080077daa2705a403ffaf60924aa3702002c4aae141c501000678bb44b850080179caded4796040030590f99e3f82001e198d5c9f301000786721b885c08000f0d6d2578d84000f0d1f4892f820007869502f83c10003c322e7335608000f0c508b4b18400078622e6f6cc2000b4945ce2a221000f0cc6bb7b1408003c32a3529fb04003c33348c83882000f0cf702745810003c34fe02ade08001e1adfa9a0704000f0d6fd4d03820007860abce46c10003c3055e723608001e186b63c2b04003c3093a7fd002000f0c0adbc6b01000b499c64ebfa08001e19ee04e8b04004bef1f9472f820007866b45320810003c3397d658608001e19de5ec3404000f0c9b701a2820007864ddc6ccc1000786635727cc0800786635727cc04001ee027534dc02001e19a97b84c40fe6e1a3dd018170, 0x418f97ac23570ec2027ec5ff97bba2101493e998edb91081498430625b9d03f92524d41920281fc929278d0f0a40ff24a471e71a7907e4949289b53ee03e49499502bbb201f9431af0ce11600f980d9f20981d407e7fa3aeff264603e7501c8dfa9a981f9b975b7bdc77c0f92526ad51080007f24a5053cf52d03f925282488faa81fc9294139c2904101cd489499a362080e6a30063c17d0407351972f3ce4820735200a6dd17810507386cdb0af008183eca66b0abd040f85bfaadba480204454dc9dce1681047ddc737c9e9a08122ad72081b4e0411637623db47b02043020ccc533f4104204379ae9c4c08128cd56906e68041124c63de7e490204425d6be3f1fc10449f6d06161a0080fc3775ac025c040ec49b16d1f1a8203d5b1fb8b7938102c4dd3124348608076250e4cbc110403b1287265e0881fe549215794fc40ff2a490abca7e207ebf6e28799a5b03f9524bb3c1ce701f74e017410ba200fe746d5471f1e007ea0e046f5d0a003facbda06e8eb481fa86ba2d7e49fc0fe87cda305dd0807ff85a1ee5c29b0400685ebe0e22e0201001823b9f3700ffef73a3767e8c08030f269e541b504017aa7d2cab3b8200c3a47ca4504410016fa155565e208016933884dbcc04005a4dbf515c902001693b5a336e41000b49d979efc208005a4ec670cf504002d2488eb91a820016924475c8d41000b490e17d51a07ffa7bb3dc488403ff4f8c3e659c302005130e9f0256010030aa34f2adc808046da13d0290e0400917b97d9d1282005a4ca815dd9010016933b792f5408002d26ffe0c6c84002d26aca5322820016935bb147d41000b4976224ee208002d255d07884840016928b9c544420021dc6e7bf5d61002d2528280d140800b498f6760090400b49972b014982002d26845f13881000b49b33752aa08005a4dfa62ded04002d26fd316f682001692d01388541000b496809c42a08005a4b80be5250400b49642db69002002d2591c0c22010021dcc66a635e08005a4d492e5810400a69ad4e39048200169329a583b81000b499b0478a208005a4cef4671c04002d26283b3a782001692ff1001641001691a60ca5b408016932a05776404005ca4576632002005a4d73ed3e7c0fbc73842695ecd0, 0x8e7c766738a028041cd49cf9d3e2d0204ce1b84e374f8102670cc6bb7b14082670cf1051b3c03edb86635dbd8a01f6dc33057331500fdb70cc6bb7b1407b6e198d76f62803b6e198d76f62801ee08926b1094d00eeacea31fce81807bbd32efb1091003bb009a33793dc01edb86647dc0b100edb86635dbd8a007db70ce545fcf803edb867adbfa1201f6dc33d6dfd090104ce187ef55320082631e3b9ac0f40411392255641060210c8545c3166c0109d866379384e00827669af580fe8042964fb4e02f80020b37ae490676d010ab6becc9e21a8082602864ed9ac404277bf4298fece020b2b35f2e6696010b00808c5105a0082ba65cdc61354042db749256854e020b813a2a38040010b6fe7816d0ae0082a093bdbde34c04276198df322700209d86635dbd8a0107624cc69979700813b0ce0e90efc0409d867074877e01fab3c95b5ac5d00fd5a09b174b32007c0e85d02cd53403ee2845a60734e01ee30cc6ce4b7c00fbe124cc75edb007c57ac0547a00403f16d3be8aec6801f167481e71a8900ff2ce7624db8c007fb4a2f7cd089003fd8aabbf942760201bda6007202801007ac9833d12e8080b709db10022404043f8f9351426020209b408ac3e201003d4536b897600803c331b1b13b00400f0ccf1f6c2002003c335e0d74b01001e19af06ba580800f0cd82f330404007865316bbd402003c3298b5dea01001e1900818af80803c330878739c0400f0cbd3e44c202023fe42dfe36e010069ae9bbf72b0080bcf791dc0a0003ff894648415480200f0cc6bb7b1401003c331aedec500800786635dbd8a04007866662ffd602003c333876ad701001e18fbceb21008007861a33b09204003c331aedec502005a4ca864e2780fe824cb4ff25680801d9e90b523f80401e198d1ed9520200786635dbd8a01001e199c3b56b80800f0cd2d0844404007866968422202003c2a173c11801001e151254633007fc6b3fe1c9c7403f8983e622bd1e01fe3af9d6f46fb01005a4ca864e2780800f0cc6bb7b140400786635dbd8a02003c32f9b5f4b01001e19802c1ed00800f0cc447171c040078663395dd202003c331aedec501000d00351c09980803c331aedec500400f710c11e48c0200f0cd4caedde00fff5e08a8940a80, 0x10786a0465ecd500856371ca628b04040e6a4cbf297d20202670cca86ea3010133866543751808133866543751803f6dc332a1ba8c01fb6e19950dd4600fedb866543751807db70cca86ea3003db70cca86ea3001f7043378c2f3c00f7566f9e320f9007dd9446dfd30d003dce9412fe246a01f6dc335d6562200f6dc332a1ba8c007edb866543751803f6dc332a1ba8c01fb6e19950dd460102670cca86ea300809d86669b52000404ec332d3969c0204ec332adcdf40104ec332a48d0200813b34db58efd40414b27de3225b00205b31b5d1c4ea0105fd25feb33dd80818391f138bf000413af80da06342020595bf53d18a50105803eb68403d00815d330b1186bc0416dba513e25040205c09d2449be70105b7f334d64bf80815049e17daa880413b0cca9a0ade0204ec332a1ba8c0103b1265f94be900809d86654375180404ec332a1ba8c01fdc619950dd4600fee30cca86ea3007e54932fca5f4803f71866543751801f7186654cdd4c00fdf09271d8d82007e2bd60d14fb1003f8d935295918401f8b3a48d550ae01006263ab056bf008020c8eafef47404007daafabdfc401feed7f63d5a5100ffe6eaf4baa6d807ffd237cd86e940400c843c637d8e0200a36d79f69a201001ea2a2f329e80801e199524681004007866543751802001e19950dd4601000f0cca86ea3008007866543751804003c332a1ba8c02001e19950dd4601000f0cca86ea300801e19950dd460040078665ce0df4020135afb09256801000d0f5fd331700803b5a157bfa0c03fee810570a58402007866543751801001e19950dd46008003c332a1ba8c04003c332a1ba8c02001e19950dd4601000f0cca86ea3008003c332a1ba8c04001e19950dd4602002d265f94be9010039e92604b89007fbce7eedcf5f403ff8af1af6173002003c332a1ba8c01000f0cca86ea3008007866543751804003c332a1ba8c02001e19950dd4601000f0cca86ea3008007865cdf840c03fd6d43791ab0e020006e2ec11b7701002d25958a4f9808007866543751804003c332a1ba8c02001e192271e3601000f0ca3537b18080078652eb761804003c3328f8ab002001e19950dd4601001e19950dd4600801e19950dd46004007b859731126020078669dc474e01005e8e922145ec0, 0x2362b1be584352010b2810d09eb3a80899c331f60cd70041cd4993d4c4600204ce197f7a0380102670cbdb98038082670cc2c2440c03edb86676ba69e01f6dc3347723e200fdb70ce2a471a007b7ef07c336a6c03b6e19906cdb0e01eeff1982e618e00eeace4c8ff2ad807bbc664cd8afd003b9d2824e1723001edb8664da91a100edb8663a0a953807db70cc4713dbc03edb86624c2bf201f6dc3313feb280102761998a363b00813b0ccc27f5dc0409d866613faee0209d8664fcbf6f0109d8666affaf700827669d5793698042965094c41a1c020b5e264b83713010acdf52a725ae0082c6c483a1f2b4042b1fc291f55a2020b2b7e91c4022010b007d592c76a8082ba651f069118042db7487b4bfde020b19543c7f2e7010b6fe4793df1e8082a093b06cc67c04276198fbc511c0209d86630eb8a20107624ca6b429200813b0cc419efbc0409d86620cf7de01fb8c332df080100fdc61996f8400807ca9265b681ab003ee30cc9a393f201ee30cca623a3200fbe124f1980f3807c6d2d64b9b25c03f27e06eba926a01f16748559283301002566029bf220080500e64fc35ec03ff9d83391aed801fd3fb717240b201002cb307fcce9808074187a9875cc03ff068a743e57c020165aa9ec8c7b01003d45140857a00803c331f5946e00400f0cc5f27bce02003c331067bef01001e198833df780800f0cc3c404d0040078665e9057802003c332f482bc01001e1997a415e00803c3323890d7c0400f0cc96119fa02026b5f396d8b101003d585e6ab5a00800b72b97ba68803fe078c809b5980200f0cadc8696e01003c330e643d6808007865d2f29800400786608a56b802003c330859b8d01001e1994f4be8008007866694db5004003c3334a6da802005a4cb97f8cc0100786634043d6007ff3fb2dc23a8c03f5ddf082c6c1402007866161220601001e1984d8b2400800f0cc36e19e4040078661b70cf202003c332b4128b01001e1995a094580800f0cca7a5f400401e198bba02260200306a3d9172601005a4bbe7523300800f0cc3182ef80400786618c177c02002552d8ab5ef01001e1945e20a780800f0cad2c9188040078663c1243802003c332c98d4601003c33212fa1080803c3309058ea80400f712e5b4a9c0200f0cd7c88177010327904a3e1b380, 0x41ebde215dcdd80214028aff234290104ce19950dd460084ce198a71b3dc040e6a4b32e16c70202670c0964bfa81013385f08f5084081338629f33c2803f6dc3927ed2dc01fbc78378f2dc800fef0cd05a30a5407db70ce085f89403dcae7f889bf2c01f75d0e468f53b00f7836a1a6c832007de96c0482dfa003dce940f3a4fca01f6dc33144e41b00f9291a4b372d5007f5ed19cc0ef3803fb8ba256ad29401fdc5d30d4858701013b0e992fdd000809d8689efafd00404ec343a02c380204ec33a7aea990104ec33676b9ff008144dabd18274c0414b28edb8fc7e02058fb53c0aee80105ba2ecf4b0d800817a8b2cdd569804174c0c774d3140205b408fedf8840105803ea72199700815d326925b3f00416dba06bfdf5e02053c9bdf46b2e010533c6d36ecd7808150493ce2805c0413b0cbbd91d500204c98c6cee275010376709fa13e000809ca3bfbf10a80404e4dbe2e040a01fdc619e49f36e00fee30cf24f9b7007e549346368cd403f718666dd4a7a01f718664a2c0f500feb88ceaa0056807e2bd67b30df7403f8e6facee02b001fba374602aafd00ffa8ffcd2abc580806844add3e7440401c9703414a900202293dde035a1010027eccbac386807ffac849a8e57403feda4e4b7b9cc01ff01793a4453f00ff800b5a8238d807f46fcddc2509004002f9b1dceb2002001de58c26be401000f0a236bf8c8080078621e5360804003c34578b84a02001e1a2a6e16a01000f0cff107a780801e19936723c8040078666662292020135afb4b4f1a01006180b01388e00805e6cd927bd1c0400694076a653402002023131a68901001e19071d8e7008002deb1d6529e0400199b808348e02001e17bb86e7a01000f0ce38b3ae008003c33e16880204001e19e09833d02002d2685b6bf381003c3321a446c00800f0cca646c1c0400f0cc2e6a3c401ff94463012b3300ffe1759bb603180800786035ab42404003c301ad5a1202001e19bf086fa01000f0cdf8437d008007866d12c4880400f0cc6ae4f9802003c3320955a800ffc1d2d5fe689807ff456561f317804003c32efc3c8602001e1955d230701000f09093c264007fd61212a5153c04003c333f2d07e02001e19e5f6e2901001e198d5c9f300801e1989559c2004007b8a93fb75402007866a5ee13100ff20612b0845ac0, 0x81b8fa4ea3e096040d038e8a6bb9c02099c3338addd90102670cca86ea30082670cbcffde580407352399f6314820133851511299c10099c2c645ece608099c2fbf8c06603fb6e1bbe82f4901fdb70e3e9218180ff6dc40b26394607f00c4e8ee0b2c03eeee39984dff401fb8211f5deb6400fbe4bb4558ff3007f0437318b826803ee74a07dbfe3901fdc6190694d7380fdc6190dd3e8e007fb8c2f64426ba03fdc6182594e2f01fee30c12ca71781009d86c3ff714c0804ec3553ed99e0402761aa1e8c6d0202761a164b0750102761aa2ab3058080ae175550a846040a594c87ff6fe0202edbf3ed02a081028cd3fb825074080b3d85dd95cd0040cb071c96122c0202cabc0ef1d7f8102c01f5390ccb8080ae98a79d6ec8040b6dcac32d2ba0202c5c054f88478102dbf6f4805dd008085bc94352ad80408c4acdac4785020274cbb41bc1e0101d88efb681e9c0804ec2e322d82e040276171916c1701fee30d361af9a80ff71869b0d7cd407f2a49add8a3ea03fb8c336df4d3001fb8c33576dadf00fef84acc83dca007f15eb2ecfa4e403fcdd8c407c97901ffa12291dbde7810031339ac5f6f8080342256e9f3a20400e4b81a0a548020114afd7c7b36010009e33afef2c807ff3553fc2f3b2040016ff7546ae701ff7cec08d78e380ff7548ba24e7f407f6d136700006404003c31cdcaebe02000f0c22e67db8100078616d1ed9c08003c312cb271604001e1a8f1d63302000f0d478eb19810007869a61a6fc0800f0cd4c6da5004003c3354c0d8c02009ad803f843201001ae1938887d80802f3de469d70404002bed5cdc25102003c32703b12101000f0c88ed75f808001e18660513f04001e18fc6030f02000f0c8cf4790810007867f883d3c08001e1a6ee54ab04000f0d3f80ab782001693666ea5541001e199b8f80e008007866532360e04007866132e1b101ffccb9921ef150100078643cae52408003c31ee0304604001e18f70182302000f0d071e80981000786838f404c08003c33f1848c60400786635727cc02001e19904aad401001693193d954c08003c323e8f41a04001e1934c25bd02000f0cbe6051b0100078654c6341408003c328aa89dc04001e19d7f8aed02000f0cfdb8cec81000f0cc6ae4f980800f0cc6ae4f9804003dc43012e4402003c2fe3a6c2380fe117d856516ae0, 0x10410024271d95c080d94b306682ee040ab766ad7338602099c3331f78320102670cca86ea30082670cae9168b404073522f37f08082013384ac5ad9fc10099c2bce03b1608099c2f745e77e03fb6e1c0c5fda701fdb754ff168fd80ff6dc79c0644c607ee6c052b9a17003edb86aedaa13801fb8211f5deb6400fbab4d4b88846807eeca235588e3803f34f02157f7c501fd93d6185f98880fdc619071d8e7007fb8c2d45e779e03fdc616c5db2cd01fee30b62ed96681009d8763c0401c0804ec390fc31b60402761c54de1190202761aee6e0100102a996af5f33a8080c4620d1a25e6040a5a2b1e340780202edbf3ed02a08102fe92f7a869bc080b589a6e52c80040ba47f42f14b60202cadfa2378ff810278c956308e10080ae98372f03f4040af2dc4aee75e0202a0eb0691a318102dbf247b1fa6808047976fa1fc7c040760d2b8007ab020276044db32170101d890a3a00bdc0804ec2d00189a204027616800c4d101fee30dac3dfe280ff7186d61eff1407f2a49c3a949d603fb8c33eed535001fb8c347000d8a00fef84ab3adf46807f15eb3ef1dcd403ff170678490c7020109caf28f5b9810031337f40b760080342256e9f3a20400e4898e559a4020114afd7c7b36010056b06670a79807fef5070de8b5e03ff2f238128aeb01ffc71c11f1c6080ffe52714d0b0f407fded3cd9d2d4c04003c3165149c402000f0bed33aa381000785fbf883dc08003c30508874a04001e1b531d4d902000f0da98ea6c81000786cab5cbbc0800f0cfa5da19004003c338514fd802009ad814144f60100096f329862000802f3de469d704040002196ef44f502003c331ab93e601000f0c9e6830f808001e189bb7e7704001e1919e8f2102000f0c8e4c24b810007868af1709408001e1aca2ee5704000f0d75337ef8200169381480f141001e19a4f532b008007866532360e040078661b3c21302001e1861fe10e010007863d148ab408003c31a83424a04001e18d41a12502000f0d28ae44c810007869457226408003c343cb21ae0400786635727cc02001e19c09ed20010016931d44985c08003c3243edf0604001e190c7c3d302000f0cbe6051b010007865821614c08003c32b59e13c04001e19d29a00102000f0d05c6d4e81000f0cc6ae4f980800f0cc6ae4f9804003dc43012e4402003c328d9f73780fcdfbbd91cf4e60, 0x2081f50eee278981023ca8568a39a4080d95dfb743802040ab7bcd0c163402099c3331f78320102670cca86ea30082670cae3b7dc804073522f37f08082013384ac5ad9fc10099c2bce03b1608099c2f745e77e03fb6e1c0c5fda701fdb75263e23f280ff6dc795fbc02e07ee6c87b43404403edb86aedaa13801fb8211f5deb6400fbab37c7c5904007f755975220d6003f34e238f66f0f01fd93bfdc5405880fdc619071d8e7007fb8c2d45e779e03fdc616c5db2cd01fee30b62ed96681009d8763c0401c0804ec390fc31b60402761c578d68f0202761aee6e0100102a99769f96c38080c463a58bf1d2040a5a2a04493120202def98ffa2bd8102acd84274be6c080b7018c5b431c040ba47f42f14b60202cadfa2378ff810278bbd1fd7188080ae993492d9f8040af37be6267ea020267ae32fe5d68102dbf251c3821008047a9e16998580407611e6e7d62d020276043ae7bdd0101d890a5a38d640804ec2d00189a204027616800c4d101fee30dac3dfe280ff7186d61eff1407f2a49c3a949d603fb8c33eed535001fb8c347000d8a00fef84ab3adf46807f15eb3efa514803fefa993f79fc3020109caee88588810031337f40b760080342256e9f3a20400e489b69bb8e020114afd7c7b36010056b06670a79807ff662499a5e1a03ff99743b58c5301ffc79a5c7e24180ffe5153257ecbc07fdec479edc5a804003c3165149c402000f0bed33aa381000785fbf883dc08003c30508874a04001e1b531d4d902000f0da98ea6c81000786cab5cbbc0800f0cfa5da19004003c338514fd802009ad814144f6010005a5cb7710980802f3de469d7040400018207592dd02003c331ab93e601000f0c9e6830f808001e189bb7e7704001e1919e8f2102000f0c8e4c24b810007868af1709408001e1aca2ee5704000f0d75337ef8200169381480f141001e19a4f532b008007866532360e040078661b3c21302001e1861fe10e010007863d148ab408003c31a83424a04001e18d41a12502000f0d28ae44c810007869457226408003c343cb21ae0400786635727cc02001e19c09ed20010016931d44985c08003c3243edf0604001e190c7c3d302000f0cbe6051b010007865821614c08003c32b59e13c04001e19d29a00102000f0d05c6d4e81000f0cc6ae4f980800f0cc6ae4f9804003dc43012e4402003c328ef71f280fcdfd13be54ae60, 0x410b3daf5a865301fdb3ab075afb280fed9d84071927407f680f9309fd7603f6dc2e52659b601f6dc330db867900fdb70cca86ea3007db70ce9f8d5e003f9253238bffa081fedb8c0d33764c0ff6dc59076b6a607f6dc4616710320404ce16a5a3145020267053830e5e810099ad894bc6860812a52d37a9c4c04112493d5465700203248b76814ab0102b337c7c58488080b30726570d9c040a94b715e02b10202761cd3de10a81027619dbe55ae80804ec39253dd660402761c5cec17b02013b0e2e760bd80ff717ef9c4af8407fb85ef8d7f35203fdb6239e22eff01fdc08d0ad2c6200fcf4707af3bb3807f4cb86eefb9f203f5b53618ea38201fdb8cc2ec4f5580fdbd52758bfa9c07f816e84f274ac03f8e47f42f14b601fe1adfa2378ff80fe101f5390ccb807f82993492d9f803f8add1df8e93e01fe304e8a73aa080fe2bf9e040ebc007f7c25034b823403f7186806898e101fdc61af5245b700fe5493e9fe5eb407fb8c395591fb203fdc61caac8fd902013b0b00eda1381009d858076d09c080ec491edfb7320404ec3223b5d7e02044b1fb1565a20100f7ee2c74bb8008041ead90f25d404010b4ef9f703b020109d41bd7fda81003133c50f972007f9e57a40419b20400a28e90a0b92020112e8bb66a05010056b06670a79808037f83f1280ee04012aea8c7a3490200826da86d8ad81000f5175e718fc0800f0cd4d2242804003c346d063fa02000f0d6fd4d0381000786b692bc6c08003c35af3734a04001e170baa0c902000f0b85d5064810007859ca7e60c07fdc81c24c6ab003ffbea93f7b23602009acd682a875010030c05809c4700802f3de469d7040400611ce3c24d702003c331ab93e601000f0cd8cddd6008001e1a43efd4b04001e19eb5591502000f0cfb09776810007863f180c3c08001e186b63c2b04000f0c0d6bc2b82001692cc0c85440ffbdbafda8b0b808007865d242fee04007866564da3702001e19bf086fa0100078684e6ebfc08003c34a2b913204001e1a515c89902000f0c4b2c9c58100078625964e2c08003c31a83424a03ffe79a61261c802001e19238d5a90100169332137d8408003c33dc09d1604001e1f4754f9f02000f0cca755ae010007866a40ef1408003c3366d29a804001e1961d5aa502000f0c93aad3780ffe0b3e06931f00800f0cc6ae4f9804003dc25ce581002003c3352f709880fced8af8e35e6e0, 0x8215c1618df416040867c40c6292701fdb38cbff89f880fed9cdf9e2eccc07f68b4858e95ee03f6dc2e44f8e6801f6dc330db867900fdb70cca86ea3007db70ce9f8d5e003f925322095e7a81fedb8c0525702c0ff6dc587bcdaae07f6dc45d0a22360404ce16a2f3bcf02026704bb5786f81009977ce6a406608129d0b1937d2404113050e7fac8e02028a11f6f7c508102b337c767d298080aea235124b1c040a94b5fea4ac10202761cce7f61e81027619dbe55ae80804ec391fdf27a0402761c5cec17b02013b0e2e760bd80ff717ed42de84407fb88dc552c97e03fd9e8663a55ed01fdc38f97110bb00fcf68b9e4b88f007f4a6c30c3ea7a03f5ee0a5d1c50c01fdbd4c5614be480fdb21eefa8cbdc07f95c8f6b0123403f8ce36cf1986c01fe1abcbac7aff80fe101f5390ccb807f82993492d9f803f8add1df8e93e01fe5c53334b38c80fe2bf9e040ebc007f7c2502f5974803f7186806898e101fdc61af5245b700fe5493e9fe5eb407fb8c395591fb203fdc61caac8fd902013b0afe3e49d81009d857f1f24ec080ec491e89cc460404ec3223b5d7e0204455a567e9c90100f9a00bdba83008041ead8fd08b804015dca52902b5020109d41bd7fda81003133c5bb6cf807f982dd648fa120400e0dd81a4c5a020114afd7c7b36010056b06670a798080526bbf63020e04010cca234ee210200826da86d8ad81000f5175e718fc0800f0cd4d2242804003c346d063fa02000f0d6fd4d0381000786b692bc6c08003c35af3734a04001e170baa0c902000f0b85d5064810007859bfc103407fdecb8e8bc8dc03ffc544628871402009acd2662aaa010030c05809c4700802f3de469d7040400611ce3c24d702003c331ab93e601000f0cd8cddd6008001e1a43efd4b04001e19eb5591502000f0cfb09776810007863f180c3c08001e186b63c2b04000f0c0d6bc2b82001692cc0c85440ffc02bcad0779808007865d242fee04007866564da3702001e19bf086fa0100078684e6ebfc08003c34a2b913204001e1a515c89902000f0c4b2c9c58100078625964e2c08003c31ad92d3603ffdde6111fa9802001e19238d5a90100169332137d8408003c33dc09d1604001e1f348996502000f0cca755ae010007866a40ef1408003c3366d29a804001e1961d5aa502000f0c93aad3780ffddd4b111fb080800f0cc6ae4f9804003dc43012e4402003c3352f709880fcee4f4dd56c360, 0x103b101a699058c080ab9f7b562d6a04055a31595b6e101fdb6ef1db517180fedb779794678407f693c70de463e03f6dc311f45bc801f6dc330f1013400fdb70cca86ea3007db70d0b889a1003f9e863f983dfa81ff0acc6dd2c3bc0ff80248953c56e07f8020eb07050e0404ce1558b4c1d020266d40d40d7e81008ff38a0a564608126ef92ddcd8c0409d86639e7e4c02028a11f5deb640102b33af1951000080bf3dd9cebc70040a94a4fe606930202761ec49435081027619b0440f100804ec37bd761a20402761be419bbd02013b0df20cdde80ff717f63d2aad407fa66e45a3543603fdc581bfba85701fdc5141cd826e00fdc6175a495bf807f719a42ce362603f72bb70cf711201fd61f14395cb380fd9b2d778c014407f95c8f6b0123403f7050af24eb0801fe1a94e415ba080fe566597da6be007fb974abe096a003f8add93c602d201fe304e8a73aa080fe2bf9e040ebc007f7c24fb3d7c1403f71866b99b3b901fdc61a062efb100fe549396c2ca1407fb8c3680a3d3e03fdc61b4051e9f02013b0b5c373bf81009d85ae1b9dfc080ec494ad6edf60404ec325968ab60203bc47bf5f18d0101504788290b5008041ead5ec458004010b4ef9f703b020109d31e1e3cb81003131ec83852007fcad1310a60aa0400e48d980801a020114afd7c7b360100392be00309900802730d018432204012aea8c7a3490200826c851d02a81000f51692639f40800f0cd01f4b4004003c341c7a02602000f0d48e65d481000786a31b82f408003c34fe02ade04001e180d6ad0902000f0c06b568481000785e1caeff407f97991251b46c03fe9b5dd02b03a01ff69a701573a301001f5cc992b9500800c9cc74f3b50040060dbaf9163102003c331ab93e601000f0cd61e860008001e1a23b7bc304001e19db3985102000f0cf4531cf8100078643cae52408001e1890fa89f04000f0c93aad3782001692dc2891840ffa501432af38008007865d242fee04007866539e4c102001e19b44b122010007867e30918c08003c343cb21ae04001e1a1e590d702000f0c6b64b4d8100078635b25a6c08003c31fe1f10a040078627c4c52a02001e192e4ab81010016933167a7ac08003c33b1145b604001e1ca819a6302000f0cca755ae010007866a40ef1408003c336c3149404001e19673459102000f0c97b1d6881000974392cce300800f0cc6ae4f9804003dc24a1a1d602003c3352f709880fe18f2e5142d660, 0x23091d9ce408d40104ce19e7fa6418082670cc6ae4f980413386635727cc01f6dc331ab93e600fb6e198d5c9f3007db70cc6ae4f9803db70cc6ae4f9801db70cc7cb07e000f7c608ba872230076dc3324539e2003e57c8d309b41401fb96bcb8a8b6300fddce58c8ee62007ddce271a7285c0409d8663a514a00204ec331c540a701013b0cc75127e008276198d9a82f004276198d700a48020b345aa0c08de010acceb726cd588082ce9b94338564042d16338ed48f00209d86652300cb0109d86635727cc00813b0cc6ae4f980409d86635727cc0204ec331ab93e600fdc6198d5c9f3007ee30cc6ae4f9803f717045802bc401f6d4b50f8bc2400f7186635cccb8007dc669af00aa7803de64fb4b3163001f7185005b5a5400f89486baa9305807e2d958b640e5003e37b25c746cf801f7bc78f1ee9bc00f8407cfd0b1fc807e0a64d24b67e003e2b7477e3a4f801f7d478c0ab2c500f8afe7520735f007df093bd4da16803dc6198dd8cb7801f7186635727cc00f9524ca815dd9007ee30cc6ae4f9803f7186635727cc0204ec331ab93e6010276198d5c9f30083b125dc3a53ac0412a8cac902504020f24ed08f2c0501009124d0b2cab008107ac073caa6c04042d3be7dc0ec020427480b6eeaa00ff853b0fea0910080160a4453efd004014d4d07ffbac02013c52289a7f101007f8f65c0b470080709ccd09b67404037d4cac419b4020209b32baf89a01003d453683e9700803c331ae665c00400f0cc6ae4f9802003c331ab93e601001e198d5c9f300800f0cc6ae4f980400786635727cc02003c331ab93e601001e198d5c9f30080393571521aa40400f0ca32e7ad401fdebda393ae6000ffec3575c17028080a7d72bee0cf004011cd668ef02c0200f0cc6ae4f9801003c331ab93e600800786635727cc0400786635727cc02003c331ab93e601001e198d5c9f300800786635727cc04003c31422d2c602005a4ba24e16800fe31b0d41be56807fad0a803b2c700401e198b2bf6480200786635727cc01001e198d5c9f300800f0cc6ae4f980400786635727cc01ffa34ac1bb2de00ffd176254c01a00800f0c80df6fd803fb8f6d73106d80200090095f35c201005a4ca815dd900800f0cc6ae4f980400786635727cc02003c32cfe37c701001e19861c4c700800f0cc439eba004007866332c81402003c331ab93e601003c3211964a180803c331ab93e60040015a0dd4714202007da2f5163fd01009992ca75eb980, 0x41e1a81f0004600216389a8c55d370102670cc82919e8081338664148cf404099c3320a467a01fb6e19905233d00fdb70cc82919e807edb867430993403edb8698c59fb001eee202ce4704400fb6e19b4e0544807b6e19c9a3dcd803f24a4cb4a3ce501fdb70cd37013240ff7186412d1d1407f718652a0d5040404ec3383fc08802027619ccbb61c01009d8689ab54340813bc7fac048700413b0cc82919e802051423f1a895c0105666f94bace700815d446b9f60880415294172bb91c0204ec335545ccb0104ec3320a467a00809d8664148cf40404ec3320a467a02027619905233d00fee30cc82919e807f718664148cf403fb8c3320a467a01fb8c3320a467a00fb8c333aff22e807ee334e20ae67003ef327dbd4556801fc0f72493127e00fbca10580b50d007efcf115fc709003f1c8fe9d8f3bc01fc35bf4a5a49300fc203ead0cc2b007f05326aa07e4003f15ba00ad83f001fc609d1ad27d500fc57f3c66d00c007ef849df1fda4003ee30cc83c3a9601fb8c3320a467a00fca926587b4db807f718664148cf403fb8c339168bd6020276195540b1901013b0caaa058c8081d8931f7cc7d40408e2ebb41834a0207ee4b0c31789010048927cecc37008083d6004b546004023560fbfd4c4020213a41c4b25500ffab54aca2d8d8080683e86b8a13c0401c8db371afcc020228def734ceb0100acfe70911600080a4d781bb98bc0402545962454a4020104db5cb168301001ea29e3789580801e199068c780040078664148cf402001e19905233d01000f0cc82919e8080078664148cf404003c32bd4cc6c02001e195ea663601000f0cadfb86000801e197171c70003ffb605b55d86601ff68ffb477e9a00ffda553e0b86880800f6d39b6d2480400c239d35aed6020078664148cf401001e19a475432008003c33bc5e33604003c336e814d802001e19c355aff01000f0c8910949808003c3127e03d204001e18232bc8d02002d25972abab80ff1c9fcd3875d807fffaa8ac493a004006416063794e02003c3320a467a01000f0cc82919e808007867029962404003c33814cb1202001e1918d783a01000f0c8c6bc1d008007864839627004003e9a6248c7002003c33268083c01002d26587b4db8080078664148cf404003c335e6541402001e18c7cb56d01000f0c8b7aefd008007864bb2095c0400218a47a703802001e1947d3fcb01001e19905233d00801e168b0fe7d004007b7a60de17e02001e70acecf5000fe21f35d73718c0, 0x883b200bca0ed6041f1250478f25a021cd499502bbb201039a931536923c081cd4989ef7346040e6a4c4f7b9a301f9252691cbc8680fc929348e5e43407e494a102e840603ea9150b34859c01e6c66a7232afd00f95b6f1a0430480792526644a0a6c03f5fb729b7882d81fe5492f9b152a40ff2a4972c721aa07f2a4983e4eeae0407922723aeaf902046b34d2aa59581011ca7715874a2081e2f9c2c8e718041d8932a05776402079e6d460d41d010819acf14f65b80820be69f36e154041fbde16b84ebb0207624caa82baf8107624ca007d770080ec498df676560407624c72630a10203b126393185080fe54933975adcc07f2a499d66acbe03f9524ceb3565f01f9524cc9a5a1c00f9524cb1bf4a7007e54cf550a22b603e6cbc5c89c1f401fa9e2f7eb652380fa2b60795899b407e9efd6f6c630803eaa0c0eb7043601fa50c7713c83f80fa305dfab2662807e87cbff62982c03e8dea9296429601f92634b1e51b180fa83e92baab4e007e746eae98ebdc03e54932a22286901f9524c8a8d1c700fafdb96bf0d86407f2a498d4aa07e03f9524c6a5503f0203b1266d8cacd8101d89336c6566c082c4dcc512b7ae040ec4996b0524e02056cbc92d008c01006cdbab507d98080c5c11b36f75c0403219dcc1edeb02031d75c822fef80feaa4b449114400809c6533e9e41a0402ae69b55364002033e0f87571a2010104113351f6c8080d0410b81570a040346d003e10b50200b3e0731313681002df3634fb42c0802d263f07fc3c0400b4991d283f002002d263a8930b810016931d44985c0800b498e4c614204005a4ce3275fd02002d267193afe81001693381e021c0802d2658bdc7b00400b4995d2a0fc0201d0872d0f75401009241081d4d500808db9ad3d850c04012356ab46e8501ff0181565e06001002d26164a152808005a4bf6e156d04005a4c5a38f7b02002d2636822da810016933167a7ac08005a4ce3275fd04002d267193afe820043b98cd4c6bc1005a4ca864e2780801692d046045a040169301ddeb6d01ff82f2a041aae01001693193d954c0800b498ef8371a04005a4c77c1b8d02002d266426fb08100169332137d840800b49985de8ea04016932a05776402005a4cb0e007c00ffb7e373e3c2b40800b498ef8371a04005a4c87ddc5102002d25cd0bf6b01001692f6f06bf40800b49830f647804005a4cbbdc1bf02002d26682dfe181002d26540aeec80802d26494d91480400b94e204687a0200b49a0e5fd7980fac432bc755cda0, 0x104164c578ee03c081cd49b4e4e94604099c3320a467a02086e41f9ca74001011df69d08d1dc08099c2c13d29120404ce160c989ff01fdb70f74ae03e80fedb87b9ab2c1c07f6dc3533b581603f6dc33ec25dda01f6dc33409477800fee30cca86ea3007ee30c9667565403fca923a4b38ec81ff7184ef7a625c0ffb8c2b0cb31e607fb8c2f13b62e60402761a494e83702013b0d1df0e7481004ec35945dcae0809d867119c7980409d86635727cc02028a11f5deb640102b337c767d298080aea235124b1c040a94a0792c4e9020276195b28178810276196d2486b00804ec3167c3f3a040276189bb7e7702013b0c4ddbf3b80ff7186e234084407fb8c357ee30fe03fdc61aba12d9301fdc61a23b7bc300fdc619d2963cc807f719aeca08c9e03f79981ac85d9001fe3dbf3ed02a080fe4e92f7a869bc07f95c8f6b0123403f8e2147aef6dc01fe1adb47f8eb580fddabf17dd9ad807f82993492d9f803f7bbdbbcb7ffc01fdee65cc84a9680fe2bf9e040ebc007f702c03ec945803f71865f2ebf9d01fdc6193e280da00fe5492f4fe79bc07fb8c3177dfffe03fdc618bbeffff02013b0d1f4892f81009d868fa4497c080ec49ae2e8ed60404ec33735381c020126237d8b31301002449b344dc1808041eba52209200400e9b48b34e7501ffe1052dafdfa810031323f1343e8080342256e9f3a20400e4b81a0a54802011372cfce9fe01002ca41709c7b0080253c29c339d204006d14aae6d670200826da86d8ad81000f505bfc429c0800f0c915cb0dc04003c3281aeca002000f0c7a29156810007863dc0608c08003c32037dbf604001e1a41407d502000f0d20a03ea8100078690501f540800f0cd2c358c804003c335a1f87802009ad7f68b8e4010013c3b22e79380802f3de469d7040400611ce3c24d70200129b75c740201000f0c49291ad008001e184b2baa304001e19046e37102000f0c8e4c24b81000786777a371c08001e19f36397704000f0cf9b1cbb8200169353a341b41001e198d76f62808007866532360e04007866188cc9d01ffd714de3609601000786467a3c8408003c323e8f41a04001e191f47a0d02000f0cf702745810007867b813a2c08003c33b1145b60400786635727cc02001e19904aad4010016931d44985c08003c32cf8bafe04001e194f9bc5902000f0cae444570100078648b12ae408003c31f44d80c04001e19c7dca2902000f0cded861f81000f0cc6ae4f980800f0cc6ae4f9804003dc7583ca0202003c336dd073480fd04f268b0fb7e0, 0x2058755485c46d81019ab7957d43ec081cd4998b3d3d60408dbe24d963700207afbdd377e6e0101338630ff818408099c3157a7e760404ce18abd3f3b01fdcd2631f7fb080fee69421731bf407f6dcb3e041d4a03f842ab0a7682801fb8c3325e279f00fee30c027ffcc007e34cae432bd8803fca92598190a881ff7186080d8d0c0ffb8c30b68f6ce07fb8c31e8a455a0402761b6b475ff020146977048c1881004ec6f4376fd60809d866fc21be80409d86635727cc020289f08fb85090102b337c767d298080a089de099d14040a221d517a89702021c60a665f13810276197b3d11680804e93c87531360402760dd0edb2902013b06f084df680ff7187a0296e0c07fb8c35a9d885e03fdc61acf8d94301fdc61a2e7519b00fdc619a242180807f719a6ec56cea03f7993ed2cc58c01fe1ad5c3609be80fdf9bb92b4188407f95c8f6b0123403f8a97ef149b3001fe1ad0d720a5880fda75f1cb2c4e007f82993492d9f803f8a662b35609a01fda67c403bb6080fe2bf9e040ebc007f7c24d34d486003f718660dc563901fdc61967c5d7f00fe5492b9ecf77c07fb8c23e035a9e03fdc611f2ca2c502013b0d53a3bac81009d86a9d1dd64080ec49b896016a0404ec33d6ab22a020052ad64892c401002449386efeb008041eafeaadfe004009a40e67e46101fdeddbba75862810031315c32ecb8080341edcdc4ed20400e4b81a0a548020114afd7c7b36010056b06670a798080526bbf63020e04012aea8c7a3490200826da86d8ad81000f5116967b2c0800f0cc206c08804003c30d4182e002000f0ba4b573181000785d8653e2408003c3121f513e04001e1a6ee54ab02000f0d3772a55810007869a61a6fc0800f0ce83e13c804003c3344a4cc802009ad7c8e6c0e010030c05809c470080526ab10d95940400611ce3c24d702003c331ab93e601000f0cbd489dc808001e193cd061f04001e195fb7d1d02000f0ca7cde2c810012893fd6806408004a1c3d7003704004c2f01785c18200547ca50db2241001e198d76f62808007866532360e040078661b3c21302001e1979398fe0100078651e36fdc08003c32291486a04001e19148a43502000f0e76f442f8100078738caca1c08003c3a16e28e20400786635727cc02001e19af2b1a10100169321f7714408003c32a49639e04001e195d087a702000f0cbe6051b010007865cd43a3408003c32eb50e7404001e19b7c096502000f0d2b5d9c281000f0cc6ae4f980800f0cc6ae4f9804003dbed9722a602003c32f7ad6ec80fd7fe4bb58013e0, 0x40f1258fe9a46101fdb70cbe8d79100fedb865f46bc8807e4949be3c7ec803f6dc3300210d801f8515c0f8f41200fedb866551412007f6dc32fa35e4403fb6e197d1af220202670cbe8d791010133865df6099c0804ec3301b35130404ec3337f6bde0205c1c07b5118c010198a153c23f600813b0cd166082c0403b1263ba86b302009d865f46bc881004ec32fa35e440804ec32fa35e4403fdc619a00262001fee30cbe8d79100ffb8c32fa35e4407f71865f46bc8803f71866cde66de01fdda11e59d09300fe02d51973a84007f77886594d6e403f7d4a038259a501fdc61975dbe0780fdc61975b8c1d807fb8c32fa35e4403fdc6197d1af2201fee30cbe8d79101009d865f46bc880804ec32fa35e44040276197d1af22020276197d1af2201027619889ab9280809d9a67afbf5a040a593b292bb7a0202cd22e0ebf48810269633661c18c080a7ffcde9f0dc0407bced963a59602024846586ca988102c01e047957e0080ae98ea07b91c0408f38eec0448002018d6a1c1438f8102dbf8c7882040080a824e1b255d00409d865c4b0a9302027619725d94a0101d893187586d80804ec32fa35e44040276197d1af2201fee30cbe8d79100ff71865f46bc8807f2a498eea1acc03fb8c32fa35e4401fee3f65cb1019010024492aef796808041eaef27d910040075b63f1b925020109cf59ef73780ffe57cb718387807fc3c264e039ce03fc96b7fe90a1c01fcf69a32634e701001083c4b6366007fa6e00b65d27203fd59b43f8201502007deec70a78581000f513208ea5c0800f0cb533111804003c32e20bd1e02000f0cb2786fe010007865f46bc8808003c32fa35e4404001e197d1af2202000f0cbe8d791010007865f46bc880800f0cbe8d791004003c32f11df6402009ad78174f3d0100024efdc9939008007e7c592069404006088fc9fe9902003c32fa35e4401000f0cabc2157008001e19273006204001e1957842ae02000f0cae716cd010007865f46bc8808001e197d1af2204000f0cd6b78b7020016931dd435981001e197d35491808007864bfcfab604004db727693c102001e19537d27d010007865f46bc8808003c32fa35e4404001e197d1af2202000f0cbe8d791010007865f46bc8808003c32fa35e44040078659672d6602001e18b6aa67101001692eb7c8f5008003c32fa35e4404001e197d1af2202000f0cbb9e29e81000786388bb67008003c32041e4b604001e19cd15b0802000f0cd158dcb01000f0cbe8d79100800f0cbe8d791004003dc27a2300802003c3306268db80fd09b07ca65ada0, 0x81bf36eea8b6f60406857d2839b8a01fdb70cd77772c80fedb866b0fe38c07e5f596513a9ea03f910a4ba38a8201f7500b3ac1a4d00fedb865b9fad2407f6dc32d2400ba03fb6e196c6a26f82013b0cdc284a681009d866d1365140804ec3378b734e0404ec3417205800205a18f3b0b92f01013b0d71ab2a600813b0ccc7155d80403b1262f23c0a82009d86543d7cdc1004ec32aca94460804ec32dcfd69203fdc619d9e45b901fee30cffbd91680ffb8c353bc88be07f7186b28c59e803f8c86507afc4401fdda11eb23daf00fe032863f4cbd007f82a23263944803f7d4a0564ee7701fdc6197e1209980fdc619793c121007fb8c32c223ff603fdc6196111ffb01fee30cb088ffd81009d866b0fe38c0804ec3353206da04027619a6e0df70202761996c4d330102761986bf5aa00809d9a691173ca040a593bcae4be202020b40c4b06c5810245127641f9f4080949f3b415dc40406f276c8892780202807a2eca9178102c01ac24a2b18080ae981d57fb84040945a6a7ce3be02022271c8ea93c810265fabce60bd0080a824e369f52c0409c0dc3a6f46f020276197285b7a0101d8931aed0d8c0804ec32c223ff6040276196111ffb01fee30cd3706fb80ff718669b837dc07f2a4996dc389603fb8c333038fdc02003c3308f890e010024492db2e24808041eaf3eec3780400afe99c3b967020109ceb11938d810030fdb0e938e007fc41930bd20f603ff1ad79ac527001fe72356d10be000ffb20221572ba807fe15d40dbc97203fc925ebc9bdad01fffd22947f17881000f5134cc533c0800f0ca78482cc04003c32e25c17e02000f0cadd9a87810007865798aa1408003c32bcc550a04001e19a99036d02000f0cd4c81b6810007866a640db40800f0cc354637804003c32e96036202009ad790899a600fff9138795425807f552f9548f9a40400605bee7dec902003c33069b33701000f0ca51fcc8008001e18f04da9f04001e1948e7ed502000f0ca7234e0810007866c678f3c08001e19dc93b2f04000f0ce63bd358200169336724d241001e1980b8995008007865211880e040078651c34bd502001aa004a1b670100078654e952b408003c32bcc550a04001e195e62a8502000f0cd4c81b6810007866a640db408003c33587f1c6040078661aa31bc02001e19121c24d01001692f8b1738408003c3241439d604001e1986a8c6f02000f0c753785d010007864d0eb96c08003c326d24e1004001e1a044852b02000f0cee49d9781000f0cc0a50c180800f0cc0faf70404003dc198ea9b002003c32e4e70f880fd2c6005f73f760, 0x103898cb7a02dac080ebac894ca9ba0404ce2292c7fb001fdb70cdc6cc5a80fedb866f8e0e8407e5f21e77d9dba03f81bf98f21a7401f6dc336c5467e00fedb865adf855807fb8c32bd0a95703fdc619659df6b02013b0ce1cb74681009d8670e5ba340804ec33c23f53e0405d35e644dd28020518df48b2f8f01013b0cf66bf1180813b0cc9ae8d840403b1262c9001582009d8652054d641004ec329ae7c8a0804ec32d5f94ae03fdc61a6cbd69701fef70b5c14f8680ffc4e97efc23c207f9bf06d6555c403fc19c95de97b401fdda39ebf88f200fe033319c939a007f7bf2a08ecf0c03f7d4a05dc165f01fdc6197feea9380fdc6197711aea007fb8c32b06283a03fdc6195ae099301fee30cad704c981009d866e3662d40804ec3361970a604027619b0cb853020276199ca875e01027619889bfa400809d9a69889bb2040a593ba4b26f40200e542480e6dc8101ec6683f1a5cc0805d0e954bed200405d399fac1a120201b8d71659c458101faa76a6a8340080944e7a0b8cb00407790de0f9b6e0202971069b830b81022fe5c7ba35b8080a824e28971640409bdd5b2a772f0202761971b2ffe0101d89318f7580c0804ec32b5c1326040276195ae099301fee30cd70e16e80ff71866b870b7407f2a4998e6a02203fb8c333950ebc02003c330f18ae6010024492ea1321808041eaf487285c04005153f7a70070200ec6d5c4f6fa8100312a7a7aebf00800d232bcbcd1a040025bcbfe563601ff8dc51525a4b00ffc7c0474f9420080101b2d46b2ea040052b856a634f01fe81439fe9aa181000f5131b39ffc0800f0cac23eac004003c32db57f9a02000f0ca9694988100078655607a9c08003c32b06283a04001e19b37adc902000f0cd9bd6e4810007866c32e14c0800f0cc6f20aa804003c32f27824202009ad799a188601000dd31afdeb4807f70c81f63f414040026085a9f96502003c330bac1e601000f0ca15b436808001e18b718c7504001e192feb23302000f0c9d54405810007866ee238ac08001e19ee8c5ed04000f0cef38294820016933bdec7ec1001e19889fbd88080078652de9ae2040078656ed4ca501ff565c5a25cfe010007865159778c08003c32b06283a04001e19583141d02000f0cd9bd6e4810007866cdeb72408003c3371b316a0400786622159a402001e19256c7c60100169306d7ca4408003c3209eb5a604001e1975ba02f02000f0c8a48e4f010007864e31b72c08003c325604b6804001e1a49447ab02000f0d060a8ff81000f0cc1935be80800f0cc1e946d404003dc197452b802003c32a4291ab80fce338811a8e360, 0x2049955a8a2d5280fedb8661fd9a7807f6dc330c3394803fb6e19a222bcb0202670cb4f31950101338657ca3548081b93fced9021004054bb570f27f80204ec33417aff20100ae915e1d6e300804ec3715e0f780402761b884124601fee30c8b554f000ff718645aaa78007fb8c31b73237803fb8c32e94720401fb8c328e6963900fee30c44ac30f007ee30cc673fcbc03fd900cfeef44601ff93a5cc25f8a00ffd26f23cf215007fd26da02c3a8c040276191eb8a4202013b0c9f785e501004ec32025fc600809d865cd2f91c04085c0c25f1f000201fddaded61f601026b1ac8fec42808094b94385fcdc040a94a076f05bd020276198d9c96f8102761998e2abb00804ec33bab3bf804027619d54bd9a02013b0ceaa5ecd00ff71864fbc2f2807fb8c325da960c03fdc6192ed4b0601fdc6195f28d5200fdc619842a5a3807f61c6dc3bdfc203f6c158807e87001fe3dbf3e412d580fdfccf7ca0966407f6b58ca47432403f8e0965762e6e01fe1a9a362074280fe101d54def6c807f79c8d59ae74803f8adbe4331b9401fddf98d1c1cd380fe2bf9dfb1ef1007f7c24eeaec8cc03f7186656b6ff501fdc619c52fcd600fe54934e852b4807fb8c3415fd5a403fdc61a130cb3402013b0c976a58301009d864bb52c18080ec498cbf16d00401eace8e1293202003c3309ca7a600ffda3ceb44f5000802fc6c2cb3d5c0400fbfb7466dc5020109d0f1389cb8100312fcc896958080342256a2754a0400e4b818ec5b2020114afd6a9ba0010056b0662929400804877e3c7e96e04012aea8b5c3b30200826da74f91781000f514d597c040800f0cca23333c04003c3362197c202000f0ceaa5ecd0100078674a7209008003c33bab3bf804001e192ed4b0602000f0c976a583010007864bb52c180800f0cc15e0d6c04003c32b7e913a02009ad75b0b74d010030c057c246180802f3de42258ac04006103b421d8b02003c33199b45001000f0ccdc9018808001e19d7fb31004001e19b7c318802000f0cdd3937f010007865a798ca808001e1946fec2c04000f0c9e20b2a02001693141f7ee01001e198ce7f978080078658a382c6040078663be79e502001e199f99062010007867552f66808003c339a7ba7004001e19cd3dd3802000f0cb243c1f010007865921e0f808003c32d3cc6540400786633368a002001de234b0435010016932ef8e8a008003c338a5f9ac04001e19b7c318802000f0ce90e495810007867f97eae808003c346cd413e04001e197c2017602000f0cb39b6da01000f0cc666d1400800f0ccb19aa2804003dc1e853da802003c33385752180fdbaf9d16c200e0, 0x40b23041ee9fe30203010b714d30200fedb8659677dac07f6dc32d2400ba03fb6e197d1af220202670c8e4c24b81013386080d8d0c08184be288e45ce0407cf3981cdc580204ec331bdac5201009d86f9066ef40804ec360fdf7e20402761b07efbf101fee30c4f339f680ff71862799cfb407fb8c3066032fa03fb4e91822e57e01fb8c32fef407000fee30cca86ea3007ee30cc6bb7b1403fca92798eb3b281ff7187046fa24c0ffb8c3d16c62b607fb8c3818bfb4e04027618c6ad5d702013b0c51e2f6c81004ec2ed345fd60809a205ee9fed004084b2c16a4d400201c62a45ad2280102aa370e0e6f90080a31d171f90b4040a94a0792c4e902027619be7fb8681027619a78a33180804ec3487dfa960402761a3e9125f02013b0d1f4892f80ff71862845a58c07fb8c31376fcee03fdc6189bb7e7701fdc619148a43500fdc618d58851b007f612aaa176dfa03f6dc493254d6e01fdfbb5fef2c6980fde0b52ebd0fbc07f8a635940e18803f8d3370ec462401fe19fdc4f8cfa80fe101f5390ccb807f8298e60a1e4003f8add0726828e01fe1d2c4e49f5580fe2bf9e040ebc007f7c24fa3bbb5003f71866b18d35701fdc619d4832aa00fe54935bb147d407fb8c3487dfa9603fdc61a43efd4b02013b0c74ca66a81009d863a653354080ec497edc2ada04003c32daba44302003c32d3ddf4901001a287e517050080293d964b56700400cda98abd31f020109d10fdf57381003133a832abd8080342256e9f3a20400e4e3178e5aa0201137dbed7f05010056b06670a7980803f21457e9e6a04012aea8c7a3490200826da86d8ad81000f51611833d40800f0cd278b7b404003c33ae6504002000f0d1084326810007868999c4e408003c344210c9a04001e18e186c7302000f0c70c36398100078637b5dbf40800f0cb9ed709004003c32b3a85e402009ad76ef4d1d0100453206e7e3200802f3de469d704040060c6ee18eff02003c331ab93e601000f0ce0300da808001e1a7443f9704001e19fe20f4f02000f0cf7027458100078657edf47408001e19321304704000f0c990982382001692ff1001641001e198d76f62808007865ed1c68a0400786658fcfad02001e19e49f36e010007867edc676408003c3411bca4e04001e1a08de52702000f0c965a2ad810007864a813f9408003c326984b7a0400786635727cc02001e1947cc762010016933416ff0c08003c337602d9204001e1a5ec93e702000f0cd12bb55010007867701ce1c08003c3412a872804001e1969e3b0702000f0cafdbe8e81000f0cc6ae4f980800f0cc6ae4f9804003dc1836adba02003c333accf7280fdc5ee26a8cece0, 0x83c350116ca9d004099c331ab93e60204ce198ccda2800fdb70cc23f31c007edb8660a870f803f6dc33b0c919c0203ddb1c6c34c0010247e784b14d78081d8932b16c75c0409d8668334e880209d86635727cc01013b0cc6ae4f980809d86635727cc0404ec331ab93e601fdc6198d5c9f300fee30cc6ae4f9807f7186635727cc03f7186635727cc01f718663e583f000fdc619950dd46007dc6198d76f62803f9524ca815dd901fee30cc6ae4f980ff7186635727cc07f7186635727cc0404ec331ab93e6020276198d5c9f301009d86635727cc0813b0cc6ae4f980413b0cc6ae4f98020513590e8a299010514d347ecc8700812568b76356f004152940f2589d20204ec33205e2a60104ec331ab93e600809d86635727cc0404ec331ab93e6020276198d5c9f300fee30cc6ae4f9807f7186635727cc03fb8c331ab93e601fb8c331ab93e600fb8c331ae665c007ee334d780553c03ef327da598b1801fbf31dc42e10f00fbb460d9f8626007eeff9a727ff5803eee35c821125a01fb2f76862ab9400fc203ac45da50007f05326925b3f003f15ba3bf1d27c01fbf0693ebc35200fc57f3c081d78007ef849defcbba003ee30cc6c1704601fb8c331ab93e600fca926540aeec807f7186635727cc03fb8c331ab93e6020276198d5c9f301013b0cc6ae4f98081139aac870770040007e9fc08ba4020078660b138a00100489266209fe008083d5fd55bfc0040215ea4313638020213a40866ccb01006268c6f174800802fd0dfe993480400720e7f8e4040202295faf8f66c00ffa9cfc9421ea80800e92f46858f403fe4ad402dfe980200f3cc2c0690401001ea29b41f4b80801e198d7332e00400786635727cc02001e198d5c9f301000f0cc6ae4f980800786635727cc04003c331ab93e602001e198d5c9f301000f0cc6ae4f980801e198d5c9f3004007865720e1a0020135a252bd6f201006180b01388e00805e77576cb7cc0400c239c7849ae0200786635727cc01001e198d5c9f3008003c331ab93e604003c331ab93e602001e198d5c9f301000f0cc6ae4f9808003c331ab93e604001e198d5c9f302002d242c4a4b381000fdc32e3d2d00800f0c8cf97d680400f0cc845528402003c331ab93e601000f0cc6ae4f980800786635727cc04003c331ab93e601ff8270d75b9d100ffc11fa489f718080078451113f3c0400f0c9685204e02003c3320955a801002d26540aeec80800786635727cc04003c331ab93e602001e197cc0a3601000f0cc05eced8080078660c54a2004003c33199640a02001e198d5c9f301001e198d5c9f300801e198d5c9f3004007b886025c88020078659c1f48f00fe20d17fc484ec0, 0x116b8ecc5908270084ce197837cf1c040e58b5f794ed00204ec33242dd7d00fb6e19f8b4130807db70cdd68793403edb8670a908500204ec331c1cc79010276198ddf0538083b12654337c6c0413b0cb181a8ae0213b0cc581995e010276198d5c9f300813b0cc6ae4f980409d86635727cc01fb8c33241ef0300fdc619920f781807ee30cc6ae4f9803ee30cc6ae4f9801ee30cc8366d8700fb8c332a1ba8c007b8c3314e367b803f2a499502bbb201fdc6198d5c9f300fee30cc6ae4f9807ee30cc6ae4f980409d866483de060204ec331ab93e601013b0cc6ae4f9808276198d5c9f3004276198d5c9f30020a2822ede11cb010a63023b1fca9808258cf363b7eb8042a5281e4b13a40209d86638ae4ea0109d8663013ce000813b0cc454e3240409d86622a71920204ec3311538c900fdc619920f781807ee30cc6ae4f9803f7186635727cc01f7186635727cc00f718663724773007dc669b1b001d803de64fb4b3163001f8c47ba9c1a3400f7db77d1b1f50007e0d6dae7c90f803daf76a0131fa001f7413fc64b6d900f7bf3758bea00007de0e5c37d467803de2c0b3060bd601f7eeb9ab948bd00f7ea0cdd725cb007dc826abddc36c03dc6198c003f6601f718662c0ccaf00f9524ca36304a807ee30cc6ae4f9803f7186635727cc0204ec331ab93e6010276198d5c9f300802d2656507af40400f0cc6ae4f980200f0cc6ec157601009124d0f418a808107abfaab7f800403d4629ec22260203d7503087c020100c4c9e93eee78080d0809d6ee88c0402a7541529df202041fb43daefd200ffd3fb3b6fd088080426b9ce88b5003ff048627a84660200b6a4651130d00ffea77289532900803c3314dbe1280400f0cc581995e02003c3311538c901001e1988a9c6480800f0cc454e3240400786635727cc02003c331ab93e601001e198d5c9f300803c331ab93e600400f0cc7c3815002026b5f239b0380100a169934fa080080bcefaa39c41403fb155df73a40201fdbf1d912a6a001003c3311538c900800786635727cc0400786635727cc02003c331ab93e601001e198d5c9f300800786635727cc04003c331ab93e602005a4ca815dd90100786635dbd8a00801e1994c8d8380401e1984cb86c402007866255670801001e198d5c9f300800f0cc6ae4f980400786635727cc02003c331ab93e601001e198d5c9f300800f0cc6ae4f980401e198d5c9f3002007845fba580201005a4c929b22900800f0cc6ae4f980400786635727cc02003c32f98146c01001e19816973880800f0cc1e07f2c04007866332c81402003c331ab93e601003c331ab93e600803c331ab93e600400f712c92bc7c0200f0cd4bdc262010121e5aa8695400, 0x20f10972eef6ca0104edde84265bb00811d6dce7d832c0404eddc5b81f4502028b410d1704180fee376c1394c2407f71bb5817780a03fb8ddeda39edf020276e50b2eb2881013b780e8fb96c081d9336249a2ee04088351a9e463402089879156b6aa01013b771ceb01ac0809dbb8ecb6bc20404eddc765b5e101fdc6ef01dcf0c80fee37780ee786407f71bbc0773c3203f71bbd71ead6c01f71bbcef32d9800fdc6ef5613602807dc6ed58bd99bc03f954cb656ceb381fee376af81d9240ff71bb4daf64ea07f71bb8713508e0404edd64b9ead9020276ea8b6d36b81009dba07776cda0813b7780ee78640413aedfb297aa00205155cbcc3a2c0103e73cac515558081166f51f2465804152fe2faf68660204eddf36150790104eddef55e99500809dbbc0773c320404eddc308c7e5020276ee18463f280fee37809dce08407f71bc0fabcdc203fb8de082bd1cd01fb8ddf45ead6900fb8dde8ad1ef8807ee39fc5c5baec03ef3929499b3e401fba65fb21483f00fc9ed0d85176a807ec6b230e94fc403f056d3147576401fc344ecdf89cf00fc21da396d92b007f05992cd4c3e803f0ca1c861ba5001fc6247fde7f7400fc599eedf9aec007ef8b4cae8b4dc03efbb30c4d425c01fb8de2055e42d00fcaa6682cb692c07f71bbc0773c3203fb8dde03b9e19020276f027dcd0581013b7813ee682c0801733a944915404017d2c474489402042980a980c58010049686842328008084ab98c48448040219f3c5ef4dc020216f96c5314b0100633e3b71c618080690cb5f543c80401c9d079cf37202010f02970832d00ff9168e5dbe0a008004950e1fb1f00402592aeaf5af80201083122dc5c101001f78645586a00801eef44114c1404007bbc0773c3202001eef01dcf0c81000f7780ee786408007bb850fcf0604003de00c9a18502001ef0064d0c281000f780de3e3940801eef6c40d70404007bc0b2da2ca0201390646af1f5010062562493da780802a34aeca6ec80400c2fcf41bb3402007b985eb350201001eee4bf5912008003dd6d73c6d104003dda0a2386702001eed3c1c42681000f7780ee786408003dde03b9e1904001eef01dcf0c82002e67975790cc1003ddd0f9a80600800f7728af24500400f77a23cb36e02003dde03b9e1901000f76cbb2ee9408007bb6ae23b1e04003ddb5711d8f02001ef042b63a181000f78215b1d0c08007bbc0773c320400117067764ba02003dd604f58f801002e66e41f888408007bbc0773c3204003dd884d309102001eee31480da81000f76e84addb408007bb710a396a04003ddbd1708e702001eef01dcf0c81001eef01dcf0c80801eef01dcf0c804007ede32270ee02007bbd8b23d5600ff001f549aff980, 0x42e0c7105bfff80209dbbd99ae7a40109d8668ef7f5680827350ea442ae00409d865e4d9b490204ec33158dfc780fdc61979bde34407ee30cb9414a7203f71865c15bc170204ec32bcba06c81027619e3f03e4c083b1267641d4b6041292e596ba2d6021133cd6bae1c3010276196f24e57c0813b0cbfa078de0409d865fd03c6f01fb8c337e0a99c80fdc619bf054ce407ee30cda79e29e03ee30cd36d9d4201ee30cd41eefe300fb8c3359bdb23007b550841638cd003f2a4992a8223781fdc6195247fa340fee30cab277ea207ee30cbd9cf7560409d8663d73f7f0204ec335f2a2cf81013b0cb9ebdf320827619a62f64ac04276198cada69c02092c35daf7e0f0109e392a7dc87b0082752a5787aa5c0429e4857e466ce0209d86697f26180109d86696ba11280813b0cbaed9ff60409d86569580150204ec32b4ac00a80fdc619f40c4a8c07ee30d21f658fa03f71869603f05101f71867fb26a0300f7186696688a1007dc669dcf8400803de64ff82566c001f8b785d7d27fa00f81d1de0d0607007e245abeeadf5403d99d5d9d34f0001f7c855d3f8b3100f7d6c83b06edd007e0a598eabb46403e2b745579f2be01f8924a413d00700f8afe7d4de8e8807df093d2c539ac03dcedf03801af201f71866a0cb98d00f9524cc2e5df1c07ee30cc0a239a203f718660511cd10200d89a706b46881006c295028ee6c0813d1eb8ddde2e0405c51bb8254380209529996124b80100afdb77018eb808107ac325b8f1004047eef2eb153002044b6025a78120100c4fb5f564580080d08985953e4c04039251f56294e0202e64b6ec46fb0100e2e29c3fbe18080f365f45487300404699a4d0ba0e020209b19e37f0401003d4564ce47300803c3346d7570c0400f0cc52a1d1402003c32e7af7cc81001e1971d43cdc0800f0cb1ddd9120400786787b2f3102003c33c3d979881001e1a21b117ec0803c33810fdc140400f0ce824fde802026b5fde1c2630100609bbfedfce008021a671c9440403ff5c66c6ce3960200f0c3f00870f01003b12dd859fa00800785ccfb421d0400781690100c1020014f2734dcba81001e19d1d0b084080078680df203d04003c343cabd5682005a4d5ff7568c10078668dbdbb380801e199c7dd0b00401e19a5815cea02007866127e81f01001e176c4f33540800f0c9a5f9c8a04007864d2fce4502003c33e00a8ef81001e19ef5971a40800f0ce5e315f60400ff5597ed3d6020023af0629ce201005a4ceb2bfdbc0800f0cc3a77bee04007865df7b05d02003c32f16cfb281001e1969e814440800f0ca659ae36040078664b4a08b02003c3365e087681003c32aff927c00803c3347001a980400f71397cff9c0200f0ce1521a9600ff20c60bf899040]
set_option maxRecDepth 100000 in
def NT (i j : ℕ) : ℤ := tb 61 NLower (max i j) (min i j)
set_option maxRecDepth 100000 in
def cr0 : List ℤ := (List.range 1).map (dec 31 0x6c440518)
set_option maxRecDepth 100000 in
def cr1 : List ℤ := (List.range 2).map (dec 29 0x3aefce2afab75ec)
set_option maxRecDepth 100000 in
def cr2 : List ℤ := (List.range 3).map (dec 29 0x649e46eebb15c8efa3be26)
set_option maxRecDepth 100000 in
def cr3 : List ℤ := (List.range 4).map (dec 29 0xf75de84449e58a776973e7068c8c9)
set_option maxRecDepth 100000 in
def cr4 : List ℤ := (List.range 5).map (dec 28 0xf20495ddc1eac48494cd2dcac72a752cc4c)
set_option maxRecDepth 100000 in
def cr5 : List ℤ := (List.range 6).map (dec 28 0xd452e409ae79fb990b9a78445b87ae774a3730b15c)
set_option maxRecDepth 100000 in
def cr6 : List ℤ := (List.range 7).map (dec 27 0x1f2a1cbef31f76ea750938b7707b14f926f73b22bb2e1580)
set_option maxRecDepth 100000 in
def cr7 : List ℤ := (List.range 8).map (dec 28 0xdd389a266263916ed38c372b062e53fbf597b8244d553dbc36ddb3ae)
set_option maxRecDepth 100000 in
def cr8 : List ℤ := (List.range 9).map (dec 28 0xd9129f99888d1e664408d6f0be0a72e6d2253e4a2f7b8da8455498436fbbc8b)
set_option maxRecDepth 100000 in
def cr9 : List ℤ := (List.range 10).map (dec 28 0xe0cbbad9141f687ca438d6635c186ef0f1a72ccd4c53efc5e7b8853c5543e1c6ed6110)
set_option maxRecDepth 100000 in
def cr10 : List ℤ := (List.range 11).map (dec 28 0xcfaf4de70fcdd672a87656e7e9948e480e694f6e2d97e3b4985df73f843c31fae6ddff718b6bf)
set_option maxRecDepth 100000 in
def cr11 : List ℤ := (List.range 12).map (dec 28 0xe66c06098cb5106f98e8571725736cdc8ae86309918ff564ea63ba5586021f7842bbb7ae5c59f6ebf2e7)
set_option maxRecDepth 100000 in
def cr12 : List ℤ := (List.range 13).map (dec 29 0x1a728b548ee90504aa3e2f9aa19750e1695ab6b77eb9553c5636782457902037e0887f37bc341074f1734e48e18038c)
set_option maxRecDepth 100000 in
def cr13 : List ℤ := (List.range 14).map (dec 28 0xeab26dbc35011997fc5229ccfbc15323e4c6fa2bd05dffd027bc4a49a5f4a048363d97901ff9682d73f6d731fda754a3aa)
set_option maxRecDepth 100000 in
def cr14 : List ℤ := (List.range 15).map (dec 29 0x62993f6eefca0d58194f97937b326cb0f5b6594cc046c105ab6504051cc577874e1bfa7e30c127ff940b777440f1df344f76690390b75)
set_option maxRecDepth 100000 in
def cr15 : List ℤ := (List.range 16).map (dec 28 0xe156e048b181688bb517a961589a851f248915c34769a66626c1a7ea65f4390865aec580899e780a40e485ad7cf845513aae871dc7590bb6)
set_option maxRecDepth 100000 in
def cr16 : List ℤ := (List.range 17).map (dec 28 0xe9a736f842b6f49118bdd8c946fc99a1ee98a1d4d494ce459694595d62dd0907cb11c8818edaf7fa6c317fc8ebe860b5418427319ae57b026e01c43)
set_option maxRecDepth 100000 in
def cr17 : List ℤ := (List.range 18).map (dec 28 0xe57027b9dab4a984344cc9118f118c943e099a14878a1caec94cd5cc6944b9c62dc5567cb0149818e9637fa64197fc86ec860b89b8427176ae579516dfd735)
set_option maxRecDepth 100000 in
def cr18 : List ℤ := (List.range 19).map (dec 28 0xe5a42e97d4656c7c395ce77d61fe6c67c5d7492c2b6067a136f9e7b065437d098b11218036fb27fbb98e7c7667a7c4da7a7c52a767c2f9687b838b7553f16c6e11f8d)
set_option maxRecDepth 100000 in
def cr19 : List ℤ := (List.range 20).map (dec 28 0xdea4984a5156037d46b847c3b15877d43ed6c67c337492d126067c5f6f9ea566542c2198b10f28036f8c7fbb9597c7666d7c4da607c52a5c7c2f9737b838b1553f1666e11eb0)
set_option maxRecDepth 100000 in
def cr20 : List ℤ := (List.range 21).map (dec 28 0xd72d64c8e3383194d57a07bde0eb7a94cbf7724fd46dfc13b6f6e5135d0ec256e1f80e5ff5c30811db2c8135c0c81324567cd7a597d055217d041f57be395b7ba89f6556583274310fa)
set_option maxRecDepth 100000 in
def cr21 : List ℤ := (List.range 22).map (dec 28 0xe5eba1ca82ebdb90f275698d8365758a9c67208a2c6c322034e67627493e1935f4575d5c002fa5710b098690c7a82cb5418fdccd87c33a5f7975c8a7c1e78876e258b77c16f22b3eadf7acf536)
set_option maxRecDepth 100000 in
def cr22 : List ℤ := (List.range 23).map (dec 29 0x6ce6831e87a75671ba40b88c484554900b925e152a3eeb815fd6d3cb4827c3aed17a890d8851931b546f01fc275b74640196a71f90c908b4e3b2bddc786df790f18fb80c5e762f592bc0c782cae64b13127334d)
set_option maxRecDepth 100000 in
def cr23 : List ℤ := (List.range 24).map (dec 28 0xd336aa7b9a97a5ab27ea49213a908ec3daa95a52fd735a4906f1b72c6a7109f728a751565c18a3105c14824d7c783758d397351de869965a8889c7c7b477597d0e0ea7cf17327687fcd77eda312b6c5bc82164a0)
set_option maxRecDepth 100000 in
def cr24 : List ℤ := (List.range 25).map (dec 29 0x1b7341fc9740ba74dd214327c92b350a890cf8880dc7c63bd2a9e1fb622ebf495f6ff164e2d7c5bf9661b4d461ad5d188ba591b04dd9a61cbe2af0cf880b8854d3d3e33b6e1f64d812faa5fdc79095523cfabfaca06d334ffc5721)
set_option maxRecDepth 100000 in
def cr25 : List ℤ := (List.range 26).map (dec 28 0xe69459290250c68f790e29fd1b6786b84338bb0c598b5bfc590a703c706b77d6b32f216ef2fdb54b47353d63bf476871737da3da07a527ba83d225b83d4ff9843ed0a8978d257abebb47ac39a37a28b4579547813fee20a679353e)
set_option maxRecDepth 100000 in
def cr26 : List ℤ := (List.range 27).map (dec 27 0x1fa2eb4e12e8f9c55a7618a7facb2b8f1be117ef443ba7a4875c6ad1594dd1d4dbf438cd1307653a84c6630b54bbcd3bce964f7e13480f7bcdf6078bf640ff22c820c2df09f593df11dcf3e2640d7c323b2f704bed54f6efb6edcfc)
set_option maxRecDepth 100000 in
def cr27 : List ℤ := (List.range 28).map (dec 27 0xebef739134582658f3e844da4959a4c81921792be3093d7447e702859b4451070391d6f323b9262e773e59b281f959a095ad33be00eb7e30fd0f69b8aa0b3560c16b0b48319d371453419f04e8b3e0d2977c47baaf6ef87d54cb7cb610439)
set_option maxRecDepth 100000 in
def cr28 : List ℤ := (List.range 29).map (dec 28 0xc6be58b81dd81f89ac901969ae5089df5bf9a532e7909e2128c398ac894093a85d292088892f875de0977278b02740f84f40edfe382622db77ead6e7e58ed97b88ab783044c18302ebd835bd738a38a897c343187c39e5f7c3a31c7b7e6b65539b7d6d37571)
set_option maxRecDepth 100000 in
def cr29 : List ℤ := (List.range 30).map (dec 27 0x3ffee1f3e601417d54d12f258851d0f91aab3c2b6768056e9fb61d54aab1baee5a3e611e126a57355a73494bd3407eeadf686b1fabe261f6a2dc20ee4a7f15648ff0b8a5f01cafbe6be1b7b306ad072aef600bfacc0366108bb8f1510f76d7737b0fb1c857c)
set_option maxRecDepth 100000 in
def cr30 : List ℤ := (List.range 31).map (dec 27 0x1c4d74fe418c60bd297667bd1722e99b265adda6fad5667e78be9589b7e71d71d99ab0e61ec6441f88aea818e6e0036525e638ad3e50f1526551fa7f144a517787fbff2b0640835f511403e37540806579107b958e02d985c0775678b814e1112da8b73eb923405f0b)
set_option maxRecDepth 100000 in
def cr31 : List ℤ := (List.range 32).map (dec 27 0xc2df771347fa06236778be862387dd0b18f463ff9d53cd6b6a18727c45330cec2085b65784b854d5971edd12d6bdf2e3629cc490b4cc94a49430b5463dfdf668c54b427800e6610206409fa3d63bed18438177e4703bccf600f3fe402d1a485cd263088a3b2b9dc8839825c8)
set_option maxRecDepth 100000 in
def cr32 : List ℤ := (List.range 33).map (dec 28 0xbb101998b0549da0fcc28b0d44307cc921d7d740bc786f00a726b37e597c5b871b20df52c7c624ca40376c5cfd265e638159bfeb398d54bfa1074d1abdffc793074cd8b9cfea85f728f8125afb82e8dfb7d90c66789028d8b82a2084052a47f94709808c5988bab7358881b87dce59bf64a7c14)
set_option maxRecDepth 100000 in
def cr33 : List ℤ := (List.range 34).map (dec 29 0x2eed7215548a0748a7008f5162364269adb1ef9bea227d8c180bc149959c1edd90b4abe736f4ab7724779a5d414e2e8ce95bff64273a32b96f00a5147a49367cdbd802b8b6ca32a8ce2a7233f1890ca6844878fc4fe4205eee3862f73d1a996376f8be819745de99b59030f4228b49408c4160daf7472b72dadbf5a)
set_option maxRecDepth 100000 in
def cr34 : List ℤ := (List.range 35).map (dec 28 0xd412678af2071c984c9b17d0efe4a0e1bb686420f98007ad17f9b0f07585cc56b861815abbfc0630347d52e997c517800e619d6c16516ef6588c62b836f4027b6a57d7e2a79299aef0a8b6ed0c8eca73084dcb4c8b8f8417f09c927f3ea637ed7ba980d489774286a0845e251913252d8e8ef75d7bb33477dc49d)
set_option maxRecDepth 100000 in
def cr35 : List ℤ := (List.range 36).map (dec 29 0xd2b4e08c7d4b556053382906e470d860c5c54a6e683e30bec20fa9bf037dc0e2d3b3d6cedb67d77ec147c1e6a6f60327f7881d541e970d2df67d6633965ad16cee1f9c9c26fbdc7ca82738cecc6c2712326069518869f28610bc2c57ff9fa0ae2f190593091831c27140f6af721ac0b78fe987b58e0a1913d681c93727f13ad680de3)
set_option maxRecDepth 100000 in
def cr36 : List ℤ := (List.range 37).map (dec 28 0xc95105da0d34b593daaf583c71328f17cae876db8a9eac249916c87b7d13f797d9c0c7743c2717406357606860e6713a4c529f0b44ef6b6b6022b7955114ec85f037a7f4098e7c41154843589d9d2d5628caa3c18b225588631e1b86723d77c37b1e7fa07ad7eec1a68326087855542a7d44f3087163138220fecdb3690767d109e)
set_option maxRecDepth 100000 in
def cr37 : List ℤ := (List.range 38).map (dec 29 0x2e6049a12b5bc22988628846daad71f3f5ef90f1f1f8877d1ba4c7bb45a39f0354ffb1ea17f94c463d89d45ddde41e8c452052677b51927b94b4545a4e04b74404d764bfecb8e1dc71f61602af9631bb80e41ad4f98f3ba37ff4ed102453e847b6e141a8c4ba150ace909da11b86037d24291196608635c3047efc18cb4d6dc5104a078c7edcededd1ed)
set_option maxRecDepth 100000 in
def cr38 : List ℤ := (List.range 39).map (dec 28 0xd7d667aadf4e9b8c9ab45917f8268ca59907b2085c76a20448452aa18f1ef4685bfb0074c733b785dcce791334c6f5ac6f555f4cf6a605bf3ff422427bc7f5826dc4b7e06f087d1bf6a80017068002311818698f8fa23e58b4fdc086e4198849f32f7b2d0b2809e3f7809749380b36b68503a4682e3c6a830926d8a9aa028908332dd6f7d07a9e97d)
set_option maxRecDepth 100000 in
def cr39 : List ℤ := (List.range 40).map (dec 29 0xc4062695b85e47abeef73d198af6d9077fe3467ca959dd4f3df013f6a6846a989c749c27e244460ef046bdf7a7617e396ff8e9972c66c9c6510d5cdce42958bd7e951af586ff646957ede2ef3f2b8a11f7338cafa21e907ea8991482cccba281235d064b90280ad87ac0ee5455f8f4afefd4be077dd80474222ea9205f4c8b035d6c38b2f008c45fd4d77491ec8dd56f50)
set_option maxRecDepth 100000 in
def cr40 : List ℤ := (List.range 41).map (dec 27 0x7c906cfa5a9c294fade7a893cc0c899e4591e064f1da477dd8d206447e2fb84b42b31d9f45e2c7623bb4c5717951e1ee77337d9ea792a3591ff530eeea3c0e67de418333eaadf57cf1718f70977df28c7bbdc1f9b7d28667219883a2655b940d8ea57f4a7e6ffa0ae1f1409e3e89ae07b87fb107585ca016c03404b24c8ba719b110a19f739f0db27fa09)
set_option maxRecDepth 100000 in
def cr41 : List ℤ := (List.range 42).map (dec 28 0xc7a072c85847229425b5f8c5ed88929d42e877bdf988de898878119a7ad6f22859b64582482c4872a8d7858b1d77afa27c7c6a5ab79dd0ad73e5dad621f38568129084d2f0ef81d15517e1f16a7e06c007d1b4997e0c7747d65da57e3b1028880b3384b0e3980828bc7f52c2f7f6fe8c7db5e6f7e2c72d7d3ae2881b28337fea49e800a34485ef6118434ef3ae65cd370422ba)
set_option maxRecDepth 100000 in
def cr42 : List ℤ := (List.range 43).map (dec 28 0xc6a99968b6c7c4858a6b3942fad18c6024092a75508765e1888de5008780f4e7ad6dd4859b4f2824814c872a53e858adbd7afa1367c6a4a279dcf1173e5af9621f1b9681289b4d2f1d681d15297e1eebf7e069d37d1b1677e0c6217d65be17e3af4d8880bb584b0db980827137f52a997f6fc477db5c407e2c5657d3ab8981b27847fea355800a20685ef6998434eb0ae65c8f70417c2)
set_option maxRecDepth 100000 in
def cr43 : List ℤ := (List.range 44).map (dec 28 0xf2537ba84a469c8562c7a74c75e27259375840902a6b746a27fa868174e5ad580330a77af9492779254b777f47267484676a36f3c7c5d76d7d653358766b638fa6a89a622e27bc1a21e88500b18363bbc7ed26fc7e6f5b47db4ade7d9c1977cd05e47d79d637c33daf7bb3f807c17c667cdd8007b4737f7efda807f7982b7ea4f627c2e1577bc50bd7bceac57c6816a7b6801155228976984948)
set_option maxRecDepth 100000 in
def cr44 : List ℤ := (List.range 45).map (dec 28 0xde98f409660b0c8828d6d8990c787bb7c496d716a781bd69c69a770d77bd47a6c6d9b9766d8687167e37734f7cb796976f6da33ec6e1e2a38cf23ff887e7b48ae3f7c95fe8c8b3ca09981f694286f9b23824727a7e963e97e483737d7b95f7e1d9e67d7c0f2742457f7c1e6347bc8cfb7c5d81f7d200b37ba8ba67f59eb37fc4d917f13c0c7c4ad3b7bfb5c17c032697c5198c7b72fa7552deb06b53fd3)
set_option maxRecDepth 100000 in
def cr45 : List ℤ := (List.range 46).map (dec 28 0xe1bc4bc88bdefd87604aa77bb0d6769ce8277a51f872b5cb67c7f2d5704e6da7a375a36eb4dd9768ddeb76e33a97126b2b783ef6868f429d6a064d18c46bf8881cf638beb7a498260a6abd691c83abfe386e175d82d43c37fb6fcb7f187327eac9117e937a97e1a6097e9fec578fb5007beebea7cdc6a17d993207c5a9418001ea2804e0797fdd7e07c7f2ec7c5e4327c62b507c28aa97b86fa855429ce6e9fc6b)
set_option maxRecDepth 100000 in
def cr46 : List ℤ := (List.range 47).map (dec 28 0xfdbe9918cca35b9289f4a94f1a8b62ac4e05d45d04814dfad6c45bf1738a03a6cd05fa578330e5cda09b6d178cb6c0b4b561b39b57017af1509870b52ed22498049c08fe9712988dd52b185a56d1bf6ac8810a488ca382f850f62d7fdb8897e80c737dce4907dd14517d17c937c3e86f6fe0d8d78024387a33c7c7ba7b9e79615f680a69328120f26807e683793119f791c6267921fc07829b8f77215cf2a993866070e34)
set_option maxRecDepth 100000 in
def cr47 : List ℤ := (List.range 48).map (dec 29 0xd69c4f54b57ad9e3613b9d0f156d8874981bbcb03ff1e0dacfef366fcc775a97aaabc6aa95bdc012de41e1f500e6503110c7058c9229eb20c3566c5a63021e715c9314605915b5d3b879073a470801ae6d823ef117f21383e56b6c47cd366211eb8312e2d3c88dd00d467e9d3ddb0fcf6e77a13c83bdafebae76e15e7b5cb9013da3181c83bdc12ff26a249651d1021ebe8ab236ebdeb7fc9f8733fefbee3c67617e823c123380ae9415b1639c5f)
set_option maxRecDepth 100000 in
def cr48 : List ℤ := (List.range 49).map (dec 28 0xaccc90ccabe637964dd118d0814d886ad278c25f4271c0de46f3fe45793721b7891ad354c28dc56283796e0bf1655aa0ad62299316460bbe5a78b2e6df3f78489b1a14f238f38b9fe1f88047e99483d0caaee06c87b9be1842ef3a87a81c78541fb08a717638e43ce094e9a757826647753a50e80bea5e7309a0e770e3ef824cbca803992f8194d8a84faf82848104d85c5269759df2676f551e7cdac5b769444f77eab2b2b7ba668147160)
set_option maxRecDepth 100000 in
def cr49 : List ℤ := (List.range 50).map (dec 29 0x355c24470519f81b6b66ad4ceb199e406072319bfad79bc11fd32237a357db4b20f1eee7373b3e8badeb8fc9815b6ecea5927256a7404322c1c799303cdebbebfbb6d33713a3c60f394dba34108621f182fe6ff465418c20691ae521a4a2e863cbf7c9626c9a425523d1f001948abf53ac7e0a3e5ebdfda2f4788b47f83d64bb8a55f9e542b0d09d197282355674257dece294a8f7128b5e78bfd77cbad1f4c1e4141d2fa530887719e1e3c37f3b8c2907e10474e4a)
set_option maxRecDepth 100000 in
def cr50 : List ℤ := (List.range 51).map (dec 29 0x612f9ef235d5320f7b4dba8e2232445a040a621a952112d8d418b242b4bcf74815ededb44f34b8427bb83c839386481b2a53e2f6969586d663813a8f25d5d203542e13c5437b4a1feb7e42b0dbe841c3082c3cf80d722a3f9ac99203e355912137a7855a54445ac97421d0507f118623e84c6d46c3180962031623104608597a8f22db6440939f9c40bafe4561b8130a77bf4bb64e291f3030e1a87f769f1b0c03d366e0100898f8600107d3a7e9bad3cf917470aa6fdd3389)
set_option maxRecDepth 100000 in
def cr51 : List ℤ := (List.range 52).map (dec 29 0xc992950d26f09ce74b9e82f2ab187a9378f952f6ffa6733c3c93066be199f3551bb370a95d321e4eee02b656f07fa7b11e880da1b91b0bf3bc495ee21f233470a2dbcc8b20df8907277407b52fa0cb75b35fbe8fbf6e9b7d5a76f4148959e22e3e0d13b3ecd8c03ee94c0f4b427e05a9514c932e8fcfdc7482cdb75ea6c5acf18dc017659be83db561e5cb7a97af40591a847fcd63e737ffe1a916d10b7ca107be4f87bd2c2afde1caed2e818bef7403af23e3e3658ea77d88ecef8e2)
set_option maxRecDepth 100000 in
def cr52 : List ℤ := (List.range 53).map (dec 28 0xe622294a32cbb3a5d11b0951d5967955a62a84be0aa20c831996323b9aa984196fa01b7a7154d70a0c9f6e1fcb067b98736d29a38682d6336f01d4a5e76d816b5e2057657a0362cebd3778af9d6579b535f4100382cdabc81e2e67848311b8a353287ca8e6c8e7a3de99bd0aca11e0ad8f042c58cdccef9264c947bc1de78249248819d52481b3da06c661577d478dd7ddb9758104a1180d27978787c9e75021ab6deaebf794677c81f2c6a7b01d0a5f5e7ab384bb4d6cee128)
set_option maxRecDepth 100000 in
def cr53 : List ℤ := (List.range 54).map (dec 29 0x36fe28e32745df8a352a41508799ea5e4d4f5114899f9ce74d04aa4765e4844a3128c09699e893e6386f26c9ba1569ae17143b69d7e68b2e0eee1a388818da81a885ccaef1317693399bdf016e0abfd67b32b10af4b5f65c4ce362f8a877a7cdc0a5c1c62aba1d604ed03ec6667ce68644b35a33a5e60f23230188587474b6c5560e120cc18d907f881876f7abbbb0800ddfeab0d10340a5f7f828d93cd015762042fe2fadd94c6d9e97ec0d8146e0e1da5cff60c4d7b2e352433d08589681b74d286e4d)
set_option maxRecDepth 100000 in
def cr54 : List ℤ := (List.range 55).map (dec 28 0xe02e2c4b684aa096a7d2ea733cb9a186a6e8b1d8e083f34f4a19beee98bdd82945db1494ccf549aea339748a7cc728ba44724e5836c771bd6b0063162b5ef7691a5da5740abb62f5cb865030e0732d3aa7c74ef467c565e7645b957b741d47cfd05282b041d859f8d98ec868e87cc985965ca509ebf0748f0f8958a6b4e48f466ab83d035c851390382231857174e017ba26a37b486f38171a457fd923a86409d28f6917877a1f7a80f389981bce0474c98ca74e88ca7ba649232f001775018b0)
set_option maxRecDepth 100000 in
def cr55 : List ℤ := (List.range 56).map (dec 29 0xc9d3d074d29d1ee8b09a67317a558a6ac97f52e9c8fe37e7d730f0535da9ecfb6ce31588259830d9292697097297283c544989dd8d07eee97ff975a4370b806605d7ee826ecd92a3f55846283081bbbd8f6ddbcf086c38793f9f9337e8eb62d4def8fda703f7f3d740c1360d2e16056f9275178e8c2132ed05717066acdb7920dcd3f88f9bd1c69457360b04b49075eb708a2a6c93d3477bdf6511290b2e2667e4a6c03affd9522ff452d20dba8e7fda82f3d443aa9f2b8a32ff255bf77aa5ebbdab315cc6e8d70e27afea)
set_option maxRecDepth 100000 in
def cr56 : List ℤ := (List.range 57).map (dec 28 0xffd1bf080954608e056618c8111393423dfa35cfd8aa7b1568de8d6680a9334a0da5fa92951738f9e259911cbd3960a4d9775ea9d75de63475c6d7a6aee77a6c8daa66f87d666d00ed4583efeb6ad18e85d38f6d7318f6279845c86651c5175e9acf7d88bfc7e782508766dc890f44ad95c3a5789af1209e4aea49b3985091e4d1d8bf8709918be9a7fbe7e67fabb379508b8b7a0545978f882a8308f6f7e99f6f7fb87b089c83bc8c82d988246b4b74257b37bbc5407ff0ea572f23cc78880aa3525d5a71b2235)
set_option maxRecDepth 100000 in
def cr57 : List ℤ := (List.range 58).map (dec 29 0x3986ddc92b92561951cda1ca540b4a3c33ff92326970970287a4162215e55b02131237cb69e8cdc54b0e91b644be0f52055a8c923fd613be839e5d98f20ced060fc714cd46b774009d9afe4badb0af615be81dbb801efe97c27c8cd2f66b476c1877309dbf11b71733aff21b3f7f91972c0c05b2e1025b5f2ef57818e48ee8d09fd8d670f0abd1e34ab78a7c9bbc7b02b85ff8a61effb43407e22dfd3c618af9e501a8afdfdd0d74cfa5c3cf46b520be2ac30f04ec377eac273b5a5321ecb2be102f977671355cc3b35eae0e85c4f4d33da62)
set_option maxRecDepth 100000 in
def cr58 : List ℤ := (List.range 59).map (dec 28 0xc925645b3f90fe9fa4ca09522ca884c1275934d7ef9561ca89c7126e8c6cb8a896041185340d9ab9aeef8b7c04b861d83d85f4d7194caf1f798add4787d1c37d7ce5e75e2af16c9650a6cbf07e62741fe55365b04fc1ffc7a835b37a218bb81542bf6f9b49f73644507f94cdd81e24d389d85698c371198d7e238927636c9e6590494da193896e048881602d852aba77f11cd883e4352833588b71d0760825bef271c400e7bdd34370dcc3a75d86d77ab67378a66dc3722a0667cc3ed87b2157172b7ca37a6128c3841cbd71362a9)
set_option maxRecDepth 100000 in
def cr59 : List ℤ := (List.range 60).map (dec 29 0xba565e7d396ef329c4c75f3d31f6fa19f3a3c3eef49a2ead7051ffc7c59b7f0d04262511222ff39b029ceffa5208de4871b8d6389cda71a29b77915ca61bd92ef79e94778cf5bd818799a909b77d71ed89a3c00c7d7e915535ea33b6c5d89d4bba3cf7806df77f5a0d35226901cf6432cff24dab7fa4431c0b63d360eb3aaf35eb04b8bc9d79d3f0fc3a532f2cb27251908b4812dc84506c9fd0bf32fe09f1c8096eea3cf6e4fdf17b96702836557dbaa7c3f0ae8363c7470b0b61de981bbca3bbc2af89eb9bceeff631837334f103c658dbce7a42ded19215f)
set_option maxRecDepth 100000 in
def cr60 : List ℤ := (List.range 61).map (dec 28 0xd42fdc0b7bda4c99af7d7a27b5ab9c04ac48e66eee920e7a5a62cae891c742c93046c67935e4c8e5b5ea8ac5159a05153891468938e640538df5a458670dc47a7519d797ee4a810d9647437ee477678915b4a3fd657dc293afcc377061f78872b8b1852b76b7662ca8601423e69aec5d7f864587f894be830972786cf0ab907d3148b469b39b4aeef9ecff1b88335ca740dc316e804cc7f26d567edefd88149a5e7a7a43b7ab4eb98194cb77b6daf57ede7e987a9e75872335888c77f977caa007b852f37fdbfa8725ce487822e48315015671101b1)
set_option maxRecDepth 100000 in
def cr61 : List ℤ := (List.range 62).map (dec 29 0x301b711913430d4961565a4662ca3299ee8212b987238af938d45cad2761649ea316b723c99e254cc89132ee4275ae51188fc39c4c694ccad33e650d3c3329b4eab987e3543b1c398dd20bc9cf1496ef67b837a32c2e6a15302856cec934d47e785f34652eee4df874909a6c0579f580b36010259dea1300fe29a1f7f65e36c0d446de0e0ecb90e83e918736a0447171c1a3d473ef0a9fa367d87879be309fe600771af004fe9a8134ff6bac8de75e3ca55efc1117a7f6706c3f6b01121a43d3109eda9687595f73d0aaf45f058414f8b6ed175417313e1d3598b3077e6fc9aaf1)
set_option maxRecDepth 100000 in
def cr62 : List ℤ := (List.range 63).map (dec 28 0xdbb74749af1d507fe4769947abe29e1b728a1d4fe28fea8d29a89f06892131993a775f9b4befaad33f5ca0099d996305708a34ac49ce17bc8a1c56589afe1f87da528829927579dfaa278d54ab738b5415b596a1527ee91518c5405a84b707e6ad197a1a2e27137e0d764376f78420c96a8dfe97214c897dd94b67ea4818845a1cc843579087dd3b8866c8228cefc18881ff44888b91684f825e8749d5a8075f08809dac981caf3e7663bb4795cf427ebb7337ffabf97fba76486a5ba986067c687b1dc27b0f8e17ca43857c8b2d376b3c4477d85d62b5639d7e8f30d)
set_option maxRecDepth 100000 in
def cr63 : List ℤ := (List.range 64).map (dec 28 0xf9bbce1bbd02be9b464a17defdcf8cca158a8002abbabe060a61a142905b04ca1db48382bb403a0519e0bae4c0aa507c7da0b81e08a7be5cb6369a48a2848787e758c9ac5973a2d33046974fc3657c31477c34f35ebf51c44f873f000d25a582d8ae661b01286718e299e2bc484185a776bac2a689acfd863235c7ca25a77d8232e7d670e77bf6ff7897872e8a7d24e977547384e5de8876744884395cd86314af7e3a9a47da42387f8356d7288097752015f7b05e0b7d088967b4846c85e65c185b6af686a73df77528617890c11787ff1c730b90073484a60080fc669641df)
set_option maxRecDepth 100000 in
def cr64 : List ℤ := (List.range 65).map (dec 28 0xe89dfa37a93c8581f273486a6a007eda58a8dc87ac8724bfa8d3529c91f55948f0c3188d14887886a7758a225248d14b3776040dc8795b8c8095d809e0cd5c8a6e36784356e07f2d6188bbcc66741ee707204c0a715ff2466fd15764952f863fe94b7e1db83862b9d6708dd788145d2e7fa988f7ea79807d6b6957d434827d432827dde1067d416537b86c408093cf28273475882eded837dd7a7f2281f7eb07747e142057dc38807d04f457db6cb47c24c797bc2b1f7c48da17d0c45f7b8b6a07f3e85d7fae79e7ef2d8e7c424ff7beb4fa7bf39257c584be7b6fd2e552a8066aca53a)
set_option maxRecDepth 100000 in
def cr65 : List ℤ := (List.range 66).map (dec 28 0xe5d880b92ed9a77bee32b8259522881f3b47cb12e08d899cc86845cc8cb42309311b588f5420c8b754878e2e71288e1f8c8d3436e71fc86e8796f9b80973b09e14c218a029aa849bacd7f412708bbb1be741fe487205d62715e93d66febdf649e11363ee3a97e4eb9d86346727062aea814603b7fa9c157ea7d077d6bf2f7d43e657d4357b7dde3707d41a357b872c980940eb8273503882eb2a837df797f22e677eb0c937e149867dc3b9a7d053677db70b47c24b497bc2c4b7c4917d7d0c8117b8bc0e7f3ed7f7faebcf7ef33b87c426a07beb7ff7bf3c0f7c5837e7b6fdca552a8a76acbef7)
set_option maxRecDepth 100000 in
def cr66 : List ℤ := (List.range 67).map (dec 28 0xe3168657f62a5d7de022f73d261079be42d6ec4fd57d3410e704987c792ef467a083c4780c0c9794e54478072846a96eee7f030f37b7690979652b07f5b35f7fcc31a65d4c4e70e8431732c64d71247696d8efe78b5c7f38d62d968decfb297362f68e6183889ce09d8be3f83922b146839703189ecaa982e20df82a210c88a44e686c33967945fbd7b545677de1c0b7bfe650754e511792533e7bbf6137ef777a7ef88187c344e87a6f53f82098b482b9c1d86224e38dbda8890b68ff8d4bd5f866af9e8bc02177fd11ae8021acb7fa51629009065885736e86c273fa21db569c546ae8849d356ace7e9)
set_option maxRecDepth 100000 in
def cr67 : List ℤ := (List.range 68).map (dec 28 0xe1ca10a902e2cb7f5d5147dd898373c366879ca9c06ec93647d2231d704f71e793fce67a01751780e9407942b1378665dc6a9b7f97f021997b4aa8379637207f57de67fca02965d5cb270e527c732c77d7126a636d90dea8b653cc8d4fd158df6c0a973ae958e62bf889cecb78be462a922b98c8396e2389ed16182e21c182a214688a464986c343779457987b53fc67de18f87bfe087754d9067924f967bbf0f67ef73bd7ef85b87c340977a6eeeb8209aea82b9f128622a5a8dbe01890b73cc8d4c786866b4778bc0b017fd11148021a887fa508f9009d2a88579e286c2c22a21f6a89c55d3788478cc6acd5b9)
set_option maxRecDepth 100000 in
def cr68 : List ℤ := (List.range 69).map (dec 29 0x186c1ae98ced3494791c0c1df99b44ea5ead67003a55b86e2531a2486e2ff0197d704a20836ced751c887882ec68ef480faf8fb402cf358f029f6e74ea137bf5c1c391b7c55ee1489eeb2eacf5b16be4b1688215ac8fdb4df6ba4c6797573c0a0d4d206083f2fc841a597cac06c2761fd6624e8f112f6c9c99cd046c602e95a4447ea51a804168587766c8418d7a3038aaafef35517f6dd113e7045b9e983ee2daeb9747b2f60f3bfb1e39d6cd494eddc0007af71e0bc4f43d20ed711709ea37b83c2e704a165d4e32dcbfb238c79d7f9f137c23594c5afd920adc310f468ae1bb461b1dea696a89537032e6725f2c9b9bbd8125b7b190e8c6b59)
set_option maxRecDepth 100000 in
def cr69 : List ℤ := (List.range 70).map (dec 28 0xc1cd2ceac580e08d938df8fe6ea77bbee76799816a6a1a3e17594291578705b776dd976c21513677ca6a6b433c462e28af74267ac6576fea60f8d4e7d5718d78a484b679d0417a8bf1b75bbe6a4dfcfb85fd081c67b14ba64e9f1f60913c28d17fce8f6549e8365a65a9aaf3e8c5e95f9b7e05889532428abb2ae8cc5dec8f38ef198e93e0899b9f89c609d69a4705c74c81127846b947464b71698c8477431a79751245c6ddc26c6ccd34976a89047c748077acd85e825b1d68325a737f4843687f514f88e80ef99432218fdf1c89b6179e5cb4b2d605dba756f8f06954fbd37b8a5017727f506e9e50278e805c9c0b5857ea9ab8)
set_option maxRecDepth 100000 in
def cr70 : List ℤ := (List.range 71).map (dec 29 0x546aaf8e4388f6d487317c96e62274d7a21a1d9bdcf6e6b8a746fd0b8634b93f95752173eed428f47147c4636efa679a5ada00d362d1171bc94836c082d58a32bf8e4e16e8716347cb62c5e45c7dfab2e94444d3a81259b15de959afe2a62e1250616fc9dc8c4139eda2655b970ebafee85de99744f1ef2655d8fed1a56a22a2f1bb04a5115d61d0b08d0f29b12861d4474998284e2d99354fd92e487f0bd3cbdc6df2de778944e802c347c26e65bb00ace1dbff17ee4f5e40763b7fbb8d7462623689bf178053388d6859ce2ecd3e9b119ff18727517f82531b8e9d76dc89958300e3bf880883dbb774d9e9d6cb59cf1f46df617d351c06e26eaaff40d2fdb2e50)
set_option maxRecDepth 100000 in
def cr71 : List ℤ := (List.range 72).map (dec 28 0xbd1d621ac134c792a631b99d992989008d68a9641076284f073991ba7a82a93668d1665d3ec1d780eb43780a2bb672202160cad28646513a698f61a71b63966a0dce370d0e046d9d6a86bcada172117e36a6a07b3c6907063e6f746c9b20e6f8fd7d6ccd7969014c0392e5e79926bbc4710377a87d5819a1586029c16731a092c3d9d6ac0879b9eb58233cb58800b3097315f4919a9be7fd19427faa2257ab2f3b7742e395ea701974a5d7a50eb3467a093816a21e596b145556153d7b92556e598aa464b036e00843c5ba7b3b642896cd4a8060cec83fb8ee82b62d082ac53083090936cae7437c178d67e65350804b2eb7f6b7aa8c9486771c75ce)
set_option maxRecDepth 100000 in
def cr72 : List ℤ := (List.range 73).map (dec 28 0xcfb601c9e84b0e9e79bf2bc1b585cb788e79592651994445a67071a4616f634684766c587773e4e99be167484a2430861a40175e432602c150fd35e6caba1854b2fd74f0de7867cc7ad6b0bebb5d54985666e9e25bf265a21ba3ec540d55161ba242683ae4b53f9086a101c99a6d256f85a1d1980184d68d1893bbcc2ae69c6864dbfbcc97a54814785e9a409a1b3879148f20b97497aabbd26675e3a42787e4e3709f9af629835856c6e81648976a45fb01645d327e5e4d4e05a0c0ec485bb0b7b90a527a1672b8599138977e3ed8e5cb7b90fda1e87eac699019e3a99d299f97e5daf9da7a637a682b172e78cc7c2dfc2869d1a182da2ada609a1a50c1816)
set_option maxRecDepth 100000 in
def cr73 : List ℤ := (List.range 74).map (dec 27 0x3fb5823ca7b6d5865243b4f6b72aa6e88866d97979b76b4d40dbe519aee07311ddbd5e5d362a285a156e71c4b1574a84a74ffc82b2da4e88e29b4d58403b51d80db36c9d7c9de02fabfc65fc79c2b31d1019c25853b2f16813e77f29321c01778456aeb878c4a27e996c780561b0e0ac627a0e86e7b77014a976cd10c2c5244ccd13e4512b938666b1fff53753259320e1b755268e5d8b033ad95dd78aa786e0d641d972f95a5e428f60c062c85c9320ddae562ec5e818341f22fd0634a083fd9414f9a78be7eef2aa805a42c8cd41abd3a8af4080ff3731e48489ec94f5fc91ff2691731469ee9380b40bdc07d912ab0188a6aae80672f33880)
set_option maxRecDepth 100000 in
def cr74 : List ℤ := (List.range 75).map (dec 28 0xda3f30286f2e7ba0e345b905b33b8fea2c4b0522c2b141d1d952dc4d98e0eae6f35c9d6bf7f5e63ee7317195c964e59fcc77c70393f709f737d6b9d1e553d53ab644d65d40aa55d15bb5738a216ac011b4f9cdc64bd0e135e59d567e518250cc659d40b87304f1582e558f870496fa0883aa49784485d584d111e81f1f6f89c8cf8b37e43aa7040cb94c6d0d9417eabb6eca5eb8384288eca4b8a95e348c5ddf336f3b0b6746b7df6e0f6b95ceff3e451caf1665d4c73cf30e343e81b97b2721591f56a69a5479d849fc3e863010b901595e99b52f398bac1aa26dd10838ff2a3f168249c94ee89b4239f9e5d3487ec87817c4b6757d3679184bf2518249218a70de5255c0b50)
set_option maxRecDepth 100000 in
def cr75 : List ℤ := (List.range 76).map (dec 28 0xc6f29458095c3d89c8368a51142b850e33695f43539c27d5ba589d308b923bb8d9d6e5761ba3674383b47aedbc26e636c964978a282b99d85e153f26ea9e4b4e170db6b7a57779e91d66effb376ad073f6adc7da6b80435652c14061dadba7c68cc74987a266512ed56bb9a6f683261c86dc4a7873a406887e6818a10e629ea87ad95108899d62a0098025b795bafcd9174c598c7d366988a91590a0b64bb3cace687fdc86ec37e474355d16c059d658f829f60496cb80f320e80a0bfe7b7c7ce83f622d82cb11184180ff84f3cb2869ea8b8b0ce3792d2a1a83dce7d555c58a81f507d839c659841ca8e8640df78cd956d7f6f7567e905ac7eb49f78153f4d805289c8f94ddd71c4052)
set_option maxRecDepth 100000 in
def cr76 : List ℤ := (List.range 77).map (dec 29 0x158a4fdc80682cac9712d2637cbfab33b68dc88f1b9dc7b367367e98c5551256b18d02bfac7a43d29e8557f6f0ba3567387ee13614b345aaaffb8f499ca46be288eaef70b8571f01a8ca30a4472c7b43b8b61c2d81d732ef4f8ca5740c0f42f2f6ae5afe21f4ef446f73b04c202dab2c158a0cfecfbbd28176ccf8ecb48ec9669f0dc50c8d9e880c21544b51400691042872f26a08a4fb3ddd43b6121f18d4c308e292f856173cc989156e6949f92fa12d4d7dc707d3a5bf2a5cd1ba18eb55db17de2460bf9ae33e2294c2709bdec284e7fdec3988789b82ff5cceceea46e900ce389501ce0b3e0ccf82c38c81af0bbc0454555eb8d04cfdf354a85b79bec24731420671c70ed2081582640f3409f584e3c75530e3acca3)
set_option maxRecDepth 100000 in
def cr77 : List ℤ := (List.range 78).map (dec 28 0xb4478b98d0107b83f33859506da88d746d48de16218e5f84391372a28a7a7669f73eb38afc1268cea0827f504c07f31f9e6737fc37fd351c61a32898421e825e00db365a675953a83d36351817781539170e3a17612fc9b79738b66d788636405afd7045e3972a322038f165641f52e382fe7ea7db5bb3711d1ef98e641d9d3603e876b2f578c2cd1af11321b48793c9cffaf49681e7388b86768e9bbc285d6cd58384b278993fba8977e447a7b12f7c64cd87aa16757fc20a26ff5ece84de8a57af0cde8de50958432e8c8a02d068ead2487d04e887c986ac7d77c6b771a1447d6de3677048fe7ea525d7b57297638e4c67905352842b92684da6bd831792d76fb5ee7f867a1816d0f390cfeb3764592c)
set_option maxRecDepth 100000 in
def cr78 : List ℤ := (List.range 79).map (dec 29 0x5972444646709fd0982378874990dc7a6367243ca98d1d5ba568d252484887a32261916a33b9a94d85e482b450e110208e82b703ffede75dbbcb424a7d215e57142fce15645775ba0b261b07d7139b26d1513c57747e5e39ad38a99bd22bce21e40f674cab7afe4ca6daf629c2f4bae5a2687302baa0ffd1d8e8752db76fd46a4aabcc8e2beba5461f713d90df389a604856866b8e5bba5090f568a79ba039749b15bf619f1711280bf858762cfb47ec7b69fc8be4300516ad7f91c7dbdf47e460a13da110778687fd3be83562bb6e29aef0f077915287e3eb9c5c89d71f86188efb663f37fbc35cb79a92c9e4e494cfb3bc727d045debded6cf99b503b0db8e6508211cf142be226e05e84c3020362f8cf9e883ee1e7ba220f844d4f5943)
set_option maxRecDepth 100000 in
def cr79 : List ℤ := (List.range 80).map (dec 28 0xced0e647d9672d84761cd77dfa0b8c86e7f88c84fe813060294503e8847ace48c69d2594b7acb91997d4959555497277cf73574f871102e4734d7b378af79a672e08e81db52b5d0de3060e6aa24b2c9966452f6b76923937b1e6f16996d29726f0746601ce55aa240771a584c832ce9f4176d2965fc322614c9bc6cc39296d17314934d8719c3507990260667ad2d678d4d5a096ad791848567a9dcd0dd98b4ba891bf3ff9589bde85dfcc6a4ba6248f3224d7c4cf8579c0694897567c7c7fbd08d822f07cf9a0f82956f28eb672d822541c894b5a38da073583d87768522fc07b96dee74c921387af72f7b75f777e30d6c820929c7fd34157f7510c766b7698b7db5291b9e376f53430640e701666b20b92ed4ba6a06b38)
set_option maxRecDepth 100000 in
def cr80 : List ℤ := (List.range 81).map (dec 29 0x168da7888264ddd3ccb6e3222242c2fd7197e87c435cc4e3983a158856b2180c9185676efc9cb4bc2638c80d438b81c8aad2cdc5d94a65d26b0b4e6ac3c5706b1e2bc8fc809a2ecd1cd92a3866358b633201fe814220fe6d26e7c97c0979836f2e88dada1594e54aa98683cb502dd1910d9326d96ecf49113a571b534738d5dbd41a48e00ee146890316433913be1e193f302c3b8a868ef684584d5ae55cd82d1944731a157807cb4d5ace5be068721935e2863403d4f62d3f235c62f104af3478179d353b63b416085b8b5230793f852621545b16f2e2e315c508985478188c39c2e17b820539c71037c70c7742dd3395a2db617b933ef5e53e57c292d141b3be4dca864aaf6f654c85c3bf54261338a167ff94eaa15ba89fcd36bc01a476439fc90e9bed70)
set_option maxRecDepth 100000 in
def cr81 : List ℤ := (List.range 82).map (dec 28 0xd587f87882c3d17fd72348ff6a958a0e4e5833670192b963693752f57de26eb8add27a7c383138cd0c5f9729c3798e14f988b10f982e33a97582dd173a012c6e4eeeb8026018615ae9e7884e286a9026554d7bbe51301c564cb06474227336b87e45672283e7360eed56a419d5ca5f3a52093cd835eee14c76e9860a905558dd7ce939a97283f6b8387c64fc8956d348512abd8a5639f88ec043947903f87aff4fa2a8a4d95a21de8bf307d9fe3bce8ac05119d665b078849ed87bd2dd8517f987df50b78e8f5e0968dade987bec485d6f477ff1c6c888a1af8288edb802a7b07c3e55178f24977d23b4a85f8c3483cf1ca711195f7f2d974754be306624fc7653628386cb4ed8c7fcc690ef3c16944b0965d96ef8309d9894b1ee47b382eb)
set_option maxRecDepth 100000 in
def cr82 : List ℤ := (List.range 83).map (dec 29 0x59f8297e0c2d90907a75c881d3107c0135182056f82aefdc7cf84e0810ca829911eaed2c31dc31be90b6500c6ab7f3e42f5ae118686988df8b20c8375501df85f24ee16e0976909543c678f4d9187dbee8246375882abfae6150e15e0d71cbbba9cb6105e6732f41901822ac1acd4be4c60d647227b44584b991ad0f66ab3c46c0990b6934ab5c7fa9fac54191b4face6ac32246ae1d69a1d0f2281e8da771243e2288a333eba11b627bd9ae949e44a5dbb245a5bf904facde85b9e1fc7ee66962df92a106d18ba825dd9542e7e26e2db9cd1199456d86ab250c817288e0461adcfe5ed957f5361abf83aa9e0c3166d0823f6f810ab50c0714e82140dfcef7688887ee0822bfc808621a810e3066a08474affa83ed671b20463e170beb6d17a732c8c08aab4a256cd8f0874ab2)
set_option maxRecDepth 100000 in
def cr83 : List ℤ := (List.range 84).map (dec 27 0xf093f1535ed721d54ccfc1ded7a844214b1a7af71e3c9adbd738d98a38e5d472084a2aa8694a3981399d9ef7310e1de7df01bc766ec8871131710c11b1c311b5b69522b58b361ac449c80e8d069aafc1d324f81b693139dc870f17163cd903d6b99694bacd0df5777250f21d064de106e7cd50f82f75bafca2c222dbfa5fc8b80f451879b106112f0f12b3455aa67ae1e8ca092d4b1bd92515dc0720fa57a554631ca8bd2a5255664e2e5d9ab5bbfb982affbf10db779d59f3f42f3bd683f23af06c0dba1c384749ba7f09204a6d4730819cfb56f2d363187dc4388f96876602b869407414c826bd4f08a80d6070784c3a2b498002643051e24212ffc14216d84858f2d0f687dee04b2fd44dcc1b75b4c19024233224779f41b9cac)
set_option maxRecDepth 100000 in
def cr84 : List ℤ := (List.range 85).map (dec 28 0xc111936b514e0395b73298058c098549f6d8619f2686b1dc4825618b708763287c64a79e7970a8772a8099b37fd9d2e8f19df85d0a21ec10926930e85a2e9e86b9493704763c6d6fa406088f645adc60c385df41560df7e3b5e4a4491856f1c887843218e6a468978054d21683a876c7483b6561021a68284140333811b76cf49e227ab65424466e534f9d302f8b479295b2fb9dc8175a2f92e89c7393aad83061856fa75883e298a686ae6accb0b397cee398bb7af274a583b7edc9ef7f8057170f9eed880d44b85b4aee863b5928bb37ee98f531e9339a0ea722c0c691eedb5fb19c081ca871829de7683208ed842b89286baf6e84de1078532c3887f5b1986762048a1c6588cef4e58b3ed998f3411481d784e82de66882cdd677fecd9a818d303897870495a7302)
set_option maxRecDepth 100000 in
def cr85 : List ℤ := (List.range 86).map (dec 28 0xd21aec98369b2d8977a6e9947ae77f30b678e190f18cd5b97807c7788184796796b8fa840acb883e22958d20b3b8eb22c07ea18d094044cd85f490378b653c88056ae890b1ec6ef0f036e82e586ec5d29602a9ac5f1b48667dcf7b724563768fb67a36b04f83cfbd0c4e4a9af20e58d47bcef79600ba0a53813d45dd584674be7c575ef70128edc1c7855f1e7dbca81800a0337bd523a8384c528415b5c7d408c97d8750d82d56ff825160c91d5ded899c3b082f1851833f7f37f899e17fccdc781a9acb7fc3db87e169447e4bb577cb85d07abf0ad8334c53805f13f8be046f81728797e81ab07dbc2a37cadf557c6db327b3d11a7cbd5de8468c0a80ae7457d908237d1b37e7c1073f7df988d7eb02327d6748e7e463057c6f47b7c924a882080ee7fc3c3683b07a7602bf77)
set_option maxRecDepth 100000 in
def cr86 : List ℤ := (List.range 87).map (dec 28 0xce0d62d78ebc507bf326884f70778307ba98097e9c845e0dd7dba5a881cfae382f02647bd356083404c78733a9d6e11f0c88fba937f258e280aa93881f123c8babff083fcc6684d98607307c1971786ff6e2dbd76f0eb366f55a2f6c3f9707d25fc47f53ae0534ff385a717e35adac26835e05d7dd78e465704856f3ed1c665705d7cf189a7b543755263a9a7bea17880188f280064ec7e50ce07ecbaa17e99e2c7de0bf47d16b148226752838f93c82f58d984999528163eae8176a61801b67e7fccdad80900f67fab9057edcf3e7f01cad7e479277d42e798110f6d7fa2b078551bf482a4ff57eeb7827e987d97df0f587e0cc247d666a57e285f18244945804781c7e93a537e5b6137dbe6da7eb71de7f1f31b7e600057f0d6317e0ea607e2187a8114fe57fd99fa81cfa976eb8289)
set_option maxRecDepth 100000 in
def cr87 : List ℤ := (List.range 88).map (dec 28 0xc886693801d5a78ecbb0680d60347db38e5791817c81a3d6482f78b986942418386e6380ffee47c0663a7e2f9588a5aff37d1234889bb18b8199aa3821da3081a0621952968181b45b282266e279df2a2762366c71704ef627453b6e6547c798e2ba81e255d786bdfa5442ee44fde01b7e6f6657d3439173188a06fc63d761ccd2a977aa10678186c771fe4f4f658497f86e5b7ebeec87eee0477cfb8af7dcdddc7d6b6047d6ee127c6e1a8823f9038378bfb82910ed836aa8b80a149c810a23b7fa51787f50a3c7f60b497e501527e72a507eaba187dbf66e7c5e061807f2087f87a1085a948e827a3567e0c1817de268c7ce60847d9e8497cd36ef7d9a22b826efcc801e5697e09ebe7dd7e6f7cfd6ca7e00cd47e8a52b7d851267ed49167da35137db9d4881416837fc3e9c81b935c6b24796)
set_option maxRecDepth 100000 in
def cr88 : List ℤ := (List.range 89).map (dec 28 0xe446642760295c7e437a091a332670d1f4a7cfc9d86f2ca097d01c9772cbff27f379d58444d787e0f3a77bde7747401a8b85755f07f3df17846b59b7d7c0b5813a3737c3866f95faee68d2bb478f9094b75f1ad97256aa76d938d466aebb0789091480d35c06d65fc06702df34ce0705755c0de7d8e1287b9471773f6cfb70306f3665d41f950a5905812dc27726a39542e3b97ebd92b7e30c847e621767c5919c7da11927d36dcf7d40f7b7c29a5d8244769836d53982628d082e0479804813680d91a77f6c6c27f180757ed68f77db13ad7e42bf97e84c707d812177bf534b803f4387f7e97e85d57b8825a7567da73767d902c67c6d7a07d6cb877c910a37d59e2b828221f800bc297dcbb497d9c8147ca64f17dae7407e471497d222f57ebae997d72d6f7d8afe181557b27fba1c481af0d66986dd3)
set_option maxRecDepth 100000 in
def cr89 : List ℤ := (List.range 90).map (dec 27 0x3cb7896c0024e180db2e8e2d6391cb982154b8af98f47a30bc83645efd05b41d499f8ae6926ed7e96dfdde49be86c9674b499b2843efdd8c2dbbe3581c87a08e0dc843b9d8338ba515ae75a68ffaa7b700e292ea9c7a2e0a79e2f4b0b7044eb8596946615c1a48ad038e0cb0ab55c04597109fad210f15378b03245a16d6ca7fe917dd812004ba6124eb54709978a104ff50680f9dffd5d13df39a77ad2574fea0f6dfce337bf35a2b81ba1ff24637cdd1a529b54a4218a310d706da6c60d11314055aab8001c1904393aa01f0e6bf074567e48426fa02f39ed1d46c14525a7f45fe5147bb2216f86dbf458ed7dc3f0ef972b75f1c877bda17a97cc31f908cdf2e02c0633ecb2087d20c16f8317f9f8049c3f5b2e47d70720fc91171f1ceb1be4b4f282062feff88ede0ec5d33029248)
set_option maxRecDepth 100000 in
def cr90 : List ℤ := (List.range 91).map (dec 27 0x1e77d349bc01353fdc6b684535d4e31529db352d454ce23e999e27eb9336add630d3c06a2867b493a0fb9e73a29152bbac8db87f137211905bf5d465023e2d1ef7de3c0ad7437cdc3ff68a3aa4055bf0252ab42d561fa2d3c6574947f13ae11d48b7eb30360c2f4e80c50561731bb706b406dc5951918ac2950b521594f203b35593789894b778d1ebf862100543c71b128a0afb130cc6d0dffdd3ebe105e07a0f85efe46b11fbfc06beda987821c09725a03a5c091353aeb0368a313e706daa120d116d4055b3c8001d37043991a01f1afbf074c87e484e4fa031c1ed1dcf41452fb7f46029147b96a16f8973f459ee7dc40b6f973051f1c8b6bda18507cc333908cde2602c07c3ecb2a57d20d38f831b55f805043f5b38e7d70916fc91231f1ceec3e4b56f8206274ff892d20ec5e0302966d)
set_option maxRecDepth 100000 in
def cr91 : List ℤ := (List.range 92).map (dec 27 0xe73253d08c613a0b27233a2fda58a323a2f9dee71b6453eca2e8bd95220c32d3d9dddcddf244342c8806c3af05049a5ffb5ecbf4a4a37840d951255235c0ba7eb90ec63815091cdbaf2997de4f1aa78c205cdea6cad4111633d7674a77a398cf5f4112dc76ad3387a4ad8819a3f3d87473f286f6caafdd88f0193483792327d137119d6ca6f4468c55f9322607362271c0c4738579c9cd2f0a12a02072689401183a7da0006fd0dbbdf913223eb365e7f451c91878c2de91900bfb35c68bcf60b08f599a0f612940ab70c80ace43077c2060971213f4f93c7ebd940fb7b3b1f21040c1a57287f60dbb136f4b2187e653fddea77ebc55afc4afe5f421e7be05b697d8518b085a37e03a0fabf290f67dd41b0fa40159fbe7713fc0b9b7e9b1c2fd2c121f418573e920aa81c98f0ffc454a0f4080b299be9)
set_option maxRecDepth 100000 in
def cr92 : List ℤ := (List.range 93).map (dec 29 0x1507b4e88b0fd1245b6c8761f4ffa1042e329845506d415c0f5a2a7fadb21434379079dcfc7afe8a5f43ec46ff87b3182deecdc18ece6e18a5fdaf0af2687ee40af45a1627ddff44d6f6e394d80b4b9d30d675416cf5c7a80494935c3806f2afb6fde219731919096068d7cb30d01de91aa6bace30481492a2c1ca1d67832db0361ec380d60889c85bbdd18a6d5aaef261b1431b4d8824533c81a90da0fb1d931d215eb9a9087e44d007a2164a53902dacf48480bd3be56ae55f05d384f7394e2790902ec0a8ae89ff342af04ba83a85d2d9bc098bf59e1261f9090e17b82e64c845d4d41a2a8a25efe8c57a7f3dcdcbee2874ddca646b06873cd7db9b0dc2d142560b843a900018547f3ba85bf7030a5df75464ea6e7346da459241885ad6055096aff75dc87f2c83fbf8ccd6a035df65020eead80d8a6b3f9575ddf87d53afc6784881553fe400d8f82102b86cdd24a20)
set_option maxRecDepth 100000 in
def cr93 : List ℤ := (List.range 94).map (dec 28 0xb8da366974f495865da717a334187732dec8b86dd5844e11f833931796d4f36851cd9688c94bc8dbeae2826044975d90bc856853988e0adc7dd50ab781af667ca976072e3ca2773cfeb7a8ef4f6de1dd75890ea856b87b342d07d6620e60f5cea2cb8a7e1758e4ac1c918f07c919f167a283c207ab8138a59c3c9b164654c6c48d7aaccace9527f90aa73121a87e01c8961fcb7e6ee768f8950d804161c89cb1ce9208789885425f87416ca82611548a725077eb70ea7e811a67efb4d477bbcb77f403bd9275ae47bdf36165e09b781d142d7b19896852db00836b9898c4e8f08d6a621805842180224d077fbc5172e304185b857e7b3366085eade083c899e833239b82406fa834d2b379bba1977ba3117308162893eecc7adece28196dc080f2db581b48a6834d8088309e4e83cd2f27fef3e07f923797f9a1bc80bbc25806637484587a37aee9ab)
set_option maxRecDepth 100000 in
def cr94 : List ℤ := (List.range 95).map (dec 29 0x510a0f7df73016d0008570853656940618999fbd92e302335a383fd3cb42c6489a19eb9b9014314e80a096cbbcd92c9e5cd7e90298f1f80136cebde7a055ef7bae0eeb6f707809d73ba36d21ddf678c2e910bde70b3af4b3b49a098efe4529ef5bbc6db7a8d3540b0ce2842201194cc1490171bfc71e63e6a416c69067d928ae337395857fe730e634d9469cc658bf68cac7322db23dcf31d0ee4016881170cc5c7108a085cc2b1228364a18ba88c67d83aa24794a50c204f18400ebdbe5483fdf04ba82fa7aab688b3e2b4d8237a5db428e2eeb843e6ee0f73bb6df6ee0e91b2f0f2e8968259f41445830b63170a62f281ead7b62631bccf7d91c5e87d510c2d3384ac25645149446150f06f0d3de3a83153c8c242a386080cda70544950798e697badb8e19cf7985b07065f381e6133c1cb371a1ee3fa30e5d4fc88da0c03fce32b1f9de5ccfd1adc3821280bc066671a2c3063cde8881c)
set_option maxRecDepth 100000 in
def cr95 : List ℤ := (List.range 96).map (dec 28 0xbecd0e895936c9827f4a97c58cd3813e7767fae2f680ddb007dcf90684518828a965b57d4972285b911e86c76a2749219c7f7e89f6f50c3086705e27e9f79d7d2dd0079e49f37b0c36f7710fb568ff92d6b728176fd234460406ce53b237b68a6e9b78b8662776b07d8c1f3ef8e18bb68e89b978ed0e4baeaaadb9044afea994c2aa6df029c208189a770c9f9289d7b8b21507868829f8628f7d8c9165f934c60482a528c8df7ef5a18d5428ae5237833cd208462ea083f7ea376ad3d97a728c978bba0295dc1bd905bac27822fc47a41b8578b1040830a6c98d26247852cac07d052b37846ca0892043785b4e258020b7c7b4a88f7c17dbb8a655797d67f44849caf48e3af88826003a800b86c7e92d6281014648158e6080cdf5184ab31e6e8886a842054c7b97eeb810ddf985632cb81cf852822ab5e7eaad0f83114ab803dfa8855b796849b54388399f666ddb0a)
set_option maxRecDepth 100000 in
def cr96 : List ℤ := (List.range 97).map (dec 28 0xc3da3f6872f0c08be751e825d1bf89ec40b933952d88e4a4c83ac53291c32f486e094a8a30e0278ed90884bd0a0829e94274fb2387b2f34f75d1ed6844f0046eacbcd72ce9f16f5707b6a0240567f8d45638b73859c2eeb669cf61360f59947d83fe428b8db7098c696dd310c98eb95d9d6cb3aab676d791d4b80dae12f393cb636f60cf9ef433ae5e396677c72e6f3a5da7a37afafc982526de960d9119491b8a9bbe05aa0dded681f1d37c922529956b2558d46a7084b806b8c20a5983ffcc784ba77e882e525bef76448fe336e717aed7823f38a55fada766190e2a4fc5c99ede8d28537fec93cded4a02159c82df71d816790b80514b482341f89c936427e31a0b821b2668cc05e68823044835148684dd22f7d1bec47c262d576f9a4c7f0562779ff84c786686c755a1e585d74c3834f0575a2e03e555ef5f8909c8782611b880dc50a9703753855c76582af45c58826b5)
set_option maxRecDepth 100000 in
def cr97 : List ℤ := (List.range 98).map (dec 28 0xb9e55bf73f36bb80e883885ed1a07cd49d77c637277f089a97d628e280df090810ba6782868948676327858076f7a8994381fc81b6d5a0337aef2768013e017d1036576ad02f6bcaa8964c51976ec10d6573d7b252d260966604ad792a9db7508fe85a6a9a46332bf7737c029710696b898f8208b5abef8aa8a128ac4ff7a9716a78b40753b941e78aa4fe08c3e59d9a89d42e9cb63367c06c3b86c6e21833e3f795ada0093325b88ec314b7d57e6c95f7689868a62b83d40a981891ad80443a780c11cc80e38377fcd14c83803768e34dae78748067c7bd497c2a550870133484483978666f3582a24a687b42b78773195849027082fc55c831364e8694e7c81ae78284ad8107951dac8221c858442fcb813352681ce1407fa5e147f882cb7f9239d82e89c57f539c489e76df7a02ee07c907017b1e6227bb51e77a445627615c48820586095a45c76cf497e8543fd57f9cbbd76c95fc)
set_option maxRecDepth 100000 in
def cr98 : List ℤ := (List.range 99).map (dec 29 0x51c9b0861cb065503299e28096aaac2da8c1df527ca6f9fee147cd9a0d4063f6a609fea7affbe7fd816a0243de779ddf3376aceec8c9b791023db4651c55e667000ee726637ab7835bd4022edd936bf8d80ad376a7bac5306f5325de5e45cbd3b373774bcd3be6dec11813d638d4449a47c7222fbdeb19ba15e7f710b9682c8ac39edc385980eb0b64bd164541dc3050d5d8f197a770b823b4fed54c7774cce4429460217afe1705d764f917c86f4a9860da4cc4b4cfd3f0f592c4a1a4203268a0cac2fd06a86ec81760a83f21d5d9f7e347cfccd2e67daf95441339b162b9bb18fb81ad28ce251d42b1869a11218e303202d181a13adc2db761e068f9b103508ec80d782ac0ba5eae0f11be103b5a2280ceb04c3a1d74a0df0dd4faec4347e7bc69bee373a9f9ed1cefbf46a47df5f33c2fe06ca120d43cf0455ff78b54343d0f8f9deb227f2f730af579ce6213c24ba29fa0f42d12825347389152c0095712100aa24da8f1aa)
set_option maxRecDepth 100000 in
def cr99 : List ℤ := (List.range 100).map (dec 28 0xaf5a7ef94eb3c47de8557835a5928119b6e83963db804e32a7df634c7bf82fb7ccec1380382307ae27bb7c904f28133c2b790c44b77e39bd76f08776372b5473952ef709c7aa6fd04166bca0a97a6349b88d13e17e733996832f2a81bc2516f4aee870fba3b722122065875986e07a6c761ad8d7451c79880d3b78856f0d90132c88f345c1aaba273a53ce50c2d38deafaa90bdaa24b3a9581e47aea0af825ab9b84a1b9587240508b202d4946112d8bcf7a97f9f64f8b12c74834223d81ef13681eb15e80071207d65ce57cf32497d3750c7acd35483d2fba8d0027b81007c783af763847630283d62d18153f2780a9c1c83b6a568253b017e9c76c7ebb8667dba9777c7eabe834785f7f6077989b9fa0861dc917fb65eb7eb7c677e1ed017d0616d7c083f17d820be842e43b80e79d77e4f10b7dd0fb47d1b8957ef58247f7de3b7e95db47e950457d03c6d7d21bb981cb4c07fe21db83ceb0c651d386)
set_option maxRecDepth 100000 in
def cr100 : List ℤ := (List.range 101).map (dec 27 0x60253d383ef5a508d6e1df1d73f41ee3a982b2a7706b69a1fe717cbdb3b4d7cd2722fc3b4b9f4867abf042ab802a14d02356e9e84b663d17f9b7a42d92e46716a001c74be6d9397cea68cf850495fb77c2400cff27ef4a24f2acd920eb68bbaf841b7824482eefe3cddb541fb92eafd7c75f36f7a40a21645bdc30cbe98b0d99f1207226557a944bff1f1a11966336bddaa9051b94d0a02b7c19228ff47b8a0ce8d3c13748a8231d8b14e49aa1d5a0744b575c86fd012ff67e060353224051e868087bc6fde65e5fb1ed13f9e0db7d3985f02f21be28a27abd729327e7879904b0fd207f1f1405c4208067f2d0414746057b1f3fafc3c7f6bbeefde440df9887840def3c7fb8ff709aae760c12d33fff7a57f790fefe745a1fa52db3f0dd727ed7cc504209b601e9643f9ec237efd834fd5937dfe5fde3feb6597f6dfdefea7135fa4c50bf50b8b80de5d2ffe87de07acbcb990b68)
set_option maxRecDepth 100000 in
def cr101 : List ℤ := (List.range 102).map (dec 27 0x3275f45c526fb48addd3d09e9ec63143b8be8608e80d554f064a23e030f633bbd3f27ad41a2f75b6e1ebd4debe35cf682d041307209ede7c3993b1aca57aa064cca91855efaa0fbe16cf679061a4dc290d5dff9f6bf264017a5d06ee04779df2e129b7336686e7fa74d7634e9b4d7bf31ffcad778f64cec07f522f4818c633ad6943c96722ceddaa51d67dacf8e6c309827669e10b1478c25b5a79b76045befee87ee01192ec4633088ba90e32a321523a53f0c7ca5198ede42500b36f2095599c0d9c60814fbeefe0391dfb71253ff8d937c74ae70322f1e4f6404bb0c28e7dc048d099420a10e0f3c07eb2980f250508e4ac60c1b953f795a47f008a4fbf57c1f3840c4216b70802b9b714f72720db478403639f7f4979cfde8cf9f58f4c3e429db7dfdf7b082311e0457fdbf664aa7e43528fb8aba5fe2e9f3ffc6057f4a06efda5379f58fd53ebe8bf81c5be3001b56e0ededd33fefce)
set_option maxRecDepth 100000 in
def cr102 : List ℤ := (List.range 103).map (dec 27 0x19909735f7e7023e1d6299f4c1cf2642be9e4503ec1231dc7ae5ab307278a5f32fa342c961f875c4befc0a6c6099925bffcd0775758a8f4af03a06417bba58d3e7271694cb0de41b30ccd3673b10699b100d502329e24b8452d032a8094d8cdeea5d21e4d05371b77d63cfadcce43b398077bcb9445db73d7608e36a90e0b3fad40ffa509348fbf240db4aca8ef4db84bdacbb43bf61777df731a5dc44696d91fb3472623871f0139e42cd35286eab56ed4da4a4a6642c37ba598b5237b0ba4eb609c0914161d097f73f40fa21d71f232e53e377d17b135a908fd792212abdc332e328c205db088e7b610b2f140adb3680a12a90763dd208fd473f0b0637e5cdf6fae84a5eff6efc171e6d7f2b82b130753e177dd93fb98027e60578fb3d421f44c00be0ccb47db657f0901aca05d24b3f6203b7dfe9c8faeddc9fb43323fb17e07e68474fe74d51f52c31beaa1a283471d7022465607690fb1cac7a)
set_option maxRecDepth 100000 in
def cr103 : List ℤ := (List.range 104).map (dec 28 0xc7a2bcd803bdb285803d68243be7871fabc8268cb181e5cf3775f2e27a7377976d770875e20008060e707811dd1747ce6477bf29b81a97a47c206dc8c4cab287264827d8ac968be7e028999a6494808c17de3ee17b4ced485d318085669a5881e7fc7cef0957fbf88794eea9a7d0a03687ec76c90c92e77f8dca1873e12184477d2850153776c8323745e4bd731b44370fafa65db4ca677c27076bdc27867b015e5cc2fc55c582d2829efeb786b8438362b8d8113c757f4687a87a8e9d82b16167e2dcca887d5387dfd4c57f433677f8a7087e9c4b87de99247d8f3137eb559f85827c37b7e4547f6a4c77b9445883c94cf81034f080dc7e67fee8177fb436e804ea227f688667ed61317ef89747e161897ceaf1a8151cdf7f4d30a847334082c52857ee2c757e8190f7dcf53f7db371d7cef36d7db3de7825f3aa800a9867dea5037da41717f8af147e6d99f7ee32b07e07bb17ef679d7de35607df7b5d8126e9e7fd0be481c69bc6d46eb9)
set_option maxRecDepth 100000 in
def cr104 : List ℤ := (List.range 105).map (dec 27 0x75d8b41850f336fe0475a11159ac07f7038486240ff2483e0af0823c349927aa1bfaec262b5cf8b98bfeb6de781341ee9ea695e49a893fd3b0e7b4af1d1a2d61a1fb5dabdd1c958a9466f15121a24ff6213dd5b687a13a4b068e5a6155e42c41063d7ceaa80fc537425c7ca8be150f887cabbf20f244200b4c643b36228502ed10bc44c1db444fba4c911752294ce40077d7bedcc3b4965d6d95438c949675728e2eaea03c0843b09ef365f8e131d223ff08377a1d68f0fbd33a0b4efcbf03f7a8848f2ef888ab9fb879dbf8a49c7e793c8fbbc631f60edabf6e9f4852fe0ef68c2660413e03b90f7f836c53f018149602edc23fe41597f8e04affe2db5fbf55b3f5aea17ede688fbd81b9f290b440935b67f472c109227a60abd783f4f5c67e4a1a4fafc0a1f64771be613807d888ad04d85b9fff81d3ee03397d7c15cfe9ffedf8d844bf5ae957dc50c0fdca559f70a89beec0f68134726ff9426a06ff13b617fe3)
set_option maxRecDepth 100000 in
def cr105 : List ℤ := (List.range 106).map (dec 27 0x3d40fa3bf6e6c3804d2bcf9b50cdfcd9c33fbbe967fb04a0f1865d214435b396368c7ce3b32f4851420143cbb82f89e7933ac100d97fa01f1cec314d328134537075c026127705b7b7b878451e2328b8699d4aa433fab783811d707047d70a085585436bcfc82d1116fca76e64b6008c05002385783fb14a6e6209124f44b2976839313f087f321dc91ed3a6ec41748a04cf717369416c77babcc856da086ee164b7d826ae4312eca47977796fd95e320a67c93e5f3e77138ed1009d03e08e2e4bedeedd88397fcfa4c5fdfc0adfbfa220e7f46f5afad8fa9f3f2c63f1adfe83ef54af410cae048df23d400b6835039f02152ba006d233fff7fb7ff6cd701cffba0097d03f95e8e7f37234fc68965f4503f412cb847ecae3305097420c3388bfd090c7efe7cafd0cd2df5bd903e4a1ff7d599f904d5389fef2673e938187cc054f0758009fa29823f7d5537e2a49afdfee09f7d1153f0409c811fe86ffa83ce07289bb6ebb91)
set_option maxRecDepth 100000 in
def cr106 : List ℤ := (List.range 107).map (dec 28 0xcf904357b8c7b97f000127c601577bcf29d820ba3d80371957f06f7e7cf28347ec1c1875a709085c7f2c7bc5a407fe0f357913ac17b1e9996f3db35706e73983a0d2275fd766819f426904adfc71a32af9e837a7789d9047cbf9408c4a563846016d87355dd83763458eef8058aad381836948d929eab4818890687c7af18dab68880c495290791b88516c648603b377347b066f77e0e69fc5c071b9d6d353af387188b326142e9d6c460fa4faaa574d4b53b762fd847eb0c01851a7ac72d26cb7a4135089adc2185080b57eb181b8e28a287fe22f67f551db7e3ba497dd14c07e82c387e407927f941847fa4f9d7c443b97c283607eba535866b6ec8244a9b811fb1d806444f80314e681fce0480e7e8d7ee07507ef101e7db4d8c7c51f66833c95c7ea609184e8608849d7957fab19c7ec3adc7e303237cbf89a7ba9cf97cccff683709f27ffc30f7ccd53b7c46a3d8307db87e5f67c7eed7357dec2707eac19e7d432657d5db62818ccd47fcf66482c0f546795919)
set_option maxRecDepth 100000 in
def cr107 : List ℤ := (List.range 108).map (dec 29 0xbe2af11c2aa463602f9d3afc74dbc7cbb6d643fd66ede8d7e18f7bb7d87e9e306b9d8c919cf5efaefabcf9f7dad200b85d9f6dd479d98fcb2ccb804e05ec0e318c60c6feeaffd567b8bde4e4463723b23718b8ef35c9c06b68c90c6fc6c521997ccb0e5151079efcfac15ae21e28cef471d4b62a81551eec580ec2a2164800f033040780efd0443fba6e4e887c129873e1933993c4b4a634d9937a34c09eeba58ea05ead508130d2a0afce200db45c8e53aac245db8f53dfe4e53f03f80267193649a449f51a644f6ca18782831de43901c65f6e4000f8c8d0b73a0041442778ce1e86c0f18f092188477893ea01d25f310404fb9d5c3786f7bcb74ac9721ac9b2106d74068aa66173c40e3d9e1d9816fb4e3d77c28b943a89cfa1e0d9d1b047aeeb817ab6dbe674901e5ee52ad31485382855d6bee55f2de65cacf0174f96801aa50c013ae9611526730b8e3267a3b8c6b9ed7e91b48369901d8869829892741a0b7ae11e8c230807a52853424dc103ec9e04d58f6f9b3de8807e47d4042154e11de2beffc574f)
set_option maxRecDepth 100000 in
def cr108 : List ℤ := (List.range 109).map (dec 28 0xbc90b508ee00f785d241a833e15382fc341861530b875e62d758da9f7a3a0bd80551587e9f61475080a0764fe427b5cfb9774b1927faa6687dfdeb382ebbd77709fe47970a06873b6cd6b0547a773753b8069658723b8ed75dd4a488f18a5848c6728bd4fdd83d8a90749020983972f88c3308482c13ad8a7fa3c890f0257988be481cc1ad9a646e699783a69fa4f8c93b0897973fef46a36422647aa6f6a5bb1e657dff1389f93575ee5d8540831449bae1536a915189b209b8b548e58a63bfb70ab0cd7f42b7a7b923c7826cb137e7927d7df147b87f90d27dc20e280326cd81552b08db010c7da434e7d3c2207e0c7ae789c7b675adcd0906532680500f98c0ba4a70fd237815c67b7f8fcfc7fe8db57eb57e780ff37a7ccd3537e03be3815ebb682579768b1e78c6e4495277728ae7f85e8283969aa818ace58242c348383b6484b145b85108516c4cd7c7e3611182ac29d81fba88833946684bcae68435ba685861ef8061b99806a6c7806af7d80625908091bfd8485aae8222d8e)
set_option maxRecDepth 100000 in
def cr109 : List ℤ := (List.range 110).map (dec 29 0x2d0a5f510d2a733809c429437625ce1593c77053bfcb82ecf2042fd578de7780a8f9b0dfe846bc5cc00485d1ea30f0edb3fefc7a31bc63c015ef9f83967906c63737ebfbe4bc4a6b05ed2f3e2cec43e675ccdccbd110efdf1faf9aee2ad837954094c52a43da0b30eeaf9bf6f27d1af4342e71c560d453af238d5978a1f794c252d18a3ddf1910d95b198932ed3cbaa7aca6014c813924895938e1eacb81cf5dbca1f46d5505a36bad415b081bc94e2b3c7ee44026a53a83eea9f24738e45f26afa483f08860ede401c7199ca97071019d2f78aaff1abfa7bdaa17d3d4afae97518a1c5b5c05e81a200c7425055e9637e7ad02be6a6515f11478cf8067ed77276ca3d50fa9e2ffbb9d0ce50d282ec913bc4689c1fd21da90769ba7824c26942773a7e1ca58d7085c467831e0214343d5f230296cf1e298a28ec0f7c31faf16621b000f1061a0686098c9446cdbe204f78f5034fc82830961742762281fe7206f071716382e0b5242424f3a14bb1070ab0ee68731b034068569a04f0273026aff7800b969c05e1fca12c614f123e596)
set_option maxRecDepth 100000 in
def cr110 : List ℤ := (List.range 111).map (dec 28 0xb3932868f3fdd77e33f7088a2dd28ef9b608960d9280e4e7a80accdd7cf64b184e35fe825b40f7429e76724cb137e1f0f6774147279ded6b60d83bc66784c582ef68984907388ccbd698de6bb16f49fa1743803977f2f5772eb3a2876c9ba84276d98bda68b82b7e268ed987880aee1987a54ee87794a788e207f86d436ba5029408d3a8dd7c020a3978f2dd94b59be99e850890bdf3e8e4020e90bd0b86b7d39667ebb386690d5b5b41cb53a5ebb38b47f254c6408744573d34fabb1b75830c08d26735887e7fe9ab1e798beacfd8e4988d7e28a048ffdde48a44d907292c218621f0e8463a1e84d7d9680bc9ab80f4fa3811dbe281330c383a61c5823658c8435ab488eef1491541fc83a197c80f8f1d84e92ca81fddfd816c0297f64e4681721ef80e39238453b1c88beeee83e37e184297a6861fb287f682be783e1f17fccfa37fb54cd82c419883b1d778010bfb832598d86a442b75e020078ff9be7e7e66d81e23c187b6f5f72d449c7fef8617f92c387f9a95580bb94b806642c84588d17af2bec)
set_option maxRecDepth 100000 in
def cr111 : List ℤ := (List.range 112).map (dec 27 0xe98d2a12327a362f0d78c442e2988fe15735229a2275c53c082a1d828452cf16db95e2f0473d1fe2a8ca2e9f0c49a79d8a795c30d59e796bf4a56adf8a8a5a694aef73b78b70030af234e2fcaa334bb85877408a6f18d9e9dc267843cd963894e00544324023e28adb7a35e07fb5515179186e20ead5c2a085c8ffb24d3a0d55e2f00de47010468b7aab0e5ffec235707846ea4198404d850978c45a8f054b3673005cf29aeb8661ccca54e5340c6ed34e534861eabcdc1e476c63cd3d8f01d9d1a9bc3671eff544cceca81cff3714320665f216ebc2919b5e4b46d0abac86108914c171e188064acf047e4f60a9b81c1f043883b8e3cfac6692297af93ec92378cb03f2fe1262a11781d3f51a1a80bbbdd0816e1208663a3fa41277f3d44afb3fe4df0ad2ec30467f82c1b7d1c20595e6c9a240690897f9f0b2fee3b19f6483fbe616f37e369af07f0ace046edbbf7ee587e77e76fc20e65ff742c401d7897fabe0cfdb9f7df62ff0bed2ab08192794fffad860faf0d34d41f7)
set_option maxRecDepth 100000 in
def cr112 : List ℤ := (List.range 113).map (dec 27 0x7e1079c6d52abcea208c24cc015c177e0a888d626f30ae5a01de9fc0b45df7ebf45f0752385ec589b3f6dbaf8221f10e3971a5e08c9b364367a3b18b351c86a0a25926d481887b829e8790aa85b1e6f4e4377762d83004dd035e60a2174a845818338fcc807146d9121e15ad4f1d9d084416031ba2ed654471140980db890471130b419e32f75c50e951b6a0724cd5d5b9648cda24802c8e826870105b99c57d5d662ca35de4f25b1cb44edc4ad60f733734c6067d082944c1460ee6e6c48ff51882d14f10e5c6a48627c4d321577585a40f15af16002493bfebaa1896835afa152e9fce1ea3f8e74f7da8b30f94952df05210be63d4a796501307a2d2e396d4c3b23dad8a67ddef2d68ba0af3284006e977f646c9013a535fb0d03bec4f387ddccb2f8aa455e89394c0ecc567f2d88f157269e1591f63eb9aa47cdfcbef6d5ce9efa126bd4598c7c113cb093826e01f2b4be74e8f7c7c146f64dde9f473923efdfb47c5e518fc02e95efb5a4be0a654823ddc6ff52e8a0e54fdadebda8)
set_option maxRecDepth 100000 in
def cr113 : List ℤ := (List.range 114).map (dec 27 0x3e903d0b4fb36e715ac4105ce22a61691ec563bfa8c48300e16e0f60c60c2c3c2223899073b160bf01ee06e0bd2169b7a7c958df6ce95b4a6972e0fc9ebbe61771cf193a1582904604cf482adf7f0ae84d5ef90793552f9d7e66e4b019c2de318ef7c72e7569133605195e57211971b44b57bf8734fdf2340a425edaf8c2eb5608c84ad3358e88dfaedcfd19f07b698f230d555cc248b995c7d9fb882701ed05c88cd83e7b3ad62fed4f98f62b3c6348a7052433e786509c83228df952e13e944c3c97c986c88150fa5b2a413e164c13cc074eb5b4fe55e4e00b2e2bfe754f896d80af92d9e5fce242bf8a1607dc619af95792df07655be71738795760d07764a23bf07f3a51b1c8a6aeb2f2ba25e0af39d4006fa67f648e7013af89fb0e7fbec501d7ddce26f8aa8fde8948fc0ecd877f2d8e5157234a159243beb9c877cdffd2f6d65edefa19dbd45ac97c1163109380fe01f2e13e74fb87c7c37cf64e46df474573efe0f67c5e8cafc03081efb6183e0a734823dd06ff52f420e55162dec563)
set_option maxRecDepth 100000 in
def cr114 : List ℤ := (List.range 115).map (dec 28 0xcdb32d28c4078e8717ca17da39a57f9c349795dca87cdcb49797f20977ceb867ad27fc7c21d9879bf7fb846bbf38106a5481e99dc8351fb69ef6b9089a44eb800c2167d9992778dcc8981b8845795d14376055a67df37c682fdd9e78f63e87fee5487b427777ecf4e06f35a1b77f22046e52d04771fdb37f7585e7a84fca8dffe7a7e9d5a773816647bbf3a477ed427779bcec8488c367497897739a49c815c6887c4033179d5cc578b8d4e8b10da28d1f664972d9a39c58c49b0f4f1d9efd5a68f566c787fefb889bd04e818ff2a66f5c997fa6df07f743e682d1db68056d338639835816ac707e5fc647fbe8307f8abfe7f47ef7806b06e7e674587eb25497e75c127ffc94372f1283788fb1d8266ad182c0d4481bbbd080521d78040f937d63a5d7e55dcf7c0ece07acaa437d432e37dec3097f0dc847eb409776aa1d67ed6f918388d4582a63b57e65aa87df6f4d7d042447e8e1007e131fa7eb75647f6091881467457bbb3d180201447ea31e67efcfba7f60e1a7eafbea8288e8880134217792721811b0a37fd68d681cc9c56e3bb71)
set_option maxRecDepth 100000 in
def cr115 : List ℤ := (List.range 116).map (dec 28 0xc9b51536b15d818a7538284f9b527d8ef287f89e73774205d7ac5a53776adb676520cb7b860ef7c930dc78dd64a84de9f28484a0f812e2e084ed5faa3d081c79b72d980758907ca346b79db82981c09b0799759377d5c7080dca20817e4347aafdf58071e8178eff4c7db5aa470328fa7689ded6fbdc597b053887e907ee832512c8c39d2f7c3c57e71a51867a70e63795e4237cc83c88549d25750d4f3737e2e180379137bc4a8078f668077b0e708b422878d274909523ae29b2329faf7897d9ff86268c99d9c8ca902c898b0dd8072ccb63a74de8143b747dd926981241db86a83d38543adf81636fe7e6fcd57fd183a7f7aa757f3dcf080761657e616b77e9308d7e510c17fc6daf7331f4978caf328270a2e82c5b4a81b2646805e36480486047d5a3477e50ba17bfd0347ab83c37d191427dd03b27f0c3b87eaf0e376c23037ecd295836a4e182a3b327e5fb037deeb5d7cf80d67e982e77e20a297ec2b4d7f2cba78156cd97b8fef7803de057eb3d157f03bad7f66ecf7eb796b82c0e638034b19772bc80811ad227fd6b5081ccb826e40268)
set_option maxRecDepth 100000 in
def cr116 : List ℤ := (List.range 117).map (dec 27 0x771e6a0666926cd88c165ec8297c1ddd9e7e8e302df0abc1892084b70171e685445ed486351e3d7ffbf7ba8e7fbd11afd8a94a4f610dc5eb594acae1e0ce0462e10a1d747e09598c2daab3a0efce27512d3a571376a08640e9f26c1e5e3df42650cc7aae2d0fac5f95cd22c347e4df37fcb7f0e186e41b088e2b1af19c712134a8618c49b72bc7c5629a39f923bcbcb1c79e8d279cd183016f916daba97dc1dbaac23a6f5786c5639cd19889a6d7ca6cfe9bde9f1ce497987e63045afc6cd375791055a524326623f371fc22336f56ad94707b0196222865c07bcec7b11e9b1315d1a26cb88be2de127180cc30c0de460377f23d65b087c3b6d311d230229b0cf48155ef6a01870ddc4fc58070ccc2765817c2067705034fe067690bf0b5437f64f26fef5901f6d8a1407a6dc805b8fd0098662054effb751eb77ee9a3f122350e1b38a6c0766ca7fae0a6ff0fa81f682e43e6b36b7e4d94f08857ee05795a3f2fa4a7ef5ddcfcc0c0a00142b402ed9c7fdaf00ff76bedf858fcbe0e7fa818e1c2fffe6720fb88834ff41d)
set_option maxRecDepth 100000 in
def cr117 : List ℤ := (List.range 118).map (dec 29 0x26fbdf0efdf4ac680436953fc7e251fec60aafe9b0b9810cd28bb559e598b29a5cfad021c5b7bf4c3604ffa1d6a7710f60ccd879899463bb6dfb5f9fea60fe7bf7279f83eb3f79350e203b4551a0851684af0f247317d6a1ab5076ea219557de1a393fffc795fd915e9146b7cb82470e1bcedc695cd203d4fe0fb2b7a8ff6eb790a121f13e89d01bf237863b9fd3d040fd5dc7ca7ae6022d17d689e23ac30fa1b703cff18fc69b783369d362c0589c58bf9cebebdbc7103ffcb72b91be762614349714eaa63f337d892c1275dde5d0f53383a8aebc584aed1a425c967d2eb5201a7b1f8bdbfab2721f257a9502632e67f84fb1417fe572129733cf39f44875ca77ac2bfc9e613eb06d0a308fb8bcad2c3f797501fb1097afada4e98138388c32223e596008aae7c5cd28962c113fdd24ca030496efa55f9c7f3a3573e88d069f96a9defbdd4037eb3033c0b697260a79f44dd0509170660babfa52331fce633306f199281801ba4119712dfc781e2fd9b1bb8546babb7cc764dfaba11b06d385f8276df94201b92a137cb4108ac95185ad6b540b5e72603f1d39016ec4d82369883f6c6e2e097f971037827a)
set_option maxRecDepth 100000 in
def cr118 : List ℤ := (List.range 119).map (dec 28 0xb952b218afd5d57aafbeb7b014e07d9b8d07ac634a7b6c90f7cbbf1366eab6069dcf026bd81ff648bcdd5b863226d8e3e588e8c9a907a43a7c54e2a85102f18024b957f416ad881a14b8a71c378ed670b83d41258f514347f45f047d530117a30cd37d8ad447f4a31d892947a7fc4b187fa763b6da70d287c181681a14e47739bd08b8c6db705b91a8073093800648b8031ef573d3e4f7759ed46e08ebd83ffdc789000d37b66ec47439e5870906f970d21db6ef87196be2c6ea0afb87a892fd6ae884a8abb5998e04a3b278c87d08608dfe8f9465f8fca7a167fa5797b93b487e413ed811648e85137268c9702c8b3f2428503b7b790fdf77b46ac482f92ed847e991864546e852d43b7dd2c697d75fff7dda8b386b8f5b80d19457439a40725f1fa7d769d684650cf818f2377ebadfc7fbe05c7f7e8937f1242d7ff4bda7fe210d81e031a83f5f486d4ae1e7de097e82c98888518acd8325ab38147c9281e07f37fd5c6a7fc8437812834c7e7fe5f81e04988286c1f80b263c81bf3748205d2681fb8fe82451387f1c7027fb257e7f9972983771508264f1880dd8217533513)
set_option maxRecDepth 100000 in
def cr119 : List ℤ := (List.range 120).map (dec 28 0xc6c6749800be8b7e4190d83e1ef580144d481f5ffc731224076a34dc7d21a8b8d75c3054ea8285df464a4a148ec8462c5784ccd7e833780784d4f896b2bb7498bf2e28dae5cf77b095575ae74c8c06be9981d5eb89e44739b07f347d1ddbc64ec9337b1cff47ac97507cf3adb9a0fa50789990e833493774f14e07cfd37e73af7b760bb3f58649f6886953658562e0d85378cf7f786546d750ce7433e2771b4ebe73f005a8c572fc7ec9f2c5fd0bff5dd25666ca1c5f664b2b6619cdbab31c38dbdb86f6d8f64d1e26f101d60ee7e8937820914aeaaa458a67994d0c93bb1d1474f8fd37e31e8b89cc04c8f1886898a7a1a9a218d98563c2d7f42de09d678648402f7380ef96a7e5f2067f2c4737f1e39f7ef4dd57f3b506807308d7f789b981d8b4f876a78f8ea2843969e22769248297b4e3cd82124b687fc14c8148048820c0a9810234482414aa856a525852bf687df6d05904a7a77dc9d5080527a97eb430f7e198327dc012b7d00f857f400a78b057ed8a4079f71971897e2b2657dc7c9b8070fa380df7f480488127e7edf67cb342b7cd611782331a0800fa2d85f668f61bb947)
set_option maxRecDepth 100000 in
def cr120 : List ℤ := (List.range 121).map (dec 27 0x7c160fe7483ac91f8f1921fb889401a41e864f89305f503db9d9fd3944b7b76f36629d08c1822c15acad63c9c20c76301757d5d40b68bea457981e293907dc359ca6abf3a2b2197de354518772be0ced934c417548cf396729bd535f63a16add593275acfb0fc4304608f99143ed85b8e3d79efb74f29d4d1e13a0b7826f6b1e4ef809b5fdc730c23f3d08006ec6f6233d5f460a1befdf826f85d98a74e10dcc26e23c9921f7076b3cf2c1e519a3122b4c34156d107eed370cc6677907d0b24b7bf5c9e7a9a9a6aac49743e1b2a187a0fe324b26f9b0299c419f37980a25f10d01bbe32b5d1c0ef4147f84ea70b98fda22859f40aa34b96a5464fbd8d55fe43fcbf1eba97b69bfd0047e6200bdd9c0c500d80132f2fb8c36a28d93e3bfc249875de9b098b73df56ebebeb23ad7f241270047df9f6c0043eedfa87e16fecf7cb66de51f32c1f36a7821406b1d817cde9809ebeee2977d3566ef7d0cc5f0704a3d681e47c540ad09103de023fe5be954237cb9df6f7034d1f5ca4a3f20f5b7cc52f4fc38451f07f3fbe22c388228ec4ff679420e7f772ec3111)
set_option maxRecDepth 100000 in
def cr121 : List ℤ := (List.range 122).map (dec 27 0x35b9f3b49493fb84fb2af1f5480209685fc8c17577b642bcfaa0e6dd75742bc28b528070482c952096110ef2486b3c763d9c4cd81bfd5d1242f3e66d747b2f3a90d7dc41ea164b3d655fb8b02cbf3d76ffe0b6b6140cde717f113c554a1b0e17b1b2be0c07482d2faaf072599f955b5bea3d1a7cf2260dddf161bd1c0bbad86d1742ae86e55df35ce775f32a8d8077c2f20f62e665da0dedb31bdc871dca36db41091a01a67bb52835773c5d0e4e61fdb60825b4caa426da3062d4be43a6b89b05079cccbf6a9edac1bd9a5d6cdcc28200b9b8c75949b4aa52e311fbee404d788447502c0f02177cb1c17014d8a2751d27a65362e1ad93e186c7a47367908d97120871d64124a327f44994fa8b639f331d0be4cced7e20f450c6ddaa0c78f340345979a7f97b0b182ca11f72340bfeb281640930b807760b738b3f9e36b7f2614709c0f7e168b3dc17b9e97f5553913e450e17d549bf9ba607e5034cfb0df75f31dc9bdda5c87d313a1088ca3e033faf3f0037b7d86132f95add9fa36e73f949227e193c4fce8c69f31a51be7348f81e4028ffaa1f20f0accb18a194)
set_option maxRecDepth 100000 in
def cr122 : List ℤ := (List.range 123).map (dec 27 0x1e59e869ffb02cc90d53c7764fbecf710d9d3cafcb9e9a9774a2964ec5e1c636c14cc449be775a66f8eaf886226ad444a78b527488fe717cd06601537d416eea781251f6eeac389e27bc8be0fbe67db7ba8d79d1d9eecd03398be997a968271dbfd22646eca472dfa290aacc6fff8651d1b453c600c7182f12a10df398e146eb6bf582b987305f34b7d90a54fa104403af48fdc42125ae0c637c5c342709b08a804413bf4ee58fa1c35c6123ba9e771165c23b2c26b56c9c566b908e8cd26f75e54cb61aa39139746a6c34786cd09811be0c488987867ca8efaa3f8a434a1446dc37f9c9a218cfa87bd1dac5549099975ce00faae8474e169286c0c679e974d0f6f6e2dedf86c45bf1407c7c5f2b0f945d1df048ad3e7594d7895a2305841724987243c4313a79c13dd06088960a0be2401c6e47f766bb014064dfbf1723ec5f847de7446f99bd75ebe94bc130cae8089071113c84e1629d13ef4dbd7d40520f7f0cf5f08aa3bd6c8277c5c8db090b5ea024964be995e47cc1c3ef71a801f5f60a3f256897cd24e4fc3f289f09901be25de682264beff69afa0e84b9aede7e7)
set_option maxRecDepth 100000 in
def cr123 : List ℤ := (List.range 124).map (dec 27 0xe90e984e338cea2568f13a50c76831a07f21ceadd940d643e80c7172116eeee10d619d5f4639c6d12898312cf43003a6f65fabf20a7798e08b336d7ee22b2f8ac44a8b28ba36a106af2fe035648404c5e6727dcf90431cd63639d439d0d9f8768a670ad4a31d5c615c5ab5078ec9d9f151ab1a0fa80344d02a5933e182e78b44a42861448bb40aa08d44f3ece29235d2acbd376168aa1162fe0e7322c5f2fc55be688abb8932d8006e0d7a95c8cb4d6a1bb00d780d42a908911d67d8d199bd2ab3cd5b616846e2a9b417e4bc9266a2c143de96dedb222fff81c626ef6f895e1b8ca0496fcde7e36d650a7ce558b83d5b6bf02b89e7002959e59dd52a4f438f620842fb5cef90129e29c31bbf00627ab6c94fc74311f7a75cbf9588277f0f3b05a62ba98331249cb053356e15906281ee0c96afc031abc7fd7e2f0370fae0009afbef915e7e30ee0f9a3f9debd5f7413c55f7f6453b151d1c61478c13f25ca17d9019ef8dab95f14bdf3d8cb6b7c9ae3508e63ba0291c0beb78a87cfb582f7c3a25f735653f4609a7d32416fc70ff5f155353e3c9618212d9cff7c9fe0eac08afa7171)
set_option maxRecDepth 100000 in
def cr124 : List ℤ := (List.range 125).map (dec 27 0x709e2137393fe6f77e74a18948dc05cbed7b1d024eaf71317e00bac481dd48e3c70b1df36fe0059f1c0f6b4f6eb997b1ef525642985943f3c8a906c67312ebcea21d327bca0c7a73575f8ff5efa1f807f2c142ae67af627f506e85dc9301d3bdfdca80a6886ff05fd5da3a294bdcd667958610fffb9261373e335e68aa6de8a9316b2bc249e19a491802ba0107c1531db6d9f45a34537d178016df51674dddff3554b504a4e8171f5f0b6715276b85f3aef9eca96eed77902d768c4736d7e0d639711d33366ce5193f424af084c24bd005a7cc1a31e15c78379ed718deccb2d16d0522e528bc254a3b8044e8b0f38779cda0383591e0997e0ac113556dd5fa634c3d815377fca94efe446de13d703a6fbc974a304b10852a626cac4c68a6c38b12948e77ae32760328cae38253c38fb4f323aaa0af3eabbf88fb7e0f31cfb8268de7ed87bef4a697e12ba4f4d71a1da396f4375462873ca592d18681983288bebe9577ce7d78f6ed651efb470bd48cfb7c1778509349ae01f9b13e77ea17c81da0f65eee9f4939e3f0142f7c67f62fc080e9efc8933e0cad2823be7eff548760e58f92e00050)
set_option maxRecDepth 100000 in
def cr125 : List ℤ := (List.range 126).map (dec 27 0x359b99abe149bb7600382f497766459775c8e36d2a77d792e0af1b5e29bebc18382779b3310f63171ddc176bbaa5cf386547231df4985e6e56d3e63691856c698fe1ff9df509894118f6b858f1c10717aca265da0c1470038d2cbdaf72fd85db88474306534785d8b9224f685eea0a7b6e791187df2ef06218aa20ce604221a0a7fbf5e509138dde9b0c5c2a13355947b6eb2e699609577a3c555d26af57e8f3ae4ee09cc17c2ff95f720b07eed96f21d73eb43bff11571f5998c85b8ad7f212e2eb0a1a672b8c4c55061e7ad327d2f472ed8064c13708f71fd54ad3440c9e7cbf5050a352622203fd3eda1c1784a93b006974213f62f42094f686b5d132389efe19fb7d40df28b9ee42c50d443520bac39c1911ec8011b1efa6aa11f2dc8e3e457c37b67d8b08a862a1d746a436f6828c01af509299960fa2f5c0b4cfd80bfd3f07d8b260a4713bf5bf3c7ed0804fba3a25f2964841b06d17f608d913538a218a63fbfeee2f7ed870efc9d669f4657fbe10fab7d9b3fd085bb3a0399543f339e47de83c0fa7b135fc57333fcc21d7ebcac6fd3d939f45a543e99fa881c2d78ffcad560f4de5b2dfc98)
set_option maxRecDepth 100000 in
def cr126 : List ℤ := (List.range 127).map (dec 27 0x1c2199a611f946bd9b910744be230050af6358c67c446a0595cf961730de21e9ec6a358d38e70abdb0edca809bcb4fd3a23f2888d0a44e2900f9e55b63be8962f84164ccd91ce5ddcd56c3b489207348bcb04d1c4e0d9a053de688281f161cfad000de2d91ccb19712859751f2c10751f5ad95bf1afb681f19430db0f1a281721401face79dcf0f1660bfdbd8ba7c0ae45a59cb22cbe84299ed5a813b58c188263838f27d86a2d7f65bd56584700955aed02e2a1a60fb3bae9cb6aba814bb542fd955b43ad534a2675f0ecc5af3aa803069d38b4b4ea61056f36ee2df2d17440f38687c949190474daa2291a5bf5eadc7921739018e1d619a97ec28850b850d773228f1de185d8dc0f167d9ec7a5b12aa58a0c5f2941bf3e07fa885cfa3bbe5f25f2abe03f3e7bc8ead09985d61016f747edc568c2e24f0958b460fe06bc0bdc1c80d170f082e74e0b0b163f5f0ea7ed6c60fbcc2e5f31fb1c1ba1717f669b3133609a18d1fdbffe7827ef1576fce6681f4a2fc3e1b39e7daeb8d0841a4603d1143f3d2417dfa66efab09a9fcbc08bfd66d17edaf28fd4d485f495ba3ea127a81bcb14ffd0cc20f5a53b31f23b)
set_option maxRecDepth 100000 in
def cr127 : List ℤ := (List.range 128).map (dec 28 0xc14f1207dc069d92413d177d00bb6f672736898fb489d7d57978088a689413983a700f91f076a7f87cc97ea6a857cee85d80f05e07c55ef57d350067e03b4372c264c7b4677b7f104696ffcffb72010a87d232fb80081a07d9e47c7e1a9477d8081e781d0188b0cf798602d48874aaed7b2aaa784bf9736ef82426fcef2774c9ffc83fbcf6847f83282dd5e58b98c857461a51645003969cf4aa639e52d5f4eba575fb5836ae3e3f6f827436d3d8d866a0ccd8039a217325ebb716f0f872f488777240de784b023567da6c61f669e5849b7d6b2e44e6763b3c9968f6da2560c5bfb0dbc7d51dd17ada2b376f2a92837465e8966aac8da2e5a8da2e6f7ea688f78f16ce9d680386dd2c347589af572a9dbf85b2a9482575459c440cb8e162e588a772f8837d1787ba2207de5cb27d862837d1a70b7c04aea825e44c838bb5784f73098bf944081e384e846127e837889c837c66f8b4e3ce8a9129d7fcb6f57fbd54e7eff9fb7e76cc4816ba3d7e279fe86f71da85730d782b6e568173bc682209127621eb872cf0767fffd6f836fa7481a030380b9347801f3f5807de918228122821a4b3826cd2e7f93d747ee58087ef335981034d680432fa8434462752cc4d)
set_option maxRecDepth 100000 in
def cr128 : List ℤ := (List.range 129).map (dec 28 0xcd5fee6a6d151687c864466b2dc9641ebdc6f7274b528e3736c3f3b16cee55f64bec5a9cc0603aa10cd379758b884aa1df83a819f8a4378285a4d1581910457984f156a1467d723049165e6b8c665e9157359a357ed7c9482595df74bd9767967b2a7d119b370e56d2895fa5287e9e48a30aab684fe55b7fd5a195dc08f165fa7b8688a7057b4b1477e26bce802827c83abe1970f4198519708854ab55859622c94affc667b3f370753ef5d7c89b305517b475a7b5c074ace9c6ffc1b55f3b55777925e96534f285964aad1d5bf5347539d332b8820545208e4c6cb01b92b4a5c8577a99bfbe75762985f96e8e4c8f75b859cd88849310ff39b127c188efad57ce4d3876c8b07b267499710a83a736cc74770c4047bca4a665b036eb898f19a08a10393b630b8ffb6759631596803134080330cc7f0ba857db235487ce2fc9328807985d466b5a985a6647e7c580ad758af065389975519b95b619bd5c1c843704d8322e13848b0a588488238fdccc6800bfd28cf987490f0f8b8e23b56896e68b8dd36e4814eff281bed02846265c85933c884827fa85b0252844b02386ed69b89ed74f88ca3d88b97a0080e7986811927f8117f2180a8664813185e8919a0e868c8cd)
set_option maxRecDepth 100000 in
def cr129 : List ℤ := (List.range 130).map (dec 28 0xe26e0f47e44c3d72a8b108b2b3817cce6f278b1d2c8c00aed8cd993a8d016fb80c2cd69d2f5a4824d8877e9c1548ad49a57b2816d77d46f47cf1a197b91cda8d73685858e95e6b876d378241f07f10f827b995cc76a48c07e7fc887fd93b27d3b68686f62d78447b9984edb8a82f077185e4c4b68735f47c60b768c583007b2371270c0265744b3048627362816d7b37206b6e736b9bb767da007a100d7702d5755efc6e4771bbf967b7d1d8737ef95ceb42082e7dde7b59a7e7c7ec58719e5c67124e8378ec80c7db1057706e68b776039a727960f615dc746c211b868ad0fe9cb2525a3138bf71c10b87cd0413b20999a7e4cf8a835ce3d91362d18f9dbf287bd4f3876401e8cbd0b18fd392c6531f916956d3c9055f1e8638a4e847e4409eb239b90155e389463e58aca05b85df08d7f55f3d7f345ea7f1a1667e45399808c9f38c1b42a8f3c9848876f4d89acad28600b1c83cd2e5827f31587848a187eb5c87ca1b8c7dc3190803eda2808c2ea85515e4825f09985ad1e685da520843edfc823c32d8346d07805ae098079aa981970647ca331a81e8815818c34480e498481a17718347b0183078a483c4ff87fe59d47f7e0cf7f86ae180c81cd8064d388473b6d7a38319)
set_option maxRecDepth 100000 in
def cr130 : List ℤ := (List.range 131).map (dec 28 0xb142ab788bd78c8699f2d88b0b24823016e8626bd37f393c9813153f81fa79e88866d7887349e8d8eefd8490b5780611c38a3587078d73f77bbb56179afe1d7e9b993845f3e78000d80743b1cc79140097cdb8dc81b82bb7fc4b227c14f2a7aabe687bcade883a379b81d529a82f4fc98ca3c7a7e728958e7cbc386c96d19733c8579d0bbb6be1caa7cf210582509c686524867c392127c26b227286409616397c77f6dc567c15f663160147c662b672ed85975ddb91656baf46d4f39e728619474d8c9e6ea142d7263613732b43073844255020a6959decdf3805d7f58c73dc51c47cb7dfd9127e52e6ea08759d8d7df40e5ab99c855202791af1ab8d9b536a0045ed7bfc9db701915c83acf36893922e7f9b9d580dc301a1d066c8ce682288bbe61ba32a2a9a76804915a78c9126e8c929409e80c9fc380ec3838125bc27d460ba859058ca27157e90909208e26f4177b87ea8bf8e188baae2d8708ac2949899b8f741a384f6ab0836c66f812db18823f1b38cd6b237fbde0b8d1d9688d25af68a57c418695d8a89a75db809441f80c63f18377413851121e7da565b83f1cd982a0ee7847be4b879ea0286e7c9e88d219d802f7ab7fbd5b67fc7cbd813855680eb2c888d0e597af5063)
set_option maxRecDepth 100000 in
def crows : List (List ℤ) := [cr0, cr1, cr2, cr3, cr4, cr5, cr6, cr7, cr8, cr9, cr10, cr11, cr12, cr13, cr14, cr15, cr16, cr17, cr18, cr19, cr20, cr21, cr22, cr23, cr24, cr25, cr26, cr27, cr28, cr29, cr30, cr31, cr32, cr33, cr34, cr35, cr36, cr37, cr38, cr39, cr40, cr41, cr42, cr43, cr44, cr45, cr46, cr47, cr48, cr49, cr50, cr51, cr52, cr53, cr54, cr55, cr56, cr57, cr58, cr59, cr60, cr61, cr62, cr63, cr64, cr65, cr66, cr67, cr68, cr69, cr70, cr71, cr72, cr73, cr74, cr75, cr76, cr77, cr78, cr79, cr80, cr81, cr82, cr83, cr84, cr85, cr86, cr87, cr88, cr89, cr90, cr91, cr92, cr93, cr94, cr95, cr96, cr97, cr98, cr99, cr100, cr101, cr102, cr103, cr104, cr105, cr106, cr107, cr108, cr109, cr110, cr111, cr112, cr113, cr114, cr115, cr116, cr117, cr118, cr119, cr120, cr121, cr122, cr123, cr124, cr125, cr126, cr127, cr128, cr129, cr130]
set_option maxRecDepth 100000 in
def czr : List ℤ := [491342400, 295776000, 1110307200, 294710400, 631463801620800, 474054970502400, 1319414195745600, 3958241970430800, 4692213597748800, 699092400, 1257736800, 3996804319720800, 299275200, 3439348800, 469423200, 1319413865240400, 480541200, 556868400, 1319413929261600, 528681600, 1510128000, 734188800, 314193600, 1727985600, 302190300, 334602900, 353483400, 362527200, 478248600, 309636000, 307804500, 309480000, 450820800, 294710400, 589665600, 294710400, 453110400, 328843200, 453825600, 307489200, 313009200, 327957600, 311475600, 327426000, 304142400, 299270400, 477720000, 307531200, 442459200, 442053600, 736737600, 442059600, 589407600, 294840000, 443572800, 297321600, 597696000, 294700800, 445027200, 300936000, 457531200, 298017600, 457641600, 312194400, 317965200, 318297600, 312447600, 457005600, 298075200, 457804800, 300907200, 444787200, 294700800, 596577600, 297288000, 443625600, 294864000, 589398000, 442059600, 736737600, 442053600, 442459200, 307411200, 477854400, 299299200, 304192800, 327640800, 311457600, 328026000, 313039200, 307556400, 453883200, 328881600, 453398400, 294710400, 589636800, 294710400, 450561600, 309624000, 307488000, 308901600, 478021500, 362409600, 353390400, 336965100, 302446800, 1739630400, 314136000, 735187200, 1508054400, 528541200, 1319413929184800, 557151600, 479718000, 1319413863511200, 469248000, 3352051200, 299332800, 3985083764512800, 1255995600, 698683200, 4704608605071600, 3958241971640400, 1319414195475600, 473458769054400, 633490134721200, 294710400, 1112116800, 295800000, 490732800]

set_option maxRecDepth 100000 in
def tabs : Tabs where
  n := 130
  loN := 4
  hiN := 6
  Zn := 360364800
  ppn := 16
  rrn := 5
  ssn := 27579245561
  Wg := 13
  vlo := 0x2871430a105062829410a0650228094009fe4fc27d13d89ea4f427993c89e24f027713a89d04e427153889c34e0a6fd37a9bc4dc26c13589a44d0266132898c4c5262130c9844c126012f89744b825a12c895c4ac25412989444a024e126892c494248123891648a244922090e48424111f88f847823b11c88e046c23511988c846022f11688b045422911448a044f2271134898448223110888043c21d10d8868433a1950c6861430217d0b8854428212108884242020f907883a41c20c1058826412208904081e40e20690308144062021000
  vhi := 0x2891438a185082831414a085032811404a004ff27e13e89ec4f527a13cc9e44f127813b89d44e8272138a9c44e1a70537e9bd4de26e13609ac4d226813309944c626293109864c2260930097c4ba25c12d09644ae25612a094c4a2250127093449624a124091c48b245122491048724212088fc47c23c11d88e447023611a88cc46423011788b445822a11488a2450227913889a44c224111888444021e10e886c434219d0ca863430a1810be85c42a2141090844421210107c83c41d20e106082c413209104482040f207103481840a2031010
  vlen := 0x202100880840220090048024012009004802403201101080240120090048024012011010804404200d002801401200900480140220210088084022021008808401200900480240120090088084022021008808402202100880840220210088084022021008806401200900480240320110108044042011010804404201101080440420110108044042011004802401200900480240420110108044042011010804400a009004802400a005006808402202100880240120090048024012021008806401200900480240120090048044042011010
  vsg := 0x1ffefff7ffbffdffefff800c006002fff7ffbffdffefff7ffbffdfff001800c006003001800c006003001800c005ffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff800c006003001800c006003001800c006003001800c006003001800c006003001800c006002fff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffdffefff7ffbffe003001800c006003001800c006003001800c0060030017ffbffdffefff7ffbffdffefff7ffbffdfff001800c006003001800c006002fff7ffbffe003001800c006003001
  Wa := 61
  vAl := 0x241a0000000000010bb800000000000896000000000000412c000000000002025800000000001000000000000000800000000000000404b00000000000200000000000000100000000000000080960000000000041c200000000000217700000000000115180000000000081c200000000000407080000000000200000000000000100000000000000080e10000000000040e10000000000021518000000000011e780000000000088ca00000000000441a00000000000207080000000000100e100000000000804b000000000004000000000000002000000000000001012c0000000000080960000000000041770000000000022a300000000000113ec00000000000989c0000000000047e90000000000027e9000000000001189c000000000008a8c0000000000040e100000000000203840000000000100000000000000080000000000000040708000000000020708000000000010a8c0000000000091940000000000047e90000000000029ab00000000000134bc00000000000bbc4000000000004e10000000000002bb80000000000012a3000000000000a0d000000000000480e8000000000029150000000000012b5c00000000000a6ac0000000000047e90000000000025b6800000000001119400000000000854600000000000407080000000000200000000000000100000000000000080e10000000000042a30000000000022328000000000012db4000000000008fd200000000000535600000000000256b80000000000148a800000000000901d0000000000050680000000000025460000000000015dc0000000000009c20000000000005de20000000000026978000000000014d58000000000008fd20000000000048ca00000000000215180000000000103840000000000080e100000000000400000000000000200000000000000101c20000000000081c20000000000045460000000000023138000000000013f48000000000008fd2000000000004c4e00000000000227d80000000000115180000000000082ee00000000000404b000000000002025800000000001000000000000000800000000000000402580000000000201c20000000000103840000000000088340000000000044650000000000023cf0000000000010a8c0000000000081c200000000000407080000000000200000000000000100000000000000080e10000000000040e10000000000022a30000000000010bb800000000000838400000000000404b0000000000020000000000000010000000000000008096000000000004000000000000002000000000000001012c0000000000082580000000000044b000000000000217700000000000120d000000000000
  vBt := 0x212c0000000000010258000000000008190000000000004096000000000002012c00000000001009600000000000804b000000000004012c00000000002012c00000000001009600000000000804b00000000000415180000000000204b00000000000104b000000000000807080000000000403840000000000201c20000000000100e100000000000807080000000000403840000000000204b00000000000104b000000000000812c00000000000425800000000000202a3000000000010025800000000008012c00000000004025800000000002012c000000000010096000000000008012c0000000000409600000000000212c000000000001025800000000000825800000000000404b000000000002070800000000001038400000000000870800000000000403840000000000201c20000000000100e100000000000807080000000000403840000000000201c20000000000103840000000000087080000000000040e10000000000021c200000000000103840000000000081c200000000000409600000000000212c00000000000102580000000000084b000000000000404b000000000002096000000000001012c0000000000081c20000000000040e100000000000207080000000000103840000000000083f480000000000403840000000000201c20000000000100e10000000000080708000000000041fa40000000000207080000000000103840000000000081c20000000000040e100000000000202580000000000104b000000000000809600000000000425800000000000204b000000000001096000000000000812c0000000000040e10000000000020708000000000010e100000000000081c200000000000438400000000000207080000000000100e100000000000807080000000000403840000000000201c20000000000100e1000000000008070800000000004384000000000002070800000000001038400000000000809600000000000412c00000000000204b000000000001096000000000000812c000000000004009600000000002012c00000000001009600000000000804b000000000004009600000000002004b0000000000101518000000000084b0000000000004096000000000002096000000000001025800000000000807080000000000403840000000000201c20000000000100e100000000000807080000000000403840000000000209600000000000102580000000000082a3000000000004025800000000002012c000000000010096000000000008025800000000004025800000000002012c00000000001009600000000000812c0000000000040c800000000000204b000000000001096000000000000
  Wf := 34
  vYv := 0x80000003600000061800000006000000038000000020000000080000000200000000800000002000000008000000020000000180000003e000000018000000020000000080000000200000000800000002000000008000000020000000380000001e0000000180000000200000000800000002000000008000000020000000080000000200000000800000016000008e9800000bda000aef4780000001a00000002800000002000000008000000020000000080000000200000000800000002000000008000000060000000480000026200085fe2800c266320012049b800047b4600000b7d8000003fa0000006780000010e0006d59680000003a0000000480000000600000000800000002000000008000000020000000080000000200000000800000002000000018000000120000000e8001c376a0000004480000019e0000010480000367600009d3d80042501e0027775e8001ed1ca000000a1800000012000000018000000020000000080000000200000000800000002000000008000000020000000080000000a000000068002a74320000031d80000218600000005800000002000000008000000020000000080000000200000000800000002000000008000000060000000780000000e000000008000000020000000080000000200000000800000002000000008000000060000000f8000000060000000080000000200000000800000002000000008000000020000000080000000e000000018000001920000000c
  vOv := 0x80000000200000000800000002000000008000000020000000180000000e0000000380000000e00000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000380000000e00000003800000006000000008000000020000000080000000200000000
  vA1 := 0x8000000020000000080000000200000000800000002000000398000000720000001c8000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000720000001c8000000ea000000008000000020000000080000000200000000
  vA2 := 0x8000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000002180000000200000000800000002000000008000000020000000080000000200000000800000092000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000f6000000008000000020000000080000000200000000800000002000000008000000020000003c800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000248000000020000000080000000200000000800000002000000008000000020000000080000008600000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000
  vA3 := 0x8000077ce00aa2eb18000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000972000000008000000020000000080000000200000000800000002000000008000000020000038c80000188a0000002a800000002000000008000000020000000080000000200000000800000002000000008000000020febfeb6985d2c17a368fae3892c2366fe0000008480000000200000000800000002000000008000000020000000080000000200000000800000002003fe3038cd739d025f644969b6675ce0673a30f3cadda6243a439686939d82170da3672f8f2a86769b9a54ad1969a89c9823221ddb5f280000000200000000800000002000000008000000020000000080000000200000000800000002000000008877297caa239278c94a3ed49ea3ef83938d9d8813a7643ebb790cb678daac9990e09c8edc802d6da500997ca53f0637fdd9a5801b5146e000000008000000020000000080000000200000000800000002000000008000000020000000080000021e4b74eb708d6f4594a66a9bdd283adc276e00000000800000002000000008000000020000000080000000200000000800000002000000008000000aa000005eb800000dde000000008000000020000000080000000200000000800000002000000008000000020000025680000000200000000800000002000000008000000020000000080000000200000000800000002000000008027f8c2a00002cd7
  vA4 := 0x80000000200000000800000002000000008000000020000000080000074a000002908000019ee00000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000000080000000200000000800000002000000008000000020000069f800000b22000001d9800000002000000008000000020000000080000000200000000
  YYT := YYT
  OOT := OOT
  YOT := YOT
  Wt := 43
  thT := thT
  Wn := 61
  NT := NT
  crows := crows
  czr := czr

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem grid_ok : (List.range 130).all (fun i => gridChk tabs G24 i) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem vec_ok : (List.range 130).all (fun i => vecChk tabs i) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem scal_ok : scalChk tabs = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem lin_ok : (List.range 130).all (fun i => linChk tabs G24 Tri.zero i) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem const_ok : constChk tabs G24 Tri.zero = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem len_ok : lenChk tabs = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair_0 : (List.range' 0 30).all (fun i => (List.range 130).all (fun j => pairChk tabs G24 Tri.zero i j) && czRowChk tabs G24 i) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair_1 : (List.range' 30 30).all (fun i => (List.range 130).all (fun j => pairChk tabs G24 Tri.zero i j) && czRowChk tabs G24 i) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair_2 : (List.range' 60 30).all (fun i => (List.range 130).all (fun j => pairChk tabs G24 Tri.zero i j) && czRowChk tabs G24 i) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair_3 : (List.range' 90 30).all (fun i => (List.range 130).all (fun j => pairChk tabs G24 Tri.zero i j) && czRowChk tabs G24 i) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair_4 : (List.range' 120 10).all (fun i => (List.range 130).all (fun j => pairChk tabs G24 Tri.zero i j) && czRowChk tabs G24 i) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_0 : (List.range' 0 33).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_1 : (List.range' 33 15).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_2 : (List.range' 48 13).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_3 : (List.range' 61 11).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_4 : (List.range' 72 10).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_5 : (List.range' 82 9).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_6 : (List.range' 91 9).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_7 : (List.range' 100 9).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_8 : (List.range' 109 9).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_9 : (List.range' 118 9).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex.R2

open Erdos1186Ex

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dom_10 : (List.range' 127 4).all (fun a => domRow tabs a) = true := by
  decide +kernel

end Erdos1186Ex.R2

namespace Erdos1186Ex

open Erdos1186Ex.R2

theorem region2_pair_all : ∀ i < 130, ∀ j < 130, pairChk R2.tabs G24 Tri.zero i j = true := by
  intro i hi j hj
  by_cases h0 : i < 30
  · exact (all_range_of2c R2.pair_0 i (by omega) (by omega)).1 j hj
  by_cases h1 : i < 60
  · exact (all_range_of2c R2.pair_1 i (by omega) (by omega)).1 j hj
  by_cases h2 : i < 90
  · exact (all_range_of2c R2.pair_2 i (by omega) (by omega)).1 j hj
  by_cases h3 : i < 120
  · exact (all_range_of2c R2.pair_3 i (by omega) (by omega)).1 j hj
  by_cases h4 : i < 130
  · exact (all_range_of2c R2.pair_4 i (by omega) (by omega)).1 j hj
  omega

theorem region2_cz_all : ∀ i < 130, czRowChk R2.tabs G24 i = true := by
  intro i hi
  by_cases h0 : i < 30
  · exact (all_range_of2c R2.pair_0 i (by omega) (by omega)).2
  by_cases h1 : i < 60
  · exact (all_range_of2c R2.pair_1 i (by omega) (by omega)).2
  by_cases h2 : i < 90
  · exact (all_range_of2c R2.pair_2 i (by omega) (by omega)).2
  by_cases h3 : i < 120
  · exact (all_range_of2c R2.pair_3 i (by omega) (by omega)).2
  by_cases h4 : i < 130
  · exact (all_range_of2c R2.pair_4 i (by omega) (by omega)).2
  omega

theorem region2_dom_all : ∀ a < 131, domRow R2.tabs a = true := by
  intro a ha
  by_cases h0 : a < 33
  · exact all_range_of R2.dom_0 a (by omega) (by omega)
  by_cases h1 : a < 48
  · exact all_range_of R2.dom_1 a (by omega) (by omega)
  by_cases h2 : a < 61
  · exact all_range_of R2.dom_2 a (by omega) (by omega)
  by_cases h3 : a < 72
  · exact all_range_of R2.dom_3 a (by omega) (by omega)
  by_cases h4 : a < 82
  · exact all_range_of R2.dom_4 a (by omega) (by omega)
  by_cases h5 : a < 91
  · exact all_range_of R2.dom_5 a (by omega) (by omega)
  by_cases h6 : a < 100
  · exact all_range_of R2.dom_6 a (by omega) (by omega)
  by_cases h7 : a < 109
  · exact all_range_of R2.dom_7 a (by omega) (by omega)
  by_cases h8 : a < 118
  · exact all_range_of R2.dom_8 a (by omega) (by omega)
  by_cases h9 : a < 127
  · exact all_range_of R2.dom_9 a (by omega) (by omega)
  by_cases h10 : a < 131
  · exact all_range_of R2.dom_10 a (by omega) (by omega)
  omega

theorem region2 : RegionLB G24 (1 / 5) (3 / 10) := by
  have h := region_of_tabs R2.tabs G24 Tri.zero 130 (by decide +kernel) (by decide +kernel)
    (fun i hi => all_range0_of R2.grid_ok i hi) (fun i hi => all_range0_of R2.vec_ok i hi) R2.scal_ok
    region2_pair_all (fun i hi => all_range0_of R2.lin_ok i hi) region2_cz_all R2.const_ok R2.len_ok region2_dom_all
    (Tri.zero_ok _)
  have e1 : ((R2.tabs.loN : ℤ) : ℚ) / 20 = ((1 / 5) : ℚ) := by
    have e : R2.tabs.loN = 4 := rfl
    rw [e]; norm_num
  have e2 : ((R2.tabs.hiN : ℤ) : ℚ) / 20 = ((3 / 10) : ℚ) := by
    have e : R2.tabs.hiN = 6 := rfl
    rw [e]; norm_num
  rw [e1, e2] at h
  exact h

end Erdos1186Ex

namespace OMA.Erdos1186G24NearCut
open Finset OMA.Erdos1186G24Cut OMA.Erdos1186Region2 OMA.Erdos1186G24Energy Erdos1186Ex

private theorem model_mass (y : ℕ → ℝ) : G24.mval y = g24Mass y := by
  simp only [Grid.mval, Grid.wt, Grid.len, G24, g24Mass, g24Length, cellCount,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]

private theorem model_objective (y : ℕ → ℝ) : G24.Lval y = g24Objective y := by
  unfold Grid.Lval g24Objective
  congr 1
  · apply sum_congr rfl
    intro i hi
    simp [G24, cellCount, g24RealAlpha, g24RealBeta]
  · apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    unfold Grid.pterm pairObjective
    simp only [G24, Grid.wt, Grid.len, g24Length, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    cases ha : g24Sign i <;> cases hb : g24Sign j <;> simp [ha,hb] <;> ring_nf

theorem middleCut : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1.H2 := by
  refine ⟨110680, by norm_num, ?_⟩
  intro w hw d
  dsimp only
  intro hlo hhi
  let n := 1096*w
  let t := ((Icc 1 n).filter (fun x => d x = true)).card
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 1096) (show 0 < w from hw)
  have hloReal : (n : ℝ) ≤ 5 * (t : ℝ) := by exact_mod_cast hlo
  have hhiReal : 10 * (t : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hhi
  have hMass := density_mass w hw d
  have hMassLower : (1/5 : ℝ) ≤ g24Mass (density w d) := by
    rw [hMass]
    exact (le_div_iff₀ hn).2 (by linarith only [hloReal])
  have hMassUpper : g24Mass (density w d) ≤ (3/10 : ℝ) := by
    rw [hMass]
    exact (div_le_iff₀ hn).2 (by linarith only [hhiReal])
  have hObj : 0 ≤ g24Objective (density w d) := by
    rw [← model_objective]
    apply region2 (density w d) (fun _ hi => density_bounds w d hw hi)
    · simpa [model_mass] using hMassLower
    · simpa [model_mass] using hMassUpper
  have hTerm : 0 ≤ 2 * (n : ℝ)^2 * g24Objective (density w d) := by positivity
  change (signedCutWeight w d : ℝ) ≤ 110680 * (n : ℝ)
  exact (le_add_of_nonneg_right hTerm).trans (transfer w hw d)

end OMA.Erdos1186G24NearCut

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1_H1_R1.H2 :=
  OMA.Erdos1186G24NearCut.middleCut
