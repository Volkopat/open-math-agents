import OMAReductions.R_Erdos1140_erdos_1140_R2
import Mathlib

open Filter

-- The level-8p argument is from @sturdy4days's merged PR #20140.
-- Its Siegel lower-bound development and source notices are retained below.

/- From merged OMA #8180 (0675effa26d78cdd4eb11a9fd04c6c4ec6f10809), retaining the primitive
Siegel lower-bound dependency closure and original source notices. The two omitted Euler
factors for modulus 8p yield a lower bound of one quarter for the correction. -/
/- Adapted and modified from Whidden (7a1748306e026825ed6a5555516cc2f28989b2ac), PrimeNumberTheoremAnd, Robin1984 and openai/math (3344da59991ed94f9ba711217b29c1d760badfa6, BombieriVinogradov character blocks). Modified for the frozen H1 checker. Sources: kimihiro64/bombieri-vinogradov, kimihiro64/PrimeNumberTheoremAnd@0f15a38c619298b5cd786d39a84dd4bb8997324c, kimihiro64/Robin1984@bfa72aec0c25c8ee29cefe4449d778ff30412bee; openai/math. All four distribute the following Apache-2.0 license.
Authors: James Sundstrom
Authors: Matteo Cipollina
Authors: Michael Stoll
Authors: Robby Sneiderman
Authors: Stefan Kebekus, Matteo Cipollina
Copyright (c) 2024 James Sundstrom. All rights reserved.
Copyright (c) 2024 Michael Stoll. All rights reserved.
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Copyright (c) 2026. All rights reserved.
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

section

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle

lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]


end Rectangle










































end

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





noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im















def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

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



































def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z

lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)

noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  Filter.limUnder (nhdsWithin z₀ {z₀}ᶜ) (fun z ↦ (z - z₀) * f z)

























end

section

open Filter Set Complex Real



end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz







end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz








end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter MeasureTheory Set Topology

namespace BombieriVinogradov.SiegelWalfisz







end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace Real


end Real

end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz





end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz




end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset

namespace BombieriVinogradov.SiegelWalfisz







end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz






end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz



end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz


end BombieriVinogradov.SiegelWalfisz

end
end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def quadraticCharacterFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem quadraticCharacterFour_sq : quadraticCharacterFour ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem quadraticCharacterFour_ne_one : quadraticCharacterFour ≠ 1 := by
  rw [quadraticCharacterFour, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
  intro hone
  have hvalue := congrArg (fun chi : MulChar (ZMod 4) ℤ ↦ chi (3 : ℕ)) hone
  have hthree : ZMod.χ₄ (3 : ℕ) = -1 :=
    ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [hthree] at hvalue
  have hunit : IsUnit (3 : ZMod 4) := by decide
  have honeValue : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = 1 :=
    MulChar.one_apply hunit
  rw [honeValue] at hvalue
  norm_num at hvalue

theorem three_le_level_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) : 3 ≤ N := by
  by_contra hN
  have hNle : N ≤ 2 := by omega
  interval_cases N
  · exact (NeZero.ne 0) rfl
  · exact hchi (Subsingleton.elim _ _)
  · apply hchi
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    simp


theorem primitiveCharacter_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem primitiveCharacter_sq_eq_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) :
    chi.primitiveCharacter ^ 2 = 1 := by
  apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
  rw [map_pow, chi.changeLevel_primitiveCharacter, hchi, map_one]

theorem three_le_conductor_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact three_le_level_of_ne_one chi.primitiveCharacter
    (primitiveCharacter_ne_one chi hchi)

theorem quadraticCharacterFour_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterFour := by
  rw [DirichletCharacter.IsPrimitive]
  have hlower := three_le_conductor_of_ne_one quadraticCharacterFour
    quadraticCharacterFour_ne_one
  have hdvd := quadraticCharacterFour.conductor_dvd_level
  have hupper : quadraticCharacterFour.conductor ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdvd
  interval_cases quadraticCharacterFour.conductor
  · norm_num at hdvd
  · rfl

theorem crossLevelMul_sq_eq_one {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1) :
    DirichletCharacter.mul chi psi ^ 2 = 1 := by
  change (DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi) ^ 2 = 1
  rw [mul_pow, ← map_pow, hchiSquare, map_one, ← map_pow, hpsiSquare, map_one, one_mul]

theorem crossLevelMul_ne_one_of_primitive_of_ne {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : DirichletCharacter.IsPrimitive chi)
    (hpsi : DirichletCharacter.IsPrimitive psi) (hNM : N ≠ M) :
    DirichletCharacter.mul chi psi ≠ 1 := by
  intro hmul
  change DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi = 1 at hmul
  have hinv : DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi =
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  have hconductor := congrArg DirichletCharacter.conductor hinv
  rw [DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_inv,
    DirichletCharacter.conductor_changeLevel,
    hchi, hpsi] at hconductor
  exact hNM hconductor

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticValue_cases {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hχ : χ ^ 2 = 1) (n : ℕ) :
    χ n = 0 ∨ χ n = 1 ∨ χ n = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ n

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLevelCorrection {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℝ) : ℂ :=
  ∏ p ∈ N.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-(s : ℂ)))

theorem characterLevelCorrection_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    {s : ℝ} (hs : 0 < s) : 0 < characterLevelCorrection chi s := by
  rw [characterLevelCorrection]
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  have hrpowPos : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
  have hrpowLt : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpgt (neg_neg_of_pos hs)
  rcases quadraticValue_cases chi.primitiveCharacter
      (primitiveCharacter_sq_eq_one chi hchiSquare) p with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, one_mul, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s),
      ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.zero_lt_real.mpr (sub_pos.mpr hrpowLt)
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s)]
    convert Complex.zero_lt_real.mpr (show 0 < 1 + (p : ℝ) ^ (-s) by positivity) using 1
    norm_num [Complex.ofReal_add]

theorem LFunction_eq_primitive_mul_correction {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : ℝ} :
    chi.LFunction s =
      chi.primitiveCharacter.LFunction s * characterLevelCorrection chi s := by
  have hprimitive := primitiveCharacter_ne_one chi hchi
  have hchange := DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
    chi.primitiveCharacter (s := (s : ℂ)) (.inl hprimitive)
  rw [chi.changeLevel_primitiveCharacter] at hchange
  exact hchange

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter LSeries Set

namespace BombieriVinogradov.SiegelWalfisz

private theorem quadraticLFunction_im_eq_zero_of_one_lt_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1)
    {x : ℝ} (hx : 1 < x) : (chi.LFunction x).im = 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)]
  rw [LSeries, Complex.im_tsum (chi.LSeriesSummable_of_one_lt_re (by simpa using hx))]
  convert tsum_zero with n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    rcases quadraticValue_cases chi hchi n with hzero | hone | hneg
    · simp [hzero]
    · rw [hone, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp
    · rw [hneg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      simp

private theorem quadraticLFunction_im_eq_zero_at_one_bv616 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    (chi.LFunction 1).im = 0 := by
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).im
  have hLcont : ContinuousAt chi.LFunction (1 : ℂ) :=
    (chi.differentiableAt_LFunction 1 (.inr hchi_ne)).continuousAt
  have hLreal : ContinuousAt (fun x : ℝ ↦ chi.LFunction x) 1 :=
    hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
  have hfcont : ContinuousAt f 1 :=
    Complex.continuous_im.continuousAt.comp' hLreal
  have hlimit : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds (f 1)) :=
    hfcont.mono_left inf_le_left
  have hzero : Tendsto f (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hx).symm
  exact tendsto_nhds_unique hlimit hzero

theorem quadraticLFunction_one_re_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    0 < (chi.LFunction 1).re := by
  have habs : LSeries.abscissaOfAbsConv (chi ·) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) chi]
    exact EReal.coe_lt_top 1
  have hseries : Tendsto (fun x : ℝ ↦ LSeries (chi ·) x) atTop (nhds 1) := by
    simpa using LSeries.tendsto_atTop habs
  have hL : Tendsto (fun x : ℝ ↦ chi.LFunction x) atTop (nhds 1) := by
    apply hseries.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hx)).symm
  have hre : Tendsto (fun x : ℝ ↦ (chi.LFunction x).re) atTop (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp hL using 1 <;>
      simp [Function.comp_def]
  have heventuallyPos : ∀ᶠ x : ℝ in atTop, 0 < (chi.LFunction x).re :=
    hre (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨X, hXpos, hXone⟩ :=
    (heventuallyPos.and (eventually_gt_atTop (a := (1 : ℝ)))).exists
  by_contra hnot
  have himOne := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hreOne_ne : (chi.LFunction 1).re ≠ 0 := by
    intro hreOne
    apply chi.LFunction_apply_one_ne_zero hchi_ne
    apply Complex.ext
    · simpa using hreOne
    · simpa using himOne
  have hreOne_neg : (chi.LFunction 1).re < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hreOne_ne
  let f : ℝ → ℝ := fun x ↦ (chi.LFunction x).re
  have hfcont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hLcont : ContinuousAt chi.LFunction (x : ℂ) :=
      (chi.differentiable_LFunction hchi_ne).continuous.continuousAt
    have hLreal : ContinuousAt (fun y : ℝ ↦ chi.LFunction y) x :=
      hLcont.comp_of_eq Complex.continuous_ofReal.continuousAt rfl
    exact Complex.continuous_re.continuousAt.comp' hLreal
  have hzeroMem : 0 ∈ Icc (f 1) (f X) := ⟨hreOne_neg.le, hXpos.le⟩
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hXone.le hfcont.continuousOn hzeroMem
  have himY : (chi.LFunction y).im = 0 := by
    rcases hy.1.eq_or_lt with rfl | hylt
    · exact himOne
    · exact quadraticLFunction_im_eq_zero_of_one_lt_bv616 chi hchi hylt
  have hLy : chi.LFunction y = 0 := by
    apply Complex.ext
    · simpa [f] using hfy
    · simpa using himY
  exact chi.LFunction_ne_zero_of_one_le_re (.inl hchi_ne) (by simpa using hy.1) hLy

theorem norm_quadraticLFunction_one_eq_re {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) (hchi_ne : chi ≠ 1) :
    ‖chi.LFunction 1‖ = (chi.LFunction 1).re := by
  have him := quadraticLFunction_im_eq_zero_at_one_bv616 chi hchi hchi_ne
  have hre := quadraticLFunction_one_re_pos chi hchi hchi_ne
  rw [Complex.norm_def, Complex.normSq_apply, him]
  norm_num [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hre]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

abbrev BoundedDirichletCharacter (N : ℕ) :=
  Σ M : Fin (N + 1), DirichletCharacter ℂ M.val

noncomputable def finiteLevelValue (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) : ℝ := by
  classical
  exact if hlevel : 0 < entry.1.val then
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      if hquadratic : entry.2 ^ 2 = 1 ∧ Ne entry.2 1 then
        (entry.2.LFunction 1).re * (entry.1.val : ℝ) ^ epsilon
      else
        1
    else
      1

theorem finiteLevelValue_pos (epsilon : ℝ) {N : ℕ}
    (entry : BoundedDirichletCharacter N) :
    0 < finiteLevelValue epsilon entry := by
  classical
  rw [finiteLevelValue]
  split
  · next hlevel =>
      let _ : NeZero entry.1.val := ⟨hlevel.ne'⟩
      split
      · next hquadratic =>
          have hlevelReal : (0 : ℝ) < (entry.1.val : ℕ) := by
            exact_mod_cast hlevel
          exact mul_pos
            (quadraticLFunction_one_re_pos entry.2 hquadratic.1 hquadratic.2)
            (Real.rpow_pos_of_pos hlevelReal epsilon)
      · norm_num
  · norm_num

noncomputable def finiteLevelValues (epsilon : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset (BoundedDirichletCharacter N)).image
    (finiteLevelValue epsilon)

theorem finiteLevelValues_nonempty (epsilon : ℝ) (N : ℕ) :
    (finiteLevelValues epsilon N).Nonempty := by
  classical
  unfold finiteLevelValues
  exact Finset.image_nonempty.mpr Finset.univ_nonempty

noncomputable def finiteLevelConstant (epsilon : ℝ) (N : ℕ) : ℝ :=
  (finiteLevelValues epsilon N).min' (finiteLevelValues_nonempty epsilon N)

theorem finiteLevelConstant_pos (epsilon : ℝ) (N : ℕ) :
    0 < finiteLevelConstant epsilon N := by
  classical
  have hmem := Finset.min'_mem (finiteLevelValues epsilon N)
    (finiteLevelValues_nonempty epsilon N)
  unfold finiteLevelValues at hmem
  obtain ⟨entry, _, hentry⟩ := Finset.mem_image.mp hmem
  unfold finiteLevelConstant
  unfold finiteLevelValues
  rw [← hentry]
  exact finiteLevelValue_pos epsilon entry

theorem finiteLevelConstant_le_value {epsilon : ℝ} {N M : ℕ}
    [NeZero M] (hMN : M ≤ N) (hM : 3 ≤ M)
    (psi : DirichletCharacter ℂ M) (hpsiSquare : psi ^ 2 = 1)
    (hpsi : Ne psi 1) :
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
      (psi.LFunction 1).re := by
  classical
  let level : Fin (N + 1) := ⟨M, Nat.lt_succ_of_le hMN⟩
  let entry : BoundedDirichletCharacter N := ⟨level, psi⟩
  have hlevel : 0 < level.val := by
    dsimp [level]
    omega
  have hentryValue : finiteLevelValue epsilon entry =
      (psi.LFunction 1).re * (M : ℝ) ^ epsilon := by
    rw [finiteLevelValue]
    simp [entry, level, hlevel, hpsiSquare, hpsi]
  have hentryMem : finiteLevelValue epsilon entry ∈ finiteLevelValues epsilon N := by
    rw [finiteLevelValues]
    exact Finset.mem_image.mpr ⟨entry, Finset.mem_univ _, rfl⟩
  have hminimum : finiteLevelConstant epsilon N ≤ finiteLevelValue epsilon entry := by
    exact Finset.min'_le _ _ hentryMem
  rw [hentryValue] at hminimum
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hscaled := mul_le_mul_of_nonneg_right hminimum
    (Real.rpow_nonneg hMnonneg (-epsilon))
  calc
    finiteLevelConstant epsilon N * (M : ℝ) ^ (-epsilon) ≤
        ((psi.LFunction 1).re * (M : ℝ) ^ epsilon) *
          (M : ℝ) ^ (-epsilon) := hscaled
    _ = (psi.LFunction 1).re := by
      rw [mul_assoc, ← Real.rpow_add hMpos]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) : ℝ :=
  max (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))

theorem seven_eighths_le_siegelLowerEndpoint (epsilon : ℝ) (D : ℕ) :
    7 / 8 ≤ siegelLowerEndpoint epsilon D :=
  le_max_left _ _

theorem siegelLowerEndpoint_lt_one {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) : siegelLowerEndpoint epsilon D < 1 := by
  apply max_lt
  · norm_num
  · have hdenominator : 0 < 2 * ((D : ℝ) + 1) := by positivity
    have : 0 < epsilon / (2 * ((D : ℝ) + 1)) := div_pos hepsilon hdenominator
    linarith

theorem siegel_exponent_control {epsilon s : ℝ} (hepsilon : 0 < epsilon)
    (D : ℕ) (hs : siegelLowerEndpoint epsilon D ≤ s) :
    (D : ℝ) * (1 - s) + epsilon / 2 ≤ epsilon := by
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hDplus : 0 < (D : ℝ) + 1 := by positivity
  have hrange : 1 - epsilon / (2 * ((D : ℝ) + 1)) ≤ s :=
    (le_max_right (7 / 8) (1 - epsilon / (2 * ((D : ℝ) + 1)))).trans hs
  have hgap : 1 - s ≤ epsilon / (2 * ((D : ℝ) + 1)) := by linarith
  have hscaled : (D : ℝ) * (1 - s) ≤
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hgap hDnonneg
  have hratio : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 :=
    (div_le_one hDplus).2 (by linarith)
  have habsorb : (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) ≤ epsilon / 2 := by
    calc
      (D : ℝ) * (epsilon / (2 * ((D : ℝ) + 1))) =
          (epsilon / 2) * ((D : ℝ) / ((D : ℝ) + 1)) := by
        field_simp
      _ ≤ epsilon / 2 :=
        mul_le_of_le_one_right (div_nonneg hepsilon.le zero_le_two) hratio
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelCauchyCircle : Set ℂ := sphere 2 (3 / 2 : ℝ)


theorem siegelCauchyCircle_norm_sub_one_lower {s : ℂ}
    (hs : s ∈ siegelCauchyCircle) : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have hdist : dist s (2 : ℂ) = (3 / 2 : ℝ) := by
    simpa only [siegelCauchyCircle, mem_sphere] using hs
  have htriangle : dist s (2 : ℂ) ≤ dist s (1 : ℂ) + dist (1 : ℂ) (2 : ℂ) :=
    dist_triangle _ _ _
  rw [hdist] at htriangle
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  try rw [hone] at htriangle
  linarith

theorem siegelCauchyCircle_ne_one {s : ℂ} (hs : s ∈ siegelCauchyCircle) : s ≠ 1 := by
  intro h
  subst s
  have hbound := siegelCauchyCircle_norm_sub_one_lower hs
  norm_num at hbound


end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

def siegelAnalyticDomain : Set ℂ := ball 2 (7 / 4 : ℝ)

theorem siegelCauchyCircle_subset_analyticDomain :
    siegelCauchyCircle ⊆ siegelAnalyticDomain := by
  intro s hs
  rw [siegelCauchyCircle, mem_sphere] at hs
  rw [siegelAnalyticDomain, mem_ball]
  linarith

theorem siegelAnalyticDomain_re_lower {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    (1 / 4 : ℝ) < s.re := by
  have hnorm : ‖s - 2‖ < (7 / 4 : ℝ) := by
    simpa [siegelAnalyticDomain, mem_ball, Complex.dist_eq] using hs
  have hre : |s.re - 2| < (7 / 4 : ℝ) :=
    (Complex.abs_re_le_norm (s - 2)).trans_lt (by simpa using hnorm)
  linarith [neg_abs_le (s.re - 2)]

theorem siegelAnalyticDomain_norm_upper {s : ℂ} (hs : s ∈ siegelAnalyticDomain) :
    ‖s‖ < (15 / 4 : ℝ) := by
  have hdist : dist s (2 : ℂ) < (7 / 4 : ℝ) := by
    simpa only [siegelAnalyticDomain, mem_ball] using hs
  have htriangle : dist s (0 : ℂ) ≤ dist s (2 : ℂ) + dist (2 : ℂ) (0 : ℂ) :=
    dist_triangle _ _ _
  rw [Complex.dist_eq] at hdist
  simp only [Complex.dist_eq] at htriangle
  norm_num at htriangle
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlock {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ j : ZMod N, χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)

theorem characterLBlock_recenter {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) (s : ℂ) :
    characterLBlock χ k s =
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) := by
  rw [characterLBlock]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [χ.sum_eq_zero_of_ne_one hχ, zero_mul, sub_zero]

theorem characterLBlock_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) :
    DifferentiableOn ℂ (characterLBlock χ k) siegelAnalyticDomain := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [show characterLBlock χ k = fun s ↦
      ∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s)) by
    funext s
    exact characterLBlock_recenter χ hχ k s]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    rw [χ.map_zero' hN]
    simp
  · have hx : ((k * N + j.val : ℕ) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (by
        have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        omega)
    have hy : ((((k + 1) * N : ℕ) : ℂ)) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (NeZero.ne N))
    exact (((differentiableAt_id.neg).const_cpow (Or.inl hx)).sub
      ((differentiableAt_id.neg).const_cpow (Or.inl hy))).const_mul (χ j)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

private theorem sum_zmod_val_inv_le_harmonic_bv622 (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  calc
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) = ∑ i : Fin N, ((i.val : ℝ)⁻¹) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro i
      change ((i.val : ℝ)⁻¹) = ((((ZMod.finEquiv N) i).val : ℝ)⁻¹)
      congr 2
      obtain _ | n := N
      · exact (NeZero.ne 0 rfl).elim
      · rfl
    _ ≤ ∑ i : Fin N, 2 * ((((i.val + 1 : ℕ) : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hipos : (0 : ℝ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hi0
        have hisucc : (0 : ℝ) < i.val + 1 := by positivity
        rw [← one_div, ← div_eq_mul_inv]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [div_le_div_iff₀ hipos hisucc]
        norm_num
        have hiNat : i.val + 1 ≤ 2 * i.val := by omega
        exact_mod_cast hiNat
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_fin_eq_sum_range, harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]

theorem norm_characterLBlock_zero_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlock chi 0 1‖ ≤ 2 * (1 + Real.log N) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock]
  calc
    ‖∑ j : ZMod N, chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : ZMod N, ((j.val : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * ‖((j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ := by
            norm_num only [Nat.zero_mul, Nat.zero_add]
            exact mul_le_mul_of_nonneg_right (chi.norm_le_one j) (norm_nonneg _)
          _ = ((j.val : ℝ)⁻¹) := by
            rw [one_mul, show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num,
              ← Complex.ofReal_natCast j.val,
              ← Complex.ofReal_cpow (Nat.cast_nonneg j.val) (-1), Complex.norm_real,
              Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j.val) _),
              Real.rpow_neg_one]
    _ ≤ 2 * (harmonic N : ℝ) := sum_zmod_val_inv_le_harmonic_bv622 N
    _ ≤ 2 * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_one_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖(x : ℂ) ^ ((-1 : ℝ) : ℂ) - (y : ℂ) ^ ((-1 : ℝ) : ℂ)‖ ≤
      (y - x) / x ^ 2 := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← Complex.ofReal_cpow hx.le (-1), ← Complex.ofReal_cpow hy.le (-1),
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_neg_one, Real.rpow_neg_one]
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hy hx).mpr hxy
  rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
  have hid : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
    field_simp
  rw [hid, pow_two]
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (mul_pos hx hx)
    (mul_le_mul_of_nonneg_left hxy hx.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖characterLBlock chi k 1‖ ≤ ((k : ℝ) ^ 2)⁻¹ := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock_recenter chi hchi]
  calc
    ‖∑ j : ZMod N, chi j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
          (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
            (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N, (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxNat : 0 < k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hkN : k * N ≤ k * N + j.val := Nat.le_add_right _ _
        have hx : (0 : ℝ) < (k * N + j.val : ℕ) := by exact_mod_cast hxNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hkNreal : ((k * N : ℕ) : ℝ) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hkN
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
        have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
        have hvar := norm_cpow_neg_one_sub_le hx hxy
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * (((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                ((k * N + j.val : ℕ) : ℝ) ^ 2) := by
            have hvar' :
                ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
                  (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
                    ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                      ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
              rw [show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num]
              simpa only [Complex.ofReal_natCast] using hvar
            exact mul_le_mul (chi.norm_le_one j) hvar'
              (by positivity) (by positivity)
          _ ≤ (N : ℝ) / ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
            simpa using div_le_div_of_nonneg_right hlen (sq_nonneg _)
          _ ≤ (N : ℝ) / ((k * N : ℕ) : ℝ) ^ 2 := by
            have hkNposNat : 0 < k * N := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hk) (NeZero.pos N)
            have hdenpos : 0 < (((k * N : ℕ) : ℝ) ^ 2) := by
              exact pow_pos (by exact_mod_cast hkNposNat) 2
            have hsq : (((k * N : ℕ) : ℝ) ^ 2) ≤
                (((k * N + j.val : ℕ) : ℝ) ^ 2) := by
              nlinarith [show (0 : ℝ) ≤ (k * N : ℕ) by positivity]
            exact div_le_div_of_nonneg_left hNpos.le hdenpos hsq
          _ = (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
            norm_num [Nat.cast_mul]
            field_simp
    _ = ((k : ℝ) ^ 2)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_cpow_neg_sub_le {s : ℂ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hre : (1 / 4 : ℝ) ≤ s.re) (hs : ‖s‖ ≤ (15 / 4 : ℝ)) :
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖ ≤
      (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    subst s
    norm_num at hre
  have hderiv (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ ↦ (u : ℂ) ^ (-s))
        ((-s) * (t : ℂ) ^ (-s - 1)) (Icc x y) t := by
    exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)))
      hs0).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc x y) :
      ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ (15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ) := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
    have hpow_exp : t ^ (-s.re - 1) ≤ t ^ (-5 / 4 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hx.trans ht.1
      · linarith
    have hpow_base : t ^ (-5 / 4 : ℝ) ≤ x ^ (-5 / 4 : ℝ) := by
      exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx) ht.1 (by norm_num)
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact mul_le_mul hs (hpow_exp.trans hpow_base) (Real.rpow_nonneg htpos.le _) (by norm_num)
  have hmv := (convex_Icc x y : Convex ℝ (Icc x y)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy)
  rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hmv
  calc
    ‖(x : ℂ) ^ (-s) - (y : ℂ) ^ (-s)‖
        ≤ ((15 / 4 : ℝ) * x ^ (-5 / 4 : ℝ)) * (y - x) := hmv
    _ = (15 / 4 : ℝ) * (y - x) * x ^ (-5 / 4 : ℝ) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockMajorant (N k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

theorem norm_characterLBlock_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlock χ k s‖ ≤ characterLBlockMajorant N k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [characterLBlock_recenter χ hχ]
  calc
    ‖∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖
        ≤ ∑ j : ZMod N, ‖χ j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [χ.map_zero' hN]
        simp only [zero_mul, norm_zero]
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxoneNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hxkNat : k + 1 ≤ k * N + j.val := by
          have hNp := NeZero.pos N
          have hk : k ≤ k * N := by
            simpa using Nat.mul_le_mul_left k hNp
          omega
        have hxone : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxoneNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hxk : (((k + 1 : ℕ) : ℝ)) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hxkNat
        have hpow : ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
        have hvar := norm_cpow_neg_sub_le hxone hxy
          (le_of_lt (siegelAnalyticDomain_re_lower hs))
          (le_of_lt (siegelAnalyticDomain_norm_upper hs))
        rw [norm_mul]
        calc
          ‖χ j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖
              ≤ ‖χ j‖ * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
          _ ≤ 1 * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
            gcongr
            exact χ.norm_le_one j
          _ = (15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by ring
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) *
                ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlen (by norm_num)) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = characterLBlockMajorant N k := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [characterLBlockMajorant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k : ℕ, characterLBlock χ k s

theorem characterLBlockMajorant_summable (N : ℕ) :
    Summable (characterLBlockMajorant N) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hp
  change Summable (fun k : ℕ ↦
    (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  exact hshift.mul_left ((15 / 4 : ℝ) * (N : ℝ) ^ 2)

theorem characterLBlockSeries_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (characterLBlockSeries χ) siegelAnalyticDomain := by
  change DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ, characterLBlock χ k s)
    siegelAnalyticDomain
  exact Complex.differentiableOn_tsum_of_summable_norm
    (characterLBlockMajorant_summable N)
    (fun k ↦ characterLBlock_differentiableOn χ hχ k)
    (by exact Metric.isOpen_ball)
    (fun k s hs ↦ norm_characterLBlock_le χ hχ k hs)

theorem norm_characterLBlockSeries_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlockSeries χ s‖ ≤ ∑' k : ℕ, characterLBlockMajorant N k := by
  rw [characterLBlockSeries]
  exact tsum_of_norm_bounded (characterLBlockMajorant_summable N).hasSum
    (fun k ↦ norm_characterLBlock_le χ hχ k hs)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLTailConstant : ℝ :=
  ∑' k : ℕ, ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)

theorem characterLTail_summable :
    Summable (fun k : ℕ ↦ ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  have hp : Summable (fun k : ℕ ↦ (((k : ℝ) ^ 2)⁻¹)) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hp

theorem characterLTailConstant_nonneg : 0 ≤ characterLTailConstant := by
  rw [characterLTailConstant]
  exact tsum_nonneg fun k ↦ by positivity

theorem characterLBlock_one_norm_summable {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    Summable (fun k : ℕ ↦ ‖characterLBlock chi k 1‖) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, Metric.mem_ball]
    norm_num [Complex.dist_eq]
  exact (characterLBlockMajorant_summable N).of_nonneg_of_le
    (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs

set_option maxHeartbeats 4000000 in
theorem characterLBlock_tail_norm_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ ≤ characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  have htailNorm : Summable (fun k : ℕ ↦ ‖characterLBlock chi (k + 1) 1‖) :=
    (summable_nat_add_iff 1).mpr hnorm
  rw [characterLTailConstant]
  exact htailNorm.tsum_le_tsum
    (fun k ↦ norm_characterLBlock_one_le chi hchi (Nat.le_add_left 1 k))
    characterLTail_summable

theorem norm_characterLBlockSeries_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlockSeries chi 1‖ ≤
      2 * (1 + Real.log N) + characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  rw [characterLBlockSeries]
  calc
    ‖∑' k : ℕ, characterLBlock chi k 1‖ ≤
        ∑' k : ℕ, ‖characterLBlock chi k 1‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ‖characterLBlock chi 0 1‖ +
        ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ := hnorm.tsum_eq_zero_add
    _ ≤ 2 * (1 + Real.log N) + characterLTailConstant :=
      add_le_add (norm_characterLBlock_zero_one_le chi hchi)
        (characterLBlock_tail_norm_le chi hchi)

end BombieriVinogradov.SiegelWalfisz

end

section

open Complex Filter LSeries Metric Set Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_characterLBlockSeries_of_one_lt_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = characterLBlockSeries χ s := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  have hzero : (fun n : ℕ ↦ χ n) 0 = 0 := by
    simpa using χ.map_zero' hN
  have hsum : Summable (fun n : ℕ ↦ χ n * (n : ℂ) ^ (-s)) := by
    rw [← funext (LSeries.term_def₀ hzero s)]
    exact DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hterm (j : ZMod N) (k : ℕ) :
      χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) =
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
    have hcast : ((j.val + N * k : ℕ) : ZMod N) = j := by
      simp [Nat.cast_add, Nat.cast_mul]
    rw [hcast]
    congr 2
    simp only [Nat.add_comm, Nat.mul_comm]
  have hsub (j : ZMod N) :
      Summable (fun k : ℕ ↦ χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ ↦ j.val + N * k) := by
      intro a b hab
      exact Nat.mul_left_cancel (NeZero.pos N) (Nat.add_left_cancel hab)
    have h := hsum.comp_injective hinj
    exact h.congr (hterm j)
  have hswap := Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _hj ↦ hsub j)
  calc
    χ.LFunction s = LSeries (χ ·) s := DirichletCharacter.LFunction_eq_LSeries χ hs
    _ = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
      rw [LSeries_def₀ hzero]
      congr 1
      funext n
      rw [Complex.cpow_neg, div_eq_mul_inv]
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ ((j.val + N * k : ℕ) : ZMod N) * ((j.val + N * k : ℕ) : ℂ) ^ (-s) :=
      Nat.sumByResidueClasses hsum N
    _ = ∑ j : ZMod N, ∑' k : ℕ,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_congr (hterm j)
    _ = ∑' k : ℕ, ∑ j : ZMod N,
        χ j * ((k * N + j.val : ℕ) : ℂ) ^ (-s) := by
      simpa only [Finset.mem_univ, ↓reduceIte] using hswap.symm
    _ = characterLBlockSeries χ s := rfl

theorem LFunction_eq_characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) : χ.LFunction s = characterLBlockSeries χ s := by
  have hL : AnalyticOnNhd ℂ (χ.LFunction) siegelAnalyticDomain :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hB : AnalyticOnNhd ℂ (characterLBlockSeries χ) siegelAnalyticDomain :=
    (characterLBlockSeries_differentiableOn χ hχ).analyticOnNhd Metric.isOpen_ball
  have h2 : (2 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num
  have heq : χ.LFunction =ᶠ[𝓝 (2 : ℂ)] characterLBlockSeries χ := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    exact LFunction_eq_characterLBlockSeries_of_one_lt_re χ hχ hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_ball (2 : ℂ) (7 / 4 : ℝ)).isPreconnected h2 heq hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLLogBoundConstant : ℝ :=
  2 + characterLTailConstant

theorem characterLLogBoundConstant_pos : 0 < characterLLogBoundConstant := by
  rw [characterLLogBoundConstant]
  linarith [characterLTailConstant_nonneg]

theorem norm_LFunction_one_le_log {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖chi.LFunction 1‖ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num [Complex.dist_eq]
  have hlog : 1 ≤ 1 + Real.log N := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    linarith [Real.log_nonneg hN]
  rw [LFunction_eq_characterLBlockSeries chi hchi hs]
  calc
    ‖characterLBlockSeries chi 1‖ ≤
        2 * (1 + Real.log N) + characterLTailConstant :=
      norm_characterLBlockSeries_one_le chi hchi
    _ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
      rw [characterLLogBoundConstant]
      nlinarith [characterLTailConstant_nonneg]

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLAbsoluteMajorant (k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

noncomputable def characterLBoundConstant : ℝ :=
  1 + ∑' k : ℕ, characterLAbsoluteMajorant k

theorem characterLBoundConstant_pos : 0 < characterLBoundConstant := by
  have hnon : 0 ≤ ∑' k : ℕ, characterLAbsoluteMajorant k := by
    apply tsum_nonneg
    intro k
    rw [characterLAbsoluteMajorant]
    positivity
  rw [characterLBoundConstant]
  linarith

theorem norm_LFunction_le_square_on_analyticDomain {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖χ.LFunction s‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  rw [LFunction_eq_characterLBlockSeries χ hχ hs]
  apply (norm_characterLBlockSeries_le χ hχ hs).trans
  calc
    ∑' k : ℕ, characterLBlockMajorant N k =
        (N : ℝ) ^ 2 * ∑' k : ℕ, characterLAbsoluteMajorant k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [characterLAbsoluteMajorant, characterLBlockMajorant]
      ring
    _ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
      rw [mul_comm characterLBoundConstant]
      apply mul_le_mul_of_nonneg_left
      · rw [characterLBoundConstant]
        linarith
      · positivity


theorem norm_LFunction_one_le_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  apply norm_LFunction_le_square_on_analyticDomain χ hχ
  rw [siegelAnalyticDomain, mem_ball]
  norm_num [Complex.dist_eq]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction

namespace BombieriVinogradov.SiegelWalfisz

theorem arithmeticFunction_mul_apply_primePower (f g : ArithmeticFunction ℂ)
    {p r : ℕ} (hp : p.Prime) :
    (f * g) (p ^ r) = ∑ i ∈ Finset.range (r + 1), f (p ^ i) * g (p ^ (r - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y ↦ f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

noncomputable def characterPairArithmetic {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n ↦ χ n * ψ n

theorem toArithmeticFunction_apply_of_ne_zero (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    toArithmeticFunction f n = f n := by
  simp [toArithmeticFunction, hn]

theorem characterPairArithmetic_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (characterPairArithmetic χ ψ).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {m n} hm hn _ ↦ ?_⟩
  · simp [characterPairArithmetic, toArithmeticFunction]
  · simp [characterPairArithmetic, toArithmeticFunction, hm, hn, map_mul]
    ring

theorem arithmeticZeta_primePower {p i : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ i) = 1 := by
  simp [hp.ne_zero]

theorem characterArithmetic_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p i : ℕ} (hp : p.Prime) :
    toArithmeticFunction (χ ·) (p ^ i) = (χ p) ^ i := by
  rw [← χ.apply_eq_toArithmeticFunction_apply (pow_ne_zero i hp.ne_zero), Nat.cast_pow,
    map_pow]

theorem characterPairArithmetic_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p i : ℕ} (hp : p.Prime) :
    characterPairArithmetic χ ψ (p ^ i) = (χ p * ψ p) ^ i := by
  have hpPow : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  rw [characterPairArithmetic, toArithmeticFunction_apply_of_ne_zero _ hpPow]
  simp only [Nat.cast_pow, map_pow, mul_pow]

noncomputable def siegelProductCoefficients {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    characterPairArithmetic χ ψ

theorem siegelProductCoefficients_isMultiplicative {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (siegelProductCoefficients χ ψ).IsMultiplicative := by
  exact (((isMultiplicative_zeta.natCast.mul χ.isMultiplicative_toArithmeticFunction).mul
    ψ.isMultiplicative_toArithmeticFunction).mul (characterPairArithmetic_isMultiplicative χ ψ))

theorem siegelProductCoefficients_grouped {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·)) *
        (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients, mul_assoc]

theorem siegelProductCoefficients_grouped_swap {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (ψ ·)) *
        (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) := by
  rw [siegelProductCoefficients]
  ring


end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def localPairCoefficient (a b : ℂ) (r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1), a ^ i * b ^ (r - i)

theorem arithmeticFunction_mul_apply_primePower_eq_localPair
    (f g : ArithmeticFunction ℂ) (a b : ℂ) {p r : ℕ} (hp : p.Prime)
    (hf : ∀ i : ℕ, f (p ^ i) = a ^ i) (hg : ∀ i : ℕ, g (p ^ i) = b ^ i) :
    (f * g) (p ^ r) = localPairCoefficient a b r := by
  rw [arithmeticFunction_mul_apply_primePower f g hp, localPairCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]

theorem localPairCoefficient_comm (a b : ℂ) (r : ℕ) :
    localPairCoefficient a b r = localPairCoefficient b a r := by
  simpa [localPairCoefficient] using (Commute.all a b).geom_sum₂_comm (r + 1)

theorem localPairCoefficient_one_left_eq_geom (b : ℂ) (r : ℕ) :
    localPairCoefficient 1 b r = ∑ i ∈ Finset.range (r + 1), b ^ i := by
  calc
    localPairCoefficient 1 b r = localPairCoefficient b 1 r :=
      localPairCoefficient_comm 1 b r
    _ = ∑ i ∈ Finset.range (r + 1), b ^ i := by
      simp [localPairCoefficient]

theorem localPairCoefficient_one_left_nonneg (b : ℂ)
    (hb : b = 0 ∨ b = 1 ∨ b = -1) (r : ℕ) :
    0 ≤ localPairCoefficient 1 b r := by
  rw [localPairCoefficient_one_left_eq_geom]
  rcases hb with rfl | rfl | rfl
  · simp [zero_geom_sum]
  · simp only [one_geom_sum]
    exact_mod_cast Nat.zero_le (r + 1)
  · rw [neg_one_geom_sum]
    split_ifs <;> simp

theorem localPairCoefficient_one_right_nonneg (a : ℂ)
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (r : ℕ) :
    0 ≤ localPairCoefficient a 1 r := by
  rw [localPairCoefficient_comm]
  exact localPairCoefficient_one_left_nonneg a ha r

theorem localPairCoefficient_zero_zero_nonneg (r : ℕ) :
    0 ≤ localPairCoefficient 0 0 r := by
  cases r with
  | zero => simp [localPairCoefficient]
  | succ r =>
      rw [localPairCoefficient]
      apply Finset.sum_nonneg
      intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · simp
      · simp [zero_pow hi0]

theorem zeta_mul_character_primePower {N : ℕ} (χ : DirichletCharacter ℂ N)
    {p r : ℕ} (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (χ ·))
        (p ^ r) = localPairCoefficient 1 (χ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ by simpa using arithmeticZeta_primePower hp)
    (fun _ ↦ characterArithmetic_primePower χ hp)

theorem character_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (χ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (χ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower χ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

theorem character_right_mul_pair_primePower {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p r : ℕ} (hp : p.Prime) :
    (toArithmeticFunction (ψ ·) * characterPairArithmetic χ ψ) (p ^ r) =
      localPairCoefficient (ψ p) (χ p * ψ p) r :=
  arithmeticFunction_mul_apply_primePower_eq_localPair _ _ _ _ hp
    (fun _ ↦ characterArithmetic_primePower ψ hp)
    (fun _ ↦ characterPairArithmetic_primePower χ ψ hp)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_primePower_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) {p r : ℕ} (hp : p.Prime) :
    0 ≤ siegelProductCoefficients χ ψ (p ^ r) := by
  rcases quadraticValue_cases χ hχ p with hχp | hχp | hχp
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, zero_mul]
      exact localPairCoefficient_zero_zero_nonneg (r - i)
  · rw [siegelProductCoefficients_grouped_swap,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower ψ hp]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) i
    · rw [character_mul_pair_primePower χ ψ hp, hχp, one_mul]
      exact localPairCoefficient_one_left_nonneg _ (quadraticValue_cases ψ hψ p) (r - i)
  · rw [siegelProductCoefficients_grouped,
      arithmeticFunction_mul_apply_primePower _ _ hp]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · rw [zeta_mul_character_primePower χ hp, hχp]
      exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) i
    · rw [character_right_mul_pair_primePower χ ψ hp, hχp]
      rcases quadraticValue_cases ψ hψ p with hψp | hψp | hψp
      · rw [hψp]
        norm_num
        exact localPairCoefficient_zero_zero_nonneg (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_left_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)
      · rw [hψp]
        norm_num
        exact localPairCoefficient_one_right_nonneg (-1) (Or.inr (Or.inr rfl)) (r - i)

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductCoefficients_nonneg {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1) (n : ℕ) :
    0 ≤ siegelProductCoefficients χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [(siegelProductCoefficients_isMultiplicative χ ψ).multiplicative_factorization
      _ hn] using!
      Finset.prod_nonneg fun p hp ↦
        siegelProductCoefficients_primePower_nonneg χ ψ hχ hψ
          (Nat.prime_of_mem_primeFactors hp)

theorem siegelProductCoefficients_one {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelProductCoefficients χ ψ 1 = 1 :=
  (siegelProductCoefficients_isMultiplicative χ ψ).map_one

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem crossLevelMul_apply_nat {N M : ℕ} (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    DirichletCharacter.mul χ ψ n = χ n * ψ n := by
  rw [DirichletCharacter.mul, MulChar.mul_apply]
  by_cases hN : n.Coprime N
  · by_cases hM : n.Coprime M
    · have hLcm : n.Coprime (N.lcm M) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul N M) (hN.mul_right hM)
      have hLcmInt : IsCoprime (n : ℤ) (N.lcm M) :=
        Nat.isCoprime_iff_coprime.mpr hLcm
      have hχEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = χ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' χ _ hLcmInt
      have hψEval :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = ψ n := by
        simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ _ hLcmInt
      rw [hχEval, hψEval]
    · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
        hM (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right N M) h)
      have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
        hLcm (Nat.isCoprime_iff_coprime.mp h)
      have hMInt : ¬IsCoprime (n : ℤ) M := fun h ↦
        hM (Nat.isCoprime_iff_coprime.mp h)
      have hLiftZero :
          DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
      have hZero : ψ n = 0 := by
        simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hMInt
      rw [hLiftZero, hZero, mul_zero, mul_zero]
  · have hLcm : ¬n.Coprime (N.lcm M) := fun h ↦
      hN (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left N M) h)
    have hLcmInt : ¬IsCoprime (n : ℤ) (N.lcm M) := fun h ↦
      hLcm (Nat.isCoprime_iff_coprime.mp h)
    have hNInt : ¬IsCoprime (n : ℤ) N := fun h ↦
      hN (Nat.isCoprime_iff_coprime.mp h)
    have hLiftZero :
        DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hLcmInt
    have hZero : χ n = 0 := by
      simpa using (DirichletCharacter.apply_eq_zero_iff _ _).mpr hNInt
    rw [hLiftZero, hZero, zero_mul, zero_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterPairArithmetic_eq_crossLevel {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    characterPairArithmetic χ ψ =
      toArithmeticFunction (DirichletCharacter.mul χ ψ ·) := by
  rw [characterPairArithmetic]
  apply toArithmeticFunction_congr
  intro n _
  exact (crossLevelMul_apply_nat χ ψ n).symm

theorem characterArithmetic_LSeriesSummable {N : ℕ}
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s fun hn ↦
    (χ.apply_eq_toArithmeticFunction_apply hn).symm).mpr
      (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)

theorem characterPairArithmetic_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (characterPairArithmetic χ ψ) s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeriesSummable (DirichletCharacter.mul χ ψ) hs

theorem siegelProductCoefficients_LSeriesSummable {N M : ℕ}
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (siegelProductCoefficients χ ψ) s := by
  rw [siegelProductCoefficients]
  exact ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
        (characterArithmetic_LSeriesSummable χ hs))
      (characterArithmetic_LSeriesSummable ψ hs))
    (characterPairArithmetic_LSeriesSummable χ ψ hs)

end BombieriVinogradov.SiegelWalfisz

end

section

open ArithmeticFunction
open LSeries

namespace BombieriVinogradov.SiegelWalfisz

theorem characterArithmetic_LSeries_eq_LFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (toArithmeticFunction (χ ·)) s = χ.LFunction s := by
  rw [LSeries_congr (fun hn ↦ (χ.apply_eq_toArithmeticFunction_apply hn).symm) s]
  exact (DirichletCharacter.LFunction_eq_LSeries χ hs).symm

theorem characterPairArithmetic_LSeries_eq_LFunction {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (characterPairArithmetic χ ψ) s =
      (DirichletCharacter.mul χ ψ).LFunction s := by
  rw [characterPairArithmetic_eq_crossLevel]
  exact characterArithmetic_LSeries_eq_LFunction (DirichletCharacter.mul χ ψ) hs

theorem siegelProduct_LSeries_eq {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (siegelProductCoefficients χ ψ) s =
      riemannZeta s * χ.LFunction s * ψ.LFunction s *
        (DirichletCharacter.mul χ ψ).LFunction s := by
  have hzeta : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hχ := characterArithmetic_LSeriesSummable χ hs
  have hψ := characterArithmetic_LSeriesSummable ψ hs
  have hpair := characterPairArithmetic_LSeriesSummable χ ψ hs
  rw [siegelProductCoefficients,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ) hpair,
    ArithmeticFunction.LSeries_mul'
      (ArithmeticFunction.LSeriesSummable_mul hzeta hχ) hψ,
    ArithmeticFunction.LSeries_mul' hzeta hχ,
    characterArithmetic_LSeries_eq_LFunction χ hs,
    characterArithmetic_LSeries_eq_LFunction ψ hs,
    characterPairArithmetic_LSeries_eq_LFunction χ ψ hs]
  simp_rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    ← ArithmeticFunction.natCoe_apply]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLProduct {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  χ.LFunction s * ψ.LFunction s * (DirichletCharacter.mul χ ψ).LFunction s

noncomputable def siegelProductResidue {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) : ℂ :=
  χ.LFunction 1 * ψ.LFunction 1 * (DirichletCharacter.mul χ ψ).LFunction 1

theorem siegelLProduct_differentiable {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelLProduct χ ψ) := by
  exact ((DirichletCharacter.differentiable_LFunction hχ).mul
    (DirichletCharacter.differentiable_LFunction hψ)).mul
      (DirichletCharacter.differentiable_LFunction hmul)

theorem siegelLProduct_one {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    siegelLProduct χ ψ 1 = siegelProductResidue χ ψ :=
  rfl

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelResidueBoundConstant : ℝ := characterLBoundConstant ^ 3

theorem siegelResidueBoundConstant_pos : 0 < siegelResidueBoundConstant := by
  rw [siegelResidueBoundConstant]
  exact pow_pos characterLBoundConstant_pos 3

theorem norm_siegelProductResidue_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    ‖siegelProductResidue χ ψ‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hχb := norm_LFunction_one_le_square χ hχ
  have hψb := norm_LFunction_one_le_square ψ hψ
  have hmulb := norm_LFunction_one_le_square (DirichletCharacter.mul χ ψ) hmul
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(DirichletCharacter.mul χ ψ).LFunction 1‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelLProduct_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    ‖siegelLProduct χ ψ s‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hsDomain := siegelCauchyCircle_subset_analyticDomain hs
  have hχb := norm_LFunction_le_square_on_analyticDomain χ hχ hsDomain
  have hψb := norm_LFunction_le_square_on_analyticDomain ψ hψ hsDomain
  have hmulb := norm_LFunction_le_square_on_analyticDomain
    (DirichletCharacter.mul χ ψ) hmul hsDomain
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelLProduct, norm_mul, norm_mul]
  calc
    ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(DirichletCharacter.mul χ ψ).LFunction s‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem zetaRegularized_differentiable : Differentiable ℂ riemannZeta₀ :=
  differentiable_riemannZeta₀

theorem riemannZeta_eq_pole_add_regularized {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s :=
  riemannZeta_eq_inv_sub_add hs

end BombieriVinogradov.SiegelWalfisz

end

section

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_zetaRegularized_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta₀ s‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (2 : ℂ) (3 / 2 : ℝ)).bddAbove_image
    zetaRegularized_differentiable.continuous.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs
  exact (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)

theorem exists_riemannZeta_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta s‖ ≤ C := by
  obtain ⟨C, hC, hregular⟩ := exists_zetaRegularized_circle_bound
  refine ⟨2 + C, by linarith, ?_⟩
  intro s hs
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [riemannZeta_eq_pole_add_regularized (siegelCauchyCircle_ne_one hs)]
  exact (norm_add_le _ _).trans ((add_le_add hinv (hregular s hs)).trans_eq (by ring))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def entireDividedDifference (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z - f c) / (z - c)) c (deriv f c)

theorem entireDividedDifference_apply_of_ne (f : ℂ → ℂ) {c z : ℂ} (hz : z ≠ c) :
    entireDividedDifference f c z = (f z - f c) / (z - c) := by
  rw [entireDividedDifference, Function.update_of_ne hz]

theorem entireDividedDifference_differentiableAt_of_ne (f : ℂ → ℂ) {c z : ℂ}
    (hf : Differentiable ℂ f) (hz : z ≠ c) :
    DifferentiableAt ℂ (entireDividedDifference f c) z := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · have hconst : DifferentiableAt ℂ (fun _ : ℂ ↦ f c) z := by fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) z := by fun_prop
    exact ((hf z).sub hconst).div hden (sub_ne_zero.mpr hz)
  · filter_upwards [eventually_ne_nhds hz] with w hw
    exact entireDividedDifference_apply_of_ne f hw

theorem entireDividedDifference_differentiable (f : ℂ → ℂ) (c : ℂ)
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (entireDividedDifference f c) := by
  intro z
  rcases eq_or_ne z c with rfl | hz
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact entireDividedDifference_differentiableAt_of_ne f hf (by simpa using hw)
    · simpa [entireDividedDifference] using (hf z).hasDerivAt.continuousAt_div
  · exact entireDividedDifference_differentiableAt_of_ne f hf hz

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelPoleSubtracted {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    ℂ → ℂ := fun s ↦
  riemannZeta₀ s * siegelLProduct χ ψ s +
    entireDividedDifference (siegelLProduct χ ψ) 1 s

theorem siegelProduct_sub_pole_entire {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    Differentiable ℂ (siegelPoleSubtracted χ ψ) := by
  exact zetaRegularized_differentiable.mul (siegelLProduct_differentiable χ ψ hχ hψ hmul) |>.add
    (entireDividedDifference_differentiable _ _
      (siegelLProduct_differentiable χ ψ hχ hψ hmul))

theorem siegelPoleSubtracted_apply_of_ne {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelPoleSubtracted χ ψ s =
      riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1) := by
  rw [siegelPoleSubtracted, entireDividedDifference_apply_of_ne _ hs,
    siegelLProduct_one, riemannZeta_eq_pole_add_regularized hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelPoleSubtracted_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
            ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K := by
  obtain ⟨CriemannZeta, hCriemannZeta, hzeta⟩ := exists_riemannZeta_circle_bound
  refine ⟨(CriemannZeta + 2) * siegelResidueBoundConstant,
    mul_pos (by linarith) siegelResidueBoundConstant_pos, 4, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul s hs
  have hL := norm_siegelLProduct_le χ ψ hχ hψ hmul hs
  have hres := norm_siegelProductResidue_le χ ψ hχ hψ hmul
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [siegelPoleSubtracted_apply_of_ne χ ψ (siegelCauchyCircle_ne_one hs)]
  calc
    ‖riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1)‖
        ≤ ‖riemannZeta s * siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ / (s - 1)‖ := norm_sub_le _ _
    _ = ‖riemannZeta s‖ * ‖siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ‖ * ‖s - 1‖⁻¹ := by
      rw [norm_mul, norm_div, div_eq_mul_inv]
    _ ≤ CriemannZeta * (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) +
          (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) * 2 := by
      apply add_le_add
      · exact mul_le_mul (hzeta s hs) hL (norm_nonneg _) hCriemannZeta.le
      · exact mul_le_mul hres hinv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg siegelResidueBoundConstant_pos.le (pow_nonneg (by positivity) _))
    _ = ((CriemannZeta + 2) * siegelResidueBoundConstant) * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.ComplexAnalysis

noncomputable def taylorCoefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c / (n.factorial : ℂ)

theorem norm_taylorCoefficient_le {f : ℂ → ℂ} {c : ℂ} {R C : ℝ}
    (n : ℕ) (hR : 0 < R) (hf : Differentiable ℂ f)
    (hC : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ C) :
    ‖taylorCoefficient f c n‖ ≤ C / R ^ n := by
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf.diffContOnCl hC
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  rw [taylorCoefficient, norm_div]
  simp only [norm_natCast]
  calc
    ‖iteratedDeriv n f c‖ / n.factorial ≤
        (n.factorial * C / R ^ n) / n.factorial :=
      (div_le_div_iff_of_pos_right hfac).2 hderiv
    _ = C / R ^ n := by
      field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.ComplexAnalysis

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (siegelPoleSubtracted χ ψ) 2 m

theorem norm_siegelRegularCoefficient {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ =
      ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖ := by
  rw [siegelRegularCoefficient, norm_mul, norm_pow, norm_neg]
  have hone : ‖(1 : ℂ)‖ = 1 := by
    simpa only [Nat.cast_one] using Complex.norm_natCast 1
  rw [hone, one_pow, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelRegularCoefficient_le_of_circle_bound
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {C : ℝ} {K : ℕ}
    (hcircle : ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
      ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K)
    (m : ℕ) :
    ‖siegelRegularCoefficient χ ψ m‖ ≤
      C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  rw [norm_siegelRegularCoefficient]
  have hcauchy := BombieriVinogradov.ComplexAnalysis.norm_taylorCoefficient_le
    m (by norm_num : (0 : ℝ) < 3 / 2)
    (siegelProduct_sub_pole_entire χ ψ hχ hψ hmul)
    (fun z hz ↦ hcircle hz)
  calc
    ‖BombieriVinogradov.ComplexAnalysis.taylorCoefficient
        (siegelPoleSubtracted χ ψ) 2 m‖
        ≤ (C * ((N : ℝ) * (M : ℝ)) ^ K) / (3 / 2 : ℝ) ^ m := hcauchy
    _ = C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_coefficient_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ m : ℕ, ‖siegelRegularCoefficient χ ψ m‖ ≤
            C * ((N : ℝ) * (M : ℝ)) ^ K * (2 / 3 : ℝ) ^ m := by
  obtain ⟨C, hC, K, hcircle⟩ := siegelPoleSubtracted_circle_bound
  refine ⟨C, hC, K, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul m
  exact norm_siegelRegularCoefficient_le_of_circle_bound χ ψ hχ hψ hmul
    (hcircle χ ψ hχ hψ hmul) m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem hasSum_siegelRegularCoefficient {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (s : ℂ) :
    HasSum (fun m : ℕ => siegelRegularCoefficient chi psi m * (2 - s) ^ m)
      (siegelPoleSubtracted chi psi s) := by
  have h := Complex.hasSum_taylorSeries_of_entire
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul) 2 s
  refine HasSum.congr_fun h (fun m => ?_)
  unfold siegelRegularCoefficient BombieriVinogradov.ComplexAnalysis.taylorCoefficient
  simp only [smul_eq_mul]
  have hpow : (s - 2) ^ m = (-1 : ℂ) ^ m * (2 - s) ^ m := by
    rw [show s - 2 = -(2 - s) by ring, neg_pow]
  rw [hpow]
  field_simp [Nat.factorial_ne_zero]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourceCoefficient {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (m : ℕ) : ℂ :=
  (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
    (LSeries (siegelProductCoefficients chi psi)) 2 m

theorem siegelSourceCoefficient_nonneg {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) (m : ℕ) :
    0 ≤ siegelSourceCoefficient chi psi m := by
  have hsumm : LSeriesSummable (siegelProductCoefficients chi psi) (3 / 2 : ℂ) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  have habs : LSeries.abscissaOfAbsConv (siegelProductCoefficients chi psi) < (2 : ℝ) :=
    hsumm.abscissaOfAbsConv_le.trans_lt (by norm_num)
  have hderiv := LSeries.iteratedDeriv_alternating
    (siegelProductCoefficients_nonneg chi psi hchi hpsi) habs m
  have hfactorial : (0 : ℂ) ≤ m.factorial := by positivity
  simpa [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, mul_div_assoc] using
      div_nonneg hderiv hfactorial

theorem one_le_siegelSourceCoefficient_zero {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1) :
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 := by
  rw [siegelSourceCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient]
  simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [LSeries]
  have hsumm : Summable (LSeries.term (siegelProductCoefficients chi psi) 2) :=
    siegelProductCoefficients_LSeriesSummable chi psi (by norm_num)
  calc
    (1 : ℂ) = ∑ n ∈ {1}, LSeries.term (siegelProductCoefficients chi psi) 2 n := by
      simp [LSeries.term_def, siegelProductCoefficients_one]
    _ ≤ ∑' n, LSeries.term (siegelProductCoefficients chi psi) 2 n :=
      hsumm.sum_le_tsum {1} fun n _ =>
        LSeries.term_nonneg (siegelProductCoefficients_nonneg chi psi hchi hpsi n) 2

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem pole_source_coefficient (residue : ℂ) (m : ℕ) :
    (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
      (fun s : ℂ => residue / (s - 1)) 2 m = residue := by
  rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    show (fun s : ℂ => residue / (s - 1)) = fun s : ℂ => residue * (s - 1)⁻¹ by
      funext s
      rw [div_eq_mul_inv],
    iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  have hinv : deriv^[m] (fun s : ℂ => (s - 1)⁻¹) 2 =
      (-1 : ℂ) ^ m * m.factorial := by
    have h := congrFun (iter_deriv_inv_linear_sub m (1 : ℂ) 1) 2
    norm_num at h
    simpa using h
  rw [hinv]
  field_simp [Nat.factorial_ne_zero]
  have hsign : (((-1 : ℂ) ^ m) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, one_mul]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelSourceCoefficient_eq_regular_add_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) (m : ℕ) :
    siegelSourceCoefficient chi psi m =
      siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
  let halfPlane : Set ℂ := {s | 1 < s.re}
  have hopen : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have htwo : (2 : ℂ) ∈ halfPlane := by norm_num [halfPlane]
  have heq : halfPlane.EqOn (LSeries (siegelProductCoefficients chi psi))
      (fun s => siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)) := by
    intro s hs
    have hsone : s ≠ 1 := by
      intro h
      subst s
      norm_num [halfPlane] at hs
    rw [siegelProduct_LSeries_eq chi psi hs]
    change _ = siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1)
    rw [siegelPoleSubtracted_apply_of_ne chi psi hsone]
    rw [siegelLProduct]
    ring
  have hderiv := heq.iteratedDeriv_of_isOpen hopen m htwo
  have hregular : ContDiffAt ℂ m (siegelPoleSubtracted chi psi) 2 :=
    (siegelProduct_sub_pole_entire chi psi hchi hpsi hmul).contDiff.contDiffAt
  have hpole : ContDiffAt ℂ m
      (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 := by
    fun_prop (disch := norm_num)
  change iteratedDeriv m (LSeries (siegelProductCoefficients chi psi)) 2 =
    iteratedDeriv m
      (siegelPoleSubtracted chi psi +
        fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 at hderiv
  rw [iteratedDeriv_add hregular hpole] at hderiv
  rw [siegelSourceCoefficient, siegelRegularCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    BombieriVinogradov.ComplexAnalysis.taylorCoefficient, hderiv]
  calc
    (-1 : ℂ) ^ m *
          ((iteratedDeriv m (siegelPoleSubtracted chi psi) 2 +
            iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2) /
            (m.factorial : ℂ)) =
        (-1 : ℂ) ^ m *
            (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
          (-1 : ℂ) ^ m *
            (iteratedDeriv m (fun s : ℂ => siegelProductResidue chi psi / (s - 1)) 2 /
              (m.factorial : ℂ)) := by ring
    _ = (-1 : ℂ) ^ m *
          (iteratedDeriv m (siegelPoleSubtracted chi psi) 2 / (m.factorial : ℂ)) +
        siegelProductResidue chi psi := by
      have hpoleCoefficient := pole_source_coefficient (siegelProductResidue chi psi) m
      rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient] at hpoleCoefficient
      rw [hpoleCoefficient]

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.range cutoff, siegelSourceCoefficient chi psi m * (t : ℂ) ^ m

theorem one_le_siegelSourcePartialSum {N M : ℕ}
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    {cutoff : ℕ} (hcutoff : 0 < cutoff) {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℂ) ≤ siegelSourcePartialSum chi psi cutoff t := by
  calc
    (1 : ℂ) ≤ siegelSourceCoefficient chi psi 0 :=
      one_le_siegelSourceCoefficient_zero chi psi hchiSquare hpsiSquare
    _ = siegelSourceCoefficient chi psi 0 * (t : ℂ) ^ 0 := by simp
    _ ≤ ∑ m ∈ Finset.range cutoff,
        siegelSourceCoefficient chi psi m * (t : ℂ) ^ m := by
      exact Finset.single_le_sum
        (fun m _ => mul_nonneg
          (siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m)
          (pow_nonneg (by exact_mod_cast ht) m))
        (Finset.mem_range.mpr hcutoff)

theorem regularPartialSum_eq_source_sub_residue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.range cutoff,
        siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) =
      siegelSourcePartialSum chi psi cutoff t -
        siegelProductResidue chi psi * ∑ m ∈ Finset.range cutoff, (t : ℂ) ^ m := by
  rw [siegelSourcePartialSum]
  simp_rw [siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def regularCoefficientTail
    (a : ℕ → ℂ) (cutoff : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, a (cutoff + k) * (t : ℂ) ^ (cutoff + k)

theorem norm_regularCoefficientTail_le
    (a : ℕ → ℂ) {A t : ℝ} (cutoff : ℕ)
    (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht : t ≤ 9 / 8)
    (ha : ∀ m, ‖a m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    ‖regularCoefficientTail a cutoff t‖ ≤
      4 * A * (3 / 4 : ℝ) ^ cutoff := by
  have hterm (k : ℕ) :
      ‖a (cutoff + k) * (t : ℂ) ^ (cutoff + k)‖ ≤
        A * (3 / 4 : ℝ) ^ (cutoff + k) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      ‖a (cutoff + k)‖ * t ^ (cutoff + k) ≤
          (A * (2 / 3 : ℝ) ^ (cutoff + k)) * t ^ (cutoff + k) :=
        mul_le_mul_of_nonneg_right (ha _) (pow_nonneg ht0 _)
      _ = A * ((2 / 3 : ℝ) * t) ^ (cutoff + k) := by
        rw [mul_assoc, mul_pow]
      _ ≤ A * (3 / 4 : ℝ) ^ (cutoff + k) := by
        gcongr
        nlinarith
  have hgeom : HasSum (fun k : ℕ => (3 / 4 : ℝ) ^ k) 4 := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hmajor : HasSum (fun k : ℕ => A * (3 / 4 : ℝ) ^ (cutoff + k))
      (4 * A * (3 / 4 : ℝ) ^ cutoff) := by
    have h := hgeom.mul_left (A * (3 / 4 : ℝ) ^ cutoff)
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  exact tsum_of_norm_bounded hmajor hterm

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelProductValue {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  riemannZeta s * siegelLProduct chi psi s

theorem siegelProductValue_eq_regular_add_pole {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℂ} (hs : s ≠ 1) :
    siegelProductValue chi psi s =
      siegelPoleSubtracted chi psi s + siegelProductResidue chi psi / (s - 1) := by
  rw [siegelPoleSubtracted_apply_of_ne chi psi hs]
  unfold siegelProductValue
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_decomposition {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    (cutoff : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    siegelProductValue chi psi (1 - delta) =
      siegelSourcePartialSum chi psi cutoff (1 + delta) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta) -
          siegelProductResidue chi psi * ((1 + delta : ℝ) : ℂ) ^ cutoff / delta := by
  let s : ℂ := (1 - delta : ℝ)
  let t : ℝ := 1 + delta
  have hs : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    linarith
  have hexpansion := hasSum_siegelRegularCoefficient chi psi hchi hpsi hmul s
  have hsplit : siegelPoleSubtracted chi psi s =
      (∑ m ∈ Finset.range cutoff, siegelRegularCoefficient chi psi m * (t : ℂ) ^ m) +
        regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff t := by
    have hsum := hexpansion.summable.sum_add_tsum_nat_add cutoff
    rw [hexpansion.tsum_eq] at hsum
    have hst : (2 - s : ℂ) = t := by
      dsimp [s, t]
      push_cast
      ring
    rw [hst] at hsum
    simpa only [regularCoefficientTail, Nat.add_comm] using hsum.symm
  have hsdef : (1 : ℂ) - delta = s := by
    dsimp [s]
    push_cast
    rfl
  have htdef : 1 + delta = t := rfl
  rw [hsdef, htdef]
  rw [siegelProductValue_eq_regular_add_pole chi psi hs, hsplit]
  rw [regularPartialSum_eq_source_sub_residue chi psi hchi hpsi hmul]
  have ht : (t : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [t] at hre
    norm_num at hre
    linarith
  rw [geom_sum_eq ht]
  dsimp [s, t]
  push_cast
  field_simp
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_lower_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {A delta : ℝ} (hA : 0 ≤ A) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    {cutoff : ℕ} (hcutoff : 0 < cutoff)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤ A * (2 / 3 : ℝ) ^ m) :
    1 - (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta -
        4 * A * (3 / 4 : ℝ) ^ cutoff ≤
      (siegelProductValue chi psi (1 - delta)).re := by
  let partialSum := siegelSourcePartialSum chi psi cutoff (1 + delta)
  let tail := regularCoefficientTail (siegelRegularCoefficient chi psi) cutoff (1 + delta)
  have hpartialComplex : (1 : ℂ) ≤ partialSum :=
    one_le_siegelSourcePartialSum chi psi hchiSquare hpsiSquare hcutoff (by linarith)
  have hpartial : 1 ≤ partialSum.re := (Complex.le_def.mp hpartialComplex).1
  have htailNorm : ‖tail‖ ≤ 4 * A * (3 / 4 : ℝ) ^ cutoff :=
    norm_regularCoefficientTail_le (siegelRegularCoefficient chi psi) cutoff hA
      (by linarith) (by linarith) hcoeff
  have htailRe : -(4 * A * (3 / 4 : ℝ) ^ cutoff) ≤ tail.re := by
    exact (neg_le_neg htailNorm).trans ((abs_le.mp (Complex.abs_re_le_norm tail)).1)
  have hdecomp := congrArg Complex.re
    (siegelProductValue_decomposition chi psi hchi hpsi hmul cutoff hdelta)
  have hpowcast : (((1 + delta : ℝ) : ℂ) ^ cutoff) =
      (((1 + delta) ^ cutoff : ℝ) : ℂ) := by
    norm_cast
  have hbasecast : (1 : ℂ) + delta = ((1 + delta : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpowRe : ((1 + (delta : ℂ)) ^ cutoff).re = (1 + delta) ^ cutoff := by
    rw [hbasecast, hpowcast]
    rfl
  have hpowIm : ((1 + (delta : ℂ)) ^ cutoff).im = 0 := by
    rw [hbasecast, hpowcast]
    rfl
  have hpoleRe :
      (siegelProductResidue chi psi * (((1 + delta : ℝ) : ℂ) ^ cutoff) / delta).re =
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta := by
    simp
    rw [hpowRe, hpowIm]
    ring
  rw [Complex.sub_re, Complex.add_re, hpoleRe] at hdecomp
  change (siegelProductValue chi psi (1 - delta)).re =
      partialSum.re + tail.re -
        (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta at hdecomp
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

open Filter
open Topology

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_nonneg {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    0 ≤ siegelProductResidue chi psi := by
  obtain ⟨C, _hC, K, hbound⟩ := siegelProduct_coefficient_bound
  let A : ℝ := C * ((N : ℝ) * (M : ℝ)) ^ K
  have hregular : Tendsto (fun m => siegelRegularCoefficient chi psi m)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg (siegelRegularCoefficient chi psi m))
      (fun m => hbound chi psi hchi hpsi hmul m) ?_
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (show ‖(2 / 3 : ℝ)‖ < 1 by norm_num)
    have hconst : Tendsto (fun _ : ℕ => A) atTop (𝓝 A) := tendsto_const_nhds
    have hmulZero := hconst.mul hpow
    simpa [A] using hmulZero
  have hsource : Tendsto (fun m => siegelSourceCoefficient chi psi m)
      atTop (𝓝 (siegelProductResidue chi psi)) := by
    have hseq : (fun m => siegelSourceCoefficient chi psi m) =
        fun m => siegelRegularCoefficient chi psi m + siegelProductResidue chi psi := by
      funext m
      exact siegelSourceCoefficient_eq_regular_add_residue chi psi hchi hpsi hmul m
    rw [hseq]
    simpa using hregular.add_const (siegelProductResidue chi psi)
  exact ge_of_tendsto hsource <| Eventually.of_forall fun m =>
    siegelSourceCoefficient_nonneg chi psi hchiSquare hpsiSquare m

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelTruncationIndex (B Q : ℝ) (K : ℕ) : ℕ :=
  ⌈4 * Real.log (B * Q ^ K)⌉₊ + 1

theorem truncationIndex_lower {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    4 * Real.log (B * Q ^ K) < siegelTruncationIndex B Q K := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  have hceil := Nat.le_ceil (4 * Real.log (B * Q ^ K))
  exact hceil.trans_lt (lt_add_one _)

theorem truncationIndex_upper {B Q : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) :
    (siegelTruncationIndex B Q K : ℝ) <
      4 * Real.log (B * Q ^ K) + 2 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQpow : 1 ≤ Q ^ K := one_le_pow₀ hQ
  have hX : 1 ≤ B * Q ^ K :=
    hB.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hQpow hB0)
  have hlog : 0 ≤ 4 * Real.log (B * Q ^ K) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hX)
  unfold siegelTruncationIndex
  rw [Nat.cast_add, Nat.cast_one]
  linarith [Nat.ceil_lt_add_one hlog]

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationPoleGrowth {B Q delta : ℝ} {K : ℕ}
    (hB : 1 ≤ B) (hQ : 1 ≤ Q) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    (1 + delta) ^ siegelTruncationIndex B Q K ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hXpos : 0 < X := mul_pos (zero_lt_one.trans_le hB) (pow_pos hQpos K)
  have hcutoff := truncationIndex_upper (K := K) hB hQ
  have hmul : (cutoff : ℝ) * delta ≤
      (4 * Real.log X + 2) * delta :=
    mul_le_mul_of_nonneg_right hcutoff.le hdelta0
  have hexponent : (cutoff : ℝ) * delta ≤ 4 * delta * Real.log X + 2 := by
    calc
      (cutoff : ℝ) * delta ≤ (4 * Real.log X + 2) * delta := hmul
      _ ≤ 4 * delta * Real.log X + 2 := by nlinarith
  have hbase : 1 + delta ≤ Real.exp delta := by
    simpa only [add_comm] using Real.add_one_le_exp delta
  have hbase0 : 0 ≤ 1 + delta := by linarith
  have hpow : (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := by
    exact pow_le_pow_left₀ hbase0 hbase cutoff
  calc
    (1 + delta) ^ cutoff ≤ (Real.exp delta) ^ cutoff := hpow
    _ = Real.exp ((cutoff : ℝ) * delta) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * delta * Real.log X + 2) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp 2 * X ^ (4 * delta) := by
      rw [Real.exp_add, Real.rpow_def_of_pos hXpos]
      have harg : 4 * delta * Real.log X = Real.log X * (4 * delta) := by ring
      rw [harg]
      ring
    _ ≤ Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by
      have hBrpow : B ^ (4 * delta) ≤ B := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hB (by nlinarith : 4 * delta ≤ 1)
      have hQrpow : (Q ^ K) ^ (4 * delta) = Q ^ ((4 * K : ℝ) * delta) := by
        calc
          (Q ^ K) ^ (4 * delta) = (Q ^ (4 * delta)) ^ K :=
            (Real.rpow_pow_comm hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * delta) * K) :=
            (Real.rpow_mul_natCast hQ0 (4 * delta) K).symm
          _ = Q ^ ((4 * K : ℝ) * delta) := by
            congr 1
            ring
      dsimp [X]
      rw [Real.mul_rpow hB0 (pow_nonneg hQ0 K), hQrpow]
      have hQnonneg : 0 ≤ Q ^ ((4 * K : ℝ) * delta) := Real.rpow_nonneg hQ0 _
      calc
        Real.exp 2 * (B ^ (4 * delta) * Q ^ ((4 * K : ℝ) * delta)) ≤
            Real.exp 2 * (B * Q ^ ((4 * K : ℝ) * delta)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hBrpow hQnonneg) (Real.exp_nonneg 2)
        _ = Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := by ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncationTail_lt_half {A B Q : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 := by
  let cutoff := siegelTruncationIndex B Q K
  let X := B * Q ^ K
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQpowpos : 0 < Q ^ K := pow_pos hQpos K
  have hXpos : 0 < X := mul_pos hBpos hQpowpos
  have hbase : Real.log (3 / 4 : ℝ) ≤ -1 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (3 / 4 : ℝ) by norm_num)
    norm_num at h ⊢
    exact h
  have hcutoff : 4 * Real.log X < (cutoff : ℝ) := by
    exact truncationIndex_lower hB hQ
  have hcutoff0 : 0 ≤ (cutoff : ℝ) := by positivity
  have hexponent : Real.log (3 / 4 : ℝ) * (cutoff : ℝ) < -Real.log X := by
    calc
      Real.log (3 / 4 : ℝ) * (cutoff : ℝ) ≤
          (-1 / 4 : ℝ) * (cutoff : ℝ) :=
        mul_le_mul_of_nonneg_right hbase hcutoff0
      _ < -Real.log X := by nlinarith
  have hpow : (3 / 4 : ℝ) ^ cutoff < 1 / X := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    have h := Real.exp_lt_exp.mpr hexponent
    rw [Real.exp_neg, Real.exp_log hXpos] at h
    simpa only [inv_eq_one_div] using h
  rcases hA.eq_or_lt with rfl | hApos
  · norm_num
  · have hpref : 0 < 4 * A * Q ^ K := mul_pos (mul_pos (by norm_num) hApos) hQpowpos
    calc
      4 * A * Q ^ K * (3 / 4 : ℝ) ^ cutoff <
          4 * A * Q ^ K * (1 / X) := mul_lt_mul_of_pos_left hpow hpref
      _ = 4 * A / B := by
        dsimp [X]
        field_simp
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hBpos]
        nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelTruncation_spec {A B Q delta : ℝ} {K : ℕ}
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hAB : 8 * A ≤ B) (hQ : 1 ≤ Q)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8) :
    4 * A * Q ^ K * (3 / 4 : ℝ) ^ siegelTruncationIndex B Q K < 1 / 2 ∧
      (1 + delta) ^ siegelTruncationIndex B Q K ≤
        Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) :=
  ⟨truncationTail_lt_half hA hB hAB hQ,
    truncationPoleGrowth hB hQ hdelta0 hdelta⟩

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos_of_coefficient_bound {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {C B Q delta : ℝ} {K : ℕ}
    (hC : 0 < C) (hB : 1 ≤ B) (hCB : 8 * C ≤ B) (hQ : 1 ≤ Q)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1 / 8)
    (hcoeff : ∀ m, ‖siegelRegularCoefficient chi psi m‖ ≤
      C * Q ^ K * (2 / 3 : ℝ) ^ m)
    (hsmall : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
      Q ^ ((4 * K : ℝ) * delta) < delta) :
    0 < (siegelProductValue chi psi (1 - delta)).re := by
  let cutoff := siegelTruncationIndex B Q K
  have hcutoff : 0 < cutoff := by
    dsimp [cutoff, siegelTruncationIndex]
    omega
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueRe : 0 ≤ (siegelProductResidue chi psi).re :=
    (Complex.le_def.mp hresidue).1
  have htruncation := siegelTruncation_spec (K := K)
    hC.le hB hCB hQ hdelta.le hdeltaUpper
  have htail : 4 * (C * Q ^ K) * (3 / 4 : ℝ) ^ cutoff < 1 / 2 := by
    simpa only [mul_assoc] using htruncation.1
  have hpoleGrowth : (1 + delta) ^ cutoff ≤
      Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta) := htruncation.2
  have hpoleNumerator :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff ≤
        (siegelProductResidue chi psi).re *
          (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) :=
    mul_le_mul_of_nonneg_left hpoleGrowth hresidueRe
  have hpole :
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta < 1 / 2 := by
    calc
      (siegelProductResidue chi psi).re * (1 + delta) ^ cutoff / delta ≤
          (siegelProductResidue chi psi).re *
            (Real.exp 2 * B * Q ^ ((4 * K : ℝ) * delta)) / delta :=
        div_le_div_of_nonneg_right hpoleNumerator hdelta.le
      _ < 1 / 2 := by
        rw [div_lt_iff₀ hdelta]
        ring_nf at hsmall ⊢
        linarith
  have hlower := siegelProductValue_re_lower_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul (mul_nonneg hC.le (pow_nonneg (zero_le_one.trans hQ) K))
    hdelta hdeltaUpper hcutoff hcoeff
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProduct_pos :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
        chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
          DirichletCharacter.mul chi psi ≠ 1 →
          ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
            C * ‖siegelProductResidue chi psi‖ <
              (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
              0 < (siegelProductValue chi psi s).re := by
  obtain ⟨C0, hC0, K, hcoeff⟩ := siegelProduct_coefficient_bound
  let B : ℝ := max 1 (8 * C0)
  have hB : 1 ≤ B := le_max_left _ _
  have hC0B : 8 * C0 ≤ B := le_max_right _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨2 * (Real.exp 2 * B), mul_pos (by norm_num) (mul_pos (Real.exp_pos 2) hBpos),
    4 * K, ?_⟩
  intro N M instN instM instLcm chi psi hchiSquare hpsiSquare hchi hpsi hmul s hsLower hsUpper hsmall
  let Q : ℝ := (N : ℝ) * (M : ℝ)
  let delta : ℝ := 1 - s
  have hdelta : 0 < delta := sub_pos.mpr hsUpper
  have hdeltaUpper : delta ≤ 1 / 8 := by
    dsimp [delta]
    linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_le_mul hN hM (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ N)]
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hQ0 : 0 ≤ Q := hQpos.le
  have hresidue := siegelProductResidue_nonneg chi psi hchiSquare hpsiSquare hchi hpsi hmul
  have hresidueParts := Complex.le_def.mp hresidue
  have hnormResidue : ‖siegelProductResidue chi psi‖ =
      (siegelProductResidue chi psi).re := by
    have habs := Complex.abs_re_eq_norm.mpr hresidueParts.2.symm
    rw [abs_of_nonneg hresidueParts.1] at habs
    exact habs.symm
  have hsourceSmall :
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
        Q ^ ((4 * K : ℝ) * delta) < delta := by
    have hsmall' : 2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re <
        delta * Q ^ (-((4 * K : ℝ) * delta)) := by
      simpa [Q, delta, hnormResidue] using hsmall
    have hpowPos : 0 < Q ^ ((4 * K : ℝ) * delta) := Real.rpow_pos_of_pos hQpos _
    calc
      2 * (Real.exp 2 * B) * (siegelProductResidue chi psi).re *
          Q ^ ((4 * K : ℝ) * delta) <
        (delta * Q ^ (-((4 * K : ℝ) * delta))) *
          Q ^ ((4 * K : ℝ) * delta) :=
        mul_lt_mul_of_pos_right hsmall' hpowPos
      _ = delta := by
        rw [Real.rpow_neg hQ0]
        field_simp
  have hpositive := siegelProduct_pos_of_coefficient_bound chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hC0 hB hC0B hQ hdelta hdeltaUpper
    (fun m => by simpa [Q, mul_assoc] using hcoeff chi psi hchi hpsi hmul m) hsourceSmall
  simpa [delta] using hpositive

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelPositivityPair (C : ℝ) (D : ℕ) : Prop :=
  0 < C ∧
    ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
      (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M),
      chi ^ 2 = 1 → psi ^ 2 = 1 → chi ≠ 1 → psi ≠ 1 →
        DirichletCharacter.mul chi psi ≠ 1 →
        ∀ s : ℝ, 7 / 8 ≤ s → s < 1 →
          C * ‖siegelProductResidue chi psi‖ <
            (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) →
            0 < (siegelProductValue chi psi s).re

theorem exists_siegelPositivityPair :
    ∃ C : ℝ, ∃ D : ℕ, IsSiegelPositivityPair C D := by
  obtain ⟨C, hC, D, hpos⟩ := siegelProduct_pos
  exact ⟨C, D, hC, hpos⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductResidue_lower_of_nonpos {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * ‖siegelProductResidue chi psi‖ := by
  apply le_of_not_gt
  intro hsmall
  have hpositive := hpair.2 chi psi hchiSquare hpsiSquare hchi hpsi hmul
    s hsLower hsUpper hsmall
  linarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelProductResidue_le_log {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : chi ≠ 1) (hmul : DirichletCharacter.mul chi psi ≠ 1) :
    ‖siegelProductResidue chi psi‖ ≤
      characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by
  have hchiBound := norm_LFunction_one_le_log chi hchi
  have hmulBound := norm_LFunction_one_le_log (DirichletCharacter.mul chi psi) hmul
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlogN : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have hfirstUpper : 0 ≤
      (characterLLogBoundConstant * (1 + Real.log N)) * ‖psi.LFunction 1‖ :=
    mul_nonneg (mul_nonneg characterLLogBoundConstant_pos.le hlogN) (norm_nonneg _)
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖chi.LFunction 1‖ * ‖psi.LFunction 1‖ *
        ‖(DirichletCharacter.mul chi psi).LFunction 1‖ ≤
      (characterLLogBoundConstant * (1 + Real.log N)) *
        ‖psi.LFunction 1‖ *
          (characterLLogBoundConstant * (1 + Real.log (N.lcm M))) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hchiBound (norm_nonneg _)) hmulBound
        (norm_nonneg _) hfirstUpper
    _ = characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖ := by ring

theorem targetLValue_transfer {C : ℝ} {D : ℕ}
    (hpair : IsSiegelPositivityPair C D)
    {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1)
    (hmul : DirichletCharacter.mul chi psi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnonpos : (siegelProductValue chi psi s).re ≤ 0) :
    (1 - s) * ((N : ℝ) * (M : ℝ)) ^ (-(D : ℝ) * (1 - s)) ≤
      C * (characterLLogBoundConstant ^ 2 * (1 + Real.log N) *
        (1 + Real.log (N.lcm M)) * ‖psi.LFunction 1‖) := by
  exact (siegelProductResidue_lower_of_nonpos hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsLower hsUpper hnonpos).trans
      (mul_le_mul_of_nonneg_left (norm_siegelProductResidue_le_log chi psi hchi hmul)
        hpair.1.le)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelLargeLevelDenominator
    (C : ℝ) (N : ℕ) (delta : ℝ) : ℝ :=
  C * characterLLogBoundConstant ^ 2 * (1 + Real.log N) * (1 + delta⁻¹)

theorem siegelLargeLevelDenominator_pos {C delta : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 0 < N) (hdelta : 0 < delta) :
    0 < siegelLargeLevelDenominator C N delta := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < 1 + Real.log N := by
    linarith [Real.log_nonneg hNreal]
  have hinverse : 0 < 1 + delta⁻¹ := by
    have : 0 < delta⁻¹ := inv_pos.mpr hdelta
    linarith
  unfold siegelLargeLevelDenominator
  exact mul_pos (mul_pos (mul_pos hC (pow_pos characterLLogBoundConstant_pos 2)) hlog)
    hinverse

noncomputable def siegelLargeLevelConstant
    (C epsilon s : ℝ) (N : ℕ) : ℝ :=
  ((1 - s) / siegelLargeLevelDenominator C N (epsilon / 2)) *
    (N : ℝ) ^ (-epsilon)

theorem siegelLargeLevelConstant_pos {C epsilon s : ℝ} {N : ℕ}
    (hC : 0 < C) (hepsilon : 0 < epsilon) (hN : 0 < N) (hs : s < 1) :
    0 < siegelLargeLevelConstant C epsilon s N := by
  have hdenominator := siegelLargeLevelDenominator_pos hC hN
    (div_pos hepsilon zero_lt_two)
  unfold siegelLargeLevelConstant
  exact mul_pos (div_pos (sub_pos.mpr hs) hdenominator)
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) (-epsilon))

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem one_add_log_le_rpow_mul {x delta : ℝ}
    (hx : 1 ≤ x) (hdelta : 0 < delta) :
    1 + Real.log x ≤ (1 + delta⁻¹) * x ^ delta := by
  have hpow : 1 ≤ x ^ delta := by
    simpa using Real.rpow_le_rpow zero_le_one hx hdelta.le
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hx) hdelta
  calc
    1 + Real.log x ≤ x ^ delta + x ^ delta / delta := add_le_add hpow hlog
    _ = (1 + delta⁻¹) * x ^ delta := by
      rw [div_eq_mul_inv]
      ring

theorem one_add_log_lcm_le_rpow_mul {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) {delta : ℝ} (hdelta : 0 < delta) :
    1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
  have hmul : 0 < N * M := Nat.mul_pos hN hM
  have hlcmNat : N.lcm M ≤ N * M :=
    Nat.le_of_dvd hmul (Nat.lcm_dvd_mul N M)
  have hlcm : (0 : ℝ) < N.lcm M := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hN.ne' hM.ne')
  have hlcmMul : (N.lcm M : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast hlcmNat
  have hproduct : (1 : ℝ) ≤ (N * M : ℕ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmul.ne'
  calc
    1 + Real.log (N.lcm M) ≤ 1 + Real.log (N * M : ℕ) := by
      simpa [add_comm] using add_le_add_left (Real.log_le_log hlcm hlcmMul) 1
    _ ≤ (1 + delta⁻¹) * (N * M : ℕ) ^ delta :=
      one_add_log_le_rpow_mul hproduct hdelta
    _ = (1 + delta⁻¹) * ((N : ℝ) * (M : ℝ)) ^ delta := by
      norm_num

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem weighted_rpow_transfer {prefactor bound base exponent delta epsilon value : ℝ}
    (hprefactor : 0 < prefactor) (hbound : 0 < bound) (hbase : 1 ≤ base)
    (hsum : exponent + delta ≤ epsilon)
    (hweighted : prefactor * base ^ (-exponent) ≤
      bound * base ^ delta * value) :
    (prefactor / bound) * base ^ (-epsilon) ≤ value := by
  have hbasePos : 0 < base := zero_lt_one.trans_le hbase
  have hpowerDelta : 0 < base ^ delta := Real.rpow_pos_of_pos hbasePos delta
  have hdenominator : 0 < bound * base ^ delta := mul_pos hbound hpowerDelta
  have hdivided :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) ≤ value := by
    rw [div_le_iff₀ hdenominator]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hquotient :
      (prefactor * base ^ (-exponent)) / (bound * base ^ delta) =
        (prefactor / bound) * base ^ (-(exponent + delta)) := by
    rw [show -(exponent + delta) = -exponent + -delta by ring,
      Real.rpow_add hbasePos, Real.rpow_neg hbasePos.le]
    field_simp
    rw [← Real.rpow_add hbasePos]
    norm_num
  have hpower : base ^ (-epsilon) ≤ base ^ (-(exponent + delta)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  calc
    (prefactor / bound) * base ^ (-epsilon) ≤
        (prefactor / bound) * base ^ (-(exponent + delta)) :=
      mul_le_mul_of_nonneg_left hpower (div_nonneg hprefactor.le hbound.le)
    _ = (prefactor * base ^ (-exponent)) / (bound * base ^ delta) :=
      hquotient.symm
    _ ≤ value := hdivided

end BombieriVinogradov.SiegelWalfisz

end

section

open Filter Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem riemannZeta_im_real (s : ℝ) : (riemannZeta s).im = 0 := by
  have hsym := riemannZeta_conj (s : ℂ)
  have him := congrArg Complex.im hsym
  simp at him
  linarith

theorem exists_riemannZeta_neg_left :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ s : ℝ, 1 - eta < s → s < 1 → (riemannZeta s).re < 0 := by
  have hofReal : Tendsto (fun s : ℝ ↦ (s : ℂ))
      (nhdsWithin 1 (Iio 1)) (nhdsWithin 1 ({1}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hsne : s ≠ 1 := ne_of_lt (Set.mem_Iio.mp hs)
      change (s : ℂ) ≠ 1
      exact_mod_cast hsne
  have hresidue : Tendsto
      (fun s : ℝ ↦ (((s : ℂ) - 1) * riemannZeta s).re)
      (nhdsWithin 1 (Iio 1)) (nhds 1) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp
      (riemannZeta_residue_one.comp hofReal) using 1 <;>
        simp [Function.comp_def]
  have heventually : ∀ᶠ s : ℝ in nhdsWithin 1 (Iio 1),
      0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hresidue (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhdsWithin_iff.mp heventually
  refine ⟨eta, heta, ?_⟩
  intro s hsLower hsUpper
  have hdist : dist s 1 < eta := by
    rw [Real.dist_eq]
    rw [abs_of_nonpos (sub_nonpos.mpr hsUpper.le)]
    linarith
  have hproduct : 0 < (((s : ℂ) - 1) * riemannZeta s).re :=
    hball ⟨hdist, hsUpper⟩
  have him := riemannZeta_im_real s
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.sub_im, Complex.ofReal_im, Complex.one_im, zero_mul,
    sub_zero] at hproduct
  nlinarith

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_siegelComparisonPoint {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ s : ℝ, lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧ (riemannZeta s).re < 0 := by
  obtain ⟨eta, heta, hzeta⟩ := exists_riemannZeta_neg_left
  let s := max lower (1 - eta / 2)
  have hlowerS : lower ≤ s := le_max_left _ _
  have hsevenS : 7 / 8 ≤ s := hlower.trans hlowerS
  have hsUpper : s < 1 := by
    apply max_lt hupper
    linarith
  have hetaS : 1 - eta < s := by
    have : 1 - eta < 1 - eta / 2 := by linarith
    exact this.trans_le (le_max_right _ _)
  exact ⟨s, hlowerS, hsevenS, hsUpper, hzeta s hetaS hsUpper⟩

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem real_mem_siegelAnalyticDomain {s : ℝ} (hsLower : 7 / 8 ≤ s)
    (hsUpper : s ≤ 1) : (s : ℂ) ∈ siegelAnalyticDomain := by
  rw [siegelAnalyticDomain, Metric.mem_ball, Complex.dist_eq]
  have hnonpos : s - 2 ≤ 0 := by linarith
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos hnonpos]
  norm_num at hsLower ⊢
  linarith

private theorem characterLBlock_im_eq_zero_bv675 {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    (k : ℕ) (s : ℝ) : (characterLBlock chi k s).im = 0 := by
  rw [characterLBlock, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hchiSquare j with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast (k * N + j.val),
      ← Complex.ofReal_cpow (Nat.cast_nonneg (k * N + j.val)) (-s)]
    simp

theorem quadraticLFunction_im_eq_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hs : (s : ℂ) ∈ siegelAnalyticDomain) :
    (chi.LFunction s).im = 0 := by
  have hsum : Summable (fun k : ℕ ↦ characterLBlock chi k s) := by
    apply Summable.of_norm
    exact (characterLBlockMajorant_summable N).of_nonneg_of_le
      (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs
  rw [LFunction_eq_characterLBlockSeries chi hchi hs, characterLBlockSeries,
    Complex.im_tsum hsum]
  convert tsum_zero with k
  exact characterLBlock_im_eq_zero_bv675 chi hchiSquare k s

end BombieriVinogradov.SiegelWalfisz

end

section

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 → chi.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  let f : ℝ → ℝ := fun t ↦ (chi.LFunction t).re
  have hfcont : Continuous f := by
    exact Complex.continuous_re.comp
      ((chi.differentiable_LFunction hchi).continuous.comp Complex.continuous_ofReal)
  have hone : 0 < f 1 := quadraticLFunction_one_re_pos chi hchiSquare hchi
  by_contra hnot
  have himS := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hfs_ne : f s ≠ 0 := by
    intro hfs
    apply hnozero s le_rfl hsUpper.le
    apply Complex.ext
    · simpa [f] using hfs
    · simpa using himS
  have hfsNeg : f s < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hfs_ne
  have hzeroMem : 0 ∈ Icc (f s) (f 1) := ⟨hfsNeg.le, hone.le⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hsUpper.le hfcont.continuousOn hzeroMem
  have himT := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain (hsLower.trans ht.1) ht.2)
  apply hnozero t ht.1 ht.2
  apply Complex.ext
  · simpa [f] using hft
  · simpa using himT

end BombieriVinogradov.SiegelWalfisz

end

section

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

theorem quadraticLFunction_re_pos_of_primitive_no_zero {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchiSquare : chi ^ 2 = 1) (hchi : chi ≠ 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hnozero : ∀ t : ℝ, s ≤ t → t ≤ 1 →
      chi.primitiveCharacter.LFunction t ≠ 0) :
    0 < (chi.LFunction s).re := by
  have hprimitiveNe := primitiveCharacter_ne_one chi hchi
  have hprimitiveSquare := primitiveCharacter_sq_eq_one chi hchiSquare
  have hprimitivePos := quadraticLFunction_re_pos_of_no_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe hsLower hsUpper hnozero
  have hcorrection := characterLevelCorrection_pos chi hchiSquare
    (show 0 < s by linarith)
  have hcorrectionParts := Complex.lt_def.mp hcorrection
  have hprimitiveIm := quadraticLFunction_im_eq_zero chi.primitiveCharacter
    hprimitiveSquare hprimitiveNe
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  rw [LFunction_eq_primitive_mul_correction chi hchi, Complex.mul_re]
  rw [hprimitiveIm]
  norm_num
  exact mul_pos hprimitivePos (by simpa using hcorrectionParts.1)

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_re_eq_product {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1)
    (hchi : Ne chi 1) (hpsi : Ne psi 1)
    (hmul : Ne (DirichletCharacter.mul chi psi) 1)
    {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1) :
    (siegelProductValue chi psi s).re =
      (riemannZeta s).re * (chi.LFunction s).re * (psi.LFunction s).re *
        ((DirichletCharacter.mul chi psi).LFunction s).re := by
  have hmulSquare := crossLevelMul_sq_eq_one chi psi hchiSquare hpsiSquare
  have hzetaIm := riemannZeta_im_real s
  have hchiIm := quadraticLFunction_im_eq_zero chi hchiSquare hchi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hpsiIm := quadraticLFunction_im_eq_zero psi hpsiSquare hpsi
    (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  have hmulIm := quadraticLFunction_im_eq_zero (DirichletCharacter.mul chi psi)
    hmulSquare hmul (real_mem_siegelAnalyticDomain hsLower hsUpper.le)
  simp only [siegelProductValue, siegelLProduct, Complex.mul_re, Complex.mul_im,
    hzetaIm, hchiIm, hpsiIm, hmulIm, mul_zero, zero_mul, add_zero, sub_zero]
  ring

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def PrimitiveQuadraticZeroFreeFrom (s : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
    DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 -> Ne chi 1 ->
      ∀ t : ℝ, s ≤ t -> t ≤ 1 -> Ne (chi.LFunction t) 0

theorem PrimitiveQuadraticZeroFreeFrom.mono {lower s : ℝ}
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom lower) (h : lower ≤ s) :
    PrimitiveQuadraticZeroFreeFrom s := by
  intro N _ chi hprimitive hsquare hne t hst ht
  exact hzeroFree N chi hprimitive hsquare hne t (h.trans hst) ht

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelProductValue_nonpos_of_left_zero {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    {s : ℝ} (hzero : chi.LFunction s = 0) :
    (siegelProductValue chi psi s).re ≤ 0 := by
  simp [siegelProductValue, siegelLProduct, hzero]

theorem quadraticCharacterFour_product_nonpos_of_zeroFree {M : ℕ}
    [NeZero M] [NeZero ((4 : ℕ).lcm M)]
    (psi : DirichletCharacter ℂ M)
    (hpsiPrimitive : DirichletCharacter.IsPrimitive psi)
    (hpsiSquare : psi ^ 2 = 1) (hpsi : Ne psi 1)
    (hM : 4 < M) {s : ℝ} (hsLower : 7 / 8 ≤ s) (hsUpper : s < 1)
    (hzeta : (riemannZeta s).re < 0)
    (hzeroFree : PrimitiveQuadraticZeroFreeFrom s) :
    (siegelProductValue quadraticCharacterFour psi s).re ≤ 0 := by
  have hlevels : Ne 4 M := Ne.symm (Nat.ne_of_gt hM)
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne quadraticCharacterFour psi
    quadraticCharacterFour_isPrimitive hpsiPrimitive hlevels
  have hmulSquare := crossLevelMul_sq_eq_one quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare
  have hfourNoZero := hzeroFree 4 quadraticCharacterFour
    quadraticCharacterFour_isPrimitive quadraticCharacterFour_sq
      quadraticCharacterFour_ne_one
  have hfourPos := quadraticLFunction_re_pos_of_no_zero quadraticCharacterFour
    quadraticCharacterFour_sq quadraticCharacterFour_ne_one hsLower hsUpper hfourNoZero
  have hpsiNoZero := hzeroFree M psi hpsiPrimitive hpsiSquare hpsi
  have hpsiPos := quadraticLFunction_re_pos_of_no_zero psi hpsiSquare hpsi
    hsLower hsUpper hpsiNoZero
  let _ : NeZero (DirichletCharacter.mul quadraticCharacterFour psi).conductor :=
    ⟨(DirichletCharacter.mul quadraticCharacterFour psi).conductor_ne_zero⟩
  have hmulPrimitiveSquare := primitiveCharacter_sq_eq_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare
  have hmulPrimitiveNe := primitiveCharacter_ne_one
    (DirichletCharacter.mul quadraticCharacterFour psi) hmul
  have hmulPrimitiveNoZero := hzeroFree
    (DirichletCharacter.mul quadraticCharacterFour psi).conductor
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter
    (DirichletCharacter.mul quadraticCharacterFour psi).primitiveCharacter_isPrimitive
    hmulPrimitiveSquare hmulPrimitiveNe
  have hmulPos := quadraticLFunction_re_pos_of_primitive_no_zero
    (DirichletCharacter.mul quadraticCharacterFour psi) hmulSquare hmul
      hsLower hsUpper hmulPrimitiveNoZero
  rw [siegelProductValue_re_eq_product quadraticCharacterFour psi
    quadraticCharacterFour_sq hpsiSquare quadraticCharacterFour_ne_one hpsi hmul
      hsLower hsUpper]
  exact (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hzeta hfourPos) hpsiPos)
      hmulPos).le

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

def IsSiegelSeed (lower : ℝ) (N : ℕ) (chi : DirichletCharacter ℂ N)
    (s : ℝ) : Prop :=
  0 < N ∧ DirichletCharacter.IsPrimitive chi ∧ chi ^ 2 = 1 ∧ Ne chi 1 ∧
    lower ≤ s ∧ 7 / 8 ≤ s ∧ s < 1 ∧
      ∀ (M : ℕ) [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (psi : DirichletCharacter ℂ M), N < M ->
          DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
            (siegelProductValue chi psi s).re ≤ 0

theorem exists_siegelSeed {lower : ℝ}
    (hlower : 7 / 8 ≤ lower) (hupper : lower < 1) :
    ∃ (N : ℕ) (chi : DirichletCharacter ℂ N) (s : ℝ),
      IsSiegelSeed lower N chi s := by
  by_cases hzeroFree : PrimitiveQuadraticZeroFreeFrom lower
  · obtain ⟨s, hlowerS, hsevenS, hsUpper, hzeta⟩ :=
      exists_siegelComparisonPoint hlower hupper
    have hzeroFreeS := hzeroFree.mono hlowerS
    refine ⟨4, quadraticCharacterFour, s, ?_⟩
    refine ⟨by norm_num, quadraticCharacterFour_isPrimitive,
      quadraticCharacterFour_sq, quadraticCharacterFour_ne_one,
      hlowerS, hsevenS, hsUpper, ?_⟩
    intro M _ _ _ psi hM hpsiPrimitive hpsiSquare hpsi
    exact quadraticCharacterFour_product_nonpos_of_zeroFree psi hpsiPrimitive
      hpsiSquare hpsi hM hsevenS hsUpper hzeta hzeroFreeS
  · rw [PrimitiveQuadraticZeroFreeFrom] at hzeroFree
    push Not at hzeroFree
    obtain ⟨N, hN, chi, hprimitive, hchiSquare, hchi, s,
      hlowerS, hsOne, hzero⟩ := hzeroFree
    let _ : NeZero N := hN
    have hsUpper : s < 1 := by
      apply lt_of_le_of_ne hsOne
      intro hs
      apply chi.LFunction_apply_one_ne_zero hchi
      simpa [hs] using hzero
    refine ⟨N, chi, s, ?_⟩
    refine ⟨NeZero.pos N, hprimitive, hchiSquare, hchi,
      hlowerS, hlower.trans hlowerS, hsUpper, ?_⟩
    intro M _ _ _ psi _ _ _ _
    exact siegelProductValue_nonpos_of_left_zero chi psi hzero

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound_largeLevel {C epsilon : ℝ} {D N : ℕ}
    {chi : DirichletCharacter ℂ N} {s : ℝ}
    (hpair : IsSiegelPositivityPair C D) (hepsilon : 0 < epsilon)
    (hseed : IsSiegelSeed (siegelLowerEndpoint epsilon D) N chi s) :
    ∀ (M : ℕ) [NeZero M] [NeZero (N.lcm M)]
      (psi : DirichletCharacter ℂ M), N < M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          siegelLargeLevelConstant C epsilon s N * (M : ℝ) ^ (-epsilon) ≤
            (psi.LFunction 1).re := by
  obtain ⟨hN, hchiPrimitive, hchiSquare, hchi, hlowerS,
    hsevenS, hsUpper, hseedNonpos⟩ := hseed
  let _ : NeZero N := ⟨hN.ne'⟩
  intro M _ _ psi hNM hpsiPrimitive hpsiSquare hpsi
  have hM : 0 < M := NeZero.pos M
  have hmul := crossLevelMul_ne_one_of_primitive_of_ne chi psi
    hchiPrimitive hpsiPrimitive (Ne.symm (Nat.ne_of_gt hNM))
  have hnonpos := hseedNonpos M psi hNM hpsiPrimitive hpsiSquare hpsi
  have hraw := targetLValue_transfer hpair chi psi hchiSquare hpsiSquare
    hchi hpsi hmul hsevenS hsUpper hnonpos
  have hnorm := norm_quadraticLFunction_one_eq_re psi hpsiSquare hpsi
  rw [hnorm] at hraw
  have hvaluePos := quadraticLFunction_one_re_pos psi hpsiSquare hpsi
  let delta : ℝ := epsilon / 2
  let base : ℝ := (N : ℝ) * (M : ℝ)
  let fixed : ℝ := C * characterLLogBoundConstant ^ 2 * (1 + Real.log N)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hbase : 1 ≤ base := by
    dsimp [base]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hM.ne')
  have hfixed : 0 < fixed := by
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 < 1 + Real.log N := by
      linarith [Real.log_nonneg hNreal]
    dsimp [fixed]
    exact mul_pos (mul_pos hpair.1 (pow_pos characterLLogBoundConstant_pos 2)) hlog
  have hlogBound : 1 + Real.log (N.lcm M) ≤
      (1 + delta⁻¹) * base ^ delta := by
    simpa [delta, base] using one_add_log_lcm_le_rpow_mul hN hM hdelta
  have hscaled : fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re ≤
      fixed * ((1 + delta⁻¹) * base ^ delta) * (psi.LFunction 1).re :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogBound hfixed.le) hvaluePos.le
  have hweighted :
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
        siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
    calc
      (1 - s) * base ^ (-((D : ℝ) * (1 - s))) ≤
          fixed * (1 + Real.log (N.lcm M)) * (psi.LFunction 1).re := by
        simpa [base, fixed, mul_assoc] using hraw
      _ ≤ fixed * ((1 + delta⁻¹) * base ^ delta) *
          (psi.LFunction 1).re := hscaled
      _ = siegelLargeLevelDenominator C N delta * base ^ delta *
          (psi.LFunction 1).re := by
        dsimp [fixed]
        unfold siegelLargeLevelDenominator
        ring
  have hdirect := weighted_rpow_transfer (sub_pos.mpr hsUpper)
    (siegelLargeLevelDenominator_pos hpair.1 hN hdelta) hbase
      (siegel_exponent_control hepsilon D hlowerS) hweighted
  have hbasePower : base ^ (-epsilon) =
      (N : ℝ) ^ (-epsilon) * (M : ℝ) ^ (-epsilon) := by
    dsimp [base]
    exact Real.mul_rpow (by positivity) (by positivity)
  rw [hbasePower] at hdirect
  simpa [siegelLargeLevelConstant, delta, mul_assoc] using hdirect

end BombieriVinogradov.SiegelWalfisz

end

section

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelLowerBound :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ (M : ℕ) [NeZero M] (psi : DirichletCharacter ℂ M), 3 ≤ M ->
        DirichletCharacter.IsPrimitive psi -> psi ^ 2 = 1 -> Ne psi 1 ->
          c * (M : ℝ) ^ (-epsilon) ≤ (psi.LFunction 1).re := by
  intro epsilon hepsilon
  obtain ⟨C, D, hpair⟩ := exists_siegelPositivityPair
  obtain ⟨N, chi, s, hseed⟩ := exists_siegelSeed
    (seven_eighths_le_siegelLowerEndpoint epsilon D)
    (siegelLowerEndpoint_lt_one hepsilon D)
  have hN : 0 < N := hseed.1
  have hsUpper : s < 1 := hseed.2.2.2.2.2.2.1
  let _ : NeZero N := ⟨hN.ne'⟩
  let c := min (finiteLevelConstant epsilon N)
    (siegelLargeLevelConstant C epsilon s N)
  have hcPositive : 0 < c := by
    apply lt_min
    · exact finiteLevelConstant_pos epsilon N
    · exact siegelLargeLevelConstant_pos hpair.1 hepsilon hN hsUpper
  refine ⟨c, hcPositive, ?_⟩
  intro M _ psi hM hpsiPrimitive hpsiSquare hpsi
  have hpowerNonneg : 0 ≤ (M : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg M) (-epsilon)
  by_cases hMN : M ≤ N
  · have hcoefficient : c ≤ finiteLevelConstant epsilon N := min_le_left _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (finiteLevelConstant_le_value hMN hM psi hpsiSquare hpsi)
  · have hNM : N < M := Nat.lt_of_not_ge hMN
    let _ : NeZero (N.lcm M) :=
      ⟨Nat.lcm_ne_zero hN.ne' (NeZero.ne M)⟩
    have hcoefficient : c ≤ siegelLargeLevelConstant C epsilon s N :=
      min_le_right _ _
    exact (mul_le_mul_of_nonneg_right hcoefficient hpowerNonneg).trans
      (siegelLowerBound_largeLevel hpair hepsilon hseed M psi hNM
        hpsiPrimitive hpsiSquare hpsi)

end BombieriVinogradov.SiegelWalfisz

end

open Filter BombieriVinogradov.SiegelWalfisz
namespace OMA.E1140

theorem half_factor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ^2=1)
    (r : ℕ) (hr : r.Prime) :
    ∃ a : ℝ, 1/2 ≤ a ∧ 1 - χ r * (r:ℂ)^(-(1:ℂ)) = (a:ℂ) := by
  have rr : (2:ℝ) ≤ r := by exact_mod_cast hr.two_le
  have iv : (r:ℝ)⁻¹ ≤ 1/2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) rr
  have hp : (r:ℂ)^(-(1:ℂ)) = (((r:ℝ)⁻¹):ℂ) := by rw [Complex.cpow_neg_one]; simp
  rw [hp]
  rcases quadraticValue_cases χ hχ r with z|pos|neg
  · exact ⟨1,by norm_num,by simp [z]⟩
  · exact ⟨1 - (r:ℝ)⁻¹,by linarith,by simp [pos]⟩
  · exact ⟨1 + (r:ℝ)⁻¹, by have := inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) r); linarith,
      by simp [neg]⟩

theorem siegel_eight_prime :
    ∀ᶠ p : ℕ in atTop, ∀ (_hp:p.Prime) [NeZero (8*p)] (χ : DirichletCharacter ℂ (8*p)),
    χ ≠ 1 → χ^2=1 → ((8*p:ℕ):ℝ)^(-(1/1024:ℝ)) ≤ (χ.LFunction 1).re := by
  obtain ⟨c,hc,sw⟩ := siegelLowerBound (1/2048:ℝ) (by norm_num)
  have htop : Tendsto (fun p : ℕ => ((8*p:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (show (0:ℝ)<8 by norm_num)
  have little := (tendsto_rpow_neg_atTop (show 0<(1/2048:ℝ) by norm_num)).comp htop
  filter_upwards [little.eventually_lt_const (show 0<c/4 by positivity),eventually_ge_atTop 3]
    with p small p3
  intro hp inst χ ne sq
  let Q : ℝ := ((8*p:ℕ):ℝ)
  let u := Q ^ (-(1/2048:ℝ))
  have posQ : 0 < Q := by dsimp [Q]; positivity
  have posu : 0 < u := Real.rpow_pos_of_pos posQ _
  change u < c/4 at small
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hpr := sw χ.conductor χ.primitiveCharacter (three_le_conductor_of_ne_one χ ne)
    χ.primitiveCharacter_isPrimitive (primitiveCharacter_sq_eq_one χ sq) (primitiveCharacter_ne_one χ ne)
  have cond : χ.conductor ≤ 8*p := Nat.le_of_dvd (by positivity) χ.conductor_dvd_level
  have comp : u ≤ (χ.conductor : ℝ)^(-(1/2048:ℝ)) := by
    apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by dsimp [Q];exact_mod_cast cond)
    norm_num
  have lower : c*u ≤ (χ.primitiveCharacter.LFunction 1).re :=
    (mul_le_mul_of_nonneg_left comp hc.le).trans hpr
  have pf : (8*p).primeFactors = {2,p} := by
    rw [Nat.primeFactors_mul (by decide) hp.ne_zero, hp.primeFactors,show (8:ℕ).primeFactors={2} by
      rw [show 8 = 2^3 by decide, Nat.primeFactors_pow 2 (by decide : 3≠0), Nat.prime_two.primeFactors]]
    ext n; simp
  obtain ⟨a,ha,hfa⟩ := half_factor χ.primitiveCharacter (primitiveCharacter_sq_eq_one χ sq) 2 Nat.prime_two
  obtain ⟨b,hb,hfb⟩ := half_factor χ.primitiveCharacter (primitiveCharacter_sq_eq_one χ sq) p hp
  have corr : characterLevelCorrection χ 1 = ((a*b:ℝ):ℂ) := by
    rw [characterLevelCorrection,pf,Finset.prod_insert (by simp; omega),Finset.prod_singleton]
    rw [Complex.ofReal_one,hfa,hfb,Complex.ofReal_mul]
  have big : 1/4 ≤ a*b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have link := LFunction_eq_primitive_mul_correction χ ne (s:=1)
  rw [corr] at link
  have realpart := congrArg Complex.re link
  simp only [Complex.ofReal_one,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at realpart
  rw [realpart]
  have ident : Q^(-(1/1024:ℝ)) = u*u := by
    dsimp [u]
    rw [← Real.rpow_add posQ]
    norm_num
  change Q^(-(1/1024:ℝ)) ≤ _
  rw [ident]
  calc
    u * u ≤ (c/4)*u := mul_le_mul_of_nonneg_right small.le posu.le
    _ = (c*u)*(1/4) := by ring
    _ ≤ _ := mul_le_mul lower big (by norm_num) ((mul_pos hc posu).le.trans lower)

end OMA.E1140

theorem OMA.solution : OMA.R_Erdos1140_erdos_1140_R2.H1 := by
  exact OMA.E1140.siegel_eight_prime
