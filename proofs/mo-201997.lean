import OMAStatements.S_mo_201997
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Algebra.Polynomial

/-!
# A local field with the covariance of a square

The five-dimensional counterexample applies one sixth of the Laplacian to the
input field. Its construction uses the Hermite expansion of Schwartz tests and
a Gaussian series with prescribed covariance. The kernel calculation is on
smooth compactly supported tests whose supports are disjoint.

The sections under GaussianField, Nuclear, and SchwartzNuclear are adapted
from https://github.com/mrdouglasny/gaussian-field (Michael R. Douglas, commit
1283a2721377a36e80672799fcc1f69a494c8ea0). Their imports are collected above.
The source is abridged to the definitions and results needed for this proof.

Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Copyright (c) 2026 Michael R. Douglas. All rights reserved.

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

-- SchwartzNuclear.HermiteFunctions
section
open MeasureTheory Polynomial Real
open scoped ContDiff
noncomputable section
def hermiteFunctionNormConst (n : ℕ) : ℝ :=
  Real.sqrt ((n.factorial * Real.sqrt Real.pi)⁻¹)
def hermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  hermiteFunctionNormConst n *
  ((hermite n).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2) *
  Real.exp (-(x ^ 2) / 2)
private lemma continuous_hermiteFunction (n : ℕ) : Continuous (hermiteFunction n) := by
  unfold hermiteFunction hermiteFunctionNormConst
  fun_prop
private lemma pow_mul_exp_neg_le (k : ℕ) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |x| ^ k * Real.exp (-b * x ^ 2) ≤ ↑k.factorial * Real.exp (1 / (2 * b)) := by
  have hpow : |x| ^ k ≤ ↑k.factorial * Real.exp (|x|) := by
    have hfact_pos : (0 : ℝ) < ↑k.factorial := Nat.cast_pos.mpr k.factorial_pos
    have h : |x| ^ k / ↑k.factorial ≤ Real.exp (|x|) := le_trans
      (Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range (k + 1)) =>
          div_nonneg (pow_nonneg (abs_nonneg x) i) (Nat.cast_nonneg' (i.factorial)))
        (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (k + 1)))
      (Real.sum_le_exp_of_nonneg (abs_nonneg x) (k + 1))
    rwa [div_le_iff₀ hfact_pos, mul_comm] at h
  have hquad : |x| ≤ b / 2 * x ^ 2 + 1 / (2 * b) := by
    have heq : b / 2 * x ^ 2 + 1 / (2 * b) = (b ^ 2 * x ^ 2 + 1) / (2 * b) := by field_simp
    rw [heq, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
    nlinarith [sq_abs x, sq_nonneg (b * |x| - 1)]
  calc |x| ^ k * Real.exp (-b * x ^ 2)
      ≤ |x| ^ k * Real.exp (-(b / 2) * x ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg x) k)
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
    _ ≤ ↑k.factorial * Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ↑k.factorial * (Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2)) := by ring
    _ = ↑k.factorial * Real.exp (|x| + -(b / 2) * x ^ 2) := by rw [← Real.exp_add]
    _ ≤ ↑k.factorial * Real.exp (1 / (2 * b)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg' _)
        exact Real.exp_le_exp.mpr (by linarith)
private lemma integrable_pow_mul_exp_neg_mul_sq (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) volume := by
  have hcont : Continuous (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) := by fun_prop
  set C : ℝ := ↑k.factorial * Real.exp (1 / (2 * b))
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (half_pos hb)).const_mul C)
    hcont.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hpow : |x| ^ k ≤ ↑k.factorial * Real.exp (|x|) := by
    have hfact_pos : (0 : ℝ) < ↑k.factorial := Nat.cast_pos.mpr k.factorial_pos
    have h : |x| ^ k / ↑k.factorial ≤ Real.exp (|x|) := le_trans
      (Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range (k + 1)) =>
          div_nonneg (pow_nonneg (abs_nonneg x) i) (Nat.cast_nonneg' (i.factorial)))
        (Finset.mem_range.mpr (by omega) : k ∈ Finset.range (k + 1)))
      (Real.sum_le_exp_of_nonneg (abs_nonneg x) (k + 1))
    rwa [div_le_iff₀ hfact_pos, mul_comm] at h
  have hquad : |x| ≤ b / 2 * x ^ 2 + 1 / (2 * b) := by
    have heq : b / 2 * x ^ 2 + 1 / (2 * b) = (b ^ 2 * x ^ 2 + 1) / (2 * b) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * b)]
    nlinarith [sq_abs x, sq_nonneg (b * |x| - 1)]
  have hfactor : Real.exp (-b * x ^ 2) =
      Real.exp (-(b / 2) * x ^ 2) * Real.exp (-(b / 2) * x ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hfactor, show |x| ^ k * (Real.exp (-(b / 2) * x ^ 2) * Real.exp (-(b / 2) * x ^ 2)) =
    (|x| ^ k * Real.exp (-(b / 2) * x ^ 2)) * Real.exp (-(b / 2) * x ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc |x| ^ k * Real.exp (-(b / 2) * x ^ 2)
      ≤ ↑k.factorial * Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = ↑k.factorial * (Real.exp (|x|) * Real.exp (-(b / 2) * x ^ 2)) := by ring
    _ = ↑k.factorial * Real.exp (|x| + -(b / 2) * x ^ 2) := by
        rw [← Real.exp_add]
    _ ≤ ↑k.factorial * Real.exp (1 / (2 * b)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg' _)
        exact Real.exp_le_exp.mpr (by linarith)
private lemma integrable_eval_mul_exp_neg_mul_sq (p : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) volume := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun x : ℝ => (p + q).eval x * Real.exp (-b * x ^ 2)) =
           (fun x => p.eval x * Real.exp (-b * x ^ 2)) +
           (fun x => q.eval x * Real.exp (-b * x ^ 2)) := by
      ext x; simp [Polynomial.eval_add, add_mul]
    rw [this]; exact hp.add hq
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    show Integrable (fun x : ℝ => a * x ^ k * Real.exp (-b * x ^ 2)) volume
    have heq : (fun x : ℝ => a * x ^ k * Real.exp (-b * x ^ 2)) =
               fun x => a * (x ^ k * Real.exp (-b * x ^ 2)) := by ext x; ring
    rw [heq]
    exact (integrable_pow_mul_exp_neg_mul_sq k hb).const_mul a
private lemma polynomial_eval_mul_exp_neg_bound (P : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |P.eval x * Real.exp (-b * x ^ 2)| ≤ C := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Cp, hCp, hp⟩ := hp
    obtain ⟨Cq, hCq, hq⟩ := hq
    exact ⟨Cp + Cq, add_nonneg hCp hCq, fun x => by
      simp only [Polynomial.eval_add, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hp x) (hq x))⟩
  | monomial k a =>
    refine ⟨|a| * (↑k.factorial * Real.exp (1 / (2 * b))), by positivity, fun x => ?_⟩
    simp only [Polynomial.eval_monomial]
    rw [show a * x ^ k * Real.exp (-b * x ^ 2) =
      a * (x ^ k * Real.exp (-b * x ^ 2)) from by ring, abs_mul,
      show |x ^ k * Real.exp (-b * x ^ 2)| =
        |x| ^ k * Real.exp (-b * x ^ 2) from by
          rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]]
    exact mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le k hb x) (abs_nonneg a)
theorem hermiteFunction_memLp (n : ℕ) :
    MemLp (hermiteFunction n) 2 MeasureTheory.volume := by
  have hcont := continuous_hermiteFunction n
  rw [← integrable_norm_rpow_iff hcont.aestronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  suffices h : Integrable (fun x : ℝ => (hermiteFunction n x) ^ 2) volume by
    exact h.congr (by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      simp [sq_abs])
  set P := (hermite n).map (Int.castRingHom ℝ) with hP_def
  set c := hermiteFunctionNormConst n with hc_def
  set Q := P.comp (C (Real.sqrt 2) * X) with hQ_def
  have hQeval : ∀ x : ℝ, Q.eval x = P.eval (x * Real.sqrt 2) := by
    intro x; simp only [hQ_def, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]; congr 1; ring
  have h_eq : (fun x : ℝ => (hermiteFunction n x) ^ 2) =
              fun x => c ^ 2 * ((Q * Q).eval x * Real.exp (-1 * x ^ 2)) := by
    ext x
    unfold hermiteFunction
    simp only [← hc_def, ← hP_def, Polynomial.eval_mul, ← hQeval]
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) = Real.exp (-1 * x ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (c * Q.eval x * Real.exp (-(x ^ 2) / 2)) ^ 2
        = c ^ 2 * Q.eval x ^ 2 *
          (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2)) := by ring
      _ = c ^ 2 * Q.eval x ^ 2 * Real.exp (-1 * x ^ 2) := by rw [hexp]
      _ = c ^ 2 * (Q.eval x * Q.eval x * Real.exp (-1 * x ^ 2)) := by ring
  rw [h_eq]
  exact (integrable_eval_mul_exp_neg_mul_sq (Q * Q) one_pos).const_mul (c ^ 2)
abbrev hermiteR (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)
theorem hermite_derivative (n : ℕ) :
    derivative (hermite (n + 1)) = (↑(n + 1) : ℤ[X]) * hermite n := by
  induction n with
  | zero => simp [hermite_succ, hermite_zero]
  | succ n ih =>
    show derivative (X * hermite (n + 1) - derivative (hermite (n + 1)))
        = (↑(n + 2) : ℤ[X]) * hermite (n + 1)
    rw [map_sub, derivative_mul, derivative_X, one_mul]
    simp only [ih]
    rw [derivative_mul, derivative_natCast, zero_mul, zero_add]
    have step : hermite (n + 1) + X * ((↑(n + 1) : ℤ[X]) * hermite n) -
        (↑(n + 1) : ℤ[X]) * derivative (hermite n) =
        hermite (n + 1) +
        (↑(n + 1) : ℤ[X]) * (X * hermite n - derivative (hermite n)) := by ring
    rw [step, ← hermite_succ,
        show (↑(n + 2) : ℤ[X]) = 1 + ↑(n + 1) from by push_cast; ring]
    ring
private theorem hermiteR_derivative (n : ℕ) :
    derivative (hermiteR (n + 1)) = (↑(n + 1) : ℝ[X]) * hermiteR n := by
  simp only [hermiteR]
  rw [Polynomial.derivative_map, hermite_derivative, Polynomial.map_mul, Polynomial.map_natCast]
abbrev gaussian (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))
private theorem deriv_hermiteEval_mul_gaussian (m : ℕ) (x : ℝ) :
    deriv (fun u => (hermiteR m).eval u * gaussian u) x =
    -((hermiteR (m + 1)).eval x) * gaussian x := by
  have hdiff_exp : DifferentiableAt ℝ (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) x :=
    DifferentiableAt.exp (by fun_prop)
  have hd := deriv_fun_mul (hermiteR m).differentiable.differentiableAt hdiff_exp
  rw [hd]
  have hpoly : deriv (fun u => (hermiteR m).eval u) x = (derivative (hermiteR m)).eval x := by
    have h1 : (fun u => (hermiteR m).eval u) = fun u => Polynomial.aeval u (hermiteR m) := by
      ext u; simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
    rw [h1, Polynomial.deriv_aeval]
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
  rw [hpoly]
  have hexp : deriv (fun u : ℝ => Real.exp (-(u ^ 2 / 2))) x = -x * gaussian x := by
    have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2 / 2)) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).neg
      convert this using 1 <;> first | rfl | ring
    exact h1.exp.deriv.trans (mul_comm _ _)
  rw [hexp]
  have hrec : (hermiteR (m + 1)).eval x = x * (hermiteR m).eval x - (derivative (hermiteR m)).eval x := by
    have h1 : hermiteR (m + 1) = X * hermiteR m - derivative (hermiteR m) := by
      unfold hermiteR
      rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.derivative_map]
    rw [h1]; simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
  rw [hrec]; ring
private theorem integrable_hermiteR_mul_gaussian (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * gaussian x) volume := by
  have h : (fun x : ℝ => p.eval x * gaussian x) =
      fun x => p.eval x * Real.exp (-(1/2) * x ^ 2) := by
    ext x; show p.eval x * Real.exp (-(x ^ 2 / 2)) = _; congr 1; congr 1; ring
  rw [h]
  exact integrable_eval_mul_exp_neg_mul_sq p (by positivity : (0:ℝ) < 1/2)
private theorem integrable_hermiteProd_mul_gaussian (n m : ℕ) :
    Integrable (fun x : ℝ => (hermiteR n).eval x * (hermiteR m).eval x * gaussian x) volume := by
  have h : (fun x : ℝ => (hermiteR n).eval x * (hermiteR m).eval x * gaussian x) =
      fun x => (hermiteR n * hermiteR m).eval x * gaussian x := by
    ext x; simp [Polynomial.eval_mul, mul_assoc]
  rw [h]
  exact integrable_hermiteR_mul_gaussian (hermiteR n * hermiteR m)
private theorem integrable_hermite_mul_neg_hermite_gaussian (n m : ℕ) :
    Integrable (fun x : ℝ => (hermiteR n).eval x *
      (-(hermiteR (m + 1)).eval x * gaussian x)) volume := by
  have h : (fun x : ℝ => (hermiteR n).eval x * (-(hermiteR (m + 1)).eval x * gaussian x)) =
      fun x => -((hermiteR n * hermiteR (m + 1)).eval x * gaussian x) := by
    ext x; simp [Polynomial.eval_mul]; ring
  rw [h]
  exact (integrable_hermiteR_mul_gaussian (hermiteR n * hermiteR (m + 1))).neg
private theorem differentiable_hermiteEval_mul_gaussian (m : ℕ) :
    Differentiable ℝ (fun u => (hermiteR m).eval u * gaussian u) :=
  (hermiteR m).differentiable.mul
    (Differentiable.exp (by fun_prop : Differentiable ℝ (fun u : ℝ => -(u ^ 2 / 2))))
noncomputable def J (n m : ℕ) : ℝ :=
  ∫ x, (hermiteR n).eval x * ((hermiteR m).eval x * gaussian x)
private theorem J_succ_succ (n m : ℕ) : J (n + 1) (m + 1) = (↑(n + 1) : ℝ) * J n m := by
  unfold J
  have hJ : ∫ x, (hermiteR (n + 1)).eval x * ((hermiteR (m + 1)).eval x * gaussian x) =
      -∫ x, (hermiteR (n + 1)).eval x *
        (deriv (fun u => (hermiteR m).eval u * gaussian u) x) := by
    have h_eq : ∀ x : ℝ, (hermiteR (n + 1)).eval x * ((hermiteR (m + 1)).eval x * gaussian x) =
        -((hermiteR (n + 1)).eval x *
          deriv (fun u => (hermiteR m).eval u * gaussian u) x) := by
      intro x; rw [deriv_hermiteEval_mul_gaussian]; ring
    simp_rw [h_eq, integral_neg]
  rw [hJ]
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (𝕜 := ℝ) (E := ℝ)
    (μ := volume)
    (f := fun x => (hermiteR (n + 1)).eval x)
    (g := fun u => (hermiteR m).eval u * gaussian u)
    (v := (1 : ℝ))
    ?_ ?_ ?_ (fun x _ => (hermiteR (n + 1)).differentiable.differentiableAt)
    (fun x _ => (differentiable_hermiteEval_mul_gaussian m).differentiableAt)
  simp only [fderiv_apply_one_eq_deriv] at hibp
  rw [neg_eq_iff_eq_neg.mpr hibp]
  have h_rw : ∀ x : ℝ, deriv (fun x => (hermiteR (n + 1)).eval x) x *
      ((hermiteR m).eval x * gaussian x) =
      (↑(n + 1) : ℝ) * ((hermiteR n).eval x * ((hermiteR m).eval x * gaussian x)) := by
    intro x
    rw [Polynomial.deriv, hermiteR_derivative]
    simp [Polynomial.eval_mul, Polynomial.eval_natCast]; ring
  simp_rw [h_rw, integral_const_mul]
  ·
    show Integrable (fun x => fderiv ℝ (fun x => (hermiteR (n + 1)).eval x) x 1 *
      ((hermiteR m).eval x * gaussian x)) volume
    have : (fun x => fderiv ℝ (fun x => (hermiteR (n + 1)).eval x) x 1 *
        ((hermiteR m).eval x * gaussian x)) =
        fun x => ((↑(n + 1) : ℝ) * (hermiteR n).eval x) *
          ((hermiteR m).eval x * gaussian x) := by
      ext x
      rw [fderiv_apply_one_eq_deriv, Polynomial.deriv, hermiteR_derivative]
      simp [Polynomial.eval_mul, Polynomial.eval_natCast]
    rw [this]
    have : (fun x => ((↑(n + 1) : ℝ) * (hermiteR n).eval x) *
        ((hermiteR m).eval x * gaussian x)) =
        fun x => (↑(n + 1) : ℝ) * ((hermiteR n).eval x * (hermiteR m).eval x * gaussian x) := by
      ext x; ring
    rw [this]
    exact (integrable_hermiteProd_mul_gaussian n m).const_mul _
  ·
    show Integrable (fun x => (hermiteR (n + 1)).eval x *
      (fderiv ℝ (fun u => (hermiteR m).eval u * gaussian u) x 1)) volume
    have : (fun x => (hermiteR (n + 1)).eval x *
        (fderiv ℝ (fun u => (hermiteR m).eval u * gaussian u) x 1)) =
        fun x => (hermiteR (n + 1)).eval x *
          deriv (fun u => (hermiteR m).eval u * gaussian u) x := by
      ext x; rw [fderiv_apply_one_eq_deriv]
    rw [this]
    have : (fun x => (hermiteR (n + 1)).eval x *
        deriv (fun u => (hermiteR m).eval u * gaussian u) x) =
        fun x => (hermiteR (n + 1)).eval x *
          (-(hermiteR (m + 1)).eval x * gaussian x) := by
      ext x; rw [deriv_hermiteEval_mul_gaussian]
    rw [this]
    exact integrable_hermite_mul_neg_hermite_gaussian (n + 1) m
  ·
    exact (integrable_hermiteProd_mul_gaussian (n + 1) m).congr
      (by filter_upwards; intro x; ring)
private theorem J_comm (n m : ℕ) : J n m = J m n := by
  unfold J; congr 1; ext x; ring
private theorem J_zero_zero : J 0 0 = Real.sqrt (2 * Real.pi) := by
  unfold J hermiteR
  simp only [hermite_zero]
  have h : (fun x : ℝ => (Polynomial.map (Int.castRingHom ℝ) (C 1)).eval x *
      ((Polynomial.map (Int.castRingHom ℝ) (C 1)).eval x * gaussian x)) =
      fun x => Real.exp (-(1/2) * x ^ 2) := by
    ext x; simp [gaussian]; ring
  rw [h, integral_gaussian (1/2)]
  congr 1; ring
private theorem J_succ_zero (k : ℕ) : J (k + 1) 0 = 0 := by
  have h1 : J (k + 2) 1 = (↑(k + 2) : ℝ) * J (k + 1) 0 := J_succ_succ (k + 1) 0
  have h2 : J (k + 2) 1 = J (k + 1) 0 := by
    rw [J_comm (k + 2) 1]
    show J 1 (k + 2) = J (k + 1) 0
    rw [show (1 : ℕ) = 0 + 1 from rfl, show k + 2 = (k + 1) + 1 from rfl,
        J_succ_succ 0 (k + 1)]
    simp [J_comm]
  have h3 : (↑(k + 1) : ℝ) * J (k + 1) 0 = 0 := by
    have h12 : (↑(k + 2) : ℝ) * J (k + 1) 0 - J (k + 1) 0 = 0 := by linarith
    have : (↑(k + 1) : ℝ) * J (k + 1) 0 =
        (↑(k + 2) : ℝ) * J (k + 1) 0 - J (k + 1) 0 := by push_cast; ring
    linarith
  have h4 : (↑(k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp h3).resolve_left h4
theorem J_eq : ∀ m n : ℕ,
    J n m = if n = m then ↑(n.factorial) * Real.sqrt (2 * Real.pi) else 0 := by
  intro m
  induction m with
  | zero =>
    intro n
    cases n with
    | zero => simp [J_zero_zero]
    | succ k => simp [J_succ_zero k]
  | succ m ih =>
    intro n
    cases n with
    | zero =>
      rw [J_comm, J_succ_zero]
      simp
    | succ k =>
      rw [J_succ_succ, ih]
      by_cases h : k = m
      · subst h; simp [Nat.factorial_succ, Nat.cast_mul]; ring
      · simp [h]
private theorem integral_hermiteProd_gaussian_sq (n m : ℕ) :
    ∫ x, (hermiteR n).eval (x * Real.sqrt 2) *
      ((hermiteR m).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2))) =
    (Real.sqrt 2)⁻¹ * J n m := by
  set g : ℝ → ℝ := fun u => (hermiteR n).eval u * ((hermiteR m).eval u * gaussian u)
  have hg_eq : ∀ x, (hermiteR n).eval (x * Real.sqrt 2) *
      ((hermiteR m).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2))) =
      g (Real.sqrt 2 * x) := by
    intro x
    simp only [g, gaussian, mul_comm (Real.sqrt 2) x]
    congr 1; congr 1; congr 1
    rw [mul_pow, Real.sq_sqrt two_pos.le]; ring
  simp_rw [hg_eq]
  rw [Measure.integral_comp_mul_left g (Real.sqrt 2),
    show |(Real.sqrt 2)⁻¹| = (Real.sqrt 2)⁻¹ from
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr two_pos)),
    smul_eq_mul]
  congr 1
private theorem hermiteFunction_integral_eq (n m : ℕ) :
    ∫ x, hermiteFunction n x * hermiteFunction m x =
    hermiteFunctionNormConst n * hermiteFunctionNormConst m *
      ((Real.sqrt 2)⁻¹ * J n m) := by
  have h_integrand : (fun x => hermiteFunction n x * hermiteFunction m x) =
      fun x => hermiteFunctionNormConst n * hermiteFunctionNormConst m *
        ((hermiteR n).eval (x * Real.sqrt 2) *
         ((hermiteR m).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2)))) := by
    ext x; unfold hermiteFunction hermiteR
    set cn := hermiteFunctionNormConst n
    set cm := hermiteFunctionNormConst m
    set Hn := ((hermite n).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2)
    set Hm := ((hermite m).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2)
    set G := Real.exp (-(x ^ 2) / 2)
    show cn * Hn * G * (cm * Hm * G) = cn * cm * (Hn * (Hm * Real.exp (-(x ^ 2))))
    have hG : G * G = Real.exp (-(x ^ 2)) := by
      show Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) = Real.exp (-(x ^ 2))
      rw [← Real.exp_add]; congr 1; ring
    calc cn * Hn * G * (cm * Hm * G)
        = cn * cm * (Hn * Hm) * (G * G) := by ring
      _ = cn * cm * (Hn * Hm) * Real.exp (-(x ^ 2)) := by rw [hG]
      _ = cn * cm * (Hn * (Hm * Real.exp (-(x ^ 2)))) := by ring
  rw [h_integrand, integral_const_mul]
  congr 1
  exact integral_hermiteProd_gaussian_sq n m
theorem hermiteFunction_orthonormal :
    ∀ n m : ℕ, ∫ x, hermiteFunction n x * hermiteFunction m x = if n = m then 1 else 0 := by
  intro n m
  rw [hermiteFunction_integral_eq, J_eq]
  split_ifs with h
  ·
    subst h
    simp only [hermiteFunctionNormConst]
    have hfact : (0 : ℝ) < ↑n.factorial := Nat.cast_pos.mpr n.factorial_pos
    have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
    have h_sq : Real.sqrt ((↑n.factorial * Real.sqrt Real.pi)⁻¹) *
        Real.sqrt ((↑n.factorial * Real.sqrt Real.pi)⁻¹) =
        (↑n.factorial * Real.sqrt Real.pi)⁻¹ :=
      Real.mul_self_sqrt (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg' _) (Real.sqrt_nonneg _)))
    rw [h_sq]
    have h2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul two_pos.le Real.pi
    rw [h2pi]
    field_simp
  ·
    ring
noncomputable def gaussianSchwartz : SchwartzMap ℝ ℝ where
  toFun x := Real.exp (-(x ^ 2 / 2))
  smooth' := by fun_prop
  decay' := by
    intro k n
    set P := (Polynomial.hermite n).map (algebraMap ℤ ℝ)
    obtain ⟨C, hC_nonneg, hbound⟩ :=
      polynomial_eval_mul_exp_neg_bound (X ^ k * P) (by positivity : (0 : ℝ) < 1 / 2)
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs]
    have hiter : iteratedDeriv n (fun x => Real.exp (-(x ^ 2 / 2))) x =
        (-1 : ℝ) ^ n * Polynomial.aeval x (Polynomial.hermite n) *
        Real.exp (-(x ^ 2 / 2)) := by
      rw [iteratedDeriv_eq_iterate]
      exact Polynomial.deriv_gaussian_eq_hermite_mul_gaussian n x
    rw [hiter, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (Real.exp_pos _)]
    have haeval : Polynomial.aeval x (Polynomial.hermite n) = P.eval x := by
      simp [P, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [haeval]
    have hrw : |x| ^ k * (|P.eval x| * Real.exp (-(x ^ 2 / 2))) =
        |(X ^ k * P).eval x * Real.exp (-(1 / 2) * x ^ 2)| := by
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
          abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      ring_nf
    rw [hrw]
    exact hbound x
private lemma derivCLM_iterate_apply (n : ℕ) (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    (⇑(SchwartzMap.derivCLM ℝ ℝ))^[n] g x = deriv^[n] (⇑g) x := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => exact ih _
private lemma pow_mul_gaussian_schwartz (k : ℕ) :
    ∃ (φ : SchwartzMap ℝ ℝ), ∀ x, φ x = x ^ k * Real.exp (-(x ^ 2 / 2)) := by
  induction k with
  | zero =>
    exact ⟨gaussianSchwartz, fun x => by
      change Real.exp (-(x ^ 2 / 2)) = x ^ 0 * Real.exp (-(x ^ 2 / 2)); simp⟩
  | succ k ih =>
    obtain ⟨ψ, hψ⟩ := ih
    refine ⟨SchwartzMap.smulLeftCLM ℝ (fun x => x) ψ, fun x => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id']
    simp only [smul_eq_mul, hψ x]
    ring
private lemma poly_mul_gaussian_schwartz (P : ℝ[X]) :
    ∃ (φ : SchwartzMap ℝ ℝ), ∀ x, φ x = P.eval x * Real.exp (-(x ^ 2 / 2)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨φp, hφp⟩ := hp
    obtain ⟨φq, hφq⟩ := hq
    exact ⟨φp + φq, fun x => by
      simp only [add_apply, Polynomial.eval_add, add_mul, hφp x, hφq x]⟩
  | monomial k a =>
    obtain ⟨ψ, hψ⟩ := pow_mul_gaussian_schwartz k
    exact ⟨a • ψ, fun x => by
      simp only [smul_apply, smul_eq_mul, Polynomial.eval_monomial, hψ x]
      ring⟩
theorem hermiteFunction_schwartz (n : ℕ) :
    ∃ (φ : SchwartzMap ℝ ℝ), ∀ x, φ x = hermiteFunction n x := by
  set Q := (hermiteR n).comp (C (Real.sqrt 2) * X) with hQ_def
  obtain ⟨ψ, hψ⟩ := poly_mul_gaussian_schwartz Q
  refine ⟨hermiteFunctionNormConst n • ψ, fun x => ?_⟩
  simp only [smul_apply, smul_eq_mul, hψ x]
  unfold hermiteFunction
  have hQeval : Q.eval x = ((hermite n).map (Int.castRingHom ℝ)).eval (x * Real.sqrt 2) := by
    simp [hQ_def, hermiteR, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_comm x (Real.sqrt 2)]
  rw [← hQeval]
  have hexp : Real.exp (-(x ^ 2 / 2)) = Real.exp (-(x ^ 2) / 2) := by
    congr 1; ring
  rw [hexp, mul_assoc]
private lemma normConst_pos (n : ℕ) : 0 < hermiteFunctionNormConst n := by
  unfold hermiteFunctionNormConst
  exact Real.sqrt_pos.mpr (inv_pos.mpr (mul_pos
    (Nat.cast_pos.mpr n.factorial_pos) (Real.sqrt_pos.mpr Real.pi_pos)))
private lemma normConst_nonneg (n : ℕ) : 0 ≤ hermiteFunctionNormConst n :=
  le_of_lt (normConst_pos n)
private lemma normConst_sq (n : ℕ) :
    hermiteFunctionNormConst n * hermiteFunctionNormConst n =
    (↑n.factorial * Real.sqrt Real.pi)⁻¹ := by
  unfold hermiteFunctionNormConst
  exact Real.mul_self_sqrt (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg' _) (Real.sqrt_nonneg _)))
private lemma normConst_succ (n : ℕ) :
    hermiteFunctionNormConst n = Real.sqrt (↑(n + 1)) * hermiteFunctionNormConst (n + 1) := by
  simp only [hermiteFunctionNormConst]
  rw [← Real.sqrt_mul (Nat.cast_nonneg' (n + 1))]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hfact : (0 : ℝ) < ↑n.factorial := Nat.cast_pos.mpr n.factorial_pos
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hn1 : (0 : ℝ) < ↑(n + 1) := Nat.cast_pos.mpr (Nat.succ_pos n)
  field_simp
lemma hermite_X_mul (n : ℕ) :
    X * hermite (n + 1) = hermite (n + 2) + (↑(n + 1) : ℤ[X]) * hermite n := by
  linear_combination -(hermite_succ (n + 1)) + hermite_derivative n
lemma hermiteR_recurrence_succ (n : ℕ) (t : ℝ) :
    t * (hermiteR (n + 1)).eval t =
    (hermiteR (n + 2)).eval t + ↑(n + 1) * (hermiteR n).eval t := by
  have h := congr_arg (fun p => (Polynomial.map (Int.castRingHom ℝ) p).eval t)
    (hermite_X_mul n)
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_natCast, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast] at h
  linarith
lemma hermiteR_recurrence_zero (t : ℝ) :
    t * (hermiteR 0).eval t = (hermiteR 1).eval t := by
  simp [hermiteR, hermite_zero, hermite_succ, Polynomial.eval_X,
    Polynomial.map_X]
private lemma mul_x_hermiteFunction_aux (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x =
    hermiteFunctionNormConst n *
    (x * (hermiteR n).eval (x * Real.sqrt 2)) *
    Real.exp (-(x ^ 2) / 2) := by
  unfold hermiteFunction
  ring
private lemma normConst_div_sqrt2 (n : ℕ) :
    hermiteFunctionNormConst n / Real.sqrt 2 =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunctionNormConst (n + 1) := by
  rw [normConst_succ n, mul_div_assoc, Real.sqrt_div (Nat.cast_nonneg' (n + 1))]
  ring
private lemma normConst_mul_div_sqrt2 (n : ℕ) :
    ↑(n + 1) * hermiteFunctionNormConst (n + 1) / Real.sqrt 2 =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunctionNormConst n := by
  have hn1 : (0 : ℝ) ≤ ↑(n + 1) := Nat.cast_nonneg' (n + 1)
  have hc := normConst_succ n
  conv_lhs => rw [show (↑(n + 1) : ℝ) = Real.sqrt (↑(n + 1)) * Real.sqrt (↑(n + 1)) from
    (Real.mul_self_sqrt hn1).symm]
  rw [mul_assoc, hc.symm, mul_div_assoc, Real.sqrt_div hn1]
  ring
theorem mul_x_hermiteFunction (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
    Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x := by
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2pos
  set t := x * Real.sqrt 2 with ht_def
  set e := Real.exp (-(x ^ 2) / 2) with he_def
  have hx_eq : x = t / Real.sqrt 2 := by
    rw [ht_def, mul_div_cancel_right₀ x h2ne]
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_div, Real.sqrt_zero, zero_mul, add_zero, Nat.zero_sub]
    unfold hermiteFunction
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    rw [hx_eq]
    simp only [ht_simp]
    have hrec := hermiteR_recurrence_zero t
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    have lhs_eq : t / Real.sqrt 2 * (hermiteFunctionNormConst 0 * (hermiteR 0).eval t * e') =
      hermiteFunctionNormConst 0 / Real.sqrt 2 * (t * (hermiteR 0).eval t) * e' := by ring
    rw [lhs_eq, hrec, normConst_div_sqrt2 0]
    ring
  | succ n =>
    rw [show (n + 1 : ℕ) - 1 = n from by omega]
    unfold hermiteFunction
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    rw [hx_eq]
    simp only [ht_simp]
    have hrec := hermiteR_recurrence_succ n t
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    have lhs_eq : t / Real.sqrt 2 *
      (hermiteFunctionNormConst (n + 1) * (hermiteR (n + 1)).eval t * e') =
      hermiteFunctionNormConst (n + 1) / Real.sqrt 2 * (t * (hermiteR (n + 1)).eval t) * e' := by
      ring
    rw [lhs_eq, hrec]
    have key1 := normConst_div_sqrt2 (n + 1)
    have key2 := normConst_mul_div_sqrt2 n
    have expand : hermiteFunctionNormConst (n + 1) / Real.sqrt 2 *
      ((hermiteR (n + 2)).eval t + ↑(n + 1) * (hermiteR n).eval t) * e' =
      hermiteFunctionNormConst (n + 1) / Real.sqrt 2 * (hermiteR (n + 2)).eval t * e' +
      (↑(n + 1) * hermiteFunctionNormConst (n + 1) / Real.sqrt 2) * (hermiteR n).eval t * e' := by
      ring
    rw [expand, key1, key2]
    ring
lemma hermiteFunction_contDiff (j : ℕ) (m : ℕ) :
    ContDiff ℝ m (hermiteFunction j) := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz j
  have : hermiteFunction j = ⇑φ := funext fun x => (hφ x).symm
  rw [this]; exact φ.smooth _
theorem deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (hermiteFunction n) x =
    Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x -
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x := by
  have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt h2pos
  set t := x * Real.sqrt 2 with ht_def
  set e := Real.exp (-(x ^ 2) / 2) with he_def
  have hx_eq : x = t / Real.sqrt 2 := by
    rw [ht_def, mul_div_cancel_right₀ x h2ne]
  have hpoly_hasderiv : HasDerivAt (fun u => (hermiteR n).eval (u * Real.sqrt 2))
      (Real.sqrt 2 * (Polynomial.derivative (hermiteR n)).eval (x * Real.sqrt 2)) x := by
    have h_inner : HasDerivAt (fun u : ℝ => u * Real.sqrt 2) (Real.sqrt 2) x := by
      have := (hasDerivAt_id x).mul_const (Real.sqrt 2)
      simpa using this
    have h_outer : HasDerivAt (fun u => (hermiteR n).eval u)
        ((Polynomial.derivative (hermiteR n)).eval (x * Real.sqrt 2)) (x * Real.sqrt 2) := by
      have : (fun u => (hermiteR n).eval u) = fun u => Polynomial.aeval u (hermiteR n) := by
        ext u; simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
      rw [this]
      exact Polynomial.hasDerivAt_aeval (hermiteR n) (x * Real.sqrt 2)
    have hcomp := h_outer.comp x h_inner
    rwa [mul_comm] at hcomp
  have hexp_hasderiv : HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) (-x * e) x := by
    have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-x) x := by
      have := ((hasDerivAt_pow 2 x).neg.div_const 2)
      convert this using 1 <;> first | rfl | ring
    have h2 := h1.exp
    rw [he_def]
    convert h2 using 1; ring
  have hprod : HasDerivAt (fun u => (hermiteR n).eval (u * Real.sqrt 2) * Real.exp (-(u ^ 2) / 2))
      (Real.sqrt 2 * (Polynomial.derivative (hermiteR n)).eval (x * Real.sqrt 2) * e +
       (hermiteR n).eval (x * Real.sqrt 2) * (-x * e)) x := by
    have := hpoly_hasderiv.mul hexp_hasderiv
    rw [he_def] at this
    convert this using 2 <;> rfl
  have hfn_eq : hermiteFunction n = fun u =>
      hermiteFunctionNormConst n * ((hermiteR n).eval (u * Real.sqrt 2) * Real.exp (-(u ^ 2) / 2)) := by
    ext u; unfold hermiteFunction; ring
  have hfull := hprod.const_mul (hermiteFunctionNormConst n)
  rw [hfn_eq, hfull.deriv]
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_div, Real.sqrt_zero, zero_mul, zero_sub, Nat.zero_sub]
    have hd0 : Polynomial.derivative (hermiteR 0) = 0 := by
      simp [hermiteR, hermite_zero]
    rw [hd0, Polynomial.eval_zero, mul_zero, zero_mul, zero_add]
    unfold hermiteFunction
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    rw [hx_eq]
    simp only [ht_simp]
    have hrec := hermiteR_recurrence_zero t
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    have he_eq : e = e' := by
      rw [he_def, he'_def]; congr 1; rw [hx_eq]
    rw [he_eq]
    have lhs_eq : hermiteFunctionNormConst 0 *
      ((hermiteR 0).eval t * (-(t / Real.sqrt 2) * e')) =
      -(hermiteFunctionNormConst 0 / Real.sqrt 2) * (t * (hermiteR 0).eval t) * e' := by ring
    rw [lhs_eq, hrec, normConst_div_sqrt2 0]
    ring
  | succ n =>
    rw [show (n + 1 : ℕ) - 1 = n from by omega]
    have hd := hermiteR_derivative n
    rw [hd, Polynomial.eval_mul, Polynomial.eval_natCast]
    have hrec := hermiteR_recurrence_succ n t
    unfold hermiteFunction
    have ht_simp : t / Real.sqrt 2 * Real.sqrt 2 = t := div_mul_cancel₀ t h2ne
    rw [hx_eq]
    simp only [ht_simp]
    set e' := Real.exp (-(t / Real.sqrt 2) ^ 2 / 2) with he'_def
    have he_eq : e = e' := by
      rw [he_def, he'_def]; congr 1; rw [hx_eq]
    rw [he_eq]
    have key1 := normConst_mul_div_sqrt2 n
    have key2 := normConst_div_sqrt2 (n + 1)
    have h_sqrt2_eq : Real.sqrt 2 = Real.sqrt 2 * Real.sqrt 2 / Real.sqrt 2 := by
      rw [mul_div_cancel_right₀ _ h2ne]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have expand : hermiteFunctionNormConst (n + 1) *
      (Real.sqrt 2 * (↑(n + 1) * (hermiteR n).eval t) * e' +
       (hermiteR (n + 1)).eval t * (-(t / Real.sqrt 2) * e')) =
      (↑(n + 1) * hermiteFunctionNormConst (n + 1) / Real.sqrt 2) * (hermiteR n).eval t * e' -
      (hermiteFunctionNormConst (n + 1) / Real.sqrt 2) * (hermiteR (n + 2)).eval t * e' := by
      have lhs_factor : hermiteFunctionNormConst (n + 1) *
        (Real.sqrt 2 * (↑(n + 1) * (hermiteR n).eval t) * e' +
         (hermiteR (n + 1)).eval t * (-(t / Real.sqrt 2) * e')) =
        hermiteFunctionNormConst (n + 1) / Real.sqrt 2 *
        (Real.sqrt 2 * Real.sqrt 2 * (↑(n + 1) * (hermiteR n).eval t) -
         t * (hermiteR (n + 1)).eval t) * e' := by
        field_simp; ring
      rw [lhs_factor, hsq2, hrec]
      ring
    rw [expand, key1, key2]
    ring
private lemma hermiteFunction_sq_integrable (j : ℕ) :
    Integrable (fun x => hermiteFunction j x * hermiteFunction j x) volume := by
  exact (hermiteFunction_memLp j).integrable_mul (hermiteFunction_memLp j)
private lemma hermiteFunction_l2_sq (j : ℕ) :
    ∫ x, hermiteFunction j x * hermiteFunction j x = 1 := by
  have := hermiteFunction_orthonormal j j
  simp only [ite_true] at this; exact this
private lemma hermiteFunction_deriv_l2_sq (n : ℕ) :
    ∫ x, deriv (hermiteFunction n) x * deriv (hermiteFunction n) x = (2 * ↑n + 1) / 2 := by
  let f_A : ℝ → ℝ := fun x => ↑n / 2 * (hermiteFunction (n - 1) x * hermiteFunction (n - 1) x)
  let f_B : ℝ → ℝ := fun x => ↑(n + 1) / 2 * (hermiteFunction (n + 1) x * hermiteFunction (n + 1) x)
  let f_C : ℝ → ℝ := fun x => 2 * Real.sqrt (↑n / 2) * Real.sqrt (↑(n + 1) / 2) *
      (hermiteFunction (n - 1) x * hermiteFunction (n + 1) x)
  have h_eq : (fun x => deriv (hermiteFunction n) x * deriv (hermiteFunction n) x) =
      fun x => f_A x + f_B x - f_C x := by
    ext x; simp only [f_A, f_B, f_C]
    rw [deriv_hermiteFunction]
    have h1 : Real.sqrt (↑n / 2) * Real.sqrt (↑n / 2) = ↑n / 2 :=
      Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg' n) (by norm_num))
    have h2 : Real.sqrt (↑(n + 1) / 2) * Real.sqrt (↑(n + 1) / 2) = ↑(n + 1) / 2 :=
      Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg' (n+1)) (by norm_num))
    nlinarith [h1, h2]
  rw [h_eq]
  have hA : Integrable f_A := (hermiteFunction_sq_integrable (n - 1)).const_mul _
  have hB : Integrable f_B := (hermiteFunction_sq_integrable (n + 1)).const_mul _
  have hC : Integrable f_C :=
    ((hermiteFunction_memLp (n - 1)).integrable_mul (hermiteFunction_memLp (n + 1))).const_mul _
  have split_add : ∀ (f g : ℝ → ℝ), Integrable f → Integrable g →
      ∫ x, f x + g x = (∫ x, f x) + ∫ x, g x :=
    fun f g hf hg => integral_add hf hg
  have split_sub : ∀ (f g : ℝ → ℝ), Integrable f → Integrable g →
      ∫ x, f x - g x = (∫ x, f x) - ∫ x, g x :=
    fun f g hf hg => integral_sub hf hg
  have step1 : ∫ x, f_A x + f_B x - f_C x =
      ∫ x, f_A x + (f_B x - f_C x) := by congr 1; ext x; ring
  rw [step1]
  simp only [show ∀ x, f_B x - f_C x = (f_B - f_C) x from fun x => rfl]
  rw [split_add _ _ hA (hB.sub hC)]
  simp only [show ∀ x, (f_B - f_C) x = f_B x - f_C x from fun x => rfl]
  rw [split_sub _ _ hB hC]
  simp only [f_A, f_B, f_C, integral_const_mul, hermiteFunction_l2_sq, mul_one]
  have hne : n - 1 ≠ n + 1 := by omega
  rw [hermiteFunction_orthonormal (n - 1) (n + 1), if_neg hne, mul_zero]
  push_cast; ring
private lemma hasDerivAt_hermiteFunction_sq (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t => hermiteFunction n t * hermiteFunction n t)
      (2 * hermiteFunction n x * deriv (hermiteFunction n) x) x := by
  have hd : HasDerivAt (hermiteFunction n) (deriv (hermiteFunction n) x) x :=
    ((hermiteFunction_contDiff n 1).differentiable one_ne_zero x).hasDerivAt
  have := hd.mul hd
  convert this using 1 <;> first | rfl | ring
private lemma deriv_hermiteFunction_memLp (n : ℕ) :
    MemLp (deriv (hermiteFunction n)) 2 volume := by
  have h_eq : deriv (hermiteFunction n) =
      fun x => Real.sqrt (↑n / 2) * hermiteFunction (n - 1) x -
               Real.sqrt (↑(n + 1) / 2) * hermiteFunction (n + 1) x := by
    ext x; exact deriv_hermiteFunction n x
  rw [h_eq]
  exact (hermiteFunction_memLp (n - 1)).const_mul (Real.sqrt (↑n / 2))
    |>.sub ((hermiteFunction_memLp (n + 1)).const_mul (Real.sqrt (↑(n + 1) / 2)))
private lemma integrable_hermiteFunction_mul_deriv (n : ℕ) :
    Integrable (fun x => hermiteFunction n x * deriv (hermiteFunction n) x) volume :=
  (hermiteFunction_memLp n).integrable_mul (deriv_hermiteFunction_memLp n)
private lemma schwartz_tendsto_atBot (φ : SchwartzMap ℝ ℝ) :
    Filter.Tendsto (fun x => φ x) Filter.atBot (nhds 0) := by
  have hza := ZeroAtInftyContinuousMapClass.zero_at_infty φ
  rw [cocompact_eq_atBot_atTop] at hza
  exact hza.mono_left le_sup_left
private lemma schwartz_tendsto_atTop (φ : SchwartzMap ℝ ℝ) :
    Filter.Tendsto (fun x => φ x) Filter.atTop (nhds 0) := by
  have hza := ZeroAtInftyContinuousMapClass.zero_at_infty φ
  rw [cocompact_eq_atBot_atTop] at hza
  exact hza.mono_left le_sup_right
private lemma hermiteFunction_sq_tendsto_atBot (n : ℕ) :
    Filter.Tendsto (fun x => hermiteFunction n x * hermiteFunction n x)
      Filter.atBot (nhds 0) := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz n
  have heq : (fun x => hermiteFunction n x * hermiteFunction n x) =
      fun x => φ x * φ x := by ext x; rw [← hφ x]
  rw [heq, show (0 : ℝ) = 0 * 0 from (mul_zero 0).symm]
  exact (schwartz_tendsto_atBot φ).mul (schwartz_tendsto_atBot φ)
private lemma hermiteFunction_sq_tendsto_atTop (n : ℕ) :
    Filter.Tendsto (fun x => hermiteFunction n x * hermiteFunction n x)
      Filter.atTop (nhds 0) := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz n
  have heq : (fun x => hermiteFunction n x * hermiteFunction n x) =
      fun x => φ x * φ x := by ext x; rw [← hφ x]
  rw [heq, show (0 : ℝ) = 0 * 0 from (mul_zero 0).symm]
  exact (schwartz_tendsto_atTop φ).mul (schwartz_tendsto_atTop φ)
theorem hermiteFunction_sup_bound :
    ∃ (C : ℝ) (s : ℝ), 0 < C ∧ 0 ≤ s ∧
    ∀ (n : ℕ) (x : ℝ), |hermiteFunction n x| ≤ C * (1 + ↑n) ^ s := by
  refine ⟨Real.sqrt 2, 1 / 2, Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2),
    by norm_num, fun n a => ?_⟩
  set f := fun t => hermiteFunction n t * hermiteFunction n t with hf_def
  set f' := fun t => 2 * (hermiteFunction n t * deriv (hermiteFunction n) t) with hf'_def
  have hderiv : ∀ t ∈ Set.Iic a, HasDerivAt f (f' t) t := by
    intro t _
    have := hasDerivAt_hermiteFunction_sq n t
    simp only [hf'_def, mul_assoc] at this ⊢
    exact this
  have hf'_int : IntegrableOn f' (Set.Iic a) volume :=
    ((integrable_hermiteFunction_mul_deriv n).const_mul 2).integrableOn
  have htend : Filter.Tendsto f Filter.atBot (nhds 0) :=
    hermiteFunction_sq_tendsto_atBot n
  have hFTC := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' hderiv hf'_int htend
  have hfa : f a = hermiteFunction n a * hermiteFunction n a := rfl
  rw [sub_zero] at hFTC
  have hf'_abs_int : Integrable (fun t => |f' t|) volume :=
    ((integrable_hermiteFunction_mul_deriv n).const_mul 2).abs
  have h_sq_bound : hermiteFunction n a * hermiteFunction n a ≤ ∫ t, |f' t| := by
    calc hermiteFunction n a * hermiteFunction n a
        = f a := rfl
      _ ≤ |f a| := le_abs_self _
      _ = |∫ t in Set.Iic a, f' t| := by rw [hFTC]
      _ ≤ ∫ t in Set.Iic a, |f' t| := by
          rw [show |∫ t in Set.Iic a, f' t| = ‖∫ t in Set.Iic a, f' t‖ from
              (Real.norm_eq_abs _).symm]
          exact le_trans (norm_integral_le_integral_norm _)
            (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall
              (fun t => Real.norm_eq_abs (f' t)))))
      _ ≤ ∫ t, |f' t| :=
          MeasureTheory.setIntegral_le_integral hf'_abs_int
            (Filter.Eventually.of_forall (fun t => abs_nonneg _))
  have h_amgm : ∀ t : ℝ,
      |f' t| ≤ hermiteFunction n t * hermiteFunction n t +
      deriv (hermiteFunction n) t * deriv (hermiteFunction n) t := by
    intro t
    show |2 * (hermiteFunction n t * deriv (hermiteFunction n) t)| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2), abs_mul]
    have hab := two_mul_le_add_sq (|hermiteFunction n t|) (|deriv (hermiteFunction n) t|)
    rw [mul_assoc] at hab
    calc 2 * (|hermiteFunction n t| * |deriv (hermiteFunction n) t|)
        ≤ |hermiteFunction n t| ^ 2 + |deriv (hermiteFunction n) t| ^ 2 := hab
      _ = hermiteFunction n t * hermiteFunction n t +
          deriv (hermiteFunction n) t * deriv (hermiteFunction n) t := by
          rw [sq_abs, sq_abs]; simp [sq]
  have hderiv_sq_int :
      Integrable (fun x => deriv (hermiteFunction n) x * deriv (hermiteFunction n) x) volume :=
    (deriv_hermiteFunction_memLp n).integrable_mul (deriv_hermiteFunction_memLp n)
  have h_int_bound : ∫ t, |f' t| ≤
      (∫ t, hermiteFunction n t * hermiteFunction n t) +
      (∫ t, deriv (hermiteFunction n) t * deriv (hermiteFunction n) t) := by
    calc ∫ t, |f' t|
        ≤ ∫ t, (hermiteFunction n t * hermiteFunction n t +
                deriv (hermiteFunction n) t * deriv (hermiteFunction n) t) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t => abs_nonneg _))
            ((hermiteFunction_sq_integrable n).add hderiv_sq_int)
            (Filter.Eventually.of_forall h_amgm)
      _ = (∫ t, hermiteFunction n t * hermiteFunction n t) +
          (∫ t, deriv (hermiteFunction n) t * deriv (hermiteFunction n) t) :=
          integral_add (hermiteFunction_sq_integrable n) hderiv_sq_int
  rw [hermiteFunction_l2_sq, hermiteFunction_deriv_l2_sq] at h_int_bound
  have h_sq_final : hermiteFunction n a * hermiteFunction n a ≤ 1 + (2 * ↑n + 1) / 2 :=
    le_trans h_sq_bound h_int_bound
  have h_arith : 1 + (2 * (↑n : ℝ) + 1) / 2 ≤ 2 * (1 + ↑n) := by
    have : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
    linarith
  have h_sq_le : hermiteFunction n a * hermiteFunction n a ≤ 2 * (1 + ↑n) :=
    le_trans h_sq_final h_arith
  have h1n_pos : (0 : ℝ) < 1 + ↑n := by positivity
  have h1n_nonneg : (0 : ℝ) ≤ 1 + ↑n := le_of_lt h1n_pos
  have habs_sq : |hermiteFunction n a| ^ 2 ≤ 2 * (1 + ↑n) := by
    rw [sq_abs, sq]; exact h_sq_le
  have h_abs_le : |hermiteFunction n a| ≤ Real.sqrt (2 * (1 + ↑n)) := by
    rw [← Real.sqrt_sq (abs_nonneg _)]
    exact Real.sqrt_le_sqrt habs_sq
  have h_sqrt_split : Real.sqrt (2 * (1 + ↑n)) = Real.sqrt 2 * Real.sqrt (1 + ↑n) :=
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) _
  rw [h_sqrt_split] at h_abs_le
  conv at h_abs_le => rhs; rw [show Real.sqrt (1 + ↑n) = (1 + ↑n) ^ ((1:ℝ) / 2)
    from Real.sqrt_eq_rpow _]
  exact h_abs_le
private theorem hermiteFunction_pointwise_bound (k m : ℕ) :
    ∃ (C : ℝ) (s : ℝ), 0 < C ∧ 0 ≤ s ∧
    ∀ (n : ℕ) (x : ℝ),
    |x| ^ k * ‖iteratedDeriv m (hermiteFunction n) x‖ ≤
    C * (1 + ↑n) ^ s := by
  induction m with
  | zero =>
    induction k with
    | zero =>
      obtain ⟨C, s, hC, hs, hbound⟩ := hermiteFunction_sup_bound
      exact ⟨C, s, hC, hs, fun n x => by
        simp only [pow_zero, one_mul, iteratedDeriv_zero, Real.norm_eq_abs]
        exact hbound n x⟩
    | succ k ih =>
      obtain ⟨C, s, hC, hs, hbound⟩ := ih
      refine ⟨C * ((2 : ℝ) ^ s + 1), s + 1, by positivity, by linarith, fun n x => ?_⟩
      simp only [iteratedDeriv_zero, Real.norm_eq_abs] at hbound ⊢
      rw [pow_succ, mul_assoc, ← abs_mul]
      rw [mul_x_hermiteFunction]
      have h_tri : |Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
          Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x| ≤
          Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
          Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x| :=
        (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)])
      have h_main : |x| ^ k *
          (Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
           Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x|) ≤
          C * ((2 : ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := by
        have hrearr : |x| ^ k *
            (Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
             Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x|) =
            Real.sqrt ((↑(n + 1) : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n + 1) x|) +
            Real.sqrt ((↑n : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n - 1) x|) := by ring
        rw [hrearr]
        have hb1 := hbound (n + 1) x
        have hb2 := hbound (n - 1) x
        have hsqrt1 : Real.sqrt ((↑(n + 1) : ℝ) / 2) ≤ 1 + (↑n : ℝ) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 + ↑n)]
          apply Real.sqrt_le_sqrt; push_cast
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [sq_nonneg ((n : ℝ) + 1)]
        have hsqrt2 : Real.sqrt ((↑n : ℝ) / 2) ≤ 1 + (↑n : ℝ) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 + ↑n)]
          apply Real.sqrt_le_sqrt
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
        have hrpow1 : (1 + ↑(n + 1) : ℝ) ^ s ≤ (2:ℝ) ^ s * (1 + ↑n) ^ s := by
          rw [← Real.mul_rpow (by positivity : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ 1 + ↑n)]
          apply Real.rpow_le_rpow (by positivity) _ hs; push_cast; linarith
        have hrpow2 : (1 + ↑(n - 1) : ℝ) ^ s ≤ (1 + (↑n : ℝ)) ^ s := by
          apply Real.rpow_le_rpow (by positivity) _ hs
          have : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
          linarith
        have hrpow_split : (1 + (↑n : ℝ)) ^ (s + 1) = (1 + ↑n) ^ s * (1 + ↑n) := by
          rw [Real.rpow_add (by positivity : (0:ℝ) < 1 + ↑n), Real.rpow_one]
        calc Real.sqrt ((↑(n + 1) : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n + 1) x|) +
             Real.sqrt ((↑n : ℝ) / 2) * (|x| ^ k * |hermiteFunction (n - 1) x|)
            ≤ Real.sqrt ((↑(n + 1) : ℝ) / 2) * (C * (1 + ↑(n + 1)) ^ s) +
              Real.sqrt ((↑n : ℝ) / 2) * (C * (1 + ↑(n - 1)) ^ s) := by gcongr
          _ ≤ (1 + ↑n) * (C * ((2:ℝ) ^ s * (1 + ↑n) ^ s)) +
              (1 + ↑n) * (C * (1 + ↑n) ^ s) := by gcongr
          _ = C * ((2:ℝ) ^ s + 1) * ((1 + ↑n) ^ s * (1 + ↑n)) := by ring
          _ = C * ((2:ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := by rw [hrpow_split]
      calc |x| ^ k * |Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
              Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x|
          ≤ |x| ^ k * (Real.sqrt ((↑(n + 1) : ℝ) / 2) * |hermiteFunction (n + 1) x| +
              Real.sqrt ((↑n : ℝ) / 2) * |hermiteFunction (n - 1) x|) := by
            gcongr
        _ ≤ C * ((2 : ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := h_main
  | succ m ih =>
    obtain ⟨C, s, hC, hs, hbound⟩ := ih
    refine ⟨C * ((2 : ℝ) ^ s + 1), s + 1, by positivity, by linarith, fun n x => ?_⟩
    rw [iteratedDeriv_succ']
    have hderiv_eq : deriv (hermiteFunction n) =
        fun x => Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x -
                 Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x := by
      ext x; exact deriv_hermiteFunction n x
    rw [hderiv_eq]
    have hcd1 : ContDiffAt ℝ m (fun x => Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x) x :=
      ((hermiteFunction_contDiff (n - 1) m).const_smul (Real.sqrt ((↑n : ℝ) / 2))).contDiffAt
    have hcd2 : ContDiffAt ℝ m (fun x => Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x) x :=
      ((hermiteFunction_contDiff (n + 1) m).const_smul (Real.sqrt ((↑(n + 1) : ℝ) / 2))).contDiffAt
    rw [iteratedDeriv_fun_sub hcd1 hcd2]
    simp only [iteratedDeriv_const_mul_field]
    have h_tri : ‖Real.sqrt ((↑n : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n - 1)) x -
        Real.sqrt ((↑(n + 1) : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n + 1)) x‖ ≤
        ‖Real.sqrt ((↑n : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n - 1)) x‖ +
        ‖Real.sqrt ((↑(n + 1) : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n + 1)) x‖ :=
      norm_sub_le _ _
    calc |x| ^ k * ‖Real.sqrt ((↑n : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n - 1)) x -
            Real.sqrt ((↑(n + 1) : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n + 1)) x‖
        ≤ |x| ^ k * (‖Real.sqrt ((↑n : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n - 1)) x‖ +
            ‖Real.sqrt ((↑(n + 1) : ℝ) / 2) * iteratedDeriv m (hermiteFunction (n + 1)) x‖) := by
          gcongr
      _ = |x| ^ k * (Real.sqrt ((↑n : ℝ) / 2) * ‖iteratedDeriv m (hermiteFunction (n - 1)) x‖ +
            Real.sqrt ((↑(n + 1) : ℝ) / 2) * ‖iteratedDeriv m (hermiteFunction (n + 1)) x‖) := by
          congr 1
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
              Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ = Real.sqrt ((↑n : ℝ) / 2) * (|x| ^ k * ‖iteratedDeriv m (hermiteFunction (n - 1)) x‖) +
          Real.sqrt ((↑(n + 1) : ℝ) / 2) * (|x| ^ k * ‖iteratedDeriv m (hermiteFunction (n + 1)) x‖) := by
          ring
      _ ≤ Real.sqrt ((↑n : ℝ) / 2) * (C * (1 + ↑(n - 1)) ^ s) +
          Real.sqrt ((↑(n + 1) : ℝ) / 2) * (C * (1 + ↑(n + 1)) ^ s) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hbound (n - 1) x) (Real.sqrt_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hbound (n + 1) x) (Real.sqrt_nonneg _)
      _ ≤ (1 + ↑n) * (C * (1 + ↑n) ^ s) +
          (1 + ↑n) * (C * ((2:ℝ) ^ s * (1 + ↑n) ^ s)) := by
          apply add_le_add
          · apply mul_le_mul _ _ (by positivity) (by positivity)
            · rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 + ↑n)]
              apply Real.sqrt_le_sqrt
              have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              nlinarith [sq_nonneg ((n : ℕ) : ℝ)]
            · apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
              apply Real.rpow_le_rpow (by positivity) _ hs
              have : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := Nat.cast_le.mpr (Nat.sub_le n 1)
              linarith
          · apply mul_le_mul _ _ (by positivity) (by positivity)
            · rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 + ↑n)]
              apply Real.sqrt_le_sqrt; push_cast
              have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              nlinarith [sq_nonneg ((n : ℝ) + 1)]
            · apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
              rw [← Real.mul_rpow (by positivity : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ 1 + ↑n)]
              apply Real.rpow_le_rpow (by positivity) _ hs; push_cast; linarith
      _ = C * ((2:ℝ) ^ s + 1) * ((1 + ↑n) ^ s * (1 + ↑n)) := by ring
      _ = C * ((2:ℝ) ^ s + 1) * (1 + ↑n) ^ (s + 1) := by
          rw [Real.rpow_add (by positivity : (0:ℝ) < 1 + ↑n), Real.rpow_one]
theorem hermiteFunction_seminorm_bound (k m : ℕ) :
    ∃ (C : ℝ) (s : ℝ), 0 < C ∧ 0 ≤ s ∧
    ∀ n : ℕ, SchwartzMap.seminorm ℝ k m
      (Classical.choose (hermiteFunction_schwartz n)) ≤ C * (1 + n) ^ s := by
  obtain ⟨C, s, hC, hs, hbound⟩ := hermiteFunction_pointwise_bound k m
  refine ⟨C, s, hC, hs, fun n => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℝ k m
  · positivity
  · intro x
    have hext : ⇑(Classical.choose (hermiteFunction_schwartz n)) = hermiteFunction n :=
      funext (Classical.choose_spec (hermiteFunction_schwartz n))
    simp only [hext]
    exact hbound n x
theorem sobolevHermite_hs_sum_bound (s : ℝ) (hs : 1/2 < s) :
    ∃ C : ℝ, ∀ N : ℕ, ∑ i ∈ Finset.range N, ((1 + (i : ℝ)) ^ (-2 * s)) ≤ C := by
  have hexp : -2 * s < -1 := by linarith
  have hsumm : Summable (fun i : ℕ => (1 + (i : ℝ)) ^ (-2 * s)) := by
    have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ (-2 * s)) 1).mpr
      (Real.summable_nat_rpow.mpr hexp)
    simp only [Nat.cast_add, Nat.cast_one] at h
    exact h.congr fun m => by rw [add_comm]
  exact ⟨∑' (i : ℕ), (1 + (i : ℝ)) ^ (-2 * s), fun N =>
    hsumm.sum_le_tsum (Finset.range N) (fun i _ =>
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ↑i) _)⟩
private lemma hermiteR_eval_mul_gaussian_eq (n : ℕ) (x : ℝ) :
    (hermiteR n).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2 / 2)) =
    (hermiteFunctionNormConst n)⁻¹ * hermiteFunction n x := by
  unfold hermiteFunction
  rw [show -(x ^ 2 / 2) = -(x ^ 2) / 2 from by ring]
  rw [show hermiteFunctionNormConst n * (hermiteR n).eval (x * Real.sqrt 2) *
    Real.exp (-(x ^ 2) / 2) = hermiteFunctionNormConst n *
    ((hermiteR n).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2) / 2)) from by ring]
  rw [inv_mul_cancel_left₀ (ne_of_gt (normConst_pos n))]
private lemma integral_f_hermiteR_gaussian_zero
    (f : ℝ → ℝ) (_hf : MemLp f 2 volume)
    (horth : ∀ n, ∫ x, f x * hermiteFunction n x = 0)
    (n : ℕ) :
    ∫ x, f x * ((hermiteR n).eval (x * Real.sqrt 2) * Real.exp (-(x ^ 2 / 2))) = 0 := by
  simp_rw [hermiteR_eval_mul_gaussian_eq]
  rw [show (fun x => f x * ((hermiteFunctionNormConst n)⁻¹ * hermiteFunction n x)) =
      fun x => (hermiteFunctionNormConst n)⁻¹ * (f x * hermiteFunction n x) from by ext x; ring]
  rw [integral_const_mul, horth n, mul_zero]
private lemma integral_f_xpow_gaussian_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (horth : ∀ n, ∫ x, f x * hermiteFunction n x = 0) :
    ∀ k : ℕ, ∫ x, f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) = 0 := by
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have h_sqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt h_sqrt2_pos
  have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_pG_memLp : ∀ (p : ℝ[X]),
      MemLp (fun x => p.eval x * Real.exp (-(x ^ 2 / 2))) 2 volume := by
    intro p
    obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz p
    exact MemLp.ae_eq (Filter.Eventually.of_forall hφ) (φ.memLp 2 volume)
  have h_integrable : ∀ (p : ℝ[X]),
      Integrable (fun x => f x * (p.eval x * Real.exp (-(x ^ 2 / 2)))) volume := by
    intro p
    have h_int := L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf) (MemLp.toLp _ (h_pG_memLp p))
    refine h_int.congr ?_
    filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp (h_pG_memLp p)] with x hfx hpGx
    rw [hfx, hpGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial, RCLike.re_to_real]
  have h_mono_integrable : ∀ (c : ℝ) (i : ℕ),
      Integrable (fun x => c * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2))))) volume := by
    intro c i
    have : (fun x : ℝ => c * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2))))) =
        fun x => c * (f x * ((Polynomial.X ^ i).eval x * Real.exp (-(x ^ 2 / 2)))) := by
      ext x; simp [Polynomial.eval_pow, Polynomial.eval_X]
    rw [this]
    exact (h_integrable (Polynomial.X ^ i)).const_mul c
  have h_hermiteR_zero : ∀ n, ∫ x, f x * ((hermiteR n).eval (x * Real.sqrt 2) *
      Real.exp (-(x ^ 2 / 2))) = 0 := integral_f_hermiteR_gaussian_zero f hf horth
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  set Q := (hermiteR k).comp (Polynomial.C (Real.sqrt 2) * Polynomial.X) with hQ_def
  have hQeval : ∀ x : ℝ, Q.eval x = (hermiteR k).eval (x * Real.sqrt 2) := by
    intro x
    simp [hQ_def, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, mul_comm x (Real.sqrt 2)]
  have hR_natDeg : (hermiteR k).natDegree = k :=
    ((hermite_monic k).natDegree_map (Int.castRingHom ℝ)).trans natDegree_hermite
  have hR_monic : (hermiteR k).Monic := (hermite_monic k).map (Int.castRingHom ℝ)
  have hCX_natDeg : (Polynomial.C (Real.sqrt 2) * Polynomial.X).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X _ h_sqrt2_ne
  have hCX_lead : (Polynomial.C (Real.sqrt 2) * Polynomial.X).leadingCoeff = Real.sqrt 2 :=
    Polynomial.leadingCoeff_C_mul_X (Real.sqrt 2)
  have hCX_ne : (Polynomial.C (Real.sqrt 2) * Polynomial.X).natDegree ≠ 0 := by
    rw [hCX_natDeg]; exact one_ne_zero
  have hQ_natDeg : Q.natDegree = k := by
    rw [hQ_def, Polynomial.natDegree_comp, hCX_natDeg, mul_one, hR_natDeg]
  have hQ_lead : Q.leadingCoeff = Real.sqrt 2 ^ k := by
    rw [hQ_def, Polynomial.leadingCoeff_comp hCX_ne, hR_monic, one_mul,
      hCX_lead, hR_natDeg]
  have h_sqrt2_pow_ne : Real.sqrt 2 ^ k ≠ 0 := pow_ne_zero k h_sqrt2_ne
  set R := Q - Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k with hR_def
  have hQR : ∀ x : ℝ, Q.eval x = Real.sqrt 2 ^ k * x ^ k + R.eval x := by
    intro x
    simp [hR_def, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hR_deg : R.natDegree < k ∨ k = 0 := by
    by_cases hk : k = 0
    · right; exact hk
    · left
      rw [hR_def]
      have hmon_deg : (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k).natDegree = k :=
        Polynomial.natDegree_C_mul_X_pow k _ h_sqrt2_pow_ne
      have hmon_lead : (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k).leadingCoeff =
          Real.sqrt 2 ^ k :=
        Polynomial.leadingCoeff_C_mul_X_pow _ _
      have h_cancel : Q.leadingCoeff = (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k).leadingCoeff := by
        rw [hQ_lead, hmon_lead]
      have hQ_ne : Q ≠ 0 := by
        intro h; exact h_sqrt2_pow_ne (hQ_lead ▸ Polynomial.leadingCoeff_eq_zero.mpr h)
      have hmon_ne : Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k ≠ 0 := by
        intro h; exact h_sqrt2_pow_ne (hmon_lead.symm.trans (Polynomial.leadingCoeff_eq_zero.mpr h))
      have h_same_deg : Q.degree = (Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k).degree := by
        rw [Polynomial.degree_eq_natDegree hQ_ne, Polynomial.degree_eq_natDegree hmon_ne,
          hQ_natDeg, hmon_deg]
      have h_deg_lt := Polynomial.degree_sub_lt h_same_deg hQ_ne h_cancel
      rw [Polynomial.degree_eq_natDegree hQ_ne, hQ_natDeg] at h_deg_lt
      by_cases hR_zero : Q - Polynomial.C (Real.sqrt 2 ^ k) * Polynomial.X ^ k = 0
      · rw [hR_zero]; exact Nat.pos_of_ne_zero hk
      · rwa [Polynomial.degree_eq_natDegree hR_zero, Nat.cast_lt] at h_deg_lt
  have h_xpow : ∀ x : ℝ, x ^ k = (Real.sqrt 2 ^ k)⁻¹ * (Q.eval x - R.eval x) := by
    intro x
    have hsub : Q.eval x - R.eval x = Real.sqrt 2 ^ k * x ^ k := by linarith [hQR x]
    rw [hsub, inv_mul_cancel_left₀ h_sqrt2_pow_ne]
  have h_rewrite : ∀ x : ℝ,
      f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) =
      (Real.sqrt 2 ^ k)⁻¹ * (f x * (Q.eval x * Real.exp (-(x ^ 2 / 2)))) -
      (Real.sqrt 2 ^ k)⁻¹ * (f x * (R.eval x * Real.exp (-(x ^ 2 / 2)))) := by
    intro x; rw [h_xpow x]; ring
  simp_rw [h_rewrite]
  rw [integral_sub ((h_integrable Q).const_mul _) ((h_integrable R).const_mul _),
    integral_const_mul, integral_const_mul]
  have hQ_zero : ∫ x, f x * (Q.eval x * Real.exp (-(x ^ 2 / 2))) = 0 := by
    simp_rw [hQeval]; exact h_hermiteR_zero k
  rw [hQ_zero, mul_zero, zero_sub]
  suffices hR_zero : ∫ x, f x * (R.eval x * Real.exp (-(x ^ 2 / 2))) = 0 by
    rw [hR_zero, mul_zero, neg_zero]
  rcases hR_deg with hR_lt | hk0
  · have hR_eval : ∀ x : ℝ, R.eval x * Real.exp (-(x ^ 2 / 2)) =
        ∑ i ∈ Finset.range (R.natDegree + 1),
          R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))) := by
      intro x; rw [Polynomial.eval_eq_sum_range x, Finset.sum_mul]; congr 1; ext i; ring
    have h_eq_sum : ∫ x, f x * (R.eval x * Real.exp (-(x ^ 2 / 2))) =
        ∑ i ∈ Finset.range (R.natDegree + 1),
          R.coeff i * ∫ x, f x * (x ^ i * Real.exp (-(x ^ 2 / 2))) := by
      simp_rw [hR_eval, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => ?_)]
      · congr 1; ext i
        rw [show (fun x => f x * (R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))))) =
          fun x => R.coeff i * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2)))) from by ext x; ring,
          integral_const_mul]
      · show Integrable (fun x => f x * (R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))))) volume
        rw [show (fun x => f x * (R.coeff i * (x ^ i * Real.exp (-(x ^ 2 / 2))))) =
          fun x => R.coeff i * (f x * (x ^ i * Real.exp (-(x ^ 2 / 2)))) from by ext x; ring]
        exact h_mono_integrable _ _
    rw [h_eq_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [ih i (by have := Finset.mem_range.mp hi; omega), mul_zero]
  · subst hk0
    have hQ_const : Q = Polynomial.C 1 := by
      simp [hQ_def, hermiteR, hermite_zero, Polynomial.map_one, Polynomial.one_comp]
    have hR_zero_poly : R = 0 := by simp [hR_def, hQ_const, pow_zero, mul_one]
    simp [hR_zero_poly]
private lemma integral_f_poly_gaussian_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (horth : ∀ n, ∫ x, f x * hermiteFunction n x = 0)
    (P : ℝ[X]) :
    ∫ x, f x * (P.eval x * Real.exp (-(x ^ 2 / 2))) = 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have h_split : (fun x => f x * ((p + q).eval x * Real.exp (-(x ^ 2 / 2)))) =
        (fun x => f x * (p.eval x * Real.exp (-(x ^ 2 / 2))) +
                   f x * (q.eval x * Real.exp (-(x ^ 2 / 2)))) := by
      ext x; simp [Polynomial.eval_add, add_mul, mul_add]
    rw [h_split]
    have h_int_poly : ∀ (r : ℝ[X]),
        Integrable (fun x => f x * (r.eval x * Real.exp (-(x ^ 2 / 2)))) volume := by
      intro r
      obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz r
      have hrG : MemLp (fun x => r.eval x * Real.exp (-(x ^ 2 / 2))) 2 volume :=
        MemLp.ae_eq (Filter.Eventually.of_forall hφ) (φ.memLp 2 volume)
      refine (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf) (MemLp.toLp _ hrG)).congr ?_
      filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hrG] with x hfx hrGx
      rw [hfx, hrGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial, RCLike.re_to_real]
    rw [integral_add (h_int_poly p) (h_int_poly q), hp, hq, add_zero]
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    have h_rw : (fun x => f x * (a * x ^ k * Real.exp (-(x ^ 2 / 2)))) =
        fun x => a * (f x * (x ^ k * Real.exp (-(x ^ 2 / 2)))) := by ext x; ring
    rw [h_rw, integral_const_mul, integral_f_xpow_gaussian_zero f hf horth k, mul_zero]
private lemma integrable_f_mul_gaussian
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    Integrable (fun x => f x * Real.exp (-(x ^ 2 / 2))) volume := by
  obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz (1 : ℝ[X])
  have hG : MemLp (fun x => Real.exp (-(x ^ 2 / 2))) 2 volume := by
    have h1 : MemLp (fun x => (1 : ℝ[X]).eval x * Real.exp (-(x ^ 2 / 2))) 2 volume :=
      MemLp.ae_eq (Filter.Eventually.of_forall hφ) (φ.memLp 2 volume)
    exact MemLp.ae_eq (Filter.Eventually.of_forall (fun x => by simp)) h1
  exact (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf)
    (MemLp.toLp _ hG)).congr
    (by filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hG] with x hfx hGx
        rw [hfx, hGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial, RCLike.re_to_real])
private lemma integrable_f_mul_half_gaussian
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) :
    Integrable (fun x => f x * Real.exp (-(x ^ 2 / 4))) volume := by
  have hG : MemLp (fun x => Real.exp (-(x ^ 2 / 4))) 2 volume := by
    have hmeas : AEStronglyMeasurable (fun x => Real.exp (-(x ^ 2 / 4))) volume :=
      Measurable.aestronglyMeasurable (by fun_prop)
    rw [memLp_two_iff_integrable_sq hmeas]
    have h_sq : (fun x => Real.exp (-(x ^ 2 / 4)) ^ 2) =
        (fun x => Real.exp (-(1/2) * x ^ 2)) := by
      ext x; rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h_sq]
    exact integrable_exp_neg_mul_sq (by positivity)
  exact (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf)
    (MemLp.toLp _ hG)).congr
    (by filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hG] with x hfx hGx
        rw [hfx, hGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial, RCLike.re_to_real])
set_option maxHeartbeats 800000 in
private lemma integrable_g_mul_exp_linear
    (f : ℝ → ℝ) (hf : MemLp f 2 volume) (c : ℝ) :
    Integrable (fun x => ‖f x * Real.exp (-(x ^ 2 / 2))‖ * Real.exp (c * |x|)) volume := by
  have hfg := integrable_f_mul_half_gaussian f hf
  apply (hfg.norm.const_mul (Real.exp (c ^ 2))).mono'
  · apply AEStronglyMeasurable.mul
    · exact (hf.aestronglyMeasurable.mul
        (Measurable.aestronglyMeasurable (by fun_prop))).norm
    · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with x
    have hexp1 : (0 : ℝ) < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
    have hexp2 : (0 : ℝ) < Real.exp (c * |x|) := Real.exp_pos _
    have hexp3 : (0 : ℝ) < Real.exp (-(x ^ 2 / 4)) := Real.exp_pos _
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos hexp1, abs_of_pos hexp2,
      abs_of_pos hexp3, abs_abs]
    calc |f x| * Real.exp (-(x ^ 2 / 2)) * Real.exp (c * |x|)
        = |f x| * Real.exp (-(x ^ 2 / 2) + c * |x|) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ |f x| * Real.exp (c ^ 2 + -(x ^ 2 / 4)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.exp_le_exp_of_le
          nlinarith [sq_nonneg (|x| / 2 - c), sq_abs x]
      _ = Real.exp (c ^ 2) * (|f x| * Real.exp (-(x ^ 2 / 4))) := by
          rw [Real.exp_add]; ring
set_option maxHeartbeats 3200000 in
private lemma fourierIntegral_f_mul_gaussian_eq_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h_moments : ∀ k : ℕ, ∫ x, f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) = 0) :
    ∀ ξ : ℝ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (fun x => (↑(f x * Real.exp (-(x ^ 2 / 2))) : ℂ)) ξ = 0 := by
  intro ξ
  set g : ℝ → ℝ := fun x => f x * Real.exp (-(x ^ 2 / 2)) with hg_def
  set g_ℂ : ℝ → ℂ := fun x => (↑(g x) : ℂ) with hg_ℂ_def
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  set z : ℝ → ℂ := fun x => ↑(-2 * π * innerₗ ℝ x ξ) * Complex.I with hz_def
  let expPartialSum : ℂ → ℕ → ℂ := fun w N =>
    Finset.sum (Finset.range N) fun k => w ^ k / (Nat.factorial k : ℂ)
  let F : ℕ → ℝ → ℂ := fun N x => expPartialSum (z x) N * g_ℂ x
  set target : ℝ → ℂ := fun x => Complex.exp (z x) * g_ℂ x with htarget_def
  have h_pw : ∀ x, Filter.Tendsto (fun N => F N x) Filter.atTop (nhds (target x)) := by
    intro x
    apply Filter.Tendsto.mul_const
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp (z x)).tendsto_sum_nat
  set bound : ℝ → ℝ := fun x => ‖g x‖ * Real.exp (2 * π * |ξ| * |x|) with hbound_def
  have inner_eq : ∀ y : ℝ, innerₗ ℝ y ξ = y * ξ := by
    intro y; rw [innerₗ_apply_apply, real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial,
      RCLike.re_to_real, mul_comm]
  have norm_z : ∀ y : ℝ, ‖z y‖ ≤ 2 * π * |ξ| * |y| := by
    intro y
    simp only [z, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, inner_eq,
      Real.norm_eq_abs]
    have : |-2 * π * (y * ξ)| = 2 * π * |ξ| * |y| := by
      have h1 : (-2 : ℝ) * π * (y * ξ) = -(2 * π * (y * ξ)) := by ring
      rw [h1, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_mul]
      ring
    linarith
  have h_bound : ∀ N, ∀ᵐ x ∂volume, ‖F N x‖ ≤ bound x := by
    intro N
    filter_upwards with x
    show ‖expPartialSum (z x) N * g_ℂ x‖ ≤ _
    have hgn : ‖g_ℂ x‖ = ‖g x‖ := by simp [g_ℂ, Complex.norm_real, Real.norm_eq_abs]
    have h_ps : ‖expPartialSum (z x) N‖ ≤ Real.exp (2 * π * |ξ| * |x|) :=
      calc ‖expPartialSum (z x) N‖
          = ‖∑ k ∈ Finset.range N, z x ^ k / (Nat.factorial k : ℂ)‖ := rfl
        _ ≤ ∑ k ∈ Finset.range N, ‖z x ^ k / (Nat.factorial k : ℂ)‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range N, ‖z x‖ ^ k / (Nat.factorial k) := by
            congr 1; ext k
            rw [norm_div, norm_pow, Complex.norm_natCast]
        _ ≤ Real.exp ‖z x‖ :=
            Real.sum_le_exp_of_nonneg (norm_nonneg _) N
        _ ≤ Real.exp (2 * π * |ξ| * |x|) :=
            Real.exp_le_exp_of_le (norm_z x)
    simp only [hbound_def]
    calc ‖expPartialSum (z x) N * g_ℂ x‖
        ≤ ‖expPartialSum (z x) N‖ * ‖g_ℂ x‖ := norm_mul_le _ _
      _ = ‖expPartialSum (z x) N‖ * ‖g x‖ := by rw [hgn]
      _ ≤ Real.exp (2 * π * |ξ| * |x|) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right h_ps (norm_nonneg _)
      _ = ‖g x‖ * Real.exp (2 * π * |ξ| * |x|) := mul_comm _ _
  have h_bound_int : Integrable bound volume := by
    have key := integrable_g_mul_exp_linear f hf (2 * π * |ξ|)
    exact key.congr (by filter_upwards with x; simp [hbound_def, g, mul_assoc])
  have hg_ℂ_meas : AEStronglyMeasurable g_ℂ volume :=
    RCLike.continuous_ofReal.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop)))
  have hz_cont : Continuous z := by
    simp only [z, inner_eq]
    fun_prop
  have h_summand_cont : ∀ k : ℕ,
      Continuous (fun x : ℝ => z x ^ k / (Nat.factorial k : ℂ)) :=
    fun k => (hz_cont.pow k).div_const _
  have h_meas : ∀ N, AEStronglyMeasurable (F N) volume := by
    intro N
    show AEStronglyMeasurable (fun x => expPartialSum (z x) N * g_ℂ x) volume
    apply AEStronglyMeasurable.mul _ hg_ℂ_meas
    exact Finset.aestronglyMeasurable_fun_sum _ (fun k _ =>
      (h_summand_cont k).measurable.aestronglyMeasurable)
  have h_DCT := tendsto_integral_of_dominated_convergence bound h_meas h_bound_int h_bound
    (Filter.Eventually.of_forall h_pw)
  set c : ℂ := ↑(-2 * π * ξ) * Complex.I with hc_def
  have h_zk : ∀ (k : ℕ) (y : ℝ), z y ^ k = c ^ k * ↑(y ^ k) := by
    intro k y
    simp only [z, innerₗ_apply_apply]
    rw [show @inner ℝ ℝ _ y ξ = y * ξ from by
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, mul_comm]]
    rw [show (↑(-2 * π * (y * ξ)) : ℂ) * Complex.I = c * ↑y from by
      simp only [c]; push_cast; ring]
    rw [mul_pow, Complex.ofReal_pow]
  have h_mono_int : ∀ k : ℕ,
      Integrable (fun y => f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) volume := by
    intro k
    obtain ⟨φ, hφ⟩ := poly_mul_gaussian_schwartz (Polynomial.X ^ k)
    have hpG : MemLp (fun y => y ^ k * Real.exp (-(y ^ 2 / 2))) 2 volume :=
      MemLp.ae_eq (Filter.Eventually.of_forall (fun y => by simp [hφ y, Polynomial.eval_pow,
        Polynomial.eval_X])) (φ.memLp 2 volume)
    exact (L2.integrable_inner (𝕜 := ℝ) (MemLp.toLp f hf) (MemLp.toLp _ hpG)).congr
      (by filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hpG] with x hfx hGx
          rw [hfx, hGx, real_inner_eq_re_inner ℝ, RCLike.inner_apply', conj_trivial,
            RCLike.re_to_real])
  have h_summand_eq : ∀ k : ℕ, (fun y => z y ^ k / (Nat.factorial k : ℂ) * g_ℂ y) =
      fun y => (c ^ k / (Nat.factorial k : ℂ)) *
        (↑(f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) : ℂ) := by
    intro k; ext y; rw [h_zk]; simp only [g_ℂ, g]; push_cast; ring
  have h_summand_int : ∀ k : ℕ,
      Integrable (fun y => z y ^ k / (Nat.factorial k : ℂ) * g_ℂ y) volume := by
    intro k; rw [h_summand_eq]; exact (h_mono_int k).ofReal.const_mul _
  have h_zero : ∀ N, ∫ x, F N x = 0 := by
    intro N
    show ∫ x, expPartialSum (z x) N * g_ℂ x = 0
    simp only [expPartialSum, Finset.sum_mul]
    rw [integral_finsetSum _ (fun k _ => h_summand_int k)]
    apply Finset.sum_eq_zero
    intro k _
    rw [h_summand_eq]
    calc ∫ y, c ^ k / ↑k.factorial * (↑(f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) : ℂ)
        = c ^ k / ↑k.factorial * ∫ y, (↑(f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) : ℂ) :=
          integral_const_mul _ _
      _ = c ^ k / ↑k.factorial * ↑(∫ y, f y * (y ^ k * Real.exp (-(y ^ 2 / 2)))) :=
          congr_arg _ integral_ofReal
      _ = 0 := by rw [h_moments k, Complex.ofReal_zero, mul_zero]
  exact tendsto_nhds_unique h_DCT
    (tendsto_const_nhds.congr (fun N => (h_zero N).symm))
set_option maxHeartbeats 800000 in
private lemma integral_smul_f_mul_gaussian_eq_zero
    (f : ℝ → ℝ) (hf : MemLp f 2 volume)
    (h_moments : ∀ k : ℕ, ∫ x, f x * (x ^ k * Real.exp (-(x ^ 2 / 2))) = 0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, φ x • (f x * Real.exp (-(x ^ 2 / 2))) = 0 := by
  set g : ℝ → ℝ := fun x => f x * Real.exp (-(x ^ 2 / 2)) with hg_def
  set g_ℂ : ℝ → ℂ := fun x => (↑(g x) : ℂ) with hg_ℂ_def
  have hFT := fourierIntegral_f_mul_gaussian_eq_zero f hf h_moments
  have hg_int : Integrable g volume := integrable_f_mul_gaussian f hf
  have hg_ℂ_int : Integrable g_ℂ volume := hg_int.ofReal
  have hφc_ℂ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
  have hφd_ℂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  set ψ : SchwartzMap ℝ ℂ := hφc_ℂ.toSchwartzMap hφd_ℂ
  set η : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ
  have hη_int : Integrable (η : ℝ → ℂ) volume := η.integrable
  have hFF : FourierTransform.fourier η = ψ := FourierTransform.fourier_fourierInv_eq ψ
  have hFT_g : ∀ ξ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      g_ℂ ξ = 0 := fun ξ => hFT ξ
  have hParseval := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (e := Real.fourierChar) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner hη_int hg_ℂ_int
  simp only [flip_innerₗ, hFT_g, smul_zero, integral_zero] at hParseval
  have h_FT_eta : ∀ ξ, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (η : ℝ → ℂ) ξ = (↑(φ ξ) : ℂ) :=
    fun ξ => congr_fun (congr_arg DFunLike.coe hFF) ξ
  simp only [h_FT_eta] at hParseval
  suffices h : (↑(∫ x, φ x • g x) : ℂ) = 0 by exact_mod_cast h
  calc (↑(∫ x, φ x • g x) : ℂ)
      = ∫ x, ((↑(φ x • g x)) : ℂ) := integral_ofReal.symm
    _ = ∫ x, (↑(φ x) : ℂ) • g_ℂ x := by
        congr 1; funext x; simp [hg_ℂ_def, smul_eq_mul, Complex.ofReal_mul]
    _ = 0 := hParseval
private theorem hermiteFunction_complete_proof :
    ∀ f : ℝ → ℝ, MemLp f 2 volume →
    (∀ n, ∫ x, f x * hermiteFunction n x = 0) →
    f =ᵐ[volume] 0 := by
  intro f hf horth
  have h_moments := integral_f_xpow_gaussian_zero f hf horth
  suffices hg : (fun x => f x * Real.exp (-(x ^ 2 / 2))) =ᵐ[volume] 0 by
    filter_upwards [hg] with x hx
    have hexp_pos : Real.exp (-(x ^ 2 / 2)) > 0 := Real.exp_pos _
    exact (mul_eq_zero.mp hx).resolve_right (ne_of_gt hexp_pos)
  have hg_loc : LocallyIntegrable (fun x => f x * Real.exp (-(x ^ 2 / 2))) volume :=
    (integrable_f_mul_gaussian f hf).locallyIntegrable
  exact ae_eq_zero_of_integral_contDiff_smul_eq_zero hg_loc
    (integral_smul_f_mul_gaussian_eq_zero f hf h_moments)
theorem hermiteFunction_complete :
    ∀ f : ℝ → ℝ, MemLp f 2 volume →
    (∀ n, ∫ x, f x * hermiteFunction n x = 0) →
    f =ᵐ[volume] 0 :=
  hermiteFunction_complete_proof
end
end

-- SchwartzNuclear.SchwartzHermiteExpansion
section
open MeasureTheory Real SchwartzMap
open scoped BigOperators
noncomputable section
def schwartzHermiteBasis1D (n : ℕ) : SchwartzMap ℝ ℝ :=
  Classical.choose (hermiteFunction_schwartz n)
theorem schwartzHermiteBasis1D_apply (n : ℕ) (x : ℝ) :
    schwartzHermiteBasis1D n x = hermiteFunction n x :=
  Classical.choose_spec (hermiteFunction_schwartz n) x
theorem schwartzHermiteBasis1D_coe (n : ℕ) :
    ⇑(schwartzHermiteBasis1D n) = hermiteFunction n :=
  funext (schwartzHermiteBasis1D_apply n)
def hermiteCoeff1D (n : ℕ) (f : SchwartzMap ℝ ℝ) : ℝ :=
  ∫ x, f x * hermiteFunction n x
theorem hermiteCoeff1D_eq_integral (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    hermiteCoeff1D n f = ∫ x, f x * hermiteFunction n x := rfl
theorem hermiteCoeff1D_linear (n : ℕ) :
    IsLinearMap ℝ (hermiteCoeff1D n) where
  map_add := by
    intro f g
    simp only [hermiteCoeff1D]
    rw [show (fun x => (f + g) x * hermiteFunction n x) =
        fun x => f x * hermiteFunction n x + g x * hermiteFunction n x from by
      ext x; simp [add_mul]]
    exact integral_add
      ((f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n))
      ((g.memLp 2 volume).integrable_mul (hermiteFunction_memLp n))
  map_smul := by
    intro c f
    simp only [hermiteCoeff1D]
    rw [show (fun x => (c • f) x * hermiteFunction n x) =
        fun x => c * (f x * hermiteFunction n x) from by
      ext x; simp [smul_eq_mul, mul_assoc]]
    exact integral_const_mul c _
private theorem hermiteFunction_differentiable (k : ℕ) : Differentiable ℝ (hermiteFunction k) :=
  (hermiteFunction_contDiff k 1).differentiable_one
private theorem deriv2_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (deriv (hermiteFunction n)) x =
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑(n - 1) : ℝ) / 2) * hermiteFunction (n - 1 - 1) x -
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction n x -
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction n x +
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 2) : ℝ) / 2) * hermiteFunction (n + 2) x := by
  have hderiv_eq : deriv (hermiteFunction n) =
      fun y => Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) y -
               Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) y := by
    ext y; exact deriv_hermiteFunction n y
  set a := Real.sqrt ((↑n : ℝ) / 2)
  set b := Real.sqrt ((↑(n + 1) : ℝ) / 2)
  have hfn_eq : (fun y => a * hermiteFunction (n - 1) y - b * hermiteFunction (n + 1) y) =
      (fun y => a * hermiteFunction (n - 1) y) - (fun y => b * hermiteFunction (n + 1) y) := by
    ext y; simp [Pi.sub_apply]
  rw [hderiv_eq, hfn_eq]
  rw [deriv_sub
        ((hermiteFunction_differentiable _).differentiableAt.const_mul _)
        ((hermiteFunction_differentiable _).differentiableAt.const_mul _)]
  simp only [deriv_const_mul_field]
  rw [deriv_hermiteFunction (n - 1) x, deriv_hermiteFunction (n + 1) x]
  rw [show n + 1 - 1 = n from Nat.succ_sub_one n]
  rw [show n + 1 + 1 = n + 2 from rfl]
  cases n with
  | zero =>
    simp only [a, b, Nat.cast_zero, zero_div, Real.sqrt_zero, zero_mul, neg_zero, zero_sub,
               zero_add, Nat.zero_sub]
    ring
  | succ m =>
    rw [show m + 1 - 1 = m from Nat.succ_sub_one m]
    ring
private theorem x_sq_mul_hermiteFunction (n : ℕ) (x : ℝ) :
    x ^ 2 * hermiteFunction n x =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 2) : ℝ) / 2) * hermiteFunction (n + 2) x +
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction n x +
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction n x +
    Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑(n - 1) : ℝ) / 2) * hermiteFunction (n - 1 - 1) x := by
  have hx2 : x ^ 2 * hermiteFunction n x = x * (x * hermiteFunction n x) := by ring
  rw [hx2, mul_x_hermiteFunction n x]
  have hdist : x * (Real.sqrt ((↑(n + 1) : ℝ) / 2) * hermiteFunction (n + 1) x +
      Real.sqrt ((↑n : ℝ) / 2) * hermiteFunction (n - 1) x) =
    Real.sqrt ((↑(n + 1) : ℝ) / 2) * (x * hermiteFunction (n + 1) x) +
    Real.sqrt ((↑n : ℝ) / 2) * (x * hermiteFunction (n - 1) x) := by ring
  rw [hdist, mul_x_hermiteFunction (n + 1) x, mul_x_hermiteFunction (n - 1) x]
  rw [show n + 1 - 1 = n from Nat.succ_sub_one n]
  rw [show n + 1 + 1 = n + 2 from rfl]
  cases n with
  | zero =>
    simp [Real.sqrt_zero]
    ring
  | succ m =>
    rw [show m + 1 - 1 = m from Nat.succ_sub_one m]
    rw [show m + 1 = m + 1 from rfl]
    ring
theorem hermiteFunction_harmonic_oscillator_eigenvalue (n : ℕ) (x : ℝ) :
    -(iteratedDeriv 2 (hermiteFunction n) x) + x ^ 2 * hermiteFunction n x =
    (2 * ↑n + 1) * hermiteFunction n x := by
  have hiter : iteratedDeriv 2 (hermiteFunction n) x = deriv (deriv (hermiteFunction n)) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [hiter, deriv2_hermiteFunction, x_sq_mul_hermiteFunction]
  have hsq_np1 : Real.sqrt ((↑(n + 1) : ℝ) / 2) * Real.sqrt ((↑(n + 1) : ℝ) / 2) = (↑(n + 1) : ℝ) / 2 :=
    Real.mul_self_sqrt (by positivity)
  have hsq_n : Real.sqrt ((↑n : ℝ) / 2) * Real.sqrt ((↑n : ℝ) / 2) = (↑n : ℝ) / 2 :=
    Real.mul_self_sqrt (by positivity)
  rw [hsq_np1, hsq_n]
  push_cast
  ring
theorem schwartz_integration_by_parts_twice
    (f g : SchwartzMap ℝ ℝ) :
    ∫ x, iteratedDeriv 2 f x * g x = ∫ x, f x * iteratedDeriv 2 g x := by
  have hf2 : ∀ x, iteratedDeriv 2 (⇑f) x = deriv (deriv (⇑f)) x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have hg2 : ∀ x, iteratedDeriv 2 (⇑g) x = deriv (deriv (⇑g)) x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  simp_rw [hf2, hg2]
  have hf' : deriv (⇑f) = ⇑(derivCLM ℝ ℝ f) := by
    ext x; simp [derivCLM_apply]
  have hg' : deriv (⇑g) = ⇑(derivCLM ℝ ℝ g) := by
    ext x; simp [derivCLM_apply]
  rw [hf', hg']
  have ibp1 := integral_mul_deriv_eq_neg_deriv_mul (derivCLM ℝ ℝ f) g
  have lhs_eq : ∫ x, deriv (⇑(derivCLM ℝ ℝ f)) x * g x =
      -(∫ x, (derivCLM ℝ ℝ f) x * deriv (⇑g) x) := by linarith
  have ibp2 := integral_mul_deriv_eq_neg_deriv_mul f (derivCLM ℝ ℝ g)
  simp only [derivCLM_apply] at ibp1 ibp2 lhs_eq ⊢
  linarith
theorem hermiteCoeff_harmonic_oscillator (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    ∫ x, (-(iteratedDeriv 2 f x) + x ^ 2 * f x) * hermiteFunction n x =
    (2 * ↑n + 1) * hermiteCoeff1D n f := by
  set ψ := schwartzHermiteBasis1D n
  have hψ_coe : ⇑ψ = hermiteFunction n := schwartzHermiteBasis1D_coe n
  have hψ_apply : ∀ x, ψ x = hermiteFunction n x := schwartzHermiteBasis1D_apply n
  set f'' : SchwartzMap ℝ ℝ := derivCLM ℝ ℝ (derivCLM ℝ ℝ f)
  set ψ'' : SchwartzMap ℝ ℝ := derivCLM ℝ ℝ (derivCLM ℝ ℝ ψ)
  have hf''_coe : ⇑f'' = deriv (deriv ⇑f) := by
    have h1 : ⇑(derivCLM ℝ ℝ f) = deriv ⇑f := funext (derivCLM_apply (𝕜 := ℝ) f)
    ext x; show f'' x = deriv (deriv ⇑f) x
    change (derivCLM ℝ ℝ (derivCLM ℝ ℝ f)) x = _
    rw [derivCLM_apply (𝕜 := ℝ), h1]
  have hψ''_coe : ⇑ψ'' = deriv (deriv ⇑ψ) := by
    have h1 : ⇑(derivCLM ℝ ℝ ψ) = deriv ⇑ψ := funext (derivCLM_apply (𝕜 := ℝ) ψ)
    ext x; show ψ'' x = deriv (deriv ⇑ψ) x
    change (derivCLM ℝ ℝ (derivCLM ℝ ℝ ψ)) x = _
    rw [derivCLM_apply (𝕜 := ℝ), h1]
  have hf''_eq : ∀ x, iteratedDeriv 2 (⇑f) x = f'' x := by
    intro x; rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]; exact (congrFun hf''_coe x).symm
  have hψ''_iter : ∀ x, iteratedDeriv 2 (hermiteFunction n) x = ψ'' x := by
    intro x; rw [show hermiteFunction n = ⇑ψ from hψ_coe.symm]
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]; exact (congrFun hψ''_coe x).symm
  have hint_f''ψ : Integrable (fun x => iteratedDeriv 2 (⇑f) x * hermiteFunction n x) :=
    ((f''.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)).congr
      (by filter_upwards with x; show f'' x * hermiteFunction n x = _; rw [← hf''_eq])
  have hint_fψ'' : Integrable (fun x => f x * iteratedDeriv 2 (hermiteFunction n) x) :=
    ((f.memLp 2 volume).integrable_mul (ψ''.memLp 2 volume)).congr
      (by filter_upwards with x; show f x * ψ'' x = _; rw [← hψ''_iter])
  have hint_fψ : Integrable (fun x => f x * hermiteFunction n x) := by
    rw [show (fun x => f x * hermiteFunction n x) = (⇑f * hermiteFunction n) from rfl]
    exact (f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)
  have hint_x2fψ : Integrable (fun x => x ^ 2 * f x * hermiteFunction n x) := by
    have heigen : ∀ x, x ^ 2 * f x * hermiteFunction n x =
        (2 * ↑n + 1) * (f x * hermiteFunction n x) + f x * iteratedDeriv 2 (hermiteFunction n) x := by
      intro x
      have h := hermiteFunction_harmonic_oscillator_eigenvalue n x
      have : x ^ 2 * hermiteFunction n x =
          (2 * ↑n + 1) * hermiteFunction n x + iteratedDeriv 2 (hermiteFunction n) x := by linarith
      calc x ^ 2 * f x * hermiteFunction n x
          = f x * (x ^ 2 * hermiteFunction n x) := by ring
        _ = f x * ((2 * ↑n + 1) * hermiteFunction n x + iteratedDeriv 2 (hermiteFunction n) x) := by
            rw [this]
        _ = (2 * ↑n + 1) * (f x * hermiteFunction n x) +
            f x * iteratedDeriv 2 (hermiteFunction n) x := by ring
    simp_rw [heigen]; exact (hint_fψ.const_mul _).add hint_fψ''
  have hibp : ∫ x, iteratedDeriv 2 (⇑f) x * hermiteFunction n x =
      ∫ x, f x * iteratedDeriv 2 (hermiteFunction n) x := by
    have h := schwartz_integration_by_parts_twice f ψ
    simp only [hψ_coe] at h; exact h
  have heigen : ∀ x, x ^ 2 * f x * hermiteFunction n x =
      (2 * ↑n + 1) * (f x * hermiteFunction n x) +
      f x * iteratedDeriv 2 (hermiteFunction n) x := by
    intro x
    have h := hermiteFunction_harmonic_oscillator_eigenvalue n x
    have hx2 : x ^ 2 * hermiteFunction n x =
        (2 * ↑n + 1) * hermiteFunction n x + iteratedDeriv 2 (hermiteFunction n) x := by linarith
    calc x ^ 2 * f x * hermiteFunction n x
        = f x * (x ^ 2 * hermiteFunction n x) := by ring
      _ = f x * ((2 * ↑n + 1) * hermiteFunction n x + iteratedDeriv 2 (hermiteFunction n) x) := by rw [hx2]
      _ = _ := by ring
  have h_integrand : ∀ x, (-(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x) * hermiteFunction n x =
      (2 * ↑n + 1) * (f x * hermiteFunction n x) +
      (f x * iteratedDeriv 2 (hermiteFunction n) x - iteratedDeriv 2 (⇑f) x * hermiteFunction n x) := by
    intro x
    have h1 := heigen x
    have hlhs : (-(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x) * hermiteFunction n x =
        -(iteratedDeriv 2 (⇑f) x * hermiteFunction n x) + x ^ 2 * f x * hermiteFunction n x := by ring
    rw [hlhs, h1]; ring
  simp_rw [h_integrand]
  have hint_main := hint_fψ.const_mul (2 * ↑n + 1)
  have hint_diff : Integrable (fun x => f x * iteratedDeriv 2 (hermiteFunction n) x -
      iteratedDeriv 2 (⇑f) x * hermiteFunction n x) := hint_fψ''.sub hint_f''ψ
  rw [integral_add hint_main hint_diff, integral_const_mul, integral_sub hint_fψ'' hint_f''ψ]
  rw [hibp]; unfold hermiteCoeff1D; linarith
private lemma cauchy_schwarz_integral (f g : ℝ → ℝ) (hf : Integrable (fun x => f x ^ 2))
    (hg : Integrable (fun x => g x ^ 2)) (hfg : Integrable (fun x => f x * g x)) :
    |∫ x, f x * g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  set A := ∫ x, f x ^ 2 with hA_def
  set B := ∫ x, g x ^ 2 with hB_def
  set C := ∫ x, f x * g x with hC_def
  have hA_nn : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  have hB_nn : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  have hquad : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B := by
    intro t
    have hint : Integrable (fun x => (f x + t * g x) ^ 2) := by
      have h1 : (fun x => (f x + t * g x) ^ 2) =
          fun x => f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) := by
        ext x; ring
      rw [h1]; exact hf.add ((hfg.const_mul _).add (hg.const_mul _))
    have h0 : (0 : ℝ) ≤ ∫ x, (f x + t * g x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    have heq : ∫ x, (f x + t * g x) ^ 2 = A + 2 * t * C + t ^ 2 * B := by
      have hint1 : Integrable (fun x => 2 * t * (f x * g x)) := hfg.const_mul _
      have hint2 : Integrable (fun x => t ^ 2 * (g x ^ 2)) := hg.const_mul _
      have h_sq : ∫ x, (f x + t * g x) ^ 2 =
          ∫ x, f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) := by
        congr 1; ext x; ring
      have h_s1 : ∫ x, f x ^ 2 + (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) =
          (∫ x, f x ^ 2) + ∫ x, (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) :=
        integral_add hf (hint1.add hint2)
      have h_s2 : ∫ x, (2 * t * (f x * g x) + t ^ 2 * (g x ^ 2)) =
          (∫ x, 2 * t * (f x * g x)) + ∫ x, t ^ 2 * (g x ^ 2) :=
        integral_add hint1 hint2
      rw [h_sq, h_s1, h_s2, integral_const_mul, integral_const_mul]; ring
    linarith
  by_cases hB : B = 0
  ·
    have hg2_ae : (fun x => g x ^ 2) =ᵐ[MeasureTheory.volume] 0 := by
      rwa [← integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun x => sq_nonneg (g x))) hg]
    have hC0 : C = 0 := by
      have : (fun x => f x * g x) =ᵐ[MeasureTheory.volume] (fun _ => 0) := by
        filter_upwards [hg2_ae] with x hx
        simp only [Pi.zero_apply] at hx
        have := sq_eq_zero_iff.mp hx
        rw [this, mul_zero]
      rw [hC_def, integral_congr_ae this, integral_zero]
    simp [hC0, hB, abs_zero]
  ·
    have hB_pos : 0 < B := lt_of_le_of_ne hB_nn (Ne.symm hB)
    have h := hquad (-C / B)
    have hsimp : A + 2 * (-C / B) * C + (-C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp; ring
    rw [hsimp] at h
    have hCsq : C ^ 2 ≤ A * B := by
      have h1 : C ^ 2 / B ≤ A := by linarith
      calc C ^ 2 = C ^ 2 / B * B := by field_simp
        _ ≤ A * B := by exact mul_le_mul_of_nonneg_right h1 hB_pos.le
    calc |C| = Real.sqrt (C ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hCsq
      _ = Real.sqrt A * Real.sqrt B := by rw [Real.sqrt_mul hA_nn]
private lemma abs_hermiteCoeff1D_le_sqrt_integral_sq (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    |hermiteCoeff1D n f| ≤ Real.sqrt (∫ x, f x ^ 2) := by
  unfold hermiteCoeff1D
  have hint : Integrable (fun x => f x * hermiteFunction n x) :=
    (f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)
  have hf2 : Integrable (fun x => f x ^ 2) := by
    have h := (f.memLp 2 volume).integrable_mul (f.memLp 2 volume)
    exact h.congr (by filter_upwards with x; show f x * f x = f x ^ 2; ring)
  have hψ2 : Integrable (fun x => hermiteFunction n x ^ 2) := by
    have h := (hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp n)
    exact h.congr (by filter_upwards with x; show hermiteFunction n x * hermiteFunction n x = hermiteFunction n x ^ 2; ring)
  have horth : ∫ x, hermiteFunction n x ^ 2 = 1 := by
    have := hermiteFunction_orthonormal n n
    simp at this; convert this using 1; congr 1; ext x; ring
  calc |∫ x, f x * hermiteFunction n x|
      ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, hermiteFunction n x ^ 2) :=
        cauchy_schwarz_integral f (hermiteFunction n) hf2 hψ2 hint
    _ = Real.sqrt (∫ x, f x ^ 2) := by rw [horth, Real.sqrt_one, mul_one]
private lemma hasTemperateGrowth_x_sq :
    Function.HasTemperateGrowth (fun x : ℝ => x ^ 2) := by
  have : (fun x : ℝ => x ^ 2) = fun x => x * x := by ext; ring
  rw [this]; exact Function.HasTemperateGrowth.id'.mul .id'
private def harmonicOscillator : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ) :=
  -(derivCLM ℝ ℝ ∘L derivCLM ℝ ℝ) + smulLeftCLM ℝ (fun x : ℝ => x ^ 2)
private lemma harmonicOscillator_apply (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    harmonicOscillator f x = -(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x := by
  simp only [harmonicOscillator, add_apply, neg_apply,
    ContinuousLinearMap.comp_apply]
  change -(deriv (deriv (⇑f)) x) + (smulLeftCLM ℝ (fun x : ℝ => x ^ 2) f) x =
    -(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x
  rw [smulLeftCLM_apply_apply hasTemperateGrowth_x_sq, smul_eq_mul]
  congr 1
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
private lemma hermiteCoeff1D_harmonicOscillator (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    hermiteCoeff1D n (harmonicOscillator f) = (2 * ↑n + 1) * hermiteCoeff1D n f := by
  unfold hermiteCoeff1D
  have : (fun x => harmonicOscillator f x * hermiteFunction n x) =
      fun x => (-(iteratedDeriv 2 (⇑f) x) + x ^ 2 * f x) * hermiteFunction n x := by
    ext x; rw [harmonicOscillator_apply]
  rw [this]; exact hermiteCoeff_harmonic_oscillator n f
private lemma hermiteCoeff1D_harmonicOscillator_pow :
    ∀ (m n : ℕ) (f : SchwartzMap ℝ ℝ),
    hermiteCoeff1D n ((harmonicOscillator ^ m) f) =
      (2 * ↑n + 1) ^ m * hermiteCoeff1D n f := by
  intro m; induction m with
  | zero => intro n f; simp
  | succ k ih =>
    intro n f
    rw [pow_succ, mul_apply_eq_comp, ih n (harmonicOscillator f),
      hermiteCoeff1D_harmonicOscillator, pow_succ]; ring
private lemma schwartz_l2_le_sup_seminorm :
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      Real.sqrt (∫ x, (f x) ^ 2) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by
  have h_int : Integrable (fun x : ℝ => (1 + ‖x‖) ^ ((-2) : ℝ)) volume :=
    integrable_one_add_norm (by
      rw [show Module.finrank ℝ ℝ = 1 from Module.finrank_self ℝ]; norm_num)
  have hI_nn : 0 ≤ ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ) :=
    integral_nonneg (fun x => rpow_nonneg (by positivity) _)
  refine ⟨(1, 0), 2 * Real.sqrt (∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ)) + 1,
    by linarith [Real.sqrt_nonneg (∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ))], fun f => ?_⟩
  set S := (Finset.Iic (1, 0)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f
  have hS_nn : (0 : ℝ) ≤ S := apply_nonneg _ _
  have hint_f2 : Integrable (fun x => (f x) ^ 2) volume :=
    ((f.memLp 2 volume).integrable_mul (f.memLp 2 volume)).congr
      (by filter_upwards with x; show f x * f x = f x ^ 2; ring)
  have h_pw : ∀ x : ℝ, (f x) ^ 2 ≤ 4 * S ^ 2 * (1 + ‖x‖) ^ ((-2) : ℝ) := by
    intro x
    have hx_pos : (0 : ℝ) < 1 + ‖x‖ := by positivity
    have h := one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (1, 0))
      (k := 1) (n := 0) le_rfl le_rfl f x
    simp only [pow_one, norm_iteratedFDeriv_zero] at h
    have h_rpow_eq : (1 + ‖x‖) ^ ((-2) : ℝ) = ((1 + ‖x‖) ^ 2)⁻¹ := by
      have : (-2 : ℝ) = -(↑(2 : ℕ) : ℝ) := by norm_num
      rw [this, rpow_neg hx_pos.le, rpow_natCast]
    rw [h_rpow_eq]
    rw [← div_eq_mul_inv, le_div_iff₀ (show (0 : ℝ) < (1 + ‖x‖) ^ 2 from by positivity)]
    have h_eq : (f x) ^ 2 * (1 + ‖x‖) ^ 2 = ((1 + ‖x‖) * ‖f x‖) ^ 2 := by
      rw [mul_pow, mul_comm ((1 + ‖x‖) ^ 2)]; congr 1
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_eq]
    calc ((1 + ‖x‖) * ‖f x‖) ^ 2 ≤ (2 * S) ^ 2 :=
          sq_le_sq' (by nlinarith [norm_nonneg (f x)]) (by linarith)
      _ = 4 * S ^ 2 := by ring
  have h_integral : ∫ x, (f x) ^ 2 ≤
      4 * S ^ 2 * ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ) :=
    calc ∫ x, (f x) ^ 2
        ≤ ∫ x, 4 * S ^ 2 * (1 + ‖x‖) ^ ((-2) : ℝ) :=
          integral_mono hint_f2 (h_int.const_mul _) h_pw
      _ = 4 * S ^ 2 * ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ) := integral_const_mul _ _
  set I := ∫ x : ℝ, (1 + ‖x‖) ^ ((-2) : ℝ)
  calc Real.sqrt (∫ x, (f x) ^ 2)
      ≤ Real.sqrt (4 * S ^ 2 * I) := Real.sqrt_le_sqrt h_integral
    _ = Real.sqrt (4 * S ^ 2) * Real.sqrt I := Real.sqrt_mul (by positivity) I
    _ = 2 * S * Real.sqrt I := by
        rw [show (4 : ℝ) * S ^ 2 = (2 * S) ^ 2 from by ring,
          Real.sqrt_sq (by linarith)]
    _ ≤ (2 * Real.sqrt I + 1) * S := by nlinarith [Real.sqrt_nonneg I]
private lemma clm_single_seminorm_bound (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ))
    (k l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : NNReal), C ≠ 0 ∧
      (SchwartzMap.seminorm ℝ k l).comp T.toLinearMap ≤
        C • s.sup (schwartzSeminormFamily ℝ ℝ ℝ) := by
  have hws := schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ)
  set q := (SchwartzMap.seminorm ℝ k l).comp T.toLinearMap
  have hq : Continuous q := by
    show Continuous (fun f => SchwartzMap.seminorm ℝ k l (T f))
    exact (hws.continuous_seminorm (k, l)).comp T.continuous
  exact Seminorm.bound_of_continuous hws q hq
set_option maxHeartbeats 800000 in
private lemma clm_finset_sup_seminorm_bound (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ)) :
    ∀ (S : Finset (ℕ × ℕ)),
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      S.sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) (T f) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by
  intro S
  induction S using Finset.induction with
  | empty =>
    exact ⟨(0, 0), 1, one_pos, fun f => by simp⟩
  | @insert a s ha ih =>
    obtain ⟨q_s, C_s, hC_s, h_s⟩ := ih
    obtain ⟨s_a, C_a, hC_a, hle_a⟩ := clm_single_seminorm_bound T a.1 a.2
    let snf : ℕ × ℕ → Seminorm ℝ (SchwartzMap ℝ ℝ) :=
      fun p => SchwartzMap.seminorm ℝ p.1 p.2
    have h_a : ∀ f : SchwartzMap ℝ ℝ, SchwartzMap.seminorm ℝ a.1 a.2 (T f) ≤
        (C_a : ℝ) * s_a.sup snf f := fun f => by
      have := hle_a f
      simp only [Seminorm.comp_apply, smul_apply, NNReal.smul_def] at this
      exact this
    set q₁ := max q_s.1 (s_a.sup Prod.fst)
    set q₂ := max q_s.2 (s_a.sup Prod.snd)
    refine ⟨(q₁, q₂), max C_s (C_a : ℝ) + 1, by positivity, fun f => ?_⟩
    haveI : SMulCommClass ℝ ℝ (SchwartzMap ℝ ℝ) :=
      ⟨fun r s f => by rw [← mul_smul, ← mul_smul, mul_comm]⟩
    rw [Finset.sup_insert]
    apply sup_le
    ·
      have hsub_a : s_a.sup snf ≤ (Finset.Iic (q₁, q₂)).sup snf := by
        apply Finset.sup_le; intro ⟨i, j⟩ hij
        apply Finset.le_sup (f := snf)
        simp only [Finset.mem_Iic, Prod.le_def]
        exact ⟨le_trans (Finset.le_sup (f := Prod.fst) hij) (le_max_right _ _),
               le_trans (Finset.le_sup (f := Prod.snd) hij) (le_max_right _ _)⟩
      calc snf a (T f)
          ≤ (C_a : ℝ) * s_a.sup snf f := h_a f
        _ ≤ (C_a : ℝ) * (Finset.Iic (q₁, q₂)).sup snf f :=
            mul_le_mul_of_nonneg_left (hsub_a f) (NNReal.coe_nonneg C_a)
        _ ≤ (max C_s (C_a : ℝ) + 1) * (Finset.Iic (q₁, q₂)).sup snf f := by
            gcongr; linarith [le_max_right C_s (C_a : ℝ)]
    ·
      have hsub_s : (Finset.Iic q_s).sup snf ≤ (Finset.Iic (q₁, q₂)).sup snf := by
        apply Finset.sup_le; intro ⟨i, j⟩ hij
        apply Finset.le_sup (f := snf)
        simp only [Finset.mem_Iic, Prod.le_def] at hij ⊢
        exact ⟨le_trans hij.1 (le_max_left _ _), le_trans hij.2 (le_max_left _ _)⟩
      calc s.sup snf (T f)
          ≤ C_s * (Finset.Iic q_s).sup snf f := h_s f
        _ ≤ C_s * (Finset.Iic (q₁, q₂)).sup snf f :=
            mul_le_mul_of_nonneg_left (hsub_s f) (le_of_lt hC_s)
        _ ≤ (max C_s (C_a : ℝ) + 1) * (Finset.Iic (q₁, q₂)).sup snf f := by
            gcongr; linarith [le_max_left C_s (C_a : ℝ)]
private lemma clm_sup_seminorm_bound (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ))
    (q₀ : ℕ × ℕ) :
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) (T f) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f :=
  clm_finset_sup_seminorm_bound T (Finset.Iic q₀)
private lemma pow_clm_sup_seminorm_bound (T : (SchwartzMap ℝ ℝ) →L[ℝ] (SchwartzMap ℝ ℝ))
    (m : ℕ) (q₀ : ℕ × ℕ) :
    ∃ (q : ℕ × ℕ) (C : ℝ), 0 < C ∧ ∀ (f : SchwartzMap ℝ ℝ),
      (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) ((T ^ m) f) ≤
        C * (Finset.Iic q).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f := by
  induction m with
  | zero =>
    exact ⟨q₀, 1, one_pos, fun f => by simp⟩
  | succ k ih =>
    obtain ⟨q_k, C_k, hC_k, h_k⟩ := ih
    obtain ⟨q_T, C_T, hC_T, h_T⟩ := clm_sup_seminorm_bound T q_k
    refine ⟨q_T, C_k * C_T, by positivity, fun f => ?_⟩
    rw [pow_succ, mul_apply_eq_comp]
    calc (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) ((T ^ k) (T f))
        ≤ C_k * (Finset.Iic q_k).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) (T f) :=
          h_k (T f)
      _ ≤ C_k * (C_T * (Finset.Iic q_T).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f) :=
          by gcongr; exact h_T f
      _ = C_k * C_T * (Finset.Iic q_T).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f :=
          by ring
theorem hermiteCoeff1D_decay :
    ∀ k : ℝ, ∃ (C : ℝ) (q : ℕ × ℕ), 0 < C ∧
      ∀ (f : SchwartzMap ℝ ℝ) (n : ℕ),
        |hermiteCoeff1D n f| * (1 + (n : ℝ)) ^ k ≤
          C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  intro k
  obtain ⟨q₀, C₀, hC₀_pos, h_l2⟩ := schwartz_l2_le_sup_seminorm
  set m := ⌈max k 0⌉₊ with hm_def
  obtain ⟨q_H, C_H, hC_H_pos, h_H⟩ := pow_clm_sup_seminorm_bound harmonicOscillator m q₀
  refine ⟨C₀ * C_H, q_H, by positivity, fun f n => ?_⟩
  have h_cs := abs_hermiteCoeff1D_le_sqrt_integral_sq n ((harmonicOscillator ^ m) f)
  have h_l2' := h_l2 ((harmonicOscillator ^ m) f)
  have h_H' := h_H f
  have h_iter : |hermiteCoeff1D n f| * (2 * ↑n + 1) ^ m =
      |hermiteCoeff1D n ((harmonicOscillator ^ m) f)| := by
    rw [hermiteCoeff1D_harmonicOscillator_pow, abs_mul,
      abs_of_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * ↑n + 1) m), mul_comm]
  have h_rpow_le : (1 + (n : ℝ)) ^ k ≤ (2 * ↑n + 1) ^ m := by
    have h1 : (1 : ℝ) ≤ 1 + ↑n := le_add_of_nonneg_right (Nat.cast_nonneg n)
    calc (1 + (n : ℝ)) ^ k
        ≤ (1 + ↑n) ^ (↑m : ℝ) :=
          rpow_le_rpow_of_exponent_le h1
            (le_trans (le_max_left k 0) (Nat.le_ceil (max k 0)))
      _ = (1 + ↑n) ^ m := by rw [rpow_natCast]
      _ ≤ (2 * ↑n + 1) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith) m
  calc |hermiteCoeff1D n f| * (1 + ↑n) ^ k
      ≤ |hermiteCoeff1D n f| * (2 * ↑n + 1) ^ m :=
        mul_le_mul_of_nonneg_left h_rpow_le (abs_nonneg _)
    _ = |hermiteCoeff1D n ((harmonicOscillator ^ m) f)| := h_iter
    _ ≤ Real.sqrt (∫ x, ((harmonicOscillator ^ m) f x) ^ 2) := h_cs
    _ ≤ C₀ * (Finset.Iic q₀).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2)
          ((harmonicOscillator ^ m) f) := h_l2'
    _ ≤ C₀ * (C_H * (Finset.Iic q_H).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f) :=
        by exact mul_le_mul_of_nonneg_left h_H' hC₀_pos.le
    _ = C₀ * C_H * (Finset.Iic q_H).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f :=
        by ring
set_option maxHeartbeats 4000000 in
theorem hermite_expansion_seminorm_summable (f : SchwartzMap ℝ ℝ) (k l : ℕ) :
    Summable (fun n => |hermiteCoeff1D n f| *
      SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)) := by
  obtain ⟨C_h, s, hC_h_pos, _, h_sem⟩ := hermiteFunction_seminorm_bound k l
  obtain ⟨C_d, q, hC_d_pos, h_dec⟩ := hermiteCoeff1D_decay (s + 2)
  have h_rpow : ∀ n : ℕ, (1 + (n : ℝ)) ^ s =
      (1 + (n : ℝ)) ^ (s + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n; rw [← rpow_add (by positivity : (0 : ℝ) < 1 + (n : ℝ))]; congr 1; ring
  set S := (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  set K := C_h * C_d * S with hK_def
  have h_bound : ∀ n : ℕ, |hermiteCoeff1D n f| *
      SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) ≤
      K * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    have h_z_nn : (0 : ℝ) ≤ (1 + (n : ℝ)) ^ ((-2) : ℝ) := rpow_nonneg (by positivity) _
    calc |hermiteCoeff1D n f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)
        ≤ |hermiteCoeff1D n f| * (C_h * (1 + ↑n) ^ s) :=
          mul_le_mul_of_nonneg_left (h_sem n) (abs_nonneg _)
      _ = C_h * (|hermiteCoeff1D n f| * (1 + ↑n) ^ (s + 2)) * (1 + ↑n) ^ ((-2) : ℝ) := by
          rw [h_rpow n]; ring
      _ ≤ C_h * (C_d * S) * (1 + ↑n) ^ ((-2) : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (h_dec f n) hC_h_pos.le) h_z_nn
      _ = K * (1 + ↑n) ^ ((-2) : ℝ) := by rw [hK_def]; ring
  have h_sum : Summable (fun n : ℕ => K * (1 + (n : ℝ)) ^ ((-2) : ℝ)) := by
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    exact h1.const_smul K
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    h_bound h_sum
theorem hermite_expansion_schwartz_seminorm_summable (f : SchwartzMap ℝ ℝ) (k l : ℕ) :
    Summable (fun n => SchwartzMap.seminorm ℝ k l
      (hermiteCoeff1D n f • schwartzHermiteBasis1D n)) := by
  simp_rw [map_smul_eq_mul, Real.norm_eq_abs]
  exact hermite_expansion_seminorm_summable f k l
private lemma schwartz_mul_hermite_integrable (f : SchwartzMap ℝ ℝ) (n : ℕ) :
    Integrable (fun x => f x * hermiteFunction n x) volume :=
  (f.memLp 2 volume).integrable_mul (hermiteFunction_memLp n)
private lemma hermite_mul_hermite_integrable (n m : ℕ) :
    Integrable (fun x => hermiteFunction n x * hermiteFunction m x) volume :=
  (hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp m)
private lemma partial_sum_mul_hermite_integrable (f : SchwartzMap ℝ ℝ) (N m : ℕ) :
    Integrable (fun x => (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x) volume := by
  simp_rw [Finset.sum_mul]
  apply integrable_finsetSum
  intro n _
  exact ((hermite_mul_hermite_integrable n m).const_mul _).congr
    (by filter_upwards with x; ring)
private lemma partial_sum_inner_hermite (f : SchwartzMap ℝ ℝ) (N m : ℕ) (hm : m < N) :
    ∫ x, (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x =
    hermiteCoeff1D m f := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun n _ => by
    exact ((hermite_mul_hermite_integrable n m).const_mul _).congr
      (by filter_upwards with x; ring))]
  simp_rw [show ∀ n, (fun x => hermiteCoeff1D n f * hermiteFunction n x * hermiteFunction m x) =
    (fun x => hermiteCoeff1D n f * (hermiteFunction n x * hermiteFunction m x)) from
    by intro n; ext x; ring]
  simp_rw [integral_const_mul, hermiteFunction_orthonormal]
  simp only [Finset.sum_ite_eq', Finset.mem_range.mpr hm, ite_true, mul_one,
    mul_ite, mul_zero]
private lemma partial_sum_l2_norm_sq (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∫ x, (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) ^ 2 =
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 := by
  have h1 : ∫ x, (∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x) ^ 2 =
      ∫ x, ∑ m ∈ Finset.range N, hermiteCoeff1D m f *
        ((∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x) *
          hermiteFunction m x) := by
    congr 1; ext x; simp only [sq, Finset.mul_sum]; congr 1; ext m; ring
  rw [h1, integral_finsetSum _ (fun m _ =>
    (partial_sum_mul_hermite_integrable f N m).const_mul _)]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [partial_sum_inner_hermite f N m (Finset.mem_range.mp hm), sq]
private lemma cross_term_integral (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∫ x, f x * (∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) =
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun n _ =>
    ((schwartz_mul_hermite_integrable f n).const_mul (hermiteCoeff1D n f)).congr
      (by filter_upwards with x; ring))]
  congr 1; ext n
  rw [show (fun x => f x * (hermiteCoeff1D n f * hermiteFunction n x)) =
    fun x => hermiteCoeff1D n f * (f x * hermiteFunction n x) from by ext x; ring,
    integral_const_mul]; unfold hermiteCoeff1D; ring
private lemma bessel_identity (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∫ x, (f x - ∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) ^ 2 =
    (∫ x, (f x) ^ 2) - ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 := by
  set S := fun x => ∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x
  have hint_f2 : Integrable (fun x => (f x) ^ 2) volume :=
    ((f.memLp 2 volume).integrable_mul (f.memLp 2 volume)).congr
      (by filter_upwards with x; show f x * f x = f x ^ 2; ring)
  have hint_S_memLp : MemLp S 2 volume := by
    apply memLp_finsetSum; intro n _; exact (hermiteFunction_memLp n).const_mul _
  have hint_fS : Integrable (fun x => f x * S x) volume :=
    (f.memLp 2 volume).integrable_mul hint_S_memLp
  have hint_S2 : Integrable (fun x => (S x) ^ 2) volume :=
    (hint_S_memLp.integrable_mul hint_S_memLp).congr
      (by filter_upwards with x; show S x * S x = S x ^ 2; ring)
  have hint_neg2fS : Integrable (fun x => -2 * (f x * S x)) volume :=
    hint_fS.const_mul (-2)
  calc ∫ x, (f x - S x) ^ 2
      = ∫ x, (f x ^ 2 + (-2 * (f x * S x) + S x ^ 2)) := by
        congr 1; ext x; ring
    _ = (∫ x, f x ^ 2) + ∫ x, (-2 * (f x * S x) + S x ^ 2) :=
        integral_add hint_f2 (hint_neg2fS.add hint_S2)
    _ = (∫ x, f x ^ 2) + ((∫ x, -2 * (f x * S x)) + ∫ x, S x ^ 2) :=
        by rw [integral_add hint_neg2fS hint_S2]
    _ = (∫ x, f x ^ 2) + (-2 * (∫ x, f x * S x) + ∫ x, S x ^ 2) :=
        by rw [integral_const_mul]
    _ = (∫ x, f x ^ 2) + (-2 * ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 +
        ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2) := by
        rw [cross_term_integral, partial_sum_l2_norm_sq]
    _ = _ := by ring
private lemma integral_f_sq_nonneg (f : SchwartzMap ℝ ℝ) :
    0 ≤ ∫ x, (f x) ^ 2 :=
  integral_nonneg (fun x => sq_nonneg (f x))
private lemma bessel_inequality (f : SchwartzMap ℝ ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f ^ 2 ≤ ∫ x, (f x) ^ 2 := by
  have h := bessel_identity f N
  have hnn : 0 ≤ ∫ x, (f x - ∑ n ∈ Finset.range N,
      hermiteCoeff1D n f * hermiteFunction n x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith
private lemma hermiteCoeff_sq_summable (f : SchwartzMap ℝ ℝ) :
    Summable (fun n => hermiteCoeff1D n f ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (fun u => by
    calc ∑ x ∈ u, hermiteCoeff1D x f ^ 2
        ≤ ∑ n ∈ Finset.range (u.sup id + 1), hermiteCoeff1D n f ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_range]
            exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
          · intros; exact sq_nonneg _
      _ ≤ ∫ x, (f x) ^ 2 := bessel_inequality f _)
private lemma hermite_series_summable_pointwise (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Summable (fun n => hermiteCoeff1D n f * hermiteFunction n x) := by
  apply Summable.of_norm_bounded (g := fun n => |hermiteCoeff1D n f| *
    SchwartzMap.seminorm ℝ 0 0 (schwartzHermiteBasis1D n))
  · exact hermite_expansion_seminorm_summable f 0 0
  · intro n
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h := SchwartzMap.le_seminorm ℝ 0 0 (schwartzHermiteBasis1D n) x
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
    rwa [schwartzHermiteBasis1D_apply, Real.norm_eq_abs] at h
private lemma hermiteCoeff_abs_summable (f : SchwartzMap ℝ ℝ) :
    Summable (fun n => |hermiteCoeff1D n f|) := by
  obtain ⟨C, q, hC, h_dec⟩ := hermiteCoeff1D_decay 2
  set S := (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have h_bound : ∀ n : ℕ, |hermiteCoeff1D n f| ≤ C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    have h1n_pos : (0 : ℝ) < 1 + ↑n := by positivity
    have h := h_dec f n
    have h2_pos : (0 : ℝ) < (1 + (↑n : ℝ)) ^ (2 : ℝ) := rpow_pos_of_pos h1n_pos 2
    have hle : |hermiteCoeff1D n f| ≤ C * S / (1 + (↑n : ℝ)) ^ (2 : ℝ) :=
      (le_div_iff₀ h2_pos).mpr h
    rw [div_eq_mul_inv, ← rpow_neg h1n_pos.le] at hle; exact hle
  have h_sum : Summable (fun n : ℕ => C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ)) := by
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    exact h1.const_smul (C * S)
  exact .of_nonneg_of_le (fun n => abs_nonneg _) h_bound h_sum
private lemma hermite_series_memLp (f : SchwartzMap ℝ ℝ) :
    MemLp (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) 2 volume := by
  set S : ℕ → ℝ → ℝ := fun N x =>
    ∑ n ∈ Finset.range N, hermiteCoeff1D n f * hermiteFunction n x with hS_def
  have hS_memLp : ∀ N, MemLp (S N) 2 volume := fun N => by
    apply memLp_finsetSum; intro n _; exact (hermiteFunction_memLp n).const_mul _
  have hS_tendsto : ∀ x, Filter.Tendsto (fun N => S N x) Filter.atTop
      (nhds (∑' n, hermiteCoeff1D n f * hermiteFunction n x)) := fun x =>
    (hermite_series_summable_pointwise f x).hasSum.tendsto_sum_nat
  have h_aesm : AEStronglyMeasurable
      (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) volume :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun N => (hS_memLp N).aestronglyMeasurable)
      (ae_of_all _ hS_tendsto)
  refine ⟨h_aesm, ?_⟩
  apply lt_of_le_of_lt
  · exact Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun N => (hS_memLp N).aestronglyMeasurable) _ (ae_of_all _ hS_tendsto)
  have h_lintegral_sq : ∀ (g : ℝ → ℝ) (hg : Integrable (fun x => g x ^ 2) volume),
      ∫⁻ x, ‖g x‖ₑ ^ ENNReal.toReal 2 ∂volume = ENNReal.ofReal (∫ x, g x ^ 2 ∂volume) := by
    intro g hg
    have h_nn : 0 ≤ᵐ[volume] (fun x => g x ^ 2) := ae_of_all _ (fun x => sq_nonneg _)
    simp only [ENNReal.toReal_ofNat]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
    simp_rw [ENNReal.rpow_natCast]
    rw [show (fun x => ‖g x‖ₑ ^ 2) = (fun x => ENNReal.ofReal (g x ^ 2)) from by
      ext x; rw [← enorm_pow, enorm_eq_ofReal (sq_nonneg _)]]
    rw [← ofReal_integral_eq_lintegral_ofReal hg h_nn]
  have h_eLpNorm_le : ∀ N, eLpNorm (S N) 2 volume ≤ eLpNorm f 2 volume := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    rw [h_lintegral_sq (S N) (hS_memLp N).integrable_sq,
        h_lintegral_sq f (f.memLp 2 volume).integrable_sq]
    exact ENNReal.ofReal_le_ofReal (by rw [partial_sum_l2_norm_sq]; exact bessel_inequality f N)
  apply lt_of_le_of_lt
  · apply Filter.liminf_le_of_frequently_le'
    exact Filter.Frequently.of_forall (fun N => h_eLpNorm_le N)
  · exact (f.memLp 2 volume).2
private lemma integral_tsum_mul_hermite (f : SchwartzMap ℝ ℝ) (m : ℕ) :
    ∫ x, (∑' n, hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x =
    ∑' n, ∫ x, hermiteCoeff1D n f * hermiteFunction n x * hermiteFunction m x := by
  conv_lhs => rw [show (fun x => (∑' n, hermiteCoeff1D n f * hermiteFunction n x) *
      hermiteFunction m x) = fun x => ∑' n, (hermiteCoeff1D n f *
      hermiteFunction n x * hermiteFunction m x) from by
    ext x; rw [← tsum_mul_right]]
  rw [integral_tsum
    (fun n => ((hermite_mul_hermite_integrable n m).const_mul _).congr
      (by filter_upwards with x; ring) |>.aestronglyMeasurable)
    (by
      have h_int : ∀ n, Integrable (fun a => hermiteCoeff1D n f *
          hermiteFunction n a * hermiteFunction m a) volume :=
        fun n => ((hermite_mul_hermite_integrable n m).const_mul _).congr
          (by filter_upwards with x; ring)
      have h_summable_nn : Summable (fun n => ‖hermiteCoeff1D n f‖₊) := by
        rw [← NNReal.summable_coe]
        exact (hermiteCoeff_abs_summable f).congr
          (fun n => by simp [coe_nnnorm, Real.norm_eq_abs])
      have hψ_sq : ∀ k, ∫ x, hermiteFunction k x ^ 2 = 1 := fun k => by
        have := hermiteFunction_orthonormal k k
        simp at this; convert this using 1; congr 1; ext x; ring
      have hψ_sq_int : ∀ k, Integrable (fun x => hermiteFunction k x ^ 2) := fun k =>
        ((hermiteFunction_memLp k).integrable_mul (hermiteFunction_memLp k)).congr
          (by filter_upwards with x; show hermiteFunction k x * hermiteFunction k x = _; ring)
      have h_ψψ_norm_le : ∀ n, ∫ a, |hermiteFunction n a * hermiteFunction m a| ≤ 1 := by
        intro n
        calc ∫ a, |hermiteFunction n a * hermiteFunction m a|
            = ∫ a, |hermiteFunction n a| * |hermiteFunction m a| := by
              congr 1; ext a; exact abs_mul _ _
          _ ≤ ∫ a, ((hermiteFunction n a ^ 2 + hermiteFunction m a ^ 2) / 2) := by
              apply integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _))
                ((hψ_sq_int n).add (hψ_sq_int m) |>.div_const 2)
              exact Filter.Eventually.of_forall fun a => by
                simp only [Pi.add_apply]
                have h := two_mul_le_add_sq |hermiteFunction n a| |hermiteFunction m a|
                rw [sq_abs, sq_abs] at h
                linarith
          _ = 1 := by
              rw [integral_div, integral_add (hψ_sq_int n) (hψ_sq_int m), hψ_sq n, hψ_sq m]
              norm_num
      have h_bound : ∀ n, ∫⁻ a, ‖hermiteCoeff1D n f * hermiteFunction n a *
          hermiteFunction m a‖ₑ ≤ ↑‖hermiteCoeff1D n f‖₊ := by
        intro n
        change ∫⁻ a, ↑‖hermiteCoeff1D n f * hermiteFunction n a *
            hermiteFunction m a‖₊ ≤ ↑‖hermiteCoeff1D n f‖₊
        conv_lhs => arg 2; ext a; rw [mul_assoc, nnnorm_mul, ENNReal.coe_mul]
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        suffices h : ∫⁻ a, ↑‖hermiteFunction n a * hermiteFunction m a‖₊ ≤ 1 by
          calc ↑‖hermiteCoeff1D n f‖₊ * ∫⁻ a, ↑‖hermiteFunction n a *
                  hermiteFunction m a‖₊
              ≤ ↑‖hermiteCoeff1D n f‖₊ * 1 := by gcongr
            _ = ↑‖hermiteCoeff1D n f‖₊ := mul_one _
        have hint := hermite_mul_hermite_integrable n m
        calc ∫⁻ a, ↑‖hermiteFunction n a * hermiteFunction m a‖₊
            = ∫⁻ a, ENNReal.ofReal ‖hermiteFunction n a * hermiteFunction m a‖ := by
              congr 1; ext a; exact (ofReal_norm _).symm
          _ = ENNReal.ofReal (∫ a, ‖hermiteFunction n a * hermiteFunction m a‖) := by
              exact (ofReal_integral_eq_lintegral_ofReal hint.norm
                (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).symm
          _ ≤ ENNReal.ofReal 1 :=
              ENNReal.ofReal_le_ofReal (h_ψψ_norm_le n)
          _ = 1 := ENNReal.ofReal_one
      apply ne_top_of_le_ne_top
        (ENNReal.tsum_coe_ne_top_iff_summable.mpr h_summable_nn)
      exact ENNReal.tsum_le_tsum h_bound)]
private lemma hermite_series_eq_f_ae (f : SchwartzMap ℝ ℝ) :
    (fun x => f x - ∑' n, hermiteCoeff1D n f * hermiteFunction n x) =ᵐ[volume] 0 := by
  apply hermiteFunction_complete
  ·
    exact (f.memLp 2 volume).sub (hermite_series_memLp f)
  ·
    intro m
    have hint_fψ := schwartz_mul_hermite_integrable f m
    have hint_Sψ : Integrable (fun x => (∑' n, hermiteCoeff1D n f *
        hermiteFunction n x) * hermiteFunction m x) volume :=
      (hermite_series_memLp f).integrable_mul (hermiteFunction_memLp m)
    rw [show (fun x => (f x - ∑' n, hermiteCoeff1D n f * hermiteFunction n x) *
        hermiteFunction m x) = fun x => f x * hermiteFunction m x -
        (∑' n, hermiteCoeff1D n f * hermiteFunction n x) * hermiteFunction m x from by
      ext x; ring]
    rw [integral_sub hint_fψ hint_Sψ, integral_tsum_mul_hermite]
    simp_rw [show ∀ n, (fun x => hermiteCoeff1D n f * hermiteFunction n x *
        hermiteFunction m x) = fun x => hermiteCoeff1D n f *
        (hermiteFunction n x * hermiteFunction m x) from by intro n; ext x; ring]
    simp_rw [integral_const_mul, hermiteFunction_orthonormal]
    simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq]
    unfold hermiteCoeff1D; ring
set_option maxHeartbeats 800000 in
private lemma parseval_identity (f : SchwartzMap ℝ ℝ) :
    ∫ x, (f x) ^ 2 = ∑' n, hermiteCoeff1D n f ^ 2 := by
  apply le_antisymm
  ·
    have hae := hermite_series_eq_f_ae f
    have h_sq_ae : (fun x => (f x) ^ 2) =ᵐ[volume]
        (fun x => (∑' n, hermiteCoeff1D n f * hermiteFunction n x) ^ 2) := by
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply, sub_eq_zero] at hx; rw [hx]
    rw [integral_congr_ae h_sq_ae]
    set c := fun n => hermiteCoeff1D n f
    set ψ := hermiteFunction
    set T := fun x => ∑' n, c n * ψ n x with hT_def
    set S : ℕ → ℝ → ℝ := fun N x =>
      ∑ n ∈ Finset.range N, c n * ψ n x with hS_def
    have hS_sq_eq : ∀ N, ∫ x, (S N x) ^ 2 =
        ∑ n ∈ Finset.range N, c n ^ 2 := partial_sum_l2_norm_sq f
    have hS_tendsto : ∀ x, Filter.Tendsto (fun N => S N x) Filter.atTop (nhds (T x)) :=
      fun x => (hermite_series_summable_pointwise f x).hasSum.tendsto_sum_nat
    have hc_summable := hermiteCoeff_sq_summable f
    have h_le_tsum : ∀ N, ∫ x, (S N x) ^ 2 ≤ ∑' n, c n ^ 2 := by
      intro N
      rw [hS_sq_eq]
      exact hc_summable.sum_le_tsum _ (fun _ _ => sq_nonneg _)
    have hT_sq_nn : 0 ≤ᵐ[volume] (fun x => (T x) ^ 2) :=
      ae_of_all _ (fun x => sq_nonneg _)
    have hT_sq_int : Integrable (fun x => (T x) ^ 2) volume :=
      ((hermite_series_memLp f).integrable_mul (hermite_series_memLp f)).congr
        (by filter_upwards with x; show T x * T x = T x ^ 2; ring)
    have hS_sq_int : ∀ N, Integrable (fun x => (S N x) ^ 2) volume := by
      intro N
      have hSmemLp : MemLp (S N) 2 volume := by
        apply memLp_finsetSum; intro n _; exact (hermiteFunction_memLp n).const_mul _
      exact (hSmemLp.integrable_mul hSmemLp).congr
        (by filter_upwards with x; show S N x * S N x = S N x ^ 2; ring)
    have hT_sq_aesm : AEStronglyMeasurable (fun x => (T x) ^ 2) volume :=
      hT_sq_int.aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae hT_sq_nn hT_sq_aesm]
    apply ENNReal.toReal_le_of_le_ofReal (tsum_nonneg (fun n => sq_nonneg (c n)))
    calc ∫⁻ x, ENNReal.ofReal ((T x) ^ 2) ∂volume
        = ∫⁻ x, Filter.liminf (fun N => ENNReal.ofReal ((S N x) ^ 2)) Filter.atTop ∂volume := by
          congr 1; ext x
          exact (Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal
            ((Filter.Tendsto.pow (hS_tendsto x) 2)))).symm
      _ ≤ Filter.liminf (fun N => ∫⁻ x, ENNReal.ofReal ((S N x) ^ 2) ∂volume) Filter.atTop := by
          apply lintegral_liminf_le'
          intro N
          exact (hS_sq_int N).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ = Filter.liminf (fun N => ENNReal.ofReal (∫ x, (S N x) ^ 2 ∂volume)) Filter.atTop := by
          congr 1; ext N
          exact (ofReal_integral_eq_lintegral_ofReal (hS_sq_int N)
            (ae_of_all _ (fun x => sq_nonneg _))).symm
      _ = Filter.liminf (fun N => ENNReal.ofReal
            (∑ n ∈ Finset.range N, c n ^ 2)) Filter.atTop := by
          congr 1; ext N; rw [hS_sq_eq]
      _ = ENNReal.ofReal (∑' n, c n ^ 2) := by
          exact Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal
            hc_summable.hasSum.tendsto_sum_nat)
  ·
    exact le_of_tendsto'
      (hermiteCoeff_sq_summable f).hasSum.tendsto_sum_nat
      (fun N => bessel_inequality f N)
theorem hermite_expansion_l2_convergence (f : SchwartzMap ℝ ℝ) :
    Filter.Tendsto
      (fun N => ∫ x, (f x - ∑ n ∈ Finset.range N,
        hermiteCoeff1D n f * hermiteFunction n x) ^ 2)
      Filter.atTop (nhds 0) := by
  simp_rw [bessel_identity f]
  have hparseval := parseval_identity f
  have htend := (hermiteCoeff_sq_summable f).hasSum.tendsto_sum_nat
  rw [show (0 : ℝ) = (∫ x, (f x) ^ 2) - ∑' n, hermiteCoeff1D n f ^ 2 from by
    rw [hparseval]; ring]
  exact Filter.Tendsto.sub tendsto_const_nhds htend
private lemma hermiteFunction_norm_le_seminorm (n : ℕ) (x : ℝ) :
    |hermiteFunction n x| ≤ SchwartzMap.seminorm ℝ 0 0 (schwartzHermiteBasis1D n) := by
  have h := SchwartzMap.le_seminorm ℝ 0 0 (schwartzHermiteBasis1D n) x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
  rwa [schwartzHermiteBasis1D_apply, Real.norm_eq_abs] at h
private lemma iteratedFDeriv_schwartzHermiteBasis1D_eq (n k : ℕ) (x : ℝ) :
    iteratedFDeriv ℝ k (⇑(schwartzHermiteBasis1D n)) x =
    iteratedFDeriv ℝ k (hermiteFunction n) x := by
  exact congr_arg (iteratedFDeriv ℝ k · x) (schwartzHermiteBasis1D_coe n)
private lemma hermite_term_iteratedFDeriv_bound (f : SchwartzMap ℝ ℝ) (k n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => hermiteCoeff1D n f * hermiteFunction n y) x‖ ≤
    |hermiteCoeff1D n f| * SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n) := by
  have hsm : iteratedFDeriv ℝ k (fun y => hermiteCoeff1D n f * hermiteFunction n y) x =
      hermiteCoeff1D n f • iteratedFDeriv ℝ k (hermiteFunction n) x := by
    rw [show (fun y => hermiteCoeff1D n f * hermiteFunction n y) =
      (fun y => hermiteCoeff1D n f • hermiteFunction n y) from by ext; simp [smul_eq_mul]]
    exact iteratedFDeriv_const_smul_apply'
      ((hermiteFunction_contDiff n k).contDiffAt)
  rw [hsm, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by
    have h := SchwartzMap.le_seminorm ℝ 0 k (schwartzHermiteBasis1D n) x
    simp only [pow_zero, one_mul] at h
    rwa [iteratedFDeriv_schwartzHermiteBasis1D_eq] at h) (abs_nonneg _)
private lemma hermite_term_bound_summable (f : SchwartzMap ℝ ℝ) (k : ℕ) :
    Summable (fun n => |hermiteCoeff1D n f| *
      SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n)) :=
  hermite_expansion_seminorm_summable f 0 k
private lemma hermite_series_eq_f_everywhere (f : SchwartzMap ℝ ℝ) :
    ∀ x, f x = ∑' n, hermiteCoeff1D n f * hermiteFunction n x := by
  have hae := hermite_series_eq_f_ae f
  have h_cont : Continuous (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) :=
    continuous_tsum
      (fun n => continuous_const.mul (hermiteFunction_contDiff n 0).continuous)
      (hermite_term_bound_summable f 0)
      (fun n x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hermiteFunction_norm_le_seminorm n x) (abs_nonneg _))
  have hae' : (⇑f) =ᵐ[volume]
      (fun x => ∑' n, hermiteCoeff1D n f * hermiteFunction n x) := by
    filter_upwards [hae] with y hy
    simp only [Pi.zero_apply, sub_eq_zero] at hy; exact hy
  exact congr_fun ((f.continuous.ae_eq_iff_eq volume h_cont).mp hae')
private lemma hermite_series_iteratedFDeriv (f : SchwartzMap ℝ ℝ) (l : ℕ) (x : ℝ) :
    iteratedFDeriv ℝ l (fun y => ∑' n, hermiteCoeff1D n f * hermiteFunction n y) x =
    ∑' n, iteratedFDeriv ℝ l (fun y => hermiteCoeff1D n f * hermiteFunction n y) x := by
  apply iteratedFDeriv_tsum_apply (N := ⊤)
      (v := fun k n => |hermiteCoeff1D n f| * SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n))
  · intro n; exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
  · intro k _; exact hermite_term_bound_summable f k
  · intro k n y _; exact hermite_term_iteratedFDeriv_bound f k n y
  · exact le_top
private lemma schwartz_seminorm_remainder_le (f : SchwartzMap ℝ ℝ) (k l : ℕ)
    (s : Finset ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (h_vanish : ∀ t : Finset ℕ, Disjoint t s →
      ∑ i ∈ t, |hermiteCoeff1D i f| *
        SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D i) ≤ ε) :
    SchwartzMap.seminorm ℝ k l
      (f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i) ≤ ε := by
  apply SchwartzMap.seminorm_le_bound' ℝ k l _ hε
  intro x
  set r := f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i with hr_def
  let g : ℕ → ℝ → ℝ := fun n y => hermiteCoeff1D n f * hermiteFunction n y
  have h_summ_iFD : Summable (fun n => iteratedFDeriv ℝ l (g n) x) := by
    apply Summable.of_norm_bounded
      (g := fun n => |hermiteCoeff1D n f| *
        SchwartzMap.seminorm ℝ 0 l (schwartzHermiteBasis1D n))
    · exact hermite_term_bound_summable f l
    · intro n; exact hermite_term_iteratedFDeriv_bound f l n x
  have h_iFD_f : iteratedFDeriv ℝ l (⇑f) x = ∑' n, iteratedFDeriv ℝ l (g n) x := by
    have hf_eq : ⇑f = fun y => ∑' n, g n y := funext (hermite_series_eq_f_everywhere f)
    rw [hf_eq]; exact hermite_series_iteratedFDeriv f l x
  have hsum_coe : ∀ y, (∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
      ∑ i ∈ s, g i y := by
    intro y
    have : ∀ (t : Finset ℕ), (∑ i ∈ t, hermiteCoeff1D i f • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
        ∑ i ∈ t, g i y := by
      intro t; induction t using Finset.cons_induction with
      | empty => simp
      | cons a t' ha ih => simp [smul_eq_mul,
          schwartzHermiteBasis1D_apply, g]
    exact this s
  have h_iFD_sum : iteratedFDeriv ℝ l
      (⇑(∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ)) x =
      ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
    have hcoe : ⇑(∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) =
        fun y => ∑ i ∈ s, g i y := funext hsum_coe
    rw [hcoe]
    have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
      (fun i _ => (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
    have := congr_fun h_eq x
    simp only [Finset.sum_apply] at this
    exact this
  have h_iFD_r : iteratedFDeriv ℝ l (⇑r) x =
      ∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x := by
    have hf_cd : ContDiff ℝ l (⇑f) := (f.smooth l).of_le le_rfl
    have hg_cd : ContDiff ℝ l (fun y => ∑ i ∈ s, g i y) :=
      ContDiff.sum (fun i _ =>
        (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
    have hcoe_r : (⇑r : ℝ → ℝ) = fun y => f y - ∑ i ∈ s, g i y := by
      ext y; simp only [hr_def, sub_apply]
      exact congrArg (f y - ·) (hsum_coe y)
    rw [hcoe_r]
    set h_sum := fun y => ∑ i ∈ s, g i y with h_sum_def
    have h_neg_cd : ContDiff ℝ l (-h_sum) := hg_cd.neg
    have h_rw : (fun y => f y - h_sum y) = ⇑f + (-h_sum) := by
      ext; simp [sub_eq_add_neg]
    rw [h_rw, iteratedFDeriv_add hf_cd h_neg_cd, Pi.add_apply,
      iteratedFDeriv_neg, Pi.neg_apply, h_iFD_f]
    have h_iFD_h : iteratedFDeriv ℝ l h_sum x = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
      rw [h_sum_def]
      have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
        (fun i _ => (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
      calc iteratedFDeriv ℝ l (fun y => ∑ i ∈ s, g i y) x
          = (∑ j ∈ s, iteratedFDeriv ℝ l (g j)) x := congr_fun h_eq x
        _ = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := Finset.sum_apply x s _
    rw [h_iFD_h]
    rw [← h_summ_iFD.sum_add_tsum_compl (s := s)]
    abel
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm, h_iFD_r]
  have h_norm_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
      ‖iteratedFDeriv ℝ l (g ↑i) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun ⟨n, _⟩ => hermite_term_iteratedFDeriv_bound f l n x)
      ((hermite_term_bound_summable f l).subtype _)
  have h_sem_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
      |hermiteCoeff1D (↑i) f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D (↑i))) :=
    (hermite_expansion_seminorm_summable f k l).subtype _
  have h_ptwise : ∀ (i : ↥(↑s : Set ℕ)ᶜ),
      |x| ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖ ≤
      |hermiteCoeff1D (↑i) f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D (↑i)) := by
    intro ⟨n, _⟩
    have hg_eq : g n = ⇑(hermiteCoeff1D n f • schwartzHermiteBasis1D n) := by
      ext y; simp [g, smul_eq_mul, schwartzHermiteBasis1D_apply]
    rw [hg_eq]
    have h_bound := SchwartzMap.le_seminorm ℝ k l
      (hermiteCoeff1D n f • schwartzHermiteBasis1D n) x
    rw [Real.norm_eq_abs] at h_bound
    calc |x| ^ k * ‖iteratedFDeriv ℝ l
            (⇑(hermiteCoeff1D n f • schwartzHermiteBasis1D n)) x‖
        ≤ SchwartzMap.seminorm ℝ k l
            (hermiteCoeff1D n f • schwartzHermiteBasis1D n) := h_bound
      _ = |hermiteCoeff1D n f| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
  calc |x| ^ k * ‖∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x‖
      ≤ |x| ^ k * ∑' (i : ↥(↑s : Set ℕ)ᶜ), ‖iteratedFDeriv ℝ l (g ↑i) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
          (pow_nonneg (abs_nonneg x) k)
    _ = ∑' (i : ↥(↑s : Set ℕ)ᶜ), (|x| ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖) := by
        rw [tsum_mul_left]
    _ ≤ ∑' (i : ↥(↑s : Set ℕ)ᶜ),
          (|hermiteCoeff1D (↑i) f| *
            SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D (↑i))) :=
        (h_norm_summ.mul_left _).tsum_le_tsum h_ptwise h_sem_summ
    _ ≤ ε := by
        apply h_sem_summ.tsum_le_of_sum_le
        intro t
        set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
        have h_disj : Disjoint t' s := by
          rw [Finset.disjoint_left]
          intro n hn hn_s
          rw [Finset.mem_map] at hn
          obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
          exact hm hn_s
        have h_le := h_vanish t' h_disj
        rw [ht'_def, Finset.sum_map] at h_le
        exact h_le
set_option maxHeartbeats 1600000 in
lemma schwartz_hermite_hasSum (f : SchwartzMap ℝ ℝ) :
    HasSum (fun n => hermiteCoeff1D n f • schwartzHermiteBasis1D n) f := by
  rw [HasSum]
  show Filter.Tendsto _ Filter.atTop _
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ f]
  intro ⟨k, l⟩ ε hε
  have h_sem := hermite_expansion_seminorm_summable f k l
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp h_sem (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs => ?_⟩
  rw [show (∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i) - f =
    -(f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i) from by abel,
    map_neg_eq_map]
  calc SchwartzMap.seminorm ℝ k l
        (f - ∑ i ∈ s, hermiteCoeff1D i f • schwartzHermiteBasis1D i)
      ≤ ε / 2 := by
        apply schwartz_seminorm_remainder_le f k l s (half_pos hε).le
        intro t ht
        have h_disj : Disjoint t s₀ := Disjoint.mono_right hs ht
        have := hs₀ t h_disj
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
          mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at this
        exact le_of_lt this
    _ < ε := half_lt_self hε
theorem schwartz_hermite_expansion_1D :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
       (T : (SchwartzMap ℝ ℝ) →L[ℝ] H) (f : SchwartzMap ℝ ℝ) (w : H),
       @inner ℝ H _ w (T f) =
         ∑' n, hermiteCoeff1D n f * @inner ℝ H _ w (T (schwartzHermiteBasis1D n)) := by
  intro H _ _ _ T f w
  have h_T := (schwartz_hermite_hasSum f).map T T.continuous
  simp only [Function.comp_def, map_smul] at h_T
  have h_inner := h_T.map (innerSL ℝ w) (innerSL ℝ w).continuous
  simp only [Function.comp_def, innerSL_apply_apply, real_inner_smul_right] at h_inner
  exact h_inner.tsum_eq.symm
end
end

-- SchwartzNuclear.Basis1D
section
open MeasureTheory Real SchwartzMap
noncomputable section
def hermiteCoeff1DCLM (n : ℕ) : SchwartzMap ℝ ℝ →L[ℝ] ℝ where
  toLinearMap := {
    toFun := hermiteCoeff1D n
    map_add' := (hermiteCoeff1D_linear n).map_add
    map_smul' := (hermiteCoeff1D_linear n).map_smul
  }
  cont := by
    obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay (0 : ℝ)
    have h0 : ∀ f, |hermiteCoeff1D n f| ≤
        C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
      intro f
      have := hbound f n
      simp only [rpow_zero, mul_one] at this
      exact this
    have key : ∀ f, ‖hermiteCoeff1D n f‖ ≤
        C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
      intro f
      calc ‖hermiteCoeff1D n f‖
          = |hermiteCoeff1D n f| := Real.norm_eq_abs _
        _ ≤ C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := h0 f
    let lm : SchwartzMap ℝ ℝ →ₗ[ℝ] ℝ := {
      toFun := hermiteCoeff1D n
      map_add' := (hermiteCoeff1D_linear n).map_add
      map_smul' := (hermiteCoeff1D_linear n).map_smul
    }
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ ℝ ℝ) (norm_withSeminorms ℝ ℝ) lm
    intro _
    use Finset.Iic q, ⟨C, le_of_lt hC⟩
    exact fun f => key f
@[simp] theorem hermiteCoeff1DCLM_apply (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    hermiteCoeff1DCLM n f = hermiteCoeff1D n f := rfl
theorem schwartz_hermite_expansion_CLF
    (φ : SchwartzMap ℝ ℝ →L[ℝ] ℝ) (f : SchwartzMap ℝ ℝ) :
    φ f = ∑' n, hermiteCoeff1D n f * φ (schwartzHermiteBasis1D n) := by
  have h := @schwartz_hermite_expansion_1D ℝ _ _ _ φ f 1
  have key : ∀ x : ℝ, @inner ℝ ℝ _ 1 x = x := fun x => by
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    simp
  simp only [key] at h
  exact h
private theorem seminorm_le_sup_of_mem {q : ℕ × ℕ} {k' l' : ℕ}
    (hk : k' ≤ q.1) (hl : l' ≤ q.2) (f : SchwartzMap ℝ ℝ) :
    SchwartzMap.seminorm ℝ k' l' f ≤
      2 ^ q.1 * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  apply SchwartzMap.seminorm_le_bound ℝ k' l' f (by positivity)
  intro x
  have hx_le : ‖x‖ ^ k' ≤ (1 + ‖x‖) ^ q.1 :=
    calc ‖x‖ ^ k'
        ≤ (1 + ‖x‖) ^ k' :=
          pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) k'
      _ ≤ (1 + ‖x‖) ^ q.1 :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg x)) hk
  calc ‖x‖ ^ k' * ‖iteratedFDeriv ℝ l' f x‖
      ≤ (1 + ‖x‖) ^ q.1 * ‖iteratedFDeriv ℝ l' f x‖ := by gcongr
    _ ≤ 2 ^ q.1 * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f :=
        SchwartzMap.one_add_le_sup_seminorm_apply le_rfl hl f x
theorem hermiteCoeff1D_decay_single :
    ∀ (k : ℕ), ∃ (C : ℝ) (q : ℕ × ℕ), 0 < C ∧
      ∀ (f : SchwartzMap ℝ ℝ) (n : ℕ),
        |hermiteCoeff1D n f| * (1 + (n : ℝ)) ^ (k : ℝ) ≤
          C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  intro k
  exact hermiteCoeff1D_decay (k : ℝ)
theorem schwartzHermiteBasis1D_growth (k l : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∃ (s : ℕ),
      ∀ m, SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D m) ≤
        C * (1 + (m : ℝ)) ^ s := by
  obtain ⟨C, s, hC, _hs, hbound⟩ := hermiteFunction_seminorm_bound k l
  refine ⟨C, hC, ⌈max s 0⌉₊, fun m => ?_⟩
  calc SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D m)
      = SchwartzMap.seminorm ℝ k l (Classical.choose (hermiteFunction_schwartz m)) := by
        congr 1
    _ ≤ C * (1 + ↑m) ^ s := hbound m
    _ ≤ C * (1 + ↑m) ^ (↑⌈max s 0⌉₊ : ℝ) := by
        gcongr
        · exact le_add_of_nonneg_right (Nat.cast_nonneg m)
        · exact le_trans (le_max_left s 0) (Nat.le_ceil (max s 0))
    _ = C * (1 + ↑m) ^ ⌈max s 0⌉₊ := by rw [rpow_natCast]
end
end

-- Nuclear.DyninMityagin
section
noncomputable section
namespace GaussianField
class DyninMityaginSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] extends T1Space E where
  ι : Type
  p : ι → Seminorm ℝ E
  h_with : WithSeminorms p
  h_countable : Countable ι
  h_completeSpace :
    @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)
  basis : ℕ → E
  coeff : ℕ → (E →L[ℝ] ℝ)
  expansion :
    ∀ (φ : E →L[ℝ] ℝ) (f : E), φ f = ∑' m, (coeff m f) * φ (basis m)
  basis_growth :
    ∀ (i : ι), ∃ C > 0, ∃ (s : ℕ),
    ∀ m, p i (basis m) ≤ C * (1 + (m : ℝ)) ^ s
  coeff_decay :
    ∀ (k : ℕ), ∃ C > 0, ∃ (s : Finset ι),
    ∀ f m, |coeff m f| * (1 + (m : ℝ)) ^ k ≤ C * (s.sup p) f
class DyninMityaginSpace.HasBiorthogonalBasis (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [DyninMityaginSpace E] : Prop where
  coeff_basis : ∀ n m, DyninMityaginSpace.coeff (E := E) n (DyninMityaginSpace.basis m) =
    if n = m then 1 else 0
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
theorem DyninMityaginSpace.expansion_H
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : E →L[ℝ] H) (w : H) (f : E) :
    @inner ℝ H _ w (T f) =
    ∑' m, (DyninMityaginSpace.coeff m f) * @inner ℝ H _ w (T (DyninMityaginSpace.basis m)) := by
  have hφ := DyninMityaginSpace.expansion ((innerSL ℝ w).comp T) f
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hφ
  exact hφ
end GaussianField
end
end

-- Nuclear.NuclearTensorProduct
section
noncomputable section
namespace GaussianField
structure RapidDecaySeq where
  val : ℕ → ℝ
  rapid_decay : ∀ k : ℕ, Summable (fun m => |val m| * (1 + (m : ℝ)) ^ k)
namespace RapidDecaySeq
theorem ext {a b : RapidDecaySeq} (h : ∀ m, a.val m = b.val m) : a = b := by
  cases a; cases b; congr 1; exact funext h
theorem weight_pos (m : ℕ) (k : ℕ) : (0 : ℝ) < (1 + (m : ℝ)) ^ k := by positivity
theorem weight_nonneg (m : ℕ) (k : ℕ) : (0 : ℝ) ≤ (1 + (m : ℝ)) ^ k :=
  le_of_lt (weight_pos m k)
instance instZero : Zero RapidDecaySeq where
  zero := ⟨0, fun k => by simp [summable_zero]⟩
@[simp] theorem zero_val (m : ℕ) : (0 : RapidDecaySeq).val m = 0 := rfl
instance instAdd : Add RapidDecaySeq where
  add a b := ⟨a.val + b.val, fun k => by
    apply Summable.of_nonneg_of_le
    · intro m; exact mul_nonneg (abs_nonneg _) (weight_nonneg m k)
    · intro m; simp only [Pi.add_apply]
      calc |a.val m + b.val m| * (1 + ↑m) ^ k
          ≤ (|a.val m| + |b.val m|) * (1 + ↑m) ^ k :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg m k)
        _ = |a.val m| * (1 + ↑m) ^ k + |b.val m| * (1 + ↑m) ^ k := add_mul _ _ _
    · exact (a.rapid_decay k).add (b.rapid_decay k)⟩
@[simp] theorem add_val (a b : RapidDecaySeq) (m : ℕ) :
    (a + b).val m = a.val m + b.val m := rfl
instance instNeg : Neg RapidDecaySeq where
  neg a := ⟨fun m => -a.val m, fun k => by
    simp only [abs_neg]; exact a.rapid_decay k⟩
@[simp] theorem neg_val (a : RapidDecaySeq) (m : ℕ) : (-a).val m = -a.val m := rfl
instance instSMul : SMul ℝ RapidDecaySeq where
  smul r a := ⟨fun m => r * a.val m, fun k => by
    have h : (fun m => |r * a.val m| * (1 + (m : ℝ)) ^ k) =
             fun m => |r| * (|a.val m| * (1 + (m : ℝ)) ^ k) := by
      ext m; rw [abs_mul, mul_assoc]
    rw [h]
    exact (a.rapid_decay k).const_smul |r|⟩
@[simp] theorem smul_val (r : ℝ) (a : RapidDecaySeq) (m : ℕ) :
    (r • a).val m = r * a.val m := rfl
instance instAddCommGroup : AddCommGroup RapidDecaySeq where
  add_assoc a b c := ext fun m => add_assoc _ _ _
  zero_add a := ext fun m => zero_add _
  add_zero a := ext fun m => add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext fun m => neg_add_cancel _
  add_comm a b := ext fun m => add_comm _ _
instance instModule : Module ℝ RapidDecaySeq where
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _
def rapidDecaySeminorm (k : ℕ) : Seminorm ℝ RapidDecaySeq where
  toFun a := ∑' m, |a.val m| * (1 + (m : ℝ)) ^ k
  map_zero' := by simp [zero_val, tsum_zero]
  add_le' a b := by
    calc ∑' m, |(a + b).val m| * (1 + ↑m) ^ k
        ≤ ∑' m, (|a.val m| * (1 + ↑m) ^ k + |b.val m| * (1 + ↑m) ^ k) := by
          exact ((a + b).rapid_decay k).tsum_le_tsum
            (fun m => by simp only [add_val]
                         calc |a.val m + b.val m| * (1 + ↑m) ^ k
                             ≤ (|a.val m| + |b.val m|) * (1 + ↑m) ^ k :=
                               mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg m k)
                           _ = _ := add_mul _ _ _)
            ((a.rapid_decay k).add (b.rapid_decay k))
      _ = ∑' m, |a.val m| * (1 + ↑m) ^ k + ∑' m, |b.val m| * (1 + ↑m) ^ k :=
          (a.rapid_decay k).tsum_add (b.rapid_decay k)
  neg' a := by
    congr 1; ext m; rw [neg_val, abs_neg]
  smul' r a := by
    show ∑' m, |r * a.val m| * (1 + ↑m) ^ k = ‖r‖ * ∑' m, |a.val m| * (1 + ↑m) ^ k
    simp_rw [abs_mul, Real.norm_eq_abs, mul_assoc]
    exact tsum_mul_left
instance instTopologicalSpace : TopologicalSpace RapidDecaySeq :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℝ) rapidDecaySeminorm).topology
theorem rapidDecay_withSeminorms :
    WithSeminorms (rapidDecaySeminorm : ℕ → Seminorm ℝ RapidDecaySeq) :=
  ⟨rfl⟩
instance instIsTopologicalAddGroup : IsTopologicalAddGroup RapidDecaySeq :=
  rapidDecay_withSeminorms.topologicalAddGroup
instance instContinuousSMul : ContinuousSMul ℝ RapidDecaySeq :=
  rapidDecay_withSeminorms.continuousSMul
private theorem coord_le_seminorm0 (a : RapidDecaySeq) (m : ℕ) :
    |a.val m| ≤ rapidDecaySeminorm 0 a := by
  show |a.val m| ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0
  calc |a.val m|
      = |a.val m| * (1 + (m : ℝ)) ^ 0 := by simp [pow_zero]
    _ ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0 :=
        (a.rapid_decay 0).le_tsum m
          (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))
private theorem finset_sum_le_seminorm (a : RapidDecaySeq) (k : ℕ) (s : Finset ℕ) :
    ∑ m ∈ s, |a.val m| * (1 + (m : ℝ)) ^ k ≤ rapidDecaySeminorm k a :=
  (a.rapid_decay k).sum_le_tsum s (fun m _ => mul_nonneg (abs_nonneg _) (weight_nonneg m k))
private theorem cauchySeq_seminorm_bound
    (u : ℕ → RapidDecaySeq)
    (hu : @CauchySeq RapidDecaySeq ℕ
      (IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq) _ u)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n m, N ≤ n → N ≤ m → rapidDecaySeminorm k (u n - u m) < ε := by
  letI : UniformSpace RapidDecaySeq := IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq
  have h_ent : {p : RapidDecaySeq × RapidDecaySeq | rapidDecaySeminorm k (p.1 - p.2) < ε} ∈
      uniformity RapidDecaySeq := by
    show {p : RapidDecaySeq × RapidDecaySeq | rapidDecaySeminorm k (p.1 - p.2) < ε} ∈
      uniformity RapidDecaySeq
    rw [show uniformity RapidDecaySeq = Filter.comap (fun p : RapidDecaySeq × RapidDecaySeq =>
        p.2 - p.1) (nhds 0) from rfl]
    apply Filter.mem_comap.mpr
    refine ⟨{x | rapidDecaySeminorm k x < ε}, ?_, ?_⟩
    ·
      have h0 : rapidDecaySeminorm k 0 = 0 := map_zero _
      have : {x | rapidDecaySeminorm k x < ε} ∈ nhds (0 : RapidDecaySeq) :=
        (rapidDecay_withSeminorms.continuous_seminorm k).continuousAt.preimage_mem_nhds
          (by rw [h0]; exact Iio_mem_nhds hε)
      exact this
    · intro ⟨a, b⟩ (hx : rapidDecaySeminorm k (b - a) < ε)
      show rapidDecaySeminorm k (a - b) < ε
      rwa [show a - b = -(b - a) from (neg_sub b a).symm, map_neg_eq_map]
  exact hu.mem_entourage h_ent
instance instCompleteSpace :
    @CompleteSpace RapidDecaySeq (IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq) := by
  letI : UniformSpace RapidDecaySeq := IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq
  haveI : IsUniformAddGroup RapidDecaySeq := isUniformAddGroup_of_addCommGroup
  haveI : (nhds (0 : RapidDecaySeq)).IsCountablyGenerated := by
    rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf rapidDecaySeminorm).1
      rapidDecay_withSeminorms]
    exact Filter.iInf.isCountablyGenerated _
  haveI : (uniformity RapidDecaySeq).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  have hcauchy : ∀ k ε, 0 < ε → ∃ N, ∀ n m, N ≤ n → N ≤ m →
      rapidDecaySeminorm k (u n - u m) < ε :=
    fun k ε hε => cauchySeq_seminorm_bound u hu k ε hε
  have coord_cauchy : ∀ m, CauchySeq (fun n => (u n).val m) := by
    intro m
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy 0 ε hε
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      calc |((u n).val m - (u N).val m)|
          = |(u n - u N).val m| := by
            show _ = |((u n) + (-(u N))).val m|; simp [add_val, neg_val, sub_eq_add_neg]
        _ ≤ rapidDecaySeminorm 0 (u n - u N) := coord_le_seminorm0 _ m
        _ < ε := hN n N hn le_rfl⟩
  choose a ha using fun m => cauchySeq_tendsto_of_complete (coord_cauchy m)
  have seminorm_bound : ∀ k, ∃ B, ∀ n, rapidDecaySeminorm k (u n) ≤ B := by
    intro k
    obtain ⟨N, hN⟩ := hcauchy k 1 one_pos
    have h_large : ∀ n, N ≤ n → rapidDecaySeminorm k (u n) ≤
        rapidDecaySeminorm k (u N) + 1 := by
      intro n hn
      calc rapidDecaySeminorm k (u n)
          = rapidDecaySeminorm k ((u n - u N) + u N) := by rw [sub_add_cancel]
        _ ≤ rapidDecaySeminorm k (u n - u N) + rapidDecaySeminorm k (u N) :=
            map_add_le_add _ _ _
        _ ≤ 1 + rapidDecaySeminorm k (u N) := by
            linarith [hN n N hn le_rfl]
        _ = rapidDecaySeminorm k (u N) + 1 := by ring
    let B := (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
        (fun n => rapidDecaySeminorm k (u n)) ⊔ (rapidDecaySeminorm k (u N) + 1)
    refine ⟨B, fun n => ?_⟩
    by_cases hn : N ≤ n
    · exact le_sup_of_le_right (h_large n hn)
    · push Not at hn
      apply le_sup_of_le_left
      exact Finset.le_sup' (fun i => rapidDecaySeminorm k (u i))
        (Finset.mem_range.mpr (by omega))
  have a_rapid : ∀ k, Summable (fun m => |a m| * (1 + (m : ℝ)) ^ k) := by
    intro k
    obtain ⟨B, hB⟩ := seminorm_bound k
    apply summable_of_sum_le (fun m => mul_nonneg (abs_nonneg _) (weight_nonneg m k))
    intro s
    have h_sum_lim : Filter.Tendsto
        (fun n => ∑ m ∈ s, |(u n).val m| * (1 + (m : ℝ)) ^ k)
        Filter.atTop (nhds (∑ m ∈ s, |a m| * (1 + (m : ℝ)) ^ k)) := by
      apply tendsto_finsetSum
      intro m _
      exact (Filter.Tendsto.abs (ha m)).mul tendsto_const_nhds
    have h_sum_le : ∀ n, ∑ m ∈ s, |(u n).val m| * (1 + (m : ℝ)) ^ k ≤ B := by
      intro n
      exact le_trans (finset_sum_le_seminorm (u n) k s) (hB n)
    exact le_of_tendsto h_sum_lim (Filter.Eventually.of_forall h_sum_le)
  let L : RapidDecaySeq := ⟨a, a_rapid⟩
  refine ⟨L, ?_⟩
  rw [rapidDecay_withSeminorms.tendsto_nhds_atTop u L]
  intro k ε hε
  obtain ⟨N, hN⟩ := hcauchy k (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  show rapidDecaySeminorm k (u n - L) < ε
  have h_eq : rapidDecaySeminorm k (u n - L) =
      ∑' m, |(u n).val m - a m| * (1 + (m : ℝ)) ^ k := by
    show ∑' m, |(u n - L).val m| * (1 + (m : ℝ)) ^ k = _
    simp only [sub_eq_add_neg, add_val, neg_val, L]
  rw [h_eq]
  suffices h : ∑' m, |(u n).val m - a m| * (1 + (m : ℝ)) ^ k ≤ ε / 2 by linarith
  apply Real.tsum_le_of_sum_le (fun m => mul_nonneg (abs_nonneg _) (weight_nonneg m k))
  intro s
  have h_lim : Filter.Tendsto
      (fun j => ∑ m ∈ s, |(u n).val m - (u j).val m| * (1 + (m : ℝ)) ^ k)
      Filter.atTop (nhds (∑ m ∈ s, |(u n).val m - a m| * (1 + (m : ℝ)) ^ k)) := by
    apply tendsto_finsetSum
    intro m _
    exact ((tendsto_const_nhds.sub (ha m)).abs).mul tendsto_const_nhds
  apply le_of_tendsto h_lim
  rw [Filter.eventually_atTop]
  refine ⟨N, fun j hj => ?_⟩
  calc ∑ m ∈ s, |(u n).val m - (u j).val m| * (1 + (m : ℝ)) ^ k
      = ∑ m ∈ s, |(u n - u j).val m| * (1 + (m : ℝ)) ^ k := by
        simp only [sub_eq_add_neg, add_val, neg_val]
    _ ≤ rapidDecaySeminorm k (u n - u j) := finset_sum_le_seminorm (u n - u j) k s
    _ ≤ ε / 2 := le_of_lt (hN n j hn hj)
def basisVec (m : ℕ) : RapidDecaySeq where
  val n := if n = m then 1 else 0
  rapid_decay k := by
    apply summable_of_ne_finset_zero (s := {m})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
@[simp] theorem basisVec_val_self (m : ℕ) : (basisVec m).val m = 1 := by
  simp [basisVec]
@[simp] theorem basisVec_val_ne {m n : ℕ} (h : n ≠ m) : (basisVec m).val n = 0 := by
  simp [basisVec, h]
theorem rapidDecaySeminorm_basisVec (k m : ℕ) :
    rapidDecaySeminorm k (basisVec m) = (1 + (m : ℝ)) ^ k := by
  show ∑' n, |(basisVec m).val n| * (1 + (n : ℝ)) ^ k = (1 + (m : ℝ)) ^ k
  rw [tsum_eq_single m]
  · simp [basisVec]
  · intro n hn; simp [basisVec, hn]
def coeffLM (m : ℕ) : RapidDecaySeq →ₗ[ℝ] ℝ where
  toFun a := a.val m
  map_add' a b := rfl
  map_smul' r a := by simp [smul_eq_mul]
def coeffCLM (m : ℕ) : RapidDecaySeq →L[ℝ] ℝ where
  toLinearMap := coeffLM m
  cont := by
    apply WithSeminorms.continuous_of_isBounded rapidDecay_withSeminorms (norm_withSeminorms ℝ ℝ)
    intro _
    refine ⟨{0}, 1, ?_⟩
    intro a
    simp only [Seminorm.comp_apply, Finset.sup_singleton, one_smul,
      coe_normSeminorm, coeffLM, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
    change |a.val m| ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0
    calc |a.val m|
        = |a.val m| * (1 + (m : ℝ)) ^ 0 := by simp [pow_zero]
      _ ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0 :=
          (a.rapid_decay 0).le_tsum m
            (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))
private theorem sum_smul_basisVec_val (a : RapidDecaySeq) (s : Finset ℕ) (n : ℕ) :
    (∑ m ∈ s, a.val m • basisVec m).val n = if n ∈ s then a.val n else 0 := by
  induction s using Finset.induction with
  | empty => simp
  | insert m _ hm ih =>
    rw [Finset.sum_insert hm, add_val, ih]
    simp only [smul_val, basisVec, mul_ite, mul_one, mul_zero, Finset.mem_insert]
    by_cases h : n = m
    · subst h; simp [show n ∉ _ from hm]
    · simp [h]
theorem hasSum_basisVec (a : RapidDecaySeq) :
    HasSum (fun m => a.val m • basisVec m) a := by
  rw [HasSum, (rapidDecay_withSeminorms.tendsto_nhds _ a)]
  intro k ε hε
  simp only [SummationFilter.unconditional_filter]
  set g : ℕ → ℝ := fun n => |a.val n| * (1 + (n : ℝ)) ^ k with hg_def
  have hg_nn : ∀ n, 0 ≤ g n := fun n => mul_nonneg (abs_nonneg _) (weight_nonneg n k)
  have hg_sum : Summable g := a.rapid_decay k
  have hgHS := hg_sum.hasSum
  rw [HasSum, SummationFilter.unconditional_filter] at hgHS
  have h_ev := (tendsto_order.mp hgHS).1 _ (sub_lt_self (∑' n, g n) hε)
  rw [Filter.eventually_atTop] at h_ev ⊢
  obtain ⟨s₀, hs₀⟩ := h_ev
  exact ⟨s₀, fun s hss => by
    have h_partial := hs₀ s hss
    have h_err_terms : ∀ n,
        |((∑ m ∈ s, a.val m • basisVec m) - a).val n| * (1 + ↑n) ^ k =
        if n ∈ s then 0 else g n := by
      intro n
      simp only [sub_eq_add_neg, add_val, neg_val, sum_smul_basisVec_val]
      split <;> simp [g, abs_neg]
    show (rapidDecaySeminorm k) ((∑ m ∈ s, a.val m • basisVec m) - a) < ε
    change ∑' n, |((∑ m ∈ s, a.val m • basisVec m) - a).val n| * (1 + ↑n) ^ k < ε
    simp_rw [h_err_terms]
    have h_compl_summable : Summable (fun n => if (n ∈ s) then (0 : ℝ) else g n) :=
      Summable.of_nonneg_of_le
        (fun n => by split <;> simp [hg_nn])
        (fun n => by split <;> simp [hg_nn])
        hg_sum
    have h_fin_summable : Summable (fun n => if (n ∈ s) then g n else (0 : ℝ)) :=
      summable_of_ne_finset_zero (s := s) (fun n hn => if_neg hn)
    have h_split : ∑' n, g n =
        ∑' n, (if (n ∈ s) then g n else (0 : ℝ)) +
        ∑' n, (if (n ∈ s) then (0 : ℝ) else g n) := by
      rw [← h_fin_summable.tsum_add h_compl_summable]
      congr 1; ext n; split <;> simp
    have h_fin_eq : ∑' n, (if (n ∈ s) then g n else (0 : ℝ)) = ∑ n ∈ s, g n := by
      rw [tsum_eq_sum (fun n hn => if_neg hn)]
      exact Finset.sum_congr rfl (fun n hn => if_pos hn)
    linarith⟩
theorem rapidDecay_expansion (φ : RapidDecaySeq →L[ℝ] ℝ) (a : RapidDecaySeq) :
    φ a = ∑' m, (a.val m) * φ (basisVec m) := by
  have h : HasSum (fun m => φ (a.val m • basisVec m)) (φ a) :=
    (hasSum_basisVec a).mapL φ
  have h' : HasSum (fun m => a.val m * φ (basisVec m)) (φ a) := by
    convert h using 1; ext m; simp [map_smul, smul_eq_mul]
  exact h'.tsum_eq.symm
instance rapidDecay_t1Space : T1Space RapidDecaySeq :=
  rapidDecay_withSeminorms.T1_of_separating fun a ha => by
    refine ⟨0, ?_⟩
    intro h
    apply ha
    have h' : ∑' m, |a.val m| = 0 := by
      have := h; simp only [rapidDecaySeminorm, pow_zero, mul_one] at this; exact this
    have hcomp : ∀ m, a.val m = 0 := by
      intro m
      have hle : |a.val m| ≤ 0 := by
        calc |a.val m| = |a.val m| * (1 + (m : ℝ)) ^ 0 := by simp [pow_zero]
          _ ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0 :=
              (a.rapid_decay 0).le_tsum m
                (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))
          _ = 0 := by simp [pow_zero, mul_one, h']
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    exact RapidDecaySeq.ext hcomp
instance rapidDecay_dyninMityaginSpace : DyninMityaginSpace RapidDecaySeq where
  ι := ℕ
  p := rapidDecaySeminorm
  h_with := rapidDecay_withSeminorms
  h_countable := instCountableNat
  h_completeSpace := instCompleteSpace
  basis := basisVec
  coeff := coeffCLM
  expansion := rapidDecay_expansion
  basis_growth k := ⟨1, one_pos, k, fun m => by
    rw [rapidDecaySeminorm_basisVec]; linarith⟩
  coeff_decay k := ⟨1, one_pos, {k}, fun a m => by
    simp only [Finset.sup_singleton, coeffCLM, ContinuousLinearMap.coe_mk', coeffLM,
      LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    show |a.val m| * (1 + ↑m) ^ k ≤ ∑' n, |a.val n| * (1 + ↑n) ^ k
    exact (a.rapid_decay k).le_tsum m
      (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j k))⟩
instance rapidDecay_hasBiorthogonalBasis :
    DyninMityaginSpace.HasBiorthogonalBasis RapidDecaySeq where
  coeff_basis n m := by
    show (basisVec m).val n = if n = m then 1 else 0
    simp [basisVec]
theorem rapidDecaySeminorm_mono {j j' : ℕ} (hjj : j ≤ j') :
    rapidDecaySeminorm j ≤ rapidDecaySeminorm j' := by
  intro a
  show ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j ≤ ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j'
  apply (a.rapid_decay j).tsum_le_tsum _ (a.rapid_decay j')
  intro m
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg m)) hjj
theorem finset_sup_rapidDecaySeminorm_le (s : Finset ℕ) :
    s.sup rapidDecaySeminorm ≤ rapidDecaySeminorm (s.sup id) := by
  apply Finset.sup_le
  intro j hj
  exact rapidDecaySeminorm_mono (Finset.le_sup (f := id) hj)
theorem finset_sup_rapidDecaySeminorm_basisVec_le (s : Finset ℕ) (m : ℕ) :
    (s.sup rapidDecaySeminorm) (basisVec m) ≤ (1 + (m : ℝ)) ^ (s.sup id) := by
  calc (s.sup rapidDecaySeminorm) (basisVec m)
      ≤ rapidDecaySeminorm (s.sup id) (basisVec m) :=
        finset_sup_rapidDecaySeminorm_le s (basisVec m)
    _ = (1 + (m : ℝ)) ^ (s.sup id) :=
        rapidDecaySeminorm_basisVec _ m
end RapidDecaySeq
noncomputable abbrev DyninMityaginSpace.ofRapidDecayEquiv
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {ι : Type} [Countable ι] (p : ι → Seminorm ℝ E) (hp : WithSeminorms p)
    (equiv : E ≃L[ℝ] RapidDecaySeq) : DyninMityaginSpace E where
  toT1Space := t1Space_of_injective_of_continuous equiv.injective equiv.continuous
  ι := ι
  p := p
  h_with := hp
  h_countable := ‹Countable ι›
  h_completeSpace := by
    letI uE : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    letI uR : UniformSpace RapidDecaySeq :=
      IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq
    haveI : IsUniformAddGroup RapidDecaySeq := isUniformAddGroup_of_addCommGroup
    exact (completeSpace_congr (e := equiv.toLinearEquiv.toEquiv)
      equiv.isUniformEmbedding).2 RapidDecaySeq.instCompleteSpace
  basis m := equiv.symm (RapidDecaySeq.basisVec m)
  coeff m := (RapidDecaySeq.coeffCLM m).comp equiv.toContinuousLinearMap
  expansion φ f := by
    show φ f = ∑' m, (equiv f).val m * φ (equiv.symm (RapidDecaySeq.basisVec m))
    have h := RapidDecaySeq.rapidDecay_expansion
      (φ.comp equiv.symm.toContinuousLinearMap) (equiv f)
    simp only [ContinuousLinearMap.comp_apply] at h
    rwa [show (↑equiv.symm : RapidDecaySeq →L[ℝ] E) (equiv f) = f from
      equiv.symm_apply_apply f] at h
  basis_growth i := by
    set q : Seminorm ℝ RapidDecaySeq := (p i).comp equiv.symm.toLinearMap
    have hq_cont : Continuous q :=
      (hp.continuous_seminorm i).comp equiv.symm.continuous
    obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
      Seminorm.bound_of_continuous RapidDecaySeq.rapidDecay_withSeminorms q hq_cont
    set N := s_fin.sup id
    have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
    refine ⟨(C_nn : ℝ), hC_pos, N, fun m => ?_⟩
    calc p i (equiv.symm (RapidDecaySeq.basisVec m))
        = q (RapidDecaySeq.basisVec m) := rfl
      _ ≤ C_nn • (s_fin.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m) :=
          hle (RapidDecaySeq.basisVec m)
      _ ≤ (C_nn : ℝ) * (1 + (m : ℝ)) ^ N := by
          simp only [NNReal.smul_def, smul_eq_mul]
          exact mul_le_mul_of_nonneg_left
            (RapidDecaySeq.finset_sup_rapidDecaySeminorm_basisVec_le s_fin m)
            (NNReal.coe_nonneg C_nn)
  coeff_decay k := by
    set q : Seminorm ℝ E := (RapidDecaySeq.rapidDecaySeminorm k).comp equiv.toLinearMap
    have hq_cont : Continuous q :=
      (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm k).comp equiv.continuous
    obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
      Seminorm.bound_of_continuous hp q hq_cont
    have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
    refine ⟨(C_nn : ℝ), hC_pos, s_fin, fun f m => ?_⟩
    have h_le_tsum : |(RapidDecaySeq.coeffCLM m (equiv f))| * (1 + (m : ℝ)) ^ k ≤
        RapidDecaySeq.rapidDecaySeminorm k (equiv f) := by
      show |(equiv f).val m| * (1 + (m : ℝ)) ^ k ≤
        ∑' n, |(equiv f).val n| * (1 + (n : ℝ)) ^ k
      exact ((equiv f).rapid_decay k).le_tsum m
        (fun j _ => mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg j k))
    have h_bound : RapidDecaySeq.rapidDecaySeminorm k (equiv f) ≤
        (C_nn : ℝ) * (s_fin.sup p) f := by
      have := hle f
      simp only [smul_apply,
        NNReal.smul_def, smul_eq_mul] at this
      exact this
    show |(RapidDecaySeq.coeffCLM m (equiv f))| * (1 + (m : ℝ)) ^ k ≤
      (C_nn : ℝ) * (s_fin.sup p) f
    exact le_trans h_le_tsum h_bound
theorem DyninMityaginSpace.ofRapidDecayEquiv_hasBiorthogonalBasis
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {ι : Type} [Countable ι] (p : ι → Seminorm ℝ E) (hp : WithSeminorms p)
    (equiv : E ≃L[ℝ] RapidDecaySeq) :
    letI := DyninMityaginSpace.ofRapidDecayEquiv p hp equiv
    DyninMityaginSpace.HasBiorthogonalBasis E :=
  letI := DyninMityaginSpace.ofRapidDecayEquiv p hp equiv
  { coeff_basis := fun n m => by
      show RapidDecaySeq.coeffCLM n (equiv (equiv.symm (RapidDecaySeq.basisVec m))) =
        if n = m then 1 else 0
      rw [ContinuousLinearEquiv.apply_symm_apply]
      show (RapidDecaySeq.basisVec m).val n = if n = m then 1 else 0
      simp [RapidDecaySeq.basisVec, eq_comm] }
theorem nat_pair_bound (n m : ℕ) : Nat.pair n m ≤ (n + m + 1) ^ 2 := by
  have hpair : Nat.pair n m ≤ (max n m + 1) ^ 2 :=
    Nat.le_of_lt (Nat.pair_lt_max_add_one_sq n m)
  have hmax : max n m + 1 ≤ n + m + 1 := by
    exact Nat.succ_le_succ (max_le (Nat.le_add_right n m) (Nat.le_add_left m n))
  exact hpair.trans (Nat.pow_le_pow_left hmax 2)
theorem nat_unpair_le (p : ℕ) : (Nat.unpair p).1 ≤ p ∧ (Nat.unpair p).2 ≤ p :=
  ⟨Nat.unpair_left_le p, Nat.unpair_right_le p⟩
end GaussianField
end
end

-- SchwartzNuclear.ParametricCalculus
section
open MeasureTheory SchwartzMap
open scoped ContDiff
private noncomputable def curryLeftLIE {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :=
  let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm
  @LinearIsometryEquiv.mk ℝ ℝ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ _
    (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F)
    NormedAddCommGroup.toSeminormedAddCommGroup
    NormedAddCommGroup.toSeminormedAddCommGroup
    NormedSpace.toModule NormedSpace.toModule
    L.toLinearEquiv L.norm_map'
private lemma curryLeftLIE_coe_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :
    ⇑(curryLeftLIE (E := E) (F := F) k) =
    ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm := rfl
lemma norm_iteratedFDeriv_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (n l' : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ l' f) z‖ =
      ‖iteratedFDeriv ℝ (n + l') f z‖ := by
  revert n
  induction l' with
  | zero =>
    intro n
    simp only [Nat.add_zero]
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.norm_iteratedFDeriv_comp_left f z n
  | succ k ih =>
    intro n
    rw [iteratedFDeriv_succ_eq_comp_left (f := f) (n := k)]
    rw [show ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm =
      ⇑(curryLeftLIE (E := E) (F := F) k) from (curryLeftLIE_coe_eq k).symm]
    rw [(curryLeftLIE k).norm_iteratedFDeriv_comp_left]
    rw [norm_iteratedFDeriv_fderiv]
    rw [ih (n + 1)]
    conv_lhs => rw [show n + 1 + k = n + (k + 1) from by omega]
lemma contDiff_schwartz_parametric_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : SchwartzMap E ℝ) (g : SchwartzMap ℝ ℝ)
    (ι : H → ℝ → E)
    (hι_smooth : ∀ t, ContDiff ℝ ∞ (ι · t))
    (hι_meas : ∀ (m : ℕ) (y : H), AEStronglyMeasurable
      (fun t => iteratedFDeriv ℝ m (fun y' => f (ι y' t)) y) volume)
    (hι_bound : ∀ m : ℕ, ∃ C : ℝ, ∀ y t,
      ‖iteratedFDeriv ℝ m (fun y' => f (ι y' t)) y‖ ≤ C) :
    ContDiff ℝ ∞ (fun y => ∫ t, f (ι y t) * g t) ∧
    ∀ (m : ℕ) (y : H),
      iteratedFDeriv ℝ m (fun y' => ∫ t, f (ι y' t) * g t) y =
      ∫ t, iteratedFDeriv ℝ m (fun y' => f (ι y' t) * g t) y := by
  set Φ_t : ℝ → H → ℝ := fun t y => f (ι y t) * g t with hΦ_t_def
  set Φ : H → ℝ := fun y => ∫ t, Φ_t t y with hΦ_def
  have inner_smooth : ∀ t, ContDiff ℝ ∞ (fun y => f (ι y t)) :=
    fun t => (f.smooth ⊤).comp (hι_smooth t)
  have Φ_t_smooth : ∀ t, ContDiff ℝ ∞ (Φ_t t) := by
    intro t; exact (inner_smooth t).mul contDiff_const
  have hΦ_t_deriv : ∀ (m : ℕ) (y : H) (t : ℝ),
      iteratedFDeriv ℝ m (Φ_t t) y =
      g t • iteratedFDeriv ℝ m (fun y' => f (ι y' t)) y := by
    intro m y t
    have h_eq : Φ_t t = fun y' => g t • f (ι y' t) := by
      ext y'; simp [Φ_t, mul_comm, smul_eq_mul]
    rw [h_eq]
    exact iteratedFDeriv_const_smul_apply'
      ((inner_smooth t).of_le (by exact_mod_cast le_top) |>.contDiffAt)
  have h_bound : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y t,
      ‖iteratedFDeriv ℝ m (Φ_t t) y‖ ≤ C * ‖g t‖ := by
    intro m
    obtain ⟨C, hC⟩ := hι_bound m
    refine ⟨max C 0, le_max_right _ _, fun y t => ?_⟩
    rw [hΦ_t_deriv, norm_smul (α := ℝ)]
    calc ‖g t‖ * ‖iteratedFDeriv ℝ m (fun y ↦ f (ι y t)) y‖
        ≤ ‖g t‖ * max C 0 :=
          mul_le_mul_of_nonneg_left
            (le_trans (hC y t) (le_max_left C 0)) (norm_nonneg _)
      _ = max C 0 * ‖g t‖ := mul_comm _ _
  have g_integrable : Integrable (fun t => g t) := g.integrable
  have Φ_t_meas : ∀ (m : ℕ) (y : H),
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ m (Φ_t t) y) volume := by
    intro m y
    simp_rw [hΦ_t_deriv m y]
    exact g.continuous.aestronglyMeasurable.smul (hι_meas m y)
  have Φ_t_raw_integrable : ∀ (y : H), Integrable (fun t => Φ_t t y) volume := by
    intro y
    obtain ⟨C, hC_pos, hC⟩ := h_bound 0
    have hC' : ∀ y t, ‖Φ_t t y‖ ≤ C * ‖g t‖ := by
      intro y t
      have h := hC y t
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
        LinearIsometryEquiv.norm_map] at h
      exact h
    exact (g_integrable.norm.const_mul C).mono
      (by
        have h := Φ_t_meas 0 y
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def] at h
        exact ((continuousMultilinearCurryFin0 ℝ H ℝ).symm.isometry.isEmbedding
          |>.aestronglyMeasurable_comp_iff).mp h)
      (Filter.Eventually.of_forall fun t => le_trans (hC' y t)
        (le_of_eq (Real.norm_of_nonneg (mul_nonneg hC_pos (norm_nonneg _))).symm))
  have Φ_t_integrable : ∀ (m : ℕ) (y : H),
      Integrable (fun t => iteratedFDeriv ℝ m (Φ_t t) y) volume := by
    intro m y
    obtain ⟨C, hC_pos, hC⟩ := h_bound m
    exact (g_integrable.norm.const_mul C).mono (Φ_t_meas m y)
      (Filter.Eventually.of_forall fun t => le_trans (hC y t)
        (le_of_eq (Real.norm_of_nonneg (mul_nonneg hC_pos (norm_nonneg _))).symm))
  set I : (n : ℕ) → H → ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ :=
    fun n y => ∫ t, iteratedFDeriv ℝ n (Φ_t t) y with hI_def
  have I_diff : ∀ (n : ℕ) (y : H),
      HasFDerivAt (I n) ((curryLeftLIE (E := H) (F := ℝ) n).symm.toContinuousLinearEquiv.toContinuousLinearMap
        (I (n + 1) y)) y := by
    intro n y₀
    set L := (curryLeftLIE (E := H) (F := ℝ) n).symm.toContinuousLinearEquiv
    have h_cdiff : ∀ t, ContDiff ℝ (↑(n + 1) : ℕ∞) (Φ_t t) :=
      fun t => (Φ_t_smooth t).of_le (by exact_mod_cast le_top)
    have h_differentiable : ∀ t, Differentiable ℝ (fun y => iteratedFDeriv ℝ n (Φ_t t) y) :=
      fun t => (h_cdiff t).differentiable_iteratedFDeriv (by
        apply WithTop.coe_lt_coe.mpr
        apply WithTop.coe_lt_coe.mpr
        omega)
    have h_fderiv_eq : ∀ t y, fderiv ℝ (fun y' => iteratedFDeriv ℝ n (Φ_t t) y') y =
        L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y) := by
      intro t y
      have h1 := congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := Φ_t t) (n := n)) y
      rw [Function.comp_def] at h1
      show fderiv ℝ (fun y' => iteratedFDeriv ℝ n (Φ_t t) y') y =
        (curryLeftLIE (E := H) (F := ℝ) n).symm (iteratedFDeriv ℝ (n + 1) (Φ_t t) y)
      rw [← curryLeftLIE_coe_eq] at h1
      rw [h1, (curryLeftLIE (E := H) (F := ℝ) n).symm_apply_apply]
    have h_hasFDerivAt : ∀ t y, HasFDerivAt (fun y' => iteratedFDeriv ℝ n (Φ_t t) y')
        (L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y)) y := by
      intro t y
      rw [← h_fderiv_eq]
      exact (h_differentiable t y).hasFDerivAt
    obtain ⟨C, hC_pos, hC_bound⟩ := h_bound (n + 1)
    have h_result : HasFDerivAt (fun y => ∫ t, iteratedFDeriv ℝ n (Φ_t t) y)
        (∫ t, L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y₀)) y₀ :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun y t => L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y))
        (s := Set.univ) Filter.univ_mem
        (Filter.Eventually.of_forall fun x => Φ_t_meas n x)
        (Φ_t_integrable n y₀)
        (L.toContinuousLinearMap.continuous.comp_aestronglyMeasurable (Φ_t_meas (n + 1) y₀))
        (Filter.Eventually.of_forall fun t => fun y _ => by
          show ‖(curryLeftLIE (E := H) (F := ℝ) n).symm
            (iteratedFDeriv ℝ (n + 1) (Φ_t t) y)‖ ≤ C * ‖g t‖
          rw [(curryLeftLIE (E := H) (F := ℝ) n).symm.norm_map]
          exact hC_bound y t)
        (g_integrable.norm.const_mul C)
        (Filter.Eventually.of_forall fun t => fun y _ => h_hasFDerivAt t y)
    rw [show (∫ t, L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y₀)) =
      L.toContinuousLinearMap (I (n + 1) y₀) from
        L.toContinuousLinearMap.integral_comp_comm (Φ_t_integrable (n + 1) y₀)] at h_result
    exact h_result
  have I_contDiff : ∀ (m : ℕ) (n : ℕ), ContDiff ℝ (m : ℕ∞) (I n) := by
    intro m
    induction m with
    | zero =>
      intro n
      have h_diff : Differentiable ℝ (I n) := fun y => (I_diff n y).differentiableAt
      exact contDiff_zero.mpr h_diff.continuous
    | succ m ih =>
      intro n
      show ContDiff ℝ ((↑↑m : WithTop ℕ∞) + 1) (I n)
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun y => (I_diff n y).differentiableAt, ?_, ?_⟩
      ·
        intro h; exact absurd h WithTop.coe_ne_top
      ·
        have h_fderiv_eq : fderiv ℝ (I n) =
            fun y => (curryLeftLIE (E := H) (F := ℝ) n).symm.toContinuousLinearEquiv.toContinuousLinearMap
              (I (n + 1) y) :=
          funext fun y => (I_diff n y).fderiv
        rw [h_fderiv_eq]
        exact ((curryLeftLIE n).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff).comp
          (ih (n + 1))
  have h_iter : ∀ (m : ℕ) (y : H), iteratedFDeriv ℝ m Φ y = I m y := by
    intro m
    induction m with
    | zero =>
      intro y
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, hI_def]
      change (continuousMultilinearCurryFin0 ℝ H ℝ).symm (Φ y) =
        ∫ t, (continuousMultilinearCurryFin0 ℝ H ℝ).symm (Φ_t t y)
      set L0 := (continuousMultilinearCurryFin0 ℝ H ℝ).symm.toContinuousLinearEquiv
      exact (L0.toContinuousLinearMap.integral_comp_comm (Φ_t_raw_integrable y)).symm
    | succ m ih =>
      intro y
      have h_succ : iteratedFDeriv ℝ (m + 1) Φ y =
          (curryLeftLIE (E := H) (F := ℝ) m) (fderiv ℝ (iteratedFDeriv ℝ m Φ) y) := by
        have := congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := Φ) (n := m)) y
        rw [Function.comp_def] at this
        rw [this, ← curryLeftLIE_coe_eq]
      rw [h_succ]
      have h_eq_fun : iteratedFDeriv ℝ m Φ = I m := funext ih
      rw [h_eq_fun]
      rw [(I_diff m y).fderiv]
      exact (curryLeftLIE m).apply_symm_apply (I (m + 1) y)
  refine ⟨?_, fun m y => h_iter m y⟩
  have h_Φ_eq : Φ = (continuousMultilinearCurryFin0 ℝ H ℝ) ∘ I 0 := by
    ext y
    simp only [Function.comp_def]
    have h := h_iter 0 y
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def] at h
    rw [← h]
    exact ((continuousMultilinearCurryFin0 ℝ H ℝ).apply_symm_apply (Φ y)).symm
  rw [h_Φ_eq]
  exact contDiff_infty.mpr fun m =>
    ((continuousMultilinearCurryFin0 ℝ H ℝ).contDiff).comp (I_contDiff m 0)
end

-- SchwartzNuclear.SchwartzSlicing
section
open MeasureTheory Real SchwartzMap Measure
open scoped ContDiff
private lemma le_infty_add (n : ℕ) : (∞ : WithTop ℕ∞) + ↑n ≤ ∞ := by
  show (↑(⊤ : ℕ∞) : WithTop ℕ∞) + ↑(↑n : ℕ∞) ≤ ↑(⊤ : ℕ∞)
  rw [← WithTop.coe_add, WithTop.coe_le_coe]; exact le_of_eq (top_add _)
private lemma nat_le_infty (n : ℕ) : (↑n : WithTop ℕ∞) ≤ ∞ :=
  (show (↑(↑n : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)
noncomputable section
namespace GaussianField
def euclideanSnoc (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y i) t)
def euclideanInit (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 _).symm (fun i => x (Fin.castSucc i))
lemma euclideanSnoc_init_last (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSnoc d (euclideanInit d x) (x (Fin.last d)) = x := by
  simp only [euclideanSnoc, euclideanInit]
  apply (WithLp.equiv 2 _).injective
  simp only [Equiv.apply_symm_apply]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]
private lemma euclideanSnoc_hasTemperateGrowth (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    Function.HasTemperateGrowth (euclideanSnoc (d + 1) y) := by
  set L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
        (Fin.last (d + 1)))
  set c := euclideanSnoc (d + 1) y 0
  have h_snoc_decomp : ∀ t,
      Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) t =
      Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
        Pi.single (Fin.last (d + 1)) t := by
    intro t
    ext i
    rw [Pi.add_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  have h_eq : euclideanSnoc (d+1) y = (fun t => c + L t) := by
    funext t
    simp only [c, L, euclideanSnoc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
    show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
      (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
      (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm (Pi.single (Fin.last (d+1)) t)
    rw [h_snoc_decomp]
    simp [EuclideanSpace.equiv]
  rw [h_eq]
  exact Function.HasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    L.hasTemperateGrowth
private lemma euclideanSnoc_antilipschitz (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    AntilipschitzWith 1 (euclideanSnoc (d + 1) y) := by
  refine AntilipschitzWith.of_le_mul_dist (fun s t => ?_)
  simp only [NNReal.coe_one, one_mul]
  have hcoord : ∀ i : Fin (d+2),
    ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ =
    if i = Fin.last (d+1) then ‖s - t‖ else 0 := by
    intro i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  have hsum : ∑ i, ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ ^ 2
    = ‖s - t‖ ^ 2 := by
    conv_lhs => arg 2; ext i; rw [hcoord]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  show dist s t ≤ dist (euclideanSnoc (d + 1) y s) (euclideanSnoc (d + 1) y t)
  rw [dist_eq_norm, dist_eq_norm (E := EuclideanSpace ℝ _), EuclideanSpace.norm_eq,
    hsum, Real.sqrt_sq (norm_nonneg _)]
private lemma euclideanSnoc_norm_sq (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖euclideanSnoc (d + 1) y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  have hlast : (euclideanSnoc (d + 1) y t) (Fin.last (d + 1)) = t := by
    simp [euclideanSnoc, Fin.snoc_last]
  have hcast : ∀ j : Fin (d + 1),
      (euclideanSnoc (d + 1) y t) (Fin.castSucc j) = y j := by
    intro j; simp [euclideanSnoc, Fin.snoc_castSucc]
  simp only [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [show ∑ i : Fin (d + 2), ‖(euclideanSnoc (d + 1) y t) i‖ ^ 2 =
    (∑ j : Fin (d + 1), ‖(euclideanSnoc (d + 1) y t) (Fin.castSucc j)‖ ^ 2) +
    ‖(euclideanSnoc (d + 1) y t) (Fin.last (d + 1))‖ ^ 2 from
    Fin.sum_univ_castSucc _]
  rw [hlast, norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hcast]
private lemma euclideanSnoc_norm_ge_left (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖y‖ ≤ ‖euclideanSnoc (d + 1) y t‖ := by
  rw [← Real.sqrt_sq (norm_nonneg y),
    ← Real.sqrt_sq (norm_nonneg (euclideanSnoc (d + 1) y t))]
  apply Real.sqrt_le_sqrt
  rw [euclideanSnoc_norm_sq]
  linarith [sq_nonneg t]
private lemma euclideanSnoc_norm_ge_right (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖t‖ ≤ ‖euclideanSnoc (d + 1) y t‖ := by
  rw [← Real.sqrt_sq (norm_nonneg t),
    ← Real.sqrt_sq (norm_nonneg (euclideanSnoc (d + 1) y t))]
  apply Real.sqrt_le_sqrt
  rw [euclideanSnoc_norm_sq, Real.norm_eq_abs, sq_abs]
  linarith [sq_nonneg ‖y‖]
noncomputable def schwartz_slice (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    SchwartzMap ℝ ℝ where
  toFun t := f (euclideanSnoc (d + 1) y t)
  smooth' :=
    (compCLMOfAntilipschitz ℝ (euclideanSnoc_hasTemperateGrowth d y)
      (euclideanSnoc_antilipschitz d y) f).smooth'
  decay' :=
    (compCLMOfAntilipschitz ℝ (euclideanSnoc_hasTemperateGrowth d y)
      (euclideanSnoc_antilipschitz d y) f).decay'
private lemma hermiteCoeff_integrand_bound (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖f (euclideanSnoc (d + 1) y t) * hermiteFunction n t‖ ≤
      SchwartzMap.seminorm ℝ 0 0 f * ‖hermiteFunction n t‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_seminorm ℝ f _) (norm_nonneg _)
private lemma hermiteCoeff_bound_integrable (n : ℕ) (C : ℝ) :
    Integrable (fun t : ℝ => C * ‖hermiteFunction n t‖) := by
  apply Integrable.const_mul
  rw [show (fun t => ‖hermiteFunction n t‖) =
    (fun t => ‖(schwartzHermiteBasis1D n) t‖) from
    by ext t; rw [schwartzHermiteBasis1D_apply]]
  exact (schwartzHermiteBasis1D n).integrable.norm
private lemma continuous_euclideanSnoc_y (d : ℕ) (t : ℝ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  apply LipschitzWith.continuous (K := 1)
  intro y₁ y₂
  simp only [ENNReal.coe_one, one_mul, edist_dist, dist_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  rw [show euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t =
    euclideanSnoc (d + 1) (y₁ - y₂) 0 from by
    ext i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]]
  have h : ‖euclideanSnoc (d + 1) (y₁ - y₂) 0‖ ^ 2 = ‖y₁ - y₂‖ ^ 2 := by
    rw [euclideanSnoc_norm_sq]; ring
  nlinarith [norm_nonneg (euclideanSnoc (d + 1) (y₁ - y₂) 0), norm_nonneg (y₁ - y₂),
    sq_nonneg (‖euclideanSnoc (d + 1) (y₁ - y₂) 0‖ - ‖y₁ - y₂‖)]
private lemma euclideanSnoc_y_hasTemperateGrowth (d : ℕ) (t : ℝ) :
    Function.HasTemperateGrowth (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  set L_fun : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    { toFun := fun y => euclideanSnoc (d + 1) y 0
      map_add' := fun y₁ y₂ => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      map_smul' := fun a y => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc] }
  have hL_bound : ∀ y, ‖L_fun y‖ ≤ 1 * ‖y‖ := fun y => by
    rw [one_mul]
    have hdef : ‖L_fun y‖ = ‖euclideanSnoc (d + 1) y 0‖ := rfl
    have h : ‖euclideanSnoc (d + 1) y 0‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [euclideanSnoc_norm_sq]; ring
    nlinarith [norm_nonneg (euclideanSnoc (d + 1) y 0), norm_nonneg y,
      sq_nonneg (‖euclideanSnoc (d + 1) y 0‖ - ‖y‖)]
  set L := L_fun.mkContinuous 1 hL_bound
  have h_eq : (fun y => euclideanSnoc (d + 1) y t) = fun y => c + L y := by
    funext y
    show euclideanSnoc (d + 1) y t =
      euclideanSnoc (d + 1) 0 t + euclideanSnoc (d + 1) y 0
    ext i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  rw [h_eq]
  exact Function.HasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    L.hasTemperateGrowth
private lemma euclideanSnoc_y_antilipschitz (d : ℕ) (t : ℝ) :
    AntilipschitzWith 1 (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  refine AntilipschitzWith.of_le_mul_dist (fun y₁ y₂ => ?_)
  simp only [NNReal.coe_one, one_mul]
  rw [dist_eq_norm, dist_eq_norm]
  have h : ‖euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t‖ ^ 2 =
      ‖y₁ - y₂‖ ^ 2 := by
    rw [show euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t =
      euclideanSnoc (d + 1) (y₁ - y₂) 0 from by
      ext i
      simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last]
      · intro j; simp [Fin.snoc_castSucc]]
    rw [euclideanSnoc_norm_sq]; ring
  nlinarith [norm_nonneg (euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t),
    norm_nonneg (y₁ - y₂),
    sq_nonneg (‖euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t‖ - ‖y₁ - y₂‖)]
private noncomputable def schwartz_slice_y (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (t : ℝ) : SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ :=
  compCLMOfAntilipschitz ℝ (euclideanSnoc_y_hasTemperateGrowth d t)
    (euclideanSnoc_y_antilipschitz d t) f
private noncomputable def euclideanSnoc_linearCLM (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
  LinearMap.mkContinuous
    { toFun := fun y => euclideanSnoc (d + 1) y 0
      map_add' := fun y₁ y₂ => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      map_smul' := fun a y => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc] }
    1 (fun y => by
      rw [one_mul]
      show ‖euclideanSnoc (d + 1) y 0‖ ≤ _
      have h : ‖euclideanSnoc (d + 1) y 0‖ ^ 2 = ‖y‖ ^ 2 := by
        rw [euclideanSnoc_norm_sq]; ring
      nlinarith [norm_nonneg (euclideanSnoc (d + 1) y 0), norm_nonneg y,
        sq_nonneg (‖euclideanSnoc (d + 1) y 0‖ - ‖y‖)])
private lemma euclideanSnoc_linearCLM_apply (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSnoc_linearCLM d y = euclideanSnoc (d + 1) y 0 := rfl
private lemma euclideanSnoc_decomp (d : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    euclideanSnoc (d + 1) y t =
      euclideanSnoc (d + 1) 0 t + euclideanSnoc_linearCLM d y := by
  ext i
  simp only [euclideanSnoc, euclideanSnoc_linearCLM_apply,
    WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]
private lemma euclideanSnoc_linearCLM_norm_le (d : ℕ) :
    ‖euclideanSnoc_linearCLM d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _
private lemma schwartz_slice_y_le_seminorm (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (t : ℝ) (k m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖ ≤
      f.seminorm ℝ k m := by
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  set L := euclideanSnoc_linearCLM d
  set f' : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z => f (c + z)
  have hf'_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f' := by
    exact f.smooth'.comp (contDiff_const.add contDiff_id)
  have h_chain : iteratedFDeriv ℝ m (f' ∘ ⇑L) y =
      (iteratedFDeriv ℝ m f' (L y)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hf'_smooth y
      (WithTop.coe_le_coe.mpr le_top)
  have h_trans : ∀ z, iteratedFDeriv ℝ m f' z =
      iteratedFDeriv ℝ m (f : EuclideanSpace ℝ (Fin (d + 2)) → ℝ) (c + z) :=
    fun z => iteratedFDeriv_comp_add_left m c z
  have h_fun_eq : (schwartz_slice_y d f t : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =
      f' ∘ ⇑L := by
    ext y'
    simp only [schwartz_slice_y, compCLMOfAntilipschitz_apply, Function.comp_apply, f']
    congr 1
    exact euclideanSnoc_decomp d y' t
  have h_norm : ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖ ≤
      ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
    rw [show (schwartz_slice_y d f t : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) = f' ∘ ⇑L
        from h_fun_eq]
    rw [h_chain]
    calc ‖(iteratedFDeriv ℝ m f' (L y)).compContinuousLinearMap (fun _ => L)‖
        ≤ ‖iteratedFDeriv ℝ m f' (L y)‖ * ∏ _ : Fin m, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ m f' (L y)‖ * 1 := by
          gcongr
          calc ∏ _ : Fin m, ‖L‖ ≤ ∏ _ : Fin m, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                  (fun _ _ => euclideanSnoc_linearCLM_norm_le d)
            _ = 1 := by simp
      _ = ‖iteratedFDeriv ℝ m f (c + L y)‖ := by rw [mul_one, h_trans]
      _ = ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
          rw [euclideanSnoc_decomp d y t]
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ :=
        mul_le_mul_of_nonneg_left h_norm (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖euclideanSnoc (d + 1) y t‖ ^ k *
        ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
        gcongr; exact euclideanSnoc_norm_ge_left d y t
    _ ≤ f.seminorm ℝ k m := SchwartzMap.le_seminorm ℝ k m f _
private lemma contDiff_parametric_hermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ) :
    ContDiff ℝ ∞
      (fun y => ∫ t, f (euclideanSnoc (d + 1) y t) * hermiteFunction n t) ∧
    ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))),
      iteratedFDeriv ℝ m
        (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y =
      ∫ t, iteratedFDeriv ℝ m
        (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y := by
  simp_rw [show ∀ t, hermiteFunction n t = (schwartzHermiteBasis1D n) t from
    fun t => (schwartzHermiteBasis1D_apply n t).symm]
  exact contDiff_schwartz_parametric_integral f (schwartzHermiteBasis1D n)
    (euclideanSnoc (d + 1))
    (fun t => by
      rw [show (fun y => euclideanSnoc (d + 1) y t) =
        (fun y => euclideanSnoc (d + 1) 0 t + euclideanSnoc_linearCLM d y) from
        funext (fun y => euclideanSnoc_decomp d y t)]
      exact contDiff_const.add (euclideanSnoc_linearCLM d).contDiff)
    (fun m y => by
      set L := euclideanSnoc_linearCLM d
      have h_chain : ∀ t, iteratedFDeriv ℝ m (fun y' => f (euclideanSnoc (d + 1) y' t)) y =
          (iteratedFDeriv ℝ m (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)).compContinuousLinearMap
            (fun _ => L) := by
        intro t
        set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
        have hf' : ContDiff ℝ (↑(⊤ : ℕ∞)) ((↑f : _ → ℝ) ∘ (c + ·)) :=
          f.smooth'.comp (contDiff_const.add contDiff_id)
        have h_eq : (fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t)) =
            ((↑f : _ → ℝ) ∘ (c + ·)) ∘ ⇑L := by
          ext y'; simp only [Function.comp_apply]; congr 1
          exact euclideanSnoc_decomp d y' t
        rw [h_eq, L.iteratedFDeriv_comp_right hf' y (WithTop.coe_le_coe.mpr le_top)]
        congr 1
        change iteratedFDeriv ℝ m (fun z => (↑f : _ → ℝ) (c + z)) (L y) =
          iteratedFDeriv ℝ m (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)
        rw [iteratedFDeriv_comp_add_left]; congr 1
        exact (euclideanSnoc_decomp d y t).symm
      simp_rw [h_chain]
      have h_snoc_cont : Continuous (fun t : ℝ => euclideanSnoc (d + 1) y t) := by
        set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
          (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
              (Fin.last (d + 1)))
        have h_decomp : (fun t => euclideanSnoc (d + 1) y t) =
            (fun t => euclideanSnoc (d + 1) y 0 + L_t t) := by
          funext t
          simp only [L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
          show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
            (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
            (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
          have : ∀ (s : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) s =
              Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
                Pi.single (Fin.last (d + 1)) s := by
            intro s; ext i; rw [Pi.add_apply]
            refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc_last]
            · intro j; simp [Fin.snoc_castSucc]
          rw [this t]; simp [EuclideanSpace.equiv]
        rw [h_decomp]; exact continuous_const.add L_t.continuous
      exact ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L)).continuous.comp
        ((f.smooth'.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv'.comp
          h_snoc_cont)).aestronglyMeasurable)
    (fun m => by
      exact ⟨f.seminorm ℝ 0 m, fun y t => by
        have := schwartz_slice_y_le_seminorm d f t 0 m y
        have h_slice :
            (fun y' : EuclideanSpace ℝ (Fin (d + 1)) =>
              f (euclideanSnoc (d + 1) y' t)) = ⇑(schwartz_slice_y d f t) := by
          ext y'
          simp [schwartz_slice_y]
        rw [h_slice]
        simpa using this⟩)
private lemma schwartz_partial_hermiteCoeff_smooth (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    ContDiff ℝ ∞ (fun y => hermiteCoeff1D n (schwartz_slice d f y)) :=
  (contDiff_parametric_hermiteCoeff d f n).1
private lemma schwartz_partial_hermiteCoeff_decay (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) (k m : ℕ) :
    ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ m
        (fun y' => hermiteCoeff1D n (schwartz_slice d f y')) y‖ ≤ C := by
  exact ⟨f.seminorm ℝ k m * ∫ t, ‖hermiteFunction n t‖, fun y => by
    obtain ⟨_, h_comm⟩ := contDiff_parametric_hermiteCoeff d f n
    change ‖y‖ ^ k * ‖iteratedFDeriv ℝ m
      (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y‖ ≤ _
    rw [h_comm]
    have h_factor : ∀ t, iteratedFDeriv ℝ m
        (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y =
        hermiteFunction n t • iteratedFDeriv ℝ m (schwartz_slice_y d f t) y := by
      intro t
      have h_eq : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
          (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
        ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
      rw [h_eq]
      exact iteratedFDeriv_const_smul_apply'
        (((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    simp_rw [h_factor]
    calc ‖y‖ ^ k * ‖∫ t, hermiteFunction n t •
          iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖
        ≤ ‖y‖ ^ k * ∫ t, ‖hermiteFunction n t •
          iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖ := by
          gcongr; exact norm_integral_le_integral_norm _
      _ = ‖y‖ ^ k * ∫ t, ‖hermiteFunction n t‖ *
          ‖iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖ := by
          simp_rw [norm_smul]
      _ = ∫ t, ‖hermiteFunction n t‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖) := by
          rw [← integral_const_mul]; congr 1; ext t; ring
      _ ≤ ∫ t, ‖hermiteFunction n t‖ * (f.seminorm ℝ k m) := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _)
              (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)))
          · exact (hermiteCoeff_bound_integrable n (f.seminorm ℝ k m)).congr
              (Filter.Eventually.of_forall (fun t => by ring))
          · exact Filter.Eventually.of_forall (fun t =>
              mul_le_mul_of_nonneg_left
                (schwartz_slice_y_le_seminorm d f t k m y) (norm_nonneg _))
      _ = f.seminorm ℝ k m * ∫ t, ‖hermiteFunction n t‖ := by
          rw [← integral_const_mul]; congr 1; ext t; ring⟩
noncomputable def schwartz_partial_hermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun y := hermiteCoeff1D n (schwartz_slice d f y)
  smooth' := schwartz_partial_hermiteCoeff_smooth d f n
  decay' := schwartz_partial_hermiteCoeff_decay d f n
lemma schwartz_partial_hermiteCoeff_eq_1D (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) :
    schwartz_partial_hermiteCoeff d f n y =
      hermiteCoeff1D n (schwartz_slice d f y) := rfl
lemma schwartz_slice_eq (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    schwartz_slice d f y t = f (euclideanSnoc (d + 1) y t) := rfl
lemma integral_euclidean_snoc (d : ℕ) (g : EuclideanSpace ℝ (Fin (d + 2)) → ℝ)
    (hg : Integrable g) :
    ∫ x, g x = ∫ y : EuclideanSpace ℝ (Fin (d + 1)), ∫ t : ℝ, g (euclideanSnoc (d + 1) y t) := by
  have hv := PiLp.volume_preserving_toLp (ι := Fin (d + 2))
  rw [← hv.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) => ℝ) (Fin.last (d + 1))).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 2) => ℝ) (Fin.last (d + 1))).symm _
  rw [← hem.integral_comp' (f := e)]
  set F : ℝ × (Fin (d + 1) → ℝ) → ℝ :=
    fun p => g ((MeasurableEquiv.toLp 2 _) (e p))
  have hint : Integrable F :=
    (hem.integrable_comp_emb e.measurableEmbedding).mpr
      ((hv.integrable_comp_emb (MeasurableEquiv.toLp 2 _).measurableEmbedding).mpr hg)
  rw [volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint, integral_integral_swap hint]
  have hv' := PiLp.volume_preserving_toLp (ι := Fin (d + 1))
  rw [← hv'.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  congr 1; funext y'
  congr 1; funext t
  show F (t, y') = g (euclideanSnoc (d + 1) ((MeasurableEquiv.toLp 2 _) y') t)
  simp only [F, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    MeasurableEquiv.toLp_apply]
  congr 1
  ext i
  simp only [euclideanSnoc, WithLp.equiv_symm_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]
private lemma schwartz_slice_partial_chain_rule (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    iteratedFDeriv ℝ l' (fun y' => f (euclideanSnoc (d + 1) y' t)) y v =
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t))
        (fun i => euclideanSnoc_linearCLM d (v i)) := by
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  set L := euclideanSnoc_linearCLM d
  set f' : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z => f (c + z)
  have hf'_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f' :=
    f.smooth'.comp (contDiff_const.add contDiff_id)
  have h_fun_eq : (fun y' => f (euclideanSnoc (d + 1) y' t)) = f' ∘ ⇑L := by
    ext y'
    simp only [Function.comp_apply, f']
    congr 1
    exact euclideanSnoc_decomp d y' t
  rw [h_fun_eq]
  rw [L.iteratedFDeriv_comp_right hf'_smooth y (WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext u
  rw [iteratedFDeriv_comp_add_left,
    show c + L y = euclideanSnoc (d + 1) y t from (euclideanSnoc_decomp d y t).symm]
private lemma euclideanSnoc_Pi_single_norm_le (d : ℕ) (t : ℝ) :
    ‖(EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
      (Pi.single (Fin.last (d + 1)) t)‖ ≤ ‖t‖ := by
  rw [EuclideanSpace.norm_eq]
  rw [show ∑ i : Fin (d + 2),
      ‖((EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
        (Pi.single (Fin.last (d + 1)) t)) i‖ ^ 2 = ‖t‖ ^ 2 from by
    have : ∀ i : Fin (d + 2),
        ‖((EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
          (Pi.single (Fin.last (d + 1)) t)) i‖ ^ 2 =
        if i = Fin.last (d + 1) then ‖t‖ ^ 2 else 0 := by
      intro i
      simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply,
        PiLp.toLp_apply, Pi.single_apply]
      by_cases hi : i = Fin.last (d + 1) <;> simp [hi]
    simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]]
  exact le_of_eq (Real.sqrt_sq (norm_nonneg t))
private lemma euclideanSnoc_t_contDiff (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    ContDiff ℝ ∞ (fun t : ℝ => euclideanSnoc (d + 1) y t) := by
  unfold euclideanSnoc
  show ContDiff ℝ ∞ (⇑(PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (d + 2) => ℝ)).symm ∘ (fun t => Fin.snoc (fun i => y.ofLp i) t))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 2) => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr (fun i => by
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact contDiff_id
      · intro j; simp only [Fin.snoc_castSucc]; exact contDiff_const))
noncomputable def schwartz_slice_partial (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) :
    SchwartzMap ℝ ℝ where
  toFun t := iteratedFDeriv ℝ l' (fun y' => f (euclideanSnoc (d + 1) y' t)) y v
  smooth' := by
    set w := fun i => euclideanSnoc_linearCLM d (v i)
    set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
    have h_eq : (fun t => iteratedFDeriv ℝ l' (fun y' =>
        f (euclideanSnoc (d + 1) y' t)) y v) =
        fun t => G (euclideanSnoc (d + 1) y t) := by
      ext t; exact schwartz_slice_partial_chain_rule d f l' y v t
    rw [h_eq]
    exact ((ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
      (f.smooth'.iteratedFDeriv_right (le_infty_add l'))).comp
      (euclideanSnoc_t_contDiff d y)
  decay' := by
    set L := euclideanSnoc_linearCLM d
    set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
    set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
    intro k b
    set C_w := ‖ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖
    refine ⟨C_w * f.seminorm ℝ k (b + l'), fun t => ?_⟩
    have h_val : iteratedFDeriv ℝ l' (fun y' =>
        f (euclideanSnoc (d + 1) y' t)) y v = G (euclideanSnoc (d + 1) y t) :=
      schwartz_slice_partial_chain_rule d f l' y v t
    have h_fun_eq : (fun t => iteratedFDeriv ℝ l' (fun y' =>
        f (euclideanSnoc (d + 1) y' t)) y v) =
        fun t => G (euclideanSnoc (d + 1) y t) := by
      ext s; exact schwartz_slice_partial_chain_rule d f l' y v s
    rw [h_fun_eq]
    set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
      (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
          (Fin.last (d + 1)))
    set c₀ := euclideanSnoc (d + 1) y 0
    have h_snoc_eq : (fun t => euclideanSnoc (d + 1) y t) = (fun t => c₀ + L_t t) := by
      funext s
      simp only [c₀, L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
      show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) s) =
        (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
        (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) s)
      have : ∀ (u : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) u =
          Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
            Pi.single (Fin.last (d + 1)) u := by
        intro u; ext i; rw [Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      rw [this s]; simp [EuclideanSpace.equiv]
    have h_Lt_norm : ‖L_t‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro s; rw [one_mul]
      exact euclideanSnoc_Pi_single_norm_le d s
    have h_G_smooth : ContDiff ℝ ∞ G :=
      (ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
        (f.smooth'.iteratedFDeriv_right (le_infty_add l'))
    set G' := fun z => G (c₀ + z)
    have hG'_smooth : ContDiff ℝ ∞ G' := h_G_smooth.comp (contDiff_const.add contDiff_id)
    have h_fun_eq2 : (fun t => G (euclideanSnoc (d + 1) y t)) = G' ∘ ⇑L_t := by
      funext s; exact congr_arg G (congr_fun h_snoc_eq s)
    have h_deriv_bound : ‖iteratedFDeriv ℝ b (fun t => G (euclideanSnoc (d + 1) y t)) t‖ ≤
        ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
      rw [h_fun_eq2,
          L_t.iteratedFDeriv_comp_right hG'_smooth t (WithTop.coe_le_coe.mpr le_top)]
      calc ‖(iteratedFDeriv ℝ b G' (L_t t)).compContinuousLinearMap fun _ => L_t‖
          ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * ∏ _ : Fin b, ‖L_t‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * 1 := by
            gcongr; calc ∏ _ : Fin b, ‖L_t‖ ≤ ∏ _ : Fin b, (1 : ℝ) :=
                  Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => h_Lt_norm)
              _ = 1 := by simp
        _ = ‖iteratedFDeriv ℝ b G (c₀ + L_t t)‖ := by
            rw [mul_one]; congr 1; exact iteratedFDeriv_comp_add_left b c₀ (L_t t)
        _ = ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
            rw [show c₀ + L_t t = euclideanSnoc (d + 1) y t from
              (congr_fun h_snoc_eq t).symm]
    set L_apply := ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w
    have hf_smooth_l' : ContDiff ℝ ∞ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) :=
      f.smooth'.iteratedFDeriv_right (le_infty_add l')
    have h_G_bound : ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ ≤
        C_w * ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖ := by
      calc ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖
          = ‖L_apply.compContinuousMultilinearMap
              (iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
                (euclideanSnoc (d + 1) y t))‖ := by
            rw [show G = ⇑L_apply ∘ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) from rfl,
                L_apply.iteratedFDeriv_comp_left
                  hf_smooth_l'.contDiffAt (nat_le_infty b)]
        _ ≤ ‖L_apply‖ *
            ‖iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
              (euclideanSnoc (d + 1) y t)‖ :=
            L_apply.norm_compContinuousMultilinearMap_le _
        _ = _ := by rw [norm_iteratedFDeriv_iteratedFDeriv]
    calc ‖t‖ ^ k * ‖iteratedFDeriv ℝ b (fun t => G (euclideanSnoc (d + 1) y t)) t‖
        ≤ ‖t‖ ^ k * ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ :=
          mul_le_mul_of_nonneg_left h_deriv_bound (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖t‖ ^ k * (C_w * ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ)
            (euclideanSnoc (d + 1) y t)‖) :=
          mul_le_mul_of_nonneg_left h_G_bound (pow_nonneg (norm_nonneg _) _)
      _ = C_w * (‖t‖ ^ k *
            ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
          ring
      _ ≤ C_w * (‖euclideanSnoc (d + 1) y t‖ ^ k *
            ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
          gcongr; exact euclideanSnoc_norm_ge_right d y t
      _ ≤ C_w * f.seminorm ℝ k (b + l') := by
          gcongr; exact SchwartzMap.le_seminorm ℝ k (b + l') f _
lemma schwartz_partial_hermiteCoeff_iteratedFDeriv (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) :
    iteratedFDeriv ℝ l' (schwartz_partial_hermiteCoeff d f n) y v =
      hermiteCoeff1D n (schwartz_slice_partial d f l' y v) := by
  obtain ⟨_, h_comm⟩ := contDiff_parametric_hermiteCoeff d f n
  change (iteratedFDeriv ℝ l' (fun y' =>
    ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) v = _
  rw [h_comm]
  have h_factor_v : ∀ t, (iteratedFDeriv ℝ l'
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) v =
      schwartz_slice_partial d f l' y v t * hermiteFunction n t := by
    intro t
    have h_eq : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
      ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
    rw [h_eq]
    have h_smul : iteratedFDeriv ℝ l'
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') y =
        hermiteFunction n t • iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y :=
      iteratedFDeriv_const_smul_apply'
        (((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    rw [h_smul, _root_.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have h_int : Integrable (fun t => iteratedFDeriv ℝ l'
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) := by
    apply (hermiteCoeff_bound_integrable n (f.seminorm ℝ 0 l')).mono'
    ·
      apply Continuous.aestronglyMeasurable
      set L := euclideanSnoc_linearCLM d
      have h_chain : ∀ t, iteratedFDeriv ℝ l'
            (fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t)) y =
          (iteratedFDeriv ℝ l' (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)).compContinuousLinearMap
            (fun _ => L) := by
        intro t
        set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
        have hf' : ContDiff ℝ (↑(⊤ : ℕ∞)) ((↑f : _ → ℝ) ∘ (c + ·)) :=
          f.smooth'.comp (contDiff_const.add contDiff_id)
        have h_eq : (fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t)) =
            ((↑f : _ → ℝ) ∘ (c + ·)) ∘ ⇑L := by
          ext y'; simp only [Function.comp_apply]; congr 1
          exact euclideanSnoc_decomp d y' t
        rw [h_eq, L.iteratedFDeriv_comp_right hf' y (WithTop.coe_le_coe.mpr le_top)]
        congr 1
        change iteratedFDeriv ℝ l' (fun z => (↑f : _ → ℝ) (c + z)) (L y) =
          iteratedFDeriv ℝ l' (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)
        rw [iteratedFDeriv_comp_add_left]; congr 1
        exact (euclideanSnoc_decomp d y t).symm
      have h_fn_eq : (fun t => iteratedFDeriv ℝ l'
            (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) =
          (fun t => hermiteFunction n t •
            (iteratedFDeriv ℝ l' (↑f : _ → ℝ)
              (euclideanSnoc (d + 1) y t)).compContinuousLinearMap
              (fun _ => L)) := by
        ext t
        have h_mul : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
          ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
        rw [h_mul]
        have h_smul : iteratedFDeriv ℝ l'
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') y =
            hermiteFunction n t • iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y :=
          iteratedFDeriv_const_smul_apply'
            (((schwartz_slice_y d f t).smooth'.of_le
              (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
        rw [h_smul]
        have h_inner : iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y =
            (iteratedFDeriv ℝ l' (↑f : _ → ℝ)
              (euclideanSnoc (d + 1) y t)).compContinuousLinearMap (fun _ => L) := by
          have h_sw : (↑(schwartz_slice_y d f t) : _ → ℝ) =
              fun y' => (↑f : _ → ℝ) (euclideanSnoc (d + 1) y' t) := by
            ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply]
          rw [h_sw]; exact h_chain t
        rw [h_inner]
      rw [h_fn_eq]
      have h_snoc_cont : Continuous (fun t : ℝ => euclideanSnoc (d + 1) y t) := by
        set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
          (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
              (Fin.last (d + 1)))
        have h_decomp : (fun t => euclideanSnoc (d + 1) y t) =
            (fun t => euclideanSnoc (d + 1) y 0 + L_t t) := by
          funext t
          simp only [L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
          show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
            (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
            (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
          have : ∀ (s : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) s =
              Fin.snoc (fun i => y.ofLp i) 0 + Pi.single (Fin.last (d + 1)) s := by
            intro s; ext i; rw [Pi.add_apply]
            refine Fin.lastCases ?_ ?_ i
            · simp [Fin.snoc_last]
            · intro j; simp [Fin.snoc_castSucc]
          rw [this t]; simp [EuclideanSpace.equiv]
        rw [h_decomp]; exact continuous_const.add L_t.continuous
      exact Continuous.smul (hermiteFunction_contDiff n 0).continuous
        ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L)).continuous.comp
          ((f.smooth'.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedFDeriv'.comp
            h_snoc_cont))
    · exact Filter.Eventually.of_forall (fun t => by
        have h_eq' : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
          ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
        rw [h_eq']
        have h_smul' : iteratedFDeriv ℝ l'
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') y =
            hermiteFunction n t • iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y :=
          iteratedFDeriv_const_smul_apply'
            (((schwartz_slice_y d f t).smooth'.of_le
              (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
        rw [h_smul', norm_smul]
        calc ‖hermiteFunction n t‖ * ‖iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y‖
            ≤ ‖hermiteFunction n t‖ * f.seminorm ℝ 0 l' := by
              gcongr; simpa using schwartz_slice_y_le_seminorm d f t 0 l' y
          _ = f.seminorm ℝ 0 l' * ‖hermiteFunction n t‖ := mul_comm _ _)
  rw [ContinuousMultilinearMap.integral_apply h_int v]
  congr 1; ext t
  exact h_factor_v t
private lemma schwartz_slice_partial_pointwise_bound (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) (k a b : ℕ) (t : ℝ) :
    ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b
      (↑(schwartz_slice_partial d f l' y v)) t‖) ≤
      ‖ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ
        (fun i => euclideanSnoc_linearCLM d (v i))‖ *
      f.seminorm ℝ (k + a) (b + l') := by
  set L := euclideanSnoc_linearCLM d
  set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
  set g := schwartz_slice_partial d f l' y v
  set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
    (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
  set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
        (Fin.last (d + 1)))
  set c₀ := euclideanSnoc (d + 1) y 0
  have h_snoc_eq : (fun t => euclideanSnoc (d + 1) y t) = (fun t => c₀ + L_t t) := by
    funext t
    simp only [c₀, L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
    show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
      (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
      (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
    have : ∀ (s : ℝ), Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) s =
        Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
          Pi.single (Fin.last (d + 1)) s := by
      intro s; ext i; rw [Pi.add_apply]
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last]
      · intro j; simp [Fin.snoc_castSucc]
    rw [this t]; simp [EuclideanSpace.equiv]
  have h_Lt_norm : ‖L_t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro t; rw [one_mul]
    exact euclideanSnoc_Pi_single_norm_le d t
  have h_G_smooth : ContDiff ℝ ∞ G :=
    (ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
      (f.smooth'.iteratedFDeriv_right (le_infty_add l'))
  set G' := fun z => G (c₀ + z)
  have hG'_smooth : ContDiff ℝ ∞ G' := h_G_smooth.comp (contDiff_const.add contDiff_id)
  have h_fun_eq : (↑g : ℝ → ℝ) = G' ∘ ⇑L_t := by
    ext s
    show g s = G (c₀ + L_t s)
    rw [show c₀ + L_t s = euclideanSnoc (d + 1) y s from (congr_fun h_snoc_eq s).symm]
    exact schwartz_slice_partial_chain_rule d f l' y v s
  have h_deriv : ‖iteratedFDeriv ℝ b (↑g) t‖ ≤
      ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
    rw [h_fun_eq,
        L_t.iteratedFDeriv_comp_right hG'_smooth t (WithTop.coe_le_coe.mpr le_top)]
    calc ‖(iteratedFDeriv ℝ b G' (L_t t)).compContinuousLinearMap fun _ => L_t‖
        ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * ∏ _ : Fin b, ‖L_t‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * 1 := by
          gcongr; calc ∏ _ : Fin b, ‖L_t‖ ≤ ∏ _ : Fin b, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => h_Lt_norm)
            _ = 1 := by simp
      _ = ‖iteratedFDeriv ℝ b G (c₀ + L_t t)‖ := by
          rw [mul_one]; congr 1; exact iteratedFDeriv_comp_add_left b c₀ (L_t t)
      _ = ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
          rw [show c₀ + L_t t = euclideanSnoc (d + 1) y t from (congr_fun h_snoc_eq t).symm]
  have h_G_bound : ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ ≤
      ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
        ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖ := by
    set L_apply := ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w
    have hf_smooth_l' : ContDiff ℝ ∞ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) :=
      f.smooth'.iteratedFDeriv_right (le_infty_add l')
    have h_G_eq : G = ⇑L_apply ∘ (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) := rfl
    calc ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖
        = ‖L_apply.compContinuousMultilinearMap
            (iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
              (euclideanSnoc (d + 1) y t))‖ := by
          rw [h_G_eq, L_apply.iteratedFDeriv_comp_left
            hf_smooth_l'.contDiffAt (nat_le_infty b)]
      _ ≤ ‖L_apply‖ *
          ‖iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
            (euclideanSnoc (d + 1) y t)‖ :=
          L_apply.norm_compContinuousMultilinearMap_le _
      _ = _ := by rw [norm_iteratedFDeriv_iteratedFDeriv]
  set C_w := ‖ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖
  calc ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖)
      ≤ ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖) := by
        gcongr
    _ ≤ ‖y‖ ^ k * (‖t‖ ^ a * (C_w *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖)) := by
        gcongr
    _ = C_w * (‖y‖ ^ k * ‖t‖ ^ a *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by ring
    _ ≤ C_w * (‖euclideanSnoc (d + 1) y t‖ ^ (k + a) *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
        gcongr
        calc ‖y‖ ^ k * ‖t‖ ^ a
            ≤ ‖euclideanSnoc (d + 1) y t‖ ^ k * ‖euclideanSnoc (d + 1) y t‖ ^ a := by
              gcongr
              · exact euclideanSnoc_norm_ge_left d y t
              · exact euclideanSnoc_norm_ge_right d y t
          _ = ‖euclideanSnoc (d + 1) y t‖ ^ (k + a) := (pow_add _ k a).symm
    _ ≤ C_w * f.seminorm ℝ (k + a) (b + l') := by
        gcongr; exact SchwartzMap.le_seminorm ℝ (k + a) (b + l') f _
lemma schwartz_slice_partial_seminorm_bound (d : ℕ) (k' l' a b : ℕ) :
    ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
        (y : EuclideanSpace ℝ (Fin (d + 1)))
        (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))),
        ‖y‖ ^ k' * schwartzSeminormFamily ℝ ℝ ℝ (a, b)
          (schwartz_slice_partial d f l' y v) ≤
          C * (∏ i, ‖v i‖) *
            q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f
    := by
  refine ⟨1, {(k' + a, b + l')}, one_pos, fun f y v => ?_⟩
  simp only [Finset.sup_singleton, one_mul]
  set g := schwartz_slice_partial d f l' y v
  set L := euclideanSnoc_linearCLM d
  set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
  have h_apply_le : ‖ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖ ≤ ∏ i : Fin l', ‖v i‖ := by
    calc ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖
        ≤ ∏ i, ‖w i‖ := by
          apply ContinuousLinearMap.opNorm_le_bound
          · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
          · intro A
            calc ‖A w‖ ≤ ‖A‖ * ∏ i, ‖w i‖ := A.le_opNorm w
              _ = (∏ i, ‖w i‖) * ‖A‖ := mul_comm _ _
      _ ≤ ∏ i, ‖v i‖ := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro i _
          calc ‖w i‖ = ‖L (v i)‖ := rfl
            _ ≤ ‖L‖ * ‖v i‖ := ContinuousLinearMap.le_opNorm L (v i)
            _ ≤ 1 * ‖v i‖ := by gcongr; exact euclideanSnoc_linearCLM_norm_le d
            _ = ‖v i‖ := one_mul _
  by_cases hy : ‖y‖ ^ k' = 0
  · simp only [hy, zero_mul]
    positivity
  · have hy_pos : 0 < ‖y‖ ^ k' := lt_of_le_of_ne (pow_nonneg (norm_nonneg _) _) (Ne.symm hy)
    have h_sem : SchwartzMap.seminorm ℝ a b g ≤
        ((∏ i : Fin l', ‖v i‖) * f.seminorm ℝ (k' + a) (b + l')) / ‖y‖ ^ k' := by
      apply SchwartzMap.seminorm_le_bound ℝ a b g (by positivity)
      intro t
      rw [le_div_iff₀ hy_pos]
      calc ‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖ * ‖y‖ ^ k'
          = ‖y‖ ^ k' * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖) := by ring
        _ ≤ ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ * f.seminorm ℝ (k' + a) (b + l') :=
            schwartz_slice_partial_pointwise_bound d f l' y v k' a b t
        _ ≤ (∏ i : Fin l', ‖v i‖) * f.seminorm ℝ (k' + a) (b + l') := by
            gcongr
    calc ‖y‖ ^ k' * SchwartzMap.seminorm ℝ a b g
        ≤ ‖y‖ ^ k' * (((∏ i, ‖v i‖) * f.seminorm ℝ (k' + a) (b + l')) / ‖y‖ ^ k') :=
          mul_le_mul_of_nonneg_left h_sem (le_of_lt hy_pos)
      _ = (∏ i, ‖v i‖) * f.seminorm ℝ (k' + a) (b + l') :=
          mul_div_cancel₀ _ (ne_of_gt hy_pos)
end GaussianField
end
end

-- SchwartzNuclear.HermiteTensorProduct
section
noncomputable section
open GaussianField MeasureTheory Real SchwartzMap
open scoped ContDiff
namespace GaussianField
noncomputable def schwartzDomCongr {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : D ≃L[ℝ] E) :
    SchwartzMap E F ≃L[ℝ] SchwartzMap D F :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLMOfContinuousLinearEquiv ℝ g)
    (compCLMOfContinuousLinearEquiv ℝ g.symm)
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.apply_symm_apply x))
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.symm_apply_apply x))
noncomputable def euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
noncomputable def euclideanFin1MeasEquiv : EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)
lemma euclideanFin1MeasEquiv_mp :
    MeasureTheory.MeasurePreserving euclideanFin1MeasEquiv volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
    (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ)
lemma euclideanFin1MeasEquiv_apply (x : EuclideanSpace ℝ (Fin 1)) :
    euclideanFin1MeasEquiv x = x 0 := by
  simp [euclideanFin1MeasEquiv, MeasurableEquiv.funUnique, MeasurableEquiv.toLp, WithLp.equiv]
theorem hermiteCoeff1D_basis_kronecker (n m : ℕ) :
    hermiteCoeff1D n (schwartzHermiteBasis1D m) = if n = m then 1 else 0 := by
  show ∫ x, schwartzHermiteBasis1D m x * hermiteFunction n x = _
  simp_rw [schwartzHermiteBasis1D_apply]
  convert hermiteFunction_orthonormal m n using 1
  exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)
private theorem hermiteCoeff_rapid_decay (f : SchwartzMap ℝ ℝ) (k : ℕ) :
    Summable (fun m => |hermiteCoeff1D m f| * (1 + (m : ℝ)) ^ k) := by
  obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay ((k : ℝ) + 2)
  set S := (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have h_le : ∀ m : ℕ, |hermiteCoeff1D m f| * (1 + (m : ℝ)) ^ k ≤
      C * S * (1 + (m : ℝ)) ^ ((-2) : ℝ) := by
    intro m
    have h1m : (0 : ℝ) < 1 + ↑m := by positivity
    have h_bd := hbound f m
    have h_split : (1 + (m : ℝ)) ^ ((k : ℝ) + 2) =
        (1 + (m : ℝ)) ^ (k : ℕ) * (1 + (m : ℝ)) ^ (2 : ℝ) := by
      rw [← rpow_natCast (1 + ↑m) k, ← rpow_add h1m]
    rw [h_split] at h_bd
    have h2_pos : (0 : ℝ) < (1 + ↑m) ^ (2 : ℝ) := rpow_pos_of_pos h1m 2
    have hle : |hermiteCoeff1D m f| * (1 + ↑m) ^ k ≤ C * S / (1 + ↑m) ^ (2 : ℝ) := by
      rw [le_div_iff₀ h2_pos]
      calc |hermiteCoeff1D m f| * (1 + ↑m) ^ k * (1 + ↑m) ^ (2 : ℝ)
          = |hermiteCoeff1D m f| * ((1 + ↑m) ^ (k : ℕ) * (1 + ↑m) ^ (2 : ℝ)) := by ring
        _ ≤ C * S := h_bd
    rwa [div_eq_mul_inv, ← rpow_neg h1m.le] at hle
  have h_sum : Summable (fun m : ℕ => C * S * (1 + (m : ℝ)) ^ ((-2) : ℝ)) := by
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    exact h1.const_smul (C * S)
  exact .of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _)
    (pow_nonneg (by positivity) k)) h_le h_sum
private def toRapidDecay1DLM : SchwartzMap ℝ ℝ →ₗ[ℝ] RapidDecaySeq where
  toFun f := ⟨fun n => hermiteCoeff1D n f, hermiteCoeff_rapid_decay f⟩
  map_add' f g := RapidDecaySeq.ext fun n => (hermiteCoeff1D_linear n).map_add f g
  map_smul' r f := RapidDecaySeq.ext fun n => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    exact (hermiteCoeff1D_linear n).map_smul r f
private noncomputable def toRapidDecay1DCLM : SchwartzMap ℝ ℝ →L[ℝ] RapidDecaySeq where
  toLinearMap := toRapidDecay1DLM
  cont := by
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ ℝ ℝ) RapidDecaySeq.rapidDecay_withSeminorms
    intro k
    obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay ((k : ℝ) + 2)
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h_rpow_sum : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    set L := ∑' n : ℕ, (1 + (n : ℝ)) ^ ((-2) : ℝ)
    refine ⟨Finset.Iic q, ⟨C * L, by positivity⟩, fun f => ?_⟩
    simp only [Seminorm.comp_apply]
    set S := (Finset.Iic q).sup (schwartzSeminormFamily ℝ ℝ ℝ) f
    have h_le : ∀ n : ℕ, |hermiteCoeff1D n f| * (1 + (n : ℝ)) ^ k ≤
        C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
      intro n
      have h1n : (0 : ℝ) < 1 + ↑n := by positivity
      have h_bd := hbound f n
      have h_split : (1 + (n : ℝ)) ^ ((k : ℝ) + 2) =
          (1 + (n : ℝ)) ^ (k : ℕ) * (1 + (n : ℝ)) ^ (2 : ℝ) := by
        rw [← rpow_natCast (1 + ↑n) k, ← rpow_add h1n]
      rw [h_split] at h_bd
      have h2_pos : (0 : ℝ) < (1 + ↑n) ^ (2 : ℝ) := rpow_pos_of_pos h1n 2
      have hle : |hermiteCoeff1D n f| * (1 + ↑n) ^ k ≤ C * S / (1 + ↑n) ^ (2 : ℝ) := by
        rw [le_div_iff₀ h2_pos]
        calc |hermiteCoeff1D n f| * (1 + ↑n) ^ k * (1 + ↑n) ^ (2 : ℝ)
            = |hermiteCoeff1D n f| * ((1 + ↑n) ^ (k : ℕ) * (1 + ↑n) ^ (2 : ℝ)) := by ring
          _ ≤ C * S := h_bd
      rwa [div_eq_mul_inv, ← rpow_neg h1n.le] at hle
    have h_tsum := (hermiteCoeff_rapid_decay f k).tsum_le_tsum h_le (h_rpow_sum.const_smul (C * S))
    calc ∑' n, |hermiteCoeff1D n f| * (1 + ↑n) ^ k
        ≤ ∑' (n : ℕ), C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := h_tsum
      _ = C * S * L := by rw [tsum_mul_left]
      _ = C * L * S := by ring
noncomputable instance schwartzMap_T2Space : T2Space (SchwartzMap ℝ ℝ) := by
  haveI : T1Space (SchwartzMap ℝ ℝ) :=
    WithSeminorms.T1_of_separating (schwartz_withSeminorms ℝ ℝ ℝ) fun f hf =>
      by
        exact ⟨⟨0, 0⟩, fun h => hf (SchwartzMap.ext fun x =>
          norm_le_zero_iff.mp ((SchwartzMap.norm_le_seminorm ℝ f x).trans (le_of_eq h)))⟩
  exact inferInstance
private lemma scalar_hermite_iteratedFDeriv_bound (c : ℝ) (n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => c * hermiteFunction n y) x‖ ≤
    |c| * SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n) := by
  rw [show (fun y => c * hermiteFunction n y) =
    (fun y => c • hermiteFunction n y) from by ext; simp [smul_eq_mul]]
  rw [iteratedFDeriv_const_smul_apply' ((hermiteFunction_contDiff n k).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by
    have h := SchwartzMap.le_seminorm ℝ 0 k (schwartzHermiteBasis1D n) x
    simp only [pow_zero, one_mul] at h
    rwa [show iteratedFDeriv ℝ k (⇑(schwartzHermiteBasis1D n)) x =
      iteratedFDeriv ℝ k (hermiteFunction n) x from
      congr_arg (iteratedFDeriv ℝ k · x) (schwartzHermiteBasis1D_coe n)] at h)
    (abs_nonneg _)
private lemma rapidDecay_seminorm_summable (a : RapidDecaySeq) (k l : ℕ) :
    Summable (fun n => |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)) := by
  obtain ⟨C, hC, s, hbasis⟩ := schwartzHermiteBasis1D_growth k l
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (fun n => by
      calc |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)
          ≤ |a.val n| * (C * (1 + ↑n) ^ s) :=
            mul_le_mul_of_nonneg_left (hbasis n) (abs_nonneg _)
        _ = C * (|a.val n| * (1 + ↑n) ^ s) := by ring)
    (Summable.mul_left C (a.rapid_decay s))
private lemma rapidDecay_hermite_contDiff (a : RapidDecaySeq) :
    ContDiff ℝ ∞ (fun x => ∑' n, a.val n * hermiteFunction n x) := by
  apply contDiff_tsum
    (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
  · intro n
    exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
  · intro j _; exact rapidDecay_seminorm_summable a 0 j
  · intro j n x _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j x
private lemma rapidDecay_pointwise_seminorm_le (a : RapidDecaySeq) (k l : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x‖ ≤
    ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
  have h_iFD : iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x =
      ∑' n, iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x := by
    apply iteratedFDeriv_tsum_apply (N := ⊤)
      (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
    · intro n
      exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
    · intro j _; exact rapidDecay_seminorm_summable a 0 j
    · intro j n y _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j y
    · exact le_top
  rw [h_iFD]
  have h_norm_summ : Summable (fun n =>
      ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => scalar_hermite_iteratedFDeriv_bound (a.val n) n l x)
      (rapidDecay_seminorm_summable a 0 l)
  have h_ptwise : ∀ n, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ ≤
      |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
    intro n
    have hfun_eq : (fun y => a.val n * hermiteFunction n y) =
        ⇑(a.val n • schwartzHermiteBasis1D n) := by
      ext y; simp [smul_eq_mul, schwartzHermiteBasis1D_apply]
    rw [hfun_eq]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • schwartzHermiteBasis1D n)) x‖
        ≤ SchwartzMap.seminorm ℝ k l (a.val n • schwartzHermiteBasis1D n) :=
          SchwartzMap.le_seminorm ℝ k l _ x
      _ = |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
  calc ‖x‖ ^ k * ‖∑' n, iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖
      ≤ ‖x‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
          (pow_nonneg (norm_nonneg _) k)
    _ = ∑' n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ :=
        tsum_mul_left.symm
    _ ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) :=
        (Summable.of_nonneg_of_le
          (fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _))
          h_ptwise (rapidDecay_seminorm_summable a k l)).tsum_le_tsum
          h_ptwise (rapidDecay_seminorm_summable a k l)
private lemma rapidDecay_hermite_decay (a : RapidDecaySeq) (k l : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x‖ ≤ C :=
  ⟨_, rapidDecay_pointwise_seminorm_le a k l⟩
private noncomputable def rapidDecay_schwartzMap (a : RapidDecaySeq) : SchwartzMap ℝ ℝ where
  toFun := fun x => ∑' n, a.val n * hermiteFunction n x
  smooth' := rapidDecay_hermite_contDiff a
  decay' := rapidDecay_hermite_decay a
private lemma rapidDecay_schwartzMap_apply (a : RapidDecaySeq) (x : ℝ) :
    rapidDecay_schwartzMap a x = ∑' n, a.val n * hermiteFunction n x := rfl
set_option maxHeartbeats 1600000 in
private theorem rapidDecay_hermite_hasSum (a : RapidDecaySeq) :
    HasSum (fun n => a.val n • schwartzHermiteBasis1D n) (rapidDecay_schwartzMap a) := by
  rw [HasSum]
  show Filter.Tendsto _ Filter.atTop _
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ (rapidDecay_schwartzMap a)]
  intro ⟨k, l⟩ ε hε
  have h_sem := rapidDecay_seminorm_summable a k l
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp h_sem (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs => ?_⟩
  rw [show (∑ i ∈ s, a.val i • schwartzHermiteBasis1D i) - rapidDecay_schwartzMap a =
    -(rapidDecay_schwartzMap a - ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i) from by abel,
    map_neg_eq_map]
  calc SchwartzMap.seminorm ℝ k l
        (rapidDecay_schwartzMap a - ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i)
      ≤ ε / 2 := by
        apply SchwartzMap.seminorm_le_bound ℝ k l _ (half_pos hε).le
        intro x
        set r := rapidDecay_schwartzMap a -
          ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i with hr_def
        let g : ℕ → ℝ → ℝ := fun n y => a.val n * hermiteFunction n y
        have h_summ_iFD : Summable (fun n => iteratedFDeriv ℝ l (g n) x) := by
          apply Summable.of_norm_bounded
            (g := fun n => |a.val n| *
              SchwartzMap.seminorm ℝ 0 l (schwartzHermiteBasis1D n))
          · exact rapidDecay_seminorm_summable a 0 l
          · intro n; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n l x
        have h_iFD_limit : iteratedFDeriv ℝ l
            (fun y => ∑' n, a.val n * hermiteFunction n y) x =
            ∑' n, iteratedFDeriv ℝ l (g n) x := by
          apply iteratedFDeriv_tsum_apply (N := ⊤)
            (v := fun j n => |a.val n| *
              SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
          · intro n
            exact contDiff_infty.mpr (fun m =>
              contDiff_const.mul (hermiteFunction_contDiff n m))
          · intro j _; exact rapidDecay_seminorm_summable a 0 j
          · intro j n y _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j y
          · exact le_top
        have hsum_coe : ∀ y,
            (∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
            ∑ i ∈ s, g i y := by
          intro y
          have : ∀ (t : Finset ℕ),
              (∑ i ∈ t, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
              ∑ i ∈ t, g i y := by
            intro t; induction t using Finset.cons_induction with
            | empty => simp
            | cons a' t' ha' ih =>
              simp [smul_eq_mul, schwartzHermiteBasis1D_apply, g]
          exact this s
        have h_iFD_sum : iteratedFDeriv ℝ l
            (⇑(∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ)) x =
            ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
          have hcoe : ⇑(∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) =
              fun y => ∑ i ∈ s, g i y := funext hsum_coe
          rw [hcoe]
          have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
            (fun i _ => (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
          exact congr_fun h_eq x |>.trans (Finset.sum_apply x s _)
        have h_iFD_r : iteratedFDeriv ℝ l (⇑r) x =
            ∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x := by
          have hf_cd : ContDiff ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) :=
            (rapidDecay_hermite_contDiff a).of_le (mod_cast le_top)
          have hg_cd : ContDiff ℝ l (fun y => ∑ i ∈ s, g i y) :=
            ContDiff.sum (fun i _ =>
              (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
          have hcoe_r : (⇑r : ℝ → ℝ) = fun y =>
              (∑' n, a.val n * hermiteFunction n y) - ∑ i ∈ s, g i y := by
            ext y; simp only [hr_def, sub_apply, rapidDecay_schwartzMap_apply]
            exact congrArg ((∑' n, a.val n * hermiteFunction n y) - ·) (hsum_coe y)
          rw [hcoe_r]
          set h_sum := fun y => ∑ i ∈ s, g i y with h_sum_def
          have h_neg_cd : ContDiff ℝ l (-h_sum) := hg_cd.neg
          have h_rw : (fun y => (∑' n, a.val n * hermiteFunction n y) - h_sum y) =
              (fun y => ∑' n, a.val n * hermiteFunction n y) + (-h_sum) := by
            ext; simp [sub_eq_add_neg]
          rw [h_rw, iteratedFDeriv_add hf_cd h_neg_cd, Pi.add_apply,
            iteratedFDeriv_neg, Pi.neg_apply, h_iFD_limit]
          have h_iFD_h : iteratedFDeriv ℝ l h_sum x =
              ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
            rw [h_sum_def]
            have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
              (fun i _ =>
                (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
            calc iteratedFDeriv ℝ l (fun y => ∑ i ∈ s, g i y) x
                = (∑ j ∈ s, iteratedFDeriv ℝ l (g j)) x := congr_fun h_eq x
              _ = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := Finset.sum_apply x s _
          rw [h_iFD_h]
          rw [← h_summ_iFD.sum_add_tsum_compl (s := s)]
          abel
        have h_norm_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            ‖iteratedFDeriv ℝ l (g ↑i) x‖) :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun n => scalar_hermite_iteratedFDeriv_bound (a.val n) n l x)
            (rapidDecay_seminorm_summable a 0 l)).subtype _
        have h_sem_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            |a.val ↑i| *
            SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i)) :=
          (rapidDecay_seminorm_summable a k l).subtype _
        have h_ptwise : ∀ (i : ↥(↑s : Set ℕ)ᶜ),
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖ ≤
            |a.val ↑i| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i) := by
          intro ⟨n, _⟩
          have hg_eq : g n = ⇑(a.val n • schwartzHermiteBasis1D n) := by
            ext y; simp [g, smul_eq_mul, schwartzHermiteBasis1D_apply]
          rw [hg_eq]
          calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • schwartzHermiteBasis1D n)) x‖
              ≤ SchwartzMap.seminorm ℝ k l (a.val n • schwartzHermiteBasis1D n) :=
                SchwartzMap.le_seminorm ℝ k l _ x
            _ = |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
                rw [map_smul_eq_mul, Real.norm_eq_abs]
        rw [h_iFD_r]
        calc ‖x‖ ^ k * ‖∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x‖
            ≤ ‖x‖ ^ k * ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                ‖iteratedFDeriv ℝ l (g ↑i) x‖ :=
              mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
                (pow_nonneg (norm_nonneg _) k)
          _ = ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖) := by
              rw [tsum_mul_left]
          _ ≤ ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (|a.val ↑i| *
                  SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i)) :=
              (h_norm_summ.mul_left _).tsum_le_tsum h_ptwise h_sem_summ
          _ ≤ ε / 2 := by
              apply h_sem_summ.tsum_le_of_sum_le
              intro t
              set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
              have h_disj : Disjoint t' s := by
                rw [Finset.disjoint_left]
                intro n hn hn_s
                rw [Finset.mem_map] at hn
                obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
                exact hm hn_s
              have h_disj₀ : Disjoint t' s₀ := Disjoint.mono_right hs h_disj
              have h_lt := hs₀ t' h_disj₀
              rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
                mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at h_lt
              rw [ht'_def, Finset.sum_map] at h_lt
              exact le_of_lt h_lt
    _ < ε := half_lt_self hε
private theorem rapidDecay_hermite_summable (a : RapidDecaySeq) :
    Summable (fun n => a.val n • schwartzHermiteBasis1D n) :=
  ⟨_, rapidDecay_hermite_hasSum a⟩
private noncomputable def fromRapidDecay1DLM : RapidDecaySeq →ₗ[ℝ] SchwartzMap ℝ ℝ where
  toFun := fun a => ∑' n, a.val n • schwartzHermiteBasis1D n
  map_add' := fun a b => by
    simp only [RapidDecaySeq.add_val]
    rw [show (fun n => (a.val n + b.val n) • schwartzHermiteBasis1D n) =
      (fun n => a.val n • schwartzHermiteBasis1D n + b.val n • schwartzHermiteBasis1D n) from by
      ext n; rw [add_smul]]
    exact (rapidDecay_hermite_summable a).tsum_add (rapidDecay_hermite_summable b)
  map_smul' := fun r a => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    rw [show (fun n => (r * a.val n) • schwartzHermiteBasis1D n) =
      (fun n => r • (a.val n • schwartzHermiteBasis1D n)) from by
      ext n; rw [mul_smul]]
    exact (rapidDecay_hermite_summable a).tsum_const_smul r
private lemma fromRapidDecay1DLM_eq (a : RapidDecaySeq) :
    fromRapidDecay1DLM a = rapidDecay_schwartzMap a :=
  (rapidDecay_hermite_hasSum a).tsum_eq
private lemma fromRapidDecay1DLM_seminorm_le (a : RapidDecaySeq) (k l : ℕ) :
    SchwartzMap.seminorm ℝ k l (fromRapidDecay1DLM a) ≤
      ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
  rw [fromRapidDecay1DLM_eq]
  exact SchwartzMap.seminorm_le_bound ℝ k l _ (tsum_nonneg fun n =>
    mul_nonneg (abs_nonneg _) (apply_nonneg _ _)) (rapidDecay_pointwise_seminorm_le a k l)
private lemma fromRapidDecay1DLM_bound (k l : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∃ (s : ℕ), ∀ (a : RapidDecaySeq),
      SchwartzMap.seminorm ℝ k l (fromRapidDecay1DLM a) ≤
        C * RapidDecaySeq.rapidDecaySeminorm s a := by
  obtain ⟨C, hC, s, hbasis⟩ := schwartzHermiteBasis1D_growth k l
  exact ⟨C, hC, s, fun a => by
    calc (SchwartzMap.seminorm ℝ k l) (fromRapidDecay1DLM a)
        ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) :=
          fromRapidDecay1DLM_seminorm_le a k l
      _ ≤ ∑' n, |a.val n| * (C * (1 + (n : ℝ)) ^ s) :=
          (rapidDecay_seminorm_summable a k l).tsum_le_tsum
            (fun n => mul_le_mul_of_nonneg_left (hbasis n) (abs_nonneg _))
            ((a.rapid_decay s).mul_left C |>.congr fun n => by ring)
      _ = C * ∑' n, |a.val n| * (1 + (n : ℝ)) ^ s := by
          rw [← tsum_mul_left]; congr 1; ext n; ring⟩
private lemma fromRapidDecay1DLM_isBounded :
    Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
      (schwartzSeminormFamily ℝ ℝ ℝ) fromRapidDecay1DLM := by
  intro ⟨k, l⟩
  obtain ⟨C, hC, s, hbound⟩ := fromRapidDecay1DLM_bound k l
  exact ⟨{s}, ⟨C, hC.le⟩, fun a => by
    simp only [Seminorm.comp_apply, schwartzSeminormFamily, Finset.sup_singleton]
    exact hbound a⟩
private noncomputable def fromRapidDecay1DCLM : RapidDecaySeq →L[ℝ] SchwartzMap ℝ ℝ where
  toLinearMap := fromRapidDecay1DLM
  cont :=
    WithSeminorms.continuous_of_isBounded RapidDecaySeq.rapidDecay_withSeminorms
      (schwartz_withSeminorms ℝ ℝ ℝ) fromRapidDecay1DLM fromRapidDecay1DLM_isBounded
noncomputable def schwartzRapidDecayEquiv1D :
    SchwartzMap ℝ ℝ ≃L[ℝ] RapidDecaySeq :=
  ContinuousLinearEquiv.equivOfInverse
    toRapidDecay1DCLM
    fromRapidDecay1DCLM
    (fun f => by
      show ∑' n, hermiteCoeff1D n f • schwartzHermiteBasis1D n = f
      exact ((schwartz_hermite_hasSum f).unique
        (schwartz_hermite_hasSum f).summable.hasSum).symm)
    (fun a => by
      apply RapidDecaySeq.ext; intro n
      show hermiteCoeff1D n (∑' m, a.val m • schwartzHermiteBasis1D m) = a.val n
      rw [show hermiteCoeff1D n (∑' m, a.val m • schwartzHermiteBasis1D m) =
        hermiteCoeff1DCLM n (∑' m, a.val m • schwartzHermiteBasis1D m) from rfl,
        (hermiteCoeff1DCLM n).map_tsum (rapidDecay_hermite_summable a)]
      simp only [hermiteCoeff1DCLM_apply, map_smul, smul_eq_mul,
        hermiteCoeff1D_basis_kronecker]
      simp_rw [show ∀ m, (if n = m then (1 : ℝ) else 0) = if m = n then 1 else 0 from
        fun m => by split_ifs <;> simp_all]
      simp [mul_ite, mul_one, mul_zero, tsum_ite_eq])
theorem schwartzRapidDecayEquiv1D_symm_apply (a : RapidDecaySeq) (t : ℝ) :
    (schwartzRapidDecayEquiv1D.symm a) t =
      ∑' n, a.val n * hermiteFunction n t := by
  simp only [schwartzRapidDecayEquiv1D, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]
  show fromRapidDecay1DCLM a t = _
  show fromRapidDecay1DLM a t = _
  rw [fromRapidDecay1DLM_eq]
  show rapidDecay_schwartzMap a t = _
  rfl
abbrev MultiIndex (d : ℕ) := Fin d → ℕ
def MultiIndex.abs {d : ℕ} (α : MultiIndex d) : ℕ :=
  ∑ i, α i
noncomputable def multiIndexEquiv : (d : ℕ) → MultiIndex (d + 1) ≃ ℕ
  | 0 => Equiv.funUnique (Fin 1) ℕ
  | (d + 1) => (Fin.succFunEquiv ℕ (d + 1)).trans
      ((Equiv.prodCongr (multiIndexEquiv d) (Equiv.refl ℕ)).trans Nat.pairEquiv)
private lemma multiIndexEquiv_succ_apply (d : ℕ) (α : MultiIndex (d + 2)) :
    multiIndexEquiv (d + 1) α =
      Nat.pair (multiIndexEquiv d ((Fin.succFunEquiv ℕ (d + 1) α).1))
        ((Fin.succFunEquiv ℕ (d + 1) α).2) := by
  simp [multiIndexEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Nat.pairEquiv]
  rfl
private lemma multiIndexEquiv_succ_symm (d : ℕ) (n : ℕ) :
    (multiIndexEquiv (d + 1)).symm n =
      (Fin.succFunEquiv ℕ (d + 1)).symm
        ((multiIndexEquiv d).symm (Nat.unpair n).1, (Nat.unpair n).2) := by
  apply (multiIndexEquiv (d + 1)).injective
  simp only [Equiv.apply_symm_apply]
  rw [multiIndexEquiv_succ_apply]
  simp only [Equiv.apply_symm_apply, Nat.pair_unpair]
private lemma multiIndex_abs_succ (d : ℕ) (α : MultiIndex (d + 2)) :
    (MultiIndex.abs α : ℝ) =
      (MultiIndex.abs ((Fin.succFunEquiv ℕ (d + 1) α).1) : ℝ) +
        ((Fin.succFunEquiv ℕ (d + 1) α).2 : ℝ) := by
  simp only [MultiIndex.abs]
  push_cast
  rw [Fin.sum_univ_castSucc (n := d + 1)]
  congr 1
private lemma multiIndex_abs_succ_symm (d : ℕ) (n : ℕ) :
    (MultiIndex.abs ((multiIndexEquiv (d + 1)).symm n) : ℝ) =
      (MultiIndex.abs ((multiIndexEquiv d).symm (Nat.unpair n).1) : ℝ) +
        ((Nat.unpair n).2 : ℝ) := by
  rw [multiIndexEquiv_succ_symm]
  have h := multiIndex_abs_succ d
    ((Fin.succFunEquiv ℕ (d + 1)).symm
      ((multiIndexEquiv d).symm (Nat.unpair n).1, (Nat.unpair n).2))
  simp only [Equiv.apply_symm_apply] at h
  exact h
lemma multiIndexEquiv_growth (d : ℕ) :
    ∃ C > 0, ∃ k : ℕ, ∀ α : MultiIndex (d + 1),
      (1 + (multiIndexEquiv d α : ℝ)) ≤ C * (1 + (MultiIndex.abs α : ℝ)) ^ k := by
  induction d with
  | zero =>
    refine ⟨1, one_pos, 1, fun α => ?_⟩
    simp only [multiIndexEquiv, Equiv.funUnique_apply, one_mul, pow_one]
    suffices h : (α default : ℝ) ≤ (MultiIndex.abs α : ℝ) by linarith
    gcongr
    show α default ≤ ∑ i, α i
    rw [Fin.default_eq_zero]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  | succ d ih =>
    obtain ⟨C₁, hC₁, k₁, hbound₁⟩ := ih
    refine ⟨(C₁ + 1) ^ 2, by positivity, 2 * (k₁ + 1), fun α => ?_⟩
    rw [multiIndexEquiv_succ_apply]
    set β := (Fin.succFunEquiv ℕ (d + 1) α).1
    set a := (Fin.succFunEquiv ℕ (d + 1) α).2
    set m := multiIndexEquiv d β
    have h_abs := multiIndex_abs_succ d α
    have h_pair_bound : (1 : ℝ) + ↑(Nat.pair m a) ≤ ((1 + ↑m) + ↑a) ^ 2 := by
      have h1 : Nat.pair m a < (max m a + 1) ^ 2 := Nat.pair_lt_max_add_one_sq m a
      have h2 : max m a + 1 ≤ m + a + 1 := by omega
      have h3 : (max m a + 1) ^ 2 ≤ (m + a + 1) ^ 2 := Nat.pow_le_pow_left h2 2
      have h4 : Nat.pair m a + 1 ≤ (m + a + 1) ^ 2 := by omega
      have h5 : ((Nat.pair m a + 1 : ℕ) : ℝ) ≤ (((m + a + 1) ^ 2 : ℕ) : ℝ) :=
        Nat.cast_le.mpr h4
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at h5
      linarith
    have h_ih := hbound₁ β
    have h_one_abs : (1 : ℝ) ≤ 1 + (MultiIndex.abs α : ℝ) :=
      le_add_of_nonneg_right (Nat.cast_nonneg _)
    have h_β_le : (1 + (MultiIndex.abs β : ℝ)) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
      linarith [h_abs, (show (0 : ℝ) ≤ ↑a from Nat.cast_nonneg a)]
    have h_a_le : (a : ℝ) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
      linarith [h_abs, (show (0 : ℝ) ≤ (MultiIndex.abs β : ℝ) from Nat.cast_nonneg _)]
    have h_sum : (1 + (m : ℝ)) + ↑a ≤ (C₁ + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
      have hm : (1 : ℝ) + ↑m ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
        calc (1 : ℝ) + ↑m ≤ C₁ * (1 + (MultiIndex.abs β : ℝ)) ^ k₁ := h_ih
          _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ k₁ := by
              apply mul_le_mul_of_nonneg_left _ hC₁.le
              exact pow_le_pow_left₀ (by positivity) h_β_le k₁
          _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
              apply mul_le_mul_of_nonneg_left _ hC₁.le
              exact pow_le_pow_right₀ h_one_abs (Nat.le_succ k₁)
      have ha : (a : ℝ) ≤ 1 * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
        rw [one_mul]
        calc (a : ℝ) ≤ (1 + (MultiIndex.abs α : ℝ)) ^ 1 := by rw [pow_one]; exact h_a_le
          _ ≤ (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) :=
              pow_le_pow_right₀ h_one_abs (by omega)
      linarith
    calc (1 : ℝ) + ↑(Nat.pair m a)
        ≤ ((1 + ↑m) + ↑a) ^ 2 := h_pair_bound
      _ ≤ ((C₁ + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1)) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) h_sum
      _ = (C₁ + 1) ^ 2 * (1 + (MultiIndex.abs α : ℝ)) ^ (2 * (k₁ + 1)) := by
          rw [mul_pow]; ring_nf
lemma multiIndexEquiv_symm_growth (d : ℕ) :
    ∃ C > 0, ∃ k : ℕ, ∀ n : ℕ,
      (1 + (MultiIndex.abs ((multiIndexEquiv d).symm n) : ℝ)) ≤ C * (1 + (n : ℝ)) ^ k := by
  induction d with
  | zero =>
    refine ⟨1, one_pos, 1, fun n => ?_⟩
    simp only [multiIndexEquiv, one_mul, pow_one, MultiIndex.abs]
    show (1 : ℝ) + ↑((Equiv.funUnique (Fin 1) ℕ).symm n 0) ≤ 1 + ↑n
    simp [Equiv.funUnique]
  | succ d ih =>
    obtain ⟨C₁, hC₁, k₁, hbound₁⟩ := ih
    refine ⟨C₁ + 1, by linarith, k₁ + 1, fun n => ?_⟩
    rw [multiIndex_abs_succ_symm]
    set p := (Nat.unpair n).1
    set q := (Nat.unpair n).2
    have h_unpair : (p : ℝ) + ↑q ≤ ↑n := by
      exact_mod_cast Nat.unpair_add_le n
    have h_p_le : (p : ℝ) ≤ ↑n := by linarith [show (0 : ℝ) ≤ ↑q from Nat.cast_nonneg q]
    have h_q_le : (q : ℝ) ≤ ↑n := by linarith [show (0 : ℝ) ≤ ↑p from Nat.cast_nonneg p]
    have h_one_n : (1 : ℝ) ≤ 1 + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have h_ih := hbound₁ p
    have h_1p : (1 : ℝ) + ↑p ≤ 1 + ↑n := by linarith
    have h_beta : (1 : ℝ) + ↑(MultiIndex.abs ((multiIndexEquiv d).symm p)) ≤
        C₁ * (1 + ↑n) ^ k₁ := by
      calc _ ≤ C₁ * (1 + ↑p) ^ k₁ := h_ih
        _ ≤ C₁ * (1 + ↑n) ^ k₁ := by
            apply mul_le_mul_of_nonneg_left _ hC₁.le
            exact pow_le_pow_left₀ (by positivity) h_1p k₁
    calc (1 : ℝ) + (↑(MultiIndex.abs ((multiIndexEquiv d).symm p)) + ↑q)
        ≤ C₁ * (1 + ↑n) ^ k₁ + ↑n := by linarith [h_beta, h_q_le]
      _ ≤ C₁ * (1 + ↑n) ^ (k₁ + 1) + (1 + ↑n) ^ (k₁ + 1) := by
          have hk : C₁ * (1 + ↑n) ^ k₁ ≤ C₁ * (1 + ↑n) ^ (k₁ + 1) := by
            apply mul_le_mul_of_nonneg_left _ hC₁.le
            exact pow_le_pow_right₀ h_one_n (Nat.le_succ k₁)
          have hn : (n : ℝ) ≤ (1 + ↑n) ^ (k₁ + 1) := by
            calc (n : ℝ) ≤ (1 + ↑n) ^ 1 := by rw [pow_one]; linarith
              _ ≤ (1 + ↑n) ^ (k₁ + 1) := pow_le_pow_right₀ h_one_n (by omega)
          linarith
      _ = (C₁ + 1) * (1 + ↑n) ^ (k₁ + 1) := by ring
noncomputable def hermiteFunctionNd (d : ℕ) (α : MultiIndex d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => ∏ i : Fin d, hermiteFunction (α i) (x i)
private lemma hermiteFunctionNd_factor_contDiff (d : ℕ) (α : MultiIndex d) (i : Fin d) (m : ℕ) :
    ContDiff ℝ m (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction (α i) (x i)) :=
  (hermiteFunction_contDiff (α i) m).comp (contDiff_piLp_apply (p := 2))
private lemma hermiteFunctionNd_contDiff (d : ℕ) (α : MultiIndex d) :
    ContDiff ℝ ∞ (hermiteFunctionNd d α) := by
  apply contDiff_infty.mpr
  intro m
  exact contDiff_prod (fun i _ => hermiteFunctionNd_factor_contDiff d α i m)
private lemma hermiteFunction_schwartz_seminorm_bound (n k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |t| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction n) t‖ ≤ C := by
  obtain ⟨φ, hφ⟩ := hermiteFunction_schwartz n
  have hcoe : (fun t => hermiteFunction n t) = ⇑φ := (funext hφ).symm
  refine ⟨SchwartzMap.seminorm ℝ k m φ, apply_nonneg _ _, fun t => ?_⟩
  have hle := SchwartzMap.le_seminorm ℝ k m φ t
  rw [Real.norm_eq_abs] at hle
  rwa [show iteratedFDeriv ℝ m (⇑φ) t = iteratedFDeriv ℝ m (hermiteFunction n) t from
    congr_arg (iteratedFDeriv ℝ m · t) hcoe.symm] at hle
private lemma euclidean_proj_norm_le_one (d : ℕ) (i : Fin d) :
    ‖(EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simp only [one_mul]; exact PiLp.norm_apply_le (p := 2) x i)
private lemma norm_iteratedFDeriv_hermite_comp_proj_le (d : ℕ) (n : ℕ) (i : Fin d) (m : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ m
      (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) x‖ ≤
    ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ := by
  have hf_smooth : ContDiff ℝ ∞ (hermiteFunction n) :=
    contDiff_infty.mpr (hermiteFunction_contDiff n)
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) i
  have hL_le : ‖L‖ ≤ 1 := euclidean_proj_norm_le_one d i
  have hcomp : (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) =
      (hermiteFunction n) ∘ L := rfl
  have hiFD : iteratedFDeriv ℝ m ((hermiteFunction n) ∘ L) x =
      (iteratedFDeriv ℝ m (hermiteFunction n) (L x)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hf_smooth x (i := m) (mod_cast le_top)
  have h_prod_le : ∏ _j : Fin m, ‖L‖ ≤ 1 := by
    calc ∏ _j : Fin m, ‖L‖ ≤ ∏ _j : Fin m, (1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hL_le)
      _ = 1 := by simp
  rw [hcomp, hiFD]
  calc ‖(iteratedFDeriv ℝ m (hermiteFunction n) (L x)).compContinuousLinearMap
        (fun _ => L)‖
      ≤ ‖iteratedFDeriv ℝ m (hermiteFunction n) (L x)‖ * ∏ _j : Fin m, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ * 1 :=
        mul_le_mul_of_nonneg_left h_prod_le (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ := mul_one _
private lemma iteratedFDeriv_hermite_comp_proj_bound (d : ℕ) (n : ℕ) (i : Fin d) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      |x i| ^ k * ‖iteratedFDeriv ℝ m
        (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hermiteFunction_schwartz_seminorm_bound n k m
  refine ⟨C, hC, fun x => ?_⟩
  calc |x i| ^ k * ‖iteratedFDeriv ℝ m
        (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction n (x i)) x‖
      ≤ |x i| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction n) (x i)‖ :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_hermite_comp_proj_le d n i m x)
          (pow_nonneg (abs_nonneg _) _)
    _ ≤ C := hbound (x i)
private lemma hermiteFunctionNd_decay (d : ℕ) (α : MultiIndex d) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (hermiteFunctionNd d α) x‖ ≤ C := by
  rcases d with _ | d
  ·
    refine ⟨1, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.eq_zero x
    subst hx
    simp only [norm_zero]
    rcases k with _ | k
    · simp only [pow_zero, one_mul]
      have hf : hermiteFunctionNd 0 α = fun _ => 1 := by
        ext x; simp [hermiteFunctionNd, Finset.prod_empty]
      rw [hf]
      rcases n with _ | n
      · simp
      · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
    · simp [zero_pow (Nat.succ_ne_zero k), zero_mul]
  set fac : Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
    fun j x => hermiteFunction (α j) (x j)
  have hfac_smooth : ∀ j, ContDiff ℝ ∞ (fac j) := fun j =>
    contDiff_infty.mpr (hermiteFunctionNd_factor_contDiff (d + 1) α j)
  have hprod_eq : (fun x => ∏ j : Fin (d + 1), fac j x) = hermiteFunctionNd (d + 1) α := by
    ext x; simp [hermiteFunctionNd, fac]
  have hfac_bound : ∀ j : Fin (d + 1), ∀ m : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
        ‖iteratedFDeriv ℝ m (fac j) x‖ ≤ M := by
    intro j m
    obtain ⟨C, hC, hbound⟩ := iteratedFDeriv_hermite_comp_proj_bound (d + 1) (α j) j 0 m
    exact ⟨C, hC, fun x => by simpa using hbound x⟩
  have hfac_decay : ∀ j : Fin (d + 1), ∀ m : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
        |x j| ^ k * ‖iteratedFDeriv ℝ m (fac j) x‖ ≤ C := by
    intro j m
    exact iteratedFDeriv_hermite_comp_proj_bound (d + 1) (α j) j k m
  have h_l2_le_l1 : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ≤ ∑ j : Fin (d + 1), |x j| := by
    intro x
    rw [EuclideanSpace.norm_eq]
    have hsq : ∑ j : Fin (d + 1), ‖x j‖ ^ 2 ≤
        (∑ j : Fin (d + 1), |x j|) ^ 2 := by
      simpa only [Real.norm_eq_abs] using
        Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (fun j _ => abs_nonneg (x j))
    calc √(∑ j, ‖x j‖ ^ 2) ≤ √((∑ j, |x j|) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = ∑ j, |x j| := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
            (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
  have h_norm_pow_le : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ^ k ≤ ((d + 1 : ℝ) ^ k) * ∑ j : Fin (d + 1), |x j| ^ k := by
    intro x
    rcases k with _ | k
    ·
      simp only [pow_zero, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    have h1 : (1 : ℝ) ≤ (d + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    calc ‖x‖ ^ (k + 1) ≤ (∑ j : Fin (d + 1), |x j|) ^ (k + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) (h_l2_le_l1 x) _
      _ ≤ ((Finset.univ : Finset (Fin (d + 1))).card : ℝ) ^ k *
            ∑ j ∈ Finset.univ, |x j| ^ (k + 1) :=
          _root_.pow_sum_le_card_mul_sum_pow (fun j _ => abs_nonneg (x j)) k
      _ = (d + 1 : ℝ) ^ k * ∑ j : Fin (d + 1), |x j| ^ (k + 1) := by
          simp [Finset.card_univ, Fintype.card_fin]
      _ ≤ (d + 1 : ℝ) ^ (k + 1) * ∑ j : Fin (d + 1), |x j| ^ (k + 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_right₀ h1 (Nat.le_succ k)
          · exact Finset.sum_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  have hprod_bound : ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      ‖iteratedFDeriv ℝ n (fun z => ∏ j : Fin (d + 1), fac j z) y‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
        (p : Multiset (Fin (d + 1))).countPerms *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) y‖ := by
    intro y
    exact norm_iteratedFDeriv_prod_le
      (fun j _ => hfac_smooth j) (mod_cast le_top)
  have hprod_eq' : ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      iteratedFDeriv ℝ n (hermiteFunctionNd (d + 1) α) y =
      iteratedFDeriv ℝ n (fun z => ∏ j : Fin (d + 1), fac j z) y := by
    intro y; rw [hprod_eq]
  choose M hM using hfac_bound
  choose C_dec hC_dec using hfac_decay
  have h_term : ∀ (x : EuclideanSpace ℝ (Fin (d + 1)))
      (j₀ : Fin (d + 1)) (p : Sym (Fin (d + 1)) n),
      |x j₀| ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ ≤
        C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
            M j ((p : Multiset (Fin (d + 1))).count j) := by
    intro x j₀ p
    rw [(Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 1)))
      (fun j => ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖)
      (Finset.mem_univ j₀)).symm, ← mul_assoc]
    exact mul_le_mul
      ((hC_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀)).2 x)
      (Finset.prod_le_prod (fun j _ => norm_nonneg _)
        (fun j _ => (hM j ((p : Multiset (Fin (d + 1))).count j)).2 x))
      (Finset.prod_nonneg fun j _ => norm_nonneg _)
      ((hC_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀)).1)
  have h_full : ∀ (x : EuclideanSpace ℝ (Fin (d + 1)))
      (p : Sym (Fin (d + 1)) n),
      ‖x‖ ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ ≤
        (d + 1 : ℝ) ^ k *
          ∑ j₀ : Fin (d + 1),
            C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                M j ((p : Multiset (Fin (d + 1))).count j) := by
    intro x p
    calc ‖x‖ ^ k *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖
        ≤ ((d + 1 : ℝ) ^ k * ∑ j₀ : Fin (d + 1), |x j₀| ^ k) *
            ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
              ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ :=
          mul_le_mul_of_nonneg_right (h_norm_pow_le x)
            (Finset.prod_nonneg fun j _ => norm_nonneg _)
      _ = (d + 1 : ℝ) ^ k *
            ∑ j₀ : Fin (d + 1), |x j₀| ^ k *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ := by
          rw [mul_assoc, Finset.sum_mul]
      _ ≤ (d + 1 : ℝ) ^ k *
            ∑ j₀ : Fin (d + 1),
              C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
                ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                  M j ((p : Multiset (Fin (d + 1))).count j) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum fun j₀ _ => h_term x j₀ p
          · positivity
  refine ⟨∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
      (p : Multiset (Fin (d + 1))).countPerms *
        ((d + 1 : ℝ) ^ k *
          ∑ j₀ : Fin (d + 1),
            C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                M j ((p : Multiset (Fin (d + 1))).count j)),
    fun x => ?_⟩
  rw [hprod_eq' x]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => ∏ j : Fin (d + 1), fac j z) x‖
      ≤ ‖x‖ ^ k *
          ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
            (p : Multiset (Fin (d + 1))).countPerms *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac j) x‖ :=
        mul_le_mul_of_nonneg_left (hprod_bound x) (pow_nonneg (norm_nonneg _) _)
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym n,
          (p : Multiset (Fin (d + 1))).countPerms *
            ((d + 1 : ℝ) ^ k *
              ∑ j₀ : Fin (d + 1),
                C_dec j₀ ((p : Multiset (Fin (d + 1))).count j₀) *
                  ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
                    M j ((p : Multiset (Fin (d + 1))).count j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p _
        rw [mul_left_comm (‖x‖ ^ k)]
        exact mul_le_mul_of_nonneg_left (h_full x p) (by positivity)
noncomputable def schwartzHermiteBasisNd (d : ℕ) (α : MultiIndex d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ where
  toFun := hermiteFunctionNd d α
  smooth' := hermiteFunctionNd_contDiff d α
  decay' := hermiteFunctionNd_decay d α
noncomputable def hermiteCoeffNd (d : ℕ) (α : MultiIndex d)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) : ℝ :=
  ∫ x, f x * hermiteFunctionNd d α x
lemma hermiteCoeffNd_eq_hermiteCoeff1D
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ) (n : ℕ) :
    hermiteCoeffNd 1 (fun _ : Fin 1 => n) f =
    hermiteCoeff1D n ((schwartzDomCongr euclideanFin1Equiv).symm f) := by
  unfold hermiteCoeffNd hermiteCoeff1D hermiteFunctionNd
  simp only [Fin.prod_univ_one]
  symm
  rw [← euclideanFin1MeasEquiv_mp.integral_comp']
  congr 1; ext x
  simp only [euclideanFin1MeasEquiv_apply]
  congr 1
  show f (euclideanFin1Equiv.symm (x 0)) = f x
  congr 1; simp [euclideanFin1Equiv]; ext i; fin_cases i; rfl
private lemma schwartz_mul_hermiteBasisNd_integrable (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (α : MultiIndex d) :
    Integrable (fun x => f x * hermiteFunctionNd d α x) :=
  (f.memLp 2 volume).integrable_mul ((schwartzHermiteBasisNd d α).memLp 2 volume)
private lemma euclideanSnoc_castSucc (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    euclideanSnoc d y t (Fin.castSucc i) = y i := by
  unfold euclideanSnoc
  simp [Fin.snoc_castSucc]
private lemma euclideanSnoc_last (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    euclideanSnoc d y t (Fin.last d) = t := by
  unfold euclideanSnoc
  simp [Fin.snoc_last]
private lemma hermiteFunctionNd_snoc (d : ℕ) (α : MultiIndex (d + 2))
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    hermiteFunctionNd (d + 2) α (euclideanSnoc (d + 1) y t) =
    hermiteFunctionNd (d + 1) (fun i => α (Fin.castSucc i)) y *
    hermiteFunction (α (Fin.last (d + 1))) t := by
  unfold hermiteFunctionNd
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [euclideanSnoc_castSucc]
  · rw [euclideanSnoc_last]
private lemma hermiteCoeffNd_fubini (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (α : MultiIndex (d + 2)) :
    hermiteCoeffNd (d + 2) α f =
      hermiteCoeffNd (d + 1) (fun i => α (Fin.castSucc i))
        (schwartz_partial_hermiteCoeff d f (α (Fin.last (d + 1)))) := by
  unfold hermiteCoeffNd
  rw [integral_euclidean_snoc d _ (schwartz_mul_hermiteBasisNd_integrable (d + 2) f α)]
  congr 1
  ext y
  rw [schwartz_partial_hermiteCoeff_eq_1D]
  unfold hermiteCoeff1D
  have h_factor : ∀ t, f (euclideanSnoc (d + 1) y t) * hermiteFunctionNd (d + 2) α (euclideanSnoc (d + 1) y t) =
      (f (euclideanSnoc (d + 1) y t) * hermiteFunction (α (Fin.last (d + 1))) t) *
      hermiteFunctionNd (d + 1) (fun i => α (Fin.castSucc i)) y := by
    intro t
    rw [hermiteFunctionNd_snoc]
    ring
  simp_rw [h_factor]
  have h_pull := @integral_smul_const ℝ ℝ _ volume _ _ ℝ _ _ _
    (fun t => f (euclideanSnoc (d + 1) y t) * hermiteFunction (α (Fin.last (d + 1))) t)
    (hermiteFunctionNd (d + 1) (fun i => α (Fin.castSucc i)) y)
  simp only [smul_eq_mul] at h_pull
  rw [h_pull]
  congr 1
private lemma schwartz_partial_hermiteCoeff_seminorm_bound (d : ℕ) (k' l' : ℕ) (k : ℝ) :
    ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ),
        SchwartzMap.seminorm ℝ k' l'
          (schwartz_partial_hermiteCoeff d f n) * (1 + (n : ℝ)) ^ k ≤
          C * q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
  obtain ⟨C₁, q₁_raw, hC₁, h1decay⟩ := hermiteCoeff1D_decay k
  set q₁ := Finset.Iic q₁_raw with hq₁_def
  have hne : q₁.Nonempty := ⟨⊥, Finset.mem_Iic.mpr bot_le⟩
  have h_single : ∀ idx : ℕ × ℕ, ∃ (C_i : ℝ) (q_i : Finset (ℕ × ℕ)), 0 < C_i ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
        (y : EuclideanSpace ℝ (Fin (d + 1)))
        (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))),
        ‖y‖ ^ k' * schwartzSeminormFamily ℝ ℝ ℝ idx
          (schwartz_slice_partial d f l' y v) ≤
          C_i * (∏ i, ‖v i‖) *
            q_i.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
    intro ⟨a, b⟩
    exact schwartz_slice_partial_seminorm_bound d k' l' a b
  choose C_fn q_fn hC_pos h_bnd using h_single
  set C_max := q₁.sup' hne C_fn
  set q₂ := q₁.biUnion q_fn
  set C₂ := C₁ * C_max
  have hC_max_pos : 0 < C_max :=
    lt_of_lt_of_le (hC_pos hne.choose) (Finset.le_sup' C_fn hne.choose_spec)
  have hC₂_pos : 0 < C₂ := mul_pos hC₁ hC_max_pos
  refine ⟨C₂, q₂, hC₂_pos, fun f n => ?_⟩
  set g := schwartz_partial_hermiteCoeff d f n
  set S_f := q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f
  have hSf_nonneg : 0 ≤ S_f := apply_nonneg _ _
  have hc : 0 < (1 + (n : ℝ)) ^ k := by positivity
  rw [← le_div_iff₀ hc]
  apply SchwartzMap.seminorm_le_bound ℝ k' l' _
    (div_nonneg (mul_nonneg hC₂_pos.le hSf_nonneg) hc.le)
  intro y
  set c := ‖y‖ ^ k'
  have hc_nonneg : 0 ≤ c := by positivity
  show c * ‖iteratedFDeriv ℝ l' g y‖ ≤ C₂ * S_f / (1 + (n : ℝ)) ^ k
  rw [le_div_iff₀ hc]
  have hrw : c * ‖iteratedFDeriv ℝ l' g y‖ * (1 + (n : ℝ)) ^ k =
      ‖c • iteratedFDeriv ℝ l' g y‖ * (1 + (n : ℝ)) ^ k := by
    rw [norm_smul, Real.norm_of_nonneg hc_nonneg]
  rw [hrw]
  have h_op : ‖c • iteratedFDeriv ℝ l' g y‖ ≤ C₂ * S_f / (1 + (n : ℝ)) ^ k := by
    apply ContinuousMultilinearMap.opNorm_le_bound
      (div_nonneg (mul_nonneg hC₂_pos.le hSf_nonneg) hc.le)
    intro v
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have heval : ‖(c • iteratedFDeriv ℝ l' g y) v‖ =
        c * ‖iteratedFDeriv ℝ l' g y v‖ := by
      rw [smul_apply, norm_smul, Real.norm_of_nonneg hc_nonneg]
    rw [heval]
    have h_comm := schwartz_partial_hermiteCoeff_iteratedFDeriv d f n l' y v
    rw [h_comm]
    set slice := schwartz_slice_partial d f l' y v
    have h_decay := h1decay slice n
    calc c * ‖hermiteCoeff1D n slice‖ * (1 + (n : ℝ)) ^ k
        = c * (|hermiteCoeff1D n slice| * (1 + (n : ℝ)) ^ k) := by
          rw [Real.norm_eq_abs]; ring
      _ ≤ c * (C₁ * q₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) slice) :=
          mul_le_mul_of_nonneg_left h_decay hc_nonneg
      _ = C₁ * (c * q₁.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) slice) := by ring
      _ ≤ C₁ * (C_max * (∏ i, ‖v i‖) * S_f) := by
          apply mul_le_mul_of_nonneg_left _ hC₁.le
          rcases eq_or_ne c 0 with hc0 | hcne
          · rw [hc0, zero_mul]
            exact mul_nonneg (mul_nonneg hC_max_pos.le
              (Finset.prod_nonneg fun _ _ => norm_nonneg _)) hSf_nonneg
          · have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg hcne.symm
            rw [← le_div_iff₀' hc_pos]
            apply Seminorm.finset_sup_apply_le
              (div_nonneg (mul_nonneg (mul_nonneg hC_max_pos.le
                (Finset.prod_nonneg fun _ _ => norm_nonneg _)) hSf_nonneg) hc_pos.le)
            intro idx hidx
            rw [le_div_iff₀' hc_pos]
            calc c * (fun m => SchwartzMap.seminorm ℝ m.1 m.2) idx slice
                = c * schwartzSeminormFamily ℝ ℝ ℝ idx slice := rfl
              _ ≤ C_fn idx * (∏ i, ‖v i‖) *
                  (q_fn idx).sup (schwartzSeminormFamily ℝ _ ℝ) f :=
                h_bnd idx f y v
              _ ≤ C_max * (∏ i, ‖v i‖) *
                  (q_fn idx).sup (schwartzSeminormFamily ℝ _ ℝ) f := by
                  apply mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (Finset.le_sup' C_fn hidx)
                      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
                    (apply_nonneg _ _)
              _ ≤ C_max * (∏ i, ‖v i‖) * S_f := by
                  apply mul_le_mul_of_nonneg_left
                  · exact (Finset.sup_mono
                      (f := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
                      (Finset.subset_biUnion_of_mem q_fn hidx)) f
                  · exact mul_nonneg hC_max_pos.le
                      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = C₁ * C_max * S_f * ∏ i, ‖v i‖ := by ring
      _ = C₂ * S_f * ∏ i, ‖v i‖ := rfl
  calc ‖c • iteratedFDeriv ℝ l' g y‖ * (1 + (n : ℝ)) ^ k
      ≤ (C₂ * S_f / (1 + (n : ℝ)) ^ k) * (1 + (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right h_op hc.le
    _ = C₂ * S_f := div_mul_cancel₀ _ hc.ne.symm
private lemma schwartz_partial_hermiteCoeff_seminorm_bound'
    (d : ℕ) (q : Finset (ℕ × ℕ)) (k : ℝ) :
    ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ),
        q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
          (schwartz_partial_hermiteCoeff d f n) * (1 + (n : ℝ)) ^ k ≤
          C * q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
  by_cases hq : q = ∅
  · exact ⟨1, ∅, one_pos, fun f n => by simp [hq, zero_mul]⟩
  ·
    have h_single : ∀ idx : ℕ × ℕ, ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
        ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ),
          schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ idx
            (schwartz_partial_hermiteCoeff d f n) * (1 + (n : ℝ)) ^ k ≤
            C * q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f := by
      intro ⟨k', l'⟩
      exact schwartz_partial_hermiteCoeff_seminorm_bound d k' l' k
    choose C_fn q'_fn hC_pos h_bnd using h_single
    have hne := Finset.nonempty_of_ne_empty hq
    have hCM : 0 < q.sup' hne C_fn :=
      lt_of_lt_of_le (hC_pos hne.choose) (Finset.le_sup' C_fn hne.choose_spec)
    refine ⟨q.sup' hne C_fn, q.biUnion q'_fn, hCM, fun f n => ?_⟩
    set B := q.sup' hne C_fn * (q.biUnion q'_fn).sup
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f
    have hc : (0 : ℝ) < (1 + (n : ℝ)) ^ k := by positivity
    have h_each : ∀ idx ∈ q,
        schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ idx
          (schwartz_partial_hermiteCoeff d f n) ≤ B / (1 + (n : ℝ)) ^ k := by
      intro idx hidx
      rw [le_div_iff₀ hc]
      calc schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ idx
              (schwartz_partial_hermiteCoeff d f n) * (1 + (n : ℝ)) ^ k
          ≤ C_fn idx * (q'_fn idx).sup
              (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f :=
            h_bnd idx f n
        _ ≤ B := by
            apply mul_le_mul
            · exact Finset.le_sup' C_fn hidx
            · exact (Finset.sup_mono
                (f := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
                (Finset.subset_biUnion_of_mem q'_fn hidx)) f
            · exact apply_nonneg _ _
            · exact hCM.le
    have h_sup := Seminorm.finset_sup_apply_le
      (div_nonneg (mul_nonneg hCM.le (apply_nonneg _ _)) hc.le) h_each
    calc q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
            (schwartz_partial_hermiteCoeff d f n) * (1 + (n : ℝ)) ^ k
        ≤ B / (1 + (n : ℝ)) ^ k * (1 + (n : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_right h_sup hc.le
      _ = B := div_mul_cancel₀ B (ne_of_gt hc)
private lemma hermiteCoeffNd_injective_succ (d' : ℕ)
    (ih : ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ,
      (∀ α : MultiIndex (d' + 1), hermiteCoeffNd (d' + 1) α f = 0) → f = 0)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 2))) ℝ)
    (h : ∀ α : MultiIndex (d' + 2), hermiteCoeffNd (d' + 2) α f = 0) : f = 0 := by
  have h_partial : ∀ n, schwartz_partial_hermiteCoeff d' f n = 0 := by
    intro n
    apply ih
    intro β
    have := hermiteCoeffNd_fubini d' f (Fin.snoc β n)
    simp only [Fin.snoc_last] at this
    rw [h] at this
    convert this.symm using 1
    congr 1; funext i; simp [Fin.snoc_castSucc]
  have h_slice : ∀ y, schwartz_slice d' f y = 0 := by
    intro y
    have h_coeff : ∀ n, hermiteCoeff1D n (schwartz_slice d' f y) = 0 := by
      intro n
      rw [← schwartz_partial_hermiteCoeff_eq_1D]
      exact congr_fun (congrArg SchwartzMap.toFun (h_partial n)) y
    have hs' := schwartz_hermite_hasSum (schwartz_slice d' f y)
    have heq : (fun n => hermiteCoeff1D n (schwartz_slice d' f y) •
        schwartzHermiteBasis1D n) = fun _ => 0 := by
      ext n; simp [h_coeff n]
    rw [heq] at hs'
    exact hs'.unique hasSum_zero
  ext x
  have h_zero : ∀ y t, (schwartz_slice d' f y) t = 0 := by
    intro y t
    exact congr_fun (congrArg SchwartzMap.toFun (h_slice y)) t
  have h_val := h_zero (euclideanInit (d' + 1) x) (x (Fin.last (d' + 1)))
  rw [schwartz_slice_eq] at h_val
  change f x = 0
  rw [← euclideanSnoc_init_last (d' + 1) x]
  exact h_val
private lemma hermiteCoeffNd_injective (d' : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
    (h : ∀ α : MultiIndex (d' + 1), hermiteCoeffNd (d' + 1) α f = 0) : f = 0 := by
  induction d' with
  | zero =>
    let g := (schwartzDomCongr euclideanFin1Equiv).symm f
    have h_coeff : ∀ n : ℕ, hermiteCoeff1D n g = 0 := by
      intro n
      rw [← hermiteCoeffNd_eq_hermiteCoeff1D]
      exact h (fun _ => n)
    have hg : g = 0 := by
      have hs := schwartz_hermite_hasSum g
      have heq : (fun n => hermiteCoeff1D n g • schwartzHermiteBasis1D n) = fun _ => 0 := by
        ext n; simp [h_coeff n]
      rw [heq] at hs
      exact hs.unique hasSum_zero
    change (schwartzDomCongr euclideanFin1Equiv).symm f = 0 at hg
    exact (ContinuousLinearEquiv.injective _) (by rw [hg, map_zero])
  | succ d'' ih =>
    exact hermiteCoeffNd_injective_succ d''
      (fun g hg => ih g hg) f h
private lemma hermiteCoeffNd_decay (d' : ℕ) (k : ℝ) :
    ∃ (C : ℝ) (q : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
        (α : MultiIndex (d' + 1)),
        |hermiteCoeffNd (d' + 1) α f| * (1 + (MultiIndex.abs α : ℝ)) ^ k ≤
          C * q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) f := by
  induction d' with
  | zero =>
    obtain ⟨C₁, q₁, hC₁, h1d⟩ := hermiteCoeff1D_decay k
    set T : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
      (schwartzDomCongr euclideanFin1Equiv).symm.toContinuousLinearMap with hT_def
    have hw_src := schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin 1)) ℝ
    have h_per_idx : ∀ idx : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (Ci : ℝ), 0 < Ci ∧
        ∀ f, SchwartzMap.seminorm ℝ idx.1 idx.2 (T f) ≤
          Ci * s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
      intro ⟨k', l'⟩
      let p : Seminorm ℝ _ :=
        (SchwartzMap.seminorm ℝ k' l').comp T.toLinearMap
      have hp : Continuous p :=
        ((schwartz_withSeminorms ℝ ℝ ℝ).continuous_seminorm ⟨k', l'⟩).comp T.continuous
      obtain ⟨s, C, hCne, hle⟩ := Seminorm.bound_of_continuous hw_src p hp
      exact ⟨s, ↑C, by exact_mod_cast pos_iff_ne_zero.mpr hCne, fun f => by
        have := hle f; simp only [smul_apply] at this; exact this⟩
    have h_clm : ∃ (C₂ : ℝ) (q₂ : Finset (ℕ × ℕ)), 0 < C₂ ∧
        ∀ f, (Finset.Iic q₁).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (T f) ≤
          C₂ * q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
      by_cases hq : (Finset.Iic q₁) = ∅
      · exact ⟨1, ∅, one_pos, fun f => by simp [hq]⟩
      · choose s_fn C_fn hC_pos h_bnd using h_per_idx
        have hne := Finset.nonempty_of_ne_empty hq
        have hCM : 0 < (Finset.Iic q₁).sup' hne (C_fn ·) :=
          lt_of_lt_of_le (hC_pos hne.choose) (Finset.le_sup' _ hne.choose_spec)
        refine ⟨(Finset.Iic q₁).sup' hne (C_fn ·),
               (Finset.Iic q₁).biUnion (s_fn ·), hCM, fun f => ?_⟩
        apply Seminorm.finset_sup_apply_le (mul_nonneg hCM.le (apply_nonneg _ _))
        intro idx hidx
        calc SchwartzMap.seminorm ℝ idx.1 idx.2 (T f)
            ≤ C_fn idx * (s_fn idx).sup
                (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := h_bnd idx f
          _ ≤ (Finset.Iic q₁).sup' hne (C_fn ·) *
                ((Finset.Iic q₁).biUnion (s_fn ·)).sup
                  (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
              apply mul_le_mul
              · exact Finset.le_sup' _ hidx
              · exact (Finset.sup_mono
                  (f := schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
                  (Finset.subset_biUnion_of_mem (s_fn ·) hidx)) f
              · exact apply_nonneg _ _
              · exact hCM.le
    obtain ⟨C₂, q₂, hC₂, h_clm_bound⟩ := h_clm
    refine ⟨C₁ * C₂, q₂, mul_pos hC₁ hC₂, fun f α => ?_⟩
    have h_abs : MultiIndex.abs α = α 0 := by
      simp [MultiIndex.abs]
    rw [h_abs]
    set g := T f
    have h_coeff : hermiteCoeffNd 1 α f = hermiteCoeff1D (α 0) g := by
      have : α = fun _ => α 0 := by ext i; exact congr_arg α (Fin.eq_zero i)
      rw [this]
      exact hermiteCoeffNd_eq_hermiteCoeff1D f (α 0)
    rw [h_coeff]
    calc |hermiteCoeff1D (α 0) g| * (1 + (α 0 : ℝ)) ^ k
        ≤ C₁ * (Finset.Iic q₁).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g := h1d g (α 0)
      _ ≤ C₁ * (C₂ * q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f) :=
          mul_le_mul_of_nonneg_left (h_clm_bound f) hC₁.le
      _ = (C₁ * C₂) * q₂.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) f := by
          ring
  | succ d'' ih =>
    obtain ⟨C_ih, q_ih, hC_ih, h_ih⟩ := ih
    by_cases hk : k < 0
    ·
      obtain ⟨C_ax, q_ax, hC_ax, h_ax⟩ :=
        schwartz_partial_hermiteCoeff_seminorm_bound' d'' q_ih 0
      refine ⟨C_ih * C_ax, q_ax, mul_pos hC_ih hC_ax, fun f α => ?_⟩
      rw [hermiteCoeffNd_fubini d'' f α]
      set α_rest : MultiIndex (d'' + 1) := fun i => α (Fin.castSucc i)
      set n := α (Fin.last (d'' + 1))
      set g := schwartz_partial_hermiteCoeff d'' f n
      have h_abs_rest_le : (MultiIndex.abs α_rest : ℝ) ≤ MultiIndex.abs α := by
        exact_mod_cast show MultiIndex.abs α_rest ≤ MultiIndex.abs α from by
          have : MultiIndex.abs α = MultiIndex.abs α_rest + n := by
            simp only [MultiIndex.abs, α_rest, n]; exact Fin.sum_univ_castSucc α
          omega
      have h1α : (1 : ℝ) ≤ 1 + (MultiIndex.abs α_rest : ℝ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg _)
      have h_weight : (1 + (MultiIndex.abs α : ℝ)) ^ k ≤
          (1 + (MultiIndex.abs α_rest : ℝ)) ^ k := by
        apply rpow_le_rpow_of_nonpos (by linarith) (by linarith) hk.le
      have h_ax0 := h_ax f n
      simp only [rpow_zero, mul_one] at h_ax0
      calc |hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α : ℝ)) ^ k
          ≤ |hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α_rest : ℝ)) ^ k :=
            mul_le_mul_of_nonneg_left h_weight (abs_nonneg _)
        _ ≤ C_ih * q_ih.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 1))) ℝ) g := h_ih g α_rest
        _ ≤ C_ih * (C_ax * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f) :=
            mul_le_mul_of_nonneg_left h_ax0 hC_ih.le
        _ = (C_ih * C_ax) * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f := by ring
    ·
      push Not at hk
      obtain ⟨C_ax, q_ax, hC_ax, h_ax⟩ :=
        schwartz_partial_hermiteCoeff_seminorm_bound' d'' q_ih k
      refine ⟨C_ih * C_ax, q_ax, mul_pos hC_ih hC_ax, fun f α => ?_⟩
      rw [hermiteCoeffNd_fubini d'' f α]
      set α_rest : MultiIndex (d'' + 1) := fun i => α (Fin.castSucc i)
      set n := α (Fin.last (d'' + 1))
      set g := schwartz_partial_hermiteCoeff d'' f n
      have h_abs_eq : (MultiIndex.abs α : ℕ) =
          MultiIndex.abs α_rest + n := by
        simp only [MultiIndex.abs, α_rest, n]
        exact Fin.sum_univ_castSucc α
      have h_product_bound : (1 + (MultiIndex.abs α : ℝ)) ^ k ≤
          (1 + (MultiIndex.abs α_rest : ℝ)) ^ k * (1 + (n : ℝ)) ^ k := by
        rw [← mul_rpow (by positivity) (by positivity)]
        apply rpow_le_rpow (by positivity) _ hk
        calc (1 + (MultiIndex.abs α : ℝ))
            = 1 + (↑(MultiIndex.abs α_rest) + ↑n) := by push_cast [h_abs_eq]; ring
          _ ≤ (1 + ↑(MultiIndex.abs α_rest)) * (1 + ↑n) := by
              have : (1 + ↑(MultiIndex.abs α_rest)) * (1 + (↑n : ℝ)) =
                  1 + ↑(MultiIndex.abs α_rest) + ↑n + ↑(MultiIndex.abs α_rest) * ↑n := by ring
              linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (MultiIndex.abs α_rest))
                (Nat.cast_nonneg (α := ℝ) n)]
      calc |hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α : ℝ)) ^ k
          ≤ |hermiteCoeffNd (d'' + 1) α_rest g| *
              ((1 + (MultiIndex.abs α_rest : ℝ)) ^ k * (1 + (n : ℝ)) ^ k) :=
            mul_le_mul_of_nonneg_left h_product_bound (abs_nonneg _)
        _ = (|hermiteCoeffNd (d'' + 1) α_rest g| *
              (1 + (MultiIndex.abs α_rest : ℝ)) ^ k) * (1 + (n : ℝ)) ^ k := by ring
        _ ≤ (C_ih * q_ih.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 1))) ℝ) g) * (1 + (n : ℝ)) ^ k :=
            mul_le_mul_of_nonneg_right (h_ih g α_rest) (by positivity)
        _ = C_ih * (q_ih.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 1))) ℝ) g * (1 + (n : ℝ)) ^ k) := by ring
        _ ≤ C_ih * (C_ax * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f) :=
            mul_le_mul_of_nonneg_left (h_ax f n) hC_ih.le
        _ = (C_ih * C_ax) * q_ax.sup (schwartzSeminormFamily ℝ
              (EuclideanSpace ℝ (Fin (d'' + 2))) ℝ) f := by ring
private lemma schwartzHermiteBasisNd_growth (d : ℕ) (k l : ℕ) :
    ∃ (C : ℝ) (_ : 0 < C) (s : ℕ), ∀ (α : MultiIndex d),
      SchwartzMap.seminorm ℝ k l (schwartzHermiteBasisNd d α) ≤
        C * (1 + (MultiIndex.abs α : ℝ)) ^ s := by
  rcases d with _ | d
  · refine ⟨1, one_pos, 0, fun α => ?_⟩
    simp only [pow_zero, mul_one]
    apply SchwartzMap.seminorm_le_bound ℝ k l _ zero_le_one
    intro x
    have hx : x = 0 := Subsingleton.eq_zero x; subst hx
    simp only [norm_zero]
    rcases k with _ | k'
    · simp only [pow_zero, one_mul]
      have hf : ⇑(schwartzHermiteBasisNd 0 α) =
          fun (_ : EuclideanSpace ℝ (Fin 0)) => (1 : ℝ) := by
        ext y; show hermiteFunctionNd 0 α y = 1; simp [hermiteFunctionNd]
      rw [hf]
      rcases l with _ | l'
      · simp
      · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero l')]
    · simp [zero_pow (Nat.succ_ne_zero k'), zero_mul]
  choose C_0 hC_0_rest using fun m' => schwartzHermiteBasis1D_growth 0 m'
  choose s_0 hbound_0 using fun m' => (hC_0_rest m').2
  choose C_k hC_k_rest using fun m' => schwartzHermiteBasis1D_growth k m'
  choose s_k hbound_k using fun m' => (hC_k_rest m').2
  set C₁ := (Finset.range (l + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ l)⟩
    (fun m' => max (C_0 m') (C_k m') + 1) with hC₁_def
  set s₁ := (Finset.range (l + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ l)⟩
    (fun m' => max (s_0 m') (s_k m')) with hs₁_def
  have hC₁_pos : 0 < C₁ := by
    have : 0 < max (C_0 0) (C_k 0) + 1 := by linarith [le_max_left (C_0 0) (C_k 0), (hC_0_rest 0).1]
    exact lt_of_lt_of_le this
      (Finset.le_sup' (fun m' => max (C_0 m') (C_k m') + 1)
        (Finset.mem_range.mpr (Nat.zero_lt_succ l)))
  have h_unif_0 : ∀ m' ≤ l, ∀ n : ℕ,
      SchwartzMap.seminorm ℝ 0 m' (schwartzHermiteBasis1D n) ≤
        C₁ * (1 + (n : ℝ)) ^ s₁ := by
    intro m' hm' n
    have hmem : m' ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm')
    have hC : C_0 m' ≤ C₁ :=
      le_trans (le_trans (le_max_left (C_0 m') (C_k m'))
        (le_add_of_nonneg_right zero_le_one))
        (Finset.le_sup' (fun m' => max (C_0 m') (C_k m') + 1) hmem)
    have hs : s_0 m' ≤ s₁ :=
      le_trans (le_max_left (s_0 m') (s_k m'))
        (Finset.le_sup' (fun m' => max (s_0 m') (s_k m')) hmem)
    calc SchwartzMap.seminorm ℝ 0 m' (schwartzHermiteBasis1D n)
        ≤ C_0 m' * (1 + (n : ℝ)) ^ s_0 m' := hbound_0 m' n
      _ ≤ C₁ * (1 + (n : ℝ)) ^ s₁ :=
          mul_le_mul hC (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg n)) hs)
            (by positivity) hC₁_pos.le
  have h_unif_k : ∀ m' ≤ l, ∀ n : ℕ,
      SchwartzMap.seminorm ℝ k m' (schwartzHermiteBasis1D n) ≤
        C₁ * (1 + (n : ℝ)) ^ s₁ := by
    intro m' hm' n
    have hmem : m' ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm')
    have hC : C_k m' ≤ C₁ :=
      le_trans (le_trans (le_max_right (C_0 m') (C_k m'))
        (le_add_of_nonneg_right zero_le_one))
        (Finset.le_sup' (fun m' => max (C_0 m') (C_k m') + 1) hmem)
    have hs : s_k m' ≤ s₁ :=
      le_trans (le_max_right (s_0 m') (s_k m'))
        (Finset.le_sup' (fun m' => max (s_0 m') (s_k m')) hmem)
    calc SchwartzMap.seminorm ℝ k m' (schwartzHermiteBasis1D n)
        ≤ C_k m' * (1 + (n : ℝ)) ^ s_k m' := hbound_k m' n
      _ ≤ C₁ * (1 + (n : ℝ)) ^ s₁ :=
          mul_le_mul hC (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg n)) hs)
            (by positivity) hC₁_pos.le
  have h_alpha_le : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)),
      (1 + (α j : ℝ)) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
    intro α j; gcongr; show α j ≤ ∑ i, α i
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  suffices h_poly : ∃ (C : ℝ) (s : ℕ), 0 < C ∧
      ∀ (α : MultiIndex (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1))),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (hermiteFunctionNd (d + 1) α) x‖ ≤
          C * (1 + (MultiIndex.abs α : ℝ)) ^ s by
    obtain ⟨C, s, hC, hbound⟩ := h_poly
    exact ⟨C, hC, s, fun α =>
      SchwartzMap.seminorm_le_bound ℝ k l (schwartzHermiteBasisNd (d + 1) α) (by positivity)
        (hbound α)⟩
  set fac : MultiIndex (d + 1) → Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
    fun α j x => hermiteFunction (α j) (x j)
  have hfac_smooth : ∀ α j, ContDiff ℝ ∞ (fac α j) := fun α j =>
    contDiff_infty.mpr (hermiteFunctionNd_factor_contDiff (d + 1) α j)
  have hM_poly : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)) (m : ℕ) (_ : m ≤ l)
      (x : EuclideanSpace ℝ (Fin (d + 1))),
      ‖iteratedFDeriv ℝ m (fac α j) x‖ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ := by
    intro α j m hm x
    have h_le_sem : ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ ≤
        SchwartzMap.seminorm ℝ 0 m (schwartzHermiteBasis1D (α j)) := by
      have h := SchwartzMap.le_seminorm ℝ 0 m (schwartzHermiteBasis1D (α j)) (x j)
      simp only [pow_zero, one_mul] at h
      rwa [show iteratedFDeriv ℝ m (⇑(schwartzHermiteBasis1D (α j))) (x j) =
        iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j) from
        congr_arg (iteratedFDeriv ℝ m · (x j)) (schwartzHermiteBasis1D_coe (α j))] at h
    calc ‖iteratedFDeriv ℝ m (fac α j) x‖
        ≤ ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ :=
          norm_iteratedFDeriv_hermite_comp_proj_le (d + 1) (α j) j m x
      _ ≤ SchwartzMap.seminorm ℝ 0 m (schwartzHermiteBasis1D (α j)) := h_le_sem
      _ ≤ C₁ * (1 + (α j : ℝ)) ^ s₁ := h_unif_0 m hm (α j)
      _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (h_alpha_le α j) s₁) hC₁_pos.le
  have hC_poly : ∀ (α : MultiIndex (d + 1)) (j : Fin (d + 1)) (m : ℕ) (_ : m ≤ l)
      (x : EuclideanSpace ℝ (Fin (d + 1))),
      |x j| ^ k * ‖iteratedFDeriv ℝ m (fac α j) x‖ ≤
        C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ := by
    intro α j m hm x
    have h_le_sem : |x j| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ ≤
        SchwartzMap.seminorm ℝ k m (schwartzHermiteBasis1D (α j)) := by
      have h := SchwartzMap.le_seminorm ℝ k m (schwartzHermiteBasis1D (α j)) (x j)
      rw [Real.norm_eq_abs] at h
      rwa [show iteratedFDeriv ℝ m (⇑(schwartzHermiteBasis1D (α j))) (x j) =
        iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j) from
        congr_arg (iteratedFDeriv ℝ m · (x j)) (schwartzHermiteBasis1D_coe (α j))] at h
    calc |x j| ^ k * ‖iteratedFDeriv ℝ m (fac α j) x‖
        ≤ |x j| ^ k * ‖iteratedFDeriv ℝ m (hermiteFunction (α j)) (x j)‖ :=
          mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_hermite_comp_proj_le (d + 1) (α j) j m x)
            (pow_nonneg (abs_nonneg _) _)
      _ ≤ SchwartzMap.seminorm ℝ k m (schwartzHermiteBasis1D (α j)) := h_le_sem
      _ ≤ C₁ * (1 + (α j : ℝ)) ^ s₁ := h_unif_k m hm (α j)
      _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁ :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (h_alpha_le α j) s₁) hC₁_pos.le
  have h_count_le : ∀ (p : Sym (Fin (d + 1)) l) (j : Fin (d + 1)),
      (p : Multiset (Fin (d + 1))).count j ≤ l :=
    fun p j => (Multiset.count_le_card j ↑p).trans (le_of_eq p.prop)
  have h_l2_le_l1 : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ≤ ∑ j : Fin (d + 1), |x j| := by
    intro x
    rw [EuclideanSpace.norm_eq]
    have hsq : ∑ j : Fin (d + 1), ‖x j‖ ^ 2 ≤
        (∑ j : Fin (d + 1), |x j|) ^ 2 := by
      simpa only [Real.norm_eq_abs] using
        Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (fun j _ => abs_nonneg (x j))
    calc √(∑ j, ‖x j‖ ^ 2) ≤ √((∑ j, |x j|) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = ∑ j, |x j| := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
            (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
  have h_norm_pow_le : ∀ x : EuclideanSpace ℝ (Fin (d + 1)),
      ‖x‖ ^ k ≤ ((d + 1 : ℝ) ^ k) * ∑ j : Fin (d + 1), |x j| ^ k := by
    intro x
    rcases k with _ | k_
    · simp only [pow_zero, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    have h1 : (1 : ℝ) ≤ (d + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
    calc ‖x‖ ^ (k_ + 1) ≤ (∑ j : Fin (d + 1), |x j|) ^ (k_ + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) (h_l2_le_l1 x) _
      _ ≤ ((Finset.univ : Finset (Fin (d + 1))).card : ℝ) ^ k_ *
            ∑ j ∈ Finset.univ, |x j| ^ (k_ + 1) :=
          _root_.pow_sum_le_card_mul_sum_pow (fun j _ => abs_nonneg (x j)) k_
      _ = (d + 1 : ℝ) ^ k_ * ∑ j : Fin (d + 1), |x j| ^ (k_ + 1) := by
          simp [Finset.card_univ, Fintype.card_fin]
      _ ≤ (d + 1 : ℝ) ^ (k_ + 1) * ∑ j : Fin (d + 1), |x j| ^ (k_ + 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_right₀ h1 (Nat.le_succ k_)
          · exact Finset.sum_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)
  have hprod_eq : ∀ (α : MultiIndex (d + 1)),
      (fun x => ∏ j : Fin (d + 1), fac α j x) = hermiteFunctionNd (d + 1) α := by
    intro α; ext x; simp [hermiteFunctionNd, fac]
  have hprod_bound : ∀ (α : MultiIndex (d + 1)) (y : EuclideanSpace ℝ (Fin (d + 1))),
      ‖iteratedFDeriv ℝ l (fun z => ∏ j : Fin (d + 1), fac α j z) y‖ ≤
      ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
        (p : Multiset (Fin (d + 1))).countPerms *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) y‖ := by
    intro α y
    exact norm_iteratedFDeriv_prod_le
      (fun j _ => hfac_smooth α j) (mod_cast le_top)
  have h_term : ∀ (α : MultiIndex (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1)))
      (j₀ : Fin (d + 1)) (p : Sym (Fin (d + 1)) l),
      |x j₀| ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ ≤
        (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
    intro α x j₀ p
    rw [(Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 1)))
      (fun j => ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖)
      (Finset.mem_univ j₀)).symm, ← mul_assoc]
    calc |x j₀| ^ k * ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j₀) (fac α j₀) x‖ *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖
        ≤ (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) *
            ∏ _j ∈ (Finset.univ : Finset (Fin (d + 1))).erase j₀,
              (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) := by
          apply mul_le_mul
          · exact hC_poly α j₀ _ (h_count_le p j₀) x
          · exact Finset.prod_le_prod (fun j _ => norm_nonneg _)
              (fun j _ => hM_poly α j _ (h_count_le p j) x)
          · exact Finset.prod_nonneg fun j _ => norm_nonneg _
          · positivity
      _ = (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) *
            (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^
              ((Finset.univ : Finset (Fin (d + 1))).erase j₀).card := by
          rw [Finset.prod_const]
      _ ≤ (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
          have hcard : ((Finset.univ : Finset (Fin (d + 1))).erase j₀).card = d := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ j₀),
              Finset.card_univ, Fintype.card_fin]; omega
          rw [hcard, pow_succ']
  have h_full : ∀ (α : MultiIndex (d + 1)) (x : EuclideanSpace ℝ (Fin (d + 1)))
      (p : Sym (Fin (d + 1)) l),
      ‖x‖ ^ k *
        ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
          ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ ≤
        (d + 1 : ℝ) ^ (k + 1) *
          (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
    intro α x p
    calc ‖x‖ ^ k *
          ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
            ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖
        ≤ ((d + 1 : ℝ) ^ k * ∑ j₀ : Fin (d + 1), |x j₀| ^ k) *
            ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
              ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ :=
          mul_le_mul_of_nonneg_right (h_norm_pow_le x)
            (Finset.prod_nonneg fun j _ => norm_nonneg _)
      _ = (d + 1 : ℝ) ^ k *
            ∑ j₀ : Fin (d + 1), |x j₀| ^ k *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ := by
          rw [mul_assoc, Finset.sum_mul]
      _ ≤ (d + 1 : ℝ) ^ k *
            ∑ _j₀ : Fin (d + 1),
              (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum fun j₀ _ => h_term α x j₀ p
          · positivity
      _ = (d + 1 : ℝ) ^ (k + 1) *
            (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  set K := (d + 1 : ℝ) ^ (k + 1) * C₁ ^ (d + 1) *
    (∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
      ((p : Multiset (Fin (d + 1))).countPerms : ℝ)) with hK_def
  refine ⟨K + 1, (d + 1) * s₁, by positivity, fun α x => ?_⟩
  have hprod_eq' : iteratedFDeriv ℝ l (hermiteFunctionNd (d + 1) α) x =
      iteratedFDeriv ℝ l (fun z => ∏ j : Fin (d + 1), fac α j z) x :=
    congrArg (iteratedFDeriv ℝ l · x) (hprod_eq α).symm
  rw [hprod_eq']
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun z => ∏ j : Fin (d + 1), fac α j z) x‖
      ≤ ‖x‖ ^ k *
          ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
            (p : Multiset (Fin (d + 1))).countPerms *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖ :=
        mul_le_mul_of_nonneg_left (hprod_bound α x) (pow_nonneg (norm_nonneg _) _)
    _ = ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
          (p : Multiset (Fin (d + 1))).countPerms *
            (‖x‖ ^ k *
              ∏ j ∈ (Finset.univ : Finset (Fin (d + 1))),
                ‖iteratedFDeriv ℝ ((p : Multiset (Fin (d + 1))).count j) (fac α j) x‖) := by
        rw [Finset.mul_sum]; ring_nf
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin (d + 1))).sym l,
          (p : Multiset (Fin (d + 1))).countPerms *
            ((d + 1 : ℝ) ^ (k + 1) *
              (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) ^ (d + 1)) := by
        apply Finset.sum_le_sum; intro p _
        apply mul_le_mul_of_nonneg_left (h_full α x p) (by positivity)
    _ = K * (1 + (MultiIndex.abs α : ℝ)) ^ ((d + 1) * s₁) := by
        simp only [hK_def, mul_pow, ← Finset.sum_mul]; ring
    _ ≤ (K + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ ((d + 1) * s₁) := by
        apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        positivity
private lemma integral_euclidean_prod_eq_prod (d : ℕ)
    (f : Fin d → ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin d), ∏ i, f i (x i) =
      ∏ i : Fin d, ∫ t : ℝ, f i t := by
  have h_pi := integral_fintype_prod_volume_eq_prod f
  convert h_pi using 1
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
    (fun y : Fin d → ℝ => ∏ i, f i (y i))
private lemma hermiteFunctionNd_orthonormal (d : ℕ) (α β : MultiIndex d) :
    ∫ x : EuclideanSpace ℝ (Fin d),
      hermiteFunctionNd d α x * hermiteFunctionNd d β x =
      if α = β then 1 else 0 := by
  simp only [hermiteFunctionNd, ← Finset.prod_mul_distrib]
  rw [integral_euclidean_prod_eq_prod d
    (fun i t => hermiteFunction (α i) t * hermiteFunction (β i) t)]
  simp_rw [hermiteFunction_orthonormal]
  by_cases h : α = β
  · subst h; simp
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
private lemma hermiteCoeffNd_basisNd_kronecker (d : ℕ) (α β : MultiIndex d) :
    hermiteCoeffNd d α (schwartzHermiteBasisNd d β) = if α = β then 1 else 0 := by
  show ∫ x, schwartzHermiteBasisNd d β x * hermiteFunctionNd d α x = _
  simp_rw [show ∀ x, schwartzHermiteBasisNd d β x = hermiteFunctionNd d β x from fun _ => rfl]
  convert hermiteFunctionNd_orthonormal d β α using 1
  exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)
private lemma hermiteCoeffNd_linear (d : ℕ) (α : MultiIndex d) :
    IsLinearMap ℝ (hermiteCoeffNd d α) where
  map_add f g := by
    simp only [hermiteCoeffNd]
    rw [show (fun x => (f + g) x * hermiteFunctionNd d α x) =
      fun x => f x * hermiteFunctionNd d α x + g x * hermiteFunctionNd d α x from by
        ext x; simp [add_mul]]
    exact integral_add
      (schwartz_mul_hermiteBasisNd_integrable d f α)
      (schwartz_mul_hermiteBasisNd_integrable d g α)
  map_smul c f := by
    simp only [hermiteCoeffNd]
    rw [show (fun x => (c • f) x * hermiteFunctionNd d α x) =
      fun x => c * (f x * hermiteFunctionNd d α x) from by
        ext x; simp [smul_eq_mul, mul_assoc]]
    exact MeasureTheory.integral_const_mul c _
private noncomputable def hermiteCoeffNdCLM (d : ℕ) (α : MultiIndex d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ →L[ℝ] ℝ where
  toLinearMap := {
    toFun := hermiteCoeffNd d α
    map_add' := (hermiteCoeffNd_linear d α).map_add
    map_smul' := (hermiteCoeffNd_linear d α).map_smul
  }
  cont := by
    set Ψ := schwartzHermiteBasisNd d α
    set M := ∫ x : EuclideanSpace ℝ (Fin d), ‖Ψ x‖
    have hΨ_int : Integrable (⇑Ψ) volume := Ψ.integrable
    let lm : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ →ₗ[ℝ] ℝ := {
      toFun := hermiteCoeffNd d α
      map_add' := (hermiteCoeffNd_linear d α).map_add
      map_smul' := (hermiteCoeffNd_linear d α).map_smul
    }
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ _ ℝ) (norm_withSeminorms ℝ ℝ) lm
    intro _
    refine ⟨{(0, 0)}, ⟨M, integral_nonneg (fun _ => norm_nonneg _)⟩, fun f => ?_⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton, lm]
    show ‖hermiteCoeffNd d α f‖ ≤
      M * SchwartzMap.seminorm ℝ 0 0 f
    calc ‖hermiteCoeffNd d α f‖
        = ‖∫ x, f x * hermiteFunctionNd d α x‖ := rfl
      _ ≤ ∫ x, ‖f x * hermiteFunctionNd d α x‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x, ‖f x‖ * ‖Ψ x‖ := by
          congr 1; ext x; exact norm_mul _ _
      _ ≤ ∫ x, SchwartzMap.seminorm ℝ 0 0 f * ‖Ψ x‖ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun _ =>
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
          · exact hΨ_int.norm.const_mul _
          · exact Filter.Eventually.of_forall fun x =>
              mul_le_mul_of_nonneg_right
                (SchwartzMap.norm_le_seminorm ℝ f x) (norm_nonneg _)
      _ = SchwartzMap.seminorm ℝ 0 0 f * M := integral_const_mul _ _
      _ = M * SchwartzMap.seminorm ℝ 0 0 f := mul_comm _ _
@[simp] private theorem hermiteCoeffNdCLM_apply (d : ℕ) (α : MultiIndex d)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :
    hermiteCoeffNdCLM d α f = hermiteCoeffNd d α f := rfl
private theorem hermiteCoeffNd_rapid_decayFlat (d' : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) (k : ℕ) :
    Summable (fun n => |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| *
      (1 + (n : ℝ)) ^ k) := by
  obtain ⟨C₁, hC₁, k₁, hgrowth⟩ := multiIndexEquiv_growth d'
  obtain ⟨D, q, hD, hdecay⟩ := hermiteCoeffNd_decay d' (↑(k₁ * (k + 2)) : ℝ)
  set S := q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) f
  have h_le : ∀ n : ℕ,
      |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + (n : ℝ)) ^ k ≤
      D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    set α := (multiIndexEquiv d').symm n
    have h1n : (0 : ℝ) < 1 + ↑n := by positivity
    have hn_le : (1 + (n : ℝ)) ≤ C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁ := by
      have := hgrowth α; simp only [α, Equiv.apply_symm_apply] at this; exact this
    have h_bd : |hermiteCoeffNd (d' + 1) α f| *
        (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) ≤ D * S := by
      have := hdecay f α; rwa [rpow_natCast] at this
    have h_combined : |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2) ≤
        C₁ ^ (k + 2) * (D * S) := by
      calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2)
          ≤ |hermiteCoeffNd (d' + 1) α f| *
            (C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc (1 + ↑n) ^ (k + 2)
                ≤ (C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁) ^ (k + 2) :=
                  pow_le_pow_left₀ (by positivity) hn_le _
              _ = C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) := by
                  rw [mul_pow, ← pow_mul]
        _ = C₁ ^ (k + 2) * (|hermiteCoeffNd (d' + 1) α f| *
              (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by ring
        _ ≤ C₁ ^ (k + 2) * (D * S) :=
            mul_le_mul_of_nonneg_left h_bd (pow_nonneg hC₁.le _)
    rw [pow_add, ← mul_assoc] at h_combined
    calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ k
        ≤ C₁ ^ (k + 2) * (D * S) / (1 + ↑n) ^ 2 :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ↑n) ^ 2)).mpr h_combined
      _ = D * S * C₁ ^ (k + 2) * ((1 + ↑n) ^ (2 : ℕ))⁻¹ := by rw [div_eq_mul_inv]; ring
      _ = D * S * C₁ ^ (k + 2) * (1 + ↑n) ^ ((-2) : ℝ) := by
          congr 1
          rw [show ((-2 : ℝ) : ℝ) = -(↑2 : ℕ) from by norm_num]
          rw [rpow_neg h1n.le, rpow_natCast]
  have h_sum : Summable (fun n : ℕ => D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
    (((summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).comp_injective
      (fun a b h => Nat.succ_injective h)).congr
      (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm]))
    |>.const_smul (D * S * C₁ ^ (k + 2))
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _))
    h_le h_sum
private noncomputable def toRapidDecayNdLM (d' : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ →ₗ[ℝ] RapidDecaySeq where
  toFun f := ⟨fun n => hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f,
    hermiteCoeffNd_rapid_decayFlat d' f⟩
  map_add' f g := RapidDecaySeq.ext fun n =>
    (hermiteCoeffNd_linear (d' + 1) _).map_add f g
  map_smul' r f := RapidDecaySeq.ext fun n => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    exact (hermiteCoeffNd_linear (d' + 1) _).map_smul r f
private lemma toRapidDecayNdLM_isBounded (d' : ℕ) :
    Seminorm.IsBounded
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
      RapidDecaySeq.rapidDecaySeminorm
      (toRapidDecayNdLM d') := by
  intro k
  obtain ⟨C₁, hC₁, k₁, hgrowth⟩ := multiIndexEquiv_growth d'
  obtain ⟨D, q, hD, hdecay⟩ := hermiteCoeffNd_decay d' (↑(k₁ * (k + 2)) : ℝ)
  have h_rpow_sum : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
    ((summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).comp_injective
      (fun a b h => Nat.succ_injective h)).congr
      (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
  set L := ∑' n : ℕ, (1 + (n : ℝ)) ^ ((-2) : ℝ)
  refine ⟨q, ⟨D * C₁ ^ (k + 2) * L, by positivity⟩, fun f => ?_⟩
  simp only [Seminorm.comp_apply]
  set S := q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) f
  show ∑' n, |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + ↑n) ^ k ≤
    D * C₁ ^ (k + 2) * L * S
  have h_le : ∀ n : ℕ,
      |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + (n : ℝ)) ^ k ≤
      D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
    intro n
    set α := (multiIndexEquiv d').symm n
    have h1n : (0 : ℝ) < 1 + ↑n := by positivity
    have hn_le : (1 + (n : ℝ)) ≤ C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁ := by
      have := hgrowth α; simp only [α, Equiv.apply_symm_apply] at this; exact this
    have h_bd : |hermiteCoeffNd (d' + 1) α f| *
        (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) ≤ D * S := by
      have := hdecay f α; rwa [rpow_natCast] at this
    have h_combined : |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2) ≤
        C₁ ^ (k + 2) * (D * S) := by
      calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ (k + 2)
          ≤ |hermiteCoeffNd (d' + 1) α f| *
            (C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc (1 + ↑n) ^ (k + 2)
                ≤ (C₁ * (1 + ↑(MultiIndex.abs α)) ^ k₁) ^ (k + 2) :=
                  pow_le_pow_left₀ (by positivity) hn_le _
              _ = C₁ ^ (k + 2) * (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2)) := by
                  rw [mul_pow, ← pow_mul]
        _ = C₁ ^ (k + 2) * (|hermiteCoeffNd (d' + 1) α f| *
              (1 + ↑(MultiIndex.abs α)) ^ (k₁ * (k + 2))) := by ring
        _ ≤ C₁ ^ (k + 2) * (D * S) :=
            mul_le_mul_of_nonneg_left h_bd (pow_nonneg hC₁.le _)
    rw [pow_add, ← mul_assoc] at h_combined
    have hle : |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ k ≤
        D * S * C₁ ^ (k + 2) * (1 + ↑n) ^ ((-2) : ℝ) := by
      calc |hermiteCoeffNd (d' + 1) α f| * (1 + ↑n) ^ k
          ≤ C₁ ^ (k + 2) * (D * S) / (1 + ↑n) ^ 2 :=
            (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ↑n) ^ 2)).mpr h_combined
        _ = D * S * C₁ ^ (k + 2) * ((1 + ↑n) ^ (2 : ℕ))⁻¹ := by rw [div_eq_mul_inv]; ring
        _ = D * S * C₁ ^ (k + 2) * (1 + ↑n) ^ ((-2) : ℝ) := by
            congr 1
            rw [show ((-2 : ℝ) : ℝ) = -(↑2 : ℕ) from by norm_num]
            rw [rpow_neg h1n.le, rpow_natCast]
    exact hle
  calc ∑' n, |hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f| * (1 + ↑n) ^ k
      ≤ ∑' (n : ℕ), D * S * C₁ ^ (k + 2) * (1 + (n : ℝ)) ^ ((-2) : ℝ) :=
        (hermiteCoeffNd_rapid_decayFlat d' f k).tsum_le_tsum h_le
          (h_rpow_sum.const_smul (D * S * C₁ ^ (k + 2)))
    _ = D * S * C₁ ^ (k + 2) * L := tsum_mul_left
    _ = D * C₁ ^ (k + 2) * L * S := by ring
noncomputable def toRapidDecayNdCLM (d : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ →L[ℝ] RapidDecaySeq :=
  match d with
  | 0 => 0
  | d' + 1 => {
      toLinearMap := toRapidDecayNdLM d'
      cont := WithSeminorms.continuous_of_isBounded
        (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
        RapidDecaySeq.rapidDecay_withSeminorms
        _ (toRapidDecayNdLM_isBounded d')
    }
private noncomputable def flatBasisNd (d : ℕ) (n : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ :=
  schwartzHermiteBasisNd (d + 1) ((multiIndexEquiv d).symm n)
private lemma scalar_flatBasisNd_iFDeriv_bound (d : ℕ) (c : ℝ) (n l : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖iteratedFDeriv ℝ l (fun y => c * flatBasisNd d n y) x‖ ≤
      |c| * SchwartzMap.seminorm ℝ 0 l (flatBasisNd d n) := by
  have hcoe : (fun y => c * flatBasisNd d n y) = ⇑(c • flatBasisNd d n) := by
    ext y; simp [smul_eq_mul]
  rw [hcoe]
  calc ‖iteratedFDeriv ℝ l (⇑(c • flatBasisNd d n)) x‖
      ≤ (SchwartzMap.seminorm ℝ 0 l) (c • flatBasisNd d n) := by
          have h := SchwartzMap.le_seminorm ℝ 0 l (c • flatBasisNd d n) x
          simp only [pow_zero, one_mul] at h; exact h
    _ = |c| * (SchwartzMap.seminorm ℝ 0 l) (flatBasisNd d n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
private lemma rapidDecay_seminorm_summableNd (d : ℕ) (a : RapidDecaySeq) (k l : ℕ) :
    Summable (fun n => |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n)) := by
  obtain ⟨C₁, hC₁, s₁, hbasis⟩ := schwartzHermiteBasisNd_growth (d + 1) k l
  obtain ⟨C₂, hC₂, k₂, hsymm⟩ := multiIndexEquiv_symm_growth d
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (fun n => by
      set α := (multiIndexEquiv d).symm n
      calc |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n)
          ≤ |a.val n| * (C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ s₁) :=
            mul_le_mul_of_nonneg_left (hbasis α) (abs_nonneg _)
        _ ≤ |a.val n| * (C₁ * (C₂ * (1 + (n : ℝ)) ^ k₂) ^ s₁) := by
            gcongr; exact hsymm n
        _ = (C₁ * C₂ ^ s₁) * (|a.val n| * (1 + (n : ℝ)) ^ (k₂ * s₁)) := by
            rw [mul_pow]; ring)
    ((a.rapid_decay (k₂ * s₁)).mul_left (C₁ * C₂ ^ s₁))
private lemma rapidDecay_pointwise_summableNd (d : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    Summable (fun n => a.val n * flatBasisNd d n x) := by
  apply Summable.of_norm_bounded
    (g := fun n => |a.val n| * SchwartzMap.seminorm ℝ 0 0 (flatBasisNd d n))
  · exact rapidDecay_seminorm_summableNd d a 0 0
  · intro n
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by rw [← Real.norm_eq_abs]; exact SchwartzMap.norm_le_seminorm ℝ _ x)
      (abs_nonneg _)
private lemma rapidDecay_hermite_contDiffNd (d : ℕ) (a : RapidDecaySeq) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
      ∑' n, a.val n * flatBasisNd d n x) := by
  apply contDiff_tsum
    (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (flatBasisNd d n))
  · intro n
    exact contDiff_const.mul (flatBasisNd d n).smooth'
  · intro j _; exact rapidDecay_seminorm_summableNd d a 0 j
  · intro j n x _; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n j x
private lemma rapidDecay_pointwise_seminorm_leNd (d : ℕ) (a : RapidDecaySeq) (k l : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l
      (fun y => ∑' n, a.val n * flatBasisNd d n y) x‖ ≤
    ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
  have h_iFD : iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * flatBasisNd d n y) x =
      ∑' n, iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x := by
    apply iteratedFDeriv_tsum_apply (N := ⊤)
      (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (flatBasisNd d n))
    · intro n; exact contDiff_const.mul (flatBasisNd d n).smooth'
    · intro j _; exact rapidDecay_seminorm_summableNd d a 0 j
    · intro j n y _; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n j y
    · exact le_top
  rw [h_iFD]
  have h_norm_summ : Summable (fun n =>
      ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => scalar_flatBasisNd_iFDeriv_bound d (a.val n) n l x)
      (rapidDecay_seminorm_summableNd d a 0 l)
  have h_ptwise : ∀ n, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖ ≤
      |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
    intro n
    have hfun_eq : (fun y => a.val n * flatBasisNd d n y) =
        ⇑(a.val n • flatBasisNd d n) := by
      ext y; simp [smul_eq_mul]
    rw [hfun_eq]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • flatBasisNd d n)) x‖
        ≤ SchwartzMap.seminorm ℝ k l (a.val n • flatBasisNd d n) :=
          SchwartzMap.le_seminorm ℝ k l _ x
      _ = |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
  calc ‖x‖ ^ k * ‖∑' n, iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖
      ≤ ‖x‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
          (pow_nonneg (norm_nonneg _) k)
    _ = ∑' n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => a.val n * flatBasisNd d n y) x‖ :=
        tsum_mul_left.symm
    _ ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) :=
        (Summable.of_nonneg_of_le
          (fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _))
          h_ptwise (rapidDecay_seminorm_summableNd d a k l)).tsum_le_tsum
          h_ptwise (rapidDecay_seminorm_summableNd d a k l)
private noncomputable def rapidDecay_schwartzMapNd (d : ℕ) (a : RapidDecaySeq) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun x := ∑' n, a.val n * flatBasisNd d n x
  smooth' := rapidDecay_hermite_contDiffNd d a
  decay' k l := ⟨_, rapidDecay_pointwise_seminorm_leNd d a k l⟩
private lemma rapidDecay_schwartzMapNd_apply (d : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    rapidDecay_schwartzMapNd d a x = ∑' n, a.val n * flatBasisNd d n x := rfl
private noncomputable instance schwartzMapNd_T2Space (d : ℕ) :
    T2Space (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) := by
  haveI : T1Space (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :=
    WithSeminorms.T1_of_separating (schwartz_withSeminorms ℝ _ ℝ) fun f hf =>
      ⟨⟨0, 0⟩, fun h => hf (SchwartzMap.ext fun x =>
        norm_le_zero_iff.mp ((SchwartzMap.norm_le_seminorm ℝ f x).trans (le_of_eq h)))⟩
  exact inferInstance
set_option maxHeartbeats 1600000 in
private theorem rapidDecay_hermite_hasSumNd (d : ℕ) (a : RapidDecaySeq) :
    HasSum (fun n => a.val n • flatBasisNd d n) (rapidDecay_schwartzMapNd d a) := by
  rw [HasSum]
  show Filter.Tendsto _ Filter.atTop _
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ).tendsto_nhds _
    (rapidDecay_schwartzMapNd d a)]
  intro ⟨k, l⟩ ε hε
  have h_sem := rapidDecay_seminorm_summableNd d a k l
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp h_sem (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs => ?_⟩
  rw [show (∑ i ∈ s, a.val i • flatBasisNd d i) - rapidDecay_schwartzMapNd d a =
    -(rapidDecay_schwartzMapNd d a - ∑ i ∈ s, a.val i • flatBasisNd d i) from by abel,
    map_neg_eq_map]
  calc SchwartzMap.seminorm ℝ k l
        (rapidDecay_schwartzMapNd d a - ∑ i ∈ s, a.val i • flatBasisNd d i)
      ≤ ε / 2 := by
        apply SchwartzMap.seminorm_le_bound ℝ k l _ (half_pos hε).le
        intro x
        set r := rapidDecay_schwartzMapNd d a -
          ∑ i ∈ s, a.val i • flatBasisNd d i with hr_def
        let g : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
          fun n y => a.val n * flatBasisNd d n y
        have h_summ_iFD : Summable (fun n => iteratedFDeriv ℝ l (g n) x) := by
          apply Summable.of_norm_bounded
            (g := fun n => |a.val n| * SchwartzMap.seminorm ℝ 0 l (flatBasisNd d n))
          · exact rapidDecay_seminorm_summableNd d a 0 l
          · intro n; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n l x
        have h_iFD_limit : iteratedFDeriv ℝ l
            (fun y => ∑' n, a.val n * flatBasisNd d n y) x =
            ∑' n, iteratedFDeriv ℝ l (g n) x := by
          apply iteratedFDeriv_tsum_apply (N := ⊤)
            (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (flatBasisNd d n))
          · intro n; exact contDiff_const.mul (flatBasisNd d n).smooth'
          · intro j _; exact rapidDecay_seminorm_summableNd d a 0 j
          · intro j n y _; exact scalar_flatBasisNd_iFDeriv_bound d (a.val n) n j y
          · exact le_top
        have hsum_coe : ∀ y,
            (∑ i ∈ s, a.val i • flatBasisNd d i :
              SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) y =
            ∑ i ∈ s, g i y := by
          intro y
          have : ∀ (t : Finset ℕ),
              (∑ i ∈ t, a.val i • flatBasisNd d i :
                SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) y =
              ∑ i ∈ t, g i y := by
            intro t; induction t using Finset.cons_induction with
            | empty => simp
            | cons a' t' ha' ih =>
              simp [smul_eq_mul, g]
          exact this s
        have h_iFD_sum : iteratedFDeriv ℝ l
            (⇑(∑ i ∈ s, a.val i • flatBasisNd d i :
              SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)) x =
            ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
          have hcoe : ⇑(∑ i ∈ s, a.val i • flatBasisNd d i :
              SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) =
              fun y => ∑ i ∈ s, g i y := funext hsum_coe
          rw [hcoe]
          have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
            (fun i _ => (contDiff_const.mul (flatBasisNd d i).smooth').of_le (mod_cast le_top))
          exact congr_fun h_eq x |>.trans (Finset.sum_apply x s _)
        have h_iFD_r : iteratedFDeriv ℝ l (⇑r) x =
            ∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x := by
          have hf_cd : ContDiff ℝ l
              (fun y => ∑' n, a.val n * flatBasisNd d n y) :=
            (rapidDecay_hermite_contDiffNd d a).of_le (mod_cast le_top)
          have hg_cd : ContDiff ℝ l (fun y => ∑ i ∈ s, g i y) :=
            ContDiff.sum (fun i _ =>
              (contDiff_const.mul (flatBasisNd d i).smooth').of_le (mod_cast le_top))
          have hcoe_r : (⇑r : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) = fun y =>
              (∑' n, a.val n * flatBasisNd d n y) - ∑ i ∈ s, g i y := by
            ext y; simp only [hr_def, sub_apply,
              rapidDecay_schwartzMapNd_apply]
            exact congrArg
              ((∑' n, a.val n * flatBasisNd d n y) - ·) (hsum_coe y)
          rw [hcoe_r]
          set h_sum := fun y => ∑ i ∈ s, g i y with h_sum_def
          have h_neg_cd : ContDiff ℝ l (-h_sum) := hg_cd.neg
          have h_rw : (fun y =>
              (∑' n, a.val n * flatBasisNd d n y) - h_sum y) =
              (fun y => ∑' n, a.val n * flatBasisNd d n y) + (-h_sum) := by
            ext; simp [sub_eq_add_neg]
          rw [h_rw, iteratedFDeriv_add hf_cd h_neg_cd, Pi.add_apply,
            iteratedFDeriv_neg, Pi.neg_apply, h_iFD_limit]
          have h_iFD_h : iteratedFDeriv ℝ l h_sum x =
              ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
            rw [h_sum_def]
            have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
              (fun i _ =>
                (contDiff_const.mul (flatBasisNd d i).smooth').of_le (mod_cast le_top))
            calc iteratedFDeriv ℝ l (fun y => ∑ i ∈ s, g i y) x
                = (∑ j ∈ s, iteratedFDeriv ℝ l (g j)) x := congr_fun h_eq x
              _ = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := Finset.sum_apply x s _
          rw [h_iFD_h]
          rw [← h_summ_iFD.sum_add_tsum_compl (s := s)]
          abel
        have h_norm_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            ‖iteratedFDeriv ℝ l (g ↑i) x‖) :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun n => scalar_flatBasisNd_iFDeriv_bound d (a.val n) n l x)
            (rapidDecay_seminorm_summableNd d a 0 l)).subtype _
        have h_sem_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            |a.val ↑i| * SchwartzMap.seminorm ℝ k l (flatBasisNd d ↑i)) :=
          (rapidDecay_seminorm_summableNd d a k l).subtype _
        have h_ptwise : ∀ (i : ↥(↑s : Set ℕ)ᶜ),
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖ ≤
            |a.val ↑i| * SchwartzMap.seminorm ℝ k l (flatBasisNd d ↑i) := by
          intro ⟨n, _⟩
          have hg_eq : g n = ⇑(a.val n • flatBasisNd d n) := by
            ext y; simp [g, smul_eq_mul]
          rw [hg_eq]
          calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l
                (⇑(a.val n • flatBasisNd d n)) x‖
              ≤ SchwartzMap.seminorm ℝ k l (a.val n • flatBasisNd d n) :=
                SchwartzMap.le_seminorm ℝ k l _ x
            _ = |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) := by
                rw [map_smul_eq_mul, Real.norm_eq_abs]
        rw [h_iFD_r]
        calc ‖x‖ ^ k * ‖∑' (i : ↥(↑s : Set ℕ)ᶜ),
                iteratedFDeriv ℝ l (g ↑i) x‖
            ≤ ‖x‖ ^ k * ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                ‖iteratedFDeriv ℝ l (g ↑i) x‖ :=
              mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
                (pow_nonneg (norm_nonneg _) k)
          _ = ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖) := by
              rw [tsum_mul_left]
          _ ≤ ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (|a.val ↑i| * SchwartzMap.seminorm ℝ k l (flatBasisNd d ↑i)) :=
              (h_norm_summ.mul_left _).tsum_le_tsum h_ptwise h_sem_summ
          _ ≤ ε / 2 := by
              apply h_sem_summ.tsum_le_of_sum_le
              intro t
              set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
              have h_disj : Disjoint t' s := by
                rw [Finset.disjoint_left]
                intro n hn hn_s
                rw [Finset.mem_map] at hn
                obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
                exact hm hn_s
              have h_disj₀ : Disjoint t' s₀ := Disjoint.mono_right hs h_disj
              have h_lt := hs₀ t' h_disj₀
              rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
                mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at h_lt
              rw [ht'_def, Finset.sum_map] at h_lt
              exact le_of_lt h_lt
    _ < ε := half_lt_self hε
private theorem rapidDecay_hermite_summableNd (d : ℕ) (a : RapidDecaySeq) :
    Summable (fun n => a.val n • flatBasisNd d n) :=
  ⟨_, rapidDecay_hermite_hasSumNd d a⟩
private noncomputable def fromRapidDecayNdLM (d : ℕ) :
    RapidDecaySeq →ₗ[ℝ] SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun := rapidDecay_schwartzMapNd d
  map_add' a b := SchwartzMap.ext fun x => by
    show ∑' n, (a + b).val n * flatBasisNd d n x =
      (∑' n, a.val n * flatBasisNd d n x) + (∑' n, b.val n * flatBasisNd d n x)
    simp only [RapidDecaySeq.add_val, add_mul]
    exact (rapidDecay_pointwise_summableNd d a x).tsum_add
      (rapidDecay_pointwise_summableNd d b x)
  map_smul' r a := SchwartzMap.ext fun x => by
    show ∑' n, (r • a).val n * flatBasisNd d n x =
      r • (∑' n, a.val n * flatBasisNd d n x)
    simp only [RapidDecaySeq.smul_val, smul_eq_mul, mul_assoc]
    exact tsum_mul_left
private lemma fromRapidDecayNdLM_eq (d : ℕ) (a : RapidDecaySeq) :
    fromRapidDecayNdLM d a = ∑' n, a.val n • flatBasisNd d n :=
  (rapidDecay_hermite_hasSumNd d a).tsum_eq.symm
private lemma fromRapidDecayNdLM_seminorm_le (d : ℕ) (a : RapidDecaySeq) (k l : ℕ) :
    SchwartzMap.seminorm ℝ k l (fromRapidDecayNdLM d a) ≤
      ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) :=
  SchwartzMap.seminorm_le_bound ℝ k l _ (tsum_nonneg fun _ =>
    mul_nonneg (abs_nonneg _) (apply_nonneg _ _)) (rapidDecay_pointwise_seminorm_leNd d a k l)
private lemma fromRapidDecayNdLM_bound (d : ℕ) (k l : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∃ (s : ℕ), ∀ (a : RapidDecaySeq),
      SchwartzMap.seminorm ℝ k l (fromRapidDecayNdLM d a) ≤
        C * RapidDecaySeq.rapidDecaySeminorm s a := by
  obtain ⟨C₁, hC₁, s₁, hbasis⟩ := schwartzHermiteBasisNd_growth (d + 1) k l
  obtain ⟨C₂, hC₂, k₂, hsymm⟩ := multiIndexEquiv_symm_growth d
  refine ⟨C₁ * C₂ ^ s₁, by positivity, k₂ * s₁, fun a => ?_⟩
  calc SchwartzMap.seminorm ℝ k l (fromRapidDecayNdLM d a)
      ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (flatBasisNd d n) :=
        fromRapidDecayNdLM_seminorm_le d a k l
    _ ≤ ∑' n, |a.val n| * (C₁ * (C₂ * (1 + (n : ℝ)) ^ k₂) ^ s₁) := by
        apply (rapidDecay_seminorm_summableNd d a k l).tsum_le_tsum _
          ((a.rapid_decay (k₂ * s₁)).mul_left (C₁ * C₂ ^ s₁) |>.congr fun n => by
            rw [mul_pow]; ring)
        intro n
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc SchwartzMap.seminorm ℝ k l (flatBasisNd d n)
            ≤ C₁ * (1 + (MultiIndex.abs ((multiIndexEquiv d).symm n) : ℝ)) ^ s₁ := hbasis _
          _ ≤ C₁ * (C₂ * (1 + (n : ℝ)) ^ k₂) ^ s₁ := by
              gcongr; exact hsymm n
    _ = C₁ * C₂ ^ s₁ * ∑' n, |a.val n| * (1 + (n : ℝ)) ^ (k₂ * s₁) := by
        rw [← tsum_mul_left]; congr 1; ext n; rw [mul_pow]; ring
private lemma fromRapidDecayNdLM_isBounded (d : ℕ) :
    Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
      (fromRapidDecayNdLM d) := by
  intro ⟨k, l⟩
  obtain ⟨C, hC, s, hbound⟩ := fromRapidDecayNdLM_bound d k l
  exact ⟨{s}, ⟨C, hC.le⟩, fun a => by
    simp only [Seminorm.comp_apply, schwartzSeminormFamily, Finset.sup_singleton]
    exact hbound a⟩
noncomputable def fromRapidDecayNdCLM (d : ℕ) :
    RapidDecaySeq →L[ℝ] SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ :=
  match d with
  | 0 => 0
  | d' + 1 => {
      toLinearMap := fromRapidDecayNdLM d'
      cont := WithSeminorms.continuous_of_isBounded
        RapidDecaySeq.rapidDecay_withSeminorms
        (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d' + 1))) ℝ)
        _ (fromRapidDecayNdLM_isBounded d')
    }
private lemma hermiteCoeffNd_rapidDecay_schwartzMapNd (d' : ℕ) (a : RapidDecaySeq) (n : ℕ) :
    hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n)
      (rapidDecay_schwartzMapNd d' a) = a.val n := by
  rw [show (rapidDecay_schwartzMapNd d' a : SchwartzMap _ _) =
      ∑' m, a.val m • flatBasisNd d' m from
    (rapidDecay_hermite_hasSumNd d' a).tsum_eq.symm]
  rw [show hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n)
        (∑' m, a.val m • flatBasisNd d' m) =
      hermiteCoeffNdCLM (d' + 1) ((multiIndexEquiv d').symm n)
        (∑' m, a.val m • flatBasisNd d' m) from rfl,
    (hermiteCoeffNdCLM (d' + 1) ((multiIndexEquiv d').symm n)).map_tsum
      (rapidDecay_hermite_summableNd d' a)]
  simp only [hermiteCoeffNdCLM_apply, map_smul, smul_eq_mul,
    flatBasisNd, hermiteCoeffNd_basisNd_kronecker]
  simp_rw [(multiIndexEquiv d').symm.injective.eq_iff]
  simp_rw [show ∀ m, (if n = m then (1 : ℝ) else 0) = if m = n then 1 else 0 from
    fun m => by split_ifs <;> simp_all]
  simp [mul_ite, mul_one, mul_zero, tsum_ite_eq]
private lemma schwartz_hermite_completeness_nd (d' : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ) :
    HasSum (fun n => hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f •
      flatBasisNd d' n) f := by
  set a := toRapidDecayNdLM d' f
  set S_f := fromRapidDecayNdLM d' a
  have h_sum : HasSum (fun n => a.val n • flatBasisNd d' n) S_f :=
    rapidDecay_hermite_hasSumNd d' a
  have h_eq : S_f = f := by
    have h_sub : S_f - f = 0 := by
      apply hermiteCoeffNd_injective d'
      intro α
      rw [(hermiteCoeffNd_linear (d' + 1) α).map_sub, sub_eq_zero]
      set n := multiIndexEquiv d' α
      have h_alpha : α = (multiIndexEquiv d').symm n :=
        ((multiIndexEquiv d').symm_apply_apply α).symm
      rw [h_alpha]
      have h_Sf := hermiteCoeffNd_rapidDecay_schwartzMapNd d' a n
      have h_a : a.val n = hermiteCoeffNd (d' + 1) ((multiIndexEquiv d').symm n) f := rfl
      rw [h_a] at h_Sf
      exact h_Sf
    exact sub_eq_zero.mp h_sub
  rwa [h_eq] at h_sum
noncomputable def schwartzRapidDecayEquivNd (d' : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d' + 1))) ℝ ≃L[ℝ] RapidDecaySeq :=
  ContinuousLinearEquiv.equivOfInverse
    (toRapidDecayNdCLM (d' + 1))
    (fromRapidDecayNdCLM (d' + 1))
    (fun f => by
      have h_f := schwartz_hermite_completeness_nd d' f
      have h_recon := rapidDecay_hermite_hasSumNd d' (toRapidDecayNdLM d' f)
      exact h_recon.unique h_f)
    (fun a => by
      apply RapidDecaySeq.ext; intro n
      exact hermiteCoeffNd_rapidDecay_schwartzMapNd d' a n)
theorem schwartzRapidDecayEquivNd_symm_apply (d' : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d' + 1))) :
    ((schwartzRapidDecayEquivNd d').symm a) x =
      ∑' n, a.val n * hermiteFunctionNd (d' + 1) ((multiIndexEquiv d').symm n) x := by
  simp only [schwartzRapidDecayEquivNd]
  show fromRapidDecayNdCLM (d' + 1) a x = _
  show rapidDecay_schwartzMapNd d' a x = _
  show ∑' n, a.val n * flatBasisNd d' n x = _
  rfl
theorem schwartzRapidDecayEquivNd_summable (d' : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d' + 1))) :
    Summable (fun n => a.val n * hermiteFunctionNd (d' + 1) ((multiIndexEquiv d').symm n) x) :=
  rapidDecay_pointwise_summableNd d' a x
theorem schwartzRapidDecayEquivNd_norm_summable (d' : ℕ) (a : RapidDecaySeq)
    (x : EuclideanSpace ℝ (Fin (d' + 1))) :
    Summable (fun n => ‖a.val n * hermiteFunctionNd (d' + 1) ((multiIndexEquiv d').symm n) x‖) :=
  (schwartzRapidDecayEquivNd_summable d' a x).norm
theorem schwartzRapidDecayEquiv1D_summable (a : RapidDecaySeq) (t : ℝ) :
    Summable (fun n => a.val n * hermiteFunction n t) := by
  apply Summable.of_norm_bounded
    (g := fun n => |a.val n| * SchwartzMap.seminorm ℝ 0 0 (schwartzHermiteBasis1D n))
  · exact rapidDecay_seminorm_summable a 0 0
  · intro n
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (by rw [← Real.norm_eq_abs, ← schwartzHermiteBasis1D_apply]
          exact SchwartzMap.norm_le_seminorm ℝ _ t)
      (abs_nonneg _)
theorem schwartzRapidDecayEquiv1D_norm_summable (a : RapidDecaySeq) (t : ℝ) :
    Summable (fun n => ‖a.val n * hermiteFunction n t‖) :=
  (schwartzRapidDecayEquiv1D_summable a t).norm
theorem hermiteFunctionNd_unpair (d : ℕ) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + 2))) :
    hermiteFunctionNd (d + 2) ((multiIndexEquiv (d + 1)).symm n) x =
      hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm (Nat.unpair n).1)
        (euclideanInit (d + 1) x) *
      hermiteFunction (Nat.unpair n).2 (x (Fin.last (d + 1))) := by
  set α := (multiIndexEquiv (d + 1)).symm n
  conv_lhs => rw [← euclideanSnoc_init_last (d + 1) x]
  rw [hermiteFunctionNd_snoc d α (euclideanInit (d + 1) x) (x (Fin.last (d + 1)))]
  have h_alpha := multiIndexEquiv_succ_symm d n
  congr 1
  ·
    simp only [hermiteFunctionNd]
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    show ((multiIndexEquiv (d + 1)).symm n) (Fin.castSucc j) =
        ((multiIndexEquiv d).symm (Nat.unpair n).1) j
    conv_lhs => rw [h_alpha]
    simp only [Fin.succFunEquiv, Equiv.symm_trans_apply, Equiv.prodCongrRight_symm,
      Equiv.prodCongrRight_apply]
    rw [show Fin.castSucc j = Fin.castAdd 1 j from rfl]
    simp [Fin.append_left]
  ·
    congr 1
    show ((multiIndexEquiv (d + 1)).symm n) (Fin.last (d + 1)) = (Nat.unpair n).2
    conv_lhs => rw [h_alpha]
    set f := (Fin.succFunEquiv ℕ (d + 1)).symm
      ((multiIndexEquiv d).symm (Nat.unpair n).1, (Nat.unpair n).2)
    have hf : (Fin.succFunEquiv ℕ (d + 1) f).2 = (Nat.unpair n).2 :=
      congr_arg Prod.snd (Equiv.apply_symm_apply _ _)
    simp only [Fin.succFunEquiv, Equiv.trans_apply] at hf
    exact hf
noncomputable def schwartzRapidDecayEquivFin (d : ℕ) (hd : 0 < d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L[ℝ] RapidDecaySeq :=
  match d, hd with
  | 1, _ => (schwartzDomCongr euclideanFin1Equiv).symm.trans schwartzRapidDecayEquiv1D
  | d' + 2, _ => schwartzRapidDecayEquivNd (d' + 1)
noncomputable def schwartzRapidDecayEquiv (D : Type*)
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Nontrivial D] :
    SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq :=
  have hd : 0 < Module.finrank ℝ D := Module.finrank_pos
  (schwartzDomCongr (toEuclidean (E := D))).symm.trans
    (schwartzRapidDecayEquivFin (Module.finrank ℝ D) hd)
end GaussianField
end
end

-- SchwartzNuclear.HermiteNuclear
section
noncomputable section
open GaussianField TopologicalSpace
namespace GaussianField
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
noncomputable instance schwartz_dyninMityaginSpace [Nontrivial D] :
    DyninMityaginSpace (SchwartzMap D ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ D ℝ)
    (schwartzRapidDecayEquiv D)
noncomputable instance schwartz_dyninMityaginSpace_1D :
    DyninMityaginSpace (SchwartzMap ℝ ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ ℝ ℝ)
    schwartzRapidDecayEquiv1D
noncomputable instance schwartz_hasBiorthogonalBasis_1D :
    DyninMityaginSpace.HasBiorthogonalBasis (SchwartzMap ℝ ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv_hasBiorthogonalBasis
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ ℝ ℝ)
    schwartzRapidDecayEquiv1D
noncomputable instance schwartz_dyninMityaginSpace_euclidean (d : ℕ) :
    DyninMityaginSpace (SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (schwartzRapidDecayEquivNd d)
instance rapidDecaySeq_separableSpace : SeparableSpace RapidDecaySeq := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have h_dense : (Submodule.span ℝ (Set.range RapidDecaySeq.basisVec)).topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro a _
    exact mem_closure_of_tendsto (RapidDecaySeq.hasSum_basisVec a).tendsto_sum_nat
      (Filter.Eventually.of_forall fun s =>
        Submodule.sum_mem _ fun m _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
  have h1 := (Set.countable_range RapidDecaySeq.basisVec).isSeparable.span (R := ℝ)
  have h2 := h1.closure
  have h3 : closure (↑(Submodule.span ℝ (Set.range RapidDecaySeq.basisVec)) :
      Set RapidDecaySeq) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, h_dense]; rfl
  rwa [h3] at h2
instance schwartz_separableSpace [Nontrivial D] :
    SeparableSpace (SchwartzMap D ℝ) := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have h_range : Set.range (schwartzRapidDecayEquiv D).symm = Set.univ :=
    Function.Surjective.range_eq (schwartzRapidDecayEquiv D).symm.surjective
  rw [← h_range]
  exact isSeparable_range (schwartzRapidDecayEquiv D).symm.continuous
end GaussianField
end
end

-- GaussianLaw
section
noncomputable section

open MeasureTheory

namespace StrongGaussianLaw

variable {E K : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The random Hilbert vector defines a Borel random variable in the strong dual,
by continuous precomposition with the Hilbert factor. -/
theorem measurable_series (j : E →L[ℝ] K) (v : ℕ → K) :
    @Measurable (ℕ → ℝ) (StrongDual ℝ E) _ (borel _)
      (fun ξ => (innerSL ℝ (∑' n, ξ n • v n)).comp j) := by
  borelize K
  borelize (StrongDual ℝ E)
  have hs : StronglyMeasurable (fun ξ : ℕ → ℝ => ∑' n, ξ n • v n) :=
    StronglyMeasurable.tsum fun n =>
      (measurable_pi_apply n).stronglyMeasurable.smul stronglyMeasurable_const
  exact ((ContinuousLinearMap.precomp ℝ j).continuous.comp
    (innerSL ℝ (E := K)).continuous).measurable.comp hs.measurable

omit [CompleteSpace K] in
theorem eval_series {j : E →L[ℝ] K} {v : ℕ → K} {ξ : ℕ → ℝ}
    (hs : Summable (fun n => ξ n • v n)) (f : E) :
    (innerSL ℝ (∑' n, ξ n • v n)).comp j f =
      ∑' n, ξ n * inner ℝ (v n) (j f) := by
  change inner ℝ (∑' n, ξ n • v n) (j f) = _
  rw [real_inner_comm]
  change innerSL ℝ (j f) (∑' n, ξ n • v n) = _
  rw [(innerSL ℝ (j f)).map_tsum hs]
  exact tsum_congr fun n => by simp [innerSL_apply_apply, real_inner_comm (j f) (v n)]

end StrongGaussianLaw
end
end

-- GaussianField.NuclearFactorization
section
open scoped BigOperators
open Finset
noncomputable section
namespace GaussianField
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
lemma summable_one_add_rpow_neg_two :
    Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-2) : ℝ)) := by
  have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-2) : ℝ)) 1).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : ((-2) : ℝ) < -1))
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact h.congr fun m => by rw [add_comm]
omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E] in
private lemma finset_sup_seminorm_poly_bound
    {ι' : Type*} (p' : ι' → Seminorm ℝ E)
    (s : Finset ι')
    (x : ℕ → E)
    (hx : ∀ i : ι', ∃ C > 0, ∃ (t : ℕ),
      ∀ m : ℕ, p' i (x m) ≤ C * (1 + (m : ℝ)) ^ t) :
    ∃ (C₁ : ℝ) (p₁ : ℕ), 0 < C₁ ∧
      ∀ m : ℕ, (s.sup p') (x m) ≤ C₁ * (1 + (m : ℝ)) ^ p₁ := by
  induction s using Finset.cons_induction with
  | empty =>
    refine ⟨1, 0, one_pos, fun m => ?_⟩
    simp only [Finset.sup_empty, Seminorm.bot_eq_zero, zero_apply]
    positivity
  | cons a s' ha ih =>
    obtain ⟨C_prev, p_prev, hC_prev, h_prev⟩ := ih
    obtain ⟨C_a, hC_a, t_a, h_a⟩ := hx a
    refine ⟨C_prev + C_a, max p_prev t_a, add_pos hC_prev hC_a, fun m => ?_⟩
    rw [Finset.sup_cons]
    have hone_le : (1 : ℝ) ≤ 1 + (m : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg' m)
    calc (p' a ⊔ s'.sup p') (x m)
        = p' a (x m) ⊔ (s'.sup p') (x m) :=
          Seminorm.sup_apply _ _ _
      _ ≤ p' a (x m) + (s'.sup p') (x m) := by
          exact max_le (le_add_of_nonneg_right
            (apply_nonneg _ _)) (le_add_of_nonneg_left
            (apply_nonneg _ _))
      _ ≤ C_a * (1 + ↑m) ^ t_a + C_prev * (1 + ↑m) ^ p_prev :=
          add_le_add (h_a m) (h_prev m)
      _ ≤ C_a * (1 + ↑m) ^ max p_prev t_a +
          C_prev * (1 + ↑m) ^ max p_prev t_a := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hone_le (le_max_right _ _))
              (le_of_lt hC_a)
          · exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hone_le (le_max_left _ _))
              (le_of_lt hC_prev)
      _ = (C_prev + C_a) * (1 + ↑m) ^ max p_prev t_a := by ring
theorem clm_image_growth
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : E →L[ℝ] H) :
    ∃ (C : ℝ) (p₁ : ℕ), 0 < C ∧
      ∀ m : ℕ, ‖T (DyninMityaginSpace.basis m)‖ ≤ C * (1 + (m : ℝ)) ^ p₁ := by
  have hcont : Continuous ((normSeminorm ℝ H).comp T.toLinearMap) := by
    exact T.continuous.norm
  obtain ⟨s, C₀, hC₀_ne, hle⟩ :=
    Seminorm.bound_of_continuous DyninMityaginSpace.h_with _ hcont
  have hfinset_bound : ∃ (C₁ : ℝ) (p₁ : ℕ), 0 < C₁ ∧
      ∀ m : ℕ, (s.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis m) ≤
        C₁ * (1 + (m : ℝ)) ^ p₁ :=
    finset_sup_seminorm_poly_bound DyninMityaginSpace.p s DyninMityaginSpace.basis
      DyninMityaginSpace.basis_growth
  obtain ⟨C₁, p₁, hC₁_pos, hfinset⟩ := hfinset_bound
  have hC₀_pos : (0 : ℝ) < C₀ := by positivity
  exact ⟨C₀ * C₁, p₁, mul_pos hC₀_pos hC₁_pos, fun m =>
    calc ‖T (DyninMityaginSpace.basis m)‖
        ≤ C₀ * (s.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis m) := by
          have := hle (DyninMityaginSpace.basis m)
          simp only [Seminorm.comp_apply, coe_normSeminorm, smul_apply,
                     NNReal.smul_def, smul_eq_mul] at this
          exact this
      _ ≤ C₀ * (C₁ * (1 + (m : ℝ)) ^ p₁) :=
          mul_le_mul_of_nonneg_left (hfinset m) (le_of_lt hC₀_pos)
      _ = C₀ * C₁ * (1 + (m : ℝ)) ^ p₁ := by ring⟩
theorem nuclear_clm_representation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : E →L[ℝ] H) :
    ∃ (φ : ℕ → (E →L[ℝ] ℝ)) (y : ℕ → H),
      Summable (fun m => ‖y m‖) ∧
      (∃ (s : Finset (DyninMityaginSpace.ι (E := E))) (B : ℝ), 0 < B ∧
        ∀ (m : ℕ) (f : E), |φ m f| ≤ B * (s.sup DyninMityaginSpace.p) f) ∧
      (∀ (f : E) (w : H),
        @inner ℝ H _ w (T f) = ∑' m, φ m f * @inner ℝ H _ w (y m)) := by
  set ψ := DyninMityaginSpace.basis (E := E) with hψ_def
  set c := DyninMityaginSpace.coeff (E := E) with hc_def
  obtain ⟨C_g, p₁, hCg_pos, hgrowth⟩ := clm_image_growth T
  set s_exp : ℕ := p₁ + 2
  set s_real : ℝ := ↑s_exp with hs_def
  set y : ℕ → H := fun m => ((1 + (m : ℝ)) ^ (-s_real)) • T (ψ m) with hy_def
  set φ : ℕ → (E →L[ℝ] ℝ) :=
    fun m => (1 + (m : ℝ)) ^ s_real • c m with hφ_def
  refine ⟨φ, y, ?_, ?_, ?_⟩
  ·
    simp only [hy_def]
    refine Summable.of_norm_bounded (summable_one_add_rpow_neg_two.mul_left C_g) (fun m => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ↑m) _)]
    have hpos : (0 : ℝ) < 1 + ↑m := by positivity
    calc (1 + (↑m : ℝ)) ^ (-s_real) * ‖T (ψ m)‖
        ≤ (1 + (↑m : ℝ)) ^ (-s_real) * (C_g * (1 + (↑m : ℝ)) ^ p₁) :=
          mul_le_mul_of_nonneg_left (hgrowth m) (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ p₁) := by ring
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ ((p₁ : ℝ))) := by
          congr 2; exact (Real.rpow_natCast _ _).symm
      _ = C_g * (1 + (↑m : ℝ)) ^ ((-2) : ℝ) := by
          congr 1; rw [← Real.rpow_add hpos]; congr 1
          rw [hs_def, show s_exp = p₁ + 2 from rfl]; push_cast; ring
  ·
    obtain ⟨C_s, hCs_pos, s, hdecay_s⟩ := DyninMityaginSpace.coeff_decay (E := E) s_exp
    exact ⟨s, C_s, hCs_pos, fun m f => by
      simp only [hφ_def, smul_apply, smul_eq_mul]
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + ↑m) s_real)]
      rw [hs_def, Real.rpow_natCast, mul_comm]
      exact hdecay_s f m⟩
  ·
    intro f w
    rw [DyninMityaginSpace.expansion_H T w f]
    congr 1
    ext m
    simp only [hφ_def, hy_def, smul_apply, smul_eq_mul,
               inner_smul_right]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    rw [Real.rpow_neg (le_of_lt hpos)]
    have hne : (1 + (↑m : ℝ)) ^ s_real ≠ 0 := (Real.rpow_pos_of_pos hpos s_real).ne'
    field_simp; rfl
end GaussianField
end
end

-- GaussianField.SpectralTheorem
section
noncomputable section
namespace GaussianField
open scoped InnerProductSpace
open LinearMap Submodule Filter Metric
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 800000 in
private theorem hasEigenvector_aux
    [Nontrivial E]
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ (μ : ℝ) (x : E), x ≠ 0 ∧ (T : E →ₗ[ℝ] E) x = μ • x ∧ |μ| = ‖T‖ := by
  have hα_pos : (0 : ℝ) < ‖T‖ := norm_pos_iff.mpr hne
  have hα_ne : (‖T‖ : ℝ) ≠ 0 := ne_of_gt hα_pos
  have hα2_pos : (0 : ℝ) < ‖T‖ ^ 2 := by positivity
  have hα2_ne : (‖T‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt hα2_pos
  set α := ‖T‖ with hα_def
  have hT_sym : (T : E →ₗ[ℝ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  have hseq : ∀ n : ℕ, ∃ x : E, ‖x‖ < 1 ∧ α - 1 / ((n : ℝ) + 1) < ‖T x‖ := by
    intro n
    exact T.exists_lt_apply_of_lt_opNorm (by linarith [show (0:ℝ) < 1/((n:ℝ)+1) from by positivity])
  choose x hx_norm hx_lb using hseq
  have hcpt : IsCompact (closure (T '' closedBall (0 : E) 1)) :=
    hK.isCompact_closure_image_closedBall 1
  have hTx_mem : ∀ n, T (x n) ∈ closure (T '' closedBall (0 : E) 1) := by
    intro n
    apply subset_closure
    exact Set.mem_image_of_mem T (mem_closedBall_zero_iff.mpr (hx_norm n).le)
  obtain ⟨y, _, φ, hφ, hTxφ⟩ := hcpt.isSeqCompact hTx_mem
  have hy_norm : ‖y‖ = α := by
    have hTxφ_norm := (continuous_norm.tendsto y).comp hTxφ
    have hle : ‖y‖ ≤ α := by
      apply le_of_tendsto hTxφ_norm
      apply Filter.Eventually.of_forall; intro n
      calc ‖T (x (φ n))‖ ≤ α * ‖x (φ n)‖ := T.le_opNorm _
        _ ≤ α * 1 := by gcongr; exact (hx_norm _).le
        _ = α := mul_one _
    have hge : α ≤ ‖y‖ := by
      have hf_lb : ∀ n : ℕ, α - 1 / ((n : ℝ) + 1) ≤ ‖T (x (φ n))‖ := by
        intro n
        have h1 := hx_lb (φ n)
        have hφn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
        have : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        linarith
      have h_lb_tendsto : Tendsto (fun n : ℕ => α - 1 / ((n : ℝ) + 1)) atTop (nhds α) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
          have := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
          exact this
        have := tendsto_const_nhds (x := α).sub h1
        simp only [sub_zero] at this; exact this
      have hTxφ_norm' : Tendsto (fun n => ‖T (x (φ n))‖) atTop (nhds ‖y‖) := by
        exact (continuous_norm.tendsto y).comp hTxφ
      exact le_of_tendsto_of_tendsto h_lb_tendsto hTxφ_norm'
        (Filter.Eventually.of_forall hf_lb)
    linarith
  have hTTxφ : Tendsto (fun n => T (T (x (φ n)))) atTop (nhds (T y)) :=
    (T.continuous.tendsto y).comp hTxφ
  have hTx_norm : Tendsto (fun n => ‖T (x (φ n))‖) atTop (nhds α) := by
    rw [← hy_norm]
    exact (continuous_norm.tendsto y).comp hTxφ
  have hkey : Tendsto (fun n => ‖T (T (x (φ n))) - α ^ 2 • x (φ n)‖) atTop (nhds 0) := by
    suffices hsq : Tendsto (fun n => ‖T (T (x (φ n))) - α ^ 2 • x (φ n)‖ ^ 2) atTop (nhds 0) by
      have := hsq.sqrt
      simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at this
      exact this
    have hpointwise : ∀ n, ‖T (T (x (φ n))) - α ^ 2 • x (φ n)‖ ^ 2 ≤
        α ^ 2 * (α ^ 2 - ‖T (x (φ n))‖ ^ 2) := by
      intro n
      set z := x (φ n)
      have hz_norm : ‖z‖ ≤ 1 := (hx_norm (φ n)).le
      have hTTz_norm : ‖T (T z)‖ ≤ α * ‖T z‖ := T.le_opNorm (T z)
      have hinner : ⟪T (T z), z⟫_ℝ = ‖T z‖ ^ 2 := by
        have h1 : @inner ℝ E _ ((T : E →ₗ[ℝ] E) (T z)) z =
            @inner ℝ E _ (T z) ((T : E →ₗ[ℝ] E) z) := hT_sym (T z) z
        simp only [ContinuousLinearMap.coe_coe] at h1
        rw [h1, real_inner_self_eq_norm_sq]
      have hexpand : ‖T (T z) - α ^ 2 • z‖ ^ 2 =
          ‖T (T z)‖ ^ 2 - 2 * (α ^ 2 * ⟪T (T z), z⟫_ℝ) + (α ^ 2) ^ 2 * ‖z‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right, norm_smul,
            Real.norm_of_nonneg (sq_nonneg α)]
        ring
      rw [hexpand, hinner]
      have h1 : ‖T (T z)‖ ^ 2 ≤ α ^ 2 * ‖T z‖ ^ 2 := by
        calc ‖T (T z)‖ ^ 2 ≤ (α * ‖T z‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hTTz_norm 2
          _ = α ^ 2 * ‖T z‖ ^ 2 := mul_pow α ‖T z‖ 2
      have h2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - ‖z‖), norm_nonneg z]
      nlinarith
    have h_ub_tendsto : Tendsto (fun n => α ^ 2 * (α ^ 2 - ‖T (x (φ n))‖ ^ 2))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n => α ^ 2 - ‖T (x (φ n))‖ ^ 2) atTop (nhds 0) := by
        have := tendsto_const_nhds (x := α ^ 2).sub (hTx_norm.pow 2)
        simp only [sub_self] at this; exact this
      have := h1.const_mul (α ^ 2)
      simp only [mul_zero] at this; exact this
    exact squeeze_zero (fun n => sq_nonneg _) hpointwise h_ub_tendsto
  have hx_conv : Tendsto (fun n => x (φ n)) atTop (nhds ((α ^ 2)⁻¹ • T y)) := by
    have hα2_smul : Tendsto (fun n => α ^ 2 • x (φ n)) atTop (nhds (T y)) := by
      have h_diff : Tendsto (fun n => T (T (x (φ n))) - α ^ 2 • x (φ n)) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        exact hkey
      have : Tendsto (fun n => T (T (x (φ n))) - (T (T (x (φ n))) - α ^ 2 • x (φ n)))
          atTop (nhds (T y - 0)) :=
        hTTxφ.sub h_diff
      simp only [sub_sub_cancel, sub_zero] at this
      exact this
    have hTy_eq : T y = α ^ 2 • ((α ^ 2)⁻¹ • T y) := by
      rw [smul_smul, mul_inv_cancel₀ hα2_ne, one_smul]
    rw [hTy_eq] at hα2_smul
    rwa [tendsto_const_smul_iff₀ hα2_ne] at hα2_smul
  set x₀ := (α ^ 2)⁻¹ • T y with hx₀_def
  have hT2x0 : T (T x₀) = α ^ 2 • x₀ := by
    have h_TTx0 : T (T x₀) = T y := by
      have h1 : Tendsto (fun n => T (T (x (φ n)))) atTop (nhds (T (T x₀))) :=
        (T.continuous.tendsto (T x₀)).comp ((T.continuous.tendsto x₀).comp hx_conv)
      exact tendsto_nhds_unique h1 hTTxφ
    have h_α2x0 : α ^ 2 • x₀ = T y := by
      simp [hx₀_def, smul_smul, mul_inv_cancel₀ hα2_ne]
    rw [h_TTx0, ← h_α2x0]
  have hx0_norm : ‖x₀‖ = 1 := by
    have hx_norm_conv : Tendsto (fun n => ‖x (φ n)‖) atTop (nhds ‖x₀‖) :=
      (continuous_norm.tendsto x₀).comp hx_conv
    have hge : 1 ≤ ‖x₀‖ := by
      by_contra h
      push Not at h
      have hlt : α * ‖x₀‖ < α := by nlinarith
      have h_ub : Tendsto (fun n => α * ‖x (φ n)‖) atTop (nhds (α * ‖x₀‖)) :=
        hx_norm_conv.const_mul α
      have h_lb_le : ∀ n, ‖T (x (φ n))‖ ≤ α * ‖x (φ n)‖ := fun n => T.le_opNorm _
      have := le_of_tendsto_of_tendsto hTx_norm h_ub (Filter.Eventually.of_forall h_lb_le)
      linarith
    have hle : ‖x₀‖ ≤ 1 := by
      apply le_of_tendsto hx_norm_conv
      apply Filter.Eventually.of_forall
      intro n; exact (hx_norm _).le
    linarith
  have hx0_ne : x₀ ≠ 0 := by
    intro h; simp [h] at hx0_norm
  set ep := T x₀ + α • x₀ with hep_def
  set em := T x₀ - α • x₀ with hem_def
  have hTep : T ep = α • ep := by
    simp only [hep_def, map_add, map_smul]
    rw [hT2x0]; module
  have hTem : T em = (-α) • em := by
    simp only [hem_def, map_sub, map_smul]
    rw [hT2x0]; module
  have hne_ep_em : ep ≠ 0 ∨ em ≠ 0 := by
    by_contra h
    push Not at h
    have : ep - em = ((2 : ℝ) * α) • x₀ := by simp [hep_def, hem_def]; module
    rw [h.1, h.2, sub_zero] at this
    have := smul_eq_zero.mp this.symm
    rcases this with h2 | h2
    · linarith [show (0:ℝ) < 2 * α from by positivity]
    · exact hx0_ne h2
  have hα_abs : |α| = ‖T‖ := abs_of_nonneg (le_of_lt hα_pos)
  rcases hne_ep_em with hep_ne | hem_ne
  · exact ⟨α, ep, hep_ne, by exact_mod_cast hTep, hα_abs⟩
  · exact ⟨-α, em, hem_ne, by exact_mod_cast hTem,
      by rw [abs_neg]; exact hα_abs⟩
theorem compact_selfAdjoint_hasEigenvector
    [Nontrivial E]
    {T : E →L[ℝ] E} (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T)
    (hT_ne : T ≠ 0) :
    ∃ μ : ℝ, Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) μ ∧ |μ| = ‖T‖ := by
  obtain ⟨μ, x, hx_ne, hx_eig, hμ_abs⟩ := hasEigenvector_aux T hT_sa hT_compact hT_ne
  refine ⟨μ, ?_, hμ_abs⟩
  rw [Module.End.HasEigenvalue]
  intro h_bot
  rw [Submodule.eq_bot_iff] at h_bot
  exact hx_ne (h_bot x (Module.End.mem_eigenspace_iff.mpr hx_eig))
theorem compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot
    {T : E →L[ℝ] E} (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)ᗮ = ⊥ := by
  have hT_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT_sa
  set W := (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)ᗮ with hW_def
  have hW_inv : ∀ w ∈ W, (T : E →ₗ[ℝ] E) w ∈ W :=
    fun w hw => hT_sym.orthogonalComplement_iSup_eigenspaces_invariant hw
  set T_W := (T.comp W.subtypeL).codRestrict W (fun ⟨u, hu⟩ => hW_inv u hu) with hT_W_def
  have instCS_W : CompleteSpace ↥W :=
    Submodule.instOrthogonalCompleteSpace (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)
  have hT_W_sym : (T_W : ↥W →ₗ[ℝ] ↥W).IsSymmetric := by
    intro ⟨x, _⟩ ⟨y, _⟩
    simp only [Submodule.coe_inner]
    change @inner ℝ E _ (T x) y = @inner ℝ E _ x (T y)
    exact hT_sym x y
  have hT_W_sa : @IsSelfAdjoint (↥W →L[ℝ] ↥W)
      (@ContinuousLinearMap.instStarId ℝ ↥W _ _ _ instCS_W) T_W :=
    (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric ℝ ↥W _ _ _ instCS_W).mpr hT_W_sym
  have hT_W_compact : IsCompactOperator T_W :=
    (hT_compact.comp_clm W.subtypeL).codRestrict _ (Submodule.isClosed_orthogonal _)
  have hT_W_zero : T_W = 0 := by
    by_contra hT_W_ne
    obtain ⟨v, hv_ne⟩ : ∃ v : ↥W, T_W v ≠ 0 := by
      by_contra h
      push Not at h
      exact hT_W_ne (ContinuousLinearMap.ext (fun v => h v))
    haveI : Nontrivial W := by
      refine ⟨⟨v, 0, ?_⟩⟩
      intro heq
      exact hv_ne (by rw [heq]; simp)
    obtain ⟨μ, e_W, he_ne, he_eig, _⟩ :=
      @hasEigenvector_aux ↥W _ _ instCS_W _ T_W hT_W_sa hT_W_compact hT_W_ne
    have hT_W_eq : (T_W : ↥W →ₗ[ℝ] ↥W) = (T : E →ₗ[ℝ] E).restrict hW_inv := by
      ext ⟨x, hx⟩
      simp only [ContinuousLinearMap.coe_coe, LinearMap.restrict_apply]
      rfl
    have h_no_eig : Module.End.eigenspace ((T : E →ₗ[ℝ] E).restrict hW_inv) μ = ⊥ := by
      have : hW_inv = hT_sym.orthogonalComplement_iSup_eigenspaces_invariant := by
        ext x hx; rfl
      rw [this]
      exact hT_sym.orthogonalComplement_iSup_eigenspaces μ
    have he_mem : e_W ∈ Module.End.eigenspace ((T : E →ₗ[ℝ] E).restrict hW_inv) μ := by
      rw [Module.End.mem_eigenspace_iff]
      rw [← hT_W_eq]
      exact he_eig
    rw [h_no_eig] at he_mem
    exact he_ne ((Submodule.mem_bot ℝ).mp he_mem)
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hTw : (T : E →ₗ[ℝ] E) w = 0 := by
    have : T_W ⟨w, hw⟩ = 0 := by rw [hT_W_zero]; simp
    have h := congr_arg Subtype.val this
    simp only [ZeroMemClass.coe_zero] at h
    exact h
  have hw_eig : w ∈ Module.End.eigenspace (T : E →ₗ[ℝ] E) 0 := by
    rw [Module.End.mem_eigenspace_iff]
    simp [hTw]
  have hw_sup : w ∈ ⨆ μ, Module.End.eigenspace (T : E →ₗ[ℝ] E) μ :=
    le_iSup (fun μ => Module.End.eigenspace (T : E →ₗ[ℝ] E) μ) 0 hw_eig
  have hw_inner : @inner ℝ E _ w w = 0 :=
    Submodule.inner_right_of_mem_orthogonal hw_sup hw
  rwa [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at hw_inner
private theorem eigenvector_basis
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eigenval : ι → ℝ),
      ∀ i, (T : E →ₗ[ℝ] E) (b i) = eigenval i • b i := by
  have hspan := compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot
    (T := T) hT hK
  have hT_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  let eigset : Set E := ⋃ (μ : ℝ), ↑(Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)
  have hZ : ∃ S ⊆ eigset, Orthonormal ℝ ((↑) : S → E) ∧
      ∀ u, S ⊆ u → u ⊆ eigset → Orthonormal ℝ ((↑) : u → E) → u = S := by
    have := zorn_subset_nonempty
      {b : Set E | b ⊆ eigset ∧ Orthonormal ℝ ((↑) : b → E)}
      (fun c hc cc _c0 => ⟨⋃₀ c,
        ⟨fun x ⟨s, hs, hx⟩ => (hc hs).1 hx,
         orthonormal_sUnion_of_directed cc.directedOn (fun s hs => (hc hs).2)⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩)
      ∅ ⟨Set.empty_subset _, orthonormal_empty ℝ E⟩
    obtain ⟨S, _, hSmax⟩ := this
    have hSe := hSmax.1.1
    have hSo := hSmax.1.2
    exact ⟨S, hSe, hSo, fun u hSu hue huo =>
      (hSmax.2 ⟨hue, huo⟩ hSu).antisymm hSu⟩
  obtain ⟨S, hSe, hSo, hSmax⟩ := hZ
  have hT_span_inv : Submodule.span ℝ S ≤ (Submodule.span ℝ S).comap (T : E →ₗ[ℝ] E) := by
    rw [Submodule.span_le]
    intro s hs
    show (T : E →ₗ[ℝ] E) s ∈ Submodule.span ℝ S
    have hse := hSe hs; rw [Set.mem_iUnion] at hse
    obtain ⟨μ, hμ⟩ := hse
    rw [Module.End.mem_eigenspace_iff.mp hμ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hs)
  have hT_orth_inv : ∀ w ∈ (Submodule.span ℝ S)ᗮ,
      (T : E →ₗ[ℝ] E) w ∈ (Submodule.span ℝ S)ᗮ := by
    intro w hw
    rw [Submodule.mem_orthogonal'] at hw ⊢
    intro u hu
    rw [real_inner_comm]
    rw [← hT_sym u w, real_inner_comm]
    exact hw _ (hT_span_inv hu)
  have h_span_bot : (Submodule.span ℝ S)ᗮ = ⊥ := by
    by_contra h_ne
    obtain ⟨w, hw, hw_ne⟩ := (Submodule.ne_bot_iff _).mp h_ne
    set W := (Submodule.span ℝ S)ᗮ with hW_def
    have extend_S : ∀ e ∈ W, e ∈ eigset → ‖e‖ = 1 → False := by
      intro e he_W he_eig he_norm
      have he_orth : ∀ s ∈ Submodule.span ℝ S, @inner ℝ E _ e s = 0 := by
        rwa [Submodule.mem_orthogonal'] at he_W
      have he_notin : e ∉ S := by
        intro hmem
        have h_inner := he_orth e (Submodule.subset_span hmem)
        rw [real_inner_self_eq_norm_sq, he_norm, one_pow] at h_inner
        exact one_ne_zero h_inner
      have hSue_orth : Orthonormal ℝ ((↑) : ↥(S ∪ {e}) → E) := by
        refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x, hx⟩ ⟨y, hy⟩ hne => ?_⟩
        · rcases hx with hx | hx
          · exact hSo.1 ⟨x, hx⟩
          · have := Set.mem_singleton_iff.mp hx; subst this; exact he_norm
        · have hne_val : x ≠ y := fun h => hne (Subtype.ext h)
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · show @inner ℝ E _ x y = 0
            exact hSo.2 (show (⟨x, hx⟩ : ↥S) ≠ ⟨y, hy⟩ from
              fun h => hne_val (congr_arg Subtype.val h))
          · show @inner ℝ E _ x y = 0
            have hye : y = e := Set.mem_singleton_iff.mp hy; subst hye
            rw [real_inner_comm]; exact he_orth x (Submodule.subset_span hx)
          · show @inner ℝ E _ x y = 0
            have hxe : x = e := Set.mem_singleton_iff.mp hx; subst hxe
            exact he_orth y (Submodule.subset_span hy)
          · exfalso; apply hne_val
            rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
      have hSue_sub : S ∪ {e} ⊆ eigset := by
        intro x hx; rcases hx with hx | hx
        · exact hSe hx
        · rw [Set.mem_singleton_iff.mp hx]; exact he_eig
      have hSue_eq := hSmax (S ∪ {e}) Set.subset_union_left hSue_sub hSue_orth
      exact he_notin (hSue_eq ▸ Set.mem_union_right S rfl)
    by_cases hTw_all : ∀ v ∈ W, (T : E →ₗ[ℝ] E) v = 0
    · have hw_norm_ne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw_ne
      exact extend_S ((‖w‖⁻¹ : ℝ) • w) (W.smul_mem _ hw)
        (Set.mem_iUnion.mpr ⟨0, Module.End.mem_eigenspace_iff.mpr (by
          show (T : E →ₗ[ℝ] E) ((‖w‖⁻¹ : ℝ) • w) = 0 • ((‖w‖⁻¹ : ℝ) • w)
          rw [zero_smul, map_smul, hTw_all w hw, smul_zero])⟩)
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw_norm_ne])
    · push Not at hTw_all; obtain ⟨v, hv, hTv_ne⟩ := hTw_all
      set T_W := (T.comp W.subtypeL).codRestrict W (fun ⟨u, hu⟩ => hT_orth_inv u hu)
      have instCS_W : CompleteSpace ↥W :=
        Submodule.instOrthogonalCompleteSpace (Submodule.span ℝ S)
      have hT_W_sym : (T_W : ↥W →ₗ[ℝ] ↥W).IsSymmetric := by
        intro ⟨x, _⟩ ⟨y, _⟩
        rw [Submodule.coe_inner, Submodule.coe_inner]
        change @inner ℝ E _ (T x) y = @inner ℝ E _ x (T y)
        exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) x y
      have hT_W_sa : @IsSelfAdjoint (↥W →L[ℝ] ↥W)
          (@ContinuousLinearMap.instStarId ℝ ↥W _ _ _ instCS_W) T_W :=
        (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric ℝ ↥W _ _ _ instCS_W).mpr hT_W_sym
      have hT_W_compact : IsCompactOperator T_W :=
        (hK.comp_clm W.subtypeL).codRestrict _ (Submodule.isClosed_orthogonal _)
      have hT_W_ne : T_W ≠ 0 := by
        intro h
        have : T_W ⟨v, hv⟩ = 0 := by rw [h]; simp
        have h2 : (T_W ⟨v, hv⟩ : E) = 0 := congr_arg Subtype.val this
        exact hTv_ne h2
      haveI : Nontrivial W := by
        refine ⟨⟨⟨v, hv⟩, 0, ?_⟩⟩
        intro h
        have := congr_arg Subtype.val h
        simp only [ZeroMemClass.coe_zero] at this
        exact hTv_ne (by rw [this]; simp)
      obtain ⟨μ, e_W, he_ne, he_eig, _⟩ :=
        @hasEigenvector_aux ↥W _ _ instCS_W _ T_W hT_W_sa hT_W_compact hT_W_ne
      have he_eig_E : (T : E →ₗ[ℝ] E) (e_W : E) = μ • (e_W : E) := by
        have h := congr_arg Subtype.val he_eig
        simp only [SetLike.val_smul] at h
        exact h
      have he_norm_ne : ‖(e_W : E)‖ ≠ 0 := by
        intro h; apply he_ne; ext; exact norm_eq_zero.mp h
      exact extend_S ((‖(e_W : E)‖⁻¹ : ℝ) • (e_W : E)) (W.smul_mem _ e_W.2)
        (Set.mem_iUnion.mpr ⟨μ, Module.End.mem_eigenspace_iff.mpr (by
          show (T : E →ₗ[ℝ] E) _ = μ • _
          rw [map_smul, he_eig_E, smul_comm])⟩)
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ he_norm_ne])
  have h_range : (Submodule.span ℝ (Set.range ((↑) : S → E)))ᗮ = ⊥ := by
    rwa [Subtype.range_coe_subtype, Set.setOf_mem_eq]
  let b := HilbertBasis.mkOfOrthogonalEqBot hSo h_range
  have h_eig : ∀ (x : S), ∃ μ : ℝ, (T : E →ₗ[ℝ] E) (x : E) = μ • (x : E) := by
    intro ⟨x, hx⟩
    have := hSe hx; rw [Set.mem_iUnion] at this
    obtain ⟨μ, hμ⟩ := this; exact ⟨μ, Module.End.mem_eigenspace_iff.mp hμ⟩
  refine ⟨↥S, b, fun i => (h_eig i).choose, fun i => ?_⟩
  have hbi : (b i : E) = (i : E) :=
    congr_fun (HilbertBasis.coe_mkOfOrthogonalEqBot hSo h_range) i
  rw [hbi]; exact (h_eig i).choose_spec
theorem compact_selfAdjoint_spectral
    (T : E →L[ℝ] E)
    (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eigenval : ι → ℝ),
      (∀ i, (T : E →ₗ[ℝ] E) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i) (T x)) := by
  obtain ⟨ι, b, μ, hev⟩ := eigenvector_basis T hT_sa hT_compact
  refine ⟨ι, b, μ, hev, fun x => ?_⟩
  have hrepr := b.hasSum_repr x
  have hT_sum : HasSum (fun i => T (b.repr x i • b i)) (T x) :=
    hrepr.mapL T
  have key : ∀ i, T (b.repr x i • b i) = (μ i * @inner ℝ _ _ (b i) x) • b i := fun i => by
    change (T : E →ₗ[ℝ] E) (b.repr x i • b i) = _
    rw [map_smul, hev i, smul_smul, HilbertBasis.repr_apply_apply, mul_comm]
  simp_rw [key] at hT_sum
  exact hT_sum
end GaussianField
end
end

-- GaussianField.NuclearSVD
section
open scoped BigOperators
open Filter TopologicalSpace
noncomputable section
namespace GaussianField
abbrev ell2' := lp (fun _ : ℕ => ℝ) 2
def ell2_basis (m : ℕ) : ell2' := lp.single 2 m (1 : ℝ)
theorem ell2_basis_orthonormal : Orthonormal ℝ ell2_basis := by
  refine ⟨fun m => ?_, fun m n hmn => ?_⟩
  · show ‖ell2_basis m‖ = 1
    simp only [ell2_basis]
    have hp : (0 : ENNReal) < 2 := by norm_num
    rw [lp.norm_single hp]
    exact norm_one
  · show @inner ℝ ell2' _ (ell2_basis m) (ell2_basis n) = 0
    simp only [ell2_basis]
    rw [lp.inner_eq_tsum]
    simp only [lp.coeFn_single, Pi.single_apply]
    convert tsum_zero (α := ℝ) (β := ℕ) with i
    rfl
    simp only [RCLike.inner_apply, conj_trivial]
    split_ifs <;> simp_all
theorem ell2_not_finiteDimensional : ¬ FiniteDimensional ℝ ell2' := by
  intro hfin
  have hli := ell2_basis_orthonormal.linearIndependent
  haveI : Module.Finite ℝ ell2' := hfin
  exact hli.finite.false
instance ell2_separableSpace : SeparableSpace ell2' := by
  rw [← isSeparable_univ_iff]
  have h_dense : (Submodule.span ℝ (Set.range ell2_basis)).topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h_sum : HasSum (fun m => lp.single 2 m ((x : ℕ → ℝ) m)) x :=
      lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
    exact mem_closure_of_tendsto h_sum.tendsto_sum_nat
      (Filter.Eventually.of_forall fun s =>
        Submodule.sum_mem _ fun m _ => by
          have : lp.single 2 m ((x : ℕ → ℝ) m) = (x : ℕ → ℝ) m • ell2_basis m := by
            simp [ell2_basis]; rw [← lp.single_smul]; simp
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
  have h1 := (Set.countable_range ell2_basis).isSeparable.span (R := ℝ)
  have h2 := h1.closure
  have h3 : closure (↑(Submodule.span ℝ (Set.range ell2_basis)) : Set ell2') = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, h_dense]; rfl
  rwa [h3] at h2
theorem orthonormal_countable' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeparableSpace E] {ι : Type*} {e : ι → E} (he : Orthonormal ℝ e) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (e i) (1/2))
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    simp only [Metric.mem_ball] at hz1 hz2
    have h_norm : ‖e i - e j‖ ^ 2 = 2 := by
      rw [sq, ← @inner_self_eq_norm_mul_norm ℝ]
      simp only [inner_sub_left, inner_sub_right]
      simp [he.2 hij, he.2 (Ne.symm hij), he.1 i, he.1 j]; ring
    have h_ge : ‖e i - e j‖ ≥ Real.sqrt 2 := by
      by_contra h_lt
      push Not at h_lt
      have := sq_lt_sq' (by linarith [norm_nonneg (e i - e j)]) h_lt
      rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)] at this; linarith
    linarith [dist_triangle_left (e i) (e j) z, dist_eq_norm (e i) (e j),
              Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num), Real.sqrt_one]
  · intro i; exact Metric.isOpen_ball
  · intro i; exact ⟨e i, Metric.mem_ball_self (by norm_num)⟩
theorem hilbertBasis_fintype_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} [Fintype ι] (b : HilbertBasis ι ℝ E) :
    FiniteDimensional ℝ E := by
  have h_span := b.dense_span
  have h_closed : IsClosed (Submodule.span ℝ (Set.range (b : ι → E)) : Set E) := by
    have : Module.Finite ℝ (Submodule.span ℝ (Set.range (b : ι → E))) :=
      Module.Finite.span_of_finite _ (Set.finite_range _)
    exact Submodule.closed_of_finiteDimensional _
  rw [IsClosed.submodule_topologicalClosure_eq h_closed] at h_span
  have : (⊤ : Submodule ℝ E).FG := by
    rw [← h_span]
    exact ⟨(Set.finite_range (b : ι → E)).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  exact Module.Finite.of_fg_top this
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
theorem compact_selfAdjoint_spectral_nat
    (h_inf : ¬ FiniteDimensional ℝ H)
    (T : H →L[ℝ] H)
    (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    ∃ (u : ℕ → H) (eigenval : ℕ → ℝ),
      Orthonormal ℝ u ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range u)).topologicalClosure) ∧
      (∀ n, (T : H →ₗ[ℝ] H) (u n) = eigenval n • u n) ∧
      (∀ x, HasSum (fun n => (eigenval n * @inner ℝ _ _ (u n) x) • u n) (T x)) := by
  obtain ⟨ι, b, eigenval, hev, hsum⟩ := compact_selfAdjoint_spectral T hT_sa hT_compact
  haveI : Countable ι := orthonormal_countable' b.orthonormal
  haveI : Infinite ι := by
    refine ⟨fun hfin => ?_⟩
    haveI := Fintype.ofFinite ι
    exact h_inf (hilbertBasis_fintype_finiteDimensional b)
  obtain ⟨φ⟩ : Nonempty (ι ≃ ℕ) := nonempty_equiv_of_countable
  refine ⟨b ∘ φ.symm, eigenval ∘ φ.symm, ?_, ?_, ?_, ?_⟩
  · exact b.orthonormal.comp _ φ.symm.injective
  · have h_range : Set.range (b ∘ φ.symm) = Set.range (b : ι → H) := by
      ext x; constructor
      · rintro ⟨n, rfl⟩; exact ⟨φ.symm n, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨φ i, by simp⟩
    rw [h_range]; exact ge_of_eq b.dense_span
  · intro n; exact hev (φ.symm n)
  · intro x; exact (φ.symm.hasSum_iff).mpr (hsum x)
section NuclearOperator
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
omit [InnerProductSpace ℝ K] [CompleteSpace K] in
theorem summable_norm_sq_of_summable_norm {y : ℕ → K}
    (hy : Summable (fun m => ‖y m‖)) :
    Summable (fun m => ‖y m‖ ^ 2) := by
  apply Summable.of_norm_bounded_eventually_nat hy
  have h_tend := hy.tendsto_atTop_zero
  have h_ev : ∀ᶠ m in atTop, ‖y m‖ < 1 := by
    have := h_tend.eventually (Metric.ball_mem_nhds 0 one_pos)
    exact this.mono fun m hm => by simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hm
  exact h_ev.mono fun m hm => by
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
    calc ‖y m‖ ^ 2 = ‖y m‖ * ‖y m‖ := sq _
      _ ≤ 1 * ‖y m‖ := mul_le_mul_of_nonneg_right (le_of_lt hm) (norm_nonneg _)
      _ = ‖y m‖ := one_mul _
theorem summable_smul_of_ell2 (x : ell2') {y : ℕ → K}
    (hy : Summable (fun m => ‖y m‖)) :
    Summable (fun m => (x : ℕ → ℝ) m • y m) := by
  apply Summable.of_norm
  simp_rw [norm_smul]
  have hx_sq : Summable (fun m => ‖(x : ℕ → ℝ) m‖ ^ 2) := by
    refine (lp.summable_inner (𝕜 := ℝ) x x).congr fun m => ?_
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
  have hy_sq := summable_norm_sq_of_summable_norm hy
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · intro m
    have h_amgm : ‖(x : ℕ → ℝ) m‖ * ‖y m‖ ≤ (‖(x : ℕ → ℝ) m‖ ^ 2 + ‖y m‖ ^ 2) / 2 := by
      have := sq_nonneg (‖(x : ℕ → ℝ) m‖ - ‖y m‖)
      nlinarith [sq_abs (‖(x : ℕ → ℝ) m‖), sq_abs (‖y m‖)]
    exact h_amgm
  · exact (hx_sq.add hy_sq).div_const 2
def nuclear_linearMap (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ell2' →ₗ[ℝ] K where
  toFun x := ∑' m, (x : ℕ → ℝ) m • y m
  map_add' x₁ x₂ := by
    simp only [lp.coeFn_add, Pi.add_apply, add_smul]
    have h1 : Summable (fun m => (↑x₁ : ℕ → ℝ) m • y m) := summable_smul_of_ell2 x₁ hy
    have h2 : Summable (fun m => (↑x₂ : ℕ → ℝ) m • y m) := summable_smul_of_ell2 x₂ hy
    exact (h1.hasSum.add h2.hasSum).tsum_eq
  map_smul' c x := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_smul]
    exact (summable_smul_of_ell2 x hy).tsum_const_smul c
theorem nuclear_operator_bound (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ∃ C : ℝ, ∀ x : ell2', ‖nuclear_linearMap y hy x‖ ≤ C * ‖x‖ := by
  use ∑' m, ‖y m‖
  intro x
  have hp : (2 : ENNReal) ≠ 0 := by norm_num
  have h_bound : ∀ m, ‖(x : ℕ → ℝ) m • y m‖ ≤ ‖x‖ * ‖y m‖ := by
    intro m; rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm hp x m) (norm_nonneg _)
  have h_norm_sum : Summable (fun m => ‖(x : ℕ → ℝ) m • y m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) h_bound (hy.mul_left ‖x‖)
  calc ‖nuclear_linearMap y hy x‖
      ≤ ∑' m, ‖(x : ℕ → ℝ) m • y m‖ := norm_tsum_le_tsum_norm h_norm_sum
    _ ≤ ∑' m, ‖x‖ * ‖y m‖ :=
        Summable.tsum_le_tsum h_bound h_norm_sum (hy.mul_left ‖x‖)
    _ = (∑' m, ‖y m‖) * ‖x‖ := by rw [tsum_mul_left]; ring
def nuclear_clm (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ell2' →L[ℝ] K :=
  (nuclear_linearMap y hy).mkContinuous
    (nuclear_operator_bound y hy).choose
    (nuclear_operator_bound y hy).choose_spec
theorem nuclear_clm_basis (y : ℕ → K) (hy : Summable (fun m => ‖y m‖))
    (m : ℕ) : nuclear_clm y hy (ell2_basis m) = y m := by
  simp only [nuclear_clm, LinearMap.mkContinuous_apply, nuclear_linearMap,
             LinearMap.coe_mk, AddHom.coe_mk, ell2_basis]
  simp_rw [lp.coeFn_single, Pi.single_apply]
  simp_rw [ite_smul, one_smul, zero_smul]
  rw [tsum_eq_single m (fun k hk => if_neg hk)]
  simp
end NuclearOperator
section Compactness
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
theorem inner_ell2_basis_eq_coord (x : ell2') (m : ℕ) :
    @inner ℝ ell2' _ (ell2_basis m) x = (x : ℕ → ℝ) m := by
  simp only [ell2_basis]
  rw [lp.inner_eq_tsum]
  simp_rw [lp.coeFn_single, Pi.single_apply]
  conv_lhs =>
    arg 1; ext k
    rw [show @inner ℝ ℝ _ (if k = m then (1 : ℝ) else 0) ((x : ℕ → ℝ) k) =
        if k = m then (x : ℕ → ℝ) k else 0 by
      simp only [RCLike.inner_apply, conj_trivial]
      split_ifs <;> simp]
  rw [tsum_eq_single m (fun k hk => if_neg hk)]
  simp
omit [CompleteSpace K] in
theorem smulRight_isCompactOperator
    (f : ell2' →L[ℝ] ℝ) (v : K) :
    IsCompactOperator (f.smulRight v) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 one_pos, ?_⟩
  refine ⟨(fun c : ℝ => c • v) '' Metric.closedBall 0 ‖f‖, ?_, ?_⟩
  · exact (isCompact_closedBall 0 ‖f‖).image (continuous_id.smul continuous_const)
  · rintro w ⟨x, hx, rfl⟩
    simp only [ContinuousLinearMap.smulRight_apply]
    refine ⟨f x, ?_, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ ‖f‖ * 1 := by apply mul_le_mul_of_nonneg_left (le_of_lt h1) f.opNorm_nonneg
      _ = ‖f‖ := mul_one _
omit [CompleteSpace K] in
theorem finset_sum_isCompactOperator
    {s : Finset ℕ} {F : ℕ → (ell2' →L[ℝ] K)}
    (hF : ∀ m ∈ s, IsCompactOperator (F m)) :
    IsCompactOperator (∑ m ∈ s, F m) := by
  induction s using Finset.induction with
  | empty => simpa using isCompactOperator_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF _ (Finset.mem_insert_self _ _)).add
      (ih (fun m hm' => hF m (Finset.mem_insert_of_mem hm')))
omit [CompleteSpace K] in
theorem rank1_norm_le (y : ℕ → K) (m : ℕ) :
    ‖(innerSL ℝ (ell2_basis m)).smulRight (y m)‖ ≤ ‖y m‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  calc ‖innerSL ℝ (ell2_basis m)‖ * ‖y m‖ ≤ 1 * ‖y m‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [innerSL_apply_norm]
        simp [ell2_basis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    _ = ‖y m‖ := one_mul _
theorem nuclear_clm_isCompact (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    IsCompactOperator (nuclear_clm y hy) := by
  let T : ℕ → (ell2' →L[ℝ] K) := fun m => (innerSL ℝ (ell2_basis m)).smulRight (y m)
  have hT_summable : Summable T :=
    Summable.of_norm_bounded hy (rank1_norm_le y)
  let A_N : ℕ → (ell2' →L[ℝ] K) := fun N => ∑ m ∈ Finset.range N, T m
  have hA_compact : ∀ N, IsCompactOperator (A_N N) := fun N => by
    show IsCompactOperator ⇑(∑ m ∈ Finset.range N, T m)
    rw [FunLike.coe_sum]
    exact finset_sum_isCompactOperator
      (fun m _ => smulRight_isCompactOperator (innerSL ℝ (ell2_basis m)) (y m))
  have hA_tend_tsum : Tendsto A_N atTop (nhds (∑' m, T m)) :=
    hT_summable.tendsto_sum_tsum_nat
  have hA_eq : ∑' m, T m = nuclear_clm y hy := by
    ext x
    have h_eval : (∑' m, T m) x = ∑' m, (T m) x := by
      change ((ContinuousLinearMap.apply ℝ K) x) (∑' m, T m) =
        ∑' m, ((ContinuousLinearMap.apply ℝ K) x) (T m)
      exact (ContinuousLinearMap.apply ℝ K x).map_tsum hT_summable
    rw [h_eval]
    have h_Tm : ∀ m, (T m) x = (x : ℕ → ℝ) m • y m := by
      intro m
      simp only [T, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
      rw [inner_ell2_basis_eq_coord]
    simp_rw [h_Tm]
    rfl
  rw [hA_eq] at hA_tend_tsum
  exact isCompactOperator_of_tendsto hA_tend_tsum (Filter.Eventually.of_forall hA_compact)
end Compactness
section GramOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
theorem gram_isSelfAdjoint' (T : E →L[ℝ] F) :
    IsSelfAdjoint (T.adjoint.comp T) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
theorem gram_isCompact' (T : E →L[ℝ] F) (hT : IsCompactOperator T) :
    IsCompactOperator (T.adjoint.comp T) :=
  hT.clm_comp T.adjoint
end GramOperator
set_option maxHeartbeats 800000 in
theorem summable_sqrt_eigenvalues
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (y : ℕ → K) (hy : Summable (fun m => ‖y m‖))
    (A : ell2' →L[ℝ] K) (hA_basis : ∀ m, A (ell2_basis m) = y m)
    (e : ℕ → K) (he_on : Orthonormal ℝ e)
    (μ_ : ℕ → ℝ)
    (h_Bev : ∀ n, (A.comp A.adjoint) (e n) = μ_ n • e n)
    (h_adjnorm : ∀ n, ‖A.adjoint (e n)‖ ^ 2 = μ_ n) :
    Summable (fun n => Real.sqrt (μ_ n)) := by
  have hσ_eq : ∀ n, Real.sqrt (μ_ n) = ‖A.adjoint (e n)‖ := by
    intro n; rw [← Real.sqrt_sq (norm_nonneg _), h_adjnorm]
  have h_adj_orth : ∀ n k, n ≠ k →
      @inner ℝ ell2' _ (A.adjoint (e n)) (A.adjoint (e k)) = 0 := by
    intro n k hnk
    rw [ContinuousLinearMap.adjoint_inner_right A (A.adjoint (e n)) (e k)]
    conv_lhs => rw [show A (A.adjoint (e n)) = (A.comp A.adjoint) (e n) from
      (ContinuousLinearMap.comp_apply A A.adjoint (e n)).symm]
    rw [h_Bev n, inner_smul_left]; simp [he_on.2 hnk]
  set w : ℕ → ell2' := fun n =>
    if Real.sqrt (μ_ n) = 0 then 0 else (Real.sqrt (μ_ n))⁻¹ • A.adjoint (e n)
  have hw_norm : ∀ n, Real.sqrt (μ_ n) ≠ 0 → ‖w n‖ = 1 := by
    intro n hσ; simp only [w, if_neg hσ, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), hσ_eq, inv_mul_cancel₀]
    rwa [hσ_eq] at hσ
  have hw_orth : ∀ n k, n ≠ k → @inner ℝ ell2' _ (w n) (w k) = 0 := by
    intro n k hnk; simp only [w]
    split_ifs with hn hk hk
    · simp
    · simp
    · simp
    · simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
                  h_adj_orth n k hnk, mul_zero, mul_zero]
  have hw_le : ∀ n, ‖w n‖ ≤ 1 := by
    intro n; by_cases h : Real.sqrt (μ_ n) = 0
    · simp [w, h]
    · exact le_of_eq (hw_norm n h)
  have hw_bessel : ∀ (x : ell2') (S : Finset ℕ),
      ∑ n ∈ S, (@inner ℝ ell2' _ (w n) x) ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x S
    set P := ∑ n ∈ S, @inner ℝ ell2' _ (w n) x • w n with hP_def
    have h0 : (0 : ℝ) ≤ ‖x - P‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at h0
    have h_xP : @inner ℝ ell2' _ x P = ∑ n ∈ S, (@inner ℝ ell2' _ (w n) x) ^ 2 := by
      simp only [hP_def, inner_sum, inner_smul_right, sq, real_inner_comm]
    have h_wP : ∀ n ∈ S, @inner ℝ ell2' _ (w n) P =
        @inner ℝ ell2' _ (w n) x * @inner ℝ ell2' _ (w n) (w n) := by
      intro n hn
      simp only [hP_def, inner_sum, inner_smul_right]
      rw [Finset.sum_eq_single n]
      · intro k _ hkn; rw [hw_orth n k (Ne.symm hkn), mul_zero]
      · intro hn'; exact absurd hn hn'
    have h_P_sq : ‖P‖ ^ 2 ≤ ∑ n ∈ S, (@inner ℝ ell2' _ (w n) x) ^ 2 := by
      rw [hP_def, sq, ← real_inner_self_eq_norm_mul_norm, sum_inner]
      simp only [inner_smul_left, starRingEnd_apply, star_trivial]
      apply Finset.sum_le_sum
      intro n hn
      rw [h_wP n hn, real_inner_self_eq_norm_mul_norm, sq]
      have hw1 : ‖w n‖ * ‖w n‖ ≤ 1 :=
        calc ‖w n‖ * ‖w n‖ ≤ 1 * 1 :=
              mul_le_mul (hw_le n) (hw_le n) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      nlinarith [sq_nonneg (@inner ℝ ell2' _ (w n) x)]
    linarith
  have he_bessel : ∀ (v : K) (S : Finset ℕ),
      ∑ n ∈ S, (@inner ℝ K _ (e n) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    intro v S
    have := he_on.sum_inner_products_le v (s := S)
    simp only [Real.norm_eq_abs, sq_abs] at this; exact this
  apply summable_of_sum_le (c := ∑' m, ‖y m‖) (fun n => Real.sqrt_nonneg _)
  intro S
  have h_coord : ∀ m n, (↑(A.adjoint (e n)) : ℕ → ℝ) m = @inner ℝ K _ (e n) (y m) := by
    intro m n
    have : (↑(A.adjoint (e n)) : ℕ → ℝ) m =
        @inner ℝ ell2' _ (ell2_basis m) (A.adjoint (e n)) := by
      unfold ell2_basis; rw [lp.inner_single_left]
      simp [RCLike.inner_apply, conj_trivial]
    rw [this, ContinuousLinearMap.adjoint_inner_right, hA_basis, real_inner_comm]
  have hc_sum : ∀ n,
      Summable (fun m => (↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m)) := by
    intro n
    exact (lp.summable_inner (𝕜 := ℝ) (w n) (A.adjoint (e n))).congr
      (fun m => by
        simp only [RCLike.inner_apply, conj_trivial, h_coord]; ring)
  have hσ_tsum : ∀ n ∈ S, Real.sqrt (μ_ n) =
      ∑' m, (↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m) := by
    intro n _
    by_cases hσ : Real.sqrt (μ_ n) = 0
    · rw [hσ]
      have : w n = 0 := by simp [w, hσ]
      simp only [this, lp.coeFn_zero, Pi.zero_apply, zero_mul, tsum_zero]
    · have hw_eq : w n = (Real.sqrt (μ_ n))⁻¹ • A.adjoint (e n) := by simp [w, hσ]
      have key : @inner ℝ ell2' _ (w n) (A.adjoint (e n)) = Real.sqrt (μ_ n) := by
        rw [hw_eq, inner_smul_left, starRingEnd_apply, star_trivial,
            real_inner_self_eq_norm_mul_norm, ← hσ_eq]; field_simp
      rw [← key, ← (lp.hasSum_inner (𝕜 := ℝ) (w n) (A.adjoint (e n))).tsum_eq]
      congr 1; ext m
      simp only [RCLike.inner_apply, conj_trivial, h_coord]; ring
  calc ∑ n ∈ S, Real.sqrt (μ_ n)
      = ∑ n ∈ S, ∑' m, (↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m) :=
        Finset.sum_congr rfl hσ_tsum
    _ ≤ ∑ n ∈ S, ∑' m, ‖(↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m)‖ := by
        apply Finset.sum_le_sum; intro n _
        exact (hc_sum n).tsum_mono (hc_sum n).norm (fun m => Real.le_norm_self _)
    _ = ∑' m, ∑ n ∈ S, ‖(↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m)‖ :=
        (Summable.tsum_finsetSum (fun n _ => (hc_sum n).norm)).symm
    _ ≤ ∑' m, ‖y m‖ := by
        apply (summable_sum (fun n _ => (hc_sum n).norm)).tsum_mono hy
        intro m; simp only [norm_mul, Real.norm_eq_abs]
        calc ∑ n ∈ S, |(↑(w n) : ℕ → ℝ) m| * |@inner ℝ K _ (e n) (y m)|
            ≤ Real.sqrt (∑ n ∈ S, ((↑(w n) : ℕ → ℝ) m) ^ 2) *
              Real.sqrt (∑ n ∈ S, (@inner ℝ K _ (e n) (y m)) ^ 2) := by
              rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
              rw [← Real.sqrt_sq (Finset.sum_nonneg
                (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) : (0 : ℝ) ≤ _)]
              apply Real.sqrt_le_sqrt
              have := Finset.sum_mul_sq_le_sq_mul_sq S
                (fun n => |(↑(w n) : ℕ → ℝ) m|) (fun n => |@inner ℝ K _ (e n) (y m)|)
              simp only [sq_abs] at this
              linarith [sq_nonneg (∑ n ∈ S, |(↑(w n) : ℕ → ℝ) m| * |@inner ℝ K _ (e n) (y m)|)]
          _ ≤ 1 * ‖y m‖ := by
              apply mul_le_mul
              · have hw_b := hw_bessel (ell2_basis m) S
                rw [show ‖ell2_basis m‖ = 1 from by
                  simp [ell2_basis, lp.norm_single two_pos], one_pow] at hw_b
                have h_conv : ∀ n, @inner ℝ ell2' _ (w n) (ell2_basis m) =
                    (↑(w n) : ℕ → ℝ) m := by
                  intro n; rw [real_inner_comm]; unfold ell2_basis
                  rw [lp.inner_single_left]
                  simp [RCLike.inner_apply, conj_trivial]
                simp only [h_conv] at hw_b
                exact (Real.sqrt_le_sqrt hw_b).trans (by rw [Real.sqrt_one])
              · have he_b := he_bessel (y m) S
                exact (Real.sqrt_le_sqrt he_b).trans (by rw [Real.sqrt_sq (norm_nonneg _)])
              · exact Real.sqrt_nonneg _
              · exact le_of_lt zero_lt_one
          _ = ‖y m‖ := one_mul _
set_option maxHeartbeats 400000 in
theorem nuclear_sequence_svd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SeparableSpace K] (h_inf : ¬ FiniteDimensional ℝ K)
    (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ∃ (e : ℕ → K) (σ_ : ℕ → ℝ) (W : ℕ → ℕ → ℝ),
      Orthonormal ℝ e ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) ∧
      (∀ n, 0 ≤ σ_ n) ∧
      Summable σ_ ∧
      (∀ n m, @inner ℝ K _ (e n) (y m) = σ_ n * W n m) ∧
      (∀ n, σ_ n ≠ 0 → HasSum (fun m => (W n m) ^ 2) 1) ∧
      (∀ n k, n ≠ k → σ_ n ≠ 0 → σ_ k ≠ 0 →
        HasSum (fun m => W n m * W k m) 0) ∧
      (∀ n, σ_ n = 0 → ∀ m, W n m = 0) := by
  let A := nuclear_clm y hy
  have hA_basis : ∀ m, A (ell2_basis m) = y m := nuclear_clm_basis y hy
  have hA_compact : IsCompactOperator A := nuclear_clm_isCompact y hy
  set B := A.comp A.adjoint with hB_def
  have hB_sa : IsSelfAdjoint B := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hB_compact : IsCompactOperator B := hA_compact.comp_clm A.adjoint
  obtain ⟨e, μ_, he_on, he_span, he_ev, he_sum⟩ :=
    compact_selfAdjoint_spectral_nat h_inf B hB_sa hB_compact
  have h_Bev : ∀ n, B (e n) = μ_ n • e n := by
    intro n; exact_mod_cast he_ev n
  have h_B_inner_adjnorm : ∀ n,
      @inner ℝ K _ (B (e n)) (e n) = ‖A.adjoint (e n)‖ ^ 2 := by
    intro n
    simp only [hB_def, ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right A (A.adjoint (e n)) (e n)]
    exact real_inner_self_eq_norm_sq _
  have h_inner_self_one : ∀ n, @inner ℝ K _ (e n) (e n) = (1 : ℝ) := by
    intro n; rw [real_inner_self_eq_norm_sq, sq, he_on.1 n, mul_one]
  have hμ_nn : ∀ n, 0 ≤ μ_ n := by
    intro n
    have h_eigen : @inner ℝ K _ (B (e n)) (e n) = μ_ n := by
      rw [h_Bev n, real_inner_smul_left, h_inner_self_one, mul_one]
    linarith [h_B_inner_adjnorm n, sq_nonneg ‖A.adjoint (e n)‖]
  have h_adjnorm : ∀ n, ‖A.adjoint (e n)‖ ^ 2 = μ_ n := by
    intro n
    have h2 : @inner ℝ K _ (B (e n)) (e n) = μ_ n := by
      rw [h_Bev n, real_inner_smul_left, h_inner_self_one, mul_one]
    linarith [h_B_inner_adjnorm n]
  let σ_ : ℕ → ℝ := fun n => Real.sqrt (μ_ n)
  have hσ_zero_iff : ∀ n, σ_ n = 0 ↔ μ_ n = 0 := by
    intro n; simp [σ_]; exact Real.sqrt_eq_zero (hμ_nn n)
  have hAdj_zero_of_σ : ∀ n, σ_ n = 0 → A.adjoint (e n) = 0 := by
    intro n hσ
    have hμ : μ_ n = 0 := (hσ_zero_iff n).mp hσ
    have : ‖A.adjoint (e n)‖ ^ 2 = 0 := by rw [h_adjnorm]; exact hμ
    exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖A.adjoint (e n)‖])
  have h_coord : ∀ n m, @inner ℝ ell2' _ (A.adjoint (e n)) (ell2_basis m) =
      (A.adjoint (e n) : ℕ → ℝ) m :=
    fun n m => by rw [real_inner_comm]; exact inner_ell2_basis_eq_coord _ _
  let W : ℕ → ℕ → ℝ := fun n m =>
    if σ_ n = 0 then 0
    else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m
  refine ⟨e, σ_, W, he_on, he_span, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact fun n => Real.sqrt_nonneg _
  ·
    exact summable_sqrt_eigenvalues y hy A hA_basis e he_on μ_ h_Bev h_adjnorm
  ·
    intro n m
    show @inner ℝ K _ (e n) (y m) =
      σ_ n * (if σ_ n = 0 then 0 else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m)
    split_ifs with hσ
    · have hAdj := hAdj_zero_of_σ n hσ
      rw [← hA_basis m, ← ContinuousLinearMap.adjoint_inner_left, hAdj,
          inner_zero_left]
      simp
    · rw [← hA_basis m, ← ContinuousLinearMap.adjoint_inner_left, h_coord]
      field_simp
  ·
    intro n hσ_ne
    show HasSum (fun m => (if σ_ n = 0 then 0
      else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m) ^ 2) 1
    simp only [if_neg hσ_ne]
    have h := lp.hasSum_inner (𝕜 := ℝ) (A.adjoint (e n)) (A.adjoint (e n))
    rw [real_inner_self_eq_norm_sq] at h
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] at h
    have h2 := h.mul_left ((σ_ n)⁻¹ ^ 2)
    simp only [← mul_pow] at h2
    convert h2 using 1
    rfl
    rw [mul_pow, inv_pow, h_adjnorm, show σ_ n = Real.sqrt (μ_ n) from rfl,
        Real.sq_sqrt (hμ_nn n)]
    have hμ_ne : μ_ n ≠ 0 := by
      intro h; exact hσ_ne (by simp [σ_, h])
    exact (inv_mul_cancel₀ hμ_ne).symm
  ·
    intro n k hnk hσn hσk
    show HasSum (fun m =>
      (if σ_ n = 0 then 0 else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m) *
      (if σ_ k = 0 then 0 else (σ_ k)⁻¹ * (A.adjoint (e k) : ℕ → ℝ) m)) 0
    simp only [if_neg hσn, if_neg hσk]
    have h_adj_orth : @inner ℝ ell2' _ (A.adjoint (e n)) (A.adjoint (e k)) = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_right A (A.adjoint (e n)) (e k)]
      conv_lhs => rw [show A (A.adjoint (e n)) = (A.comp A.adjoint) (e n) from
        (ContinuousLinearMap.comp_apply A A.adjoint (e n)).symm]
      rw [h_Bev n, inner_smul_left]
      simp [he_on.2 hnk]
    have h := lp.hasSum_inner (𝕜 := ℝ) (A.adjoint (e n)) (A.adjoint (e k))
    rw [h_adj_orth] at h
    have h2 : HasSum (fun m => (A.adjoint (e n) : ℕ → ℝ) m *
        (A.adjoint (e k) : ℕ → ℝ) m) 0 := by
      refine h.congr_fun fun m => ?_
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]; ring
    have h3 := h2.mul_left ((σ_ n)⁻¹ * (σ_ k)⁻¹)
    simp only [mul_zero] at h3
    exact h3.congr_fun fun m => by ring
  ·
    intro n hσ m
    show (if σ_ n = 0 then 0 else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m) = 0
    simp [hσ]
end GaussianField
end
end

-- GaussianField.TargetFactorization
section
open scoped BigOperators
open Filter TopologicalSpace
noncomputable section
namespace GaussianField
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E] in
theorem ell2_inner_eq_tsum (x y : ell2') :
    @inner ℝ ell2' _ x y = ∑' m, @inner ℝ _ _ ((x : ℕ → ℝ) m) ((y : ℕ → ℝ) m) :=
  lp.inner_eq_tsum x y
omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E] in
theorem summable_smul_ell2 (σ_ : ℕ → ℝ) (u : ℕ → ell2')
    (hσ : Summable σ_) (hσ_nn : ∀ n, 0 ≤ σ_ n)
    (hu : ∀ n, σ_ n ≠ 0 → ‖u n‖ = 1) :
    Summable (fun n => ‖σ_ n • u n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hσ
  intro n
  rw [norm_smul]
  by_cases hσn : σ_ n = 0
  · simp [hσn]
  · rw [hu n hσn, mul_one, Real.norm_of_nonneg (hσ_nn n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem nuclear_ell2_embedding_from_decay
    (φ : ℕ → (E →L[ℝ] ℝ))
    (s : Finset (DyninMityaginSpace.ι (E := E))) (C : ℝ) (hC : 0 < C)
    (hφ_decay : ∀ (m : ℕ) (f : E),
      |φ m f| ≤ (C * (s.sup DyninMityaginSpace.p) f) * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ)) :
    ∃ (j : E →L[ℝ] ell2'),
      ∀ (f : E) (m : ℕ), (j f : ℕ → ℝ) m = φ m f := by
  have hφ_memℓp : ∀ (f : E), Memℓp (fun m => φ m f) 2 := by
    intro f
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat]
    set Cf := C * (s.sup DyninMityaginSpace.p) f with hCf_def
    have hbd : ∀ m : ℕ, |φ m f| ≤ Cf * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
      intro m; exact hφ_decay m f
    have hsq_bound : ∀ m : ℕ, ‖φ m f‖ ^ (2 : ℝ) ≤
        Cf ^ 2 * (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) := by
      intro m
      have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
      have hCf_nn : 0 ≤ Cf * (1 + ↑m) ^ ((-2 : ℤ) : ℝ) := by
        apply mul_nonneg (mul_nonneg (le_of_lt hC) (apply_nonneg _ _))
        exact Real.rpow_nonneg (le_of_lt hpos) _
      rw [Real.norm_eq_abs]
      have h1 : |φ m f| ^ (2 : ℝ) ≤ (Cf * (1 + ↑m) ^ ((-2 : ℤ) : ℝ)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (hbd m) (by norm_num)
      have h2 : (Cf * (1 + ↑m) ^ ((-2 : ℤ) : ℝ)) ^ (2 : ℝ) =
          Cf ^ 2 * (1 + ↑m) ^ ((-4 : ℤ) : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast, mul_pow]
        congr 1
        rw [← Real.rpow_natCast ((1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ)) 2,
            show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_cast,
            ← Real.rpow_mul (le_of_lt hpos)]
        norm_cast
      linarith
    have h4_summ : Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) := by
      have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-4 : ℤ) : ℝ)) 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : ((-4 : ℤ) : ℝ) < -1))
      simp only [Nat.cast_add, Nat.cast_one] at h
      exact h.congr fun m => by push_cast; ring_nf
    exact Summable.of_nonneg_of_le
      (fun m => by positivity)
      hsq_bound
      (h4_summ.mul_left _)
  set j_fun : E → ell2' :=
    fun f => ⟨fun m => φ m f, hφ_memℓp f⟩ with hj_fun_def
  have hadd : ∀ (f g : E), j_fun (f + g) = j_fun f + j_fun g := by
    intro f g; ext m
    simp only [hj_fun_def, map_add, lp.coeFn_add, Pi.add_apply]
  have hsmul : ∀ (a : ℝ) (f : E), j_fun (a • f) = a • j_fun f := by
    intro a f; ext m
    simp [hj_fun_def, lp.coeFn_smul, map_smul, smul_eq_mul, Pi.smul_apply]
  set j_lin : E →ₗ[ℝ] ell2' :=
    { toFun := j_fun, map_add' := hadd, map_smul' := hsmul }
  have h4_summ : Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) := by
    have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-4 : ℤ) : ℝ)) 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num : ((-4 : ℤ) : ℝ) < -1))
    simp only [Nat.cast_add, Nat.cast_one] at h
    exact h.congr fun m => by push_cast; ring_nf
  set ζ4 := ∑' (m : ℕ), (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) with hζ4_def
  have h_norm_sq : ∀ f : E, ‖j_fun f‖ ^ 2 ≤
      C ^ 2 * ζ4 * ((s.sup DyninMityaginSpace.p) f) ^ 2 := by
    intro f
    rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
    simp_rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hj_fun_def]
    have h_sq_summ : Summable (fun m : ℕ => (φ m f) ^ 2) := by
      have h := lp.summable_inner (𝕜 := ℝ) (⟨fun m => φ m f, hφ_memℓp f⟩ : ell2')
        (⟨fun m => φ m f, hφ_memℓp f⟩ : ell2')
      simp only at h
      exact h.congr (fun m => by
        rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]; ring)
    have h_ptwise : ∀ m : ℕ, (φ m f) ^ 2 ≤
        (C * (s.sup DyninMityaginSpace.p) f) ^ 2 *
          (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) := by
      intro m
      have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
      have hCf_nn : 0 ≤ C * (s.sup DyninMityaginSpace.p) f *
          (1 + ↑m) ^ ((-2 : ℤ) : ℝ) := by
        apply mul_nonneg (mul_nonneg (le_of_lt hC) (apply_nonneg _ _))
        exact Real.rpow_nonneg (le_of_lt hpos) _
      rw [← sq_abs (φ m f)]
      calc |φ m f| ^ 2
          ≤ (C * (s.sup DyninMityaginSpace.p) f *
              (1 + ↑m) ^ ((-2 : ℤ) : ℝ)) ^ 2 :=
            sq_le_sq' (by linarith [abs_nonneg (φ m f)]) (hφ_decay m f)
        _ = (C * (s.sup DyninMityaginSpace.p) f) ^ 2 *
              (1 + ↑m) ^ ((-4 : ℤ) : ℝ) := by
            rw [mul_pow]; congr 1
            rw [← Real.rpow_natCast ((1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ)) 2,
                ← Real.rpow_mul (le_of_lt hpos)]
            norm_cast
    calc ∑' m, (φ m f) ^ 2
        ≤ ∑' (m : ℕ), ((C * (s.sup DyninMityaginSpace.p) f) ^ 2 *
            (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) :=
          Summable.tsum_le_tsum h_ptwise h_sq_summ (h4_summ.mul_left _)
      _ = (C * (s.sup DyninMityaginSpace.p) f) ^ 2 * ζ4 := tsum_mul_left
      _ = C ^ 2 * ζ4 * ((s.sup DyninMityaginSpace.p) f) ^ 2 := by ring
  have hζ4_nn : 0 ≤ ζ4 := tsum_nonneg (fun m => Real.rpow_nonneg (by positivity) _)
  set B : ℝ := C * Real.sqrt ζ4
  have hB_nn : 0 ≤ B := by positivity
  have h_norm_bound : ∀ f : E, ‖j_fun f‖ ≤ B * (s.sup DyninMityaginSpace.p) f := by
    intro f
    have hB_sq : B ^ 2 = C ^ 2 * ζ4 := by
      show (C * Real.sqrt ζ4) ^ 2 = C ^ 2 * ζ4
      rw [mul_pow, Real.sq_sqrt hζ4_nn]
    have h2 := h_norm_sq f
    have h3 : ‖j_fun f‖ ^ 2 ≤ (B * (s.sup DyninMityaginSpace.p) f) ^ 2 := by
      rw [mul_pow, hB_sq]; exact h2
    exact le_of_sq_le_sq h3 (mul_nonneg hB_nn (apply_nonneg _ _))
  have j_cont : Continuous j_lin := by
    apply WithSeminorms.continuous_normedSpace_rng ell2' DyninMityaginSpace.h_with
    refine ⟨s, ⟨⟨B, hB_nn⟩, ?_⟩⟩
    rw [Seminorm.le_def]
    intro f
    simp only [Seminorm.comp_apply, coe_normSeminorm,
               ]
    exact h_norm_bound f
  exact ⟨⟨j_lin, j_cont⟩, fun f m => rfl⟩
theorem nuclear_clm_target_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (h_inf : ¬ FiniteDimensional ℝ H)
    (T : E →L[ℝ] H) :
    ∃ (e : ℕ → H)
      (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K)
      (j : E →L[ℝ] K) (v : ℕ → K),
      Orthonormal ℝ e ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) ∧
      Summable (fun n => ‖v n‖) ∧
      ∀ (f : E) (n : ℕ),
        @inner ℝ H _ (e n) (T f) = @inner ℝ K _ (v n) (j f) := by
  set c := DyninMityaginSpace.coeff (E := E) with hc_def
  set ψ := DyninMityaginSpace.basis (E := E) with hψ_def
  obtain ⟨C_g, p₁, hCg_pos, hT_growth⟩ := clm_image_growth T
  set s_exp : ℕ := p₁ + 2
  set s_real : ℝ := ↑s_exp with hs_def
  set y : ℕ → H := fun m => ((1 + (m : ℝ)) ^ (-s_real)) • T (ψ m) with hy_def
  set φ : ℕ → (E →L[ℝ] ℝ) :=
    fun m => ((1 + (m : ℝ)) ^ s_real) • c m with hφ_def
  have hy_sum : Summable (fun m => ‖y m‖) := by
    simp only [hy_def]
    refine Summable.of_norm_bounded (summable_one_add_rpow_neg_two.mul_left C_g) (fun m => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ↑m) _)]
    have hpos : (0 : ℝ) < 1 + ↑m := by positivity
    calc (1 + (↑m : ℝ)) ^ (-s_real) * ‖T (ψ m)‖
        ≤ (1 + (↑m : ℝ)) ^ (-s_real) * (C_g * (1 + (↑m : ℝ)) ^ p₁) :=
          mul_le_mul_of_nonneg_left (hT_growth m) (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ p₁) := by ring
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ ((p₁ : ℝ))) := by
          congr 2; exact (Real.rpow_natCast _ _).symm
      _ = C_g * (1 + (↑m : ℝ)) ^ ((-2) : ℝ) := by
          congr 1; rw [← Real.rpow_add hpos]; congr 1
          rw [hs_def, show s_exp = p₁ + 2 from rfl]; push_cast; ring
  have hexpand : ∀ (f : E) (w : H),
      @inner ℝ H _ w (T f) = ∑' m, φ m f * @inner ℝ H _ w (y m) := by
    intro f w
    rw [DyninMityaginSpace.expansion_H T w f]
    congr 1; ext m
    simp only [hφ_def, hy_def, smul_apply, smul_eq_mul, inner_smul_right]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    rw [Real.rpow_neg (le_of_lt hpos)]
    have hne : (1 + (↑m : ℝ)) ^ s_real ≠ 0 := (Real.rpow_pos_of_pos hpos s_real).ne'
    field_simp; rfl
  obtain ⟨e, σ_, W, he_on, he_span, hσ_nn, hσ_sum,
          hsvd_inner, hW_unit, hW_orth, hW_zero⟩ :=
    nuclear_sequence_svd h_inf y hy_sum
  obtain ⟨C_d, hCd_pos, s_d, hdecay_strong⟩ := DyninMityaginSpace.coeff_decay (E := E) (s_exp + 2)
  have hφ_decay : ∀ (m : ℕ) (f : E),
      |φ m f| ≤ (C_d * (s_d.sup DyninMityaginSpace.p) f) *
        (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
    intro m f
    simp only [hφ_def, smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + ↑m) s_real)]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    have hd := hdecay_strong f m
    rw [mul_comm ((1 + (↑m : ℝ)) ^ s_real) (|c m f|)]
    rw [hs_def, Real.rpow_natCast]
    have h_split : (1 + (↑m : ℝ)) ^ s_exp =
        (1 + ↑m) ^ (s_exp + 2) * (1 + ↑m) ^ ((-2 : ℤ) : ℝ) := by
      rw [show ((-2 : ℤ) : ℝ) = (-2 : ℝ) from by norm_cast,
          ← Real.rpow_natCast (1 + (↑m : ℝ)) (s_exp + 2),
          ← Real.rpow_add hpos, ← Real.rpow_natCast (1 + (↑m : ℝ)) s_exp]
      congr 1; push_cast; ring
    rw [h_split]
    simp only [hc_def]
    have hrpow_nn : (0 : ℝ) ≤ (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ) :=
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ↑m) _
    rw [← mul_assoc]
    gcongr
  obtain ⟨j, hj_spec⟩ := nuclear_ell2_embedding_from_decay φ s_d C_d hCd_pos hφ_decay
  have hv_mem : ∀ n, Memℓp (fun m => σ_ n * W n m) 2 := by
    intro n
    by_cases hσn : σ_ n = 0
    · have : (fun m => σ_ n * W n m) = 0 := by ext; simp [hσn]
      rw [this]; exact zero_memℓp
    · have : Memℓp (fun m => W n m) 2 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_ofNat]
        exact (hW_unit n hσn).summable.congr (fun m => by simp [Real.norm_eq_abs, sq_abs])
      exact this.const_smul (σ_ n)
  set v : ℕ → ell2' := fun n => ⟨fun m => σ_ n * W n m, hv_mem n⟩
  refine ⟨e, ell2', inferInstance, inferInstance, inferInstance, j, v,
          he_on, he_span, ?_, ?_⟩
  ·
    suffices h : ∀ n, ‖v n‖ = σ_ n by
      rw [show (fun n => ‖v n‖) = σ_ from funext h]
      exact hσ_sum
    intro n
    by_cases hσn : σ_ n = 0
    · have : v n = 0 := by
        ext m; simp only [v, hσn, hW_zero n hσn m, mul_zero, lp.coeFn_zero, Pi.zero_apply]
      rw [this, norm_zero, hσn]
    · have h_sq : ‖v n‖ ^ 2 = σ_ n ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
        simp_rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, v]
        simp_rw [mul_pow]
        rw [tsum_mul_left, (hW_unit n hσn).tsum_eq, mul_one]
      have h1 : (‖v n‖ - σ_ n) * (‖v n‖ + σ_ n) = 0 := by nlinarith [h_sq]
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · linarith [norm_nonneg (v n), hσ_nn n]
  ·
    intro f n
    have lhs : @inner ℝ H _ (e n) (T f) = ∑' m, (φ m f) * (σ_ n * W n m) := by
      rw [hexpand f (e n)]
      congr 1; ext m; rw [hsvd_inner]
    have rhs : @inner ℝ ell2' _ (v n) (j f) = ∑' m, (σ_ n * W n m) * (φ m f) := by
      rw [lp.inner_eq_tsum]
      congr 1; ext m
      simp only [v]
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
      rw [hj_spec f m]; ring
    rw [lhs, rhs]
    congr 1; ext m; ring
end GaussianField
end
end

-- GaussianField.Construction
section
noncomputable section
namespace GaussianField
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators
open Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
abbrev Configuration (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] :=
  WeakDual ℝ E
instance instMeasurableSpaceConfiguration :
    MeasurableSpace (Configuration E) :=
  MeasurableSpace.comap (fun ω f => ω f) MeasurableSpace.pi
omit [DyninMityaginSpace E] in
theorem configuration_measurable_of_eval_measurable
    {X : Type*} [MeasurableSpace X] (g : X → Configuration E)
    (h : ∀ φ : E, Measurable (fun x => g x φ)) :
    @Measurable X (Configuration E) _ instMeasurableSpaceConfiguration g := by
  rw [measurable_iff_comap_le]
  show (MeasurableSpace.comap (fun ω f => ω f) MeasurableSpace.pi).comap g ≤ _
  rw [MeasurableSpace.comap_comp]
  exact (measurable_pi_lambda _ h).comap_le
omit [DyninMityaginSpace E] in
theorem configuration_eval_measurable (φ : E) :
    @Measurable (Configuration E) ℝ instMeasurableSpaceConfiguration _ (fun ω => ω φ) := by
  intro s hs
  exact ⟨(fun f => f φ) ⁻¹' s, measurable_pi_apply φ hs, rfl⟩
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
def covariance (T : E →L[ℝ] H) (f g : E) : ℝ :=
  @inner ℝ H _ (T f) (T g)
private noncomputable def fullFactorization
    (T : E →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H) :=
  nuclear_clm_target_factorization h_inf T
private noncomputable def factProps (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) :=
  (fullFactorization T h_inf).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
private noncomputable def adaptedONB (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : ℕ → H :=
  (fullFactorization T h_inf).choose
private noncomputable def FactK (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : Type :=
  (fullFactorization T h_inf).choose_spec.choose
private noncomputable instance instNACG_FactK (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : NormedAddCommGroup (FactK T h_inf) :=
  (fullFactorization T h_inf).choose_spec.choose_spec.choose
private noncomputable instance instIPS_FactK (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : InnerProductSpace ℝ (FactK T h_inf) :=
  (fullFactorization T h_inf).choose_spec.choose_spec.choose_spec.choose
private noncomputable instance instCS_FactK (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : CompleteSpace (FactK T h_inf) :=
  (fullFactorization T h_inf).choose_spec.choose_spec.choose_spec.choose_spec.choose
private noncomputable def factJ (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : E →L[ℝ] FactK T h_inf :=
  (fullFactorization T h_inf).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
private noncomputable def factV (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : ℕ → FactK T h_inf :=
  (fullFactorization T h_inf).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
private lemma adaptedONB_orthonormal (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : Orthonormal ℝ (adaptedONB T h_inf) :=
  (factProps T h_inf).1
private lemma adaptedONB_spans (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) :
    ⊤ ≤ (Submodule.span ℝ (Set.range (adaptedONB T h_inf))).topologicalClosure :=
  (factProps T h_inf).2.1
private lemma factV_summable (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : Summable (fun n => ‖factV T h_inf n‖) :=
  (factProps T h_inf).2.2.1
private lemma factV_inner_eq (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) (f : E) (n : ℕ) :
    @inner ℝ H _ (adaptedONB T h_inf n) (T f) =
    @inner ℝ (FactK T h_inf) _ (factV T h_inf n) (factJ T h_inf f) :=
  (factProps T h_inf).2.2.2 f n
private noncomputable def adaptedBasis (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) : HilbertBasis ℕ ℝ H :=
  HilbertBasis.mk (adaptedONB_orthonormal T h_inf) (adaptedONB_spans T h_inf)
private lemma adaptedBasis_eq_ONB (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) :
    ⇑(adaptedBasis T h_inf) = adaptedONB T h_inf :=
  HilbertBasis.coe_mk _ _
private noncomputable def coeff (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) (n : ℕ) (f : E) : ℝ :=
  @inner ℝ H _ (adaptedONB T h_inf n) (T f)
private lemma coeff_sq_summable (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) (f : E) :
    Summable (fun n => (coeff T h_inf n f) ^ 2) := by
  set c := (adaptedBasis T h_inf).repr (T f) with hc_def
  have hsumm := Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) c.property
  simp only [ENNReal.toReal_ofNat] at hsumm
  have hsumm' : Summable (fun n => ‖(c : ℕ → ℝ) n‖^(2 : ℕ)) := by
    simp only [← Real.rpow_natCast] at hsumm ⊢
    convert hsumm using 2; rfl
  convert hsumm' using 2 with n
  rw [coeff, show adaptedONB T h_inf n = adaptedBasis T h_inf n from
    (adaptedBasis_eq_ONB T h_inf).symm ▸ rfl]
  rw [show @inner ℝ H _ (adaptedBasis T h_inf n) (T f) =
    (adaptedBasis T h_inf).repr (T f) n from
    ((adaptedBasis T h_inf).repr_apply_apply (T f) n).symm]
  simp [sq_abs, ← hc_def]
private lemma coeff_parseval (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) (f : E) :
    ∑' n, (coeff T h_inf n f) ^ 2 = ‖T f‖ ^ 2 := by
  set x := T f with hx_def
  set c := (adaptedBasis T h_inf).repr x with hc_def
  have hiso : ‖x‖ = ‖c‖ := ((adaptedBasis T h_inf).repr.norm_map x).symm
  have hlp := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) c
  simp only [ENNReal.toReal_ofNat] at hlp
  have hlp' : ‖c‖^(2 : ℕ) = ∑' n, ‖(c : ℕ → ℝ) n‖^(2 : ℕ) := by
    simp only [← Real.rpow_natCast] at hlp ⊢
    convert hlp using 2 <;> rfl
  calc ∑' n, (coeff T h_inf n f)^2
      = ∑' n, ‖(c : ℕ → ℝ) n‖^2 := by
        congr 1; ext n
        rw [coeff, show adaptedONB T h_inf n = adaptedBasis T h_inf n from
          (adaptedBasis_eq_ONB T h_inf).symm ▸ rfl]
        rw [show @inner ℝ H _ (adaptedBasis T h_inf n) x =
          (adaptedBasis T h_inf).repr x n from
          ((adaptedBasis T h_inf).repr_apply_apply x n).symm]
        simp [sq_abs, ← hc_def]
    _ = ‖c‖^2 := hlp'.symm
    _ = ‖x‖^2 := by rw [hiso]
abbrev NoiseSpace := ℕ → ℝ
private noncomputable def noiseMeasure : Measure NoiseSpace :=
  Measure.infinitePi (fun _ => gaussianReal 0 1)
private instance noiseMeasure_isProbability : IsProbabilityMeasure noiseMeasure :=
  Measure.instIsProbabilityMeasureForallInfinitePi _
private def IsGoodNoise (T : E →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H)
    (ξ : NoiseSpace) : Prop :=
  Summable (fun n => ξ n • factV T h_inf n)
private lemma IsGoodNoise.scalar_summable
    {T : E →L[ℝ] H} {h_inf : ¬ FiniteDimensional ℝ H} {ξ : NoiseSpace}
    (h : IsGoodNoise T h_inf ξ) (f : E) :
    Summable (fun n => ξ n * coeff T h_inf n f) := by
  have hK := (innerSL ℝ (factJ T h_inf f)).summable h
  exact hK.congr fun n => by
    rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm,
        ← factV_inner_eq T h_inf f n]; rfl
private noncomputable def seriesLimitFun
    (T : E →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H)
    (ξ : NoiseSpace) (f : E) : ℝ :=
  if IsGoodNoise T h_inf ξ
  then ∑' n, ξ n * coeff T h_inf n f
  else 0
private noncomputable def seriesLimitLinear
    (T : E →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H)
    (ξ : NoiseSpace) : E →ₗ[ℝ] ℝ where
  toFun := seriesLimitFun T h_inf ξ
  map_add' := fun f g => by
    simp only [seriesLimitFun]
    split_ifs with h
    · have hf := h.scalar_summable f
      have hg := h.scalar_summable g
      have heq : (fun n => ξ n * coeff T h_inf n (f + g)) =
                 (fun n => ξ n * coeff T h_inf n f + ξ n * coeff T h_inf n g) := by
        ext n; simp [coeff, inner_add_right, mul_add]
      conv_lhs => rw [heq]
      exact hf.tsum_add hg
    · simp
  map_smul' := fun c f => by
    simp only [seriesLimitFun, RingHom.id_apply, smul_eq_mul]
    split_ifs with h
    · have hf := h.scalar_summable f
      have heq : (fun n => ξ n * coeff T h_inf n (c • f)) =
                 (fun n => c • (ξ n * coeff T h_inf n f)) := by
        ext n; simp [coeff, real_inner_smul_right, smul_eq_mul]; ring
      conv_lhs => rw [heq]
      rw [hf.tsum_const_smul c, smul_eq_mul]
    · rw [mul_zero]
private noncomputable def seriesLimit
    (T : E →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H)
    (ξ : NoiseSpace) : Configuration E :=
  ⟨seriesLimitLinear T h_inf ξ, by
    by_cases h : IsGoodNoise T h_inf ξ
    ·
      let w : FactK T h_inf := ∑' n, ξ n • factV T h_inf n
      have h_eq : ∀ f, ∑' n, ξ n * coeff T h_inf n f =
          @inner ℝ (FactK T h_inf) _ w (factJ T h_inf f) := by
        intro f
        simp_rw [coeff, factV_inner_eq T h_inf f]
        have h_clm := (innerSL ℝ (factJ T h_inf f)).map_tsum h
        rw [show @inner ℝ (FactK T h_inf) _ w (factJ T h_inf f) =
              @inner ℝ (FactK T h_inf) _ (factJ T h_inf f) w from
                real_inner_comm _ _]
        rw [show @inner ℝ (FactK T h_inf) _ (factJ T h_inf f) w =
              (innerSL ℝ (factJ T h_inf f)) w from rfl]
        rw [h_clm]
        congr 1; ext n
        simp [innerSL_apply_apply, real_inner_comm (factV T h_inf n) (factJ T h_inf f)]
      have h_cont : Continuous (fun f => @inner ℝ (FactK T h_inf) _ w (factJ T h_inf f)) :=
        ((innerSL ℝ w).comp (factJ T h_inf)).continuous
      convert h_cont using 1
      ext f
      show seriesLimitFun T h_inf ξ f = _
      simp only [seriesLimitFun, if_pos h]
      exact h_eq f
    ·
      have h0 : (seriesLimitLinear T h_inf ξ).toFun = fun _ => 0 := by
        ext f; show seriesLimitFun T h_inf ξ f = 0
        simp only [seriesLimitFun, if_neg h]
      simp only [h0]
      exact continuous_const⟩
set_option maxHeartbeats 1600000 in
private theorem hilbert_gaussian_series_converges
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (v : ℕ → K) (hv : Summable (fun n => ‖v n‖)) :
    ∀ᵐ ξ ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)),
      Summable (fun n => ξ n • v n) := by
  set μ := fun _ : ℕ => gaussianReal (0 : ℝ) 1
  set P := Measure.infinitePi μ
  set C := ∫⁻ x : ℝ, ↑‖x‖₊ ∂(μ 0) with hC_def
  have hC : C ≠ ⊤ := by
    have h := (IsGaussian.integrable_dual (μ 0)
      (ContinuousLinearMap.id ℝ ℝ)).hasFiniteIntegral
    rw [hasFiniteIntegral_def] at h
    simp only [ContinuousLinearMap.id_apply, enorm_eq_nnnorm] at h
    exact h.ne
  have hv_nn : Summable (fun n => ‖v n‖₊) := by
    have h1 : (fun n => (‖v n‖₊ : ℝ)) = fun n => ‖v n‖ := funext fun n => coe_nnnorm (v n)
    exact NNReal.summable_coe.mp (h1 ▸ hv)
  have hv_ennreal : tsum (fun n => ((‖v n‖₊ : NNReal) : ENNReal)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hv_nn
  have h_meas_f : ∀ n, Measurable (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal)) :=
    fun n => (measurable_pi_apply n).nnnorm.coe_nnreal_ennreal
  have h_meas : ∀ n, Measurable (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal) * ‖v n‖₊) :=
    fun n => (h_meas_f n).mul_const _
  have h_eval : ∀ n, ∫⁻ ξ, (‖ξ n‖₊ : ENNReal) ∂P = C := fun n =>
    (measurePreserving_eval_infinitePi μ n).lintegral_comp
      measurable_nnnorm.coe_nnreal_ennreal
  have h_finite : ∫⁻ ξ, ∑' n, ((‖ξ n‖₊ : ENNReal) * ‖v n‖₊) ∂P ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (h_meas n).aemeasurable)]
    simp_rw [lintegral_mul_const _ (h_meas_f _), h_eval, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hC hv_ennreal
  have h_ae := ae_lt_top (Measurable.tsum h_meas) h_finite
  exact h_ae.mono fun ξ hξ => by
    simp_rw [← ENNReal.coe_mul] at hξ
    have hξ' : Summable (fun n => ‖ξ n‖₊ * ‖v n‖₊) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp hξ.ne
    have hξ'' : Summable (fun n => ‖ξ n • v n‖) := by
      refine (NNReal.summable_coe.mpr hξ').congr fun n => ?_
      rw [NNReal.coe_mul, coe_nnnorm, coe_nnnorm, norm_smul]
    exact hξ''.of_norm
private theorem isGoodNoise_ae (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) :
    ∀ᵐ ξ ∂noiseMeasure, IsGoodNoise T h_inf ξ :=
  hilbert_gaussian_series_converges (factV T h_inf) (factV_summable T h_inf)
private theorem limUnder_partialSum_measurable
    (T : E →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H)
    (φ : E) :
    Measurable (fun ξ : NoiseSpace =>
      Filter.limUnder Filter.atTop (fun N => ∑ k ∈ Finset.range N,
        ξ k * coeff T h_inf k φ)) := by
  apply MeasureTheory.StronglyMeasurable.measurable
  apply MeasureTheory.StronglyMeasurable.limUnder
  intro N
  have : (fun ξ : NoiseSpace => ∑ k ∈ Finset.range N, ξ k * coeff T h_inf k φ) =
    ∑ k ∈ Finset.range N, (fun ξ => ξ k * coeff T h_inf k φ) := by
    ext ξ; simp [Finset.sum_apply]
  rw [this]
  apply Finset.stronglyMeasurable_sum
  intro k _
  exact ((measurable_pi_apply k).stronglyMeasurable).mul stronglyMeasurable_const
private theorem aemeasurable_seriesLimit (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) :
    AEMeasurable (seriesLimit T h_inf) noiseMeasure := by
  have h_null : noiseMeasure {ξ | ¬IsGoodNoise T h_inf ξ} = 0 :=
    ae_iff.mp (isGoodNoise_ae T h_inf)
  obtain ⟨N, hN_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null h_null
  set S := Nᶜ with hS_def
  have hS_meas : MeasurableSet S := hN_meas.compl
  have hS_sub : ∀ ξ ∈ S, IsGoodNoise T h_inf ξ := fun ξ hξ => by
    by_contra h; exact hξ (hN_sub h)
  have hS_null : noiseMeasure Sᶜ = 0 := by rwa [hS_def, compl_compl]
  let g : NoiseSpace → Configuration E := S.indicator (seriesLimit T h_inf)
  have hg_meas : @Measurable NoiseSpace (Configuration E) _ instMeasurableSpaceConfiguration g := by
    apply configuration_measurable_of_eval_measurable
    intro φ
    have h_eval : (fun ξ => g ξ φ) = S.indicator (fun ξ => seriesLimit T h_inf ξ φ) := by
      ext ξ; simp only [g, Set.indicator]; split_ifs <;> rfl
    rw [h_eval]
    have h_eq : S.indicator (fun ξ => seriesLimit T h_inf ξ φ) =
        S.indicator (fun ξ => Filter.limUnder Filter.atTop
          (fun N => ∑ k ∈ Finset.range N, ξ k * coeff T h_inf k φ)) := by
      ext ξ; simp only [Set.indicator]; split_ifs with h
      · have hgood := hS_sub ξ h
        show seriesLimitFun T h_inf ξ φ = _
        simp only [seriesLimitFun, if_pos hgood]
        exact ((hgood.scalar_summable φ).hasSum.tendsto_sum_nat).limUnder_eq.symm
      · rfl
    rw [h_eq]
    exact (limUnder_partialSum_measurable T h_inf φ).indicator hS_meas
  have hg_ae : seriesLimit T h_inf =ᵐ[noiseMeasure] g := by
    rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
    exact ⟨S, mem_ae_iff.mpr hS_null, fun ξ hξ => by simp [g, hξ]⟩
  exact ⟨g, hg_meas, hg_ae⟩
private noncomputable def hilbertEmbedding (hfin : FiniteDimensional ℝ H) : H →L[ℝ] ell2' := by
  haveI := hfin
  exact ∑ i : Fin (Module.finrank ℝ H),
    (innerSL ℝ ((stdOrthonormalBasis ℝ H) i)).smulRight (ell2_basis i.val)
omit [CompleteSpace H] [SeparableSpace H] in
private lemma hilbertEmbedding_apply (hfin : FiniteDimensional ℝ H) (x : H) :
    hilbertEmbedding hfin x = ∑ i : Fin (Module.finrank ℝ H),
      @inner ℝ H _ ((stdOrthonormalBasis ℝ H) i) x • ell2_basis i.val := by
  simp only [hilbertEmbedding, sum_apply,
             ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
omit [CompleteSpace H] [SeparableSpace H] in
private lemma hilbertEmbedding_inner (hfin : FiniteDimensional ℝ H) (x y : H) :
    @inner ℝ ell2' _ (hilbertEmbedding hfin x) (hilbertEmbedding hfin y) =
    @inner ℝ H _ x y := by
  haveI := hfin
  rw [hilbertEmbedding_apply, hilbertEmbedding_apply]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
             starRingEnd_apply, star_trivial]
  simp_rw [show ∀ (i j : Fin (Module.finrank ℝ H)),
      @inner ℝ ell2' _ (ell2_basis i.val) (ell2_basis j.val) =
      if i = j then 1 else 0 from fun i j => by
    rcases eq_or_ne i j with h | h
    · rw [if_pos h, h, real_inner_self_eq_norm_sq,
          ell2_basis_orthonormal.1 j.val, one_pow]
    · rw [if_neg h]; exact ell2_basis_orthonormal.2 (show i.val ≠ j.val from
        fun h' => h (Fin.ext h'))]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← (stdOrthonormalBasis ℝ H).repr.inner_map_map x y, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial,
             OrthonormalBasis.repr_apply_apply, mul_comm]
def measure (T : E →L[ℝ] H) :
    @Measure (Configuration E) instMeasurableSpaceConfiguration :=
  if hfin : FiniteDimensional ℝ H then
    @Measure.map NoiseSpace (Configuration E) _ instMeasurableSpaceConfiguration
      (seriesLimit ((hilbertEmbedding hfin).comp T) ell2_not_finiteDimensional) noiseMeasure
  else
    @Measure.map NoiseSpace (Configuration E) _ instMeasurableSpaceConfiguration
      (seriesLimit T hfin) noiseMeasure
instance measure_isProbability (T : E →L[ℝ] H) :
    @IsProbabilityMeasure (Configuration E) instMeasurableSpaceConfiguration
      (measure T) := by
  unfold measure; split_ifs with hfin
  · exact Measure.isProbabilityMeasure_map
      (aemeasurable_seriesLimit ((hilbertEmbedding hfin).comp T) ell2_not_finiteDimensional)
  · exact Measure.isProbabilityMeasure_map (aemeasurable_seriesLimit T hfin)
private theorem partialSum_tendsto (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) (f : E) :
    ∀ᵐ ξ ∂noiseMeasure, Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, ξ k * coeff T h_inf k f)
      Filter.atTop
      (nhds (seriesLimit T h_inf ξ f)) := by
  filter_upwards [isGoodNoise_ae T h_inf] with ξ hgood
  have hsummable := hgood.scalar_summable f
  have hlimit : (seriesLimit T h_inf ξ f) =
      ∑' n, ξ n * coeff T h_inf n f := by
    show seriesLimitFun T h_inf ξ f = _
    simp only [seriesLimitFun, if_pos hgood]
  rw [hlimit]
  exact hsummable.hasSum.tendsto_sum_nat
private theorem coord_projections_indep :
    iIndepFun (m := fun _ => inferInstance)
    (fun i (ξ : NoiseSpace) ↦ ξ i) noiseMeasure := by
  have h := @iIndepFun_infinitePi ℕ (fun _ => ℝ) (fun _ => inferInstance)
    (fun _ => ℝ) (fun _ => inferInstance) (fun _ => gaussianReal 0 1) _
    (fun _ => id) (fun _ => measurable_id)
  simp only [id_eq] at h
  exact h
private theorem noise_integral_factor (n : ℕ)
    (g : NoiseSpace → ℂ) (h : ℝ → ℂ)
    (hg : ∀ ξ ξ', (∀ k < n, ξ k = ξ' k) → g ξ = g ξ')
    (hg_meas : Measurable g)
    (hh_meas : Measurable h) :
    ∫ ξ, g ξ * h (ξ n) ∂noiseMeasure =
      (∫ ξ, g ξ ∂noiseMeasure) * (∫ x, h x ∂gaussianReal 0 1) := by
  have hdisj : Disjoint (Finset.range n) ({n} : Finset ℕ) := by
    rw [Finset.disjoint_left]; intro a ha hn
    simp only [Finset.mem_singleton] at hn
    simp only [Finset.mem_range] at ha; omega
  let X : NoiseSpace → (Finset.range n → ℝ) := fun ξ i => ξ i
  let Y : NoiseSpace → ℝ := fun ξ => ξ n
  have hX_meas : Measurable X := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hY_meas : Measurable Y := measurable_pi_apply n
  let Y' : NoiseSpace → ({n} : Finset ℕ) → ℝ := fun ξ i => ξ i
  have hindep' : IndepFun X Y' noiseMeasure :=
    coord_projections_indep.indepFun_finset (Finset.range n) {n} hdisj
      (fun _ => measurable_pi_apply _)
  have hindep : IndepFun X Y noiseMeasure := by
    have hY_eq : Y = (fun f => f ⟨n, Finset.mem_singleton_self n⟩) ∘ Y' := rfl
    rw [hY_eq]
    exact hindep'.comp measurable_id (measurable_pi_apply _)
  let extend_to_full : (Finset.range n → ℝ) → NoiseSpace :=
    fun f k => if hk : k < n then f ⟨k, Finset.mem_range.mpr hk⟩ else 0
  have hext_meas : Measurable extend_to_full := by
    apply measurable_pi_lambda; intro k; by_cases hk : k < n
    · simp only [extend_to_full, dif_pos hk]; exact measurable_pi_apply _
    · simp only [extend_to_full, dif_neg hk]; exact measurable_const
  let g' : (Finset.range n → ℝ) → ℂ := g ∘ extend_to_full
  have hg'_meas : Measurable g' := hg_meas.comp hext_meas
  have hg_factor : ∀ ξ, g ξ = g' (X ξ) := by
    intro ξ; simp only [g', Function.comp_apply]
    apply hg; intro k hk; simp only [extend_to_full, X, dif_pos hk]
  have heval : MeasurePreserving Y noiseMeasure (gaussianReal 0 1) :=
    measurePreserving_eval_infinitePi (fun _ => gaussianReal 0 1) n
  have hY_int : ∫ x, h x ∂gaussianReal 0 1 = ∫ ξ, h (Y ξ) ∂noiseMeasure := by
    simp only [← heval.map_eq]
    exact integral_map hY_meas.aemeasurable hh_meas.aestronglyMeasurable
  rw [hY_int]
  conv_lhs => arg 2; ext ξ; rw [hg_factor ξ]
  conv_rhs => arg 1; arg 2; ext ξ; rw [hg_factor ξ]
  conv_lhs => arg 2; ext ξ; rw [show h (ξ n) = h (Y ξ) from rfl]
  exact hindep.integral_fun_comp_mul_comp hX_meas.aemeasurable hY_meas.aemeasurable
    hg'_meas.aestronglyMeasurable hh_meas.aestronglyMeasurable
private theorem partial_sum_charFun (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) (f : E) (N : ℕ) :
    ∫ ξ, Complex.exp (Complex.I * ↑(∑ k ∈ Finset.range N,
      ξ k * coeff T h_inf k f)) ∂noiseMeasure =
    Complex.exp (-(1/2 : ℂ) * ∑ k ∈ Finset.range N,
      (coeff T h_inf k f : ℂ) ^ 2) := by
  simp_rw [Complex.ofReal_sum, Complex.ofReal_mul]
  conv_lhs => arg 2; ext ξ; rw [Finset.mul_sum]
  simp_rw [Complex.exp_sum]
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty, mul_zero,
      Complex.exp_zero, integral_const]
    have h : noiseMeasure.real Set.univ = 1 := by
      simp only [Measure.real, measure_univ, ENNReal.toReal_one]
    simp only [h, one_smul]
  | succ n ih =>
    simp only [Finset.range_add_one, Finset.prod_insert Finset.notMem_range_self,
               Finset.sum_insert Finset.notMem_range_self]
    conv_lhs => arg 2; ext xi; rw [mul_comm]
    let g := fun xi : NoiseSpace =>
      ∏ x ∈ Finset.range n, Complex.exp (Complex.I * (↑(xi x) * ↑(coeff T h_inf x f)))
    let h := fun x : ℝ => Complex.exp (Complex.I * (↑x * ↑(coeff T h_inf n f)))
    have hfactor : ∫ xi, g xi * h (xi n) ∂noiseMeasure =
        (∫ xi, g xi ∂noiseMeasure) * (∫ x, h x ∂gaussianReal 0 1) := by
      apply noise_integral_factor
      · intro xi xi' hcoords; simp only [g]
        apply Finset.prod_congr rfl
        intro k hk; rw [hcoords k (Finset.mem_range.mp hk)]
      · exact (by continuity : Continuous g).measurable
      · exact (by continuity : Continuous h).measurable
    rw [hfactor, ih]
    have hcf : ∫ x, h x ∂gaussianReal 0 1 =
        Complex.exp (-(1/2 : ℂ) * (coeff T h_inf n f : ℂ) ^ 2) := by
      simp only [h]
      have hcf' := charFun_gaussianReal (μ := 0) (v := 1) (coeff T h_inf n f)
      simp only [charFun_apply_real] at hcf'
      convert hcf' using 1
      · apply integral_congr_ae; filter_upwards with x; congr 1; ring
      · congr 1; simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
        norm_cast; push_cast; ring
    rw [hcf, ← Complex.exp_add]; congr 1; ring
private theorem charFun_noise_integral (T : E →L[ℝ] H)
    (h_inf : ¬ FiniteDimensional ℝ H) (f : E) :
    ∫ ξ : NoiseSpace, Complex.exp (Complex.I * ↑(seriesLimit T h_inf ξ f)) ∂noiseMeasure =
    Complex.exp (-(1/2 : ℂ) * ↑(@inner ℝ H _ (T f) (T f))) := by
  have hparseval : (@inner ℝ H _ (T f) (T f) : ℂ) =
      ∑' n, (coeff T h_inf n f : ℂ) ^ 2 := by
    have h := coeff_parseval T h_inf f
    rw [← real_inner_self_eq_norm_sq] at h
    simp only [← Complex.ofReal_pow] at h ⊢
    rw [← h]; simp only [Complex.ofReal_tsum]
  rw [hparseval]
  have hsummable : Summable (fun n => (coeff T h_inf n f : ℂ) ^ 2) := by
    have hr := coeff_sq_summable T h_inf f
    simp only [← Complex.ofReal_pow]
    exact Complex.summable_ofReal.mpr hr
  have hcf_limit : Filter.Tendsto
      (fun N => Complex.exp (-(1/2 : ℂ) * ∑ k ∈ Finset.range N,
        (coeff T h_inf k f : ℂ) ^ 2))
      Filter.atTop
      (nhds (Complex.exp (-(1/2 : ℂ) * ∑' n, (coeff T h_inf n f : ℂ) ^ 2))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    apply Filter.Tendsto.const_mul
    exact hsummable.hasSum.tendsto_sum_nat
  have hpartial : ∀ N, ∫ ξ, Complex.exp (Complex.I *
      ↑(∑ k ∈ Finset.range N, ξ k * coeff T h_inf k f)) ∂noiseMeasure =
      Complex.exp (-(1/2 : ℂ) * ∑ k ∈ Finset.range N,
        (coeff T h_inf k f : ℂ) ^ 2) :=
    fun N => partial_sum_charFun T h_inf f N
  have hdct : Filter.Tendsto
      (fun N => ∫ ξ, Complex.exp (Complex.I *
        ↑(∑ k ∈ Finset.range N, ξ k * coeff T h_inf k f)) ∂noiseMeasure)
      Filter.atTop
      (nhds (∫ ξ, Complex.exp (Complex.I * ↑(seriesLimit T h_inf ξ f)) ∂noiseMeasure)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro N; apply Continuous.aestronglyMeasurable; continuity
    · exact integrable_const 1
    · intro N; filter_upwards with ξ
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [partialSum_tendsto T h_inf f] with ξ htends
      apply Complex.continuous_exp.continuousAt.tendsto.comp
      apply Filter.Tendsto.const_mul
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp htends
  exact tendsto_nhds_unique hdct
    (Filter.Tendsto.congr (fun N => (hpartial N).symm) hcf_limit)
theorem charFun (T : E →L[ℝ] H) (f : E) :
    ∫ ω : Configuration E,
      Complex.exp (Complex.I * ↑(ω f)) ∂(measure T) =
    Complex.exp (-(1/2 : ℂ) * ↑(@inner ℝ H _ (T f) (T f))) := by
  have hmeas_integrand : ∀ (μ : @Measure (Configuration E) instMeasurableSpaceConfiguration),
      AEStronglyMeasurable (fun ω : Configuration E =>
        Complex.exp (Complex.I * ↑(ω f))) μ :=
    fun _ => (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (configuration_eval_measurable f)))).aestronglyMeasurable
  unfold measure
  by_cases hfin : FiniteDimensional ℝ H
  ·
    rw [dif_pos hfin]
    rw [integral_map
      (aemeasurable_seriesLimit ((hilbertEmbedding hfin).comp T) ell2_not_finiteDimensional)
      (hmeas_integrand _)]
    have h := charFun_noise_integral ((hilbertEmbedding hfin).comp T)
      ell2_not_finiteDimensional f
    simp only [ContinuousLinearMap.comp_apply] at h
    rwa [hilbertEmbedding_inner] at h
  ·
    rw [dif_neg hfin]
    rw [integral_map (aemeasurable_seriesLimit T hfin) (hmeas_integrand _)]
    exact charFun_noise_integral T hfin f
theorem measurable_forgetStrong :
    @Measurable (StrongDual ℝ E) (Configuration E) (borel _)
      instMeasurableSpaceConfiguration StrongDual.toWeakDual := by
  letI : MeasurableSpace (StrongDual ℝ E) := borel _
  letI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  exact configuration_measurable_of_eval_measurable _ fun f =>
    (continuous_eval_const f : Continuous (fun ω : StrongDual ℝ E => ω f)).measurable
private theorem exists_strong_lift_series (T : E →L[ℝ] H) (hi : ¬ FiniteDimensional ℝ H) :
    ∃ μ : @Measure (StrongDual ℝ E) (borel _),
      @IsProbabilityMeasure _ (borel _) μ ∧
      @Measure.map _ (Configuration E) (borel _) instMeasurableSpaceConfiguration
        StrongDual.toWeakDual μ = noiseMeasure.map (seriesLimit T hi) := by
  letI : MeasurableSpace (StrongDual ℝ E) := borel _
  letI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  let realisation (ξ : NoiseSpace) : StrongDual ℝ E :=
    (innerSL ℝ (∑' n, ξ n • factV T hi n)).comp (factJ T hi)
  have hm : Measurable realisation := StrongGaussianLaw.measurable_series (factJ T hi) (factV T hi)
  refine ⟨noiseMeasure.map realisation, Measure.isProbabilityMeasure_map hm.aemeasurable, ?_⟩
  rw [Measure.map_map measurable_forgetStrong hm]
  apply Measure.map_congr
  filter_upwards [isGoodNoise_ae T hi] with ξ hgood
  apply ContinuousLinearMap.ext
  intro f
  change (innerSL ℝ (∑' n, ξ n • factV T hi n)).comp (factJ T hi) f = seriesLimitFun T hi ξ f
  rw [StrongGaussianLaw.eval_series hgood, seriesLimitFun, if_pos hgood]
  exact tsum_congr fun n => congrArg (ξ n * ·) (factV_inner_eq T hi f n).symm
theorem exists_strong_lift (T : E →L[ℝ] H) :
    ∃ μ : @Measure (StrongDual ℝ E) (borel _),
      @IsProbabilityMeasure _ (borel _) μ ∧
      @Measure.map _ (Configuration E) (borel _) instMeasurableSpaceConfiguration
        StrongDual.toWeakDual μ = measure T := by
  unfold measure
  split_ifs with hfin
  · exact exists_strong_lift_series ((hilbertEmbedding hfin).comp T) ell2_not_finiteDimensional
  · exact exists_strong_lift_series T hfin
end GaussianField
end
end

-- GaussianField.Properties
section
noncomputable section
namespace GaussianField
open MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped BigOperators NNReal
open Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : E →L[ℝ] H)
theorem pairing_is_gaussian (f : E) :
    (measure T).map (fun ω : Configuration E => ω f) =
      gaussianReal 0 (@inner ℝ H _ (T f) (T f) : ℝ).toNNReal := by
  haveI : IsProbabilityMeasure ((measure T).map
      (fun ω : Configuration E => ω f)) :=
    Measure.isProbabilityMeasure_map (configuration_eval_measurable f).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real]
  have hmeas_integrand : AEStronglyMeasurable (fun x : ℝ => Complex.exp (↑t * ↑x * I))
      ((measure T).map (fun ω : Configuration E => ω f)) :=
    (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
  rw [integral_map (configuration_eval_measurable f).aemeasurable hmeas_integrand]
  have h_char := charFun T (t • f)
  simp only [map_smul, smul_eq_mul] at h_char
  simp_rw [show ∀ (ω : Configuration E),
      cexp (↑t * ↑(ω f) * I) = cexp (I * ↑(t * ω f))
    from fun ω => by congr 1; push_cast; ring]
  rw [h_char]
  rw [charFun_gaussianReal]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [Real.coe_toNNReal _ real_inner_self_nonneg]
  push_cast; ring
theorem pairing_memLp (f : E) (p : ℝ≥0) :
    MemLp (fun ω : Configuration E => ω f) p (measure T) := by
  have h_gauss := pairing_is_gaussian T f
  have h_memLp : MemLp id p
      (gaussianReal 0 (@inner ℝ H _ (T f) (T f) : ℝ).toNNReal) :=
    memLp_id_gaussianReal p
  rw [← h_gauss] at h_memLp
  rwa [memLp_map_measure_iff h_memLp.aestronglyMeasurable
    (configuration_eval_measurable f).aemeasurable] at h_memLp
theorem pairing_integrable (f : E) :
    Integrable (fun ω : Configuration E => ω f)
      (measure T) :=
  memLp_one_iff_integrable.mp (pairing_memLp T f 1)
theorem measure_centered (f : E) :
    ∫ ω : Configuration E, ω f ∂(measure T) = 0 := by
  have h_gauss := pairing_is_gaussian T f
  have h_map := integral_map (configuration_eval_measurable f).aemeasurable
    (measurable_id.aestronglyMeasurable
      (μ := (measure T).map (fun ω : Configuration E => ω f)))
  simp only [id] at h_map
  rw [h_map.symm, h_gauss, integral_id_gaussianReal]
theorem second_moment_eq_covariance (f : E) :
    ∫ ω : Configuration E, (ω f) ^ 2 ∂(measure T) =
      @inner ℝ H _ (T f) (T f) := by
  have h_gauss := pairing_is_gaussian T f
  set σ := (@inner ℝ H _ (T f) (T f) : ℝ).toNNReal with hσ_def
  have h_var : Var[fun ω : Configuration E => ω f; measure T] =
      ∫ ω, (ω f) ^ 2 ∂(measure T) :=
    variance_of_integral_eq_zero
      (configuration_eval_measurable f).aemeasurable
      (measure_centered T f)
  have h_var2 : Var[fun ω : Configuration E => ω f; measure T] = σ := by
    have h : Var[fun x : ℝ => x;
        (measure T).map (fun ω : Configuration E => ω f)] =
        Var[fun ω : Configuration E => ω f; measure T] :=
      variance_map aemeasurable_id (configuration_eval_measurable f).aemeasurable
    rw [← h, h_gauss, variance_fun_id_gaussianReal]
  rw [← h_var, h_var2, hσ_def]
  exact Real.coe_toNNReal _ real_inner_self_nonneg
theorem pairing_product_integrable (f g : E) :
    Integrable (fun ω : Configuration E => ω f * ω g)
      (measure T) := by
  have hf : MemLp (fun ω : Configuration E => ω f) 2 (measure T) := by
    exact_mod_cast pairing_memLp T f 2
  have hg : MemLp (fun ω : Configuration E => ω g) 2 (measure T) := by
    exact_mod_cast pairing_memLp T g 2
  exact hf.integrable_mul hg
theorem cross_moment_eq_covariance (f g : E) :
    ∫ ω : Configuration E, (ω f) * (ω g) ∂(measure T) =
      @inner ℝ H _ (T f) (T g) := by
  have h_polar : @inner ℝ H _ (T f) (T g) =
      (1/4) * (@inner ℝ H _ (T (f + g)) (T (f + g)) -
               @inner ℝ H _ (T (f - g)) (T (f - g))) := by
    simp only [map_add, map_sub]
    rw [show @inner ℝ H _ (T f + T g) (T f + T g) =
        @inner ℝ H _ (T f) (T f) + 2 * @inner ℝ H _ (T f) (T g) +
        @inner ℝ H _ (T g) (T g) from by
      rw [inner_add_left, inner_add_right, inner_add_right,
          real_inner_comm (T g) (T f)]; ring]
    rw [show @inner ℝ H _ (T f - T g) (T f - T g) =
        @inner ℝ H _ (T f) (T f) - 2 * @inner ℝ H _ (T f) (T g) +
        @inner ℝ H _ (T g) (T g) from by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
          real_inner_comm (T g) (T f)]; ring]
    ring
  have h_int_polar : ∫ ω : Configuration E, ω f * ω g ∂measure T =
      (1/4) * (∫ ω, (ω (f + g)) ^ 2 ∂measure T -
               ∫ ω, (ω (f - g)) ^ 2 ∂measure T) := by
    have hfg_int := pairing_product_integrable T f g
    have hp : ∀ ω : Configuration E,
        (ω (f + g)) ^ 2 - (ω (f - g)) ^ 2 = 4 * (ω f * ω g) := fun ω => by
      rw [show ω (f + g) = ω f + ω g from ω.map_add f g,
          show ω (f - g) = ω f - ω g from ω.map_sub f g]; ring
    have hfg_sq := (pairing_memLp T (f + g) 2).integrable_sq
    have hfmg_sq := (pairing_memLp T (f - g) 2).integrable_sq
    rw [← integral_sub hfg_sq hfmg_sq]
    simp_rw [hp]
    rw [integral_const_mul]
    ring
  rw [h_int_polar, h_polar]
  congr 1
  rw [second_moment_eq_covariance T (f + g),
      second_moment_eq_covariance T (f - g)]
end GaussianField
end
end

-- StrongMarginals
section
open MeasureTheory ProbabilityTheory TopologicalSpace
open GaussianField

noncomputable section

namespace MO201997

variable {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]

/-- The full Borel law on the strong dual realizes the Hilbert covariance on every pair
of test functions, with centered one-dimensional Gaussian marginals. -/
theorem strongGaussian_exists (T : E →L[ℝ] H) :
    ∃ μ : @Measure (StrongDual ℝ E) (borel _),
      letI : MeasurableSpace (StrongDual ℝ E) := borel _
      IsProbabilityMeasure μ ∧
      (∀ f : E, HasLaw (fun φ : StrongDual ℝ E => φ f)
        (gaussianReal 0 (inner ℝ (T f) (T f)).toNNReal) μ) ∧
      ∀ f g : E, (∫ φ : StrongDual ℝ E, φ f * φ g ∂μ) = inner ℝ (T f) (T g) := by
  letI : MeasurableSpace (StrongDual ℝ E) := borel _
  letI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  obtain ⟨μ, hprob, hmap⟩ := exists_strong_lift T
  have hm : @Measurable (StrongDual ℝ E) (Configuration E) (borel _)
      instMeasurableSpaceConfiguration StrongDual.toWeakDual := measurable_forgetStrong
  refine ⟨μ, hprob, ?_, ?_⟩
  · intro f
    have hw := configuration_eval_measurable (E := E) f
    refine ⟨(hw.comp hm).aemeasurable, ?_⟩
    calc
      μ.map (fun φ : StrongDual ℝ E => φ f) =
          (μ.map StrongDual.toWeakDual).map (fun ω : Configuration E => ω f) :=
        (Measure.map_map hw hm).symm
      _ = _ := by rw [hmap, pairing_is_gaussian]
  · intro f g
    have hprod := (configuration_eval_measurable (E := E) f).mul
      (configuration_eval_measurable g)
    have hi := integral_map (μ := μ) hm.aemeasurable hprod.aestronglyMeasurable
    calc
      (∫ φ : StrongDual ℝ E, φ f * φ g ∂μ) =
        ∫ ω : Configuration E, ω f * ω g ∂(μ.map StrongDual.toWeakDual) := hi.symm
      _ = _ := by rw [hmap, cross_moment_eq_covariance]

end MO201997
end
end

-- CovarianceHilbert
section
open Filter Topology TopologicalSpace UniformSpace

namespace MO201997

noncomputable section

universe u
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- A copy of the test space carrying its covariance seminorm. -/
structure CovarianceSpace (_Q : PreInnerProductSpace.Core ℝ E) where
  val : E

namespace CovarianceSpace

variable (Q : PreInnerProductSpace.Core ℝ E)

def equiv : CovarianceSpace Q ≃ E := ⟨val, mk, fun _ => rfl, fun _ => rfl⟩
instance : AddCommGroup (CovarianceSpace Q) := (equiv Q).addCommGroup
instance : Module ℝ (CovarianceSpace Q) := (equiv Q).module ℝ
instance core : PreInnerProductSpace.Core ℝ (CovarianceSpace Q) where
  inner x y := Q.inner x.val y.val
  conj_inner_symm x y := Q.conj_inner_symm x.val y.val
  re_inner_nonneg x := Q.re_inner_nonneg x.val
  add_left x y z := Q.add_left x.val y.val z.val
  smul_left x y r := Q.smul_left x.val y.val r
instance : SeminormedAddCommGroup (CovarianceSpace Q) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ (CovarianceSpace Q) := InnerProductSpace.ofCore (core Q)

def inclusion : E →ₗ[ℝ] CovarianceSpace Q := ((equiv Q).linearEquiv ℝ).symm.toLinearMap

theorem norm_inclusion (x : E) : ‖inclusion Q x‖ = Real.sqrt (Q.inner x x) := rfl

variable [TopologicalSpace E] [IsTopologicalAddGroup E]

def toSeminormed (hc : ContinuousAt (fun x => Q.inner x x) 0) :
    E →L[ℝ] CovarianceSpace Q where
  toLinearMap := inclusion Q
  cont := by
    apply continuous_of_continuousAt_zero (inclusion Q)
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inclusion]
    have h0 : Q.inner 0 0 = 0 := by
      have h := Q.add_left 0 0 0
      simpa using h
    simpa [h0, Function.comp_def] using
      (Real.continuous_sqrt.continuousAt (x := Q.inner 0 0)).tendsto.comp hc.tendsto

/-- The completion automatically identifies the radical of a semidefinite covariance. -/
abbrev Hilbert := Completion (CovarianceSpace Q)

def toHilbert (hc : ContinuousAt (fun x => Q.inner x x) 0) :
    E →L[ℝ] Hilbert Q :=
  (UniformSpace.Completion.toComplL : CovarianceSpace Q →L[ℝ] Hilbert Q).comp
    (toSeminormed Q hc)

theorem toHilbert_inner (hc : ContinuousAt (fun x => Q.inner x x) 0) (x y : E) :
    inner ℝ (toHilbert Q hc x) (toHilbert Q hc y) = Q.inner x y :=
  UniformSpace.Completion.inner_coe (𝕜 := ℝ) _ _

theorem separableHilbert [SeparableSpace E] (hc : ContinuousAt (fun x => Q.inner x x) 0) :
    SeparableSpace (Hilbert Q) := by
  have hd : DenseRange (toHilbert Q hc) := UniformSpace.Completion.denseRange_coe.comp
    ((equiv Q).symm.surjective.denseRange) (UniformSpace.Completion.continuous_coe _)
  exact hd.separableSpace (toHilbert Q hc).continuous

end CovarianceSpace
end
end MO201997
end

-- RieszForm
section
open MeasureTheory Filter OMA.S_mo_201997
open scoped Topology

namespace MO201997

theorem riesz_smul_left (a c : ℝ) (f g : Test 5) :
    rieszPair a (c • f) g = c * rieszPair a f g := by
  unfold rieszPair
  simp only [smul_apply, smul_eq_mul, mul_assoc]
  simp_rw [integral_const_mul]

theorem diagonal_continuousAt_zero (C : ℝ)
    (h : ∀ f : Test 5, ‖rieszPair 4 f f‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 f * C + ‖f.toLp 1 volume‖) * ‖f.toLp 1 volume‖) :
    ContinuousAt (fun f : Test 5 => rieszPair 4 f f) 0 := by
  have hs : Continuous (SchwartzMap.seminorm ℝ 0 0 : Test 5 → ℝ) :=
    (schwartz_withSeminorms ℝ (Space 5) ℝ).continuous_seminorm (0, 0)
  have hl : Continuous (fun f : Test 5 => ‖f.toLp 1 volume‖) :=
    SchwartzMap.continuous_toLp.norm
  have boundCont : Continuous (fun f : Test 5 => (SchwartzMap.seminorm ℝ 0 0 f * C + ‖f.toLp 1 volume‖) * ‖f.toLp 1 volume‖) :=
    ((hs.mul (continuous_const (y := C))).add hl).mul hl
  have hc := boundCont.continuousAt (x := 0)
  change Tendsto _ (𝓝 0) (𝓝 (rieszPair 4 0 0))
  have hz : rieszPair 4 (0 : Test 5) 0 = 0 := by simp [rieszPair]
  rw [hz]
  apply squeeze_zero_norm h
  simpa [ContinuousAt, SchwartzMap.toLp] using hc

end MO201997
end

-- RieszInput
section
open MeasureTheory Set Filter
open OMA.S_mo_201997

namespace RieszInput

noncomputable section

abbrev E := Space 5
abbrev T := Test 5

private def nearKernel (a : ℝ) (z : E) : ℝ :=
  (Metric.ball (0:E) 1).indicator (fun v : E => ‖v‖ ^ (-a)) z

private theorem integrable_near {a : ℝ} (ha : a < 5) : Integrable (nearKernel a) := by
  apply (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := a) (by simp) (by simpa using ha) ?_ ?_
  · filter_upwards with x
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  · exact (measurable_id.norm.pow_const _).aestronglyMeasurable

abbrev integrand (a : ℝ) (f g : T) (p : E × E) := f p.1 * g p.2 * ‖p.1 - p.2‖ ^ (-a)

private def majorant (a : ℝ) (f g : T) (p : E × E) : ℝ :=
  ((SchwartzMap.seminorm ℝ 0 0) f) * (nearKernel a (p.1-p.2) * ‖g p.2‖) + ‖f p.1‖ * ‖g p.2‖

private theorem integrable_majorant {a : ℝ} (ha : a < 5) (f g : T) :
    Integrable (majorant a f g) (volume.prod volume) := by
  have hnear := ((integrable_near ha).mul_prod (g.integrable (μ := volume)).norm)
  have hnear' := (measurePreserving_sub_prod (volume : Measure E) volume).integrable_comp
    hnear.aestronglyMeasurable |>.mpr hnear
  have hfar := (f.integrable (μ := volume)).norm.mul_prod (g.integrable (μ := volume)).norm
  exact (hnear'.const_mul _).add hfar

private theorem norm_integrand_le_majorant {a : ℝ} (h0 : 0 ≤ a) (f g : T) (p : E × E) :
    ‖integrand a f g p‖ ≤ majorant a f g p := by
    let M := (SchwartzMap.seminorm ℝ 0 0) f
    change ‖f p.1 * g p.2 * ‖p.1 - p.2‖ ^ (-a)‖ ≤
      M * (nearKernel a (p.1 - p.2) * ‖g p.2‖) + ‖f p.1‖ * ‖g p.2‖
    simp only [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hz : p.1 - p.2 ∈ Metric.ball (0:E) 1
    · rw [nearKernel, indicator_of_mem hz]
      have hf := f.norm_le_seminorm ℝ p.1
      calc
        _ ≤ M * ‖g p.2‖ * ‖p.1 - p.2‖ ^ (-a) := by gcongr
        _ ≤ _ := by rw [mul_right_comm M, mul_assoc]; exact le_add_of_nonneg_right (by positivity)
    · rw [nearKernel, indicator_of_notMem hz, zero_mul, mul_zero, zero_add]
      apply mul_le_of_le_one_right (by positivity)
      apply Real.rpow_le_one_of_one_le_of_nonpos _ (neg_nonpos.mpr h0)
      simpa [Metric.mem_ball, dist_zero_right] using hz

theorem integrable_integrand {a : ℝ} (h0 : 0 ≤ a) (ha : a < 5) (f g : T) :
    Integrable (integrand a f g) (volume.prod volume) := by
  apply (integrable_majorant ha f g).mono' _ (.of_forall (norm_integrand_le_majorant h0 f g))
  unfold integrand
  exact ((f.continuous.measurable.comp measurable_fst).mul
    (g.continuous.measurable.comp measurable_snd) |>.mul
    ((measurable_fst.sub measurable_snd).norm.pow_const _)).aestronglyMeasurable

theorem integral_product {a : ℝ} (h0 : 0 ≤ a) (ha : a < 5) (f g : T) :
    rieszPair a f g = ∫ p : E × E, integrand a f g p ∂volume.prod volume := by
  exact (integral_prod _ (integrable_integrand h0 ha f g)).symm

def nearMass : ℝ := ∫ z : E, nearKernel 4 z

theorem nearMass_nonneg : 0 ≤ nearMass := by
  apply integral_nonneg
  intro z
  exact indicator_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg x) _) _

theorem norm_rieszPair_le (f g : T) : ‖rieszPair 4 f g‖ ≤
    ((SchwartzMap.seminorm ℝ 0 0) f * nearMass + ‖f.toLp 1 volume‖) * ‖g.toLp 1 volume‖ := by
  rw [integral_product (by norm_num) (by norm_num)]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono (integrable_integrand (by norm_num) (by norm_num) f g).norm
    (integrable_majorant (by norm_num) f g) (norm_integrand_le_majorant (by norm_num) f g)).trans
  apply le_of_eq
  have hnear := ((integrable_near (a := 4) (by norm_num)).mul_prod (g.integrable (μ := volume)).norm)
  have hpres := measurePreserving_sub_prod (volume : Measure E) volume
  have hnear' := hpres.integrable_comp hnear.aestronglyMeasurable |>.mpr hnear
  have hfar := (f.integrable (μ := volume)).norm.mul_prod (g.integrable (μ := volume)).norm
  change (∫ p : E × E, (SchwartzMap.seminorm ℝ 0 0) f * (nearKernel 4 (p.1-p.2) * ‖g p.2‖) +
    ‖f p.1‖ * ‖g p.2‖ ∂volume.prod volume) = _
  change Integrable (fun p : E × E => nearKernel 4 (p.1 - p.2) * ‖g p.2‖) (volume.prod volume) at hnear'
  rw [integral_add (hnear'.const_mul ((SchwartzMap.seminorm ℝ 0 0) f)) hfar, integral_const_mul, integral_prod_mul (fun x => ‖f x‖) (fun y => ‖g y‖)]
  have hshift : (∫ p : E × E, nearKernel 4 (p.1-p.2) * ‖g p.2‖ ∂volume.prod volume) =
      ∫ p : E × E, nearKernel 4 p.1 * ‖g p.2‖ ∂volume.prod volume := by
    rw [integral_prod_symm _ hnear', integral_prod_symm _ hnear]
    simp_rw [integral_mul_const, integral_sub_right_eq_self]
  rw [hshift, integral_prod_mul (nearKernel 4) (fun y => ‖g y‖), SchwartzMap.norm_toLp_one, SchwartzMap.norm_toLp_one]
  unfold nearMass
  ring

theorem rieszPair_comm (f g : T) : rieszPair 4 f g = rieszPair 4 g f := by
  rw [integral_product (by norm_num) (by norm_num),
    integral_product (by norm_num) (by norm_num)]
  rw [← integral_prod_swap (integrand 4 g f)]
  congr 1
  funext p
  simp [integrand, mul_comm (f p.1), norm_sub_rev]

theorem rieszPair_add_left (f g k : T) : rieszPair 4 (f+g) k = rieszPair 4 f k + rieszPair 4 g k := by
  simp only [integral_product (a := (4:ℝ)) (by norm_num) (by norm_num)]
  rw [← integral_add (integrable_integrand (a := 4) (by norm_num) (by norm_num) f k)
    (integrable_integrand (a := 4) (by norm_num) (by norm_num) g k)]
  congr 1
  funext p
  simp [integrand, add_mul]

theorem rieszPair_add_right (f g k : T) : rieszPair 4 f (g+k) = rieszPair 4 f g + rieszPair 4 f k := by
  rw [rieszPair_comm f, rieszPair_add_left, rieszPair_comm g, rieszPair_comm k]

end
end RieszInput
end

-- RieszHeat
section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace

namespace RieszInput
noncomputable section
abbrev HeatSpace := EuclideanSpace ℝ (Fin 5)

def heat (t : ℝ) (x : HeatSpace) := Real.exp (-t * ‖x‖ ^ 2)

lemma heat_pos (t : ℝ) (x : HeatSpace) : 0 < heat t x := Real.exp_pos _

lemma heat_le_one {t : ℝ} (ht : 0 ≤ t) (x : HeatSpace) : heat t x ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))

lemma heat_continuous : Continuous (fun z : ℝ × HeatSpace => heat z.1 z.2) := by
  unfold heat
  fun_prop

def heatNorm (t : ℝ) := ∫ z : HeatSpace, heat (4*t) z

lemma heatNorm_pos {t : ℝ} (ht : 0 < t) : 0 < heatNorm t := by
  unfold heatNorm heat
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  positivity

lemma heat_integrable {t : ℝ} (ht : 0 < t) : Integrable (heat t) := by
  by_contra hn
  have hi := integral_undef (μ := volume) hn
  apply (ne_of_gt (a := ∫ x, heat t x) _ ) hi
  unfold heat
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  positivity

def halfCenter (x y : HeatSpace) := (1/2:ℝ) • (x+y)

lemma heat_square (t : ℝ) (x y u : HeatSpace) :
    heat (2*t) (x-u) * heat (2*t) (y-u) =
      heat t (x-y) * heat (4*t) (halfCenter x y - u) := by
  unfold heat halfCenter
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, norm_add_sq_real,
    real_inner_smul_left, inner_add_left, mul_pow]
  norm_num
  ring

lemma integral_heat_square (t : ℝ) (x y : HeatSpace) :
    (∫ u : HeatSpace, heat (2*t) (x-u) * heat (2*t) (y-u)) = heatNorm t * heat t (x-y) := by
  simp_rw [heat_square]
  rw [integral_const_mul, integral_sub_left_eq_self]
  exact mul_comm _ _

lemma heat_quadratic_nonneg {t : ℝ} (ht : 0 < t) {f : HeatSpace → ℝ}
    (hf : Integrable f) (hm : Measurable f) :
    0 ≤ ∫ p : HeatSpace × HeatSpace, f p.1 * f p.2 * heat t (p.1 - p.2) := by
  let H := fun (p : HeatSpace × HeatSpace) (u : HeatSpace) =>
    (f p.1 * f p.2) * (heat (2*t) (p.1-u) * heat (2*t) (p.2-u))
  have hmeas : Measurable (Function.uncurry H) := by
    unfold H Function.uncurry heat
    fun_prop
  have hfprod := hf.norm.mul_prod hf.norm
  have hinner (p : HeatSpace × HeatSpace) :
      Integrable (fun u => heat (2*t) (p.1-u) * heat (2*t) (p.2-u)) := by
    simp_rw [heat_square]
    exact ((heat_integrable (t := 4*t) (by positivity)).comp_sub_left _).const_mul _
  have hnorm (p : HeatSpace × HeatSpace) :
      (∫ u : HeatSpace, ‖H p u‖) = heatNorm t * (‖f p.1‖ * ‖f p.2‖ * heat t (p.1-p.2)) := by
    simp only [H, norm_mul, Real.norm_of_nonneg (heat_pos _ _).le]
    rw [integral_const_mul, integral_heat_square]
    ring
  have hint : Integrable (Function.uncurry H) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · exact .of_forall fun p => (hinner p).const_mul (f p.1 * f p.2)
    · simp_rw [Function.uncurry_apply_pair, hnorm]
      apply Integrable.const_mul
      apply hfprod.mono'
      · exact (((hm.comp measurable_fst).norm.mul (hm.comp measurable_snd).norm).mul
          (heat_continuous.measurable.comp (measurable_const.prodMk
            (measurable_fst.sub measurable_snd)))).aestronglyMeasurable
      · filter_upwards with p
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (heat_pos _ _).le)]
        exact mul_le_of_le_one_right (by positivity) (heat_le_one ht.le _)
  suffices h : 0 ≤ heatNorm t * ∫ p : HeatSpace × HeatSpace, f p.1 * f p.2 * heat t (p.1 - p.2) by
    exact nonneg_of_mul_nonneg_right h (heatNorm_pos ht)
  rw [← integral_const_mul]
  have eqn (p : HeatSpace × HeatSpace) :
      heatNorm t * (f p.1 * f p.2 * heat t (p.1-p.2)) = ∫ u, H p u := by
    simp only [H, integral_const_mul, integral_heat_square]
    ring
  simp_rw [eqn]
  rw [integral_integral_swap hint]
  apply integral_nonneg
  intro u
  have hprod : (fun p : HeatSpace × HeatSpace => H p u) =
      (fun p => (f p.1 * heat (2*t) (p.1-u)) * (f p.2 * heat (2*t) (p.2-u))) := by
    ext p
    simp only [H]
    ring
  change 0 ≤ ∫ p : HeatSpace × HeatSpace, H p u
  rw [hprod]
  change 0 ≤ ∫ p : HeatSpace × HeatSpace, _ ∂volume.prod volume
  rw [integral_prod_mul (fun x => f x * heat (2*t) (x-u)) (fun x => f x * heat (2*t) (x-u))]
  exact mul_self_nonneg _

end
end RieszInput
end

-- RieszPositive
section
open OMA.S_mo_201997 MeasureTheory Filter Set

namespace RieszInput

private theorem laplace_repr {z : E} (hz : z ≠ 0) :
    (∫ t : ℝ in Ioi 0, t * heat t z) = ‖z‖ ^ (-(4:ℝ)) := by
  have hn := norm_pos_iff.mpr hz
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := ‖z‖^2) (by norm_num) (by positivity)
  norm_num [heat, mul_comm, ← neg_mul] at hg ⊢
  convert hg using 1 <;> try ring

private theorem laplace_int {z : E} (hz : z ≠ 0) :
    IntegrableOn (fun t : ℝ => t * heat t z) (Ioi 0) := by
  have hn := norm_pos_iff.mpr hz
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := ‖z‖^2)
    (by norm_num) (by norm_num) (by positivity)
  simpa [heat, mul_comm, neg_mul] using hg

private lemma offDiag : ∀ᵐ p : E × E ∂volume.prod volume, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
  filter_upwards with x
  exact (volume.ae_ne x).mono fun _ h => h.symm

theorem rieszPair_nonneg (f : T) : 0 ≤ rieszPair 4 f f := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let μ : Measure (E × E) := volume.prod volume
  let F := fun (p : E × E) (t : ℝ) => (f p.1 * f p.2) * (t * heat t (p.1-p.2))
  have hmeas : Measurable (Function.uncurry F) := by
    unfold F Function.uncurry heat
    fun_prop (disch := exact f.continuous.measurable)
  have hnorm {p : E × E} (hp : p.1 ≠ p.2) :
      (∫ t, ‖F p t‖ ∂ν) = ‖integrand 4 f f p‖ := by
    have hn : ∀ᵐ t ∂ν, 0 < t := self_mem_ae_restrict measurableSet_Ioi
    have he : ∀ᵐ t ∂ν, ‖F p t‖ = ‖f p.1 * f p.2‖ * (t * heat t (p.1-p.2)) := by
      filter_upwards [hn] with t ht
      rw [show F p t = _ from rfl, norm_mul, Real.norm_of_nonneg (mul_nonneg ht.le (heat_pos _ _).le)]
    rw [integral_congr_ae he, integral_const_mul, laplace_repr (sub_ne_zero.mpr hp)]
    simp [integrand, norm_mul]
  have hint : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [offDiag] with p hp
      exact (laplace_int (sub_ne_zero.mpr hp)).const_mul (f p.1 * f p.2)
    · apply (integrable_integrand (a := 4) (by norm_num) (by norm_num) f f).norm.congr
      filter_upwards [offDiag] with p hp
      exact (hnorm hp).symm
  rw [integral_product (by norm_num) (by norm_num)]
  have he : (fun p : E × E => integrand 4 f f p) =ᵐ[μ] (fun p => ∫ t, F p t ∂ν) := by
    filter_upwards [offDiag] with p hp
    simp only [F, integral_const_mul, ν, laplace_repr (sub_ne_zero.mpr hp), integrand]
  rw [integral_congr_ae he, integral_integral_swap hint]
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  have eqt : (fun p : E × E => F p t) = fun p => t * (f p.1 * f p.2 * heat t (p.1-p.2)) := by
    ext p
    simp only [F]
    ring
  change 0 ≤ ∫ p, F p t ∂μ
  rw [eqt, integral_const_mul]
  exact mul_nonneg (le_of_lt ht) (heat_quadratic_nonneg ht f.integrable f.continuous.measurable)

end RieszInput
end

-- Locality
section
open MeasureTheory ProbabilityTheory Laplacian LineDeriv
open OMA.S_mo_201997

namespace MO201997

/-- Differentiation preserves the part of space observed by a test. -/
theorem tsupport_laplacian_subset {d : ℕ} (f : Test d) :
    tsupport (Δ f : Test d) ⊆ tsupport f := by
  classical
  apply closure_minimal _ (isClosed_tsupport _)
  apply Function.support_subset_iff'.2
  intro x hx
  rw [SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis ℝ (Space d)),
    sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply image_eq_zero_of_notMem_tsupport
  intro hi
  exact hx (SchwartzMap.tsupport_lineDerivOp_subset _ _
    (SchwartzMap.tsupport_lineDerivOp_subset _ _ hi))

/-- The transpose of the test-function Laplacian, normalized at gamma = 1. -/
noncomputable def fieldMap (d : ℕ) : Field d →L[ℝ] Field d :=
  (1 / 6 : ℝ) • ContinuousLinearMap.precomp ℝ (laplacianCLM ℝ (Space d) (Test d))

theorem fieldMap_apply {d : ℕ} (φ : Field d) (f : Test d) :
    fieldMap d φ f = (1 / 6 : ℝ) * φ (Δ f) := rfl

theorem fieldMap_local (d : ℕ) : localMap (fieldMap d) := by
  intro U _ f hf
  let : MeasurableSpace (Field d) := observed U
  have hEval : Measurable (fun φ : Field d => φ (Δ f)) :=
    Measurable.of_comap_le (le_iSup_of_le
      (⟨Δ f, (tsupport_laplacian_subset f).trans hf⟩ :
        {g : Test d // tsupport g ⊆ U}) le_rfl)
  exact measurable_const.mul hEval

noncomputable local instance : MeasurableSpace (Field 5) := borel _
local instance : BorelSpace (Field 5) := ⟨rfl⟩

/-- The analytic inputs for the counterexample are the input field's two-point function
and the differentiated Riesz kernel on separated tests. -/
theorem localField_disproof (μ : Measure (Field 5)) [IsProbabilityMeasure μ]
    (law : ∀ f : Test 5, HasLaw (fun φ : Field 5 => φ f)
      (gaussianReal 0 (rieszPair 4 f f).toNNReal) μ)
    (cov : ∀ f g : Test 5, (∫ φ : Field 5, φ f * φ g ∂μ) = rieszPair 4 f g)
    (kernel : ∀ f g : Test 5, HasCompactSupport f → HasCompactSupport g →
      Disjoint (tsupport f) (tsupport g) →
        rieszPair 4 (Δ f) (Δ g) = 72 * rieszPair 8 f g) :
    ¬ (type_of% @OMA.S_mo_201997.main) := by
  intro h
  have noField := h 5 (by decide) 2 1 (by norm_num) (by norm_num) (by norm_num)
    μ inferInstance (by norm_num; exact law)
  apply noField
  refine ⟨fieldMap 5, (fieldMap 5).continuous.measurable, fieldMap_local 5, ?_, ?_⟩
  · intro f
    have hLaw := gaussianReal_const_mul (law (Δ f)) (1 / 6 : ℝ)
    rw [mul_zero] at hLaw
    refine ⟨MemLp.comp_of_map (g := id) (hLaw.map_eq.symm ▸ memLp_id_gaussianReal' 2 (by simp))
      hLaw.aemeasurable, ?_⟩
    exact hLaw.integral_eq.trans integral_id_gaussianReal
  · intro f g hf hg hfg
    simp only [fieldMap_apply]
    calc
      _ = ∫ φ : Field 5, (1 / 36 : ℝ) * (φ (Δ f) * φ (Δ g)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with φ
        ring
      _ = _ := by
        rw [integral_const_mul, cov, kernel f g hf hg hfg]
        norm_num
        ring

end MO201997
end

-- KernelIBP
section
noncomputable section
open MeasureTheory Filter Topology Laplacian Metric Set
open scoped ContDiff
open OMA.S_mo_201997

namespace MO201997

theorem smoothReplacement {K : Set (Space 5)} (hK : IsCompact K) {a : Space 5} (ha : a ∉ K)
    {k : Space 5 → ℝ} (hk : ∀ x, x ≠ a → ContDiffAt ℝ ∞ k x) :
    ∃ t : Test 5, ∀ x ∈ K, (t : Space 5 → ℝ) =ᶠ[𝓝 x] k := by
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl a ha
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 a
  let small : ContDiffBump a := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let big : ContDiffBump a := ⟨R,R+1,hR,lt_add_one _⟩
  let q : Space 5 → ℝ := fun x => big x * ((1-small x) * k x)
  have hq : HasCompactSupport q := big.hasCompactSupport.mul_right (f' := fun x => (1-small x)*k x)
  have hqd : ContDiff ℝ ∞ q := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x = a
    · subst x
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [small.eventuallyEq_one] with z hz
      simp [q, show small z = 1 from hz]
    · exact big.contDiff.contDiffAt.mul ((contDiffAt_const.sub small.contDiff.contDiffAt).mul (hk x hx))
  refine ⟨hq.toSchwartzMap hqd, fun x hx => ?_⟩
  have hd : r ≤ dist x a := by
    by_contra! hh
    exact hrK hh hx
  have hp : small.rOut < dist x a := by dsimp [small]; linarith
  have hsmall : ∀ᶠ z in 𝓝 x, small.rOut < dist z a :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hp
  filter_upwards [big.eventuallyEq_one_of_mem_ball (hKR hx), hsmall] with z hzb hzs
  change big z * ((1-small z)* k z) = k z
  simp [show big z = 1 from hzb, small.zero_of_le_dist hzs.le]

theorem lapSupport (f : Test 5) : tsupport (Δ f : Test 5) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport _)
  by_contra h
  have hz : (f : Space 5 → ℝ) =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp h
  have hl := (InnerProductSpace.laplacian_congr_nhds hz).eq_of_nhds
  exact hx (by simpa [SchwartzMap.laplacian_apply] using hl)

theorem offDiagonalIBP (f : Test 5) (hf : HasCompactSupport f) {a : Space 5} (ha : a ∉ tsupport f)
    (k : Space 5 → ℝ) (hk : ∀ x, x ≠ a → ContDiffAt ℝ ∞ k x) :
    (∫ x, (Δ f : Test 5) x * k x) = ∫ x, f x * (Δ k) x := by
  obtain ⟨t, ht⟩ := smoothReplacement hf ha hk
  trans ∫ x : Space 5, (Δ f : Test 5) x * t x
  · apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · rw [(ht x hx).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport (fun h => hx (lapSupport f h))]
  rw [← SchwartzMap.integral_mul_laplacian_right_eq_left]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport f
  · rw [SchwartzMap.laplacian_apply, (InnerProductSpace.laplacian_congr_nhds (ht x hx)).eq_of_nhds]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end MO201997
end
end

-- Kernel
section
noncomputable section

open MeasureTheory Filter Topology Laplacian
open scoped RealInnerProductSpace
open OMA.S_mo_201997

namespace MO201997

private def sqKernel (p : ℝ) (x : Space 5) := (‖x‖ ^ 2) ^ p

private theorem sqKernel_diff (p : ℝ) {x : Space 5} (hx : x ≠ 0) :
    HasFDerivAt (sqKernel p) ((p * (‖x‖ ^ 2) ^ (p - 1)) • (2 • innerSL ℝ x)) x :=
  (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

private theorem sqKernel_second (p : ℝ) {x : Space 5} (hx : x ≠ 0) (v : Space 5) :
    iteratedFDeriv ℝ 2 (sqKernel p) x ![v,v] =
      4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * ⟪x,v⟫ ^ 2 +
      2 * p * (‖x‖ ^ 2) ^ (p - 1) * ‖v‖ ^ 2 := by
  have hn : fderiv ℝ (sqKernel p) =ᶠ[𝓝 x]
      fun z => (p * (‖z‖ ^ 2) ^ (p - 1)) • (2 • innerSL ℝ z) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with z hz
    exact (sqKernel_diff p hz).fderiv
  have h := ((sqKernel_diff (p-1) hx).const_mul p).smul
    ((innerSL ℝ (E := Space 5)).hasFDerivAt.const_smul (2 : ℕ))
  rw [iteratedFDeriv_two_apply, hn.fderiv_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change HasFDerivAt (fun z : Space 5 => (p * (‖z‖ ^ 2) ^ (p - 1)) • (2 • innerSL ℝ z)) _ x at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, sqKernel, innerSL_apply_apply,
    show p - 1 - 1 = p - 2 by ring]
  change p * (‖x‖ ^ 2) ^ (p - 1) * (2 * ⟪v,v⟫) +
    p * ((p - 1) * (‖x‖ ^ 2) ^ (p - 2) * (2 * ⟪x,v⟫)) *
      (2 * ⟪x,v⟫) = _
  rw [real_inner_self_eq_norm_sq]
  ring

private theorem laplacian_sqKernel (p : ℝ) {x : Space 5} (hx : x ≠ 0) :
    (Δ (sqKernel p)) x =
    4 * p * (p - 1) * (‖x‖ ^ 2) ^ (p - 2) * ‖x‖^2 +
      10 * p * (‖x‖ ^ 2) ^ (p - 1) := by
  let b := EuclideanSpace.basisFun (Fin 5) ℝ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [sqKernel_second p hx, Finset.sum_add_distrib, ← Finset.mul_sum,
    b.norm_eq_one, one_pow, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hs : (∑ i, ⟪x,b i⟫^2) = ‖x‖^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_left x
  rw [hs]
  ring

private theorem laplacian_shift (k : Space 5 → ℝ) (a x : Space 5) :
    (Δ (fun z => k (z-a))) x = (Δ k) (x-a) := by
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_sub]

theorem laplacian_shift_four (a x : Space 5) (hx : x ≠ a) :
    (Δ (fun z : Space 5 => ‖z-a‖ ^ (-(4:ℝ)))) x = 4 * ‖x-a‖ ^ (-(6:ℝ)) := by
  have normpow (z : Space 5) : ‖z‖ ^ (-(4:ℝ)) = sqKernel (-2) z := by
    norm_num [sqKernel, Real.rpow_neg (norm_nonneg _), Real.rpow_neg (sq_nonneg _),
      Real.rpow_ofNat, ← pow_mul]
  simp_rw [normpow, laplacian_shift, laplacian_sqKernel _ (sub_ne_zero.mpr hx)]
  have hs := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  norm_num [Real.rpow_neg (sq_nonneg _), Real.rpow_neg (norm_nonneg _),
    Real.rpow_ofNat]; field_simp; ring

theorem laplacian_shift_six (a x : Space 5) (hx : x ≠ a) :
    (Δ (fun z : Space 5 => ‖z-a‖ ^ (-(6:ℝ)))) x = 18 * ‖x-a‖ ^ (-(8:ℝ)) := by
  have normpow (z : Space 5) : ‖z‖ ^ (-(6:ℝ)) = sqKernel (-3) z := by
    norm_num [sqKernel, Real.rpow_neg (norm_nonneg _), Real.rpow_neg (sq_nonneg _),
      Real.rpow_ofNat, ← pow_mul]
  simp_rw [normpow, laplacian_shift, laplacian_sqKernel _ (sub_ne_zero.mpr hx)]
  have hs := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  norm_num [Real.rpow_neg (sq_nonneg _), Real.rpow_neg (norm_nonneg _),
    Real.rpow_ofNat]; field_simp; ring

end MO201997
end
end

-- KernelPair
section
noncomputable section
open MeasureTheory Filter Topology Laplacian Set
open scoped ContDiff
open OMA.S_mo_201997

namespace MO201997

private def shiftedKernel (p : ℝ) (a x : Space 5) := ‖x-a‖ ^ (-p)

private theorem pair_eq (p : ℝ) (f g : Test 5) :
    rieszPair p f g = ∫ x, f x * ∫ y, g y * shiftedKernel p x y := by
  unfold rieszPair
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [shiftedKernel, norm_sub_rev x y]
  ring

private theorem pair_symm (p : ℝ) (f g : Test 5) (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) (hfg : Disjoint (tsupport f) (tsupport g)) :
    rieszPair p f g = rieszPair p g f := by
  let H : Space 5 × Space 5 → ℝ := fun z => f z.1 * g z.2 * ‖z.1-z.2‖ ^ (-p)
  have hc : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    rintro ⟨x,y⟩
    by_cases h : x = y
    · subst y
      apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
      by_cases hx : x ∈ tsupport f
      · have hy := Set.disjoint_left.mp hfg hx
        have hz := (notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto
          (continuous_snd.continuousAt (x := (x,x)))
        filter_upwards [hz] with z hh
        simp [H, show g z.2 = 0 from hh]
      · have hz := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto
          (continuous_fst.continuousAt (x := (x,x)))
        filter_upwards [hz] with z hh
        simp [H, show f z.1 = 0 from hh]
    · apply ((f.continuous.comp continuous_fst).continuousAt.mul
        (g.continuous.comp continuous_snd).continuousAt).mul
      exact ((continuous_fst.sub continuous_snd).norm.continuousAt).rpow_const
        (Or.inl (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)))
  have hcc : HasCompactSupport H := (hf.prod hg).of_isClosed_subset (isClosed_tsupport H)
    (closure_minimal (fun z hz => ⟨subset_tsupport f (by
      intro hh; exact hz (by simp [H,hh])), subset_tsupport g (by
      intro hh; exact hz (by simp [H,hh]))⟩) (hf.isClosed.prod hg.isClosed))
  have hint : Integrable H (volume.prod volume) := hc.integrable_of_hasCompactSupport hcc
  have hs := integral_integral_swap (f := fun x y => f x*g y*‖x-y‖^(-p)) hint
  unfold rieszPair
  rw [hs]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  rw [norm_sub_rev x y, mul_comm (f x) (g y)]

private theorem pair_laplacian_right (p q c : ℝ)
    (hΔ : ∀ a x : Space 5, x ≠ a →
      (Δ (shiftedKernel p a)) x = c * shiftedKernel q a x)
    (f g : Test 5) (hg : HasCompactSupport g) (hfg : Disjoint (tsupport f) (tsupport g)) :
    rieszPair p f (Δ g) = c * rieszPair q f g := by
  simp only [pair_eq]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport f
  · have hn : x ∉ tsupport g := Set.disjoint_left.mp hfg hx
    have hdiff (z : Space 5) (hz : z ≠ x) : ContDiffAt ℝ ∞ (shiftedKernel p x) z :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hz)).rpow_const_of_ne
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz))
    rw [offDiagonalIBP g hg hn (shiftedKernel p x) hdiff]
    rw [mul_left_comm c]
    apply congrArg (fun r : ℝ => f x * r)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ tsupport g
    · rw [hΔ x y (fun h => hn (h ▸ hy))]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem rieszPair_laplacian (f g : Test 5) (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfg : Disjoint (tsupport f) (tsupport g)) :
    rieszPair 4 (Δ f) (Δ g) = 72 * rieszPair 8 f g := by
  have hf' : HasCompactSupport (Δ f : Test 5) :=
    hf.of_isClosed_subset (isClosed_tsupport _) (lapSupport f)
  have hfg' := hfg.mono_left (lapSupport f)
  rw [pair_laplacian_right 4 6 4 laplacian_shift_four (Δ f) g hg hfg',
    pair_symm 6 (Δ f) g hf' hg hfg',
    pair_laplacian_right 6 8 18 laplacian_shift_six g f hf hfg.symm,
    pair_symm 8 g f hg hf hfg.symm]
  ring

end MO201997
end
end

-- MathAnalyticJoin
section
open OMA.S_mo_201997 MeasureTheory ProbabilityTheory

namespace MO201997

/-- The Riesz covariance gives a seminorm on the real five-dimensional test space. -/
noncomputable def rieszCore : PreInnerProductSpace.Core ℝ (Test 5) where
  inner := rieszPair 4
  conj_inner_symm f g := RieszInput.rieszPair_comm g f
  re_inner_nonneg := RieszInput.rieszPair_nonneg
  add_left := RieszInput.rieszPair_add_left
  smul_left f g c := riesz_smul_left 4 c f g

theorem rieszCore_continuous : ContinuousAt (fun f => rieszCore.inner f f) 0 :=
  diagonal_continuousAt_zero RieszInput.nearMass (fun f => RieszInput.norm_rieszPair_le f f)

end MO201997

open MO201997

/-- In dimension five, the field differentiated by one sixth of the Laplacian
has the required local evaluations and off-diagonal covariance. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_201997.main) := by
  letI : MeasurableSpace (Field 5) := borel _
  letI := CovarianceSpace.separableHilbert rieszCore rieszCore_continuous
  obtain ⟨μ, hμ, law, cov⟩ :=
    strongGaussian_exists (CovarianceSpace.toHilbert rieszCore rieszCore_continuous)
  letI : IsProbabilityMeasure μ := hμ
  have hip (f g : Test 5) : inner ℝ (CovarianceSpace.toHilbert rieszCore rieszCore_continuous f)
      (CovarianceSpace.toHilbert rieszCore rieszCore_continuous g) = rieszPair 4 f g :=
    CovarianceSpace.toHilbert_inner rieszCore rieszCore_continuous f g
  apply localField_disproof μ _ _ rieszPair_laplacian
  · intro f
    rw [← hip f f]
    exact law f
  · intro f g
    exact (cov f g).trans (hip f g)
end
