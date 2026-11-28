import OMAReductions.R_Erdos653_erdos_653_R2
import Mathlib

/-!
# Shifted-grid norm estimates for Erdős 653

The Gaussian-integer estimates below are adapted from Liam Kruer and Jensen
Kohlmeyer (gus), Conjectures.io, result 257ce6dd-e3e5-4169-9d7e-2811092977ca,
https://conjectures.io/results/257ce6dd-e3e5-4169-9d7e-2811092977ca/solution.
The SHA-256 of the original Main.lean is
f3b51c0df8d3c8fb5ad2b71b01474345fc3dece2d1bd37c9d60b45acc711fde4.

We strengthen their residue selection by excluding three coordinate lines and
transfer the resulting disk counts to the project's full difference square.
The low palette gains at most one norm from zero. For prime distribution we use the convolution of the character modulo four
with the von Mangoldt function. Its bounded partial sums, together with
Chebyshev's estimate and summation by parts, give both of the required
progression estimates. A fixed multiplicative interval replaces the dyadic
interval in the original prime selection.

The source construction credits Prime Number Theorem and More, organized by
Alex Kontorovich and Terence Tao, https://github.com/AlexKontorovich/PrimeNumberTheoremAnd,
revision a5154676af9aa3095150ee410cdda80555aa0642. We have also consulted
its IEANTN/Mertens.lean for the classical unsigned Mertens estimate.
The applicable Apache License follows.
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

-- Source: DistanceCounts/Core.lean
section
/-! Positive pinned-distance counts and the epsilon formulation used by the construction. -/

noncomputable section

namespace DistanceCounts


end DistanceCounts
end
end

-- Source: DistanceCounts/GaussianNorm.lean
section
/-! Inert-prime residues and exact denominators of rational squared distances. -/

noncomputable section

namespace DistanceCounts.GaussianNorm

/-- The actual Gaussian residue class, not a coordinatewise surrogate. -/
def residue (p : ℕ) (z : GaussianInt) :
    GaussianInt ⧸ Ideal.span ({(p : GaussianInt)} : Set GaussianInt) :=
  Ideal.Quotient.mk _ z

/-- Being nonzero modulo a rational integer is exactly Gaussian nondivisibility. -/
theorem residue_ne_zero_iff (p : ℕ) (z : GaussianInt) :
    residue p z ≠ 0 ↔ ¬(p : GaussianInt) ∣ z := by
  simp only [residue, ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Adding an integer-grid difference to `z/q` preserves every residue at a
prime factor of `q`. This is the arithmetic uniformity over pins in §3.3. -/
theorem residue_add_denominator_mul (p q : ℕ) (hpq : p ∣ q) (z w : GaussianInt) :
    residue p (z + (q : GaussianInt) * w) = residue p z := by
  apply Ideal.Quotient.eq.2
  apply Ideal.mem_span_singleton.2
  have hcast : (p : GaussianInt) ∣ (q : GaussianInt) := by
    obtain ⟨k, hk⟩ := hpq
    exact ⟨(k : GaussianInt), by exact_mod_cast hk⟩
  simpa only [add_sub_cancel_left] using dvd_mul_of_dvd_left hcast w

/-- An inert rational prime divides a Gaussian norm precisely when it divides
its Gaussian argument. The forward implication uses primality and conjugation. -/
theorem inert_dvd_norm_iff (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3)
    (z : GaussianInt) : (p : ℤ) ∣ z.norm ↔ (p : GaussianInt) ∣ z := by
  have hprime : Prime (p : GaussianInt) :=
    @GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p ⟨hp⟩ hp3
  constructor
  · intro h
    have hc : (p : GaussianInt) ∣ (z.norm : GaussianInt) := by
      simpa only [Int.cast_natCast] using
        (Zsqrtd.intCast_dvd_intCast (p : ℤ) z.norm).2 h
    rw [Zsqrtd.norm_eq_mul_conj] at hc
    rcases hprime.dvd_or_dvd hc with hz | hz
    · exact hz
    · obtain ⟨w, hw⟩ := hz
      refine ⟨star w, ?_⟩
      simpa [mul_comm] using congrArg star hw
  · intro h
    apply (Zsqrtd.intCast_dvd_intCast (p : ℤ) z.norm).1
    change (p : GaussianInt) ∣ (z.norm : GaussianInt)
    rw [Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_of_dvd_left h (star z)

/-- The natural-valued norm version used by rational reduction. -/
theorem inert_dvd_natNorm_iff (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3)
    (z : GaussianInt) : p ∣ z.norm.natAbs ↔ (p : GaussianInt) ∣ z := by
  rw [← Int.natCast_dvd, inert_dvd_norm_iff p hp hp3 z]


end DistanceCounts.GaussianNorm
end
end

-- Source: DistanceCounts/OffsetSeparation.lean
section
/-! Prime-denominator separation. Integer arrays are unrestricted; all separation
comes from the fixed rational offsets and their explicit nonzero residues. -/

noncomputable section
open scoped BigOperators

namespace DistanceCounts.OffsetSeparation

/-- The actual rational vector represented by a Gaussian numerator. -/
def rationalOffset (z : GaussianInt) (p : ℕ) : ℚ × ℚ :=
  ((z.re : ℚ) / p, (z.im : ℚ) / p)


/-- Signed multiplicity of an index in the difference of two pairs. -/
def pairCoefficient {I : Type*} [DecidableEq I] (i j a b k : I) : ℤ :=
  (if k = i then 1 else 0) + (if k = j then 1 else 0) -
    (if k = a then 1 else 0) - (if k = b then 1 else 0)


theorem pairCoefficient_sum {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℚ) (i j a b : I) :
    (∑ k, (pairCoefficient i j a b k : ℚ) * r k) =
      r i + r j - r a - r b := by
  simp [pairCoefficient, Int.cast_add, Int.cast_sub, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul]


end DistanceCounts.OffsetSeparation
end
end

-- Source: DistanceCounts/Geometry.lean
section
/-! Exact Euclidean identities and distant horizontal control lines. -/

noncomputable section

namespace DistanceCounts


end DistanceCounts
end
end

-- Source: DistanceCounts/LineCount.lean
section
/-! Exact midpoint collision counts and the Euclidean line-control extension identity. -/

noncomputable section

namespace DistanceCounts


end DistanceCounts
end
end

-- Source: DistanceCounts/ObliqueLine.lean
section
/-! Arbitrarily oriented Euclidean control lines and their exact extension count. -/

noncomputable section

namespace DistanceCounts


end DistanceCounts
end
end

-- Source: DistanceCounts/GridPairs.lean
section
/-! Exact grid displacement counts and finite maximum-norm kernel estimates. -/

noncomputable section

namespace DistanceCounts
namespace GridPairs

open Finset
open scoped Classical


end GridPairs
end DistanceCounts
end
end

-- Source: DistanceCounts/CoarseGrid.lean
section
noncomputable section

namespace DistanceCounts.CoarseGrid

open OffsetSeparation

/-- The two prime indices present in a coarse block. -/
def blockAxes {t : ℕ} (b : Fin t × Fin t) : Finset (Fin t ⊕ Fin t) :=
  {.inl b.1, .inr b.2}

/-- Shared row and column denominators cancel before a modulus is formed. -/
def pairSupport {t : ℕ} (b c : Fin t × Fin t) : Finset (Fin t ⊕ Fin t) :=
  (blockAxes b \ blockAxes c) ∪ (blockAxes c \ blockAxes b)

/-- Orientation is pin minus target, matching `sqDist` coordinate differences. -/
def pairSign {t : ℕ} (b c : Fin t × Fin t) (i : Fin t ⊕ Fin t) : ℤ :=
  (if i ∈ blockAxes b then 1 else 0) - (if i ∈ blockAxes c then 1 else 0)

theorem blockAxes_card {t : ℕ} (b : Fin t × Fin t) : (blockAxes b).card = 2 := by
  simp [blockAxes]

theorem pairSupport_card_le_four {t : ℕ} (b c : Fin t × Fin t) :
    (pairSupport b c).card ≤ 4 := by
  have h₁ : (blockAxes b \ blockAxes c).card ≤ 2 := by
    calc
      _ ≤ (blockAxes b).card := Finset.card_le_card Finset.sdiff_subset
      _ = 2 := blockAxes_card b
  have h₂ : (blockAxes c \ blockAxes b).card ≤ 2 := by
    calc
      _ ≤ (blockAxes c).card := Finset.card_le_card Finset.sdiff_subset
      _ = 2 := blockAxes_card c
  exact (Finset.card_union_le _ _).trans (by omega)


end DistanceCounts.CoarseGrid
end
end

-- Source: DistanceCounts/GaussianResidues.lean
section
noncomputable section

namespace DistanceCounts.GaussianResidues

abbrev Residue (q : ℕ) :=
  GaussianInt ⧸ Ideal.span ({(q : GaussianInt)} : Set GaussianInt)

/-- Integer coordinates characterize equality in the actual Gaussian quotient. -/
theorem residue_eq_iff (q : ℕ) (z w : GaussianInt) :
    GaussianNorm.residue q z = GaussianNorm.residue q w ↔
      (z.re : ZMod q) = (w.re : ZMod q) ∧
      (z.im : ZMod q) = (w.im : ZMod q) := by
  rw [GaussianNorm.residue, GaussianNorm.residue, Ideal.Quotient.eq,
    Ideal.mem_span_singleton]
  have h := Zsqrtd.intCast_dvd (q : ℤ) (z - w)
  simp only [Int.cast_natCast, Zsqrtd.re_sub, Zsqrtd.im_sub] at h
  rw [h]
  constructor
  · rintro ⟨hr, hi⟩
    constructor
    · apply sub_eq_zero.mp
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (z.re - w.re) q).2 hr
    · apply sub_eq_zero.mp
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (z.im - w.im) q).2 hi
  · rintro ⟨hr, hi⟩
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
      simpa [hr]
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
      simpa [hi]

/-- This is a map of sets, not a map to the coordinatewise product ring. -/
def coordinates (q : ℕ) (a : Residue q) : ZMod q × ZMod q :=
  ((Quotient.out a).re, (Quotient.out a).im)

theorem coordinates_residue (q : ℕ) (z : GaussianInt) :
    coordinates q (GaussianNorm.residue q z) = ((z.re : ZMod q), (z.im : ZMod q)) := by
  apply Prod.ext
  · exact ((residue_eq_iff q _ _).1 (Ideal.Quotient.mk_out _)).1
  · exact ((residue_eq_iff q _ _).1 (Ideal.Quotient.mk_out _)).2

theorem coordinates_injective (q : ℕ) : Function.Injective (coordinates q) := by
  intro a b h
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (residue_eq_iff q z w).2
  change coordinates q (GaussianNorm.residue q z) =
    coordinates q (GaussianNorm.residue q w) at h
  rw [coordinates_residue, coordinates_residue] at h
  exact Prod.mk.inj h

/-- The genuine underlying-set equivalence; multiplication is described below. -/
def coordinateEquiv (q : ℕ) : Residue q ≃ ZMod q × ZMod q where
  toFun := coordinates q
  invFun v := GaussianNorm.residue q ⟨ZMod.cast v.1, ZMod.cast v.2⟩
  left_inv a := by
    apply coordinates_injective q
    change coordinates q
      (GaussianNorm.residue q ⟨ZMod.cast (coordinates q a).1,
        ZMod.cast (coordinates q a).2⟩) = coordinates q a
    rw [coordinates_residue]
    exact Prod.ext (ZMod.intCast_zmod_cast _) (ZMod.intCast_zmod_cast _)
  right_inv v := by
    change coordinates q (GaussianNorm.residue q ⟨ZMod.cast v.1, ZMod.cast v.2⟩) = v
    rw [coordinates_residue]
    exact Prod.ext (ZMod.intCast_zmod_cast _) (ZMod.intCast_zmod_cast _)

theorem finite_residue (q : ℕ) (hq : 0 < q) : Finite (Residue q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact Finite.of_injective (coordinates q) (coordinates_injective q)

theorem card_residue (q : ℕ) : Nat.card (Residue q) = q ^ 2 := by
  rw [Nat.card_congr (coordinateEquiv q)]
  simp [Nat.card_prod, pow_two]

theorem coordinates_zero (q : ℕ) : coordinates q 0 = (0, 0) := by
  simpa [GaussianNorm.residue] using coordinates_residue q 0

theorem coordinates_one (q : ℕ) : coordinates q 1 = (1, 0) := by
  simpa [GaussianNorm.residue] using coordinates_residue q 1

theorem coordinates_mul (q : ℕ) (a b : Residue q) :
    coordinates q (a * b) =
      ((coordinates q a).1 * (coordinates q b).1 -
        (coordinates q a).2 * (coordinates q b).2,
       (coordinates q a).1 * (coordinates q b).2 +
        (coordinates q a).2 * (coordinates q b).1) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
  change coordinates q (GaussianNorm.residue q (z * w)) =
    ((coordinates q (GaussianNorm.residue q z)).1 *
        (coordinates q (GaussianNorm.residue q w)).1 -
      (coordinates q (GaussianNorm.residue q z)).2 *
        (coordinates q (GaussianNorm.residue q w)).2,
     (coordinates q (GaussianNorm.residue q z)).1 *
        (coordinates q (GaussianNorm.residue q w)).2 +
      (coordinates q (GaussianNorm.residue q z)).2 *
        (coordinates q (GaussianNorm.residue q w)).1)
  simp [coordinates_residue, Zsqrtd.re_mul, Zsqrtd.im_mul, sub_eq_add_neg]

/-- Conjugation induced by Gaussian conjugation on the quotient. -/
def conjugate (q : ℕ) (a : Residue q) : Residue q :=
  (coordinateEquiv q).symm ((coordinates q a).1, -(coordinates q a).2)

theorem coordinates_conjugate (q : ℕ) (a : Residue q) :
    coordinates q (conjugate q a) = ((coordinates q a).1, -(coordinates q a).2) :=
  (coordinateEquiv q).apply_symm_apply _

theorem conjugate_residue (q : ℕ) (z : GaussianInt) :
    conjugate q (GaussianNorm.residue q z) = GaussianNorm.residue q (star z) := by
  apply coordinates_injective q
  simp [coordinates_conjugate, coordinates_residue]

/-- Reduction of the actual Gaussian norm. -/
def norm (q : ℕ) (a : Residue q) : ZMod q :=
  (coordinates q a).1 ^ 2 + (coordinates q a).2 ^ 2

theorem norm_residue (q : ℕ) (z : GaussianInt) :
    norm q (GaussianNorm.residue q z) = (z.norm : ZMod q) := by
  simp [norm, coordinates_residue, Zsqrtd.norm]
  ring


/-- A counting lemma whose finiteness hypotheses are local to its use. -/
private theorem card_le_fibers {A B : Type*} [Finite A] [Fintype B]
    (f : A → B) (k : ℕ) (h : ∀ b, Nat.card {a // f a = b} ≤ k) :
    Nat.card A ≤ Fintype.card B * k := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  calc
    ∑ b, Nat.card {a // f a = b} ≤ ∑ _ : B, k := Finset.sum_le_sum fun b _ => h b
    _ = Fintype.card B * k := by simp

/-- Over a domain, a square has at most two roots, including characteristic two. -/
private theorem card_square_fiber {K : Type*} [CommRing K] [IsDomain K] [Finite K]
    (t : K) : Nat.card {x : K // x ^ 2 = t} ≤ 2 := by
  classical
  by_cases ht : ∃ x : K, x ^ 2 = t
  · obtain ⟨r, hr⟩ := ht
    let f : {x : K // x ^ 2 = t} → Bool := fun x => decide (x.1 = r)
    have hx (x : {x : K // x ^ 2 = t}) : x.1 = r ∨ x.1 = -r := by
      have hm : (x.1 - r) * (x.1 + r) = 0 := by
        calc
          _ = x.1 ^ 2 - r ^ 2 := by ring
          _ = 0 := by rw [x.2, hr, sub_self]
      rcases mul_eq_zero.mp hm with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · right
        linear_combination h
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      have hd : (x.1 = r) ↔ (y.1 = r) := by simpa [f] using h
      rcases hx x with hxr | hxr
      · exact hxr.trans (hd.mp hxr).symm
      · rcases hx y with hy | hy
        · exact (hd.mpr hy).trans hy.symm
        · exact hxr.trans hy.symm
    simpa using Nat.card_le_card_of_injective f hf
  · haveI : IsEmpty {x : K // x ^ 2 = t} := ⟨fun x => ht ⟨x.1, x.2⟩⟩
    simp

/-- Every norm fiber in the real prime quotient has at most `2p` elements. -/
theorem card_norm_fiber_prime (p : ℕ) (hp : p.Prime) (t : ZMod p) :
    Nat.card {a : Residue p // norm p a = t} ≤ 2 * p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Finite (Residue p) := finite_residue p hp.pos
  let f : {a : Residue p // norm p a = t} → ZMod p :=
    fun a => (coordinates p a.1).2
  have hb (y : ZMod p) : Nat.card {a // f a = y} ≤ 2 := by
    let g : {a // f a = y} → {x : ZMod p // x ^ 2 = t - y ^ 2} :=
      fun a => ⟨(coordinates p a.1.1).1, by
        have ha := a.1.2
        change (coordinates p a.1.1).1 ^ 2 + (coordinates p a.1.1).2 ^ 2 = t at ha
        have hy : (coordinates p a.1.1).2 = y := a.2
        rw [hy] at ha
        exact eq_sub_of_add_eq ha⟩
    have hg : Function.Injective g := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      apply coordinates_injective p
      exact Prod.ext (congrArg Subtype.val h) (a.2.trans b.2.symm)
    exact (Nat.card_le_card_of_injective g hg).trans (card_square_fiber _)
  simpa [ZMod.card, Nat.mul_comm] using card_le_fibers f 2 hb

/-- A nonzero homogeneous linear equation cuts out at most one point above
each value of one coordinate. -/
theorem card_linear_fiber_prime (p : ℕ) (hp : p.Prime) (u v : ZMod p)
    (huv : u ≠ 0 ∨ v ≠ 0) :
    Nat.card {a : Residue p //
      u * (coordinates p a).1 + v * (coordinates p a).2 = 0} ≤ p := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases huv with hu | hv
  · let f : {a : Residue p //
        u * (coordinates p a).1 + v * (coordinates p a).2 = 0} → ZMod p :=
      fun a => (coordinates p a.1).2
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply coordinates_injective p
      apply Prod.ext
      · apply mul_left_cancel₀ hu
        have ha := a.2
        have hb := b.2
        change (coordinates p a.1).2 = (coordinates p b.1).2 at h
        rw [h] at ha
        linear_combination ha - hb
      · exact h
    simpa using Nat.card_le_card_of_injective f hf
  · let f : {a : Residue p //
        u * (coordinates p a).1 + v * (coordinates p a).2 = 0} → ZMod p :=
      fun a => (coordinates p a.1).1
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply coordinates_injective p
      apply Prod.ext
      · exact h
      · apply mul_left_cancel₀ hv
        have ha := a.2
        have hb := b.2
        change (coordinates p a.1).1 = (coordinates p b.1).1 at h
        rw [h] at ha
        linear_combination ha - hb
    simpa using Nat.card_le_card_of_injective f hf

theorem ratio_equation_coordinates (p : ℕ) (a b c : Residue p) :
    a * b = conjugate p a * c ↔
      ((coordinates p b).1 - (coordinates p c).1) * (coordinates p a).1 -
        ((coordinates p b).2 + (coordinates p c).2) * (coordinates p a).2 = 0 ∧
      ((coordinates p b).2 - (coordinates p c).2) * (coordinates p a).1 +
        ((coordinates p b).1 + (coordinates p c).1) * (coordinates p a).2 = 0 := by
  rw [← (coordinates_injective p).eq_iff, coordinates_mul, coordinates_mul,
    coordinates_conjugate, Prod.mk.injEq]
  constructor
  · rintro ⟨hr, hi⟩
    constructor
    · linear_combination hr
    · linear_combination hi
  · rintro ⟨hr, hi⟩
    constructor
    · linear_combination hr
    · linear_combination hi

/-- No division by `a` is involved: the bound includes the zero solution. -/
theorem card_ratio_fiber_prime (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (b c : Residue p) (hb : b ≠ 0) :
    Nat.card {a : Residue p // a * b = conjugate p a * c} ≤ p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Finite (Residue p) := finite_residue p hp.pos
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    have := hp.two_le
    omega
  let u := (coordinates p b).1 - (coordinates p c).1
  let v := -((coordinates p b).2 + (coordinates p c).2)
  let s := (coordinates p b).2 - (coordinates p c).2
  let t := (coordinates p b).1 + (coordinates p c).1
  have hnonzero : (u ≠ 0 ∨ v ≠ 0) ∨ (s ≠ 0 ∨ t ≠ 0) := by
    by_contra h
    have hh : u = 0 ∧ v = 0 ∧ s = 0 ∧ t = 0 := by tauto
    rcases hh with ⟨hu, hv, hs, ht⟩
    apply hb
    apply coordinates_injective p
    rw [coordinates_zero]
    apply Prod.ext
    · have hz : (2 : ZMod p) * (coordinates p b).1 = 0 := by
        dsimp [u] at hu
        dsimp [t] at ht
        linear_combination hu + ht
      exact (mul_eq_zero.mp hz).resolve_left htwo
    · have hz : (2 : ZMod p) * (coordinates p b).2 = 0 := by
        dsimp [v] at hv
        dsimp [s] at hs
        linear_combination hs - hv
      exact (mul_eq_zero.mp hz).resolve_left htwo
  rcases hnonzero with h | h
  · let f : {a : Residue p // a * b = conjugate p a * c} →
        {a : Residue p // u * (coordinates p a).1 + v * (coordinates p a).2 = 0} :=
      fun a => ⟨a.1, by
        have ha := ((ratio_equation_coordinates p a.1 b c).1 a.2).1
        dsimp [u, v]
        linear_combination ha⟩
    have hf : Function.Injective f := by
      intro a a' haa
      apply Subtype.ext
      exact congrArg
        (fun x : {a : Residue p //
          u * (coordinates p a).1 + v * (coordinates p a).2 = 0} => x.1) haa
    exact (Nat.card_le_card_of_injective f hf).trans
      (card_linear_fiber_prime p hp u v h)
  · let f : {a : Residue p // a * b = conjugate p a * c} →
        {a : Residue p // s * (coordinates p a).1 + t * (coordinates p a).2 = 0} :=
      fun a => ⟨a.1, ((ratio_equation_coordinates p a.1 b c).1 a.2).2⟩
    have hf : Function.Injective f := by
      intro a a' haa
      apply Subtype.ext
      exact congrArg
        (fun x : {a : Residue p //
          s * (coordinates p a).1 + t * (coordinates p a).2 = 0} => x.1) haa
    exact (Nat.card_le_card_of_injective f hf).trans
      (card_linear_fiber_prime p hp s t h)

theorem norm_ne_zero_iff_inert (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3)
    (a : Residue p) : norm p a ≠ 0 ↔ a ≠ 0 := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  change norm p (GaussianNorm.residue p z) ≠ 0 ↔ GaussianNorm.residue p z ≠ 0
  rw [norm_residue, GaussianNorm.residue_ne_zero_iff,
    ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, GaussianNorm.inert_dvd_norm_iff p hp hp3]

/-- Nonzero classes are precisely the units in an inert prime quotient. -/
theorem isUnit_iff_ne_zero_inert (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3)
    (a : Residue p) : IsUnit a ↔ a ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro ha hz
    obtain ⟨w, hw⟩ := ha.exists_right_inv
    rw [hz, zero_mul] at hw
    have hc := congrArg (fun a => (coordinates p a).1) hw
    simpa [coordinates_zero, coordinates_one] using hc
  · intro ha
    have hn := (norm_ne_zero_iff_inert p hp hp3 a).2 ha
    let w := (coordinateEquiv p).symm
      ((coordinates p a).1 / norm p a, -(coordinates p a).2 / norm p a)
    apply IsUnit.of_mul_eq_one w
    apply coordinates_injective p
    rw [coordinates_mul, coordinates_one]
    have hw : coordinates p w =
        ((coordinates p a).1 / norm p a, -(coordinates p a).2 / norm p a) :=
      (coordinateEquiv p).apply_symm_apply _
    rw [hw]
    apply Prod.ext
    · dsimp
      field_simp [hn]
      simp only [norm]
      ring
    · dsimp
      ring

theorem card_nonzero (q : ℕ) (hq : 0 < q) :
    Nat.card {a : Residue q // a ≠ 0} = q ^ 2 - 1 := by
  classical
  letI : Finite (Residue q) := finite_residue q hq
  letI : Fintype (Residue q) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, card_residue]

theorem card_units_inert (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) :
    Nat.card {a : Residue p // IsUnit a} = p ^ 2 - 1 := by
  have h : {a : Residue p // IsUnit a} ≃ {a : Residue p // a ≠ 0} :=
    Equiv.subtypeEquivRight (fun a => isUnit_iff_ne_zero_inert p hp hp3 a)
  rw [Nat.card_congr h, card_nonzero p hp.pos]

theorem card_unit_group_inert (p : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) :
    Nat.card (Residue p)ˣ = p ^ 2 - 1 := by
  let f : (Residue p)ˣ → {a : Residue p // IsUnit a} := fun u => ⟨u, u.isUnit⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      apply Units.ext
      exact congrArg Subtype.val h
    · rintro ⟨a, u, rfl⟩
      exact ⟨u, rfl⟩
  rw [Nat.card_eq_of_bijective f hf, card_units_inert p hp hp3]

/-- This is the bad numerator for the oblique projection, on actual classes. -/
theorem card_bad_projection_prime (p : ℕ) (hp : p.Prime) (L : ZMod p) :
    Nat.card {a : Residue p //
      L * (coordinates p a).1 + (coordinates p a).2 = 0} ≤ p := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa using card_linear_fiber_prime p hp L 1 (Or.inr one_ne_zero)

/-- The canonical reduction between the genuine quotient rings. -/
def reduce {p q : ℕ} (hpq : p ∣ q) : Residue q →+* Residue p :=
  Ideal.Quotient.lift _ (Ideal.Quotient.mk _) (by
    intro z hz
    apply Ideal.Quotient.eq_zero_iff_mem.2
    apply Ideal.mem_span_singleton.2
    have hpq' : (p : GaussianInt) ∣ (q : GaussianInt) := by
      obtain ⟨k, rfl⟩ := hpq
      exact ⟨(k : GaussianInt), by simp⟩
    exact hpq'.trans (Ideal.mem_span_singleton.1 hz))

theorem reduce_residue {p q : ℕ} (hpq : p ∣ q) (z : GaussianInt) :
    reduce hpq (GaussianNorm.residue q z) = GaussianNorm.residue p z := rfl


theorem norm_reduce {p q : ℕ} (hpq : p ∣ q) (a : Residue q) :
    norm p (reduce hpq a) = ZMod.castHom hpq (ZMod p) (norm q a) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  change norm p (reduce hpq (GaussianNorm.residue q z)) =
    ZMod.castHom hpq (ZMod p) (norm q (GaussianNorm.residue q z))
  rw [reduce_residue, norm_residue, norm_residue, map_intCast]

theorem conjugate_reduce {p q : ℕ} (hpq : p ∣ q) (a : Residue q) :
    conjugate p (reduce hpq a) = reduce hpq (conjugate q a) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  change conjugate p (reduce hpq (GaussianNorm.residue q z)) =
    reduce hpq (conjugate q (GaussianNorm.residue q z))
  rw [reduce_residue, conjugate_residue, conjugate_residue, reduce_residue]

/-- The actual CRT reduction map. Only its injectivity is needed for upper bounds. -/
def crtReduction (S : Finset ℕ) :
    Residue (∏ p ∈ S, p) → ∀ p : S, Residue p.1 :=
  fun a p => reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) a

theorem crtReduction_injective (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    Function.Injective (crtReduction S) := by
  intro a b h
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.2
  apply Ideal.mem_span_singleton.2
  have hd : ∀ p ∈ S, (p : GaussianInt) ∣ z - w := by
    intro p hp
    have he := congrFun h ⟨p, hp⟩
    change GaussianNorm.residue p z = GaussianNorm.residue p w at he
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 he)
  have hcop : (S : Set ℕ).Pairwise
      (fun p r => IsCoprime (p : GaussianInt) (r : GaussianInt)) := by
    intro p hp r hr hpr
    exact ((Nat.coprime_primes (hprime p hp) (hprime r hr)).2 hpr).cast
  simpa using (Finset.prod_dvd_of_coprime hcop hd)

/-- CRT bounds the size of any compatible fiber by the product of its local sizes. -/
theorem card_crt_fiber_le (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (P : Residue (∏ p ∈ S, p) → Prop) (Q : ∀ p : S, Residue p.1 → Prop)
    (hPQ : ∀ a, P a → ∀ p : S, Q p (crtReduction S a p)) :
    Nat.card {a // P a} ≤ ∏ p : S, Nat.card {a // Q p a} := by
  letI : ∀ p : S, Finite (Residue p.1) :=
    fun p => finite_residue p.1 (hprime p.1 p.2).pos
  let f : {a // P a} → ∀ p : S, {a // Q p a} :=
    fun a p => ⟨crtReduction S a.1 p, hPQ a.1 a.2 p⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply crtReduction_injective S hprime
    funext p
    exact congrArg Subtype.val (congrFun h p)
  simpa only [Nat.card_pi] using Nat.card_le_card_of_injective f hf

/-- Distinct prime factors give `2^|S| q`; inertness is not needed for this bound. -/
theorem card_norm_fiber_product (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (t : ZMod (∏ p ∈ S, p)) :
    Nat.card {a : Residue (∏ p ∈ S, p) // norm (∏ p ∈ S, p) a = t} ≤
      2 ^ S.card * (∏ p ∈ S, p) := by
  classical
  let Q (p : S) (a : Residue p.1) :=
    norm p.1 a = ZMod.castHom (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) (ZMod p.1) t
  have h := card_crt_fiber_le S hprime
    (fun a => norm (∏ p ∈ S, p) a = t) Q (by
      intro a ha p
      change norm p.1 (reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) a) =
        ZMod.castHom (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) (ZMod p.1) t
      rw [norm_reduce, ha])
  calc
    Nat.card {a : Residue (∏ p ∈ S, p) // norm (∏ p ∈ S, p) a = t}
        ≤ ∏ p : S, Nat.card {a // Q p a} := h
    _ ≤ ∏ p : S, 2 * p.1 := Finset.prod_le_prod' fun p _ =>
      card_norm_fiber_prime p.1 (hprime p.1 p.2) _
    _ = 2 ^ S.card * (∏ p ∈ S, p) := by
      rw [Finset.prod_mul_distrib]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
        Finset.prod_coe_sort S (fun p : ℕ => p)]

theorem card_norm_fiber_four_primes (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hfour : S.card ≤ 4) (t : ZMod (∏ p ∈ S, p)) :
    Nat.card {a : Residue (∏ p ∈ S, p) // norm (∏ p ∈ S, p) a = t} ≤
      16 * (∏ p ∈ S, p) := by
  have hpow : 2 ^ S.card ≤ 2 ^ 4 :=
    pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hfour
  exact (card_norm_fiber_product S hprime t).trans
    (Nat.mul_le_mul_right _ (by norm_num at hpow ⊢; exact hpow))

/-- The local ratio equations are imposed on actual CRT projections of `b,c`.
The number of prime factors need not be bounded for this estimate. -/
theorem card_ratio_fiber_product (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hinert : ∀ p ∈ S, p % 4 = 3)
    (b c : Residue (∏ p ∈ S, p))
    (hb : ∀ p : S, crtReduction S b p ≠ 0) :
    Nat.card {a : Residue (∏ p ∈ S, p) //
      a * b = conjugate (∏ p ∈ S, p) a * c} ≤ (∏ p ∈ S, p) := by
  classical
  let Q (p : S) (a : Residue p.1) :=
    a * crtReduction S b p = conjugate p.1 a * crtReduction S c p
  have h := card_crt_fiber_le S hprime
    (fun a => a * b = conjugate (∏ p ∈ S, p) a * c) Q (by
      intro a ha p
      have he := congrArg
        (reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2)) ha
      change reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) a *
          reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) b =
        conjugate p.1 (reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) a) *
          reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2) c
      simpa only [map_mul, ← conjugate_reduce] using he)
  calc
    Nat.card {a : Residue (∏ p ∈ S, p) //
        a * b = conjugate (∏ p ∈ S, p) a * c}
        ≤ ∏ p : S, Nat.card {a // Q p a} := h
    _ ≤ ∏ p : S, p.1 := Finset.prod_le_prod' fun p _ =>
      card_ratio_fiber_prime p.1 (hprime p.1 p.2)
        (by have := hinert p.1 p.2; omega) _ _ (hb p)
    _ = ∏ p ∈ S, p := Finset.prod_coe_sort S (fun p : ℕ => p)

end DistanceCounts.GaussianResidues
end
end

-- Source: DistanceCounts/GaussianUnitCRT.lean
section
noncomputable section

namespace DistanceCounts.GaussianUnitCRT

open GaussianResidues

/-- The canonical quotient reductions, bundled as a ring homomorphism. -/
def crtHom (S : Finset ℕ) :
    Residue (∏ p ∈ S, p) →+* ∀ p : S, Residue p.1 where
  toFun := crtReduction S
  map_one' := by funext p; exact map_one (reduce _)
  map_mul' a b := by funext p; exact map_mul (reduce _) a b
  map_zero' := by funext p; exact map_zero (reduce _)
  map_add' a b := by funext p; exact map_add (reduce _) a b

/-- Surjectivity follows from the exact cardinalities of the genuine rings. -/
theorem crtReduction_bijective (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    Function.Bijective (crtReduction S) := by
  letI : ∀ p : S, Finite (Residue p.1) :=
    fun p => finite_residue p.1 (hprime p.1 p.2).pos
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨crtReduction_injective S hprime, ?_⟩
  rw [card_residue, Nat.card_pi]
  simp_rw [card_residue]
  rw [Finset.prod_pow, Finset.prod_coe_sort S (fun p : ℕ => p)]

/-- CRT for actual Gaussian quotient rings, not for coordinatewise products. -/
def crtEquiv (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    Residue (∏ p ∈ S, p) ≃+* ∀ p : S, Residue p.1 :=
  RingEquiv.ofBijective (crtHom S) (crtReduction_bijective S hprime)


theorem half_square_le_four_fraction (q : ℕ) :
    (q : ℝ) ^ 2 / 2 ≤ (8 / 9 : ℝ) ^ 4 * (q : ℝ) ^ 2 := by
  nlinarith [sq_nonneg (q : ℝ)]


/-- Squarefree cofactors are exactly the products with one prime removed. -/
theorem cofactor_eq_prod_erase (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (p : S) : (∏ r ∈ S, r) / p.1 = ∏ r ∈ S.erase p.1, r := by
  apply Nat.div_eq_of_eq_mul_left (hprime p.1 p.2).pos
  simpa only [mul_comm] using (Finset.mul_prod_erase S (fun r : ℕ => r) p.2).symm

theorem cofactor_coprime (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (p : S) : Nat.Coprime ((∏ r ∈ S, r) / p.1) p.1 := by
  rw [cofactor_eq_prod_erase S hprime p, Nat.coprime_prod_left_iff]
  intro r hr
  obtain ⟨hne, hrS⟩ := Finset.mem_erase.mp hr
  exact (Nat.coprime_primes (hprime r hrS) (hprime p.1 p.2)).2 hne

/-- The cofactor is a unit in the actual local quotient; inertness is unnecessary. -/
theorem cofactor_isUnit (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (p : S) : IsUnit (((∏ r ∈ S, r) / p.1 : ℕ) : Residue p.1) := by
  have h : IsCoprime (((∏ r ∈ S, r) / p.1 : ℕ) : Residue p.1)
      (p.1 : Residue p.1) := (cofactor_coprime S hprime p).cast
  have hpzero : (p.1 : Residue p.1) = 0 := by
    have hz : GaussianNorm.residue p.1 (p.1 : GaussianInt) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (dvd_refl _))
    simpa only [GaussianNorm.residue, map_natCast] using hz
  rw [hpzero] at h
  exact isCoprime_zero_right.1 h


end DistanceCounts.GaussianUnitCRT
end
end

-- Source: DistanceCounts/BoundedResidueLift.lean
section
/-! Bounded set-theoretic representatives; no ring-homomorphism property is asserted. -/

noncomputable section

namespace DistanceCounts.BoundedResidueLift

open GaussianResidues OffsetSeparation

/-- Both integer coordinates are canonical representatives from `ZMod.val`. -/
def lift (q : ℕ) (a : Residue q) : GaussianInt :=
  ⟨((coordinates q a).1.val : ℤ), ((coordinates q a).2.val : ℤ)⟩

theorem residue_lift (q : ℕ) (hq : 0 < q) (a : Residue q) :
    GaussianNorm.residue q (lift q a) = a := by
  letI : NeZero q := ⟨ne_of_gt hq⟩
  apply coordinates_injective q
  rw [coordinates_residue]
  apply Prod.ext <;> simp [lift, ZMod.natCast_zmod_val]

theorem coordinate_bounds (q : ℕ) (hq : 0 < q) (a : Residue q) :
    (0 ≤ (lift q a).re ∧ (lift q a).re < (q : ℤ)) ∧
    (0 ≤ (lift q a).im ∧ (lift q a).im < (q : ℤ)) := by
  letI : NeZero q := ⟨ne_of_gt hq⟩
  change (0 ≤ ((coordinates q a).1.val : ℤ) ∧
      ((coordinates q a).1.val : ℤ) < (q : ℤ)) ∧
    (0 ≤ ((coordinates q a).2.val : ℤ) ∧
      ((coordinates q a).2.val : ℤ) < (q : ℤ))
  refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩
  · exact_mod_cast ZMod.val_lt (coordinates q a).1
  · exact_mod_cast ZMod.val_lt (coordinates q a).2

theorem rationalOffset_bounds (q : ℕ) (hq : 0 < q) (a : Residue q) :
    (0 ≤ (rationalOffset (lift q a) q).1 ∧ (rationalOffset (lift q a) q).1 < 1) ∧
    (0 ≤ (rationalOffset (lift q a) q).2 ∧ (rationalOffset (lift q a) q).2 < 1) := by
  have hb := coordinate_bounds q hq a
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  constructor
  · constructor
    · exact div_nonneg (by exact_mod_cast hb.1.1) hqQ.le
    · apply (div_lt_one hqQ).mpr
      exact_mod_cast hb.1.2
  · constructor
    · exact div_nonneg (by exact_mod_cast hb.2.1) hqQ.le
    · apply (div_lt_one hqQ).mpr
      exact_mod_cast hb.2.2


end DistanceCounts.BoundedResidueLift
end
end

-- Source: DistanceCounts/LatticeCount.lean
section
/-! Uniform Gaussian lattice disk and shifted-coset counts from unit-cell volumes. -/

noncomputable section

namespace DistanceCounts

open Set MeasureTheory
open scoped ENNReal

/-- Coordinate-bounded enumeration of exactly the Gaussian integers in a closed disk. -/
def gaussianDisk (c : ℂ) (r : ℝ) : Finset GaussianInt := by
  classical
  exact (((Finset.Icc ⌊c.re - r⌋ ⌊c.re + r⌋).product
    (Finset.Icc ⌊c.im - r⌋ ⌊c.im + r⌋)).image
      (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))).filter
        (fun z => dist (z : ℂ) c ≤ r)

lemma mem_gaussianDisk (c : ℂ) (r : ℝ) (z : GaussianInt) :
    z ∈ gaussianDisk c r ↔ dist (z : ℂ) c ≤ r := by
  classical
  constructor
  · intro hz
    exact (Finset.mem_filter.mp hz).2
  · intro hz
    have hx : |(z.re : ℝ) - c.re| ≤ r := by
      have h : |(z.re : ℝ) - c.re| ≤ dist (z : ℂ) c := by
        simpa only [Complex.sub_re, ← GaussianInt.intCast_re, dist_eq_norm] using
          Complex.abs_re_le_norm ((z : ℂ) - c)
      exact h.trans hz
    have hy : |(z.im : ℝ) - c.im| ≤ r := by
      have h : |(z.im : ℝ) - c.im| ≤ dist (z : ℂ) c := by
        simpa only [Complex.sub_im, ← GaussianInt.intCast_im, dist_eq_norm] using
          Complex.abs_im_le_norm ((z : ℂ) - c)
      exact h.trans hz
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(z.re, z.im), ?_, ?_⟩, hz⟩
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor
        · apply Int.floor_le_iff.mpr
          linarith
        · apply Int.le_floor.mpr
          linarith
      · apply Finset.mem_Icc.mpr
        constructor
        · apply Int.floor_le_iff.mpr
          linarith
        · apply Int.le_floor.mpr
          linarith
    · cases z
      rfl

/-- Half-open unit square whose lower-left vertex is the given lattice point. -/
def gaussianCell (z : GaussianInt) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Ico (z.re : ℝ) ((z.re : ℝ) + 1) ×ˢ
     Ico (z.im : ℝ) ((z.im : ℝ) + 1))

lemma mem_gaussianCell (z : GaussianInt) (x : ℂ) :
    x ∈ gaussianCell z ↔
      ((z.re : ℝ) ≤ x.re ∧ x.re < (z.re : ℝ) + 1) ∧
      ((z.im : ℝ) ≤ x.im ∧ x.im < (z.im : ℝ) + 1) := Iff.rfl

lemma measurableSet_gaussianCell (z : GaussianInt) : MeasurableSet (gaussianCell z) :=
  (measurableSet_Ico.prod measurableSet_Ico).preimage
    Complex.measurableEquivRealProd.measurable

lemma volume_gaussianCell (z : GaussianInt) : volume (gaussianCell z) = 1 := by
  rw [gaussianCell, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

lemma disjoint_gaussianCell {z w : GaussianInt} (h : z ≠ w) :
    Disjoint (gaussianCell z) (gaussianCell w) := by
  apply Set.disjoint_left.mpr
  intro x hz hw
  rw [mem_gaussianCell] at hz hw
  apply h
  apply Zsqrtd.ext
  · exact (Int.floor_eq_iff.mpr hz.1).symm.trans (Int.floor_eq_iff.mpr hw.1)
  · exact (Int.floor_eq_iff.mpr hz.2).symm.trans (Int.floor_eq_iff.mpr hw.2)

lemma dist_lt_two_of_mem_gaussianCell {z : GaussianInt} {x : ℂ}
    (hx : x ∈ gaussianCell z) : dist x (z : ℂ) < 2 := by
  rw [mem_gaussianCell] at hx
  have hre : 0 ≤ (x - (z : ℂ)).re := by
    simpa only [Complex.sub_re, ← GaussianInt.intCast_re] using sub_nonneg.mpr hx.1.1
  have him : 0 ≤ (x - (z : ℂ)).im := by
    simpa only [Complex.sub_im, ← GaussianInt.intCast_im] using sub_nonneg.mpr hx.2.1
  have hre' : (x - (z : ℂ)).re < 1 := by
    have h : x.re - (z.re : ℝ) < 1 := by linarith [hx.1.2]
    simpa only [Complex.sub_re, ← GaussianInt.intCast_re] using h
  have him' : (x - (z : ℂ)).im < 1 := by
    have h : x.im - (z.im : ℝ) < 1 := by linarith [hx.2.2]
    simpa only [Complex.sub_im, ← GaussianInt.intCast_im] using h
  have hn := Complex.norm_le_abs_re_add_abs_im (x - (z : ℂ))
  rw [abs_of_nonneg hre, abs_of_nonneg him] at hn
  rw [dist_eq_norm]
  linarith

lemma exists_mem_gaussianCell (x : ℂ) : ∃ z : GaussianInt, x ∈ gaussianCell z := by
  refine ⟨⟨⌊x.re⌋, ⌊x.im⌋⟩, ?_⟩
  exact ⟨⟨Int.floor_le _, Int.lt_floor_add_one _⟩,
    ⟨Int.floor_le _, Int.lt_floor_add_one _⟩⟩

/-- The exact union of the unit cells belonging to a finite collection of lattice points. -/
def gaussianCells (s : Finset GaussianInt) : Set ℂ := ⋃ z ∈ s, gaussianCell z

lemma volume_gaussianCells (s : Finset GaussianInt) :
    volume (gaussianCells s) = (s.card : ℝ≥0∞) := by
  classical
  rw [gaussianCells, measure_biUnion_finset
    (fun _ _ _ _ h => disjoint_gaussianCell h)
    (fun z _ => measurableSet_gaussianCell z)]
  simp [volume_gaussianCell]

lemma gaussianCells_subset_ball (c : ℂ) (r : ℝ) :
    gaussianCells (gaussianDisk c r) ⊆ Metric.ball c (r + 2) := by
  intro x hx
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
  have hz' := (mem_gaussianDisk c r z).mp hz
  have hx' := dist_lt_two_of_mem_gaussianCell hxz
  apply Metric.mem_ball.mpr
  calc
    dist x c ≤ dist x (z : ℂ) + dist (z : ℂ) c := dist_triangle _ _ _
    _ < r + 2 := by linarith

lemma ball_subset_gaussianCells (c : ℂ) (r : ℝ) :
    Metric.ball c (r - 2) ⊆ gaussianCells (gaussianDisk c r) := by
  intro x hx
  obtain ⟨z, hz⟩ := exists_mem_gaussianCell x
  apply Set.mem_iUnion₂.mpr
  refine ⟨z, (mem_gaussianDisk c r z).mpr ?_, hz⟩
  have hx' := Metric.mem_ball.mp hx
  have hz' := dist_lt_two_of_mem_gaussianCell hz
  calc
    dist (z : ℂ) c ≤ dist (z : ℂ) x + dist x c := dist_triangle _ _ _
    _ ≤ r := by rw [dist_comm (z : ℂ) x]; linarith

lemma real_volume_complex_ball (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.ball c r) = Real.pi * r ^ 2 := by
  rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp [mul_comm]

lemma gaussianDisk_card_upper (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ((gaussianDisk c r).card : ℝ) ≤ Real.pi * (r + 2) ^ 2 := by
  have h := measureReal_mono (μ := volume) (gaussianCells_subset_ball c r)
    (by rw [Complex.volume_ball]; finiteness)
  rw [real_volume_complex_ball c (r := r + 2) (by linarith)] at h
  simpa [Measure.real, volume_gaussianCells] using h

lemma gaussianDisk_card_lower (c : ℂ) {r : ℝ} (hr : 2 ≤ r) :
    Real.pi * (r - 2) ^ 2 ≤ ((gaussianDisk c r).card : ℝ) := by
  have h := measureReal_mono (μ := volume) (ball_subset_gaussianCells c r)
    (by rw [volume_gaussianCells]; exact ENNReal.natCast_ne_top _)
  rw [real_volume_complex_ball c (r := r - 2) (by linarith)] at h
  simpa [Measure.real, volume_gaussianCells] using h

/-- A uniform, explicit shifted Gauss disk estimate, including radius zero. -/
theorem gaussianDisk_card_error (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    |((gaussianDisk c r).card : ℝ) - Real.pi * r ^ 2| ≤
      (4 * Real.pi) * (r + 1) := by
  apply abs_le.mpr
  constructor
  · by_cases hr' : 2 ≤ r
    · have hl := gaussianDisk_card_lower c hr'
      nlinarith [Real.pi_pos]
    · have hc : 0 ≤ ((gaussianDisk c r).card : ℝ) := Nat.cast_nonneg _
      have hsq : r ^ 2 ≤ 4 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsq Real.pi_nonneg
      have hpr := mul_nonneg Real.pi_nonneg hr
      nlinarith
  · have hu := gaussianDisk_card_upper c hr
    nlinarith


/-- Gaussian integers in the affine ideal `a + d ℤ[i]` and in the specified disk.
The membership theorem below identifies this finite enumeration exactly when `d ≠ 0`. -/
def gaussianCosetDisk (a d : GaussianInt) (c : ℂ) (r : ℝ) : Finset GaussianInt := by
  classical
  exact (gaussianDisk ((c - (a : ℂ)) / (d : ℂ)) (r / ‖(d : ℂ)‖)).image
    (fun z => a + d * z)

lemma gaussian_affine_dist (a d z : GaussianInt) (hd : d ≠ 0) (c : ℂ) :
    dist ((a + d * z : GaussianInt) : ℂ) c =
      ‖(d : ℂ)‖ * dist (z : ℂ) ((c - (a : ℂ)) / (d : ℂ)) := by
  have hd' : (d : ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr hd
  have he :
      ((a + d * z : GaussianInt) : ℂ) - c =
        (d : ℂ) * ((z : ℂ) - (c - (a : ℂ)) / (d : ℂ)) := by
    rw [GaussianInt.toComplex_add, GaussianInt.toComplex_mul, mul_sub,
      mul_div_cancel₀ _ hd']
    ring
  rw [dist_eq_norm, he, norm_mul, dist_eq_norm]

lemma mem_gaussianCosetDisk (a d w : GaussianInt) (hd : d ≠ 0) (c : ℂ) (r : ℝ) :
    w ∈ gaussianCosetDisk a d c r ↔
      (∃ z : GaussianInt, a + d * z = w) ∧ dist (w : ℂ) c ≤ r := by
  classical
  have hn : 0 < ‖(d : ℂ)‖ :=
    norm_pos_iff.mpr (GaussianInt.toComplex_eq_zero.not.mpr hd)
  constructor
  · intro hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨⟨z, rfl⟩, ?_⟩
    rw [gaussian_affine_dist a d z hd c]
    have hz' := (mem_gaussianDisk _ _ z).mp hz
    exact (by simpa [mul_comm] using (le_div_iff₀ hn).mp hz')
  · rintro ⟨⟨z, rfl⟩, hz⟩
    apply Finset.mem_image.mpr
    refine ⟨z, (mem_gaussianDisk _ _ z).mpr ?_, rfl⟩
    rw [gaussian_affine_dist a d z hd c] at hz
    exact (le_div_iff₀ hn).mpr (by simpa [mul_comm] using hz)

lemma gaussianCosetDisk_card (a d : GaussianInt) (hd : d ≠ 0) (c : ℂ) (r : ℝ) :
    (gaussianCosetDisk a d c r).card =
      (gaussianDisk ((c - (a : ℂ)) / (d : ℂ)) (r / ‖(d : ℂ)‖)).card := by
  classical
  apply Finset.card_image_of_injective
  intro x y h
  exact mul_left_cancel₀ hd (add_left_cancel h)

/-- Uniform shifted-coset estimate obtained by the genuine similarity `z ↦ a + d*z`. -/
theorem gaussianCosetDisk_card_error (a d : GaussianInt) (hd : d ≠ 0)
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    |((gaussianCosetDisk a d c r).card : ℝ) -
      Real.pi * (r / ‖(d : ℂ)‖) ^ 2| ≤
        (4 * Real.pi) * (r / ‖(d : ℂ)‖ + 1) := by
  rw [gaussianCosetDisk_card a d hd c r]
  exact gaussianDisk_card_error _ (div_nonneg hr (norm_nonneg _))

end DistanceCounts
end
end

-- Source: DistanceCounts/PairModulus.lean
section
noncomputable section

namespace DistanceCounts.PairModulus

open CoarseGrid OffsetSeparation GaussianResidues

variable {t : ℕ}

/-- Only the uncancelled row and column primes occur. -/
def primeSet (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t) : Finset ℕ :=
  (pairSupport b c).image p

def modulus (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t) : ℕ :=
  ∏ i ∈ pairSupport b c, p i

def numerator (p : Fin t ⊕ Fin t → ℕ) (z : Fin t ⊕ Fin t → GaussianInt)
    (b c : Fin t × Fin t) : GaussianInt :=
  ∑ i ∈ pairSupport b c,
    (modulus p b c / p i : ℕ) * (pairSign b c i : GaussianInt) * z i


theorem modulus_pos (p : Fin t ⊕ Fin t → ℕ) (hp : ∀ i, (p i).Prime)
    (b c : Fin t × Fin t) : 0 < modulus p b c :=
  Finset.prod_pos fun i _ => (hp i).pos

theorem primeSet_prime (p : Fin t ⊕ Fin t → ℕ) (hp : ∀ i, (p i).Prime)
    (b c : Fin t × Fin t) : ∀ r ∈ primeSet p b c, r.Prime := by
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  exact hp i

theorem primeSet_card_le_four (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t) :
    (primeSet p b c).card ≤ 4 :=
  (Finset.card_image_le).trans (pairSupport_card_le_four b c)

theorem modulus_eq_primeSet_prod (p : Fin t ⊕ Fin t → ℕ)
    (hd : Function.Injective p) (b c : Fin t × Fin t) :
    modulus p b c = ∏ r ∈ primeSet p b c, r := by
  symm
  exact Finset.prod_image hd.injOn


theorem pairSign_zero_of_not_mem (b c : Fin t × Fin t) (k : Fin t ⊕ Fin t)
    (hk : k ∉ pairSupport b c) : pairSign b c k = 0 := by
  simp only [pairSupport, Finset.mem_union, Finset.mem_sdiff] at hk
  by_cases hb : k ∈ blockAxes b <;> by_cases hc : k ∈ blockAxes c <;>
    simp_all [pairSign]

theorem pairSign_eq_one_or_neg_one (b c : Fin t × Fin t) (k : Fin t ⊕ Fin t)
    (hk : k ∈ pairSupport b c) : pairSign b c k = 1 ∨ pairSign b c k = -1 := by
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨hb, hc⟩ := Finset.mem_sdiff.mp hk
    simp [pairSign, hb, hc]
  · obtain ⟨hc, hb⟩ := Finset.mem_sdiff.mp hk
    simp [pairSign, hb, hc]

theorem signed_sum (b c : Fin t × Fin t) (r : Fin t ⊕ Fin t → ℚ) :
    (∑ k ∈ pairSupport b c, (pairSign b c k : ℚ) * r k) =
      r (.inl b.1) + r (.inr b.2) - r (.inl c.1) - r (.inr c.2) := by
  classical
  rw [Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
    rw [pairSign_zero_of_not_mem b c k hk]; simp)]
  have hs (k : Fin t ⊕ Fin t) : pairSign b c k =
      pairCoefficient (.inl b.1) (.inr b.2) (.inl c.1) (.inr c.2) k := by
    cases k with
    | inl k => simp [pairSign, blockAxes, pairCoefficient]
    | inr k => simp [pairSign, blockAxes, pairCoefficient]
  simp_rw [hs]
  exact pairCoefficient_sum r _ _ _ _

theorem prime_dvd_modulus (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t)
    (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) : p k ∣ modulus p b c :=
  Finset.dvd_prod_of_mem p hk

theorem cofactor_mul (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t)
    (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) :
    modulus p b c / p k * p k = modulus p b c :=
  Nat.div_mul_cancel (prime_dvd_modulus p b c k hk)

private theorem rationalOffset_sum {I : Type*} (s : Finset I)
    (f : I → GaussianInt) (q : ℕ) :
    rationalOffset (∑ i ∈ s, f i) q = ∑ i ∈ s, rationalOffset (f i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rationalOffset]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [show rationalOffset (f i + ∑ j ∈ s, f j) q =
      rationalOffset (f i) q + rationalOffset (∑ j ∈ s, f j) q by
        ext <;> simp [rationalOffset, add_div]]
    rw [ih]

private theorem fst_sum {I : Type*} (s : Finset I) (f : I → ℚ × ℚ) :
    (∑ k ∈ s, f k).1 = ∑ k ∈ s, (f k).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp [Finset.sum_insert, hk, ih]

private theorem snd_sum {I : Type*} (s : Finset I) (f : I → ℚ × ℚ) :
    (∑ k ∈ s, f k).2 = ∑ k ∈ s, (f k).2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp [Finset.sum_insert, hk, ih]

theorem rationalOffset_numerator (p : Fin t ⊕ Fin t → ℕ)
    (z : Fin t ⊕ Fin t → GaussianInt) (hp : ∀ i, (p i).Prime)
    (b c : Fin t × Fin t) :
    rationalOffset (numerator p z b c) (modulus p b c) =
      rationalOffset (z (.inl b.1)) (p (.inl b.1)) +
      rationalOffset (z (.inr b.2)) (p (.inr b.2)) -
      rationalOffset (z (.inl c.1)) (p (.inl c.1)) -
      rationalOffset (z (.inr c.2)) (p (.inr c.2)) := by
  have hq : (modulus p b c : ℚ) ≠ 0 := by
    exact_mod_cast (modulus_pos p hp b c).ne'
  have ht (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) (a : ℤ) :
      ((modulus p b c / p k : ℕ) : ℚ) * pairSign b c k * a / modulus p b c =
        (pairSign b c k : ℚ) * ((a : ℚ) / p k) := by
    have hpk : (p k : ℚ) ≠ 0 := by exact_mod_cast (hp k).ne_zero
    have hm : ((modulus p b c / p k : ℕ) : ℚ) * p k = modulus p b c := by
      exact_mod_cast cofactor_mul p b c k hk
    field_simp [hq, hpk]
    nlinarith [congrArg (fun x : ℚ => (pairSign b c k : ℚ) * (a : ℚ) * x) hm]
  rw [numerator, rationalOffset_sum]
  apply Prod.ext
  · simp only [fst_sum, Prod.fst_add, Prod.fst_sub, rationalOffset,
      Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
      Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero,
      Int.cast_mul, Int.cast_natCast]
    rw [Finset.sum_congr rfl (fun k hk => ht k hk (z k).re)]
    exact signed_sum b c (fun k => (z k).re / (p k : ℚ))
  · simp only [snd_sum, Prod.snd_add, Prod.snd_sub, rationalOffset,
      Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
      Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero,
      Int.cast_mul, Int.cast_natCast]
    rw [Finset.sum_congr rfl (fun k hk => ht k hk (z k).im)]
    exact signed_sum b c (fun k => (z k).im / (p k : ℚ))


theorem cofactor_eq_prod_erase (p : Fin t ⊕ Fin t → ℕ)
    (hp : ∀ i, (p i).Prime) (b c : Fin t × Fin t)
    (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) :
    modulus p b c / p k = ∏ r ∈ (pairSupport b c).erase k, p r := by
  apply Nat.div_eq_of_eq_mul_left (hp k).pos
  simpa [modulus, mul_comm] using
    (Finset.mul_prod_erase (pairSupport b c) p hk).symm

theorem cofactor_isUnit (p : Fin t ⊕ Fin t → ℕ)
    (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (b c : Fin t × Fin t) (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) :
    IsUnit ((modulus p b c / p k : ℕ) : Residue (p k)) := by
  rw [modulus_eq_primeSet_prod p hd]
  exact GaussianUnitCRT.cofactor_isUnit (primeSet p b c) (primeSet_prime p hp b c)
    ⟨p k, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩

theorem sign_isUnit (p : Fin t ⊕ Fin t → ℕ)
    (b c : Fin t × Fin t) (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) :
    IsUnit (pairSign b c k : Residue (p k)) := by
  rcases pairSign_eq_one_or_neg_one b c k hk with h | h <;> rw [h] <;> simp

/-- The sign and the cofactor are genuine units, in the prescribed orientation. -/
theorem signed_cofactor_isUnit (p : Fin t ⊕ Fin t → ℕ)
    (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (b c : Fin t × Fin t) (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) :
    IsUnit (((modulus p b c / p k : ℕ) : Residue (p k)) * pairSign b c k) :=
  (cofactor_isUnit p hp hd b c k hk).mul (sign_isUnit p b c k hk)

theorem numerator_residue (p : Fin t ⊕ Fin t → ℕ)
    (z : Fin t ⊕ Fin t → GaussianInt) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (b c : Fin t × Fin t)
    (k : Fin t ⊕ Fin t) (hk : k ∈ pairSupport b c) :
    GaussianNorm.residue (p k) (numerator p z b c) =
      ((modulus p b c / p k : ℕ) : Residue (p k)) *
        pairSign b c k * GaussianNorm.residue (p k) (z k) := by
  classical
  change (Ideal.Quotient.mk _ : GaussianInt →+* Residue (p k))
    (∑ r ∈ pairSupport b c, _) = _
  rw [map_sum]
  rw [Finset.sum_eq_single k]
  · simp only [map_mul, map_natCast, map_intCast, GaussianNorm.residue]
  · intro r hr hrk
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    have hdvd : p k ∣ modulus p b c / p r := by
      rw [cofactor_eq_prod_erase p hp b c r hr]
      exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hrk.symm, hk⟩)
    obtain ⟨a, ha⟩ := hdvd
    have hc : (p k : GaussianInt) ∣ (modulus p b c / p r : ℕ) := by
      exact ⟨(a : GaussianInt), by exact_mod_cast ha⟩
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _
  · exact fun h => (h hk).elim


theorem numerator_isUnit (p : Fin t ⊕ Fin t → ℕ)
    (z : Fin t ⊕ Fin t → GaussianInt) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (b c : Fin t × Fin t)
    (hz : ∀ k ∈ pairSupport b c, IsUnit (GaussianNorm.residue (p k) (z k))) :
    IsUnit (GaussianNorm.residue (modulus p b c) (numerator p z b c)) := by
  rw [modulus_eq_primeSet_prod p hd]
  let e := GaussianUnitCRT.crtEquiv (primeSet p b c) (primeSet_prime p hp b c)
  have hu : IsUnit (e (GaussianNorm.residue (∏ r ∈ primeSet p b c, r)
      (numerator p z b c))) := by
    apply Pi.isUnit_iff.mpr
    intro r
    change IsUnit (reduce (Finset.dvd_prod_of_mem (fun x : ℕ => x) r.2)
      (GaussianNorm.residue (∏ r ∈ primeSet p b c, r) (numerator p z b c)))
    rw [reduce_residue]
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp r.2
    cases r with
    | mk r hr =>
      dsimp at he ⊢
      subst r
      rw [numerator_residue p z hp hd b c k hk]
      exact (signed_cofactor_isUnit p hp hd b c k hk).mul (hz k hk)
  have hn := hu.map e.symm.toMonoidHom
  change IsUnit (e.symm (e (GaussianNorm.residue (∏ r ∈ primeSet p b c, r)
    (numerator p z b c)))) at hn
  simpa only [RingEquiv.symm_apply_apply] using hn


/-- Independent local unit choices indexed by the actual uncancelled axes. -/
abbrev LocalUnits (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t) :=
  ∀ k : pairSupport b c, (Residue (p k.1))ˣ

def localLift (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t)
    (u : LocalUnits p b c) (k : Fin t ⊕ Fin t) : GaussianInt :=
  if hk : k ∈ pairSupport b c then BoundedResidueLift.lift (p k) (u ⟨k, hk⟩) else 0

theorem localLift_residue (p : Fin t ⊕ Fin t → ℕ) (hp : ∀ i, (p i).Prime)
    (b c : Fin t × Fin t) (u : LocalUnits p b c) (k : pairSupport b c) :
    GaussianNorm.residue (p k.1) (localLift p b c u k.1) =
      (u k : Residue (p k.1)) := by
  simp only [localLift, dif_pos k.2]
  exact BoundedResidueLift.residue_lift _ (hp k.1).pos _

/-- This lands in the actual global Gaussian quotient, not a tuple surrogate. -/
def localChoiceMap (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t)
    (u : LocalUnits p b c) : Residue (modulus p b c) :=
  GaussianNorm.residue (modulus p b c) (numerator p (localLift p b c u) b c)


theorem localChoiceMap_injective (p : Fin t ⊕ Fin t → ℕ)
    (hp : ∀ i, (p i).Prime) (hd : Function.Injective p) (b c : Fin t × Fin t) :
    Function.Injective (localChoiceMap p b c) := by
  intro u v huv
  funext k
  apply Units.ext
  have h := congrArg (reduce (prime_dvd_modulus p b c k.1 k.2)) huv
  change reduce _ (GaussianNorm.residue _ _) = reduce _ (GaussianNorm.residue _ _) at h
  rw [reduce_residue, reduce_residue, numerator_residue p _ hp hd b c k.1 k.2,
    numerator_residue p _ hp hd b c k.1 k.2,
    localLift_residue p hp b c u k, localLift_residue p hp b c v k] at h
  exact (signed_cofactor_isUnit p hp hd b c k.1 k.2).mul_left_cancel h


/-- The CRT map does not depend on which Gaussian representatives are used. -/
theorem localChoiceMap_eq_numerator (p : Fin t ⊕ Fin t → ℕ)
    (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (b c : Fin t × Fin t) (u : LocalUnits p b c)
    (z : Fin t ⊕ Fin t → GaussianInt)
    (hz : ∀ k : pairSupport b c, GaussianNorm.residue (p k.1) (z k.1) =
      (u k : Residue (p k.1))) :
    localChoiceMap p b c u = GaussianNorm.residue (modulus p b c) (numerator p z b c) := by
  unfold localChoiceMap
  rw [modulus_eq_primeSet_prod p hd]
  apply crtReduction_injective (primeSet p b c) (primeSet_prime p hp b c)
  funext r
  change reduce _ (GaussianNorm.residue _ _) = reduce _ (GaussianNorm.residue _ _)
  rw [reduce_residue, reduce_residue]
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp r.2
  cases r with
  | mk r hr =>
    dsimp at he ⊢
    subst r
    rw [numerator_residue p _ hp hd b c k hk, numerator_residue p _ hp hd b c k hk,
      localLift_residue p hp b c u ⟨k, hk⟩, hz ⟨k, hk⟩]


/-- The bounded-lift hypothesis is on the physical rational offsets. -/
def BoundedOffsets (p : Fin t ⊕ Fin t → ℕ) (z : Fin t ⊕ Fin t → GaussianInt) : Prop :=
  ∀ k, (0 ≤ (rationalOffset (z k) (p k)).1 ∧
      (rationalOffset (z k) (p k)).1 < 1) ∧
    (0 ≤ (rationalOffset (z k) (p k)).2 ∧
      (rationalOffset (z k) (p k)).2 < 1)

theorem boundedOffsets_lift (p : Fin t ⊕ Fin t → ℕ) (hp : ∀ i, (p i).Prime)
    (u : ∀ k, Residue (p k)) :
    BoundedOffsets p (fun k => BoundedResidueLift.lift (p k) (u k)) :=
  fun k => BoundedResidueLift.rationalOffset_bounds (p k) (hp k).pos (u k)


end DistanceCounts.PairModulus
end
end

-- Source: DistanceCounts/Degrees.lean
section
/-! The exact cancelled-index threshold degrees and their distinct good-block values. -/

noncomputable section

namespace DistanceCounts


/-- The actual high-neighbor rule, with shared row and column indices cancelled. -/
def highTargets (s a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (2 * s)) ×ˢ (Finset.range (2 * s))).filter fun cd =>
    a ≠ cd.1 ∧
      (if b = cd.2 then 2 * s ≤ a + cd.1
       else (2 * s) ^ 2 ≤ (a + cd.1) * (2 * s) + b + cd.2)

lemma threshold_iff {t a b c d : ℕ} (ht : 0 < t)
    (hb : b < t) (hd : d < t) :
    t ^ 2 ≤ (a + c) * t + b + d ↔
      t ≤ a + c ∨ (a + c + 1 = t ∧ t ≤ b + d) := by
  constructor
  · intro h
    by_cases hlarge : t ≤ a + c
    · exact Or.inl hlarge
    · right
      have hedge : a + c + 1 = t := by
        by_contra hne
        have hgap : a + c + 2 ≤ t := by omega
        have hm := Nat.mul_le_mul_right t hgap
        nlinarith
      constructor
      · exact hedge
      · nlinarith
  · rintro (h | ⟨he, hb⟩)
    · have hm := Nat.mul_le_mul_right t h
      nlinarith
    · nlinarith

lemma high_rule_iff {t a b c d : ℕ} (ht : 0 < t)
    (hb : b < t) (hd : d < t) :
    (if b = d then t ≤ a + c else t ^ 2 ≤ (a + c) * t + b + d) ↔
      t ≤ a + c ∨ (a + c + 1 = t ∧ t ≤ b + d ∧ b ≠ d) := by
  by_cases hbd : b = d
  · simp [hbd]
  · simp only [hbd, if_false, threshold_iff ht hb hd]
    tauto


end DistanceCounts
end
end

-- Source: DistanceCounts/ThresholdWeights.lean
section
noncomputable section

namespace DistanceCounts.ThresholdWeights

/-- The first row and first column deliberately have the same positive weight. -/
def weight {t : ℕ} : Fin t ⊕ Fin t → ℝ
  | .inl a => Real.log 2 * ((a.val : ℝ) * t + 1 / 8) / (t : ℝ) ^ 2
  | .inr b => Real.log 2 * ((b.val : ℝ) + 1 / 8) / (t : ℝ) ^ 2

theorem weight_pos {t : ℕ} (ht : 0 < t) (i : Fin t ⊕ Fin t) :
    0 < weight i := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  cases i with
  | inl a =>
    exact div_pos (mul_pos hlog (by positivity)) (pow_pos ht' 2)
  | inr b =>
    exact div_pos (mul_pos hlog (by positivity)) (pow_pos ht' 2)

/-- Only indices surviving cancellation contribute to the modulus exponent. -/
def pairExponent {t : ℕ} (b c : Fin t × Fin t) : ℝ :=
  ∑ i ∈ CoarseGrid.pairSupport b c, weight i

/-- Row and column cancellations are independent, including the self block. -/
theorem pairExponent_eq {t : ℕ} (b c : Fin t × Fin t) :
    pairExponent b c =
      (if b.1 = c.1 then 0 else weight (.inl b.1) + weight (.inl c.1)) +
      (if b.2 = c.2 then 0 else weight (.inr b.2) + weight (.inr c.2)) := by
  classical
  have hsupport : CoarseGrid.pairSupport b c =
      (if b.1 = c.1 then ∅ else {Sum.inl b.1, Sum.inl c.1}) ∪
      (if b.2 = c.2 then ∅ else {Sum.inr b.2, Sum.inr c.2}) := by
    ext i
    cases i <;> by_cases hr : b.1 = c.1 <;> by_cases hc : b.2 = c.2 <;>
      simp [CoarseGrid.pairSupport, CoarseGrid.blockAxes, hr, hc] <;> aesop
  have hdisj : Disjoint
      (if b.1 = c.1 then (∅ : Finset (Fin t ⊕ Fin t)) else {Sum.inl b.1, Sum.inl c.1})
      (if b.2 = c.2 then ∅ else {Sum.inr b.2, Sum.inr c.2}) := by
    apply Finset.disjoint_left.mpr
    intro i
    cases i <;> by_cases hr : b.1 = c.1 <;> by_cases hc : b.2 = c.2 <;>
      simp [hr, hc]
  unfold pairExponent
  rw [hsupport, Finset.sum_union hdisj]
  by_cases hr : b.1 = c.1 <;> by_cases hc : b.2 = c.2 <;>
    simp [hr, hc, eq_comm]


/-- An integer part plus a quarter for each uncancelled pair of axes. -/
def pairNumerator {t : ℕ} (b c : Fin t × Fin t) : ℝ :=
  (if b.1 = c.1 then 0 else ((b.1.val : ℝ) + c.1.val) * t + 1 / 4) +
  (if b.2 = c.2 then 0 else (b.2.val : ℝ) + c.2.val + 1 / 4)

theorem pairExponent_formula {t : ℕ} (b c : Fin t × Fin t) :
    pairExponent b c = Real.log 2 * pairNumerator b c / (t : ℝ) ^ 2 := by
  rw [pairExponent_eq]
  unfold pairNumerator
  split_ifs <;> simp [weight] <;> ring

private theorem shifted_nat_threshold (n m : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1) :
    (n : ℝ) + δ ≠ (m : ℝ) ∧ ((m : ℝ) < n + δ ↔ m ≤ n) := by
  by_cases h : m ≤ n
  · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
    constructor
    · linarith
    · constructor
      · intro _; exact h
      · intro _; linarith
  · have hn : n + 1 ≤ m := by omega
    have hn' : (n : ℝ) + 1 ≤ m := by exact_mod_cast hn
    constructor
    · linarith
    · constructor
      · intro hh; linarith
      · intro hh; exact (h hh).elim

/-- Arithmetic classification, proved from the actual cancelled numerator. -/
theorem pairNumerator_threshold {s : ℕ} (hs : 0 < s)
    (b c : Fin (2 * s) × Fin (2 * s)) :
    pairNumerator b c ≠ ((2 * s : ℕ) : ℝ) ^ 2 ∧
      ((((2 * s : ℕ) : ℝ) ^ 2 < pairNumerator b c) ↔
        (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val) := by
  have ht : 0 < 2 * s := by omega
  have ht' : (2 : ℝ) ≤ (2 * s : ℕ) := by exact_mod_cast (show 2 ≤ 2 * s by omega)
  have hrval : b.1.val = c.1.val ↔ b.1 = c.1 := Fin.val_inj
  have hcval : b.2.val = c.2.val ↔ b.2 = c.2 := Fin.val_inj
  by_cases hr : b.1 = c.1
  · have hlow : pairNumerator b c < ((2 * s : ℕ) : ℝ) ^ 2 := by
      by_cases hc : b.2 = c.2
      · simp only [pairNumerator, hr, hc, if_true, zero_add]
        positivity
      · have hsum : b.2.val + c.2.val + 2 ≤ 2 * (2 * s) := by
          have hb := b.2.isLt
          have hc' := c.2.isLt
          omega
        have hsum' : (b.2.val : ℝ) + c.2.val + 2 ≤ 2 * (2 * s : ℕ) := by
          exact_mod_cast hsum
        simp only [pairNumerator, hr, hc, if_true, if_false, zero_add]
        nlinarith
    refine ⟨ne_of_lt hlow, ?_⟩
    have hnot : (c.1.val, c.2.val) ∉ DistanceCounts.highTargets s b.1.val b.2.val := by
      simp [DistanceCounts.highTargets, hrval, hr]
    exact iff_of_false (not_lt_of_ge hlow.le) hnot
  · by_cases hc : b.2 = c.2
    · have hshift := shifted_nat_threshold
        ((b.1.val + c.1.val) * (2 * s)) ((2 * s) ^ 2)
        (δ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      have hnum : pairNumerator b c =
          (((b.1.val + c.1.val) * (2 * s) : ℕ) : ℝ) + 1 / 4 := by
        simp [pairNumerator, hr, hc]
      have hmul : (2 * s) ^ 2 ≤ (b.1.val + c.1.val) * (2 * s) ↔
          2 * s ≤ b.1.val + c.1.val := by
        constructor <;> intro h
        · by_contra hn
          have hlt : b.1.val + c.1.val < 2 * s := by omega
          have hm := Nat.mul_lt_mul_of_pos_right hlt ht
          nlinarith
        · have hm := Nat.mul_le_mul_right (2 * s) h
          nlinarith
      have hmem : (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val ↔
          2 * s ≤ b.1.val + c.1.val := by
        simp [DistanceCounts.highTargets, c.1.isLt, c.2.isLt, hrval, hcval, hr, hc]
      rw [hnum]
      rw [Nat.cast_pow] at hshift
      exact ⟨hshift.1, hshift.2.trans (hmul.trans hmem.symm)⟩
    · have hshift := shifted_nat_threshold
        ((b.1.val + c.1.val) * (2 * s) + b.2.val + c.2.val) ((2 * s) ^ 2)
        (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      have hnum : pairNumerator b c =
          (((b.1.val + c.1.val) * (2 * s) + b.2.val + c.2.val : ℕ) : ℝ) + 1 / 2 := by
        simp only [pairNumerator, hr, hc, if_false, Nat.cast_add, Nat.cast_mul]
        ring
      have hmem : (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val ↔
          (2 * s) ^ 2 ≤ (b.1.val + c.1.val) * (2 * s) + b.2.val + c.2.val := by
        simp [DistanceCounts.highTargets, c.1.isLt, c.2.isLt, hrval, hcval, hr, hc]
      rw [hnum]
      rw [Nat.cast_pow] at hshift
      exact ⟨hshift.1, hshift.2.trans hmem.symm⟩

theorem pairExponent_ne_log_two {s : ℕ} (hs : 0 < s)
    (b c : Fin (2 * s) × Fin (2 * s)) : pairExponent b c ≠ Real.log 2 := by
  have hden : (0 : ℝ) < ((2 * s : ℕ) : ℝ) ^ 2 := by positivity
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  intro heq
  rw [pairExponent_formula, div_eq_iff hden.ne'] at heq
  exact (pairNumerator_threshold hs b c).1 ((mul_left_cancel₀ hlog.ne') heq)

/-- Exact high/low classification; no geometric threshold assumption is needed. -/
theorem log_two_lt_pairExponent_iff {s : ℕ} (hs : 0 < s)
    (b c : Fin (2 * s) × Fin (2 * s)) :
    Real.log 2 < pairExponent b c ↔
      (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val := by
  have hden : (0 : ℝ) < ((2 * s : ℕ) : ℝ) ^ 2 := by positivity
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [pairExponent_formula, lt_div_iff₀ hden, mul_lt_mul_iff_right₀ hlog]
  exact (pairNumerator_threshold hs b c).2

theorem pairExponent_lt_log_two_iff {s : ℕ} (hs : 0 < s)
    (b c : Fin (2 * s) × Fin (2 * s)) :
    pairExponent b c < Real.log 2 ↔
      (c.1.val, c.2.val) ∉ DistanceCounts.highTargets s b.1.val b.2.val := by
  rw [← log_two_lt_pairExponent_iff hs b c]
  exact ⟨fun h => not_lt_of_ge h.le, fun h =>
    lt_of_le_of_ne (le_of_not_gt h) (pairExponent_ne_log_two hs b c)⟩


end DistanceCounts.ThresholdWeights
end
end

-- Source: DistanceCounts/RepresentationCount.lean
section
/-! Finite Gaussian norm circles, their unit orbits, and prime-norm reductions. -/

noncomputable section

namespace DistanceCounts

/-- The actual Gaussian integers on a norm circle, enumerated inside a genuine disk. -/
def normCircle (n : ℕ) : Finset GaussianInt := by
  classical
  exact (gaussianDisk 0 (Real.sqrt n)).filter (fun z => z.norm.natAbs = n)

lemma gaussian_complex_norm (z : GaussianInt) :
    ‖(z : ℂ)‖ = Real.sqrt (z.norm.natAbs : ℝ) := by
  rw [Complex.norm_def, ← GaussianInt.intCast_real_norm]
  congr 1
  simpa only [Int.cast_natCast] using
    congrArg (fun n : ℤ => (n : ℝ)) (GaussianInt.abs_natCast_norm z).symm

lemma mem_normCircle (n : ℕ) (z : GaussianInt) :
    z ∈ normCircle n ↔ z.norm.natAbs = n := by
  classical
  constructor
  · exact fun hz => (Finset.mem_filter.mp hz).2
  · intro hz
    apply Finset.mem_filter.mpr
    refine ⟨(mem_gaussianDisk _ _ _).mpr ?_, hz⟩
    simp only [dist_zero_right, gaussian_complex_norm, hz, le_refl]

lemma mem_normCircle_iff_norm (n : ℕ) (z : GaussianInt) :
    z ∈ normCircle n ↔ z.norm = (n : ℤ) := by
  rw [mem_normCircle, ← Int.natCast_inj, GaussianInt.abs_natCast_norm]

lemma self_mem_normCircle (z : GaussianInt) : z ∈ normCircle z.norm.natAbs :=
  (mem_normCircle _ _).mpr rfl


lemma ne_zero_of_mem_normCircle {n : ℕ} (hn : n ≠ 0) {z : GaussianInt}
    (hz : z ∈ normCircle n) : z ≠ 0 := by
  intro h
  subst z
  have := (mem_normCircle n 0).mp hz
  exact hn (by simpa using this.symm)

/-- This transfers the existing sum-of-two-squares theorem to the finite circle,
including its special convention at zero. -/
lemma normCircle_nonempty_iff_sum_two_squares (n : ℕ) :
    (normCircle n).Nonempty ↔ ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.re.natAbs, z.im.natAbs, ?_⟩
    rw [← (mem_normCircle _ _).mp hz, GaussianInt.natAbs_norm_eq]
    ring
  · rintro ⟨a, b, hab⟩
    refine ⟨⟨a, b⟩, (mem_normCircle _ _).mpr ?_⟩
    simpa [GaussianInt.natAbs_norm_eq, pow_two] using hab.symm

lemma normCircle_nonempty_iff (n : ℕ) :
    (normCircle n).Nonempty ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
  rw [normCircle_nonempty_iff_sum_two_squares, Nat.eq_sq_add_sq_iff]

/-- There are exactly four norm-one elements; no quotient or unit multiplicity
is silently discarded. -/
lemma normCircle_one :
    normCircle 1 = {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩} := by
  classical
  ext z
  rcases z with ⟨a, b⟩
  constructor
  · intro hz
    have h : a * a + b * b = 1 := by
      simpa [Zsqrtd.norm] using (mem_normCircle_iff_norm 1 ⟨a, b⟩).mp hz
    have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b]
    have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a]
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    interval_cases a <;> interval_cases b <;> norm_num at *
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz <;> cases hz <;>
      apply (mem_normCircle_iff_norm _ _).mpr <;> norm_num [Zsqrtd.norm]

lemma normCircle_one_card : (normCircle 1).card = 4 := by
  classical
  rw [normCircle_one]
  norm_num [Zsqrtd.ext_iff]


lemma mem_normCircle_one_iff (z : GaussianInt) : z ∈ normCircle 1 ↔ IsUnit z := by
  rw [mem_normCircle, Zsqrtd.norm_eq_one_iff]

/-- All four associates of an element, represented as actual Gaussian integers. -/
def normUnitOrbit (z : GaussianInt) : Finset GaussianInt := by
  classical
  exact (normCircle 1).image (fun u => z * u)

lemma mem_normUnitOrbit (z w : GaussianInt) :
    w ∈ normUnitOrbit z ↔ Associated z w := by
  classical
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact associated_mul_unit_right z u ((mem_normCircle_one_iff u).mp hu)
  · rintro ⟨u, hu⟩
    exact Finset.mem_image.mpr
      ⟨u, (mem_normCircle_one_iff _).mpr u.isUnit, hu⟩

lemma normUnitOrbit_card {z : GaussianInt} (hz : z ≠ 0) :
    (normUnitOrbit z).card = 4 := by
  classical
  rw [normUnitOrbit, Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ hz h),
    normCircle_one_card]


open scoped Classical in


/-- Multiplication by a nonzero Gaussian integer embeds every smaller norm circle. -/
lemma normCircle_mul_image_subset (a : GaussianInt) (n : ℕ) :
    (normCircle n).image (fun w => a * w) ⊆ normCircle (a.norm.natAbs * n) := by
  classical
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  rw [mem_normCircle, Zsqrtd.norm_mul, Int.natAbs_mul, (mem_normCircle _ _).mp hw]


/-- A Gaussian element of rational prime norm is genuinely a Gaussian prime. -/
lemma gaussian_prime_of_prime_norm {z : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hz : z.norm.natAbs = p) : Prime z := by
  apply irreducible_iff_prime.mp
  constructor
  · intro hu
    have := (Zsqrtd.norm_eq_one_iff.mpr hu).symm.trans hz
    exact hp.ne_one this.symm
  · intro a b hab
    have hnorm : p = a.norm.natAbs * b.norm.natAbs := by
      rw [← hz, hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    rcases hp.isUnit_or_isUnit hnorm with ha | hb
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp (Nat.isUnit_iff.mp ha))
    · exact Or.inr (Zsqrtd.norm_eq_one_iff.mp (Nat.isUnit_iff.mp hb))

/-- Every representation of a prime norm lies in one of the two conjugate
associate classes. This is a UFD consequence, not a counting assumption. -/
lemma normCircle_prime_eq_orbits {p : ℕ} (hp : p.Prime) {z : GaussianInt}
    (hz : z.norm.natAbs = p) :
    normCircle p = normUnitOrbit z ∪ normUnitOrbit (star z) := by
  classical
  ext w
  rw [Finset.mem_union, mem_normUnitOrbit, mem_normUnitOrbit]
  constructor
  · intro hw
    have hw' := (mem_normCircle _ _).mp hw
    have hwp := gaussian_prime_of_prime_norm hp hw'
    have hzp := gaussian_prime_of_prime_norm hp hz
    have hcp := gaussian_prime_of_prime_norm hp (show (star z).norm.natAbs = p by simpa using hz)
    have he : (w.norm : GaussianInt) = (z.norm : GaussianInt) := by
      have he' : w.norm = z.norm := by
        rw [← GaussianInt.abs_natCast_norm w, ← GaussianInt.abs_natCast_norm z, hw', hz]
      rw [he']
    have hd : w ∣ z * star z := by
      rw [← Zsqrtd.norm_eq_mul_conj, ← he, Zsqrtd.norm_eq_mul_conj]
      exact dvd_mul_right _ _
    rcases hwp.dvd_or_dvd hd with hd | hd
    · exact Or.inl (hwp.associated_of_dvd hzp hd).symm
    · exact Or.inr (hwp.associated_of_dvd hcp hd).symm
  · intro hw
    apply (mem_normCircle _ _).mpr
    rcases hw with hw | hw
    · exact (congrArg Int.natAbs (Zsqrtd.norm_eq_of_associated (by norm_num) hw)).symm.trans hz
    · simpa using (congrArg Int.natAbs
        (Zsqrtd.norm_eq_of_associated (by norm_num) hw)).symm.trans
          (show (star z).norm.natAbs = p by simpa using hz)

lemma normCircle_prime_card_le_eight {p : ℕ} (hp : p.Prime) :
    (normCircle p).card ≤ 8 := by
  classical
  by_cases h : (normCircle p).Nonempty
  · obtain ⟨z, hz⟩ := h
    have hz0 := ne_zero_of_mem_normCircle hp.ne_zero hz
    rw [normCircle_prime_eq_orbits hp ((mem_normCircle _ _).mp hz)]
    calc
      _ ≤ (normUnitOrbit z).card + (normUnitOrbit (star z)).card := Finset.card_union_le _ _
      _ = 8 := by rw [normUnitOrbit_card hz0, normUnitOrbit_card (by simpa using hz0)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]
    exact Nat.zero_le _

lemma prime_norm_re_ne_zero {p : ℕ} (hp : p.Prime) {z : GaussianInt}
    (hz : z.norm.natAbs = p) : z.re ≠ 0 := by
  intro hre
  apply hp.prime.not_isSquare
  refine ⟨z.im.natAbs, ?_⟩
  simpa [GaussianInt.natAbs_norm_eq, hre] using hz.symm

lemma prime_norm_im_ne_zero {p : ℕ} (hp : p.Prime) {z : GaussianInt}
    (hz : z.norm.natAbs = p) : z.im ≠ 0 := by
  intro him
  apply hp.prime.not_isSquare
  refine ⟨z.re.natAbs, ?_⟩
  simpa [GaussianInt.natAbs_norm_eq, him] using hz.symm

/-- At a split rational prime the two conjugate Gaussian prime classes are
distinct. The four units are checked explicitly, including the axis cases. -/
lemma not_associated_conj_of_split_prime_norm {p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) {z : GaussianInt} (hz : z.norm.natAbs = p) :
    ¬Associated z (star z) := by
  rintro ⟨u, hu⟩
  have hunit := (mem_normCircle_one_iff (u : GaussianInt)).mpr u.isUnit
  rw [normCircle_one] at hunit
  simp only [Finset.mem_insert, Finset.mem_singleton] at hunit
  have hnorm : z.re * z.re + z.im * z.im = (p : ℤ) := by
    have h := (mem_normCircle_iff_norm p z).mp ((mem_normCircle p z).mpr hz)
    simpa [Zsqrtd.norm] using h
  have hp4' : (p : ℤ) % 4 = 1 := by exact_mod_cast hp4
  rcases hunit with hunit | hunit | hunit | hunit
  · have him := congrArg Zsqrtd.im hu
    simp [hunit] at him
    exact prime_norm_im_ne_zero hp hz (by omega)
  · have hre := congrArg Zsqrtd.re hu
    simp [hunit] at hre
    exact prime_norm_re_ne_zero hp hz (by omega)
  · have hre := congrArg Zsqrtd.re hu
    simp [hunit] at hre
    have him : z.im = -z.re := by omega
    rw [him] at hnorm
    have heven : (p : ℤ) = 2 * (z.re * z.re) := by nlinarith [hnorm]
    omega
  · have hre := congrArg Zsqrtd.re hu
    simp [hunit] at hre
    have him : z.im = z.re := by omega
    rw [him] at hnorm
    have heven : (p : ℤ) = 2 * (z.re * z.re) := by nlinarith [hnorm]
    omega


/-- Removing an inert rational prime from both coordinates is an exact
bijection of norm circles, even when the residual norm is zero. -/
theorem normCircle_inert_square (p n : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) :
    normCircle (p * p * n) = (normCircle n).image (fun w => (p : GaussianInt) * w) := by
  classical
  ext z
  constructor
  · intro hz
    have hz' := (mem_normCircle _ _).mp hz
    have hpd : p ∣ z.norm.natAbs := by
      rw [hz']
      exact ⟨p * n, by ring⟩
    obtain ⟨w, rfl⟩ := (GaussianNorm.inert_dvd_natNorm_iff p hp hp3 z).mp hpd
    refine Finset.mem_image.mpr ⟨w, (mem_normCircle _ _).mpr ?_, rfl⟩
    have hmul : (p * p) * w.norm.natAbs = (p * p) * n := by
      simpa [Zsqrtd.norm_mul, Zsqrtd.norm_natCast, Int.natAbs_mul] using hz'
    exact mul_left_cancel₀ (mul_ne_zero hp.ne_zero hp.ne_zero) hmul
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    apply (mem_normCircle _ _).mpr
    simp [Zsqrtd.norm_mul, Zsqrtd.norm_natCast, Int.natAbs_mul,
      (mem_normCircle _ _).mp hw]

theorem normCircle_inert_square_card (p n : ℕ) (hp : p.Prime) (hp3 : p % 4 = 3) :
    (normCircle (p * p * n)).card = (normCircle n).card := by
  classical
  rw [normCircle_inert_square p n hp hp3]
  apply Finset.card_image_of_injective
  have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact fun _ _ h => mul_left_cancel₀ hp0 h


/-- Exact prime-step decomposition before counting overlaps. Unlike the
prime-norm case, the two images can overlap when `p` divides `n`. -/
theorem normCircle_prime_mul (p n : ℕ) (hp : p.Prime) {z : GaussianInt}
    (hz : z.norm.natAbs = p) :
    normCircle (p * n) =
      (normCircle n).image (fun v => z * v) ∪
      (normCircle n).image (fun v => star z * v) := by
  classical
  have hzp := gaussian_prime_of_prime_norm hp hz
  have hzc : (star z).norm.natAbs = p := by simpa using hz
  have hzn : z.norm = (p : ℤ) :=
    (mem_normCircle_iff_norm _ _).mp ((mem_normCircle _ _).mpr hz)
  have hpcast : (p : GaussianInt) = z * star z := by
    rw [← Zsqrtd.norm_eq_mul_conj, hzn]
    simp
  ext w
  constructor
  · intro hw
    have hwn := (mem_normCircle_iff_norm _ _).mp hw
    have hwn' := (mem_normCircle _ _).mp hw
    have hd : z ∣ w * star w := by
      rw [← Zsqrtd.norm_eq_mul_conj, hwn, Int.cast_natCast, Nat.cast_mul, hpcast]
      exact dvd_mul_of_dvd_left (dvd_mul_right z (star z)) _
    have hdiv : z ∣ w ∨ star z ∣ w := by
      rcases hzp.dvd_or_dvd hd with hd | hd
      · exact Or.inl hd
      · right
        obtain ⟨v, hv⟩ := hd
        exact ⟨star v, by simpa using congrArg star hv⟩
    apply Finset.mem_union.mpr
    rcases hdiv with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · left
      apply Finset.mem_image.mpr
      refine ⟨v, (mem_normCircle _ _).mpr ?_, rfl⟩
      have hmul : p * v.norm.natAbs = p * n := by
        simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hz] using hwn'
      exact mul_left_cancel₀ hp.ne_zero hmul
    · right
      apply Finset.mem_image.mpr
      refine ⟨v, (mem_normCircle _ _).mpr ?_, rfl⟩
      have hmul : p * v.norm.natAbs = p * n := by
        simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hzc, hz] using hwn'
      exact mul_left_cancel₀ hp.ne_zero hmul
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · simpa [hz] using normCircle_mul_image_subset z n hw
    · simpa [hzc, hz] using normCircle_mul_image_subset (star z) n hw

end DistanceCounts
end
end

-- Source: DistanceCounts/GaussianDivisibility.lean
section
/-! Actual Gaussian divisibility populations and their first two split-prime moments. -/

noncomputable section

namespace DistanceCounts.GaussianDivisibility

/-- Squared covolume of multiplication by a Gaussian integer. -/
def normMass (d : GaussianInt) : ℝ := d.norm.natAbs

lemma normMass_mul (a b : GaussianInt) : normMass (a * b) = normMass a * normMass b := by
  simp [normMass, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma normMass_star (d : GaussianInt) : normMass (star d) = normMass d := by
  simp [normMass]

lemma normMass_natCast (n : ℕ) : normMass (n : GaussianInt) = (n : ℝ) ^ 2 := by
  simp [normMass, Zsqrtd.norm_natCast, pow_two]

lemma normMass_eq_sq_norm (d : GaussianInt) : normMass d = ‖(d : ℂ)‖ ^ 2 := by
  rw [gaussian_complex_norm, Real.sq_sqrt (Nat.cast_nonneg _)]
  rfl

lemma one_le_normMass {d : GaussianInt} (hd : d ≠ 0) : 1 ≤ normMass d := by
  have h : 0 < d.norm.natAbs := Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hd)
  change (1 : ℝ) ≤ (d.norm.natAbs : ℝ)
  exact_mod_cast Nat.succ_le_of_lt h

lemma one_le_complex_norm {d : GaussianInt} (hd : d ≠ 0) : 1 ≤ ‖(d : ℂ)‖ := by
  have h := one_le_normMass hd
  rw [normMass_eq_sq_norm] at h
  nlinarith [norm_nonneg (d : ℂ)]

/-- The filtered disk, including zero, of multiples of `d`. -/
def divisorDisk (d : GaussianInt) (R : ℝ) : Finset GaussianInt := by
  classical
  exact (gaussianDisk 0 R).filter (fun z => d ∣ z)

/-- The actual norm-divisibility event, not independent surrogate variables. -/
def primeDisk (p : ℕ) (R : ℝ) : Finset GaussianInt := by
  classical
  exact (gaussianDisk 0 R).filter (fun z => p ∣ z.norm.natAbs)

lemma mem_divisorDisk (d z : GaussianInt) (R : ℝ) :
    z ∈ divisorDisk d R ↔ dist (z : ℂ) 0 ≤ R ∧ d ∣ z := by
  classical
  simp [divisorDisk, mem_gaussianDisk]

lemma mem_primeDisk (p : ℕ) (z : GaussianInt) (R : ℝ) :
    z ∈ primeDisk p R ↔ dist (z : ℂ) 0 ≤ R ∧ p ∣ z.norm.natAbs := by
  classical
  simp [primeDisk, mem_gaussianDisk]

lemma divisorDisk_eq_coset (d : GaussianInt) (hd : d ≠ 0) (R : ℝ) :
    divisorDisk d R = gaussianCosetDisk 0 d 0 R := by
  classical
  ext z
  rw [mem_divisorDisk, mem_gaussianCosetDisk _ _ _ hd]
  simp only [zero_add]
  constructor
  · rintro ⟨hR, w, hw⟩
    exact ⟨⟨w, hw.symm⟩, hR⟩
  · rintro ⟨⟨w, hw⟩, hR⟩
    exact ⟨hR, w, hw.symm⟩

/-- The sharp scale-sensitive error inherited from the genuine ideal lattice. -/
theorem divisorDisk_card_error_scaled (d : GaussianInt) (hd : d ≠ 0)
    {R : ℝ} (hR : 0 ≤ R) :
    |((divisorDisk d R).card : ℝ) - Real.pi * R ^ 2 / normMass d| ≤
      (4 * Real.pi) * (R / ‖(d : ℂ)‖ + 1) := by
  have h := gaussianCosetDisk_card_error 0 d hd 0 hR
  rw [← divisorDisk_eq_coset d hd R] at h
  simpa only [normMass_eq_sq_norm, div_pow, mul_div_assoc] using h

/-- A single constant works simultaneously for every nonzero Gaussian divisor. -/
theorem divisorDisk_card_error (d : GaussianInt) (hd : d ≠ 0)
    {R : ℝ} (hR : 0 ≤ R) :
    |((divisorDisk d R).card : ℝ) - Real.pi * R ^ 2 / normMass d| ≤
      (4 * Real.pi) * (R + 1) := by
  apply (divisorDisk_card_error_scaled d hd hR).trans
  have hn := one_le_complex_norm hd
  have hs : R / ‖(d : ℂ)‖ ≤ R :=
    (div_le_iff₀ (by linarith : 0 < ‖(d : ℂ)‖)).mpr (by nlinarith)
  exact mul_le_mul_of_nonneg_left
    (show R / ‖(d : ℂ)‖ + 1 ≤ R + 1 by linarith) (by positivity)

/-- Once zero is removed the count has no additive error, even for very large divisors. -/
theorem divisorDisk_erase_zero_card_upper (d : GaussianInt) (hd : d ≠ 0)
    {R : ℝ} (hR : 0 ≤ R) :
    (((divisorDisk d R).erase 0).card : ℝ) ≤ 9 * Real.pi * R ^ 2 / normMass d := by
  classical
  by_cases he : ((divisorDisk d R).erase 0).Nonempty
  · obtain ⟨w, hw⟩ := he
    obtain ⟨hw0, hw⟩ := Finset.mem_erase.mp hw
    obtain ⟨hwr, u, rfl⟩ := (mem_divisorDisk d w R).mp hw
    have hu : u ≠ 0 := by intro h; simp [h] at hw0
    have hn : 0 < ‖(d : ℂ)‖ := by linarith [one_le_complex_norm hd]
    have hr1 : 1 ≤ R / ‖(d : ℂ)‖ := by
      have hu1 := one_le_complex_norm hu
      simp only [dist_zero_right, GaussianInt.toComplex_mul, norm_mul] at hwr
      apply (le_div_iff₀ hn).mpr
      nlinarith
    have hc : (((divisorDisk d R).erase 0).card : ℝ) ≤
        ((gaussianDisk 0 (R / ‖(d : ℂ)‖)).card : ℝ) := by
      have hcard := Finset.card_le_card (Finset.erase_subset (s := divisorDisk d R) 0)
      have heq : (divisorDisk d R).card =
          (gaussianDisk 0 (R / ‖(d : ℂ)‖)).card := by
        rw [divisorDisk_eq_coset d hd, gaussianCosetDisk_card _ _ hd]
        simp
      rw [heq] at hcard
      exact_mod_cast hcard
    have hupp := gaussianDisk_card_upper 0 (div_nonneg hR (norm_nonneg (d : ℂ)))
    have hs : (R / ‖(d : ℂ)‖ + 2) ^ 2 ≤ 9 * (R / ‖(d : ℂ)‖) ^ 2 := by
      nlinarith
    calc
      _ ≤ Real.pi * (R / ‖(d : ℂ)‖ + 2) ^ 2 := hc.trans hupp
      _ ≤ Real.pi * (9 * (R / ‖(d : ℂ)‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hs Real.pi_nonneg
      _ = _ := by rw [normMass_eq_sq_norm, div_pow]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (by positivity) (by unfold normMass; positivity)

lemma exists_split_factor (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ z : GaussianInt, z.norm.natAbs = p := by
  obtain ⟨a, b, hab⟩ := @Nat.Prime.sq_add_sq p ⟨hp⟩ (by omega)
  obtain ⟨z, hz⟩ := (normCircle_nonempty_iff_sum_two_squares p).mpr ⟨a, b, hab.symm⟩
  exact ⟨z, (mem_normCircle _ _).mp hz⟩

lemma split_factorization {p : ℕ} {z : GaussianInt} (hz : z.norm.natAbs = p) :
    (p : GaussianInt) = z * star z := by
  have hn : z.norm = (p : ℤ) :=
    (mem_normCircle_iff_norm _ _).mp ((mem_normCircle _ _).mpr hz)
  rw [← Zsqrtd.norm_eq_mul_conj, hn]
  simp

/-- The exact split-prime divisibility disjunction. -/
theorem split_dvd_norm_iff {p : ℕ} (hp : p.Prime) {z : GaussianInt}
    (hz : z.norm.natAbs = p) (w : GaussianInt) :
    p ∣ w.norm.natAbs ↔ z ∣ w ∨ star z ∣ w := by
  have hzp := gaussian_prime_of_prime_norm hp hz
  constructor
  · intro h
    have hc : (p : GaussianInt) ∣ (w.norm : GaussianInt) := by
      simpa only [Int.cast_natCast] using
        (Zsqrtd.intCast_dvd_intCast (p : ℤ) w.norm).mpr ((Int.natCast_dvd).mpr h)
    have hzpc : z ∣ (p : GaussianInt) := by
      rw [split_factorization hz]
      exact dvd_mul_right _ _
    have hd := dvd_trans hzpc hc
    rw [Zsqrtd.norm_eq_mul_conj] at hd
    rcases hzp.dvd_or_dvd hd with hw | hw
    · exact Or.inl hw
    · right
      obtain ⟨u, hu⟩ := hw
      refine ⟨star u, ?_⟩
      simpa [mul_comm] using congrArg star hu
  · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩) <;>
      simp [Zsqrtd.norm_mul, Int.natAbs_mul, hz]

/-- Both conjugate factors divide exactly the rational-prime multiples. -/
theorem split_factor_inter_iff {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    {z : GaussianInt} (hz : z.norm.natAbs = p) (w : GaussianInt) :
    z ∣ w ∧ star z ∣ w ↔ (p : GaussianInt) ∣ w := by
  have hzp := gaussian_prime_of_prime_norm hp hz
  have hcp := gaussian_prime_of_prime_norm hp (show (star z).norm.natAbs = p by simpa using hz)
  have hnot : ¬star z ∣ z := by
    intro h
    exact not_associated_conj_of_split_prime_norm hp hp4 hz
      (hcp.associated_of_dvd hzp h).symm
  rw [split_factorization hz]
  constructor
  · rintro ⟨⟨u, rfl⟩, hu⟩
    obtain ⟨v, rfl⟩ := (hcp.dvd_or_dvd hu).resolve_left hnot
    exact ⟨v, by ring⟩
  · intro h
    exact ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩

lemma primeDisk_eq_union {p : ℕ} (hp : p.Prime) {z : GaussianInt}
    (hz : z.norm.natAbs = p) (R : ℝ) :
    primeDisk p R = divisorDisk z R ∪ divisorDisk (star z) R := by
  classical
  ext w
  simp only [Finset.mem_union, mem_primeDisk, mem_divisorDisk, split_dvd_norm_iff hp hz]
  tauto

lemma split_divisorDisk_inter {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    {z : GaussianInt} (hz : z.norm.natAbs = p) (R : ℝ) :
    divisorDisk z R ∩ divisorDisk (star z) R = divisorDisk (p : GaussianInt) R := by
  classical
  ext w
  simp only [Finset.mem_inter, mem_divisorDisk]
  have h := split_factor_inter_iff hp hp4 hz w
  tauto

lemma divisorDisk_inter (a b : GaussianInt) (hab : IsCoprime a b) (R : ℝ) :
    divisorDisk a R ∩ divisorDisk b R = divisorDisk (a * b) R := by
  classical
  ext w
  simp only [Finset.mem_inter, mem_divisorDisk]
  constructor
  · rintro ⟨⟨hw, ha⟩, _, hb⟩
    exact ⟨hw, hab.mul_dvd ha hb⟩
  · rintro ⟨hw, h⟩
    exact ⟨⟨hw, dvd_trans (dvd_mul_right _ _) h⟩,
      hw, dvd_trans (dvd_mul_left _ _) h⟩

/-- The three-term inclusion-exclusion estimate, with no probabilistic input. -/
lemma card_union_error (A B : Finset GaussianInt) (a b c E : ℝ)
    (ha : |(A.card : ℝ) - a| ≤ E) (hb : |(B.card : ℝ) - b| ≤ E)
    (hc : |((A ∩ B).card : ℝ) - c| ≤ E) :
    |((A ∪ B).card : ℝ) - (a + b - c)| ≤ 3 * E := by
  classical
  have he : ((A ∪ B).card : ℝ) + ((A ∩ B).card : ℝ) =
      (A.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast Finset.card_union_add_card_inter A B
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  apply abs_le.mpr
  constructor <;> linarith

/-- Natural density of the split norm-divisibility event. -/
def splitDensity (p : ℕ) : ℝ := 2 / (p : ℝ) - 1 / (p : ℝ) ^ 2

/-- A divisor coprime to `p` can be imposed without changing the local split density.
This is the three-term building block for the genuine nine-term second moment. -/
theorem divisor_primeDisk_card_error (d : GaussianInt) (hd : d ≠ 0)
    (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdp : IsCoprime d (p : GaussianInt)) {R : ℝ} (hR : 0 ≤ R) :
    |((divisorDisk d R ∩ primeDisk p R).card : ℝ) -
      Real.pi * R ^ 2 * splitDensity p / normMass d| ≤
      (12 * Real.pi) * (R + 1) := by
  classical
  obtain ⟨z, hz⟩ := exists_split_factor p hp hp4
  have hz0 := (gaussian_prime_of_prime_norm hp hz).ne_zero
  have hzc0 : star z ≠ 0 := by simpa using hz0
  have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdz : IsCoprime d z := hdp.of_isCoprime_of_dvd_right
    (by rw [split_factorization hz]; exact dvd_mul_right _ _)
  have hdc : IsCoprime d (star z) := hdp.of_isCoprime_of_dvd_right
    (by rw [split_factorization hz]; exact dvd_mul_left _ _)
  let A := divisorDisk d R ∩ divisorDisk z R
  let B := divisorDisk d R ∩ divisorDisk (star z) R
  have hA : A = divisorDisk (d * z) R := divisorDisk_inter d z hdz R
  have hB : B = divisorDisk (d * star z) R := divisorDisk_inter d (star z) hdc R
  have hI : A ∩ B = divisorDisk (d * (p : GaussianInt)) R := by
    change (divisorDisk d R ∩ divisorDisk z R) ∩
      (divisorDisk d R ∩ divisorDisk (star z) R) = _
    rw [← Finset.inter_inter_distrib_left, split_divisorDisk_inter hp hp4 hz,
      divisorDisk_inter d (p : GaussianInt) hdp]
  have hU : divisorDisk d R ∩ primeDisk p R = A ∪ B := by
    rw [primeDisk_eq_union hp hz, Finset.inter_union_distrib_left]
  have eA := divisorDisk_card_error (d * z) (mul_ne_zero hd hz0) hR
  have eB := divisorDisk_card_error (d * star z) (mul_ne_zero hd hzc0) hR
  have eI := divisorDisk_card_error (d * (p : GaussianInt)) (mul_ne_zero hd hp0) hR
  rw [← hA] at eA
  rw [← hB] at eB
  rw [← hI] at eI
  have he := card_union_error A B _ _ _ _ eA eB eI
  have hm : Real.pi * R ^ 2 / normMass (d * z) +
      Real.pi * R ^ 2 / normMass (d * star z) -
      Real.pi * R ^ 2 / normMass (d * (p : GaussianInt)) =
      Real.pi * R ^ 2 * splitDensity p / normMass d := by
    have hn : normMass z = (p : ℝ) := by simp [normMass, hz]
    have hdN : normMass d ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (one_le_normMass hd))
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [normMass_mul, normMass_mul, normMass_mul, normMass_star, hn, normMass_natCast]
    unfold splitDensity
    field_simp [hdN, hpR] <;> ring
  rw [hm, ← hU] at he
  convert he using 1 <;> ring

/-- First moment for the actual split-prime norm event, uniformly in the prime. -/
theorem primeDisk_card_error (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    {R : ℝ} (hR : 0 ≤ R) :
    |((primeDisk p R).card : ℝ) - Real.pi * R ^ 2 * splitDensity p| ≤
      (12 * Real.pi) * (R + 1) := by
  have he := divisor_primeDisk_card_error 1 one_ne_zero p hp hp4 isCoprime_one_left hR
  have hs : divisorDisk 1 R ∩ primeDisk p R = primeDisk p R := by
    classical
    ext w
    simp only [Finset.mem_inter, mem_divisorDisk, mem_primeDisk, one_dvd, and_true]
    tauto
  simpa [hs, normMass] using he

/-- The two distinct-prime events have the product main term and a universal error.
The proof expands their two three-term union identities into nine genuine ideal counts. -/
theorem primeDisk_inter_card_error (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) (hpq : p ≠ q)
    {R : ℝ} (hR : 0 ≤ R) :
    |((primeDisk p R ∩ primeDisk q R).card : ℝ) -
      Real.pi * R ^ 2 * splitDensity p * splitDensity q| ≤
      (36 * Real.pi) * (R + 1) := by
  classical
  obtain ⟨z, hz⟩ := exists_split_factor q hq hq4
  have hz0 := (gaussian_prime_of_prime_norm hq hz).ne_zero
  have hzc0 : star z ≠ 0 := by simpa using hz0
  have hq0 : (q : GaussianInt) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqp : IsCoprime (q : GaussianInt) (p : GaussianInt) :=
    ((Nat.coprime_primes hq hp).mpr hpq.symm).cast
  have hzp : IsCoprime z (p : GaussianInt) := hqp.of_isCoprime_of_dvd_left
    (by rw [split_factorization hz]; exact dvd_mul_right _ _)
  have hcp : IsCoprime (star z) (p : GaussianInt) := hqp.of_isCoprime_of_dvd_left
    (by rw [split_factorization hz]; exact dvd_mul_left _ _)
  let A := divisorDisk z R ∩ primeDisk p R
  let B := divisorDisk (star z) R ∩ primeDisk p R
  have hI : A ∩ B = divisorDisk (q : GaussianInt) R ∩ primeDisk p R := by
    change (divisorDisk z R ∩ primeDisk p R) ∩
      (divisorDisk (star z) R ∩ primeDisk p R) = _
    rw [Finset.inter_inter_inter_comm, Finset.inter_self,
      split_divisorDisk_inter hq hq4 hz]
  have hU : primeDisk p R ∩ primeDisk q R = A ∪ B := by
    rw [Finset.inter_comm, primeDisk_eq_union hq hz, Finset.union_inter_distrib_right]
  have eA := divisor_primeDisk_card_error z hz0 p hp hp4 hzp hR
  have eB := divisor_primeDisk_card_error (star z) hzc0 p hp hp4 hcp hR
  have eI := divisor_primeDisk_card_error (q : GaussianInt) hq0 p hp hp4 hqp hR
  rw [← hI] at eI
  have he := card_union_error A B _ _ _ _ eA eB eI
  have hm : Real.pi * R ^ 2 * splitDensity p / normMass z +
      Real.pi * R ^ 2 * splitDensity p / normMass (star z) -
      Real.pi * R ^ 2 * splitDensity p / normMass (q : GaussianInt) =
      Real.pi * R ^ 2 * splitDensity p * splitDensity q := by
    have hn : normMass z = (q : ℝ) := by simp [normMass, hz]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    rw [normMass_star, hn, normMass_natCast]
    unfold splitDensity
    field_simp [hpR, hqR] <;> ring
  rw [hm, ← hU] at he
  convert he using 1 <;> ring

/-- Exact population adjustment: zero contributes one to every raw divisibility count. -/
lemma erase_zero_card (S : Finset GaussianInt) (hS : 0 ∈ S) :
    ((S.erase 0).card : ℝ) = (S.card : ℝ) - 1 := by
  classical
  have h := Finset.card_erase_add_one hS
  have hc : ((S.erase 0).card : ℝ) + 1 = (S.card : ℝ) := by exact_mod_cast h
  linarith

lemma primeDisk_zero_mem (p : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ∈ primeDisk p R := by
  rw [mem_primeDisk]
  simpa using hR

lemma erase_zero_card_error (S : Finset GaussianInt) (hS : 0 ∈ S)
    (M C R : ℝ) (hR : 0 ≤ R) (he : |(S.card : ℝ) - M| ≤ C * (R + 1)) :
    |((S.erase 0).card : ℝ) - M| ≤ (C + 1) * (R + 1) := by
  rw [erase_zero_card S hS]
  obtain ⟨he₁, he₂⟩ := abs_le.mp he
  apply abs_le.mpr
  constructor <;> nlinarith

/-- First moment in the nonzero population used for point-weighted normal order. -/
theorem primeDisk_erase_zero_card_error (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    {R : ℝ} (hR : 0 ≤ R) :
    |(((primeDisk p R).erase 0).card : ℝ) - Real.pi * R ^ 2 * splitDensity p| ≤
      (12 * Real.pi + 1) * (R + 1) :=
  erase_zero_card_error _ (primeDisk_zero_mem p hR) _ _ _ hR (primeDisk_card_error p hp hp4 hR)

/-- Off-diagonal second moment after removing the common zero vector. -/
theorem primeDisk_inter_erase_zero_card_error (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) (hpq : p ≠ q)
    {R : ℝ} (hR : 0 ≤ R) :
    |(((primeDisk p R ∩ primeDisk q R).erase 0).card : ℝ) -
      Real.pi * R ^ 2 * splitDensity p * splitDensity q| ≤
      (36 * Real.pi + 1) * (R + 1) := by
  classical
  exact erase_zero_card_error _
    (Finset.mem_inter.mpr ⟨primeDisk_zero_mem p hR, primeDisk_zero_mem q hR⟩)
    _ _ _ hR (primeDisk_inter_card_error p q hp hq hp4 hq4 hpq hR)

end DistanceCounts.GaussianDivisibility
end
end

-- Source: DistanceCounts/SieveWeights.lean
section
/-! Exact finite Boolean-divisor Möbius inversion and optimal Selberg square weights. -/

noncomputable section

namespace DistanceCounts.SieveWeights

open Finset

variable {α : Type*} [DecidableEq α]

/-- A finite lower ideal in the Boolean divisor lattice. The prime indices need not be
natural numbers; in particular, conjugate Gaussian primes can have the same norm. -/
structure DivisorFamily (α : Type*) [DecidableEq α] where
  members : Finset (Finset α)
  nonempty : members.Nonempty
  lower : ∀ {S T}, T ∈ members → S ⊆ T → S ∈ members

variable (F : DivisorFamily α)

 def norm (n : α → ℝ) (S : Finset α) : ℝ := ∏ p ∈ S, n p
 def phi (n : α → ℝ) (S : Finset α) : ℝ := ∏ p ∈ S, (n p - 1)
 def mobius (S : Finset α) : ℝ := (-1) ^ S.card

namespace DivisorFamily

 def mass (n : α → ℝ) : ℝ := ∑ S ∈ F.members, 1 / phi n S
 def optimalY (n : α → ℝ) (S : Finset α) : ℝ :=
  if S ∈ F.members then mobius S / (phi n S * F.mass n) else 0
 def inverse (y : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ T ∈ F.members, if S ⊆ T then mobius (T \ S) * y T else 0
 def zeta (f : Finset α → ℝ) (R : Finset α) : ℝ :=
  ∑ S ∈ F.members, if R ⊆ S then f S else 0
 def weight (n : α → ℝ) (S : Finset α) : ℝ :=
  norm n S * F.inverse (F.optimalY n) S

 theorem empty_mem : ∅ ∈ F.members := by
  obtain ⟨T, hT⟩ := F.nonempty
  exact F.lower hT (empty_subset T)

 theorem norm_pos (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) (S : Finset α) :
    0 < norm n S := by
  exact prod_pos fun p _ => lt_of_lt_of_le (by norm_num) (hn p)

 theorem phi_one_le (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) (S : Finset α) :
    1 ≤ phi n S := by
  apply one_le_prod
  intro p _
  linarith [hn p]

 theorem phi_pos (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) (S : Finset α) :
    0 < phi n S := lt_of_lt_of_le zero_lt_one (phi_one_le n hn S)

 theorem mass_pos (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) : 0 < F.mass n := by
  exact sum_pos (fun S _ => one_div_pos.mpr (phi_pos n hn S)) F.nonempty

 theorem mobius_mul_self (S : Finset α) : mobius S * mobius S = 1 := by
  unfold mobius
  rw [← mul_pow]
  norm_num

 theorem abs_mobius (S : Finset α) : |mobius S| = 1 := by
  simp [mobius, abs_pow]

 theorem mobius_sdiff_mul (S T : Finset α) (hST : S ⊆ T) :
    mobius (T \ S) * mobius S = mobius T := by
  unfold mobius
  rw [← pow_add, card_sdiff_add_card_eq_card hST]

 theorem mobius_sdiff_mul_mobius (S T : Finset α) (hST : S ⊆ T) :
    mobius (T \ S) * mobius T = mobius S := by
  rw [← mobius_sdiff_mul S T hST]
  rw [← mul_assoc, mobius_mul_self, one_mul]

 theorem sum_mobius_powerset (T : Finset α) :
    (∑ S ∈ T.powerset, mobius S) = if T = ∅ then 1 else 0 := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (Finset.sum_powerset_neg_one_pow_card (x := T))
  simpa [mobius] using h

/-- Cancellation on a Boolean interval, established by complementation in its top. -/
 theorem interval_cancellation (R T : Finset α) (hT : T ∈ F.members) :
    (∑ S ∈ F.members, if R ⊆ S ∧ S ⊆ T then mobius (T \ S) else 0) =
      if R = T then 1 else 0 := by
  by_cases hRT : R ⊆ T
  · rw [← sum_filter]
    have hsum : (∑ S ∈ F.members.filter (fun S => R ⊆ S ∧ S ⊆ T),
        mobius (T \ S)) = ∑ U ∈ (T \ R).powerset, mobius U := by
      apply sum_bij (fun S _ => T \ S)
      · intro S hS
        simp only [mem_filter] at hS
        rw [mem_powerset]
        intro p hp
        simp only [mem_sdiff] at hp ⊢
        exact ⟨hp.1, fun hpR => hp.2 (hS.2.1 hpR)⟩
      · intro S hS U hU heq
        simp only [mem_filter] at hS hU
        apply Finset.ext
        intro p
        have hh := Finset.ext_iff.mp heq p
        simp only [mem_sdiff] at hh
        have h1 := hS.2.2
        have h2 := hU.2.2
        simp only [Finset.subset_iff] at h1 h2
        aesop
      · intro U hU
        have hu : U ⊆ T \ R := mem_powerset.mp hU
        refine ⟨T \ U, ?_, ?_⟩
        · rw [mem_filter]
          refine ⟨F.lower hT sdiff_subset, ?_, sdiff_subset⟩
          intro p hp
          rw [mem_sdiff]
          exact ⟨hRT hp, fun hpU => (mem_sdiff.mp (hu hpU)).2 hp⟩
        · apply Finset.ext
          intro p
          have hsub : U ⊆ T := hu.trans sdiff_subset
          simp only [Finset.subset_iff] at hsub
          simp only [mem_sdiff]
          aesop
      · intro S _
        rfl
    rw [hsum, sum_mobius_powerset]
    have he : T \ R = ∅ ↔ R = T := by
      rw [sdiff_eq_empty_iff_subset]
      exact ⟨fun h => subset_antisymm hRT h, fun h => h ▸ subset_rfl⟩
    simp only [he]
  · have hne : R ≠ T := fun h => hRT (h ▸ subset_rfl)
    rw [if_neg hne]
    apply sum_eq_zero
    intro S _
    have hh : ¬ (R ⊆ S ∧ S ⊆ T) := fun h => hRT (h.1.trans h.2)
    simp [hh]

/-- Finite upper Möbius inversion. No arithmetic-function or ideal axiom is used. -/
 theorem zeta_inverse (y : Finset α → ℝ) (R : Finset α) :
    F.zeta (F.inverse y) R = if R ∈ F.members then y R else 0 := by
  unfold zeta inverse
  simp_rw [ite_sum_zero]
  rw [sum_comm]
  have hterm : ∀ T ∈ F.members,
      (∑ S ∈ F.members,
        if R ⊆ S then (if S ⊆ T then mobius (T \ S) * y T else 0) else 0) =
      (if R = T then 1 else 0) * y T := by
    intro T hT
    rw [← F.interval_cancellation R T hT, sum_mul]
    apply sum_congr rfl
    intro S _
    by_cases hRS : R ⊆ S <;> by_cases hST : S ⊆ T <;> simp [hRS, hST]
  rw [sum_congr rfl hterm]
  by_cases hR : R ∈ F.members
  · simp [hR]
  · simp [hR]


 theorem weight_div_norm (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) (S : Finset α) :
    F.weight n S / norm n S = F.inverse (F.optimalY n) S := by
  unfold weight
  exact mul_div_cancel_left₀ _ (norm_pos n hn S).ne'

 theorem transform_weight (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) (R : Finset α) :
    (∑ S ∈ F.members, if R ⊆ S then F.weight n S / norm n S else 0) =
      F.optimalY n R := by
  simp_rw [F.weight_div_norm n hn]
  rw [← zeta, F.zeta_inverse]
  by_cases hR : R ∈ F.members <;> simp [optimalY, hR]

 theorem weight_empty (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) :
    F.weight n ∅ = 1 := by
  have hG := (F.mass_pos n hn).ne'
  unfold weight inverse
  simp only [norm, prod_empty, one_mul, empty_subset, sdiff_empty, if_true]
  have hterm : ∀ T ∈ F.members,
      mobius T * F.optimalY n T = (1 / phi n T) / F.mass n := by
    intro T hT
    rw [optimalY, if_pos hT]
    have hp := (phi_pos n hn T).ne'
    have hm := mobius_mul_self T
    field_simp
    nlinarith
  rw [sum_congr rfl hterm, ← sum_div, ← mass, div_self hG]

 theorem phi_divisor_sum (n : α → ℝ) (T : Finset α) :
    (∑ R ∈ T.powerset, phi n R) = norm n T := by
  simpa [phi, norm] using (Finset.prod_add_one (f := fun p => n p - 1) T).symm

 theorem phi_common_divisor_sum (n : α → ℝ) (S T : Finset α)
    (hS : S ∈ F.members) :
    (∑ R ∈ F.members, if R ⊆ S ∧ R ⊆ T then phi n R else 0) =
      norm n (S ∩ T) := by
  rw [← sum_filter]
  have he : F.members.filter (fun R => R ⊆ S ∧ R ⊆ T) = (S ∩ T).powerset := by
    ext R
    simp only [mem_filter, mem_powerset, subset_inter_iff]
    exact ⟨fun h => h.2, fun h => ⟨F.lower hS h.1, h⟩⟩
  rw [he, phi_divisor_sum]

 theorem norm_union_inter (n : α → ℝ) (S T : Finset α) :
    norm n (S ∪ T) * norm n (S ∩ T) = norm n S * norm n T :=
  prod_union_inter

/-- Boolean version of Mathlib's `mainSum_lambdaSquared_eq_sum_mul_sum_sq`.
The two distinct prime ideals above a split prime remain distinct indices. -/
 theorem quadratic_diagonal (n : α → ℝ) (hn : ∀ p, 2 ≤ n p)
    (w : Finset α → ℝ) :
    (∑ S ∈ F.members, ∑ T ∈ F.members, w S * w T / norm n (S ∪ T)) =
      ∑ R ∈ F.members, phi n R *
        (∑ S ∈ F.members, if R ⊆ S then w S / norm n S else 0) ^ 2 := by
  have hkernel : ∀ S ∈ F.members, ∀ T ∈ F.members,
      w S * w T / norm n (S ∪ T) =
        ∑ R ∈ F.members, if R ⊆ S ∧ R ⊆ T then
          phi n R * (w S / norm n S) * (w T / norm n T) else 0 := by
    intro S hS T _
    have hN := norm_union_inter n S T
    have h1 := (norm_pos n hn S).ne'
    have h2 := (norm_pos n hn T).ne'
    have h3 := (norm_pos n hn (S ∪ T)).ne'
    calc
      _ = norm n (S ∩ T) * (w S / norm n S) * (w T / norm n T) := by
        field_simp
        nlinarith [congrArg (fun x : ℝ => w S * w T * x) hN]
      _ = _ := by
        rw [← F.phi_common_divisor_sum n S T hS, sum_mul, sum_mul]
        apply sum_congr rfl
        intro R _
        split_ifs <;> simp
  calc
    _ = ∑ S ∈ F.members, ∑ T ∈ F.members, ∑ R ∈ F.members,
        if R ⊆ S ∧ R ⊆ T then
          phi n R * (w S / norm n S) * (w T / norm n T) else 0 := by
      apply sum_congr rfl
      intro S hS
      exact sum_congr rfl (fun T hT => hkernel S hS T hT)
    _ = ∑ R ∈ F.members, ∑ S ∈ F.members, ∑ T ∈ F.members,
        if R ⊆ S ∧ R ⊆ T then
          phi n R * (w S / norm n S) * (w T / norm n T) else 0 := by
      rw [eq_comm, sum_comm]
      apply sum_congr rfl
      intro S _
      exact sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro R _
      simp_rw [sq, sum_mul, mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro T _
      by_cases hRS : R ⊆ S <;> by_cases hRT : R ⊆ T <;>
        simp [hRS, hRT, mul_assoc]

 theorem optimal_diagonal (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) :
    (∑ R ∈ F.members, phi n R * (F.optimalY n R) ^ 2) = 1 / F.mass n := by
  have hG := (F.mass_pos n hn).ne'
  have hterm : ∀ R ∈ F.members,
      phi n R * (F.optimalY n R) ^ 2 = (1 / phi n R) / F.mass n ^ 2 := by
    intro R hR
    rw [optimalY, if_pos hR]
    have hp := (phi_pos n hn R).ne'
    have hm := mobius_mul_self R
    field_simp
    nlinarith
  rw [sum_congr rfl hterm, ← sum_div, ← mass]
  field_simp

/-- The exact main term (5d). -/
 theorem quadratic_weight (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) :
    (∑ S ∈ F.members, ∑ T ∈ F.members,
      F.weight n S * F.weight n T / norm n (S ∪ T)) = 1 / F.mass n := by
  rw [F.quadratic_diagonal n hn]
  simp_rw [F.transform_weight n hn]
  exact F.optimal_diagonal n hn

 theorem phi_sdiff_mul (n : α → ℝ) (S T : Finset α) (hST : S ⊆ T) :
    phi n (T \ S) * phi n S = phi n T :=
  prod_sdiff hST

/-- Removing a fixed divisor embeds its multiples in the same lower family. -/
 theorem complementary_mass_le (n : α → ℝ) (hn : ∀ p, 2 ≤ n p)
    (S : Finset α) :
    (∑ T ∈ F.members.filter (fun T => S ⊆ T), 1 / phi n (T \ S)) ≤ F.mass n := by
  let H := F.members.filter (fun T => S ⊆ T)
  have hinj : ∀ T ∈ H, ∀ U ∈ H, T \ S = U \ S → T = U := by
    intro T hT U hU he
    have ht : S ⊆ T := (mem_filter.mp hT).2
    have hu : S ⊆ U := (mem_filter.mp hU).2
    have hh := congrArg (fun V : Finset α => V ∪ S) he
    simpa [sdiff_union_of_subset ht, sdiff_union_of_subset hu] using hh
  have hsub : H.image (fun T => T \ S) ⊆ F.members := by
    intro U hU
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hU
    exact F.lower (mem_filter.mp hT).1 sdiff_subset
  calc
    _ = ∑ U ∈ H.image (fun T => T \ S), 1 / phi n U :=
      (sum_image hinj).symm
    _ ≤ F.mass n := sum_le_sum_of_subset_of_nonneg hsub
      (fun U _ _ => (one_div_pos.mpr (phi_pos n hn U)).le)

/-- The explicit positive-sum form of the optimal coefficients. -/
 theorem weight_formula (n : α → ℝ) (hn : ∀ p, 2 ≤ n p) (S : Finset α) :
    F.weight n S =
      norm n S * mobius S / (phi n S * F.mass n) *
        (∑ T ∈ F.members.filter (fun T => S ⊆ T), 1 / phi n (T \ S)) := by
  have hG := (F.mass_pos n hn).ne'
  have hpS := (phi_pos n hn S).ne'
  unfold weight inverse
  rw [← sum_filter, mul_sum, mul_sum]
  apply sum_congr rfl
  intro T hT
  obtain ⟨hT, hST⟩ := mem_filter.mp hT
  rw [optimalY, if_pos hT]
  have hm := mobius_sdiff_mul_mobius S T hST
  have hp := phi_sdiff_mul n S T hST
  have hpT := (phi_pos n hn T).ne'
  have hpD := (phi_pos n hn (T \ S)).ne'
  have he : mobius (T \ S) * (mobius T / (phi n T * F.mass n)) =
      mobius S / (phi n S * F.mass n) * (1 / phi n (T \ S)) := by
    calc
      _ = (mobius (T \ S) * mobius T) / (phi n T * F.mass n) := by ring
      _ = mobius S / (phi n T * F.mass n) := by rw [hm]
      _ = _ := by
        rw [← hp]
        field_simp
        <;> ring
  rw [he]
  ring

/-- The first inequality in (5e), with no arithmetic distribution input. -/
 theorem abs_weight_le_norm_div_phi (n : α → ℝ) (hn : ∀ p, 2 ≤ n p)
    (S : Finset α) : |F.weight n S| ≤ norm n S / phi n S := by
  have hN := norm_pos n hn S
  have hp := phi_pos n hn S
  have hG := F.mass_pos n hn
  have hsum : 0 ≤ ∑ T ∈ F.members.filter (fun T => S ⊆ T),
      1 / phi n (T \ S) :=
    sum_nonneg (fun T _ => (one_div_pos.mpr (phi_pos n hn (T \ S))).le)
  rw [F.weight_formula n hn, abs_mul, abs_div, abs_mul, abs_mobius,
    abs_of_pos hN, abs_of_pos (mul_pos hp hG), abs_of_nonneg hsum, mul_one]
  calc
    _ ≤ norm n S / (phi n S * F.mass n) * F.mass n :=
      mul_le_mul_of_nonneg_left (F.complementary_mass_le n hn S)
        (div_pos hN (mul_pos hp hG)).le
    _ = norm n S / phi n S := by field_simp

 theorem abs_weight_le_norm (n : α → ℝ) (hn : ∀ p, 2 ≤ n p)
    (S : Finset α) : |F.weight n S| ≤ norm n S := by
  apply (F.abs_weight_le_norm_div_phi n hn S).trans
  exact div_le_self (norm_pos n hn S).le (phi_one_le n hn S)


end DivisorFamily
end DistanceCounts.SieveWeights
end
end

-- Source: DistanceCounts/GaussianMass.lean
section
/-! Genuine Gaussian associate classes, finite norm balls, and squarefree mass. -/

noncomputable section

namespace DistanceCounts.GaussianMass

open Finset UniqueFactorizationMonoid
open scoped Classical

/-- The norm descends to the actual quotient by Gaussian units. Zero is retained
in the ambient monoid and explicitly removed from all counting supports. -/
def classNorm : Associates GaussianInt → ℕ :=
  Quotient.lift (fun z : GaussianInt => z.norm.natAbs)
    (fun _ _ h => congrArg Int.natAbs (Zsqrtd.norm_eq_of_associated (by norm_num) h))

lemma classNorm_mk (z : GaussianInt) : classNorm (Associates.mk z) = z.norm.natAbs := rfl


lemma classNorm_one : classNorm 1 = 1 := by
  change (1 : GaussianInt).norm.natAbs = 1
  simp

lemma classNorm_mul (a b : Associates GaussianInt) :
    classNorm (a * b) = classNorm a * classNorm b := by
  obtain ⟨z, rfl⟩ := Associates.mk_surjective a
  obtain ⟨w, rfl⟩ := Associates.mk_surjective b
  change (z * w).norm.natAbs = z.norm.natAbs * w.norm.natAbs
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

lemma classNorm_eq_zero (a : Associates GaussianInt) : classNorm a = 0 ↔ a = 0 := by
  obtain ⟨z, rfl⟩ := Associates.mk_surjective a
  rw [classNorm_mk, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero, Associates.mk_eq_zero]

lemma classNorm_pos (a : Associates GaussianInt) : 0 < classNorm a ↔ a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, classNorm_eq_zero]

lemma classNorm_eq_one (a : Associates GaussianInt) : classNorm a = 1 ↔ a = 1 := by
  obtain ⟨z, rfl⟩ := Associates.mk_surjective a
  rw [classNorm_mk, Zsqrtd.norm_eq_one_iff, Associates.mk_eq_one]

lemma classNorm_prime_two_le {p : Associates GaussianInt} (hp : Prime p) :
    2 ≤ classNorm p := by
  have h0 := (classNorm_pos p).mpr hp.ne_zero
  have h1 : classNorm p ≠ 1 := by
    intro h
    apply hp.not_isUnit
    rw [(classNorm_eq_one p).mp h]
    exact isUnit_one
  omega

lemma classNorm_le_of_dvd {a b : Associates GaussianInt} (hb : b ≠ 0) (hab : a ∣ b) :
    classNorm a ≤ classNorm b := by
  obtain ⟨c, rfl⟩ := hab
  have hc : c ≠ 0 := fun h => hb (by simp [h])
  rw [classNorm_mul]
  exact Nat.le_mul_of_pos_right _ ((classNorm_pos c).mpr hc)

/-- The finite nonzero Gaussian representatives below the norm cutoff. -/
def representatives (D : ℝ) : Finset GaussianInt := by
  classical
  exact (gaussianDisk 0 (Real.sqrt D)).erase 0

/-- Principal nonzero classes, with no representative selected. -/
def classBall (D : ℝ) : Finset (Associates GaussianInt) := by
  classical
  exact (representatives D).image Associates.mk

lemma mem_representatives {D : ℝ} (hD : 0 ≤ D) (z : GaussianInt) :
    z ∈ representatives D ↔ z ≠ 0 ∧ (z.norm.natAbs : ℝ) ≤ D := by
  classical
  rw [representatives, mem_erase, mem_gaussianDisk]
  simp only [dist_zero_right, gaussian_complex_norm]
  rw [Real.sqrt_le_sqrt_iff hD]

lemma mem_classBall {D : ℝ} (hD : 0 ≤ D) (a : Associates GaussianInt) :
    a ∈ classBall D ↔ a ≠ 0 ∧ (classNorm a : ℝ) ≤ D := by
  classical
  constructor
  · intro ha
    obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
    obtain ⟨hz0, hzD⟩ := (mem_representatives hD z).mp hz
    exact ⟨Associates.mk_ne_zero.mpr hz0, hzD⟩
  · obtain ⟨z, rfl⟩ := Associates.mk_surjective a
    rintro ⟨hz0, hzD⟩
    exact mem_image.mpr ⟨z, (mem_representatives hD z).mpr
      ⟨Associates.mk_ne_zero.mp hz0, hzD⟩, rfl⟩

lemma representatives_fiber {D : ℝ} (hD : 0 ≤ D) {z : GaussianInt}
    (hz : z ∈ representatives D) :
    (representatives D).filter (fun w => Associates.mk w = Associates.mk z) =
      normUnitOrbit z := by
  classical
  obtain ⟨hz0, hzD⟩ := (mem_representatives hD z).mp hz
  ext w
  rw [mem_filter, Associates.mk_eq_mk_iff_associated, mem_normUnitOrbit]
  constructor
  · exact fun h => h.2.symm
  · intro h
    have he : w.norm.natAbs = z.norm.natAbs :=
      (congrArg Int.natAbs (Zsqrtd.norm_eq_of_associated (by norm_num) h)).symm
    refine ⟨(mem_representatives hD w).mpr ⟨?_, by simpa [he] using hzD⟩, h.symm⟩
    intro hw
    have hn : z.norm.natAbs = 0 := by simpa [hw] using he.symm
    exact hz0 (GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp hn))

/-- Each nonzero class has exactly four representatives in a norm ball. -/
theorem representatives_card {D : ℝ} (hD : 0 ≤ D) :
    (representatives D).card = 4 * (classBall D).card := by
  classical
  rw [card_eq_sum_card_image Associates.mk (representatives D)]
  have hf : ∀ a ∈ (representatives D).image Associates.mk,
      ((representatives D).filter (fun w => Associates.mk w = a)).card = 4 := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
    rw [representatives_fiber hD hz]
    exact normUnitOrbit_card ((mem_representatives hD z).mp hz).1
  rw [sum_congr rfl hf]
  simp [classBall, mul_comm]

/-- The origin contributes one, and is not a nonzero principal ideal. -/
theorem disk_card_eq_four_mul_classBall_add_one {D : ℝ} (hD : 0 ≤ D) :
    (gaussianDisk 0 (Real.sqrt D)).card = 4 * (classBall D).card + 1 := by
  classical
  have hzero : (0 : GaussianInt) ∈ gaussianDisk 0 (Real.sqrt D) := by
    rw [mem_gaussianDisk]
    simpa using Real.sqrt_nonneg D
  have he := card_erase_add_one hzero
  change (representatives D).card + 1 = _ at he
  rw [representatives_card hD] at he
  exact he.symm


/-- Explicit form of the ideal count in (5b). -/
theorem classBall_card_error {D : ℝ} (hD : 0 ≤ D) :
    |((classBall D).card : ℝ) - (Real.pi / 4) * D| ≤
      (Real.pi + 1) * (Real.sqrt D + 1) := by
  have hd := gaussianDisk_card_error (0 : ℂ) (Real.sqrt_nonneg D)
  rw [Real.sq_sqrt hD] at hd
  have hc : ((gaussianDisk 0 (Real.sqrt D)).card : ℝ) =
      4 * ((classBall D).card : ℝ) + 1 := by
    exact_mod_cast disk_card_eq_four_mul_classBall_add_one hD
  rw [hc] at hd
  obtain ⟨hl, hu⟩ := abs_le.mp hd
  apply abs_le.mpr
  constructor <;> nlinarith [Real.sqrt_nonneg D]


/-- The genuine distinct Gaussian prime classes dividing an associate class. -/
def primeSupport (a : Associates GaussianInt) : Finset (Associates GaussianInt) :=
  (normalizedFactors a).toFinset

lemma mem_primeSupport {a p : Associates GaussianInt} (ha : a ≠ 0) :
    p ∈ primeSupport a ↔ Prime p ∧ p ∣ a := by
  rw [primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff ha]

lemma prime_of_mem_primeSupport {a p : Associates GaussianInt} (hp : p ∈ primeSupport a) :
    Prime p := prime_of_normalized_factor p (Multiset.mem_toFinset.mp hp)

/-- Squarefree Euler phi; the unit has empty support and phi one. -/
def squarefreePhi (a : Associates GaussianInt) : ℝ :=
  ∏ p ∈ primeSupport a, ((classNorm p : ℝ) - 1)

lemma squarefreePhi_one_le (a : Associates GaussianInt) : 1 ≤ squarefreePhi a := by
  apply one_le_prod
  intro p hp
  have h : (2 : ℝ) ≤ classNorm p := by
    exact_mod_cast classNorm_prime_two_le (prime_of_mem_primeSupport hp)
  linarith

lemma squarefreePhi_pos (a : Associates GaussianInt) : 0 < squarefreePhi a :=
  lt_of_lt_of_le zero_lt_one (squarefreePhi_one_le a)

lemma primeSupport_prod {a : Associates GaussianInt} (ha : Squarefree a) :
    (∏ p ∈ primeSupport a, p) = a := by
  have hn := (squarefree_iff_nodup_normalizedFactors ha.ne_zero).mp ha
  have he : (primeSupport a).val = normalizedFactors a := Multiset.dedup_eq_self.mpr hn
  simp only [Finset.prod, Multiset.map_id']
  rw [he]
  exact associated_iff_eq.mp (prod_normalizedFactors ha.ne_zero)

lemma classNorm_prod (S : Finset (Associates GaussianInt)) :
    classNorm (∏ p ∈ S, p) = ∏ p ∈ S, classNorm p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [classNorm_one]
  | @insert p S hp ih => rw [prod_insert hp, prod_insert hp, classNorm_mul, ih]


/-- Squarefree support excludes zero even at cutoff zero. -/
def squarefreeBall (D : ℝ) : Finset (Associates GaussianInt) := by
  classical
  exact (classBall D).filter Squarefree

lemma mem_squarefreeBall {D : ℝ} (hD : 0 ≤ D) (a : Associates GaussianInt) :
    a ∈ squarefreeBall D ↔ Squarefree a ∧ (classNorm a : ℝ) ≤ D := by
  classical
  rw [squarefreeBall, mem_filter, mem_classBall hD]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.ne_zero, h.2⟩, h.1⟩⟩

def squarefreeMass (D : ℝ) : ℝ :=
  ∑ a ∈ squarefreeBall D, 1 / squarefreePhi a

def reciprocalMass (D : ℝ) : ℝ :=
  ∑ a ∈ classBall D, 1 / (classNorm a : ℝ)

lemma classBall_mono {D E : ℝ} (hD : 0 ≤ D) (hDE : D ≤ E) :
    classBall D ⊆ classBall E := by
  intro a ha
  obtain ⟨ha0, haD⟩ := (mem_classBall hD a).mp ha
  exact (mem_classBall (hD.trans hDE) a).mpr ⟨ha0, haD.trans hDE⟩


/-- A finite annulus estimate ready for summation over dyadic annuli. -/
theorem annulus_reciprocal_lower {E D : ℝ} (hE : 0 ≤ E) (hED : E ≤ D) (hD : 0 < D) :
    ((Real.pi / 4) * (D - E) -
      (Real.pi + 1) * (Real.sqrt D + Real.sqrt E + 2)) / D ≤
      ∑ a ∈ classBall D \ classBall E, 1 / (classNorm a : ℝ) := by
  classical
  have hsub := classBall_mono hE hED
  have hc : (((classBall D \ classBall E).card : ℕ) : ℝ) +
      ((classBall E).card : ℝ) = ((classBall D).card : ℝ) := by
    exact_mod_cast card_sdiff_add_card_eq_card hsub
  have hl := (abs_le.mp (classBall_card_error hD.le)).1
  have hu := (abs_le.mp (classBall_card_error hE)).2
  have hcount : (Real.pi / 4) * (D - E) -
      (Real.pi + 1) * (Real.sqrt D + Real.sqrt E + 2) ≤
        ((classBall D \ classBall E).card : ℝ) := by
    nlinarith
  calc
    _ ≤ ((classBall D \ classBall E).card : ℝ) / D :=
      div_le_div_of_nonneg_right hcount hD.le
    _ = ∑ _a ∈ classBall D \ classBall E, 1 / D := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro a ha
      obtain ⟨ha0, haD⟩ := (mem_classBall hD.le a).mp (mem_sdiff.mp ha).1
      have hn : (0 : ℝ) < classNorm a := by
        exact_mod_cast (classNorm_pos a).mpr ha0
      exact one_div_le_one_div_of_le hn haD


lemma squarefree_prime_prod (S : Finset (Associates GaussianInt))
    (hS : ∀ p ∈ S, Prime p) : Squarefree (∏ p ∈ S, p) := by
  classical
  have hz : (∏ p ∈ S, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have hf : normalizedFactors (∏ p ∈ S, p) = S.val := by
    simpa only [Finset.prod, Multiset.map_id'] using
      (normalizedFactors_prod_of_prime (m := S.val) hS)
  rw [squarefree_iff_nodup_normalizedFactors hz, hf]
  exact S.nodup

lemma primeSupport_prime_prod (S : Finset (Associates GaussianInt))
    (hS : ∀ p ∈ S, Prime p) : primeSupport (∏ p ∈ S, p) = S := by
  have hf : normalizedFactors (∏ p ∈ S, p) = S.val := by
    simpa only [Finset.prod, Multiset.map_id'] using
      (normalizedFactors_prod_of_prime (m := S.val) hS)
  simp [primeSupport, hf]

lemma primeSupport_injective_squarefree {a b : Associates GaussianInt}
    (ha : Squarefree a) (hb : Squarefree b) (h : primeSupport a = primeSupport b) :
    a = b := by
  calc
    a = ∏ p ∈ primeSupport a, p := (primeSupport_prod ha).symm
    _ = ∏ p ∈ primeSupport b, p := by rw [h]
    _ = b := primeSupport_prod hb

lemma primeSupport_subset_norm_le {a : Associates GaussianInt} (ha : Squarefree a)
    {S : Finset (Associates GaussianInt)} (hS : S ⊆ primeSupport a) :
    classNorm (∏ p ∈ S, p) ≤ classNorm a := by
  have hn : classNorm a = ∏ p ∈ primeSupport a, classNorm p := by
    calc
      classNorm a = classNorm (∏ p ∈ primeSupport a, p) :=
        congrArg classNorm (primeSupport_prod ha).symm
      _ = _ := classNorm_prod _
  rw [classNorm_prod, hn]
  apply prod_le_prod_of_subset_of_one_le' hS
  intro p hp _
  exact le_trans (by norm_num) (classNorm_prime_two_le (prime_of_mem_primeSupport hp))


end DistanceCounts.GaussianMass
end
end

-- Source: DistanceCounts/GaussianMoments.lean
section
/-! Finite, point-weighted moments on the actual nonzero Gaussian disk. -/

noncomputable section

namespace DistanceCounts.GaussianMoments

open Finset GaussianDivisibility
open scoped BigOperators Classical

/-- Number of primes in `T` dividing the norm of the actual vector `z`. -/
def splitOmega (T : Finset ℕ) (z : GaussianInt) : ℕ :=
  (T.filter (fun p => p ∣ z.norm.natAbs)).card

/-- The sum of local densities, not an assumed population mean. -/
def center (T : Finset ℕ) : ℝ := ∑ p ∈ T, splitDensity p

lemma splitDensity_nonneg_le_one {p : ℕ} (hp : p.Prime) :
    0 ≤ splitDensity p ∧ splitDensity p ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hi1 : 1 / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr hp1
  have he : splitDensity p = 1 - (1 - 1 / (p : ℝ)) ^ 2 := by
    unfold splitDensity
    field_simp [ne_of_gt hp0]
    <;> ring
  rw [he]
  constructor <;> nlinarith [sq_nonneg (1 - 1 / (p : ℝ)),
    mul_nonneg hi0 (sub_nonneg.mpr hi1)]


lemma representatives_sq {R : ℝ} (hR : 0 ≤ R) :
    GaussianMass.representatives (R ^ 2) = (gaussianDisk 0 R).erase 0 := by
  simp only [GaussianMass.representatives, Real.sqrt_sq hR]

/-- The population term in centering retains its own boundary error. -/
theorem population_card_error {R : ℝ} (hR : 0 ≤ R) :
    |((GaussianMass.representatives (R ^ 2)).card : ℝ) - Real.pi * R ^ 2| ≤
      (4 * Real.pi + 1) * (R + 1) := by
  rw [representatives_sq hR]
  apply erase_zero_card_error _ _ _ _ _ hR (gaussianDisk_card_error 0 hR)
  simpa only [mem_gaussianDisk, GaussianInt.toComplex_zero, dist_self] using hR

private def indicator (p : ℕ) (z : GaussianInt) : ℝ :=
  if p ∣ z.norm.natAbs then 1 else 0

private lemma splitOmega_cast (T : Finset ℕ) (z : GaussianInt) :
    (splitOmega T z : ℝ) = ∑ p ∈ T, indicator p z := by
  simp [splitOmega, indicator]

private lemma indicator_sum (p : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ GaussianMass.representatives (R ^ 2), indicator p z) =
      (((primeDisk p R).erase 0).card : ℝ) := by
  rw [representatives_sq hR]
  simp only [indicator, Finset.sum_boole]
  congr 2
  ext z
  simp only [Finset.mem_filter, Finset.mem_erase, primeDisk]
  tauto

private lemma indicator_mul_sum (p q : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ GaussianMass.representatives (R ^ 2), indicator p z * indicator q z) =
      (((primeDisk p R ∩ primeDisk q R).erase 0).card : ℝ) := by
  have hi (z : GaussianInt) : indicator p z * indicator q z =
      if p ∣ z.norm.natAbs ∧ q ∣ z.norm.natAbs then 1 else 0 := by
    unfold indicator
    split_ifs <;> simp_all
  simp_rw [hi]
  rw [representatives_sq hR]
  simp only [Finset.sum_boole]
  congr 2
  ext z
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter, primeDisk]
  tauto


private lemma centered_pair_identity (p q : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ GaussianMass.representatives (R ^ 2),
      (indicator p z - splitDensity p) * (indicator q z - splitDensity q)) =
      (((primeDisk p R ∩ primeDisk q R).erase 0).card : ℝ) -
        splitDensity q * (((primeDisk p R).erase 0).card : ℝ) -
        splitDensity p * (((primeDisk q R).erase 0).card : ℝ) +
        splitDensity p * splitDensity q *
          ((GaussianMass.representatives (R ^ 2)).card : ℝ) := by
  have hi (z : GaussianInt) :
      (indicator p z - splitDensity p) * (indicator q z - splitDensity q) =
        indicator p z * indicator q z - splitDensity q * indicator p z -
          splitDensity p * indicator q z + splitDensity p * splitDensity q := by ring
  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, indicator_mul_sum p q hR,
    indicator_sum p hR, indicator_sum q hR]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Ordered-pair covariance bound. The diagonal is treated by the first moment;
only distinct primes use the two-prime lattice estimate. -/
private lemma centered_pair_upper (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp4 : p % 4 = 1) (hq4 : q % 4 = 1) {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ GaussianMass.representatives (R ^ 2),
      (indicator p z - splitDensity p) * (indicator q z - splitDensity q)) ≤
      (if p = q then Real.pi * R ^ 2 * splitDensity p else 0) +
        (64 * Real.pi + 4) * (R + 1) := by
  let A := Real.pi * R ^ 2
  let E₀ := (4 * Real.pi + 1) * (R + 1)
  let E₁ := (12 * Real.pi + 1) * (R + 1)
  let E₂ := (36 * Real.pi + 1) * (R + 1)
  let cp : ℝ := ((primeDisk p R).erase 0).card
  let cq : ℝ := ((primeDisk q R).erase 0).card
  let J : ℝ := ((primeDisk p R ∩ primeDisk q R).erase 0).card
  let N : ℝ := (GaussianMass.representatives (R ^ 2)).card
  obtain ⟨hdp0, hdp1⟩ := splitDensity_nonneg_le_one hp
  obtain ⟨hdq0, hdq1⟩ := splitDensity_nonneg_le_one hq
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₁₂ : E₁ ≤ E₂ := by
    dsimp [E₁, E₂]
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_nonneg hR]
  have hcp : A * splitDensity p - E₁ ≤ cp := by
    have h := (abs_le.mp (primeDisk_erase_zero_card_error p hp hp4 hR)).1
    change -E₁ ≤ cp - A * splitDensity p at h
    linarith
  have hcq : A * splitDensity q - E₁ ≤ cq := by
    have h := (abs_le.mp (primeDisk_erase_zero_card_error q hq hq4 hR)).1
    change -E₁ ≤ cq - A * splitDensity q at h
    linarith
  have hN : N ≤ A + E₀ := by
    have h := (abs_le.mp (population_card_error hR)).2
    change N - A ≤ E₀ at h
    linarith
  have hJ : J ≤ A * splitDensity p * splitDensity q +
      (if p = q then A * splitDensity p else 0) + E₂ := by
    by_cases hpq : p = q
    · subst q
      have h := (abs_le.mp (primeDisk_erase_zero_card_error p hp hp4 hR)).2
      have hJcp : J = cp := by simp [J, cp]
      rw [hJcp, if_pos rfl]
      change cp - A * splitDensity p ≤ E₁ at h
      nlinarith [mul_nonneg hA (sq_nonneg (splitDensity p))]
    · have h := (abs_le.mp
        (primeDisk_inter_erase_zero_card_error p q hp hq hp4 hq4 hpq hR)).2
      change J - A * splitDensity p * splitDensity q ≤ E₂ at h
      rw [if_neg hpq]
      linarith
  have hprod0 := mul_nonneg hdp0 hdq0
  have hprod1 : splitDensity p * splitDensity q ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hdp1 hdq1 hdq0 (by norm_num)
      _ = _ := by ring
  have hcp' := mul_le_mul_of_nonneg_left hcp hdq0
  have hcq' := mul_le_mul_of_nonneg_left hcq hdp0
  have hN' := mul_le_mul_of_nonneg_left hN hprod0
  have hep := mul_le_mul_of_nonneg_left hdp1 hE₁
  have heq := mul_le_mul_of_nonneg_left hdq1 hE₁
  have heN := mul_le_mul_of_nonneg_left hprod1 hE₀
  rw [centered_pair_identity p q hR]
  change J - splitDensity q * cp - splitDensity p * cq +
    splitDensity p * splitDensity q * N ≤ _
  calc
    _ ≤ (if p = q then A * splitDensity p else 0) + E₂ +
        E₁ * splitDensity q + E₁ * splitDensity p +
        E₀ * (splitDensity p * splitDensity q) := by
      nlinarith [hJ, hcp', hcq', hN']
    _ ≤ (if p = q then A * splitDensity p else 0) + E₂ + E₁ + E₁ + E₀ := by
      linarith
    _ = _ := by dsimp [A, E₀, E₁, E₂]; ring

/-- The genuine finite centered second moment, normalized by disk area.
No assertion that the density center equals the empirical mean is used. -/
theorem centered_second_moment_upper (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ p % 4 = 1) {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ GaussianMass.representatives (R ^ 2),
      ((splitOmega T z : ℝ) - center T) ^ 2) ≤
      Real.pi * R ^ 2 * center T +
        (64 * Real.pi + 4) * (R + 1) * (T.card : ℝ) ^ 2 := by
  have hexpand (z : GaussianInt) : ((splitOmega T z : ℝ) - center T) ^ 2 =
      ∑ p ∈ T, ∑ q ∈ T,
        (indicator p z - splitDensity p) * (indicator q z - splitDensity q) := by
    rw [splitOmega_cast, center, ← Finset.sum_sub_distrib, pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  calc
    _ = ∑ z ∈ GaussianMass.representatives (R ^ 2), ∑ p ∈ T, ∑ q ∈ T,
        (indicator p z - splitDensity p) * (indicator q z - splitDensity q) :=
      Finset.sum_congr rfl (fun z _ => hexpand z)
    _ = ∑ p ∈ T, ∑ q ∈ T, ∑ z ∈ GaussianMass.representatives (R ^ 2),
        (indicator p z - splitDensity p) * (indicator q z - splitDensity q) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
    _ ≤ ∑ p ∈ T, ∑ q ∈ T,
        ((if p = q then Real.pi * R ^ 2 * splitDensity p else 0) +
          (64 * Real.pi + 4) * (R + 1)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact centered_pair_upper p q (hT p hp).1 (hT q hq).1
        (hT p hp).2 (hT q hq).2 hR
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      have hdiag : (∑ p ∈ T, ∑ q ∈ T,
          if p = q then Real.pi * R ^ 2 * splitDensity p else 0) =
          Real.pi * R ^ 2 * center T := by
        simp [center, ← Finset.mul_sum]
      rw [hdiag]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Deterministic Chebyshev inequality on the actual nonzero vector population. -/
theorem exceptional_card_mul_sq_le (T : Finset ℕ) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    (((GaussianMass.representatives (R ^ 2)).filter
      (fun z => a ≤ |(splitOmega T z : ℝ) - center T|)).card : ℝ) * a ^ 2 ≤
      ∑ z ∈ GaussianMass.representatives (R ^ 2),
        ((splitOmega T z : ℝ) - center T) ^ 2 := by
  let S := GaussianMass.representatives (R ^ 2)
  let E := S.filter (fun z => a ≤ |(splitOmega T z : ℝ) - center T|)
  change (E.card : ℝ) * a ^ 2 ≤ _
  calc
    _ = ∑ _z ∈ E, a ^ 2 := by simp
    _ ≤ ∑ z ∈ E, ((splitOmega T z : ℝ) - center T) ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      have h := (Finset.mem_filter.mp hz).2
      have hs := sq_abs ((splitOmega T z : ℝ) - center T)
      have hm := mul_nonneg (sub_nonneg.mpr h)
        (show 0 ≤ |(splitOmega T z : ℝ) - center T| + a by positivity)
      nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun z _ _ => sq_nonneg _)

/-- Exceptional-vector cardinal bound with an explicit universal boundary constant. -/
theorem exceptional_card_upper (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ p % 4 = 1) {R : ℝ} (hR : 0 ≤ R)
    {a : ℝ} (ha : 0 < a) :
    (((GaussianMass.representatives (R ^ 2)).filter
      (fun z => a ≤ |(splitOmega T z : ℝ) - center T|)).card : ℝ) ≤
      (Real.pi * R ^ 2 * center T +
        (64 * Real.pi + 4) * (R + 1) * (T.card : ℝ) ^ 2) / a ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  exact (exceptional_card_mul_sq_le T R ha).trans (centered_second_moment_upper T hT hR)

end DistanceCounts.GaussianMoments
end
end

-- Source: DistanceCounts/GaussianExcess.lean
section
/-! A uniform repeated-factor first moment on the actual nonzero Gaussian disk. -/

noncomputable section

namespace DistanceCounts.GaussianExcess

open Finset GaussianDivisibility

/-- Repeated rational-prime factors of the actual Gaussian norm. -/
def excess (T : Finset ℕ) (z : GaussianInt) : ℕ :=
  ∑ p ∈ T, (z.norm.natAbs.factorization p - 1)

/-- Allocate every factor of a split prime power to one of its two Gaussian factors. -/
theorem split_pow_dvd_norm {p : ℕ} (hp : p.Prime) {a : GaussianInt}
    (ha : a.norm.natAbs = p) (k : ℕ) (z : GaussianInt)
    (h : p ^ k ∣ z.norm.natAbs) :
    ∃ j ≤ k, a ^ j * star a ^ (k - j) ∣ z := by
  induction k generalizing z with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ k ih =>
    have hpz : p ∣ z.norm.natAbs := dvd_trans (dvd_pow_self p (by omega)) h
    rcases (split_dvd_norm_iff hp ha z).mp hpz with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · have hu : p ^ k ∣ u.norm.natAbs := by
        have hh : p * p ^ k ∣ p * u.norm.natAbs := by
          simpa [pow_succ, Zsqrtd.norm_mul, Int.natAbs_mul, ha, mul_comm] using h
        exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hh
      obtain ⟨j, hj, v, hv⟩ := ih u hu
      refine ⟨j + 1, by omega, v, ?_⟩
      rw [hv, show k + 1 - (j + 1) = k - j by omega, pow_succ]
      ring
    · have hu : p ^ k ∣ u.norm.natAbs := by
        have hh : p * p ^ k ∣ p * u.norm.natAbs := by
          simpa [pow_succ, Zsqrtd.norm_mul, Int.natAbs_mul, ha, mul_comm] using h
        exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hh
      obtain ⟨j, hj, v, hv⟩ := ih u hu
      refine ⟨j, by omega, v, ?_⟩
      rw [hv, show k + 1 - j = (k - j) + 1 by omega, pow_succ]
      ring

lemma allocated_norm {p : ℕ} {a : GaussianInt} (ha : a.norm.natAbs = p)
    {j k : ℕ} (hj : j ≤ k) :
    (a ^ j * star a ^ (k - j)).norm.natAbs = p ^ k := by
  have hpow (b : GaussianInt) (m : ℕ) :
      (b ^ m).norm.natAbs = b.norm.natAbs ^ m := by
    induction m with
    | zero => simp
    | succ m ih => simp [pow_succ, Zsqrtd.norm_mul, Int.natAbs_mul, ih]
  simp only [Zsqrtd.norm_mul, Int.natAbs_mul, hpow,
    Zsqrtd.norm_conj, ha]
  rw [← pow_add, Nat.add_sub_of_le hj]

/-- The norm-prime-power event is covered by `k + 1` genuine divisor lattices. -/
theorem pow_event_subset_biUnion {p : ℕ} (hp : p.Prime) {a : GaussianInt}
    (ha : a.norm.natAbs = p) (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (GaussianMass.representatives (R ^ 2)).filter (fun z => p ^ k ∣ z.norm.natAbs) ⊆
      (range (k + 1)).biUnion
        (fun j => (divisorDisk (a ^ j * star a ^ (k - j)) R).erase 0) := by
  classical
  intro z hz
  obtain ⟨hz, hdiv⟩ := mem_filter.mp hz
  have hz' : z ∈ (gaussianDisk 0 R).erase 0 := by
    simpa [GaussianMass.representatives, Real.sqrt_sq hR] using hz
  obtain ⟨hz0, hzR⟩ := mem_erase.mp hz'
  obtain ⟨j, hj, hd⟩ := split_pow_dvd_norm hp ha k z hdiv
  exact mem_biUnion.mpr ⟨j, mem_range.mpr (by omega), mem_erase.mpr
    ⟨hz0, mem_filter.mpr ⟨hzR, hd⟩⟩⟩

/-- Uniform higher-divisibility bound, including prime powers larger than the disk. -/
theorem pow_event_card_upper (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (((GaussianMass.representatives (R ^ 2)).filter
      (fun z => p ^ k ∣ z.norm.natAbs)).card : ℝ) ≤
      9 * Real.pi * R ^ 2 * (k + 1) / (p : ℝ) ^ k := by
  classical
  obtain ⟨a, ha⟩ := exists_split_factor p hp hp4
  have hcard := (card_le_card (pow_event_subset_biUnion hp ha k hR)).trans
    card_biUnion_le
  have hc : (((GaussianMass.representatives (R ^ 2)).filter
      (fun z => p ^ k ∣ z.norm.natAbs)).card : ℝ) ≤
      ∑ j ∈ range (k + 1), (((divisorDisk
        (a ^ j * star a ^ (k - j)) R).erase 0).card : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ j ∈ range (k + 1), (((divisorDisk
        (a ^ j * star a ^ (k - j)) R).erase 0).card : ℝ) := hc
    _ ≤ ∑ _j ∈ range (k + 1), 9 * Real.pi * R ^ 2 / (p : ℝ) ^ k := by
      apply sum_le_sum
      intro j hj
      have hn := allocated_norm ha (Nat.le_of_lt_succ (mem_range.mp hj))
      have hd : a ^ j * star a ^ (k - j) ≠ 0 := by
        intro he
        have hh : p ^ k = 0 := by simpa [he] using hn.symm
        exact (pow_ne_zero k hp.ne_zero) hh
      have he := divisorDisk_erase_zero_card_upper _ hd hR
      simpa only [normMass, hn, Nat.cast_pow] using he
    _ = _ := by simp; ring

lemma split_prime_five_le {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) : 5 ≤ p := by
  have := hp.two_le
  omega

/-- An elementary finite geometric-tail bound; no infinite sum interchange is needed. -/
lemma power_tail_sum_le (p N : ℕ) (hp : 5 ≤ p) :
    (∑ k ∈ range N, ((k : ℝ) + 3) / (p : ℝ) ^ (k + 2)) ≤ 6 / (p : ℝ) ^ 2 := by
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hstep (k : ℕ) :
      ((k : ℝ) + 3) / (p : ℝ) ^ (k + 2) ≤
        2 * ((k : ℝ) + 3) / (p : ℝ) ^ (k + 2) -
          2 * ((k : ℝ) + 4) / (p : ℝ) ^ (k + 3) := by
    have hratio : 2 * ((k : ℝ) + 4) ≤ ((k : ℝ) + 3) * (p : ℝ) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k,
        mul_nonneg (sub_nonneg.mpr hpR) (show 0 ≤ (k : ℝ) + 3 by positivity)]
    have hdec : 2 * ((k : ℝ) + 4) / (p : ℝ) ^ (k + 3) ≤
        ((k : ℝ) + 3) / (p : ℝ) ^ (k + 2) := by
      rw [show k + 3 = (k + 2) + 1 by omega, pow_succ,
        mul_comm ((p : ℝ) ^ (k + 2)) (p : ℝ), ← div_div]
      exact div_le_div_of_nonneg_right ((div_le_iff₀ hp0).mpr hratio) (by positivity)
    calc
      _ ≤ ((k : ℝ) + 3) / (p : ℝ) ^ (k + 2) +
          (((k : ℝ) + 3) / (p : ℝ) ^ (k + 2) -
            2 * ((k : ℝ) + 4) / (p : ℝ) ^ (k + 3)) :=
        le_add_of_nonneg_right (sub_nonneg.mpr hdec)
      _ = _ := by ring
  have hsum (n : ℕ) :
      (∑ k ∈ range n, ((k : ℝ) + 3) / (p : ℝ) ^ (k + 2)) ≤
        6 / (p : ℝ) ^ 2 - 2 * ((n : ℝ) + 3) / (p : ℝ) ^ (n + 2) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ]
      have hs := hstep n
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      rw [show (n : ℝ) + 1 + 3 = (n : ℝ) + 4 by ring,
        show n + 1 + 2 = n + 3 by omega]
      linarith only [ih, hs]
  exact (hsum N).trans (sub_le_self _ (by positivity))

/-- Layer-cake identity for one valuation, with a genuinely finite cutoff. -/
lemma valuation_excess_eq_sum {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (N : ℕ) (hN : n.factorization p - 1 ≤ N) :
    ((n.factorization p - 1 : ℕ) : ℝ) =
      ∑ k ∈ range N, if p ^ (k + 2) ∣ n then (1 : ℝ) else 0 := by
  classical
  rw [sum_boole]
  have he : (range N).filter (fun k => p ^ (k + 2) ∣ n) =
      range (n.factorization p - 1) := by
    ext k
    simp only [mem_filter, mem_range, hp.pow_dvd_iff_le_factorization hn]
    omega
  rw [he, card_range]

/-- First moment of one repeated split-prime valuation on actual Gaussian vectors. -/
theorem prime_excess_sum_le (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ GaussianMass.representatives (R ^ 2),
      ((z.norm.natAbs.factorization p - 1 : ℕ) : ℝ)) ≤
      54 * Real.pi * R ^ 2 / (p : ℝ) ^ 2 := by
  classical
  let S := GaussianMass.representatives (R ^ 2)
  let N := S.sup (fun z => z.norm.natAbs.factorization p - 1)
  have hlayer (z : GaussianInt) (hz : z ∈ S) :
      ((z.norm.natAbs.factorization p - 1 : ℕ) : ℝ) =
        ∑ k ∈ range N, if p ^ (k + 2) ∣ z.norm.natAbs then (1 : ℝ) else 0 := by
    have hz0 := ((GaussianMass.mem_representatives (sq_nonneg R) z).mp hz).1
    have hn : z.norm.natAbs ≠ 0 := by
      intro hn
      exact hz0 (GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp hn))
    exact valuation_excess_eq_sum hp hn N
      (le_sup (f := fun z : GaussianInt => z.norm.natAbs.factorization p - 1) hz)
  calc
    _ = ∑ k ∈ range N, ((S.filter (fun z => p ^ (k + 2) ∣ z.norm.natAbs)).card : ℝ) := by
      change (∑ z ∈ S, _) = _
      rw [sum_congr rfl hlayer, sum_comm]
      simp only [sum_boole]
    _ ≤ ∑ k ∈ range N, 9 * Real.pi * R ^ 2 *
        (((k : ℝ) + 3) / (p : ℝ) ^ (k + 2)) := by
      apply sum_le_sum
      intro k hk
      have he := pow_event_card_upper p hp hp4 (k + 2) hR
      have hkcast : ((k + 2 : ℕ) : ℝ) + 1 = (k : ℝ) + 3 := by
        push_cast
        ring
      simpa only [hkcast, mul_div_assoc] using he
    _ = 9 * Real.pi * R ^ 2 *
        (∑ k ∈ range N, ((k : ℝ) + 3) / (p : ℝ) ^ (k + 2)) := by
      rw [mul_sum]
    _ ≤ 9 * Real.pi * R ^ 2 * (6 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (power_tail_sum_le p N (split_prime_five_le hp hp4))
        (by positivity)
    _ = _ := by ring

/-- A deliberately loose, universal reciprocal-square bound for arbitrary finite split sets. -/
lemma reciprocal_square_sum_le (T : Finset ℕ)
    (hT : ∀ p ∈ T, 5 ≤ p) : (∑ p ∈ T, 1 / (p : ℝ) ^ 2) ≤ 2 := by
  let b : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hb (n : ℕ) : 0 ≤ b n - b (n + 1) := by
    dsimp [b]
    push_cast
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have ht (p : ℕ) (hp : 5 ≤ p) : 1 / (p : ℝ) ^ 2 ≤ 2 * (b p - b (p + 1)) := by
    have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp
    dsimp [b]
    push_cast
    have hp0 : (0 : ℝ) < p := by linarith
    have hp1 : (0 : ℝ) < p + 1 := by linarith
    have hp2 : (0 : ℝ) < p + 2 := by linarith
    field_simp
    nlinarith [sq_nonneg ((p : ℝ) - 5)]
  have htel (n : ℕ) : (∑ k ∈ range n, (b k - b (k + 1))) = 1 - b n := by
    induction n with
    | zero => simp [b]
    | succ n ih => rw [sum_range_succ, ih]; ring
  have hsub : T ⊆ range (T.sup id + 1) := by
    intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hp))
  calc
    _ ≤ ∑ p ∈ T, 2 * (b p - b (p + 1)) := sum_le_sum (fun p hp => ht p (hT p hp))
    _ = 2 * ∑ p ∈ T, (b p - b (p + 1)) := by rw [mul_sum]
    _ ≤ 2 * ∑ p ∈ range (T.sup id + 1), (b p - b (p + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hb p)
    _ = 2 * (1 - b (T.sup id + 1)) := by rw [htel]
    _ ≤ 2 := by
      have : 0 ≤ b (T.sup id + 1) := by
        dsimp [b]
        positivity
      linarith

/-- Uniform repeated split-factor first moment; the constant is independent of the finite
prime set and the radius. All events above count actual nonzero Gaussian integers. -/
theorem excess_sum_le (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ p % 4 = 1) {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ GaussianMass.representatives (R ^ 2), (excess T z : ℝ)) ≤
      (108 * Real.pi) * R ^ 2 := by
  classical
  calc
    _ = ∑ z ∈ GaussianMass.representatives (R ^ 2), ∑ p ∈ T,
        ((z.norm.natAbs.factorization p - 1 : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro z _
      change ((∑ p ∈ T, (z.norm.natAbs.factorization p - 1) : ℕ) : ℝ) = _
      exact Nat.cast_sum (R := ℝ) T (fun p => z.norm.natAbs.factorization p - 1)
    _ = ∑ p ∈ T, ∑ z ∈ GaussianMass.representatives (R ^ 2),
        ((z.norm.natAbs.factorization p - 1 : ℕ) : ℝ) := sum_comm
    _ ≤ ∑ p ∈ T, 54 * Real.pi * R ^ 2 / (p : ℝ) ^ 2 :=
      sum_le_sum (fun p hp => prime_excess_sum_le p (hT p hp).1 (hT p hp).2 hR)
    _ = (54 * Real.pi * R ^ 2) * ∑ p ∈ T, 1 / (p : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ (54 * Real.pi * R ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left (reciprocal_square_sum_le T
        (fun p hp => split_prime_five_le (hT p hp).1 (hT p hp).2)) (by positivity)
    _ = _ := by ring

end DistanceCounts.GaussianExcess
end
end

noncomputable section
open Finset Filter
open scoped Topology
namespace DistanceCounts.PrimeProgressions
def splitPrimeReciprocal (N : ℕ) : ℝ :=
  ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p % 4 = 1), 1 / (p : ℝ)


end DistanceCounts.PrimeProgressions
namespace DistanceCounts.MertensTransfer
def kernel (x : ℝ) : ℝ := 1 / (x * Real.log x)

lemma kernel_pos {x : ℝ} (hx : 2 ≤ x) : 0 < kernel x := by
  exact one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos (by linarith)))

lemma kernel_antitone : AntitoneOn kernel (Set.Ici 2) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  change 2 ≤ y at hy
  apply one_div_le_one_div_of_le
  · exact mul_pos (by linarith [hx]) (Real.log_pos (by linarith [hx]))
  · exact mul_le_mul hxy (Real.log_le_log (by linarith [hx]) hxy)
      (Real.log_pos (by linarith [hx])).le (by linarith [hy])

lemma integral_kernel {y : ℝ} (hy : 2 ≤ y) :
    (∫ x in (2 : ℝ)..y, kernel x) = Real.log (Real.log y) - Real.log (Real.log 2) := by
  have hanti : AntitoneOn kernel (Set.uIcc 2 y) := by
    rw [Set.uIcc_of_le hy]
    exact kernel_antitone.mono Set.Icc_subset_Ici_self
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hanti.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hy] at hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hx1 : x ≠ 1 := by linarith [hx.1]
  have hxm : x ≠ -1 := by linarith [hx.1]
  simpa [kernel, one_div, div_eq_mul_inv, mul_inv_rev, mul_comm] using
    Real.hasDerivAt_log_log hx0 hx1 hxm

/-- Integral comparison with an error bounded independently of the endpoint. -/
lemma kernel_sum_bounds {N : ℕ} (hN : 2 ≤ N) :
    Real.log (Real.log N) - Real.log (Real.log 2) ≤ ∑ k ∈ Ico 2 N, kernel k ∧
    (∑ k ∈ Ico 2 N, kernel k) ≤
      Real.log (Real.log N) - Real.log (Real.log 2) + kernel 2 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : AntitoneOn kernel (Set.Icc (2 : ℝ) N) :=
    kernel_antitone.mono Set.Icc_subset_Ici_self
  have hlo := ha.integral_le_sum_Ico hN
  have hhi := ha.sum_le_integral_Ico hN
  norm_num only [Nat.cast_ofNat] at hlo hhi
  rw [integral_kernel hNr] at hlo hhi
  have hshift : (∑ k ∈ Ico 2 N, kernel (k + 1 : ℕ)) =
      (∑ k ∈ Ico 2 N, kernel k) + kernel N - kernel 2 := by
    rw [Finset.sum_Ico_add' (fun k : ℕ => kernel k) 2 N 1]
    have ht := sum_Ico_succ_top hN (fun k : ℕ => kernel k)
    have hb := sum_eq_sum_Ico_succ_bot (show 2 < N + 1 by omega)
      (fun k : ℕ => kernel k)
    norm_num only [Nat.cast_ofNat] at hb
    linarith
  rw [hshift] at hhi
  exact ⟨hlo, by linarith [kernel_pos hNr]⟩

lemma tendsto_loglog :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

end DistanceCounts.MertensTransfer
end

/-! The two prime estimates needed for the Gaussian construction, from
the elementary convolution proof of Mertens' first theorem and the real
nonprincipal character modulo four. -/
noncomputable section
open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction
namespace DistanceCounts.ElementaryProgressions

def chi (n : ℕ) : ℝ := (ZMod.χ₄ n : ℤ)

private def chiPartial (n : ℕ) : ℝ := if n % 4 = 2 ∨ n % 4 = 3 then 1 else 0

private theorem chiPartial_bounds (n : ℕ) : 0 ≤ chiPartial n ∧ chiPartial n ≤ 1 := by
  unfold chiPartial
  split <;> norm_num

private theorem chi_step (n : ℕ) : chi n = chiPartial (n+1) - chiPartial n := by
  simp only [chi, chiPartial, ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> first | norm_num | omega
  all_goals omega

private theorem chi_abs (n : ℕ) : |chi n| ≤ 1 := by
  rw [chi_step,abs_le]
  constructor <;> linarith [(chiPartial_bounds n).1,(chiPartial_bounds n).2,
    (chiPartial_bounds (n+1)).1,(chiPartial_bounds (n+1)).2]

private theorem chi_mul (a b : ℕ) : chi (a*b) = chi a * chi b := by
  simp only [chi, Nat.cast_mul, map_mul, Int.cast_mul]

/-- A decreasing nonnegative weight costs at most its first term on any interval. -/
private theorem interval_cancel (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hf : ∀ k, a ≤ k → 0 ≤ f k)
    (hm : ∀ k, a ≤ k → f (k+1) ≤ f k) :
    |∑ k ∈ Ico a b, chi k * f k| ≤ f a := by
  have bounds (n : ℕ) (hn : a ≤ n) :
      f n * chiPartial n - f a * chiPartial a ≤ ∑ k ∈ Ico a n, chi k * f k ∧
      (∑ k ∈ Ico a n, chi k * f k) ≤ f n * chiPartial n - f a * chiPartial a + f a - f n := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [sum_Ico_succ_top hn,chi_step]
      have hp := chiPartial_bounds (n+1)
      have hd := sub_nonneg.mpr (hm n hn)
      constructor <;> nlinarith only [ih.1,ih.2,mul_nonneg hd hp.1,
        mul_nonneg hd (sub_nonneg.mpr hp.2)]
  have hb := bounds b hab
  have hfa := hf a le_rfl
  have hfb := hf b hab
  have hpa := chiPartial_bounds a
  have hpb := chiPartial_bounds b
  apply abs_le.mpr
  constructor <;> nlinarith only [hb.1,hb.2,mul_nonneg hfa hpa.1,
    mul_nonneg hfa (sub_nonneg.mpr hpa.2),mul_nonneg hfb hpb.1,
    mul_nonneg hfb (sub_nonneg.mpr hpb.2)]

def H (n : ℕ) : ℝ := ∑ k ∈ Ioc 0 n, chi k / k

private theorem H_tail {m n : ℕ} (hmn : m ≤ n) : |H n - H m| ≤ 1 / ((m:ℝ)+1) := by
  have hI (j : ℕ) : Ioc 0 j = Ico 1 (j+1) := by ext k; simp; omega
  have hi : H n - H m = ∑ k ∈ Ico (m+1) (n+1), chi k * (1 / (k : ℝ)) := by
    unfold H
    simp only [hI, ← sum_Ico_consecutive (fun k : ℕ => chi k / k) (show 1 ≤ m+1 by omega) (show m+1 ≤ n+1 by omega), mul_one_div, add_sub_cancel_left]
  rw [hi]
  have h := interval_cancel (fun k : ℕ => 1/(k:ℝ)) (m+1) (n+1) (by omega)
    (by intros; positivity) (by
      intro k hk
      exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < k by omega))
        (by exact_mod_cast (Nat.le_succ k)))
  simpa using h

private theorem H_lower {n : ℕ} (hn : 1 ≤ n) : 1 / 2 ≤ H n := by
  have h := (abs_le.mp (H_tail hn)).1
  have h1 : H 1 = 1 := by norm_num [H,chi,ZMod.χ₄_nat_eq_if_mod_four]
  rw [h1] at h
  norm_num at h
  linarith

private theorem log_weight_antitone (k : ℕ) (hk : 4 ≤ k) :
    Real.log (k+1 : ℕ) / (k+1 : ℕ) ≤ Real.log k / k := by
  apply Real.log_div_self_antitoneOn
  · change Real.exp 1 ≤ (k : ℝ)
    linarith [Real.exp_one_lt_d9, (show (4:ℝ) ≤ k by exact_mod_cast hk)]
  · change Real.exp 1 ≤ ((k+1 : ℕ) : ℝ)
    linarith [Real.exp_one_lt_d9, (show (4:ℝ) ≤ (k+1 : ℕ) by exact_mod_cast (show 4 ≤ k+1 by omega))]
  · exact_mod_cast Nat.le_succ k

private theorem log_chi_bounded : ∃ C : ℝ, ∀ n,
    |∑ k ∈ Ioc 0 n, chi k * (Real.log k / k)| ≤ C := by
  let f (k : ℕ) := chi k * (Real.log k / k)
  let C := ∑ k ∈ range 4, |f k|
  refine ⟨C + |Real.log 4|, ?_⟩
  intro n
  have hI : Ioc 0 n = Ico 1 (n+1) := by ext k; simp; omega
  rw [hI]
  change |∑ k ∈ Ico 1 (n+1), f k| ≤ _
  have hsmall (S : Finset ℕ) (hS : S ⊆ range 4) :
      |∑ k ∈ S, f k| ≤ C := (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum_of_subset_of_nonneg hS (by intros; positivity))
  by_cases hn : n+1 ≤ 4
  · exact (hsmall _ (fun k hk => mem_range.mpr ((mem_Ico.mp hk).2.trans_le hn))).trans
      (le_add_of_nonneg_right (abs_nonneg _))
  · rw [← sum_Ico_consecutive f (by decide : 1 ≤ 4) (show 4 ≤ n+1 by omega)]
    have htail := interval_cancel (fun k : ℕ => Real.log k / k) 4 (n+1) (by omega)
      (by intro k hk; exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))) (by positivity))
      (fun k hk => log_weight_antitone k hk)
    exact (abs_add_le _ _).trans (add_le_add (hsmall _ (fun k hk => mem_range.mpr (mem_Ico.mp hk).2))
      (htail.trans (by norm_num; linarith [le_abs_self (Real.log 4), Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)])))

private theorem log_convolution (N : ℕ) :
    (∑ n ∈ Ioc 0 N, chi n * (Real.log n / n)) =
       ∑ d ∈ Ioc 0 N, (chi d * Λ d / d) * H (N/d) := by
  let f : ArithmeticFunction ℝ := ⟨fun d => chi d * Λ d / d, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨fun d => chi d / d, by simp⟩
  have eval (n : ℕ) : (f*g) n = chi n * (Real.log n / n) := by
    rw [ArithmeticFunction.mul_apply]
    calc
      _ = ∑ v ∈ n.divisorsAntidiagonal, chi n / n * Λ v.1 := by
        apply sum_congr rfl
        intro v hv
        obtain ⟨a,b⟩ := v
        have hm : a*b = n := (Nat.mem_divisorsAntidiagonal.mp hv).1
        subst n
        change chi a * Λ a / a * (chi b / b) = _
        rw [chi_mul,Nat.cast_mul]
        ring
      _ = _ := by
        rw [← mul_sum, Nat.sum_divisorsAntidiagonal (fun d _ => Λ d), vonMangoldt_sum]
        ring
  calc
    _ = ∑ n ∈ Ioc 0 N, (f*g) n := sum_congr rfl (fun n _ => (eval n).symm)
    _ = _ := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum f g N

private theorem psi_sum (N : ℕ) : ∑ d ∈ Ioc 0 N, Λ d ≤ (Real.log 4 + 4) * N := by
  have e : (∑ d ∈ Ioc 0 N, Λ d) = Chebyshev.psi N := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
    simp
  rw [e]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)

private theorem signed_weight_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |∑ d ∈ Ioc 0 N, chi d * Λ d / d| ≤ C := by
  obtain ⟨c,hc⟩ := log_chi_bounded
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hc 1)
  let D := Real.log 4 + 4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2*(c+D),by positivity,?_⟩
  intro N hN
  let V (d : ℕ) := chi d * Λ d / d
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have herr (d : ℕ) (hd : d ∈ Ioc 0 N) :
      |V d * (H N - H (N/d))| ≤ Λ d / N := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
    have hdiv := H_tail (Nat.div_le_self N d)
    have hdN : (N:ℝ) ≤ (d:ℝ) * ((N/d:ℕ) + (1:ℝ)) := by
      exact_mod_cast (show N ≤ d * (N/d+1) by
        have hn := Nat.div_add_mod N d
        have hr := Nat.mod_lt N (mem_Ioc.mp hd).1
        rw [Nat.mul_add, Nat.mul_one]
        omega)
    have hsmall : 1 / ((N/d:ℕ) + (1:ℝ)) ≤ (d:ℝ) / N := by
      apply (div_le_div_iff₀ (by positivity) hNr).mpr
      linarith only [hdN]
    have h1 : |V d| ≤ Λ d / d := by
      rw [show V d = chi d * (Λ d / d) by dsimp [V]; ring, abs_mul,
        abs_of_nonneg (div_nonneg vonMangoldt_nonneg hd0.le)]
      simpa using mul_le_mul_of_nonneg_right (chi_abs d) (div_nonneg vonMangoldt_nonneg hd0.le)
    rw [abs_mul]
    calc
      _ ≤ (Λ d / d) * ((d:ℝ)/N) :=
        mul_le_mul h1 (hdiv.trans hsmall) (abs_nonneg _) (div_nonneg vonMangoldt_nonneg hd0.le)
      _ = _ := by field_simp
  have eh : |(∑ d ∈ Ioc 0 N, V d) * H N - (∑ n ∈ Ioc 0 N, chi n * (Real.log n/n))| ≤ D := by
    rw [log_convolution, sum_mul, ← sum_sub_distrib]
    change |∑ d ∈ Ioc 0 N, (V d * H N - V d * H (N/d))| ≤ D
    simp_rw [← mul_sub]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum herr).trans
    rw [← sum_div, div_le_iff₀ hNr]
    exact psi_sum N
  have eb := abs_add_le ((∑ d ∈ Ioc 0 N, V d) * H N - (∑ n ∈ Ioc 0 N, chi n * (Real.log n/n)))
    (∑ n ∈ Ioc 0 N, chi n * (Real.log n/n))
  rw [sub_add_cancel,abs_mul,abs_of_nonneg (by linarith [H_lower hN] : 0 ≤ H N)] at eb
  change |∑ d ∈ Ioc 0 N, V d| ≤ _
  nlinarith only [eb,eh,hc N,mul_nonneg (abs_nonneg (∑ d ∈ Ioc 0 N, V d)) (sub_nonneg.mpr (H_lower hN))]

private theorem all_weight_bound (N : ℕ) (hN : 1 ≤ N) :
    |(∑ d ∈ Ioc 0 N, Λ d / d) - Real.log N| ≤ Real.log 4 + 5 := by
  let S := ∑ n ∈ Ioc 0 N, Real.log n
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have conv : S = ∑ d ∈ Ioc 0 N, Λ d * (N / d : ℕ) := by
    have h := sum_Ioc_mul_zeta_eq_sum (Λ : ArithmeticFunction ℝ) N
    simpa only [vonMangoldt_mul_zeta, ArithmeticFunction.log_apply] using h
  have upper : S ≤ (N:ℝ)*Real.log N := by
    calc
      _ ≤ ∑ _d ∈ Ioc 0 N, Real.log N :=
        sum_le_sum (fun n hn => Real.log_le_log (by exact_mod_cast (mem_Ioc.mp hn).1)
          (by exact_mod_cast (mem_Ioc.mp hn).2))
      _ = _ := by simp
  have lower : (N:ℝ)*Real.log N - N ≤ S := by
    have h := MonotoneOn.integral_le_sum_Ico (f := Real.log) hN
      (Real.strictMonoOn_log.monotoneOn.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1))
    rw [integral_log] at h
    have he : (∑ i ∈ Ico 1 N, Real.log (i+1 : ℕ)) = S := by
      dsimp [S]
      rw [sum_Ico_add' (fun i : ℕ => Real.log i) 1 N 1]
      have hset : Ioc 0 N = insert 1 (Ico 2 (N+1)) := by ext i; simp; omega
      rw [hset,sum_insert (by simp)]
      simp
    rw [he] at h
    norm_num at h
    linarith
  have lowerS : S ≤ (∑ d ∈ Ioc 0 N, Λ d/d) * N := by
    rw [conv,sum_mul]
    apply sum_le_sum
    intro d hd
    have hdn : (d:ℝ) > 0 := by exact_mod_cast (mem_Ioc.mp hd).1
    have hh : ((N/d:ℕ):ℝ) * d ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
    simpa only [div_mul_eq_mul_div, mul_comm (Λ d) (N:ℝ)] using
      (show Λ d * ((N/d:ℕ):ℝ) ≤ Λ d / d * N by
        rw [div_mul_eq_mul_div, le_div_iff₀ hdn, mul_assoc]
        exact mul_le_mul_of_nonneg_left hh vonMangoldt_nonneg)
  have upperS : (∑ d ∈ Ioc 0 N, Λ d/d) * N ≤ S + (Real.log 4+4)*N := by
    rw [conv,sum_mul]
    apply le_trans _ (add_le_add_right (psi_sum N) _)
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hdn : (d:ℝ) > 0 := by exact_mod_cast (mem_Ioc.mp hd).1
    have hh : (N:ℝ) ≤ ((N/d:ℕ) + (1:ℝ))*d := by
      exact_mod_cast (show N ≤ (N/d+1)*d by
        have hm := Nat.div_add_mod N d
        have hr := Nat.mod_lt N (mem_Ioc.mp hd).1
        rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (N/d) d]
        omega)
    rw [div_mul_eq_mul_div, div_le_iff₀ hdn]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) (vonMangoldt_nonneg (n := d))]
  have hL : -1 ≤ (∑ d ∈ Ioc 0 N, Λ d/d) - Real.log N := by
    by_contra! bad
    nlinarith only [lower,lowerS,mul_neg_of_neg_of_pos (sub_neg.mpr bad) hNr]
  have hU : (∑ d ∈ Ioc 0 N, Λ d/d) - Real.log N ≤ Real.log 4 + 4 := by
    by_contra! bad
    nlinarith only [upper,upperS,mul_pos (sub_pos.mpr bad) hNr]
  rw [abs_le]
  constructor <;> linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]


def primeTerm (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

def classWeight (r N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, if n % 4 = r then primeTerm n else 0

private def remainderTerm (n : ℕ) : ℝ := (if n.Prime then 0 else Λ n) / n

private theorem rem_nonneg (n : ℕ) : 0 ≤ remainderTerm n := by
  unfold remainderTerm
  split_ifs <;> positivity

private theorem rem_sum : Summable remainderTerm := by
  have h := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  apply h.congr
  intro n
  have hz : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [remainderTerm, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, hz]

private theorem mangoldt_div_eq (n : ℕ) : Λ n / n = primeTerm n + remainderTerm n := by
  by_cases h : n.Prime
  · simp [primeTerm,remainderTerm,h,vonMangoldt_apply_prime h]
  · simp [primeTerm,remainderTerm,h]

private theorem primeTerm_nonneg (n : ℕ) : 0 ≤ primeTerm n := by
  unfold primeTerm
  split_ifs with h
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.one_lt.le)) (by positivity)
  · rfl

private theorem split_term (n : ℕ) :
    primeTerm n + chi n * primeTerm n =
      2*(if n%4=1 then primeTerm n else 0) + (if n=2 then primeTerm 2 else 0) ∧
    primeTerm n - chi n * primeTerm n =
      2*(if n%4=3 then primeTerm n else 0) + (if n=2 then primeTerm 2 else 0) := by
  by_cases hp : n.Prime
  · by_cases hn : n=2
    · subst n
      norm_num [chi,ZMod.χ₄_nat_eq_if_mod_four]
    · have ho := hp.odd_of_ne_two hn
      have ht := ho.not_two_dvd_nat
      rcases (show n%4=1 ∨ n%4=3 by omega) with h|h
      · simp [chi,ZMod.χ₄_nat_one_mod_four h,h,hn,two_mul]
      · simp [chi,ZMod.χ₄_nat_three_mod_four h,h,hn,two_mul]
  · have hn : n ≠ 2 := by rintro rfl; exact hp Nat.prime_two
    simp [primeTerm,hp,hn]

theorem classWeight_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ r : ℕ, r = 1 ∨ r = 3 →
    |classWeight r N - (1/2:ℝ)*Real.log N| ≤ C := by
  obtain ⟨D,hD,hs⟩ := signed_weight_bounded
  let R := ∑' n, remainderTerm n
  have hR : 0 ≤ R := tsum_nonneg rem_nonneg
  let C := Real.log 4 + 5 + D + 2*R + primeTerm 2
  have hC : 0 ≤ C := by dsimp [C]; positivity [primeTerm_nonneg 2]
  refine ⟨C,hC,?_⟩
  intro N hN r hr
  let A := ∑ n ∈ Ioc 0 N, primeTerm n
  let B := ∑ n ∈ Ioc 0 N, chi n * primeTerm n
  let T := ∑ n ∈ Ioc 0 N, if n=2 then primeTerm 2 else 0
  have hT : 0 ≤ T ∧ T ≤ primeTerm 2 := by
    dsimp [T]
    simp only [sum_ite_eq', mem_Ioc, Nat.zero_lt_succ, true_and]
    split_ifs <;> simp [primeTerm_nonneg]
  have rem_le : (∑ n ∈ Ioc 0 N, remainderTerm n) ≤ R :=
    rem_sum.sum_le_tsum _ (fun n _ => rem_nonneg n)
  have rem_ge : 0 ≤ ∑ n ∈ Ioc 0 N, remainderTerm n := sum_nonneg fun n _ => rem_nonneg n
  have hu := abs_le.mp (all_weight_bound N hN)
  simp_rw [mangoldt_div_eq, sum_add_distrib] at hu
  have hA : |A-Real.log N| ≤ Real.log 4+5+R := by
    apply abs_le.mpr
    constructor <;> dsimp [A] <;> linarith only [hu.1,hu.2,rem_le,rem_ge,hR]
  have hB' : |∑ n ∈ Ioc 0 N, chi n * remainderTerm n| ≤ R := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply le_trans _ rem_le
    apply sum_le_sum
    intro n _
    rw [abs_mul,abs_of_nonneg (rem_nonneg n)]
    simpa using mul_le_mul_of_nonneg_right (chi_abs n) (rem_nonneg n)
  have hB : |B| ≤ D+R := by
    have hv := hs N hN
    simp_rw [mul_div_assoc,mangoldt_div_eq,mul_add,sum_add_distrib] at hv
    have h := abs_le.mp hv
    have h' := abs_le.mp hB'
    apply abs_le.mpr
    constructor <;> dsimp [B] <;> linarith only [h.1,h.2,h'.1,h'.2]
  have h1 : A+B = 2 * classWeight 1 N + T := by
    dsimp [A,B,classWeight,T]
    rw [← sum_add_distrib,mul_sum,← sum_add_distrib]
    exact sum_congr rfl (fun n _ => (split_term n).1)
  have h3 : A-B = 2 * classWeight 3 N + T := by
    dsimp [A,B,classWeight,T]
    rw [← sum_sub_distrib,mul_sum,← sum_add_distrib]
    exact sum_congr rfl (fun n _ => (split_term n).2)
  have a := abs_le.mp hA
  have b := abs_le.mp hB
  rcases hr with rfl|rfl <;> apply abs_le.mpr <;> constructor <;> dsimp [C] at * <;>
    linarith only [a.1,a.2,b.1,b.2,hT.1,hT.2,h1,h3,hC]

/-- One fixed multiplicative interval suffices to find an inert prime. -/
theorem inert_interval : ∃ B : ℕ, 2 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ N ≤ p ∧ p < B * N := by
  obtain ⟨C,hC,h⟩ := classWeight_bound
  obtain ⟨K,hK⟩ := exists_nat_gt (max 2 (Real.exp (4*C+2)))
  have hk : (2:ℝ) < K := (le_max_left _ _).trans_lt hK
  have hk' : Real.exp (4*C+2) < K := (le_max_right _ _).trans_lt hK
  have hl : 4*C+2 < Real.log K := (Real.lt_log_iff_exp_lt (by linarith)).mpr hk'
  have hk2 : 2 ≤ K := by exact_mod_cast hk.le
  refine ⟨K+1,by omega,?_⟩
  intro N hN
  have hKN : 1 ≤ K*N := Nat.mul_pos (by omega) hN
  have ha := (abs_le.mp (h N hN 3 (Or.inr rfl))).2
  have hb := (abs_le.mp (h (K*N) hKN 3 (Or.inr rfl))).1
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by exact_mod_cast (show N ≠ 0 by omega))] at hb
  have hg : classWeight 3 N < classWeight 3 (K*N) := by linarith only [ha,hb,hl]
  by_contra! hn
  have hsub : Ioc 0 N ⊆ Ioc 0 (K*N) :=
    Ioc_subset_Ioc_right (by simpa using Nat.mul_le_mul_right N (show 1 ≤ K by omega))
  apply hg.ne
  apply sum_subset hsub
  intro n hn' hnN
  have lo : N < n := by have hh := mem_Ioc.mp hn'; by_contra! he; exact hnN (mem_Ioc.mpr ⟨hh.1,he⟩)
  by_cases hp : n.Prime
  · by_cases hr : n%4=3
    · have hh := hn n hp hr lo.le
      have hu := (mem_Ioc.mp hn').2
      rw [Nat.add_mul,Nat.one_mul] at hh
      omega
    · simp [hr]
  · simp [primeTerm,hp]


private theorem weighted_partial_bound (f u : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hU : ∀ n : ℕ, |∑ k ∈ range n, u k| ≤ M) (a b : ℕ) (hab : a ≤ b)
    (hf : ∀ k, a ≤ k → 0 ≤ f k) (hm : ∀ k, a ≤ k → f (k+1) ≤ f k) :
    |∑ k ∈ Ico a b, f k * u k| ≤ 2 * M * f a := by
  let U (n : ℕ) := ∑ k ∈ range n, u k
  have step (n : ℕ) : u n = U (n+1)-U n := by simp [U,Finset.sum_range_succ]
  have bounds (n : ℕ) (hn : a ≤ n) :
      f n * U n - f a * U a - M*(f a-f n) ≤ ∑ k ∈ Ico a n, f k * u k ∧
      (∑ k ∈ Ico a n, f k * u k) ≤ f n * U n - f a * U a + M*(f a-f n) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [sum_Ico_succ_top hn,step n]
      have h := abs_le.mp (hU (n+1))
      change -M ≤ U (n+1) ∧ U (n+1) ≤ M at h
      have hd := sub_nonneg.mpr (hm n hn)
      constructor <;> nlinarith only [ih.1,ih.2,
        mul_nonneg hd (sub_nonneg.mpr h.1),mul_nonneg hd (sub_nonneg.mpr h.2)]
  have h := bounds b hab
  have hp (k : ℕ) (hk : a ≤ k) : -(M*f k) ≤ f k * U k ∧ f k * U k ≤ M*f k := by
    have hh := abs_le.mp (hU k)
    change -M ≤ U k ∧ U k ≤ M at hh
    constructor <;> nlinarith only [mul_nonneg (hf k hk) (sub_nonneg.mpr hh.1),
      mul_nonneg (hf k hk) (sub_nonneg.mpr hh.2)]
  have p := hp a le_rfl
  have q := hp b hab
  apply abs_le.mpr
  constructor <;> linarith only [h.1,h.2,p.1,p.2,q.1,q.2]

private def centered (k : ℕ) : ℝ :=
  (if k%4=1 then primeTerm k else 0) - (1/2:ℝ)*(1/(k:ℝ))

private theorem centered_sums : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, |∑ k ∈ range n, centered k| ≤ M := by
  obtain ⟨C,hC,h⟩ := classWeight_bound
  refine ⟨C+1,by positivity,?_⟩
  rintro (_|n)
  · simp; linarith
  have he : (∑ k ∈ range (n+1), centered k) = classWeight 1 n - (1/2:ℝ) * harmonic n := by
    rw [Nat.range_succ_eq_Icc_zero, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
    simp only [centered, sum_sub_distrib, ← mul_sum, classWeight]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    have hI : Ioc 0 n = Icc 1 n := by ext k; simp; omega
    simp [hI,one_div]
  rw [he]
  rcases n with _|n
  · simp [classWeight]; linarith
  have hlogle : Real.log (n+1 : ℕ) ≤ harmonic (n+1) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ (n+1))).trans (log_add_one_le_harmonic _)
  have hhar := harmonic_le_one_add_log (n+1)
  have ha := abs_le.mp (h (n+1) (by omega) 1 (Or.inl rfl))
  apply abs_le.mpr
  constructor <;> linarith only [ha.1,ha.2,hlogle,hhar]

private def reciprocalTerm (k : ℕ) : ℝ :=
  if k.Prime ∧ k%4=1 then 1/(k:ℝ) else 0

private theorem reciprocal_limit_bound : ∃ D : ℝ, ∀ N : ℕ, 2 ≤ N →
    |PrimeProgressions.splitPrimeReciprocal N - (1/2:ℝ)*Real.log (Real.log N)| ≤ D := by
  obtain ⟨M,hM,hU⟩ := centered_sums
  let w (k : ℕ) : ℝ := 1 / Real.log k
  let C := 2*M*w 2
  refine ⟨C + |Real.log (Real.log 2)| + |MertensTransfer.kernel 2| + 1,?_⟩
  intro N hN
  have hw (n : ℕ) (hn : 2 ≤ n) : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hsum := weighted_partial_bound w centered hM hU 2 N hN (fun k hk => (one_div_pos.mpr (hw k hk)).le)
    (fun k hk => one_div_le_one_div_of_le (hw k hk)
      (Real.log_le_log (by exact_mod_cast (show 0<k by omega)) (by exact_mod_cast Nat.le_succ k)))
  have hiden (k : ℕ) (hk : 2 ≤ k) : w k * centered k =
      reciprocalTerm k - (1/2:ℝ)*MertensTransfer.kernel k := by
    have hk' : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
    by_cases hp : k.Prime <;> by_cases hr : k%4=1 <;>
      simp only [w,centered,primeTerm,reciprocalTerm,MertensTransfer.kernel,hp,hr,
        and_self, false_and, and_false, true_and, if_true, if_false] <;>
      field_simp [hk'.ne',(hw k hk).ne'] <;> ring
  rw [sum_congr rfl (fun k hk => hiden k (mem_Ico.mp hk).1),sum_sub_distrib,← mul_sum] at hsum
  have hproj : PrimeProgressions.splitPrimeReciprocal N = (∑ k ∈ Ico 2 N, reciprocalTerm k) + reciprocalTerm N := by
    have hs := sum_Ico_consecutive reciprocalTerm (Nat.zero_le 2) hN
    simp only [Nat.Ico_zero_eq_range] at hs
    have hr2 : ∑ k ∈ range 2, reciprocalTerm k = 0 := by
      norm_num [Finset.sum_range_succ,reciprocalTerm]
    rw [hr2,zero_add] at hs
    rw [PrimeProgressions.splitPrimeReciprocal,sum_filter,Finset.sum_range_succ]
    exact congrArg (· + reciprocalTerm N) hs.symm
  have hr : 0 ≤ reciprocalTerm N ∧ reciprocalTerm N ≤ 1 := by
    have hp : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
    dsimp [reciprocalTerm]
    split_ifs
    · exact ⟨by positivity, (div_le_iff₀ (by linarith)).mpr (by linarith)⟩
    · norm_num
  have hk := MertensTransfer.kernel_sum_bounds hN
  have hC := abs_le.mp hsum
  change -C ≤ _ ∧ _ ≤ C at hC
  rw [hproj,abs_le]
  constructor <;> linarith only [hC.1,hC.2,hk.1,hk.2,hr.1,hr.2,
    le_abs_self (Real.log (Real.log 2)), neg_abs_le (Real.log (Real.log 2)),
    le_abs_self (MertensTransfer.kernel 2),abs_nonneg (MertensTransfer.kernel 2)]

theorem reciprocal_limit :
    Tendsto (fun N : ℕ => PrimeProgressions.splitPrimeReciprocal N / Real.log (Real.log N))
      atTop (𝓝 (1/2:ℝ)) := by
  obtain ⟨D,hD⟩ := reciprocal_limit_bound
  have ht := MertensTransfer.tendsto_loglog
  have hinv := (tendsto_const_nhds (x := D)).div_atTop ht
  have hlow : Tendsto (fun N : ℕ => (1/2:ℝ) - D / Real.log (Real.log N)) atTop (𝓝 (1/2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1/2:ℝ))).sub hinv
  have hupp : Tendsto (fun N : ℕ => (1/2:ℝ) + D / Real.log (Real.log N)) atTop (𝓝 (1/2)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1/2:ℝ))).add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop 2,ht.eventually (eventually_gt_atTop (0:ℝ))] with N hN hp
    have h := (abs_le.mp (hD N hN)).1
    apply (le_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 2,ht.eventually (eventually_gt_atTop (0:ℝ))] with N hN hp
    have h := (abs_le.mp (hD N hN)).2
    apply (div_le_iff₀ hp).mpr
    rw [add_mul, div_mul_cancel₀ _ hp.ne']
    linarith

end DistanceCounts.ElementaryProgressions
end
namespace DistanceCounts.MertensTransfer

open Filter
open scoped Topology

theorem tendsto_splitPrimeReciprocal :
    Tendsto (fun N : ℕ => PrimeProgressions.splitPrimeReciprocal N / Real.log (Real.log N))
      atTop (𝓝 (1 / 2 : ℝ)) := ElementaryProgressions.reciprocal_limit

end DistanceCounts.MertensTransfer

-- Source: DistanceCounts/GaussianCutoff.lean
section
/-! Real-radius truncation, its actual density center, and its boundary error. -/

noncomputable section

namespace DistanceCounts.GaussianCutoff

open Filter Finset
open scoped Topology Classical

/-- The cutoff is taken at every real radius, not only at integral radii. -/
def cutoff (R : ℝ) : ℕ := ⌊R ^ (1 / 10 : ℝ)⌋₊

/-- The inclusive split-prime truncation used by the AP reciprocal sum. -/
def smallPrimes (R : ℝ) : Finset ℕ :=
  (range (cutoff R + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)

lemma mem_smallPrimes {R : ℝ} {p : ℕ} (hp : p ∈ smallPrimes R) :
    p ≤ cutoff R ∧ p.Prime ∧ p % 4 = 1 := by
  simpa [smallPrimes, Nat.lt_succ_iff] using hp

lemma smallPrimes_five_le {R : ℝ} {p : ℕ} (hp : p ∈ smallPrimes R) : 5 ≤ p :=
  GaussianExcess.split_prime_five_le (mem_smallPrimes hp).2.1 (mem_smallPrimes hp).2.2

lemma cutoff_le {R : ℝ} (hR : 0 ≤ R) : (cutoff R : ℝ) ≤ R ^ (1 / 10 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg hR _)

/-- The lower power absorbs the absolute floor error. -/
theorem eventually_cutoff_bounds :
    ∀ᶠ R : ℝ in atTop,
      R ^ (1 / 20 : ℝ) ≤ (cutoff R : ℝ) ∧
        (cutoff R : ℝ) ≤ R ^ (1 / 10 : ℝ) := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually
      (eventually_ge_atTop 2)] with R hR hpow
  have hsquare : R ^ (1 / 10 : ℝ) = (R ^ (1 / 20 : ℝ)) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast hR]
    norm_num
  have hfloor : R ^ (1 / 10 : ℝ) - 1 < (cutoff R : ℝ) :=
    Nat.sub_one_lt_floor _
  exact ⟨by rw [hsquare] at hfloor; nlinarith, cutoff_le hR⟩

theorem tendsto_cutoff : Tendsto cutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_cutoff_bounds,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).eventually
      (eventually_ge_atTop (n : ℝ))] with R hR hn
  exact_mod_cast hn.trans hR.1

lemma tendsto_loglog :
    Tendsto (fun R : ℝ => Real.log (Real.log R)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma tendsto_cutoff_loglog :
    Tendsto (fun R : ℝ => Real.log (Real.log (cutoff R : ℝ))) atTop atTop :=
  MertensTransfer.tendsto_loglog.comp tendsto_cutoff

/-- Positivity and the associated nonvanishing conditions required by divisions. -/
lemma eventually_positive :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ 1 < (cutoff R : ℝ) ∧
      0 < Real.log R ∧ 0 < Real.log (cutoff R : ℝ) ∧
      0 < Real.log (Real.log R) ∧ 0 < Real.log (Real.log (cutoff R : ℝ)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_cutoff.eventually (eventually_ge_atTop 2),
    tendsto_loglog.eventually (eventually_gt_atTop 0),
    tendsto_cutoff_loglog.eventually (eventually_gt_atTop 0)] with R hR hc hl hlc
  have hc' : (1 : ℝ) < cutoff R := by exact_mod_cast (show 1 < cutoff R by omega)
  exact ⟨by linarith, hc', Real.log_pos hR, Real.log_pos hc', hl, hlc⟩

lemma eventually_nonzero :
    ∀ᶠ R : ℝ in atTop, R ≠ 0 ∧ (cutoff R : ℝ) ≠ 0 ∧
      Real.log R ≠ 0 ∧ Real.log (cutoff R : ℝ) ≠ 0 ∧
      Real.log (Real.log R) ≠ 0 ∧ Real.log (Real.log (cutoff R : ℝ)) ≠ 0 := by
  filter_upwards [eventually_positive] with R h
  exact ⟨h.1.ne', (lt_trans zero_lt_one h.2.1).ne', h.2.2.1.ne',
    h.2.2.2.1.ne', h.2.2.2.2.1.ne', h.2.2.2.2.2.ne'⟩

lemma loglog_rpow {R a : ℝ} (hR : 1 < R) (ha : 0 < a) :
    Real.log (Real.log (R ^ a)) = Real.log (Real.log R) + Real.log a := by
  rw [Real.log_rpow (by linarith), Real.log_mul ha.ne' (Real.log_pos hR).ne']
  ring

/-- Two explicit translates of log-log squeeze the floor cutoff. -/
lemma eventually_loglog_bounds :
    ∀ᶠ R : ℝ in atTop,
      Real.log (Real.log R) + Real.log (1 / 20 : ℝ) ≤
        Real.log (Real.log (cutoff R : ℝ)) ∧
      Real.log (Real.log (cutoff R : ℝ)) ≤
        Real.log (Real.log R) + Real.log (1 / 10 : ℝ) := by
  filter_upwards [eventually_cutoff_bounds, eventually_positive,
    eventually_gt_atTop (1 : ℝ)] with R hb hp hR
  constructor
  · rw [← loglog_rpow hR (by norm_num : (0 : ℝ) < 1 / 20)]
    apply Real.log_le_log
    · exact Real.log_pos (Real.one_lt_rpow hR (by norm_num))
    · exact Real.log_le_log (Real.rpow_pos_of_pos hp.1 _) hb.1
  · rw [← loglog_rpow hR (by norm_num : (0 : ℝ) < 1 / 10)]
    apply Real.log_le_log hp.2.2.2.1
    exact Real.log_le_log (lt_trans zero_lt_one hp.2.1) hb.2

lemma tendsto_const_div_loglog (C : ℝ) :
    Tendsto (fun R : ℝ => C / Real.log (Real.log R)) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_loglog) :
      Tendsto (fun R : ℝ => C * (Real.log (Real.log R))⁻¹) atTop (𝓝 (C * 0)))

theorem tendsto_loglog_cutoff_div_loglog :
    Tendsto (fun R : ℝ => Real.log (Real.log (cutoff R : ℝ)) /
      Real.log (Real.log R)) atTop (𝓝 1) := by
  have hlo : Tendsto (fun R : ℝ =>
      1 + Real.log (1 / 20 : ℝ) / Real.log (Real.log R)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_loglog (Real.log (1 / 20 : ℝ)))
  have hhi : Tendsto (fun R : ℝ =>
      1 + Real.log (1 / 10 : ℝ) / Real.log (Real.log R)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_loglog (Real.log (1 / 10 : ℝ)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_loglog_bounds, eventually_positive] with R hb hp
    apply (le_div_iff₀ hp.2.2.2.2.1).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hp.2.2.2.2.1.ne']
    exact hb.1
  · filter_upwards [eventually_loglog_bounds, eventually_positive] with R hb hp
    apply (div_le_iff₀ hp.2.2.2.2.1).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hp.2.2.2.2.1.ne']
    exact hb.2

lemma center_eq (R : ℝ) :
    GaussianMoments.center (smallPrimes R) =
      2 * PrimeProgressions.splitPrimeReciprocal (cutoff R) -
        ∑ p ∈ smallPrimes R, 1 / (p : ℝ) ^ 2 := by
  simp only [GaussianMoments.center, GaussianDivisibility.splitDensity,
    sum_sub_distrib, PrimeProgressions.splitPrimeReciprocal, ← mul_sum]
  congr 1
  unfold smallPrimes
  rw [mul_sum]
  exact sum_congr rfl fun p _ => by ring

lemma reciprocal_square_sum_bounds (R : ℝ) :
    0 ≤ (∑ p ∈ smallPrimes R, 1 / (p : ℝ) ^ 2) ∧
      (∑ p ∈ smallPrimes R, 1 / (p : ℝ) ^ 2) ≤ 2 :=
  ⟨sum_nonneg (fun p _ => by positivity),
    GaussianExcess.reciprocal_square_sum_le _ (fun _ hp => smallPrimes_five_le hp)⟩

lemma tendsto_reciprocal_square_sum_div_loglog :
    Tendsto (fun R : ℝ => (∑ p ∈ smallPrimes R, 1 / (p : ℝ) ^ 2) /
      Real.log (Real.log R)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_const_div_loglog 2)
  · filter_upwards [eventually_positive] with R hR
    exact div_nonneg (reciprocal_square_sum_bounds R).1 hR.2.2.2.2.1.le
  · filter_upwards [eventually_positive] with R hR
    exact div_le_div_of_nonneg_right (reciprocal_square_sum_bounds R).2 hR.2.2.2.2.1.le

/-- Composition uses the actual inclusive AP Mertens sum. -/
theorem tendsto_splitPrimeReciprocal_div_loglog :
    Tendsto (fun R : ℝ => PrimeProgressions.splitPrimeReciprocal (cutoff R) /
      Real.log (Real.log R)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := (MertensTransfer.tendsto_splitPrimeReciprocal.comp tendsto_cutoff).mul
    tendsto_loglog_cutoff_div_loglog
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_nonzero] with R hR
  dsimp only [Function.comp_apply]
  field_simp [hR.2.2.2.2.2, hR.2.2.2.2.1]

theorem tendsto_center_div_loglog :
    Tendsto (fun R : ℝ => GaussianMoments.center (smallPrimes R) /
      Real.log (Real.log R)) atTop (𝓝 1) := by
  have h := (tendsto_splitPrimeReciprocal_div_loglog.const_mul 2).sub
    tendsto_reciprocal_square_sum_div_loglog
  norm_num only at h
  convert h using 1
  ext R
  rw [center_eq, sub_div, mul_div_assoc]

lemma card_smallPrimes_le (R : ℝ) : (smallPrimes R).card ≤ cutoff R + 1 := by
  exact (card_filter_le _ _).trans_eq (card_range _)

lemma eventually_card_smallPrimes_le :
    ∀ᶠ R : ℝ in atTop,
      ((smallPrimes R).card : ℝ) ≤ (cutoff R : ℝ) + 1 ∧
      (cutoff R : ℝ) + 1 ≤ R ^ (1 / 10 : ℝ) + 1 := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  exact ⟨by exact_mod_cast card_smallPrimes_le R, by linarith [cutoff_le hR]⟩

/-- A power majorant for the actual finite-set boundary term. -/
lemma eventually_boundary_le :
    ∀ᶠ R : ℝ in atTop,
      0 ≤ ((R + 1) * ((smallPrimes R).card : ℝ) ^ 2) / R ^ 2 ∧
      ((R + 1) * ((smallPrimes R).card : ℝ) ^ 2) / R ^ 2 ≤
        8 * R ^ (-(4 / 5 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_card_smallPrimes_le]
    with R hR hc
  have hR0 : 0 < R := by linarith
  have hx : 1 ≤ R ^ (1 / 10 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hc' : ((smallPrimes R).card : ℝ) ≤ 2 * R ^ (1 / 10 : ℝ) := by
    linarith [hc.1.trans hc.2]
  have hsquare : (R ^ (1 / 10 : ℝ)) ^ (2 : ℕ) = R ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast hR0.le]
    norm_num
  have hcsquare : ((smallPrimes R).card : ℝ) ^ 2 ≤ 4 * R ^ (1 / 5 : ℝ) := by
    have hn : 0 ≤ ((smallPrimes R).card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_self_le_mul_self hn hc']
  have hnum : (R + 1) * ((smallPrimes R).card : ℝ) ^ 2 ≤
      8 * R * R ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ (2 * R) * (4 * R ^ (1 / 5 : ℝ)) :=
        mul_le_mul (by linarith) hcsquare (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have heq : (8 * R * R ^ (1 / 5 : ℝ)) / R ^ 2 =
      8 * R ^ (-(4 / 5 : ℝ)) := by
    have hrpow : R ^ (-(4 / 5 : ℝ)) = R ^ (1 / 5 : ℝ) / R := by
      convert Real.rpow_sub hR0 (1 / 5) 1 using 1 <;> norm_num
    rw [hrpow]
    field_simp [hR0.ne']
    <;> ring
  exact ⟨by positivity,
    (div_le_div_of_nonneg_right hnum (sq_nonneg R)).trans_eq heq⟩

theorem tendsto_boundary_error :
    Tendsto (fun R : ℝ => ((R + 1) * ((smallPrimes R).card : ℝ) ^ 2) / R ^ 2)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun R : ℝ => 8 * R ^ (-(4 / 5 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).const_mul 8
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
    (eventually_boundary_le.mono fun _ h => h.1)
    (eventually_boundary_le.mono fun _ h => h.2)

end DistanceCounts.GaussianCutoff
end
end

-- Source: DistanceCounts/RepresentationFormula.lean
section
/-! Exact overlaps and prime-step recurrences for the genuine finite norm circles. -/

noncomputable section

namespace DistanceCounts

/-- The common elements of the two split-prime images have a unique common
rational-prime factor. The norm equation records divisibility without division,
so this statement also treats the zero circle correctly. -/
lemma mem_normCircle_split_inter (p n : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    {z : GaussianInt} (hz : z.norm.natAbs = p) (w : GaussianInt) :
    w ∈ (normCircle n).image (fun v => z * v) ∩
      (normCircle n).image (fun v => star z * v) ↔
      ∃ c : GaussianInt, p * c.norm.natAbs = n ∧ (p : GaussianInt) * c = w := by
  classical
  have hzp := gaussian_prime_of_prime_norm hp hz
  have hzc : (star z).norm.natAbs = p := by simpa using hz
  have hcp := gaussian_prime_of_prime_norm hp hzc
  have hnot : ¬star z ∣ z := by
    intro hd
    exact not_associated_conj_of_split_prime_norm hp hp4 hz
      (hcp.associated_of_dvd hzp hd).symm
  have hzn : z.norm = (p : ℤ) :=
    (mem_normCircle_iff_norm _ _).mp ((mem_normCircle _ _).mpr hz)
  have hpcast : (p : GaussianInt) = z * star z := by
    rw [← Zsqrtd.norm_eq_mul_conj, hzn]
    simp
  constructor
  · intro hw
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hw
    obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp ha
    obtain ⟨b, _, hbw⟩ := Finset.mem_image.mp hb
    have hd : star z ∣ z * a := ⟨b, haw.trans hbw.symm⟩
    have hda : star z ∣ a := (hcp.dvd_or_dvd hd).resolve_left hnot
    obtain ⟨c, rfl⟩ := hda
    refine ⟨c, ?_, ?_⟩
    · simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hzc, hz] using
        (mem_normCircle _ _).mp ha
    · simpa only [hpcast, mul_assoc] using haw
  · rintro ⟨c, hc, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · refine Finset.mem_image.mpr ⟨star z * c, ?_, ?_⟩
      · apply (mem_normCircle _ _).mpr
        simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hzc, hz] using hc
      · rw [hpcast, mul_assoc]
    · refine Finset.mem_image.mpr ⟨z * c, ?_, ?_⟩
      · apply (mem_normCircle _ _).mpr
        simpa [Zsqrtd.norm_mul, Int.natAbs_mul, hz] using hc
      · rw [hpcast]
        ring

/-- When the residual norm is divisible by the split prime, the overlap is
exactly the rational-prime multiple of the quotient circle. -/
theorem normCircle_split_inter_of_dvd (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) {z : GaussianInt} (hz : z.norm.natAbs = p) (hd : p ∣ n) :
    (normCircle n).image (fun v => z * v) ∩
      (normCircle n).image (fun v => star z * v) =
      (normCircle (n / p)).image (fun c => (p : GaussianInt) * c) := by
  classical
  ext w
  rw [mem_normCircle_split_inter p n hp hp4 hz]
  constructor
  · rintro ⟨c, hc, hcw⟩
    refine Finset.mem_image.mpr ⟨c, (mem_normCircle _ _).mpr ?_, hcw⟩
    apply mul_left_cancel₀ hp.ne_zero
    exact hc.trans (Nat.mul_div_cancel' hd).symm
  · intro hw
    obtain ⟨c, hc, hcw⟩ := Finset.mem_image.mp hw
    refine ⟨c, ?_, hcw⟩
    rw [(mem_normCircle _ _).mp hc, Nat.mul_div_cancel' hd]

/-- If the split prime does not divide the residual norm, the images are
disjoint. This excludes overlap by actual Gaussian prime cancellation. -/
theorem normCircle_split_inter_of_not_dvd (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) {z : GaussianInt} (hz : z.norm.natAbs = p) (hd : ¬p ∣ n) :
    (normCircle n).image (fun v => z * v) ∩
      (normCircle n).image (fun v => star z * v) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨c, hc, _⟩ := (mem_normCircle_split_inter p n hp hp4 hz w).mp hw
  exact hd ⟨c.norm.natAbs, hc.symm⟩

/-- Inclusion-exclusion gives the exact additive recurrence, including at zero.
There is no subtraction of natural cardinalities and no multiplicativity input. -/
theorem normCircle_split_mul_card (p n : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    (normCircle (p * n)).card + (if p ∣ n then (normCircle (n / p)).card else 0) =
      2 * (normCircle n).card := by
  classical
  obtain ⟨a, b, hab⟩ := @Nat.Prime.sq_add_sq p ⟨hp⟩ (by omega)
  obtain ⟨z, hzmem⟩ := (normCircle_nonempty_iff_sum_two_squares p).mpr
    ⟨a, b, hab.symm⟩
  have hz := (mem_normCircle _ _).mp hzmem
  have hz0 := ne_zero_of_mem_normCircle hp.ne_zero hzmem
  have hzc0 : star z ≠ 0 := by simpa using hz0
  have hp0 : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcard := Finset.card_union_add_card_inter
    ((normCircle n).image (fun v => z * v))
    ((normCircle n).image (fun v => star z * v))
  rw [← normCircle_prime_mul p n hp hz,
    Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ hz0 h),
    Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ hzc0 h)] at hcard
  by_cases hd : p ∣ n
  · rw [normCircle_split_inter_of_dvd p n hp hp4 hz hd,
      Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ hp0 h)] at hcard
    simpa only [if_pos hd, two_mul] using hcard
  · rw [normCircle_split_inter_of_not_dvd p n hp hp4 hz hd,
      Finset.card_empty] at hcard
    simpa only [if_neg hd, two_mul] using hcard

/-- The unramified first step doubles the number of representations. -/
theorem normCircle_split_mul_card_of_not_dvd (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hd : ¬p ∣ n) :
    (normCircle (p * n)).card = 2 * (normCircle n).card := by
  simpa only [if_neg hd, add_zero] using normCircle_split_mul_card p n hp hp4

/-- The second-order recurrence solves to a linear factor along every split
prime-power direction, with an arbitrary coprime residual norm. -/
theorem normCircle_split_pow_mul_card (p k n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hd : ¬p ∣ n) :
    (normCircle (p ^ k * n)).card = (k + 1) * (normCircle n).card := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simpa only [pow_one] using normCircle_split_mul_card_of_not_dvd p n hp hp4 hd
  | more k ih₀ ih₁ =>
    have hd' : p ∣ p ^ (k + 1) * n := by
      rw [pow_succ', mul_assoc]
      exact dvd_mul_right _ _
    have hdiv : p ^ (k + 1) * n / p = p ^ k * n := by
      rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have hstep := normCircle_split_mul_card p (p ^ (k + 1) * n) hp hp4
    rw [if_pos hd', hdiv, ih₀, ih₁] at hstep
    have hpow : p * (p ^ (k + 1) * n) = p ^ (k + 2) * n := by
      simpa only [mul_assoc] using
        congrArg (fun a : ℕ => a * n) (pow_succ' p (k + 1)).symm
    rw [hpow] at hstep
    nlinarith


/-- Multiplication by `1+i` parametrizes the entire doubled norm circle. The
conjugate image is the same image, because `1-i = (1+i)(-i)`. -/
theorem normCircle_two_mul (n : ℕ) :
    normCircle (2 * n) =
      (normCircle n).image (fun v => (⟨1, 1⟩ : GaussianInt) * v) := by
  classical
  let z : GaussianInt := ⟨1, 1⟩
  let u : GaussianInt := ⟨0, -1⟩
  have hz : z.norm.natAbs = 2 := by norm_num [z, Zsqrtd.norm]
  have hu : u.norm.natAbs = 1 := by norm_num [u, Zsqrtd.norm]
  have hconj : star z = z * u := by
    ext <;> norm_num [z, u]
  change normCircle (2 * n) = (normCircle n).image (fun v => z * v)
  rw [normCircle_prime_mul 2 n Nat.prime_two hz]
  apply Finset.union_eq_left.mpr
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  refine Finset.mem_image.mpr ⟨u * v, ?_, ?_⟩
  · apply (mem_normCircle _ _).mpr
    simp [Zsqrtd.norm_mul, Int.natAbs_mul, hu, (mem_normCircle _ _).mp hv]
  · rw [hconj, mul_assoc]

/-- The ramified prime does not change the representation count. -/
theorem normCircle_two_mul_card (n : ℕ) :
    (normCircle (2 * n)).card = (normCircle n).card := by
  classical
  rw [normCircle_two_mul]
  apply Finset.card_image_of_injective
  have hz0 : (⟨1, 1⟩ : GaussianInt) ≠ 0 := by
    intro h
    have := congrArg Zsqrtd.re h
    norm_num at this
  exact fun _ _ h => mul_left_cancel₀ hz0 h

/-- Removing any power of the ramified prime is exact, not merely an estimate. -/
theorem normCircle_two_pow_mul_card (k n : ℕ) :
    (normCircle (2 ^ k * n)).card = (normCircle n).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, normCircle_two_mul_card, ih]


/-- Repeated inert-square removal handles every even inert exponent. -/
theorem normCircle_inert_even_pow_mul_card (p k n : ℕ) (hp : p.Prime)
    (hp3 : p % 4 = 3) :
    (normCircle (p ^ (2 * k) * n)).card = (normCircle n).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : p ^ (2 * (k + 1)) * n = p * p * (p ^ (2 * k) * n) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add, pow_two]
      ring
    rw [he, normCircle_inert_square_card p _ hp hp3, ih]


/-- Independent prime-power removals give the representation count of a genuine
finite product. No multiplicativity of representation counts is assumed. -/
theorem normCircle_prod_primePowers_card (S : Finset ℕ) (k : ℕ → ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (heven : ∀ p ∈ S, p % 4 = 3 → Even (k p)) :
    (normCircle (∏ p ∈ S, p ^ k p)).card =
      4 * ∏ p ∈ S, if p % 4 = 1 then k p + 1 else 1 := by
  classical
  revert hprime heven
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    simp [normCircle_one_card]
  | @insert p S hpS ih =>
    intro hprime heven
    have hpp := hprime p (Finset.mem_insert_self p S)
    have hprimeS : ∀ q ∈ S, q.Prime :=
      fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have hevenS : ∀ q ∈ S, q % 4 = 3 → Even (k q) :=
      fun q hq => heven q (Finset.mem_insert_of_mem hq)
    have ih' := ih hprimeS hevenS
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS]
    rcases hpp.eq_two_or_odd with htwo | hodd
    · subst p
      rw [normCircle_two_pow_mul_card, ih']
      norm_num
    · have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hp4 with hp1 | hp3
      · have hcop : Nat.Coprime p (∏ q ∈ S, q ^ k q) := by
          apply Nat.Coprime.prod_right
          intro q hq
          apply Nat.Coprime.pow_right
          apply (Nat.coprime_primes hpp (hprimeS q hq)).mpr
          rintro rfl
          exact hpS hq
        have hd := hpp.coprime_iff_not_dvd.mp hcop
        rw [normCircle_split_pow_mul_card p (k p) _ hpp hp1 hd, ih']
        simp only [if_pos hp1]
        ring
      · obtain ⟨r, hr⟩ := heven p (Finset.mem_insert_self p S) hp3
        have hk : k p = 2 * r := by omega
        rw [hk, normCircle_inert_even_pow_mul_card p r _ hpp hp3, ih']
        norm_num [hp3]

/-- The classical product formula for the actual Gaussian norm circle. The
positive-norm and representability hypotheses account for every inert factor. -/
theorem normCircle_card_factorization (n : ℕ) (hn : n ≠ 0)
    (hrep : (normCircle n).Nonempty) :
    (normCircle n).card =
      4 * ∏ p ∈ n.primeFactors.filter (fun p => p % 4 = 1), (n.factorization p + 1) := by
  classical
  have heven : ∀ p ∈ n.primeFactors, p % 4 = 3 → Even (n.factorization p) := by
    intro p hp hp3
    rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]
    exact (normCircle_nonempty_iff n).mp hrep p hp hp3
  calc
    (normCircle n).card =
        (normCircle (∏ p ∈ n.primeFactors, p ^ n.factorization p)).card :=
      congrArg (fun m => (normCircle m).card) (Nat.prod_primeFactors_pow_factorization hn)
    _ = 4 * ∏ p ∈ n.primeFactors,
        if p % 4 = 1 then n.factorization p + 1 else 1 :=
      normCircle_prod_primePowers_card n.primeFactors n.factorization
        (fun p hp => Nat.prime_of_mem_primeFactors hp) heven
    _ = _ := by simp only [Finset.prod_filter]

end DistanceCounts
end
end

-- Source: DistanceCounts/RepresentationLog.lean
section
noncomputable section

namespace DistanceCounts.RepresentationLog

/-- The exact representation product gives a logarithmic sandwich. The error
is precisely the excess of split-prime exponents over their first occurrence. -/
theorem normCircle_log_bounds (n : ℕ) (hn : n ≠ 0)
    (hrep : (normCircle n).Nonempty) :
    let S := n.primeFactors.filter (fun p => p % 4 = 1)
    Real.log 4 + Real.log 2 * (S.card : ℝ) ≤ Real.log ((normCircle n).card : ℝ) ∧
      Real.log ((normCircle n).card : ℝ) ≤
        Real.log 4 + Real.log 2 *
          ((S.card : ℝ) + ((∑ p ∈ S, (n.factorization p - 1) : ℕ) : ℝ)) := by
  classical
  dsimp only
  let S := n.primeFactors.filter (fun p => p % 4 = 1)
  change Real.log 4 + Real.log 2 * (S.card : ℝ) ≤
      Real.log ((normCircle n).card : ℝ) ∧
    Real.log ((normCircle n).card : ℝ) ≤
      Real.log 4 + Real.log 2 *
        ((S.card : ℝ) + ((∑ p ∈ S, (n.factorization p - 1) : ℕ) : ℝ))
  have hpos : ∀ p ∈ S, 0 < n.factorization p := by
    intro p hp
    have hp' : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
    exact (Nat.prime_of_mem_primeFactors hp').factorization_pos_of_dvd hn
      (Nat.dvd_of_mem_primeFactors hp')
  have hsum : (∑ p ∈ S, n.factorization p) =
      S.card + ∑ p ∈ S, (n.factorization p - 1) := by
    calc
      (∑ p ∈ S, n.factorization p) =
          ∑ p ∈ S, (1 + (n.factorization p - 1)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have := hpos p hp
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hlop : 2 ^ S.card ≤ ∏ p ∈ S, (n.factorization p + 1) := by
    calc
      2 ^ S.card = ∏ _p ∈ S, (2 : ℕ) := (Finset.prod_const 2).symm
      _ ≤ _ := Finset.prod_le_prod' fun p hp => by
        have := hpos p hp
        omega
  have hhip : (∏ p ∈ S, (n.factorization p + 1)) ≤
      2 ^ (S.card + ∑ p ∈ S, (n.factorization p - 1)) := by
    calc
      (∏ p ∈ S, (n.factorization p + 1)) ≤
          ∏ p ∈ S, 2 ^ n.factorization p :=
        Finset.prod_le_prod' fun p _ =>
          (show n.factorization p < 2 ^ n.factorization p from Nat.lt_two_pow_self).succ_le
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum, hsum]
  have hformula : (normCircle n).card =
      4 * ∏ p ∈ S, (n.factorization p + 1) :=
    normCircle_card_factorization n hn hrep
  have hloNat : 4 * 2 ^ S.card ≤ (normCircle n).card := by
    rw [hformula]
    exact Nat.mul_le_mul_left 4 hlop
  have hhiNat : (normCircle n).card ≤
      4 * 2 ^ (S.card + ∑ p ∈ S, (n.factorization p - 1)) := by
    rw [hformula]
    exact Nat.mul_le_mul_left 4 hhip
  have hlo : Real.log ((4 : ℝ) * 2 ^ S.card) ≤
      Real.log ((normCircle n).card : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hloNat)
  have hhi : Real.log ((normCircle n).card : ℝ) ≤
      Real.log ((4 : ℝ) * 2 ^ (S.card + ∑ p ∈ S, (n.factorization p - 1))) :=
    Real.log_le_log (by exact_mod_cast Finset.card_pos.mpr hrep)
      (by exact_mod_cast hhiNat)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlo hhi
  constructor
  · simpa only [mul_comm] using hlo
  · simpa only [Nat.cast_add, mul_comm] using hhi

/-- Every nonzero Gaussian integer supplies both hypotheses of the pointwise
representation estimate at its actual natural-valued norm. -/
theorem normCircle_log_bounds_natNorm (z : GaussianInt) (hz : z ≠ 0) :
    let n := z.norm.natAbs
    let S := n.primeFactors.filter (fun p => p % 4 = 1)
    Real.log 4 + Real.log 2 * (S.card : ℝ) ≤ Real.log ((normCircle n).card : ℝ) ∧
      Real.log ((normCircle n).card : ℝ) ≤
        Real.log 4 + Real.log 2 *
          ((S.card : ℝ) + ((∑ p ∈ S, (n.factorization p - 1) : ℕ) : ℝ)) := by
  have hn : z.norm.natAbs ≠ 0 := by
    simpa only [Ne, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero] using hz
  exact normCircle_log_bounds z.norm.natAbs hn
    ⟨z, (mem_normCircle _ _).mpr rfl⟩

/-- Distinct prime divisors above the explicit cutoff occupy at most forty
places when the integer has size at most the square of the radius. -/
theorem large_primeFactors_card_le (R : ℝ) (hR : 1 < R) (n M : ℕ)
    (hn : n ≠ 0) (hnR : (n : ℝ) ≤ R ^ (2 : ℕ))
    (hM : R ^ (1 / 20 : ℝ) ≤ (M : ℝ)) :
    (n.primeFactors.filter (fun p => M < p)).card ≤ 40 := by
  classical
  let T := n.primeFactors.filter (fun p => M < p)
  have hT : T ⊆ n.primeFactors := Finset.filter_subset _ _
  have hprod_dvd : (∏ p ∈ T, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset T n.primeFactors id hT).trans
      (Nat.prod_primeFactors_dvd n)
  have hprod_le : (∏ p ∈ T, p) ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod_dvd
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hrootpos : 0 < R ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hRpos _
  have hroot_le : ∀ p ∈ T, R ^ (1 / 20 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    have hMp : M < p := (Finset.mem_filter.mp hp).2
    exact hM.trans (by exact_mod_cast hMp.le)
  have hpow_le : (R ^ (1 / 20 : ℝ)) ^ T.card ≤ R ^ (2 : ℕ) := by
    calc
      (R ^ (1 / 20 : ℝ)) ^ T.card = ∏ _p ∈ T, R ^ (1 / 20 : ℝ) :=
        (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ T, (p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => hrootpos.le) hroot_le
      _ ≤ (n : ℝ) := by
        have hcast : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ n := by exact_mod_cast hprod_le
        simpa only [Nat.cast_prod] using hcast
      _ ≤ R ^ (2 : ℕ) := hnR
  have hlog := Real.log_le_log (pow_pos hrootpos T.card) hpow_le
  rw [Real.log_pow, Real.log_pow, Real.log_rpow hRpos] at hlog
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hcard : (T.card : ℝ) ≤ 40 := by
    nlinarith
  exact_mod_cast hcard

/-- Restricting the omitted prime divisors to the split primes preserves the
same deterministic bound; no distribution hypothesis is needed. -/
theorem large_splitPrimeFactors_card_le (R : ℝ) (hR : 1 < R) (n M : ℕ)
    (hn : n ≠ 0) (hnR : (n : ℝ) ≤ R ^ (2 : ℕ))
    (hM : R ^ (1 / 20 : ℝ) ≤ (M : ℝ)) :
    ((n.primeFactors.filter (fun p => p % 4 = 1)).filter (fun p => M < p)).card ≤ 40 := by
  classical
  apply le_trans (Finset.card_le_card ?_) (large_primeFactors_card_le R hR n M hn hnR hM)
  intro p hp
  obtain ⟨hpS, hpM⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpS).1, hpM⟩

end DistanceCounts.RepresentationLog
end
end

-- Source: DistanceCounts/GaussianNormalOrder.lean
section
/-! Finite comparisons for point-weighted Gaussian representation normal order. -/

noncomputable section

namespace DistanceCounts.GaussianNormalOrder

open Finset Filter GaussianMoments GaussianCutoff
open scoped Classical Topology

/-- All split primes that can divide the norm of a vector in the radius-R population. -/
def allPrimes (R : ℝ) : Finset ℕ :=
  (range (⌊R ^ 2⌋₊ + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)

/-- The actual split prime divisors of a vector's norm. -/
def normPrimes (z : GaussianInt) : Finset ℕ :=
  z.norm.natAbs.primeFactors.filter (fun p => p % 4 = 1)

lemma allPrimes_spec (R : ℝ) : ∀ p ∈ allPrimes R, p.Prime ∧ p % 4 = 1 := by
  intro p hp
  exact (mem_filter.mp hp).2

lemma natNorm_ne_zero {z : GaussianInt} (hz : z ≠ 0) : z.norm.natAbs ≠ 0 := by
  simpa only [Ne, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero] using hz

lemma normPrimes_subset_all {R : ℝ} {z : GaussianInt}
    (hz : z ∈ GaussianMass.representatives (R ^ 2)) : normPrimes z ⊆ allPrimes R := by
  obtain ⟨hz0, hnR⟩ := (GaussianMass.mem_representatives (sq_nonneg R) z).mp hz
  have hn0 := natNorm_ne_zero hz0
  have hn : z.norm.natAbs ≤ ⌊R ^ 2⌋₊ := (Nat.le_floor_iff (sq_nonneg R)).mpr hnR
  intro p hp
  obtain ⟨hpS, hp4⟩ := mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hpS
  have hpdiv := Nat.dvd_of_mem_primeFactors hpS
  have hpn := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdiv
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), hprime, hp4⟩

lemma omega_eq_small_normPrimes (R : ℝ) {z : GaussianInt} (hz : z ≠ 0) :
    splitOmega (smallPrimes R) z =
      ((normPrimes z).filter (fun p => p ≤ cutoff R)).card := by
  have hn0 := natNorm_ne_zero hz
  unfold splitOmega
  congr 1
  ext p
  simp only [smallPrimes, normPrimes, mem_filter, mem_range, Nat.lt_succ_iff,
    Nat.mem_primeFactors]
  tauto

lemma normPrimes_card_bounds {R : ℝ} (hR : 1 < R)
    (hM : R ^ (1 / 20 : ℝ) ≤ (cutoff R : ℝ)) {z : GaussianInt}
    (hz : z ∈ GaussianMass.representatives (R ^ 2)) :
    splitOmega (smallPrimes R) z ≤ (normPrimes z).card ∧
      (normPrimes z).card ≤ splitOmega (smallPrimes R) z + 40 := by
  obtain ⟨hz0, hnR⟩ := (GaussianMass.mem_representatives (sq_nonneg R) z).mp hz
  have hω := omega_eq_small_normPrimes R hz0
  have hpart : ((normPrimes z).filter (fun p => p ≤ cutoff R)).card +
      ((normPrimes z).filter (fun p => cutoff R < p)).card = (normPrimes z).card := by
    simpa only [not_le] using
      (card_filter_add_card_filter_not (s := normPrimes z) (fun p => p ≤ cutoff R))
  have hlarge : ((normPrimes z).filter (fun p => cutoff R < p)).card ≤ 40 := by
    simpa only [normPrimes, Finset.filter_filter] using
      RepresentationLog.large_splitPrimeFactors_card_le R hR z.norm.natAbs (cutoff R)
        (natNorm_ne_zero hz0) hnR hM
  omega

/-- The truncation loses at most forty distinct primes; all multiplicity loss
is dominated by the actual full excess statistic on the same population. -/
theorem logarithm_pointwise_error {R : ℝ} (hR : 1 < R)
    (hM : R ^ (1 / 20 : ℝ) ≤ (cutoff R : ℝ)) {z : GaussianInt}
    (hz : z ∈ GaussianMass.representatives (R ^ 2)) :
    |Real.log ((normCircle z.norm.natAbs).card : ℝ) -
      Real.log 2 * (splitOmega (smallPrimes R) z : ℝ)| ≤
        Real.log 4 + 40 * Real.log 2 +
          Real.log 2 * (GaussianExcess.excess (allPrimes R) z : ℝ) := by
  have hz0 := ((GaussianMass.mem_representatives (sq_nonneg R) z).mp hz).1
  have hcounts := normPrimes_card_bounds hR hM hz
  have hlog := RepresentationLog.normCircle_log_bounds_natNorm z hz0
  change Real.log 4 + Real.log 2 * ((normPrimes z).card : ℝ) ≤
      Real.log ((normCircle z.norm.natAbs).card : ℝ) ∧
    Real.log ((normCircle z.norm.natAbs).card : ℝ) ≤
      Real.log 4 + Real.log 2 *
        (((normPrimes z).card : ℝ) +
          ((∑ p ∈ normPrimes z, (z.norm.natAbs.factorization p - 1) : ℕ) : ℝ)) at hlog
  have hexcess : (∑ p ∈ normPrimes z, (z.norm.natAbs.factorization p - 1)) ≤
      GaussianExcess.excess (allPrimes R) z := by
    exact sum_le_sum_of_subset_of_nonneg (normPrimes_subset_all hz)
      (fun _ _ _ => Nat.zero_le _)
  have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlo : Real.log 2 * (splitOmega (smallPrimes R) z : ℝ) ≤
      Real.log ((normCircle z.norm.natAbs).card : ℝ) := by
    have hc : (splitOmega (smallPrimes R) z : ℝ) ≤ (normPrimes z).card := by
      exact_mod_cast hcounts.1
    have hh := mul_le_mul_of_nonneg_left hc hlogTwo
    linarith [hlog.1]
  have hsum : ((normPrimes z).card : ℝ) +
      ((∑ p ∈ normPrimes z, (z.norm.natAbs.factorization p - 1) : ℕ) : ℝ) ≤
        (splitOmega (smallPrimes R) z : ℝ) + 40 +
          (GaussianExcess.excess (allPrimes R) z : ℝ) := by
    exact_mod_cast Nat.add_le_add hcounts.2 hexcess
  have hupper : Real.log ((normCircle z.norm.natAbs).card : ℝ) ≤
      Real.log 4 + Real.log 2 * ((splitOmega (smallPrimes R) z : ℝ) + 40 +
        (GaussianExcess.excess (allPrimes R) z : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hsum hlogTwo
    linarith [hlog.2]
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  nlinarith

/-- Deterministic Markov bound for the actual repeated-factor statistic. -/
theorem excess_exceptional_card_upper (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ p % 4 = 1) {R a : ℝ}
    (hR : 0 ≤ R) (ha : 0 < a) :
    (((GaussianMass.representatives (R ^ 2)).filter
      (fun z => a ≤ (GaussianExcess.excess T z : ℝ))).card : ℝ) ≤
        (108 * Real.pi) * R ^ 2 / a := by
  let B := (GaussianMass.representatives (R ^ 2)).filter
    (fun z => a ≤ (GaussianExcess.excess T z : ℝ))
  apply (le_div_iff₀ ha).mpr
  change (B.card : ℝ) * a ≤ _
  calc
    (B.card : ℝ) * a = ∑ _z ∈ B, a := by simp
    _ ≤ ∑ z ∈ B, (GaussianExcess.excess T z : ℝ) :=
      sum_le_sum (fun z hz => (mem_filter.mp hz).2)
    _ ≤ ∑ z ∈ GaussianMass.representatives (R ^ 2),
        (GaussianExcess.excess T z : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := GaussianExcess.excess_sum_le T hT hR

/-- Strict failure of the logarithmic normal-order window. -/
def logarithmBad (R ε : ℝ) : Finset GaussianInt :=
  (GaussianMass.representatives (R ^ 2)).filter (fun z =>
    ε * Real.log (Real.log R) <
      |Real.log ((normCircle z.norm.natAbs).card : ℝ) -
        Real.log 2 * Real.log (Real.log R)|)

/-- The two genuine exceptional populations used in the final comparison. -/
def exceptional (R k : ℝ) : Finset GaussianInt :=
  ((GaussianMass.representatives (R ^ 2)).filter (fun z =>
    k * Real.log (Real.log R) ≤ |(splitOmega (smallPrimes R) z : ℝ) -
      center (smallPrimes R)|)) ∪
  ((GaussianMass.representatives (R ^ 2)).filter (fun z =>
    k * Real.log (Real.log R) ≤ (GaussianExcess.excess (allPrimes R) z : ℝ)))

/-- This explicit upper bound tends to zero using the already proved
density-center and lattice-boundary limits. -/
def errorBound (R k : ℝ) : ℝ :=
  (Real.pi / k ^ 2) *
      (center (smallPrimes R) / Real.log (Real.log R)) *
      (Real.log (Real.log R))⁻¹ +
    ((64 * Real.pi + 4) / k ^ 2) *
      (((R + 1) * ((smallPrimes R).card : ℝ) ^ 2) / R ^ 2) *
      ((Real.log (Real.log R))⁻¹) ^ 2 +
    ((108 * Real.pi) / k) * (Real.log (Real.log R))⁻¹

lemma tendsto_errorBound (k : ℝ) :
    Tendsto (fun R : ℝ => errorBound R k) atTop (𝓝 0) := by
  have hinv : Tendsto (fun R : ℝ => (Real.log (Real.log R))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp GaussianCutoff.tendsto_loglog
  have h1 := (GaussianCutoff.tendsto_center_div_loglog.mul hinv).const_mul
    (Real.pi / k ^ 2)
  have h2 := (GaussianCutoff.tendsto_boundary_error.mul (hinv.pow 2)).const_mul
    ((64 * Real.pi + 4) / k ^ 2)
  have h3 := hinv.const_mul ((108 * Real.pi) / k)
  simpa only [errorBound, mul_assoc, mul_zero, one_mul, zero_pow (by decide : 2 ≠ 0),
    zero_add] using (h1.add h2).add h3

lemma exceptional_card_bound {R k : ℝ} (hR : 0 < R) (hk : 0 < k)
    (hlog : 0 < Real.log (Real.log R)) :
    ((exceptional R k).card : ℝ) / R ^ 2 ≤ errorBound R k := by
  have ha : 0 < k * Real.log (Real.log R) := mul_pos hk hlog
  have hT : ∀ p ∈ smallPrimes R, p.Prime ∧ p % 4 = 1 :=
    fun p hp => (mem_smallPrimes hp).2
  have hw := exceptional_card_upper (smallPrimes R) hT hR.le ha
  have he := excess_exceptional_card_upper (allPrimes R) (allPrimes_spec R) hR.le ha
  have hu : ((exceptional R k).card : ℝ) ≤
      (((GaussianMass.representatives (R ^ 2)).filter (fun z =>
        k * Real.log (Real.log R) ≤ |(splitOmega (smallPrimes R) z : ℝ) -
          center (smallPrimes R)|)).card : ℝ) +
      (((GaussianMass.representatives (R ^ 2)).filter (fun z =>
        k * Real.log (Real.log R) ≤ (GaussianExcess.excess (allPrimes R) z : ℝ))).card : ℝ) := by
    unfold exceptional
    exact_mod_cast card_union_le _ _
  have hh := div_le_div_of_nonneg_right (hu.trans (add_le_add hw he)) (sq_nonneg R)
  have heq :
      ((Real.pi * R ^ 2 * center (smallPrimes R) +
          (64 * Real.pi + 4) * (R + 1) * ((smallPrimes R).card : ℝ) ^ 2) /
          (k * Real.log (Real.log R)) ^ 2 +
        (108 * Real.pi) * R ^ 2 / (k * Real.log (Real.log R))) / R ^ 2 =
        errorBound R k := by
    unfold errorBound
    field_simp [ne_of_gt hR, ne_of_gt hk, ne_of_gt hlog]
  exact hh.trans_eq heq

lemma logarithmBad_subset_exceptional {R ε k : ℝ} (hR : 1 < R)
    (hM : R ^ (1 / 20 : ℝ) ≤ (cutoff R : ℝ))
    (hbudget : Real.log 4 + 40 * Real.log 2 +
      Real.log 2 * |center (smallPrimes R) - Real.log (Real.log R)| +
      2 * Real.log 2 * k * Real.log (Real.log R) ≤ ε * Real.log (Real.log R)) :
    logarithmBad R ε ⊆ exceptional R k := by
  intro z hz
  have hzP := (mem_filter.mp hz).1
  have hzbad := (mem_filter.mp hz).2
  by_contra hzex
  have hw : |(splitOmega (smallPrimes R) z : ℝ) - center (smallPrimes R)| <
      k * Real.log (Real.log R) := by
    apply lt_of_not_ge
    intro hw
    exact hzex (mem_union_left _ (mem_filter.mpr ⟨hzP, hw⟩))
  have he : (GaussianExcess.excess (allPrimes R) z : ℝ) <
      k * Real.log (Real.log R) := by
    apply lt_of_not_ge
    intro he
    exact hzex (mem_union_right _ (mem_filter.mpr ⟨hzP, he⟩))
  have hp := logarithm_pointwise_error hR hM hzP
  have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have ht := abs_sub_le
    (Real.log ((normCircle z.norm.natAbs).card : ℝ))
    (Real.log 2 * (splitOmega (smallPrimes R) z : ℝ))
    (Real.log 2 * Real.log (Real.log R))
  have ht' := abs_sub_le (splitOmega (smallPrimes R) z : ℝ)
    (center (smallPrimes R)) (Real.log (Real.log R))
  have hm := mul_le_mul_of_nonneg_left ht' hlogTwo
  have hw' := mul_le_mul_of_nonneg_left hw.le hlogTwo
  have he' := mul_le_mul_of_nonneg_left he.le hlogTwo
  have habs : |Real.log 2 * (splitOmega (smallPrimes R) z : ℝ) -
      Real.log 2 * Real.log (Real.log R)| =
        Real.log 2 * |(splitOmega (smallPrimes R) z : ℝ) - Real.log (Real.log R)| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hlogTwo]
  nlinarith

lemma tendsto_deterministic_error :
    Tendsto (fun R : ℝ =>
      (Real.log 4 + 40 * Real.log 2) / Real.log (Real.log R) +
        Real.log 2 * |center (smallPrimes R) / Real.log (Real.log R) - 1|)
      atTop (𝓝 0) := by
  have h1 := GaussianCutoff.tendsto_const_div_loglog (Real.log 4 + 40 * Real.log 2)
  have h2 := (GaussianCutoff.tendsto_center_div_loglog.sub
    (tendsto_const_nhds (x := (1 : ℝ)))).abs
  simpa only [sub_self, abs_zero, mul_zero, add_zero] using
    h1.add (h2.const_mul (Real.log 2))

/-- Outside o(R²) actual nonzero vectors, the logarithm of the norm-circle
cardinality is `(log 2 + o(1))*log(log R)`. -/
theorem tendsto_logarithmBad_card {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ((logarithmBad R ε).card : ℝ) / R ^ 2)
      atTop (𝓝 0) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let k := ε / (4 * Real.log 2)
  have hk : 0 < k := by dsimp [k]; positivity
  have hsmall := tendsto_deterministic_error.eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_errorBound k)
  · exact Eventually.of_forall fun R => div_nonneg (Nat.cast_nonneg _) (sq_nonneg R)
  · filter_upwards [hsmall, eventually_cutoff_bounds, eventually_gt_atTop (1 : ℝ),
      GaussianCutoff.tendsto_loglog.eventually (eventually_gt_atTop 0)] with
      R hsmall hM hR hlog
    have hscale :
        ((Real.log 4 + 40 * Real.log 2) / Real.log (Real.log R) +
          Real.log 2 * |center (smallPrimes R) / Real.log (Real.log R) - 1|) *
            Real.log (Real.log R) =
        Real.log 4 + 40 * Real.log 2 +
          Real.log 2 * |center (smallPrimes R) - Real.log (Real.log R)| := by
      have heq : center (smallPrimes R) / Real.log (Real.log R) - 1 =
          (center (smallPrimes R) - Real.log (Real.log R)) / Real.log (Real.log R) := by
        field_simp
      rw [heq, abs_div, abs_of_pos hlog]
      field_simp
    have hdet := mul_le_mul_of_nonneg_right hsmall.le hlog.le
    rw [hscale] at hdet
    have hkEq : 2 * Real.log 2 * k = ε / 2 := by
      dsimp [k]
      field_simp
      ring
    have hbudget : Real.log 4 + 40 * Real.log 2 +
        Real.log 2 * |center (smallPrimes R) - Real.log (Real.log R)| +
        2 * Real.log 2 * k * Real.log (Real.log R) ≤ ε * Real.log (Real.log R) := by
      rw [hkEq]
      nlinarith
    have hsub := logarithmBad_subset_exceptional hR hM.1 hbudget
    have hc : ((logarithmBad R ε).card : ℝ) ≤ (exceptional R k).card := by
      exact_mod_cast card_le_card hsub
    exact (div_le_div_of_nonneg_right hc (sq_nonneg R)).trans
      (exceptional_card_bound (lt_trans zero_lt_one hR) hk hlog)

/-- Failure of the exact power window in the point-weighted statement. -/
def normalBad (R ε : ℝ) : Finset GaussianInt :=
  (GaussianMass.representatives (R ^ 2)).filter (fun z =>
    ((normCircle z.norm.natAbs).card : ℝ) < (Real.log R) ^ (Real.log 2 - ε) ∨
      (Real.log R) ^ (Real.log 2 + ε) < ((normCircle z.norm.natAbs).card : ℝ))

lemma normalBad_subset_logarithmBad {R ε : ℝ} (hR : 1 < R) :
    normalBad R ε ⊆ logarithmBad R ε := by
  intro z hz
  obtain ⟨hzP, hzbad⟩ := mem_filter.mp hz
  refine mem_filter.mpr ⟨hzP, ?_⟩
  have hc : (0 : ℝ) < (normCircle z.norm.natAbs).card := by
    exact_mod_cast card_pos.mpr
      (show (normCircle z.norm.natAbs).Nonempty from ⟨z, self_mem_normCircle z⟩)
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have habs1 := le_abs_self
    (Real.log ((normCircle z.norm.natAbs).card : ℝ) - Real.log 2 * Real.log (Real.log R))
  have habs2 := neg_le_abs
    (Real.log ((normCircle z.norm.natAbs).card : ℝ) - Real.log 2 * Real.log (Real.log R))
  rcases hzbad with hlo | hhi
  · have hl := (Real.log_lt_log_iff hc (Real.rpow_pos_of_pos hlogR _)).mpr hlo
    rw [Real.log_rpow hlogR] at hl
    nlinarith
  · have hh := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hlogR _) hc).mpr hhi
    rw [Real.log_rpow hlogR] at hh
    nlinarith

/-- Point-weighted normal order, at every real radius, with the genuine
representation count and no external normal-order assumption. -/
theorem tendsto_normalBad_card {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => ((normalBad R ε).card : ℝ) / R ^ 2)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_logarithmBad_card hε)
  · exact Eventually.of_forall fun R => div_nonneg (Nat.cast_nonneg _) (sq_nonneg R)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hc : ((normalBad R ε).card : ℝ) ≤ (logarithmBad R ε).card := by
      exact_mod_cast card_le_card (normalBad_subset_logarithmBad (ε := ε) hR)
    exact div_le_div_of_nonneg_right hc (sq_nonneg R)

end DistanceCounts.GaussianNormalOrder
end
end

-- Source: DistanceCounts/LowPalette.lean
section
noncomputable section

namespace DistanceCounts.LowPalette

open Finset Filter
open scoped Classical Topology

abbrev population (R : ℝ) := GaussianMass.representatives (R ^ 2)

def norms (R : ℝ) : Finset ℕ :=
  (population R).image (fun z => z.norm.natAbs)

/-- Norms of the actual vectors in one canonical Gaussian quotient class. -/
def normPalette {q : ℕ} (a : GaussianResidues.Residue q) (R : ℝ) : Finset ℕ :=
  ((population R).filter (fun z => GaussianNorm.residue q z = a)).image
    (fun z => z.norm.natAbs)

/-- Every class of the quotient, including the zero class. -/
def allResidues (q : ℕ) (hq : 0 < q) : Finset (GaussianResidues.Residue q) :=
  @Finset.univ _ (@Fintype.ofFinite _ (GaussianResidues.finite_residue q hq))

lemma mem_allResidues (q : ℕ) (hq : 0 < q) (a : GaussianResidues.Residue q) :
    a ∈ allResidues q hq := by
  letI : Fintype (GaussianResidues.Residue q) :=
    @Fintype.ofFinite _ (GaussianResidues.finite_residue q hq)
  exact Finset.mem_univ a

def aggregate (q : ℕ) (hq : 0 < q) (R : ℝ) : ℝ :=
  ∑ a ∈ allResidues q hq, ((normPalette a R).card : ℝ)

def circleResidues (q n : ℕ) : Finset (GaussianResidues.Residue q) :=
  (normCircle n).image (GaussianNorm.residue q)

lemma mem_norms_bounds {R : ℝ} {n : ℕ} (hn : n ∈ norms R) :
    0 < n ∧ (n : ℝ) ≤ R ^ 2 := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hn
  obtain ⟨hz0, hzR⟩ := (GaussianMass.mem_representatives (sq_nonneg R) z).mp hz
  exact ⟨Nat.pos_of_ne_zero (GaussianNormalOrder.natNorm_ne_zero hz0), hzR⟩

/-- A positive norm below the cutoff has its entire circle in the population. -/
theorem population_norm_fiber {R : ℝ} {n : ℕ} (hn : 0 < n)
    (hnR : (n : ℝ) ≤ R ^ 2) :
    (population R).filter (fun z => z.norm.natAbs = n) = normCircle n := by
  ext z
  rw [mem_filter, mem_normCircle]
  constructor
  · exact fun h => h.2
  · intro hz
    refine ⟨(GaussianMass.mem_representatives (sq_nonneg R) z).mpr ⟨?_, ?_⟩, hz⟩
    · exact ne_zero_of_mem_normCircle hn.ne' ((mem_normCircle n z).mpr hz)
    · simpa only [hz] using hnR

lemma population_norm_fiber_of_mem {R : ℝ} {n : ℕ} (hn : n ∈ norms R) :
    (population R).filter (fun z => z.norm.natAbs = n) = normCircle n :=
  population_norm_fiber (mem_norms_bounds hn).1 (mem_norms_bounds hn).2


lemma normPalette_eq_filter {q : ℕ} (a : GaussianResidues.Residue q) (R : ℝ) :
    normPalette a R = (norms R).filter (fun n => a ∈ circleResidues q n) := by
  ext n
  constructor
  · intro hn
    obtain ⟨z, hz, hzn⟩ := mem_image.mp hn
    obtain ⟨hzP, hza⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_image.mpr ⟨z, hzP, hzn⟩,
      mem_image.mpr ⟨z, (mem_normCircle n z).mpr hzn, hza⟩⟩
  · intro hn
    obtain ⟨hn, ha⟩ := mem_filter.mp hn
    obtain ⟨z, hz, hza⟩ := mem_image.mp ha
    have hzP : z ∈ population R := by
      have : z ∈ (population R).filter (fun z => z.norm.natAbs = n) := by
        rw [population_norm_fiber_of_mem hn]
        exact hz
      exact (mem_filter.mp this).1
    exact mem_image.mpr ⟨z, mem_filter.mpr ⟨hzP, hza⟩,
      (mem_normCircle n z).mp hz⟩

/-- Exact double counting of norm/residue incidences, not vectors. -/
theorem aggregate_eq_sum_circleResidues (q : ℕ) (hq : 0 < q) (R : ℝ) :
    aggregate q hq R = ∑ n ∈ norms R, ((circleResidues q n).card : ℝ) := by
  unfold aggregate
  simp only [normPalette_eq_filter, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  have hsub : circleResidues q n ⊆ allResidues q hq :=
    fun a _ => mem_allResidues q hq a
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← sum_filter]
  have heq : (allResidues q hq).filter (fun a => a ∈ circleResidues q n) =
      circleResidues q n := by
    ext a
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  rw [heq]

/-- Actual circle residues inject into the corresponding quotient norm fiber. -/
theorem circleResidues_card_le (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hfour : P.card ≤ 4) (n : ℕ) :
    (circleResidues (∏ p ∈ P, p) n).card ≤ 16 * (∏ p ∈ P, p) := by
  let q := ∏ p ∈ P, p
  have hq : 0 < q := prod_pos (fun p hp => (hprime p hp).pos)
  letI : Finite (GaussianResidues.Residue q) := GaussianResidues.finite_residue q hq
  let f : {a // a ∈ circleResidues q n} →
      {a : GaussianResidues.Residue q // GaussianResidues.norm q a = (n : ZMod q)} :=
    fun a => ⟨a.1, by
      obtain ⟨z, hz, hza⟩ := mem_image.mp a.2
      rw [← hza, GaussianResidues.norm_residue,
        (mem_normCircle_iff_norm n z).mp hz]
      simp⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : a.1 = b.1 := congrArg
      (fun x : {a : GaussianResidues.Residue q //
        GaussianResidues.norm q a = (n : ZMod q)} => x.1) hab
    exact Subtype.ext hab'
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at hh
  exact hh.trans (GaussianResidues.card_norm_fiber_four_primes P hprime hfour _)

lemma sum_circle_card (R : ℝ) :
    ∑ n ∈ norms R, ((normCircle n).card : ℝ) = (population R).card := by
  have h := card_eq_sum_card_image (fun z : GaussianInt => z.norm.natAbs) (population R)
  change (population R).card = ∑ n ∈ norms R,
    ((population R).filter (fun z => z.norm.natAbs = n)).card at h
  rw [sum_congr rfl (fun n hn => congrArg Finset.card
    (population_norm_fiber_of_mem hn))] at h
  exact_mod_cast h.symm

/-- The error is point-weighted once: bad incidences are bounded by the
actual bad vectors, with no factor depending on the modulus. -/
theorem aggregate_le (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hfour : P.card ≤ 4) {R ε : ℝ} (hR : 1 < R) :
    aggregate (∏ p ∈ P, p) (prod_pos (fun p hp => (hprime p hp).pos)) R ≤
      (16 * ((∏ p ∈ P, p : ℕ) : ℝ) / (Real.log R) ^ (Real.log 2 - ε)) *
        (population R).card + (GaussianNormalOrder.normalBad R ε).card := by
  let q := ∏ p ∈ P, p
  let T := (Real.log R) ^ (Real.log 2 - ε)
  let B := GaussianNormalOrder.normalBad R ε
  have hT : 0 < T := Real.rpow_pos_of_pos (Real.log_pos hR) _
  have hK : 0 ≤ (16 * (q : ℝ) / T) := by positivity
  have hB : B ⊆ population R := filter_subset _ _
  have hBsum : ∑ n ∈ norms R,
      (((B.filter (fun z => z.norm.natAbs = n)).card) : ℝ) = B.card := by
    have h := card_eq_sum_card_fiberwise (f := fun z : GaussianInt => z.norm.natAbs)
      (s := B) (t := norms R) (fun z hz => mem_image_of_mem _ (hB hz))
    exact_mod_cast h.symm
  rw [aggregate_eq_sum_circleResidues]
  calc
    ∑ n ∈ norms R, ((circleResidues q n).card : ℝ) ≤
        ∑ n ∈ norms R, ((16 * (q : ℝ) / T) * (normCircle n).card +
          ((B.filter (fun z => z.norm.natAbs = n)).card : ℝ)) := by
      apply sum_le_sum
      intro n hn
      by_cases hgood : T ≤ ((normCircle n).card : ℝ)
      · have hc : ((circleResidues q n).card : ℝ) ≤ 16 * (q : ℝ) := by
          exact_mod_cast circleResidues_card_le P hprime hfour n
        have hscale := mul_le_mul_of_nonneg_left hgood hK
        have hcancel : (16 * (q : ℝ) / T) * T = 16 * (q : ℝ) :=
          div_mul_cancel₀ _ hT.ne'
        rw [hcancel] at hscale
        exact (hc.trans hscale).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
      · have hbad : ((normCircle n).card : ℝ) < T := lt_of_not_ge hgood
        have hf : B.filter (fun z => z.norm.natAbs = n) = normCircle n := by
          change (GaussianNormalOrder.normalBad R ε).filter
            (fun z => z.norm.natAbs = n) = normCircle n
          ext z
          rw [mem_filter, GaussianNormalOrder.normalBad, mem_filter,
            mem_normCircle]
          constructor
          · exact fun h => h.2
          · intro hzn
            have hzP : z ∈ population R := by
              have hz : z ∈ (population R).filter (fun z => z.norm.natAbs = n) := by
                rw [population_norm_fiber_of_mem hn]
                exact (mem_normCircle n z).mpr hzn
              exact (mem_filter.mp hz).1
            exact ⟨⟨hzP, Or.inl (by simpa only [hzn] using hbad)⟩, hzn⟩
        rw [hf]
        have hc : ((circleResidues q n).card : ℝ) ≤ (normCircle n).card := by
          exact_mod_cast card_image_le (f := GaussianNorm.residue q) (s := normCircle n)
        exact hc.trans (le_add_of_nonneg_left (mul_nonneg hK (Nat.cast_nonneg _)))
    _ = (16 * (q : ℝ) / T) * (population R).card + B.card := by
      rw [sum_add_distrib, ← mul_sum, sum_circle_card, hBsum]

/-- The original nonzero radius-R population has density pi. -/
theorem tendsto_population_card :
    Tendsto (fun R : ℝ => ((population R).card : ℝ) / R ^ 2) atTop (𝓝 Real.pi) := by
  let b : ℝ → ℝ := fun R => 4 * (Real.pi + 1) * (R⁻¹ + (R⁻¹) ^ 2)
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa [b] using (hi.add (hi.pow 2)).const_mul (4 * (Real.pi + 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (tendsto_const_nhds (x := Real.pi)).sub hb)
    (by simpa using (tendsto_const_nhds (x := Real.pi)).add hb)
  all_goals
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hc := GaussianMass.classBall_card_error (sq_nonneg R)
    rw [Real.sqrt_sq hR.le] at hc
    have hp : ((population R).card : ℝ) =
        4 * ((GaussianMass.classBall (R ^ 2)).card : ℝ) := by
      exact_mod_cast GaussianMass.representatives_card (sq_nonneg R)
    have hlo := (abs_le.mp hc).1
    have hhi := (abs_le.mp hc).2
    have hbR : b R * R ^ 2 = 4 * (Real.pi + 1) * (R + 1) := by
      dsimp [b]
      field_simp [hR.ne']
      <;> ring
    first
    | apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
      rw [hp]
      nlinarith
    | apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
      rw [hp]
      nlinarith

/-- Explicit radius-only error; no modulus appears in the exceptional term. -/
def error (c R : ℝ) : ℝ :=
  16 * (Real.log R) ^ (-((Real.log 2 - c) / 2)) *
      (((population R).card : ℝ) / R ^ 2) +
    ((GaussianNormalOrder.normalBad R ((Real.log 2 - c) / 2)).card : ℝ) / R ^ 2

theorem tendsto_error {c : ℝ} (hc : c < Real.log 2) :
    Tendsto (error c) atTop (𝓝 0) := by
  unfold error
  have hε : 0 < (Real.log 2 - c) / 2 := by linarith
  have hp := (tendsto_rpow_neg_atTop hε).comp Real.tendsto_log_atTop
  have h := ((hp.const_mul 16).mul tendsto_population_card).add
    (GaussianNormalOrder.tendsto_normalBad_card hε)
  simpa only [Function.comp_def, mul_zero, zero_mul, zero_add] using h

/-- Uniform low-denominator transition. Inertness is unnecessary: the bound
holds for every product of at most four distinct primes, hence for inert ones. -/
theorem aggregate_div_sq_le_error {c R : ℝ} (hc : c < Real.log 2) (hR : 1 < R)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (hfour : P.card ≤ 4)
    (hq : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (Real.log R) ^ c) :
    aggregate (∏ p ∈ P, p) (prod_pos (fun p hp => (hprime p hp).pos)) R / R ^ 2 ≤
      error c R := by
  let ε := (Real.log 2 - c) / 2
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hT : 0 < (Real.log R) ^ (Real.log 2 - ε) := Real.rpow_pos_of_pos hlog _
  have hratio : (16 * ((∏ p ∈ P, p : ℕ) : ℝ)) /
      (Real.log R) ^ (Real.log 2 - ε) ≤ 16 * (Real.log R) ^ (-ε) := by
    calc
      _ ≤ (16 * (Real.log R) ^ c) / (Real.log R) ^ (Real.log 2 - ε) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) hT.le
      _ = _ := by
        rw [mul_div_assoc, ← Real.rpow_sub hlog]
        congr 2
        dsimp [ε]
        ring
  have h := div_le_div_of_nonneg_right
    (aggregate_le P hprime hfour (ε := ε) hR) (sq_nonneg R)
  have hm := mul_le_mul_of_nonneg_right hratio
    (div_nonneg (Nat.cast_nonneg (population R).card) (sq_nonneg R))
  rw [add_div, mul_div_assoc] at h
  apply h.trans
  change (16 * ((∏ p ∈ P, p : ℕ) : ℝ) /
      (Real.log R) ^ (Real.log 2 - ε)) *
      (((population R).card : ℝ) / R ^ 2) +
      ((GaussianNormalOrder.normalBad R ε).card : ℝ) / R ^ 2 ≤
    16 * (Real.log R) ^ (-ε) * (((population R).card : ℝ) / R ^ 2) +
      ((GaussianNormalOrder.normalBad R ε).card : ℝ) / R ^ 2
  linarith only [hm]

theorem eventually_uniform_low {c : ℝ} (hc : c < Real.log 2) :
    ∀ᶠ R : ℝ in atTop, ∀ P : Finset ℕ,
      ∀ hprime : ∀ p ∈ P, p.Prime, P.card ≤ 4 →
      ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (Real.log R) ^ c →
      aggregate (∏ p ∈ P, p) (prod_pos (fun p hp => (hprime p hp).pos)) R / R ^ 2 ≤
        error c R := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  exact fun P hprime hfour hq => aggregate_div_sq_le_error hc hR P hprime hfour hq

end DistanceCounts.LowPalette
end
end

-- Source: DistanceCounts/PrimitiveNormPairs.lean
section
/-! Gcd-based primitive equal-norm pairs and their exact transverse congruences. -/

noncomputable section

namespace DistanceCounts.PrimitiveNormPairs

/-- Coprime equal-norm Gaussian integers are conjugate up to an actual unit. -/
theorem coprime_equal_norm_conjugate {v t : GaussianInt} (hv : v ≠ 0)
    (hcop : IsCoprime v t) (hn : v.norm = t.norm) :
    ∃ u : GaussianIntˣ, t = (u : GaussianInt) * star v := by
  have hd : v ∣ t * star t := by
    rw [← Zsqrtd.norm_eq_mul_conj, ← hn, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _
  obtain ⟨a, ha⟩ := hcop.dvd_of_dvd_mul_left hd
  have hvN : v.norm ≠ 0 := GaussianInt.norm_eq_zero.not.mpr hv
  have haN : a.norm = 1 := by
    have he := congrArg Zsqrtd.norm ha
    rw [Zsqrtd.norm_conj, Zsqrtd.norm_mul, ← hn] at he
    apply mul_left_cancel₀ hvN
    simpa only [mul_one] using he.symm
  have hau : IsUnit (star a) :=
    (Zsqrtd.norm_eq_one_iff.mp (show a.norm.natAbs = 1 by simp [haN])).star
  obtain ⟨u, hu⟩ := hau
  refine ⟨u, ?_⟩
  have he := congrArg star ha
  simpa only [star_star, star_mul, ← hu] using he

/-- The common factor is the actual gcd, and the primitive vector is its actual
Euclidean quotient. Coprimality with the conjugate is derived, not assumed. -/
theorem gcd_decomposition {z w : GaussianInt} (hz : z ≠ 0) (hw : w ≠ 0)
    (hn : z.norm = w.norm) :
    ∃ (g v : GaussianInt) (u : GaussianIntˣ),
      g = EuclideanDomain.gcd z w ∧ v = z / EuclideanDomain.gcd z w ∧
      g ≠ 0 ∧ v ≠ 0 ∧ z = g * v ∧ w = g * (u : GaussianInt) * star v ∧
      IsCoprime v (star v) := by
  letI : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt
  let g := GCDMonoid.gcd z w
  let v := z / g
  let t := w / g
  have hg : g ≠ 0 := gcd_ne_zero_of_left hz
  have hv : v ≠ 0 := left_div_gcd_ne_zero hz
  have hzv : z = g * v :=
    (EuclideanDomain.mul_div_cancel' hg (GCDMonoid.gcd_dvd_left z w)).symm
  have hwt : w = g * t :=
    (EuclideanDomain.mul_div_cancel' hg (GCDMonoid.gcd_dvd_right z w)).symm
  have hcop : IsCoprime v t := isCoprime_div_gcd_div_gcd hw
  have hvt : v.norm = t.norm := by
    rw [hzv, hwt, Zsqrtd.norm_mul, Zsqrtd.norm_mul] at hn
    exact mul_left_cancel₀ (GaussianInt.norm_eq_zero.not.mpr hg) hn
  obtain ⟨u, hu⟩ := coprime_equal_norm_conjugate hv hcop hvt
  refine ⟨g, v, u, rfl, rfl, hg, hv, hzv, ?_, ?_⟩
  · rw [hwt, hu, mul_assoc]
  · apply hcop.of_isCoprime_of_dvd_right
    rw [hu]
    exact dvd_mul_left _ _

/-- Cancelling the gcd preserves the exact Gaussian congruence. Neither oddness
nor positivity is needed for cancellation itself. -/
theorem cancel_common_factor {q : ℕ} {z w g v : GaussianInt} {u : GaussianIntˣ}
    (hz : z = g * v) (hw : w = g * (u : GaussianInt) * star v)
    (hcop : IsCoprime (q : GaussianInt) g) (hd : (q : GaussianInt) ∣ z - w) :
    (q : GaussianInt) ∣ v - (u : GaussianInt) * star v := by
  apply hcop.dvd_of_dvd_mul_left
  simpa only [hz, hw, mul_sub, mul_assoc] using hd

/-- Exhaustive enumeration of the four actual Gaussian units. -/
theorem unit_values (u : GaussianIntˣ) :
    (u : GaussianInt) = ⟨1, 0⟩ ∨ (u : GaussianInt) = ⟨-1, 0⟩ ∨
      (u : GaussianInt) = ⟨0, 1⟩ ∨ (u : GaussianInt) = ⟨0, -1⟩ := by
  have h := (mem_normCircle_one_iff (u : GaussianInt)).mpr u.isUnit
  rw [normCircle_one] at h
  simpa only [Finset.mem_insert, Finset.mem_singleton] using h

/-- The exact transverse coefficients, with no unit or rational factor dropped. -/
theorem transverse_differences (v : GaussianInt) :
    v - (⟨1, 0⟩ : GaussianInt) * star v = ⟨0, 2 * v.im⟩ ∧
    v - (⟨-1, 0⟩ : GaussianInt) * star v = ⟨2 * v.re, 0⟩ ∧
    v - (⟨0, 1⟩ : GaussianInt) * star v = ⟨v.re - v.im, -(v.re - v.im)⟩ ∧
    v - (⟨0, -1⟩ : GaussianInt) * star v = ⟨v.re + v.im, v.re + v.im⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp <;> ring

private theorem odd_dvd_two_mul_iff {q a : ℤ} (hq : Odd q) :
    q ∣ 2 * a ↔ q ∣ a := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := hq
    have he : q * a - k * (2 * a) = a := by rw [hk]; ring
    rw [← he]
    exact dvd_sub (dvd_mul_right q a) (dvd_mul_of_dvd_right h k)
  · intro h
    exact dvd_mul_of_dvd_right h 2

private theorem rational_dvd_iff (q : ℕ) (v : GaussianInt) :
    (q : GaussianInt) ∣ v ↔ (q : ℤ) ∣ v.re ∧ (q : ℤ) ∣ v.im := by
  simpa only [Int.cast_natCast] using Zsqrtd.intCast_dvd (q : ℤ) v

/-- For odd rational moduli, the four congruences are equivalences. The axis
cases cancel precisely the factor two; the diagonal cases have coefficient one. -/
theorem transverse_congruences (q : ℕ) (hq : Odd q) (v : GaussianInt) :
    ((q : GaussianInt) ∣ v - (⟨1, 0⟩ : GaussianInt) * star v ↔ (q : ℤ) ∣ v.im) ∧
    ((q : GaussianInt) ∣ v - (⟨-1, 0⟩ : GaussianInt) * star v ↔ (q : ℤ) ∣ v.re) ∧
    ((q : GaussianInt) ∣ v - (⟨0, 1⟩ : GaussianInt) * star v ↔
      (q : ℤ) ∣ v.re - v.im) ∧
    ((q : GaussianInt) ∣ v - (⟨0, -1⟩ : GaussianInt) * star v ↔
      (q : ℤ) ∣ v.re + v.im) := by
  have hqZ : Odd (q : ℤ) := by
    obtain ⟨k, hk⟩ := hq
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := transverse_differences v
  rw [h₁, h₂, h₃, h₄]
  simp [rational_dvd_iff, odd_dvd_two_mul_iff hqZ]
  intro hd
  simpa only [neg_sub] using (dvd_neg.mpr hd)

/-- A nonidentity equal-norm collision forces a nonzero transverse coordinate
in the appropriate one of the four unit directions. -/
theorem nonzero_transverse {q : ℕ} (hq : Odd q) {v : GaussianInt} {u : GaussianIntˣ}
    (hd : (q : GaussianInt) ∣ v - (u : GaussianInt) * star v)
    (hne : v ≠ (u : GaussianInt) * star v) :
    ((q : ℤ) ∣ v.im ∧ v.im ≠ 0) ∨
    ((q : ℤ) ∣ v.re ∧ v.re ≠ 0) ∨
    ((q : ℤ) ∣ v.re - v.im ∧ v.re - v.im ≠ 0) ∨
    ((q : ℤ) ∣ v.re + v.im ∧ v.re + v.im ≠ 0) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := transverse_congruences q hq v
  rcases unit_values u with hu | hu | hu | hu
  · left
    refine ⟨h₁.mp (by simpa only [hu] using hd), ?_⟩
    intro h
    apply hne
    ext <;> simp [hu, h]
  · right; left
    refine ⟨h₂.mp (by simpa only [hu] using hd), ?_⟩
    intro h
    apply hne
    ext <;> simp [hu, h]
  · right; right; left
    refine ⟨h₃.mp (by simpa only [hu] using hd), ?_⟩
    intro h
    apply hne
    ext <;> simp [hu] <;> omega
  · right; right; right
    refine ⟨h₄.mp (by simpa only [hu] using hd), ?_⟩
    intro h
    apply hne
    ext <;> simp [hu] <;> omega

/-- The gcd decomposition together with the transverse conclusion, for a
positive odd modulus coprime to the actual common factor. -/
theorem collision_decomposition {q : ℕ} (_hq : 0 < q) (hqodd : Odd q)
    {z w : GaussianInt} (hz : z ≠ 0) (hw : w ≠ 0) (hn : z.norm = w.norm)
    (hne : w ≠ z) (hd : (q : GaussianInt) ∣ z - w)
    (hcop : IsCoprime (q : GaussianInt) (EuclideanDomain.gcd z w)) :
    ∃ (g v : GaussianInt) (u : GaussianIntˣ),
      g = EuclideanDomain.gcd z w ∧ v = z / EuclideanDomain.gcd z w ∧
      g ≠ 0 ∧ v ≠ 0 ∧ z = g * v ∧ w = g * (u : GaussianInt) * star v ∧
      IsCoprime v (star v) ∧
      (((q : ℤ) ∣ v.im ∧ v.im ≠ 0) ∨
       ((q : ℤ) ∣ v.re ∧ v.re ≠ 0) ∨
       ((q : ℤ) ∣ v.re - v.im ∧ v.re - v.im ≠ 0) ∨
       ((q : ℤ) ∣ v.re + v.im ∧ v.re + v.im ≠ 0)) := by
  obtain ⟨g, v, u, hgcd, hvdiv, hg, hv, hzv, hwv, hprim⟩ := gcd_decomposition hz hw hn
  refine ⟨g, v, u, hgcd, hvdiv, hg, hv, hzv, hwv, hprim, ?_⟩
  apply nonzero_transverse hqodd
  · exact cancel_common_factor hzv hwv (hgcd.symm ▸ hcop) hd
  · intro he
    apply hne
    calc
      w = g * ((u : GaussianInt) * star v) := by rw [hwv, mul_assoc]
      _ = g * v := by rw [← he]
      _ = z := hzv.symm


end DistanceCounts.PrimitiveNormPairs
end
end

-- Source: DistanceCounts/GaussianPrimeWeight.lean
section
/-! A Chebyshev bound for the logarithmic first moment of genuine Gaussian primes. -/

noncomputable section

namespace DistanceCounts.GaussianPrimeWeight

open Finset GaussianMass
open scoped Classical

/-- All prime associate classes, with no choice of sign or conjugate. -/
def primeClassesY (Y : ℝ) : Finset (Associates GaussianInt) :=
  (classBall Y).filter Prime

lemma mem_primeClassesY {Y : ℝ} (hY : 0 ≤ Y) (a : Associates GaussianInt) :
    a ∈ primeClassesY Y ↔ Prime a ∧ (classNorm a : ℝ) ≤ Y := by
  rw [primeClassesY, mem_filter, mem_classBall hY]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.ne_zero, h.2⟩, h.1⟩⟩

lemma classNorm_natCast (n : ℕ) :
    classNorm (Associates.mk (n : GaussianInt)) = n ^ 2 := by
  simp [classNorm_mk, Zsqrtd.norm_natCast, pow_two, Int.natAbs_mul]

/-- Primality detects a rational prime factor of a nonzero integer. -/
lemma prime_dvd_natCast_exists {a : Associates GaussianInt} (ha : Prime a)
    (n : ℕ) (hn : n ≠ 0) (hd : a ∣ Associates.mk (n : GaussianInt)) :
    ∃ p : ℕ, p.Prime ∧ a ∣ Associates.mk (p : GaussianInt) := by
  revert hn hd
  induction n using Nat.recOnMul with
  | zero => exact fun hn _ => (hn rfl).elim
  | one => exact fun _ hd => (ha.not_dvd_one (by simpa using hd)).elim
  | prime p hp => exact fun _ hd => ⟨p, hp, hd⟩
  | mul m n hm ih =>
      intro hn hd
      rw [Nat.cast_mul, ← Associates.mk_mul_mk] at hd
      rcases ha.dvd_or_dvd hd with hd | hd
      · exact hm (fun h => hn (by simp [h])) hd
      · exact ih (fun h => hn (by simp [h])) hd

/-- Every Gaussian prime lies over a rational prime: use the actual identity
`z * conjugate z = norm z`, rather than a prime-distribution hypothesis. -/
lemma prime_lies_over {a : Associates GaussianInt} (ha : Prime a) :
    ∃ p : ℕ, p.Prime ∧ a ∣ Associates.mk (p : GaussianInt) := by
  obtain ⟨z, rfl⟩ := Associates.mk_surjective a
  apply prime_dvd_natCast_exists ha z.norm.natAbs
  · exact ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (classNorm_prime_two_le ha))
  · apply Associates.mk_dvd_mk.mpr
    rw [GaussianInt.natCast_natAbs_norm, Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right _ _

/-- A divisor of a rational prime either has that prime as its norm or is the
entire rational prime class. The latter case includes inert primes. -/
lemma prime_over_classification {a : Associates GaussianInt} (ha : Prime a)
    {p : ℕ} (hp : p.Prime) (hd : a ∣ Associates.mk (p : GaussianInt)) :
    classNorm a = p ∨ a = Associates.mk (p : GaussianInt) := by
  obtain ⟨b, hb⟩ := hd
  by_cases hb1 : b = 1
  · exact Or.inr (by simpa [hb1] using hb.symm)
  · have ha1 : classNorm a ≠ 1 := fun h => ha.ne_one ((classNorm_eq_one a).mp h)
    have hb1' : classNorm b ≠ 1 := fun h => hb1 ((classNorm_eq_one b).mp h)
    have he : classNorm a * classNorm b = p ^ 2 := by
      rw [← classNorm_mul, ← hb, classNorm_natCast]
    exact Or.inl ((hp.mul_eq_prime_sq_iff ha1 hb1').mp he).1


/-- The prime-norm fiber is an image of the full norm circle, including both
conjugate unit orbits. Eight is a deliberately loose bound on its cardinality. -/
def primeNormClasses (p : ℕ) : Finset (Associates GaussianInt) :=
  (normCircle p).image Associates.mk

lemma mem_primeNormClasses (p : ℕ) (a : Associates GaussianInt) :
    a ∈ primeNormClasses p ↔ classNorm a = p := by
  constructor
  · rintro ha
    obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
    exact (mem_normCircle p z).mp hz
  · intro ha
    obtain ⟨z, rfl⟩ := Associates.mk_surjective a
    exact mem_image.mpr ⟨z, (mem_normCircle p z).mpr ha, rfl⟩

lemma primeNormClasses_card_le_eight {p : ℕ} (hp : p.Prime) :
    (primeNormClasses p).card ≤ 8 :=
  (card_image_le).trans (normCircle_prime_card_le_eight hp)

/-- This cover includes the ramified class, both split classes, and the inert
class. It is allowed to contain a composite rational class in the split case. -/
def rationalPrimeCover (p : ℕ) : Finset (Associates GaussianInt) :=
  primeNormClasses p ∪ {Associates.mk (p : GaussianInt)}

lemma primeClassesY_subset_cover {Y : ℝ} (hY : 0 ≤ Y) :
    primeClassesY Y ⊆ (Nat.primesLE ⌊Y⌋₊).biUnion rationalPrimeCover := by
  intro a ha
  obtain ⟨hap, haY⟩ := (mem_primeClassesY hY a).mp ha
  obtain ⟨p, hp, hd⟩ := prime_lies_over hap
  obtain hn | he := prime_over_classification hap hp hd
  · apply mem_biUnion.mpr
    refine ⟨p, Nat.mem_primesLE.mpr ⟨?_, hp⟩, mem_union.mpr (Or.inl ?_)⟩
    · apply (Nat.le_floor_iff hY).mpr
      simpa [hn] using haY
    · exact (mem_primeNormClasses p a).mpr hn
  · subst a
    apply mem_biUnion.mpr
    refine ⟨p, Nat.mem_primesLE.mpr ⟨?_, hp⟩, mem_union.mpr (Or.inr (mem_singleton_self _))⟩
    apply (Nat.le_floor_iff hY).mpr
    have hpp : p ≤ p ^ 2 := by nlinarith [hp.two_le]
    exact (by exact_mod_cast hpp : (p : ℝ) ≤ (p ^ 2 : ℕ)).trans
      (by simpa [classNorm_natCast] using haY)

def weight (a : Associates GaussianInt) : ℝ :=
  Real.log (classNorm a) / classNorm a

lemma weight_nonneg (a : Associates GaussianInt) : 0 ≤ weight a := by
  unfold weight
  by_cases h : classNorm a = 0
  · simp [h]
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h))
      (Nat.cast_nonneg _)

private lemma weight_union_le (s t : Finset (Associates GaussianInt)) :
    (∑ a ∈ s ∪ t, weight a) ≤ (∑ a ∈ s, weight a) + ∑ a ∈ t, weight a := by
  have he := sum_union_inter (s₁ := s) (s₂ := t) (f := weight)
  have hn : 0 ≤ ∑ a ∈ s ∩ t, weight a := sum_nonneg (fun a _ => weight_nonneg a)
  linarith

private lemma weight_biUnion_le (s : Finset ℕ) :
    (∑ a ∈ s.biUnion rationalPrimeCover, weight a) ≤
      ∑ p ∈ s, ∑ a ∈ rationalPrimeCover p, weight a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [biUnion_insert, sum_insert hp]
      have hu := weight_union_le (rationalPrimeCover p) (s.biUnion rationalPrimeCover)
      linarith

lemma rationalPrimeCover_weight_le {p : ℕ} (hp : p.Prime) :
    (∑ a ∈ rationalPrimeCover p, weight a) ≤ 10 * (Real.log p / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hcircle : (∑ a ∈ primeNormClasses p, weight a) ≤ 8 * (Real.log p / p) := by
    calc
      _ = (primeNormClasses p).card * (Real.log p / p) := by
        rw [sum_congr rfl (fun a ha => show weight a = Real.log p / p by
          rw [weight, (mem_primeNormClasses p a).mp ha])]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast primeNormClasses_card_le_eight hp) (div_nonneg hl hp0.le)
  have hrat : weight (Associates.mk (p : GaussianInt)) ≤ 2 * (Real.log p / p) := by
    rw [weight, classNorm_natCast, Nat.cast_pow, Real.log_pow]
    have hpp : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    calc
      _ ≤ (2 * Real.log p) / p := div_le_div_of_nonneg_left (by positivity) hp0 hpp
      _ = _ := by ring
  have hcover := weight_union_le (primeNormClasses p) {Associates.mk (p : GaussianInt)}
  simp only [sum_singleton] at hcover
  unfold rationalPrimeCover
  linarith

/-- Discrete partial summation of the ordinary Chebyshev estimate. Only one
harmonic sum occurs, so the result is logarithmic, not squared-logarithmic. -/
lemma rationalPrime_weight_le {Y : ℝ} (hY : 1 ≤ Y) :
    (∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p / p) ≤
      (2 * Real.log 4) * (1 + Real.log Y) := by
  let n := ⌊Y⌋₊
  let c : ℕ → ℝ := fun i => if i.Prime then Real.log i else 0
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hn : 0 < n := Nat.floor_pos.mpr hY
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have htheta (k : ℕ) : (∑ i ∈ range (k + 1), c i) = Chebyshev.theta k := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    simp [Nat.primesLE, Nat.primesBelow_eq_filter_range, sum_filter, c]
  have hsum : (∑ p ∈ Nat.primesLE n, Real.log p / p) =
      ∑ i ∈ range (n + 1), (1 / (i : ℝ)) * c i := by
    simp only [Nat.primesLE, Nat.primesBelow_eq_filter_range, sum_filter]
    apply sum_congr rfl
    intro i _
    simp only [c]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  have hab : (∑ p ∈ Nat.primesLE n, Real.log p / p) =
      Chebyshev.theta n / n +
        ∑ i ∈ range n, Chebyshev.theta i / ((i : ℝ) * (i + 1)) := by
    rw [hsum]
    change (∑ i ∈ range (n + 1), (1 / (i : ℝ)) • c i) = _
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel, smul_eq_mul, htheta, Nat.cast_add, Nat.cast_one]
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    · ring
    · apply sum_congr rfl
      intro i _
      by_cases hi : i = 0
      · simp [hi, Chebyshev.theta]
      · have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast hi
        have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hi0, hi1]
        <;> ring
  have hK : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hhead : Chebyshev.theta n / n ≤ Real.log 4 :=
    (div_le_iff₀ hn0).mpr (Chebyshev.theta_le_log4_mul_x hn0.le)
  have hterm (i : ℕ) : Chebyshev.theta i / ((i : ℝ) * (i + 1)) ≤
      Real.log 4 / (i + 1) := by
    by_cases hi : i = 0
    · simp [hi, hK]
    · have hi0 : (0 : ℝ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi
      calc
        _ ≤ (Real.log 4 * i) / ((i : ℝ) * (i + 1)) :=
          div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x hi0.le) (by positivity)
        _ = _ := by
          have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
          field_simp [ne_of_gt hi0, hi1]
          <;> ring
  have hhar : (∑ i ∈ range n, Real.log 4 / ((i : ℝ) + 1)) =
      Real.log 4 * (harmonic n : ℝ) := by
    simp [harmonic, div_eq_mul_inv, mul_sum]
  calc
    _ = Chebyshev.theta n / n +
        ∑ i ∈ range n, Chebyshev.theta i / ((i : ℝ) * (i + 1)) := hab
    _ ≤ Real.log 4 + ∑ i ∈ range n, Real.log 4 / (i + 1) :=
      add_le_add hhead (sum_le_sum (fun i _ => hterm i))
    _ = Real.log 4 * (1 + (harmonic n : ℝ)) := by rw [hhar]; ring
    _ ≤ Real.log 4 * (1 + (1 + Real.log Y)) :=
      mul_le_mul_of_nonneg_left (by
        dsimp [n]
        linarith [harmonic_floor_le_one_add_log Y hY]) hK
    _ ≤ _ := by nlinarith [mul_nonneg hK (Real.log_nonneg hY)]

/-- Uniform logarithmic Gaussian-prime weight, with an absolute explicit
constant. No congruence-class prime theorem is used. -/
theorem primeClassesY_weight_le {Y : ℝ} (hY : 1 ≤ Y) :
    (∑ a ∈ primeClassesY Y, Real.log (classNorm a) / classNorm a) ≤
      (20 * Real.log 4) * (1 + Real.log Y) := by
  change (∑ a ∈ primeClassesY Y, weight a) ≤ _
  calc
    _ ≤ ∑ a ∈ (Nat.primesLE ⌊Y⌋₊).biUnion rationalPrimeCover, weight a :=
      sum_le_sum_of_subset_of_nonneg (primeClassesY_subset_cover (zero_le_one.trans hY))
        (fun a _ _ => weight_nonneg a)
    _ ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, ∑ a ∈ rationalPrimeCover p, weight a :=
      weight_biUnion_le _
    _ ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, 10 * (Real.log p / p) :=
      sum_le_sum (fun p hp => rationalPrimeCover_weight_le (Nat.mem_primesLE.mp hp).2)
    _ = 10 * ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log p / p := by rw [mul_sum]
    _ ≤ 10 * ((2 * Real.log 4) * (1 + Real.log Y)) :=
      mul_le_mul_of_nonneg_left (rationalPrime_weight_le hY) (by norm_num)
    _ = _ := by ring


end DistanceCounts.GaussianPrimeWeight
end
end

-- Source: DistanceCounts/GaussianMassGrowth.lean
section
/-! Logarithmic mass growth for the actual nonzero Gaussian associate classes. -/

namespace DistanceCounts.GaussianMass

open Finset UniqueFactorizationMonoid
open scoped Classical

lemma reciprocalMass_nonneg (D : ℝ) : 0 ≤ reciprocalMass D := by
  exact sum_nonneg fun _ _ => by positivity

lemma reciprocalMass_mono {D E : ℝ} (hD : 0 ≤ D) (hDE : D ≤ E) :
    reciprocalMass D ≤ reciprocalMass E := by
  exact sum_le_sum_of_subset_of_nonneg (classBall_mono hD hDE)
    (fun _ _ _ => by positivity)

lemma reciprocalMass_double {D : ℝ} (hD : 10000 ≤ D) :
    reciprocalMass D + 1 / 4 ≤ reciprocalMass (2 * D) := by
  have hD0 : 0 ≤ D := by linarith
  have hs : 100 ≤ Real.sqrt D :=
    (Real.le_sqrt (by norm_num) hD0).mpr (by norm_num; exact hD)
  have hs2 : Real.sqrt (2 * D) ≤ 2 * Real.sqrt D := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hD0]
  have herr : (Real.pi + 1) * (Real.sqrt (2 * D) + Real.sqrt D + 2) ≤
      20 * Real.sqrt D := by
    calc
      _ ≤ 5 * (3 * Real.sqrt D + 2) := by
        gcongr
        · linarith [Real.pi_lt_four]
        · linarith
      _ ≤ _ := by nlinarith
  have hmain : D / 2 ≤ (Real.pi / 4) * (2 * D - D) -
      (Real.pi + 1) * (Real.sqrt (2 * D) + Real.sqrt D + 2) := by
    have hpi : 3 * D ≤ Real.pi * D :=
      mul_le_mul_of_nonneg_right (le_of_lt Real.pi_gt_three) hD0
    have hsq : 80 * Real.sqrt D ≤ D := by
      nlinarith [Real.sq_sqrt hD0, mul_nonneg (by linarith : 0 ≤ Real.sqrt D)
        (by linarith : 0 ≤ Real.sqrt D - 80)]
    nlinarith
  have hann : (1 / 4 : ℝ) ≤
      ∑ a ∈ classBall (2 * D) \ classBall D, 1 / (classNorm a : ℝ) := by
    have hpos : 0 < 2 * D := by linarith
    have h := annulus_reciprocal_lower hD0 (by linarith : D ≤ 2 * D) hpos
    exact (by
      apply (le_div_iff₀ hpos).mpr
      nlinarith : (1 / 4 : ℝ) ≤
        ((Real.pi / 4) * (2 * D - D) -
          (Real.pi + 1) * (Real.sqrt (2 * D) + Real.sqrt D + 2)) / (2 * D)).trans h
  have heq := sum_sdiff (f := fun a => 1 / (classNorm a : ℝ))
    (classBall_mono hD0 (show D ≤ 2 * D by linarith))
  change (∑ a ∈ classBall D, 1 / (classNorm a : ℝ)) + 1 / 4 ≤
    ∑ a ∈ classBall (2 * D), 1 / (classNorm a : ℝ)
  linarith

lemma reciprocalMass_dyadic (n : ℕ) :
    (n : ℝ) / 4 ≤ reciprocalMass (10000 * (2 : ℝ) ^ n) := by
  induction n with
  | zero => simpa using reciprocalMass_nonneg 10000
  | succ n ih =>
    have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hd := reciprocalMass_double (D := 10000 * (2 : ℝ) ^ n) (by nlinarith)
    have heq : 2 * (10000 * (2 : ℝ) ^ n) = 10000 * 2 ^ (n + 1) := by ring
    rw [heq] at hd
    push_cast
    linarith

lemma reciprocalMass_log_lower {D : ℝ} (hD : 10000 ≤ D) :
    (Real.log (D / 10000) / Real.log 2 - 1) / 4 ≤ reciprocalMass D := by
  have hDpos : 0 < D := by linarith
  have hratio : 1 ≤ D / 10000 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let n := ⌊Real.log (D / 10000) / Real.log 2⌋₊
  have hn : (n : ℝ) ≤ Real.log (D / 10000) / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hratio) hlog2.le)
  have hn' : Real.log (D / 10000) / Real.log 2 < (n : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hpow : (2 : ℝ) ^ n ≤ D / 10000 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hlog2).mp hn
  have hcut : 10000 * (2 : ℝ) ^ n ≤ D := by linarith
  have hm := (reciprocalMass_dyadic n).trans
    (reciprocalMass_mono (by positivity) hcut)
  linarith

/-- A uniform positive logarithmic lower bound, with explicit finite cutoff. -/
theorem reciprocalMass_log_growth :
    ∃ c D₀ : ℝ, 0 < c ∧ 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      c * Real.log D ≤ reciprocalMass D := by
  refine ⟨1 / (8 * Real.log 2), (20000 : ℝ) ^ 2, by positivity, by positivity, ?_⟩
  intro D hD
  have hDlarge : 10000 ≤ D := by nlinarith
  have hDpos : 0 < D := by nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs : 2 * Real.log 20000 ≤ Real.log D := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 20000 ^ 2) hD
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have h20000 : Real.log (20000 : ℝ) = Real.log 10000 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (10000 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hbound := reciprocalMass_log_lower hDlarge
  rw [Real.log_div hDpos.ne' (by norm_num : (10000 : ℝ) ≠ 0)] at hbound
  have halg : 1 / (8 * Real.log 2) * Real.log D ≤
      ((Real.log D - Real.log 10000) / Real.log 2 - 1) / 4 := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < 8 * Real.log 2 by positivity)).mp
    field_simp
    nlinarith
  exact halg.trans hbound

lemma factors_reconstruct {a : Associates GaussianInt} (ha : a ≠ 0) :
    (∏ p ∈ primeSupport a, p ^ (normalizedFactors a).count p) = a := by
  rw [primeSupport, ← Finset.prod_multiset_count]
  exact associated_iff_eq.mp (prod_normalizedFactors ha)

lemma support_prod_dvd {a : Associates GaussianInt} (ha : a ≠ 0) :
    (∏ p ∈ primeSupport a, p) ∣ a := by
  conv_rhs => rw [← factors_reconstruct ha]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have hcount : 0 < (normalizedFactors a).count p :=
    Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcount)
  rw [hk, pow_succ]
  exact dvd_mul_left p (p ^ k)

lemma support_prod_mem_squarefreeBall {D : ℝ} (hD : 0 ≤ D)
    {a : Associates GaussianInt} (ha : a ∈ classBall D) :
    (∏ p ∈ primeSupport a, p) ∈ squarefreeBall D := by
  obtain ⟨ha0, haD⟩ := (mem_classBall hD a).mp ha
  apply (mem_squarefreeBall hD _).mpr
  constructor
  · exact squarefree_prime_prod _ (fun _ hp => prime_of_mem_primeSupport hp)
  · have hn := classNorm_le_of_dvd ha0 (support_prod_dvd ha0)
    exact (by exact_mod_cast hn :
      (classNorm (∏ p ∈ primeSupport a, p) : ℝ) ≤ classNorm a).trans haD

lemma shifted_geometric_sum_le {x : ℝ} (hx : 1 < x) (M : ℕ) :
   (∑ k : Fin M, (1 / x) ^ (k.val + 1)) ≤ 1 / (x - 1) := by
 have hx0 : 0 < x := by linarith
 have hr : 0 ≤ 1 / x := by positivity
 have hr1 : 1 / x < 1 := (div_lt_one hx0).mpr hx
 have hg := hasSum_geometric_of_lt_one hr hr1
 have hs : (∑ k ∈ range M, (1 / x) ^ k) ≤ (1 - 1 / x)⁻¹ :=
   (hg.summable.sum_le_tsum (range M) (fun _ _ => pow_nonneg hr _)).trans_eq hg.tsum_eq
 rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 / x) ^ (k + 1)) M]
 calc
   (∑ k ∈ range M, (1 / x) ^ (k + 1)) =
       (1 / x) * ∑ k ∈ range M, (1 / x) ^ k := by
     rw [mul_sum]
     exact sum_congr rfl (fun _ _ => pow_succ' _ _)
   _ ≤ (1 / x) * (1 - 1 / x)⁻¹ := mul_le_mul_of_nonneg_left hs hr
   _ = 1 / (x - 1) := by
     have hx1 : x - 1 ≠ 0 := by linarith
     have hr0 : 1 - 1 / x ≠ 0 := by linarith
     field_simp

/-- Grouping integers by their radical, then summing each finite exponent box,
is bounded by the exact geometric Euler weight of that radical. -/
lemma support_fiber_mass_le {D : ℝ} (hD : 0 ≤ D)
   (S : Finset (Associates GaussianInt)) (hS : ∀ p ∈ S, Prime p) :
   (∑ a ∈ (classBall D).filter (fun a => primeSupport a = S),
     1 / (classNorm a : ℝ)) ≤ 1 / ∏ p ∈ S, ((classNorm p : ℝ) - 1) := by
 let F := (classBall D).filter (fun a => primeSupport a = S)
 let M := F.sup (fun a => (normalizedFactors a).card) + 1
 let code (a : F) (p : S) : Fin M :=
   ⟨(normalizedFactors a.val).count p.val - 1, by
     have hc := Multiset.count_le_card p.val (normalizedFactors a.val)
     have hs := Finset.le_sup (f := fun a => (normalizedFactors a).card) a.property
     dsimp [M]
     omega⟩
 have ha0 (a : F) : a.val ≠ 0 :=
   ((mem_classBall hD a.val).mp (mem_filter.mp a.property).1).1
 have hsupport (a : F) : primeSupport a.val = S :=
   (mem_filter.mp a.property).2
 have hexp (a : F) (p : S) :
     (code a p).val + 1 = (normalizedFactors a.val).count p.val := by
   have hp : p.val ∈ primeSupport a.val := (hsupport a).symm ▸ p.property
   have hc : 0 < (normalizedFactors a.val).count p.val :=
     Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
   dsimp [code]
   omega
 have hreconstruct (a : F) :
     (∏ p : S, p.val ^ ((code a p).val + 1)) = a.val := by
   simp_rw [hexp a]
   rw [Finset.prod_coe_sort S (fun p => p ^ (normalizedFactors a.val).count p)]
   simpa only [hsupport a] using factors_reconstruct (ha0 a)
 have hinj : Function.Injective code := by
   intro a b hab
   apply Subtype.ext
   rw [← hreconstruct a, ← hreconstruct b, hab]
 let weight (f : S → Fin M) : ℝ :=
   ∏ p : S, (1 / (classNorm p.val : ℝ)) ^ ((f p).val + 1)
 have hweight (a : F) : 1 / (classNorm a.val : ℝ) = weight (code a) := by
   let N : Associates GaussianInt →* ℕ :=
      { toFun := classNorm
        map_one' := classNorm_one
        map_mul' := classNorm_mul }
   have hn : classNorm a.val =
       ∏ p : S, classNorm p.val ^ ((code a p).val + 1) := by
     change N a.val = ∏ p : S, N p.val ^ ((code a p).val + 1)
     simpa only [map_prod, map_pow] using congrArg N (hreconstruct a).symm
   have hnr : (classNorm a.val : ℝ) =
       ∏ p : S, (classNorm p.val : ℝ) ^ ((code a p).val + 1) := by
     exact_mod_cast hn
   rw [hnr]
   simp only [weight, one_div, inv_pow, ← Finset.prod_inv_distrib]
 change (∑ a ∈ F, 1 / (classNorm a : ℝ)) ≤ _
 calc
   (∑ a ∈ F, 1 / (classNorm a : ℝ)) = ∑ a : F, weight (code a) := by
     rw [← Finset.sum_coe_sort F (fun a => 1 / (classNorm a : ℝ))]
     exact sum_congr rfl fun a _ => hweight a
   _ = ∑ f ∈ (univ : Finset F).image code, weight f :=
     (sum_image (fun _ _ _ _ h => hinj h)).symm
   _ ≤ ∑ f : S → Fin M, weight f :=
     sum_le_univ_sum_of_nonneg (fun f => prod_nonneg (fun _ _ => by positivity))
   _ = ∏ p : S, ∑ k : Fin M, (1 / (classNorm p.val : ℝ)) ^ (k.val + 1) :=
     (Fintype.prod_sum (fun (p : S) (k : Fin M) =>
       (1 / (classNorm p.val : ℝ)) ^ (k.val + 1))).symm
   _ ≤ ∏ p : S, 1 / ((classNorm p.val : ℝ) - 1) := by
     apply prod_le_prod
     · intro p _
       exact sum_nonneg fun _ _ => by positivity
     · intro p _
       apply shifted_geometric_sum_le
       have hp := classNorm_prime_two_le (hS p.val p.property)
       have hp' : (2 : ℝ) ≤ classNorm p.val := by exact_mod_cast hp
       linarith
   _ = 1 / ∏ p ∈ S, ((classNorm p : ℝ) - 1) := by
      simp only [one_div, Finset.prod_inv_distrib]
      rw [Finset.prod_coe_sort S (fun p => (classNorm p : ℝ) - 1)]

/-- The finite Euler product comparison is stronger than the squarefree-times-
square comparison: no reciprocal-square summability constant is needed. -/
theorem reciprocalMass_le_squarefreeMass {D : ℝ} (hD : 0 ≤ D) :
   reciprocalMass D ≤ squarefreeMass D := by
 have hmap : ∀ a ∈ classBall D,
     primeSupport a ∈ (squarefreeBall D).image primeSupport := by
   intro a ha
   refine mem_image.mpr ⟨∏ p ∈ primeSupport a, p,
     support_prod_mem_squarefreeBall hD ha, ?_⟩
   exact primeSupport_prime_prod _ (fun _ hp => prime_of_mem_primeSupport hp)
 calc
   reciprocalMass D =
       ∑ S ∈ (squarefreeBall D).image primeSupport,
         ∑ a ∈ (classBall D).filter (fun a => primeSupport a = S),
           1 / (classNorm a : ℝ) :=
     (sum_fiberwise_of_maps_to hmap _).symm
   _ ≤ ∑ S ∈ (squarefreeBall D).image primeSupport,
       1 / ∏ p ∈ S, ((classNorm p : ℝ) - 1) := by
     apply sum_le_sum
     intro S hS
     obtain ⟨a, ha, rfl⟩ := mem_image.mp hS
     exact support_fiber_mass_le hD _ (fun _ hp => prime_of_mem_primeSupport hp)
   _ = squarefreeMass D := by
     rw [sum_image]
     · rfl
     · intro a ha b hb heq
       exact primeSupport_injective_squarefree (mem_filter.mp ha).2
         (mem_filter.mp hb).2 heq

/-- The Selberg denominator grows logarithmically for genuine Gaussian classes. -/
theorem squarefreeMass_log_growth :
   ∃ c D₀ : ℝ, 0 < c ∧ 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
     c * Real.log D ≤ squarefreeMass D := by
 obtain ⟨c, D₀, hc, hD₀, h⟩ := reciprocalMass_log_growth
 exact ⟨c, D₀, hc, hD₀, fun D hD =>
   (h D hD).trans (reciprocalMass_le_squarefreeMass (hD₀.le.trans hD))⟩

end DistanceCounts.GaussianMass
end

-- Source: DistanceCounts/GaussianSmoothPart.lean
section
/-! The actual Gaussian small-prime factor, its first moment, and the original
manuscript cutoffs. All populations consist of nonzero Gaussian vectors. -/

noncomputable section

namespace DistanceCounts.GaussianSmoothPart

open Finset Filter GaussianMass GaussianPrimeWeight
open scoped Classical Topology

/-- The finite multiplicity in the unique factorization of the actual class. -/
def valuation (p : Associates GaussianInt) (z : GaussianInt) : ℕ :=
  p.count (Associates.mk z).factors

/-- Both split conjugate classes and the ramified class retain their actual
multiplicities; this is a factor of `Associates.mk z`, not a norm surrogate. -/
def smallPartY (Y : ℝ) (z : GaussianInt) : Associates GaussianInt :=
  ∏ p ∈ primeClassesY Y, p ^ valuation p z

private def normHom : Associates GaussianInt →* ℕ where
  toFun := classNorm
  map_one' := classNorm_one
  map_mul' := classNorm_mul

lemma classNorm_pow (a : Associates GaussianInt) (k : ℕ) :
    classNorm (a ^ k) = classNorm a ^ k := normHom.map_pow a k

lemma prime_of_mem {Y : ℝ} {p : Associates GaussianInt}
    (hp : p ∈ primeClassesY Y) : Prime p := (mem_filter.mp hp).2

lemma smallPartY_ne_zero (Y : ℝ) (z : GaussianInt) : smallPartY Y z ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (prime_of_mem hp).ne_zero

lemma log_smallPartY_nonneg (Y : ℝ) (z : GaussianInt) :
    0 ≤ Real.log (classNorm (smallPartY Y z)) := by
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    ((classNorm_eq_zero _).not.mpr (smallPartY_ne_zero Y z))

/-- The logarithm of the genuine product is exactly the weighted valuation sum. -/
theorem log_smallPartY (Y : ℝ) (z : GaussianInt) :
    Real.log (classNorm (smallPartY Y z)) =
      ∑ p ∈ primeClassesY Y, (valuation p z : ℝ) * Real.log (classNorm p) := by
  have hn : classNorm (smallPartY Y z) =
      ∏ p ∈ primeClassesY Y, classNorm p ^ valuation p z := by
    change normHom (∏ p ∈ primeClassesY Y, p ^ valuation p z) =
      ∏ p ∈ primeClassesY Y, normHom p ^ valuation p z
    simp only [map_prod, map_pow]
  rw [hn, Nat.cast_prod, Real.log_prod]
  · apply sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    rw [Nat.cast_pow]
    exact pow_ne_zero _ (by exact_mod_cast
      (ne_of_gt ((classNorm_pos p).mpr (prime_of_mem hp).ne_zero)))

lemma pow_dvd_iff_le_valuation {p : Associates GaussianInt} (hp : Prime p)
    {z : GaussianInt} (hz : z ≠ 0) (k : ℕ) :
    p ^ k ∣ Associates.mk z ↔ k ≤ valuation p z := by
  exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hz) hp.irreducible

/-- Exact finite layer cake, with any upper bound on the actual multiplicity. -/
lemma valuation_layer_cake {p : Associates GaussianInt} (hp : Prime p)
    {z : GaussianInt} (hz : z ≠ 0) {M : ℕ} (hM : valuation p z ≤ M) :
    (valuation p z : ℝ) =
      ∑ k ∈ range M, if p ^ (k + 1) ∣ Associates.mk z then (1 : ℝ) else 0 := by
  simp_rw [pow_dvd_iff_le_valuation hp hz]
  have he : (range M).filter (fun k => k + 1 ≤ valuation p z) =
      range (valuation p z) := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  rw [← sum_filter, he]
  simp

/-- Transfer an actual associate divisor back to its Gaussian ideal lattice. -/
lemma divisor_population_le {a : Associates GaussianInt} (ha : a ≠ 0)
    {R : ℝ} (hR : 0 ≤ R) :
    (((representatives (R ^ 2)).filter (fun z => a ∣ Associates.mk z)).card : ℝ) ≤
      9 * Real.pi * R ^ 2 / classNorm a := by
  obtain ⟨d, rfl⟩ := Associates.mk_surjective a
  have hd : d ≠ 0 := Associates.mk_ne_zero.mp ha
  have he : (representatives (R ^ 2)).filter (fun z => Associates.mk d ∣ Associates.mk z) =
      (GaussianDivisibility.divisorDisk d R).erase 0 := by
    ext z
    simp only [representatives, Real.sqrt_sq hR, mem_filter, mem_erase,
      mem_gaussianDisk, GaussianDivisibility.mem_divisorDisk, Associates.mk_dvd_mk]
    tauto
  rw [he]
  exact GaussianDivisibility.divisorDisk_erase_zero_card_upper d hd hR

/-- Sum of the multiplicity of one genuine Gaussian prime over the disk. The
finite layer cake needs no truncation hypothesis on its prime powers. -/
theorem valuation_sum_le {p : Associates GaussianInt} (hp : Prime p)
    {R : ℝ} (hR : 0 ≤ R) :
    (∑ z ∈ representatives (R ^ 2), (valuation p z : ℝ)) ≤
      (18 * Real.pi) * R ^ 2 / classNorm p := by
  let A := representatives (R ^ 2)
  let M := A.sup (valuation p)
  have hN : (2 : ℝ) ≤ classNorm p := by exact_mod_cast classNorm_prime_two_le hp
  have hN0 : (0 : ℝ) < classNorm p := by linarith
  have hgeom : (∑ k ∈ range M, (1 / (classNorm p : ℝ)) ^ (k + 1)) ≤
      2 / classNorm p := by
    have hg := shifted_geometric_sum_le (x := (classNorm p : ℝ)) (by linarith) M
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (1 / (classNorm p : ℝ)) ^ (k + 1)) M] at hg
    apply hg.trans
    apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < classNorm p - 1) hN0).mpr
    linarith
  calc
    (∑ z ∈ A, (valuation p z : ℝ)) =
        ∑ z ∈ A, ∑ k ∈ range M,
          if p ^ (k + 1) ∣ Associates.mk z then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro z hz
      exact valuation_layer_cake hp ((mem_representatives (sq_nonneg R) z).mp hz).1
        (Finset.le_sup (f := valuation p) hz)
    _ = ∑ k ∈ range M,
        (((representatives (R ^ 2)).filter (fun z => p ^ (k + 1) ∣ Associates.mk z)).card : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one, A]
    _ ≤ ∑ k ∈ range M, 9 * Real.pi * R ^ 2 / (classNorm p : ℝ) ^ (k + 1) := by
      apply sum_le_sum
      intro k _
      simpa only [classNorm_pow, Nat.cast_pow] using
        divisor_population_le (pow_ne_zero (k + 1) hp.ne_zero) hR
    _ = (9 * Real.pi * R ^ 2) *
        ∑ k ∈ range M, (1 / (classNorm p : ℝ)) ^ (k + 1) := by
      simp only [mul_sum, div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow]
    _ ≤ (9 * Real.pi * R ^ 2) * (2 / classNorm p) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

/-- Absolute first moment at every real radius, using the proved prime weight
bound rather than a smoothness or independence assumption. -/
theorem log_smallPartY_sum_le {R Y : ℝ} (hR : 0 ≤ R) (hY : 1 ≤ Y) :
    (∑ z ∈ representatives (R ^ 2), Real.log (classNorm (smallPartY Y z))) ≤
      (360 * Real.pi * Real.log 4) * R ^ 2 * (1 + Real.log Y) := by
  simp_rw [log_smallPartY]
  rw [sum_comm]
  calc
    _ = ∑ p ∈ primeClassesY Y,
        (∑ z ∈ representatives (R ^ 2), (valuation p z : ℝ)) * Real.log (classNorm p) := by
      simp only [sum_mul]
    _ ≤ ∑ p ∈ primeClassesY Y,
        ((18 * Real.pi) * R ^ 2 / classNorm p) * Real.log (classNorm p) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right (valuation_sum_le (prime_of_mem hp) hR)
      apply Real.log_nonneg
      exact_mod_cast (le_trans (by decide : 1 ≤ 2)
        (classNorm_prime_two_le (prime_of_mem hp)))
    _ = ((18 * Real.pi) * R ^ 2) *
        ∑ p ∈ primeClassesY Y, Real.log (classNorm p) / classNorm p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ((18 * Real.pi) * R ^ 2) * ((20 * Real.log 4) * (1 + Real.log Y)) :=
      mul_le_mul_of_nonneg_left (primeClassesY_weight_le hY) (by positivity)
    _ = _ := by ring


/-- Vectors whose genuine small-prime factor is larger than `S`. -/
def exceptional (R Y S : ℝ) : Finset GaussianInt :=
  (representatives (R ^ 2)).filter (fun z => S < (classNorm (smallPartY Y z) : ℝ))

/-- Deterministic Markov inequality, before specializing either cutoff. -/
theorem exceptional_card_le {R Y S : ℝ} (hR : 0 ≤ R) (hY : 1 ≤ Y) (hS : 1 < S) :
    ((exceptional R Y S).card : ℝ) ≤
      (360 * Real.pi * Real.log 4) * R ^ 2 * (1 + Real.log Y) / Real.log S := by
  apply (le_div_iff₀ (Real.log_pos hS)).mpr
  calc
    _ = ∑ _z ∈ exceptional R Y S, Real.log S := by simp
    _ ≤ ∑ z ∈ exceptional R Y S, Real.log (classNorm (smallPartY Y z)) := by
      apply sum_le_sum
      intro z hz
      exact (Real.log_lt_log (zero_lt_one.trans hS) (mem_filter.mp hz).2).le
    _ ≤ ∑ z ∈ representatives (R ^ 2), Real.log (classNorm (smallPartY Y z)) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun z _ _ => log_smallPartY_nonneg Y z)
    _ ≤ _ := log_smallPartY_sum_le hR hY

/-- The manuscript's original small-prime scale, without changing its exponent. -/
def manuscriptY (R κ : ℝ) : ℝ := Real.exp ((Real.log R) ^ κ)

/-- The manuscript's original smooth-part cutoff. -/
def manuscriptS (R κ : ℝ) : ℝ := Real.exp ((Real.log R) ^ (2 * κ))

/-- Vanishing exceptional density through all real radii, at exactly
`Y = exp((log R)^κ)` and `S = exp((log R)^(2κ))`. -/
theorem tendsto_exceptional_card {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun R : ℝ =>
      ((exceptional R (manuscriptY R κ) (manuscriptS R κ)).card : ℝ) / R ^ 2)
      atTop (𝓝 0) := by
  let C : ℝ := 360 * Real.pi * Real.log 4
  let t : ℝ → ℝ := fun R => (Real.log R) ^ κ
  have ht : Tendsto t atTop atTop := (tendsto_rpow_atTop hκ).comp Real.tendsto_log_atTop
  have hi : Tendsto (fun R => (t R)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ht
  have hb : Tendsto (fun R => C * ((t R)⁻¹ ^ 2 + (t R)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((hi.pow 2).add hi).const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Eventually.of_forall fun R => div_nonneg (Nat.cast_nonneg _) (sq_nonneg R)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := zero_lt_one.trans hR
    have hl : 0 < Real.log R := Real.log_pos hR
    have ht0 : 0 < t R := Real.rpow_pos_of_pos hl κ
    have hY : 1 ≤ manuscriptY R κ := Real.one_le_exp_iff.mpr ht0.le
    have hpower : (Real.log R) ^ (2 * κ) = (t R) ^ 2 := by
      rw [mul_comm (2 : ℝ) κ, Real.rpow_mul hl.le, Real.rpow_two]
    have hS : 1 < manuscriptS R κ := by
      apply Real.one_lt_exp_iff.mpr
      exact Real.rpow_pos_of_pos hl _
    have hc := exceptional_card_le hR0.le hY hS
    have hlogY : Real.log (manuscriptY R κ) = t R := Real.log_exp _
    have hlogS : Real.log (manuscriptS R κ) = (t R) ^ 2 := by
      rw [manuscriptS, Real.log_exp, hpower]
    rw [hlogY, hlogS] at hc
    calc
      _ ≤ (C * R ^ 2 * (1 + t R) / (t R) ^ 2) / R ^ 2 :=
        div_le_div_of_nonneg_right hc (sq_nonneg R)
      _ = C * ((t R)⁻¹ ^ 2 + (t R)⁻¹) := by
        field_simp [ne_of_gt hR0, ne_of_gt ht0]
        <;> ring

end DistanceCounts.GaussianSmoothPart
end
end

-- Source: DistanceCounts/SmallFlipLattice.lean
section
/-! Finite reciprocal estimates for the four small-flip lattice directions. -/

noncomputable section

namespace DistanceCounts.SmallFlipLattice

open GaussianDivisibility

private lemma sum_le_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (g : β → α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (h : A ⊆ B.image g) :
    ∑ x ∈ A, f x ≤ ∑ y ∈ B, f (g y) := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => hf x)).trans
    (Finset.sum_image_le_of_nonneg (fun x _ => hf x))

private lemma sum_biUnion_upper {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (A : α → Finset β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ I.biUnion A, f x ≤ ∑ i ∈ I, ∑ x ∈ A i, f x := by
  classical
  have h := sum_le_cover (I.biUnion A) (I.sigma A)
    (fun p => p.2) f hf (by
      intro x hx
      obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_image.mpr ⟨⟨i, x⟩, Finset.mem_sigma.mpr ⟨hi, hx⟩, rfl⟩)
  simpa only [Finset.sum_sigma] using h

/-- A telescoping majorant, valid even at the origin of the longitudinal axis. -/
lemma reciprocal_quadratic_majorant {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) :
    1 / (a ^ 2 + b ^ 2) ≤ 4 * (1 / (a + b) - 1 / (a + b + 1)) := by
  have hb0 : 0 < b := by linarith
  have hab : 0 < a + b := by positivity
  have hab1 : 0 < a + b + 1 := by positivity
  have hd : 0 < a ^ 2 + b ^ 2 := by positivity
  have hpoly : (a + b) * (a + b + 1) ≤ 4 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b),
      mul_nonneg hab.le (by linarith : 0 ≤ a + b - 1)]
  have he : 4 * (1 / (a + b) - 1 / (a + b + 1)) =
      4 / ((a + b) * (a + b + 1)) := by
    field_simp [ne_of_gt hab, ne_of_gt hab1] <;> ring
  rw [he]
  exact (div_le_div_iff₀ hd (mul_pos hab hab1)).mpr (by simpa using hpoly)

private lemma sum_reciprocal_quadratic_nat (M : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    ∑ a ∈ Finset.range M, 1 / ((a : ℝ) ^ 2 + b ^ 2) ≤ 4 / b := by
  have ht : ∑ a ∈ Finset.range M,
      (1 / ((a : ℝ) + b) - 1 / ((a : ℝ) + b + 1)) =
      1 / b - 1 / ((M : ℝ) + b) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  calc
    _ ≤ ∑ a ∈ Finset.range M,
        4 * (1 / ((a : ℝ) + b) - 1 / ((a : ℝ) + b + 1)) :=
      Finset.sum_le_sum (fun a _ => reciprocal_quadratic_majorant (Nat.cast_nonneg a) hb)
    _ = 4 * (1 / b - 1 / ((M : ℝ) + b)) := by rw [← Finset.mul_sum, ht]
    _ ≤ 4 / b := by
      have : 0 ≤ 1 / ((M : ℝ) + b) := by positivity
      simp only [div_eq_mul_inv, one_mul] at *
      linarith

private def signed (e : Bool) (n : ℕ) : ℤ := if e then n else -(n : ℤ)

private lemma exists_signed (z : ℤ) : ∃ e, signed e z.natAbs = z := by
  by_cases hz : 0 ≤ z
  · exact ⟨true, by simpa [signed, Int.natCast_natAbs, abs_of_nonneg hz]⟩
  · exact ⟨false, by simp [signed, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hz)]⟩

private lemma signed_sq (e : Bool) (n : ℕ) : ((signed e n : ℤ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
  cases e <;> simp [signed]

private def integerRange (M : ℕ) : Finset ℤ :=
  ((Finset.univ : Finset Bool) ×ˢ Finset.range (M + 1)).image (fun p => signed p.1 p.2)

private lemma mem_integerRange {M : ℕ} {z : ℤ} (hz : z.natAbs ≤ M) :
    z ∈ integerRange M := by
  obtain ⟨e, he⟩ := exists_signed z
  exact Finset.mem_image.mpr ⟨(e, z.natAbs),
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩, he⟩

/-- The finite lattice-line bound. The longitudinal interval may be arbitrarily long. -/
lemma integer_line_reciprocal_upper (M : ℕ) {b : ℤ} (hb : b ≠ 0) :
    ∑ a ∈ integerRange M, 1 / ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ≤
      8 / (b.natAbs : ℝ) := by
  have hb1 : (1 : ℝ) ≤ b.natAbs := by
    exact_mod_cast Nat.succ_le_of_lt (Int.natAbs_pos.mpr hb)
  have hbsq : (b : ℝ) ^ 2 = (b.natAbs : ℝ) ^ 2 := by
    have h : (b.natAbs : ℤ) ^ 2 = b ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
    simpa only [Int.cast_pow, Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ℝ)) h.symm
  have h := sum_le_cover (integerRange M)
    ((Finset.univ : Finset Bool) ×ˢ Finset.range (M + 1))
    (fun p => signed p.1 p.2)
    (fun a => 1 / ((a : ℝ) ^ 2 + (b : ℝ) ^ 2))
    (fun a => by positivity) (by intro x hx; exact hx)
  simp only [Finset.sum_product, signed_sq, hbsq] at h
  have hs := sum_reciprocal_quadratic_nat (M + 1) hb1
  simpa only [hbsq] using h.trans (show
    (∑ e : Bool, ∑ a ∈ Finset.range (M + 1),
      1 / ((a : ℝ) ^ 2 + (b.natAbs : ℝ) ^ 2)) ≤ 8 / (b.natAbs : ℝ) by
        simp only [Fintype.sum_bool]
        linarith [show (8 : ℝ) / b.natAbs = 2 * (4 / b.natAbs) by ring])

private def multiples (q K : ℕ) : Finset ℤ :=
  ((Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K).image (fun p => signed p.1 (q * p.2))

private lemma mem_multiples {q K : ℕ} (hq : 1 ≤ q) {b : ℤ}
    (hb : b ≠ 0) (hqb : (q : ℤ) ∣ b) (hK : b.natAbs ≤ K) : b ∈ multiples q K := by
  obtain ⟨k, hk⟩ := hqb
  have hk0 : k ≠ 0 := by intro h; simp [h] at hk; exact hb hk
  have ha : b.natAbs = q * k.natAbs := by rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
  have hkK : k.natAbs ≤ K := by
    calc k.natAbs = 1 * k.natAbs := by simp
         _ ≤ q * k.natAbs := Nat.mul_le_mul_right _ hq
         _ ≤ K := ha ▸ hK
  obtain ⟨e, he⟩ := exists_signed b
  apply Finset.mem_image.mpr
  refine ⟨(e, k.natAbs), Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr hk0, hkK⟩⟩, ?_⟩
  simpa only [← ha] using he

/-- A finite rectangular enlargement of the nonzero transverse multiples. -/
lemma reciprocal_rectangle_upper (q M K : ℕ) (hq : 1 ≤ q) :
    ∑ p ∈ integerRange M ×ˢ multiples q K,
      1 / ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤
      16 / (q : ℝ) * (harmonic K : ℝ) := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Finset.sum_product, Finset.sum_comm]
  calc
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K,
        ∑ a ∈ integerRange M, 1 / ((a : ℝ) ^ 2 + (signed p.1 (q * p.2) : ℝ) ^ 2) := by
      apply sum_le_cover _ _ _ _ (fun b => Finset.sum_nonneg (fun a _ => by positivity))
      intro b hb
      exact hb
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.Icc 1 K,
        8 / ((q : ℝ) * (p.2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hk := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).1
      have hn : signed p.1 (q * p.2) ≠ 0 := by
        cases h : p.1 <;> simp [signed, h, Nat.ne_of_gt (show 0 < q by omega),
          Nat.ne_of_gt (show 0 < p.2 by omega)]
      have hs := integer_line_reciprocal_upper M hn
      cases he : p.1 <;> simpa [signed, he, Nat.cast_mul] using hs
    _ = 16 / (q : ℝ) * (harmonic K : ℝ) := by
      simp only [Finset.sum_product, Fintype.sum_bool]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      simp_rw [div_mul_eq_div_mul_one_div, one_div]
      simp only [← Finset.mul_sum]
      ring

/-- Longitudinal and transverse coordinates for the horizontal, vertical,
and the two diagonal directions, respectively. -/
def coordinates (i : Fin 4) (z : GaussianInt) : ℤ × ℤ :=
  ![(z.re, z.im), (z.im, z.re), (z.re + z.im, z.re - z.im),
    (z.re - z.im, z.re + z.im)] i

/-- Actual vectors; in particular the transverse coordinate zero is excluded. -/
def directionVectors (i : Fin 4) (q : ℕ) (S : ℝ) : Finset GaussianInt := by
  classical
  exact ((gaussianDisk 0 (Real.sqrt S)).erase 0).filter
    (fun z => (q : ℤ) ∣ (coordinates i z).2 ∧ (coordinates i z).2 ≠ 0)

/-- The union of all four genuine small-flip directions. -/
def smallFlipVectors (q : ℕ) (S : ℝ) : Finset GaussianInt := by
  classical
  exact Finset.univ.biUnion (fun i : Fin 4 => directionVectors i q S)

lemma mem_directionVectors (i : Fin 4) (q : ℕ) (S : ℝ) (z : GaussianInt) :
    z ∈ directionVectors i q S ↔ z ≠ 0 ∧ ‖(z : ℂ)‖ ≤ Real.sqrt S ∧
      (q : ℤ) ∣ (coordinates i z).2 ∧ (coordinates i z).2 ≠ 0 := by
  classical
  simp [directionVectors, mem_gaussianDisk, and_assoc]

lemma mem_smallFlipVectors (q : ℕ) (S : ℝ) (z : GaussianInt) :
    z ∈ smallFlipVectors q S ↔ z ≠ 0 ∧ ‖(z : ℂ)‖ ≤ Real.sqrt S ∧
      (((q : ℤ) ∣ z.im ∧ z.im ≠ 0) ∨ ((q : ℤ) ∣ z.re ∧ z.re ≠ 0) ∨
        ((q : ℤ) ∣ z.re - z.im ∧ z.re - z.im ≠ 0) ∨
        ((q : ℤ) ∣ z.re + z.im ∧ z.re + z.im ≠ 0)) := by
  classical
  simp only [smallFlipVectors, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_directionVectors]
  simp [Fin.exists_fin_succ, coordinates, and_or_left, and_assoc]

private lemma coordinates_injective (i : Fin 4) : Function.Injective (coordinates i) := by
  intro z w h
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  apply Zsqrtd.ext <;> fin_cases i <;> simp [coordinates] at ha hb ⊢ <;> omega

private lemma normMass_coordinates (z : GaussianInt) :
    normMass z = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  have hn := congrArg (fun n : ℤ => (n : ℝ)) (GaussianInt.abs_natCast_norm z)
  simpa [normMass, Zsqrtd.norm, pow_two] using hn

private lemma coordinates_sq_upper (i : Fin 4) (z : GaussianInt) :
    ((coordinates i z).1 : ℝ) ^ 2 + ((coordinates i z).2 : ℝ) ^ 2 ≤ 2 * normMass z := by
  rw [normMass_coordinates]
  fin_cases i <;> simp [coordinates] <;> nlinarith [sq_nonneg (z.re : ℝ), sq_nonneg (z.im : ℝ)]

private lemma coordinates_abs_le {S : ℝ} (hS : 1 ≤ S) (i : Fin 4) (z : GaussianInt)
    (hz : ‖(z : ℂ)‖ ≤ Real.sqrt S) :
    ((coordinates i z).1.natAbs : ℝ) ≤ 2 * S ∧
      ((coordinates i z).2.natAbs : ℝ) ≤ 2 * S := by
  have hN : normMass z ≤ S := by
    rw [normMass_eq_sq_norm]
    have h := (sq_le_sq₀ (norm_nonneg (z : ℂ)) (Real.sqrt_nonneg S)).mpr hz
    simpa only [Real.sq_sqrt (show 0 ≤ S by linarith)] using h
  have hcoord := (coordinates_sq_upper i z).trans (mul_le_mul_of_nonneg_left hN (by norm_num))
  have hsq (a : ℤ) : (a.natAbs : ℝ) ^ 2 = (a : ℝ) ^ 2 := by
    have h : (a.natAbs : ℤ) ^ 2 = a ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
    simpa only [Int.cast_pow, Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ℝ)) h
  have h₁ := Nat.cast_nonneg (α := ℝ) (coordinates i z).1.natAbs
  have h₂ := Nat.cast_nonneg (α := ℝ) (coordinates i z).2.natAbs
  rw [← hsq (coordinates i z).1, ← hsq (coordinates i z).2] at hcoord
  constructor <;> nlinarith [sq_nonneg ((coordinates i z).1.natAbs : ℝ),
    sq_nonneg ((coordinates i z).2.natAbs : ℝ),
    sq_nonneg (((coordinates i z).1.natAbs : ℝ) - 1),
    sq_nonneg (((coordinates i z).2.natAbs : ℝ) - 1)]

/-- Each of the four actual directions has reciprocal mass at most
`64 (1 + log S) / q`. The diagonal image is enlarged without any parity premise. -/
theorem directionVectors_reciprocal_upper (i : Fin 4) (q : ℕ) (hq : 1 ≤ q)
    {S : ℝ} (hS : 1 ≤ S) :
    ∑ z ∈ directionVectors i q S, 1 / normMass z ≤
      64 * (1 + Real.log S) / (q : ℝ) := by
  classical
  let M : ℕ := ⌊2 * S⌋₊
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmaps : (directionVectors i q S).image (coordinates i) ⊆
      integerRange M ×ˢ multiples q M := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hz0, hzR, hqz, hzt⟩ := (mem_directionVectors i q S z).mp hz
    obtain ⟨ha, hb⟩ := coordinates_abs_le hS i z hzR
    exact Finset.mem_product.mpr
      ⟨mem_integerRange (Nat.le_floor ha), mem_multiples hq hzt hqz (Nat.le_floor hb)⟩
  have hrec : ∑ z ∈ directionVectors i q S, 1 / normMass z ≤
      2 * (∑ p ∈ integerRange M ×ˢ multiples q M,
        1 / ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    calc
      _ ≤ ∑ z ∈ directionVectors i q S,
          2 * (1 / (((coordinates i z).1 : ℝ) ^ 2 + ((coordinates i z).2 : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro z hz
        obtain ⟨hz0, _, _, hzt⟩ := (mem_directionVectors i q S z).mp hz
        have hN : 0 < normMass z := lt_of_lt_of_le zero_lt_one (one_le_normMass hz0)
        have ht : (0 : ℝ) < ((coordinates i z).1 : ℝ) ^ 2 +
            ((coordinates i z).2 : ℝ) ^ 2 := by
          have hcast : ((coordinates i z).2 : ℝ) ≠ 0 := by exact_mod_cast hzt
          positivity
        have hh := coordinates_sq_upper i z
        rw [mul_one_div]
        exact (div_le_div_iff₀ hN ht).mpr (by simpa using hh)
      _ = 2 * (∑ p ∈ (directionVectors i q S).image (coordinates i),
          1 / ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
        rw [Finset.sum_image (fun x _ y _ h => coordinates_injective i h), Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hmaps (fun p _ _ => by positivity)) (by norm_num)
  have hh : (harmonic M : ℝ) ≤ 2 * (1 + Real.log S) := by
    have h := harmonic_floor_le_one_add_log (2 * S) (by linarith)
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hlogS := Real.log_nonneg hS
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : S ≠ 0)] at h
    dsimp [M]
    linarith
  calc
    _ ≤ 2 * (16 / (q : ℝ) * (harmonic M : ℝ)) :=
      hrec.trans (mul_le_mul_of_nonneg_left (reciprocal_rectangle_upper q M M hq) (by norm_num))
    _ ≤ 2 * (16 / (q : ℝ) * (2 * (1 + Real.log S))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hh (by positivity)) (by norm_num)
    _ = _ := by ring

/-- Quantitative reciprocal mass of the four-direction union, counting a vector once. -/
theorem smallFlipVectors_reciprocal_upper (q : ℕ) (hq : 1 ≤ q)
    {S : ℝ} (hS : 1 ≤ S) :
    ∑ z ∈ smallFlipVectors q S, 1 / normMass z ≤
      256 * (1 + Real.log S) / (q : ℝ) := by
  classical
  calc
    _ ≤ ∑ i : Fin 4, ∑ z ∈ directionVectors i q S, 1 / normMass z :=
      sum_biUnion_upper _ _ _ (fun z => by unfold normMass; positivity)
    _ ≤ ∑ _i : Fin 4, 64 * (1 + Real.log S) / (q : ℝ) :=
      Finset.sum_le_sum (fun i _ => directionVectors_reciprocal_upper i q hq hS)
    _ = _ := by simp; ring

/-- Actual nonzero Gaussian vectors in radius `R` divisible by a small-flip vector. -/
def smallFlipDivisibleVectors (q : ℕ) (S R : ℝ) : Finset GaussianInt := by
  classical
  exact (smallFlipVectors q S).biUnion (fun v => (divisorDisk v R).erase 0)

lemma mem_smallFlipDivisibleVectors (q : ℕ) (S R : ℝ) (z : GaussianInt) :
    z ∈ smallFlipDivisibleVectors q S R ↔ z ≠ 0 ∧ ‖(z : ℂ)‖ ≤ R ∧
      ∃ v ∈ smallFlipVectors q S, v ∣ z := by
  classical
  simp only [smallFlipDivisibleVectors, Finset.mem_biUnion, Finset.mem_erase,
    mem_divisorDisk, dist_zero_right]
  aesop

/-- The small-flip union count; no independence or equidistribution input is used. -/
theorem smallFlipDivisibleVectors_card_upper (q : ℕ) (hq : 1 ≤ q)
    {S R : ℝ} (hS : 1 ≤ S) (hR : 0 ≤ R) :
    ((smallFlipDivisibleVectors q S R).card : ℝ) ≤
      (2304 * Real.pi) * R ^ 2 * (1 + Real.log S) / (q : ℝ) := by
  classical
  calc
    _ ≤ ∑ v ∈ smallFlipVectors q S, (((divisorDisk v R).erase 0).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := smallFlipVectors q S)
        (t := fun v => (divisorDisk v R).erase 0))
    _ ≤ ∑ v ∈ smallFlipVectors q S, 9 * Real.pi * R ^ 2 / normMass v := by
      apply Finset.sum_le_sum
      intro v hv
      exact divisorDisk_erase_zero_card_upper v ((mem_smallFlipVectors q S v).mp hv).1 hR
    _ = (9 * Real.pi * R ^ 2) * (∑ v ∈ smallFlipVectors q S, 1 / normMass v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (9 * Real.pi * R ^ 2) * (256 * (1 + Real.log S) / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left (smallFlipVectors_reciprocal_upper q hq hS) (by positivity)
    _ = _ := by ring

end DistanceCounts.SmallFlipLattice
end
end

-- Source: DistanceCounts/GaussianMassExclusions.lean
section
/-! Removing finitely many genuine Gaussian prime classes from squarefree mass. -/

noncomputable section

namespace DistanceCounts.GaussianMass

open Finset
open scoped Classical

/-- Squarefree classes below the original norm cutoff avoiding the excluded primes. -/
def excludedBall (D : ℝ) (E : Finset (Associates GaussianInt)) :
    Finset (Associates GaussianInt) :=
  (squarefreeBall D).filter (fun a => Disjoint (primeSupport a) E)

/-- The actual reciprocal-phi mass, with no alteration of the Gaussian norm. -/
def excludedMass (D : ℝ) (E : Finset (Associates GaussianInt)) : ℝ :=
  ∑ a ∈ excludedBall D E, 1 / squarefreePhi a

/-- Delete the excluded prime classes from a squarefree support. -/
def exclusionRemainder (E : Finset (Associates GaussianInt))
    (a : Associates GaussianInt) : Associates GaussianInt :=
  ∏ p ∈ primeSupport a \ E, p

lemma primeSupport_exclusionRemainder (E : Finset (Associates GaussianInt))
    (a : Associates GaussianInt) :
    primeSupport (exclusionRemainder E a) = primeSupport a \ E := by
  apply primeSupport_prime_prod
  intro p hp
  exact prime_of_mem_primeSupport (mem_sdiff.mp hp).1

lemma squarefree_exclusionRemainder (E : Finset (Associates GaussianInt))
    (a : Associates GaussianInt) : Squarefree (exclusionRemainder E a) := by
  apply squarefree_prime_prod
  intro p hp
  exact prime_of_mem_primeSupport (mem_sdiff.mp hp).1

lemma exclusionRemainder_mem {D : ℝ} (hD : 0 ≤ D)
    (E : Finset (Associates GaussianInt)) {a : Associates GaussianInt}
    (ha : a ∈ squarefreeBall D) : exclusionRemainder E a ∈ excludedBall D E := by
  obtain ⟨haSq, haD⟩ := (mem_squarefreeBall hD a).mp ha
  apply mem_filter.mpr
  constructor
  · apply (mem_squarefreeBall hD _).mpr
    refine ⟨squarefree_exclusionRemainder E a, ?_⟩
    have hn : (classNorm (exclusionRemainder E a) : ℝ) ≤ classNorm a := by
      exact_mod_cast primeSupport_subset_norm_le haSq
        (show primeSupport a \ E ⊆ primeSupport a from sdiff_subset)
    exact hn.trans haD
  · rw [primeSupport_exclusionRemainder]
    exact disjoint_sdiff_self_left

/-- The retained class and the removed support reconstruct the original class. -/
lemma exclusion_reconstruct (E : Finset (Associates GaussianInt))
    {a : Associates GaussianInt} (ha : Squarefree a) :
    exclusionRemainder E a * (∏ p ∈ primeSupport a ∩ E, p) = a := by
  unfold exclusionRemainder
  rw [← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter, primeSupport_prod ha]

lemma exclusion_split_injective (E : Finset (Associates GaussianInt))
    {a b : Associates GaussianInt} (ha : Squarefree a) (hb : Squarefree b)
    (h : (exclusionRemainder E a, primeSupport a ∩ E) =
      (exclusionRemainder E b, primeSupport b ∩ E)) : a = b := by
  have hfirst : exclusionRemainder E a = exclusionRemainder E b :=
    congrArg Prod.fst h
  have hsecond : primeSupport a ∩ E = primeSupport b ∩ E :=
    congrArg Prod.snd h
  calc
    a = exclusionRemainder E a * (∏ p ∈ primeSupport a ∩ E, p) :=
      (exclusion_reconstruct E ha).symm
    _ = exclusionRemainder E b * (∏ p ∈ primeSupport b ∩ E, p) := by
      rw [hfirst, hsecond]
    _ = b := exclusion_reconstruct E hb

lemma squarefreePhi_exclusion_factor (E : Finset (Associates GaussianInt))
    (a : Associates GaussianInt) :
    squarefreePhi a = squarefreePhi (exclusionRemainder E a) *
      ∏ p ∈ primeSupport a ∩ E, ((classNorm p : ℝ) - 1) := by
  unfold squarefreePhi
  rw [primeSupport_exclusionRemainder,
    ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter]

lemma reciprocalPhi_exclusion_factor (E : Finset (Associates GaussianInt))
    (a : Associates GaussianInt) :
    1 / squarefreePhi a = (1 / squarefreePhi (exclusionRemainder E a)) *
      ∏ p ∈ primeSupport a ∩ E, (1 / ((classNorm p : ℝ) - 1)) := by
  rw [squarefreePhi_exclusion_factor E a]
  simp only [one_div, mul_inv_rev, prod_inv_distrib]
  ring

/-- Expanding the finite Euler factor includes every possible removed support. -/
lemma exclusion_powerset_sum (E : Finset (Associates GaussianInt)) :
    (∑ T ∈ E.powerset, ∏ p ∈ T, (1 / ((classNorm p : ℝ) - 1))) =
      ∏ p ∈ E, (1 + 1 / ((classNorm p : ℝ) - 1)) := by
  simpa only [prod_const_one, mul_one, add_comm] using
    (prod_add (fun p : Associates GaussianInt => 1 / ((classNorm p : ℝ) - 1))
      (fun _ => (1 : ℝ)) E).symm

/-- Splitting supports injects the original mass into the retained classes times
all subsets of the excluded primes. Only the retained class keeps the cutoff. -/
theorem squarefreeMass_le_excludedMass_mul {D : ℝ} (hD : 1 ≤ D)
    (E : Finset (Associates GaussianInt)) (hE : ∀ p ∈ E, Prime p) :
    squarefreeMass D ≤ excludedMass D E *
      ∏ p ∈ E, (1 + 1 / ((classNorm p : ℝ) - 1)) := by
  let split : Associates GaussianInt →
      Associates GaussianInt × Finset (Associates GaussianInt) :=
    fun a => (exclusionRemainder E a, primeSupport a ∩ E)
  let weight : Associates GaussianInt × Finset (Associates GaussianInt) → ℝ :=
    fun x => (1 / squarefreePhi x.1) *
      ∏ p ∈ x.2, (1 / ((classNorm p : ℝ) - 1))
  have hsub : (squarefreeBall D).image split ⊆ (excludedBall D E).product E.powerset := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    apply mem_product.mpr
    exact ⟨exclusionRemainder_mem (by linarith) E ha,
      mem_powerset.mpr inter_subset_right⟩
  have hinj : ∀ a ∈ squarefreeBall D, ∀ b ∈ squarefreeBall D,
      split a = split b → a = b := by
    intro a ha b hb hab
    exact exclusion_split_injective E (mem_filter.mp ha).2 (mem_filter.mp hb).2 hab
  have hnonneg : ∀ x ∈ (excludedBall D E).product E.powerset, 0 ≤ weight x := by
    intro x hx
    obtain ⟨_, hxE⟩ := mem_product.mp hx
    apply mul_nonneg (le_of_lt (one_div_pos.mpr (squarefreePhi_pos x.1)))
    apply prod_nonneg
    intro p hp
    have hn : (2 : ℝ) ≤ classNorm p := by
      exact_mod_cast classNorm_prime_two_le (hE p ((mem_powerset.mp hxE) hp))
    exact le_of_lt (one_div_pos.mpr (by linarith))
  calc
    squarefreeMass D = ∑ x ∈ (squarefreeBall D).image split, weight x := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro a _
      exact reciprocalPhi_exclusion_factor E a
    _ ≤ ∑ x ∈ (excludedBall D E).product E.powerset, weight x :=
      sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hnonneg x hx)
    _ = excludedMass D E *
        (∑ T ∈ E.powerset, ∏ p ∈ T, (1 / ((classNorm p : ℝ) - 1))) := by
      exact (Finset.sum_product (excludedBall D E) E.powerset weight).trans
        (Finset.sum_mul_sum (excludedBall D E) E.powerset
          (fun a : Associates GaussianInt => 1 / squarefreePhi a)
          (fun T : Finset (Associates GaussianInt) =>
            ∏ p ∈ T, (1 / ((classNorm p : ℝ) - 1)))).symm
    _ = _ := by rw [exclusion_powerset_sum]

lemma excludedMass_nonneg (D : ℝ) (E : Finset (Associates GaussianInt)) :
    0 ≤ excludedMass D E := by
  exact sum_nonneg (fun a _ => le_of_lt (one_div_pos.mpr (squarefreePhi_pos a)))

/-- Four Gaussian prime classes of norm at least nine cost at most `(9/8)^4`. -/
theorem exclusion_factor_le_four (E : Finset (Associates GaussianInt))
    (hcard : E.card ≤ 4) (hnorm : ∀ p ∈ E, 9 ≤ classNorm p) :
    (∏ p ∈ E, (1 + 1 / ((classNorm p : ℝ) - 1))) ≤ (9 / 8 : ℝ) ^ 4 := by
  calc
    _ ≤ ∏ _p ∈ E, (9 / 8 : ℝ) := by
      apply prod_le_prod
      · intro p hp
        have hn : (9 : ℝ) ≤ classNorm p := by exact_mod_cast hnorm p hp
        have hi : 0 ≤ 1 / ((classNorm p : ℝ) - 1) :=
          le_of_lt (one_div_pos.mpr (by linarith))
        linarith
      · intro p hp
        have hn : (9 : ℝ) ≤ classNorm p := by exact_mod_cast hnorm p hp
        have hi : 1 / ((classNorm p : ℝ) - 1) ≤ (1 / 8 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith
    _ = (9 / 8 : ℝ) ^ E.card := prod_const _
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hcard


/-- A rational inert prime has genuine Gaussian norm `p²`, not `p`. -/
lemma classNorm_mk_natCast (p : ℕ) :
    classNorm (Associates.mk (p : GaussianInt)) = p ^ 2 := by
  simp [classNorm_mk, Zsqrtd.norm_natCast, Int.natAbs_mul, pow_two]

/-- Uniform exclusion for any finite set of at most four distinct inert primes. -/
theorem inert_exclusion_factor_le_four (P : Finset ℕ) (hcard : P.card ≤ 4)
    (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3) :
    (∏ q ∈ P.image (fun p : ℕ => Associates.mk (p : GaussianInt)),
      (1 + 1 / ((classNorm q : ℝ) - 1))) ≤ (9 / 8 : ℝ) ^ 4 := by
  apply exclusion_factor_le_four
  · exact (Finset.card_image_le
      (s := P) (f := fun p : ℕ => Associates.mk (p : GaussianInt))).trans hcard
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := (Finset.mem_image
      (s := P) (f := fun p : ℕ => Associates.mk (p : GaussianInt))).mp hq
    rw [classNorm_mk_natCast]
    have hp3 := (hP p hp).2
    have hpmin : 3 ≤ p := by omega
    nlinarith

theorem squarefreeMass_le_inert_excludedMass_four {D : ℝ} (hD : 1 ≤ D)
    (P : Finset ℕ) (hcard : P.card ≤ 4)
    (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3) :
    squarefreeMass D ≤
      excludedMass D (P.image (fun p : ℕ => Associates.mk (p : GaussianInt))) *
        (9 / 8 : ℝ) ^ 4 := by
  have hprime :
      ∀ q ∈ P.image (fun p : ℕ => Associates.mk (p : GaussianInt)), Prime q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := (Finset.mem_image
      (s := P) (f := fun p : ℕ => Associates.mk (p : GaussianInt))).mp hq
    exact Associates.prime_mk.mpr
      (@GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p ⟨(hP p hp).1⟩ (hP p hp).2)
  exact (squarefreeMass_le_excludedMass_mul hD _ hprime).trans
    (mul_le_mul_of_nonneg_left (inert_exclusion_factor_le_four P hcard hP)
      (excludedMass_nonneg D _))

end DistanceCounts.GaussianMass
end
end

-- Source: DistanceCounts/GaussianSieveFamily.lean
section
/-! Selberg weights indexed by genuine Gaussian prime classes, with actual lcm divisors. -/

noncomputable section

namespace DistanceCounts.GaussianSieveFamily

open Finset GaussianMass
open scoped Classical

/-- Distinct conjugate Gaussian primes remain distinct indices. -/
abbrev PrimeClass := {p : Associates GaussianInt // Prime p}

def primeNorm (p : PrimeClass) : ℝ := classNorm p.val

lemma primeNorm_two_le (p : PrimeClass) : 2 ≤ primeNorm p := by
  change (2 : ℝ) ≤ (classNorm p.val : ℝ)
  exact_mod_cast classNorm_prime_two_le p.property

/-- Lift the actual finite prime support, without adding any artificial primes. -/
def support (a : Associates GaussianInt) : Finset PrimeClass :=
  (primeSupport a).subtype Prime

lemma mem_support (a : Associates GaussianInt) (p : PrimeClass) :
    p ∈ support a ↔ p.val ∈ primeSupport a := Finset.mem_subtype

def underlying (S : Finset PrimeClass) : Finset (Associates GaussianInt) :=
  S.map (Function.Embedding.subtype Prime)

lemma underlying_support (a : Associates GaussianInt) :
    underlying (support a) = primeSupport a :=
  Finset.subtype_map_of_mem (fun _ hp => prime_of_mem_primeSupport hp)

lemma prime_underlying (S : Finset PrimeClass) : ∀ p ∈ underlying S, Prime p := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := mem_map.mp hp
  exact q.property

/-- The squarefree class attached to a finite set of genuine primes. -/
def classProduct (S : Finset PrimeClass) : Associates GaussianInt := ∏ p ∈ S, p.val

lemma classProduct_eq (S : Finset PrimeClass) :
    classProduct S = ∏ p ∈ underlying S, p := by
  simp [classProduct, underlying]

lemma squarefree_classProduct (S : Finset PrimeClass) : Squarefree (classProduct S) := by
  rw [classProduct_eq]
  exact squarefree_prime_prod _ (prime_underlying S)

lemma primeSupport_classProduct (S : Finset PrimeClass) :
    primeSupport (classProduct S) = underlying S := by
  rw [classProduct_eq]
  exact primeSupport_prime_prod _ (prime_underlying S)

lemma support_classProduct (S : Finset PrimeClass) : support (classProduct S) = S := by
  ext p
  rw [mem_support, primeSupport_classProduct]
  simp [underlying, p.property]

lemma classProduct_support {a : Associates GaussianInt} (ha : Squarefree a) :
    classProduct (support a) = a := by
  rw [classProduct_eq, underlying_support, primeSupport_prod ha]

lemma support_injective_squarefree {a b : Associates GaussianInt}
    (ha : Squarefree a) (hb : Squarefree b) (h : support a = support b) : a = b := by
  rw [← classProduct_support ha, ← classProduct_support hb, h]

lemma classProduct_injective : Function.Injective classProduct := by
  intro S T h
  simpa only [support_classProduct] using congrArg support h

lemma classProduct_norm (S : Finset PrimeClass) :
    (classNorm (classProduct S) : ℝ) = SieveWeights.norm primeNorm S := by
  rw [classProduct_eq, classNorm_prod, Nat.cast_prod]
  simp [underlying, SieveWeights.norm, primeNorm]

lemma support_phi (a : Associates GaussianInt) :
    SieveWeights.phi primeNorm (support a) = squarefreePhi a := by
  unfold SieveWeights.phi primeNorm support squarefreePhi
  exact prod_subtype_of_mem (fun p => (classNorm p : ℝ) - 1)
    (fun _ hp => prime_of_mem_primeSupport hp)

lemma underlying_mono {S T : Finset PrimeClass} (h : S ⊆ T) :
    underlying S ⊆ underlying T := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
  exact mem_map.mpr ⟨q, h hq, rfl⟩

/-- The lower family is precisely the actual squarefree norm ball avoiding `E`. -/
def family (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    SieveWeights.DivisorFamily PrimeClass where
  members := (excludedBall D E).image support
  nonempty := by
    refine ⟨support 1, mem_image.mpr ⟨1, ?_, rfl⟩⟩
    apply mem_filter.mpr
    constructor
    · exact (mem_squarefreeBall (by linarith) 1).mpr
        ⟨squarefree_one, by simpa [classNorm_one] using hD⟩
    · simp [primeSupport]
  lower := by
    intro S T hT hST
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hT
    obtain ⟨haBall, haE⟩ := mem_filter.mp ha
    obtain ⟨haSq, haD⟩ := (mem_squarefreeBall (by linarith) a).mp haBall
    have hsub : underlying S ⊆ primeSupport a := by
      simpa only [underlying_support] using underlying_mono hST
    refine mem_image.mpr ⟨classProduct S, mem_filter.mpr ⟨?_, ?_⟩,
      support_classProduct S⟩
    · apply (mem_squarefreeBall (by linarith) _).mpr
      refine ⟨squarefree_classProduct S, ?_⟩
      have hn : (classNorm (classProduct S) : ℝ) ≤ classNorm a := by
        rw [classProduct_eq]
        exact_mod_cast primeSupport_subset_norm_le haSq hsub
      exact hn.trans haD
    · rw [primeSupport_classProduct]
      exact haE.mono_left hsub

lemma mem_family_iff (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt))
    (S : Finset PrimeClass) :
    S ∈ (family D hD E).members ↔ classProduct S ∈ excludedBall D E := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := mem_image.mp h
    have haSq : Squarefree a := (mem_filter.mp (mem_filter.mp ha).1).2
    simpa only [classProduct_support haSq] using ha
  · intro h
    exact mem_image.mpr ⟨classProduct S, h, support_classProduct S⟩

lemma family_mass (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    (family D hD E).mass primeNorm = excludedMass D E := by
  unfold SieveWeights.DivisorFamily.mass family
  rw [sum_image]
  · simp only [support_phi, excludedMass]
  · intro a ha b hb hab
    exact support_injective_squarefree
      (mem_filter.mp (mem_filter.mp ha).1).2
      (mem_filter.mp (mem_filter.mp hb).1).2 hab


/-- The actual normalized Selberg coefficients, zero off the norm-cutoff family. -/
def weight (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt))
    (S : Finset PrimeClass) : ℝ := (family D hD E).weight primeNorm S

lemma weight_empty (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    weight D hD E ∅ = 1 :=
  (family D hD E).weight_empty primeNorm primeNorm_two_le


/-- The denominator uses the union (lcm) of prime sets, not their product. -/
theorem quadratic_weight (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    (∑ S ∈ (family D hD E).members, ∑ T ∈ (family D hD E).members,
      weight D hD E S * weight D hD E T / SieveWeights.norm primeNorm (S ∪ T)) =
        1 / excludedMass D E := by
  rw [← family_mass D hD E]
  exact (family D hD E).quadratic_weight primeNorm primeNorm_two_le

lemma supported_norm_le (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt))
    {S : Finset PrimeClass} (hS : S ∈ (family D hD E).members) :
    SieveWeights.norm primeNorm S ≤ D := by
  have hm := (mem_family_iff D hD E S).mp hS
  rw [← classProduct_norm]
  exact ((mem_squarefreeBall (by linarith) _).mp (mem_filter.mp hm).1).2

lemma abs_weight_le (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt))
    {S : Finset PrimeClass} (hS : S ∈ (family D hD E).members) :
    |weight D hD E S| ≤ D :=
  ((family D hD E).abs_weight_le_norm primeNorm primeNorm_two_le S).trans
    (supported_norm_le D hD E hS)

lemma family_card_le (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    (family D hD E).members.card ≤ (classBall D).card := by
  exact (card_image_le).trans (card_le_card (fun _ ha =>
    (mem_filter.mp (mem_filter.mp ha).1).1))

lemma classBall_card_le_twelve {D : ℝ} (hD : 1 ≤ D) :
    ((classBall D).card : ℝ) ≤ 12 * D := by
  have hD0 : 0 ≤ D := by linarith
  have hc := (abs_le.mp (classBall_card_error hD0)).2
  have hs : Real.sqrt D ≤ D := by
    nlinarith [Real.sq_sqrt hD0, Real.sqrt_nonneg D]
  have hm : Real.pi / 4 * D ≤ D := by
    have := mul_le_mul_of_nonneg_right (show Real.pi / 4 ≤ 1 by
      linarith [Real.pi_lt_four]) hD0
    simpa using this
  have he : (Real.pi + 1) * (Real.sqrt D + 1) ≤ 5 * (2 * D) :=
    mul_le_mul (by linarith [Real.pi_lt_four]) (by linarith)
      (by positivity) (by norm_num)
  linarith

/-- A uniform total coefficient budget obtained from the genuine class count. -/
theorem sum_abs_weight_le (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    (∑ S ∈ (family D hD E).members, |weight D hD E S|) ≤ 12 * D ^ 2 := by
  have hc : ((family D hD E).members.card : ℝ) ≤ 12 * D :=
    (Nat.cast_le.mpr (family_card_le D hD E)).trans (classBall_card_le_twelve hD)
  calc
    _ ≤ ∑ _S ∈ (family D hD E).members, D :=
      sum_le_sum (fun _ hS => abs_weight_le D hD E hS)
    _ = ((family D hD E).members.card : ℝ) * D := by simp
    _ ≤ (12 * D) * D := mul_le_mul_of_nonneg_right hc (by linarith)
    _ = _ := by ring

/-- A representative of the actual associate product, chosen only at this bridge. -/
def representative (S : Finset PrimeClass) : GaussianInt :=
  Classical.choose (Associates.mk_surjective (classProduct S))

lemma mk_representative (S : Finset PrimeClass) :
    Associates.mk (representative S) = classProduct S :=
  Classical.choose_spec (Associates.mk_surjective (classProduct S))

lemma representative_ne_zero (S : Finset PrimeClass) : representative S ≠ 0 := by
  apply Associates.mk_ne_zero.mp
  rw [mk_representative]
  exact (squarefree_classProduct S).ne_zero


lemma representative_norm (S : Finset PrimeClass) :
    GaussianDivisibility.normMass (representative S) = SieveWeights.norm primeNorm S := by
  rw [← classProduct_norm, ← mk_representative, classNorm_mk]
  rfl

lemma classProduct_dvd_iff (S : Finset PrimeClass) (a : Associates GaussianInt) :
    classProduct S ∣ a ↔ ∀ p ∈ S, p.val ∣ a := by
  induction S using Finset.induction_on with
  | empty => simp [classProduct]
  | @insert p S hp ih =>
    have hs : Squarefree (p.val * classProduct S) := by
      simpa only [classProduct, prod_insert hp] using squarefree_classProduct (insert p S)
    have hrel := IsRelPrime.of_squarefree_mul hs
    rw [show classProduct (insert p S) = p.val * classProduct S by
      simp [classProduct, hp]]
    constructor
    · intro h q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact dvd_trans (dvd_mul_right _ _) h
      · exact (ih.mp (dvd_trans (dvd_mul_left _ _) h)) q hq
    · intro h
      exact hrel.mul_dvd (h p (mem_insert_self _ _))
        (ih.mpr (fun q hq => h q (mem_insert_of_mem hq)))

lemma representative_dvd_iff (S : Finset PrimeClass) (z : GaussianInt) :
    representative S ∣ z ↔ ∀ p ∈ S, p.val ∣ Associates.mk z := by
  rw [← Associates.mk_dvd_mk, mk_representative, classProduct_dvd_iff]

/-- Simultaneous divisibility is exactly the squarefree union, even with overlap. -/
theorem representative_union_dvd (S T : Finset PrimeClass) (z : GaussianInt) :
    representative (S ∪ T) ∣ z ↔ representative S ∣ z ∧ representative T ∣ z := by
  simp only [representative_dvd_iff, mem_union, or_imp, forall_and]


/-- The exact quadratic main term expressed with genuine Gaussian lcm norms. -/
theorem quadratic_representative (D : ℝ) (hD : 1 ≤ D)
    (E : Finset (Associates GaussianInt)) :
    (∑ S ∈ (family D hD E).members, ∑ T ∈ (family D hD E).members,
      weight D hD E S * weight D hD E T /
        GaussianDivisibility.normMass (representative (S ∪ T))) =
          1 / excludedMass D E := by
  simp only [representative_norm]
  exact quadratic_weight D hD E

end DistanceCounts.GaussianSieveFamily
end
end

-- Source: DistanceCounts/GaussianProgressions.lean
section
/-! Exact Gaussian congruence populations and coprime divisibility lattice counts. -/

noncomputable section

namespace DistanceCounts.GaussianProgressions

open GaussianDivisibility

/-- The actual closed disk restricted to one rational-modulus Gaussian congruence. -/
def progression (a : GaussianInt) (q : ℕ) (R : ℝ) : Finset GaussianInt := by
  classical
  exact (gaussianDisk 0 R).filter (fun z => (q : GaussianInt) ∣ z - a)

/-- The same progression with genuine Gaussian divisibility imposed. -/
def divisibleProgression (a : GaussianInt) (q : ℕ) (d : GaussianInt)
    (R : ℝ) : Finset GaussianInt := by
  classical
  exact (progression a q R).filter (fun z => d ∣ z)

lemma mem_progression (a z : GaussianInt) (q : ℕ) (R : ℝ) :
    z ∈ progression a q R ↔
      dist (z : ℂ) 0 ≤ R ∧ (q : GaussianInt) ∣ z - a := by
  classical
  simp [progression, mem_gaussianDisk]


/-- Bezout coefficients give an actual simultaneous residue, with no condition on `a`. -/
theorem exists_crt_residue (a m d : GaussianInt) (hmd : IsCoprime m d) :
    ∃ b : GaussianInt, m ∣ b - a ∧ d ∣ b := by
  obtain ⟨u, v, huv⟩ := hmd
  refine ⟨v * d * a, ?_, ?_⟩
  · refine ⟨-(u * a), ?_⟩
    calc
      v * d * a - a = ((u * m + v * d) - 1) * a + m * (-(u * a)) := by ring
      _ = m * (-(u * a)) := by rw [huv]; ring
  · exact ⟨v * a, by ring⟩

/-- Once a simultaneous residue is fixed, the two congruences are exactly one ideal coset. -/
lemma crt_dvd_iff (a b m d z : GaussianInt) (hmd : IsCoprime m d)
    (hb : m ∣ b - a) (hdb : d ∣ b) :
    (m ∣ z - a ∧ d ∣ z) ↔ m * d ∣ z - b := by
  constructor
  · rintro ⟨hza, hdz⟩
    apply hmd.mul_dvd
    · have he : z - b = (z - a) - (b - a) := by ring
      rw [he]
      exact dvd_sub hza hb
    · exact dvd_sub hdz hdb
  · intro hz
    have hmz : m ∣ z - b := dvd_trans (dvd_mul_right m d) hz
    have hdz : d ∣ z - b := dvd_trans (dvd_mul_left d m) hz
    constructor
    · have he : z - a = (z - b) + (b - a) := by ring
      rw [he]
      exact dvd_add hmz hb
    · have he : z = (z - b) + b := by ring
      rw [he]
      exact dvd_add hdz hdb

open scoped Classical in
/-- The CRT identity is an equality of finite sets, for every centre and every radius.
In particular the boundary is closed and zero is never silently discarded. -/
theorem disk_filter_eq_coset (a b m d : GaussianInt) (hm : m ≠ 0) (hd : d ≠ 0)
    (hmd : IsCoprime m d) (hb : m ∣ b - a) (hdb : d ∣ b)
    (c : ℂ) (R : ℝ) :
    ((gaussianDisk c R).filter (fun z => m ∣ z - a ∧ d ∣ z)) =
      gaussianCosetDisk b (m * d) c R := by
  classical
  ext z
  rw [Finset.mem_filter, mem_gaussianDisk,
    mem_gaussianCosetDisk _ _ _ (mul_ne_zero hm hd), crt_dvd_iff a b m d z hmd hb hdb]
  constructor
  · rintro ⟨hR, w, hw⟩
    refine ⟨⟨w, ?_⟩, hR⟩
    rw [← hw]
    ring
  · rintro ⟨⟨w, hw⟩, hR⟩
    refine ⟨hR, w, ?_⟩
    rw [← hw]
    ring

/-- Any Bezout residue identifies the actual filtered progression with its ideal lattice. -/
theorem divisibleProgression_eq_coset (a b : GaussianInt) (q : ℕ) (hq : 0 < q)
    (d : GaussianInt) (hd : d ≠ 0) (hqd : IsCoprime (q : GaussianInt) d)
    (hb : (q : GaussianInt) ∣ b - a) (hdb : d ∣ b) (R : ℝ) :
    divisibleProgression a q d R = gaussianCosetDisk b ((q : GaussianInt) * d) 0 R := by
  classical
  have hq0 : (q : GaussianInt) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simpa only [divisibleProgression, progression, Finset.filter_filter] using
    disk_filter_eq_coset a b (q : GaussianInt) d hq0 hd hqd hb hdb 0 R

/-- Both the residue and the finite-set CRT identity are constructed, not assumed. -/
theorem exists_divisibleProgression_eq_coset (a : GaussianInt) (q : ℕ) (hq : 0 < q)
    (d : GaussianInt) (hd : d ≠ 0) (hqd : IsCoprime (q : GaussianInt) d) (R : ℝ) :
    ∃ b : GaussianInt, (q : GaussianInt) ∣ b - a ∧ d ∣ b ∧
      divisibleProgression a q d R = gaussianCosetDisk b ((q : GaussianInt) * d) 0 R := by
  obtain ⟨b, hb, hdb⟩ := exists_crt_residue a (q : GaussianInt) d hqd
  exact ⟨b, hb, hdb, divisibleProgression_eq_coset a b q hq d hd hqd hb hdb R⟩

lemma complex_norm_natCast (q : ℕ) : ‖((q : GaussianInt) : ℂ)‖ = (q : ℝ) := by
  have h : ‖((q : GaussianInt) : ℂ)‖ ^ 2 = (q : ℝ) ^ 2 := by
    rw [← normMass_eq_sq_norm, normMass_natCast]
  nlinarith [norm_nonneg ((q : GaussianInt) : ℂ), Nat.cast_nonneg (α := ℝ) q]

/-- The quantitative CRT count at its exact lattice scale. -/
theorem divisibleProgression_card_error_scaled (a : GaussianInt) (q : ℕ) (hq : 0 < q)
    (d : GaussianInt) (hd : d ≠ 0) (hqd : IsCoprime (q : GaussianInt) d)
    {R : ℝ} (hR : 0 ≤ R) :
    |((divisibleProgression a q d R).card : ℝ) -
      Real.pi * R ^ 2 / ((q : ℝ) ^ 2 * normMass d)| ≤
      (4 * Real.pi) * (R / ((q : ℝ) * ‖(d : ℂ)‖) + 1) := by
  obtain ⟨b, hb, hdb, heq⟩ := exists_divisibleProgression_eq_coset a q hq d hd hqd R
  have hq0 : (q : GaussianInt) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have he := gaussianCosetDisk_card_error b ((q : GaussianInt) * d)
    (mul_ne_zero hq0 hd) 0 hR
  rw [← heq, GaussianInt.toComplex_mul, norm_mul, complex_norm_natCast] at he
  simpa only [normMass_eq_sq_norm, div_pow, mul_pow, mul_div_assoc] using he


/-- Uniformity in the nonzero divisor preserves the rational progression scale `R/q`. -/
theorem divisibleProgression_card_error (a : GaussianInt) (q : ℕ) (hq : 0 < q)
    (d : GaussianInt) (hd : d ≠ 0) (hqd : IsCoprime (q : GaussianInt) d)
    {R : ℝ} (hR : 0 ≤ R) :
    |((divisibleProgression a q d R).card : ℝ) -
      Real.pi * R ^ 2 / ((q : ℝ) ^ 2 * normMass d)| ≤
      (4 * Real.pi) * (R / (q : ℝ) + 1) := by
  apply (divisibleProgression_card_error_scaled a q hq d hd hqd hR).trans
  have hn := one_le_complex_norm hd
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hden : (q : ℝ) ≤ (q : ℝ) * ‖(d : ℂ)‖ := by nlinarith
  have hs : R / ((q : ℝ) * ‖(d : ℂ)‖) ≤ R / (q : ℝ) :=
    div_le_div_of_nonneg_left hR hqR hden
  exact mul_le_mul_of_nonneg_left
    (show R / ((q : ℝ) * ‖(d : ℂ)‖) + 1 ≤ R / (q : ℝ) + 1 by linarith)
    (by positivity)


end DistanceCounts.GaussianProgressions
end
end

-- Source: DistanceCounts/GaussianSieve.lean
section
/-! The finite Selberg upper bound for actual Gaussian primes in a congruence class. -/

noncomputable section

namespace DistanceCounts.GaussianSieve

open Finset GaussianMass GaussianSieveFamily GaussianDivisibility GaussianProgressions
open scoped Classical

/-- Exclude exactly the associate classes of the rational primes in the modulus. -/
def excludedClasses (P : Finset ℕ) : Finset (Associates GaussianInt) :=
  P.image (fun p : ℕ => Associates.mk (p : GaussianInt))

/-- All Gaussian prime elements in the actual progression, including every associate. -/
def primeProgression (a : GaussianInt) (q : ℕ) (R : ℝ) : Finset GaussianInt :=
  (progression a q R).filter Prime

lemma supported_disjoint (D : ℝ) (hD : 1 ≤ D)
    (E : Finset (Associates GaussianInt)) {S : Finset PrimeClass}
    (hS : S ∈ (family D hD E).members) : Disjoint (underlying S) E := by
  have h := (mem_filter.mp ((mem_family_iff D hD E S).mp hS)).2
  rwa [primeSupport_classProduct] at h

lemma representative_not_dvd_of_disjoint (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hinert : ∀ p ∈ P, p % 4 = 3)
    (S : Finset PrimeClass) (hS : Disjoint (underlying S) (excludedClasses P))
    {p : ℕ} (hp : p ∈ P) : ¬(p : GaussianInt) ∣ representative S := by
  intro hd
  have hpG : Prime (p : GaussianInt) :=
    @GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p ⟨hprime p hp⟩ (hinert p hp)
  have hd' : Associates.mk (p : GaussianInt) ∣ classProduct S := by
    rw [← mk_representative]
    exact Associates.mk_dvd_mk.mpr hd
  have hm : Associates.mk (p : GaussianInt) ∈ underlying S := by
    rw [← primeSupport_classProduct]
    exact (mem_primeSupport (squarefree_classProduct S).ne_zero).mpr
      ⟨Associates.prime_mk.mpr hpG, hd'⟩
  exact Finset.disjoint_left.mp hS hm (mem_image.mpr ⟨p, hp, rfl⟩)

/-- Exclusion proves Bezout coprimality for the actual chosen Gaussian divisor. -/
lemma representative_coprime_of_disjoint (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hinert : ∀ p ∈ P, p % 4 = 3)
    (S : Finset PrimeClass) (hS : Disjoint (underlying S) (excludedClasses P)) :
    IsCoprime ((∏ p ∈ P, p : ℕ) : GaussianInt) (representative S) := by
  rw [Nat.cast_prod]
  apply IsCoprime.prod_left
  intro p hp
  have hpG : Prime (p : GaussianInt) :=
    @GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p ⟨hprime p hp⟩ (hinert p hp)
  exact hpG.coprime_iff_not_dvd.mpr
    (representative_not_dvd_of_disjoint P hprime hinert S hS hp)


/-- Lcm divisors remain coprime, although their norms need not remain below `D`. -/
lemma supported_union_representative_coprime (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hinert : ∀ p ∈ P, p % 4 = 3)
    (D : ℝ) (hD : 1 ≤ D) {S T : Finset PrimeClass}
    (hS : S ∈ (family D hD (excludedClasses P)).members)
    (hT : T ∈ (family D hD (excludedClasses P)).members) :
    IsCoprime ((∏ p ∈ P, p : ℕ) : GaussianInt) (representative (S ∪ T)) := by
  apply representative_coprime_of_disjoint P hprime hinert
  apply Finset.disjoint_left.mpr
  intro p hp hpE
  obtain ⟨s, hs, rfl⟩ := mem_map.mp hp
  rcases mem_union.mp hs with hs | hs
  · exact Finset.disjoint_left.mp (supported_disjoint D hD _ hS)
      (mem_map.mpr ⟨s, hs, rfl⟩) hpE
  · exact Finset.disjoint_left.mp (supported_disjoint D hD _ hT)
      (mem_map.mpr ⟨s, hs, rfl⟩) hpE

/-- The Selberg score uses genuine element divisibility, not a surrogate indicator. -/
def sieveScore (D : ℝ) (hD : 1 ≤ D) (E : Finset (Associates GaussianInt))
    (z : GaussianInt) : ℝ :=
  ∑ S ∈ (family D hD E).members,
    if representative S ∣ z then weight D hD E S else 0

lemma supported_dvd_large_prime_iff (D : ℝ) (hD : 1 ≤ D)
    (E : Finset (Associates GaussianInt)) {S : Finset PrimeClass}
    (hS : S ∈ (family D hD E).members) {z : GaussianInt}
    (hz : Prime z) (hDz : D < normMass z) : representative S ∣ z ↔ S = ∅ := by
  constructor
  · intro hd
    rcases hz.irreducible.dvd_iff.mp hd with hu | ha
    · apply classProduct_injective
      rw [← mk_representative, Associates.mk_eq_one.mpr hu]
      simp [classProduct]
    · have hn : normMass z = normMass (representative S) := by
        unfold normMass
        exact_mod_cast congrArg Int.natAbs
          (Zsqrtd.norm_eq_of_associated (by norm_num) ha)
      have hbound := supported_norm_le D hD E hS
      rw [← representative_norm, ← hn] at hbound
      exact False.elim (not_lt_of_ge hbound hDz)
  · rintro rfl
    simp [representative_dvd_iff]

/-- Every prime beyond the cutoff has score exactly one. -/
theorem sieveScore_large_prime (D : ℝ) (hD : 1 ≤ D)
    (E : Finset (Associates GaussianInt)) {z : GaussianInt}
    (hz : Prime z) (hDz : D < normMass z) : sieveScore D hD E z = 1 := by
  unfold sieveScore
  have he : (∑ S ∈ (family D hD E).members,
      if representative S ∣ z then weight D hD E S else 0) =
      ∑ S ∈ (family D hD E).members, if S = ∅ then weight D hD E S else 0 := by
    apply sum_congr rfl
    intro S hS
    rw [supported_dvd_large_prime_iff D hD E hS hz hDz]
    by_cases heq : S = ∅ <;> simp only [heq, ite_true, ite_false]
  rw [he]
  simp [(family D hD E).empty_mem, weight_empty]

/-- Even the entire small norm ball, not just its primes, costs at most `9πD`. -/
lemma smallProgression_card_le (a : GaussianInt) (q : ℕ) (R D : ℝ) (hD : 1 ≤ D) :
    (((progression a q R).filter (fun z => normMass z ≤ D)).card : ℝ) ≤
      9 * Real.pi * D := by
  have hD0 : 0 ≤ D := by linarith
  have hsub : (progression a q R).filter (fun z => normMass z ≤ D) ⊆
      gaussianDisk 0 (Real.sqrt D) := by
    intro z hz
    apply (mem_gaussianDisk _ _ _).mpr
    have hn := (mem_filter.mp hz).2
    simpa only [dist_zero_right, gaussian_complex_norm, normMass] using Real.sqrt_le_sqrt hn
  have hc : (((progression a q R).filter (fun z => normMass z ≤ D)).card : ℝ) ≤
      ((gaussianDisk 0 (Real.sqrt D)).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  have hs : 1 ≤ Real.sqrt D := by
    nlinarith [Real.sq_sqrt hD0, Real.sqrt_nonneg D]
  have he := gaussianDisk_card_upper (0 : ℂ) (Real.sqrt_nonneg D)
  have hs2 : (Real.sqrt D + 2) ^ 2 ≤ 9 * D := by
    nlinarith [Real.sq_sqrt hD0]
  apply hc.trans (he.trans _)
  calc
    Real.pi * (Real.sqrt D + 2) ^ 2 ≤ Real.pi * (9 * D) :=
      mul_le_mul_of_nonneg_left hs2 Real.pi_nonneg
    _ = 9 * Real.pi * D := by ring

/-- Pointwise prime majorization, separating only the actual small norm population. -/
lemma primeProgression_card_le_score (a : GaussianInt) (q : ℕ) (R D : ℝ)
    (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    ((primeProgression a q R).card : ℝ) ≤ 9 * Real.pi * D +
      ∑ z ∈ progression a q R, sieveScore D hD E z ^ 2 := by
  have hpoint : ∀ z ∈ progression a q R,
      (if Prime z then (1 : ℝ) else 0) ≤
        (if normMass z ≤ D then (1 : ℝ) else 0) + sieveScore D hD E z ^ 2 := by
    intro z _
    by_cases hz : Prime z
    · by_cases hs : normMass z ≤ D
      · simp only [hz, hs, ite_true]
        nlinarith [sq_nonneg (sieveScore D hD E z)]
      · rw [sieveScore_large_prime D hD E hz (lt_of_not_ge hs)]
        simp [hz, hs]
    · simp only [hz, ite_false]
      split_ifs <;> nlinarith [sq_nonneg (sieveScore D hD E z)]
  have he := sum_le_sum hpoint
  have hsmall := smallProgression_card_le a q R D hD
  have hc : ((primeProgression a q R).card : ℝ) =
      ∑ z ∈ progression a q R, if Prime z then (1 : ℝ) else 0 := by
    simp [primeProgression, ← sum_filter]
  have hs : (((progression a q R).filter (fun z => normMass z ≤ D)).card : ℝ) =
      ∑ z ∈ progression a q R, if normMass z ≤ D then (1 : ℝ) else 0 := by
    simp [← sum_filter]
  rw [sum_add_distrib, ← hc, ← hs] at he
  linarith

/-- Exact expansion over the real progression into its genuine lcm count matrix. -/
theorem sieveScore_second_moment (a : GaussianInt) (q : ℕ) (R D : ℝ)
    (hD : 1 ≤ D) (E : Finset (Associates GaussianInt)) :
    (∑ z ∈ progression a q R, sieveScore D hD E z ^ 2) =
      ∑ S ∈ (family D hD E).members, ∑ T ∈ (family D hD E).members,
        weight D hD E S * weight D hD E T *
          ((divisibleProgression a q (representative (S ∪ T)) R).card : ℝ) := by
  unfold sieveScore
  simp_rw [pow_two, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  have hterm : ∀ z : GaussianInt,
      (if representative S ∣ z then weight D hD E S else 0) *
          (if representative T ∣ z then weight D hD E T else 0) =
        if representative (S ∪ T) ∣ z then weight D hD E S * weight D hD E T else 0 := by
    intro z
    rw [representative_union_dvd]
    split_ifs <;> simp_all
  simp_rw [hterm]
  rw [← sum_filter]
  simp [divisibleProgression, mul_comm]

/-- Signed coefficients are handled by absolute errors before summation. -/
lemma weighted_card_upper (w c m e : ℝ) (he : |c - m| ≤ e) :
    w * c ≤ w * m + |w| * e := by
  have hh : w * (c - m) ≤ |w| * e := calc
    w * (c - m) ≤ |w * (c - m)| := le_abs_self _
    _ = |w| * |c - m| := abs_mul _ _
    _ ≤ |w| * e := mul_le_mul_of_nonneg_left he (abs_nonneg _)
  nlinarith

/-- The finite sieve bound has no residue, coprimality, or mass-growth hypothesis.
The constant counts all prime elements rather than quotienting out their four units. -/
theorem primeProgression_card_upper (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hinert : ∀ p ∈ P, p % 4 = 3)
    (a : GaussianInt) (D : ℝ) (hD : 1 ≤ D) {R : ℝ} (hR : 0 ≤ R) :
    ((primeProgression a (∏ p ∈ P, p) R).card : ℝ) ≤
      9 * Real.pi * D +
      Real.pi * R ^ 2 /
        (((∏ p ∈ P, p : ℕ) : ℝ) ^ 2 * excludedMass D (excludedClasses P)) +
      576 * Real.pi * (R / ((∏ p ∈ P, p : ℕ) : ℝ) + 1) * D ^ 4 := by
  let q : ℕ := ∏ p ∈ P, p
  let E := excludedClasses P
  let F := (family D hD E).members
  let w := weight D hD E
  let A : ℝ := Real.pi * R ^ 2 / (q : ℝ) ^ 2
  let e : ℝ := 4 * Real.pi * (R / (q : ℝ) + 1)
  have hq : 0 < q := prod_pos (fun p hp => (hprime p hp).pos)
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hterm : ∀ S ∈ F, ∀ T ∈ F,
      w S * w T * ((divisibleProgression a q (representative (S ∪ T)) R).card : ℝ) ≤
        A * (w S * w T / normMass (representative (S ∪ T))) +
          e * (|w S| * |w T|) := by
    intro S hS T hT
    have hc := divisibleProgression_card_error a q hq (representative (S ∪ T))
      (representative_ne_zero _) (supported_union_representative_coprime
        P hprime hinert D hD hS hT) hR
    have hh := weighted_card_upper (w S * w T) _ _ e hc
    convert hh using 1 <;> simp only [abs_mul, A, div_eq_mul_inv, mul_inv_rev] <;> ring
  have hmatrix := sum_le_sum (fun S hS => sum_le_sum (fun T hT => hterm S hS T hT))
  have hmain : (∑ S ∈ F, ∑ T ∈ F,
      A * (w S * w T / normMass (representative (S ∪ T)))) = A / excludedMass D E := by
    simp_rw [← mul_sum]
    rw [quadratic_representative D hD E]
    ring
  have herr : (∑ S ∈ F, ∑ T ∈ F, e * (|w S| * |w T|)) =
      e * (∑ S ∈ F, |w S|) ^ 2 := by
    simp_rw [← mul_sum]
    rw [← sum_mul]
    ring
  simp_rw [sum_add_distrib] at hmatrix
  rw [hmain, herr] at hmatrix
  have hbudget := sum_abs_weight_le D hD E
  have hsum0 : 0 ≤ ∑ S ∈ F, |w S| := sum_nonneg (fun _ _ => abs_nonneg _)
  have hbudget2 : (∑ S ∈ F, |w S|) ^ 2 ≤ 144 * D ^ 4 := by
    have hsq := (sq_le_sq₀ hsum0 (show 0 ≤ 12 * D ^ 2 by positivity)).mpr hbudget
    nlinarith
  have herrbound := mul_le_mul_of_nonneg_left hbudget2 he0
  have hscore := primeProgression_card_le_score a q R D hD E
  rw [sieveScore_second_moment] at hscore
  have hm : A / excludedMass D E =
      Real.pi * R ^ 2 / ((q : ℝ) ^ 2 * excludedMass D E) := by
    dsimp [A]
    rw [div_div]
  have he : e * (144 * D ^ 4) =
      576 * Real.pi * (R / (q : ℝ) + 1) * D ^ 4 := by dsimp [e]; ring
  rw [hm] at hmatrix
  rw [he] at herrbound
  change ((primeProgression a q R).card : ℝ) ≤
    9 * Real.pi * D + Real.pi * R ^ 2 / ((q : ℝ) ^ 2 * excludedMass D E) +
      576 * Real.pi * (R / (q : ℝ) + 1) * D ^ 4
  linarith

end DistanceCounts.GaussianSieve
end
end

-- Source: DistanceCounts/GaussianPrimeBounds.lean
section
/-! Uniform polylogarithmic-modulus bounds from the finite Gaussian Selberg sieve. -/

noncomputable section

namespace DistanceCounts.GaussianPrimeBounds

open Filter Finset GaussianMass GaussianSieve
open scoped Topology Classical

/-- The normalized boundary and small-prime errors, independently of the modulus. -/
def normalizedError (A Z : ℝ) : ℝ :=
  9 * Real.pi * ((Real.log Z) ^ (2 * A + 1) / Z ^ (15 / 16 : ℝ)) +
    576 * Real.pi * ((Real.log Z) ^ (A + 1) / Z ^ (1 / 4 : ℝ) +
      (Real.log Z) ^ (2 * A + 1) / Z ^ (3 / 4 : ℝ))

theorem normalizedError_tendsto (A : ℝ) :
    Tendsto (normalizedError A) atTop (𝓝 0) := by
  unfold normalizedError
  have h₁ := (isLittleO_log_rpow_rpow_atTop (2 * A + 1)
    (by norm_num : (0 : ℝ) < 15 / 16)).tendsto_div_nhds_zero
  have h₂ := (isLittleO_log_rpow_rpow_atTop (A + 1)
    (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have h₃ := (isLittleO_log_rpow_rpow_atTop (2 * A + 1)
    (by norm_num : (0 : ℝ) < 3 / 4)).tendsto_div_nhds_zero
  simpa only [normalizedError, mul_zero, zero_add] using
    (h₁.const_mul (9 * Real.pi)).add ((h₂.add h₃).const_mul (576 * Real.pi))

/-- Four excluded inert classes lose only a fixed factor in the logarithmic mass. -/
theorem eventually_excludedMass_log_lower :
    ∃ k : ℝ, 0 < k ∧ ∀ᶠ Z : ℝ in atTop,
      1 ≤ Z ^ (1 / 16 : ℝ) ∧
      ∀ P : Finset ℕ, P.card ≤ 4 →
        (∀ p ∈ P, p.Prime ∧ p % 4 = 3) →
        k * Real.log Z ≤ excludedMass (Z ^ (1 / 16 : ℝ)) (excludedClasses P) := by
  obtain ⟨c, D₀, hc, _, hgrowth⟩ := squarefreeMass_log_growth
  let k : ℝ := c / (16 * (9 / 8 : ℝ) ^ 4)
  refine ⟨k, by dsimp [k]; positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).eventually
      (eventually_ge_atTop (max D₀ 1))] with Z hZ hD
  have hD₁ : 1 ≤ Z ^ (1 / 16 : ℝ) := (le_max_right _ _).trans hD
  refine ⟨hD₁, fun P hcard hP => ?_⟩
  have hm := (hgrowth _ ((le_max_left _ _).trans hD)).trans
    (squarefreeMass_le_inert_excludedMass_four hD₁ P hcard hP)
  rw [Real.log_rpow (by linarith : 0 < Z)] at hm
  change k * Real.log Z ≤
    excludedMass (Z ^ (1 / 16 : ℝ))
      (P.image (fun p : ℕ => Associates.mk (p : GaussianInt)))
  dsimp [k]
  norm_num at hm ⊢
  nlinarith

/-- Exact normalization before the modulus is bounded; in particular no `q` is dropped. -/
lemma sieve_error_normalization {Z q : ℝ} (hZ : 0 < Z) (hq : 0 < q) :
    (9 * Real.pi * Z ^ (1 / 16 : ℝ) +
      576 * Real.pi * (Real.sqrt Z / q + 1) * (Z ^ (1 / 16 : ℝ)) ^ 4) *
        (q ^ 2 * Real.log Z / Z) =
      9 * Real.pi * (q ^ 2 * Real.log Z / Z ^ (15 / 16 : ℝ)) +
        576 * Real.pi * (q * Real.log Z / Z ^ (1 / 4 : ℝ) +
          q ^ 2 * Real.log Z / Z ^ (3 / 4 : ℝ)) := by
  let t := Z ^ (1 / 16 : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos hZ _
  have h16 : t ^ (16 : ℕ) = Z := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hZ.le]
    norm_num
  have h8 : t ^ (8 : ℕ) = Real.sqrt Z := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hZ.le, Real.sqrt_eq_rpow]
    norm_num
  have h15 : t ^ (15 : ℕ) = Z ^ (15 / 16 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hZ.le]
    norm_num
  have h4 : t ^ (4 : ℕ) = Z ^ (1 / 4 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hZ.le]
    norm_num
  have h12 : t ^ (12 : ℕ) = Z ^ (3 / 4 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hZ.le]
    norm_num
  change (9 * Real.pi * t + 576 * Real.pi * (Real.sqrt Z / q + 1) * t ^ 4) *
      (q ^ 2 * Real.log Z / Z) = _
  rw [← h8, ← h15, ← h4, ← h12]
  conv_lhs => arg 2; arg 2; rw [← h16]
  field_simp [ne_of_gt ht, ne_of_gt hq]
  <;> ring

lemma sieve_error_le_normalizedError {A Z q : ℝ} (hZ : 1 < Z) (hq : 0 < q)
    (hqlog : q ≤ (Real.log Z) ^ A) :
    (9 * Real.pi * Z ^ (1 / 16 : ℝ) +
      576 * Real.pi * (Real.sqrt Z / q + 1) * (Z ^ (1 / 16 : ℝ)) ^ 4) *
        (q ^ 2 * Real.log Z / Z) ≤ normalizedError A Z := by
  have hZ₀ : 0 < Z := lt_trans zero_lt_one hZ
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have hqL : q * Real.log Z ≤ (Real.log Z) ^ (A + 1) := by
    rw [Real.rpow_add_one (ne_of_gt hL)]
    exact mul_le_mul_of_nonneg_right hqlog hL.le
  have hq₂L : q ^ 2 * Real.log Z ≤ (Real.log Z) ^ (2 * A + 1) := by
    rw [Real.rpow_add_one (ne_of_gt hL)]
    have he : (Real.log Z) ^ (2 * A) = ((Real.log Z) ^ A) ^ (2 : ℕ) := by
      rw [← Real.rpow_mul_natCast hL.le]
      congr 1
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hq.le (Real.rpow_pos_of_pos hL A).le).mpr hqlog) hL.le
  rw [sieve_error_normalization hZ₀ hq]
  unfold normalizedError
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hq₂L (Real.rpow_pos_of_pos hZ₀ _).le)
      (by positivity))
    (mul_le_mul_of_nonneg_left
      (add_le_add
        (div_le_div_of_nonneg_right hqL (Real.rpow_pos_of_pos hZ₀ _).le)
        (div_le_div_of_nonneg_right hq₂L (Real.rpow_pos_of_pos hZ₀ _).le))
      (by positivity))

/-- Uniform in the residue and in every product of at most four inert rational primes.
The cutoff and constant depend only on `A`, not on the modulus or its prime factors. -/
theorem primeProgression_card_polylog (A : ℝ) (_hA : 0 < A) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ P : Finset ℕ, P.card ≤ 4 →
        (∀ p ∈ P, p.Prime ∧ p % 4 = 3) →
        (((∏ p ∈ P, p : ℕ) : ℝ) ≤ (Real.log Z) ^ A) →
        ∀ a : GaussianInt,
          ((primeProgression a (∏ p ∈ P, p) (Real.sqrt Z)).card : ℝ) ≤
            C * Z / (((∏ p ∈ P, p : ℕ) : ℝ) ^ 2 * Real.log Z) := by
  obtain ⟨k, hk, hmass⟩ := eventually_excludedMass_log_lower
  have herr : ∀ᶠ Z : ℝ in atTop, normalizedError A Z < 1 :=
    (normalizedError_tendsto A).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.mp (hmass.and herr)
  refine ⟨Real.pi / k + 1, max Z₁ 2, by positivity,
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro Z hZ P hcard hP hqlog a
  have hZ₁' := hZ₁ Z ((le_max_left _ _).trans hZ)
  have hZ₂ : 1 < Z := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
    ((le_max_right _ _).trans hZ)
  have hZ₀ : 0 < Z := lt_trans zero_lt_one hZ₂
  have hL : 0 < Real.log Z := Real.log_pos hZ₂
  let q : ℝ := ((∏ p ∈ P, p : ℕ) : ℝ)
  have hq : 0 < q := by
    change (0 : ℝ) < ((∏ p ∈ P, p : ℕ) : ℝ)
    exact_mod_cast (Finset.prod_pos (fun p hp => (hP p hp).1.pos) :
      0 < ∏ p ∈ P, p)
  let M := excludedMass (Z ^ (1 / 16 : ℝ)) (excludedClasses P)
  have hM : k * Real.log Z ≤ M := hZ₁'.1.2 P hcard hP
  have hM₀ : 0 < M := lt_of_lt_of_le (mul_pos hk hL) hM
  let N := q ^ 2 * Real.log Z / Z
  have hN : 0 < N := by dsimp [N]; positivity
  have hfinite := primeProgression_card_upper P (fun p hp => (hP p hp).1)
    (fun p hp => (hP p hp).2) a (Z ^ (1 / 16 : ℝ)) hZ₁'.1.1
    (Real.sqrt_nonneg Z)
  rw [Real.sq_sqrt hZ₀.le] at hfinite
  have hfiniteN := mul_le_mul_of_nonneg_right hfinite hN.le
  have hmain : (Real.pi * Z / (q ^ 2 * M)) * N ≤ Real.pi / k := by
    have he : (Real.pi * Z / (q ^ 2 * M)) * N = Real.pi * Real.log Z / M := by
      dsimp [N]
      field_simp [ne_of_gt hq, ne_of_gt hZ₀, ne_of_gt hM₀]
      <;> ring
    rw [he]
    apply (div_le_iff₀ hM₀).mpr
    have hh := mul_le_mul_of_nonneg_left hM (le_of_lt (div_pos Real.pi_pos hk))
    calc
      Real.pi * Real.log Z = (Real.pi / k) * (k * Real.log Z) := by
        field_simp [ne_of_gt hk]
        <;> ring
      _ ≤ Real.pi / k * M := hh
  have herror := (sieve_error_le_normalizedError hZ₂ hq hqlog).trans hZ₁'.2.le
  have hnormalized :
      ((primeProgression a (∏ p ∈ P, p) (Real.sqrt Z)).card : ℝ) * N ≤
        Real.pi / k + 1 := by
    change _ ≤ (9 * Real.pi * Z ^ (1 / 16 : ℝ) +
      Real.pi * Z / (q ^ 2 * M) +
      576 * Real.pi * (Real.sqrt Z / q + 1) * (Z ^ (1 / 16 : ℝ)) ^ 4) * N
      at hfiniteN
    change (9 * Real.pi * Z ^ (1 / 16 : ℝ) +
      576 * Real.pi * (Real.sqrt Z / q + 1) * (Z ^ (1 / 16 : ℝ)) ^ 4) * N ≤ 1
      at herror
    nlinarith [hfiniteN, hmain, herror]
  have hfinal := (le_div_iff₀ hN).mpr hnormalized
  change _ ≤ (Real.pi / k + 1) * Z / (q ^ 2 * Real.log Z)
  have heq : (Real.pi / k + 1) / N =
      (Real.pi / k + 1) * Z / (q ^ 2 * Real.log Z) := by
    dsimp [N]
    field_simp [ne_of_gt hq, ne_of_gt hL, ne_of_gt hZ₀]
    <;> ring
  exact hfinal.trans_eq heq

/-- A finite residue family costs at most its cardinality; overlaps only improve the bound. -/
theorem primeProgression_biUnion_card_polylog (A : ℝ) (hA : 0 < A) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ P : Finset ℕ, P.card ≤ 4 →
        (∀ p ∈ P, p.Prime ∧ p % 4 = 3) →
        (((∏ p ∈ P, p : ℕ) : ℝ) ≤ (Real.log Z) ^ A) →
        ∀ F : Finset GaussianInt,
          ((F.biUnion (fun a => primeProgression a (∏ p ∈ P, p)
            (Real.sqrt Z))).card : ℝ) ≤
            (F.card : ℝ) * (C * Z /
              (((∏ p ∈ P, p : ℕ) : ℝ) ^ 2 * Real.log Z)) := by
  obtain ⟨C, Z₀, hC, hZ₀, hbound⟩ := primeProgression_card_polylog A hA
  refine ⟨C, Z₀, hC, hZ₀, fun Z hZ P hcard hP hq F => ?_⟩
  calc
    _ ≤ ∑ a ∈ F, ((primeProgression a (∏ p ∈ P, p) (Real.sqrt Z)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (F.biUnion (fun a => primeProgression a (∏ p ∈ P, p) (Real.sqrt Z))).card ≤
          ∑ a ∈ F, (primeProgression a (∏ p ∈ P, p) (Real.sqrt Z)).card)
    _ ≤ ∑ _a ∈ F, C * Z /
        (((∏ p ∈ P, p : ℕ) : ℝ) ^ 2 * Real.log Z) :=
      Finset.sum_le_sum (fun a _ => hbound Z hZ P hcard hP hq a)
    _ = _ := by simp

end DistanceCounts.GaussianPrimeBounds
end
end

-- Source: DistanceCounts/LargeFlipCount.lean
section
/-! A finite prime sieve for actual large conjugate-prime flips. -/

noncomputable section

namespace DistanceCounts.LargeFlipCount

open Finset GaussianMass GaussianDivisibility GaussianNorm GaussianResidues
open GaussianProgressions GaussianSieve
open scoped Classical

/-- Actual nonzero vectors, with genuine prime and equal-norm flip witnesses.
The witness is allowed to be the vector itself. -/
def largeFlipVectors (q : ℕ) (R Y T : ℝ) : Finset GaussianInt :=
  ((gaussianDisk 0 R).erase 0).filter fun z =>
    IsUnit (residue q z) ∧ ((normCircle z.norm.natAbs).card : ℝ) ≤ T ∧
    ∃ π : GaussianInt, Prime π ∧ Y ≤ normMass π ∧ π ∣ z ∧
      ∃ w ∈ normCircle z.norm.natAbs, (q : GaussianInt) ∣ z - w ∧ star π ∣ w

lemma mem_largeFlipVectors (q : ℕ) (R Y T : ℝ) (z : GaussianInt) :
    z ∈ largeFlipVectors q R Y T ↔
      z ≠ 0 ∧ ‖(z : ℂ)‖ ≤ R ∧ IsUnit (residue q z) ∧
      ((normCircle z.norm.natAbs).card : ℝ) ≤ T ∧
      ∃ π : GaussianInt, Prime π ∧ Y ≤ normMass π ∧ π ∣ z ∧
        ∃ w ∈ normCircle z.norm.natAbs, (q : GaussianInt) ∣ z - w ∧ star π ∣ w := by
  simp [largeFlipVectors, mem_gaussianDisk, and_assoc]

/-- Multiplication injects the smaller genuine norm circle into the larger one. -/
theorem normCircle_card_mul_le (π u : GaussianInt) (hπ : π ≠ 0) :
    (normCircle u.norm.natAbs).card ≤ (normCircle (π * u).norm.natAbs).card := by
  apply Finset.card_le_card_of_injOn (fun v => π * v)
  · intro v hv
    apply (mem_normCircle _ _).mpr
    simp only [Zsqrtd.norm_mul, Int.natAbs_mul, (mem_normCircle _ _).mp hv]
  · intro v _ w _ h
    exact mul_left_cancel₀ hπ h

/-- The finite solutions of one ratio equation in the actual quotient. -/
def ratioResidues (q : ℕ) (hq : 0 < q) (u v : GaussianInt) : Finset (Residue q) := by
  letI : Finite (Residue q) := finite_residue q hq
  letI : Fintype {a : Residue q //
      a * residue q u = conjugate q a * residue q v} := Fintype.ofFinite _
  exact (Finset.univ : Finset {a : Residue q //
    a * residue q u = conjugate q a * residue q v}).image Subtype.val

lemma mem_ratioResidues (q : ℕ) (hq : 0 < q) (u v : GaussianInt) (a : Residue q) :
    a ∈ ratioResidues q hq u v ↔
      a * residue q u = conjugate q a * residue q v := by
  letI : Finite (Residue q) := finite_residue q hq
  letI : Fintype {a : Residue q //
      a * residue q u = conjugate q a * residue q v} := Fintype.ofFinite _
  dsimp only [ratioResidues]
  simp

lemma ratioResidues_card (q : ℕ) (hq : 0 < q) (u v : GaussianInt) :
    (ratioResidues q hq u v).card =
      Nat.card {a : Residue q // a * residue q u = conjugate q a * residue q v} := by
  letI : Finite (Residue q) := finite_residue q hq
  letI : Fintype {a : Residue q //
      a * residue q u = conjugate q a * residue q v} := Fintype.ofFinite _
  dsimp only [ratioResidues]
  rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
  exact Nat.card_eq_fintype_card.symm

/-- Actual Gaussian lifts of the union of the equal-norm ratio fibers. -/
def ratioLifts (q : ℕ) (hq : 0 < q) (u : GaussianInt) : Finset GaussianInt :=
  ((normCircle u.norm.natAbs).biUnion (ratioResidues q hq u)).image Quotient.out

lemma ratioLifts_card_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3)
    (hq : 0 < ∏ p ∈ P, p) (u : GaussianInt)
    (hu : IsUnit (residue (∏ p ∈ P, p) u)) :
    (ratioLifts (∏ p ∈ P, p) hq u).card ≤
      (∏ p ∈ P, p) * (normCircle u.norm.natAbs).card := by
  have hlocal (p : P) :
      crtReduction P (residue (∏ p ∈ P, p) u) p ≠ 0 := by
    have hunit := hu.map (reduce (Finset.dvd_prod_of_mem (fun p : ℕ => p) p.2))
    exact (isUnit_iff_ne_zero_inert p.1 (hP p.1 p.2).1 (hP p.1 p.2).2 _).mp hunit
  calc
    _ ≤ ((normCircle u.norm.natAbs).biUnion
        (ratioResidues (∏ p ∈ P, p) hq u)).card := Finset.card_image_le
    _ ≤ ∑ v ∈ normCircle u.norm.natAbs,
        (ratioResidues (∏ p ∈ P, p) hq u v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ normCircle u.norm.natAbs, (∏ p ∈ P, p) := by
      apply Finset.sum_le_sum
      intro v _
      rw [ratioResidues_card]
      exact card_ratio_fiber_product P (fun p hp => (hP p hp).1)
        (fun p hp => (hP p hp).2) _ _ hlocal
    _ = _ := by simp [Nat.mul_comm]

/-- Cofactors retain the unit and representation-count restrictions of the vector. -/
def cofactors (q : ℕ) (R Y T : ℝ) : Finset GaussianInt :=
  (representatives (R ^ 2 / Y)).filter fun u =>
    IsUnit (residue q u) ∧ ((normCircle u.norm.natAbs).card : ℝ) ≤ T

/-- Each prime is counted in genuine lifted progressions at its exact norm scale. -/
def primeCandidates (q : ℕ) (hq : 0 < q) (R : ℝ) (u : GaussianInt) : Finset GaussianInt :=
  (ratioLifts q hq u).biUnion fun a =>
    primeProgression a q (Real.sqrt (R ^ 2 / normMass u))

/-- All cofactor, norm, radius, representation, and quotient facts follow from
an actual flip. No residue family is supplied as a hypothesis. -/
theorem largeFlip_factorization {q : ℕ} {R Y T : ℝ} (hR : 0 ≤ R) (hY : 0 < Y)
    {z : GaussianInt} (hz : z ∈ largeFlipVectors q R Y T) :
    ∃ π u v : GaussianInt, Prime π ∧ z = π * u ∧
      u ∈ cofactors q R Y T ∧ v ∈ normCircle u.norm.natAbs ∧
      normMass π ≤ R ^ 2 / normMass u ∧
      residue q π * residue q u = conjugate q (residue q π) * residue q v := by
  obtain ⟨hz0, hzR, hzunit, hzT, π, hπ, hYπ, ⟨u, hzu⟩,
    w, hw, hzw, ⟨v, hwv⟩⟩ := (mem_largeFlipVectors q R Y T z).mp hz
  have hu0 : u ≠ 0 := by intro h; simp [h] at hzu; exact hz0 hzu
  have huN : 0 < normMass u := lt_of_lt_of_le zero_lt_one (one_le_normMass hu0)
  have hπN : 0 < π.norm.natAbs :=
    Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hπ.ne_zero)
  have hnorm : π.norm.natAbs * v.norm.natAbs = π.norm.natAbs * u.norm.natAbs := by
    have h := (mem_normCircle _ _).mp hw
    simpa only [hwv, hzu, Zsqrtd.norm_mul, Zsqrtd.norm_conj, Int.natAbs_mul] using h
  have hvu : v.norm.natAbs = u.norm.natAbs := Nat.eq_of_mul_eq_mul_left hπN hnorm
  have hzN : normMass z ≤ R ^ 2 := by
    rw [normMass_eq_sq_norm]
    exact (sq_le_sq₀ (norm_nonneg (z : ℂ)) hR).mpr hzR
  have hprod : normMass π * normMass u ≤ R ^ 2 := by
    simpa only [hzu, normMass_mul] using hzN
  have huY : normMass u ≤ R ^ 2 / Y := by
    apply (le_div_iff₀ hY).mpr
    exact (by nlinarith [mul_le_mul_of_nonneg_right hYπ huN.le] :
      normMass u * Y ≤ R ^ 2)
  have huunit : IsUnit (residue q u) := by
    apply isUnit_of_mul_isUnit_right (x := residue q π)
    simpa only [hzu, residue, map_mul] using hzunit
  have huT : ((normCircle u.norm.natAbs).card : ℝ) ≤ T := by
    have hh : ((normCircle u.norm.natAbs).card : ℝ) ≤
        (normCircle (π * u).norm.natAbs).card := by
      exact_mod_cast normCircle_card_mul_le π u hπ.ne_zero
    exact hh.trans (by simpa only [hzu] using hzT)
  refine ⟨π, u, v, hπ, hzu, ?_, (mem_normCircle _ _).mpr hvu,
    (le_div_iff₀ huN).mpr hprod, ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨(mem_representatives (div_nonneg (sq_nonneg R) hY.le) u).mpr
        ⟨hu0, huY⟩, huunit, huT⟩
  · have he : residue q z = residue q w :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hzw)
    rw [conjugate_residue]
    simpa only [hzu, hwv, residue, map_mul] using he

/-- Explicit incidence inclusion into products of actual prime progression populations. -/
theorem largeFlipVectors_subset (q : ℕ) (hq : 0 < q) {R Y T : ℝ}
    (hR : 0 ≤ R) (hY : 0 < Y) :
    largeFlipVectors q R Y T ⊆
      (cofactors q R Y T).biUnion fun u =>
        (primeCandidates q hq R u).image (fun π => π * u) := by
  intro z hz
  obtain ⟨π, u, v, hπ, rfl, hu, hv, hπR, he⟩ := largeFlip_factorization hR hY hz
  apply Finset.mem_biUnion.mpr
  refine ⟨u, hu, Finset.mem_image.mpr ⟨π, ?_, rfl⟩⟩
  apply Finset.mem_biUnion.mpr
  let a : GaussianInt := Quotient.out (residue q π)
  have ha : a ∈ ratioLifts q hq u := by
    letI : DecidableEq (Residue q) := fun a b => Classical.propDecidable (a = b)
    apply Finset.mem_image.mpr
    refine ⟨residue q π, Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩, rfl⟩
    exact (mem_ratioResidues q hq u v _).mpr he
  refine ⟨a, ha, Finset.mem_filter.mpr ⟨?_, hπ⟩⟩
  apply (mem_progression a π q _).mpr
  constructor
  · simp only [dist_zero_right, gaussian_complex_norm]
    exact Real.sqrt_le_sqrt hπR
  · apply Ideal.mem_span_singleton.1
    apply Ideal.Quotient.eq.1
    exact (Ideal.Quotient.mk_out (residue q π)).symm

/-- Uniform finite sieve bound, prior to any estimate of the logarithmic sum. -/
theorem largeFlipVectors_card_polylog (A : ℝ) (hA : 0 < A) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧
      ∀ P : Finset ℕ, P.card ≤ 4 →
        (∀ p ∈ P, p.Prime ∧ p % 4 = 3) →
        ∀ R Y T : ℝ, 0 ≤ R → max Z₀ 2 ≤ Y → 0 ≤ T →
        (((∏ p ∈ P, p : ℕ) : ℝ) ≤ (Real.log Y) ^ A) →
        ((largeFlipVectors (∏ p ∈ P, p) R Y T).card : ℝ) ≤
          C * (T / ((∏ p ∈ P, p : ℕ) : ℝ)) * R ^ 2 *
            ∑ u ∈ representatives (R ^ 2 / Y),
              1 / (normMass u * Real.log (R ^ 2 / normMass u)) := by
  obtain ⟨C, Z₀, hC, hZ₀, hbound⟩ :=
    GaussianPrimeBounds.primeProgression_biUnion_card_polylog A hA
  refine ⟨C, Z₀, hC, hZ₀, ?_⟩
  intro P hfour hP R Y T hR hY hT hqlog
  let q : ℕ := ∏ p ∈ P, p
  have hq : 0 < q := Finset.prod_pos fun p hp => (hP p hp).1.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hY₁ : 1 < Y := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hY)
  have hY₀ : 0 < Y := zero_lt_one.trans hY₁
  have hscale (u : GaussianInt) (hu : u ∈ representatives (R ^ 2 / Y)) :
      0 < normMass u ∧ Y ≤ R ^ 2 / normMass u := by
    obtain ⟨hu0, huR⟩ :=
      (mem_representatives (div_nonneg (sq_nonneg R) hY₀.le) u).mp hu
    have huN : 0 < normMass u := lt_of_lt_of_le zero_lt_one (one_le_normMass hu0)
    refine ⟨huN, (le_div_iff₀ huN).mpr ?_⟩
    have hh := (le_div_iff₀ hY₀).mp huR
    have normMass_eq_natNorm : normMass u = (u.norm.natAbs : ℝ) := rfl
    simpa only [normMass_eq_natNorm, mul_comm] using hh
  have hprime (u : GaussianInt) (hu : u ∈ cofactors q R Y T) :
      ((primeCandidates q hq R u).card : ℝ) ≤
        C * (T / (q : ℝ)) * R ^ 2 *
          (1 / (normMass u * Real.log (R ^ 2 / normMass u))) := by
    obtain ⟨huR, huunit, huT⟩ := Finset.mem_filter.mp hu
    obtain ⟨huN, huY⟩ := hscale u huR
    have hZ : Z₀ ≤ R ^ 2 / normMass u :=
      ((le_max_left _ _).trans hY).trans huY
    have hlog : 0 < Real.log (R ^ 2 / normMass u) := Real.log_pos (hY₁.trans_le huY)
    have hqZ : (q : ℝ) ≤ (Real.log (R ^ 2 / normMass u)) ^ A :=
      hqlog.trans (Real.rpow_le_rpow (Real.log_pos hY₁).le
        (Real.log_le_log hY₀ huY) hA.le)
    have hf : ((ratioLifts q hq u).card : ℝ) ≤ (q : ℝ) * T := by
      have hh : ((ratioLifts q hq u).card : ℝ) ≤
          (q : ℝ) * ((normCircle u.norm.natAbs).card : ℝ) := by
        exact_mod_cast ratioLifts_card_le P hP hq u huunit
      exact hh.trans (mul_le_mul_of_nonneg_left huT hqR.le)
    calc
      _ ≤ ((ratioLifts q hq u).card : ℝ) *
          (C * (R ^ 2 / normMass u) / ((q : ℝ) ^ 2 * Real.log (R ^ 2 / normMass u))) :=
        hbound _ hZ P hfour hP hqZ (ratioLifts q hq u)
      _ ≤ ((q : ℝ) * T) *
          (C * (R ^ 2 / normMass u) / ((q : ℝ) ^ 2 * Real.log (R ^ 2 / normMass u))) :=
        mul_le_mul_of_nonneg_right hf (by positivity)
      _ = _ := by
        field_simp [ne_of_gt hqR, ne_of_gt huN, ne_of_gt hlog]
        <;> ring
  have hnonneg (u : GaussianInt) (hu : u ∈ representatives (R ^ 2 / Y)) :
      0 ≤ C * (T / (q : ℝ)) * R ^ 2 *
        (1 / (normMass u * Real.log (R ^ 2 / normMass u))) := by
    obtain ⟨huN, huY⟩ := hscale u hu
    have : 0 < Real.log (R ^ 2 / normMass u) := Real.log_pos (hY₁.trans_le huY)
    positivity
  calc
    _ ≤ (((cofactors q R Y T).biUnion fun u =>
        (primeCandidates q hq R u).image (fun π => π * u)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (largeFlipVectors_subset q hq hR hY₀)
    _ ≤ ∑ u ∈ cofactors q R Y T,
        (((primeCandidates q hq R u).image (fun π => π * u)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        ((cofactors q R Y T).biUnion fun u =>
          (primeCandidates q hq R u).image (fun π => π * u)).card ≤ _)
    _ ≤ ∑ u ∈ cofactors q R Y T, ((primeCandidates q hq R u).card : ℝ) := by
      apply Finset.sum_le_sum
      intro u _
      exact_mod_cast (Finset.card_image_le :
        ((primeCandidates q hq R u).image (fun π => π * u)).card ≤ _)
    _ ≤ ∑ u ∈ cofactors q R Y T, C * (T / (q : ℝ)) * R ^ 2 *
        (1 / (normMass u * Real.log (R ^ 2 / normMass u))) :=
      Finset.sum_le_sum hprime
    _ ≤ ∑ u ∈ representatives (R ^ 2 / Y), C * (T / (q : ℝ)) * R ^ 2 *
        (1 / (normMass u * Real.log (R ^ 2 / normMass u))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun u hu _ => hnonneg u hu)
    _ = _ := by rw [← Finset.mul_sum]

end DistanceCounts.LargeFlipCount
end
end

-- Source: DistanceCounts/HighCollisionCover.lean
section
/-! The exact arithmetic cover of genuine unit-residue collisions. -/

noncomputable section

namespace DistanceCounts.HighCollisionCover

open Finset GaussianMass GaussianDivisibility GaussianNorm GaussianPrimeWeight
open GaussianSmoothPart SmallFlipLattice LargeFlipCount
open scoped Classical

/-- Actual nonzero vectors with a distinct equal-norm partner in the same disk
and the same unit residue class. -/
def collisionVectors (q : ℕ) (R : ℝ) : Finset GaussianInt :=
  ((gaussianDisk 0 R).erase 0).filter fun z =>
    IsUnit (residue q z) ∧ ∃ w ∈ gaussianDisk 0 R,
      w ≠ z ∧ z.norm = w.norm ∧ residue q z = residue q w

lemma mem_collisionVectors (q : ℕ) (R : ℝ) (z : GaussianInt) :
    z ∈ collisionVectors q R ↔ z ≠ 0 ∧ ‖(z : ℂ)‖ ≤ R ∧
      IsUnit (residue q z) ∧ ∃ w ∈ gaussianDisk 0 R,
        w ≠ z ∧ z.norm = w.norm ∧ residue q z = residue q w := by
  simp [collisionVectors, mem_gaussianDisk, and_assoc]

/-- The actual excessive-representation population, with a strict cutoff. -/
def excessiveRepresentations (R T : ℝ) : Finset GaussianInt :=
  (representatives (R ^ 2)).filter fun z =>
    T < ((normCircle z.norm.natAbs).card : ℝ)

/-- A lifted inverse gives Bezout coefficients with the actual modulus. -/
theorem isCoprime_of_unit_residue {q : ℕ} {z : GaussianInt}
    (hz : IsUnit (residue q z)) : IsCoprime (q : GaussianInt) z := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv'.mp hz
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a
  have he : residue q (b * z) = residue q 1 := by
    simpa only [residue, map_mul, map_one, hb] using ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  refine ⟨-c, b, ?_⟩
  linear_combination hc

/-- Unit residues are coprime to the genuine common factor, not merely to an
assumed primitive cofactor. -/
theorem isCoprime_gcd_of_unit_residue {q : ℕ} {z w : GaussianInt}
    (hz : IsUnit (residue q z)) :
    IsCoprime (q : GaussianInt) (EuclideanDomain.gcd z w) :=
  (isCoprime_of_unit_residue hz).of_isCoprime_of_dvd_right
    (EuclideanDomain.gcd_dvd_left z w)

/-- Inert prime products are positive and odd, including the empty product. -/
theorem inert_product_pos_odd (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3) :
    0 < ∏ p ∈ P, p ∧ Odd (∏ p ∈ P, p) := by
  refine ⟨Finset.prod_pos (fun p hp => (hP p hp).1.pos), ?_⟩
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | @insert p P hp ih =>
    intro hP
    rw [Finset.prod_insert hp]
    have hpodd : Odd p := Nat.odd_iff.mpr (by
      have := (hP p (Finset.mem_insert_self p P)).2
      omega)
    exact hpodd.mul (ih (fun r hr => hP r (Finset.mem_insert_of_mem hr)))

/-- Divisibility of nonzero associate classes is detected by every actual
prime multiplicity. -/
private lemma dvd_of_counts_le {a b : Associates GaussianInt}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : Associates GaussianInt, Irreducible p →
      p.count a.factors ≤ p.count b.factors) : a ∣ b := by
  apply Associates.factors_le.mp
  obtain ⟨sa, hsa⟩ := Associates.factors_eq_some_iff_ne_zero.mpr ha
  obtain ⟨sb, hsb⟩ := Associates.factors_eq_some_iff_ne_zero.mpr hb
  rw [hsa, hsb, WithTop.coe_le_coe]
  apply Multiset.le_iff_count.mpr
  intro p
  have hp := h p.1 p.2
  simpa only [hsa, hsb, Associates.count_some p.2] using hp

/-- Full prime-power multiplicities are retained: any actual divisor supported
on the cutoff classes divides the genuine small-prime part. -/
theorem divisor_dvd_smallPartY {Y : ℝ} {v z : GaussianInt}
    (hv : v ≠ 0) (hz : z ≠ 0) (hvz : v ∣ z)
    (hsupport : ∀ p : Associates GaussianInt, Prime p →
      p ∣ Associates.mk v → p ∈ primeClassesY Y) :
    Associates.mk v ∣ smallPartY Y z := by
  apply dvd_of_counts_le (Associates.mk_ne_zero.mpr hv) (smallPartY_ne_zero Y z)
  intro p hp
  by_cases hc : p.count (Associates.mk v).factors = 0
  · rw [hc]
    exact Nat.zero_le _
  have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
  have hmem : p ∈ primeClassesY Y :=
    hsupport p hprime (Associates.le_of_count_ne_zero (Associates.mk_ne_zero.mpr hv) hp hc)
  have hcount : p.count (Associates.mk v).factors ≤ valuation p z :=
    Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hz) hp
      (Associates.mk_dvd_mk.mpr hvz)
  have hpow : p ^ valuation p z ∣ smallPartY Y z :=
    Finset.dvd_prod_of_mem (fun r => r ^ valuation r z) hmem
  have hbound : valuation p z ≤ p.count (smallPartY Y z).factors :=
    (Associates.prime_pow_dvd_iff_le (smallPartY_ne_zero Y z) hp).mp hpow
  exact hcount.trans hbound

/-- If the primitive factor exceeds the actual smooth part, it has an actual
large Gaussian prime divisor. No squarefree restriction occurs. -/
theorem exists_large_prime_divisor {Y S : ℝ} (hY : 0 ≤ Y)
    {v z : GaussianInt} (hv : v ≠ 0) (hz : z ≠ 0) (hvz : v ∣ z)
    (hSv : S < normMass v) (hzS : (classNorm (smallPartY Y z) : ℝ) ≤ S) :
    ∃ π : GaussianInt, Prime π ∧ Y < normMass π ∧ π ∣ v := by
  have hex : ∃ p : Associates GaussianInt,
      Prime p ∧ p ∣ Associates.mk v ∧ p ∉ primeClassesY Y := by
    by_contra h
    have hs : ∀ p : Associates GaussianInt, Prime p →
        p ∣ Associates.mk v → p ∈ primeClassesY Y := by
      intro p hp hd
      by_contra hn
      exact h ⟨p, hp, hd, hn⟩
    have hd := divisor_dvd_smallPartY hv hz hvz hs
    have hn : normMass v ≤ (classNorm (smallPartY Y z) : ℝ) := by
      have hn' := classNorm_le_of_dvd (smallPartY_ne_zero Y z) hd
      rw [classNorm_mk] at hn'
      change (v.norm.natAbs : ℝ) ≤ _
      exact_mod_cast hn'
    exact (not_lt_of_ge (hn.trans hzS)) hSv
  obtain ⟨p, hp, hd, hnot⟩ := hex
  obtain ⟨π, rfl⟩ := Associates.mk_surjective p
  refine ⟨π, Associates.prime_mk.mp hp, ?_, Associates.mk_dvd_mk.mp hd⟩
  have hlarge : Y < (classNorm (Associates.mk π) : ℝ) := by
    by_contra h
    exact hnot ((mem_primeClassesY hY _).mpr ⟨hp, le_of_not_gt h⟩)
  exact hlarge

/-- The concrete four-set cover follows solely from collision, gcd, unit,
valuation, and norm facts. The modulus may have any number of inert prime
factors; in particular this applies to the at-most-four-prime sieve moduli. -/
theorem collisionVectors_subset (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3)
    {R Y S T : ℝ} (hR : 0 ≤ R) (hY : 0 ≤ Y) :
    collisionVectors (∏ p ∈ P, p) R ⊆
      excessiveRepresentations R T ∪ GaussianSmoothPart.exceptional R Y S ∪
        smallFlipDivisibleVectors (∏ p ∈ P, p) S R ∪
          largeFlipVectors (∏ p ∈ P, p) R Y T := by
  intro z hz
  obtain ⟨hz0, hzR, hzunit, w, _hwR, hwz, hn, hres⟩ :=
    (mem_collisionVectors _ _ _).mp hz
  have hzN : normMass z ≤ R ^ 2 := by
    rw [normMass_eq_sq_norm]
    exact (sq_le_sq₀ (norm_nonneg (z : ℂ)) hR).mpr hzR
  have hzrep : z ∈ representatives (R ^ 2) :=
    (mem_representatives (sq_nonneg R) z).mpr ⟨hz0, hzN⟩
  by_cases hzT : T < ((normCircle z.norm.natAbs).card : ℝ)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzrep, hzT⟩)))
  by_cases hzS : S < (classNorm (smallPartY Y z) : ℝ)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzrep, hzS⟩)))
  obtain ⟨hq, hqodd⟩ := inert_product_pos_odd P hP
  have hw0 : w ≠ 0 := by
    intro hw
    apply hz0
    apply GaussianInt.norm_eq_zero.mp
    simpa only [hw, Zsqrtd.norm_zero] using hn
  have hd : ((∏ p ∈ P, p : ℕ) : GaussianInt) ∣ z - w :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hres)
  obtain ⟨g, v, u, _hgcd, _hvdiv, _hg, hv, hzv, hwv, _hprim, htrans⟩ :=
    PrimitiveNormPairs.collision_decomposition hq hqodd hz0 hw0 hn hwz hd
      (isCoprime_gcd_of_unit_residue hzunit)
  have hvz : v ∣ z := by
    rw [hzv]
    exact dvd_mul_left v g
  by_cases hvS : normMass v ≤ S
  · have hvr : ‖(v : ℂ)‖ ≤ Real.sqrt S := by
      rw [normMass_eq_sq_norm] at hvS
      exact (Real.le_sqrt (norm_nonneg _) (le_trans (sq_nonneg _) hvS)).mpr hvS
    have hvsmall : v ∈ smallFlipVectors (∏ p ∈ P, p) S :=
      (mem_smallFlipVectors _ _ _).mpr ⟨hv, hvr, htrans⟩
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      ((mem_smallFlipDivisibleVectors _ _ _ _).mpr ⟨hz0, hzR, v, hvsmall, hvz⟩))
  · obtain ⟨π, hπ, hYπ, hπv⟩ := exists_large_prime_divisor hY hv hz0 hvz
      (lt_of_not_ge hvS) (le_of_not_gt hzS)
    have hstar : star π ∣ star v := by
      obtain ⟨a, ha⟩ := hπv
      exact ⟨star a, by simp only [ha, star_mul, mul_comm]⟩
    have hπw : star π ∣ w := by
      rw [hwv]
      exact dvd_mul_of_dvd_right hstar (g * (u : GaussianInt))
    apply Finset.mem_union_right
    apply (mem_largeFlipVectors _ _ _ _ _).mpr
    refine ⟨hz0, hzR, hzunit, le_of_not_gt hzT, π, hπ, hYπ.le,
      hπv.trans hvz, w, ?_, hd, hπw⟩
    exact (mem_normCircle _ _).mpr (congrArg Int.natAbs hn.symm)

end DistanceCounts.HighCollisionCover
end
end

-- Source: DistanceCounts/ResidueExceptions.lean
section
noncomputable section

namespace DistanceCounts.ResidueExceptions

open Finset
open scoped Classical

/-- The actual colliding vectors in one canonical quotient class. -/
def collisionFiber (q : ℕ) (R : ℝ) (a : GaussianResidues.Residue q) :
    Finset GaussianInt :=
  (HighCollisionCover.collisionVectors q R).filter
    (fun z => GaussianNorm.residue q z = a)

lemma mem_collisionFiber (q : ℕ) (R : ℝ) (a : GaussianResidues.Residue q)
    (z : GaussianInt) :
    z ∈ collisionFiber q R a ↔
      z ∈ HighCollisionCover.collisionVectors q R ∧ GaussianNorm.residue q z = a := by
  exact mem_filter

/-- Every actual collision belongs to exactly one residue fiber. -/
theorem sum_collisionFiber_card (q : ℕ) (hq : 0 < q) (R : ℝ) :
    ∑ a ∈ LowPalette.allResidues q hq, (collisionFiber q R a).card =
      (HighCollisionCover.collisionVectors q R).card := by
  exact (card_eq_sum_card_fiberwise
    (f := GaussianNorm.residue q)
    (s := HighCollisionCover.collisionVectors q R)
    (t := LowPalette.allResidues q hq)
    (fun z _ => LowPalette.mem_allResidues q hq (GaussianNorm.residue q z))).symm

theorem sum_collisionFiber_card_real (q : ℕ) (hq : 0 < q) (R : ℝ) :
    ∑ a ∈ LowPalette.allResidues q hq, ((collisionFiber q R a).card : ℝ) =
      ((HighCollisionCover.collisionVectors q R).card : ℝ) := by
  exact_mod_cast sum_collisionFiber_card q hq R


/-- Low residues are exceptional for their actual distinct-norm palette. -/
def badLow (q : ℕ) (hq : 0 < q) (R H : ℝ) : Finset (GaussianResidues.Residue q) :=
  (LowPalette.allResidues q hq).filter
    (fun a => H < ((LowPalette.normPalette a R).card : ℝ))

/-- High residues are exceptional for their actual colliding-vector population. -/
def badHigh (q : ℕ) (hq : 0 < q) (R H : ℝ) : Finset (GaussianResidues.Residue q) :=
  (LowPalette.allResidues q hq).filter
    (fun a => H < ((collisionFiber q R a).card : ℝ))

lemma mem_badLow (q : ℕ) (hq : 0 < q) (R H : ℝ)
    (a : GaussianResidues.Residue q) :
    a ∈ badLow q hq R H ↔ H < ((LowPalette.normPalette a R).card : ℝ) := by
  simp [badLow, LowPalette.mem_allResidues]

lemma mem_badHigh (q : ℕ) (hq : 0 < q) (R H : ℝ)
    (a : GaussianResidues.Residue q) :
    a ∈ badHigh q hq R H ↔ H < ((collisionFiber q R a).card : ℝ) := by
  simp [badHigh, LowPalette.mem_allResidues]

lemma palette_card_le_of_not_badLow {q : ℕ} {hq : 0 < q} {R H : ℝ}
    {a : GaussianResidues.Residue q} (ha : a ∉ badLow q hq R H) :
    ((LowPalette.normPalette a R).card : ℝ) ≤ H :=
  le_of_not_gt (fun h => ha ((mem_badLow q hq R H a).mpr h))

lemma collisionFiber_card_le_of_not_badHigh {q : ℕ} {hq : 0 < q} {R H : ℝ}
    {a : GaussianResidues.Residue q} (ha : a ∉ badHigh q hq R H) :
    ((collisionFiber q R a).card : ℝ) ≤ H :=
  le_of_not_gt (fun h => ha ((mem_badHigh q hq R H a).mpr h))

/-- Finite Markov inequality, proved directly from the actual nonnegative sum. -/
private theorem card_filter_mul_le_sum {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) (H : ℝ) :
    ((s.filter (fun a => H < f a)).card : ℝ) * H ≤ ∑ a ∈ s, f a := by
  calc
    _ = ∑ _a ∈ s.filter (fun a => H < f a), H := by simp
    _ ≤ ∑ a ∈ s.filter (fun a => H < f a), f a :=
      sum_le_sum (fun a ha => (mem_filter.mp ha).2.le)
    _ ≤ ∑ a ∈ s, f a :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun a ha _ => hf a ha)

/-- No distribution premise is needed; even the threshold need not be positive. -/
theorem badLow_card_mul_le (q : ℕ) (hq : 0 < q) (R H : ℝ) :
    ((badLow q hq R H).card : ℝ) * H ≤ LowPalette.aggregate q hq R := by
  exact card_filter_mul_le_sum (LowPalette.allResidues q hq)
    (fun a => ((LowPalette.normPalette a R).card : ℝ))
    (fun _ _ => Nat.cast_nonneg _) H

theorem badHigh_card_mul_le (q : ℕ) (hq : 0 < q) (R H : ℝ) :
    ((badHigh q hq R H).card : ℝ) * H ≤
      ((HighCollisionCover.collisionVectors q R).card : ℝ) := by
  have h := card_filter_mul_le_sum (LowPalette.allResidues q hq)
    (fun a => ((collisionFiber q R a).card : ℝ))
    (fun _ _ => Nat.cast_nonneg _) H
  rw [sum_collisionFiber_card_real] at h
  exact h

/-- Cancellation uses the positive threshold, never the error rate. -/
private theorem normalized_markov {B A C Q L τ R : ℝ}
    (hC : 0 < C) (hQ : 0 < Q) (hL : 0 < L) (hτ : 0 < τ)
    (hR : R = C * Q * L) (h : B * (τ * L ^ 2) ≤ A) :
    B / Q ^ 2 ≤ C ^ 2 * A / R ^ 2 / τ := by
  have hH : 0 < τ * L ^ 2 := mul_pos hτ (sq_pos_of_pos hL)
  calc
    B / Q ^ 2 ≤ (A / (τ * L ^ 2)) / Q ^ 2 :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hH).mpr h) (sq_nonneg Q)
    _ = C ^ 2 * A / R ^ 2 / τ := by
      rw [hR]
      field_simp [hC.ne', hQ.ne', hL.ne', hτ.ne']
      <;> ring

/-- The precise low-residue fraction at the actual coarse radius. -/
theorem badLow_normalized (q : ℕ) (hq : 0 < q) {C L τ R : ℝ}
    (hC : 0 < C) (hL : 0 < L) (hτ : 0 < τ)
    (hR : R = C * (q : ℝ) * L) :
    ((badLow q hq R (τ * L ^ 2)).card : ℝ) / (q : ℝ) ^ 2 ≤
      C ^ 2 * LowPalette.aggregate q hq R / R ^ 2 / τ := by
  exact normalized_markov hC (by exact_mod_cast hq) hL hτ hR
    (badLow_card_mul_le q hq R (τ * L ^ 2))

/-- The precise high-residue fraction, using the actual collision population. -/
theorem badHigh_normalized (q : ℕ) (hq : 0 < q) {C L τ R : ℝ}
    (hC : 0 < C) (hL : 0 < L) (hτ : 0 < τ)
    (hR : R = C * (q : ℝ) * L) :
    ((badHigh q hq R (τ * L ^ 2)).card : ℝ) / (q : ℝ) ^ 2 ≤
      C ^ 2 * ((HighCollisionCover.collisionVectors q R).card : ℝ) / R ^ 2 / τ := by
  exact normalized_markov hC (by exact_mod_cast hq) hL hτ hR
    (badHigh_card_mul_le q hq R (τ * L ^ 2))

/-- Actual unit classes whose oblique projection vanishes. -/
def badProjectedUnits (q : ℕ) (hq : 0 < q) (L : ZMod q) :
    Finset (GaussianResidues.Residue q) :=
  (LowPalette.allResidues q hq).filter fun a =>
    IsUnit a ∧ L * (GaussianResidues.coordinates q a).1 +
      (GaussianResidues.coordinates q a).2 = 0

lemma mem_badProjectedUnits (q : ℕ) (hq : 0 < q) (L : ZMod q)
    (a : GaussianResidues.Residue q) :
    a ∈ badProjectedUnits q hq L ↔ IsUnit a ∧
      L * (GaussianResidues.coordinates q a).1 +
        (GaussianResidues.coordinates q a).2 = 0 := by
  simp [badProjectedUnits, LowPalette.mem_allResidues]

/-- The unit restriction can only reduce the actual linear-fiber cardinality. -/
theorem badProjectedUnits_card_le (p : ℕ) (hp : p.Prime) (L : ZMod p) :
    (badProjectedUnits p hp.pos L).card ≤ p := by
  letI : Finite (GaussianResidues.Residue p) :=
    GaussianResidues.finite_residue p hp.pos
  let f : {a // a ∈ badProjectedUnits p hp.pos L} →
      {a : GaussianResidues.Residue p //
        L * (GaussianResidues.coordinates p a).1 +
          (GaussianResidues.coordinates p a).2 = 0} :=
    fun a => ⟨a.1, ((mem_badProjectedUnits p hp.pos L a.1).mp a.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : {a : GaussianResidues.Residue p //
      L * (GaussianResidues.coordinates p a).1 +
        (GaussianResidues.coordinates p a).2 = 0} => x.1) hab)
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard] at h
  exact h.trans (GaussianResidues.card_bad_projection_prime p hp L)

end DistanceCounts.ResidueExceptions
end
end

-- Source: DistanceCounts/CoarseConditions.lean
section
/-! Actual finite arithmetic conditions used by the geometric coarse configuration. -/

noncomputable section

namespace DistanceCounts.CoarseConditions

open CoarseGrid PairModulus

/-- One disk contains every scaled difference for a fixed pair of blocks. -/
def pairRadius {t : ℕ} (L : ℕ) (p : Fin t ⊕ Fin t → ℕ) (b c : Fin t × Fin t) : ℝ :=
  6 * (modulus p b c : ℝ) * L

/-- The canonical class of the signed offset numerator; grid terms do not affect it. -/
def pairResidue {t : ℕ} (p : Fin t ⊕ Fin t → ℕ) (z : Fin t ⊕ Fin t → GaussianInt)
    (b c : Fin t × Fin t) : GaussianResidues.Residue (modulus p b c) :=
  GaussianNorm.residue (modulus p b c) (numerator p z b c)

/-- These are actual palette and collision-fiber cardinalities, not a coarse-count assumption. -/
def PaletteBounds (s L : ℕ) (p : Fin (2 * s) ⊕ Fin (2 * s) → ℕ)
    (z : Fin (2 * s) ⊕ Fin (2 * s) → GaussianInt) (ε : ℝ) : Prop :=
  ∀ b c : Fin (2 * s) × Fin (2 * s),
    if (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val then
      ((ResidueExceptions.collisionFiber (modulus p b c) (pairRadius L p b c)
        (pairResidue p z b c)).card : ℝ) ≤ ε * (L : ℝ) ^ 2
    else
      ((LowPalette.normPalette (pairResidue p z b c) (pairRadius L p b c)).card : ℝ) ≤
        ε * (L : ℝ) ^ 2


end DistanceCounts.CoarseConditions
end
end

-- Inert primes with the prescribed logarithmic scales.
section

noncomputable section

open Filter Finset
open scoped Topology Classical

namespace DistanceCounts.PrimeScaleFamilies

lemma tendsto_log_nat : Tendsto (fun L : ℕ => Real.log L) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_loglog_nat :
    Tendsto (fun L : ℕ => Real.log (Real.log L)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_nat

private def radix : ℕ := Classical.choose ElementaryProgressions.inert_interval

private theorem radix_ge_two : 2 ≤ radix :=
  (Classical.choose_spec ElementaryProgressions.inert_interval).1

private theorem radix_pos : 0 < radix := by have := radix_ge_two; omega

private def primeThreshold : ℕ := 1

private lemma prime_interval (n : ℕ) (hn : primeThreshold ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ n ≤ p ∧ p < radix * n :=
  (Classical.choose_spec ElementaryProgressions.inert_interval).2 n hn

/-- One fixed injective rank is used even when several requested exponents coincide. -/
def rank {I : Type*} [Fintype I] (i : I) : ℕ := (Fintype.equivFin I i).val

lemma rank_injective {I : Type*} [Fintype I] :
    Function.Injective (rank (I := I)) := by
  intro i j h
  apply (Fintype.equivFin I).injective
  exact Fin.ext h

private def base (w : ℝ) (L : ℕ) : ℕ :=
  max primeThreshold ⌊(Real.log L) ^ w⌋₊

private def endpoint {I : Type*} [Fintype I] (w : I → ℝ) (L : ℕ) (i : I) : ℕ :=
  radix ^ rank i * base (w i) L

private lemma endpoint_large {I : Type*} [Fintype I]
    (w : I → ℝ) (L : ℕ) (i : I) : primeThreshold ≤ endpoint w L i := by
  have hp : 1 ≤ radix ^ rank i := by
    have : 0 < radix ^ rank i := pow_pos radix_pos _
    omega
  have hb : primeThreshold ≤ base (w i) L := le_max_left _ _
  apply hb.trans
  change base (w i) L ≤ radix ^ rank i * base (w i) L
  simpa only [one_mul] using (Nat.mul_le_mul_right (base (w i) L) hp)

/-- Every value, including at the finitely many small inputs, is an actual inert prime. -/
def primeFamily {I : Type*} [Fintype I] (w : I → ℝ) (L : ℕ) (i : I) : ℕ :=
  Classical.choose (prime_interval (endpoint w L i) (endpoint_large w L i))

lemma primeFamily_spec {I : Type*} [Fintype I] (w : I → ℝ) (L : ℕ) (i : I) :
    (primeFamily w L i).Prime ∧ primeFamily w L i % 4 = 3 ∧
      endpoint w L i ≤ primeFamily w L i ∧
      primeFamily w L i < radix * endpoint w L i :=
  Classical.choose_spec (prime_interval (endpoint w L i) (endpoint_large w L i))

lemma primeFamily_prime {I : Type*} [Fintype I] (w : I → ℝ) (L : ℕ) (i : I) :
    (primeFamily w L i).Prime := (primeFamily_spec w L i).1

lemma primeFamily_mod_four {I : Type*} [Fintype I] (w : I → ℝ) (L : ℕ) (i : I) :
    primeFamily w L i % 4 = 3 := (primeFamily_spec w L i).2.1

private lemma eventually_base_bounds {w : ℝ} (hw : 0 < w) :
    ∀ᶠ L : ℕ in atTop,
      (Real.log L) ^ w / 2 ≤ (base w L : ℝ) ∧
        (base w L : ℝ) ≤ (Real.log L) ^ w := by
  have ht := (tendsto_rpow_atTop hw).comp tendsto_log_nat
  filter_upwards [ht.eventually (eventually_ge_atTop
    (max (primeThreshold : ℝ) 2))] with L hL
  have hN : (primeThreshold : ℝ) ≤ (Real.log L) ^ w := (le_max_left _ _).trans hL
  have htwo : (2 : ℝ) ≤ (Real.log L) ^ w := (le_max_right _ _).trans hL
  have hfloor : primeThreshold ≤ ⌊(Real.log L) ^ w⌋₊ := Nat.le_floor hN
  rw [base, max_eq_right hfloor]
  constructor
  · have := Nat.lt_floor_add_one ((Real.log L) ^ w)
    linarith
  · exact Nat.floor_le (by linarith)

private lemma log_power_limit (a w : ℝ) (ha : 0 < a) :
    Tendsto (fun L : ℕ => Real.log (a * (Real.log L) ^ w) /
      Real.log (Real.log L)) atTop (𝓝 w) := by
  have h : Tendsto (fun L : ℕ => Real.log a / Real.log (Real.log L) + w)
      atTop (𝓝 w) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_loglog_nat).add_const w
  apply h.congr'
  filter_upwards [tendsto_log_nat.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_loglog_nat.eventually (eventually_gt_atTop (0 : ℝ))] with L hl hll
  rw [Real.log_mul ha.ne' (Real.rpow_pos_of_pos hl w).ne', Real.log_rpow hl]
  field_simp
  <;> ring

lemma tendsto_primeFamily_log {I : Type*} [Fintype I] (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (i : I) :
    Tendsto (fun L : ℕ => Real.log (primeFamily w L i) /
      Real.log (Real.log L)) atTop (𝓝 (w i)) := by
  have hrad : 0 < (radix : ℝ) := by exact_mod_cast radix_pos
  have hb : ∀ᶠ L : ℕ in atTop,
      ((radix : ℝ) ^ rank i / 2) * (Real.log L) ^ w i ≤ (primeFamily w L i : ℝ) ∧
      (primeFamily w L i : ℝ) ≤ ((radix : ℝ) * (radix : ℝ) ^ rank i) * (Real.log L) ^ w i := by
    filter_upwards [eventually_base_bounds (hw i)] with L hL
    have hp := primeFamily_spec w L i
    dsimp [endpoint] at hp
    have hlo : (radix : ℝ) ^ rank i * (base (w i) L : ℝ) ≤ primeFamily w L i := by
      exact_mod_cast hp.2.2.1
    have hhi : (primeFamily w L i : ℝ) < (radix : ℝ) * ((radix : ℝ) ^ rank i * (base (w i) L : ℝ)) := by
      exact_mod_cast hp.2.2.2
    constructor
    · have := mul_le_mul_of_nonneg_left hL.1 (show 0 ≤ (radix : ℝ) ^ rank i by positivity)
      nlinarith
    · have hbound := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hL.2 (pow_nonneg hrad.le (rank i))) hrad.le
      exact (hhi.le.trans hbound).trans_eq (by ring)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (log_power_limit ((radix : ℝ) ^ rank i / 2) (w i) (by positivity))
    (log_power_limit ((radix : ℝ) * (radix : ℝ) ^ rank i) (w i) (by positivity))
  · filter_upwards [hb, tendsto_log_nat.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_loglog_nat.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hl hll
    exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) hL.1) hll.le
  · filter_upwards [hb, tendsto_loglog_nat.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL hll
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast (primeFamily_prime w L i).pos) hL.2) hll.le

private lemma primeFamily_lt_of_equal_weight {I : Type*} [Fintype I]
    (w : I → ℝ) (L : ℕ) {i j : I} (hw : w i = w j) (hr : rank i < rank j) :
    primeFamily w L i < primeFamily w L j := by
  have hp : radix ^ (rank i + 1) ≤ radix ^ rank j :=
    pow_le_pow_right₀ radix_pos (by omega)
  have he : radix * endpoint w L i ≤ endpoint w L j := by
    simpa [endpoint, hw, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using Nat.mul_le_mul_right (base (w j) L) hp
  exact (primeFamily_spec w L i).2.2.2.trans_le
    (he.trans (primeFamily_spec w L j).2.2.1)

lemma eventually_primeFamily_injective {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    ∀ᶠ L : ℕ in atTop, Function.Injective (primeFamily w L) := by
  have hpair : ∀ i j : I, ∀ᶠ L : ℕ in atTop,
      primeFamily w L i = primeFamily w L j → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ _ => hij
    by_cases hw' : w i = w j
    · have hr : rank i ≠ rank j := fun h => hij (rank_injective h)
      rcases lt_or_gt_of_ne hr with hr | hr
      · exact Eventually.of_forall fun L h =>
          False.elim ((primeFamily_lt_of_equal_weight w L hw' hr).ne h)
      · exact Eventually.of_forall fun L h =>
          False.elim ((primeFamily_lt_of_equal_weight w L hw'.symm hr).ne h.symm)
    · have h := ((tendsto_primeFamily_log w hw i).sub
        (tendsto_primeFamily_log w hw j)).eventually_ne (sub_ne_zero.mpr hw')
      filter_upwards [h] with L hL heq
      exact False.elim (hL (by rw [heq, sub_self]))
  simpa only [Function.Injective, eventually_all] using hpair

/-- A fixed subset product, retaining its indexing even before eventual distinctness. -/
def subsetModulus {I : Type*} [Fintype I] (w : I → ℝ) (s : Finset I) (L : ℕ) : ℕ :=
  ∏ i ∈ s, primeFamily w L i

lemma subsetModulus_pos {I : Type*} [Fintype I] (w : I → ℝ) (s : Finset I) (L : ℕ) :
    0 < subsetModulus w s L :=
  Finset.prod_pos fun i _ => (primeFamily_prime w L i).pos

lemma tendsto_subsetModulus_log {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (s : Finset I) :
    Tendsto (fun L : ℕ => Real.log (subsetModulus w s L) /
      Real.log (Real.log L)) atTop (𝓝 (∑ i ∈ s, w i)) := by
  have h := tendsto_finset_sum s (fun i _ => tendsto_primeFamily_log w hw i)
  convert h using 1
  ext L
  rw [subsetModulus, Nat.cast_prod, Real.log_prod, Finset.sum_div]
  intro i _
  exact_mod_cast (primeFamily_prime w L i).ne_zero

/-- Exponent convergence implies both power windows, including when the exponent is zero. -/
lemma eventually_power_window {f : ℕ → ℝ} {a : ℝ}
    (hf : ∀ᶠ L : ℕ in atTop, 0 < f L)
    (h : Tendsto (fun L : ℕ => Real.log (f L) / Real.log (Real.log L))
      atTop (𝓝 a)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop,
      (Real.log L) ^ (a - ε) ≤ f L ∧ f L ≤ (Real.log L) ^ (a + ε) := by
  filter_upwards [hf, h.eventually (lt_mem_nhds (show a - ε < a by linarith)),
    h.eventually (gt_mem_nhds (show a < a + ε by linarith)),
    tendsto_log_nat.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_loglog_nat.eventually (eventually_gt_atTop (0 : ℝ))]
    with L hf hl hu hx hxx
  constructor
  · exact (Real.rpow_le_iff_le_log hx hf).2 ((lt_div_iff₀ hxx).1 hl).le
  · exact (Real.le_rpow_iff_log_le hf hx).2 ((div_lt_iff₀ hxx).1 hu).le

lemma eventually_subsetModulus_window {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop,
      (Real.log L) ^ ((∑ i ∈ s, w i) - ε) ≤ (subsetModulus w s L : ℝ) ∧
      (subsetModulus w s L : ℝ) ≤ (Real.log L) ^ ((∑ i ∈ s, w i) + ε) :=
  eventually_power_window (Eventually.of_forall fun L => by
    exact_mod_cast subsetModulus_pos w s L) (tendsto_subsetModulus_log w hw s) hε

/-- The radius used to place a full modulus-scaled lattice box in a disk. -/
def radius {I : Type*} [Fintype I] (w : I → ℝ) (s : Finset I) (C : ℝ) (L : ℕ) : ℝ :=
  C * subsetModulus w s L * L

lemma tendsto_radius {I : Type*} [Fintype I] (w : I → ℝ)
    (s : Finset I) {C : ℝ} (hC : 0 < C) :
    Tendsto (radius w s C) atTop atTop := by
  apply tendsto_atTop_mono _ (Tendsto.const_mul_atTop hC
    (tendsto_natCast_atTop_atTop : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop))
  intro L
  have hq : (1 : ℝ) ≤ subsetModulus w s L := by
    exact_mod_cast (Nat.succ_le_iff.mpr (subsetModulus_pos w s L))
  dsimp [radius]
  exact mul_le_mul_of_nonneg_right (show C ≤ C * (subsetModulus w s L : ℝ) by
    nlinarith) (Nat.cast_nonneg L)

lemma tendsto_radius_log {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (s : Finset I) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun L : ℕ => Real.log (radius w s C L) / Real.log L)
      atTop (𝓝 1) := by
  have hsmall : Tendsto (fun L : ℕ => Real.log (Real.log L) / Real.log L)
      atTop (𝓝 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_nat
  have hq : Tendsto (fun L : ℕ => Real.log (subsetModulus w s L) / Real.log L)
      atTop (𝓝 0) := by
    have h := (tendsto_subsetModulus_log w hw s).mul hsmall
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [tendsto_loglog_nat.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL
    exact div_mul_div_cancel₀ hL.ne'
  have h := ((tendsto_const_nhds.div_atTop tendsto_log_nat
    (a := Real.log C)).add hq).add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    tendsto_log_nat.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hl
  have hq0 : (subsetModulus w s L : ℝ) ≠ 0 := by
    exact_mod_cast (subsetModulus_pos w s L).ne'
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [radius, Real.log_mul (mul_ne_zero hC.ne' hq0) hL0,
    Real.log_mul hC.ne' hq0]
  field_simp
  <;> ring

private lemma tendsto_log_ratio {f g : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop)
    (h : Tendsto (fun L => f L / g L) atTop (𝓝 1)) :
    Tendsto (fun L => Real.log (f L) / Real.log (g L)) atTop (𝓝 1) := by
  have hl := h.log one_ne_zero
  simp only [Real.log_one] at hl
  have hh := (hl.div_atTop (Real.tendsto_log_atTop.comp hg)).add_const 1
  simp only [Function.comp_def, zero_add] at hh
  apply hh.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop (0 : ℝ)),
    hg.eventually (eventually_gt_atTop (1 : ℝ))] with L hfL hgL
  rw [Real.log_div hfL.ne' (zero_lt_one.trans hgL).ne']
  have := (Real.log_pos hgL).ne'
  field_simp
  <;> ring

lemma tendsto_radius_loglog {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (s : Finset I) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun L : ℕ => Real.log (Real.log (radius w s C L)) /
      Real.log (Real.log L)) atTop (𝓝 1) :=
  tendsto_log_ratio (Real.tendsto_log_atTop.comp (tendsto_radius w s hC))
    tendsto_log_nat (tendsto_radius_log w hw s hC)

lemma tendsto_subsetModulus_log_radius {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (s : Finset I) {C : ℝ} (hC : 0 < C) :
    Tendsto (fun L : ℕ => Real.log (subsetModulus w s L) /
      Real.log (Real.log (radius w s C L))) atTop (𝓝 (∑ i ∈ s, w i)) := by
  have h := (tendsto_subsetModulus_log w hw s).div
    (tendsto_radius_loglog w hw s hC) one_ne_zero
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [tendsto_loglog_nat.eventually (eventually_gt_atTop (0 : ℝ))]
    with L hL
  exact div_div_div_cancel_right₀ hL.ne' _ _

lemma eventually_subsetModulus_radius_window {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 < w i) (s : Finset I) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop,
      (Real.log (radius w s C L)) ^ ((∑ i ∈ s, w i) - ε) ≤
        (subsetModulus w s L : ℝ) ∧
      (subsetModulus w s L : ℝ) ≤
        (Real.log (radius w s C L)) ^ ((∑ i ∈ s, w i) + ε) := by
  have h := tendsto_subsetModulus_log_radius w hw s hC
  have hl := Real.tendsto_log_atTop.comp (tendsto_radius w s hC)
  have hll := Real.tendsto_log_atTop.comp hl
  filter_upwards [
    h.eventually (lt_mem_nhds (show (∑ i ∈ s, w i) - ε < ∑ i ∈ s, w i by linarith)),
    h.eventually (gt_mem_nhds (show (∑ i ∈ s, w i) < (∑ i ∈ s, w i) + ε by linarith)),
    hl.eventually (eventually_gt_atTop (0 : ℝ)),
    hll.eventually (eventually_gt_atTop (0 : ℝ))] with L hlo hhi hx hxx
  have hq : (0 : ℝ) < subsetModulus w s L := by
    exact_mod_cast subsetModulus_pos w s L
  exact ⟨(Real.rpow_le_iff_le_log hx hq).2 ((lt_div_iff₀ hxx).1 hlo).le,
    (Real.le_rpow_iff_log_le hq hx).2 ((div_lt_iff₀ hxx).1 hhi).le⟩

/-- The finite-type form needs no preselected enumeration and no distinctness of weights. -/
theorem exists_prime_family {I : Type*} [Finite I] (w : I → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ P : ℕ → I → ℕ,
      (∀ L i, (P L i).Prime ∧ P L i % 4 = 3) ∧
      (∀ᶠ L : ℕ in atTop, Function.Injective (P L)) ∧
      ∀ i, Tendsto (fun L : ℕ => Real.log (P L i) / Real.log (Real.log L))
        atTop (𝓝 (w i)) := by
  letI := Fintype.ofFinite I
  exact ⟨primeFamily w, fun L i => ⟨primeFamily_prime w L i, primeFamily_mod_four w L i⟩,
    eventually_primeFamily_injective w hw, tendsto_primeFamily_log w hw⟩

end DistanceCounts.PrimeScaleFamilies
end
end


-- Source: DistanceCounts/GaussianLogWeight.lean
section
/-! Reciprocal logarithmic weights on the actual nonzero Gaussian lattice.
The finite dyadic cover includes the final shell and the norm-one units. -/

noncomputable section

namespace DistanceCounts.GaussianLogWeight

open Finset GaussianMass
open scoped Classical

/-- The summand, with the squared outer radius as parameter. -/
def weight (X : ℝ) (z : GaussianInt) : ℝ :=
  1 / ((z.norm.natAbs : ℝ) * Real.log (X / z.norm.natAbs))

lemma norm_one_le {z : GaussianInt} (hz : z ≠ 0) :
    (1 : ℝ) ≤ z.norm.natAbs := by
  have h : 0 < z.norm.natAbs :=
    Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hz)
  exact_mod_cast Nat.succ_le_of_lt h

/-- Removing the origin gives a population bound valid even below norm one. -/
lemma representatives_card_le {D : ℝ} (hD : 0 ≤ D) :
    ((representatives D).card : ℝ) ≤ 9 * Real.pi * D := by
  have h := GaussianDivisibility.divisorDisk_erase_zero_card_upper
    (1 : GaussianInt) one_ne_zero (Real.sqrt_nonneg D)
  simpa [GaussianDivisibility.divisorDisk, GaussianDivisibility.normMass,
    representatives, Real.sq_sqrt hD] using h

lemma denominator_pos {X : ℝ} (hX : 0 < X) {z : GaussianInt}
    (hz : z ∈ representatives (X / 2)) :
    0 < (z.norm.natAbs : ℝ) * Real.log (X / z.norm.natAbs) := by
  obtain ⟨hz0, hzX⟩ := (mem_representatives (by positivity) z).mp hz
  have hn : (0 : ℝ) < z.norm.natAbs := lt_of_lt_of_le zero_lt_one (norm_one_le hz0)
  apply mul_pos hn (Real.log_pos _)
  apply (lt_div_iff₀ hn).mpr
  linarith

lemma weight_nonneg {X : ℝ} (hX : 0 < X) {z : GaussianInt}
    (hz : z ∈ representatives (X / 2)) : 0 ≤ weight X z :=
  (one_div_pos.mpr (denominator_pos hX hz)).le

/-- Shell `k` has norms in `(X/2^(k+1), X/2^k]`. Restricting to
`representatives (X/2)` makes positivity uniform in every finite sum. -/
def shell (X : ℝ) (k : ℕ) : Finset GaussianInt :=
  (representatives (X / 2)).filter (fun z =>
    X / (2 : ℝ) ^ (k + 1) < z.norm.natAbs ∧
      (z.norm.natAbs : ℝ) ≤ X / (2 : ℝ) ^ k)

/-- Genuine finite shell coverage: the norm lower bound one supplies the
upper index, so there is no discarded tail or exceptional unit contribution. -/
lemma shell_cover {X : ℝ} (hX : 0 < X) {z : GaussianInt}
    (hz : z ∈ representatives (X / 2)) :
    ∃ k ∈ Icc 1 ⌊Real.log X / Real.log 2⌋₊, z ∈ shell X k := by
  obtain ⟨hz0, hzX⟩ := (mem_representatives (by positivity) z).mp hz
  have hn1 := norm_one_le hz0
  have hn : (0 : ℝ) < z.norm.natAbs := by linarith
  have hratio : (2 : ℝ) ≤ X / z.norm.natAbs := by
    apply (le_div_iff₀ hn).mpr
    linarith
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ X / z.norm.natAbs by linarith) (show (1 : ℝ) < 2 by norm_num)
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0, zero_add, pow_one] at hkhi
    linarith
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hp' : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hrX : X / z.norm.natAbs ≤ X := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hlog := Real.log_le_log hp (hklo.trans hrX)
  rw [Real.log_pow] at hlog
  have hkN : k ≤ ⌊Real.log X / Real.log 2⌋₊ :=
    Nat.le_floor ((le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog)
  refine ⟨k, mem_Icc.mpr ⟨hk1, hkN⟩, mem_filter.mpr ⟨hz, ?_, ?_⟩⟩
  · apply (div_lt_iff₀ hp').mpr
    have ht := (div_lt_iff₀ hn).mp hkhi
    nlinarith
  · apply (le_div_iff₀ hp).mpr
    have ht := (le_div_iff₀ hn).mp hklo
    nlinarith

/-- Every nonempty dyadic shell costs at most a constant times `1/k`.
The lattice bound remains valid if its upper radius falls below norm one. -/
lemma shell_sum_le {X : ℝ} (hX : 0 < X) {k : ℕ} (hk : 1 ≤ k) :
    (∑ z ∈ shell X k, weight X z) ≤
      (18 * Real.pi / Real.log 2) / k := by
  let D : ℝ := X / (2 : ℝ) ^ k
  let L : ℝ := (k : ℝ) * Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hL : 0 < L := mul_pos hk0 (Real.log_pos (by norm_num))
  have hterm (z : GaussianInt) (hz : z ∈ shell X k) :
      weight X z ≤ 2 / (D * L) := by
    obtain ⟨hzA, hzlo, hzhi⟩ := mem_filter.mp hz
    have hn : (0 : ℝ) < z.norm.natAbs := by
      have hz0 := ((mem_representatives (by positivity) z).mp hzA).1
      linarith [norm_one_le hz0]
    have hlo : D / 2 ≤ (z.norm.natAbs : ℝ) := by
      have he : X / (2 : ℝ) ^ (k + 1) = D / 2 := by
        dsimp [D]
        rw [pow_succ, div_mul_eq_div_div]
      rw [he] at hzlo
      exact hzlo.le
    have hratio : (2 : ℝ) ^ k ≤ X / z.norm.natAbs := by
      apply (le_div_iff₀ hn).mpr
      have ht := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).mp hzhi
      nlinarith
    have hlog : L ≤ Real.log (X / z.norm.natAbs) := by
      have ht := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ k) hratio
      simpa only [Real.log_pow] using ht
    have hden : D * L / 2 ≤
        (z.norm.natAbs : ℝ) * Real.log (X / z.norm.natAbs) := by
      calc
        D * L / 2 = (D / 2) * L := by ring
        _ ≤ (z.norm.natAbs : ℝ) * Real.log (X / z.norm.natAbs) :=
          mul_le_mul hlo hlog hL.le (le_of_lt hn)
    calc
      weight X z ≤ 1 / (D * L / 2) :=
        one_div_le_one_div_of_le (by positivity) hden
      _ = 2 / (D * L) := by field_simp
  have hsub : shell X k ⊆ representatives D := by
    intro z hz
    obtain ⟨hzA, _, hzhi⟩ := mem_filter.mp hz
    exact (mem_representatives hD.le z).mpr
      ⟨((mem_representatives (by positivity) z).mp hzA).1, hzhi⟩
  have hc : ((shell X k).card : ℝ) ≤ 9 * Real.pi * D := by
    calc
      _ ≤ ((representatives D).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ ≤ _ := representatives_card_le hD.le
  calc
    (∑ z ∈ shell X k, weight X z) ≤ ∑ _z ∈ shell X k, 2 / (D * L) :=
      sum_le_sum hterm
    _ = ((shell X k).card : ℝ) * (2 / (D * L)) := by simp
    _ ≤ (9 * Real.pi * D) * (2 / (D * L)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (18 * Real.pi / Real.log 2) / k := by
      dsimp [L]
      field_simp [ne_of_gt hD, ne_of_gt hk0,
        ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
      <;> ring

/-- The lattice estimate at squared radius `X`, before rescaling its logarithms. -/
theorem sum_le_log_log_quotient {X : ℝ} (hX : 2 ≤ X) :
    (∑ z ∈ representatives (X / 2), weight X z) ≤
      (18 * Real.pi / Real.log 2) *
        (1 + Real.log (Real.log X / Real.log 2)) := by
  have hX0 : 0 < X := by linarith
  let N := ⌊Real.log X / Real.log 2⌋₊
  have hcover : (∑ z ∈ representatives (X / 2), weight X z) ≤
      ∑ k ∈ Icc 1 N, ∑ z ∈ shell X k, weight X z := by
    simp only [shell, sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro z hz
    obtain ⟨k, hk, hzk⟩ := shell_cover hX0 hz
    have hp := (mem_filter.mp hzk).2
    calc
      weight X z = (if X / (2 : ℝ) ^ (k + 1) < z.norm.natAbs ∧
          (z.norm.natAbs : ℝ) ≤ X / (2 : ℝ) ^ k then weight X z else 0) := by
        rw [if_pos hp]
      _ ≤ _ := single_le_sum (s := Icc 1 N) (a := k)
        (f := fun i : ℕ => if X / (2 : ℝ) ^ (i + 1) < z.norm.natAbs ∧
          (z.norm.natAbs : ℝ) ≤ X / (2 : ℝ) ^ i then weight X z else 0)
        (fun i _ => by
          split_ifs <;> first | exact weight_nonneg hX0 hz | exact le_rfl) hk
  have hL : 1 ≤ Real.log X / Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX
  have hhar : (∑ k ∈ Icc 1 N, (18 * Real.pi / Real.log 2) / k) =
      (18 * Real.pi / Real.log 2) * (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      mul_sum, div_eq_mul_inv]
  calc
    _ ≤ ∑ k ∈ Icc 1 N, (18 * Real.pi / Real.log 2) / k :=
      hcover.trans (sum_le_sum fun k hk => shell_sum_le hX0 (mem_Icc.mp hk).1)
    _ = _ := hhar
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (harmonic_floor_le_one_add_log _ hL) (by positivity)

/-- An absolute constant for the actual-vector reciprocal logarithmic sum. -/
theorem reciprocal_log_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, Real.exp 1 ≤ R →
      (∑ z ∈ representatives (R ^ 2 / 2),
        1 / ((z.norm.natAbs : ℝ) * Real.log (R ^ 2 / z.norm.natAbs))) ≤
          C * (1 + Real.log (Real.log R)) := by
  let K : ℝ := 18 * Real.pi / Real.log 2
  let B : ℝ := 2 + |Real.log (2 / Real.log 2)|
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨K * B, mul_pos hK hB, ?_⟩
  intro R hR
  have hR2 : 2 ≤ R := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hR0 : 0 < R := by linarith
  have hlogR : 1 ≤ Real.log R := by
    have h := Real.log_le_log (Real.exp_pos 1) hR
    simpa using h
  have hlogR0 : 0 < Real.log R := by linarith
  have hll : 0 ≤ Real.log (Real.log R) := Real.log_nonneg hlogR
  have hX : 2 ≤ R ^ 2 := by nlinarith
  have he : Real.log (Real.log (R ^ 2) / Real.log 2) =
      Real.log (2 / Real.log 2) + Real.log (Real.log R) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [show 2 * Real.log R / Real.log 2 =
      (2 / Real.log 2) * Real.log R by ring,
      Real.log_mul (ne_of_gt (div_pos (by norm_num) hl2)) (ne_of_gt hlogR0)]
  have habs := le_abs_self (Real.log (2 / Real.log 2))
  have hbnd : 1 + Real.log (2 / Real.log 2) + Real.log (Real.log R) ≤
      B * (1 + Real.log (Real.log R)) := by
    dsimp [B]
    nlinarith [abs_nonneg (Real.log (2 / Real.log 2)),
      mul_nonneg (abs_nonneg (Real.log (2 / Real.log 2))) hll]
  have hs := sum_le_log_log_quotient hX
  rw [he] at hs
  change (∑ z ∈ representatives (R ^ 2 / 2), weight (R ^ 2) z) ≤ _
  calc
    _ ≤ K * (1 + (Real.log (2 / Real.log 2) + Real.log (Real.log R))) := hs
    _ ≤ K * (B * (1 + Real.log (Real.log R))) :=
      mul_le_mul_of_nonneg_left (by simpa only [add_assoc] using hbnd) hK.le
    _ = _ := by ring

/-- Positive-sum enlargement, on the actual supports, handles every `Y ≥ 2`. -/
theorem reciprocal_log_sum_bound_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, Real.exp 1 ≤ R → ∀ Y : ℝ, 2 ≤ Y →
      (∑ z ∈ representatives (R ^ 2 / Y),
        1 / ((z.norm.natAbs : ℝ) * Real.log (R ^ 2 / z.norm.natAbs))) ≤
          C * (1 + Real.log (Real.log R)) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_log_sum_bound
  refine ⟨C, hC, ?_⟩
  intro R hR Y hY
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hY0 : 0 < Y := by linarith
  have hcut : R ^ 2 / Y ≤ R ^ 2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg R) (by norm_num) hY
  have hsub : representatives (R ^ 2 / Y) ⊆ representatives (R ^ 2 / 2) := by
    intro z hz
    obtain ⟨hz0, hzn⟩ := (mem_representatives (by positivity) z).mp hz
    exact (mem_representatives (by positivity) z).mpr ⟨hz0, hzn.trans hcut⟩
  apply le_trans (sum_le_sum_of_subset_of_nonneg hsub ?_) (hbound R hR)
  intro z hz _
  exact weight_nonneg (sq_pos_of_pos hR0) hz

end DistanceCounts.GaussianLogWeight
end
end

-- Source: DistanceCounts/HighTransitionRates.lean
section
/-! Radius-only decay for the four actual high-transition populations. -/

noncomputable section

namespace DistanceCounts.HighTransitionRates

open Filter Finset
open scoped Topology Classical

/-- Half the strict gap above the transition exponent. -/
def epsilon (c : ℝ) : ℝ := (c - Real.log 2) / 2

/-- The manuscript scales, safely below both the modulus and radius exponents. -/
def kappa (c : ℝ) : ℝ := min c 1 / 8

/-- The actual normal-order upper cutoff. -/
def threshold (R c : ℝ) : ℝ := (Real.log R) ^ (Real.log 2 + epsilon c)

lemma parameters {c : ℝ} (hc : Real.log 2 < c) :
    0 < epsilon c ∧ 0 < kappa c ∧ 0 < 2 * kappa c ∧
      2 * kappa c < min c 1 := by
  have hc0 : 0 < c := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hc
  have hm : 0 < min c 1 := lt_min hc0 zero_lt_one
  dsimp [epsilon, kappa]
  constructor
  · linarith
  constructor
  · positivity
  constructor <;> linarith

/-- The precise exponent conversion needed by the proved prime bound. -/
lemma log_manuscriptY_rpow {R κ : ℝ} (hR : 1 < R) (hκ : 0 < κ) (A : ℝ) :
    (Real.log (GaussianSmoothPart.manuscriptY R κ)) ^ (A / κ) =
      (Real.log R) ^ A := by
  rw [GaussianSmoothPart.manuscriptY, Real.log_exp,
    ← Real.rpow_mul (Real.log_pos hR).le]
  congr 1
  field_simp [ne_of_gt hκ]
  <;> ring

lemma tendsto_manuscriptY {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun R => GaussianSmoothPart.manuscriptY R κ) atTop atTop :=
  Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop hκ).comp Real.tendsto_log_atTop)

private lemma tendsto_power_ratio {a b : ℝ} (hab : a < b) :
    Tendsto (fun x : ℝ => x ^ a / x ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_sub hx]
  congr 1
  ring

private lemma tendsto_power_ratio_log {a b : ℝ} (hab : a < b) :
    Tendsto (fun x : ℝ => x ^ a / x ^ b * (1 + Real.log x)) atTop (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => 1 / x ^ (b - a)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero] using
      (tendsto_power_ratio (a := 0) (b := b - a) (sub_pos.mpr hab))
  have hl := (isLittleO_log_rpow_rpow_atTop 1 (sub_pos.mpr hab)).tendsto_div_nhds_zero
  have h : Tendsto (fun x : ℝ => (1 + Real.log x) / x ^ (b - a)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, add_div, zero_add] using hi.add hl
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_sub hx, show a - b = -(b - a) by ring, Real.rpow_neg hx.le]
  ring

/-- The small-flip majorant retains exactly the manuscript's `log S`. -/
def smallRate (c R : ℝ) : ℝ :=
  (2304 * Real.pi) * (1 + Real.log (GaussianSmoothPart.manuscriptS R (kappa c))) /
    (Real.log R) ^ c

/-- The large-flip majorant uses the genuine reciprocal-log sum, not a harmonic substitute. -/
def largeRate (c C R : ℝ) : ℝ :=
  C * threshold R c / (Real.log R) ^ c * (1 + Real.log (Real.log R))

lemma tendsto_smallRate {c : ℝ} (hc : Real.log 2 < c) :
    Tendsto (smallRate c) atTop (𝓝 0) := by
  unfold smallRate
  have hp := parameters hc
  have hc0 : 0 < c := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans hc
  have hk : 2 * kappa c < c := hp.2.2.2.trans_le (min_le_left _ _)
  have h0 := (tendsto_power_ratio (a := 0) hc0).comp Real.tendsto_log_atTop
  have hs := (tendsto_power_ratio hk).comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, Real.rpow_zero, smallRate,
    GaussianSmoothPart.manuscriptS, Real.log_exp, add_div, mul_add,
    mul_div_assoc, zero_add, mul_zero] using (h0.add hs).const_mul (2304 * Real.pi)

lemma tendsto_largeRate {c : ℝ} (hc : Real.log 2 < c) (C : ℝ) :
    Tendsto (largeRate c C) atTop (𝓝 0) := by
  unfold largeRate
  have hexp : Real.log 2 + epsilon c < c := by dsimp [epsilon]; linarith
  have h := (tendsto_power_ratio_log hexp).comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, largeRate, threshold, mul_div_assoc,
    mul_assoc, mul_zero] using h.const_mul C

/-- An explicit error depending only on the radius and fixed constants. Its
first two terms are the actual exceptional densities, not assumed rates. -/
def errorBound (c C R : ℝ) : ℝ :=
  ((GaussianNormalOrder.normalBad R (epsilon c)).card : ℝ) / R ^ 2 +
  ((GaussianSmoothPart.exceptional R (GaussianSmoothPart.manuscriptY R (kappa c))
    (GaussianSmoothPart.manuscriptS R (kappa c))).card : ℝ) / R ^ 2 +
  smallRate c R + largeRate c C R

lemma tendsto_errorBound {c : ℝ} (hc : Real.log 2 < c) (C : ℝ) :
    Tendsto (errorBound c C) atTop (𝓝 0) := by
  unfold errorBound
  have hp := parameters hc
  simpa only [errorBound, zero_add] using
    (((GaussianNormalOrder.tendsto_normalBad_card hp.1).add
      (GaussianSmoothPart.tendsto_exceptional_card hp.2.1)).add
      (tendsto_smallRate hc)).add (tendsto_largeRate hc C)

/-- The complete actual upper bound, with no squarefreeness exclusion. The
small-flip API takes its cutoff before its radius. -/
def upperDensity (q : ℕ) (R c : ℝ) : ℝ :=
  (((GaussianNormalOrder.normalBad R (epsilon c)).card : ℝ) +
    ((GaussianSmoothPart.exceptional R (GaussianSmoothPart.manuscriptY R (kappa c))
      (GaussianSmoothPart.manuscriptS R (kappa c))).card : ℝ) +
    ((SmallFlipLattice.smallFlipDivisibleVectors q
      (GaussianSmoothPart.manuscriptS R (kappa c)) R).card : ℝ) +
    ((LargeFlipCount.largeFlipVectors q R
      (GaussianSmoothPart.manuscriptY R (kappa c)) (threshold R c)).card : ℝ)) / R ^ 2

/-- Uniformity is simultaneous over all real radii and all products of at most
four inert primes in the stated window. The prime bound and reciprocal-log
estimate are proved inputs instantiated here, never hypotheses of this result. -/
theorem exists_uniform_error {c A : ℝ} (hc : Real.log 2 < c) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (errorBound c C) atTop (𝓝 0) ∧
      ∀ᶠ R : ℝ in atTop, ∀ q : ℕ, ∀ P : Finset ℕ,
        q = ∏ p ∈ P, p → P.card ≤ 4 →
        (∀ p ∈ P, p.Prime ∧ p % 4 = 3) →
        (Real.log R) ^ c ≤ (q : ℝ) → (q : ℝ) ≤ (Real.log R) ^ A →
        upperDensity q R c ≤ errorBound c C R := by
  have hp := parameters hc
  obtain ⟨C₁, Z₀, hC₁, _hZ₀, hfinite⟩ :=
    LargeFlipCount.largeFlipVectors_card_polylog (A / kappa c) (div_pos hA hp.2.1)
  obtain ⟨C₂, hC₂, hweight⟩ := GaussianLogWeight.reciprocal_log_sum_bound_uniform
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, tendsto_errorBound hc _, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (Real.exp 1),
    (tendsto_manuscriptY hp.2.1).eventually (eventually_ge_atTop (max Z₀ 2))]
    with R hR hRexp hY
  intro q P hqeq hfour hP hqlow hqhigh
  subst q
  let q : ℕ := ∏ p ∈ P, p
  have hq : 0 < q := Finset.prod_pos fun p hp => (hP p hp).1.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hl : 0 < Real.log R := Real.log_pos hR
  have hpow : 0 < (Real.log R) ^ c := Real.rpow_pos_of_pos hl _
  have hT : 0 ≤ threshold R c := (Real.rpow_pos_of_pos hl _).le
  have hS : 1 ≤ GaussianSmoothPart.manuscriptS R (kappa c) :=
    Real.one_le_exp_iff.mpr (Real.rpow_nonneg hl.le _)
  have hY2 : 2 ≤ GaussianSmoothPart.manuscriptY R (kappa c) :=
    (le_max_right _ _).trans hY
  have hlog1 : 1 ≤ Real.log R := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hRexp
  have hloglog : 0 ≤ 1 + Real.log (Real.log R) := by
    have := Real.log_nonneg hlog1
    linarith
  have hqY : (q : ℝ) ≤
      (Real.log (GaussianSmoothPart.manuscriptY R (kappa c))) ^ (A / kappa c) := by
    rw [log_manuscriptY_rpow hR hp.2.1]
    exact hqhigh
  have hsmall : ((SmallFlipLattice.smallFlipDivisibleVectors q
      (GaussianSmoothPart.manuscriptS R (kappa c)) R).card : ℝ) / R ^ 2 ≤
      smallRate c R := by
    have hb := SmallFlipLattice.smallFlipDivisibleVectors_card_upper q
      (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hq)) hS hR0.le
    have hn : 0 ≤ (2304 * Real.pi) *
        (1 + Real.log (GaussianSmoothPart.manuscriptS R (kappa c))) := by
      have := Real.log_nonneg hS
      positivity
    calc
      _ ≤ ((2304 * Real.pi) * R ^ 2 *
          (1 + Real.log (GaussianSmoothPart.manuscriptS R (kappa c))) / (q : ℝ)) /
          R ^ 2 := div_le_div_of_nonneg_right hb (sq_nonneg R)
      _ = (2304 * Real.pi) *
          (1 + Real.log (GaussianSmoothPart.manuscriptS R (kappa c))) / (q : ℝ) := by
        field_simp [ne_of_gt hR0, ne_of_gt hq0]
        <;> ring
      _ ≤ smallRate c R := div_le_div_of_nonneg_left hn hpow hqlow
  have hlarge : ((LargeFlipCount.largeFlipVectors q R
      (GaussianSmoothPart.manuscriptY R (kappa c)) (threshold R c)).card : ℝ) /
      R ^ 2 ≤ largeRate c (C₁ * C₂) R := by
    have hb := hfinite P hfour hP R _ _ hR0.le hY hT hqY
    have hw := hweight R hRexp (GaussianSmoothPart.manuscriptY R (kappa c)) hY2
    have hw' : (∑ u ∈ GaussianMass.representatives
        (R ^ 2 / GaussianSmoothPart.manuscriptY R (kappa c)),
        1 / (GaussianDivisibility.normMass u *
          Real.log (R ^ 2 / GaussianDivisibility.normMass u))) ≤
        C₂ * (1 + Real.log (Real.log R)) := hw
    have hcoef : 0 ≤ C₁ * (threshold R c / (q : ℝ)) * R ^ 2 := by positivity
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hw' hcoef)
    have hn : 0 ≤ (C₁ * C₂) * threshold R c * (1 + Real.log (Real.log R)) := by
      positivity
    calc
      _ ≤ (C₁ * (threshold R c / (q : ℝ)) * R ^ 2 *
          (C₂ * (1 + Real.log (Real.log R)))) / R ^ 2 :=
        div_le_div_of_nonneg_right hb' (sq_nonneg R)
      _ = ((C₁ * C₂) * threshold R c * (1 + Real.log (Real.log R))) / (q : ℝ) := by
        field_simp [ne_of_gt hR0, ne_of_gt hq0]
        <;> ring
      _ ≤ ((C₁ * C₂) * threshold R c * (1 + Real.log (Real.log R))) /
          (Real.log R) ^ c := div_le_div_of_nonneg_left hn hpow hqlow
      _ = largeRate c (C₁ * C₂) R := by unfold largeRate; ring
  unfold upperDensity errorBound
  rw [add_div, add_div, add_div]
  linarith [hsmall, hlarge]

end DistanceCounts.HighTransitionRates
end
end

-- Source: DistanceCounts/HighTransition.lean
section
/-! Uniform high-denominator collision decay for the actual Gaussian populations. -/

noncomputable section

namespace DistanceCounts.HighTransition

open Filter Finset HighCollisionCover HighTransitionRates
open scoped Topology Classical

theorem excessive_subset_normalBad (R c : ℝ) :
    excessiveRepresentations R (threshold R c) ⊆ GaussianNormalOrder.normalBad R (epsilon c) := by
  intro z hz
  obtain ⟨hz, he⟩ := mem_filter.mp hz
  exact mem_filter.mpr ⟨hz, Or.inr he⟩

theorem collision_density_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 3) {R c : ℝ} (hR : 0 ≤ R) :
    ((collisionVectors (∏ p ∈ P, p) R).card : ℝ) / R ^ 2 ≤
      upperDensity (∏ p ∈ P, p) R c := by
  let Y := GaussianSmoothPart.manuscriptY R (kappa c)
  let S := GaussianSmoothPart.manuscriptS R (kappa c)
  let A := GaussianNormalOrder.normalBad R (epsilon c)
  let B := GaussianSmoothPart.exceptional R Y S
  let C := SmallFlipLattice.smallFlipDivisibleVectors (∏ p ∈ P, p) S R
  let D := LargeFlipCount.largeFlipVectors (∏ p ∈ P, p) R Y (threshold R c)
  have hY : 0 ≤ Y := by unfold Y GaussianSmoothPart.manuscriptY; positivity
  have he := excessive_subset_normalBad R c
  have hcover : collisionVectors (∏ p ∈ P, p) R ⊆ A ∪ B ∪ C ∪ D := by
    intro z hz
    have hz' := collisionVectors_subset P hP (S := S) (T := threshold R c) hR hY hz
    simp only [mem_union] at hz' ⊢
    rcases hz' with ((hz' | hz') | hz') | hz'
    · exact Or.inl (Or.inl (Or.inl (he hz')))
    · exact Or.inl (Or.inl (Or.inr hz'))
    · exact Or.inl (Or.inr hz')
    · exact Or.inr hz'
  have hcard := card_le_card hcover
  have h₁ := card_union_le (A ∪ B ∪ C) D
  have h₂ := card_union_le (A ∪ B) C
  have h₃ := card_union_le A B
  have hn : ((collisionVectors (∏ p ∈ P, p) R).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) + (D.card : ℝ) := by
    exact_mod_cast (show (collisionVectors (∏ p ∈ P, p) R).card ≤
      A.card + B.card + C.card + D.card by omega)
  exact div_le_div_of_nonneg_right hn (sq_nonneg R)

/-- This bounds actual collisions, not an assumed high-transition property. -/
theorem exists_uniform_collision_error {c A : ℝ}
    (hc : Real.log 2 < c) (hA : 0 < A) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ R : ℝ in atTop, ∀ P : Finset ℕ, P.card ≤ 4 →
        (∀ p ∈ P, p.Prime ∧ p % 4 = 3) →
        (Real.log R) ^ c ≤ ((∏ p ∈ P, p : ℕ) : ℝ) →
        ((∏ p ∈ P, p : ℕ) : ℝ) ≤ (Real.log R) ^ A →
        ((collisionVectors (∏ p ∈ P, p) R).card : ℝ) / R ^ 2 ≤ e R := by
  obtain ⟨C, hC, ht, hu⟩ := HighTransitionRates.exists_uniform_error hc hA
  refine ⟨errorBound c C, ht, ?_⟩
  filter_upwards [hu, eventually_ge_atTop (0 : ℝ)] with R hRu hR
  intro P hcard hP hlo hhi
  exact (collision_density_le P hP hR).trans (hRu _ P rfl hcard hP hlo hhi)

end DistanceCounts.HighTransition
end
end

-- Source: DistanceCounts/FiniteCoordinateSelection.lean
section
/-! Finite-coordinate avoidance by counting restriction fibers and taking a union bound.
The bad events may overlap arbitrarily; no independence hypothesis is used. -/

noncomputable section

open scoped BigOperators

namespace DistanceCounts.FiniteCoordinateSelection

variable {I : Type*} [Fintype I] [DecidableEq I]
  (Ω : I → Type*) [∀ i, Fintype (Ω i)]

/-- Splitting a full assignment into its specified coordinates and all remaining
coordinates. This also applies when either coordinate set is empty. -/
def restrictionEquiv (S : Finset I) :
    (∀ i, Ω i) ≃ (∀ i : S, Ω i) × (∀ i : {i // i ∉ S}, Ω i) := by
  classical
  exact Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω

/-- The number of local tuples is the product of the coordinate cardinalities. -/
theorem card_localTuple (S : Finset I) :
    Fintype.card (∀ i : S, Ω i) = ∏ i ∈ S, Fintype.card (Ω i) := by
  classical
  rw [Fintype.card_pi]
  exact Finset.prod_coe_sort S (fun i => Fintype.card (Ω i))

/-- The same complement factor occurs in the total count and in every restriction
fiber. -/
theorem card_assignments_eq (S : Finset I) :
    Fintype.card (∀ i, Ω i) =
      Fintype.card (∀ i : S, Ω i) * Fintype.card (∀ i : {i // i ∉ S}, Ω i) := by
  classical
  simpa only [Fintype.card_prod] using Fintype.card_congr (restrictionEquiv Ω S)

/-- Local tuples whose injective encoding is forbidden. -/
def localBad (S : Finset I) {R : Type*} (ψ : (∀ i : S, Ω i) → R)
    (B : Finset R) : Finset (∀ i : S, Ω i) := by
  classical
  exact Finset.univ.filter (fun x => ψ x ∈ B)

/-- Full assignments whose restriction has a forbidden encoding. -/
def badAssignments (S : Finset I) {R : Type*} (ψ : (∀ i : S, Ω i) → R)
    (B : Finset R) : Finset (∀ i, Ω i) := by
  classical
  exact Finset.univ.filter (fun ω => ψ (fun i : S => ω i) ∈ B)

/-- Injectivity, not any distributional assumption, bounds the local bad count. -/
theorem card_localBad_le (S : Finset I) {R : Type*}
    (ψ : (∀ i : S, Ω i) → R) (hψ : Function.Injective ψ) (B : Finset R) :
    (localBad Ω S ψ B).card ≤ B.card := by
  classical
  apply Finset.card_le_card_of_injOn ψ
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact hψ hxy

/-- Exact counting of bad full assignments: each bad local tuple has one extension
for every tuple on the complementary coordinates. -/
theorem card_badAssignments_eq (S : Finset I) {R : Type*}
    (ψ : (∀ i : S, Ω i) → R) (B : Finset R) :
    (badAssignments Ω S ψ B).card =
      (localBad Ω S ψ B).card * Fintype.card (∀ i : {i // i ∉ S}, Ω i) := by
  classical
  let e : {ω : (∀ i, Ω i) // ψ (fun i : S => ω i) ∈ B} ≃
      {x : (∀ i : S, Ω i) × (∀ i : {i // i ∉ S}, Ω i) // ψ x.1 ∈ B} :=
    (restrictionEquiv Ω S).subtypeEquiv (fun _ => Iff.rfl)
  let f : {x : (∀ i : S, Ω i) × (∀ i : {i // i ∉ S}, Ω i) // ψ x.1 ∈ B} ≃
      {x : (∀ i : S, Ω i) // ψ x ∈ B} × (∀ i : {i // i ∉ S}, Ω i) :=
    Equiv.prodSubtypeFstEquivSubtypeProd
      (α := ∀ i : S, Ω i) (β := ∀ i : {i // i ∉ S}, Ω i)
      (p := fun x => ψ x ∈ B)
  simpa only [Fintype.card_prod, Fintype.card_subtype, badAssignments, localBad]
    using Fintype.card_congr (e.trans f)

/-- The forbidden-image count times the unrestricted complement count bounds the
actual number of bad full assignments. -/
theorem card_badAssignments_le (S : Finset I) {R : Type*}
    (ψ : (∀ i : S, Ω i) → R) (hψ : Function.Injective ψ) (B : Finset R) :
    (badAssignments Ω S ψ B).card ≤
      B.card * Fintype.card (∀ i : {i // i ∉ S}, Ω i) := by
  rw [card_badAssignments_eq]
  exact Nat.mul_le_mul_right _ (card_localBad_le Ω S ψ hψ B)

/-- Cancelling the complement factor gives the exact finite-coordinate fraction
bound. Nonempty coordinate spaces ensure that neither denominator vanishes. -/
theorem bad_assignment_fraction_le [∀ i, Nonempty (Ω i)]
    (S : Finset I) {R : Type*} (ψ : (∀ i : S, Ω i) → R)
    (hψ : Function.Injective ψ) (B : Finset R) :
    ((badAssignments Ω S ψ B).card : ℝ) / Fintype.card (∀ i, Ω i) ≤
      (B.card : ℝ) / (∏ i ∈ S, Fintype.card (Ω i) : ℕ) := by
  classical
  have hL : 0 < (Fintype.card (∀ i : S, Ω i) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (∀ i : S, Ω i))
  have hC : 0 < (Fintype.card (∀ i : {i // i ∉ S}, Ω i) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos : 0 < Fintype.card (∀ i : {i // i ∉ S}, Ω i))
  calc
    ((badAssignments Ω S ψ B).card : ℝ) / Fintype.card (∀ i, Ω i) =
        ((badAssignments Ω S ψ B).card : ℝ) /
          ((Fintype.card (∀ i : S, Ω i) : ℝ) *
            Fintype.card (∀ i : {i // i ∉ S}, Ω i)) := by
      rw [card_assignments_eq Ω S, Nat.cast_mul]
    _ ≤ ((B.card : ℝ) * Fintype.card (∀ i : {i // i ∉ S}, Ω i)) /
          ((Fintype.card (∀ i : S, Ω i) : ℝ) *
            Fintype.card (∀ i : {i // i ∉ S}, Ω i)) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hL.le hC.le)
      exact_mod_cast card_badAssignments_le Ω S ψ hψ B
    _ = (B.card : ℝ) / Fintype.card (∀ i : S, Ω i) :=
      mul_div_mul_right _ _ (ne_of_gt hC)
    _ = (B.card : ℝ) / (∏ i ∈ S, Fintype.card (Ω i) : ℕ) := by
      rw [card_localTuple]

variable {E : Type*} [Fintype E]

/-- The union of the actual bad events in the full function space. -/
def badUnion (S : E → Finset I) (R : E → Type*)
    (ψ : ∀ e, (∀ i : S e, Ω i) → R e) (B : ∀ e, Finset (R e)) :
    Finset (∀ i, Ω i) := by
  classical
  exact Finset.univ.biUnion (fun e => badAssignments Ω (S e) (ψ e) (B e))

/-- A quantitative union bound, valid even when different events share all their
coordinates or their bad assignments. -/
theorem bad_union_fraction_le [∀ i, Nonempty (Ω i)]
    (S : E → Finset I) (R : E → Type*)
    (ψ : ∀ e, (∀ i : S e, Ω i) → R e)
    (hψ : ∀ e, Function.Injective (ψ e)) (B : ∀ e, Finset (R e)) :
    ((badUnion Ω S R ψ B).card : ℝ) / Fintype.card (∀ i, Ω i) ≤
      ∑ e, ((B e).card : ℝ) / (∏ i ∈ S e, Fintype.card (Ω i) : ℕ) := by
  classical
  have htotal : 0 ≤ (Fintype.card (∀ i, Ω i) : ℝ) := Nat.cast_nonneg _
  have hcount : (badUnion Ω S R ψ B).card ≤
      ∑ e, (badAssignments Ω (S e) (ψ e) (B e)).card :=
    Finset.card_biUnion_le
  calc
    ((badUnion Ω S R ψ B).card : ℝ) / Fintype.card (∀ i, Ω i) ≤
        ((∑ e, (badAssignments Ω (S e) (ψ e) (B e)).card : ℕ) : ℝ) /
          Fintype.card (∀ i, Ω i) := by
      apply div_le_div_of_nonneg_right _ htotal
      exact_mod_cast hcount
    _ = ∑ e, ((badAssignments Ω (S e) (ψ e) (B e)).card : ℝ) /
          Fintype.card (∀ i, Ω i) := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum fun e _ =>
      bad_assignment_fraction_le Ω (S e) (ψ e) (hψ e) (B e)

/-- Simultaneous avoidance in the genuine finite dependent function space.
Only injectivity of the local encodings and the numerical union bound are
required; no independence between events or prior good assignment is assumed.
Empty event sets and empty coordinate sets are included. -/
theorem exists_avoiding [∀ i, Nonempty (Ω i)]
    (S : E → Finset I) (R : E → Type*)
    (ψ : ∀ e, (∀ i : S e, Ω i) → R e)
    (hψ : ∀ e, Function.Injective (ψ e)) (B : ∀ e, Finset (R e))
    (hsmall : (∑ e, ((B e).card : ℝ) /
      (∏ i ∈ S e, Fintype.card (Ω i) : ℕ) : ℝ) < 1) :
    ∃ ω : ∀ i, Ω i, ∀ e, ψ e (fun i : S e => ω i) ∉ B e := by
  classical
  have htotal : 0 < (Fintype.card (∀ i, Ω i) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (∀ i, Ω i))
  have hfrac := (bad_union_fraction_le Ω S R ψ hψ B).trans_lt hsmall
  have hltReal : ((badUnion Ω S R ψ B).card : ℝ) <
      (Fintype.card (∀ i, Ω i) : ℝ) := (div_lt_one htotal).mp hfrac
  have hlt : (badUnion Ω S R ψ B).card < (Finset.univ : Finset (∀ i, Ω i)).card := by
    exact_mod_cast hltReal
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨ω, fun e he => hω ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨e, Finset.mem_univ _, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩

end DistanceCounts.FiniteCoordinateSelection
end
end

-- Source: DistanceCounts/OffsetSelection.lean
section
noncomputable section

open Filter Finset
open scoped Topology Classical BigOperators

namespace DistanceCounts.OffsetSelection

open CoarseGrid PairModulus CoarseConditions GaussianResidues

abbrev Axis (s : ℕ) := Fin (2 * s) ⊕ Fin (2 * s)
abbrev Block (s : ℕ) := Fin (2 * s) × Fin (2 * s)
abbrev Event (s : ℕ) := (Block s × Block s) ⊕ Axis s

def primes (s L : ℕ) : Axis s → ℕ :=
  PrimeScaleFamilies.primeFamily ThresholdWeights.weight L

lemma primes_prime (s L : ℕ) (i : Axis s) : (primes s L i).Prime :=
  PrimeScaleFamilies.primeFamily_prime _ _ _

lemma primes_inert (s L : ℕ) (i : Axis s) : primes s L i % 4 = 3 :=
  PrimeScaleFamilies.primeFamily_mod_four _ _ _

lemma primes_injective {s : ℕ} (hs : 0 < s) :
    ∀ᶠ L in atTop, Function.Injective (primes s L) :=
  PrimeScaleFamilies.eventually_primeFamily_injective _
    (ThresholdWeights.weight_pos (by omega))

lemma primes_tendsto {s : ℕ} (hs : 0 < s) (i : Axis s) :
    Tendsto (fun L => (primes s L i : ℝ)) atTop atTop := by
  have hw := ThresholdWeights.weight_pos (show 0 < 2 * s by omega) i
  have hwin := PrimeScaleFamilies.eventually_power_window
    (Eventually.of_forall fun L => show (0 : ℝ) < primes s L i by
      exact_mod_cast (primes_prime s L i).pos)
    (PrimeScaleFamilies.tendsto_primeFamily_log ThresholdWeights.weight
      (ThresholdWeights.weight_pos (show 0 < 2 * s by omega)) i)
    (show 0 < ThresholdWeights.weight i / 2 by positivity)
  apply tendsto_atTop_mono' _ _
    ((tendsto_rpow_atTop (show 0 < ThresholdWeights.weight i -
      ThresholdWeights.weight i / 2 by linarith)).comp PrimeScaleFamilies.tendsto_log_nat)
  exact hwin.mono fun _ h => h.1

lemma radius_tendsto (s : ℕ) (b c : Block s) :
    Tendsto (fun L => pairRadius L (primes s L) b c) atTop atTop :=
  PrimeScaleFamilies.tendsto_radius ThresholdWeights.weight (pairSupport b c)
    (show (0 : ℝ) < 6 by norm_num)

/-- The error is the actual normalized population relevant to this ordered pair. -/
def pairError (s L : ℕ) (b c : Block s) : ℝ :=
  if (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val then
    ((HighCollisionCover.collisionVectors (modulus (primes s L) b c)
      (pairRadius L (primes s L) b c)).card : ℝ) /
      (pairRadius L (primes s L) b c) ^ 2
  else
    LowPalette.aggregate (modulus (primes s L) b c)
      (modulus_pos _ (primes_prime s L) b c) (pairRadius L (primes s L) b c) /
      (pairRadius L (primes s L) b c) ^ 2

lemma pairError_nonneg (s L : ℕ) (b c : Block s) : 0 ≤ pairError s L b c := by
  unfold pairError LowPalette.aggregate
  split_ifs <;> positivity

lemma pairError_tendsto {s : ℕ} (hs : 0 < s) (b c : Block s) :
    Tendsto (fun L => pairError s L b c) atTop (𝓝 0) := by
  let a := ThresholdWeights.pairExponent b c
  have hw := ThresholdWeights.weight_pos (show 0 < 2 * s by omega)
  have hr := radius_tendsto s b c
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => (hw i).le
  by_cases hh : (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val
  · have hgap : Real.log 2 < a :=
      (ThresholdWeights.log_two_lt_pairExponent_iff hs b c).mpr hh
    let δ := (a - Real.log 2) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hc : Real.log 2 < a - δ := by dsimp [δ]; linarith
    obtain ⟨e, he, hu⟩ := HighTransition.exists_uniform_collision_error hc
      (show 0 < a + δ by linarith)
    have hwin := PrimeScaleFamilies.eventually_subsetModulus_radius_window
      ThresholdWeights.weight hw (pairSupport b c) (show (0 : ℝ) < 6 by norm_num) hδ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (he.comp hr)
      (Eventually.of_forall fun L => pairError_nonneg s L b c)
    filter_upwards [hr.eventually hu, hwin, primes_injective hs] with L hU hW hd
    have h := hU (primeSet (primes s L) b c) (primeSet_card_le_four _ b c)
      (fun r hr => by
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
        exact ⟨primes_prime s L i, primes_inert s L i⟩)
    have hq := modulus_eq_primeSet_prod (primes s L) hd b c
    have hlo : (Real.log (pairRadius L (primes s L) b c)) ^ (a - δ) ≤
        (modulus (primes s L) b c : ℝ) := hW.1
    have hhi : (modulus (primes s L) b c : ℝ) ≤
        (Real.log (pairRadius L (primes s L) b c)) ^ (a + δ) := hW.2
    rw [hq] at hlo hhi
    simpa only [Function.comp_def, pairError, if_pos hh, hq] using h hlo hhi
  · have hgap : a < Real.log 2 :=
      (ThresholdWeights.pairExponent_lt_log_two_iff hs b c).mpr hh
    let δ := (Real.log 2 - a) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hc : a + δ < Real.log 2 := by dsimp [δ]; linarith
    have hwin := PrimeScaleFamilies.eventually_subsetModulus_radius_window
      ThresholdWeights.weight hw (pairSupport b c) (show (0 : ℝ) < 6 by norm_num) hδ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((LowPalette.tendsto_error hc).comp hr)
      (Eventually.of_forall fun L => pairError_nonneg s L b c)
    filter_upwards [hr.eventually (LowPalette.eventually_uniform_low hc),
      hwin, primes_injective hs] with L hU hW hd
    have hq := modulus_eq_primeSet_prod (primes s L) hd b c
    have hhi : (modulus (primes s L) b c : ℝ) ≤
        (Real.log (pairRadius L (primes s L) b c)) ^ (a + δ) := hW.2
    rw [hq] at hhi
    simpa only [Function.comp_def, pairError, if_neg hh, hq] using hU (primeSet (primes s L) b c)
      (primeSet_prime _ (primes_prime s L) b c) (primeSet_card_le_four _ b c) hhi

/-- All ordered block pairs remain in this sum, including self pairs. -/
def totalError (s L : ℕ) : ℝ := ∑ bc : Block s × Block s, max 0 (pairError s L bc.1 bc.2)

def tolerance (s L : ℕ) : ℝ := Real.sqrt (totalError s L) + 1 / ((L : ℝ) + 1)

lemma totalError_nonneg (s L : ℕ) : 0 ≤ totalError s L :=
  Finset.sum_nonneg fun _ _ => le_max_left _ _

lemma pairError_le_total (s L : ℕ) (b c : Block s) : pairError s L b c ≤ totalError s L :=
  (le_max_right _ _).trans (Finset.single_le_sum
    (f := fun bc : Block s × Block s => max 0 (pairError s L bc.1 bc.2))
    (fun _ _ => le_max_left _ _)
    (Finset.mem_univ (b, c)))

lemma totalError_tendsto {s : ℕ} (hs : 0 < s) :
    Tendsto (totalError s) atTop (𝓝 0) := by
  unfold totalError
  have h := tendsto_finset_sum (Finset.univ : Finset (Block s × Block s))
    (fun bc _ => (tendsto_const_nhds (x := (0 : ℝ))).max
      (pairError_tendsto hs bc.1 bc.2))
  simpa [totalError] using h

lemma tolerance_pos (s L : ℕ) : 0 < tolerance s L :=
  add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)

lemma tolerance_tendsto {s : ℕ} (hs : 0 < s) :
    Tendsto (tolerance s) atTop (𝓝 0) := by
  unfold tolerance
  have hL : Tendsto (fun L : ℕ => (L : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun L => by linarith) tendsto_natCast_atTop_atTop
  have h := ((totalError_tendsto hs).sqrt).add
    (tendsto_inv_atTop_zero.comp hL)
  simpa only [Function.comp_def, one_div, Real.sqrt_zero, zero_add] using h

lemma error_div_tolerance (s L : ℕ) (b c : Block s) :
    pairError s L b c / tolerance s L ≤ Real.sqrt (totalError s L) := by
  apply (div_le_iff₀ (tolerance_pos s L)).mpr
  have hs := Real.sq_sqrt (totalError_nonneg s L)
  have hp : 0 ≤ Real.sqrt (totalError s L) * (1 / ((L : ℝ) + 1)) := by positivity
  have h := pairError_le_total s L b c
  dsimp [tolerance]
  nlinarith

/-- The denominator counts the genuine local unit tuples. -/
def localCard {s : ℕ} (p : Axis s → ℕ) (S : Finset (Axis s)) : ℕ :=
  ∏ i ∈ S, Nat.card (Residue (p i))ˣ

lemma unitCard_lower (p : ℕ) (hp : p.Prime) (hi : p % 4 = 3) :
    (8 / 9 : ℝ) * (p : ℝ) ^ 2 ≤ (Nat.card (Residue p)ˣ : ℝ) := by
  rw [card_unit_group_inert p hp hi]
  have hp3 : 3 ≤ p := by omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  rw [Nat.cast_sub hp2, Nat.cast_pow, Nat.cast_one]
  nlinarith [sq_nonneg ((p : ℝ) - 3)]

lemma localCard_lower {s : ℕ} (p : Axis s → ℕ)
    (hp : ∀ i, (p i).Prime) (hi : ∀ i, p i % 4 = 3)
    (S : Finset (Axis s)) (hS : S.card ≤ 4) :
    ((∏ i ∈ S, p i : ℕ) : ℝ) ^ 2 / 2 ≤ (localCard p S : ℝ) := by
  have hprod : (8 / 9 : ℝ) ^ S.card * ((∏ i ∈ S, p i : ℕ) : ℝ) ^ 2 ≤
      (localCard p S : ℝ) := by
    rw [localCard, Nat.cast_prod, Nat.cast_prod]
    calc
      _ = ∏ i ∈ S, ((8 / 9 : ℝ) * (p i : ℝ) ^ 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity)
        (fun i _ => unitCard_lower (p i) (hp i) (hi i))
  have hpow : (8 / 9 : ℝ) ^ 4 ≤ (8 / 9 : ℝ) ^ S.card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hS
  exact (GaussianUnitCRT.half_square_le_four_fraction _).trans
    ((mul_le_mul_of_nonneg_right hpow (sq_nonneg _)).trans hprod)

def eventSupport {s : ℕ} : Event s → Finset (Axis s)
  | .inl bc => pairSupport bc.1 bc.2
  | .inr i => {i}

def eventResidue {s : ℕ} (p : Axis s → ℕ) : Event s → Type
  | .inl bc => Residue (modulus p bc.1 bc.2)
  | .inr i => Residue (p i)

def eventMap {s : ℕ} (p : Axis s → ℕ) :
    ∀ e : Event s, (∀ i : eventSupport e, (Residue (p i.1))ˣ) → eventResidue p e
  | .inl bc => localChoiceMap p bc.1 bc.2
  | .inr i => fun u => (u ⟨i, Finset.mem_singleton_self i⟩ : Residue (p i))

lemma eventMap_injective {s : ℕ} (p : Axis s → ℕ)
    (hp : ∀ i, (p i).Prime) (hd : Function.Injective p) (e : Event s) :
    Function.Injective (eventMap p e) := by
  cases e with
  | inl bc => exact localChoiceMap_injective p hp hd bc.1 bc.2
  | inr i =>
    intro u v h
    funext j
    obtain ⟨j, hj⟩ := j
    have hji : j = i := Finset.mem_singleton.mp hj
    subst j
    exact Units.ext h

def eventBad (s L : ℕ) : ∀ e : Event s, Finset (eventResidue (primes s L) e)
  | .inl bc =>
    if (bc.2.1.val, bc.2.2.val) ∈ DistanceCounts.highTargets s bc.1.1.val bc.1.2.val then
      ResidueExceptions.badHigh (modulus (primes s L) bc.1 bc.2)
        (modulus_pos _ (primes_prime s L) bc.1 bc.2)
        (pairRadius L (primes s L) bc.1 bc.2) (tolerance s L * (L : ℝ) ^ 2)
    else
      ResidueExceptions.badLow (modulus (primes s L) bc.1 bc.2)
        (modulus_pos _ (primes_prime s L) bc.1 bc.2)
        (pairRadius L (primes s L) bc.1 bc.2) (tolerance s L * (L : ℝ) ^ 2)
  | .inr i => ResidueExceptions.badProjectedUnits (primes s L i)
      (primes_prime s L i).pos (L : ZMod (primes s L i))

private theorem eventBad_pair_high (s L : ℕ) (b c : Block s)
    (hh : (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val) :
    eventBad s L (.inl (b, c)) =
      ResidueExceptions.badHigh (modulus (primes s L) b c)
        (modulus_pos _ (primes_prime s L) b c)
        (pairRadius L (primes s L) b c) (tolerance s L * (L : ℝ) ^ 2) := by
  unfold eventBad
  exact if_pos hh

private theorem eventBad_pair_low (s L : ℕ) (b c : Block s)
    (hh : (c.1.val, c.2.val) ∉ DistanceCounts.highTargets s b.1.val b.2.val) :
    eventBad s L (.inl (b, c)) =
      ResidueExceptions.badLow (modulus (primes s L) b c)
        (modulus_pos _ (primes_prime s L) b c)
        (pairRadius L (primes s L) b c) (tolerance s L * (L : ℝ) ^ 2) := by
  unfold eventBad
  exact if_neg hh

lemma bad_pair_fraction (s L : ℕ) (hL : 0 < L) (b c : Block s) :
    ((eventBad s L (.inl (b, c))).card : ℝ) /
      (modulus (primes s L) b c : ℝ) ^ 2 ≤ 36 * Real.sqrt (totalError s L) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hnorm : ((eventBad s L (.inl (b, c))).card : ℝ) /
      (modulus (primes s L) b c : ℝ) ^ 2 ≤ 36 * (pairError s L b c / tolerance s L) := by
    by_cases hh : (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val
    · rw [eventBad_pair_high s L b c hh]
      have h := ResidueExceptions.badHigh_normalized
        (modulus (primes s L) b c) (modulus_pos _ (primes_prime s L) b c)
        (show (0 : ℝ) < 6 by norm_num) hLr (tolerance_pos s L)
        (show pairRadius L (primes s L) b c =
          6 * (modulus (primes s L) b c : ℝ) * L from rfl)
      convert h using 1 <;> norm_num [pairError, hh, mul_div_assoc]
      rfl
    · rw [eventBad_pair_low s L b c hh]
      have h := ResidueExceptions.badLow_normalized
        (modulus (primes s L) b c) (modulus_pos _ (primes_prime s L) b c)
        (show (0 : ℝ) < 6 by norm_num) hLr (tolerance_pos s L)
        (show pairRadius L (primes s L) b c =
          6 * (modulus (primes s L) b c : ℝ) * L from rfl)
      convert h using 1 <;> norm_num [pairError, hh, mul_div_assoc]
      rfl
  exact hnorm.trans (mul_le_mul_of_nonneg_left (error_div_tolerance s L b c) (by norm_num))

private lemma fraction_le_twice {B Q D : ℝ} (hB : 0 ≤ B) (hQ : 0 < Q)
    (hD : Q ^ 2 / 2 ≤ D) : B / D ≤ 2 * (B / Q ^ 2) := by
  calc
    _ ≤ B / (Q ^ 2 / 2) :=
      div_le_div_of_nonneg_left hB (by positivity) hD
    _ = _ := by ring

def eventBound (s L : ℕ) : Event s → ℝ
  | .inl _ => 72 * Real.sqrt (totalError s L)
  | .inr i => 2 / (primes s L i : ℝ)

lemma event_fraction_le (s L : ℕ) (hL : 0 < L) (e : Event s) :
    ((eventBad s L e).card : ℝ) / (localCard (primes s L) (eventSupport e) : ℝ) ≤
      eventBound s L e := by
  cases e with
  | inl bc =>
    have hd := localCard_lower (primes s L) (primes_prime s L) (primes_inert s L)
      (pairSupport bc.1 bc.2) (pairSupport_card_le_four bc.1 bc.2)
    have hq : (0 : ℝ) < modulus (primes s L) bc.1 bc.2 := by
      exact_mod_cast modulus_pos _ (primes_prime s L) bc.1 bc.2
    have h := (fraction_le_twice (Nat.cast_nonneg _) hq hd).trans
      (mul_le_mul_of_nonneg_left (bad_pair_fraction s L hL bc.1 bc.2) (by norm_num))
    simpa only [eventSupport, eventBound, ← mul_assoc, show (2 : ℝ) * 36 = 72 by norm_num]
      using h
  | inr i =>
    have hp : (0 : ℝ) < primes s L i := by
      exact_mod_cast (primes_prime s L i).pos
    have hd := localCard_lower (primes s L) (primes_prime s L) (primes_inert s L)
      {i} (by simp)
    simp only [Finset.prod_singleton] at hd
    have hcard : ((eventBad s L (.inr i)).card : ℝ) ≤ primes s L i := by
      exact_mod_cast ResidueExceptions.badProjectedUnits_card_le (primes s L i)
        (primes_prime s L i) (L : ZMod (primes s L i))
    calc
      _ ≤ 2 * (((eventBad s L (.inr i)).card : ℝ) / (primes s L i : ℝ) ^ 2) :=
        fraction_le_twice (Nat.cast_nonneg _) hp hd
      _ ≤ 2 * ((primes s L i : ℝ) / (primes s L i : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcard (sq_nonneg _))
          (by norm_num)
      _ = eventBound s L (.inr i) := by
        dsimp [eventBound]
        field_simp [hp.ne']
        <;> ring

lemma eventBound_tendsto {s : ℕ} (hs : 0 < s) (e : Event s) :
    Tendsto (fun L => eventBound s L e) atTop (𝓝 0) := by
  cases e with
  | inl bc =>
    simpa [eventBound] using ((totalError_tendsto hs).sqrt).const_mul 72
  | inr i =>
    exact tendsto_const_nhds.div_atTop (primes_tendsto hs i)


end DistanceCounts.OffsetSelection
end
end


open Finset

namespace OMA.GridOffsets

/-- Among all pairs of residues, at most `3 * q` lie on one of the three forbidden lines. -/
theorem bad_coordinate_card (q : ℕ) [NeZero q] (l : ZMod q) :
    ((univ : Finset (ZMod q × ZMod q)).filter (fun z =>
      z.1 = 0 ∨ z.2 = 0 ∨ z.1 + l * z.2 = 0)).card ≤ 3 * q := by
  classical
  let X := (univ : Finset (ZMod q)).image (fun v => ((0 : ZMod q), v))
  let Y := (univ : Finset (ZMod q)).image (fun u => (u, (0 : ZMod q)))
  let D := (univ : Finset (ZMod q)).image (fun v => (-l * v, v))
  have hsub : univ.filter (fun z : ZMod q × ZMod q =>
      z.1 = 0 ∨ z.2 = 0 ∨ z.1 + l * z.2 = 0) ⊆ (X ∪ Y) ∪ D := by
    rintro ⟨u,v⟩ h
    rcases (mem_filter.mp h).2 with hu | hv | hd
    · exact mem_union_left _ (mem_union_left _
        (mem_image.mpr ⟨v, mem_univ _, Prod.ext hu.symm rfl⟩))
    · exact mem_union_left _ (mem_union_right _
        (mem_image.mpr ⟨u, mem_univ _, Prod.ext rfl hv.symm⟩))
    · apply mem_union_right _
      refine mem_image.mpr ⟨v, mem_univ _, Prod.ext ?_ rfl⟩
      change u + l * v = 0 at hd
      linear_combination -hd
  have hX : X.card ≤ q := (card_image_le).trans_eq (by simp)
  have hY : Y.card ≤ q := (card_image_le).trans_eq (by simp)
  have hD : D.card ≤ q := (card_image_le).trans_eq (by simp)
  have hXY := card_union_le X Y
  have hU := card_union_le (X ∪ Y) D
  exact (card_le_card hsub).trans (by omega)

end OMA.GridOffsets

noncomputable section
open Filter Finset
open scoped Topology Classical
namespace DistanceCounts.ThreeProjections
open GaussianResidues CoarseConditions OffsetSelection PairModulus CoarseGrid

def badLines (q : ℕ) (hq : 0 < q) (l : ZMod q) : Finset (Residue q) :=
  (LowPalette.allResidues q hq).filter fun a => (coordinates q a).1 = 0 ∨
    (coordinates q a).2 = 0 ∨ (coordinates q a).1 + l * (coordinates q a).2 = 0

theorem badLines_card (q : ℕ) (hq : 0 < q) (l : ZMod q) : (badLines q hq l).card ≤ 3 * q := by
  letI : NeZero q := ⟨hq.ne'⟩
  apply le_trans _ (OMA.GridOffsets.bad_coordinate_card q l)
  apply card_le_card_of_injOn (coordinates q)
  · intro a ha
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩
  · exact (coordinates_injective q).injOn

def bad (s L : ℕ) : (e : Event s) → Finset (eventResidue (primes s L) e)
  | .inl bc => eventBad s L (.inl bc)
  | .inr i => badLines (primes s L i) (primes_prime s L i).pos L

theorem fraction {s L : ℕ} (hL : 0 < L) (e : Event s) :
    ((bad s L e).card : ℝ) / (localCard (primes s L) (eventSupport e) : ℝ) ≤
      3 * eventBound s L e := by
  cases e with
  | inl bc =>
    have hp : 0 ≤ eventBound s L (.inl bc) := by simp only [eventBound]; positivity
    exact (event_fraction_le s L hL (.inl bc)).trans (by linarith)
  | inr i =>
    let p := primes s L i
    have hp : 0 < (p : ℝ) := by exact_mod_cast (primes_prime s L i).pos
    have hd := localCard_lower (primes s L) (primes_prime s L) (primes_inert s L) {i} (by simp)
    simp only [prod_singleton] at hd
    have hD : 0 < (localCard (primes s L) {i} : ℝ) :=
      (show 0 < (p : ℝ)^2 / 2 by positivity).trans_le hd
    have hc : ((bad s L (.inr i)).card : ℝ) ≤ 3 * p := by
      exact_mod_cast badLines_card p (primes_prime s L i).pos L
    change _ / (localCard (primes s L) {i} : ℝ) ≤ 3 * (2 / (p : ℝ))
    apply (div_le_iff₀ hD).mpr
    apply hc.trans
    calc
      3 * (p : ℝ) = (3 * (2 / (p : ℝ))) * ((p : ℝ)^2 / 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

theorem eventually_units {s : ℕ} (hs : 0 < s) :
    ∀ᶠ L : ℕ in atTop, ∃ ω : ∀ i : Axis s, (Residue (primes s L i))ˣ,
      ∀ e : Event s, eventMap (primes s L) e (fun i : eventSupport e => ω i.1) ∉ bad s L e := by
  have ht := tendsto_finsetSum (univ : Finset (Event s))
    (fun e _ => (eventBound_tendsto hs e).const_mul 3)
  simp only [mul_zero, sum_const_zero] at ht
  filter_upwards [primes_injective hs, ht.eventually (gt_mem_nhds (zero_lt_one' ℝ)),
    eventually_gt_atTop (0 : ℕ)] with L hd hsmall hL
  letI : ∀ i : Axis s, Finite (Residue (primes s L i)) :=
    fun i => finite_residue _ (primes_prime s L i).pos
  letI : ∀ i : Axis s, Fintype (Residue (primes s L i))ˣ := fun _ => Fintype.ofFinite _
  apply FiniteCoordinateSelection.exists_avoiding
    (fun i : Axis s => (Residue (primes s L i))ˣ) eventSupport
    (eventResidue (primes s L)) (eventMap (primes s L))
    (eventMap_injective _ (primes_prime s L) hd) (bad s L)
  have h := (Finset.sum_le_sum (fun e (_ : e ∈ (univ : Finset (Event s))) => fraction hL e)).trans_lt hsmall
  simpa only [localCard, Nat.card_eq_fintype_card] using h

private theorem eventBad_pair_high (s L : ℕ) (b c : Block s)
    (hh : (c.1.val, c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val) :
    eventBad s L (.inl (b, c)) =
      ResidueExceptions.badHigh (modulus (primes s L) b c)
        (modulus_pos _ (primes_prime s L) b c)
        (pairRadius L (primes s L) b c) (tolerance s L * (L : ℝ) ^ 2) := by
  unfold eventBad
  exact if_pos hh

private theorem eventBad_pair_low (s L : ℕ) (b c : Block s)
    (hh : (c.1.val, c.2.val) ∉ DistanceCounts.highTargets s b.1.val b.2.val) :
    eventBad s L (.inl (b, c)) =
      ResidueExceptions.badLow (modulus (primes s L) b c)
        (modulus_pos _ (primes_prime s L) b c)
        (pairRadius L (primes s L) b c) (tolerance s L * (L : ℝ) ^ 2) := by
  unfold eventBad
  exact if_neg hh


/-- In the same choice, retain the disk norm estimates and avoid all three projections. -/
theorem eventually_lifts {s : ℕ} (hs : 0 < s) :
    ∀ᶠ L : ℕ in atTop, ∃ z : Axis s → GaussianInt,
      BoundedOffsets (primes s L) z ∧ (∀ i, IsUnit (GaussianNorm.residue (primes s L i) (z i))) ∧
      (∀ i, ¬ (primes s L i : ℤ) ∣ (z i).re) ∧ (∀ i, ¬ (primes s L i : ℤ) ∣ (z i).im) ∧
      (∀ i, ¬ (primes s L i : ℤ) ∣ (z i).re + (L : ℤ) * (z i).im) ∧
      PaletteBounds s L (primes s L) z (tolerance s L) := by
  filter_upwards [eventually_units hs, primes_injective hs] with L ⟨ω,hω⟩ hd
  let z (i : Axis s) := BoundedResidueLift.lift (primes s L i) (ω i)
  have hr i : GaussianNorm.residue (primes s L i) (z i) = (ω i : Residue (primes s L i)) :=
    BoundedResidueLift.residue_lift _ (primes_prime s L i).pos _
  have hc (i) : ¬ ((primes s L i : ℤ) ∣ (z i).re ∨ (primes s L i : ℤ) ∣ (z i).im ∨
      (primes s L i : ℤ) ∣ (z i).re + (L : ℤ) * (z i).im) := by
    intro he
    apply hω (.inr i)
    change (ω i : Residue _) ∈ badLines (primes s L i) _ _
    apply mem_filter.mpr
    refine ⟨(LowPalette.mem_allResidues _ _ _), ?_⟩
    rw [← hr i, coordinates_residue]
    rcases he with hr | hi | ho
    · exact Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr)
    · exact Or.inr (Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hi))
    · right; right
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ho
  refine ⟨z, boundedOffsets_lift _ (primes_prime s L) _,
    fun i => hr i ▸ (ω i).isUnit, fun i h => hc i (Or.inl h),
    fun i h => hc i (Or.inr (Or.inl h)), fun i h => hc i (Or.inr (Or.inr h)), ?_⟩
  intro b c
  have he := localChoiceMap_eq_numerator (primes s L) (primes_prime s L) hd b c
    (fun i : pairSupport b c => ω i.1) z (fun i => hr i.1)
  let T : Finset (Residue (modulus (primes s L) b c)) := eventBad s L (.inl (b,c))
  have h0 : localChoiceMap (primes s L) b c (fun i : pairSupport b c => ω i.1) ∉ T :=
    hω (.inl (b,c))
  have h : GaussianNorm.residue (modulus (primes s L) b c) (numerator (primes s L) z b c) ∉ T := by
    rw [← he]
    exact h0
  change pairResidue (primes s L) z b c ∉ eventBad s L (.inl (b,c)) at h
  by_cases hh : (c.1.val,c.2.val) ∈ DistanceCounts.highTargets s b.1.val b.2.val
  · rw [eventBad_pair_high s L b c hh] at h
    simpa only [if_pos hh] using ResidueExceptions.collisionFiber_card_le_of_not_badHigh h
  · rw [eventBad_pair_low s L b c hh] at h
    simpa only [if_neg hh] using ResidueExceptions.palette_card_le_of_not_badLow h

end DistanceCounts.ThreeProjections
end


noncomputable section
open Finset Filter
open scoped Topology
namespace DistanceCounts.GridNorms
open PairModulus CoarseConditions OffsetSeparation

private abbrev Block (t : ℕ) := Fin t × Fin t

private def strong {t : ℕ} (i : Fin t) : Finset (Fin t) :=
  (Ioi i.rev).erase i

private def high {t : ℕ} (u : Block t) : Finset (Block t) :=
  (strong u.1).product univ ∪ ({u.1.rev} : Finset (Fin t)).product (strong u.2)

private theorem mem_strong {t : ℕ} {i j : Fin t} :
    j ∈ strong i ↔ j ≠ i ∧ t - 1 < i.val + j.val := by
  rw [strong, mem_erase, mem_Ioi]
  simp only [Fin.lt_def, Fin.val_rev]
  omega

private theorem mem_high {t : ℕ} {u v : Block t} :
    v ∈ high u ↔ (v.1 ≠ u.1 ∧ t - 1 < u.1.val + v.1.val) ∨
      (u.1.val + v.1.val = t - 1 ∧ v.2 ≠ u.2 ∧ t - 1 < u.2.val + v.2.val) := by
  rw [high]
  rw [mem_union]
  change v ∈ (strong u.1 ×ˢ univ) ∨ v ∈ ({u.1.rev} ×ˢ strong u.2) ↔ _
  simp only [mem_product, mem_univ, and_true, mem_singleton, mem_strong]
  rw [show v.1 = u.1.rev ↔ u.1.val + v.1.val = t - 1 by
    rw [Fin.ext_iff, Fin.val_rev]
    omega]

private abbrev Label (t : ℕ) := Fin t ⊕ Fin t

private def mark {t : ℕ} (b : Block t) (k : Label t) : ℤ :=
  match k with
  | .inl i => if b.1 = i then 1 else 0
  | .inr j => if b.2 = j then 1 else 0

private def commonDen {t : ℕ} (p : Label t → ℕ) : ℕ := ∏ k, p k

private def cofactor {t : ℕ} (p : Label t → ℕ) (k : Label t) : ℕ :=
  ∏ i ∈ univ.erase k, p i

private def centerCoord {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ) (b : Block t) : ℤ :=
  ∑ k, mark b k * (cofactor p k : ℤ) * z k

private def shiftedCoord {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ)
    (u v : Block t) (a : ℤ) : ℤ :=
  centerCoord p z u - centerCoord p z v + (commonDen p : ℤ) * a

private def shiftedNorm {t : ℕ} (p : Label t → ℕ) (x y : Label t → ℤ)
    (u v : Block t) (a : ℤ × ℤ) : ℤ :=
  shiftedCoord p x u v a.1 ^ 2 + shiftedCoord p y u v a.2 ^ 2

private theorem commonDen_pos {t : ℕ} {p : Label t → ℕ} (hp : ∀ k, (p k).Prime) :
    0 < commonDen p :=
  prod_pos fun k _ => (hp k).pos

private theorem centerCoord_eq {t : ℕ} (p : Label t → ℕ) (z : Label t → ℤ)
    (u : Block t) :
    centerCoord p z u =
      (cofactor p (.inl u.1) : ℤ) * z (.inl u.1) +
        (cofactor p (.inr u.2) : ℤ) * z (.inr u.2) := by
  rw [centerCoord, Fintype.sum_sum_type]
  simp [mark, ite_mul, eq_comm (a := u.1), eq_comm (a := u.2)]

private def box (L : ℕ) : Finset (ℤ × ℤ) :=
  (Ico (-(L : ℤ)) (L : ℤ)).product (Ico (-(L : ℤ)) (L : ℤ))

private theorem high_iff {s : ℕ} (hs : 0 < s) (b c : Block (2*s)) :
    c ∈ high b ↔ (c.1.val,c.2.val) ∈ highTargets s b.1.val b.2.val := by
  rw [mem_high]
  simp only [highTargets, mem_filter, mem_product, mem_range, c.1.isLt, c.2.isLt,
    and_self, true_and]
  rw [high_rule_iff (by omega) b.2.isLt c.2.isLt]
  have hb := b.1.isLt
  have hc := c.1.isLt
  simp only [ne_eq, Fin.ext_iff]
  omega

private def vec {t : ℕ} (p : Label t → ℕ) (z : Label t → GaussianInt)
    (b c : Block t) (a : ℤ × ℤ) : GaussianInt :=
  numerator p z b c + (modulus p b c : GaussianInt) * ⟨a.1,a.2⟩

private theorem vec_injective {t : ℕ} (p : Label t → ℕ) (z : Label t → GaussianInt)
    (hp : ∀ k, (p k).Prime) (b c : Block t) : Function.Injective (vec p z b c) := by
  rintro ⟨a₁,a₂⟩ ⟨b₁,b₂⟩ h
  have hq : (modulus p b c : GaussianInt) ≠ 0 := by exact_mod_cast (modulus_pos _ hp b c).ne'
  have e := mul_left_cancel₀ hq (add_left_cancel (a := numerator p z b c) h)
  exact Prod.ext (congrArg Zsqrtd.re e) (congrArg Zsqrtd.im e)

private def normalized {t : ℕ} (p : Label t → ℕ) (u : Label t → ℤ)
    (b c : Block t) (a : ℤ) : ℚ :=
  (u (.inl b.1) : ℚ) / p (.inl b.1) + (u (.inr b.2) : ℚ) / p (.inr b.2) -
  (u (.inl c.1) : ℚ) / p (.inl c.1) - (u (.inr c.2) : ℚ) / p (.inr c.2) + a

private theorem norm_global_coord {t : ℕ} (p : Label t → ℕ) (u : Label t → ℤ)
    (hp : ∀ k, (p k).Prime) (b c : Block t) (a : ℤ) :
    (shiftedCoord p u b c a : ℚ) = (commonDen p : ℚ) * normalized p u b c a := by
  have h (k : Label t) : (cofactor p k : ℚ) * u k = (commonDen p : ℚ) * (u k / (p k : ℚ)) := by
    have hc : cofactor p k * p k = commonDen p := prod_erase_mul univ p (mem_univ k)
    have hn : (p k : ℚ) ≠ 0 := by exact_mod_cast (hp k).ne_zero
    rw [← hc, Nat.cast_mul]
    field_simp
  simp only [shiftedCoord, centerCoord_eq, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, h, normalized]
  ring

private theorem norm_pair_coord {t : ℕ} (p : Label t → ℕ) (z : Label t → GaussianInt)
    (hp : ∀ k, (p k).Prime) (b c : Block t) (a : ℤ × ℤ) :
    ((vec p z b c a).re : ℚ) = (modulus p b c : ℚ) * normalized p (fun k => (z k).re) b c a.1 ∧
    ((vec p z b c a).im : ℚ) = (modulus p b c : ℚ) * normalized p (fun k => (z k).im) b c a.2 := by
  have h := rationalOffset_numerator p z hp b c
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  have hq : (modulus p b c : ℚ) ≠ 0 := by exact_mod_cast (modulus_pos p hp b c).ne'
  simp only [Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub, rationalOffset] at hx hy
  have hx' := (div_eq_iff hq).mp hx
  have hy' := (div_eq_iff hq).mp hy
  simp only [vec, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_mul, Zsqrtd.im_mul,
    Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul, zero_add, mul_zero, add_zero,
    Int.cast_add, Int.cast_mul, Int.cast_natCast, normalized]
  constructor <;> linarith only [hx',hy']

private theorem same_norm_card {t : ℕ} (p : Label t → ℕ) (z : Label t → GaussianInt)
    (hp : ∀ k, (p k).Prime) (b c : Block t) (A : Finset (ℤ × ℤ)) :
    (A.image (shiftedNorm p (fun k => (z k).re) (fun k => (z k).im) b c)).card =
      ((A.image (vec p z b c)).image (fun v => v.norm)).card := by
  let encode (d : ℕ) (n : ℤ) : ℚ := (n : ℚ) / (d : ℚ)^2
  have hinj (d : ℕ) (hd : 0 < d) : Function.Injective (encode d) := by
    intro x y he
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have e := (div_left_inj' (pow_ne_zero 2 hd')).mp he
    exact_mod_cast e
  rw [← card_image_of_injective _ (hinj _ (commonDen_pos hp)),
    ← card_image_of_injective _ (hinj _ (modulus_pos p hp b c))]
  simp only [image_image]
  congr 1
  apply Finset.image_congr
  intro a _
  have hh := norm_pair_coord p z hp b c a
  have hQ : (commonDen p : ℚ) ≠ 0 := by exact_mod_cast (commonDen_pos hp).ne'
  have hq : (modulus p b c : ℚ) ≠ 0 := by exact_mod_cast (modulus_pos p hp b c).ne'
  simp only [Function.comp_apply, encode, shiftedNorm, Zsqrtd.norm, Int.cast_sub, Int.cast_neg, Int.cast_one,
    Int.cast_add, Int.cast_mul, Int.cast_pow, norm_global_coord p _ hp, hh.1, hh.2]
  field_simp [hQ,hq]
  <;> ring

private theorem vec_disk {t L : ℕ} (hL : 0 < L) (p : Label t → ℕ) (z : Label t → GaussianInt)
    (hp : ∀ k, (p k).Prime) (hb : BoundedOffsets p z) (b c : Block t)
    {a : ℤ × ℤ} (ha : a ∈ box L) :
    ‖(vec p z b c a : ℂ)‖ ≤ pairRadius L p b c := by
  have bound (u : Label t → ℤ) (hu : ∀ k, 0 ≤ (u k : ℚ) / p k ∧ (u k : ℚ) / p k < 1)
      (v : ℤ) (hv : v ∈ Ico (-(L : ℤ)) (L : ℤ)) :
      |normalized p u b c v| ≤ (L : ℚ) + 2 := by
    have hv' := mem_Ico.mp hv
    have hlo : -(L : ℚ) ≤ v := by exact_mod_cast hv'.1
    have hhi : (v : ℚ) < L := by exact_mod_cast hv'.2
    unfold normalized
    apply abs_le.mpr
    constructor <;> linarith [(hu (.inl b.1)).1,(hu (.inl b.1)).2,(hu (.inr b.2)).1,
      (hu (.inr b.2)).2,(hu (.inl c.1)).1,(hu (.inl c.1)).2,(hu (.inr c.2)).1,(hu (.inr c.2)).2]
  have hh := norm_pair_coord p z hp b c a
  have hq : 0 ≤ (modulus p b c : ℚ) := by positivity
  have coord (v : ℤ) (u : ℚ) (h : (v : ℚ) = (modulus p b c : ℚ)*u)
      (hu : |u| ≤ (L : ℚ) + 2) : |(v : ℝ)| ≤ (modulus p b c : ℝ) * ((L : ℝ) + 2) := by
    have h' : |(v : ℚ)| ≤ (modulus p b c : ℚ) * ((L : ℚ) + 2) := by
      rw [h, abs_mul, abs_of_nonneg hq]
      exact mul_le_mul_of_nonneg_left hu hq
    have hi : |v| ≤ (modulus p b c : ℤ) * ((L : ℤ) + 2) := by exact_mod_cast h'
    exact_mod_cast hi
  have hx := coord _ _ hh.1 (bound _ (fun k => (hb k).1) _ (mem_product.mp ha).1)
  have hy := coord _ _ hh.2 (bound _ (fun k => (hb k).2) _ (mem_product.mp ha).2)
  have hn := Complex.norm_le_abs_re_add_abs_im (vec p z b c a : ℂ)
  rw [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at hn
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold pairRadius
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (modulus p b c)) (sub_nonneg.mpr h1)]

private theorem count_high {q : ℕ} {R : ℝ} {r : GaussianResidues.Residue q}
    (A : Finset GaussianInt) (hur : IsUnit r)
    (hA : ∀ v ∈ A, ‖(v : ℂ)‖ ≤ R ∧ GaussianNorm.residue q v = r) :
    A.card - (A.image (fun v => v.norm)).card ≤ (ResidueExceptions.collisionFiber q R r).card := by
  let C := ResidueExceptions.collisionFiber q R r
  have hi : Set.InjOn (fun v : GaussianInt => v.norm) (↑(A \ C) : Set GaussianInt) := by
    intro v hv w hw he
    have hv' := mem_sdiff.mp hv
    have hw' := mem_sdiff.mp hw
    by_contra hne
    have hv0 : v ≠ 0 := by
      intro h0
      apply hne
      exact h0.trans (GaussianInt.norm_eq_zero.mp (by simpa [h0] using he.symm)).symm
    obtain ⟨hdr,hvr⟩ := hA v hv'.1
    obtain ⟨hdw,hwr⟩ := hA w hw'.1
    apply hv'.2
    apply (ResidueExceptions.mem_collisionFiber _ _ _ _).mpr
    refine ⟨(HighCollisionCover.mem_collisionVectors _ _ _).mpr
      ⟨hv0,hdr,hvr ▸ hur,w,?_,Ne.symm hne,he,hvr.trans hwr.symm⟩,hvr⟩
    simpa only [mem_gaussianDisk,dist_zero_right] using hdw
  have hcard : (A \ C).card ≤ (A.image (fun v => v.norm)).card := by
    rw [← card_image_of_injOn hi]
    exact card_le_card (image_subset_image sdiff_subset)
  have hcover : A.card ≤ (A \ C).card + C.card := card_le_card_sdiff_add_card
  change _ ≤ C.card
  omega

private theorem count_low {q : ℕ} {R : ℝ} {r : GaussianResidues.Residue q} (hR : 0 ≤ R)
    (A : Finset GaussianInt) (hA : ∀ v ∈ A, ‖(v : ℂ)‖ ≤ R ∧ GaussianNorm.residue q v = r) :
    (A.image (fun v => v.norm)).card ≤ (LowPalette.normPalette r R).card + 1 := by
  classical
  let P := (LowPalette.normPalette r R).image (fun n : ℕ => (n : ℤ))
  have hsub : A.image (fun v => v.norm) ⊆ insert 0 P := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hn
    by_cases hz : v = 0
    · simp [hz]
    · apply mem_insert_of_mem
      obtain ⟨hvr,hres⟩ := hA v hv
      refine mem_image.mpr ⟨v.norm.natAbs,?_,GaussianInt.natCast_natAbs_norm v⟩
      refine mem_image.mpr ⟨v,mem_filter.mpr ⟨?_,hres⟩,rfl⟩
      apply (GaussianMass.mem_representatives (sq_nonneg R) v).mpr
      refine ⟨hz,?_⟩
      change GaussianDivisibility.normMass v ≤ _
      rw [GaussianDivisibility.normMass_eq_sq_norm]
      exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hvr
  exact (card_le_card hsub).trans ((card_insert_le 0 P).trans (Nat.add_le_add_right card_image_le 1))
end DistanceCounts.GridNorms
end

noncomputable section
open Filter Finset DistanceCounts
open scoped Topology
namespace DistanceCounts.GridNorms

private theorem grid_estimates {s L : ℕ} (hs : 0 < s) (hL : 0 < L)
    (p : Label (2*s) → ℕ) (z : Label (2*s) → GaussianInt) {η : ℝ}
    (hp : ∀ k, (p k).Prime) (hd : Function.Injective p)
    (hb : PairModulus.BoundedOffsets p z) (hu : ∀ k, IsUnit (GaussianNorm.residue (p k) (z k)))
    (he : CoarseConditions.PaletteBounds s L p z η) (b c : Block (2*s)) :
    let M := ((box L).image (shiftedNorm p (fun k => (z k).re) (fun k => (z k).im) b c)).card
    if c ∈ high b then ((box L).card - M : ℕ) ≤ (η + 1 / (L : ℝ)) * (L : ℝ)^2
    else (M : ℝ) ≤ (η + 1 / (L : ℝ)) * (L : ℝ)^2 := by
  dsimp only
  let A := (box L).image (vec p z b c)
  let q := PairModulus.modulus p b c
  let r := CoarseConditions.pairResidue p z b c
  let R := CoarseConditions.pairRadius L p b c
  have hA : ∀ v ∈ A, ‖(v : ℂ)‖ ≤ R ∧ GaussianNorm.residue q v = r := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
    exact ⟨vec_disk hL p z hp hb b c ha, GaussianNorm.residue_add_denominator_mul _ _ (dvd_refl _) _ _⟩
  have hcard : A.card = (box L).card := card_image_of_injective _ (vec_injective p z hp b c)
  have hl : 0 < (L : ℝ) := by exact_mod_cast hL
  have hl1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsum : (η + 1 / (L : ℝ)) * (L : ℝ)^2 = η*(L : ℝ)^2 + L := by field_simp
  rw [same_norm_card p z hp, ← hcard, hsum]
  have e := he b c
  by_cases hh : c ∈ high b
  · rw [if_pos hh]
    rw [if_pos ((high_iff hs b c).mp hh)] at e
    have hc := count_high A (PairModulus.numerator_isUnit p z hp hd b c (fun k _ =>hu k)) hA
    exact (show ((A.card - (A.image (fun v => v.norm)).card : ℕ) : ℝ) ≤
      ((ResidueExceptions.collisionFiber q R r).card : ℝ) by exact_mod_cast hc).trans (by linarith only [e,hl])
  · rw [if_neg hh]
    rw [if_neg (fun h => hh ((high_iff hs b c).mpr h))] at e
    have hc := count_low (show 0 ≤ R by dsimp [R,CoarseConditions.pairRadius]; positivity) A hA
    have hc' : ((A.image (fun v => v.norm)).card : ℝ) ≤ (LowPalette.normPalette r R).card + 1 := by
      exact_mod_cast hc
    exact hc'.trans (by linarith only [e,hl1])

end DistanceCounts.GridNorms

theorem OMA.solution : OMA.R_Erdos653_erdos_653_R2.H1 := by
  intro m
  let s := m+1
  have hs : 0 < s := Nat.succ_pos _
  refine ⟨fun L => OffsetSelection.tolerance s L + 1 / (L : ℝ), ?_, ?_⟩
  · simpa only [add_zero] using (OffsetSelection.tolerance_tendsto hs).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  · filter_upwards [ThreeProjections.eventually_lifts hs, OffsetSelection.primes_injective hs,
      eventually_gt_atTop (0 : ℕ)] with L ⟨z,hb,hu,hx,hy,hxy,he⟩ hd hL
    refine ⟨OffsetSelection.primes s L,fun k => (z k).re,fun k => (z k).im,hd,
      fun k => ⟨OffsetSelection.primes_prime _ _ _,OffsetSelection.primes_inert _ _ _⟩,hx,hy,hxy,?_⟩
    exact GridNorms.grid_estimates hs hL _ z (OffsetSelection.primes_prime s L) hd hb hu he
end
