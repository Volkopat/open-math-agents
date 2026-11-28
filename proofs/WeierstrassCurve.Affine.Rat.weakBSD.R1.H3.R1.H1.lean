import OMAReductions.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1
import Mathlib

/-!
# The L-series of an elliptic curve over `ℚ` converges absolutely on `Re s > 3/2`

Step `H1` of the reduction `WeierstrassCurve.Affine.Rat.weakBSD.R1.H3.R1`: for every elliptic
curve `E` over `ℚ` and every `s` with `3/2 < Re s`, the Dirichlet series with coefficients
`WeierstrassCurve.LFunction E` is absolutely summable at `s`. The proof works for every
Weierstrass curve over every number field and is specialised in the last line.

Credit: @carterleffen

## The argument

1. *Hasse bound* (`MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted.hasse_bound`).
   For an elliptic curve over a finite field with `q` elements, `(q + 1 - N)² ≤ 4q`. This is
   Manin's elementary proof (degrees of the `x`-coordinates of `P₀ + nQ` on a quadratic twist over
   the rational function field), in odd characteristic and in characteristic two separately.
2. *Local coefficients* (`BSDResearch.local_coefficient_hasse`). At a place of good reduction
   the local polynomial `1 - a T + q T²` has reciprocal roots of absolute value `√q` by step 1;
   at a place of bad reduction the reciprocal roots are `0` or `±1`. So coefficient `m` of the
   inverse power series is at most `(m + 1) q^(m/2) ≤ (2 √q)^m` in absolute value.
3. *Residue fields* (`BSDResearch.local_card_eq_norm`). The residue field of the ring of integers
   of the completion at `v` is the residue field of `v`, so the `q` of Mathlib's local Euler
   factor is the absolute norm of `v`.
4. *Sum over the primes* (`BSDResearch.prime_norm_summable`). `∑ N(v)^(-t)` converges for
   `t > 1`, since the Dedekind zeta function has a simple pole with nonzero residue at `1`.
5. *Euler product* (`BSDResearch.eulerProduct_summable_of_hasse`). With weights
   `|f n| / n^t`, `t = Re s`, every finite sum of a Dirichlet convolution is at most the product
   of the bounds of the factors; the local factor at `v` is bounded by `1 + C N(v)^(1/2 - t)`,
   and finite products of these by `exp (C ∑ N(v)^(1/2 - t))`, finite by step 4 because
   `t - 1/2 > 1`. Each coefficient of Mathlib's `eulerProduct` is the coefficient of a finite
   product, so the same bound holds for the L-function, which is absolute summability.

## Provenance

This file is assembled by a script from three sources.

**(a) ATLAS**, https://github.com/facebookresearch/atlas-lean, commit
805f71dcbadd5ebf8f380f156391fc82ded8979a, directory
`MathlibExt/AlgebraicGeometry/EllipticCurve`, the seven modules

  ManinSequence.lean, ManinProjectiveDegree.lean, PointCount.lean, VariableChangePoint.lean,
  ManinTwist.lean, ManinTwistCharTwo.lean, HasseBound.lean

Authors, as stated in the modules: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex. They
supply step 1 and nothing else. Mathlib has no Hasse bound. The license file of that repository
opens with the sentence

  Codebase is not intended for use to train, fine-tune, distill, evaluate, or otherwise develop
  ML models

and continues with the Apache License, Version 2.0.

**(b) EllipticCurves**, by Michael Stoll and the other contributors to that repository,
https://github.com/MichaelStollBayreuth/EllipticCurves, commit
c4c72f486112ab61eca3b1a69135ec06789897f8, licensed under the Apache License, Version 2.0. Six
declarations are taken:

  EllipticCurves/MordellWeil.lean: `den_duplication_eq`, `den_duplication_eq_zero_iff`,
    `addX_self_of_Y_ne` (the duplication formula for the `x`-coordinate, used once in
    `ManinTwist`)
  EllipticCurves/Mathlib/Basic.lean: `comap_maximalIdeal_adicCompletionIntegers`
  EllipticCurves/Mathlib/AdicCompletionExtension.lean: `exists_valued_sub_lt_one`,
    `residueFieldEquivAdicCompletionIntegers` (step 3)

**(c) A local library on the Birch and Swinnerton-Dyer conjecture** by @carterleffen (not
published; namespace `BSDResearch`), modules `BSD/IdealNorms.lean` (steps 3 and 4),
`BSD/HasseEuler.lean` (step 2) and `BSD/AbsoluteConvergence.lean` (step 5).

Written for this file: the statement and three-line proof of `OMA.solution`.

## Changes made to the sources

All changes are made by the assembling script. No kept declaration changes its statement.

* Each source module becomes one block between `begin` / `end` marker comments, in dependency
  order, wrapped in a `section`, so that `open`, `variable` and `universe` lines stay inside
  their block.
* The module-system lines are dropped: `module`, the imports, `@[expose] public section`, and
  the modifier `public` of `hasse_bound`. Private declarations stay private.
* The seven ATLAS modules are otherwise whole, as they stand in the local library. Its copies of
  `ManinTwist` and `ManinTwistCharTwo` differ from the cited commit in one name: four
  occurrences of `FiniteField.expand_card`, the name of that lemma in the pinned Mathlib. The
  one-line comment recording this in the local copies is dropped.
* From the three EllipticCurves modules only the six declarations above are kept, each with its
  docstring, under the `namespace`, `open` and `variable` lines they need.
* From the local library: `local_polynomial_coefficient_hasse` (end of `HasseEuler`) and
  `elliptic_abscissa_le`, `elliptic_LSeries_tendsto_one` (end of `AbsoluteConvergence`) are
  not used and are left out; with the last two goes the dependency on `BSD/EulerSeries.lean`.
* The module docstrings of the source modules become plain comments, so that this is the
  only module docstring of the file.
* No proof is edited.

The portions of this file taken from ATLAS and from EllipticCurves are licensed under the Apache
License, Version 2.0 (the "License"); you may not use them except in compliance with the License.
You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0. Unless
required by applicable law or agreed to in writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied. See the License for the specific language governing permissions and limitations under the
License.
-/

/- ===== begin EllipticCurves/MordellWeil.lean (EllipticCurves @ c4c72f486112), three lemmas ===== -/
section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

lemma den_duplication_eq {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have Heq := (W'.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * Heq

lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R} (h : W'.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔ y = W'.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff, negY]
  grind only

variable {F : Type*} [Field F] {W : Affine F} [DecidableEq F]

lemma addX_self_of_Y_ne {x y : F} (h : W.Equation x y) (hn : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (h : a ≠ 0) : a ^ 2 * (b * (c / a)) = a * b * c := by field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', addX, sub_sub, sub_sub, mul_sub, mul_add]
  simp only [slope, ↓reduceIte, hn]
  rw [negY, show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring, div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.equation_iff x y).mp h

end WeierstrassCurve.Affine

end
/- ===== end EllipticCurves/MordellWeil.lean ===== -/

/- ===== begin MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean (atlas-lean @ 805f71dcbadd) ===== -/
section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

/-
# Integer sequences in Manin's proof

This file contains the elementary arithmetic at the end of Manin's proof of the Hasse bound.
-/

namespace Int

/-- A two-sided integer sequence with constant second difference two is the expected monic
quadratic once its values at `0` and `-1` are known. -/
theorem eq_quadratic_of_recurrence (d : ℤ → ℤ) (q N : ℤ)
    (hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2)
    (hzero : d 0 = q) (hnegOne : d (-1) = N) (n : ℤ) :
    d n = n ^ 2 + (q + 1 - N) * n + q := by
  let p : ℤ → ℤ := fun m ↦ m ^ 2 + (q + 1 - N) * m + q
  have hp (m : ℤ) : p (m - 1) + p (m + 1) = 2 * p m + 2 := by
    simp only [p]
    ring
  have hpzero : p 0 = q := by
    simp [p]
  have hpnegOne : p (-1) = N := by
    simp [p]
    ring
  have hpair : ∀ m : ℤ, d m = p m ∧ d (m - 1) = p (m - 1) := by
    intro m
    refine Int.inductionOn' m 0 ?_ ?_ ?_
    · exact ⟨hzero.trans hpzero.symm, by simpa using hnegOne.trans hpnegOne.symm⟩
    · intro k _ hk
      refine ⟨?_, ?_⟩
      · linarith [hrec k, hp k]
      · simpa only [add_sub_cancel_right] using hk.1
    · intro k _ hk
      refine ⟨hk.2, ?_⟩
      have hd := hrec (k - 1)
      have hpd := hp (k - 1)
      rw [show k - 1 + 1 = k by ring] at hd hpd
      linarith
  exact (hpair n).1

/-- An integral monic quadratic that is nonnegative at every integer and does not vanish at two
consecutive integers has nonpositive discriminant. -/
theorem sq_le_four_mul_of_quadratic_nonnegative {a q : ℤ}
    (hnonneg : ∀ n : ℤ, 0 ≤ n ^ 2 + a * n + q)
    (hnotTwoZeros : ∀ n : ℤ,
      n ^ 2 + a * n + q = 0 → (n + 1) ^ 2 + a * (n + 1) + q = 0 → False) :
    a ^ 2 ≤ 4 * q := by
  by_contra hle
  have hbad : 4 * q < a ^ 2 := lt_of_not_ge hle
  rcases Int.even_or_odd a with ha | ha
  · obtain ⟨k, hk⟩ := ha
    have h := hnonneg (-k)
    rw [hk] at hbad h
    nlinarith
  · obtain ⟨k, hk⟩ := ha
    have hleft := hnonneg (-k - 1)
    have hright := hnonneg (-k)
    have hzleft : (-k - 1) ^ 2 + a * (-k - 1) + q = 0 := by
      rw [hk] at hbad hleft hright ⊢
      nlinarith
    have hzright : (-k) ^ 2 + a * (-k) + q = 0 := by
      rw [hk] at hbad hleft hright ⊢
      nlinarith
    apply hnotTwoZeros (-k - 1) hzleft
    convert hzright using 1
    ring

end Int

namespace MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The four properties of the polynomial-degree sequence used in Manin's proof. -/
structure ManinDegreeData (q N : ℕ) where
  /-- The numerator degree attached to the point indexed by an integer. -/
  d : ℤ → ℕ
  /-- Frobenius has degree `q`. -/
  zero : d 0 = q
  /-- Frobenius minus the identity has degree equal to the rational point count. -/
  negOne : d (-1) = N
  /-- The degree sequence has constant second difference two. -/
  recurrence : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2
  /-- Consecutive points in the sequence cannot both have degree zero. -/
  noAdjacentZeros : ∀ n, d n = 0 → d (n + 1) = 0 → False

namespace ManinDegreeData

/-- Build Manin degree data from its nonnegative quadratic formula, provided consecutive integer
values do not both vanish. -/
def ofQuadratic (q N : ℕ) (a : ℤ) (ha : a = (q : ℤ) + 1 - (N : ℤ))
    (hnonneg : ∀ n, 0 ≤ n ^ 2 + a * n + q)
    (hnoAdjacent : ∀ n, n ^ 2 + a * n + q = 0 →
      (n + 1) ^ 2 + a * (n + 1) + q = 0 → False) : ManinDegreeData q N where
  d n := (n ^ 2 + a * n + q).toNat
  zero := by simp
  negOne := by
    have h := hnonneg (-1)
    apply Int.ofNat_injective
    change (((-1 : ℤ) ^ 2 + a * (-1) + q).toNat : ℤ) = (N : ℤ)
    rw [Int.toNat_of_nonneg h]
    simp [ha]
    ring
  recurrence n := by
    have hm := hnonneg (n - 1)
    have hn := hnonneg n
    have hp := hnonneg (n + 1)
    apply Int.ofNat_injective
    change ((((n - 1) ^ 2 + a * (n - 1) + q).toNat : ℕ) : ℤ) +
        (((n + 1) ^ 2 + a * (n + 1) + q).toNat : ℕ) =
      2 * (((n ^ 2 + a * n + q).toNat : ℕ) : ℤ) + 2
    rw [Int.toNat_of_nonneg hm, Int.toNat_of_nonneg hn, Int.toNat_of_nonneg hp]
    ring
  noAdjacentZeros n hn hn1 := by
    apply hnoAdjacent n
    · exact le_antisymm (Int.toNat_eq_zero.mp hn) (hnonneg n)
    · exact le_antisymm (Int.toNat_eq_zero.mp hn1) (hnonneg (n + 1))

/-- Manin degree data implies the integral squared form of the Hasse bound. -/
theorem hasse_bound {q N : ℕ} (data : ManinDegreeData q N) :
    (((q : ℤ) + 1 - (N : ℤ)) ^ 2 ≤ 4 * (q : ℤ)) := by
  let dInt : ℤ → ℤ := fun n ↦ data.d n
  have hrec : ∀ n, dInt (n - 1) + dInt (n + 1) = 2 * dInt n + 2 := by
    intro n
    dsimp only [dInt]
    exact_mod_cast data.recurrence n
  have hzero : dInt 0 = q := by
    dsimp only [dInt]
    exact_mod_cast data.zero
  have hnegOne : dInt (-1) = N := by
    dsimp only [dInt]
    exact_mod_cast data.negOne
  have hquadratic (n : ℤ) :
      dInt n = n ^ 2 + ((q : ℤ) + 1 - (N : ℤ)) * n + q :=
    Int.eq_quadratic_of_recurrence dInt q N hrec hzero hnegOne n
  apply Int.sq_le_four_mul_of_quadratic_nonnegative
  · intro n
    rw [← hquadratic]
    exact Int.natCast_nonneg _
  · intro n hn hn1
    apply data.noAdjacentZeros n
    · apply Int.ofNat_injective
      simpa [dInt, hquadratic n] using hn
    · apply Int.ofNat_injective
      simpa [dInt, hquadratic (n + 1)] using hn1

end ManinDegreeData

end MathlibExt.AlgebraicGeometry.EllipticCurve

end
/- ===== end MathlibExt/AlgebraicGeometry/EllipticCurve/ManinSequence.lean ===== -/

/- ===== begin MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean (atlas-lean @ 805f71dcbadd) ===== -/
section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

/-
# Projective numerator degrees for Manin's proof

This file isolates the characteristic-free commutative algebra used to recover the numerator
degrees of two rational functions from primitive projective product and sum coordinates.
-/

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

noncomputable section

open Polynomial

universe u

variable {K : Type u} [Field K]

private local instance : DecidableEq K := Classical.decEq K
private local instance : DecidableEq K[X] := Classical.decEq K[X]

/-- Three homogeneous coordinates are primitive when they generate the unit ideal. -/
def PrimitiveTriple (a b c : K[X]) : Prop :=
  ∃ u v w : K[X], u * a + v * b + w * c = 1

private lemma common_dvd_isUnit_of_isCoprime {p a b : K[X]}
    (hab : IsCoprime a b) (hpa : p ∣ a) (hpb : p ∣ b) : IsUnit p := by
  rcases hpa with ⟨a', ha⟩
  rcases hpb with ⟨b', hb⟩
  rcases hab with ⟨u, v, huv⟩
  refine isUnit_iff_exists_inv.mpr ⟨u * a' + v * b', ?_⟩
  calc
    p * (u * a' + v * b') = u * (p * a') + v * (p * b') := by ring
    _ = 1 := by rw [← ha, ← hb, huv]

private lemma gcd_three_isUnit_of_no_common_irreducible {a b c : K[X]}
    (hc : c ≠ 0)
    (h : ∀ p : K[X], Irreducible p → p ∣ a → p ∣ b → p ∣ c → False) :
    IsUnit (EuclideanDomain.gcd a (EuclideanDomain.gcd b c)) := by
  by_contra hunit
  have hg0 : EuclideanDomain.gcd a (EuclideanDomain.gcd b c) ≠ 0 := by
    simp only [ne_eq, EuclideanDomain.gcd_eq_zero_iff]
    tauto
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor hunit hg0
  apply h p hp
  · exact hpg.trans (EuclideanDomain.gcd_dvd_left _ _)
  · exact hpg.trans ((EuclideanDomain.gcd_dvd_right _ _).trans
      (EuclideanDomain.gcd_dvd_left _ _))
  · exact hpg.trans ((EuclideanDomain.gcd_dvd_right _ _).trans
      (EuclideanDomain.gcd_dvd_right _ _))

/-- Three polynomials are primitive if no irreducible polynomial divides all three. -/
theorem primitiveTriple_of_no_common_irreducible {a b c : K[X]}
    (hc : c ≠ 0)
    (h : ∀ p : K[X], Irreducible p → p ∣ a → p ∣ b → p ∣ c → False) :
    PrimitiveTriple a b c := by
  have hgcd := gcd_three_isUnit_of_no_common_irreducible hc h
  rcases isUnit_iff_exists_inv.mp hgcd with ⟨z, hz⟩
  refine ⟨EuclideanDomain.gcdA a (EuclideanDomain.gcd b c) * z,
    EuclideanDomain.gcdA b c *
      EuclideanDomain.gcdB a (EuclideanDomain.gcd b c) * z,
    EuclideanDomain.gcdB b c *
      EuclideanDomain.gcdB a (EuclideanDomain.gcd b c) * z, ?_⟩
  rw [← hz]
  rw [EuclideanDomain.gcd_eq_gcd_ab a (EuclideanDomain.gcd b c),
    EuclideanDomain.gcd_eq_gcd_ab b c]
  ring

private lemma primitiveTriple_linearCombination {a b c : K[X]}
    (h : PrimitiveTriple a b c) :
    ∃ u v w : K[X], u * a + v * b + w * c = 1 := by
  exact h

private lemma dvd_of_primitiveTriple {a b c p x : K[X]}
    (h : PrimitiveTriple a b c)
    (ha : p ∣ x * a) (hb : p ∣ x * b) (hc : p ∣ x * c) : p ∣ x := by
  obtain ⟨u, v, w, huv⟩ := primitiveTriple_linearCombination h
  have hdvd : p ∣ u * (x * a) + v * (x * b) + w * (x * c) :=
    ((ha.mul_left u).add (hb.mul_left v)).add (hc.mul_left w)
  have heq : u * (x * a) + v * (x * b) + w * (x * c) = x := by
    calc
      u * (x * a) + v * (x * b) + w * (x * c) =
          x * (u * a + v * b + w * c) := by ring
      _ = x := by rw [huv, mul_one]
  rwa [heq] at hdvd

private lemma primitive_numeratorTriple {a b c d : K[X]}
    (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hb : b ≠ 0) (hd : d ≠ 0) :
    PrimitiveTriple (a * c) (a * d + b * c) (b * d) := by
  apply primitiveTriple_of_no_common_irreducible (mul_ne_zero hb hd)
  intro p hp hpac hpsum hpbd
  have hprime := hp.prime
  rcases hprime.dvd_mul.mp hpac with hpa | hpc
  · rcases hprime.dvd_mul.mp hpbd with hpb | hpd
    · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
    · have hpad : p ∣ a * d := hpa.mul_right d
      have hpbc : p ∣ b * c := by
        have hdvd := hpsum.sub hpad
        have heq : (a * d + b * c) - a * d = b * c := by ring
        rwa [heq] at hdvd
      rcases hprime.dvd_mul.mp hpbc with hpb | hpc
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)
  · rcases hprime.dvd_mul.mp hpbd with hpb | hpd
    · have hpbc : p ∣ b * c := hpb.mul_right c
      have hpad : p ∣ a * d := by
        have hdvd := hpsum.sub hpbc
        have heq : (a * d + b * c) - b * c = a * d := by ring
        rwa [heq] at hdvd
      rcases hprime.dvd_mul.mp hpad with hpa | hpd
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)
    · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)

private lemma ratFunc_num_denom_mul (x y : RatFunc K) :
    algebraMap K[X] (RatFunc K) (x.num * y.num) /
        algebraMap K[X] (RatFunc K) (x.denom * y.denom) = x * y := by
  rw [map_mul, map_mul, ← div_mul_div_comm]
  rw [RatFunc.num_div_denom, RatFunc.num_div_denom]

private lemma ratFunc_num_denom_add (x y : RatFunc K) :
    algebraMap K[X] (RatFunc K)
          (x.num * y.denom + x.denom * y.num) /
        algebraMap K[X] (RatFunc K) (x.denom * y.denom) = x + y := by
  rw [map_add, map_mul, map_mul, map_mul]
  calc
    _ = algebraMap K[X] (RatFunc K) x.num /
          algebraMap K[X] (RatFunc K) x.denom +
        algebraMap K[X] (RatFunc K) y.num /
          algebraMap K[X] (RatFunc K) y.denom := by
      field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x),
        RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero y)]
    _ = x + y := by
      rw [RatFunc.num_div_denom, RatFunc.num_div_denom]

/-- A primitive projective presentation of the product and sum of two nonzero rational
functions has first-coordinate degree equal to the sum of their numerator degrees. -/
theorem projective_first_natDegree {u v h : K[X]}
    (hprimitive : PrimitiveTriple u v h)
    (hh : h ≠ 0) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hprod : algebraMap K[X] (RatFunc K) u /
      algebraMap K[X] (RatFunc K) h = x * y)
    (hsum : algebraMap K[X] (RatFunc K) v /
      algebraMap K[X] (RatFunc K) h = x + y) :
    u.natDegree = x.num.natDegree + y.num.natDegree := by
  let a := x.num
  let b := x.denom
  let c := y.num
  let d := y.denom
  have ha : a ≠ 0 := RatFunc.num_ne_zero hx
  have hb : b ≠ 0 := RatFunc.denom_ne_zero x
  have hc : c ≠ 0 := RatFunc.num_ne_zero hy
  have hd : d ≠ 0 := RatFunc.denom_ne_zero y
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  have hfractionProd :
      algebraMap K[X] (RatFunc K) (a * c) /
          algebraMap K[X] (RatFunc K) (b * d) =
        algebraMap K[X] (RatFunc K) u /
          algebraMap K[X] (RatFunc K) h := by
    rw [ratFunc_num_denom_mul]
    exact hprod.symm
  have hfractionSum :
      algebraMap K[X] (RatFunc K) (a * d + b * c) /
          algebraMap K[X] (RatFunc K) (b * d) =
        algebraMap K[X] (RatFunc K) v /
          algebraMap K[X] (RatFunc K) h := by
    rw [ratFunc_num_denom_add]
    exact hsum.symm
  have hcross0 : (a * c) * h = u * (b * d) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul] using
      (div_eq_div_iff (RatFunc.algebraMap_ne_zero hbd)
        (RatFunc.algebraMap_ne_zero hh)).mp hfractionProd
  have hcross1 : (a * d + b * c) * h = v * (b * d) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul] using
      (div_eq_div_iff (RatFunc.algebraMap_ne_zero hbd)
        (RatFunc.algebraMap_ne_zero hh)).mp hfractionSum
  have hnumPrimitive :
      PrimitiveTriple (a * c) (a * d + b * c) (b * d) :=
    primitive_numeratorTriple (RatFunc.isCoprime_num_denom x)
      (RatFunc.isCoprime_num_denom y) hb hd
  have hh_dvd_bd : h ∣ b * d := by
    apply dvd_of_primitiveTriple hprimitive
    · refine ⟨a * c, ?_⟩
      calc
        (b * d) * u = u * (b * d) := by ring
        _ = (a * c) * h := hcross0.symm
        _ = h * (a * c) := by ring
    · refine ⟨a * d + b * c, ?_⟩
      calc
        (b * d) * v = v * (b * d) := by ring
        _ = (a * d + b * c) * h := hcross1.symm
        _ = h * (a * d + b * c) := by ring
    · exact ⟨b * d, by ring⟩
  have hbd_dvd_h : b * d ∣ h := by
    apply dvd_of_primitiveTriple hnumPrimitive
    · refine ⟨u, ?_⟩
      calc
        h * (a * c) = (a * c) * h := by ring
        _ = u * (b * d) := hcross0
        _ = (b * d) * u := by ring
    · refine ⟨v, ?_⟩
      calc
        h * (a * d + b * c) = (a * d + b * c) * h := by ring
        _ = v * (b * d) := hcross1
        _ = (b * d) * v := by ring
    · exact ⟨h, by ring⟩
  have hdegreeH : h.natDegree = (b * d).natDegree := by
    have hdegree := Polynomial.degree_eq_degree_of_associated
      (associated_of_dvd_dvd hh_dvd_bd hbd_dvd_h)
    rw [degree_eq_natDegree hh, degree_eq_natDegree hbd] at hdegree
    exact WithBot.coe_eq_coe.mp hdegree
  have hu : u ≠ 0 := by
    intro hu
    rw [hu, zero_mul] at hcross0
    exact mul_ne_zero (mul_ne_zero ha hc) hh hcross0
  have hdegreeCross := congrArg Polynomial.natDegree hcross0
  rw [Polynomial.natDegree_mul (mul_ne_zero ha hc) hh,
    Polynomial.natDegree_mul hu hbd,
    Polynomial.natDegree_mul ha hc,
    Polynomial.natDegree_mul hb hd] at hdegreeCross
  rw [Polynomial.natDegree_mul hb hd] at hdegreeH
  dsimp only [a, b, c, d] at hdegreeCross hdegreeH ⊢
  omega

end

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

end
/- ===== end MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean ===== -/

/- ===== begin MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean (atlas-lean @ 805f71dcbadd) ===== -/
section

/-
# Point counts of elliptic curves over finite fields

This file defines the Frobenius trace of an elliptic curve over a finite field through its rational
point count. It also supplies a finiteness instance for the canonical affine point type.
-/

open Polynomial

namespace WeierstrassCurve.Affine

universe u

variable {R : Type u} [CommRing R] (W : Affine R)

namespace Point

/-- The nonsingular points of a Weierstrass curve over a finite commutative ring form a finite
type. The point at infinity is included. -/
instance instFinitePoint [Finite R] : Finite W.Point := by
  let _ : Finite (WithZero {xy : R × R // W.Nonsingular xy.1 xy.2}) :=
    inferInstanceAs (Finite (Option {xy : R × R // W.Nonsingular xy.1 xy.2}))
  exact Finite.of_injective W.nonsingularPointEquiv W.nonsingularPointEquiv.injective

end Point

variable {F : Type u} [Field F]

/-- The Frobenius trace of an elliptic curve over a finite field, defined by
`a_q(E) = q + 1 - #E(𝔽_q)`. The point at infinity belongs to `W.Point`. -/
noncomputable def frobeniusTrace (W : Affine F) [Finite F] : ℤ :=
  (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ)

variable (W : Affine F)

theorem frobeniusTrace_eq [Finite F] :
    W.frobeniusTrace = (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ) :=
  rfl

/-- The rational-point count is one plus the number of affine solutions to the Weierstrass
equation; the extra point is the point at infinity. -/
theorem natCard_point_eq_natCard_affineSolutions_add_one [Finite F] [W.IsElliptic] :
    Nat.card W.Point = Nat.card {xy : F × F // W.Equation xy.1 xy.2} + 1 := by
  calc
    Nat.card W.Point =
        Nat.card (WithZero {xy : F × F // W.Equation xy.1 xy.2}) :=
      Nat.card_congr W.pointEquiv
    _ = Nat.card {xy : F × F // W.Equation xy.1 xy.2} + 1 := by
      change Nat.card (Option {xy : F × F // W.Equation xy.1 xy.2}) = _
      exact Finite.card_option

private noncomputable def equationPolynomial (x : F) : F[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

private lemma equationPolynomial_ne_zero (x : F) : equationPolynomial W x ≠ 0 := by
  apply Polynomial.Monic.ne_zero
  unfold equationPolynomial
  monicity <;> norm_num

private lemma equationPolynomial_natDegree (x : F) :
    (equationPolynomial W x).natDegree = 2 := by
  unfold equationPolynomial
  compute_degree <;> norm_num

private lemma equation_iff_eval_equationPolynomial (x y : F) :
    W.Equation x y ↔ (equationPolynomial W x).eval y = 0 := by
  rw [equation_iff]
  simp only [equationPolynomial, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  constructor <;> intro h <;> linear_combination h

private lemma equationFiber_natCard_le_two [Finite F] (x : F) :
    Nat.card {y : F // W.Equation x y} ≤ 2 := by
  rw [show Nat.card {y : F // W.Equation x y} =
      Set.ncard {y : F | W.Equation x y} from rfl]
  rw [show {y : F | W.Equation x y} = (equationPolynomial W x).rootSet F by
    ext y
    rw [Polynomial.mem_rootSet, and_iff_right (equationPolynomial_ne_zero W x)]
    simpa [aeval_def] using equation_iff_eval_equationPolynomial W x y]
  calc
    ((equationPolynomial W x).rootSet F).ncard ≤
        (equationPolynomial W x).natDegree :=
      Polynomial.ncard_rootSet_le _ _
    _ = 2 := equationPolynomial_natDegree W x

private def affineSolutionsEquivSigma :
    {xy : F × F // W.Equation xy.1 xy.2} ≃ Σ x : F, {y : F // W.Equation x y} where
  toFun xy := ⟨xy.1.1, xy.1.2, xy.2⟩
  invFun xy := ⟨(xy.1, xy.2.1), xy.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A Weierstrass equation over a finite field has at most two affine points over each
`x`-coordinate, plus the point at infinity. -/
theorem natCard_point_le_two_mul_natCard_add_one [Finite F] :
    Nat.card W.Point ≤ 2 * Nat.card F + 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  let encode : W.Point → Option {xy : F × F // W.Equation xy.1 xy.2}
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  have hinj : Function.Injective encode := by
    intro P Q h
    cases P <;> cases Q <;> simp_all [encode]
  calc
    Nat.card W.Point ≤ Nat.card (Option {xy : F × F // W.Equation xy.1 xy.2}) :=
      Nat.card_le_card_of_injective encode hinj
    _ = Nat.card {xy : F × F // W.Equation xy.1 xy.2} + 1 :=
      Finite.card_option
    _ =
        (∑ x : F, Nat.card {y : F // W.Equation x y}) + 1 := by
      rw [Nat.card_congr (affineSolutionsEquivSigma W), Nat.card_sigma]
    _ ≤ (∑ _x : F, 2) + 1 := by
      gcongr with x
      exact equationFiber_natCard_le_two W x
    _ = 2 * Nat.card F + 1 := by simp [Nat.card_eq_fintype_card, mul_comm]

/-- The point-count formula rearranged as `#E(𝔽_q) = q + 1 - a_q(E)`. -/
theorem natCard_point_eq_natCard_add_one_sub_frobeniusTrace [Finite F] :
    (Nat.card W.Point : ℤ) = (Nat.card F : ℤ) + 1 - W.frobeniusTrace := by
  rw [frobeniusTrace]
  ring

/-- The point count and Frobenius trace sum to `q + 1`. -/
theorem natCard_point_add_frobeniusTrace_eq [Finite F] :
    (Nat.card W.Point : ℤ) + W.frobeniusTrace = (Nat.card F : ℤ) + 1 := by
  rw [frobeniusTrace]
  ring

end WeierstrassCurve.Affine

end
/- ===== end MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean ===== -/

/- ===== begin MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean (atlas-lean @ 805f71dcbadd) ===== -/
section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

/-
# Variable changes on affine Weierstrass points

This file transports affine solutions and rational points along an admissible variable change.
-/

namespace WeierstrassCurve.VariableChange

universe u

variable {F : Type u} [Field F]

/-- The affine-coordinate map associated to an admissible Weierstrass variable change. -/
def mapAffineCoordinates (C : VariableChange F) (xy : F × F) : F × F :=
  (C.u ^ 2 * xy.1 + C.r,
    C.u ^ 3 * xy.2 + C.u ^ 2 * C.s * xy.1 + C.t)

@[simp]
theorem mapAffineCoordinates_one (xy : F × F) :
    mapAffineCoordinates (1 : VariableChange F) xy = xy := by
  ext <;> simp [mapAffineCoordinates, one_def]

theorem mapAffineCoordinates_mul (C C' : VariableChange F) (xy : F × F) :
    mapAffineCoordinates (C * C') xy =
      mapAffineCoordinates C' (mapAffineCoordinates C xy) := by
  ext <;> simp only [mapAffineCoordinates, mul_def, Units.val_mul]
  · ring
  · ring

@[simp]
theorem mapAffineCoordinates_inv_apply (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C⁻¹ (mapAffineCoordinates C xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

@[simp]
theorem mapAffineCoordinates_apply_inv (C : VariableChange F) (xy : F × F) :
    mapAffineCoordinates C (mapAffineCoordinates C⁻¹ xy) = xy := by
  rw [← mapAffineCoordinates_mul]
  simp

/-- Affine coordinates form an equivalence under an admissible Weierstrass variable change. -/
def affineCoordinatesEquiv (C : VariableChange F) : F × F ≃ F × F where
  toFun := mapAffineCoordinates C
  invFun := mapAffineCoordinates C⁻¹
  left_inv := mapAffineCoordinates_inv_apply C
  right_inv := mapAffineCoordinates_apply_inv C

/-- The affine-coordinate map carries the changed Weierstrass equation to the original one. -/
theorem equation_mapAffineCoordinates_iff (C : VariableChange F) (W : WeierstrassCurve F)
    (xy : F × F) :
    (C • W).toAffine.Equation xy.1 xy.2 ↔
      W.toAffine.Equation (mapAffineCoordinates C xy).1
        (mapAffineCoordinates C xy).2 := by
  rcases xy with ⟨x, y⟩
  change (C • W).toAffine.Equation x y ↔
    W.toAffine.Equation
      (C.u ^ 2 * x + C.r)
      (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
  rw [(C • W).toAffine.equation_iff_variableChange,
    W.toAffine.equation_iff_variableChange]
  rw [← mul_smul]
  simp only [Affine.equation_zero, variableChange_a₆]
  simp only [mul_def, one_mul, mul_zero, zero_add, Units.val_inv_eq_inv_val,
    inv_pow, mul_eq_zero, inv_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff, Units.ne_zero, false_or, inv_one,
    Units.val_one, one_pow]
  constructor <;> intro h <;> ring_nf at h ⊢ <;> exact h

/-- Affine solutions of Weierstrass equations are equivalent under a variable change. -/
def affineEquationEquiv (C : VariableChange F) (W : WeierstrassCurve F) :
    {xy : F × F // (C • W).toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // W.toAffine.Equation xy.1 xy.2} where
  toFun xy :=
    ⟨mapAffineCoordinates C xy.1,
      (equation_mapAffineCoordinates_iff C W xy.1).mp xy.2⟩
  invFun xy :=
    ⟨mapAffineCoordinates C⁻¹ xy.1, by
      rw [equation_mapAffineCoordinates_iff]
      simpa using xy.2⟩
  left_inv xy := by
    apply Subtype.ext
    exact mapAffineCoordinates_inv_apply C xy.1
  right_inv xy := by
    apply Subtype.ext
    exact mapAffineCoordinates_apply_inv C xy.1

/-- Rational points of elliptic Weierstrass equations are equivalent under a variable change. -/
noncomputable def pointEquiv (C : VariableChange F) (W : WeierstrassCurve F)
    [W.IsElliptic] :
    (C • W).toAffine.Point ≃ W.toAffine.Point :=
  (C • W).toAffine.pointEquiv |>.trans
    ((affineEquationEquiv C W).optionCongr.trans W.toAffine.pointEquiv.symm)

/-- An admissible variable change preserves the number of rational points of an elliptic
Weierstrass equation over a finite field. -/
theorem natCard_point_eq [Finite F] (C : VariableChange F) (W : WeierstrassCurve F)
    [W.IsElliptic] :
    Nat.card ((C • W).toAffine.Point) = Nat.card W.toAffine.Point :=
  Nat.card_congr (pointEquiv C W)

end WeierstrassCurve.VariableChange

end
/- ===== end MathlibExt/AlgebraicGeometry/EllipticCurve/VariableChangePoint.lean ===== -/

/- ===== begin MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean (atlas-lean @ 805f71dcbadd) ===== -/
section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

/-
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/

open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

private def cubic (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

private lemma cubic_ne_zero (W : WeierstrassCurve F) : cubic W ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : F[X] ↦ p.coeff 3) h
  simp [cubic] at hcoeff

private lemma cubic_monic (W : WeierstrassCurve F) : (cubic W).Monic := by
  unfold cubic
  monicity <;> norm_num

private lemma cubic_natDegree (W : WeierstrassCurve F) : (cubic W).natDegree = 3 := by
  unfold cubic
  compute_degree <;> norm_num

private lemma cubic_degree (W : WeierstrassCurve F) : (cubic W).degree = 3 := by
  rw [degree_eq_natDegree (cubic_ne_zero W), cubic_natDegree]
  norm_num

private lemma cubic_discr (W : WeierstrassCurve F) :
    (cubic W).discr =
      W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ -
        27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three (cubic_degree W)]
  norm_num [cubic]

private def duplicationNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 - C (2 * W.a₄) * X ^ 2 - C (8 * W.a₆) * X +
    C (W.a₄ ^ 2 - 4 * W.a₂ * W.a₆)

private lemma duplicationNumerator_eq (W : WeierstrassCurve F) :
    duplicationNumerator W =
      (cubic W).derivative ^ 2 -
        C 4 * (C W.a₂ + C 2 * X) * cubic W := by
  simp only [duplicationNumerator, cubic, derivative_add, derivative_pow,
    derivative_X, derivative_C, derivative_mul, map_ofNat]
  simp only [C_eq_natCast, C_ofNat, map_mul, map_sub, map_pow]
  ring

private lemma delta_eq_sixteen_mul_cubic_discr
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    W.Δ = 16 * (cubic W).discr := by
  rw [WeierstrassCurve.Δ_of_isCharNeTwoNF, cubic_discr]
  ring

private lemma cubic_discr_ne_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : (cubic W).discr ≠ 0 := by
  intro h
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  apply hΔ
  rw [delta_eq_sixteen_mul_cubic_discr, h, mul_zero]

private lemma cubic_separable (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : (cubic W).Separable := by
  rw [Polynomial.separable_def]
  have hdegDeriv : (cubic W).derivative.natDegree ≤ 2 := by
    simpa [cubic_natDegree] using Polynomial.natDegree_derivative_le (cubic W)
  have hres :
      Polynomial.resultant (cubic W) (cubic W).derivative 3 2 =
        -(cubic W).discr := by
    have h := Polynomial.resultant_deriv (f := cubic W) (by
      rw [cubic_degree]
      norm_num)
    rw [cubic_natDegree] at h
    norm_num [cubic_monic W] at h
    exact h
  have hresne :
      Polynomial.resultant (cubic W) (cubic W).derivative 3 2 ≠ 0 := by
    rw [hres]
    exact neg_ne_zero.mpr (cubic_discr_ne_zero W)
  obtain ⟨p, q, _, _, hpq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (cubic W) (cubic W).derivative (m := 3) (n := 2)
        (cubic_natDegree W).le hdegDeriv (by omega)
  refine ⟨C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * p,
    C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * q, ?_⟩
  calc
    (C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * p) *
          cubic W +
        (C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ * q) *
          (cubic W).derivative =
        C (Polynomial.resultant (cubic W) (cubic W).derivative 3 2)⁻¹ *
          (cubic W * p + (cubic W).derivative * q) := by ring
    _ = 1 := by rw [hpq, ← map_mul, inv_mul_cancel₀ hresne, map_one]

private lemma isCoprime_cubic_duplicationNumerator
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    IsCoprime (cubic W) (duplicationNumerator W) := by
  have hc : IsCoprime (cubic W) ((cubic W).derivative ^ 2) :=
    ((Polynomial.separable_def (cubic W)).mp (cubic_separable W)).pow_right
  obtain ⟨u, v, huv⟩ := hc
  let k : F[X] := C 4 * (C W.a₂ + C 2 * X)
  refine ⟨u + v * k, v, ?_⟩
  rw [duplicationNumerator_eq]
  change (u + v * k) * cubic W +
    v * ((cubic W).derivative ^ 2 - k * cubic W) = 1
  calc
    (u + v * k) * cubic W +
        v * ((cubic W).derivative ^ 2 - k * cubic W) =
      u * cubic W + v * (cubic W).derivative ^ 2 := by ring
    _ = 1 := huv

private lemma product_formula {R : Type*} [CommRing R]
    (a b c t f g : R) :
    let cubicAtT := t ^ 3 + a * t ^ 2 + b * t + c
    let common :=
      (t * g + f) * (b * g + t * f) + 2 * g * (a * t * f + c * g)
    common ^ 2 -
        4 * cubicAtT * g * (f ^ 3 + a * f ^ 2 * g + b * f * g ^ 2 + c * g ^ 3) =
      (t * g - f) ^ 2 *
        ((t * f - b * g) ^ 2 - 4 * c * g * ((t + a) * g + f)) := by
  dsimp only
  ring

private def cubicRat (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (cubic W)

private lemma cubicRat_ne_zero (W : WeierstrassCurve F) : cubicRat W ≠ 0 := by
  exact RatFunc.algebraMap_ne_zero (cubic_ne_zero W)

private lemma cubicRat_eq (W : WeierstrassCurve F) :
    cubicRat W = RatFunc.X ^ 3 + RatFunc.C W.a₂ * RatFunc.X ^ 2 +
      RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆ := by
  simp [cubicRat, cubic, RatFunc.algebraMap_X]

private lemma intDegree_cubicRat (W : WeierstrassCurve F) :
    (cubicRat W).intDegree = 3 := by
  rw [cubicRat, RatFunc.intDegree_polynomial, cubic_natDegree]
  norm_num

private lemma intDegree_pow {x : RatFunc F} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

private lemma intDegree_add_le_of_le {x y : RatFunc F} {m : ℤ}
    (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m) :
    (x + y).intDegree ≤ m := by
  by_cases hxy : x + y = 0
  · simp [hxy, hm]
  by_cases hy0 : y = 0
  · simpa [hy0] using hx
  exact (RatFunc.intDegree_add_le hy0 hxy).trans (max_le hx hy)

private lemma intDegree_add_sub_le_of_le {x y z : RatFunc F} {m : ℤ}
    (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m)
    (hz : z.intDegree ≤ m) : (x + y - z).intDegree ≤ m := by
  rw [sub_eq_add_neg]
  apply intDegree_add_le_of_le (x := x + y) (y := -z) hm
  · exact intDegree_add_le_of_le (x := x) (y := y) hm hx hy
  · rw [RatFunc.intDegree_neg]
    exact hz

private lemma intDegree_mul_le_of_le {x y : RatFunc F} {m n : ℤ}
    (hmn : 0 ≤ m + n) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ n) :
    (x * y).intDegree ≤ m + n := by
  by_cases hx0 : x = 0
  · simp [hx0, hmn]
  by_cases hy0 : y = 0
  · simp [hy0, hmn]
  rw [RatFunc.intDegree_mul hx0 hy0]
  exact add_le_add hx hy

private def twist (W : WeierstrassCurve F) : WeierstrassCurve (RatFunc F) :=
  ⟨0, RatFunc.C W.a₂ * cubicRat W, 0, RatFunc.C W.a₄ * cubicRat W ^ 2,
    RatFunc.C W.a₆ * cubicRat W ^ 3⟩

private instance (W : WeierstrassCurve F) : (twist W).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

private lemma twist_discriminant (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).Δ = cubicRat W ^ 6 * RatFunc.C W.Δ := by
  rw [WeierstrassCurve.Δ_of_isCharNeTwoNF,
    WeierstrassCurve.Δ_of_isCharNeTwoNF]
  simp only [twist, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
  ring

private instance (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, twist_discriminant, isUnit_iff_ne_zero]
  apply mul_ne_zero (pow_ne_zero 6 (cubicRat_ne_zero W))
  have hΔ : W.Δ ≠ 0 := by
    rw [← W.coe_Δ']
    exact Units.ne_zero W.Δ'
  simpa using RatFunc.C_injective.ne hΔ

private lemma q_equation (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).toAffine.Equation
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twist]
  rw [cubicRat_eq]
  ring

private def Q (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (q_equation W)

private lemma card_odd [Finite F] (hchar : ringChar F ≠ 2) : Odd (Nat.card F) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  obtain ⟨p, hpF, n, hp, hcard⟩ := @FiniteField.card' F _ fintypeF
  let _ : CharP F p := hpF
  have hpne : p ≠ 2 := by
    intro h
    apply hchar
    rw [ringChar.eq F p, h]
  rw [hcard]
  exact hp.odd_of_ne_two hpne |>.pow

private lemma twice_half_card_add_three [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 3) / 2) = Nat.card F + 3 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma aeval_cubic_X_pow_card [Finite F] (W : WeierstrassCurve F) :
    aeval (RatFunc.X ^ Nat.card F) (cubic W) = cubicRat W ^ Nat.card F := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  calc
    aeval (RatFunc.X ^ Fintype.card F) (cubic W) =
        aeval RatFunc.X (Polynomial.expand F (Fintype.card F) (cubic W)) := by
      rw [Polynomial.expand_aeval]
    _ = aeval RatFunc.X (cubic W ^ Fintype.card F) := by
      rw [FiniteField.expand_card]
    _ = cubicRat W ^ Fintype.card F := by
      simp [cubicRat, RatFunc.aeval_X_left_eq_algebraMap]

private def pZeroX [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  cubicRat W * RatFunc.X ^ Nat.card F

private def pZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  cubicRat W ^ ((Nat.card F + 3) / 2)

private lemma pZero_equation [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] :
    (twist W).toAffine.Equation (pZeroX W) (pZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twist, pZeroX, pZeroY]
  have hcubic := aeval_cubic_X_pow_card W
  simp only [cubic, map_add, map_mul, map_pow, aeval_X, aeval_C] at hcubic
  rw [← pow_mul]
  rw [show (Nat.card F + 3) / 2 * 2 = Nat.card F + 3 by
    rw [mul_comm, twice_half_card_add_three hchar]]
  simp only [zero_mul, add_zero]
  calc
    cubicRat W ^ (Nat.card F + 3) =
        cubicRat W ^ 3 * cubicRat W ^ Nat.card F := by
      rw [pow_add]
      ring
    _ = cubicRat W ^ 3 *
        ((RatFunc.X ^ Nat.card F) ^ 3 +
          algebraMap F (RatFunc F) W.a₂ * (RatFunc.X ^ Nat.card F) ^ 2 +
          algebraMap F (RatFunc F) W.a₄ * RatFunc.X ^ Nat.card F +
          algebraMap F (RatFunc F) W.a₆) := by
      rw [← hcubic]
    _ = _ := by
      simp only [RatFunc.algebraMap_eq_C]
      ring

private def P₀ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (twist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (pZero_equation hchar W)

private local instance : DecidableEq F := Classical.decEq F

private def point [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    (twist W).toAffine.Point :=
  P₀ hchar W + n • Q W

private def paperX (W : WeierstrassCurve F) (x : RatFunc F) : RatFunc F :=
  x / cubicRat W

private def paperY (W : WeierstrassCurve F) (y : RatFunc F) : RatFunc F :=
  y / cubicRat W ^ 2

private def badAtInfinity (W : WeierstrassCurve F) :
    (twist W).toAffine.Point → Prop
  | 0 => False
  | .some x _ _ => (paperX W x).intDegree ≤ 0

private lemma paper_coordinates_equation (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y) :
    cubicRat W * paperY W y ^ 2 =
      paperX W x ^ 3 + RatFunc.C W.a₂ * paperX W x ^ 2 +
        RatFunc.C W.a₄ * paperX W x + RatFunc.C W.a₆ := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [twist] at heq
  unfold paperX paperY
  field_simp [cubicRat_ne_zero W]
  linear_combination heq

private lemma intDegree_pow_le_zero {x : RatFunc F} (hx : x.intDegree ≤ 0) (n : ℕ) :
    (x ^ n).intDegree ≤ 0 := by
  by_cases hx0 : x = 0
  · cases n <;> simp [hx0]
  rw [intDegree_pow hx0]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hx

private lemma intDegree_cubic_paperX_le_zero (W : WeierstrassCurve F)
    {x : RatFunc F} (hx : x.intDegree ≤ 0) :
    (x ^ 3 + RatFunc.C W.a₂ * x ^ 2 + RatFunc.C W.a₄ * x +
      RatFunc.C W.a₆).intDegree ≤ 0 := by
  have hx3 : (x ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
  have hx2 : (x ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hx 2
  have ha2 : (RatFunc.C W.a₂ * x ^ 2).intDegree ≤ 0 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₂) (y := x ^ 2)
      (m := 0) (n := 0) (by norm_num) (by simp) hx2
  have ha4 : (RatFunc.C W.a₄ * x).intDegree ≤ 0 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₄) (y := x)
      (m := 0) (n := 0) (by norm_num) (by simp) hx
  have h₁ := intDegree_add_le_of_le (m := 0) (by norm_num) hx3 ha2
  have h₂ := intDegree_add_le_of_le (m := 0) (by norm_num) h₁ ha4
  exact intDegree_add_le_of_le (m := 0) (by norm_num) h₂ (by simp)

private lemma intDegree_cubicRat_mul_paperY_le_one
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y : RatFunc F} (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : (paperX W x).intDegree ≤ 0) :
    (cubicRat W * paperY W y).intDegree ≤ 1 := by
  let r := paperX W x
  let s := paperY W y
  change (cubicRat W * s).intDegree ≤ 1
  by_cases hs0 : s = 0
  · simp [s, hs0]
  have hA : cubicRat W ≠ 0 := cubicRat_ne_zero W
  have hAs : cubicRat W * s ≠ 0 := mul_ne_zero hA hs0
  have heq := paper_coordinates_equation W hxy
  change cubicRat W * s ^ 2 =
    r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r + RatFunc.C W.a₆ at heq
  have hr : r.intDegree ≤ 0 := hx
  have hcubic := intDegree_cubic_paperX_le_zero W hr
  have hproduct :
      (cubicRat W *
        (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
          RatFunc.C W.a₆)).intDegree ≤ 3 := by
    have := intDegree_mul_le_of_le (x := cubicRat W)
      (y := r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆) (m := 3) (n := 0) (by norm_num)
      (by rw [intDegree_cubicRat]) hcubic
    norm_num at this ⊢
    exact this
  have hsquare : (cubicRat W * s) ^ 2 =
      cubicRat W *
        (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
          RatFunc.C W.a₆) := by
    calc
      (cubicRat W * s) ^ 2 = cubicRat W * (cubicRat W * s ^ 2) := by ring
      _ = _ := by rw [heq]
  rw [← hsquare, intDegree_pow hAs] at hproduct
  norm_num at hproduct ⊢
  omega

private lemma paperX_Q_coordinate (W : WeierstrassCurve F) :
    paperX W (cubicRat W * RatFunc.X) = RatFunc.X := by
  unfold paperX
  field_simp [cubicRat_ne_zero W]

private lemma paperX_addX_Q_eq (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      cubicRat W *
          ((paperY W y - 1) / (paperX W x - RatFunc.X)) ^ 2 -
        RatFunc.C W.a₂ - paperX W x - RatFunc.X := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, twist]
  unfold paperX paperY
  field_simp [cubicRat_ne_zero W, hx]
  ring

private lemma paperX_addX_Q_canceled (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      ((RatFunc.X + paperX W x) *
          (RatFunc.C W.a₄ + RatFunc.X * paperX W x) +
        2 * (RatFunc.C W.a₂ * RatFunc.X * paperX W x + RatFunc.C W.a₆) -
        2 * cubicRat W * paperY W y) /
      (RatFunc.X - paperX W x) ^ 2 := by
  rw [paperX_addX_Q_eq W hx]
  have heq := paper_coordinates_equation W hxy
  have hden : paperX W x - RatFunc.X ≠ 0 := by
    intro h
    apply hx
    have hpaper : paperX W x = RatFunc.X := sub_eq_zero.mp h
    unfold paperX at hpaper
    calc
      x = RatFunc.X * cubicRat W := (div_eq_iff (cubicRat_ne_zero W)).mp hpaper
      _ = cubicRat W * RatFunc.X := mul_comm _ _
  rw [cubicRat_eq W] at heq ⊢
  field_simp [hden, sub_ne_zero.mpr (Ne.symm <| sub_ne_zero.mp hden)]
  linear_combination (paperX W x - RatFunc.X) ^ 2 * heq

set_option maxHeartbeats 500000 in
-- The expanded three-term rational-function bound needs extra elaboration budget.
private lemma intDegree_canceled_numerator_le_two
    (A r s : RatFunc F) (a b c : F) (hr : r.intDegree ≤ 0)
    (hAs : (A * s).intDegree ≤ 1) :
    ((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
      2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) -
      2 * A * s).intDegree ≤ 2 := by
  have hXr : (RatFunc.X * r).intDegree ≤ 1 := by
    simpa using intDegree_mul_le_of_le (x := RatFunc.X) (y := r)
      (m := 1) (n := 0) (by norm_num) (by simp) hr
  have hXadd : (RatFunc.X + r).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) (by simp) (hr.trans (by norm_num))
  have hbXr : (RatFunc.C b + RatFunc.X * r).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) (by simp) hXr
  have hfirst :
      ((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r)).intDegree ≤ 2 := by
    simpa using intDegree_mul_le_of_le
      (x := RatFunc.X + r) (y := RatFunc.C b + RatFunc.X * r)
      (m := 1) (n := 1) (by norm_num) hXadd hbXr
  have haXr : (RatFunc.C a * RatFunc.X * r).intDegree ≤ 1 := by
    have haX : (RatFunc.C a * RatFunc.X).intDegree ≤ 1 := by
      simpa using intDegree_mul_le_of_le (x := RatFunc.C a) (y := RatFunc.X)
        (m := 0) (n := 1) (by norm_num) (by simp) (by simp)
    simpa [mul_assoc] using intDegree_mul_le_of_le
      (x := RatFunc.C a * RatFunc.X) (y := r)
      (m := 1) (n := 0) (by norm_num) haX hr
  have hmiddleInside :
      (RatFunc.C a * RatFunc.X * r + RatFunc.C c).intDegree ≤ 1 :=
    intDegree_add_le_of_le (m := 1) (by norm_num) haXr (by simp)
  have hmiddle :
      (2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c)).intDegree ≤ 1 := by
    rw [show 2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) =
      (RatFunc.C a * RatFunc.X * r + RatFunc.C c) +
        (RatFunc.C a * RatFunc.X * r + RatFunc.C c) by ring]
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hmiddleInside hmiddleInside
  have hlast : (2 * A * s).intDegree ≤ 1 := by
    rw [show 2 * A * s = A * s + A * s by ring]
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hAs hAs
  exact intDegree_add_sub_le_of_le
    (x := (RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r))
    (y := 2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c))
    (z := 2 * A * s) (m := 2) (by norm_num) hfirst
      (hmiddle.trans (by norm_num)) (hlast.trans (by norm_num))

private lemma intDegree_X_sub_eq_one {r : RatFunc F} (hr : r.intDegree ≤ 0) :
    (RatFunc.X - r).intDegree = 1 := by
  have hneg : (-r).intDegree ≤ 1 := by
    rw [RatFunc.intDegree_neg]
    exact hr.trans (by norm_num)
  have hdiffLe : (RatFunc.X - r).intDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    exact intDegree_add_le_of_le (x := RatFunc.X) (y := -r)
      (m := 1) (by norm_num) (by simp) hneg
  have hdiffNotLe : ¬(RatFunc.X - r).intDegree ≤ 0 := by
    intro hdiff
    have hbad : (RatFunc.X : RatFunc F).intDegree ≤ 0 := by
      rw [show (RatFunc.X : RatFunc F) = (RatFunc.X - r) + r by ring]
      exact intDegree_add_le_of_le (x := RatFunc.X - r) (y := r)
        (m := 0) (by norm_num) hdiff hr
    norm_num at hbad
  omega

private lemma intDegree_canceled_expression_le_zero
    (A r s : RatFunc F) (a b c : F) (hr : r.intDegree ≤ 0)
    (hAs : (A * s).intDegree ≤ 1) :
    (((RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
      2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) - 2 * A * s) /
      (RatFunc.X - r) ^ 2).intDegree ≤ 0 := by
  let numerator :=
    (RatFunc.X + r) * (RatFunc.C b + RatFunc.X * r) +
      2 * (RatFunc.C a * RatFunc.X * r + RatFunc.C c) - 2 * A * s
  have hnumerator : numerator.intDegree ≤ 2 := by
    dsimp only [numerator]
    exact intDegree_canceled_numerator_le_two A r s a b c hr hAs
  have hdiffDegree : (RatFunc.X - r).intDegree = 1 := intDegree_X_sub_eq_one hr
  have hdiffNe : RatFunc.X - r ≠ 0 := by
    intro h
    rw [h] at hdiffDegree
    simp at hdiffDegree
  have hdenDegree : ((RatFunc.X - r) ^ 2).intDegree = 2 := by
    rw [intDegree_pow hdiffNe, hdiffDegree]
    norm_num
  change (numerator / (RatFunc.X - r) ^ 2).intDegree ≤ 0
  by_cases hn0 : numerator = 0
  · simp [hn0]
  rw [RatFunc.intDegree_div hn0 (pow_ne_zero 2 hdiffNe), hdenDegree]
  omega

private lemma intDegree_paperX_addX_Q_le_zero
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y : RatFunc F} (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X)
    (hdegree : (paperX W x).intDegree ≤ 0) :
    (paperX W
      ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
        ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
          (cubicRat W ^ 2)))).intDegree ≤ 0 := by
  rw [paperX_addX_Q_canceled W hxy hx]
  exact intDegree_canceled_expression_le_zero
    (cubicRat W) (paperX W x) (paperY W y) W.a₂ W.a₄ W.a₆ hdegree
      (intDegree_cubicRat_mul_paperY_le_one W hxy hdegree)

private lemma badAtInfinity_neg (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (P : (twist W).toAffine.Point) :
    badAtInfinity W (-P) ↔ badAtInfinity W P := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      rw [WeierstrassCurve.Affine.Point.neg_some]
      rfl

private lemma badAtInfinity_add_Q (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {P : (twist W).toAffine.Point}
    (hP : badAtInfinity W P) : badAtInfinity W (P + Q W) := by
  cases P with
  | zero => simp [badAtInfinity] at hP
  | some x y hxy =>
      change (paperX W x).intDegree ≤ 0 at hP
      have hx : x ≠ cubicRat W * RatFunc.X := by
        intro hx
        have hpaper : paperX W x = RatFunc.X := by
          rw [hx, paperX_Q_coordinate]
        rw [hpaper] at hP
        norm_num at hP
      have hvertical :
          ¬(x = cubicRat W * RatFunc.X ∧
            y = (twist W).toAffine.negY (cubicRat W * RatFunc.X)
              (cubicRat W ^ 2)) := fun h ↦ hx h.1
      rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) _ from rfl]
      rw [WeierstrassCurve.Affine.Point.add_some hvertical]
      exact intDegree_paperX_addX_Q_le_zero W hxy hx hP

private lemma badAtInfinity_sub_Q (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {P : (twist W).toAffine.Point}
    (hP : badAtInfinity W P) : badAtInfinity W (P - Q W) := by
  have hnegP : badAtInfinity W (-P) := (badAtInfinity_neg W P).mpr hP
  have hadd := badAtInfinity_add_Q W hnegP
  rw [show P - Q W = -(-P + Q W) by abel]
  exact (badAtInfinity_neg W (-P + Q W)).mpr hadd

private lemma badAtInfinity_add_Q_iff (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (P : (twist W).toAffine.Point) :
    badAtInfinity W (P + Q W) ↔ badAtInfinity W P := by
  refine ⟨fun h ↦ ?_, badAtInfinity_add_Q W⟩
  have hsub := badAtInfinity_sub_Q W h
  simpa using hsub

private lemma point_add_one [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    point hchar W (n + 1) = point hchar W n + Q W := by
  rw [point, point, add_one_zsmul]
  abel

private lemma paperX_pZeroX [Finite F] (W : WeierstrassCurve F) :
    paperX W (pZeroX W) = RatFunc.X ^ Nat.card F := by
  unfold paperX pZeroX
  field_simp [cubicRat_ne_zero W]

private lemma pZero_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ¬badAtInfinity W (P₀ hchar W) := by
  intro hbad
  change (paperX W (pZeroX W)).intDegree ≤ 0 at hbad
  rw [paperX_pZeroX, intDegree_pow RatFunc.X_ne_zero] at hbad
  simp only [RatFunc.intDegree_X, mul_one] at hbad
  have hcard : (0 : ℤ) < Nat.card F := by exact_mod_cast Nat.card_pos
  omega

private lemma point_not_badAtInfinity [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    ¬badAtInfinity W (point hchar W n) := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa [point] using pZero_not_badAtInfinity hchar W
  · intro k _ hk hbad
    apply hk
    apply (badAtInfinity_add_Q_iff W (point hchar W k)).mp
    rw [← point_add_one hchar W k]
    exact hbad
  · intro k _ hk hbad
    apply hk
    have hstep := point_add_one hchar W (k - 1)
    rw [show k - 1 + 1 = k by ring] at hstep
    rw [hstep]
    exact (badAtInfinity_add_Q_iff W (point hchar W (k - 1))).mpr hbad

private lemma Q_ne_zero (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    Q W ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

private def d [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) : ℕ :=
  match point hchar W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num (x / cubicRat W)).natDegree

private lemma num_natDegree_gt_denom_natDegree [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} {x y : RatFunc F}
    {hxy : (twist W).toAffine.Nonsingular x y}
    (hn : point hchar W n = .some x y hxy) :
    (RatFunc.denom (x / cubicRat W)).natDegree <
      (RatFunc.num (x / cubicRat W)).natDegree := by
  have hnotBad := point_not_badAtInfinity hchar W n
  have hnotLe : ¬(paperX W x).intDegree ≤ 0 := by
    intro hdegree
    apply hnotBad
    rw [hn]
    exact hdegree
  have hpos : 0 < (paperX W x).intDegree := lt_of_not_ge hnotLe
  unfold paperX RatFunc.intDegree at hpos
  omega

private lemma d_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    d hchar W 0 = Nat.card F := by
  rw [d, point]
  simp only [zero_zsmul, add_zero, P₀, WeierstrassCurve.Affine.Point.mk]
  have hx : pZeroX W / cubicRat W = RatFunc.X ^ Nat.card F := by
    rw [div_eq_iff (cubicRat_ne_zero W)]
    simp only [pZeroX]
    ring
  rw [hx]
  change
    (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
      Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

private lemma d_eq_zero_iff_point_eq_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (n : ℤ) :
    d hchar W n = 0 ↔ point hchar W n = 0 := by
  cases hp : point hchar W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [d, hp]
  | some x y hxy =>
      have hdeg := num_natDegree_gt_denom_natDegree hchar W hp
      constructor
      · intro hd
        simp only [d, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

private lemma noAdjacentZeros [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ∀ n, d hchar W n = 0 → d hchar W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (d_eq_zero_iff_point_eq_zero hchar W n).mp hn
  have hp1 := (d_eq_zero_iff_point_eq_zero hchar W (n + 1)).mp hn1
  apply Q_ne_zero W
  have hs := point_add_one hchar W n
  rw [hp, hp1] at hs
  simpa using hs.symm

private def frobeniusPolynomial [Finite F] : F[X] :=
  X ^ Nat.card F - X

private def eulerPolynomial [Finite F] (W : WeierstrassCurve F) : F[X] :=
  cubic W ^ ((Nat.card F - 1) / 2)

private def minusOneNumerator [Finite F] (W : WeierstrassCurve F) : F[X] :=
  cubic W * (eulerPolynomial W + 1) ^ 2 -
    (C W.a₂ + X ^ Nat.card F + X) * frobeniusPolynomial ^ 2

private lemma card_gt_three [Finite F] (hchar : ringChar F ≠ 2)
    (hcard : Nat.card F ≠ 3) : 3 < Nat.card F := by
  obtain ⟨k, hk⟩ := card_odd hchar
  have hlarge := Finite.one_lt_card (α := F)
  omega

private lemma twice_half_card_sub_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma twice_half_card_add_one [Finite F] (hchar : ringChar F ≠ 2) :
    2 * ((Nat.card F + 1) / 2) = Nat.card F + 1 := by
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma cubic_pow_card [Finite F] (W : WeierstrassCurve F) :
    cubic W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₂ * X ^ (2 * Nat.card F) +
        C W.a₄ * X ^ Nat.card F + C W.a₆ := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  rw [← FiniteField.expand_card]
  simp only [cubic, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma minusOneNumerator_eq [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    minusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
        C (2 * W.a₂) * X ^ (Nat.card F + 1) +
        C W.a₄ * X ^ Nat.card F +
        C 2 * cubic W ^ ((Nat.card F + 1) / 2) + C W.a₄ * X +
        C (2 * W.a₆) := by
  have heven := twice_half_card_sub_one (F := F) hchar
  have hpower :
      cubic W * eulerPolynomial W ^ 2 = cubic W ^ Nat.card F := by
    rw [eulerPolynomial, ← pow_mul]
    rw [show (Nat.card F - 1) / 2 * 2 = Nat.card F - 1 by
      rw [mul_comm, heven]]
    calc
      cubic W * cubic W ^ (Nat.card F - 1) =
          cubic W ^ (Nat.card F - 1 + 1) := (pow_succ' _ _).symm
      _ = cubic W ^ Nat.card F := by
        congr
        have hpos := Nat.card_pos (α := F)
        omega
  have hmiddle :
      cubic W * (C 2 * eulerPolynomial W) =
        C 2 * cubic W ^ ((Nat.card F + 1) / 2) := by
    rw [eulerPolynomial]
    have hadd : (Nat.card F - 1) / 2 + 1 = (Nat.card F + 1) / 2 := by
      obtain ⟨k, hk⟩ := card_odd hchar
      omega
    rw [show cubic W * (C 2 * cubic W ^ ((Nat.card F - 1) / 2)) =
      C 2 * cubic W ^ ((Nat.card F - 1) / 2 + 1) by ring]
    rw [hadd]
  unfold minusOneNumerator
  rw [show (eulerPolynomial W + 1) ^ 2 =
    eulerPolynomial W ^ 2 + C 2 * eulerPolynomial W + 1 by
      rw [Polynomial.C_ofNat]
      ring]
  rw [mul_add, mul_add, hpower, hmiddle, mul_one, cubic_pow_card]
  unfold frobeniusPolynomial
  simp only [cubic, map_mul, map_ofNat]
  ring

private lemma natDegree_add_le_of_le {p q : F[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n :=
  (Polynomial.natDegree_add_le p q).trans (max_le hp hq)

private lemma minusOneNumerator_natDegree [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (hcard : Nat.card F ≠ 3) :
    (minusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  have hq := card_gt_three (F := F) hchar hcard
  have hhalf := twice_half_card_add_one (F := F) hchar
  let remainder : F[X] :=
    X ^ (Nat.card F + 2) +
      (C (2 * W.a₂) * X ^ (Nat.card F + 1) +
        (C W.a₄ * X ^ Nat.card F +
          (C 2 * cubic W ^ ((Nat.card F + 1) / 2) +
            (C W.a₄ * X + C (2 * W.a₆)))))
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    dsimp only [remainder]
    apply natDegree_add_le_of_le
    · rw [Polynomial.natDegree_X_pow]
      omega
    apply natDegree_add_le_of_le
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    apply natDegree_add_le_of_le
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    apply natDegree_add_le_of_le
    · calc
        (C 2 * cubic W ^ ((Nat.card F + 1) / 2)).natDegree ≤
            (cubic W ^ ((Nat.card F + 1) / 2)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        _ = (Nat.card F + 1) / 2 * 3 := by
          rw [Polynomial.natDegree_pow, cubic_natDegree]
        _ ≤ 2 * Nat.card F := by omega
    apply natDegree_add_le_of_le
    · simpa only [pow_one] using
        (Polynomial.natDegree_C_mul_X_pow_le W.a₄ 1).trans (by omega)
    · rw [Polynomial.natDegree_C]
      omega
  have heq :
      minusOneNumerator W = X ^ (2 * Nat.card F + 1) + remainder := by
    rw [minusOneNumerator_eq hchar]
    dsimp only [remainder]
    ring
  rw [heq]
  have hlt :
      remainder.natDegree < (X ^ (2 * Nat.card F + 1) : F[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    omega
  calc
    (X ^ (2 * Nat.card F + 1) + remainder).natDegree =
        (X ^ (2 * Nat.card F + 1) : F[X]).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt
    _ = 2 * Nat.card F + 1 := Polynomial.natDegree_X_pow _

private lemma pZeroX_ne_qX [Finite F] (W : WeierstrassCurve F) :
    pZeroX W ≠ cubicRat W * RatFunc.X := by
  intro h
  have hpow : RatFunc.X ^ Nat.card F = RatFunc.X :=
    mul_left_cancel₀ (cubicRat_ne_zero W) h
  have hdegree := congrArg RatFunc.intDegree hpow
  rw [intDegree_pow RatFunc.X_ne_zero, RatFunc.intDegree_X] at hdegree
  simp only [mul_one] at hdegree
  have hcard := Finite.one_lt_card (α := F)
  omega

private lemma paperY_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W (pZeroY W) = cubicRat W ^ ((Nat.card F - 1) / 2) := by
  have hexponent :
      (Nat.card F + 3) / 2 = (Nat.card F - 1) / 2 + 2 := by
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  unfold paperY pZeroY
  rw [hexponent, pow_add]
  field_simp [cubicRat_ne_zero W]

private lemma cubic_mul_eulerPolynomial [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    cubic W * eulerPolynomial W = cubic W ^ ((Nat.card F + 1) / 2) := by
  unfold eulerPolynomial
  rw [show cubic W * cubic W ^ ((Nat.card F - 1) / 2) =
    cubic W ^ ((Nat.card F - 1) / 2 + 1) by
      exact (pow_succ' _ _).symm]
  congr 1
  obtain ⟨k, hk⟩ := card_odd hchar
  omega

private lemma minusOneNumerator_canceled_eq [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    minusOneNumerator W =
      (X + X ^ Nat.card F) * (C W.a₄ + X * X ^ Nat.card F) +
        C 2 * (C W.a₂ * X * X ^ Nat.card F + C W.a₆) +
        C 2 * cubic W * eulerPolynomial W := by
  rw [minusOneNumerator_eq hchar]
  rw [show C 2 * cubic W * eulerPolynomial W =
    C 2 * (cubic W * eulerPolynomial W) by ring]
  rw [cubic_mul_eulerPolynomial hchar]
  simp only [cubic, map_mul, map_ofNat]
  ring

private lemma paperY_neg_pZeroY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) :
    paperY W ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) =
      -(cubicRat W ^ ((Nat.card F - 1) / 2)) := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  rw [show paperY W (-pZeroY W) = -paperY W (pZeroY W) by
    unfold paperY
    exact neg_div _ _]
  rw [paperY_pZeroY hchar W]

private lemma algebraMap_frobeniusPolynomial [Finite F] :
    algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) =
      RatFunc.X ^ Nat.card F - RatFunc.X := by
  simp [frobeniusPolynomial, RatFunc.algebraMap_X]

private lemma algebraMap_minusOneNumerator [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    algebraMap F[X] (RatFunc F) (minusOneNumerator W) =
      (RatFunc.X + RatFunc.X ^ Nat.card F) *
          (RatFunc.C W.a₄ + RatFunc.X * RatFunc.X ^ Nat.card F) +
        2 * (RatFunc.C W.a₂ * RatFunc.X * RatFunc.X ^ Nat.card F +
          RatFunc.C W.a₆) +
        2 * cubicRat W * cubicRat W ^ ((Nat.card F - 1) / 2) := by
  rw [minusOneNumerator_canceled_eq hchar]
  simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, cubicRat, eulerPolynomial]

private lemma paperX_negPZero_add_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] :
    paperX W
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))) =
      algebraMap F[X] (RatFunc F) (minusOneNumerator W) /
        algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) ^ 2 := by
  have hp : (twist W).toAffine.Nonsingular (pZeroX W) (pZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (pZero_equation hchar W)
  have hneg : (twist W).toAffine.Nonsingular (pZeroX W)
      ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) :=
    ((twist W).toAffine.nonsingular_neg _ _).mpr hp
  rw [paperX_addX_Q_canceled W hneg (pZeroX_ne_qX W)]
  rw [paperX_pZeroX, paperY_neg_pZeroY hchar W]
  rw [algebraMap_minusOneNumerator hchar, algebraMap_frobeniusPolynomial]
  ring

private lemma point_neg_one_eq_some [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] :
    ∃ y hxy, point hchar W (-1) =
      .some
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))) y hxy := by
  have hp : (twist W).toAffine.Nonsingular (pZeroX W) (pZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (pZero_equation hchar W)
  have hneg : (twist W).toAffine.Nonsingular (pZeroX W)
      ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) :=
    ((twist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -P₀ hchar W = .some (pZeroX W)
        ((twist W).toAffine.negY (pZeroX W) (pZeroY W)) hneg := by
    rw [show P₀ hchar W = .some (pZeroX W) (pZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) (pZeroX_ne_qX W)
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W))
  rw [← hnegP, ← show Q W = .some (cubicRat W * RatFunc.X)
    (cubicRat W ^ 2) _ from rfl] at hadd
  have hpoint : point hchar W (-1) = -(-P₀ hchar W + Q W) := by
    unfold point
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private def squareFiber (W : WeierstrassCurve F) (x : F) :=
  {y : F // y ^ 2 = (cubic W).eval x}

private instance squareFiberFinite [Finite F] (W : WeierstrassCurve F)
    (x : F) : Finite (squareFiber W x) := by
  unfold squareFiber
  infer_instance

private lemma two_ne_zero_of_ringChar_ne_two (hchar : ringChar F ≠ 2) :
    (2 : F) ≠ 0 := by
  let _ : CharP F (ringChar F) := ringChar.charP F
  intro htwo
  have hdvd : ringChar F ∣ 2 :=
    (CharP.cast_eq_zero_iff F (ringChar F) 2).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwoChar
  · have hcast : ((1 : ℕ) : F) = 0 :=
      (CharP.cast_eq_zero_iff F (ringChar F) 1).mpr (by simp [hone])
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa only [Nat.cast_one] using hcast)
  · exact hchar htwoChar

private lemma squareFiber_natCard_eq_one [Finite F] (W : WeierstrassCurve F)
    (x : F) (hzero : (cubic W).eval x = 0) :
    Nat.card (squareFiber W x) = 1 := by
  let _ : Nonempty (squareFiber W x) :=
    ⟨⟨0, by simp [hzero]⟩⟩
  let _ : Subsingleton (squareFiber W x) := ⟨by
    intro y z
    apply Subtype.ext
    have hy : y.1 = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using y.2)
    have hz : z.1 = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using z.2)
    rw [hy, hz]⟩
  exact Nat.card_unique

private lemma squareFiber_natCard_eq_two [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    Nat.card (squareFiber W x) = 2 := by
  classical
  rcases hsquare with ⟨r, hr⟩
  have hrpow : r ^ 2 = (cubic W).eval x := by
    simpa [pow_two] using hr.symm
  have hrzero : r ≠ 0 := by
    intro hr0
    apply hzero
    rw [← hrpow, hr0]
    simp
  have hneg : -r ≠ r := by
    intro h
    have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
    have hadd : r + r = 0 := by
      calc
        r + r = -r + r := congrArg (fun z : F ↦ z + r) h.symm
        _ = 0 := neg_add_cancel r
    have hproduct : (2 : F) * r = 0 := by
      rw [two_mul]
      exact hadd
    exact hrzero ((mul_eq_zero.mp hproduct).resolve_left htwo)
  let e : squareFiber W x ≃ Bool :=
    { toFun := fun y ↦ if y.1 = r then true else false
      invFun := fun b ↦ match b with
        | true => ⟨r, hrpow⟩
        | false => ⟨-r, by simpa using hrpow⟩
      left_inv := by
        intro y
        have hy : y.1 = r ∨ y.1 = -r :=
          (sq_eq_sq_iff_eq_or_eq_neg).mp (y.2.trans hrpow.symm)
        apply Subtype.ext
        rcases hy with hy | hy
        · simp [hy]
        · simp [hy, hneg]
      right_inv := by
        intro b
        cases b <;> simp [hneg] }
  simpa using Nat.card_congr e

private lemma squareFiber_natCard_eq_zero [Finite F]
    (W : WeierstrassCurve F) (x : F)
    (hsquare : ¬IsSquare ((cubic W).eval x)) :
    Nat.card (squareFiber W x) = 0 := by
  let _ : IsEmpty (squareFiber W x) := ⟨fun y ↦ hsquare ⟨y.1, by
    simpa [pow_two] using y.2.symm⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private lemma eval_eulerPolynomial [Fintype F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) (x : F) :
    (eulerPolynomial W).eval x =
      ((quadraticChar F) ((cubic W).eval x) : F) := by
  have hhalf :
      Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := card_odd hchar
    omega
  have hcriterion :=
    quadraticChar_eq_pow_of_char_ne_two' hchar ((cubic W).eval x)
  rw [hhalf] at hcriterion
  unfold eulerPolynomial
  rw [eval_pow, Nat.card_eq_fintype_card]
  exact hcriterion.symm

private lemma eval_eulerPolynomial_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (eulerPolynomial W).eval x = 0 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar, hzero]
  simp

private lemma eval_eulerPolynomial_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [(quadraticChar_one_iff_isSquare hzero).mpr hsquare]
  simp

private lemma eval_eulerPolynomial_eq_neg_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (eulerPolynomial W).eval x = -1 := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [eval_eulerPolynomial hchar]
  rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsquare]
  simp

private lemma eval_frobeniusPolynomial [Finite F] (x : F) :
    (frobeniusPolynomial : F[X]).eval x = 0 := by
  let _ : Fintype F := Fintype.ofFinite F
  unfold frobeniusPolynomial
  rw [eval_sub, eval_pow, eval_X, Nat.card_eq_fintype_card,
    FiniteField.pow_card, sub_self]

private lemma eval_minusOneNumerator [Finite F]
    (W : WeierstrassCurve F) (x : F) :
    (minusOneNumerator W).eval x =
      (cubic W).eval x * ((eulerPolynomial W).eval x + 1) ^ 2 := by
  unfold minusOneNumerator
  simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_one]
  rw [eval_frobeniusPolynomial]
  ring

private lemma eval_derivative_minusOneNumerator_of_cubic_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F)
    (hzero : (cubic W).eval x = 0) :
    (minusOneNumerator W).derivative.eval x = (cubic W).derivative.eval x := by
  have heuler := eval_eulerPolynomial_eq_zero hchar W x hzero
  have hfrobenius := eval_frobeniusPolynomial (F := F) x
  unfold minusOneNumerator
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_add,
    derivative_one, eval_sub, eval_add, eval_mul, eval_pow, eval_one]
  rw [hzero, heuler, hfrobenius]
  ring

private lemma eval_derivative_cubic_ne_zero
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (x : F) (hzero : (cubic W).eval x = 0) :
    (cubic W).derivative.eval x ≠ 0 := by
  intro hderivative
  obtain ⟨u, v, huv⟩ :=
    (Polynomial.separable_def (cubic W)).mp (cubic_separable W)
  have heval := congrArg (Polynomial.eval x) huv
  simp only [eval_add, eval_mul, eval_one] at heval
  rw [hzero, hderivative] at heval
  simp at heval

private lemma eval_derivative_eq_zero_of_sq_dvd {p : F[X]} {x : F}
    (hdiv : (X - C x) ^ 2 ∣ p) : p.derivative.eval x = 0 := by
  rcases hdiv with ⟨q, rfl⟩
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_X,
    derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  ring

private lemma minusOneNumerator_ne_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (hcard : Nat.card F ≠ 3) : minusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := minusOneNumerator_natDegree hchar W hcard
  rw [hzero] at hdegree
  simp at hdegree

private lemma rootMultiplicity_minusOneNumerator_eq_one [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) (hzero : (cubic W).eval x = 0) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 1 := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hroot : (minusOneNumerator W).IsRoot x := by
    change (minusOneNumerator W).eval x = 0
    rw [eval_minusOneNumerator, hzero]
    ring
  have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneNumerator W) := by
    rw [Polynomial.le_rootMultiplicity_iff hB]
    simpa using (Polynomial.dvd_iff_isRoot.mpr hroot)
  have hupper : Polynomial.rootMultiplicity x (minusOneNumerator W) ≤ 1 := by
    rw [Polynomial.rootMultiplicity_le_iff hB]
    intro hsquare
    have hderivative := eval_derivative_eq_zero_of_sq_dvd hsquare
    rw [eval_derivative_minusOneNumerator_of_cubic_eq_zero hchar W x hzero]
      at hderivative
    exact eval_derivative_cubic_ne_zero W x hzero hderivative
  omega

private lemma rootMultiplicity_minusOneNumerator_eq_zero [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hzero : (cubic W).eval x ≠ 0)
    (hsquare : IsSquare ((cubic W).eval x)) :
    Polynomial.rootMultiplicity x (minusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heuler := eval_eulerPolynomial_eq_one hchar W x hzero hsquare
  have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  have hsum : (1 + 1 : F) ≠ 0 := by
    intro h
    apply htwo
    norm_num at h ⊢
    exact h
  have heval : (minusOneNumerator W).eval x ≠ 0 := by
    rw [eval_minusOneNumerator, heuler]
    exact mul_ne_zero hzero (pow_ne_zero 2 hsum)
  exact heval hroot

private lemma sq_X_sub_C_dvd_minusOneNumerator [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    (x : F) (hsquare : ¬IsSquare ((cubic W).eval x)) :
    (X - C x) ^ 2 ∣ minusOneNumerator W := by
  have heuler := eval_eulerPolynomial_eq_neg_one hchar W x hsquare
  have heulerRoot : (eulerPolynomial W + 1).IsRoot x := by
    simp only [IsRoot, eval_add, eval_one, heuler]
    ring
  have hfrobeniusRoot : (frobeniusPolynomial : F[X]).IsRoot x :=
    eval_frobeniusPolynomial x
  obtain ⟨u, hu⟩ := Polynomial.dvd_iff_isRoot.mpr heulerRoot
  obtain ⟨v, hv⟩ := Polynomial.dvd_iff_isRoot.mpr hfrobeniusRoot
  refine ⟨cubic W * u ^ 2 - (C W.a₂ + X ^ Nat.card F + X) * v ^ 2, ?_⟩
  unfold minusOneNumerator
  rw [hu, hv]
  ring

private lemma count_roots_frobeniusPolynomial [Finite F] (x : F) :
    Multiset.count x (frobeniusPolynomial : F[X]).roots = 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  unfold frobeniusPolynomial
  rw [Nat.card_eq_fintype_card, FiniteField.roots_X_pow_card_sub_X]
  simp

private lemma count_roots_frobeniusPolynomial_sq [Finite F] (x : F) :
    Multiset.count x ((frobeniusPolynomial : F[X]) ^ 2).roots = 2 := by
  rw [Polynomial.roots_pow, Multiset.count_nsmul,
    count_roots_frobeniusPolynomial]

private lemma frobeniusPolynomial_ne_zero [Finite F] :
    (frobeniusPolynomial : F[X]) ≠ 0 := by
  intro hzero
  have hcount := count_roots_frobeniusPolynomial (F := F) 0
  rw [hzero] at hcount
  simp at hcount

private def minusOneGCD [Finite F] (W : WeierstrassCurve F) : F[X] :=
  gcd (minusOneNumerator W) (frobeniusPolynomial ^ 2)

private lemma count_roots_minusOneGCD [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3)
    (x : F) :
    Multiset.count x (minusOneGCD W).roots =
      2 - Nat.card (squareFiber W x) := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hG : minusOneGCD W ≠ 0 := by
    intro hzero
    unfold minusOneGCD at hzero
    exact hB ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivB : minusOneGCD W ∣ minusOneNumerator W := by
    unfold minusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (frobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_frobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣ (frobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hzero : (cubic W).eval x = 0
  · have hlinearB : X - C x ∣ minusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (minusOneNumerator W).eval x = 0
      rw [eval_minusOneNumerator, hzero]
      ring
    have hlinearL' : X - C x ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
      exact hlinearL.trans ⟨frobeniusPolynomial, by ring⟩
    have hcommon : X - C x ∣ minusOneGCD W := by
      unfold minusOneGCD
      exact dvd_gcd hlinearB hlinearL'
    have hlower : 1 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity x (minusOneGCD W) ≤
            Polynomial.rootMultiplicity x (minusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
        _ = 1 := rootMultiplicity_minusOneNumerator_eq_one
          hchar W hcard x hzero
    have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      squareFiber_natCard_eq_one W x hzero]
  · by_cases hsquare : IsSquare ((cubic W).eval x)
    · have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x (minusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hB hGdivB x
          _ = 0 := rootMultiplicity_minusOneNumerator_eq_zero
            hchar W x hzero hsquare
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_two hchar W x hzero hsquare]
    · have hcommon : (X - C x) ^ 2 ∣ minusOneGCD W := by
        unfold minusOneGCD
        exact dvd_gcd
          (sq_X_sub_C_dvd_minusOneNumerator hchar W x hsquare) hlinearLsq
      have hlower : 2 ≤ Polynomial.rootMultiplicity x (minusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL :
          Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_frobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (minusOneGCD W) ≤ 2 := by
        calc
          Polynomial.rootMultiplicity x (minusOneGCD W) ≤
              Polynomial.rootMultiplicity x ((frobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (minusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        squareFiber_natCard_eq_zero W x hsquare]

private lemma squareFiber_natCard_le_two [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F) :
    Nat.card (squareFiber W x) ≤ 2 := by
  by_cases hzero : (cubic W).eval x = 0
  · rw [squareFiber_natCard_eq_one W x hzero]
    omega
  by_cases hsquare : IsSquare ((cubic W).eval x)
  · rw [squareFiber_natCard_eq_two hchar W x hzero hsquare]
  · rw [squareFiber_natCard_eq_zero W x hsquare]
    omega

private lemma frobeniusPolynomial_splits [Finite F] :
    (frobeniusPolynomial : F[X]).Splits := by
  let _ : Fintype F := Fintype.ofFinite F
  rw [Polynomial.splits_iff_card_roots]
  unfold frobeniusPolynomial
  rw [Nat.card_eq_fintype_card, FiniteField.roots_X_pow_card_sub_X,
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  simp

private lemma minusOneGCD_natDegree [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
  have hL : (frobeniusPolynomial : F[X]) ≠ 0 :=
    frobeniusPolynomial_ne_zero
  have hLsq : (frobeniusPolynomial : F[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hGdivL : minusOneGCD W ∣ (frobeniusPolynomial : F[X]) ^ 2 := by
    unfold minusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (minusOneGCD W).Splits :=
    (frobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (minusOneGCD W).roots) =
        (minusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (minusOneGCD W).roots) (by simp))
  calc
    (minusOneGCD W).natDegree = (minusOneGCD W).roots.card :=
      hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (minusOneGCD W).roots := hsum.symm
    _ = ∑ x : F, (2 - Nat.card (squareFiber W x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_minusOneGCD hchar W hcard x

private lemma minusOneGCD_natDegree_add_fiber_sum [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneGCD W).natDegree + ∑ x : F, Nat.card (squareFiber W x) =
      2 * Nat.card F := by
  rw [minusOneGCD_natDegree hchar W hcard]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (squareFiber W x) +
        Nat.card (squareFiber W x))) = ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (squareFiber_natCard_le_two hchar W x)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma equation_iff_square (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 = (cubic W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharNeTwoNF,
    WeierstrassCurve.a₃_of_isCharNeTwoNF, zero_mul]
  simp only [cubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  simp

private def affineSolutionsEquivSquareFibers (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, squareFiber W x where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (equation_iff_square W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (equation_iff_square W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma pointCount_eq_fiber_sum [Fintype F]
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    Nat.card W.toAffine.Point =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivSquareFibers W), Nat.card_sigma]

private lemma natDegree_num_div (p q : F[X]) (hq : q ≠ 0) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q)).natDegree =
      (p / gcd p q).natDegree := by
  have hg : gcd p q ≠ 0 := by
    intro hzero
    exact hq ((gcd_eq_zero_iff _ _).mp hzero).2
  have hgdivq : gcd p q ∣ q := gcd_dvd_right _ _
  have hmul :
      gcd p q * (q / gcd p q) = q :=
    EuclideanDomain.mul_div_cancel' hg hgdivq
  have hquotient : q / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hq hmul.symm
  rw [RatFunc.num_div, Polynomial.natDegree_C_mul]
  exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hquotient)

private lemma minusOneQuotient_natDegree [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (minusOneNumerator W / minusOneGCD W).natDegree =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  have hB := minusOneNumerator_ne_zero hchar W hcard
  have hG : minusOneGCD W ≠ 0 := by
    intro hzero
    unfold minusOneGCD at hzero
    exact hB ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivB : minusOneGCD W ∣ minusOneNumerator W := by
    unfold minusOneGCD
    exact gcd_dvd_left _ _
  have hmulB :
      minusOneGCD W * (minusOneNumerator W / minusOneGCD W) =
        minusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivB
  have hquotB : minusOneNumerator W / minusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulB
    exact hB hmulB.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotB
  rw [hmulB, minusOneNumerator_natDegree hchar W hcard] at hdegreeProduct
  have hdegreeG := minusOneGCD_natDegree_add_fiber_sum hchar W hcard
  omega

private lemma num_natDegree_minusOneRat [Fintype F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (hcard : Nat.card F ≠ 3) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (minusOneNumerator W) /
        algebraMap F[X] (RatFunc F) (frobeniusPolynomial : F[X]) ^ 2)).natDegree =
      (∑ x : F, Nat.card (squareFiber W x)) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (frobeniusPolynomial : F[X]) 2]
  rw [natDegree_num_div _ _ (pow_ne_zero 2 frobeniusPolynomial_ne_zero)]
  exact minusOneQuotient_natDegree hchar W hcard

private lemma d_neg_one [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (hcard : Nat.card F ≠ 3) :
    d hchar W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := point_neg_one_eq_some hchar W
  unfold d
  rw [hpoint]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (pZeroX W) (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (pZeroX W) (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY (pZeroX W) (pZeroY W))
            (cubicRat W ^ 2))))).natDegree = _
  rw [paperX_negPZero_add_Q hchar W]
  rw [num_natDegree_minusOneRat hchar W hcard]
  exact (pointCount_eq_fiber_sum W).symm

private def symmetricInput (f g : F[X]) : Fin 3 → F[X] :=
  ![X * f, X * g + f, g]

private def symmetricOutput (W : WeierstrassCurve F) (f g : F[X]) :
    Fin 3 → F[X] :=
  fun i ↦ MvPolynomial.eval (symmetricInput f g) ((W.map C).addSubMap i)

private lemma symmetricOutput_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (f g : F[X]) :
    symmetricOutput W f g 0 =
      (X * f) ^ 2 - C (2 * W.a₄) * (X * f) * g -
        C (4 * W.a₆) * (X * g + f) * g -
          C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [C_ofNat]

private lemma symmetricOutput_one (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (f g : F[X]) :
    symmetricOutput W f g 1 =
      C 2 * (X * g + f) * (X * f) +
        C (4 * W.a₂) * (X * f) * g +
          C (2 * W.a₄) * (X * g + f) * g + C (4 * W.a₆) * g ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [C_ofNat]

private lemma symmetricOutput_two (W : WeierstrassCurve F)
    (f g : F[X]) :
    symmetricOutput W f g 2 = (X * g - f) ^ 2 := by
  simp [symmetricOutput, symmetricInput, WeierstrassCurve.addSubMap]
  ring

private lemma primitive_symmetricOutput (W : WeierstrassCurve F)
    [W.IsElliptic] {f g : F[X]} (hfg : IsCoprime f g)
    (hh : X * g - f ≠ 0) :
    PrimitiveTriple (symmetricOutput W f g 0)
      (symmetricOutput W f g 1) (symmetricOutput W f g 2) := by
  apply primitiveTriple_of_no_common_irreducible
  · rw [symmetricOutput_two]
    exact pow_ne_zero 2 hh
  · intro p hp hp0 hp1 hp2
    have hout : ∀ i : Fin 3, p ∣ symmetricOutput W f g i := by
      intro i
      fin_cases i
      · exact hp0
      · exact hp1
      · exact hp2
    have hinPow (i : Fin 3) : p ∣ symmetricInput f g i ^ 4 := by
      rw [← (W.map C).addSubMapCoeff_condition (symmetricInput f g) i]
      apply Finset.dvd_sum
      intro j _
      exact (hout j).mul_left _
    have hin (i : Fin 3) : p ∣ symmetricInput f g i :=
      hp.prime.dvd_of_dvd_pow (hinPow i)
    have hpg : p ∣ g := by simpa [symmetricInput] using hin 2
    have hpf : p ∣ f := by
      have hdiff := (hin 1).sub (hpg.mul_left X)
      simpa [symmetricInput] using hdiff
    exact hp.not_isUnit (hfg.isUnit_of_dvd' hpf hpg)

private lemma symmetricOutput_zero_natDegree (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] {f g : F[X]} (hf : f ≠ 0)
    (hdegree : g.natDegree < f.natDegree) :
    (symmetricOutput W f g 0).natDegree = 2 * f.natDegree + 2 := by
  let t₁ := C (2 * W.a₄) * (X * f) * g
  let t₂ := C (4 * W.a₆) * (X * g + f) * g
  let t₃ := C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2
  let remainder := t₁ + t₂ + t₃
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hXg : (X * g).natDegree ≤ f.natDegree := by
    calc
      (X * g).natDegree ≤ X.natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ f.natDegree := by rw [Polynomial.natDegree_X]; omega
  have hXgAdd : (X * g + f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_add_le (X * g) f).trans (max_le hXg le_rfl)
  have ht₁ : t₁.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₁]
    calc
      (C (2 * W.a₄) * (X * f) * g).natDegree ≤
          (C (2 * W.a₄) * (X * f)).natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (X * f).natDegree + g.natDegree :=
        Nat.add_le_add_right
          (Polynomial.natDegree_C_mul_le (2 * W.a₄) (X * f)) g.natDegree
      _ ≤ 2 * f.natDegree := by rw [hXf]; omega
  have ht₂ : t₂.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₂]
    calc
      (C (4 * W.a₆) * (X * g + f) * g).natDegree ≤
          (C (4 * W.a₆) * (X * g + f)).natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (X * g + f).natDegree + g.natDegree :=
        Nat.add_le_add_right
          (Polynomial.natDegree_C_mul_le (4 * W.a₆) (X * g + f)) g.natDegree
      _ ≤ 2 * f.natDegree := by omega
  have ht₃ : t₃.natDegree ≤ 2 * f.natDegree := by
    dsimp only [t₃]
    calc
      (C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2).natDegree ≤
          (g ^ 2).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
      _ ≤ 2 * f.natDegree := by omega
  have hremainder : remainder.natDegree ≤ 2 * f.natDegree := by
    dsimp only [remainder]
    exact (Polynomial.natDegree_add_le (t₁ + t₂) t₃).trans
      (max_le
        ((Polynomial.natDegree_add_le t₁ t₂).trans (max_le ht₁ ht₂)) ht₃)
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  rw [symmetricOutput_zero]
  have heq :
      (X * f) ^ 2 - C (2 * W.a₄) * (X * f) * g -
          C (4 * W.a₆) * (X * g + f) * g -
            C (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) * g ^ 2 =
        (X * f) ^ 2 - remainder := by
    dsimp only [remainder, t₁, t₂, t₃]
    ring
  rw [heq]
  calc
    ((X * f) ^ 2 - remainder).natDegree = ((X * f) ^ 2).natDegree := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      rw [hmain]
      omega
    _ = 2 * f.natDegree + 2 := hmain

private def additionCommon (W : WeierstrassCurve F) (r : RatFunc F) : RatFunc F :=
  (RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
    2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)

private def symmetricFirstRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  (RatFunc.X * r - RatFunc.C W.a₄) ^ 2 -
    4 * RatFunc.C W.a₆ * (RatFunc.X + RatFunc.C W.a₂ + r)

private def symmetricSecondRat (W : WeierstrassCurve F)
    (r : RatFunc F) : RatFunc F :=
  2 * additionCommon W r

private def symmetricDenominatorRat (r : RatFunc F) : RatFunc F :=
  (RatFunc.X - r) ^ 2

private lemma addition_product_identity (W : WeierstrassCurve F)
    {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆) :
    (additionCommon W r - 2 * cubicRat W * s) *
        (additionCommon W r + 2 * cubicRat W * s) =
      symmetricDenominatorRat r * symmetricFirstRat W r := by
  have hsquare :
      (cubicRat W * s) ^ 2 =
        cubicRat W *
          (r ^ 3 + RatFunc.C W.a₂ * r ^ 2 +
            RatFunc.C W.a₄ * r + RatFunc.C W.a₆) := by
    calc
      (cubicRat W * s) ^ 2 = cubicRat W * (cubicRat W * s ^ 2) := by ring
      _ = _ := by rw [heq]
  have hproduct := product_formula
    (RatFunc.C W.a₂) (RatFunc.C W.a₄) (RatFunc.C W.a₆)
      RatFunc.X r 1
  rw [cubicRat_eq] at hsquare
  dsimp only at hproduct
  unfold additionCommon symmetricDenominatorRat symmetricFirstRat
  rw [cubicRat_eq W]
  calc
    _ = ((RatFunc.X + r) * (RatFunc.C W.a₄ + RatFunc.X * r) +
          2 * (RatFunc.C W.a₂ * RatFunc.X * r + RatFunc.C W.a₆)) ^ 2 -
        4 * ((RatFunc.X ^ 3 + RatFunc.C W.a₂ * RatFunc.X ^ 2 +
          RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * s) ^ 2 := by ring
    _ = _ := by
      rw [hsquare]
      linear_combination hproduct

private lemma algebraMap_symmetricOutput_zero (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F)
        (symmetricOutput W r.num r.denom 0) =
      algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricFirstRat W r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_zero]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  rw [hr]
  unfold symmetricFirstRat
  ring

private lemma algebraMap_symmetricOutput_one (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F)
        (symmetricOutput W r.num r.denom 1) =
      algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricSecondRat W r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_one]
  simp only [map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C]
  rw [hr]
  unfold symmetricSecondRat additionCommon
  ring

private lemma algebraMap_symmetricOutput_two (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F)
        (symmetricOutput W r.num r.denom 2) =
      algebraMap F[X] (RatFunc F) r.denom ^ 2 * symmetricDenominatorRat r := by
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hr := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  rw [symmetricOutput_two]
  simp only [map_sub, map_mul, map_pow, RatFunc.algebraMap_X]
  rw [hr]
  unfold symmetricDenominatorRat
  ring

private lemma symmetricOutput_zero_ratio (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 0) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      symmetricFirstRat W r / symmetricDenominatorRat r := by
  rw [algebraMap_symmetricOutput_zero, algebraMap_symmetricOutput_two]
  field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)]

private lemma symmetricOutput_one_ratio (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 1) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      symmetricSecondRat W r / symmetricDenominatorRat r := by
  rw [algebraMap_symmetricOutput_one, algebraMap_symmetricOutput_two]
  field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)]

private lemma symmetricOutput_pair_product (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] {r s : RatFunc F}
    (heq : cubicRat W * s ^ 2 =
      r ^ 3 + RatFunc.C W.a₂ * r ^ 2 + RatFunc.C W.a₄ * r +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X - r ≠ 0) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 0) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      (additionCommon W r - 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 *
        ((additionCommon W r + 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2) := by
  rw [symmetricOutput_zero_ratio]
  unfold symmetricDenominatorRat
  have hproduct := addition_product_identity W heq
  unfold symmetricDenominatorRat at hproduct
  field_simp [hdiff]
  linear_combination -hproduct

private lemma symmetricOutput_pair_sum (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] (r s : RatFunc F) (hdiff : RatFunc.X - r ≠ 0) :
    algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 1) /
        algebraMap F[X] (RatFunc F) (symmetricOutput W r.num r.denom 2) =
      (additionCommon W r - 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 +
        (additionCommon W r + 2 * cubicRat W * s) /
          (RatFunc.X - r) ^ 2 := by
  rw [symmetricOutput_one_ratio]
  unfold symmetricSecondRat symmetricDenominatorRat
  field_simp [hdiff]
  unfold additionCommon
  ring

private lemma paperY_negY (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) :
    paperY W ((twist W).toAffine.negY x y) = -paperY W y := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  unfold paperY
  ring

private lemma paperX_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
            (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) -
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  rw [paperX_addX_Q_canceled W hxy hx]
  rfl

private lemma paperX_neg_addX_Q_common (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] {x y : RatFunc F}
    (hxy : (twist W).toAffine.Nonsingular x y)
    (hx : x ≠ cubicRat W * RatFunc.X) :
    paperX W
        ((twist W).toAffine.addX x (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope x (cubicRat W * RatFunc.X)
            ((twist W).toAffine.negY x y) (cubicRat W ^ 2))) =
      (additionCommon W (paperX W x) +
          2 * cubicRat W * paperY W y) /
        (RatFunc.X - paperX W x) ^ 2 := by
  have hneg : (twist W).toAffine.Nonsingular x
      ((twist W).toAffine.negY x y) :=
    ((twist W).toAffine.nonsingular_neg x y).mpr hxy
  rw [paperX_addX_Q_common W hneg hx]
  rw [paperY_negY]
  ring

private def addQX (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) : RatFunc F :=
  (twist W).toAffine.addX x (cubicRat W * RatFunc.X)
    ((twist W).toAffine.slope x (cubicRat W * RatFunc.X) y
      (cubicRat W ^ 2))

private def subQX (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] (x y : RatFunc F) : RatFunc F :=
  (twist W).toAffine.addX x (cubicRat W * RatFunc.X)
    ((twist W).toAffine.slope x (cubicRat W * RatFunc.X)
      ((twist W).toAffine.negY x y) (cubicRat W ^ 2))

private lemma X_sub_paperX_ne_zero (W : WeierstrassCurve F)
    {x : RatFunc F} (hx : x ≠ cubicRat W * RatFunc.X) :
    RatFunc.X - paperX W x ≠ 0 := by
  intro hzero
  apply hx
  have hpaper : paperX W x = RatFunc.X := by
    exact (sub_eq_zero.mp hzero).symm
  unfold paperX at hpaper
  calc
    x = RatFunc.X * cubicRat W :=
      (div_eq_iff (cubicRat_ne_zero W)).mp hpaper
    _ = cubicRat W * RatFunc.X := by ring

private lemma X_mul_denom_sub_num_ne_zero {r : RatFunc F}
    (h : RatFunc.X - r ≠ 0) : X * r.denom - r.num ≠ 0 := by
  intro hzero
  apply h
  have hden := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum := (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  have hmap := congrArg (algebraMap F[X] (RatFunc F)) hzero
  simp only [map_sub, map_mul, map_zero, RatFunc.algebraMap_X] at hmap
  rw [hnum] at hmap
  apply (mul_eq_zero.mp ?_).resolve_right hden
  linear_combination hmap

private lemma ratFunc_ne_zero_of_num_degree_gt {r : RatFunc F}
    (hdegree : r.denom.natDegree < r.num.natDegree) : r ≠ 0 := by
  intro hzero
  rw [hzero] at hdegree
  simp at hdegree

private lemma four_ne_zero_of_ringChar_ne_two (hchar : ringChar F ≠ 2) :
    (4 : F) ≠ 0 := by
  have htwo := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  intro hfour
  have hmul : (2 : F) * 2 = 0 := by
    calc
      (2 : F) * 2 = 4 := by norm_num
      _ = 0 := hfour
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact htwo hzero
  · exact htwo hzero

private lemma Q_y_ne_negY [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    cubicRat W ^ 2 ≠
      (twist W).toAffine.negY (cubicRat W * RatFunc.X) (cubicRat W ^ 2) := by
  simp only [WeierstrassCurve.Affine.negY, twist, zero_mul, sub_zero]
  intro hneg
  have htwoF := two_ne_zero_of_ringChar_ne_two (F := F) hchar
  have htwo : (2 : RatFunc F) ≠ 0 := by
    intro hzero
    apply htwoF
    apply RatFunc.C_injective
    simpa only [map_ofNat, map_zero] using hzero
  have hsum : (2 : RatFunc F) * cubicRat W ^ 2 = 0 := by
    linear_combination hneg
  rcases mul_eq_zero.mp hsum with htwoZero | hcubicZero
  · exact htwo htwoZero
  · exact cubicRat_ne_zero W (sq_eq_zero_iff.mp hcubicZero)

private lemma paperX_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2) (cubicRat W ^ 2))) =
      algebraMap F[X] (RatFunc F) (duplicationNumerator W) /
        (4 * cubicRat W) := by
  have hnum :
      (cubicRat W * RatFunc.X) ^ 4 -
          (twist W).toAffine.b₄ * (cubicRat W * RatFunc.X) ^ 2 -
          2 * (twist W).toAffine.b₆ * (cubicRat W * RatFunc.X) -
          (twist W).toAffine.b₈ =
        cubicRat W ^ 4 *
          algebraMap F[X] (RatFunc F) (duplicationNumerator W) := by
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, twist]
    simp only [duplicationNumerator, map_add, map_sub, map_mul, map_pow,
      map_ofNat, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
    ring
  have hden :
      4 * (cubicRat W * RatFunc.X) ^ 3 +
          (twist W).toAffine.b₂ * (cubicRat W * RatFunc.X) ^ 2 +
          2 * (twist W).toAffine.b₄ * (cubicRat W * RatFunc.X) +
          (twist W).toAffine.b₆ =
        4 * cubicRat W ^ 4 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, twist]
    rw [cubicRat_eq W]
    ring
  have hfourRat : (4 : RatFunc F) ≠ 0 := by
    intro hzero
    apply four_ne_zero_of_ringChar_ne_two (F := F) hchar
    apply RatFunc.C_injective
    simpa only [map_ofNat, map_zero] using hzero
  rw [(twist W).toAffine.addX_self_of_Y_ne (q_equation W)
    (Q_y_ne_negY hchar W)]
  rw [hnum, hden]
  unfold paperX
  field_simp [cubicRat_ne_zero W, hfourRat]

private lemma duplicationNumerator_natDegree (W : WeierstrassCurve F) :
    (duplicationNumerator W).natDegree = 4 := by
  unfold duplicationNumerator
  compute_degree <;> norm_num

private lemma natDegree_num_div_of_isCoprime (p q : F[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hcop : IsCoprime p q) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p /
        algebraMap F[X] (RatFunc F) q)).natDegree = p.natDegree := by
  rw [natDegree_num_div p q hq]
  have hgUnit : IsUnit (gcd p q) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg : gcd p q ≠ 0 := hgUnit.ne_zero
  have hmul : gcd p q * (p / gcd p q) = p :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hquot : p / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hp hmul.symm
  have hdegree := Polynomial.natDegree_mul hg hquot
  rw [hmul, Polynomial.natDegree_eq_zero_of_isUnit hgUnit, zero_add] at hdegree
  exact hdegree.symm

private lemma num_natDegree_doubleQ [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (duplicationNumerator W) /
        (4 * cubicRat W))).natDegree = 4 := by
  have hfour := four_ne_zero_of_ringChar_ne_two (F := F) hchar
  have hCfour : C (4 : F) ≠ 0 := Polynomial.C_ne_zero.mpr hfour
  have hden : C (4 : F) * cubic W ≠ 0 :=
    mul_ne_zero hCfour (cubic_ne_zero W)
  have hcopFour : IsCoprime (duplicationNumerator W) (C (4 : F)) := by
    refine ⟨0, C (4 : F)⁻¹, ?_⟩
    rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hfour, C_1]
  have hcop :
      IsCoprime (duplicationNumerator W) (C (4 : F) * cubic W) :=
    hcopFour.mul_right (isCoprime_cubic_duplicationNumerator W).symm
  have hmapDen :
      (4 : RatFunc F) * cubicRat W =
        algebraMap F[X] (RatFunc F) (C (4 : F) * cubic W) := by
    rw [map_mul, RatFunc.algebraMap_C]
    change (4 : RatFunc F) * cubicRat W = RatFunc.C (4 : F) * cubicRat W
    congr 1
    simp only [map_ofNat]
  rw [hmapDen]
  rw [natDegree_num_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := duplicationNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    hden hcop]
  exact duplicationNumerator_natDegree W

private lemma d_eq_one_of_point_eq_Q [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = Q W) : d hchar W n = 1 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  change (RatFunc.num (paperX W (cubicRat W * RatFunc.X))).natDegree = 1
  rw [paperX_Q_coordinate]
  change
    (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma d_eq_one_of_point_eq_neg_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = -Q W) : d hchar W n = 1 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num (paperX W (cubicRat W * RatFunc.X))).natDegree = 1
  rw [paperX_Q_coordinate]
  change
    (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma d_eq_four_of_point_eq_two_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = Q W + Q W) : d hchar W n = 4 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (Q_y_ne_negY hchar W)]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2)
            (cubicRat W ^ 2))))).natDegree = 4
  rw [paperX_doubleQ hchar W, num_natDegree_doubleQ hchar W]

private lemma d_eq_four_of_point_eq_neg_two_Q [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} (hn : point hchar W n = -(Q W + Q W)) :
    d hchar W n = 4 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  unfold d
  rw [hn]
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (Q_y_ne_negY hchar W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      (paperX W
        ((twist W).toAffine.addX (cubicRat W * RatFunc.X)
          (cubicRat W * RatFunc.X)
          ((twist W).toAffine.slope (cubicRat W * RatFunc.X)
            (cubicRat W * RatFunc.X) (cubicRat W ^ 2)
            (cubicRat W ^ 2))))).natDegree = 4
  rw [paperX_doubleQ hchar W, num_natDegree_doubleQ hchar W]

private lemma point_sub_one [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] (n : ℤ) :
    point hchar W (n - 1) = point hchar W n - Q W := by
  have hstep := point_add_one hchar W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

private lemma generic_neighbor_degree_identity (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (twist W).toAffine.Nonsingular x y}
    {hMinus : (twist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (twist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ cubicRat W * RatFunc.X)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (twist W).toAffine.Point) + Q W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (twist W).toAffine.Point) - Q W)
    (hdegree : (paperX W x).denom.natDegree <
      (paperX W x).num.natDegree)
    (hdegreeMinus : (paperX W xMinus).denom.natDegree <
      (paperX W xMinus).num.natDegree)
    (hdegreePlus : (paperX W xPlus).denom.natDegree <
      (paperX W xPlus).num.natDegree) :
    (paperX W xMinus).num.natDegree +
        (paperX W xPlus).num.natDegree =
      2 * (paperX W x).num.natDegree + 2 := by
  have hQ : (twist W).toAffine.Nonsingular
      (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (q_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus = addQX W x y := by
    exact hplusEq.1
  have hneg : (twist W).toAffine.Nonsingular x
      ((twist W).toAffine.negY x y) :=
    ((twist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (twist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (twist W).toAffine.Point) - Q W =
    -(-(.some x y hxy : (twist W).toAffine.Point) + Q W) by abel] at hminusEq
  rw [show Q W = .some (cubicRat W * RatFunc.X) (cubicRat W ^ 2) hQ from rfl]
    at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus = subQX W x y := by
    exact hminusEq.1
  have hrPlus :
      paperX W xPlus =
        (additionCommon W (paperX W x) -
            2 * cubicRat W * paperY W y) /
          (RatFunc.X - paperX W x) ^ 2 := by
    rw [hxPlus]
    exact paperX_addX_Q_common W hxy hxQ
  have hrMinus :
      paperX W xMinus =
        (additionCommon W (paperX W x) +
            2 * cubicRat W * paperY W y) /
          (RatFunc.X - paperX W x) ^ 2 := by
    rw [hxMinus]
    exact paperX_neg_addX_Q_common W hxy hxQ
  have heq := paper_coordinates_equation W hxy
  have hdiff := X_sub_paperX_ne_zero W hxQ
  have hprod := symmetricOutput_pair_product W heq hdiff
  have hsum := symmetricOutput_pair_sum W (paperX W x) (paperY W y) hdiff
  rw [← hrPlus, ← hrMinus] at hprod hsum
  have hprod' :
      algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 0) /
        algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 2) =
        paperX W xMinus * paperX W xPlus := by
    simpa only [mul_comm] using hprod
  have hsum' :
      algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 1) /
        algebraMap F[X] (RatFunc F)
          (symmetricOutput W (paperX W x).num (paperX W x).denom 2) =
        paperX W xMinus + paperX W xPlus := by
    simpa only [add_comm] using hsum
  have hpoly : X * (paperX W x).denom - (paperX W x).num ≠ 0 :=
    X_mul_denom_sub_num_ne_zero hdiff
  have hprimitive := primitive_symmetricOutput W
    (RatFunc.isCoprime_num_denom (paperX W x)) hpoly
  have hout2 :
      symmetricOutput W (paperX W x).num (paperX W x).denom 2 ≠ 0 := by
    rw [symmetricOutput_two]
    exact pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout2
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod' hsum'
  have hcenter := symmetricOutput_zero_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma d_recurrence [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (n : ℤ) :
    d hchar W (n - 1) + d hchar W (n + 1) = 2 * d hchar W n + 2 := by
  cases hn : point hchar W n with
  | zero =>
      have hplus := point_add_one hchar W n
      have hminus := point_sub_one hchar W n
      rw [hn] at hplus hminus
      have hplusQ : point hchar W (n + 1) = Q W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : point hchar W (n - 1) = -Q W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := d_eq_one_of_point_eq_Q hchar W hplusQ
      have hdMinus := d_eq_one_of_point_eq_neg_Q hchar W hminusQ
      have hd : d hchar W n = 0 := by simp [d, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : point hchar W (n - 1) with
      | zero =>
          have hsub := point_sub_one hchar W n
          rw [hn, hminusPoint] at hsub
          have hnQ : point hchar W n = Q W := by
            have hxyQ :
                (.some x y hxy : (twist W).toAffine.Point) = Q W :=
              sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := point_add_one hchar W n
          rw [hnQ] at hplus
          have hd := d_eq_one_of_point_eq_Q hchar W hnQ
          have hdPlus := d_eq_four_of_point_eq_two_Q hchar W hplus
          have hdMinus : d hchar W (n - 1) = 0 := by
            simp [d, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : point hchar W (n + 1) with
          | zero =>
              have hadd := point_add_one hchar W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : point hchar W n = -Q W := by
                have htranslated := congrArg
                  (fun P : (twist W).toAffine.Point ↦ P - Q W) hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (twist W).toAffine.Point) = -Q W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := point_sub_one hchar W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  point hchar W (n - 1) = -(Q W + Q W) := by
                calc
                  point hchar W (n - 1) = -Q W - Q W := hminus
                  _ = -(Q W + Q W) := by abel
              have hd := d_eq_one_of_point_eq_neg_Q hchar W hnNegQ
              have hdMinus :=
                d_eq_four_of_point_eq_neg_two_Q hchar W hminusNegTwo
              have hdPlus : d hchar W (n + 1) = 0 := by
                simp [d, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := point_add_one hchar W n
              have hminus := point_sub_one hchar W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (twist W).toAffine.Point) ≠ Q W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (twist W).toAffine.Point) ≠ -Q W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (twist W).toAffine.Nonsingular
                  (cubicRat W * RatFunc.X) (cubicRat W ^ 2) :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (q_equation W)
              have hxQ : x ≠ cubicRat W * RatFunc.X := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show Q W = .some (cubicRat W * RatFunc.X)
                    (cubicRat W ^ 2) hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show Q W = .some (cubicRat W * RatFunc.X)
                    (cubicRat W ^ 2) hQ from rfl]
                  exact heq
              have hdegree :=
                num_natDegree_gt_denom_natDegree hchar W hn
              have hdegreeMinus :=
                num_natDegree_gt_denom_natDegree
                  hchar W hminusPoint
              have hdegreePlus :=
                num_natDegree_gt_denom_natDegree
                  hchar W hplusPoint
              have hgeneric := generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [d, hn, hminusPoint, hplusPoint, paperX] using hgeneric

private lemma ringChar_ne_two (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic] : ringChar F ≠ 2 := by
  intro hchar
  let _ : CharP F 2 := ringChar.of_eq hchar
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h16 : (16 : F) = 0 := by
    calc
      (16 : F) = (2 : F) * 8 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h64 : (64 : F) = 0 := by
    calc
      (64 : F) = (2 : F) * 32 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h288 : (288 : F) = 0 := by
    calc
      (288 : F) = (2 : F) * 144 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have h432 : (432 : F) = 0 := by
    calc
      (432 : F) = (2 : F) * 216 := by norm_num
      _ = 0 := by rw [htwo, zero_mul]
  have hdelta : W.Δ = 0 := by
    rw [WeierstrassCurve.Δ_of_isCharNeTwoNF, h16, h64, h288, h432]
    ring
  rw [← W.coe_Δ'] at hdelta
  exact Units.ne_zero W.Δ' hdelta

private lemma degreeDataAtThree_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 7) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 3 N) := by
  let a : ℤ := 4 - N
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hpos
  have hNle : (N : ℤ) ≤ 7 := by exact_mod_cast hle
  have hdisc : a ^ 2 ≤ 9 := by
    dsimp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNpos) (sub_nonneg.mpr hNle)]
  refine ⟨MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic
    3 N a (by simp [a]) ?_ ?_⟩
  · intro n
    norm_num
    nlinarith [sq_nonneg (2 * n + a)]
  · intro n hn _
    norm_num at hn
    nlinarith [sq_nonneg (2 * n + a)]

/-- Over the three-element field, the elementary two-points-per-fiber bound supplies Manin degree
data for every Weierstrass equation. -/
theorem manin_degree_data_of_card_eq_three [Finite F] (hF : Nat.card F = 3)
    (W : WeierstrassCurve F) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtThree_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

/-- Manin's numerator-degree sequence in odd characteristic has the initial values, recurrence,
and zero separation needed for the Hasse bound. -/
theorem manin_degree_data_of_isCharNeTwoNF [Finite F]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  by_cases hF : Nat.card F = 3
  · exact manin_degree_data_of_card_eq_three hF W
  · exact ⟨{
      d := d (ringChar_ne_two W) W
      zero := d_zero (ringChar_ne_two W) W
      negOne := d_neg_one (ringChar_ne_two W) W hF
      recurrence := d_recurrence (ringChar_ne_two W) W
      noAdjacentZeros := noAdjacentZeros (ringChar_ne_two W) W }⟩

/-- Hasse's bound for an elliptic Weierstrass equation in odd-characteristic normal form. -/
theorem hasse_bound_of_isCharNeTwoNF [Finite F]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) :=
  (Classical.choice (manin_degree_data_of_isCharNeTwoNF W)).hasse_bound

end

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

end
/- ===== end MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean ===== -/

/- ===== begin MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean (atlas-lean @ 805f71dcbadd) ===== -/
section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

/-
# Manin's elementary proof in characteristic two

This file packages the ordinary and supersingular normal-form cases, following
Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).
-/

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

noncomputable section

open Polynomial
open scoped CharTwo
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

universe u

variable {F : Type u} [Field F]

private lemma ratFunc_ne_zero_of_num_degree_gt {r : RatFunc F}
    (hdegree : r.denom.natDegree < r.num.natDegree) : r ≠ 0 := by
  intro hzero
  rw [hzero] at hdegree
  simp at hdegree

private lemma intDegree_pow {x : RatFunc F} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

private lemma intDegree_pow_le_zero {x : RatFunc F} (hx : x.intDegree ≤ 0)
    (n : ℕ) : (x ^ n).intDegree ≤ 0 := by
  by_cases hx0 : x = 0
  · cases n <;> simp [hx0]
  rw [intDegree_pow hx0]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hx

private lemma intDegree_add_le_of_le {x y : RatFunc F} {m : ℤ}
    (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m) :
    (x + y).intDegree ≤ m := by
  by_cases hxy : x + y = 0
  · simp [hxy, hm]
  by_cases hy0 : y = 0
  · simpa [hy0] using hx
  exact (RatFunc.intDegree_add_le hy0 hxy).trans (max_le hx hy)

private lemma intDegree_mul_le_of_le {x y : RatFunc F} {m n : ℤ}
    (hmn : 0 ≤ m + n) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ n) :
    (x * y).intDegree ≤ m + n := by
  by_cases hx0 : x = 0
  · simp [hx0, hmn]
  by_cases hy0 : y = 0
  · simp [hy0, hmn]
  rw [RatFunc.intDegree_mul hx0 hy0]
  exact add_le_add hx hy

private lemma intDegree_add_eq_left_of_lt {x y : RatFunc F}
    (hx0 : x ≠ 0) (hdegree : y.intDegree < x.intDegree) :
    (x + y).intDegree = x.intDegree := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hsum0 : x + y ≠ 0 := by
    intro hzero
    have hxy : x = -y := by linear_combination hzero
    have hdegrees := congrArg RatFunc.intDegree hxy
    rw [RatFunc.intDegree_neg] at hdegrees
    omega
  apply le_antisymm
  · exact (RatFunc.intDegree_add_le hy0 hsum0).trans
      (max_le le_rfl hdegree.le)
  · have hneg : -y ≠ 0 := neg_ne_zero.mpr hy0
    have hrecover : (x + y) + -y = x := by ring
    have hrecover0 : (x + y) + -y ≠ 0 := by rw [hrecover]; exact hx0
    have hbound := RatFunc.intDegree_add_le hneg hrecover0
    rw [hrecover, RatFunc.intDegree_neg] at hbound
    by_contra hnot
    have hlt : (x + y).intDegree < x.intDegree := lt_of_not_ge hnot
    omega

private def quadraticDegree (q : ℕ) (a n : ℤ) : ℤ :=
  n ^ 2 + a * n + q

private def nonnegativeQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ))
    (hnonneg : ∀ n, 0 ≤ quadraticDegree q a n)
    (hnoAdjacent : ∀ n, quadraticDegree q a n = 0 →
      quadraticDegree q a (n + 1) = 0 → False) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic q N a ha
    (by simpa only [quadraticDegree] using hnonneg)
    (by simpa only [quadraticDegree] using hnoAdjacent)

private def positiveQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ)) (hpos : ∀ n, 0 < quadraticDegree q a n) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  nonnegativeQuadraticDegreeData q N a ha (fun n ↦ (hpos n).le)
    (fun n hn _ ↦ by nlinarith [hpos n])

private lemma degreeDataAtTwo_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 5) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 2 N) := by
  have hcases : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨positiveQuadraticDegreeData 2 1 2 (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (n + 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 2 1 (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (2 * n + 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 3 0 (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg n])⟩
  · exact ⟨positiveQuadraticDegreeData 2 4 (-1) (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (2 * n - 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 5 (-2) (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (n - 1)])⟩

private lemma degreeDataAtFour_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 9) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 4 N) := by
  let a : ℤ := 5 - N
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hpos
  have hNle : (N : ℤ) ≤ 9 := by exact_mod_cast hle
  have hdisc : a ^ 2 ≤ 16 := by
    dsimp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNpos) (sub_nonneg.mpr hNle)]
  refine ⟨nonnegativeQuadraticDegreeData 4 N a (by simp [a]) ?_ ?_⟩
  · intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg (2 * n + a)]
  · intro n hn hn1
    norm_num [quadraticDegree] at hn hn1
    nlinarith [sq_nonneg (2 * n + a)]

/-- Over the two-element field, the elementary cardinality bound already supplies Manin degree
data for every Weierstrass equation. -/
theorem manin_degree_data_of_card_eq_two [Finite F] (hF : Nat.card F = 2)
    (W : WeierstrassCurve F) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtTwo_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

/-- Over the four-element field, the elementary two-points-per-fiber bound supplies Manin degree
data for every Weierstrass equation. -/
theorem manin_degree_data_of_card_eq_four [Finite F] (hF : Nat.card F = 4)
    (W : WeierstrassCurve F) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtFour_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

private def frobeniusTail (h k : F[X]) : ℕ → F[X]
  | 0 => 0
  | e + 1 => frobeniusTail h k e ^ 2 + k ^ (2 ^ (e + 1) - 2) * h

private lemma frobeniusTail_identity [CharP F 2] (h k : F[X]) (e : ℕ) :
    frobeniusTail h k e ^ 2 + k ^ (2 ^ e) * frobeniusTail h k e =
      h ^ (2 ^ e) + k ^ (2 * (2 ^ e - 1)) * h := by
  induction e with
  | zero => simp [frobeniusTail, CharTwo.add_self_eq_zero]
  | succ e ih =>
      let q := 2 ^ e
      have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
      have hqpos : 0 < q := by simp [q]
      have hsq := congrArg (fun p : F[X] ↦ p ^ 2) ih
      rw [CharTwo.add_sq, CharTwo.add_sq, mul_pow, mul_pow] at hsq
      have hB4 : (frobeniusTail h k e ^ 2) ^ 2 = frobeniusTail h k e ^ 4 := by
        ring
      have hk2q : (k ^ (2 ^ e)) ^ 2 = k ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
      have hh2q : (h ^ (2 ^ e)) ^ 2 = h ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
      have hk4q : (k ^ (2 * (2 ^ e - 1))) ^ 2 = k ^ (4 * q - 4) := by
        rw [← pow_mul]
        congr 1
        dsimp [q]
        omega
      rw [hB4, hk2q, hh2q, hk4q] at hsq
      have hsq' :
          frobeniusTail h k e ^ 4 + k ^ (2 * q) * frobeniusTail h k e ^ 2 =
            h ^ (2 * q) + k ^ (4 * q - 4) * h ^ 2 := hsq
      rw [frobeniusTail, hq, CharTwo.add_sq]
      rw [show (k ^ (2 * q - 2) * h) ^ 2 =
        k ^ (4 * q - 4) * h ^ 2 by
          rw [mul_pow, ← pow_mul]
          congr 2
          omega]
      rw [mul_add]
      rw [show k ^ (2 * q) * (k ^ (2 * q - 2) * h) =
        k ^ (4 * q - 2) * h by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega]
      rw [show h ^ (2 * q) = (h ^ q) ^ 2 by
        rw [← pow_mul]
        congr 1
        omega]
      rw [show k ^ (2 * (2 * q - 1)) = k ^ (4 * q - 2) by
        congr 1
        omega]
      have hcancel :
          k ^ (4 * q - 4) * h ^ 2 + k ^ (4 * q - 4) * h ^ 2 = 0 :=
        CharTwo.add_self_eq_zero _
      linear_combination hsq' + hcancel

private def charTwoExponent [Finite F] : ℕ := Nat.log 2 (Nat.card F)

private lemma card_eq_two_pow [Finite F] [CharP F 2] :
    Nat.card F = 2 ^ charTwoExponent (F := F) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  obtain ⟨e, _, he⟩ := @FiniteField.card F _ fintypeF 2 _
  unfold charTwoExponent
  rw [@Nat.card_eq_fintype_card F fintypeF, he, Nat.log_pow (by norm_num)]

private def charTwoFiber (b c : F) :=
  {y : F // y ^ 2 + b * y = c}

private instance charTwoFiberFinite [Finite F] (b c : F) :
    Finite (charTwoFiber b c) := by
  unfold charTwoFiber
  infer_instance

private lemma charTwoFiber_card_eq_one [Finite F] [CharP F 2] (c : F) :
    Nat.card (charTwoFiber 0 c) = 1 := by
  have hsquareInjective : Function.Injective (fun y : F ↦ y ^ 2) := by
    intro y z hyz
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hyz) with hyz | hyz
    · exact hyz
    · simpa only [CharTwo.neg_eq] using hyz
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hsquareInjective c
  let _ : Nonempty (charTwoFiber 0 c) := ⟨⟨r, by simpa using hr⟩⟩
  let _ : Subsingleton (charTwoFiber 0 c) := ⟨by
    intro y z
    apply Subtype.ext
    apply hsquareInjective
    simpa using y.property.trans z.property.symm⟩
  exact Nat.card_unique

private lemma charTwoFiber_card_eq_two [Finite F] [CharP F 2]
    {b c r : F} (hb : b ≠ 0) (hr : r ^ 2 + b * r = c) :
    Nat.card (charTwoFiber b c) = 2 := by
  classical
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hrb : (r + b) ^ 2 + b * (r + b) = c := by
    linear_combination hr + (r * b + b ^ 2) * htwo
  have hbr : r + b ≠ r := by
    intro h
    apply hb
    linear_combination h
  let e : charTwoFiber b c ≃ Bool :=
    { toFun := fun y ↦ if y.1 = r then true else false
      invFun := fun value ↦ match value with
        | true => ⟨r, hr⟩
        | false => ⟨r + b, hrb⟩
      left_inv := by
        intro y
        have hfactor : (y.1 + r) * (y.1 + r + b) = 0 := by
          linear_combination y.property + hr + (y.1 * r + c) * htwo
        have hy : y.1 = r ∨ y.1 = r + b := by
          rcases mul_eq_zero.mp hfactor with h | h
          · left
            simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
          · right
            have hyr : y.1 + r = b := by
              simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
            calc
              y.1 = (y.1 + r) + r := by
                rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
              _ = b + r := by rw [hyr]
              _ = r + b := add_comm _ _
        apply Subtype.ext
        rcases hy with hy | hy
        · simp [hy]
        · simp [hy, hbr]
      right_inv := by
        intro value
        cases value <;> simp [hbr] }
  simpa using Nat.card_congr e

private lemma charTwoFiber_card_eq_zero [Finite F] (b c : F)
    (hempty : ¬∃ y, y ^ 2 + b * y = c) :
    Nat.card (charTwoFiber b c) = 0 := by
  let _ : IsEmpty (charTwoFiber b c) := ⟨fun y ↦ hempty ⟨y.1, y.property⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private lemma charTwoFiber_card_le_two [Finite F] [CharP F 2]
    (b c : F) : Nat.card (charTwoFiber b c) ≤ 2 := by
  by_cases hb : b = 0
  · subst b
    rw [charTwoFiber_card_eq_one]
    omega
  by_cases hexists : ∃ y, y ^ 2 + b * y = c
  · obtain ⟨r, hr⟩ := hexists
    rw [charTwoFiber_card_eq_two hb hr]
  · rw [charTwoFiber_card_eq_zero b c hexists]
    omega

private def frobeniusValue (c b : F) : ℕ → F
  | 0 => 0
  | e + 1 => frobeniusValue c b e ^ 2 + b ^ (2 ^ (e + 1) - 2) * c

private lemma eval_frobeniusTail (h k : F[X]) (x : F) (e : ℕ) :
    (frobeniusTail h k e).eval x =
      frobeniusValue (h.eval x) (k.eval x) e := by
  induction e with
  | zero => simp [frobeniusTail, frobeniusValue]
  | succ e ih => simp [frobeniusTail, frobeniusValue, ih]

private lemma frobenius_pow_eq_linear_add_value [CharP F 2]
    {b c y : F} (hy : y ^ 2 + b * y = c) (e : ℕ) :
    y ^ (2 ^ e) = b ^ (2 ^ e - 1) * y + frobeniusValue c b e := by
  induction e with
  | zero => simp [frobeniusValue]
  | succ e ih =>
      let q := 2 ^ e
      have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
      have hqpos : 0 < q := by simp [q]
      have hy' : y ^ 2 = b * y + c := by
        calc
          y ^ 2 = c - b * y := eq_sub_of_add_eq hy
          _ = c + b * y := by
            simp only [sub_eq_add_neg, CharTwo.neg_eq]
          _ = b * y + c := add_comm _ _
      have hbpow : (b ^ (q - 1)) ^ 2 = b ^ (2 * q - 2) := by
        rw [← pow_mul]
        congr 1
        omega
      have hbnext : b ^ (2 * q - 2) * (b * y) = b ^ (2 * q - 1) * y := by
        calc
          b ^ (2 * q - 2) * (b * y) =
              (b ^ (2 * q - 2) * b) * y := by ring
          _ = b ^ (2 * q - 2 + 1) * y := by rw [pow_succ]
          _ = b ^ (2 * q - 1) * y := by congr 2; omega
      rw [hq]
      calc
        y ^ (2 * q) = (y ^ q) ^ 2 := by
          rw [← pow_mul]
          congr 1
          omega
        _ = (b ^ (q - 1) * y + frobeniusValue c b e) ^ 2 := by
          rw [show q = 2 ^ e by rfl, ih]
        _ = b ^ (2 * q - 2) * y ^ 2 + frobeniusValue c b e ^ 2 := by
          rw [CharTwo.add_sq, mul_pow, hbpow]
        _ = b ^ (2 * q - 2) * (b * y + c) +
              frobeniusValue c b e ^ 2 := by rw [hy']
        _ = b ^ (2 * q - 1) * y +
              (frobeniusValue c b e ^ 2 + b ^ (2 * q - 2) * c) := by
          rw [mul_add, hbnext]
          ring
        _ = b ^ (2 * q - 1) * y + frobeniusValue c b (e + 1) := by
          rw [frobeniusValue, hq]

private lemma frobeniusValue_eq_zero_of_mem_fiber [Finite F] [CharP F 2]
    {b c y : F} (hb : b ≠ 0) (hy : y ^ 2 + b * y = c) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hyq : y ^ Nat.card F = y := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card y
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have h := frobenius_pow_eq_linear_add_value hy
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hyq, hbq1, one_mul] at h
  have hzero : (0 : F) = frobeniusValue c b (charTwoExponent (F := F)) :=
    add_left_cancel (by simpa only [add_zero] using h)
  exact hzero.symm

private lemma frobeniusValue_eq_zero_or_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 ∨
      frobeniusValue c b (charTwoExponent (F := F)) = b := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq : b ^ Nat.card F = b := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card b
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hcq : c ^ Nat.card F = c := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card c
  have htail := congrArg (Polynomial.eval (0 : F))
    (frobeniusTail_identity (C c) (C b) (charTwoExponent (F := F)))
  simp only [eval_add, eval_mul, eval_pow, eval_C] at htail
  rw [eval_frobeniusTail, eval_C, eval_C,
    ← card_eq_two_pow (F := F), hbq, hcq] at htail
  rw [show b ^ (2 * (Nat.card F - 1)) = 1 by
    rw [mul_comm, pow_mul, hbq1, one_pow], one_mul] at htail
  rw [CharTwo.add_self_eq_zero] at htail
  have hfactor :
      frobeniusValue c b (charTwoExponent (F := F)) *
        (frobeniusValue c b (charTwoExponent (F := F)) + b) = 0 := by
    calc
      _ = frobeniusValue c b (charTwoExponent (F := F)) ^ 2 +
          b * frobeniusValue c b (charTwoExponent (F := F)) := by ring
      _ = 0 := htail
  rcases mul_eq_zero.mp hfactor with hzero | heq
  · exact Or.inl hzero
  · exact Or.inr (by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left heq)

private def charTwoQuadratic (b c : F) : F[X] :=
  X ^ 2 + C b * X + C c

private def frobeniusQuotient (b c : F) : ℕ → F[X]
  | 0 => 0
  | e + 1 =>
      charTwoQuadratic b c * frobeniusQuotient b c e ^ 2 +
        C (b ^ (2 ^ (e + 1) - 2))

private lemma frobenius_polynomial_mod_quadratic [CharP F 2]
    (b c : F) (e : ℕ) :
    X ^ (2 ^ e) + C (b ^ (2 ^ e - 1)) * X + C (frobeniusValue c b e) =
      charTwoQuadratic b c * frobeniusQuotient b c e := by
  induction e with
  | zero => simp [frobeniusValue, frobeniusQuotient,
      CharTwo.add_self_eq_zero]
  | succ e ih =>
      let q := 2 ^ e
      have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
      have hqpos : 0 < q := by simp [q]
      have hbpow : (b ^ (q - 1)) ^ 2 = b ^ (2 * q - 2) := by
        rw [← pow_mul]
        congr 1
        omega
      have hbnext : b ^ (2 * q - 2) * b = b ^ (2 * q - 1) := by
        calc
          b ^ (2 * q - 2) * b = b ^ (2 * q - 2 + 1) := (pow_succ _ _).symm
          _ = b ^ (2 * q - 1) := by congr 1; omega
      rw [frobeniusValue, frobeniusQuotient, hq]
      rw [show X ^ (2 * q) = (X ^ q) ^ 2 by
        rw [← pow_mul]
        congr 1
        omega]
      rw [show C (b ^ (2 * q - 1)) * X =
        C (b ^ (2 * q - 2)) * (C b * X) by
          calc
            C (b ^ (2 * q - 1)) * X =
                C (b ^ (2 * q - 2) * b) * X := by rw [hbnext]
            _ = (C (b ^ (2 * q - 2)) * C b) * X := by rw [map_mul]
            _ = C (b ^ (2 * q - 2)) * (C b * X) := by ring]
      rw [show C (frobeniusValue c b e ^ 2 + b ^ (2 * q - 2) * c) =
        C (frobeniusValue c b e) ^ 2 +
          C (b ^ (2 * q - 2)) * C c by simp]
      rw [show C (b ^ (2 * q - 2)) = C (b ^ (q - 1)) ^ 2 by
        rw [← map_pow, hbpow]]
      calc
        (X ^ q) ^ 2 + C (b ^ (q - 1)) ^ 2 * (C b * X) +
              (C (frobeniusValue c b e) ^ 2 +
                C (b ^ (q - 1)) ^ 2 * C c) =
            (X ^ q + C (b ^ (q - 1)) * X +
              C (frobeniusValue c b e)) ^ 2 +
                C (b ^ (q - 1)) ^ 2 * charTwoQuadratic b c := by
          rw [CharTwo.add_sq, CharTwo.add_sq]
          unfold charTwoQuadratic
          have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
          linear_combination
            -(X ^ 2 * C (b ^ (q - 1)) ^ 2) * htwo
        _ = (charTwoQuadratic b c * frobeniusQuotient b c e) ^ 2 +
              C (b ^ (q - 1)) ^ 2 * charTwoQuadratic b c := by
          rw [show X ^ q + C (b ^ (q - 1)) * X +
            C (frobeniusValue c b e) =
              charTwoQuadratic b c * frobeniusQuotient b c e by
                simpa only [q] using ih]
        _ = charTwoQuadratic b c *
              (charTwoQuadratic b c * frobeniusQuotient b c e ^ 2 +
                C (b ^ (q - 1)) ^ 2) := by ring

private def charTwoFrobeniusPolynomial [Finite F] : F[X] :=
  X ^ Nat.card F - X

private lemma eval_charTwoFrobeniusPolynomial [Finite F] (x : F) :
    (charTwoFrobeniusPolynomial : F[X]).eval x = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  unfold charTwoFrobeniusPolynomial
  rw [eval_sub, eval_pow, eval_X, @Nat.card_eq_fintype_card F fintypeF,
    FiniteField.pow_card, sub_self]

private lemma charTwoFrobeniusPolynomial_ne_zero [Finite F] :
    (charTwoFrobeniusPolynomial : F[X]) ≠ 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hdegree := FiniteField.X_pow_card_sub_X_natDegree_eq F
    (@Fintype.one_lt_card F fintypeF _)
  intro hzero
  unfold charTwoFrobeniusPolynomial at hzero
  rw [@Nat.card_eq_fintype_card F fintypeF] at hzero
  rw [hzero] at hdegree
  simp only [natDegree_zero] at hdegree
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  omega

private lemma charTwoFrobeniusPolynomial_splits [Finite F] :
    (charTwoFrobeniusPolynomial : F[X]).Splits := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [Polynomial.splits_iff_card_roots]
  unfold charTwoFrobeniusPolynomial
  rw [@Nat.card_eq_fintype_card F fintypeF,
    FiniteField.roots_X_pow_card_sub_X,
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  simp

private lemma exists_mem_charTwoFiber_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    ∃ y, y ^ 2 + b * y = c := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hmod := frobenius_polynomial_mod_quadratic b c
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hbq1, hvalue] at hmod
  simp only [map_one, one_mul, map_zero, add_zero] at hmod
  have hmod' :
      charTwoFrobeniusPolynomial =
        charTwoQuadratic b c *
          frobeniusQuotient b c (charTwoExponent (F := F)) := by
    unfold charTwoFrobeniusPolynomial
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using hmod
  have hdiv : charTwoQuadratic b c ∣
      (charTwoFrobeniusPolynomial : F[X]) :=
    ⟨frobeniusQuotient b c (charTwoExponent (F := F)), hmod'⟩
  have hsplit : (charTwoQuadratic b c).Splits :=
    charTwoFrobeniusPolynomial_splits.of_dvd
      charTwoFrobeniusPolynomial_ne_zero hdiv
  have hnatDegree : (charTwoQuadratic b c).natDegree = 2 := by
    exact (Polynomial.isMonicOfDegree_add_add_two b c).natDegree_eq
  have hdegree : (charTwoQuadratic b c).degree ≠ 0 := by
    apply Polynomial.degree_ne_of_natDegree_ne
    rw [hnatDegree]
    norm_num
  obtain ⟨y, hy⟩ := hsplit.exists_eval_eq_zero hdegree
  refine ⟨y, ?_⟩
  unfold charTwoQuadratic at hy
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy
  have hy' : y ^ 2 + b * y = -c := eq_neg_of_add_eq_zero_left hy
  simpa only [CharTwo.neg_eq] using hy'

private lemma charTwoFiber_card_eq_two_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    Nat.card (charTwoFiber b c) = 2 := by
  obtain ⟨y, hy⟩ := exists_mem_charTwoFiber_of_value_eq_zero hb hvalue
  exact charTwoFiber_card_eq_two hb hy

private lemma charTwoFiber_card_eq_zero_of_value_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = b) :
    Nat.card (charTwoFiber b c) = 0 := by
  apply charTwoFiber_card_eq_zero
  rintro ⟨y, hy⟩
  have hzero := frobeniusValue_eq_zero_of_mem_fiber hb hy
  exact hb (hvalue ▸ hzero)

private def ordinaryH (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₂ * X ^ 2 + C W.a₆

private def ordinaryU [Finite F] (W : WeierstrassCurve F) : F[X] :=
  X * frobeniusTail (ordinaryH W) X (charTwoExponent (F := F))

private lemma ordinaryH_pow_card [Finite F] (W : WeierstrassCurve F) :
    ordinaryH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₂ * X ^ (2 * Nat.card F) + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.expand_card F _ fintypeF]
  simp only [ordinaryH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma ordinaryU_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryU W ^ 2 + X ^ (Nat.card F + 1) * ordinaryU W =
      X ^ 2 * ordinaryH W ^ Nat.card F + X ^ (2 * Nat.card F) * ordinaryH W := by
  have htail := frobeniusTail_identity (ordinaryH W) X
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  have hterm :
      X ^ 2 * (X ^ (2 * (Nat.card F - 1)) * ordinaryH W) =
        X ^ (2 * Nat.card F) * ordinaryH W := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  unfold ordinaryU
  calc
    (X * frobeniusTail (ordinaryH W) X charTwoExponent) ^ 2 +
        X ^ (Nat.card F + 1) *
          (X * frobeniusTail (ordinaryH W) X charTwoExponent) =
      X ^ 2 * (frobeniusTail (ordinaryH W) X charTwoExponent ^ 2 +
        X ^ Nat.card F * frobeniusTail (ordinaryH W) X charTwoExponent) := by
          ring
    _ = X ^ 2 * (ordinaryH W ^ Nat.card F +
        X ^ (2 * (Nat.card F - 1)) * ordinaryH W) := by rw [htail]
    _ = _ := by rw [mul_add, hterm]

private def ordinaryTwist (W : WeierstrassCurve F) :
    WeierstrassCurve (RatFunc F) :=
  ⟨RatFunc.X, RatFunc.X ^ 3 + RatFunc.C W.a₆, 0, 0,
    RatFunc.C W.a₆ * RatFunc.X ^ 6⟩

private lemma ordinaryTwist_discriminant [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryTwist W).Δ = RatFunc.C W.a₆ * RatFunc.X ^ 12 := by
  simp only [ordinaryTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero, zero_add, sub_zero, CharTwo.neg_eq]
  ring_nf

private instance [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJNeZeroNF] : (ordinaryTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, ordinaryTwist_discriminant,
    isUnit_iff_ne_zero]
  apply mul_ne_zero
  · have hb : W.a₆ ≠ 0 := by
      have h := W.Δ'.ne_zero
      rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
      exact h
    intro hC
    apply hb
    apply RatFunc.C_injective
    simpa using hC
  · exact pow_ne_zero 12 RatFunc.X_ne_zero

private lemma ordinaryQ_equation [CharP F 2] (W : WeierstrassCurve F) :
    (ordinaryTwist W).toAffine.Equation (RatFunc.X ^ 3) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ordinaryTwist]
  ring_nf
  rw [CharTwo.two_eq_zero]
  simp

private def ordinaryQ [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJNeZeroNF] : (ordinaryTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (ordinaryQ_equation W)

private def ordinaryPZeroX [Finite F] : RatFunc F :=
  RatFunc.X ^ (Nat.card F + 2)

private def ordinaryPZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (X ^ 2 * ordinaryU W)

private lemma ordinary_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (X ^ 2 * ordinaryU W) ^ 2 +
        X * X ^ (Nat.card F + 2) * (X ^ 2 * ordinaryU W) =
      (X ^ (Nat.card F + 2)) ^ 3 +
        (X ^ 3 + C W.a₆) * (X ^ (Nat.card F + 2)) ^ 2 +
        C W.a₆ * X ^ 6 := by
  have hu := ordinaryU_identity W
  have hh := ordinaryH_pow_card W
  rw [hh] at hu
  unfold ordinaryH at hu
  have hcancel :
      C W.a₂ * X ^ (2 * Nat.card F + 6) +
        C W.a₂ * X ^ (2 * Nat.card F + 6) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination X ^ 4 * hu + hcancel

private lemma ordinaryPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryTwist W).toAffine.Equation (ordinaryPZeroX (F := F))
      (ordinaryPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (ordinary_pZero_polynomial_equation W)
  simpa only [ordinaryTwist, ordinaryPZeroX, ordinaryPZeroY, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

private def ordinaryPZero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (ordinaryPZero_equation W)

private local instance : DecidableEq F := Classical.decEq F

private def ordinaryPoint [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    (ordinaryTwist W).toAffine.Point := ordinaryPZero W + n • ordinaryQ W

private lemma ordinaryPoint_add_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    ordinaryPoint W (n + 1) = ordinaryPoint W n + ordinaryQ W := by
  rw [ordinaryPoint, ordinaryPoint, add_one_zsmul]
  abel

private def ordinaryPaperX (x : RatFunc F) : RatFunc F := x / RatFunc.X ^ 2

private def ordinaryPaperY (y : RatFunc F) : RatFunc F := y / RatFunc.X ^ 3

private def ordinaryBadAtInfinity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryTwist W).toAffine.Point → Prop
  | 0 => False
  | .some x _ _ => (ordinaryPaperX x).intDegree ≤ 0

private lemma ordinary_paper_coordinates_equation [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y) :
    ordinaryPaperY y ^ 2 + ordinaryPaperX x * ordinaryPaperY y =
      ordinaryPaperX x ^ 3 +
        (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * ordinaryPaperX x ^ 2 +
          RatFunc.C W.a₆ := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [ordinaryTwist] at heq
  unfold ordinaryPaperX ordinaryPaperY
  field_simp [RatFunc.X_ne_zero]
  linear_combination heq

private lemma intDegree_C_div_X_sq_le_zero (b : F) :
    (RatFunc.C b / RatFunc.X ^ 2).intDegree ≤ 0 := by
  by_cases hb : b = 0
  · simp [hb]
  have hCb : RatFunc.C b ≠ 0 := by
    intro hzero
    apply hb
    apply RatFunc.C_injective
    simpa using hzero
  rw [RatFunc.intDegree_div hCb (pow_ne_zero 2 RatFunc.X_ne_zero)]
  rw [intDegree_pow RatFunc.X_ne_zero]
  simp

private lemma ordinary_coefficient_intDegree_le_one (W : WeierstrassCurve F) :
    (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2).intDegree ≤ 1 := by
  exact intDegree_add_le_of_le (m := 1) (by norm_num) (by simp)
    ((intDegree_C_div_X_sq_le_zero W.a₆).trans (by norm_num))

private lemma ordinaryPaperY_intDegree_le_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y)
    (hx : (ordinaryPaperX x).intDegree ≤ 0) :
    (ordinaryPaperY y).intDegree ≤ 0 := by
  let r := ordinaryPaperX x
  let s := ordinaryPaperY y
  by_contra hsnot
  have hspos : 0 < s.intDegree := lt_of_not_ge hsnot
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hspos
    simp at hspos
  have hs2 : (s ^ 2).intDegree = 2 * s.intDegree := by
    rw [intDegree_pow hs0]
    norm_num
  have hrs : (r * s).intDegree ≤ s.intDegree := by
    simpa using intDegree_mul_le_of_le (x := r) (y := s)
      (m := 0) (n := s.intDegree) (by simpa using hspos.le) hx le_rfl
  have hlhs : (s ^ 2 + r * s).intDegree = 2 * s.intDegree := by
    rw [intDegree_add_eq_left_of_lt (pow_ne_zero 2 hs0), hs2]
    omega
  have hr3 : (r ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
  have hr2 : (r ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hx 2
  have hmiddle :
      ((RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2).intDegree ≤ 1 :=
    intDegree_mul_le_of_le (m := 1) (n := 0) (by norm_num)
      (ordinary_coefficient_intDegree_le_one W) hr2
  have hrhs :
      (r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆).intDegree ≤ 1 := by
    have hfirst := intDegree_add_le_of_le (m := 1) (by norm_num)
      (hr3.trans (by norm_num)) hmiddle
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hfirst (by simp)
  have heq := ordinary_paper_coordinates_equation W hxy
  change s ^ 2 + r * s =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆ at heq
  have hlhsLe : (s ^ 2 + r * s).intDegree ≤ 1 := by rw [heq]; exact hrhs
  rw [hlhs] at hlhsLe
  omega

private lemma ordinaryPaperX_addX_Q_eq [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hx : x ≠ RatFunc.X ^ 3) :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0)) =
      (ordinaryPaperY y /
          (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, ordinaryTwist, sub_zero]
  unfold ordinaryPaperX ordinaryPaperY
  field_simp [RatFunc.X_ne_zero, hx]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  linear_combination RatFunc.X ^ 3 * (x + RatFunc.X ^ 3) ^ 2 * htwo

private lemma ordinaryPaperX_addX_Q_intDegree_le_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y)
    (hxQ : x ≠ RatFunc.X ^ 3)
    (hx : (ordinaryPaperX x).intDegree ≤ 0) :
    (ordinaryPaperX
      ((ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0))).intDegree ≤ 0 := by
  let r := ordinaryPaperX x
  let s := ordinaryPaperY y
  change r.intDegree ≤ 0 at hx
  have hs : s.intDegree ≤ 0 := ordinaryPaperY_intDegree_le_zero W hxy hx
  have hdiff : r - RatFunc.X ≠ 0 := by
    intro hzero
    have hr : r = RatFunc.X := sub_eq_zero.mp hzero
    apply hxQ
    unfold r ordinaryPaperX at hr
    calc
      x = RatFunc.X * RatFunc.X ^ 2 :=
        (div_eq_iff (pow_ne_zero 2 RatFunc.X_ne_zero)).mp hr
      _ = RatFunc.X ^ 3 := by ring
  have hdiffDegree : (r - RatFunc.X).intDegree = 1 := by
    rw [show r - RatFunc.X = -RatFunc.X + r by ring]
    rw [intDegree_add_eq_left_of_lt (neg_ne_zero.mpr RatFunc.X_ne_zero)]
    · simp
    · rw [RatFunc.intDegree_neg]
      norm_num
      omega
  have hslope : (s / (r - RatFunc.X)).intDegree ≤ 0 := by
    by_cases hs0 : s = 0
    · simp [hs0]
    rw [RatFunc.intDegree_div hs0 hdiff, hdiffDegree]
    omega
  have hslope2 : ((s / (r - RatFunc.X)) ^ 2).intDegree ≤ 0 :=
    intDegree_pow_le_zero hslope 2
  rw [ordinaryPaperX_addX_Q_eq W hxQ]
  change ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
    RatFunc.C W.a₆ / RatFunc.X ^ 2 + r).intDegree ≤ 0
  have hfirst := intDegree_add_le_of_le (m := 0) (by norm_num) hslope2 hslope
  have hsecond := intDegree_add_le_of_le (m := 0) (by norm_num) hfirst
    (intDegree_C_div_X_sq_le_zero W.a₆)
  exact intDegree_add_le_of_le (m := 0) (by norm_num) hsecond hx

private lemma ordinaryPaperX_Q_coordinate :
    ordinaryPaperX (RatFunc.X ^ 3 : RatFunc F) = RatFunc.X := by
  unfold ordinaryPaperX
  field_simp [RatFunc.X_ne_zero]

private lemma ordinaryBadAtInfinity_neg [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (P : (ordinaryTwist W).toAffine.Point) :
    ordinaryBadAtInfinity W (-P) ↔ ordinaryBadAtInfinity W P := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      rw [WeierstrassCurve.Affine.Point.neg_some]
      rfl

private lemma ordinaryBadAtInfinity_add_Q [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {P : (ordinaryTwist W).toAffine.Point}
    (hP : ordinaryBadAtInfinity W P) :
    ordinaryBadAtInfinity W (P + ordinaryQ W) := by
  cases P with
  | zero => simp [ordinaryBadAtInfinity] at hP
  | some x y hxy =>
      change (ordinaryPaperX x).intDegree ≤ 0 at hP
      have hx : x ≠ RatFunc.X ^ 3 := by
        intro hx
        have hpaper : ordinaryPaperX x = RatFunc.X := by
          rw [hx, ordinaryPaperX_Q_coordinate]
        rw [hpaper] at hP
        norm_num at hP
      have hvertical :
          ¬(x = RatFunc.X ^ 3 ∧
            y = (ordinaryTwist W).toAffine.negY (RatFunc.X ^ 3) 0) :=
        fun h ↦ hx h.1
      rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 _ from rfl]
      rw [WeierstrassCurve.Affine.Point.add_some hvertical]
      exact ordinaryPaperX_addX_Q_intDegree_le_zero W hxy hx hP

private lemma ordinaryBadAtInfinity_sub_Q [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {P : (ordinaryTwist W).toAffine.Point}
    (hP : ordinaryBadAtInfinity W P) :
    ordinaryBadAtInfinity W (P - ordinaryQ W) := by
  have hnegP : ordinaryBadAtInfinity W (-P) :=
    (ordinaryBadAtInfinity_neg W P).mpr hP
  have hadd := ordinaryBadAtInfinity_add_Q W hnegP
  rw [show P - ordinaryQ W = -(-P + ordinaryQ W) by abel]
  exact (ordinaryBadAtInfinity_neg W (-P + ordinaryQ W)).mpr hadd

private lemma ordinaryBadAtInfinity_add_Q_iff [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (P : (ordinaryTwist W).toAffine.Point) :
    ordinaryBadAtInfinity W (P + ordinaryQ W) ↔ ordinaryBadAtInfinity W P := by
  refine ⟨fun h ↦ ?_, ordinaryBadAtInfinity_add_Q W⟩
  have hsub := ordinaryBadAtInfinity_sub_Q W h
  simpa using hsub

private lemma ordinaryPaperX_pZeroX [Finite F] :
    ordinaryPaperX (ordinaryPZeroX (F := F)) = RatFunc.X ^ Nat.card F := by
  unfold ordinaryPaperX ordinaryPZeroX
  rw [show Nat.card F + 2 = 2 + Nat.card F by omega, pow_add]
  field_simp [RatFunc.X_ne_zero]

private lemma ordinaryPZero_not_badAtInfinity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ¬ordinaryBadAtInfinity W (ordinaryPZero W) := by
  intro hbad
  change (ordinaryPaperX (ordinaryPZeroX (F := F))).intDegree ≤ 0 at hbad
  rw [ordinaryPaperX_pZeroX, intDegree_pow RatFunc.X_ne_zero] at hbad
  simp only [RatFunc.intDegree_X, mul_one] at hbad
  have hcard : (0 : ℤ) < Nat.card F := by exact_mod_cast Nat.card_pos
  omega

private lemma ordinaryPoint_not_badAtInfinity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    ¬ordinaryBadAtInfinity W (ordinaryPoint W n) := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa [ordinaryPoint] using ordinaryPZero_not_badAtInfinity W
  · intro k _ hk hbad
    apply hk
    apply (ordinaryBadAtInfinity_add_Q_iff W (ordinaryPoint W k)).mp
    rw [← ordinaryPoint_add_one W k]
    exact hbad
  · intro k _ hk hbad
    apply hk
    have hstep := ordinaryPoint_add_one W (k - 1)
    rw [show k - 1 + 1 = k by ring] at hstep
    rw [hstep]
    exact (ordinaryBadAtInfinity_add_Q_iff W (ordinaryPoint W (k - 1))).mpr hbad

private def ordinaryD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (n : ℤ) : ℕ :=
  match ordinaryPoint W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num (ordinaryPaperX x)).natDegree

private lemma ordinaryQ_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryQ W ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

private lemma ordinaryD_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryD W 0 = Nat.card F := by
  rw [ordinaryD, ordinaryPoint]
  simp only [zero_zsmul, add_zero, ordinaryPZero,
    WeierstrassCurve.Affine.Point.mk]
  have hx : ordinaryPaperX (ordinaryPZeroX (F := F)) =
      RatFunc.X ^ Nat.card F := by
    unfold ordinaryPaperX ordinaryPZeroX
    rw [show Nat.card F + 2 = 2 + Nat.card F by omega, pow_add]
    field_simp [RatFunc.X_ne_zero]
  rw [hx]
  change (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
    Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

private lemma ordinary_num_degree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} {x y : RatFunc F}
    {hxy : (ordinaryTwist W).toAffine.Nonsingular x y}
    (hn : ordinaryPoint W n = .some x y hxy) :
    (RatFunc.denom (ordinaryPaperX x)).natDegree <
      (RatFunc.num (ordinaryPaperX x)).natDegree := by
  have hnotBad := ordinaryPoint_not_badAtInfinity W n
  have hnotLe : ¬(ordinaryPaperX x).intDegree ≤ 0 := by
    intro hdegree
    apply hnotBad
    rw [hn]
    exact hdegree
  have hpos : 0 < (ordinaryPaperX x).intDegree := lt_of_not_ge hnotLe
  unfold RatFunc.intDegree at hpos
  omega

private lemma ordinaryD_eq_zero_iff [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (n : ℤ) :
    ordinaryD W n = 0 ↔ ordinaryPoint W n = 0 := by
  cases hp : ordinaryPoint W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [ordinaryD, hp]
  | some x y hxy =>
      have hdeg := ordinary_num_degree W hp
      constructor
      · intro hd
        simp only [ordinaryD, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

private lemma ordinaryNoAdjacentZeros [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    : ∀ n, ordinaryD W n = 0 → ordinaryD W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (ordinaryD_eq_zero_iff W n).mp hn
  have hp1 := (ordinaryD_eq_zero_iff W (n + 1)).mp hn1
  apply ordinaryQ_ne_zero W
  have hs := ordinaryPoint_add_one W n
  rw [hp, hp1] at hs
  simpa using hs.symm

private def ordinaryMinusOneNumerator [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W

private lemma ordinaryH_derivative [CharP F 2] (W : WeierstrassCurve F) :
    (ordinaryH W).derivative = X ^ 2 := by
  unfold ordinaryH
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : ((3 : ℕ) : F) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, htwo,
      Nat.cast_one, zero_add]
  rw [htwo, hthree, map_zero, map_one]
  norm_num

private lemma derivative_frobeniusTail_ordinary [CharP F 2]
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (ordinaryH W) X e).derivative = X ^ (2 ^ e) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [frobeniusTail]
  have hexponent : 2 ^ (e + 1) - 2 = 2 * (2 ^ e - 1) := by
    rw [pow_succ]
    omega
  rw [hexponent, show X ^ (2 * (2 ^ e - 1)) =
    (X ^ (2 ^ e - 1)) ^ 2 by
      rw [← pow_mul]
      congr 1
      omega]
  rw [derivative_add, derivative_pow, derivative_mul, derivative_pow,
    ordinaryH_derivative]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  rw [htwo, map_zero]
  norm_num
  rw [← pow_mul, ← pow_add]
  congr 1
  rw [pow_succ]
  have hpowpos : 0 < 2 ^ e := pow_pos (by norm_num) e
  omega

private lemma ordinaryU_derivative [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).derivative =
      frobeniusTail (ordinaryH W) X (charTwoExponent (F := F)) +
        X ^ (Nat.card F + 1) := by
  have hexponent : 0 < charTwoExponent (F := F) := by
    have hcard : 1 < Nat.card F := Finite.one_lt_card
    rw [card_eq_two_pow (F := F)] at hcard
    exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard
  unfold ordinaryU
  rw [derivative_mul, derivative_X,
    derivative_frobeniusTail_ordinary W _ hexponent]
  rw [← card_eq_two_pow (F := F)]
  simp only [one_mul]
  rw [mul_comm, ← pow_succ]

private lemma ordinaryH_natDegree (W : WeierstrassCurve F) :
    (ordinaryH W).natDegree = 3 := by
  unfold ordinaryH
  compute_degree <;> norm_num

private lemma frobeniusTail_ordinary_natDegree
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (ordinaryH W) X e).natDegree = 3 * 2 ^ (e - 1) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusTail, ordinaryH_natDegree]
  | more e ih ih1 =>
      rw [frobeniusTail]
      have htail : frobeniusTail (ordinaryH W) X (e + 1) ≠ 0 := by
        intro hzero
        have hdegree := ih1 (by omega)
        rw [hzero] at hdegree
        simp at hdegree
      have hxpow : X ^ (2 ^ (e + 2) - 2) ≠ (0 : F[X]) :=
        pow_ne_zero _ X_ne_zero
      have hH : ordinaryH W ≠ 0 := by
        intro hzero
        have hdegree := ordinaryH_natDegree W
        rw [hzero] at hdegree
        simp at hdegree
      rw [natDegree_add_eq_left_of_natDegree_lt]
      · rw [natDegree_pow, ih1 (by omega)]
        simp [pow_succ]
        ring
      · rw [natDegree_mul hxpow hH, natDegree_pow, natDegree_X,
          ordinaryH_natDegree, natDegree_pow, ih1 (by omega)]
        norm_num
        have hpow : 2 ≤ 2 ^ (e + 1) := by
          rw [pow_succ]
          have hpos : 0 < 2 ^ e := pow_pos (by norm_num) e
          omega
        rw [pow_succ]
        omega

private lemma charTwoExponent_pos [Finite F] [CharP F 2] :
    0 < charTwoExponent (F := F) := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  rw [card_eq_two_pow (F := F)] at hcard
  exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard

private lemma ordinaryU_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).natDegree =
      1 + 3 * 2 ^ (charTwoExponent (F := F) - 1) := by
  unfold ordinaryU
  have htailDegree := frobeniusTail_ordinary_natDegree W
    (charTwoExponent (F := F)) (charTwoExponent_pos (F := F))
  have htail : frobeniusTail (ordinaryH W) X
      (charTwoExponent (F := F)) ≠ 0 := by
    intro hzero
    rw [hzero] at htailDegree
    simp at htailDegree
  rw [natDegree_mul X_ne_zero htail, natDegree_X, htailDegree]

private lemma ordinaryMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk]
    rw [pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hU : (ordinaryU W).natDegree ≤ 2 * Nat.card F := by
    rw [ordinaryU_natDegree W]
    change 1 + 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    dsimp only [remainder]
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have hfirst : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    have hsecond : (X ^ (Nat.card F + 1) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hfirst hsecond)) hU)
  have heq : ordinaryMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold ordinaryMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

private lemma eval_ordinaryU [Finite F] (W : WeierstrassCurve F) (x : F) :
    (ordinaryU W).eval x =
      x * frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
  simp only [ordinaryU, eval_mul, eval_X, eval_frobeniusTail]

private lemma eval_ordinaryMinusOneNumerator [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F) :
    (ordinaryMinusOneNumerator W).eval x =
      x ^ 2 + x * frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q1 : x ^ (2 * Nat.card F + 1) = x ^ 3 := by
    calc
      x ^ (2 * Nat.card F + 1) = x ^ (2 * Nat.card F) * x := pow_succ _ _
      _ = (x ^ Nat.card F) ^ 2 * x := by
        rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul]
      _ = x ^ 3 := by rw [hxq]; ring
  have hxq2 : x ^ (Nat.card F + 2) = x ^ 3 := by
    rw [pow_add, hxq]
    ring
  have hxq1 : x ^ (Nat.card F + 1) = x ^ 2 := by
    rw [pow_add, hxq]
    ring
  simp only [ordinaryMinusOneNumerator, eval_add, eval_pow, eval_X,
    eval_ordinaryU, hx2q1, hxq2, hxq1]
  have hcancel : x ^ 3 + x ^ 3 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hcancel

private lemma eval_derivative_ordinaryMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) (x : F) :
    (ordinaryMinusOneNumerator W).derivative.eval x =
      x + frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hqcast : ((Nat.card F : ℕ) : F) = 0 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact Nat.cast_card_eq_zero F
  have hcoeff1 : (((2 * Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hcoeff2 : (((Nat.card F + 2 : ℕ) : F)) = 0 := by
    push_cast
    rw [hqcast, zero_add]
    exact CharTwo.two_eq_zero
  have hcoeff3 : (((Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have hxq1 : x ^ (Nat.card F + 1) = x ^ 2 := by
    rw [pow_add, hxq]
    ring
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  have hexponent3 : Nat.card F + 1 - 1 = Nat.card F := by omega
  unfold ordinaryMinusOneNumerator
  simp only [derivative_add, derivative_pow, derivative_X,
    ordinaryU_derivative, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    eval_one, eval_frobeniusTail, hcoeff1, hcoeff2, hcoeff3, one_mul,
    zero_mul, hexponent1, hexponent3, hx2q, hxq, hxq1]
  have hcancel : x ^ 2 + x ^ 2 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hcancel

private lemma frobeniusValue_zero_coefficient (c : F) (e : ℕ) (he : 0 < e) :
    frobeniusValue c 0 e = c ^ (2 ^ (e - 1)) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusValue]
  | more e ih ih1 =>
      rw [frobeniusValue, ih1 (by omega)]
      have hexponent : 0 < 2 ^ (e + 2) - 2 := by
        have hpowpos : 0 < 2 ^ e := pow_pos (by norm_num) e
        rw [show e + 2 = (e + 1) + 1 by omega, pow_succ, pow_succ]
        omega
      rw [zero_pow (Nat.ne_of_gt hexponent), zero_mul, add_zero, ← pow_mul]
      congr 1

private lemma ordinary_a₆_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    W.a₆ ≠ 0 := by
  have h := W.Δ'.ne_zero
  rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact h

private lemma ordinaryTailValue_zero_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    frobeniusValue ((ordinaryH W).eval 0) 0
      (charTwoExponent (F := F)) ≠ 0 := by
  rw [frobeniusValue_zero_coefficient _ _ (charTwoExponent_pos (F := F))]
  simp only [ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C,
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_add]
  exact pow_ne_zero _ (ordinary_a₆_ne_zero W)

private lemma ordinaryEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 + x * y = (ordinaryH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₃_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₄_of_isCharTwoJNeZeroNF, one_mul, zero_mul,
    add_zero, ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

private def affineSolutionsEquivOrdinaryFibers [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, charTwoFiber x ((ordinaryH W).eval x) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (ordinaryEquation_iff_fiber W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (ordinaryEquation_iff_fiber W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma ordinaryPointCount_eq_fiber_sum [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] [W.IsElliptic] :
    Nat.card W.toAffine.Point =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivOrdinaryFibers W), Nat.card_sigma]

private lemma ordinaryMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : ordinaryMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := ordinaryMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

private lemma rootMultiplicity_ordinaryNumerator_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) = 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot 0 := by
    change (ordinaryMinusOneNumerator W).eval 0 = 0
    rw [eval_ordinaryMinusOneNumerator]
    simp
  have hpositive : 0 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
    (Polynomial.rootMultiplicity_pos hN).mpr hroot
  have hnotTwo : ¬1 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) := by
    intro htwo
    have hderivativeRoot :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mp htwo |>.2
    have hderivative := eval_derivative_ordinaryMinusOneNumerator W 0
    rw [show (ordinaryMinusOneNumerator W).derivative.eval 0 = 0 from
      hderivativeRoot] at hderivative
    simp only [zero_add] at hderivative
    exact ordinaryTailValue_zero_ne_zero W hderivative.symm
  omega

private lemma rootMultiplicity_ordinaryNumerator_eq_zero [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) (x : F) (hx : x ≠ 0)
    (hvalue : frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) = 0) :
    Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heval := eval_ordinaryMinusOneNumerator W x
  rw [hvalue, mul_zero, add_zero] at heval
  exact (pow_ne_zero 2 hx) (heval.symm.trans hroot)

private lemma ordinaryNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F)
    (hvalue : frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) = x) :
    (X - C x) ^ 2 ∣ ordinaryMinusOneNumerator W := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot x := by
    change (ordinaryMinusOneNumerator W).eval x = 0
    rw [eval_ordinaryMinusOneNumerator, hvalue]
    simpa only [pow_two] using CharTwo.add_self_eq_zero (x * x)
  have hderivativeRoot : (ordinaryMinusOneNumerator W).derivative.IsRoot x := by
    change (ordinaryMinusOneNumerator W).derivative.eval x = 0
    rw [eval_derivative_ordinaryMinusOneNumerator, hvalue]
    exact CharTwo.add_self_eq_zero x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

private lemma count_roots_charTwoFrobeniusPolynomial [Finite F] (x : F) :
    Multiset.count x (charTwoFrobeniusPolynomial : F[X]).roots = 1 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  unfold charTwoFrobeniusPolynomial
  rw [@Nat.card_eq_fintype_card F fintypeF,
    FiniteField.roots_X_pow_card_sub_X]
  simp

private lemma count_roots_charTwoFrobeniusPolynomial_sq [Finite F] (x : F) :
    Multiset.count x ((charTwoFrobeniusPolynomial : F[X]) ^ 2).roots = 2 := by
  rw [Polynomial.roots_pow, Multiset.count_nsmul,
    count_roots_charTwoFrobeniusPolynomial]

private def ordinaryMinusOneGCD [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  gcd (ordinaryMinusOneNumerator W) (charTwoFrobeniusPolynomial ^ 2)

private lemma count_roots_ordinaryMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (x : F) :
    Multiset.count x (ordinaryMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hx : x = 0
  · subst x
    have hlinearN : X - C 0 ∣ ordinaryMinusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (ordinaryMinusOneNumerator W).eval 0 = 0
      rw [eval_ordinaryMinusOneNumerator]
      simp
    have hlinearL' : X - C 0 ∣
        (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
      hlinearL.trans ⟨charTwoFrobeniusPolynomial, by ring⟩
    have hcommon : X - C 0 ∣ ordinaryMinusOneGCD W := by
      unfold ordinaryMinusOneGCD
      exact dvd_gcd hlinearN hlinearL'
    have hlower : 1 ≤
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper :
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤
            Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN 0
        _ = 1 := rootMultiplicity_ordinaryNumerator_zero W
    have hroot : Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot, charTwoFiber_card_eq_one]
  · rcases frobeniusValue_eq_zero_or_eq
        (c := (ordinaryH W).eval x) hx with hvalue | hvalue
    · have hupper :
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
          _ = 0 := rootMultiplicity_ordinaryNumerator_eq_zero W x hx hvalue
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_two_of_value_eq_zero hx hvalue]
    · have hcommon : (X - C x) ^ 2 ∣ ordinaryMinusOneGCD W := by
        unfold ordinaryMinusOneGCD
        exact dvd_gcd (ordinaryNumerator_sq_dvd_of_value_eq W x hvalue)
          hlinearLsq
      have hlower : 2 ≤
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL : Polynomial.rootMultiplicity x
          ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_charTwoFrobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 2 :=
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x
                ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_zero_of_value_eq hx hvalue]

private lemma ordinaryMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (ordinaryMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots) =
        (ordinaryMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (ordinaryMinusOneGCD W).roots) (by simp))
  calc
    (ordinaryMinusOneGCD W).natDegree =
        (ordinaryMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_ordinaryMinusOneGCD W x

private lemma ordinaryMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x)) =
      2 * Nat.card F := by
  rw [ordinaryMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) +
        Nat.card (charTwoFiber x ((ordinaryH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two x _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma charTwo_natDegree_num_div (p q : F[X]) (hq : q ≠ 0) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p /
        algebraMap F[X] (RatFunc F) q)).natDegree =
      (p / gcd p q).natDegree := by
  have hg : gcd p q ≠ 0 := by
    intro hzero
    exact hq ((gcd_eq_zero_iff _ _).mp hzero).2
  have hgdivq : gcd p q ∣ q := gcd_dvd_right _ _
  have hmul : gcd p q * (q / gcd p q) = q :=
    EuclideanDomain.mul_div_cancel' hg hgdivq
  have hquotient : q / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hq hmul.symm
  rw [RatFunc.num_div, Polynomial.natDegree_C_mul]
  exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hquotient)

private lemma ordinaryMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : ordinaryMinusOneGCD W *
      (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W) =
        ordinaryMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, ordinaryMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := ordinaryMinusOneGCD_natDegree_add_fiber_sum W
  omega

private lemma num_natDegree_ordinaryMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact ordinaryMinusOneQuotient_natDegree W

private lemma ordinaryPZeroX_ne_QX [Finite F] :
    ordinaryPZeroX (F := F) ≠ RatFunc.X ^ 3 := by
  intro heq
  have hdegree := congrArg RatFunc.intDegree heq
  simp only [ordinaryPZeroX] at hdegree
  rw [intDegree_pow RatFunc.X_ne_zero,
    intDegree_pow RatFunc.X_ne_zero] at hdegree
  simp only [RatFunc.intDegree_X, mul_one] at hdegree
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  omega

private lemma ordinaryPaperY_neg_pZeroY [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryPaperY
        ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
          (ordinaryPZeroY W)) =
      algebraMap F[X] (RatFunc F) (ordinaryU W) / RatFunc.X +
        RatFunc.X ^ Nat.card F := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist,
    ordinaryPZeroX, ordinaryPZeroY, sub_eq_add_neg, CharTwo.neg_eq]
  unfold ordinaryPaperY
  rw [map_mul, map_pow, RatFunc.algebraMap_X]
  field_simp [RatFunc.X_ne_zero]
  ring

private lemma algebraMap_charTwoFrobeniusPolynomial [Finite F] [CharP F 2] :
    algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial =
      RatFunc.X ^ Nat.card F + RatFunc.X := by
  simp only [charTwoFrobeniusPolynomial, sub_eq_add_neg, CharTwo.neg_eq,
    map_add, map_pow, RatFunc.algebraMap_X]

private lemma ordinaryPaperX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) =
      algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [ordinaryPaperX_addX_Q_eq W ordinaryPZeroX_ne_QX]
  rw [ordinaryPaperX_pZeroX, ordinaryPaperY_neg_pZeroY W]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [ordinaryMinusOneNumerator, map_add, map_pow,
    RatFunc.algebraMap_X, sub_eq_add_neg, CharTwo.neg_eq]
  let q := Nat.card F
  let t : RatFunc F := RatFunc.X
  let r := t ^ q
  let u := algebraMap F[X] (RatFunc F) (ordinaryU W)
  let a := RatFunc.C W.a₂
  let b := RatFunc.C W.a₆
  let s := u / t + r
  let L := r + t
  let n := t ^ (2 * q + 1) + t ^ (q + 2) + t ^ (q + 1) + u
  change (s / L) ^ 2 + s / L + b / t ^ 2 + r = n / L ^ 2
  have ht : t ≠ 0 := RatFunc.X_ne_zero
  have hL : L ≠ 0 := by
    dsimp only [L, r, t, q]
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hu := congrArg (algebraMap F[X] (RatFunc F)) (ordinaryU_identity W)
  rw [ordinaryH_pow_card W] at hu
  simp only [ordinaryH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hu
  change u ^ 2 + t ^ (q + 1) * u =
    t ^ 2 * (t ^ (3 * q) + a * t ^ (2 * q) + b) +
      t ^ (2 * q) * (t ^ 3 + a * t ^ 2 + b) at hu
  have htq1 : t ^ (q + 1) = t * r := by
    dsimp only [r]
    rw [pow_succ]
    ring
  have ht2q : t ^ (2 * q) = r ^ 2 := by
    dsimp only [r]
    calc
      t ^ (2 * q) = t ^ (q * 2) := by congr 1; omega
      _ = (t ^ q) ^ 2 := pow_mul t q 2
  have ht3q : t ^ (3 * q) = r ^ 3 := by
    dsimp only [r]
    calc
      t ^ (3 * q) = t ^ (q * 3) := by congr 1; omega
      _ = (t ^ q) ^ 3 := pow_mul t q 3
  rw [htq1, ht2q, ht3q] at hu
  have hu' : u ^ 2 + t * r * u =
      t ^ 2 * r ^ 3 + b * t ^ 2 + t ^ 3 * r ^ 2 + b * r ^ 2 := by
    have hcancel : a * t ^ 2 * r ^ 2 + a * t ^ 2 * r ^ 2 = 0 :=
      CharTwo.add_self_eq_zero _
    linear_combination hu + hcancel
  dsimp only [s, n]
  field_simp [ht, hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hu' +
    (u * t * t ^ q + t * t ^ q * b + t ^ 2 * t ^ (q * 2) +
      t ^ 2 * t ^ (q * 3) + t ^ 2 * b + t ^ 3 * t ^ (q * 2) +
        t ^ (q * 2) * b) * htwo

private lemma ordinaryPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ∃ y hxy, ordinaryPoint W (-1) =
      .some
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) y hxy := by
  have hp : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryPZero_equation W)
  have hneg : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F))
      ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
        (ordinaryPZeroY W)) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -ordinaryPZero W = .some (ordinaryPZeroX (F := F))
        ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
          (ordinaryPZeroY W)) hneg := by
    rw [show ordinaryPZero W =
      .some (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) ordinaryPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryQ_equation W))
  rw [← hnegP, ← show ordinaryQ W = .some (RatFunc.X ^ 3) 0 _ from rfl]
    at hadd
  have hpoint : ordinaryPoint W (-1) =
      -(-ordinaryPZero W + ordinaryQ W) := by
    unfold ordinaryPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private lemma ordinaryD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := ordinaryPoint_neg_one_eq_some W
  unfold ordinaryD
  rw [hpoint]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)))).natDegree = _
  rw [ordinaryPaperX_negPZero_add_Q W]
  rw [num_natDegree_ordinaryMinusOneRat W]
  exact (ordinaryPointCount_eq_fiber_sum W).symm

private lemma ordinary_product_formula {R : Type*} [CommRing R] [CharP R 2]
    (t f g b z : R)
    (curve : z ^ 2 + t * f * g * z + t ^ 2 * f ^ 3 * g +
      b * t ^ 2 * g ^ 4 + t ^ 3 * f ^ 2 * g ^ 2 + b * f ^ 2 * g ^ 2 = 0) :
    (t * f * (t * g + f) + t * f * g + z) *
        (t * f * (t * g + f) + z) =
      (t ^ 2 * f ^ 2 + b * g ^ 2) * (t * g + f) ^ 2 := by
  have htwo : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination curve +
    (-t * f * g ^ 3 * b + t * f ^ 2 * z + t ^ 2 * f * g * z -
      t ^ 2 * g ^ 4 * b - f ^ 2 * g ^ 2 * b) * htwo

private def ordinaryNeighborFirst (W : WeierstrassCurve F) (f g : F[X]) : F[X] :=
  (X * f) ^ 2 + C W.a₆ * g ^ 2

private def ordinaryNeighborSecond (f g : F[X]) : F[X] :=
  X * f * g

private def neighborDenominator (f g : F[X]) : F[X] :=
  (X * g + f) ^ 2

private lemma ordinaryNeighborFirst_natDegree
    (W : WeierstrassCurve F) {f g : F[X]} (hf : f ≠ 0)
    (hdegree : g.natDegree < f.natDegree) :
    (ordinaryNeighborFirst W f g).natDegree = 2 * f.natDegree + 2 := by
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  have hremainder : (C W.a₆ * g ^ 2).natDegree < 2 * f.natDegree + 2 := by
    calc
      (C W.a₆ * g ^ 2).natDegree ≤ (g ^ 2).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
      _ < 2 * f.natDegree + 2 := by omega
  unfold ordinaryNeighborFirst
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hmain
  · rwa [hmain]

private lemma ordinaryNeighbor_primitive [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {f g : F[X]} (hfg : IsCoprime f g) (hden : X * g + f ≠ 0) :
    PrimitiveTriple (ordinaryNeighborFirst W f g)
      (ordinaryNeighborSecond f g) (neighborDenominator f g) := by
  have hb : W.a₆ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
    exact h
  apply primitiveTriple_of_no_common_irreducible
    (pow_ne_zero 2 hden)
  intro p hp hpFirst hpSecond hpDen
  have hprime := hp.prime
  have hpD : p ∣ X * g + f := hprime.dvd_of_dvd_pow hpDen
  have forceG (hpMain : p ∣ (X * f) ^ 2) : p ∣ g := by
    have hpRest : p ∣ C W.a₆ * g ^ 2 := by
      have hdifference := hpFirst.sub hpMain
      convert hdifference using 1
      unfold ordinaryNeighborFirst
      ring
    rcases hprime.dvd_mul.mp hpRest with hpC | hpg
    · have hCunit : IsUnit (C W.a₆) :=
        Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb)
      exact (hprime.not_dvd_one
        (hpC.trans (isUnit_iff_dvd_one.mp hCunit))).elim
    · exact hprime.dvd_of_dvd_pow hpg
  have commonDvd (hpf : p ∣ f) (hpg : p ∣ g) : False :=
    hp.not_isUnit (hfg.isUnit_of_dvd' hpf hpg)
  rcases hprime.dvd_mul.mp hpSecond with hpXf | hpg
  · rcases hprime.dvd_mul.mp hpXf with hpX | hpf
    · have hpMain : p ∣ (X * f) ^ 2 := by
        simpa [pow_two] using (hpX.mul_right f).mul_right (X * f)
      have hpg := forceG hpMain
      have hpf : p ∣ f := by
        have hdifference := hpD.sub (hpX.mul_right g)
        convert hdifference using 1
        ring
      exact commonDvd hpf hpg
    · have hpMain : p ∣ (X * f) ^ 2 := by
        simpa [pow_two] using hpXf.mul_right (X * f)
      exact commonDvd hpf (forceG hpMain)
  · have hpf : p ∣ f := by
      have hdifference := hpD.sub (hpg.mul_left X)
      convert hdifference using 1
      ring
    exact commonDvd hpf hpg

private lemma ordinaryNeighborFirst_ratio (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (ordinaryNeighborFirst W r.num r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) /
        (RatFunc.X + r) ^ 2 := by
  simp only [ordinaryNeighborFirst, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d := by
    exact (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    ((RatFunc.X * algebraMap F[X] (RatFunc F) r.num) ^ 2 +
        RatFunc.C W.a₆ * d ^ 2) /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show (RatFunc.X * (r * d)) ^ 2 + RatFunc.C W.a₆ * d ^ 2 =
      d ^ 2 * (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma ordinaryNeighborSecond_ratio (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (ordinaryNeighborSecond r.num r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      RatFunc.X * r / (RatFunc.X + r) ^ 2 := by
  simp only [ordinaryNeighborSecond, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d := by
    exact (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    RatFunc.X * algebraMap F[X] (RatFunc F) r.num * d /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show RatFunc.X * (r * d) * d = d ^ 2 * (RatFunc.X * r) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma ordinary_neighbor_plus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + r * s =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X + r ≠ 0) :
    (s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r =
      (RatFunc.X * r * (RatFunc.X + r) + RatFunc.X * s) /
        (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆ + r * s := by
    calc
      s ^ 2 = (s ^ 2 + r * s) + r * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  rw [div_pow, hs2, hdiffEq]
  field_simp [hdiff, RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma ordinary_neighbor_minus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + r * s =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s + r) / (r - RatFunc.X)) ^ 2 +
        (s + r) / (r - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + r =
      (RatFunc.X * r * (RatFunc.X + r) + RatFunc.X * r + RatFunc.X * s) /
        (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆ + r * s := by
    calc
      s ^ 2 = (s ^ 2 + r * s) + r * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  have hsr2 : (s + r) ^ 2 =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆ + r * s + r ^ 2 := by
    calc
      (s + r) ^ 2 = s ^ 2 + r ^ 2 := by
        rw [add_sq, show (2 : RatFunc F) = 0 from CharTwo.two_eq_zero]
        ring
      _ = _ := by rw [hs2]
  rw [div_pow, hsr2, hdiffEq]
  field_simp [hdiff, RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma ordinary_neighbor_pair_product [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + r * s =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) *
      (((s + r) / (r - RatFunc.X)) ^ 2 +
        (s + r) / (r - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) /
        (RatFunc.X + r) ^ 2 := by
  rw [ordinary_neighbor_plus W heq hdiff,
    ordinary_neighbor_minus W heq hdiff]
  have heq' := heq
  field_simp [RatFunc.X_ne_zero] at heq'
  have heq'' :
      s * r * RatFunc.X ^ 2 + s ^ 2 * RatFunc.X ^ 2 =
        r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
          r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆ := by
    calc
      _ = s * (s + r) * RatFunc.X ^ 2 := by ring
      _ = r ^ 2 *
          (r * RatFunc.X ^ 2 + (RatFunc.X ^ 3 + RatFunc.C W.a₆)) +
            RatFunc.X ^ 2 * RatFunc.C W.a₆ := heq'
      _ = _ := by ring
  have hcurve :
      (RatFunc.X * s) ^ 2 + RatFunc.X * r * (RatFunc.X * s) +
        RatFunc.X ^ 2 * r ^ 3 + RatFunc.C W.a₆ * RatFunc.X ^ 2 +
          RatFunc.X ^ 3 * r ^ 2 + RatFunc.C W.a₆ * r ^ 2 = 0 := by
    calc
      _ = (s * r * RatFunc.X ^ 2 + s ^ 2 * RatFunc.X ^ 2) +
          (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
            r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) := by
            ring
      _ = (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
            r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) +
          (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
            r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) := by
              rw [heq'']
      _ = 0 := CharTwo.add_self_eq_zero _
  have hcurve' :
      (RatFunc.X * s) ^ 2 + RatFunc.X * r * 1 * (RatFunc.X * s) +
        RatFunc.X ^ 2 * r ^ 3 * 1 +
          RatFunc.C W.a₆ * RatFunc.X ^ 2 * 1 ^ 4 +
            RatFunc.X ^ 3 * r ^ 2 * 1 ^ 2 +
              RatFunc.C W.a₆ * r ^ 2 * 1 ^ 2 = 0 := by
    simpa using hcurve
  have hformula := ordinary_product_formula RatFunc.X r 1
    (RatFunc.C W.a₆) (RatFunc.X * s) hcurve'
  field_simp [hdiff]
  linear_combination hformula

private lemma ordinary_neighbor_pair_sum [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) +
      (((s + r) / (r - RatFunc.X)) ^ 2 +
        (s + r) / (r - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) =
      RatFunc.X * r / (RatFunc.X + r) ^ 2 := by
  have hdiff' : r - RatFunc.X ≠ 0 := by
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using hdiff
  field_simp [hdiff, hdiff', RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, CharTwo.neg_eq, sub_eq_add_neg, mul_zero, zero_add, add_zero]
  ring

private lemma ordinaryPaperY_negY [CharP F 2]
    (W : WeierstrassCurve F) (x y : RatFunc F) :
    ordinaryPaperY ((ordinaryTwist W).toAffine.negY x y) =
      ordinaryPaperY y + ordinaryPaperX x := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist,
    sub_eq_add_neg, CharTwo.neg_eq]
  unfold ordinaryPaperY ordinaryPaperX
  field_simp [RatFunc.X_ne_zero]
  ring

private lemma neighborPolynomial_ne_zero (r : RatFunc F)
    (hdiff : RatFunc.X + r ≠ 0) : X * r.denom + r.num ≠ 0 := by
  intro hzero
  have hden : algebraMap F[X] (RatFunc F) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num =
      r * algebraMap F[X] (RatFunc F) r.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  have hmap := congrArg (algebraMap F[X] (RatFunc F)) hzero
  simp only [map_add, map_mul, RatFunc.algebraMap_X, map_zero] at hmap
  rw [hnum] at hmap
  apply hdiff
  exact (mul_eq_zero.mp (show
    (RatFunc.X + r) * algebraMap F[X] (RatFunc F) r.denom = 0 by
      linear_combination hmap)).resolve_right hden

private lemma ordinary_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (ordinaryTwist W).toAffine.Nonsingular x y}
    {hMinus : (ordinaryTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (ordinaryTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X ^ 3)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W)
    (hdegree : (ordinaryPaperX x).denom.natDegree <
      (ordinaryPaperX x).num.natDegree)
    (hdegreeMinus : (ordinaryPaperX xMinus).denom.natDegree <
      (ordinaryPaperX xMinus).num.natDegree)
    (hdegreePlus : (ordinaryPaperX xPlus).denom.natDegree <
      (ordinaryPaperX xPlus).num.natDegree) :
    (ordinaryPaperX xMinus).num.natDegree +
        (ordinaryPaperX xPlus).num.natDegree =
      2 * (ordinaryPaperX x).num.natDegree + 2 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0) :=
    hplusEq.1
  have hneg : (ordinaryTwist W).toAffine.Nonsingular x
      ((ordinaryTwist W).toAffine.negY x y) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W =
    -(-(.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W) by
      abel] at hminusEq
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : ordinaryPaperX xPlus =
      (ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxPlus]
    exact ordinaryPaperX_addX_Q_eq W hxQ
  have hrMinus : ordinaryPaperX xMinus =
      ((ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        (ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X) +
            RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxMinus, ordinaryPaperX_addX_Q_eq W hxQ,
      ordinaryPaperY_negY W]
  have heq := ordinary_paper_coordinates_equation W hxy
  have hdiff : RatFunc.X + ordinaryPaperX x ≠ 0 := by
    intro hzero
    apply hxQ
    have hr : ordinaryPaperX x = RatFunc.X := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
    unfold ordinaryPaperX at hr
    calc
      x = RatFunc.X * RatFunc.X ^ 2 :=
        (div_eq_iff (pow_ne_zero 2 RatFunc.X_ne_zero)).mp hr
      _ = RatFunc.X ^ 3 := by ring
  have hpairProd := ordinary_neighbor_pair_product W heq hdiff
  have hpairSum := ordinary_neighbor_pair_sum W
    (s := ordinaryPaperY y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborFirst W (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus * ordinaryPaperX xPlus := by
    rw [ordinaryNeighborFirst_ratio]
    calc
      _ = ordinaryPaperX xPlus * ordinaryPaperX xMinus := hpairProd.symm
      _ = ordinaryPaperX xMinus * ordinaryPaperX xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborSecond (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus + ordinaryPaperX xPlus := by
    rw [ordinaryNeighborSecond_ratio]
    calc
      _ = ordinaryPaperX xPlus + ordinaryPaperX xMinus := hpairSum.symm
      _ = ordinaryPaperX xMinus + ordinaryPaperX xPlus := by ring
  have hpoly : X * (ordinaryPaperX x).denom + (ordinaryPaperX x).num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := ordinaryNeighbor_primitive W
    (RatFunc.isCoprime_num_denom (ordinaryPaperX x)) hpoly
  have hout : neighborDenominator (ordinaryPaperX x).num
      (ordinaryPaperX x).denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := ordinaryNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma num_natDegree_div_of_isCoprime (p q : F[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hcop : IsCoprime p q) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p /
        algebraMap F[X] (RatFunc F) q)).natDegree = p.natDegree := by
  rw [charTwo_natDegree_num_div p q hq]
  have hgUnit : IsUnit (gcd p q) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg : gcd p q ≠ 0 := hgUnit.ne_zero
  have hmul : gcd p q * (p / gcd p q) = p :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hquot : p / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hp hmul.symm
  have hdegree := Polynomial.natDegree_mul hg hquot
  rw [hmul, Polynomial.natDegree_eq_zero_of_isUnit hgUnit, zero_add] at hdegree
  exact hdegree.symm

private lemma ordinaryPoint_sub_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    ordinaryPoint W (n - 1) = ordinaryPoint W n - ordinaryQ W := by
  have hstep := ordinaryPoint_add_one W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

private lemma ordinaryD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma ordinaryD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = -ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma ordinaryQ_y_ne_negY [CharP F 2]
    (W : WeierstrassCurve F) :
    (0 : RatFunc F) ≠
      (ordinaryTwist W).toAffine.negY (RatFunc.X ^ 3) 0 := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  simpa only [add_zero] using
    (mul_ne_zero (RatFunc.X_ne_zero (K := F))
      (pow_ne_zero 3 (RatFunc.X_ne_zero (K := F)))).symm

private def ordinaryDoubleNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 + C W.a₆

private lemma ordinaryPaperX_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)) =
      algebraMap F[X] (RatFunc F) (ordinaryDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (X ^ 2) := by
  rw [(ordinaryTwist W).toAffine.slope_of_Y_ne rfl
    (ordinaryQ_y_ne_negY W)]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    ordinaryTwist, ordinaryPaperX, map_add, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, ordinaryDoubleNumerator, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  field_simp [RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma ordinaryDoubleNumerator_natDegree (W : WeierstrassCurve F) :
    (ordinaryDoubleNumerator W).natDegree = 4 := by
  unfold ordinaryDoubleNumerator
  compute_degree
  norm_num

private lemma ordinaryDoubleNumerator_coprime [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    IsCoprime (ordinaryDoubleNumerator W) (X ^ 2) := by
  have hb : W.a₆ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
    exact h
  refine ⟨C W.a₆⁻¹, C W.a₆⁻¹ * X ^ 2, ?_⟩
  unfold ordinaryDoubleNumerator
  have hinv : C W.a₆⁻¹ * C W.a₆ = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hb, C_1]
  have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  linear_combination hinv + X ^ 4 * C W.a₆⁻¹ * htwo

private lemma ordinary_num_natDegree_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (ordinaryDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (X ^ 2))).natDegree = 4 := by
  rw [num_natDegree_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := ordinaryDoubleNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    (pow_ne_zero 2 X_ne_zero) (ordinaryDoubleNumerator_coprime W)]
  exact ordinaryDoubleNumerator_natDegree W

private lemma ordinaryD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = ordinaryQ W + ordinaryQ W) :
    ordinaryD W n = 4 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (ordinaryQ_y_ne_negY W)]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)))).natDegree = 4
  rw [ordinaryPaperX_doubleQ W, ordinary_num_natDegree_doubleQ W]

private lemma ordinaryD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = -(ordinaryQ W + ordinaryQ W)) :
    ordinaryD W n = 4 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (ordinaryQ_y_ne_negY W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)))).natDegree = 4
  rw [ordinaryPaperX_doubleQ W, ordinary_num_natDegree_doubleQ W]

private lemma ordinaryD_recurrence [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ∀ n, ordinaryD W (n - 1) + ordinaryD W (n + 1) = 2 * ordinaryD W n + 2 := by
  intro n
  cases hn : ordinaryPoint W n with
  | zero =>
      have hplus := ordinaryPoint_add_one W n
      have hminus := ordinaryPoint_sub_one W n
      rw [hn] at hplus hminus
      have hplusQ : ordinaryPoint W (n + 1) = ordinaryQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : ordinaryPoint W (n - 1) = -ordinaryQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := ordinaryD_eq_one_of_point_eq_Q W hplusQ
      have hdMinus := ordinaryD_eq_one_of_point_eq_neg_Q W hminusQ
      have hd : ordinaryD W n = 0 := by simp [ordinaryD, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : ordinaryPoint W (n - 1) with
      | zero =>
          have hsub := ordinaryPoint_sub_one W n
          rw [hn, hminusPoint] at hsub
          have hnQ : ordinaryPoint W n = ordinaryQ W := by
            have hxyQ :
                (.some x y hxy : (ordinaryTwist W).toAffine.Point) =
                  ordinaryQ W := sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := ordinaryPoint_add_one W n
          rw [hnQ] at hplus
          have hd := ordinaryD_eq_one_of_point_eq_Q W hnQ
          have hdPlus := ordinaryD_eq_four_of_point_eq_two_Q W hplus
          have hdMinus : ordinaryD W (n - 1) = 0 := by
            simp [ordinaryD, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : ordinaryPoint W (n + 1) with
          | zero =>
              have hadd := ordinaryPoint_add_one W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : ordinaryPoint W n = -ordinaryQ W := by
                have htranslated := congrArg
                  (fun P : (ordinaryTwist W).toAffine.Point ↦ P - ordinaryQ W)
                  hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (ordinaryTwist W).toAffine.Point) =
                      -ordinaryQ W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := ordinaryPoint_sub_one W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  ordinaryPoint W (n - 1) =
                    -(ordinaryQ W + ordinaryQ W) := by
                calc
                  ordinaryPoint W (n - 1) = -ordinaryQ W - ordinaryQ W :=
                    hminus
                  _ = -(ordinaryQ W + ordinaryQ W) := by abel
              have hd := ordinaryD_eq_one_of_point_eq_neg_Q W hnNegQ
              have hdMinus :=
                ordinaryD_eq_four_of_point_eq_neg_two_Q W hminusNegTwo
              have hdPlus : ordinaryD W (n + 1) = 0 := by
                simp [ordinaryD, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := ordinaryPoint_add_one W n
              have hminus := ordinaryPoint_sub_one W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (ordinaryTwist W).toAffine.Point) ≠
                    ordinaryQ W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (ordinaryTwist W).toAffine.Point) ≠
                    -ordinaryQ W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (ordinaryTwist W).toAffine.Nonsingular
                  (RatFunc.X ^ 3) 0 :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (ordinaryQ_equation W)
              have hxQ : x ≠ RatFunc.X ^ 3 := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
                  exact heq
              have hdegree := ordinary_num_degree W hn
              have hdegreeMinus := ordinary_num_degree W hminusPoint
              have hdegreePlus := ordinary_num_degree W hplusPoint
              have hgeneric := ordinary_generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [ordinaryD, hn, hminusPoint, hplusPoint] using hgeneric

private lemma ordinary_degree_computation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  exact ⟨{
    d := ordinaryD W
    zero := ordinaryD_zero W
    negOne := ordinaryD_neg_one W
    recurrence := ordinaryD_recurrence W
    noAdjacentZeros := ordinaryNoAdjacentZeros W }⟩

private def superH (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₄ * X + C W.a₆

private def superV [Finite F] (W : WeierstrassCurve F) : F[X] :=
  frobeniusTail (superH W) (C W.a₃) (charTwoExponent (F := F))

private lemma superH_pow_card [Finite F] (W : WeierstrassCurve F) :
    superH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₄ * X ^ Nat.card F + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.expand_card F _ fintypeF]
  simp only [superH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma superV_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      superH W ^ Nat.card F + superH W := by
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  let fintypeF : Fintype F := Fintype.ofFinite F
  have haq : W.a₃ ^ Nat.card F = W.a₃ := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card F _ fintypeF W.a₃
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card_sub_one_eq_one F _ fintypeF W.a₃ ha
  have htail := frobeniusTail_identity (superH W) (C W.a₃)
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hCq : C W.a₃ ^ Nat.card F = C W.a₃ := by rw [← map_pow, haq]
  have hCq1 : C W.a₃ ^ (2 * (Nat.card F - 1)) = 1 := by
    rw [show 2 * (Nat.card F - 1) = (Nat.card F - 1) * 2 by omega,
      pow_mul, ← map_pow, haq1, map_one, one_pow]
  rw [hCq, hCq1, one_mul] at htail
  exact htail

private def superTwist (W : WeierstrassCurve F) : WeierstrassCurve (RatFunc F) :=
  ⟨0, 0, RatFunc.C W.a₃, RatFunc.C W.a₄,
    RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X⟩

private lemma superTwist_discriminant [CharP F 2]
    (W : WeierstrassCurve F) : (superTwist W).Δ = RatFunc.C W.a₃ ^ 4 := by
  simp only [superTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero, sub_zero, CharTwo.neg_eq]
  ring_nf
  rw [CharTwo.neg_eq]

private instance [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] : (superTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, superTwist_discriminant,
    isUnit_iff_ne_zero]
  apply pow_ne_zero
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  intro hC
  apply ha
  apply RatFunc.C_injective
  simpa using hC

private lemma superQ_equation [CharP F 2] (W : WeierstrassCurve F) :
    (superTwist W).toAffine.Equation RatFunc.X 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [superTwist]

private def superQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (superQ_equation W)

private def superPZeroX [Finite F] : RatFunc F := RatFunc.X ^ Nat.card F

private def superPZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (superV W)

private lemma super_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      (X ^ Nat.card F) ^ 3 + C W.a₄ * X ^ Nat.card F +
        (X ^ 3 + C W.a₄ * X) := by
  rw [superV_identity W, superH_pow_card W]
  unfold superH
  ring_nf
  have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  linear_combination C W.a₆ * htwo

private lemma superPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Equation (superPZeroX (F := F))
      (superPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (super_pZero_polynomial_equation W)
  simpa only [superTwist, superPZeroX, superPZeroY, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

private def superPZero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (superPZero_equation W)

private def superPoint [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
    (superTwist W).toAffine.Point := superPZero W + n • superQ W

private def superD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (n : ℤ) : ℕ :=
  match superPoint W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num x).natDegree

private lemma superPoint_add_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
    superPoint W (n + 1) = superPoint W n + superQ W := by
  rw [superPoint, superPoint, add_one_zsmul]
  abel

private lemma superQ_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superQ W ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

private lemma superD_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superD W 0 = Nat.card F := by
  rw [superD, superPoint]
  simp only [zero_zsmul, add_zero, superPZero, WeierstrassCurve.Affine.Point.mk,
    superPZeroX]
  change (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
    Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

private lemma super_num_degree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {x y : RatFunc F} (hxy : (superTwist W).toAffine.Nonsingular x y) :
    (RatFunc.denom x).natDegree < (RatFunc.num x).natDegree := by
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  have hCa : RatFunc.C W.a₃ ≠ 0 := by
    intro hzero
    apply ha
    apply RatFunc.C_injective
    simpa using hzero
  have heq :
      y ^ 2 + RatFunc.C W.a₃ * y =
        x ^ 3 + RatFunc.C W.a₄ * x +
          RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X := by
    have heq' := hxy.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq'
    simp only [superTwist, zero_mul, add_zero] at heq'
    linear_combination heq'
  have hxpos : 0 < x.intDegree := by
    by_contra hxnot
    have hx : x.intDegree ≤ 0 := le_of_not_gt hxnot
    let lower := x ^ 3 + RatFunc.C W.a₄ * x + RatFunc.C W.a₄ * RatFunc.X
    have hx3 : (x ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
    have hbx : (RatFunc.C W.a₄ * x).intDegree ≤ 0 := by
      simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₄) (y := x)
        (m := 0) (n := 0) (by norm_num) (by simp) hx
    have hbX : (RatFunc.C W.a₄ * RatFunc.X).intDegree ≤ 1 := by
      simpa using intDegree_mul_le_of_le
        (x := RatFunc.C W.a₄) (y := RatFunc.X)
        (m := 0) (n := 1) (by norm_num) (by simp) (by simp)
    have hlower : lower.intDegree ≤ 1 := by
      dsimp only [lower]
      have hfirst := intDegree_add_le_of_le (m := 1) (by norm_num)
        (hx3.trans (by norm_num)) (hbx.trans (by norm_num))
      exact intDegree_add_le_of_le (m := 1) (by norm_num) hfirst hbX
    have hX3 : (RatFunc.X ^ 3 : RatFunc F).intDegree = 3 := by
      rw [intDegree_pow RatFunc.X_ne_zero]
      norm_num
    have hrhs : (RatFunc.X ^ 3 + lower).intDegree = 3 := by
      rw [intDegree_add_eq_left_of_lt (pow_ne_zero 3 RatFunc.X_ne_zero)]
      · exact hX3
      · rw [hX3]
        omega
    have heq' :
        y ^ 2 + RatFunc.C W.a₃ * y = RatFunc.X ^ 3 + lower := by
      dsimp only [lower]
      linear_combination heq
    by_cases hy0 : y = 0
    · subst y
      have hrhs0 : RatFunc.X ^ 3 + lower = 0 := by
        simpa using heq'.symm
      rw [hrhs0] at hrhs
      norm_num at hrhs
    by_cases hy : y.intDegree ≤ 0
    · have hy2 : (y ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hy 2
      have hay : (RatFunc.C W.a₃ * y).intDegree ≤ 0 := by
        simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₃) (y := y)
          (m := 0) (n := 0) (by norm_num) (by simp) hy
      have hlhs : (y ^ 2 + RatFunc.C W.a₃ * y).intDegree ≤ 0 :=
        intDegree_add_le_of_le (m := 0) (by norm_num) hy2 hay
      have hdegrees := congrArg RatFunc.intDegree heq'
      rw [hrhs] at hdegrees
      omega
    · have hypos : 0 < y.intDegree := lt_of_not_ge hy
      have hy2 : (y ^ 2).intDegree = 2 * y.intDegree := by
        rw [intDegree_pow hy0]
        norm_num
      have hay : (RatFunc.C W.a₃ * y).intDegree = y.intDegree := by
        rw [RatFunc.intDegree_mul hCa hy0]
        simp
      have hlhs :
          (y ^ 2 + RatFunc.C W.a₃ * y).intDegree = 2 * y.intDegree := by
        rw [intDegree_add_eq_left_of_lt (pow_ne_zero 2 hy0), hy2]
        rw [hay]
        omega
      have hdegrees := congrArg RatFunc.intDegree heq'
      rw [hlhs, hrhs] at hdegrees
      omega
  unfold RatFunc.intDegree at hxpos
  omega

private lemma superD_eq_zero_iff [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (n : ℤ) :
    superD W n = 0 ↔ superPoint W n = 0 := by
  cases hp : superPoint W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [superD, hp]
  | some x y hxy =>
      have hdeg := super_num_degree W hxy
      constructor
      · intro hd
        simp only [superD, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

private lemma superNoAdjacentZeros [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    : ∀ n, superD W n = 0 → superD W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (superD_eq_zero_iff W n).mp hn
  have hp1 := (superD_eq_zero_iff W (n + 1)).mp hn1
  apply superQ_ne_zero W
  have hs := superPoint_add_one W n
  rw [hp, hp1] at hs
  simpa using hs.symm

private lemma super_a₃_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    W.a₃ ≠ 0 := by
  have h := W.Δ'.ne_zero
  rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
  intro ha
  apply h
  simp [ha]

private def superMinusOneNumerator [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
    C W.a₄ * (X ^ Nat.card F + X) + C W.a₃ * superV W + C (W.a₃ ^ 2)

private lemma superH_natDegree (W : WeierstrassCurve F) :
    (superH W).natDegree = 3 := by
  unfold superH
  compute_degree <;> norm_num

private lemma frobeniusTail_super_natDegree
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (superH W) (C W.a₃) e).natDegree =
      3 * 2 ^ (e - 1) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusTail, superH_natDegree]
  | more e ih ih1 =>
      rw [frobeniusTail]
      have htail : frobeniusTail (superH W) (C W.a₃) (e + 1) ≠ 0 := by
        intro hzero
        have hdegree := ih1 (by omega)
        rw [hzero] at hdegree
        simp at hdegree
      rw [natDegree_add_eq_left_of_natDegree_lt]
      · rw [natDegree_pow, ih1 (by omega)]
        simp [pow_succ]
        ring
      · calc
          (C W.a₃ ^ (2 ^ (e + 2) - 2) * superH W).natDegree =
              (C (W.a₃ ^ (2 ^ (e + 2) - 2)) * superH W).natDegree := by
                rw [map_pow]
          _ ≤ (superH W).natDegree := Polynomial.natDegree_C_mul_le _ _
          _ = 3 := superH_natDegree W
          _ < (frobeniusTail (superH W) (C W.a₃) (e + 1) ^ 2).natDegree := by
            rw [natDegree_pow, ih1 (by omega)]
            rw [show e + 1 - 1 = e by omega]
            have hpow : 0 < 2 ^ e := pow_pos (by norm_num) e
            nlinarith

private lemma superV_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superV W).natDegree = 3 * 2 ^ (charTwoExponent (F := F) - 1) :=
  frobeniusTail_super_natDegree W _ (charTwoExponent_pos (F := F))

private lemma superMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk, pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hV : (superV W).natDegree ≤ 2 * Nat.card F := by
    rw [superV_natDegree W]
    change 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    C W.a₄ * (X ^ Nat.card F + X) + C W.a₃ * superV W + C (W.a₃ ^ 2)
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have h₁ : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by rw [natDegree_X_pow]; omega
    have h₂ : (C W.a₄ * (X ^ Nat.card F + X)).natDegree ≤
        2 * Nat.card F := by
      calc
        _ ≤ (X ^ Nat.card F + X : F[X]).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        _ ≤ max (Nat.card F) 1 := by
          exact (natDegree_add_le _ _).trans (max_le
            (by rw [natDegree_X_pow]; exact le_max_left _ _)
            (by rw [natDegree_X]; exact le_max_right _ _))
        _ ≤ 2 * Nat.card F := by omega
    have h₃ : (C W.a₃ * superV W).natDegree ≤ 2 * Nat.card F :=
      (Polynomial.natDegree_C_mul_le _ _).trans hV
    have h₄ : (C (W.a₃ ^ 2) : F[X]).natDegree ≤ 2 * Nat.card F := by
      rw [natDegree_C]
      omega
    dsimp only [remainder]
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le h₁ h₂)) h₃)) h₄)
  have heq : superMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold superMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

private lemma eval_superV [Finite F] (W : WeierstrassCurve F) (x : F) :
    (superV W).eval x =
      frobeniusValue ((superH W).eval x) W.a₃
        (charTwoExponent (F := F)) := by
  simp only [superV, eval_frobeniusTail, eval_C]

private lemma eval_superMinusOneNumerator [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F) :
    (superMinusOneNumerator W).eval x =
      W.a₃ * frobeniusValue ((superH W).eval x) W.a₃
        (charTwoExponent (F := F)) + W.a₃ ^ 2 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q1 : x ^ (2 * Nat.card F + 1) = x ^ 3 := by
    calc
      x ^ (2 * Nat.card F + 1) = x ^ (2 * Nat.card F) * x := pow_succ _ _
      _ = (x ^ Nat.card F) ^ 2 * x := by
        rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul]
      _ = x ^ 3 := by rw [hxq]; ring
  have hxq2 : x ^ (Nat.card F + 2) = x ^ 3 := by
    rw [pow_add, hxq]
    ring
  simp only [superMinusOneNumerator, eval_add, eval_mul, eval_pow, eval_X,
    eval_C, eval_superV, hx2q1, hxq2, hxq]
  have hcancel₁ : x ^ 3 + x ^ 3 = 0 := CharTwo.add_self_eq_zero _
  have hcancel₂ : W.a₄ * (x + x) = 0 := by rw [CharTwo.add_self_eq_zero, mul_zero]
  linear_combination hcancel₁ + hcancel₂

private lemma superEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔
      y ^ 2 + W.a₃ * y = (superH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJEqZeroNF,
    WeierstrassCurve.a₂_of_isCharTwoJEqZeroNF, zero_mul, add_zero,
    superH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

private def affineSolutionsEquivSuperFibers [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, charTwoFiber W.a₃ ((superH W).eval x) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (superEquation_iff_fiber W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (superEquation_iff_fiber W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma superPointCount_eq_fiber_sum [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] [W.IsElliptic] :
    Nat.card W.toAffine.Point =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivSuperFibers W), Nat.card_sigma]

private lemma superPZeroX_ne_QX [Finite F] :
    superPZeroX (F := F) ≠ RatFunc.X := by
  intro heq
  have hdegree := congrArg RatFunc.intDegree heq
  simp only [superPZeroX] at hdegree
  rw [intDegree_pow RatFunc.X_ne_zero] at hdegree
  simp only [RatFunc.intDegree_X, mul_one] at hdegree
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  omega

private lemma superX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0) =
      algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne superPZeroX_ne_QX]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    superTwist, superPZeroX, superPZeroY, zero_mul, add_zero,
    sub_eq_add_neg, CharTwo.neg_eq]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [superMinusOneNumerator, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hL : (RatFunc.X ^ Nat.card F + RatFunc.X : RatFunc F) ≠ 0 := by
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hv := congrArg (algebraMap F[X] (RatFunc F)) (superV_identity W)
  rw [superH_pow_card W] at hv
  simp only [superH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hv
  field_simp [hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hv +
    ((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃ +
      RatFunc.X ^ (Nat.card F * 3) + RatFunc.C W.a₄ *
        RatFunc.X ^ Nat.card F + RatFunc.C W.a₆ + RatFunc.X ^ 3 +
      RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * htwo +
    (-((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃) +
      RatFunc.X * RatFunc.X ^ (Nat.card F * 2) -
      RatFunc.X * RatFunc.C W.a₄ +
      RatFunc.X ^ 2 * RatFunc.X ^ Nat.card F -
      RatFunc.X ^ Nat.card F * RatFunc.C W.a₄ - RatFunc.C W.a₆) * htwo

private lemma superPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    ∃ y hxy, superPoint W (-1) =
      .some
        ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
            ((superTwist W).toAffine.negY (superPZeroX (F := F))
              (superPZeroY W)) 0)) y hxy := by
  have hp : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F)) (superPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superPZero_equation W)
  have hneg : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F))
      ((superTwist W).toAffine.negY (superPZeroX (F := F))
        (superPZeroY W)) :=
    ((superTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -superPZero W = .some (superPZeroX (F := F))
        ((superTwist W).toAffine.negY (superPZeroX (F := F))
          (superPZeroY W)) hneg := by
    rw [show superPZero W =
      .some (superPZeroX (F := F)) (superPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) superPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superQ_equation W))
  rw [← hnegP, ← show superQ W = .some RatFunc.X 0 _ from rfl] at hadd
  have hpoint : superPoint W (-1) = -(-superPZero W + superQ W) := by
    unfold superPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private lemma superH_derivative [CharP F 2] (W : WeierstrassCurve F) :
    (superH W).derivative = X ^ 2 + C W.a₄ := by
  unfold superH
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : ((3 : ℕ) : F) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, htwo,
      Nat.cast_one, zero_add]
  rw [hthree, map_one]
  norm_num

private lemma derivative_frobeniusTail_super [CharP F 2]
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (superH W) (C W.a₃) e).derivative =
      C (W.a₃ ^ (2 ^ e - 2)) * (X ^ 2 + C W.a₄) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [frobeniusTail, derivative_add, derivative_pow, derivative_mul,
    derivative_pow, derivative_C, superH_derivative]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  rw [htwo, map_zero]
  norm_num

private lemma eval_derivative_superMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] (x : F) :
    (superMinusOneNumerator W).derivative.eval x = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hqcast : ((Nat.card F : ℕ) : F) = 0 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact Nat.cast_card_eq_zero F
  have hcoeff1 : (((2 * Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hcoeff2 : (((Nat.card F + 2 : ℕ) : F)) = 0 := by
    push_cast
    rw [hqcast, zero_add]
    exact CharTwo.two_eq_zero
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one W.a₃ ha
  have hcard : 2 ≤ Nat.card F := Finite.one_lt_card
  have hamul : W.a₃ * W.a₃ ^ (Nat.card F - 2) = 1 := by
    calc
      W.a₃ * W.a₃ ^ (Nat.card F - 2) =
          W.a₃ ^ (Nat.card F - 2 + 1) := (pow_succ' _ _).symm
      _ = W.a₃ ^ (Nat.card F - 1) := by congr 1; omega
      _ = 1 := haq1
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  unfold superMinusOneNumerator superV
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add]
  rw [derivative_frobeniusTail_super W _ (charTwoExponent_pos (F := F))]
  rw [← card_eq_two_pow (F := F)]
  simp only [derivative_pow, derivative_X, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, eval_one, hcoeff1, hcoeff2, one_mul, zero_mul,
    hexponent1, hx2q, hqcast, add_zero]
  rw [← mul_assoc, hamul, one_mul]
  simp only [mul_one, zero_add]
  exact CharTwo.add_self_eq_zero (x ^ 2 + W.a₄)

private lemma superMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : superMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := superMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

private lemma rootMultiplicity_superNumerator_eq_zero [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] (x : F)
    (hvalue : frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) = 0) :
    Polynomial.rootMultiplicity x (superMinusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heval := eval_superMinusOneNumerator W x
  rw [hvalue, mul_zero, zero_add] at heval
  exact (pow_ne_zero 2 (super_a₃_ne_zero W)) (heval.symm.trans hroot)

private lemma superNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F)
    (hvalue : frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) = W.a₃) :
    (X - C x) ^ 2 ∣ superMinusOneNumerator W := by
  have hN := superMinusOneNumerator_ne_zero W
  have hroot : (superMinusOneNumerator W).IsRoot x := by
    change (superMinusOneNumerator W).eval x = 0
    rw [eval_superMinusOneNumerator, hvalue]
    simpa only [pow_two] using
      CharTwo.add_self_eq_zero (W.a₃ * W.a₃)
  have hderivativeRoot : (superMinusOneNumerator W).derivative.IsRoot x := by
    exact eval_derivative_superMinusOneNumerator W x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

private def superMinusOneGCD [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  gcd (superMinusOneNumerator W) (charTwoFrobeniusPolynomial ^ 2)

private lemma count_roots_superMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F) :
    Multiset.count x (superMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) := by
  have hN := superMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  rcases frobeniusValue_eq_zero_or_eq
      (c := (superH W).eval x) ha with hvalue | hvalue
  · have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 0 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
        _ = 0 := rootMultiplicity_superNumerator_eq_zero W x hvalue
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 0 :=
      Nat.eq_zero_of_le_zero hupper
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_two_of_value_eq_zero ha hvalue]
  · have hcommon : (X - C x) ^ 2 ∣ superMinusOneGCD W := by
      unfold superMinusOneGCD
      exact dvd_gcd (superNumerator_sq_dvd_of_value_eq W x hvalue)
        hlinearLsq
    have hlower : 2 ≤ Polynomial.rootMultiplicity x (superMinusOneGCD W) :=
      (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
    have hrootL : Polynomial.rootMultiplicity x
        ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
      rw [← Polynomial.count_roots]
      exact count_roots_charTwoFrobeniusPolynomial_sq x
    have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 2 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x
              ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
        _ = 2 := hrootL
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 2 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_zero_of_value_eq ha hvalue]

private lemma superMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (superMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (superMinusOneGCD W).roots) =
        (superMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (superMinusOneGCD W).roots) (by simp))
  calc
    (superMinusOneGCD W).natDegree =
        (superMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (superMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_superMinusOneGCD W x

private lemma superMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) =
      2 * Nat.card F := by
  rw [superMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) +
        Nat.card (charTwoFiber W.a₃ ((superH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two W.a₃ _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma superMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneNumerator W / superMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  have hN := superMinusOneNumerator_ne_zero W
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : superMinusOneGCD W *
      (superMinusOneNumerator W / superMinusOneGCD W) =
        superMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : superMinusOneNumerator W / superMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, superMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := superMinusOneGCD_natDegree_add_fiber_sum W
  omega

private lemma num_natDegree_superMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact superMinusOneQuotient_natDegree W

private lemma superD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := superPoint_neg_one_eq_some W
  unfold superD
  rw [hpoint]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0))).natDegree = _
  rw [superX_negPZero_add_Q W]
  rw [num_natDegree_superMinusOneRat W]
  exact (superPointCount_eq_fiber_sum W).symm

private lemma super_product_formula {R : Type*} [CommRing R] [CharP R 2]
    (t f g a b z : R)
    (curve : z ^ 2 + a * g ^ 2 * z + f ^ 3 * g + b * f * g ^ 3 +
      t ^ 3 * g ^ 4 + b * t * g ^ 4 = 0) :
    ((t * f + b * g) * (t * g + f) + a * z + a ^ 2 * g ^ 2) *
        ((t * f + b * g) * (t * g + f) + a * z) =
      (t ^ 2 * f ^ 2 + b ^ 2 * g ^ 2 + a ^ 2 * g * (t * g + f)) *
        (t * g + f) ^ 2 := by
  have htwo : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination a ^ 2 * curve +
    (-t * f ^ 2 * g ^ 2 * a ^ 2 + t * f ^ 2 * a * z +
      t * f ^ 3 * b * g + t * b * g ^ 2 * a * z + t ^ 2 * f * g * a * z -
      t ^ 2 * f * g ^ 3 * a ^ 2 + 2 * t ^ 2 * f ^ 2 * b * g ^ 2 +
      t ^ 3 * f * b * g ^ 3 - t ^ 3 * g ^ 4 * a ^ 2 +
      f * b * g * a * z - f ^ 3 * g * a ^ 2) * htwo

private def superNeighborFirst (W : WeierstrassCurve F) (f g : F[X]) : F[X] :=
  (X * f) ^ 2 + (C (W.a₄ ^ 2) * g ^ 2 +
    C (W.a₃ ^ 2) * g * (X * g + f))

private def superNeighborSecond (W : WeierstrassCurve F) (g : F[X]) : F[X] :=
  C (W.a₃ ^ 2) * g ^ 2

private lemma superNeighborFirst_natDegree
    (W : WeierstrassCurve F) {f g : F[X]} (hf : f ≠ 0)
    (hdegree : g.natDegree < f.natDegree) :
    (superNeighborFirst W f g).natDegree = 2 * f.natDegree + 2 := by
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  have hfirst : (C (W.a₄ ^ 2) * g ^ 2).natDegree ≤ 2 * g.natDegree := by
    calc
      (C (W.a₄ ^ 2) * g ^ 2).natDegree ≤ (g ^ 2).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
  have hXg : (X * g).natDegree ≤ f.natDegree := by
    calc
      (X * g).natDegree ≤ X.natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ f.natDegree := by rw [Polynomial.natDegree_X]; omega
  have hD : (X * g + f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le hXg le_rfl)
  have hsecond :
      (C (W.a₃ ^ 2) * g * (X * g + f)).natDegree ≤
        g.natDegree + f.natDegree := by
    calc
      (C (W.a₃ ^ 2) * g * (X * g + f)).natDegree ≤
          (C (W.a₃ ^ 2) * g).natDegree + (X * g + f).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ g.natDegree + f.natDegree :=
        Nat.add_le_add (Polynomial.natDegree_C_mul_le _ _) hD
  have hremainder :
      (C (W.a₄ ^ 2) * g ^ 2 +
        C (W.a₃ ^ 2) * g * (X * g + f)).natDegree <
          2 * f.natDegree + 2 := by
    apply (Polynomial.natDegree_add_le _ _).trans_lt
    rw [max_lt_iff]
    constructor <;> omega
  unfold superNeighborFirst
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hmain
  · rwa [hmain]

private lemma superNeighbor_primitive [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {f g : F[X]} (hfg : IsCoprime f g) (hden : X * g + f ≠ 0) :
    PrimitiveTriple (superNeighborFirst W f g) (superNeighborSecond W g)
      (neighborDenominator f g) := by
  have ha := super_a₃_ne_zero W
  apply primitiveTriple_of_no_common_irreducible (pow_ne_zero 2 hden)
  intro p hp _hpFirst hpSecond hpDen
  have hprime := hp.prime
  have hpD : p ∣ X * g + f := hprime.dvd_of_dvd_pow hpDen
  have hpG : p ∣ g := by
    have hpProduct : p ∣ C (W.a₃ ^ 2) * g ^ 2 := hpSecond
    rcases hprime.dvd_mul.mp hpProduct with hpC | hpg
    · have hCunit : IsUnit (C (W.a₃ ^ 2)) :=
        Polynomial.isUnit_C.mpr
          (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 ha))
      exact (hprime.not_dvd_one
        (hpC.trans (isUnit_iff_dvd_one.mp hCunit))).elim
    · exact hprime.dvd_of_dvd_pow hpg
  have hpF : p ∣ f := by
    have hdifference := hpD.sub (hpG.mul_left X)
    convert hdifference using 1
    ring
  exact hp.not_isUnit (hfg.isUnit_of_dvd' hpF hpG)

private lemma superNeighborFirst_ratio (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (superNeighborFirst W r.num r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C (W.a₄ ^ 2) +
        RatFunc.C (W.a₃ ^ 2) * (RatFunc.X + r)) /
          (RatFunc.X + r) ^ 2 := by
  simp only [superNeighborFirst, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d :=
    (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    ((RatFunc.X * algebraMap F[X] (RatFunc F) r.num) ^ 2 +
        (RatFunc.C W.a₄ ^ 2 * d ^ 2 +
          RatFunc.C W.a₃ ^ 2 * d *
            (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num))) /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show
    (RatFunc.X * (r * d)) ^ 2 + (RatFunc.C W.a₄ ^ 2 * d ^ 2 +
        RatFunc.C W.a₃ ^ 2 * d * (RatFunc.X * d + r * d)) =
      d ^ 2 * (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₄ ^ 2 +
        RatFunc.C W.a₃ ^ 2 * (RatFunc.X + r)) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma superNeighborSecond_ratio (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (superNeighborSecond W r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      RatFunc.C (W.a₃ ^ 2) / (RatFunc.X + r) ^ 2 := by
  simp only [superNeighborSecond, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d :=
    (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    RatFunc.C W.a₃ ^ 2 * d ^ 2 /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  rw [show RatFunc.C W.a₃ ^ 2 * d ^ 2 =
      d ^ 2 * RatFunc.C W.a₃ ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma super_neighbor_plus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + RatFunc.C W.a₃ * s =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
    (hdiff : RatFunc.X + r ≠ 0) :
    (s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X =
      ((RatFunc.X * r + RatFunc.C W.a₄) * (RatFunc.X + r) +
        RatFunc.C W.a₃ * s) / (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
          RatFunc.C W.a₃ * s := by
    calc
      s ^ 2 = (s ^ 2 + RatFunc.C W.a₃ * s) +
          RatFunc.C W.a₃ * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  rw [div_pow, hs2, hdiffEq]
  field_simp [hdiff]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero]
  ring

private lemma super_neighbor_minus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + RatFunc.C W.a₃ * s =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X =
      ((RatFunc.X * r + RatFunc.C W.a₄) * (RatFunc.X + r) +
        RatFunc.C W.a₃ * s + RatFunc.C (W.a₃ ^ 2)) /
          (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
          RatFunc.C W.a₃ * s := by
    calc
      s ^ 2 = (s ^ 2 + RatFunc.C W.a₃ * s) +
          RatFunc.C W.a₃ * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  have hsum2 : (s + RatFunc.C W.a₃) ^ 2 =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
          RatFunc.C W.a₃ * s + RatFunc.C (W.a₃ ^ 2) := by
    calc
      (s + RatFunc.C W.a₃) ^ 2 = s ^ 2 + RatFunc.C (W.a₃ ^ 2) := by
        rw [add_sq, show (2 : RatFunc F) = 0 from CharTwo.two_eq_zero]
        simp only [zero_mul, add_zero, ← map_pow]
      _ = _ := by rw [hs2]
  rw [div_pow, hsum2, hdiffEq]
  field_simp [hdiff]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero]
  ring

private lemma super_neighbor_pair_product [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + RatFunc.C W.a₃ * s =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) *
      (((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C (W.a₄ ^ 2) +
        RatFunc.C (W.a₃ ^ 2) * (RatFunc.X + r)) /
          (RatFunc.X + r) ^ 2 := by
  rw [super_neighbor_plus W heq hdiff, super_neighbor_minus W heq hdiff]
  have hcurve :
      s ^ 2 + RatFunc.C W.a₃ * s + r ^ 3 +
        RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
          RatFunc.C W.a₄ * RatFunc.X = 0 := by
    calc
      _ = (s ^ 2 + RatFunc.C W.a₃ * s) +
          (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
            RatFunc.C W.a₄ * RatFunc.X) := by ring
      _ = (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
            RatFunc.C W.a₄ * RatFunc.X) +
          (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
            RatFunc.C W.a₄ * RatFunc.X) := by rw [heq]
      _ = 0 := CharTwo.add_self_eq_zero _
  have hformula := super_product_formula RatFunc.X r 1
    (RatFunc.C W.a₃) (RatFunc.C W.a₄) s (by simpa using hcurve)
  simp only [map_pow] at ⊢
  simp only [mul_one, one_pow] at hformula
  field_simp [hdiff]
  linear_combination hformula

private lemma super_neighbor_pair_sum [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) +
      (((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) =
      RatFunc.C (W.a₃ ^ 2) / (RatFunc.X + r) ^ 2 := by
  have hdiff' : r - RatFunc.X ≠ 0 := by
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using hdiff
  field_simp [hdiff, hdiff']
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    CharTwo.neg_eq, sub_eq_add_neg, mul_zero, zero_add, add_zero,
    ← map_pow]

private lemma super_coordinates_equation [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF]
    {x y : RatFunc F} (hxy : (superTwist W).toAffine.Nonsingular x y) :
    y ^ 2 + RatFunc.C W.a₃ * y =
      x ^ 3 + RatFunc.C W.a₄ * x +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [superTwist, zero_mul, add_zero] at heq
  linear_combination heq

private lemma super_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (superTwist W).toAffine.Nonsingular x y}
    {hMinus : (superTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (superTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (superTwist W).toAffine.Point) + superQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (superTwist W).toAffine.Point) - superQ W)
    (hdegree : x.denom.natDegree < x.num.natDegree)
    (hdegreeMinus : xMinus.denom.natDegree < xMinus.num.natDegree)
    (hdegreePlus : xPlus.denom.natDegree < xPlus.num.natDegree) :
    xMinus.num.natDegree + xPlus.num.natDegree =
      2 * x.num.natDegree + 2 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X y 0) := hplusEq.1
  have hneg : (superTwist W).toAffine.Nonsingular x
      ((superTwist W).toAffine.negY x y) :=
    ((superTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (superTwist W).toAffine.Point) - superQ W =
    -(-(.some x y hxy : (superTwist W).toAffine.Point) + superQ W) by
      abel] at hminusEq
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X
          ((superTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : xPlus = (y / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxPlus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, superTwist, zero_mul,
      add_zero, sub_eq_add_neg, CharTwo.neg_eq]
  have hrMinus : xMinus =
      ((y + RatFunc.C W.a₃) / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxMinus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      superTwist, zero_mul, add_zero, sub_eq_add_neg,
      CharTwo.neg_eq]
  have heq := super_coordinates_equation W hxy
  have hdiff : RatFunc.X + x ≠ 0 := by
    intro hzero
    apply hxQ
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
  have hpairProd := super_neighbor_pair_product W heq hdiff
  have hpairSum := super_neighbor_pair_sum W (s := y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (superNeighborFirst W x.num x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus * xPlus := by
    rw [superNeighborFirst_ratio]
    calc
      _ = xPlus * xMinus := hpairProd.symm
      _ = xMinus * xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F) (superNeighborSecond W x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus + xPlus := by
    rw [superNeighborSecond_ratio]
    calc
      _ = xPlus + xMinus := hpairSum.symm
      _ = xMinus + xPlus := by ring
  have hpoly : X * x.denom + x.num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := superNeighbor_primitive W
    (RatFunc.isCoprime_num_denom x) hpoly
  have hout : neighborDenominator x.num x.denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := superNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma superPoint_sub_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
    superPoint W (n - 1) = superPoint W n - superQ W := by
  have hstep := superPoint_add_one W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

private lemma superD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma superD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = -superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma superQ_y_ne_negY [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (0 : RatFunc F) ≠ (superTwist W).toAffine.negY RatFunc.X 0 := by
  simp only [WeierstrassCurve.Affine.negY, superTwist, zero_mul, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  intro hzero
  apply super_a₃_ne_zero W
  apply RatFunc.C_injective
  simpa using hzero.symm

private def superDoubleNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 + C (W.a₄ ^ 2)

private def superDoubleDenominator (W : WeierstrassCurve F) : F[X] :=
  C (W.a₃ ^ 2)

private lemma superX_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0) =
      algebraMap F[X] (RatFunc F) (superDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (superDoubleDenominator W) := by
  rw [(superTwist W).toAffine.slope_of_Y_ne rfl (superQ_y_ne_negY W)]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    superTwist, superDoubleNumerator, superDoubleDenominator, map_add,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  have haC : RatFunc.C W.a₃ ≠ 0 := by
    intro hzero
    apply super_a₃_ne_zero W
    apply RatFunc.C_injective
    simpa using hzero
  field_simp [haC]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma superDoubleNumerator_natDegree (W : WeierstrassCurve F) :
    (superDoubleNumerator W).natDegree = 4 := by
  unfold superDoubleNumerator
  compute_degree
  norm_num

private lemma superDoubleDenominator_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superDoubleDenominator W ≠ 0 := by
  exact Polynomial.C_ne_zero.mpr (pow_ne_zero 2 (super_a₃_ne_zero W))

private lemma superDouble_coprime [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    IsCoprime (superDoubleNumerator W) (superDoubleDenominator W) := by
  have ha2 : W.a₃ ^ 2 ≠ 0 := pow_ne_zero 2 (super_a₃_ne_zero W)
  refine ⟨0, C (W.a₃ ^ 2)⁻¹, ?_⟩
  simp only [zero_mul, zero_add, superDoubleDenominator]
  rw [← C_mul, inv_mul_cancel₀ ha2, C_1]

private lemma super_num_natDegree_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (superDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (superDoubleDenominator W))).natDegree = 4 := by
  rw [num_natDegree_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := superDoubleNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    (superDoubleDenominator_ne_zero W) (superDouble_coprime W)]
  exact superDoubleNumerator_natDegree W

private lemma superD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = superQ W + superQ W) :
    superD W n = 4 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (superQ_y_ne_negY W)]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0))).natDegree = 4
  rw [superX_doubleQ W, super_num_natDegree_doubleQ W]

private lemma superD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = -(superQ W + superQ W)) :
    superD W n = 4 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (superQ_y_ne_negY W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0))).natDegree = 4
  rw [superX_doubleQ W, super_num_natDegree_doubleQ W]

private lemma superD_recurrence [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    ∀ n, superD W (n - 1) + superD W (n + 1) = 2 * superD W n + 2 := by
  intro n
  cases hn : superPoint W n with
  | zero =>
      have hplus := superPoint_add_one W n
      have hminus := superPoint_sub_one W n
      rw [hn] at hplus hminus
      have hplusQ : superPoint W (n + 1) = superQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : superPoint W (n - 1) = -superQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := superD_eq_one_of_point_eq_Q W hplusQ
      have hdMinus := superD_eq_one_of_point_eq_neg_Q W hminusQ
      have hd : superD W n = 0 := by simp [superD, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : superPoint W (n - 1) with
      | zero =>
          have hsub := superPoint_sub_one W n
          rw [hn, hminusPoint] at hsub
          have hnQ : superPoint W n = superQ W := by
            have hxyQ :
                (.some x y hxy : (superTwist W).toAffine.Point) = superQ W :=
              sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := superPoint_add_one W n
          rw [hnQ] at hplus
          have hd := superD_eq_one_of_point_eq_Q W hnQ
          have hdPlus := superD_eq_four_of_point_eq_two_Q W hplus
          have hdMinus : superD W (n - 1) = 0 := by
            simp [superD, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : superPoint W (n + 1) with
          | zero =>
              have hadd := superPoint_add_one W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : superPoint W n = -superQ W := by
                have htranslated := congrArg
                  (fun P : (superTwist W).toAffine.Point ↦ P - superQ W)
                  hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (superTwist W).toAffine.Point) =
                      -superQ W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := superPoint_sub_one W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  superPoint W (n - 1) = -(superQ W + superQ W) := by
                calc
                  superPoint W (n - 1) = -superQ W - superQ W := hminus
                  _ = -(superQ W + superQ W) := by abel
              have hd := superD_eq_one_of_point_eq_neg_Q W hnNegQ
              have hdMinus :=
                superD_eq_four_of_point_eq_neg_two_Q W hminusNegTwo
              have hdPlus : superD W (n + 1) = 0 := by
                simp [superD, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := superPoint_add_one W n
              have hminus := superPoint_sub_one W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (superTwist W).toAffine.Point) ≠ superQ W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (superTwist W).toAffine.Point) ≠
                    -superQ W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (superQ_equation W)
              have hxQ : x ≠ RatFunc.X := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
                  exact heq
              have hdegree := super_num_degree W hxy
              have hdegreeMinus := super_num_degree W hMinus
              have hdegreePlus := super_num_degree W hPlus
              have hgeneric := super_generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [superD, hn, hminusPoint, hplusPoint] using hgeneric

private lemma supersingular_degree_computation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  exact ⟨{
    d := superD W
    zero := superD_zero W
    negOne := superD_neg_one W
    recurrence := superD_recurrence W
    noAdjacentZeros := superNoAdjacentZeros W }⟩

/-- Manin's degree computation in either characteristic-two normal form. -/
theorem manin_degree_data_of_isCharTwoNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  by_cases hF : Nat.card F = 2
  · exact manin_degree_data_of_card_eq_two hF W
  · by_cases hF' : Nat.card F = 4
    · exact manin_degree_data_of_card_eq_four hF' W
    · cases ‹W.IsCharTwoNF› with
      | of_j_ne_zero => exact ordinary_degree_computation W
      | of_j_eq_zero => exact supersingular_degree_computation W

/-- Hasse's bound for a characteristic-two elliptic curve in either Manin normal form. -/
theorem hasse_bound_of_isCharTwoNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) :=
  (Classical.choice (manin_degree_data_of_isCharTwoNF W)).hasse_bound

/-- Hasse's bound for the ordinary characteristic-two Manin normal form. -/
theorem hasse_bound_of_isCharTwoJNeZeroNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) := by
  let _ : W.IsCharTwoNF := .of_j_ne_zero
  exact hasse_bound_of_isCharTwoNF W

/-- Hasse's bound for the supersingular characteristic-two Manin normal form. -/
theorem hasse_bound_of_isCharTwoJEqZeroNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) := by
  let _ : W.IsCharTwoNF := .of_j_eq_zero
  exact hasse_bound_of_isCharTwoNF W

end

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

end
/- ===== end MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean ===== -/

/- ===== begin MathlibExt/AlgebraicGeometry/EllipticCurve/HasseBound.lean (atlas-lean @ 805f71dcbadd) ===== -/
section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted

/-
# Hasse bound for elliptic curves

Records Hasse's bound on the number of points of an elliptic curve over a finite field.
-/

/--
If `F` is a finite field and `W : WeierstrassCurve F` is elliptic, then with `q = Nat.card F` and
`N = Nat.card (W.toAffine.Point)` we have `(q + 1 - N)^2 ≤ 4 * q` in `ℤ`. Source: H. Hasse, J.
Reine Angew. Math. 1936; modern Silverman, The Arithmetic of Elliptic Curves, 2nd ed.;
Lean states integral squared form of |N-(q+1)| ≤ 2√q including point at infinity.

Proof: Manin's elementary polynomial-degree argument on a twist over `F(t)`, done separately
for the odd-characteristic and characteristic-two normal forms. In characteristic two the point
count uses the fibres of the additive map `y ↦ y² + b y`, followed by the same projective
neighboring-degree recurrence, as in Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).

Proves `Wanted` entry `hasse_bound`.
-/
theorem hasse_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    (((Nat.card F : ℤ) + 1 - (Nat.card (W.toAffine.Point) : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) := by
  open MathlibExt.AlgebraicGeometry.EllipticCurve in
  by_cases hchar : ringChar F = 2
  · let _ : CharP F 2 := ringChar.of_eq hchar
    obtain ⟨C, hC⟩ := W.exists_variableChange_isCharTwoNF
    let _ : (C • W).IsCharTwoNF := hC
    have hbound := ManinTwistCharTwo.hasse_bound_of_isCharTwoNF (C • W)
    simpa only [WeierstrassCurve.VariableChange.natCard_point_eq C W] using hbound
  · let _ : Invertible (2 : F) := invertibleOfNonzero (Ring.two_ne_zero hchar)
    obtain ⟨C, hC⟩ := W.exists_variableChange_isCharNeTwoNF
    let _ : (C • W).IsCharNeTwoNF := hC
    have hbound := ManinTwist.hasse_bound_of_isCharNeTwoNF (C • W)
    simpa only [WeierstrassCurve.VariableChange.natCard_point_eq C W] using hbound

end MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted

end
/- ===== end MathlibExt/AlgebraicGeometry/EllipticCurve/HasseBound.lean ===== -/

/- ===== begin EllipticCurves/Mathlib/Basic.lean and
EllipticCurves/Mathlib/AdicCompletionExtension.lean (EllipticCurves @ c4c72f486112),
three declarations ===== -/
section

open IsDedekindDomain WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The maximal ideal of the ring of integers of the completion of `K` at `v` contracts
to `v` itself. -/
theorem comap_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).comap
      (algebraMap R (v.adicCompletionIntegers K)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [show ((algebraMap R (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
    v.adicCompletion K) = ((algebraMap R K x : K) : v.adicCompletion K) from rfl,
    valuedAdicCompletion_eq_valuation']

variable (v : HeightOneSpectrum R)

/-- Any element of the ring of integers of the completion is congruent to an element of `R`
modulo the maximal ideal. -/
theorem exists_valued_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) < 1 := by
  -- approximate by an element of `K` first
  have hball : {y | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy ↦ by simpa using hy⟩
  obtain ⟨w, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp (denseRange_algebraMap (K := K) v _) _ hball
  rw [Set.mem_ofPred_eq] at hwball
  -- the approximating element is integral at `v`
  have hz1 : v.valuation K z ≤ 1 := by
    rw [show v.valuation K z = Valued.v (algebraMap K (v.adicCompletion K) z) from
      (v.valuedAdicCompletion_eq_valuation' z).symm]
    calc Valued.v (algebraMap K (v.adicCompletion K) z)
        = Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)
            + (x : v.adicCompletion K)) := by ring_nf
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)))
            (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hwball.le x.2
  -- approximate the element of `K` by an element of `R`
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz1 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) z -
      algebraMap R (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      show Valued.v (algebraMap K (v.adicCompletion K) (z - algebraMap R K a)) =
        v.valuation K (z - algebraMap R K a) from v.valuedAdicCompletion_eq_valuation' _,
      Valuation.map_sub_swap]
    simpa using ha
  calc Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a)
      = Valued.v (((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) z)
          + (algebraMap K (v.adicCompletion K) z - algebraMap R (v.adicCompletion K) a)) := by
        ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := max_lt (by rwa [Valuation.map_sub_swap] at hwball) ha'

/-- The residue field of `v` maps isomorphically onto the residue field of the ring of
integers of the completion at `v`. -/
noncomputable def residueFieldEquivAdicCompletionIntegers :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  refine RingEquiv.ofBijective (Ideal.quotientMap (IsLocalRing.maximalIdeal _)
    (algebraMap R (v.adicCompletionIntegers K))
    (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)).symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective'
      (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)))
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := v.exists_valued_sub_lt_one (K := K) x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine (Ideal.Quotient.eq).mpr ?_
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰))).mpr ?_
    rw [show ((algebraMap R (v.adicCompletionIntegers K) a - x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap R (v.adicCompletion K) a - (x : v.adicCompletion K)
      from rfl, Valuation.map_sub_swap]
    exact ha

end IsDedekindDomain.HeightOneSpectrum

end
/- ===== end EllipticCurves/Mathlib ===== -/

/- ===== begin BSD/IdealNorms.lean (local library) ===== -/
section

/- # Prime norms and absolute convergence of norm weights -/

namespace BSDResearch

open Filter NumberField IsDedekindDomain
open scoped Topology

variable {K : Type*} [Field K] [NumberField K]

/-- The cardinality in Mathlib's local Euler factors is the absolute ideal norm. -/
theorem local_card_eq_norm (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = v.asIdeal.absNorm :=
  Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := K)).symm.toEquiv

theorem local_card_northcott : Northcott (fun v : HeightOneSpectrum (𝓞 K) ↦
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) := by
  simp only [local_card_eq_norm]
  exact ⟨fun n ↦ (Ideal.finite_setOfPred_absNorm_le n).preimage
    (fun _ _ _ _ h ↦ HeightOneSpectrum.ext h)⟩

/-- The Dedekind zeta residue implies convergence of the defining ideal series
at every real exponent greater than one. -/
theorem ideal_norm_summable (t : ℝ) (ht : 1 < t) :
    Summable (fun I : Ideal (𝓞 K) ↦ ((I.absNorm : ℝ) ^ t)⁻¹) := by
  classical
  let A (n : ℕ) : ℂ := Nat.card {I : Ideal (𝓞 K) // I.absNorm = n}
  have hn : ∀ᶠ x : ℝ in 𝓝[>] 1, ((x : ℂ) - 1) * dedekindZeta K x ≠ 0 :=
    (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).eventually_ne
      (by exact_mod_cast dedekindZeta_residue_ne_zero K)
  obtain ⟨x, hx, hxt⟩ := (hn.and ((eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds)).exists
  have hxS : LSeriesSummable A x := by
    by_contra h
    exact hx (mul_eq_zero_of_right _ (LSeries.eq_zero_of_not_LSeriesSummable A x h))
  have htS : LSeriesSummable A t := hxS.of_re_le_re hxt.le
  have hnorm := (summable_norm_iff.mpr htS)
  let F (I : Ideal (𝓞 K)) := ((I.absNorm : ℝ) ^ t)⁻¹
  apply (summable_partition (f := F) (s := fun n : ℕ ↦ {I | I.absNorm = n})
    (fun I ↦ by dsimp [F]; positivity)
    (fun I ↦ ⟨I.absNorm, rfl, fun _ h ↦ h.symm⟩)).mpr
  have hfin (n : ℕ) : Finite {I : Ideal (𝓞 K) // I.absNorm = n} :=
    Ideal.finite_setOfPred_absNorm_eq n
  constructor
  · intro n
    let _ := @Fintype.ofFinite _ (hfin n)
    change Summable (fun i : {I : Ideal (𝓞 K) // I.absNorm = n} ↦ F i.val)
    exact (hasSum_fintype _).summable
  · apply hnorm.congr
    intro n
    let _ := @Fintype.ofFinite _ (hfin n)
    change ‖LSeries.term A (t : ℂ) n‖ = ∑' (i : {I : Ideal (𝓞 K) // I.absNorm = n}), F i.val
    rw [LSeries.norm_term_eq]
    have he (i : {I : Ideal (𝓞 K) // I.absNorm = n}) : F i.val = ((n : ℝ) ^ t)⁻¹ :=
      congrArg (fun a : ℕ ↦ ((a : ℝ) ^ t)⁻¹) i.property
    simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    by_cases h : n = 0
    · simp [h, Real.zero_rpow (by linarith : t ≠ 0)]
    · simp [h, A, div_eq_mul_inv]

theorem prime_norm_summable (t : ℝ) (ht : 1 < t) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) ↦ ((v.asIdeal.absNorm : ℝ) ^ t)⁻¹) :=
  (ideal_norm_summable (K := K) t ht).comp_injective (fun _ _ h ↦ HeightOneSpectrum.ext h)

end BSDResearch

end
/- ===== end BSD/IdealNorms.lean ===== -/

/- ===== begin BSD/HasseEuler.lean (local library) ===== -/
section

/-
# Hasse's estimate for all local Euler coefficients

For good reduction the reciprocal roots have complex absolute value √q.
The two geometric series give a bound of (n + 1) q^(n/2) for coefficient n.
At bad primes one or both reciprocal roots are zero.
-/

namespace BSDResearch

open WeierstrassCurve
open scoped Classical ComplexConjugate

private noncomputable def geometricSeries (a : ℂ) : PowerSeries ℂ := PowerSeries.mk (a ^ ·)

private theorem geometricSeries_inv (a : ℂ) :
    geometricSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  rw [mul_sub, mul_one, ← mul_assoc]
  ext n
  cases n with
  | zero => simp [geometricSeries]
  | succ n => simp [PowerSeries.coeff_succ_mul_X, geometricSeries, pow_succ]

variable {R V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field V] [Algebra R V] [IsFractionRing R V] [Finite (IsLocalRing.ResidueField R)]

private theorem linear_factorization (a b : ℤ) (α β : ℂ)
    (hs : α + β = (a : ℂ)) (hp : α * β = (b : ℂ)) :
    PowerSeries.map (Int.castRingHom ℂ)
      ((1 - Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) =
      (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X) := by
  simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_one, map_add, map_sub, map_mul, map_one,
    map_pow, PowerSeries.map_C, PowerSeries.map_X, Int.coe_castRingHom]
  rw [← hs, ← hp, map_add, map_mul]
  ring

private theorem local_reciprocal_roots (W : WeierstrassCurve V) :
    ∃ α β : ℂ, ‖α‖ ≤ Real.sqrt (Nat.card (IsLocalRing.ResidueField R)) ∧
      ‖β‖ ≤ Real.sqrt (Nat.card (IsLocalRing.ResidueField R)) ∧
      PowerSeries.map (Int.castRingHom ℂ) (W.localPolynomial R : PowerSeries ℤ) =
        (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X) := by
  let q := Nat.card (IsLocalRing.ResidueField R)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.card_pos (α := IsLocalRing.ResidueField R)
  have hsqrt : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq
  by_cases hg : (W.minimal R).HasGoodReduction R
  · let k := IsLocalRing.ResidueField R
    let _ := Fintype.ofFinite k
    let C := (W.minimal R).reduction R
    let _ : C.IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
    let a : ℤ := (q : ℤ) + 1 - (Nat.card C.toAffine.Point : ℤ)
    have h : a ^ 2 ≤ 4 * (q : ℤ) :=
      MathlibExt.AlgebraicGeometry.EllipticCurve.HasseBoundWanted.hasse_bound C
    have h' : (a : ℝ)^2 ≤ 4 * (q : ℝ) := by exact_mod_cast h
    let α : ℂ := ⟨a/2, Real.sqrt (q - (a/2 : ℝ)^2)⟩
    have hns : Complex.normSq α = q := by
      simp only [Complex.normSq_apply, α, ← sq]
      rw [Real.sq_sqrt (by nlinarith)]
      ring
    have hnorm : ‖α‖ = Real.sqrt q := by rw [Complex.norm_def, hns]
    have hab : α * conj α = (q : ℂ) := by simp [Complex.mul_conj, hns]
    have hsum : α + conj α = (a : ℂ) := by
      rw [Complex.add_conj]
      simp [α]
      ring
    refine ⟨α, conj α, hnorm.le, by rw [Complex.norm_conj]; exact hnorm.le, ?_⟩
    have hp : W.localPolynomial R = 1 - Polynomial.C a * Polynomial.X +
        Polynomial.C (q : ℤ) * Polynomial.X ^ 2 := if_pos hg
    rw [hp]
    exact linear_factorization a q α (conj α) hsum (by simpa only [Int.cast_natCast] using hab)
  · by_cases hm : (W.minimal R).HasSplitMultiplicativeReduction R
    · refine ⟨1, 0, by simpa using hsqrt, by rw [norm_zero]; exact Real.sqrt_nonneg _, ?_⟩
      simp [localPolynomial, hg, hm]
    · by_cases hm' : (W.minimal R).HasMultiplicativeReduction R
      · refine ⟨-1, 0, by simpa using hsqrt, by rw [norm_zero]; exact Real.sqrt_nonneg _, ?_⟩
        simp [localPolynomial, hg, hm, hm']
      · exact ⟨0, 0, by rw [norm_zero]; exact Real.sqrt_nonneg _, by rw [norm_zero]; exact Real.sqrt_nonneg _, by simp [localPolynomial, hg, hm, hm']⟩

private theorem coeff_product_bound (A B : PowerSeries ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hA : ∀ n, ‖A.coeff n‖ ≤ r^n) (hB : ∀ n, ‖B.coeff n‖ ≤ r^n) (n : ℕ) :
    ‖(A*B).coeff n‖ ≤ (n+1 : ℝ)*r^n := by
  rw [PowerSeries.coeff_mul]
  calc
    _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ‖A.coeff ij.1 * B.coeff ij.2‖ := norm_sum_le _ _
    _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal n, r^n := by
      apply Finset.sum_le_sum
      intro ij hij
      rw [norm_mul, ← Finset.HasAntidiagonal.mem_antidiagonal.mp hij, pow_add]
      exact mul_le_mul (hA _) (hB _) (norm_nonneg _) (pow_nonneg hr _)
    _ = _ := by simp

private theorem coeff_linear_bound (a : ℂ) (n : ℕ) :
    ‖(1 - PowerSeries.C a * PowerSeries.X).coeff n‖ ≤ ‖a‖ ^ n := by
  rcases n with _ | _ | n
  · simp
  · simp [PowerSeries.coeff_one, PowerSeries.coeff_succ_mul_X]
  · simp [PowerSeries.coeff_one, PowerSeries.coeff_succ_mul_X]

set_option maxHeartbeats 800000 in
theorem local_coefficient_hasse (W : WeierstrassCurve V) (n : ℕ) :
    |(((W.localPowerSeries R).coeff n : ℤ) : ℝ)| ≤
      (n + 1 : ℝ) * Real.sqrt (Nat.card (IsLocalRing.ResidueField R)) ^ n := by
  let F := (W.localPowerSeries R).map (Int.castRingHom ℂ)
  let p := PowerSeries.map (Int.castRingHom ℂ) (W.localPolynomial R : PowerSeries ℤ)
  obtain ⟨α, β, hα, hβ, hp⟩ := local_reciprocal_roots (R := R) W
  have hFp : F * p = 1 := by
    unfold F p
    rw [← map_mul]
    have hc : PowerSeries.constantCoeff (W.localPolynomial R : PowerSeries ℤ) = 1 := by
      unfold localPolynomial
      split_ifs <;> simp
    rw [localPowerSeries, PowerSeries.invOfUnit_mul _ _ hc, map_one]
  have hGp : (geometricSeries α * geometricSeries β) * p = 1 := by
    unfold p
    rw [hp]
    calc
      _ = (geometricSeries α * (1 - PowerSeries.C α * PowerSeries.X)) *
          (geometricSeries β * (1 - PowerSeries.C β * PowerSeries.X)) := by ring
      _ = _ := by rw [geometricSeries_inv, geometricSeries_inv, one_mul]
  have he : F = geometricSeries α * geometricSeries β := by
    calc
      _ = F * ((geometricSeries α * geometricSeries β) * p) := by rw [hGp, mul_one]
      _ = (geometricSeries α * geometricSeries β) * (F * p) := by ring
      _ = _ := by rw [hFp, mul_one]
  let r := Real.sqrt (Nat.card (IsLocalRing.ResidueField R))
  have hn : |(((W.localPowerSeries R).coeff n : ℤ) : ℝ)| = ‖F.coeff n‖ := by
    simp [F, Complex.norm_intCast]
  rw [hn, he]
  apply coeff_product_bound _ _ (Real.sqrt_nonneg _)
  · intro m
    simpa [geometricSeries] using pow_le_pow_left₀ (norm_nonneg _) hα m
  · intro m
    simpa [geometricSeries] using pow_le_pow_left₀ (norm_nonneg _) hβ m

end BSDResearch

end
/- ===== end BSD/HasseEuler.lean ===== -/

/- ===== begin BSD/AbsoluteConvergence.lean (local library) ===== -/
section

/- # Absolute convergence of the global elliptic L-series on Re(s) > 3/2 -/

namespace BSDResearch

open Finset Filter ArithmeticFunction WeierstrassCurve NumberField IsDedekindDomain
open scoped Topology

private noncomputable def weight (t : ℝ) (f : ArithmeticFunction ℤ) (n : ℕ) : ℝ :=
  |(f n : ℝ)| / (n : ℝ) ^ t

private theorem weight_nonneg (t : ℝ) (f : ArithmeticFunction ℤ) (n : ℕ) : 0 ≤ weight t f n := by
  unfold weight
  positivity

private def boundedSums (t : ℝ) (f : ArithmeticFunction ℤ) (B : ℝ) :=
  ∀ S : Finset ℕ, ∑ n ∈ S, weight t f n ≤ B

private theorem boundedSums_one (t : ℝ) : boundedSums t 1 1 := by
  intro S
  have he (n : ℕ) : weight t 1 n = if n = 1 then 1 else 0 := by
    by_cases h : n = 1 <;> simp [weight, h]
  simp_rw [he]
  simp
  split <;> norm_num

private theorem boundedSums_mul {t B D : ℝ} {f g : ArithmeticFunction ℤ}
    (hf : boundedSums t f B) (hg : boundedSums t g D) : boundedSums t (f*g) (B*D) := by
  classical
  intro S
  let H (p : ℕ × ℕ) := weight t f p.1 * weight t g p.2
  have h0 (p) : 0 ≤ H p := mul_nonneg (weight_nonneg ..) (weight_nonneg ..)
  have hterm (n : ℕ) : weight t (f*g) n ≤ ∑ p ∈ n.divisorsAntidiagonal, H p := by
    unfold weight
    rw [ArithmeticFunction.mul_apply, Int.cast_sum]
    calc
      _ ≤ (∑ p ∈ n.divisorsAntidiagonal, |((f p.1 * g p.2 : ℤ) : ℝ)|) / (n : ℝ)^t :=
        div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (by positivity)
      _ = _ := by
        rw [sum_div]
        apply sum_congr rfl
        intro p hp
        have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
        rw [← he, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), Int.cast_mul, abs_mul]
        unfold H weight
        ring
  let pairs := S.biUnion Nat.divisorsAntidiagonal
  have hdis : (S : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
    intro i _ j _ h
    exact disjoint_left.mpr fun _ hi hj ↦ h
      ((Nat.mem_divisorsAntidiagonal.mp hi).1.symm.trans (Nat.mem_divisorsAntidiagonal.mp hj).1)
  have hsub : pairs ⊆ (pairs.image Prod.fst) ×ˢ (pairs.image Prod.snd) := by
    intro p hp
    exact mem_product.mpr ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩
  calc
    _ ≤ ∑ n ∈ S, ∑ p ∈ n.divisorsAntidiagonal, H p := sum_le_sum fun n _ ↦ hterm n
    _ = ∑ p ∈ pairs, H p := (sum_biUnion hdis).symm
    _ ≤ ∑ p ∈ (pairs.image Prod.fst) ×ˢ (pairs.image Prod.snd), H p :=
      sum_le_sum_of_subset_of_nonneg hsub fun p _ _ ↦ h0 p
    _ = (∑ i ∈ pairs.image Prod.fst, weight t f i) * ∑ j ∈ pairs.image Prod.snd, weight t g j := by
      rw [sum_product, sum_mul_sum]
    _ ≤ _ := mul_le_mul (hf _) (hg _) (sum_nonneg fun _ _ ↦ weight_nonneg ..)
      (by simpa using hf ∅)

private theorem boundedSums_local (G : PowerSeries ℤ) (t : ℝ) (q : ℕ) (hq₂ : 1 < q)
    (hG : ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ (2 * Real.sqrt q)^m)
    (hr : 2 * Real.sqrt q / (q : ℝ)^t < 1) :
    boundedSums t (ofPowerSeries q G) (1 - 2 * Real.sqrt q / (q : ℝ)^t)⁻¹ := by
  classical
  let w := weight t (ofPowerSeries q G)
  let r := 2 * Real.sqrt q / (q : ℝ)^t
  have hgeom := hasSum_geometric_of_lt_one (by positivity : 0 ≤ r) hr
  have hcoeff (m : ℕ) : w (q ^ m) ≤ r ^ m := by
    simp only [w, weight, ofPowerSeries_apply_pow hq₂, Nat.cast_pow, r, div_pow]
    rw [← Real.rpow_natCast_mul (by positivity), mul_comm (m : ℝ) t, Real.rpow_mul_natCast (by positivity)]
    exact div_le_div_of_nonneg_right (hG m) (by positivity)
  have hoff (n : ℕ) (hn : n ∉ Set.range (q ^ ·)) : w n = 0 := by
    simp [w, weight, ofPowerSeries_apply hq₂, Function.extend_apply' _ _ _ hn]
  have hinj := Nat.pow_right_injective hq₂
  have hsub : Function.support w ⊆ Set.range (q ^ ·) := fun n hn ↦ by
    by_contra he
    exact hn (hoff n he)
  have hcomp : Summable (w ∘ (q ^ ·)) :=
    hgeom.summable.of_nonneg_of_le (fun _ ↦ weight_nonneg ..) hcoeff
  have hw := (hinj.summable_iff hoff).mp hcomp
  intro S
  calc
    _ ≤ ∑' n, w n := hw.sum_le_tsum S (fun _ _ ↦ weight_nonneg ..)
    _ = ∑' m : ℕ, w (q ^ m) := (hinj.tsum_eq hsub).symm
    _ ≤ ∑' m : ℕ, r ^ m := hcomp.tsum_le_tsum hcoeff hgeom.summable
    _ = _ := hgeom.tsum_eq

variable {K : Type*} [Field K] [NumberField K]

private theorem summable_of_boundedSums (f : ArithmeticFunction ℤ) (s : ℂ) (B : ℝ)
    (hf : boundedSums s.re f B) : LSeriesSummable ((↑) ∘ f) s := by
  have hw := summable_of_sum_le (weight_nonneg s.re f) hf
  change Summable (LSeries.term _ s)
  apply summable_norm_iff.mp
  apply hw.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases h : n = 0
  · simp [weight, h]
  · simp [weight, h, Complex.norm_intCast]

private theorem euler_bound_of_stable {ι : Type*} (F : ι → ArithmeticFunction ℤ)
    (f : ArithmeticFunction ℤ) (t : ℝ) (b : ι → ℝ)
    (hs : ∀ n, ∀ᶠ T : Finset ι in atTop, (∏ v ∈ T, F v) n = f n)
    (hb : ∀ v, 0 ≤ b v) (hsu : Summable b) (hbound : ∀ v, boundedSums t (F v) (1 + b v)) :
    boundedSums t f (Real.exp (∑' v, b v)) := by
  classical
  have hprod (T : Finset ι) : boundedSums t (∏ v ∈ T, F v) (∏ v ∈ T, (1+b v)) := by
    induction T using Finset.induction_on with
    | empty => simpa using boundedSums_one t
    | insert v T hv h => simpa [prod_insert hv] using boundedSums_mul (hbound v) h
  intro S
  obtain ⟨T, hT⟩ := ((S.eventually_all).mpr fun n _ ↦ hs n).exists
  calc
    _ = ∑ n ∈ S, weight t (∏ v ∈ T, F v) n :=
      sum_congr rfl fun n hn ↦ by simp only [weight, hT n hn]
    _ ≤ _ := hprod T S
    _ ≤ _ := Real.prod_one_add_le_exp_sum T hb
    _ ≤ _ := Real.exp_le_exp.mpr (hsu.sum_le_tsum T (fun v _ ↦ hb v))

private theorem weighted_euler_product {ι : Type*} (q : ι → ℕ) [Northcott q]
    (hq₂ : ∀ v, 1 < q v) (G : ι → PowerSeries ℤ) (h₀ : ∀ v, (G v).constantCoeff = 1)
    (hG : ∀ v m, |(((G v).coeff m : ℤ) : ℝ)| ≤ (2 * Real.sqrt (q v))^m)
    {s : ℂ} (hs : 3 / 2 < s.re)
    (hprimes : Summable (fun v ↦ ((q v : ℝ) ^ (s.re - 1/2))⁻¹)) :
    LSeriesSummable ((↑) ∘ eulerProduct (fun v ↦ ofPowerSeries (q v) (G v))) s := by
  classical
  let t := s.re
  let F (v : ι) := ofPowerSeries (q v) (G v)
  let η := 2 / (2 : ℝ) ^ (t-1/2)
  let u (v : ι) := ((q v : ℝ) ^ (t-1/2))⁻¹
  let C := 2 / (1-η)
  have ht : 1 < t-1/2 := by dsimp [t]; linarith
  have hη : η < 1 := by
    apply (div_lt_one (by positivity)).mpr
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) ht
  have hC : 0 ≤ C := div_nonneg (by norm_num) (sub_pos.mpr hη).le
  have hbound (v : ι) : boundedSums t (F v) (1+C*u v) := by
    have hq : (2 : ℝ) ≤ q v := by exact_mod_cast (hq₂ v : 2 ≤ q v)
    have hp : 0 < (q v : ℝ) := by linarith
    have hr : 2 * Real.sqrt (q v) / (q v : ℝ)^t = 2*u v := by
      dsimp [u]
      rw [Real.rpow_sub hp, ← Real.sqrt_eq_rpow]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    have hle : 2*u v ≤ η := by
      unfold η u
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact Real.rpow_le_rpow (by norm_num) hq (by linarith)
    have hl := boundedSums_local (G v) t (q v) (hq₂ v) (hG v) (hr ▸ hle.trans_lt hη)
    intro S
    apply (hl S).trans
    rw [hr]
    have hv : 0 < 1-2*u v := by linarith
    have he : (1-2*u v)⁻¹ = 1 + (2*u v)/(1-2*u v) := by field_simp; ring
    rw [he]
    have hu : 0 ≤ u v := by dsimp [u]; positivity
    have hd := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu)
      (sub_pos.mpr hη) (by linarith : 1-η ≤ 1-2*u v)
    unfold C
    linarith only [hd, show 2*u v/(1-η) = 2/(1-η)*u v by ring]
  have hu : ∀ v, 0 ≤ C*u v := fun v ↦ mul_nonneg hC (by dsimp [u]; positivity)
  have hsu : Summable (fun v ↦ C*u v) := hprimes.mul_left C
  apply summable_of_boundedSums (eulerProduct F) s (Real.exp (∑' v, C*u v))
  exact euler_bound_of_stable F (eulerProduct F) t _ (tendsTo_eulerProduct_ofPowerSeries q G h₀)
    hu hsu hbound

theorem eulerProduct_summable_of_hasse
    (G : HeightOneSpectrum (𝓞 K) → PowerSeries ℤ) (h₀ : ∀ v, (G v).constantCoeff = 1)
    (hG : ∀ v m, |(((G v).coeff m : ℤ) : ℝ)| ≤ (2 * Real.sqrt v.asIdeal.absNorm)^m)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable ((↑) ∘ eulerProduct (fun v ↦ ofPowerSeries v.asIdeal.absNorm (G v))) s := by
  let _ : Northcott (fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal.absNorm) := by
    simpa only [local_card_eq_norm] using (local_card_northcott (K := K))
  apply weighted_euler_product (fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal.absNorm) _ G h₀ hG hs
    (prime_norm_summable _ (by linarith))
  intro v
  let _ : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    @Fintype.ofFinite _ (Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv)
  rw [← local_card_eq_norm v, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

theorem LSeriesSummable_of_three_halves_lt_re (W : WeierstrassCurve K) {s : ℂ} (hs : 3/2 < s.re) :
    LSeriesSummable ((↑) ∘ W.LFunction) s := by
  classical
  unfold LFunction localEulerFactor
  simp only [local_card_eq_norm]
  apply eulerProduct_summable_of_hasse _ (fun v ↦ by simp [localPowerSeries]) _ hs
  intro v m
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := K)).toEquiv
  rw [← local_card_eq_norm v, mul_pow]
  exact (local_coefficient_hasse (R := v.adicCompletionIntegers K) (W⁄(v.adicCompletion K)) m).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast m.lt_two_pow_self.succ_le) (by positivity))

end BSDResearch

end
/- ===== end BSD/AbsoluteConvergence.lean ===== -/

theorem OMA.solution : OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1.H1 := by
  intro E _ s hs
  exact BSDResearch.LSeriesSummable_of_three_halves_lt_re E hs

/-
The following text reproduces the ATLAS license notice and the Apache License, Version 2.0. The Apache license also applies to the incorporated EllipticCurves source.

Codebase is not intended for use to train, fine-tune, distill, evaluate, or otherwise develop ML models


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
