import FormalConjectures.ErdosProblems.«670»
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! # The dimension-uniform form of Erdős Problem 670 -/

/-
Ho Boon Suan, Erdős’s diameter conjecture for separated distances fails in high dimensions.
Adapted from https://github.com/boonsuan/erdos670/tree/c053b2580e0cf7e74c8d905f96feb101061612a3
The upstream modules are bundled to meet the one-file submission format.

MIT License

Copyright (c) 2026 Ho Boon Suan

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Counterexample to a dimension-free diameter conjecture of Erdos - Definitions

This file introduces the basic scalar-valued objects used throughout the formalization:
the squared distance profile `H`, the distance profile `G = sqrt o H`, and the asymptotic
constant `cStar = 1 - 1 / pi^2`.

## Main definitions

* `DiameterConstruction.H` : the squared distance profile.
* `DiameterConstruction.G` : the distance profile.
* `DiameterConstruction.cStar` : the asymptotic constant.

## References

* "A counterexample to a dimension-free diameter conjecture of Erdos"
-/

namespace DiameterConstruction

open Real

noncomputable section

/-- The squared distance profile function `H(θ) = πθ/4 - (1 - cos θ)/8`.

This arises as the squared distance between points at angular separation `θ` in a
weighted product of regular polygons, after applying a one-frequency perturbation
to the identity Fourier series `∑ (1 - cos jθ)/j²`. -/
def H (θ : ℝ) : ℝ := π * θ / 4 - (1 - cos θ) / 8

/-- The distance profile function `G(θ) = √(H(θ))`.

The pairwise distances in the construction are given by `G(2πs/m)` for
`s = 1, …, N`. The key properties are that `G` is strictly increasing and
strictly concave on `(0, π)`. -/
def G (θ : ℝ) : ℝ := sqrt (H θ)

/-- The asymptotic constant `c* = 1 - 1/π² ≈ 0.8987`.

This is the ratio `diam(𝒳ₘ)/m` in the limit, which is strictly less than `1`,
disproving the dimension-free form of Erdős's conjecture. -/
def cStar : ℝ := 1 - 1 / π ^ 2

/-- The first derivative of `H`: `H'(θ) = π/4 - sin(θ)/8`. -/
def H' (θ : ℝ) : ℝ := π / 4 - sin θ / 8

/-- The second derivative of `H`: `H''(θ) = -cos(θ)/8`. -/
def H'' (θ : ℝ) : ℝ := -(cos θ) / 8

/-- The first derivative of `G`: `G'(θ) = H'(θ) / (2√(H(θ)))`. -/
def G' (θ : ℝ) : ℝ := H' θ / (2 * sqrt (H θ))

/-- The numerator of `G''(θ)`, equal to `2H(θ)H''(θ) - H'(θ)²`. -/
def G''_num (θ : ℝ) : ℝ := 2 * H θ * H'' θ - H' θ ^ 2

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Analytic properties of H and G

This file proves the key analytic properties of the squared distance profile `H` and the
distance profile `G = √H`:

* `H` is strictly increasing on `[0, π]` with `H(0) = 0` and `H(π) = (π² - 1)/4`.
* `G` is strictly increasing on `[0, π]` (Lemma 3.2 of the paper).
* `G` is strictly concave on `[0, π]` (Lemma 3.2 of the paper).

The strict concavity is the main analytic result. The proof follows the paper:
the numerator `2H·H'' - (H')²` of `G''` is bounded above by `-ε²(1 - cos θ)² < 0`.

## Main results

* `DiameterConstruction.H_pos` : `H(θ) > 0` for `θ ∈ (0, π]`.
* `DiameterConstruction.G_strictMonoOn` : `G` is strictly increasing on `[0, π]`.
* `DiameterConstruction.G_strictConcaveOn` : `G` is strictly concave on `[0, π]`.
-/

namespace DiameterConstruction

open Real Set

noncomputable section

/- ### Properties of H -/

@[simp]
lemma H_zero : H 0 = 0 := by
  simp [H]

lemma H_pi : H π = (π ^ 2 - 1) / 4 := by
  unfold H; norm_num; ring;

lemma hasDerivAt_H (θ : ℝ) : HasDerivAt H (H' θ) θ := by
  convert!
    (HasDerivAt.sub
      (HasDerivAt.div_const (HasDerivAt.const_mul Real.pi (hasDerivAt_id θ)) 4)
      (HasDerivAt.div_const (HasDerivAt.const_sub (1 : ℝ) (Real.hasDerivAt_cos θ)) 8))
    using 1
  unfold H'
  ring

lemma H'_pos (θ : ℝ) : 0 < H' θ := by
  exact sub_pos_of_lt ( by nlinarith [ Real.pi_gt_three, Real.sin_le_one θ ] )

lemma H_pos {θ : ℝ} (hθ₀ : 0 < θ) (_hθπ : θ ≤ π) : 0 < H θ := by
  -- Since $H$ is strictly increasing on $(0, \pi]$, we have $H(θ) > H(0) = 0$.
  have hH_pos : StrictMono H := by
    exact strictMono_of_deriv_pos fun x => by rw [ hasDerivAt_H x |> HasDerivAt.deriv ] ; exact H'_pos x;
  exact lt_of_le_of_lt ( by norm_num [ H_zero ] ) ( hH_pos hθ₀ )

lemma H_nonneg {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ π) : 0 ≤ H θ := by
  exact ( if h : θ = 0 then by rw [ h ] ; exact H_zero.symm ▸ le_rfl else H_pos ( lt_of_le_of_ne hθ₀ ( Ne.symm h ) ) hθπ |> le_of_lt )

lemma H_ne_zero {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) : H θ ≠ 0 :=
  ne_of_gt (H_pos hθ₀ hθπ)

lemma continuous_H : Continuous H := by
  unfold H
  fun_prop

lemma continuousOn_H : ContinuousOn H (Icc 0 π) :=
  continuous_H.continuousOn

lemma hasDerivAt_H' (θ : ℝ) : HasDerivAt H' (H'' θ) θ := by
  convert! HasDerivAt.sub ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_sin θ |> HasDerivAt.div_const <| 8 ) using 1 ; norm_num [ H'' ];
  ring

/- ### Properties of G -/

lemma G_nonneg (θ : ℝ) : 0 ≤ G θ :=
  Real.sqrt_nonneg _

lemma G_pos {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) : 0 < G θ :=
  Real.sqrt_pos_of_pos (H_pos hθ₀ hθπ)

lemma G_ne_zero {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) : G θ ≠ 0 :=
  ne_of_gt (G_pos hθ₀ hθπ)

@[simp]
lemma G_zero : G 0 = 0 := by
  simp [G]

lemma G_sq {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ π) : G θ ^ 2 = H θ := by
  simp [G]
  exact Real.sq_sqrt (H_nonneg hθ₀ hθπ)

lemma hasDerivAt_G {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ ≤ π) :
    HasDerivAt G (G' θ) θ := by
      convert! HasDerivAt.sqrt ( hasDerivAt_H θ ) _ using 1;
      exact H_ne_zero hθ₀ hθπ

lemma continuousOn_G : ContinuousOn G (Icc 0 π) := by
  exact ContinuousOn.sqrt ( continuousOn_H )

/- ### G is strictly increasing -/

lemma G_strictMonoOn : StrictMonoOn G (Icc 0 π) := by
  intros x hx y hy hxy;
  -- Since H is strictly increasing on ℝ, we have H(x) < H(y).
  have hH : DiameterConstruction.H x < DiameterConstruction.H y := by
    exact strictMono_of_deriv_pos ( fun θ => by rw [ hasDerivAt_H θ |> HasDerivAt.deriv ] ; exact H'_pos θ ) hxy;
  exact Real.sqrt_lt_sqrt ( DiameterConstruction.H_nonneg hx.1 hx.2 ) hH

/- ### The numerator bound , key to concavity -/

/-- The auxiliary function `φ(θ) = sin θ - θ cos θ`. -/
def phi (θ : ℝ) : ℝ := sin θ - θ * cos θ

lemma phi_lt_pi {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) : phi θ < π := by
  unfold phi;
  by_cases h₂ : θ ≤ Real.pi / 2;
  · nlinarith [ Real.sin_le_one θ, Real.cos_nonneg_of_mem_Icc ⟨ by linarith, h₂ ⟩, Real.pi_gt_three ];
  · -- Since $\theta > \frac{\pi}{2}$, we have $\cos \theta < 0$.
    have h_cos_neg : Real.cos θ < 0 := by
      exact Real.cos_neg_of_pi_div_two_lt_of_lt ( by linarith ) ( by linarith );
    have := Real.sin_lt ( show 0 < Real.pi - θ by linarith );
    norm_num at this; nlinarith [ Real.pi_le_four, Real.sin_sq_add_cos_sq θ, Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ ] ;

/-
The numerator `2H(θ)H''(θ) - H'(θ)²` equals
`-(π/4)² + 2·(π/4)·(1/8)·φ(θ) - (1/8)²·(1 - cos θ)²`.
-/
lemma G''_num_eq (θ : ℝ) :
    G''_num θ = -(π / 4) ^ 2 + 2 * (π / 4) * (1 / 8) * phi θ
      - (1 / 8) ^ 2 * (1 - cos θ) ^ 2 := by
        unfold G''_num H H' H'' phi
        ring_nf
        rw [Real.sin_sq]
        ring_nf

/-
**Key bound**: The numerator `2H·H'' - (H')²` satisfies
`2H(θ)H''(θ) - H'(θ)² ≤ -(1/64)(1 - cos θ)²`.
-/
lemma G''_num_le (θ : ℝ) (hθ₀ : 0 < θ) (hθπ : θ < π) :
    G''_num θ ≤ -(1 / 64) * (1 - cos θ) ^ 2 := by
      have := phi_lt_pi hθ₀ hθπ;
      rw [ G''_num_eq ] ; nlinarith [ pi_gt_three, mul_lt_mul_of_pos_left this <| Real.pi_pos ] ;

lemma G''_num_neg {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) : G''_num θ < 0 := by
  exact lt_of_le_of_lt ( G''_num_le θ hθ₀ hθπ ) ( mul_neg_of_neg_of_pos ( by norm_num ) ( sq_pos_of_pos ( sub_pos_of_lt ( by nlinarith [ Real.sin_sq_add_cos_sq θ, Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ ] ) ) ) )

/- ### G is strictly concave -/

/-
The derivative of `G'` (i.e., `G''`) is `G''_num(θ) / (4 · H(θ)^(3/2))`.
-/
lemma hasDerivAt_G' {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) :
    HasDerivAt G' (G''_num θ / (4 * H θ * sqrt (H θ))) θ := by
      convert! HasDerivAt.div ( hasDerivAt_H' θ ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) <| HasDerivAt.sqrt ( hasDerivAt_H θ ) _ ) _ using 1;
      · norm_num [ G''_num, H'' ];
        grind;
      · exact H_ne_zero hθ₀ hθπ.le;
      · exact mul_ne_zero two_ne_zero <| ne_of_gt <| Real.sqrt_pos.mpr <| H_pos hθ₀ hθπ.le

lemma deriv_G_eq {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < π) :
    deriv G θ = G' θ := by
  exact (hasDerivAt_G hθ₀ hθπ.le).deriv

lemma iteratedDeriv_two_G_neg {θ : ℝ} (hθ : θ ∈ interior (Icc 0 π)) :
    deriv^[2] G θ < 0 := by
      -- From the hypothesis hθ, we know that θ is in the interior of [0, π], which means 0 < θ < π.
      have hθ_pos : 0 < θ ∧ θ < Real.pi := by
        rwa [ interior_Icc ] at hθ;
      -- From the hypothesis hθ, we know that θ is in the interior of [0, π], which means 0 < θ < π. Therefore, we can apply the lemma hasDerivAt_G' to get the derivative of G' at θ.
      have h_deriv_G' : HasDerivAt G' (G''_num θ / (4 * H θ * Real.sqrt (H θ))) θ := by
        exact hasDerivAt_G' hθ_pos.1 hθ_pos.2;
      convert! h_deriv_G'.deriv ▸ div_neg_of_neg_of_pos ( G''_num_neg hθ_pos.1 hθ_pos.2 ) _ using 1;
      · exact Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hθ_pos.1 hθ_pos.2 ) fun x hx => deriv_G_eq hx.1 hx.2 );
      · exact mul_pos ( mul_pos zero_lt_four ( H_pos hθ_pos.1 hθ_pos.2.le ) ) ( Real.sqrt_pos.mpr ( H_pos hθ_pos.1 hθ_pos.2.le ) )

/-- **Lemma 3.2 (Concavity)**: `G` is strictly concave on `[0, π]`. -/
theorem G_strictConcaveOn : StrictConcaveOn ℝ (Icc 0 π) G := by
  exact strictConcaveOn_of_deriv2_neg (convex_Icc 0 π) continuousOn_G
    fun θ hθ => iteratedDeriv_two_G_neg hθ

/- ### Consequence for distance gaps (Corollary 3.3) -/

/-
**Corollary 3.3**: For any arithmetic grid `2πs/m` with `s = 1, …, N`,
the forward differences of `G` are strictly decreasing. In particular,
the smallest gap is the last one `G(2πN/m) - G(2π(N-1)/m)`.
-/
theorem G_gaps_decreasing {a b c : ℝ} (ha : a ∈ Icc 0 π) (hc : c ∈ Icc 0 π)
    (hab : a < b) (hbc : b < c) (hstep : c - b = b - a) :
    G c - G b < G b - G a := by
      -- By definition of $G$, we know that $G$ is strictly concave on $[0, \pi]$.
      have hG_concave : StrictConcaveOn ℝ (Set.Icc 0 Real.pi) G :=
        G_strictConcaveOn;
      have := hG_concave.2 ha hc;
      contrapose! this;
      exact ⟨ by linarith, 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by rw [ show ( 1 / 2 : ℝ ) • a + ( 1 / 2 : ℝ ) • c = b by norm_num; linarith ] ; norm_num; linarith ⟩

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Singer difference sets

This file formalizes Singer's theorem: for every prime power `q`, there exists a cyclic
`(q^2 + q + 1, q + 1, 1)` difference set in `ZMod (q^2 + q + 1)`.

The construction follows the finite-field proof via the trace-zero hyperplane in a cubic
extension and transports the resulting cyclic quotient back to `ZMod`.
-/

namespace DiameterConstruction

open Finset ZMod
open scoped LinearAlgebra.Projectivization

/-- A cyclic `(m, n, 1)` difference set in `ZMod m`: a subset of size `n` such that every
nonzero residue has a unique representation as a difference of two elements. -/
structure SingerDiffSet (m : ℕ) [NeZero m] (n : ℕ) where
  carrier : Finset (ZMod m)
  card_eq : carrier.card = n
  diff_unique : ∀ r : ZMod m, r ≠ 0 →
    ∃! p : ZMod m × ZMod m, p.1 ∈ carrier ∧ p.2 ∈ carrier ∧ p.1 - p.2 = r

noncomputable section

namespace SingerConstruction

section ProjectiveSubtype

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def projectivizationSubtypeTo (s : Submodule K V) :
    ℙ K s → {x : ℙ K V // x ∈ s.projectivization} := fun x =>
  ⟨Projectivization.map s.subtype s.subtype_injective x, by
    induction x using Projectivization.ind with
    | h v hv =>
        rw [Projectivization.map_mk]
        exact (Submodule.mk_mem_projectivization_iff s _).2 v.property⟩

def projectivizationSubtypeInv (s : Submodule K V) :
    {x : ℙ K V // x ∈ s.projectivization} → ℙ K s := fun x =>
  have hxmem : x.1.rep ∈ s := by
    have hxmk : Projectivization.mk K x.1.rep x.1.rep_nonzero ∈ s.projectivization := by
      simp [x.1.mk_rep, x.2]
    exact (Submodule.mk_mem_projectivization_iff s x.1.rep_nonzero).1 hxmk
  Projectivization.mk K (⟨x.1.rep, hxmem⟩ : s) (by simpa using x.1.rep_nonzero)

def projectivizationSubtypeEquiv (s : Submodule K V) :
    ℙ K s ≃ {x : ℙ K V // x ∈ s.projectivization} where
  toFun := projectivizationSubtypeTo s
  invFun := projectivizationSubtypeInv s
  left_inv x := by
    induction x using Projectivization.ind with
    | h v hv =>
        change
          Projectivization.mk K
              (⟨(Projectivization.mk K (v : V) (by simpa using hv)).rep, ?_⟩ : s) _ =
            Projectivization.mk K v hv
        erw [Projectivization.mk_eq_mk_iff' K]
        obtain ⟨a, ha⟩ :=
          Projectivization.exists_smul_eq_mk_rep (K := K) (V := V) (v := (v : V))
            (by simpa using hv)
        refine ⟨a, Subtype.ext ?_⟩
        exact ha
  right_inv x := by
    apply Subtype.ext
    change
      Projectivization.map s.subtype s.subtype_injective
          (Projectivization.mk K (⟨x.1.rep, ?_⟩ : s) _) = x.1
    erw [Projectivization.map_mk]
    exact x.1.mk_rep

end ProjectiveSubtype

variable (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)

abbrev BaseField := GaloisField p n
abbrev CubicExtension := FiniteField.Extension (BaseField p n) p 3

def scalarSubgroup : Subgroup (CubicExtension p n)ˣ :=
  (Units.map ((algebraMap (BaseField p n) (CubicExtension p n)) : (BaseField p n) →* (CubicExtension p n))).range


abbrev QuotientUnits := (CubicExtension p n)ˣ ⧸ scalarSubgroup p n

def projToQuotient : ℙ (BaseField p n) (CubicExtension p n) → (QuotientUnits p n) :=
  Projectivization.lift
    (fun v => QuotientGroup.mk (Units.mk0 (v : (CubicExtension p n)) v.2))
    (by
      intro a b t h
      have ht : t ≠ 0 := by
        intro ht0
        apply a.2
        simp [h, ht0]
      apply QuotientGroup.eq.mpr
      refine ⟨(Units.mk0 t ht)⁻¹, ?_⟩
      ext
      simp [h, Algebra.smul_def, mul_assoc])

def quotientToProj : (QuotientUnits p n) → ℙ (BaseField p n) (CubicExtension p n) := by
  refine Quotient.lift (fun u : (CubicExtension p n)ˣ => Projectivization.mk (BaseField p n) (u : (CubicExtension p n)) u.ne_zero) ?_
  intro u v huv
  change QuotientGroup.leftRel (scalarSubgroup p n) u v at huv
  rw [QuotientGroup.leftRel_apply] at huv
  rw [Projectivization.mk_eq_mk_iff' (BaseField p n) (u : (CubicExtension p n)) (v : (CubicExtension p n)) u.ne_zero v.ne_zero]
  rcases huv with ⟨c, hc⟩
  refine ⟨((c⁻¹ : (BaseField p n)ˣ) : (BaseField p n)), ?_⟩
  have hc' : (((Units.map ((algebraMap (BaseField p n) (CubicExtension p n)) : (BaseField p n) →* (CubicExtension p n))) c : (CubicExtension p n)ˣ) : (CubicExtension p n)) = (u : (CubicExtension p n))⁻¹ * (v : (CubicExtension p n)) := by
    simpa using congrArg (fun z : (CubicExtension p n)ˣ => (z : (CubicExtension p n))) hc
  calc
    (((c⁻¹ : (BaseField p n)ˣ) : (BaseField p n)) • (v : (CubicExtension p n))) =
        ((((Units.map ((algebraMap (BaseField p n) (CubicExtension p n)) : (BaseField p n) →* (CubicExtension p n))) c)⁻¹ : (CubicExtension p n)ˣ) : (CubicExtension p n)) * v := by
      simp [Algebra.smul_def]
    _ = (((v : (CubicExtension p n))⁻¹ * (v : (CubicExtension p n))) * (u : (CubicExtension p n))) := by
      simp [hc', mul_comm]
    _ = u := by
      simp [Units.ne_zero v]

theorem left_inv_projToQuotient :
    Function.LeftInverse (quotientToProj p n) (projToQuotient p n) := by
  intro x
  induction x using Projectivization.ind with
  | h v hv =>
      simp [projToQuotient, quotientToProj]

theorem right_inv_projToQuotient :
    Function.RightInverse (quotientToProj p n) (projToQuotient p n) := by
  intro x
  refine QuotientGroup.induction_on x ?_
  intro u
  simp [quotientToProj, projToQuotient]

def projEquivQuotient : ℙ (BaseField p n) (CubicExtension p n) ≃ (QuotientUnits p n) where
  toFun := projToQuotient p n
  invFun := quotientToProj p n
  left_inv := left_inv_projToQuotient p n
  right_inv := right_inv_projToQuotient p n

def traceHyperplane : Submodule (BaseField p n) (CubicExtension p n) :=
  (Algebra.trace (BaseField p n) (CubicExtension p n)).ker

theorem finrank_traceHyperplane :
    Module.finrank (BaseField p n) (traceHyperplane p n) = 2 := by
  have hrange : LinearMap.range (Algebra.trace (BaseField p n) (CubicExtension p n)) = ⊤ := by
    exact LinearMap.range_eq_top.mpr (Algebra.trace_surjective (BaseField p n) (CubicExtension p n))
  have hs := LinearMap.finrank_range_add_finrank_ker (Algebra.trace (BaseField p n) (CubicExtension p n))
  rw [hrange, finrank_top] at hs
  have hs' : 1 + Module.finrank (BaseField p n) ((Algebra.trace (BaseField p n) (CubicExtension p n)).ker) = 3 := by
    simpa [FiniteField.finrank_extension (BaseField p n) p 3, add_comm, add_left_comm, add_assoc] using hs
  have hs'' : Module.finrank (BaseField p n) ((Algebra.trace (BaseField p n) (CubicExtension p n)).ker) = 2 := by omega
  exact hs''

def traceZeroRestriction (u : (CubicExtension p n)ˣ) : traceHyperplane p n →ₗ[(BaseField p n)] (BaseField p n) where
  toFun x := Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * x.1)
  map_add' x y := by
    simp [mul_add]
  map_smul' c x := by
    change Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * (c • x.1)) = c * Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * x.1)
    rw [show (u : (CubicExtension p n)) * (c • x.1) = c • ((u : (CubicExtension p n)) * x.1) by
      simp [Algebra.smul_def, mul_assoc, mul_comm]]
    exact (Algebra.trace (BaseField p n) (CubicExtension p n)).map_smul c _

theorem traceZeroRestriction_ne_zero {u : (CubicExtension p n)ˣ} (hu : (u : (QuotientUnits p n)) ≠ 1) :
    traceZeroRestriction p n u ≠ 0 := by
  intro hzero
  obtain ⟨y, hy⟩ := (Algebra.trace_surjective (BaseField p n) (CubicExtension p n)) 1
  let c : (BaseField p n) := Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * y)
  have hall : ∀ x : (CubicExtension p n), Algebra.traceForm (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) - algebraMap (BaseField p n) (CubicExtension p n) c) x = 0 := by
    intro x
    let z : (CubicExtension p n) := x - Algebra.trace (BaseField p n) (CubicExtension p n) x • y
    have hzmem : z ∈ traceHyperplane p n := by
      show Algebra.trace (BaseField p n) (CubicExtension p n) z = 0
      simp [z, hy]
    have hz0 : Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * z) = 0 := by
      have hz := LinearMap.congr_fun hzero ⟨z, hzmem⟩
      simpa [traceZeroRestriction] using hz
    have hz2 : Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * x) - Algebra.trace (BaseField p n) (CubicExtension p n) x * c = 0 := by
      rw [show (u : (CubicExtension p n)) * z = (u : (CubicExtension p n)) * x - ((Algebra.trace (BaseField p n) (CubicExtension p n) x : (BaseField p n)) • ((u : (CubicExtension p n)) * y)) by
        simp [z, mul_sub, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]] at hz0
      rw [LinearMap.map_sub] at hz0
      simpa [c] using hz0
    have htrace_scalar : Algebra.trace (BaseField p n) (CubicExtension p n) ((algebraMap (BaseField p n) (CubicExtension p n) c) * x) = c * Algebra.trace (BaseField p n) (CubicExtension p n) x := by
      rw [show (algebraMap (BaseField p n) (CubicExtension p n) c) * x = c • x by simp [Algebra.smul_def]]
      exact (Algebra.trace (BaseField p n) (CubicExtension p n)).map_smul c x
    have hform0 :
        Algebra.traceForm (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) - algebraMap (BaseField p n) (CubicExtension p n) c) x =
          Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * x) - c * Algebra.trace (BaseField p n) (CubicExtension p n) x := by
      rw [Algebra.traceForm_apply, sub_mul, LinearMap.map_sub, htrace_scalar]
    have hform :
        Algebra.traceForm (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) - algebraMap (BaseField p n) (CubicExtension p n) c) x =
          Algebra.trace (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) * x) - Algebra.trace (BaseField p n) (CubicExtension p n) x * c := by
      simpa [mul_comm] using hform0
    exact hform.trans hz2
  have hker : ((u : (CubicExtension p n)) - algebraMap (BaseField p n) (CubicExtension p n) c) ∈ LinearMap.ker (Algebra.traceForm (BaseField p n) (CubicExtension p n)) := by
    show Algebra.traceForm (BaseField p n) (CubicExtension p n) ((u : (CubicExtension p n)) - algebraMap (BaseField p n) (CubicExtension p n) c) = 0
    ext x
    exact hall x
  have hscalar : (u : (CubicExtension p n)) - algebraMap (BaseField p n) (CubicExtension p n) c = 0 := by
    simpa [(traceForm_nondegenerate (BaseField p n) (CubicExtension p n)).ker_eq_bot] using hker
  have hu_eq : (u : (CubicExtension p n)) = algebraMap (BaseField p n) (CubicExtension p n) c := sub_eq_zero.mp hscalar
  have hc0 : c ≠ 0 := by
    intro hc
    have hu0 : (u : (CubicExtension p n)) = 0 := by
      simp [hu_eq, hc]
    exact u.ne_zero hu0
  have hu_mem : u ∈ (scalarSubgroup p n) := by
    refine ⟨Units.mk0 c hc0, ?_⟩
    ext
    simp [hu_eq]
  exact hu <| (QuotientGroup.eq_one_iff u).2 hu_mem

def projectivizationSubtypeMap (s : Submodule (BaseField p n) (CubicExtension p n)) : ℙ (BaseField p n) s → ℙ (BaseField p n) (CubicExtension p n) :=
  fun x => (projectivizationSubtypeTo s x).1

def mulLinearEquiv (u : (CubicExtension p n)ˣ) : (CubicExtension p n) ≃ₗ[(BaseField p n)] (CubicExtension p n) where
  toFun x := (u : (CubicExtension p n)) * x
  invFun x := ((u⁻¹ : (CubicExtension p n)ˣ) : (CubicExtension p n)) * x
  left_inv x := by
    simp
  right_inv x := by
    simp
  map_add' x y := by
    simp [mul_add]
  map_smul' c x := by
    simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]

def projMul (u : (CubicExtension p n)ˣ) : ℙ (BaseField p n) (CubicExtension p n) → ℙ (BaseField p n) (CubicExtension p n) :=
  Projectivization.map (mulLinearEquiv p n u).toLinearMap (mulLinearEquiv p n u).injective

theorem quotientToProj_mul (u : (CubicExtension p n)ˣ) (d : (QuotientUnits p n)) :
    quotientToProj p n ((u : (QuotientUnits p n)) * d) = projMul p n u (quotientToProj p n d) := by
  refine QuotientGroup.induction_on d ?_
  intro v
  change quotientToProj p n ((u * v : (CubicExtension p n)ˣ) : (QuotientUnits p n)) =
    projMul p n u (quotientToProj p n (v : (QuotientUnits p n)))
  rfl

def singerSet : Set (QuotientUnits p n) :=
  {d | quotientToProj p n d ∈ (traceHyperplane p n).projectivization}

def quotientSubtypeEquiv (s : Set (ℙ (BaseField p n) (CubicExtension p n))) :
    {d : (QuotientUnits p n) // quotientToProj p n d ∈ s} ≃ {x : ℙ (BaseField p n) (CubicExtension p n) // x ∈ s} where
  toFun d := ⟨quotientToProj p n d.1, d.2⟩
  invFun x := ⟨projToQuotient p n x.1, by
    rw [left_inv_projToQuotient p n x.1]
    exact x.2⟩
  left_inv d := by
    apply Subtype.ext
    exact right_inv_projToQuotient p n d.1
  right_inv x := by
    apply Subtype.ext
    exact left_inv_projToQuotient p n x.1

def singerSubtypeEquivProjectivization :
    {d : (QuotientUnits p n) // d ∈ singerSet p n} ≃ ℙ (BaseField p n) (traceHyperplane p n) :=
  (quotientSubtypeEquiv p n ((traceHyperplane p n).projectivization)).trans
    (projectivizationSubtypeEquiv (traceHyperplane p n)).symm

theorem singerSet_card :
    Nat.card {d : (QuotientUnits p n) // d ∈ singerSet p n} = (Nat.card (BaseField p n)) + 1 := by
  exact Nat.card_congr (singerSubtypeEquivProjectivization p n)
    |>.trans <| by
      simpa [finrank_traceHyperplane p n] using
        Projectivization.card_of_finrank_two (BaseField p n) (traceHyperplane p n)
          (finrank_traceHyperplane p n)

theorem quotient_isCyclic : IsCyclic (QuotientUnits p n) := by
  exact isCyclic_of_surjective (QuotientGroup.mk' (scalarSubgroup p n)) QuotientGroup.mk_surjective

theorem quotient_card :
    Nat.card (QuotientUnits p n) = (Nat.card (BaseField p n)) ^ 2 + (Nat.card (BaseField p n)) + 1 := by
  exact Nat.card_congr (projEquivQuotient p n).symm
    |>.trans <| by
      simpa [FiniteField.finrank_extension (BaseField p n) p 3, pow_succ, pow_zero, Finset.sum_range_succ,
        Finset.sum_range_one, add_assoc, add_left_comm, add_comm, one_mul, mul_comm,
        mul_left_comm, mul_assoc] using
        Projectivization.card_of_finrank (BaseField p n) (CubicExtension p n) (FiniteField.finrank_extension (BaseField p n) p 3)

def tracePointCondition (u : (CubicExtension p n)ˣ) (x : ℙ (BaseField p n) (traceHyperplane p n)) : Prop :=
  projMul p n u (projectivizationSubtypeMap p n (traceHyperplane p n) x) ∈
    (traceHyperplane p n).projectivization

theorem tracePointCondition_iff (u : (CubicExtension p n)ˣ) (x : ℙ (BaseField p n) (traceHyperplane p n)) :
    tracePointCondition p n u x ↔
      x ∈ (LinearMap.ker (traceZeroRestriction p n u)).projectivization := by
  induction x using Projectivization.ind with
  | h v hv =>
      have hu : (u : CubicExtension p n) * (v : CubicExtension p n) ≠ 0 :=
        mul_ne_zero (Units.ne_zero u) (fun hz => hv (Subtype.ext hz))
      change
        Projectivization.mk (BaseField p n) ((u : CubicExtension p n) * (v : CubicExtension p n)) hu ∈
            (traceHyperplane p n).projectivization ↔
          Projectivization.mk (BaseField p n) v hv ∈
            (LinearMap.ker (traceZeroRestriction p n u)).projectivization
      exact (Submodule.mk_mem_projectivization_iff (traceHyperplane p n) hu).trans
        (Submodule.mk_mem_projectivization_iff (LinearMap.ker (traceZeroRestriction p n u)) hv).symm

def localIntersectionToTracePoints (u : (CubicExtension p n)ˣ) :
    {d : (QuotientUnits p n) // d ∈ singerSet p n ∧ (u : (QuotientUnits p n)) * d ∈ singerSet p n} ≃
      {x : ℙ (BaseField p n) (traceHyperplane p n) // tracePointCondition p n u x} where
  toFun d := by
    let y :
        {x : ℙ (BaseField p n) (CubicExtension p n) // x ∈ (traceHyperplane p n).projectivization} :=
      ⟨quotientToProj p n d.1, d.2.1⟩
    refine ⟨(projectivizationSubtypeEquiv (traceHyperplane p n)).symm y, ?_⟩
    have hy :
        projectivizationSubtypeMap p n (traceHyperplane p n)
            ((projectivizationSubtypeEquiv (traceHyperplane p n)).symm y) =
          quotientToProj p n d.1 := by
      exact congrArg Subtype.val
        ((projectivizationSubtypeEquiv (traceHyperplane p n)).apply_symm_apply y)
    rw [tracePointCondition, hy]
    simpa [singerSet, quotientToProj_mul p n u d.1] using d.2.2
  invFun x := by
    refine ⟨projToQuotient p n (projectivizationSubtypeMap p n (traceHyperplane p n) x.1), ?_⟩
    constructor
    · change quotientToProj p n
          (projToQuotient p n (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)) ∈
            (traceHyperplane p n).projectivization
      rw [left_inv_projToQuotient p n]
      change (projectivizationSubtypeTo (traceHyperplane p n) x.1).1 ∈
          (traceHyperplane p n).projectivization
      exact (projectivizationSubtypeTo (traceHyperplane p n) x.1).2
    · change quotientToProj p n
          ((u : (QuotientUnits p n)) * projToQuotient p n
            (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)) ∈
            (traceHyperplane p n).projectivization
      rw [quotientToProj_mul p n u]
      rw [left_inv_projToQuotient p n]
      exact x.2
  left_inv d := by
    apply Subtype.ext
    change
      projToQuotient p n
        (projectivizationSubtypeMap p n (traceHyperplane p n)
          ((projectivizationSubtypeEquiv (traceHyperplane p n)).symm
            ⟨quotientToProj p n d.1, d.2.1⟩)) = d.1
    have :
        projectivizationSubtypeMap p n (traceHyperplane p n)
            ((projectivizationSubtypeEquiv (traceHyperplane p n)).symm
              ⟨quotientToProj p n d.1, d.2.1⟩) =
          quotientToProj p n d.1 := by
      exact congrArg Subtype.val
        ((projectivizationSubtypeEquiv (traceHyperplane p n)).apply_symm_apply
          ⟨quotientToProj p n d.1, d.2.1⟩)
    simpa [this] using right_inv_projToQuotient p n d.1
  right_inv x := by
    apply Subtype.ext
    change
      (projectivizationSubtypeEquiv (traceHyperplane p n)).symm
          ⟨quotientToProj p n
            (projToQuotient p n
              (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)),
            ?_⟩ = x.1
    have hx :
        quotientToProj p n
            (projToQuotient p n
              (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)) =
          projectivizationSubtypeMap p n (traceHyperplane p n) x.1 := by
      exact left_inv_projToQuotient p n
        (projectivizationSubtypeMap p n (traceHyperplane p n) x.1)
    have hx' :
        (projectivizationSubtypeEquiv (traceHyperplane p n)).symm
            ⟨projectivizationSubtypeMap p n (traceHyperplane p n) x.1,
              (projectivizationSubtypeTo (traceHyperplane p n) x.1).2⟩ = x.1 := by
      exact (projectivizationSubtypeEquiv (traceHyperplane p n)).symm_apply_apply x.1
    simpa [hx] using hx'

def localIntersectionEquivKernel (u : (CubicExtension p n)ˣ) :
    {d : (QuotientUnits p n) // d ∈ singerSet p n ∧ (u : (QuotientUnits p n)) * d ∈ singerSet p n} ≃
      ℙ (BaseField p n) (LinearMap.ker (traceZeroRestriction p n u)) :=
  (localIntersectionToTracePoints p n u).trans <|
    (Equiv.subtypeEquivRight fun x => tracePointCondition_iff p n u x).trans
      (projectivizationSubtypeEquiv (LinearMap.ker (traceZeroRestriction p n u))).symm

theorem finrank_traceZeroRestriction_ker {u : (CubicExtension p n)ˣ} (hu : (u : (QuotientUnits p n)) ≠ 1) :
    Module.finrank (BaseField p n) (LinearMap.ker (traceZeroRestriction p n u)) = 1 := by
  have hsurj : Function.Surjective (traceZeroRestriction p n u) := by
    have hK : Module.finrank (BaseField p n) (BaseField p n) = 1 := by simp
    exact surjective_of_nonzero_of_finrank_eq_one
      hK (f := traceZeroRestriction p n u)
      (traceZeroRestriction_ne_zero p n hu)
  have hrange : LinearMap.range (traceZeroRestriction p n u) = ⊤ := by
    exact LinearMap.range_eq_top.mpr hsurj
  have hs := LinearMap.finrank_range_add_finrank_ker (traceZeroRestriction p n u)
  rw [hrange, finrank_top, finrank_traceHyperplane p n] at hs
  have hs' : 1 + Module.finrank (BaseField p n) (LinearMap.ker (traceZeroRestriction p n u)) = 2 := by
    simpa [add_comm, add_left_comm, add_assoc] using hs
  omega

theorem localIntersection_card {u : (CubicExtension p n)ˣ} (hu : (u : (QuotientUnits p n)) ≠ 1) :
    Nat.card {d : (QuotientUnits p n) // d ∈ singerSet p n ∧ (u : (QuotientUnits p n)) * d ∈ singerSet p n} = 1 := by
  refine Nat.card_congr (localIntersectionEquivKernel p n u) |>.trans ?_
  simpa [finrank_traceZeroRestriction_ker p n hu] using
    Projectivization.card_of_finrank (BaseField p n)
      (LinearMap.ker (traceZeroRestriction p n u))
      (finrank_traceZeroRestriction_ker p n hu)

theorem singerSet_translate_unique_aux {u : (CubicExtension p n)ˣ} (hu : (u : (QuotientUnits p n)) ≠ 1) :
    ∃! d : (QuotientUnits p n), d ∈ singerSet p n ∧ (u : (QuotientUnits p n)) * d ∈ singerSet p n := by
  let A := {d : (QuotientUnits p n) // d ∈ singerSet p n ∧ (u : (QuotientUnits p n)) * d ∈ singerSet p n}
  have hA : Nat.card A = 1 := localIntersection_card p n hu
  have hsub : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA).1
  let a : A := Classical.choice ((Nat.card_eq_one_iff_unique.mp hA).2)
  refine ⟨a.1, a.2, ?_⟩
  intro d hd
  have : (⟨d, hd⟩ : A) = a := Subsingleton.elim _ _
  simpa using congrArg Subtype.val this

theorem singerSet_translate_unique (g : (QuotientUnits p n)) (hg : g ≠ 1) :
    ∃! d : (QuotientUnits p n), d ∈ singerSet p n ∧ g * d ∈ singerSet p n := by
  refine QuotientGroup.induction_on g ?_ hg
  intro u hu
  exact singerSet_translate_unique_aux p n hu

lemma unique_translate_to_unique_difference
    {A : Type*} [AddCommGroup A] {D : Set A}
    (h : ∀ x : A, x ≠ 0 → ∃! b : A, b ∈ D ∧ x + b ∈ D) :
    ∀ x : A, x ≠ 0 →
      ∃! p : A × A, p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 - p.2 = x := by
  intro x hx
  rcases h x hx with ⟨b, hb, hb_unique⟩
  refine ⟨(x + b, b), ?_, ?_⟩
  · refine ⟨hb.2, hb.1, ?_⟩
    simp [sub_eq_add_neg, add_assoc]
  · intro p hp
    have hpb : p.2 ∈ D ∧ x + p.2 ∈ D := by
      refine ⟨hp.2.1, ?_⟩
      have hxpb : x + p.2 = p.1 := by
        calc
          x + p.2 = (p.1 - p.2) + p.2 := by rw [hp.2.2]
          _ = p.1 := by
            simp [sub_eq_add_neg, add_assoc]
      simpa [hxpb] using hp.1
    have hp2 : p.2 = b := hb_unique _ hpb
    have hp1 : p.1 = x + b := by
      calc
        p.1 = x + p.2 := by
          have hxpb : x + p.2 = p.1 := by
            calc
              x + p.2 = (p.1 - p.2) + p.2 := by rw [hp.2.2]
              _ = p.1 := by
                simp [sub_eq_add_neg, add_assoc]
          exact hxpb.symm
        _ = x + b := by rw [hp2]
    ext <;> simp [hp1, hp2]

theorem singer_exists_zmod :
    let m := (Nat.card (BaseField p n)) ^ 2 + (Nat.card (BaseField p n)) + 1
    ∃ D : Finset (ZMod m), D.card = (Nat.card (BaseField p n)) + 1 ∧
      ∀ r : ZMod m, r ≠ 0 →
        ∃! p : ZMod m × ZMod m, p.1 ∈ D ∧ p.2 ∈ D ∧ p.1 - p.2 = r := by
  classical
  let m : ℕ := (Nat.card (BaseField p n)) ^ 2 + (Nat.card (BaseField p n)) + 1
  have hQm : Nat.card (QuotientUnits p n) = m := quotient_card p n
  let e : Multiplicative (ZMod m) ≃* (QuotientUnits p n) :=
    hQm ▸ zmodCyclicMulEquiv (G := (QuotientUnits p n)) (quotient_isCyclic p n)
  let f : ZMod m ≃ (QuotientUnits p n) := Multiplicative.ofAdd.trans e.toEquiv
  let Dset : Set (ZMod m) := {x | f x ∈ singerSet p n}
  have hDcard : Nat.card {x : ZMod m // x ∈ Dset} = (Nat.card (BaseField p n)) + 1 := by
    simpa [Dset] using
      (Nat.card_congr ((f).subtypeEquiv fun x => Iff.rfl)).trans (singerSet_card p n)
  have htranslate :
      ∀ x : ZMod m, x ≠ 0 → ∃! b : ZMod m, b ∈ Dset ∧ x + b ∈ Dset := by
    intro x hx
    have hg : f x ≠ 1 := by
      intro hx1
      apply hx
      apply Multiplicative.ofAdd.injective
      apply e.injective
      simpa [f] using hx1
    rcases singerSet_translate_unique p n (f x) hg with ⟨d, hd, hd_unique⟩
    let b : ZMod m := (e.symm d).toAdd
    refine ⟨b, ?_, ?_⟩
    · constructor
      · change f ((e.symm d).toAdd) ∈ singerSet p n
        simpa [f] using hd.1
      · change f (x + (e.symm d).toAdd) ∈ singerSet p n
        change e (Multiplicative.ofAdd (x + (e.symm d).toAdd)) ∈ singerSet p n
        rw [show Multiplicative.ofAdd (x + (e.symm d).toAdd) =
            Multiplicative.ofAdd x * e.symm d by simp]
        simpa [f] using hd.2
    · intro b' hb'
      apply f.injective
      have hb'' : f b' ∈ singerSet p n ∧ f x * f b' ∈ singerSet p n := by
        refine ⟨hb'.1, ?_⟩
        have hxadd : f (x + b') = f x * f b' := by
          change e (Multiplicative.ofAdd (x + b')) = _
          rw [show Multiplicative.ofAdd (x + b') =
              Multiplicative.ofAdd x * Multiplicative.ofAdd b' by simp]
          simp [f]
        simpa [Dset, hxadd] using hb'.2
      have : f b' = d := hd_unique _ hb''
      simpa [b, f] using this
  let D : Finset (ZMod m) := (Set.toFinite Dset).toFinset
  refine ⟨D, ?_, ?_⟩
  · have hfin : Dset.Finite := Set.toFinite Dset
    calc
      D.card = Fintype.card {x : ZMod m // x ∈ Dset} := by
        simpa [D] using hfin.card_toFinset
      _ = (Nat.card (BaseField p n)) + 1 := by rwa [← Nat.card_eq_fintype_card]
  · intro r hr
    simpa [D, Dset, Set.mem_toFinset] using
      unique_translate_to_unique_difference (A := ZMod m) (D := Dset) htranslate r hr

end SingerConstruction

theorem singer_exists_prime_power (p n : ℕ) [Fact p.Prime] (_hn : n ≠ 0) :
    let q := Nat.card (GaloisField p n)
    let m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by
      have hq : 0 < q := Nat.card_pos
      omega⟩
    Nonempty (SingerDiffSet m (q + 1)) := by
  classical
  dsimp
  obtain ⟨D, hcard, hdiff⟩ := SingerConstruction.singer_exists_zmod (p := p) (n := n)
  refine ⟨{ carrier := D, card_eq := hcard, diff_unique := ?_ }⟩
  intro r hr
  exact hdiff r hr

/-- Singer's theorem: every prime power `q` yields a cyclic
`(q^2 + q + 1, q + 1, 1)` difference set in `ZMod (q^2 + q + 1)`. -/
theorem singer_exists {q : ℕ} (hq : IsPrimePow q) :
    letI m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by omega⟩
    Nonempty (SingerDiffSet m (q + 1)) := by
  classical
  rcases (isPrimePow_nat_iff q).1 hq with ⟨p, n, hp, hnpos, hqpow⟩
  letI : Fact p.Prime := ⟨hp⟩
  let hn : n ≠ 0 := Nat.ne_of_gt hnpos
  simpa [GaloisField.card (p := p) (n := n) hn, hqpow] using
    singer_exists_prime_power (p := p) (n := n) hn

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Combinatorial consequences of Singer difference sets

This file isolates the paper's finite combinatorial step: in a Singer difference set,
unordered pairs are indexed by the cyclic separation `s = 1, ..., (m-1)/2`.
-/

namespace DiameterConstruction

open ZMod

section SingerPairs

variable {m n : ℕ} [NeZero m] (D : SingerDiffSet m n)

omit [NeZero m] in
lemma sub_ne_zero_of_ne {a b : ZMod m} (h : a ≠ b) : a - b ≠ 0 := by
  intro hsub
  exact h (sub_eq_zero.mp hsub)

/-- In a Singer difference set, two ordered pairs with the same nonzero difference coincide. -/
lemma ordered_pair_eq_of_sub_eq
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b)
    (hsub : a - b = c - d) :
    a = c ∧ b = d := by
  let r : ZMod m := a - b
  have hr0 : r ≠ 0 := sub_ne_zero_of_ne hab
  obtain ⟨p, hp, hpuniq⟩ := D.diff_unique r hr0
  have habp : (a, b) = p := by
    apply hpuniq
    exact ⟨ha, hb, by simp [r]⟩
  have hcdp : (c, d) = p := by
    apply hpuniq
    exact ⟨hc, hd, by simpa [r] using hsub.symm⟩
  have hpair : (a, b) = (c, d) := habp.trans hcdp.symm
  simpa [Prod.mk.injEq] using hpair

/-- Equal absolute cyclic separations force equality up to swapping the pair. -/
lemma eq_or_eq_swap_of_natAbs_sub_eq
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b)
    (hsep : (a - b).valMinAbs.natAbs = (c - d).valMinAbs.natAbs) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases (ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs (a := a - b) (b := c - d)).mp hsep with h | h
  · exact Or.inl <| ordered_pair_eq_of_sub_eq (D := D) ha hb hc hd hab h
  · have hswap : a - b = d - c := by
      simpa using h
    exact Or.inr <| ordered_pair_eq_of_sub_eq (D := D) ha hb hd hc hab hswap

end SingerPairs

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Cyclic separation angles and the distance profile

This file packages the cyclic separation parameter attached to a difference in `ZMod m`,
and shows that on a Singer difference set the profile value `G(sepAngle (a - b))`
already distinguishes unordered pairs.
-/

namespace DiameterConstruction

open Real Set ZMod

noncomputable section

/-- The angle attached to a cyclic separation in `ZMod m`, using the closest representative. -/
def sepAngle {m : ℕ} [NeZero m] (r : ZMod m) : ℝ :=
  2 * π * (r.valMinAbs.natAbs : ℝ) / m

lemma sepAngle_nonneg {m : ℕ} [NeZero m] (r : ZMod m) : 0 ≤ sepAngle r := by
  unfold sepAngle
  positivity

lemma sepAngle_le_pi {m : ℕ} [NeZero m] (r : ZMod m) : sepAngle r ≤ π := by
  have hcastNat : (r.valMinAbs.natAbs : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by
    exact_mod_cast r.natAbs_valMinAbs_le
  have htwice : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) ≤ m := by
    exact_mod_cast (Nat.mul_div_le m 2)
  have hcast : (r.valMinAbs.natAbs : ℝ) ≤ (m : ℝ) / 2 := by
    nlinarith
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero <| NeZero.ne m)
  calc
    sepAngle r = (2 * π / m) * (r.valMinAbs.natAbs : ℝ) := by
      unfold sepAngle
      ring
    _ ≤ (2 * π / m) * (m / 2) := by
      gcongr
    _ = π := by
      field_simp [hmpos.ne']

lemma sepAngle_mem_Icc {m : ℕ} [NeZero m] (r : ZMod m) : sepAngle r ∈ Set.Icc 0 π :=
  ⟨sepAngle_nonneg r, sepAngle_le_pi r⟩

lemma sepAngle_pos {m : ℕ} [NeZero m] {r : ZMod m} (hr : r ≠ 0) : 0 < sepAngle r := by
  have hvm : r.valMinAbs ≠ 0 := fun h0 => hr ((ZMod.valMinAbs_eq_zero r).mp h0)
  have hnat : 0 < r.valMinAbs.natAbs := by
    exact Int.natAbs_pos.mpr hvm
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero <| NeZero.ne m)
  have hcoeff : 0 < 2 * π / (m : ℝ) := by
    exact div_pos (mul_pos zero_lt_two Real.pi_pos) hmpos
  calc
    0 < (2 * π / (m : ℝ)) * (r.valMinAbs.natAbs : ℝ) := by
      exact mul_pos hcoeff (by exact_mod_cast hnat)
    _ = sepAngle r := by
      unfold sepAngle
      ring

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Fourier identities for the Erdos counterexample profile

This file establishes the Fourier-series identities that connect the explicit coefficients
from the paper to the profile function `H`:

* the classical identity
  `∑ (1 - cos (n θ)) / n^2 = π θ / 2 - θ^2 / 4` on `[0, 2π]`,
* its odd-frequency part
  `∑ (1 - cos ((2k+1) θ)) / (2k+1)^2 = π θ / 4` on `[0, π]`,
* and the perturbed odd series whose sum is exactly `H`.
-/

namespace DiameterConstruction

open scoped Real Topology
open Real Set

noncomputable section

/-- The perturbed odd coefficients from the paper:
`c₁ = 7/8`, and `c_{2k+1} = 1 / (2k+1)^2` for higher odd frequencies. -/
def perturbedOddCoeff (k : ℕ) : ℝ :=
  if k = 0 then (7 : ℝ) / 8 else 1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)

@[simp] lemma perturbedOddCoeff_zero : perturbedOddCoeff 0 = (7 : ℝ) / 8 := by
  simp [perturbedOddCoeff]

lemma perturbedOddCoeff_pos (k : ℕ) : 0 < perturbedOddCoeff k := by
  by_cases hk : k = 0
  · simp [perturbedOddCoeff, hk]
  · simp [perturbedOddCoeff, hk]
    positivity

lemma cos_inv_sq_hasSum_explicit {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * x))
      (π ^ 2 * (x ^ 2 - x + (1 : ℝ) / 6)) := by
  convert! (hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx) using 1
  have hcoeff :
      ((-1 : ℝ) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ)) = π ^ 2 := by
    norm_num
    ring
  rw [hcoeff]
  change π ^ 2 * (x ^ 2 - x + (1 : ℝ) / 6) = π ^ 2 * bernoulliFun 2 x
  rw [bernoulliFun_two]
  ring

/-- The classical cosine-series identity
`∑ (1 - cos(n θ)) / n^2 = π θ / 2 - θ^2 / 4` on `[0, 2π]`. -/
lemma hasSum_one_sub_cos_div_sq {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) * (1 - Real.cos (n * θ)))
      (π * θ / 2 - θ ^ 2 / 4) := by
  have htwo_pi_pos : 0 < 2 * π := by positivity
  have hx : θ / (2 * π) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hθ.1 (le_of_lt htwo_pi_pos)
    · exact (div_le_iff₀ htwo_pi_pos).2 (by nlinarith [hθ.2])
  have hcos := cos_inv_sq_hasSum_explicit hx
  have hzeta : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  have hsub :
      HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 - (1 / (n : ℝ) ^ 2 * Real.cos (n * θ)))
        (π ^ 2 / 6 - π ^ 2 * ((θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6)) := by
    exact hzeta.sub (hcos.congr_fun fun n => by
      have harg : 2 * π * (n : ℝ) * (θ / (2 * π)) = (n : ℝ) * θ := by
        field_simp [Real.pi_ne_zero]
      simp [harg])
  have hsub' :
      HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) * (1 - Real.cos (n * θ)))
        (π ^ 2 / 6 - π ^ 2 * ((θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6)) := by
    exact hsub.congr_fun (fun n => by ring)
  have hrhs : π ^ 2 / 6 - π ^ 2 * ((θ / (2 * π)) ^ 2 - θ / (2 * π) + 1 / 6) =
      π * θ / 2 - θ ^ 2 / 4 := by
    field_simp [Real.pi_ne_zero]
    ring
  exact hrhs ▸ hsub'

/-- The odd-frequency part of the previous identity:
`∑ (1 - cos((2k+1)θ)) / (2k+1)^2 = π θ / 4` on `[0, π]`. -/
lemma hasSum_odd_one_sub_cos_div_sq {θ : ℝ} (hθ : θ ∈ Set.Icc 0 π) :
    HasSum (fun k : ℕ => (1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) * (1 - Real.cos ((2 * k + 1) * θ)))
      (π * θ / 4) := by
  let f : ℕ → ℝ := fun n => (1 / (n : ℝ) ^ 2) * (1 - Real.cos (n * θ))
  have hall : HasSum f (π * θ / 2 - θ ^ 2 / 4) := by
    simpa [f] using hasSum_one_sub_cos_div_sq (θ := θ) (by
      refine ⟨hθ.1, ?_⟩
      nlinarith [hθ.2, Real.pi_pos])
  have hdouble : HasSum (fun k : ℕ => (1 / 4 : ℝ) * ((1 / (k : ℝ) ^ 2) * (1 - Real.cos (k * (2 * θ)))))
      ((π * θ - θ ^ 2) / 4) := by
    have h2θ : 2 * θ ∈ Set.Icc (0 : ℝ) (2 * π) := by
      constructor
      · nlinarith [hθ.1]
      · nlinarith [hθ.2]
    have hdouble0 :
        HasSum (fun k : ℕ => (1 / 4 : ℝ) * ((1 / (k : ℝ) ^ 2) * (1 - Real.cos (k * (2 * θ)))))
          ((1 / 4 : ℝ) * (π * (2 * θ) / 2 - (2 * θ) ^ 2 / 4)) :=
      (hasSum_one_sub_cos_div_sq (θ := 2 * θ) h2θ).mul_left (1 / 4 : ℝ)
    convert! hdouble0 using 1
    ring
  have heven : HasSum (fun k : ℕ => f (2 * k))
      ((π * θ - θ ^ 2) / 4) := by
    convert! hdouble using 1
    · funext k
      simp [f]
      ring_nf
  have hsodd : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have hs0 : Summable ((fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) ∘ fun k : ℕ => 2 * k + 1) := by
      exact hasSum_zeta_two.summable.comp_injective (fun a b h => by omega)
    have hs : Summable (fun k : ℕ => (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
      simpa [Function.comp_def] using hs0
    refine (hs.mul_left 2).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
    · have hcos : 1 - Real.cos ((2 * k + 1) * θ) ≤ 2 := by
        nlinarith [Real.neg_one_le_cos ((2 * k + 1) * θ)]
      calc
        f (2 * k + 1)
            = (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) * (1 - Real.cos ((2 * k + 1) * θ)) := by
                simp [f]
        _ ≤ (1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)) * 2 := by gcongr
        _ = 2 * (1 / ((((2 * k + 1 : ℕ) : ℝ)) ^ 2)) := by
          ring
  have htsum := tsum_even_add_odd (f := f) heven.summable hsodd
  have hodd_tsum : ∑' k : ℕ, f (2 * k + 1) = π * θ / 4 := by
    rw [hall.tsum_eq, heven.tsum_eq] at htsum
    linarith
  convert! (hsodd.hasSum_iff.mpr hodd_tsum) using 1 with k
  simp [f]

/-- The perturbed odd series from the paper sums to the explicit profile `H`. -/
lemma hasSum_perturbedOddCoeff_profile {θ : ℝ} (hθ : θ ∈ Set.Icc 0 π) :
    HasSum (fun k : ℕ => perturbedOddCoeff k * (1 - Real.cos ((2 * k + 1) * θ))) (H θ) := by
  have hodd := hasSum_odd_one_sub_cos_div_sq hθ
  have h0 :
      (1 / ((2 * 0 + 1 : ℕ) : ℝ) ^ 2) * (1 - Real.cos ((2 * 0 + 1) * θ)) =
        1 - Real.cos θ := by
    norm_num
  convert! hodd.update 0 ((7 : ℝ) / 8 * (1 - Real.cos θ)) using 1
  · funext k
    by_cases hk : k = 0
    · subst hk
      simp [perturbedOddCoeff]
    · simp [perturbedOddCoeff, hk]
  · norm_num
    unfold H
    ring

/-- A `tsum` version of the previous identity. -/
theorem H_eq_tsum_perturbedOddCoeff {θ : ℝ} (hθ : θ ∈ Set.Icc 0 π) :
    H θ = ∑' k : ℕ, perturbedOddCoeff k * (1 - Real.cos ((2 * k + 1) * θ)) :=
  (hasSum_perturbedOddCoeff_profile hθ).tsum_eq.symm

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Euclidean realization of the cyclic profile

This file formalizes the weighted product-of-polygons construction from the paper.
For nonnegative weights `W_1, ..., W_N`, it defines the associated map into
`R^(2N)` and proves the exact squared-distance formula.
-/

namespace DiameterConstruction

open Real

noncomputable section

/-- The `r`-th polygon frequency, indexed from `1` rather than `0`. -/
def polygonFrequency {N : Nat} (r : Fin N) : Nat :=
  r.1 + 1

/-- The amplitude in the `r`-th two-dimensional factor. -/
def polygonAmplitude {N : Nat} (W : Fin N → NNReal) (r : Fin N) : Real :=
  Real.sqrt ((W r : Real) / 2)

/-- The finite weighted squared-distance profile attached to `W`. -/
def polygonSqProfile {N : Nat} (W : Fin N → NNReal) (theta : Real) : Real :=
  ∑ r : Fin N, (W r : Real) * (1 - Real.cos ((polygonFrequency r : Real) * theta))

/-- The weighted product-of-polygons realization at angle parameter `tau`. -/
def polygonPoint {N : Nat} (W : Fin N → NNReal) (tau : Real) :
    EuclideanSpace Real (Fin N × Fin 2) :=
  WithLp.toLp 2 fun p : Fin N × Fin 2 =>
    let amp := polygonAmplitude W p.1
    let theta := (polygonFrequency p.1 : Real) * tau
    if p.2 = 0 then amp * Real.cos theta else amp * Real.sin theta

/-- The same realization, sampled on the `m`-th roots of unity. -/
def cyclicPolygonPoint {N m : Nat} [NeZero m] (W : Fin N → NNReal) (t : ZMod m) :
    EuclideanSpace Real (Fin N × Fin 2) :=
  polygonPoint W (2 * Real.pi * (t.val : Real) / m)

/-- Reindex the `N` two-dimensional factors as a single `Fin (N * 2)` coordinate set. -/
def polygonPointReindex {N : Nat} :
    EuclideanSpace Real (Fin N × Fin 2) ≃ₗᵢ[Real] EuclideanSpace Real (Fin (N * 2)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Real Real finProdFinEquiv

@[simp] lemma polygonPoint_apply_zero {N : Nat} (W : Fin N → NNReal) (tau : Real) (r : Fin N) :
    polygonPoint W tau (r, 0) =
      polygonAmplitude W r * Real.cos ((polygonFrequency r : Real) * tau) := by
  simp [polygonPoint]

@[simp] lemma polygonPoint_apply_one {N : Nat} (W : Fin N → NNReal) (tau : Real) (r : Fin N) :
    polygonPoint W tau (r, 1) =
      polygonAmplitude W r * Real.sin ((polygonFrequency r : Real) * tau) := by
  simp [polygonPoint]

lemma real_dist_sq_eq_sq_sub (x y : Real) : dist x y ^ 2 = (x - y) ^ 2 := by
  rw [Real.dist_eq, sq_abs]

lemma two_coord_sq_sum (amp alpha beta : Real) :
    (amp * Real.cos alpha - amp * Real.cos beta) ^ 2 +
        (amp * Real.sin alpha - amp * Real.sin beta) ^ 2 =
      2 * amp ^ 2 * (1 - Real.cos (alpha - beta)) := by
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq alpha, Real.sin_sq_add_cos_sq beta]

lemma polygonAmplitude_sq {N : Nat} (W : Fin N → NNReal) (r : Fin N) :
    polygonAmplitude W r ^ 2 = (W r : Real) / 2 := by
  unfold polygonAmplitude
  have hnonneg : 0 ≤ ((W r : Real) / 2) := by
    exact div_nonneg (show 0 ≤ (W r : Real) by exact_mod_cast (W r).2) (by norm_num)
  exact Real.sq_sqrt hnonneg

lemma polygonPoint_factor_dist_sq {N : Nat} (W : Fin N → NNReal) (tau sigma : Real)
    (r : Fin N) :
    dist (polygonPoint W tau (r, 0)) (polygonPoint W sigma (r, 0)) ^ 2 +
        dist (polygonPoint W tau (r, 1)) (polygonPoint W sigma (r, 1)) ^ 2 =
      (W r : Real) * (1 - Real.cos ((polygonFrequency r : Real) * (tau - sigma))) := by
  rw [real_dist_sq_eq_sq_sub, real_dist_sq_eq_sq_sub]
  rw [polygonPoint_apply_zero, polygonPoint_apply_zero, polygonPoint_apply_one, polygonPoint_apply_one]
  rw [two_coord_sq_sum]
  rw [polygonAmplitude_sq]
  ring_nf

/-- Squared distances in the weighted polygon realization are given exactly by the
finite Fourier profile attached to the weights. -/
theorem polygonPoint_dist_sq {N : Nat} (W : Fin N → NNReal) (tau sigma : Real) :
    dist (polygonPoint W tau) (polygonPoint W sigma) ^ 2 =
      polygonSqProfile W (tau - sigma) := by
  rw [EuclideanSpace.dist_sq_eq, polygonSqProfile, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Fin.sum_univ_two]
  exact polygonPoint_factor_dist_sq W tau sigma r

/-- The same formula for the `m`-cyclic sampling of the construction. -/
theorem cyclicPolygonPoint_dist_sq {N m : Nat} [NeZero m] (W : Fin N → NNReal)
    (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) W t) (cyclicPolygonPoint (m := m) W u) ^ 2 =
      polygonSqProfile W
        ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)) := by
  simpa [cyclicPolygonPoint] using
    polygonPoint_dist_sq W
      (2 * Real.pi * (t.val : Real) / m) (2 * Real.pi * (u.val : Real) / m)

lemma cos_mul_valMinAbs_eq_cos_mul_sepAngle {m : Nat} [NeZero m] (f : Nat) (r : ZMod m) :
    Real.cos ((f : Real) * (2 * Real.pi * (r.valMinAbs : Real) / m)) =
      Real.cos ((f : Real) * sepAngle r) := by
  by_cases hr : 0 ≤ r.valMinAbs
  · have hcast : ((r.valMinAbs.natAbs : Nat) : Real) = (r.valMinAbs : Real) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hr]
    rw [sepAngle, hcast]
  · have hr' : r.valMinAbs ≤ 0 := le_of_not_ge hr
    have hcast0 : ((r.valMinAbs.natAbs : Nat) : Real) = -(r.valMinAbs : Real) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hr', Int.cast_neg]
    have hcast : (r.valMinAbs : Real) = -((r.valMinAbs.natAbs : Nat) : Real) := by
      linarith
    rw [hcast, sepAngle]
    have hneg :
        (f : Real) * (2 * Real.pi * (-((r.valMinAbs.natAbs : Nat) : Real)) / m) =
          -((f : Real) * (2 * Real.pi * ((r.valMinAbs.natAbs : Nat) : Real) / m)) := by
      ring
    rw [hneg, Real.cos_neg]

lemma cos_mul_raw_sub_eq_cos_mul_sepAngle {m : Nat} [NeZero m] (f : Nat) (t u : ZMod m) :
    Real.cos ((f : Real) *
      ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m))) =
      Real.cos ((f : Real) * sepAngle (t - u)) := by
  let z : Int := (t - u).valMinAbs
  have hz : ((z : Int) : ZMod m) = t - u := by
    simp [z]
  have hzero : (((t.val : Int) - u.val - z : Int) : ZMod m) = 0 := by
    simp [Int.cast_sub, hz, z]
  have hdiv : (m : Int) ∣ ((t.val : Int) - u.val - z) := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  rcases hdiv with ⟨k, hk⟩
  have hkInt : (t.val : Int) - u.val = z + k * m := by
    linarith
  have hkReal : (t.val : Real) - (u.val : Real) = (z : Real) + k * m := by
    exact_mod_cast hkInt
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m)).ne'
  have hangle :
      ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)) =
        2 * Real.pi * (z : Real) / m + (k : Real) * (2 * Real.pi) := by
    calc
      ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m))
          = (2 * Real.pi) * ((t.val : Real) - (u.val : Real)) / m := by ring
      _ = (2 * Real.pi) * ((z : Real) + k * m) / m := by rw [hkReal]
      _ = 2 * Real.pi * (z : Real) / m + (k : Real) * (2 * Real.pi) := by
        field_simp [hm0]
  have hmulcast : (f : Real) * (k : Real) = (((f : Int) * k : Int) : Real) := by
    exact_mod_cast (show (f : Int) * k = (f : Int) * k by rfl)
  calc
    Real.cos ((f : Real) *
        ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)))
        = Real.cos ((f : Real) * (2 * Real.pi * (z : Real) / m) +
            (((f : Int) * k : Int) : Real) * (2 * Real.pi)) := by
            rw [hangle]
            congr 1
            calc
              (f : Real) * (2 * Real.pi * (z : Real) / m + (k : Real) * (2 * Real.pi))
                  = (f : Real) * (2 * Real.pi * (z : Real) / m) +
                      (f : Real) * ((k : Real) * (2 * Real.pi)) := by ring
              _ = (f : Real) * (2 * Real.pi * (z : Real) / m) +
                    (((f : Int) * k : Int) : Real) * (2 * Real.pi) := by
                    rw [show (f : Real) * ((k : Real) * (2 * Real.pi)) =
                        ((f : Real) * (k : Real)) * (2 * Real.pi) by ring, hmulcast]
    _ = Real.cos ((f : Real) * (2 * Real.pi * (z : Real) / m)) := by
      rw [Real.cos_add_int_mul_two_pi]
    _ = Real.cos ((f : Real) * sepAngle (t - u)) := by
      simpa [z] using cos_mul_valMinAbs_eq_cos_mul_sepAngle (m := m) f (t - u)

lemma polygonSqProfile_eq_sepAngle {N m : Nat} [NeZero m] (W : Fin N → NNReal)
    (t u : ZMod m) :
    polygonSqProfile W
        ((2 * Real.pi * (t.val : Real) / m) - (2 * Real.pi * (u.val : Real) / m)) =
      polygonSqProfile W (sepAngle (t - u)) := by
  unfold polygonSqProfile
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [cos_mul_raw_sub_eq_cos_mul_sepAngle (m := m) (f := polygonFrequency r) t u]

/-- The cyclic realization depends only on the intrinsic cyclic separation angle. -/
theorem cyclicPolygonPoint_dist_sq_eq_profile {N m : Nat} [NeZero m] (W : Fin N → NNReal)
    (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) W t) (cyclicPolygonPoint (m := m) W u) ^ 2 =
      polygonSqProfile W (sepAngle (t - u)) := by
  rw [cyclicPolygonPoint_dist_sq (m := m) W t u, polygonSqProfile_eq_sepAngle (m := m) W t u]

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# The discrete profile realized by the Fourier weights

This file packages the paper's specific finite weight family

`W_r = sum_{j odd, j congruent to plus or minus r mod m} c_j`

coming from the perturbed odd Fourier coefficients. It proves that the resulting
weighted polygon profile agrees with `H` on the cyclic grid `sepAngle : ZMod m -> R`,
so the realized Euclidean distances are exactly `G(sepAngle (t - u))`.
-/

namespace DiameterConstruction

open scoped Real Topology
open Real Set ZMod

noncomputable section

/-- The least absolute residue of a natural frequency modulo `m`. -/
def residueNatAbs {m : Nat} [NeZero m] (j : Nat) : Nat :=
  ((j : ZMod m).valMinAbs.natAbs)

/-- The least absolute residue of the odd frequency `2k + 1` modulo `m`. -/
def oddResidueNatAbs {m : Nat} [NeZero m] (k : Nat) : Nat :=
  residueNatAbs (m := m) (2 * k + 1)

lemma residueNatAbs_le_half {m : Nat} [NeZero m] (j : Nat) :
    residueNatAbs (m := m) j <= m / 2 := by
  simpa [residueNatAbs] using (ZMod.natAbs_valMinAbs_le (j : ZMod m))

lemma oddResidueNatAbs_le_half {m : Nat} [NeZero m] (k : Nat) :
    oddResidueNatAbs (m := m) k <= m / 2 := by
  simpa [oddResidueNatAbs] using residueNatAbs_le_half (m := m) (2 * k + 1)

lemma hasSum_two_mul_perturbedOddCoeff :
    HasSum (fun k : Nat => (2 : Real) * perturbedOddCoeff k) (H Real.pi) := by
  have hpi : HasSum (fun k : Nat =>
      perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * Real.pi))) (H Real.pi) := by
    simpa using hasSum_perturbedOddCoeff_profile (θ := Real.pi)
      (show Real.pi ∈ Set.Icc (0 : Real) Real.pi from ⟨Real.pi_pos.le, le_rfl⟩)
  refine hpi.congr_fun ?_
  intro k
  have hcos : Real.cos (((2 * k + 1 : Nat) : Real) * Real.pi) = -1 := by
    rw [Real.cos_nat_mul_pi]
    exact (show Odd (2 * k + 1) from ⟨k, by omega⟩).neg_one_pow
  calc
    (2 : Real) * perturbedOddCoeff k
      = perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * Real.pi)) := by
          rw [hcos]
          ring

/-- The perturbed odd coefficients form a summable series. -/
lemma hasSum_perturbedOddCoeff :
    HasSum perturbedOddCoeff (H Real.pi / 2) := by
  have hscaled := hasSum_two_mul_perturbedOddCoeff.mul_left ((1 : Real) / 2)
  convert! hscaled using 1 with k <;> ring

lemma summable_perturbedOddCoeff : Summable perturbedOddCoeff :=
  hasSum_perturbedOddCoeff.summable

/-- The real weight assigned to the residue class `+-r (mod m)`. -/
def residueClassWeightReal {m : Nat} [NeZero m] (r : Fin (m / 2)) : Real :=
  ∑' k : Nat,
    if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0

/-- The corresponding nonnegative weight used in the Euclidean realization. -/
def residueClassWeight {m : Nat} [NeZero m] (r : Fin (m / 2)) : NNReal :=
  Real.toNNReal (residueClassWeightReal (m := m) r)

lemma summable_residueClassWeightReal_summand {m : Nat} [NeZero m] (r : Fin (m / 2)) :
    Summable (fun k : Nat =>
      if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) := by
  have hnonneg : ∀ k : Nat,
      0 <= if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0 := by
    intro k
    by_cases hk : oddResidueNatAbs (m := m) k = polygonFrequency r
    · simp [hk, (perturbedOddCoeff_pos k).le]
    · simp [hk]
  have hle : ∀ k : Nat,
      (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0)
        <= perturbedOddCoeff k := by
    intro k
    by_cases hk : oddResidueNatAbs (m := m) k = polygonFrequency r
    · simp [hk]
    · simp [hk, (perturbedOddCoeff_pos k).le]
  exact Summable.of_nonneg_of_le hnonneg hle summable_perturbedOddCoeff

lemma residueClassWeightReal_nonneg {m : Nat} [NeZero m] (r : Fin (m / 2)) :
    0 <= residueClassWeightReal (m := m) r := by
  unfold residueClassWeightReal
  refine tsum_nonneg ?_
  intro k
  by_cases hk : oddResidueNatAbs (m := m) k = polygonFrequency r
  · simp [hk, (perturbedOddCoeff_pos k).le]
  · simp [hk]

@[simp] lemma coe_residueClassWeight {m : Nat} [NeZero m] (r : Fin (m / 2)) :
    ((residueClassWeight (m := m) r : NNReal) : Real) = residueClassWeightReal (m := m) r := by
  simp [residueClassWeight, Real.toNNReal_of_nonneg, residueClassWeightReal_nonneg]

/-- The raw angular parameter `2*pi*t/m` attached to `t in ZMod m`. -/
def cyclicRawAngle {m : Nat} [NeZero m] (t : ZMod m) : Real :=
  2 * Real.pi * (t.val : Real) / m

lemma cos_mul_raw_eq_cos_mul_sepAngle {m : Nat} [NeZero m] (f : Nat) (x : ZMod m) :
    Real.cos ((f : Real) * cyclicRawAngle (m := m) x) =
      Real.cos ((f : Real) * sepAngle x) := by
  simpa [cyclicRawAngle] using
    (cos_mul_raw_sub_eq_cos_mul_sepAngle (m := m) (f := f) x 0)

lemma cos_nat_mul_raw_eq_cos_residueNatAbs_mul_raw {m : Nat} [NeZero m]
    (j : Nat) (x : ZMod m) :
    Real.cos ((j : Real) * cyclicRawAngle (m := m) x) =
      Real.cos ((residueNatAbs (m := m) j : Real) * cyclicRawAngle (m := m) x) := by
  let z : Int := ((j : ZMod m).valMinAbs)
  have hz : ((z : Int) : ZMod m) = (j : ZMod m) := by
    simp [z]
  have hzero : (((j : Int) - z : Int) : ZMod m) = 0 := by
    simp [Int.cast_sub, hz, z]
  have hdiv : (m : Int) ∣ ((j : Int) - z) := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  rcases hdiv with ⟨k, hk⟩
  have hkInt : (j : Int) = z + k * m := by
    linarith
  have hkReal : (j : Real) = (z : Real) + k * m := by
    exact_mod_cast hkInt
  have hm0 : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m)).ne'
  have hperiod :
      (j : Real) * cyclicRawAngle (m := m) x =
        (z : Real) * cyclicRawAngle (m := m) x +
          (((k * (x.val : Int)) : Int) : Real) * (2 * Real.pi) := by
    calc
      (j : Real) * cyclicRawAngle (m := m) x
          = ((z : Real) + k * m) * cyclicRawAngle (m := m) x := by
              rw [hkReal]
      _ = (z : Real) * cyclicRawAngle (m := m) x +
            (k : Real) * (m : Real) * cyclicRawAngle (m := m) x := by
            ring
      _ = (z : Real) * cyclicRawAngle (m := m) x +
            (k : Real) * ((x.val : Real) * (2 * Real.pi)) := by
            unfold cyclicRawAngle
            field_simp [hm0]
      _ = (z : Real) * cyclicRawAngle (m := m) x +
            (((k * (x.val : Int)) : Int) : Real) * (2 * Real.pi) := by
            have hcast : (((k * (x.val : Int)) : Int) : Real) = (k : Real) * (x.val : Real) := by
              exact_mod_cast (show (k * (x.val : Int) : Int) = k * (x.val : Int) by rfl)
            rw [hcast]
            ring
  calc
    Real.cos ((j : Real) * cyclicRawAngle (m := m) x)
        = Real.cos ((z : Real) * cyclicRawAngle (m := m) x +
            (((k * (x.val : Int)) : Int) : Real) * (2 * Real.pi)) := by
            rw [hperiod]
    _ = Real.cos ((z : Real) * cyclicRawAngle (m := m) x) := by
      rw [Real.cos_add_int_mul_two_pi]
    _ = Real.cos ((residueNatAbs (m := m) j : Real) * cyclicRawAngle (m := m) x) := by
      by_cases hz' : 0 <= z
      · have hcast : ((residueNatAbs (m := m) j : Nat) : Real) = (z : Real) := by
          simpa [residueNatAbs, z] using
            (show ((z.natAbs : Nat) : Real) = (z : Real) by
              rw [← Int.cast_natCast, Int.natAbs_of_nonneg hz'])
        rw [hcast]
      · have hz'' : z <= 0 := le_of_not_ge hz'
        have hcast : ((residueNatAbs (m := m) j : Nat) : Real) = -(z : Real) := by
          simpa [residueNatAbs, z] using
            (show ((z.natAbs : Nat) : Real) = -(z : Real) by
              rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hz'', Int.cast_neg])
        rw [hcast]
        have hneg :
            (-(z : Real)) * cyclicRawAngle (m := m) x =
              -((z : Real) * cyclicRawAngle (m := m) x) := by
          ring
        rw [hneg, Real.cos_neg]

lemma cos_nat_mul_sepAngle_eq_cos_residueNatAbs_mul_sepAngle {m : Nat} [NeZero m]
    (j : Nat) (x : ZMod m) :
    Real.cos ((j : Real) * sepAngle x) =
      Real.cos ((residueNatAbs (m := m) j : Real) * sepAngle x) := by
  calc
    Real.cos ((j : Real) * sepAngle x)
        = Real.cos ((j : Real) * cyclicRawAngle (m := m) x) := by
            symm
            exact cos_mul_raw_eq_cos_mul_sepAngle (m := m) j x
    _ = Real.cos ((residueNatAbs (m := m) j : Real) * cyclicRawAngle (m := m) x) := by
          exact cos_nat_mul_raw_eq_cos_residueNatAbs_mul_raw (m := m) j x
    _ = Real.cos ((residueNatAbs (m := m) j : Real) * sepAngle x) := by
          exact cos_mul_raw_eq_cos_mul_sepAngle (m := m) (residueNatAbs (m := m) j) x

lemma polygonFrequency_injective {N : Nat} :
    Function.Injective (@polygonFrequency N) := by
  intro r s h
  apply Fin.ext
  have h' : Nat.succ r.1 = Nat.succ s.1 := by
    simpa [polygonFrequency, Nat.succ_eq_add_one] using h
  exact Nat.succ.inj h'

lemma sum_if_eq_polygonFrequency {m : Nat} (n : Nat) (hn : n <= m / 2) (a : Real) :
    ∑ r : Fin (m / 2), (if n = polygonFrequency r then a else 0) =
      if n = 0 then 0 else a := by
  classical
  by_cases hn0 : n = 0
  · simp [hn0, polygonFrequency]
  · let r0 : Fin (m / 2) := ⟨n - 1, by omega⟩
    have hr0 : polygonFrequency r0 = n := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      dsimp [polygonFrequency, r0]
      omega
    rw [Finset.sum_eq_single r0]
    · simp [hr0, hn0]
    · intro r _ hrne
      by_cases hEq : n = polygonFrequency r
      · exfalso
        apply hrne
        exact polygonFrequency_injective (by simpa [hr0] using hEq.symm)
      · simp [hEq]
    · intro hr0mem
      simp at hr0mem

lemma sum_residueClassContribution {m : Nat} [NeZero m] (x : ZMod m) (k : Nat) :
    ∑ r : Fin (m / 2),
      (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) *
        (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x)) =
      perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
  let residue := oddResidueNatAbs (m := m) k
  let target :=
    perturbedOddCoeff k * (1 - Real.cos ((residue : Real) * sepAngle x))
  have hsum :
      ∑ r : Fin (m / 2),
        (if residue = polygonFrequency r then perturbedOddCoeff k else 0) *
          (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x)) =
        if residue = 0 then 0 else target := by
    calc
      ∑ r : Fin (m / 2),
          (if residue = polygonFrequency r then perturbedOddCoeff k else 0) *
            (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
          =
            ∑ r : Fin (m / 2),
              if residue = polygonFrequency r then target else 0 := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                by_cases hmatch : residue = polygonFrequency r
                · simp [hmatch, target]
                · simp [hmatch]
      _ = if residue = 0 then 0 else target := by
            exact sum_if_eq_polygonFrequency (n := residue)
              (hn := oddResidueNatAbs_le_half (m := m) k) target
  have htarget :
      target =
        perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
    unfold target residue oddResidueNatAbs
    congr 2
    symm
    exact cos_nat_mul_sepAngle_eq_cos_residueNatAbs_mul_sepAngle (m := m) (2 * k + 1) x
  calc
    ∑ r : Fin (m / 2),
        (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) *
          (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
      = if oddResidueNatAbs (m := m) k = 0 then 0 else target := by
          simpa [residue] using hsum
    _ = target := by
          by_cases hzero : oddResidueNatAbs (m := m) k = 0
          · simp [residue, target, hzero]
          · simp [hzero]
    _ = perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
          exact htarget

/-- The polygon profile coming from the grouped Fourier weights agrees with the
perturbed odd Fourier series on the cyclic grid. -/
theorem polygonSqProfile_residueClassWeight_eq_tsum {m : Nat} [NeZero m] (x : ZMod m) :
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x) =
      ∑' k : Nat, perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
  let g : Fin (m / 2) -> Nat -> Real := fun r k =>
    (if oddResidueNatAbs (m := m) k = polygonFrequency r then perturbedOddCoeff k else 0) *
      (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
  have hs :
      ∀ r ∈ (Finset.univ : Finset (Fin (m / 2))), Summable (g r) := by
    intro r hr
    unfold g
    exact (summable_residueClassWeightReal_summand (m := m) r).mul_right
      (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))
  calc
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x)
        = ∑ r : Fin (m / 2), ∑' k : Nat, g r k := by
            unfold polygonSqProfile
            refine Finset.sum_congr rfl ?_
            intro r hr
            unfold g
            simpa [residueClassWeightReal] using
              ((summable_residueClassWeightReal_summand (m := m) r).tsum_mul_right
                (1 - Real.cos ((polygonFrequency r : Real) * sepAngle x))).symm
    _ = ∑' k : Nat, ∑ r : Fin (m / 2), g r k := by
          symm
          exact Summable.tsum_finsetSum hs
    _ = ∑' k : Nat, perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) := by
          refine tsum_congr ?_
          intro k
          simpa [g] using sum_residueClassContribution (m := m) x k

/-- On the cyclic grid, the weighted polygon profile is exactly the explicit profile `H`. -/
theorem polygonSqProfile_residueClassWeight_eq_H {m : Nat} [NeZero m] (x : ZMod m) :
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x) = H (sepAngle x) := by
  have htheta : sepAngle x ∈ Set.Icc 0 Real.pi := sepAngle_mem_Icc x
  calc
    polygonSqProfile (residueClassWeight (m := m)) (sepAngle x)
      = ∑' k : Nat, perturbedOddCoeff k * (1 - Real.cos (((2 * k + 1 : Nat) : Real) * sepAngle x)) :=
          polygonSqProfile_residueClassWeight_eq_tsum (m := m) x
    _ = H (sepAngle x) := by
          simpa using (H_eq_tsum_perturbedOddCoeff htheta).symm

/-- The concrete cyclic Euclidean realization attached to the Fourier weights has
squared distances given exactly by `H`. -/
theorem cyclicResiduePoint_dist_sq_eq_H {m : Nat} [NeZero m] (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u) ^ 2 =
        H (sepAngle (t - u)) := by
  rw [cyclicPolygonPoint_dist_sq_eq_profile (m := m) (W := residueClassWeight (m := m)) t u,
    polygonSqProfile_residueClassWeight_eq_H (m := m) (x := t - u)]

/-- The same concrete realization has distances given exactly by `G`. -/
theorem cyclicResiduePoint_dist_eq_G {m : Nat} [NeZero m] (t u : ZMod m) :
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u) =
        G (sepAngle (t - u)) := by
  calc
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
        (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u)
        =
          Real.sqrt
            (dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t)
              (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) u) ^ 2) := by
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]
    _ = Real.sqrt (H (sepAngle (t - u))) := by
          rw [cyclicResiduePoint_dist_sq_eq_H (m := m) t u]
    _ = G (sepAngle (t - u)) := by
          rfl

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Scaling the discrete realization

This file formalizes the exact finite scaling argument:

* the distances `d_s = G(2 * pi * s / m)` form a strictly increasing sequence whose
  smallest gap is the last one,
* scaling by the reciprocal of that last gap makes all distinct realized distances at
  least `1` apart,
* for every prime power `q`, the Singer realization therefore gives an exact finite
  counterexample configuration,
* and the diameter of the scaled point set is identified exactly with the top grid
  distance, both before and after reindexing into the paper's ambient dimension.
-/

namespace DiameterConstruction

open scoped Real Topology
open Real Set ZMod

noncomputable section

/-- The `s`-th grid distance `d_s = G(2 * pi * s / m)`. -/
def gridDist {m : Nat} [NeZero m] (s : Nat) : Real :=
  G (2 * Real.pi * s / m)

/-- The forward gap `d_(s + 1) - d_s`. -/
def gridGap {m : Nat} [NeZero m] (s : Nat) : Real :=
  gridDist (m := m) (s + 1) - gridDist (m := m) s

/-- The last forward gap, i.e. the smallest one in the paper. -/
def lastGap {m : Nat} [NeZero m] : Real :=
  gridGap (m := m) (m / 2 - 1)

/-- Scaling by the reciprocal of the smallest gap normalizes all distinct realized
distances to be at least `1` apart. -/
def scaleFactor {m : Nat} [NeZero m] : Real :=
  1 / lastGap (m := m)

/-- The scaled concrete realization used in the final counterexample. -/
def scaledResiduePoint {m : Nat} [NeZero m] (t : ZMod m) :
    EuclideanSpace Real (Prod (Fin (m / 2)) (Fin 2)) :=
  scaleFactor (m := m) •
    cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) t

lemma sepAngle_natCast {m : Nat} [NeZero m] {s : Nat} (hs : s <= m / 2) :
    sepAngle ((s : Nat) : ZMod m) = 2 * Real.pi * s / m := by
  unfold sepAngle
  rw [ZMod.valMinAbs_natCast_of_le_half hs]
  simp

lemma gridAngle_mem_Icc {m : Nat} [NeZero m] {s : Nat} (hs : s <= m / 2) :
    2 * Real.pi * s / m ∈ Set.Icc (0 : Real) Real.pi := by
  rw [← sepAngle_natCast (m := m) hs]
  exact sepAngle_mem_Icc ((s : Nat) : ZMod m)

lemma gridDist_nonneg {m : Nat} [NeZero m] (s : Nat) : 0 <= gridDist (m := m) s := by
  exact G_nonneg _

lemma gridAngle_strictMono {m : Nat} [NeZero m] {s t : Nat}
    (_ht : t <= m / 2) (hst : s < t) :
    2 * Real.pi * s / m < 2 * Real.pi * t / m := by
  have hcoeff : 0 < 2 * Real.pi / (m : Real) := by
    have hmpos : (0 : Real) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    exact div_pos (mul_pos zero_lt_two Real.pi_pos) hmpos
  calc
    2 * Real.pi * s / m = (2 * Real.pi / (m : Real)) * s := by ring
    _ < (2 * Real.pi / (m : Real)) * t := by
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hst) hcoeff
    _ = 2 * Real.pi * t / m := by ring

lemma gridDist_strictMono {m : Nat} [NeZero m] {s t : Nat}
    (hs : s <= m / 2) (ht : t <= m / 2) (hst : s < t) :
    gridDist (m := m) s < gridDist (m := m) t := by
  exact G_strictMonoOn (gridAngle_mem_Icc (m := m) hs) (gridAngle_mem_Icc (m := m) ht)
    (gridAngle_strictMono (m := m) ht hst)

lemma gridGap_strictDecreasing {m : Nat} [NeZero m] {s : Nat}
    (_hs1 : 1 <= s) (hs3 : s + 2 <= m / 2) :
    gridGap (m := m) (s + 1) < gridGap (m := m) s := by
  have hs0 : s <= m / 2 := by
    omega
  have hs2 : s + 1 <= m / 2 := by
    omega
  have hs4 : s + 1 + 1 <= m / 2 := by
    omega
  have hdecr :=
    G_gaps_decreasing
      (a := 2 * Real.pi * ((s : Nat) : Real) / m)
      (b := 2 * Real.pi * ((s + 1 : Nat) : Real) / m)
      (c := 2 * Real.pi * ((s + 1 + 1 : Nat) : Real) / m)
      (gridAngle_mem_Icc (m := m) hs0)
      (gridAngle_mem_Icc (m := m) hs4)
      (gridAngle_strictMono (m := m) (s := s) (t := s + 1) hs2 (by omega))
      (gridAngle_strictMono (m := m) (s := s + 1) (t := s + 1 + 1) hs4 (by omega))
      (by
        have hm0 : (m : Real) ≠ 0 := by
          exact_mod_cast (NeZero.ne m)
        field_simp [hm0]
        norm_num [Nat.cast_add])
  simpa [gridGap, gridDist, Nat.add_assoc] using hdecr

lemma lastGap_le_gridGap {m : Nat} [NeZero m] {s : Nat}
    (hs1 : 1 <= s) (hs2 : s + 1 <= m / 2) :
    lastGap (m := m) <= gridGap (m := m) s := by
  let N : Nat := m / 2
  suffices haux :
      ∀ k s : Nat, 1 <= s -> s + 1 <= N -> s + k = N - 1 ->
        lastGap (m := m) <= gridGap (m := m) s by
    have hk : s + ((N - 1) - s) = N - 1 := by
      omega
    exact haux ((N - 1) - s) s hs1 (by simpa [N] using hs2) hk
  intro k
  induction k with
  | zero =>
      intro s hs1 hs2 hk
      have hs : s = N - 1 := by
        omega
      simp [lastGap, gridGap, N, hs]
  | succ k ih =>
      intro s hs1 hs2 hk
      have hs3 : s + 2 <= N := by
        omega
      have hstep : gridGap (m := m) (s + 1) < gridGap (m := m) s := by
        simpa [N] using gridGap_strictDecreasing (m := m) hs1 hs3
      have hk' : (s + 1) + k = N - 1 := by
        omega
      have hs1' : 1 <= s + 1 := by
        omega
      have hs2' : (s + 1) + 1 <= N := by
        omega
      have ih' : lastGap (m := m) <= gridGap (m := m) (s + 1) := by
        exact ih (s + 1) hs1' hs2' hk'
      exact le_trans ih' hstep.le

lemma lastGap_le_gridDist_diff {m : Nat} [NeZero m] {s t : Nat}
    (hs1 : 1 <= s) (ht : t <= m / 2) (hst : s < t) :
    lastGap (m := m) <= gridDist (m := m) t - gridDist (m := m) s := by
  have hs2 : s + 1 <= m / 2 := by
    omega
  have hgap : lastGap (m := m) <= gridGap (m := m) s :=
    lastGap_le_gridGap (m := m) hs1 hs2
  have hnext_le : gridDist (m := m) (s + 1) <= gridDist (m := m) t := by
    by_cases hEq : s + 1 = t
    · simp [hEq]
    · have hlt : s + 1 < t := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hst) hEq
      exact le_of_lt (gridDist_strictMono (m := m) hs2 ht hlt)
  have hdiff : gridGap (m := m) s <= gridDist (m := m) t - gridDist (m := m) s := by
    unfold gridGap
    linarith
  exact le_trans hgap hdiff

lemma lastGap_pos {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    0 < lastGap (m := m) := by
  have hmono :
      gridDist (m := m) (m / 2 - 1) < gridDist (m := m) (m / 2) := by
    apply gridDist_strictMono (m := m)
    · omega
    · exact le_rfl
    · omega
  have hsucc : m / 2 - 1 + 1 = m / 2 := by
    omega
  have hsub : 0 < gridDist (m := m) (m / 2) - gridDist (m := m) (m / 2 - 1) := by
    exact sub_pos.mpr hmono
  simpa [lastGap, gridGap, hsucc] using hsub

lemma scaleFactor_pos {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    0 < scaleFactor (m := m) := by
  unfold scaleFactor
  exact one_div_pos.mpr (lastGap_pos (m := m) hN)

lemma scaleFactor_nonneg {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    0 <= scaleFactor (m := m) := by
  exact (scaleFactor_pos (m := m) hN).le

lemma residuePoint_dist_eq_gridDist {m : Nat} [NeZero m] (a b : ZMod m) :
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
        (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) =
      gridDist (m := m) ((a - b).valMinAbs.natAbs) := by
  unfold gridDist
  rw [cyclicResiduePoint_dist_eq_G]
  rfl

lemma scaledResiduePoint_dist_eq {m : Nat} [NeZero m] (hN : 2 <= m / 2) (a b : ZMod m) :
    dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) =
      scaleFactor (m := m) *
        dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) := by
  unfold scaledResiduePoint
  rw [dist_smul₀, Real.norm_of_nonneg (scaleFactor_nonneg (m := m) hN)]

lemma scaledResiduePoint_injective {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    Function.Injective (scaledResiduePoint (m := m)) := by
  intro a b hab
  by_contra hne
  have hdist0 : dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) = 0 := by
    simp [hab]
  have hdistpos :
      0 < dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) := by
    rw [scaledResiduePoint_dist_eq (m := m) hN a b]
    have hraw :
        0 <
          dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
            (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) := by
      rw [cyclicResiduePoint_dist_eq_G]
      exact G_pos (sepAngle_pos (sub_ne_zero_of_ne hne)) (sepAngle_le_pi _)
    exact mul_pos (scaleFactor_pos (m := m) hN) hraw
  exact (ne_of_gt hdistpos) hdist0

lemma residuePoint_dist_gap_ge_lastGap
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    lastGap (m := m) <=
      |dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) -
        dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) c)
          (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) d)| := by
  let s1 : Nat := (a - b).valMinAbs.natAbs
  let s2 : Nat := (c - d).valMinAbs.natAbs
  have hs1pos : 1 <= s1 := by
    exact Nat.succ_le_of_lt <| Int.natAbs_pos.mpr <| by
      exact (ZMod.valMinAbs_eq_zero (a - b)).not.mpr (sub_ne_zero_of_ne hab)
  have hs2pos : 1 <= s2 := by
    exact Nat.succ_le_of_lt <| Int.natAbs_pos.mpr <| by
      exact (ZMod.valMinAbs_eq_zero (c - d)).not.mpr (sub_ne_zero_of_ne hcd)
  have hs1le : s1 <= m / 2 := by
    simpa [s1] using ZMod.natAbs_valMinAbs_le (a - b)
  have hs2le : s2 <= m / 2 := by
    simpa [s2] using ZMod.natAbs_valMinAbs_le (c - d)
  have hsneq : s1 ≠ s2 := by
    intro hs
    exact hpair <|
      eq_or_eq_swap_of_natAbs_sub_eq (D := D) ha hb hc hd hab <| by
        simpa [s1, s2] using hs
  rcases lt_or_gt_of_ne hsneq with hlt | hgt
  · have hgap : lastGap (m := m) <= gridDist (m := m) s2 - gridDist (m := m) s1 :=
      lastGap_le_gridDist_diff (m := m) hs1pos hs2le hlt
    have hmono : gridDist (m := m) s1 < gridDist (m := m) s2 :=
      gridDist_strictMono (m := m) hs1le hs2le hlt
    rw [residuePoint_dist_eq_gridDist (m := m) a b, residuePoint_dist_eq_gridDist (m := m) c d]
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hmono.le)]
    exact hgap
  · have hgap : lastGap (m := m) <= gridDist (m := m) s1 - gridDist (m := m) s2 :=
      lastGap_le_gridDist_diff (m := m) hs2pos hs1le hgt
    have hmono : gridDist (m := m) s2 < gridDist (m := m) s1 :=
      gridDist_strictMono (m := m) hs2le hs1le hgt
    rw [residuePoint_dist_eq_gridDist (m := m) a b, residuePoint_dist_eq_gridDist (m := m) c d]
    rw [abs_of_nonneg (sub_nonneg.mpr hmono.le)]
    exact hgap

lemma scaledResiduePoint_dist_gap_ge_one
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    1 <=
      |dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) -
        dist (scaledResiduePoint (m := m) c) (scaledResiduePoint (m := m) d)| := by
  let A : Real :=
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b)
  let B : Real :=
    dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) c)
      (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) d)
  have hgap :
      lastGap (m := m) <= |A - B| := by
    simpa [A, B] using
      residuePoint_dist_gap_ge_lastGap (m := m) D ha hb hc hd hab hcd hpair
  have hscale1 := scaledResiduePoint_dist_eq (m := m) hN a b
  have hscale2 := scaledResiduePoint_dist_eq (m := m) hN c d
  have hscale_nonneg : 0 <= scaleFactor (m := m) := scaleFactor_nonneg (m := m) hN
  have hlast_ne : lastGap (m := m) ≠ 0 := (lastGap_pos (m := m) hN).ne'
  have hone : 1 = scaleFactor (m := m) * lastGap (m := m) := by
    rw [scaleFactor]
    exact (one_div_mul_cancel hlast_ne).symm
  have hscaled_abs :
      |dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) -
        dist (scaledResiduePoint (m := m) c) (scaledResiduePoint (m := m) d)| =
      scaleFactor (m := m) * |A - B| := by
    rw [hscale1, hscale2]
    change
      |scaleFactor (m := m) * A - scaleFactor (m := m) * B| =
        scaleFactor (m := m) * |A - B|
    calc
      |scaleFactor (m := m) * A - scaleFactor (m := m) * B|
          = |scaleFactor (m := m) * (A - B)| := by
              congr 1
              ring
      _ = |scaleFactor (m := m)| * |A - B| := by
            rw [abs_mul]
      _ = scaleFactor (m := m) * |A - B| := by
            rw [abs_of_nonneg hscale_nonneg]
  calc
    1 = scaleFactor (m := m) * lastGap (m := m) := hone
    _ <= scaleFactor (m := m) * |A - B| := by
      exact mul_le_mul_of_nonneg_left hgap hscale_nonneg
    _ =
        |dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) -
          dist (scaledResiduePoint (m := m) c) (scaledResiduePoint (m := m) d)| := by
            exact hscaled_abs.symm

lemma scaledResiduePoint_dist_le_top
    {m : Nat} [NeZero m] (hN : 2 <= m / 2) (a b : ZMod m) :
    dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) <=
      scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  rw [scaledResiduePoint_dist_eq (m := m) hN a b]
  refine mul_le_mul_of_nonneg_left ?_ (scaleFactor_nonneg (m := m) hN)
  by_cases hab : a = b
  · simp [hab, gridDist_nonneg]
  · rw [residuePoint_dist_eq_gridDist (m := m) a b]
    let s : Nat := (a - b).valMinAbs.natAbs
    have hsle : s <= m / 2 := by
      simpa [s] using ZMod.natAbs_valMinAbs_le (a - b)
    rcases eq_or_lt_of_le hsle with hsEq | hslt
    · simp [s, hsEq]
    · exact le_of_lt (gridDist_strictMono (m := m) hsle (le_rfl : m / 2 <= m / 2) hslt)

lemma topSeparation_nonzero {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    (((m / 2 : Nat) : ZMod m)) ≠ 0 := by
  intro hzero
  have hdiv : m ∣ m / 2 := (ZMod.natCast_eq_zero_iff (m / 2) m).1 hzero
  rcases hdiv with ⟨k, hk⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    have hhalf_zero : m / 2 = 0 := by simpa [hkzero] using hk
    omega
  have hkone : 1 <= k := Nat.succ_le_of_lt hkpos
  have hm_le_half : m <= m / 2 := by
    calc
      m = m * 1 := by rw [Nat.mul_one]
      _ <= m * k := Nat.mul_le_mul_left m hkone
      _ = m / 2 := hk.symm
  have hhalf_lt : m / 2 < m := Nat.div_lt_self hmpos (by omega)
  exact (Nat.not_le_of_gt hhalf_lt) hm_le_half

lemma scaledResiduePoint_exists_top_distance
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n) :
    ∃ a ∈ D.carrier, ∃ b ∈ D.carrier,
      dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) =
        scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  have hr0 : (((m / 2 : Nat) : ZMod m)) ≠ 0 := topSeparation_nonzero (m := m) hN
  obtain ⟨p, hp, _⟩ := D.diff_unique ((m / 2 : Nat) : ZMod m) hr0
  rcases p with ⟨a, b⟩
  rcases hp with ⟨ha, hb, hab⟩
  refine ⟨a, ha, b, hb, ?_⟩
  have hs :
      ((a - b).valMinAbs.natAbs) = m / 2 := by
    rw [hab]
    rw [ZMod.valMinAbs_natCast_of_le_half (le_rfl : m / 2 ≤ m / 2)]
    exact Int.natAbs_natCast _
  calc
    dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) =
        scaleFactor (m := m) *
          dist (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) a)
            (cyclicPolygonPoint (m := m) (residueClassWeight (m := m)) b) := by
          exact scaledResiduePoint_dist_eq (m := m) hN a b
    _ = scaleFactor (m := m) * gridDist (m := m) ((a - b).valMinAbs.natAbs) := by
          rw [residuePoint_dist_eq_gridDist (m := m) a b]
    _ = scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
          rw [hs]

/-- The scaled realization reindexed as a point in `R^(2 * floor(m / 2))`. -/
def scaledResiduePointFin {m : Nat} [NeZero m] (t : ZMod m) :
    EuclideanSpace Real (Fin ((m / 2) * 2)) :=
  polygonPointReindex (scaledResiduePoint (m := m) t)

lemma scaledResiduePointFin_dist_eq {m : Nat} [NeZero m] (a b : ZMod m) :
    dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) =
      dist (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b) := by
  rw [scaledResiduePointFin]
  exact (polygonPointReindex (N := m / 2)).dist_map
    (scaledResiduePoint (m := m) a) (scaledResiduePoint (m := m) b)

lemma scaledResiduePointFin_injective {m : Nat} [NeZero m] (hN : 2 <= m / 2) :
    Function.Injective (scaledResiduePointFin (m := m)) := by
  exact (polygonPointReindex (N := m / 2)).injective.comp
    (scaledResiduePoint_injective (m := m) hN)

lemma scaledResiduePointFin_dist_gap_ge_one
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n)
    {a b c d : ZMod m}
    (ha : a ∈ D.carrier) (hb : b ∈ D.carrier)
    (hc : c ∈ D.carrier) (hd : d ∈ D.carrier)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    1 <=
      |dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) -
        dist (scaledResiduePointFin (m := m) c) (scaledResiduePointFin (m := m) d)| := by
  simpa [scaledResiduePointFin_dist_eq (m := m) a b, scaledResiduePointFin_dist_eq (m := m) c d]
    using scaledResiduePoint_dist_gap_ge_one (m := m) hN D ha hb hc hd hab hcd hpair

lemma scaledResiduePointFin_dist_le_top
    {m : Nat} [NeZero m] (hN : 2 <= m / 2) (a b : ZMod m) :
    dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) <=
      scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  simpa [scaledResiduePointFin_dist_eq (m := m) a b] using
    scaledResiduePoint_dist_le_top (m := m) hN a b

/-- The scaled Singer configuration in the reindexed Euclidean space `R^(2 * floor(m / 2))`. -/
def scaledSingerPointSetFin {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    Set (EuclideanSpace Real (Fin ((m / 2) * 2))) :=
  scaledResiduePointFin (m := m) '' (D.carrier : Set (ZMod m))

lemma scaledSingerPointSetFin_bounded
    {m n : Nat} [NeZero m] (D : SingerDiffSet m n) :
    Bornology.IsBounded (scaledSingerPointSetFin (m := m) D) := by
  apply Set.Finite.isBounded
  simpa [scaledSingerPointSetFin] using
    (Finset.finite_toSet D.carrier).image (scaledResiduePointFin (m := m))

lemma scaledResiduePointFin_exists_top_distance
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n) :
    ∃ a ∈ D.carrier, ∃ b ∈ D.carrier,
      dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) =
        scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  obtain ⟨a, ha, b, hb, hdist⟩ := scaledResiduePoint_exists_top_distance (m := m) hN D
  refine ⟨a, ha, b, hb, ?_⟩
  simpa [scaledResiduePointFin_dist_eq (m := m) a b] using hdist

lemma scaledResiduePointFin_diam_eq_top
    {m n : Nat} [NeZero m] (hN : 2 <= m / 2) (D : SingerDiffSet m n) :
    Metric.diam (scaledSingerPointSetFin (m := m) D) =
      scaleFactor (m := m) * gridDist (m := m) (m / 2) := by
  refine le_antisymm ?_ ?_
  · refine Metric.diam_le_of_forall_dist_le
      (mul_nonneg (scaleFactor_nonneg (m := m) hN) (gridDist_nonneg (m := m) (m / 2))) ?_
    intro x hx y hy
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    exact scaledResiduePointFin_dist_le_top (m := m) hN a b
  · obtain ⟨a, ha, b, hb, hdist⟩ := scaledResiduePointFin_exists_top_distance (m := m) hN D
    have hmema : scaledResiduePointFin (m := m) a ∈ scaledSingerPointSetFin (m := m) D :=
      ⟨a, ha, rfl⟩
    have hmemb : scaledResiduePointFin (m := m) b ∈ scaledSingerPointSetFin (m := m) D :=
      ⟨b, hb, rfl⟩
    calc
      scaleFactor (m := m) * gridDist (m := m) (m / 2) =
          dist (scaledResiduePointFin (m := m) a) (scaledResiduePointFin (m := m) b) := by
            exact hdist.symm
      _ <= Metric.diam (scaledSingerPointSetFin (m := m) D) := by
            exact Metric.dist_le_diam_of_mem (scaledSingerPointSetFin_bounded (m := m) D)
              hmema hmemb

/-- Exact finite counterexample theorem, now reindexed into `R^(2 * floor(m / 2))`. -/
theorem primePower_counterexample_fin
    {q : Nat} (hq : IsPrimePow q) :
    let m := q ^ 2 + q + 1
    letI : NeZero m := ⟨by
      have hq2 : 2 <= q := hq.two_le
      omega⟩
    ∃ D : SingerDiffSet m (q + 1),
      let p := scaledResiduePointFin (m := m)
      Function.Injective p ∧
      (∀ {a b c d : ZMod m},
        a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
        a ≠ b → c ≠ d →
        ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
          1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
      (∀ a ∈ D.carrier, ∀ b ∈ D.carrier,
        dist (p a) (p b) <= scaleFactor (m := m) * gridDist (m := m) (m / 2)) := by
  classical
  dsimp
  have hq2 : 2 <= q := hq.two_le
  have hqq : 4 <= q * q := by
    simpa using Nat.mul_le_mul hq2 hq2
  have hm4 : 4 <= q ^ 2 + q + 1 := by
    rw [pow_two]
    omega
  have hN : 2 <= (q ^ 2 + q + 1) / 2 := by
    exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)
  obtain ⟨D⟩ := singer_exists hq
  refine ⟨D, scaledResiduePointFin_injective (m := q ^ 2 + q + 1) hN, ?_, ?_⟩
  · intro a b c d ha hb hc hd hab hcd hpair
    exact
      scaledResiduePointFin_dist_gap_ge_one
        (m := q ^ 2 + q + 1) hN D ha hb hc hd hab hcd hpair
  · intro a ha b hb
    exact scaledResiduePointFin_dist_le_top (m := q ^ 2 + q + 1) hN a b

lemma primePower_reindexed_dim (q : Nat) :
    ((q ^ 2 + q + 1) / 2) * 2 = q ^ 2 + q := by
  have hfactor : q ^ 2 + q = q * (q + 1) := by
    calc
      q ^ 2 + q = q * q + q * 1 := by rw [pow_two, Nat.mul_one]
      _ = q * (q + 1) := by rw [Nat.mul_add]
  have hEven : 2 ∣ q ^ 2 + q := by
    by_cases hqEven : 2 ∣ q
    · rw [hfactor]
      exact dvd_mul_of_dvd_left hqEven (q + 1)
    · have hq1 : 2 ∣ q + 1 := by
        rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
        · exact False.elim <| hqEven (Nat.dvd_of_mod_eq_zero h0)
        · exact Nat.dvd_of_mod_eq_zero (by omega)
      rw [hfactor]
      exact dvd_mul_of_dvd_right hq1 q
  rcases hEven with ⟨k, hk⟩
  rw [hk]
  omega

lemma primePower_ambientDim_eq_n (q : Nat) :
    ((q ^ 2 + q + 1) / 2) * 2 = (q + 1) ^ 2 - (q + 1) := by
  calc
    ((q ^ 2 + q + 1) / 2) * 2 = q ^ 2 + q := primePower_reindexed_dim q
    _ = (q + 1) ^ 2 - (q + 1) := by
      calc
        q ^ 2 + q = (q + 1) * q := by
          rw [Nat.succ_mul, pow_two]
        _ = (q + 1) ^ 2 - (q + 1) := by
          rw [pow_two, Nat.mul_succ, Nat.add_sub_cancel]

/-- Exact finite counterexample theorem in the paper's ambient dimension `R^(n^2 - n)`,
with the exact diameter formula included. -/
theorem primePower_counterexample_exactDimension_with_diam
    {q : Nat} (hq : IsPrimePow q) :
    ∃ D : SingerDiffSet (q ^ 2 + q + 1) (q + 1),
      ∃ p : ZMod (q ^ 2 + q + 1) →
          EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))),
        Function.Injective p ∧
        (∀ {a b c d : ZMod (q ^ 2 + q + 1)},
          a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
          a ≠ b → c ≠ d →
          ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
            1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
        Metric.diam (p '' (D.carrier : Set (ZMod (q ^ 2 + q + 1)))) =
          scaleFactor (m := q ^ 2 + q + 1) * gridDist (m := q ^ 2 + q + 1) ((q ^ 2 + q + 1) / 2) := by
  classical
  have hdim : ((q ^ 2 + q + 1) / 2) * 2 = (q + 1) ^ 2 - (q + 1) :=
    primePower_ambientDim_eq_n q
  let e :
      EuclideanSpace Real (Fin (((q ^ 2 + q + 1) / 2) * 2)) ≃ₗᵢ[Real]
        EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))) :=
    LinearIsometryEquiv.piLpCongrLeft 2 Real Real (finCongr hdim)
  obtain ⟨D, hinj, hsep, _hdiamUpper⟩ := primePower_counterexample_fin (q := q) hq
  have hdiam : Metric.diam (scaledSingerPointSetFin (m := q ^ 2 + q + 1) D) =
      scaleFactor (m := q ^ 2 + q + 1) * gridDist (m := q ^ 2 + q + 1) ((q ^ 2 + q + 1) / 2) :=
    scaledResiduePointFin_diam_eq_top (m := q ^ 2 + q + 1) (by
      have hq2 : 2 <= q := hq.two_le
      have hqq : 4 <= q * q := by
        simpa using Nat.mul_le_mul hq2 hq2
      have hm4 : 4 <= q ^ 2 + q + 1 := by
        rw [pow_two]
        omega
      exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)) D
  refine ⟨D, fun t => e (scaledResiduePointFin (m := q ^ 2 + q + 1) t), ?_, ?_, ?_⟩
  · exact e.injective.comp hinj
  · intro a b c d ha hb hc hd hab hcd hpair
    simpa [e.dist_map] using hsep ha hb hc hd hab hcd hpair
  · simpa [scaledSingerPointSetFin, image_image] using
      (e.diam_image (scaledSingerPointSetFin (m := q ^ 2 + q + 1) D)).trans hdiam

end

end DiameterConstruction

/-
Copyright (c) 2026 Ho Boon Suan
Released under the MIT license, as described in the file LICENSE.
-/

/-
# Main theorem - A counterexample to Erdos's dimension-free diameter conjecture

Erdos conjectured that every `n`-point set in Euclidean space whose pairwise distances are
mutually at least `1` apart must have diameter at least `(1 + o(1)) * n^2`, independently
of the ambient dimension. This file packages the final asymptotic statements proved by the
construction developed in the earlier files.

The construction combines:
1. A Singer difference set `D ⊂ ZMod m` with `m = q^2 + q + 1` and `|D| = q + 1 = n`.
2. A weighted product of regular `m`-gons whose distance profile is `G (2 * pi * s / m)`.
3. The strict concavity of `G` ensures the distance gaps are decreasing, so after scaling,
   all pairwise distances are at least `1` apart.
4. The asymptotic diameter is `(1 - 1 / pi^2 + o(1)) * n^2`, contradicting the conjecture.

## Main results

* `DiameterConstruction.primePowerDiameter_over_order_tendsto_cStar`
* `DiameterConstruction.primePowerDiameter_over_cardSq_tendsto_cStar`
* `DiameterConstruction.infinitely_many_quantitative_counterexamples`
-/

namespace DiameterConstruction

open Real Set Filter
open scoped Topology

noncomputable section

/- ### The asymptotic constant -/

lemma cStar_lt_one : cStar < 1 := by
  exact sub_lt_self _ <| by positivity;

/- ### Asymptotic diameter (Proposition 4.1)

The ratio `G(π) / (2π · G'(π⁻))` equals `c*`. Since the diameter of the scaled
point set is `dₙ / (dₙ - dₙ₋₁)` and this ratio converges to `G(π) / (2π · G'(π⁻))`,
the asymptotic diameter is `c* · m ∼ c* · n²`. -/

lemma H'_pi : H' π = π / 4 := by
  exact sub_eq_self.mpr ( by norm_num )

/-
The limit ratio `4·H(π)/π²` equals `c* = 1 - 1/π²`.

This is the key asymptotic identity: by the mean value theorem, the diameter of the
scaled construction satisfies `diam(𝒳ₘ)/m → G(π)/(2π·G'(π⁻)) = 4H(π)/π² = c*`.
-/
lemma diameter_ratio_eq_cStar :
    4 * H π / π ^ 2 = cStar := by
      rw [ H_pi ] ; ring_nf;
      unfold cStar;
      norm_num

def primePowerOrder (q : Nat) : Nat := q ^ 2 + q + 1

instance primePowerOrder_neZero (q : Nat) : NeZero (primePowerOrder q) := by
  refine ⟨by
    unfold primePowerOrder
    omega⟩

/-- The exact finite diameter of the scaled construction for the parameter `q`,
before rewriting it in asymptotic form. -/
def primePowerDiameter (q : Nat) : Real :=
  scaleFactor (m := primePowerOrder q) * gridDist (m := primePowerOrder q) (primePowerOrder q / 2)

/-- The top grid angle `theta_N = 2 * pi * N / m` with `N = floor(m / 2)`. -/
def topGapAngle (q : Nat) : Real :=
  2 * Real.pi * (((primePowerOrder q) / 2 : Nat) : Real) / primePowerOrder q

/-- The penultimate grid angle `theta_(N-1)`. -/
def prevTopGapAngle (q : Nat) : Real :=
  2 * Real.pi * ((((primePowerOrder q) / 2 - 1 : Nat)) : Real) / primePowerOrder q

lemma primePowerOrder_half_ge_two {q : Nat} (hq : 2 <= q) :
    2 <= primePowerOrder q / 2 := by
  unfold primePowerOrder
  have hqq : 4 <= q * q := by
    simpa using Nat.mul_le_mul hq hq
  have hm4 : 4 <= q ^ 2 + q + 1 := by
    rw [pow_two]
    omega
  exact (Nat.le_div_iff_mul_le Nat.two_pos).2 (by simpa using hm4)

lemma topGapAngle_mem_Icc (q : Nat) : topGapAngle q ∈ Icc 0 π := by
  simpa [topGapAngle] using
    gridAngle_mem_Icc (m := primePowerOrder q)
      (s := primePowerOrder q / 2)
      (le_rfl : primePowerOrder q / 2 <= primePowerOrder q / 2)

lemma prevTopGapAngle_mem_Icc (q : Nat) (_hq : 2 <= q) :
    prevTopGapAngle q ∈ Icc 0 π := by
  have hs : primePowerOrder q / 2 - 1 <= primePowerOrder q / 2 := by
    omega
  simpa [prevTopGapAngle] using
    gridAngle_mem_Icc (m := primePowerOrder q)
      (s := primePowerOrder q / 2 - 1) hs

lemma prevTopGapAngle_lt_topGapAngle (q : Nat) (hq : 2 <= q) :
    prevTopGapAngle q < topGapAngle q := by
  simpa [prevTopGapAngle, topGapAngle] using
    gridAngle_strictMono (m := primePowerOrder q)
      (s := primePowerOrder q / 2 - 1)
      (t := primePowerOrder q / 2)
      (le_rfl : primePowerOrder q / 2 <= primePowerOrder q / 2)
      (by
        have hN : 2 <= primePowerOrder q / 2 := primePowerOrder_half_ge_two hq
        omega)

lemma topGapAngle_eq (q : Nat) :
    topGapAngle q = π - π / primePowerOrder q := by
  have hdouble_nat : 2 * (primePowerOrder q / 2) = primePowerOrder q - 1 := by
    unfold primePowerOrder
    rw [Nat.mul_comm]
    simpa using primePower_reindexed_dim q
  have hdouble :
      (2 : Real) * (((primePowerOrder q / 2 : Nat) : Real)) = ((primePowerOrder q - 1 : Nat) : Real) := by
    exact_mod_cast hdouble_nat
  have hm0 : (primePowerOrder q : Real) ≠ 0 := by
    exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
  have hm1 : (((primePowerOrder q - 1 : Nat) : Real)) = (primePowerOrder q : Real) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (primePowerOrder_neZero q).ne))]
    norm_num
  calc
    topGapAngle q = π * ((2 : Real) * (((primePowerOrder q / 2 : Nat) : Real)) / primePowerOrder q) := by
      unfold topGapAngle
      ring
    _ = π * (((primePowerOrder q - 1 : Nat) : Real) / primePowerOrder q) := by rw [hdouble]
    _ = π - π / primePowerOrder q := by
      rw [hm1]
      field_simp [hm0]

lemma prevTopGapAngle_eq (q : Nat) (hq : 2 <= q) :
    prevTopGapAngle q = π - 3 * π / primePowerOrder q := by
  have hdouble_prev_nat : 2 * (primePowerOrder q / 2 - 1) = primePowerOrder q - 3 := by
    have hdouble_nat : 2 * (primePowerOrder q / 2) = primePowerOrder q - 1 := by
      unfold primePowerOrder
      rw [Nat.mul_comm]
      simpa using primePower_reindexed_dim q
    omega
  have hdouble_prev :
      (2 : Real) * (((primePowerOrder q / 2 - 1 : Nat) : Real)) = ((primePowerOrder q - 3 : Nat) : Real) := by
    exact_mod_cast hdouble_prev_nat
  have hm0 : (primePowerOrder q : Real) ≠ 0 := by
    exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
  have hm3nat : 3 <= primePowerOrder q := by
    unfold primePowerOrder
    omega
  have hm3 : (((primePowerOrder q - 3 : Nat) : Real)) = (primePowerOrder q : Real) - 3 := by
    rw [Nat.cast_sub hm3nat]
    norm_num
  calc
    prevTopGapAngle q =
        π * ((2 : Real) * (((primePowerOrder q / 2 - 1 : Nat) : Real)) / primePowerOrder q) := by
          unfold prevTopGapAngle
          ring
    _ = π * (((primePowerOrder q - 3 : Nat) : Real) / primePowerOrder q) := by rw [hdouble_prev]
    _ = π - 3 * π / primePowerOrder q := by
          rw [hm3]
          field_simp [hm0]

lemma G'_pi : G' π = π / (8 * G π) := by
  unfold G'
  rw [H'_pi]
  rw [G]
  ring_nf

lemma continuousAt_G'_pi : ContinuousAt G' π := by
  unfold G'
  refine ContinuousAt.div ?_ ?_ ?_
  · exact (hasDerivAt_H' π).continuousAt
  · exact ContinuousAt.mul continuousAt_const (continuous_H.continuousAt.sqrt)
  · have hHpi : 0 < H π := H_pos Real.pi_pos le_rfl
    exact mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.2 hHpi)

lemma diameter_ratio_limit_value_eq_cStar :
    G π / (2 * π * G' π) = cStar := by
  have hGne : G π ≠ 0 := G_ne_zero Real.pi_pos le_rfl
  calc
    G π / (2 * π * G' π) = 4 * G π ^ 2 / π ^ 2 := by
      rw [G'_pi]
      field_simp [hGne, Real.pi_ne_zero]
      ring
    _ = 4 * H π / π ^ 2 := by rw [G_sq Real.pi_pos.le le_rfl]
    _ = cStar := diameter_ratio_eq_cStar

lemma continuous_G : Continuous G := by
  exact continuous_H.sqrt

lemma lastGap_eq_topGap_difference (q : Nat) (hq : 2 <= q) :
    lastGap (m := primePowerOrder q) = G (topGapAngle q) - G (prevTopGapAngle q) := by
  have hsucc : primePowerOrder q / 2 - 1 + 1 = primePowerOrder q / 2 := by
    have hN : 2 <= primePowerOrder q / 2 := primePowerOrder_half_ge_two hq
    omega
  simp [lastGap, gridGap, gridDist, topGapAngle, prevTopGapAngle, hsucc]

lemma exists_topGap_mvt_point (q : Nat) (hq : 2 <= q) :
    ∃ ξ ∈ Ioo (prevTopGapAngle q) (topGapAngle q),
      G' ξ = (G (topGapAngle q) - G (prevTopGapAngle q)) / (topGapAngle q - prevTopGapAngle q) := by
  have hab : prevTopGapAngle q < topGapAngle q := prevTopGapAngle_lt_topGapAngle q hq
  refine exists_hasDerivAt_eq_slope G G' hab ?_ ?_
  · refine continuousOn_G.mono ?_
    exact Icc_subset_Icc (prevTopGapAngle_mem_Icc q hq).1 (topGapAngle_mem_Icc q).2
  · intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt (prevTopGapAngle_mem_Icc q hq).1 hx.1
    have hxpi : x <= π := le_trans hx.2.le (topGapAngle_mem_Icc q).2
    exact hasDerivAt_G hx0 hxpi

noncomputable def topGapMVTPoint (q : Nat) : Real :=
  if hq : 2 <= q then
    Classical.choose (exists_topGap_mvt_point q hq)
  else
    π

lemma topGapMVTPoint_mem_Ioo (q : Nat) (hq : 2 <= q) :
    topGapMVTPoint q ∈ Ioo (prevTopGapAngle q) (topGapAngle q) := by
  simpa [topGapMVTPoint, hq] using (Classical.choose_spec (exists_topGap_mvt_point q hq)).1

lemma topGapMVTPoint_eq_slope (q : Nat) (hq : 2 <= q) :
    G' (topGapMVTPoint q) =
      (G (topGapAngle q) - G (prevTopGapAngle q)) / (topGapAngle q - prevTopGapAngle q) := by
  simpa [topGapMVTPoint, hq] using (Classical.choose_spec (exists_topGap_mvt_point q hq)).2

lemma topGapAngle_sub_prevTopGapAngle (q : Nat) (hq : 2 <= q) :
    topGapAngle q - prevTopGapAngle q = 2 * π / primePowerOrder q := by
  rw [topGapAngle_eq q, prevTopGapAngle_eq q hq]
  ring

lemma primePowerOrder_tendsto_atTop :
    Tendsto (fun q : Nat => (primePowerOrder q : Real)) atTop atTop := by
  refine tendsto_atTop_mono (fun q => ?_) tendsto_natCast_atTop_atTop
  have hquad : (q : Real) <= (q : Real) ^ 2 + q + 1 := by
    nlinarith [sq_nonneg (q : Real)]
  simpa [primePowerOrder] using hquad

lemma topGapAngle_tendsto_pi :
    Tendsto topGapAngle atTop (𝓝 π) := by
  have hdiv : Tendsto (fun q : Nat => π / (primePowerOrder q : Real)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop primePowerOrder_tendsto_atTop
  have heq : topGapAngle = fun q : Nat => π - π / (primePowerOrder q : Real) := by
    funext q
    exact topGapAngle_eq q
  rw [heq]
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => π) atTop (𝓝 π)).sub hdiv)

lemma prevTopGapAngle_tendsto_pi :
    Tendsto prevTopGapAngle atTop (𝓝 π) := by
  have hdiv : Tendsto (fun q : Nat => 3 * π / (primePowerOrder q : Real)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop primePowerOrder_tendsto_atTop
  have hmain :
      Tendsto (fun q : Nat => π - 3 * π / (primePowerOrder q : Real)) atTop (𝓝 π) :=
    by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : Nat => π) atTop (𝓝 π)).sub hdiv)
  have heq :
      prevTopGapAngle =ᶠ[atTop] fun q : Nat => π - 3 * π / (primePowerOrder q : Real) := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    rw [prevTopGapAngle_eq q hq]
  exact hmain.congr' heq.symm

lemma topGapMVTPoint_tendsto_pi :
    Tendsto topGapMVTPoint atTop (𝓝 π) := by
  have hlow : ∀ᶠ q in atTop, prevTopGapAngle q <= topGapMVTPoint q := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    exact (topGapMVTPoint_mem_Ioo q hq).1.le
  have hhigh : ∀ᶠ q in atTop, topGapMVTPoint q <= topGapAngle q := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    exact (topGapMVTPoint_mem_Ioo q hq).2.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    prevTopGapAngle_tendsto_pi topGapAngle_tendsto_pi hlow hhigh

lemma G'_topGapMVTPoint_tendsto_pi :
    Tendsto (fun q : Nat => G' (topGapMVTPoint q)) atTop (𝓝 (G' π)) := by
  exact continuousAt_G'_pi.tendsto.comp topGapMVTPoint_tendsto_pi

lemma primePowerDiameter_ratio_eq_mvt (q : Nat) (hq : 2 <= q) :
    primePowerDiameter q / (primePowerOrder q : Real) =
      G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q)) := by
  have hN : 2 <= primePowerOrder q / 2 := primePowerOrder_half_ge_two hq
  have hm0 : (primePowerOrder q : Real) ≠ 0 := by
    exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
  have hlast_ne : lastGap (m := primePowerOrder q) ≠ 0 := (lastGap_pos (m := primePowerOrder q) hN).ne'
  have hgrid : gridDist (m := primePowerOrder q) (primePowerOrder q / 2) = G (topGapAngle q) := by
    rfl
  have hlast :
      lastGap (m := primePowerOrder q) =
        (2 * π / primePowerOrder q) * G' (topGapMVTPoint q) := by
    calc
      lastGap (m := primePowerOrder q) = G (topGapAngle q) - G (prevTopGapAngle q) :=
        lastGap_eq_topGap_difference q hq
      _ = (topGapAngle q - prevTopGapAngle q) * G' (topGapMVTPoint q) := by
        have hstep_ne : topGapAngle q - prevTopGapAngle q ≠ 0 := by
          exact sub_ne_zero.mpr (prevTopGapAngle_lt_topGapAngle q hq).ne'
        rw [topGapMVTPoint_eq_slope q hq]
        field_simp [hstep_ne]
      _ = (2 * π / primePowerOrder q) * G' (topGapMVTPoint q) := by
        rw [topGapAngle_sub_prevTopGapAngle q hq]
  calc
    primePowerDiameter q / (primePowerOrder q : Real) =
        (scaleFactor (m := primePowerOrder q) *
          gridDist (m := primePowerOrder q) (primePowerOrder q / 2)) / (primePowerOrder q : Real) := by
          rfl
    _ = gridDist (m := primePowerOrder q) (primePowerOrder q / 2) /
          ((primePowerOrder q : Real) * lastGap (m := primePowerOrder q)) := by
            unfold scaleFactor
            field_simp [hlast_ne, hm0]
    _ = G (topGapAngle q) /
          ((primePowerOrder q : Real) *
            ((2 * π / primePowerOrder q) * G' (topGapMVTPoint q))) := by
              rw [hgrid, hlast]
    _ = G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q)) := by
          have hm_mul : (primePowerOrder q : Real) * (2 * π / primePowerOrder q) = 2 * π := by
            field_simp [hm0]
          have hden :
              (primePowerOrder q : Real) *
                  ((2 * π / primePowerOrder q) * G' (topGapMVTPoint q)) =
                2 * π * G' (topGapMVTPoint q) := by
            calc
              (primePowerOrder q : Real) *
                  ((2 * π / primePowerOrder q) * G' (topGapMVTPoint q)) =
                  ((primePowerOrder q : Real) * (2 * π / primePowerOrder q)) *
                    G' (topGapMVTPoint q) := by ring
              _ = (2 * π) * G' (topGapMVTPoint q) := by rw [hm_mul]
              _ = 2 * π * G' (topGapMVTPoint q) := by ring
          rw [hden]

theorem primePowerDiameter_over_order_tendsto_cStar :
    Tendsto (fun q : Nat => primePowerDiameter q / (primePowerOrder q : Real)) atTop (𝓝 cStar) := by
  have heq :
      (fun q : Nat => primePowerDiameter q / (primePowerOrder q : Real)) =ᶠ[atTop]
        (fun q : Nat => G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q))) := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    rw [primePowerDiameter_ratio_eq_mvt q hq]
  have hnum : Tendsto (fun q : Nat => G (topGapAngle q)) atTop (𝓝 (G π)) := by
    exact continuous_G.continuousAt.tendsto.comp topGapAngle_tendsto_pi
  have hden : Tendsto (fun q : Nat => 2 * π * G' (topGapMVTPoint q)) atTop (𝓝 (2 * π * G' π)) := by
    exact tendsto_const_nhds.mul G'_topGapMVTPoint_tendsto_pi
  have hG'pi_ne : G' π ≠ 0 := by
    have hGne : G π ≠ 0 := G_ne_zero Real.pi_pos le_rfl
    rw [G'_pi]
    exact div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num) hGne)
  have hden_ne : 2 * π * G' π ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hG'pi_ne
  have hratio :
      Tendsto (fun q : Nat => G (topGapAngle q) / (2 * π * G' (topGapMVTPoint q)))
        atTop (𝓝 (G π / (2 * π * G' π))) := by
    exact Tendsto.div hnum hden hden_ne
  simpa [diameter_ratio_limit_value_eq_cStar] using hratio.congr' heq.symm

lemma primePowerOrder_over_cardSq_tendsto_one :
    Tendsto (fun q : Nat => (primePowerOrder q : Real) / (q + 1) ^ 2) atTop (𝓝 1) := by
  have hrecip : Tendsto (fun q : Nat => (1 : Real) / (q + 1 : Real)) atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun q : Nat => (1 : Real) / (q + 1 : Real)) atTop (𝓝 0))
  have hbase :
      Tendsto (fun q : Nat => (1 : Real) - (1 : Real) / (q + 1 : Real)) atTop (𝓝 (1 - 0)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real)) atTop (𝓝 1)).sub hrecip
  have heqquot :
      (fun q : Nat => (q : Real) / (q + 1 : Real)) =ᶠ[atTop]
        fun q : Nat => (1 : Real) - (1 : Real) / (q + 1 : Real) := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hq1 : (q + 1 : Real) ≠ 0 := by positivity
    field_simp [hq1]
    ring
  have hquot :
      Tendsto (fun q : Nat => (q : Real) / (q + 1 : Real)) atTop (𝓝 1) := by
    simpa using hbase.congr' heqquot.symm
  have hprod :
      Tendsto
        (fun q : Nat =>
          ((q : Real) / (q + 1 : Real)) * ((1 : Real) / (q + 1 : Real)))
        atTop (𝓝 (1 * 0)) := by
    exact hquot.mul hrecip
  have heqsmall :
      (fun q : Nat => (q : Real) / (q + 1 : Real) ^ 2) =ᶠ[atTop]
        fun q : Nat => ((q : Real) / (q + 1 : Real)) * ((1 : Real) / (q + 1 : Real)) := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hq1 : (q + 1 : Real) ≠ 0 := by positivity
    field_simp [hq1]
  have hsmall :
      Tendsto (fun q : Nat => (q : Real) / (q + 1 : Real) ^ 2) atTop (𝓝 0) := by
    simpa using hprod.congr' heqsmall.symm
  have hmain :
      Tendsto
        (fun q : Nat => (1 : Real) - (q : Real) / (q + 1 : Real) ^ 2)
        atTop (𝓝 (1 - 0)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real)) atTop (𝓝 1)).sub hsmall
  have heq :
      (fun q : Nat => (primePowerOrder q : Real) / (q + 1) ^ 2) =ᶠ[atTop]
        fun q : Nat => (1 : Real) - (q : Real) / (q + 1 : Real) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hq1sq : ((q + 1 : Real) ^ 2) ≠ 0 := by positivity
    calc
      (primePowerOrder q : Real) / (q + 1) ^ 2 =
          (((q : Real) ^ 2 + q + 1) / (q + 1 : Real) ^ 2) := by
            norm_num [primePowerOrder]
      _ = (1 : Real) - (q : Real) / (q + 1 : Real) ^ 2 := by
            field_simp [hq1sq]
            ring
  simpa using hmain.congr' heq.symm

theorem primePowerDiameter_over_cardSq_tendsto_cStar :
    Tendsto (fun q : Nat => primePowerDiameter q / (q + 1) ^ 2) atTop (𝓝 cStar) := by
  have heq :
      (fun q : Nat => primePowerDiameter q / (q + 1) ^ 2) =ᶠ[atTop]
        (fun q : Nat =>
          (primePowerDiameter q / (primePowerOrder q : Real)) *
            ((primePowerOrder q : Real) / (q + 1) ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro q
    have hm0 : (primePowerOrder q : Real) ≠ 0 := by
      exact_mod_cast (show primePowerOrder q ≠ 0 from primePowerOrder_neZero q |>.ne)
    field_simp [hm0]
  have hmul :
      Tendsto
        (fun q : Nat =>
          (primePowerDiameter q / (primePowerOrder q : Real)) *
            ((primePowerOrder q : Real) / (q + 1) ^ 2))
        atTop (𝓝 (cStar * 1)) := by
    exact primePowerDiameter_over_order_tendsto_cStar.mul primePowerOrder_over_cardSq_tendsto_one
  simpa using hmul.congr' heq.symm

def primePowerDiameterError (q : Nat) : Real :=
  primePowerDiameter q / (q + 1) ^ 2 - cStar

lemma primePowerDiameterError_tendsto_zero :
    Tendsto primePowerDiameterError atTop (𝓝 0) := by
  change Tendsto (fun q : ℕ => primePowerDiameter q / ((q : ℝ) + 1) ^ 2 - cStar)
    atTop (𝓝 0)
  simpa only [sub_self] using
    (primePowerDiameter_over_cardSq_tendsto_cStar.sub
      (tendsto_const_nhds : Tendsto (fun _ : Nat => cStar) atTop (𝓝 cStar)))

theorem infinitely_many_quantitative_counterexamples :
    ∃ ε : Nat → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ N : Nat, ∃ q, N <= q ∧ q.Prime ∧
        ∃ D : SingerDiffSet (primePowerOrder q) (q + 1),
          ∃ p : ZMod (primePowerOrder q) →
              EuclideanSpace Real (Fin ((q + 1) ^ 2 - (q + 1))),
            Function.Injective p ∧
            (∀ {a b c d : ZMod (primePowerOrder q)},
              a ∈ D.carrier → b ∈ D.carrier → c ∈ D.carrier → d ∈ D.carrier →
              a ≠ b → c ≠ d →
              ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
                1 <= |dist (p a) (p b) - dist (p c) (p d)|) ∧
            Metric.diam (p '' (D.carrier : Set (ZMod (primePowerOrder q)))) <=
              (cStar + ε q) * (q + 1) ^ 2 := by
  refine ⟨primePowerDiameterError, primePowerDiameterError_tendsto_zero, ?_⟩
  intro N
  obtain ⟨q, hqN, hqPrime⟩ := Nat.exists_infinite_primes N
  have hqPow : IsPrimePow q := hqPrime.isPrimePow
  obtain ⟨D, p, hinj, hsep, hdiam⟩ :=
    primePower_counterexample_exactDimension_with_diam (q := q) hqPow
  refine ⟨q, hqN, hqPrime, D, p, hinj, hsep, ?_⟩
  have hq1sq : ((q + 1 : Real) ^ 2) ≠ 0 := by positivity
  calc
    Metric.diam (p '' (D.carrier : Set _)) = primePowerDiameter q := by
      simpa [primePowerDiameter, primePowerOrder] using hdiam
    _ = (cStar + primePowerDiameterError q) * (q + 1) ^ 2 := by
      unfold primePowerDiameterError
      field_simp [hq1sq]
      ring
    _ <= (cStar + primePowerDiameterError q) * (q + 1) ^ 2 := le_rfl

end

end DiameterConstruction

open Filter in
theorem OMA.solution : type_of% @Erdos670.erdos_670.variants.uniform_in_dim := by
  classical
  intro h
  obtain ⟨error, herror, examples⟩ :=
    DiameterConstruction.infinitely_many_quantitative_counterexamples
  let ε : ℝ := (1 - DiameterConstruction.cStar) / 3
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [DiameterConstruction.cStar_lt_one]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
  have hevent : ∀ᶠ q in atTop, error q < ε := herror.eventually_lt_const hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  obtain ⟨q, hq, _, D, p, hinj, hsep, hdiam⟩ := examples (max N M)
  let A := D.carrier.map ⟨p, hinj⟩
  have hcard : A.card = q + 1 := by simpa [A] using D.card_eq
  have hA : Erdos670.HasSeparatedDistances A := by
    intro a ha b hb c hc e he hab hce hpairs
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    refine hsep ha' hb' hc' he' (fun hab' => hab (congrArg p hab'))
      (fun hce' => hce (congrArg p hce')) ?_
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hpairs rfl
    · exact hpairs (Sym2.eq_swap)
  have hdiam' : Metric.diam (↑A : Set (EuclideanSpace ℝ (Fin ((q + 1) ^ 2 - (q + 1))))) ≤
      (DiameterConstruction.cStar + error q) * ((q : ℝ) + 1) ^ 2 := by
    have hset : (↑A : Set (EuclideanSpace ℝ (Fin ((q + 1) ^ 2 - (q + 1))))) = p '' (D.carrier : Set _) := by
      ext x
      simp [A]
    rwa [hset]
  have hbound := hN (q + 1) (by omega : N ≤ q + 1) _ A hcard hA
  push_cast at hbound
  have hcoeff : DiameterConstruction.cStar + error q < 1 - ε := by
    have := hM q (by omega : M ≤ q)
    dsimp [ε] at *
    linarith [DiameterConstruction.cStar_lt_one]
  have hsq : 0 < ((q : ℝ) + 1) ^ 2 := by positivity
  exact (not_lt_of_ge hbound) (hdiam'.trans_lt (mul_lt_mul_of_pos_right hcoeff hsq))
