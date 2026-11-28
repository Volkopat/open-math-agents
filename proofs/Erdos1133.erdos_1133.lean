import FormalConjectures.ErdosProblems.«1133»
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.IntermediateValue

/-
Adapted from github.com/peilinliu66-dev/jsp940-erdos1133-formalization (commit 83ab7d38a4abbdfc1c9509cfbb7b49514cca217e),
(c) peilinliu66-dev (formalization contribution, with Codex AI assistance), Apache-2.0.
Licensed under the Apache License, Version 2.0; you may obtain a copy of the licence at http://www.apache.org/licenses/LICENSE-2.0.
Foundational modules of the Erdos1152 formalization by the same contributor, from
github.com/peilinliu66-dev/jsp957-erdos1152-formalization (commit 5f77404a2c8869efa1797a93862d5da170925977), Apache-2.0 notice as above.
Modified: namespaces renamed to OMA.Port1.*, modules concatenated, simp attribute uses replaced by explicit simp arguments,
adapted to the Lean and Mathlib versions of this site. The result is known mathematics (Yang 2026; Olevskii and Ulanovskii 2018).
-/


/- ===== OMA.Port1.E1152.FiniteFourier ===== -/
section

/-!
Finite Fourier calculations for the finite-dimensional form of the
Olevskii--Ulanovskii argument.  The circle has period `2π`; its measure here is
normalized Haar measure, not the length measure.  No sampling bound is assumed.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset

namespace OMA.Port1.E1152

abbrev FourierCircle := AddCircle (2 * Real.pi)
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev CircleFunction := C(FourierCircle, ℂ)

noncomputable def character (n : ℤ) : CircleFunction := fourier n
noncomputable def circleMeasure : Measure FourierCircle := AddCircle.haarAddCircle

instance : IsProbabilityMeasure circleMeasure := by
  unfold circleMeasure
  infer_instance

theorem character_zero (x : FourierCircle) : character 0 x = 1 := by
  simp [character, fourier_zero]

theorem character_at_zero (n : ℤ) : character n 0 = 1 := by
  exact fourier_eval_zero n

theorem character_add (j k : ℤ) (x : FourierCircle) :
    character (j + k) x = character j x * character k x := fourier_add

theorem character_norm (n : ℤ) (x : FourierCircle) :
    ‖character n x‖ = 1 := by
  exact Circle.norm_coe _

theorem character_translate (n : ℤ) (x y : FourierCircle) :
    character n (x + y) = character n x * character n y := by
  simp only [character, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem character_sub (n : ℤ) (x y : FourierCircle) :
    character n (x - y) = character n x * character (-n) y := by
  rw [sub_eq_add_neg, character_translate]
  congr 1
  simp only [character, fourier_apply, smul_neg, neg_smul]

theorem character_integral (n : ℤ) :
    ∫ x, character n x ∂circleMeasure = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn, character_zero]
  · rw [if_neg hn]
    let : circleMeasure.IsAddRightInvariant := by
      unfold circleMeasure
      infer_instance
    exact integral_eq_zero_of_add_right_eq_neg
      (μ := circleMeasure) (fourier_add_half_inv_index hn (by positivity))

noncomputable def finiteFourier (s : Finset ℤ) (c : ℤ → ℂ) : CircleFunction :=
  ∑ n ∈ s, c n • character n

theorem finiteFourier_apply (s : Finset ℤ) (c : ℤ → ℂ)
    (x : FourierCircle) : finiteFourier s c x = ∑ n ∈ s, c n * character n x := by
  simp [finiteFourier]

theorem integral_character_mul (j k : ℤ) :
    ∫ x, character j x * character k x ∂circleMeasure =
      if j + k = 0 then 1 else 0 := by
  simp only [← character_add, character_integral]

noncomputable def coefficient (f : CircleFunction) (n : ℤ) : ℂ :=
  ∫ x, character (-n) x * f x ∂circleMeasure

theorem coefficient_finiteFourier (s : Finset ℤ) (c : ℤ → ℂ) (n : ℤ) :
    coefficient (finiteFourier s c) n = if n ∈ s then c n else 0 := by
  classical
  unfold coefficient
  simp only [finiteFourier_apply, mul_sum]
  rw [integral_finsetSum]
  · simp_rw [show ∀ j x, character (-n) x * (c j * character j x) =
        c j * (character (-n) x * character j x) by intros; ring,
      integral_const_mul, integral_character_mul]
    simpa [neg_add_eq_zero, eq_comm] using
      (sum_ite_eq' s n c)
  · intro j hj
    exact (by fun_prop : Continuous fun x : FourierCircle =>
      character (-n) x * (c j * character j x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_coefficient_le (f : CircleFunction) (n : ℤ) :
    ‖coefficient f n‖ ≤ ‖f‖ := by
  unfold coefficient
  simpa using norm_integral_le_of_norm_le_const (μ := circleMeasure)
    (C := ‖f‖) (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, character_norm, one_mul]
      exact f.norm_coe_le_norm x)

noncomputable def circleConvolution (f g : CircleFunction) :
    FourierCircle → ℂ := fun x => ∫ y, f y * g (x-y) ∂circleMeasure

/-- A real nonnegative convolution kernel has operator bound equal to its mass. -/
theorem norm_convolution_le (f g : CircleFunction) (C : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C) :
    ∀ x, ‖circleConvolution f g x‖ ≤ (∫ y, ‖f y‖ ∂circleMeasure) * C := by
  intro x
  unfold circleConvolution
  calc
    ‖∫ y, f y * g (x-y) ∂circleMeasure‖
        ≤ ∫ y, ‖f y * g (x-y)‖ ∂circleMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f y‖ * C ∂circleMeasure := by
      apply integral_mono
      · exact (by fun_prop : Continuous fun y : FourierCircle =>
          ‖f y * g (x-y)‖).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (by fun_prop : Continuous fun y : FourierCircle =>
          ‖f y‖*C).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · intro y
        change ‖f y * g (x-y)‖ ≤ ‖f y‖ * C
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = (∫ y, ‖f y‖ ∂circleMeasure)*C := integral_mul_const _ _

/-- The dimension argument in the localized finite sampling construction.
All constraints are actual linear maps on the finite vector of coefficients. -/
theorem exists_common_kernel_vector {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hcard : Fintype.card κ < Fintype.card ι)
    (L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) :
    ∃ a : ι → ℂ, a ≠ 0 ∧ L a = 0 := by
  by_contra h
  have hzero : ∀ a, L a = 0 → a = 0 := by
    intro a ha
    by_contra hn
    exact h ⟨a, hn, ha⟩
  have hinj : Function.Injective L := by
    intro a b hab
    have hz : L (a-b) = 0 := by simp [map_sub, hab]
    exact sub_eq_zero.mp (hzero _ hz)
  have hf := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_pi, Module.finrank_self, mul_one] at hf
  exact (not_le_of_gt hcard) hf

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.FejerGrid ===== -/
section

/-!
The nonnegative finite Fejér grid used to impose the extra sampling constraints.
The grid weights form an exact partition of one and interpolate the coefficient
vector on the grid.  In particular their norm bound does not contain `L`.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset

namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def circleGrid (L : ℕ) (q : ZMod L) : FourierCircle :=
  ((2 * Real.pi * q.val / L : ℝ) : FourierCircle)

noncomputable def oneSidedDirichlet (L : ℕ) : CircleFunction :=
  ∑ j : Fin L, character (j : ℤ)

noncomputable def fejerGridWeight (L : ℕ) (q : ZMod L) : C(FourierCircle, ℝ) where
  toFun x := ‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2
  continuous_toFun := by fun_prop

theorem fejerGridWeight_nonneg (L : ℕ) (q : ZMod L) (x : FourierCircle) :
    0 ≤ fejerGridWeight L q x := by
  change 0 ≤ ‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2
  positivity

theorem character_grid (L : ℕ) [NeZero L] (n : ℤ) (q : ZMod L) :
    character n (circleGrid L q) = ZMod.stdAddChar ((n : ZMod L)*q) := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    character n (circleGrid L q) =
        Complex.exp (2 * Real.pi * Complex.I * (n * (q.val : ℤ)) / L) := by
      simp only [circleGrid, character, fourier_coe_apply]
      congr 1
      push_cast
      field_simp [hL, hpi]
      <;> ring
    _ = ZMod.stdAddChar ((n * (q.val : ℤ) : ℤ) : ZMod L) := by
      simpa only [Int.cast_mul] using (ZMod.stdAddChar_coe (N := L) (n * (q.val : ℤ))).symm
    _ = ZMod.stdAddChar ((n : ZMod L) * q) := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem sum_character_grid (L : ℕ) [NeZero L] (n : ℤ) :
    ∑ q : ZMod L, character n (circleGrid L q) =
      if (n : ZMod L) = 0 then (L : ℂ) else 0 := by
  simp only [character_grid]
  split_ifs with hn
  · simp [hn]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L hn)

theorem fin_sub_cast_zero (L : ℕ) [NeZero L] (i j : Fin L) :
    (((i : ℤ)-(j : ℤ) : ℤ) : ZMod L) = 0 ↔ i = j := by
  rw [Int.cast_sub, sub_eq_zero]
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt, Fin.ext_iff] using hv
  · intro h; simp [h]

theorem normSq_dirichlet_expansion (L : ℕ) (x : FourierCircle) :
    (‖oneSidedDirichlet L x‖^2 : ℂ) =
      ∑ i : Fin L, ∑ j : Fin L, character ((i:ℤ)-(j:ℤ)) x := by
  have hnorm : (‖oneSidedDirichlet L x‖^2 : ℂ) =
      oneSidedDirichlet L x * conj (oneSidedDirichlet L x) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hnorm]
  simp only [oneSidedDirichlet, ContinuousMap.sum_apply, map_sum,
    sum_mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [sub_eq_add_neg, character_add]
  congr 1
  exact (fourier_neg (n := (j:ℤ))).symm

/-- Exact nonnegative partition of unity, independent of the grid size. -/
theorem sum_fejerGridWeight (L : ℕ) [NeZero L] (x : FourierCircle) :
    ∑ q : ZMod L, fejerGridWeight L q x = 1 := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hsum (i j : Fin L) :
      ∑ q : ZMod L, character ((i:ℤ)-(j:ℤ)) x *
        character (-((i:ℤ)-(j:ℤ))) (circleGrid L q) =
      if i = j then (L : ℂ) else 0 := by
    rw [← mul_sum, sum_character_grid]
    by_cases h : i = j
    · simp [h, character_zero]
    · have hz : ((-((i:ℤ)-(j:ℤ)) : ℤ) : ZMod L) ≠ 0 := by
        intro hz
        have hz' : (((i:ℤ)-(j:ℤ) : ℤ) : ZMod L) = 0 := by
          apply neg_eq_zero.mp
          simpa only [Int.cast_neg] using hz
        exact h ((fin_sub_cast_zero L i j).mp hz')
      rw [if_neg hz, mul_zero, if_neg h]
  have hweight (q : ZMod L) :
      (fejerGridWeight L q x : ℂ) =
        (∑ i : Fin L, ∑ j : Fin L,
          character ((i:ℤ)-(j:ℤ)) x *
            character (-((i:ℤ)-(j:ℤ))) (circleGrid L q)) / (L : ℂ)^2 := by
    change ((‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2 : ℝ) : ℂ) = _
    simp only [Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, normSq_dirichlet_expansion, character_sub]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_one]
  rw [Finset.sum_congr rfl (fun q _ => hweight q), ← Finset.sum_div]
  have hswap :
      (∑ q : ZMod L, ∑ i : Fin L, ∑ j : Fin L,
        character ((i:ℤ)-(j:ℤ)) x *
          character (-((i:ℤ)-(j:ℤ))) (circleGrid L q)) =
      ∑ i : Fin L, ∑ j : Fin L, ∑ q : ZMod L,
        character ((i:ℤ)-(j:ℤ)) x *
          character (-((i:ℤ)-(j:ℤ))) (circleGrid L q) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [hsum]
  simp [pow_two, hL]

private theorem finEquiv_apply_eq_natCast (L : ℕ) [NeZero L] (i : Fin L) :
    (ZMod.finEquiv L) i = (i.val : ZMod L) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    change i.val = i.val % (n + 1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

theorem grid_dirichlet (L : ℕ) [NeZero L] (p q : ZMod L) :
    oneSidedDirichlet L (circleGrid L p-circleGrid L q) =
      if p = q then (L : ℂ) else 0 := by
  classical
  simp only [oneSidedDirichlet, ContinuousMap.sum_apply, character_sub,
    character_grid, Int.cast_natCast, Int.cast_neg]
  have he (i : Fin L) : ZMod.stdAddChar ((i : ZMod L)*p) *
      ZMod.stdAddChar (-((i : ZMod L))*q) =
      ZMod.stdAddChar ((p-q)*(i : ZMod L)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  simp_rw [he]
  have hEquiv : (∑ i : Fin L, ZMod.stdAddChar ((p-q)*(i : ZMod L))) =
      ∑ i : ZMod L, ZMod.stdAddChar ((p-q)*i) := by
    exact Fintype.sum_equiv (ZMod.finEquiv L).toEquiv _ _ (fun i => by
      change ZMod.stdAddChar ((p-q)*(i : ZMod L)) =
        ZMod.stdAddChar ((p-q)*(ZMod.finEquiv L i))
      rw [finEquiv_apply_eq_natCast L i])
  rw [hEquiv]
  by_cases hpq : p = q
  · simp [hpq]
  · rw [if_neg hpq]
    exact AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar L (sub_ne_zero.mpr hpq))

theorem fejerGridWeight_at_grid (L : ℕ) [NeZero L] (p q : ZMod L) :
    fejerGridWeight L q (circleGrid L p) = if p = q then 1 else 0 := by
  change ‖oneSidedDirichlet L (circleGrid L p-circleGrid L q)‖^2 / (L : ℝ)^2 = _
  rw [grid_dirichlet]
  split_ifs <;> simp [Complex.norm_natCast, NeZero.ne L]

-- The grid is auxiliary and is positive at every construction site.
-- ZMod 0 is infinite, so its unrestricted univ-sum is not well-typed.
noncomputable def fejerGridCombination (L : ℕ) [NeZero L] (a : ZMod L → ℂ) : CircleFunction where
  toFun x := ∑ q : ZMod L, a q * (fejerGridWeight L q x : ℂ)
  continuous_toFun := by fun_prop

theorem fejerGridCombination_at_grid (L : ℕ) [NeZero L]
    (a : ZMod L → ℂ) (p : ZMod L) :
    fejerGridCombination L a (circleGrid L p) = a p := by
  simp [fejerGridCombination, fejerGridWeight_at_grid, apply_ite]

theorem norm_fejerGridCombination_le (L : ℕ) [NeZero L]
    (a : ZMod L → ℂ) (C : ℝ) (ha : ∀ q, ‖a q‖ ≤ C) :
    ∀ x, ‖fejerGridCombination L a x‖ ≤ C := by
  intro x
  calc
    ‖∑ q : ZMod L, a q * (fejerGridWeight L q x : ℂ)‖
        ≤ ∑ q : ZMod L, ‖a q * (fejerGridWeight L q x : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q : ZMod L, C * fejerGridWeight L q x := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fejerGridWeight_nonneg L q x)]
      exact mul_le_mul_of_nonneg_right (ha q) (fejerGridWeight_nonneg L q x)
    _ = C := by rw [← mul_sum, sum_fejerGridWeight, mul_one]

noncomputable def fejerGridCombinationLinear (L : ℕ) [NeZero L] :
    (ZMod L → ℂ) →ₗ[ℂ] CircleFunction where
  toFun := fejerGridCombination L
  map_add' a b := by ext x; simp [fejerGridCombination, add_mul, sum_add_distrib]
  map_smul' c a := by ext x; simp [fejerGridCombination, mul_assoc, mul_sum]

/-- One grid polynomial satisfying an arbitrary finite family of linear constraints,
normalized at an actual grid point. No mutual separation of the original data enters. -/
theorem exists_normalized_fejer_annihilator (L : ℕ) [NeZero L]
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ < L)
    (Ψ : CircleFunction →ₗ[ℂ] (κ → ℂ)) :
    ∃ a : ZMod L → ℂ, ∃ p : ZMod L,
      a p = 1 ∧ (∀ q, ‖a q‖ ≤ 1) ∧
      Ψ (fejerGridCombination L a) = 0 ∧
      (∀ x, ‖fejerGridCombination L a x‖ ≤ 1) ∧
      fejerGridCombination L a (circleGrid L p) = 1 := by
  obtain ⟨a, ha, hΨ⟩ := exists_common_kernel_vector
    (ι := ZMod L) (κ := κ) (by simpa using hκ)
    (Ψ.comp (fejerGridCombinationLinear L))
  obtain ⟨p, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod L))
    (fun q => ‖a q‖) (Finset.univ_nonempty)
  have hap : a p ≠ 0 := by
    intro hzero
    apply ha
    ext q
    have hq := hp.2 q (mem_univ q)
    have hq0 : ‖a q‖ ≤ 0 := by simpa [hzero] using hq
    exact norm_le_zero_iff.mp hq0
  let b : ZMod L → ℂ := fun q => (a p)⁻¹ * a q
  have hbn : ∀ q, ‖b q‖ ≤ 1 := by
    intro q
    simp only [b, norm_mul, norm_inv]
    rw [inv_mul_eq_div, div_le_one (norm_pos_iff.mpr hap)]
    exact hp.2 q (mem_univ q)
  have hbp : b p = 1 := inv_mul_cancel₀ hap
  have hbΨ : Ψ (fejerGridCombination L b) = 0 := by
    have he : fejerGridCombination L b = (a p)⁻¹ • fejerGridCombination L a := by
      ext x
      simp [b, fejerGridCombination, mul_assoc, mul_sum]
    rw [he, map_smul]
    change (a p)⁻¹ • (Ψ.comp (fejerGridCombinationLinear L)) a = 0
    rw [hΨ, smul_zero]
  exact ⟨b, p, hbp, hbn, hbΨ, norm_fejerGridCombination_le L b 1 hbn,
    by simpa [fejerGridCombination_at_grid] using hbp⟩

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.FejerFilter ===== -/
section

/-! The de la Vallée Poussin filter, with its uniform operator bound proved
from the positive Fejér kernels.  This is the low/high-frequency separator in
Privalov's finite-dimensional sampling proof. -/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private abbrev differencePairs (L : ℕ) (n : ℤ) :=
  {p : Fin L × Fin L // (p.1 : ℤ)-(p.2 : ℤ)=n}

private noncomputable def nonnegDifferenceEquiv (L q : ℕ) :
    Fin (L-q) ≃ differencePairs L (q : ℤ) where
  toFun i := ⟨(⟨q+i, by omega⟩, ⟨i, by omega⟩), by dsimp; omega⟩
  invFun p := ⟨p.1.2, by have := p.2; have := p.1.1.isLt; omega⟩
  left_inv i := by ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; have := p.2; dsimp at *; omega
    · rfl

private def differenceNegEquiv (L : ℕ) (n : ℤ) :
    differencePairs L n ≃ differencePairs L (-n) where
  toFun p := ⟨p.1.swap, by have := p.2; dsimp at *; omega⟩
  invFun p := ⟨p.1.swap, by have := p.2; dsimp at *; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_differencePairs (L : ℕ) (n : ℤ) :
    Fintype.card (differencePairs L n) = L-n.natAbs := by
  obtain ⟨q, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using (Fintype.card_congr (nonnegDifferenceEquiv L q)).symm
  · rw [← Fintype.card_congr (differenceNegEquiv L (q : ℤ))]
    simpa using (Fintype.card_congr (nonnegDifferenceEquiv L q)).symm

noncomputable def fejerKernel (L : ℕ) : CircleFunction where
  toFun x := ((‖oneSidedDirichlet L x‖^2 / (L : ℝ) : ℝ) : ℂ)
  continuous_toFun := by fun_prop

private theorem fejerKernel_expansion (L : ℕ) (x : FourierCircle) :
    fejerKernel L x = (L : ℂ)⁻¹ *
      ∑ i : Fin L, ∑ j : Fin L, character ((i:ℤ)-(j:ℤ)) x := by
  change ((‖oneSidedDirichlet L x‖^2 / (L : ℝ) : ℝ) : ℂ) = _
  rw [Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow, normSq_dirichlet_expansion, div_eq_mul_inv]
  ring

/-- The exact triangular Fourier coefficients, including the cutoff endpoints. -/
theorem coefficient_fejerKernel (L : ℕ) (n : ℤ) :
    coefficient (fejerKernel L) n = ((L-n.natAbs : ℕ) : ℂ) / L := by
  classical
  unfold coefficient
  simp_rw [fejerKernel_expansion, mul_left_comm (character (-n) _),
    integral_const_mul, mul_sum, ← character_add]
  rw [integral_finsetSum]
  · have hInt (i j : Fin L) : Integrable
        (fun x : FourierCircle => character (-n+((i:ℤ)-(j:ℤ))) x) circleMeasure :=
      (character _).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hInner (i : Fin L) := integral_finsetSum Finset.univ (fun j _ => hInt i j)
    simp_rw [hInner, character_integral]
    have he : (∑ i : Fin L, ∑ j : Fin L,
        if -n+((i:ℤ)-(j:ℤ))=0 then (1 : ℂ) else 0) =
        (Fintype.card (differencePairs L n) : ℂ) := by
      rw [← Fintype.sum_prod_type']
      have hp (p : Fin L × Fin L) :
          -n+((p.1:ℤ)-(p.2:ℤ))=0 ↔ (p.1:ℤ)-(p.2:ℤ)=n := by omega
      simp_rw [hp]
      simp only [Finset.sum_boole, differencePairs]
      rw [Fintype.card_subtype]
    rw [he, card_differencePairs, div_eq_mul_inv]
    ring
  · intro i hi
    exact (by fun_prop : Continuous fun x : FourierCircle =>
      ∑ j : Fin L, character (-n+((i:ℤ)-(j:ℤ))) x).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem integral_norm_fejerKernel (L : ℕ) [NeZero L] :
    ∫ x, ‖fejerKernel L x‖ ∂circleMeasure = 1 := by
  have hnonneg (x : FourierCircle) :
      0 ≤ ‖oneSidedDirichlet L x‖^2/(L : ℝ) := by positivity
  have he (x : FourierCircle) :
      (‖fejerKernel L x‖ : ℂ) = fejerKernel L x := by
    change (‖((‖oneSidedDirichlet L x‖^2 / (L : ℝ) : ℝ) : ℂ)‖ : ℂ) = _
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg x)]
    rfl
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [he]
  have hc := coefficient_fejerKernel L 0
  simpa [coefficient, NeZero.ne L, character_zero] using hc

noncomputable def valleeKernel (L : ℕ) : CircleFunction :=
  (2 : ℂ) • fejerKernel (2*L) - fejerKernel L

theorem integral_norm_valleeKernel_le (L : ℕ) [NeZero L] :
    ∫ x, ‖valleeKernel L x‖ ∂circleMeasure ≤ 3 := by
  have : NeZero (2*L) := ⟨mul_ne_zero (by decide) (NeZero.ne L)⟩
  calc
    _ ≤ ∫ x, 2*‖fejerKernel (2*L) x‖+‖fejerKernel L x‖ ∂circleMeasure := by
      apply integral_mono
      · exact (valleeKernel L).continuous.norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (by fun_prop : Continuous fun x : FourierCircle =>
          2*‖fejerKernel (2*L) x‖+‖fejerKernel L x‖).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro x
        simpa [valleeKernel, norm_mul] using
          norm_sub_le ((2 : ℂ)*fejerKernel (2*L) x) (fejerKernel L x)
    _ = 3 := by
      rw [integral_add, integral_const_mul, integral_norm_fejerKernel,
        integral_norm_fejerKernel]
      · norm_num
      · exact ((fejerKernel (2*L)).continuous.norm.const_mul 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (fejerKernel L).continuous.norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

theorem coefficient_valleeKernel (L : ℕ) (n : ℤ) :
    coefficient (valleeKernel L) n =
      2*(((2*L-n.natAbs : ℕ) : ℂ)/(2*L))-
        (((L-n.natAbs : ℕ) : ℂ)/L) := by
  unfold coefficient valleeKernel
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    mul_sub, mul_left_comm (character (-n) _)]
  rw [integral_sub, integral_const_mul]
  · change 2*coefficient (fejerKernel (2*L)) n-coefficient (fejerKernel L) n = _
    simp [coefficient_fejerKernel]
  · exact (by fun_prop : Continuous fun x : FourierCircle =>
      2*(character (-n) x*fejerKernel (2*L) x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (by fun_prop : Continuous fun x : FourierCircle =>
      character (-n) x*fejerKernel L x).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem coefficient_valleeKernel_low (L : ℕ) [NeZero L] (n : ℤ)
    (hn : n.natAbs ≤ L) : coefficient (valleeKernel L) n = 1 := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [coefficient_valleeKernel, Nat.cast_sub (by omega), Nat.cast_sub hn]
  push_cast
  field_simp [hL]
  ring

theorem coefficient_valleeKernel_high (L : ℕ) (n : ℤ)
    (hn : 2*L ≤ n.natAbs) : coefficient (valleeKernel L) n = 0 := by
  simp [coefficient_valleeKernel, Nat.sub_eq_zero_of_le hn,
    Nat.sub_eq_zero_of_le (show L ≤ n.natAbs by omega)]

theorem convolution_character (K : CircleFunction) (n : ℤ) (x : FourierCircle) :
    circleConvolution K (character n) x = character n x * coefficient K n := by
  unfold circleConvolution coefficient
  simp_rw [character_sub]
  rw [show (fun y => K y*(character n x*character (-n) y)) =
      fun y => character n x*(character (-n) y*K y) by funext y; ring,
    integral_const_mul]

theorem vallee_low_character (L : ℕ) [NeZero L] (n : ℤ)
    (hn : n.natAbs ≤ L) (x : FourierCircle) :
    circleConvolution (valleeKernel L) (character n) x = character n x := by
  simp [convolution_character, coefficient_valleeKernel_low L n hn]

theorem vallee_high_character (L : ℕ) (n : ℤ)
    (hn : 2*L ≤ n.natAbs) (x : FourierCircle) :
    circleConvolution (valleeKernel L) (character n) x = 0 := by
  simp [convolution_character, coefficient_valleeKernel_high L n hn]

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.Spectrum ===== -/
section

noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Finite trigonometric spectrum, as a genuine subspace of circle functions. -/
noncomputable def spectrumSpace (s : Set ℤ) : Submodule ℂ CircleFunction :=
  Submodule.span ℂ (character '' s)

noncomputable def bandSpace (k : ℕ) : Submodule ℂ CircleFunction :=
  spectrumSpace (Set.Icc (-(k:ℤ)) k)

theorem character_mem_spectrum {s : Set ℤ} {j : ℤ} (hj : j∈s) :
    character j∈spectrumSpace s := subset_span ⟨j,hj,rfl⟩

theorem spectrum_mono {s t : Set ℤ} (hst : s⊆t) : spectrumSpace s≤ spectrumSpace t :=
  span_mono (image_mono hst)

theorem spectrum_mul {s t u : Set ℤ} (hsum : ∀j∈s,∀k∈t,j+k∈u)
    {f g : CircleFunction} (hf : f∈spectrumSpace s) (hg : g∈spectrumSpace t) :
    f*g∈spectrumSpace u := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    induction hg using Submodule.span_induction with
    | mem g hg =>
      rcases hg with ⟨k,hk,rfl⟩
      have he : character j*character k=character (j+k) := by
        ext x; exact (character_add j k x).symm
      rw [he]
      exact character_mem_spectrum (hsum j hj k hk)
    | zero => simp
    | add f g hf hg ihf ihg =>
      simpa [mul_add] using (spectrumSpace u).add_mem ihf ihg
    | smul c f hf ih =>
      simpa [mul_smul_comm] using (spectrumSpace u).smul_mem c ih
  | zero => simp
  | add f g hf hg ihf ihg =>
    simpa [add_mul] using (spectrumSpace u).add_mem ihf ihg
  | smul c f hf ih =>
    simpa [smul_mul_assoc] using (spectrumSpace u).smul_mem c ih

theorem band_mul {k l : ℕ} {f g : CircleFunction}
    (hf : f∈bandSpace k) (hg : g∈bandSpace l) : f*g∈bandSpace (k+l) := by
  apply spectrum_mul (s := Set.Icc (-(k:ℤ)) k) (t := Set.Icc (-(l:ℤ)) l) _ hf hg
  intro j hj n hn
  simp only [Set.mem_Icc] at *
  constructor <;> omega

noncomputable def translateCircle (v : FourierCircle) (f : CircleFunction) : CircleFunction where
  toFun x := f (x+v)
  continuous_toFun := by fun_prop

noncomputable def reflectCircle (v : FourierCircle) (f : CircleFunction) : CircleFunction where
  toFun x := f (v-x)
  continuous_toFun := by fun_prop

theorem translate_character (v : FourierCircle) (j : ℤ) :
    translateCircle v (character j) = character j v • character j := by
  ext x
  simp [translateCircle,character_translate,mul_comm]

theorem reflect_character (v : FourierCircle) (j : ℤ) :
    reflectCircle v (character j) = character j v • character (-j) := by
  ext x
  simp [reflectCircle,character_sub]

theorem translate_spectrum (v : FourierCircle) {s : Set ℤ} {f : CircleFunction}
    (hf : f∈spectrumSpace s) : translateCircle v f∈spectrumSpace s := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    rw [translate_character]
    exact (spectrumSpace s).smul_mem _ (character_mem_spectrum hj)
  | zero =>
    change (0 : CircleFunction) ∈ spectrumSpace s
    exact (spectrumSpace s).zero_mem
  | add f g hf hg ihf ihg =>
    have he : translateCircle v (f+g)=translateCircle v f+translateCircle v g := by ext; rfl
    rw [he]; exact (spectrumSpace s).add_mem ihf ihg
  | smul c f hf ih =>
    have he : translateCircle v (c•f)=c•translateCircle v f := by ext; rfl
    rw [he]; exact (spectrumSpace s).smul_mem _ ih

theorem reflect_band (v : FourierCircle) {k : ℕ} {f : CircleFunction}
    (hf : f∈bandSpace k) : reflectCircle v f∈bandSpace k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    rw [reflect_character]
    apply (bandSpace k).smul_mem
    exact character_mem_spectrum (by simp only [Set.mem_Icc] at *; constructor <;> omega)
  | zero =>
    change (0 : CircleFunction) ∈ bandSpace k
    exact (bandSpace k).zero_mem
  | add f g hf hg ihf ihg =>
    have he : reflectCircle v (f+g)=reflectCircle v f+reflectCircle v g := by ext; rfl
    rw [he]; exact (bandSpace k).add_mem ihf ihg
  | smul c f hf ih =>
    have he : reflectCircle v (c•f)=c•reflectCircle v f := by ext; rfl
    rw [he]; exact (bandSpace k).smul_mem _ ih

theorem convolution_add_right (K f g : CircleFunction) (x : FourierCircle) :
    circleConvolution K (f+g) x =circleConvolution K f x+circleConvolution K g x := by
  unfold circleConvolution
  simp only [ContinuousMap.add_apply,mul_add]
  rw [integral_add]
  all_goals
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _

theorem convolution_smul_right (K f : CircleFunction) (c : ℂ)
    (x : FourierCircle) : circleConvolution K (c•f) x=c*circleConvolution K f x := by
  unfold circleConvolution
  simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_left_comm (K _),integral_const_mul]

theorem convolution_sub_right (K f g : CircleFunction) (x : FourierCircle) :
    circleConvolution K (f-g) x =circleConvolution K f x-circleConvolution K g x := by
  unfold circleConvolution
  simp only [ContinuousMap.sub_apply,mul_sub]
  rw [integral_sub]
  all_goals
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _

theorem vallee_fixes_band (L : ℕ) [NeZero L] {f : CircleFunction}
    (hf : f∈bandSpace L) : ∀x,circleConvolution (valleeKernel L) f x=f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    intro x
    exact vallee_low_character L j (by
      have : |j|≤ (L:ℤ) := abs_le.mpr hj
      exact Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using this)) x
  | zero => simp [circleConvolution]
  | add f g hf hg ihf ihg =>
    intro x
    rw [convolution_add_right,ihf,ihg,ContinuousMap.add_apply]
  | smul c f hf ih =>
    intro x
    rw [convolution_smul_right,ih]
    rfl

theorem vallee_kills_high (L : ℕ) {f : CircleFunction}
    (hf : f∈spectrumSpace {j : ℤ | 2*L≤ j.natAbs}) :
    ∀x,circleConvolution (valleeKernel L) f x=0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    exact vallee_high_character L j hj
  | zero => simp [circleConvolution]
  | add f g hf hg ihf ihg =>
    intro x
    rw [convolution_add_right,ihf,ihg,add_zero]
  | smul c f hf ih =>
    intro x
    rw [convolution_smul_right,ih,mul_zero]

/-- Recover a finite coefficient list rather than assuming a Fourier expansion. -/
theorem band_expansion {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    ∃c : ℤ→ℂ,f=finiteFourier (Finset.Icc (-(k:ℤ)) k) c := by
  have hs : (Set.Icc (-(k:ℤ)) k)=(Finset.Icc (-(k:ℤ)) k : Set ℤ) := by ext; simp
  rw [bandSpace,spectrumSpace,hs,Submodule.mem_span_image_finset_iff_exists_fun'] at hf
  obtain ⟨c,hc⟩ := hf
  exact ⟨c,hc.symm⟩

theorem fejerGridWeight_band (L : ℕ) [NeZero L] (q : ZMod L) :
    (⟨fun x => (fejerGridWeight L q x : ℂ),by fun_prop⟩ : CircleFunction)
      ∈bandSpace (L-1) := by
  have he : (⟨fun x => (fejerGridWeight L q x : ℂ),by fun_prop⟩ : CircleFunction) =
      (1/(L:ℂ)^2) •
        ∑i:Fin L,∑j:Fin L,translateCircle (-circleGrid L q)
          (character ((i:ℤ)-(j:ℤ))) := by
    ext x
    simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul]
    change ((‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2 : ℝ) : ℂ) =
      (1/(L:ℂ)^2) * ∑ i : Fin L, ∑ j : Fin L,
        character ((i:ℤ)-(j:ℤ)) (x + -circleGrid L q)
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,
      normSq_dirichlet_expansion,sub_eq_add_neg]
    ring
  rw [he]
  apply (bandSpace (L-1)).smul_mem
  apply (bandSpace (L-1)).sum_mem
  intro i hi
  apply (bandSpace (L-1)).sum_mem
  intro j hj
  apply translate_spectrum
  apply character_mem_spectrum
  have hi := i.isLt
  have hj := j.isLt
  simp only [Set.mem_Icc]
  constructor <;> omega

theorem fejerGridCombination_band (L : ℕ) [NeZero L] (a : ZMod L→ℂ) :
    fejerGridCombination L a∈bandSpace (L-1) := by
  have he : fejerGridCombination L a =
      ∑q:ZMod L,a q•(⟨fun x => (fejerGridWeight L q x:ℂ),by fun_prop⟩ : CircleFunction) := by
    ext x; simp [fejerGridCombination]
  rw [he]
  exact (bandSpace (L-1)).sum_mem fun q hq =>
    (bandSpace (L-1)).smul_mem _ (fejerGridWeight_band L q)

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.SinePolynomial ===== -/
section

/-!
Uniform bound for the harmonic sine polynomial.  The Abel estimate, the short
initial block and the long oscillatory tail are proved separately; the bound is
absolute, not logarithmic in the degree.  This supplies the bounded input in
Privalov's construction while its low-frequency part has harmonic-size value.
-/
noncomputable section
open scoped BigOperators Real
open Finset Set
namespace OMA.Port1.E1152

private theorem abel_finite (z w : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n+1), w j*z j =
      w n*(∑ j ∈ range (n+1), z j) +
      ∑ j ∈ range n, (w j-w (j+1))*(∑ k ∈ range (j+1), z k) := by
  induction n with
  | zero => simp [character_zero]
  | succ n ih =>
    rw [sum_range_succ, ih]
    rw [sum_range_succ (f := fun j =>
      (w j-w (j+1))*(∑ k ∈ range (j+1), z k)) (n := n)]
    rw [sum_range_succ (f := z) (n := n+1)]
    ring

/-- Abel's finite inequality with decreasing nonnegative weights. -/
theorem abs_weighted_sum_le (z w : ℕ → ℝ) (n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hw : ∀j≤ n, 0≤ w j)
    (hmono : ∀j< n, w (j+1)≤ w j)
    (hpartial : ∀j≤ n, |∑k∈range (j+1),z k|≤ C) :
    |∑j∈range (n+1),w j*z j|≤ C*w 0 := by
  rw [abel_finite]
  calc
    _ ≤ |w n*(∑j∈range (n+1),z j)|+
        |∑j∈range n,(w j-w (j+1))*(∑k∈range (j+1),z k)| := abs_add_le _ _
    _ ≤ w n*C+∑j∈range n,(w j-w (j+1))*C := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hw n le_rfl)]
        exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) (hw n le_rfl)
      · apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro j hj
        have hjn := mem_range.mp hj
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hmono j hjn))]
        exact mul_le_mul_of_nonneg_left (hpartial j (by omega))
          (sub_nonneg.mpr (hmono j hjn))
    _ = C*w 0 := by
      rw [← sum_mul, sum_range_sub']
      ring

private theorem sine_step (v t : ℝ) :
    Real.cos (v-t/2)-Real.cos (v+t/2)=2*Real.sin (t/2)*Real.sin v := by
  rw [Real.cos_sub_cos]
  have h1 : (v-t/2+(v+t/2))/2=v := by ring
  have h2 : (v-t/2-(v+t/2))/2=-(t/2) := by ring
  rw [h1,h2,Real.sin_neg]
  ring

theorem partial_sine_identity (a n : ℕ) (t : ℝ) :
    2*Real.sin (t/2)*(∑j∈range n,Real.sin (((a+j : ℕ):ℝ)*t)) =
      Real.cos (((a:ℝ)-1/2)*t)-Real.cos (((a+n:ℕ):ℝ)*t-t/2) := by
  induction n with
  | zero => simp; congr 1 <;> ring
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih]
    have hs := sine_step (((a+n:ℕ):ℝ)*t) t
    rw [← hs]
    push_cast
    ring_nf

private theorem partial_sine_bound (a n : ℕ) {t : ℝ}
    (ht : 0< t) (htπ : t≤ Real.pi) :
    |∑j∈range n,Real.sin (((a+j:ℕ):ℝ)*t)|≤ Real.pi/t := by
  have hs : t/Real.pi≤ Real.sin (t/2) := by
    have hh := Real.mul_le_sin (by linarith : 0≤ t/2) (by linarith : t/2≤ Real.pi/2)
    convert hh using 1 <;> field_simp <;> ring
  have hpos : 0< Real.sin (t/2) := lt_of_lt_of_le (div_pos ht Real.pi_pos) hs
  have hid := congrArg abs (partial_sine_identity a n t)
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0< (2:ℝ)),
    abs_of_pos hpos] at hid
  have hb : |Real.cos (((a:ℝ)-1/2)*t)-Real.cos (((a+n:ℕ):ℝ)*t-t/2)|≤2 := by
    apply (abs_sub _ _).trans
    have h₁ := Real.abs_cos_le_one (((a:ℝ)-1/2)*t)
    have h₂ := Real.abs_cos_le_one (((a+n:ℕ):ℝ)*t-t/2)
    linarith
  have hn : |∑j∈range n,Real.sin (((a+j:ℕ):ℝ)*t)|≤1/Real.sin (t/2) := by
    apply (le_div_iff₀ hpos).mpr
    nlinarith [hb]
  apply hn.trans
  rw [div_le_div_iff₀ hpos ht]
  have := (div_le_iff₀ Real.pi_pos).mp hs
  nlinarith

private theorem weighted_sine_tail (a n : ℕ) (ha : 0< a) {t : ℝ}
    (ht : 0< t) (htπ : t≤ Real.pi) :
    |∑j∈range n,Real.sin (((a+j:ℕ):ℝ)*t)/(a+j:ℕ)|≤
      Real.pi/(t*a) := by
  cases n with
  | zero => simp; positivity
  | succ n =>
    have h := abs_weighted_sum_le
      (fun j => Real.sin (((a+j:ℕ):ℝ)*t))
      (fun j => (1:ℝ)/(a+j:ℕ)) n (Real.pi/t) (by positivity)
      (fun j hj => by positivity)
      (fun j hj => by
        apply one_div_le_one_div_of_le
        · exact_mod_cast (show 0< a+j by omega)
        · exact_mod_cast Nat.le_succ (a+j))
      (fun j hj => partial_sine_bound a (j+1) ht htπ)
    simpa [div_eq_mul_inv, mul_assoc,mul_comm,mul_left_comm] using h

noncomputable def harmonicSine (n : ℕ) (t : ℝ) : ℝ :=
  ∑j∈range n,Real.sin (((j+1:ℕ):ℝ)*t)/(j+1:ℕ)

/-- The uniform harmonic sine bound on the principal half-period. -/
theorem harmonicSine_bound_nonneg (n : ℕ) {t : ℝ}
    (ht : 0≤ t) (htπ : t≤ Real.pi) : |harmonicSine n t|≤1+Real.pi := by
  by_cases hz : t=0
  · simp [harmonicSine,hz]; positivity
  have ht0 : 0< t := lt_of_le_of_ne ht (Ne.symm hz)
  let M : ℕ := ⌊t⁻¹⌋₊
  have hM : (M:ℝ)≤ t⁻¹ := Nat.floor_le (by positivity)
  have hM' : t⁻¹< (M:ℝ)+1 := Nat.lt_floor_add_one _
  have hMt : (M:ℝ)*t≤1 := by
    have := mul_le_mul_of_nonneg_right hM ht
    simpa [inv_mul_cancel₀ hz] using this
  have hMt' : 1≤ ((M:ℝ)+1)*t := by
    have := mul_lt_mul_of_pos_right hM' ht0
    have : 1< ((M:ℝ)+1)*t := by simpa [inv_mul_cancel₀ hz] using this
    exact this.le
  have hsmall (k : ℕ) (hk : k≤ M) : |harmonicSine k t|≤1 := by
    calc
      _ ≤ ∑j∈range k,|Real.sin (((j+1:ℕ):ℝ)*t)/(j+1:ℕ)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑j∈range k,t := by
        apply sum_le_sum
        intro j hj
        rw [abs_div,abs_of_pos (by positivity : 0< ((j+1:ℕ):ℝ)),
          div_le_iff₀ (by positivity)]
        calc
          |Real.sin (((j+1:ℕ):ℝ)*t)|≤|((j+1:ℕ):ℝ)*t| := Real.abs_sin_le_abs
          _ = t*((j+1:ℕ):ℝ) := by rw [abs_of_nonneg (by positivity)]; ring
      _ ≤ 1 := by
        simp only [sum_const,card_range,nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ht).trans hMt
  by_cases hn : n≤ M
  · exact (hsmall n hn).trans (by linarith [Real.pi_pos])
  · have hsplit : harmonicSine n t = harmonicSine M t+
        ∑j∈range (n-M),Real.sin (((M+1+j:ℕ):ℝ)*t)/(M+1+j:ℕ) := by
      conv_lhs => rw [harmonicSine,←Nat.add_sub_of_le (le_of_not_ge hn),sum_range_add]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [show M+j+1 = M+1+j by omega]
    rw [hsplit]
    have htail := weighted_sine_tail (M+1) (n-M) (by omega) ht0 htπ
    have htail' : Real.pi/(t*((M+1:ℕ):ℝ))≤ Real.pi := by
      rw [div_le_iff₀ (by positivity)]
      have hm := mul_le_mul_of_nonneg_left hMt' Real.pi_pos.le
      push_cast
      nlinarith [hm]
    exact (abs_add_le _ _).trans (add_le_add (hsmall M le_rfl) (htail.trans htail'))

theorem harmonicSine_bound (n : ℕ) {t : ℝ} (ht : |t|≤ Real.pi) :
    |harmonicSine n t|≤1+Real.pi := by
  by_cases ht0 : 0≤ t
  · exact harmonicSine_bound_nonneg n ht0 ((le_abs_self t).trans ht)
  · have he : harmonicSine n (-t) = -harmonicSine n t := by
      simp [harmonicSine, mul_neg, Real.sin_neg, neg_div, sum_neg_distrib]
    have h := harmonicSine_bound_nonneg n (by linarith : 0≤-t)
      (by rwa [abs_of_neg (lt_of_not_ge ht0)] at ht)
    simpa [he] using h

noncomputable def privalovLow (A : ℕ) (t : ℝ) : ℝ :=
  ∑j∈range A,Real.cos (((A-1-j:ℕ):ℝ)*t)/(j+1:ℕ)

noncomputable def privalovHigh (A : ℕ) (t : ℝ) : ℝ :=
  ∑j∈range A,Real.cos (((A+1+j:ℕ):ℝ)*t)/(j+1:ℕ)

/-- The two frequency blocks have bounded difference despite the harmonic peak. -/
theorem privalov_split_identity (A : ℕ) (t : ℝ) :
    privalovLow A t-privalovHigh A t =
      2*Real.sin ((A:ℝ)*t)*harmonicSine A t := by
  unfold privalovLow privalovHigh harmonicSine
  rw [←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjA := mem_range.mp hj
  rw [←sub_div,Real.cos_sub_cos]
  have h1 : ((((A-1-j:ℕ):ℝ)*t+((A+1+j:ℕ):ℝ)*t)/2)=(A:ℝ)*t := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast; ring
  have h2 : ((((A-1-j:ℕ):ℝ)*t-((A+1+j:ℕ):ℝ)*t)/2)=-((j+1:ℕ):ℝ)*t := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast; ring
  rw [h1,h2]
  simp only [neg_mul,Real.sin_neg]
  ring

theorem privalov_split_bound (A : ℕ) {t : ℝ} (ht : |t|≤ Real.pi) :
    |privalovLow A t-privalovHigh A t|≤2*(1+Real.pi) := by
  rw [privalov_split_identity,abs_mul,abs_mul]
  calc
    |(2:ℝ)| * |Real.sin ((A:ℝ)*t)| * |harmonicSine A t|
        ≤ 2*1*(1+Real.pi) := by
          gcongr
          · norm_num
          · exact Real.abs_sin_le_one _
          · exact harmonicSine_bound A ht
    _ = 2*(1+Real.pi) := by ring

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.PrivalovProbe ===== -/
section

/-! Explicit low/high trigonometric blocks, and the constraint-annihilating
Fejér grid.  These are the actual finite objects in the sampling lower bound. -/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def cosineCharacter (n : ℤ) : CircleFunction :=
  (2:ℂ)⁻¹ • (character n+character (-n))

theorem character_coe (n : ℤ) (t : ℝ) :
    character n (t : FourierCircle)=Complex.exp (((n:ℝ)*t:ℝ)*Complex.I) := by
  simp only [character,fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem cosineCharacter_coe (n : ℤ) (t : ℝ) :
    cosineCharacter n (t:FourierCircle)=(Real.cos ((n:ℝ)*t):ℂ) := by
  simp only [cosineCharacter,ContinuousMap.smul_apply,ContinuousMap.add_apply,
    smul_eq_mul,character_coe]
  rw [show ((-n : ℤ) : ℝ) * t = -((n : ℝ) * t) by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  ring

noncomputable def probeLow (A d : ℕ) : CircleFunction :=
  ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(A-1-j:ℕ))

noncomputable def probeHigh (A d : ℕ) : CircleFunction :=
  ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(A+1+j:ℕ))

noncomputable def probeNormalization : ℝ := 2*(1+Real.pi)
noncomputable def boundedProbe (A d : ℕ) : CircleFunction :=
  (probeNormalization:ℂ)⁻¹ • (probeLow A d-probeHigh A d)

noncomputable def harmonicHeight (A : ℕ) : ℝ := ∑j∈range A,(1:ℝ)/(j+1:ℕ)

theorem probeNormalization_pos : 0< probeNormalization := by
  unfold probeNormalization; positivity

theorem harmonicHeight_nonneg (A : ℕ) : 0≤ harmonicHeight A := by
  unfold harmonicHeight
  exact sum_nonneg fun _ _ => by positivity

private theorem character_mul_argument (d : ℕ) (n : ℤ) (x : FourierCircle) :
    character ((d:ℤ)*n) x=character n (d•x) := by
  simp only [character,fourier_apply]
  congr 1
  rw [←natCast_zsmul,smul_smul]
  congr 1
  ring

private theorem cosine_mul_argument (d : ℕ) (n : ℤ) (x : FourierCircle) :
    cosineCharacter ((d:ℤ)*n) x=cosineCharacter n (d•x) := by
  simp only [cosineCharacter,ContinuousMap.smul_apply,ContinuousMap.add_apply,smul_eq_mul]
  rw [character_mul_argument,show -((d:ℤ)*n)=(d:ℤ)*(-n) by ring,
    character_mul_argument]

theorem boundedProbe_norm (A d : ℕ) (x : FourierCircle) :
    ‖boundedProbe A d x‖≤1 := by
  let t := AddCircle.equivIco (2*Real.pi) (-Real.pi) (d•x)
  have ht : |(t:ℝ)|≤ Real.pi := by
    have ht₁ := t.2.1
    have ht₂ := t.2.2
    rw [abs_le]
    constructor <;> linarith
  have htx : ((t:ℝ):FourierCircle)=d•x :=
    (AddCircle.equivIco (2*Real.pi) (-Real.pi)).symm_apply_apply _
  have hlo : probeLow A d x=(privalovLow A t:ℂ) := by
    simp only [probeLow,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    simp_rw [cosine_mul_argument,←htx,cosineCharacter_coe]
    simp [privalovLow,div_eq_mul_inv,mul_comm]
  have hhi : probeHigh A d x=(privalovHigh A t:ℂ) := by
    simp only [probeHigh,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    simp_rw [cosine_mul_argument,←htx,cosineCharacter_coe]
    simp [privalovHigh,div_eq_mul_inv,mul_comm]
  simp only [boundedProbe,ContinuousMap.smul_apply,ContinuousMap.sub_apply,
    smul_eq_mul,hlo,hhi,←Complex.ofReal_sub,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos probeNormalization_pos,inv_mul_eq_div,
    div_le_one probeNormalization_pos]
  exact privalov_split_bound A ht

noncomputable def privalovModes (A : ℕ) : Finset ℤ :=
  ((Finset.Icc (-(2*A:ℕ):ℤ) (2*A:ℕ)).erase (-(A:ℤ))).erase (A:ℤ)

theorem mem_privalovModes (A : ℕ) (n : ℤ) :
    n∈privalovModes A ↔ -(2*A:ℕ)≤ n ∧ n≤ (2*A:ℕ) ∧ n≠-(A:ℤ) ∧ n≠(A:ℤ) := by
  simp only [privalovModes,mem_erase,Finset.mem_Icc]
  tauto

theorem card_privalovModes (A : ℕ) (hA : 0< A) :
    (privalovModes A).card=4*A-1 := by
  unfold privalovModes
  rw [card_erase_of_mem,card_erase_of_mem]
  · simp only [Int.card_Icc]
    omega
  · simp only [Finset.mem_Icc]; constructor <;> omega
  · simp only [mem_erase,Finset.mem_Icc]
    constructor
    · omega
    · constructor <;> omega

private theorem low_modes (A j : ℕ) (hj : j< A) :
    ((A-1-j:ℕ):ℤ)∈privalovModes A ∧ -((A-1-j:ℕ):ℤ)∈privalovModes A := by
  constructor <;> rw [mem_privalovModes] <;> constructor <;> omega

private theorem high_modes (A j : ℕ) (hj : j< A) :
    ((A+1+j:ℕ):ℤ)∈privalovModes A ∧ -((A+1+j:ℕ):ℤ)∈privalovModes A := by
  constructor <;> rw [mem_privalovModes] <;> constructor <;> omega

noncomputable def modulationConstraints (A d m : ℕ)
    (ψ : Fin m → CircleFunction →ₗ[ℂ] ℂ) :
    CircleFunction →ₗ[ℂ] ((↥(privalovModes A)) × Fin m → ℂ) where
  toFun f q := ψ q.2 (character ((d:ℤ)*q.1) * f)
  map_add' f g := by ext q; simp [mul_add]
  map_smul' c f := by ext q; simp [mul_smul_comm]

/-- All extra-node constraints are imposed simultaneously by one genuine finite
polynomial. The number of grid coefficients exceeds the number of equations. -/
theorem exists_privalov_grid (A d m : ℕ) (hA : 0< A) (hm : 0< m)
    (ψ : Fin m → CircleFunction →ₗ[ℂ] ℂ) :
    ∃ Q : CircleFunction, ∃ t₀ : FourierCircle,
      Q∈bandSpace (4*m*A-1) ∧ Q t₀=1 ∧ (∀x,‖Q x‖≤1) ∧
      ∀q∈privalovModes A,∀j,ψ j (character ((d:ℤ)*q)*Q)=0 := by
  let L := 4*m*A
  haveI : NeZero L := ⟨by dsimp [L]; positivity⟩
  have hc : Fintype.card (↥(privalovModes A) × Fin m)< L := by
    rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,card_privalovModes A hA]
    dsimp [L]
    have hh : (4*A-1)*m<4*A*m := Nat.mul_lt_mul_of_pos_right (by omega) hm
    nlinarith
  obtain ⟨a,p,hap,han,hΨ,hQn,hQp⟩ := exists_normalized_fejer_annihilator
    L hc (modulationConstraints A d m ψ)
  refine ⟨fejerGridCombination L a,circleGrid L p,fejerGridCombination_band L a,
    hQp,hQn,?_⟩
  intro q hq j
  exact congrFun hΨ (⟨q,hq⟩,j)

private theorem shifted_cosine (v : FourierCircle) (n : ℤ) (Q : CircleFunction) :
    translateCircle v (cosineCharacter n)*Q =
      (2:ℂ)⁻¹ • (character n v • (character n*Q)+
        character (-n) v • (character (-n)*Q)) := by
  ext x
  simp [translateCircle,cosineCharacter,character_translate]
  ring

/-- Each translated probe is killed by the original functionals, not merely a
new predicate recording that it ought to be killed. -/
theorem privalov_probe_constraints (A d m : ℕ)
    (ψ : Fin m → CircleFunction →ₗ[ℂ] ℂ) (Q : CircleFunction)
    (hQ : ∀q∈privalovModes A,∀j,ψ j (character ((d:ℤ)*q)*Q)=0)
    (v : FourierCircle) (j : Fin m) :
    ψ j (translateCircle v (boundedProbe A d)*Q)=0 := by
  have hp (freq : ℕ→ℕ) (hf : ∀i< A,
      (freq i:ℤ)∈privalovModes A ∧ -(freq i:ℤ)∈privalovModes A) :
      ψ j (translateCircle v (∑i∈range A,((i+1:ℕ):ℂ)⁻¹ •
        cosineCharacter ((d:ℤ)*(freq i:ℤ)))*Q)=0 := by
    have he : translateCircle v (∑i∈range A,((i+1:ℕ):ℂ)⁻¹ •
        cosineCharacter ((d:ℤ)*(freq i:ℤ)))*Q =
        ∑i∈range A,((i+1:ℕ):ℂ)⁻¹ •
          (translateCircle v (cosineCharacter ((d:ℤ)*(freq i:ℤ)))*Q) := by
      ext x; simp [translateCircle,sum_mul,mul_assoc]
    rw [he,map_sum]
    apply sum_eq_zero
    intro i hi
    rw [map_smul,shifted_cosine,map_smul,map_add,map_smul,map_smul]
    have h1 := hQ _ (hf i (mem_range.mp hi)).1 j
    have h2 := hQ _ (hf i (mem_range.mp hi)).2 j
    rw [h1,show -((d:ℤ)*(freq i:ℤ))=(d:ℤ)*(-(freq i:ℤ)) by ring,h2]
    simp
  have hl := hp (fun i => A-1-i) (fun i hi => low_modes A i hi)
  have hh := hp (fun i => A+1+i) (fun i hi => high_modes A i hi)
  change ψ j (translateCircle v (probeLow A d)*Q)=0 at hl
  change ψ j (translateCircle v (probeHigh A d)*Q)=0 at hh
  have he : translateCircle v (boundedProbe A d)*Q =
      (probeNormalization:ℂ)⁻¹ •
        (translateCircle v (probeLow A d)*Q-translateCircle v (probeHigh A d)*Q) := by
    ext x
    simp [translateCircle,boundedProbe]
    ring
  rw [he,map_smul,map_sub,hl,hh,sub_self,smul_zero]

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.Privalov ===== -/
section

/-!
Finite Privalov lower bound, with explicit integer parameters.  The theorem is
about an arbitrary projection onto a specified finite trigonometric space and
actual extra linear functionals.  Its conclusion constructs the bounded input;
no sampling lower bound, Bernstein existence theorem or analytic axiom occurs
among its parameters.  Later interpolation specializes the projection.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def operatorOrbit (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ : FourierCircle) (n : ℤ) : CircleFunction :=
  translateCircle (-t₀) (character n) * reflectCircle t₀ (U (character n*Q))

theorem operatorOrbit_apply (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ τ : FourierCircle) (n : ℤ) :
    operatorOrbit U Q t₀ n τ =
      U (translateCircle (τ-t₀) (character n)*Q) (t₀-τ) := by
  rw [translate_character,smul_mul_assoc,map_smul U]
  change character n (τ + -t₀) * U (character n*Q) (t₀-τ) =
    character n (τ-t₀) * U (character n*Q) (t₀-τ)
  simp only [sub_eq_add_neg]

theorem operatorOrbit_low (U : CircleFunction→ₗ[ℂ]CircleFunction) (k l : ℕ)
    (hfix : ∀f∈bandSpace k,U f=f) (Q : CircleFunction) (hQ : Q∈bandSpace l)
    (t₀ : FourierCircle) (n : ℤ) (hn : n.natAbs+l≤ k) :
    operatorOrbit U Q t₀ n=reflectCircle t₀ Q := by
  have hchar : character n∈bandSpace n.natAbs := by
    apply character_mem_spectrum
    change -(n.natAbs:ℤ)≤ n ∧ n≤ (n.natAbs:ℤ)
    simpa using abs_le.mp (le_refl |n|)
  have hprod : character n*Q∈bandSpace k := by
    apply spectrum_mono (s := Set.Icc (-(n.natAbs+l:ℕ):ℤ) (n.natAbs+l:ℕ))
      (t := Set.Icc (-(k:ℤ)) k) _ (band_mul hchar hQ)
    intro j hj
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  unfold operatorOrbit
  rw [hfix _ hprod]
  ext τ
  change character n (τ + -t₀) * (character n (t₀-τ) * Q (t₀-τ)) = Q (t₀-τ)
  rw [←mul_assoc,←character_translate]
  simp [sub_eq_add_neg,add_assoc,character_at_zero]

theorem operatorOrbit_high (U : CircleFunction→ₗ[ℂ]CircleFunction) (k L : ℕ)
    (hrange : ∀f,U f∈bandSpace k) (Q : CircleFunction)
    (t₀ : FourierCircle) (n : ℤ) (hn : k+2*L≤ n.natAbs) :
    operatorOrbit U Q t₀ n∈spectrumSpace {j:ℤ|2*L≤ j.natAbs} := by
  unfold operatorOrbit
  apply spectrum_mul (s := {n}) (t := Set.Icc (-(k:ℤ)) k)
  · intro i hi j hj
    have hin : i=n := mem_singleton_iff.mp hi
    subst i
    have hjb : j.natAbs≤ k := by
      exact Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using abs_le.mpr hj)
    have htri : n.natAbs≤ (n+j).natAbs+j.natAbs := by
      have hh := Int.natAbs_add_le (n+j) (-j)
      simpa using hh
    change 2*L≤ (n+j).natAbs
    omega
  · exact translate_spectrum _ (character_mem_spectrum (mem_singleton n))
  · exact reflect_band t₀ (hrange _)

noncomputable def orbitBlock (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ : FourierCircle) (A d : ℕ) (freq : ℕ→ℕ) : CircleFunction :=
  ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ •
    ((2:ℂ)⁻¹ • (operatorOrbit U Q t₀ ((d:ℤ)*(freq j:ℤ))+
      operatorOrbit U Q t₀ (-((d:ℤ)*(freq j:ℤ)))))

noncomputable def boundedProbeOrbit (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ : FourierCircle) (A d : ℕ) : CircleFunction :=
  (probeNormalization:ℂ)⁻¹ •
    (orbitBlock U Q t₀ A d (fun j => A-1-j)-
      orbitBlock U Q t₀ A d (fun j => A+1+j))

theorem orbitBlock_apply (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ τ : FourierCircle) (A d : ℕ) (freq : ℕ→ℕ) :
    orbitBlock U Q t₀ A d freq τ =
      U (translateCircle (τ-t₀) (∑j∈range A,
        ((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(freq j:ℤ)))*Q) (t₀-τ) := by
  have he : translateCircle (τ-t₀) (∑j∈range A,
      ((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(freq j:ℤ)))*Q =
      ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ •
        ((2:ℂ)⁻¹ •
          (translateCircle (τ-t₀) (character ((d:ℤ)*(freq j:ℤ)))*Q+
           translateCircle (τ-t₀) (character (-((d:ℤ)*(freq j:ℤ))))*Q)) := by
    ext x
    simp [translateCircle,cosineCharacter,sum_mul,mul_add,add_mul,mul_assoc]
  rw [he,map_sum]
  simp only [orbitBlock,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.add_apply,map_smul,map_add,smul_eq_mul,operatorOrbit_apply]

theorem boundedProbeOrbit_apply (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ τ : FourierCircle) (A d : ℕ) :
    boundedProbeOrbit U Q t₀ A d τ =
      U (translateCircle (τ-t₀) (boundedProbe A d)*Q) (t₀-τ) := by
  have he : translateCircle (τ-t₀) (boundedProbe A d)*Q =
      (probeNormalization:ℂ)⁻¹ •
        (translateCircle (τ-t₀) (probeLow A d)*Q-
         translateCircle (τ-t₀) (probeHigh A d)*Q) := by
    ext x; simp [translateCircle,boundedProbe]; ring
  rw [he,map_smul U,map_sub U]
  simp only [boundedProbeOrbit,ContinuousMap.smul_apply,ContinuousMap.sub_apply,
    smul_eq_mul,orbitBlock_apply,probeLow,probeHigh]

private theorem orbitBlock_low (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (A d L k : ℕ) (hfix : ∀f∈bandSpace k,U f=f)
    (Q : CircleFunction) (hQ : Q∈bandSpace (L-1)) (t₀ : FourierCircle)
    (hbudget : (A-1)*d+(L-1)≤ k) :
    orbitBlock U Q t₀ A d (fun j => A-1-j)=
      (harmonicHeight A:ℂ) • reflectCircle t₀ Q := by
  have hc (j : ℕ) (hj : j< A) :
      (((d:ℤ)*(A-1-j:ℕ)):ℤ).natAbs+(L-1)≤ k := by
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have := Nat.mul_le_mul_left d (show A-1-j≤ A-1 by omega)
    nlinarith
  unfold orbitBlock
  apply ContinuousMap.ext
  intro τ
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.add_apply,smul_eq_mul]
  have hs (j : ℕ) (hj : j∈range A) :
      ((j+1:ℕ):ℂ)⁻¹*((2:ℂ)⁻¹*
        (operatorOrbit U Q t₀ ((d:ℤ)*(A-1-j:ℕ)) τ+
         operatorOrbit U Q t₀ (-((d:ℤ)*(A-1-j:ℕ))) τ)) =
      ((j+1:ℕ):ℂ)⁻¹*reflectCircle t₀ Q τ := by
    rw [operatorOrbit_low U k (L-1) hfix Q hQ t₀ _ (hc j (mem_range.mp hj)),
      operatorOrbit_low U k (L-1) hfix Q hQ t₀ _ (by simpa using hc j (mem_range.mp hj))]
    ring
  rw [sum_congr rfl hs,←sum_mul]
  simp [harmonicHeight,div_eq_mul_inv]

private theorem orbitBlock_high (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (A d L k : ℕ) (hrange : ∀f,U f∈bandSpace k)
    (Q : CircleFunction) (t₀ : FourierCircle) (hbudget : k+2*L≤ (A+1)*d) :
    orbitBlock U Q t₀ A d (fun j => A+1+j)∈
      spectrumSpace {n:ℤ|2*L≤ n.natAbs} := by
  unfold orbitBlock
  apply (spectrumSpace _).sum_mem
  intro j hj
  apply (spectrumSpace _).smul_mem
  apply (spectrumSpace _).smul_mem
  apply (spectrumSpace _).add_mem
  · apply operatorOrbit_high U k L hrange
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    nlinarith [Nat.mul_le_mul_left d (show A+1≤ A+1+j by omega)]
  · apply operatorOrbit_high U k L hrange
    simp only [Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast]
    nlinarith [Nat.mul_le_mul_left d (show A+1≤ A+1+j by omega)]

/-- A finite-dimensional Privalov theorem with explicit parameters
`L=4mA`, `d=2L`, `k=Ad`.  The logarithmic growth is supplied by `harmonicHeight A`.
The input is produced by the Fejér grid, not postulated as a sampling witness. -/
theorem finite_privalov (A m : ℕ) (hA : 0< A) (hm : 0< m)
    (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (hrange : ∀f,U f∈bandSpace (8*m*A*A))
    (hfix : ∀f∈bandSpace (8*m*A*A),U f=f)
    (ψ : Fin m→CircleFunction→ₗ[ℂ]ℂ) :
    ∃g : CircleFunction,∃z : FourierCircle,
      (∀x,‖g x‖≤1) ∧ (∀j,ψ j g=0) ∧
      harmonicHeight A/(3*probeNormalization)≤‖U g z‖ := by
  let L := 4*m*A
  let d := 2*L
  let k := 8*m*A*A
  haveI : NeZero L := ⟨by dsimp [L]; positivity⟩
  obtain ⟨Q,t₀,hQband,hQ0,hQnorm,hQψ⟩ := exists_privalov_grid A d m hA hm ψ
  let G := boundedProbeOrbit U Q t₀ A d
  have hlow : orbitBlock U Q t₀ A d (fun j => A-1-j)=
      (harmonicHeight A:ℂ) • reflectCircle t₀ Q := by
    apply orbitBlock_low U A d L k hfix Q hQband t₀
    dsimp [d,L,k]
    have hsub : A-1+1=A := by omega
    nlinarith [Nat.sub_le (4*m*A) 1]
  have hhigh : orbitBlock U Q t₀ A d (fun j => A+1+j)∈
      spectrumSpace {n:ℤ|2*L≤ n.natAbs} := by
    apply orbitBlock_high U A d L k hrange
    dsimp [d,L,k]
    nlinarith
  have hreflect : reflectCircle t₀ Q∈bandSpace L := by
    apply spectrum_mono _ (reflect_band t₀ hQband)
    intro n hn
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  have hfilter : circleConvolution (valleeKernel L) G 0 =
      (harmonicHeight A/(probeNormalization):ℝ) := by
    change circleConvolution (valleeKernel L)
      ((probeNormalization:ℂ)⁻¹ •
        (orbitBlock U Q t₀ A d (fun j => A-1-j)-
         orbitBlock U Q t₀ A d (fun j => A+1+j))) 0 = _
    rw [convolution_smul_right,convolution_sub_right,hlow,
      convolution_smul_right,vallee_fixes_band L hreflect,
      vallee_kills_high L hhigh]
    simp [reflectCircle,hQ0,div_eq_mul_inv,mul_comm]
  obtain ⟨τ,hτ,hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ: Set FourierCircle).Nonempty) G.continuous.norm.continuousOn
  have hnorm : harmonicHeight A/probeNormalization≤3*‖G τ‖ := by
    have hb := norm_convolution_le (valleeKernel L) G ‖G τ‖
      (fun y => hmax (mem_univ y)) 0
    rw [hfilter,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (harmonicHeight_nonneg A) probeNormalization_pos.le)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (integral_norm_valleeKernel_le L) (norm_nonneg _))
  let g := translateCircle (τ-t₀) (boundedProbe A d)*Q
  refine ⟨g,t₀-τ,?_,?_,?_⟩
  · intro x
    change ‖boundedProbe A d (x+(τ-t₀))*Q x‖≤1
    rw [norm_mul]
    exact (mul_le_mul (boundedProbe_norm A d _) (hQnorm x)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro j
    exact privalov_probe_constraints A d m ψ Q hQψ (τ-t₀) j
  · have he : G τ=U g (t₀-τ) := boundedProbeOrbit_apply U Q t₀ τ A d
    rw [←he]
    rw [div_le_iff₀ (mul_pos (by norm_num) probeNormalization_pos)]
    have hh := (div_le_iff₀ probeNormalization_pos).mp hnorm
    nlinarith

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.CircleInterpolation ===== -/
section

/-! Actual trigonometric interpolation and the finite sampling witness.
The original finite node set is arbitrary; no uniform separation is used. -/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule Polynomial
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem character_one_pow (n : ℕ) (x : FourierCircle) :
    character 1 x ^ n=character (n:ℤ) x := by
  induction n with
  | zero => simp [character_zero]
  | succ n ih =>
    rw [pow_succ,ih]
    push_cast
    exact (character_add n 1 x).symm

noncomputable def polynomialCircle (k : ℕ) : ℂ[X]→ₗ[ℂ]CircleFunction where
  toFun p := ⟨fun x => character (-(k:ℤ)) x*p.eval (character 1 x),by fun_prop⟩
  map_add' p q := by ext x; simp [eval_add,mul_add]
  map_smul' c p := by ext x; simp [eval_smul,mul_left_comm]

theorem polynomialCircle_apply (k : ℕ) (p : ℂ[X]) (x : FourierCircle) :
    polynomialCircle k p x=character (-(k:ℤ)) x*p.eval (character 1 x) := rfl

theorem polynomialCircle_X_pow (k n : ℕ) :
    polynomialCircle k ((Polynomial.X:ℂ[X])^n)=character ((n:ℤ)-k) := by
  ext x
  simp only [polynomialCircle_apply,eval_pow,eval_X,character_one_pow]
  rw [←character_add]
  congr 2
  ring

theorem polynomialCircle_band (k : ℕ) (p : ℂ[X]) (hp : p.natDegree≤2*k) :
    polynomialCircle k p∈bandSpace k := by
  have he : polynomialCircle k p =
      ∑i∈range (p.natDegree+1),p.coeff i•character ((i:ℤ)-k) := by
    ext x
    rw [polynomialCircle_apply,Polynomial.eval_eq_sum_range,mul_sum]
    simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    apply sum_congr rfl
    intro i hi
    rw [character_one_pow,mul_left_comm,←character_add]
    congr 2
    ring
  rw [he]
  apply (bandSpace k).sum_mem
  intro i hi
  apply (bandSpace k).smul_mem
  apply character_mem_spectrum
  have hi := mem_range.mp hi
  simp only [Set.mem_Icc]
  constructor <;> omega

theorem exists_polynomialCircle {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    ∃p : ℂ[X],p.natDegree≤2*k ∧ polynomialCircle k p=f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    change -(k:ℤ) ≤ j ∧ j ≤ k at hj
    refine ⟨(Polynomial.X:ℂ[X])^(j+k).toNat,?_,?_⟩
    · simp only [natDegree_X_pow]
      omega
    · rw [polynomialCircle_X_pow]
      congr 1
      omega
  | zero => exact ⟨0,by simp,by simp⟩
  | add f g hf hg ihf ihg =>
    rcases ihf with ⟨p,hp,he⟩
    rcases ihg with ⟨q,hq,he'⟩
    exact ⟨p+q,(natDegree_add_le _ _).trans (max_le hp hq),by simp [he,he']⟩
  | smul c f hf ih =>
    rcases ih with ⟨p,hp,he⟩
    exact ⟨c•p,(natDegree_smul_le c p).trans hp,by simp [he]⟩

theorem character_one_injective : Function.Injective (fun x:FourierCircle => character 1 x) := by
  intro x y h
  have h' : AddCircle.toCircle x=AddCircle.toCircle y := by
    apply Subtype.ext
    simpa [character,fourier_one] using h
  exact AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0) h'

noncomputable def circleInterpolation (k : ℕ) (T : Finset FourierCircle) :
    CircleFunction→ₗ[ℂ]CircleFunction where
  toFun f := polynomialCircle k (Lagrange.interpolate T (fun x=>character 1 x)
    (fun x=>character k x*f x))
  map_add' f g := by
    have he : (fun x=>character k x*(f+g) x)=
        (fun x=>character k x*f x)+(fun x=>character k x*g x) := by
      ext x; simp [mul_add]
    rw [he,map_add,map_add]
  map_smul' c f := by
    have he : (fun x=>character k x*(c•f) x)=c•(fun x=>character k x*f x) := by
      ext x; simp [mul_left_comm]
    rw [he,map_smul,map_smul]
    rfl

theorem circleInterpolation_range (k : ℕ) (T : Finset FourierCircle)
    (hT : T.card=2*k+1) (f : CircleFunction) :
    circleInterpolation k T f∈bandSpace k := by
  apply polynomialCircle_band
  have h := Lagrange.degree_interpolate_le (s := T)
    (fun x=>character k x*f x) character_one_injective.injOn
  apply Polynomial.natDegree_le_of_degree_le
  simpa [hT] using h

theorem circleInterpolation_at_node (k : ℕ) (T : Finset FourierCircle)
    (f : CircleFunction) (x : FourierCircle) (hx : x∈T) :
    circleInterpolation k T f x=f x := by
  change character (-(k:ℤ)) x*
    (Lagrange.interpolate T (fun x=>character 1 x)
      (fun x=>character k x*f x)).eval (character 1 x)=f x
  rw [Lagrange.eval_interpolate_at_node _ character_one_injective.injOn hx,
    ←mul_assoc,←character_add]
  simp [character_zero]

theorem circleInterpolation_fixes (k : ℕ) (T : Finset FourierCircle)
    (hT : T.card=2*k+1) (f : CircleFunction) (hf : f∈bandSpace k) :
    circleInterpolation k T f=f := by
  obtain ⟨p,hp,rfl⟩ := exists_polynomialCircle hf
  have hv : ∀x,character k x*polynomialCircle k p x=p.eval (character 1 x) := by
    intro x
    rw [polynomialCircle_apply,←mul_assoc,←character_add]
    simp [character_zero]
  change polynomialCircle k (Lagrange.interpolate T (fun x=>character 1 x)
    (fun x=>character k x*polynomialCircle k p x))=polynomialCircle k p
  simp_rw [hv]
  congr 1
  symm
  apply Lagrange.eq_interpolate character_one_injective.injOn
  rw [hT]
  exact (Polynomial.degree_le_of_natDegree_le hp).trans_lt (by exact_mod_cast Nat.lt_succ_self (2*k))

local instance : Infinite FourierCircle := by
  haveI : Infinite (Set.Ico (0:ℝ) (0+2*Real.pi)) := by
    exact (Set.Ico_infinite (by positivity)).to_subtype
  exact Infinite.of_injective _ (AddCircle.equivIco (2*Real.pi) 0).symm.injective

/-- Finite trigonometric sampling lower bound in the exact form needed for
localization. It is now a theorem about every finite node set, not a parameter. -/
theorem finite_trigonometric_sampling_witness (A m : ℕ) (hA : 0< A) (hm : 0< m)
    (Γ : Finset FourierCircle) (hΓ : Γ.card≤2*(8*m*A*A)+m+1) :
    ∃P : CircleFunction,∃z : FourierCircle,
      P∈bandSpace (8*m*A*A) ∧
      (∀x∈Γ,‖P x‖≤1) ∧
      harmonicHeight A/(3*probeNormalization)≤‖P z‖ := by
  classical
  let k := 8*m*A*A
  obtain ⟨S,hΓS,hS⟩ := Infinite.exists_superset_card_eq Γ (2*k+m+1) hΓ
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq
    (show 2*k+1≤ S.card by omega)
  have hrest : (S\T).card=m := by
    rw [card_sdiff_of_subset hTS,hS,hT]
    omega
  let e : (↥(S\T))≃Fin m := Fintype.equivFinOfCardEq (by simpa using hrest)
  let U := circleInterpolation k T
  let ψ : Fin m→CircleFunction→ₗ[ℂ]ℂ := fun j =>
    { toFun := fun f => U f (e.symm j)
      map_add' := by intro f g; simp
      map_smul' := by intro c f; simp }
  obtain ⟨g,z,hg,hψ,hgz⟩ := finite_privalov A m hA hm U
    (circleInterpolation_range k T hT) (circleInterpolation_fixes k T hT) ψ
  refine ⟨U g,z,circleInterpolation_range k T hT g,?_,hgz⟩
  intro x hx
  by_cases hxT : x∈T
  · rw [circleInterpolation_at_node k T g x hxT]
    exact hg x
  · have hxrest : x∈S\T := mem_sdiff.mpr ⟨hΓS hx,hxT⟩
    have he := hψ (e ⟨x,hxrest⟩)
    change U g (e.symm (e ⟨x,hxrest⟩))=0 at he
    have hz : U g x=0 := by simpa using he
    simp [hz]

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.HarmonicBudget ===== -/
section

noncomputable section
open scoped BigOperators Real
open Finset Set Filter
namespace OMA.Port1.E1152

/-- A dyadic block contributes at least one half. -/
theorem harmonicHeight_double (n : ℕ) (hn : 0< n) :
    harmonicHeight n+1/2≤ harmonicHeight (2*n) := by
  rw [show 2*n=n+n by omega]
  unfold harmonicHeight
  rw [sum_range_add]
  apply add_le_add le_rfl
  calc
    (1:ℝ)/2 = ∑j∈range n,(1:ℝ)/(2*n) := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      field_simp
    _ ≤ ∑j∈range n,(1:ℝ)/(n+j+1:ℕ) := by
      apply sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le
      · positivity
      · have := mem_range.mp hj
        exact_mod_cast (show n+j+1≤2*n by omega)

theorem harmonicHeight_pow_two (j : ℕ) :
    1+(j:ℝ)/2≤ harmonicHeight (2^j) := by
  induction j with
  | zero => simp [harmonicHeight]
  | succ j ih =>
    have hs := harmonicHeight_double (2^j) (by positivity)
    rw [Nat.mul_comm 2 (2^j)] at hs
    rw [pow_succ]
    push_cast
    nlinarith [hs]

theorem exists_harmonicHeight_ge (B : ℝ) :
    ∃A : ℕ,0< A ∧ B≤ harmonicHeight A := by
  obtain ⟨j,hj⟩ := exists_nat_gt (2*B)
  refine ⟨2^j,by positivity,?_⟩
  exact (show B≤1+(j:ℝ)/2 by linarith).trans (harmonicHeight_pow_two j)

/-- Explicit parameter family for the finite Bernstein localization.
`m=4q`, `k=32q A²`, `ρ=k+2q`, `R₀=k+q` gives an exact node budget
and a band gap independent of the scale parameter `q`.
-/
def localizationDegree (A q : ℕ) : ℕ := 32*q*A*A
def localizationRadius (A q : ℕ) : ℕ := localizationDegree A q+2*q
noncomputable def localizationInner (A q : ℕ) : ℝ := localizationDegree A q+q
noncomputable def localizationBandwidth (A : ℕ) : ℝ :=
  Real.pi*(32*A*A)/(32*A*A+1)
noncomputable def localizationGamma (A : ℕ) : ℝ :=
  Real.pi/(16*(32*A*A+1))

theorem localization_node_budget (A q : ℕ) :
    2*localizationRadius A q+1=2*(8*(4*q)*A*A)+4*q+1 := by
  unfold localizationRadius localizationDegree
  ring

theorem localization_frequency (A q : ℕ) (hq : 0< q) :
    Real.pi*localizationDegree A q/localizationInner A q=localizationBandwidth A := by
  unfold localizationInner localizationBandwidth localizationDegree
  push_cast
  have hqr : (q:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hd : (32*(A:ℝ)*A+1)≠0 := by positivity
  field_simp [hqr,hd]

theorem localization_gap (A : ℕ) :
    localizationBandwidth A+16*localizationGamma A=Real.pi ∧
      0< localizationGamma A := by
  unfold localizationBandwidth localizationGamma
  constructor
  · field_simp
  · positivity

theorem localization_margin (A q : ℕ) :
    (localizationRadius A q:ℝ)-localizationInner A q=q := by
  unfold localizationRadius localizationInner
  push_cast
  ring

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.NormalizeTrig ===== -/
section

noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def conjugateCircle (f : CircleFunction) : CircleFunction where
  toFun x := conj (f x)
  continuous_toFun := by fun_prop

private theorem conjugate_character (n : ℤ) :
    conjugateCircle (character n)=character (-n) := by
  ext x
  exact (fourier_neg (n := n)).symm

theorem conjugate_band {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    conjugateCircle f∈bandSpace k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨n,hn,rfl⟩
    rw [conjugate_character]
    apply character_mem_spectrum
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  | zero =>
    have he : conjugateCircle 0 = (0 : CircleFunction) := by
      ext x
      simp [conjugateCircle]
    rw [he]
    exact (bandSpace k).zero_mem
  | add f g hf hg ihf ihg =>
    have he : conjugateCircle (f+g)=conjugateCircle f+conjugateCircle g := by
      ext x; simp [conjugateCircle]
    rw [he]; exact (bandSpace k).add_mem ihf ihg
  | smul c f hf ih =>
    have he : conjugateCircle (c•f)=conj c•conjugateCircle f := by
      ext x; simp [conjugateCircle]
    rw [he]; exact (bandSpace k).smul_mem _ ih

noncomputable def realPartCircle (f : CircleFunction) : CircleFunction where
  toFun x := ((f x).re:ℂ)
  continuous_toFun := by fun_prop

theorem realPart_band {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    realPartCircle f∈bandSpace k := by
  have he : realPartCircle f=(2:ℂ)⁻¹•(f+conjugateCircle f) := by
    ext x
    change ((f x).re : ℂ) = (2 : ℂ)⁻¹ * (f x + conj (f x))
    rw [Complex.add_conj]
    push_cast
    ring
  rw [he]
  exact (bandSpace k).smul_mem _ ((bandSpace k).add_mem hf (conjugate_band hf))

/-- Normalize at an actual maximum, rotate its phase and take its real part.
Both the global bound and all node bounds survive with constants independent
of the positions of the nodes. -/
theorem normalized_real_trig_witness {k : ℕ} (Γ : Finset FourierCircle)
    (M : ℝ) (hM : 0< M) (P : CircleFunction) (hP : P∈bandSpace k)
    (hnodes : ∀x∈Γ,‖P x‖≤1) (z : FourierCircle) (hz : M≤‖P z‖) :
    ∃Q : CircleFunction,∃t₀ : FourierCircle,
      Q∈bandSpace k ∧ Q t₀=(M:ℂ) ∧
      (∀x,(Q x).im=0) ∧ (∀x,‖Q x‖≤ M) ∧ (∀x∈Γ,‖Q x‖≤1) := by
  obtain ⟨t₀,ht₀,hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ:Set FourierCircle).Nonempty) P.continuous.norm.continuousOn
  have hP0 : 0<‖P t₀‖ := lt_of_lt_of_le hM (hz.trans (hmax (mem_univ z)))
  let c : ℂ := (M:ℂ)/P t₀
  have hc : ‖c‖=M/‖P t₀‖ := by
    simp [c,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
  have hc1 : ‖c‖≤1 := by
    rw [hc,div_le_one hP0]
    exact hz.trans (hmax (mem_univ z))
  let Q := realPartCircle (c•P)
  have hQP : Q∈bandSpace k := realPart_band ((bandSpace k).smul_mem c hP)
  have hreal (x) : (Q x).im=0 := by simp [Q,realPartCircle]
  have hnorm (x) : ‖Q x‖≤‖c‖*‖P x‖ := by
    change ‖((c*P x).re : ℂ)‖ ≤ ‖c‖*‖P x‖
    rw [Complex.norm_real,Real.norm_eq_abs]
    simpa only [norm_mul] using Complex.abs_re_le_norm (c*P x)
  refine ⟨Q,t₀,hQP,?_,hreal,?_,?_⟩
  · change ((c*P t₀).re : ℂ) = (M : ℂ)
    dsimp only [c]
    rw [div_mul_cancel₀ _ (norm_pos_iff.mp hP0)]
    rfl
  · intro x
    apply (hnorm x).trans
    rw [hc]
    calc
      M/‖P t₀‖*‖P x‖≤ M/‖P t₀‖*‖P t₀‖ :=
        mul_le_mul_of_nonneg_left (hmax (mem_univ x)) (by positivity)
      _=M := div_mul_cancel₀ _ hP0.ne'
  · intro x hx
    exact (hnorm x).trans ((mul_le_mul hc1 (hnodes x hx) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))

/-- A uniformly normalized real trigonometric witness for every finite node set
within the explicit finite sampling budget. -/
theorem real_trig_sampling (A q : ℕ) (hA : 0< A) (hq : 0< q)
    (Γ : Finset FourierCircle) (hΓ : Γ.card≤2*localizationRadius A q+1)
    (M : ℝ) (hM : 0< M) (hheight : M≤ harmonicHeight A/(3*probeNormalization)) :
    ∃Q : CircleFunction,∃t₀ : FourierCircle,
      Q∈bandSpace (localizationDegree A q) ∧ Q t₀=(M:ℂ) ∧
      (∀x,(Q x).im=0) ∧ (∀x,‖Q x‖≤ M) ∧ (∀x∈Γ,‖Q x‖≤1) := by
  obtain ⟨P,z,hP,hPn,hPz⟩ := finite_trigonometric_sampling_witness A (4*q) hA
    (by omega) Γ (by rwa [localization_node_budget] at hΓ)
  have hk : 8*(4*q)*A*A=localizationDegree A q := by unfold localizationDegree; ring
  rw [hk] at hP
  exact normalized_real_trig_witness Γ M hM P hP hPn z (hheight.trans hPz)

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.EntireSinc ===== -/
section

noncomputable section
open scoped Topology Real
open MeasureTheory Set Filter
namespace OMA.Port1.E1152

/-- Unnormalized entire sinc: `sin z/z`, with its removable value filled in. -/
def entireSinc (z : ℂ) : ℂ := if z=0 then 1 else Complex.sin z/z

theorem entireSinc_eq_dslope : entireSinc=dslope Complex.sin 0 := by
  ext z
  by_cases hz : z=0
  · simp [entireSinc,hz,dslope_same]
  · simp [entireSinc,hz,dslope_of_ne Complex.sin hz,slope,div_eq_mul_inv,mul_comm]

theorem differentiable_entireSinc : Differentiable ℂ entireSinc := by
  rw [entireSinc_eq_dslope]
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr
      Complex.differentiable_sin.differentiableOn)

theorem entireSinc_zero : entireSinc 0=1 := by simp [entireSinc]

theorem entireSinc_real (x : ℝ) : entireSinc (x:ℂ)=(Real.sinc x:ℂ) := by
  by_cases hx : x=0
  · simp [hx, entireSinc_zero]
  · simp [entireSinc,Real.sinc,hx,Complex.ofReal_eq_zero,Complex.ofReal_sin]

theorem norm_complex_sin_le (z : ℂ) : ‖Complex.sin z‖≤ Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_exp,Complex.norm_exp]
  have h1 : (-(z*Complex.I)).re≤|z.im| := by simp; exact le_abs_self _
  have h2 : (z*Complex.I).re≤|z.im| := by simp; exact neg_le_abs _
  linarith [Real.exp_le_exp.mpr h1,Real.exp_le_exp.mpr h2]

theorem norm_complex_cos_le (z : ℂ) : ‖Complex.cos z‖≤ Real.exp |z.im| := by
  rw [Complex.cos,norm_div]
  norm_num
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  apply (norm_add_le _ _).trans
  rw [Complex.norm_exp,Complex.norm_exp]
  have h1 : (-(z*Complex.I)).re≤|z.im| := by simp; exact le_abs_self _
  have h2 : (z*Complex.I).re≤|z.im| := by simp; exact neg_le_abs _
  linarith [Real.exp_le_exp.mpr h1,Real.exp_le_exp.mpr h2]

/-- An integral representation valid also at the removable point. -/
theorem entireSinc_integral (z : ℂ) :
    entireSinc z=∫t:ℝ in (0:ℝ)..1,Complex.cos (z*t) := by
  by_cases hz : z=0
  · simp [hz, entireSinc_zero]
  have hd (t : ℝ) : HasDerivAt (fun s:ℝ => Complex.sin (z*s)/z)
      (Complex.cos (z*t)) t := by
    apply HasDerivAt.comp_ofReal (e := fun s:ℂ => Complex.sin (z*s)/z)
    simpa only [Function.comp_def, id_eq, mul_one, mul_div_cancel_right₀ _ hz] using
      ((Complex.hasDerivAt_sin (z*t)).comp (t:ℂ)
        ((hasDerivAt_id (t:ℂ)).const_mul z)).div_const z
  have hi : IntervalIntegrable (fun t:ℝ => Complex.cos (z*t)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t) hi]
  simp [entireSinc,hz]

theorem norm_entireSinc_le_exp (z : ℂ) : ‖entireSinc z‖≤ Real.exp |z.im| := by
  rw [entireSinc_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => Complex.cos (z*t))
    (a := (0:ℝ)) (b := 1) (C := Real.exp |z.im|) (fun t ht => ?_)
  · simpa using h
  · apply (norm_complex_cos_le (z*t)).trans
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add,
      abs_mul,Real.norm_eq_abs]
    have ht' : 0≤ t ∧ t≤1 := by
      have htt : 0< t ∧ t≤1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] using ht
      exact ⟨htt.1.le,htt.2⟩
    rw [abs_of_nonneg ht'.1]
    exact mul_le_of_le_one_right (abs_nonneg _) ht'.2

/-- Global algebraic decay with the correct exponential type. -/
theorem norm_entireSinc_decay (z : ℂ) :
    ‖entireSinc z‖≤2*Real.exp |z.im|/(1+‖z‖) := by
  by_cases hz : ‖z‖≤1
  · apply (norm_entireSinc_le_exp z).trans
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos |z.im|]
  · have hn : 0<‖z‖ := by linarith [norm_nonneg z]
    have hzne : z≠0 := norm_pos_iff.mp hn
    rw [entireSinc,if_neg hzne,norm_div]
    apply (div_le_div_of_nonneg_right (norm_complex_sin_le z) hn.le).trans
    rw [div_le_div_iff₀ hn (by positivity)]
    nlinarith [Real.exp_pos |z.im|]

theorem sinc_power_nonneg (γ x : ℝ) : 0≤ Real.sinc (γ*x)^4 := by positivity

theorem sinc_power_le_one (γ x : ℝ) : Real.sinc (γ*x)^4≤1 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one (γ*x)) 4
  simpa only [show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs,one_pow] using h

theorem exists_sinc_fourth_near_one : ∃η>0,∀x:ℝ,|x|≤η→1/2≤ Real.sinc x^4 := by
  have hc := (Real.continuous_sinc.pow 4).continuousAt (x := 0)
  obtain ⟨η,hη,hηc⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  refine ⟨η/2,by positivity,?_⟩
  intro x hx
  have hh := hηc (show dist x 0<η by simpa [Real.dist_eq] using hx.trans_lt (half_lt_self hη))
  simp only [Pi.pow_apply,Real.sinc_zero,one_pow,Real.dist_eq] at hh
  linarith [(abs_lt.mp hh).1]

theorem sinc_fourth_tail {γ d : ℝ} (hγ : 0<γ) (hd : d≠0) :
    Real.sinc (γ*d)^4≤ (1/(γ*|d|))^4 := by
  have hgd : γ*d≠0 := mul_ne_zero hγ.ne' hd
  have h : |Real.sinc (γ*d)|≤1/(γ*|d|) := by
    rw [Real.sinc_of_ne_zero hgd,abs_div,abs_mul,abs_of_pos hγ]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 4
  simpa only [show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs,one_pow] using hh

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.TrigExtension ===== -/
section

noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def trigExtension (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) : ℂ :=
  ∑n∈Finset.Icc (-(k:ℤ)) k,
    coefficient P n*Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)

theorem trigExtension_entire (k : ℕ) (R : ℝ) (P : CircleFunction) :
    Differentiable ℂ (trigExtension k R P) := by
  unfold trigExtension
  fun_prop

theorem trigExtension_real (k : ℕ) (R : ℝ) (P : CircleFunction)
    (hP : P∈bandSpace k) (x : ℝ) :
    trigExtension k R P x=P ((Real.pi*x/R:ℝ):FourierCircle) := by
  obtain ⟨c,hc⟩ := band_expansion hP
  have hcoeff (n : ℤ) (hn : n∈Finset.Icc (-(k:ℤ)) k) : coefficient P n=c n := by
    rw [hc,coefficient_finiteFourier,if_pos hn]
  rw [hc]
  unfold trigExtension
  simp only [finiteFourier_apply]
  apply sum_congr rfl
  intro n hn
  rw [←hc,hcoeff n hn,character_coe]
  congr 2
  push_cast
  ring

private theorem norm_exponential_frequency (n : ℤ) (R : ℝ) (z : ℂ) :
    ‖Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)‖=
      Real.exp (-(Real.pi*n/R:ℝ)*z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp

private theorem frequency_abs_bound {k : ℕ} {n : ℤ}
    (hn : n∈Finset.Icc (-(k:ℤ)) k) {R : ℝ} (hR : 0< R) :
    |Real.pi*n/R|≤ Real.pi*k/R := by
  have hb : |(n:ℝ)|≤ (k:ℝ) := by
    have := abs_le.mpr (Finset.mem_Icc.mp hn)
    exact_mod_cast this
  rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos hR]
  gcongr

private theorem card_int_band (k : ℕ) :
    (Finset.Icc (-(k:ℤ)) k).card = 2*k+1 := by
  rw [Int.card_Icc]
  omega

/-- Exponential type and a coefficient bound uniform over every normalized witness. -/
theorem trigExtension_bound (k : ℕ) (R : ℝ) (hR : 0< R) (P : CircleFunction)
    (z : ℂ) :
    ‖trigExtension k R P z‖≤ (2*k+1:ℕ)*‖P‖*
      Real.exp ((Real.pi*k/R)*|z.im|) := by
  unfold trigExtension
  apply (norm_sum_le _ _).trans
  calc
    (∑n∈Finset.Icc (-(k:ℤ)) k,
      ‖coefficient P n*Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)‖)
      ≤∑n∈Finset.Icc (-(k:ℤ)) k,‖P‖*Real.exp ((Real.pi*k/R)*|z.im|) := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul,norm_exponential_frequency]
        apply mul_le_mul (norm_coefficient_le P n)
        · apply Real.exp_le_exp.mpr
          calc
            -(Real.pi*n/R)*z.im≤|-(Real.pi*n/R)*z.im| := le_abs_self _
            _=|Real.pi*n/R| * |z.im| := by simp [abs_mul]
            _≤_ := mul_le_mul_of_nonneg_right (frequency_abs_bound hn hR) (abs_nonneg _)
        · positivity
        · positivity
    _=(2*k+1:ℕ)*‖P‖*Real.exp ((Real.pi*k/R)*|z.im|) := by
      simp only [sum_const,nsmul_eq_mul,card_int_band]
      ring

noncomputable def trigDerivative (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) : ℂ :=
  ∑n∈Finset.Icc (-(k:ℤ)) k,
    coefficient P n*((Real.pi*n/R:ℂ)*Complex.I)*
      Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)

theorem trigExtension_derivative (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) :
    HasDerivAt (trigExtension k R P) (trigDerivative k R P z) z := by
  unfold trigExtension trigDerivative
  apply HasDerivAt.fun_sum
  intro n hn
  simpa only [id_eq,mul_one,mul_assoc,mul_comm,mul_left_comm] using
    (((hasDerivAt_id z).const_mul (Real.pi*n/R:ℂ)).mul_const Complex.I).cexp.const_mul
      (coefficient P n)

theorem trigDerivative_real_bound (k : ℕ) (R : ℝ) (hR : 0< R)
    (P : CircleFunction) (x : ℝ) :
    ‖trigDerivative k R P x‖≤ ((2*k+1:ℕ):ℝ)*‖P‖*(Real.pi*k/R) := by
  unfold trigDerivative
  apply (norm_sum_le _ _).trans
  calc
    _≤∑n∈Finset.Icc (-(k:ℤ)) k,‖P‖*(Real.pi*k/R) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul,norm_mul,norm_mul,norm_exponential_frequency]
      simp only [Complex.ofReal_im,mul_zero,Real.exp_zero,mul_one,Complex.norm_I,
        Complex.norm_real,Real.norm_eq_abs]
      rw [show (Real.pi*n/R:ℂ) = ((Real.pi*n/R:ℝ):ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (norm_coefficient_le P n) (frequency_abs_bound hn hR)
        (abs_nonneg _) (norm_nonneg _)
    _=_ := by
      simp only [sum_const,nsmul_eq_mul,card_int_band]
      ring

theorem trigExtension_real_lipschitz (k : ℕ) (R : ℝ) (hR : 0< R)
    (P : CircleFunction) (x y : ℝ) :
    ‖trigExtension k R P x-trigExtension k R P y‖≤
      ((2*k+1:ℕ):ℝ)*‖P‖*(Real.pi*k/R)*|x-y| := by
  have hd (t : ℝ) : HasDerivAt (fun u:ℝ => trigExtension k R P u)
      (trigDerivative k R P t) t := (trigExtension_derivative k R P t).comp_ofReal
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t).hasDerivWithinAt)
      (fun t ht => trigDerivative_real_bound k R hR P t)
      (convex_univ : Convex ℝ (Set.univ:Set ℝ))
      (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using hb

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.LocalBernstein ===== -/
section

/-!
Actual local Bernstein functions from finite trigonometric interpolation.
This is the finite version of the Olevskii--Ulanovskii argument (OWP2013-16,
Theorem 3* and its Privalov proof).  Using fixed parameters depending on `B`
avoids formalizing the infinite periodic-set density theorem.  It does not
change the original interpolation nodes or assume a common separation bound.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real Topology
open MeasureTheory Set Finset Filter
namespace OMA.Port1.E1152
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem fourth_tail_budget {M γ q d : ℝ}
    (hM : 1≤ M) (hγ : 0<γ) (hq : M≤γ*q) (hd : q≤|d|) :
    M*Real.sinc (γ*d)^4≤1 := by
  have hq0 : 0< q := by nlinarith
  have hd0 : d≠0 := by intro h; simp [h] at hd; linarith
  have hb := sinc_fourth_tail hγ hd0
  have hx : 1≤γ*|d| := by nlinarith
  have hm : M≤γ*|d| := by nlinarith
  have hp : γ*|d|≤ (γ*|d|)^4 := by
    nlinarith [sq_nonneg (γ*|d|-1),sq_nonneg ((γ*|d|)^2-1)]
  calc
    M*Real.sinc (γ*d)^4≤ M*(1/(γ*|d|))^4 :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    _≤1 := by
      rw [div_pow,one_pow,mul_one_div,div_le_one (by positivity)]
      exact hm.trans hp

/-- Complete finite-node Bernstein conclusion, including the whole exterior
`|x| ≥ ρ`, a uniform positive-length peak interval, and a complex exponential
bound.  All constants precede the arbitrary finite node set. -/
theorem local_bernstein_exists (B : ℝ) (hB : 1< B) :
    ∃ρ : ℕ,∃σ M ℓ K : ℝ,
      0<ρ ∧ 0<σ ∧ σ< Real.pi ∧ 0< M ∧ 0<ℓ ∧ 0< K ∧
      ∀Λ : Finset ℝ,(∀x∈Λ,x∈Icc (-(ρ:ℝ)) ρ)→Λ.card≤2*ρ+1→
      ∃g : ℂ→ℂ,∃a b : ℝ,
        Differentiable ℂ g ∧ (∀x:ℝ,(g x).im=0) ∧
        (∀x:ℝ,‖g x‖≤ M) ∧
        (∀x∈Λ,‖g x‖≤1) ∧ (∀x:ℝ,(ρ:ℝ)≤|x|→‖g x‖≤1) ∧
        a< b ∧ b-a=ℓ ∧ Icc a b⊆Icc (-(ρ:ℝ)) ρ ∧
        (∀x∈Icc a b,2*B≤ (g x).re) ∧
        (∀z:ℂ,‖g z‖≤ K*Real.exp (σ*|z.im|)) := by
  let M : ℝ := 8*B
  have hM : 1≤ M := by dsimp [M]; linarith
  have hM0 : 0< M := by linarith
  obtain ⟨A,hA,hheight⟩ := exists_harmonicHeight_ge (3*probeNormalization*M)
  have hsampling : M≤ harmonicHeight A/(3*probeNormalization) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) probeNormalization_pos)]
    nlinarith
  let γ := localizationGamma A
  have hγ : 0<γ := (localization_gap A).2
  obtain ⟨q,hq⟩ := exists_nat_gt (max 1 (M/γ))
  have hq0 : 0< q := by
    have hqpos : (0:ℝ)< q := lt_trans zero_lt_one
      (lt_of_le_of_lt (le_max_left _ _) hq)
    exact_mod_cast hqpos
  have hqM : M≤γ*q := by
    have h := lt_of_le_of_lt (le_max_right 1 (M/γ)) hq
    rw [div_lt_iff₀ hγ] at h
    nlinarith
  let k := localizationDegree A q
  let ρ := localizationRadius A q
  let R := localizationInner A q
  let σ := localizationBandwidth A+4*γ
  have hR : 0< R := by dsimp [R,localizationInner]; positivity
  have hρ : 0<ρ := by dsimp [ρ,localizationRadius]; omega
  have hmargin : (ρ:ℝ)-R=q := localization_margin A q
  have hσ0 : 0<σ := by
    dsimp [σ,localizationBandwidth]
    positivity
  have hσπ : σ< Real.pi := by
    have hg := (localization_gap A).1
    dsimp [σ,γ] at *
    linarith [(localization_gap A).2]
  let D : ℝ := (2*k+1:ℕ)*M*(Real.pi*k/R)
  have hD : 0≤ D := by dsimp [D]; positivity
  obtain ⟨η,hη,hηs⟩ := exists_sinc_fourth_near_one
  let δ : ℝ := min ((q:ℝ)/2) (min (M/(4*(D+1))) (η/(2*γ)))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδq : δ≤ (q:ℝ)/2 := min_le_left _ _
  have hδD : D*δ≤ M/4 := by
    have hb : δ≤ M/(4*(D+1)) := (min_le_right _ _).trans (min_le_left _ _)
    have hb' := (le_div_iff₀ (by positivity : 0<4*(D+1))).mp hb
    nlinarith
  have hδγ : γ*δ≤η := by
    have hb : δ≤η/(2*γ) := (min_le_right _ _).trans (min_le_right _ _)
    have hb' := (le_div_iff₀ (by positivity : 0<2*γ)).mp hb
    nlinarith
  let K : ℝ := (2*k+1:ℕ)*M
  refine ⟨ρ,σ,M,2*δ,K,hρ,hσ0,hσπ,hM0,by positivity,by dsimp [K]; positivity,?_⟩
  intro Λ hΛ hΛcard
  let θ : ℝ→FourierCircle := fun x => ((Real.pi*x/R:ℝ):FourierCircle)
  let Γ := Λ.image θ
  have hΓ : Γ.card≤2*localizationRadius A q+1 :=
    (Finset.card_image_le).trans hΛcard
  obtain ⟨P,t₀,hP,hP0,hPreal,hPnorm,hPnodes⟩ :=
    real_trig_sampling A q hA hq0 Γ hΓ M hM0 hsampling
  have hPn : ‖P‖≤ M := (ContinuousMap.norm_le P hM0.le).mpr hPnorm
  let t := AddCircle.equivIco (2*Real.pi) (-Real.pi) t₀
  have ht : |(t:ℝ)|≤ Real.pi := by
    have ht₁ := t.2.1
    have ht₂ := t.2.2
    rw [abs_le]
    constructor <;> linarith
  have htc : ((t:ℝ):FourierCircle)=t₀ :=
    (AddCircle.equivIco (2*Real.pi) (-Real.pi)).symm_apply_apply _
  let u₀ : ℝ := R*(t:ℝ)/Real.pi
  have hu₀ : |u₀|≤ R := by
    dsimp [u₀]
    rw [abs_div,abs_mul,abs_of_pos hR,abs_of_pos Real.pi_pos,
      div_le_iff₀ Real.pi_pos]
    nlinarith
  have hθu : θ u₀=t₀ := by
    rw [←htc]
    congr 1
    dsimp [θ,u₀]
    field_simp
  let F := trigExtension k R P
  have hFreal (x : ℝ) : F x=P (θ x) := trigExtension_real k R P hP x
  have hFu : F u₀=(M:ℂ) := by rw [hFreal,hθu,hP0]
  have hFnorm (x : ℝ) : ‖F x‖≤ M := by rw [hFreal]; exact hPnorm _
  have hFlipschitz (x : ℝ) : ‖F x-F u₀‖≤ D*|x-u₀| := by
    apply (trigExtension_real_lipschitz k R hR P x u₀).trans
    dsimp [D]
    gcongr
  let g : ℂ→ℂ := fun z => F z * entireSinc ((γ:ℂ)*(z-u₀))^4
  have greal (x : ℝ) : g x=F x*(Real.sinc (γ*(x-u₀))^4:ℝ) := by
    dsimp [g]
    rw [show (γ:ℂ)*((x:ℂ)-(u₀:ℂ))=((γ*(x-u₀):ℝ):ℂ) by push_cast; rfl,
      entireSinc_real]
    norm_cast
  have gnorm (x : ℝ) : ‖g x‖=‖F x‖*Real.sinc (γ*(x-u₀))^4 := by
    rw [greal,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sinc_power_nonneg γ (x-u₀))]
  refine ⟨g,u₀-δ,u₀+δ,?_,?_,?_,?_,?_,by linarith,by ring,?_,?_,?_⟩
  · exact (trigExtension_entire k R P).mul
      ((differentiable_entireSinc.comp (by fun_prop)).pow 4)
  · intro x
    rw [greal,hFreal]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hPreal,
      mul_zero,zero_mul,add_zero]
  · intro x
    rw [gnorm]
    exact (mul_le_mul (hFnorm x) (sinc_power_le_one γ (x-u₀))
      (sinc_power_nonneg γ (x-u₀)) hM0.le).trans_eq (mul_one M)
  · intro x hx
    rw [gnorm,hFreal]
    exact (mul_le_mul (hPnodes _ (mem_image_of_mem θ hx))
      (sinc_power_le_one γ (x-u₀)) (sinc_power_nonneg γ (x-u₀)) zero_le_one).trans_eq
      (one_mul 1)
  · intro x hx
    rw [gnorm]
    have hd : (q:ℝ)≤|x-u₀| := by
      have htri := abs_sub_le x u₀
      have htri' : |x|≤|x-u₀|+|u₀| := by
        simpa using abs_add_le (x-u₀) u₀
      linarith
    exact (mul_le_mul_of_nonneg_right (hFnorm x) (sinc_power_nonneg γ (x-u₀))).trans
      (fourth_tail_budget hM hγ hqM hd)
  · intro x hx
    have hu := abs_le.mp hu₀
    simp only [Set.mem_Icc] at hx ⊢
    constructor <;> linarith
  · intro x hx
    have hxd : |x-u₀|≤δ := by
      rw [abs_le]
      constructor <;> linarith [hx.1,hx.2]
    have hdiff : |(F x).re-M|≤ M/4 := by
      have hh := (Complex.abs_re_le_norm (F x-F u₀)).trans
        ((hFlipschitz x).trans (mul_le_mul_of_nonneg_left hxd hD))
      rw [hFu] at hh
      simpa using hh.trans hδD
    have hs : 1/2≤ Real.sinc (γ*(x-u₀))^4 := by
      apply hηs
      rw [abs_mul,abs_of_pos hγ]
      exact (mul_le_mul_of_nonneg_left hxd hγ.le).trans hδγ
    rw [greal,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have hf : 3*M/4≤ (F x).re := by linarith [(abs_le.mp hdiff).1]
    have hb := mul_le_mul hf hs (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤ (F x).re)
    dsimp [M] at *
    nlinarith
  · intro z
    have ht := trigExtension_bound k R hR P z
    have hs := norm_entireSinc_le_exp ((γ:ℂ)*(z-u₀))
    have him : |((γ:ℂ)*(z-u₀)).im|=γ*|z.im| := by
      simp [abs_mul,abs_of_pos hγ]
    rw [him] at hs
    have hs4 := pow_le_pow_left₀ (norm_nonneg _) hs 4
    rw [←norm_pow,←Real.exp_nat_mul] at hs4
    dsimp [g]
    rw [norm_mul]
    calc
      _≤ ((2*k+1:ℕ)*M*Real.exp ((Real.pi*k/R)*|z.im|))*
          Real.exp (4*(γ*|z.im|)) := by
            apply mul_le_mul
            · exact ht.trans (by gcongr)
            · convert hs4 using 1 <;> norm_num
            · positivity
            · positivity
      _=K*Real.exp (σ*|z.im|) := by
        rw [mul_assoc,←Real.exp_add]
        dsimp [K,σ,k,R]
        rw [localization_frequency A q hq0]
        congr 2
        ring

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1152.SixthWindow ===== -/
section

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
namespace OMA.Port1.E1152

private theorem exists_sinc_sixth_near_one : ∃η>0,∀x:ℝ,|x|≤η→1/2≤ Real.sinc x^6 := by
  have hc := (Real.continuous_sinc.pow 6).continuousAt (x := 0)
  obtain ⟨η,hη,hcη⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  refine ⟨η/2,by positivity,?_⟩
  intro x hx
  have hdist : dist x 0 < η := by
    simpa [Real.dist_eq] using hx.trans_lt (half_lt_self hη)
  have h := hcη hdist
  simp only [Pi.pow_apply,Real.sinc_zero,one_pow,Real.dist_eq] at h
  linarith [(abs_lt.mp h).1]

private theorem sixth_window_decay {ε : ℝ} (hε : 0<ε) (z : ℂ) :
    ‖entireSinc ((ε:ℂ)*z)^6‖≤
      (2/min 1 ε)^6 * Real.exp (6*ε*|z.im|)/(1+‖z‖)^6 := by
  let c := min 1 ε
  have hc : 0< c := lt_min (by norm_num) hε
  have hd : c*(1+‖z‖)≤1+ε*‖z‖ := by
    have h1 : c≤1 := min_le_left _ _
    have h2 : c≤ε := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg z)]
  have hb := norm_entireSinc_decay ((ε:ℂ)*z)
  simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,
    abs_mul,abs_of_pos hε,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hb
  have hb' : ‖entireSinc ((ε:ℂ)*z)‖≤
      (2/c)*Real.exp (ε*|z.im|)/(1+‖z‖) := by
    apply hb.trans
    have hdn : 0< c*(1+‖z‖) := by positivity
    calc
      2*Real.exp (ε*|z.im|)/(1+ε*‖z‖)
          ≤2*Real.exp (ε*|z.im|)/(c*(1+‖z‖)) := by
            exact div_le_div_of_nonneg_left (by positivity) hdn hd
      _=(2/c)*Real.exp (ε*|z.im|)/(1+‖z‖) := by field_simp
  have hh := pow_le_pow_left₀ (norm_nonneg _) hb' 6
  rw [←norm_pow,div_pow,mul_pow,←Real.exp_nat_mul] at hh
  convert hh using 1 <;> congr 2 <;> ring

/-- The exact decay class used by the sampling and moment-correction construction.
The bandwidth includes the sixth-power window before the auxiliary mesh is chosen. -/
theorem local_bernstein_decay_exists (B : ℝ) (hB : 1< B) :
    ∃ρ : ℕ,∃σ M ℓ C : ℝ,
      0<ρ ∧ 0<σ ∧ σ< Real.pi ∧ 0< M ∧ 0<ℓ ∧ 0< C ∧
      ∀Λ : Finset ℝ,(∀x∈Λ,x∈Icc (-(ρ:ℝ)) ρ)→Λ.card≤2*ρ+1→
      ∃g : ℂ→ℂ,∃a b : ℝ,
        Differentiable ℂ g ∧ (∀x:ℝ,(g x).im=0) ∧
        (∀x:ℝ,‖g x‖≤ M) ∧
        (∀x∈Λ,‖g x‖≤1) ∧ (∀x:ℝ,(ρ:ℝ)≤|x|→‖g x‖≤1) ∧
        a< b ∧ b-a=ℓ ∧ Icc a b⊆Icc (-(ρ:ℝ)) ρ ∧
        (∀x∈Icc a b,B≤ (g x).re) ∧
        (∀z:ℂ,‖g z‖≤ C*Real.exp (σ*|z.im|)/(1+‖z‖)^6) := by
  obtain ⟨ρ,σ₀,M,ℓ,K,hρ,hσ₀,hσπ,hM,hℓ,hK,hdata⟩ := local_bernstein_exists B hB
  obtain ⟨η,hη,hηs⟩ := exists_sinc_sixth_near_one
  let ε := min ((Real.pi-σ₀)/12) (η/(2*(ρ+1)))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεσ : σ₀+6*ε< Real.pi := by
    have h := min_le_left ((Real.pi-σ₀)/12) (η/(2*(ρ+1)))
    dsimp [ε] at *
    linarith
  have hερ : ε*(ρ:ℝ)≤η := by
    have hh : ε≤η/(2*(ρ+1)) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0<2*((ρ:ℝ)+1))).mp hh
    nlinarith
  let C := K*(2/min 1 ε)^6
  refine ⟨ρ,σ₀+6*ε,M,ℓ,C,hρ,by positivity,hεσ,hM,hℓ,by dsimp [C]; positivity,?_⟩
  intro Λ hΛ hcard
  obtain ⟨g₀,a,b,hd,hr,hbound,hnodes,hext,hab,hbl,hsub,hpeak,hgrowth⟩ := hdata Λ hΛ hcard
  let g : ℂ→ℂ := fun z => g₀ z*entireSinc ((ε:ℂ)*z)^6
  have hreal (x : ℝ) : g x=g₀ x*(Real.sinc (ε*x)^6:ℝ) := by
    dsimp [g]
    rw [show (ε:ℂ)*(x:ℂ)=((ε*x:ℝ):ℂ) by push_cast; rfl,entireSinc_real]
    norm_cast
  have hs (x : ℝ) : 0≤ Real.sinc (ε*x)^6 ∧ Real.sinc (ε*x)^6≤1 := by
    refine ⟨by positivity,?_⟩
    have hp := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one (ε*x)) 6
    have hp' : |Real.sinc (ε*x)^6| ≤ 1 := by
      simpa only [abs_pow,one_pow] using hp
    exact (le_abs_self _).trans hp'
  have hn (x : ℝ) : ‖g x‖≤‖g₀ x‖ := by
    rw [hreal,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hs x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hs x).2
  refine ⟨g,a,b,hd.mul ((differentiable_entireSinc.comp (by fun_prop)).pow 6),?_,
    fun x=>(hn x).trans (hbound x),fun x hx=>(hn x).trans (hnodes x hx),
    fun x hx=>(hn x).trans (hext x hx),hab,hbl,hsub,?_,?_⟩
  · intro x
    rw [hreal]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hr,
      mul_zero,zero_mul,add_zero]
  · intro x hx
    have hxρ : |x|≤ρ := abs_le.mpr (hsub hx)
    have hw : 1/2≤ Real.sinc (ε*x)^6 := by
      apply hηs
      rw [abs_mul,abs_of_pos hε]
      exact (mul_le_mul_of_nonneg_left hxρ hε.le).trans hερ
    rw [hreal,Complex.mul_re]
    simp only [Complex.ofReal_im,mul_zero,sub_zero,Complex.ofReal_re]
    have hp := hpeak x hx
    nlinarith [mul_le_mul hp hw (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤ (g₀ x).re)]
  · intro z
    have hw := sixth_window_decay hε z
    dsimp [g]
    rw [norm_mul]
    calc
      _≤ (K*Real.exp (σ₀*|z.im|))*
          ((2/min 1 ε)^6*Real.exp (6*ε*|z.im|)/(1+‖z‖)^6) :=
        mul_le_mul (hgrowth z) hw (norm_nonneg _) (by positivity)
      _=C*Real.exp ((σ₀+6*ε)*|z.im|)/(1+‖z‖)^6 := by
        dsimp [C]
        rw [add_mul,Real.exp_add]
        ring

end OMA.Port1.E1152
end
end

/- ===== OMA.Port1.E1133.Multipeak ===== -/
section

noncomputable section
open scoped BigOperators Real Topology
open Finset Set

namespace OMA.Port1.E1133

/-- The universal summable majorant for separated translates. -/
def squareTailMass : ℝ := ∑' j : ℤ, 1 / (j : ℝ)^2

theorem summable_squareTail : Summable (fun j : ℤ => 1 / (j : ℝ)^2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

theorem squareTailMass_nonneg : 0 ≤ squareTailMass :=
  tsum_nonneg (fun _ => by positivity)

theorem shifted_square_sum_le (s : Finset ℤ) (i : ℤ) :
    ∑ j ∈ s, 1 / ((j-i : ℤ) : ℝ)^2 ≤ squareTailMass := by
  calc
    ∑ j ∈ s, 1 / ((j-i : ℤ) : ℝ)^2 =
        ∑ j ∈ s.image (fun j => j-i), 1 / (j:ℝ)^2 :=
      (Finset.sum_image (s:=s) (g:=fun j:ℤ => j-i)
        (f:=fun j:ℤ => 1/(j:ℝ)^2) (fun a _ b _ h => sub_left_inj.mp h)).symm
    _ ≤ squareTailMass :=
      summable_squareTail.sum_le_tsum _ (fun _ _ => by positivity)

theorem sixth_tail_le_square {C D d : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hd : 0 ≤ d) (j : ℤ) (hj : j ≠ 0)
    (hdist : D*|(j:ℝ)|/2 ≤ d) :
    C/(1+d)^6 ≤ (4*C/D^2) * (1/(j:ℝ)^2) := by
  have hjr : (j:ℝ) ≠ 0 := by exact_mod_cast hj
  have hb : 0 < D*|(j:ℝ)|/2 := by positivity
  have hden : (D*|(j:ℝ)|/2)^2 ≤ (1+d)^6 := by
    calc
      (D*|(j:ℝ)|/2)^2 ≤ d^2 := pow_le_pow_left₀ hb.le hdist 2
      _ ≤ (1+d)^2 := pow_le_pow_left₀ hd (by linarith) 2
      _ ≤ (1+d)^6 := pow_le_pow_right₀ (by linarith) (by omega)
  calc
    C/(1+d)^6 ≤ C/(D*|(j:ℝ)|/2)^2 :=
      div_le_div_of_nonneg_left hC (sq_pos_of_pos hb) hden
    _ = (4*C/D^2) * (1/(j:ℝ)^2) := by
      rw [div_pow,mul_pow,sq_abs]
      field_simp
      ring

/-- Uniform interference of arbitrarily many separated packets. The bound is
independent of the number of selected cells. -/
theorem packet_tail_at_nearest (s : Finset ℤ) (c : ℤ → ℝ) (u : ℤ → ℝ → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (hdecay : ∀ j ∈ s, ∀ x : ℝ, |u j x| ≤ C/(1+|x-c j|)^6)
    (x : ℝ) (i : ℤ) (hi : i ∈ s)
    (hnear : ∀ j ∈ s, |x-c i| ≤ |x-c j|) :
    ∑ j ∈ s.erase i, |u j x| ≤ (4*C/D^2)*squareTailMass := by
  have hpoint : ∀ j ∈ s.erase i,
      |u j x| ≤ (4*C/D^2) * (1/((j-i:ℤ):ℝ)^2) := by
    intro j hj
    have hjs : j ∈ s := mem_of_mem_erase hj
    have hji : j-i ≠ 0 := sub_ne_zero.mpr (ne_of_mem_erase hj)
    have hdist : D*|((j-i:ℤ):ℝ)|/2 ≤ |x-c j| := by
      have ht := abs_sub_le (c j) x (c i)
      rw [abs_sub_comm (c j) x] at ht
      linarith [hsep i hi j hjs,hnear j hjs]
    exact (hdecay j hjs x).trans
      (sixth_tail_le_square hC hD (abs_nonneg _) (j-i) hji hdist)
  calc
    ∑ j ∈ s.erase i, |u j x| ≤
        ∑ j ∈ s.erase i, (4*C/D^2) * (1/((j-i:ℤ):ℝ)^2) :=
      Finset.sum_le_sum hpoint
    _ = (4*C/D^2) * (∑ j ∈ s.erase i, 1/((j-i:ℤ):ℝ)^2) := by
      rw [Finset.mul_sum]
    _ ≤ (4*C/D^2)*squareTailMass :=
      mul_le_mul_of_nonneg_left (shifted_square_sum_le _ _) (by positivity)

theorem nearest_at_peak (s : Finset ℤ) (c : ℤ → ℝ)
    {D ρ : ℝ} (hD : 0 < D) (hgap : 2*ρ ≤ D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (x : ℝ) (i : ℤ) (hi : i ∈ s) (hx : |x-c i| ≤ ρ) :
    ∀ j ∈ s, |x-c i| ≤ |x-c j| := by
  intro j hj
  by_cases hji : j=i
  · subst j
    rfl
  have hone : (1:ℝ) ≤ |((j-i:ℤ):ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hji)
  have hDij : D ≤ |c j-c i| := by
    have h := mul_le_mul_of_nonneg_left hone hD.le
    simpa using h.trans (hsep i hi j hj)
  have ht := abs_sub_le (c j) x (c i)
  rw [abs_sub_comm (c j) x] at ht
  linarith

/-- Exact finite entire superposition; the signs remain completely free. -/
def signedPacketSum (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, (ψ i : ℂ)*g i z

theorem signedPacketSum_real (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ)
    (hr : ∀ i ∈ s, ∀ x : ℝ, (g i x).im=0) (x : ℝ) :
    (signedPacketSum s ψ g x).im=0 := by
  simp only [signedPacketSum,Complex.im_sum,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,add_zero]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hr i hi x,mul_zero]

theorem signedPacketSum_re (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ) (x : ℝ) :
    (signedPacketSum s ψ g x).re = ∑ i ∈ s, ψ i*(g i x).re := by
  simp [signedPacketSum,Complex.mul_re]

theorem signedPacketSum_entire (s : Finset ℤ) (ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ)
    (hg : ∀ i ∈ s, Differentiable ℂ (g i)) :
    Differentiable ℂ (signedPacketSum s ψ g) := by
  unfold signedPacketSum
  apply Differentiable.fun_sum
  intro i hi
  exact (hg i hi).const_mul (ψ i:ℂ)

theorem centered_decay_to_origin (g : ℂ → ℂ) {a C σ : ℝ}
    (_hC : 0 ≤ C)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C*Real.exp (σ*|z.im|)/(1+‖z-(a:ℂ)‖)^6)
    (z : ℂ) :
    ‖g z‖ ≤ (C*(1+|a|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 := by
  have hz : ‖z‖ ≤ ‖z-(a:ℂ)‖+|a| := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using norm_add_le (z-(a:ℂ)) (a:ℂ)
  have hb : 1+‖z‖ ≤ (1+|a|)*(1+‖z-(a:ℂ)‖) := by
    nlinarith [mul_nonneg (abs_nonneg a) (norm_nonneg (z-(a:ℂ)))]
  have hp := pow_le_pow_left₀ (by positivity : 0≤1+‖z‖) hb 6
  rw [mul_pow] at hp
  have hbase := (le_div_iff₀ (by positivity : 0< (1+‖z-(a:ℂ)‖)^6)).mp (hg z)
  apply (le_div_iff₀ (by positivity : 0< (1+‖z‖)^6)).mpr
  calc
    ‖g z‖*(1+‖z‖)^6 ≤ ‖g z‖*((1+|a|)^6*(1+‖z-(a:ℂ)‖)^6) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = (1+|a|)^6*(‖g z‖*(1+‖z-(a:ℂ)‖)^6) := by ring
    _ ≤ (1+|a|)^6*(C*Real.exp (σ*|z.im|)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (C*(1+|a|)^6)*Real.exp (σ*|z.im|) := by ring

/-- A genuine sixth-power bound, sufficient for analytic periodization. The
large prefactor is used only in complex analysis, never for real tail budgets. -/
theorem signedPacketSum_decay (s : Finset ℤ) (c ψ : ℤ → ℝ)
    (g : ℤ → ℂ → ℂ) {C σ : ℝ} (hC : 0 ≤ C)
    (hψ : ∀ i ∈ s, |ψ i|=1)
    (hg : ∀ i ∈ s, ∀ z : ℂ, ‖g i z‖ ≤
      C*Real.exp (σ*|z.im|)/(1+‖z-(c i:ℂ)‖)^6) (z : ℂ) :
    ‖signedPacketSum s ψ g z‖ ≤
      (∑ i ∈ s, C*(1+|c i|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 := by
  calc
    ‖signedPacketSum s ψ g z‖ ≤ ∑ i ∈ s, ‖(ψ i:ℂ)*g i z‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖g i z‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hψ i hi,one_mul]
    _ ≤ ∑ i ∈ s, (C*(1+|c i|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 :=
      Finset.sum_le_sum (fun i hi => centered_decay_to_origin (g i) hC (hg i hi) z)
    _ = (∑ i ∈ s, C*(1+|c i|)^6)*Real.exp (σ*|z.im|)/(1+‖z‖)^6 := by
      rw [←Finset.sum_div,←Finset.sum_mul]

theorem real_norm_eq_abs_re {z : ℂ} (hz : z.im=0) : ‖z‖=|z.re| := by
  rw [←Complex.re_add_im z,hz,Complex.ofReal_zero,zero_mul,add_zero,
    Complex.norm_real,Real.norm_eq_abs]
  simp only [Complex.ofReal_re]

/-- A signed sum retains a large peak if all other packets have bounded total
mass there. This is applied to actual entire packets constructed below. -/
theorem signed_sum_peak {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (hi : i ∈ s) (u ψ : ι → ℝ)
    (hψ : ∀ j ∈ s, |ψ j| = 1) {B E : ℝ}
    (hpeak : B ≤ u i) (htail : ∑ j ∈ s.erase i, |u j| ≤ E) :
    B-E ≤ ψ i * (∑ j ∈ s, ψ j * u j) := by
  have hisq : ψ i * ψ i = 1 := by
    have h := hψ i hi
    have h' := sq_abs (ψ i)
    rw [h] at h'
    nlinarith
  rw [← Finset.add_sum_erase _ _ hi, mul_add, ← mul_assoc, hisq, one_mul]
  have hnorm : |∑ j ∈ s.erase i, ψ j * u j| ≤ E := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ j ∈ s.erase i, |ψ j * u j| = ∑ j ∈ s.erase i, |u j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, hψ j (mem_of_mem_erase hj), one_mul]
      _ ≤ E := htail
  have hm : |ψ i * (∑ j ∈ s.erase i, ψ j * u j)| ≤ E := by
    rw [abs_mul, hψ i hi, one_mul]
    exact hnorm
  linarith [(abs_le.mp hm).1]

theorem signed_sum_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (hi : i ∈ s) (u ψ : ι → ℝ)
    (hψ : ∀ j ∈ s, |ψ j| = 1) {A E : ℝ}
    (hmain : |u i| ≤ A) (htail : ∑ j ∈ s.erase i, |u j| ≤ E) :
    |∑ j ∈ s, ψ j * u j| ≤ A+E := by
  rw [← Finset.add_sum_erase _ _ hi]
  apply (abs_add_le _ _).trans
  have hnorm : |∑ j ∈ s.erase i, ψ j * u j| ≤ E := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ j ∈ s.erase i, |ψ j * u j| = ∑ j ∈ s.erase i, |u j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, hψ j (mem_of_mem_erase hj), one_mul]
      _ ≤ E := htail
  rw [abs_mul, hψ i hi, one_mul]
  exact add_le_add hmain hnorm

/-- Every bound here concerns the constructed finite sum, not an assumed
interpolation operator. Separation makes the estimates uniform in `s.card`. -/
theorem signedPacketSum_estimates (s : Finset ℤ) (hs : s.Nonempty)
    (c p ψ : ℤ → ℝ) (g : ℤ → ℂ → ℂ) {B C D M ρ : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hgap : 2*ρ ≤ D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (hbudget : (4*C/D^2)*squareTailMass ≤ 1)
    (hψ : ∀ i ∈ s, |ψ i|=1)
    (hr : ∀ i ∈ s, ∀ x : ℝ, (g i x).im=0)
    (hb : ∀ i ∈ s, ∀ x : ℝ, ‖g i x‖≤ M)
    (hdecay : ∀ i ∈ s, ∀ x : ℝ, ‖g i x‖≤ C/(1+|x-c i|)^6)
    (hp : ∀ i ∈ s, |p i-c i|≤ρ ∧ B≤ (g i (p i)).re)
    (Γ : Finset ℝ) (hnodes : ∀ i ∈ s, ∀ x ∈ Γ, ‖g i x‖≤1) :
    (∀ x : ℝ, ‖signedPacketSum s ψ g x‖≤ M+1) ∧
    (∀ x ∈ Γ, ‖signedPacketSum s ψ g x‖≤2) ∧
    (∀ i ∈ s, B-1≤ψ i*(signedPacketSum s ψ g (p i)).re) := by
  let u : ℤ → ℝ → ℝ := fun i x => (g i x).re
  have hdec : ∀ i ∈ s, ∀ x : ℝ, |u i x|≤ C/(1+|x-c i|)^6 := by
    intro i hi x
    exact (Complex.abs_re_le_norm _).trans (hdecay i hi x)
  have htail (x : ℝ) (i : ℤ) (hi : i ∈ s)
      (hnear : ∀ j ∈ s, |x-c i|≤|x-c j|) :
      ∑ j ∈ s.erase i, |u j x|≤1 :=
    (packet_tail_at_nearest s c u hC hD hsep hdec x i hi hnear).trans hbudget
  have hnorm (x : ℝ) : ‖signedPacketSum s ψ g x‖=
      |∑ i ∈ s, ψ i*u i x| := by
    rw [real_norm_eq_abs_re (signedPacketSum_real s ψ g hr x),signedPacketSum_re]
  refine ⟨?_,?_,?_⟩
  · intro x
    obtain ⟨i,hi,hnear⟩ := s.exists_min_image (fun i => |x-c i|) hs
    rw [hnorm]
    exact signed_sum_bound s i hi (fun i => u i x) ψ hψ
      ((Complex.abs_re_le_norm _).trans (hb i hi x)) (htail x i hi hnear)
  · intro x hx
    obtain ⟨i,hi,hnear⟩ := s.exists_min_image (fun i => |x-c i|) hs
    rw [hnorm]
    have hh := signed_sum_bound s i hi (fun i => u i x) ψ hψ
      ((Complex.abs_re_le_norm _).trans (hnodes i hi x hx)) (htail x i hi hnear)
    norm_num at hh
    exact hh
  · intro i hi
    rw [signedPacketSum_re]
    exact signed_sum_peak s i hi (fun j => u j (p i)) ψ hψ (hp i hi).2
      (htail (p i) i hi (nearest_at_peak s c hD hgap hsep (p i) i hi (hp i hi).1))


/-- The 957 packets apply to every sparse cell of the actual global node set.
They are small at every global node, including nodes outside that cell. -/
theorem sparse_cell_packets (B : ℝ) (hB : 1 < B) :
    ∃ ρ : ℕ, ∃ σ M C : ℝ,
      0 < ρ ∧ 0 < σ ∧ σ < Real.pi ∧ 0 < M ∧ 0 < C ∧
      ∀ (Γ : Finset ℝ) (a : ℝ),
        (Γ.filter (fun x => |x-a| ≤ ρ)).card ≤ 2*ρ+1 →
        ∃ g : ℂ → ℂ, ∃ p : ℝ,
          Differentiable ℂ g ∧ (∀ x : ℝ, (g x).im = 0) ∧
          (∀ x : ℝ, ‖g x‖ ≤ M) ∧
          (∀ x ∈ Γ, ‖g x‖ ≤ 1) ∧ |p-a| ≤ ρ ∧ B ≤ (g p).re ∧
          (∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ*|z.im|) /
            (1+‖z-(a:ℂ)‖)^6) := by
  obtain ⟨ρ,σ,M,ℓ,C,hρ,hσ,hσπ,hM,hℓ,hC,hdata⟩ :=
    OMA.Port1.E1152.local_bernstein_decay_exists B hB
  refine ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,?_⟩
  intro Γ a hcard
  let Λ := (Γ.filter (fun x => |x-a| ≤ ρ)).image (fun x => x-a)
  have hΛ : ∀ x ∈ Λ, x ∈ Icc (-(ρ:ℝ)) ρ := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact abs_le.mp (mem_filter.mp hy).2
  have hΛcard : Λ.card ≤ 2*ρ+1 := (card_image_le).trans hcard
  obtain ⟨g,l,r,hg,hr,hbound,hnodes,hext,hlr,hlen,hsub,hpeak,hdecay⟩ :=
    hdata Λ hΛ hΛcard
  have hl : l ∈ Icc (-(ρ:ℝ)) ρ := hsub ⟨le_rfl,hlr.le⟩
  refine ⟨fun z => g (z-(a:ℂ)),l+a,hg.comp (by fun_prop),?_,?_,?_,?_,?_,?_⟩
  · intro x
    simpa using hr (x-a)
  · intro x
    simpa using hbound (x-a)
  · intro x hx
    by_cases ha : |x-a| ≤ ρ
    · simpa using hnodes (x-a) (mem_image_of_mem _ (mem_filter.mpr ⟨hx,ha⟩))
    · simpa using hext (x-a) (le_of_lt (lt_of_not_ge ha))
  · simpa using (abs_le.mpr hl)
  · simpa using hpeak l ⟨le_rfl,hlr.le⟩
  · intro z
    simpa using hdecay (z-(a:ℂ))

/-- Actual entire packets, with their peak locations chosen before any signs. -/
structure SparsePacketFamily (Γ : Finset ℝ) (s : Finset ℤ) (c : ℤ → ℝ)
    (B ρ σ M C : ℝ) where
  g : ℤ → ℂ → ℂ
  p : ℤ → ℝ
  entire : ∀ i ∈ s, Differentiable ℂ (g i)
  real : ∀ i ∈ s, ∀ x : ℝ, (g i x).im=0
  bound : ∀ i ∈ s, ∀ x : ℝ, ‖g i x‖≤ M
  nodes : ∀ i ∈ s, ∀ x ∈ Γ, ‖g i x‖≤1
  near : ∀ i ∈ s, |p i-c i|≤ρ
  peak : ∀ i ∈ s, B≤ (g i (p i)).re
  decay : ∀ i ∈ s, ∀ z : ℂ,
    ‖g i z‖≤ C*Real.exp (σ*|z.im|)/(1+‖z-(c i:ℂ)‖)^6

theorem sparse_packet_family_exists (B : ℝ) (hB : 1< B) :
    ∃ ρ : ℕ, ∃ σ M C : ℝ,
      0<ρ ∧ 0<σ ∧ σ< Real.pi ∧ 0< M ∧ 0< C ∧
      ∀ (Γ : Finset ℝ) (s : Finset ℤ) (c : ℤ → ℝ),
        (∀ i ∈ s, (Γ.filter (fun x => |x-c i|≤ρ)).card≤2*ρ+1) →
        Nonempty (SparsePacketFamily Γ s c B ρ σ M C) := by
  obtain ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,hdata⟩ := sparse_cell_packets B hB
  refine ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,?_⟩
  intro Γ s c hsparse
  have hlocal := fun i : s => hdata Γ (c i) (hsparse i i.property)
  choose g₀ p₀ hd hr hb hn hp hpk hdec using hlocal
  let g : ℤ → ℂ → ℂ := fun i => if hi:i∈s then g₀ ⟨i,hi⟩ else 0
  let p : ℤ → ℝ := fun i => if hi:i∈s then p₀ ⟨i,hi⟩ else 0
  refine ⟨⟨g,p,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i hi
    simpa [g,hi] using hd ⟨i,hi⟩
  · intro i hi x
    simpa [g,hi] using hr ⟨i,hi⟩ x
  · intro i hi x
    simpa [g,hi] using hb ⟨i,hi⟩ x
  · intro i hi x hx
    simpa [g,hi] using hn ⟨i,hi⟩ x hx
  · intro i hi
    simpa [p,hi] using hp ⟨i,hi⟩
  · intro i hi
    simpa [p,g,hi] using hpk ⟨i,hi⟩
  · intro i hi z
    simpa [g,hi] using hdec ⟨i,hi⟩ z

theorem SparsePacketFamily.real_decay
    {Γ : Finset ℝ} {s : Finset ℤ} {c : ℤ → ℝ} {B ρ σ M C : ℝ}
    (F : SparsePacketFamily Γ s c B ρ σ M C) :
    ∀ i ∈ s, ∀ x : ℝ, ‖F.g i x‖≤ C/(1+|x-c i|)^6 := by
  intro i hi x
  simpa [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using F.decay i hi (x:ℂ)

theorem SparsePacketFamily.signed_estimates
    {Γ : Finset ℝ} {s : Finset ℤ} {c : ℤ → ℝ} {B ρ σ M C D : ℝ}
    (F : SparsePacketFamily Γ s c B ρ σ M C) (hs : s.Nonempty)
    (hC : 0≤ C) (hD : 0< D) (hgap : 2*ρ≤ D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)|≤|c j-c i|)
    (hbudget : (4*C/D^2)*squareTailMass≤1)
    (ψ : ℤ → ℝ) (hψ : ∀i∈s,|ψ i|=1) :
    (∀ x : ℝ, ‖signedPacketSum s ψ F.g x‖≤ M+1) ∧
    (∀ x ∈ Γ, ‖signedPacketSum s ψ F.g x‖≤2) ∧
    (∀ i ∈ s, B-1≤ψ i*(signedPacketSum s ψ F.g (F.p i)).re) :=
  signedPacketSum_estimates s hs c F.p ψ F.g hC hD hgap hsep hbudget hψ
    F.real F.bound F.real_decay (fun i hi => ⟨F.near i hi,F.peak i hi⟩) Γ F.nodes

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.TrigZeroCount ===== -/
section

/-! Algebraic zero counting and exact node-factor division for finite Fourier bands.
The functions, bands and polynomial realization are the actual circle objects
from the JSP957 library; no zero-count or interpolation assertion is assumed. -/

noncomputable section
open scoped BigOperators ComplexConjugate Real
open Set Finset Polynomial
open OMA.Port1.E1152

namespace OMA.Port1.E1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem character_ne_zero (j : ℤ) (x : FourierCircle) : character j x ≠ 0 := by
  have := character_norm j x
  intro h
  simp [h] at this

/-- A nonzero band-m circle function has at most 2m distinct zeros. -/
theorem band_zero_card_le {m : ℕ} {f : CircleFunction}
    (hf : f ∈ bandSpace m) (hf0 : f ≠ 0)
    (S : Finset FourierCircle) (hS : ∀ x ∈ S, f x = 0) :
    S.card ≤ 2 * m := by
  classical
  obtain ⟨p, hp, hpf⟩ := exists_polynomialCircle hf
  have hp0 : p ≠ 0 := by
    intro h
    apply hf0
    simpa [h] using hpf.symm
  have hroots : (S.image (fun x => character 1 x)).val ⊆ p.roots := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    apply (Polynomial.mem_roots hp0).mpr
    have he := hS x hx
    rw [← hpf, polynomialCircle_apply] at he
    exact (mul_eq_zero.mp he).resolve_left (character_ne_zero _ _)
  have hcard := (Polynomial.card_le_degree_of_subset_roots hroots).trans hp
  simpa only [Finset.card_image_of_injective S character_one_injective] using hcard

/-- The ordinary monic polynomial having precisely the prescribed circle nodes. -/
def circleNodePolynomial (Γ : Finset FourierCircle) : ℂ[X] :=
  ∏ γ ∈ Γ, (Polynomial.X - Polynomial.C (character 1 γ))

/-- The centered Laurent node product; with 2N nodes it belongs to band N.
A constant phase makes this function real-valued. -/
def circleNodeProduct (N : ℕ) (Γ : Finset FourierCircle) : CircleFunction :=
  polynomialCircle N (circleNodePolynomial Γ)

theorem circleNodeProduct_apply (N : ℕ) (Γ : Finset FourierCircle)
    (x : FourierCircle) :
    circleNodeProduct N Γ x =
      character (-(N : ℤ)) x * ∏ γ ∈ Γ, (character 1 x - character 1 γ) := by
  simp [circleNodeProduct, circleNodePolynomial, polynomialCircle_apply,
    Polynomial.eval_prod]

theorem circleNodePolynomial_monic (Γ : Finset FourierCircle) :
    (circleNodePolynomial Γ).Monic := by
  exact Polynomial.monic_prod_X_sub_C _ _

theorem circleNodePolynomial_natDegree (Γ : Finset FourierCircle) :
    (circleNodePolynomial Γ).natDegree = Γ.card := by
  simp [circleNodePolynomial, Polynomial.natDegree_prod_of_monic,
    Polynomial.monic_X_sub_C]

theorem circleNodeProduct_eq_zero_iff (N : ℕ) (Γ : Finset FourierCircle)
    (x : FourierCircle) : circleNodeProduct N Γ x = 0 ↔ x ∈ Γ := by
  classical
  rw [circleNodeProduct_apply, mul_eq_zero]
  simp only [character_ne_zero, false_or, Finset.prod_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨γ, hγ, he⟩
    exact character_one_injective he ▸ hγ
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem circleNodePolynomial_dvd {m : ℕ} {f : CircleFunction}
    (p : ℂ[X]) (hpf : polynomialCircle m p = f)
    (Γ : Finset FourierCircle) (hfΓ : ∀ x ∈ Γ, f x = 0) :
    circleNodePolynomial Γ ∣ p := by
  classical
  unfold circleNodePolynomial
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact Polynomial.pairwise_coprime_X_sub_C character_one_injective hab
  · intro x hx
    apply Polynomial.dvd_iff_isRoot.mpr
    have he := hfΓ x hx
    rw [← hpf, polynomialCircle_apply] at he
    exact (mul_eq_zero.mp he).resolve_left (character_ne_zero _ _)

/-- Vanishing at 2N distinct circle nodes removes exactly N from each end of
the Fourier band. This is the algebraic sine-product division used in the
finite trigonometric interpolation obstruction. -/
theorem exists_band_node_quotient {m N : ℕ} (hNm : N ≤ m)
    {f : CircleFunction} (hf : f ∈ bandSpace m)
    (Γ : Finset FourierCircle) (hΓ : Γ.card = 2 * N)
    (hfΓ : ∀ x ∈ Γ, f x = 0) :
    ∃ g : CircleFunction, g ∈ bandSpace (m - N) ∧
      f = circleNodeProduct N Γ * g := by
  classical
  by_cases hf0 : f = 0
  · exact ⟨0, (bandSpace (m - N)).zero_mem, by simp [hf0]⟩
  obtain ⟨p, hp, hpf⟩ := exists_polynomialCircle hf
  obtain ⟨q, hpq⟩ := circleNodePolynomial_dvd p hpf Γ hfΓ
  have hp0 : p ≠ 0 := by
    intro h
    apply hf0
    simpa [h] using hpf.symm
  have hq0 : q ≠ 0 := by
    intro h
    apply hp0
    simp [hpq, h]
  have hD0 := (circleNodePolynomial_monic Γ).ne_zero
  have hqd : q.natDegree ≤ 2 * (m - N) := by
    rw [hpq, Polynomial.natDegree_mul hD0 hq0,
      circleNodePolynomial_natDegree, hΓ] at hp
    omega
  refine ⟨polynomialCircle (m - N) q, polynomialCircle_band _ _ hqd, ?_⟩
  rw [← hpf, hpq]
  ext x
  simp only [circleNodeProduct, polynomialCircle_apply, ContinuousMap.mul_apply,
    Polynomial.eval_mul]
  rw [show character (-(N : ℤ)) x *
      (circleNodePolynomial Γ).eval (character 1 x) *
      (character (-((m - N : ℕ) : ℤ)) x * q.eval (character 1 x)) =
      (character (-(N : ℤ)) x * character (-((m - N : ℕ) : ℤ)) x) *
      ((circleNodePolynomial Γ).eval (character 1 x) * q.eval (character 1 x)) by ring,
    ← character_add]
  rw [show -(N : ℤ) + -((m - N : ℕ) : ℤ) = -(m : ℤ) by omega]

/-- Once the node product is rotated to the real axis, taking the real part
of its exact quotient preserves the factorization and the smaller band. -/
theorem exists_real_band_node_quotient {m N : ℕ} (hNm : N ≤ m)
    {f : CircleFunction} (hf : f ∈ bandSpace m)
    (hreal : ∀ x, (f x).im = 0)
    (Γ : Finset FourierCircle) (hΓ : Γ.card = 2 * N)
    (hfΓ : ∀ x ∈ Γ, f x = 0) (c : ℂ) (hc : c ≠ 0)
    (hphase : ∀ x, (c * circleNodeProduct N Γ x).im = 0) :
    ∃ g : CircleFunction, g ∈ bandSpace (m - N) ∧
      (∀ x, (g x).im = 0) ∧ f = (c • circleNodeProduct N Γ) * g := by
  obtain ⟨g₀, hg₀, he₀⟩ := exists_band_node_quotient hNm hf Γ hΓ hfΓ
  let g : CircleFunction := c⁻¹ • g₀
  have he : f = (c • circleNodeProduct N Γ) * g := by
    rw [he₀]
    ext x
    simp only [g, ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
    field_simp
  have hoff : ∀ x ∉ Γ, (g x).im = 0 := by
    intro x hx
    have hP : c * circleNodeProduct N Γ x ≠ 0 :=
      mul_ne_zero hc (mt (circleNodeProduct_eq_zero_iff N Γ x).mp hx)
    have hPre : (c * circleNodeProduct N Γ x).re ≠ 0 := by
      intro hr
      apply hP
      exact Complex.ext hr (hphase x)
    have him := hreal x
    rw [he] at him
    change ((c * circleNodeProduct N Γ x) * g x).im = 0 at him
    rw [Complex.mul_im, hphase x, zero_mul, add_zero] at him
    exact (mul_eq_zero.mp him).resolve_left hPre
  refine ⟨realPartCircle g, realPart_band ((bandSpace (m - N)).smul_mem _ hg₀),
    by intro x; rfl, ?_⟩
  ext x
  by_cases hx : x ∈ Γ
  · simp only [hfΓ x hx, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
      smul_eq_mul, (circleNodeProduct_eq_zero_iff N Γ x).mpr hx, mul_zero, zero_mul]
  · have hgx : realPartCircle g x = g x := by
      apply Complex.ext
      · rfl
      · exact (hoff x hx).symm
    rw [he]
    simp only [ContinuousMap.mul_apply, hgx]

private theorem exists_zero_between_opposite (u : ℝ → ℝ) (hu : Continuous u)
    {a b : ℝ} (hab : a < b) (hsign : u a * u b < 0) :
    ∃ x ∈ Set.Ioo a b, u x = 0 := by
  rcases mul_neg_iff.mp hsign with h | h
  · exact intermediate_value_Ioo' hab.le hu.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le hu.continuousOn ⟨h.1, h.2⟩

/-- Consecutive strict sign changes of a real band-m function, in an arc of
length less than one period, number at most 2m. -/
theorem band_alternating_card_le {m k : ℕ} {f : CircleFunction}
    (hf : f ∈ bandSpace m) (hreal : ∀ x, (f x).im = 0)
    (t : Fin (k + 1) → ℝ) (ht : StrictMono t)
    (hspan : t (Fin.last k) - t 0 < 2 * Real.pi)
    (hsign : ∀ i : Fin k,
      (f (t i.castSucc : FourierCircle)).re * (f (t i.succ : FourierCircle)).re < 0) :
    k ≤ 2 * m := by
  classical
  by_cases hk : k = 0
  · omega
  have hu : Continuous (fun x : ℝ => (f (x : FourierCircle)).re) := by fun_prop
  have hz : ∀ i : Fin k, ∃ x ∈ Set.Ioo (t i.castSucc) (t i.succ),
      (f (x : FourierCircle)).re = 0 := by
    intro i
    exact exists_zero_between_opposite _ hu (ht (by simp)) (hsign i)
  choose z hzi hz0 using hz
  have hzmono : StrictMono z := by
    intro i j hij
    have htij : t i.succ ≤ t j.castSucc := ht.monotone (by simpa using hij)
    exact (hzi i).2.trans_le (htij.trans (hzi j).1.le)
  have hzarc (i : Fin k) : z i ∈ Set.Ico (t 0) (t 0 + 2 * Real.pi) := by
    constructor
    · exact (ht.monotone (Fin.zero_le _)).trans (hzi i).1.le
    · have hlast : t i.succ ≤ t (Fin.last k) := ht.monotone (Fin.le_last _)
      linarith [(hzi i).2]
  have hzinj : Function.Injective (fun i => (z i : FourierCircle)) := by
    intro i j he
    apply hzmono.injective
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (hzarc i) (hzarc j)).mp he
  have hf0 : f ≠ 0 := by
    intro he
    have h := hsign ⟨0, Nat.pos_of_ne_zero hk⟩
    simp [he] at h
  let S : Finset FourierCircle := Finset.univ.image (fun i => (z i : FourierCircle))
  have hS : ∀ x ∈ S, f x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply Complex.ext <;> simp [hz0 i, hreal]
  have hbound := band_zero_card_le hf hf0 S hS
  simpa [S, Finset.card_image_of_injective _ hzinj] using hbound

private theorem sub_mul_neg_of_abs_lt {a b : ℝ} (hab : |a| < |b|) :
    (a - b) * b < 0 := by
  by_cases hb : 0 ≤ b
  · rw [abs_of_nonneg hb] at hab
    have hbpos := (abs_nonneg a).trans_lt hab
    exact mul_neg_of_neg_of_pos (sub_neg.mpr ((le_abs_self a).trans_lt hab)) hbpos
  · have hbneg : b < 0 := lt_of_not_ge hb
    rw [abs_of_neg hbneg] at hab
    have ha : b < a := by linarith [neg_abs_le a]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ha) hbneg

private theorem opposite_quotient_sign {a b p : ℝ} (hp : p ≠ 0)
    (hab : |a| < |b|) : ((a - b) / p) * (b / p) < 0 := by
  rw [div_mul_div_comm]
  exact div_neg_of_neg_of_pos (sub_mul_neg_of_abs_lt hab) (mul_self_pos.mpr hp)

private theorem opposite_preserves_alternation {u v a b : ℝ}
    (hua : u * a < 0) (hvb : v * b < 0) (hab : a * b < 0) : u * v < 0 := by
  rcases mul_neg_iff.mp hua with h | h <;>
    rcases mul_neg_iff.mp hvb with h' | h' <;>
    rcases mul_neg_iff.mp hab with h'' | h'' <;>
    nlinarith

/-- The precise finite oscillation obstruction. Values of phi divided by the
real node product alternate at k+1 peaks. An interpolant uniformly smaller at
those peaks therefore needs at least k/2 extra Fourier degrees. -/
theorem interpolant_peak_oscillations_le {m N k : ℕ} (hNm : N ≤ m)
    (Γ : Finset FourierCircle) (hΓ : Γ.card = 2 * N)
    (φ H : CircleFunction) (hφ : φ ∈ bandSpace N) (hH : H ∈ bandSpace m)
    (hφreal : ∀ x, (φ x).im = 0) (hHreal : ∀ x, (H x).im = 0)
    (hsame : ∀ x ∈ Γ, H x = φ x)
    (c : ℂ) (hc : c ≠ 0)
    (hphase : ∀ x, (c * circleNodeProduct N Γ x).im = 0)
    (t : Fin (k + 1) → ℝ) (ht : StrictMono t)
    (hspan : t (Fin.last k) - t 0 < 2 * Real.pi)
    (htΓ : ∀ i, (t i : FourierCircle) ∉ Γ)
    (hsmall : ∀ i, |(H (t i : FourierCircle)).re| < |(φ (t i : FourierCircle)).re|)
    (hsign : ∀ i : Fin k,
      ((φ (t i.castSucc : FourierCircle)).re /
        (c * circleNodeProduct N Γ (t i.castSucc : FourierCircle)).re) *
      ((φ (t i.succ : FourierCircle)).re /
        (c * circleNodeProduct N Γ (t i.succ : FourierCircle)).re) < 0) :
    k ≤ 2 * (m - N) := by
  have hφm : φ ∈ bandSpace m := by
    apply spectrum_mono (s := Set.Icc (-(N : ℤ)) N)
      (t := Set.Icc (-(m : ℤ)) m) ?_ hφ
    intro j hj
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  obtain ⟨g, hg, hgreal, hfactor⟩ := exists_real_band_node_quotient hNm
    ((bandSpace m).sub_mem hH hφm)
    (by intro x; simp [hHreal, hφreal]) Γ hΓ
    (by intro x hx; simp [hsame x hx]) c hc hphase
  have hPre (i : Fin (k + 1)) :
      (c * circleNodeProduct N Γ (t i : FourierCircle)).re ≠ 0 := by
    intro he
    have hz : c * circleNodeProduct N Γ (t i : FourierCircle) = 0 :=
      Complex.ext he (hphase _)
    exact (mul_ne_zero hc (mt (circleNodeProduct_eq_zero_iff N Γ _).mp (htΓ i))) hz
  have hgvalue (i : Fin (k + 1)) :
      (g (t i : FourierCircle)).re =
        ((H (t i : FourierCircle)).re - (φ (t i : FourierCircle)).re) /
        (c * circleNodeProduct N Γ (t i : FourierCircle)).re := by
    have h := congrArg (fun F : CircleFunction => (F (t i : FourierCircle)).re) hfactor
    change (H (t i : FourierCircle) - φ (t i : FourierCircle)).re =
      ((c * circleNodeProduct N Γ (t i : FourierCircle)) * g (t i : FourierCircle)).re at h
    rw [Complex.sub_re, Complex.mul_re, hphase, zero_mul, sub_zero] at h
    apply (eq_div_iff (hPre i)).mpr
    nlinarith [h]
  apply band_alternating_card_le hg hgreal t ht hspan
  intro i
  rw [hgvalue i.castSucc, hgvalue i.succ]
  exact opposite_preserves_alternation
    (opposite_quotient_sign (hPre i.castSucc) (hsmall i.castSucc))
    (opposite_quotient_sign (hPre i.succ) (hsmall i.succ)) (hsign i)

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.Phase ===== -/
section

/-! A constant phase makes the centered circle-node product real-valued. -/

noncomputable section
open scoped BigOperators ComplexConjugate Real
open Set Finset
open OMA.Port1.E1152

namespace OMA.Port1.E1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem conj_character (j : ℤ) (x : FourierCircle) :
    conj (character j x) = character (-j) x := by
  exact fourier_neg.symm

theorem character_neg_one_pow (k : ℕ) (x : FourierCircle) :
    character (-1) x ^ k = character (-(k : ℤ)) x := by
  rw [← conj_character, ← map_pow, character_one_pow, conj_character]

theorem conj_character_sub (x y : FourierCircle) :
    conj (character 1 x - character 1 y) =
      (-1 : ℂ) * character (-1) x * character (-1) y *
        (character 1 x - character 1 y) := by
  have hx : character (-1) x * character 1 x = 1 := by
    rw [← character_add]; norm_num [character_zero]
  have hy : character (-1) y * character 1 y = 1 := by
    rw [← character_add]; norm_num [character_zero]
  rw [map_sub, conj_character, conj_character]
  calc
    character (-1) x - character (-1) y =
      character (-1) x * (character (-1) y * character 1 y) -
        character (-1) y * (character (-1) x * character 1 x) := by rw [hx, hy]; ring
    _ = _ := by ring

theorem circleNodeProduct_conj (N : ℕ) (Γ : Finset FourierCircle)
    (hΓ : Γ.card = 2 * N) (x : FourierCircle) :
    conj (circleNodeProduct N Γ x) =
      (∏ γ ∈ Γ, character (-1) γ) * circleNodeProduct N Γ x := by
  classical
  have hp : (∏ γ ∈ Γ, conj (character 1 x - character 1 γ)) =
      ((-1 : ℂ) * character (-1) x) ^ Γ.card *
        (∏ γ ∈ Γ, character (-1) γ) *
        ∏ γ ∈ Γ, (character 1 x - character 1 γ) := by
    simp_rw [conj_character_sub]
    simp only [Finset.prod_mul_distrib, Finset.prod_const]
    ring
  rw [circleNodeProduct_apply, map_mul, map_prod, conj_character, neg_neg, hp,
    hΓ, mul_pow, character_neg_one_pow]
  have he : (-1 : ℂ) ^ (2 * N) = 1 := by simp [pow_mul]
  rw [he, one_mul]
  calc
    _ = (character (N : ℤ) x * character (-((2 * N : ℕ) : ℤ)) x) *
        (∏ γ ∈ Γ, character (-1) γ) *
        ∏ γ ∈ Γ, (character 1 x - character 1 γ) := by ring
    _ = _ := by
      rw [← character_add,
        show (N : ℤ) + -((2 * N : ℕ) : ℤ) = -(N : ℤ) by omega]
      ring

/-- Any function satisfying a fixed unit conjugation relation admits a nonzero
constant phase making all its values real. No angle representatives are needed. -/
theorem exists_real_phase_of_conj {α : Type*} (F : α → ℂ) (A : ℂ)
    (hA : conj A * A = 1) (hF : ∀ x, conj (F x) = A * F x) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x, (c * F x).im = 0 := by
  by_cases hneg : A = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    intro x
    apply Complex.conj_eq_iff_im.mp
    rw [map_mul, Complex.conj_I, hF, hneg]
    ring
  · refine ⟨1 + A, ?_, ?_⟩
    · intro hz
      apply hneg
      have := congrArg (fun z : ℂ => z - 1) hz
      simpa using this
    · intro x
      apply Complex.conj_eq_iff_im.mp
      rw [map_mul, map_add, map_one, hF]
      calc
        (1 + conj A) * (A * F x) = (A + conj A * A) * F x := by ring
        _ = (1 + A) * F x := by rw [hA]; ring

/-- The actual centered node product with an even number of nodes is real after
one constant nonzero phase correction. -/
theorem circleNodeProduct_exists_real_phase (N : ℕ) (Γ : Finset FourierCircle)
    (hΓ : Γ.card = 2 * N) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x : FourierCircle,
      (c * circleNodeProduct N Γ x).im = 0 := by
  apply exists_real_phase_of_conj (circleNodeProduct N Γ)
    (∏ γ ∈ Γ, character (-1) γ)
  · rw [map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro γ hγ
    rw [conj_character, ← character_add]
    norm_num [character_zero]
  · exact circleNodeProduct_conj N Γ hΓ

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.PeakSigns ===== -/
section

noncomputable section
open Set Finset

namespace OMA.Port1.E1133

def peakDirection (v : ℝ) : ℝ := if 0 < v then 1 else -1

theorem abs_peakDirection (v : ℝ) : |peakDirection v| = 1 := by
  unfold peakDirection
  split_ifs <;> norm_num

theorem peakDirection_mul (v : ℝ) : peakDirection v * v = |v| := by
  unfold peakDirection
  split_ifs with h
  · simp [abs_of_pos h]
  · simp [abs_of_nonpos (le_of_not_gt h)]

theorem alternating_direction_positive {v u : ℝ} (hv : v ≠ 0) (j : ℕ)
    (hu : 0 < ((-1 : ℝ)^j * peakDirection v) * u) :
    0 < (-1 : ℝ)^j * (u/v) := by
  have hpos : 0 < |v| := abs_pos.mpr hv
  have heq : ((-1 : ℝ)^j * (u/v)) * |v| =
      ((-1 : ℝ)^j * peakDirection v) * u := by
    rw [← peakDirection_mul v]
    field_simp
  exact (mul_pos_iff_of_pos_right hpos).mp (heq.symm ▸ hu)

theorem alternating_products_negative {u v : ℝ} (j : ℕ)
    (hu : 0 < (-1 : ℝ)^j*u) (hv : 0 < (-1 : ℝ)^(j+1)*v) : u*v < 0 := by
  rw [pow_succ] at hv
  rcases neg_one_pow_eq_or (R := ℝ) j with hj | hj
  · rw [hj] at hu hv
    nlinarith
  · rw [hj] at hu hv
    nlinarith

/-- Choose all packet signs before constructing their superposition. Any
result with those strict peak signs has alternating quotients by the fixed,
nonzero node-product values. -/
theorem choose_alternating_peak_signs (s : Finset ℤ) {k : ℕ}
    (hs : s.card = k+1) (v : ℤ → ℝ) (hv : ∀ j ∈ s, v j ≠ 0) :
    ∃ ψ : ℤ → ℝ, (∀ j, |ψ j| = 1) ∧
      ∀ u : ℤ → ℝ, (∀ j ∈ s, 0 < ψ j*u j) →
        ∀ i : Fin k,
          (u (s.orderEmbOfFin hs i.castSucc) / v (s.orderEmbOfFin hs i.castSucc)) *
          (u (s.orderEmbOfFin hs i.succ) / v (s.orderEmbOfFin hs i.succ)) < 0 := by
  classical
  let e := s.orderIsoOfFin hs
  let ψ : ℤ → ℝ := fun j => if hj : j ∈ s then
    (-1 : ℝ)^((e.symm ⟨j,hj⟩).val) * peakDirection (v j) else 1
  have hψ : ∀ j, |ψ j| = 1 := by
    intro j
    dsimp [ψ]
    split_ifs <;> simp [abs_mul,abs_pow,abs_peakDirection]
  have heval (i : Fin (k+1)) :
      ψ (s.orderEmbOfFin hs i) = (-1 : ℝ)^i.val * peakDirection (v (s.orderEmbOfFin hs i)) := by
    simp [ψ,← Finset.coe_orderIsoOfFin_apply,e]
  refine ⟨ψ,hψ,?_⟩
  intro u hu i
  have hleft := hu _ (s.orderEmbOfFin_mem hs i.castSucc)
  have hright := hu _ (s.orderEmbOfFin_mem hs i.succ)
  rw [heval] at hleft hright
  exact alternating_products_negative i.val
    (alternating_direction_positive (hv _ (s.orderEmbOfFin_mem hs i.castSucc)) _ hleft)
    (alternating_direction_positive (hv _ (s.orderEmbOfFin_mem hs i.succ)) _ hright)

theorem peak_not_mem_nodes (Γ : Finset ℝ) (g : ℂ → ℂ) (p : ℝ)
    (hnodes : ∀ x ∈ Γ, ‖g x‖ ≤ 1) (hpeak : 1 < (g p).re) : p ∉ Γ := by
  intro hp
  have h := (Complex.re_le_norm (g p)).trans (hnodes p hp)
  linarith

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.TrigMultipeak ===== -/
section

noncomputable section
open scoped BigOperators Real
open Finset Set OMA.Port1.E1152

namespace OMA.Port1.E1133
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Convert actual freely signed peaks into bad data for every degree below
the oscillation threshold. The chosen data are independent of that degree. -/
theorem finite_trig_obstruction_of_peaks (N : ℕ) (Γ : Finset FourierCircle)
    (hΓ : Γ.card=2*N) (s : Finset ℤ) (hs : s.Nonempty) (t : ℤ → ℝ)
    (ht : ∀ i ∈ s, ∀ j ∈ s, i< j → t i< t j)
    (htbounds : ∀i∈s,t i∈Ioo (-Real.pi) Real.pi)
    (htΓ : ∀i∈s,(t i:FourierCircle)∉Γ)
    (A : ℝ) (hA : 0< A)
    (hpeaks : ∀ψ:ℤ→ℝ,(∀i,|ψ i|=1)→∃φ:CircleFunction,
      φ∈bandSpace N ∧ (∀x,(φ x).im=0) ∧ (∀x∈Γ,‖φ x‖≤1) ∧
      ∀i∈s,A<ψ i*(φ (t i:FourierCircle)).re) :
    ∃y:FourierCircle→ℝ,(∀x∈Γ,|y x|≤1) ∧
      ∀ m : ℕ, N ≤ m → 2 * (m - N) < s.card - 1 → ∀ H : CircleFunction,
        H ∈ bandSpace m → (∀ x, (H x).im = 0) → ‖H‖ ≤ A →
        ∃x∈Γ,(H x).re≠y x := by
  classical
  obtain ⟨phase,hphase0,hphase⟩ := circleNodeProduct_exists_real_phase N Γ hΓ
  let v : ℤ→ℝ := fun i => (phase*circleNodeProduct N Γ (t i:FourierCircle)).re
  have hv : ∀i∈s,v i≠0 := by
    intro i hi hzero
    have he : phase*circleNodeProduct N Γ (t i:FourierCircle)=0 :=
      Complex.ext hzero (hphase _)
    have hp0 : circleNodeProduct N Γ (t i:FourierCircle)≠0 := by
      intro hz
      exact htΓ i hi ((circleNodeProduct_eq_zero_iff N Γ _).mp hz)
    exact mul_ne_zero hphase0 hp0 he
  let k := s.card-1
  have hscard : s.card=k+1 := by
    have := Finset.card_pos.mpr hs
    dsimp [k]
    omega
  obtain ⟨ψ,hψ,halt⟩ := choose_alternating_peak_signs s hscard v hv
  obtain ⟨φ,hφ,hφr,hφnodes,hφpeak⟩ := hpeaks ψ hψ
  refine ⟨fun x => (φ x).re,fun x hx => (Complex.abs_re_le_norm _).trans (hφnodes x hx),?_⟩
  intro m hNm hm H hH hHr hHnorm
  by_contra hnone
  push Not at hnone
  have hsame : ∀x∈Γ,H x=φ x := by
    intro x hx
    exact Complex.ext (hnone x hx) (by rw [hHr,hφr])
  let q : Fin (k+1)→ℝ := fun i => t (s.orderEmbOfFin hscard i)
  have hq : StrictMono q := by
    intro i j hij
    exact ht _ (s.orderEmbOfFin_mem hscard i) _ (s.orderEmbOfFin_mem hscard j)
      ((s.orderEmbOfFin hscard).strictMono hij)
  have hqspan : q (Fin.last k)-q 0<2*Real.pi := by
    have hl := htbounds _ (s.orderEmbOfFin_mem hscard (Fin.last k))
    have hr := htbounds _ (s.orderEmbOfFin_mem hscard 0)
    dsimp [q]
    linarith [hl.2,hr.1]
  have hsmall : ∀ i : Fin (k+1), |(H (q i:FourierCircle)).re| < |(φ (q i:FourierCircle)).re| := by
    intro i
    have hp := hφpeak _ (s.orderEmbOfFin_mem hscard i)
    have hψp : ψ (s.orderEmbOfFin hscard i)*(φ (q i:FourierCircle)).re ≤
        |(φ (q i:FourierCircle)).re| := by
      calc
        _ ≤ |ψ (s.orderEmbOfFin hscard i)*(φ (q i:FourierCircle)).re| := le_abs_self _
        _ = _ := by rw [abs_mul,hψ,one_mul]
    exact (Complex.abs_re_le_norm _).trans
      ((ContinuousMap.norm_coe_le_norm H (q i:FourierCircle)).trans hHnorm) |>.trans_lt
        (hp.trans_le hψp)
  have hsign := halt (fun i => (φ (t i:FourierCircle)).re)
    (fun i hi => hA.trans (hφpeak i hi))
  have hbound := interpolant_peak_oscillations_le hNm Γ hΓ φ H hφ hH hφr hHr hsame
    phase hphase0 hphase q hq hqspan
    (fun i => htΓ _ (s.orderEmbOfFin_mem hscard i)) hsmall hsign
  exact (not_lt_of_ge hbound) hm

end OMA.Port1.E1133




end
end

/- ===== OMA.Port1.E1133.Periodization ===== -/
section

noncomputable section

open Filter Topology Set MeasureTheory
open scoped BigOperators

namespace OMA.Port1.E1133

def sixthLatticeWeight (k : ℤ) : ℝ := 1 / (1 + |(k : ℝ)|) ^ 6

theorem sixthLatticeWeight_nonneg (k : ℤ) : 0 ≤ sixthLatticeWeight k := by
  unfold sixthLatticeWeight
  positivity

theorem sixthLatticeWeight_summable : Summable sixthLatticeWeight := by
  have hnat : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 6 := by
    simpa using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (6 : ℕ)))
  apply Summable.of_nat_of_neg
  · simpa [sixthLatticeWeight, abs_of_nonneg, add_comm] using hnat
  · simpa [sixthLatticeWeight, abs_of_nonneg, add_comm] using hnat

/-- The parameter `T` is the actual period; the application takes `T=2N`. -/
def periodize (g : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℤ, g (z + ((T * (k : ℝ) : ℝ) : ℂ))

/-- A summable majorant on any bounded complex disk. -/
theorem periodize_term_local_bound (g : ℂ → ℂ) {C σ T R : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T) (hR : 0 ≤ R)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) (hz : ‖z‖ ≤ R) (k : ℤ) :
    ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ ≤
      (C * Real.exp (σ * R) * ((T + R + 1) / T) ^ 6) * sixthLatticeWeight k := by
  let u := z + ((T * (k : ℝ) : ℝ) : ℂ)
  have him : |u.im| ≤ R := by
    simpa [u] using (Complex.abs_im_le_norm z).trans hz
  have htri : T * |(k : ℝ)| ≤ ‖u‖ + R := by
    have ht := norm_sub_le u z
    have heq : u - z = ((T * (k : ℝ) : ℝ) : ℂ) := by dsimp [u]; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hT] at ht
    linarith
  have hden : T * (1 + |(k : ℝ)|) ≤ (T + R + 1) * (1 + ‖u‖) := by
    nlinarith [norm_nonneg u, mul_nonneg (add_nonneg hT.le hR) (norm_nonneg u)]
  have hr : (1 + |(k : ℝ)|) / (1 + ‖u‖) ≤ (T + R + 1) / T := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + ‖u‖) hT).2
    nlinarith
  have hr6 := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |(k : ℝ)|) / (1 + ‖u‖)) hr 6
  have hexp : Real.exp (σ * |u.im|) ≤ Real.exp (σ * R) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left him hσ
  calc
    ‖g u‖ ≤ C * Real.exp (σ * |u.im|) / (1 + ‖u‖) ^ 6 := hg u
    _ ≤ C * Real.exp (σ * R) / (1 + ‖u‖) ^ 6 := by gcongr
    _ = (C * Real.exp (σ * R) *
        ((1 + |(k : ℝ)|) / (1 + ‖u‖)) ^ 6) * sixthLatticeWeight k := by
      unfold sixthLatticeWeight
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr6 (by positivity)) (sixthLatticeWeight_nonneg k)

theorem periodize_summable (g : ℂ → ℂ) {C σ T : ℝ}
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) : Summable fun k : ℤ => g (z + ((T * (k : ℝ) : ℝ) : ℂ)) := by
  apply Summable.of_norm_bounded
    (sixthLatticeWeight_summable.mul_left
      (C * Real.exp (σ * ‖z‖) * ((T + ‖z‖ + 1) / T) ^ 6))
  exact fun k => periodize_term_local_bound g hC hσ hT (norm_nonneg z) hg z le_rfl k

theorem differentiable_periodize (g : ℂ → ℂ) {C σ T : ℝ}
    (hd : Differentiable ℂ g) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6) :
    Differentiable ℂ (periodize g T) := by
  intro z
  let R := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs := sixthLatticeWeight_summable.mul_left
    (C * Real.exp (σ * R) * ((T + R + 1) / T) ^ 6)
  have hdiff : DifferentiableOn ℂ (periodize g T) (Metric.ball 0 R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hs
    · intro k
      exact (hd.comp (differentiable_id.add_const _)).differentiableOn
    · exact Metric.isOpen_ball
    · intro k w hw
      apply periodize_term_local_bound g hC hσ hT hR hg w
      exact le_of_lt (by simpa [Metric.mem_ball] using hw)
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by
    simp [Metric.mem_ball, R]))

theorem periodize_periodic (g : ℂ → ℂ) (T : ℝ) :
    Function.Periodic (periodize g T) (T : ℂ) := by
  intro z
  unfold periodize
  have he := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun k : ℤ => g (z + ((T * (k : ℝ) : ℝ) : ℂ)))
  convert he using 1
  congr 1
  funext k
  congr 1
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  push_cast
  ring

theorem periodize_real (g : ℂ → ℂ) {C σ T : ℝ}
    (hreal : ∀ x : ℝ, (g x).im = 0) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (x : ℝ) : (periodize g T x).im = 0 := by
  have hs := periodize_summable g hC hσ hT hg (x : ℂ)
  change Complex.imCLM (∑' k : ℤ, g ((x : ℂ) + ((T * (k : ℝ) : ℝ) : ℂ))) = 0
  rw [Complex.imCLM.map_tsum hs]
  have he : ∀ k : ℤ, Complex.imCLM (g ((x : ℂ) + ((T * (k : ℝ) : ℝ) : ℂ))) = 0 := by
    intro k
    change (g ((x : ℂ) + ((T * (k : ℝ) : ℝ) : ℂ))).im = 0
    rw [← Complex.ofReal_add]
    exact hreal _
  simp_rw [he]
  simp

/-- A bound uniform in the height of a vertical strip, preserving the exact
exponential type. -/
theorem periodize_term_strip_bound (g : ℂ → ℂ) {C σ T R : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T) (hR : 0 ≤ R)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) (hz : |z.re| ≤ R) (k : ℤ) :
    ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ ≤
      (C * Real.exp (σ * |z.im|) * ((T + R + 1) / T) ^ 6) * sixthLatticeWeight k := by
  let u := z + ((T * (k : ℝ) : ℝ) : ℂ)
  have him : u.im = z.im := by simp [u]
  have htri : T * |(k : ℝ)| ≤ ‖u‖ + R := by
    have ht : |u.re - z.re| ≤ |u.re| + |z.re| := by
      simpa using abs_sub_le u.re 0 z.re
    have heq : u.re - z.re = T * (k : ℝ) := by simp [u]
    rw [heq, abs_mul, abs_of_pos hT] at ht
    linarith [Complex.abs_re_le_norm u]
  have hden : T * (1 + |(k : ℝ)|) ≤ (T + R + 1) * (1 + ‖u‖) := by
    nlinarith [norm_nonneg u, mul_nonneg (add_nonneg hT.le hR) (norm_nonneg u)]
  have hr : (1 + |(k : ℝ)|) / (1 + ‖u‖) ≤ (T + R + 1) / T := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + ‖u‖) hT).2
    nlinarith
  have hr6 := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |(k : ℝ)|) / (1 + ‖u‖)) hr 6
  calc
    ‖g u‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖u‖) ^ 6 := by simpa [him] using hg u
    _ = (C * Real.exp (σ * |z.im|) *
        ((1 + |(k : ℝ)|) / (1 + ‖u‖)) ^ 6) * sixthLatticeWeight k := by
      unfold sixthLatticeWeight
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr6 (by positivity)) (sixthLatticeWeight_nonneg k)

theorem periodize_strip_bound (g : ℂ → ℂ) {C σ T R : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T) (hR : 0 ≤ R)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6)
    (z : ℂ) (hz : |z.re| ≤ R) :
    ‖periodize g T z‖ ≤
      (C * ((T + R + 1) / T) ^ 6 * ∑' k : ℤ, sixthLatticeWeight k) * Real.exp (σ * |z.im|) := by
  let A := C * Real.exp (σ * |z.im|) * ((T + R + 1) / T) ^ 6
  have hmaj := sixthLatticeWeight_summable.mul_left A
  have hn : Summable fun k : ℤ => ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (periodize_term_strip_bound g hC hT hR hg z hz) hmaj
  calc
    ‖periodize g T z‖ ≤ ∑' k : ℤ, ‖g (z + ((T * (k : ℝ) : ℝ) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℤ, A * sixthLatticeWeight k :=
      Summable.tsum_le_tsum (periodize_term_strip_bound g hC hT hR hg z hz) hn hmaj
    _ = _ := by rw [tsum_mul_left]; dsimp [A]; ring

/-- Vertical contour translation for an entire periodic function: the two
vertical sides cancel exactly. -/
theorem periodic_horizontal_integral (H : ℂ → ℂ) {T : ℝ}
    (hd : Differentiable ℂ H) (hp : Function.Periodic H (T : ℂ)) (y : ℝ) :
    (∫ x : ℝ in (-T / 2)..(T / 2), H (x : ℂ)) =
      ∫ x : ℝ in (-T / 2)..(T / 2), H ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have hv : ∀ t : ℝ, H (((T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      H (((-T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    have heq : (((T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (((-T / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + (T : ℂ) := by push_cast; ring
    rw [heq, hp]
  have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H
    (((-T / 2 : ℝ) : ℂ)) (((T / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) hd.differentiableOn
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_mul, sub_zero, add_zero, zero_add, Complex.ofReal_zero] at hr
  simp_rw [hv] at hr
  have hr' : (∫ x : ℝ in (-T / 2)..(T / 2), H (x : ℂ)) -
      (∫ x : ℝ in (-T / 2)..(T / 2), H ((x : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    simpa only [add_sub_cancel_right] using hr
  exact sub_eq_zero.mp hr'

def frequencyTwist (H : ℂ → ℂ) (T : ℝ) (j : ℤ) (z : ℂ) : ℂ :=
  H z * Complex.exp (-(2 * Real.pi * (j : ℝ) / T : ℝ) * Complex.I * z)

theorem differentiable_frequencyTwist (H : ℂ → ℂ) (T : ℝ) (j : ℤ)
    (hd : Differentiable ℂ H) : Differentiable ℂ (frequencyTwist H T j) := by
  exact hd.mul (Complex.differentiable_exp.comp (differentiable_id.const_mul _))

theorem frequencyTwist_periodic (H : ℂ → ℂ) {T : ℝ} (hT : T ≠ 0)
    (hp : Function.Periodic H (T : ℂ)) (j : ℤ) :
    Function.Periodic (frequencyTwist H T j) (T : ℂ) := by
  intro z
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  unfold frequencyTwist
  rw [hp]
  have heq : (-(2 * Real.pi * (j : ℝ) / T : ℝ) : ℂ) * Complex.I * (z + (T : ℂ)) =
      (-(2 * Real.pi * (j : ℝ) / T : ℝ) : ℂ) * Complex.I * z +
        ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp [hTc]
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_frequencyTwist (H : ℂ → ℂ) (T : ℝ) (j : ℤ) (z : ℂ) :
    ‖frequencyTwist H T j z‖ =
      ‖H z‖ * Real.exp ((2 * Real.pi * (j : ℝ) / T) * z.im) := by
  rw [frequencyTwist, norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

/-- Entire periodic functions of exponential type have no Fourier modes above
that type. This is proved by an actual Cauchy contour translation. -/
theorem frequency_integral_eq_zero (H : ℂ → ℂ) {T K σ : ℝ}
    (hT : 0 < T) (_hK : 0 ≤ K) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ))
    (hbound : ∀ z : ℂ, |z.re| ≤ T / 2 → ‖H z‖ ≤ K * Real.exp (σ * |z.im|))
    (j : ℤ) (hfreq : σ < |2 * Real.pi * (j : ℝ) / T|) :
    (∫ x : ℝ in (-T / 2)..(T / 2), frequencyTwist H T j (x : ℂ)) = 0 := by
  let ω : ℝ := 2 * Real.pi * (j : ℝ) / T
  have ht : Tendsto (fun t : ℝ => K * T * Real.exp ((σ - |ω|) * t)) atTop (𝓝 0) := by
    have hneg : σ - |ω| < 0 := by dsimp [ω]; linarith
    simpa using (Real.tendsto_exp_atBot.comp
      ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop_of_neg hneg)).const_mul (K * T)
  have hdecay : ∀ t : ℝ, 0 ≤ t →
      ‖∫ x : ℝ in (-T / 2)..(T / 2), frequencyTwist H T j (x : ℂ)‖ ≤
        K * T * Real.exp ((σ - |ω|) * t) := by
    intro t ht0
    let y : ℝ := if 0 ≤ ω then -t else t
    have hy : |y| = t := by
      dsimp [y]
      split_ifs <;> simp [abs_of_nonneg ht0]
    have hωy : ω * y = -|ω| * t := by
      dsimp [y]
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h), neg_neg]
    rw [periodic_horizontal_integral (frequencyTwist H T j)
      (differentiable_frequencyTwist H T j hd) (frequencyTwist_periodic H hT.ne' hp j) y]
    have hib := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T / 2) (b := T / 2) (C := K * Real.exp ((σ - |ω|) * t))
      (f := fun x : ℝ => frequencyTwist H T j ((x : ℂ) + (y : ℂ) * Complex.I)) (by
        intro x hx
        have hx' : |x| ≤ T / 2 := by
          rw [uIoc_of_le (by linarith : -T / 2 ≤ T / 2)] at hx
          exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
        have hh := hbound ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hx')
        rw [norm_frequencyTwist]
        have him : (((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by simp
        rw [him] at hh ⊢
        calc
          ‖H ((x : ℂ) + (y : ℂ) * Complex.I)‖ * Real.exp (ω * y) ≤
              (K * Real.exp (σ * |y|)) * Real.exp (ω * y) :=
            mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
          _ = K * Real.exp ((σ - |ω|) * t) := by
            rw [mul_assoc, ← Real.exp_add, hy, hωy]
            congr 2
            ring)
    have hab : |T / 2 - (-T / 2)| = T := by rw [abs_of_nonneg (by linarith)]; ring
    rw [hab] at hib
    nlinarith
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact ge_of_tendsto ht (eventually_ge_atTop 0 |>.mono fun t ht => hdecay t ht)

def entirePeriodicCircle (H : ℂ → ℂ) (T : ℝ) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ)) : C(AddCircle T, ℂ) := by
  let hpR : Function.Periodic (fun x : ℝ => H (x : ℂ)) T := by
    intro x
    simpa only [Complex.ofReal_add] using hp (x : ℂ)
  exact ⟨hpR.lift, continuous_coinduced_dom.mpr (hd.continuous.comp Complex.continuous_ofReal)⟩

theorem entirePeriodicCircle_apply (H : ℂ → ℂ) (T : ℝ)
    (hd : Differentiable ℂ H) (hp : Function.Periodic H (T : ℂ)) (x : ℝ) :
    entirePeriodicCircle H T hd hp (x : AddCircle T) = H (x : ℂ) := by
  rfl

theorem entirePeriodicCircle_coeff_eq_integral (H : ℂ → ℂ) (T : ℝ)
    [Fact (0 < T)] (hd : Differentiable ℂ H) (hp : Function.Periodic H (T : ℂ)) (j : ℤ) :
    fourierCoeff (entirePeriodicCircle H T hd hp) j =
      (1 / T : ℝ) • ∫ x : ℝ in (-T / 2)..(T / 2), frequencyTwist H T j (x : ℂ) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-T / 2), show -T / 2 + T = T / 2 by ring]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [fourier_coe_apply, entirePeriodicCircle_apply, smul_eq_mul]
  unfold frequencyTwist
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

theorem entirePeriodicCircle_coeff_zero (H : ℂ → ℂ) {T K σ : ℝ}
    [hT : Fact (0 < T)] (hK : 0 ≤ K) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ))
    (hbound : ∀ z : ℂ, |z.re| ≤ T / 2 → ‖H z‖ ≤ K * Real.exp (σ * |z.im|))
    (j : ℤ) (hfreq : σ < |2 * Real.pi * (j : ℝ) / T|) :
    fourierCoeff (entirePeriodicCircle H T hd hp) j = 0 := by
  rw [entirePeriodicCircle_coeff_eq_integral,
    frequency_integral_eq_zero H hT.out hK hd hp hbound j hfreq, smul_zero]

def periodizationBandwidth (σ T : ℝ) : ℕ := Nat.ceil (σ * T / (2 * Real.pi))

theorem periodizationBandwidth_le {σ T : ℝ} {n : ℕ}
    (h : σ * T / (2 * Real.pi) ≤ (n : ℝ)) :
    periodizationBandwidth σ T ≤ n := by
  exact Nat.ceil_le.mpr h

theorem frequency_above_band {σ T : ℝ} (hT : 0 < T) (j : ℤ)
    (hj : j ∉ Finset.Icc (-(periodizationBandwidth σ T : ℤ)) (periodizationBandwidth σ T : ℤ)) :
    σ < |2 * Real.pi * (j : ℝ) / T| := by
  have hn : ¬ |j| ≤ (periodizationBandwidth σ T : ℤ) := by
    intro h
    exact hj (Finset.mem_Icc.mpr (abs_le.mp h))
  have hjr : (periodizationBandwidth σ T : ℝ) < |(j : ℝ)| := by
    exact_mod_cast lt_of_not_ge hn
  have hceil : σ * T / (2 * Real.pi) ≤ (periodizationBandwidth σ T : ℝ) := Nat.le_ceil _
  have hratio := hceil.trans_lt hjr
  have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hratio
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos, abs_of_pos hT]
  exact (lt_div_iff₀ hT).mpr (by nlinarith)

/-- An actual finite Fourier expansion, rather than a bandwidth assumption. -/
theorem entire_periodic_finite_expansion (H : ℂ → ℂ) {T K σ : ℝ}
    [hT : Fact (0 < T)] (hK : 0 ≤ K) (hd : Differentiable ℂ H)
    (hp : Function.Periodic H (T : ℂ))
    (hbound : ∀ z : ℂ, |z.re| ≤ T / 2 → ‖H z‖ ≤ K * Real.exp (σ * |z.im|)) :
    ∃ c : ℤ → ℂ, ∀ x : ℝ,
      H (x : ℂ) = ∑ j ∈ Finset.Icc (-(periodizationBandwidth σ T : ℤ))
        (periodizationBandwidth σ T : ℤ),
          c j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (x : ℂ) / (T : ℂ)) := by
  classical
  let F := entirePeriodicCircle H T hd hp
  let s := Finset.Icc (-(periodizationBandwidth σ T : ℤ)) (periodizationBandwidth σ T : ℤ)
  have hz : ∀ j ∉ s, fourierCoeff F j = 0 := by
    intro j hj
    exact entirePeriodicCircle_coeff_zero H hK hd hp hbound j (frequency_above_band hT.out j hj)
  have hs : Summable (fourierCoeff F) := summable_of_ne_finset_zero hz
  refine ⟨fourierCoeff F, ?_⟩
  intro x
  have heq := (has_pointwise_sum_fourier_series_of_summable hs (x : AddCircle T)).tsum_eq
  rw [tsum_eq_sum (s := s) (by
    intro j hj
    rw [hz j hj, zero_smul])] at heq
  simpa [F, s, smul_eq_mul, fourier_coe_apply, entirePeriodicCircle_apply] using heq.symm

theorem periodize_finite_expansion (g : ℂ → ℂ) {C σ T : ℝ}
    [hT : Fact (0 < T)] (hd : Differentiable ℂ g) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C * Real.exp (σ * |z.im|) / (1 + ‖z‖) ^ 6) :
    ∃ c : ℤ → ℂ, ∀ x : ℝ,
      periodize g T (x : ℂ) = ∑ j ∈ Finset.Icc (-(periodizationBandwidth σ T : ℤ))
        (periodizationBandwidth σ T : ℤ),
          c j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (x : ℂ) / (T : ℂ)) := by
  apply entire_periodic_finite_expansion (periodize g T)
    (K := C * ((T + T / 2 + 1) / T) ^ 6 * ∑' k : ℤ, sixthLatticeWeight k)
  · exact mul_nonneg (by positivity) (tsum_nonneg sixthLatticeWeight_nonneg)
  · exact differentiable_periodize g hd hC hσ hT.out hg
  · exact periodize_periodic g T
  · exact fun z hz => periodize_strip_bound g hC hT.out (by linarith [hT.out]) hg z hz

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.MultipeakPeriodTail ===== -/
section

noncomputable section
open scoped BigOperators
open Finset Set

namespace OMA.Port1.E1133

private theorem sixth_tail_product_bound {C D a b d : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : D * (a+b) ≤ d) :
    C / (1+d)^6 ≤ (C / D^2) * (1/a^2) * (1/b^2) := by
  have hDp : 0 < D := by linarith
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hDa : D*a ≤ d := by nlinarith
  have hDb : b ≤ d := by nlinarith
  have hdp : 0 ≤ d := hbp.le.trans hDb
  have hsq1 := pow_le_pow_left₀ (by positivity : 0 ≤ D*a) hDa 2
  have hsq2 := pow_le_pow_left₀ hbp.le hDb 2
  have hden : D^2*a^2*b^2 ≤ (1+d)^6 := by
    calc
      D^2*a^2*b^2 = (D*a)^2*b^2 := by ring
      _ ≤ d^2*d^2 := mul_le_mul hsq1 hsq2 (by positivity) (by positivity)
      _ = d^4 := by ring
      _ ≤ (1+d)^4 := pow_le_pow_left₀ hdp (by linarith) 4
      _ ≤ (1+d)^6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  calc
    C / (1+d)^6 ≤ C/(D^2*a^2*b^2) :=
      div_le_div_of_nonneg_left hC (by positivity) hden
    _ = (C / D^2) * (1/a^2) * (1/b^2) := by field_simp

/-- Every positive period translate is far from the rightmost packet, with
an additional distance proportional to the index gap. -/
private theorem packet_positive_shift_distance (s : Finset ℤ) (hs : s.Nonempty)
    (c : ℤ → ℝ) {N D x : ℝ} (hD : 0 < D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hx : |x| ≤ N) (k : ℤ) (hk : 0 < k) (j : ℤ) (hj : j ∈ s) :
    D*((k:ℝ)+((s.max' hs-j+1:ℤ):ℝ)) ≤ |x+2*N*k-c j| := by
  let m := s.max' hs
  have hm : m ∈ s := s.max'_mem hs
  have hjm : j ≤ m := s.le_max' j hj
  have hN : 2*D ≤ N := by
    have hb := hbound m hm
    rcases hb with ⟨h1,h2⟩
    linarith
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hor := horder j hj m hm hjm
  have hb := (hbound m hm).2
  have hxr := (abs_le.mp hx).1
  have hgap : 0 ≤ ((m-j:ℤ):ℝ) := by exact_mod_cast sub_nonneg.mpr hjm
  have hdist : D*((k:ℝ)+((m-j+1:ℤ):ℝ)) ≤ x+2*N*k-c j := by
    push_cast at hor hgap ⊢
    nlinarith [mul_nonneg (show 0 ≤ 2*N-D by linarith) (show 0 ≤ (k:ℝ)-1 by linarith)]
  exact hdist.trans (le_abs_self _)

private theorem packet_negative_shift_distance (s : Finset ℤ) (hs : s.Nonempty)
    (c : ℤ → ℝ) {N D x : ℝ} (hD : 0 < D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hx : |x| ≤ N) (k : ℤ) (hk : k < 0) (j : ℤ) (hj : j ∈ s) :
    D*((-(k:ℝ))+((j-s.min' hs+1:ℤ):ℝ)) ≤ |x+2*N*k-c j| := by
  let m := s.min' hs
  have hm : m ∈ s := s.min'_mem hs
  have hmj : m ≤ j := s.min'_le j hj
  have hN : 2*D ≤ N := by
    have hb := hbound m hm
    rcases hb with ⟨h1,h2⟩
    linarith
  have hk1 : (1:ℝ) ≤ -(k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ -k by omega)
  have hor := horder m hm j hj hmj
  have hb := (hbound m hm).1
  have hxr := (abs_le.mp hx).2
  have hgap : 0 ≤ ((j-m:ℤ):ℝ) := by exact_mod_cast sub_nonneg.mpr hmj
  have hdist : D*((-(k:ℝ))+((j-m+1:ℤ):ℝ)) ≤ -(x+2*N*k-c j) := by
    push_cast at hor hgap ⊢
    nlinarith [mul_nonneg (show 0 ≤ 2*N-D by linarith) (show 0 ≤ -(k:ℝ)-1 by linarith)]
  exact hdist.trans (neg_le_abs _)

/-- A bound for each nonzero period translate of all packets, independent
of both the number of packets and the period length. -/
theorem multipeak_shift_norm_bound (s : Finset ℤ) (c : ℤ → ℝ)
    (g : ℤ → ℂ → ℂ) {C D N : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hdecay : ∀ j ∈ s, ∀ t : ℝ, ‖g j t‖ ≤ C/(1+|t-c j|)^6)
    (x : ℝ) (hx : |x| ≤ N) (k : ℤ) (hk : k ≠ 0) :
    ∑ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖ ≤
      ((C/D^2)*squareTailMass)*(1/(k:ℝ)^2) := by
  classical
  by_cases hs : s.Nonempty
  · have hDp : 0 < D := by linarith
    rcases lt_or_gt_of_ne hk with hkneg | hkpos
    · let m := s.min' hs
      have hpoint : ∀ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖ ≤
          ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m-1):ℤ):ℝ)^2)) := by
        intro j hj
        have hb : (1:ℝ) ≤ ((j-s.min' hs+1:ℤ):ℝ) := by
          exact_mod_cast (show (1:ℤ) ≤ j-s.min' hs+1 by have := s.min'_le j hj; omega)
        have hp := sixth_tail_product_bound hC hD
          (show (1:ℝ) ≤ -(k:ℝ) by exact_mod_cast (show (1:ℤ) ≤ -k by omega)) hb
          (packet_negative_shift_distance s hs c hDp hbound horder hx k hkneg j hj)
        have he : ((j-s.min' hs+1:ℤ):ℝ) = ((j-(m-1):ℤ):ℝ) := by dsimp [m]; push_cast; ring
        rw [he, neg_sq] at hp
        exact (hdecay j hj _).trans hp
      calc
        _ ≤ ∑ j ∈ s, ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m-1):ℤ):ℝ)^2)) := sum_le_sum hpoint
        _ = ((C/D^2)*(1/(k:ℝ)^2))*(∑ j ∈ s, 1/(((j-(m-1):ℤ):ℝ)^2)) := by rw [mul_sum]
        _ ≤ ((C/D^2)*(1/(k:ℝ)^2))*squareTailMass :=
          mul_le_mul_of_nonneg_left (shifted_square_sum_le s (m-1)) (by positivity)
        _ = _ := by ring
    · let m := s.max' hs
      have hpoint : ∀ j ∈ s, ‖g j ((x+2*N*k:ℝ):ℂ)‖ ≤
          ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m+1):ℤ):ℝ)^2)) := by
        intro j hj
        have hb : (1:ℝ) ≤ ((s.max' hs-j+1:ℤ):ℝ) := by
          exact_mod_cast (show (1:ℤ) ≤ s.max' hs-j+1 by have := s.le_max' j hj; omega)
        have hp := sixth_tail_product_bound hC hD
          (show (1:ℝ) ≤ k by exact_mod_cast hkpos) hb
          (packet_positive_shift_distance s hs c hDp hbound horder hx k hkpos j hj)
        have he : ((s.max' hs-j+1:ℤ):ℝ) = -((j-(m+1):ℤ):ℝ) := by dsimp [m]; push_cast; ring
        rw [he, neg_sq] at hp
        exact (hdecay j hj _).trans hp
      calc
        _ ≤ ∑ j ∈ s, ((C/D^2)*(1/(k:ℝ)^2))*(1/(((j-(m+1):ℤ):ℝ)^2)) := sum_le_sum hpoint
        _ = ((C/D^2)*(1/(k:ℝ)^2))*(∑ j ∈ s, 1/(((j-(m+1):ℤ):ℝ)^2)) := by rw [mul_sum]
        _ ≤ ((C/D^2)*(1/(k:ℝ)^2))*squareTailMass :=
          mul_le_mul_of_nonneg_left (shifted_square_sum_le s (m+1)) (by positivity)
        _ = _ := by ring
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    simp only [he, sum_empty]
    exact mul_nonneg (mul_nonneg (by positivity) squareTailMass_nonneg) (by positivity)

/-- The signed sum incurs only a uniformly small real error when periodized.
Only the centered real-axis decay enters this bound. -/
theorem multipeak_periodize_error (s : Finset ℤ) (c ψ : ℤ → ℝ)
    (g : ℤ → ℂ → ℂ) {C D N : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-N+2*D) (N-2*D))
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hψ : ∀ j ∈ s, |ψ j|=1)
    (hdecay : ∀ j ∈ s, ∀ t : ℝ, ‖g j t‖ ≤ C/(1+|t-c j|)^6)
    (x : ℝ) (hx : |x| ≤ N) :
    ‖periodize (signedPacketSum s ψ g) (2*N) x - signedPacketSum s ψ g x‖ ≤
      (C/D^2)*squareTailMass^2 := by
  let G := signedPacketSum s ψ g
  let r : ℤ → ℂ := fun k => if k=0 then 0 else G ((x+2*N*k:ℝ):ℂ)
  let A := (C/D^2)*squareTailMass
  have hA : 0 ≤ A := mul_nonneg (by positivity) squareTailMass_nonneg
  have hnorm (t : ℝ) : ‖G (t:ℂ)‖ ≤ ∑ j ∈ s, ‖g j t‖ := by
    calc
      _ ≤ ∑ j ∈ s, ‖(ψ j:ℂ)*g j t‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hψ j hj, one_mul]
  have hp : ∀ k : ℤ, ‖r k‖ ≤ A*(1/(k:ℝ)^2) := by
    intro k
    by_cases hk : k=0
    · simp [r, hk]
    · simpa [r, hk, A] using (hnorm (x+2*N*k)).trans
        (multipeak_shift_norm_bound s c g hC hD hbound horder hdecay x hx k hk)
  have hmaj := summable_squareTail.mul_left A
  have hn : Summable fun k : ℤ => ‖r k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hp hmaj
  have hs0 : Summable fun k : ℤ => if k=0 then G (x:ℂ) else 0 := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  have hs : Summable fun k : ℤ => G ((x+2*N*k:ℝ):ℂ) := by
    convert hs0.add hn.of_norm using 1
    funext k
    by_cases hk : k=0 <;> simp [r, hk]
  have hsum : periodize G (2*N) x - G x = ∑' k : ℤ, r k := by
    have heq := hs.tsum_eq_add_tsum_ite 0
    simp only [Int.cast_zero, mul_zero, add_zero] at heq
    have hre : (fun k : ℤ => G ((x+2*N*k:ℝ):ℂ)) =
        (fun k : ℤ => G ((x:ℂ)+(((2*N)*k:ℝ):ℂ))) := by
      funext k
      rw [Complex.ofReal_add]
    change (∑' k : ℤ, G ((x:ℂ)+(((2*N)*k:ℝ):ℂ))) - G x = _
    rw [← hre]
    exact sub_eq_iff_eq_add.mpr (by simpa [r, add_comm] using heq)
  change ‖periodize G (2*N) x-G x‖ ≤ _
  rw [hsum]
  calc
    ‖∑' k : ℤ, r k‖ ≤ ∑' k : ℤ, ‖r k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℤ, A*(1/(k:ℝ)^2) := hn.tsum_le_tsum hp hmaj
    _ = A*squareTailMass := by rw [tsum_mul_left]; rfl
    _ = _ := by dsimp [A]; ring

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.PeriodizationCircle ===== -/
section

noncomputable section
open scoped BigOperators
open OMA.Port1.E1152

namespace OMA.Port1.E1133

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem exists_circle_of_finite_expansion (F : ℂ → ℂ) (T : ℝ) (m : ℕ)
    (c : ℤ → ℂ)
    (he : ∀ x : ℝ, F x=∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ),
      c j*Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(x:ℂ)/(T:ℂ))) :
    ∃ P : CircleFunction, P ∈ bandSpace m ∧
      ∀ x : ℝ, P ((2*Real.pi*x/T : ℝ) : FourierCircle)=F x := by
  refine ⟨finiteFourier (Finset.Icc (-(m:ℤ)) (m:ℤ)) c, ?_, ?_⟩
  · unfold finiteFourier
    apply Submodule.sum_mem
    intro j hj
    exact (bandSpace m).smul_mem (c j) (character_mem_spectrum (Finset.mem_Icc.mp hj))
  · intro x
    rw [finiteFourier_apply, he x]
    apply Finset.sum_congr rfl
    intro j _
    rw [character_coe]
    congr 2
    push_cast
    ring

theorem periodize_circle_of_bandwidth_le (g : ℂ → ℂ) {C σ T : ℝ} {m : ℕ}
    (hd : Differentiable ℂ g) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hT : 0 < T)
    (hg : ∀ z : ℂ, ‖g z‖ ≤ C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (hm : periodizationBandwidth σ T ≤ m) :
    ∃ P : CircleFunction, P ∈ bandSpace m ∧
      ∀ x : ℝ, P ((2*Real.pi*x/T : ℝ) : FourierCircle)=periodize g T x := by
  let : Fact (0 < T) := ⟨hT⟩
  obtain ⟨c,hc⟩ := periodize_finite_expansion g (T := T) hd hC hσ hg
  obtain ⟨P,hP,hPe⟩ := exists_circle_of_finite_expansion (periodize g T) T
    (periodizationBandwidth σ T) c hc
  refine ⟨P, ?_, hPe⟩
  apply spectrum_mono (t := Set.Icc (-(m:ℤ)) m) _ hP
  intro j hj
  simp only [Set.mem_Icc] at *
  constructor <;> omega

/-- Every circle argument has a representative in the normalized physical scale. -/
theorem normalized_circle_surjective {T : ℝ} (hT : T ≠ 0) :
    Function.Surjective (fun x : ℝ => ((2*Real.pi*x/T : ℝ) : FourierCircle)) := by
  intro u
  let t := AddCircle.equivIco (2*Real.pi) (-Real.pi) u
  refine ⟨(t:ℝ)*T/(2*Real.pi), ?_⟩
  dsimp only
  have he : 2*Real.pi*((t:ℝ)*T/(2*Real.pi))/T=(t:ℝ) := by field_simp
  rw [he]
  exact (AddCircle.equivIco (2*Real.pi) (-Real.pi)).symm_apply_apply u

theorem circle_norm_le_of_physical {P : CircleFunction} {T B : ℝ} (hT : T ≠ 0)
    (hB : 0 ≤ B)
    (hb : ∀ x : ℝ, ‖P ((2*Real.pi*x/T : ℝ) : FourierCircle)‖ ≤ B) : ‖P‖ ≤ B := by
  apply (ContinuousMap.norm_le P hB).mpr
  intro u
  obtain ⟨x,rfl⟩ := normalized_circle_surjective hT u
  exact hb x

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.NodeNormalization ===== -/
section

noncomputable section
open Set Finset
open OMA.Port1.E1152

namespace OMA.Port1.E1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Physical points in one period of length `2 * r` viewed on the Fourier circle. -/
def normalizeNode (r x : ℝ) : FourierCircle := ((Real.pi * x / r : ℝ) : FourierCircle)

theorem normalizeNode_angle_mem {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ico (-r) r) :
    Real.pi * x / r ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
  constructor
  · apply (le_div_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le]
  · apply (div_lt_iff₀ hr).mpr
    nlinarith [mul_lt_mul_of_pos_left hx.2 Real.pi_pos]

theorem normalizeNode_injOn {r : ℝ} (hr : 0 < r) :
    Set.InjOn (normalizeNode r) (Ico (-r) r) := by
  intro x hx y hy hxy
  have heq : Real.pi * x / r = Real.pi * y / r :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (normalizeNode_angle_mem hr hx) (normalizeNode_angle_mem hr hy)).mp hxy
  have hm : Real.pi * x = Real.pi * y := (div_left_inj' hr.ne').mp heq
  nlinarith [Real.pi_pos]

def normalizedNodes (r : ℝ) (Γ : Finset ℝ) : Finset FourierCircle :=
  Γ.image (normalizeNode r)

theorem normalizedNodes_card {r : ℝ} (hr : 0 < r) (Γ : Finset ℝ)
    (hΓ : ∀ x ∈ Γ, x ∈ Ico (-r) r) : (normalizedNodes r Γ).card = Γ.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  exact normalizeNode_injOn hr (hΓ x hx) (hΓ y hy) hxy

theorem mem_normalizedNodes_iff {r : ℝ} {Γ : Finset ℝ} {z : FourierCircle} :
    z ∈ normalizedNodes r Γ ↔ ∃ x ∈ Γ, normalizeNode r x = z := by
  exact Finset.mem_image

theorem normalizeNode_mem_normalizedNodes_iff {r : ℝ} (hr : 0 < r)
    (Γ : Finset ℝ) (hΓ : ∀ x ∈ Γ, x ∈ Ico (-r) r)
    {x : ℝ} (hx : x ∈ Ico (-r) r) :
    normalizeNode r x ∈ normalizedNodes r Γ ↔ x ∈ Γ := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := mem_normalizedNodes_iff.mp h
    have : y = x := normalizeNode_injOn hr (hΓ y hy) hx heq
    simpa [this] using hy
  · intro hxΓ
    exact mem_normalizedNodes_iff.mpr ⟨x, hxΓ, rfl⟩

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.PeriodizedPeaks ===== -/
section

noncomputable section
open scoped BigOperators Real
open Finset Set OMA.Port1.E1152
namespace OMA.Port1.E1133
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A separated family of genuine local packets yields arbitrarily signed
peaks in the original trigonometric band, with unit data at every node. -/
theorem SparsePacketFamily.periodized_peaks
    {Γ : Finset ℝ} {s : Finset ℤ} {c : ℤ → ℝ} {A B ρ σ M C D : ℝ}
    (F : SparsePacketFamily Γ s c B ρ σ M C) (n : ℕ) (hn : 0 < n)
    (hs : s.Nonempty) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hσπ : σ ≤ Real.pi)
    (hD : 1 ≤ D) (hgap : 2*ρ ≤ D)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i|)
    (horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i)
    (hbound : ∀ j ∈ s, c j ∈ Icc (-(n:ℝ)+2*D) ((n:ℝ)-2*D))
    (hnodebound : ∀ x ∈ Γ, |x| ≤ n)
    (hpeakbound : ∀ j ∈ s, |F.p j| ≤ n)
    (hbudget : (4*C/D^2)*squareTailMass ≤ 1)
    (hperiodbudget : (C/D^2)*squareTailMass^2 ≤ 1)
    (hBA : 3*A+2 < B) (ψ : ℤ → ℝ) (hψ : ∀ i, |ψ i|=1) :
    ∃ φ : CircleFunction, φ ∈ bandSpace n ∧ (∀ x, (φ x).im=0) ∧
      (∀ x ∈ normalizedNodes n Γ, ‖φ x‖ ≤ 1) ∧
      ∀ j ∈ s, A < ψ j*(φ (normalizeNode n (F.p j))).re := by
  classical
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hT : 0 < 2*(n:ℝ) := by positivity
  have hD0 : 0 < D := by linarith
  let G := signedPacketSum s ψ F.g
  let C₀ := ∑ i ∈ s, C*(1+|c i|)^6
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun i hi => by positivity)
  have hdec : ∀ z : ℂ, ‖G z‖ ≤ C₀*Real.exp (σ*|z.im|)/(1+‖z‖)^6 :=
    signedPacketSum_decay s c ψ F.g hC (fun i _ => hψ i) F.decay
  have hband : periodizationBandwidth σ (2*(n:ℝ)) ≤ n := by
    apply periodizationBandwidth_le
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hσπ hnr.le]
  obtain ⟨P,hP,hPe⟩ := periodize_circle_of_bandwidth_le G
    (signedPacketSum_entire s ψ F.g F.entire) hC₀ hσ hT hdec hband
  have hPe' (x : ℝ) : P (normalizeNode n x)=periodize G (2*(n:ℝ)) x := by
    have he : 2*Real.pi*x/(2*(n:ℝ))=Real.pi*x/n := by ring
    simpa only [he,normalizeNode] using hPe x
  have hPr : ∀ x, (P x).im=0 := by
    intro x
    obtain ⟨t,rfl⟩ := normalized_circle_surjective hT.ne' x
    rw [hPe]
    exact periodize_real G (signedPacketSum_real s ψ F.g F.real) hC₀ hσ hT hdec t
  have herr (x : ℝ) (hx : |x| ≤ n) : ‖P (normalizeNode n x)-G x‖ ≤ 1 := by
    rw [hPe']
    exact (multipeak_periodize_error s c ψ F.g hC hD hbound horder
      (fun i _ => hψ i) F.real_decay x hx).trans hperiodbudget
  obtain ⟨_,hnodes,hpeaks⟩ := F.signed_estimates hs hC hD0 hgap hsep
    hbudget ψ (fun i _ => hψ i)
  let φ : CircleFunction := (1/3:ℂ) • P
  have hφe (x : FourierCircle) : φ x=(1/3:ℂ)*P x := rfl
  refine ⟨φ,(bandSpace n).smul_mem (1/3:ℂ) hP,?_,?_,?_⟩
  · intro x
    rw [hφe,Complex.mul_im,hPr]
    norm_num
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := mem_normalizedNodes_iff.mp hx
    have hb : ‖P (normalizeNode n t)‖ ≤ 3 := by
      calc
        _ ≤ ‖P (normalizeNode n t)-G t‖+‖G t‖ := by simpa [add_comm] using norm_le_insert' (P (normalizeNode n t)) (G t)
        _ ≤ 1+2 := add_le_add (herr t (hnodebound t ht)) (hnodes t ht)
        _ = 3 := by norm_num
    rw [hφe,norm_mul]
    norm_num
    linarith
  · intro j hj
    have he := herr (F.p j) (hpeakbound j hj)
    have hre : |(P (normalizeNode n (F.p j))).re-(G (F.p j)).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans he
    have hsigned : |ψ j*((P (normalizeNode n (F.p j))).re-(G (F.p j)).re)| ≤ 1 := by
      simpa only [abs_mul,hψ,one_mul] using hre
    have hpk := hpeaks j hj
    have hlower := (abs_le.mp hsigned).1
    rw [hφe,Complex.mul_re]
    norm_num
    nlinarith

end OMA.Port1.E1133

end
end

/- ===== OMA.Port1.E1133.SparseCells ===== -/
section

/-! Sparse, separated packets for arbitrary finite node sets. The unit gap
between adjacent closed core intervals avoids endpoint double counting. -/

noncomputable section
open scoped BigOperators
open Finset Set

namespace OMA.Port1.E1133

/-- Among finitely many residue classes, one retains at least the average
number of indices, with an exact integer inequality. -/
theorem exists_large_residue (s : Finset ℕ) (K : ℕ) (hK : 0 < K) :
    ∃ r < K, s.card ≤ K * (s.filter fun i => i % K = r).card := by
  classical
  obtain ⟨r, hr, hmax⟩ := (Finset.range K).exists_max_image
    (fun r => (s.filter fun i => i % K = r).card) (by simpa using Nat.ne_of_gt hK)
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  have hsum := Finset.sum_le_sum (fun j hj => hmax j hj)
  have hpart : s.card = ∑ j ∈ Finset.range K, (s.filter fun i => i % K = j).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i hK))
  rw [hpart]
  simpa using hsum

theorem cell_cores_disjoint (Γ : Finset ℝ) (ρ : ℕ) (a : ℝ) :
    Pairwise (fun i j : ℕ => Disjoint
      (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*i)| ≤ ρ)
      (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*j)| ≤ ρ)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := abs_le.mp (Finset.mem_filter.mp hxi).2
  have hj := abs_le.mp (Finset.mem_filter.mp hxj).2
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    push_cast at hi hj
    nlinarith
  · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    push_cast at hi hj
    nlinarith

/-- A genuine counting bound: all closed cores are disjoint, so every dense
core consumes at least `2ρ+2` distinct nodes. -/
theorem sparse_cells_count (Γ : Finset ℝ) (ρ m : ℕ) (a : ℝ) :
    let good := (Finset.range m).filter fun (i : ℕ) =>
      (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*(i : ℝ))| ≤ ρ).card ≤ 2*ρ+1
    (2*ρ+2) * m ≤ Γ.card + (2*ρ+2) * good.card := by
  classical
  let cell : ℕ → Finset ℝ := fun i =>
    Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*i)| ≤ ρ
  let good := (Finset.range m).filter fun i => (cell i).card ≤ 2*ρ+1
  let bad := (Finset.range m) \ good
  change (2*ρ+2) * m ≤ Γ.card + (2*ρ+2) * good.card
  have hd : (↑bad : Set ℕ).PairwiseDisjoint cell := fun i _ j _ hij =>
    cell_cores_disjoint Γ ρ a hij
  have hsubset : bad.biUnion cell ⊆ Γ := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxi).1
  have hcard : ∑ i ∈ bad, (cell i).card ≤ Γ.card := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsubset
  have hbad : (2*ρ+2)*bad.card ≤ Γ.card := by
    have hsum := Finset.sum_le_sum (s := bad) (fun i hi =>
      show 2*ρ+2 ≤ (cell i).card from by
        have hin := Finset.mem_sdiff.mp hi
        have hn : ¬ (cell i).card ≤ 2*ρ+1 := by
          intro hh
          exact hin.2 (Finset.mem_filter.mpr ⟨hin.1, hh⟩)
        omega)
    have hh : (2*ρ+2)*bad.card ≤ ∑ i ∈ bad, (cell i).card := by
      simpa [mul_comm] using hsum
    exact hh.trans hcard
  have hpartition : bad.card + good.card = m := by
    dsimp [bad]
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range]
    have hle : good.card ≤ m := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range m)
    change m - good.card + good.card = m
    exact Nat.sub_add_cancel hle
  nlinarith

/-- Reindexing a large residue class by its quotient makes the spacing scale
appear directly in the integer indices used by the packet tail estimates. -/
theorem packed_sparse_cells (Γ : Finset ℝ) (ρ m K : ℕ) (hK : 0 < K) (a : ℝ) :
    ∃ r < K, ∃ s : Finset ℤ,
      (∀ j ∈ s, ∃ i < m, j = (i / K : ℕ) ∧ i % K = r) ∧
      (2*ρ+2)*m ≤ Γ.card + (2*ρ+2)*K*s.card ∧
      ∀ j ∈ s, (Γ.filter fun x =>
        |x - (a + (2*ρ+1 : ℕ)*((K : ℝ)*j+r))| ≤ ρ).card ≤ 2*ρ+1 := by
  classical
  let good := (Finset.range m).filter fun (i : ℕ) =>
    (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*(i : ℝ))| ≤ ρ).card ≤ 2*ρ+1
  obtain ⟨r, hr, hlarge⟩ := exists_large_residue good K hK
  let chosen := good.filter fun i => i % K = r
  let s : Finset ℤ := chosen.image fun i => (i / K : ℕ)
  have hmod (i : ℕ) (hi : i ∈ chosen) : i % K = r := (Finset.mem_filter.mp hi).2
  have hdiv (i : ℕ) (hi : i ∈ chosen) : K * (i / K) + r = i := by
    have hh := Nat.mod_add_div i K
    rw [hmod i hi] at hh
    omega
  have hs : s.card = chosen.card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj he
    change (i / K : ℤ) = (j / K : ℤ) at he
    have he' : i / K = j / K := by exact_mod_cast he
    have hi' := hdiv i hi
    have hj' := hdiv j hj
    rw [he'] at hi'
    omega
  refine ⟨r, hr, s, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1,
      rfl, hmod i hi⟩
  · have hc := sparse_cells_count Γ ρ m a
    change (2*ρ+2)*m ≤ Γ.card + (2*ρ+2)*good.card at hc
    change good.card ≤ K * chosen.card at hlarge
    rw [hs]
    nlinarith
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hid : (K : ℝ) * (i / K : ℕ) + r = i := by exact_mod_cast hdiv i hi
    simpa only [Int.cast_natCast, hid] using
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2

/-- Arbitrary node sets of cardinality at most `2N` have a linear number of
sparse cores. Their centers are indexed with the exact spacing needed by the
packet estimates, and stay two spacing lengths away from the period seam. -/
theorem separated_sparse_cells (ρ K : ℕ) (hK : 0 < K) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Γ : Finset ℝ,
      Γ.card ≤ 2*N →
      ∃ s : Finset ℤ, ∃ c : ℤ → ℝ,
        s.Nonempty ∧ η*(N : ℝ) ≤ s.card ∧
        (∀ i j : ℤ, ((2*ρ+1)*K : ℕ) * |((j-i : ℤ) : ℝ)| = |c j-c i|) ∧
        (∀ j ∈ s, -(N : ℝ) + 2*((2*ρ+1)*K : ℕ) ≤ c j ∧
          c j ≤ N - 2*((2*ρ+1)*K : ℕ)) ∧
        (∀ j ∈ s, (Γ.filter fun x => |x-c j| ≤ ρ).card ≤ 2*ρ+1) ∧
        (∀ i j : ℤ, c j-c i = ((2*ρ+1)*K : ℕ)*((j-i : ℤ) : ℝ)) := by
  classical
  let L : ℕ := 2*ρ+1
  let D : ℕ := L*K
  have hL : 0 < L := by dsimp [L]; omega
  have hD : 0 < D := Nat.mul_pos hL hK
  let B : ℕ := 4*(L+1)*D + (L+1)*L
  let N₀ : ℕ := B + 2*D + 1
  refine ⟨1/((L+1)*D : ℕ), by positivity, N₀, ?_⟩
  intro N hN Γ hΓ
  have hB : B ≤ N := by dsimp [N₀] at hN; omega
  have hNpos : 0 < N := by dsimp [N₀] at hN; omega
  have h4D : 4*D ≤ 2*N := by dsimp [N₀] at hN; omega
  let m : ℕ := (2*N-4*D)/L
  let a : ℝ := -(N : ℝ) + 2*D
  obtain ⟨r, hr, s, hw, hc, hsp⟩ := packed_sparse_cells Γ ρ m K hK a
  let c : ℤ → ℝ := fun j => a + L*((K : ℝ)*j+r)
  have hfloor : 2*N ≤ L*m + 4*D + L := by
    have hm : (2*N-4*D)%L + L*m = 2*N-4*D := Nat.mod_add_div _ _
    have hmod := Nat.mod_lt (2*N-4*D) hL
    have hsub := Nat.sub_add_cancel h4D
    omega
  have hlinear : N ≤ (L+1)*D*s.card := by
    change (L+1)*m ≤ Γ.card + (L+1)*K*s.card at hc
    have hh := Nat.mul_le_mul_left L hc
    have hf := Nat.mul_le_mul_left (L+1) hfloor
    have hg := Nat.mul_le_mul_left L hΓ
    dsimp [D, B] at hB hf ⊢
    nlinarith
  have hsn : s.Nonempty := Finset.card_pos.mp (by
    by_contra hn
    have hz : s.card = 0 := by omega
    rw [hz, mul_zero] at hlinear
    omega)
  refine ⟨s, c, hsn, ?_, ?_, ?_, ?_, ?_⟩
  · have hlin : (N : ℝ) ≤ ((L+1)*D : ℕ)*(s.card : ℝ) := by exact_mod_cast hlinear
    have hp : (0 : ℝ) < ((L+1)*D : ℕ) := by positivity
    rw [one_div, mul_comm]
    change (N : ℝ) / ((L+1)*D : ℕ) ≤ s.card
    exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hlin)
  · intro i j
    have he : c j-c i = (D : ℝ)*((j-i : ℤ) : ℝ) := by
      dsimp [c, D]
      push_cast
      ring
    have habs : |(D : ℝ)| = D := abs_of_nonneg (Nat.cast_nonneg D)
    rw [he, abs_mul, habs]
  · intro j hj
    obtain ⟨i, hi, hji, hmod⟩ := hw j hj
    have hind : K*(i/K)+r = i := by
      have hd := Nat.mod_add_div i K
      rw [hmod] at hd
      omega
    have hjcast : (K : ℝ)*(j : ℝ)+r = i := by
      rw [hji]
      exact_mod_cast hind
    have he : c j = a + (L : ℝ)*i := by dsimp [c]; rw [hjcast]
    have him : (L : ℝ)*i ≤ L*m := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi.le) (Nat.cast_nonneg _)
    have hmN : L*m ≤ 2*N-4*D := Nat.mul_div_le _ _
    have hmN' : (L : ℝ)*m ≤ 2*(N : ℝ)-4*D := by
      have hnat : L*m+4*D ≤ 2*N := by omega
      have hnatr : (L : ℝ)*m+4*D ≤ 2*N := by exact_mod_cast hnat
      linarith
    rw [he]
    change -(N : ℝ)+2*D ≤ a+(L : ℝ)*i ∧ a+(L : ℝ)*i ≤ N-2*D
    dsimp [a]
    constructor
    · have hpos : (0 : ℝ) ≤ (L : ℝ)*i := by positivity
      linarith
    · linarith
  · exact hsp
  · intro i j
    dsimp [c, L]
    push_cast
    ring

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.SpacingBudget ===== -/
section

/-! Fixed spacing and strict integer zero-count budgets for the multipeak
construction. The choices depend only on the packet bounds, not on the nodes. -/

noncomputable section

namespace OMA.Port1.E1133

/-- A large integer spacing simultaneously controls within-period packet tails
and tails from the other periods. -/
theorem exists_packet_spacing (C S : ℝ) (hC : 0 < C) (hS : 0 ≤ S) (ρ : ℕ) :
    ∃ K : ℕ, 0 < K ∧
      let D : ℝ := ((2*ρ+1)*K : ℕ)
      1 ≤ D ∧ 2*(ρ : ℝ) < D ∧
        (4*C/D^2)*S ≤ 1 ∧ (C/D^2)*S^2 ≤ 1 := by
  obtain ⟨K, hKg⟩ := exists_nat_gt (1+4*C*S+C*S^2)
  have hCS : 0 ≤ C*S := mul_nonneg hC.le hS
  have hCS2 : 0 ≤ C*S^2 := mul_nonneg hC.le (sq_nonneg S)
  have hK1 : (1 : ℝ) < K := by nlinarith
  have hK : 0 < K := by exact_mod_cast (lt_trans zero_lt_one hK1)
  refine ⟨K, hK, ?_⟩
  let D : ℝ := ((2*ρ+1)*K : ℕ)
  change 1 ≤ D ∧ 2*(ρ : ℝ) < D ∧ (4*C/D^2)*S ≤ 1 ∧ (C/D^2)*S^2 ≤ 1
  have hDeq : D = (2*(ρ : ℝ)+1)*(K : ℝ) := by dsimp [D]; push_cast; rfl
  have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hKD : (K : ℝ) ≤ D := by rw [hDeq]; nlinarith
  have hD1 : 1 ≤ D := hK1.le.trans hKD
  have hρD : 2*(ρ : ℝ) < D := by rw [hDeq]; nlinarith
  have hDsq : D ≤ D^2 := by nlinarith
  have hfirst : 4*C*S ≤ D^2 := by nlinarith
  have hsecond : C*S^2 ≤ D^2 := by nlinarith
  have hpos : 0 < D^2 := by positivity
  refine ⟨hD1, hρD, ?_, ?_⟩
  · rw [div_mul_eq_mul_div]
    exact (div_le_one hpos).mpr hfirst
  · rw [div_mul_eq_mul_div]
    exact (div_le_one hpos).mpr hsecond

/-- A linear number of peaks eventually strictly exceeds twice the excess
Fourier degree plus one. Both subtractions in the conclusion are in `ℕ`. -/
theorem exists_strict_zero_budget (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ c m : ℕ,
      η*(n : ℝ) ≤ c → n ≤ m →
      (m : ℝ) ≤ n+δ*n → 2*(m-n) < c-1 := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (4/η)
  refine ⟨η/8, by positivity, n₀, ?_⟩
  intro n hn c m hpeaks hnm hm
  have hnreal : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hfour : 4 < η*(n : ℝ) := by
    have hlarge : 4/η < (n : ℝ) := hn₀.trans_le hnreal
    have hh := (div_lt_iff₀ hη).mp hlarge
    nlinarith
  have hc : 2 ≤ c := by
    have hh : (4 : ℝ) < c := hfour.trans_le hpeaks
    exact_mod_cast (show (2 : ℝ) ≤ c by linarith)
  have hsub : ((m-n : ℕ) : ℝ) = (m : ℝ)-n := Nat.cast_sub hnm
  have hcsub : ((c-1 : ℕ) : ℝ) = (c : ℝ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ c by omega)]
    norm_num
  have hstrict : 2*((m-n : ℕ) : ℝ) < ((c-1 : ℕ) : ℝ) := by
    rw [hsub, hcsub]
    nlinarith
  exact_mod_cast hstrict

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.FiniteTrigCore ===== -/
section

noncomputable section
open scoped BigOperators Real
open Finset Set OMA.Port1.E1152
namespace OMA.Port1.E1133
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Arbitrary nodes admit bounded real data that cannot be interpolated with
a fixed uniform bound, even after adding a positive proportion of frequencies. -/
theorem finite_trig_obstruction :
    ∀ A > (0:ℝ), ∃ δ > (0:ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ Γ : Finset ℝ, (∀ x ∈ Γ, x ∈ Ico (-(n:ℝ)) n) → Γ.card=2*n →
    ∃ y : ℝ → ℝ, (∀ x ∈ Γ, |y x| ≤ 1) ∧
      ∀ m : ℕ, n ≤ m → (m:ℝ) ≤ n+δ*n →
      ∀ H : CircleFunction, H ∈ bandSpace m → (∀ x, (H x).im=0) → ‖H‖ ≤ A →
      ∃ x ∈ Γ, (H ((Real.pi*x/n:ℝ):FourierCircle)).re ≠ y x := by
  classical
  intro A hA
  let B := 3*A+4
  have hB : 1 < B := by dsimp [B]; linarith
  obtain ⟨ρ,σ,M,C,hρ,hσ,hσπ,hM,hC,hpackets⟩ := sparse_packet_family_exists B hB
  obtain ⟨K,hK,hD,hgap,hbudget,hperiodbudget⟩ :=
    exists_packet_spacing C squareTailMass hC squareTailMass_nonneg ρ
  let D : ℝ := ((2*ρ+1)*K : ℕ)
  change 1 ≤ D at hD
  change 2*(ρ:ℝ) < D at hgap
  change (4*C/D^2)*squareTailMass ≤ 1 at hbudget
  change (C/D^2)*squareTailMass^2 ≤ 1 at hperiodbudget
  have hD0 : 0 < D := by linarith
  obtain ⟨η,hη,N₀,hcells⟩ := separated_sparse_cells ρ K hK
  obtain ⟨δ,hδ,n₀,hcount⟩ := exists_strict_zero_budget η hη
  refine ⟨δ,hδ,max (max N₀ n₀) 1,?_⟩
  intro n hn Γ hΓrange hΓcard
  have hnN : N₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnn : n₀ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnpos : 0 < n := by have := (le_max_right (max N₀ n₀) 1).trans hn; omega
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hnpos
  obtain ⟨s,c,hs,hcard,habs,hinterior,hsparse,horiented⟩ := hcells n hnN Γ hΓcard.le
  obtain ⟨F⟩ := hpackets Γ s c hsparse
  have hsep : ∀ i ∈ s, ∀ j ∈ s, D*|((j-i:ℤ):ℝ)| ≤ |c j-c i| :=
    fun i _ j _ => (habs i j).le
  have horder : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → D*((j-i:ℤ):ℝ) ≤ c j-c i :=
    fun i _ j _ _ => (horiented i j).symm.le
  have hcenters : ∀ i ∈ s, ∀ j ∈ s, i < j → D ≤ c j-c i := by
    intro i hi j hj hij
    have hdij : (1:ℝ) ≤ ((j-i:ℤ):ℝ) := by exact_mod_cast (show (1:ℤ) ≤ j-i by omega)
    have he : c j-c i = D*((j-i:ℤ):ℝ) := horiented i j
    rw [he]
    nlinarith
  have hpbound : ∀ j ∈ s, F.p j ∈ Ioo (-(n:ℝ)) n := by
    intro j hj
    have hc := hinterior j hj
    have hp := abs_le.mp (F.near j hj)
    change -(n:ℝ)+2*D ≤ c j ∧ c j ≤ (n:ℝ)-2*D at hc
    constructor <;> linarith
  have hpmono : ∀ i ∈ s, ∀ j ∈ s, i < j → F.p i < F.p j := by
    intro i hi j hj hij
    have hc := hcenters i hi j hj hij
    have hp := abs_le.mp (F.near i hi)
    have hq := abs_le.mp (F.near j hj)
    linarith
  let t : ℤ → ℝ := fun j => Real.pi*F.p j/n
  have ht : ∀ i ∈ s, ∀ j ∈ s, i < j → t i < t j := by
    intro i hi j hj hij
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (hpmono i hi j hj hij) Real.pi_pos) hnr
  have htb : ∀ j ∈ s, t j ∈ Ioo (-Real.pi) Real.pi := by
    intro j hj
    have hp := hpbound j hj
    constructor
    · apply (lt_div_iff₀ hnr).mpr
      nlinarith [mul_lt_mul_of_pos_left hp.1 Real.pi_pos]
    · apply (div_lt_iff₀ hnr).mpr
      nlinarith [mul_lt_mul_of_pos_left hp.2 Real.pi_pos]
  have hpΓ : ∀ j ∈ s, F.p j ∉ Γ := by
    intro j hj
    exact peak_not_mem_nodes Γ (F.g j) (F.p j) (F.nodes j hj) (hB.trans_le (F.peak j hj))
  have htΓ : ∀ j ∈ s, (t j:FourierCircle) ∉ normalizedNodes n Γ := by
    intro j hj hmem
    have hx := hpbound j hj
    exact hpΓ j hj ((normalizeNode_mem_normalizedNodes_iff hnr Γ hΓrange ⟨hx.1.le,hx.2⟩).mp hmem)
  have hnormcard : (normalizedNodes n Γ).card=2*n :=
    (normalizedNodes_card hnr Γ hΓrange).trans hΓcard
  have hpeaks : ∀ ψ : ℤ → ℝ, (∀ i, |ψ i|=1) →
      ∃ φ : CircleFunction, φ ∈ bandSpace n ∧ (∀ x, (φ x).im=0) ∧
        (∀ x ∈ normalizedNodes n Γ, ‖φ x‖ ≤ 1) ∧
        ∀ j ∈ s, A < ψ j*(φ (t j:FourierCircle)).re := by
    intro ψ hψ
    apply F.periodized_peaks n hnpos hs hC.le hσ.le hσπ.le hD hgap.le hsep horder
      hinterior
    · intro x hx
      exact abs_le.mpr ⟨(hΓrange x hx).1,(hΓrange x hx).2.le⟩
    · intro j hj
      exact abs_le.mpr ⟨(hpbound j hj).1.le,(hpbound j hj).2.le⟩
    · exact hbudget
    · exact hperiodbudget
    · dsimp [B]; linarith
    · exact hψ
  obtain ⟨y,hy,hbad⟩ := finite_trig_obstruction_of_peaks n (normalizedNodes n Γ)
    hnormcard s hs t ht htb htΓ A hA hpeaks
  refine ⟨fun x => y (normalizeNode n x),?_,?_⟩
  · intro x hx
    exact hy _ (mem_normalizedNodes_iff.mpr ⟨x,hx,rfl⟩)
  · intro m hnm hm H hH hHr hHnorm
    obtain ⟨z,hz,hneq⟩ := hbad m hnm (hcount n hnn s.card m hcard hnm hm) H hH hHr hHnorm
    obtain ⟨x,hx,rfl⟩ := mem_normalizedNodes_iff.mp hz
    exact ⟨x,hx,hneq⟩

end OMA.Port1.E1133

end
end

/- ===== OMA.Port1.E1133.Statement ===== -/
section

noncomputable section
open Filter Set
open scoped BigOperators

namespace OMA.Port1.E1133

/-- The complete original question, including repeated indexed nodes. -/
def RobustInterpolation : Prop :=
  ∀ C > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∀ x : Fin n → Icc (-1 : ℝ) 1,
    ∃ y : Fin n → Icc (-1 : ℝ) 1,
    ∀ P : Polynomial ℝ,
      (P.natDegree : ℝ) < (1 + ε) * (n : ℝ) →
      ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) ≥
        (1 - ε) * (n : ℝ) →
      ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C

/-- A bounded polynomial on the actual interval, not on its sample nodes. -/
def BoundedOnSegment (C : ℝ) (P : Polynomial ℝ) : Prop :=
  ∀ z ∈ Icc (-1 : ℝ) 1, |P.eval z| ≤ C

/-- Angular coordinate in the bandwidth-normalized interval `[0,D]`. -/
def angularNode (D : ℝ) (x : Icc (-1 : ℝ) 1) : ℝ :=
  D / Real.pi * Real.arccos (x : ℝ)

theorem angularNode_mem {D : ℝ} (hD : 0 ≤ D) (x : Icc (-1 : ℝ) 1) :
    angularNode D x ∈ Icc 0 D := by
  constructor
  · exact mul_nonneg (div_nonneg hD Real.pi_pos.le) (Real.arccos_nonneg _)
  · calc
      angularNode D x ≤ D / Real.pi * Real.pi :=
        mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) (div_nonneg hD Real.pi_pos.le)
      _ = D := by field_simp

theorem cos_angularNode {D : ℝ} (hD : 0 < D) (x : Icc (-1 : ℝ) 1) :
    Real.cos (Real.pi / D * angularNode D x) = (x : ℝ) := by
  have he : Real.pi / D * angularNode D x = Real.arccos (x : ℝ) := by
    dsimp [angularNode]
    field_simp
  rw [he]
  exact Real.cos_arccos x.property.1 x.property.2

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.PolynomialPullback ===== -/
section

noncomputable section
open scoped BigOperators
open Set Polynomial

namespace OMA.Port1.E1133

/-- Bernstein growth class with an arbitrary finite complex prefactor. -/
def IsBernsteinFunction (σ H : ℝ) (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ (∀ t : ℝ, ‖f t‖ ≤ H) ∧
    ∃ K > (0 : ℝ), ∀ z : ℂ, ‖f z‖ ≤ K * Real.exp (σ * |z.im|)

def polynomialPullback (D : ℝ) (P : ℝ[X]) (z : ℂ) : ℂ :=
  (P.map Complex.ofRealHom).eval (Complex.cos ((Real.pi / D : ℝ) * z))

theorem polynomialPullback_entire (D : ℝ) (P : ℝ[X]) :
    Differentiable ℂ (polynomialPullback D P) := by
  unfold polynomialPullback
  fun_prop

theorem polynomialPullback_real (D : ℝ) (P : ℝ[X]) (t : ℝ) :
    polynomialPullback D P t = ((P.eval (Real.cos (Real.pi / D * t)) : ℝ) : ℂ) := by
  unfold polynomialPullback
  rw [← Complex.ofReal_mul, ← Complex.ofReal_cos]
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply Complex.ofRealHom _

theorem polynomialPullback_at_node {D : ℝ} (hD : 0 < D)
    (P : ℝ[X]) (x : Icc (-1 : ℝ) 1) :
    polynomialPullback D P (angularNode D x) = ((P.eval (x : ℝ) : ℝ) : ℂ) := by
  rw [polynomialPullback_real, cos_angularNode hD]

theorem polynomialPullback_bound_real (D : ℝ) (P : ℝ[X]) (H : ℝ)
    (hP : BoundedOnSegment H P) (t : ℝ) :
    ‖polynomialPullback D P t‖ ≤ H := by
  rw [polynomialPullback_real, Complex.norm_real, Real.norm_eq_abs]
  exact hP _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

private theorem mapped_polynomial_bound (P : ℝ[X]) (w : ℂ) (a : ℝ)
    (ha : 0 ≤ a) (hw : ‖w‖ ≤ Real.exp a) :
    ‖(P.map Complex.ofRealHom).eval w‖ ≤
      (∑ j ∈ P.support, |P.coeff j|) * Real.exp ((P.natDegree : ℝ) * a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum]
  unfold Polynomial.sum
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul, norm_pow, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    ‖w‖ ^ j ≤ (Real.exp a) ^ j := pow_le_pow_left₀ (norm_nonneg _) hw j
    _ = Real.exp ((j : ℝ) * a) := (Real.exp_nat_mul a j).symm
    _ ≤ Real.exp ((P.natDegree : ℝ) * a) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ ha
      exact_mod_cast Polynomial.le_natDegree_of_mem_supp j hj

theorem polynomialPullback_isBernstein {D H : ℝ} (hD : 0 < D)
    (P : ℝ[X]) (hdeg : (P.natDegree : ℝ) ≤ D) (hP : BoundedOnSegment H P) :
    IsBernsteinFunction Real.pi H (polynomialPullback D P) := by
  refine ⟨polynomialPullback_entire D P, polynomialPullback_bound_real D P H hP, ?_⟩
  let K : ℝ := 1 + ∑ j ∈ P.support, |P.coeff j|
  have hsum : 0 ≤ ∑ j ∈ P.support, |P.coeff j| := Finset.sum_nonneg (by intros; positivity)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro z
  have hfreq : 0 < Real.pi / D := div_pos Real.pi_pos hD
  have him : |(((Real.pi / D : ℝ) : ℂ) * z).im| = Real.pi / D * |z.im| := by
    simp [abs_mul, abs_of_pos hfreq]
  have hw := OMA.Port1.E1152.norm_complex_cos_le (((Real.pi / D : ℝ) : ℂ) * z)
  rw [him] at hw
  have hb := mapped_polynomial_bound P _ _ (mul_nonneg hfreq.le (abs_nonneg _)) hw
  have hrate : (P.natDegree : ℝ) * (Real.pi / D * |z.im|) ≤ Real.pi * |z.im| := by
    calc
      (P.natDegree : ℝ) * (Real.pi / D * |z.im|) ≤ D * (Real.pi / D * |z.im|) :=
        mul_le_mul_of_nonneg_right hdeg (mul_nonneg hfreq.le (abs_nonneg _))
      _ = Real.pi * |z.im| := by field_simp
  apply hb.trans
  apply mul_le_mul
  · dsimp [K]; linarith
  · exact Real.exp_le_exp.mpr hrate
  · positivity
  · dsimp [K]; positivity

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.FiniteObstruction ===== -/
section

noncomputable section
open Set
namespace OMA.Port1.E1133

/-- The sole analytic input to the grouping reduction. All indexed nodes,
including repetitions, and all entire interpolants are quantified here. -/
def FiniteBernsteinObstruction (H : ℝ) (k : ℕ) : Prop :=
  ∀ (t : Fin k → ℝ) (a : ℝ),
    (∀ i, t i ∈ Icc a (a + (k : ℝ) + 1)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi H f →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

theorem finiteObstruction_group {H : ℝ} {k : ℕ}
    (h : FiniteBernsteinObstruction H k)
    {α : Type*} [DecidableEq α] (g : Finset α) (hg : g.card = k)
    (t : α → ℝ) (a : ℝ) (ht : ∀ i ∈ g, t i ∈ Icc a (a + (k : ℝ) + 1)) :
    ∃ y : α → ℝ, (∀ i, |y i| ≤ 1) ∧
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi H f →
        ∃ i ∈ g, f (t i) ≠ (y i : ℂ) := by
  classical
  let e : Fin k ≃ g := (Fintype.equivFinOfCardEq (by simpa using hg)).symm
  obtain ⟨v, hv⟩ := h (fun j => t (e j)) a (fun j => ht _ (e j).property)
  let y : α → ℝ := fun i => if hi : i ∈ g then (v (e.symm ⟨i, hi⟩) : ℝ) else 0
  refine ⟨y, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ g
    · dsimp [y]
      rw [dif_pos hi, abs_le]
      exact (v (e.symm ⟨i, hi⟩)).property
    · simp [y, hi]
  · intro f hf
    obtain ⟨j, hj⟩ := hv f hf
    refine ⟨e j, (e j).property, ?_⟩
    simpa [y] using hj

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.BernsteinOperations ===== -/
section

noncomputable section
open Set
open scoped ComplexConjugate

namespace OMA.Port1.E1133

def bernsteinAffine (f : ℂ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  f ((a : ℂ) * z + b)

theorem IsBernsteinFunction.affine {σ H : ℝ} {f : ℂ → ℂ}
    (hf : IsBernsteinFunction σ H f) (a b : ℝ) :
    IsBernsteinFunction (σ * |a|) H (bernsteinAffine f a b) := by
  rcases hf with ⟨hd, hr, K, hK, hbound⟩
  refine ⟨?_, ?_, K, hK, ?_⟩
  · unfold bernsteinAffine
    exact hd.comp (by fun_prop)
  · intro t
    simpa [bernsteinAffine, ← Complex.ofReal_mul, ← Complex.ofReal_add] using hr (a * t + b)
  · intro z
    simpa [bernsteinAffine, Complex.mul_im, abs_mul, mul_assoc] using
      hbound ((a : ℂ) * z + b)

def bernsteinReflection (f : ℂ → ℂ) (z : ℂ) : ℂ := conj (f (conj z))

theorem bernsteinReflection_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (bernsteinReflection f) := by
  intro z
  exact differentiableAt_conj_conj_iff.mpr (hf (conj z))

def bernsteinRealification (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (f z + bernsteinReflection f z) / 2

theorem bernsteinRealification_real (f : ℂ → ℂ) (t : ℝ) :
    bernsteinRealification f t = ((f t).re : ℂ) := by
  apply Complex.ext <;>
    simp [bernsteinRealification, bernsteinReflection, Complex.div_re, Complex.div_im] <;> ring

theorem bernsteinRealification_real_value {f : ℂ → ℂ} {t y : ℝ}
    (h : f t = (y : ℂ)) : bernsteinRealification f t = (y : ℂ) := by
  rw [bernsteinRealification_real, h]
  simp

theorem bernsteinRealification_im (f : ℂ → ℂ) (t : ℝ) :
    (bernsteinRealification f t).im = 0 := by
  rw [bernsteinRealification_real]
  simp

theorem IsBernsteinFunction.realification {σ H : ℝ} {f : ℂ → ℂ}
    (hf : IsBernsteinFunction σ H f) :
    IsBernsteinFunction σ H (bernsteinRealification f) := by
  obtain ⟨hd, hr, K, hK, hb⟩ := hf
  refine ⟨?_, ?_, K, hK, ?_⟩
  · exact (hd.add (bernsteinReflection_entire hd)).div_const 2
  · intro t
    rw [bernsteinRealification_real, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hr t)
  · intro z
    have href : ‖bernsteinReflection f z‖ ≤ K * Real.exp (σ * |z.im|) := by
      simpa [bernsteinReflection] using hb (conj z)
    calc
      ‖bernsteinRealification f z‖ = ‖f z + bernsteinReflection f z‖ / 2 := by
        simp [bernsteinRealification, norm_div]
      _ ≤ (‖f z‖ + ‖bernsteinReflection f z‖) / 2 := by
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ ≤ K * Real.exp (σ * |z.im|) := by linarith [hb z]

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.IndexedObstruction ===== -/
section

noncomputable section
open Set

namespace OMA.Port1.E1133

/-- The finite analytic obstruction restricted to distinct nodes. -/
def InjectiveBernsteinObstruction (H : ℝ) (k : ℕ) : Prop :=
  ∀ (t : Fin k → ℝ), Function.Injective t → ∀ (a : ℝ),
    (∀ i, t i ∈ Icc a (a + (k : ℝ) + 1)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi H f →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

theorem finiteObstruction_of_injective {H : ℝ} {k : ℕ}
    (h : InjectiveBernsteinObstruction H k) : FiniteBernsteinObstruction H k := by
  classical
  intro t a ht
  by_cases hi : Function.Injective t
  · exact h t hi a ht
  · simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨i, j, hij, hne⟩ := hi
    let y : Fin k → Icc (-1 : ℝ) 1 := fun l =>
      if l = i then ⟨0, by constructor <;> norm_num⟩
      else ⟨1, by constructor <;> norm_num⟩
    refine ⟨y, ?_⟩
    intro f _
    by_contra hfit
    push Not at hfit
    have hzero : f (t i) = 0 := by simpa [y] using hfit i
    have hone : f (t j) = 1 := by simpa [y, Ne.symm hne] using hfit j
    have : (0 : ℂ) = 1 := hzero.symm.trans ((congrArg (fun x : ℝ => f x) hij).trans hone)
    exact zero_ne_one this

/-- A freely chosen shorter centered interval leaves a gap at the period ends.
The bandwidth exactly compensates for the affine compression. -/
def CenteredIntervalRealBernsteinObstruction (H : ℝ) (k : ℕ) (L : ℝ) : Prop :=
  ∀ (t : Fin k → ℝ), Function.Injective t →
    (∀ i, t i ∈ Icc (-L / 2) (L / 2)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction (Real.pi * (((k : ℝ) + 1) / L)) H f →
        (∀ x : ℝ, (f x).im = 0) →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

theorem finiteObstruction_of_centered_interval_real {H L : ℝ} {k : ℕ}
    (hL : 0 < L) (h : CenteredIntervalRealBernsteinObstruction H k L) :
    FiniteBernsteinObstruction H k := by
  classical
  apply finiteObstruction_of_injective
  intro t hinj a ht
  let c : ℝ := ((k : ℝ) + 1) / L
  let b : ℝ := a + ((k : ℝ) + 1) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcL : c * L = (k : ℝ) + 1 := by
    dsimp [c]
    field_simp
  let s : Fin k → ℝ := fun i => (t i - b) / c
  have hs : Function.Injective s := by
    intro i j hij
    apply hinj
    have heq : t i - b = t j - b := (div_left_inj' hc.ne').mp hij
    linarith
  have hloc : ∀ i, s i ∈ Icc (-L / 2) (L / 2) := by
    intro i
    obtain ⟨hil, hir⟩ := ht i
    constructor
    · apply (le_div_iff₀ hc).mpr
      dsimp [b]
      nlinarith
    · apply (div_le_iff₀ hc).mpr
      dsimp [b]
      nlinarith
  obtain ⟨y, hy⟩ := h s hs hloc
  refine ⟨y, ?_⟩
  intro f hf
  have hfa : IsBernsteinFunction (Real.pi * (((k : ℝ) + 1) / L)) H
      (bernsteinAffine f c b) := by
    simpa only [abs_of_pos hc] using hf.affine c b
  obtain ⟨i, hi⟩ := hy (bernsteinRealification (bernsteinAffine f c b))
    hfa.realification (bernsteinRealification_im _)
  refine ⟨i, ?_⟩
  intro heq
  apply hi
  apply bernsteinRealification_real_value
  convert heq using 1
  unfold bernsteinAffine
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
  congr 1
  congr 1
  dsimp [s]
  field_simp
  ring

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.ExactInterpolation ===== -/
section

/-! Uniform approximate interpolation implies exact interpolation, by a
convergent residual-correction series inside a closed Fourier band. -/

noncomputable section
open scoped BigOperators Topology Real
open Set Finset Filter
open OMA.Port1.E1152

namespace OMA.Port1.E1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A quantitative residual-correction theorem. The approximate preimages may
be chosen nonlinearly; no linear right inverse is assumed or constructed. -/
theorem exists_exact_preimage_of_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ y : F, ∃ x ∈ S,
      ‖x‖ ≤ K * ‖y‖ ∧ ‖y - T x‖ ≤ q * ‖y‖)
    (y : F) :
    ∃ x ∈ S, T x = y ∧ ‖x‖ ≤ K / (1 - q) * ‖y‖ := by
  classical
  choose A hAS hAnorm hAerr using happrox
  let r : ℕ → F := Nat.rec y (fun _ v => v - T (A v))
  let u : ℕ → E := fun n => A (r n)
  have hrzero : r 0 = y := rfl
  have hrsucc (n : ℕ) : r (n + 1) = r n - T (u n) := rfl
  have hrnorm (n : ℕ) : ‖r n‖ ≤ q ^ n * ‖y‖ := by
    induction n with
    | zero => simp [hrzero]
    | succ n ih =>
      calc
        ‖r (n + 1)‖ ≤ q * ‖r n‖ := hAerr (r n)
        _ ≤ q * (q ^ n * ‖y‖) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * ‖y‖ := by rw [pow_succ]; ring
  have hunorm (n : ℕ) : ‖u n‖ ≤ (K * ‖y‖) * q ^ n := by
    exact (hAnorm (r n)).trans (by
      calc
        K * ‖r n‖ ≤ K * (q ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hrnorm n) hK
        _ = (K * ‖y‖) * q ^ n := by ring)
  have hgeo : Summable (fun n : ℕ => (K * ‖y‖) * q ^ n) :=
    (hasSum_geometric_of_lt_one hq hq1).summable.mul_left _
  have hunormsum : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hunorm hgeo
  have husum : Summable u := hunormsum.of_norm
  have hmem : (∑' n, u n) ∈ S :=
    hS.mem_of_tendsto husum.hasSum.tendsto_sum_nat
      (Eventually.of_forall fun n => S.sum_mem fun i hi => hAS (r i))
  have hpartial (n : ℕ) : T (∑ i ∈ Finset.range n, u i) = y - r n := by
    induction n with
    | zero => simp [hrzero]
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, hrsucc]
      abel
  have hrlim : Tendsto r atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => hrnorm n)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖y‖
  have hTlim : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop
      (𝓝 (T (∑' n, u n))) := T.continuous.tendsto _ |>.comp husum.hasSum.tendsto_sum_nat
  have hylim : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop (𝓝 y) := by
    simpa only [hpartial, sub_zero] using tendsto_const_nhds.sub hrlim
  refine ⟨∑' n, u n, hmem, tendsto_nhds_unique hTlim hylim, ?_⟩
  calc
    ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm hunormsum
    _ ≤ ∑' n : ℕ, (K * ‖y‖) * q ^ n := Summable.tsum_le_tsum hunorm hunormsum hgeo
    _ = K / (1 - q) * ‖y‖ := by
      rw [tsum_mul_left, (hasSum_geometric_of_lt_one hq hq1).tsum_eq]
      ring

/-- Unit-data approximate solvability already suffices; all other residuals
are reduced to it by scalar normalization. -/
theorem exists_exact_preimage_of_unit_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ y : F, ‖y‖ ≤ 1 → ∃ x ∈ S,
      ‖x‖ ≤ K ∧ ‖y - T x‖ ≤ q)
    (y : F) :
    ∃ x ∈ S, T x = y ∧ ‖x‖ ≤ K / (1 - q) * ‖y‖ := by
  apply exists_exact_preimage_of_approx T S hS K q hK hq hq1 ?_ y
  intro z
  by_cases hz : z = 0
  · exact ⟨0, S.zero_mem, by simp [hz], by simp [hz]⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  obtain ⟨x, hx, hxn, hxe⟩ := happrox (‖z‖⁻¹ • z) (by
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn, le_refl])
  refine ⟨‖z‖ • x, S.smul_mem _ hx, ?_, ?_⟩
  · rw [norm_smul, norm_norm]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hxn (norm_nonneg z)
  · have he : z - T (‖z‖ • x) = ‖z‖ • (‖z‖⁻¹ • z - T x) := by
      rw [map_smul, smul_sub, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [he, norm_smul, norm_norm]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hxe (norm_nonneg z)

/-- The actual real-valued part of the finite complex Fourier band. -/
def realFourierBand (m : ℕ) : Submodule ℝ CircleFunction where
  carrier := {f | f ∈ bandSpace m ∧ ∀ x, (f x).im = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨(bandSpace m).add_mem hf.1 hg.1, by intro x; simp [hf.2, hg.2]⟩
  smul_mem' := by
    intro c f hf
    refine ⟨((bandSpace m).restrictScalars ℝ).smul_mem c hf.1, ?_⟩
    intro x
    change ((c : ℂ) * f x).im = 0
    simp [hf.2]

/-- Closure is proved from the finite spanning family of characters, rather
than postulated as part of the interpolation hypothesis. -/
theorem realFourierBand_isClosed (m : ℕ) : IsClosed (realFourierBand m : Set CircleFunction) := by
  have : FiniteDimensional ℂ (bandSpace m) :=
    FiniteDimensional.span_of_finite ℂ
      ((Set.finite_Icc (-(m : ℤ)) m).image character)
  have hband := (bandSpace m).closed_of_finiteDimensional
  have hreal : IsClosed {f : CircleFunction | ∀ x, (f x).im = 0} := by
    have h : IsClosed (⋂ x : FourierCircle, {f : CircleFunction | (f x).im = 0}) :=
      isClosed_iInter (fun x : FourierCircle =>
      isClosed_eq (show Continuous (fun f : CircleFunction => (f x).im) by fun_prop)
        continuous_const)
    simpa only [Set.ofPred_forall] using h
  exact hband.inter hreal

/-- The true finite-dimensional real sample vector of a continuous function. -/
def circleSampleMap {ι : Type*} [Fintype ι] (node : ι → FourierCircle) :
    CircleFunction →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousMap.evalCLM ℝ (node i))

theorem circleSampleMap_apply {ι : Type*} [Fintype ι]
    (node : ι → FourierCircle) (f : CircleFunction) (i : ι) :
    circleSampleMap node f i = (f (node i)).re := rfl

/-- The unit-data form needed after windowing and periodization. Its conclusion
applies to all data vectors, so it also supplies every residual correction. -/
theorem exact_real_trig_interpolation_of_unit_approx
    {ι : Type*} [Fintype ι] (node : ι → FourierCircle) (m : ℕ)
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ d : ι → ℝ, ‖d‖ ≤ 1 → ∃ f : CircleFunction,
      f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      ‖f‖ ≤ K ∧ ∀ i, |(f (node i)).re - d i| ≤ q)
    (d : ι → ℝ) :
    ∃ f : CircleFunction, f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      (∀ i, f (node i) = (d i : ℂ)) ∧ ‖f‖ ≤ K / (1 - q) * ‖d‖ := by
  have ha : ∀ y : ι → ℝ, ‖y‖ ≤ 1 → ∃ f ∈ realFourierBand m,
      ‖f‖ ≤ K ∧ ‖y - circleSampleMap node f‖ ≤ q := by
    intro y hy
    obtain ⟨f, hfb, hfr, hfn, hfe⟩ := happrox y hy
    refine ⟨f, ⟨hfb, hfr⟩, hfn, ?_⟩
    apply (pi_norm_le_iff_of_nonneg hq).mpr
    intro i
    simpa only [Pi.sub_apply, circleSampleMap_apply, Real.norm_eq_abs, abs_sub_comm]
      using hfe i
  obtain ⟨f, hf, he, hn⟩ := exists_exact_preimage_of_unit_approx
    (circleSampleMap node) (realFourierBand m) (realFourierBand_isClosed m)
    K q hK hq hq1 ha d
  refine ⟨f, hf.1, hf.2, ?_, hn⟩
  intro i
  apply Complex.ext
  · exact congrFun he i
  · exact hf.2 (node i)

/-- In particular, unit data admit an exact interpolant of norm at most
K/(1-q), the form used to contradict the finite obstruction. -/
theorem exact_unit_real_trig_interpolation
    {ι : Type*} [Fintype ι] (node : ι → FourierCircle) (m : ℕ)
    (K q : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1)
    (happrox : ∀ d : ι → ℝ, ‖d‖ ≤ 1 → ∃ f : CircleFunction,
      f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      ‖f‖ ≤ K ∧ ∀ i, |(f (node i)).re - d i| ≤ q)
    (d : ι → ℝ) (hd : ‖d‖ ≤ 1) :
    ∃ f : CircleFunction, f ∈ bandSpace m ∧ (∀ x, (f x).im = 0) ∧
      (∀ i, f (node i) = (d i : ℂ)) ∧ ‖f‖ ≤ K / (1 - q) := by
  obtain ⟨f, hfb, hfr, hfe, hfn⟩ := exact_real_trig_interpolation_of_unit_approx
    node m K q hK hq hq1 happrox d
  refine ⟨f, hfb, hfr, hfe, hfn.trans ?_⟩
  have hconst : 0 ≤ K / (1 - q) := div_nonneg hK (sub_pos.mpr hq1).le
  simpa using mul_le_mul_of_nonneg_left hd hconst

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.AnalyticParameters ===== -/
section

noncomputable section
namespace OMA.Port1.E1133

def interiorRatio (δ : ℝ) : ℝ := 1 / (1 + δ/4)
def plateauRate (δ : ℝ) : ℝ := Real.pi * δ / 24
def compressedType (δ : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (((2*n : ℕ) : ℝ) + 1) / (2*interiorRatio δ*n)

theorem interiorRatio_pos {δ : ℝ} (hδ : 0 < δ) : 0 < interiorRatio δ := by
  unfold interiorRatio
  positivity

theorem interiorRatio_lt_one {δ : ℝ} (hδ : 0 < δ) : interiorRatio δ < 1 := by
  unfold interiorRatio
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem plateauRate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < plateauRate δ := by
  unfold plateauRate
  positivity

theorem compressedType_bounds {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hn : (4+δ)/δ ≤ (n : ℝ)) :
    Real.pi ≤ compressedType δ n ∧
      compressedType δ n + 6*plateauRate δ ≤ Real.pi*(1+3*δ/4) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hscale : (4+δ) ≤ (n : ℝ)*δ := (div_le_iff₀ hδ).mp hn
  have hβ := interiorRatio_pos hδ
  have heq : compressedType δ n = Real.pi*((1+δ/4)*(1+1/(2*(n : ℝ)))) := by
    unfold compressedType interiorRatio
    push_cast
    field_simp
  rw [heq]
  constructor
  · have hone : 1 ≤ (1+δ/4)*(1+1/(2*(n : ℝ))) := by
      nlinarith [one_div_pos.mpr (show (0 : ℝ) < 2*n by positivity)]
    nlinarith [Real.pi_pos]
  · have hsmall : (1+δ/4)/(2*(n : ℝ)) ≤ δ/4 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*n)).mpr
      nlinarith
    have hs : (1+δ/4)*(1+1/(2*(n : ℝ))) ≤ 1+δ/2 := by
      calc
        _ = 1+δ/4 + (1+δ/4)/(2*(n : ℝ)) := by ring
        _ ≤ _ := by linarith
    unfold plateauRate
    nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le]

theorem compressed_bandwidth_budget {δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hn : (4+δ)/δ ≤ (n : ℝ)) :
    let m := Nat.ceil ((compressedType δ n + 6*plateauRate δ)*(2*(n : ℝ))/(2*Real.pi))
    n ≤ m ∧ (m : ℝ) ≤ n + δ*n := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hnδ : 4+δ ≤ (n : ℝ)*δ := (div_le_iff₀ hδ).mp hn
  obtain ⟨hlo,hhi⟩ := compressedType_bounds hδ hn
  have hα := plateauRate_pos hδ
  let b : ℝ := (compressedType δ n+6*plateauRate δ)*(2*(n : ℝ))/(2*Real.pi)
  have hb : (n : ℝ) ≤ b := by
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlo (show (0 : ℝ) ≤ 2*n by positivity),
      mul_nonneg hα.le hn0.le]
  have hbu : b ≤ (1+3*δ/4)*(n : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhi (show (0 : ℝ) ≤ 2*n by positivity)]
  dsimp only
  constructor
  · exact Nat.cast_le.mp (hb.trans (Nat.le_ceil b))
  · have hc : (Nat.ceil b : ℝ) < b+1 := Nat.ceil_lt_add_one (hn0.le.trans hb)
    change (Nat.ceil b : ℝ) ≤ _
    nlinarith

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.PlateauWindow ===== -/
section

noncomputable section
open scoped Topology Real
open MeasureTheory Set Filter
open OMA.Port1.E1152

namespace OMA.Port1.E1133

/-- The sixth-power sinc plateau used to truncate an entire interpolant. -/
def plateauWindow (α τ : ℝ) (z : ℂ) : ℂ :=
  (α : ℂ) * ∫ t : ℝ in -τ..τ, entireSinc ((α : ℂ) * (z - t)) ^ 6

def plateauWindowReal (α τ x : ℝ) : ℝ :=
  α * ∫ t : ℝ in -τ..τ, Real.sinc (α * (x-t)) ^ 6

theorem plateauWindow_real (α τ x : ℝ) :
    plateauWindow α τ x = (plateauWindowReal α τ x : ℂ) := by
  unfold plateauWindow plateauWindowReal
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [show (α : ℂ) * ((x : ℂ) - t) = ((α * (x-t) : ℝ) : ℂ) by push_cast; rfl,
    entireSinc_real]
  push_cast
  rfl

theorem differentiable_plateauWindow (α τ : ℝ) : Differentiable ℂ (plateauWindow α τ) := by
  let F : ℂ → ℝ → ℂ := fun z t => entireSinc ((α : ℂ) * (z-t)) ^ 6
  let F' : ℂ → ℝ → ℂ := fun z t =>
    6 * entireSinc ((α : ℂ) * (z-t)) ^ 5 *
      (deriv entireSinc ((α : ℂ) * (z-t)) * α)
  have hc : Continuous entireSinc := differentiable_entireSinc.continuous
  have hc' : Continuous (deriv entireSinc) := differentiable_entireSinc.deriv.continuous
  have hd (z : ℂ) (t : ℝ) : HasDerivAt (fun w => F w t) (F' z t) z := by
    convert (((differentiable_entireSinc _).hasDerivAt.comp z
        ((hasDerivAt_id z).sub_const (t : ℂ) |>.const_mul (α : ℂ))).pow 6) using 1 <;>
      first | rfl | simp [F']
  have hcF (z : ℂ) : Continuous (F z) := by dsimp [F]; fun_prop
  have hcF' : Continuous (fun p : ℂ × ℝ => F' p.1 p.2) := by dsimp [F']; fun_prop
  have hi : Differentiable ℂ (fun z => ∫ t : ℝ in -τ..τ, F z t) := by
    intro z
    obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod
      (isCompact_uIcc (a := -τ) (b := τ))).exists_bound_of_continuousOn hcF'.continuousOn
    have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (s := Metric.closedBall z 1) (bound := fun _ => C)
      (μ := volume) (a := -τ) (b := τ)
      (Metric.closedBall_mem_nhds z (by norm_num : (0 : ℝ) < 1))
      (Eventually.of_forall fun w => (hcF w).aestronglyMeasurable)
      ((hcF z).intervalIntegrable _ _)
      ((hcF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun t ht w hw => hC (w,t) ⟨hw, uIoc_subset_uIcc ht⟩)
      (continuous_const.intervalIntegrable _ _)
      (ae_of_all _ fun t _ w _ => hd w t)
    exact h.2.differentiableAt
  convert hi.const_mul (α : ℂ) using 1 <;> rfl

theorem sinc_sixth_le_one (x : ℝ) : Real.sinc x ^ 6 ≤ 1 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one x) 6
  simpa only [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, sq_abs, one_pow] using h

theorem sinc_sixth_le_cauchy (x : ℝ) : Real.sinc x ^ 6 ≤ 2 / (1+x^2) := by
  have h1 := sinc_sixth_le_one x
  have hs : (Real.sinc x)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one x) 2
  have h4 : (Real.sinc x)^4 ≤ 1 := by nlinarith [sq_nonneg ((Real.sinc x)^2-1)]
  have hsin : x * Real.sinc x = Real.sin x := by
    by_cases hx : x=0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]; field_simp
  have hsin2 : (Real.sin x)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one x) 2
  have hprod : x^2 * Real.sinc x^6 ≤ 1 := by
    calc
      _ = (Real.sin x)^2 * (Real.sinc x)^4 := by rw [← hsin]; ring
      _ ≤ 1 * 1 := mul_le_mul hsin2 h4 (by positivity) (by norm_num)
      _ = 1 := by norm_num
  apply (le_div_iff₀ (by positivity : 0 < 1+x^2)).mpr
  nlinarith

theorem plateauWindowReal_nonneg {α τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ) (x : ℝ) :
    0 ≤ plateauWindowReal α τ x := by
  apply mul_nonneg hα
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) (fun _ => by positivity)

theorem plateauWindowReal_change_variables (α τ x : ℝ) :
    plateauWindowReal α τ x =
      ∫ u : ℝ in α*(x-τ)..α*(x+τ), Real.sinc u ^ 6 := by
  unfold plateauWindowReal
  have h := intervalIntegral.smul_integral_comp_sub_mul
    (fun u : ℝ => Real.sinc u ^ 6) (a := -τ) (b := τ) α (α*x)
  simpa only [smul_eq_mul, ← mul_sub, sub_neg_eq_add] using h

/-- A deliberately nonoptimal absolute upper bound, independent of both scales. -/
theorem plateauWindowReal_le {α τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ) (x : ℝ) :
    plateauWindowReal α τ x ≤ 2 * Real.pi := by
  rw [plateauWindowReal_change_variables]
  have hi : IntervalIntegrable (fun u : ℝ => Real.sinc u ^ 6) volume
      (α*(x-τ)) (α*(x+τ)) := (Real.continuous_sinc.pow 6).intervalIntegrable _ _
  have hc : Continuous (fun u : ℝ => 2/(1+u^2)) := by
    exact continuous_const.div (by fun_prop) (fun u => by positivity)
  have h := intervalIntegral.integral_mono (show α*(x-τ) ≤ α*(x+τ) by nlinarith)
    hi (hc.intervalIntegrable _ _) sinc_sixth_le_cauchy
  calc
    _ ≤ ∫ u : ℝ in α*(x-τ)..α*(x+τ), 2/(1+u^2) := h
    _ = 2 * (Real.arctan (α*(x+τ)) - Real.arctan (α*(x-τ))) := by
      simp_rw [show ∀ u : ℝ, 2/(1+u^2)=2*(1/(1+u^2)) by intro u; ring]
      rw [intervalIntegral.integral_const_mul, integral_one_div_one_add_sq]
    _ ≤ 2 * Real.pi := by
      linarith [Real.arctan_lt_pi_div_two (α*(x+τ)),
        Real.neg_pi_div_two_lt_arctan (α*(x-τ))]

theorem exists_sinc_sixth_near_one : ∃ η > 0, ∀ x : ℝ, |x| ≤ η →
    1/2 ≤ Real.sinc x ^ 6 := by
  have hc := (Real.continuous_sinc.pow 6).continuousAt (x := 0)
  obtain ⟨η,hη,hcη⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  refine ⟨η/2,by positivity,?_⟩
  intro x hx
  have h := hcη (show dist x 0 < η by
    simpa [Real.dist_eq] using hx.trans_lt (half_lt_self hη))
  simp only [Pi.pow_apply, Real.sinc_zero, one_pow, Real.dist_eq] at h
  linarith [(abs_lt.mp h).1]

theorem plateauWindowReal_lower {η α τ x : ℝ} (hη : 0 < η)
    (hs : ∀ u : ℝ, |u| ≤ η → 1/2 ≤ Real.sinc u ^ 6)
    (hα : 0 ≤ α) (hsize : η ≤ α*τ) (hx : |x| ≤ τ) :
    η/2 ≤ plateauWindowReal α τ x := by
  rw [plateauWindowReal_change_variables]
  have hx' := abs_le.mp hx
  have ha : α*(x-τ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα (by linarith)
  have hb : 0 ≤ α*(x+τ) := mul_nonneg hα (by linarith)
  have hi : IntervalIntegrable (fun u : ℝ => Real.sinc u ^ 6) volume
      (α*(x-τ)) (α*(x+τ)) := (Real.continuous_sinc.pow 6).intervalIntegrable _ _
  by_cases hxx : 0 ≤ x
  · have hηb : η ≤ α*(x+τ) := by nlinarith
    have hsmall : η/2 ≤ ∫ u : ℝ in 0..η, Real.sinc u^6 := by
      have hm := intervalIntegral.integral_mono_on (μ := volume) hη.le
        (continuous_const.intervalIntegrable 0 η)
        ((Real.continuous_sinc.pow 6).intervalIntegrable 0 η)
        (fun u (hu : u ∈ Icc 0 η) => hs u (by simpa [abs_of_nonneg hu.1] using hu.2))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one_div, Pi.pow_apply] using hm
    exact hsmall.trans (intervalIntegral.integral_mono_interval ha hη.le hηb
      (ae_of_all _ fun _ => by positivity) hi)
  · have hηa : α*(x-τ) ≤ -η := by nlinarith
    have hsmall : η/2 ≤ ∫ u : ℝ in -η..0, Real.sinc u^6 := by
      have hm := intervalIntegral.integral_mono_on (μ := volume) (show -η ≤ 0 by linarith)
        (continuous_const.intervalIntegrable (-η) 0)
        ((Real.continuous_sinc.pow 6).intervalIntegrable (-η) 0)
        (fun u (hu : u ∈ Icc (-η) 0) => hs u (abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩))
      simpa only [intervalIntegral.integral_const, zero_sub, neg_neg, smul_eq_mul, mul_one_div, Pi.pow_apply] using hm
    exact hsmall.trans (intervalIntegral.integral_mono_interval hηa (by linarith) hb
      (ae_of_all _ fun _ => by positivity) hi)

theorem plateauWindow_uniform_positive : ∃ η > 0, ∀ α τ x : ℝ,
    0 ≤ α → η ≤ α*τ → |x| ≤ τ → η/2 ≤ plateauWindowReal α τ x := by
  obtain ⟨η,hη,hs⟩ := exists_sinc_sixth_near_one
  exact ⟨η,hη,fun _ _ _ hα hsize hx => plateauWindowReal_lower hη hs hα hsize hx⟩

theorem scaled_sinc_sixth_decay {α : ℝ} (hα : 0 < α) (z : ℂ) :
    ‖entireSinc ((α : ℂ)*z)^6‖ ≤
      (2/min 1 α)^6 * Real.exp (6*α*|z.im|)/(1+‖z‖)^6 := by
  let c := min 1 α
  have hc : 0 < c := lt_min (by norm_num) hα
  have hd : c*(1+‖z‖) ≤ 1+α*‖z‖ := by
    have h1 : c ≤ 1 := min_le_left _ _
    have h2 : c ≤ α := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg z)]
  have hb := norm_entireSinc_decay ((α : ℂ)*z)
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
    abs_mul, abs_of_pos hα, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hb
  have hb' : ‖entireSinc ((α : ℂ)*z)‖ ≤
      (2/c)*Real.exp (α*|z.im|)/(1+‖z‖) := by
    apply hb.trans
    calc
      _ ≤ 2*Real.exp (α*|z.im|)/(c*(1+‖z‖)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd
      _ = _ := by field_simp
  have hh := pow_le_pow_left₀ (norm_nonneg _) hb' 6
  rw [← norm_pow, div_pow, mul_pow, ← Real.exp_nat_mul] at hh
  simpa [c, mul_assoc] using hh

/-- The compact convolution preserves sixth-order complex decay and adds type `6α`. -/
theorem plateauWindow_complex_decay {α τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (z : ℂ) :
    ‖plateauWindow α τ z‖ ≤
      (2*α*τ*((2/min 1 α)*(1+τ))^6) *
        Real.exp (6*α*|z.im|)/(1+‖z‖)^6 := by
  let C := ((2/min 1 α)*(1+τ))^6 * Real.exp (6*α*|z.im|)/(1+‖z‖)^6
  have hkernel (t : ℝ) (ht : t ∈ uIoc (-τ) τ) :
      ‖entireSinc ((α : ℂ)*(z-t))^6‖ ≤ C := by
    have ht' : |t| ≤ τ := by
      have hm : t ∈ Ioc (-τ) τ := by simpa [uIoc_of_le (show -τ ≤ τ by linarith)] using ht
      exact abs_le.mpr ⟨hm.1.le,hm.2⟩
    have hn : ‖z‖ ≤ ‖z-(t : ℂ)‖+τ := by
      calc
        _ ≤ ‖z-(t : ℂ)‖+‖(t : ℂ)‖ := norm_le_norm_sub_add z t
        _ ≤ _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using add_le_add_right ht' _
    have hp : 1+‖z‖ ≤ (1+τ)*(1+‖z-(t : ℂ)‖) := by
      nlinarith [norm_nonneg (z-(t : ℂ))]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖z‖) hp 6
    have hh := scaled_sinc_sixth_decay hα (z-t)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hh
    apply hh.trans
    dsimp [C]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      _ ≤ ((2/min 1 α)^6*Real.exp (6*α*|z.im|))*
          ((1+τ)*(1+‖z-(t : ℂ)‖))^6 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -τ) (b := τ) hkernel
  unfold plateauWindow
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  calc
    _ ≤ α*(C*|τ-(-τ)|) := mul_le_mul_of_nonneg_left hi hα.le
    _ = _ := by rw [abs_of_nonneg (by linarith : 0 ≤ τ-(-τ))]; dsimp [C]; ring

theorem sinc_sixth_tail {α d : ℝ} (hα : 0 < α) (hd : d ≠ 0) :
    Real.sinc (α*d)^6 ≤ (1/(α*|d|))^6 := by
  have h : |Real.sinc (α*d)| ≤ 1/(α*|d|) := by
    rw [Real.sinc_of_ne_zero (mul_ne_zero hα.ne' hd), abs_div, abs_mul, abs_of_pos hα]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 6
  simpa only [show (6 : ℕ)=2*3 from rfl, pow_mul, sq_abs] using hh

/-- Outside the plateau, the distance from the whole integration interval controls the tail. -/
theorem plateauWindowReal_tail {α τ x : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (hx : τ < |x|) :
    plateauWindowReal α τ x ≤ 2*α*τ / (α*(|x|-τ))^6 := by
  have hi : IntervalIntegrable (fun t : ℝ => Real.sinc (α*(x-t))^6) volume (-τ) τ :=
    (Real.continuous_sinc.comp (by fun_prop) |>.pow 6).intervalIntegrable _ _
  have hpoint (t : ℝ) (ht : t ∈ Icc (-τ) τ) :
      Real.sinc (α*(x-t))^6 ≤ (1/(α*(|x|-τ)))^6 := by
    have ht' : |t| ≤ τ := abs_le.mpr ht
    have hd : |x|-τ ≤ |x-t| := by linarith [abs_sub_abs_le_abs_sub x t]
    have hdt : 0 < |x-t| := lt_of_lt_of_le (sub_pos.mpr hx) hd
    apply (sinc_sixth_tail hα (sub_ne_zero.mpr (fun h => by simp [h] at hdt))).trans
    exact pow_le_pow_left₀ (by positivity)
      (one_div_le_one_div_of_le (mul_pos hα (sub_pos.mpr hx))
        (mul_le_mul_of_nonneg_left hd hα.le)) 6
  have hm := intervalIntegral.integral_mono_on (μ := volume) (show -τ ≤ τ by linarith)
    hi (continuous_const.intervalIntegrable _ _) hpoint
  unfold plateauWindowReal
  calc
    _ ≤ α * ((τ-(-τ)) * (1/(α*(|x|-τ)))^6) := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul] using
        mul_le_mul_of_nonneg_left hm hα.le
    _ = _ := by rw [div_pow]; ring

theorem norm_plateauWindow_real_le {α τ : ℝ} (hα : 0 ≤ α) (hτ : 0 ≤ τ) (x : ℝ) :
    ‖plateauWindow α τ x‖ ≤ 2*Real.pi := by
  rw [plateauWindow_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (plateauWindowReal_nonneg hα hτ x)]
  exact plateauWindowReal_le hα hτ x

theorem norm_plateauWindow_real_tail {α τ x : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ)
    (hx : τ < |x|) :
    ‖plateauWindow α τ x‖ ≤ 2*α*τ/(α*(|x|-τ))^6 := by
  rw [plateauWindow_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (plateauWindowReal_nonneg hα.le hτ x)]
  exact plateauWindowReal_tail hα hτ hx

theorem mul_plateauWindow_decay {f : ℂ → ℂ} {α τ σ K : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (hf : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|)) (z : ℂ) :
    ‖f z * plateauWindow α τ z‖ ≤
      (K*(2*α*τ*((2/min 1 α)*(1+τ))^6)) *
        Real.exp ((σ+6*α)*|z.im|)/(1+‖z‖)^6 := by
  rw [norm_mul]
  apply (mul_le_mul (hf z) (plateauWindow_complex_decay hα hτ z)
    (norm_nonneg _) (by positivity)).trans_eq
  rw [add_mul, Real.exp_add]
  ring

end OMA.Port1.E1133


end
end

/- ===== OMA.Port1.E1133.EntireToTrig ===== -/
section

noncomputable section
open Filter Topology Set MeasureTheory
open scoped BigOperators
open OMA.Port1.E1152

namespace OMA.Port1.E1133

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- This real-axis error constant uses the uniform real bound `H`, not the
nonuniform complex growth prefactor of the entire interpolant. -/
def plateauPeriodError (α τ T H : ℝ) : ℝ :=
  (2*H*α*τ)*(2/(α*(T/2-τ)))^6 * ∑' k : ℤ, sixthLatticeWeight k

theorem windowed_translate_bound {f : ℂ → ℂ} {α τ T H : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H) (x : ℝ) (hx : |x| ≤ T/2)
    (k : ℤ) (hk : k ≠ 0) :
    ‖f ((x+T*(k:ℝ) : ℝ) : ℂ) * plateauWindow α τ ((x+T*(k:ℝ) : ℝ) : ℂ)‖ ≤
      ((2*H*α*τ)*(2/(α*(T/2-τ)))^6) * sixthLatticeWeight k := by
  have hT : 0 < T := by linarith
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hh : (0 : ℤ) < |k| := abs_pos.mpr hk
    exact_mod_cast (show (1 : ℤ) ≤ |k| by omega)
  have ht : T*|(k:ℝ)| ≤ |x+T*(k:ℝ)|+|x| := by
    have hh := abs_sub_le (x+T*(k:ℝ)) 0 x
    simpa [abs_mul, abs_of_pos hT] using hh
  have hdk : (T/2-τ)/2 * (1+|(k:ℝ)|) ≤ |x+T*(k:ℝ)|-τ := by
    nlinarith [mul_nonneg hτ (sub_nonneg.mpr hk1),
      mul_nonneg hT.le (sub_nonneg.mpr hk1)]
  have hout : τ < |x+T*(k:ℝ)| := by
    have hp : 0 < (T/2-τ)/2*(1+|(k:ℝ)|) := by positivity
    linarith
  have hr : (1+|(k:ℝ)|)/(α*(|x+T*(k:ℝ)|-τ)) ≤ 2/(α*(T/2-τ)) := by
    apply (div_le_div_iff₀ (mul_pos hα (sub_pos.mpr hout))
      (mul_pos hα (sub_pos.mpr hgap))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdk hα.le]
  have hr6 := pow_le_pow_left₀ (by positivity : 0 ≤
    (1+|(k:ℝ)|)/(α*(|x+T*(k:ℝ)|-τ))) hr 6
  rw [norm_mul]
  calc
    _ ≤ H*(2*α*τ/(α*(|x+T*(k:ℝ)|-τ))^6) :=
      mul_le_mul (hf _) (norm_plateauWindow_real_tail hα hτ hout) (norm_nonneg _) hH
    _ = ((2*H*α*τ)*((1+|(k:ℝ)|)/(α*(|x+T*(k:ℝ)|-τ)))^6)*
        sixthLatticeWeight k := by
      unfold sixthLatticeWeight
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr6 (by positivity)) (sixthLatticeWeight_nonneg k)

/-- Removing the zero translate from a summable periodization. -/
theorem periodize_error_of_real_majorant (g : ℂ → ℂ) (T x A : ℝ)
    (hA : 0 ≤ A)
    (hs : Summable fun k : ℤ => g ((x : ℂ)+((T*(k:ℝ) : ℝ) : ℂ)))
    (hb : ∀ k : ℤ, k ≠ 0 → ‖g ((x+T*(k:ℝ) : ℝ) : ℂ)‖ ≤ A*sixthLatticeWeight k) :
    ‖periodize g T x-g x‖ ≤ A*∑' k : ℤ, sixthLatticeWeight k := by
  let r : ℤ → ℂ := fun k => if k=0 then 0 else g ((x+T*(k:ℝ) : ℝ) : ℂ)
  have hbound : ∀ k : ℤ, ‖r k‖ ≤ A*sixthLatticeWeight k := by
    intro k
    by_cases hk : k=0
    · simp only [r,hk,if_pos rfl,norm_zero]
      exact mul_nonneg hA (sixthLatticeWeight_nonneg 0)
    · simpa [r,hk] using hb k hk
  have hmaj := sixthLatticeWeight_summable.mul_left A
  have hn : Summable fun k : ℤ => ‖r k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmaj
  have hsum : periodize g T x-g x=∑' k : ℤ,r k := by
    have heq := hs.tsum_eq_add_tsum_ite 0
    simp only [Int.cast_zero,mul_zero,Complex.ofReal_zero,add_zero] at heq
    have hre : (fun k : ℤ => if k=0 then 0 else g ((x:ℂ)+((T*(k:ℝ):ℝ):ℂ)))=r := by
      funext k
      simp [r]
    rw [hre] at heq
    exact eq_sub_iff_add_eq.mpr (by simpa [periodize,add_comm] using heq.symm) |>.symm
  rw [hsum]
  calc
    _ ≤ ∑' k : ℤ,‖r k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℤ,A*sixthLatticeWeight k :=
      Summable.tsum_le_tsum hbound hn hmaj
    _ = _ := tsum_mul_left

theorem windowed_periodize_error {f : ℂ → ℂ} {α τ T H K σ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H)
    (hg : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|))
    (x : ℝ) (hx : |x| ≤ T/2) :
    ‖periodize (fun z => f z*plateauWindow α τ z) T x-
      f x*plateauWindow α τ x‖ ≤ plateauPeriodError α τ T H := by
  unfold plateauPeriodError
  apply periodize_error_of_real_majorant _ T x
    ((2*H*α*τ)*(2/(α*(T/2-τ)))^6) (by positivity)
  · exact periodize_summable _
      (C := K*(2*α*τ*((2/min 1 α)*(1+τ))^6)) (σ := σ+6*α)
      (by positivity) (by positivity) (show 0 < T by linarith)
      (mul_plateauWindow_decay hα hτ hK hg) (x : ℂ)
  · intro k hk
    simpa only [Complex.ofReal_add,Complex.ofReal_mul] using
      windowed_translate_bound hα hτ hgap hH hf x hx k hk

theorem windowed_periodize_center_bound {f : ℂ → ℂ} {α τ T H K σ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H)
    (hg : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|))
    (x : ℝ) (hx : |x| ≤ T/2) :
    ‖periodize (fun z => f z*plateauWindow α τ z) T x‖ ≤
      H*(2*Real.pi)+plateauPeriodError α τ T H := by
  have he := windowed_periodize_error hα hτ hgap hH hK hσ hf hg x hx
  have hz : ‖f x*plateauWindow α τ x‖ ≤ H*(2*Real.pi) := by
    rw [norm_mul]
    exact mul_le_mul (hf x) (norm_plateauWindow_real_le hα.le hτ x) (norm_nonneg _) hH
  exact (norm_le_norm_sub_add _ _).trans (by linarith)

theorem periodic_real_bound_of_center {F : ℂ → ℂ} {T B : ℝ}
    (hT : 0 < T) (hp : Function.Periodic F (T : ℂ))
    (hb : ∀ x : ℝ, |x| ≤ T/2 → ‖F x‖ ≤ B) : ∀ x : ℝ, ‖F x‖ ≤ B := by
  intro x
  let k : ℤ := ⌊(x+T/2)/T⌋
  let y : ℝ := x-(k:ℝ)*T
  have hklo : (k:ℝ)*T ≤ x+T/2 :=
    (le_div_iff₀ hT).mp (Int.floor_le ((x+T/2)/T))
  have hkhi : x+T/2 < ((k:ℝ)+1)*T :=
    (div_lt_iff₀ hT).mp (Int.lt_floor_add_one ((x+T/2)/T))
  have hy : |y| ≤ T/2 := abs_le.mpr ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩
  have he : F (y : ℂ)=F x := by
    dsimp [y]
    push_cast
    exact hp.sub_int_mul_eq k
  rw [← he]
  exact hb y hy

theorem windowed_periodize_bound {f : ℂ → ℂ} {α τ T H K σ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H)
    (hg : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|)) :
    ∀ x : ℝ, ‖periodize (fun z => f z*plateauWindow α τ z) T x‖ ≤
      H*(2*Real.pi)+plateauPeriodError α τ T H :=
  periodic_real_bound_of_center (by linarith) (periodize_periodic _ T)
    (windowed_periodize_center_bound hα hτ hgap hH hK hσ hf hg)

/-- Dividing the desired labels by the strictly positive plateau keeps the
input data in the unit ball after one uniform scaling. -/
theorem window_division_data {ρ r d : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r) (hd : |d| ≤ 1) :
    |ρ*d/r| ≤ 1 := by
  have hr0 : 0 < r := hρ.trans_le hr
  rw [abs_div, abs_mul, abs_of_pos hρ, abs_of_pos hr0]
  apply (div_le_iff₀ hr0).mpr
  nlinarith

theorem plateauPeriodError_scaled {α β r H : ℝ} (hα : α ≠ 0)
    (hβ : 1-β ≠ 0) (hr : r ≠ 0) :
    plateauPeriodError α (β*r) (2*r) H =
      (128*H*β*(∑' k : ℤ,sixthLatticeWeight k)/(α^5*(1-β)^6))/r^5 := by
  unfold plateauPeriodError
  have hd : α*(2*r/2-β*r)=α*(1-β)*r := by ring
  rw [hd]
  field_simp
  ring

/-- A fixed fractional gap between the nodes and the period seam makes the
uniform real-axis error arbitrarily small. -/
theorem exists_large_plateauPeriodError {α β H q : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) (hH : 0 ≤ H) (hq : 0 < q) :
    ∃ R ≥ (1 : ℝ), ∀ r ≥ R, plateauPeriodError α (β*r) (2*r) H ≤ q := by
  let A := 128*H*β*(∑' k : ℤ,sixthLatticeWeight k)/(α^5*(1-β)^6)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg (by positivity) (tsum_nonneg sixthLatticeWeight_nonneg))
      (by positivity)
  refine ⟨max 1 (A/q), le_max_left _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hAr : A ≤ q*r := by
    have hh : A/q ≤ r := (le_max_right _ _).trans hr
    exact (div_le_iff₀ hq).mp hh |>.trans_eq (mul_comm _ _)
  have hrpow : r ≤ r^5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hr1 4]
  rw [plateauPeriodError_scaled hα.ne' (by linarith : 1-β ≠ 0) hr0.ne']
  change A/r^5 ≤ q
  exact (div_le_iff₀ (by positivity : 0 < r^5)).mpr
    (hAr.trans (mul_le_mul_of_nonneg_left hrpow hq.le))

theorem exists_window_data_interpolant {ι : Type*} {α τ ρ σ H : ℝ}
    (node : ι → ℝ) (hρ : 0 < ρ)
    (hwin : ∀ i, ρ ≤ plateauWindowReal α τ (node i))
    (hinterp : ∀ d : ι → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ, IsBernsteinFunction σ H f ∧ ∀ i, f (node i)=(d i : ℂ))
    (d : ι → ℝ) (hd : ∀ i, |d i| ≤ 1) :
    ∃ f : ℂ → ℂ, IsBernsteinFunction σ (H/ρ) f ∧
      (∀ x : ℝ, (f x).im=0) ∧
      ∀ i, f (node i)*plateauWindow α τ (node i)=(d i : ℂ) := by
  obtain ⟨f,hf,hfi⟩ := hinterp (fun i => ρ*d i/plateauWindowReal α τ (node i))
    (fun i => window_division_data hρ (hwin i) (hd i))
  let f₀ := bernsteinRealification f
  have hf₀ : IsBernsteinFunction σ H f₀ := hf.realification
  obtain ⟨hent,hreal,K,hK,hgrowth⟩ := hf₀
  refine ⟨fun z => f₀ z/(ρ:ℂ), ⟨hent.div_const _, ?_, K/ρ, by positivity, ?_⟩, ?_, ?_⟩
  · intro x
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact div_le_div_of_nonneg_right (hreal x) hρ.le
  · intro z
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact (div_le_div_of_nonneg_right (hgrowth z) hρ.le).trans_eq (by ring)
  · intro x
    dsimp only
    have hr : f₀ x=((f x).re : ℂ) := bernsteinRealification_real _ _
    rw [hr, ← Complex.ofReal_div]
    simp
  · intro i
    dsimp only
    have hi : f₀ (node i)=(ρ*d i/plateauWindowReal α τ (node i) : ℝ) :=
      bernsteinRealification_real_value (hfi i)
    have hw : plateauWindowReal α τ (node i) ≠ 0 := ne_of_gt (hρ.trans_le (hwin i))
    rw [hi, plateauWindow_real, ← Complex.ofReal_div, ← Complex.ofReal_mul]
    congr 1
    field_simp

/-- Bounded entire interpolation yields a uniformly bounded approximate
trigonometric interpolant. The error and norm are independent of the complex
growth prefactor selected by the original interpolant. -/
theorem entire_interpolation_gives_approx_trig {ι : Type*} [Fintype ι]
    (node : ι → ℝ) {α τ T H ρ σ q : ℝ} {m : ℕ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2)
    (hH : 0 ≤ H) (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hq : 0 ≤ q)
    (hnodes : ∀ i, |node i| ≤ τ)
    (hwin : ∀ i, ρ ≤ plateauWindowReal α τ (node i))
    (hm : periodizationBandwidth (σ+6*α) T ≤ m)
    (herror : plateauPeriodError α τ T (H/ρ) ≤ q)
    (hinterp : ∀ d : ι → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ, IsBernsteinFunction σ H f ∧ ∀ i, f (node i)=(d i : ℂ))
    (d : ι → ℝ) (hd : ‖d‖ ≤ 1) :
    ∃ P : CircleFunction, P ∈ bandSpace m ∧
      (∀ u : FourierCircle, (P u).im=0) ∧
      ‖P‖ ≤ (H/ρ)*(2*Real.pi)+q ∧
      ∀ i, |(P ((2*Real.pi*node i/T : ℝ) : FourierCircle)).re-d i| ≤ q := by
  have hd' : ∀ i, |d i| ≤ 1 := by
    intro i
    have hh := norm_le_pi_norm d i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hd
  obtain ⟨f,hf,hfr,hfi⟩ := exists_window_data_interpolant node hρ hwin hinterp d hd'
  obtain ⟨hfd,hfb,K,hK,hfg⟩ := hf
  have hT : 0 < T := by linarith
  have hHp : 0 ≤ H/ρ := div_nonneg hH hρ.le
  let G : ℂ → ℂ := fun z => f z*plateauWindow α τ z
  let C : ℝ := K*(2*α*τ*((2/min 1 α)*(1+τ))^6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hGd : Differentiable ℂ G := hfd.mul (differentiable_plateauWindow α τ)
  have hGg : ∀ z : ℂ, ‖G z‖ ≤ C*Real.exp ((σ+6*α)*|z.im|)/(1+‖z‖)^6 :=
    mul_plateauWindow_decay hα hτ hK.le hfg
  have hGr : ∀ x : ℝ, (G x).im=0 := by
    intro x
    dsimp [G]
    rw [plateauWindow_real,Complex.mul_im,hfr]
    simp
  obtain ⟨P,hPb,hPe⟩ := periodize_circle_of_bandwidth_le G hGd hC
    (by positivity) hT hGg hm
  refine ⟨P,hPb,?_,?_,?_⟩
  · intro u
    obtain ⟨x,rfl⟩ := normalized_circle_surjective hT.ne' u
    rw [hPe]
    exact periodize_real G hGr hC (by positivity) hT hGg x
  · apply circle_norm_le_of_physical hT.ne' (by positivity)
    intro x
    rw [hPe]
    exact (windowed_periodize_bound hα hτ hgap hHp hK.le hσ hfb hfg x).trans
      (add_le_add_right herror _)
  · intro i
    have hi := windowed_periodize_error hα hτ hgap hHp hK.le hσ hfb hfg (node i)
      ((hnodes i).trans hgap.le)
    rw [hfi i] at hi
    have hci : ‖P ((2*Real.pi*node i/T : ℝ) : FourierCircle)-(d i : ℂ)‖ ≤ q := by
      rw [hPe]
      exact hi.trans herror
    simpa only [Complex.sub_re,Complex.ofReal_re] using
      (Complex.abs_re_le_norm (P ((2*Real.pi*node i/T : ℝ) : FourierCircle)-(d i : ℂ))).trans hci

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.ObstructionAssembly ===== -/
section

noncomputable section
open Set
open OMA.Port1.E1152

namespace OMA.Port1.E1133

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- Full finite trigonometric obstruction; the data are independent of the
allowed degree. This is the common interface between the two analytic halves. -/
def TrigObstructionAt (A δ : ℝ) (n : ℕ) : Prop :=
  ∀ Γ : Finset ℝ, (∀ x ∈ Γ, x ∈ Ico (-(n : ℝ)) n) → Γ.card = 2*n →
    ∃ y : ℝ → ℝ, (∀ x ∈ Γ, |y x| ≤ 1) ∧
      ∀ m : ℕ, n ≤ m → (m : ℝ) ≤ n+δ*n →
        ∀ P : CircleFunction, P ∈ bandSpace m → (∀ u, (P u).im=0) →
          ‖P‖ ≤ A → ∃ x ∈ Γ, (P ((Real.pi*x/n : ℝ) : FourierCircle)).re ≠ y x

def FiniteTrigObstructions : Prop :=
  ∀ A > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → TrigObstructionAt A δ n

/-- Exact assembly of the contradiction. Both analytic inputs remain named
hypotheses here and are discharged by the final theorem, not asserted as axioms. -/
theorem centered_obstruction_of_trig_and_approx
    {H A δ τ K q : ℝ} {n m : ℕ}
    (hτ : 0 < τ) (hτn : τ < (n : ℝ))
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hq1 : q < 1) (hKA : K/(1-q) ≤ A)
    (hNm : n ≤ m) (hm : (m : ℝ) ≤ n+δ*n)
    (htrig : TrigObstructionAt A δ n)
    (happrox : ∀ t : Fin (2*n) → ℝ, Function.Injective t →
      (∀ i, t i ∈ Icc (-τ) τ) →
      (∀ d : Fin (2*n) → ℝ, (∀ i, |d i| ≤ 1) →
        ∃ f : ℂ → ℂ,
          IsBernsteinFunction (Real.pi*((((2*n : ℕ) : ℝ)+1)/(2*τ))) H f ∧
          ∀ i, f (t i)=(d i : ℂ)) →
      ∀ d : Fin (2*n) → ℝ, ‖d‖ ≤ 1 →
        ∃ P : CircleFunction, P ∈ bandSpace m ∧ (∀ u, (P u).im=0) ∧
          ‖P‖ ≤ K ∧ ∀ i, |(P ((Real.pi*t i/n : ℝ) : FourierCircle)).re-d i| ≤ q) :
    CenteredIntervalRealBernsteinObstruction H (2*n) (2*τ) := by
  classical
  intro t ht hloc
  have htloc : ∀ i, t i ∈ Icc (-τ) τ := by
    intro i
    obtain ⟨hl,hu⟩ := hloc i
    constructor <;> linarith
  by_contra hno
  push Not at hno
  have hinterp : ∀ d : Fin (2*n) → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ,
        IsBernsteinFunction (Real.pi*((((2*n : ℕ) : ℝ)+1)/(2*τ))) H f ∧
        ∀ i, f (t i)=(d i : ℂ) := by
    intro d hd
    obtain ⟨f,hf,hfr,hfi⟩ := hno (fun i => ⟨d i,abs_le.mp (hd i)⟩)
    exact ⟨f,hf,hfi⟩
  let Γ : Finset ℝ := Finset.univ.image t
  have hΓcard : Γ.card = 2*n := by
    simp [Γ,Finset.card_image_of_injective _ ht]
  have hΓloc : ∀ x ∈ Γ, x ∈ Ico (-(n : ℝ)) n := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hil,hir⟩ := htloc i
    constructor <;> linarith
  obtain ⟨y,hy,hybad⟩ := htrig Γ hΓloc hΓcard
  let d : Fin (2*n) → ℝ := fun i => y (t i)
  have hd : ‖d‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    exact hy (t i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  obtain ⟨P,hPb,hPr,hPd,hPK⟩ := exact_unit_real_trig_interpolation
    (fun i : Fin (2*n) => ((Real.pi*t i/n : ℝ) : FourierCircle))
    m K q hK hq hq1 (happrox t ht htloc hinterp) d hd
  obtain ⟨x,hx,hbad⟩ := hybad m hNm hm P hPb hPr (hPK.trans hKA)
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  apply hbad
  exact congrArg Complex.re (hPd i)

/-- Every parameter in the window argument is chosen here. In particular the
window constants are fixed before the degree slack, avoiding a circular choice. -/
theorem finiteBernsteinObstructions_of_finiteTrig
    (htrig : FiniteTrigObstructions) :
    ∀ H > (0 : ℝ), ∃ k : ℕ, 2 ≤ k ∧ FiniteBernsteinObstruction H k := by
  intro H hH
  obtain ⟨η,hη,hwindow⟩ := plateauWindow_uniform_positive
  let ρ : ℝ := η/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let K : ℝ := (H/ρ)*(2*Real.pi)+1/2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨δ,hδ,n₀,hfinite⟩ := htrig (2*K) (by positivity)
  let β := interiorRatio δ
  let α := plateauRate δ
  have hβ : 0 < β := interiorRatio_pos hδ
  have hβ1 : β < 1 := interiorRatio_lt_one hδ
  have hα : 0 < α := plateauRate_pos hδ
  obtain ⟨R,hR1,hR⟩ := exists_large_plateauPeriodError
    (H := H/ρ) hα hβ.le hβ1 (by positivity) (show (0 : ℝ) < 1/2 by norm_num)
  obtain ⟨n,hn⟩ := exists_nat_gt
    (max 1 (max R (max (η/(α*β)) (max ((4+δ)/δ) (n₀ : ℝ)))))
  have hbounds : (1 : ℝ) ≤ n ∧ R ≤ n ∧ η/(α*β) ≤ n ∧
      (4+δ)/δ ≤ n ∧ (n₀ : ℝ) ≤ n := by
    simpa only [max_le_iff] using hn.le
  obtain ⟨hn1,hnR,hnη,hnδ,hn₀⟩ := hbounds
  have hnpos : (0 : ℝ) < n := by linarith
  have hnNat : 0 < n := by exact_mod_cast hnpos
  let τ : ℝ := β*n
  have hτ : 0 < τ := mul_pos hβ hnpos
  have hτn : τ < n := by
    dsimp [τ]
    nlinarith
  have hητ : η ≤ α*τ := by
    have hh := (div_le_iff₀ (mul_pos hα hβ)).mp hnη
    dsimp [τ]
    nlinarith
  let σ := compressedType δ n
  have hσ : 0 ≤ σ := Real.pi_pos.le.trans (compressedType_bounds hδ hnδ).1
  let m := periodizationBandwidth (σ+6*α) (2*(n : ℝ))
  have hm : n ≤ m ∧ (m : ℝ) ≤ n+δ*n := compressed_bandwidth_budget hδ hnδ
  refine ⟨2*n, by omega, ?_⟩
  apply finiteObstruction_of_centered_interval_real (L := 2*τ) (by positivity)
  apply centered_obstruction_of_trig_and_approx (A := 2*K) (δ := δ)
    (K := K) (q := 1/2) (m := m) hτ hτn hK.le (by norm_num) (by norm_num)
    (by norm_num; ring_nf; rfl) hm.1 hm.2 (hfinite n (by exact_mod_cast hn₀))
  intro t ht hloc hinterp d hd
  have hσeq : Real.pi*((((2*n : ℕ) : ℝ)+1)/(2*τ)) = σ := by
    dsimp [σ,compressedType,τ,β]
    ring
  have hinterp' : ∀ d : Fin (2*n) → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ, IsBernsteinFunction σ H f ∧ ∀ i, f (t i)=(d i : ℂ) := by
    simpa only [hσeq] using hinterp
  have hnloc : ∀ i, |t i| ≤ τ := fun i => abs_le.mpr (hloc i)
  have hwin : ∀ i, ρ ≤ plateauWindowReal α τ (t i) := by
    intro i
    exact hwindow α τ (t i) hα.le hητ (hnloc i)
  have herror : plateauPeriodError α τ (2*(n : ℝ)) (H/ρ) ≤ 1/2 := hR n hnR
  obtain ⟨P,hPb,hPr,hPK,hPe⟩ := entire_interpolation_gives_approx_trig
    t hα hτ.le (show τ < 2*(n : ℝ)/2 by linarith) hH.le hρ hσ
    (show (0 : ℝ) ≤ 1/2 by norm_num) hnloc hwin (le_refl m) herror hinterp' d hd
  refine ⟨P,hPb,hPr,hPK,?_⟩
  intro i
  convert hPe i using 1 <;> congr 2 <;> ring

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.AngularBins ===== -/
section

noncomputable section
open Set
namespace OMA.Port1.E1133

def binCount (D L : ℝ) : ℕ := ⌊D / L⌋₊ + 1

theorem binCount_le {D L : ℝ} (hD : 0 ≤ D) (hL : 0 < L) :
    (binCount D L : ℝ) ≤ D / L + 1 := by
  simp only [binCount, Nat.cast_add, Nat.cast_one]
  simpa only [add_comm] using add_le_add_right (Nat.floor_le (div_nonneg hD hL.le)) 1

def angularBin {D L : ℝ} (hL : 0 < L) (t : Icc 0 D) : Fin (binCount D L) :=
  ⟨⌊(t : ℝ) / L⌋₊, Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right t.property.2 hL.le))⟩

theorem angularBin_bounds {D L : ℝ} (hL : 0 < L) (t : Icc 0 D) :
    (t : ℝ) ∈ Icc ((angularBin hL t).val * L) (((angularBin hL t).val + 1) * L) := by
  have ht0 : 0 ≤ (t : ℝ) / L := div_nonneg t.property.1 hL.le
  constructor
  · apply (le_div_iff₀ hL).mp
    exact Nat.floor_le ht0
  · apply le_of_lt
    apply (div_lt_iff₀ hL).mp
    exact Nat.lt_floor_add_one _

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.Grouping ===== -/
section

/-!
Finite grouping of indexed samples. Coincident sample locations remain
distinct indices: no injectivity assumption on a later node map is used.
-/

noncomputable section
open scoped BigOperators

namespace OMA.Port1.E1133

variable {α : Type*} [DecidableEq α]

/-- Split a finite set into disjoint `k`-element groups, discarding fewer than `k`
indices. The groups are actual subsets of the original index set. -/
theorem exists_disjoint_equal_groups (s : Finset α) (k : ℕ) (hk : 0 < k) :
    ∃ G : Finset (Finset α),
      (∀ g ∈ G, g ⊆ s ∧ g.card = k) ∧
      (G : Set (Finset α)).Pairwise Disjoint ∧ s.card ≤ k * G.card + (k - 1) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hsmall : s.card < k
    · refine ⟨∅, by simp, by simp, ?_⟩
      simp only [Finset.card_empty, mul_zero, zero_add]
      omega
    · have hks : k ≤ s.card := Nat.le_of_not_gt hsmall
      obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hks
      have htpos : 0 < t.card := by omega
      have htnonempty : t.Nonempty := Finset.card_pos.mp htpos
      have hstrict : s \ t ⊂ s := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨a, ha⟩ := htnonempty
        have hmem : a ∈ s \ t := heq.symm ▸ hts ha
        exact (Finset.mem_sdiff.mp hmem).2 ha
      obtain ⟨G, hG, hdis, hbudget⟩ := ih (s \ t) hstrict
      have htG : t ∉ G := by
        intro ht
        obtain ⟨a, ha⟩ := htnonempty
        exact (Finset.mem_sdiff.mp ((hG t ht).1 ha)).2 ha
      refine ⟨insert t G, ?_, ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact ⟨hts, htcard⟩
        · exact ⟨(hG g hg).1.trans Finset.sdiff_subset, (hG g hg).2⟩
      · intro g hg h hh hgh
        by_cases hgt : g = t
        · subst g
          have hhG : h ∈ G := (Finset.mem_insert.mp hh).resolve_left hgh.symm
          apply Finset.disjoint_left.mpr
          intro a hat hah
          exact (Finset.mem_sdiff.mp ((hG h hhG).1 hah)).2 hat
        · have hgG : g ∈ G := (Finset.mem_insert.mp hg).resolve_left hgt
          by_cases hht : h = t
          · subst h
            apply Finset.disjoint_left.mpr
            intro a hag hat
            exact (Finset.mem_sdiff.mp ((hG g hgG).1 hag)).2 hat
          · have hhG : h ∈ G := (Finset.mem_insert.mp hh).resolve_left hht
            exact hdis hgG hhG hgh
      · rw [Finset.card_insert_of_notMem htG]
        have hcard : (s \ t).card = s.card - k := by
          rw [Finset.card_sdiff_of_subset hts, htcard]
        rw [hcard] at hbudget
        nlinarith [Nat.sub_add_cancel hks]

/-- A group containing only one bin cannot also belong to a different bin's
family, because all groups have positive size. -/
theorem exists_grouping_by_bins {β : Type*} [Fintype β] [DecidableEq β]
    (s : Finset α) (b : α → β) (k : ℕ) (hk : 0 < k) :
    ∃ G : Finset (Finset α),
      (∀ g ∈ G, g ⊆ s ∧ g.card = k ∧ ∃ j : β, ∀ a ∈ g, b a = j) ∧
      (G : Set (Finset α)).Pairwise Disjoint ∧
      s.card ≤ k * G.card + (k - 1) * Fintype.card β := by
  classical
  have hex (j : β) := exists_disjoint_equal_groups (s.filter fun a => b a = j) k hk
  choose G hG hdis hbudget using hex
  have hmono (j : β) (g : Finset α) (hg : g ∈ G j) :
      g ⊆ s ∧ g.card = k ∧ ∀ a ∈ g, b a = j := by
    refine ⟨(hG j g hg).1.trans (Finset.filter_subset _ _), (hG j g hg).2, ?_⟩
    exact fun a ha => (Finset.mem_filter.mp ((hG j g hg).1 ha)).2
  have hcross (i j : β) (hij : i ≠ j) (g : Finset α) (hg : g ∈ G i)
      (h : Finset α) (hh : h ∈ G j) : Disjoint g h := by
    apply Finset.disjoint_left.mpr
    intro a hag hah
    exact hij (((hmono i g hg).2.2 a hag).symm.trans ((hmono j h hh).2.2 a hah))
  have hfamily : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint G := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    have hgcard := (hmono i g hgi).2.1
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < g.card by omega)
    exact Finset.disjoint_left.mp (hcross i j hij g hgi g hgj) ha ha
  let groups := Finset.univ.biUnion G
  have hgroupscard : groups.card = ∑ j, (G j).card := by
    exact Finset.card_biUnion hfamily
  refine ⟨groups, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨hgs, hgcard, hjg⟩ := hmono j g hgj
    exact ⟨hgs, hgcard, j, hjg⟩
  · intro g hg h hh hgh
    obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨j, hj, hhj⟩ := Finset.mem_biUnion.mp hh
    by_cases hij : i = j
    · subst j
      exact hdis i hgi hhj hgh
    · exact hcross i j hij g hgi h hhj
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbudget j)
    have hpartition : (∑ j : β, (s.filter fun a => b a = j).card) = s.card := by
      have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := Finset.univ)
        (f := b) (by simp)
      exact h.symm
    rw [hpartition, Finset.sum_add_distrib, ← Finset.mul_sum, ← hgroupscard] at hsum
    simpa [mul_comm] using hsum

/-- Independently selected local data on disjoint groups define one global
label vector, before any approximating polynomial is considered. -/
theorem glue_group_labels (G : Finset (Finset α))
    (hdis : (G : Set (Finset α)).Pairwise Disjoint)
    (a : Finset α → α → ℝ) (ha : ∀ g ∈ G, ∀ i ∈ g, |a g i| ≤ 1) :
    ∃ y : α → ℝ, (∀ i, |y i| ≤ 1) ∧ ∀ g ∈ G, ∀ i ∈ g, y i = a g i := by
  classical
  let occurs (i : α) : Prop := ∃ g ∈ G, i ∈ g
  let y (i : α) : ℝ := if hi : occurs i then a (Classical.choose hi) i else 0
  have hchoice (i : α) (hi : occurs i) :
      Classical.choose hi ∈ G ∧ i ∈ Classical.choose hi := Classical.choose_spec hi
  refine ⟨y, ?_, ?_⟩
  · intro i
    by_cases hi : occurs i
    · dsimp [y]
      rw [dif_pos hi]
      exact ha _ (hchoice i hi).1 i (hchoice i hi).2
    · simp [y, hi]
  · intro g hg i hi
    have hocc : occurs i := ⟨g, hg, hi⟩
    have hchosen : Classical.choose hocc = g := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdis (hchoice i hocc).1 hg hne)
        (hchoice i hocc).2 hi
    dsimp [y]
    rw [dif_pos hocc, hchosen]

/-- One error in every disjoint group forces at least as many erroneous indices
as there are groups. This counts indices even when their sample locations agree. -/
theorem groups_force_errors (s : Finset α) (G : Finset (Finset α))
    (hinside : ∀ g ∈ G, g ⊆ s) (hdis : (G : Set (Finset α)).Pairwise Disjoint)
    (Bad : α → Prop) [DecidablePred Bad]
    (hbad : ∀ g ∈ G, ∃ i ∈ g, Bad i) : G.card ≤ (s.filter Bad).card := by
  classical
  choose a ha hBa using fun g : G => hbad g.val g.property
  let f : G → (s.filter Bad) := fun g =>
    ⟨a g, Finset.mem_filter.mpr ⟨hinside g.val g.property (ha g), hBa g⟩⟩
  have hf : Function.Injective f := by
    intro g h heq
    apply Subtype.ext
    by_contra hgh
    have hai : a g = a h := congrArg Subtype.val heq
    exact Finset.disjoint_left.mp (hdis g.property h.property hgh) (ha g) (hai ▸ ha h)
  simpa using Fintype.card_le_of_injective f hf

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.Budget ===== -/
section

noncomputable section
namespace OMA.Port1.E1133

/-- One parameter controls both the degree surplus and the allowed errors. -/
def obstructionEpsilon (k : ℕ) : ℝ := 1 / (8 * (k : ℝ)^2)

theorem obstructionEpsilon_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < obstructionEpsilon k := by
  unfold obstructionEpsilon
  have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  positivity

/-- The exact elementary estimate used after partitioning the angular interval. -/
theorem robust_group_budget {k n q : ℕ} (hk : 2 ≤ k) (hn : 4*k^2 ≤ n)
    (hgroup : (n : ℝ) / k - ((1 + obstructionEpsilon k) * n) / (k + 1) - 1 ≤ q) :
    obstructionEpsilon k * n < q := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (4 : ℝ) * (k : ℝ)^2 ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have heq : (n : ℝ) / k - ((1 + obstructionEpsilon k) * n) / (k + 1) - 1 -
      obstructionEpsilon k * n =
      (n : ℝ) * (7*(k : ℝ)-2) / (8*(k : ℝ)^2*((k : ℝ)+1)) - 1 := by
    unfold obstructionEpsilon
    field_simp
    ring
  have hcoef : (1 : ℝ) / (2*(k : ℝ)^2) ≤
      (7*(k : ℝ)-2) / (8*(k : ℝ)^2*((k : ℝ)+1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos hk0]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcoef hn0
  have hlarge : (2 : ℝ) ≤ (n : ℝ) / (2*(k : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he : (1 : ℝ) ≤ (n : ℝ) / k -
      ((1 + obstructionEpsilon k) * n) / (k + 1) - 1 - obstructionEpsilon k * n := by
    rw [heq]
    simp only [← mul_div_assoc, mul_one] at hmul
    linarith
  linarith

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.Reduction ===== -/
section

noncomputable section
open Set Filter
namespace OMA.Port1.E1133

/-- The complete finite reduction. The analytic obstruction is displayed as
an assumption of this intermediate theorem; it is not an axiom. -/
theorem robust_labels_of_finite_obstruction {C : ℝ} {k n : ℕ}
    (hk : 2 ≤ k) (hn : 4*k^2 ≤ n) (hcore : FiniteBernsteinObstruction C k)
    (x : Fin n → Icc (-1 : ℝ) 1) :
    ∃ y : Fin n → Icc (-1 : ℝ) 1,
      ∀ P : Polynomial ℝ, (P.natDegree : ℝ) < (1 + obstructionEpsilon k) * (n : ℝ) →
      ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) ≥
        (1 - obstructionEpsilon k) * (n : ℝ) →
      ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C := by
  classical
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hn0 : 0 < n := by nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let D : ℝ := (1 + obstructionEpsilon k) * n
  have hD : 0 < D := mul_pos (by linarith [obstructionEpsilon_pos hk]) hnR
  let N := binCount D ((k : ℝ) + 1)
  have hL : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  let t : Fin n → Icc 0 D := fun i => ⟨angularNode D (x i), angularNode_mem hD.le (x i)⟩
  let b : Fin n → Fin N := fun i => angularBin hL (t i)
  obtain ⟨G,hG,hdis,hcount⟩ := exists_grouping_by_bins Finset.univ b k hk0
  have hcount' : n ≤ k * G.card + k * N := by
    have hh : n ≤ k * G.card + (k-1) * N := by simpa using hcount
    exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_right N (Nat.sub_le k 1)) _)
  have hq : obstructionEpsilon k * (n : ℝ) < G.card := by
    apply robust_group_budget hk hn
    have hbN : (N : ℝ) ≤ D / ((k : ℝ) + 1) + 1 := binCount_le hD.le hL
    have hc : (n : ℝ) ≤ (k : ℝ) * G.card + (k : ℝ) * N := by exact_mod_cast hcount'
    have hd : (n : ℝ) / k ≤ (G.card : ℝ) + N := by
      apply (div_le_iff₀ hkR).mpr
      nlinarith
    dsimp only [D] at hbN
    linarith
  have hlab (g : G) : ∃ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) ∧
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi C f →
        ∃ i ∈ g.val, f (t i) ≠ (a i : ℂ) := by
    obtain ⟨hgs,hgcard,j,hj⟩ := hG g.val g.property
    apply finiteObstruction_group hcore g.val hgcard (fun i => (t i : ℝ)) (j.val * ((k : ℝ)+1))
    intro i hi
    have hb := angularBin_bounds hL (t i)
    have hij : angularBin hL (t i) = j := hj i hi
    rw [hij] at hb
    convert hb using 1 <;> ring
  choose a ha hbad using hlab
  let a' : Finset (Fin n) → Fin n → ℝ := fun g i =>
    if hg : g ∈ G then a ⟨g,hg⟩ i else 0
  obtain ⟨y,hy,hyg⟩ := glue_group_labels G hdis a' (by
    intro g hg i hi
    simpa [a',hg] using ha ⟨g,hg⟩ i)
  refine ⟨fun i => ⟨y i, abs_le.mp (hy i)⟩, ?_⟩
  intro P hdeg hfit
  by_contra hno
  have hbounded : BoundedOnSegment C P := by
    intro z hz
    exact le_of_not_gt (fun h => hno ⟨z,hz,h⟩)
  have hPB := polynomialPullback_isBernstein hD P hdeg.le hbounded
  have herr : G.card ≤ (Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card := by
    apply groups_force_errors Finset.univ G (fun _ _ => Finset.subset_univ _) hdis
    intro g hg
    obtain ⟨i,hi,hne⟩ := hbad ⟨g,hg⟩ (polynomialPullback D P) hPB
    refine ⟨i,hi,?_⟩
    have hval : y i = a ⟨g,hg⟩ i := by simpa [a',hg] using hyg g hg i hi
    have heval := polynomialPullback_at_node hD P (x i)
    change polynomialPullback D P (angularNode D (x i)) ≠ _ at hne
    rw [heval] at hne
    intro he
    apply hne
    exact congrArg (fun r : ℝ => (r : ℂ)) (he.trans hval)
  have hpartition :
      (Finset.univ.filter (fun i => P.eval (x i : ℝ) = y i)).card +
      (Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card = n := by
    simpa using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => P.eval (x i : ℝ) = y i)
  have hpartitionR :
      ((Finset.univ.filter (fun i => P.eval (x i : ℝ) = y i)).card : ℝ) +
      ((Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card : ℝ) = n := by
    exact_mod_cast hpartition
  have herrR : (G.card : ℝ) ≤
      (Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card := by exact_mod_cast herr
  change ((Finset.univ.filter (fun i => P.eval (x i : ℝ) = y i)).card : ℝ) ≥ _ at hfit
  nlinarith

theorem robustInterpolation_of_finiteObstructions
    (hcore : ∀ C > (0 : ℝ), ∃ k : ℕ, 2 ≤ k ∧ FiniteBernsteinObstruction C k) :
    RobustInterpolation := by
  intro C hC
  obtain ⟨k,hk,hkcore⟩ := hcore C hC
  refine ⟨obstructionEpsilon k, obstructionEpsilon_pos hk, ?_⟩
  filter_upwards [eventually_ge_atTop (4*k^2)] with n hn
  exact robust_labels_of_finite_obstruction hk hn hkcore

end OMA.Port1.E1133
end
end

/- ===== OMA.Port1.E1133.Main ===== -/
section

noncomputable section
open Filter Set

namespace OMA.Port1.E1133

/-- The finite analytic input is proved, with no unresolved interpolation or
sampling assumptions. Indexed nodes may coincide. -/
theorem finite_bernstein_obstruction :
    ∀ H > (0 : ℝ), ∃ k : ℕ, 2 ≤ k ∧ FiniteBernsteinObstruction H k :=
  finiteBernsteinObstructions_of_finiteTrig finite_trig_obstruction

/-- The affirmative answer to the complete robust interpolation question. -/
theorem erdos_1133 :
    ∀ C > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ x : Fin n → Icc (-1 : ℝ) 1,
        ∃ y : Fin n → Icc (-1 : ℝ) 1,
          ∀ P : Polynomial ℝ,
            (P.natDegree : ℝ) < (1+ε)*(n : ℝ) →
            ((Finset.univ.filter (fun i => P.eval (x i : ℝ)=(y i : ℝ))).card : ℝ) ≥
              (1-ε)*(n : ℝ) →
            ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C :=
  robustInterpolation_of_finiteObstructions finite_bernstein_obstruction

end OMA.Port1.E1133
end
end

theorem OMA.solution : type_of% @Erdos1133.erdos_1133 := by
  exact OMA.Port1.E1133.erdos_1133
