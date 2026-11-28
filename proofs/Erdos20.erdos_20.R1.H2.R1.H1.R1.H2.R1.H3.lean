import OMAReductions.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Log
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
theorem ite_eq_left_of_eq_true {α : Sort*} {c : Prop} [Decidable c] (a b : α) (h : c = True) :
    (if c then a else b) = a := by
  subst h
  exact if_pos trivial
theorem ite_eq_right {c : Prop} {h : Decidable c} {α : Sort*} {t e : α} (hnc : ¬ c) :
    ite c t e = e := if_neg hnc
theorem ite_eq_left {c : Prop} {h : Decidable c} {α : Sort*} {t e : α} (hc : c) :
    ite c t e = t := if_pos hc
theorem Finset.sum_sq_eq_zero_iff {ι R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {s : Finset ι} {f : ι → R} : ∑ i ∈ s, f i ^ 2 = 0 ↔ ∀ i ∈ s, f i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))]
  simp
namespace OAI
open scoped BigOperators
namespace MatrixMultiplication.Foundation
abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K
namespace Tensor
section Algebra
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]
def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z
def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2
variable [Fintype X] [Fintype Y] [Fintype Z]
end Algebra
section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]
def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)
end Pullback
end Tensor
end MatrixMultiplication.Foundation
end OAI
namespace OAI
open scoped BigOperators
namespace MatrixMultiplication.Foundation
namespace Tensor
variable {K X Y Z U V W : Type*} [CommSemiring K]
def diagonal (ι : Type*) [DecidableEq ι] : Tensor K ι ι ι :=
  fun i j k => if i = j ∧ i = k then 1 else 0
end Tensor
end MatrixMultiplication.Foundation
end OAI
namespace OAI
open scoped BigOperators
namespace MatrixMultiplication.Foundation
namespace Tensor
variable {K A B C D E F : Type*} [CommSemiring K]
def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
end Tensor
end MatrixMultiplication.Foundation
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter
open scoped Topology NNReal
theorem le_of_pow_le_polynomial_mul_pow {x y : ℝ} (hy : 0 ≤ y) (L : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → x ^ m ≤ ((m : ℝ) + 1) ^ L * y ^ m) : x ≤ y := by
  by_contra! hxy
  have hx := hy.trans_lt hxy
  have hr := tendsto_pow_const_mul_const_pow_of_lt_one L (div_nonneg hy hx.le)
    ((div_lt_one hx).2 hxy)
  have hlim : Tendsto (fun m : ℕ => (2 : ℝ) ^ L * ((m : ℝ) ^ L * (y / x) ^ m))
      atTop (𝓝 0) := by simpa using hr.const_mul ((2 : ℝ) ^ L)
  have hone : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hp : ((m : ℝ) + 1) ^ L ≤ (2 * (m : ℝ)) ^ L :=
      pow_le_pow_left₀ (by positivity) (by linarith) L
    rw [div_pow, ← mul_div_assoc, ← mul_div_assoc, le_div_iff₀ (pow_pos hx _), one_mul,
      ← mul_assoc, ← mul_pow]
    exact (h m hm).trans (mul_le_mul_of_nonneg_right hp (pow_nonneg hy _)))
  norm_num at hone
theorem nnreal_le_of_pow_le_polynomial_mul_pow {x y : ℝ≥0} (L : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → x ^ m ≤ ((m : ℝ≥0) + 1) ^ L * y ^ m) : x ≤ y := by
  apply NNReal.coe_le_coe.mp
  apply le_of_pow_le_polynomial_mul_pow y.2 L
  intro m hm
  exact_mod_cast h m hm
theorem eq_of_nat_mul_close {a b C : ℝ}
    (h : ∀ m : ℕ, |(m : ℝ) * (a - b)| ≤ C) : a = b := by
  by_contra hab
  obtain ⟨m, hm⟩ := exists_lt_nsmul (abs_pos.mpr (sub_ne_zero.mpr hab)) C
  rw [nsmul_eq_mul] at hm
  have hbound := h m
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hbound
  exact hm.not_ge hbound
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
theorem dimension_price_eq_logb {p : ℕ → ℝ} (hmono : ∀ i j, 0 < i → i ≤ j → p i ≤ p j)
    (hone : p 1 = 0) (hmul : ∀ i j, 0 < i → 0 < j → p (i * j) = p i + p j)
    {q : ℕ} (hq : 0 < q) : p q = p 2 * Real.logb 2 q := by
  have hp (i : ℕ) (hi : 0 < i) (n : ℕ) : p (i ^ n) = n * p i := by
    induction n with
    | zero => simp [hone]
    | succ n ih => rw [pow_succ, hmul _ _ (pow_pos hi _) hi, ih, Nat.cast_succ, add_mul, one_mul]
  have hp2 : 0 ≤ p 2 := by simpa [hone] using hmono 1 2 (by decide) (by decide)
  have happrox (k : ℕ) : k * p q ≤ k * (p 2 * Real.logb 2 q) + p 2 ∧
      k * (p 2 * Real.logb 2 q) ≤ k * p q + p 2 := by
    let b := Nat.log 2 (q ^ k)
    have hlo : 2 ^ b ≤ q ^ k := Nat.pow_log_le_self _ (pow_pos hq _).ne'
    have hhi : q ^ k ≤ 2 ^ (b + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hplo := hmono _ _ (pow_pos (by decide : 0 < 2) _) hlo
    have hphi := hmono _ _ (pow_pos hq _) hhi
    rw [hp _ (by decide) _, hp _ hq _] at hplo
    rw [hp _ hq _, hp _ (by decide) _, Nat.cast_add_one] at hphi
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (2 : ℝ) ^ b) (by exact_mod_cast hlo : (2 : ℝ)^b ≤ (q : ℝ)^k)
    have hu := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (q : ℝ)^k) (by exact_mod_cast hhi : (q : ℝ)^k ≤ (2 : ℝ)^(b+1))
    simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      Nat.cast_add_one, mul_one] at hl hu
    constructor <;> nlinarith only [hphi, hplo, mul_le_mul_of_nonneg_left hl hp2,
      mul_le_mul_of_nonneg_left hu hp2]
  apply eq_of_nat_mul_close (C := p 2)
  intro k
  rw [abs_le, mul_sub]
  obtain ⟨hu, hl⟩ := happrox k
  constructor <;> linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Real
open scoped NNReal
variable {A : Type*} [Semiring A] (v : A →* ℝ≥0) (hmono : ∀ {a b : ℕ}, 0 < a → a ≤ b → v (a : A) ≤ v (b : A))
include hmono in
theorem spectral_natCast_one_le (n : ℕ) (hn : 0 < n) : 1 ≤ v (n : A) := by
  simpa using hmono (a := 1) (b := n) (by decide) hn
include hmono in
private theorem spectral_natCast_logb_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    logb 2 (v (a : A)) ≤ logb 2 (v (b : A)) :=
  logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono a ha))
    (by exact_mod_cast hmono ha hab)
include hmono in
theorem spectral_natCast_logb (n : ℕ) (hn : 0 < n) :
    logb 2 (v (n : A)) = logb 2 (v (2 : A)) * logb 2 n := by
  refine dimension_price_eq_logb (p := fun i => logb 2 (v (i : A)))
    (fun _ _ => spectral_natCast_logb_mono v hmono) (by simp) ?_ hn
  intro i j hi hj
  have hpos {k : ℕ} (hk : 0 < k) : (v (k : A) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (spectral_natCast_one_le v hmono k hk)).ne'
  rw [Nat.cast_mul, map_mul, NNReal.coe_mul, logb_mul (hpos hi) (hpos hj)]
include hmono in
theorem spectral_natCast_eq_rpow (n : ℕ) (hn : 0 < n) :
    v (n : A) = (n : ℝ≥0) ^ logb 2 (v (2 : A)) := by
  apply NNReal.eq
  rw [NNReal.coe_rpow, NNReal.coe_natCast]
  have hv : 0 < (v (n : A) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le (spectral_natCast_one_le v hmono n hn)
  apply (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).injOn
      (show 0 < (v (n : A) : ℝ) from hv) (Real.rpow_pos_of_pos (by exact_mod_cast hn : 0 < (n : ℝ)) _)
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity)]
  exact spectral_natCast_logb v hmono n hn
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set NNReal
variable {S : Type*} [Semiring S]
def normalizedSpectrum (restricts : S → S → Prop) : Set (S → ℝ≥0) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧ ∀ x y, restricts x y → f x ≤ f y}
def normalizedSpectrum.toRingHom {restricts : S → S → Prop}
    (f : normalizedSpectrum restricts) : S →+* ℝ≥0 where
  toFun := f.1
  map_zero' := f.2.1
  map_one' := f.2.2.1
  map_add' := f.2.2.2.1
  map_mul' := f.2.2.2.2.1
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open scoped NNReal
variable {A : Type*} [CommSemiring A] {res : A → A → Prop} {P : Submonoid A}
theorem one_le_spectral_value (f : normalizedSpectrum res) {t : A} (ht : res 1 t) :
    1 ≤ f.val t := by
  simpa only [f.property.2.1] using f.property.2.2.2.2 1 t ht
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace Crossing
noncomputable section
variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
def basisTensor {A : I → Type*} {S : Type*} [Fintype S]
    (term : S → ∀ i, A i) (x : ∀ i, A i) : F :=
  ∑ s, if x = term s then 1 else 0
def IsRestriction {A B : I → Type*} [∀ i, Fintype (A i)]
    (X : (∀ i, B i) → F) (Y : (∀ i, A i) → F) : Prop :=
  ∃ M : ∀ i, B i → A i → F, ∀ x,
    X x = ∑ a, Y a * ∏ i, M i (x i) (a i)
theorem restriction_basisTensor_iff {A B : I → Type*} [∀ i, Fintype (A i)]
    {S : Type*} [Fintype S] (term : S → ∀ i, A i) (X : (∀ i, B i) → F) :
    IsRestriction X (basisTensor term) ↔
      ∃ M : ∀ i, B i → A i → F, ∀ x, X x = ∑ s, ∏ i, M i (x i) (term s i) := by
  unfold IsRestriction basisTensor
  congr! 3 with M x
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
end
end Crossing
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
open Crossing
variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
variable {A B C : I → Type*} [∀ i, Fintype (A i)]
theorem restrict_of_equiv {X : (∀ i, B i) → F} {Y : (∀ i, A i) → F}
    (e : ∀ i, B i ≃ A i) (h : ∀ x, X x = Y (fun i => e i (x i))) :
    IsRestriction X Y := by
  classical
  refine ⟨fun i b a => if a = e i b then 1 else 0, fun x => ?_⟩
  rw [h x]
  simp_rw [Fintype.prod_boole]
  have heq (a : ∀ i, A i) : (∀ i, a i = e i (x i)) ↔ a = fun i => e i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]
theorem restrict_refl (X : (∀ i, A i) → F) : IsRestriction X X :=
  restrict_of_equiv (fun i => Equiv.refl (A i)) fun _ => rfl
theorem restrict_trans [∀ i, Fintype (B i)] {X : (∀ i, C i) → F}
    {Y : (∀ i, B i) → F} {Z : (∀ i, A i) → F}
    (hXY : IsRestriction X Y) (hYZ : IsRestriction Y Z) : IsRestriction X Z := by
  classical
  obtain ⟨M, hM⟩ := hXY
  obtain ⟨N, hN⟩ := hYZ
  refine ⟨fun i c a => ∑ b, N i b a * M i c b, fun x => ?_⟩
  rw [hM x]
  simp_rw [hN, Finset.sum_mul, Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    mul_assoc]
  exact Finset.sum_comm
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
structure Raw (I : Type u) (K : Type w) where
  Leg : I → Type v
  finiteLeg : ∀ i, Fintype (Leg i)
  coeff : (∀ i, Leg i) → K
instance instRawFiniteLeg {I : Type u} {K : Type w} (T : Raw.{v} I K) (i : I) : Fintype (T.Leg i) := T.finiteLeg i
@[simp] theorem instRawFiniteLeg_eq {I : Type u} {K : Type w} (T : Raw.{v} I K) (i : I) : instRawFiniteLeg T i = T.finiteLeg i := rfl
@[simp] theorem instRawFiniteLeg_eqf {I : Type u} {K : Type w} (T : Raw.{v} I K) : (fun i => instRawFiniteLeg T i) = T.finiteLeg := rfl
@[simp] theorem Raw_eta_inst {I : Type u} {K : Type w} (T : Raw.{v} I K) : (⟨T.Leg, T.finiteLeg, T.coeff⟩ : Raw.{v} I K) = T := rfl
namespace Raw
variable {I : Type u} {K : Type w}
noncomputable section
open scoped Classical
abbrev Restricts [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) :=
  Crossing.IsRestriction X.coeff Y.coeff
def Equivalent [Fintype I] [CommSemiring K] (X Y : Raw.{v} I K) : Prop :=
  X.Restricts Y ∧ Y.Restricts X
def setoid (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] : Setoid (Raw.{v} I K) where
  r := Equivalent
  iseqv := ⟨fun X => ⟨restrict_refl X.coeff, restrict_refl X.coeff⟩,
    fun h => And.symm h, fun h g => ⟨restrict_trans h.1 g.1, restrict_trans g.2 h.2⟩⟩
theorem reindex_equivalent [Fintype I] [CommSemiring K] {X Y : Raw.{v} I K}
    (e : ∀ i, X.Leg i ≃ Y.Leg i) (h : ∀ x, X.coeff x = Y.coeff (fun i => e i (x i))) :
    X.Equivalent Y := by
  refine ⟨restrict_of_equiv e h, restrict_of_equiv (fun i => (e i).symm) ?_⟩
  intro y
  simpa using (h (fun i => (e i).symm (y i))).symm
def zero (I : Type u) (K : Type w) [Zero K] : Raw.{v} I K :=
  ⟨fun _ => PEmpty, fun _ => inferInstance, fun _ => 0⟩
def one (I : Type u) (K : Type w) [One K] : Raw.{v} I K :=
  ⟨fun _ => PUnit, fun _ => inferInstance, fun _ => 1⟩
def mul [Mul K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i × Y.Leg i, fun _ => inferInstance,
    fun x => X.coeff (fun i => (x i).1) * Y.coeff (fun i => (x i).2)⟩
def diagonal (I : Type u) (K : Type w) (α : Type v) [Fintype α] [CommSemiring K] : Raw.{v} I K :=
  ⟨fun _ => α, fun _ => inferInstance, fun x => ∑ a : α, if x = fun _ => a then 1 else 0⟩
end
end Raw
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical NNReal
noncomputable section
section
namespace Crossing
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {B : I → Type*} [∀ i, Fintype (B i)]
theorem restricts_from_coordinate_diagonal_equiv {L : Type*} [Fintype L]
    (e : L ≃ (∀ i, B i)) (T : (∀ i, B i) → K) :
    IsRestriction T (basisTensor (I := I) (fun (l : L) _ ↦ l)) := by
  classical
  let o : I := Classical.choice inferInstance
  let M (i : I) (b : B i) (a : ∀ i, B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then T a else 1)
  apply (restriction_basisTensor_iff _ _).mpr
  refine ⟨fun i b l ↦ M i b (e l), fun b ↦ ?_⟩
  have hprod (a : ∀ i, B i) :
      (∏ i, M i (b i) a) = if b = a then T a else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  rw [e.sum_comp (fun a ↦ ∏ i, M i (b i) a)]
  simp [hprod]
theorem unit_restricts_of_nonzero {T : (∀ i, B i) → K} (h : T ≠ 0) :
    IsRestriction (fun _ : I → PUnit ↦ (1 : K)) T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T a ≠ 0 := by
    by_contra! hn
    exact h (funext hn)
  let o : I := Classical.choice inferInstance
  let M (i : I) (_ : PUnit) (b : B i) : K :=
    (if b = a i then 1 else 0) * (if i = o then (T a)⁻¹ else 1)
  refine ⟨M, fun _ ↦ ?_⟩
  have hprod (b : ∀ i, B i) :
      (∏ i, M i PUnit.unit (b i)) = if b = a then (T a)⁻¹ else 0 := by
    simp only [M, Finset.prod_mul_distrib, Fintype.prod_boole, ← funext_iff]
    simp
  simp [hprod, mul_ite, ha]
end Crossing
namespace SiteTensor.Raw
universe v
theorem restricts_diagonal (I : Type*) [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) :
    X.Restricts (diagonal I K (ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))))) := by
  classical
  let e : ULift.{v} (Fin (Fintype.card (∀ i, X.Leg i))) ≃ (∀ i, X.Leg i) :=
    Equiv.ulift.trans (Fintype.equivFin _).symm
  have h := Crossing.restricts_from_coordinate_diagonal_equiv e X.coeff
  unfold Crossing.basisTensor at h
  convert! h using 1
  funext x
  simp only [diagonal]
  congr 1
  funext a
  split_ifs <;> simp_all
theorem one_restricts_of_nonzero {I : Type*} [Fintype I] [Nonempty I]
    {K : Type*} [Field K] (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    (one I K).Restricts X :=
  Crossing.unit_restricts_of_nonzero h
end SiteTensor.Raw
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
noncomputable section
variable {X Y Z K : Type*} [Fintype X]
def pushCoeff [AddCommMonoid K] (f : X → Y) (T : X → K) (y : Y) : K :=
  ∑ x, if f x = y then T x else 0
theorem pushCoeff_comp [AddCommMonoid K] [Fintype Y]
    (g : Y → Z) (f : X → Y) (T : X → K) :
    pushCoeff g (pushCoeff f T) = pushCoeff (g ∘ f) T := by
  funext z
  unfold pushCoeff
  have hs (y : Y) : (if g y = z then ∑ x, if f x = y then T x else 0 else 0) =
      ∑ x, if g y = z then if f x = y then T x else 0 else 0 := by
    by_cases h : g y = z <;> simp [h]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp
theorem pushCoeff_add [AddCommMonoid K] (f : X → Y) (T U : X → K) :
    pushCoeff f (T + U) = pushCoeff f T + pushCoeff f U := by
  funext y
  simp only [pushCoeff, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp
theorem pushCoeff_equiv [AddCommMonoid K] (e : X ≃ Y) (T : X → K) (y : Y) :
    pushCoeff e T y = T (e.symm y) := by
  simp [pushCoeff, ← e.eq_symm_apply]
theorem sum_pushCoeff_mul [Semiring K] [Fintype Y] (f : X → Y) (T : X → K) (g : Y → K) :
    ∑ y, pushCoeff f T y * g y = ∑ x, T x * g (f x) := by
  simp only [pushCoeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
variable {I : Type*} [Fintype I] {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [AddCommMonoid K]
def sumCoeff (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (y : ∀ i, A i ⊕ B i) : K :=
  pushCoeff (fun x i => Sum.inl (x i)) T y + pushCoeff (fun x i => Sum.inr (x i)) U y
theorem sumCoeff_inl [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i) : sumCoeff T U (fun i => Sum.inl (x i)) = T x := by
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) =
      (fun i => Sum.inl (x i)) ↔ y = x := by
    simp [funext_iff]
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inl (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]
theorem sumCoeff_inr [Nonempty I] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, B i) : sumCoeff T U (fun i => Sum.inr (x i)) = U x := by
  have hr (y : ∀ i, B i) : (fun i => (Sum.inr (y i) : A i ⊕ B i)) =
      (fun i => Sum.inr (x i)) ↔ y = x := by
    simp [funext_iff]
  have hl (y : ∀ i, A i) : (fun i => (Sum.inl (y i) : A i ⊕ B i)) ≠
      (fun i => Sum.inr (x i)) := by
    intro h
    cases congrFun h (Classical.arbitrary I)
  simp [sumCoeff, pushCoeff, hl, hr]
theorem sumCoeff_mixed (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (y : ∀ i, A i ⊕ B i)
    (hl : ∀ x : ∀ i, A i, (fun i => Sum.inl (x i)) ≠ y)
    (hr : ∀ x : ∀ i, B i, (fun i => Sum.inr (x i)) ≠ y) :
    sumCoeff T U y = 0 := by
  simp [sumCoeff, pushCoeff, hl, hr]
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
variable {I K : Type*} [Fintype I] [AddCommMonoid K]
variable {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
private theorem pushCoeff_relabel {X Y Z : Type*} [Fintype X]
    (e : Y ≃ Z) (f : X → Y) (g : X → Z) (h : ∀ x, e (f x) = g x)
    (T : X → K) (y : Y) : pushCoeff f T y = pushCoeff g T (e y) := by
  classical
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← h, e.injective.eq_iff]
private theorem pushCoeff_add_apply {X Y : Type*} [Fintype X]
    (f : X → Y) (T U : X → K) (y : Y) :
    pushCoeff f (fun x => T x + U x) y = pushCoeff f T y + pushCoeff f U y :=
  congrFun (pushCoeff_add f T U) y
theorem sumCoeff_comm (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (x : ∀ i, A i ⊕ B i) :
    sumCoeff T U x = sumCoeff U T (fun i => Equiv.sumComm _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumComm (A i) (B i)
  unfold sumCoeff
  rw [add_comm]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
    (pushCoeff_relabel e _ _ (fun _ => rfl) T x)
theorem sumCoeff_assoc (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) (V : (∀ i, C i) → K)
    (x : ∀ i, (A i ⊕ B i) ⊕ C i) :
    sumCoeff (sumCoeff T U) V x =
      sumCoeff T (sumCoeff U V) (fun i => Equiv.sumAssoc _ _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumAssoc (A i) (B i) (C i)
  unfold sumCoeff
  simp_rw [pushCoeff_add_apply, pushCoeff_comp, add_assoc]
  exact congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) T x)
    (congrArg₂ (· + ·) (pushCoeff_relabel e _ _ (fun _ => rfl) U x)
      (pushCoeff_relabel e _ _ (fun _ => rfl) V x))
theorem sumCoeff_zero [∀ i, IsEmpty (B i)] (T : (∀ i, A i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff T (0 : (∀ i, B i) → K) x = T (fun i => Equiv.sumEmpty _ _ (x i)) := by
  let e := Equiv.piCongrRight fun i => Equiv.sumEmpty (A i) (B i)
  unfold sumCoeff
  rw [pushCoeff_relabel e _ (Equiv.refl _) (fun _ => rfl) T, pushCoeff_equiv]
  simp only [pushCoeff, Pi.zero_apply, ite_self, Finset.sum_const_zero, add_zero]
  rfl
theorem zero_sumCoeff [∀ i, IsEmpty (A i)] (U : (∀ i, B i) → K) (x : ∀ i, A i ⊕ B i) :
    sumCoeff (0 : (∀ i, A i) → K) U x = U (fun i => Equiv.emptySum _ _ (x i)) := by
  rw [sumCoeff_comm, sumCoeff_zero]
  rfl
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K] {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
theorem sumCoeff_product_distrib (T : (∀ i, A i) → K) (U : (∀ i, B i) → K)
    (V : (∀ i, C i) → K) (x : ∀ i, A i × (B i ⊕ C i)) :
    T (fun i => (x i).1) * sumCoeff U V (fun i => (x i).2) =
      sumCoeff (fun y : ∀ i, A i × B i => T (fun i => (y i).1) * U (fun i => (y i).2))
        (fun y : ∀ i, A i × C i => T (fun i => (y i).1) * V (fun i => (y i).2))
        (fun i => Equiv.prodSumDistrib _ _ _ (x i)) := by
  classical
  let u (i : I) := (x i).1
  let v (i : I) := (x i).2
  change T u * sumCoeff U V v = sumCoeff _ _ (fun i => Equiv.prodSumDistrib _ _ _ (u i, v i))
  generalize v = w
  by_cases hl : ∃ y : ∀ i, B i, (fun i => Sum.inl (y i)) = w
  · obtain ⟨y, rfl⟩ := hl
    simp only [Equiv.prodSumDistrib_apply_left, sumCoeff_inl]
  by_cases hr : ∃ y : ∀ i, C i, (fun i => Sum.inr (y i)) = w
  · obtain ⟨y, rfl⟩ := hr
    simp only [Equiv.prodSumDistrib_apply_right, sumCoeff_inr]
  have hleft (z : ∀ i, A i × B i) :
      (fun i => Sum.inl (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hl ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  have hright (z : ∀ i, A i × C i) :
      (fun i => Sum.inr (z i)) ≠ (fun i => Equiv.prodSumDistrib _ _ _ (u i, w i)) := by
    intro eq
    refine hr ⟨fun i => (z i).2, funext fun i => ?_⟩
    have h := congrArg (fun t => ((Equiv.prodSumDistrib (A i) (B i) (C i)).symm t).2)
      (congrFun eq i)
    simpa using h
  rw [sumCoeff_mixed _ _ _ (not_exists.mp hl) (not_exists.mp hr),
    sumCoeff_mixed _ _ _ hleft hright, mul_zero]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
variable {I K : Type*} [Fintype I] [CommSemiring K]
theorem mul_assoc_equivalent (X Y Z : Raw I K) :
    ((X.mul Y).mul Z).Equivalent (X.mul (Y.mul Z)) := by
  apply reindex_equivalent (fun _ => Equiv.prodAssoc _ _ _)
  intro x
  apply mul_assoc
theorem mul_comm_equivalent (X Y : Raw I K) :
    (X.mul Y).Equivalent (Y.mul X) := by
  apply reindex_equivalent (fun _ => Equiv.prodComm _ _)
  intro x
  apply mul_comm
theorem one_mul_equivalent (X : Raw I K) : ((one I K).mul X).Equivalent X := by
  apply reindex_equivalent (fun _ => Equiv.punitProd _)
  intro x
  apply one_mul
theorem zero_mul_equivalent [Nonempty I] (X : Raw I K) :
    ((zero I K).mul X).Equivalent (zero I K) := by
  apply reindex_equivalent (fun _ => Equiv.pemptyProd _)
  intro x
  exact (x (Classical.arbitrary I)).1.elim
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
variable {I F : Type*} [Fintype I] [CommSemiring F] {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
theorem restrict_product
    {X : (∀ i, A i) → F} {Y : (∀ i, B i) → F}
    {X' : (∀ i, C i) → F} {Y' : (∀ i, D i) → F}
    (hX : Crossing.IsRestriction X' X) (hY : Crossing.IsRestriction Y' Y) :
    Crossing.IsRestriction
      (fun a : ∀ i, C i × D i => X' (fun i => (a i).1) * Y' (fun i => (a i).2))
      (fun a : ∀ i, A i × B i => X (fun i => (a i).1) * Y (fun i => (a i).2)) := by
  classical
  obtain ⟨M, hM⟩ := hX
  obtain ⟨N, hN⟩ := hY
  refine ⟨fun i x a => M i x.1 a.1 * N i x.2 a.2, fun x => ?_⟩
  dsimp
  rw [hM, hN, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A B).symm _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
universe v u w
variable {I : Type u} {K : Type w} [Fintype I]
noncomputable def add [AddCommMonoid K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i ⊕ Y.Leg i, fun _ => inferInstance, sumCoeff X.coeff Y.coeff⟩
theorem mul_restricts [CommSemiring K] {X Y U V : Raw.{v} I K}
    (h : X.Restricts Y) (h' : U.Restricts V) : (X.mul U).Restricts (Y.mul V) :=
  restrict_product h h'
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
def TensorClass (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] :=
  Quotient (Raw.setoid.{v} I K)
variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]
def ofRaw (X : Raw.{v} I K) : TensorClass.{v} I K :=
  Quotient.mk _ X
@[simp] theorem ofRaw_eq_iff {X Y : Raw.{v} I K} :
    ofRaw X = ofRaw Y ↔ X.Equivalent Y := Quotient.eq
instance : LE (TensorClass.{v} I K) where
  le := Quotient.lift₂ Raw.Restricts fun _ _ _ _ hX hY => propext
    ⟨fun h => restrict_trans hX.2 (restrict_trans h hY.1),
     fun h => restrict_trans hX.1 (restrict_trans h hY.2)⟩
@[simp] theorem ofRaw_le_iff {X Y : Raw.{v} I K} :
    ofRaw X ≤ ofRaw Y ↔ X.Restricts Y := Iff.rfl
instance : PartialOrder (TensorClass.{v} I K) where
  le_refl X := Quotient.inductionOn X fun x => restrict_refl x.coeff
  le_trans X Y Z := Quotient.inductionOn₃ X Y Z fun _ _ _ => restrict_trans
  le_antisymm X Y := Quotient.inductionOn₂ X Y fun _ _ h g => Quotient.sound ⟨h, g⟩
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
open Crossing
variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]
variable {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)] [∀ i, Fintype (D i)]
omit [∀ i, Fintype (C i)] in
theorem pushCoeff_restriction {X : (∀ i, B i) → K} {T : (∀ i, A i) → K}
    (M : ∀ i, B i → A i → K)
    (hM : ∀ x, X x = ∑ a, T a * ∏ i, M i (x i) (a i))
    (f : ∀ i, B i → C i) (y : ∀ i, C i) :
    pushCoeff (fun x i => f i (x i)) X y =
      ∑ a, T a * ∏ i, ∑ b, if f i b = y i then M i b (a i) else 0 := by
  simp only [Fintype.prod_sum, Finset.mul_sum, Fintype.prod_ite_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold pushCoeff
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hM x, funext_iff]
  split <;> simp [*]
theorem restrict_sum {X : (∀ i, B i) → K} {Y : (∀ i, D i) → K}
    {T : (∀ i, A i) → K} {U : (∀ i, C i) → K}
    (h : IsRestriction X T) (h' : IsRestriction Y U) :
    IsRestriction (sumCoeff X Y) (sumCoeff T U) := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨N, hN⟩ := h'
  let L (i : I) : B i ⊕ D i → A i ⊕ C i → K
    | .inl b, .inl a => M i b a
    | .inr d, .inr c => N i d c
    | _, _ => 0
  refine ⟨L, fun y => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, sum_pushCoeff_mul]
  rw [pushCoeff_restriction M hM, pushCoeff_restriction N hN]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => congrArg (T a * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]
  · refine Finset.sum_congr rfl fun c _ => congrArg (U c * ·) ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    cases y i <;> simp [L]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]
noncomputable section
instance : Add (TensorClass.{v} I K) where
  add := Quotient.map₂ Raw.add fun _ _ h _ _ g =>
    ⟨restrict_sum h.1 g.1, restrict_sum h.2 g.2⟩
instance : Mul (TensorClass.{v} I K) where
  mul := Quotient.map₂ Raw.mul fun _ _ h _ _ g =>
    ⟨Raw.mul_restricts h.1 g.1, Raw.mul_restricts h.2 g.2⟩
instance : Zero (TensorClass.{v} I K) := ⟨ofRaw (Raw.zero I K)⟩
instance : One (TensorClass.{v} I K) := ⟨ofRaw (Raw.one I K)⟩
@[simp] theorem ofRaw_add (X Y : Raw.{v} I K) : ofRaw (X.add Y) = ofRaw X + ofRaw Y := rfl
@[simp] theorem ofRaw_mul (X Y : Raw.{v} I K) : ofRaw (X.mul Y) = ofRaw X * ofRaw Y := rfl
@[simp] theorem ofRaw_zero : ofRaw (Raw.zero.{v} I K) = 0 := rfl
@[simp] theorem ofRaw_one : ofRaw (Raw.one.{v} I K) = 1 := rfl
private theorem class_add_comm (X Y : TensorClass.{v} I K) : X + Y = Y + X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumComm _ _) (sumCoeff_comm x.coeff y.coeff)
private theorem class_zero_add (X : TensorClass.{v} I K) : 0 + X = X := by
  let (i : I) : IsEmpty ((Raw.zero.{v} I K).Leg i) := inferInstanceAs (IsEmpty PEmpty)
  exact
  Quotient.inductionOn X fun x => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.emptySum _ _) (zero_sumCoeff x.coeff)
private theorem class_mul_comm (X Y : TensorClass.{v} I K) : X * Y = Y * X :=
  Quotient.inductionOn₂ X Y fun x y => Quotient.sound (x.mul_comm_equivalent y)
private theorem class_one_mul (X : TensorClass.{v} I K) : 1 * X = X :=
  Quotient.inductionOn X fun x => Quotient.sound (x.one_mul_equivalent)
variable [Nonempty I]
private theorem class_zero_mul (X : TensorClass.{v} I K) : 0 * X = 0 :=
  Quotient.inductionOn X fun x => Quotient.sound (x.zero_mul_equivalent)
private theorem class_left_distrib (X Y Z : TensorClass.{v} I K) :
    X * (Y + Z) = X * Y + X * Z :=
  Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.prodSumDistrib _ _ _)
      (sumCoeff_product_distrib x.coeff y.coeff z.coeff)
instance : CommSemiring (TensorClass.{v} I K) where
  add_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.sumAssoc _ _ _) (sumCoeff_assoc x.coeff y.coeff z.coeff)
  add_comm := class_add_comm
  zero_add := class_zero_add
  add_zero X := (class_add_comm X 0).trans (class_zero_add X)
  nsmul := nsmulRec
  mul_assoc X Y Z := Quotient.inductionOn₃ X Y Z fun x y z =>
    Quotient.sound (x.mul_assoc_equivalent y z)
  mul_comm := class_mul_comm
  one_mul := class_one_mul
  mul_one X := (class_mul_comm X 1).trans (class_one_mul X)
  zero_mul := class_zero_mul
  mul_zero X := (class_mul_comm X 0).trans (class_zero_mul X)
  left_distrib := class_left_distrib
  right_distrib X Y Z := by rw [class_mul_comm, class_left_distrib, class_mul_comm Z X, class_mul_comm Z Y]
omit [Nonempty I] in
theorem add_mono {X Y U V : TensorClass.{v} I K} (h : X ≤ Y) (g : U ≤ V) :
    X + U ≤ Y + V := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  induction U using Quotient.inductionOn
  induction V using Quotient.inductionOn
  exact restrict_sum h g
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v u w
variable {I : Type u} [Fintype I] {K : Type w}
section Semiring
variable [CommSemiring K]
theorem zero_le_tensor [Nonempty I] (X : TensorClass.{v} I K) : 0 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    change (Raw.zero I K).Restricts x
    refine ⟨fun _ _ _ => 0, fun y => ?_⟩
    exact (y (Classical.arbitrary I)).elim
theorem ofRaw_eq_zero_iff (X : Raw.{v} I K) : ofRaw X = 0 ↔ X.coeff = 0 := by
  change ofRaw X = ofRaw (Raw.zero I K) ↔ _
  rw [ofRaw_eq_iff]
  constructor
  · rintro ⟨⟨M, hM⟩, _⟩
    funext x
    simpa [Raw.zero] using hM x
  · intro h
    constructor
    · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
      simp [Raw.zero, h]
    · refine ⟨fun _ _ _ => 0, fun y => ?_⟩
      simp [Raw.zero, h]
end Semiring
theorem one_le_of_ne_zero [Nonempty I] [Field K] {X : TensorClass.{v} I K}
    (h : X ≠ 0) : 1 ≤ X := by
  induction X using Quotient.inductionOn with
  | h x =>
    exact x.one_restricts_of_nonzero (fun h0 => h ((ofRaw_eq_zero_iff x).mpr h0))
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped NNReal
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → _))
def rawLogPrice (c : ℝ) (X : Raw.{v} I K) : ℝ :=
  c * Real.logb 2 (φ.val (ofRaw X) : ℝ)
theorem one_le_raw_spectralValue (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    1 ≤ φ.val (ofRaw X) :=
  one_le_spectral_value φ (X.one_restricts_of_nonzero h)
theorem rawLogPrice_zero (c : ℝ) (X : Raw.{v} I K) (h : X.coeff = 0) :
    rawLogPrice φ c X = 0 := by
  simp [rawLogPrice, (ofRaw_eq_zero_iff X).mpr h, φ.property.1]
theorem rawLogPrice_nonneg {c : ℝ} (hc : 0 ≤ c) (X : Raw.{v} I K) :
    0 ≤ rawLogPrice φ c X := by
  by_cases h : X.coeff = 0
  · rw [rawLogPrice_zero φ c X h]
  · apply mul_nonneg hc (Real.logb_nonneg (by norm_num) _)
    exact_mod_cast one_le_raw_spectralValue φ X h
theorem rawLogPrice_mono {c : ℝ} (hc : 0 ≤ c) {X Y : Raw.{v} I K}
    (h : X.Restricts Y) : rawLogPrice φ c X ≤ rawLogPrice φ c Y := by
  by_cases hX : X.coeff = 0
  · rw [rawLogPrice_zero φ c X hX]
    exact rawLogPrice_nonneg φ hc _
  · apply mul_le_mul_of_nonneg_left _ hc
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
    · exact_mod_cast φ.property.2.2.2.2 (ofRaw X) (ofRaw Y) h
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor.Raw
universe v
variable (I K : Type*) [Fintype I] [CommSemiring K]
theorem diagonal_equiv {α β : Type v} [Fintype α] [Fintype β] (e : α ≃ β) :
    (diagonal I K α).Equivalent (diagonal I K β) := by
  classical
  apply reindex_equivalent (fun _ => e)
  intro (x : I → α)
  simp only [diagonal]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  have h : (fun i => e (x i)) = (fun _ => e a) ↔ x = (fun _ => a) := by
    simp [funext_iff]
  congr! 1
  exact h.symm
theorem diagonal_empty_equivalent :
    (diagonal I K PEmpty.{v + 1}).Equivalent (zero I K) := by
  classical
  apply reindex_equivalent (fun _ => Equiv.refl _)
  intro x
  simp [diagonal]
theorem diagonal_unit_equivalent :
    (diagonal I K PUnit.{v + 1}).Equivalent (one I K) := by
  classical
  apply reindex_equivalent (X := diagonal I K _) (Y := one I K) (fun _ => Equiv.refl _)
  intro (x : I → PUnit.{v + 1})
  simp [diagonal, one, Subsingleton.elim x (fun _ => PUnit.unit)]
private theorem push_constant_labels (α : Type v) [Fintype α] {Y : Type*}
    (f : (I → α) → Y) (y : Y) :
    pushCoeff f (diagonal I K α).coeff y =
      ∑ a : α, if f (fun _ => a) = y then 1 else 0 := by
  classical
  let c (a : α) : I → α := fun _ => a
  have hc : (diagonal I K α).coeff = pushCoeff c (fun _ => 1) := by
    funext x
    apply Finset.sum_congr rfl
    intro a _
    change (if x = c a then (1 : K) else 0) = (if c a = x then 1 else 0)
    congr! 1
    exact eq_comm
  rw [hc, pushCoeff_comp]
  rfl
theorem diagonal_sum_equivalent (α β : Type v) [Fintype α] [Fintype β] :
    ((diagonal I K α).add (diagonal I K β)).Equivalent (diagonal I K (α ⊕ β)) := by
  classical
  apply reindex_equivalent (X := (diagonal I K α).add (diagonal I K β))
    (Y := diagonal I K (α ⊕ β)) (fun _ => Equiv.refl _)
  intro (x : I → α ⊕ β)
  let f (y : I → α) (i : I) : α ⊕ β := Sum.inl (y i)
  let g (y : I → β) (i : I) : α ⊕ β := Sum.inr (y i)
  change pushCoeff f (diagonal I K α).coeff x +
    pushCoeff g (diagonal I K β).coeff x = (diagonal I K (α ⊕ β)).coeff x
  rw [push_constant_labels I K α, push_constant_labels I K β]
  simp only [diagonal, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro a _ <;>
    congr! 1 <;> exact eq_comm
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v
variable (I K : Type*) [Fintype I] [Nonempty I] [CommSemiring K]
@[simp] theorem ofRaw_diagonal_eq_natCast (α : Type v) [Fintype α] :
    ofRaw (Raw.diagonal I K α) = (Fintype.card α : TensorClass.{v} I K) := by
  classical
  refine Fintype.induction_empty_option (P := fun β _ =>
    ofRaw (Raw.diagonal I K β) = (Fintype.card β : TensorClass.{v} I K)) ?_ ?_ ?_ α
  · intro β γ _ e ih
    let := Fintype.ofEquiv γ e.symm
    rw [← Fintype.card_congr e, ← ih]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_equiv I K e.symm)
  · rw [Fintype.card_pempty, Nat.cast_zero, ← ofRaw_zero]
    exact ofRaw_eq_iff.mpr (Raw.diagonal_empty_equivalent I K)
  · intro β _ ih
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one, ← ih, ← ofRaw_one]
    have h := Raw.diagonal_equiv I K (Equiv.optionEquivSumPUnit.{v} β)
    rw [ofRaw_eq_iff.mpr h, ← ofRaw_eq_iff.mpr (Raw.diagonal_sum_equivalent I K β PUnit.{v + 1}),
      ofRaw_add, ofRaw_eq_iff.mpr (Raw.diagonal_unit_equivalent I K)]
@[simp] theorem ofRaw_diagonal_fin_eq_natCast (n : ℕ) :
    ofRaw (Raw.diagonal I K (Fin n)) = (n : TensorClass.{0} I K) := by
  simpa only [Fintype.card_fin] using ofRaw_diagonal_eq_natCast I K (Fin n)
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor.Raw
universe u v w
variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [CommSemiring K]
variable {α β : Type v} [Fintype α] [Fintype β]
theorem diagonal_restricts_of_embedding (e : α ↪ β) :
    (diagonal I K α).Restricts (diagonal I K β) := by
  classical
  unfold Restricts diagonal
  refine ⟨fun _ a b => if b = e a then 1 else 0, fun x => ?_⟩
  simp_rw [Fintype.prod_boole]
  have heq (y : I → β) : (∀ i, y i = e (x i)) ↔ y = fun i => e (x i) :=
    funext_iff.symm
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  let i₀ : I := Classical.choice inferInstance
  rw [Finset.sum_eq_single (x i₀), Finset.sum_eq_single (e (x i₀))]
  · simp [funext_iff]
  · intro b _ hb
    exact ite_eq_right fun h => (hb (congrFun h i₀).symm).elim
  · simp
  · intro a _ ha
    exact ite_eq_right fun h => (ha (congrFun h i₀).symm).elim
  · simp
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
namespace SiteTensor
open Crossing
variable {I K : Type*} [Fintype I] [CommSemiring K]
variable {A B : I → Type*} [∀ i, Fintype (A i)]
theorem pushCoeff_restricts (f : ∀ i, A i → B i) (X : (∀ i, A i) → K) :
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨fun i b a => if f i a = b then 1 else 0, fun x => ?_⟩
  simp only [pushCoeff, Fintype.prod_boole, ← funext_iff, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all
theorem equivalent_pushCoeff [∀ i, Fintype (B i)] (f : ∀ i, A i ↪ B i)
    (X : (∀ i, A i) → K) :
    IsRestriction X (pushCoeff (fun x i => f i (x i)) X) ∧
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨?_, pushCoeff_restricts (fun i => f i) X⟩
  refine ⟨fun i a b => if b = f i a then 1 else 0, fun x => ?_⟩
  rw [sum_pushCoeff_mul]
  simp [Fintype.prod_boole, ← funext_iff, mul_ite]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
section
namespace SiteTensor.Raw
variable {I J K : Type*} [Fintype I]
def group (T : SiteTensor.Raw I K) (σ : I → J) : SiteTensor.Raw J K where
  Leg := fun j => (i : {i : I // σ i = j}) → T.Leg i.1
  finiteLeg := fun _ => inferInstance
  coeff := fun x => T.coeff (fun i => x (σ i) ⟨i, rfl⟩)
end SiteTensor.Raw
open SiteTensor
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped Classical
def groupIndexEquiv {I J : Type*} (σ : I → J) (A : I → Type*) :
    (∀ i, A i) ≃ (∀ j, (t : {i // σ i = j}) → A t.1) :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)
@[simp] theorem groupIndexEquiv_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ i, A i) (j : J) (t : {i // σ i = j}) : groupIndexEquiv σ A a j t = a t.1 := rfl
@[simp] theorem groupIndexEquiv_symm_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ j, (t : {i // σ i = j}) → A t.1) (i : I) :
    (groupIndexEquiv σ A).symm a i = a (σ i) ⟨i, rfl⟩ := rfl
namespace Raw
variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]
theorem group_restricts (σ : I → J) {X Y : Raw I K} (h : X.Restricts Y) :
    (X.group σ).Restricts (Y.group σ) := by
  classical
  obtain ⟨M, hM⟩ := h
  refine ⟨fun j b a => ∏ i : {i // σ i = j}, M i.1 (b i) (a i), fun x => ?_⟩
  change X.coeff ((groupIndexEquiv σ X.Leg).symm x) = _
  rw [hM]
  refine Fintype.sum_equiv (groupIndexEquiv σ Y.Leg) _ _ fun a => ?_
  apply congrArg (Y.coeff a * ·)
  let w (p : Σ j, {i // σ i = j}) := M p.2.1 (x p.1 p.2) (a p.2.1)
  calc
    _ = ∏ p, w p := Fintype.prod_equiv (Equiv.sigmaFiberEquiv σ).symm _ _ (fun i => rfl)
    _ = _ := Fintype.prod_sigma w
theorem group_mul_equivalent (σ : I → J) (X Y : Raw I K) :
    ((X.mul Y).group σ).Equivalent ((X.group σ).mul (Y.group σ)) := by
  apply reindex_equivalent (fun j =>
    Equiv.arrowProdEquivProdArrow {i // σ i = j} (fun i => X.Leg i.1) (fun i => Y.Leg i.1))
  intro x
  rfl
theorem group_one_equivalent (σ : I → J) :
    ((one I K).group σ).Equivalent (one J K) := by
  let (j : J) : Unique (((one I K).group σ).Leg j) := inferInstanceAs (Unique (∀ _ : {i // σ i = j}, PUnit))
  apply reindex_equivalent (fun _ => Equiv.equivPUnit _)
  intro x
  rfl
theorem group_zero_equivalent (σ : I → J) (hs : Function.Surjective σ) :
    ((zero I K).group σ).Equivalent (zero J K) := by
  classical
  have (j : J) : IsEmpty (((zero I K).group σ).Leg j) := by
    obtain ⟨i, hi⟩ := hs j
    exact ⟨fun x => (x ⟨i, hi⟩).elim⟩
  apply reindex_equivalent (fun _ => Equiv.equivPEmpty _)
  intro x
  rfl
end Raw
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Classical
namespace SiteTensor.Raw
universe v
variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]
private def groupedTags (σ : I → J) (hs : Function.Surjective σ) (A B : I → Type v) (j : J) :
    ((∀ t : {i // σ i = j}, A t.1) ⊕ (∀ t : {i // σ i = j}, B t.1)) ↪
      (∀ t : {i // σ i = j}, A t.1 ⊕ B t.1) where
  toFun := Sum.elim (fun a t => Sum.inl (a t)) (fun b t => Sum.inr (b t))
  inj' := by
    obtain ⟨i, hi⟩ := hs j
    intro a b h
    cases a <;> cases b
    · congr 1
      funext t
      exact Sum.inl.inj (congrFun h t)
    · cases congrFun h ⟨i, hi⟩
    · cases congrFun h ⟨i, hi⟩
    · congr 1
      funext t
      exact Sum.inr.inj (congrFun h t)
omit [Fintype J] in
private theorem group_eq_push (σ : I → J) (X : Raw.{v} I K) :
    (X.group σ).coeff = pushCoeff (groupIndexEquiv σ X.Leg) X.coeff := by
  funext x
  exact (pushCoeff_equiv (groupIndexEquiv σ X.Leg) X.coeff x).symm
theorem group_add_equivalent (σ : I → J) (hs : Function.Surjective σ) (X Y : Raw.{v} I K) :
    ((X.add Y).group σ).Equivalent ((X.group σ).add (Y.group σ)) := by
  let g := groupedTags σ hs X.Leg Y.Leg
  let e := groupIndexEquiv σ (fun i => X.Leg i ⊕ Y.Leg i)
  let S := (X.group σ).add (Y.group σ)
  have h : ((X.add Y).group σ).coeff = pushCoeff (fun x j => g j (x j)) S.coeff := by
    rw [group_eq_push]
    change pushCoeff e (pushCoeff (fun x i => Sum.inl (x i)) X.coeff +
      pushCoeff (fun y i => Sum.inr (y i)) Y.coeff) =
      pushCoeff (fun (x : ∀ j, (X.group σ).Leg j ⊕ (Y.group σ).Leg j) j => g j (x j)) (pushCoeff (fun x j => Sum.inl (x j)) (X.group σ).coeff +
        pushCoeff (fun y j => Sum.inr (y j)) (Y.group σ).coeff)
    rw [group_eq_push, group_eq_push, pushCoeff_add, pushCoeff_add]
    congr 1 <;> (erw [pushCoeff_comp, pushCoeff_comp, pushCoeff_comp]) <;> rfl
  have hg := equivalent_pushCoeff g S.coeff
  unfold Equivalent Restricts
  rw [h]
  exact ⟨hg.2, hg.1⟩
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
noncomputable section
open scoped NNReal
universe v u u' w
variable {I : Type u} {J : Type u'} {K : Type w} [Fintype I] [Fintype J] [CommSemiring K]
def groupClass (σ : I → J) : TensorClass.{v} I K → TensorClass.{max u v} J K :=
  Quotient.map (fun X => X.group σ) fun _ _ h =>
    ⟨Raw.group_restricts σ h.1, Raw.group_restricts σ h.2⟩
@[simp] theorem groupClass_ofRaw (σ : I → J) (X : Raw.{v} I K) :
    groupClass σ (ofRaw X) = ofRaw (X.group σ) := rfl
theorem groupClass_mono (σ : I → J) : Monotone (groupClass (K := K) σ) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ => Raw.group_restricts σ
def groupMulHom [Nonempty I] [Nonempty J] (σ : I → J) :
    TensorClass.{v} I K →* TensorClass.{max u v} J K where
  toFun := groupClass σ
  map_one' := ofRaw_eq_iff.mpr (Raw.group_one_equivalent σ)
  map_mul' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_mul_equivalent σ x y)
def groupRingHom [Nonempty I] [Nonempty J] (σ : I → J) (hs : Function.Surjective σ) :
    TensorClass.{v} I K →+* TensorClass.{max u v} J K where
  __ := groupMulHom σ
  map_zero' := ofRaw_eq_iff.mpr (Raw.group_zero_equivalent σ hs)
  map_add' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.group_add_equivalent σ hs x y)
def groupSpectralPoint [Nonempty I] [Nonempty J] (σ : I → J) (hs : Function.Surjective σ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{max u v} J K → _ → Prop)) :
    normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop) := by
  let ψ := (normalizedSpectrum.toRingHom φ).comp (groupRingHom σ hs)
  exact ⟨ψ, ψ.map_zero, ψ.map_one, ψ.map_add, ψ.map_mul,
    fun x y h => φ.property.2.2.2.2 _ _ (groupClass_mono σ h)⟩
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
noncomputable section
open scoped NNReal
variable {I J : Type} {K : Type*} [Fintype I] [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
def rawWireDistance (s t : J) : ℝ :=
  rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group ![s, t])
omit [Nonempty J] in
theorem Raw.group_const_restricts_one (T : Raw.{0} I K) (s : J) :
    (T.group (fun _ => s)).Restricts (Raw.one J K) := by
  classical
  let M (j : J) (b : (T.group (fun _ => s)).Leg j) (_ : (Raw.one J K).Leg j) : K :=
    if h : s = j then T.coeff (fun i => b ⟨i, h⟩) else 1
  refine ⟨M, fun x => ?_⟩
  let (j : J) : Unique ((Raw.one J K).Leg j) := inferInstanceAs (Unique PUnit)
  rw [Fintype.sum_unique]
  change T.coeff (fun i => x s ⟨i, rfl⟩) = 1 * ∏ j, M j (x j) PUnit.unit
  rw [one_mul, Finset.prod_eq_single s]
  · simp [M]
  · intro j _ hj
    simp [M, Ne.symm hj]
  · simp
theorem rawLogPrice_const (hc : 0 ≤ c) (T : Raw.{0} I K) (s : J) :
    rawLogPrice φ c (T.group (fun _ => s)) = 0 := by
  apply le_antisymm _ (rawLogPrice_nonneg φ hc _)
  have h := rawLogPrice_mono φ hc (T.group_const_restricts_one s)
  simpa [rawLogPrice, φ.property.2.1] using h
@[simp] theorem rawWireDistance_self (hc : 0 ≤ c) (s : J) : rawWireDistance φ c s s = 0 := by
  have h : (![s, s] : Fin 2 → J) = fun _ => s := by funext i; fin_cases i <;> rfl
  simpa only [rawWireDistance, h] using rawLogPrice_const φ c hc (Raw.diagonal (Fin 2) K (Fin 2)) s
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
theorem rank_fromBlocks_diagonal {F I J I' J' : Type*} [Field F] [Fintype J] [Fintype J']
    (A : Matrix I J F) (B : Matrix I' J' F) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow I I' F F
  let d := LinearEquiv.sumArrowLequivProdArrow J J' F F
  have h : (Matrix.fromBlocks A 0 0 B).mulVecLin =
      e.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap B.mulVecLin) ∘ₗ d.toLinearMap := by
    apply LinearMap.ext
    intro x
    ext (i | i) <;> simp [Matrix.fromBlocks_mulVec, e, d] <;> rfl
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq, LinearMap.range_prodMap]
  let e2 : ((LinearMap.range A.mulVecLin).prod (LinearMap.range B.mulVecLin)) ≃ₗ[F]
      (LinearMap.range A.mulVecLin) × (LinearMap.range B.mulVecLin) :=
    { toFun := fun x => (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
      invFun := fun y => ⟨(y.1.1, y.2.1), Submodule.mem_prod.mpr ⟨y.1.2, y.2.2⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e2.finrank_eq, Module.finrank_prod]
  rfl
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped BigOperators Classical
namespace Crossing
variable {I : Type*} (s : I → Prop) [DecidablePred s]
abbrev cutEquiv (B : I → Type*) := Equiv.piEquivPiSubtypeProd s B
private theorem cut_symm_left {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // s i}) :
      (cutEquiv s D).symm (u,v) i = u i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
private theorem cut_symm_right {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // ¬ s i}) :
      (cutEquiv s D).symm (u,v) i = v i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
def cutMatrix {K : Type*} {B : I → Type*} (T : (∀ i, B i) → K) :
    Matrix (∀ i : {i // s i}, B i) (∀ i : {i // ¬ s i}, B i) K :=
  fun r c ↦ T ((cutEquiv s B).symm (r, c))
variable {K : Type*} [Field K] [Fintype I] {A B : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
omit [∀ i, Fintype (B i)] in
theorem cutMatrix_factor_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) :
    ∃ (P : Matrix (∀ i : {i // s i}, B i) (∀ i : {i // s i}, A i) K)
      (Q : Matrix (∀ i : {i // ¬ s i}, A i) (∀ i : {i // ¬ s i}, B i) K),
      cutMatrix s X = P * cutMatrix s Y * Q := by
  classical
  obtain ⟨M, hm⟩ := h
  let P : Matrix (∀ i : {i // s i}, B i) (∀ i : {i // s i}, A i) K :=
    fun r a ↦ ∏ i : {i // s i}, M i.val (r i) (a i)
  let Q : Matrix (∀ i : {i // ¬ s i}, A i) (∀ i : {i // ¬ s i}, B i) K :=
    fun a c ↦ ∏ i : {i // ¬ s i}, M i.val (c i) (a i)
  refine ⟨P, Q, ?_⟩
  ext r c
  rw [cutMatrix, hm, ← Equiv.sum_comp (cutEquiv s A).symm, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Fintype.prod_subtype_mul_prod_subtype s]
  simp only [cut_symm_left, cut_symm_right, P, Q, cutMatrix]
  ring
theorem cutMatrix_rank_le_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) : (cutMatrix s X).rank ≤ (cutMatrix s Y).rank := by
  obtain ⟨P, Q, e⟩ := cutMatrix_factor_of_restriction s X Y h
  rw [e]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
end Crossing
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators Classical
noncomputable section
section
private theorem rank_eq_rank_on_support {K R C R' C' : Type*} [Field K]
    [Fintype R'] [Fintype C'] [Fintype C] (M : Matrix R C K)
    (r : R' ↪ R) (c : C' ↪ C)
    (hr : ∀ x ∉ Set.range r, ∀ y, M x y = 0)
    (hc : ∀ y ∉ Set.range c, ∀ x, M x y = 0) :
    M.rank = (M.submatrix r c).rank := by
  classical
  let P : Matrix R R' K := fun i a => if i = r a then 1 else 0
  let Q : Matrix C' C K := fun b j => if c b = j then 1 else 0
  have left (x : R) (b : C') : (P * M.submatrix r c) x b = M x (c b) := by
    rw [Matrix.mul_apply]
    by_cases hx : x ∈ Set.range r
    · obtain ⟨a, rfl⟩ := hx
      simp [P, Matrix.submatrix, r.injective.eq_iff, ite_mul]
    · have h (a : R') : x ≠ r a := fun e => hx ⟨a, e.symm⟩
      simp [P, h, hr _ hx]
  have eq : M = P * M.submatrix r c * Q := by
    ext x y
    rw [Matrix.mul_apply]
    simp only [left]
    by_cases hy : y ∈ Set.range c
    · obtain ⟨b, rfl⟩ := hy
      simp [Q, c.injective.eq_iff, mul_ite]
    · have h (b : C') : c b ≠ y := fun e => hy ⟨b, e⟩
      simp [Q, h, hc _ hy]
  exact le_antisymm (calc
    M.rank = (P * M.submatrix r c * Q).rank := congrArg Matrix.rank eq
    _ ≤ (P * M.submatrix r c).rank := Matrix.rank_mul_le_left _ _
    _ ≤ _ := Matrix.rank_mul_le_right _ _) (Matrix.rank_submatrix_le M r c)
namespace SiteTensor
private def homogeneousTags {J : Type*} [Nonempty J] (A B : J → Type*) :
    ((∀ j, A j) ⊕ (∀ j, B j)) ↪ (∀ j, A j ⊕ B j) where
  toFun := Sum.elim (fun a j => Sum.inl (a j)) (fun b j => Sum.inr (b j))
  inj' := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (funext fun j => Sum.inl.inj (congrFun h j))
    · cases congrFun h (Classical.arbitrary J)
    · cases congrFun h (Classical.arbitrary J)
    · exact congrArg Sum.inr (funext fun j => Sum.inr.inj (congrFun h j))
@[simp] private theorem homogeneousTags_inl {J : Type*} [Nonempty J] (A B : J → Type*)
    (a : ∀ j, A j) (j : J) : homogeneousTags A B (Sum.inl a) j = Sum.inl (a j) := rfl
@[simp] private theorem homogeneousTags_inr {J : Type*} [Nonempty J] (A B : J → Type*)
    (b : ∀ j, B j) (j : J) : homogeneousTags A B (Sum.inr b) j = Sum.inr (b j) := rfl
variable {I K : Type*} {A B : I → Type*}
variable (s : I → Prop) [DecidablePred s] [Fintype I] [Field K]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
open Crossing
theorem cutMatrix_rank_sumCoeff [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (sumCoeff T U)).rank = (cutMatrix s T).rank + (cutMatrix s U).rank := by
  classical
  let : Nonempty I := ⟨(Classical.arbitrary {i // s i}).val⟩
  let r := homogeneousTags (fun i : {i // s i} => A i) (fun i => B i)
  let c := homogeneousTags (fun i : {i // ¬ s i} => A i) (fun i => B i)
  let M := cutMatrix s (sumCoeff T U)
  have support (x y) (h : x ∉ Set.range r ∨ y ∉ Set.range c) : M x y = 0 := by
    apply sumCoeff_mixed
    · intro a he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inl (fun i => a i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inl (fun i => a i), congrArg Prod.snd e⟩)
    · intro b he
      have e := (cutEquiv s (fun i => A i ⊕ B i)).apply_symm_apply (x,y)
      rw [← he] at e
      exact h.elim (fun hx => hx ⟨Sum.inr (fun i => b i), congrArg Prod.fst e⟩)
        (fun hy => hy ⟨Sum.inr (fun i => b i), congrArg Prod.snd e⟩)
  have block : M.submatrix r c = Matrix.fromBlocks (cutMatrix s T) 0 0 (cutMatrix s U) := by
    ext x y
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change sumCoeff T U _ = T _
        convert sumCoeff_inl T U ((cutEquiv s A).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
      | inr y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
    | inr x =>
      cases y with
      | inl y =>
        apply sumCoeff_mixed
        · intro a he
          have h := congrFun he (Classical.arbitrary {i // s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // s i}).property] at h
        · intro b he
          have h := congrFun he (Classical.arbitrary {i // ¬ s i}).val
          simp [r, c, cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
            (Classical.arbitrary {i // ¬ s i}).property] at h
      | inr y =>
        change sumCoeff T U _ = U _
        convert sumCoeff_inr T U ((cutEquiv s B).symm (x,y)) using 1
        congr 1
        funext i
        by_cases hi : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply,
          r, c, hi]
  change M.rank = _
  rw [rank_eq_rank_on_support M r c (fun x hx y => support x y (Or.inl hx))
    (fun y hy x => support x y (Or.inr hy)), block, rank_fromBlocks_diagonal]
namespace Raw
universe v
theorem cutMatrix_rank_zero (F : Type*) [Field F] :
    (cutMatrix s (zero.{v} I F).coeff).rank = 0 :=
  Matrix.rank_zero
theorem cutMatrix_rank_one (F : Type*) [Field F] :
    (cutMatrix s (one.{v} I F).coeff).rank = 1 := by
  classical
  let r : ({i // s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  let c : ({i // ¬s i} → PUnit.{v+1}) ≃ Unit := Equiv.ofUnique _ _
  have eq : cutMatrix s (one.{v} I F).coeff = (1 : Matrix Unit Unit F).submatrix r c := by
    ext x y
    change 1 = (1 : Matrix Unit Unit F) (r x) (c y)
    simp
  rw [eq]
  exact (Matrix.rank_submatrix (1 : Matrix Unit Unit F) r c).trans
    ((Matrix.rank_one (R := F)).trans Fintype.card_unit)
end Raw
end SiteTensor
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Kronecker
theorem rank_kronecker {K m n p q : Type*} [Field K]
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n K) (B : Matrix p q K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  let bm := Pi.basisFun K m
  let bn := Pi.basisFun K n
  let bp := Pi.basisFun K p
  let bq := Pi.basisFun K q
  rw [(A ⊗ₖ B).rank_eq_finrank_range_toLin (bm.tensorProduct bp) (bn.tensorProduct bq),
    Matrix.toLin_kronecker, A.rank_eq_finrank_range_toLin bm bn,
    B.rank_eq_finrank_range_toLin bp bq, TensorProduct.range_map, ← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _),
    Module.finrank_tensorProduct]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Classical Kronecker
noncomputable section
namespace SiteTensor
open Crossing
variable {I K : Type*} (s : I → Prop) [DecidablePred s] {A B : I → Type*}
theorem cutMatrix_product [Mul K] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2)) =
      ((cutMatrix s T) ⊗ₖ (cutMatrix s U)).submatrix
        (Equiv.arrowProdEquivProdArrow {i // s i} (fun i ↦ A i.val) (fun i ↦ B i.val))
        (Equiv.arrowProdEquivProdArrow {i // ¬s i} (fun i ↦ A i.val) (fun i ↦ B i.val)) := by
  ext r c
  change T _ * U _ = T _ * U _
  apply congrArg₂ (· * ·)
  · apply congrArg T
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]
  · apply congrArg U
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]
theorem cutMatrix_rank_product [Field K] [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2))).rank =
      (cutMatrix s T).rank * (cutMatrix s U).rank := by
  rw [cutMatrix_product, Matrix.rank_submatrix, rank_kronecker]
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped NNReal Classical
noncomputable section
namespace SiteTensor
universe v u w
open Crossing
variable {I : Type u} (s : I → Prop) [DecidablePred s] [Fintype I] (K : Type w) [Field K]
def cutRank : TensorClass.{v} I K → ℕ :=
  Quotient.lift (fun X : Raw.{v} I K => (cutMatrix s X.coeff).rank) fun X Y h =>
    le_antisymm (cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h.1)
      (cutMatrix_rank_le_of_restriction s Y.coeff X.coeff h.2)
@[simp] theorem cutRank_ofRaw (X : Raw.{v} I K) :
    cutRank s K (ofRaw X) = (cutMatrix s X.coeff).rank := rfl
theorem monotone_cutRank : Monotone (cutRank.{v} s K) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun X Y h => ?_
  exact cutMatrix_rank_le_of_restriction s X.coeff Y.coeff h
variable [Nonempty I] [Nonempty {i // s i}] [Nonempty {i // ¬ s i}]
def cutSpectrum : normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y) := by
  refine ⟨fun x => (cutRank s K x : ℝ≥0), ?_, ?_, ?_, ?_, ?_⟩
  · change ((cutMatrix s (Raw.zero.{v} I K).coeff).rank : ℝ≥0) = 0
    rw [Raw.cutMatrix_rank_zero, Nat.cast_zero]
  · change ((cutMatrix s (Raw.one.{v} I K).coeff).rank : ℝ≥0) = 1
    rw [Raw.cutMatrix_rank_one, Nat.cast_one]
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (sumCoeff X.coeff Y.coeff)).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) + (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_sumCoeff s X.coeff Y.coeff
  · intro x y
    refine Quotient.inductionOn₂ x y fun X Y => ?_
    change ((cutMatrix s (X.mul Y).coeff).rank : ℝ≥0) =
      ((cutMatrix s X.coeff).rank : ℝ≥0) * (cutMatrix s Y.coeff).rank
    exact_mod_cast cutMatrix_rank_product s X.coeff Y.coeff
  · exact fun x y h => Nat.cast_le.mpr ((monotone_cutRank s K) h)
@[simp] theorem cutSpectrum_ofRaw (X : Raw.{v} I K) :
    (cutSpectrum s K).val (ofRaw X) = ((cutMatrix s X.coeff).rank : ℝ≥0) := rfl
theorem spectrum_nonempty (I : Type u) [Fintype I] [Nontrivial I] (K : Type w) [Field K] :
    (normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y)).Nonempty := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  let s (x : I) := x = i
  let : Nonempty {x // s x} := ⟨⟨i, rfl⟩⟩
  let : Nonempty {x // ¬ s x} := ⟨⟨j, Ne.symm hij⟩⟩
  exact Set.nonempty_of_mem (cutSpectrum.{v} s K).property
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem degreeProfiles_nonempty [Nonempty ι] (m : ℕ) :
    (piAntidiag (univ : Finset ι) m).Nonempty := by
  let i := Classical.arbitrary ι
  refine ⟨fun j ↦ if j = i then m else 0, ?_⟩
  simp
theorem degreeProfiles_card_le (m : ℕ) :
    (piAntidiag (univ : Finset ι) m).card ≤ (m + 1) ^ Fintype.card ι := by
  let S := piAntidiag (univ : Finset ι) m
  let encode (k : S) (i : ι) : Fin (m + 1) :=
    ⟨k.val i, Nat.lt_succ_of_le (by
      rw [← (mem_piAntidiag.mp k.property).1]
      exact single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i))⟩
  have h : Function.Injective encode := by
    intro k l hkl
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hkl i)
  simpa [S] using Fintype.card_le_of_injective encode h
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Finset
open scoped NNReal
variable {A : Type*} [CommSemiring A] (v : A →* ℝ≥0) {p : ℝ} (hp : 0 < p) (hnat : ∀ n : ℕ, 0 < n → v (n : A) = (n : ℝ≥0) ^ p)
noncomputable def normalizeSpectral (p : ℝ) : A →* ℝ≥0 := (NNReal.rpowMonoidHom p⁻¹).comp v
include hp hnat in
private theorem normalizeSpectral_natCast (n : ℕ) (hn : 0 < n) :
    normalizeSpectral v p (n : A) = (n : ℝ≥0) := by
  change v (n : A) ^ p⁻¹ = _
  rw [hnat n hn, ← NNReal.rpow_mul, mul_inv_cancel₀ hp.ne', NNReal.rpow_one]
include hp hnat in
theorem normalizeSpectral_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (hadd : ∀ x y, v (x + y) ≤ v x + v y) (hsub : ∀ x y, v x ≤ v (x + y)) (x : ι → A) :
    normalizeSpectral v p (∑ i, x i) = ∑ i, normalizeSpectral v p (x i) := by
  classical
  let w := normalizeSpectral v p
  let a := ∑ i, x i
  let b := ∑ i, w (x i)
  have hw (z : A) : w z ^ p = v z := by
    change (v z ^ p⁻¹) ^ p = v z
    rw [← NNReal.rpow_mul, inv_mul_cancel₀ hp.ne', NNReal.rpow_one]
  have hpow (m : ℕ) : v a ^ m ≤ ((m : ℝ≥0) + 1) ^ Fintype.card ι * (b ^ p)^m ∧
      b^m ≤ ((m : ℝ≥0) + 1) ^ Fintype.card ι * (w a)^m := by
    let J := (univ : Finset ι).piAntidiag m
    let t (k : ι → ℕ) : A := (Nat.multinomial univ k : A) * ∏ i, (x i)^(k i)
    have ha : a ^ m = ∑ k ∈ J, t k := Finset.sum_pow_eq_sum_piAntidiag univ x m
    have hb : b ^ m = ∑ k ∈ J, w (t k) := by
      dsimp only [b]
      rw [Finset.sum_pow_eq_sum_piAntidiag]
      apply Finset.sum_congr rfl
      intro k _
      simp only [t, map_mul, map_prod, map_pow]
      rw [show w (Nat.multinomial univ k : A) = (Nat.multinomial univ k : ℝ≥0) from
        normalizeSpectral_natCast v hp hnat _ (Nat.multinomial_pos univ k)]
    have hcard : (J.card : ℝ≥0) ≤ ((m : ℝ≥0) + 1)^Fintype.card ι := by
      exact_mod_cast degreeProfiles_card_le (ι := ι) m
    constructor
    · have hterm (k : ι → ℕ) (hk : k ∈ J) : v (t k) ≤ (b ^ p)^m := by
        rw [← hw, ← NNReal.rpow_mul_natCast, mul_comm p (m : ℝ), NNReal.rpow_natCast_mul]
        apply NNReal.rpow_le_rpow _ hp.le
        rw [hb]
        exact Finset.single_le_sum (f := fun j => w (t j)) (fun _ _ => by positivity) hk
      rw [← map_pow, ha]
      calc
        v (∑ k ∈ J, t k) ≤ ∑ k ∈ J, v (t k) :=
          Finset.le_sum_nonempty_of_subadditive v hadd (degreeProfiles_nonempty m) t
        _ ≤ ∑ _k ∈ J, (b^p)^m := sum_le_sum hterm
        _ = (J.card : ℝ≥0) * (b^p)^m := by simp
        _ ≤ _ := by gcongr
    · have hterm (k : ι → ℕ) (hk : k ∈ J) : w (t k) ≤ (w a)^m := by
        rw [← map_pow, ha, ← J.add_sum_erase t hk]
        exact NNReal.rpow_le_rpow (hsub _ _) (inv_nonneg.mpr hp.le)
      rw [hb]
      calc
        ∑ k ∈ J, w (t k) ≤ ∑ _k ∈ J, (w a)^m := sum_le_sum hterm
        _ = (J.card : ℝ≥0) * (w a)^m := by simp
        _ ≤ _ := by gcongr
  change w a = b
  apply le_antisymm
  · apply (NNReal.rpow_le_rpow_iff hp).mp
    rw [hw]
    exact nnreal_le_of_pow_le_polynomial_mul_pow _ fun m _ => (hpow m).1
  · exact nnreal_le_of_pow_le_polynomial_mul_pow _ fun m _ => (hpow m).2
include hp hnat in
noncomputable def normalizeSpectralHom (hzero : v 0 = 0)
    (hadd : ∀ x y, v (x + y) ≤ v x + v y) (hsub : ∀ x y, v x ≤ v (x + y)) : A →+* ℝ≥0 where
  __ := normalizeSpectral v p
  map_zero' := by
    change v 0 ^ p⁻¹ = 0
    rw [hzero, NNReal.zero_rpow (inv_ne_zero hp.ne')]
  map_add' a b := by
    simpa [Fin.sum_univ_two] using normalizeSpectral_sum v hp hnat hadd hsub ![a, b]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped NNReal
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
theorem exists_le_natCast (X : TensorClass.{v} I K) : ∃ n : ℕ, X ≤ n := by
  classical
  induction X using Quotient.inductionOn with
  | _ T =>
    refine ⟨Fintype.card (∀ i, T.Leg i), ?_⟩
    change ofRaw T ≤ (Fintype.card (∀ i, T.Leg i) : TensorClass.{v} I K)
    simpa only [ofRaw_diagonal_eq_natCast, Fintype.card_ulift, Fintype.card_fin] using
        (ofRaw_le_iff.mpr (T.restricts_diagonal I))
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped BigOperators Classical
universe v
variable {I K : Type*} {α β : Type v} [Fintype I] [CommSemiring K]
namespace Raw
theorem diagonal_coeff_at (i₀ : I) [Fintype α] (x : I → α) :
    (diagonal I K α).coeff x = if ∀ i, x i = x i₀ then 1 else 0 := by
  classical
  simp only [diagonal]
  rw [Finset.sum_eq_single (x i₀)]
  · simp [funext_iff]
  · intro b _ hb
    apply ite_eq_right
    intro hx
    exact hb (congrFun hx i₀).symm
  · simp
theorem diagonal_product_equivalent [Nonempty I] [Fintype α] [Fintype β] :
    ((diagonal I K α).mul (diagonal I K β)).Equivalent (diagonal I K (α × β)) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  apply reindex_equivalent (X := (diagonal I K α).mul (diagonal I K β))
    (Y := diagonal I K (α × β)) (fun _ => Equiv.refl _)
  intro (x : I → α × β)
  change (diagonal I K α).coeff (fun i => (x i).1) *
    (diagonal I K β).coeff (fun i => (x i).2) = (diagonal I K (α × β)).coeff x
  simp only [diagonal_coeff_at i₀, Prod.ext_iff, forall_and,
    ← ite_and, ite_mul, one_mul, zero_mul]
end Raw
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
open scoped BigOperators Classical
universe v u w z
noncomputable section
variable {S : Type u} (O : Type z) {K : Type w}
def withTrivial (X : Raw.{v} S K) : Raw.{v} (S ⊕ O) K where
  Leg := Sum.elim X.Leg (fun _ => PUnit)
  finiteLeg := Sum.rec (fun s => X.finiteLeg s) (fun _ => inferInstanceAs (Fintype PUnit))
  coeff x := X.coeff (fun s => x (.inl s))
def withTrivialIndex (X : Raw.{v} S K) :
    (∀ i, (withTrivial O X).Leg i) ≃ (∀ s, X.Leg s) where
  toFun x s := x (.inl s)
  invFun x := Sum.rec x fun _ => PUnit.unit
  left_inv x := by funext i; cases i <;> rfl
  right_inv _ := rfl
variable [Fintype S] [Fintype O] [CommSemiring K]
theorem withTrivial_restricts {X Y : Raw.{v} S K} (h : X.Restricts Y) :
    (withTrivial O X).Restricts (withTrivial O Y) := by
  classical
  let : DecidableEq (S ⊕ O) := Classical.decEq _
  obtain ⟨M, hM⟩ := h
  let N (i : S ⊕ O) : (withTrivial O X).Leg i → (withTrivial O Y).Leg i → K :=
    match i with
    | .inl s => M s
    | .inr _ => fun _ _ => 1
  refine ⟨N, fun x => ?_⟩
  rw [show (withTrivial O X).coeff x = _ from hM (fun s => x (.inl s))]
  exact Fintype.sum_equiv (withTrivialIndex O Y).symm _ _ (fun a => by
    simp [withTrivialIndex, withTrivial, Fintype.prod_sum_type, N]
    rfl)
theorem withTrivial_mul_equivalent (X Y : Raw.{v} S K) :
    (withTrivial O (mul X Y)).Equivalent (mul (withTrivial O X) (withTrivial O Y)) := by
  let e (i : S ⊕ O) : (withTrivial O (mul X Y)).Leg i ≃
      (mul (withTrivial O X) (withTrivial O Y)).Leg i := match i with
    | .inl _ => Equiv.refl _
    | .inr _ => ⟨fun _ => (PUnit.unit, PUnit.unit), fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩
  exact reindex_equivalent e (fun _ => rfl)
theorem withTrivial_one_equivalent :
    (withTrivial O (one S K : Raw.{v} S K)).Equivalent (one (S ⊕ O) K) := by
  apply reindex_equivalent (fun i => ?_)
  · intro x; rfl
  · cases i <;> exact Equiv.refl _
end
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped NNReal
noncomputable section
variable (S O K : Type*) [Fintype S] [Fintype O] [Nonempty S] [CommSemiring K]
def Raw.supportDiagonal (α : Type) [Fintype α] : Raw.{0} (S ⊕ O) K :=
  Raw.withTrivial O (Raw.diagonal S K α)
def supportDiagonalHom : ℕ →* TensorClass.{0} (S ⊕ O) K where
  toFun n := ofRaw (Raw.supportDiagonal S O K (Fin n))
  map_one' := by
    have he := (Raw.diagonal_equiv S K (Equiv.ofUnique (Fin 1) PUnit))
    have hu := Raw.diagonal_unit_equivalent.{0} S K
    have h (X Y : Raw.{0} S K) (hXY : X.Equivalent Y) :
        ofRaw (Raw.withTrivial O X) = ofRaw (Raw.withTrivial O Y) :=
      ofRaw_eq_iff.mpr ⟨Raw.withTrivial_restricts O hXY.1, Raw.withTrivial_restricts O hXY.2⟩
    exact (h _ _ he).trans ((h _ _ hu).trans
      (ofRaw_eq_iff.mpr (Raw.withTrivial_one_equivalent O)))
  map_mul' n m := by
    have he := Raw.diagonal_equiv S K (finProdFinEquiv (m := n) (n := m)).symm
    have hm := (Raw.diagonal_product_equivalent (I := S) (K := K) (α := Fin n) (β := Fin m))
    have h (X Y : Raw.{0} S K) (hXY : X.Equivalent Y) :
        ofRaw (Raw.withTrivial O X) = ofRaw (Raw.withTrivial O Y) :=
      ofRaw_eq_iff.mpr ⟨Raw.withTrivial_restricts O hXY.1, Raw.withTrivial_restricts O hXY.2⟩
    exact (h _ _ he).trans ((h _ _ hm).symm.trans
      (ofRaw_eq_iff.mpr (Raw.withTrivial_mul_equivalent O _ _)))
theorem supportDiagonalHom_mono : Monotone (supportDiagonalHom S O K) := by
  intro n m h
  exact Raw.withTrivial_restricts O (Raw.diagonal_restricts_of_embedding S K (Fin.castLEEmb h))
theorem supportDiagonal_log_price
    (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (S ⊕ O) K → _ → Prop))
    {q : ℕ} (hq : 0 < q) :
    Real.logb 2 (f.val (ofRaw (Raw.supportDiagonal S O K (Fin q))) : ℝ) =
      Real.logb 2 (f.val (ofRaw (Raw.supportDiagonal S O K (Fin 2))) : ℝ) * Real.logb 2 q := by
  let v := (normalizedSpectrum.toRingHom f).toMonoidHom.comp (supportDiagonalHom S O K)
  apply spectral_natCast_logb (A := ℕ) (v := v) _ q hq
  intro a b _ hab
  exact f.property.2.2.2.2 _ _ (supportDiagonalHom_mono S O K hab)
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators NNReal
namespace SiteTensor
theorem ordinary_add_restricts {I K : Type*} [Fintype I] [CommSemiring K]
    {A : I → Type*} [∀ i, Fintype (A i)] (T U : (∀ i, A i) → K) :
    Crossing.IsRestriction (T + U) (sumCoeff T U) := by
  classical
  let fold (i : I) (a : A i) (s : A i ⊕ A i) : K := if Sum.elim id id s = a then 1 else 0
  refine ⟨fold, fun x => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  rw [sum_pushCoeff_mul, sum_pushCoeff_mul]
  have elim (V : (∀ i, A i) → K) :
      (∑ a, V a * ∏ i, (if a i = x i then (1 : K) else 0)) = V x := by
    simp_rw [Fintype.prod_boole]
    simp [← funext_iff, mul_ite]
  exact congrArg₂ (· + ·) (elim T).symm (elim U).symm
universe v
noncomputable section
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {A : I → Type v} [∀ i, Fintype (A i)]
def ofCoeffs (T : (∀ i, A i) → K) : TensorClass.{v} I K :=
  ofRaw ⟨A, inferInstance, T⟩
@[simp] theorem ofCoeffs_zero : ofCoeffs (0 : (∀ i, A i) → K) = 0 := by
  apply ofRaw_eq_iff.mpr
  constructor <;> exact ⟨fun _ _ _ => 0, fun _ => by simp [Raw.zero]⟩
theorem ordinary_sum_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    ofCoeffs (∑ j, T j) ≤ ∑ j, ofCoeffs (T j) := by
  classical
  generalize (Finset.univ : Finset J) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (ofRaw_le_iff.mpr (ordinary_add_restricts _ _)).trans (add_mono le_rfl ih)
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
def coeffValue (T : (∀ i, A i) → K) : ℝ≥0 := φ.val (ofCoeffs T)
@[simp] theorem coeffValue_zero : coeffValue φ (0 : (∀ i, A i) → K) = 0 := by
  simp [coeffValue, φ.2.1]
theorem ordinary_sum_value_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    coeffValue φ (∑ j, T j) ≤ ∑ j, coeffValue φ (T j) := by
  have h := φ.2.2.2.2.2 _ _ (ordinary_sum_le T)
  change coeffValue φ (∑ j, T j) ≤ normalizedSpectrum.toRingHom φ (∑ j, ofCoeffs (T j)) at h
  rw [map_sum] at h
  exact h
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
open scoped BigOperators Classical
universe v u w z
variable {S : Type u} (O : Type z) {K : Type w} [Fintype S] [Fintype O] [CommSemiring K]
theorem withTrivial_add_restricts (X Y : Raw.{v} S K) :
    (withTrivial O (add X Y)).Restricts (add (withTrivial O X) (withTrivial O Y)) := by
  classical
  let : DecidableEq (S ⊕ O) := Classical.decEq _
  let M (i : S ⊕ O) : (withTrivial O (add X Y)).Leg i →
      (add (withTrivial O X) (withTrivial O Y)).Leg i → K := match i with
    | .inl _ => fun x a => if a = x then 1 else 0
    | .inr _ => fun _ _ => 1
  refine ⟨M, fun x => ?_⟩
  change sumCoeff X.coeff Y.coeff (fun s => x (.inl s)) =
    ∑ a, sumCoeff (withTrivial O X).coeff (withTrivial O Y).coeff a *
      ∏ i, M i (x i) (a i)
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib]
  rw [sum_pushCoeff_mul, sum_pushCoeff_mul]
  have weight {B : S → Type v} (a b : ∀ i, B i) (q : K) :
      (@ite K (a = b) (Classical.propDecidable _) q 0) = q * ∏ i, (if a i = b i then (1 : K) else 0) := by
    simp [Fintype.prod_boole, ← funext_iff, mul_ite]
  congr 1
  · unfold pushCoeff
    refine Fintype.sum_equiv (withTrivialIndex O X).symm _ _ (fun a => ?_)
    simp only [withTrivial, withTrivialIndex, Fintype.prod_sum_type, M, Finset.prod_const_one,
      mul_one]
    exact weight (B := fun s => X.Leg s ⊕ Y.Leg s) (fun s => .inl (a s)) (fun s => x (.inl s)) (X.coeff a)
  · unfold pushCoeff
    refine Fintype.sum_equiv (withTrivialIndex O Y).symm _ _ (fun a => ?_)
    simp only [withTrivial, withTrivialIndex, Fintype.prod_sum_type, M, Finset.prod_const_one,
      mul_one]
    exact weight (B := fun s => X.Leg s ⊕ Y.Leg s) (fun s => .inr (a s)) (fun s => x (.inl s)) (Y.coeff a)
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped BigOperators NNReal
namespace SiteTensor
universe v
variable {S O K : Type*} [Fintype S] [Fintype O] [Nonempty S] [CommSemiring K]
def withTrivialHom (O : Type*) [Fintype O] :
    TensorClass.{v} S K →* TensorClass.{v} (S ⊕ O) K where
  toFun := Quotient.map (Raw.withTrivial O) (fun _ _ h =>
    ⟨Raw.withTrivial_restricts O h.1, Raw.withTrivial_restricts O h.2⟩)
  map_one' := ofRaw_eq_iff.mpr (Raw.withTrivial_one_equivalent O)
  map_mul' X Y := Quotient.inductionOn₂ X Y fun x y =>
    ofRaw_eq_iff.mpr (Raw.withTrivial_mul_equivalent O x y)
theorem withTrivialHom_mono : Monotone (withTrivialHom (S := S) (K := K) O) := by
  intro X Y
  exact Quotient.inductionOn₂ X Y (fun _ _ => Raw.withTrivial_restricts O)
theorem withTrivialHom_add_le (X Y : TensorClass.{v} S K) :
    withTrivialHom O (X + Y) ≤ withTrivialHom O X + withTrivialHom O Y :=
  Quotient.inductionOn₂ X Y (Raw.withTrivial_add_restricts O)
@[simp] theorem withTrivialHom_zero :
    withTrivialHom O (0 : TensorClass.{v} S K) = 0 :=
  (ofRaw_eq_zero_iff _).mpr rfl
theorem withTrivialHom_natCast (n : ℕ) :
    withTrivialHom O (n : TensorClass.{0} S K) = supportDiagonalHom S O K n := by
  rw [← ofRaw_diagonal_fin_eq_natCast S K n]
  rfl
section Field
variable {F : Type*} [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (S ⊕ O) F → _ → Prop))
variable {A : S → Type} [∀ s, Fintype (A s)]
theorem subset_log_price_eq_zero_of_diagonal
    (hδ : Real.logb 2 (φ.val (ofRaw (Raw.supportDiagonal S O F (Fin 2)))) = 0)
    (X : TensorClass.{0} S F) :
    Real.logb 2 (φ.val (withTrivialHom O X)) = 0 := by
  by_cases hx : X = 0
  · simp [hx, φ.property.1]
  obtain ⟨n, hn⟩ := exists_le_natCast X
  have hn' : 0 < n := by
    by_contra! h
    have h0 : n = 0 := by omega
    exact hx (le_antisymm (by simpa [h0] using hn) (zero_le_tensor _))
  have hlow := φ.property.2.2.2.2 _ _ (withTrivialHom_mono (O := O) (one_le_of_ne_zero hx))
  simp only [map_one, φ.property.2.1] at hlow
  have hhi := φ.property.2.2.2.2 _ _ (withTrivialHom_mono (O := O) hn)
  rw [withTrivialHom_natCast] at hhi
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast zero_lt_one.trans_le hlow) (by exact_mod_cast hhi)
  have hd := supportDiagonal_log_price S O F φ hn'
  rw [hδ, zero_mul] at hd
  exact le_antisymm (hlog.trans_eq hd) (Real.logb_nonneg (by norm_num) (by exact_mod_cast hlow))
end Field
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open Real
open scoped NNReal
noncomputable section
variable {S O K : Type*} [Fintype S] [Fintype O] [Nonempty S] [CommSemiring K] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (S ⊕ O) K → _ → Prop))
def subsetDiagonalExponent : ℝ := logb 2 (φ.val (ofRaw (Raw.supportDiagonal S O K (Fin 2))))
def normalizedSubsetPoint (hp : 0 < subsetDiagonalExponent φ) :
    normalizedSpectrum ((· ≤ ·) : TensorClass.{0} S K → _ → Prop) := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (withTrivialHom (S := S) O)
  have hm : Monotone v := fun _ _ h => φ.2.2.2.2.2 _ _ (withTrivialHom_mono h)
  have hn {a b : ℕ} (_ : 0 < a) (h : a ≤ b) : v (a : TensorClass.{0} S K) ≤ v b := by
    apply hm
    rw [← ofRaw_diagonal_fin_eq_natCast S K a, ← ofRaw_diagonal_fin_eq_natCast S K b]
    exact Raw.diagonal_restricts_of_embedding S K (Fin.castLEEmb h)
  have hdiag : logb 2 (v 2) = subsetDiagonalExponent φ := congrArg (fun z => logb 2 (φ.val z))
    (withTrivialHom_natCast (S := S) (O := O) (K := K) 2)
  let F : TensorClass.{0} S K →+* ℝ≥0 := normalizeSpectralHom v hp (fun n hn' => by
    rw [← hdiag]; exact spectral_natCast_eq_rpow v hn n hn')
    ((congrArg φ.val withTrivialHom_zero).trans φ.2.1)
    (fun x y => (φ.2.2.2.2.2 _ _ (withTrivialHom_add_le x y)).trans_eq (φ.2.2.2.1 _ _))
    (fun x y => hm (by simpa only [add_zero] using add_mono (le_refl x) (zero_le_tensor y)))
  exact ⟨F, map_zero F, map_one F, map_add F, map_mul F, fun _ _ h =>
    NNReal.rpow_le_rpow (hm h) (inv_nonneg.mpr hp.le)⟩
theorem normalizedSubsetPoint_apply (hp : 0 < subsetDiagonalExponent φ) (X : TensorClass.{0} S K) :
    (normalizedSubsetPoint φ hp).val X =
      φ.val (withTrivialHom O X) ^ (subsetDiagonalExponent φ)⁻¹ := rfl
theorem normalizedSubsetPoint_price (hp : 0 < subsetDiagonalExponent φ)
    (X : TensorClass.{0} S K) (c : ℝ) :
    c * logb 2 (φ.val (withTrivialHom O X)) =
      (c * subsetDiagonalExponent φ) * logb 2 ((normalizedSubsetPoint φ hp).val X) := by
  rw [normalizedSubsetPoint_apply, NNReal.coe_rpow]
  by_cases hz : φ.val (withTrivialHom O X) = 0
  · simp [hz, Real.zero_rpow (inv_ne_zero hp.ne')]
  have hpos : 0 < (φ.val (withTrivialHom O X) : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hz)
  rw [Real.logb_rpow_eq_mul_logb_of_pos hpos]
  field_simp
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
noncomputable section
variable {I J : Type} {F : Type*} [Fintype I] [Fintype J] [Field F]
theorem Raw.group_withTrivial_equivalent (σ : I → J) (T : Raw.{0} I F) :
    ((T.withTrivial J).group (Sum.elim σ id)).Equivalent (T.group σ) := by
  let e (j : J) : (((T.withTrivial J).group (Sum.elim σ id)).Leg j) ≃ (T.group σ).Leg j :=
    { toFun := fun x i => x ⟨.inl i.val, i.property⟩
      invFun := fun y i => match i with
        | ⟨.inl k, h⟩ => y ⟨k, h⟩
        | ⟨.inr _, _⟩ => PUnit.unit
      left_inv := by
        intro x
        funext i
        rcases i with ⟨k | k, h⟩ <;> rfl
      right_inv := fun _ => rfl }
  exact Raw.reindex_equivalent e (fun _ => rfl)
variable [Nontrivial I] [Nonempty J]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J F → _ → Prop))
theorem rawLogPrice_group_placement (σ : I → J) (c : ℝ) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I F → _ → Prop),
      ∀ T : Raw.{0} I F, rawLogPrice φ c (T.group σ) =
        rawLogPrice φ c ((Raw.diagonal I F (Fin 2)).group σ) *
          Real.logb 2 (ψ.val (ofRaw T) : ℝ) := by
  let f : I ⊕ J → J := Sum.elim σ id
  have hf : Function.Surjective f := fun j => ⟨Sum.inr j, rfl⟩
  let χ := groupSpectralPoint f hf φ
  have eval (T : Raw.{0} I F) :
      χ.val (withTrivialHom J (ofRaw T)) = φ.val (ofRaw (T.group σ)) :=
    congrArg φ.val (ofRaw_eq_iff.mpr (Raw.group_withTrivial_equivalent σ T))
  have hd : c * subsetDiagonalExponent χ =
      rawLogPrice φ c ((Raw.diagonal I F (Fin 2)).group σ) :=
    congrArg (fun z : NNReal => c * Real.logb 2 (z : ℝ)) (eval (Raw.diagonal I F (Fin 2)))
  have hp : 0 ≤ subsetDiagonalExponent χ := by
    simpa only [rawLogPrice, one_mul, subsetDiagonalExponent] using
      rawLogPrice_nonneg χ (c := 1) (by norm_num) (Raw.supportDiagonal I J F (Fin 2))
  rcases hp.eq_or_lt with hz | hpos
  · obtain ⟨ψ, hψ⟩ := spectrum_nonempty I F
    refine ⟨⟨ψ, hψ⟩, fun T => ?_⟩
    rw [← hd, ← hz, mul_zero, zero_mul, rawLogPrice, ← eval]
    rw [subset_log_price_eq_zero_of_diagonal χ hz.symm, mul_zero]
  · refine ⟨normalizedSubsetPoint χ hpos, fun T => ?_⟩
    rw [← hd, rawLogPrice, ← eval]
    exact normalizedSubsetPoint_price χ hpos (ofRaw T) c
theorem rawLogPrice_group_embedding (e : I ↪ J) (c : ℝ) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I F → _ → Prop),
      ∀ T : Raw.{0} I F, rawLogPrice φ c (T.group e) =
        rawLogPrice φ c ((Raw.diagonal I F (Fin 2)).group e) *
          Real.logb 2 (ψ.val (ofRaw T) : ℝ) :=
  rawLogPrice_group_placement φ e c
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
universe u v
variable {I J : Type u} {D K : Type*} [Fintype I] [Fintype J] [Fintype D] [CommSemiring K]
theorem group_group_equivalent (T : Raw.{max u v} I K) (p : I → J) (q : J → D) :
    ((T.group p).group q).Equivalent (T.group (q ∘ p)) := by
  apply reindex_equivalent (X := (T.group p).group q) (Y := T.group (q ∘ p)) (fun d => {
    toFun := fun f t => f ⟨p t.1, t.2⟩ ⟨t.1, rfl⟩
    invFun := fun f j i => f ⟨i.1, (congrArg q i.2).trans j.2⟩
    left_inv := by
      intro f
      funext ⟨j, hj⟩ ⟨i, hi⟩
      change p i = j at hi
      subst j
      rfl
    right_inv := fun _ => rfl })
  intro x
  rfl
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K] {A : I → Type*} [∀ i, Fintype (A i)]
theorem scalar_mul_restricts (c : K) (T : (∀ i, A i) → K) :
    Crossing.IsRestriction (c • T) T := by
  classical
  let i₀ := Classical.arbitrary I
  refine ⟨fun i y x ↦ if x = y then (if i = i₀ then c else 1) else 0, fun x ↦ ?_⟩
  simp_rw [Fintype.prod_ite_zero]
  simp [← funext_iff, mul_ite, mul_comm]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open MatrixMultiplication.Foundation
open scoped BigOperators
section
abbrev matrixTensor (F : Type*) [Field F] (n12 n23 n31 : ℕ) :=
  Tensor.matrixCoefficients (K := F) (Fin n31) (Fin n12) (Fin n23)
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {K ι : Type*} [Field K]
def affineZariskiClosure (S : Set (ι → K)) : Set (ι → K) :=
  {x | ∀ p : MvPolynomial ι K, (∀ y ∈ S, MvPolynomial.eval y p = 0) →
    MvPolynomial.eval x p = 0}
theorem subset_affineZariskiClosure (S : Set (ι → K)) : S ⊆ affineZariskiClosure S :=
  fun x hx _ hp ↦ hp x hx
@[simp] theorem affineZariskiClosure_idem (S : Set (ι → K)) :
    affineZariskiClosure (affineZariskiClosure S) = affineZariskiClosure S :=
  Set.Subset.antisymm (fun _ hx p hp ↦ hx p fun _ hy ↦ hy p hp)
    (subset_affineZariskiClosure _)
theorem mapsTo_affineZariskiClosure_of_polynomial {κ : Type*}
    (f : κ → MvPolynomial ι K) {S : Set (ι → K)} {T : Set (κ → K)}
    (hf : Set.MapsTo (fun x j ↦ MvPolynomial.eval x (f j)) S T) :
    Set.MapsTo (fun x j ↦ MvPolynomial.eval x (f j)) (affineZariskiClosure S)
      (affineZariskiClosure T) := by
  intro x hx p hp
  change MvPolynomial.eval (MvPolynomial.eval x ∘ f) p = 0
  rw [MvPolynomial.eval_assoc]
  apply hx
  intro y hy
  rw [← MvPolynomial.eval_assoc]
  exact hp _ (hf hy)
theorem mapsTo_affineZariskiClosure_of_mul (s : ι → K) {S : Set (ι → K)}
    (hs : Set.MapsTo (fun x i ↦ s i * x i) S S) :
    Set.MapsTo (fun x i ↦ s i * x i) (affineZariskiClosure S) (affineZariskiClosure S) := by
  let f (i : ι) : MvPolynomial ι K := MvPolynomial.C (s i) * MvPolynomial.X i
  have heval (x : ι → K) (i : ι) : MvPolynomial.eval x (f i) = s i * x i := by simp [f]
  simpa only [heval] using mapsTo_affineZariskiClosure_of_polynomial f (S := S) (T := S)
    (by simpa only [heval] using hs)
theorem polynomialCurve_zero_mem_affineZariskiClosure [Infinite K]
    (c : ι → Polynomial K) {S : Set (ι → K)}
    (hc : ∀ t : K, t ≠ 0 → (fun i ↦ (c i).eval t) ∈ S) :
    (fun i ↦ (c i).eval 0) ∈ affineZariskiClosure S := by
  intro p hp
  let f : Polynomial K := p.eval₂ Polynomial.C c
  have heval (t : K) : f.eval t = MvPolynomial.eval (fun i ↦ (c i).eval t) p := by
    have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by ext; simp
    rw [show f = p.eval₂ Polynomial.C c from rfl, MvPolynomial.polynomial_eval_eval₂, hC,
      MvPolynomial.eval₂_id]
  have hf : f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.finite_singleton (0 : K)).infinite_compl.mono
    intro t ht
    exact (heval t).trans (hp _ (hc t ht))
  rw [← heval, hf, Polynomial.eval_zero]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {K ι : Type*} [Field K]
def coordinatePower (n : ℕ) (x : ι → K) (w : Fin n → ι) : K := ∏ j, x (w j)
theorem affineZariskiClosure_submodule {κ : Type*} [Fintype κ] (U : Submodule K (κ → K)) :
    affineZariskiClosure (U : Set (κ → K)) = U := by
  classical
  apply Set.Subset.antisymm _ (subset_affineZariskiClosure _)
  intro x hx
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U x).mp
  intro f hf
  let e (i : κ) : κ → K := fun j ↦ if i = j then 1 else 0
  let p : MvPolynomial κ K := ∑ i, MvPolynomial.C (f (e i)) * MvPolynomial.X i
  have hp (y : κ → K) : MvPolynomial.eval y p = f y := by
    have hy : ∑ i, y i • e i = y := by
      ext j
      simp [e, Finset.sum_apply, Pi.smul_apply, mul_ite]
    simpa [p, mul_comm] using congrArg f hy
  rw [← hp x]
  apply hx p
  intro y hy
  rw [hp]
  exact (Submodule.mem_dualAnnihilator f).mp hf y hy
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K] {A : I → Type v} [∀ i, Fintype (A i)]
def groupedPower (n : ℕ) (T : (∀ i, A i) → K) (x : ∀ i, Fin n → A i) : K :=
  coordinatePower n T (fun j i ↦ x i j)
theorem ofRaw_groupedPower (n : ℕ) (T : (∀ i, A i) → K) :
    ofRaw (I := I) (K := K) ⟨fun i ↦ Fin n → A i, fun _ ↦ inferInstance, groupedPower n T⟩ =
      ofRaw (⟨A, inferInstance, T⟩ : Raw I K) ^ n := by
  classical
  induction n with
  | zero =>
    rw [pow_zero]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i ↦ Equiv.equivPUnit (Fin 0 → A i))
    intro x
    change ∏ j : Fin 0, T (fun i ↦ x i j) = 1
    simp
  | succ n ih =>
    rw [pow_succ', ← ih, ← ofRaw_mul]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i ↦ (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A i)).symm)
    intro x
    exact Fin.prod_univ_succ (fun j ↦ T (fun i ↦ x i j))
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped Classical
variable {I : Type*} [Fintype I]
abbrev MaskLeg (S : Finset I) (α : Type) (i : I) := i ∈ S → α
noncomputable def Raw.maskDiagonal (K : Type*) [Field K] (S : Finset I) (α : Type) [Fintype α] :
    Raw.{0} I K :=
  ⟨MaskLeg S α, fun _ ↦ Fintype.ofFinite _, Crossing.basisTensor (fun (a : α) i (_ : i ∈ S) ↦ a)⟩
theorem basisTensor_paired_eq_mul {K : Type*} [Field K]
    {A B C : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
    {J L : Type} [Fintype J] [Fintype L] (a : J → ∀ i, A i) (b : L → ∀ i, B i)
    (c : J × L → ∀ i, C i) (e : ∀ i, C i ≃ A i × B i)
    (h : ∀ s t i, e i (c (s,t) i) = (a s i, b t i)) :
    ofRaw (I := I) (K := K) ⟨C, inferInstance, Crossing.basisTensor c⟩ =
      ofRaw (I := I) (K := K) ⟨A, inferInstance, Crossing.basisTensor a⟩ *
        ofRaw (I := I) (K := K) ⟨B, inferInstance, Crossing.basisTensor b⟩ := by
  classical
  rw [← ofRaw_mul]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent e
  intro x
  change Crossing.basisTensor c x = Crossing.basisTensor a (fun i ↦ (e i (x i)).1) *
    Crossing.basisTensor b (fun i ↦ (e i (x i)).2)
  simp only [Crossing.basisTensor, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have heq : x = c (s, t) ↔ ((fun i ↦ (e i (x i)).1) = a s ∧
      (fun i ↦ (e i (x i)).2) = b t) := by
    constructor
    · rintro rfl
      exact ⟨funext fun i ↦ congrArg Prod.fst (h s t i), funext fun i ↦ congrArg Prod.snd (h s t i)⟩
    · rintro ⟨ha,hb⟩
      funext i
      exact (e i).injective ((Prod.ext (congrFun ha i) (congrFun hb i)).trans (h s t i).symm)
  by_cases ha : (fun i ↦ (e i (x i)).1) = a s <;> simp [heq, ha]
theorem basisTensor_eq_maskDiagonal_mul {K : Type*} [Field K]
    {C : I → Type} [∀ i, Fintype (C i)] {J L : Type} [Fintype J] [Fintype L]
    (S T : Finset I) (c : J × L → ∀ i, C i)
    (e : ∀ i, C i ≃ MaskLeg S J i × MaskLeg T L i)
    (h : ∀ s t i, e i (c (s,t) i) = (fun _ ↦ s, fun _ ↦ t)) :
    ofRaw (I := I) (K := K) ⟨C, inferInstance, Crossing.basisTensor c⟩ =
      ofRaw (Raw.maskDiagonal K S J) * ofRaw (Raw.maskDiagonal K T L) := by
  let (i : I) : Fintype (MaskLeg S J i) := (Raw.maskDiagonal K S J).finiteLeg i
  let (i : I) : Fintype (MaskLeg T L i) := (Raw.maskDiagonal K T L).finiteLeg i
  exact basisTensor_paired_eq_mul (K := K) (A := MaskLeg S J) (B := MaskLeg T L)
    (fun a _ _ ↦ a) (fun b _ _ ↦ b) c e h
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
open scoped Classical NNReal
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]
theorem Raw.maskDiagonal_coeff_at (S : Finset I) {i₀ : I} (hi₀ : i₀ ∈ S)
    {α : Type} [Fintype α] (x : ∀ i, MaskLeg S α i) :
    (Raw.maskDiagonal K S α).coeff x = if ∀ (i : I) (hi : i ∈ S), x i hi = x i₀ hi₀ then 1 else 0 := by
  unfold Raw.maskDiagonal Crossing.basisTensor
  dsimp only
  rw [Finset.sum_eq_single (x i₀ hi₀)]
  · simp only [funext_iff]
  · intro a _ hne
    exact ite_eq_right fun ha ↦ hne (congrFun (congrFun ha i₀) hi₀).symm
  · simp
omit [DecidableEq I] in
theorem Raw.restrict_by_read {X Y : Raw.{0} I K} (g : ∀ i, X.Leg i → Y.Leg i)
    (hcoeff : ∀ x, X.coeff x = Y.coeff (fun i ↦ g i (x i))) : X.Restricts Y := by
  classical
  refine ⟨fun i x y ↦ if y = g i x then 1 else 0, fun x ↦ ?_⟩
  rw [hcoeff x]
  simp_rw [Fintype.prod_boole]
  have heq (y : ∀ i, Y.Leg i) : (∀ i, y i = g i (x i)) ↔ y = fun i ↦ g i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]
theorem Raw.maskDiagonal_restricts_of_embedding (S : Finset I) (hS : S.Nonempty)
    {α β : Type} [Fintype α] [Fintype β] (e : α ↪ β) :
    (Raw.maskDiagonal K S α).Restricts (Raw.maskDiagonal K S β) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  let g (i : I) (x : MaskLeg S α i) : MaskLeg S β i := fun hi ↦ e (x hi)
  apply Raw.restrict_by_read (X := Raw.maskDiagonal K S α) (Y := Raw.maskDiagonal K S β) g
  intro x
  calc
    _ = _ := Raw.maskDiagonal_coeff_at (K := K) S hi₀ x
    _ = _ := ?_
    _ = _ := (Raw.maskDiagonal_coeff_at (K := K) S hi₀ (fun i ↦ g i (x i))).symm
  simp [g]
theorem ofRaw_maskDiagonal_equiv (S : Finset I) (hS : S.Nonempty)
    {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) :
    ofRaw (Raw.maskDiagonal K S α) = ofRaw (Raw.maskDiagonal K S β) :=
  ofRaw_eq_iff.mpr ⟨Raw.maskDiagonal_restricts_of_embedding S hS e.toEmbedding,
    Raw.maskDiagonal_restricts_of_embedding S hS e.symm.toEmbedding⟩
omit [DecidableEq I] in
theorem ofRaw_maskDiagonal_prod (S : Finset I) (α β : Type) [Fintype α] [Fintype β] :
    ofRaw (Raw.maskDiagonal K S (α × β)) =
      ofRaw (Raw.maskDiagonal K S α) * ofRaw (Raw.maskDiagonal K S β) := by
  let a (x : α) (i : I) (_ : i ∈ S) := x
  let b (x : β) (i : I) (_ : i ∈ S) := x
  let c (x : α × β) (i : I) (_ : i ∈ S) := x
  let e (i : I) : MaskLeg S (α × β) i ≃ MaskLeg S α i × MaskLeg S β i :=
    { toFun := fun f ↦ (fun j ↦ (f j).1, fun j ↦ (f j).2)
      invFun := fun f j ↦ (f.1 j, f.2 j)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let : ∀ i, Fintype (MaskLeg S α i) := (Raw.maskDiagonal K S α).finiteLeg
  let : ∀ i, Fintype (MaskLeg S β i) := (Raw.maskDiagonal K S β).finiteLeg
  let : ∀ i, Fintype (MaskLeg S (α × β) i) := (Raw.maskDiagonal K S (α × β)).finiteLeg
  exact basisTensor_paired_eq_mul (K := K) (A := MaskLeg S α) (B := MaskLeg S β)
    (C := MaskLeg S (α × β)) a b c e (fun _ _ _ ↦ rfl)
variable [Nonempty I]
def maskDiagonalHom (K : Type*) [Field K] (S : Finset I) (hS : S.Nonempty) :
    ℕ →* TensorClass.{0} I K where
  toFun n := ofRaw (Raw.maskDiagonal K S (Fin n))
  map_one' := by
    obtain ⟨i, hi⟩ := hS
    apply ofRaw_eq_iff.mpr
    apply Raw.reindex_equivalent (X := Raw.maskDiagonal K S (Fin 1)) (Y := Raw.one I K)
      (fun j ↦ Equiv.ofUnique (MaskLeg S (Fin 1) j) PUnit)
    intro x
    calc
      _ = _ := Raw.maskDiagonal_coeff_at (K := K) S hi x
      _ = _ := ite_eq_left (fun _ _ ↦ Subsingleton.elim (α := Fin 1) _ _)
  map_mul' n m := (ofRaw_maskDiagonal_equiv S hS finProdFinEquiv.symm).trans
    (ofRaw_maskDiagonal_prod S (Fin n) (Fin m))
theorem maskDiagonalHom_mono (S : Finset I) (hS : S.Nonempty) : Monotone (maskDiagonalHom K S hS) :=
  fun _ _ h ↦ Raw.maskDiagonal_restricts_of_embedding S hS (Fin.castLEEmb h)
theorem maskDiagonal_log_price
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
    (S : Finset I) (hS : S.Nonempty) {q : ℕ} (hq : 0 < q) :
    Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin q))) : ℝ) =
      Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin 2))) : ℝ) * Real.logb 2 q := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (maskDiagonalHom K S hS)
  apply spectral_natCast_logb (A := ℕ) (v := v) _ q hq
  intro a b _ hab
  exact φ.property.2.2.2.2 _ _ (maskDiagonalHom_mono S hS hab)
omit [Nonempty I] in
theorem Raw.maskDiagonal_ne_zero (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] : (Raw.maskDiagonal K S α).coeff ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  let a : α := Classical.choice inferInstance
  intro hzero
  have h := congrFun hzero (fun _ _ ↦ a)
  change (Raw.maskDiagonal K S α).coeff (fun _ _ ↦ a) = 0 at h
  exact one_ne_zero (by simpa only [Raw.maskDiagonal_coeff_at (K := K) S hi (fun _ _ ↦ a),
    implies_true, ite_true] using h)
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
section
open SiteTensor
namespace SiteTensor.Raw
theorem ofRaw_group_diagonal_eq_mask {J I : Type} {K : Type*} [Fintype I] [Nonempty I]
    [Fintype J] [Field K] (σ : J ↪ I) (S : Finset I)
    (hS : ∀ i, i ∈ S ↔ ∃ j, σ j = i) (α : Type) [Fintype α] :
    ofRaw ((diagonal J K α).group σ) = ofRaw (maskDiagonal K S α) := by
  classical
  let fiber (i : I) (h : i ∈ S) : {j : J // σ j = i} :=
    ⟨((hS i).mp h).choose, ((hS i).mp h).choose_spec⟩
  have unique (i : I) (a b : {j : J // σ j = i}) : a = b :=
    Subtype.ext (σ.injective (a.property.trans b.property.symm))
  let e (i : I) : ((j : {j : J // σ j = i}) → α) ≃ (i ∈ S → α) :=
    { toFun := fun x h ↦ x (fiber i h)
      invFun := fun x j ↦ x ((hS i).mpr ⟨j, j.property⟩)
      left_inv := fun x ↦ funext fun j ↦ congrArg x (unique i _ j)
      right_inv := fun _ ↦ rfl }
  apply ofRaw_eq_iff.mpr (reindex_equivalent e ?_)
  intro x
  simp only [Raw.group, Raw.diagonal, Raw.maskDiagonal, Crossing.basisTensor]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply propext
  constructor
  · intro hx
    funext i hi
    change x i (fiber i hi) = a
    obtain ⟨j, hj⟩ := fiber i hi
    subst i
    exact congrFun hx j
  · intro hx
    funext j
    have hj : σ j ∈ S := (hS _).mpr ⟨j,rfl⟩
    exact (congrArg (x _) (unique _ _ (fiber _ hj))).trans (congrFun (congrFun hx _) hj)
end SiteTensor.Raw
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Finset
section Increments
variable {α : Type*} [DecidableEq α] (δ : Finset α → ℝ)
def DiminishingIncrements : Prop :=
  ∀ ⦃I A : Finset α⦄ ⦃z : α⦄, I.Nonempty → I ⊆ A → z ∉ A →
    δ (insert z A) - δ A ≤ δ (insert z I) - δ I
def IntersectingSubmodular : Prop :=
  ∀ ⦃A B : Finset α⦄, (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B
variable {δ}
theorem diminishingIncrements_union (h : DiminishingIncrements δ)
    {I A : Finset α} (hne : I.Nonempty) (hIA : I ⊆ A)
    (S : Finset α) (hdis : Disjoint S A) :
    δ (A ∪ S) - δ A ≤ δ (I ∪ S) - δ I := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert z S hz ih =>
    obtain ⟨hzA, hSA⟩ := Finset.disjoint_insert_left.mp hdis
    have step := h (I := I ∪ S) (A := A ∪ S) (z := z) (hne.mono (Finset.subset_union_left (s₂ := S)))
      (Finset.union_subset_union hIA (Finset.Subset.refl S))
      (by simpa only [Finset.mem_union, not_or] using And.intro hzA hz)
    rw [Finset.union_insert, Finset.union_insert]
    linarith [ih hSA]
theorem intersectingSubmodular_iff_diminishingIncrements :
    IntersectingSubmodular δ ↔ DiminishingIncrements δ := by
  constructor
  · intro h I A z hI hIA hz
    have hinter : A ∩ insert z I = I := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      grind
    have hunion : A ∪ insert z I = insert z A := by
      rw [Finset.union_insert, Finset.union_eq_left.mpr hIA]
    have h' := h (A := A) (B := insert z I) (by simpa only [hinter] using hI)
    rw [hinter, hunion] at h'
    linarith
  · intro h A B hAB
    have h' := diminishingIncrements_union h hAB Finset.inter_subset_left
      (B \ A) Finset.sdiff_disjoint
    have heq : (A ∩ B) ∪ (B \ A) = B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      grind
    rw [heq, Finset.union_sdiff_self_eq_union] at h'
    linarith
end Increments
section IntegerWeights
variable {ι : Type*} [Fintype ι]
theorem firstWeight_eq_sq (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = (g - h) ^ 2 := by
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hs]
  ring
theorem firstWeight_eq_zero_iff (g h v₁ : ℤ) (v : ι → ℤ)
    (hs : g = h + ∑ j, v j - Fintype.card ι * v₁) :
    g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * v₁)) +
      ∑ j, -(2 * h * v j) = 0 ↔ g = h := by
  rw [firstWeight_eq_sq g h v₁ v hs]
  simp [sub_eq_zero]
theorem secondWeight_eq_sum_sq (v₁ : ℤ) (v : ι → ℤ)
    (hs : ∑ j, v j = Fintype.card ι * v₁) :
    ∑ j, v j ^ 2 - Fintype.card ι * v₁ ^ 2 = ∑ j, (v j - v₁) ^ 2 := by
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_right_comm (2 : ℤ) _ v₁]
  rw [← Finset.mul_sum, hs]
  simp
  ring
end IntegerWeights
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Polynomial
section
private theorem exists_weight_polynomial (F : Type*) [Field F]
    (S T : Prop) [Decidable S] [Decidable T] (e : ℤ) (hne : S → 0 ≤ e)
    (hz : S ∧ e = 0 ↔ T) :
    ∃ P : F[X], (∀ t : F, t ≠ 0 → P.eval t = (if S then 1 else 0) * t ^ e) ∧
      P.eval 0 = if T then 1 else 0 := by
  by_cases hS : S
  · refine ⟨X ^ e.toNat, ?_, ?_⟩
    · intro t _
      simp only [eval_X_pow, hS, ite_true, one_mul]
      rw [← zpow_natCast, Int.toNat_of_nonneg (hne hS)]
    · by_cases he : e = 0
      · simp [he, hz.mp ⟨hS, he⟩]
      · have he' : e.toNat ≠ 0 := by have := hne hS; omega
        have hT : ¬T := fun h ↦ he (hz.mpr h).2
        simp [zero_pow he', hT]
  · have hT : ¬T := fun h ↦ hS (hz.mpr h).1
    exact ⟨0, by simp [hS], by simp [hT]⟩
private theorem zpow_sum_eq_prod {F ι : Type*} [Field F] (t : F) (ht : t ≠ 0)
    (s : Finset ι) (w : ι → ℤ) : t ^ (∑ j ∈ s, w j) = ∏ j ∈ s, t ^ w j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [hj, zpow_add₀ ht, ih]
theorem firstDiagonalSpecialization (F : Type*) [Field F] {ι : Type*} [Fintype ι]
    (g h a : ℤ) (v : ι → ℤ) :
    ∃ P : F[X],
      (∀ t : F, t ≠ 0 → P.eval t =
        (if g = h + ∑ j, v j - Fintype.card ι * a then 1 else 0) *
          (t ^ (g ^ 2) * t ^ (-h ^ 2 + 2 * h * (Fintype.card ι * a)) *
            ∏ j, t ^ (-(2 * h * v j)))) ∧
      P.eval 0 = if g = h ∧ ∑ j, v j = Fintype.card ι * a then 1 else 0 := by
  let e := g ^ 2 + (-h ^ 2 + 2 * h * (Fintype.card ι * a)) + ∑ j, -(2 * h * v j)
  have hweight (hs : g = h + ∑ j, v j - Fintype.card ι * a) : e = (g - h) ^ 2 :=
    firstWeight_eq_sq g h a v hs
  obtain ⟨P, hP, hP₀⟩ := exists_weight_polynomial F
    (g = h + ∑ j, v j - Fintype.card ι * a)
    (g = h ∧ ∑ j, v j = Fintype.card ι * a) e
    (fun hs ↦ hweight hs ▸ sq_nonneg _) (by
      constructor
      · rintro ⟨hs, he⟩
        obtain heq := (firstWeight_eq_zero_iff g h a v hs).mp he
        exact ⟨heq, by linarith⟩
      · rintro ⟨heq, hc⟩
        have hs : g = h + ∑ j, v j - Fintype.card ι * a := by rw [hc, add_sub_cancel_right, heq]
        exact ⟨hs, (firstWeight_eq_zero_iff g h a v hs).mpr heq⟩)
  refine ⟨P, fun t ht ↦ ?_, hP₀⟩
  rw [hP t ht]
  simp only [e, zpow_add₀ ht, zpow_sum_eq_prod t ht]
theorem secondDiagonalSpecialization (F : Type*) [Field F] {ι : Type*} [Fintype ι]
    (g h a : ℤ) (v : ι → ℤ) [Decidable (∀ j, v j = a)] :
    ∃ P : F[X],
      (∀ t : F, t ≠ 0 → P.eval t =
        (if g = h ∧ ∑ j, v j = Fintype.card ι * a then 1 else 0) *
          (t ^ (-(Fintype.card ι : ℤ) * a ^ 2) * ∏ j, t ^ (v j ^ 2))) ∧
      P.eval 0 = if g = h ∧ ∀ j, v j = a then 1 else 0 := by
  let e := -(Fintype.card ι : ℤ) * a ^ 2 + ∑ j, v j ^ 2
  have hweight (hc : ∑ j, v j = Fintype.card ι * a) : e = ∑ j, (v j - a) ^ 2 := by
    rw [← secondWeight_eq_sum_sq a v hc]
    dsimp [e]
    ring
  obtain ⟨P, hP, hP₀⟩ := exists_weight_polynomial F
    (g = h ∧ ∑ j, v j = Fintype.card ι * a) (g = h ∧ ∀ j, v j = a) e
    (fun hs ↦ hweight hs.2 ▸ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)) (by
      constructor
      · rintro ⟨⟨hg, hc⟩, he⟩
        refine ⟨hg, ?_⟩
        rw [hweight hc, Finset.sum_sq_eq_zero_iff] at he
        simpa [sub_eq_zero] using he
      · rintro ⟨hg, hv⟩
        have hc : ∑ j, v j = Fintype.card ι * a := by simp [hv]
        exact ⟨⟨hg, hc⟩, by simp [hweight hc, hv]⟩)
  refine ⟨P, fun t ht ↦ ?_, hP₀⟩
  rw [hP t ht]
  simp only [e, zpow_add₀ ht, zpow_sum_eq_prod t ht]
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {q k : ℕ}
def supportExponent (h g a : Fin q) (v : Fin k → Fin q) : ℕ :=
  (q - 1 - h.val + k * a.val) + (∑ j, (q - 1 - (v j).val)) + g.val
private theorem complement_sum_add (v : Fin k → Fin q) :
    (∑ j, (q - 1 - (v j).val)) + (∑ j, (v j).val) = k * (q - 1) := by
  rw [← Finset.sum_add_distrib]
  have h (j : Fin k) : q - 1 - (v j).val + (v j).val = q - 1 := by
    have := (v j).isLt
    omega
  simp [h]
theorem supportExponent_eq_iff (h g a : Fin q) (v : Fin k → Fin q) :
    supportExponent h g a v = (k + 1) * (q - 1) ↔
      (g.val : ℤ) = h.val + (∑ j, ((v j).val : ℤ)) - (k : ℤ) * a.val := by
  rw [eq_sub_iff_add_eq]
  have heq : ((g.val + k * a.val : ℕ) : ℤ) = (g.val : ℤ) + (k : ℤ) * a.val := by
    norm_cast
  have hsum : ((h.val + ∑ j, (v j).val : ℕ) : ℤ) = (h.val : ℤ) + ∑ j, ((v j).val : ℤ) := by
    norm_cast
  rw [← heq, ← hsum, Nat.cast_inj]
  have hcomp := complement_sum_add v
  have hh := h.isLt
  simp only [supportExponent, Nat.add_mul, Nat.one_mul]
  omega
theorem supportExponent_le (h g a : Fin q) (v : Fin k → Fin q) :
    supportExponent h g a v ≤ 2 * (k + 1) * (q - 1) := by
  have ha : a.val ≤ q - 1 := by have := a.isLt; omega
  have hg : g.val ≤ q - 1 := by have := g.isLt; omega
  have hmul := Nat.mul_le_mul_left k ha
  have hcomp := complement_sum_add v
  rw [supportExponent, Nat.mul_assoc, Nat.add_mul, Nat.one_mul]
  omega
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators
open Polynomial
section
theorem exists_monomial_coefficient_weights (F : Type*) [Field F] [Infinite F] (D d : ℕ) :
    ∃ x : Fin (D + 1) ↪ F, ∃ w : Fin (D + 1) → F, ∀ e ≤ D,
      ∑ i, w i * x i ^ e = if e = d then 1 else 0 := by
  classical
  let x : Fin (D + 1) ↪ F := Fin.valEmbedding.trans (Infinite.natEmbedding F)
  refine ⟨x, fun i ↦ (Lagrange.basis Finset.univ x i).coeff d, ?_⟩
  intro e he
  have hdeg : (X ^ e : F[X]).degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    rw [degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le he
  have h := congrArg (fun f : F[X] ↦ f.coeff d) (Lagrange.eq_interpolate x.injective.injOn hdeg)
  simp only [Lagrange.interpolate_apply, finsetSum_coeff, coeff_C_mul, eval_pow, eval_X,
    coeff_X_pow] at h
  simpa only [mul_comm, eq_comm] using h.symm
theorem exists_equation_restriction (F : Type*) [Field F] [Infinite F] (q k : ℕ) :
    ∃ x : Fin (2 * (k + 1) * (q - 1) + 1) ↪ F,
      ∃ w : Fin (2 * (k + 1) * (q - 1) + 1) → F,
        ∀ (h g a : Fin q) (v : Fin k → Fin q),
          ∑ l, (w l * x l ^ (q - 1 - h.val + k * a.val)) *
              (∏ j, x l ^ (q - 1 - (v j).val)) * x l ^ g.val =
            if (g.val : ℤ) = h.val + (∑ j, ((v j).val : ℤ)) - (k : ℤ) * a.val then 1 else 0 := by
  obtain ⟨x, w, hw⟩ := exists_monomial_coefficient_weights F (2 * (k + 1) * (q - 1))
    ((k + 1) * (q - 1))
  refine ⟨x, w, fun h g a v ↦ ?_⟩
  simp only [← supportExponent_eq_iff h g a v]
  rw [← hw _ (supportExponent_le h g a v)]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [supportExponent, pow_add, mul_assoc]
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
structure IncrementCoordinate (q k m : ℕ) where
  h : Fin q
  a : Fin q
  g : Fin q
  hOther : Fin k → Fin q
  v : Fin k → Fin q
  hExtra : Fin m → Fin q
def IncrementCoordinate.shared {q k m : ℕ} (c : IncrementCoordinate q k m) : Prop :=
  (∀ j, c.hOther j = c.h) ∧ (∀ j, c.hExtra j = c.h)
instance {q k m : ℕ} (c : IncrementCoordinate q k m) : Decidable c.shared := by
  unfold IncrementCoordinate.shared
  infer_instance
def commonLabelRestrictions (F : Type*) [Field F] (q k m L : ℕ) :
    Set (IncrementCoordinate q k m → F) :=
  {T | ∃ (U : Fin q → Fin q → Fin L → F) (V : Fin k → Fin q → Fin q → Fin L → F)
      (Z : Fin q → Fin L → F), ∀ c, T c =
        if c.shared then ∑ l, U c.h c.a l * (∏ j, V j (c.hOther j) (c.v j) l) * Z c.g l
        else 0}
theorem localScaling_preserves_commonLabelRestrictions {F : Type*} [Field F] (q k m L : ℕ)
    (u : Fin q → Fin q → F) (b : Fin k → Fin q → Fin q → F) (z : Fin q → F) :
    Set.MapsTo (fun T c ↦ (u c.h c.a * (∏ j, b j (c.hOther j) (c.v j)) * z c.g) * T c)
      (commonLabelRestrictions F q k m L) (commonLabelRestrictions F q k m L) := by
  rintro T ⟨U, V, Z, hT⟩
  refine ⟨fun h a l ↦ u h a * U h a l, fun j h v l ↦ b j h v * V j h v l,
    fun g l ↦ z g * Z g l, fun c ↦ ?_⟩
  simp only [hT c]
  by_cases hc : c.shared
  · simp only [hc, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.prod_mul_distrib]
    ac_rfl
  · simp [hc]
theorem commonLabelEquation_mem_restrictions (F : Type*) [Field F] [Infinite F] (q k m : ℕ) :
    (fun c : IncrementCoordinate q k m ↦
      if c.shared ∧ (c.g.val : ℤ) = c.h.val + (∑ j, ((c.v j).val : ℤ)) - (k : ℤ) * c.a.val
      then 1 else 0) ∈ commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1) := by
  obtain ⟨x, w, h⟩ := exists_equation_restriction F q k
  refine ⟨fun h a l ↦ w l * x l ^ (q - 1 - h.val + k * a.val),
    fun _ _ v l ↦ x l ^ (q - 1 - v.val), fun g l ↦ x l ^ g.val, fun c ↦ ?_⟩
  by_cases hc : c.shared
  · simpa only [hc, true_and, ite_true] using (h c.h c.g c.a c.v).symm
  · simp [hc]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Polynomial
section
private theorem specialize_local_scalings {F : Type*} [Field F] [Infinite F]
    {q k m L : ℕ} {S T : IncrementCoordinate q k m → F}
    (u : F → Fin q → Fin q → F) (b : F → Fin k → Fin q → Fin q → F)
    (z : F → Fin q → F)
    (hS : S ∈ affineZariskiClosure (commonLabelRestrictions F q k m L))
    (hcurve : ∀ c, ∃ P : F[X],
      (∀ t : F, t ≠ 0 → P.eval t =
        (u t c.h c.a * (∏ j, b t j (c.hOther j) (c.v j)) * z t c.g) * S c) ∧
      P.eval 0 = T c) :
    T ∈ affineZariskiClosure (commonLabelRestrictions F q k m L) := by
  choose P hP hP₀ using hcurve
  rw [← affineZariskiClosure_idem, ← funext hP₀]
  apply polynomialCurve_zero_mem_affineZariskiClosure
  intro t ht
  simp only [hP _ t ht]
  exact mapsTo_affineZariskiClosure_of_mul _
    (localScaling_preserves_commonLabelRestrictions q k m L (u t) (b t) (z t)) hS
def commonLabelTarget (F : Type*) [Field F] {q k m : ℕ} (c : IncrementCoordinate q k m) : F :=
  if c.shared ∧ c.g = c.h ∧ ∀ j, c.v j = c.a then 1 else 0
theorem commonLabelTarget_mem_closure (F : Type*) [Field F] [Infinite F] (q k m : ℕ) :
    commonLabelTarget F ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1)) := by
  classical
  let S (c : IncrementCoordinate q k m) : F :=
    if c.shared ∧ (c.g.val : ℤ) = c.h.val + (∑ j, ((c.v j).val : ℤ)) - (k : ℤ) * c.a.val
    then 1 else 0
  let T (c : IncrementCoordinate q k m) : F :=
    if c.shared ∧ (c.g.val : ℤ) = c.h.val ∧ (∑ j, ((c.v j).val : ℤ)) = (k : ℤ) * c.a.val
    then 1 else 0
  have hS : S ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1)) :=
    subset_affineZariskiClosure _ (commonLabelEquation_mem_restrictions F q k m)
  have hT : T ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m (2 * (k + 1) * (q - 1) + 1)) := by
    apply specialize_local_scalings
      (fun t h a ↦ t ^ (-(h.val : ℤ) ^ 2 + 2 * h.val * ((k : ℤ) * a.val)))
      (fun t _ h v ↦ t ^ (-(2 * (h.val : ℤ) * v.val)))
      (fun t g ↦ t ^ ((g.val : ℤ) ^ 2)) hS
    intro c
    by_cases hc : c.shared
    · obtain ⟨P, hP, hP₀⟩ := firstDiagonalSpecialization F
        (c.g.val : ℤ) c.h.val c.a.val (fun j ↦ ((c.v j).val : ℤ))
      refine ⟨P, fun t ht ↦ ?_, ?_⟩
      · rw [hP t ht]
        simp only [Fintype.card_fin, hc.1, S, hc, true_and]
        ac_rfl
      · simpa only [Fintype.card_fin, T, hc, true_and] using hP₀
    · exact ⟨0, by simp [S, hc], by simp [T, hc]⟩
  apply specialize_local_scalings
    (fun t _ a ↦ t ^ (-(k : ℤ) * (a.val : ℤ) ^ 2))
    (fun t _ _ v ↦ t ^ ((v.val : ℤ) ^ 2)) (fun _ _ ↦ 1) hT
  intro c
  by_cases hc : c.shared
  · obtain ⟨P, hP, hP₀⟩ := secondDiagonalSpecialization F
      (c.g.val : ℤ) c.h.val c.a.val (fun j ↦ ((c.v j).val : ℤ))
    refine ⟨P, fun t ht ↦ ?_, ?_⟩
    · rw [hP t ht]
      simp only [Fintype.card_fin, T, hc, true_and, one_mul, mul_comm]
    · simpa only [commonLabelTarget, hc, true_and, Nat.cast_inj, Fin.val_inj] using hP₀
  · exact ⟨0, by simp [T, hc], by simp [commonLabelTarget, hc]⟩
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
abbrev IncrementSite (k m : ℕ) := Fin (k + 1) ⊕ Option (Fin m)
def incrementOldInput (q k m L : ℕ) : IncrementSite k m → Type
  | .inl _ => Fin q × Fin L
  | .inr none => Fin L
  | .inr (some _) => Fin q
def incrementSiteOutput (q k m : ℕ) : IncrementSite k m → Type
  | .inl _ => Fin q × Fin q
  | .inr _ => Fin q
instance (q k m L : ℕ) (i : IncrementSite k m) : Fintype (incrementOldInput q k m L i) :=
  match i with
  | .inl _ => inferInstanceAs (Fintype (Fin q × Fin L))
  | .inr none => inferInstanceAs (Fintype (Fin L))
  | .inr (some _) => inferInstanceAs (Fintype (Fin q))
instance (q k m : ℕ) (i : IncrementSite k m) : Fintype (incrementSiteOutput q k m i) :=
  match i with
  | .inl _ => inferInstanceAs (Fintype (Fin q × Fin q))
  | .inr _ => inferInstanceAs (Fintype (Fin q))
def incrementOutputCoordinate (q k m : ℕ) :
    (∀ i, incrementSiteOutput q k m i) ≃ IncrementCoordinate q k m where
  toFun x := {
    h := (x (.inl 0)).1
    a := (x (.inl 0)).2
    g := x (.inr none)
    hOther := fun j ↦ (x (.inl j.succ)).1
    v := fun j ↦ (x (.inl j.succ)).2
    hExtra := fun j ↦ x (.inr (some j)) }
  invFun c := fun i ↦ match i with
    | .inl j => Fin.cases (c.h, c.a) (fun t ↦ (c.hOther t, c.v t)) j
    | .inr none => c.g
    | .inr (some j) => c.hExtra j
  left_inv x := by
    funext i
    rcases i with j | j
    · refine Fin.cases ?_ (fun t ↦ ?_) j <;> rfl
    · cases j <;> rfl
  right_inv c := by rfl
def incrementTargetBasis (q k m : ℕ) (s : Fin q × Fin q) : ∀ i, incrementSiteOutput q k m i
  | .inl _ => s
  | .inr _ => s.1
theorem incrementTargetBasis_apply (F : Type*) [Field F] (q k m : ℕ)
    (x : ∀ i, incrementSiteOutput q k m i) :
    Crossing.basisTensor (F := F) (incrementTargetBasis q k m) x =
      let c := incrementOutputCoordinate q k m x
      if c.shared ∧ c.g = c.h ∧ (∀ j, c.v j = c.a) then 1 else 0 := by
  classical
  let c := incrementOutputCoordinate q k m x
  have match_iff (s : Fin q × Fin q) : x = incrementTargetBasis q k m s ↔
      (c.shared ∧ c.g = c.h ∧ ∀ j, c.v j = c.a) ∧ s = (c.h, c.a) := by
    constructor
    · intro heq
      subst x
      exact ⟨⟨⟨fun _ ↦ rfl, fun _ ↦ rfl⟩, rfl, fun _ ↦ rfl⟩, rfl⟩
    · rintro ⟨⟨hshare, hg, hv⟩, rfl⟩
      funext i
      rcases i with j | j
      · refine Fin.cases ?_ (fun t ↦ ?_) j
        · rfl
        · exact Prod.ext (hshare.1 t) (hv t)
      · cases j with
        | none => exact hg
        | some j => exact hshare.2 j
  unfold Crossing.basisTensor
  simp_rw [match_iff]
  by_cases hc : c.shared ∧ c.g = c.h ∧ ∀ j, c.v j = c.a <;> simp [hc, c] at *
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {F : Type*} [Field F]
def incrementSourceBasis (q k m L : ℕ) (s : Fin q × Fin L) :
    ∀ i, incrementOldInput q k m L i
  | .inl _ => s
  | .inr none => s.2
  | .inr (some _) => s.1
private def incrementLocalMatrices {q k m L : ℕ}
    (U : Fin q → Fin q → Fin L → F) (V : Fin k → Fin q → Fin q → Fin L → F)
    (Z : Fin q → Fin L → F) :
    ∀ i, incrementSiteOutput q k m i → incrementOldInput q k m L i → F
  | .inl j => Fin.cases
      (fun y s ↦ if y.1 = s.1 then U y.1 y.2 s.2 else 0)
      (fun j y s ↦ if y.1 = s.1 then V j y.1 y.2 s.2 else 0) j
  | .inr none => Z
  | .inr (some _) => fun (y h : Fin q) ↦ if y = h then 1 else 0
theorem isRestriction_of_mem_commonLabelRestrictions {q k m L : ℕ}
    {T : IncrementCoordinate q k m → F} (hT : T ∈ commonLabelRestrictions F q k m L) :
    Crossing.IsRestriction (T ∘ incrementOutputCoordinate q k m)
      (Crossing.basisTensor (incrementSourceBasis q k m L)) := by
  classical
  obtain ⟨U, V, Z, hT⟩ := hT
  apply (Crossing.restriction_basisTensor_iff _ _).mpr
  refine ⟨incrementLocalMatrices U V Z, fun x ↦ ?_⟩
  let c := incrementOutputCoordinate q k m x
  change T c = _
  rw [hT c, Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_option, Fin.prod_univ_succ]
  change _ = ∑ h : Fin q, ∑ l : Fin L,
    ((if c.h = h then U c.h c.a l else 0) *
      (∏ j, if c.hOther j = h then V j (c.hOther j) (c.v j) l else 0)) *
        (Z c.g l * ∏ j, (if c.hExtra j = h then (1 : F) else 0))
  rw [Finset.sum_eq_single c.h]
  · simp only [ite_true, Fintype.prod_ite_zero, eq_self]
    by_cases ha : ∀ j, c.hOther j = c.h <;> by_cases hb : ∀ j, c.hExtra j = c.h <;>
      simp [IncrementCoordinate.shared, ha, hb]
  · intro h _ hne
    simp [Ne.symm hne]
  · simp
theorem mem_siteRestrictionClosure_of_mem_commonLabelClosure {q k m L : ℕ}
    {T : IncrementCoordinate q k m → F} (hT : T ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m L)) :
    T ∘ incrementOutputCoordinate q k m ∈ affineZariskiClosure {S | Crossing.IsRestriction S
      (Crossing.basisTensor (incrementSourceBasis q k m L))} := by
  let f (x : ∀ i, incrementSiteOutput q k m i) : MvPolynomial (IncrementCoordinate q k m) F :=
    MvPolynomial.X (incrementOutputCoordinate q k m x)
  have heval (S : IncrementCoordinate q k m → F) :
      (fun x ↦ MvPolynomial.eval S (f x)) = S ∘ incrementOutputCoordinate q k m := by
    funext x
    simp [f]
  refine heval T ▸ mapsTo_affineZariskiClosure_of_polynomial f (fun S hS ↦ ?_) hT
  simp only [heval]
  exact isRestriction_of_mem_commonLabelRestrictions hS
theorem commonLabel_borderRestriction (F : Type*) [Field F] [Infinite F] (q k m : ℕ) :
    Crossing.basisTensor (F := F) (incrementTargetBasis q k m) ∈
      affineZariskiClosure {S | Crossing.IsRestriction S (Crossing.basisTensor
        (incrementSourceBasis q k m (2 * (k + 1) * (q - 1) + 1)))} := by
  have ht : Crossing.basisTensor (F := F) (incrementTargetBasis q k m) =
      commonLabelTarget F ∘ incrementOutputCoordinate q k m :=
    funext (incrementTargetBasis_apply F q k m)
  rw [ht]
  exact mem_siteRestrictionClosure_of_mem_commonLabelClosure (commonLabelTarget_mem_closure F q k m)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open SiteTensor
def incrementJointMask (k m : ℕ) : Finset (IncrementSite k m) :=
  Finset.univ.map Function.Embedding.inl
def incrementOldMask (k m : ℕ) : Finset (IncrementSite k m) :=
  Finset.univ.erase (.inr none)
def incrementAuxMask (k m : ℕ) : Finset (IncrementSite k m) :=
  insert (.inr none) (incrementJointMask k m)
private def bothLabels {α β : Type} {P Q : Prop} (h : P) (k : Q) :
    α × β ≃ (P → α) × (Q → β) where
  toFun x := (fun _ ↦ x.1, fun _ ↦ x.2)
  invFun x := (x.1 h, x.2 k)
  left_inv _ := rfl
  right_inv _ := rfl
private def leftLabel {α β : Type} {P Q : Prop} (h : P) (k : ¬Q) :
    α ≃ (P → α) × (Q → β) where
  toFun a := (fun _ ↦ a, fun z ↦ (k z).elim)
  invFun x := x.1 h
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (funext fun z ↦ (k z).elim)
private def rightLabel {α β : Type} {P Q : Prop} (h : ¬P) (k : Q) :
    β ≃ (P → α) × (Q → β) where
  toFun b := (fun z ↦ (h z).elim, fun _ ↦ b)
  invFun x := x.2 k
  left_inv _ := rfl
  right_inv _ := Prod.ext (funext fun z ↦ (h z).elim) rfl
private def sourceLegEquiv (q k m L : ℕ) (i : IncrementSite k m) : incrementOldInput q k m L i ≃
    MaskLeg (incrementOldMask k m) (Fin q) i × MaskLeg (incrementAuxMask k m) (Fin L) i := by
  rcases i with j | j
  · exact bothLabels (by simp [incrementOldMask]) (by simp [incrementAuxMask, incrementJointMask])
  · cases j with
    | none => exact rightLabel (by simp [incrementOldMask]) (by simp [incrementAuxMask])
    | some j => exact leftLabel (by simp [incrementOldMask]) (by simp [incrementAuxMask, incrementJointMask])
private def targetLegEquiv (q k m : ℕ) (i : IncrementSite k m) : incrementSiteOutput q k m i ≃
    MaskLeg Finset.univ (Fin q) i × MaskLeg (incrementJointMask k m) (Fin q) i := by
  rcases i with j | j
  · exact bothLabels (Finset.mem_univ _) (by simp [incrementJointMask])
  · exact leftLabel (Finset.mem_univ _) (by simp [incrementJointMask])
theorem ofCoeffs_incrementSourceBasis (K : Type*) [Field K] (q k m L : ℕ) :
    ofCoeffs (Crossing.basisTensor (F := K) (incrementSourceBasis q k m L)) =
      ofRaw (Raw.maskDiagonal K (incrementOldMask k m) (Fin q)) *
        ofRaw (Raw.maskDiagonal K (incrementAuxMask k m) (Fin L)) := by
  classical
  apply basisTensor_eq_maskDiagonal_mul (K := K) (incrementOldMask k m) (incrementAuxMask k m)
    (incrementSourceBasis q k m L) (sourceLegEquiv q k m L)
  intro s t i
  rcases i with j | j
  · rfl
  · cases j with
    | none => exact Prod.ext (funext fun h ↦ by simp [incrementOldMask] at h) rfl
    | some j => exact Prod.ext rfl (funext fun h ↦ by simp [incrementAuxMask, incrementJointMask] at h)
theorem ofCoeffs_incrementTargetBasis (K : Type*) [Field K] (q k m : ℕ) :
    ofCoeffs (Crossing.basisTensor (F := K) (incrementTargetBasis q k m)) =
      ofRaw (Raw.maskDiagonal K (Finset.univ : Finset (IncrementSite k m)) (Fin q)) *
        ofRaw (Raw.maskDiagonal K (incrementJointMask k m) (Fin q)) := by
  classical
  apply basisTensor_eq_maskDiagonal_mul (K := K) Finset.univ (incrementJointMask k m)
    (incrementTargetBasis q k m) (targetLegEquiv q k m)
  intro s t i
  rcases i with j | j
  · rfl
  · exact Prod.ext rfl (funext fun h ↦ by simp [incrementJointMask] at h)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
theorem exists_incrementSite_embedding {X : Type*} [DecidableEq X]
    {I A : Finset X} (hI : I.Nonempty) (hIA : I ⊆ A) {z : X} (hz : z ∉ A) :
    ∃ e : IncrementSite (I.card - 1) (A \ I).card ↪ X,
      (incrementJointMask _ _).map e = I ∧ (incrementOldMask _ _).map e = A ∧
      (incrementAuxMask _ _).map e = insert z I ∧ Finset.univ.map e = insert z A := by
  have hcard : 0 < I.card := Finset.card_pos.mpr hI
  let i := (I.equivFinOfCardEq (show I.card = (I.card - 1) + 1 by omega)).symm
  let j := (A \ I).equivFin.symm
  let f : IncrementSite (I.card - 1) (A \ I).card → X
    | .inl k => i k
    | .inr none => z
    | .inr (some k) => j k
  have hInject : Function.Injective f := by
    have hi (k) := (i k).property
    have hj (k) := Finset.mem_sdiff.mp (j k).property
    rintro (a | _ | a) (b | _ | b) h <;> dsimp only [f] at h
    · exact congrArg Sum.inl (i.injective (Subtype.ext h))
    · exact (hz (h ▸ hIA (hi a))).elim
    · exact ((hj b).2 (h ▸ hi a)).elim
    · exact (hz (h.symm ▸ hIA (hi b))).elim
    · rfl
    · exact (hz (h.symm ▸ (hj b).1)).elim
    · exact ((hj a).2 (h.symm ▸ hi b)).elim
    · exact (hz (h ▸ (hj a).1)).elim
    · exact congrArg (fun k => Sum.inr (some k)) (j.injective (Subtype.ext h))
  let e : IncrementSite (I.card - 1) (A \ I).card ↪ X := ⟨f, hInject⟩
  have joint : (incrementJointMask _ _).map e = I := by
    ext x
    simp only [incrementJointMask, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.inl_apply, exists_exists_eq_and]
    constructor
    · rintro ⟨k, rfl⟩
      exact (i k).property
    · intro hx
      exact ⟨i.symm ⟨x,hx⟩, by change (i (i.symm _) : X) = x; simp⟩
  have old : (incrementOldMask _ _).map e = A := by
    ext x
    simp only [incrementOldMask, Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases k with k | _ | k
      · exact hIA (i k).property
      · exact (hk rfl).elim
      · exact (Finset.mem_sdiff.mp (j k).property).1
    · intro hx
      by_cases hin : x ∈ I
      · exact ⟨.inl (i.symm ⟨x,hin⟩), by simp, by change (i (i.symm _) : X) = x; simp⟩
      · have hj : x ∈ A \ I := Finset.mem_sdiff.mpr ⟨hx,hin⟩
        exact ⟨.inr (some (j.symm ⟨x,hj⟩)), by simp, by change (j (j.symm _) : X) = x; simp⟩
  have ez : e (.inr none) = z := rfl
  refine ⟨e, joint, old, ?_, ?_⟩
  · rw [incrementAuxMask, Finset.map_insert, ez, joint]
  · calc
      Finset.univ.map e = (insert (.inr none) (incrementOldMask _ _)).map e := by
        simp [incrementOldMask]
      _ = insert z A := by rw [Finset.map_insert, old, ez]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped Classical
noncomputable section
variable {I K E : Type*} [Fintype I] [Field K] [Field E] {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
abbrev RestrictionProfile (A B : I → Type*) (n : ℕ) := (Σ i, B i × A i) → Fin (n + 1)
private def localHistogram {n : ℕ} {V : Type*} (w : Fin n → V) (v : V) : Fin (n + 1) :=
  ⟨(Finset.univ.filter (w · = v)).card,
    Nat.lt_succ_of_le (by simpa using Finset.card_filter_le Finset.univ (w · = v))⟩
private theorem prod_histogram {V : Type*} [Fintype V] {n : ℕ} (w : Fin n → V) (f : V → E) :
    ∏ v, f v ^ (localHistogram w v : ℕ) = ∏ j, f (w j) := by
  simpa only [localHistogram, Finset.prod_const] using Finset.prod_fiberwise' Finset.univ w f
private def profileMatrix (n : ℕ) (p : RestrictionProfile A B n) (i : I)
    (b : Fin n → B i) (a : Fin n → A i) : K :=
  if (localHistogram fun j ↦ (b j, a j)) = fun v ↦ p ⟨i, v⟩ then 1 else 0
def profileRestriction (n : ℕ) (S : (∀ i, A i) → K) (p : RestrictionProfile A B n)
    (b : ∀ i, Fin n → B i) : K :=
  ∑ a, groupedPower n S a * ∏ i, profileMatrix n p i (b i) (a i)
theorem profileRestriction_restricts (n : ℕ) (S : (∀ i, A i) → K) (p : RestrictionProfile A B n) :
    Crossing.IsRestriction (profileRestriction n S p) (groupedPower n S) :=
  ⟨profileMatrix n p, fun _ ↦ rfl⟩
omit [∀ i, Fintype (B i)] in
private theorem groupedPower_restrict_eq (n : ℕ) (S : (∀ i, A i) → E)
    (T : (∀ i, B i) → E) (M : ∀ i, B i → A i → E)
    (h : ∀ b, T b = ∑ a, S a * ∏ i, M i (b i) (a i)) (b : ∀ i, Fin n → B i) :
    groupedPower n T b = ∑ a, groupedPower n S a * ∏ i, ∏ j, M i (b i j) (a i j) := by
  unfold groupedPower coordinatePower
  simp_rw [h, Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.piComm (fun (_ : Fin n) i ↦ A i))
  intro a
  rw [Finset.prod_mul_distrib, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun j i ↦ M i (b i j) (a j i))]
  rfl
theorem groupedPower_mem_span_profileRestrictions [Algebra K E] (n : ℕ)
    (S : (∀ i, A i) → K) {T : (∀ i, B i) → E}
    (h : Crossing.IsRestriction T (fun a ↦ algebraMap K E (S a))) :
    groupedPower n T ∈ Submodule.span E (Set.range (fun p : RestrictionProfile A B n ↦
      fun x ↦ algebraMap K E (profileRestriction n S p x))) := by
  classical
  obtain ⟨M, hM⟩ := h
  let w (p : RestrictionProfile A B n) := ∏ i, ∏ v : B i × A i, M i v.1 v.2 ^ (p ⟨i, v⟩ : ℕ)
  apply (Submodule.mem_span_range_iff_exists_fun E).mpr
  refine ⟨w, ?_⟩
  ext b
  rw [groupedPower_restrict_eq n _ T M hM b]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, profileRestriction,
    map_sum, map_mul, map_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  let p₀ : RestrictionProfile A B n := fun ⟨i,v⟩ ↦ localHistogram (fun j ↦ (b i j, a i j)) v
  have hind (p : RestrictionProfile A B n) :
      (∏ i, algebraMap K E (profileMatrix n p i (b i) (a i))) = if p = p₀ then 1 else 0 := by
    simp only [profileMatrix, apply_ite, map_one, map_zero, Fintype.prod_boole]
    have heq : (∀ i, (localHistogram fun j ↦ (b i j, a i j)) = fun v ↦ p ⟨i, v⟩) ↔ p = p₀ := by
      constructor
      · intro h
        funext ⟨i,v⟩
        exact (congrFun (h i) v).symm
      · rintro rfl i
        rfl
    simp only [heq]
    split <;> simp_all
  simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hw : w p₀ = ∏ i, ∏ j, M i (b i j) (a i j) :=
    Finset.prod_congr rfl (fun i _ ↦ prod_histogram (fun j ↦ (b i j, a i j)) (fun v ↦ M i v.1 v.2))
  simp only [hw, groupedPower, coordinatePower, map_prod, mul_comm]
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
theorem mem_span_of_map_mem_span {F E X J : Type*} [Field F] [Field E] [Algebra F E]
    [Fintype J] (x : X → F) (U : J → X → F)
    (h : (fun i => algebraMap F E (x i)) ∈
      Submodule.span E (Set.range (fun j i => algebraMap F E (U j i)))) :
    x ∈ Submodule.span F (Set.range U) := by
  obtain ⟨l, hl⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have retract (t : F) : l (algebraMap F E t) = t := LinearMap.congr_fun hl t
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp h
  refine (Submodule.mem_span_range_iff_exists_fun F).mpr ⟨fun j => l (a j), ?_⟩
  funext i
  have hi := congrFun ha i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  have hli := congrArg l hi
  rw [map_sum, retract] at hli
  convert hli using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (a j), ← Algebra.smul_def, l.map_smul]
  exact mul_comm _ _
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
universe v
open scoped NNReal
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K] {A : I → Type v} [∀ i, Fintype (A i)] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
theorem coeffValue_smul_le (c : K) (T : (∀ i, A i) → K) :
    coeffValue φ (c • T) ≤ coeffValue φ T :=
  φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (scalar_mul_restricts c T))
theorem coeffValue_span_le {J : Type*} [Fintype J] (U : J → (∀ i, A i) → K)
    {T : (∀ i, A i) → K} (hT : T ∈ Submodule.span K (Set.range U))
    {B : ℝ≥0} (hB : ∀ j, coeffValue φ (U j) ≤ B) :
    coeffValue φ T ≤ Fintype.card J * B := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hT
  calc
    _ ≤ ∑ j, coeffValue φ (c j • U j) := ordinary_sum_value_le φ _
    _ ≤ ∑ _j : J, B := Finset.sum_le_sum fun j _ ↦ (coeffValue_smul_le φ _ _).trans (hB j)
    _ = _ := by simp
theorem coeffValue_groupedPower (n : ℕ) (T : (∀ i, A i) → K) :
    coeffValue φ (groupedPower n T) = coeffValue φ T ^ n := by
  change normalizedSpectrum.toRingHom φ (ofRaw _) = normalizedSpectrum.toRingHom φ (ofRaw _) ^ n
  rw [ofRaw_groupedPower, map_pow]
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor
open scoped NNReal
universe v
variable {I K E : Type*} [Fintype I] [Nonempty I] [Field K] [Field E] [Algebra K E] {A B : I → Type v} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
omit [Nonempty I] in
theorem groupedPower_mem_span_of_geometric_restriction (T : (∀ i, B i) → K) (S : (∀ i, A i) → K)
    (hTS : (fun b ↦ algebraMap K E (T b)) ∈ affineZariskiClosure
      {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K E (S a))}) (n : ℕ) :
    groupedPower n T ∈ Submodule.span K (Set.range (profileRestriction (B := B) n S)) := by
  classical
  apply mem_span_of_map_mem_span (E := E)
  let U := Submodule.span E (Set.range (fun p : RestrictionProfile A B n ↦
    fun x ↦ algebraMap K E (profileRestriction n S p x)))
  let f (b : ∀ i, Fin n → B i) : MvPolynomial (∀ i, B i) E := ∏ j, MvPolynomial.X (fun i ↦ b i j)
  have hmap : Set.MapsTo (fun Y w ↦ MvPolynomial.eval Y (f w))
      {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K E (S a))} (U : Set _) := by
    intro Y hY
    have heval : (fun w ↦ MvPolynomial.eval Y (f w)) = groupedPower n Y := by
      funext w
      simp [f, groupedPower, coordinatePower]
    change (fun w ↦ MvPolynomial.eval Y (f w)) ∈ U
    rw [heval]
    exact groupedPower_mem_span_profileRestrictions n S hY
  have hh := mapsTo_affineZariskiClosure_of_polynomial f hmap hTS
  simpa [affineZariskiClosure_submodule, groupedPower, coordinatePower, f, U] using hh
theorem coeffValue_le_of_geometric_restriction
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (T : (∀ i, B i) → K) (S : (∀ i, A i) → K)
    (hTS : (fun b ↦ algebraMap K E (T b)) ∈ affineZariskiClosure
      {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K E (S a))}) :
    coeffValue φ T ≤ coeffValue φ S := by
  classical
  apply nnreal_le_of_pow_le_polynomial_mul_pow (Fintype.card (Σ i, B i × A i))
  intro n _
  have hb (p : RestrictionProfile A B n) :
      coeffValue φ (profileRestriction n S p) ≤ coeffValue φ S ^ n := by
    rw [← coeffValue_groupedPower φ n S]
    exact φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (profileRestriction_restricts n S p))
  have ht := coeffValue_span_le φ (profileRestriction n S)
    (groupedPower_mem_span_of_geometric_restriction T S hTS n) hb
  simpa [RestrictionProfile, coeffValue_groupedPower] using ht
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Classical
theorem Crossing.map_basisTensor {K E I J : Type*} [CommSemiring K] [CommSemiring E]
    [Fintype I] [Fintype J] {A : I → Type*} (f : K →+* E) (a : J → ∀ i, A i) (x : ∀ i, A i) :
    f (basisTensor (F := K) a x) = basisTensor (F := E) a x := by
  simp [basisTensor]
theorem commonLabel_geometricRestriction (K : Type*) [Field K] (q k m : ℕ) :
    (fun b ↦ algebraMap K (AlgebraicClosure K)
      (Crossing.basisTensor (F := K) (incrementTargetBasis q k m) b)) ∈
      affineZariskiClosure {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K (AlgebraicClosure K)
        (Crossing.basisTensor (F := K)
          (incrementSourceBasis q k m (2 * (k + 1) * (q - 1) + 1)) a))} := by
  simpa only [Crossing.map_basisTensor] using commonLabel_borderRestriction (AlgebraicClosure K) q k m
theorem commonLabel_value_le (K : Type*) [Field K] (q k m : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} (IncrementSite k m) K → _ → Prop)) :
    SiteTensor.coeffValue φ (Crossing.basisTensor (F := K) (incrementTargetBasis q k m)) ≤
      SiteTensor.coeffValue φ (Crossing.basisTensor (F := K)
        (incrementSourceBasis q k m (2 * (k+1) * (q-1) + 1))) :=
  SiteTensor.coeffValue_le_of_geometric_restriction (E := AlgebraicClosure K) φ _ _
    (commonLabel_geometricRestriction K q k m)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
theorem priceIncrement_of_finite_diagonal {r : ℕ} (hr : 0 < r) {a az i iz : ℝ}
    (hiz : 0 ≤ iz)
    (hfinite : ∀ q : ℕ, 2 ≤ q →
      (az + i) * Real.logb 2 q ≤ a * Real.logb 2 q +
        iz * Real.logb 2 (2 * r * (q - 1) + 1 : ℕ)) :
    az - a ≤ iz - i := by
  by_contra! h
  have hgap : 0 < az + i - a - iz := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((iz * Real.logb 2 (2 * r : ℕ)) / (az + i - a - iz))
  let n := m + 1
  let q := 2 ^ n
  have hq : 2 ≤ q := by
    dsimp [q, n]
    rw [pow_succ]
    have : 0 < (2 : ℕ) ^ m := by positivity
    omega
  have hlogq : Real.logb 2 q = n := by
    simp [q, Nat.cast_pow, Real.logb_pow]
  have hsize : 2 * r * (q - 1) + 1 ≤ 2 * r * q := by
    have heq : q = (q - 1) + 1 := by omega
    conv_rhs => rw [heq, Nat.mul_add, Nat.mul_one]
    omega
  have hlogL : Real.logb 2 (2 * r * (q - 1) + 1 : ℕ) ≤
      Real.logb 2 (2 * r : ℕ) + n := by
    rw [← hlogq, ← Real.logb_mul (by positivity) (by positivity)]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    exact_mod_cast hsize
  have hcomp := (hfinite q hq).trans (add_le_add_right (mul_le_mul_of_nonneg_left hlogL hiz) _)
  rw [hlogq] at hcomp
  have hlarge : iz * Real.logb 2 (2 * r : ℕ) < n * (az + i - a - iz) := by
    exact (div_lt_iff₀ hgap).mp (hm.trans_le (by exact_mod_cast Nat.le_succ m))
  linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
def triangleWireTerm (q : ℕ) (s : Fin q × Fin q × Fin q) : Fin 3 → Fin q × Fin q :=
  ![(s.1, s.2.1), (s.2.1, s.2.2), (s.2.2, s.1)]
theorem triangleWireTerm_injective (q : ℕ) : Function.Injective (triangleWireTerm q) := by
  intro a b h
  have h₀ : (a.1, a.2.1) = (b.1, b.2.1) := congrFun h 0
  have h₁ : a.2 = b.2 := congrFun h 1
  exact Prod.ext (congrArg (Prod.fst : Fin q × Fin q → Fin q) h₀) h₁
noncomputable def triangleAPTensor (K : Type*) [Field K] (q : ℕ)
    (x : Fin 3 → Fin q × Fin q) : K :=
  ∑ s : Fin q × Fin q × Fin q, if x = triangleWireTerm q s ∧
    (s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val = 0 then 1 else 0
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Polynomial
section
open scoped Classical
theorem basisTensor_zeroWeight_mem_closure (K : Type*) [Field K] [Infinite K]
    {I J : Type*} [Fintype I] [Fintype J] {A : I → Type*} [∀ i, Fintype (A i)]
    (a : J → ∀ i, A i) (w : ∀ i, A i → ℤ) (hw : ∀ j, 0 ≤ ∑ i, w i (a j i)) :
    (fun x ↦ ∑ j, if x = a j ∧ ∑ i, w i (a j i) = 0 then 1 else 0) ∈
      affineZariskiClosure {Y | Crossing.IsRestriction Y (Crossing.basisTensor (F := K) a)} := by
  classical
  let e (j : J) : ℤ := ∑ i, w i (a j i)
  let P (x : ∀ i, A i) : K[X] := ∑ j, if x = a j then X ^ (e j).toNat else 0
  have ht (t : K) (ht : t ≠ 0) : (fun x ↦ (P x).eval t) ∈
      {Y | Crossing.IsRestriction Y (Crossing.basisTensor (F := K) a)} := by
    apply (Crossing.restriction_basisTensor_iff _ _).mpr
    refine ⟨fun i b c ↦ if b = c then t ^ w i c else 0, fun x ↦ ?_⟩
    simp only [P, Polynomial.eval_finsetSum, Fintype.prod_ite_zero]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : x = a j
    · subst x
      simp only [ite_true, eval_X_pow, ← zpow_natCast, e, Int.toNat_of_nonneg (hw j)]
      rw [ite_eq_left_of_eq_true _ _ (propext ⟨fun _ ↦ trivial, fun _ _ ↦ trivial⟩)]
      exact Finset.induction_on (motive := fun s ↦ t ^ (∑ i ∈ s, w i (a j i)) =
        ∏ i ∈ s, t ^ w i (a j i)) Finset.univ (by simp) (fun i s hi ih ↦ by
          simp [hi, zpow_add₀ ht, ih])
    · simp [h, ← funext_iff]
  have hzero (x : ∀ i, A i) : (P x).eval 0 =
      ∑ j, if x = a j ∧ ∑ i, w i (a j i) = 0 then 1 else 0 := by
    simp only [P, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hx : x = a j
    · by_cases he : e j = 0
      · have he' : ∑ i, w i (a j i) = 0 := he
        simp [hx, he, he']
      · have hpos : (e j).toNat ≠ 0 := by have hh := hw j; change 0 ≤ e j at hh; omega
        simp [hx, zero_pow hpos, ← show e j = ∑ i, w i (a j i) from rfl, he]
    · simp [hx]
  rw [← funext hzero]
  exact polynomialCurve_zero_mem_affineZariskiClosure P ht
private def triangleAPWeight (q : ℕ) : Fin 3 → Fin q × Fin q → ℤ :=
  ![fun x ↦ ((x.1.val : ℤ) - 2 * x.2.val) ^ 2,
    fun x ↦ (x.2.val : ℤ) ^ 2 - 4 * x.1.val * x.2.val,
    fun x ↦ 2 * (x.1.val : ℤ) * x.2.val]
private theorem triangleAPWeight_sum {q : ℕ} (s : Fin q × Fin q × Fin q) :
    ∑ i, triangleAPWeight q i (triangleWireTerm q s i) =
      ((s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val) ^ 2 := by
  rw [Fin.sum_univ_three]
  change ((s.1.val : ℤ) - 2 * s.2.1.val) ^ 2 +
    ((s.2.2.val : ℤ) ^ 2 - 4 * s.2.1.val * s.2.2.val) +
    2 * (s.2.2.val : ℤ) * s.1.val = _
  ring
theorem triangleAPTensor_mem_restrictionClosure (K : Type*) [Field K] [Infinite K] (q : ℕ) :
    triangleAPTensor K q ∈ affineZariskiClosure {Y | Crossing.IsRestriction Y
      (Crossing.basisTensor (F := K) (triangleWireTerm q))} := by
  have h := basisTensor_zeroWeight_mem_closure K (triangleWireTerm q) (triangleAPWeight q)
    (fun j ↦ triangleAPWeight_sum j ▸ sq_nonneg _)
  convert h using 1
  funext x
  simp [triangleAPTensor, triangleAPWeight_sum]
theorem triangleAPTensor_value_le_wire (K : Type*) [Field K] (q : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} (Fin 3) K → _ → Prop)) :
    SiteTensor.coeffValue φ (triangleAPTensor K q) ≤ SiteTensor.coeffValue φ
      (Crossing.basisTensor (F := K) (triangleWireTerm q)) := by
  apply SiteTensor.coeffValue_le_of_geometric_restriction (E := AlgebraicClosure K)
  have ht : (fun b ↦ algebraMap K (AlgebraicClosure K) (triangleAPTensor K q b)) =
      triangleAPTensor (AlgebraicClosure K) q := by
    funext b
    simp [triangleAPTensor]
  have hs : (fun b ↦ algebraMap K (AlgebraicClosure K) (Crossing.basisTensor (triangleWireTerm q) b)) =
      Crossing.basisTensor (F := AlgebraicClosure K) (triangleWireTerm q) := by
    funext b
    simp [Crossing.basisTensor]
  rw [ht, hs]
  exact triangleAPTensor_mem_restrictionClosure (AlgebraicClosure K) q
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open SiteTensor
private def twiceLabel {r : ℕ} (s : Fin r) : Fin (2*r) := ⟨2*s.val, by omega⟩
private def sumLabel {r : ℕ} (s t : Fin r) : Fin (2*r) := ⟨s.val+t.val, by omega⟩
private def progression {r : ℕ} (a : Fin r × Fin r) : Fin (2*r) × Fin (2*r) × Fin (2*r) :=
  (twiceLabel a.1, sumLabel a.1 a.2, twiceLabel a.2)
private def readPair {r : ℕ} (i : Fin 3) (a : Fin r × Fin r) :=
  triangleWireTerm (2*r) (progression a) i
private theorem progression_weight {r : ℕ} (a : Fin r × Fin r) :
    let s := progression a
    (s.1.val : ℤ) - 2 * (s.2.1.val : ℤ) + (s.2.2.val : ℤ) = 0 := by
  simp [progression, twiceLabel, sumLabel]
  ring
private theorem coherent_of_progression {r : ℕ} (x : Fin 3 → Fin r × Fin r)
    (s : Fin (2*r) × Fin (2*r) × Fin (2*r))
    (hread : (fun i ↦ readPair i (x i)) = triangleWireTerm (2*r) s)
    (hAP : (s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val = 0) : ∀ i, x i = x 0 := by
  have h₀ : (twiceLabel (x 0).1, sumLabel (x 0).1 (x 0).2) = (s.1, s.2.1) := congrFun hread 0
  have h₁ : (sumLabel (x 1).1 (x 1).2, twiceLabel (x 1).2) = (s.2.1, s.2.2) := congrFun hread 1
  have h₂ : (twiceLabel (x 2).2, twiceLabel (x 2).1) = (s.2.2, s.1) := congrFun hread 2
  have first {a b c d : Fin (2*r)} (h : (a,b) = (c,d)) : a.val = c.val := congrArg (fun p ↦ p.1.val) h
  have second {a b c d : Fin (2*r)} (h : (a,b) = (c,d)) : b.val = d.val := congrArg (fun p ↦ p.2.val) h
  have h0a := first h₀
  have h0b := second h₀
  have h1a := first h₁
  have h1b := second h₁
  have h2a := first h₂
  have h2b := second h₂
  simp only [twiceLabel, sumLabel] at h0a h0b h1a h1b h2a h2b
  intro i
  fin_cases i
  · rfl
  · change x 1 = x 0
    apply Prod.ext <;> apply Fin.ext <;> omega
  · change x 2 = x 0
    apply Prod.ext <;> apply Fin.ext <;> omega
private theorem triangleAPTensor_eq_indicator (K : Type*) [Field K] (q : ℕ)
    (x : Fin 3 → Fin q × Fin q) :
    triangleAPTensor K q x = if ∃ s : Fin q × Fin q × Fin q, x = triangleWireTerm q s ∧
      (s.1.val : ℤ) - 2 * s.2.1.val + s.2.2.val = 0 then 1 else 0 := by
  classical
  unfold triangleAPTensor
  split_ifs with h
  · obtain ⟨s, hs, hp⟩ := h
    rw [Finset.sum_eq_single s]
    · simp [hs,hp]
    · intro t _ hts
      exact ite_eq_right fun hc ↦ hts (triangleWireTerm_injective q (hc.1.symm.trans hs))
    · simp
  · apply Finset.sum_eq_zero
    intro s _
    exact ite_eq_right fun hp ↦ h ⟨s,hp⟩
theorem diagonal_restricts_triangleAPTensor (K : Type*) [Field K] (r : ℕ) :
    Crossing.IsRestriction (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff (triangleAPTensor K (2*r)) := by
  classical
  let Y : Raw.{0} (Fin 3) K := ⟨fun _ ↦ Fin (2*r) × Fin (2*r), fun _ ↦ inferInstance, triangleAPTensor K (2*r)⟩
  apply Raw.restrict_by_read (X := Raw.diagonal (Fin 3) K (Fin r × Fin r)) (Y := Y) readPair
  intro x
  change (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff x = triangleAPTensor K _ (fun i ↦ readPair i (x i))
  rw [Raw.diagonal_coeff_at (0 : Fin 3) x, triangleAPTensor_eq_indicator]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨progression (x 0), funext (fun i ↦ congrArg (readPair i) (h i)), progression_weight _⟩
  · rintro ⟨s, hs, hp⟩
    exact coherent_of_progression x s hs hp
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open SiteTensor
theorem triangleDiagonal_value_le (K : Type*) [Field K] (r : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop)) :
    coeffValue φ (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff ≤
      coeffValue φ (Crossing.basisTensor (F := K) (triangleWireTerm (2*r))) :=
  (φ.2.2.2.2.2 _ _ (show ofCoeffs (Raw.diagonal (Fin 3) K (Fin r × Fin r)).coeff ≤
    ofCoeffs (triangleAPTensor K (2*r)) from diagonal_restricts_triangleAPTensor K r)).trans
    (triangleAPTensor_value_le_wire K (2*r) φ)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
noncomputable section
open MatrixMultiplication.Foundation
open scoped NNReal
section
structure RankFunctional (F : Type*) [Field F] where
  value {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] : Tensor F X Y Z → ℝ≥0
  diagonal (r : ℕ) : value (Tensor.diagonal (K := F) (Fin r)) = r
  product {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
      [Fintype U] [Fintype V] [Fintype W] (T : Tensor F X Y Z) (S : Tensor F U V W) :
    value (Tensor.product T S) = value T * value S
  restrict_le {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
      [Fintype U] [Fintype V] [Fintype W] (T : Tensor F X Y Z)
      (A : U → X → F) (B : V → Y → F) (C : W → Z → F) :
    value (Tensor.restrict A B C T) ≤ value T
namespace RankFunctional
variable {F : Type*} [Field F] (φ : RankFunctional F)
variable {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
theorem pullback_le (T : Tensor F X Y Z) (a : U → X) (b : V → Y) (c : W → Z) :
    φ.value (Tensor.pullback a b c T) ≤ φ.value T := by
  classical
  convert φ.restrict_le T
      (fun u x => if x = a u then 1 else 0)
      (fun v y => if y = b v then 1 else 0)
      (fun w z => if z = c w then 1 else 0) using 2
  funext u v w
  simp [Tensor.pullback, Tensor.restrict, ite_mul, mul_ite]
theorem pullback_equiv (T : Tensor F X Y Z) (a : U ≃ X) (b : V ≃ Y) (c : W ≃ Z) :
    φ.value (Tensor.pullback a b c T) = φ.value T := by
  refine le_antisymm (φ.pullback_le T a b c) ?_
  have h := φ.pullback_le (Tensor.pullback a b c T) a.symm b.symm c.symm
  have heq : Tensor.pullback a.symm b.symm c.symm (Tensor.pullback a b c T) = T := by
    funext x y z
    simp [Tensor.pullback]
  rwa [heq] at h
end RankFunctional
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
open MatrixMultiplication.Foundation
section
def wire12 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F (Fin n) (Fin n) Unit :=
  fun i j _ ↦ if i = j then 1 else 0
def wire23 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F Unit (Fin n) (Fin n) :=
  fun _ i j ↦ if i = j then 1 else 0
def wire31 (F : Type*) [Zero F] [One F] (n : ℕ) : Tensor F (Fin n) Unit (Fin n) :=
  fun i _ j ↦ if j = i then 1 else 0
def wireSite1Equiv (n12 n31 : ℕ) :
    Fin n31 × Fin n12 ≃ (Fin n12 × Unit) × Fin n31 where
  toFun x := ((x.2, ()), x.1)
  invFun x := (x.2, x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
def wireSite2Equiv (n12 n23 : ℕ) :
    Fin n12 × Fin n23 ≃ (Fin n12 × Fin n23) × Unit where
  toFun x := (x, ())
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
def wireSite3Equiv (n23 n31 : ℕ) :
    Fin n23 × Fin n31 ≃ (Unit × Fin n23) × Fin n31 where
  toFun x := (((), x.1), x.2)
  invFun x := (x.1.2, x.2)
  left_inv _ := rfl
  right_inv _ := rfl
theorem matrixTensor_eq_wireProduct (F : Type*) [Field F] (n12 n23 n31 : ℕ) :
    matrixTensor F n12 n23 n31 =
      Tensor.pullback (wireSite1Equiv n12 n31) (wireSite2Equiv n12 n23) (wireSite3Equiv n23 n31)
        (Tensor.product (Tensor.product (wire12 F n12) (wire23 F n23)) (wire31 F n31)) := by
  funext x y z
  simp only [matrixTensor, Tensor.matrixCoefficients, Tensor.pullback, Tensor.product,
    wire12, wire23, wire31, wireSite1Equiv, wireSite2Equiv, wireSite3Equiv,
    Equiv.coe_fn_mk]
  by_cases h12 : x.2 = y.1 <;> by_cases h23 : y.2 = z.1 <;>
    by_cases h31 : z.2 = x.1 <;> simp [h12, h23, h31]
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
namespace SiteTensor
open MatrixMultiplication.Foundation
open scoped BigOperators Classical NNReal
noncomputable section
private def tuple {A : Fin 3 → Type*} (x : A 0) (y : A 1) (z : A 2) : ∀ i, A i :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i => i.elim0)))
private def coords (A : Fin 3 → Type*) : (∀ i, A i) ≃ A 0 × A 1 × A 2 :=
  (Fin.consEquiv A).symm.trans ((Equiv.refl _).prodCongr (piFinTwoEquiv _))
variable {F : Type*} [CommSemiring F] {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
def ofThree (T : Tensor F X Y Z) : Raw (Fin 3) F where
  Leg := ![X, Y, Z]
  finiteLeg := tuple (inferInstanceAs (Fintype X)) (inferInstanceAs (Fintype Y)) (inferInstanceAs (Fintype Z))
  coeff := fun x => T (x 0) (x 1) (x 2)
theorem ofThree_restrict (T : Tensor F X Y Z) (A : U → X → F) (B : V → Y → F) (C : W → Z → F) :
    (ofThree (Tensor.restrict A B C T)).Restricts (ofThree T) := by
  let : DecidableEq (Fin 3) := fun i j => Classical.propDecidable (i = j)
  let M : ∀ i, (ofThree (Tensor.restrict A B C T)).Leg i → (ofThree T).Leg i → F := tuple A B C
  refine ⟨M, fun p => ?_⟩
  change (∑ x, ∑ y, ∑ z, A (p 0) x * B (p 1) y * C (p 2) z * T x y z) =
    ∑ q : (i : Fin 3) → (ofThree T).Leg i, T (q 0) (q 1) (q 2) * ∏ i, M i (p i) (q i)
  let e := coords (ofThree T).Leg
  calc
    _ = ∑ q : X × Y × Z, A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2 * T q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = _ := by
      apply Fintype.sum_equiv e.symm
      intro q
      simp only [Fin.prod_univ_three]
      change A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2 * T q.1 q.2.1 q.2.2 =
        T q.1 q.2.1 q.2.2 * (A (p 0) q.1 * B (p 1) q.2.1 * C (p 2) q.2.2)
      ac_rfl
theorem ofThree_product (T : Tensor F X Y Z) (S : Tensor F U V W) :
    (ofThree (Tensor.product T S)).Equivalent ((ofThree T).mul (ofThree S)) := by
  let e : ∀ i, (ofThree (Tensor.product T S)).Leg i ≃ ((ofThree T).mul (ofThree S)).Leg i :=
    tuple (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  apply Raw.reindex_equivalent e
  intro p
  rfl
private theorem diagonal_eq_sum {α : Type} [Fintype α] [DecidableEq α] (q : Fin 3 → α) :
    (if q 0 = q 1 ∧ q 0 = q 2 then (1 : F) else 0) =
      ∑ a : α, @ite F (q = fun _ => a) (Classical.propDecidable _) 1 0 := by
  have eq (a : α) : q = (fun _ => a) ↔ q 0 = a ∧ q 1 = a ∧ q 2 = a := by
    simp [funext_iff, Fin.forall_fin_succ]
  simp_rw [eq]
  rw [Finset.sum_eq_single (q 0)]
  · simp [eq_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp
theorem ofThree_diagonal (α : Type) [Fintype α] [DecidableEq α] :
    (ofThree (Tensor.diagonal (K := F) α)).Equivalent (Raw.diagonal (Fin 3) F α) := by
  let e : ∀ i, (ofThree (Tensor.diagonal (K := F) α)).Leg i ≃ α :=
    tuple (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  apply Raw.reindex_equivalent e
  intro x
  exact diagonal_eq_sum (F := F) (fun i => e i (x i))
def rankFunctionalOfSpectrum {K : Type*} [Field K]
    (f : normalizedSpectrum (fun x y : TensorClass.{0} (Fin 3) K => x ≤ y)) : RankFunctional K where
  value T := f.1 (ofRaw (ofThree T))
  diagonal r := by
    rw [ofRaw_eq_iff.mpr (ofThree_diagonal (F := K) (Fin r)), ofRaw_diagonal_fin_eq_natCast]
    exact map_natCast (normalizedSpectrum.toRingHom f) r
  product T S := by
    rw [ofRaw_eq_iff.mpr (ofThree_product T S), ofRaw_mul]
    exact f.2.2.2.2.1 _ _
  restrict_le T A B C := f.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (ofThree_restrict T A B C))
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
namespace SiteTensor
open scoped Classical
private def occupiedLeg {α : Type} {p : Prop} (h : p) : α ≃ (p → α) where
  toFun a _ := a
  invFun f := f h
  left_inv _ := rfl
  right_inv _ := rfl
private def emptyLeg {α : Type} {p : Prop} (h : ¬ p) : Unit ≃ (p → α) where
  toFun _ hp := (h hp).elim
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := funext fun hp ↦ (h hp).elim
private def threeLegs {A : Fin 3 → Type*} (x : A 0) (y : A 1) (z : A 2) : ∀ i, A i :=
  Fin.cons x (Fin.cons y (Fin.cons z (fun i ↦ i.elim0)))
variable (F : Type*) [Field F]
private theorem coeff_pair_p1 {I α : Type} [Fintype I] [DecidableEq I] [Fintype α]
    (i j : I) (x : ∀ k, MaskLeg {i, j} α k) :
    (Raw.maskDiagonal F {i, j} α).coeff x =
      if x i (by simp) = x j (by simp) then 1 else 0 := by
  classical
  rw [Raw.maskDiagonal_coeff_at (K := F) {i, j} (Finset.mem_insert_self _ _) x]
  congr 1
  apply propext
  constructor
  · intro h
    exact (h j (by simp)).symm
  · intro h k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · rfl
    · obtain rfl := Finset.mem_singleton.mp hk
      exact h.symm
theorem ofRaw_ofThree_wire12 (n : ℕ) :
    ofRaw (ofThree (wire12 F n)) = ofRaw (Raw.maskDiagonal F ({0, 1} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {0, 1}
  let e : ∀ i, (ofThree (wire12 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (occupiedLeg (by decide)) (occupiedLeg (by decide)) (emptyLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair_p1 F (0 : Fin 3) 1 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire12]
  split_ifs <;> first | rfl | contradiction
theorem ofRaw_ofThree_wire23 (n : ℕ) :
    ofRaw (ofThree (wire23 F n)) = ofRaw (Raw.maskDiagonal F ({1, 2} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {1, 2}
  let e : ∀ i, (ofThree (wire23 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (emptyLeg (by decide)) (occupiedLeg (by decide)) (occupiedLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair_p1 F (1 : Fin 3) 2 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire23]
  split_ifs <;> first | rfl | contradiction
theorem ofRaw_ofThree_wire31 (n : ℕ) :
    ofRaw (ofThree (wire31 F n)) = ofRaw (Raw.maskDiagonal F ({2, 0} : Finset (Fin 3)) (Fin n)) := by
  let S : Finset (Fin 3) := {2, 0}
  let e : ∀ i, (ofThree (wire31 F n)).Leg i ≃ MaskLeg S (Fin n) i :=
    threeLegs (occupiedLeg (by decide)) (emptyLeg (by decide)) (occupiedLeg (by decide))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (coeff_pair_p1 F (2 : Fin 3) 0 (fun i ↦ e i (x i))).symm
  simp only [ofThree, wire31]
  split_ifs <;> first | rfl | contradiction
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
open SiteTensor Foundation
open scoped NNReal Classical
theorem triangleWire_class (K : Type*) [Field K] (q : ℕ) :
    ofCoeffs (Crossing.basisTensor (F := K) (triangleWireTerm q)) =
      ofRaw (ofThree (matrixTensor K q q q)) := by
  classical
  let e : ∀ i : Fin 3, (Fin q × Fin q) ≃ (ofThree (matrixTensor K q q q)).Leg i :=
    Fin.cons (Equiv.refl _) (Fin.cons (Equiv.refl _) (Fin.cons (Equiv.refl _) (fun i ↦ i.elim0)))
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  refine Eq.trans ?_ (show
    (if (x 0).2 = (x 1).1 ∧ (x 1).2 = (x 2).1 ∧ (x 2).2 = (x 0).1
     then (1 : K) else 0) = _ from ?_)
  swap
  · unfold ofThree matrixTensor Tensor.matrixCoefficients
    congr 1
  simp only [Crossing.basisTensor]
  let s := ((x 0).1, (x 0).2, (x 1).2)
  have he (t : Fin q × Fin q × Fin q) : x = triangleWireTerm q t ↔
      (x 0).2 = (x 1).1 ∧ (x 1).2 = (x 2).1 ∧ (x 2).2 = (x 0).1 ∧ t = s := by
    constructor
    · intro h
      subst x
      exact ⟨rfl,rfl,rfl,rfl⟩
    · rintro ⟨h₁, h₂, h₃, rfl⟩
      funext i
      fin_cases i
      · rfl
      · exact Prod.ext h₁.symm rfl
      · exact Prod.ext h₂.symm h₃
  simp_rw [he]
  by_cases h₁ : (x 0).2 = (x 1).1 <;> by_cases h₂ : (x 1).2 = (x 2).1 <;>
    by_cases h₃ : (x 2).2 = (x 0).1 <;> simp [h₁, h₂, h₃]
theorem triangleWire_value (K : Type*) [Field K] (q : ℕ)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop)) :
    coeffValue φ (Crossing.basisTensor (F := K) (triangleWireTerm q)) =
      φ.val (ofRaw (Raw.maskDiagonal K {0,1} (Fin q))) *
        φ.val (ofRaw (Raw.maskDiagonal K {1,2} (Fin q))) *
        φ.val (ofRaw (Raw.maskDiagonal K {2,0} (Fin q))) := by
  rw [coeffValue, triangleWire_class, ← ofRaw_ofThree_wire12, ← ofRaw_ofThree_wire23,
    ← ofRaw_ofThree_wire31]
  let ψ := rankFunctionalOfSpectrum φ
  change ψ.value (matrixTensor K q q q) = ψ.value (wire12 K q) * ψ.value (wire23 K q) *
    ψ.value (wire31 K q)
  rw [matrixTensor_eq_wireProduct, ψ.pullback_equiv, ψ.product, ψ.product]
theorem two_le_sum_binary_wire_logs {K : Type*} [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))
    (hbound : ∀ r : ℕ, (r : ℝ≥0) ^ 2 ≤
      coeffValue φ (Crossing.basisTensor (F := K) (triangleWireTerm (2 * r)))) :
    let D (i j : Fin 3) := Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K {i,j} (Fin 2))) : ℝ)
    2 ≤ D 0 1 + D 1 2 + D 2 0 := by
  let D (i j : Fin 3) (q : ℕ) := (φ.val (ofRaw (Raw.maskDiagonal K {i,j} (Fin q))) : ℝ)
  let b := Real.logb 2 (D 0 1 2) + Real.logb 2 (D 1 2 2) + Real.logb 2 (D 2 0 2)
  change 2 ≤ b
  have hb (n : ℕ) : 2 * (n : ℝ) ≤ b * (n+1) := by
    let r := 2 ^ n
    let q := 2 * r
    have hr : 0 < r := by positivity
    have hq : 0 < q := by positivity
    have h := hbound r
    rw [triangleWire_value] at h
    have h' : (r : ℝ)^2 ≤ D 0 1 q * D 1 2 q * D 2 0 q := by exact_mod_cast h
    have hpos (i j : Fin 3) : 0 < D i j q := by
      let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
      have hne := Raw.maskDiagonal_ne_zero (K := K) {i,j} (Finset.insert_nonempty _ _) (Fin q)
      have hone := φ.property.2.2.2.2 _ _ (show (1 : TensorClass.{0} (Fin 3) K) ≤ ofRaw (Raw.maskDiagonal K {i,j} (Fin q)) from
        Raw.one_restricts_of_nonzero _ hne)
      rw [φ.property.2.1] at hone
      exact_mod_cast zero_lt_one.trans_le hone
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by positivity) h'
    have logr : Real.logb 2 r = n := by simp [r, Real.logb_pow]
    have logq : Real.logb 2 q = n+1 := by
      simp [q, Nat.cast_mul, Real.logb_mul, hr.ne', logr, add_comm]
    have scale (i j : Fin 3) : Real.logb 2 (D i j q) = Real.logb 2 (D i j 2) * (n+1) := by
      rw [← logq]
      exact maskDiagonal_log_price φ {i,j} (Finset.insert_nonempty _ _) hq
    rw [Real.logb_pow, logr, Real.logb_mul (mul_pos (hpos 0 1) (hpos 1 2)).ne' (hpos 2 0).ne',
      Real.logb_mul (hpos 0 1).ne' (hpos 1 2).ne', scale, scale, scale] at hlog
    simpa only [b, add_mul, Nat.cast_ofNat] using hlog
  by_contra! hsmall
  obtain ⟨n, hn⟩ := exists_nat_gt (b / (2-b))
  have := (div_lt_iff₀ (sub_pos.mpr hsmall)).mp hn
  linarith [hb n]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open OAI.MatrixMultiplication
open scoped Classical NNReal
section
open SiteTensor
theorem two_le_sum_wire_logs (K : Type*) [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop)) :
    let D (i j : Fin 3) := Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K {i,j} (Fin 2))) : ℝ)
    2 ≤ D 0 1 + D 1 2 + D 2 0 := by
  apply two_le_sum_binary_wire_logs φ
  intro r
  have h := triangleDiagonal_value_le K r φ
  change φ.val (ofRaw (Raw.diagonal (Fin 3) K (Fin r × Fin r))) ≤ _ at h
  rw [ofRaw_diagonal_eq_natCast] at h
  change normalizedSpectrum.toRingHom φ _ ≤ _ at h
  simpa [map_natCast, pow_two] using h
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

abbrev T (I : Type) := Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ

section
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Reading one coordinate at each site against Kronecker deltas. -/
theorem sum_read {A : I → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (F : (∀ i, A i) → ℂ) (g : ∀ i, A i) :
    ∑ z, F z * ∏ i, (if g i = z i then (1 : ℂ) else 0) = F g := by
  classical
  rw [Finset.sum_eq_single g]
  · simp
  · intro b _ hb
    obtain ⟨i, hi⟩ : ∃ i, g i ≠ b i := by
      by_contra h
      push Not at h
      exact hb (funext fun i => (h i).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]
  · simp

variable (Φ : T I → ℝ)
variable (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
include hmono

/-- Reading coordinates through maps: the smaller tensor is a restriction. -/
theorem read_le {X S : T I} (g : ∀ i, Fin (X.1 i) → Fin (S.1 i))
    (h : ∀ x, X.2 x = S.2 (fun i => g i (x i))) : Φ X ≤ Φ S := by
  apply hmono S X
  refine ⟨fun i p q => if g i p = q then 1 else 0, fun y => ?_⟩
  rw [h y, ← sum_read S.2 (fun i => g i (y i))]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- The coordinate presentation of a raw tensor. -/
noncomputable def toSig (X : Raw.{0} I ℂ) : T I :=
  ⟨fun i => Fintype.card (X.Leg i), fun z => X.coeff (fun i => (Fintype.equivFin (X.Leg i)).symm (z i))⟩

omit hmono [Fintype I] [DecidableEq I] in
@[simp] theorem toSig_snd (X : Raw.{0} I ℂ) (z) :
    (toSig X).2 z = X.coeff (fun i => (Fintype.equivFin (X.Leg i)).symm (z i)) := rfl

theorem raw_read_le {X : Raw.{0} I ℂ} {S : T I} (g : ∀ i, X.Leg i → Fin (S.1 i))
    (h : ∀ x, X.coeff x = S.2 (fun i => g i (x i))) : Φ (toSig X) ≤ Φ S :=
  read_le Φ hmono (X := toSig X) (fun i p => g i ((Fintype.equivFin (X.Leg i)).symm p))
    (fun x => h _)

theorem read_raw_le {X : Raw.{0} I ℂ} {S : T I} (g : ∀ i, Fin (S.1 i) → X.Leg i)
    (h : ∀ z, S.2 z = X.coeff (fun i => g i (z i))) : Φ S ≤ Φ (toSig X) :=
  read_le Φ hmono (X := S) (S := toSig X) (fun i p => Fintype.equivFin (X.Leg i) (g i p))
    (fun z => by rw [h z]; show _ = X.coeff _; simp)

theorem raw_eq {X : Raw.{0} I ℂ} {S : T I} (e : ∀ i, X.Leg i ≃ Fin (S.1 i))
    (h : ∀ x, X.coeff x = S.2 (fun i => e i (x i))) : Φ (toSig X) = Φ S :=
  le_antisymm (raw_read_le Φ hmono (fun i => e i) h)
    (read_raw_le Φ hmono (fun i => (e i).symm) fun z => by simp [h])

theorem raw_mono {X Y : Raw.{0} I ℂ} (h : X.Restricts Y) : Φ (toSig X) ≤ Φ (toSig Y) := by
  obtain ⟨M, hM⟩ := h
  apply hmono (toSig Y) (toSig X)
  refine ⟨fun i p q => M i ((Fintype.equivFin _).symm p) ((Fintype.equivFin _).symm q),
    fun y => ?_⟩
  simp only [toSig_snd]
  rw [hM]
  have key := Fintype.sum_equiv (Equiv.piCongrRight fun i => (Fintype.equivFin (Y.Leg i))).symm
    (fun z => (∏ i, M i ((Fintype.equivFin (X.Leg i)).symm (y i))
      ((Fintype.equivFin (Y.Leg i)).symm (z i))) *
        Y.coeff (fun i => (Fintype.equivFin (Y.Leg i)).symm (z i)))
    (fun a => Y.coeff a * ∏ i, M i ((Fintype.equivFin (X.Leg i)).symm (y i)) (a i))
    (fun z => by rw [mul_comm]; rfl)
  refine Eq.trans ?_ (Eq.trans key.symm ?_)
  · convert rfl
  · rfl

end


section ops
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The coordinate direct sum, as in the target statement. -/
def sigAdd (X Y : T I) : T I :=
  ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩

/-- The coordinate tensor product, as in the target statement. -/
def sigMul (X Y : T I) : T I :=
  ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩

/-- The one-bit partial diagonal on `S`, as in the target statement. -/
def maskSig (S : Finset I) : T I :=
  ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩

noncomputable def addEquiv (X Y : Raw.{0} I ℂ) (i : I) :
    X.Leg i ⊕ Y.Leg i ≃ Fin (Fintype.card (X.Leg i) + Fintype.card (Y.Leg i)) :=
  (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv

noncomputable def mulEquiv (X Y : Raw.{0} I ℂ) (i : I) :
    X.Leg i × Y.Leg i ≃ Fin (Fintype.card (X.Leg i) * Fintype.card (Y.Leg i)) :=
  (Equiv.prodCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finProdFinEquiv

theorem mulEquiv_symm (X Y : Raw.{0} I ℂ) (i : I) (p : X.Leg i × Y.Leg i) :
    finProdFinEquiv.symm (mulEquiv X Y i p) =
      (Fintype.equivFin _ p.1, Fintype.equivFin _ p.2) := by
  rw [mulEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem addEquiv_inl (X Y : Raw.{0} I ℂ) (i : I) (a : X.Leg i) :
    ((addEquiv X Y i (Sum.inl a) : Fin _) : ℕ) = (Fintype.equivFin _ a : ℕ) := by
  rw [addEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.coe_castAdd]

theorem addEquiv_inr (X Y : Raw.{0} I ℂ) (i : I) (b : Y.Leg i) :
    ((addEquiv X Y i (Sum.inr b) : Fin _) : ℕ) = Fintype.card (X.Leg i) + (Fintype.equivFin _ b : ℕ) := by
  rw [addEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.coe_natAdd]

theorem mul_coeff (X Y : Raw.{0} I ℂ) (x : ∀ i, X.Leg i × Y.Leg i) :
    (X.mul Y).coeff x = (sigMul (toSig X) (toSig Y)).2 (fun i => mulEquiv X Y i (x i)) := by
  dsimp only [sigMul, toSig, Raw.mul]
  simp only [mulEquiv_symm, Equiv.symm_apply_apply]

theorem add_coeff [Nonempty I] (X Y : Raw.{0} I ℂ) (x : ∀ i, X.Leg i ⊕ Y.Leg i) :
    (X.add Y).coeff x = (sigAdd (toSig X) (toSig Y)).2 (fun i => addEquiv X Y i (x i)) := by
  classical
  show sumCoeff X.coeff Y.coeff x = _
  dsimp only [sigAdd, toSig]
  by_cases hL : ∀ i, ∃ a, x i = Sum.inl a
  · choose a ha using hL
    obtain rfl : x = fun i => Sum.inl (a i) := funext ha
    rw [sumCoeff_inl]
    have hlt : ∀ i, ((addEquiv X Y i (Sum.inl (a i)) : Fin _) : ℕ) < Fintype.card (X.Leg i) := by
      intro i; rw [addEquiv_inl]; exact (Fintype.equivFin _ (a i)).isLt
    rw [dif_pos hlt]
    congr 1
    funext i
    apply (Fintype.equivFin _).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext (addEquiv_inl X Y i (a i)).symm
  · by_cases hR : ∀ i, ∃ b, x i = Sum.inr b
    · choose b hb using hR
      obtain rfl : x = fun i => Sum.inr (b i) := funext hb
      rw [sumCoeff_inr]
      obtain ⟨i₀⟩ := ‹Nonempty I›
      have hnlt : ¬ ∀ i, ((addEquiv X Y i (Sum.inr (b i)) : Fin _) : ℕ) < Fintype.card (X.Leg i) := by
        intro h; have := h i₀; rw [addEquiv_inr] at this
        omega
      have hge : ∀ i, Fintype.card (X.Leg i) ≤ ((addEquiv X Y i (Sum.inr (b i)) : Fin _) : ℕ) := by
        intro i; rw [addEquiv_inr]; exact Nat.le_add_right _ _
      rw [dif_neg hnlt, dif_pos hge]
      congr 1
      funext i
      apply (Fintype.equivFin _).injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      simp only [addEquiv_inr]
      omega
    · push Not at hL hR
      obtain ⟨i, hi⟩ := hL
      obtain ⟨j, hj⟩ := hR
      rw [sumCoeff_mixed]
      · obtain ⟨b, hb⟩ : ∃ b, x i = Sum.inr b := by
          rcases h : x i with a | b
          · exact absurd h (hi a)
          · exact ⟨b, rfl⟩
        obtain ⟨a, ha⟩ : ∃ a, x j = Sum.inl a := by
          rcases h : x j with a | b
          · exact ⟨a, rfl⟩
          · exact absurd h (hj b)
        have h1 : ¬ ∀ k, ((addEquiv X Y k (x k) : Fin _) : ℕ) < Fintype.card (X.Leg k) := by
          intro h; have := h i; rw [hb, addEquiv_inr] at this
          omega
        have h2 : ¬ ∀ k, Fintype.card (X.Leg k) ≤ ((addEquiv X Y k (x k) : Fin _) : ℕ) := by
          intro h; have := h j; rw [ha, addEquiv_inl] at this
          have := (Fintype.equivFin _ a).isLt
          omega
        rw [dif_neg h1, dif_neg h2]
      · intro a h; exact hi (a i) (congrFun h i).symm
      · intro b h; exact hj (b j) (congrFun h j).symm

end ops


section mask
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Reading a mask leg as a coordinate. -/
def maskTo (S : Finset I) (i : I) (f : MaskLeg S (Fin 2) i) : Fin (if i ∈ S then 2 else 1) :=
  ⟨if h : i ∈ S then (f h : ℕ) else 0, by
    split_ifs with h
    · exact (f h).isLt
    · exact Nat.zero_lt_one⟩

/-- Reading a coordinate as a mask leg. -/
def maskFrom (S : Finset I) (i : I) (z : Fin (if i ∈ S then 2 else 1)) : MaskLeg S (Fin 2) i :=
  fun h => ⟨z, by have := z.isLt; simp only [h, if_true] at this; exact this⟩

theorem maskTo_val (S : Finset I) (i : I) (hi : i ∈ S) (f : MaskLeg S (Fin 2) i) :
    ((maskTo S i f : Fin _) : ℕ) = (f hi : ℕ) := by
  simp [maskTo, hi]

theorem mask_le (Φ : T I → ℝ) (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
    (S : Finset I) (hS : S.Nonempty) :
    Φ (toSig (Raw.maskDiagonal ℂ S (Fin 2))) = Φ (maskSig S) := by
  obtain ⟨i₀, hi₀⟩ := hS
  apply le_antisymm
  · refine raw_read_le Φ hmono (S := maskSig S) (fun i f => maskTo S i f) (fun x => ?_)
    refine (Raw.maskDiagonal_coeff_at S hi₀ x).trans ?_
    show _ = if ∀ i ∈ S, ∀ j ∈ S, ((maskTo S i (x i) : Fin _) : ℕ) = maskTo S j (x j) then 1 else 0
    by_cases hc : ∀ (i : I) (hi : i ∈ S), x i hi = x i₀ hi₀
    · rw [if_pos hc, if_pos]
      intro i hi j hj
      exact (maskTo_val S i hi (x i)).trans ((congrArg Fin.val (hc i hi)).trans
        ((congrArg Fin.val (hc j hj)).symm.trans (maskTo_val S j hj (x j)).symm))
    · rw [if_neg hc, if_neg]
      intro hall
      apply hc
      intro i hi
      apply Fin.ext
      have := hall i hi i₀ hi₀
      exact (maskTo_val S i hi (x i)).symm.trans (this.trans (maskTo_val S i₀ hi₀ (x i₀)))
  · refine read_raw_le Φ hmono (X := Raw.maskDiagonal ℂ S (Fin 2)) (S := maskSig S)
      (fun i z => maskFrom S i z) (fun z => ?_)
    refine Eq.trans ?_ (Raw.maskDiagonal_coeff_at S hi₀ (fun i => maskFrom S i (z i))).symm
    show (if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then (1 : ℂ) else 0) = _
    by_cases hc : ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j
    · rw [if_pos hc, if_pos]
      intro i hi
      exact Fin.ext (hc i hi i₀ hi₀)
    · rw [if_neg hc, if_neg]
      intro hall
      apply hc
      intro i hi j hj
      have h1 := congrArg Fin.val (hall i hi)
      have h2 := congrArg Fin.val (hall j hj)
      exact h1.trans h2.symm

end mask


section spec
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The spectral point on tensor classes induced by a coordinate spectral point. -/
noncomputable def phiClass (Φ : T I → ℝ) (h0 : ∀ X, 0 ≤ Φ X) (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) :
    TensorClass.{0} I ℂ → NNReal :=
  Quotient.lift (s := Raw.setoid.{0} I ℂ) (fun X => ⟨Φ (toSig X), h0 _⟩)
    (fun _ _ h => Subtype.ext (le_antisymm (raw_mono Φ hmono h.1) (raw_mono Φ hmono h.2)))

theorem phiClass_mem [Nonempty I] (Φ : T I → ℝ) (h0 : ∀ X, 0 ≤ Φ X)
    (h1 : Φ ⟨fun _ => 1, fun _ => 1⟩ = 1)
    (hz : ∀ X : T I, (∀ z, X.2 z = 0) → Φ X = 0)
    (hmono : ∀ X Y : T I,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X)
    (hmul : ∀ X Y : T I, Φ (sigMul X Y) = Φ X * Φ Y)
    (hadd : ∀ X Y : T I, Φ (sigAdd X Y) = Φ X + Φ Y) :
    phiClass Φ h0 hmono ∈ normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show Φ (toSig (Raw.zero I ℂ)) = 0
    exact hz _ (fun _ => rfl)
  · apply Subtype.ext
    show Φ (toSig (Raw.one I ℂ)) = 1
    rw [raw_eq Φ hmono (S := ⟨fun _ => 1, fun _ => 1⟩) (fun _ => ⟨fun _ => 0, fun _ => PUnit.unit, fun _ => rfl,
        fun _ => Subsingleton.elim _ _⟩)
      (fun _ => rfl)]
    exact h1
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y => ?_
    apply Subtype.ext
    show Φ (toSig (X.add Y)) = Φ (toSig X) + Φ (toSig Y)
    rw [raw_eq Φ hmono (S := sigAdd (toSig X) (toSig Y)) (addEquiv X Y) (add_coeff X Y)]
    exact hadd _ _
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y => ?_
    apply Subtype.ext
    show Φ (toSig (X.mul Y)) = Φ (toSig X) * Φ (toSig Y)
    rw [raw_eq Φ hmono (S := sigMul (toSig X) (toSig Y)) (mulEquiv X Y) (mul_coeff X Y)]
    exact hmul _ _
  · intro x y
    refine Quotient.inductionOn₂ (s₁ := Raw.setoid.{0} I ℂ) (s₂ := Raw.setoid.{0} I ℂ) x y
      fun X Y h => ?_
    exact raw_mono Φ hmono h

end spec

end OMAPort


namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

section rev
variable {I : Type} [Fintype I] [DecidableEq I]

/-- A coordinate tensor as a raw tensor with the same coefficients. -/
abbrev sigRaw (X : T I) : Raw.{0} I ℂ := ⟨fun i => Fin (X.1 i), fun _ => inferInstance, X.2⟩

variable [Nonempty I] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))

/-- A spectral point read on coordinate tensors. -/
noncomputable def psi (X : T I) : ℝ := (φ.val (ofRaw (sigRaw X)) : ℝ)

theorem psi_nonneg (X : T I) : 0 ≤ psi φ X := (φ.val _).2

theorem psi_mono (X Y : T I) (h : ∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
    ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) : psi φ Y ≤ psi φ X := by
  obtain ⟨A, hA⟩ := h
  have hr : (sigRaw Y).Restricts (sigRaw X) := by
    refine ⟨A, fun y => ?_⟩
    change Y.2 y = _
    rw [hA y, show (∑ z, (∏ i, A i (y i) (z i)) * X.2 z) = ∑ z, X.2 z * ∏ i, A i (y i) (z i) from
      Finset.sum_congr rfl fun z _ => mul_comm _ _]
    convert rfl
  have := φ.2.2.2.2.2 _ _ ((ofRaw_le_iff).mpr hr)
  exact_mod_cast this

theorem psi_eq_of_equiv {R : Raw.{0} I ℂ} {S : T I} (e : ∀ i, R.Leg i ≃ Fin (S.1 i))
    (h : ∀ x, R.coeff x = S.2 (fun i => e i (x i))) : psi φ S = (φ.val (ofRaw R) : ℝ) := by
  have he : ofRaw R = ofRaw (sigRaw S) := ofRaw_eq_iff.mpr (Raw.reindex_equivalent e h)
  rw [psi, he]

theorem psi_one : psi φ ⟨fun _ => 1, fun _ => 1⟩ = 1 := by
  rw [psi_eq_of_equiv φ (R := Raw.one I ℂ) (S := ⟨fun _ => 1, fun _ => 1⟩) (fun _ => ⟨fun _ => 0, fun _ => PUnit.unit, fun _ => rfl,
      fun _ => Subsingleton.elim _ _⟩) (fun _ => rfl), ofRaw_one, φ.2.2.1]
  rfl

theorem psi_zero (X : T I) (h : ∀ z, X.2 z = 0) : psi φ X = 0 := by
  have h0 : ofRaw (sigRaw X) = 0 := (ofRaw_eq_zero_iff _).mpr (funext h)
  rw [psi, h0, φ.2.1]
  rfl

theorem psi_mul (X Y : T I) : psi φ (sigMul X Y) = psi φ X * psi φ Y := by
  let R : Raw.{0} I ℂ := ⟨fun i => Fin (X.1 i) × Fin (Y.1 i), fun _ => inferInstance,
    fun x => X.2 (fun i => (x i).1) * Y.2 (fun i => (x i).2)⟩
  have hR : ofRaw R = ofRaw (sigRaw X) * ofRaw (sigRaw Y) := rfl
  rw [psi_eq_of_equiv φ (R := R) (S := sigMul X Y) (fun _ => finProdFinEquiv) (fun x => ?_), hR,
    φ.2.2.2.2.1]
  · rfl
  show X.2 (fun i => (x i).1) * Y.2 (fun i => (x i).2) =
    X.2 (fun i => (finProdFinEquiv.symm (finProdFinEquiv (x i))).1) *
      Y.2 (fun i => (finProdFinEquiv.symm (finProdFinEquiv (x i))).2)
  simp only [Equiv.symm_apply_apply]

theorem psi_add (X Y : T I) : psi φ (sigAdd X Y) = psi φ X + psi φ Y := by
  let R : Raw.{0} I ℂ := ⟨fun i => Fin (X.1 i) ⊕ Fin (Y.1 i), fun _ => inferInstance, sumCoeff X.2 Y.2⟩
  have hR : ofRaw R = ofRaw (sigRaw X) + ofRaw (sigRaw Y) := rfl
  rw [psi_eq_of_equiv φ (R := R) (S := sigAdd X Y) (fun _ => finSumFinEquiv) (fun x => ?_), hR,
    φ.2.2.2.1]
  · rfl
  show sumCoeff X.2 Y.2 x =
    if h : ∀ i, ((finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)) : ℕ) < X.1 i then
      X.2 (fun i => ⟨finSumFinEquiv (x i), h i⟩)
    else if h' : ∀ i, X.1 i ≤ ((finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)) : ℕ) then
      Y.2 (fun i => ⟨(finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)) - X.1 i, by
        have h2 := (finSumFinEquiv (x i) : Fin (X.1 i + Y.1 i)).2; have := h' i; omega⟩)
    else 0
  split_ifs with h1 h2
  · have hx : ∀ i, ∃ a, x i = Sum.inl a := by
      intro i
      rcases hxi : x i with a | b
      · exact ⟨a, rfl⟩
      · exfalso
        have := h1 i
        rw [hxi] at this
        simp at this
    choose a ha using hx
    obtain rfl : x = fun i => Sum.inl (a i) := funext ha
    rw [sumCoeff_inl]
    exact congrArg X.2 (funext fun i => Fin.ext (by simp))
  · have hx : ∀ i, ∃ b, x i = Sum.inr b := by
      intro i
      rcases hxi : x i with a | b
      · exfalso
        have := h2 i
        rw [hxi] at this
        simp at this
        omega
      · exact ⟨b, rfl⟩
    choose b hb using hx
    obtain rfl : x = fun i => Sum.inr (b i) := funext hb
    rw [sumCoeff_inr]
    exact congrArg Y.2 (funext fun i => Fin.ext (by simp))
  · rw [sumCoeff_mixed]
    · intro a h
      apply h1
      intro i
      rw [← h]
      simp
    · intro b h
      apply h2
      intro i
      rw [← h]
      simp

/-- The mask diagonal read through `psi`. -/
theorem psi_mask (S : Finset I) (hS : S.Nonempty) :
    psi φ (maskSig S) = (φ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ) := by
  have h := mask_le (psi φ) (psi_mono φ) S hS
  have e : psi φ (toSig (Raw.maskDiagonal ℂ S (Fin 2))) =
      (φ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ) :=
    psi_eq_of_equiv φ (fun i => Fintype.equivFin _) (fun x => congrArg _ (funext fun i => ((Fintype.equivFin _).symm_apply_apply (x i)).symm))
  rw [← e, h]

end rev

end OMAPort
namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

section glue
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The wire tensor of the parent statement: one shared bit between the sites `s` and `t`. -/
def wireT (s t : I) : T I :=
  ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩

/-- The unit tensor. -/
def unitT : T I := ⟨fun _ => 1, fun _ => 1⟩

/-- A spectral point in the coordinate encoding (the predicate `P` of the statement, unpacked). -/
structure SP (Φ : T I → ℝ) : Prop where
  h0 : ∀ X, 0 ≤ Φ X
  h1 : Φ unitT = 1
  hz : ∀ X : T I, (∀ z, X.2 z = 0) → Φ X = 0
  hmono : ∀ X Y : T I, (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
    ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X
  hmul : ∀ X Y : T I, Φ (sigMul X Y) = Φ X * Φ Y
  hadd : ∀ X Y : T I, Φ (sigAdd X Y) = Φ X + Φ Y

theorem nonempty_of_SP {Φ : T I → ℝ} (h : SP Φ) : Nonempty I := by
  by_contra hI
  rw [not_nonempty_iff] at hI
  have key : ∀ X Y : T I, (∀ y z, Y.2 y = X.2 z) → Φ Y ≤ Φ X := fun X Y hyz =>
    h.hmono X Y ⟨fun i => isEmptyElim i, fun y => by
      rw [Fintype.sum_unique]
      simp only [Fintype.prod_empty, one_mul]
      exact hyz y default⟩
  have hs : ∀ z, (sigAdd (unitT : T I) unitT).2 z = 1 := by
    intro z
    simp [sigAdd, unitT]
  have e1 := key (sigAdd unitT unitT) unitT (fun y z => by rw [hs z]; rfl)
  have e2 := key unitT (sigAdd unitT unitT) (fun y z => by rw [hs y]; rfl)
  have e3 := h.hadd unitT unitT
  rw [h.h1] at e1 e2 e3
  linarith

theorem phi_toSig_sigRaw {Φ : T I → ℝ} (h : SP Φ) (X : T I) : Φ (toSig (sigRaw X)) = Φ X :=
  raw_eq Φ h.hmono (X := sigRaw X) (S := X) (fun _ => Equiv.refl _) (fun _ => rfl)

/-- The spectral point on tensor classes of a coordinate spectral point. -/
noncomputable def fwd [Nonempty I] {Φ : T I → ℝ} (h : SP Φ) :
    normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop) :=
  ⟨phiClass Φ h.h0 h.hmono, phiClass_mem Φ h.h0 h.h1 h.hz h.hmono h.hmul h.hadd⟩

theorem psi_fwd [Nonempty I] {Φ : T I → ℝ} (h : SP Φ) : psi (fwd h) = Φ := by
  funext X
  exact phi_toSig_sigRaw h X

theorem SP_psi [Nonempty I] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) :
    SP (psi φ) :=
  ⟨psi_nonneg φ, psi_one φ, psi_zero φ, psi_mono φ, psi_mul φ, psi_add φ⟩

theorem psi_toSig [Nonempty I] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop))
    (R : Raw.{0} I ℂ) : psi φ (toSig R) = (φ.val (ofRaw R) : ℝ) :=
  psi_eq_of_equiv φ (fun i => Fintype.equivFin _)
    (fun x => congrArg _ (funext fun i => ((Fintype.equivFin _).symm_apply_apply (x i)).symm))

theorem SP_wire_self {Φ : T I → ℝ} (h : SP Φ) (s : I) : Φ (wireT s s) = 1 := by
  apply le_antisymm
  · rw [← h.h1]
    apply h.hmono unitT (wireT s s)
    refine ⟨fun _ _ _ => 1, fun y => ?_⟩
    haveI : ∀ i, Unique (Fin ((unitT : T I).1 i)) := fun _ => (inferInstance : Unique (Fin 1))
    rw [Fintype.sum_unique]
    simp [wireT, unitT]
  · rw [← h.h1]
    apply h.hmono (wireT s s) unitT
    have hpos : ∀ i, 0 < (wireT s s).1 i := fun i => by
      simp only [wireT]; split_ifs <;> norm_num
    let z0 : ∀ i, Fin ((wireT s s).1 i) := fun i => ⟨0, hpos i⟩
    refine ⟨fun i _ b => if (b : ℕ) = 0 then 1 else 0, fun y => ?_⟩
    rw [Fintype.sum_eq_single z0]
    · simp [z0, wireT, unitT]
    · intro z hz
      obtain ⟨i, hi⟩ : ∃ i, z i ≠ z0 i := by
        by_contra hc
        push_neg at hc
        exact hz (funext hc)
      have hi' : ((z i : ℕ) = 0) = False := by
        apply propext
        constructor
        · intro e; exact hi (Fin.ext e)
        · intro e; exact e.elim
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])]
      simp

theorem wire_eq_mask {Φ : T I → ℝ} (h : SP Φ) (s t : I) :
    Φ (wireT s t) = Φ (maskSig {s, t}) := by
  have hd : ∀ i, (wireT s t).1 i = (maskSig ({s, t} : Finset I)).1 i := fun i => by
    simp [wireT, maskSig]
  rw [← phi_toSig_sigRaw h (wireT s t)]
  apply raw_eq Φ h.hmono (X := sigRaw (wireT s t)) (S := maskSig {s, t})
    (fun i => finCongr (hd i))
  intro x
  change (if ((x s : ℕ) = x t) then (1 : ℂ) else 0) =
    if ∀ i ∈ ({s, t} : Finset I), ∀ j ∈ ({s, t} : Finset I),
      ((finCongr (hd i) (x i) : ℕ) = finCongr (hd j) (x j)) then 1 else 0
  simp only [finCongr_apply, Fin.coe_cast]
  congr 1
  apply propext
  constructor
  · intro e i hi j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · rfl
    · exact e
    · exact e.symm
    · rfl
  · intro e
    exact e s (by simp) t (by simp)

/-- The wire distance of the statement is OpenAI's `rawWireDistance` of the class point. -/
theorem logb_psi_wire [Nonempty I]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I ℂ → _ → Prop)) (s t : I) :
    Real.logb 2 (psi φ (wireT s t)) = rawWireDistance φ 1 s t := by
  by_cases hst : s = t
  · subst hst
    rw [rawWireDistance_self φ 1 zero_le_one, SP_wire_self (SP_psi φ), Real.logb_one]
  · have hinj : Function.Injective (![s, t] : Fin 2 → I) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    have hS : ∀ i, i ∈ ({s, t} : Finset I) ↔ ∃ j, (⟨![s, t], hinj⟩ : Fin 2 ↪ I) j = i := by
      intro i
      simp only [Finset.mem_insert, Finset.mem_singleton, Function.Embedding.coeFn_mk]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨j, rfl⟩
        fin_cases j <;> simp
    have hm := Raw.ofRaw_group_diagonal_eq_mask (K := ℂ) ⟨![s, t], hinj⟩ {s, t} hS (Fin 2)
    simp only [Function.Embedding.coeFn_mk] at hm
    rw [rawWireDistance, rawLogPrice, one_mul, hm, wire_eq_mask (SP_psi φ),
      ← psi_toSig φ, mask_le (psi φ) (psi_mono φ) {s, t} ⟨s, by simp⟩]

theorem logb_wire_fwd [Nonempty I] {Φ : T I → ℝ} (h : SP Φ) (s t : I) :
    Real.logb 2 (Φ (wireT s t)) = rawWireDistance (fwd h) 1 s t := by
  rw [← logb_psi_wire (fwd h) s t, psi_fwd h]

end glue

end OMAPort


namespace OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

/-- Binary log-price of the mask diagonal on `S`. -/
noncomputable def maskLog {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V ℂ → _ → Prop)) (S : Finset V) : ℝ :=
  Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ)

/-- Grouping a mask diagonal by an embedding gives the mask diagonal of the image. -/
theorem ofRaw_group_mask {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty J] (e : I ↪ J) (S : Finset I) (hS : S.Nonempty) :
    ofRaw ((Raw.maskDiagonal ℂ S (Fin 2)).group e) = ofRaw (Raw.maskDiagonal ℂ (S.map e) (Fin 2)) := by
  classical
  haveI : Nonempty I := ⟨hS.choose⟩
  let ι : S ↪ I := Function.Embedding.subtype _
  have h1 : ofRaw ((Raw.diagonal S ℂ (Fin 2)).group ι) = ofRaw (Raw.maskDiagonal ℂ S (Fin 2)) :=
    Raw.ofRaw_group_diagonal_eq_mask ι S
      (fun i => ⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩) (Fin 2)
  have h2 : ofRaw ((Raw.diagonal S ℂ (Fin 2)).group (ι.trans e)) =
      ofRaw (Raw.maskDiagonal ℂ (S.map e) (Fin 2)) :=
    Raw.ofRaw_group_diagonal_eq_mask (ι.trans e) (S.map e)
      (fun j => by
        simp only [Finset.mem_map, Function.Embedding.trans_apply]
        constructor
        · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨⟨a, ha⟩, rfl⟩; exact ⟨a, ha, rfl⟩) (Fin 2)
  have h3 : ofRaw (((Raw.diagonal S ℂ (Fin 2)).group ι).group e) =
      ofRaw ((Raw.diagonal S ℂ (Fin 2)).group (ι.trans e)) :=
    ofRaw_eq_iff.mpr (Raw.group_group_equivalent _ _ _)
  rw [← h2, ← h3, ← groupClass_ofRaw, ← h1, groupClass_ofRaw]

theorem maskLog_nonneg {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V ℂ → _ → Prop)) (S : Finset V)
    (hS : S.Nonempty) : 0 ≤ maskLog φ S :=
  Real.logb_nonneg one_lt_two (by
    exact_mod_cast one_le_raw_spectralValue φ _ (Raw.maskDiagonal_ne_zero S hS (Fin 2)))

/-- Diminishing increments of the mask log-prices of any spectral point (OpenAI's argument for
`SpectralPlacementPrices.intersectingSubmodular`, with the placement replaced by a restriction). -/
theorem maskLog_diminishing {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V ℂ → _ → Prop)) :
    DiminishingIncrements (maskLog φ) := by
  classical
  intro I A z hI hIA hz
  let k := I.card - 1
  let m := (A \ I).card
  obtain ⟨e, hj, ho, ha, hu⟩ := exists_incrementSite_embedding hI hIA hz
  have hcard := Finset.card_pos.mpr hI
  have hk : k + 1 = I.card := by dsimp [k]; omega
  have hjne : (incrementJointMask k m).Nonempty := ⟨.inl 0, by simp [incrementJointMask]⟩
  have hone : (incrementOldMask k m).Nonempty := ⟨.inl 0, by simp [incrementOldMask]⟩
  have hane : (incrementAuxMask k m).Nonempty := Finset.insert_nonempty _ _
  have hune : (Finset.univ : Finset (IncrementSite k m)).Nonempty := Finset.univ_nonempty
  haveI : Nontrivial (IncrementSite (I.card - 1) (A \ I).card) :=
    ⟨⟨Sum.inl 0, Sum.inr none, Sum.inl_ne_inr⟩⟩
  obtain ⟨ψ, hψ⟩ := rawLogPrice_group_embedding φ e 1
  let c := rawLogPrice φ 1 ((Raw.diagonal (IncrementSite k m) ℂ (Fin 2)).group e)
  have hc : 0 ≤ c := rawLogPrice_nonneg φ zero_le_one _
  have hd : ∀ S : Finset (IncrementSite k m), S.Nonempty →
      maskLog φ (S.map e) = c * Real.logb 2 (ψ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ) := by
    intro S hS
    have h1 := hψ (Raw.maskDiagonal ℂ S (Fin 2))
    rw [rawLogPrice, one_mul, ofRaw_group_mask e S hS] at h1
    exact h1
  apply priceIncrement_of_finite_diagonal hcard (maskLog_nonneg φ _ (Finset.insert_nonempty _ _))
  intro q hq
  let L := 2 * (k+1) * (q-1) + 1
  have hqpos : 0 < q := by omega
  have hL : 0 < L := Nat.zero_lt_succ _
  let D (S : Finset (IncrementSite k m)) (n : ℕ) :=
    (ψ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin n))) : ℝ)
  have hD (S : Finset (IncrementSite k m)) (hs : S.Nonempty) (n : ℕ) (hn : 0 < n) :
      0 < D S n := by
    let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    have h := ψ.property.2.2.2.2 _ _
      (show (1 : TensorClass.{0} (IncrementSite k m) ℂ) ≤ ofRaw (Raw.maskDiagonal ℂ S (Fin n)) from
        Raw.one_restricts_of_nonzero _ (Raw.maskDiagonal_ne_zero S hs (Fin n)))
    rw [ψ.property.2.1] at h
    exact_mod_cast zero_lt_one.trans_le h
  have comp := commonLabel_value_le ℂ q k m ψ
  unfold coeffValue at comp
  rw [ofCoeffs_incrementTargetBasis, ofCoeffs_incrementSourceBasis,
    ψ.property.2.2.2.1, ψ.property.2.2.2.1] at comp
  have hr : D Finset.univ q * D (incrementJointMask k m) q ≤
      D (incrementOldMask k m) q * D (incrementAuxMask k m) L := by exact_mod_cast comp
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos (hD _ hune q hqpos) (hD _ hjne q hqpos)) hr
  rw [Real.logb_mul (hD _ hune _ hqpos).ne' (hD _ hjne _ hqpos).ne',
    Real.logb_mul (hD _ hone _ hqpos).ne' (hD _ hane _ hL).ne'] at hlog
  have hp (S : Finset (IncrementSite k m)) (hs : S.Nonempty) (n : ℕ) (hn : 0 < n) :
      c * Real.logb 2 (D S n) = maskLog φ (S.map e) * Real.logb 2 n := by
    dsimp only [D]
    rw [maskDiagonal_log_price ψ S hs hn, hd S hs, mul_assoc]
  have res := mul_le_mul_of_nonneg_left hlog hc
  rw [mul_add, mul_add, hp _ hune _ hqpos, hp _ hjne _ hqpos, hp _ hone _ hqpos,
    hp _ hane _ hL, hu, hj, ho, ha, ← add_mul] at res
  simpa only [L, hk] using res

theorem maskLog_submodular {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V ℂ → _ → Prop)) :
    IntersectingSubmodular (maskLog φ) :=
  intersectingSubmodular_iff_diminishingIncrements.mpr (maskLog_diminishing φ)

theorem psi_maskSig {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V ℂ → _ → Prop)) (S : Finset V)
    (hS : S.Nonempty) : Real.logb 2 (psi φ (maskSig S)) = maskLog φ S := by
  rw [← mask_le (psi φ) (psi_mono φ) S hS, psi_toSig]
  rfl

end OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H2_R1.H3 := by
  intro δ hmono hpair hpts
  classical
  constructor
  · intro A B hAB
    let U := A ∪ B
    have hAU : A ⊆ U := Finset.subset_union_left
    have hBU : B ⊆ U := Finset.subset_union_right
    by_cases hU : U.card ≤ 1
    · have hsub : ∀ p ∈ U, ∀ q ∈ U, p = q := fun p hp q hq => Finset.card_le_one.mp hU p hp q hq
      obtain ⟨y0, hy0⟩ := hAB
      have hy0A := (Finset.mem_inter.mp hy0).1
      have hy0B := (Finset.mem_inter.mp hy0).2
      have eqU : ∀ X : Finset (EuclideanSpace ℝ (Fin 2)), X ⊆ U → y0 ∈ X → X = U := by
        intro X hX hyX
        apply Finset.Subset.antisymm hX
        intro p hp
        rw [hsub p hp y0 (hAU hy0A)]
        exact hyX
      rw [eqU A hAU hy0A, eqU B hBU hy0B, Finset.union_self, Finset.inter_self]
    push_neg at hU
    let I := {p // p ∈ U}
    haveI : Nontrivial I := by
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hU
      exact ⟨⟨⟨p, hp⟩, ⟨q, hq⟩, fun h => hpq (congrArg Subtype.val h)⟩⟩
    let x : I ↪ EuclideanSpace ℝ (Fin 2) := Function.Embedding.subtype _
    obtain ⟨Ψ, hP, hΨ⟩ := hpts I x
    obtain ⟨h0, h1, hz, hm, hmul, hadd⟩ := hP
    have hS : OMAPort.SP Ψ := ⟨h0, h1, hz, hm, hmul, hadd⟩
    haveI : Nonempty I := OMAPort.nonempty_of_SP hS
    let φ := OMAPort.fwd hS
    have hpsi : OMAPort.psi φ = Ψ := OMAPort.psi_fwd hS
    have hUx : Finset.univ.image x = U := by
      ext p
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact i.2
      · intro hp; exact ⟨⟨p, hp⟩, rfl⟩
    have hpos : 0 < δ U := by
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hU
      have h2 : ({p, q} : Finset _) ⊆ U := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      have := hmono h2
      rw [hpair] at this
      exact lt_of_lt_of_le (dist_pos.mpr hpq) this
    have key : ∀ S : Finset I, S.Nonempty → δ (S.image x) = δ U * OMAPort.maskLog φ S := by
      intro S hSn
      have h := hΨ S hSn
      rw [hUx] at h
      change Real.logb 2 (Ψ (OMAPort.maskSig S)) = _ at h
      rw [← hpsi, OMAPort.psi_maskSig φ S hSn] at h
      rw [h]
      field_simp
    let A' : Finset I := Finset.univ.filter (fun i => i.1 ∈ A)
    let B' : Finset I := Finset.univ.filter (fun i => i.1 ∈ B)
    have hA' : A'.image x = A := by
      ext p
      simp only [A', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hp; exact ⟨⟨p, hAU hp⟩, hp, rfl⟩
    have hB' : B'.image x = B := by
      ext p
      simp only [B', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hp; exact ⟨⟨p, hBU hp⟩, hp, rfl⟩
    have hinj : Function.Injective x := x.injective
    have hU' : (A' ∪ B').image x = A ∪ B := by rw [Finset.image_union, hA', hB']
    have hI' : (A' ∩ B').image x = A ∩ B := by rw [Finset.image_inter_of_injOn _ _ hinj.injOn, hA', hB']
    have hABne : (A' ∩ B').Nonempty := by
      obtain ⟨y, hy⟩ := hAB
      rw [← hI'] at hy
      obtain ⟨i, hi, -⟩ := Finset.mem_image.mp hy
      exact ⟨i, hi⟩
    have hA'ne : A'.Nonempty := hABne.mono Finset.inter_subset_left
    have hB'ne : B'.Nonempty := hABne.mono Finset.inter_subset_right
    have hsub := OMAPort.maskLog_submodular φ hABne
    rw [← hU', ← hI', ← hA', ← hB', key _ (hA'ne.mono Finset.subset_union_left), key _ hABne,
      key _ hA'ne, key _ hB'ne, ← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left hsub hpos.le
  · intro p q r
    by_cases hpq : p = q
    · subst hpq
      rw [show ({p, p, r} : Finset (EuclideanSpace ℝ (Fin 2))) = {p, r} by
        ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hpair, dist_self,
        dist_comm r p]
      linarith
    by_cases hqr : q = r
    · subst hqr
      rw [show ({p, q, q} : Finset (EuclideanSpace ℝ (Fin 2))) = {p, q} by
        ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hpair, dist_self,
        dist_comm q p]
      linarith
    by_cases hrp : r = p
    · subst hrp
      rw [show ({r, q, r} : Finset (EuclideanSpace ℝ (Fin 2))) = {r, q} by
        ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, hpair, dist_self,
        dist_comm q r]
      linarith
    let f : Fin 3 → EuclideanSpace ℝ (Fin 2) := ![p, q, r]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij <;>
        first | rfl | exact absurd hij hpq | exact absurd hij.symm hpq | exact absurd hij hqr |
          exact absurd hij.symm hqr | exact absurd hij hrp | exact absurd hij.symm hrp
    let x : Fin 3 ↪ EuclideanSpace ℝ (Fin 2) := ⟨f, hf⟩
    obtain ⟨Ψ, hP, hΨ⟩ := hpts (Fin 3) x
    obtain ⟨h0, h1, hz, hm, hmul, hadd⟩ := hP
    have hS : OMAPort.SP Ψ := ⟨h0, h1, hz, hm, hmul, hadd⟩
    let φ := OMAPort.fwd hS
    have hpsi : OMAPort.psi φ = Ψ := OMAPort.psi_fwd hS
    have hU : Finset.univ.image x = {p, q, r} := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [x, f]
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    have hpos : 0 < δ {p, q, r} := by
      have h2 : ({p, q} : Finset _) ⊆ {p, q, r} := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
        tauto
      have := hmono h2
      rw [hpair] at this
      exact lt_of_lt_of_le (dist_pos.mpr hpq) this
    have edge : ∀ i j : Fin 3, OMAPort.maskLog φ {i, j} = dist (x i) (x j) / δ {p, q, r} := by
      intro i j
      have h := hΨ {i, j} (Finset.insert_nonempty _ _)
      rw [hU] at h
      change Real.logb 2 (Ψ (OMAPort.maskSig {i, j})) = _ at h
      rw [← hpsi, OMAPort.psi_maskSig φ _ (Finset.insert_nonempty _ _)] at h
      rw [h, Finset.image_insert, Finset.image_singleton, hpair]
    have h2 := two_le_sum_wire_logs ℂ φ
    simp only at h2
    change 2 ≤ OMAPort.maskLog φ {0, 1} + OMAPort.maskLog φ {1, 2} + OMAPort.maskLog φ {2, 0} at h2
    rw [edge, edge, edge] at h2
    have hx0 : x 0 = p := rfl
    have hx1 : x 1 = q := rfl
    have hx2 : x 2 = r := rfl
    rw [hx0, hx1, hx2, ← add_div, ← add_div, le_div_iff₀ hpos] at h2
    linarith

