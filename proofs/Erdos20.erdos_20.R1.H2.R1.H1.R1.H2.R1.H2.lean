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
theorem ite_eq_right {c : Prop} {h : Decidable c} {α : Sort*} {t e : α} (hnc : ¬ c) :
    ite c t e = e := if_neg hnc
theorem ite_eq_left {c : Prop} {h : Decidable c} {α : Sort*} {t e : α} (hc : c) :
    ite c t e = t := if_pos hc
theorem dite_eq_right {c : Prop} {h : Decidable c} {α : Sort*} {t : c → α} {e : ¬ c → α} (hnc : ¬ c) :
    dite c t e = e hnc := dif_neg hnc
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter
open scoped Topology NNReal
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
instance [Nonempty I] [NoZeroDivisors K] : NoZeroDivisors (TensorClass.{v} I K) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} := by
    induction a using Quotient.inductionOn with | h X =>
    induction b using Quotient.inductionOn with | h Y =>
    change ofRaw (X.mul Y) = 0 → ofRaw X = 0 ∨ ofRaw Y = 0
    simp only [ofRaw_eq_zero_iff]
    intro h
    by_cases hX : X.coeff = 0
    · exact Or.inl hX
    · apply Or.inr
      obtain ⟨x, hx⟩ : ∃ x, X.coeff x ≠ 0 := by
        by_contra! h0
        exact hX (funext h0)
      funext y
      exact (mul_eq_zero.mp (congrFun h (fun i => (x i, y i)))).resolve_left hx
end Semiring
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
theorem rawLogPrice_mul (c : ℝ) (X Y : Raw.{v} I K)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) :
    rawLogPrice φ c (X.mul Y) = rawLogPrice φ c X + rawLogPrice φ c Y := by
  have pos (T : Raw.{v} I K) (h : T.coeff ≠ 0) : (φ.val (ofRaw T) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_raw_spectralValue φ T h)).ne'
  simp only [rawLogPrice, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul,
    Real.logb_mul (pos X hX) (pos Y hY), mul_add]
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
theorem group_ne_zero_iff [Zero K] (T : SiteTensor.Raw I K) (σ : I → J) :
    (T.group σ).coeff ≠ 0 ↔ T.coeff ≠ 0 := by
  constructor
  · intro h hzero
    exact h (funext fun x => congrFun hzero _)
  · intro h hzero
    apply h
    exact funext fun x => congrFun hzero (fun _ i => x i.1)
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
end Raw
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
section Logarithms
variable {A B : Type} {F : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} B F → _ → Prop))
theorem rawLogPrice_group_diagonal (σ : A → B) (c : ℝ) {α : Type} [Fintype α] [Nonempty α] :
    rawLogPrice φ c ((Raw.diagonal A F α).group σ) =
      rawLogPrice φ c ((Raw.diagonal A F (Fin 2)).group σ) * Real.logb 2 (Fintype.card α) := by
  let v : TensorClass.{0} A F →* ℝ≥0 := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom σ)
  have hv : ∀ {m n : ℕ}, 0 < m → m ≤ n → v m ≤ v n := by
    intro m n _ h
    apply φ.property.2.2.2.2
    apply groupClass_mono σ
    rw [← ofRaw_diagonal_fin_eq_natCast A F m, ← ofRaw_diagonal_fin_eq_natCast A F n]
    exact Raw.diagonal_restricts_of_embedding A F (Fin.castLEEmb h)
  have h := spectral_natCast_logb v hv (Fintype.card α) Fintype.card_pos
  have eval (β : Type) [Fintype β] : φ.val (ofRaw ((Raw.diagonal A F β).group σ)) =
      v (Fintype.card β : TensorClass.{0} A F) := by
    rw [← ofRaw_diagonal_eq_natCast A F β]
    rfl
  rw [rawLogPrice, rawLogPrice, eval α, eval (Fin 2), Fintype.card_fin, Nat.cast_ofNat, h, mul_assoc]
end Logarithms
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators
section
variable {I J : Type*} [Fintype I]
theorem price_transport_le_sum (p : (I → J) → ℝ) (d : J → J → ℝ) (c : I → ℝ)
    (step : ∀ (a b : I → J) (i : I), (∀ j, j ≠ i → a j = b j) →
      p b ≤ p a + d (a i) (b i) * c i)
    (x y : I → J) : p y ≤ p x + ∑ i, d (x i) (y i) * c i := by
  classical
  let move (s : Finset I) (i : I) := if i ∈ s then y i else x i
  have bound (s : Finset I) :
      p (move s) ≤ p x + ∑ i ∈ s, d (x i) (y i) * c i := by
    induction s using Finset.induction_on with
    | empty => simp [move]
    | @insert i s hi ih =>
      have hs := step (move s) (move (insert i s)) i fun j hj => by simp [move, hj]
      simp only [move, hi, ↓reduceIte, Finset.mem_insert_self] at hs
      rw [Finset.sum_insert hi, ← add_assoc, add_right_comm]
      exact hs.trans (add_le_add_left ih _)
  simpa [move] using bound Finset.univ
theorem abs_price_sub_le_transport (p : (I → J) → ℝ) (d : J → J → ℝ) (c : I → ℝ)
    (symm : ∀ a b, d a b = d b a)
    (step : ∀ (a b : I → J) (i : I), (∀ j, j ≠ i → a j = b j) →
      p b ≤ p a + d (a i) (b i) * c i)
    (x y : I → J) : |p x - p y| ≤ ∑ i, d (x i) (y i) * c i := by
  obtain hxy := price_transport_le_sum p d c step x y
  obtain hyx := price_transport_le_sum p d c step y x
  simp_rw [fun i => symm (y i) (x i)] at hyx
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
open scoped Classical
universe u
theorem grouped_diagonal_reindex {A B : Type u} {J : Type*} [Fintype A] [Fintype B] [Fintype J]
    (K D : Type*) [CommSemiring K] [Fintype D] (e : A ≃ B) (σ : B → J) :
    ((diagonal B K D).group σ).Equivalent ((diagonal A K D).group (σ ∘ e)) := by
  let fiber (j : J) : {i : A // σ (e i) = j} ≃ {i : B // σ i = j} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  apply reindex_equivalent (fun j => Equiv.arrowCongr (fiber j).symm (Equiv.refl D))
  intro x
  apply Finset.sum_congr rfl
  intro d _
  change (if (fun i => x (σ i) ⟨i, rfl⟩) = (fun _ => d) then (1 : K) else 0) =
    (if (fun i => x (σ (e i)) ⟨e i, rfl⟩) = (fun _ => d) then 1 else 0)
  let labels (i : B) : D := x (σ i) ⟨i, rfl⟩
  have heq : (labels = fun _ => d) ↔ ((labels ∘ e) = fun _ => d) := by
    constructor
    · intro h
      exact funext fun i => congrFun h (e i)
    · intro h
      exact funext fun i => by simpa [Function.comp] using congrFun h (e.symm i)
  exact if_congr heq rfl rfl
theorem grouped_wire_symm {J : Type*} [Fintype J] (K D : Type*) [CommSemiring K]
    [Fintype D] (s t : J) :
    ((diagonal (Fin 2) K D).group ![s, t]).Equivalent
      ((diagonal (Fin 2) K D).group ![t, s]) := by
  have h : ![s, t] ∘ Fin.revPerm = ![t, s] := by
    funext i
    fin_cases i <;> rfl
  rw [← h]
  exact grouped_diagonal_reindex K D (Fin.revPerm (n := 2)) ![s, t]
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
open scoped Classical BigOperators
variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]
private theorem diagonal_pair_coeff {D : Type*} [Fintype D] (z : Fin 2 → D) :
    (diagonal (Fin 2) K D).coeff z = if z 0 = z 1 then 1 else 0 := by
  classical
  have he (a : D) : (z = fun _ => a) ↔ z 0 = a ∧ z 1 = a := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · intro h
      funext i
      fin_cases i <;> simp [h]
  unfold diagonal
  dsimp only
  rw [Finset.sum_eq_single (z 0)]
  · simp only [he, true_and, eq_comm]
  · intro a _ ha
    exact ite_eq_right (fun h => ha ((he a).mp h).1.symm)
  · simp
theorem move_restricts_with_wire (T : Raw I K) (p q : I → J) (i₀ : I)
    (hagree : ∀ i, i ≠ i₀ → p i = q i) :
    (T.group q).Restricts ((T.group p).mul ((diagonal (Fin 2) K (T.Leg i₀)).group
      ![p i₀, q i₀])) := by
  classical
  let loc : Fin 2 → J := ![p i₀, q i₀]
  let W := (diagonal (Fin 2) K (T.Leg i₀)).group loc
  let S := (T.group p).mul W
  let ok (j : J) (x : (T.group q).Leg j) (y : S.Leg j) : Prop :=
    (∀ (i : I), i ≠ i₀ → ∀ (h : p i = j) (h' : q i = j),
      y.1 ⟨i, h⟩ = x ⟨i, h'⟩) ∧
    (∀ h : p i₀ = j, y.1 ⟨i₀, h⟩ = y.2 ⟨0, h⟩) ∧
    (∀ h : q i₀ = j, y.2 ⟨1, h⟩ = x ⟨i₀, h⟩)
  refine ⟨fun j x y => if ok j x y then 1 else 0, ?_⟩
  intro x
  let v (i : I) := x (q i) ⟨i, rfl⟩
  let keep (j : J) : S.Leg j := (fun i => v i.val, fun _ => v i₀)
  have hok (j : J) : ok j (x j) (keep j) := by
    refine ⟨?_, fun _ => rfl, ?_⟩
    · rintro i _ h rfl
      rfl
    · rintro rfl
      rfl
  have hcoeff (y : ∀ j, S.Leg j) : S.coeff y =
      T.coeff (fun i => (y (p i)).1 ⟨i, rfl⟩) *
        (if (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩ then 1 else 0) :=
    congrArg (_ * ·) (diagonal_pair_coeff (fun k => (y (loc k)).2 ⟨k, rfl⟩))
  change T.coeff v = ∑ y : ∀ j, S.Leg j, S.coeff y * ∏ j, if ok j (x j) (y j) then 1 else 0
  have hp (y : ∀ j, S.Leg j) : (∏ j, if ok j (x j) (y j) then (1 : K) else 0) =
      if ∀ j, ok j (x j) (y j) then 1 else 0 := Fintype.prod_boole
  simp_rw [hp]
  rw [Finset.sum_eq_single keep]
  · rw [hcoeff keep]
    have hw : (keep (p i₀)).2 ⟨0, rfl⟩ = (keep (q i₀)).2 ⟨1, rfl⟩ := rfl
    rw [ite_eq_left hw, ite_eq_left hok, mul_one, mul_one]
  · intro y _ hy
    by_cases hc : ∀ j, ok j (x j) (y j)
    · by_cases hw : (y (p i₀)).2 ⟨0, rfl⟩ = (y (q i₀)).2 ⟨1, rfl⟩
      · exfalso
        apply hy
        have hright : (y (q i₀)).2 ⟨1,rfl⟩ = v i₀ := (hc _).2.2 rfl
        have hleft := hw.trans hright
        funext j
        apply Prod.ext
        · funext ⟨i, hi⟩
          subst j
          by_cases h : i = i₀
          · subst i
            exact ((hc _).2.1 rfl).trans hleft
          · have transport (j : J) (hj : q i = j) : x j ⟨i, hj⟩ = v i := by
              subst j
              rfl
            exact ((hc _).1 i h rfl (hagree i h).symm).trans (transport _ _)
        · funext ⟨k, hk⟩
          subst j
          fin_cases k
          · exact hleft
          · exact hright
      · simp [hcoeff, hw]
    · simp [hc]
  · simp
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
variable {I J : Type} {K : Type*} [Fintype I] [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
def rawWireDistance (s t : J) : ℝ :=
  rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group ![s, t])
theorem rawWireDistance_symm (s t : J) : rawWireDistance φ c s t = rawWireDistance φ c t s := by
  unfold rawWireDistance rawLogPrice
  rw [ofRaw_eq_iff.mpr (Raw.grouped_wire_symm K (Fin 2) s t)]
private theorem diagonal_pair_ne_zero (D : Type) [Fintype D] [Nonempty D] :
    (Raw.diagonal (Fin 2) K D).coeff ≠ 0 := by
  classical
  let d := Classical.arbitrary D
  intro hzero
  have h := congrFun hzero (fun _ => d)
  have he (a : D) : (fun _ : Fin 2 => d) = (fun _ => a) ↔ d = a :=
    ⟨fun h => congrFun h 0, by rintro rfl; rfl⟩
  change (Raw.diagonal (Fin 2) K D).coeff (fun _ => d) = (0 : K) at h
  simp [Raw.diagonal, he] at h
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
theorem rawLogPrice_move_le (hc : 0 ≤ c) (T : Raw.{0} I K) (hT : T.coeff ≠ 0)
    (a b : I → J) (i : I) (hagree : ∀ j, j ≠ i → a j = b j) :
    rawLogPrice φ c (T.group b) ≤ rawLogPrice φ c (T.group a) +
      rawWireDistance φ c (a i) (b i) * Real.logb 2 (Fintype.card (T.Leg i)) := by
  classical
  obtain ⟨x, _⟩ : ∃ x, T.coeff x ≠ 0 := by
    by_contra! h
    exact hT (funext h)
  let : Nonempty (T.Leg i) := ⟨x i⟩
  let f := ![a i, b i]
  have hd := ((Raw.diagonal (Fin 2) K (T.Leg i)).group_ne_zero_iff f).mpr
    (diagonal_pair_ne_zero (K := K) (T.Leg i))
  have h := rawLogPrice_mono φ hc (Raw.move_restricts_with_wire T a b i hagree)
  rw [rawLogPrice_mul φ c _ _ ((T.group_ne_zero_iff a).mpr hT) hd,
    rawLogPrice_group_diagonal] at h
  exact h
theorem rawLogPrice_transport (hc : 0 ≤ c) (T : Raw.{0} I K) (x y : I → J) :
    |rawLogPrice φ c (T.group x) - rawLogPrice φ c (T.group y)| ≤
      ∑ i, rawWireDistance φ c (x i) (y i) * Real.logb 2 (Fintype.card (T.Leg i)) := by
  by_cases hT : T.coeff = 0
  · have h (a : I → J) : (T.group a).coeff = 0 := funext fun y => congrFun hT _
    rw [rawLogPrice_zero φ c _ (h x), rawLogPrice_zero φ c _ (h y), sub_self, abs_zero]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (rawLogPrice_nonneg φ hc _)
    rcases (Fintype.card (T.Leg i)).eq_zero_or_pos with hi | hi
    · simp [hi]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hi)
  · exact abs_price_sub_le_transport _ _ _ (rawWireDistance_symm φ c)
      (rawLogPrice_move_le φ c hc T hT) x y
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
open scoped Classical
variable {H I J : Type} {K : Type*} [Fintype H] [Fintype I] [Fintype J]
omit [Fintype J] in
private theorem grouped_diagonal_coeff [CommSemiring K] (σ : I → J) (D : Type) [Fintype D] :
    ((Raw.diagonal I K D).group σ).coeff =
      pushCoeff (fun d (j : J) (_ : {i // σ i = j}) ↦ d) (fun _ : D ↦ (1 : K)) := by
  funext x
  apply Finset.sum_congr rfl
  intro d _
  change (if (fun i ↦ x (σ i) ⟨i, rfl⟩) = (fun _ ↦ d) then 1 else 0) =
    (if (fun _ _ ↦ d) = x then 1 else 0)
  congr 1
  apply propext
  constructor
  · intro hx
    funext j p
    obtain ⟨i, rfl⟩ := p
    exact (congrFun hx i).symm
  · intro hx
    funext i
    exact (congrFun (congrFun hx (σ i)) ⟨i, rfl⟩).symm
theorem Raw.group_diagonal_restricts_of_comp [CommSemiring K] (σ : I → J) (f : H → I)
    (D : Type) [Fintype D] :
    ((diagonal H K D).group (σ ∘ f)).Restricts ((diagonal I K D).group σ) := by
  let crop (j : J) (a : {i // σ i = j} → D) (p : {h // (σ ∘ f) h = j}) : D :=
    a ⟨f p.val, p.property⟩
  have h := pushCoeff_restricts crop ((diagonal I K D).group σ).coeff
  change Crossing.IsRestriction _ _
  have he : ((diagonal H K D).group (σ ∘ f)).coeff =
      pushCoeff (fun x j ↦ crop j (x j)) ((diagonal I K D).group σ).coeff := by
    rw [grouped_diagonal_coeff, grouped_diagonal_coeff]
    erw [pushCoeff_comp]
    rfl
  rw [he]
  exact h
end SiteTensor
end
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
end Raw
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped BigOperators NNReal
private theorem exists_logb_summand {L : Type*} [Fintype L] {v : ℝ≥0} (f : L → ℝ≥0)
    (hv : 0 < v) (hs : v ≤ ∑ j, f j) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, 0 < f j ∧ c * Real.logb 2 v ≤ c * Real.logb 2 (f j) + c * Real.logb 2 (Fintype.card L) := by
  classical
  cases isEmpty_or_nonempty L with
  | inl h => simp at hs; exact False.elim (hv.ne' hs)
  | inr h =>
    obtain ⟨j, hj⟩ := Finite.exists_max f
    have hsum : v ≤ (Fintype.card L : ℝ≥0) * f j := calc
      _ ≤ ∑ l, f l := hs
      _ ≤ ∑ _l : L, f j := Finset.sum_le_sum fun l _ => hj l
      _ = _ := by simp
    have hp : 0 < (f j : ℝ) := by exact_mod_cast pos_of_mul_pos_right (hv.trans_le hsum) (by positivity)
    have hn : 0 < (Fintype.card L : ℝ) := by exact_mod_cast (Fintype.card_pos (α := L))
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hv : 0 < (v : ℝ)) (show (v : ℝ) ≤ (Fintype.card L : ℝ) * f j by exact_mod_cast hsum)
    rw [Real.logb_mul hn.ne' hp.ne'] at hlog
    exact ⟨j, by exact_mod_cast hp, by linarith [mul_le_mul_of_nonneg_left hlog hc]⟩
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
theorem coeffValue_one_le {T : (∀ i, A i) → K} (h : T ≠ 0) : 1 ≤ coeffValue φ T := by
  have hle : (1 : TensorClass.{v} I K) ≤ ofCoeffs T :=
    ofRaw_le_iff.mpr (Crossing.unit_restricts_of_nonzero h)
  simpa [coeffValue, φ.2.2.1] using φ.2.2.2.2.2 _ _ hle
theorem ordinary_sum_value_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    coeffValue φ (∑ j, T j) ≤ ∑ j, coeffValue φ (T j) := by
  have h := φ.2.2.2.2.2 _ _ (ordinary_sum_le T)
  change coeffValue φ (∑ j, T j) ≤ normalizedSpectrum.toRingHom φ (∑ j, ofCoeffs (T j)) at h
  rw [map_sum] at h
  exact h
theorem ordinary_sum_logb_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K)
    (hT : ∑ j, T j ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, T j ≠ 0 ∧ c * Real.logb 2 (coeffValue φ (∑ k, T k)) ≤
      c * Real.logb 2 (coeffValue φ (T j)) + c * Real.logb 2 (Fintype.card J) := by
  obtain ⟨j, hj, h⟩ := exists_logb_summand _ (zero_lt_one.trans_le (coeffValue_one_le φ hT))
    (ordinary_sum_value_le φ T) hc
  exact ⟨j, fun h0 => by simp [h0] at hj, h⟩
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
variable {K ι : Type*} [Field K]
def coordinatePower (n : ℕ) (x : ι → K) (w : Fin n → ι) : K := ∏ j, x (w j)
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
noncomputable section
section
namespace SiteTensor
variable {I J : Type} [Fintype I] [Fintype J] {K : Type*} [Field K]
def Raw.powerTensor (T : Raw.{0} I K) (n : ℕ) : Raw.{0} I K :=
  ⟨fun i ↦ Fin n → T.Leg i, fun _ ↦ inferInstance, groupedPower n T.coeff⟩
omit [Fintype I] in
theorem Raw.powerTensor_ne_zero (T : Raw.{0} I K) (hT : T.coeff ≠ 0) (n : ℕ) :
    (T.powerTensor n).coeff ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, T.coeff x ≠ 0 := Function.ne_iff.mp hT
  intro h
  have hz := congrFun h (fun i _ ↦ x i)
  change (∏ _ : Fin n, T.coeff x) = 0 at hz
  exact (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hx) hz
variable [Nonempty I] [Nonempty J]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
theorem rawLogPrice_group_powerTensor (T : Raw.{0} I K) (σ : I → J) (n : ℕ) :
    rawLogPrice φ c ((T.powerTensor n).group σ) = n * rawLogPrice φ c (T.group σ) := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom (K := K) σ)
  have he (S : Raw.{0} I K) : φ.val (ofRaw (S.group σ)) = v (ofRaw S) := rfl
  simp only [rawLogPrice, he, Raw.powerTensor, ofRaw_groupedPower, map_pow, NNReal.coe_pow,
    Real.logb_pow, inferInstance, instRawFiniteLeg_eq, instRawFiniteLeg_eqf, Raw_eta_inst]
  ring
theorem rawLogPrice_add_select (hc : 0 ≤ c) {A : J → Type} [∀ j, Fintype (A j)]
    (U V : (∀ j, A j) → K) (hne : U + V ≠ 0) :
    (U ≠ 0 ∧ rawLogPrice φ c ⟨A, inferInstance, U + V⟩ ≤
      rawLogPrice φ c ⟨A, inferInstance, U⟩ + c) ∨
    (V ≠ 0 ∧ rawLogPrice φ c ⟨A, inferInstance, U + V⟩ ≤
      rawLogPrice φ c ⟨A, inferInstance, V⟩ + c) := by
  classical
  let T : Fin 2 → (∀ j, A j) → K := ![U,V]
  have hsum : ∑ i, T i = U + V := by simp [T, Fin.sum_univ_two]
  obtain ⟨i, hi, hp⟩ := ordinary_sum_logb_le φ T (hsum ▸ hne) hc
  rw [hsum] at hp
  fin_cases i
  · left
    exact ⟨hi, by simpa [rawLogPrice, coeffValue, ofCoeffs, T,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hp⟩
  · right
    exact ⟨hi, by simpa [rawLogPrice, coeffValue, ofCoeffs, T,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hp⟩
end SiteTensor
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
variable {I : Type*} [Fintype I]
abbrev MaskLeg (S : Finset I) (α : Type) (i : I) := i ∈ S → α
noncomputable def Raw.maskDiagonal (K : Type*) [Field K] (S : Finset I) (α : Type) [Fintype α] :
    Raw.{0} I K :=
  ⟨MaskLeg S α, fun _ ↦ Fintype.ofFinite _, Crossing.basisTensor (fun (a : α) i (_ : i ∈ S) ↦ a)⟩
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
variable [Nonempty I]
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
noncomputable section
open Set
open scoped Classical
section
def SiteTensor.RawDiagonalJointConvexity (K : Type*) [Field K] : Prop :=
  ∀ {J : Type} [Fintype J] [Nonempty J]
    (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} J K → _ → Prop))
    (c : ℝ), 0 < c → ∀ (r : ℕ) [NeZero r] (a z b : Fin r → J) (t : ℝ),
    t ∈ Icc (0 : ℝ) 1 →
    (∀ i, SiteTensor.rawWireDistance φ c (z i) (a i) = t * SiteTensor.rawWireDistance φ c (a i) (b i)) →
    (∀ i, SiteTensor.rawWireDistance φ c (z i) (b i) = (1-t) * SiteTensor.rawWireDistance φ c (a i) (b i)) →
    SiteTensor.rawLogPrice φ c ((SiteTensor.Raw.diagonal (Fin r) K (Fin 2)).group z) ≤
      (1-t) * SiteTensor.rawLogPrice φ c ((SiteTensor.Raw.diagonal (Fin r) K (Fin 2)).group a) +
      t * SiteTensor.rawLogPrice φ c ((SiteTensor.Raw.diagonal (Fin r) K (Fin 2)).group b)
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
abbrev CubeTable (r : ℕ) := (Fin r → Bool) → ℝ
namespace CubeTable
open Finset Function Set
noncomputable section
variable {r : ℕ}
def gap (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) : ℝ :=
  N (update x i false) - N (update x i true)
def lower (N : CubeTable r) (i : Fin r) : ℝ :=
  univ.inf' univ_nonempty (gap N i)
def upper (N : CubeTable r) (i : Fin r) : ℝ :=
  univ.sup' univ_nonempty (gap N i)
def width (N : CubeTable r) (i : Fin r) : ℝ := upper N i - lower N i
def midpoint (N : CubeTable r) (i : Fin r) : ℝ := (upper N i + lower N i) / 2
theorem gap_mem (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) :
    gap N i x ∈ Icc (lower N i) (upper N i) :=
  ⟨univ.inf'_le _ (mem_univ x), univ.le_sup' _ (mem_univ x)⟩
theorem lower_le_upper (N : CubeTable r) (i : Fin r) : lower N i ≤ upper N i :=
  let h := gap_mem N i (fun _ ↦ false)
  h.1.trans h.2
theorem lower_ge_of_forall (N : CubeTable r) (i : Fin r) {l : ℝ}
    (h : ∀ x, l ≤ gap N i x) : l ≤ lower N i :=
  Finset.le_inf' _ _ (fun x _ ↦ h x)
theorem upper_le_of_forall (N : CubeTable r) (i : Fin r) {u : ℝ}
    (h : ∀ x, gap N i x ≤ u) : upper N i ≤ u :=
  Finset.sup'_le _ _ (fun x _ ↦ h x)
theorem midpoint_mem (N : CubeTable r) (i : Fin r) : midpoint N i ∈ Icc (lower N i) (upper N i) := by
  unfold midpoint
  constructor <;> linarith [lower_le_upper N i]
theorem abs_gap_sub_gap_le_width (N : CubeTable r) (i : Fin r) (x y : Fin r → Bool) :
    |gap N i x - gap N i y| ≤ width N i := by
  have hx := gap_mem N i x
  have hy := gap_mem N i y
  rw [width, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
def child (N : CubeTable r) (i : Fin r) (b : Bool) : CubeTable r := fun x ↦
  if x i = b then min (N x) (N (update x i (!b)) + (if b then -midpoint N i else midpoint N i))
  else N x
abbrev plus (N : CubeTable r) (i : Fin r) := child N i false
abbrev minus (N : CubeTable r) (i : Fin r) := child N i true
theorem child_le (N : CubeTable r) (i : Fin r) (b : Bool) : child N i b ≤ N := by
  intro x
  unfold child
  split_ifs <;> first | exact min_le_left _ _ | rfl
theorem gap_plus (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) :
    gap (plus N i) i x = min (gap N i x) (midpoint N i) := by
  simp [gap, plus, child, ← min_sub_sub_right]
theorem gap_minus (N : CubeTable r) (i : Fin r) (x : Fin r → Bool) :
    gap (minus N i) i x = max (gap N i x) (midpoint N i) := by
  simp [gap, minus, child, ← max_sub_sub_left]
private theorem gap_child_other_mem (N : CubeTable r) (i j : Fin r) (b : Bool)
    (hji : j ≠ i) (x : Fin r → Bool) :
    gap (child N i b) j x ∈ Icc (lower N j) (upper N j) := by
  have h := gap_mem N j x
  have h' := gap_mem N j (update x i (!b))
  simp only [gap, Set.mem_Icc] at h h'
  simp only [gap, child, update_of_ne hji.symm, update_comm hji]
  split_ifs <;> grind
theorem gap_child_mem (N : CubeTable r) (i j : Fin r) (b : Bool) (x : Fin r → Bool) :
    gap (child N i b) j x ∈ Icc (lower N j) (upper N j) := by
  by_cases hji : j = i
  · subst j
    have h := gap_mem N i x
    have hc := midpoint_mem N i
    cases b
    · rw [show child N i false = plus N i from rfl, gap_plus]
      exact ⟨le_min h.1 hc.1, (min_le_left _ _).trans h.2⟩
    · rw [show child N i true = minus N i from rfl, gap_minus]
      exact ⟨h.1.trans (le_max_left _ _), max_le h.2 hc.2⟩
  · exact gap_child_other_mem N i j b hji x
theorem lower_le_child (N : CubeTable r) (i j : Fin r) (b : Bool) :
    lower N j ≤ lower (child N i b) j :=
  lower_ge_of_forall _ _ (fun x ↦ (gap_child_mem N i j b x).1)
theorem upper_child_le (N : CubeTable r) (i j : Fin r) (b : Bool) :
    upper (child N i b) j ≤ upper N j :=
  upper_le_of_forall _ _ (fun x ↦ (gap_child_mem N i j b x).2)
theorem width_child_le (N : CubeTable r) (i j : Fin r) (b : Bool) :
    width (child N i b) j ≤ width N j :=
  sub_le_sub (upper_child_le N i j b) (lower_le_child N i j b)
theorem width_child (N : CubeTable r) (i : Fin r) (b : Bool) :
    width (child N i b) i ≤ width N i / 2 := by
  cases b
  · have h := upper_le_of_forall (plus N i) i (u := midpoint N i)
      (fun x ↦ by rw [gap_plus]; exact min_le_right _ _)
    dsimp [plus] at h
    unfold width
    linarith [lower_le_child N i i false, show 2 * midpoint N i = upper N i + lower N i by unfold midpoint; ring]
  · have h := lower_ge_of_forall (minus N i) i (l := midpoint N i)
      (fun x ↦ by rw [gap_minus]; exact le_max_right _ _)
    dsimp [minus] at h
    unfold width
    linarith [upper_child_le N i i true, show 2 * midpoint N i = upper N i + lower N i by unfold midpoint; ring]
end
end CubeTable
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace CubeTable
open Finset Function
noncomputable section
variable {r : ℕ}
structure IsCoupling (w : CubeTable r) (t : Fin r → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ w x
  total : ∑ x, w x = 1
  marginal : ∀ i, (∑ x, if x i then w x else 0) = t i
def cost (w N : CubeTable r) : ℝ := ∑ x, w x * N x
def independent (t : Fin r → ℝ) : CubeTable r :=
  fun x ↦ ∏ i, if x i then t i else 1 - t i
theorem independent_isCoupling {t : Fin r → ℝ} (ht : ∀ i, t i ∈ Set.Icc 0 1) :
    IsCoupling (independent t) t := by
  let p (i : Fin r) (b : Bool) := if b then t i else 1 - t i
  have htotal (i : Fin r) : ∑ b : Bool, p i b = 1 := by simp [p]
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ ↦ by
      change 0 ≤ if x i then t i else 1 - t i
      split <;> first | exact (ht i).1 | exact sub_nonneg.mpr (ht i).2)
  · change (∑ x : Fin r → Bool, ∏ i, p i (x i)) = 1
    rw [← Fintype.prod_sum]
    simp only [htotal, Finset.prod_const_one]
  · intro i
    let q (j : Fin r) (b : Bool) := if j = i ∧ b = false then 0 else p j b
    have hq (x : Fin r → Bool) : (if x i then independent t x else 0) = ∏ j, q j (x j) := by
      cases hi : x i with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [q, hi])).symm
      | true =>
        simp only [↓reduceIte]
        apply Finset.prod_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp [q, p, hi]
        · simp [q, p, hj]
    simp only [hq, ← Fintype.prod_sum]
    have hj (j : Fin r) : (∑ b : Bool, q j b) = if j = i then t j else 1 := by
      by_cases h : j = i <;> simp [q, p, h]
    simp only [hj, Fintype.prod_ite_eq']
theorem cost_mono {w : CubeTable r} {t : Fin r → ℝ} (hw : IsCoupling w t)
    {N M : CubeTable r} (h : N ≤ M) : cost w N ≤ cost w M :=
  Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (hw.nonneg x)
def additiveApprox (N : CubeTable r) : CubeTable r := fun x ↦
  N (fun _ ↦ false) + ∑ i, if x i then -gap N i (fun _ ↦ false) else 0
theorem abs_sub_additiveApprox (N : CubeTable r) {ε : ℝ} (hε : 0 ≤ ε)
    (hwid : ∀ i, width N i ≤ ε) (x : Fin r → Bool) : |N x - additiveApprox N x| ≤ r * ε := by
  let o : Fin r → Bool := fun _ ↦ false
  let d (i : Fin r) := if x i then -gap N i o else 0
  have h (s : Finset (Fin r)) :
      |N (s.piecewise x o) - (N o + ∑ i ∈ s, d i)| ≤ s.card * ε := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      let y := s.piecewise x o
      have hy : update y i false = y := update_eq_self_iff.mpr (by simp [y, hi, o])
      have hstep : |N (update y i (x i)) - N y - d i| ≤ ε := by
        cases hx : x i with
        | false => simpa [d, hx, hy] using hε
        | true =>
          have hb := (abs_gap_sub_gap_le_width N i o y).trans (hwid i)
          simp only [gap, hy] at hb
          simp only [d, hx, ↓reduceIte, sub_neg_eq_add, gap]
          convert hb using 2
          all_goals first | rfl | ring1

      rw [piecewise_insert, sum_insert hi, card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      calc
        _ = |(N (update y i (x i)) - N y - d i) + (N y - (N o + ∑ j ∈ s, d j))| := by
          congr 1
          change N (update y i (x i)) - _ = _
          ring
        _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hstep ih).trans_eq (by ring))
  simpa [additiveApprox, o, d] using h univ
private theorem cost_additiveApprox {w : CubeTable r} {t : Fin r → ℝ}
    (hw : IsCoupling w t) (N : CubeTable r) :
    cost w (additiveApprox N) = N (fun _ ↦ false) + ∑ i, t i * (-gap N i (fun _ ↦ false)) := by
  simp only [cost, additiveApprox, mul_add, mul_sum, sum_add_distrib, ← sum_mul, hw.total, one_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hw.marginal i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x i <;> simp [hx]
private theorem abs_cost_sub_of_uniform {w N M : CubeTable r} {t : Fin r → ℝ}
    (hw : IsCoupling w t) {d : ℝ} (h : ∀ x, |N x - M x| ≤ d) :
    |cost w N - cost w M| ≤ d := by
  simp only [cost, ← Finset.sum_sub_distrib, ← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ x, w x * d := Finset.sum_le_sum fun x _ ↦ by
      rw [abs_mul, abs_of_nonneg (hw.nonneg x)]
      exact mul_le_mul_of_nonneg_left (h x) (hw.nonneg x)
    _ = d := by rw [← sum_mul, hw.total, one_mul]
theorem cost_le_cost_of_width {w π : CubeTable r} {t : Fin r → ℝ}
    (hw : IsCoupling w t) (hπ : IsCoupling π t) (N : CubeTable r)
    {ε : ℝ} (hε : 0 ≤ ε) (hwid : ∀ i, width N i ≤ ε) :
    cost w N ≤ cost π N + 2 * (r : ℝ) * ε := by
  have hA := abs_sub_additiveApprox N hε hwid
  have hwA := (abs_le.mp (abs_cost_sub_of_uniform hw hA)).2
  have hπA := (abs_le.mp (abs_cost_sub_of_uniform hπ hA)).1
  rw [cost_additiveApprox hw] at hwA
  rw [cost_additiveApprox hπ] at hπA
  linarith
end
end CubeTable
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Finset Function
theorem independent_relocation {I X : Type*} [DecidableEq I] (H : (I → X) → ℝ)
    (a b z : I → X) (t : I → ℝ) (s : Finset I) (p : I → X)
    (ht : ∀ i ∈ s, t i ∈ Set.Icc 0 1)
    (hmove : ∀ i ∈ s, ∀ q : I → X, H (update q i (z i)) ≤
      (1 - t i) * H (update q i (a i)) + t i * H (update q i (b i))) :
    H (s.piecewise z p) ≤ ∑ U ∈ s.powerset,
      (∏ i ∈ s, if i ∈ U then t i else 1 - t i) *
        H (s.piecewise (U.piecewise b a) p) := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert i s hi ih =>
    have ht' := fun j (hj : j ∈ s) ↦ ht j (mem_insert_of_mem hj)
    have hmove' := fun j (hj : j ∈ s) ↦ hmove j (mem_insert_of_mem hj)
    rw [piecewise_insert, sum_powerset_insert hi]
    refine (hmove i (mem_insert_self ..) _).trans ?_
    simp only [update_piecewise_of_notMem _ _ _ hi]
    apply (add_le_add
      (mul_le_mul_of_nonneg_left (ih (update p i (a i)) ht' hmove')
        (sub_nonneg.mpr (ht i (mem_insert_self ..)).2))
      (mul_le_mul_of_nonneg_left (ih (update p i (b i)) ht' hmove')
        (ht i (mem_insert_self ..)).1)).trans_eq
    simp only [mul_sum]
    congr 1
    · apply sum_congr rfl
      intro U hU
      have hiU := notMem_mono (mem_powerset.mp hU) hi
      rw [prod_insert hi, ite_eq_right hiU, piecewise_insert,
        U.piecewise_eq_of_notMem b a hiU, update_piecewise_of_notMem _ _ _ hi, mul_assoc]
    · apply sum_congr rfl
      intro U _
      have hprod : (∏ j ∈ s, if j ∈ insert i U then t j else 1 - t j) =
          ∏ j ∈ s, if j ∈ U then t j else 1 - t j := by
        apply prod_congr rfl
        intro j hj
        simp [ne_of_mem_of_not_mem hj hi]
      have hcorner : s.piecewise ((insert i U).piecewise b a) p =
          s.piecewise (U.piecewise b a) p := by
        apply s.piecewise_congr _ (fun _ _ ↦ rfl)
        intro j hj
        exact piecewise_insert_of_ne _ _ _ (ne_of_mem_of_not_mem hj hi)
      rw [prod_insert hi, ite_eq_left (mem_insert_self ..), hprod, piecewise_insert,
        piecewise_insert_self, hcorner, update_piecewise_of_notMem _ _ _ hi, mul_assoc]
theorem independent_relocation_cube {I X : Type*} [Fintype I] [DecidableEq I]
    (H : (I → X) → ℝ) (a b z : I → X) (t : I → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hmove : ∀ i, ∀ q : I → X, H (update q i (z i)) ≤
      (1 - t i) * H (update q i (a i)) + t i * H (update q i (b i))) :
    H z ≤ ∑ e : I → Bool, (∏ i, if e i then t i else 1 - t i) *
      H (fun i ↦ if e i then b i else a i) := by
  classical
  have h := independent_relocation H a b z t univ z (fun i _ ↦ ht i) (fun i _ ↦ hmove i)
  simp only [piecewise_univ, powerset_univ] at h
  let e : Finset I ≃ (I → Bool) :=
    { toFun := fun U i ↦ decide (i ∈ U)
      invFun := fun v ↦ univ.filter fun i ↦ v i
      left_inv := fun U ↦ by ext i; simp
      right_inv := fun v ↦ by ext i; simp }
  exact h.trans_eq (Fintype.sum_equiv e _ _ (fun U ↦ by simp [e]; exact Or.inl rfl))
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical BigOperators
namespace SiteTensor.Relocation
variable {I J Q H M : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [∀ i, Fintype (A i)]
variable [Fintype Q] [Fintype H] [Fintype M] [CommSemiring K]
def marked (A : I → Type) [∀ i, Fintype (A i)] (Q : Type) [Fintype Q]
    (T : (∀ i, A i) → Q → K) : Raw (I ⊕ Unit) K where
  Leg := Sum.elim A (fun _ => Q)
  finiteLeg := fun k => by
    rcases k with i | _
    · exact inferInstanceAs (Fintype (A i))
    · exact inferInstanceAs (Fintype Q)
  coeff x := T (fun i => x (.inl i)) (x (.inr ()))
def split (A : I → Type) [∀ i, Fintype (A i)] (Q H : Type) [Fintype Q] [Fintype H]
    (S : (∀ i, A i) → Q → H → H → K) : Raw (I ⊕ Fin 3) K where
  Leg := Sum.elim A ![Q,H,H]
  finiteLeg := fun k => by
    rcases k with i | t
    · exact inferInstanceAs (Fintype (A i))
    · change Fintype (![Q,H,H] t)
      exact Fin.cases (motive := fun k => Fintype (![Q,H,H] k)) (inferInstanceAs (Fintype Q))
        (fun t => Fin.cases (motive := fun k => Fintype (![H,H] k)) (inferInstanceAs (Fintype H))
          (fun t => Fin.cases (motive := fun k => Fintype (![H] k)) (inferInstanceAs (Fintype H))
            (fun t => t.elim0) t) t) t
  coeff x := S (fun i => x (.inl i)) (x (.inr 0)) (x (.inr 1)) (x (.inr 2))
def placeMark (σ : I → J) (p : J) : I ⊕ Unit → J := Sum.elim σ (fun _ => p)
def placeSplit (σ : I → J) (c a b : J) : I ⊕ Fin 3 → J := Sum.elim σ ![c,a,b]
def plusCoeff (T : (∀ i, A i) → Q → K) (L : Q → M → H → K) (D : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) : K :=
  ∑ j, ∑ m, T x j * L i m α * D j β m
def minusCoeff (T : (∀ i, A i) → Q → K) (D : Q → M → H → K) (L : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) : K :=
  ∑ j, ∑ m, T x j * D j m α * L i β m
def wire (K : Type*) (M : Type) [CommSemiring K] [Fintype M] (p q : J) : Raw J K :=
  (Raw.diagonal (Fin 2) K M).group ![p,q]
private def markTupleEquiv (A : I → Type) (Q : Type) :
    ((∀ i, A i) × Q) ≃ (∀ k : I ⊕ Unit, Sum.elim A (fun _ => Q) k) where
  toFun w k := match k with
    | .inl i => w.1 i
    | .inr _ => w.2
  invFun x := (fun i => x (.inl i), x (.inr ()))
  left_inv _ := rfl
  right_inv x := by funext k; rcases k with i | ⟨⟩ <;> rfl
theorem restricts_contraction (T : (∀ i, A i) → Q → K) (σ : I → J)
    (p q : J) (S : Raw J K) (readBg : ∀ i, S.Leg (σ i) → A i)
    (P : S.Leg p → M → K) (R : S.Leg q → Q → M → K)
    (hs : ∀ x, S.coeff x = ∑ j, ∑ m, T (fun i => readBg i (x (σ i))) j *
        P (x p) m * R (x q) j m) :
    S.Restricts (((marked A Q T).group (placeMark σ q)).mul (wire K M p q)) := by
  classical
  let U := (marked A Q T).group (placeMark σ q)
  let W := wire K M p q
  let V := U.mul W
  let E : (((∀ i, A i) × Q) × (Fin 2 → M)) ≃ (∀ k, V.Leg k) :=
    ((markTupleEquiv A Q).trans (groupIndexEquiv (placeMark σ q) (marked A Q T).Leg)).prodCongr
      (groupIndexEquiv ![p,q] (fun _ => M)) |>.trans
      (Equiv.arrowProdEquivProdArrow J U.Leg W.Leg).symm
  let ok (k : J) (x : S.Leg k) (y : V.Leg k) :=
    ∀ (i : I) (h : σ i = k), y.1 ⟨.inl i, h⟩ = readBg i (h ▸ x)
  let F (k : J) (x : S.Leg k) (y : V.Leg k) : K :=
    (if ok k x y then 1 else 0) *
      (if hp : p = k then P (hp ▸ x) (y.2 ⟨0,hp⟩) else 1) *
      (if hq : q = k then R (hq ▸ x) (y.1 ⟨.inr (),hq⟩) (y.2 ⟨1,hq⟩) else 1)
  refine ⟨F, fun x => ?_⟩
  rw [← E.sum_comp]
  let b (i : I) := readBg i (x (σ i))
  have term (s : ((∀ i, A i) × Q) × (Fin 2 → M)) :
      V.coeff (E s) * ∏ k, F k (x k) (E s k) =
        ∑ m : M, if s.1.1 = b ∧ s.2 = fun _ => m then
          T b s.1.2 * P (x p) m * R (x q) s.1.2 m else 0 := by
    have hok : (∀ k, ok k (x k) (E s k)) ↔ s.1.1 = b := by
      constructor
      · intro h
        exact funext fun i => h (σ i) i rfl
      · intro h k i hi
        subst k
        exact congrFun h i
    have hp : (∏ k, if hp : p = k then
        P (hp ▸ x k) ((E s k).2 ⟨0,hp⟩) else 1) = P (x p) (s.2 0) := by
      rw [Finset.prod_eq_single p]
      · simp only; rfl
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    have hq : (∏ k, if hq : q = k then
        R (hq ▸ x k) ((E s k).1 ⟨.inr (),hq⟩) ((E s k).2 ⟨1,hq⟩) else 1) =
        R (x q) s.1.2 (s.2 1) := by
      rw [Finset.prod_eq_single q]
      · simp only; rfl
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    have hcoeff : V.coeff (E s) = T s.1.1 s.1.2 * (∑ m : M, if s.2 = fun _ => m then 1 else 0) := by
      change _ * _ = _ * _
      congr 1
      apply Finset.sum_congr rfl
      intro m _
      congr 1
    rw [hcoeff]
    change (T s.1.1 s.1.2 * (∑ m : M, if s.2 = fun _ => m then 1 else 0)) * _ = _
    have hbprod : (∏ k, if ok k (x k) (E s k) then (1 : K) else 0) =
        if s.1.1 = b then 1 else 0 := Fintype.prod_boole.trans (if_congr hok rfl rfl)
    simp only [F, Finset.prod_mul_distrib, hbprod, hp, hq]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hb : s.1.1 = b <;> by_cases hm : s.2 = fun _ => m <;>
      simp [hb, hm, mul_assoc]
  change S.coeff x = ∑ s, V.coeff (E s) * ∏ k, F k (x k) (E s k)
  simp_rw [term]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [hs]
  symm
  rw [Finset.sum_eq_single b]
  · simp [Finset.sum_comm (f := fun (z : Fin 2 → M) (m : M) => _), b]
  · intro a _ ha; simp [ha]
  · simp
theorem plus_restricts_opposite (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (c b : J) :
    ((split A Q H (plusCoeff T L D)).group (placeSplit σ c c b)).Restricts
      (((marked A Q T).group (placeMark σ b)).mul (wire K M c b)) :=
  restricts_contraction T σ c b _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => L (x ⟨.inr 0,rfl⟩) m (x ⟨.inr 1,rfl⟩))
    (fun x j m => D j (x ⟨.inr 2,rfl⟩) m) (fun _ => rfl)
theorem minus_restricts_opposite (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (c a : J) :
    ((split A Q H (minusCoeff T D L)).group (placeSplit σ c a c)).Restricts
      (((marked A Q T).group (placeMark σ a)).mul (wire K M c a)) := by
  refine restricts_contraction T σ c a _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => L (x ⟨.inr 0,rfl⟩) (x ⟨.inr 2,rfl⟩) m)
    (fun x j m => D j m (x ⟨.inr 1,rfl⟩)) ?_
  intro x
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro m _
  exact mul_right_comm _ _ _
theorem plus_restricts (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (c a b : J) :
    ((split A Q H (plusCoeff T L D)).group (placeSplit σ c a b)).Restricts
      ((((marked A Q T).group (placeMark σ b)).mul (wire K M c b)).mul (wire K H c a)) := by
  let S := split A Q H (plusCoeff T L D)
  have h := Raw.move_restricts_with_wire S (placeSplit σ c c b) (placeSplit σ c a b)
    (.inr 1) (by
      intro t ht
      rcases t with i | t
      · rfl
      · fin_cases t <;> first | rfl | exact (ht rfl).elim)
  exact restrict_trans h (Raw.mul_restricts (plus_restricts_opposite T L D σ c b) (restrict_refl _))
theorem minus_restricts (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (c a b : J) :
    ((split A Q H (minusCoeff T D L)).group (placeSplit σ c a b)).Restricts
      ((((marked A Q T).group (placeMark σ a)).mul (wire K M c a)).mul (wire K H c b)) := by
  let S := split A Q H (minusCoeff T D L)
  have h := Raw.move_restricts_with_wire S (placeSplit σ c a c) (placeSplit σ c a b)
    (.inr 2) (by
      intro t ht
      rcases t with i | t
      · rfl
      · fin_cases t <;> first | rfl | exact (ht rfl).elim)
  exact restrict_trans h (Raw.mul_restricts (minus_restricts_opposite T D L σ c a) (restrict_refl _))
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
variable {I J Q : Type} {A : I → Type} [Fintype I] [Fintype J] [Fintype Q]
variable [∀ i, Fintype (A i)] {K : Type*} [Field K]
def powerCoeff (n : ℕ) (T : (∀ i, A i) → Q → K) (x : ∀ i, Fin n → A i) (q : Fin n → Q) : K :=
  ∏ k, T (fun i => x i k) (q k)
def powerMarkEquiv (Q : Type) [Fintype Q] (n : ℕ) : Fin ((Fintype.card Q)^n) ≃ (Fin n → Q) :=
  (Fintype.equivFinOfCardEq (by simp)).symm
def finPowerCoeff (n : ℕ) (T : (∀ i, A i) → Q → K) (x : ∀ i, Fin n → A i)
    (q : Fin ((Fintype.card Q)^n)) : K :=
  powerCoeff n T x (powerMarkEquiv Q n q)
variable (n : ℕ) (T : (∀ i, A i) → Q → K)
theorem marked_power_equivalent {D : Type} [Fintype D] (e : D ≃ (Fin n → Q)) :
    (marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).Equivalent
      ((marked A Q T).powerTensor n) := by
  let f (i : I ⊕ Unit) :
      (marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).Leg i ≃
        ((marked A Q T).powerTensor n).Leg i := by
    rcases i with i | ⟨⟩
    · exact Equiv.refl _
    · exact e
  apply Raw.reindex_equivalent f
  intro x
  rfl
variable [Nonempty J] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
private theorem price_power_basis {D : Type} [Fintype D] (e : D ≃ (Fin n → Q)) (σ : I ⊕ Unit → J) :
    rawLogPrice φ c ((marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).group σ) =
      n * rawLogPrice φ c ((marked A Q T).group σ) := by
  have h := congrArg (groupClass (K := K) σ) (ofRaw_eq_iff.mpr (marked_power_equivalent n T e))
  change ofRaw _ = ofRaw _ at h
  rw [← rawLogPrice_group_powerTensor φ c (marked A Q T) σ n]
  exact congrArg (fun S => c * Real.logb 2 (φ.val S : ℝ)) h
theorem rawLogPrice_marked_finPower (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (n : ℕ) (T : (∀ i, A i) → Q → K) (σ : I ⊕ Unit → J) :
    rawLogPrice φ c ((marked (fun i => Fin n → A i) (Fin ((Fintype.card Q)^n))
      (finPowerCoeff n T)).group σ) = n * rawLogPrice φ c ((marked A Q T).group σ) :=
  price_power_basis n T φ c (powerMarkEquiv Q n) σ
theorem marked_finPower_ne_zero (hT : (marked A Q T).coeff ≠ 0) :
    (marked (fun i => Fin n → A i) (Fin ((Fintype.card Q)^n)) (finPowerCoeff n T)).coeff ≠ 0 := by
  have h := ofRaw_eq_iff.mpr (marked_power_equivalent n T (powerMarkEquiv Q n))
  intro hz
  have he := (ofRaw_eq_zero_iff _).mpr hz
  exact (Raw.powerTensor_ne_zero _ hT n) ((ofRaw_eq_zero_iff _).mp (h.symm.trans he))
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
variable {I J : Type} {K : Type*} [Fintype I] [Fintype J]
def markCoeff (T : Raw.{0} I K) (i : I)
    (x : ∀ j : {j // j ≠ i}, T.Leg j.1) (q : T.Leg i) : K :=
  T.coeff (fun j => if h : j = i then h.symm ▸ q else x ⟨j,h⟩)
theorem marked_group_equivalent [DecidableEq I] [CommSemiring K] (T : Raw.{0} I K) (i : I) :
    ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).group
      (placeMark Subtype.val i)).Equivalent T := by
  classical
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let p := placeMark (Subtype.val : {j // j ≠ i} → I) i
  let e (j : I) : (U.group p).Leg j ≃ T.Leg j := {
    toFun := fun z => if h : j = i then h.symm ▸ z ⟨.inr (), h.symm⟩
      else z ⟨.inl ⟨j,h⟩, rfl⟩
    invFun := fun x t => match t with
      | ⟨.inl ⟨k,_⟩,h⟩ => cast (congrArg T.Leg (show j = k from h.symm)) x
      | ⟨.inr (),h⟩ => cast (congrArg T.Leg (show j = i from h.symm)) x
    left_inv := by
      intro z
      funext t
      rcases t with ⟨⟨k,hk⟩ | ⟨⟩,h⟩
      · change k = j at h
        subst j
        simp [hk]
        rfl
      · change i = j at h
        subst j
        simp
        rfl
    right_inv := by
      intro x
      by_cases h : j = i
      · subst j
        simp
        rfl
      · simp [h]
        rfl }
  apply Raw.reindex_equivalent (X := U.group p) (Y := T) e
  intro x
  apply congrArg T.coeff
  funext j
  by_cases h : j = i
  · subst j
    simp [e]
    rfl
  · simp [e,h]
    rfl
theorem ofRaw_update_eq_mark [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I)
    (σ : I → J) (p : J) :
    ofRaw (T.group (Function.update σ i p)) =
      ofRaw ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).group
        (placeMark (σ ∘ Subtype.val) p)) := by
  classical
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let q := placeMark (Subtype.val : {j // j ≠ i} → I) i
  have hp : (Function.update σ i p) ∘ q = placeMark (σ ∘ Subtype.val) p := by
    funext j
    rcases j with ⟨j,h⟩ | ⟨⟩
    · exact Function.update_of_ne h _ _
    · exact Function.update_self ..
  let f := groupClass (K := K) (Function.update σ i p)
  have h : f (ofRaw (U.group q)) = f (ofRaw T) := congrArg f
    (ofRaw_eq_iff.mpr (marked_group_equivalent T i))
  calc
    _ = f (ofRaw (U.group q)) := h.symm
    _ = ofRaw (U.group ((Function.update σ i p) ∘ q)) :=
      ofRaw_eq_iff.mpr (Raw.group_group_equivalent U q (Function.update σ i p))
    _ = _ := congrArg (fun s => ofRaw (U.group s)) hp
theorem rawLogPrice_update_eq_mark [DecidableEq I] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (T : Raw.{0} I K) (i : I) (σ : I → J) (p : J) :
    rawLogPrice φ c (T.group (Function.update σ i p)) =
      rawLogPrice φ c ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i)
        (markCoeff T i)).group (placeMark (σ ∘ Subtype.val) p)) := by
  simp only [rawLogPrice, ofRaw_update_eq_mark T i σ p]
theorem marked_reindex {A : I → Type} [∀ j, Fintype (A j)] {Q D : Type}
    [Fintype Q] [Fintype D] [CommSemiring K] (T : (∀ j, A j) → Q → K) (e : Q ≃ D) :
    (marked A Q T).Equivalent (marked A D (fun x d => T x (e.symm d))) := by
  let f (k : I ⊕ Unit) : (marked A Q T).Leg k ≃ (marked A D (fun x d => T x (e.symm d))).Leg k := by
    rcases k with k | ⟨⟩
    · exact Equiv.refl _
    · exact e
  apply Raw.reindex_equivalent f
  intro x
  exact congrArg (T (fun j => x (.inl j))) (e.symm_apply_apply _).symm
theorem ofRaw_group_eq_markFin [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I)
    {n : ℕ} (e : T.Leg i ≃ Fin n) (σ : I → J) :
    ofRaw (T.group σ) =
      ofRaw ((marked (fun j : {j // j ≠ i} => T.Leg j.1) (Fin n)
        (fun x q => markCoeff T i x (e.symm q))).group (placeMark (σ ∘ Subtype.val) (σ i))) := by
  have h := ofRaw_update_eq_mark T i σ (σ i)
  rw [Function.update_eq_self] at h
  exact h.trans (congrArg (groupClass (K := K) (placeMark (σ ∘ Subtype.val) (σ i)))
    (ofRaw_eq_iff.mpr (marked_reindex (markCoeff T i) e)))
theorem marked_ne_zero [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I) (hT : T.coeff ≠ 0) :
    (marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)).coeff ≠ 0 := by
  let : Nonempty I := ⟨i⟩
  let U := marked (fun j : {j // j ≠ i} => T.Leg j.1) (T.Leg i) (markCoeff T i)
  let q := placeMark (Subtype.val : {j // j ≠ i} → I) i
  apply (U.group_ne_zero_iff q).mp
  intro hz
  exact hT ((ofRaw_eq_zero_iff T).mp ((ofRaw_eq_iff.mpr (marked_group_equivalent T i)).symm.trans
    ((ofRaw_eq_zero_iff _).mpr hz)))
theorem marked_fin_ne_zero [DecidableEq I] [Field K] (T : Raw.{0} I K) (i : I) {n : ℕ}
    (e : T.Leg i ≃ Fin n) (hT : T.coeff ≠ 0) :
    (marked (fun j : {j // j ≠ i} => T.Leg j.1) (Fin n)
      (fun x q => markCoeff T i x (e.symm q))).coeff ≠ 0 := by
  intro hz
  exact marked_ne_zero T i hT ((ofRaw_eq_zero_iff _).mp
    ((ofRaw_eq_iff.mpr (marked_reindex (markCoeff T i) e)).trans ((ofRaw_eq_zero_iff _).mpr hz)))
theorem exists_finPower_update [DecidableEq I] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (T : Raw.{0} I K) (hT : T.coeff ≠ 0) (i : I) (x : I → J) (n : ℕ) :
    ∃ S : (∀ j : {j // j ≠ i}, Fin n → T.Leg j.1) → Fin ((Fintype.card (T.Leg i))^n) → K,
      (marked _ _ S).coeff ≠ 0 ∧ ∀ p : J,
        rawLogPrice φ c ((marked _ _ S).group (placeMark (x ∘ Subtype.val) p)) =
          n * rawLogPrice φ c (T.group (Function.update x i p)) := by
  refine ⟨finPowerCoeff n (markCoeff T i), marked_finPower_ne_zero n _ (marked_ne_zero T i hT), ?_⟩
  intro p
  rw [rawLogPrice_marked_finPower, rawLogPrice_update_eq_mark φ c T i x p]
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
structure MovingTensor (J : Type) (K : Type*) {r : ℕ} (q : Fin r → ℕ) where
  I : Type
  finiteI : Fintype I
  T : Raw.{0} I K
  mark : Fin r → I
  slot : I → Fin r ⊕ J
  slot_mark : ∀ i, slot (mark i) = .inl i
  eq_mark : ∀ k i, slot k = .inl i → k = mark i
  markEquiv : ∀ i, T.Leg (mark i) ≃ Fin (q i)
instance instMovingTensorFiniteI {J : Type} {K : Type*} {r : ℕ} {q : Fin r → ℕ} (s : MovingTensor J K q) : Fintype s.I := s.finiteI
namespace MovingTensor
variable {r : ℕ} {q : Fin r → ℕ} {J : Type} {K : Type*}
def ofRaw (T : Raw.{0} (Fin r) K) (e : ∀ i, T.Leg i ≃ Fin (q i)) : MovingTensor J K q where
  I := Fin r
  finiteI := inferInstance
  T := T
  mark := id
  slot := Sum.inl
  slot_mark _ := rfl
  eq_mark _ _ h := Sum.inl.inj h
  markEquiv := e
variable (s : MovingTensor J K q)
theorem mark_injective : Function.Injective s.mark := by
  intro i j hij
  exact Sum.inl.inj ((s.slot_mark i).symm.trans ((congrArg s.slot hij).trans (s.slot_mark j)))
def placement (p : Fin r → J) (k : s.I) : J := (s.slot k).elim p id
@[simp] theorem placement_mark (p : Fin r → J) (i : Fin r) : s.placement p (s.mark i) = p i := by
  simp [placement, s.slot_mark]
def grouped (p : Fin r → J) : Raw.{0} J K := s.T.group (s.placement p)
@[simp] theorem ofRaw_grouped (T : Raw.{0} (Fin r) K) (e : ∀ i, T.Leg i ≃ Fin (q i))
    (p : Fin r → J) : (ofRaw T e).grouped p = T.group p := rfl
def background (i : Fin r) (p : Fin r → J) : {k // k ≠ s.mark i} → J :=
  s.placement p ∘ Subtype.val
@[simp] theorem background_update_same (i : Fin r) (p : Fin r → J) (a : J) :
    s.background i (Function.update p i a) = s.background i p := by
  funext k
  change (s.slot k.val).elim _ _ = (s.slot k.val).elim _ _
  cases hs : s.slot k.val with
  | inl j =>
    have hji : j ≠ i := fun heq ↦ k.property (s.eq_mark k.val i (heq ▸ hs))
    exact Function.update_of_ne hji _ _
  | inr _ => rfl
abbrev backgroundLeg (i : Fin r) (k : {k // k ≠ s.mark i}) := s.T.Leg k.val
def markedCoeff (i : Fin r) (x : ∀ k, s.backgroundLeg i k) (t : Fin (q i)) : K :=
  markCoeff s.T (s.mark i) x ((s.markEquiv i).symm t)
theorem ofRaw_grouped_eq_marked [Fintype J] [Field K] (i : Fin r) (p : Fin r → J) :
    SiteTensor.ofRaw (s.grouped p) =
      SiteTensor.ofRaw ((marked (s.backgroundLeg i) (Fin (q i)) (s.markedCoeff i)).group
        (placeMark (s.background i p) (p i))) := by
  rw [← s.placement_mark p i]
  exact ofRaw_group_eq_markFin s.T (s.mark i) (s.markEquiv i) (s.placement p)
theorem marked_ne_zero [Field K] (i : Fin r) (hs : s.T.coeff ≠ 0) :
    (marked (s.backgroundLeg i) (Fin (q i)) (s.markedCoeff i)).coeff ≠ 0 :=
  marked_fin_ne_zero s.T (s.mark i) (s.markEquiv i) hs
private def childMark (i j : Fin r) : {k // k ≠ s.mark i} ⊕ Fin 3 :=
  if h : j = i then .inr 0 else .inl ⟨s.mark j, fun hk ↦ h (s.mark_injective hk)⟩
private def childSlot (i : Fin r) (a b : J) : {k // k ≠ s.mark i} ⊕ Fin 3 → Fin r ⊕ J :=
  Sum.elim (s.slot ∘ Subtype.val) ![Sum.inl i, Sum.inr a, Sum.inr b]
def child (i : Fin r) (H : Type) [Fintype H] (a b : J)
    (S : (∀ k, s.backgroundLeg i k) → Fin (q i) → H → H → K) : MovingTensor J K q where
  I := {k // k ≠ s.mark i} ⊕ Fin 3
  finiteI := inferInstance
  T := split (s.backgroundLeg i) (Fin (q i)) H S
  mark := s.childMark i
  slot := s.childSlot i a b
  slot_mark j := by
    by_cases h : j = i
    · subst j
      simp [childMark, childSlot]
    · simp [childMark, childSlot, h, s.slot_mark]
  eq_mark k j hk := by
    rcases k with k | k
    · change s.slot k.val = .inl j at hk
      have heq := s.eq_mark k.val j hk
      have hji : j ≠ i := fun h ↦ k.property (heq.trans (congrArg s.mark h))
      simp only [childMark, dite_eq_right hji, Sum.inl.injEq]
      exact Subtype.ext heq
    · fin_cases k <;> simp [childSlot] at hk
      subst j
      simp [childMark]
  markEquiv j := by
    by_cases h : j = i
    · subst j
      simp only [childMark]
      exact Equiv.refl _
    · simp only [childMark, dite_eq_right h]
      exact s.markEquiv j
theorem grouped_child (i : Fin r) (H : Type) [Fintype H] (a b : J)
    (S : (∀ k, s.backgroundLeg i k) → Fin (q i) → H → H → K) (p : Fin r → J) :
    (s.child i H a b S).grouped p =
      (split (s.backgroundLeg i) (Fin (q i)) H S).group (placeSplit (s.background i p) (p i) a b) := by
  apply congrArg ((split (s.backgroundLeg i) (Fin (q i)) H S).group)
  funext k
  rcases k with _ | k
  · rfl
  · fin_cases k <;> rfl
end MovingTensor
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
variable {r : ℕ} {J : Type} {K : Type*} {q : Fin r → ℕ}
abbrev MovingNode (J : Type) (K : Type*) [Zero K] {r : ℕ} (q : Fin r → ℕ) :=
  {s : MovingTensor J K q // s.T.coeff ≠ 0} × ℝ
def movingNodePrice [Fintype J] [Nonempty J] [Field K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (scale : ℝ)
    (x : MovingNode J K q) (p : Fin r → J) : ℝ :=
  rawLogPrice φ scale (x.1.val.grouped p) - x.2
def cornerAt (a b : Fin r → J) (x : Fin r → Bool) (i : Fin r) : J :=
  if x i then b i else a i
theorem cornerAt_update (a b : Fin r → J) (x : Fin r → Bool) (i : Fin r) (k : Bool) :
    cornerAt a b (Function.update x i k) =
      Function.update (cornerAt a b x) i (if k then b i else a i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [cornerAt]
  · simp [cornerAt, Function.update_of_ne h]
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Real
private theorem interior_floor {Q : ℕ} (hQ : 2 ≤ Q) {x : ℝ} (h₁ : 1 ≤ x) (h₂ : x ≤ Q) :
    ∃ b : ℕ, b + 2 ≤ Q ∧ (b : ℝ) + 1 ≤ x ∧ x ≤ (b : ℝ) + 2 := by
  by_cases htop : ⌊x⌋₊ < Q
  · have hb := (Nat.one_le_floor_iff x).mpr h₁
    obtain ⟨b, hb'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ⌊x⌋₊ ≠ 0)
    refine ⟨b, by omega, ?_, ?_⟩
    · simpa [hb'] using Nat.floor_le (by linarith : 0 ≤ x)
    · have := Nat.lt_floor_add_one x
      rw [hb', Nat.cast_succ] at this
      linarith
  · have hb : Q - 2 + 2 = Q := by omega
    refine ⟨Q - 2, hb.le, ?_, ?_⟩
    · have hx := Nat.floor_le (by linarith : 0 ≤ x)
      have h : Q ≤ ⌊x⌋₊ := by omega
      have : (Q : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h
      rw [Nat.cast_sub hQ]
      push_cast
      linarith
    · rw [Nat.cast_sub hQ]
      push_cast
      linarith
private theorem choose_adjacent {Q : ℕ} (b : ℕ) (hb : b + 1 ≤ Q) :
    (Q.choose (b + 1) : ℝ) / Q.choose b = ((Q : ℝ) - b) / ((b : ℝ) + 1) := by
  have hc : (0 : ℝ) < Q.choose b := by exact_mod_cast Nat.choose_pos (by omega : b ≤ Q)
  apply (div_eq_div_iff hc.ne' (by positivity)).mpr
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq Q b)
  push_cast [Nat.cast_sub (by omega : b ≤ Q)] at h
  linarith only [h]
theorem relocation_level_bounds {Q : ℕ} (hQ : 2 ≤ Q) {s : ℝ} (hs : s ∈ Set.Icc (-1) 1) :
    ∃ b : ℕ, b + 2 ≤ Q ∧
      logb 2 (Q.choose (b + 2)) - logb 2 (Q.choose (b + 1)) ∈
        Set.Icc (s * logb 2 Q - 2) (s * logb 2 Q) ∧
      logb 2 (Q.choose b) - logb 2 (Q.choose (b + 1)) ∈
        Set.Icc (-(s * logb 2 Q) - 2) (-(s * logb 2 Q)) := by
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ₀ : (0 : ℝ) < Q := by linarith
  let r := (Q : ℝ) ^ s
  have hr : 0 < r := Real.rpow_pos_of_pos hQ₀ _
  have hr₁ : (Q : ℝ)⁻¹ ≤ r := by
    simpa [r, Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Q) hs.1
  have hr₂ : r ≤ Q := by
    simpa [r, Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Q) hs.2
  have hQr : 1 ≤ (Q : ℝ) * r := by simpa [mul_comm] using (inv_le_iff_one_le_mul₀ hQ₀).mp hr₁
  have hden : 0 < 1 + r := by linarith
  obtain ⟨b, hb, hbx, hxb⟩ := interior_floor hQ
    ((le_div_iff₀ hden).mpr (by linarith : 1 * (1 + r) ≤ (Q : ℝ) + 1))
    ((div_le_iff₀ hden).mpr (by linarith))
  have hbx' := (le_div_iff₀ hden).mp hbx
  have hxb' := (div_le_iff₀ hden).mp hxb
  let A := (Q : ℝ) - b - 1
  let B := (b : ℝ) + 1
  have hA : 1 ≤ A := by
    have : (b : ℝ) + 2 ≤ Q := by exact_mod_cast hb
    dsimp [A]
    linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) b]
  let p := A / (B + 1)
  let m := B / (A + 1)
  have hp : 0 < p := div_pos (by linarith) (by linarith)
  have hm : 0 < m := div_pos (by linarith) (by linarith)
  have hPu : p ≤ r := by
    apply (div_le_iff₀ (by linarith : 0 < B + 1)).mpr
    dsimp [A, B]
    linarith only [hxb']
  have hMu : m ≤ r⁻¹ := by
    rw [← one_div, div_le_div_iff₀ (by linarith : 0 < A + 1) hr]
    dsimp [A, B]
    linarith only [hbx']
  have hprod : 1 / 4 ≤ p * m := by
    dsimp [p, m]
    rw [div_mul_div_comm]
    apply (le_div_iff₀ (mul_pos (by linarith) (by linarith))).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hlprod := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 1 / 4) hprod
  have hlog : logb 2 (1 / 4) = -2 := by
    rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  rw [hlog, Real.logb_mul hp.ne' hm.ne'] at hlprod
  have hpl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp hPu
  have hml := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hm hMu
  have hlr : logb 2 r = s * logb 2 Q := Real.logb_rpow_eq_mul_logb_of_pos hQ₀
  rw [hlr] at hpl
  rw [Real.logb_inv, hlr] at hml
  have hc (k : ℕ) (hk : k ≤ Q) : (0 : ℝ) < Q.choose k := by exact_mod_cast Nat.choose_pos hk
  have hp' : (Q.choose (b+2) : ℝ) / Q.choose (b+1) = p := by
    convert choose_adjacent (b + 1) hb using 1
    dsimp [p, A, B]
    push_cast
    ring
  have hm' : (Q.choose b : ℝ) / Q.choose (b+1) = m := by
    rw [← inv_div, choose_adjacent b (by omega), inv_div]
    dsimp [m, A, B]
    ring
  refine ⟨b, hb, ?_, ?_⟩
  · rw [← Real.logb_div (hc _ hb).ne' (hc _ (by omega)).ne', hp']
    exact ⟨by linarith, hpl⟩
  · rw [← Real.logb_div (hc _ (by omega)).ne' (hc _ (by omega)).ne', hm']
    exact ⟨by linarith, hml⟩
theorem relocation_level_bounds_for_threshold {n : ℕ} (hn : 0 < n) {t c : ℝ}
    (ht : 0 ≤ t) (hc : |c| ≤ n * t) :
    ∃ b : ℕ, b + 2 ≤ 2^n ∧
      t * (logb 2 ((2^n : ℕ).choose (b + 2)) - logb 2 ((2^n : ℕ).choose (b + 1))) ≤ c ∧
      t * (logb 2 ((2^n : ℕ).choose b) - logb 2 ((2^n : ℕ).choose (b + 1))) ≤ -c := by
  have hQ : 2 ≤ (2 : ℕ)^n := Nat.le_pow hn
  have hlog : logb 2 ((2^n : ℕ) : ℝ) = n := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  obtain ⟨s, hs, hcs⟩ : ∃ s ∈ Set.Icc (-1 : ℝ) 1, t * (s * n) = c := by
    rcases ht.eq_or_lt with rfl | ht'
    · have hc' : c = 0 := by simpa using hc
      exact ⟨0, by constructor <;> norm_num, by simp [hc']⟩
    have hnt : 0 < (n : ℝ) * t := by positivity
    refine ⟨c / (n * t), ⟨(le_div_iff₀ hnt).mpr ?_, (div_le_iff₀ hnt).mpr ?_⟩, ?_⟩
    · linarith [(abs_le.mp hc).1]
    · linarith [(abs_le.mp hc).2]
    · field_simp
  obtain ⟨b, hb, hp, hm⟩ := relocation_level_bounds hQ hs
  rw [hlog] at hp hm
  refine ⟨b, hb, (mul_le_mul_of_nonneg_left hp.2 ht).trans_eq hcs, ?_⟩
  exact (mul_le_mul_of_nonneg_left hm.2 ht).trans_eq (by rw [mul_neg, hcs])
open Filter
open scoped Topology
private theorem ratio_slope_limit {f : ℕ → ℝ} {a : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, f n ∈ Set.Icc (n * a - 2) (n * a)) :
    Tendsto (fun n : ℕ ↦ f n / n) atTop (𝓝 a) := by
  have hl : Tendsto (fun n : ℕ ↦ a - 2 / (n : ℝ)) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0, h] with n hn h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    apply (le_div_iff₀ hn').mpr
    rw [sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith only [h.1]
  · filter_upwards [eventually_gt_atTop 0, h] with n hn h
    exact (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr (by linarith only [h.2])
theorem relocation_level_limits {q : ℕ} (hq : 2 ≤ q) {s : ℝ} (hs : s ∈ Set.Icc (-1) 1) :
    ∃ b : ℕ → ℕ, (∀ᶠ n : ℕ in atTop, b n + 2 ≤ q^n) ∧
      Tendsto (fun n : ℕ ↦ (logb 2 ((q^n).choose (b n + 2)) -
        logb 2 ((q^n).choose (b n + 1))) / n) atTop (𝓝 (logb 2 q * s)) ∧
      Tendsto (fun n : ℕ ↦ (logb 2 ((q^n).choose (b n)) -
        logb 2 ((q^n).choose (b n + 1))) / n) atTop (𝓝 (-(logb 2 q * s))) := by
  classical
  choose f hf using fun (n : ℕ) (hn : 0 < n) ↦ relocation_level_bounds (hq.trans (Nat.le_pow hn)) hs
  let b (n : ℕ) := if hn : 0 < n then f n hn else 0
  refine ⟨b, ?_, ratio_slope_limit ?_, ratio_slope_limit ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    simpa [b, hn] using (hf n hn).1
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (hf n hn).2.1
    rw [Nat.cast_pow, Real.logb_pow] at h
    simpa [b, hn, mul_comm, mul_left_comm, mul_assoc] using h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have h := (hf n hn).2.2
    rw [Nat.cast_pow, Real.logb_pow] at h
    simpa [b, hn, mul_comm, mul_left_comm, mul_assoc] using h
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Real
open scoped Topology
theorem relocation_le_of_ratio_limits {wA wB wC u d c slope : ℝ}
    (plus minus : ℕ → ℝ)
    (hplus : Tendsto (fun n : ℕ ↦ plus n / n) atTop (𝓝 slope))
    (hminus : Tendsto (fun n : ℕ ↦ minus n / n) atTop (𝓝 (-slope)))
    (hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ) * wC ≤ c +
      max (n * wB + ((1 - u) * d) * plus n) (n * wA + (u * d) * minus n)) :
    wC ≤ max (wB + ((1 - u) * d) * slope) (wA + (u * d) * (-slope)) := by
  have hl := (tendsto_const_div_atTop_nhds_zero_nat c).add <|
    ((hplus.const_mul ((1 - u) * d)).const_add wB).max
      ((hminus.const_mul (u * d)).const_add wA)
  rw [zero_add] at hl
  refine ge_of_tendsto hl ?_
  filter_upwards [eventually_gt_atTop 0, hbound] with n hn h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change wC ≤ c / n + max (wB + ((1 - u) * d) * (plus n / n)) (wA + (u * d) * (minus n / n))
  apply (mul_le_mul_iff_of_pos_right hn').mp
  rw [add_mul, max_mul_of_nonneg _ _ hn'.le]
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  have e1 : c / ↑n * ↑n = c := div_mul_cancel₀ c hn0
  have e2 : (wB + (1 - u) * d * (plus n / ↑n)) * ↑n = ↑n * wB + (1 - u) * d * plus n := by
    rw [add_mul, mul_assoc ((1 - u) * d), div_mul_cancel₀ _ hn0]; ring1
  have e3 : (wA + u * d * (minus n / ↑n)) * ↑n = ↑n * wA + u * d * minus n := by
    rw [add_mul, mul_assoc (u * d), div_mul_cancel₀ _ hn0]; ring1
  convert h using 1
  all_goals first | rfl | ring1 | rw [e1, e2, e3]
theorem relocation_le_of_two_bounds {wA wB wC u d c : ℝ} {q : ℕ}
    (hd : 0 < d) (hq : 2 ≤ q)
    (hmove : |wA - wB| ≤ d * logb 2 q)
    (hbranches : ∀ s : ℝ, s ∈ Set.Icc (-1) 1 → ∃ plus minus : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ plus n / n) atTop (𝓝 (logb 2 q * s)) ∧
      Tendsto (fun n : ℕ ↦ minus n / n) atTop (𝓝 (-(logb 2 q * s))) ∧
      ∀ᶠ n : ℕ in atTop, (n : ℝ) * wC ≤ c +
        max (n * wB + ((1 - u) * d) * plus n) (n * wA + (u * d) * minus n)) :
    wC ≤ (1 - u) * wA + u * wB := by
  have hlog : 0 < logb 2 q := Real.logb_pos (by norm_num) (by exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hq)
  have hden := mul_pos hd hlog
  let s := (wA - wB) / (d * logb 2 q)
  have hs : s ∈ Set.Icc (-1) 1 := by
    have h := abs_le.mp hmove
    exact ⟨(le_div_iff₀ hden).mpr (by linarith), (div_le_iff₀ hden).mpr (by linarith)⟩
  obtain ⟨plus, minus, hplus, hminus, h⟩ := hbranches s hs
  have hbal : d * logb 2 q * s = wA - wB := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hden.ne'
  apply (relocation_le_of_ratio_limits plus minus hplus hminus h).trans
  apply max_le <;> linarith only [hbal, congrArg (u * ·) hbal]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Exterior
variable (K : Type*) [CommRing K] {Q : ℕ}
def sign (i : Fin Q) (S : Finset (Fin Q)) : K :=
  (-1) ^ (S.filter (· < i)).card
@[simp] theorem sign_sq (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i S * sign K i S = 1 := by
  simp [sign, ← mul_pow]
@[simp] theorem sign_erase_self (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i (S.erase i) = sign K i S := by
  simp [sign, Finset.filter_erase]
@[simp] theorem sign_insert_self (i : Fin Q) (S : Finset (Fin Q)) :
    sign K i (insert i S) = sign K i S := by
  simp [sign, Finset.filter_insert]
theorem sign_insert (i j : Fin Q) (S : Finset (Fin Q)) (hi : i ∉ S) :
    sign K j (insert i S) = if i < j then -sign K j S else sign K j S := by
  by_cases h : i < j <;> simp [sign, Finset.filter_insert, h, hi, pow_succ]
theorem sign_cancel {i j : Fin Q} {S : Finset (Fin Q)} (hij : i ≠ j)
    (hi : i ∉ S) (hj : j ∈ S) :
    sign K i S * sign K j (insert i S) + sign K j S * sign K i (S.erase j) = 0 := by
  have he := sign_insert K j i (S.erase j) (Finset.notMem_erase j S)
  rw [Finset.insert_erase hj] at he
  rw [sign_insert K i j S hi]
  rcases lt_or_gt_of_ne hij with h | h
  · simp only [h, not_lt_of_gt h, ite_true, ite_false] at he ⊢
    rw [he]
    ring
  · simp only [h, not_lt_of_gt h, ite_true, ite_false] at he ⊢
    rw [he]
    ring
end Exterior
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Exterior
open scoped BigOperators
abbrev Level (Q b : ℕ) := {S : Finset (Fin Q) // S.card = b}
theorem card_level (Q b : ℕ) : Fintype.card (Level Q b) = Q.choose b := by
  simp [Level, Fintype.card_finset_len]
variable (K : Type*) [CommRing K] {Q b : ℕ}
def create (i : Fin Q) : Matrix (Level Q (b + 1)) (Level Q b) K :=
  fun U S => if i ∉ S.val ∧ U.val = insert i S.val then sign K i S.val else 0
def contract (j : Fin Q) : Matrix (Level Q b) (Level Q (b + 1)) K :=
  fun R S => if j ∈ S.val ∧ R.val = S.val.erase j then sign K j S.val else 0
private theorem contract_create_entry (i j : Fin Q) (R S : Level Q b) :
    (contract (b := b) K j * create (b := b) K i) R S =
      if i ∉ S.val ∧ j ∈ insert i S.val ∧ R.val = (insert i S.val).erase j then
        sign K i S.val * sign K j (insert i S.val) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i ∈ S.val
  · simp [create, hi]
  let U : Level Q (b + 1) := ⟨insert i S.val, by simp [hi, S.property]⟩
  rw [Finset.sum_eq_single U]
  · dsimp [U, create, contract]
    split_ifs <;> simp_all [mul_comm]
  · intro V _ hV
    have hne : V.val ≠ insert i S.val := fun h => hV (Subtype.ext h)
    simp [create, hne]
  · simp
private theorem create_contract_entry (i j : Fin Q) (R S : Level Q (b + 1)) :
    (create (b := b) K i * contract (b := b) K j) R S =
      if j ∈ S.val ∧ i ∉ S.val.erase j ∧ R.val = insert i (S.val.erase j) then
        sign K j S.val * sign K i (S.val.erase j) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ S.val
  · let U : Level Q b := ⟨S.val.erase j, by rw [Finset.card_erase_of_mem hj, S.property]; rfl⟩
    rw [Finset.sum_eq_single U]
    · dsimp [U, create, contract]
      split_ifs <;> simp_all [mul_comm]
    · intro V _ hV
      have hne : V.val ≠ S.val.erase j := fun h => hV (Subtype.ext h)
      simp [contract, hne]
    · simp
  · simp [contract, hj]
theorem anticommutator (i j : Fin Q) :
    contract (b := b + 1) K j * create (b := b + 1) K i + create (b := b) K i * contract (b := b) K j =
      (if i = j then 1 else 0 : Matrix (Level Q (b + 1)) (Level Q (b + 1)) K) := by
  ext R S
  rw [Matrix.add_apply, contract_create_entry, create_contract_entry]
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S.val
    · simp [hi, Finset.insert_erase hi, Matrix.one_apply,
        Subtype.ext_iff]
    · simp [hi, Finset.erase_insert hi, Matrix.one_apply,
        Subtype.ext_iff]
  · have hji := Ne.symm hij
    by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val
    all_goals simp [hij, hji, hi, hj, Finset.erase_insert_of_ne hij]
    by_cases he : R.val = insert i (S.val.erase j)
    · simpa [he] using sign_cancel K hij hi hj
    · simp [he]
theorem split_coeff (v : Fin Q → K) (i : Fin Q) (R S : Level Q (b + 1)) :
    (∑ j, (contract (b := b + 1) K j * create (b := b + 1) K i) R S * v j) +
      (∑ j, (create (b := b) K i * contract (b := b) K j) R S * v j) =
        (if R = S then 1 else 0) * v i := by
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_mul, ← Matrix.add_apply]
  simp_rw [anticommutator]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply]
  · intro j _ hji
    simp [Ne.symm hji]
  · simp
end Exterior
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor.Relocation
open Exterior
open scoped BigOperators Classical
variable {I J : Type} {K : Type*} {A : I → Type} [CommRing K] {Q b : ℕ}
theorem plus_add_minus_eq (T : (∀ i, A i) → Fin Q → K)
    (x : ∀ i, A i) (i : Fin Q) (α β : Level Q (b + 1)) :
    plusCoeff T (create K) (contract K) x i α β +
      minusCoeff T (contract K) (create K) x i α β =
        T x i * (if α = β then 1 else 0) := by
  have h := split_coeff K (T x) i β α
  simp only [Matrix.mul_apply, Finset.sum_mul] at h
  simpa only [plusCoeff, minusCoeff, mul_assoc, mul_comm, mul_left_comm, eq_comm] using h
theorem grouped_split_le_of_add {U H : Type} [Fintype U] [Fintype H]
    [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)]
    (σ : I → J) (c a d : J) (P S R : (∀ i, A i) → U → H → H → K)
    (hsum : ∀ x i α β, P x i α β = S x i α β + R x i α β) :
    ofRaw ((split A U H P).group (placeSplit σ c a d)) ≤
      ofRaw ((split A U H S).group (placeSplit σ c a d)) +
        ofRaw ((split A U H R).group (placeSplit σ c a d)) := by
  let V (f : (∀ i, A i) → U → H → H → K) := (split A U H f).group (placeSplit σ c a d)
  let s : (∀ j, (V P).Leg j) → K := (V S).coeff
  let t : (∀ j, (V P).Leg j) → K := (V R).coeff
  have he : (V P).coeff = s + t := funext fun _ => hsum _ _ _ _
  apply ofRaw_le_iff.mpr
  change Crossing.IsRestriction (V P).coeff (sumCoeff s t)
  rw [he]
  exact ordinary_add_restricts _ _
theorem grouped_split_le [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)]
    (T : (∀ i, A i) → Fin Q → K) (σ : I → J) (c a d : J) :
    ofRaw ((split A (Fin Q) (Level Q (b + 1))
      (fun x i α β => T x i * (if α = β then 1 else 0))).group (placeSplit σ c a d)) ≤
      ofRaw ((split A (Fin Q) (Level Q (b + 1)) (plusCoeff T (create K) (contract K))).group
        (placeSplit σ c a d)) +
      ofRaw ((split A (Fin Q) (Level Q (b + 1)) (minusCoeff T (contract K) (create K))).group
        (placeSplit σ c a d)) :=
  grouped_split_le_of_add σ c a d _ _ _ fun x i α β => (plus_add_minus_eq T x i α β).symm
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SiteTensor.Relocation
variable {I J Q : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [Fintype Q] [∀ i, Fintype (A i)] [CommSemiring K]
theorem grouped_split_eq_mul (T : (∀ i, A i) → Q → K) (H : Type) [Fintype H] [DecidableEq H]
    (σ : I → J) (c a b : J) :
    ofRaw ((split A Q H (fun x i α β => T x i * if α = β then 1 else 0)).group
      (placeSplit σ c a b)) =
      ofRaw ((marked A Q T).group (placeMark σ c)) * ofRaw (wire K H a b) := by
  let S := (split A Q H (fun x i α β => T x i * if α = β then 1 else 0)).group
    (placeSplit σ c a b)
  let U := (marked A Q T).group (placeMark σ c)
  let W := wire K H a b
  let mark (j : J) (x : S.Leg j) : U.Leg j := fun t => match t with
    | ⟨.inl i,h⟩ => x ⟨.inl i,h⟩
    | ⟨.inr (),h⟩ => x ⟨.inr 0,h⟩
  let ends (j : J) (x : S.Leg j) : W.Leg j := fun ⟨t,h⟩ =>
    match t,h with
    | 0,h => x ⟨.inr 1,h⟩
    | 1,h => x ⟨.inr 2,h⟩
  let join (j : J) (y : U.Leg j × W.Leg j) : S.Leg j := fun t => match t with
    | ⟨.inl i,h⟩ => y.1 ⟨.inl i,h⟩
    | ⟨.inr 0,h⟩ => y.1 ⟨.inr (),h⟩
    | ⟨.inr 1,h⟩ => y.2 ⟨0,h⟩
    | ⟨.inr 2,h⟩ => y.2 ⟨1,h⟩
  let e (j : J) : S.Leg j ≃ (U.mul W).Leg j := {
    toFun := fun x => (mark j x, ends j x)
    invFun := join j
    left_inv := by
      intro x
      funext ⟨k,h⟩
      rcases k with i | i
      · rfl
      · fin_cases i <;> rfl
    right_inv := by
      intro y
      apply Prod.ext
      · funext ⟨k,h⟩
        rcases k with i | ⟨⟩ <;> rfl
      · funext ⟨i,h⟩
        fin_cases i <;> rfl }
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  let labels (t : Fin 2) : H := (ends _ (x (![a,b] t))) ⟨t,rfl⟩
  change _ * (if labels 0 = labels 1 then (1 : K) else 0) =
    _ * (Raw.diagonal (Fin 2) K H).coeff labels
  congr 1
  rw [Raw.diagonal_coeff_at (K := K) (1 : Fin 2) labels]
  congr 1
  exact propext ⟨fun h i => by fin_cases i <;> first | exact h | rfl, fun h => h 0⟩
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical NNReal
open Real
namespace SiteTensor
variable {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
private theorem logprice_le_of_sum (X Y Z : Raw.{0} J K) (c : ℝ) (hc : 0 ≤ c)
    (hX : X.coeff ≠ 0) (hs : ofRaw X ≤ ofRaw Y + ofRaw Z) :
    rawLogPrice φ c X ≤ c + max (rawLogPrice φ c Y) (rawLogPrice φ c Z) := by
  let f (T : Raw.{0} J K) : ℝ := φ.val (ofRaw T)
  have hx : 0 < f X := by exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
  have hnn := φ.property.2.2.2.2 _ _ hs
  rw [φ.property.2.2.1] at hnn
  have h : f X ≤ f Y + f Z := by exact_mod_cast hnn
  have branch {U : Raw.{0} J K} (hU : f X ≤ 2 * f U) : rawLogPrice φ c X ≤ c + rawLogPrice φ c U := by
    have hu : 0 < f U := by linarith
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hU
    rw [Real.logb_mul (by norm_num) hu.ne', Real.logb_self_eq_one (by norm_num)] at hl
    change c * logb 2 (f X) ≤ c + c * logb 2 (f U)
    linarith [mul_le_mul_of_nonneg_left hl hc]
  rcases le_total (f Y) (f Z) with h' | h'
  · exact (branch (U := Z) (by linarith)).trans (by gcongr; exact le_max_right _ _)
  · exact (branch (U := Y) (by linarith)).trans (by gcongr; exact le_max_left _ _)
omit [Fintype J] [Nonempty J] in
private theorem wire_coeff_nonzero (M : Type) [Fintype M] [Nonempty M] (p q : J) :
    (Relocation.wire K M p q).coeff ≠ 0 := by
  unfold Relocation.wire
  apply (Raw.group_ne_zero_iff ..).mpr
  intro h
  have H := congrFun h (fun _ => Classical.arbitrary M)
  change (Raw.diagonal (Fin 2) K M).coeff (fun _ => Classical.arbitrary M) = 0 at H
  simp [Raw.diagonal_coeff_at (0 : Fin 2)] at H
theorem relocation_finite_price_bound (A B C : Raw.{0} J K)
    (hA : A.coeff ≠ 0) (hB : B.coeff ≠ 0) (hC : C.coeff ≠ 0)
    (H P M : Type) [Fintype H] [Fintype P] [Fintype M] [Nonempty H] [Nonempty P] [Nonempty M]
    (a b z : J) (u d c : ℝ) (hc : 0 ≤ c)
    (hd : rawWireDistance φ c a b = d) (hza : rawWireDistance φ c z a = u * d)
    (hzb : rawWireDistance φ c z b = (1 - u) * d)
    (h : ofRaw C * ofRaw (Relocation.wire K H a b) ≤
      (ofRaw B * ofRaw (Relocation.wire K P z b)) * ofRaw (Relocation.wire K H z a) +
      (ofRaw A * ofRaw (Relocation.wire K M z a)) * ofRaw (Relocation.wire K H z b)) :
    rawLogPrice φ c C ≤ c +
      max (rawLogPrice φ c B + ((1 - u) * d) * (logb 2 (Fintype.card P) - logb 2 (Fintype.card H)))
        (rawLogPrice φ c A + (u * d) * (logb 2 (Fintype.card M) - logb 2 (Fintype.card H))) := by
  have mul_ne (X Y : Raw.{0} J K) (hx : X.coeff ≠ 0) (hy : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
    intro hzero
    have H := (ofRaw_eq_zero_iff (X.mul Y)).mpr hzero
    rw [ofRaw_mul] at H
    exact (mul_ne_zero ((ofRaw_eq_zero_iff X).not.mpr hx) ((ofRaw_eq_zero_iff Y).not.mpr hy)) H
  have hw (D : Type) [Fintype D] [Nonempty D] (p q : J) :
      rawLogPrice φ c (Relocation.wire K D p q) = rawWireDistance φ c p q * logb 2 (Fintype.card D) :=
    rawLogPrice_group_diagonal φ ![p,q] c
  have addwire (X : Raw.{0} J K) (hx : X.coeff ≠ 0) (D : Type) [Fintype D] [Nonempty D] (p q : J) :
      rawLogPrice φ c (X.mul (Relocation.wire K D p q)) =
        rawLogPrice φ c X + rawWireDistance φ c p q * logb 2 (Fintype.card D) := by
    rw [rawLogPrice_mul φ c _ _ hx (wire_coeff_nonzero D p q), hw]
  have hs := logprice_le_of_sum φ (C.mul (Relocation.wire K H a b))
    ((B.mul (Relocation.wire K P z b)).mul (Relocation.wire K H z a))
    ((A.mul (Relocation.wire K M z a)).mul (Relocation.wire K H z b)) c hc
    (mul_ne _ _ hC (wire_coeff_nonzero H a b)) h
  rw [addwire C hC, addwire _ (mul_ne _ _ hB (wire_coeff_nonzero P z b)),
    addwire _ (mul_ne _ _ hA (wire_coeff_nonzero M z a)), addwire B hB, addwire A hA,
    hd, hza, hzb] at hs
  rw [← sub_le_iff_le_add']
  apply le_trans (b := max _ _ - d * logb 2 (Fintype.card H))
  · linarith only [hs]
  rw [sub_eq_add_neg, ← max_add_add_right]
  apply max_le_max <;> apply le_of_eq <;> ring
namespace Relocation
open Exterior
theorem marked_finite_price_bound {I : Type} [Fintype I] {A : I → Type} [∀ i, Fintype (A i)]
    {Q b : ℕ} (hb : b + 2 ≤ Q) (T : (∀ i, A i) → Fin Q → K)
    (hT : (marked A (Fin Q) T).coeff ≠ 0) (σ : I → J) (a z e : J)
    (u d c : ℝ) (hc : 0 ≤ c) (hd : rawWireDistance φ c a e = d)
    (hza : rawWireDistance φ c z a = u * d) (hze : rawWireDistance φ c z e = (1 - u) * d) :
    rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ z)) ≤ c +
      max (rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ e)) +
            ((1 - u) * d) * (logb 2 (Q.choose (b+2)) - logb 2 (Q.choose (b+1))))
          (rawLogPrice φ c ((marked A (Fin Q) T).group (placeMark σ a)) +
            (u * d) * (logb 2 (Q.choose b) - logb 2 (Q.choose (b+1)))) := by
  have nz (k : ℕ) (hk : k ≤ Q) : Nonempty (Level Q k) :=
    Fintype.card_pos_iff.mp (by rw [card_level]; exact Nat.choose_pos hk)
  have := nz b (by omega)
  have := nz (b+1) (by omega)
  have := nz (b+2) hb
  have hsplit := grouped_split_le (b := b) T σ z a e
  have hprod := grouped_split_eq_mul T (Level Q (b+1)) σ z a e
  have hclass := hprod.symm.le.trans <| hsplit.trans (add_mono
    (ofRaw_le_iff.mpr (plus_restricts T (create K) (contract K) σ z a e))
    (ofRaw_le_iff.mpr (minus_restricts T (contract K) (create K) σ z a e)))
  have nth (p : J) := ((marked A (Fin Q) T).group_ne_zero_iff (placeMark σ p)).mpr hT
  simpa only [card_level] using relocation_finite_price_bound φ _ _ _ (nth a) (nth e) (nth z)
    (Level Q (b+1)) (Level Q (b+2)) (Level Q b) a e z u d c hc hd hza hze hclass
end Relocation
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Topology Classical
open Real Filter
namespace SiteTensor
variable {I J : Type} [Fintype I] [Fintype J] [Nonempty J] [DecidableEq I] {K : Type*} [Field K]
theorem rawLogPrice_relocate
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} I K) (x : I → J) (i : I) (a z b : J) (u : ℝ) (hu : u ∈ Set.Icc 0 1)
    (hza : rawWireDistance φ c z a = u * rawWireDistance φ c a b)
    (hzb : rawWireDistance φ c z b = (1 - u) * rawWireDistance φ c a b) :
    rawLogPrice φ c (T.group (Function.update x i z)) ≤
      (1 - u) * rawLogPrice φ c (T.group (Function.update x i a)) +
      u * rawLogPrice φ c (T.group (Function.update x i b)) := by
  let w (p : J) := rawLogPrice φ c (T.group (Function.update x i p))
  let d := rawWireDistance φ c a b
  let q := Fintype.card (T.Leg i)
  change w z ≤ (1 - u) * w a + u * w b
  by_cases hT : T.coeff = 0
  · have hw (p : J) : w p = 0 := rawLogPrice_zero φ c _ (funext fun _ => congrFun hT _)
    simp [hw]
  have hm (p r : J) : w p ≤ w r + rawWireDistance φ c p r * logb 2 q := by
    have h := rawLogPrice_move_le φ c hc T hT (Function.update x i r) (Function.update x i p) i
      (fun j hj => by simp [Function.update_of_ne hj])
    simpa only [Function.update_self, rawWireDistance_symm φ c r p] using h
  have ha := hm z a
  have hb := hm z b
  rw [hza] at ha
  rw [hzb] at hb
  change w z ≤ w a + (u * d) * logb 2 q at ha
  change w z ≤ w b + ((1 - u) * d) * logb 2 q at hb
  have hdeg (hdl : d * logb 2 q = 0) : w z ≤ (1 - u) * w a + u * w b := by
    rw [mul_assoc, hdl, mul_zero, add_zero] at ha hb
    linarith only [mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hu.2),
      mul_le_mul_of_nonneg_left hb hu.1]
  by_cases hd : 0 < d
  · by_cases hq : 2 ≤ q
    · apply relocation_le_of_two_bounds (d := d) (q := q) (c := c) hd hq
      · have hab := hm a b
        have hba := hm b a
        rw [rawWireDistance_symm φ c b a] at hba
        exact abs_le.mpr ⟨by dsimp [d]; linarith, by dsimp [d]; linarith⟩
      · intro s hs
        obtain ⟨l, hl, hp, hm⟩ := relocation_level_limits hq hs
        refine ⟨_, _, hp, hm, ?_⟩
        filter_upwards [hl] with n hn
        obtain ⟨S, hS, hw⟩ := Relocation.exists_finPower_update φ c T hT i x n
        have h := Relocation.marked_finite_price_bound φ hn S hS (x ∘ Subtype.val) a z b u d c
          hc rfl hza hzb
        dsimp only [w]
        rw [← hw z, ← hw b, ← hw a]
        exact h
    · have he : q = 0 ∨ q = 1 := by omega
      rcases he with hz | ho <;> apply hdeg <;> simp [*]
  · exact hdeg (by have hz : d = 0 := le_antisymm (le_of_not_gt hd) (rawLogPrice_nonneg φ hc _); rw [hz, zero_mul])
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
theorem CubeTable.IsCoupling.cost_sub_const {r : ℕ} {π : CubeTable r} {t : Fin r → ℝ}
    (h : CubeTable.IsCoupling π t) (N : CubeTable r) (C : ℝ) :
    CubeTable.cost π (fun e => N e - C) = CubeTable.cost π N - C := by
  simp only [CubeTable.cost, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h.total, one_mul]
namespace SiteTensor.Relocation
variable {r : ℕ} {q : Fin r → ℕ} {J : Type} {K : Type*}
theorem MovingTensor.placement_update (s : MovingTensor J K q) (p : Fin r → J) (i : Fin r) (v : J) :
    s.placement (Function.update p i v) = Function.update (s.placement p) (s.mark i) v := by
  funext k
  by_cases hk : k = s.mark i
  · subst k
    simp
  · rw [Function.update_of_ne hk]
    exact congrFun (s.background_update_same i p v) ⟨k,hk⟩
variable [Fintype J] [Nonempty J] [Field K]
theorem MovingTensor.rawLogPrice_independent (s : MovingTensor J K q)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (a b z : Fin r → J) (t : Fin r → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i)) :
    rawLogPrice φ c (s.grouped z) ≤ CubeTable.cost (CubeTable.independent t)
      (fun e => rawLogPrice φ c (s.grouped (fun i => if e i then b i else a i))) := by
  apply independent_relocation_cube (fun p => rawLogPrice φ c (s.grouped p)) a b z t ht
  intro i p
  simpa only [MovingTensor.grouped, s.placement_update] using
    rawLogPrice_relocate φ c hc s.T (s.placement p) (s.mark i) (a i) (z i) (b i)
      (t i) (ht i) (hza i) (hzb i)
theorem movingNodePrice_independent (x : MovingNode J K q)
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (a b z : Fin r → J) (t : Fin r → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i)) :
    movingNodePrice φ c x z ≤ CubeTable.cost (CubeTable.independent t)
      (fun e => movingNodePrice φ c x (cornerAt a b e)) := by
  unfold movingNodePrice
  rw [(CubeTable.independent_isCoupling ht).cost_sub_const]
  exact sub_le_sub_right (x.1.val.rawLogPrice_independent φ c hc a b z t ht hza hzb) _
end SiteTensor.Relocation
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Real
open scoped Topology
theorem relocation_width_limit {d B w : ℝ}
    (h : ∀ a : ℕ, d ≤ B + w / (2 : ℝ) ^ a) : d ≤ B := by
  have hw : Tendsto (fun a : ℕ ↦ w / (2 : ℝ) ^ a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact ge_of_tendsto' (by simpa using hw.const_add B) h
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter
namespace ManyRelocation
def rounds (r : ℕ) : ℕ → List (Fin r)
  | 0 => []
  | n + 1 => List.finRange r ++ rounds r n
@[simp] theorem count_rounds {r : ℕ} (j : Fin r) (n : ℕ) : (rounds r n).count j = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rounds, ih, Nat.add_comm]
@[simp] theorem length_rounds (r n : ℕ) : (rounds r n).length = r * n := by
  induction n with
  | zero => simp [rounds]
  | succ n ih => simp [rounds, ih, Nat.mul_succ, Nat.add_comm]
variable {ι T : Type*} (child : T → ι → Bool → T)
def Reaches : List ι → T → T → Prop
  | [], N, M => N = M
  | i :: rest, N, M => ∃ b, Reaches rest (child N i b) M
def AtEveryNode (ok : T → ι → Prop) : List ι → T → Prop
  | [], _ => True
  | i :: rest, N => ok N i ∧ ∀ b, AtEveryNode ok rest (child N i b)
theorem eventually_atEveryNode {I : Type*} {l : Filter I} (ok : I → T → ι → Prop)
    (inv : T → Prop) (pres : ∀ N i b, inv N → inv (child N i b))
    (h : ∀ N i, inv N → ∀ᶠ n in l, ok n N i) (sites : List ι) (N : T) (hN : inv N) :
    ∀ᶠ n in l, AtEveryNode child (ok n) sites N := by
  induction sites generalizing N with
  | nil => exact .of_forall fun _ => trivial
  | cons i rest ih =>
    filter_upwards [h N i hN, ih (child N i false) (pres N i false hN),
        ih (child N i true) (pres N i true hN)] with n hroot hleft hright
    exact ⟨hroot, fun b => by cases b <;> assumption⟩
theorem width_at_leaf [DecidableEq ι] (width : T → ι → ℝ)
    (hsplit : ∀ N i b, width (child N i b) i ≤ width N i / 2)
    (hother : ∀ N i j b, j ≠ i → width (child N i b) j ≤ width N j)
    {sites : List ι} {N M : T} (h : Reaches child sites N M) (j : ι) :
    width M j ≤ width N j / 2 ^ sites.count j := by
  induction sites generalizing N with
  | nil => cases h; simp
  | cons i rest ih =>
    obtain ⟨b, h⟩ := h
    refine (ih h).trans ?_
    by_cases hij : j = i
    · subst j
      simp only [List.count_cons_self, pow_succ]
      rw [mul_comm ((2 : ℝ) ^ _), ← div_div]
      exact div_le_div_of_nonneg_right (hsplit N i b) (by positivity)
    · simp only [List.count_cons_of_ne (Ne.symm hij)]
      exact div_le_div_of_nonneg_right (hother N i j b hij) (by positivity)
theorem le_of_reaches [Preorder T] (parent : ∀ N i b, child N i b ≤ N)
    {sites : List ι} {N M : T} (h : Reaches child sites N M) : M ≤ N := by
  induction sites generalizing N with
  | nil => cases h; rfl
  | cons i rest ih =>
    obtain ⟨b, hb⟩ := h
    exact (ih hb).trans (parent N i b)
theorem selectedLeaf {X : Type*} (inside : X → ℝ) (bounded : X → T → ℝ → Prop)
    (ok : T → ι → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (step : ∀ x N i σ, ok N i → 0 ≤ σ → bounded x N σ →
      ∃ y b, inside x ≤ inside y + ε ∧ bounded y (child N i b) (σ + ε))
    (sites : List ι) (N : T) (x : X) {σ : ℝ} (hσ : 0 ≤ σ) (hx : bounded x N σ)
    (hcheck : AtEveryNode child ok sites N) :
    ∃ y M, Reaches child sites N M ∧ inside x ≤ inside y + sites.length * ε ∧
      bounded y M (σ + sites.length * ε) := by
  induction sites generalizing N x σ with
  | nil => exact ⟨x, N, rfl, by simp, by simpa using hx⟩
  | cons i rest ih =>
    obtain ⟨y, b, hxy, hy⟩ := step x N i σ hcheck.1 hσ hx
    obtain ⟨z, M, hpath, hyz, hz⟩ := ih (child N i b) y (add_nonneg hσ hε) hy (hcheck.2 b)
    refine ⟨z, M, ⟨b, hpath⟩, ?_, ?_⟩
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · convert hz using 1
      simp [add_mul]
      ring
end ManyRelocation
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter
open scoped Topology
namespace CubeTable
variable {r : ℕ}
def AdmissibleGaps (g : Fin r → ℝ) (N : CubeTable r) : Prop :=
  ∀ i, -g i ≤ lower N i ∧ upper N i ≤ g i
theorem admissibleGaps_of_transport {g : Fin r → ℝ} {N : CubeTable r}
    (h : ∀ i x, |gap N i x| ≤ g i) : AdmissibleGaps g N :=
  fun i => ⟨lower_ge_of_forall _ _ (fun x => (abs_le.mp (h i x)).1),
    upper_le_of_forall _ _ (fun x => (abs_le.mp (h i x)).2)⟩
theorem AdmissibleGaps.child {g : Fin r → ℝ} {N : CubeTable r} (h : AdmissibleGaps g N)
    (i : Fin r) (b : Bool) : AdmissibleGaps g (child N i b) :=
  fun j => ⟨(h j).1.trans (lower_le_child N i j b), (upper_child_le N i j b).trans (h j).2⟩
theorem AdmissibleGaps.abs_midpoint_le {g : Fin r → ℝ} {N : CubeTable r}
    (h : AdmissibleGaps g N) (i : Fin r) : |midpoint N i| ≤ g i :=
  abs_le.mpr ⟨(h i).1.trans (midpoint_mem N i).1, (midpoint_mem N i).2.trans (h i).2⟩
def EndpointBound (actual table : CubeTable r) (slack : ℝ) : Prop :=
  ∀ x, actual x ≤ table x + slack
def SelectedSplit {X : Type*} (endpoint : X → CubeTable r) (inside : X → ℝ)
    (ε : ℝ) (N : CubeTable r) (i : Fin r) : Prop :=
  ∀ x σ, 0 ≤ σ → EndpointBound (endpoint x) N σ →
    ∃ y b, inside x ≤ inside y + ε ∧ EndpointBound (endpoint y) (child N i b) (σ + ε)
theorem root_le_of_selected_splits {X : ℕ → Type*} (endpoint : ∀ n, X n → CubeTable r)
    (inside : ∀ n, X n → ℝ) (root : ∀ n, X n) (M : CubeTable r) (g : Fin r → ℝ)
    {d B K : ℝ} (hM : AdmissibleGaps g M)
    (hroot : ∀ᶠ n : ℕ in atTop, d ≤ inside n (root n) ∧ endpoint n (root n) ≤ M)
    (step : ∀ ε > 0, ∀ N i, |midpoint N i| ≤ g i →
      ∀ᶠ n : ℕ in atTop, SelectedSplit (endpoint n) (inside n) ε N i)
    (leaf : ∀ᶠ n : ℕ in atTop, ∀ (y : X n) (N : CubeTable r) (σ ω : ℝ),
      N ≤ M → 0 ≤ ω → (∀ i, width N i ≤ ω) → EndpointBound (endpoint n y) N σ →
        inside n y ≤ B + K * ω + σ) : d ≤ B := by
  let W := ∑ i : Fin r, |width M i|
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hw (i : Fin r) : width M i ≤ W :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (width M j)) (Finset.mem_univ i))
  apply relocation_width_limit (w := K * W)
  intro a
  let sites := ManyRelocation.rounds r a
  have he (ε : ℝ) (hε : 0 < ε) :
      d ≤ (B + K * W / 2 ^ a) + (2 * sites.length) * ε := by
    have hcheck := ManyRelocation.eventually_atEveryNode child
      (fun n => SelectedSplit (endpoint n) (inside n) ε) (AdmissibleGaps g)
      (fun _ i b h => h.child i b) (fun N i h => step ε hε N i (h.abs_midpoint_le i)) sites M hM
    obtain ⟨n, ⟨⟨hd, hR⟩, htree⟩, hleaf⟩ := ((hroot.and hcheck).and leaf).exists
    have hentry : EndpointBound (endpoint n (root n)) M 0 := fun x => by simpa using hR x
    obtain ⟨y, N, path, interior, bound⟩ := ManyRelocation.selectedLeaf child (inside n)
      (fun x => EndpointBound (endpoint n x)) _ hε.le
      (fun x N i σ ok hs hx => ok x σ hs hx) sites M (root n) le_rfl hentry htree
    have hNM := ManyRelocation.le_of_reaches child child_le path
    have hsmall (i : Fin r) : width N i ≤ W / 2 ^ a := by
      have h := ManyRelocation.width_at_leaf child width width_child
        (fun N j k b _ => width_child_le N j k b) path i
      simp only [sites, ManyRelocation.count_rounds] at h
      exact h.trans (div_le_div_of_nonneg_right (hw i) (by positivity))
    have hprice := hleaf y N _ (W / 2 ^ a) hNM (by positivity) hsmall bound
    simp only [zero_add] at interior bound hprice
    rw [← mul_div_assoc] at hprice
    linarith
  have hzero : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := (hzero.const_mul (2 * (sites.length : ℝ))).const_add (B + K * W / 2 ^ a)
  apply ge_of_tendsto' (by simpa using hlim)
  exact fun k => he _ (by positivity)
theorem IsCoupling.cost_le_of_endpointBound {π N M : CubeTable r} {t : Fin r → ℝ} {σ : ℝ}
    (hπ : IsCoupling π t) (h : EndpointBound N M σ) : cost π N ≤ cost π M + σ := by
  calc
    _ ≤ ∑ x, π x * (M x + σ) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hπ.nonneg x)
    _ = _ := by simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hπ.total, cost]
theorem manySiteCoupledRelocation {X : ℕ → Type*} (endpoint : ∀ n, X n → CubeTable r)
    (inside : ∀ n, X n → ℝ) (root : ∀ n, X n) (M : CubeTable r) (g : Fin r → ℝ)
    {d : ℝ} (hM : AdmissibleGaps g M) {t : Fin r → ℝ} (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hroot : ∀ᶠ n : ℕ in atTop, d ≤ inside n (root n) ∧ endpoint n (root n) ≤ M)
    (step : ∀ ε > 0, ∀ N i, |midpoint N i| ≤ g i →
      ∀ᶠ n : ℕ in atTop, SelectedSplit (endpoint n) (inside n) ε N i)
    (hind : ∀ᶠ n : ℕ in atTop, ∀ y, inside n y ≤ cost (independent t) (endpoint n y))
    (π : CubeTable r) (hπ : IsCoupling π t) : d ≤ cost π M := by
  apply root_le_of_selected_splits endpoint inside root M g (K := 2 * r) hM hroot step
  filter_upwards [hind] with n hn
  intro y N σ ω hN hω hw hB
  have hprod := independent_isCoupling ht
  linarith [hn y, hprod.cost_le_of_endpointBound hB,
    cost_le_cost_of_width hprod hπ N hω hw, cost_mono hπ hN]
noncomputable def synchronized (r : ℕ) (t : ℝ) : CubeTable r := fun x =>
  (if (fun _ => false) = x then 1-t else 0) + (if (fun _ => true) = x then t else 0)
theorem synchronized_isCoupling {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    IsCoupling (synchronized r t) (fun _ => t) := by
  constructor
  · intro x
    unfold synchronized
    split_ifs <;> linarith [ht.1, ht.2]
  · simp [synchronized, Finset.sum_add_distrib]
  · intro i
    have hm (x : Fin r → Bool) : (if x i then synchronized r t x else 0) =
        if (fun _ => true) = x then t else 0 := by
      by_cases h0 : (fun _ => false) = x
      · subst x
        have hne : (fun _ : Fin r => true) ≠ (fun _ => false) :=
          fun h => Bool.noConfusion (congrFun h i)
        simp [hne]
      by_cases h1 : (fun _ => true) = x
      · subst x
        simp [synchronized, h0]
      simp [synchronized, h0, h1]
    simp [hm]
theorem cost_synchronized (t : ℝ) (M : CubeTable r) :
    cost (synchronized r t) M = (1-t) * M (fun _ => false) + t * M (fun _ => true) := by
  simp [cost, synchronized, add_mul, Finset.sum_add_distrib, ite_mul]
theorem synchronized_of_forall_couplings {d t : ℝ} {M : CubeTable r}
    (ht : t ∈ Set.Icc 0 1)
    (h : ∀ π : CubeTable r, IsCoupling π (fun _ => t) → d ≤ cost π M) :
    d ≤ (1-t) * M (fun _ => false) + t * M (fun _ => true) := by
  simpa only [cost_synchronized] using h _ (synchronized_isCoupling ht)
end CubeTable
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical BigOperators
namespace SiteTensor.Relocation
variable {I J Q H M : Type} {K : Type*} {A : I → Type}
variable [Fintype I] [Fintype J] [∀ i, Fintype (A i)]
variable [Fintype Q] [Fintype H] [Fintype M] [CommSemiring K]
private theorem copy_entry (f : H → K) (z : H) (w : K) :
    w * f z = ∑ m, (w * if m = z then 1 else 0) * f m := by
  simp [mul_ite, ite_mul]
theorem split_restricts_at_column (T : (∀ i, A i) → Q → K)
    (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β)
    (σ : I → J) (a b : J) :
    ((split A Q H S).group (placeSplit σ a a b)).Restricts
      (((marked A Q T).group (placeMark σ a)).mul (wire K H b a)) := by
  refine restricts_contraction T σ b a _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => if m = x ⟨.inr 2,rfl⟩ then 1 else 0)
    (fun x j m => f (x ⟨.inr 0,rfl⟩) j (x ⟨.inr 1,rfl⟩) m) ?_
  intro x
  refine (hS _ _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact copy_entry (K := K) (H := H) (fun m => f (x a ⟨.inr 0,rfl⟩) j (x a ⟨.inr 1,rfl⟩) m) _ _
theorem split_restricts_at_row (T : (∀ i, A i) → Q → K)
    (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β)
    (σ : I → J) (a b : J) :
    ((split A Q H S).group (placeSplit σ b a b)).Restricts
      (((marked A Q T).group (placeMark σ b)).mul (wire K H a b)) := by
  refine restricts_contraction T σ a b _ (fun i x => x ⟨.inl i, rfl⟩)
    (fun x m => if m = x ⟨.inr 1,rfl⟩ then 1 else 0)
    (fun x j m => f (x ⟨.inr 0,rfl⟩) j m (x ⟨.inr 2,rfl⟩)) ?_
  intro x
  refine (hS _ _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  exact copy_entry (K := K) (H := H) (fun m => f (x b ⟨.inr 0,rfl⟩) j m (x b ⟨.inr 2,rfl⟩)) _ _
omit [Fintype I] [∀ i, Fintype (A i)] [Fintype H] in
theorem plusCoeff_eq (T : (∀ i, A i) → Q → K) (L : Q → M → H → K) (D : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) :
    plusCoeff T L D x i α β = ∑ j, T x j * ∑ m, L i m α * D j β m := by
  simp only [plusCoeff, Finset.mul_sum, mul_assoc]
omit [Fintype I] [∀ i, Fintype (A i)] [Fintype H] in
theorem minusCoeff_eq (T : (∀ i, A i) → Q → K) (D : Q → M → H → K) (L : Q → H → M → K)
    (x : ∀ i, A i) (i : Q) (α β : H) :
    minusCoeff T D L x i α β = ∑ j, T x j * ∑ m, D j m α * L i β m := by
  simp only [minusCoeff, Finset.mul_sum, mul_assoc]
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
variable {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) {c : ℝ}
theorem rawLogPrice_mul_le (hc : 0 ≤ c) (X Y : Raw.{0} J K) :
    rawLogPrice φ c (X.mul Y) ≤ rawLogPrice φ c X + rawLogPrice φ c Y := by
  by_cases hx : X.coeff = 0
  · have h : (X.mul Y).coeff = 0 := funext fun x => by
      change X.coeff _ * Y.coeff _ = 0
      rw [hx]; exact zero_mul _
    rw [rawLogPrice_zero φ c _ h, rawLogPrice_zero φ c _ hx, zero_add]
    exact rawLogPrice_nonneg φ hc _
  by_cases hy : Y.coeff = 0
  · have h : (X.mul Y).coeff = 0 := funext fun x => by
      change X.coeff _ * Y.coeff _ = 0
      rw [hy]; exact mul_zero _
    rw [rawLogPrice_zero φ c _ h, rawLogPrice_zero φ c _ hy, add_zero]
    exact rawLogPrice_nonneg φ hc _
  exact (rawLogPrice_mul φ c X Y hx hy).le
namespace Relocation
variable {I Q H M : Type} {A : I → Type}
variable [Fintype I] [∀ i, Fintype (A i)] [Fintype Q] [Fintype H] [Fintype M]
variable [Nonempty H] [Nonempty M]
private theorem price_le_add_wire {D : Type} [Fintype D] [Nonempty D] (hc : 0 ≤ c)
    {X Y : Raw.{0} J K} (p q : J) (h : X.Restricts (Y.mul (wire K D p q))) :
    rawLogPrice φ c X ≤ rawLogPrice φ c Y +
      rawWireDistance φ c p q * Real.logb 2 (Fintype.card D) := by
  have hw : rawLogPrice φ c (wire K D p q) =
      rawWireDistance φ c p q * Real.logb 2 (Fintype.card D) :=
    rawLogPrice_group_diagonal φ ![p,q] c
  exact (rawLogPrice_mono φ hc h).trans ((rawLogPrice_mul_le φ hc Y _).trans_eq (by rw [hw]))
theorem collocated_prices (hc : 0 ≤ c)
    (T : (∀ i, A i) → Q → K) (S : (∀ i, A i) → Q → H → H → K) (f : Q → Q → H → H → K)
    (hS : ∀ x i α β, S x i α β = ∑ j, T x j * f i j α β) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H S).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) := by
  refine ⟨?_, price_le_add_wire φ hc a b (split_restricts_at_row T S f hS σ a b)⟩
  have h := price_le_add_wire φ hc b a (split_restricts_at_column T S f hS σ a b)
  rwa [rawWireDistance_symm φ c b a] at h
theorem plus_endpoint_prices (hc : 0 ≤ c) (T : (∀ i, A i) → Q → K)
    (L : Q → M → H → K) (D : Q → H → M → K) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H (plusCoeff T L D)).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) ∧
    child a ≤ parent b + t * Real.logb 2 (Fintype.card M) := by
  have h := collocated_prices φ hc T _ _ (plusCoeff_eq T L D) σ a b
  exact ⟨h.1, h.2, price_le_add_wire φ hc a b (plus_restricts_opposite T L D σ a b)⟩
theorem minus_endpoint_prices (hc : 0 ≤ c) (T : (∀ i, A i) → Q → K)
    (D : Q → M → H → K) (L : Q → H → M → K) (σ : I → J) (a b : J) :
    let child (p : J) := rawLogPrice φ c ((split A Q H (minusCoeff T D L)).group (placeSplit σ p a b))
    let parent (p : J) := rawLogPrice φ c ((marked A Q T).group (placeMark σ p))
    let t := rawWireDistance φ c a b
    child a ≤ parent a + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent b + t * Real.logb 2 (Fintype.card H) ∧
    child b ≤ parent a + t * Real.logb 2 (Fintype.card M) := by
  have h := collocated_prices φ hc T _ _ (minusCoeff_eq T D L) σ a b
  refine ⟨h.1, h.2, ?_⟩
  have h' := price_le_add_wire φ hc b a (minus_restricts_opposite T D L σ b a)
  rwa [rawWireDistance_symm φ c b a] at h'
end Relocation
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
namespace SiteTensor.Relocation
open Exterior
variable {I J : Type} {K : Type*} {A : I → Type} [Fintype I] [Fintype J] [Nonempty J] [∀ i, Fintype (A i)] [Field K] {Q b : ℕ}
theorem select_split (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    {scale : ℝ} (hscale : 0 ≤ scale) (T : (∀ i, A i) → Fin Q → K)
    (hT : (marked A (Fin Q) T).coeff ≠ 0) [Nonempty (Level Q (b + 1))]
    (σ : I → J) (c a d : J) :
    let parent := (marked A (Fin Q) T).group (placeMark σ c)
    let W := wire K (Level Q (b + 1)) a d
    let upper := split A (Fin Q) (Level Q (b + 1)) (plusCoeff T (create K) (contract K))
    let lower := split A (Fin Q) (Level Q (b + 1)) (minusCoeff T (contract K) (create K))
    (upper.coeff ≠ 0 ∧ rawLogPrice φ scale parent + rawLogPrice φ scale W ≤
      rawLogPrice φ scale (upper.group (placeSplit σ c a d)) + scale) ∨
    (lower.coeff ≠ 0 ∧ rawLogPrice φ scale parent + rawLogPrice φ scale W ≤
      rawLogPrice φ scale (lower.group (placeSplit σ c a d)) + scale) := by
  let H := Level Q (b + 1)
  let f := placeSplit σ c a d
  let V (v : (∀ i, A i) → Fin Q → H → H → K) := (split A (Fin Q) H v).group f
  let P := V (fun x i α β => T x i * if α = β then 1 else 0)
  let U := (marked A (Fin Q) T).group (placeMark σ c)
  let W := wire K H a d
  have hw : W.coeff ≠ 0 := by
    apply (Raw.group_ne_zero_iff ..).mpr
    intro h
    have hz := congrFun h (fun _ => Classical.arbitrary H)
    change (Raw.diagonal (Fin 2) K H).coeff (fun _ => Classical.arbitrary H) = 0 at hz
    simp [Raw.diagonal_coeff_at (0 : Fin 2)] at hz
  have hu : U.coeff ≠ 0 := (Raw.group_ne_zero_iff ..).mpr hT
  have hp : ofRaw P = ofRaw U * ofRaw W := grouped_split_eq_mul T H σ c a d
  have hpn : P.coeff ≠ 0 := by
    apply (ofRaw_eq_zero_iff P).not.mp
    rw [hp]
    exact mul_ne_zero ((ofRaw_eq_zero_iff U).not.mpr hu) ((ofRaw_eq_zero_iff W).not.mpr hw)
  have hpprice : rawLogPrice φ scale P = rawLogPrice φ scale U + rawLogPrice φ scale W := by
    rw [← rawLogPrice_mul φ scale U W hu hw]
    simp only [rawLogPrice, ofRaw_mul, hp]
  let s : (∀ j, P.Leg j) → K := (V (plusCoeff T (create K) (contract K))).coeff
  let t : (∀ j, P.Leg j) → K := (V (minusCoeff T (contract K) (create K))).coeff
  have he : P.coeff = s + t := funext fun _ => (plus_add_minus_eq T _ _ _ _).symm
  have hval : rawLogPrice φ scale ⟨P.Leg, inferInstance, s + t⟩ = rawLogPrice φ scale P := by
    rw [← he]
    rfl
  rcases rawLogPrice_add_select φ scale hscale s t (he ▸ hpn) with ⟨hs, hb⟩ | ⟨ht, hb⟩
  · rw [hval, hpprice] at hb
    exact Or.inl ⟨(Raw.group_ne_zero_iff ..).mp hs, hb⟩
  · rw [hval, hpprice] at hb
    exact Or.inr ⟨(Raw.group_ne_zero_iff ..).mp ht, hb⟩
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
open Function Real
namespace SiteTensor.Relocation
open Exterior
variable {r : ℕ} {J : Type} {K : Type*} [Fintype J] [Nonempty J] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
private abbrev value {q : Fin r → ℕ} (scale : ℝ) (s : MovingTensor J K q) (p : Fin r → J) :=
  rawLogPrice φ scale (s.grouped p)
private theorem value_marked {q : Fin r → ℕ} (scale : ℝ) (s : MovingTensor J K q)
    (i : Fin r) (p : Fin r → J) :
    value φ scale s p = rawLogPrice φ scale ((marked (s.backgroundLeg i) _ (s.markedCoeff i)).group
      (placeMark (s.background i p) (p i))) := by
  simp only [value, rawLogPrice, s.ofRaw_grouped_eq_marked i p]
theorem moving_selectedSplit {scale : ℝ} (hs : 0 ≤ scale) {n : ℕ} (hn : 0 < n)
    (a b z : Fin r → J) (N : CubeTable r) (i : Fin r)
    (hmid : |CubeTable.midpoint N i| ≤ n * rawWireDistance φ scale (a i) (b i))
    {ε : ℝ} (hε : scale ≤ ε) :
    CubeTable.SelectedSplit
      (fun (x : MovingNode J K (fun _ : Fin r ↦ 2 ^ n)) k ↦
        movingNodePrice φ scale x (cornerAt a b k))
      (fun x ↦ movingNodePrice φ scale x z) ε N i := by
  let d := rawWireDistance φ scale (a i) (b i)
  have hd : 0 ≤ d := rawLogPrice_nonneg φ hs _
  obtain ⟨l, hl, hhi, hlo⟩ := relocation_level_bounds_for_threshold hn hd hmid
  let Q := 2 ^ n
  let L (j : ℕ) := Level Q j
  let hlev (j : ℕ) (hj : j ≤ Q) : Nonempty (Level Q j) := by
    apply Fintype.card_pos_iff.mp
    rw [card_level]
    exact Nat.choose_pos hj
  have hQ : l + 2 ≤ Q := hl
  let : Nonempty (Level Q l) := hlev l (by omega)
  let : Nonempty (Level Q (l+1)) := hlev _ (by omega)
  let : Nonempty (Level Q (l+2)) := hlev _ hQ
  let cost (j : ℕ) := d * logb 2 (Fintype.card (L j))
  have hposcost : cost (l+2) - cost (l+1) ≤ CubeTable.midpoint N i := by
    simpa only [cost, L, card_level, Q, ← mul_sub] using hhi
  have hnegcost : cost l - cost (l+1) ≤ -CubeTable.midpoint N i := by
    simpa only [cost, L, card_level, Q, ← mul_sub] using hlo
  intro x σ _ hbound
  let s := x.1.val
  let T := s.markedCoeff i
  let upper := s.child i (L (l+1)) (a i) (b i)
    (plusCoeff T (create (b := l+1) K) (contract K))
  let lower := s.child i (L (l+1)) (a i) (b i)
    (minusCoeff T (contract (b := l) K) (create K))
  let childState (v : Bool) := if v then lower else upper
  let site (v : Bool) := if v then b i else a i
  have parent (p : Fin r → J) (t : J) :
      value φ scale s (update p i t) = rawLogPrice φ scale
        ((marked (s.backgroundLeg i) _ T).group (placeMark (s.background i p) t)) := by
    rw [value_marked φ scale s i, s.background_update_same, update_self]
  have upperBounds (p : Fin r → J) :
      value φ scale upper (update p i (a i)) ≤ value φ scale s (update p i (a i)) + cost (l+1) ∧
      value φ scale upper (update p i (b i)) ≤ value φ scale s (update p i (b i)) + cost (l+1) ∧
      value φ scale upper (update p i (a i)) ≤ value φ scale s (update p i (b i)) + cost (l+2) := by
    simp only [parent, upper, value, s.grouped_child, update_self, s.background_update_same]
    exact plus_endpoint_prices φ hs T (create (b := l+1) K) (contract K)
      (s.background i p) (a i) (b i)
  have lowerBounds (p : Fin r → J) :
      value φ scale lower (update p i (a i)) ≤ value φ scale s (update p i (a i)) + cost (l+1) ∧
      value φ scale lower (update p i (b i)) ≤ value φ scale s (update p i (b i)) + cost (l+1) ∧
      value φ scale lower (update p i (b i)) ≤ value φ scale s (update p i (a i)) + cost l := by
    simp only [parent, lower, value, s.grouped_child, update_self, s.background_update_same]
    exact minus_endpoint_prices φ hs T (contract (b := l) K) (create K)
      (s.background i p) (a i) (b i)
  have endpoints (v : Bool) (p : Fin r → J) (k : Bool) :
      value φ scale (childState v) (update p i (site k)) ≤ value φ scale s (update p i (site k)) + cost (l+1) := by
    cases v <;> cases k
    · exact (upperBounds p).1
    · exact (upperBounds p).2.1
    · exact (lowerBounds p).1
    · exact (lowerBounds p).2.1
  have opposite (v : Bool) (p : Fin r → J) :
      value φ scale (childState v) (update p i (site v)) ≤
        value φ scale s (update p i (site (!v))) + cost (l+1) +
          (if v then -CubeTable.midpoint N i else CubeTable.midpoint N i) := by
    cases v
    · change value φ scale upper (update p i (a i)) ≤
        value φ scale s (update p i (b i)) + cost (l+1) + CubeTable.midpoint N i
      linarith only [(upperBounds p).2.2, hposcost]
    · change value φ scale lower (update p i (b i)) ≤
        value φ scale s (update p i (a i)) + cost (l+1) + -CubeTable.midpoint N i
      linarith only [(lowerBounds p).2.2, hnegcost]
  have hsel := select_split (b := l) φ hs T (s.marked_ne_zero i x.1.property) (s.background i z)
    (z i) (a i) (b i)
  have hw : rawLogPrice φ scale (wire K (Level (2^n) (l+1)) (a i) (b i)) = cost (l+1) :=
    rawLogPrice_group_diagonal φ ![a i,b i] scale
  have winner : ∃ v : Bool, (childState v).T.coeff ≠ 0 ∧
      value φ scale s z + cost (l+1) ≤ value φ scale (childState v) z + scale := by
    rcases hsel with ⟨hnz, hb⟩ | ⟨hnz, hb⟩
    · refine ⟨false, hnz, ?_⟩
      simpa only [childState, Bool.false_eq_true, ite_false, upper, value_marked φ scale s i z,
        value, s.grouped_child, ← hw] using hb
    · refine ⟨true, hnz, ?_⟩
      simpa only [childState, ite_true, lower, value_marked φ scale s i z,
        value, s.grouped_child, ← hw] using hb
  obtain ⟨v, hnz, hv⟩ := winner
  let y : MovingNode J K (fun _ : Fin r ↦ 2^n) := (⟨childState v, hnz⟩, x.2 + cost (l+1))
  refine ⟨y, v, ?_, ?_⟩
  · change value φ scale s z - x.2 ≤ value φ scale (childState v) z - (x.2 + cost (l+1)) + ε
    linarith
  · intro k
    let p := cornerAt a b k
    have hp : update p i (site (k i)) = p := update_eq_self ..
    have h₁ := endpoints v p (k i)
    rw [hp] at h₁
    have hold := hbound k
    change value φ scale s p - x.2 ≤ N k + σ at hold
    change value φ scale (childState v) p - (x.2 + cost (l+1)) ≤ CubeTable.child N i v k + (σ+ε)
    have he : 0 ≤ ε := hs.trans hε
    simp only [CubeTable.child]
    split <;> rename_i hk
    · rw [← min_add_add_right]
      apply le_min
      · linarith
      · have h₂ := opposite v p
        rw [← hk, hp] at h₂
        have hm := hbound (update k i (!v))
        change value φ scale s (cornerAt a b (update k i (!v))) - x.2 ≤ N (update k i (!v)) + σ at hm
        rw [cornerAt_update] at hm
        change value φ scale s (update p i (site (!v))) - x.2 ≤ _ at hm
        rw [hk] at h₂
        linarith
    · linarith
end SiteTensor.Relocation
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SiteTensor.Raw
variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]
theorem Equivalent.coeff_ne_zero_iff {T U : Raw I K} (h : T.Equivalent U) :
    T.coeff ≠ 0 ↔ U.coeff ≠ 0 := by
  apply not_congr
  rw [← ofRaw_eq_zero_iff T, ← ofRaw_eq_zero_iff U, ofRaw_eq_iff.mpr h]
theorem exists_dyadic_padding (T : Raw.{0} I K) :
    ∃ k : ℕ, 0 < k ∧ ∃ U : Raw.{0} I K,
      (∀ i, Fintype.card (U.Leg i) = 2 ^ k) ∧ T.Equivalent U := by
  classical
  let d := Finset.univ.sup (fun i => Fintype.card (T.Leg i))
  let k := d + 1
  have hd (i : I) : Fintype.card (T.Leg i) ≤ d :=
    Finset.le_sup (f := fun i => Fintype.card (T.Leg i)) (Finset.mem_univ i)
  let e (i : I) : T.Leg i ↪ Fin (2 ^ k) :=
    (Fintype.equivFin (T.Leg i)).toEmbedding.trans
      (Fin.castLEEmb ((hd i).trans ((Nat.le_succ d).trans k.lt_two_pow_self.le)))
  let U : Raw.{0} I K := ⟨fun _ => Fin (2 ^ k), fun _ => inferInstance,
    pushCoeff (fun x i => e i (x i)) T.coeff⟩
  exact ⟨k, Nat.succ_pos _, U, fun _ => Fintype.card_fin _, equivalent_pushCoeff e T.coeff⟩
end SiteTensor.Raw
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open Filter
open scoped Topology Classical
namespace SiteTensor
open Relocation
variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K] {r : ℕ}
private def dyadicRoot (T : Raw.{0} (Fin r) K) (hT : T.coeff ≠ 0) (k : ℕ)
    (hcard : ∀ i, Fintype.card (T.Leg i) = 2 ^ k) (n : ℕ) :
    MovingNode J K (fun _ : Fin r => 2 ^ (k*n)) := by
  let R := MovingTensor.ofRaw (J := J) (q := fun _ : Fin r => 2 ^ (k*n)) (T.powerTensor n)
    (fun i => Fintype.equivFinOfCardEq (by
      change Fintype.card (Fin n → T.Leg i) = 2 ^ (k*n)
      simp [hcard, pow_mul]))
  exact (⟨R, T.powerTensor_ne_zero hT n⟩, 0)
private theorem dyadic_admissible
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} (Fin r) K) (k : ℕ) (hcard : ∀ i, Fintype.card (T.Leg i) = 2^k)
    (a b : Fin r → J) : CubeTable.AdmissibleGaps (fun i => k * rawWireDistance φ c (a i) (b i))
      (fun x => rawLogPrice φ c (T.group (cornerAt a b x))) := by
  apply CubeTable.admissibleGaps_of_transport
  intro i x
  let p := Function.update (cornerAt a b x) i (a i)
  let v := Function.update (cornerAt a b x) i (b i)
  have h := rawLogPrice_transport φ c hc T p v
  have hsum : (∑ j, rawWireDistance φ c (p j) (v j) * Real.logb 2 (Fintype.card (T.Leg j))) =
      k * rawWireDistance φ c (a i) (b i) := by
    rw [Finset.sum_eq_single i]
    · simp [p, v, hcard, Real.logb_pow, mul_comm]
    · intro j _ hji
      simp [p, v, Function.update_of_ne hji, rawWireDistance_self φ c hc]
    · simp
  rw [hsum] at h
  simpa [CubeTable.gap, cornerAt_update, p, v] using h
private theorem dyadic_coupled [NeZero r]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} (Fin r) K) (hT : T.coeff ≠ 0) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ i, Fintype.card (T.Leg i) = 2^k) (a z b : Fin r → J)
    (t : Fin r → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i))
    (π : CubeTable r) (hπ : CubeTable.IsCoupling π t) :
    rawLogPrice φ c (T.group z) ≤ CubeTable.cost π
      (fun e => rawLogPrice φ c (T.group (cornerAt a b e))) := by
  let M : CubeTable r := fun e => rawLogPrice φ c (T.group (cornerAt a b e))
  let endpoint (n : ℕ) (y : MovingNode J K (fun _ : Fin r => 2^(k*n))) (e : Fin r → Bool) :=
    movingNodePrice φ (c/n) y (cornerAt a b e)
  let inside (n : ℕ) (y : MovingNode J K (fun _ : Fin r => 2^(k*n))) := movingNodePrice φ (c/n) y z
  have hw (n : ℕ) (p q : J) : rawWireDistance φ (c/n) p q = rawWireDistance φ c p q / n := by
    unfold rawWireDistance rawLogPrice
    ring
  have rootPrice (n : ℕ) (hn : 0 < n) (p : Fin r → J) :
      movingNodePrice φ (c/n) (dyadicRoot T hT k hcard n) p = rawLogPrice φ c (T.group p) := by
    change rawLogPrice φ (c/n) ((T.powerTensor n).group p) - 0 = _
    rw [sub_zero, rawLogPrice_group_powerTensor]
    unfold rawLogPrice
    field_simp
  apply CubeTable.manySiteCoupledRelocation endpoint inside (dyadicRoot T hT k hcard) M
    (fun i => k * rawWireDistance φ c (a i) (b i)) (dyadic_admissible φ c hc T k hcard a b)
    ht ?_ ?_ ?_ π hπ
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact ⟨(rootPrice n hn z).ge, fun e => (rootPrice n hn _).le⟩
  · intro ε hε N i hmid
    have hsmall := (tendsto_const_div_atTop_nhds_zero_nat c).eventually_lt_const hε
    filter_upwards [eventually_gt_atTop 0, hsmall] with n hn hsc
    refine moving_selectedSplit φ (by positivity) (Nat.mul_pos hk hn) a b z N i ?_ hsc.le
    rw [hw, Nat.cast_mul, mul_assoc, mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0)]
    exact hmid
  · refine .of_forall fun n y => movingNodePrice_independent y φ (c/n) (by positivity) a b z t ht ?_ ?_
    · intro i
      rw [hw, hw, hza, mul_div_assoc]
    · intro i
      rw [hw, hw, hzb, mul_div_assoc]
theorem rawLogPrice_coupled_relocation
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
    (T : Raw.{0} (Fin r) K) (a z b : Fin r → J) (t : Fin r → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i))
    (π : CubeTable r) (hπ : CubeTable.IsCoupling π t) :
    rawLogPrice φ c (T.group z) ≤ CubeTable.cost π
      (fun e => rawLogPrice φ c (T.group (cornerAt a b e))) := by
  rcases eq_or_ne r 0 with rfl | hr
  · have he (x : Fin 0 → Bool) : cornerAt a b x = z := Subsingleton.elim _ _
    simp only [CubeTable.cost, he, ← Finset.sum_mul, hπ.total, one_mul, le_refl]
  let : NeZero r := ⟨hr⟩
  by_cases hT : T.coeff = 0
  · have hzero (p : Fin r → J) : rawLogPrice φ c (T.group p) = 0 :=
      rawLogPrice_zero φ c _ (funext fun x => congrFun hT _)
    simp [hzero, CubeTable.cost]
  obtain ⟨k,hk,U,hcard,hU⟩ := T.exists_dyadic_padding
  have he (p : Fin r → J) : rawLogPrice φ c (T.group p) = rawLogPrice φ c (U.group p) := by
    change c * Real.logb 2 (φ.val _ : ℝ) = _
    have eqClass : ofRaw (T.group p) = ofRaw (U.group p) := ofRaw_eq_iff.mpr
      ⟨Raw.group_restricts p hU.1, Raw.group_restricts p hU.2⟩
    rw [eqClass]
    rfl
  simp only [he]
  exact dyadic_coupled φ c hc U (hU.coeff_ne_zero_iff.mp hT) k hk hcard a z b t ht hza hzb π hπ
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
open Relocation
variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K] {r : ℕ}
theorem binaryDiagonal_coupled_relocation
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 < c)
    (a z b : Fin r → J) (t : Fin r → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i))
    (π : CubeTable r) (hπ : CubeTable.IsCoupling π t) :
    rawLogPrice φ c ((Raw.diagonal (Fin r) K (Fin 2)).group z) ≤ CubeTable.cost π
      (fun e ↦ rawLogPrice φ c ((Raw.diagonal (Fin r) K (Fin 2)).group (cornerAt a b e))) :=
  rawLogPrice_coupled_relocation φ c hc.le _ a z b t ht hza hzb π hπ
theorem rawDiagonalJointConvexity (K : Type*) [Field K] : RawDiagonalJointConvexity K := by
  intro J _ _ φ c hc r _ a z b t ht hza hzb
  let T := Raw.diagonal (Fin r) K (Fin 2)
  let M : CubeTable r := fun e ↦ rawLogPrice φ c (T.group (cornerAt a b e))
  have h := CubeTable.synchronized_of_forall_couplings (M := M) ht
    (binaryDiagonal_coupled_relocation φ c hc a z b (fun _ ↦ t) (fun _ ↦ ht) hza hzb)
  have h0 : cornerAt a b (fun _ ↦ false) = a := rfl
  have h1 : cornerAt a b (fun _ ↦ true) = b := rfl
  simpa only [M, h0, h1, T] using h
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset
open scoped BigOperators
abbrev FockState (N : ℕ) := ↥((range N).powerset)
def FockState.insert {N : ℕ} (S : FockState N) (r : Fin N) : FockState N :=
  ⟨Insert.insert r.val S.val, mem_powerset.mpr <|
    insert_subset (mem_range.mpr r.isLt) (mem_powerset.mp S.property)⟩
variable (K : Type*) [CommRing K] {N : ℕ}
end Fermion
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

/-- Grouping the binary diagonal along any map gives, up to equivalence, the mask diagonal on the image. -/
theorem ofRaw_group_diag_image {J : Type} [Fintype J] [DecidableEq J] [Nonempty J] {r : ℕ} [NeZero r]
    (f : Fin r → J) :
    ofRaw ((Raw.diagonal (Fin r) ℂ (Fin 2)).group f) =
      ofRaw (Raw.maskDiagonal ℂ (Finset.univ.image f) (Fin 2)) := by
  classical
  let S := Finset.univ.image f
  let g : Fin r → S := fun i => ⟨f i, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨i, rfl⟩
  let h : S → Fin r := Function.surjInv hg
  have hgh : ∀ y, g (h y) = y := Function.surjInv_eq hg
  let σ : S ↪ J := Function.Embedding.subtype _
  haveI : Nonempty S := ⟨g ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩⟩
  have hf : f = (σ : S → J) ∘ g := rfl
  have e1 : ((Raw.diagonal (Fin r) ℂ (Fin 2)).group ((σ : S → J) ∘ g)).Restricts
      ((Raw.diagonal S ℂ (Fin 2)).group (σ : S → J)) :=
    Raw.group_diagonal_restricts_of_comp (σ : S → J) g (Fin 2)
  have e2 : ((Raw.diagonal S ℂ (Fin 2)).group (((σ : S → J) ∘ g) ∘ h)).Restricts
      ((Raw.diagonal (Fin r) ℂ (Fin 2)).group ((σ : S → J) ∘ g)) :=
    Raw.group_diagonal_restricts_of_comp ((σ : S → J) ∘ g) h (Fin 2)
  have hcomp : ((σ : S → J) ∘ g) ∘ h = (σ : S → J) := by
    funext y
    simp only [Function.comp_apply, hgh]
  rw [hcomp] at e2
  rw [hf, ofRaw_eq_iff.mpr ⟨e1, e2⟩]
  exact Raw.ofRaw_group_diagonal_eq_mask σ S
    (fun i => ⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩) (Fin 2)

theorem rawLogPrice_group_diag {J : Type} [Fintype J] [DecidableEq J] [Nonempty J] {r : ℕ} [NeZero r]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J ℂ → _ → Prop)) (f : Fin r → J) :
    rawLogPrice φ 1 ((Raw.diagonal (Fin r) ℂ (Fin 2)).group f) =
      Real.logb 2 (psi φ (maskSig (Finset.univ.image f))) := by
  have hne : (Finset.univ.image f).Nonempty :=
    Finset.Nonempty.image ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩, Finset.mem_univ _⟩ f
  rw [rawLogPrice, one_mul, ofRaw_group_diag_image, ← mask_le (psi φ) (psi_mono φ) _ hne,
    psi_toSig]

end OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro δ hmono hpair hpts Q s t hs ht hst
  classical
  by_cases hQ : Q = ∅
  · subst hQ
    simp only [Finset.image_empty]
    have : s * δ ∅ + t * δ ∅ = δ ∅ := by rw [← add_mul, hst, one_mul]
    linarith
  have hQne : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQ
  set A := Q.image Prod.fst with hA
  set B := Q.image Prod.snd with hB
  set Z := Q.image (fun q : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => s • q.1 + t • q.2)
    with hZ
  let U := A ∪ B ∪ Z
  have hAU : A ⊆ U := fun p hp => Finset.mem_union_left _ (Finset.mem_union_left _ hp)
  have hBU : B ⊆ U := fun p hp => Finset.mem_union_left _ (Finset.mem_union_right _ hp)
  have hZU : Z ⊆ U := fun p hp => Finset.mem_union_right _ hp
  have hAne : A.Nonempty := hQne.image _
  have hBne : B.Nonempty := hQne.image _
  have hZne : Z.Nonempty := hQne.image _
  by_cases hU : U.card ≤ 1
  · have hsub : ∀ p ∈ U, ∀ q ∈ U, p = q := fun p hp q hq => Finset.card_le_one.mp hU p hp q hq
    have eq_of : ∀ X Y : Finset (EuclideanSpace ℝ (Fin 2)), X ⊆ U → Y ⊆ U → X.Nonempty → Y.Nonempty →
        X = Y := by
      intro X Y hX hY hXn hYn
      obtain ⟨y0, hy0⟩ := hYn
      obtain ⟨x0, hx0⟩ := hXn
      ext p
      constructor
      · intro hp; rw [hsub p (hX hp) y0 (hY hy0)]; exact hy0
      · intro hp; rw [hsub p (hY hp) x0 (hX hx0)]; exact hx0
    rw [eq_of A Z hAU hZU hAne hZne, eq_of B Z hBU hZU hBne hZne, ← add_mul, hst, one_mul]
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
  have key : ∀ S : Finset I, S.Nonempty →
      Real.logb 2 (Ψ (OMAPort.maskSig S)) = δ (S.image x) / δ U := by
    intro S hSn
    have h := hΨ S hSn
    rw [hUx] at h
    exact h
  have wire : ∀ u v : I, rawWireDistance φ 1 u v = dist (x u) (x v) / δ U := by
    intro u v
    rw [← OMAPort.logb_psi_wire φ u v, hpsi, OMAPort.wire_eq_mask hS u v,
      key {u, v} (Finset.insert_nonempty _ _)]
    simp only [Finset.image_insert, Finset.image_singleton]
    rw [hpair]
  have price : ∀ {r : ℕ} [NeZero r] (f : Fin r → I),
      rawLogPrice φ 1 ((Raw.diagonal (Fin r) ℂ (Fin 2)).group f) =
        δ ((Finset.univ.image f).image x) / δ U := by
    intro r _ f
    have hne : (Finset.univ.image f).Nonempty :=
      Finset.Nonempty.image ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩, Finset.mem_univ _⟩ f
    rw [OMAPort.rawLogPrice_group_diag, hpsi, key _ hne]
  let r := Q.card
  haveI : NeZero r := ⟨(Finset.card_pos.mpr hQne).ne'⟩
  let e : Fin r ≃ Q := Q.equivFin.symm
  have mem_of : ∀ (g : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (X : Finset (EuclideanSpace ℝ (Fin 2))), Q.image g = X → X ⊆ U → ∀ i, g (e i).1 ∈ U :=
    fun g X hX hXU i => hXU (hX ▸ Finset.mem_image_of_mem g (e i).2)
  let a : Fin r → I := fun i => ⟨(e i).1.1, mem_of Prod.fst A hA.symm hAU i⟩
  let b : Fin r → I := fun i => ⟨(e i).1.2, mem_of Prod.snd B hB.symm hBU i⟩
  let z : Fin r → I := fun i => ⟨s • (e i).1.1 + t • (e i).1.2,
    mem_of (fun q => s • q.1 + t • q.2) Z hZ.symm hZU i⟩
  have himg : ∀ g : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      Finset.univ.image (fun i => g (e i).1) = Q.image g := by
    intro g
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨(e i).1, (e i).2, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨e.symm ⟨q, hq⟩, by simp⟩
  have hza : ∀ i, rawWireDistance φ 1 (z i) (a i) = t * rawWireDistance φ 1 (a i) (b i) := by
    intro i
    rw [wire, wire]
    have hd : dist (x (z i)) (x (a i)) = t * dist (x (a i)) (x (b i)) := by
      change dist (s • (e i).1.1 + t • (e i).1.2) (e i).1.1 = t * dist (e i).1.1 (e i).1.2
      rw [dist_eq_norm, dist_eq_norm,
        show s • (e i).1.1 + t • (e i).1.2 - (e i).1.1 = t • ((e i).1.2 - (e i).1.1) by
          rw [show s = 1 - t by linarith, sub_smul, one_smul, smul_sub]; abel,
        norm_smul, Real.norm_of_nonneg ht, norm_sub_rev]
    rw [hd, mul_div_assoc]
  have hzb : ∀ i, rawWireDistance φ 1 (z i) (b i) = (1 - t) * rawWireDistance φ 1 (a i) (b i) := by
    intro i
    rw [wire, wire]
    have hd : dist (x (z i)) (x (b i)) = (1 - t) * dist (x (a i)) (x (b i)) := by
      change dist (s • (e i).1.1 + t • (e i).1.2) (e i).1.2 = (1 - t) * dist (e i).1.1 (e i).1.2
      rw [dist_eq_norm, dist_eq_norm,
        show s • (e i).1.1 + t • (e i).1.2 - (e i).1.2 = s • ((e i).1.1 - (e i).1.2) by
          rw [show t = 1 - s by linarith, sub_smul, one_smul, smul_sub]; abel,
        norm_smul, Real.norm_of_nonneg hs, show s = 1 - t by linarith]
    rw [hd, mul_div_assoc]
  have hR := rawDiagonalJointConvexity ℂ φ 1 one_pos r a z b t ⟨ht, by linarith⟩ hza hzb
  rw [price, price, price] at hR
  have ia : (Finset.univ.image a).image x = A := by
    rw [Finset.image_image]; exact himg Prod.fst
  have ib : (Finset.univ.image b).image x = B := by
    rw [Finset.image_image]; exact himg Prod.snd
  have iz : (Finset.univ.image z).image x = Z := by
    rw [Finset.image_image]; exact himg (fun q => s • q.1 + t • q.2)
  rw [ia, ib, iz] at hR
  have h1t : 1 - t = s := by linarith
  rw [h1t] at hR
  have hne : δ U ≠ 0 := hpos.ne'
  have e1 : δ Z = δ U * (δ Z / δ U) := by
    first | (field_simp; done) | (field_simp; ring)
  have e2 : s * δ A + t * δ B = δ U * (s * (δ A / δ U) + t * (δ B / δ U)) := by
    first | (field_simp; done) | (field_simp; ring)
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hR hpos.le

