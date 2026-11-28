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
theorem dite_eq_left {c : Prop} {h : Decidable c} {α : Sort*} {t : c → α} {e : ¬ c → α} (hc : c) :
    dite c t e = t hc := dif_pos hc
theorem dite_eq_right {c : Prop} {h : Decidable c} {α : Sort*} {t : c → α} {e : ¬ c → α} (hnc : ¬ c) :
    dite c t e = e hnc := dif_neg hnc
namespace OAI
section
section
noncomputable section
open scoped Topology ContinuousMap
namespace HyperbolicObstruction
def IsSegment {X : Type*} [MetricSpace X] (γ : ℝ → X) (x y : X) : Prop :=
  γ 0 = x ∧ γ 1 = y ∧
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    dist (γ s) (γ t) = |s - t| * dist x y
def IsGeodesic (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y
def CATZero (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ, IsSegment γ x y ∧
    ∀ z : X, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist z (γ t) ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
        t * (1 - t) * dist x y ^ 2
universe u
end HyperbolicObstruction
end
end
end
end OAI
namespace OAI
section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]
def segment (h : CATZero X) (x y : X) : ℝ → X := (h x y).choose
theorem segment_spec (h : CATZero X) (x y : X) :
    IsSegment (segment h x y) x y := (h x y).choose_spec.1
theorem segment_cn (h : CATZero X) (x y z : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist z (segment h x y t) ^ 2 ≤
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 :=
  (h x y).choose_spec.2 z t ht
theorem segment_left (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist x (segment h x y t) = t * dist x y := by
  have hs := (segment_spec h x y).2.2 0 (by norm_num) t ht
  rw [(segment_spec h x y).1] at hs
  simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hs
theorem eq_segment_of_dist (h : CATZero X) {x y p : X} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : dist x p = t * dist x y)
    (hy : dist p y = (1 - t) * dist x y) :
    p = segment h x y t := by
  have hc := segment_cn h x y p ht
  rw [dist_comm p x, hx, hy] at hc
  have hz : dist p (segment h x y t) ^ 2 ≤ 0 := by nlinarith [hc]
  have hn : 0 ≤ dist p (segment h x y t) := dist_nonneg
  exact dist_eq_zero.mp (by nlinarith)
theorem cn_of_dist (h : CATZero X) {x y p : X} (z : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : dist x p = t * dist x y)
    (hy : dist p y = (1 - t) * dist x y) :
    dist z p ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
      t * (1 - t) * dist x y ^ 2 := by
  rw [eq_segment_of_dist h ht hx hy]
  exact segment_cn h x y z ht
end CATZero
end HyperbolicObstruction
end
end
end
end
end OAI
namespace OAI
section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]
theorem segment_dist (h : CATZero X) (x y : X) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h x y s) (segment h x y t) = |s - t| * dist x y :=
  (segment_spec h x y).2.2 s hs t ht
open Filter Topology
end CATZero
end HyperbolicObstruction
end
end
end
end
end
end
end OAI
namespace OAI
section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction
namespace MetricScale
universe u
structure Space (r : ℝ) (hr : 0 < r) (X : Type u) where
  val : X
theorem Space.ext {r : ℝ} {hr : 0 < r} {X : Type u} {x y : Space r hr X} (h : x.val = y.val) :
    x = y := by
  cases x; cases y; cases h; rfl
variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]
instance : MetricSpace (Space r hr X) where
  dist x y := r * dist x.val y.val
  dist_self x := by simp
  dist_comm x y := by simp only [dist_comm]
  dist_triangle x y z := by
    simpa only [mul_add] using mul_le_mul_of_nonneg_left
      (dist_triangle x.val y.val z.val) hr.le
  eq_of_dist_eq_zero {x y} h := by
    apply Space.ext
    exact dist_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hr.ne')
lemma dist_eq (x y : Space r hr X) : dist x y = r * dist x.val y.val := rfl
variable (h : CATZero X)
include h
theorem catZero : CATZero (Space r hr X) := by
  intro x y
  refine ⟨fun t => ⟨CATZero.segment h x.val y.val t⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply Space.ext
    exact (CATZero.segment_spec h _ _).1
  · apply Space.ext
    exact (CATZero.segment_spec h _ _).2.1
  · intro s hs t ht
    change r * dist (CATZero.segment h x.val y.val s) (CATZero.segment h x.val y.val t) =
      |s - t| * (r * dist x.val y.val)
    rw [CATZero.segment_dist h _ _ hs ht]
    ring
  · intro z t ht
    have hi := mul_le_mul_of_nonneg_left (CATZero.segment_cn h x.val y.val z.val ht)
      (sq_nonneg r)
    simp only [dist_eq]
    nlinarith only [hi]
end MetricScale
end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
noncomputable section
noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace MetricLimit
universe u
variable (U : Ultrafilter ℕ) (X : ℕ → Type u) [∀ n, MetricSpace (X n)] (o : ∀ n, X n)
structure Bounded (U : Ultrafilter ℕ) (X : ℕ → Type u)
    [∀ n, MetricSpace (X n)] (o : ∀ n, X n) where
  val : ∀ n, X n
  bound : ∃ R : ℝ, ∀ n, dist (o n) (val n) ≤ R
theorem Bounded.ext {U : Ultrafilter ℕ} {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}
    {x y : Bounded U X o} (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

variable {U X o}
lemma bounded_dist (x y : Bounded U X o) :
    ∃ R : ℝ, ∀ n, dist (x.val n) (y.val n) ∈ Set.Icc 0 R := by
  obtain ⟨R, hR⟩ := x.bound
  obtain ⟨S, hS⟩ := y.bound
  exact ⟨R + S, fun n => ⟨dist_nonneg, (dist_triangle (x.val n) (o n) (y.val n)).trans
    (by rw [dist_comm (x.val n)]; exact add_le_add (hR n) (hS n))⟩⟩
def preDist (x y : Bounded U X o) : ℝ :=
  limUnder (U : Filter ℕ) (fun n => dist (x.val n) (y.val n))
lemma tendsto_dist (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n)) (U : Filter ℕ) (𝓝 (preDist x y)) := by
  obtain ⟨R, hR⟩ := bounded_dist x y
  have hh := isCompact_Icc.ultrafilter_le_nhds' (U.map (fun n => dist (x.val n) (y.val n)))
    (show Set.Icc (0 : ℝ) R ∈ U.map (fun n => dist (x.val n) (y.val n)) from
      by
        change ∀ᶠ n in (U : Filter ℕ), dist (x.val n) (y.val n) ∈ Set.Icc (0 : ℝ) R
        exact Filter.Eventually.of_forall hR)
  obtain ⟨a, ha, ht⟩ := hh
  exact tendsto_nhds_limUnder ⟨a, ht⟩
instance : PseudoMetricSpace (Bounded U X o) where
  dist := preDist
  dist_self x := by
    exact tendsto_nhds_unique (tendsto_dist x x) (by simpa only [dist_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) U (𝓝 0)))
  dist_comm x y := by simp only [preDist, dist_comm]
  dist_triangle x y z := le_of_tendsto_of_tendsto (tendsto_dist x z)
    ((tendsto_dist x y).add (tendsto_dist y z))
    (Filter.Eventually.of_forall fun n => dist_triangle (x.val n) (y.val n) (z.val n))
abbrev Space := SeparationQuotient (Bounded U X o)
def point (x : Bounded U X o) : Space (U := U) (X := X) (o := o) := SeparationQuotient.mk x
lemma tendsto_point_dist (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n)) U (𝓝 (dist (point x) (point y))) :=
  tendsto_dist x y
variable (h : ∀ n, CATZero (X n))
def segment (x y : Bounded U X o) (t : ℝ) : Bounded U X o :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    ⟨fun n => CATZero.segment (h n) (x.val n) (y.val n) t, by
      obtain ⟨R, hR⟩ := x.bound
      obtain ⟨S, hS⟩ := y.bound
      refine ⟨2 * R + S, fun n => ?_⟩
      have hd : dist (x.val n) (y.val n) ≤ R + S :=
        (dist_triangle (x.val n) (o n) (y.val n)).trans (by
          rw [dist_comm (x.val n)]; exact add_le_add (hR n) (hS n))
      calc
        _ ≤ dist (o n) (x.val n) + dist (x.val n)
          (CATZero.segment (h n) (x.val n) (y.val n) t) := dist_triangle _ _ _
        _ = dist (o n) (x.val n) + t * dist (x.val n) (y.val n) := by
          rw [CATZero.segment_left (h n) _ _ ht]
        _ ≤ R + dist (x.val n) (y.val n) := add_le_add (hR n)
          (mul_le_of_le_one_left dist_nonneg ht.2)
        _ ≤ 2 * R + S := by linarith⟩
  else x
lemma segment_val (x y : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (segment h x y t).val n = CATZero.segment (h n) (x.val n) (y.val n) t := by
  simp only [segment, dite_eq_left ht]
lemma segment_zero (x y : Bounded U X o) : segment h x y 0 = x := by
  apply Bounded.ext
  funext n
  rw [segment_val h x y (by norm_num)]
  exact (CATZero.segment_spec (h n) _ _).1
lemma segment_one (x y : Bounded U X o) : segment h x y 1 = y := by
  apply Bounded.ext
  funext n
  rw [segment_val h x y (by norm_num)]
  exact (CATZero.segment_spec (h n) _ _).2.1
lemma segment_dist (x y : Bounded U X o) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (point (segment h x y s)) (point (segment h x y t)) =
      |s - t| * dist (point x) (point y) := by
  apply tendsto_nhds_unique (tendsto_point_dist _ _)
  convert (tendsto_point_dist x y).const_mul |s - t| using 1
  funext n
  rw [segment_val h x y hs, segment_val h x y ht, CATZero.segment_dist (h n) _ _ hs ht]
lemma segment_cn (x y z : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (point z) (point (segment h x y t)) ^ 2 ≤
      (1 - t) * dist (point z) (point x) ^ 2 + t * dist (point z) (point y) ^ 2 -
        t * (1 - t) * dist (point x) (point y) ^ 2 := by
  apply le_of_tendsto_of_tendsto ((tendsto_point_dist z (segment h x y t)).pow 2)
    ((((tendsto_point_dist z x).pow 2).const_mul (1 - t)).add
      (((tendsto_point_dist z y).pow 2).const_mul t) |>.sub
        (((tendsto_point_dist x y).pow 2).const_mul (t * (1 - t))))
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [segment_val h x y ht]
  exact CATZero.segment_cn (h n) _ _ _ ht
include h
theorem catZero : CATZero (Space (U := U) (X := X) (o := o)) := by
  intro x y
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
  refine ⟨fun t => point (segment h x y t), ⟨?_, ?_, ?_⟩, ?_⟩
  · dsimp only
    rw [segment_zero]
    rfl
  · dsimp only
    rw [segment_one]
    rfl
  · exact fun s hs t ht => segment_dist h x y hs ht
  · intro z t ht
    obtain ⟨z, rfl⟩ := SeparationQuotient.surjective_mk z
    exact segment_cn h x y z ht
end MetricLimit
end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
namespace OAI
noncomputable section
namespace HyperbolicObstruction
namespace CurvatureComparison
open Set
lemma midpoint_nonpos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      f ((s+t)/2) ≤ (f s+f t)/2) (h0 : f 0 ≤ 0) (h1 : f 1 ≤ 0) :
    ∀ t ∈ Icc (0:ℝ) 1, f t ≤ 0 := by
  intro t ht
  by_contra! hpos
  let ε := f t / 2
  have he : 0 < ε := by dsimp [ε]; positivity
  let g : ℝ → ℝ := fun s => f s+ε*s^2
  have hg : ContinuousOn g (Icc 0 1) :=
    hf.add ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hg
  have hlarge : ε < g x := by
    have h := hm ht
    have hn : 0 ≤ ε*t^2 := mul_nonneg he.le (sq_nonneg t)
    dsimp [g,ε] at *
    linarith
  have hx0 : 0 < x := by
    by_contra hh
    have heq : x=0 := le_antisymm (not_lt.mp hh) hx.1
    subst x
    simp only [g,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hlarge
    linarith
  have hx1 : x < 1 := by
    by_contra hh
    have heq : x=1 := le_antisymm hx.2 (not_lt.mp hh)
    subst x
    simp only [g,one_pow,mul_one] at hlarge
    linarith
  let r := min x (1-x) / 2
  have hr : 0 < r := by dsimp [r]; exact div_pos (lt_min hx0 (sub_pos.mpr hx1)) (by norm_num)
  have hrx : r ≤ x := by
    have h := min_le_left x (1-x)
    dsimp [r]
    linarith
  have hr1 : r ≤ 1-x := by
    have h := min_le_right x (1-x)
    dsimp [r]
    linarith
  have hl : x-r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hu : x+r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hcv := hmid (x-r) hl (x+r) hu
  rw [show ((x-r)+(x+r))/2=x by ring] at hcv
  have hml := hm hl
  have hmu := hm hu
  have hp : 0 < ε*r^2 := mul_pos he (sq_pos_of_pos hr)
  dsimp [g] at hml hmu
  nlinarith
end CurvatureComparison
section
open Set Real CurvatureComparison
variable {X : Type*} [MetricSpace X]
lemma IsSegment.continuousOn {γ : ℝ → X} {x y : X} (h : IsSegment γ x y) :
    ContinuousOn γ (Icc 0 1) := by
  apply LipschitzOnWith.continuousOn (K := ⟨dist x y,dist_nonneg⟩)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [h.2.2 s hs t ht,Real.dist_eq]
  exact le_of_eq (mul_comm _ _)
end
section
open Set
variable {X : Type*} [MetricSpace X]
lemma IsSegment.reparam {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    IsSegment (fun u => γ ((1-u)*s+u*t)) (γ s) (γ t) := by
  refine ⟨by simp,by simp,?_⟩
  intro u hu v hv
  have hm (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : (1-a)*s+a*t ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (by linarith [ha.2]) hs.1) (mul_nonneg ha.1 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hs.2),
        mul_nonneg ha.1 (sub_nonneg.mpr ht.2)]
  rw [h.2.2 _ (hm u hu) _ (hm v hv),h.2.2 s hs t ht]
  rw [show (1-u)*s+u*t-((1-v)*s+v*t)=(u-v)*(t-s) by ring,abs_mul,abs_sub_comm t s]
  ring
lemma IsSegment.dist_from_source {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : dist x (γ t)=t*dist x y := by
  have hh := h.2.2 0 (by norm_num) t ht
  simpa only [h.1,zero_sub,abs_neg,abs_of_nonneg ht.1] using hh
lemma catZero_of_segment_midpoint (g : IsGeodesic X)
    (h : ∀ {γ : ℝ → X} {x y : X}, IsSegment γ x y → ∀ z : X,
      dist z (γ (1/2))^2 ≤ (dist z x^2+dist z y^2)/2-dist x y^2/4) : CATZero X := by
  intro x y
  obtain ⟨γ,hγ⟩ := g x y
  refine ⟨γ,hγ,fun z t ht => ?_⟩
  let F : ℝ → ℝ := fun s => dist z (γ s)^2-
    ((1-s)*dist z x^2+s*dist z y^2-s*(1-s)*dist x y^2)
  have hF : ContinuousOn F (Icc 0 1) := by
    apply ContinuousOn.sub
    · exact (continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)).pow 2
    · fun_prop
  have hf0 : F 0≤0 := by simp [F,hγ.1]
  have hf1 : F 1≤0 := by simp [F,hγ.2.1]
  have hm : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1, F ((a+b)/2)≤(F a+F b)/2 := by
    intro a ha b hb
    have hh := h (hγ.reparam ha hb) z
    simp only [show (1-(1/2:ℝ))*a+(1/2)*b=(a+b)/2 by ring] at hh
    rw [hγ.2.2 a ha b hb,mul_pow,sq_abs] at hh
    dsimp [F]
    nlinarith
  have hh := CurvatureComparison.midpoint_nonpos hF hm hf0 hf1 t ht
  dsimp [F] at hh
  linarith
def RadialBusemann (X : Type*) [MetricSpace X] : Prop :=
  ∀ (o x y : X) (α β : ℝ → X), IsSegment α o x → IsSegment β o y →
    ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t) ≤ t*dist x y
end
open Set Metric
end HyperbolicObstruction
end
end OAI
namespace OAI
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
namespace SharpIntegralFillings
universe u
section Geometry
variable (X : Type u) [MetricSpace X]
def IsCAT0 : Prop :=
  ∃ segment : X → X → ℝ → X,
    (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
    (∀ x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment x y s) (segment x y t) = |s - t| * dist x y) ∧
    (∀ o x y s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      dist (segment o x s) (segment o y t) ^ 2 ≤
        (s * dist o x - t * dist o y) ^ 2 +
          s * t * ((dist x y) ^ 2 - (dist o x - dist o y) ^ 2))
end Geometry
theorem IsCAT0.exists_squared_distance_convex
    {X : Type u} [MetricSpace X] (hX : IsCAT0 X) :
    ∃ segment : X → X → ℝ → X,
      (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
      ∀ o y x t, t ∈ Icc (0 : ℝ) 1 →
        dist (segment o y t) x ^ 2 ≤
          (1 - t) * dist o x ^ 2 + t * dist y x ^ 2 -
            t * (1 - t) * dist o y ^ 2 := by
  obtain ⟨s, hs, _, hc⟩ := hX
  refine ⟨s, hs, ?_⟩
  intro o y x t ht
  have h := hc o y x t 1 ht (by simp)
  rw [(hs o x).2] at h
  convert h using 1
  ring
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
end SharpIntegralFillings
end
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
theorem isClosed_normalizedSpectrum (restricts : S → S → Prop) :
    IsClosed (normalizedSpectrum restricts) := by
  have hmono : IsClosed {f : S → ℝ≥0 | ∀ x y, restricts x y → f x ≤ f y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦
      isClosed_le (continuous_apply x) (continuous_apply y)
  exact (isClosed_setOfPred_map_zero S ℝ≥0).inter <|
    (isClosed_setOfPred_map_one S ℝ≥0).inter <|
    (isClosed_setOfPred_map_add S ℝ≥0).inter ((isClosed_setOfPred_map_mul S ℝ≥0).inter hmono)
theorem isCompact_normalizedSpectrum (restricts : S → S → Prop)
    (hfinite : ∀ x : S, ∃ r : ℕ, restricts x r) : IsCompact (normalizedSpectrum restricts) := by
  choose r hr using hfinite
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun x ↦ isCompact_Icc (a := (0 : ℝ≥0)) (b := (r x : ℝ≥0))))
    (isClosed_normalizedSpectrum restricts)
  intro f hf x _
  have hle := hf.2.2.2.2 x _ (hr x)
  have hcast : f (r x : S) = (r x : ℝ≥0) := map_natCast (normalizedSpectrum.toRingHom ⟨f, hf⟩) _
  exact ⟨bot_le, hle.trans_eq hcast⟩
theorem continuous_log_price {restricts : S → S → Prop} {x : S} (hx : restricts 1 x) :
    Continuous (fun f : normalizedSpectrum restricts ↦ Real.logb 2 (f.val x : ℝ)) := by
  apply (continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)).logb
  intro f
  have hone := f.2.2.2.2.2 1 x hx
  rw [f.2.2.1] at hone
  change (f.val x : ℝ) ≠ 0
  exact_mod_cast (zero_lt_one.trans_le hone).ne'
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
def spectralLogHom (hunit : ∀ t : P, res 1 t) (f : normalizedSpectrum res) :
    Additive P →+ ℝ where
  toFun x := Real.logb 2 (f.val x.toMul.val : ℝ)
  map_zero' := by simp [f.property.2.1]
  map_add' x y := by
    have hpos (t : P) : (f.val t.val : ℝ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_spectral_value f (hunit t))).ne'
    simp only [toMul_add, Submonoid.coe_mul, f.property.2.2.2.1, NNReal.coe_mul]
    exact Real.logb_mul (hpos x.toMul) (hpos y.toMul)
def IsSpectralPrice (hunit : ∀ t : P, res 1 t) (g : Additive P →+ ℝ) : Prop :=
  g = 0 ∨ ∃ (f : normalizedSpectrum res) (c : ℝ), 0 < c ∧ g = c • spectralLogHom hunit f
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
instance [Nonempty I] [Nontrivial K] : Nontrivial (TensorClass.{v} I K) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h' := (ofRaw_eq_zero_iff (Raw.one.{v} I K)).mp h
  exact one_ne_zero (congrFun h' (fun _ => PUnit.unit))
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
structure SpectralPlacementPrices (K : Type*) [Field K] (X : Type*) [PseudoMetricSpace X] where
  price {I : Type} [Fintype I] (T : Raw.{0} I K) (x : I → X) : ℝ
  zero_tensor {I : Type} [Fintype I] (T : Raw.{0} I K) (h : T.coeff = 0) (x : I → X) :
    price T x = 0
  collapsed {I : Type} [Fintype I] (T : Raw.{0} I K) (p : X) : price T (fun _ => p) = 0
  group {I J : Type} [Fintype I] [Fintype J] (T : Raw.{0} I K) (σ : I → J) (x : J → X) :
    price T (x ∘ σ) = price (T.group σ) x
  wire (x : Fin 2 → X) : price (Raw.diagonal (Fin 2) K (Fin 2)) x = dist (x 0) (x 1)
  transport {I : Type} [Fintype I] (T : Raw.{0} I K) (x y : I → X) :
    dist (price T x) (price T y) ≤ ∑ i, dist (x i) (y i) * Real.logb 2 (Fintype.card (T.Leg i))
  dist_le_diagonal {I : Type} [Fintype I] (x : I → X) (i j : I) :
    dist (x i) (x j) ≤ price (Raw.diagonal I K (Fin 2)) x
  normalized {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ X) :
    ∃ φ : normalizedSpectrum (fun a b : TensorClass.{0} I K => a ≤ b), ∀ T : Raw.{0} I K,
      T.coeff ≠ 0 → price T x =
        price (Raw.diagonal I K (Fin 2)) x * Real.logb 2 (φ.val (ofRaw T) : ℝ)
namespace SpectralPlacementPrices
variable {K X : Type*} [Field K] [PseudoMetricSpace X]
def pullback {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K X) (f : Y → X)
    (hf : Isometry f) : SpectralPlacementPrices K Y where
  price T x := P.price T (f ∘ x)
  zero_tensor T h x := P.zero_tensor T h (f ∘ x)
  collapsed T p := P.collapsed T (f p)
  group T σ x := P.group T σ (f ∘ x)
  wire x := (P.wire (f ∘ x)).trans (hf.dist_eq (x 0) (x 1))
  transport T x y := by simpa only [Function.comp_apply, hf.dist_eq] using P.transport T (f ∘ x) (f ∘ y)
  dist_le_diagonal x i j := by simpa only [Function.comp_apply, hf.dist_eq] using P.dist_le_diagonal (f ∘ x) i j
  normalized x := P.normalized (x.trans ⟨f, hf.injective⟩)
theorem diagonal_pos {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K Y)
    {I : Type} [Fintype I] [Nontrivial I] (x : I ↪ Y) :
    0 < P.price (Raw.diagonal I K (Fin 2)) x := by
  obtain ⟨i, j, hne⟩ := exists_pair_ne I
  exact (dist_pos.mpr (x.injective.ne hne)).trans_le (P.dist_le_diagonal x i j)
theorem normalized_group {Y : Type*} [MetricSpace Y] (P : SpectralPlacementPrices K Y)
    {J : Type} [Fintype J] [Nontrivial J] (y : J ↪ Y) :
    ∃ φ : normalizedSpectrum (fun a b : TensorClass.{0} J K => a ≤ b),
      0 < P.price (Raw.diagonal J K (Fin 2)) y ∧
      ∀ {I : Type} [Fintype I] (σ : I → J) (T : Raw.{0} I K), T.coeff ≠ 0 →
        P.price T (y ∘ σ) = P.price (Raw.diagonal J K (Fin 2)) y *
          Real.logb 2 (φ.val (ofRaw (T.group σ)) : ℝ) := by
  obtain ⟨φ, hφ⟩ := P.normalized y
  refine ⟨φ, P.diagonal_pos y, ?_⟩
  intro I _ σ T hT
  exact (P.group T σ y).trans (hφ _ ((T.group_ne_zero_iff σ).2 hT))
end SpectralPlacementPrices
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
theorem rawWireDistance_triangle (hc : 0 ≤ c) (s t u : J) :
    rawWireDistance φ c s u ≤ rawWireDistance φ c s t + rawWireDistance φ c t u := by
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have h := rawLogPrice_move_le φ c hc W (diagonal_pair_ne_zero (Fin 2))
    ![s, t] ![s, u] 1 (by intro i hi; fin_cases i <;> simp_all)
  simpa [W, rawWireDistance, Raw.diagonal, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    using h
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
theorem rawWireDistance_le_group_diagonal [Field K] [Nonempty J]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    {c : ℝ} (hc : 0 ≤ c) (x : I → J) (i j : I) :
    rawWireDistance φ c (x i) (x j) ≤ rawLogPrice φ c ((Raw.diagonal I K (Fin 2)).group x) := by
  have hf : x ∘ ![i, j] = ![x i, x j] := by funext k; fin_cases k <;> rfl
  simpa only [rawWireDistance, hf] using
    rawLogPrice_mono φ hc (Raw.group_diagonal_restricts_of_comp x ![i, j] (Fin 2))
end SiteTensor
end
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
theorem ofRaw_one_le_of_nonzero (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    1 ≤ ofRaw X :=
  X.one_restricts_of_nonzero h
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
namespace SpectralPlacementPrices
open SiteTensor
variable {X K : Type*} [PseudoMetricSpace X] [Field K]
private noncomputable def representative_p2 (x : SeparationQuotient X) : X :=
  (SeparationQuotient.surjective_mk x).choose
private theorem mk_representative (x : SeparationQuotient X) :
    SeparationQuotient.mk (representative_p2 x) = x :=
  (SeparationQuotient.surjective_mk x).choose_spec
private theorem isometry_representative : Isometry (representative_p2 (X := X)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [← SeparationQuotient.dist_mk, mk_representative, mk_representative]
noncomputable def separationQuotient (P : SpectralPlacementPrices K X) :
    SpectralPlacementPrices K (SeparationQuotient X) :=
  P.pullback representative_p2 isometry_representative
theorem separationQuotient_price (P : SpectralPlacementPrices K X)
    {I : Type} [Fintype I] (T : Raw.{0} I K) (x : I → X) :
    P.separationQuotient.price T (SeparationQuotient.mk ∘ x) = P.price T x := by
  let y := representative_p2 ∘ SeparationQuotient.mk ∘ x
  have hdist (i : I) : dist (y i) (x i) = 0 := by
    change dist (representative_p2 _) _ = 0
    rw [← SeparationQuotient.dist_mk, mk_representative]
    exact dist_self _
  have h := P.transport T y x
  change P.price T y = P.price T x
  simpa [hdist] using h
end SpectralPlacementPrices
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
noncomputable section
open scoped NNReal
variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c)
def wirePseudoMetric : PseudoMetricSpace J where
  dist := rawWireDistance φ c
  dist_self := rawWireDistance_self φ c hc
  dist_comm := rawWireDistance_symm φ c
  dist_triangle := rawWireDistance_triangle φ c hc
def finitePlacementPrices : letI := wirePseudoMetric φ c hc; SpectralPlacementPrices K J := by
  letI := wirePseudoMetric φ c hc
  refine {
    price := fun T x => rawLogPrice φ c (T.group x)
    zero_tensor := fun T h x => rawLogPrice_zero φ c _ (by
      exact funext fun y => congrFun h _)
    collapsed := fun T s => rawLogPrice_const φ c hc T s
    group := fun T σ x => ?_
    wire := fun x => ?_
    transport := fun T x y => ?_
    dist_le_diagonal := fun x i j => rawWireDistance_le_group_diagonal φ hc x i j
    normalized := fun e => ?_
  }
  · unfold rawLogPrice
    rw [ofRaw_eq_iff.mpr (Raw.group_group_equivalent T σ x)]
  · show rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group x) =
      rawLogPrice φ c ((Raw.diagonal (Fin 2) K (Fin 2)).group ![x 0, x 1])
    have h : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
    rw [h]
  · rw [Real.dist_eq]
    exact rawLogPrice_transport φ c hc T x y
  · obtain ⟨ψ, hψ⟩ := rawLogPrice_group_embedding φ e c
    exact ⟨ψ, fun T _ => hψ T⟩
include hc in
theorem exists_metric_price_realization :
    ∃ (X : Type) (_ : MetricSpace X) (P : SpectralPlacementPrices K X) (ι : J → X),
      Function.Surjective ι ∧
      (∀ s t, dist (ι s) (ι t) = rawWireDistance φ c s t) ∧
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → J),
        P.price T (ι ∘ p) = rawLogPrice φ c (T.group p) := by
  let := wirePseudoMetric φ c hc
  let P := finitePlacementPrices φ c hc
  refine ⟨SeparationQuotient J, inferInstance, P.separationQuotient,
    SeparationQuotient.mk, SeparationQuotient.surjective_mk, SeparationQuotient.dist_mk, ?_⟩
  intro I _ T p
  exact P.separationQuotient_price T p
end
end SiteTensor
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open SiteTensor
variable {K : Type*} [Field K]
structure PriceEmbedding {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (P : SpectralPlacementPrices K X) (Q : SpectralPlacementPrices K Y) where
  map : X → Y
  isometry : Isometry map
  price {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → X) :
    Q.price T (map ∘ p) = P.price T p
namespace PriceEmbedding
variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z] {P : SpectralPlacementPrices K X} {Q : SpectralPlacementPrices K Y} {R : SpectralPlacementPrices K Z}
def refl (P : SpectralPlacementPrices K X) : PriceEmbedding P P :=
  ⟨id, isometry_id, fun _ _ ↦ rfl⟩
def trans (f : PriceEmbedding P Q) (g : PriceEmbedding Q R) : PriceEmbedding P R :=
  ⟨g.map ∘ f.map, g.isometry.comp f.isometry, fun T p ↦
    (g.price T (f.map ∘ p)).trans (f.price T p)⟩
end PriceEmbedding
def IsWireMidpoint {X : Type*} [PseudoMetricSpace X] (a b m : X) : Prop :=
  dist a m = dist a b / 2 ∧ dist b m = dist a b / 2
theorem IsWireMidpoint.map {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {a b m : X} (h : IsWireMidpoint a b m) {f : X → Y} (hf : Isometry f) :
    IsWireMidpoint (f a) (f b) (f m) := by
  simpa only [IsWireMidpoint, hf.dist_eq] using h
structure FinitePriceSpace (K : Type*) [Field K] where
  carrier : Type
  metric : MetricSpace carrier
  finite : Finite carrier
  prices : @SpectralPlacementPrices K _ carrier metric.toPseudoMetricSpace
instance instFinitePriceSpaceMetric {K : Type*} [Field K] (A : FinitePriceSpace K) : MetricSpace A.carrier := A.metric
instance instFinitePriceSpaceFinite {K : Type*} [Field K] (A : FinitePriceSpace K) : Finite A.carrier := A.finite
def HasFiniteMidpointExtensions (K : Type*) [Field K] : Prop :=
  ∀ (A : FinitePriceSpace K) (a b : A.carrier), ∃ (B : FinitePriceSpace K)
    (f : PriceEmbedding A.prices B.prices) (m : B.carrier), IsWireMidpoint (f.map a) (f.map b) m
private theorem insert_finite_midpoints (h : HasFiniteMidpointExtensions K) (A : FinitePriceSpace K)
    (s : Finset (A.carrier × A.carrier)) :
    ∃ (B : FinitePriceSpace K) (f : PriceEmbedding A.prices B.prices),
      ∀ p ∈ s, ∃ m, IsWireMidpoint (f.map p.1) (f.map p.2) m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨A, PriceEmbedding.refl _, by simp⟩
  | @insert p s _ ih =>
    obtain ⟨B, f, hs⟩ := ih
    obtain ⟨C, g, m, hm⟩ := h B (f.map p.1) (f.map p.2)
    refine ⟨C, f.trans g, fun q hq ↦ ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨m, hm⟩
    obtain ⟨n, hn⟩ := hs q hq
    exact ⟨g.map n, hn.map g.isometry⟩
theorem HasFiniteMidpointExtensions.all_pairs (h : HasFiniteMidpointExtensions K)
    (A : FinitePriceSpace K) :
    ∃ (B : FinitePriceSpace K) (f : PriceEmbedding A.prices B.prices),
      ∀ a b, ∃ m, IsWireMidpoint (f.map a) (f.map b) m := by
  classical
  let := Fintype.ofFinite A.carrier
  obtain ⟨B, f, hf⟩ := insert_finite_midpoints h A Finset.univ
  exact ⟨B, f, fun a b ↦ hf (a,b) (Finset.mem_univ _)⟩
structure MidpointTower (K : Type*) [Field K] where
  stage : ℕ → FinitePriceSpace K
  step n : PriceEmbedding (stage n).prices (stage (n + 1)).prices
  midpoint n (a b : (stage n).carrier) :
    ∃ m, IsWireMidpoint ((step n).map a) ((step n).map b) m
theorem HasFiniteMidpointExtensions.tower (h : HasFiniteMidpointExtensions K)
    (A : FinitePriceSpace K) :
    ∃ T : MidpointTower K, Nonempty (PriceEmbedding A.prices (T.stage 0).prices) := by
  classical
  choose next embed mid using h.all_pairs
  let stage : ℕ → FinitePriceSpace K := Nat.rec A (fun _ B ↦ next B)
  let T : MidpointTower K := ⟨stage, fun n ↦ embed (stage n), fun n ↦ mid (stage n)⟩
  exact ⟨T, ⟨PriceEmbedding.refl _⟩⟩
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SiteTensor
open scoped BigOperators NNReal Classical
universe v u w
variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [Field K]
def nonzeroClasses : Submonoid (TensorClass.{v} I K) where
  carrier := {t | t ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' := mul_ne_zero
abbrev NonzeroProduct := Additive (nonzeroClasses.{v} I K)
variable {I K}
theorem unit_le_nonzeroClass (x : nonzeroClasses.{v} I K) : 1 ≤ x.val :=
  one_le_of_ne_zero x.property
abbrev logPoint (f : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop)) :
    NonzeroProduct.{v} I K →+ ℝ := spectralLogHom unit_le_nonzeroClass f
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped NNReal
noncomputable section
namespace SiteTensor
variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]
/-- OpenAI's spectral interval lemma, as a hypothesis (step H1 of the parent reduction). -/
def IntervalProp : Prop :=
  ∀ {I' : Type} [Fintype I'] [Nonempty I'] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I' K → _ → Prop))
    (a b : I') (la lb : ℝ), 0 ≤ la → 0 ≤ lb → la + lb = rawWireDistance φ 1 a b →
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I') K → _ → Prop),
      (∀ T : Raw.{0} I' K, rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T) ∧
      rawWireDistance ψ 1 none (some a) = la ∧ rawWireDistance ψ 1 none (some b) = lb
theorem exists_midpoint_spectral_point (hint : IntervalProp (K := K))
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (a b : I) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop),
      (∀ T : Raw.{0} I K, rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T) ∧
      rawWireDistance ψ 1 none (some a) = rawWireDistance φ 1 a b / 2 ∧
      rawWireDistance ψ 1 none (some b) = rawWireDistance φ 1 a b / 2 := by
  have h : 0 ≤ rawWireDistance φ 1 a b := rawLogPrice_nonneg φ zero_le_one _
  exact hint φ a b _ _ (by positivity) (by positivity) (by ring)
end SiteTensor
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open SiteTensor
variable {K : Type*} [Field K]
theorem SpectralPlacementPrices.exists_finite_midpoint_extension
    (hint : SiteTensor.IntervalProp (K := K)) : HasFiniteMidpointExtensions K := by
  classical
  intro A a b
  by_cases hab : a = b
  · subst b
    exact ⟨A, PriceEmbedding.refl _, a, by simp [IsWireMidpoint, PriceEmbedding.refl]⟩
  have : Nontrivial A.carrier := ⟨⟨a, b, hab⟩⟩
  let := Fintype.ofFinite A.carrier
  let e := Function.Embedding.refl A.carrier
  let c := A.prices.price (Raw.diagonal A.carrier K (Fin 2)) e
  obtain ⟨φ, hc, normalized⟩ := A.prices.normalized_group e
  obtain ⟨ψ, old, hma, hmb⟩ := exists_midpoint_spectral_point hint φ a b
  obtain ⟨Y, met, Q, j, hj, hDist, hPrice⟩ := exists_metric_price_realization ψ c hc.le
  let B : FinitePriceSpace K := ⟨Y, met, Finite.of_surjective j hj, Q⟩
  let f := j ∘ some
  have hprice {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → A.carrier) :
      Q.price T (f ∘ p) = A.prices.price T p := by
    by_cases hT : T.coeff = 0
    · exact (Q.zero_tensor T hT _).trans (A.prices.zero_tensor T hT _).symm
    change Q.price T (j ∘ (some ∘ p)) = _
    rw [hPrice, show A.prices.price T p = _ from normalized p T hT]
    have heq := ofRaw_eq_iff.mpr (Raw.group_group_equivalent T p (some : A.carrier → Option _))
    have hg := old (T.group p)
    simp only [rawLogPrice, one_mul, heq] at hg
    change c * Real.logb 2 (ψ.val _) = c * Real.logb 2 (φ.val _)
    exact congrArg (c * ·) hg
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    have h := hprice (Raw.diagonal (Fin 2) K (Fin 2)) ![x,y]
    simpa [Q.wire, A.prices.wire] using h
  let emb : PriceEmbedding A.prices B.prices := ⟨f, hf, hprice⟩
  have oldDist : dist a b = c * rawWireDistance φ 1 a b := by
    let W := Raw.diagonal (Fin 2) K (Fin 2)
    have hn : W.coeff ≠ 0 := by
      intro hz
      have h := (A.prices.zero_tensor W hz ![a,b])
      rw [show A.prices.price W ![a,b] = dist a b from A.prices.wire _] at h
      exact hab (dist_eq_zero.mp h)
    have h := normalized ![a, b] W hn
    change A.prices.price W ![a,b] = _ at h
    simpa only [W, A.prices.wire, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, rawWireDistance, rawLogPrice, one_mul] using h
  have halfway (s : A.carrier)
      (hs : rawWireDistance ψ 1 none (some s) = rawWireDistance φ 1 a b / 2) :
      dist (f s) (j none) = dist a b / 2 := by
    change dist (j (some s)) (j none) = _
    rw [dist_comm, hDist, oldDist]
    have hp : rawWireDistance ψ c none (some s) = c * rawWireDistance ψ 1 none (some s) := by
      simp [rawWireDistance, rawLogPrice]
    rw [hp, hs]
    ring
  exact ⟨B, emb, j none, by
    change dist (f a) (j none) = dist (f a) (f b) / 2 ∧
      dist (f b) (j none) = dist (f a) (f b) / 2
    rw [hf.dist_eq]
    exact ⟨halfway _ hma, halfway _ hmb⟩⟩
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace DyadicSegment
variable {X : Type*}
def grid (mid : X → X → X) (x y : X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then grid mid x y n (k / 2)
    else mid (grid mid x y n (k / 2)) (grid mid x y n (k / 2 + 1))
theorem grid_even (mid : X → X → X) (x y : X) (n k : ℕ) :
    grid mid x y (n + 1) (2 * k) = grid mid x y n k := by
  simp [grid]
theorem grid_odd (mid : X → X → X) (x y : X) (n k : ℕ) :
    grid mid x y (n + 1) (2 * k + 1) =
      mid (grid mid x y n k) (grid mid x y n (k + 1)) := by
  simp [grid, show (2 * k + 1) / 2 = k by omega,
    show (2 * k + 1) % 2 = 1 by omega]
theorem grid_zero (mid : X → X → X) (x y : X) (n : ℕ) :
    grid mid x y n 0 = x := by
  induction n with
  | zero => simp [grid]
  | succ n ih => simpa using (grid_even mid x y n 0).trans ih
theorem grid_last (mid : X → X → X) (x y : X) (n : ℕ) :
    grid mid x y n (2 ^ n) = y := by
  induction n with
  | zero => simp [grid]
  | succ n ih => rwa [pow_succ', grid_even]
variable [MetricSpace X]
theorem grid_adjacent (mid : X → X → X)
    (hm : ∀ a b, dist a (mid a b) = dist a b / 2 ∧ dist (mid a b) b = dist a b / 2)
    (x y : X) (n k : ℕ) (hk : k < 2 ^ n) :
    dist (grid mid x y n k) (grid mid x y n (k + 1)) = dist x y / 2 ^ n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa using hk
    simp [this, grid]
  | succ n ih =>
    rw [pow_succ'] at hk
    let j := k / 2
    have hj : j < 2 ^ n := by dsimp [j]; omega
    have cases : k = 2 * j ∨ k = 2 * j + 1 := by dsimp [j]; omega
    have half : dist x y / 2 ^ n / 2 = dist x y / 2 ^ (n + 1) := by
      rw [pow_succ, div_div]
    rcases cases with he | ho
    · rw [he, grid_even, grid_odd, (hm _ _).1, ih _ hj, half]
    · rw [ho, show 2 * j + 1 + 1 = 2 * (j + 1) by omega,
        grid_odd, grid_even, (hm _ _).2, ih _ hj, half]
private theorem chain_dist_le (p : ℕ → X) (N : ℕ) (δ : ℝ)
    (h : ∀ k < N, dist (p k) (p (k + 1)) ≤ δ) (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ N) :
    dist (p k) (p l) ≤ ((l : ℝ) - k) * δ := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hkl ih =>
    have h₁ := ih (by omega)
    have h₂ := h l (by omega)
    have h₃ := dist_triangle (p k) (p l) (p (l + 1))
    push_cast
    linarith
theorem grid_dist (mid : X → X → X)
    (hm : ∀ a b, dist a (mid a b) = dist a b / 2 ∧ dist (mid a b) b = dist a b / 2)
    (x y : X) (n k l : ℕ) (hkl : k ≤ l) (hl : l ≤ 2 ^ n) :
    dist (grid mid x y n k) (grid mid x y n l) = ((l : ℝ) - k) / 2 ^ n * dist x y := by
  let p := grid mid x y n
  let N := 2 ^ n
  let δ := dist x y / 2 ^ n
  have bound := chain_dist_le p N δ (fun i hi => (grid_adjacent mid hm x y n i hi).le)
  have full : (N : ℝ) * δ = dist x y := by
    dsimp [N, δ]
    push_cast
    field_simp
  have ends : dist (p 0) (p N) = dist x y := by
    simp only [p, N, grid_zero, grid_last]
  have h₁ := bound 0 k (Nat.zero_le _) (hkl.trans hl)
  have h₂ := bound l N hl le_rfl
  have h₃ := dist_triangle (p 0) (p k) (p N)
  have h₄ := dist_triangle (p k) (p l) (p N)
  rw [ends] at h₃
  simp only [Nat.cast_zero, sub_zero] at h₁
  change dist (p k) (p l) = _
  rw [show ((l : ℝ) - k) / 2 ^ n * dist x y = ((l : ℝ) - k) * δ by dsimp [δ]; ring]
  exact le_antisymm (bound k l hkl hl) (by linarith)
end DyadicSegment
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open Filter Topology
namespace DyadicSegment
def index (n : ℕ) (t : ℝ) : ℕ := ⌊(2 : ℝ) ^ n * t⌋₊
@[simp] theorem index_zero (n : ℕ) : index n 0 = 0 := by simp [index]
@[simp] theorem index_one (n : ℕ) : index n 1 = 2 ^ n := by
  simp only [index, mul_one]
  exact_mod_cast Nat.floor_natCast (R := ℝ) (2 ^ n)
theorem index_mono (n : ℕ) : Monotone (index n) :=
  fun _ _ h ↦ Nat.floor_mono (mul_le_mul_of_nonneg_left h (by positivity))
theorem index_le (n : ℕ) {t : ℝ} (ht : t ≤ 1) : index n t ≤ 2 ^ n := by
  simpa using index_mono n ht
theorem index_refine (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    index (n + 1) t = 2 * index n t ∨ index (n + 1) t = 2 * index n t + 1 := by
  have hfloor : (index n t : ℝ) ≤ 2 ^ n * t := Nat.floor_le (by positivity)
  have hsucc : 2 ^ n * t < (index n t : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : 2 * index n t ≤ index (n + 1) t := by
    apply Nat.le_floor
    push_cast
    rw [pow_succ]
    linarith
  have hhi : index (n + 1) t < 2 * index n t + 2 := by
    apply (Nat.floor_lt (by positivity)).2
    push_cast
    rw [pow_succ]
    linarith
  omega
theorem tendsto_index_div {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ (index n t : ℝ) / 2 ^ n) atTop (𝓝 t) := by
  have hmesh : Tendsto (fun n : ℕ ↦ 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using (tendsto_const_nhds (x := t)).sub hmesh) tendsto_const_nhds
  · intro n
    have h := Nat.lt_floor_add_one ((2 : ℝ) ^ n * t)
    change (2 : ℝ) ^ n * t < (index n t : ℝ) + 1 at h
    change t - 1 / 2 ^ n ≤ (index n t : ℝ) / 2 ^ n
    rw [le_div_iff₀ (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity)]
    linarith
  · intro n
    apply (div_le_iff₀ (by positivity)).2
    rw [mul_comm]
    exact Nat.floor_le (by positivity)
end DyadicSegment
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Topology DyadicSegment
theorem isGeodesic_of_exactMidpoints {X : Type*} [MetricSpace X] [CompleteSpace X]
    (mid : X → X → X)
    (hm : ∀ a b, dist a (mid a b) = dist a b / 2 ∧ dist (mid a b) b = dist a b / 2) :
    HyperbolicObstruction.IsGeodesic X := by
  intro x y
  let : Nonempty X := ⟨x⟩
  let p (t : ℝ) (n : ℕ) := grid mid x y n (index n t)
  let γ (t : ℝ) := limUnder atTop (p t)
  have hlim (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Tendsto (p t) atTop (𝓝 (γ t)) := by
    apply CauchySeq.tendsto_limUnder
    apply cauchySeq_of_le_geometric_two (C := dist x y)
    intro n
    change dist (grid mid x y n (index n t)) (grid mid x y (n + 1) (index (n + 1) t)) ≤ _
    rw [← grid_even mid x y n (index n t)]
    rcases index_refine n ht.1 with he | ho
    · rw [he, dist_self]
      positivity
    · have h := index_le (n + 1) ht.2
      rw [ho] at h ⊢
      rw [grid_dist mid hm x y (n + 1) _ _ (by omega) h]
      push_cast
      rw [pow_succ]
      apply le_of_eq
      ring
  have hdist {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
      (hst : s ≤ t) : dist (γ s) (γ t) = (t - s) * dist x y := by
    apply tendsto_nhds_unique ((hlim s hs).dist (hlim t ht))
    apply (((tendsto_index_div ht.1).sub (tendsto_index_div hs.1)).mul_const (dist x y)).congr'
    apply Eventually.of_forall
    intro n
    dsimp only [p]
    rw [grid_dist mid hm x y n _ _ (index_mono n hst) (index_le n ht.2), sub_div]
  refine ⟨γ, ?_, ?_, ?_⟩
  · apply tendsto_nhds_unique (hlim 0 (by constructor <;> norm_num))
    simp [p, grid_zero]
  · apply tendsto_nhds_unique (hlim 1 (by constructor <;> norm_num))
    simp [p, grid_last]
  · intro s hs t ht
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
      exact hdist hs ht hst
    · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
      exact hdist ht hs hts
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Topology HyperbolicObstruction MetricLimit
theorem completeSpace_metricLimit {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n} :
    CompleteSpace (Space (U := U) (X := X) (o := o)) := by
  classical
  let b (j : ℕ) : ℝ := 1 / (j + 1)
  have hb (j : ℕ) : 0 < b j := by dsimp [b]; positivity
  apply Metric.complete_of_convergent_controlled_sequences b hb
  intro q hq
  choose r hr using fun j ↦ SeparationQuotient.surjective_mk (q j)
  have hd (i j : ℕ) (hij : i ≤ j) :
      ∀ᶠ n in (U : Filter ℕ), dist ((r i).val n) ((r j).val n) ≤ 2 * b i := by
    have h := tendsto_point_dist (r i) (r j)
    change Tendsto _ _ (𝓝 (dist (SeparationQuotient.mk (r i)) (SeparationQuotient.mk (r j)))) at h
    rw [hr, hr] at h
    exact (h.eventually_lt_const (by linarith [hq i i j le_rfl hij, hb i])).mono
      (fun _ ↦ le_of_lt)
  let Good (n k : ℕ) : Prop := ∀ i ∈ Finset.range (k+1), ∀ j ∈ Finset.range (k+1),
    i ≤ j → dist ((r i).val n) ((r j).val n) ≤ 2 * b i
  have hevent (k : ℕ) : ∀ᶠ n in (U : Filter ℕ), Good n k := by
    apply (Finset.eventually_all _).2
    intro i _
    apply (Finset.eventually_all _).2
    intro j _
    by_cases hij : i ≤ j
    · exact (hd i j hij).mono (fun _ hn _ ↦ hn)
    · exact Eventually.of_forall (fun _ h ↦ (hij h).elim)
  let diag (n : ℕ) := Nat.findGreatest (Good n) n
  have hg (n : ℕ) : Good n (diag n) := by
    apply Nat.findGreatest_spec (Nat.zero_le _)
    simp [Good, mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (hb 0).le]
  have hdiag (i : ℕ) : ∀ᶠ n in (U : Filter ℕ), i ≤ diag n := by
    filter_upwards [hU (eventually_ge_atTop i), hevent i] with n hin hgood
    exact Nat.le_findGreatest hin hgood
  obtain ⟨R, hR⟩ := (r 0).bound
  let x : Bounded U X o := ⟨fun n ↦ (r (diag n)).val n, R + 2 * b 0, fun n ↦
    (dist_triangle _ ((r 0).val n) _).trans (add_le_add (hR n)
      (hg n 0 (by simp) (diag n) (by simp) (Nat.zero_le _)))⟩
  have hclose (i : ℕ) : dist (q i) (point x) ≤ 2 * b i := by
    rw [← hr i]
    apply le_of_tendsto (tendsto_point_dist (r i) x)
    filter_upwards [hdiag i] with n hn
    exact hg n i (Finset.mem_range.mpr (by omega)) (diag n) (by simp) hn
  refine ⟨point x, Metric.tendsto_nhds.mpr (fun ε hε ↦ ?_)⟩
  have hlim : Tendsto (fun n ↦ 2 * b n) atTop (𝓝 0) := by
    simpa [b] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  exact (hlim.eventually_lt_const hε).mono (fun i hi ↦ (hclose i).trans_lt hi)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open Filter Topology HyperbolicObstruction MetricLimit
universe u v
variable {U : Ultrafilter ℕ} {X : ℕ → Type u} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}
variable {A : Type v} [Fintype A]
private def sectionCost (w : A → ℝ) (p q : A → Bounded U X o) (n : ℕ) : ℝ :=
  ∑ a, dist ((p a).val n) ((q a).val n) * w a
private theorem tendsto_sectionCost (w : A → ℝ) (p q : A → Bounded U X o) :
    Tendsto (sectionCost w p q) (U : Filter ℕ)
      (𝓝 (∑ a, dist (point (p a)) (point (q a)) * w a)) :=
  tendsto_finsetSum _ (fun a _ ↦ (tendsto_point_dist (p a) (q a)).mul_const (w a))
private def sectionPrice (H : (n : ℕ) → (A → X n) → ℝ) (p : A → Bounded U X o) : ℝ :=
  limUnder (U : Filter ℕ) (fun n ↦ H n (fun a ↦ (p a).val n))
private theorem tendsto_sectionPrice (w : A → ℝ) (H : (n : ℕ) → (A → X n) → ℝ)
    (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a)
    (p : A → Bounded U X o) :
    Tendsto (fun n ↦ H n (fun a ↦ (p a).val n)) (U : Filter ℕ) (𝓝 (sectionPrice H p)) := by
  let base : Bounded U X o := ⟨o, 0, by simp⟩
  let B := (∑ a, dist (point (p a)) (point base) * w a) + 1
  have hb : ∀ᶠ n in (U : Filter ℕ), sectionCost w p (fun _ ↦ base) n < B :=
    (tendsto_sectionCost w p (fun _ ↦ base)).eventually_lt_const (lt_add_one _)
  let f (n : ℕ) := H n (fun a ↦ (p a).val n)
  have hm : Metric.closedBall (0 : ℝ) B ∈ U.map f := by
    apply hb.mono
    intro n hn
    have h := hmove n (fun a ↦ (p a).val n) (fun _ ↦ o n)
    rw [hzero] at h
    exact h.trans hn.le
  obtain ⟨_, _, ht⟩ := (isCompact_closedBall (0 : ℝ) B).ultrafilter_le_nhds' _ hm
  exact tendsto_nhds_limUnder ⟨_, ht⟩
private theorem dist_sectionPrice_le (w : A → ℝ) (H : (n : ℕ) → (A → X n) → ℝ)
    (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a)
    (p q : A → Bounded U X o) :
    dist (sectionPrice H p) (sectionPrice H q) ≤ ∑ a, dist (point (p a)) (point (q a)) * w a :=
  le_of_tendsto_of_tendsto' ((tendsto_sectionPrice w H hzero hmove p).dist
    (tendsto_sectionPrice w H hzero hmove q)) (tendsto_sectionCost w p q)
    (fun n ↦ hmove n _ _)
private def representative_p1 (x : Space (U := U) (X := X) (o := o)) : Bounded U X o :=
  (SeparationQuotient.surjective_mk x).choose
private theorem point_representative (x : Space (U := U) (X := X) (o := o)) :
    point (representative_p1 x) = x := (SeparationQuotient.surjective_mk x).choose_spec
def metricLimitPrice (H : (n : ℕ) → (A → X n) → ℝ)
    (q : A → Space (U := U) (X := X) (o := o)) : ℝ :=
  sectionPrice H (representative_p1 ∘ q)
theorem tendsto_metricLimitPrice (w : A → ℝ) (H : (n : ℕ) → (A → X n) → ℝ)
    (hzero : ∀ n (x : X n), H n (fun _ ↦ x) = 0)
    (hmove : ∀ n p q, dist (H n p) (H n q) ≤ ∑ a, dist (p a) (q a) * w a)
    (p : A → Bounded U X o) :
    Tendsto (fun n ↦ H n (fun a ↦ (p a).val n)) (U : Filter ℕ)
      (𝓝 (metricLimitPrice H (point ∘ p))) := by
  have h := dist_sectionPrice_le w H hzero hmove p (representative_p1 ∘ point ∘ p)
  simp only [Function.comp_apply, point_representative, dist_self, zero_mul, Finset.sum_const_zero,
    dist_le_zero] at h
  rw [metricLimitPrice, ← h]
  exact tendsto_sectionPrice w H hzero hmove p
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Topology HyperbolicObstruction
noncomputable def blowupPriceFamily {I Y A : Type*} {X : I → Type*} (u : Ultrafilter I) (scale : I → ℝ)
    (point : ∀ i, Y → X i) (price : ∀ i, (A → X i) → ℝ) (x : A → Y) : ℝ :=
  limUnder (u : Filter I) (fun i => price i (point i ∘ x) / scale i)
theorem blowupPriceFamily_spec {I Y A : Type*} {X : I → Type*} [∀ i, PseudoMetricSpace (X i)] [PseudoMetricSpace Y]
    [Fintype A] (u : Ultrafilter I) (scale : I → ℝ) (hs : ∀ i, 0 < scale i)
    (point : ∀ i, Y → X i) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter I) (𝓝 (dist p q)))
    (w : A → ℝ) (price : ∀ i, (A → X i) → ℝ)
    (hzero : ∀ i (p : X i), price i (fun _ => p) = 0)
    (htransport : ∀ i x y, dist (price i x) (price i y) ≤ ∑ a, dist (x a) (y a) * w a) :
    (∀ x : A → Y, Tendsto (fun i => price i (point i ∘ x) / scale i)
      (u : Filter I) (𝓝 (blowupPriceFamily u scale point price x))) ∧
    (∀ y : Y, blowupPriceFamily u scale point price (fun _ => y) = 0) ∧
    ∀ x y : A → Y, dist (blowupPriceFamily u scale point price x) (blowupPriceFamily u scale point price y)
      ≤ ∑ a, dist (x a) (y a) * w a := by
  let v (x : A → Y) (i : I) := price i (point i ∘ x) / scale i
  let cost (x y : A → Y) (i : I) := ∑ a, (dist (point i (x a)) (point i (y a)) / scale i) * w a
  have hcost (x y : A → Y) : Tendsto (cost x y) (u : Filter I) (𝓝 (∑ a, dist (x a) (y a) * w a)) :=
    tendsto_finsetSum _ (fun a _ => (hdist (x a) (y a)).mul_const (w a))
  have hle (x y : A → Y) (i : I) : dist (v x i) (v y i) ≤ cost x y i := by
    have hh := div_le_div_of_nonneg_right (htransport i (point i ∘ x) (point i ∘ y)) (hs i).le
    simp only [v, cost, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hs i)]
    simpa only [Real.dist_eq, Finset.sum_div, div_mul_eq_mul_div, Function.comp_apply] using hh
  have hconstant (y : Y) (i : I) : v (fun _ => y) i = 0 := by
    change price i (fun _ => point i y) / scale i = 0
    rw [hzero, zero_div]
  have hlim (x : A → Y) : Tendsto (v x) (u : Filter I) (𝓝 (blowupPriceFamily u scale point price x)) := by
    let c : A → Y := fun _ => y₀
    let B := (∑ a, dist (x a) (c a) * w a) + 1
    have hB : ∀ᶠ i in (u : Filter I), cost x c i < B :=
      (hcost x c).eventually (gt_mem_nhds (lt_add_one _))
    have hmem : Metric.closedBall (0 : ℝ) B ∈ u.map (v x) := by
      apply hB.mono
      intro i hi
      have h := hle x c i
      rw [show v c i = 0 from hconstant y₀ i] at h
      exact h.trans hi.le
    obtain ⟨a, _, ha⟩ := (isCompact_closedBall (0 : ℝ) B).ultrafilter_le_nhds' _ hmem
    exact tendsto_nhds_limUnder ⟨a, ha⟩
  refine ⟨hlim, fun y => tendsto_nhds_unique (hlim _)
    (tendsto_const_nhds.congr fun i => (hconstant y i).symm), ?_⟩
  exact fun x y => le_of_tendsto_of_tendsto ((hlim x).dist (hlim y)) (hcost x y)
    (Eventually.of_forall (hle x y))
theorem blowupPriceFamily_reindex {I Y A B : Type*} {X : I → Type*} (u : Ultrafilter I) (scale : I → ℝ)
    (point : ∀ i, Y → X i) (e : A → B) (P : ∀ i, (A → X i) → ℝ) (Q : ∀ i, (B → X i) → ℝ)
    (he : ∀ i (x : B → X i), P i (x ∘ e) = Q i x) (y : B → Y) :
    blowupPriceFamily u scale point P (y ∘ e) = blowupPriceFamily u scale point Q y := by
  unfold blowupPriceFamily
  congr 1
  funext i
  rw [← he i (point i ∘ y)]
  rfl
theorem blowupPriceFamily_wire {I Y : Type*} {X : I → Type*} [∀ i, PseudoMetricSpace (X i)] [PseudoMetricSpace Y]
    (u : Ultrafilter I) (scale : I → ℝ) (point : ∀ i, Y → X i)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter I) (𝓝 (dist p q))) (x : Fin 2 → Y) :
    blowupPriceFamily u scale point (fun i (z : Fin 2 → X i) => dist (z 0) (z 1)) x = dist (x 0) (x 1) :=
  (hdist (x 0) (x 1)).limUnder_eq
theorem normalizedSpectralPrice_limit {I S R : Type*} [Semiring S]
    (restricts : S → S → Prop) (hrank : ∀ x, ∃ n : ℕ, restricts x n)
    (u : Ultrafilter I) (φ : I → normalizedSpectrum restricts) {c : I → ℝ} {d : ℝ}
    (hc : Tendsto c (u : Filter I) (𝓝 d)) (tensor : R → S) (hunit : ∀ t, restricts 1 (tensor t))
    (price : R → ℝ)
    (hprice : ∀ x, Tendsto (fun i => c i * Real.logb 2 ((φ i).val (tensor x) : ℝ))
      (u : Filter I) (𝓝 (price x))) :
    ∃ ψ : normalizedSpectrum restricts, ∀ x, price x = d * Real.logb 2 (ψ.val (tensor x) : ℝ) := by
  let : CompactSpace (normalizedSpectrum restricts) :=
    isCompact_iff_compactSpace.mp (isCompact_normalizedSpectrum restricts hrank)
  obtain ⟨ψ, _, hψ⟩ := isCompact_univ.ultrafilter_le_nhds' (u.map φ) (show Set.univ ∈ u.map φ from Filter.univ_mem)
  have hφ : Tendsto φ (u : Filter I) (𝓝 ψ) := hψ
  exact ⟨ψ, fun x => tendsto_nhds_unique (hprice x)
    (hc.mul (((continuous_log_price (hunit x)).tendsto ψ).comp hφ))⟩
theorem eventually_injOn_of_rescaled_dist {I Y : Type*} {X : I → Type*} [∀ i, PseudoMetricSpace (X i)] [MetricSpace Y]
    (l : Filter I) (scale : I → ℝ) (point : ∀ i, Y → X i)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      l (𝓝 (dist p q))) (s : Finset Y) :
    ∀ᶠ i in l, Set.InjOn (point i) s := by
  have hev (p q : Y) : ∀ᶠ i in l, point i p = point i q → p = q := by
    by_cases hpq : p = q
    · exact Eventually.of_forall fun _ _ => hpq
    · filter_upwards [(hdist p q).eventually (lt_mem_nhds (dist_pos.mpr hpq))] with i hi he
      simp [he] at hi
  filter_upwards [(s.eventually_all).2 fun p _ => (s.eventually_all).2 fun q _ => hev p q]
    with i hi
  exact fun p hp q hq => hi p hp q hq
theorem blowupPriceFamily_spectral {I Y A S R : Type*} {X : I → Type*}
    [∀ i, PseudoMetricSpace (X i)] [MetricSpace Y] [Fintype A] [Semiring S]
    (restricts : S → S → Prop) (hrank : ∀ x, ∃ n : ℕ, restricts x n)
    (u : Ultrafilter I) (scale : I → ℝ) (point : ∀ i, Y → X i)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter I) (𝓝 (dist p q)))
    (tensor : R → S) (hunit : ∀ t, restricts 1 (tensor t))
    (δ : ∀ i, (A → X i) → ℝ) (price : R → ∀ i, (A → X i) → ℝ)
    (hnormal : ∀ i (x : A → X i), Function.Injective x → ∃ φ : normalizedSpectrum restricts,
      ∀ t, price t i x = δ i x * Real.logb 2 (φ.val (tensor t) : ℝ))
    (p : A → Y) (hp : Function.Injective p)
    (hδ : Tendsto (fun i => δ i (point i ∘ p) / scale i) (u : Filter I)
      (𝓝 (blowupPriceFamily u scale point δ p)))
    (hprice : ∀ t, Tendsto (fun i => price t i (point i ∘ p) / scale i)
      (u : Filter I) (𝓝 (blowupPriceFamily u scale point (price t) p))) :
    ∃ ψ : normalizedSpectrum restricts, ∀ t,
      blowupPriceFamily u scale point (price t) p = blowupPriceFamily u scale point δ p * Real.logb 2 (ψ.val (tensor t) : ℝ) := by
  classical
  let valid (i : I) (φ : normalizedSpectrum restricts) :=
    ∀ t, price t i (point i ∘ p) = δ i (point i ∘ p) * Real.logb 2 (φ.val (tensor t) : ℝ)
  have hvalid : ∀ᶠ i in (u : Filter I), ∃ φ, valid i φ := by
    filter_upwards [eventually_injOn_of_rescaled_dist (u : Filter I) scale point hdist
      (Finset.univ.image p)] with i hi
    apply hnormal
    intro a b he
    exact hp (hi (Finset.mem_image_of_mem p (Finset.mem_univ a))
      (Finset.mem_image_of_mem p (Finset.mem_univ b)) he)
  obtain ⟨_, φ₀, _⟩ := hvalid.exists
  let φ (i : I) := if h : ∃ φ, valid i φ then h.choose else φ₀
  have he : ∀ᶠ i in (u : Filter I), valid i (φ i) := hvalid.mono fun i hi => by
    simpa only [φ, dite_eq_left hi] using hi.choose_spec
  apply normalizedSpectralPrice_limit restricts hrank u φ hδ tensor hunit
  intro t
  apply (hprice t).congr'
  filter_upwards [he] with i hi
  rw [hi t]
  ring
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SpectralPlacementPrices
open Filter Topology HyperbolicObstruction SiteTensor
variable {K X Y L : Type*} [Field K] [PseudoMetricSpace X] [MetricSpace Y]
def blowupFamily {Z : L → Type*} [∀ i, PseudoMetricSpace (Z i)]
    (H : ∀ i, SpectralPlacementPrices K (Z i))
    (u : Ultrafilter L) (scale : L → ℝ) (hs : ∀ i, 0 < scale i)
    (point : ∀ i, Y → Z i) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter L) (𝓝 (dist p q))) :
    SpectralPlacementPrices K Y := by
  have spec {I : Type} [Fintype I] (T : Raw.{0} I K) :=
    blowupPriceFamily_spec u scale hs point y₀ hdist _ (fun i => (H i).price T)
      (fun i => (H i).collapsed T) (fun i => (H i).transport T)
  refine {
    price := fun T => blowupPriceFamily u scale point (fun i => (H i).price T)
    zero_tensor := ?_
    collapsed := fun T => (spec T).2.1
    group := fun T σ => blowupPriceFamily_reindex u scale point σ _ _ (fun i => (H i).group T σ)
    wire := ?_
    transport := fun T => (spec T).2.2
    dist_le_diagonal := ?_
    normalized := ?_ }
  · intro I _ T h x
    apply tendsto_nhds_unique ((spec T).1 x)
    simpa only [fun i => (H i).zero_tensor T h, zero_div] using
      (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto _ (u : Filter L) _)
  · intro x
    rw [show (fun i => (H i).price (Raw.diagonal (Fin 2) K (Fin 2))) =
        (fun i (y : Fin 2 → Z i) => dist (y 0) (y 1)) from
      funext fun i => funext (H i).wire]
    exact blowupPriceFamily_wire u scale point hdist x
  · intro I _ x a b
    apply le_of_tendsto_of_tendsto (hdist (x a) (x b)) ((spec _).1 x)
    exact Eventually.of_forall fun i => div_le_div_of_nonneg_right
      ((H i).dist_le_diagonal (point i ∘ x) a b) (hs i).le
  · intro I _ _ x
    let R := {T : Raw.{0} I K // T.coeff ≠ 0}
    obtain ⟨ψ, hψ⟩ := blowupPriceFamily_spectral (fun a b : TensorClass.{0} I K => a ≤ b) exists_le_natCast
      u scale point hdist (fun T : R => ofRaw T.val)
      (fun T => ofRaw_one_le_of_nonzero T.val T.prop)
      (fun i => (H i).price (Raw.diagonal I K (Fin 2))) (fun (T : R) i => (H i).price T.val)
      (fun i x hx => by
        obtain ⟨φ, hφ⟩ := (H i).normalized ⟨x, hx⟩
        exact ⟨φ, fun T => hφ T.val T.prop⟩)
      x x.injective ((spec _).1 x) (fun T => (spec T.val).1 x)
    exact ⟨ψ, fun T hT => hψ ⟨T, hT⟩⟩
def blowup (H : SpectralPlacementPrices K X)
    (u : Ultrafilter L) (scale : L → ℝ) (hs : ∀ i, 0 < scale i)
    (point : L → Y → X) (y₀ : Y)
    (hdist : ∀ p q, Tendsto (fun i => dist (point i p) (point i q) / scale i)
      (u : Filter L) (𝓝 (dist p q))) :
    SpectralPlacementPrices K Y :=
  blowupFamily (fun _ => H) u scale hs point y₀ hdist
end SpectralPlacementPrices
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace SpectralPlacementPrices
open Filter Topology HyperbolicObstruction MetricLimit SiteTensor
variable {K : Type*} [Field K] {X : ℕ → Type*} [∀ n, MetricSpace (X n)] {o : ∀ n, X n}
private def rep_p0 {U : Ultrafilter ℕ} (x : Space (U := U) (X := X) (o := o)) : Bounded U X o :=
  (SeparationQuotient.surjective_mk x).choose
private theorem point_rep_p0 {U : Ultrafilter ℕ} (x : Space (U := U) (X := X) (o := o)) :
    point (rep_p0 x) = x := (SeparationQuotient.surjective_mk x).choose_spec
def metricLimit (U : Ultrafilter ℕ) (P : ∀ n, SpectralPlacementPrices K (X n)) :
    SpectralPlacementPrices K (Space (U := U) (X := X) (o := o)) :=
  blowupFamily P U (fun _ ↦ 1) (fun _ ↦ zero_lt_one) (fun n x ↦ (rep_p0 x).val n)
    (point (⟨o, 0, by simp⟩ : Bounded U X o))
    (fun x y ↦ by simpa only [div_one, point_rep_p0] using tendsto_point_dist (rep_p0 x) (rep_p0 y))
theorem metricLimit_price_tendsto (U : Ultrafilter ℕ) (P : ∀ n, SpectralPlacementPrices K (X n))
    {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → Bounded U X o) :
    Tendsto (fun n ↦ (P n).price T (fun i ↦ (p i).val n)) (U : Filter ℕ)
      (𝓝 ((metricLimit U P).price T (point ∘ p))) := by
  change Tendsto _ _ (𝓝 (limUnder (U : Filter ℕ)
    (fun n ↦ (P n).price T (fun i ↦ (rep_p0 (point (p i))).val n) / 1)))
  simp only [div_one]
  exact tendsto_metricLimitPrice _ _ (fun n ↦ (P n).collapsed T) (fun n ↦ (P n).transport T) p
end SpectralPlacementPrices
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open Filter Topology HyperbolicObstruction MetricLimit
universe u
variable {X : Type u} [MetricSpace X]
private theorem metricLimit_has_midpoints (U : Ultrafilter ℕ) (o : X)
    (hm : ∀ a b : X, ∃ m, IsWireMidpoint a b m) :
    ∀ a b : Space (U := U) (X := fun _ ↦ X) (o := fun _ ↦ o), ∃ m, IsWireMidpoint a b m := by
  intro a b
  obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk b
  choose v hv using fun n ↦ hm (a.val n) (b.val n)
  obtain ⟨R, hR⟩ := a.bound
  obtain ⟨D, hD⟩ := bounded_dist a b
  let m : Bounded U (fun _ ↦ X) (fun _ ↦ o) := ⟨v, R + D / 2, fun n ↦ by
    have ht := dist_triangle o (a.val n) (v n)
    rw [(hv n).1] at ht
    linarith [hR n, (hD n).2]⟩
  refine ⟨point m, ?_, ?_⟩
  · apply tendsto_nhds_unique (tendsto_point_dist a m)
    apply ((tendsto_point_dist a b).div_const 2).congr'
    exact Eventually.of_forall fun n ↦ (hv n).1.symm
  · apply tendsto_nhds_unique (tendsto_point_dist b m)
    apply ((tendsto_point_dist a b).div_const 2).congr'
    exact Eventually.of_forall fun n ↦ (hv n).2.symm
theorem exists_complete_geodesic_price_extension {K : Type*} [Field K]
    (P : SpectralPlacementPrices K X) (o : X) (hmid : ∀ a b : X, ∃ m, IsWireMidpoint a b m) :
    ∃ (Y : Type u) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding P Q) ∧ CompleteSpace Y ∧ IsGeodesic Y := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let Y := Space (U := U) (X := fun _ ↦ X) (o := fun _ ↦ o)
  let c (x : X) : Bounded U (fun _ ↦ X) (fun _ ↦ o) := ⟨fun _ ↦ x, dist o x, fun _ ↦ le_rfl⟩
  let Q : SpectralPlacementPrices K Y := SpectralPlacementPrices.metricLimit U (fun _ ↦ P)
  let f : PriceEmbedding P Q := {
    map := point ∘ c
    isometry := Isometry.of_dist_eq fun x y ↦ tendsto_nhds_unique
      (tendsto_point_dist (c x) (c y)) tendsto_const_nhds
    price := fun T p ↦ tendsto_nhds_unique
      (SpectralPlacementPrices.metricLimit_price_tendsto U (fun _ ↦ P) T (c ∘ p)) tendsto_const_nhds }
  let : CompleteSpace Y := completeSpace_metricLimit (Ultrafilter.of_le atTop)
  choose mid h using metricLimit_has_midpoints U o hmid
  refine ⟨Y, inferInstance, Q, ⟨f⟩, inferInstance, isGeodesic_of_exactMidpoints mid ?_⟩
  exact fun a b ↦ ⟨(h a b).1, (dist_comm _ _).trans (h a b).2⟩
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace MidpointTower
open Filter Topology HyperbolicObstruction MetricLimit SiteTensor
variable {K : Type*} [Field K] (T : MidpointTower K)
private def push {n m : ℕ} (h : n ≤ m) (x : (T.stage n).carrier) : (T.stage m).carrier :=
  Nat.leRecOn (C := fun i ↦ (T.stage i).carrier) h (fun {i} ↦ (T.step i).map) x
private theorem push_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (x : (T.stage n).carrier) :
    T.push (h.trans h') x = T.push h' (T.push h x) :=
  Nat.leRecOn_trans (C := fun i ↦ (T.stage i).carrier) h h' x
private def pushEmbedding {n m : ℕ} (h : n ≤ m) :
    PriceEmbedding (T.stage n).prices (T.stage m).prices where
  map := T.push h
  isometry := by
    induction m, h using Nat.le_induction with
    | base =>
      apply Isometry.of_dist_eq
      intro x y
      simp only [push, Nat.leRecOn_self]
    | succ m h ih =>
      apply Isometry.of_dist_eq
      intro x y
      simpa only [push, Nat.leRecOn_succ h, (T.step m).isometry.dist_eq] using ih.dist_eq x y
  price := by
    intro I _ R p
    induction m, h using Nat.le_induction with
    | base => simp [push, Function.comp_def, Nat.leRecOn_self]
    | succ m h ih =>
      rw [← ih, ← (T.step m).price R (T.push h ∘ p)]
      simp only [push, Function.comp_def, Nat.leRecOn_succ h]
variable (o : (T.stage 0).carrier)
private abbrev basepoint (n : ℕ) := T.push (Nat.zero_le n) o
private abbrev tailU := Ultrafilter.of (atTop : Filter ℕ)
private def sectionAt (n : ℕ) (x : (T.stage n).carrier) :
    Bounded tailU (fun i ↦ (T.stage i).carrier) (T.basepoint o) where
  val k := if h : n ≤ k then T.push h x else T.basepoint o k
  bound := by
    refine ⟨dist (T.basepoint o n) x, fun k ↦ ?_⟩
    split_ifs with h
    · change dist (T.push (Nat.zero_le k) o) _ ≤ _
      rw [T.push_trans (Nat.zero_le n) h]
      exact ((T.pushEmbedding h).isometry.dist_eq _ _).le
    · simp [dist_nonneg]
private abbrev ambient := Space (U := tailU) (X := fun i ↦ (T.stage i).carrier) (o := T.basepoint o)
private abbrev prices : SpectralPlacementPrices K (T.ambient o) :=
  SpectralPlacementPrices.metricLimit tailU (fun n ↦ (T.stage n).prices)
private def embed (n : ℕ) : PriceEmbedding (T.stage n).prices (T.prices o) where
  map x := point (T.sectionAt o n x)
  isometry := by
    apply Isometry.of_dist_eq
    intro x y
    apply tendsto_nhds_unique (tendsto_point_dist (T.sectionAt o n x) (T.sectionAt o n y))
    apply tendsto_const_nhds.congr'
    filter_upwards [Ultrafilter.of_le (atTop : Filter ℕ) (eventually_ge_atTop n)] with k hk
    simpa only [sectionAt, dite_eq_left hk, pushEmbedding] using ((T.pushEmbedding hk).isometry.dist_eq x y).symm
  price := by
    intro I _ R p
    apply tendsto_nhds_unique (SpectralPlacementPrices.metricLimit_price_tendsto tailU
      (fun k ↦ (T.stage k).prices) R (T.sectionAt o n ∘ p))
    apply tendsto_const_nhds.congr'
    filter_upwards [Ultrafilter.of_le (atTop : Filter ℕ) (eventually_ge_atTop n)] with k hk
    exact (by simpa only [Function.comp_def, sectionAt, dite_eq_left hk, pushEmbedding] using
      ((T.pushEmbedding hk).price R p).symm)
private theorem embed_push {n m : ℕ} (h : n ≤ m) (x : (T.stage n).carrier) :
    (T.embed o m).map (T.push h x) = (T.embed o n).map x := by
  apply dist_eq_zero.mp
  apply tendsto_nhds_unique (tendsto_point_dist (T.sectionAt o m (T.push h x)) (T.sectionAt o n x))
  apply tendsto_const_nhds.congr'
  filter_upwards [Ultrafilter.of_le (atTop : Filter ℕ) (eventually_ge_atTop m)] with k hk
  simp only [sectionAt, dite_eq_left hk, dite_eq_left (h.trans hk), T.push_trans h hk, dist_self]
theorem exists_midpoint_union (o : (T.stage 0).carrier) :
    ∃ (X : Type) (_ : MetricSpace X) (P : SpectralPlacementPrices K X),
      Nonempty (PriceEmbedding (T.stage 0).prices P) ∧
      ∀ a b : X, ∃ m, IsWireMidpoint a b m := by
  classical
  let S : Set (T.ambient o) := ⋃ n, Set.range (T.embed o n).map
  let ι (n : ℕ) (x : (T.stage n).carrier) : S :=
    ⟨(T.embed o n).map x, Set.mem_iUnion.mpr ⟨n, x, rfl⟩⟩
  let P := (T.prices o).pullback (Subtype.val : S → _) isometry_subtype_coe
  let f : PriceEmbedding (T.stage 0).prices P := {
    map := ι 0
    isometry := (T.embed o 0).isometry
    price := (T.embed o 0).price }
  refine ⟨S, inferInstance, P, ⟨f⟩, ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp ha
  obtain ⟨j, y, rfl⟩ := Set.mem_iUnion.mp hb
  let k := max i j
  let u := T.push (le_max_left i j) x
  let v := T.push (le_max_right i j) y
  obtain ⟨m, hm⟩ := T.midpoint k u v
  refine ⟨ι (k+1) m, ?_⟩
  change IsWireMidpoint ((T.embed o i).map x) ((T.embed o j).map y) ((T.embed o (k+1)).map m)
  have eqstep (w : (T.stage k).carrier) :
      (T.embed o (k+1)).map ((T.step k).map w) = (T.embed o k).map w := by
    simpa only [push, Nat.leRecOn_succ'] using T.embed_push o (Nat.le_succ k) w
  have h := hm.map (T.embed o (k+1)).isometry
  rw [eqstep, eqstep] at h
  dsimp only [u, v, k] at h
  rwa [T.embed_push, T.embed_push] at h
end MidpointTower
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open HyperbolicObstruction SiteTensor
variable {K : Type*} [Field K]
theorem HasFiniteMidpointExtensions.complete_geodesic_extension
    (h : HasFiniteMidpointExtensions K) (A : FinitePriceSpace K) (o : A.carrier) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y),
      Nonempty (PriceEmbedding A.prices Q) ∧ CompleteSpace Y ∧ IsGeodesic Y := by
  obtain ⟨T, ⟨f⟩⟩ := h.tower A
  obtain ⟨X, _, P, ⟨g⟩, hm⟩ := T.exists_midpoint_union (f.map o)
  obtain ⟨Y, met, Q, ⟨j⟩, complete, geodesic⟩ :=
    exists_complete_geodesic_price_extension P (g.map (f.map o)) hm
  exact ⟨Y, met, Q, ⟨(f.trans g).trans j⟩, complete, geodesic⟩
theorem HasFiniteMidpointExtensions.realize_point (h : HasFiniteMidpointExtensions K)
    {J : Type} [Fintype J] [Nonempty J]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (Y : Type) (_ : MetricSpace Y) (Q : SpectralPlacementPrices K Y) (p : J → Y),
      CompleteSpace Y ∧ IsGeodesic Y ∧
      (∀ a b, dist (p a) (p b) = rawWireDistance φ c a b) ∧
      ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (v : I → J),
        Q.price T (p ∘ v) = rawLogPrice φ c (T.group v) := by
  obtain ⟨X, met, P, q, hq, hd, hp⟩ := exists_metric_price_realization φ c hc
  let A : FinitePriceSpace K := ⟨X, met, Finite.of_surjective q hq, P⟩
  obtain ⟨Y, metY, Q, ⟨f⟩, hy, hgeo⟩ := h.complete_geodesic_extension A (q (Classical.arbitrary J))
  exact ⟨Y, metY, Q, f.map ∘ q, hy, hgeo, fun a b ↦ (f.isometry.dist_eq _ _).trans (hd a b),
    fun T v ↦ (f.price T (q ∘ v)).trans (hp T v)⟩
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical BigOperators NNReal
section
open SiteTensor
namespace SiteTensor
universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
def classPrice (g : NonzeroProduct.{v} I K →+ ℝ) (x : TensorClass.{v} I K) : ℝ :=
  if h : x = 0 then 0 else g (Additive.ofMul (⟨x, h⟩ : nonzeroClasses I K))
@[simp] theorem classPrice_zero (x : TensorClass.{v} I K) :
    classPrice 0 x = 0 := by
  simp [classPrice]
theorem classPrice_scaled_log (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → _))
    (c : ℝ) (x : TensorClass.{v} I K) :
    classPrice (c • logPoint φ) x = c * Real.logb 2 (φ.val x : ℝ) := by
  by_cases hx : x = 0
  · simp [classPrice, hx, φ.property.1]
  · simp only [classPrice, hx, ↓reduceDIte]
    rfl
end SiteTensor
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SpectralPlacementPrices
open SiteTensor
variable {I : Type} [Fintype I] [Nonempty I] {X K : Type*} [MetricSpace X] [Field K]
theorem exists_spectralPrice_of_placement (P : SpectralPlacementPrices K X) (σ : I → X) :
    ∃ g : NonzeroProduct.{0} I K →+ ℝ, IsSpectralPrice unit_le_nonzeroClass g ∧
      ∀ T : Raw.{0} I K, P.price T σ = classPrice g (ofRaw T) := by
  classical
  let A := Set.range σ
  let : Fintype A := Fintype.ofFinite A
  let J := Fin (Fintype.card A)
  let e : A ≃ J := Fintype.equivFin A
  let v : J ↪ X := e.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let q : I → J := e ∘ Set.rangeFactorization σ
  have hq : Function.Surjective q := e.surjective.comp Set.rangeFactorization_surjective
  have hvq : v ∘ q = σ := funext fun i => congrArg Subtype.val (e.symm_apply_apply _)
  let : Nonempty J := ⟨q (Classical.arbitrary I)⟩
  rcases subsingleton_or_nontrivial J with hJ | hJ
  · let i := Classical.arbitrary I
    have hs : σ = fun _ => σ i := by
      rw [← hvq]
      exact funext fun j => congrArg v (Subsingleton.elim (q j) (q i))
    refine ⟨0, Or.inl rfl, fun T => ?_⟩
    exact (congrArg (P.price T) hs).trans <|
      (P.collapsed T (σ i)).trans (classPrice_zero _).symm
  · obtain ⟨φ, hpos, hφ⟩ := P.normalized_group v
    let ψ := groupSpectralPoint q hq φ
    let d := P.price (Raw.diagonal J K (Fin 2)) v
    refine ⟨d • logPoint ψ, Or.inr ⟨ψ, d, hpos, rfl⟩, fun T => ?_⟩
    by_cases hT : T.coeff = 0
    · rw [P.zero_tensor T hT σ, (ofRaw_eq_zero_iff T).mpr hT]
      simp [classPrice]
    rw [← hvq, hφ q T hT, classPrice_scaled_log]
    rfl
end SpectralPlacementPrices
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
namespace SpectralPlacementPrices
open SiteTensor
variable {K X : Type*} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)
theorem zero_or_common_group_price {J : Type} [Fintype J] [Nonempty J] (p : J → X) :
    (∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (σ : I → J), P.price T (p ∘ σ) = 0) ∨
    ∃ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ),
      0 < c ∧ ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (σ : I → J),
        P.price T (p ∘ σ) = rawLogPrice φ c (T.group σ) := by
  obtain ⟨g, hg, hprice⟩ := P.exists_spectralPrice_of_placement p
  rcases hg with rfl | ⟨φ, c, hc, rfl⟩
  · left
    intro I _ T σ
    simp only [P.group, hprice, classPrice_zero]
  · refine Or.inr ⟨φ, c, hc, ?_⟩
    intro I _ T σ
    rw [P.group, hprice, classPrice_scaled_log]
    rfl
end SpectralPlacementPrices
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
omit [Nonempty I] in
theorem Raw.maskDiagonal_restricts_of_subset {S T : Finset I} (h : S ⊆ T)
    (α : Type) [Fintype α] :
    (Raw.maskDiagonal K S α).Restricts (Raw.maskDiagonal K T α) := by
  let c (a : α) (i : I) (_ : i ∈ T) := a
  let : ∀ i, Fintype (MaskLeg T α i) := (Raw.maskDiagonal K T α).finiteLeg
  apply (Crossing.restriction_basisTensor_iff (F := K) (A := MaskLeg T α) (B := MaskLeg S α)
    c (Raw.maskDiagonal K S α).coeff).mpr
  refine ⟨fun i x y ↦ if x = (fun hi ↦ y (h hi)) then 1 else 0, fun x ↦ ?_⟩
  simp only [Raw.maskDiagonal, Crossing.basisTensor, Fintype.prod_boole, c, funext_iff]
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
namespace SpectralPlacementPrices
open SiteTensor
variable {K X : Type*} [Field K] [PseudoMetricSpace X] (P : SpectralPlacementPrices K X)
def diagonal (S : Finset X) : ℝ :=
  if S.Nonempty then P.price (Raw.diagonal (Fin S.card) K (Fin 2))
    (fun i ↦ (S.equivFin.symm i).val) else 0
@[simp] theorem diagonal_empty : P.diagonal ∅ = 0 := by simp [diagonal]
theorem price_eq_of_class_eq {I : Type} [Fintype I] [Nonempty I] (p : I ↪ X)
    {T V : Raw.{0} I K} (he : ofRaw T = ofRaw V) : P.price T p = P.price V p := by
  cases subsingleton_or_nontrivial I with
  | inl hs =>
    let i : I := Classical.choice inferInstance
    have e : (p : I → X) = fun _ ↦ p i := funext (fun j ↦ congrArg p (Subsingleton.elim j i))
    rw [e, P.collapsed, P.collapsed]
  | inr ht =>
    by_cases hT : T.coeff = 0
    · have hV := (ofRaw_eq_zero_iff V).mp (he.symm.trans ((ofRaw_eq_zero_iff T).mpr hT))
      rw [P.zero_tensor T hT, P.zero_tensor V hV]
    · have hV : V.coeff ≠ 0 := fun h ↦ hT ((ofRaw_eq_zero_iff T).mp
        (he.trans ((ofRaw_eq_zero_iff V).mpr h)))
      obtain ⟨φ, hφ⟩ := P.normalized p
      rw [hφ T hT, hφ V hV, he]
theorem price_binaryDiagonal_eq {I : Type} [Fintype I] [Nonempty I] (p : I → X) :
    P.price (Raw.diagonal I K (Fin 2)) p = P.diagonal (Finset.univ.image p) := by
  let S := Finset.univ.image p
  have hS : S.Nonempty := Finset.univ_nonempty.image p
  let x : Fin S.card ↪ X := S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  let σ (i : I) := S.equivFin ⟨p i, Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
  have hσ : Function.Surjective σ := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (S.equivFin.symm j).property
    refine ⟨i, S.equivFin.symm.injective ?_⟩
    exact Subtype.ext (by simpa only [σ, Equiv.symm_apply_apply] using hi)
  have hp : p = x ∘ σ := funext (fun i ↦ by simp [x, σ])
  have : Nonempty (Fin S.card) := ⟨σ (Classical.choice inferInstance)⟩
  change P.price _ p = P.diagonal S
  rw [diagonal, ite_eq_left hS, hp, P.group]
  apply P.price_eq_of_class_eq x
  change groupClass σ (ofRaw (Raw.diagonal I K (Fin 2))) = _
  rw [ofRaw_diagonal_fin_eq_natCast, ofRaw_diagonal_fin_eq_natCast]
  exact map_natCast (groupRingHom σ hσ) 2
theorem diagonal_pair (x y : X) : P.diagonal {x, y} = dist x y := by
  have h := P.price_binaryDiagonal_eq ![x, y]
  rw [P.wire] at h
  simpa [Finset.univ_fin2] using h.symm
end SpectralPlacementPrices
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
namespace SpectralPlacementPrices
variable {K X : Type*} [Field K] [PseudoMetricSpace X]
theorem diagonal_nonneg (P : SpectralPlacementPrices K X) (S : Finset X) : 0 ≤ P.diagonal S := by
  classical
  by_cases h : S.Nonempty
  · simp only [diagonal, h, ite_true]
    let i : Fin S.card := ⟨0, Finset.card_pos.mpr h⟩
    simpa only [dist_self] using P.dist_le_diagonal
      (fun j : Fin S.card ↦ (S.equivFin.symm j).val) i i
  · simp [diagonal, h]
theorem exists_point_diagonal_map (P : SpectralPlacementPrices K X) {I : Type}
    [Fintype I] [Nontrivial I] (x : I ↪ X) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop),
      ∃ c : ℝ, 0 ≤ c ∧ ∀ (S : Finset I), S.Nonempty →
        P.diagonal (S.map x) =
          c * Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal K S (Fin 2))) : ℝ) := by
  classical
  obtain ⟨φ, hφ⟩ := P.normalized x
  let c := P.price (Raw.diagonal I K (Fin 2)) x
  have hc : 0 ≤ c := by
    let i := Classical.arbitrary I
    simpa only [dist_self] using P.dist_le_diagonal x i i
  refine ⟨φ, c, hc, ?_⟩
  intro S hS
  let σ : S ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hs (i : I) : i ∈ S ↔ ∃ j, σ j = i := by
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.property
  have hocc : Finset.univ.image (x ∘ σ) = S.map x := by
    ext y
    simp [σ, Function.comp_def]
  let _ : Nonempty S := hS.to_subtype
  have hd : (Raw.diagonal S K (Fin 2)).coeff ≠ 0 := by
    obtain ⟨s,hs'⟩ := hS
    intro hz
    have he (a : Fin 2) : ((fun _ : S ↦ (0 : Fin 2)) = fun _ ↦ a) ↔ a = 0 :=
      ⟨fun h ↦ (congrFun h ⟨s,hs'⟩).symm, by rintro rfl; rfl⟩
    have h : (Raw.diagonal S K (Fin 2)).coeff (fun _ ↦ (0 : Fin 2)) = 0 :=
      congrFun hz _
    simp [Raw.diagonal, he] at h
  rw [← hocc, ← P.price_binaryDiagonal_eq, P.group, hφ _ ((Raw.group_ne_zero_iff _ _).mpr hd),
    Raw.ofRaw_group_diagonal_eq_mask σ S hs]
end SpectralPlacementPrices
end
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
namespace SpectralPlacementPrices
variable {K : Type*} {X : Type} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)
theorem diagonal_mono : Monotone P.diagonal := by
  intro S T hST
  by_cases he : S = ∅
  · subst S
    rw [P.diagonal_empty]
    exact P.diagonal_nonneg T
  have hS := Finset.nonempty_iff_ne_empty.mpr he
  have hT := hS.mono hST
  cases subsingleton_or_nontrivial T with
  | inl hs =>
    obtain ⟨s, hsS⟩ := hS
    have hTS : T ⊆ S := fun t ht ↦ by
      have hts : t = s := congrArg Subtype.val (Subsingleton.elim (⟨t, ht⟩ : T) ⟨s,hST hsS⟩)
      exact hts.symm ▸ hsS
    rw [Finset.Subset.antisymm hST hTS]
  | inr hnt =>
    let e : T ↪ X := Function.Embedding.subtype _
    let U : Finset T := Finset.univ.filter (fun i ↦ i.val ∈ S)
    have hU : U.Nonempty := by
      obtain ⟨x,hx⟩ := hS
      exact ⟨⟨x,hST hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩
    have hUS : U.map e = S := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
        exact (Finset.mem_filter.mp hi).2
      · exact fun hx ↦ Finset.mem_map.mpr ⟨⟨x,hST hx⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hx⟩, rfl⟩
    have hUT : (Finset.univ : Finset T).map e = T := by ext; simp [e]
    obtain ⟨φ, c, hc, hm⟩ := P.exists_point_diagonal_map e
    have hle := rawLogPrice_mono φ hc
      (Raw.maskDiagonal_restricts_of_subset (K := K) (Finset.subset_univ U) (Fin 2))
    change c * Real.logb 2 _ ≤ c * Real.logb 2 _ at hle
    rw [← hm U hU, ← hm Finset.univ Finset.univ_nonempty, hUS, hUT] at hle
    exact hle
end SpectralPlacementPrices
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open scoped Classical NNReal
noncomputable section
section
open SiteTensor
theorem SiteTensor.ofRaw_maskDiagonal_univ {I F : Type*} [Fintype I] [Field F]
    (α : Type) [Fintype α] :
    ofRaw (Raw.maskDiagonal F (Finset.univ : Finset I) α) = ofRaw (Raw.diagonal I F α) := by
  let e (i : I) : MaskLeg Finset.univ α i ≃ α :=
    { toFun := fun g => g (Finset.mem_univ i)
      invFun := fun a _ => a
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro x
  simp only [Raw.maskDiagonal, Crossing.basisTensor, Raw.diagonal]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply propext
  constructor
  · rintro rfl
    rfl
  · exact fun h => funext (fun i => funext (fun _ => congrFun h i))
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Book
open HyperbolicObstruction Filter
open scoped Topology Classical
variable {X : Type*} [MetricSpace X]
abbrev Blowup (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (o : X) :=
  MetricLimit.Space (U := ω) (X := fun n ↦ MetricScale.Space (s n)⁻¹ (inv_pos.mpr (hs n)) X)
    (o := fun _ ↦ ⟨o⟩)
theorem blowup_catZero (hX : CATZero X) (ω : Ultrafilter ℕ) {s : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) (o : X) : CATZero (Blowup ω hs o) :=
  MetricLimit.catZero (fun _ ↦ MetricScale.catZero hX)
abbrev BlowupSection (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (o : X) :=
  MetricLimit.Bounded ω (fun n ↦ MetricScale.Space (s n)⁻¹ (inv_pos.mpr (hs n)) X) (fun _ ↦ ⟨o⟩)
variable (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) (o : X)
private noncomputable def representative_p0 (b : Blowup ω hs o) : BlowupSection ω hs o :=
  (SeparationQuotient.surjective_mk b).choose
private theorem representative_point (b : Blowup ω hs o) :
    MetricLimit.point (representative_p0 ω hs o b) = b :=
  (SeparationQuotient.surjective_mk b).choose_spec
private theorem section_dist_tendsto (p q : BlowupSection ω hs o) :
    Tendsto (fun n ↦ dist (p.val n).val (q.val n).val / s n) (ω : Filter ℕ)
      (𝓝 (dist (MetricLimit.point p) (MetricLimit.point q))) := by
  simpa only [div_eq_inv_mul, ← MetricScale.dist_eq] using MetricLimit.tendsto_point_dist p q
private abbrev Stage (n : ℕ) (X : Type*) := MetricScale.Space (s n)⁻¹ (inv_pos.mpr (hs n)) X
private noncomputable def stagePrice {I : Type*} (price : (I → X) → ℝ) (n : ℕ) (u : I → Stage hs n X) : ℝ :=
  price (fun i ↦ (u i).val) / s n
private theorem stagePrice_transport {I : Type*} [Fintype I] (price : (I → X) → ℝ) (w : I → ℝ)
    (ht : ∀ u v, dist (price u) (price v) ≤ ∑ i, dist (u i) (v i) * w i)
    (n : ℕ) (u v : I → Stage hs n X) :
    dist (stagePrice hs price n u) (stagePrice hs price n v) ≤ ∑ i, dist (u i) (v i) * w i := by
  simp only [stagePrice, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hs n)]
  rw [div_eq_inv_mul]
  simpa only [Real.dist_eq, MetricScale.dist_eq, mul_assoc, ← Finset.mul_sum] using
    mul_le_mul_of_nonneg_left (ht (fun i ↦ (u i).val) (fun i ↦ (v i).val)) (inv_nonneg.mpr (hs n).le)
noncomputable def blowupSpectralPrices {K : Type*} [Field K] (H : SpectralPlacementPrices K X) :
    SpectralPlacementPrices K (Blowup ω hs o) :=
  H.blowup ω s hs (fun n b ↦ ((representative_p0 ω hs o b).val n).val)
    (MetricLimit.point (⟨fun _ ↦ ⟨o⟩, 0, fun _ ↦ by simp⟩ : BlowupSection ω hs o))
    (fun p q ↦ by simpa only [representative_point] using
      section_dist_tendsto ω hs o (representative_p0 ω hs o p) (representative_p0 ω hs o q))
theorem tendsto_blowupSpectralPrices {K : Type*} [Field K] (H : SpectralPlacementPrices K X)
    {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I K) (z : I → BlowupSection ω hs o) :
    Tendsto (fun n ↦ H.price T (fun i ↦ ((z i).val n).val) / s n) (ω : Filter ℕ)
      (𝓝 ((blowupSpectralPrices ω hs o H).price T (MetricLimit.point ∘ z))) := by
  refine tendsto_metricLimitPrice (fun i ↦ Real.logb 2 (Fintype.card (T.Leg i)))
    (stagePrice hs (H.price T)) ?_ ?_ z
  · intro n p
    simp [stagePrice, H.collapsed]
  · exact stagePrice_transport hs (H.price T) _ (H.transport T)
end Book
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Book
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev Lift (E : Type*) := WithLp 2 (E × ℝ)
def horizontal (v : E) : Lift E := WithLp.toLp 2 (v, 0)
noncomputable def liftedDirection (g : E) (r : ℝ) : Lift E :=
  r • WithLp.toLp 2 (-g, Real.sqrt (1 - ‖g‖ ^ 2))
theorem liftedDirection_dist_sq (g v : E) (r M : ℝ) (hg : ‖g‖ ≤ 1) :
    dist (M • liftedDirection g r) (horizontal v) ^ 2 =
      M ^ 2 * r ^ 2 + ‖v‖ ^ 2 + 2 * M * r * ⟪g, v⟫_ℝ := by
  have hsq : 0 ≤ 1 - ‖g‖ ^ 2 := by nlinarith [norm_nonneg g]
  let u : Lift E := WithLp.toLp 2 (-g, Real.sqrt (1 - ‖g‖ ^ 2))
  have hu : ‖u‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [u, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hsq]
  have hhor : ‖horizontal v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp [horizontal]
  change dist (M • r • u) (horizontal v) ^ 2 = _
  rw [dist_eq_norm, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_left, mul_pow, mul_pow, hu, hhor]
  simp [u, horizontal, Real.norm_eq_abs, sq_abs]
  ring
end Book
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set SharpIntegralFillings
variable {X : Type*} [MetricSpace X]
theorem cat0_eq_fraction_point
    {γ : X → X → ℝ → X}
    (hγ : ∀ a b q t, t ∈ Icc (0 : ℝ) 1 → dist (γ a b t) q ^ 2 ≤
      (1 - t) * dist a q ^ 2 + t * dist b q ^ 2 - t * (1 - t) * dist a b ^ 2)
    {a b q : X} {t : ℝ} (ht : t ∈ Icc 0 1)
    (ha : dist a q = t * dist a b) (hb : dist b q = (1 - t) * dist a b) :
    γ a b t = q := by
  have h := hγ a b q t ht
  rw [ha, hb] at h
  ring_nf at h
  exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := γ a b t) (y := q)])
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {f g : E → X}
private theorem map_lineMap_eq_fraction
    {γ : X → X → ℝ → X}
    (hγ : ∀ a b q t, t ∈ Icc (0 : ℝ) 1 → dist (γ a b t) q ^ 2 ≤
      (1 - t) * dist a q ^ 2 + t * dist b q ^ 2 - t * (1 - t) * dist a b ^ 2)
    (hc : Convex ℝ C) (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) {t : ℝ} (ht : t ∈ Icc 0 1) :
    γ (f x) (f y) t = f (AffineMap.lineMap x y t) := by
  have hz := hc.lineMap_mem hx hy ht
  apply cat0_eq_fraction_point hγ ht
  · rw [hf x hx _ hz, hf x hx _ hy, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht.1]
  · rw [hf y hy _ hz, hf x hx _ hy, dist_right_lineMap, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2)]
theorem cat0_patch_strongConvexOn_dist_sq (hX : IsCAT0 X) (hc : Convex ℝ C)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y) (q : X) :
    StrongConvexOn C 2 (fun x ↦ dist (f x) q ^ 2) := by
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  refine ⟨hc, ?_⟩
  intro x hx y hy a b ha hb hab
  have ht : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
  have h := hγ (f x) (f y) q b ht
  rw [map_lineMap_eq_fraction hγ hc hf hx hy ht, AffineMap.lineMap_apply_module,
    show 1 - b = a by linarith, hf x hx y hy, dist_eq_norm] at h
  simpa [mul_comm b a] using h
theorem cat0_patch_convexOn_dist (hX : IsCAT0 X) (hc : Convex ℝ C)
    (hf : ∀ x ∈ C, ∀ y ∈ C, dist (f x) (f y) = dist x y) (q : X) :
    ConvexOn ℝ C (fun x ↦ dist (f x) q) := by
  refine ⟨hc, ?_⟩
  intro x hx y hy a b ha hb hab
  have hstrong := (cat0_patch_strongConvexOn_dist_sq hX hc hf q).2 hx hy ha hb hab
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, one_mul,
    smul_eq_mul] at hstrong
  have hd := abs_dist_sub_le (f x) (f y) q
  rw [hf _ hx _ hy, dist_eq_norm] at hd
  have hsquare := (sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2)
  have hprod := mul_le_mul_of_nonneg_left hsquare (mul_nonneg ha hb)
  simp only [smul_eq_mul]
  refine (sq_le_sq₀ dist_nonneg
    (add_nonneg (mul_nonneg ha dist_nonneg) (mul_nonneg hb dist_nonneg))).mp ?_
  apply hstrong.trans
  calc
    _ ≤ a * dist (f x) q ^ 2 + b * dist (f y) q ^ 2 -
        a * b * (dist (f x) q - dist (f y) q) ^ 2 := by linarith
    _ = _ := by rw [show a = 1 - b by linarith]; ring
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Set MeasureTheory Module
open scoped Topology InnerProductSpace NNReal
section
theorem exists_differentiable_seq_above_facet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f C)
    {p e : E} (hp : p ∈ interior C) (hfp : 0 < f p) (he : ‖e‖ = 1) :
    ∃ y : ℕ → E, Tendsto y atTop (𝓝 p) ∧
      ∀ j, y j ∈ interior C ∧ 0 < ⟪y j - p, e⟫_ℝ ∧
        0 < f (y j) ∧ DifferentiableAt ℝ f (y j) := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  let D := {x : E | DifferentiableAt ℝ g x}
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hd : Dense D := Measure.dense_of_ae
    (hg.ae_differentiableAt (μ := (Basis.ofVectorSpace ℝ E).addHaar))
  let H := {x : E | 0 < ⟪x - p, e⟫_ℝ}
  have ho : IsOpen H := isOpen_lt continuous_const
    ((continuous_id.sub continuous_const).inner continuous_const)
  have hc : p ∈ closure H := by
    let ray : ℝ → E := fun t ↦ p + t • e
    have hcont : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
    have h0 : (0 : ℝ) ∈ closure (Ioi 0) := by simp [closure_Ioi]
    have hr : ray '' Ioi 0 ⊆ H := by
      rintro _ ⟨t, ht, rfl⟩
      simpa [ray, H, real_inner_smul_left, real_inner_self_eq_norm_sq, he] using ht
    have := closure_mono hr (image_closure_subset_closure_image hcont (mem_image_of_mem ray h0))
    simpa [ray] using this
  let U := interior C ∩ {x : E | 0 < g x}
  have hu : IsOpen U := isOpen_interior.inter (isOpen_lt continuous_const hg.continuous)
  have hpu : p ∈ U := ⟨hp, show 0 < g p from hfg (interior_subset hp) ▸ hfp⟩
  have hcl : p ∈ closure ((U ∩ H) ∩ D) :=
    closure_minimal (hd.open_subset_closure_inter (hu.inter ho)) isClosed_closure
      (hu.inter_closure ⟨hpu, hc⟩)
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  refine ⟨y, hlim, fun j ↦ ?_⟩
  obtain ⟨⟨⟨hj, hpos⟩, hh⟩, hdiff⟩ := hy j
  refine ⟨hj, hh, (hfg (interior_subset hj)) ▸ hpos, hdiff.congr_of_eventuallyEq ?_⟩
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hj) hfg
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set Filter
open scoped RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E} {f : E → ℝ} {x z p : E}
theorem convexOn_sq_distance_sub_norm_sq
    (hcat : StrongConvexOn C 2 (fun v ↦ f v ^ 2)) (p : E) :
    ConvexOn ℝ C (fun v ↦ f v ^ 2 - ‖v - p‖ ^ 2) := by
  have h₀ : ConvexOn ℝ C (fun v ↦ f v ^ 2 - ‖v‖ ^ 2) := by
    simpa using strongConvexOn_iff_convex.mp hcat
  refine ⟨h₀.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := h₀.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h
  simp only [smul_eq_mul, norm_sub_sq_real, inner_add_left, real_inner_smul_left]
  nlinarith [congrArg (fun t : ℝ ↦ t * ‖p‖ ^ 2) hab]
variable [CompleteSpace E] {g : E}
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Book
open Filter Set HyperbolicObstruction
open scoped Topology RealInnerProductSpace
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
private theorem sq_slope {f : E → ℝ} {y g : E} (hg : HasGradientAt f g y) (w : E) :
    Tendsto (fun h : ℝ ↦ (f (y + h • w) ^ 2 - f y ^ 2) / h)
      (𝓝[>] 0) (𝓝 (2 * f y * ⟪g, w⟫)) := by
  have hline : HasDerivAt (fun h : ℝ ↦ y + h • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have hf := hg.hasFDerivAt
  have hcomp : HasDerivAt (fun h : ℝ ↦ f (y + h • w)) ⟪g,w⟫ 0 := by
    exact (show HasFDerivAt f (InnerProductSpace.toDual ℝ E g) (y + (0 : ℝ) • w) by
      simpa using hf).comp_hasDerivAt 0 hline
  simpa [div_eq_inv_mul, mul_assoc] using (hcomp.pow 2).tendsto_slope_zero_right
theorem tendsto_tangent_dist_sq (hX : CATZero X) {U : Set E} {φ : E → X}
    (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z)
    {y g : E} (hy : U ∈ 𝓝 y) (x : X)
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) (v : E) {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun h : ℝ ↦ (dist (CATZero.segment hX (φ y) x (h * M))
      (φ (y + h • v)) / h) ^ 2) (𝓝[>] 0)
      (𝓝 (M ^ 2 * dist (φ y) x ^ 2 + ‖v‖ ^ 2 + 2 * M * dist (φ y) x * ⟪g, v⟫)) := by
  let f (z : E) := dist (φ z) x
  let P (h : ℝ) := CATZero.segment hX (φ y) x (h * M)
  let Z (w : E) (h : ℝ) := φ (y + h • w)
  let A (w : E) (h : ℝ) := (dist (P h) (Z w h) / h) ^ 2
  let B (w : E) (h : ℝ) := M ^ 2 * f y ^ 2 + (1 - h * M) * ‖w‖ ^ 2 +
    M * ((f (y + h • w) ^ 2 - f y ^ 2) / h)
  let L (w : E) := M ^ 2 * f y ^ 2 + ‖w‖ ^ 2 + 2 * M * f y * ⟪g,w⟫
  change Tendsto (A v) _ (𝓝 (L v))
  have hzero : Tendsto (fun h : ℝ ↦ h) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hscale : Tendsto (fun h : ℝ ↦ h * M) (𝓝[>] 0) (𝓝 0) := by
    simpa using hzero.mul_const M
  have hpar : ∀ᶠ h : ℝ in 𝓝[>] 0, h * M ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin, hscale.eventually_lt_const zero_lt_one]
      with h hh h₁
    exact ⟨mul_nonneg (le_of_lt hh) hM, h₁.le⟩
  have hin (w : E) : ∀ᶠ h : ℝ in 𝓝[>] 0, y + h • w ∈ U := by
    have hlim : Tendsto (fun h : ℝ ↦ y + h • w) (𝓝[>] 0) (𝓝 y) := by
      simpa using (hzero.smul_const w).const_add y
    exact hlim hy
  have hdist (w : E) : ∀ᶠ h : ℝ in 𝓝[>] 0, dist (Z w h) (φ y) = h * ‖w‖ := by
    filter_upwards [hin w, self_mem_nhdsWithin] with h hin' hh
    dsimp only [Z]
    rw [hφ _ hin' y (mem_of_mem_nhds hy), dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < h from hh)]
  have hupper (w : E) : ∀ᶠ h : ℝ in 𝓝[>] 0, A w h ≤ B w h := by
    filter_upwards [hpar, hdist w, self_mem_nhdsWithin] with h hp hd hh
    have hc := CATZero.segment_cn hX (φ y) x (Z w h) hp
    rw [hd, dist_comm (Z w h)] at hc
    change dist (P h) (Z w h) ^ 2 ≤ _ at hc
    change (dist (P h) (Z w h) / h) ^ 2 ≤ _
    dsimp only [B, f]
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos (show 0 < h from hh))]
    calc
      _ ≤ _ := hc
      _ = _ := by dsimp only [Z]; field_simp [(show 0 < h from hh).ne']; ring
  have hB (w : E) : Tendsto (B w) (𝓝[>] 0) (𝓝 (L w)) := by
    have hs := (sq_slope hg w).const_mul M
    have hl := (tendsto_const_nhds (x := M ^ 2 * f y ^ 2)).add
      (((tendsto_const_nhds (x := 1)).sub hscale).mul_const (‖w‖ ^ 2))
    convert! hl.add hs using 2
    dsimp [L, f]
    ring
  let D := M ^ 2 * f y ^ 2 + ‖v‖ ^ 2
  have hpair : ∀ᶠ h : ℝ in 𝓝[>] 0, 2 * D ≤ A v h + A (-v) h := by
    filter_upwards [hin v, hin (-v), hdist v, hdist (-v), hpar, self_mem_nhdsWithin]
      with h hv hn hd hd' hp hh
    have hh' : 0 < h := hh
    have hdiff : y + h • v - (y + h • -v) = (2 * h) • v := by
      rw [smul_neg, two_mul, add_smul]; abel
    have hspan : dist (Z v h) (Z (-v) h) = 2 * h * ‖v‖ := by
      dsimp only [Z]
      rw [hφ _ hv _ hn, dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [norm_neg] at hd'
    have hc := CATZero.cn_of_dist hX (x := Z v h) (y := Z (-v) h)
      (p := φ y) (P h) (t := 1 / 2) (by norm_num)
      (by rw [hd, hspan]; ring) (by rw [dist_comm, hd', hspan]; ring)
    rw [dist_comm (P h) (φ y), CATZero.segment_left hX (φ y) x hp, hspan] at hc
    dsimp only [D, A, f]
    rw [div_pow, div_pow, ← add_div, le_div_iff₀ (sq_pos_of_pos hh')]
    linarith only [hc]
  have hlower : ∀ᶠ h : ℝ in 𝓝[>] 0, 2 * D - B (-v) h ≤ A v h := by
    filter_upwards [hpair, hupper (-v)] with h hp hu
    linarith
  have hlowlim : Tendsto (fun h ↦ 2 * D - B (-v) h) (𝓝[>] 0) (𝓝 (L v)) := by
    have heq : 2 * D - L (-v) = L v := by
      dsimp [D, L]
      rw [norm_neg, inner_neg_right]
      ring
    rw [← heq]
    exact tendsto_const_nhds.sub (hB (-v))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim (hB v) hlower (hupper v)
theorem tendsto_tangent_dist (hX : CATZero X) {U : Set E} {φ : E → X}
    (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z)
    {y g : E} (hy : U ∈ 𝓝 y) (x : X)
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) (v : E) {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun h : ℝ ↦ dist (CATZero.segment hX (φ y) x (h * M)) (φ (y + h • v)) / h)
      (𝓝[>] 0) (𝓝 (dist (M • liftedDirection g (dist (φ y) x)) (horizontal v))) := by
  have hlip : LipschitzOnWith 1 (fun u ↦ dist (φ u) x) U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu z hz
    simpa [hφ u hu z hz] using dist_dist_dist_le_left (φ u) (φ z) x
  have hgnorm : ‖g‖ ≤ 1 := by simpa using hg.hasFDerivAt.le_of_lipschitzOn hy hlip
  have hs := tendsto_tangent_dist_sq hX hφ hy x hg v hM
  rw [← liftedDirection_dist_sq _ _ _ _ hgnorm] at hs
  have hr := hs.sqrt
  rw [Real.sqrt_sq dist_nonneg] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact Real.sqrt_sq (div_nonneg dist_nonneg (le_of_lt hh))
end Book
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open HyperbolicObstruction SharpIntegralFillings
variable {X : Type*} [MetricSpace X]
theorem isCAT0_of_catZero (h : CATZero X) : IsCAT0 X := by
  refine ⟨CATZero.segment h, fun x y ↦ ⟨(CATZero.segment_spec h x y).1,
    (CATZero.segment_spec h x y).2.1⟩, fun x y s t hs ht ↦
      (CATZero.segment_spec h x y).2.2 s hs t ht, ?_⟩
  intro o x y s t hs ht
  have h₁ := CATZero.segment_cn h o x (CATZero.segment h o y t) hs
  have h₂ := CATZero.segment_cn h o y x ht
  rw [dist_comm (CATZero.segment h o y t) (CATZero.segment h o x s),
    dist_comm (CATZero.segment h o y t) o, CATZero.segment_left h o y ht,
    dist_comm (CATZero.segment h o y t) x] at h₁
  rw [dist_comm x o] at h₂
  linarith only [h₁, mul_le_mul_of_nonneg_left h₂ hs.1]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set SharpIntegralFillings
open scoped RealInnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MetricSpace X]
theorem euclidean_dist_lineMap_sq (a v w : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (AffineMap.lineMap a v t) w ^ 2 =
      (1 - t) * dist a w ^ 2 + t * dist v w ^ 2 - t * (1 - t) * dist a v ^ 2 := by
  simp only [dist_eq_norm, AffineMap.lineMap_apply_module]
  rw [show (1 - t) • a + t • v - w = (1 - t) • (a - w) + t • (v - w) by module,
    show a - v = (a - w) - (v - w) by abel, norm_add_sq_real, norm_sub_sq_real (a - w),
    norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_of_nonneg (sub_nonneg.mpr ht.2), Real.norm_of_nonneg ht.1]
  ring
theorem cat0_segment_dist_flat_sq (hX : IsCAT0 X) {g : E → X} (hg : Isometry g)
    {b P : X} {a v : E} {H t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : ∀ w, dist b (g w) ^ 2 = dist a w ^ 2 + H ^ 2)
    (hPb : dist b P = t * dist b (g v)) (hPv : dist (g v) P = (1 - t) * dist b (g v))
    (w : E) : dist P (g w) ^ 2 = dist (AffineMap.lineMap a v t) w ^ 2 + ((1 - t) * H) ^ 2 := by
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  have hP := cat0_eq_fraction_point hγ ht hPb hPv
  let c := AffineMap.lineMap a v t
  let F := fun z ↦ dist (g z) P ^ 2 - ‖z - c‖ ^ 2
  have major (z : E) : F z ≤ ((1 - t) * H) ^ 2 := by
    have h := hγ b (g v) (g z) t ht
    rw [hP, hb z, hb v, hg.dist_eq] at h
    dsimp only [F, c]
    rw [← dist_eq_norm, dist_comm z, euclidean_dist_lineMap_sq _ _ _ ht, dist_comm (g z) P]
    linarith
  have touch : F v = ((1 - t) * H) ^ 2 := by
    dsimp only [F, c]
    rw [hPv, mul_pow, hb v, ← dist_eq_norm, dist_right_lineMap,
      Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
    ring
  have hc : ConvexOn ℝ univ F := convexOn_sq_distance_sub_norm_sq
    (cat0_patch_strongConvexOn_dist_sq hX (convex_univ) (fun x _ y _ ↦ hg.dist_eq x y) P) c
  have lower : ((1 - t) * H) ^ 2 ≤ F w := by
    let z := v + (v - w)
    have hm := hc.2 (mem_univ w) (mem_univ z) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
    have hv : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • z = v := by dsimp only [z]; module
    rw [hv, touch] at hm
    simp only [smul_eq_mul] at hm
    linarith [major z]
  have heq := le_antisymm (major w) lower
  dsimp only [F, c] at heq
  rw [← dist_eq_norm, dist_comm w, dist_comm (g w) P] at heq
  linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]
private theorem norm_sub_extension (u v : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖u - (v + t • (v - u))‖ = (1 + t) * ‖u - v‖ ∧
    ‖v - (v + t • (v - u))‖ = t * ‖u - v‖ := by
  rw [show u - (v + t • (v - u)) = (1 + t) • (u - v) by module,
    show v - (v + t • (v - u)) = t • (u - v) by module]
  simp [norm_smul, abs_of_nonneg ht, abs_of_nonneg (show 0 ≤ 1 + t by linarith)]
private theorem sqrt_sq_dilate (c d h : ℝ) (hc : 0 ≤ c) :
    Real.sqrt ((c * d) ^ 2 + (c * h) ^ 2) = c * Real.sqrt (d ^ 2 + h ^ 2) := by
  rw [show (c * d) ^ 2 + (c * h) ^ 2 = c ^ 2 * (d ^ 2 + h ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
private theorem upper_flat_dist_le_of_lt (flat : E → X) {x y : X} {u v : E}
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a)
    (hx : ∀ w, dist x (flat w) = Real.sqrt (‖u - w‖ ^ 2 + a ^ 2))
    (hy : ∀ w, dist y (flat w) = Real.sqrt (‖v - w‖ ^ 2 + b ^ 2)) :
    Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) ≤ dist x y := by
  let t := b / (a - b)
  have ht : 0 ≤ t := div_nonneg hb (sub_nonneg.mpr hba.le)
  have ht₀ : t * (a - b) = b := div_mul_cancel₀ _ (sub_ne_zero.mpr hba.ne')
  have ht₁ : (1 + t) * (a - b) = a := by linarith [add_mul 1 t (a - b)]
  let w := v + t • (v - u)
  obtain ⟨hu, hv⟩ := norm_sub_extension u v ht
  have h := dist_triangle x y (flat w)
  rw [hx, hy, hu, hv] at h
  have hx' : Real.sqrt (((1 + t) * ‖u - v‖) ^ 2 + a ^ 2) =
      (1 + t) * Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) := by
    conv_lhs => rw [← ht₁]
    exact sqrt_sq_dilate _ _ _ (by linarith)
  have hy' : Real.sqrt ((t * ‖u - v‖) ^ 2 + b ^ 2) =
      t * Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) := by
    conv_lhs => rw [← ht₀]
    exact sqrt_sq_dilate _ _ _ ht
  rw [hx', hy'] at h
  linarith
private theorem upper_flat_dist_le_of_eq (flat : E → X) {x y : X} {u v : E} {a : ℝ}
    (hx : ∀ w, dist x (flat w) = Real.sqrt (‖u - w‖ ^ 2 + a ^ 2))
    (hy : ∀ w, dist y (flat w) = Real.sqrt (‖v - w‖ ^ 2 + a ^ 2)) :
    ‖u - v‖ ≤ dist x y := by
  by_contra! h
  let d := ‖u - v‖
  let ε := d - dist x y
  have hε : 0 < ε := sub_pos.mpr h
  have hd : 0 < d := lt_of_le_of_lt dist_nonneg h
  let t := a ^ 2 / (d * ε)
  have ht : 0 ≤ t := div_nonneg (sq_nonneg _) (mul_pos hd hε).le
  have ht' : t * (d * ε) = a ^ 2 := div_mul_cancel₀ _ (mul_pos hd hε).ne'
  let w := v + t • (v - u)
  have htri := dist_triangle x y (flat w)
  obtain ⟨hu, hv⟩ := norm_sub_extension u v ht
  rw [hx, hy, hu, hv] at htri
  have hlow : (1 + t) * d ≤ Real.sqrt (((1 + t) * d) ^ 2 + a ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    linarith [sq_nonneg a]
  have hhigh : t * d + ε ≤ Real.sqrt ((t * d) ^ 2 + a ^ 2) := by
    change _ ≤ dist x y + Real.sqrt ((t * d) ^ 2 + a ^ 2) at htri
    dsimp only [ε]
    linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ t * d + ε) (Real.sqrt_nonneg _)).mpr hhigh
  rw [Real.sq_sqrt (by positivity)] at hsq
  nlinarith [sq_pos_of_pos hε, sq_nonneg a]
theorem euclidean_halfSpace_dist_le (flat : E → X) {x y : X} {u v : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ w, dist x (flat w) = Real.sqrt (‖u - w‖ ^ 2 + a ^ 2))
    (hy : ∀ w, dist y (flat w) = Real.sqrt (‖v - w‖ ^ 2 + b ^ 2)) :
    Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) ≤ dist x y := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [norm_sub_rev, ← neg_sub b a, neg_sq, dist_comm]
    exact upper_flat_dist_le_of_lt flat ha h hy hx
  · simpa [Real.sqrt_sq (norm_nonneg (u - v))] using upper_flat_dist_le_of_eq flat hx hy
  · exact upper_flat_dist_le_of_lt flat hb h hx hy
theorem euclidean_halfSpace_dist_sq_le (flat : E → X) {x y : X} {u v : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ w, dist x (flat w) ^ 2 = dist u w ^ 2 + a ^ 2)
    (hy : ∀ w, dist y (flat w) ^ 2 = dist v w ^ 2 + b ^ 2) :
    dist u v ^ 2 + (a - b) ^ 2 ≤ dist x y ^ 2 := by
  have root {q : X} {v : E} {c : ℝ}
      (hq : ∀ w, dist q (flat w) ^ 2 = dist v w ^ 2 + c ^ 2) (w : E) :
      dist q (flat w) = Real.sqrt (‖v - w‖ ^ 2 + c ^ 2) := by
    rw [← dist_eq_norm, ← hq, Real.sqrt_sq dist_nonneg]
  have h := euclidean_halfSpace_dist_le flat ha hb (root hx) (root hy)
  rw [← dist_eq_norm] at h
  simpa only [Real.sq_sqrt (by positivity : 0 ≤ dist u v ^ 2 + (a - b) ^ 2)] using (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mpr h
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace X]
def flatApexHull (a : E) (H : ℝ) : Set (WithLp 2 (E × ℝ)) :=
  convexHull ℝ (insert (WithLp.toLp 2 (a, H)) (range (fun v : E ↦ WithLp.toLp 2 (v, (0 : ℝ)))))
theorem flatApexHull_base_mem (a : E) (H : ℝ) (v : E) :
    WithLp.toLp 2 (v, (0 : ℝ)) ∈ flatApexHull a H :=
  subset_convexHull _ _ (mem_insert_of_mem _ ⟨v, rfl⟩)
theorem flatApexHull_apex_mem (a : E) (H : ℝ) :
    WithLp.toLp 2 (a, H) ∈ flatApexHull a H :=
  subset_convexHull _ _ (mem_insert _ _)
private theorem horizontal_convex :
    Convex ℝ (range (fun v : E ↦ WithLp.toLp 2 (v, (0 : ℝ)))) := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ c d _ _ _
  refine ⟨c • u + d • v, ?_⟩
  apply WithLp.ofLp_injective
  simp
private theorem flatApexHull_segment (a : E) (H : ℝ) (z : flatApexHull a H) :
    ∃ v : E, ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap (WithLp.toLp 2 (a,H))
      (WithLp.toLp 2 (v, (0 : ℝ))) t = z.val := by
  have hz : z.val ∈ convexHull ℝ (insert (WithLp.toLp 2 (a, H))
      (range (fun v : E ↦ WithLp.toLp 2 (v, (0 : ℝ))))) := z.property
  rw [convexHull_insert (range_nonempty _), horizontal_convex.convexHull_eq,
    mem_convexJoin] at hz
  rcases hz with ⟨_, rfl : _ = _, _, ⟨v, rfl⟩, hz⟩
  rw [segment_eq_image_lineMap] at hz
  exact ⟨v, hz⟩
private theorem model_ruling_dist_sq (a u v : E) (H s t : ℝ) :
    dist (AffineMap.lineMap (WithLp.toLp 2 (a, H)) (WithLp.toLp 2 (u, (0 : ℝ))) s)
      (AffineMap.lineMap (WithLp.toLp 2 (a, H)) (WithLp.toLp 2 (v, (0 : ℝ))) t) ^ 2 =
      dist (AffineMap.lineMap a u s) (AffineMap.lineMap a v t) ^ 2 +
        ((1 - s) * H - (1 - t) * H) ^ 2 := by
  simp only [dist_eq_norm, AffineMap.lineMap_apply_module, WithLp.prod_norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]
theorem flatApexHull_isometry_of_segments (g : E → X) (b : X) (a : E) (H : ℝ) (P : E → ℝ → X)
    (hzero : ∀ v, P v 0 = b) (hone : ∀ v, P v 1 = g v)
    (hdist : ∀ u v {s t : ℝ}, s ∈ Icc 0 1 → t ∈ Icc 0 1 →
      dist (P u s) (P v t) ^ 2 = dist (AffineMap.lineMap a u s) (AffineMap.lineMap a v t) ^ 2 +
        ((1 - s) * H - (1 - t) * H) ^ 2) :
    ∃ f : flatApexHull a H → X, Isometry f ∧
      (∀ v, f ⟨WithLp.toLp 2 (v, 0), flatApexHull_base_mem a H v⟩ = g v) ∧
      f ⟨WithLp.toLp 2 (a, H), flatApexHull_apex_mem a H⟩ = b := by
  choose foot frac hfrac hrep using flatApexHull_segment a H
  let f (z : flatApexHull a H) := P (foot z) (frac z)
  have metric (u v : E) {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
      dist (P u s) (P v t) =
        dist (AffineMap.lineMap (WithLp.toLp 2 (a,H)) (WithLp.toLp 2 (u, (0 : ℝ))) s)
          (AffineMap.lineMap (WithLp.toLp 2 (a,H)) (WithLp.toLp 2 (v, (0 : ℝ))) t) :=
    (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      ((hdist u v hs ht).trans (model_ruling_dist_sq a u v H s t).symm)
  refine ⟨f, Isometry.of_dist_eq (fun x y ↦ ?_), ?_, ?_⟩
  · change dist (f x) (f y) = dist x.val y.val
    simpa only [f, hrep] using metric (foot x) (foot y) (hfrac x) (hfrac y)
  · intro v
    let z : flatApexHull a H := ⟨_, flatApexHull_base_mem a H v⟩
    have h := metric (foot z) v (hfrac z) (right_mem_Icc.mpr zero_le_one)
    rw [hrep, AffineMap.lineMap_apply_one, hone] at h
    exact dist_eq_zero.mp (h.trans (dist_self _))
  · let z : flatApexHull a H := ⟨_, flatApexHull_apex_mem a H⟩
    have h := metric (foot z) a (hfrac z) (left_mem_Icc.mpr zero_le_one)
    rw [hrep, AffineMap.lineMap_apply_zero, hzero] at h
    exact dist_eq_zero.mp (h.trans (dist_self _))
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set SharpIntegralFillings
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MetricSpace X]
theorem cat0_segment_pair_dist_sq (hX : IsCAT0 X) {g : E → X} (hg : Isometry g)
    {b P Q : X} {a u v : E} {H s t : ℝ} (hH : 0 ≤ H)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : ∀ w, dist b (g w) ^ 2 = dist a w ^ 2 + H ^ 2)
    (hPb : dist b P = s * dist b (g u)) (hPu : dist (g u) P = (1 - s) * dist b (g u))
    (hQb : dist b Q = t * dist b (g v)) (hQv : dist (g v) Q = (1 - t) * dist b (g v)) :
    dist P Q ^ 2 = dist (AffineMap.lineMap a u s) (AffineMap.lineMap a v t) ^ 2 +
      ((1 - s) * H - (1 - t) * H) ^ 2 := by
  have dP := cat0_segment_dist_flat_sq hX hg hs hb hPb hPu
  have dQ := cat0_segment_dist_flat_sq hX hg ht hb hQb hQv
  apply le_antisymm _ (euclidean_halfSpace_dist_sq_le g
    (mul_nonneg (sub_nonneg.mpr hs.2) hH) (mul_nonneg (sub_nonneg.mpr ht.2) hH) dP dQ)
  obtain ⟨γ, _, hγ⟩ := hX.exists_squared_distance_convex
  have hc := hγ b (g v) P t ht
  rw [cat0_eq_fraction_point hγ ht hQb hQv, dist_comm Q P, hPb, mul_pow, hb u,
    dist_comm (g v) P, dP v, hb v] at hc
  rw [dist_comm (AffineMap.lineMap a u s), euclidean_dist_lineMap_sq _ _ _ ht,
    dist_left_lineMap, Real.norm_of_nonneg hs.1, dist_comm v]
  linarith
theorem cat0_flatApexHull_isometry (hX : IsCAT0 X) {g : E → X} (hg : Isometry g)
    (b : X) (a : E) (H : ℝ) (hH : 0 ≤ H)
    (hb : ∀ w, dist b (g w) ^ 2 = dist a w ^ 2 + H ^ 2) :
    ∃ f : flatApexHull a H → X, Isometry f ∧
      (∀ v, f ⟨WithLp.toLp 2 (v, 0), flatApexHull_base_mem a H v⟩ = g v) ∧
      f ⟨WithLp.toLp 2 (a, H), flatApexHull_apex_mem a H⟩ = b := by
  obtain ⟨γ, hends, hd, _⟩ := id hX
  have start (v : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      dist b (γ b (g v) t) = t * dist b (g v) := by
    have h := hd b (g v) 0 t (by simp) ht
    simpa [(hends b (g v)).1, abs_of_nonneg ht.1] using h
  have finish (v : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (g v) (γ b (g v) t) = (1 - t) * dist b (g v) := by
    have h := hd b (g v) 1 t (by simp) ht
    simpa [(hends b (g v)).2, abs_of_nonneg (sub_nonneg.mpr ht.2)] using h
  exact flatApexHull_isometry_of_segments g b a H (fun v t ↦ γ b (g v) t)
    (fun v ↦ (hends b (g v)).1) (fun v ↦ (hends b (g v)).2)
    (fun u v _ _ hs ht ↦ cat0_segment_pair_dist_sq hX hg hH hs ht hb
      (start u hs) (finish u hs) (start v ht) (finish v ht))
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Book
open HyperbolicObstruction Filter Set
open scoped Topology RealInnerProductSpace
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (ω : Ultrafilter ℕ) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) {U : Set E} {φ : E → X} (hφ : ∀ u ∈ U, ∀ z ∈ U, dist (φ u) (φ z) = dist u z) {y : E} (hy : U ∈ 𝓝 y)
noncomputable def pageSection (v : E) : BlowupSection ω hs (φ y) := by
  classical
  refine ⟨fun n ↦ ⟨if y + s n • v ∈ U then φ (y + s n • v) else φ y⟩, ‖v‖, fun n ↦ ?_⟩
  rw [MetricScale.dist_eq]
  dsimp only
  split_ifs with hn
  · rw [hφ y (mem_of_mem_nhds hy) _ hn, dist_comm, dist_eq_norm]
    simp [norm_smul, Real.norm_of_nonneg (hs n).le, (hs n).ne']
  · simp
noncomputable def tangentFlat (v : E) : Blowup ω hs (φ y) :=
  MetricLimit.point (pageSection ω hs hφ hy v)
variable (hX : CATZero X) (x : X) {M : ℝ} (hM : 0 ≤ M)
noncomputable def raySection : BlowupSection ω hs (φ y) := by
  classical
  refine ⟨fun n ↦ ⟨if s n * M ≤ 1 then CATZero.segment hX (φ y) x (s n * M) else φ y⟩,
    M * dist (φ y) x, fun n ↦ ?_⟩
  rw [MetricScale.dist_eq]
  dsimp only
  split_ifs with hn
  · rw [CATZero.segment_left hX (φ y) x ⟨mul_nonneg (hs n).le hM, hn⟩]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (hs n).ne', one_mul]
  · simpa using mul_nonneg hM (dist_nonneg (x := φ y) (y := x))
noncomputable def tangentRayPoint : Blowup ω hs (φ y) :=
  MetricLimit.point (raySection ω hs hX x hM)
variable (hω : (ω : Filter ℕ) ≤ atTop) (h₀ : Tendsto s atTop (𝓝 0))
include hy h₀ in
private theorem eventually_in_patch (v : E) : ∀ᶠ n in atTop, y + s n • v ∈ U := by
  have hlim : Tendsto (fun n ↦ y + s n • v) atTop (𝓝 y) := by
    simpa using (h₀.smul_const v).const_add y
  exact hlim hy
include hω h₀ in
theorem isometry_tangentFlat : Isometry (tangentFlat ω hs hφ hy) := by
  classical
  apply Isometry.of_dist_eq
  intro v w
  apply tendsto_nhds_unique (MetricLimit.tendsto_point_dist _ _)
  apply (tendsto_const_nhds (x := dist v w)).congr'
  filter_upwards [hω (eventually_in_patch hy h₀ v), hω (eventually_in_patch hy h₀ w)]
    with n hv hw
  rw [MetricScale.dist_eq]
  dsimp only [pageSection]
  rw [ite_eq_left hv, ite_eq_left hw, hφ _ hv _ hw, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub,
    ← smul_sub, norm_smul, Real.norm_of_nonneg (hs n).le, ← mul_assoc,
    inv_mul_cancel₀ (hs n).ne', one_mul]
include hω h₀ in
theorem tangentRayPoint_dist_tangentFlat [CompleteSpace E] {g : E}
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) (v : E) :
    dist (tangentRayPoint (φ := φ) (y := y) ω hs hX x hM) (tangentFlat ω hs hφ hy v) =
      dist (M • liftedDirection g (dist (φ y) x)) (horizontal v) := by
  classical
  apply tendsto_nhds_unique (MetricLimit.tendsto_point_dist _ _)
  have hpos : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h₀, Eventually.of_forall hs⟩
  have ht := (tendsto_tangent_dist hX hφ hy x hg v hM).comp (hpos.mono_left hω)
  apply ht.congr'
  have hscale : Tendsto (fun n ↦ s n * M) atTop (𝓝 0) := by simpa using h₀.mul_const M
  filter_upwards [hω (eventually_in_patch hy h₀ v), hω (hscale.eventually_lt_const zero_lt_one)]
    with n hv hn
  rw [MetricScale.dist_eq]
  dsimp only [pageSection, raySection, Function.comp_apply]
  rw [ite_eq_left hv, ite_eq_left hn.le, div_eq_inv_mul]
include hω h₀ in
theorem exists_tangentHull_isometry [CompleteSpace E] {g : E}
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) :
    let A := M • liftedDirection g (dist (φ y) x)
    ∃ F : flatApexHull A.fst A.snd → Blowup ω hs (φ y), Isometry F ∧
      (∀ v, F ⟨horizontal v, flatApexHull_base_mem _ _ v⟩ = tangentFlat ω hs hφ hy v) ∧
      F ⟨A, flatApexHull_apex_mem _ _⟩ = tangentRayPoint (φ := φ) (y := y) ω hs hX x hM := by
  let A := M • liftedDirection g (dist (φ y) x)
  refine cat0_flatApexHull_isometry (isCAT0_of_catZero (blowup_catZero hX ω hs (φ y)))
    (isometry_tangentFlat ω hs hφ hy hω h₀) _ A.fst A.snd ?_ ?_
  · change 0 ≤ M * (dist (φ y) x * Real.sqrt (1 - ‖g‖ ^ 2))
    positivity
  · intro v
    rw [tangentRayPoint_dist_tangentFlat ω hs hφ hy hX x hM hω h₀ hg v]
    change dist A (horizontal v) ^ 2 = _
    rw [WithLp.prod_dist_eq_of_L2, Real.sq_sqrt (by positivity)]
    simp [horizontal]
include hω h₀ in
theorem exists_tangentHull_spectralPrices [CompleteSpace E] {K : Type*} [Field K]
    (P : SpectralPlacementPrices K X) {g : E}
    (hg : HasGradientAt (fun u ↦ dist (φ u) x) g y) :
    let A := M • liftedDirection g (dist (φ y) x)
    ∃ (F : flatApexHull A.fst A.snd → Blowup ω hs (φ y))
      (Q : SpectralPlacementPrices K (flatApexHull A.fst A.snd)), Isometry F ∧
      (∀ v, F ⟨horizontal v, flatApexHull_base_mem _ _ v⟩ = tangentFlat ω hs hφ hy v) ∧
      F ⟨A, flatApexHull_apex_mem _ _⟩ = tangentRayPoint (φ := φ) (y := y) ω hs hX x hM ∧
      ∀ {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I K) (p : I → flatApexHull A.fst A.snd)
        (z : I → BlowupSection ω hs (φ y)), (∀ i, MetricLimit.point (z i) = F (p i)) →
        Tendsto (fun n ↦ P.price T (fun i ↦ ((z i).val n).val) / s n) (ω : Filter ℕ)
          (𝓝 (Q.price T p)) := by
  obtain ⟨F, hF, hb, ha⟩ := exists_tangentHull_isometry ω hs hφ hy hX x hM hω h₀ hg
  refine ⟨F, (blowupSpectralPrices ω hs (φ y) P).pullback F hF, hF, hb, ha, ?_⟩
  intro I _ T p z hz
  have h := tendsto_blowupSpectralPrices ω hs (φ y) P T z
  rwa [show MetricLimit.point ∘ z = F ∘ p from funext hz] at h
end Book
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set HyperbolicObstruction
def QuadraticRaySectors (X : Type*) [MetricSpace X] : Prop :=
  ∀ (a b : ℝ → X) (A B c : ℝ), a 0 = b 0 →
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → dist (a s) (a t) = |s - t| * A) →
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → dist (b s) (b t) = |s - t| * B) →
    (∀ t : ℝ, 0 ≤ t → dist (a t) (b t) = t * c) →
    ∀ T : ℝ, 0 < T → dist (a T) (b 1) ^ 2 =
      (T * A) ^ 2 + B ^ 2 + T * (c ^ 2 - A ^ 2 - B ^ 2)
theorem midpoint_bound_of_opposite_sectors {Y : Type*} [MetricSpace Y]
    (a b : ℝ → Y) (z : Y) (A B c d : ℝ)
    (hab : ∀ T : ℝ, 0 < T → dist (a T) (b T) = 2 * T * A)
    (hac : ∀ T : ℝ, 0 < T → dist (a T) z ^ 2 =
      (T * A) ^ 2 + B ^ 2 + T * (c ^ 2 - A ^ 2 - B ^ 2))
    (hbc : ∀ T : ℝ, 0 < T → dist (b T) z ^ 2 =
      (T * A) ^ 2 + B ^ 2 + T * (d ^ 2 - A ^ 2 - B ^ 2)) :
    2 * A ^ 2 + 2 * B ^ 2 ≤ c ^ 2 + d ^ 2 := by
  by_contra! hfail
  let gap := 2 * A ^ 2 + 2 * B ^ 2 - (c ^ 2 + d ^ 2)
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let T := 1 + 2 * B ^ 2 / gap
  have hT : 0 < T := by dsimp [T]; positivity
  have hlarge : T * gap = gap + 2 * B ^ 2 := by
    dsimp [T]
    rw [add_mul, one_mul, div_mul_cancel₀ _ hgap.ne']
  have htri := dist_triangle (a T) z (b T)
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr htri
  rw [hab T hT, dist_comm z (b T)] at hsq
  have hs : (2 * T * A) ^ 2 ≤
      2 * (dist (a T) z ^ 2 + dist (b T) z ^ 2) := by
    nlinarith [sq_nonneg (dist (a T) z - dist (b T) z)]
  rw [hac T hT, hbc T hT] at hs
  dsimp only [gap] at hlarge
  nlinarith
variable {X : Type*} [MetricSpace X]
theorem opposite_segment_separation {x y m : X} {a b : ℝ → X}
    (ha : IsSegment a m x) (hb : IsSegment b m y)
    (hm : dist m x + dist m y = dist x y) {s : ℝ} (hs : s ∈ Icc 0 1) :
    dist (a s) (b s) = s * dist x y := by
  have hax := ha.2.2 s hs 1 (by norm_num)
  have hby := hb.2.2 s hs 1 (by norm_num)
  rw [ha.2.1, abs_of_nonpos (sub_nonpos.mpr hs.2)] at hax
  rw [hb.2.1, abs_of_nonpos (sub_nonpos.mpr hs.2)] at hby
  have h := dist_triangle (a s) m (b s)
  rw [dist_comm (a s) m, ha.dist_from_source hs, hb.dist_from_source hs] at h
  have h' := dist_triangle4 x (a s) (b s) y
  rw [dist_comm x (a s), hax, hby] at h'
  rw [← hm]
  nlinarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset
abbrev State := Finset ℕ
def weight (S : State) : ℕ := ∑ i ∈ S, (2*i + 1)
theorem mode_lt_weight {S : State} {i : ℕ} (hi : i ∈ S) : i < weight S := by
  have h := Finset.single_le_sum (f := fun j : ℕ ↦ 2*j+1) (fun _ _ ↦ Nat.zero_le _) hi
  unfold weight
  omega
theorem card_le_weight (S : State) : S.card ≤ weight S := by
  simpa only [weight, sum_const, smul_eq_mul, mul_one] using
    Finset.sum_le_sum (s := S) (f := fun _ : ℕ ↦ 1) (g := fun j ↦ 2*j+1)
      (fun i _ ↦ by omega)
def states (B : ℤ) : Finset State := ((range B.toNat).powerset).filter (fun S ↦ (weight S : ℤ) ≤ B)
@[simp] theorem mem_states {S : State} {B : ℤ} : S ∈ states B ↔ (weight S : ℤ) ≤ B := by
  simp only [states, mem_filter, mem_powerset, and_iff_right_iff_imp]
  intro h i hi
  apply mem_range.mpr
  exact (mode_lt_weight hi).trans_le (by omega)
abbrev Label (H : ℕ) := ↥((states H).erase ∅)
@[simp] theorem empty_mem_states_nat (H : ℕ) : ∅ ∈ states (H : ℤ) := by
  simp [weight]
theorem label_nonempty {H : ℕ} (i : Label H) : i.val.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase i.property)
theorem label_weight_le {H : ℕ} (i : Label H) : weight i.val ≤ H := by
  have h := mem_states.mp (Finset.mem_of_mem_erase i.property)
  exact_mod_cast h
theorem card_label (H : ℕ) : Fintype.card (Label H) = (states H).card - 1 := by
  simp [Label, Finset.card_erase_of_mem (empty_mem_states_nat H)]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open Finset
open scoped BigOperators Classical
abbrev ModeMatrix := State → ℤ → State → State → ℤ
def order (w v : ℕ) := (w+v)/2 - 1
def multiplier (L a : ℕ) : ℤ := (-1)^a * (L.choose a : ℤ)
abbrev PlusStates (H E : ℕ) (s : ℤ) := ↥(states (E+H+2*s))
abbrev MinusStates (H E : ℕ) (s : ℤ) := ↥(states (E+H-2*s))
def CoefficientIdentity (C : State → State → ℤ) (Y : ModeMatrix) : Prop :=
  ∀ (H E : ℕ) (s : ℤ) (i j : Label H) (_ : i.val.card = j.val.card)
    (α β : ↥(states (E : ℤ))),
    let L := order (weight i.val) (weight j.val)
    C i.val j.val * (if α = β then 1 else 0) =
      ∑ a : Fin (H+1), multiplier L a *
        ((∑ k : PlusStates H E s,
            Y i.val (-s-1-L+a) α.val k.val * Y j.val (s-a) k.val β.val) -
          (-1)^(i.val.card*j.val.card) * ∑ k : MinusStates H E s,
            Y j.val (s-a) α.val k.val * Y i.val (-s-1-L+a) k.val β.val)
structure Factors (I A P M : Type*) where
  plusLeft : I → A → P → ℤ
  plusRight : I → A → P → ℤ
  minusLeft : I → A → M → ℤ
  minusRight : I → A → M → ℤ
def Factors.entry {I A P M : Type*} [Fintype P] [Fintype M] (F : Factors I A P M)
    (i j : I) (α β : A) : ℤ :=
  (∑ k, F.plusLeft i α k * F.plusRight j β k) +
    ∑ k, F.minusLeft i β k * F.minusRight j α k
abbrev BlockTag (H : ℕ) := Fin (H+1) × Fin (H+1)
private def tag {H : ℕ} (j : Label H) : BlockTag H :=
  (⟨j.val.card, Nat.lt_succ_of_le ((card_le_weight j.val).trans (label_weight_le j))⟩,
   ⟨weight j.val, Nat.lt_succ_of_le (label_weight_le j)⟩)
abbrev Channel (H : ℕ) (K : Type*) := BlockTag H × (Fin (H+1) × K)
theorem card_channel (H : ℕ) (K : Type*) [Fintype K] :
    Fintype.card (Channel H K) = (H+1)^3 * Fintype.card K := by
  simp only [Channel, BlockTag, Fintype.card_prod, Fintype.card_fin]
  ring
private def split (Y : ModeMatrix) (H E : ℕ) (s : ℤ) :
    Factors (Label H) ↥(states (E : ℤ))
      (Channel H (PlusStates H E s)) (Channel H (MinusStates H E s)) where
  plusLeft i α k :=
    let L := order (weight i.val) k.1.2.val
    if i.val.card = k.1.1.val then
      multiplier L k.2.1 * Y i.val (-s-1-L+k.2.1) α.val k.2.2.val else 0
  plusRight j β k :=
    if k.1 = tag j then Y j.val (s-k.2.1) k.2.2.val β.val else 0
  minusLeft i β k :=
    let L := order (weight i.val) k.1.2.val
    if i.val.card = k.1.1.val then
      -multiplier L k.2.1 * (-1)^(i.val.card*k.1.1.val) *
        Y i.val (-s-1-L+k.2.1) k.2.2.val β.val else 0
  minusRight j α k :=
    if k.1 = tag j then Y j.val (s-k.2.1) α.val k.2.2.val else 0
private theorem split_entry {C : State → State → ℤ} {Y : ModeMatrix}
    (h : CoefficientIdentity C Y)
    (hzero : ∀ i j : State, i.card ≠ j.card → C i j = 0)
    {H E : ℕ} {s : ℤ} (i j : Label H) (α β : ↥(states (E : ℤ))) :
    (split Y H E s).entry i j α β = C i.val j.val * (if α = β then 1 else 0) := by
  unfold Factors.entry split
  dsimp only
  conv_lhs => simp only [Channel, mul_ite, mul_zero, Fintype.sum_prod_type, Prod.ext_iff, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, tag]
  by_cases he : i.val.card = j.val.card
  · simp only [ite_eq_left he]
    rw [h H E s i j he α β, ← sum_add_distrib]
    refine sum_congr rfl (fun a _ ↦ ?_)
    simp only [mul_sub, mul_sum]
    congr 1
    · exact sum_congr rfl (fun _ _ ↦ by ring)
    · rw [← Finset.sum_neg_distrib]
      exact sum_congr rfl (fun _ _ ↦ by ring)
  · simp [he, hzero i.val j.val he]
def Factors.rowMap {I A P M : Type*} [Fintype I] (F : Factors I A P M) (B : Matrix I I ℤ) :
    Factors I A P M where
  plusLeft i α k := ∑ l, B i l * F.plusLeft l α k
  plusRight := F.plusRight
  minusLeft i β k := ∑ l, B i l * F.minusLeft l β k
  minusRight := F.minusRight
theorem Factors.rowMap_entry {I A P M : Type*} [Fintype I] [Fintype P] [Fintype M]
    (F : Factors I A P M) (B : Matrix I I ℤ) (i j : I) (α β : A) :
    (F.rowMap B).entry i j α β = ∑ l, B i l * F.entry l j α β := by
  simp only [Factors.rowMap, Factors.entry, sum_mul, mul_add, mul_sum, mul_assoc, sum_add_distrib]
  congr 1 <;> rw [sum_comm]
theorem exists_integral_factors {C : State → State → ℤ} {Y : ModeMatrix}
    (h : CoefficientIdentity C Y)
    (hzero : ∀ i j : State, i.card ≠ j.card → C i j = 0)
    (H E : ℕ) (s : ℤ) (B : Matrix (Label H) (Label H) ℤ)
    (hB : B * (Matrix.of fun i j : Label H ↦ C i.val j.val) = 1) :
    ∃ F : Factors (Label H) ↥(states (E : ℤ)) (Channel H (PlusStates H E s))
      (Channel H (MinusStates H E s)),
      ∀ i j α β, F.entry i j α β = if i=j ∧ α=β then 1 else 0 := by
  refine ⟨(split Y H E s).rowMap B, fun i j α β ↦ ?_⟩
  rw [Factors.rowMap_entry]
  simp_rw [split_entry h hzero, ← mul_assoc]
  rw [← sum_mul]
  change ((B * (Matrix.of fun i j : Label H ↦ C i.val j.val)) i j) * _ = _
  rw [hB, Matrix.one_apply]
  split_ifs <;> simp_all
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Matrix Finset
noncomputable def stateMinor (f : ℕ → ℕ → ℤ) (I J : Finset ℕ) : ℤ :=
  if h : J.card = I.card then
    (Matrix.of fun i j : Fin I.card ↦ f (I.orderEmbOfFin rfl i) (J.orderEmbOfFin h j)).det
  else 0
noncomputable def pascalMinor := stateMinor (fun i j ↦ (i.choose j : ℤ))
def pairingSign (I : Finset ℕ) : ℤ := (-1) ^ (I.card.choose 2 + ∑ i ∈ I, i)
noncomputable def pairing (I J : Finset ℕ) : ℤ :=
  pairingSign I * stateMinor (fun i j ↦ ((i+j).choose i : ℤ)) I J
theorem pascal_gram_entry {N i j : ℕ} (hi : i < N) :
    (∑ k ∈ range N, (i.choose k : ℤ) * (j.choose k : ℤ)) = ((i + j).choose i : ℤ) := by
  have hN : (∑ k ∈ range N, i.choose k * j.choose k) =
      ∑ k ∈ range (i+1), i.choose k * j.choose k := by
    symm
    apply sum_subset_zero_on_sdiff (range_mono hi) <;> simp_all [Nat.choose_eq_zero_of_lt]
  exact_mod_cast hN.trans (by
    rw [Nat.add_comm i j, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply sum_congr rfl
    intro k hk
    rw [Nat.choose_symm (mem_range_succ_iff.mp hk), mul_comm])
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset
open scoped BigOperators
def wedgeSign (r : ℕ) (S : State) : ℤ := (-1) ^ (S.filter (· < r)).card
def negativeChoose (r j : ℕ) : ℤ := (-1) ^ j * ((r+j).choose j : ℤ)
def listMode : List ℕ → ℤ → State → State → ℤ
  | [], b, α, β => if b = 0 ∧ α = β then 1 else 0
  | j :: l, b, α, β =>
      (∑ r ∈ α, (r.choose j : ℤ) * wedgeSign r α *
        listMode l (b-r+j) (α.erase r) β) +
      (-1) ^ l.length * ∑ r ∈ β, negativeChoose r j * wedgeSign r β *
        listMode l (b+r+1+j) α (β.erase r)
def blockMode (I : State) := listMode (I.sort (· ≤ ·))
private theorem weight_erase_add {s : State} {r : ℕ} (hr : r ∈ s) :
    weight (s.erase r) + (2*r+1) = weight s := by
  exact Finset.sum_erase_add _ _ hr
def listWeight (l : List ℕ) := (l.map (fun r ↦ 2*r+1)).sum
theorem weight_eq_of_listMode_ne_zero {l : List ℕ} {b : ℤ} {α β : State}
    (h : listMode l b α β ≠ 0) : (weight α : ℤ) = weight β + 2*b + listWeight l := by
  induction l generalizing b α β with
  | nil =>
    have he : b = 0 ∧ α = β := by simpa [listMode] using h
    simp [he.1, he.2, listWeight]
  | cons j l ih =>
    rw [listMode] at h
    have step {x y : ℤ} (hne : x + y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by omega
    rw [show listWeight (j :: l) = 2*j+1 + listWeight l from rfl]
    rcases step h with hc | ha
    · obtain ⟨r, hr, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
      have htail := ih ((mul_ne_zero_iff.mp hterm).2)
      have hw := weight_erase_add hr
      omega
    · obtain ⟨r, hr, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ((mul_ne_zero_iff.mp ha).2)
      have htail := ih ((mul_ne_zero_iff.mp hterm).2)
      have hw := weight_erase_add hr
      omega
private theorem listWeight_sort (I : State) : listWeight (I.sort (· ≤ ·)) = weight I := by
  change (Multiset.map (fun r : ℕ ↦ 2*r+1) (I.sort (· ≤ ·) : Multiset ℕ)).sum = _
  rw [Finset.sort_eq]
  rfl
theorem weight_eq_of_blockMode_ne_zero {I α β : State} {b : ℤ}
    (h : blockMode I b α β ≠ 0) : (weight α : ℤ) = weight β + 2*b + weight I := by
  simpa only [listWeight_sort] using weight_eq_of_listMode_ne_zero h
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset Filter
open scoped BigOperators
def TruncatedIdentity : Prop :=
  ∀ (i j α β : State) (_ : i.Nonempty) (_ : i.card = j.card) (s : ℤ),
    let L := order (weight i) (weight j)
    ∀ᶠ N : ℕ in atTop,
      pairing i j * (if α = β then 1 else 0) =
        ∑ a ∈ range (L+1), multiplier L a *
          ((∑ k ∈ (range N).powerset, blockMode i (-s-1-L+a) α k * blockMode j (s-a) k β) -
            (-1)^(i.card*j.card) * ∑ k ∈ (range N).powerset,
              blockMode j (s-a) α k * blockMode i (-s-1-L+a) k β)
private theorem states_subset {B : ℤ} {N : ℕ} (hN : B ≤ N) :
    states B ⊆ (range N).powerset := by
  intro S hS
  apply mem_powerset.mpr
  intro i hi
  have hw := mem_states.mp hS
  exact mem_range.mpr ((mode_lt_weight hi).trans_le (by omega))
theorem coefficientIdentity_of_truncated (h : TruncatedIdentity) :
    CoefficientIdentity pairing blockMode := by
  intro H E s i j hij α β
  have hi := label_weight_le i
  have hj := label_weight_le j
  have hβ := mem_states.mp β.property
  let L := order (weight i.val) (weight j.val)
  have hL : L ≤ H := by dsimp [L, order]; omega
  obtain ⟨N, hN, hN'⟩ := ((h i.val j.val α.val β.val (label_nonempty i) hij s).and
    (eventually_ge_atTop (max (E+H+2*s).toNat (E+H-2*s).toNat))).exists
  let term (U V : Finset State) (a : ℕ) : ℤ := multiplier L a *
    ((∑ k ∈ U, blockMode i.val (-s-1-L+a) α.val k * blockMode j.val (s-a) k β.val) -
      (-1)^(i.val.card*j.val.card) * ∑ k ∈ V,
        blockMode j.val (s-a) α.val k * blockMode i.val (-s-1-L+a) k β.val)
  have hc : α = β ↔ α.val = β.val := Subtype.ext_iff
  rw [if_congr hc rfl rfl, hN]
  dsimp only
  trans ∑ a : Fin (H+1), term (states (E+H+2*s)) (states (E+H-2*s)) a.val
  swap
  · apply sum_congr rfl
    intro a _
    dsimp only [term]
    rw [sum_coe_sort (states (E+H+2*s)) (fun k ↦ blockMode i.val (-s-1-L+a) α.val k *
      blockMode j.val (s-a) k β.val),
      sum_coe_sort (states (E+H-2*s)) (fun k ↦ blockMode j.val (s-a) α.val k *
        blockMode i.val (-s-1-L+a) k β.val)]
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset_zero_on_sdiff (range_mono (Nat.succ_le_succ hL))
  · intro a ha
    have hla : L < a := by
      have hn := (mem_sdiff.mp ha).2
      simpa only [mem_range, not_lt, Nat.succ_le_iff] using hn
    simp [term, multiplier, Nat.choose_eq_zero_of_lt hla]
  · intro a ha
    have haL := mem_range_succ_iff.mp ha
    dsimp only [term]
    congr 1
    congr 1
    · apply (sum_subset (states_subset (B := E+H+2*s) (by omega)) ?_).symm
      intro k _ hk
      rw [mem_states] at hk
      by_cases hmk : blockMode j.val (s-a) k β.val = 0
      · simp [hmk]
      · have hw := weight_eq_of_blockMode_ne_zero hmk
        omega
    · congr 1
      apply (sum_subset (states_subset (B := E+H-2*s) (by omega)) ?_).symm
      intro k _ hk
      rw [mem_states] at hk
      by_cases hmk : blockMode i.val (-s-1-L+a) k β.val = 0
      · exact mul_eq_zero_of_right _ hmk
      · have hw := weight_eq_of_blockMode_ne_zero hmk
        omega
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Finset Real
noncomputable section
def fermionEnergy (s : Finset ℕ) : ℝ := ∑ i ∈ s, ((i : ℝ) + 1 / 2)
theorem Fermion.weight_eq_twice_energy (s : State) : (weight s : ℝ) = 2 * fermionEnergy s := by
  simp only [weight, fermionEnergy, Nat.cast_sum, Finset.mul_sum, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  exact Finset.sum_congr rfl fun i _ ↦ by ring
def fermionStates (H : ℝ) : Finset (Finset ℕ) := Fermion.states ⌊2 * H⌋
@[simp] theorem mem_fermionStates {s : Finset ℕ} {H : ℝ} :
    s ∈ fermionStates H ↔ fermionEnergy s ≤ H := by
  rw [fermionStates, Fermion.mem_states, Int.le_floor, Int.cast_natCast,
    Fermion.weight_eq_twice_energy]
  constructor <;> intro h <;> linarith
theorem Fermion.states_eq_fermionStates (B : ℤ) : states B = fermionStates ((B : ℝ) / 2) := by
  rw [fermionStates, show 2 * ((B : ℝ) / 2) = B by ring, Int.floor_intCast]
def fermionCount (H : ℝ) : ℕ := (fermionStates H).card
theorem fermionCount_pos {H : ℝ} (hH : 0 ≤ H) : 0 < fermionCount H :=
  Finset.card_pos.mpr ⟨∅, mem_fermionStates.mpr (by simpa [fermionEnergy] using hH)⟩
def fermionLogPartition (a : ℝ) : ℝ :=
  ∑' i : ℕ, Real.log (1 + Real.exp (-a * ((i : ℝ) + 1 / 2)))
private theorem summable_modeWeight {a : ℝ} (ha : 0 < a) :
    Summable (fun i : ℕ ↦ Real.exp (-a * ((i : ℝ) + 1 / 2))) :=
  Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr ha) (fun _ ↦ by linarith)
theorem summable_fermionWeight {a : ℝ} (ha : 0 < a) :
    Summable (fun s : Finset ℕ ↦ Real.exp (-a * fermionEnergy s)) := by
  simpa only [fermionEnergy, Finset.mul_sum, Real.exp_sum] using
    summable_finsetProd_of_summable_nonneg (fun i ↦ Real.exp_nonneg _) (summable_modeWeight ha)
theorem tsum_fermionWeight {a : ℝ} (ha : 0 < a) :
    ∑' s : Finset ℕ, Real.exp (-a * fermionEnergy s) = Real.exp (fermionLogPartition a) := by
  rw [fermionLogPartition, Real.rexp_tsum_eq_tprod (fun _ ↦ by positivity)
    (Real.summable_log_one_add_of_summable (summable_modeWeight ha)),
    tprod_one_add (summable_finsetProd_of_summable_nonneg (fun _ ↦ Real.exp_nonneg _)
      (summable_modeWeight ha))]
  simp only [fermionEnergy, Finset.mul_sum, Real.exp_sum]
theorem fermionCount_le_exp {a : ℝ} (ha : 0 < a) (H : ℝ) :
    (fermionCount H : ℝ) ≤ Real.exp (a * H + fermionLogPartition a) := by
  have hsum := (summable_fermionWeight ha).sum_le_tsum (fermionStates H)
    (fun s _ ↦ (Real.exp_pos _).le)
  rw [tsum_fermionWeight ha] at hsum
  have hmin : ∑ s ∈ fermionStates H, Real.exp (-a * H) ≤
      ∑ s ∈ fermionStates H, Real.exp (-a * fermionEnergy s) :=
    Finset.sum_le_sum fun s hs ↦ Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (mem_fermionStates.mp hs) (by linarith))
  have h := hmin.trans hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  rw [Real.exp_add]
  simpa [fermionCount, ← Real.exp_add, mul_assoc, mul_comm (Real.exp (a * H))] using
    mul_le_mul_of_nonneg_right h (Real.exp_pos (a * H)).le
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Real
open scoped Topology
private theorem exists_tilt_near_one {s c : ℝ} (hc : c < 2 * s) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ c < s * q + s * q ^ 3 := by
  have ht : Tendsto (fun q : ℝ ↦ s * q + s * q ^ 3) (𝓝[<] 1) (𝓝 (2 * s)) := by
    have h : Continuous (fun q : ℝ ↦ s * q + s * q ^ 3) := by fun_prop
    simpa [two_mul] using h.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Iio 1))
  have hp : ∀ᶠ q : ℝ in 𝓝[<] 1, 0 < q := nhdsWithin_le_nhds (eventually_gt_nhds zero_lt_one)
  have hlt : ∀ᶠ q : ℝ in 𝓝[<] 1, q < 1 := self_mem_nhdsWithin
  exact (hp.and (hlt.and (ht.eventually (eventually_gt_nhds hc)))).exists
theorem tendsto_log_fermionCount_div_sqrt_of_partition {A : ℝ} (hA : 0 < A)
    (hF : ∀ k : ℝ, 0 < k → Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X)
      atTop (𝓝 (A / k)))
    (hlower : ∀ q : ℝ, 0 < q → q < 1 → ∀ᶠ X : ℝ in atTop,
      fermionLogPartition ((√A / q) / X) + (√A * q ^ 3) * X - log 2 ≤
        log (fermionCount (X ^ 2))) :
    Tendsto (fun H : ℝ ↦ log (fermionCount H) / √H) atTop (𝓝 (2 * √A)) := by
  have hs : 0 < √A := sqrt_pos.mpr hA
  have hsq := sq_sqrt hA.le
  have hX : ∀ᶠ X : ℝ in atTop, 0 < X := eventually_gt_atTop 0
  have hscaled : Tendsto (fun X : ℝ ↦ log (fermionCount (X ^ 2)) / X) atTop (𝓝 (2 * √A)) := by
    apply tendsto_order.mpr
    constructor
    · intro c hc
      obtain ⟨q, hq, hq1, hqc⟩ := exists_tilt_near_one hc
      have hquot : A / (√A / q) = √A * q := by field_simp; nlinarith
      have hzero : Tendsto (fun X : ℝ ↦ log 2 / X) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have ht := ((hF (√A / q) (div_pos hs hq)).add_const (√A * q ^ 3)).sub hzero
      rw [hquot, sub_zero] at ht
      filter_upwards [ht.eventually (eventually_gt_nhds hqc), hlower q hq hq1, hX] with X h₁ h₂ hpos
      apply lt_of_lt_of_le h₁
      calc
        fermionLogPartition ((√A / q) / X) / X + √A * q ^ 3 - log 2 / X =
            (fermionLogPartition ((√A / q) / X) + (√A * q ^ 3) * X - log 2) / X := by
              field_simp
        _ ≤ _ := div_le_div_of_nonneg_right h₂ hpos.le
    · intro c hc
      have ht := (hF (√A) hs).const_add (√A)
      have heq : √A + A / √A = 2 * √A := by field_simp; nlinarith
      rw [heq] at ht
      filter_upwards [ht.eventually (eventually_lt_nhds hc), hX] with X hbound hpos
      apply lt_of_le_of_lt _ hbound
      have hcount : 0 < (fermionCount (X ^ 2) : ℝ) := by
        exact_mod_cast fermionCount_pos (sq_nonneg X)
      have hlog := (log_le_log hcount (fermionCount_le_exp (div_pos hs hpos) (X ^ 2)))
      rw [log_exp] at hlog
      calc
        log (fermionCount (X ^ 2)) / X ≤
            ((√A / X) * X ^ 2 + fermionLogPartition (√A / X)) / X :=
              div_le_div_of_nonneg_right hlog hpos.le
        _ = √A + fermionLogPartition (√A / X) / X := by field_simp
  apply (hscaled.comp Real.tendsto_sqrt_atTop).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp [Function.comp_apply, sq_sqrt hH]
theorem tendsto_logb_fermionCount_div_sqrt_of_log {L : ℝ}
    (h : Tendsto (fun H : ℝ ↦ log (fermionCount H) / √H) atTop (𝓝 L)) :
    Tendsto (fun H : ℝ ↦ logb 2 (fermionCount H) / √H) atTop (𝓝 (L / log 2)) := by
  simpa only [logb, div_right_comm (log _) (log 2)] using h.div_const (log 2)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open MeasureTheory Real Set Filter Topology
def fermionProfile (x : ℝ) : ℝ := log (1 + exp (-x))
def fermionFreeEnergy : ℝ := ∫ x in Ioi (0 : ℝ), fermionProfile x
theorem fermionProfile_pos (x : ℝ) : 0 < fermionProfile x :=
  log_pos (by simpa using exp_pos (-x))
private theorem antitone_fermionProfile : Antitone fermionProfile := by
  intro x y hxy
  exact log_le_log (by positivity) (add_le_add_right (exp_le_exp.mpr (neg_le_neg hxy)) 1)
private theorem summable_profile_nat {a : ℝ} (ha : 0 < a) :
    Summable (fun i : ℕ ↦ fermionProfile (a * i)) := by
  simpa only [fermionProfile, neg_mul] using Real.summable_log_one_add_of_summable
    (Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr ha) (fun i : ℕ ↦ le_refl (i : ℝ)))
private theorem integrable_profile_scaled {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ fermionProfile (a * x)) (Ioi 0) :=
  (antitone_fermionProfile.comp_monotone (fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha.le)).antitoneOn (Ici 0)
    |>.integrableOn_Ioi_zero_of_summable (summable_profile_nat ha) (fun x _ ↦ (fermionProfile_pos (a * x)).le)
theorem fermionFreeEnergy_pos : 0 < fermionFreeEnergy := by
  have hi : IntegrableOn fermionProfile (Ioi 0) := by
    simpa using integrable_profile_scaled zero_lt_one
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun x ↦ (fermionProfile_pos x).le) hi).mpr
  have hs : Function.support fermionProfile = univ :=
    Set.eq_univ_of_forall fun x ↦ (fermionProfile_pos x).ne'
  rw [hs, univ_inter]
  exact isOpen_Ioi.measure_pos volume nonempty_Ioi
theorem fermionLogPartition_integral_bounds {a : ℝ} (ha : 0 < a) :
    fermionFreeEnergy - a * fermionProfile 0 ≤ a * fermionLogPartition a ∧
    a * fermionLogPartition a ≤ fermionFreeEnergy + a * fermionProfile 0 := by
  let F (x : ℝ) := fermionProfile (a * x)
  have anti : Antitone F := antitone_fermionProfile.comp_monotone
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha.le)
  have nonneg (x : ℝ) : 0 ≤ F x := (fermionProfile_pos _).le
  have hs : Summable (fun i : ℕ ↦ F i) := summable_profile_nat ha
  have hm : Summable (fun i : ℕ ↦ F (i + 1 / 2)) :=
    hs.of_nonneg_of_le (fun i ↦ nonneg _) (fun i ↦ anti (by linarith))
  have hl : ∑' i : ℕ, F (i + 1 / 2) ≤ ∑' i : ℕ, F i :=
    hm.tsum_le_tsum (fun i ↦ anti (by linarith)) hs
  have hr : ∑' i : ℕ, F (i + 1 : ℕ) ≤ ∑' i : ℕ, F (i + 1 / 2) :=
    (summable_nat_add_iff 1 |>.mpr hs).tsum_le_tsum (fun i ↦ anti (by push_cast; linarith)) hm
  have h₁ := (anti.antitoneOn (Ici 0)).tsum_le_integral (integrable_profile_scaled ha) (fun x _ ↦ nonneg x)
  have h₂ := (anti.antitoneOn (Ici 0)).integral_le_tsum hs (fun x _ ↦ nonneg x)
  have heq := hs.tsum_eq_zero_add
  have hi : a * (∫ x in Ioi 0, F x) = fermionFreeEnergy := by
    simpa only [F, smul_eq_mul, mul_zero, fermionFreeEnergy] using
      integral_comp_mul_left_Ioi' fermionProfile 0 ha
  have hmEq : (∑' i : ℕ, F (i + 1 / 2)) = fermionLogPartition a := by
    simp only [F, fermionProfile, fermionLogPartition, neg_mul]
  have hF : F 0 = fermionProfile 0 := by simp [F]
  rw [← hmEq, ← hi, ← hF]
  constructor
  · rw [← mul_sub]
    apply mul_le_mul_of_nonneg_left _ ha.le
    change (∑' i : ℕ, F (i : ℝ)) = F (0 : ℕ) + ∑' i : ℕ, F (i + 1 : ℕ) at heq
    norm_cast at heq
    linarith
  · rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ ha.le
    linarith
theorem tendsto_fermionFreeEnergy :
    Tendsto (fun a : ℝ ↦ a * fermionLogPartition a) (𝓝[>] 0) (𝓝 fermionFreeEnergy) := by
  have h0 : Tendsto (fun a : ℝ ↦ a * fermionProfile 0) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).mul_const
      (fermionProfile 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using h0.const_sub fermionFreeEnergy) (by simpa using h0.const_add fermionFreeEnergy)
  · filter_upwards [self_mem_nhdsWithin] with a ha using (fermionLogPartition_integral_bounds ha).1
  · filter_upwards [self_mem_nhdsWithin] with a ha using (fermionLogPartition_integral_bounds ha).2
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
theorem eventually_exp_le_exp_div_of_rate {F G : ℝ → ℝ} {c : ℝ} (hc : c < 0)
    (h : Tendsto (fun X ↦ (F X - G X) / X) atTop (𝓝 c)) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ X in atTop, exp (F X) ≤ exp (G X) / d := by
  have hz : Tendsto (fun X : ℝ ↦ -log d / X) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (-log d)
  filter_upwards [h.eventually_lt hz hc, eventually_gt_atTop (0 : ℝ)] with X hX hpos
  have hsub := (div_lt_div_iff_of_pos_right hpos).mp hX
  rw [← exp_log hd, ← exp_sub]
  exact exp_le_exp.mpr (by linarith)
private theorem eventually_fermion_tilt {A k t w : ℝ} (hk : 0 < k) (ht : 0 < t)
    (hF : ∀ k : ℝ, 0 < k →
      Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X) atTop (𝓝 (A / k)))
    (hgap : (t - k) * w + A / t - A / k < 0) :
    ∀ᶠ X : ℝ in atTop, exp ((t / X - k / X) * (w * X ^ 2) + fermionLogPartition (t / X)) ≤
      exp (fermionLogPartition (k / X)) / 4 := by
  apply eventually_exp_le_exp_div_of_rate hgap _ (by norm_num)
  refine (((hF t ht).const_add ((t - k) * w)).sub (hF k hk)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  field_simp
theorem eventually_fermion_tilt_tails {A q : ℝ} (hA : 0 < A)
    (hF : ∀ k : ℝ, 0 < k →
      Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X) atTop (𝓝 (A / k)))
    (hq : 0 < q) (hq1 : q < 1) :
    let k := sqrt A / q
    let a := q * k
    let b := k / q
    ∀ᶠ X : ℝ in atTop, 0 < X ∧
      exp ((b / X - k / X) * (q ^ 4 * X ^ 2) + fermionLogPartition (b / X)) ≤
        exp (fermionLogPartition (k / X)) / 4 ∧
      exp ((a / X - k / X) * X ^ 2 + fermionLogPartition (a / X)) ≤
        exp (fermionLogPartition (k / X)) / 4 := by
  dsimp only
  let k := sqrt A / q
  have hk : 0 < k := div_pos (sqrt_pos.mpr hA) hq
  have hAk : A = (q * k) ^ 2 := by
    rw [show q * k = sqrt A by dsimp [k]; field_simp, sq_sqrt hA.le]
  have gap₁ : (k / q - k) * q ^ 4 + A / (k / q) - A / k < 0 := by
    rw [show (k / q - k) * q ^ 4 + A / (k / q) - A / k = -(1 - q) ^ 2 * k * q ^ 2 by
      rw [hAk]; field_simp; ring]
    have hp : 0 < (1 - q) ^ 2 * k * q ^ 2 := by positivity
    linarith
  have gap₂ : (q * k - k) * 1 + A / (q * k) - A / k < 0 := by
    rw [show (q * k - k) * 1 + A / (q * k) - A / k = -(1 - q) ^ 2 * k by
      rw [hAk]; field_simp; ring]
    have hp : 0 < (1 - q) ^ 2 * k := by positivity
    linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_fermion_tilt hk (div_pos hk hq) hF gap₁,
    eventually_fermion_tilt hk (mul_pos hq hk) hF gap₂] with X hX h₁ h₂
  exact ⟨hX, h₁, by simpa only [one_mul] using h₂⟩
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Real
theorem fermionPartition_le_window {a w b : ℝ} (ha : 0 < a) (haw : a < w) (hwb : w < b)
    (L H : ℝ) : exp (fermionLogPartition w) ≤
    exp ((b - w) * L + fermionLogPartition b) + fermionCount H * exp (-w * L) +
      exp ((a - w) * H + fermionLogPartition a) := by
  classical
  let mid (s : Finset ℕ) := if s ∈ fermionStates H then exp (-w * L) else 0
  have hm : HasSum mid ((fermionCount H : ℝ) * exp (-w * L)) := by
    have h := hasSum_sum_of_ne_finset_zero (L := .unconditional _) (s := fermionStates H) (f := mid)
      (fun s hs ↦ by simp only [mid, hs, ↓reduceIte])
    have hh : ∑ s ∈ fermionStates H, mid s = (fermionCount H : ℝ) * exp (-w * L) := calc
      _ = ∑ _s ∈ fermionStates H, exp (-w * L) :=
        Finset.sum_congr rfl (fun s hs ↦ by simp only [mid, hs, ↓reduceIte])
      _ = _ := by simp [fermionCount]
    exact hh ▸ h
  have hw (c : ℝ) (hc : 0 < c) : HasSum (fun s : Finset ℕ ↦ exp (-c * fermionEnergy s))
      (exp (fermionLogPartition c)) := tsum_fermionWeight hc ▸ (summable_fermionWeight hc).hasSum
  have hb := ((hw b (ha.trans (haw.trans hwb))).mul_left (exp ((b - w) * L)))
  have hr := ((hw a ha).mul_left (exp ((a - w) * H)))
  rw [exp_add, exp_add]
  apply hasSum_le _ (hw w (ha.trans haw)) ((hb.add hm).add hr)
  intro s
  have hmid : 0 ≤ mid s := by simp only [mid]; split <;> positivity
  have hlow : 0 ≤ exp ((b - w) * L) * exp (-b * fermionEnergy s) := by positivity
  have hhigh : 0 ≤ exp ((a - w) * H) * exp (-a * fermionEnergy s) := by positivity
  rcases le_total (fermionEnergy s) L with h | h
  · have he : -w * fermionEnergy s ≤ (b - w) * L + -b * fermionEnergy s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hwb.le) (sub_nonneg.mpr h)]
    have hh := Real.exp_le_exp.mpr he
    rw [exp_add] at hh
    linarith
  by_cases hs : fermionEnergy s ≤ H
  · have hle : exp (-w * fermionEnergy s) ≤ mid s := by
      simp only [mid, mem_fermionStates.mpr hs, ↓reduceIte]
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (by linarith))
    linarith
  · have he : -w * fermionEnergy s ≤ (a - w) * H + -a * fermionEnergy s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr haw.le) (sub_nonneg.mpr (le_of_not_ge hs))]
    have hh := Real.exp_le_exp.mpr he
    rw [exp_add] at hh
    linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Real
open scoped Topology
private theorem tendsto_fermionLogPartition_scaled (k : ℝ) (hk : 0 < k) :
    Tendsto (fun X : ℝ ↦ fermionLogPartition (k / X) / X) atTop (𝓝 (fermionFreeEnergy / k)) := by
  have ht : Tendsto (fun X : ℝ ↦ k / X) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.const_div_atTop k, (eventually_gt_atTop (0 : ℝ)).mono
      (fun _ hx ↦ div_pos hk hx)⟩
  refine ((tendsto_fermionFreeEnergy.comp ht).div_const k).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hx
  dsimp only [Function.comp_apply]
  field_simp
private theorem eventually_fermionCount_sqrt_lower (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∀ᶠ X : ℝ in atTop, fermionLogPartition ((√fermionFreeEnergy / q) / X) +
      (√fermionFreeEnergy * q ^ 3) * X - log 2 ≤ log (fermionCount (X ^ 2)) := by
  let k := √fermionFreeEnergy / q
  let a := q * k
  let b := k / q
  have hk : 0 < k := div_pos (sqrt_pos.mpr fermionFreeEnergy_pos) hq
  have ha : 0 < a := mul_pos hq hk
  have haw : a < k := by dsimp [a]; nlinarith [mul_pos (sub_pos.mpr hq1) hk]
  have hwb : k < b := (lt_div_iff₀ hq).mpr (by simpa [mul_comm] using haw)
  filter_upwards [eventually_fermion_tilt_tails fermionFreeEnergy_pos
    tendsto_fermionLogPartition_scaled hq hq1] with X ⟨hX, hlow, hhigh⟩
  have hwindow := fermionPartition_le_window (div_pos ha hX)
    ((div_lt_div_iff_of_pos_right hX).mpr haw) ((div_lt_div_iff_of_pos_right hX).mpr hwb)
    (q ^ 4 * X ^ 2) (X ^ 2)
  have half : exp (fermionLogPartition (k / X)) / 2 ≤
      (fermionCount (X ^ 2) : ℝ) * exp (-(k / X) * (q ^ 4 * X ^ 2)) := by
    linarith only [hwindow, hlow, hhigh]
  have key : -(k / X) * (q ^ 4 * X ^ 2) = -((√fermionFreeEnergy * q ^ 3) * X) := by
    dsimp [k]
    field_simp
  rw [key, exp_neg, ← div_eq_mul_inv, le_div_iff₀ (exp_pos _)] at half
  rw [le_log_iff_exp_le (by exact_mod_cast fermionCount_pos (sq_nonneg X)), exp_sub, exp_add,
    exp_log (by norm_num : (0 : ℝ) < 2)]
  linarith only [half]
theorem tendsto_log_fermionCount_div_sqrt :
    Tendsto (fun H : ℝ ↦ log (fermionCount H) / √H) atTop (𝓝 (2 * √fermionFreeEnergy)) :=
  tendsto_log_fermionCount_div_sqrt_of_partition fermionFreeEnergy_pos
    tendsto_fermionLogPartition_scaled eventually_fermionCount_sqrt_lower
theorem tendsto_logb_fermionCount_div_sqrt :
    Tendsto (fun H : ℝ ↦ logb 2 (fermionCount H) / √H) atTop
      (𝓝 (2 * √fermionFreeEnergy / log 2)) :=
  tendsto_logb_fermionCount_div_sqrt_of_log tendsto_log_fermionCount_div_sqrt
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Filter Real
open scoped Topology
theorem tendsto_label_log_of_states {H : ℕ → ℕ} {t : ℝ} (ht : 0 < t)
    (h : Tendsto (fun n : ℕ ↦ logb 2 ((states (H n)).card) / n) atTop (𝓝 t)) :
    Tendsto (fun n : ℕ ↦ logb 2 (Fintype.card (Label (H n))) / n) atTop (𝓝 t) := by
  have hcount : ∀ᶠ n : ℕ in atTop, 2 ≤ (states (H n)).card := by
    filter_upwards [h.eventually (eventually_gt_nhds ht)] with n hn
    by_contra! hsmall
    interval_cases (states (H n)).card <;> simp at hn
  have hbounds : ∀ᶠ n : ℕ in atTop,
      logb 2 (states (H n)).card - 1 ≤ logb 2 (Fintype.card (Label (H n))) ∧
      logb 2 (Fintype.card (Label (H n))) ≤ logb 2 (states (H n)).card := by
    filter_upwards [hcount] with n hn
    rw [card_label]
    have hc : (2 : ℝ) ≤ (states (H n)).card := by exact_mod_cast hn
    have hp : (0 : ℝ) < (states (H n)).card - 1 := by linarith
    rw [Nat.cast_sub (by omega : 1 ≤ (states (H n)).card), Nat.cast_one]
    constructor
    · have hhalf := logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
          (show 0 < ((states (H n)).card : ℝ) / 2 by positivity)
          (show ((states (H n)).card : ℝ) / 2 ≤ (states (H n)).card - 1 by linarith)
      simpa [logb_div (show ((states (H n)).card : ℝ) ≠ 0 by positivity) (by norm_num : (2 : ℝ) ≠ 0),
        logb_self_eq_one] using hhalf
    · exact logb_le_logb_of_le (by norm_num) hp (by linarith)
  have hlow := h.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  rw [sub_zero] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow h
  · filter_upwards [hbounds] with n hn
    simpa only [sub_div] using div_le_div_of_nonneg_right hn.1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  · filter_upwards [hbounds] with n hn
    exact div_le_div_of_nonneg_right hn.2 (Nat.cast_nonneg n)
theorem tendsto_logb_cube_overhead {H : ℕ → ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hH : ∀ n : ℕ, (H n : ℝ) ≤ q * (n : ℝ) ^ 2) :
    Tendsto (fun n : ℕ ↦ logb 2 ((H n + 1 : ℕ) ^ 3) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ logb 2 (n : ℝ) / n) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hup := (tendsto_const_div_atTop_nhds_zero_nat (logb 2 (q + 1))).add (hlog.const_mul 2)
  have hupper := hup.const_mul 3
  simp only [mul_zero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun n ↦ div_nonneg
      (logb_nonneg (by norm_num) (by exact_mod_cast (Nat.one_le_pow 3 _ (by omega) : 1 ≤ (H n + 1) ^ 3)))
      (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hq' : 0 < q + 1 := by linarith
    have hm := logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (show 0 < (H n : ℝ) + 1 by positivity)
      (show (H n : ℝ) + 1 ≤ (q + 1) * (n : ℝ) ^ 2 by nlinarith [hH n])
    rw [logb_mul hq'.ne' (by positivity), logb_pow] at hm
    push_cast
    rw [logb_pow]
    push_cast at hm ⊢
    have hh := div_le_div_of_nonneg_right hm (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simpa only [add_div, mul_div_assoc] using
      mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3)
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open Filter Real
open scoped Topology
private abbrev countCoefficient : ℝ := 2 * √fermionFreeEnergy / log 2
private theorem countCoefficient_pos : 0 < countCoefficient :=
  div_pos (mul_pos (by norm_num) (sqrt_pos.mpr fermionFreeEnergy_pos)) (log_pos (by norm_num))
private theorem tendsto_natCast_sq :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2) atTop atTop :=
  (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
private theorem tendsto_floor_scaled (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (⌊a * (n : ℝ) ^ 2⌋ : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 a) := by
  have he : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_sq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds.sub he)
    (tendsto_const_nhds (x := a))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : 0 < (n : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hn', sub_mul, inv_mul_cancel₀ hn'.ne']
    linarith [Int.lt_floor_add_one (a * (n : ℝ)^2)]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)
private theorem tendsto_states_log {B : ℕ → ℤ} {w : ℝ} (hw : 0 < w)
    (hB : Tendsto (fun n : ℕ ↦ (B n : ℝ) / 2 / (n : ℝ)^2) atTop
      (𝓝 (w / countCoefficient ^ 2))) :
    Tendsto (fun n : ℕ ↦ logb 2 ((states (B n)).card) / n) atTop (𝓝 (√w)) := by
  have hc := countCoefficient_pos
  let X (n : ℕ) : ℝ := (B n : ℝ) / 2
  have hp : 0 < w / countCoefficient ^ 2 := by positivity
  have hX : Tendsto X atTop atTop := by
    refine (hB.pos_mul_atTop hp tendsto_natCast_sq).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_mul_cancel₀ _ (by positivity)
  have hs : Tendsto (fun n : ℕ ↦ √(X n) / n) atTop (𝓝 (√w / countCoefficient)) := by
    simpa only [Real.sqrt_div (show 0 ≤ w from hw.le), Real.sqrt_sq hc.le,
      Real.sqrt_div' _ (sq_nonneg (_ : ℝ)), Real.sqrt_sq (Nat.cast_nonneg _)] using hB.sqrt
  have ha := (tendsto_logb_fermionCount_div_sqrt.comp hX).mul hs
  change Tendsto _ _ (𝓝 (countCoefficient * (√w / countCoefficient))) at ha
  rw [show countCoefficient * (√w / countCoefficient) = √w by rw [mul_comm, div_mul_cancel₀ _ hc.ne']] at ha
  refine ha.congr' ?_
  filter_upwards [hX.eventually_gt_atTop 0] with n hn
  change logb 2 (fermionCount (X n)) / √(X n) * (√(X n) / n) = _
  rw [states_eq_fermionStates]
  unfold fermionCount
  field_simp [ne_of_gt (sqrt_pos.mpr hn)]
  rfl
private def scaledCutoff (x : ℝ) (n : ℕ) : ℕ :=
  ⌊(2 * x ^ 2 / countCoefficient ^ 2) * (n : ℝ) ^ 2⌋₊
private def scaledShift (δ : ℝ) (n : ℕ) : ℤ :=
  ⌊(δ / countCoefficient ^ 2) * (n : ℝ) ^ 2⌋
private theorem scaledCutoff_le (x : ℝ) (n : ℕ) :
    (scaledCutoff x n : ℝ) ≤ (2 * x ^ 2 / countCoefficient ^ 2) * (n : ℝ)^2 :=
  Nat.floor_le (by positivity)
private theorem tendsto_scaledCutoff (x : ℝ) :
    Tendsto (fun n : ℕ ↦ (scaledCutoff x n : ℝ) / 2 / (n : ℝ)^2) atTop
      (𝓝 (x ^ 2 / countCoefficient ^ 2)) := by
  have h := ((tendsto_nat_floor_mul_div_atTop
    (show 0 ≤ 2 * x ^ 2 / countCoefficient ^ 2 by positivity)).comp tendsto_natCast_sq).div_const 2
  convert h using 1
  · funext n
    dsimp [scaledCutoff]
    ring
  · congr 1
    ring
private theorem tendsto_scaledShift (δ : ℝ) :
    Tendsto (fun n : ℕ ↦ (scaledShift δ n : ℝ) / (n : ℝ)^2) atTop
      (𝓝 (δ / countCoefficient ^ 2)) :=
  tendsto_floor_scaled _
private theorem tendsto_shifted_cutoffs (t u δ : ℝ) :
    Tendsto (fun n : ℕ ↦ (((scaledCutoff u n : ℤ) + scaledCutoff t n +
      2 * scaledShift δ n : ℤ) : ℝ) / 2 / (n : ℝ)^2) atTop
        (𝓝 ((t^2 + u^2 + δ) / countCoefficient ^ 2)) ∧
    Tendsto (fun n : ℕ ↦ (((scaledCutoff u n : ℤ) + scaledCutoff t n -
      2 * scaledShift δ n : ℤ) : ℝ) / 2 / (n : ℝ)^2) atTop
        (𝓝 ((t^2 + u^2 - δ) / countCoefficient ^ 2)) := by
  have h := (tendsto_scaledCutoff t).add (tendsto_scaledCutoff u)
  constructor
  · convert h.add (tendsto_scaledShift δ) using 1
    · funext n
      push_cast
      ring
    · congr 1
      ring
  · convert h.sub (tendsto_scaledShift δ) using 1
    · funext n
      push_cast
      ring
    · congr 1
      ring
private theorem eventually_dim_pos {D : ℕ → ℕ} {l : ℝ} (hl : 0 < l)
    (h : Tendsto (fun n : ℕ ↦ logb 2 (D n) / n) atTop (𝓝 l)) :
    ∀ᶠ n in atTop, 0 < D n := by
  filter_upwards [h.eventually_const_lt hl] with n hn
  by_contra! h
  simp [Nat.eq_zero_of_le_zero h] at hn
private theorem tendsto_logb_product {D Q : ℕ → ℕ} {w : ℝ} (hw : 0 < w)
    (hD : Tendsto (fun n : ℕ ↦ logb 2 (D n) / n) atTop (𝓝 w))
    (hQ : Tendsto (fun n : ℕ ↦ logb 2 (Q n) / n) atTop (𝓝 0)) (hq : ∀ n, 0 < Q n) :
    Tendsto (fun n : ℕ ↦ logb 2 (Q n * D n : ℕ) / n) atTop (𝓝 w) := by
  refine (by simpa using hQ.add hD : Tendsto _ _ (𝓝 w)).congr' ?_
  filter_upwards [eventually_dim_pos hw hD] with n hn
  simp only [Nat.cast_mul, logb_mul (b := 2) (x := (Q n : ℝ)) (y := (D n : ℝ))
    (by exact_mod_cast (hq n).ne') (by exact_mod_cast hn.ne'), add_div]
theorem exists_scaled_dimensions (t u δ : ℝ) (ht : 0 < t) (hu : 0 < u)
    (hlo : -(t^2 + u^2) < δ) (hhi : δ < t^2 + u^2) :
    ∃ (H E : ℕ → ℕ) (s : ℕ → ℤ),
      (∀ᶠ n in atTop, 0 < Fintype.card (Label (H n)) ∧ 0 < (states (E n)).card) ∧
      Tendsto (fun n : ℕ ↦ logb 2 (Fintype.card (Label (H n))) / n) atTop (𝓝 t) ∧
      Tendsto (fun n : ℕ ↦ logb 2 ((states (E n)).card) / n) atTop (𝓝 u) ∧
      Tendsto (fun n : ℕ ↦ logb 2 (((H n+1)^3 * (states ((E n : ℤ) + H n + 2*s n)).card : ℕ)) / n)
        atTop (𝓝 (√(t^2 + u^2 + δ))) ∧
      Tendsto (fun n : ℕ ↦ logb 2 (((H n+1)^3 * (states ((E n : ℤ) + H n - 2*s n)).card : ℕ)) / n)
        atTop (𝓝 (√(t^2 + u^2 - δ))) := by
  let H := scaledCutoff t
  let E := scaledCutoff u
  let s := scaledShift δ
  have hstate (x : ℝ) (hx : 0 < x) :
      Tendsto (fun n : ℕ ↦ logb 2 ((states (scaledCutoff x n)).card) / n) atTop (𝓝 x) := by
    have hx' := @tendsto_states_log (fun n ↦ (scaledCutoff x n : ℤ)) (x^2) (by positivity)
      (by simpa only [Int.cast_natCast] using tendsto_scaledCutoff x)
    simpa only [sqrt_sq hx.le] using hx'
  have hlabel := tendsto_label_log_of_states ht (hstate t ht)
  have htag := tendsto_logb_cube_overhead (by positivity : 0 ≤ 2 * t^2 / countCoefficient^2)
    (scaledCutoff_le t)
  obtain ⟨hp, hm⟩ := tendsto_shifted_cutoffs t u δ
  refine ⟨H, E, s, (eventually_dim_pos ht hlabel).and (eventually_dim_pos hu (hstate u hu)),
    hlabel, hstate u hu, ?_, ?_⟩
  · exact tendsto_logb_product (sqrt_pos.mpr (by linarith)) (tendsto_states_log (by linarith) hp)
      (by simpa only [H, Nat.cast_pow] using htag) (fun _ ↦ by positivity)
  · exact tendsto_logb_product (sqrt_pos.mpr (by linarith)) (tendsto_states_log (by linarith) hm)
      (by simpa only [H, Nat.cast_pow] using htag) (fun _ ↦ by positivity)
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace SpectralPlacementPrices
open SiteTensor
variable {I : Type} [Fintype I] [Nonempty I] {E K : Type*} [MetricSpace E] [Field K] (P : SpectralPlacementPrices K E)
theorem all_zero_or_normalized_at (p : I → E) :
    (∀ T : Raw.{0} I K, P.price T p = 0) ∨
      ∃ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (c : ℝ),
        0 < c ∧ ∀ T : Raw.{0} I K, P.price T p = rawLogPrice φ c T := by
  obtain ⟨g, hg, hp⟩ := P.exists_spectralPrice_of_placement p
  rcases hg with rfl | ⟨φ, c, hc, rfl⟩
  · exact Or.inl fun T => (hp T).trans (classPrice_zero _)
  · exact Or.inr ⟨φ, c, hc, fun T => (hp T).trans (classPrice_scaled_log φ c _)⟩
theorem placed_mono (p : I → E) {X Y : Raw.{0} I K} (h : X.Restricts Y) :
    P.price X p ≤ P.price Y p := by
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, hc, hp⟩
  · simp [hz]
  · simpa only [hp] using rawLogPrice_mono φ hc.le h
theorem placed_product (p : I → E) {X Y : Raw.{0} I K} (hx : X.coeff ≠ 0) (hy : Y.coeff ≠ 0) :
    P.price (X.mul Y) p = P.price X p + P.price Y p := by
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, _, hp⟩
  · simp [hz]
  · simp only [hp, rawLogPrice_mul φ c X Y hx hy]
theorem exists_binary_sum_overhead (p : I → E) : ∃ C : ℝ,
    ∀ {A : I → Type} [∀ i, Fintype (A i)] (T U : (∀ i, A i) → K), T + U ≠ 0 →
      P.price ⟨A, inferInstance, T + U⟩ p ≤
        max (P.price ⟨A, inferInstance, T⟩ p) (P.price ⟨A, inferInstance, U⟩ p) + C := by
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, hc, hp⟩
  · exact ⟨0, fun _ _ _ => by simp [hz]⟩
  refine ⟨c, ?_⟩
  intro A _ T U h
  let H : Fin 2 → (∀ i, A i) → K := ![T,U]
  have hs : ∑ i, H i = T + U := by simp [Fin.sum_univ_two, H]
  obtain ⟨j, _, hj⟩ := ordinary_sum_logb_le φ H (hs ▸ h) hc.le
  rw [hs] at hj
  simp only [hp]
  fin_cases j <;> simp [H] at hj
  · exact hj.trans (add_le_add_left (le_max_left _ _) _)
  · exact hj.trans (add_le_add_left (le_max_right _ _) _)
theorem placed_diagonal_pair (p : Fin 2 → E) (q : ℕ) :
    P.price (Raw.diagonal (Fin 2) K (Fin q)) p = dist (p 0) (p 1) * Real.logb 2 q := by
  rw [← P.wire p]
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, _, hp⟩
  · simp [hz]
  simp only [hp, rawLogPrice, ofRaw_diagonal_fin_eq_natCast, Nat.cast_ofNat]
  have he (n : ℕ) : φ.val (n : TensorClass.{0} (Fin 2) K) = n :=
    map_natCast (normalizedSpectrum.toRingHom φ) n
  rw [he q, show (2 : TensorClass.{0} (Fin 2) K) = ((2 : ℕ) : TensorClass.{0} (Fin 2) K) from rfl,
      he 2]
  norm_num [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
end SpectralPlacementPrices
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical BigOperators
namespace ShiftedCrossing
open SiteTensor

local instance (priority := 4000) {α : Type*} : DecidableEq α := Classical.decEq α
abbrev Site := Fin 2 ⊕ Fin 2
def Leg (dX dY : ℕ) : Site → Type := Sum.elim (fun _ ↦ Fin dX) (fun _ ↦ Fin dY)
instance (dX dY : ℕ) : ∀ i, Fintype (Leg dX dY i)
  | .inl _ => inferInstanceAs (Fintype (Fin dX))
  | .inr _ => inferInstanceAs (Fintype (Fin dY))
variable {K : Type*} [Field K] {dX dY r : ℕ}
def target (K : Type*) [Field K] (dX dY : ℕ) : Raw Site K :=
  ⟨Leg dX dY, inferInstance, fun a =>
    if a (.inl 0) = a (.inl 1) ∧ a (.inr 0) = a (.inr 1) then 1 else 0⟩
def partner : Bool → Fin 2 → Fin 2
  | false => id
  | true => Fin.rev
@[simp] theorem partner_partner (b : Bool) (i : Fin 2) : partner b (partner b i) = i := by
  cases b <;> simp [partner]
def cut (b : Bool) : Site → Fin 2 := Sum.elim id (partner b)
def term (b : Bool) (W : Fin 2 → Fin dX → Fin dY → Fin r → K) : Raw Site K :=
  ⟨Leg dX dY, inferInstance, fun a =>
    ∑ k, ∏ j, W j (a (.inl j)) (a (.inr (partner b j))) k⟩
theorem term_group_restricts (b : Bool) (W : Fin 2 → Fin dX → Fin dY → Fin r → K) :
    ((term b W).group (cut b)).Restricts (Raw.diagonal (Fin 2) K (Fin r)) := by
  let M (j : Fin 2) (z : ((term b W).group (cut b)).Leg j) (k : Fin r) :=
    W j (z ⟨.inl j, rfl⟩) (z ⟨.inr (partner b j), partner_partner b j⟩) k
  refine ⟨M, fun x => ?_⟩
  change _ = ∑ a : Fin 2 → Fin r, (∑ k, if a = fun _ => k then (1 : K) else 0) *
    ∏ j, M j (x j) (a j)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  dsimp only [Raw.group, term]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [M]
  cases b <;> fin_cases j <;> rfl
structure Factorization (K : Type*) [Field K] (dX dY rp rm : ℕ) where
  plus : Fin 2 → Fin dX → Fin dY → Fin rp → K
  minus : Fin 2 → Fin dX → Fin dY → Fin rm → K
  identity : ∀ x : ∀ i, Leg dX dY i, (target K dX dY).coeff x =
    (term false plus).coeff x + (term true minus).coeff x
theorem target_ne_zero (hx : 0 < dX) (hy : 0 < dY) : (target K dX dY).coeff ≠ 0 := by
  let a : ∀ j, Leg dX dY j
    | .inl _ => ⟨0,hx⟩
    | .inr _ => ⟨0,hy⟩
  intro h
  have hh := congrFun h a
  change (if _ then (1 : K) else 0) = 0 at hh
  rw [ite_eq_left ⟨rfl, rfl⟩] at hh
  exact one_ne_zero hh
def Factorization.ofInt {rp rm : ℕ}
    (Lp Rp : Fin dX → Fin dY → Fin rp → ℤ) (Lm Rm : Fin dX → Fin dY → Fin rm → ℤ)
    (h : ∀ i j a b, (if i = j ∧ a = b then (1 : ℤ) else 0) =
      (∑ k, Lp i a k * Rp j b k) + ∑ k, Lm i b k * Rm j a k) :
    Factorization K dX dY rp rm where
  plus j i a k := (![Lp,Rp] j i a k : ℤ)
  minus j i a k := (![Lm,Rm] j i a k : ℤ)
  identity := by
    intro x
    let i : Fin dX := x (.inl 0)
    let j : Fin dX := x (.inl 1)
    let a : Fin dY := x (.inr 0)
    let b : Fin dY := x (.inr 1)
    have p := h i j a b
    change (if i = j ∧ a = b then (1 : K) else 0) =
      (∑ k, ∏ s, ((![Lp,Rp] s (x (.inl s)) (x (.inr (partner false s))) k : ℤ) : K)) +
        ∑ k, ∏ s, ((![Lm,Rm] s (x (.inl s)) (x (.inr (partner true s))) k : ℤ) : K)
    simp only [Fin.prod_univ_two]
    change (if i = j ∧ a = b then (1 : K) else 0) =
      (∑ k, (Lp i a k : K) * (Rp j b k : K)) + ∑ k, (Lm i b k : K) * (Rm j a k : K)
    split_ifs at p ⊢ with he
    · simpa using congrArg (Int.castRingHom K) p
    · simpa using congrArg (Int.castRingHom K) p
end ShiftedCrossing
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open scoped BigOperators Classical
def Factors.toFactorization {I A P M : Type} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A] [Fintype P] [Fintype M]
    (F : Factors I A P M) (hF : ∀ i j α β, F.entry i j α β = if i=j ∧ α=β then 1 else 0)
    (K : Type*) [Field K] : ShiftedCrossing.Factorization K
      (Fintype.card I) (Fintype.card A) (Fintype.card P) (Fintype.card M) := by
  let c (T : Type) [Fintype T] := (Fintype.equivFin T).symm
  apply ShiftedCrossing.Factorization.ofInt
    (fun i α k ↦ F.plusLeft (c I i) (c A α) (c P k))
    (fun j β k ↦ F.plusRight (c I j) (c A β) (c P k))
    (fun i β k ↦ F.minusLeft (c I i) (c A β) (c M k))
    (fun j α k ↦ F.minusRight (c I j) (c A α) (c M k))
  intro i j α β
  have h := hF (c I i) (c I j) (c A α) (c A β)
  simp only [Equiv.apply_eq_iff_eq, Factors.entry] at h
  by_cases he : i = j ∧ α = β <;> simp only [he, ↓reduceIte] at h ⊢ <;> rw [← h] <;> congr 1
  all_goals
    apply Fintype.sum_equiv (Fintype.equivFin _) _ _
    simp [c]
theorem finite_factorization {C : State → State → ℤ} {Y : ModeMatrix}
    (h : CoefficientIdentity C Y) (hzero : ∀ i j : State, i.card ≠ j.card → C i j = 0)
    (H E : ℕ) (s : ℤ) (B : Matrix (Label H) (Label H) ℤ)
    (hB : B * (Matrix.of fun i j : Label H ↦ C i.val j.val) = 1) (K : Type*) [Field K] :
    Nonempty (ShiftedCrossing.Factorization K ((states H).card-1) (states E).card
      ((H+1)^3 * (states (E+H+2*s)).card) ((H+1)^3 * (states (E+H-2*s)).card)) := by
  obtain ⟨F, hF⟩ := exists_integral_factors h hzero H E s B hB
  simpa only [Finset.card_erase_of_mem (empty_mem_states_nat H), card_channel, PlusStates, MinusStates, Fintype.card_coe] using
    (⟨F.toFactorization hF K⟩ : Nonempty _)
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Problem336.CauchyBinet
variable {R m n : Type*} [CommRing R]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
theorem coeff_det_one_add_X_smul_card (M : Matrix n n R) :
    (Matrix.det (1 + (X : R[X]) • M.map C)).coeff (Fintype.card n) = M.det := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  have hsets : (Finset.univ : Finset n).powersetCard (Fintype.card n) =
      {Finset.univ} := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_singleton]
    exact Finset.card_eq_iff_eq_univ s
  rw [hsets, Finset.sum_singleton]
  let e : (Finset.univ : Finset n) ≃ n :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Matrix.det_submatrix_equiv_self e M
theorem det_one_add_X_mul_comm (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (1 + (X : R[X]) • (A * B).map C) =
      Matrix.det (1 + (X : R[X]) • (B * A).map C) := by
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul] using
    Matrix.det_one_add_mul_comm ((X : R[X]) • A.map C) (B.map C)
theorem det_mul_eq_sum_principal_minors (A : Matrix n m R) (B : Matrix m n R) :
    Matrix.det (A * B) =
      ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
        Matrix.det ((B * A).submatrix (Subtype.val : s → m) (Subtype.val : s → m)) := by
  rw [← coeff_det_one_add_X_smul_card (A * B), det_one_add_X_mul_comm A B,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
end Problem336.CauchyBinet
end
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset Matrix
private theorem stateMinor_of_card (f : ℕ → ℕ → ℤ) {I J : Finset ℕ} {k : ℕ}
    (hI : I.card = k) (hJ : J.card = k) :
    stateMinor f I J =
      (Matrix.of fun i j : Fin k ↦ f (I.orderEmbOfFin hI i) (J.orderEmbOfFin hJ j)).det := by
  subst k
  rw [stateMinor, dite_eq_left hJ]
private theorem sum_powersetCard_fin_val {M : Type*} [AddCommMonoid M] (N k : ℕ)
    (F : Finset ℕ → M) :
    ∑ S ∈ (univ : Finset (Fin N)).powersetCard k, F (S.map Fin.valEmbedding) =
      ∑ S ∈ (range N).powersetCard k, F S := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, powersetCard_map, sum_map]
  rfl
private theorem orderEmb_map_val {N k : ℕ} (S : Finset (Fin N)) (hS : S.card = k)
    (i : Fin k) :
    (S.orderEmbOfFin hS i : ℕ) =
      (S.map Fin.valEmbedding).orderEmbOfFin ((card_map _).trans hS) i := by
  apply congrFun (orderEmbOfFin_unique _ _ (Fin.val_strictMono.comp (S.orderEmbOfFin hS).strictMono))
  intro j
  exact mem_map.mpr ⟨_, S.orderEmbOfFin_mem hS j, rfl⟩
theorem pascal_gram_minor {N : ℕ} {I J : Finset ℕ} (hI : I ⊆ range N) :
    stateMinor (fun i j ↦ ((i + j).choose i : ℤ)) I J =
      ∑ S ∈ (range N).powerset, pascalMinor I S * pascalMinor J S := by
  classical
  by_cases hJ : J.card = I.card
  · let A : Matrix (Fin I.card) (Fin N) ℤ :=
      Matrix.of fun i k ↦ ((I.orderEmbOfFin rfl i).choose k : ℤ)
    let B : Matrix (Fin I.card) (Fin N) ℤ :=
      Matrix.of fun j k ↦ ((J.orderEmbOfFin hJ j).choose k : ℤ)
    have hgram : stateMinor (fun i j ↦ ((i + j).choose i : ℤ)) I J = (A * B.transpose).det := by
      rw [stateMinor_of_card _ rfl hJ]
      congr 1
      ext i j
      change _ = ∑ k : Fin N, _
      exact ((Fin.sum_univ_eq_sum_range _ _).trans <|
        pascal_gram_entry (j := J.orderEmbOfFin hJ j) (mem_range.mp (hI (I.orderEmbOfFin_mem rfl i)))).symm
    rw [hgram, Problem336.CauchyBinet.det_mul_eq_sum_principal_minors, Fintype.card_fin]
    let F := fun S ↦ pascalMinor I S * pascalMinor J S
    calc
      _ = ∑ S ∈ (univ : Finset (Fin N)).powersetCard I.card, F (S.map Fin.valEmbedding) := by
        apply sum_congr rfl
        intro S hS
        have hc := (mem_powersetCard.mp hS).2
        let e := (S.orderIsoOfFin hc).toEquiv
        let col := fun i : Fin I.card ↦ S.orderEmbOfFin hc i
        have hA : (A.submatrix id col).det = pascalMinor I (S.map Fin.valEmbedding) := by
          rw [pascalMinor, stateMinor_of_card _ rfl ((card_map _).trans hc)]
          congr 1
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, A, col, orderEmb_map_val]
        have hB : (B.submatrix id col).det = pascalMinor J (S.map Fin.valEmbedding) := by
          rw [pascalMinor, stateMinor_of_card _ hJ ((card_map _).trans hc)]
          congr 1
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, B, col, orderEmb_map_val]
        rw [← Matrix.det_submatrix_equiv_self e]
        change ((B.transpose * A).submatrix col col).det = _
        rw [← Matrix.submatrix_mul_equiv B.transpose A col (Equiv.refl _) col, Matrix.det_mul]
        change ((B.submatrix id col).transpose).det * (A.submatrix id col).det = _
        rw [Matrix.det_transpose, hA, hB, mul_comm]
      _ = ∑ S ∈ (range N).powersetCard I.card, F S := sum_powersetCard_fin_val ..
      _ = _ := by
        apply sum_subset (by simp [powersetCard_eq_filter])
        intro S hS hout
        have hc : S.card ≠ I.card := fun h ↦ hout (mem_powersetCard.mpr ⟨mem_powerset.mp hS, h⟩)
        simp [F, pascalMinor, stateMinor, hc]
  · rw [stateMinor, dite_eq_right hJ]
    symm
    apply sum_eq_zero
    intro S _
    by_cases hS : S.card = I.card
    · have hSJ : S.card ≠ J.card := fun h ↦ hJ (h.symm.trans hS)
      simp [pascalMinor, stateMinor, hSJ]
    · simp [pascalMinor, stateMinor, hS]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset Matrix
@[simp] theorem pascalMinor_self (I : Finset ℕ) : pascalMinor I I = 1 := by
  classical
  unfold pascalMinor stateMinor
  rw [dite_eq_left rfl]
  rw [Matrix.det_of_isLowerTriangular]
  · simp
  · intro i j hij
    change i < j at hij
    simp [Nat.choose_eq_zero_of_lt ((I.orderEmbOfFin rfl).strictMono hij)]
private theorem weight_enumeration (S : Finset ℕ) {k : ℕ} (h : S.card = k) :
    weight S = ∑ i : Fin k, (2 * S.orderEmbOfFin h i + 1) := by
  calc
    weight S = ∑ j ∈ univ.map (S.orderEmbOfFin h).toEmbedding, (2*j + 1) := by
      rw [S.map_orderEmbOfFin_univ]
      rfl
    _ = _ := sum_map _ _ _
theorem eq_or_weight_lt_of_pascalMinor_ne_zero {I J : Finset ℕ} (h : pascalMinor I J ≠ 0) :
    I = J ∨ weight J < weight I := by
  classical
  by_cases hc : J.card = I.card
  · simp only [pascalMinor, stateMinor, dite_eq_left hc, Matrix.det_apply', Matrix.of_apply] at h
    obtain ⟨σ, _, hσ⟩ := exists_ne_zero_of_sum_ne_zero h
    have hle (i : Fin I.card) : J.orderEmbOfFin hc i ≤ I.orderEmbOfFin rfl (σ i) := by
      by_contra! hn
      have hz := prod_eq_zero (s := univ) (mem_univ i)
        (f := fun j : Fin I.card ↦ (((I.orderEmbOfFin rfl (σ j)).choose (J.orderEmbOfFin hc j)) : ℤ))
        (by simp [Nat.choose_eq_zero_of_lt hn])
      exact hσ (by simp [hz])
    by_cases heq : ∀ i, J.orderEmbOfFin hc i = I.orderEmbOfFin rfl (σ i)
    · left
      symm
      apply eq_of_subset_of_card_le _ hc.ge
      intro n hn
      obtain ⟨i, hi⟩ := (J.orderIsoOfFin hc).surjective ⟨n, hn⟩
      have hi' : J.orderEmbOfFin hc i = n := congrArg Subtype.val hi
      rw [← hi', heq]
      exact I.orderEmbOfFin_mem rfl _
    · right
      push Not at heq
      obtain ⟨i, hi⟩ := heq
      rw [weight_enumeration J hc, weight_enumeration I rfl,
        ← Equiv.sum_comp σ (fun j ↦ 2 * I.orderEmbOfFin rfl j + 1)]
      apply sum_lt_sum (fun j _ ↦ by have := hle j; omega)
      exact ⟨i, mem_univ i, by have := hle i; omega⟩
  · simp [pascalMinor, stateMinor, hc] at h
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Matrix Finset
private noncomputable def pascalMatrix (H : ℕ) : Matrix (Label H) (Label H) ℤ :=
  Matrix.of fun i j ↦ pascalMinor i.val j.val
private theorem det_pascalMatrix (H : ℕ) : (pascalMatrix H).det = 1 := by
  classical
  let w (i : Label H) := weight i.val
  have ht : (pascalMatrix H).transpose.BlockTriangular w := by
    intro i j hj
    change pascalMinor j.val i.val = 0
    by_contra hn
    rcases eq_or_weight_lt_of_pascalMinor_ne_zero hn with he | he
    · simp only [w, he, lt_self_iff_false] at hj
    · exact he.not_gt hj
  have hblock (a : ℕ) : ((pascalMatrix H).transpose.toSquareBlock w a) = 1 := by
    ext i j
    by_cases he : i = j
    · subst j
      rw [Matrix.one_apply_eq]
      exact pascalMinor_self i.val.val
    · rw [Matrix.one_apply_ne he]
      change pascalMinor j.val.val i.val.val = 0
      by_contra hn
      rcases eq_or_weight_lt_of_pascalMinor_ne_zero hn with hval | hlt
      · exact he (Subtype.ext (Subtype.ext hval.symm))
      · exact hlt.ne (i.property.trans j.property.symm)
  rw [← Matrix.det_transpose, ht.det]
  simp [hblock]
private theorem gram_pairing (H : ℕ) :
    (Matrix.of (fun i j : Label H ↦ pairing i.val j.val)) =
      (Matrix.diagonal (fun i : Label H ↦ pairingSign i.val)) *
        (pascalMatrix H * (pascalMatrix H).transpose) := by
  classical
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.of_apply, pairing, Matrix.mul_apply,
    Matrix.transpose_apply, pascalMatrix]
  congr 1
  have hset {S : Finset ℕ} (hS : S ∈ (states (H : ℤ)).erase ∅) : S ⊆ range H := by
    intro k hk
    exact mem_range.mpr ((mode_lt_weight hk).trans_le (label_weight_le ⟨S,hS⟩))
  rw [pascal_gram_minor (hset i.property)]
  change _ = ∑ a : Label H, pascalMinor i.val a.val * pascalMinor j.val a.val
  rw [Finset.sum_coe_sort ((states (H : ℤ)).erase ∅) (fun S ↦ pascalMinor i.val S * pascalMinor j.val S)]
  symm
  apply sum_subset (fun S hS ↦ mem_powerset.mpr (hset hS))
  intro S _ hS
  by_cases hn : pascalMinor i.val S = 0
  · simp [hn]
  · apply False.elim (hS _)
    apply mem_erase.mpr
    constructor
    · intro h0
      subst S
      have hc : (∅ : Finset ℕ).card ≠ i.val.card := by
        simpa using (label_nonempty i).card_pos.ne
      exact hn (by rw [pascalMinor, stateMinor, dite_eq_right hc])
    · rw [mem_states, Int.ofNat_le]
      rcases eq_or_weight_lt_of_pascalMinor_ne_zero hn with he | he
      · exact he ▸ label_weight_le i
      · exact he.le.trans (label_weight_le i)
theorem pairing_left_inverse (H : ℕ) :
    ∃ A : Matrix (Label H) (Label H) ℤ,
      A * (Matrix.of (fun i j : Label H ↦ pairing i.val j.val)) = 1 := by
  classical
  apply IsUnit.exists_left_inv
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [gram_pairing, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_pascalMatrix, mul_one, mul_one, Matrix.det_diagonal]
  apply IsUnit.prod_univ_iff.mpr
  exact fun i ↦ IsUnit.pow _ (isUnit_one.neg)
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def ShiftedCrossingCost (E : Type*) [NormedAddCommGroup E] : Prop :=
  ∀ (x y : E), ‖x‖ = 1 → ‖y‖ = 1 → ∀ t u δ : ℝ, 0 < t → 0 < u →
    -(t ^ 2 + u ^ 2) < δ → δ < t ^ 2 + u ^ 2 → ∀ p m : E,
    t + u ≤ max (t * ‖x - p‖ + u * ‖y - p‖ + ‖p‖ * Real.sqrt (t ^ 2 + u ^ 2 + δ))
      (t * ‖x - m‖ + u * ‖-y - m‖ + ‖m‖ * Real.sqrt (t ^ 2 + u ^ 2 - δ))
private theorem exists_positive_direction (L : E →L[ℝ] ℝ) {r : ℝ}
    (hr : 0 ≤ r) (h : r < ‖L‖) : ∃ z : E, r * ‖z‖ < L z := by
  obtain ⟨z, hz⟩ := L.exists_mul_lt_of_lt_opNorm hr h
  rw [Real.norm_eq_abs, lt_abs] at hz
  rcases hz with h | h
  · exact ⟨z, h⟩
  · exact ⟨-z, by simpa using h⟩
private theorem eventually_cost_lt {x y z : E} {f g : E →L[ℝ] ℝ} {t u r : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hf : HasFDerivAt (‖·‖) f x) (hg : HasFDerivAt (‖·‖) g y)
    (hz : r * ‖z‖ < t * f z + u * g z) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      t * ‖x - ε • z‖ + u * ‖y - ε • z‖ + ‖ε • z‖ * r < t + u := by
  let cost (ε : ℝ) := t * ‖x - ε • z‖ + u * ‖y - ε • z‖ + ε * (‖z‖ * r)
  have dx : HasDerivAt (fun ε : ℝ => ‖x - ε • z‖) (-f z) 0 := by
    simpa [HasLineDerivAt, sub_eq_add_neg] using hf.hasLineDerivAt (-z)
  have dy : HasDerivAt (fun ε : ℝ => ‖y - ε • z‖) (-g z) 0 := by
    simpa [HasLineDerivAt, sub_eq_add_neg] using hg.hasLineDerivAt (-z)
  have hd : HasDerivAt cost (t * -f z + u * -g z + ‖z‖ * r) 0 := by
    simpa [cost, Pi.add_def] using ((dx.const_mul t).add (dy.const_mul u)).add
      ((hasDerivAt_id' (0 : ℝ)).mul_const (‖z‖ * r))
  have hs := hd.hasDerivWithinAt (s := Set.Ioi (0 : ℝ)) |>.limsup_slope_le'
    (Set.notMem_Ioi.mpr le_rfl) (show t * -f z + u * -g z + ‖z‖ * r < 0 by linarith)
  filter_upwards [hs, self_mem_nhdsWithin] with ε hε hpos
  have hp : 0 < ε := hpos
  rw [slope_def_field, sub_zero, div_lt_iff₀ hp, zero_mul, sub_lt_zero] at hε
  simpa [cost, norm_smul, Real.norm_eq_abs, abs_of_pos hp, mul_assoc, hx, hy] using hε
theorem ShiftedCrossingCost.smooth_dual {x y : E} {f g : E →L[ℝ] ℝ}
    (cost : ShiftedCrossingCost E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hf : HasFDerivAt (‖·‖) f x) (hg : HasFDerivAt (‖·‖) g y)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2) := by
  let A := ‖t • f + u • g‖
  let B := ‖t • f - u • g‖
  let S := t ^ 2 + u ^ 2
  have htf : ‖t • f‖ ≤ t := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht] using
      mul_le_mul_of_nonneg_left (hf.le_of_lipschitz lipschitzWith_one_norm) ht.le
  have hug : ‖u • g‖ ≤ u := by
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hu] using
      mul_le_mul_of_nonneg_left (hg.le_of_lipschitz lipschitzWith_one_norm) hu.le
  have hA : A ≤ t + u := (norm_add_le _ _).trans (add_le_add htf hug)
  have hB : B ≤ t + u := (norm_sub_le _ _).trans (add_le_add htf hug)
  have hA₀ : 0 ≤ A := norm_nonneg _
  have hB₀ : 0 ≤ B := norm_nonneg _
  have hA₂ : A ^ 2 ≤ 2 * S := by
    dsimp [S]; nlinarith [sq_le_sq' (by linarith : -(t + u) ≤ A) hA, sq_nonneg (t-u)]
  have hB₂ : B ^ 2 ≤ 2 * S := by
    dsimp [S]; nlinarith [sq_le_sq' (by linarith : -(t + u) ≤ B) hB, sq_nonneg (t-u)]
  change A ^ 2 + B ^ 2 ≤ 2 * S
  by_contra! hfail
  let δ := (A ^ 2 - B ^ 2) / 2
  have hmin : -S < δ := by dsimp [δ]; linarith
  have hmax : δ < S := by dsimp [δ]; linarith
  have hplus : Real.sqrt (S + δ) < A := by
    nlinarith [Real.sq_sqrt (show 0 ≤ S + δ by linarith), show S + δ < A ^ 2 by dsimp [δ]; linarith,
      Real.sqrt_nonneg (S + δ)]
  have hminus : Real.sqrt (S - δ) < B := by
    nlinarith [Real.sq_sqrt (show 0 ≤ S - δ by linarith), show S - δ < B ^ 2 by dsimp [δ]; linarith,
      Real.sqrt_nonneg (S - δ)]
  obtain ⟨p, hp⟩ := exists_positive_direction _ (Real.sqrt_nonneg _) hplus
  obtain ⟨m, hm⟩ := exists_positive_direction _ (Real.sqrt_nonneg _) hminus
  have hg' : HasFDerivAt (‖·‖) (-g) (-y) := by
    simpa using hg.hasFDerivAt_norm_smul_neg (show (-1 : ℝ) < 0 by norm_num)
  have ep := eventually_cost_lt hx hy hf hg (t := t) (u := u) (z := p) (by simpa using hp)
  have em := eventually_cost_lt hx (norm_neg y ▸ hy) hf hg' (t := t) (u := u) (z := m)
    (by simpa [sub_eq_add_neg] using hm)
  obtain ⟨ε, h₁, h₂⟩ := (ep.and em).exists
  exact (not_lt_of_ge (cost x y hx hy t u δ ht hu hmin hmax (ε • p) (ε • m)))
    (max_lt h₁ h₂)
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace ShiftedCrossing
open Filter Real
open scoped Topology
def AsymptoticFactorizations (K : Type*) [Field K] : Prop :=
  ∀ t u δ : ℝ, 0 < t → 0 < u → -(t ^ 2 + u ^ 2) < δ → δ < t ^ 2 + u ^ 2 →
    ∃ (dx dy rp rm : ℕ → ℕ) (bp bm : ℕ → ℝ),
      (∀ᶠ n in atTop, 0 < dx n ∧ 0 < dy n ∧ Nonempty (Factorization K (dx n) (dy n) (rp n) (rm n))) ∧
      Tendsto (fun n => logb 2 (dx n) / n) atTop (𝓝 t) ∧
      Tendsto (fun n => logb 2 (dy n) / n) atTop (𝓝 u) ∧
      (∀ᶠ n in atTop, logb 2 (rp n) / n ≤ bp n ∧ logb 2 (rm n) / n ≤ bm n) ∧
      Tendsto bp atTop (𝓝 (√(t ^ 2 + u ^ 2 + δ))) ∧
      Tendsto bm atTop (𝓝 (√(t ^ 2 + u ^ 2 - δ)))
theorem cost_limit {X Y Rp Rm Bp Bm : ℕ → ℝ}
    {t u bp bm xp yp dp xm ym dm C : ℝ} (hdp : 0 ≤ dp) (hdm : 0 ≤ dm)
    (hx : Tendsto (fun n => X n / n) atTop (𝓝 t)) (hy : Tendsto (fun n => Y n / n) atTop (𝓝 u))
    (hbp : Tendsto Bp atTop (𝓝 bp)) (hbm : Tendsto Bm atTop (𝓝 bm))
    (hr : ∀ᶠ n in atTop, Rp n / n ≤ Bp n ∧ Rm n / n ≤ Bm n)
    (hc : ∀ᶠ n in atTop, 2 * (X n + Y n) ≤
      max (2 * (X n * xp + Y n * yp + dp * Rp n))
        (2 * (X n * xm + Y n * ym + dm * Rm n)) + C) :
    t + u ≤ max (t * xp + u * yp + dp * bp) (t * xm + u * ym + dm * bm) := by
  have hp := ((hx.mul_const xp).add (hy.mul_const yp)).add (hbp.const_mul dp)
  have hm := ((hx.mul_const xm).add (hy.mul_const ym)).add (hbm.const_mul dm)
  have ho : Tendsto (fun n : ℕ => (C / 2) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply le_of_tendsto_of_tendsto (hx.add hy)
    (by simpa only [add_zero] using (hp.max hm).add ho)
  filter_upwards [hr, hc, eventually_gt_atTop 0] with n hrn hcn hn
  have hpos : 0 < (n : ℝ) := by exact_mod_cast hn
  change X n / n + Y n / n ≤
    max (X n / n * xp + Y n / n * yp + dp * Bp n)
      (X n / n * xm + Y n / n * ym + dm * Bm n) + (C / 2) / n
  let k : ℝ := (2 * (n : ℝ))⁻¹
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have h := mul_le_mul_of_nonneg_right hcn hk
  rw [add_mul, max_mul_of_nonneg _ _ hk] at h
  calc
    _ = 2 * (X n + Y n) * k := by dsimp [k]; field_simp
    _ ≤ _ := h
    _ = max (X n / n * xp + Y n / n * yp + dp * (Rp n / n))
         (X n / n * xm + Y n / n * ym + dm * (Rm n / n)) + (C / 2) / n := by
       dsimp [k]
       congr 1
       · congr 1 <;> field_simp
       · ring
    _ ≤ _ := by
       gcongr
       · exact hrn.1
       · exact hrn.2
end ShiftedCrossing
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Filter
open scoped Topology
theorem crossing_of_truncated (h : TruncatedIdentity) (H E : ℕ) (s : ℤ)
    (K : Type*) [Field K] :
    Nonempty (ShiftedCrossing.Factorization K (Fintype.card (Label H)) (states E).card
      ((H+1)^3 * (states (E+H+2*s)).card) ((H+1)^3 * (states (E+H-2*s)).card)) := by
  obtain ⟨B, hB⟩ := pairing_left_inverse H
  rw [card_label]
  refine finite_factorization (coefficientIdentity_of_truncated h) ?_ H E s B hB K
  intro i j hij
  simp [pairing, stateMinor, Ne.symm hij]
theorem asymptoticFactorizations_of_truncated (h : TruncatedIdentity) (K : Type*) [Field K] :
    ShiftedCrossing.AsymptoticFactorizations K := by
  intro t u δ ht hu hlo hhi
  obtain ⟨H, E, s, hpos, hx, hy, hp, hm⟩ := exists_scaled_dimensions t u δ ht hu hlo hhi
  let rp (n : ℕ) := (H n+1)^3 * (states ((E n : ℤ)+H n+2*s n)).card
  let rm (n : ℕ) := (H n+1)^3 * (states ((E n : ℤ)+H n-2*s n)).card
  refine ⟨fun n ↦ Fintype.card (Label (H n)), fun n ↦ (states (E n)).card, rp, rm,
    fun n ↦ Real.logb 2 (rp n) / n, fun n ↦ Real.logb 2 (rm n) / n, ?_, hx, hy,
    Eventually.of_forall (fun _ ↦ ⟨le_rfl, le_rfl⟩), hp, hm⟩
  filter_upwards [hpos] with n hn
  exact ⟨hn.1, hn.2, crossing_of_truncated h _ _ _ _⟩
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem mem_closure_convexHull_of_norming {S : Set (E →L[ℝ] ℝ)}
    (hS : ∀ x : E, ∀ r < ‖x‖, ∃ g ∈ S, r < g x) {f : E →L[ℝ] ℝ} (hf : ‖f‖ ≤ 1) :
    f ∈ closure (convexHull ℝ S) := by
  by_contra hout
  obtain ⟨L, r, hsep, hr⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ S).closure isClosed_closure hout
  let L' : Module.Dual ℝ (Module.Dual ℝ E) :=
    L.toLinearMap.comp LinearMap.toContinuousLinearMap.toLinearMap
  let x := (Module.evalEquiv ℝ E).symm L'
  have heval (g : E →L[ℝ] ℝ) : g x = L g :=
    Module.apply_evalEquiv_symm_apply ℝ E g.toLinearMap L'
  have hfx : f x ≤ ‖x‖ := calc
    f x ≤ ‖f x‖ := le_abs_self _
    _ ≤ 1 * ‖x‖ := f.le_of_opNorm_le hf x
    _ = ‖x‖ := one_mul _
  rw [← heval f] at hr
  obtain ⟨g, hg, hrg⟩ := hS x r (hr.trans_le hfx)
  rw [heval g] at hrg
  exact (hsep g (subset_closure (subset_convexHull ℝ S hg))).not_gt hrg
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def smoothNormDerivatives (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (E →L[ℝ] ℝ) :=
  {f | ∃ x : E, ‖x‖ = 1 ∧ HasFDerivAt (fun z : E => ‖z‖) f x}
theorem smoothNormDerivatives_norm_le_one {f : E →L[ℝ] ℝ}
    (hf : f ∈ smoothNormDerivatives E) : ‖f‖ ≤ 1 := by
  obtain ⟨x, _, hx⟩ := hf
  rw [← hx.fderiv]
  exact NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := E))
theorem exists_smoothNormDerivative_gt [FiniteDimensional ℝ E] [Nontrivial E]
    (v : E) {r : ℝ} (hr : r < ‖v‖) :
    ∃ f ∈ smoothNormDerivatives E, r < f v := by
  obtain ⟨x, hxv, hx⟩ := Metric.dense_iff.mp (dense_differentiableAt_norm (E := E))
    v ((‖v‖ - r) / 2) (by linarith)
  change DifferentiableAt ℝ (fun z : E => ‖z‖) x at hx
  have hx0 : x ≠ 0 := fun h => not_differentiableAt_norm_zero E (h ▸ hx)
  let f := fderiv ℝ (fun z : E => ‖z‖) x
  have hmem : f ∈ smoothNormDerivatives E :=
    ⟨‖x‖⁻¹ • x, norm_smul_inv_norm (𝕜 := ℝ) hx0,
      hx.hasFDerivAt.hasFDerivAt_norm_smul_pos (inv_pos.mpr (norm_pos_iff.mpr hx0))⟩
  refine ⟨f, hmem, ?_⟩
  have hdiff : f (x - v) ≤ ‖x - v‖ := calc
    f (x - v) ≤ ‖f (x - v)‖ := le_norm_self _
    _ ≤ ‖f‖ * ‖x - v‖ := f.le_opNorm _
    _ ≤ 1 * ‖x - v‖ := by gcongr; exact smoothNormDerivatives_norm_le_one hmem
    _ = ‖x - v‖ := one_mul _
  rw [map_sub, show f x = ‖x‖ from hx.fderiv_norm_self] at hdiff
  rw [Metric.mem_ball, dist_eq_norm] at hxv
  have htri := norm_sub_norm_le v x
  rw [norm_sub_rev] at htri
  linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem crossingBound_closure_convexHull (S : Set E) (t u C : ℝ)
    (h : ∀ f ∈ S, ∀ g ∈ S, ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ C)
    {f g : E} (hf : f ∈ closure (convexHull ℝ S)) (hg : g ∈ closure (convexHull ℝ S)) :
    ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ C := by
  let plus : E × E →ₗ[ℝ] E := t • LinearMap.fst ℝ E E + u • LinearMap.snd ℝ E E
  let minus : E × E →ₗ[ℝ] E := t • LinearMap.fst ℝ E E - u • LinearMap.snd ℝ E E
  let A := {p : E × E | ‖t • p.1 + u • p.2‖ ^ 2 + ‖t • p.1 - u • p.2‖ ^ 2 ≤ C}
  have hsq : ConvexOn ℝ univ (fun x : E ↦ ‖x‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2
  have hplus : ConvexOn ℝ univ (fun p : E × E ↦ ‖plus p‖ ^ 2) := hsq.comp_linearMap plus
  have hminus : ConvexOn ℝ univ (fun p : E × E ↦ ‖minus p‖ ^ 2) := hsq.comp_linearMap minus
  have hc : Convex ℝ A := by
    simpa [A, plus, minus] using (hplus.add hminus).convex_le C
  have hclosed : IsClosed A := isClosed_le (by fun_prop) continuous_const
  have hp : (f, g) ∈ closure (convexHull ℝ (S ×ˢ S)) := by
    rw [convexHull_prod, closure_prod_eq]
    exact ⟨hf, hg⟩
  exact closure_minimal (convexHull_min (fun p hp ↦ h p.1 hp.1 p.2 hp.2) hc) hclosed hp
variable [FiniteDimensional ℝ E] [Nontrivial E]
theorem closure_convexHull_smoothNormDerivatives :
    closure (convexHull ℝ (smoothNormDerivatives E)) = Metric.closedBall 0 1 := by
  apply Subset.antisymm
  · apply closure_minimal _ Metric.isClosed_closedBall
    apply convexHull_min _ (convex_closedBall ..)
    intro f hf
    simpa using smoothNormDerivatives_norm_le_one hf
  · exact fun _ hf ↦ mem_closure_convexHull_of_norming
      (fun x _ hr ↦ exists_smoothNormDerivative_gt x hr) (by simpa using hf)
theorem dualBall_crossingBound_of_smooth (t u : ℝ)
    (h : ∀ (x y : E) (f g : E →L[ℝ] ℝ), ‖x‖ = 1 → ‖y‖ = 1 →
      HasFDerivAt (fun z : E ↦ ‖z‖) f x → HasFDerivAt (fun z : E ↦ ‖z‖) g y →
      ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2))
    (f g : E →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2) := by
  apply crossingBound_closure_convexHull (smoothNormDerivatives E) t u
  · rintro a ⟨x, hx, ha⟩ b ⟨y, hy, hb⟩
    exact h x y a b hx hy ha hb
  · simpa [closure_convexHull_smoothNormDerivatives] using hf
  · simpa [closure_convexHull_smoothNormDerivatives] using hg
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace CurvatureBlowup
open HyperbolicObstruction Filter Topology Set
variable {X : Type*} [MetricSpace X]
def scale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity
abbrev ultrafilter := Ultrafilter.of (atTop : Filter ℕ)
abbrev Space (o : X) := Book.Blowup ultrafilter scale_pos o
abbrev Section (o : X) := Book.BlowupSection ultrafilter scale_pos o
private theorem tendsto_parameter (r : ℝ) :
    Tendsto (fun n : ℕ ↦ r / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
private theorem eventually_parameter {r : ℝ} (hr : 0 ≤ r) :
    ∀ᶠ n : ℕ in atTop, r / ((n : ℝ) + 1) ∈ Icc 0 1 := by
  filter_upwards [(tendsto_parameter r).eventually_lt_const zero_lt_one] with n hn
  exact ⟨div_nonneg hr (by positivity), hn.le⟩
private def sectionOf {o x : X} {a : ℝ → X} (ha : IsSegment a o x) (r : ℝ) : Section o where
  val n := ⟨if r / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) 1 then a (r / ((n : ℝ) + 1)) else o⟩
  bound := by
    refine ⟨max 0 r * dist o x, fun n ↦ ?_⟩
    rw [MetricScale.dist_eq]
    dsimp only
    split_ifs with hn
    · rw [ha.dist_from_source hn, scale, inv_inv, ← mul_assoc,
        mul_div_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
    · simp [mul_nonneg (le_max_left 0 r) dist_nonneg]
def ray {o x : X} {a : ℝ → X} (ha : IsSegment a o x) (r : ℝ) : Space o :=
  MetricLimit.point (sectionOf ha r)
private theorem tendsto_dist {o x y : X} {a b : ℝ → X}
    (ha : IsSegment a o x) (hb : IsSegment b o y) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * dist (a (r / ((n : ℝ) + 1))) (b (t / ((n : ℝ) + 1))))
      (ultrafilter : Filter ℕ) (𝓝 (dist (ray ha r) (ray hb t))) := by
  apply (MetricLimit.tendsto_point_dist (sectionOf ha r) (sectionOf hb t)).congr'
  apply Filter.Eventually.filter_mono (Ultrafilter.of_le _)
  filter_upwards [eventually_parameter hr, eventually_parameter ht] with n hn hm
  change (scale n)⁻¹ * dist _ _ = _
  simp only [sectionOf, ite_eq_left hn, ite_eq_left hm, scale, inv_inv]
theorem ray_zero {o x y : X} {a b : ℝ → X} (ha : IsSegment a o x) (hb : IsSegment b o y) :
    ray ha 0 = ray hb 0 := by
  apply dist_eq_zero.mp
  apply tendsto_nhds_unique (tendsto_dist ha hb le_rfl le_rfl)
  simp only [zero_div, ha.1, hb.1, dist_self, mul_zero]
  exact tendsto_const_nhds
theorem dist_same {o x : X} {a : ℝ → X} (ha : IsSegment a o x) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) :
    dist (ray ha r) (ray ha t) = |r - t| * dist o x := by
  apply tendsto_nhds_unique (tendsto_dist ha ha hr ht)
  apply tendsto_const_nhds.congr'
  apply Filter.Eventually.filter_mono (Ultrafilter.of_le _)
  filter_upwards [eventually_parameter hr, eventually_parameter ht] with n hn hm
  rw [ha.2.2 _ hn _ hm, ← sub_div, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1),
    ← mul_assoc, mul_div_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]
theorem dist_opposite {o x y : X} {a b : ℝ → X}
    (ha : IsSegment a o x) (hb : IsSegment b o y) {c : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, dist (a s) (b s) = s * c) {r : ℝ} (hr : 0 ≤ r) :
    dist (ray ha r) (ray hb r) = r * c := by
  apply tendsto_nhds_unique (tendsto_dist ha hb hr hr)
  apply tendsto_const_nhds.congr'
  apply Filter.Eventually.filter_mono (Ultrafilter.of_le _)
  filter_upwards [eventually_parameter hr] with n hn
  rw [h _ hn, ← mul_assoc, mul_div_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]
private theorem ratio_mono {o x y : X} {a b : ℝ → X} (hB : RadialBusemann X)
    (ha : IsSegment a o x) (hb : IsSegment b o y) :
    MonotoneOn (fun s ↦ dist (a s) (b s) / s) (Ioc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have rest {u : X} {d : ℝ → X} (hd : IsSegment d o u) :
      IsSegment (fun v ↦ d (v*t)) o (d t) := by
    simpa only [mul_zero, zero_add, hd.1] using
      hd.reparam (by norm_num : (0 : ℝ) ∈ Icc 0 1) ⟨ht.1.le, ht.2⟩
  have h := hB o (a t) (b t) _ _ (rest ha) (rest hb) (s / t)
    ⟨div_nonneg hs.1.le ht.1.le, (div_le_one ht.1).mpr hst⟩
  simp only [div_mul_cancel₀ _ ht.1.ne'] at h
  apply (div_le_div_iff₀ hs.1 ht.1).mpr
  calc
    _ ≤ (s / t * dist (a t) (b t)) * t := mul_le_mul_of_nonneg_right h ht.1.le
    _ = _ := by field_simp [ht.1.ne']
theorem dist_pair {o x y : X} {a b : ℝ → X} (hB : RadialBusemann X)
    (ha : IsSegment a o x) (hb : IsSegment b o y) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ dist x y ∧
      (∀ s ∈ Ioc (0 : ℝ) 1, c ≤ dist (a s) (b s) / s) ∧
      ∀ r : ℝ, 0 ≤ r → dist (ray ha r) (ray hb r) = r * c := by
  let f (s : ℝ) := dist (a s) (b s) / s
  let S := f '' Ioc (0 : ℝ) 1
  have h1 : (1 : ℝ) ∈ Ioc 0 1 := ⟨zero_lt_one, le_rfl⟩
  have hmem {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) : f s ∈ S := mem_image_of_mem f hs
  have hne : S.Nonempty := ⟨_, hmem h1⟩
  have hlow : 0 ∈ lowerBounds S := by
    rintro _ ⟨s, hs, rfl⟩
    exact div_nonneg dist_nonneg hs.1.le
  have hinf {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) : sInf S ≤ f s :=
    csInf_le ⟨0, hlow⟩ (hmem hs)
  refine ⟨sInf S, le_csInf hne hlow, ?_, fun _ hs ↦ hinf hs, ?_⟩
  · simpa only [f, ha.2.1, hb.2.1, div_one] using hinf h1
  intro r hr
  rcases hr.eq_or_lt with rfl | hr
  · simp [ray_zero ha hb]
  have hp (n : ℕ) : 0 < r / ((n : ℝ) + 1) := div_pos hr (by positivity)
  have hev : ∀ᶠ n : ℕ in atTop, r / ((n : ℝ) + 1) ∈ Ioc (0 : ℝ) 1 := by
    filter_upwards [eventually_parameter hr.le] with n hn
    exact ⟨hp n, hn.2⟩
  have hf : Tendsto (fun n : ℕ ↦ f (r / ((n : ℝ) + 1))) atTop (𝓝 (sInf S)) := by
    apply tendsto_order.mpr
    constructor
    · intro l hl
      exact hev.mono (fun n hn ↦ hl.trans_le (hinf hn))
    · intro u hu
      obtain ⟨_, ⟨s, hs, rfl⟩, hsu⟩ := exists_lt_of_csInf_lt hne hu
      filter_upwards [hev, (tendsto_parameter r).eventually_lt_const hs.1] with n hn hns
      exact ((ratio_mono hB ha hb) hn hs hns.le).trans_lt hsu
  apply tendsto_nhds_unique (tendsto_dist ha hb hr.le hr.le)
  apply ((hf.const_mul r).mono_left (Ultrafilter.of_le _)).congr
  intro n
  dsimp [f]
  field_simp
end CurvatureBlowup
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace CurvatureBlowup
open HyperbolicObstruction MetricLimit Filter Topology Set
variable {X : Type*} [MetricSpace X]
private theorem scaled_isGeodesic (g : IsGeodesic X) {r : ℝ} (hr : 0 < r) :
    IsGeodesic (MetricScale.Space r hr X) := by
  intro x y
  obtain ⟨γ, hγ⟩ := g x.val y.val
  refine ⟨fun t ↦ ⟨γ t⟩, MetricScale.Space.ext hγ.1, MetricScale.Space.ext hγ.2.1, ?_⟩
  intro s hs t ht
  change r * dist (γ s) (γ t) = |s - t| * (r * dist x.val y.val)
  rw [hγ.2.2 _ hs _ ht]
  ring
private theorem limit_isGeodesic {Z : ℕ → Type*} [∀ n, MetricSpace (Z n)]
    {o : ∀ n, Z n} {ω : Ultrafilter ℕ} (g : ∀ n, IsGeodesic (Z n)) :
    IsGeodesic (MetricLimit.Space (U := ω) (X := Z) (o := o)) := by
  intro x y
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
  choose γ hγ using fun n ↦ g n (x.val n) (y.val n)
  let sec (t : ℝ) : Bounded ω Z o := if ht : t ∈ Icc (0 : ℝ) 1 then
    ⟨fun n ↦ γ n t, by
      obtain ⟨R, hR⟩ := x.bound
      obtain ⟨S, hS⟩ := bounded_dist x y
      refine ⟨R + S, fun n ↦ (dist_triangle _ (x.val n) _).trans ?_⟩
      rw [(hγ n).dist_from_source ht]
      exact add_le_add (hR n) ((mul_le_of_le_one_left dist_nonneg ht.2).trans (hS n).2)⟩
    else x
  have hsec {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (n : ℕ) : (sec t).val n = γ n t := by
    simp only [sec, dite_eq_left ht]
  refine ⟨fun t ↦ point (sec t), ?_, ?_, ?_⟩
  · apply congrArg SeparationQuotient.mk
    exact Bounded.ext (funext fun n ↦ (hsec (by norm_num) n).trans (hγ n).1)
  · apply congrArg SeparationQuotient.mk
    exact Bounded.ext (funext fun n ↦ (hsec (by norm_num) n).trans (hγ n).2.1)
  · intro s hs t ht
    apply tendsto_nhds_unique (tendsto_point_dist _ _)
    apply ((tendsto_point_dist x y).const_mul |s-t|).congr
    intro n
    simp only [hsec hs, hsec ht, (hγ n).2.2 s hs t ht]
theorem isGeodesic (g : IsGeodesic X) (o : X) : IsGeodesic (Space o) :=
  limit_isGeodesic (fun n ↦ scaled_isGeodesic g (inv_pos.mpr (scale_pos n)))
end CurvatureBlowup
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open HyperbolicObstruction Set CurvatureBlowup
variable {X : Type*} [MetricSpace X]
theorem midpoint_comparison_of_quadratic_blowup
    (hB : RadialBusemann X) {m x y z : X} (hsec : QuadraticRaySectors (Space m))
    {a b w : ℝ → X} (ha : IsSegment a m x) (hb : IsSegment b m y) (hw : IsSegment w m z)
    (hmx : dist m x = dist x y / 2) (hmy : dist m y = dist x y / 2) :
    2 * dist z m ^ 2 + dist x y ^ 2 / 2 ≤ dist z x ^ 2 + dist z y ^ 2 ∧
    (2 * dist z m ^ 2 + dist x y ^ 2 / 2 = dist z x ^ 2 + dist z y ^ 2 →
      ∀ s ∈ Icc (0 : ℝ) 1,
        dist (a s) (w s) = s * dist x z ∧ dist (b s) (w s) = s * dist y z) := by
  obtain ⟨c, hc, hcx, hcr, hcw⟩ := dist_pair hB ha hw
  obtain ⟨d, hd, hdy, hdr, hdw⟩ := dist_pair hB hb hw
  have hop (T : ℝ) (hT : 0 < T) : dist (ray ha T) (ray hb T) = 2 * T * dist m x := by
    rw [dist_opposite ha hb (fun _ hs ↦ opposite_segment_separation ha hb (by linarith) hs) hT.le]
    rw [hmx]
    ring
  have poly {p : X} {r : ℝ → X} (hr : IsSegment r m p) {e : ℝ}
      (he : ∀ t, 0 ≤ t → dist (ray hr t) (ray hw t) = t * e) :=
    hsec (ray hr) (ray hw) (dist m p) (dist m z) e (ray_zero hr hw)
      (fun _ _ hs ht ↦ dist_same hr hs ht) (fun _ _ hs ht ↦ dist_same hw hs ht) he
  have hbpoly := poly hb hdw
  rw [show dist m y = dist m x by linarith] at hbpoly
  have hmid := midpoint_bound_of_opposite_sectors (ray ha) (ray hb) (ray hw 1)
    (dist m x) (dist m z) c d hop (poly ha hcw) hbpoly
  rw [hmx] at hmid
  rw [dist_comm z m, dist_comm z x, dist_comm z y]
  have hc₂ := (sq_le_sq₀ hc dist_nonneg).mpr hcx
  have hd₂ := (sq_le_sq₀ hd dist_nonneg).mpr hdy
  refine ⟨by linarith, ?_⟩
  intro heq s hs
  have hceq : c = dist x z := by nlinarith
  have hdeq : d = dist y z := by nlinarith
  subst c d
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · simp [ha.1, hb.1, hw.1]
  · exact ⟨le_antisymm (hB m x z a w ha hw s hs)
        (by simpa [mul_comm] using (le_div_iff₀ hspos).mp (hcr s ⟨hspos, hs.2⟩)),
      le_antisymm (hB m y z b w hb hw s hs)
        (by simpa [mul_comm] using (le_div_iff₀ hspos).mp (hdr s ⟨hspos, hs.2⟩))⟩
theorem catZero_of_quadratic_blowups (g : IsGeodesic X) (hB : RadialBusemann X)
    (hsec : ∀ o : X, QuadraticRaySectors (Space o)) : CATZero X := by
  apply catZero_of_segment_midpoint g
  intro γ x y hγ z
  let m := γ (1 / 2)
  have ht : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  have hmx : dist m x = dist x y / 2 := by
    rw [dist_comm]
    simpa [m, div_eq_mul_inv, mul_comm] using hγ.dist_from_source ht
  have hmy : dist m y = dist x y / 2 := by
    have h := hγ.2.2 _ ht 1 (by norm_num)
    rw [hγ.2.1] at h
    norm_num at h
    simpa [m, div_eq_mul_inv, mul_comm] using h
  obtain ⟨a, ha⟩ := g m x
  obtain ⟨b, hb⟩ := g m y
  obtain ⟨w, hw⟩ := g m z
  have h := (midpoint_comparison_of_quadratic_blowup hB (hsec m) ha hb hw hmx hmy).1
  change dist z m ^ 2 ≤ _
  linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem parallelogram_eq_of_le (h : ∀ a b : V,
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)) (x y : V) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  refine le_antisymm (h x y) ?_
  have h' := h (x + y) (x - y)
  have hp : x + y + (x - y) = (2 : ℝ) • x := by rw [two_smul]; abel
  have hm : x + y - (x - y) = (2 : ℝ) • y := by rw [two_smul]; abel
  rw [hp, hm, norm_smul, norm_smul, Real.norm_ofNat] at h'
  linarith
theorem innerProductSpace_of_dualParallelogramLe
    (h : ∀ a b : StrongDual ℝ V,
      ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2)) :
    Nonempty (InnerProductSpace ℝ V) := by
  let : InnerProductSpace ℝ (StrongDual ℝ V) :=
    InnerProductSpace.ofNorm ℝ fun a b ↦ by simpa [sq] using parallelogram_eq_of_le h a b
  let j := NormedSpace.inclusionInDoubleDualLi (E := V) ℝ
  let r := (InnerProductSpace.toDual ℝ (StrongDual ℝ V)).symm
  refine ⟨InnerProductSpace.ofNorm ℝ fun x y ↦ ?_⟩
  simpa only [← r.map_add, ← r.map_sub, ← j.map_add, ← j.map_sub,
    LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
    using parallelogram_law_with_norm_mul ℝ (r (j x)) (r (j y))
theorem innerProductSpace_of_dualBallParallelogramLe
    (h : ∀ (t u : ℝ), 0 < t → 0 < u → ∀ f g : StrongDual ℝ V, ‖f‖ ≤ 1 → ‖g‖ ≤ 1 →
      ‖t • f + u • g‖ ^ 2 + ‖t • f - u • g‖ ^ 2 ≤ 2 * (t ^ 2 + u ^ 2)) :
    Nonempty (InnerProductSpace ℝ V) := by
  apply innerProductSpace_of_dualParallelogramLe
  intro a b
  by_cases ha : a = 0
  · subst a; simp; linarith
  by_cases hb : b = 0
  · subst b; simp; linarith
  have normed (v : StrongDual ℝ V) (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀
      (norm_ne_zero_iff.mpr hv)]
  simpa [smul_smul, norm_ne_zero_iff.mpr ha, norm_ne_zero_iff.mpr hb] using
    h ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb)
      (‖a‖⁻¹ • a) (‖b‖⁻¹ • b) (normed a ha) (normed b hb)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
def FiniteMetricModel (X E : Type*) [PseudoMetricSpace X] [PseudoMetricSpace E] : Prop :=
  ∀ {I : Type} [Fintype I] (p : I → E), ∃ q : I → X, ∀ i j, dist (q i) (q j) = dist (p i) (p j)
def SectorNormRigidity (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    FiniteMetricModel X E → Nonempty (InnerProductSpace ℝ E)
def ScaledFiniteMetricModel (X E : Type*) [PseudoMetricSpace X] [PseudoMetricSpace E] : Prop :=
  ∀ {I : Type} [Fintype I] (p : I → E), ∃ c : ℝ, 0 < c ∧ ∃ q : I → X,
    ∀ i j, dist (q i) (q j) = c * dist (p i) (p j)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Set Topology
universe w
variable {K V : Type*} [Field K] [NormedAddCommGroup V] [NormedSpace ℝ V]
def HasFiniteSpectralRealizationsOn (K : Type*) [Field K] {Y : Type*} [MetricSpace Y]
    (U : Set Y) : Prop :=
  ∀ S : Finset Y, S.Nonempty → (S : Set Y) ⊆ U →
    ∃ (X : Type w) (_ : MetricSpace X) (_ : SpectralPlacementPrices K X) (c : ℝ),
      0 < c ∧ ∃ f : Y → X, ∀ p ∈ S, ∀ q ∈ S, dist (f p) (f q) = c * dist p q
theorem HasFiniteSpectralRealizationsOn.prices {Y : Type*} [MetricSpace Y] [Nonempty Y]
    (h : HasFiniteSpectralRealizationsOn.{w} K (Set.univ : Set Y)) :
    Nonempty (SpectralPlacementPrices K Y) := by
  classical
  let o : Y := Classical.arbitrary Y
  choose X m P c hc f hf using fun S : Finset Y ↦
    h (insert o S) (Finset.insert_nonempty _ _) (Set.subset_univ _)
  let ω := Ultrafilter.of (atTop : Filter (Finset Y))
  refine ⟨SpectralPlacementPrices.blowupFamily P ω c hc f o fun x y ↦ ?_⟩
  apply Tendsto.mono_left _ (Ultrafilter.of_le _)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ({x,y} : Finset Y)] with S hS
  rw [hf _ _ (Finset.mem_insert_of_mem (hS (by simp))) _
    (Finset.mem_insert_of_mem (hS (by simp))), mul_div_cancel_left₀ _ (hc S).ne']
theorem spectralPrices_of_finite_scaled_models {X : Type w} [PseudoMetricSpace X]
    {Y : Type*} [MetricSpace Y] [Nonempty Y] (h : ScaledFiniteMetricModel X Y)
    (P : SpectralPlacementPrices K X) : Nonempty (SpectralPlacementPrices K Y) := by
  classical
  apply HasFiniteSpectralRealizationsOn.prices.{w}
  intro S hS _
  obtain ⟨o, ho⟩ := hS
  let e : (↑S : Set Y) ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  obtain ⟨c, hc, q, hq⟩ := h (fun i ↦ (e.symm i).val)
  let j (x : Y) : (↑S : Set Y) := if hx : x ∈ S then ⟨x, hx⟩ else ⟨o, ho⟩
  refine ⟨SeparationQuotient X, inferInstance, P.separationQuotient, c, hc,
    fun x ↦ SeparationQuotient.mk (q (e (j x))), ?_⟩
  intro x hx y hy
  simp [SeparationQuotient.dist_mk, hq, j, hx, hy]
theorem FiniteMetricModel.spectralPrices {X : Type w} [PseudoMetricSpace X]
    {Y : Type*} [MetricSpace Y] [Nonempty Y] (h : FiniteMetricModel X Y)
    (P : SpectralPlacementPrices K X) : Nonempty (SpectralPlacementPrices K Y) := by
  apply spectralPrices_of_finite_scaled_models _ P
  intro I _ p
  obtain ⟨q, hq⟩ := h p
  exact ⟨1, zero_lt_one, q, by simpa using hq⟩
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open HyperbolicObstruction Set
variable {X : Type*} [MetricSpace X]
def SectorFraction (a b z : X) (t : ℝ) : Prop :=
  dist a z = t * dist a b ∧ dist z b = (1-t) * dist a b
def SectorBusemann (X : Type*) [MetricSpace X] : Prop :=
  ∀ a b a' b' z w : X, ∀ t ∈ Icc (0 : ℝ) 1,
    SectorFraction a b z t → SectorFraction a' b' w t →
    dist z w ≤ (1-t) * dist a a' + t * dist b b'
noncomputable def sectorSegment (g : IsGeodesic X) (a b : X) : ℝ → X := (g a b).choose
theorem sectorSegment_fraction (g : IsGeodesic X) (a b : X) {t : ℝ} (ht : t ∈ Icc 0 1) :
    SectorFraction a b (sectorSegment g a b t) t := by
  have h : IsSegment (sectorSegment g a b) a b := (g a b).choose_spec
  constructor
  · calc
      dist a _ = dist (sectorSegment g a b 0) (sectorSegment g a b t) := by rw [h.1]
      _ = _ := by simpa [abs_of_nonneg ht.1] using h.2.2 0 (by norm_num) t ht
  · calc
      dist _ b = dist (sectorSegment g a b t) (sectorSegment g a b 1) := by rw [h.2.1]
      _ = _ := by simpa [abs_of_nonpos (sub_nonpos.mpr ht.2)] using h.2.2 t ht 1 (by norm_num)
theorem SectorBusemann.fraction_unique (hB : SectorBusemann X) {a b z w : X} {t : ℝ}
    (ht : t ∈ Icc 0 1) (hz : SectorFraction a b z t) (hw : SectorFraction a b w t) :
    z = w := by
  exact dist_le_zero.mp (by simpa using hB a b a b z w t ht hz hw)
def sectorDomain (D : Set ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ∈ D}
private theorem sectorRatio_mem {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    v / (u+v) ∈ Icc 0 1 := by
  rcases eq_or_lt_of_le (add_nonneg hu hv) with h | h
  · simp [← h]
  exact ⟨div_nonneg hv h.le, (div_le_one h).mpr (by linarith)⟩
noncomputable def sectorMap (g : IsGeodesic X) (a b : ℝ → X) (p : ℝ × ℝ) : X :=
  sectorSegment g (a (p.1+p.2)) (b (p.1+p.2)) (p.2/(p.1+p.2))
theorem sectorMap_boundary_dist (g : IsGeodesic X) {a b : ℝ → X} {D : Set ℝ} {c : ℝ}
    (hsep : ∀ r ∈ D, dist (a r) (b r) = c*r) {p : ℝ × ℝ} (hp : p ∈ sectorDomain D) :
    dist (a (p.1+p.2)) (sectorMap g a b p) = c*p.2 ∧
    dist (sectorMap g a b p) (b (p.1+p.2)) = c*p.1 := by
  obtain ⟨hu, hv, hD⟩ := hp
  obtain ⟨ha, hb⟩ := sectorSegment_fraction g (a (p.1+p.2)) (b (p.1+p.2))
    (sectorRatio_mem hu hv)
  change dist _ (sectorMap g a b p) = _ at ha
  change dist (sectorMap g a b p) _ = _ at hb
  rw [hsep _ hD] at ha hb
  rcases eq_or_lt_of_le (add_nonneg hu hv) with h | h
  · have hu0 : p.1 = 0 := by linarith
    have hv0 : p.2 = 0 := by linarith
    simpa [hu0, hv0] using And.intro ha hb
  · constructor
    · rw [ha]
      field_simp
    · rw [hb]
      field_simp
      ring
private theorem radial_fraction {a : ℝ → X} {D : Set ℝ} {A : ℝ}
    (ha : ∀ r ∈ D, ∀ s ∈ D, dist (a r) (a s) = |r-s| * A)
    {r s t : ℝ} (hr : r ∈ D) (hs : s ∈ D) (ht : t ∈ Icc 0 1)
    (hi : (1-t)*r+t*s ∈ D) :
    SectorFraction (a r) (a s) (a ((1-t)*r+t*s)) t := by
  constructor
  · rw [ha _ hr _ hi, ha _ hr _ hs, show r-((1-t)*r+t*s) = t*(r-s) by ring,
      abs_mul, abs_of_nonneg ht.1]
    ring
  · rw [ha _ hi _ hs, ha _ hr _ hs, show (1-t)*r+t*s-s = (1-t)*(r-s) by ring,
      abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    ring
theorem sectorMap_affine (g : IsGeodesic X) (hB : SectorBusemann X)
    {a b : ℝ → X} {D : Set ℝ} (hD : Convex ℝ D) {A B c : ℝ}
    (ha : ∀ r ∈ D, ∀ s ∈ D, dist (a r) (a s) = |r-s| * A)
    (hb : ∀ r ∈ D, ∀ s ∈ D, dist (b r) (b s) = |r-s| * B)
    (hsep : ∀ r ∈ D, dist (a r) (b r) = c*r)
    {p q : ℝ × ℝ} (hp : p ∈ sectorDomain D) (hq : q ∈ sectorDomain D)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    sectorMap g a b ((1-t) • p + t • q) =
      sectorSegment g (sectorMap g a b p) (sectorMap g a b q) t := by
  let k := (1-t) • p + t • q
  let w := sectorSegment g (sectorMap g a b p) (sectorMap g a b q) t
  have hw : SectorFraction (sectorMap g a b p) (sectorMap g a b q) w t :=
    sectorSegment_fraction g _ _ ht
  have hk₁ : k.1 = (1-t)*p.1+t*q.1 := rfl
  have hk₂ : k.2 = (1-t)*p.2+t*q.2 := rfl
  have hr : k.1+k.2 = (1-t)*(p.1+p.2)+t*(q.1+q.2) := by rw [hk₁, hk₂]; ring
  have ht' := sub_nonneg.mpr ht.2
  have hsum : (1-t)*(p.1+p.2)+t*(q.1+q.2) ∈ D :=
    hD hp.2.2 hq.2.2 ht' ht.1 (by ring)
  have hk : k ∈ sectorDomain D := ⟨add_nonneg (mul_nonneg ht' hp.1) (mul_nonneg ht.1 hq.1),
    add_nonneg (mul_nonneg ht' hp.2.1) (mul_nonneg ht.1 hq.2.1), hr ▸ hsum⟩
  have hp' := sectorMap_boundary_dist g hsep hp
  have hq' := sectorMap_boundary_dist g hsep hq
  have hleft := hB _ _ _ _ _ _ t ht (radial_fraction ha hp.2.2 hq.2.2 ht hsum) hw
  have hright := hB _ _ _ _ _ _ t ht hw (radial_fraction hb hp.2.2 hq.2.2 ht hsum)
  rw [←hr, hp'.1, hq'.1] at hleft
  rw [←hr, hp'.2, hq'.2] at hright
  rw [show (1-t)*(c*p.2)+t*(c*q.2) = c*k.2 by rw [hk₂]; ring] at hleft
  rw [show (1-t)*(c*p.1)+t*(c*q.1) = c*k.1 by rw [hk₁]; ring] at hright
  have htr := dist_triangle (a (k.1+k.2)) w (b (k.1+k.2))
  rw [hsep _ hk.2.2] at htr
  have hval := sectorMap_boundary_dist g hsep hk
  have hfra := sectorSegment_fraction g (a (k.1+k.2)) (b (k.1+k.2)) (sectorRatio_mem hk.1 hk.2.1)
  apply hB.fraction_unique (sectorRatio_mem hk.1 hk.2.1) hfra
  constructor
  · rw [←hfra.1]
    change dist _ w = dist _ (sectorMap g a b k)
    rw [hval.1]
    linarith only [hleft, hright, htr]
  · rw [←hfra.2]
    change dist w _ = dist (sectorMap g a b k) _
    rw [hval.2]
    linarith only [hleft, hright, htr]
theorem sectorMap_axes (g : IsGeodesic X) {a b : ℝ → X} {D : Set ℝ} {c r : ℝ}
    (hsep : ∀ s ∈ D, dist (a s) (b s) = c*s) (hr : 0 ≤ r) (hrD : r ∈ D) :
    sectorMap g a b (r,0) = a r ∧ sectorMap g a b (0,r) = b r := by
  have h₁ := (sectorMap_boundary_dist g hsep (p := (r,0)) ⟨hr, le_rfl, by simpa⟩).1
  have h₂ := (sectorMap_boundary_dist g hsep (p := (0,r)) ⟨le_rfl, hr, by simpa⟩).2
  constructor
  · exact (dist_eq_zero.mp (by simpa using h₁)).symm
  · exact dist_eq_zero.mp (by simpa using h₂)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
private theorem finite_translate_quadrant {I : Type} [Fintype I] (p : I → ℝ × ℝ) :
    ∃ k : ℝ × ℝ, ∀ i, 0 ≤ p i + k := by
  classical
  refine ⟨(∑ i, |(p i).1|, ∑ i, |(p i).2|), fun i ↦ ⟨?_, ?_⟩⟩
  · have hs : |(p i).1| ≤ ∑ j, |(p j).1| := Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (p j).1) (Finset.mem_univ i)
    change 0 ≤ (p i).1 + ∑ j, |(p j).1|
    linarith [neg_le_abs (p i).1]
  · have hs : |(p i).2| ≤ ∑ j, |(p j).2| := Finset.single_le_sum
      (fun j _ ↦ abs_nonneg (p j).2) (Finset.mem_univ i)
    change 0 ≤ (p i).2 + ∑ j, |(p j).2|
    linarith [neg_le_abs (p i).2]
private theorem seminorm_sq_of_quotient_rigidity {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (N : Seminorm ℝ V)
    (hquot : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (π : V →ₗ[ℝ] E), Function.Surjective π → (∀ z, ‖π z‖ = N z) →
      Nonempty (InnerProductSpace ℝ E))
    (x y : V) (s t : ℝ) :
    N (s • x - t • y) ^ 2 = s ^ 2 * N x ^ 2 + t ^ 2 * N y ^ 2 +
      s * t * (N (x-y) ^ 2 - N x ^ 2 - N y ^ 2) := by
  classical
  let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
  let : NormedSpace ℝ V := ⟨fun a z ↦ (map_smul_eq_mul N a z).le⟩
  let E := SeparationQuotient V
  let π : V →ₗ[ℝ] E := (SeparationQuotient.mkCLM ℝ V).toLinearMap
  have hπ : Function.Surjective π := SeparationQuotient.surjective_mk
  let : FiniteDimensional ℝ E := FiniteDimensional.of_surjective π hπ
  have hnorm (z : V) : ‖π z‖ = N z := rfl
  have hpar : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ =
      2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
    let : InnerProductSpace ℝ E := (hquot E π hπ hnorm).some
    exact parallelogram_law_with_norm_mul ℝ
  let : InnerProductSpace ℝ E := InnerProductSpace.ofNorm ℝ hpar
  simp only [← hnorm, map_sub, map_smul, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    real_inner_smul_left, real_inner_smul_right, mul_pow, sq_abs]
  ring
theorem quadrant_seminorm_sq_of_rigidity {X : Type*} [MetricSpace X]
    (hX : SectorNormRigidity X) (H : ℝ × ℝ → X) (N : Seminorm ℝ (ℝ × ℝ))
    (hN : ∀ p q, 0 ≤ p → 0 ≤ q → dist (H p) (H q) = N (p - q))
    (x y : ℝ × ℝ) (s t : ℝ) :
    N (s • x - t • y) ^ 2 = s ^ 2 * N x ^ 2 + t ^ 2 * N y ^ 2 +
      s * t * (N (x-y) ^ 2 - N x ^ 2 - N y ^ 2) := by
  classical
  apply seminorm_sq_of_quotient_rigidity N _ x y s t
  intro E _ _ _ π hπ hnorm
  apply hX E
  intro I _ p
  choose v hv using fun i ↦ hπ (p i)
  obtain ⟨k, hk⟩ := finite_translate_quadrant v
  refine ⟨fun i ↦ H (v i + k), fun i j ↦ ?_⟩
  rw [hN _ _ (hk i) (hk j), add_sub_add_right_eq_sub, ← hv, ← hv, dist_eq_norm,
    ← map_sub, hnorm]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Set
open scoped Topology
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]
theorem convex_chord_dist_boundary {C : Set E} (hC : Convex ℝ C)
    (hI : (interior C).Nonempty) (H : E → X)
    (hseg : ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H p) (H ((1-t) • p + t • q)) = t * dist (H p) (H q))
    (N : Seminorm ℝ E) (hN : ∀ p ∈ interior C, ∀ q ∈ interior C,
      dist (H p) (H q) = N (p-q)) :
    ∀ p ∈ C, ∀ q ∈ C, dist (H p) (H q) = N (p-q) := by
  obtain ⟨o, ho⟩ := hI
  let chord (x : E) (t : ℝ) := (1-t) • x + t • o
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
  have hzero : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim (x : E) (hx : x ∈ C) :
      Tendsto (fun t ↦ H (chord x t)) (𝓝[>] 0) (𝓝 (H x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h := hzero.mul_const (dist (H x) (H o))
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [hsmall] with t ht
    exact (hseg x hx o (interior_subset ho) t ⟨ht.1.le, ht.2.le⟩).symm.trans (dist_comm _ _)
  have hint (x : E) (hx : x ∈ C) (t : ℝ) (ht : t ∈ Ioo 0 1) :
      chord x t ∈ interior C :=
    hC.openSegment_self_interior_subset_interior hx ho
      ⟨1-t, t, sub_pos.mpr ht.2, ht.1, sub_add_cancel _ _, rfl⟩
  intro p hp q hq
  have hnorm := ((tendsto_const_nhds (x := (1 : ℝ))).sub hzero).mul_const (N (p-q))
  apply tendsto_nhds_unique ((hlim p hp).dist (hlim q hq))
  simp only [sub_zero, one_mul] at hnorm
  apply hnorm.congr'
  filter_upwards [hsmall] with t ht
  rw [hN _ (hint p hp t ht) _ (hint q hq t ht)]
  simp only [chord, add_sub_add_right_eq_sub, ← smul_sub, map_smul_eq_mul,
    Real.norm_of_nonneg (sub_nonneg.mpr ht.2.le)]
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set Filter
open scoped Topology
variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} (H : E → X) (hseg : ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 → dist (H p) (H ((1 - t) • p + t • q)) = t * dist (H p) (H q)) (hcon : ∀ z ∈ C, ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 → dist (H ((1-t) • z + t • p)) (H ((1-t) • z + t • q)) ≤ t * dist (H p) (H q))
include hseg hcon
theorem convex_chord_dist_le {p q r s : E} (hp : p ∈ interior C)
    (hq : q ∈ C) (hr : r ∈ C) (hs : s ∈ C) {c : ℝ} (hc : 0 < c)
    (he : q - p = c • (s - r)) : dist (H p) (H q) ≤ c * dist (H r) (H s) := by
  let z (t : ℝ) := (1-t)⁻¹ • (p - t • r)
  have hcont : ContinuousAt z 0 := by dsimp [z]; fun_prop (disch := norm_num)
  have hz : ∀ᶠ t in 𝓝[>] (0 : ℝ), z t ∈ C := by
    apply eventually_nhdsWithin_of_eventually_nhds
    apply hcont (mem_interior_iff_mem_nhds.1 ?_)
    simpa [z] using hp
  have ht₁ : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds zero_lt_one)
  have htc : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < c :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hc)
  have ht₀ : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t,hz,ht₁,htc,ht₀⟩ := (hz.and (ht₁.and (htc.and ht₀))).exists
  have hbase : (1-t) • z t + t • r = p := by
    simp [z, smul_smul, sub_ne_zero.mpr ht₁.ne']
  have htI : t / c ∈ Icc 0 1 := ⟨div_nonneg ht₀.le hc.le, (div_le_one hc).2 htc.le⟩
  have htq : (t / c) • (q - p) = t • (s - r) := by
    rw [he, smul_smul, div_mul_cancel₀ _ hc.ne']
  have hend : (1-t) • z t + t • s = (1 - t/c) • p + (t/c) • q := by
    calc
      (1-t) • z t + t • s = ((1-t) • z t + t • r) + t • (s-r) := by rw [smul_sub]; abel
      _ = p + (t / c) • (q - p) := by rw [hbase, htq]
      _ = _ := by rw [smul_sub, sub_smul, one_smul]; abel
  have h := hcon (z t) hz r hr s hs t ⟨ht₀.le,ht₁.le⟩
  rw [hbase, hend, hseg p (interior_subset hp) q hq _ htI] at h
  have h' := mul_le_mul_of_nonneg_left h hc.le
  rw [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at h'
  apply le_of_mul_le_mul_left _ ht₀
  convert h' using 1
  ring
theorem convex_chord_dist_eq {p q r s : E} (hp : p ∈ interior C)
    (hq : q ∈ C) (hr : r ∈ interior C) (hs : s ∈ C) {c : ℝ} (hc : 0 < c)
    (he : q - p = c • (s-r)) : dist (H p) (H q) = c * dist (H r) (H s) := by
  refine le_antisymm (convex_chord_dist_le H hseg hcon hp hq (interior_subset hr) hs hc he) ?_
  have he' : s - r = c⁻¹ • (q-p) := by rw [he, inv_smul_smul₀ hc.ne']
  have h := convex_chord_dist_le H hseg hcon hr hs (interior_subset hp) hq (inv_pos.mpr hc) he'
  simpa only [mul_inv_cancel_left₀ hc.ne'] using mul_le_mul_of_nonneg_left h hc.le
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Set Topology
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]
private theorem seminorm_of_interior_chords {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (H : E → X)
    (hchord : ∀ {p q r s : E}, p ∈ U → q ∈ U → r ∈ U → s ∈ U →
      ∀ {c : ℝ}, 0 < c → q - p = c • (s - r) → dist (H p) (H q) = c * dist (H r) (H s)) :
    ∃ N : Seminorm ℝ E, ∀ p ∈ U, ∀ q ∈ U, dist (H p) (H q) = N (p - q) := by
  classical
  obtain ⟨o, ho⟩ := hne
  have shrink (v : E) : ∀ᶠ t : ℝ in 𝓝[>] 0, o + t • v ∈ U := by
    have hlim : Tendsto (fun t : ℝ ↦ o + t • v) (𝓝[>] 0) (𝓝 o) := by
      simpa using ((tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v).const_add o
    exact hlim (hU.mem_nhds ho)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  choose k hk hkU using fun v ↦ (hpos.and (shrink v)).exists
  let f (v : E) := dist (H o) (H (o + k v • v)) / k v
  have rep {p q : E} (hp : p ∈ U) (hq : q ∈ U) {c : ℝ} (hc : 0 < c) (v : E)
      (he : q - p = c • v) : dist (H p) (H q) = c * f v := by
    calc
      _ = (c / k v) * dist (H o) (H (o + k v • v)) := by
        apply hchord hp hq ho (hkU v) (div_pos hc (hk v))
        rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ (hk v).ne', he]
      _ = _ := by dsimp [f]; ring
  have fzero : f 0 = 0 := by simp [f]
  have fneg (v : E) : f (-v) = f v := by
    have h := rep (hkU v) ho (hk v) (-v) (by simp)
    rw [dist_comm, rep ho (hkU v) (hk v) v (by simp)] at h
    exact (mul_left_cancel₀ (hk v).ne' h).symm
  have fpos (a : ℝ) (ha : 0 < a) (v : E) : f (a • v) = a * f v := by
    let t := k (a • v)
    have ht : 0 < t := hk _
    have h : o + t • (a • v) ∈ U := hkU _
    have hd := rep ho h ht (a • v) (by simp)
    rw [rep ho h (mul_pos ht ha) v (by rw [add_sub_cancel_left, smul_smul]), mul_assoc] at hd
    exact (mul_left_cancel₀ ht.ne' hd).symm
  have fadd (v w : E) : f (v + w) ≤ f v + f w := by
    obtain ⟨t, ht, hv, hvw⟩ := (hpos.and ((shrink v).and (shrink (v+w)))).exists
    have hd := dist_triangle (H o) (H (o+t • v)) (H (o+t • (v+w)))
    rw [rep ho hvw ht (v+w) (by simp), rep ho hv ht v (by simp),
      rep hv hvw ht w (by simp [smul_add]), ← mul_add] at hd
    exact le_of_mul_le_mul_left hd ht
  refine ⟨Seminorm.of f fadd (fun a v ↦ ?_), fun p hp q hq ↦ ?_⟩
  · rcases lt_trichotomy a 0 with ha | rfl | ha
    · have h := fpos (-a) (neg_pos.mpr ha) v
      rw [neg_smul, fneg] at h
      simpa [Real.norm_eq_abs, abs_of_neg ha] using h
    · simp [fzero]
    · rw [Real.norm_of_nonneg ha.le, fpos a ha]
  · change dist (H p) (H q) = f (p-q)
    rw [dist_comm]
    simpa using rep hq hp zero_lt_one (p-q) (by simp)
theorem convex_seminorm_of_affine {C : Set E} (hC : Convex ℝ C)
    (hI : (interior C).Nonempty) (H : E → X)
    (hseg : ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H p) (H ((1 - t) • p + t • q)) = t * dist (H p) (H q))
    (hcon : ∀ z ∈ C, ∀ p ∈ C, ∀ q ∈ C, ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H ((1-t) • z + t • p)) (H ((1-t) • z + t • q)) ≤ t * dist (H p) (H q)) :
    ∃ N : Seminorm ℝ E, ∀ p ∈ C, ∀ q ∈ C, dist (H p) (H q) = N (p-q) := by
  obtain ⟨N, hN⟩ := seminorm_of_interior_chords isOpen_interior hI H
    (fun {_ _ _ _} hp hq hr hs {_} hc he ↦ convex_chord_dist_eq H hseg hcon hp (interior_subset hq)
      hr (interior_subset hs) hc he)
  exact ⟨N, convex_chord_dist_boundary hC hI H hseg N hN⟩
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Set
variable {X : Type*} [PseudoMetricSpace X]
theorem quadrant_seminorm_of_affine (H : (ℝ × ℝ) → X)
    (hseg : ∀ p q : ℝ × ℝ, 0 ≤ p → 0 ≤ q → ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H p) (H ((1 - t) • p + t • q)) = t * dist (H p) (H q))
    (hcon : ∀ z p q : ℝ × ℝ, 0 ≤ z → 0 ≤ p → 0 ≤ q → ∀ t : ℝ, t ∈ Icc 0 1 →
      dist (H ((1-t) • z + t • p)) (H ((1-t) • z + t • q)) ≤ t * dist (H p) (H q)) :
    ∃ N : Seminorm ℝ (ℝ × ℝ), ∀ p q, 0 ≤ p → 0 ≤ q → dist (H p) (H q) = N (p - q) := by
  have hC : Convex ℝ (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)) :=
    (convex_Ici _).prod (convex_Ici _)
  have hI : (interior (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ))).Nonempty := by
    refine ⟨(1,1), ?_⟩
    rw [interior_prod_eq, interior_Ici]
    change 0 < (1 : ℝ) ∧ 0 < (1 : ℝ)
    norm_num
  obtain ⟨N, hN⟩ := convex_seminorm_of_affine hC hI H
    (fun p hp q hq ↦ hseg p q hp hq) (fun z hz p hp q hq ↦ hcon z p q hz hp hq)
  exact ⟨N, fun p q hp hq ↦ hN p hp q hq⟩
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open HyperbolicObstruction Set
variable {X : Type*} [MetricSpace X]
theorem sectorMap_ray_seminorm (g : IsGeodesic X) (hB : SectorBusemann X)
    {a b : ℝ → X} {A B c : ℝ}
    (ha : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → dist (a r) (a s) = |r-s| * A)
    (hb : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → dist (b r) (b s) = |r-s| * B)
    (hsep : ∀ r : ℝ, 0 ≤ r → dist (a r) (b r) = r*c) :
    ∃ N : Seminorm ℝ (ℝ × ℝ), ∀ p q, 0 ≤ p → 0 ≤ q →
      dist (sectorMap g a b p) (sectorMap g a b q) = N (p - q) := by
  let H := sectorMap g a b
  have hdom {p : ℝ × ℝ} (hp : 0 ≤ p) : p ∈ sectorDomain (Ici 0) :=
    ⟨hp.1, hp.2, add_nonneg hp.1 hp.2⟩
  have hfrac (p q : ℝ × ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) {t : ℝ} (ht : t ∈ Icc 0 1) :
      SectorFraction (H p) (H q) (H ((1-t) • p + t • q)) t := by
    change SectorFraction _ _ (sectorMap g a b _) _
    rw [sectorMap_affine g hB (convex_Ici (0 : ℝ))
      (fun r hr s hs ↦ ha r s hr hs) (fun r hr s hs ↦ hb r s hr hs)
      (fun r hr ↦ (hsep r hr).trans (mul_comm r c)) (hdom hp) (hdom hq) ht]
    exact sectorSegment_fraction g _ _ ht
  apply quadrant_seminorm_of_affine H
  · exact fun p q hp hq _ ht ↦ (hfrac p q hp hq ht).1
  · intro z p q hz hp hq t ht
    simpa using hB _ _ _ _ _ _ t ht (hfrac z p hz hp ht) (hfrac z q hz hq ht)
theorem quadraticRaySectors_of_normRigidity (g : IsGeodesic X)
    (hB : SectorBusemann X) (hX : SectorNormRigidity X) : QuadraticRaySectors X := by
  intro a b A B c ho ha hb hsep t ht
  let H := sectorMap g a b
  obtain ⟨N, hN⟩ := sectorMap_ray_seminorm g hB ha hb hsep
  change ∀ p q, 0 ≤ p → 0 ≤ q → dist (H p) (H q) = N (p-q) at hN
  have haxes (r : ℝ) (hr : 0 ≤ r) : H (r,0) = a r ∧ H (0,r) = b r :=
    sectorMap_axes g (D := Ici 0) (fun s hs ↦ (hsep s hs).trans (mul_comm s c)) hr hr
  have hzero : H 0 = a 0 := (haxes 0 le_rfl).1
  let e : ℝ × ℝ := (1,0)
  let f : ℝ × ℝ := (0,1)
  have he : 0 ≤ e := ⟨zero_le_one, le_rfl⟩
  have hf : 0 ≤ f := ⟨le_rfl, zero_le_one⟩
  have ha₁ : N e = A := by
    have hh := hN e 0 he le_rfl
    rw [sub_zero] at hh
    rw [←hh, (haxes 1 zero_le_one).1, hzero, ha 1 0 zero_le_one le_rfl]
    norm_num
  have hb₁ : N f = B := by
    have hh := hN f 0 hf le_rfl
    rw [sub_zero] at hh
    rw [←hh, (haxes 1 zero_le_one).2, hzero, ho, hb 1 0 zero_le_one le_rfl]
    norm_num
  have hc₁ : N (e-f) = c := by
    rw [← hN _ _ he hf, (haxes 1 zero_le_one).1, (haxes 1 zero_le_one).2, hsep 1 zero_le_one,
      one_mul]
  have hte : t • e = (t,0) := by simp [e]
  have hdiag := quadrant_seminorm_sq_of_rigidity hX H N hN e f t 1
  simp only [one_smul, one_pow, one_mul, mul_one] at hdiag
  rw [←hN _ _ (smul_nonneg ht.le he) hf, hte, (haxes t ht.le).1, (haxes 1 zero_le_one).2,
    ha₁, hb₁, hc₁] at hdiag
  simpa only [mul_pow] using hdiag
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open HyperbolicObstruction
theorem ShiftedCrossingCost.innerProductSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (cost : ShiftedCrossingCost E) :
    Nonempty (InnerProductSpace ℝ E) := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    refine ⟨InnerProductSpace.ofNorm ℝ (fun a b ↦ ?_)⟩
    simp [Subsingleton.elim a 0, Subsingleton.elim b 0]
  | inr h =>
    apply innerProductSpace_of_dualBallParallelogramLe
    exact fun t u ht hu ↦ dualBall_crossingBound_of_smooth t u
      (fun _ _ _ _ hx hy hf hg ↦ cost.smooth_dual hx hy hf hg ht hu)
theorem SectorBusemann.radial {X : Type*} [MetricSpace X]
    (hB : SectorBusemann X) : RadialBusemann X := by
  intro o x y a b ha hb t ht
  have hf {p : X} {r : ℝ → X} (hr : IsSegment r o p) : SectorFraction o p (r t) t := by
    refine ⟨hr.dist_from_source ht, ?_⟩
    have hh := hr.2.2 t ht 1 (by norm_num)
    simpa [hr.2.1, abs_of_nonpos (sub_nonpos.mpr ht.2)] using hh
  simpa using hB o x o y (a t) (b t) t ht (hf ha) (hf hb)
variable {K X : Type*} [Field K] [MetricSpace X]
theorem SpectralPlacementPrices.catZero_of_shiftedCost (P : SpectralPlacementPrices K X)
    (g : IsGeodesic X) (hB : SectorBusemann X)
    (hB' : ∀ o : X, SectorBusemann (CurvatureBlowup.Space o))
    (hc : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      SpectralPlacementPrices K E → ShiftedCrossingCost E) : CATZero X := by
  apply catZero_of_quadratic_blowups g hB.radial
  intro o
  apply quadraticRaySectors_of_normRigidity (CurvatureBlowup.isGeodesic g o) (hB' o)
  intro E _ _ _ hE
  let Q := Book.blowupSpectralPrices CurvatureBlowup.ultrafilter CurvatureBlowup.scale_pos o P
  obtain ⟨R⟩ := hE.spectralPrices Q
  exact (hc E R).innerProductSpace
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
open scoped Classical
namespace ShiftedCrossing
open SiteTensor
variable {K E : Type*} [Field K] [MetricSpace E]
private abbrev wireX (K : Type*) [Field K] (q : ℕ) : Raw Site K :=
  (Raw.diagonal (Fin 2) K (Fin q)).group Sum.inl
private abbrev wireY (K : Type*) [Field K] (q : ℕ) : Raw Site K :=
  (Raw.diagonal (Fin 2) K (Fin q)).group Sum.inr
private def pairLegEquiv (dX dY : ℕ) : ∀ i : Site,
    Leg dX dY i ≃ ((wireX K dX).mul (wireY K dY)).Leg i
  | .inl j =>
    { toFun := fun x => (fun _ => x, fun h => nomatch h.property)
      invFun := fun w => w.1 ⟨j,rfl⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨a,b⟩
        apply Prod.ext
        · funext ⟨i,hi⟩
          cases Sum.inl.inj hi
          rfl
        · funext h
          exact nomatch h.property }
  | .inr j =>
    { toFun := fun x => ((fun h => nomatch h.property), fun _ => x)
      invFun := fun w => w.2 ⟨j,rfl⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨a,b⟩
        apply Prod.ext
        · funext h
          exact nomatch h.property
        · funext ⟨i,hi⟩
          cases Sum.inr.inj hi
          rfl }
private theorem wire_coeff {q : ℕ} (v : Fin 2 → Fin q) :
    (Raw.diagonal (Fin 2) K (Fin q)).coeff v = if v 0 = v 1 then 1 else 0 := by
  have h (a : Fin q) : v = (fun _ => a) ↔ v 0 = a ∧ v 1 = a := by
    constructor
    · rintro rfl; simp
    · intro he
      funext i
      fin_cases i <;> simp [he]
  simp only [Raw.diagonal, h, ite_and]
  simp [eq_comm]
private theorem target_product (dX dY : ℕ) : (target K dX dY).Equivalent
    ((wireX K dX).mul (wireY K dY)) := by
  apply Raw.reindex_equivalent (pairLegEquiv dX dY)
  intro a
  change (if a (.inl 0) = a (.inl 1) ∧ a (.inr 0) = a (.inr 1) then (1 : K) else 0) =
    (Raw.diagonal (Fin 2) K (Fin dX)).coeff (fun j => a (.inl j)) *
    (Raw.diagonal (Fin 2) K (Fin dY)).coeff (fun j => a (.inr j))
  erw [wire_coeff (K := K) (fun j => a (.inl j)), wire_coeff (K := K) (fun j => a (.inr j))]
  have h (v : Fin 2 → Fin dX) (w : Fin 2 → Fin dY) :
      (if v 0 = v 1 ∧ w 0 = w 1 then (1 : K) else 0) =
      (if v 0 = v 1 then 1 else 0) * (if w 0 = w 1 then 1 else 0) := by
    split_ifs <;> simp_all
  convert! h (fun j => a (.inl j)) (fun j => a (.inr j))
private theorem wire_ne_zero {q : ℕ} (hq : 0 < q) :
    (Raw.diagonal (Fin 2) K (Fin q)).coeff ≠ 0 := by
  intro h
  have hh := congrFun h (fun _ => (⟨0,hq⟩ : Fin q))
  rw [wire_coeff, ite_eq_left rfl] at hh
  exact one_ne_zero hh
theorem target_price (P : SpectralPlacementPrices K E) (p : Site → E)
    {dX dY : ℕ} (hX : 0 < dX) (hY : 0 < dY) :
    P.price (target K dX dY) p =
      dist (p (.inl 0)) (p (.inl 1)) * Real.logb 2 dX +
      dist (p (.inr 0)) (p (.inr 1)) * Real.logb 2 dY := by
  have eqv := target_product (K := K) dX dY
  rw [le_antisymm (P.placed_mono p eqv.1) (P.placed_mono p eqv.2), P.placed_product p
    ((Raw.group_ne_zero_iff _ _).mpr (wire_ne_zero hX))
    ((Raw.group_ne_zero_iff _ _).mpr (wire_ne_zero hY))]
  rw [← P.group, ← P.group, P.placed_diagonal_pair, P.placed_diagonal_pair]
  rfl
end ShiftedCrossing
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace ShiftedCrossing
open SiteTensor
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Field K]
private def ends (v : E) : Fin 2 → E := ![v,-v]
private def terminals (x y : E) : Site → E := Sum.elim (ends x) (ends y)
private theorem dist_opposite (v : E) : dist v (-v) = 2 * ‖v‖ := by
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ v, norm_smul]
  norm_num
private theorem cost_of_term {dx dy r : ℕ} (P : SpectralPlacementPrices K E)
    (x y z : E) (b : Bool) (W : Fin 2 → Fin dx → Fin dy → Fin r → K) :
    P.price (term b W) (terminals x y) ≤
      2 * (Real.logb 2 dx * ‖x-z‖ + Real.logb 2 dy * ‖(if b then -y else y)-z‖ +
        ‖z‖ * Real.logb 2 r) := by
  let T := term b W
  have hr := P.placed_mono (ends z) (term_group_restricts b W)
  rw [P.placed_diagonal_pair] at hr
  have ht := P.transport T (terminals x y) (ends z ∘ cut b)
  rw [Real.dist_eq, P.group] at ht
  have hu := (abs_le.mp ht).2
  have hd : dist (ends z 0) (ends z 1) = 2 * ‖z‖ := dist_opposite z
  rw [hd] at hr
  have hsum : (∑ i : Site, dist (terminals x y i) ((ends z ∘ cut b) i) *
      Real.logb 2 (Fintype.card (T.Leg i))) =
      2 * (Real.logb 2 dx * ‖x-z‖ + Real.logb 2 dy * ‖(if b then -y else y)-z‖) := by
    have cardX (j : Fin 2) : Fintype.card (T.Leg (.inl j)) = dx := Fintype.card_fin dx
    have cardY (j : Fin 2) : Fintype.card (T.Leg (.inr j)) = dy := Fintype.card_fin dy
    have hd (v w : E) : dist v (-w) = dist (-v) w := by rw [← dist_neg_neg v (-w), neg_neg]
    cases b <;> simp [Fintype.sum_sum_type, Fin.sum_univ_two, terminals, cut, partner, ends,
      cardX, cardY, ← dist_eq_norm, hd y z] <;> ring
  rw [hsum] at hu
  dsimp only [T] at hu
  linarith
theorem exists_finite_placement_bound (P : SpectralPlacementPrices K E) (x y p m : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ C : ℝ, ∀ {dx dy rp rm : ℕ}, 0 < dx → 0 < dy → Factorization K dx dy rp rm →
    2 * (Real.logb 2 dx + Real.logb 2 dy) ≤
      max (2 * (Real.logb 2 dx * ‖x-p‖ + Real.logb 2 dy * ‖y-p‖ + ‖p‖ * Real.logb 2 rp))
        (2 * (Real.logb 2 dx * ‖x-m‖ + Real.logb 2 dy * ‖-y-m‖ + ‖m‖ * Real.logb 2 rm)) + C := by
  obtain ⟨C, hC⟩ := P.exists_binary_sum_overhead (terminals x y)
  refine ⟨C, ?_⟩
  intro dx dy rp rm hdx hdy F
  let U : (∀ i, Leg dx dy i) → K := (term false F.plus).coeff
  let V : (∀ i, Leg dx dy i) → K := (term true F.minus).coeff
  have hid : (target K dx dy).coeff = U + V := funext F.identity
  have hs := hC U V (hid ▸ target_ne_zero hdx hdy)
  have heq : (⟨Leg dx dy, inferInstance, U + V⟩ :
      Raw Site K) = target K dx dy := by
    exact congrArg (fun f => (⟨Leg dx dy, inferInstance, f⟩ : Raw Site K)) hid.symm
  rw [heq, target_price P _ hdx hdy] at hs
  change dist x (-x) * _ + dist y (-y) * _ ≤
    max (P.price (term false F.plus) _) (P.price (term true F.minus) _) + C at hs
  rw [dist_opposite, dist_opposite, hx, hy, mul_one, ← mul_add] at hs
  exact hs.trans <| add_le_add_left (max_le_max (cost_of_term P x y p false F.plus)
    (cost_of_term P x y m true F.minus)) C
end ShiftedCrossing
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace ShiftedCrossing
open Real Filter
open scoped Topology
theorem AsymptoticFactorizations.shiftedCrossingCost {K E : Type*} [Field K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : AsymptoticFactorizations K) (P : SpectralPlacementPrices K E) :
    ShiftedCrossingCost E := by
  intro x y hx hy t u δ ht hu hlo hhi p m
  obtain ⟨dx, dy, rp, rm, bp, bm, hfac, hdx, hdy, hr, hbp, hbm⟩ :=
    h t u δ ht hu hlo hhi
  obtain ⟨C, finite⟩ := exists_finite_placement_bound P x y p m hx hy
  apply cost_limit (C := C) (Rp := fun n => Real.logb 2 (rp n))
    (Rm := fun n => Real.logb 2 (rm n)) (norm_nonneg p) (norm_nonneg m) hdx hdy hbp hbm hr
  filter_upwards [hfac] with n hn
  obtain ⟨hx, hy, ⟨F⟩⟩ := hn
  exact finite hx hy F
end ShiftedCrossing
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace SpectralPlacementPrices
open SiteTensor
variable {K X : Type*} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)
include P in
theorem sectorBusemann_of_rawWireDistance
    (h : ∀ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 6) K → _ → Prop))
      (c : ℝ), 0 ≤ c → ∀ a b a' b' z w : Fin 6, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      let d := rawWireDistance φ c
      d a z = u * d a b → d z b = (1-u) * d a b →
      d a' w = u * d a' b' → d w b' = (1-u) * d a' b' →
      d z w ≤ (1-u) * d a a' + u * d b b') : SectorBusemann X := by
  intro a b a' b' z w u hu hz hw
  let p : Fin 6 → X := ![a,b,a',b',z,w]
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have wire (i j : Fin 6) : P.price W (p ∘ ![i,j]) = dist (p i) (p j) := P.wire _
  rcases P.zero_or_common_group_price p with hzero | ⟨φ, c, hc, hp⟩
  · have hd (i j : Fin 6) : dist (p i) (p j) = 0 := (wire i j).symm.trans (hzero W ![i,j])
    change dist (p 4) (p 5) ≤ (1-u) * dist (p 0) (p 2) + u * dist (p 1) (p 3)
    simp only [hd, mul_zero, add_zero, le_refl]
  · have hd (i j : Fin 6) : rawWireDistance φ c i j = dist (p i) (p j) :=
      (hp W ![i,j]).symm.trans (wire i j)
    have hh := h φ c hc.le 0 1 2 3 4 5 u hu
    simp only [hd] at hh
    exact hh hz.1 hz.2 hw.1 hw.2
end SpectralPlacementPrices
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open HyperbolicObstruction
variable {K X : Type*} [Field K] [MetricSpace X]
theorem SpectralPlacementPrices.catZero_of_asymptoticFactorizations
    (P : SpectralPlacementPrices K X) (g : IsGeodesic X)
    (hc : ShiftedCrossing.AsymptoticFactorizations K)
    (hsync : ∀ (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} (Fin 6) K → _ → Prop))
      (c : ℝ), 0 ≤ c → ∀ a b a' b' z w : Fin 6, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      let d := SiteTensor.rawWireDistance φ c
      d a z = u * d a b → d z b = (1-u) * d a b →
      d a' w = u * d a' b' → d w b' = (1-u) * d a' b' →
      d z w ≤ (1-u) * d a a' + u * d b b') : CATZero X := by
  apply P.catZero_of_shiftedCost g (P.sectorBusemann_of_rawWireDistance hsync) _
    (fun _ _ _ _ Q ↦ hc.shiftedCrossingCost Q)
  exact fun o ↦ (Book.blowupSpectralPrices CurvatureBlowup.ultrafilter CurvatureBlowup.scale_pos o
    P).sectorBusemann_of_rawWireDistance hsync
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset
theorem wedgeSign_insert (i : ℕ) {s : State} {j : ℕ} (hj : j ∉ s) :
    wedgeSign i (insert j s) = (if j < i then -1 else 1) * wedgeSign i s := by
  by_cases hji : j < i
  · simp [wedgeSign, filter_insert, hji, Finset.notMem_mono (filter_subset _ _) hj, pow_succ]
  · simp [wedgeSign, filter_insert, hji]
theorem wedgeSign_erase (i : ℕ) {s : State} {j : ℕ} (hj : j ∈ s) :
    wedgeSign i (s.erase j) = (if j < i then -1 else 1) * wedgeSign i s := by
  have h := wedgeSign_insert i (s := s.erase j) (j := j) (notMem_erase _ _)
  rw [insert_erase hj] at h
  rw [h]
  split <;> simp
theorem wedgeSign_mul_self (i : ℕ) (s : State) : wedgeSign i s * wedgeSign i s = 1 := by
  simp [wedgeSign, ← mul_pow]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open scoped BigOperators
variable {α k E : Type*} [CommRing k] [Ring E] [Algebra k E]
def normal (k : Type*) [CommRing k] [Algebra k E] (C A : α → E) : List α → E
  | [] => 1
  | f :: r => C f * normal k C A r + (-1 : k) ^ r.length • (normal k C A r * A f)
private def contractions (C A : α → E) (κ : α → α → k) (x : α) (r : List α) : E :=
  ∑ j : Fin r.length, ((-1 : k) ^ j.val * κ x r[j.val]) • normal k C A (r.eraseIdx j.val)
private theorem contractions_cons (C A : α → E) (κ : α → α → k) (x f : α) (r : List α) :
    contractions C A κ x (f :: r) = κ x f • normal k C A r -
      C f * contractions C A κ x r +
      (-1 : k) ^ r.length • (contractions C A κ x r * A f) := by
  classical
  unfold contractions
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero, List.eraseIdx_zero,
    Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ, normal, Finset.mul_sum,
    Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib, sub_eq_add_neg, add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hlen : (r.eraseIdx j.val).length + 1 = r.length := by
    have hj := j.isLt
    rw [List.length_eraseIdx_of_lt j.isLt]
    omega
  have hsign : (-1 : k) ^ r.length = -((-1 : k) ^ (r.eraseIdx j.val).length) := by
    conv_lhs => rw [← hlen, pow_succ]
    simp
  simp [hsign, pow_succ, smul_add, smul_smul, mul_comm,
    mul_left_comm]
theorem ann_mul_normal (C A : α → E) (κ : α → α → k)
    (hac : ∀ x y, A x * C y + C y * A x = algebraMap k E (κ x y))
    (haa : ∀ x y, A x * A y + A y * A x = 0) (x : α) (r : List α) :
    A x * normal k C A r = (-1 : k) ^ r.length • (normal k C A r * A x) +
      ∑ j : Fin r.length, ((-1 : k) ^ j.val * κ x r[j.val]) • normal k C A (r.eraseIdx j.val) := by
  change _ = _ + contractions C A κ x r
  induction r with
  | nil => simp [normal, contractions]
  | cons f r ih =>
    have hc := eq_sub_of_add_eq (hac x f)
    have ha := eq_neg_of_add_eq_zero_left (haa x f)
    rw [contractions_cons, normal, List.length_cons, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, mul_add, mul_smul_comm, ← mul_assoc (A x), hc,
      sub_mul, mul_assoc (C f), ih, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      add_mul, smul_add, mul_assoc, ha, mul_neg, smul_neg]
    abel
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open scoped BigOperators
variable {α : Type*}
def Matching : List α → List α → Type
  | [], _ => Unit
  | _ :: l, r => Matching l r ⊕ Σ j : Fin r.length, Matching l (r.eraseIdx j.val)
instance matchingFintype : (l r : List α) → Fintype (Matching l r)
  | [], _ => inferInstanceAs (Fintype Unit)
  | _ :: l, r => by
    letI := matchingFintype l r
    letI (j : Fin r.length) := matchingFintype l (r.eraseIdx j.val)
    exact inferInstanceAs (Fintype (_ ⊕ Σ _ : Fin r.length, _))
namespace Matching
def residual : {l r : List α} → Matching l r → List α
  | [], r, _ => r
  | x :: _, _, .inl m => x :: residual m
  | _ :: _, _, .inr ⟨_, m⟩ => residual m
def weight {k : Type*} [CommRing k] (κ : α → α → k) :
    {l r : List α} → Matching l r → k
  | [], _, _ => 1
  | _ :: _, _, .inl m => weight κ m
  | x :: l, r, .inr ⟨j, m⟩ =>
    ((-1 : k) ^ l.length * ((-1 : k) ^ j.val * κ x r[j.val])) * weight κ m
theorem residual_sign {k : Type*} [CommRing k] (l r : List α) (p : Matching l r) :
    (-1 : k) ^ (residual p).length = (-1 : k) ^ l.length * (-1 : k) ^ r.length := by
  induction l generalizing r with
  | nil => simp [residual]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simpa [residual, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        congrArg (fun v : k ↦ v * (-1)) (ih r p)
    · rw [residual, ih]
      have h := j.isLt
      have hlen : (r.eraseIdx j.val).length + 1 = r.length := by
        rw [List.length_eraseIdx_of_lt h]
        omega
      rw [List.length_cons, ← congrArg (fun n : ℕ ↦ (-1 : k) ^ n) hlen, pow_succ, pow_succ]
      ring
end Matching
variable {k E : Type*} [CommRing k] [Ring E] [Algebra k E]
def wickSum (κ : α → α → k) (H : List α → E) (l r : List α) : E :=
  ∑ p : Matching l r, p.weight κ • H p.residual
private theorem wickSum_cons (κ : α → α → k) (H : List α → E) (x : α) (l r : List α) :
    wickSum κ H (x :: l) r = wickSum κ (fun w ↦ H (x :: w)) l r +
      ∑ j : Fin r.length, ((-1 : k) ^ l.length * ((-1 : k) ^ j.val * κ x r[j.val])) •
        wickSum κ H l (r.eraseIdx j.val) := by
  unfold wickSum
  change (∑ p : Matching l r ⊕ (Σ j : Fin r.length, Matching l (r.eraseIdx j.val)), _) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Matching.residual, Matching.weight, Finset.smul_sum, smul_smul]
variable (C A : α → E) (κ : α → α → k)
private theorem wickSum_normal_cons (x : α) (l r : List α) :
    wickSum κ (fun w ↦ normal k C A (x :: w)) l r =
      C x * wickSum κ (normal k C A) l r + ((-1 : k)^l.length * (-1 : k)^r.length) •
        (wickSum κ (normal k C A) l r * A x) := by
  simp only [wickSum, normal, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [Matching.residual_sign, smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul,
    mul_comm (m.weight κ) _]
theorem normal_mul_normal
    (hac : ∀ x y, A x * C y + C y * A x = algebraMap k E (κ x y))
    (haa : ∀ x y, A x * A y + A y * A x = 0) (l r : List α) :
    normal k C A l * normal k C A r =
      ∑ p : Matching l r, p.weight κ • normal k C A p.residual := by
  change _ = wickSum κ (normal k C A) l r
  induction l generalizing r with
  | nil =>
    change (1 : E) * normal k C A r = ∑ _ : Unit, (1 : k) • normal k C A r
    simp
  | cons x l ih =>
    rw [normal, wickSum_cons, wickSum_normal_cons, ← ih]
    simp_rw [← ih]
    rw [add_mul, smul_mul_assoc, mul_assoc, mul_assoc, ann_mul_normal C A κ hac haa, mul_add,
      smul_add, Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul, mul_assoc, add_assoc]
    simp only [mul_smul_comm, smul_smul]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset
variable {k E ι : Type*} [CommRing k] [Ring E] [Algebra k E] [Fintype ι]
private theorem weighted_anticommutator (a c : ι → E) (v w : ι → k) :
    (∑ i, v i • a i) * (∑ j, w j • c j) + (∑ j, w j • c j) * (∑ i, v i • a i) =
      ∑ i, ∑ j, (v i * w j) • (a i * c j + c j * a i) := by
  simp only [sum_mul, mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul, smul_add]
  rw [Finset.sum_comm (f := fun j i ↦ (w j * v i) • (a i * c j)),
    ← Finset.sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by simp [Finset.sum_add_distrib, mul_comm]
theorem weighted_same_modes (a : ι → E) (h : ∀ i j, a i * a j + a j * a i = 0)
    (v w : ι → k) :
    (∑ i, v i • a i) * (∑ j, w j • a j) + (∑ j, w j • a j) * (∑ i, v i • a i) = 0 := by
  rw [weighted_anticommutator]
  simp [h]
theorem weighted_mixed_modes [DecidableEq ι] (a c : ι → E)
    (h : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (v w : ι → k) :
    (∑ i, v i • a i) * (∑ j, w j • c j) + (∑ j, w j • c j) * (∑ i, v i • a i) =
      algebraMap k E (∑ i, v i * w i) := by
  rw [weighted_anticommutator]
  simp [h, smul_ite, Algebra.algebraMap_eq_smul_one]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset
open scoped BigOperators
noncomputable def truncatedRhs (i j α β : State) (s : ℤ) (N : ℕ) : ℤ :=
  let L := order (weight i) (weight j)
  ∑ a ∈ range (L+1), multiplier L a *
    ((∑ k ∈ (range N).powerset, blockMode i (-s-1-L+a) α k * blockMode j (s-a) k β) -
      (-1)^(i.card*j.card) * ∑ k ∈ (range N).powerset,
        blockMode j (s-a) α k * blockMode i (-s-1-L+a) k β)
theorem two_mul_order_add {i j : State} (hi : i.Nonempty) (hij : i.card = j.card) :
    2 * (order (weight i) (weight j) : ℤ) + 2 = (weight i : ℤ) + weight j := by
  have hw (S : State) : weight S = 2 * ∑ k ∈ S, k + S.card := by
    simp [weight, sum_add_distrib, mul_sum]
  have hp := card_pos.mpr hi
  simp only [order, hw]
  omega
theorem truncatedRhs_eq_zero_of_weight_ne {i j α β : State}
    (hi : i.Nonempty) (hij : i.card = j.card) (hαβ : weight α ≠ weight β)
    (s : ℤ) (N : ℕ) : truncatedRhs i j α β s N = 0 := by
  let L := order (weight i) (weight j)
  have hL : 2 * (L : ℤ) + 2 = (weight i : ℤ) + weight j := two_mul_order_add hi hij
  have hz {I J : State} {b c : ℤ} (h : (weight I : ℤ) + weight J + 2*(b+c) = 0) :
      ∑ k ∈ (range N).powerset, blockMode I b α k * blockMode J c k β = 0 := by
    apply sum_eq_zero
    intro k _
    by_contra hne
    obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hne
    have hα := weight_eq_of_blockMode_ne_zero h₁
    have hβ := weight_eq_of_blockMode_ne_zero h₂
    omega
  unfold truncatedRhs
  dsimp only
  apply sum_eq_zero
  intro a _
  change multiplier L a * _ = 0
  rw [hz (I := i) (J := j) (b := -s-1-L+a) (c := s-a) (by omega),
      hz (I := j) (J := i) (b := s-a) (c := -s-1-L+a) (by omega)]
  simp
end Fermion
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
def FockState.erase {N : ℕ} (S : FockState N) (r : ℕ) : FockState N :=
  ⟨S.val.erase r, mem_powerset.mpr ((erase_subset _ _).trans (mem_powerset.mp S.property))⟩
def FockState.insert {N : ℕ} (S : FockState N) (r : Fin N) : FockState N :=
  ⟨Insert.insert r.val S.val, mem_powerset.mpr <|
    insert_subset (mem_range.mpr r.isLt) (mem_powerset.mp S.property)⟩
variable (K : Type*) [CommRing K] {N : ℕ}
def creation (r : Fin N) : Matrix (FockState N) (FockState N) K := Matrix.of fun α β ↦
  if r.val ∈ α.val then if α.erase r = β then (wedgeSign r α.val : K) else 0 else 0
def annihilation (r : Fin N) : Matrix (FockState N) (FockState N) K := (creation K r).transpose
theorem creation_apply (r : Fin N) (α β : FockState N) :
    creation K r α β =
      if r.val ∈ α.val then if α.erase r = β then (wedgeSign r α.val : K) else 0 else 0 := rfl
theorem annihilation_apply (r : Fin N) (α β : FockState N) :
    annihilation K r α β =
      if r.val ∈ α.val then 0 else if α.insert r = β then (wedgeSign r α.val : K) else 0 := by
  change creation K r β α = _
  rw [creation_apply]
  by_cases hβ : r.val ∈ β.val
  · by_cases h : β.erase r = α
    · subst α
      have he : (β.erase r).insert r = β := Subtype.ext (insert_erase hβ)
      simp [hβ, he, show (β.erase r).val = β.val.erase r.val from rfl, wedgeSign_erase _ hβ]
    · by_cases ha : r.val ∈ α.val
      · simp [hβ, h, ha]
      · have hi : α.insert r ≠ β := by
          intro he
          apply h
          apply Subtype.ext
          have he' := congrArg Subtype.val he
          change insert r.val α.val = β.val at he'
          change β.val.erase r.val = α.val
          rw [← he', erase_insert ha]
        simp [hβ, h, ha, hi]
  · have hi : α.insert r ≠ β := by
      intro he
      apply hβ
      rw [← he]
      exact mem_insert_self _ _
    simp [hβ, hi]
theorem creation_mul_apply (r : Fin N) (B : Matrix (FockState N) (FockState N) K)
    (α β : FockState N) :
    (creation K r * B) α β =
      if r.val ∈ α.val then (wedgeSign r α.val : K) * B (α.erase r) β else 0 := by
  classical
  by_cases h : r.val ∈ α.val <;> simp [Matrix.mul_apply, creation_apply, h, ite_mul]
theorem mul_annihilation_apply (r : Fin N) (B : Matrix (FockState N) (FockState N) K)
    (α β : FockState N) :
    (B * annihilation K r) α β =
      if r.val ∈ β.val then B α (β.erase r) * (wedgeSign r β.val : K) else 0 := by
  classical
  by_cases h : r.val ∈ β.val <;>
    simp [Matrix.mul_apply, annihilation, creation_apply, h, mul_ite]
theorem annihilation_mul_apply (r : Fin N) (B : Matrix (FockState N) (FockState N) K)
    (α β : FockState N) :
    (annihilation K r * B) α β =
      if r.val ∈ α.val then 0 else (wedgeSign r α.val : K) * B (α.insert r) β := by
  classical
  by_cases h : r.val ∈ α.val <;> simp [Matrix.mul_apply, annihilation_apply, h, ite_mul]
theorem creation_mul_creation (i j : Fin N) :
    creation K i * creation K j + creation K j * creation K i = 0 := by
  ext α β
  change (creation K i * creation K j) α β + (creation K j * creation K i) α β = 0
  simp only [creation_mul_apply, creation_apply]
  have herase (r s : ℕ) : (α.erase r).erase s = (α.erase s).erase r :=
    Subtype.ext erase_right_comm
  have hval (r : ℕ) : (α.erase r).val = α.val.erase r := rfl
  by_cases hij : i.val = j.val
  · have h : i = j := Fin.ext hij
    subst j
    simp [hval]
  · have hji := Ne.symm hij
    by_cases hi : i.val ∈ α.val <;> by_cases hj : j.val ∈ α.val <;>
      simp [hi, hj, hval, hij, hji, herase i j]
    split
    · rw [wedgeSign_erase _ hi, wedgeSign_erase _ hj]
      rcases lt_or_gt_of_ne hij with h | h <;> simp [h, not_lt.mpr h.le] <;> ring
    · simp
theorem annihilation_mul_annihilation (i j : Fin N) :
    annihilation K i * annihilation K j + annihilation K j * annihilation K i = 0 := by
  simpa only [annihilation, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_zero]
    using congrArg Matrix.transpose (creation_mul_creation K j i)
theorem annihilation_mul_creation (r s : Fin N) :
    annihilation K r * creation K s + creation K s * annihilation K r =
      if r = s then 1 else 0 := by
  classical
  ext α β
  rw [Matrix.add_apply, annihilation_mul_apply, creation_mul_apply]
  by_cases hrs : r = s
  · subst s
    rw [ite_eq_left (rfl : r = r), Matrix.one_apply]
    have hsq : (wedgeSign r α.val : K) * (wedgeSign r α.val : K) = 1 := by
      rw [← Int.cast_mul, wedgeSign_mul_self, Int.cast_one]
    by_cases h : r.val ∈ α.val
    · have he : (α.erase r).insert r = α := Subtype.ext (insert_erase h)
      simp [h, annihilation_apply, show (α.erase r).val = α.val.erase r.val from rfl,
        he, wedgeSign_erase _ h, mul_ite, hsq]
    · have he : (α.insert r).erase r = α := Subtype.ext (erase_insert h)
      simp [h, creation_apply, show (α.insert r).val = insert r.val α.val from rfl,
        he, wedgeSign_insert _ h, mul_ite, hsq]
  · have hn : r.val ≠ s.val := fun h ↦ hrs (Fin.ext h)
    have hins : (α.insert r).val = insert r.val α.val := rfl
    have hera : (α.erase s).val = α.val.erase s.val := rfl
    have hcomm : (α.insert r).erase s = (α.erase s).insert r := Subtype.ext (erase_insert_of_ne hn)
    rw [ite_eq_right hrs, Matrix.zero_apply]
    by_cases hr : r.val ∈ α.val <;> by_cases hs : s.val ∈ α.val <;>
      simp [hr, hs, creation_apply, annihilation_apply, hins, hera, hn, hn.symm, hcomm]
    by_cases hb : (α.erase s).insert r = β
    · rw [ite_eq_left hb, ite_eq_left hb, wedgeSign_insert _ hr, wedgeSign_erase _ hs]
      rcases lt_or_gt_of_ne hn with h | h
      · simp [h, not_lt_of_gt h, mul_comm]
      · simp [h, not_lt_of_gt h, mul_comm]
    · simp [hb]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open LaurentPolynomial
abbrev FieldLabel := Bool × ℕ
def fieldExponent (side : Bool) (d : ℤ) : ℤ := if side then d else 0
def creationCoeff (f : FieldLabel) (r : ℕ) : LaurentPolynomial ℤ :=
  C (r.choose f.2 : ℤ) * T (fieldExponent f.1 ((r : ℤ) - f.2))
def annihilationCoeff (f : FieldLabel) (r : ℕ) : LaurentPolynomial ℤ :=
  C (negativeChoose r f.2) * T (fieldExponent f.1 (-(r : ℤ) - 1 - f.2))
def mixedNormal : List FieldLabel → State → State → LaurentPolynomial ℤ
  | [], α, β => if α = β then 1 else 0
  | f :: l, α, β =>
    (∑ r ∈ α, creationCoeff f r * C (wedgeSign r α) * mixedNormal l (α.erase r) β) +
    (-1) ^ l.length * ∑ r ∈ β,
      annihilationCoeff f r * C (wedgeSign r β) * mixedNormal l α (β.erase r)
def modeDegree (l : List ℕ) (α β : State) : ℤ :=
  ((weight α : ℤ) - weight β - listWeight l) / 2
theorem modeDegree_of_listMode_ne_zero {l : List ℕ} {α β : State} {b : ℤ}
    (h : listMode l b α β ≠ 0) : modeDegree l α β = b := by
  unfold modeDegree
  have hw := weight_eq_of_listMode_ne_zero h
  omega
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
noncomputable def contractionPolynomial (N : ℕ) (f g : FieldLabel) : LaurentPolynomial ℤ :=
  ∑ r : Fin N, annihilationCoeff f r.val * creationCoeff g r.val
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
def creationField (N : ℕ) (f : FieldLabel) :
    Matrix (FockState N) (FockState N) (LaurentPolynomial ℤ) :=
  ∑ r : Fin N, creationCoeff f r.val • creation (LaurentPolynomial ℤ) r
def annihilationField (N : ℕ) (f : FieldLabel) :
    Matrix (FockState N) (FockState N) (LaurentPolynomial ℤ) :=
  ∑ r : Fin N, annihilationCoeff f r.val • annihilation (LaurentPolynomial ℤ) r
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open LaurentPolynomial
private theorem weight_erase_cast {α : State} {r : ℕ} (hr : r ∈ α) :
    (weight (α.erase r) : ℤ) + (2 * r + 1) = weight α := by
  exact_mod_cast (Finset.sum_erase_add α (fun i : ℕ ↦ 2*i+1) hr)
private theorem modeDegree_create (l : List ℕ) (j : ℕ) (α β : State) {r : ℕ} (hr : r ∈ α) :
    modeDegree l (α.erase r) β = modeDegree (j :: l) α β - r + j := by
  unfold modeDegree
  rw [show listWeight (j :: l) = 2*j+1 + listWeight l from rfl]
  push_cast
  have hw := weight_erase_cast hr
  omega
private theorem modeDegree_annihilate (l : List ℕ) (j : ℕ) (α β : State) {r : ℕ} (hr : r ∈ β) :
    modeDegree l α (β.erase r) = modeDegree (j :: l) α β + r + 1 + j := by
  unfold modeDegree
  rw [show listWeight (j :: l) = 2*j+1 + listWeight l from rfl]
  push_cast
  have hw := weight_erase_cast hr
  omega
private theorem combine_modes (x s y d e : ℤ) :
    (C x * T d : LaurentPolynomial ℤ) * C s * (C y * T e) = C (x*s*y) * T (d+e) := by
  rw [T_add, map_mul, map_mul]
  ring
theorem mixedNormal_one_variable (side : Bool) (l : List ℕ) (α β : State) :
    mixedNormal (l.map (Prod.mk side)) α β =
      C (listMode l (modeDegree l α β) α β) * T (fieldExponent side (modeDegree l α β)) := by
  induction l generalizing α β with
  | nil =>
    by_cases he : α = β
    · subst β
      simp [modeDegree, listWeight, fieldExponent, mixedNormal, listMode]
    · simp [mixedNormal, listMode, he]
  | cons j l ih =>
    rw [List.map_cons, mixedNormal, listMode, map_add, add_mul]
    simp only [List.length_map, map_mul, map_pow, map_neg, map_one, map_sum, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun r hr ↦ ?_
      rw [ih, creationCoeff, combine_modes, modeDegree_create l j α β hr]
      rw [← map_mul, ← map_mul]
      congr 2
      cases side <;> simp [fieldExponent]
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      rw [ih, annihilationCoeff, combine_modes, modeDegree_annihilate l j α β hr]
      rw [← map_mul, ← map_mul]
      congr 2
      cases side <;> simp [fieldExponent]
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open Finset LaurentPolynomial
private theorem sum_fock_modes {N : ℕ} (S : FockState N) (g : ℕ → LaurentPolynomial ℤ) :
    (∑ r : Fin N, if r.val ∈ S.val then g r.val else 0) = ∑ r ∈ S.val, g r := by
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ ↦ if r ∈ S.val then g r else 0), ← Finset.sum_filter]
  congr 1
  exact Finset.filter_mem_eq_inter.trans (inter_eq_right.mpr (mem_powerset.mp S.property))
theorem normal_matrix_apply (N : ℕ) (l : List FieldLabel) (α β : FockState N) :
    normal (LaurentPolynomial ℤ)
      (creationField N) (annihilationField N)
      l α β = mixedNormal l α.val β.val := by
  change normal (LaurentPolynomial ℤ)
    (fun f ↦ ∑ r : Fin N, creationCoeff f r • creation (LaurentPolynomial ℤ) r)
    (fun f ↦ ∑ r : Fin N, annihilationCoeff f r • annihilation (LaurentPolynomial ℤ) r)
    l α β = _
  induction l generalizing α β with
  | nil => simp only [normal, mixedNormal, Matrix.one_apply, Subtype.ext_iff]
  | cons f l ih =>
    simp only [normal, mixedNormal, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm,
      Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      creation_mul_apply, mul_annihilation_apply, mul_ite, mul_zero, ih, FockState.erase]
    rw [← sum_fock_modes α, ← sum_fock_modes β]
    congr 1
    · apply sum_congr rfl
      intro r _
      simp [mul_assoc]
    · apply sum_congr rfl
      intro r _
      simp [mul_left_comm, mul_comm]
def fieldWord (side : Bool) (I : State) : List FieldLabel :=
  (I.sort (· ≤ ·)).map (Prod.mk side)
def fieldMatrix (N : ℕ) (side : Bool) (I : State) :
    Matrix (FockState N) (FockState N) (LaurentPolynomial ℤ) :=
  normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) (fieldWord side I)
theorem fieldMatrix_apply (N : ℕ) (side : Bool) (I : State) (α β : FockState N) :
    fieldMatrix N side I α β =
      C (blockMode I (modeDegree (I.sort (· ≤ ·)) α.val β.val) α.val β.val) *
        T (fieldExponent side (modeDegree (I.sort (· ≤ ·)) α.val β.val)) := by
  rw [fieldMatrix, normal_matrix_apply, fieldWord, mixedNormal_one_variable]
  rfl
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Filter LaurentPolynomial
def LaurentCrossingIdentity : Prop :=
  ∀ (i j a b : State), i.Nonempty → i.card = j.card → weight a = weight b → ∀ s : ℤ,
    ∀ᶠ N : ℕ in atTop, ∀ (α β : FockState N), α.val = a → β.val = b →
      (((1 - T 1) ^ order (weight i) (weight j)) *
        ((fieldMatrix N false i * fieldMatrix N true j) α β -
          (-1 : LaurentPolynomial ℤ)^(i.card*j.card) *
            ((fieldMatrix N true j * fieldMatrix N false i) α β))).coeff s =
        pairing i j * (if a = b then 1 else 0)
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open LaurentPolynomial
private lemma coeff_pair_p0 (f g : ℤ → ℤ) (d e B w : ℤ)
    (hf : ∀ b, f b ≠ 0 → d = b) (hg : ∀ b, g b ≠ 0 → e = b)
    (hs : f d ≠ 0 → g e ≠ 0 → d + e = B) :
    (C (f d) * (C (g e) * T e) : LaurentPolynomial ℤ).coeff w =
      f (B-w) * g w := by
  rw [← mul_assoc, ← map_mul, ← single_eq_C_mul_T]
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases he : e = w
  · subst w
    rw [ite_eq_left rfl]
    by_cases hg0 : g e = 0
    · simp [hg0]
    by_cases hd : d = B-e
    · rw [hd]
    have hfd : f d = 0 := by
      by_contra hn
      have := hs hn hg0
      omega
    have hfb : f (B-e) = 0 := by
      by_contra hn
      exact hd (hf _ hn)
    simp [hfd, hfb]
  · rw [ite_eq_right he]
    have hgw : g w = 0 := by
      by_contra hn
      exact he (hg _ hn)
    simp [hgw]
theorem coeff_field_pair {N : ℕ} (i j : State) (α β γ δ : FockState N) (L : ℕ) (w : ℤ)
    (hw : (weight α.val : ℤ) - weight β.val + (weight γ.val - weight δ.val) = 0)
    (hL : 2*(L : ℤ)+2 = (weight i : ℤ)+weight j) :
    (fieldMatrix N false i α β * fieldMatrix N true j γ δ).coeff w =
      blockMode i (-1-L-w) α.val β.val * blockMode j w γ.val δ.val := by
  rw [fieldMatrix_apply, fieldMatrix_apply]
  simp only [fieldExponent, Bool.false_eq_true, ↓reduceIte, T_zero, mul_one]
  let di := modeDegree (i.sort (· ≤ ·)) α.val β.val
  let dj := modeDegree (j.sort (· ≤ ·)) γ.val δ.val
  apply coeff_pair_p0 (fun b ↦ blockMode i b α.val β.val) (fun b ↦ blockMode j b γ.val δ.val)
    di dj (-1-L) w
  · exact fun _ hn ↦ modeDegree_of_listMode_ne_zero hn
  · exact fun _ hn ↦ modeDegree_of_listMode_ne_zero hn
  · intro h₁ h₂
    have h₃ := weight_eq_of_blockMode_ne_zero h₁
    have h₄ := weight_eq_of_blockMode_ne_zero h₂
    omega
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open PowerSeries
open scoped PowerSeries
def kernelNumerator (i j : ℕ) : ℤ := (-1)^i * ((i+j).choose i : ℤ)
def forwardKernel (k : ℕ) : ℤ → ℤ
  | .ofNat n => coeff n (invOneSubPow ℤ k).val
  | .negSucc _ => 0
def reverseKernel (k : ℕ) (s : ℤ) : ℤ := (-1)^k * forwardKernel k (-s-k)
theorem forwardKernel_succ_nat (k n : ℕ) :
    forwardKernel (k+1) n = ((k+n).choose k : ℤ) := by
  simp [forwardKernel, invOneSubPow_val_succ_eq_mk_add_choose]
theorem differentiated_kernel (r i j : ℕ) :
    negativeChoose r i * (r.choose j : ℤ) =
      kernelNumerator i j * forwardKernel (i+j+1) ((r : ℤ)-j) := by
  by_cases h : j ≤ r
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add, add_sub_cancel_left, forwardKernel_succ_nat]
    have hn := Nat.choose_mul (n := i+j+t) (k := i+j) (s := i) (by omega)
    have hsub : i+j+t-i = j+t := by omega
    rw [hsub, Nat.add_sub_cancel_left] at hn
    have hn' : ((j+t+i).choose i : ℤ) * (j+t).choose j =
        ((i+j).choose i : ℤ) * (i+j+t).choose (i+j) := by
      exact_mod_cast (by simpa [add_assoc, add_comm, add_left_comm, mul_comm] using hn.symm :
        (j+t+i).choose i * (j+t).choose j = (i+j).choose i * (i+j+t).choose (i+j))
    simpa only [negativeChoose, kernelNumerator, mul_assoc] using congrArg ((-1:ℤ)^i * ·) hn'
  · rw [Nat.choose_eq_zero_of_lt (by omega : r < j)]
    have he : (r : ℤ)-j = .negSucc (j-r-1) := by omega
    simp [he, forwardKernel]
def kernelDifference (f : ℤ → ℤ) (s : ℤ) := f s - f (s-1)
private theorem annihilate (k : ℕ) : (1 - (X : ℤ⟦X⟧)) * (invOneSubPow ℤ (k+1)).val =
    (invOneSubPow ℤ k).val := by
  simpa using one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℤ k 1
theorem difference_forwardKernel (k : ℕ) :
    kernelDifference (forwardKernel (k+1)) = forwardKernel k := by
  funext s
  cases s with
  | negSucc n =>
    have he : Int.negSucc n - 1 = .negSucc (n+1) := by omega
    simp [kernelDifference, forwardKernel, he]
  | ofNat n =>
    have h := congrArg (coeff n) (annihilate k)
    cases n with
    | zero =>
      change coeff 0 (invOneSubPow ℤ (k+1)).val - 0 = coeff 0 (invOneSubPow ℤ k).val
      simpa [sub_mul] using h
    | succ n =>
      unfold kernelDifference
      rw [show Int.ofNat (n+1) - 1 = Int.ofNat n by simp [Int.ofNat_eq_natCast]]
      change coeff (n+1) (invOneSubPow ℤ (k+1)).val - coeff n (invOneSubPow ℤ (k+1)).val =
        coeff (n+1) (invOneSubPow ℤ k).val
      simpa [sub_mul] using h
theorem difference_reverseKernel (k : ℕ) :
    kernelDifference (reverseKernel (k+1)) = reverseKernel k := by
  funext s
  have h := congrFun (difference_forwardKernel k) (-s-k)
  unfold kernelDifference at h
  simp only [kernelDifference, reverseKernel, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show -s - ((k : ℤ)+1) = -s-k-1 by ring,
    show -(s-1) - ((k : ℤ)+1) = -s-k by ring, ← h]
  ring
private theorem iterate_forwardKernel (n k : ℕ) :
    kernelDifference^[n] (forwardKernel (k+n)) = forwardKernel k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change kernelDifference^[n] (kernelDifference (forwardKernel ((k+n)+1))) = _
    rw [difference_forwardKernel, ih]
private theorem iterate_reverseKernel (n k : ℕ) :
    kernelDifference^[n] (reverseKernel (k+n)) = reverseKernel k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change kernelDifference^[n] (kernelDifference (reverseKernel ((k+n)+1))) = _
    rw [difference_reverseKernel, ih]
theorem kernel_zero_equal : forwardKernel 0 = reverseKernel 0 := by
  funext s
  unfold reverseKernel
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  rcases s with (_ | n) | n
  · rfl
  · rw [show -Int.ofNat (n+1) = Int.negSucc n by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]]
    simp [forwardKernel, invOneSubPow_zero]
  · rw [show -Int.negSucc n = Int.ofNat (n+1) by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]]
    simp [forwardKernel, invOneSubPow_zero]
theorem kernel_partial_cancellation (L k : ℕ) (h : k ≤ L) :
    kernelDifference^[L] (forwardKernel k) = kernelDifference^[L] (reverseKernel k) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm k n, Function.iterate_add_apply, Function.iterate_add_apply]
  rw [show kernelDifference^[k] (forwardKernel k) = forwardKernel 0 by
        simpa using iterate_forwardKernel k 0,
      show kernelDifference^[k] (reverseKernel k) = reverseKernel 0 by
        simpa using iterate_reverseKernel k 0, kernel_zero_equal]
theorem kernel_full_delta (L : ℕ) (s : ℤ) :
    (kernelDifference^[L] (forwardKernel (L+1))) s -
      (kernelDifference^[L] (reverseKernel (L+1))) s = 1 := by
  rw [add_comm L 1, iterate_forwardKernel, iterate_reverseKernel]
  rcases s with n | n
  · rw [reverseKernel, show -Int.ofNat n - (↑(1:ℕ) : ℤ) = Int.negSucc n by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega]
    simp [forwardKernel, invOneSubPow]
  · rw [reverseKernel, show -Int.negSucc n - (↑(1:ℕ) : ℤ) = Int.ofNat n by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]]
    simp [forwardKernel, invOneSubPow]
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open Filter LaurentPolynomial
def laurentAction (P : LaurentPolynomial ℤ) (f : ℤ → ℤ) (s : ℤ) : ℤ :=
  ∑ t ∈ P.coeff.support, f (s-t) * P.coeff t
theorem laurentAction_coeff (P Q : LaurentPolynomial ℤ) (s : ℤ) :
    (Q * P).coeff s = laurentAction P Q.coeff s := by
  simpa only [laurentAction, Finsupp.sum, sub_eq_add_neg] using
    AddMonoidAlgebra.coeff_mul_apply_right Q P s
theorem eventually_coeff_mul_residual (p : ℕ → LaurentPolynomial ℤ) (f : ℤ → ℤ)
    (h : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = f s)
    (P : LaurentPolynomial ℤ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, (p N * P).coeff s = laurentAction P f s := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ t ∈ P.coeff.support, (p N).coeff (s-t) = f (s-t) :=
    (eventually_all_finset _).mpr (fun t _ => h (s-t))
  filter_upwards [hall] with N hN
  rw [laurentAction_coeff]
  exact Finset.sum_congr rfl fun t ht => congrArg (· * P.coeff t) (hN t ht)
theorem coeff_clear_pow (Q : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ((1 - T 1)^L * Q).coeff s = (kernelDifference^[L] Q.coeff) s := by
  induction L generalizing s with
  | zero => simp
  | succ L ih =>
    rw [pow_succ', mul_assoc, sub_mul, one_mul, Function.iterate_succ_apply']
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    simp only [kernelDifference, T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, ← ih]
    rw [show -(1 : ℤ) + s = s - 1 by omega]
private theorem eventually_kernelDifference_iterate (p : ℕ → ℤ → ℤ) (f : ℤ → ℤ)
    (h : ∀ s, ∀ᶠ N : ℕ in atTop, p N s = f s) (L : ℕ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, (kernelDifference^[L] (p N)) s = (kernelDifference^[L] f) s := by
  induction L generalizing s with
  | zero => exact h s
  | succ L ih =>
    filter_upwards [ih s, ih (s-1)] with N h₁ h₂
    simp only [Function.iterate_succ_apply', kernelDifference, h₁, h₂]
theorem eventually_coeff_clear_residual (p : ℕ → LaurentPolynomial ℤ) (f : ℤ → ℤ)
    (h : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = f s)
    (P : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s =
      laurentAction P (kernelDifference^[L] f) s := by
  simp_rw [← mul_assoc]
  apply eventually_coeff_mul_residual
  intro t
  simp_rw [coeff_clear_pow]
  exact eventually_kernelDifference_iterate (fun N => (p N).coeff) f h L t
theorem laurentAction_kernel_partial_cancellation (P : LaurentPolynomial ℤ) (L k : ℕ)
    (h : k ≤ L) (s : ℤ) :
    laurentAction P (kernelDifference^[L] (forwardKernel k)) s =
      laurentAction P (kernelDifference^[L] (reverseKernel k)) s := by
  rw [kernel_partial_cancellation L k h]
theorem laurentAction_kernel_full_delta (P : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    laurentAction P (kernelDifference^[L] (forwardKernel (L+1))) s -
      laurentAction P (kernelDifference^[L] (reverseKernel (L+1))) s =
      ∑ t ∈ P.coeff.support, P.coeff t := by
  unfold laurentAction
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [← sub_mul, kernel_full_delta, one_mul]
theorem iterate_kernelDifference_const_mul (a : ℤ) (f : ℤ → ℤ) (L : ℕ) :
    kernelDifference^[L] (fun s => a * f s) = fun s => a * (kernelDifference^[L] f) s := by
  induction L with
  | zero => rfl
  | succ L ih =>
    funext s
    simp only [Function.iterate_succ_apply', ih, kernelDifference, mul_sub]
theorem laurentAction_const_mul (P : LaurentPolynomial ℤ) (a : ℤ) (f : ℤ → ℤ) (s : ℤ) :
    laurentAction P (fun t => a * f t) s = a * laurentAction P f s := by
  simp only [laurentAction, Finset.mul_sum, mul_assoc]
theorem eventually_coeff_clear_residual_const_mul (p : ℕ → LaurentPolynomial ℤ)
    (a : ℤ) (f : ℤ → ℤ) (h : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = a * f s)
    (P : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s =
      a * laurentAction P (kernelDifference^[L] f) s := by
  simpa only [iterate_kernelDifference_const_mul, laurentAction_const_mul] using
    eventually_coeff_clear_residual p _ h P L s
theorem eventually_coeff_clear_partial (p q : ℕ → LaurentPolynomial ℤ) (a : ℤ)
    (k L : ℕ) (hk : k ≤ L)
    (hp : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = a * forwardKernel k s)
    (hq : ∀ s, ∀ᶠ N : ℕ in atTop, (q N).coeff s = a * reverseKernel k s)
    (P : LaurentPolynomial ℤ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s -
      ((1 - T 1)^L * (q N * P)).coeff s = 0 := by
  filter_upwards [eventually_coeff_clear_residual_const_mul p a _ hp P L s,
    eventually_coeff_clear_residual_const_mul q a _ hq P L s] with N h₁ h₂
  rw [h₁, h₂, laurentAction_kernel_partial_cancellation P L k hk, sub_self]
theorem eventually_coeff_clear_full (p q : ℕ → LaurentPolynomial ℤ) (a : ℤ) (L : ℕ)
    (hp : ∀ s, ∀ᶠ N : ℕ in atTop, (p N).coeff s = a * forwardKernel (L+1) s)
    (hq : ∀ s, ∀ᶠ N : ℕ in atTop, (q N).coeff s = a * reverseKernel (L+1) s)
    (P : LaurentPolynomial ℤ) (s : ℤ) :
    ∀ᶠ N : ℕ in atTop, ((1 - T 1)^L * (p N * P)).coeff s -
      ((1 - T 1)^L * (q N * P)).coeff s = a * ∑ t ∈ P.coeff.support, P.coeff t := by
  filter_upwards [eventually_coeff_clear_residual_const_mul p a _ hp P L s,
    eventually_coeff_clear_residual_const_mul q a _ hq P L s] with N h₁ h₂
  rw [h₁, h₂, ← mul_sub, laurentAction_kernel_full_delta]
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Finset LaurentPolynomial
private theorem multiplier_succ_succ (L a : ℕ) :
    multiplier (L+1) (a+1) = multiplier L (a+1) - multiplier L a := by
  simp only [multiplier, pow_succ, Nat.choose_succ_succ, Nat.cast_add]
  ring
theorem iterate_kernelDifference_eq_sum (f : ℤ → ℤ) (L : ℕ) (s : ℤ) :
    (kernelDifference^[L] f) s = ∑ a ∈ range (L+1), multiplier L a * f (s-a) := by
  induction L generalizing s with
  | zero => simp [multiplier]
  | succ L ih =>
    rw [Function.iterate_succ_apply', kernelDifference, ih, ih, sum_range_succ' (n := L+1)]
    simp_rw [multiplier_succ_succ, sub_mul]
    rw [sum_sub_distrib]
    have hsum : (∑ a ∈ range (L+1), multiplier L (a+1) * f (s-(a+1 : ℕ))) +
        multiplier L 0 * f (s-(0 : ℕ)) = ∑ a ∈ range (L+1), multiplier L a * f (s-a) := by
      rw [← sum_range_succ' (fun a ↦ multiplier L a * f (s-a))]
      rw [sum_range_succ]
      simp [multiplier]
    have hshift (a : ℕ) : s-(a+1 : ℕ) = s-1-a := by push_cast; ring
    simp only [hshift] at *
    simp only [multiplier, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
      Nat.cast_zero, sub_zero] at *
    omega
theorem coeff_clear_pow_multiplier (f : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ((1 - T 1)^L * f).coeff s = ∑ a ∈ range (L+1), multiplier L a * f.coeff (s-a) := by
  rw [coeff_clear_pow, iterate_kernelDifference_eq_sum]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open Finset Filter LaurentPolynomial
private theorem coeff_sign_mul (n : ℕ) (p : LaurentPolynomial ℤ) (w : ℤ) :
    (((-1 : LaurentPolynomial ℤ)^n) * p).coeff w = ((-1 : ℤ)^n) * p.coeff w := by
  rw [show (-1 : LaurentPolynomial ℤ)^n = C ((-1 : ℤ)^n) by simp,
    ← single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply]
  simp
private theorem coeff_supercomm {N : ℕ} (i j : State) (hi : i.Nonempty)
    (hij : i.card = j.card) (α β : FockState N) (hαβ : weight α.val = weight β.val)
    (s : ℤ) :
    (((1 - T 1) ^ order (weight i) (weight j)) *
        ((fieldMatrix N false i * fieldMatrix N true j) α β -
          (-1 : LaurentPolynomial ℤ)^(i.card*j.card) *
            ((fieldMatrix N true j * fieldMatrix N false i) α β))).coeff s =
      truncatedRhs i j α.val β.val s N := by
  rw [coeff_clear_pow_multiplier]
  apply sum_congr rfl
  intro a _
  congr 1
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_sign_mul, Matrix.mul_apply,
    AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  let L := order (weight i) (weight j)
  have hL := two_mul_order_add hi hij
  have hb : -1-(L : ℤ)-(s-a) = -s-1-L+a := by ring
  congr 1
  · trans ∑ k : FockState N, blockMode i (-s-1-L+a) α.val k.val *
      blockMode j (s-a) k.val β.val
    · apply sum_congr rfl
      intro k _
      rw [coeff_field_pair i j α k k β L (s-a) (by omega) hL, hb]
    · exact sum_coe_sort (range N).powerset (fun k ↦
        blockMode i (-s-1-L+a) α.val k * blockMode j (s-a) k β.val)
  · congr 1
    trans ∑ k : FockState N, blockMode j (s-a) α.val k.val *
      blockMode i (-s-1-L+a) k.val β.val
    · apply sum_congr rfl
      intro k _
      rw [mul_comm (fieldMatrix N true j α k),
        coeff_field_pair i j k β α k L (s-a) (by omega) hL, hb, mul_comm]
    · exact sum_coe_sort (range N).powerset (fun k ↦
        blockMode j (s-a) α.val k * blockMode i (-s-1-L+a) k β.val)
private theorem eventually_fits (a : State) : ∀ᶠ N : ℕ in atTop, a ∈ (range N).powerset := by
  filter_upwards [eventually_ge_atTop (weight a)] with N hN
  exact mem_powerset.mpr fun i hi ↦ mem_range.mpr ((mode_lt_weight hi).trans_le hN)
theorem truncatedIdentity_of_laurent (h : LaurentCrossingIdentity) : TruncatedIdentity := by
  intro i j a b hi hij s
  change ∀ᶠ N : ℕ in atTop, pairing i j * (if a = b then 1 else 0) = truncatedRhs i j a b s N
  by_cases hab : weight a = weight b
  · filter_upwards [h i j a b hi hij hab s, eventually_fits a, eventually_fits b] with N hN ha hb
    let α : FockState N := ⟨a,ha⟩
    let β : FockState N := ⟨b,hb⟩
    exact (hN α β rfl rfl).symm.trans (coeff_supercomm i j hi hij α β hab s)
  · exact Eventually.of_forall fun N ↦ by
      rw [truncatedRhs_eq_zero_of_weight_ne hi hij hab]
      simp [show a ≠ b from fun he ↦ hab (congrArg weight he)]
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open Filter PowerSeries LaurentPolynomial
open scoped Polynomial PowerSeries BigOperators
private def poleEmbed (rev : Bool) (k : ℕ) (P : Polynomial ℤ) : LaurentPolynomial ℤ :=
  if rev then LaurentPolynomial.C ((-1)^k) * (T (-(k:ℤ)) * invert P.toLaurent)
  else P.toLaurent
private theorem poleEmbed_mul (rev : Bool) (k l : ℕ) (P Q : Polynomial ℤ) :
    poleEmbed rev (k+l) (P*Q) = poleEmbed rev k P * poleEmbed rev l Q := by
  cases rev
  · simp [poleEmbed]
  · simp only [poleEmbed, ite_true, pow_add, map_mul, Nat.cast_add, neg_add, T_add]
    ring
def PoleApprox (rev : Bool) (k : ℕ) (c : ℤ) (p : ℕ → LaurentPolynomial ℤ) : Prop :=
  ∃ P : ℕ → Polynomial ℤ, (∀ N, p N = poleEmbed rev k (P N)) ∧
    ∀ n : ℕ, ∀ᶠ N in atTop, (P N).coeff n = c * forwardKernel k n
namespace PoleApprox
theorem constant (rev : Bool) (c : ℤ) :
    PoleApprox rev 0 c (fun _ ↦ LaurentPolynomial.C c) := by
  refine ⟨fun _ ↦ Polynomial.C c, fun N ↦ ?_, fun n ↦ Eventually.of_forall fun N ↦ ?_⟩
  · cases rev <;> simp [poleEmbed]
  · change (Polynomial.C c).coeff n = c * PowerSeries.coeff n _
    rw [Polynomial.coeff_C, invOneSubPow_zero]
    simp [mul_ite]
theorem mul {rev : Bool} {k l : ℕ} {c d : ℤ} {p q : ℕ → LaurentPolynomial ℤ}
    (hp : PoleApprox rev k c p) (hq : PoleApprox rev l d q) :
    PoleApprox rev (k+l) (c*d) (fun N ↦ p N*q N) := by
  obtain ⟨P,hP,cp⟩ := hp
  obtain ⟨Q,hQ,cq⟩ := hq
  refine ⟨fun N ↦ P N * Q N, fun N ↦ by dsimp only; rw [hP, hQ, poleEmbed_mul], fun n ↦ ?_⟩
  filter_upwards [(eventually_all_finset (Finset.HasAntidiagonal.antidiagonal n)).mpr

      (fun (t : ℕ × ℕ) _ ↦ (cp t.1).and (cq t.2))] with N hN
  rw [Polynomial.coeff_mul]
  change _ = (c*d)*coeff n (invOneSubPow ℤ (k+l)).val
  rw [invOneSubPow_add, Units.val_mul, PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(hN t ht).1, (hN t ht).2]
  unfold forwardKernel
  ring
end PoleApprox
def trimPole (rev : Bool) (k : ℕ) (c : ℤ) (n : ℕ) : LaurentPolynomial ℤ :=
  if rev then ∑ t ∈ Finset.range n,
    LaurentPolynomial.C ((-1)^k * c * forwardKernel k (t:ℤ)) * T (-(t:ℤ)-k)
  else ∑ t ∈ Finset.range n, LaurentPolynomial.C (c * forwardKernel k (t:ℤ)) * T t
private def approxPoly (k : ℕ) (c : ℤ) (n : ℕ) : Polynomial ℤ :=
  ∑ t ∈ Finset.range n, Polynomial.monomial t (c*forwardKernel k t)
private theorem trimPole_eq_embed (rev : Bool) (k : ℕ) (c : ℤ) (n : ℕ) :
    trimPole rev k c n = poleEmbed rev k (approxPoly k c n) := by
  cases rev
  · simp [trimPole, poleEmbed, approxPoly, map_sum]
  · simp only [trimPole, poleEmbed, ite_true, approxPoly, map_sum, Polynomial.toLaurent_C_mul_T,
      map_mul, invert_C, invert_T, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [sub_eq_add_neg, T_add]
    ring
theorem PoleApprox.trim (rev : Bool) (k : ℕ) (c : ℤ) (d : ℕ) :
    PoleApprox rev k c (fun N ↦ trimPole rev k c (N-d)) := by
  refine ⟨fun N ↦ approxPoly k c (N-d), fun N ↦ trimPole_eq_embed _ _ _ _, fun n ↦ ?_⟩
  filter_upwards [eventually_ge_atTop (n+d+1)] with N hN
  have hn : n < N-d := by omega
  simp [approxPoly, Polynomial.coeff_monomial, hn]
private theorem coeff_toLaurent_nat (P : Polynomial ℤ) (n : ℕ) :
    P.toLaurent.coeff n = P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ n
private theorem coeff_toLaurent_neg (P : Polynomial ℤ) (n : ℕ) :
    P.toLaurent.coeff (.negSucc n) = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_not_mem_image_support
  rintro ⟨a, _, ha⟩
  change (a:ℤ) = .negSucc n at ha
  omega
theorem PoleApprox.coeff {rev : Bool} {k : ℕ} {c : ℤ} {p : ℕ → LaurentPolynomial ℤ}
    (h : PoleApprox rev k c p) (s : ℤ) :
    ∀ᶠ N in atTop, (p N).coeff s = c * (if rev then reverseKernel else forwardKernel) k s := by
  obtain ⟨P,hP,cp⟩ := h
  have hcoeff (t : ℤ) : ∀ᶠ N in atTop, (P N).toLaurent.coeff t = c * forwardKernel k t := by
    cases t with
    | ofNat n => simpa only [Int.ofNat_eq_natCast, coeff_toLaurent_nat] using cp n
    | negSucc n => exact Eventually.of_forall fun N ↦ by rw [coeff_toLaurent_neg]; simp [forwardKernel]
  cases rev
  · simpa [hP, poleEmbed] using hcoeff s
  · filter_upwards [hcoeff (-s-k)] with N hN
    rw [hP]
    simp only [poleEmbed, ite_true, reverseKernel]
    change (AddMonoidAlgebra.single 0 ((-1:ℤ)^k) *
      (AddMonoidAlgebra.single (-(k:ℤ)) 1 * invert (P N).toLaurent)).coeff s = _
    simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add, neg_neg,
      one_mul, invert_apply]
    rw [show -((k:ℤ)+s) = -s-k by ring, hN]
    ring
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
variable {α : Type*}
def wordWeight (mode : α → ℕ) (l : List α) : ℕ := (l.map (fun x ↦ 2 * mode x + 1)).sum
theorem wordWeight_eq (mode : α → ℕ) (l : List α) :
    wordWeight mode l = 2 * (l.map mode).sum + l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons] at *
    omega
private theorem wordWeight_erase (mode : α → ℕ) (l : List α) (j : Fin l.length) :
    wordWeight mode (l.eraseIdx j.val) + (2 * mode l[j.val] + 1) = wordWeight mode l := by
  induction l with
  | nil => exact Fin.elim0 j
  | cons x l ih =>
    cases j using Fin.cases with
    | zero => simp [wordWeight, Nat.add_comm]
    | succ k =>
      have h := ih k
      simp only [wordWeight, List.map_cons, List.sum_cons, Fin.val_succ,
        List.eraseIdx_cons_succ, List.getElem_cons_succ] at *
      omega
namespace Matching
def poleOrder (mode : α → ℕ) : {l r : List α} → Matching l r → ℕ
  | [], _, _ => 0
  | _ :: _, _, .inl p => poleOrder mode p
  | x :: _, r, .inr ⟨j, p⟩ => mode x + mode r[j.val] + 1 + poleOrder mode p
theorem twice_poleOrder_add_residual (mode : α → ℕ) (l r : List α) (p : Matching l r) :
    2 * p.poleOrder mode + wordWeight mode p.residual = wordWeight mode l + wordWeight mode r := by
  induction l generalizing r with
  | nil => simp [poleOrder, residual, wordWeight]
  | cons x l ih =>
    rcases p with p | ⟨j, p⟩
    · have h := ih r p
      simp only [poleOrder, residual, wordWeight, List.map_cons, List.sum_cons] at *
      omega
    · have h := ih _ p
      have h' := wordWeight_erase mode r j
      simp only [poleOrder, residual, wordWeight, List.map_cons, List.sum_cons] at *
      omega
theorem poleOrder_le_of_residual_ne_nil (mode : α → ℕ) {l r : List α}
    (p : Matching l r) (hlr : l.length = r.length) (hp : p.residual ≠ []) :
    p.poleOrder mode ≤ order (wordWeight mode l) (wordWeight mode r) := by
  have h := p.twice_poleOrder_add_residual mode ..
  rw [wordWeight_eq, wordWeight_eq mode l, wordWeight_eq mode r] at h
  have hn : 0 < p.residual.length := List.length_pos_iff.mpr hp
  simp only [order, wordWeight_eq]
  omega
theorem poleOrder_eq_of_residual_nil (mode : α → ℕ) {l r : List α}
    (p : Matching l r) (hlr : l.length = r.length) (hl : l ≠ []) (hp : p.residual = []) :
    p.poleOrder mode = order (wordWeight mode l) (wordWeight mode r) + 1 := by
  have h := p.twice_poleOrder_add_residual mode ..
  rw [hp] at h
  have hn : 0 < l.length := List.length_pos_iff.mpr hl
  simp only [show wordWeight mode [] = 0 from rfl, add_zero, wordWeight_eq] at h
  simp only [order, wordWeight_eq]
  omega
end Matching
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open LaurentPolynomial Filter
private theorem sum_empty_residual (α β : State) :
    ∑ t ∈ (mixedNormal [] α β).coeff.support, (mixedNormal [] α β).coeff t =
      (if α = β then 1 else 0) := by
  by_cases h : α = β
  · simp only [mixedNormal, ite_eq_left h, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0), Finset.sum_singleton,
      Finsupp.single_eq_same]
  · simp [mixedNormal, h]
theorem Matching.eventually_clear_of_coeff {l r : List FieldLabel} (p : Matching l r)
    (hlen : l.length = r.length) (hne : l ≠ [])
    (f g : ℕ → LaurentPolynomial ℤ) (a : ℤ)
    (hf : ∀ t, ∀ᶠ N in atTop, (f N).coeff t = a * forwardKernel (p.poleOrder Prod.snd) t)
    (hg : ∀ t, ∀ᶠ N in atTop, (g N).coeff t = a * reverseKernel (p.poleOrder Prod.snd) t)
    (α β : State) (s : ℤ) :
    let L := order (wordWeight Prod.snd l) (wordWeight Prod.snd r)
    let P := mixedNormal p.residual α β
    ∀ᶠ N in atTop, ((1-T 1)^L * (f N * P)).coeff s -
      ((1-T 1)^L * (g N * P)).coeff s =
      if p.residual = [] then a * (if α = β then 1 else 0) else 0 := by
  dsimp only
  by_cases hp : p.residual = []
  · have hk := p.poleOrder_eq_of_residual_nil Prod.snd hlen hne hp
    rw [hk] at hf hg
    simpa only [hp, ite_true, sum_empty_residual] using
      eventually_coeff_clear_full f g a _ hf hg (mixedNormal p.residual α β) s
  · simpa only [ite_eq_right hp] using eventually_coeff_clear_partial f g a _ _
      (p.poleOrder_le_of_residual_ne_nil Prod.snd hlen hp) hf hg (mixedNormal p.residual α β) s
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open LaurentPolynomial Finset
noncomputable section
theorem contractionPolynomial_forward (N i j : ℕ) :
    contractionPolynomial N (false, i) (true, j) =
      ∑ t ∈ range (N - j), C (kernelNumerator i j * forwardKernel (i + j + 1) (t : ℤ)) *
        T (t : ℤ) := by
  rw [contractionPolynomial, Fin.sum_univ_eq_sum_range
    (fun r ↦ annihilationCoeff (false, i) r * creationCoeff (true, j) r)]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    by_cases hj : j ≤ N
    · rw [show N + 1 - j = (N - j) + 1 by omega, sum_range_succ]
      congr 1
      simp only [annihilationCoeff, creationCoeff, fieldExponent, Bool.false_eq_true, ite_false,
        ite_true, T_zero, mul_one, Nat.cast_sub hj, ← mul_assoc, ← map_mul, differentiated_kernel]
    · have h₀ : N.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [show N + 1 - j = 0 by omega, show N - j = 0 by omega, creationCoeff, h₀]
end
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open LaurentPolynomial
private theorem reverse_kernelNumerator (i j : ℕ) :
    -kernelNumerator j i = (-1) ^ (i + j + 1) * kernelNumerator i j := by
  have hsign : (-1 : ℤ)^i * (-1)^i = 1 := by rw [← mul_pow]; simp
  unfold kernelNumerator
  rw [add_comm j i, ← Nat.choose_symm_add (a := i) (b := j), pow_succ, pow_add]
  linear_combination ((-1 : ℤ)^j * ((i+j).choose i : ℤ)) * hsign
private theorem reverse_contraction_mode (i j t : ℕ) :
    -(annihilationCoeff (true,j) (i+t) * creationCoeff (false,i) (i+t)) =
      C (((-1) ^ (i+j+1) : ℤ) * kernelNumerator i j * forwardKernel (i+j+1) (t : ℤ)) *
        T (-(t : ℤ) - i - j - 1) := by
  have hd := differentiated_kernel (i+t) j i
  rw [Nat.cast_add, add_sub_cancel_left, add_comm j i] at hd
  simp only [annihilationCoeff, creationCoeff, fieldExponent, ite_true, Bool.false_eq_true, ite_false,
    T_zero, mul_one, Nat.cast_add]
  rw [mul_right_comm (C _) (T _) (C _), ← map_mul, ← neg_mul, ← map_neg, hd, ← neg_mul,
    reverse_kernelNumerator]
  congr 2
  ring
theorem neg_contractionPolynomial_reverse (N i j : ℕ) :
    -contractionPolynomial N (true,j) (false,i) =
      ∑ t ∈ Finset.range (N-i),
        C (((-1)^(i+j+1) : ℤ) * kernelNumerator i j * forwardKernel (i+j+1) (t:ℤ)) *
          T (-(t:ℤ)-i-j-1) := by
  unfold contractionPolynomial
  rw [Fin.sum_univ_eq_sum_range (fun r ↦ annihilationCoeff (true,j) r * creationCoeff (false,i) r),
    ← Finset.sum_neg_distrib]
  have hvanish (n : ℕ) (hn : n ≤ i) :
      ∑ r ∈ Finset.range n, -(annihilationCoeff (true,j) r * creationCoeff (false,i) r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [creationCoeff, Nat.choose_eq_zero_of_lt ((Finset.mem_range.mp hr).trans_le hn)]
  rcases le_total N i with hN | hN
  · rw [hvanish N hN, Nat.sub_eq_zero_of_le hN]
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Finset.sum_range_add, hvanish i le_rfl, zero_add, Nat.add_sub_cancel_left]
    exact Finset.sum_congr rfl fun t _ ↦ reverse_contraction_mode i j t
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
theorem poleApprox_contractionPolynomial (rev : Bool) (i j : ℕ) :
    PoleApprox rev (i+j+1) (kernelNumerator i j)
      (fun N ↦ if rev then -contractionPolynomial N (true,j) (false,i)
        else contractionPolynomial N (false,i) (true,j)) := by
  cases rev
  · simpa only [Bool.false_eq_true, ite_false, contractionPolynomial_forward, trimPole] using
      PoleApprox.trim false (i+j+1) (kernelNumerator i j) j
  · simpa only [ite_true, neg_contractionPolynomial_reverse, trimPole, Nat.cast_add, Nat.cast_one,
      sub_add_eq_sub_sub] using PoleApprox.trim true (i+j+1) (kernelNumerator i j) i
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion.Matching
open LaurentPolynomial
noncomputable section
theorem weight_product_estimate {α : Type*} (mode : α → ℕ)
    (R : ℕ → ℤ → (ℕ → LaurentPolynomial ℤ) → Prop)
    (hC : ∀ c, R 0 c (fun _ ↦ C c))
    (hmul : ∀ {i j c d f g}, R i c f → R j d g → R (i+j) (c*d) (fun N ↦ f N * g N))
    (num : α → α → ℤ) (kern : ℕ → α → α → LaurentPolynomial ℤ)
    (l r : List α) (p : Matching l r)
    (hatom : ∀ x ∈ l, ∀ y ∈ r, R (mode x + mode y + 1) (num x y) (fun N ↦ kern N x y)) :
    R (p.poleOrder mode) (p.weight num) (fun N ↦ p.weight (kern N)) := by
  induction l generalizing r with
  | nil => simpa [poleOrder, weight] using hC 1
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · exact ih _ p (fun y hy ↦ hatom y (List.mem_cons_of_mem _ hy))
    · have htail := ih _ p (fun y hy z hz ↦
        hatom y (List.mem_cons_of_mem _ hy) z (List.mem_of_mem_eraseIdx hz))
      have hpair := hatom x List.mem_cons_self _ (List.getElem_mem j.isLt)
      have hsign := hC (((-1:ℤ)^l.length) * ((-1:ℤ)^j.val))
      have hprod := hmul (hmul hsign hpair) htail
      simpa only [poleOrder, weight, Nat.zero_add, map_mul, map_pow, map_neg, map_one,
        mul_assoc] using hprod
end
end Fermion.Matching
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion.Matching
theorem weightPoleApprox (rev : Bool) (l r : List FieldLabel) (p : Matching l r)
    (hl : ∀ f ∈ l, f.1 = false) (hr : ∀ g ∈ r, g.1 = true) :
    PoleApprox rev (p.poleOrder Prod.snd) (p.weight (fun x y ↦ kernelNumerator x.2 y.2))
      (fun N ↦ p.weight (fun x y ↦ if rev then -contractionPolynomial N y x
        else contractionPolynomial N x y)) := by
  apply weight_product_estimate Prod.snd (PoleApprox rev) (PoleApprox.constant rev)
    (fun h g ↦ PoleApprox.mul h g)
  intro x hx y hy
  have hxy := poleApprox_contractionPolynomial rev x.2 y.2
  obtain ⟨side, i⟩ := x
  obtain ⟨other, j⟩ := y
  have hs : side = false := hl _ hx
  have ht : other = true := hr _ hy
  subst side other
  exact hxy
end Fermion.Matching
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open LaurentPolynomial Filter
theorem Matching.eventually_clear_term {l r : List FieldLabel} (p : Matching l r)
    (hlen : l.length = r.length) (hne : l ≠ [])
    (hl : ∀ f ∈ l, f.1 = false) (hr : ∀ g ∈ r, g.1 = true) (α β : State) (s : ℤ) :
    let L := order (wordWeight Prod.snd l) (wordWeight Prod.snd r)
    let P := mixedNormal p.residual α β
    ∀ᶠ N in atTop, ((1-T 1)^L * (p.weight (contractionPolynomial N) * P)).coeff s -
      ((1-T 1)^L * (p.weight (fun x y => -contractionPolynomial N y x) * P)).coeff s =
      if p.residual = [] then p.weight (fun x y => kernelNumerator x.2 y.2) *
        (if α = β then 1 else 0) else 0 := by
  apply p.eventually_clear_of_coeff hlen hne
  · intro t
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      (Matching.weightPoleApprox false l r p hl hr).coeff t
  · intro t
    simpa only [↓reduceIte] using (Matching.weightPoleApprox true l r p hl hr).coeff t
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
variable (k : Type*) {α E : Type*} [CommRing k] [Ring E] [Algebra k E]
variable (C A : α → E)
variable (hcc : ∀ x y, C x * C y + C y * C x = 0)
variable (haa : ∀ x y, A x * A y + A y * A x = 0)
private theorem normal_prefix_smul (p l r : List α) (a : k) (hlen : l.length = r.length)
    (h : normal k C A l = a • normal k C A r) :
    normal k C A (p ++ l) = a • normal k C A (p ++ r) := by
  induction p with
  | nil => exact h
  | cons x p ih =>
    simp only [List.cons_append, normal, ih, List.length_append, hlen,
      mul_smul_comm, smul_mul_assoc, smul_add]
    rw [smul_comm]
include hcc haa in
theorem normal_swap_adjacent (p : List α) (x y : α) (s : List α) :
    normal k C A (p ++ x :: y :: s) = -normal k C A (p ++ y :: x :: s) := by
  have hc := eq_neg_of_add_eq_zero_left (hcc x y)
  have ha := eq_neg_of_add_eq_zero_left (haa y x)
  rw [← neg_one_smul k]
  apply normal_prefix_smul <;> try rfl
  simp only [normal, one_smul, List.length_cons, pow_succ, mul_neg, mul_one, neg_smul,
    mul_add, add_mul, smul_add, mul_smul_comm, smul_mul_assoc, ← mul_assoc (C x) (C y), hc,
    neg_mul, mul_assoc, ha, smul_neg]
  abel
include hcc haa in
private theorem normal_move_one (p : List α) (x : α) (r s : List α) :
    normal k C A (p ++ x :: (r ++ s)) =
      (-1 : k) ^ r.length • normal k C A (p ++ r ++ x :: s) := by
  induction r generalizing p with
  | nil => simp
  | cons y r ih =>
    simp only [List.cons_append, List.length_cons, pow_succ, mul_neg, mul_one, neg_smul]
    rw [normal_swap_adjacent k C A hcc haa]
    simpa [List.append_assoc] using congrArg Neg.neg (ih (p ++ [y]))
include hcc haa in
theorem normal_swap_blocks (p l r s : List α) :
    normal k C A (p ++ l ++ r ++ s) =
      (-1 : k) ^ (l.length * r.length) • normal k C A (p ++ r ++ l ++ s) := by
  induction l generalizing p with
  | nil => simp
  | cons x l ih =>
    have step₁ := ih (p ++ [x])
    have step₂ := normal_move_one k C A hcc haa p x r (l ++ s)
    simp only [List.append_assoc, List.nil_append, List.cons_append] at step₁
    simp only [List.append_assoc, List.length_cons, Nat.succ_mul, pow_add, List.cons_append] at step₂ ⊢
    rw [step₁, step₂, smul_smul]
include hcc haa in
theorem normal_append_swap (l r : List α) :
    normal k C A (l ++ r) = (-1 : k) ^ (l.length * r.length) • normal k C A (r ++ l) := by
  simpa using normal_swap_blocks k C A hcc haa [] l r []
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
open scoped BigOperators
theorem creationField_anticommute (N : ℕ) (f g : FieldLabel) :
    creationField N f * creationField N g + creationField N g * creationField N f = 0 :=
  weighted_same_modes _ (creation_mul_creation (LaurentPolynomial ℤ)) _ _
theorem annihilationField_anticommute (N : ℕ) (f g : FieldLabel) :
    annihilationField N f * annihilationField N g + annihilationField N g * annihilationField N f = 0 :=
  weighted_same_modes _ (annihilation_mul_annihilation (LaurentPolynomial ℤ)) _ _
theorem annihilationField_creationField (N : ℕ) (f g : FieldLabel) :
    annihilationField N f * creationField N g + creationField N g * annihilationField N f =
      algebraMap (LaurentPolynomial ℤ) _ (contractionPolynomial N f g) :=
  weighted_mixed_modes _ _ (annihilation_mul_creation (LaurentPolynomial ℤ)) _ _
theorem finite_normal_mul_normal (N : ℕ) (l r : List FieldLabel) :
    normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) l *
      normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) r =
      ∑ p : Matching l r, p.weight (contractionPolynomial N) •
        normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) p.residual :=
  normal_mul_normal _ _ _ (annihilationField_creationField N) (annihilationField_anticommute N) l r
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion.Matching
variable {α : Type*}
def skipCol (x : α) : {l r : List α} → Matching l r → Matching l (x :: r)
  | [], _, _ => ()
  | _ :: _, _, .inl p => .inl (skipCol x p)
  | _ :: _, _, .inr ⟨j, p⟩ => .inr ⟨j.succ, skipCol x p⟩
def pairAt (x : α) : {l r : List α} → (j : Fin l.length) →
    Matching (l.eraseIdx j.val) r → Matching l (x :: r)
  | [], _, j, _ => Fin.elim0 j
  | _ :: _, _, ⟨0, _⟩, p => .inr ⟨0, p⟩
  | _ :: l, r, ⟨j+1, h⟩, p =>
    match (p : Matching (_ :: l.eraseIdx j) r) with
    | .inl q => .inl (pairAt x ⟨j, Nat.lt_of_succ_lt_succ h⟩ q)
    | .inr ⟨k,q⟩ => .inr ⟨k.succ, pairAt x ⟨j, Nat.lt_of_succ_lt_succ h⟩ q⟩
def noCols : (l : List α) → Matching l []
  | [] => ()
  | _ :: l => .inl (noCols l)
def reverse : {l r : List α} → Matching l r → Matching r l
  | [], r, _ => noCols r
  | x :: _, _, .inl p => skipCol x (reverse p)
  | x :: _, _, .inr ⟨j,p⟩ => pairAt x j (reverse p)
end Fermion.Matching
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion.Matching
variable {α : Type*}
def leftRest : {l r : List α} → Matching l r → List α
  | [], _, _ => []
  | x :: _, _, .inl p => x :: leftRest p
  | _ :: _, _, .inr ⟨_,p⟩ => leftRest p
def rightRest : {l r : List α} → Matching l r → List α
  | [], r, _ => r
  | _ :: _, _, .inl p => rightRest p
  | _ :: _, _, .inr ⟨_,p⟩ => rightRest p
theorem residual_eq_append {l r : List α} (p : Matching l r) :
    p.residual = p.leftRest ++ p.rightRest := by
  induction l generalizing r with
  | nil => rfl
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [residual, leftRest, rightRest, ih]
private theorem rest_skipCol (x : α) {l r : List α} (p : Matching l r) :
    (skipCol x p).leftRest = p.leftRest ∧ (skipCol x p).rightRest = x :: p.rightRest := by
  induction l generalizing r with
  | nil => exact ⟨rfl,rfl⟩
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [skipCol, leftRest, rightRest, (ih p).1, (ih p).2]
private theorem rest_pairAt (x : α) {l r : List α} (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) :
    (pairAt x j p).leftRest = p.leftRest ∧ (pairAt x j p).rightRest = p.rightRest := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨_|j,hj⟩ := j
    · exact ⟨rfl,rfl⟩
    · change Matching (y :: l.eraseIdx j) r at p
      rcases p with p | ⟨k,p⟩ <;>
        simpa [pairAt, leftRest, rightRest] using ih ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p
private theorem rest_noCols (l : List α) :
    (noCols l).leftRest = l ∧ (noCols l).rightRest = [] := by
  induction l with
  | nil => exact ⟨rfl,rfl⟩
  | cons x l ih => simp [noCols, leftRest, rightRest, ih]
private theorem rest_reverse {l r : List α} (p : Matching l r) :
    p.reverse.leftRest = p.rightRest ∧ p.reverse.rightRest = p.leftRest := by
  induction l generalizing r with
  | nil => exact rest_noCols r
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [reverse, leftRest, rightRest, (rest_skipCol x p.reverse).1,
        (rest_skipCol x p.reverse).2, (ih p).1, (ih p).2, and_self]
    · simpa only [reverse, leftRest, rightRest, (rest_pairAt x j p.reverse).1,
        (rest_pairAt x j p.reverse).2] using ih p
@[simp] theorem leftRest_reverse {l r : List α} (p : Matching l r) :
    p.reverse.leftRest = p.rightRest := (rest_reverse p).1
@[simp] theorem rightRest_reverse {l r : List α} (p : Matching l r) :
    p.reverse.rightRest = p.leftRest := (rest_reverse p).2
end Fermion.Matching
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion.Matching
variable {α k : Type*} [CommRing k]
def edges : {l r : List α} → Matching l r → ℕ
  | [], _, _ => 0
  | _ :: _, _, .inl p => edges p
  | _ :: _, _, .inr ⟨_,p⟩ => edges p + 1
theorem edges_le {l r : List α} (p : Matching l r) : edges p ≤ l.length ∧ edges p ≤ r.length := by
  induction l generalizing r with
  | nil => simp [edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · have := ih p
      simp only [edges, List.length_cons]
      omega
    · have h := ih p
      rw [List.length_eraseIdx_of_lt j.isLt] at h
      have := j.isLt
      simp only [edges, List.length_cons]
      omega
@[simp] theorem edges_skipCol (x : α) {l r : List α} (p : Matching l r) :
    edges (skipCol x p) = edges p := by
  induction l generalizing r with
  | nil => rfl
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [skipCol, edges, ih]
@[simp] theorem edges_pairAt (x : α) {l r : List α} (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) : edges (pairAt x j p) = edges p + 1 := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨_|j,hj⟩ := j
    · rfl
    · change Matching (y :: l.eraseIdx j) r at p
      rcases p with p | ⟨k,p⟩ <;> simp [pairAt, edges, ih]
@[simp] theorem edges_noCols (l : List α) : edges (noCols l) = 0 := by
  induction l <;> simp [noCols, edges, *]
@[simp] theorem edges_reverse {l r : List α} (p : Matching l r) : edges (reverse p) = edges p := by
  induction l generalizing r with
  | nil => simp [reverse, edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩ <;> simp [reverse, edges, ih]
theorem weight_skipCol (κ : α → α → k) (x : α) {l r : List α} (p : Matching l r) :
    weight κ (skipCol x p) = (-1 : k) ^ edges p * weight κ p := by
  induction l generalizing r with
  | nil => simp [weight, edges]
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩
    · simp [skipCol, weight, edges, ih]
    · simp only [skipCol, weight, edges, Fin.val_succ, List.getElem_cons_succ, List.eraseIdx_cons_succ, ih, pow_succ]
      ring
theorem weight_pairAt (κ : α → α → k) (x : α) {l r : List α} (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) :
    weight κ (pairAt x j p) = (-1 : k) ^ (l.length - (j.val + 1)) * κ l[j.val] x * weight κ p := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨_|j,hj⟩ := j
    · simp [pairAt, weight]
    · change Matching (y :: l.eraseIdx j) r at p
      have hlt : j < l.length := Nat.lt_of_succ_lt_succ hj
      have hlen : l.length = (l.eraseIdx j).length + 1 := by rw [List.length_eraseIdx_of_lt hlt]; omega
      rcases p with p | ⟨t,p⟩
      · simp [pairAt, weight, ih]
      · simp only [pairAt, weight, Fin.val_succ, List.getElem_cons_succ, List.length_cons,
          Nat.add_sub_add_right, List.eraseIdx_cons_succ, ih, pow_succ]
        rw [show (-1 : k)^l.length = (-1)^(l.eraseIdx j).length * (-1) by rw [hlen, pow_succ]]
        ring
@[simp] theorem weight_noCols (κ : α → α → k) (l : List α) : weight κ (noCols l) = 1 := by
  induction l <;> simp [noCols, weight, *]
private theorem sign_skip {l r q : ℕ} (hl : q ≤ l) (hr : q ≤ r) :
    (-1 : k)^q * (-1)^(l*r + (l-q)*(r-q)) =
      (-1)^((l+1)*r + (l+1-q)*(r-q)) := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (R := k) ((l+1)*r + _)]
  congr 1
  rw [show l+1-q = (l-q)+1 by omega, Nat.add_mul, Nat.add_mul]
  simp only [one_mul]
  omega
private theorem sign_pair {l r q j : ℕ} (hj : j ≤ r) :
    ((-1 : k)^(r-j) * (-1)) * (-1)^(l*r + (l-q)*(r-q)) =
      (-1)^((l+1)*(r+1) + (l-q)*(r-q)) * ((-1)^l * (-1)^j) := by
  rw [← pow_succ, ← pow_add, ← pow_add, ← pow_add, neg_one_pow_eq_pow_mod_two,
    neg_one_pow_eq_pow_mod_two (R := k) ((l+1)*(r+1) + (l-q)*(r-q) + _)]
  congr 1
  simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
  omega
theorem weight_reverse (κ : α → α → k) {l r : List α} (p : Matching l r) :
    weight (fun x y ↦ -κ y x) (reverse p) =
      (-1 : k)^(l.length*r.length + (l.length-edges p)*(r.length-edges p)) * weight κ p := by
  induction l generalizing r with
  | nil => simp [reverse, weight, edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [reverse, weight_skipCol, edges_reverse, ih, edges, weight, List.length_cons,
        ← mul_assoc, sign_skip (edges_le p).1 (edges_le p).2]
    · simp only [reverse, weight_pairAt, ih, edges, weight, List.length_cons]
      let t := (r.eraseIdx j.val).length
      have ht : r.length = t + 1 := by
        dsimp [t]
        rw [List.length_eraseIdx_of_lt j.isLt]
        have := j.isLt
        omega
      have hj : j.val ≤ t := by have := j.isLt; omega
      have he := sign_pair (k := k) (l := l.length) (q := edges p) hj
      have hr : r.length - (j.val+1) = t-j.val := by omega
      have hb : r.length - (edges p+1) = t-edges p := by omega
      rw [hr, hb, Nat.add_sub_add_right]
      rw [show (l.length+1)*r.length = (l.length+1)*(t+1) by rw [ht]]
      change (-1 : k) ^ (t-↑j) * -κ x r[↑j] *
          ((-1) ^ (l.length*t + (l.length-edges p)*(t-edges p)) * weight κ p) = _
      linear_combination he * κ x r[↑j] * weight κ p
end Fermion.Matching
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion.Matching
variable {α : Type*}
private theorem length_rest_add_edges {l r : List α} (p : Matching l r) :
    p.leftRest.length + p.edges = l.length ∧ p.rightRest.length + p.edges = r.length := by
  induction l generalizing r with
  | nil => simp [leftRest, rightRest, edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · obtain ⟨hl, hr⟩ := ih p
      simp only [leftRest, rightRest, edges, List.length_cons]
      omega
    · obtain ⟨hl, hr⟩ := ih p
      rw [List.length_eraseIdx_of_lt j.isLt] at hr
      have := j.isLt
      simp only [leftRest, rightRest, edges, List.length_cons]
      omega
theorem leftRest_length {l r : List α} (p : Matching l r) :
    p.leftRest.length = l.length - p.edges := by
  have := (length_rest_add_edges p).1
  omega
theorem rightRest_length {l r : List α} (p : Matching l r) :
    p.rightRest.length = r.length - p.edges := by
  have := (length_rest_add_edges p).2
  omega
end Fermion.Matching
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion.Matching
variable {α : Type*}
@[simp] theorem reverse_skipCol (x : α) (l r : List α) (p : Matching l r) :
    reverse (skipCol x p) = (.inl (reverse p) : Matching (x :: r) l) := by
  induction l generalizing r with
  | nil => rfl
  | cons y l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [skipCol, reverse, ih]
      rfl
    · exact (congrArg (pairAt (l := x :: r) (r := l) y j.succ) (ih _ p)).trans rfl
@[simp] theorem reverse_pairAt (x : α) (l r : List α) (j : Fin l.length)
    (p : Matching (l.eraseIdx j.val) r) :
    reverse (pairAt x j p) = (.inr ⟨j, reverse p⟩ : Matching (x :: r) l) := by
  induction l generalizing r with
  | nil => exact Fin.elim0 j
  | cons y l ih =>
    obtain ⟨j, hj⟩ := j
    cases j with
    | zero => rfl
    | succ j =>
      change Matching (y :: l.eraseIdx j) r at p
      rcases p with p | ⟨k,p⟩
      · simp only [pairAt, reverse, skipCol, ih]
        rfl
      · exact (congrArg (pairAt (l := x :: r) (r := l) y k.succ)
          (ih _ ⟨j, Nat.lt_of_succ_lt_succ hj⟩ p)).trans rfl
@[simp] theorem reverse_reverse (l r : List α) (p : Matching l r) : reverse (reverse p) = p := by
  induction l generalizing r with
  | nil => exact Subsingleton.elim (α := Unit) _ _
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · simp only [reverse, reverse_skipCol, ih]
      rfl
    · simp only [reverse, reverse_pairAt, ih]
      rfl
def reverseEquiv (l r : List α) : Matching l r ≃ Matching r l where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_reverse l r
  right_inv := reverse_reverse r l
end Fermion.Matching
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
variable {α k E : Type*} [CommRing k] [Ring E] [Algebra k E]
variable (C A : α → E)
variable (hcc : ∀ x y, C x * C y + C y * C x = 0)
variable (haa : ∀ x y, A x * A y + A y * A x = 0)
include hcc haa in
theorem wickTerm_reverse (κ : α → α → k) {l r : List α} (p : Matching l r) :
    p.reverse.weight (fun x y ↦ -κ y x) • normal k C A p.reverse.residual =
      (-1 : k)^(l.length*r.length) • (p.weight κ • normal k C A p.residual) := by
  rw [Matching.weight_reverse, p.reverse.residual_eq_append, p.residual_eq_append,
    Matching.leftRest_reverse, Matching.rightRest_reverse,
    normal_append_swap k C A hcc haa p.leftRest p.rightRest, p.leftRest_length, p.rightRest_length,
    pow_add, smul_smul, smul_smul]
  congr 1
  ring
include hcc haa in
theorem wickSum_reverse (κ : α → α → k) (l r : List α) :
    wickSum (fun x y ↦ -κ y x) (normal k C A) r l =
      (-1 : k)^(l.length*r.length) • wickSum κ (normal k C A) l r := by
  unfold wickSum
  rw [Finset.smul_sum, ← (Matching.reverseEquiv l r).sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  exact wickTerm_reverse C A hcc haa κ p
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
namespace Fermion
theorem supercommutator_apply_eq_sum (N : ℕ) (l r : List FieldLabel) (α β : FockState N) :
    let n := normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N)
    (n l * n r - (-1 : LaurentPolynomial ℤ) ^ (l.length * r.length) • (n r * n l)) α β =
      ∑ p : Matching l r,
        (p.weight (contractionPolynomial N) - p.weight (fun x y ↦ -contractionPolynomial N y x)) *
          mixedNormal p.residual α.val β.val := by
  let n := normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N)
  have h lr rr : n lr * n rr = wickSum (contractionPolynomial N) n lr rr :=
    finite_normal_mul_normal N lr rr
  have hrev := wickSum_reverse _ _ (creationField_anticommute N) (annihilationField_anticommute N)
    (contractionPolynomial N) r l
  rw [Nat.mul_comm r.length l.length] at hrev
  change (n l * n r - _ • (n r * n l)) α β = _
  rw [h, h, ← hrev]
  simp only [wickSum, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  change _ * n p.residual α β - _ * n p.residual α β = _
  rw [← sub_mul, show n p.residual α β = mixedNormal p.residual α.val β.val from normal_matrix_apply ..]
theorem fieldMatrix_commutator_apply (N : ℕ) (i j : State) (α β : FockState N) :
    (fieldMatrix N false i * fieldMatrix N true j) α β -
        (-1 : LaurentPolynomial ℤ) ^ (i.card * j.card) *
          (fieldMatrix N true j * fieldMatrix N false i) α β =
      ∑ p : Matching (fieldWord false i) (fieldWord true j),
        (p.weight (contractionPolynomial N) - p.weight (fun x y ↦ -contractionPolynomial N y x)) *
          mixedNormal p.residual α.val β.val := by
  have word_length (s : Bool) (I : State) : (fieldWord s I).length = I.card := by
    simp [fieldWord]
  simpa only [fieldMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, word_length] using
    supercommutator_apply_eq_sum N (fieldWord false i) (fieldWord true j) α β
end Fermion
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open scoped BigOperators
variable {α k : Type*} [CommRing k]
def fullContractions (κ : α → α → k) (l r : List α) : k :=
  ∑ p : Matching l r, if p.residual.isEmpty then p.weight κ else 0
theorem fullContractions_cons (κ : α → α → k) (x : α) (l r : List α) :
    fullContractions κ (x :: l) r =
      ∑ j : Fin r.length, ((-1 : k) ^ l.length * ((-1 : k) ^ j.val * κ x r[j.val])) *
        fullContractions κ l (r.eraseIdx j.val) := by
  unfold fullContractions
  change (∑ p : Matching l r ⊕ (Σ j : Fin r.length, Matching l (r.eraseIdx j.val)), _) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp [Matching.residual, Matching.weight, Finset.mul_sum, mul_ite]
private theorem eraseIdx_ofFn {n : ℕ} (r : Fin (n+1) → α) (j : Fin (n+1)) :
    (List.ofFn r).eraseIdx j.val = List.ofFn (fun t ↦ r (j.succAbove t)) := by
  have hj : j.val < (List.ofFn r).length := by simpa using j.isLt
  apply List.ext_getElem
  · rw [List.length_eraseIdx_of_lt hj, List.length_ofFn, List.length_ofFn]; omega
  · intro i hi hi'
    have hin : i < n := by simpa using hi'
    let t : Fin n := ⟨i,hin⟩
    by_cases h : i < j.val
    · rw [List.getElem_eraseIdx_of_lt hi h]
      simp only [List.getElem_ofFn]
      exact congrArg r (j.succAbove_of_castSucc_lt t h).symm
    · rw [List.getElem_eraseIdx_of_ge hi (Nat.le_of_not_gt h)]
      simp only [List.getElem_ofFn]
      exact congrArg r (j.succAbove_of_le_castSucc t (Nat.le_of_not_gt h)).symm
private theorem fullContractions_step (κ : α → α → k) {n : ℕ}
    (l r : Fin (n+1) → α) :
    fullContractions κ (List.ofFn l) (List.ofFn r) =
      ∑ j : Fin (n+1), ((-1 : k)^n * ((-1 : k)^j.val * κ (l 0) (r j))) *
        fullContractions κ (List.ofFn (fun t ↦ l t.succ)) (List.ofFn (fun t ↦ r (j.succAbove t))) := by
  rw [List.ofFn_succ (f := l), fullContractions_cons]
  apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := r)))
  intro j
  let s : Fin (n+1) := ⟨j.val, by simpa using j.isLt⟩
  simp only [List.length_ofFn, List.getElem_ofFn]
  rw [show (List.ofFn r).eraseIdx j.val = List.ofFn (fun t ↦ r (s.succAbove t)) from
    eraseIdx_ofFn r s]
  rfl
theorem fullContractions_eq_det (κ : α → α → k) (n : ℕ) (l r : Fin n → α) :
    fullContractions κ (List.ofFn l) (List.ofFn r) =
      (-1 : k) ^ n.choose 2 * (Matrix.of (fun i j ↦ κ (l i) (r j))).det := by
  induction n with
  | zero =>
    rw [Matrix.det_isEmpty, Nat.choose_eq_zero_of_lt (by decide : 0 < 2), pow_zero, mul_one]
    change (∑ _ : Unit, (1 : k)) = 1
    simp
  | succ n ih =>
    rw [fullContractions_step, Matrix.det_succ_row_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, pow_add, Matrix.of_apply]
    rw [show (Matrix.of (fun i j ↦ κ (l i) (r j))).submatrix Fin.succ j.succAbove =
      Matrix.of (fun i s ↦ κ (l i.succ) (r (j.succAbove s))) from rfl]
    ring
private theorem sorted_ofFn (S : Finset ℕ) {n : ℕ} (h : S.card = n) :
    S.sort (· ≤ ·) = List.ofFn (S.orderEmbOfFin h) := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi'
    simp [Finset.orderEmbOfFin_apply]
theorem fullContractions_kernelNumerator (I J : Finset ℕ) (h : J.card = I.card) :
    fullContractions kernelNumerator (I.sort (· ≤ ·)) (J.sort (· ≤ ·)) = pairing I J := by
  rw [sorted_ofFn I rfl, sorted_ofFn J h, fullContractions_eq_det]
  let A : Matrix (Fin I.card) (Fin I.card) ℤ :=
    Matrix.of (fun i j ↦ ((I.orderEmbOfFin rfl i + J.orderEmbOfFin h j).choose
      (I.orderEmbOfFin rfl i) : ℤ))
  let v (i : Fin I.card) : ℤ := (-1) ^ I.orderEmbOfFin rfl i
  change _ * (Matrix.of (fun i j ↦ v i * A i j)).det = _
  rw [Matrix.det_mul_column, pairing, stateMinor, dite_eq_left h, pairingSign, pow_add]
  have hs : (∑ i : Fin I.card, I.orderEmbOfFin rfl i) = ∑ i ∈ I, i := by
    conv_rhs => rw [← I.map_orderEmbOfFin_univ rfl]
    rw [Finset.sum_map]; rfl
  change _ * ((∏ i, (-1 : ℤ) ^ I.orderEmbOfFin rfl i) * A.det) = _ * A.det
  rw [Finset.prod_pow_eq_pow_sum, hs, mul_assoc]
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
theorem fullContractions_map {α β R : Type*} [CommRing R] (κ : β → β → R)
    (f g : α → β) (l r : List α) :
    fullContractions κ (l.map f) (r.map g) =
      fullContractions (fun x y ↦ κ (f x) (g y)) l r := by
  induction l generalizing r with
  | nil =>
    change (∑ _ : Unit, if (r.map g).isEmpty then (1 : R) else 0) =
      ∑ _ : Unit, if r.isEmpty then (1 : R) else 0
    simp
  | cons x l ih =>
    simp only [List.map_cons, fullContractions_cons]
    apply Fintype.sum_equiv (finCongr (List.length_map (f := g)))
    intro j
    simp only [List.length_map, List.getElem_map, List.eraseIdx_map, ih]
    rfl
theorem fullContractions_tagged_kernelNumerator (I J : Finset ℕ) (h : J.card = I.card)
    (first second : Bool) :
    fullContractions (fun f g : Bool × ℕ ↦ kernelNumerator f.2 g.2)
      ((I.sort (· ≤ ·)).map (fun i ↦ (first, i)))
      ((J.sort (· ≤ ·)).map (fun j ↦ (second, j))) = pairing I J := by
  rw [fullContractions_map]
  exact fullContractions_kernelNumerator I J h
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Filter LaurentPolynomial
open scoped BigOperators
theorem wordWeight_fieldWord (i : State) (b : Bool) :
    wordWeight Prod.snd (fieldWord b i) = weight i := by
  simp only [wordWeight, fieldWord, List.map_map]
  change (Multiset.map (fun t : ℕ ↦ 2*t+1) (i.sort (· ≤ ·) : Multiset ℕ)).sum = _
  rw [Finset.sort_eq]
  rfl
theorem eventually_cleared_wick_sum (i j α β : State) (hij : i.card = j.card)
    (s : ℤ) (L : ℕ)
    (hterm : ∀ p : Matching (fieldWord false i) (fieldWord true j),
      ∀ᶠ N : ℕ in atTop,
        ((1 - T 1)^L * (p.weight (contractionPolynomial N) * mixedNormal p.residual α β)).coeff s -
        ((1 - T 1)^L * (p.weight (fun f g ↦ -(contractionPolynomial N g f)) *
          mixedNormal p.residual α β)).coeff s =
        (if p.residual.isEmpty then p.weight (fun f g ↦ kernelNumerator f.2 g.2) else 0) *
          (if α = β then 1 else 0)) :
    ∀ᶠ N : ℕ in atTop,
      ((1 - T 1)^L * (∑ p : Matching (fieldWord false i) (fieldWord true j),
        (p.weight (contractionPolynomial N) - p.weight (fun f g ↦ -(contractionPolynomial N g f))) *
          mixedNormal p.residual α β)).coeff s = pairing i j * (if α = β then 1 else 0) := by
  filter_upwards [eventually_all.mpr hterm] with N hN
  rw [← fullContractions_tagged_kernelNumerator i j hij.symm false true]
  simp only [fullContractions, Finset.sum_mul, Finset.mul_sum, sub_mul, mul_sub,
    AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_sub, Finsupp.finsetSum_apply, Finsupp.sub_apply]
  exact Finset.sum_congr rfl (fun p _ ↦ hN p)
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
namespace Fermion
open Filter LaurentPolynomial
theorem laurentCrossingIdentity : LaurentCrossingIdentity := by
  intro i j a b hi hij _ s
  have hl {x : State} (c : Bool) : (fieldWord c x).length = x.card := by simp [fieldWord]
  have htag (x : State) (c : Bool) : ∀ f ∈ fieldWord c x, f.1 = c := by
    intro f hf
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
    rfl
  have hne : fieldWord false i ≠ [] := by
    intro h
    have h' := hl (x := i) false
    rw [h, List.length_nil] at h'
    exact hi.card_pos.ne h'
  have het := eventually_cleared_wick_sum i j a b hij s (order (weight i) (weight j)) fun p ↦ by
    have h := p.eventually_clear_term (by simpa only [hl] using hij) hne (htag i false)
      (htag j true) a b s
    by_cases hp : p.residual = [] <;> simpa [hp, wordWeight_fieldWord] using h
  filter_upwards [het] with N hN
  intro α β ha hb
  rw [fieldMatrix_commutator_apply N i j α β]
  simpa only [ha, hb] using hN
end Fermion
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Set
open scoped Topology
theorem exists_nonunit_slope {f : ℝ → ℝ} {L t : ℝ}
    (hlip : LipschitzOnWith 1 f (Icc 0 L)) (hcv : ConvexOn ℝ (Icc 0 L) f)
    (ht : t ∈ Ioo 0 L) (htpos : 0 < f t)
    (hleft : f 0 - t < f t) (hright : f L - (L - t) < f t) :
    ∃ y ∈ Ioo 0 L, 0 < f y ∧ DifferentiableAt ℝ f y ∧ |deriv f y| < 1 := by
  have hit : t ∈ interior (Icc 0 L) := by simpa only [interior_Icc] using ht
  obtain ⟨Y, hY, hprop⟩ := exists_differentiable_seq_above_facet hlip hit htpos
    (e := (1 : ℝ)) (by simp)
  have hyin (j : ℕ) : Y j ∈ Ioo 0 L := by simpa only [interior_Icc] using (hprop j).1
  have hcont := hlip.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hit)
  have hf := hcont.tendsto.comp hY
  have hl := (tendsto_const_nhds.sub hY).eventually_lt hf hleft
  have hr := (tendsto_const_nhds.sub (tendsto_const_nhds.sub hY)).eventually_lt hf hright
  obtain ⟨j, hjl, hjr⟩ := (hl.and hr).exists
  have hy := hyin j
  have hL := (lt_trans hy.1 hy.2).le
  have hd := (hprop j).2.2.2
  refine ⟨Y j, hy, (hprop j).2.2.1, hd, abs_lt.mpr ⟨?_, ?_⟩⟩
  · apply lt_of_lt_of_le _ (hcv.slope_le_deriv (left_mem_Icc.mpr hL) (show Y j ∈ Icc 0 L from ⟨hy.1.le, hy.2.le⟩)
      hy.1 hd)
    rw [slope_def_field, sub_zero, lt_div_iff₀ hy.1]
    change f 0 - Y j < f (Y j) at hjl
    linarith
  · apply lt_of_le_of_lt (hcv.deriv_le_slope (show Y j ∈ Icc 0 L from ⟨hy.1.le, hy.2.le⟩) (right_mem_Icc.mpr hL)
      hy.2 hd) _
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hy.2)]
    change f L - (L - Y j) < f (Y j) at hjr
    linarith
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
noncomputable section
section
open Filter Topology Set WithLp
theorem mem_flatApexHull_of_height {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) {H : ℝ} (hH : 0 < H) (z : Book.Lift E) (hz : z.snd ∈ Ioo 0 H) :
    z ∈ flatApexHull a H := by
  let t := z.snd / H
  have ht₀ : 0 ≤ t := div_nonneg hz.1.le hH.le
  have ht₁ : t < 1 := (div_lt_one hH).2 hz.2
  let v := (1-t)⁻¹ • (z.fst - t • a)
  have hm := (convex_convexHull ℝ _)
    (flatApexHull_base_mem a H v) (flatApexHull_apex_mem a H)
    (sub_nonneg.mpr ht₁.le) ht₀ (sub_add_cancel 1 t)
  have he : (1-t) • toLp 2 (v, (0 : ℝ)) + t • toLp 2 (a, H) = z := by
    apply ofLp_injective
    apply Prod.ext
    · change (1-t) • ((1-t)⁻¹ • (z.fst - t • a)) + t • a = z.fst
      rw [smul_smul, mul_inv_cancel₀ (sub_pos.mpr ht₁).ne', one_smul, sub_add_cancel]
    · change (1-t) * 0 + (z.snd / H) * H = z.snd
      simp [hH.ne']
  rwa [he] at hm
def SpectralPlacementPrices.ofNeighborhood {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Field K] {U : Set E} {o : E} (hU : U ∈ 𝓝 o) (P : SpectralPlacementPrices K U) :
    SpectralPlacementPrices K E := by
  classical
  let φ (x : E) : U := if h : x ∈ U then ⟨x,h⟩ else ⟨o, mem_of_mem_nhds hU⟩
  have hφ : ∀ x ∈ U, ∀ y ∈ U, dist (φ x) (φ y) = dist x y := by
    intro x hx y hy
    simp only [φ, dite_eq_left hx, dite_eq_left hy, Subtype.dist_eq]
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  let s (n : ℕ) : ℝ := 1 / (n+1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  exact (Book.blowupSpectralPrices ω hs (φ o) P).pullback (Book.tangentFlat ω hs hφ hU)
    (Book.isometry_tangentFlat ω hs hφ hU (Ultrafilter.of_le _)
      tendsto_one_div_add_atTop_nhds_zero_nat)
def SpectralPlacementPrices.planeOfFlatApexHull {K : Type*} [Field K] {a H : ℝ} (hH : 0 < H)
    (P : SpectralPlacementPrices K (flatApexHull a H)) :
    SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2)) := by
  let c : Book.Lift ℝ := toLp 2 (a, H/2)
  have hc : c.snd ∈ Ioo (0 : ℝ) H := ⟨by change 0 < H/2; linarith, by change H/2 < H; linarith⟩
  have hn : flatApexHull a H ∈ 𝓝 c :=
    mem_of_superset ((show Continuous (fun x : Book.Lift ℝ ↦ x.snd) from WithLp.continuous_snd ..).continuousAt (Ioo_mem_nhds hc.1 hc.2))
      (fun z hz ↦ mem_flatApexHull_of_height a hH z hz)
  let f (x : EuclideanSpace ℝ (Fin 2)) : Book.Lift ℝ := toLp 2 (x 0, x 1)
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    rw [WithLp.prod_dist_eq_of_L2, EuclideanSpace.dist_eq, Fin.sum_univ_two]
    rfl
  exact (P.ofNeighborhood hn).pullback f hf
end
end
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open Filter Set HyperbolicObstruction
open scoped Topology
variable {F X : Type*} [Field F] [MetricSpace X] (P : SpectralPlacementPrices F X) (hX : CATZero X)
include P hX
private theorem plane_of_side_defect {L t : ℝ} {c : ℝ → X} {z : X}
    (hc : ∀ s ∈ Icc 0 L, ∀ u ∈ Icc 0 L, dist (c s) (c u) = dist s u)
    (ht : t ∈ Ioo 0 L) (hpos : 0 < dist (c t) z)
    (hl : dist (c 0) z - t < dist (c t) z)
    (hr : dist (c L) z - (L-t) < dist (c t) z) :
    Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))) := by
  let f (s : ℝ) := dist (c s) z
  have hLip : LipschitzOnWith 1 f (Icc 0 L) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, ← hc x hx y hy] using
      abs_dist_sub_le (c x) (c y) z
  have hcv := cat0_patch_convexOn_dist (isCAT0_of_catZero hX) (convex_Icc 0 L) hc z
  obtain ⟨y, hy, hfy, hdiff, hsmall⟩ := exists_nonunit_slope hLip hcv ht hpos hl hr
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  let s (n : ℕ) : ℝ := 1 / (n+1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hU : Icc 0 L ∈ 𝓝 y := Icc_mem_nhds hy.1 hy.2
  obtain ⟨_, Q, _⟩ := Book.exists_tangentHull_spectralPrices ω hs hc hU hX z
    (M := 1) zero_le_one (Ultrafilter.of_le _)
    tendsto_one_div_add_atTop_nhds_zero_nat P hdiff.hasDerivAt.hasGradientAt'
  apply Nonempty.intro (Q.planeOfFlatApexHull ?_)
  change 0 < (1 : ℝ) * (f y * Real.sqrt (1 - ‖deriv f y‖ ^ 2))
  rw [one_mul]
  apply mul_pos hfy (Real.sqrt_pos.mpr ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (deriv f y), abs_nonneg (deriv f y),
    mul_pos (sub_pos.mpr hsmall) (show 0 < 1 + |deriv f y| by positivity)]
theorem spectralPlane_of_fourPointDefect (a b z w : X)
    (hbad : max (dist a z + dist b w) (dist a w + dist b z) < dist a b + dist z w) :
    Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))) := by
  let L := dist a b
  have hL : 0 < L := by
    apply dist_pos.mpr
    rintro rfl
    rw [dist_self, zero_add, max_lt_iff] at hbad
    linarith [dist_triangle_left z w a]
  let c (t : ℝ) := CATZero.segment hX a b (t/L)
  have hfrac {t : ℝ} (ht : t ∈ Icc 0 L) : t/L ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
  have hc (s : ℝ) (hs : s ∈ Icc 0 L) (u : ℝ) (hu : u ∈ Icc 0 L) :
      dist (c s) (c u) = dist s u := by
    dsimp only [c]
    rw [CATZero.segment_dist hX a b (hfrac hs) (hfrac hu)]
    change |s/L - u/L| * L = _
    rw [← sub_div, abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne', Real.dist_eq]
  have hc0 : c 0 = a := by simp [c, (CATZero.segment_spec hX a b).1]
  have hcL : c L = b := by simp [c, hL.ne', (CATZero.segment_spec hX a b).2.1]
  let t (x : X) := (dist a x - dist b x + L)/2
  let h (x : X) := (dist a x + dist b x - L)/2
  have ht (x : X) : t x ∈ Icc 0 L := by
    dsimp [t,L]
    constructor <;> linarith [dist_triangle_left b x a, dist_triangle a b x, dist_comm b a]
  have hh (x : X) : 0 ≤ h x := by
    dsimp [h,L]
    linarith [dist_triangle_right a b x]
  have deficient : h z < dist (c (t z)) z ∨ h w < dist (c (t w)) w := by
    by_contra! hneg
    have tri := dist_triangle z (c (t z)) w
    have tri' := dist_triangle (c (t z)) (c (t w)) w
    rw [dist_comm z (c (t z))] at tri
    rw [hc _ (ht z) _ (ht w), Real.dist_eq] at tri'
    rw [max_lt_iff] at hbad
    cases le_total (t z) (t w) with
    | inl hz =>
      rw [abs_of_nonpos (sub_nonpos.mpr hz)] at tri'
      dsimp [h,t,L] at hneg tri'
      linarith [hneg.1,hneg.2,hbad.1,hbad.2]
    | inr hw =>
      rw [abs_of_nonneg (sub_nonneg.mpr hw)] at tri'
      dsimp [h,t,L] at hneg tri'
      linarith [hneg.1,hneg.2,hbad.1,hbad.2]
  have directly (x : X) (hd : h x < dist (c (t x)) x) :
      Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))) := by
    have hl : dist a x - t x = h x := by dsimp [t,h]; ring
    have hr : dist b x - (L - t x) = h x := by dsimp [t,h]; ring
    have hit : t x ∈ Ioo 0 L := by
      constructor
      · apply lt_of_le_of_ne (ht x).1
        intro eq
        rw [← eq, hc0] at hd
        linarith [hl]
      · apply lt_of_le_of_ne (ht x).2
        intro eq
        rw [eq, hcL] at hd
        linarith [hr]
    exact plane_of_side_defect P hX hc hit ((hh x).trans_lt hd)
      (by rwa [hc0,hl]) (by rwa [hcL,hr])
  exact deficient.elim (directly z) (directly w)
end SpectralBooks
end LinearAlgebra
end OAI
namespace OAI
namespace LinearAlgebra
namespace SpectralBooks
open HyperbolicObstruction
namespace Fermion
theorem truncatedIdentity : TruncatedIdentity :=
  truncatedIdentity_of_laurent laurentCrossingIdentity
end Fermion
universe u
variable {K : Type*} [Field K] {X : Type u} [MetricSpace X]
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

/-- Padding a tensor on `I` with a trivial leg at the new site `none`. -/
def padT {I : Type} (X : T I) : T (Option I) :=
  ⟨fun o => o.elim 1 X.1, fun z => X.2 (fun i => z (some i))⟩

theorem psi_padT_eq {I : Type} [Fintype I] [DecidableEq I]
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) ℂ → _ → Prop)) (X : T I) :
    psi ψ (padT X) = (ψ.val (ofRaw ((sigRaw X).group some)) : ℝ) := by
  classical
  haveI hempty : IsEmpty {j : I // some j = (none : Option I)} := ⟨fun j => by cases j.2⟩
  let huniq : ∀ i : I, Unique {j : I // some j = some i} := fun i =>
    ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext (Option.some_injective _ j.2)⟩
  apply psi_eq_of_equiv ψ (R := (sigRaw X).group some) (S := padT X)
    (fun o => match o with
      | none => @Equiv.ofUnique _ (Fin 1) (Pi.uniqueOfIsEmpty _) inferInstance
      | some i => @Equiv.piUnique _ (huniq i) (fun j => Fin (X.1 j.1)))
  intro x
  rfl

theorem ofRaw_sigRaw_toSig {I : Type} [Fintype I] (R : Raw.{0} I ℂ) :
    ofRaw (sigRaw (toSig R)) = ofRaw R :=
  (ofRaw_eq_iff.mpr (Raw.reindex_equivalent (X := R) (Y := sigRaw (toSig R))
    (fun i => Fintype.equivFin _)
    (fun x => congrArg _ (funext fun i => ((Fintype.equivFin _).symm_apply_apply (x i)).symm)))).symm

theorem logb_psi_maskSig {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} V ℂ → _ → Prop)) (S : Finset V)
    (hS : S.Nonempty) :
    Real.logb 2 (psi φ (maskSig S)) = Real.logb 2 (φ.val (ofRaw (Raw.maskDiagonal ℂ S (Fin 2))) : ℝ) := by
  rw [← mask_le (psi φ) (psi_mono φ) S hS, psi_toSig]

end OMAPort

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

theorem OMA.solution : OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H2_R1.H4 := by
  intro hfacts J _ _ Φ a b c e hP hv
  classical
  obtain ⟨hInt, hSync⟩ := hfacts
  -- OpenAI's spectral interval lemma, from the first fact
  have hint : SiteTensor.IntervalProp (K := ℂ) := by
    intro I' _ _ φ a' b' la lb hla hlb hsum
    have hS := OMAPort.SP_psi φ
    obtain ⟨Ψ, hPΨ, hpad, hwa, hwb⟩ := hInt I' (OMAPort.psi φ)
      ⟨hS.h0, hS.h1, hS.hz, hS.hmono, hS.hmul, hS.hadd⟩ a' b' la lb hla hlb
      (hsum.trans (OMAPort.logb_psi_wire φ a' b').symm)
    obtain ⟨g0, g1, gz, gm, gmul, gadd⟩ := hPΨ
    have hSΨ : OMAPort.SP Ψ := ⟨g0, g1, gz, gm, gmul, gadd⟩
    let ψ := OMAPort.fwd hSΨ
    have hpsi : OMAPort.psi ψ = Ψ := OMAPort.psi_fwd hSΨ
    refine ⟨ψ, fun R => ?_, ?_, ?_⟩
    · have hc : ofRaw (R.group some) = ofRaw ((OMAPort.sigRaw (OMAPort.toSig R)).group some) := by
        rw [← groupClass_ofRaw, ← groupClass_ofRaw, OMAPort.ofRaw_sigRaw_toSig]
      have h1 : (ψ.val (ofRaw (R.group some)) : ℝ) = φ.val (ofRaw R) := by
        rw [hc, ← OMAPort.psi_padT_eq, hpsi]
        have := hpad (OMAPort.toSig R)
        change Ψ (OMAPort.padT (OMAPort.toSig R)) = OMAPort.psi φ (OMAPort.toSig R) at this
        rw [this, OMAPort.psi_toSig]
      simp only [rawLogPrice, h1]
    · rw [← OMAPort.logb_psi_wire ψ none (some a'), hpsi]; exact hwa
    · rw [← OMAPort.logb_psi_wire ψ none (some b'), hpsi]; exact hwb
  -- synchronization, from the second fact (any scale c ≥ 0)
  have hsync : ∀ (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} (Fin 6) ℂ → _ → Prop))
      (c : ℝ), 0 ≤ c → ∀ a b a' b' z w : Fin 6, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      let d := SiteTensor.rawWireDistance φ c
      d a z = u * d a b → d z b = (1-u) * d a b →
      d a' w = u * d a' b' → d w b' = (1-u) * d a' b' →
      d z w ≤ (1-u) * d a a' + u * d b b' := by
    intro φ c hc a1 b1 a1' b1' z1 w1 u hu
    have hS := OMAPort.SP_psi φ
    have hscale : ∀ s t : Fin 6, SiteTensor.rawWireDistance φ c s t =
        c * Real.logb 2 (OMAPort.psi φ (OMAPort.wireT s t)) := by
      intro s t
      rw [OMAPort.logb_psi_wire φ s t]
      simp only [rawWireDistance, rawLogPrice, one_mul]
    simp only [hscale]
    intro h1 h2 h3 h4
    rcases hc.eq_or_lt with hc0 | hcpos
    · subst hc0; simp
    let L := fun s t : Fin 6 => Real.logb 2 (OMAPort.psi φ (OMAPort.wireT s t))
    have k1 : L a1 z1 = u * L a1 b1 := mul_left_cancel₀ hcpos.ne' (by rw [h1]; ring)
    have k2 : L z1 b1 = (1-u) * L a1 b1 := mul_left_cancel₀ hcpos.ne' (by rw [h2]; ring)
    have k3 : L a1' w1 = u * L a1' b1' := mul_left_cancel₀ hcpos.ne' (by rw [h3]; ring)
    have k4 : L w1 b1' = (1-u) * L a1' b1' := mul_left_cancel₀ hcpos.ne' (by rw [h4]; ring)
    have key : L z1 w1 ≤ (1-u) * L a1 a1' + u * L b1 b1' := hSync (Fin 6) (OMAPort.psi φ) ⟨hS.h0, hS.h1, hS.hz, hS.hmono, hS.hmul, hS.hadd⟩
      a1 b1 a1' b1' z1 w1 u hu.1 hu.2 k1 k2 k3 k4
    simp only [L] at key
    have := mul_le_mul_of_nonneg_left key hcpos.le
    exact this.trans (le_of_eq (by ring))
  -- the coordinate spectral point and its realization
  obtain ⟨h0, h1, hz, hm, hmul, hadd⟩ := hP
  have hS : OMAPort.SP Φ := ⟨h0, h1, hz, hm, hmul, hadd⟩
  haveI := OMAPort.nonempty_of_SP hS
  let φ := OMAPort.fwd hS
  obtain ⟨Y, _, Q, p, _, hgeo, hdist, -⟩ :=
    (SpectralPlacementPrices.exists_finite_midpoint_extension hint).realize_point φ 1 zero_le_one
  have hX := Q.catZero_of_asymptoticFactorizations hgeo
    (Fermion.asymptoticFactorizations_of_truncated Fermion.truncatedIdentity ℂ) hsync
  have hw : ∀ s t, Real.logb 2 (Φ (OMAPort.wireT s t)) = dist (p s) (p t) := fun s t =>
    (OMAPort.logb_wire_fwd hS s t).trans (hdist s t).symm
  have hbad : max (dist (p a) (p c) + dist (p b) (p e)) (dist (p a) (p e) + dist (p b) (p c)) <
      dist (p a) (p b) + dist (p c) (p e) := by
    rw [← hw, ← hw, ← hw, ← hw, ← hw, ← hw]
    exact hv
  obtain ⟨Q2⟩ := spectralPlane_of_fourPointDefect Q hX (p a) (p b) (p c) (p e) hbad
  have pairF : ∀ p q : EuclideanSpace ℝ (Fin 2), Q2.diagonal {p, q} = dist p q := fun p q => by
    convert Q2.diagonal_pair p q
  refine ⟨Q2.diagonal, Q2.diagonal_mono, pairF, ?_⟩
  intro I _ _ _ x
  obtain ⟨φ', c', hc', hd⟩ := Q2.exists_point_diagonal_map x
  have hS' := OMAPort.SP_psi φ'
  refine ⟨OMAPort.psi φ', ⟨hS'.h0, hS'.h1, hS'.hz, hS'.hmono, hS'.hmul, hS'.hadd⟩, fun S hSn => ?_⟩
  have huniv : Real.logb 2 (φ'.val (ofRaw (Raw.maskDiagonal ℂ (Finset.univ : Finset I) (Fin 2))) : ℝ) = 1 := by
    rw [ofRaw_maskDiagonal_univ, ofRaw_diagonal_fin_eq_natCast]
    have hv2 := map_natCast (normalizedSpectrum.toRingHom φ') 2
    change φ'.val ((2 : ℕ) : TensorClass.{0} I ℂ) = ((2 : ℕ) : NNReal) at hv2
    rw [hv2]
    norm_num
  have hcu : Q2.diagonal (Finset.univ.map x) = c' := by
    rw [hd Finset.univ Finset.univ_nonempty, huniv, mul_one]
  have hpos : 0 < c' := by
    obtain ⟨i, j, hij⟩ := exists_pair_ne I
    have hsub : ({x i, x j} : Finset (EuclideanSpace ℝ (Fin 2))) ⊆ Finset.univ.map x := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp
    have := Q2.diagonal_mono hsub
    rw [pairF, hcu] at this
    exact lt_of_lt_of_le (dist_pos.mpr (x.injective.ne hij)) this
  change Real.logb 2 (OMAPort.psi φ' (OMAPort.maskSig S)) = _
  rw [OMAPort.logb_psi_maskSig φ' S hSn, ← Finset.map_eq_image, ← Finset.map_eq_image, hcu,
    hd S hSn]
  field_simp

