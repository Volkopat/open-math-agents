import OMAStatements.S_arxiv_2606_14687
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.LinearCombination
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

 /-!
# Counterexample to Dmitriy Kunisky's Conjecture 1.19 (arXiv:2606.14687)

With spike strength two, realified Hermitian noise forces the phase
coordinate of the oriented leading eigenvector to vanish identically.
The unique reduced-dual optimizer predicts strictly positive variance
in that coordinate. Ordinary real symmetric Gaussian noise fills the
remaining dimensions and preserves convergence of the predicted variance.
-/
namespace SpikeGOE
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficients of a full real GOE, embedded in complex matrices. Summing over
all *ordered* pairs makes the diagonal variance exactly twice the off-diagonal
variance. A common scalar rescaling gives any desired noise level. -/
def goeEdge (i j : ι) : Matrix ι ι ℂ :=
  Matrix.single i j 1 + Matrix.single j i 1

private theorem goe_sandwich_expansion (i j : ι) (S : Matrix ι ι ℂ) :
    goeEdge i j * S * goeEdge i j =
      (Matrix.single i j (S j i) + Matrix.single i i (S j j)) +
      (Matrix.single j i (S i j) + Matrix.single j j (S i i)) := by
  simp [goeEdge, add_mul, mul_add, Matrix.single_mul_mul_single, add_assoc, add_comm, add_left_comm]

/-- The full GOE covariance formula, for any complex test matrix. -/
theorem goe_covariance_formula (S : Matrix ι ι ℂ) :
    (∑ i, ∑ j, goeEdge i j * S * goeEdge i j) =
      (2 : ℂ) • (S.transpose + Matrix.diagonal (fun _ : ι => S.trace)) := by
  classical
  simp_rw [goe_sandwich_expansion]
  ext a b
  by_cases e : a = b
  · subst b
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_add_distrib,
      Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.transpose_apply]
    ring
  · have hd (i : ι) : ¬ (i = a ∧ i = b) := fun h => e (h.1.symm.trans h.2)
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_add_distrib,
      Matrix.smul_apply, Matrix.transpose_apply, e, hd]
    ring

end SpikeGOE

/-!
Realification of Hermitian noise gives an exactly vanishing eigenvector
coordinate. The proof uses the skew-symmetric matrix representing
multiplication by i, and applies to every realization.
-/
namespace SpikePhase
open Matrix

variable {ι : Type*} [Fintype ι]

theorem skew_quadratic (J : Matrix ι ι ℝ) (hJ : J.transpose = -J)
    (u : ι → ℝ) : u ⬝ᵥ J.mulVec u = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec J u u
  rw [hJ, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

/-- Any eigenvector of the spiked matrix with nonzero signal overlap is
orthogonal to the phase direction Jv. No spectral gap is required. -/
theorem phase_coordinate_zero (J W : Matrix ι ι ℝ) (hJ : J.transpose = -J)
    (hW : W.transpose = W) (hJW : J * W = W * J)
    {θ eig : ℝ} (hθ : θ ≠ 0) (v w : ι → ℝ) (hov : v ⬝ᵥ w ≠ 0)
    (he : (θ • Matrix.vecMulVec v v + W).mulVec w = eig • w) :
    w ⬝ᵥ J.mulVec v = 0 := by
  have hJWskew : (J*W).transpose = -(J*W) := by
    rw [Matrix.transpose_mul, hJ, hW, Matrix.mul_neg, hJW]
  have hq := skew_quadratic (J*W) hJWskew w
  have hq' := skew_quadratic J hJ w
  have hact : (Matrix.vecMulVec v v).mulVec w = (v ⬝ᵥ w) • v := by
    ext i
    simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_comm, mul_left_comm]
  have hb := congrArg (fun x => w ⬝ᵥ (J.mulVec x)) he
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, hact, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct_smul, hq, add_zero, Matrix.mulVec_smul,
    dotProduct_smul, hq', smul_zero] at hb
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hθ)).resolve_left hov

variable [DecidableEq ι]

noncomputable def phase : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks 0 (-1) 1 0

noncomputable def realBlock (A B : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks A (-B) B A

omit [Fintype ι] in
theorem phase_skew : (phase (ι := ι)).transpose = -(phase (ι := ι)) := by
  ext i j
  cases i <;> cases j <;> simp [phase, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

omit [Fintype ι] [DecidableEq ι] in
theorem block_symmetric (A B : Matrix ι ι ℝ) (hA : A.transpose = A)
    (hB : B.transpose = -B) : (realBlock A B).transpose = realBlock A B := by
  simp [realBlock, Matrix.fromBlocks_transpose, hA, hB]

theorem block_commutes (A B : Matrix ι ι ℝ) :
    phase * realBlock A B = realBlock A B * phase := by
  simp [phase, realBlock, Matrix.fromBlocks_multiply]

theorem realBlock_phase_zero (A B : Matrix ι ι ℝ) (hA : A.transpose = A)
    (hB : B.transpose = -B) {θ eig : ℝ} (hθ : θ ≠ 0) (v w : ι ⊕ ι → ℝ)
    (hov : v ⬝ᵥ w ≠ 0)
    (he : (θ • Matrix.vecMulVec v v + realBlock A B).mulVec w = eig • w) :
    w ⬝ᵥ (phase.mulVec v) = 0 :=
  phase_coordinate_zero phase (realBlock A B) phase_skew (block_symmetric A B hA hB)
    (block_commutes A B) hθ v w hov he

end SpikePhase

/-!
The variance transition matrix of the realification of normalized complex GUE
has weights 2/d on the diagonal, zero on the paired phase coordinate and 1/d
elsewhere. Two transitions spread mass to every direction.
-/
namespace SpikePhase
open Finset
variable {ι : Type*} [Fintype ι]

noncomputable def transition (e : ι ≃ ι) (s : ι → ℝ) (i : ι) : ℝ :=
  ((∑ j, s j) + s i - s (e i)) / (Fintype.card ι : ℝ)

theorem transition_nonneg (e : ι ≃ ι) {s : ι → ℝ} (hs : ∀ i, 0 ≤ s i) (i : ι) :
    0 ≤ transition e s i := by
  have h : s (e i) ≤ ∑ j, s j := single_le_sum (fun j _ => hs j) (mem_univ _)
  exact div_nonneg (by linarith [hs i]) (Nat.cast_nonneg _)

theorem transition_mono (e : ι ≃ ι) {s t : ι → ℝ} (hst : ∀ i, s i ≤ t i) (i : ι) :
    transition e s i ≤ transition e t i := by
  have hh := transition_nonneg e (s := fun j => t j - s j) (fun j => sub_nonneg.mpr (hst j)) i
  unfold transition at *
  rw [Finset.sum_sub_distrib] at hh
  linarith only [show 0 ≤
    (((∑ j, t j) + t i - t (e i)) / (Fintype.card ι : ℝ) -
    ((∑ j, s j) + s i - s (e i)) / (Fintype.card ι : ℝ)) by
      convert hh using 1; ring]

theorem transition_smul (e : ι ≃ ι) (c : ℝ) (s : ι → ℝ) (i : ι) :
    transition e (fun j => c*s j) i = c * transition e s i := by
  simp only [transition, ← Finset.mul_sum]
  ring

theorem transition_sum [Nonempty ι] (e : ι ≃ ι) (s : ι → ℝ) :
    ∑ i, transition e s i = ∑ i, s i := by
  simp only [transition, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, e.sum_comp]
  field_simp
  ring

theorem variance_lower [Nonempty ι] (e : ι ≃ ι) (he : ∀ i, e (e i) = i)
    (hd : 4 ≤ Fintype.card ι) (s z : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hsum : ∑ i, s i = 1) (c : ℝ) (hc : 0 ≤ c) (hz : ∀ i, c ≤ z i)
    (hfix : ∀ i, s i = (z i)^2 * transition e s i) (i : ι) :
    c^4 / 2 ≤ (Fintype.card ι : ℝ) * s i := by
  let d : ℝ := Fintype.card ι
  have hd' : 4 ≤ d := by dsimp [d]; exact_mod_cast hd
  have hdpos : 0 < d := by linarith
  have hstep j : c^2 * transition e s j ≤ s j := by
    rw [hfix j]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc (hz j) 2) (transition_nonneg e hs _)
  have htwo : c^4 * transition e (transition e s) i ≤ s i := by
    have hm := transition_mono e hstep i
    rw [transition_smul] at hm
    calc _ = c^2 * (c^2 * transition e (transition e s) i) := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left hm (sq_nonneg c)).trans (hstep i)
  have hu : s (e i) ≤ 1 := hsum ▸ single_le_sum (fun j _ => hs j) (mem_univ (e i))
  have h : 1 / (2*d) ≤ transition e (transition e s) i := by
    unfold transition
    rw [show (∑ j, ((∑ k, s k) + s j - s (e j)) / (Fintype.card ι : ℝ)) = ∑ j, s j
      from transition_sum e s, hsum, he]
    change 1 / (2*d) ≤ (1 + (1 + s i - s (e i))/d - (1 + s (e i)-s i)/d)/d
    field_simp
    nlinarith [hs i]
  have endbound := (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ c^4)).trans htwo
  have h' : c^4 / (2*d) ≤ s i := by simpa only [div_eq_mul_inv, one_mul] using endbound
  rw [div_le_iff₀ (by positivity)] at h'
  change c^4 / 2 ≤ d * s i
  linarith

end SpikePhase

/-!
A diagonal certificate for a complex block semidefinite constraint, including
the equality case. The competitors can have arbitrary complex entries.
-/
namespace SpikePhase
open Matrix
open scoped ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
theorem gram_diagonal (M : Matrix κ κ ℂ) (G : Matrix κ ι ℂ) (i : ι) :
    (G.conjTranspose * M * G) i i = star (G.col i) ⬝ᵥ M.mulVec (G.col i) := by
  rw [Matrix.mul_assoc]
  rfl

theorem weighted_gram_nonneg (M : Matrix κ κ ℂ) (hM : M.PosSemidef)
    (G : Matrix κ ι ℂ) (z : ι → ℝ) (hz : ∀ i, 0 < z i) :
    0 ≤ ∑ i, ((G.conjTranspose * M * G) i i).re / z i := by
  apply Finset.sum_nonneg
  intro i _
  rw [gram_diagonal]
  exact div_nonneg (hM.re_dotProduct_nonneg _) (hz i).le

theorem mul_eq_zero_of_weighted_gram_zero (M : Matrix κ κ ℂ) (hM : M.PosSemidef)
    (G : Matrix κ ι ℂ) (z : ι → ℝ) (hz : ∀ i, 0 < z i)
    (he : (∑ i, ((G.conjTranspose * M * G) i i).re / z i) = 0) : M*G = 0 := by
  have hn i : 0 ≤ ((G.conjTranspose * M * G) i i).re / z i := by
    rw [gram_diagonal]
    exact div_nonneg (hM.re_dotProduct_nonneg _) (hz i).le
  have hd := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp he
  ext j i
  have hr := (div_eq_zero_iff.mp (hd i (Finset.mem_univ _))).resolve_right (hz i).ne'
  rw [gram_diagonal] at hr
  have hi := (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg (G.col i))).2
  have hk := (hM.dotProduct_mulVec_zero_iff (G.col i)).mp (Complex.ext hr hi.symm)
  exact congrFun hk j

variable [DecidableEq ι]

noncomputable def graphColumns (z : ι → ℝ) : Matrix (ι ⊕ ι) ι ℂ :=
  fromRows 1 (diagonal (fun i => (z i : ℂ)))

theorem graph_gram_diag (U T H : Matrix ι ι ℂ) (z : ι → ℝ) (i : ι) :
    let G := graphColumns z
    let M := fromBlocks U (-T) (-T.conjTranspose) H
    ((G.conjTranspose * M * G) i i).re =
      (U i i).re - 2 * z i * (T i i).re + (z i)^2 * (H i i).re := by
  dsimp only
  rw [Matrix.mul_assoc, graphColumns, Matrix.fromBlocks_mul_fromRows,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_conjTranspose,
    Matrix.conjTranspose_apply, Complex.mul_re]
  ring

theorem block_dual_inequality (U T H : Matrix ι ι ℂ)
    (hM : (fromBlocks U (-T) (-T.conjTranspose) H).PosSemidef)
    (z : ι → ℝ) (hz : ∀ i, 0 < z i) :
    2 * ∑ i, (T i i).re ≤ ∑ i, ((U i i).re / z i + z i * (H i i).re) := by
  have h := weighted_gram_nonneg _ hM (graphColumns z) z hz
  have ex i : (((graphColumns z).conjTranspose * fromBlocks U (-T) (-T.conjTranspose) H *
        graphColumns z) i i).re / z i =
      (U i i).re / z i + z i * (H i i).re - 2 * (T i i).re := by
    rw [graph_gram_diag]
    field_simp [(hz i).ne']
    ring
  simp only [ex, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  linarith

theorem fixed_of_block_dual_equality (U T H : Matrix ι ι ℂ)
    (hM : (fromBlocks U (-T) (-T.conjTranspose) H).PosSemidef) (hH : H.IsHermitian)
    (z : ι → ℝ) (hz : ∀ i, 0 < z i)
    (sat : 2 * ∑ i, (T i i).re = ∑ i, ((U i i).re / z i + z i * (H i i).re)) :
    let Z := diagonal (fun i => (z i : ℂ))
    U = Z*H*Z := by
  let Z := diagonal (fun i => (z i : ℂ))
  let M := fromBlocks U (-T) (-T.conjTranspose) H
  have ex i : (((graphColumns z).conjTranspose * M * graphColumns z) i i).re / z i =
      (U i i).re / z i + z i * (H i i).re - 2*(T i i).re := by
    dsimp only [M]
    rw [graph_gram_diag]
    field_simp [(hz i).ne']
    ring
  have hzsum : (∑ i, (((graphColumns z).conjTranspose * M * graphColumns z) i i).re / z i) = 0 := by
    simp only [ex, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have h := mul_eq_zero_of_weighted_gram_zero M hM (graphColumns z) z hz hzsum
  change fromBlocks U (-T) (-T.conjTranspose) H * fromRows 1 Z = 0 at h
  rw [fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.mul_one, Matrix.neg_mul] at h
  have top : U = T*Z := by
    ext i j
    have hi := congrArg (fun K : Matrix (ι ⊕ ι) ι ℂ => K (Sum.inl i) j) h
    change U i j + -((T*Z) i j) = 0 at hi
    exact sub_eq_zero.mp hi
  have bot : T.conjTranspose = H*Z := by
    ext i j
    have hi := congrArg (fun K : Matrix (ι ⊕ ι) ι ℂ => K (Sum.inr i) j) h
    change -(T.conjTranspose i j) + (H*Z) i j = 0 at hi
    exact (neg_add_eq_zero.mp hi)
  have hZ : Z.conjTranspose = Z := by
    dsimp [Z]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have ht := congrArg Matrix.conjTranspose bot
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, hZ, hH.eq] at ht
  exact top.trans (congrArg (fun B => B * Z) ht)

end SpikePhase

namespace SpikePhase
open Matrix OMA.S_arxiv_2606_14687 MeasureTheory

/-- Exactly the projected centered eigenvector appearing in the candidate
statement, with the phase vector as the test direction. -/
theorem centered_phase_eq_zero {d : ℕ} (J W : Mat d) (v w : Vec d)
    (hJ : J.transpose = -J) (hW : W.transpose = W) (hc : J*W = W*J)
    {θ : ℝ} (hθ : θ ≠ 0) (a : ℝ)
    (hw : isTopUnitVector (θ • projector v + W) w) (hov : 0 < realDot w v) :
    realDot (J.mulVec v) (w - a • v) = 0 := by
  obtain ⟨_, eig, he, _⟩ := hw
  have hp : v ⬝ᵥ w ≠ 0 := by
    rw [dotProduct_comm]
    exact hov.ne'
  have he' : (θ • Matrix.vecMulVec v v + W).mulVec w = eig • w := he
  have hz := phase_coordinate_zero J W hJ hW hc hθ v w hp he'
  change (J.mulVec v) ⬝ᵥ (w - a • v) = 0
  rw [dotProduct_sub, dotProduct_smul, dotProduct_comm (J.mulVec v) w, hz,
    dotProduct_comm (J.mulVec v) v, skew_quadratic J hJ v, smul_zero, sub_self]

/-- The characteristic function in this direction equals one for each
dimension and each deterministic scaling of a phase-symmetric model. -/
theorem phase_characteristic_eq_one {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : Mat d) (v : Vec d)
    (W : Ω → Mat d) (w : Ω → Vec d) (hJ : J.transpose = -J)
    {θ : ℝ} (hθ : θ ≠ 0) (scale a : ℝ)
    (hw : ∀ᵐ g ∂μ, (W g).transpose = W g ∧ J * W g = W g * J ∧
      isTopUnitVector (θ • projector v + W g) (w g) ∧ 0 < realDot (w g) v) :
    (∫ g, Complex.exp (Complex.I *
      ((scale * realDot (J.mulVec v) (w g - a • v) : ℝ) : ℂ)) ∂μ) = 1 := by
  calc
    _ = ∫ _, (1 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with g hg
      obtain ⟨hs, hc, he, ho⟩ := hg
      rw [centered_phase_eq_zero J (W g) v (w g) hJ hs hc hθ a he ho]
      simp
    _ = _ := by simp

end SpikePhase


/-! A scalar variational construction of the dual certificate, valid for every
symmetric stochastic variance matrix whose two-step transition is positive. -/
namespace PhaseOptimizer
open Finset Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def mix (P : ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, P i j * x j

noncomputable def value (P : ι → ι → ℝ) (a : ι) (θ : ℝ) (x : ι → ℝ) : ℝ :=
  θ*x a + 2*∑ i, Real.sqrt (x i) * Real.sqrt (mix P x i)

theorem mix_nonneg {P : ι → ι → ℝ} (hP : ∀ i j, 0 ≤ P i j) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i : ι) : 0 ≤ mix P x i :=
  sum_nonneg fun j _ => mul_nonneg (hP i j) (hx j)

private theorem mix_scale (P : ι → ι → ℝ) (x : ι → ℝ) (t : ℝ) (i : ι) :
    mix P (fun j => t*x j) i = t * mix P x i := by
  simp only [mix, Finset.mul_sum, mul_left_comm]

theorem value_scale (P : ι → ι → ℝ) (a : ι) (θ t : ℝ) (ht : 0 ≤ t) (x : ι → ℝ) :
    value P a θ (fun i => t*x i) = t * value P a θ x := by
  unfold value
  simp only [mix_scale, Real.sqrt_mul ht, mul_assoc]
  have h (i : ι) : Real.sqrt t * (Real.sqrt (x i) * (Real.sqrt t * Real.sqrt (mix P x i))) =
      t*(Real.sqrt (x i)*Real.sqrt (mix P x i)) := by
    rw [← Real.mul_self_sqrt ht]; ring_nf
    simp [Real.mul_self_sqrt ht]
  simp only [h, ← Finset.mul_sum]
  ring

private theorem value_continuous (P : ι → ι → ℝ) (a : ι) (θ : ℝ) :
    Continuous (value P a θ) := by unfold value mix; fun_prop

/-- An optimizing probability vector dominates the objective on the entire
nonnegative cone after scaling by the mass. -/
theorem cone_bound (P : ι → ι → ℝ) (a : ι) (θ : ℝ) (s : ι → ℝ)
    (hm : ∀ x ∈ stdSimplex ℝ ι, value P a θ x ≤ value P a θ s)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hn : 0 < ∑ i, x i) :
    value P a θ x ≤ (∑ i, x i) * value P a θ s := by
  let t := ∑ i, x i
  have ht : 0 < t := hn
  have hs : (fun i => t⁻¹ * x i) ∈ stdSimplex ℝ ι := by
    refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht.le) (hx i), ?_⟩
    rw [← mul_sum]
    exact inv_mul_cancel₀ ht.ne'
  have h := hm _ hs
  rw [value_scale P a θ _ (inv_nonneg.mpr ht.le)] at h
  calc
    _ = t*(t⁻¹*value P a θ x) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h ht.le

private def delta (i j : ι) : ℝ := if i=j then 1 else 0

private theorem delta_nonneg (i j : ι) : 0 ≤ delta i j := by unfold delta; split <;> norm_num

private theorem mix_add_atom (P : ι → ι → ℝ) (s : ι → ℝ) (i : ι) (t : ℝ) (j : ι) :
    mix P (fun k => s k+t*delta i k) j = mix P s j+t*P j i := by
  classical
  simp only [mix, mul_add, sum_add_distrib, delta, mul_ite, mul_one, mul_zero,
    ← ite_and, sum_ite_eq, mem_univ, if_true]
  simp [mul_comm]

private theorem total_add_atom (s : ι → ℝ) (hs : ∑ i, s i=1) (i : ι) (t : ℝ) :
    (∑ k, (s k+t*delta i k))=1+t := by
  simp [delta, sum_add_distrib, mul_ite, hs]

theorem zero_support_closed {P : ι → ι → ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (a : ι) {θ : ℝ} (hθ : 0 ≤ θ) {s : ι → ℝ} (hs : s ∈ stdSimplex ℝ ι)
    (hm : ∀ x ∈ stdSimplex ℝ ι, value P a θ x ≤ value P a θ s)
    (i : ι) (hi : s i = 0) : mix P s i = 0 := by
  have ps := mix_nonneg hP hs.1
  by_contra hn
  have hp : 0 < mix P s i := lt_of_le_of_ne (ps i) (Ne.symm hn)
  let c := value P a θ s
  have hc : 0 ≤ c := add_nonneg (mul_nonneg hθ (hs.1 a))
    (mul_nonneg (by norm_num) (sum_nonneg fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  let t := mix P s i / (c+1)^2
  have hcp : 0 < c+1 := by linarith
  have ht : 0 < t := div_pos hp (sq_pos_of_pos hcp)
  let x := fun k => s k+t*delta i k
  have hx j : s j ≤ x j := by dsimp [x]; linarith [mul_nonneg ht.le (delta_nonneg i j)]
  have hq j : mix P s j ≤ mix P x j := by
    change _ ≤ mix P (fun k => s k+t*delta i k) j
    rw [mix_add_atom]
    linarith [mul_nonneg ht.le (hP j i)]
  have hxsum : ∑ j, x j = 1+t := total_add_atom s hs.2 i t
  have upper := cone_bound P a θ s hm x (fun j => (hs.1 j).trans (hx j))
    (by rw [hxsum]; linarith)
  rw [hxsum] at upper
  let f := fun j => Real.sqrt (s j) * Real.sqrt (mix P s j)
  let g := fun j => Real.sqrt (x j) * Real.sqrt (mix P x j)
  have single : g i-f i ≤ ∑ j, (g j-f j) := by
    apply single_le_sum (fun j _ => sub_nonneg.mpr
      (mul_le_mul (Real.sqrt_le_sqrt (hx j)) (Real.sqrt_le_sqrt (hq j))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (mem_univ i)
  have hxi : x i=t := by simp [x, delta, hi]
  have single' : Real.sqrt t*Real.sqrt (mix P s i) ≤ (∑ j, g j) - ∑ j, f j := by
    rw [sum_sub_distrib] at single
    dsimp only [g,f] at single ⊢
    rw [hi, Real.sqrt_zero, zero_mul, sub_zero, hxi] at single
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hq i)) (Real.sqrt_nonneg t)).trans single
  have lower : value P a θ s + 2*(Real.sqrt t*Real.sqrt (mix P s i)) ≤ value P a θ x := by
    change θ*s a + 2*(∑ j, f j) + _ ≤ θ*x a + 2*(∑ j, g j)
    linarith [mul_le_mul_of_nonneg_left (hx a) hθ]
  have h := lower.trans upper
  change c + 2*(Real.sqrt t*Real.sqrt (mix P s i)) ≤ (1+t)*c at h
  have hsqrt : Real.sqrt t = Real.sqrt (mix P s i)/(c+1) := by
    simp [t, Real.sqrt_div hp.le, Real.sqrt_sq_eq_abs, abs_of_pos hcp]
  rw [hsqrt] at h
  have hh : (Real.sqrt (mix P s i)/(c+1))*Real.sqrt (mix P s i) = mix P s i/(c+1) := by
    rw [div_mul_eq_mul_div, Real.mul_self_sqrt hp.le]
  rw [hh] at h
  dsimp only [t] at h
  field_simp at h
  nlinarith [mul_pos hp hcp]

/-- Positivity reaches every coordinate whenever two transitions connect any
pair. The diagonal entries of P ensure the square roots are differentiable. -/
theorem max_positive {P : ι → ι → ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hTwo : ∀ i j, ∃ k, 0 < P i k ∧ 0 < P k j)
    (a : ι) {θ : ℝ} (hθ : 0 ≤ θ) {s : ι → ℝ} (hs : s ∈ stdSimplex ℝ ι)
    (hm : ∀ x ∈ stdSimplex ℝ ι, value P a θ x ≤ value P a θ s) :
    ∀ i, 0 < s i := by
  have next {i j : ι} (hsi : s i = 0) (hij : 0 < P i j) : s j=0 := by
    have h := zero_support_closed hP a hθ hs hm i hsi
    exact (mul_eq_zero.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hP i k) (hs.1 k))).mp h j (mem_univ _))).resolve_left hij.ne'
  intro i
  by_contra hn
  have hi := le_antisymm (le_of_not_gt hn) (hs.1 i)
  have hall j : s j=0 := by
    obtain ⟨k,hik,hkj⟩ := hTwo i j
    exact next (next hi hik) hkj
  have := hs.2
  simp [hall] at this


noncomputable def weight (P : ι → ι → ℝ) (s : ι → ℝ) (i : ι) :=
  Real.sqrt (s i) / Real.sqrt (mix P s i)

private theorem affine_deriv (u v : ℝ) : HasDerivAt (fun t : ℝ => u+t*v) v 0 := by
  simpa only [Pi.add_def, zero_add, one_mul, id_eq] using (hasDerivAt_const (0:ℝ) u).add ((hasDerivAt_id (0:ℝ)).mul_const v)

theorem stationary_coordinate {P : ι → ι → ℝ} (hP : ∀ j k, 0 ≤ P j k)
    (hSym : ∀ j k, P j k = P k j) (a : ι) (θ : ℝ) {s : ι → ℝ}
    (hs : s ∈ stdSimplex ℝ ι) (hp : ∀ j, 0 < s j) (hp' : ∀ j, 0 < mix P s j)
    (hm : ∀ x ∈ stdSimplex ℝ ι, value P a θ x ≤ value P a θ s) (i : ι) :
    value P a θ s = θ*delta i a+(weight P s i)⁻¹+mix P (weight P s) i := by
  let c := value P a θ s
  let z := weight P s
  let x := fun (t : ℝ) (j : ι) => s j+t*delta i j
  let g := fun (t : ℝ) j => Real.sqrt (s j+t*delta i j) * Real.sqrt (mix P s j+t*P j i)
  have val (t : ℝ) : value P a θ (x t) = θ*(s a+t*delta i a)+2*∑ j, g t j := by
    simp only [value, x, mix_add_atom, g]
  have hd j : HasDerivAt (fun t => g t j) ((delta i j / z j + z j*P j i)/2) 0 := by
    have h1 := (affine_deriv (s j) (delta i j)).sqrt (by simpa using (hp j).ne')
    have h2 := (affine_deriv (mix P s j) (P j i)).sqrt (by simpa using (hp' j).ne')
    convert h1.mul h2 using 1
    all_goals try rfl
    change (delta i j/(Real.sqrt (s j)/Real.sqrt (mix P s j)) + Real.sqrt (s j)/Real.sqrt (mix P s j)*P j i)/2 = _
    simp only [zero_mul, add_zero]
    field_simp [(Real.sqrt_pos.mpr (hp j)).ne', (Real.sqrt_pos.mpr (hp' j)).ne']
    <;> ring
  have hdv := ((affine_deriv (s a) (delta i a)).const_mul θ).add
    ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)).const_mul 2)
  have hc := hdv.sub ((affine_deriv 1 1).mul_const c)
  let obj := fun t => value P a θ (x t) - (1+t)*c
  have hloc : IsLocalMax obj 0 := by
    filter_upwards [Ioi_mem_nhds (show -s i < 0 by linarith [hp i]),
      Ioi_mem_nhds (show (-1:ℝ)<0 by norm_num)] with t ht ht'
    have hn (j : ι) : 0 ≤ x t j := by
      by_cases e : i=j
      · subst j; simp [x,delta]; change -s i < t at ht; linarith
      · simpa [x,delta,e] using (hp j).le
    have total : ∑ j, x t j = 1+t := total_add_atom s hs.2 i t
    have h := cone_bound P a θ s hm _ hn (by rw [total]; change -1 < t at ht'; linarith)
    rw [total] at h
    change obj t ≤ obj 0
    simpa [obj, x, c] using sub_nonpos.mpr h
  have he := hloc.hasDerivAt_eq_zero
    (show HasDerivAt obj _ 0 by simpa only [obj, val, mul_one, one_mul, Pi.add_def, Pi.sub_def] using hc)
  have hs' : 2*(∑ j, (delta i j/z j + z j*P j i)/2) = (z i)⁻¹+mix P z i := by
    rw [mul_sum]
    calc
      _ = ∑ j, (delta i j/z j + z j*P j i) := by
        apply sum_congr rfl; intro j _; ring
      _ = _ := by
        rw [sum_add_distrib]
        simp only [delta, ite_div, zero_div, one_div, sum_ite_eq, mem_univ, if_true]
        congr 1
        exact sum_congr rfl fun j _ => by rw [hSym j i, mul_comm]
  change c = θ * delta i a + (z i)⁻¹ + mix P z i
  linarith only [he, hs']

/-- An interior optimizer, positive diagonal scaling, stationarity,
fixed-point identity, and a uniform bound on every diagonal scale. -/
theorem exists_certificate (P : ι → ι → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hSym : ∀ i j, P i j=P j i) (hrow : ∀ i, ∑ j, P i j=1)
    (hTwo : ∀ i j, ∃ k, 0<P i k ∧ 0<P k j) (a : ι) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ (s z : ι → ℝ) (c : ℝ), s ∈ stdSimplex ℝ ι ∧ (∀ i, 0<s i) ∧
      (∀ i, 0 < z i) ∧ (∀ i, s i=z i^2*mix P s i) ∧
      (∀ i, c=(if i=a then θ else 0)+(z i)⁻¹+mix P z i) ∧
      c≤θ+2 ∧ (∀ i, 1/(θ+2) ≤ z i) := by
  have hne : (stdSimplex ℝ ι).Nonempty := ⟨_, single_mem_stdSimplex ℝ a⟩
  obtain ⟨s,hs,hm⟩ := (isCompact_stdSimplex ℝ ι).exists_isMaxOn hne (value_continuous P a θ).continuousOn
  have H : ∀ x ∈ stdSimplex ℝ ι, value P a θ x ≤ value P a θ s := fun x hx => hm hx
  have hp := max_positive hP hTwo a hθ hs H
  have hmix (i : ι) : 0 < mix P s i := by
    obtain ⟨j,hj,_⟩ := hTwo i i
    exact (mul_pos hj (hp j)).trans_le (single_le_sum (fun k _ => mul_nonneg (hP i k) (hs.1 k)) (mem_univ j))
  let z := weight P s
  have hz i : 0<z i := div_pos (Real.sqrt_pos.mpr (hp i)) (Real.sqrt_pos.mpr (hmix i))
  have Hc i : value P a θ s = (if i=a then θ else 0)+(z i)⁻¹+mix P z i := by
    simpa [delta, mul_ite, z] using stationary_coordinate hP hSym a θ hs hp hmix H i
  have hc : value P a θ s ≤ θ+2 := by
    have total : ∑ i, mix P s i = 1 := by
      unfold mix
      rw [sum_comm]
      simpa only [← sum_mul, show ∀ j, ∑ i, P i j=1 from fun j => by
        simpa only [fun i => hSym i j] using hrow j, one_mul] using hs.2
    have hsum : 2*(∑ i, Real.sqrt (s i)*Real.sqrt (mix P s i)) ≤ 2 := by
      rw [mul_sum]
      calc
        _ ≤ ∑ i, (s i+mix P s i) := by
          apply sum_le_sum
          intro i _
          nlinarith [sq_nonneg (Real.sqrt (s i)-Real.sqrt (mix P s i)),
            Real.sq_sqrt (hs.1 i), Real.sq_sqrt (hmix i).le]
        _ = _ := by rw [sum_add_distrib, hs.2, total]; norm_num
    have hl := mul_le_mul_of_nonneg_left (mem_Icc_of_mem_stdSimplex hs a).2 hθ
    change θ*s a + _ ≤ _
    linarith
  refine ⟨s,z,_,hs,hp,hz,?_,Hc,hc,?_⟩
  · intro i
    dsimp [z,weight]
    rw [div_pow, Real.sq_sqrt (hp i).le, Real.sq_sqrt (hmix i).le,
      div_mul_cancel₀ _ (hmix i).ne']
  · intro i
    have hn := mix_nonneg hP (fun j => (hz j).le) i
    have ha : (0:ℝ) ≤ (if i=a then θ else 0) := by split <;> positivity
    have h : 1/z i ≤ θ+2 := by rw [one_div]; linarith [Hc i]
    rw [div_le_iff₀ (hz i)] at h
    rw [div_le_iff₀ (by linarith : 0<θ+2)]
    linarith only [show 1 ≤ z i*(θ+2) by simpa only [mul_comm] using h]

end PhaseOptimizer


namespace PhaseOptimizer
open Matrix Finset OMA.S_arxiv_2606_14687
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def diagReal (s : ι → ℝ) : Matrix ι ι ℂ := diagonal (fun i => (s i : ℂ))

private theorem diagReal_star (s : ι → ℝ) : (diagReal s).conjTranspose = diagReal s := by
  rw [diagReal, diagonal_conjTranspose]
  congr 1
  funext i
  simp

private theorem diagReal_mul (s z : ι → ℝ) :
    diagReal s*diagReal z = diagReal (fun i => s i*z i) := by
  simp [diagReal, diagonal_mul_diagonal]

private theorem weighted_mix (P : ι → ι → ℝ) (hSym : ∀ i j, P i j=P j i) (z u : ι → ℝ) :
    (∑ i, z i*mix P u i) = ∑ i, u i*mix P z i := by
  simp only [mix, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  rw [hSym j i]; ring

private theorem certificate_identity (P : ι → ι → ℝ) (hp : ∀ i j, P i j=P j i)
    (z u : ι → ℝ) (hu : ∑ i, u i=1) (a : ι) (θ c : ℝ)
    (h : ∀ i, c = (if i=a then θ else 0)+(z i)⁻¹+mix P z i) :
    (∑ i, (u i / z i + z i * mix P u i)) = c - θ*u a := by
  rw [sum_add_distrib, weighted_mix P hp]
  have he := sum_congr (s₁ := (univ : Finset ι)) rfl fun i _ => congrArg (u i * ·) (h i)
  simp only [mul_add, sum_add_distrib, ← sum_mul, hu, one_mul, mul_ite, mul_zero, sum_ite_eq',
    mem_univ, if_true, ← div_eq_mul_inv] at he
  linarith only [he]

private theorem diagonal_block_feasible (s z p : ι → ℝ) (hp : ∀ i, 0≤p i)
    (hs : ∀ i, s i=z i^2*p i) :
    (fromBlocks (diagReal s) (-(diagReal fun i => z i*p i))
      (-(diagReal fun i => z i*p i).conjTranspose) (diagReal p)).PosSemidef := by
  let f := fun i => z i*Real.sqrt (p i)
  let g := fun i => -Real.sqrt (p i)
  let B := fromRows (diagReal f) (diagReal g)
  have pB := posSemidef_self_mul_conjTranspose B
  have b : B*B.conjTranspose =
      fromBlocks (diagReal s) (-(diagReal fun i => z i*p i))
      (-(diagReal fun i => z i*p i).conjTranspose) (diagReal p) := by
    simp only [B, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols,
      diagReal_star, diagReal_mul]
    have hneg (x : ι → ℝ) : -(diagReal x) = diagReal (fun i => -x i) := by
      simp [diagReal, diagonal_neg]
    rw [hneg]
    congr 1 <;> apply congrArg diagReal <;> funext i <;> dsimp only [f,g]
    · rw [hs]; nlinarith [Real.sq_sqrt (hp i), show
        (z i*Real.sqrt (p i))*(z i*Real.sqrt (p i)) = z i^2*(Real.sqrt (p i))^2 by ring]
    · calc _ = -(z i*(Real.sqrt (p i))^2) := by ring
           _ = _ := by rw [Real.sq_sqrt (hp i)]
    · calc _ = -(z i*(Real.sqrt (p i))^2) := by ring
           _ = _ := by rw [Real.sq_sqrt (hp i)]
    · nlinarith [Real.sq_sqrt (hp i)]
  exact b ▸ pB

private theorem objective_eq {d : ℕ} (a : Fin d) (θ : ℝ) (U T : CMat d) :
    dualObjective (θ • projector (Pi.single a 1)) U T = θ*(U a a).re + 2*∑ i, (T i i).re := by
  have he : complexMatrix (θ • projector (Pi.single a 1)) = Matrix.single a a (θ:ℂ) := by
    ext i j
    by_cases ei:i=a <;> by_cases ej:j=a <;> simp_all [complexMatrix,projector,Matrix.smul_apply,
      Matrix.single_apply, Pi.single_apply, eq_comm]
  unfold dualObjective
  rw [he, Matrix.trace_single_mul]
  simp [Matrix.trace,Matrix.diag_apply,Complex.mul_re]

/-- Construct a diagonal optimizer for the project's full complex SDP and
characterize every optimizer by a single fixed-point equation. -/
theorem actual_dual_certificate_with_multiplier {d k : ℕ} (A : Fin k → Mat d) (P : Fin d → Fin d → ℝ)
    (hP : ∀ i j, 0≤P i j) (symm : ∀ i j, P i j=P j i) (row : ∀ i, ∑ j, P i j=1)
    (two : ∀ i j, ∃ l, 0<P i l ∧ 0<P l j)
    (preserve : ∀ s, covarianceMap A (diagReal s) = diagReal (mix P s))
    (readDiag : ∀ (U : CMat d) i, ((covarianceMap A U) i i).re = mix P (fun j => (U j j).re) i)
    (a : Fin d) {θ : ℝ} (hθ : 0≤θ) :
    ∃ s z : Fin d → ℝ, s ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, 0<s i) ∧
      (∀ i, 0<z i ∧ 1/(θ+2)≤z i) ∧ (∀ i, s i=(z i)^2*mix P s i) ∧
      (∃ c : ℝ, ∀ i, c=(if i=a then θ else 0)+(z i)⁻¹+mix P z i) ∧
      dualOptimizer (θ • projector (Pi.single a 1)) A (diagReal s) ∧
      (∀ U : CMat d, dualOptimizer (θ • projector (Pi.single a 1)) A U →
        U=diagReal z*covarianceMap A U*diagReal z) := by
  classical
  obtain ⟨s,z,c,hs,hpos,hz,hfix,hc,_,hmin⟩ := exists_certificate P hP symm row two a hθ
  let T := diagReal (fun i => z i*mix P s i)
  let S := diagReal s
  let M := θ • projector (show Vec d from Pi.single a 1)
  have hf : dualFeasible A S T := by
    refine ⟨?_,?_⟩
    · simpa [S,diagReal,Matrix.trace_diagonal,← Complex.ofReal_sum] using congrArg Complex.ofReal hs.2
    · change (fromBlocks (diagReal s) (-T) (-T.conjTranspose) _).PosSemidef
      rw [preserve]
      exact diagonal_block_feasible s z _ (mix_nonneg hP hs.1) hfix
  have vmax : dualObjective M S T = c := by
    rw [objective_eq]
    simp only [S,T,diagReal,diagonal_apply_eq,Complex.ofReal_re]
    have hid := certificate_identity P symm z s hs.2 a θ c hc
    have hr i : s i/z i = z i*mix P s i := by
      rw [div_eq_iff (hz i).ne',hfix]; ring
    simp only [hr, ← two_mul, ← mul_sum] at hid
    linarith
  have bound (U V : CMat d) (hu : dualFeasible A U V) :
      dualObjective M U V ≤ c ∧ (dualObjective M U V=c →
         U=diagReal z*covarianceMap A U*diagReal z) := by
    let u := fun i => (U i i).re
    have hsum : ∑ i, u i=1 := by
      simpa [u,Matrix.trace, Matrix.diag_apply] using congrArg Complex.re hu.1
    have hid := certificate_identity P symm z u hsum a θ c hc
    have hj := SpikePhase.block_dual_inequality U V (covarianceMap A U) hu.2 z hz
    rw [objective_eq]
    have he : (∑ i, ((U i i).re/z i+z i*((covarianceMap A U) i i).re))=c-θ*u a := by
      simpa only [readDiag,u] using hid
    constructor
    · rw [he] at hj
      change θ*u a + _ ≤ _
      linarith
    · intro hx
      have hHerm : (covarianceMap A U).IsHermitian := hu.2.isHermitian.submatrix (f := Sum.inr)
      apply SpikePhase.fixed_of_block_dual_equality U V (covarianceMap A U) hu.2 hHerm z hz
      rw [he]; change θ*u a + _ = c at hx; linarith
  refine ⟨s,z,hs,hpos,fun i => ⟨hz i,hmin i⟩,hfix,⟨c,hc⟩,⟨T,hf,?_⟩,?_⟩
  · intro U V hfe
    exact vmax ▸ (bound U V hfe).1
  · rintro U ⟨V,hu,H⟩
    apply (bound U V hu).2
    exact le_antisymm (bound U V hu).1 (vmax ▸ H S T hf)

theorem actual_dual_certificate {d k : ℕ} (A : Fin k → Mat d) (P : Fin d → Fin d → ℝ)
    (hP : ∀ i j, 0≤P i j) (symm : ∀ i j, P i j=P j i) (row : ∀ i, ∑ j, P i j=1)
    (two : ∀ i j, ∃ l, 0<P i l ∧ 0<P l j)
    (preserve : ∀ s, covarianceMap A (diagReal s) = diagReal (mix P s))
    (readDiag : ∀ (U : CMat d) i, ((covarianceMap A U) i i).re = mix P (fun j => (U j j).re) i)
    (a : Fin d) {θ : ℝ} (hθ : 0≤θ) :
    ∃ s z : Fin d → ℝ, s ∈ stdSimplex ℝ (Fin d) ∧ (∀ i, 0<s i) ∧
      (∀ i, 0<z i ∧ 1/(θ+2)≤z i) ∧ (∀ i, s i=(z i)^2*mix P s i) ∧
      dualOptimizer (θ • projector (Pi.single a 1)) A (diagReal s) ∧
      (∀ U : CMat d, dualOptimizer (θ • projector (Pi.single a 1)) A U →
        U=diagReal z*covarianceMap A U*diagReal z) := by
  obtain ⟨s,z,hs,hp,hz,hfix,_,ho,hu⟩ :=
    actual_dual_certificate_with_multiplier A P hP symm row two preserve readDiag a hθ
  exact ⟨s,z,hs,hp,hz,hfix,ho,hu⟩

end PhaseOptimizer


/-! Compute the covariance on arbitrary complex test matrices for the
realification of a Hermitian Gaussian ensemble, before normalization. -/
namespace SpikePhase.Cov
open Matrix Finset
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

def skewEdge {R : Type*} [Ring R] (i j : ι) : Matrix ι ι R := single i j 1 - single j i 1

def symEdge {R : Type*} [Ring R] (i j : ι) : Matrix ι ι R := single i j 1 + single j i 1

def realEdge {R : Type*} [Ring R] (i j : ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  fromBlocks (symEdge i j) 0 0 (symEdge i j)

def imagEdge {R : Type*} [Ring R] (i j : ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  fromBlocks 0 (-(skewEdge i j)) (skewEdge i j) 0

noncomputable def raw (U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :=
  (∑ i, ∑ j, realEdge i j*U*realEdge i j) + ∑ i, ∑ j, imagEdge i j*U*imagEdge i j

private theorem skew_sandwich (i j : ι) (S : Matrix ι ι ℂ) :
    skewEdge i j*S*skewEdge i j =
      (single i j (S j i) - single i i (S j j)) -
      (single j j (S i i) - single j i (S i j)) := by
  simp [skewEdge,sub_mul,mul_sub,Matrix.single_mul_mul_single]
  <;> abel

theorem skew_cov (S : Matrix ι ι ℂ) :
    (∑ i, ∑ j, skewEdge i j*S*skewEdge i j) =
      (2:ℂ) • (S.transpose - diagonal (fun _ : ι => S.trace)) := by
  simp_rw [skew_sandwich]
  ext a b
  by_cases e : a=b
  · subst b
    simp [Matrix.sum_apply,Matrix.single_apply,ite_and,sum_sub_distrib,Matrix.trace,
      Matrix.diag_apply,Matrix.smul_apply,Matrix.transpose_apply]
    ring
  · have hd (i : ι) : ¬(i=a ∧ i=b) := fun h => e (h.1.symm.trans h.2)
    simp [Matrix.sum_apply,Matrix.single_apply,ite_and,sum_sub_distrib,Matrix.smul_apply,
      Matrix.transpose_apply,e,hd]
    ring_nf
    simp [sum_add_distrib]
    <;> ring

private theorem block_sandwich (X Y V T : Matrix ι ι ℂ) (i j : ι) :
    let E := symEdge (R := ℂ) i j
    let K := skewEdge (R := ℂ) i j
    realEdge i j * fromBlocks X Y V T * realEdge i j =
      fromBlocks (E*X*E) (E*Y*E) (E*V*E) (E*T*E) ∧
    imagEdge i j * fromBlocks X Y V T * imagEdge i j =
      fromBlocks (-(K*T*K)) (K*V*K) (K*Y*K) (-(K*X*K)) := by
  simp [realEdge,imagEdge,fromBlocks_multiply]

private theorem sum_blocks {τ : Type*} [Fintype τ] (X Y V T : τ → Matrix ι ι ℂ) :
    (∑ j, fromBlocks (X j) (Y j) (V j) (T j)) =
    fromBlocks (∑ j, X j) (∑ j, Y j) (∑ j, V j) (∑ j, T j) := by
  ext (i|i) (j|j) <;> simp [Matrix.sum_apply]

noncomputable def plus (S : Matrix ι ι ℂ) := (2:ℂ) • (S.transpose + diagonal (fun _ : ι => S.trace))
noncomputable def minus (S : Matrix ι ι ℂ) := (2:ℂ) • (S.transpose - diagonal (fun _ : ι => S.trace))

theorem raw_blocks (X Y V T : Matrix ι ι ℂ) :
    raw (fromBlocks X Y V T) =
      fromBlocks (plus X-minus T) (plus Y+minus V) (plus V+minus Y) (plus T-minus X) := by
  unfold raw
  simp only [fun i j => (block_sandwich X Y V T i j).1,
    fun i j => (block_sandwich X Y V T i j).2, sum_blocks, sum_neg_distrib]
  have h (B : Matrix ι ι ℂ) :
      (∑ i, ∑ j, symEdge i j*B*symEdge i j) = plus B := SpikeGOE.goe_covariance_formula B
  simp only [h,skew_cov,minus,Matrix.fromBlocks_add,sub_eq_add_neg]

private def swap : ι ⊕ ι → ι ⊕ ι := Sum.elim Sum.inr Sum.inl

theorem raw_diagonal_entry (S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (a : ι ⊕ ι) :
    raw S a a = 2*(S.trace + S a a - S (swap a) (swap a)) := by
  rw [← fromBlocks_toBlocks S,raw_blocks]
  cases a <;> simp [plus,minus,swap,Matrix.trace,Matrix.diag_apply,Fintype.sum_sum_type,Matrix.smul_apply]
  <;> ring

theorem raw_diagonal (s : ι ⊕ ι → ℂ) :
    raw (diagonal s) = diagonal (fun a => 2*((∑ j,s j)+s a-s (swap a))) := by
  ext a b
  by_cases h : a=b
  · subst b
    simpa using raw_diagonal_entry (diagonal s) a
  · rw [← fromBlocks_toBlocks (diagonal s),raw_blocks]
    cases a <;> cases b <;> simp_all [plus,minus, Matrix.smul_apply,
      Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,
      Matrix.trace,Matrix.diag_apply,Matrix.diagonal,Matrix.submatrix_apply,eq_comm]
    <;> ring

end SpikePhase.Cov


namespace SpikePhase
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Variances of the entries of the real representation of normalized GUE.
f interchanges the real and imaginary coordinates in each complex component. -/
noncomputable def profile (f : ι ≃ ι) (i j : ι) : ℝ :=
  (1+(if i=j then 1 else 0)-(if f i=j then 1 else 0))/(Fintype.card ι:ℝ)

theorem profile_mix (f : ι ≃ ι) (u : ι → ℝ) :
    PhaseOptimizer.mix (profile f) u = transition f u := by
  funext i
  simp only [PhaseOptimizer.mix,profile,transition,div_mul_eq_mul_div,← sum_div,sub_mul,add_mul,
    one_mul,ite_mul,zero_mul,sum_sub_distrib,sum_add_distrib,sum_ite_eq,mem_univ,if_true]

theorem profile_stochastic [Nonempty ι] (f : ι ≃ ι) (i : ι) : ∑ j, profile f i j=1 := by
  have h := congrFun (profile_mix f (fun _ => 1)) i
  simpa [PhaseOptimizer.mix,transition, Nat.cast_ne_zero.mpr Fintype.card_ne_zero] using h

theorem profile_symmetric (f : ι ≃ ι) (hf : Function.Involutive f) (i j : ι) :
    profile f i j=profile f j i := by
  have he : f i=j ↔ f j=i := by
    constructor
    · intro h; rw [← h]; exact hf i
    · intro h; rw [← h]; exact hf j
  simp only [profile,he,show (j=i)=(i=j) from propext eq_comm]

theorem profile_nonneg (f : ι ≃ ι) (i j : ι) : 0 ≤ profile f i j := by
  unfold profile
  split <;> split <;> positivity

theorem profile_paths (f : ι ≃ ι) (hf : Function.Involutive f) (hd : 2<Fintype.card ι) (i j : ι) :
    ∃ k, 0<profile f i k ∧ 0<profile f k j := by
  have hd' : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast (by omega : 0<Fintype.card ι)
  have e : ({f i,f j} : Finset ι).card < (univ : Finset ι).card := by
    rw [card_univ]
    exact (card_le_two).trans_lt hd
  obtain ⟨k,_,h⟩ := exists_mem_notMem_of_card_lt_card e
  simp only [mem_insert,mem_singleton,not_or] at h
  have e₂ : f k ≠ j := by intro he; exact h.2 (by rw [← he, hf])
  refine ⟨k,?_,?_⟩
  · unfold profile; rw [if_neg (Ne.symm h.1)]; split <;> positivity
  · unfold profile; rw [if_neg e₂]; split <;> positivity

theorem distinguished_weights_differ (f : ι ≃ ι) (hf : Function.Involutive f)
    (a : ι) (ha : f a ≠ a) (θ c : ℝ) (hθ : θ ≠ 0) (z : ι → ℝ)
    (h : ∀ i, c=(if i=a then θ else 0)+(z i)⁻¹+PhaseOptimizer.mix (profile f) z i) :
    z a ≠ z (f a) := by
  intro e
  have he : transition f z a = transition f z (f a) := by
    simp only [transition, hf a]; rw [e]
  have h₁ := h a
  have h₂ := h (f a)
  rw [if_pos rfl,profile_mix,e,he] at h₁
  simp only [profile_mix,if_neg ha,zero_add] at h₂
  exact hθ (by linarith)

end SpikePhase


/-! Normalize the Hermitian coefficient family and identify its exact variance
operator on the diagonal, including diagonal entries of arbitrary test matrices. -/
namespace SpikePhase.Cov
open Matrix Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Directions (ι : Type*) := (ι × ι) ⊕ (ι × ι)

def coefficient {R : Type*} [Ring R] (u : Directions ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  u.elim (fun q => realEdge q.1 q.2) (fun q => imagEdge q.1 q.2)

noncomputable def scale (ι : Type*) [Fintype ι] : ℝ :=
  (Real.sqrt (2 * (Fintype.card (ι ⊕ ι) : ℝ)))⁻¹

noncomputable def gaussianCoefficient (u : Directions ι) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  scale ι • coefficient u

noncomputable def noiseCov (U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :=
  ∑ j : Directions ι, (gaussianCoefficient j).map Complex.ofReal * U *
    (gaussianCoefficient j).map Complex.ofReal

omit [Fintype ι] in
private theorem map_coeff (j : Directions ι) :
    (coefficient (R := ℝ) j).map Complex.ofReal = coefficient (R := ℂ) j := by
  cases j with
  | inl p =>
    ext (i|i) (k|k) <;>
      simp [coefficient,realEdge,symEdge,Matrix.single_apply,apply_ite Complex.ofReal]
  | inr p =>
    ext (i|i) (k|k) <;>
      simp [coefficient,imagEdge,skewEdge,Matrix.single_apply,apply_ite Complex.ofReal]

private theorem map_scaled (j : Directions ι) :
    (gaussianCoefficient j).map Complex.ofReal = (scale ι : ℂ) • coefficient j := by
  rw [← map_coeff]
  ext i k
  simp [gaussianCoefficient,Matrix.smul_apply]

theorem normalized_covariance (U : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    noiseCov U = ((scale ι : ℂ)^2) • raw U := by
  simp only [noiseCov,map_scaled,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← pow_two]
  rw [← Finset.smul_sum, Fintype.sum_sum_type]
  simp only [coefficient,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type,raw]

omit [DecidableEq ι] in
private theorem scale_identity [Nonempty ι] :
    (scale ι)^2 * 2 = 1 / (Fintype.card (ι ⊕ ι) : ℝ) := by
  have hp : 0 < (Fintype.card (ι ⊕ ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [scale,inv_pow,Real.sq_sqrt (by positivity)]
  field_simp

theorem coefficient_symmetric (u : Directions ι) : (gaussianCoefficient u).IsSymm := by
  have hs (i j : ι) : (symEdge (R := ℝ) i j).transpose = symEdge i j := by
    simp [symEdge,add_comm]
  have hk (i j : ι) : (skewEdge (R := ℝ) i j).transpose = -skewEdge i j := by
    simp [skewEdge,neg_sub]
  cases u <;> simp [Matrix.IsSymm,gaussianCoefficient,coefficient,realEdge,imagEdge,
    fromBlocks_transpose,hs,hk]

theorem normalized_diagonal [Nonempty ι] (s : ι ⊕ ι → ℝ) :
    noiseCov (diagonal (fun i => (s i : ℂ))) =
      diagonal (fun i => (PhaseOptimizer.mix (profile (Equiv.sumComm ι ι)) s i : ℂ)) := by
  rw [normalized_covariance,raw_diagonal,← Matrix.diagonal_smul,profile_mix]
  congr 1
  funext i
  have hc := congrArg Complex.ofReal (scale_identity (ι := ι))
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat,Complex.ofReal_natCast] at hc
  change (scale ι : ℂ)^2*(2*((∑ j, (s j : ℂ)) + (s i : ℂ) - _)) = _
  rw [← mul_assoc,hc]
  simp [transition,Complex.ofReal_sum,div_eq_inv_mul]
  rfl

theorem normalized_entry [Nonempty ι] (S : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (i : ι ⊕ ι) :
    ((noiseCov S) i i).re =
      PhaseOptimizer.mix (profile (Equiv.sumComm ι ι)) (fun j => (S j j).re) i := by
  rw [normalized_covariance,Matrix.smul_apply,raw_diagonal_entry,profile_mix]
  change (((scale ι : ℂ)^2)*(2*(S.trace+S i i-_))).re = _
  rw [← mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat (n := 2),
      ← Complex.ofReal_mul,scale_identity]
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re,Complex.add_re]
  simp only [transition,Complex.re_sum,Matrix.trace,Matrix.diag_apply,div_eq_inv_mul,mul_one]
  rfl

end SpikePhase.Cov


/-! Isotropy and an explicit upper bound on the covariance norm of the
vectorized realified Hermitian noise. -/
namespace SpikePhase.Cov
open Matrix Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairing {j : Type*} [Fintype j] (A B : Matrix j j ℝ) :=
  ∑ i, ∑ k, A i k * B i k

private theorem pairSingle (B : Matrix ι ι ℝ) (i j : ι) :
    pairing (Matrix.single i j 1) B = B i j := by
  simp [pairing,Matrix.single_apply,ite_and,ite_mul]

private theorem pairSym (B : Matrix ι ι ℝ) (i j : ι) :
    pairing (symEdge i j) B = B i j+B j i := by
  simp only [symEdge,pairing,Matrix.add_apply,add_mul,sum_add_distrib]
  rw [← pairing,← pairing,pairSingle,pairSingle]

private theorem pairSkew (B : Matrix ι ι ℝ) (i j : ι) :
    pairing (skewEdge i j) B = B i j-B j i := by
  simp only [skewEdge,pairing,Matrix.sub_apply,sub_mul,sum_sub_distrib]
  rw [← pairing,← pairing,pairSingle,pairSingle]

private theorem pairReal (B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (i j : ι) :
    pairing (realEdge i j) B =
      B (.inl i) (.inl j)+B (.inl j) (.inl i)+(B (.inr i) (.inr j)+B (.inr j) (.inr i)) := by
  simp only [pairing,Fintype.sum_sum_type,realEdge,fromBlocks_apply₁₁,fromBlocks_apply₁₂,
    fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply,zero_mul,sum_const_zero,zero_add,add_zero]
  exact congrArg₂ (·+·) (pairSym (fun a b => B (.inl a) (.inl b)) i j)
    (pairSym (fun a b => B (.inr a) (.inr b)) i j)

private theorem pairImag (B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (i j : ι) :
    pairing (imagEdge i j) B =
      -(B (.inl i) (.inr j)-B (.inl j) (.inr i))+(B (.inr i) (.inl j)-B (.inr j) (.inl i)) := by
  simp only [pairing,Fintype.sum_sum_type,imagEdge,fromBlocks_apply₁₁,fromBlocks_apply₁₂,
    fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply,zero_mul,sum_const_zero,zero_add,add_zero,
    Matrix.neg_apply,neg_mul,sum_neg_distrib]
  exact congrArg₂ (·+·) (congrArg Neg.neg (pairSkew (fun a b => B (.inl a) (.inr b)) i j))
    (pairSkew (fun a b => B (.inr a) (.inl b)) i j)

private theorem fourSq (a b c d : ℝ) : (a+b+(c+d))^2 ≤ 4*(a^2+b^2+(c^2+d^2)) := by
  nlinarith [sq_nonneg (a-b),sq_nonneg (c-d),sq_nonneg ((a+b)-(c+d))]

theorem frobenius_bound (B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    (∑ u : Directions ι, (pairing (gaussianCoefficient u) B)^2) ≤
      8*(scale ι)^2*(∑ i, ∑ j, B i j ^ 2) := by
  have h j : pairing (gaussianCoefficient j) B = scale ι*pairing (coefficient j) B := by
    simp only [pairing,gaussianCoefficient,Matrix.smul_apply,smul_eq_mul,mul_assoc,mul_sum]
  simp only [h,mul_pow,← mul_sum]
  rw [mul_comm 8, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [Fintype.sum_sum_type]
  simp only [coefficient,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type,pairReal,pairImag]
  have sR := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    sum_le_sum (s := (univ : Finset ι)) fun j _ =>
      fourSq (B (.inl i) (.inl j)) (B (.inl j) (.inl i)) (B (.inr i) (.inr j)) (B (.inr j) (.inr i))
  have sI := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    sum_le_sum (s := (univ : Finset ι)) fun j _ =>
      fourSq (-(B (.inl i) (.inr j))) (B (.inl j) (.inr i)) (B (.inr i) (.inl j)) (-(B (.inr j) (.inl i)))
  simp only [neg_sq] at sI
  have sT (x y : ι → ι ⊕ ι) :
      (∑ i, ∑ j, (B (x j) (y i))^2) = ∑ i, ∑ j, (B (x i) (y j))^2 := sum_comm
  simp only [← mul_sum,sum_add_distrib,sT] at sR sI
  simp only [Fintype.sum_sum_type,sum_add_distrib]
  have expand (a b c d : ℝ) : -(a-b)+(c-d) = -a+b+(c+ -d) := by ring
  simp only [expand]
  linarith only [sR,sI]

theorem coefficients_isotropic [Nonempty ι] :
    (∑ u : Directions ι, gaussianCoefficient u * gaussianCoefficient u) = 1 := by
  have h := normalized_diagonal (ι := ι) (fun _ => 1)
  have hu : (fun i => PhaseOptimizer.mix (profile (Equiv.sumComm ι ι)) (fun _ => 1) i) = fun _ => 1 := by
    funext i; simp only [PhaseOptimizer.mix,mul_one,profile_stochastic]
  change noiseCov (diagonal (fun _ => ((1:ℝ):ℂ))) = diagonal (fun i => (PhaseOptimizer.mix _ _ i : ℂ)) at h
  simp only [hu,Complex.ofReal_one,diagonal_one,noiseCov,mul_one] at h
  ext i j
  apply Complex.ofReal_injective
  simpa [Matrix.sum_apply,Matrix.mul_apply,Complex.ofReal_sum,Matrix.one_apply,apply_ite Complex.ofReal] using congrFun (congrFun h i) j

end SpikePhase.Cov


/-! Strict contraction of the phase component of a fixed optimizer. -/
namespace SpikePhase
open Finset Matrix

private theorem pair_gap {d x y z w : ℝ}
    (ez : z^2*(1+x-y)=d*x) (ew : w^2*(1+y-x)=d*y) :
    ((d*(x+y))^2-(2*z*w)^2)*(1+x-y)*(1+y-x) =
      d^2*(x-y)^2*(1-(x+y)^2) := by
  have hp := congrArg₂ (·*·) ez ew
  linear_combination -4 * hp

theorem paired_weights {d x y z w : ℝ} (hd : 0 < d) (hx : 0 < x)
    (hy : 0 < y) (hm : x+y < 1) (hz : 0 < z) (hw : 0 < w)
    (ez : z^2*(1+x-y)=d*x) (ew : w^2*(1+y-x)=d*y) :
    2*z^2 < d ∧ 2*w^2 < d ∧ 2*z*w ≤ d*(x+y) ∧ (x ≠ y → 2*z*w < d*(x+y)) := by
  have diag {x y z : ℝ} (hp : 0 < x) (hs : x+y < 1) (hpos : 0 < z)
      (he : z^2*(1+x-y)=d*x) : 2*z^2 < d := by
    by_contra! hn
    have hle := mul_le_mul_of_nonneg_right hn hp.le
    nlinarith only [he,hle,mul_pos (sq_pos_of_pos hpos) (sub_pos.mpr hs)]
  have h₁ : 0 < 1+x-y := by linarith
  have h₂ : 0 < 1+y-x := by linarith
  have h₃ : 0 < 1-(x+y)^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hm) (show 0 < 1+(x+y) by positivity)]
  have pg := pair_gap ez ew
  rw [mul_assoc] at pg
  have lhs : 0 ≤ 2*z*w := by positivity
  have rhs : 0 ≤ d*(x+y) := by positivity
  refine ⟨diag hx hm hz ez,diag hy (by linarith) hw ew,?_,?_⟩
  · apply (sq_le_sq₀ lhs rhs).mp
    have h : 0 ≤ ((d*(x+y))^2-(2*z*w)^2) * ((1+x-y)*(1+y-x)) := by
      rw [pg]; positivity
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (mul_pos h₁ h₂)).mp h)
  · intro hxy
    apply (sq_lt_sq₀ lhs rhs).mp
    have h : 0 < ((d*(x+y))^2-(2*z*w)^2) * ((1+x-y)*(1+y-x)) := by
      rw [pg]; exact mul_pos (mul_pos (sq_pos_of_pos hd) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))) h₃
    exact sub_pos.mp ((mul_pos_iff_of_pos_right (mul_pos h₁ h₂)).mp h)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem strict_phase_contraction [Nontrivial ι] (s z : ι ⊕ ι → ℝ)
    (hs : ∀ i, 0 < s i) (hsum : ∑ i, s i=1) (hz : ∀ i, 0 < z i)
    (hfix : ∀ i, s i = (z i)^2 * transition (Equiv.sumComm ι ι) s i)
    (a : ι) (ha : z (.inl a) ≠ z (.inr a)) :
    (∀ i, 2*(z i)^2 < (Fintype.card (ι ⊕ ι) : ℝ)) ∧
    (∑ i, 2*z (.inl i)*z (.inr i)) < (Fintype.card (ι ⊕ ι) : ℝ) := by
  classical
  let d : ℝ := Fintype.card (ι ⊕ ι)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  have eq (i : ι ⊕ ι) : (z i)^2*(1+s i-s i.swap)=d*s i := by
    have h := hfix i
    simp only [transition,hsum,Equiv.sumComm_apply] at h
    change s i = _ * (_ / d) at h
    rw [← mul_div_assoc, eq_div_iff hd.ne'] at h
    linarith only [h]
  have total : ∑ i : ι, (s (.inl i)+s (.inr i)) = 1 := by
    simpa only [Fintype.sum_sum_type,sum_add_distrib] using hsum
  have p (i : ι) : 2*(z (.inl i))^2 < d ∧ 2*(z (.inr i))^2 < d ∧
      2*z (.inl i)*z (.inr i) ≤ d*(s (.inl i)+s (.inr i)) ∧
      (s (.inl i) ≠ s (.inr i) → 2*z (.inl i)*z (.inr i) < d*(s (.inl i)+s (.inr i))) := by
    obtain ⟨j,hj⟩ := exists_ne i
    have hi : s (.inl i)+s (.inr i) < 1 := by
      rw [← total,← add_sum_erase _ _ (mem_univ i)]
      have : 0 < ∑ k ∈ univ.erase i, (s (.inl k)+s (.inr k)) :=
        sum_pos' (fun k _ => (add_pos (hs _) (hs _)).le)
          ⟨j,mem_erase.mpr ⟨hj,mem_univ _⟩,add_pos (hs _) (hs _)⟩
      linarith
    exact paired_weights hd (hs (.inl i)) (hs (.inr i)) hi (hz (.inl i)) (hz (.inr i))
      (eq (.inl i)) (eq (.inr i))
  have hdiff : s (.inl a) ≠ s (.inr a) := by
    intro e
    have e₁ := eq (.inl a)
    have e₂ := eq (.inr a)
    simp only [Sum.swap_inl,Sum.swap_inr,e,add_sub_cancel_right,mul_one] at e₁ e₂
    exact ha ((sq_eq_sq₀ (hz _).le (hz _).le).mp (e₁.trans e₂.symm))
  refine ⟨fun i => by cases i with
      | inl j => exact (p j).1
      | inr j => exact (p j).2.1, ?_⟩
  calc
    _ < ∑ i : ι, d*(s (.inl i)+s (.inr i)) :=
      sum_lt_sum (fun i _ => (p i).2.2.1) ⟨a,mem_univ _,(p a).2.2.2 hdiff⟩
    _ = _ := by rw [← mul_sum,total,mul_one]

end SpikePhase


/-! Rigidity of the full complex fixed-point equation, including the
real/imaginary off-diagonal blocks of the optimizer. -/
namespace SpikePhase
open Finset Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem swap_zero (f : ι → ι → ℂ) (r : ι → ι → ℝ)
    (hr : ∀ i j, 0 ≤ r i j ∧ r i j < 1)
    (sym : ∀ i j, r i j=r j i) (h : ∀ i j, f i j=(r i j : ℂ)*f j i) (i j : ι) : f i j=0 := by
  have h₁ := h i j
  have h₂ := h j i
  rw [← sym i j] at h₂
  have hn : (1-(r i j : ℂ)^2) ≠ 0 := by
    have posi := mul_pos (sub_pos.mpr (hr i j).2) (show 0 < 1+r i j by linarith [(hr i j).1])
    exact_mod_cast (show 1-(r i j)^2 ≠ 0 by nlinarith only [posi])
  have eq : (1-(r i j : ℂ)^2)*f i j=0 := by linear_combination h₁ + (r i j : ℂ)*h₂
  exact (mul_eq_zero.mp eq).resolve_left hn

noncomputable def edgeWeight {ι : Type*} (d : ℝ) (z : ι → ℝ) (i j : ι) := z i*z j/d

private theorem weight_sym {τ : Type*} (d : ℝ) (z : τ → ℝ) (i j : τ) :
    edgeWeight d z i j=edgeWeight d z j i := by simp [edgeWeight,mul_comm]

private theorem weight_half {τ : Type*} (d : ℝ) (hd : 0 < d)
    (z : τ → ℝ) (hz : ∀ i, 0 < z i) (hh : ∀ i, 2*(z i)^2 < d) (i j : τ) :
    0 ≤ edgeWeight d z i j ∧ edgeWeight d z i j < 1/2 := by
  unfold edgeWeight
  exact ⟨(div_pos (mul_pos (hz _) (hz _)) hd).le,(div_lt_iff₀ hd).mpr (by nlinarith only [hh i,hh j,sq_nonneg (z i-z j)])⟩

/-- The LL/RR and LR/RL matrix entries are coupled under transposition.
Their two-step contractions eliminate all entries. The remaining trace in
the phase block is eliminated by strict contraction averaged over pairs. -/
theorem zero_of_block_relations (X Y V T : Matrix ι ι ℂ)
    (d : ℝ) (hd : 0 < d) (z : ι ⊕ ι → ℝ) (hz : ∀ i, 0 < z i)
    (hh : ∀ i, 2*(z i)^2 < d)
    (hs : (∑ i,2*z (.inl i)*z (.inr i)) < d)
    (ex : ∀ i j, X i j=(edgeWeight d z (.inl i) (.inl j) : ℂ)*(X j i-T j i))
    (et : ∀ i j, T i j=(edgeWeight d z (.inr i) (.inr j) : ℂ)*(T j i-X j i))
    (ey : ∀ i j, Y i j=(edgeWeight d z (.inl i) (.inr j) : ℂ)*
      (Y j i+V j i+(if i=j then Y.trace-V.trace else 0)))
    (ev : ∀ i j, V i j=(edgeWeight d z (.inr i) (.inl j) : ℂ)*
      (Y j i+V j i-(if i=j then Y.trace-V.trace else 0))) :
    X=0 ∧ Y=0 ∧ V=0 ∧ T=0 := by
  let E := edgeWeight d z
  let r := fun i j : ι => E (.inl i) (.inl j)+E (.inr i) (.inr j)
  let q := fun i j : ι => E (.inl i) (.inr j)+E (.inr i) (.inl j)
  have hW := weight_half d hd z hz hh
  have hr i j : 0 ≤ r i j ∧ r i j < 1 := by
    dsimp [r,E]
    obtain ⟨h₁,h₂⟩ := hW (.inl i) (.inl j)
    obtain ⟨h₃,h₄⟩ := hW (.inr i) (.inr j)
    exact ⟨add_nonneg h₁ h₃,by linarith⟩
  have hq i j : 0 ≤ q i j ∧ q i j < 1 := by
    dsimp [q,E]
    obtain ⟨h₁,h₂⟩ := hW (.inl i) (.inr j)
    obtain ⟨h₃,h₄⟩ := hW (.inr i) (.inl j)
    exact ⟨add_nonneg h₁ h₃,by linarith⟩
  have dr i j : X i j-T i j=0 := by
    apply swap_zero (fun i j => X i j-T i j) r hr (fun i j => by dsimp [r,E]; rw [weight_sym d z (.inl i) (.inl j),weight_sym d z (.inr i) (.inr j)])
    intro k l
    dsimp [r,E]; push_cast
    linear_combination ex k l - et k l
  have sv i j : Y i j+V i j=0 := by
    apply swap_zero (fun i j => Y i j+V i j) q hq (fun i j => by
      dsimp [q,E]; rw [weight_sym d z (.inl i) (.inr j),weight_sym d z (.inr i) (.inl j),add_comm])
    intro k l
    dsimp [q,E]; push_cast
    by_cases e : k=l
    · subst l
      have a := ey k k
      have b := ev k k
      rw [weight_sym d z (.inr k) (.inl k)] at b
      rw [weight_sym d z (.inr k) (.inl k)]
      simp only [ite_true] at a b
      linear_combination a+b
    · have a := ey k l
      have b := ev k l
      simp only [if_neg e,add_zero,sub_zero] at a b
      linear_combination a+b
  have coord (i : ι) :
      Y i i - V i i = (2 * E (.inl i) (.inr i) : ℝ) * (Y.trace-V.trace) := by
    have a := ey i i
    have b := ev i i
    rw [weight_sym d z (.inr i) (.inl i)] at b
    simp only [sv,ite_true,zero_add,zero_sub] at a b
    dsimp [E]; push_cast
    linear_combination a-b
  have eH : Y.trace-V.trace =
      ((∑ i, 2*E (.inl i) (.inr i) : ℝ) : ℂ)*(Y.trace-V.trace) := by
    rw [Complex.ofReal_sum,Finset.sum_mul]
    calc
      _ = ∑ i, (Y i i-V i i) := by simp [Matrix.trace,Matrix.diag_apply,sum_sub_distrib]
      _ = _ := sum_congr rfl (fun i _ => coord i)
  have sum_lt : (∑ i, 2*E (.inl i) (.inr i)) < 1 := by
    dsimp [E,edgeWeight]; simp only [← mul_div_assoc,← mul_assoc,← sum_div]
    exact (div_lt_one hd).mpr hs
  have hn : (1 - ((∑ i, 2*E (.inl i) (.inr i) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (sub_pos.mpr sum_lt).ne'
  have e : Y.trace-V.trace=0 := by
    apply (mul_eq_zero.mp _).resolve_left hn
    linear_combination eH
  refine ⟨?_,?_,?_,?_⟩ <;> ext i j
  · simp only [ex i j,dr,mul_zero,Matrix.zero_apply]
  · simp only [ey i j,sv,e,ite_self,zero_add,mul_zero,Matrix.zero_apply]
  · simp only [ev i j,sv,e,ite_self,sub_zero,mul_zero,Matrix.zero_apply]
  · rw [et i j,← neg_sub (X j i) (T j i),dr]; simp

end SpikePhase


/-! Trace-normalized complex fixed matrices for the realified ensemble are
unique once the marked dual weights on a phase pair differ. -/
namespace SpikePhase.Cov
open Finset Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem weight_prefactor [Nonempty ι] (z : ι ⊕ ι → ℝ) (i j : ι ⊕ ι) :
    (z i : ℂ)*(scale ι : ℂ)^2*(2:ℂ)*(z j : ℂ)=
      (edgeWeight (Fintype.card (ι ⊕ ι) : ℝ) z i j : ℂ) := by
  have hd : 0 < (Fintype.card (ι ⊕ ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  have eq : (scale ι)^2*2=1/(Fintype.card (ι ⊕ ι) : ℝ) := by
    rw [scale,inv_pow,Real.sq_sqrt (by positivity)]; field_simp
  norm_cast
  unfold edgeWeight
  rw [mul_assoc (z i) _ 2,eq]
  ring

set_option maxHeartbeats 800000 in
private theorem fixed_zero [Nonempty ι] (z : ι ⊕ ι → ℝ)
    (hz : ∀ i, 0 < z i) (hh : ∀ i, 2*(z i)^2 < (Fintype.card (ι ⊕ ι):ℝ))
    (hs : (∑ i,2*z (.inl i)*z (.inr i)) < (Fintype.card (ι ⊕ ι):ℝ))
    (X Y V T : Matrix ι ι ℂ) (tr0 : X.trace+T.trace=0)
    (fix : fromBlocks X Y V T = PhaseOptimizer.diagReal z * noiseCov (fromBlocks X Y V T) * PhaseOptimizer.diagReal z) :
    fromBlocks X Y V T=0 := by
  let d : ℝ := Fintype.card (ι ⊕ ι)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos
  rw [normalized_covariance,raw_blocks] at fix
  have ent (i j : ι ⊕ ι) := congrFun (congrFun fix i) j
  simp only [PhaseOptimizer.diagReal,mul_diagonal,diagonal_mul,Matrix.smul_apply,smul_eq_mul] at ent
  have almost (L : Matrix ι ι ℂ) (i j : ι) :
      (plus L) i j=2*(L j i+(if i=j then L.trace else 0)) ∧
      (minus L) i j=2*(L j i-(if i=j then L.trace else 0)) := by
    simp [plus,minus,Matrix.smul_apply,Matrix.diagonal_apply]
  obtain ⟨hX,hY,hV,hT⟩ := zero_of_block_relations X Y V T d hd z hz hh hs
    (fun i j => by
      have e := ent (.inl i) (.inl j)
      simp only [fromBlocks_apply₁₁,Matrix.sub_apply,(almost _ _ _).1,(almost _ _ _).2] at e
      rw [← weight_prefactor]
      by_cases h : i=j <;> (first | simp only [if_pos h] at e | simp only [if_neg h] at e) <;>
        first | linear_combination e | linear_combination e + (z (.inl i) : ℂ)*(scale ι : ℂ)^2*2*(z (.inl j) : ℂ)*tr0)
    (fun i j => by
      have e := ent (.inr i) (.inr j)
      simp only [fromBlocks_apply₂₂,Matrix.sub_apply,(almost _ _ _).1,(almost _ _ _).2] at e
      rw [← weight_prefactor]
      by_cases h : i=j <;> (first | simp only [if_pos h] at e | simp only [if_neg h] at e) <;>
        first | linear_combination e | linear_combination e + (z (.inr i) : ℂ)*(scale ι : ℂ)^2*2*(z (.inr j) : ℂ)*tr0)
    (fun i j => by
      have e := ent (.inl i) (.inr j)
      simp only [fromBlocks_apply₁₂,Matrix.add_apply,(almost _ _ _).1,(almost _ _ _).2] at e
      rw [← weight_prefactor]
      by_cases h : i=j <;> (first | simp only [if_pos h] at e ⊢ | simp only [if_neg h] at e ⊢) <;> linear_combination e)
    (fun i j => by
      have e := ent (.inr i) (.inl j)
      simp only [fromBlocks_apply₂₁,Matrix.add_apply,(almost _ _ _).1,(almost _ _ _).2] at e
      rw [← weight_prefactor]
      by_cases h : i=j <;> (first | simp only [if_pos h] at e ⊢ | simp only [if_neg h] at e ⊢) <;> linear_combination e)
  subst X; subst Y; subst V; subst T
  ext (i|i) (j|j) <;> rfl

/-- Every complex fixed matrix is determined by its trace, including matrices
that couple the real and imaginary coordinates. -/
theorem normalized_fixed_trace_unique [Nontrivial ι] (s z : ι ⊕ ι → ℝ)
    (hs : ∀ i, 0 < s i) (hsum : ∑ i, s i=1) (hz : ∀ i, 0 < z i)
    (hfix : ∀ i, s i=(z i)^2*transition (Equiv.sumComm ι ι) s i)
    (a : ι) (ha : z (.inl a) ≠ z (.inr a)) (U V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)
    (hu : U=PhaseOptimizer.diagReal z*noiseCov U*PhaseOptimizer.diagReal z)
    (hv : V=PhaseOptimizer.diagReal z*noiseCov V*PhaseOptimizer.diagReal z)
    (ht : U.trace=V.trace) : U=V := by
  obtain ⟨h₁,h₂⟩ := strict_phase_contraction s z hs hsum hz hfix a ha
  let W := U-V
  have fw : W=PhaseOptimizer.diagReal z*noiseCov W*PhaseOptimizer.diagReal z := by
    have e : noiseCov (U-V)=noiseCov U-noiseCov V := by
      simp only [noiseCov,mul_sub,sub_mul,sum_sub_distrib]
    change U-V = _*noiseCov (U-V)*_
    rw [e,mul_sub,sub_mul]
    exact congrArg₂ (·-·) hu hv
  have htW : W.trace=0 := by simp [W,Matrix.trace_sub,ht]
  rw [← fromBlocks_toBlocks W] at fw htW
  have tr : W.toBlocks₁₁.trace + W.toBlocks₂₂.trace=0 := by
    simpa [Matrix.trace,Matrix.diag_apply,Fintype.sum_sum_type] using htW
  apply sub_eq_zero.mp
  change W=0
  rw [← fromBlocks_toBlocks W]
  exact fixed_zero z hz h₁ h₂ _ _ _ _ tr fw

end SpikePhase.Cov


/-! The even-dimensional coefficient family in the index conventions and
complex semidefinite program of the submitted problem statement. -/
namespace SpikePhase.Cov
open Matrix Finset PhaseOptimizer OMA.S_arxiv_2606_14687
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d k : ℕ}

noncomputable def projectFamily (e : ι ⊕ ι ≃ Fin d) (r : Fin k ≃ Directions ι)
    (j : Fin k) : Mat d := (gaussianCoefficient (r j)).submatrix e.symm e.symm

omit [Fintype ι] in
private theorem transport_diagonal (e : ι ⊕ ι ≃ Fin d) (s : Fin d → ℝ) :
    (diagReal s).submatrix e e = diagReal (s ∘ e) := by
  simp [diagReal,submatrix_diagonal_equiv,Function.comp_def]

omit [Fintype ι] [DecidableEq ι] in
private theorem pull_inj {R : Type*} (e : ι ⊕ ι ≃ Fin d) :
    Function.Injective (fun U : Matrix (Fin d) (Fin d) R => U.submatrix e e) := by
  intro U V h; ext i j
  simpa using congrFun (congrFun h (e.symm i)) (e.symm j)

theorem project_covariance (e : ι ⊕ ι ≃ Fin d) (r : Fin k ≃ Directions ι) (U : CMat d) :
    (covarianceMap (projectFamily e r) U).submatrix e e = noiseCov (U.submatrix e e) := by
  let A := projectFamily e r
  have coeff (j : Fin k) : (complexMatrix (A j)).submatrix e e =
      (gaussianCoefficient (r j)).map Complex.ofReal := by
    ext i l; simp [A,projectFamily,complexMatrix]
  have sum_pull (t : Fin k → CMat d) :
      (∑ j, t j).submatrix e e = ∑ j, (t j).submatrix e e := by
    ext i l; simp [Matrix.sum_apply]
  rw [covarianceMap,sum_pull,noiseCov]
  have term j : (complexMatrix (A j)*U*complexMatrix (A j)).submatrix e e =
      (gaussianCoefficient (r j)).map Complex.ofReal * U.submatrix e e *
        (gaussianCoefficient (r j)).map Complex.ofReal := by
    rw [← submatrix_mul_equiv _ _ e e e,← submatrix_mul_equiv _ _ e e e,coeff]
  exact (sum_congr rfl (fun j _ => term j)).trans
    (r.sum_comp (fun u => (gaussianCoefficient u).map Complex.ofReal * U.submatrix e e *
       (gaussianCoefficient u).map Complex.ofReal))

/-- For any positive spike the upstream dual program has one optimizer on this
even-dimensional noise. Every coordinate carries a quantitative amount of mass. -/
theorem project_unique_optimizer [Nontrivial ι] (e : ι ⊕ ι ≃ Fin d)
    (r : Fin k ≃ Directions ι) (a : ι) {θ : ℝ} (hθ : 0 < θ) :
    ∃ s : Fin d → ℝ, s ∈ stdSimplex ℝ (Fin d) ∧
      (∀ j, (1/(θ+2))^4/2 ≤ (d:ℝ)*s j) ∧
      dualOptimizer (θ • projector (Pi.single (e (.inl a)) 1)) (projectFamily e r) (diagReal s) ∧
      ∀ U, dualOptimizer (θ • projector (Pi.single (e (.inl a)) 1)) (projectFamily e r) U →
        U=diagReal s := by
  classical
  let f := Equiv.sumComm ι ι
  let P := fun i j : Fin d => profile f (e.symm i) (e.symm j)
  have invf : Function.Involutive f := by intro i; cases i <;> rfl
  have cd := Fintype.one_lt_card (α := ι)
  have size : 4 ≤ Fintype.card (ι ⊕ ι) := by rw [Fintype.card_sum]; omega
  have sym i j : P i j=P j i := profile_symmetric f invf _ _
  have rwMix (s : Fin d → ℝ) (i : ι ⊕ ι) :
      mix P s (e i) = mix (profile f) (s ∘ e) i := by
    unfold mix
    simpa only [P,e.symm_apply_apply,Function.comp_apply] using
      (e.sum_comp (fun j => profile f i (e.symm j)*s j)).symm
  have row i : ∑ j, P i j=1 := by
    exact (e.symm.sum_comp (profile f (e.symm i))).trans (profile_stochastic f (e.symm i))
  have two i j : ∃ l, 0 < P i l ∧ 0 < P l j := by
    obtain ⟨l,hl,hl'⟩ := profile_paths f invf (by omega) (e.symm i) (e.symm j)
    exact ⟨e l,by simpa only [P,e.symm_apply_apply] using hl,
      by simpa only [P,e.symm_apply_apply] using hl'⟩
  have preserve s : covarianceMap (projectFamily e r) (diagReal s) = diagReal (mix P s) := by
    apply pull_inj e
    dsimp only
    rw [project_covariance,transport_diagonal,transport_diagonal]
    change noiseCov (diagonal _) = diagonal _
    rw [normalized_diagonal]
    congr 1; funext i
    exact congrArg Complex.ofReal (rwMix s i).symm
  have readD (U : CMat d) i : ((covarianceMap (projectFamily e r) U) i i).re =
      mix P (fun j => (U j j).re) i := by
    obtain ⟨j,rfl⟩ := e.surjective i
    rw [rwMix]
    have entr := congrFun (congrFun (project_covariance e r U) j) j
    exact (congrArg Complex.re entr).trans (normalized_entry _ j)
  obtain ⟨s,z,hs,hp,hz,hfix,⟨c,hc⟩,opt,fix⟩ := actual_dual_certificate_with_multiplier
    (projectFamily e r) P (fun i j => profile_nonneg _ _ _) sym row two preserve readD (e (.inl a)) hθ.le
  have sum_s : ∑ i, (s ∘ e) i=1 := (e.sum_comp s).trans hs.2
  have sf i : (s ∘ e) i=((z ∘ e) i)^2 * transition f (s ∘ e) i := by
    simpa only [Function.comp_apply,rwMix,profile_mix] using hfix (e i)
  have different : (z ∘ e) (.inl a) ≠ (z ∘ e) (.inr a) := by
    apply distinguished_weights_differ f invf (.inl a) (by simp [f]) θ c hθ.ne'
    intro i
    simpa only [rwMix,e.injective.eq_iff,Function.comp_apply] using hc (e i)
  refine ⟨s,hs,?_,opt,?_⟩
  · intro j
    obtain ⟨i,rfl⟩ := e.surjective j
    have v := variance_lower f invf size (s ∘ e) (z ∘ e) (fun j => (hp _).le) sum_s
      (1/(θ+2)) (by positivity) (fun j => (hz _).2) sf i
    have ce : Fintype.card (ι ⊕ ι)=d := (Fintype.card_congr e).trans (Fintype.card_fin d)
    simpa only [ce,Function.comp_apply] using v
  · intro U hU
    apply pull_inj e
    dsimp only
    have translated V (hV : V=diagReal z*covarianceMap (projectFamily e r) V*diagReal z) :
        V.submatrix e e=diagReal (z ∘ e)*noiseCov (V.submatrix e e)*diagReal (z ∘ e) := by
      have hv := congrArg (fun M : CMat d => M.submatrix e e) hV
      simpa only [← submatrix_mul_equiv _ _ e e e,project_covariance,transport_diagonal] using hv
    apply normalized_fixed_trace_unique (s ∘ e) (z ∘ e) (fun j => hp _) sum_s
      (fun j => (hz _).1) sf a different _ _ (translated _ (fix U hU)) (translated _ (fix _ opt))
    have ht (V : CMat d) : (V.submatrix e e).trace=V.trace :=
      e.sum_comp (fun j => V j j)
    rw [ht,ht,hU.choose_spec.1.1,opt.choose_spec.1.1]

end SpikePhase.Cov


/-! Symmetry, isotropy, and the Frobenius covariance inequality in the exact
indexing and normalization of the upstream Gaussian input hypotheses. -/
namespace SpikePhase.Cov
open Matrix Finset OMA.S_arxiv_2606_14687
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d k : ℕ}

theorem project_symmetric (e : ι ⊕ ι ≃ Fin d) (r : Fin k ≃ Directions ι) (j : Fin k) :
    (projectFamily e r j).IsSymm := (coefficient_symmetric (r j)).submatrix e.symm

theorem project_isotropic [Nonempty ι] (e : ι ⊕ ι ≃ Fin d) (r : Fin k ≃ Directions ι) :
    (∑ j, projectFamily e r j * projectFamily e r j) = 1 := by
  have h := coefficients_isotropic (ι := ι)
  have eq j : projectFamily e r j * projectFamily e r j =
      (gaussianCoefficient (r j)*gaussianCoefficient (r j)).submatrix e.symm e.symm := by
    exact submatrix_mul_equiv _ _ _ e.symm _
  simp only [eq]
  ext i l
  have t := congrFun (congrFun h (e.symm i)) (e.symm l)
  simp only [Matrix.sum_apply] at t ⊢
  simp only [submatrix_apply]
  rw [r.sum_comp (fun u => (gaussianCoefficient u*gaussianCoefficient u) (e.symm i) (e.symm l))]
  simpa only [Matrix.one_apply,e.symm.injective.eq_iff] using t

omit [DecidableEq ι] in
private theorem pull_sum {α : Type*} [AddCommMonoid α] (e : ι ⊕ ι ≃ Fin d)
    (F : Fin d → Fin d → α) :
    (∑ i, ∑ j, F (e i) (e j)) = ∑ i, ∑ j, F i j := by
  simp only [e.sum_comp]
  exact e.sum_comp (fun i => ∑ j, F i j)

theorem project_covariance_bound [Nonempty ι] (e : ι ⊕ ι ≃ Fin d) (r : Fin k ≃ Directions ι) :
    boundsCovariance (projectFamily e r) (2 / Real.sqrt d) := by
  have c : Fintype.card (ι ⊕ ι)=d := (Fintype.card_congr e).trans (Fintype.card_fin d)
  have hp : 0 < (d:ℝ) := by rw [← c]; exact_mod_cast Fintype.card_pos
  have norm : (2/Real.sqrt (d:ℝ))^2=8*(scale ι)^2 := by
    rw [scale,c,div_pow,Real.sq_sqrt hp.le,inv_pow,Real.sq_sqrt (by positivity)]
    field_simp; ring
  refine ⟨by positivity,fun B => ?_⟩
  have h := frobenius_bound (B.submatrix e e)
  have pair (j : Fin k) : (∑ i, ∑ l, projectFamily e r j i l * B i l) =
      pairing (gaussianCoefficient (r j)) (B.submatrix e e) := by
    rw [← pull_sum e (fun i l => projectFamily e r j i l*B i l)]
    simp [projectFamily,pairing,submatrix_apply]
  rw [norm]
  simp only [pair]
  rw [r.sum_comp (fun u => (pairing (gaussianCoefficient u) (B.submatrix e e))^2)]
  simpa only [submatrix_apply,pull_sum e (fun i j => B i j^2)] using h

end SpikePhase.Cov


namespace SpikePhase
open MeasureTheory MvPolynomial ProbabilityTheory

/-- One deterministic witness suffices to rule out a polynomial degeneracy
almost surely for independent atomless coordinates. -/
theorem polynomial_nonzero_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (v : Fin n → ℝ) (hv : eval v P ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), eval x P ≠ 0 := by
  classical
  induction n with
  | zero =>
    exact Filter.Eventually.of_forall fun x => Subsingleton.elim x v ▸ hv
  | succ n ih =>
    let F := finSuccEquiv ℝ n P
    let t := Fin.tail v
    have ep (x : Fin n → ℝ) (a : ℝ) :
        eval (Fin.cons a x) P = ((F.map (eval x)).eval a) := eval_eq_eval_mv_eval' x a P
    have hf : F.map (eval t) ≠ 0 := by
      intro h
      apply hv
      rw [← Fin.cons_self_tail v,ep,h,Polynomial.eval_zero]
    obtain ⟨k,hk⟩ : ∃ k, (F.map (eval t)).coeff k ≠ 0 := by
      by_contra! h
      exact hf (Polynomial.ext fun k => by simp [h])
    rw [Polynomial.coeff_map] at hk
    have htail := ih (F.coeff k) t hk
    have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    let ok := fun a (x : Fin n → ℝ) => eval (Fin.cons a x) P ≠ 0
    have meas : MeasurableSet {z : ℝ × (Fin n → ℝ) | ok z.1 z.2} := by
      have mc : Measurable (fun z : ℝ × (Fin n → ℝ) => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
        apply measurable_pi_iff.mpr
        intro i
        cases i using Fin.cases with
        | zero => simpa using (measurable_fst : Measurable (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))
        | succ j => simpa [Function.comp_def] using (measurable_pi_apply j).comp (measurable_snd : Measurable (Prod.snd : ℝ × (Fin n → ℝ) → _))
      exact (measurableSet_eq_fun (P.continuous_eval.measurable.comp mc) measurable_const).compl
    have tailFirst : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ᵐ a ∂μ, ok a x := by
      filter_upwards [htail] with x h
      have hn : F.map (eval x) ≠ 0 := by
        intro z
        apply h
        simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using congrArg (fun p : Polynomial ℝ => p.coeff k) z
      have hnull := (Polynomial.finite_setOfPred_isRoot hn).measure_zero (μ := μ)
      simpa only [ok,ep,Polynomial.IsRoot] using (show ∀ᵐ a ∂μ, ¬ (F.map (eval x)).IsRoot a from
        ae_iff.mpr (by simpa using hnull))
    have hprod := (Measure.ae_prod_iff_ae_ae meas).mpr ((Measure.ae_ae_comm meas).mpr tailFirst)
    have h := mp.quasiMeasurePreserving.ae hprod
    filter_upwards [h] with x hx
    change eval (Fin.cons (x 0) (fun i : Fin n => x ((0 : Fin (n+1)).succAbove i))) P ≠ 0 at hx
    simp only [Fin.zero_succAbove] at hx
    change eval (Fin.cons (x 0) (Fin.tail x)) P ≠ 0 at hx
    rwa [Fin.cons_self_tail] at hx
/-- A square polynomial matrix which is invertible at one noise value is
nonsingular almost surely for the standard Gaussian coordinates. -/
theorem gaussian_determinant_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (A : Matrix ι ι (MvPolynomial (Fin n) ℝ)) (v : Fin n → ℝ)
    (hv : (A.map (eval v)).det ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1), (A.map (eval x)).det ≠ 0 := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have eq (x : Fin n → ℝ) : eval x A.det = (A.map (eval x)).det := (eval x).map_det A
  simpa only [eq] using polynomial_nonzero_ae (gaussianReal 0 1) n A.det v ((eq v).symm ▸ hv)

/-- For a linear Gaussian matrix family, arbitrary prescribed powers of
the noise applied to deterministic seed columns generically span as soon
as one set of coefficients gives a nonsingular matrix. Multiple seeds
allow the real and imaginary coordinates of the Hermitian model. -/
theorem gaussian_krylov_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (A : Fin n → Matrix ι ι ℝ) (power : ι → ℕ) (seed : ι → ι → ℝ)
    (v : Fin n → ℝ)
    (hv : (Matrix.of fun i j => (((∑ h, v h • A h)^power j).mulVec (seed j)) i).det ≠ 0) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1),
      (Matrix.of fun i j => (((∑ h, x h • A h)^power j).mulVec (seed j)) i).det ≠ 0 := by
  classical
  let G : Matrix ι ι (MvPolynomial (Fin n) ℝ) := fun i j =>
    ∑ h, X h * C (A h i j)
  let B : Matrix ι ι (MvPolynomial (Fin n) ℝ) := fun i j =>
    ((G^power j).mulVec (fun a => C (seed j a))) i
  have g (x : Fin n → ℝ) : G.map (eval x) = ∑ h, x h • A h := by
    ext i j
    change eval x (∑ h, X h * C (A h i j)) = _
    simp [Matrix.sum_apply,Matrix.smul_apply]
  have b (x : Fin n → ℝ) : B.map (eval x) =
      Matrix.of fun i j => (((∑ h, x h • A h)^power j).mulVec (seed j)) i := by
    ext i j
    change eval x (((G^power j).mulVec (fun a => C (seed j a))) i) = _
    simp only [RingHom.map_mulVec,Matrix.map_pow,g,Function.comp_def,eval_C,Matrix.of_apply]
  simpa only [b] using gaussian_determinant_nonzero n B v (by rwa [b])

end SpikePhase


namespace SpikePhase
open Matrix Finset

/-- For an upper Hessenberg matrix with unit first subdiagonal, the Krylov
matrix of the first coordinate is upper triangular with unit diagonal. -/
theorem hessenberg_krylov_det {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (below : ∀ i j : Fin n, j.val+1 < i.val → H i j=0)
    (edge : ∀ i j : Fin n, j.val+1 = i.val → H i j=1) :
    (Matrix.of fun i j : Fin n => ((H^j.val).mulVec (fun a => if a.val=0 then 1 else 0)) i).det=1 := by
  let v : Fin n → ℝ := fun a => if a.val=0 then 1 else 0
  have front (k : ℕ) (i : Fin n) (hi : k ≤ i.val) :
      ((H^k).mulVec v) i = if i.val=k then 1 else 0 := by
    induction k generalizing i with
    | zero => simp [v]
    | succ k ih =>
      let j : Fin n := ⟨k,by omega⟩
      rw [pow_succ',← Matrix.mulVec_mulVec]
      change (∑ t, H i t * ((H^k).mulVec v) t) = _
      rw [sum_eq_single j]
      · have hj : j.val=k := rfl
        rw [ih j (by omega),if_pos hj,mul_one]
        by_cases eq : i.val=k+1
        · rw [if_pos eq]; exact edge i j (by omega)
        · rw [if_neg eq]; exact below i j (by omega)
      · intro t _ hne
        by_cases ht : t.val < k
        · rw [below i t (by omega),zero_mul]
        · rw [ih t (by omega),if_neg (fun he => hne (Fin.ext he)),mul_zero]
      · simp
  let B := Matrix.of fun i j : Fin n => ((H^j.val).mulVec v) i
  change B.det = 1
  have upper : B.IsUpperTriangular := by
    intro i j h
    change j.val < i.val at h
    change ((H^j.val).mulVec v) i=0
    rw [front _ _ (by exact Nat.le_of_lt h),if_neg (by omega)]
  rw [Matrix.det_of_isUpperTriangular upper]
  apply prod_eq_one
  intro i _
  change ((H^i.val).mulVec v) i=1
  rw [front _ _ le_rfl,if_pos rfl]

/-- The real symmetric adjacency matrix of a path gives an explicit witness. -/
theorem path_krylov_det (n : ℕ) :
    let H : Matrix (Fin n) (Fin n) ℝ := fun i j => if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0
    (Matrix.of fun i j : Fin n => ((H^j.val).mulVec (fun a => if a.val=0 then 1 else 0)) i).det=1 := by
  apply hessenberg_krylov_det
  · intro i j h; exact if_neg (by omega)
  · intro i j h; exact if_pos (Or.inr h)
end SpikePhase


namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eigenvector_hits_seed (H : Matrix ι ι ℝ) (sym : H.transpose=H)
    (power : ι → ℕ) (seed : ι → ι → ℝ)
    (full : (Matrix.of fun i j => ((H^power j).mulVec (seed j)) i).det ≠ 0)
    (u : ι → ℝ) (nonzero : u ≠ 0) (ev : ℝ) (eig : H.mulVec u=ev • u) :
    ∃ j, u ⬝ᵥ seed j ≠ 0 := by
  by_contra! orth
  let B := Matrix.of fun i j => ((H^power j).mulVec (seed j)) i
  have unit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr full)
  have left : u ᵥ* H = ev • u := by rw [← sym,vecMul_transpose]; exact eig
  have annihilate (j : ι) (m : ℕ) : u ⬝ᵥ ((H^m).mulVec (seed j))=0 := by
    induction m with
    | zero => simpa using orth j
    | succ m ih => rw [pow_succ',← mulVec_mulVec,dotProduct_mulVec,left,smul_dotProduct,ih,smul_zero]
  apply nonzero
  apply Matrix.vecMul_injective_of_isUnit unit
  dsimp only
  rw [zero_vecMul]
  exact funext fun j => annihilate j _

omit [DecidableEq ι] in
theorem spiked_top_overlap (W : Matrix ι ι ℝ) (v z u : ι → ℝ) (θ a b : ℝ)
    (hθ : 0 < θ) (hz : z ⬝ᵥ z = 1) (hu : u ⬝ᵥ u = 1)
    (overlap : v ⬝ᵥ z ≠ 0) (ez : W.mulVec z = a • z)
    (eu : (θ • vecMulVec v v + W).mulVec u = b • u)
    (maxz : ∀ x, x ⬝ᵥ W.mulVec x ≤ a*(x ⬝ᵥ x))
    (maxu : ∀ x, x ⬝ᵥ (θ • vecMulVec v v + W).mulVec x ≤ b*(x ⬝ᵥ x)) :
    a < b ∧ v ⬝ᵥ u ≠ 0 := by
  have form (x : ι → ℝ) : x ⬝ᵥ (θ • vecMulVec v v + W).mulVec x =
      θ*(v ⬝ᵥ x)^2 + x ⬝ᵥ W.mulVec x := by
    have act : (vecMulVec v v).mulVec x = (v ⬝ᵥ x) • v := by
      ext i; simp [vecMulVec,mulVec,dotProduct,Finset.mul_sum,mul_comm,mul_left_comm]
    rw [add_mulVec,Matrix.smul_mulVec,act,dotProduct_add,dotProduct_smul,dotProduct_smul,
      dotProduct_comm x v]; simp [pow_two]
  have h := maxu z
  rw [form,ez,dotProduct_smul,hz] at h
  simp only [smul_eq_mul,mul_one] at h
  have gap : a < b := by linarith [mul_pos hθ (sq_pos_of_ne_zero overlap)]
  refine ⟨gap,?_⟩
  intro bad
  have h := form u
  rw [eu,dotProduct_smul,hu,bad] at h
  have q := maxz u
  rw [hu,mul_one] at q
  simp only [smul_eq_mul,mul_one,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,zero_add] at h
  linarith
end SpikePhase

namespace SpikePhase
open Matrix MeasureTheory ProbabilityTheory

noncomputable def pathMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0

def pathPower {n : ℕ} : Fin n ⊕ Fin n → ℕ := Sum.elim Fin.val Fin.val

def pairedSeed {n : ℕ} (j : Fin n ⊕ Fin n) : Fin n ⊕ Fin n → ℝ :=
  let v : Fin n → ℝ := fun i => if i.val=0 then 1 else 0
  j.elim (fun _ => Sum.elim v 0) (fun _ => Sum.elim 0 v)

/-- The two seeds are the real and imaginary parts of the first complex
coordinate. At the realified path their joint Krylov determinant is one. -/
theorem paired_path_witness (n : ℕ) :
    let W := fromBlocks (pathMatrix n) 0 0 (pathMatrix n)
    (Matrix.of fun i j : Fin n ⊕ Fin n => ((W^pathPower j).mulVec (pairedSeed j)) i).det=1 := by
  let H := pathMatrix n
  let v : Fin n → ℝ := fun i => if i.val=0 then 1 else 0
  let B := Matrix.of fun i j : Fin n => ((H^j.val).mulVec v) i
  have hb : B.det=1 := path_krylov_det n
  have e : (Matrix.of fun i j : Fin n ⊕ Fin n =>
      (((fromBlocks H 0 0 H)^pathPower j).mulVec (pairedSeed j)) i) = fromBlocks B 0 0 B := by
    ext (i|i) (j|j) <;>
      simp [fromBlocks_diagonal_pow,fromBlocks_mulVec,pathPower,pairedSeed,B,v,
        Function.comp_def] <;> change ((H^j.val).mulVec (0 : Fin n → ℝ)) i = 0 <;> simp
  change (Matrix.of _).det=1
  rw [e,det_fromBlocks_zero₂₁,hb,mul_one]

theorem gaussian_paired_path_spans (n k : ℕ)
    (A : Fin k → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (g : Fin k → ℝ)
    (witness : (∑ h, g h • A h) = fromBlocks (pathMatrix n) 0 0 (pathMatrix n)) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k => gaussianReal 0 1),
      (Matrix.of fun i j => (((∑ h, x h • A h)^pathPower j).mulVec (pairedSeed j)) i).det ≠ 0 := by
  apply gaussian_krylov_nonzero k A pathPower pairedSeed g
  rw [witness,paired_path_witness]; exact one_ne_zero
end SpikePhase


namespace SpikePhase.Cov
open Matrix Finset MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sum_sym (H : Matrix ι ι ℝ) (sym : H.transpose = H) :
    ∑ i, ∑ j, (H i j / 2) • symEdge i j = H := by
  ext a b
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,symEdge,Matrix.add_apply,mul_add,sum_add_distrib]
  simp [Matrix.single_apply,ite_and,mul_ite]
  have h : H b a=H a b := congrFun (congrFun sym a) b
  linarith

/-- The normalized realified noise can realize the real representation of
every real symmetric matrix. -/
theorem realize_real_block [Nonempty ι] (H : Matrix ι ι ℝ) (sym : H.transpose=H) :
    ∃ g : Directions ι → ℝ, (∑ j, g j • gaussianCoefficient j) = fromBlocks H 0 0 H := by
  let g : Directions ι → ℝ := Sum.elim (fun p => H p.1 p.2/(2*scale ι)) (fun _ => 0)
  have hd : 0 < (Fintype.card (ι ⊕ ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  have nz : scale ι ≠ 0 := by unfold scale; positivity
  have ss (a : ℝ) : a/(2*scale ι)*scale ι=a/2 := by field_simp
  refine ⟨g,?_⟩
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,g,Sum.elim_inl,Sum.elim_inr,
    zero_mul,zero_smul,sum_const_zero,add_zero,gaussianCoefficient,smul_smul,ss,coefficient]
  have h := sum_sym H sym
  ext (a|a) (b|b) <;>
    simp only [Matrix.sum_apply,Matrix.smul_apply,realEdge,fromBlocks_apply₁₁,fromBlocks_apply₁₂,
      fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply,smul_eq_mul,mul_zero,sum_const_zero]
    <;> first | simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using congrFun (congrFun h a) b | rfl

theorem hermitian_realification_cyclic (n k : ℕ) [Nonempty (Fin n)] (r : Fin k ≃ Directions (Fin n)) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k => gaussianReal 0 1),
      (Matrix.of fun i j => (((∑ h, x h • gaussianCoefficient (r h))^pathPower j).mulVec (pairedSeed j)) i).det ≠ 0 := by
  have sym : (pathMatrix n).transpose=pathMatrix n := by
    ext i j; simp [pathMatrix,Matrix.transpose_apply,or_comm]
  obtain ⟨g,hg⟩ := realize_real_block (pathMatrix n) sym
  exact gaussian_paired_path_spans n k (fun h => gaussianCoefficient (r h)) (g ∘ r)
    ((r.sum_comp (fun u => g u • gaussianCoefficient u)).trans hg)

end SpikePhase.Cov

namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A commuting orthogonal complex structure converts overlap with either seed
into overlap with v in the very same real eigenspace. -/
theorem rotate_to_signal (W J : Matrix ι ι ℝ) (a : ℝ) (z v : ι → ℝ)
    (comm : J*W=W*J) (skew : J.transpose = -J) (orth : J.transpose*J=1)
    (eig : W.mulVec z=a • z) (unit : z ⬝ᵥ z=1)
    (hit : z ⬝ᵥ v ≠ 0 ∨ z ⬝ᵥ J.mulVec v ≠ 0) :
    ∃ y, W.mulVec y=a • y ∧ y ⬝ᵥ y=1 ∧ v ⬝ᵥ y ≠ 0 := by
  rcases hit with h|h
  · exact ⟨z,eig,unit,by rwa [dotProduct_comm]⟩
  refine ⟨J.mulVec z,?_,?_,?_⟩
  · rw [mulVec_mulVec,← comm,← mulVec_mulVec,eig,mulVec_smul]
  · rw [← Matrix.dotProduct_transpose_mulVec J z (J.mulVec z),mulVec_mulVec,orth,one_mulVec,unit]
  · have e := Matrix.dotProduct_transpose_mulVec J v z
    rw [skew,neg_mulVec,dotProduct_neg] at e
    intro hz
    rw [hz] at e
    exact h (by linarith)
end SpikePhase

namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Joint cyclicity before the spike forces the phase coordinate of every
leading unit eigenvector after the spike to vanish. -/
theorem joint_cyclic_phase_zero (W J : Matrix ι ι ℝ) (a b θ : ℝ)
    (z u v : ι → ℝ) (power : ι → ℕ) (seed : ι → ι → ℝ)
    (seeds : ∀ j, seed j = v ∨ seed j = J.mulVec v)
    (full : (Matrix.of fun i j => ((W^power j).mulVec (seed j)) i).det ≠ 0)
    (sym : W.transpose = W) (comm : J*W=W*J) (skew : J.transpose = -J)
    (orth : J.transpose*J=1) (positive : 0 < θ)
    (ez : W.mulVec z=a • z) (hz : z ⬝ᵥ z=1) (hu : u ⬝ᵥ u=1)
    (eu : (θ • vecMulVec v v + W).mulVec u=b • u)
    (maxz : ∀ x, x ⬝ᵥ W.mulVec x ≤ a*(x ⬝ᵥ x))
    (maxu : ∀ x, x ⬝ᵥ (θ • vecMulVec v v + W).mulVec x ≤ b*(x ⬝ᵥ x)) :
    a < b ∧ v ⬝ᵥ u ≠ 0 ∧ u ⬝ᵥ J.mulVec v = 0 := by
  have nz : z ≠ 0 := by rintro rfl; simp at hz
  obtain ⟨j,hj⟩ := eigenvector_hits_seed W sym power seed full z nz a ez
  have hits : z ⬝ᵥ v ≠ 0 ∨ z ⬝ᵥ J.mulVec v ≠ 0 := by
    rcases seeds j with h|h
    · exact Or.inl (h ▸ hj)
    · exact Or.inr (h ▸ hj)
  obtain ⟨y,ey,hy,ov⟩ := rotate_to_signal W J a z v comm skew orth ez hz hits
  obtain ⟨gap,overlap⟩ := spiked_top_overlap W v y u θ a b positive hy hu ov ey eu maxz maxu
  exact ⟨gap,overlap,phase_coordinate_zero J W skew sym comm positive.ne' v u overlap eu⟩

end SpikePhase
namespace SpikePhase.Cov
open Matrix MeasureTheory ProbabilityTheory

private theorem coefficient_commutes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Directions ι) : phase * gaussianCoefficient u = gaussianCoefficient u * phase := by
  cases u with
  | inl q => simp [gaussianCoefficient,coefficient,realEdge,phase,fromBlocks_multiply]
  | inr q => simp [gaussianCoefficient,coefficient,imagEdge,phase,fromBlocks_multiply]

/-- In the actual realified noise ensemble every leading unit spike eigenvector
has zero phase coordinate almost surely, simultaneously for all positive spike strengths. -/
theorem gaussian_phase_vanishes (n k : ℕ) [Nonempty (Fin n)] (r : Fin k ≃ Directions (Fin n)) :
    let e : Fin n → ℝ := fun i => if i.val=0 then 1 else 0
    let v : Fin n ⊕ Fin n → ℝ := Sum.elim e 0
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k => gaussianReal 0 1),
      let W := ∑ j, x j • gaussianCoefficient (r j)
      ∀ (a b θ : ℝ) (z u : Fin n ⊕ Fin n → ℝ), 0 < θ →
        W.mulVec z=a • z → z ⬝ᵥ z=1 → u ⬝ᵥ u=1 →
        (θ • vecMulVec v v + W).mulVec u=b • u →
        (∀ y, y ⬝ᵥ W.mulVec y ≤ a*(y ⬝ᵥ y)) →
        (∀ y, y ⬝ᵥ (θ • vecMulVec v v + W).mulVec y ≤ b*(y ⬝ᵥ y)) →
        a < b ∧ v ⬝ᵥ u ≠ 0 ∧ u ⬝ᵥ phase.mulVec v=0 := by
  dsimp only
  filter_upwards [hermitian_realification_cyclic n k r] with x full
  intro a b θ z u pos ez hz hu eu maxz maxu
  apply joint_cyclic_phase_zero _ _ _ _ _ z u _ pathPower pairedSeed _ full _ _ phase_skew _ pos ez hz hu eu maxz maxu
  · intro j
    cases j with
    | inl j => exact Or.inl rfl
    | inr j =>
      right
      ext (i|i) <;> simp [pairedSeed,phase,fromBlocks_mulVec,Function.comp_def]
      change 0 = ((-1 : Matrix (Fin n) (Fin n) ℝ).mulVec 0) i
      simp
  · simp only [transpose_sum,transpose_smul,(coefficient_symmetric _).eq]
  · simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,coefficient_commutes]
  · simp [phase,fromBlocks_transpose,fromBlocks_multiply,fromBlocks_one]
end SpikePhase.Cov

namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

scoped instance matMeasurable : MeasurableSpace (Matrix ι ι ℝ) := borel _
scoped instance matBorel : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩

/-- Positive normalization of the unspiked resolvent at the post-spike eigenvalue. -/
noncomputable def orientedResolvent (D : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ :=
  let y := D⁻¹.mulVec v
  (Real.sqrt (y ⬝ᵥ y))⁻¹ • y

theorem measurable_orientedResolvent (v : ι → ℝ) :
    Measurable (fun D : Matrix ι ι ℝ => orientedResolvent D v) := by
  have invM : Measurable (fun D : Matrix ι ι ℝ => D⁻¹) := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv]
    exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable
  have y : Measurable (fun D : Matrix ι ι ℝ => D⁻¹.mulVec v) := by
    exact (continuous_id.matrix_mulVec continuous_const).measurable.comp invM
  unfold orientedResolvent dotProduct
  fun_prop (disch := assumption)

theorem resolvent_above_spectrum (W : Matrix ι ι ℝ) {a b : ℝ} (gap : a < b)
    (bound : ∀ x, x ⬝ᵥ W.mulVec x ≤ a * (x ⬝ᵥ x)) :
    IsUnit (b • (1 : Matrix ι ι ℝ) - W).det := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  obtain ⟨v,hv,eq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  rw [sub_mulVec,Matrix.smul_mulVec,one_mulVec,sub_eq_zero] at eq
  have q := bound v
  rw [← eq,dotProduct_smul,smul_eq_mul] at q
  have pos : 0 < v ⬝ᵥ v := by
    have h := dotProduct_star_self_pos_iff.mpr hv
    simpa using h
  linarith [mul_lt_mul_of_pos_right gap pos]

theorem orientedResolvent_eq_unit (D : Matrix ι ι ℝ) (v u : ι → ℝ) (c : ℝ)
    (det : IsUnit D.det) (hc : 0 < c) (unit : u ⬝ᵥ u=1)
    (equation : D.mulVec u=c • v) : orientedResolvent D v=u := by
  have h := congrArg (fun y => D⁻¹.mulVec y) equation
  rw [mulVec_mulVec,D.nonsing_inv_mul det,one_mulVec,mulVec_smul] at h
  have y : D⁻¹.mulVec v=c⁻¹ • u := by rw [h,inv_smul_smul₀ hc.ne']
  unfold orientedResolvent
  rw [y]
  dsimp only
  rw [smul_dotProduct,dotProduct_smul,unit]
  simp only [smul_eq_mul,mul_one,← sq,Real.sqrt_sq (inv_nonneg.mpr hc.le),inv_inv,
    smul_inv_smul₀ hc.ne']
end SpikePhase
namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rayleighTop (W : Matrix ι ι ℝ) : ℝ :=
  sSup ((fun z : EuclideanSpace ℝ ι => z.ofLp ⬝ᵥ W.mulVec z.ofLp) ''
    Metric.sphere (0 : EuclideanSpace ℝ ι) 1)

private theorem continuous_rayleigh_form :
    Continuous (fun q : Matrix ι ι ℝ × EuclideanSpace ℝ ι =>
      q.2.ofLp ⬝ᵥ q.1.mulVec q.2.ofLp) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

theorem continuous_rayleighTop : Continuous (rayleighTop (ι := ι)) :=
  (isCompact_sphere _ _).continuous_sSup continuous_rayleigh_form

theorem rayleighTop_eq (W : Matrix ι ι ℝ) (u : ι → ℝ) (b : ℝ)
    (unit : u ⬝ᵥ u = 1) (eig : W.mulVec u = b • u)
    (bound : ∀ y, y ⬝ᵥ W.mulVec y ≤ b*(y ⬝ᵥ y)) : rayleighTop W=b := by
  let z : EuclideanSpace ℝ ι := WithLp.toLp 2 u
  have sq (t : EuclideanSpace ℝ ι) : ‖t‖^2=t.ofLp ⬝ᵥ t.ofLp := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct,pow_two]
  have hz : z ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1 := by
    rw [Metric.mem_sphere,dist_zero_right]
    have s := (sq z).trans unit
    nlinarith [norm_nonneg z]
  have eval : z.ofLp ⬝ᵥ W.mulVec z.ofLp=b := by
    change u ⬝ᵥ W.mulVec u = b
    rw [eig,dotProduct_smul,unit,smul_eq_mul,mul_one]
  have all : ∀ t ∈ Metric.sphere (0 : EuclideanSpace ℝ ι) 1,
      t.ofLp ⬝ᵥ W.mulVec t.ofLp ≤ b := by
    intro t ht
    rw [Metric.mem_sphere,dist_zero_right] at ht
    simpa [← sq,ht] using bound t.ofLp
  apply le_antisymm
  · exact csSup_le ⟨_,z,hz,rfl⟩ (by rintro _ ⟨t,ht,rfl⟩; exact all t ht)
  · apply le_csSup
    · exact ⟨b,by rintro _ ⟨t,ht,rfl⟩; exact all t ht⟩
    · exact ⟨z,hz,eval⟩
end SpikePhase
namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Borel choice defined for every noise matrix, including exceptional inputs. -/
noncomputable def selectSpike (θ : ℝ) (v : ι → ℝ) (W : Matrix ι ι ℝ) : ι → ℝ :=
  orientedResolvent (rayleighTop (θ • vecMulVec v v + W) • (1 : Matrix ι ι ℝ) - W) v

theorem measurable_selectSpike (θ : ℝ) (v : ι → ℝ) : Measurable (selectSpike θ v) := by
  apply (measurable_orientedResolvent v).comp
  exact (((continuous_rayleighTop.comp (continuous_const.add continuous_id)).smul continuous_const).sub continuous_id).measurable

/-- Once the strict eigenvalue gap holds this Borel choice agrees with
every positively oriented unit leading eigenvector. -/
theorem selectSpike_eq (W : Matrix ι ι ℝ) (u v : ι → ℝ) (θ a b : ℝ)
    (pos : 0 < θ) (overlap : 0 < v ⬝ᵥ u) (unit : u ⬝ᵥ u=1) (gap : a < b)
    (ew : (θ • vecMulVec v v + W).mulVec u=b • u)
    (bw : ∀ y, y ⬝ᵥ W.mulVec y ≤ a*(y ⬝ᵥ y))
    (bs : ∀ y, y ⬝ᵥ (θ • vecMulVec v v + W).mulVec y ≤ b*(y ⬝ᵥ y)) :
    selectSpike θ v W=u := by
  unfold selectSpike
  rw [rayleighTop_eq _ u b unit ew bs]
  apply orientedResolvent_eq_unit _ _ _ (θ*(v ⬝ᵥ u)) (resolvent_above_spectrum _ gap bw)
    (mul_pos pos overlap) unit
  have act : (vecMulVec v v).mulVec u=(v ⬝ᵥ u) • v := by
    ext i
    simp [vecMulVec,mulVec,dotProduct,Finset.mul_sum,mul_comm,mul_left_comm]
  rw [add_mulVec,Matrix.smul_mulVec,act,smul_smul] at ew
  rw [sub_mulVec,Matrix.smul_mulVec,one_mulVec,← ew,add_sub_cancel_right]
end SpikePhase
namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_top_unit (W : Matrix ι ι ℝ) (sym : W.IsSymm) :
    ∃ (a : ℝ) (z : ι → ℝ), z ⬝ᵥ z=1 ∧ W.mulVec z=a • z ∧
      ∀ y, y ⬝ᵥ W.mulVec y ≤ a*(y ⬝ᵥ y) := by
  have h : W.IsHermitian := isHermitian_iff_isSymm.mpr sym
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ h.eigenvalues Finset.univ_nonempty
  let a := h.eigenvalues i
  let z := h.eigenvectorBasis i
  refine ⟨a,z.ofLp,?_,h.mulVec_eigenvectorBasis i,?_⟩
  · have hz : ‖z‖=1 := h.eigenvectorBasis.orthonormal.1 i
    have q := EuclideanSpace.real_norm_sq_eq z
    simpa [dotProduct,pow_two,hz] using q.symm
  · have diag : (a • (1 : Matrix ι ι ℝ) - diagonal h.eigenvalues).PosSemidef := by
      have e : a • (1 : Matrix ι ι ℝ) - diagonal h.eigenvalues = diagonal (fun j => a-h.eigenvalues j) := by
        ext j k; by_cases hj : j=k <;> simp [hj,Matrix.one_apply,diagonal_apply]
      rw [e,posSemidef_diagonal_iff]
      exact fun j => sub_nonneg.mpr (hi j (Finset.mem_univ j))
    let U := Unitary.conjStarAlgAut ℝ _ h.eigenvectorUnitary
    have e : U (diagonal h.eigenvalues)=W := by simpa [U] using h.spectral_theorem.symm
    have e' : U (a • (1 : Matrix ι ι ℝ) - diagonal h.eigenvalues) = a • 1-W := by
      rw [map_sub,map_smul,map_one,e]
    have ps : (a • (1 : Matrix ι ι ℝ)-W).PosSemidef := by
      rw [← e']
      exact diag.mul_mul_conjTranspose_same _
    intro y
    have q := ps.dotProduct_mulVec_nonneg y
    simpa [Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul] using q
end SpikePhase
namespace SpikePhase
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_oriented_top [Nonempty ι] (M : Matrix ι ι ℝ) (sym : M.IsSymm)
    (v : ι → ℝ) (hit : ∀ b u, u ⬝ᵥ u=1 → M.mulVec u=b • u →
      (∀ y, y ⬝ᵥ M.mulVec y ≤ b*(y ⬝ᵥ y)) → v ⬝ᵥ u ≠ 0) :
    ∃ b u, u ⬝ᵥ u=1 ∧ M.mulVec u=b • u ∧
      (∀ y, y ⬝ᵥ M.mulVec y ≤ b*(y ⬝ᵥ y)) ∧ 0 < v ⬝ᵥ u := by
  obtain ⟨b,u,unit,eig,bound⟩ := exists_top_unit M sym
  rcases lt_or_gt_of_ne (hit b u unit eig bound) with neg|pos
  · refine ⟨b,-u,by simpa using unit,by rw [mulVec_neg,eig,smul_neg],bound,by simpa using neg⟩
  · exact ⟨b,u,unit,eig,bound,pos⟩

namespace Cov
open MeasureTheory ProbabilityTheory
/-- The canonical Borel selector is a positively oriented leading eigenvector
with zero phase coordinate almost surely in the realified Hermitian ensemble. -/
theorem gaussian_oriented_top (n k : ℕ) [Nonempty (Fin n)] (r : Fin k ≃ Directions (Fin n))
    (θ : ℝ) (pos : 0 < θ) :
    let e : Fin n → ℝ := fun i => if i.val=0 then 1 else 0
    let v : Fin n ⊕ Fin n → ℝ := Sum.elim e 0
    let W := fun x : Fin k → ℝ => ∑ j, x j • gaussianCoefficient (r j)
    let u := fun x => selectSpike θ v (W x)
    Measurable u ∧ ∀ᵐ x ∂Measure.pi (fun _ : Fin k => gaussianReal 0 1),
      u x ⬝ᵥ u x=1 ∧ 0 < v ⬝ᵥ u x ∧ u x ⬝ᵥ phase.mulVec v=0 ∧
      ∃ b, (θ • vecMulVec v v + W x).mulVec (u x)=b • u x ∧
        ∀ y, y ⬝ᵥ (θ • vecMulVec v v + W x).mulVec y ≤ b*(y ⬝ᵥ y) := by
  intro e v W u
  constructor
  · apply (measurable_selectSpike θ v).comp
    exact (show Continuous W by dsimp [W]; fun_prop).measurable
  · filter_upwards [gaussian_phase_vanishes n k r] with x h
    have sym : (W x).IsSymm := by
      unfold Matrix.IsSymm W
      simp only [transpose_sum,transpose_smul,(coefficient_symmetric _).eq]
    have ss : (θ • vecMulVec v v + W x).IsSymm := by
      unfold Matrix.IsSymm
      rw [transpose_add,transpose_smul,transpose_vecMulVec,sym.eq]
    obtain ⟨a,z,hz,ez,bw⟩ := exists_top_unit (W x) sym
    obtain ⟨b,y,hy,ey,bs,ov⟩ := exists_oriented_top _ ss v (fun b y hy ey bs =>
      (h a b θ z y pos ez hz hy ey bw bs).2.1)
    have facts := h a b θ z y pos ez hz hy ey bw bs
    have eq : u x=y := selectSpike_eq (W x) y v θ a b pos ov hy facts.1 ey bw bs
    rw [eq]
    exact ⟨hy,ov,facts.2.2,b,ey,bs⟩
end Cov
end SpikePhase

namespace SpikePhase.Cov
open Matrix Finset MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def realNoiseScale (ι : Type*) [Fintype ι] : ℝ :=
  (Real.sqrt (2*((Fintype.card ι : ℝ)+1)))⁻¹

noncomputable def realNoiseCoeff (j : ι × ι) : Matrix ι ι ℝ :=
  realNoiseScale ι • symEdge j.1 j.2

theorem realNoise_realizes (H : Matrix ι ι ℝ) (sym : H.transpose=H) :
    ∃ g : ι × ι → ℝ, ∑ j, g j • realNoiseCoeff j=H := by
  have pos : 0 < realNoiseScale ι := by unfold realNoiseScale; positivity
  refine ⟨fun q => H q.1 q.2 / 2 / realNoiseScale ι,?_⟩
  simp only [realNoiseCoeff,smul_smul,div_mul_cancel₀ _ pos.ne',Fintype.sum_prod_type]
  exact sum_sym H sym

theorem realNoise_cyclic (n k : ℕ) (r : Fin k ≃ Fin n × Fin n) :
    let v : Fin n → ℝ := fun a => if a.val=0 then 1 else 0
    ∀ᵐ x ∂Measure.pi (fun _ : Fin k => gaussianReal 0 1),
      (Matrix.of fun i j : Fin n => (((∑ h, x h • realNoiseCoeff (r h))^j.val).mulVec v) i).det ≠ 0 := by
  intro v
  have sym : (pathMatrix n).transpose=pathMatrix n := by
    ext i j; simp [pathMatrix,Matrix.transpose_apply,or_comm]
  obtain ⟨g,hg⟩ := realNoise_realizes (pathMatrix n) sym
  apply gaussian_krylov_nonzero k (fun j => realNoiseCoeff (r j)) Fin.val (fun _ => v) (g ∘ r)
  simp only [Function.comp_apply]
  rw [(r.sum_comp (fun j => g j • realNoiseCoeff j)).trans hg]
  exact (path_krylov_det n).trans_ne one_ne_zero

theorem realNoise_oriented_top (n k : ℕ) [Nonempty (Fin n)] (r : Fin k ≃ Fin n × Fin n)
    (θ : ℝ) (pos : 0 < θ) :
    let v : Fin n → ℝ := fun a => if a.val=0 then 1 else 0
    let W := fun x : Fin k → ℝ => ∑ j, x j • realNoiseCoeff (r j)
    let u := fun x => selectSpike θ v (W x)
    Measurable u ∧ ∀ᵐ x ∂Measure.pi (fun _ : Fin k => gaussianReal 0 1),
      u x ⬝ᵥ u x=1 ∧ 0 < v ⬝ᵥ u x ∧ ∃ b,
        (θ • vecMulVec v v + W x).mulVec (u x)=b • u x ∧
        ∀ y, y ⬝ᵥ (θ • vecMulVec v v + W x).mulVec y ≤ b*(y ⬝ᵥ y) := by
  intro v W u
  constructor
  · exact (measurable_selectSpike θ v).comp (show Continuous W by dsimp [W]; fun_prop).measurable
  · filter_upwards [realNoise_cyclic n k r] with x full
    have sym : (W x).IsSymm := by
      unfold Matrix.IsSymm W realNoiseCoeff symEdge
      simp [transpose_sum,transpose_smul,transpose_add,transpose_single,add_comm]
    have ss : (θ • vecMulVec v v + W x).IsSymm := by
      unfold Matrix.IsSymm; rw [transpose_add,transpose_smul,transpose_vecMulVec,sym.eq]
    obtain ⟨a,z,hz,ez,bw⟩ := exists_top_unit (W x) sym
    have nz : z ≠ 0 := by rintro rfl; simp at hz
    obtain ⟨_,ov⟩ := eigenvector_hits_seed (W x) sym Fin.val (fun _ => v) full z nz a ez
    rw [dotProduct_comm] at ov
    obtain ⟨b,y,hy,ey,bs,vy⟩ := exists_oriented_top _ ss v (fun b y hy ey bs =>
      (spiked_top_overlap (W x) v z y θ a b pos hz hy ov ez ey bw bs).2)
    have gap := (spiked_top_overlap (W x) v z y θ a b pos hz hy ov ez ey bw bs).1
    have eq : u x=y := selectSpike_eq (W x) y v θ a b pos vy hy gap ey bw bs
    rw [eq]; exact ⟨hy,vy,b,ey,bs⟩
end SpikePhase.Cov

namespace SpikePhase.Cov
open Matrix Finset OMA.S_arxiv_2606_14687
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realNoise_covariance (U : Matrix ι ι ℂ) :
    (∑ j : ι × ι, (realNoiseCoeff j).map Complex.ofReal * U * (realNoiseCoeff j).map Complex.ofReal) =
    ((Fintype.card ι : ℂ)+1)⁻¹ • (U.transpose + diagonal (fun _ : ι => U.trace)) := by
  have mapj (j : ι × ι) : (realNoiseCoeff j).map Complex.ofReal =
      ((realNoiseScale ι : ℝ) : ℂ) • SpikeGOE.goeEdge j.1 j.2 := by
    ext a b; simp [realNoiseCoeff,symEdge,SpikeGOE.goeEdge,Matrix.smul_apply,
      Matrix.single_apply,apply_ite Complex.ofReal,mul_add,mul_ite]
  have scaleEq : (realNoiseScale ι)^2*2=((Fintype.card ι : ℝ)+1)⁻¹ := by
    rw [realNoiseScale,inv_pow,Real.sq_sqrt (by positivity)]
    field_simp
  have e := congrArg Complex.ofReal scaleEq
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_inv,
    Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] at e
  simp only [mapj,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← pow_two,← Finset.smul_sum,
    Fintype.sum_prod_type,SpikeGOE.goe_covariance_formula,e]

theorem realNoise_isotropic {d k : ℕ} (r : Fin k ≃ Fin d × Fin d) :
    ∑ j, realNoiseCoeff (r j)*realNoiseCoeff (r j)=1 := by
  rw [r.sum_comp (fun q => realNoiseCoeff q * realNoiseCoeff q)]
  have cov := realNoise_covariance (1 : Matrix (Fin d) (Fin d) ℂ)
  ext i l
  have h := congrFun (congrFun cov i) l
  apply Complex.ofReal_injective
  simp only [mul_one,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,transpose_one,Matrix.add_apply,
    diagonal_apply,trace_one,Fintype.card_fin,Matrix.mul_apply,Matrix.map_apply] at h
  simp only [Matrix.sum_apply,Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [h]
  by_cases e : i=l <;> simp [Matrix.one_apply,e,add_comm] <;> field_simp

theorem realNoise_covariance_bound {d k : ℕ} (r : Fin k ≃ Fin d × Fin d) :
    boundsCovariance (fun j => realNoiseCoeff (r j)) (2*realNoiseScale (Fin d)) := by
  have hn : 0 < realNoiseScale (Fin d) := by unfold realNoiseScale; positivity
  refine ⟨by positivity,fun B => ?_⟩
  change (∑ j, (pairing (realNoiseCoeff (r j)) B)^2) ≤ _
  rw [r.sum_comp (fun q => (pairing (realNoiseCoeff q) B)^2),Fintype.sum_prod_type]
  have pair i j : pairing (realNoiseCoeff (i,j)) B=realNoiseScale (Fin d)*(B i j+B j i) := by
    rw [← pairSym]
    simp [pairing,realNoiseCoeff,Matrix.smul_apply,Finset.mul_sum,mul_assoc]
  simp_rw [pair,mul_pow,← Finset.mul_sum]
  have e : (∑ i, ∑ j, (B i j+B j i)^2) ≤ 4*(∑ i, ∑ j, B i j^2) := calc
    _ ≤ ∑ i, ∑ j, (2*(B i j)^2+2*(B j i)^2) := by
      gcongr with i _ j _; nlinarith [sq_nonneg (B i j-B j i)]
    _ = _ := by
      simp_rw [Finset.sum_add_distrib,← Finset.mul_sum]
      rw [Finset.sum_comm (f := fun i j => B j i ^ 2)]; ring
  calc
    _ ≤ (realNoiseScale (Fin d))^2 * (4 * ∑ i, ∑ j, B i j^2) := by gcongr
    _ = _ := by ring
end SpikePhase.Cov


namespace SpikePhase.Cov
open Matrix Finset OMA.S_arxiv_2606_14687 PhaseOptimizer
variable {d k : ℕ}

/-- The true covariance of the real input family, in the problem's complex SDP. -/
theorem real_project_covariance (r : Fin k ≃ Fin d × Fin d) (U : CMat d) :
    covarianceMap (fun j => realNoiseCoeff (r j)) U =
      ((d : ℂ)+1)⁻¹ • (U.transpose + diagonal (fun _ => U.trace)) := by
  change (∑ j, (realNoiseCoeff (r j)).map Complex.ofReal * U *
    (realNoiseCoeff (r j)).map Complex.ofReal) = _
  rw [r.sum_comp (fun q => (realNoiseCoeff q).map Complex.ofReal * U * (realNoiseCoeff q).map Complex.ofReal)]
  simpa using realNoise_covariance U

/-- For trace-one fixed points the trace term cancels. Each difference
entry then equals a strict contraction times its transposed entry. -/
theorem real_fixed_unique (r : Fin k ≃ Fin d × Fin d) (z : Fin d → ℝ)
    (hz : ∀ i, 0 < z i) (small : ∀ i, (z i)^2 < (d:ℝ)+1)
    (U V : CMat d) (tr : U.trace=V.trace)
    (fu : U=diagReal z*covarianceMap (fun j => realNoiseCoeff (r j)) U*diagReal z)
    (fv : V=diagReal z*covarianceMap (fun j => realNoiseCoeff (r j)) V*diagReal z) : U=V := by
  let c i j := z i*z j/((d:ℝ)+1)
  have delta (i j : Fin d) : U i j-V i j = (c i j : ℂ)*(U j i-V j i) := by
    have hu := congrFun (congrFun fu i) j
    have hv := congrFun (congrFun fv i) j
    simp only [real_project_covariance,diagReal,diagonal_mul,mul_diagonal,Matrix.smul_apply,
      smul_eq_mul,Matrix.add_apply,Matrix.transpose_apply,tr] at hu hv
    dsimp [c]; push_cast; rw [div_eq_mul_inv]
    linear_combination hu - hv
  ext i j
  have h := delta i j
  conv_rhs at h => rw [delta j i]
  have cs : c j i = c i j := by simp [c,mul_comm]
  rw [cs] at h
  have le : c i j < 1 := (div_lt_one (by positivity)).mpr (by
    nlinarith [small i,small j,sq_nonneg (z i-z j)])
  have cp : 0 < c i j := div_pos (mul_pos (hz i) (hz j)) (by positivity)
  have nonzero : (1-(c i j : ℂ)*(c i j : ℂ))≠0 := by
    exact_mod_cast (show (1-c i j*c i j)≠0 by nlinarith [mul_pos (sub_pos.mpr le) (add_pos cp zero_lt_one)])
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (_ : (1-(c i j : ℂ)*(c i j : ℂ))*(U i j - V i j)=0)).resolve_left nonzero
  linear_combination h
end SpikePhase.Cov

namespace SpikePhase.Cov
open Matrix Finset OMA.S_arxiv_2606_14687 PhaseOptimizer
variable {d k : ℕ}

/-- Real GOE completion of the optimizer hypothesis in odd dimensions,
including a uniform lower bound for every coordinate's predicted variance. -/
theorem real_project_optimizer (r : Fin k ≃ Fin d × Fin d) (a : Fin d) {θ : ℝ}
    (hθ : 0 ≤ θ) :
    let A := fun j => realNoiseCoeff (r j)
    ∃ s : Fin d → ℝ, s ∈ stdSimplex ℝ (Fin d) ∧
      (∀ i, (1/(θ+2))^2 / ((d:ℝ)+1) ≤ s i) ∧
      dualOptimizer (θ • projector (Pi.single a 1)) A (diagReal s) ∧
      ∀ U, dualOptimizer (θ • projector (Pi.single a 1)) A U → U=diagReal s := by
  intro A
  let P := fun i j : Fin d => ((if i=j then 1 else 0)+1 : ℝ)/((d:ℝ)+1)
  have dp : 0 < (d:ℝ)+1 := by positivity
  have pos (i j) : 0 < P i j := by unfold P; split_ifs <;> positivity
  have sym (i j) : P i j=P j i := by simp [P,eq_comm]
  have row (i) : ∑ j, P i j=1 := by
    simp [P,← sum_div,sum_add_distrib,eq_comm]; field_simp; ring
  have mixeq (s : Fin d → ℝ) i : mix P s i=(s i+∑ j,s j)/((d:ℝ)+1) := by
    simp [mix,P,div_mul_eq_mul_div,add_mul,ite_mul,← sum_div,sum_add_distrib]
  have pres (s : Fin d → ℝ) : covarianceMap A (diagReal s)=diagReal (mix P s) := by
    rw [show A=(fun j => realNoiseCoeff (r j)) from rfl,real_project_covariance]
    ext i j
    by_cases e : i=j
    · subst j; simp [diagReal,Matrix.smul_apply,mixeq,div_eq_inv_mul,Complex.ofReal_sum]
    · simp [diagReal,Matrix.smul_apply,e,Ne.symm e]
  have readD (U : CMat d) i : ((covarianceMap A U) i i).re=mix P (fun j => (U j j).re) i := by
    rw [show A=(fun j => realNoiseCoeff (r j)) from rfl,real_project_covariance,mixeq]
    have e : ((d:ℂ)+1)⁻¹ = (((d:ℝ)+1)⁻¹ : ℝ) := by push_cast; rfl
    rw [e]
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.transpose_apply,diagonal_apply_eq,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re,div_eq_inv_mul]
    congr 1
    simp [Matrix.trace,Matrix.diag_apply]
  obtain ⟨s,z,hs,hp,hz,hf,_,opt,fix⟩ := actual_dual_certificate_with_multiplier A P
    (fun i j => (pos i j).le) sym row (fun i j => ⟨a,pos _ _,pos _ _⟩) pres readD a hθ
  have scalar i : s i*((d:ℝ)+1)=(z i)^2*(s i+1) := by
    have h := hf i
    rw [mixeq,hs.2,← mul_div_assoc,eq_div_iff dp.ne'] at h
    exact h
  refine ⟨s,hs,?_,opt,?_⟩
  · intro i
    apply (div_le_iff₀ dp).mpr
    rw [scalar]
    calc
      _ ≤ (z i)^2 := by gcongr; exact (hz i).2
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (z i)) (hp i).le]
  · intro U hU
    apply real_fixed_unique r z (fun i => (hz i).1) _ U _ _ (fix U hU) (fix _ opt)
    · intro i
      by_contra! bad
      have h := mul_le_mul_of_nonneg_left bad (hp i).le
      nlinarith [scalar i,sq_pos_of_pos (hz i).1]
    · rw [hU.choose_spec.1.1,opt.choose_spec.1.1]
end SpikePhase.Cov


namespace SpikePhase
open Matrix OMA.S_arxiv_2606_14687 PhaseOptimizer Filter
open scoped Topology

noncomputable def varianceRow {d : ℕ} (b : Fin d) (s : Fin d → ℝ) : Matrix (Fin 1) (Fin d) ℝ :=
  fun _ => Pi.single b (Real.sqrt ((d:ℝ)*s b))⁻¹

theorem varianceRow_action {d : ℕ} (b : Fin d) (s x : Fin d → ℝ) (i : Fin 1) :
    ((varianceRow b s).mulVec x) i = (Real.sqrt ((d:ℝ)*s b))⁻¹*x b := by
  exact single_dotProduct (v := x) _ b

theorem varianceRow_signal {d : ℕ} (a b : Fin d) (diff : b≠a) (s : Fin d → ℝ) :
    (varianceRow b s).mulVec (Pi.single a 1)=0 := by
  ext i; simp [varianceRow_action,Pi.single_apply,diff,Ne.symm diff]

theorem varianceRow_covariance {d : ℕ} (a b : Fin d) (diff : b≠a) (s : Fin d → ℝ)
    (pos : 0 < (d:ℝ)*s b) (θ : ℝ) (i j : Fin 1) :
    (d:ℝ)*(varianceRow b s * predictedCov θ (Pi.single a 1) (diagReal s) *
      (varianceRow b s).transpose) i j = 1 := by
  let C := predictedCov θ (Pi.single a 1) (diagReal s)
  have cb : C b b=s b := by
    change (diagReal s b b).re - (1-θ⁻¹^2)*((Pi.single a 1 : Vec d) b * (Pi.single a 1 : Vec d) b)=s b
    simp [diagReal,Pi.single_apply,diff]
  let q := (Real.sqrt ((d:ℝ)*s b))⁻¹
  have e l : ((varianceRow b s)*C) i l = q*C b l :=
    single_dotProduct (v := fun h => C h l) _ _
  change (d:ℝ)*(((varianceRow b s)*C)*(varianceRow b s).transpose) i j = 1
  have e' : (((varianceRow b s)*C)*(varianceRow b s).transpose) i j = (((varianceRow b s)*C) i) b*q :=
    dotProduct_single (v := ((varianceRow b s)*C) i) _ _
  rw [e',e,cb]
  dsimp [q]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr pos)]
  nlinarith [Real.sq_sqrt pos.le]

theorem varianceRow_bound {d : ℕ} (b : Fin d) (s x : Fin d → ℝ)
    (lower : (1:ℝ)/512 ≤ (d:ℝ)*s b) :
    realDot ((varianceRow b s).mulVec x) ((varianceRow b s).mulVec x) ≤ 32^2*realDot x x := by
  have pos : 0 < (d:ℝ)*s b := by linarith
  have sq := Real.sq_sqrt pos.le
  have hroot := Real.sqrt_pos.mpr pos
  have q : (Real.sqrt ((d:ℝ)*s b))⁻¹ ^ 2 ≤ (32:ℝ)^2 := by
    rw [inv_pow,sq]
    apply (inv_le_comm₀ pos (by norm_num : (0:ℝ)<32^2)).mpr
    norm_num at *; linarith
  have le : x b*x b ≤ ∑ j, x j*x j := Finset.single_le_sum (f := fun j => x j*x j)
    (fun j _ => mul_self_nonneg _) (Finset.mem_univ b)
  simp only [realDot,varianceRow_action,Fin.sum_univ_one]
  nlinarith [mul_le_mul_of_nonneg_right q (sq_nonneg (x b)),mul_le_mul_of_nonneg_left le (by norm_num : (0:ℝ)≤32^2)]

theorem covariance_log_decay :
    Tendsto (fun n : ℕ => (2 / Real.sqrt ((n:ℝ)+1)) * Real.log ((n:ℝ)+1)^(3/2:ℝ))
      atTop (𝓝 0) := by
  have t : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_rpow_atTop (3/2) (by norm_num : 0<(1/2:ℝ))).tendsto_div_nhds_zero.comp t
  simpa [Function.comp_def,Real.sqrt_eq_rpow,div_eq_mul_inv,mul_left_comm,mul_comm,mul_assoc]
    using h.const_mul (2:ℝ)

theorem even_cf_obstruction (F : ℕ → ℂ) (h : ∀ n, F (2*n+3) = 1) :
    ¬ Tendsto F atTop (𝓝 (Complex.exp ((-(1:ℝ)/2 : ℝ) : ℂ))) := by
  intro bad
  have f : StrictMono (fun n : ℕ => 2*n+3) := by intro i j h; change 2*i+3<2*j+3; omega
  have e := bad.comp f.tendsto_atTop
  simp only [Function.comp_def,h] at e
  have q : (1:ℂ) = Complex.exp ((-(1:ℝ)/2 : ℝ) : ℂ) := tendsto_nhds_unique tendsto_const_nhds e
  have r : (1:ℝ) = Real.exp (-(1:ℝ)/2) := Complex.ofReal_injective (by rw [Complex.ofReal_exp]; exact q)
  have hh : Real.exp (-(1:ℝ)/2)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact (ne_of_gt hh) r
end SpikePhase


namespace SpikePhase.Cov
open Matrix Filter MeasureTheory ProbabilityTheory OMA.S_arxiv_2606_14687

theorem top_reindex {ι : Type*} [Fintype ι] {d : ℕ} (e : ι ≃ Fin d)
    (M : Matrix ι ι ℝ) (u : ι → ℝ) (b : ℝ)
    (unit : u ⬝ᵥ u=1) (eig : M.mulVec u=b • u)
    (bound : ∀ x, x ⬝ᵥ M.mulVec x ≤ b*(x ⬝ᵥ x)) :
    isTopUnitVector (M.submatrix e.symm e.symm) (u ∘ e.symm) := by
  refine ⟨(comp_equiv_dotProduct_comp_equiv u u e.symm).trans unit,b,?_,?_⟩
  · rw [submatrix_mulVec_equiv _ _ _ e.symm]
    simp only [Equiv.symm_symm,Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id,eig]
    rfl
  · intro x
    change x ⬝ᵥ (M.submatrix e.symm e.symm).mulVec x ≤ _
    rw [submatrix_mulVec_equiv _ _ _ e.symm,dotProduct_comp_equiv_symm]
    change (x ∘ e) ⬝ᵥ M.mulVec (x ∘ e) ≤ b*(x ⬝ᵥ x)
    simpa only [comp_equiv_dotProduct_comp_equiv] using bound (x ∘ e)

theorem project_oriented_top {m d k : ℕ} [NeZero m] (e : Fin m ⊕ Fin m ≃ Fin d)
    (r : Fin k ≃ Directions (Fin m)) {θ : ℝ} (hθ : 0 < θ) :
    let a := e (.inl 0)
    let b := e (.inr 0)
    let v : Vec d := Pi.single a 1
    ∃ w : Vec k → Vec d, Measurable w ∧ ∀ᵐ x ∂standardInputs k,
      isTopUnitVector (θ • projector v + ∑ j, x j • projectFamily e r j) (w x) ∧
      0 < realDot (w x) v ∧ w x b=0 := by
  intro a b v
  let f : Fin m → ℝ := fun i => if i.val=0 then 1 else 0
  let v₀ : Fin m ⊕ Fin m → ℝ := Sum.elim f 0
  let W := fun x : Fin k → ℝ => ∑ j, x j • gaussianCoefficient (r j)
  let u := fun x => selectSpike θ v₀ (W x)
  have sig : v₀=Pi.single (.inl 0) 1 := by
    funext j
    cases j with
    | inl i =>
      by_cases h : i=0
      · subst i; simp [v₀,f]
      · have hn : i.val≠0 := fun h₀ => h (Fin.ext h₀)
        simp [v₀,f,h,hn,Pi.single_apply]
    | inr i => simp [v₀,Pi.single_apply]
  have sig' : v₀ ∘ e.symm=v := by
    ext j
    simp only [sig,Function.comp_apply,v,Pi.single_apply,a]
    simp only [e.symm_apply_eq]
  have ph : phase.mulVec v₀=Pi.single (.inr (0:Fin m)) 1 := by
    funext j
    cases j with
    | inl i => simp [phase,v₀,fromBlocks_mulVec,Pi.single_apply,neg_mulVec]
    | inr i =>
      have h := congrFun sig (.inl i)
      simpa [phase,v₀,fromBlocks_mulVec,Pi.single_apply] using h
  obtain ⟨meas,ae⟩ := gaussian_oriented_top m k r θ hθ
  refine ⟨fun x => u x ∘ e.symm,measurable_pi_lambda _ (fun j => (measurable_pi_apply (e.symm j)).comp meas),?_⟩
  filter_upwards [ae] with x hx
  obtain ⟨unit,overlap,zero,beta,eig,bound⟩ := hx
  have hmat : (θ • vecMulVec v₀ v₀ + W x).submatrix e.symm e.symm =
      θ • projector v + ∑ j, x j • projectFamily e r j := by
    ext i j
    have h i := congrFun sig' i
    simp only [Function.comp_apply] at h
    simp [Matrix.submatrix_apply,projectFamily,projector,vecMulVec,Matrix.smul_apply,W,Matrix.sum_apply,h]
  have coord : u x (.inr 0)=0 := by
    change u x ⬝ᵥ phase.mulVec v₀=0 at zero
    simpa [ph] using zero
  refine ⟨hmat ▸ top_reindex e _ _ beta unit eig bound,?_,by simpa [b] using coord⟩
  change 0 < (u x ∘ e.symm) ⬝ᵥ v
  rw [← sig',comp_equiv_dotProduct_comp_equiv,dotProduct_comm]; exact overlap
end SpikePhase.Cov


namespace SpikePhase.Cov
open Matrix MeasureTheory ProbabilityTheory Filter PhaseOptimizer OMA.S_arxiv_2606_14687
open scoped Topology
/-- The data needed at one matrix dimension. On the phase subsequence the
oriented top vector is exactly orthogonal to the measured coordinate. -/
structure Witness (d : ℕ) (silent : Prop) where
  k : ℕ
  A : Fin k → Mat d
  v : Vec d
  w : Vec k → Vec d
  S : CMat d
  R : Matrix (Fin 1) (Fin d) ℝ
  sym : ∀ j, (A j).IsSymm
  iso : ∑ j, A j*A j=1
  cov : boundsCovariance A (2/Real.sqrt d)
  unit : realDot v v=1
  meas : Measurable w
  top : ∀ᵐ g ∂standardInputs k, isTopUnitVector ((2:ℝ) • projector v+∑ j, g j • A j) (w g) ∧
    0<realDot (w g) v
  opt : dualOptimizer ((2:ℝ) • projector v) A S
  unique : ∀ U, dualOptimizer ((2:ℝ) • projector v) A U → U=S
  kill : R.mulVec v=0
  normBound : ∀ x, realDot (R.mulVec x) (R.mulVec x) ≤ 32^2*realDot x x
  variance : 2≤d → ∀ i j, (d:ℝ)*(R*predictedCov 2 v S*R.transpose) i j=1
  vanish : silent → ∀ᵐ g ∂standardInputs k, R.mulVec (w g)=0

private theorem signal_unit {d : ℕ} (a : Fin d) : realDot (Pi.single a 1) (Pi.single a 1)=1 := by
  change Pi.single a (1:ℝ) ⬝ᵥ Pi.single a 1=1
  simp

theorem phase_witness (m : ℕ) : Nonempty (Witness (2*m+4) True) := by
  classical
  let I := Fin (m+2)
  let e : I ⊕ I ≃ Fin (2*m+4) := Fintype.equivOfCardEq (by simp [I]; omega)
  let k := Fintype.card (Directions I)
  let r : Fin k ≃ Directions I := (Fintype.equivFin _).symm
  let a := e (.inl 0)
  let b := e (.inr 0)
  have diff : b≠a := by intro h; have h' := e.injective h; cases h'
  obtain ⟨s,_,low,opt,uniq⟩ := project_unique_optimizer e r (0:I) (θ:=2) (by norm_num)
  have lo : (1:ℝ)/512 ≤ ((2*m+4:ℕ):ℝ)*s b := by
    calc
      _ = ((1:ℝ)/(2+2))^4/2 := by norm_num
      _ ≤ _ := low b
  obtain ⟨w,meas,ht⟩ := project_oriented_top e r (θ:=2) (by norm_num)
  refine ⟨⟨k,projectFamily e r,Pi.single a 1,w,diagReal s,varianceRow b s,
    project_symmetric e r,project_isotropic e r,project_covariance_bound e r,
    signal_unit a,meas,?_,opt,uniq,varianceRow_signal a b diff s,
    fun x => varianceRow_bound b s x lo,fun _ => varianceRow_covariance a b diff s (by linarith) 2,?_⟩⟩
  · filter_upwards [ht] with g h using ⟨h.1,h.2.1⟩
  · intro _
    filter_upwards [ht] with g h
    ext i
    simp only [varianceRow_action,Pi.zero_apply]
    rw [show w g b=0 from h.2.2,mul_zero]

theorem real_witness (n : ℕ) : Nonempty (Witness (n+1) False) := by
  classical
  let d := n+1
  let k := Fintype.card (Fin d × Fin d)
  let r : Fin k ≃ Fin d × Fin d := (Fintype.equivFin _).symm
  let A := fun j => realNoiseCoeff (r j)
  let v : Vec d := Pi.single 0 1
  let W := fun x : Fin k → ℝ => ∑ j, x j • A j
  let w := fun x => selectSpike 2 v (W x)
  have eqv : (fun i : Fin d => if i.val=0 then (1:ℝ) else 0)=v := by
    funext i
    by_cases hi : i=0
    · subst i; simp [v]
    · have hv : i.val≠0 := fun z => hi (Fin.ext z)
      simp [v,Pi.single_apply,hi,hv]
  obtain ⟨hm,ht⟩ := realNoise_oriented_top d k r 2 (by norm_num)
  rw [eqv] at hm ht
  obtain ⟨s,_,low,opt,uniq⟩ := real_project_optimizer r (0:Fin d) (θ:=2) (by norm_num)
  have hp : 0<(d:ℝ) := by dsimp [d]; positivity
  have hcov := realNoise_covariance_bound r
  have major : 2*realNoiseScale (Fin d) ≤ 2/Real.sqrt d := by
    simp only [realNoiseScale,Fintype.card_fin,div_eq_mul_inv]
    gcongr
    linarith
  have bc : boundsCovariance A (2/Real.sqrt d) := by
    refine ⟨by positivity,fun B => (hcov.2 B).trans ?_⟩
    gcongr <;> first | exact hcov.1 | exact major | positivity
  have sym (j) : (A j).IsSymm := by
    dsimp [A,realNoiseCoeff]; apply IsSymm.smul
    ext i l; simp [symEdge,Matrix.transpose_apply,Matrix.single_apply,eq_comm,and_comm,add_comm]
  have top : ∀ᵐ x ∂standardInputs k, isTopUnitVector ((2:ℝ) • projector v+W x) (w x) ∧
      0<realDot (w x) v := by
    filter_upwards [ht] with x h
    obtain ⟨unit,overlap,b,eig,bd⟩ := h
    refine ⟨⟨unit,b,eig,bd⟩,?_⟩
    change 0<(w x) ⬝ᵥ v
    rw [dotProduct_comm]; exact overlap
  by_cases hd : 2 ≤ d
  · let b : Fin d := ⟨1,by omega⟩
    have diff : b≠0 := fun h => by have q := congrArg Fin.val h; simp [b] at q
    have lo : (1:ℝ)/512 ≤ (d:ℝ)*s b := by
      have l := low b
      norm_num at l
      have dp : 0 < (d:ℝ)+1 := by positivity
      have dl : (2:ℝ) ≤ d := by exact_mod_cast hd
      apply le_trans _ (mul_le_mul_of_nonneg_left l hp.le)
      rw [← mul_div_assoc,le_div_iff₀ dp]; linarith
    exact ⟨⟨k,A,v,w,diagReal s,varianceRow b s,sym,realNoise_isotropic r,bc,signal_unit _,hm,
      top,opt,uniq,varianceRow_signal _ _ diff s,fun x => varianceRow_bound b s x lo,
      fun _ => varianceRow_covariance _ _ diff s (by linarith) 2,False.elim⟩⟩
  · refine ⟨⟨k,A,v,w,diagReal s,0,sym,realNoise_isotropic r,bc,signal_unit _,hm,
      top,opt,uniq,by simp,?_,fun h => (hd h).elim,False.elim⟩⟩
    intro x
    simp [realDot]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
end SpikePhase.Cov


namespace SpikePhase.Cov
open Matrix MeasureTheory ProbabilityTheory Filter PhaseOptimizer OMA.S_arxiv_2606_14687
open scoped Topology
private def Witness.weaken {d : ℕ} {P Q : Prop} (D : Witness d P) (h : Q → P) : Witness d Q :=
  { D with vanish := fun q => D.vanish (h q) }

noncomputable def dimensionWitness (n : ℕ) : Witness (n+1) (∃ m, n=2*m+3) := by
  classical
  apply Nonempty.some
  by_cases h : ∃ m, n=2*m+3
  · obtain ⟨m,rfl⟩ := h
    exact ⟨(phase_witness m).some.weaken (fun _ => trivial)⟩
  · exact ⟨(real_witness n).some.weaken h⟩

theorem characteristic_on_phase {d : ℕ} {P : Prop} (D : Witness d P) (hP : P) (c a : ℝ)
    (t : Vec 1) :
    (∫ g, Complex.exp (Complex.I * ((c*realDot t (D.R.mulVec (D.w g-a • D.v))) : ℝ))
      ∂standardInputs D.k)=1 := by
  haveI : IsProbabilityMeasure (standardInputs D.k) := by unfold standardInputs; infer_instance
  have ae := D.vanish hP
  calc
    _ = ∫ _ : Vec D.k, (1:ℂ) ∂standardInputs D.k := by
      apply integral_congr_ae
      filter_upwards [ae] with g hg
      simp [Matrix.mulVec_sub,Matrix.mulVec_smul,hg,D.kill,realDot]
    _ = _ := by simp
end SpikePhase.Cov

open Matrix MeasureTheory Filter OMA.S_arxiv_2606_14687 SpikePhase SpikePhase.Cov
open scoped Topology in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2606_14687.main) := by
  intro claim
  let D := dimensionWitness
  let Γ : Mat 1 := 1
  have sy : Γ.IsSymm := Matrix.isSymm_one
  have cv (i j : Fin 1) : Tendsto (fun n : ℕ => ((n:ℝ)+1) *
      ((D n).R * predictedCov 2 (D n).v (D n).S * (D n).R.transpose) i j) atTop (𝓝 (Γ i j)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have v := (D n).variance (by omega) i j
    have e := Subsingleton.elim i j
    simpa [Γ,e] using v.symm
  let t : Vec 1 := fun _ => 1
  have limit := claim 2 (by norm_num) (fun n => (D n).k) (fun n => (D n).A) (fun n => (D n).v)
    (fun n => (D n).w) (fun n => (D n).sym) (fun n => (D n).iso)
    ⟨fun n => 2/Real.sqrt ((n:ℝ)+1),fun n => by simpa using (D n).cov,covariance_log_decay⟩
    (fun n => (D n).unit) (fun n => (D n).meas.aemeasurable) (fun n => (D n).top)
    (fun n => ⟨(D n).S,(D n).opt,(D n).unique⟩) (fun n => (D n).S) (Or.inl fun n => (D n).opt)
    1 (by decide) (fun n => (D n).R) Γ sy (fun n => (D n).kill) ⟨32,fun n => (D n).normBound⟩ cv t
  have value : realDot t (Γ.mulVec t)=1 := by simp [Γ,t,realDot]
  rw [value] at limit
  apply even_cf_obstruction _ _ limit
  intro m
  simpa only [Complex.ofReal_mul] using characteristic_on_phase (D (2*m+3)) ⟨m,rfl⟩
    (Real.sqrt (((2*m+3:ℕ):ℝ)+1)) (Real.sqrt (1-(2:ℝ)⁻¹^2)) t
