import OMAStatements.S_wpc_dixmier_unitarizability
import Mathlib
/-! Adapted from OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. This is a port, not an independent proof. -/
-- Source: OAI.Analysis.Unitarizability.Model

namespace OAI

/-! Amenability, unitarizability, and bounded nonunitarizable representations.
Representations into the endomorphism monoid have bounded inverses because
their domain is a group. Norm-preserving invertible complex linear maps on
Hilbert spaces are unitary. No bound on similarities is imposed. -/
noncomputable section
universe u v
namespace Dixmier
open scoped BoundedContinuousFunction

def leftTranslate {G : Type u} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => g⁻¹ * x, continuous_of_discreteTopology⟩

/-- A positive normalized left-invariant complex mean. -/
def Amenable (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : Prop :=
  ∃ m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ,
    m (BoundedContinuousFunction.const G 1) = 1 ∧
    (∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) ∧
    ∀ (g : G) (f : G →ᵇ ℂ), m (leftTranslate g f) = m f

def SimilarToUnitary {G : Type u} [Group G]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)) : Prop :=
  ∃ S : H ≃L[ℂ] H, ∀ (g : G) (x : H), ‖S (π g (S.symm x))‖ = ‖x‖

/-- A uniformly 101-bounded nonunitarizable representation on a separable
complete complex Hilbert space, with its universe explicit. -/
def NonamenableWitness (G : Type u) [Group G] : Prop :=
  ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
    (π : G →* (H →L[ℂ] H)),
    (∀ g : G, ‖π g‖ ≤ 101) ∧ ¬ SimilarToUnitary π

/-- Unitarizability at an explicitly quantified Hilbert-space universe. -/
def Unitarizable (G : Type u) [Group G] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) → SimilarToUnitary π

/-- Every countable discrete nonamenable group has a bounded nonunitarizable witness. -/
def MainTheorem : Prop :=
  ∀ (G : Type u) [Group G] [Countable G] [TopologicalSpace G]
    [DiscreteTopology G], ¬ Amenable G → NonamenableWitness.{u, v} G

/-- A nonunitarizable witness contradicts unitarizability. -/
theorem witness_not_unitarizable {G : Type u} [Group G]
    (h : NonamenableWitness.{u, v} G) : ¬ Unitarizable.{u, v} G := by
  rcases h with ⟨H, hnorm, hinner, hcomplete, hsep, π, hbound, hnot⟩
  intro hunit
  exact hnot (hunit H π ⟨101, hbound⟩)

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.DiscreteModel

namespace OAI

noncomputable section
namespace Dixmier
universe u v

def CurrentMainTheorem : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G],
    (Amenable G ↔ Unitarizable.{u, max u v} G) ∧
    ∀ (ε : ℝ), 0 < ε → ¬ Amenable G →
      ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
        (Countable G → TopologicalSpace.SeparableSpace H) ∧
        (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π

end Dixmier
end

end OAI

-- Source: OAI.Analysis.Unitarizability.KernelEnergy

namespace OAI

/-! Positive rank-one kernel energy. Matrices are represented by their entries
with the unnormalized Hilbert–Schmidt (Euclidean coefficient) norm. -/
noncomputable section
namespace Dixmier
open Classical
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

def rankOneCoefficients (v : EuclideanSpace ℂ K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun p => v p.1 * conj (v p.2))

omit [Fintype K] in
@[simp] theorem rankOneCoefficients_apply (v : EuclideanSpace ℂ K) (a b : K) :
    rankOneCoefficients v (a, b) = v a * conj (v b) := rfl

theorem rankOne_inner (v w : EuclideanSpace ℂ K) :
    inner ℂ (rankOneCoefficients v) (rankOneCoefficients w) =
      inner ℂ v w * conj (inner ℂ v w) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    rankOneCoefficients, map_sum, map_mul]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [← Complex.star_def, star_mul, star_star]
  ring

theorem rankOne_inner_re (v w : EuclideanSpace ℂ K) :
    (inner ℂ (rankOneCoefficients v) (rankOneCoefficients w)).re = ‖inner ℂ v w‖^2 := by
  rw [rankOne_inner, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_eq_norm_sq _

theorem rankOne_norm_sq (v : EuclideanSpace ℂ K) (hv : ‖v‖ = 1) :
    ‖rankOneCoefficients v‖^2 = 1 := by
  rw [← @inner_self_eq_norm_sq ℂ]
  change (inner ℂ (rankOneCoefficients v) (rankOneCoefficients v)).re = 1
  rw [rankOne_inner_re, inner_self_eq_norm_sq_to_K, hv]
  norm_num

/-- Collision blocks are sums of the rank-one matrices with that label value. -/
def kernelCoefficients (v : I → EuclideanSpace ℂ K) (s : I → G) (g : G) :
    EuclideanSpace ℂ (K × K) :=
  ∑ i ∈ (Finset.univ.filter fun i => s i = g), rankOneCoefficients (v i)

omit [Fintype I] in
/-- Positivity of every pairwise Hilbert–Schmidt inner product makes each
block’s energy at least the number of its unit rank-one summands. -/
theorem rankOne_sum_energy (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (J : Finset I) : (J.card : ℝ) ≤ ‖∑ i ∈ J, rankOneCoefficients (v i)‖^2 := by
  rw [← @inner_self_eq_norm_sq ℂ]
  simp only [sum_inner, inner_sum, map_sum]
  calc
    (J.card : ℝ) = ∑ i ∈ J, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ J, ∑ j ∈ J, (inner ℂ (rankOneCoefficients (v j)) (rankOneCoefficients (v i))).re := by
      apply Finset.sum_le_sum
      intro i hi
      have he : (inner ℂ (rankOneCoefficients (v i)) (rankOneCoefficients (v i))).re = 1 := by
        change RCLike.re (inner ℂ (rankOneCoefficients (v i)) (rankOneCoefficients (v i))) = 1
        rw [inner_self_eq_norm_sq, rankOne_norm_sq _ (hv i)]
      rw [← he]
      apply Finset.single_le_sum (f := fun j => (inner ℂ (rankOneCoefficients (v j)) (rankOneCoefficients (v i))).re) _ hi
      intro j hj
      rw [rankOne_inner_re]
      positivity

def coefficientMatrix (W : EuclideanSpace ℂ (K × K)) : Matrix K K ℂ :=
  fun a b => W (a,b)

/-- The coefficient norm is the unnormalized trace definition of
Hilbert–Schmidt squared norm. -/
theorem coefficient_norm_sq_eq_trace (W : EuclideanSpace ℂ (K × K)) :
    ‖W‖^2 = (Matrix.trace (Matrix.conjTranspose (coefficientMatrix W) * coefficientMatrix W)).re := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coefficientMatrix, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, Fintype.sum_prod_type]
  simp only [← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.sum_comm (f := fun (a b : K) => ‖W (a,b)‖^2)

omit [Fintype K] in
theorem kernelCoefficients_offsupport (v : I → EuclideanSpace ℂ K) (s : I → G)
    {g : G} (hg : g ∉ Finset.univ.image s) : kernelCoefficients v s g = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  exact (hg (Finset.mem_image.mpr ⟨i, mem_univ _, (mem_filter.mp hi).2⟩)).elim

theorem kernel_energy_summable (v : I → EuclideanSpace ℂ K) (s : I → G) :
    Summable (fun g => ‖kernelCoefficients v s g‖^2) := by
  classical
  apply summable_of_ne_finset_zero (s := Finset.univ.image s)
  intro g hg
  simp [kernelCoefficients_offsupport v s hg]

/-- The kernel-energy lower bound preserves every colliding product label. -/
theorem kernel_energy_ge_card (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (s : I → G) : (Fintype.card I : ℝ) ≤ ∑' g, ‖kernelCoefficients v s g‖^2 := by
  classical
  rw [tsum_eq_sum (s := Finset.univ.image s) (fun g hg => by
    simp [kernelCoefficients_offsupport v s hg])]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_eq_sum_card_image s Finset.univ)
  simp only [Finset.card_univ, Nat.cast_sum] at hc
  calc
    (Fintype.card I : ℝ) = ∑ g ∈ Finset.univ.image s, ((Finset.univ.filter fun i => s i = g).card : ℝ) := hc
    _ ≤ ∑ g ∈ Finset.univ.image s, ‖kernelCoefficients v s g‖^2 := by
      apply Finset.sum_le_sum
      intro g hg
      exact rankOne_sum_energy v hv _

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.KernelObstruction

namespace OAI

/-! Coordinate maps and the invariant-kernel obstruction.
The Hilbert space is the lp space with finite Euclidean fibres. -/
noncomputable section
namespace Dixmier
namespace KernelObstruction
open scoped ComplexConjugate
open Finset
variable {G K : Type*} [Fintype K]
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq K := Classical.decEq K

abbrev Fibre (K : Type*) [Fintype K] := EuclideanSpace ℂ K
abbrev Space (G K : Type*) [Fintype K] := lp (fun _ : G => Fibre K) 2
abbrev Op (G K : Type*) [Fintype K] := Space G K →L[ℂ] Space G K

def inclusion (x : G) : Fibre K →L[ℂ] Space G K :=
  lp.singleContinuousLinearMap ℂ (fun _ : G => Fibre K) 2 x

def evaluation (x : G) : Space G K →L[ℂ] Fibre K :=
  lp.evalCLM ℂ (fun _ : G => Fibre K) 2 x

@[simp] theorem inclusion_apply (x : G) (v : Fibre K) :
    inclusion x v = lp.single 2 x v := rfl
@[simp] theorem evaluation_apply (x : G) (ξ : Space G K) :
    evaluation x ξ = ξ x := rfl

@[simp] theorem inclusion_norm (x : G) (v : Fibre K) : ‖inclusion x v‖ = ‖v‖ :=
  lp.norm_single (p := 2) (E := fun _ : G => Fibre K) (by norm_num) x v

theorem inclusion_opNorm_le (x : G) : ‖inclusion (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem evaluation_opNorm_le (x : G) : ‖evaluation (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) ξ x

@[simp] theorem inclusion_adjoint (x : G) :
    (inclusion (K := K) x).adjoint = evaluation x := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 x v) ξ = inner ℂ v (ξ x)
  exact lp.inner_single_left (𝕜 := ℂ) (G := fun _ : G => Fibre K) x v ξ

@[simp] theorem evaluation_inclusion (x : G) :
    (evaluation (K := K) x).comp (inclusion x) = ContinuousLinearMap.id ℂ (Fibre K) := by
  ext v a
  simp

def block (F : Op G K) (x y : G) : Fibre K →L[ℂ] Fibre K :=
  (evaluation x).comp (F.comp (inclusion y))

def row (F : Op G K) (x : G) : Space G K →L[ℂ] Fibre K :=
  (evaluation x).comp F

def col (F : Op G K) (y : G) : Fibre K →L[ℂ] Space G K :=
  F.comp (inclusion y)

def coefficients (B : Fibre K →L[ℂ] Fibre K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun ab => (B (EuclideanSpace.basisFun K ℂ ab.2)) ab.1)

@[simp] theorem coefficients_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B (a,b) = (B (EuclideanSpace.basisFun K ℂ b)) a := rfl

theorem coefficients_norm_sq (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B‖^2 = ∑ b : K, ‖B (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, coefficients_apply]
  exact Finset.sum_comm

theorem space_norm_sq (ξ : Space G K) : ‖ξ‖^2 = ∑' x, ‖ξ x‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem space_summable (ξ : Space G K) : Summable (fun x => ‖ξ x‖^2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem column_summable (L : Fibre K →L[ℂ] Space G K) :
    Summable (fun x => ‖coefficients ((evaluation x).comp L)‖^2) := by
  simp_rw [coefficients_norm_sq]
  exact summable_sum (fun b _ => space_summable (L (EuclideanSpace.basisFun K ℂ b)))

theorem column_energy (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 =
      ∑ b : K, ‖L (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp_rw [coefficients_norm_sq]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro b hb
    exact (space_norm_sq _).symm
  · intro b hb
    exact space_summable _

theorem column_energy_le (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 ≤
      (Fintype.card K : ℝ) * ‖L‖^2 := by
  rw [column_energy]
  calc
    _ ≤ ∑ b : K, ‖L‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have h := L.le_opNorm (EuclideanSpace.basisFun K ℂ b)
      simp only [(EuclideanSpace.basisFun K ℂ).norm_eq_one, mul_one] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by simp [nsmul_eq_mul]


theorem coefficients_adjoint_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B.adjoint (a,b) = conj (coefficients B (b,a)) := by
  simp only [coefficients_apply]
  rw [← EuclideanSpace.basisFun_inner, ← EuclideanSpace.basisFun_inner]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem coefficients_adjoint_norm (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B.adjoint‖ = ‖coefficients B‖ := by
  have h : ‖coefficients B.adjoint‖^2 = ‖coefficients B‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      coefficients_adjoint_apply, RCLike.norm_conj]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (coefficients B.adjoint), norm_nonneg (coefficients B)]

theorem row_block_norm (R : Space G K →L[ℂ] Fibre K) (x : G) :
    ‖coefficients (R.comp (inclusion x))‖ =
      ‖coefficients ((evaluation x).comp R.adjoint)‖ := by
  rw [← coefficients_adjoint_norm (R.comp (inclusion x)),
    ContinuousLinearMap.adjoint_comp, inclusion_adjoint]

theorem row_summable (R : Space G K →L[ℂ] Fibre K) :
    Summable (fun x => ‖coefficients (R.comp (inclusion x))‖^2) := by
  simp_rw [row_block_norm]
  exact column_summable R.adjoint

theorem row_energy_le (R : Space G K →L[ℂ] Fibre K) :
    ∑' x, ‖coefficients (R.comp (inclusion x))‖^2 ≤
      (Fintype.card K : ℝ) * ‖R‖^2 := by
  simp_rw [row_block_norm]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using column_energy_le R.adjoint

variable [Group G]

def reindex (e : G ≃ G) (ξ : Space G K) : Space G K :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

omit [Group G] in
theorem reindex_norm (e : G ≃ G) (ξ : Space G K) : ‖reindex e ξ‖ = ‖ξ‖ := by
  have h : ‖reindex e ξ‖^2 = ‖ξ‖^2 := by
    rw [space_norm_sq, space_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖^2)
  nlinarith [norm_nonneg (reindex e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : Space G K →ₗᵢ[ℂ] Space G K where
  toFun := reindex e
  map_add' ξ η := by ext x a; rfl
  map_smul' z ξ := by ext x a; rfl
  norm_map' := reindex_norm e

/-- The fibre-valued left regular representation. -/
def translation : G →* Op G K where
  toFun g := (reindexIsometry (K := K) (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x a; simp [reindexIsometry, reindex]
  map_mul' g h := by ext ξ x a; simp [reindexIsometry, reindex]

@[simp] theorem translation_apply (g : G) (ξ : Space G K) (x : G) :
    translation g ξ x = ξ (g⁻¹ * x) := rfl

@[simp] theorem translation_inclusion (g y : G) (v : Fibre K) :
    translation g (inclusion y v) = inclusion (g*y) v := by
  ext x a
  simp only [translation_apply, inclusion_apply, lp.single_apply]
  by_cases h : x = g*y
  · subst x
    simp
  · have h' : g⁻¹*x ≠ y := by intro he; apply h; rw [← he]; simp
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

def Commutant : Set (Op G K) := {F | ∀ g, Commute F (translation g)}

theorem block_invariant {F : Op G K} (hF : F ∈ Commutant) (g x y : G) :
    block F (g*x) (g*y) = block F x y := by
  ext v a
  have h := congrArg (fun B : Op G K => B (inclusion y v) (g*x)) (hF g).eq
  simp only [mul_apply_eq_comp, translation_inclusion, translation_apply,
    inv_mul_cancel_left] at h
  exact congrArg (fun v : Fibre K => v a) h

theorem block_kernel {F : Op G K} (hF : F ∈ Commutant) (x y : G) :
    block F x y = block F 1 (x⁻¹*y) := by
  simpa only [mul_one, mul_inv_cancel_left] using block_invariant hF x 1 (x⁻¹*y)



omit [Group G] in
@[simp] theorem block_sub (A C : Op G K) (x y : G) :
    block (A-C) x y = block A x y - block C x y := by
  ext v a
  rfl

@[simp] theorem coefficients_sub (A C : Fibre K →L[ℂ] Fibre K) :
    coefficients (A-C) = coefficients A - coefficients C := by ext ab; rfl

theorem commutant_sub {A C : Op G K} (hA : A ∈ Commutant) (hC : C ∈ Commutant) :
    A-C ∈ Commutant := by
  intro g
  change (A-C) * translation g = translation g * (A-C)
  simp only [sub_mul, mul_sub, (hA g).eq, (hC g).eq]

def energy (A : Op G K) : ℝ := ∑' s, ‖coefficients (block A 1 s)‖^2

theorem energy_summable (A : Op G K) :
    Summable (fun s => ‖coefficients (block A 1 s)‖^2) :=
  row_summable (row A 1)

theorem energy_nonneg (A : Op G K) : 0 ≤ energy A := tsum_nonneg (fun _ => sq_nonneg _)

theorem energy_le_row (A : Op G K) :
    energy A ≤ (Fintype.card K : ℝ) * ‖row A 1‖^2 :=
  row_energy_le (row A 1)

theorem energy_eq_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A = ∑' x, ‖coefficients ((evaluation x).comp (col A 1))‖^2 := by
  change (∑' s, ‖coefficients (block A 1 s)‖^2) = ∑' x, ‖coefficients (block A x 1)‖^2
  simp_rw [block_kernel hA _ 1, mul_one]
  exact ((Equiv.inv G).tsum_eq (fun s => ‖coefficients (block A 1 s)‖^2)).symm

theorem energy_le_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A ≤ (Fintype.card K : ℝ) * ‖col A 1‖^2 := by
  rw [energy_eq_column hA]
  exact column_energy_le _

omit [Group G] in
theorem row_norm_le (F : Op G K) (x : G) : ‖row F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (evaluation_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem col_norm_le (F : Op G K) (x : G) : ‖col F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (inclusion_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem row_difference_bound (T C : Op G K) (x : G) :
    ‖row C x‖ ≤ ‖row T x‖ + ‖T-C‖ := by
  have h : row C x = row T x - row (T-C) x := by ext v a; simp [row]
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) (row_norm_le _ _))

omit [Group G] in
theorem col_difference_bound (A T C : Op G K) (x : G) :
    ‖col (A-C) x‖ ≤ ‖col (A-T) x‖ + ‖T-C‖ := by
  have h : col (A-C) x = col (A-T) x + col (T-C) x := by
    ext v y a
    simp [col]
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (le_refl _) (col_norm_le _ _))

theorem energy_split_le (A C : Op G K) : energy A ≤ 2 * energy C + 2 * energy (A-C) := by
  have hp (s : G) : ‖coefficients (block A 1 s)‖^2 ≤
      2 * ‖coefficients (block C 1 s)‖^2 + 2 * ‖coefficients (block (A-C) 1 s)‖^2 := by
    rw [block_sub, coefficients_sub]
    have ht := norm_add_le (coefficients (block C 1 s))
      (coefficients (block A 1 s) - coefficients (block C 1 s))
    rw [add_sub_cancel] at ht
    nlinarith [norm_nonneg (coefficients (block A 1 s)),
      norm_nonneg (coefficients (block C 1 s)),
      norm_nonneg (coefficients (block A 1 s) - coefficients (block C 1 s)),
      sq_nonneg (‖coefficients (block C 1 s)‖ -
        ‖coefficients (block A 1 s) - coefficients (block C 1 s)‖)]
  have hs := ((energy_summable C).mul_left 2).add ((energy_summable (A-C)).mul_left 2)
  have h := (energy_summable A).tsum_le_tsum hp hs
  rw [((energy_summable C).mul_left 2).tsum_add ((energy_summable (A-C)).mul_left 2),
    tsum_mul_left, tsum_mul_left] at h
  exact h

/-- The kernel-energy obstruction, proved from coordinate estimates and commutation. -/
theorem kernel_obstruction {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (_hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ)
    {C : Op G K} (hC : C ∈ Commutant) :
    energy A ≤ 4 * (Fintype.card K : ℝ) * (κ + ‖T-C‖)^2 := by
  have hR : ‖row C 1‖ ≤ κ + ‖T-C‖ :=
    (row_difference_bound T C 1).trans (add_le_add hr (le_refl _))
  have hL : ‖col (A-C) 1‖ ≤ κ + ‖T-C‖ :=
    (col_difference_bound A T C 1).trans (add_le_add hc (le_refl _))
  have heC := (energy_le_row C).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hR 2) (Nat.cast_nonneg (Fintype.card K)))
  have heAC := (energy_le_column (commutant_sub hA hC)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hL 2) (Nat.cast_nonneg (Fintype.card K)))
  nlinarith [energy_split_le A C]

/-- Pointwise distance inequality for positive fibre dimension. -/
theorem kernel_distance_pointwise [Nonempty K] {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ)
    {C : Op G K} (hC : C ∈ Commutant) :
    (1/2 : ℝ) * Real.sqrt (energy A / Fintype.card K) - κ ≤ ‖T-C‖ := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have he := kernel_obstruction hA hκ hr hc hC
  have hdiv : energy A / Fintype.card K ≤ 4 * (κ + ‖T-C‖)^2 := by
    apply (div_le_iff₀ hk).mpr
    nlinarith [he]
  have hs := Real.sq_sqrt (div_nonneg (energy_nonneg A) hk.le)
  have hh : 0 ≤ κ + ‖T-C‖ := add_nonneg hκ (norm_nonneg _)
  have hsqrt : Real.sqrt (energy A / Fintype.card K) ≤ 2 * (κ + ‖T-C‖) := by
    nlinarith [Real.sqrt_nonneg (energy A / Fintype.card K)]
  linarith

/-- The distance obstruction for the metric distance to
all bounded translation-commuting operators. -/
theorem kernel_distance [Nonempty K] {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ) :
    (1/2 : ℝ) * Real.sqrt (energy A / Fintype.card K) - κ ≤ Metric.infDist T Commutant := by
  apply (Metric.le_infDist (s := Commutant) ⟨0, fun g => Commute.zero_left _⟩).mpr
  intro C hC
  simpa only [dist_eq_norm] using kernel_distance_pointwise hA hκ hr hc hC


end KernelObstruction
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Cocycle

namespace OAI

/-! Cocycle algebra in an arbitrary ring, specializing to bounded complex Hilbert-space operators. -/
namespace Dixmier
section Ring
variable {G R : Type*} [Group G] [Ring R]

def conjugate (U : G →* R) (g : G) (T : R) : R := U g * T * U g⁻¹

@[simp] theorem conjugate_one (U : G →* R) (T : R) : conjugate U 1 T = T := by
  simp [conjugate]

theorem conjugate_mul (U : G →* R) (g h : G) (T : R) :
    conjugate U (g * h) T = conjugate U g (conjugate U h T) := by
  simp [conjugate, map_mul, mul_assoc]

theorem conjugate_sub (U : G →* R) (g : G) (A B : R) :
    conjugate U g (A - B) = conjugate U g A - conjugate U g B := by
  simp [conjugate, mul_sub, sub_mul]

def coboundary (U : G →* R) (T : R) (g : G) : R := T - conjugate U g T

@[simp] theorem coboundary_one (U : G →* R) (T : R) : coboundary U T 1 = 0 := by
  simp [coboundary]

/-- The coboundary cocycle identity, before taking direct sums. -/
theorem coboundary_cocycle (U : G →* R) (T : R) (g h : G) :
    coboundary U T (g * h) = coboundary U T g + conjugate U g (coboundary U T h) := by
  simp only [coboundary, conjugate_mul, conjugate_sub]
  abel

theorem conjugate_eq_self_iff_commute (U : G →* R) (g : G) (T : R) :
    conjugate U g T = T ↔ Commute (U g) T := by
  have hinv : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  have hginv : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  constructor
  · intro h
    have hh := congrArg (fun x : R => x * U g) h
    change U g * T = T * U g
    simpa [conjugate, mul_assoc, hinv] using hh
  · intro h
    change U g * T * U g⁻¹ = T
    rw [h.eq, mul_assoc, hginv, mul_one]

/-- Comparing the two implementers gives the commutant element T - B. -/
theorem equal_coboundaries_iff_commute_sub (U : G →* R) (T B : R) (g : G) :
    coboundary U T g = coboundary U B g ↔ Commute (U g) (T - B) := by
  rw [← conjugate_eq_self_iff_commute, conjugate_sub]
  simp only [coboundary]
  constructor
  · intro h
    calc
      conjugate U g T - conjugate U g B =
          (T - (T - conjugate U g T)) - (B - (B - conjugate U g B)) := by abel
      _ = T - B := by rw [h]; abel
  · intro h
    calc
      T - conjugate U g T = B - conjugate U g B +
          ((T - B) - (conjugate U g T - conjugate U g B)) := by abel
      _ = B - conjugate U g B := by rw [h]; abel

/-- Algebraic upper triangular operator product, without any norm assertion. -/
def triangular (a b : R) : R × R → R × R :=
  fun x => (a * x.1 + b * a * x.2, a * x.2)

theorem triangular_cocycle_mul (U : G →* R) (D : G → R)
    (hD : ∀ g h, D (g * h) = D g + conjugate U g (D h))
    (g h : G) (x : R × R) :
    triangular (U g) (D g) (triangular (U h) (D h) x) =
      triangular (U (g * h)) (D (g * h)) x := by
  have hinv : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  have hinv_assoc (z : R) : U g⁻¹ * (U g * z) = z := by
    rw [← mul_assoc, hinv, one_mul]
  simp only [triangular, map_mul, hD, conjugate, Prod.mk.injEq]
  constructor
  · simp only [add_mul, mul_add, mul_assoc, hinv_assoc]
    abel
  · simp only [mul_assoc]

end Ring
end Dixmier

end OAI

-- Source: OAI.Analysis.Unitarizability.HilbertSum

namespace OAI

/-! Uniformly bounded Hilbert direct sums. The component implementers
are never summed and need not be uniformly bounded. -/
noncomputable section
namespace Dixmier
namespace HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
local instance : DecidableEq I := Classical.decEq I
abbrev Space (E : I → Type*) [∀ i, NormedAddCommGroup (E i)] := lp E 2

def inclusion (i : I) : E i →L[ℂ] Space E := lp.singleContinuousLinearMap ℂ E 2 i

def evaluation (i : I) : Space E →L[ℂ] E i := lp.evalCLM ℂ E 2 i

@[simp] theorem inclusion_apply (i : I) (x : E i) : inclusion i x = lp.single 2 i x := rfl
@[simp] theorem evaluation_apply (i : I) (x : Space E) : evaluation i x = x i := rfl

def boundedSum (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ} (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) :
    Space E →L[ℂ] Space E := lp.mapCLM 2 T hκ hT

@[simp] theorem boundedSum_apply (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) (x : Space E) (i : I) :
    boundedSum T hκ hT x i = T i (x i) := rfl

theorem boundedSum_norm_le (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) : ‖boundedSum T hκ hT‖ ≤ κ :=
  lp.norm_mapCLM_le 2 T hκ hT

theorem unitary_bound {index : I} (U : G →* (E index →L[ℂ] E index))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) :
    ‖U g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [hU]

def representation (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) : G →* (Space E →L[ℂ] Space E) where
  toFun g := boundedSum (fun i => U i g) zero_le_one (fun i => unitary_bound (U i) (hU i) g)
  map_one' := by ext x i; change U i 1 (x i) = x i; simp
  map_mul' g h := by
    ext x i
    change U i (g*h) (x i) = U i g (U i h (x i))
    rw [map_mul]; rfl

@[simp] theorem representation_apply (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) (i : I) :
    representation U hU g x i = U i g (x i) := rfl

theorem representation_norm_map (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) :
    ‖representation U hU g x‖ = ‖x‖ := by
  have hs : ‖representation U hU g x‖^2 = ‖x‖^2 := by
    have norm_sq (y : Space E) : ‖y‖^2 = ∑' i, ‖y i‖^2 := by
      simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) y
    simp only [norm_sq, representation_apply, hU]
  nlinarith [norm_nonneg (representation U hU g x), norm_nonneg x]

def cocycle (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) : Space E →L[ℂ] Space E :=
  boundedSum (fun i => D i g) hκ (fun i => hb i g)

omit [Group G] in
@[simp] theorem cocycle_apply (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) (x : Space E) (i : I) :
    cocycle D hκ hb g x i = D i g (x i) := rfl

theorem cocycle_one (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (h1 : ∀ i, D i 1 = 0) :
    cocycle D hκ hb 1 = 0 := by ext x i; simp [h1]

theorem cocycle_identity (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ)
    (hD : ∀ i g h, D i (g*h) = D i g + conjugate (U i) g (D i h)) (g h : G) :
    cocycle D hκ hb (g*h) = cocycle D hκ hb g +
      conjugate (representation U hU) g (cocycle D hκ hb h) := by
  ext x i
  change D i (g*h) (x i) = D i g (x i) + U i g (D i h (U i g⁻¹ (x i)))
  rw [hD]
  rfl

theorem representation_inclusion (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (i : I) (x : E i) :
    representation U hU g (inclusion i x) = inclusion i (U i g x) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

def compression (B : Space E →L[ℂ] Space E) (i : I) : E i →L[ℂ] E i :=
  (evaluation i).comp (B.comp (inclusion i))

theorem compression_norm_le (B : Space E →L[ℂ] Space E) (i : I) : ‖compression B i‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  change ‖B (lp.single 2 i x) i‖ ≤ ‖B‖ * ‖x‖
  calc
    _ ≤ ‖B (lp.single 2 i x)‖ := lp.norm_apply_le_norm (by norm_num) _ i
    _ ≤ ‖B‖ * ‖lp.single 2 i x‖ := B.le_opNorm _
    _ = _ := by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem compression_conjugate (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (B : Space E →L[ℂ] Space E) (i : I) (g : G) :
    compression (conjugate (representation U hU) g B) i =
      conjugate (U i) g (compression B i) := by
  ext x
  change (representation U hU g (B (representation U hU g⁻¹ (inclusion i x)))) i = _
  rw [representation_inclusion, representation_apply]
  rfl

theorem compression_implementer (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (B : Space E →L[ℂ] Space E)
    (hB : ∀ g, cocycle D hκ hb g = coboundary (representation U hU) B g) (i : I) (g : G) :
    D i g = coboundary (U i) (compression B i) g := by
  have h := congrArg (fun T => compression T i) (hB g)
  have hc : compression (cocycle D hκ hb g) i = D i g := by
    ext x
    change D i g (lp.single 2 i x i) = D i g x
    rw [lp.single_apply_self]
  have hs (A C : Space E →L[ℂ] Space E) : compression (A-C) i = compression A i - compression C i := by
    ext x; rfl
  rwa [hc, coboundary, hs, compression_conjugate] at h


/-- Countably many separable fibres have a separable Hilbert sum. The proof
uses the dense span of coordinate inclusions and convergence of finite sums. -/
theorem separableSpace [Countable I] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (Space E) := by
  let s : Set (Space E) := ⋃ i, Set.range (inclusion (E := E) i)
  let V : Submodule ℂ (Space E) := Submodule.span ℂ s
  have hs : TopologicalSpace.IsSeparable s :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (inclusion (E := E) i).continuous)
  have hv : TopologicalSpace.IsSeparable (V : Set (Space E)) := hs.span
  have hd : Dense (V : Set (Space E)) := by
    intro x
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
    apply Filter.Eventually.of_forall
    intro F
    apply subset_closure
    apply V.sum_mem
    intro i hi
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨x i, rfl⟩⟩)
  exact hd.isSeparable_iff.mp hv


end HilbertSum
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Triangular

namespace OAI

/-! Bounded Hilbert sums and triangular representations. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev Double (H : Type*) := WithLp 2 (H × H)

def inl : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H H)

def inr : H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℂ H H)

@[simp] theorem inl_apply (x : H) : inl x = WithLp.toLp 2 (x,0) := rfl
@[simp] theorem inr_apply (x : H) : inr x = WithLp.toLp 2 (0,x) := rfl
@[simp] theorem inl_norm (x : H) : ‖inl x‖ = ‖x‖ := WithLp.norm_toLp_fst 2 H H x
@[simp] theorem inr_norm (x : H) : ‖inr x‖ = ‖x‖ := WithLp.norm_toLp_snd 2 H H x

def diagonal (U : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  inl.comp (U.comp (WithLp.fstL 2 ℂ H H)) +
    inr.comp (U.comp (WithLp.sndL 2 ℂ H H))

@[simp] theorem diagonal_fst (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).fst = U x.fst := by simp [diagonal, inl, inr]
@[simp] theorem diagonal_snd (U : H →L[ℂ] H) (x : Double H) :
    (diagonal U x).snd = U x.snd := by simp [diagonal, inl, inr]

def operator (U D : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  diagonal U + inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))

@[simp] theorem operator_fst (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).fst = U x.fst + D (U x.snd) := by simp [operator, inl]
@[simp] theorem operator_snd (U D : H →L[ℂ] H) (x : Double H) :
    (operator U D x).snd = U x.snd := by simp [operator, inl]

theorem diagonal_norm_map (U : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) (x : Double H) :
    ‖diagonal U x‖ = ‖x‖ := by
  have h : ‖diagonal U x‖^2 = ‖x‖^2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, diagonal_fst, diagonal_snd, hU]
  nlinarith [norm_nonneg (diagonal U x), norm_nonneg x]

theorem operator_norm_le (U D : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) :
    ‖operator U D‖ ≤ 1 + ‖D‖ := by
  have hd : ‖diagonal U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [diagonal_norm_map U hU]
  have hn : ‖inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))‖ ≤ ‖D‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro x
    change ‖inl (D (U x.snd))‖ ≤ ‖D‖ * ‖x‖
    rw [inl_norm]
    calc
      ‖D (U x.snd)‖ ≤ ‖D‖ * ‖U x.snd‖ := D.le_opNorm _
      _ = ‖D‖ * ‖x.snd‖ := by rw [hU]
      _ ≤ ‖D‖ * ‖x‖ := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le H x) (norm_nonneg D)
  exact (norm_add_le (diagonal U) (inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H))))).trans
    (add_le_add hd hn)

@[simp] theorem inv_apply (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g⁻¹ (U g x) = x := by
  have h : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

def representation (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h)) :
    G →* (Double H →L[ℂ] Double H) where
  toFun g := operator (U g) (D g)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp [h1]
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro x
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · change (operator (U (g*h)) (D (g*h)) x).fst =
        (operator (U g) (D g) (operator (U h) (D h) x)).fst
      simp only [operator_fst, operator_snd, map_mul, hD, conjugate,
        add_apply, mul_apply_eq_comp, map_add, inv_apply]
      abel
    · simp [map_mul, mul_apply_eq_comp]

theorem representation_bound (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) {κ : ℝ} (hb : ∀ g, ‖D g‖ ≤ κ) (g : G) :
    ‖representation U D h1 hD g‖ ≤ 1 + κ :=
  (operator_norm_le (U g) (D g) (hU g)).trans (add_le_add (le_refl _) (hb g))

end Triangular
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.InvariantProjection

namespace OAI

/-! A unitarizing similarity gives a bounded commuting projection
onto every closed invariant subspace. -/
noncomputable section
namespace Dixmier
namespace InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp] theorem rep_inv (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g (U g⁻¹ x) = x := by
  have h : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

theorem orthogonal_projection_commutes (U : G →* (H →L[ℂ] H))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → U g x ∈ M) (g : G) :
    Commute M.toSubmodule.starProjection (U g) := by
  change M.toSubmodule.starProjection * U g = U g * M.toSubmodule.starProjection
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM g _ (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have hi := (LinearMap.norm_map_iff_inner_map_map (U g)).mp (hU g)
    have hm : U g⁻¹ w ∈ M := hM g⁻¹ w hw
    have hz := M.toSubmodule.starProjection_inner_eq_zero x (U g⁻¹ w) hm
    have he := hi (x - M.toSubmodule.starProjection x) (U g⁻¹ w)
    rw [map_sub, rep_inv] at he
    exact he.trans hz

def conjugated (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) : G →* (H →L[ℂ] H) where
  toFun g := S.toContinuousLinearMap.comp ((π g).comp S.symm.toContinuousLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul, mul_apply_eq_comp]

omit [CompleteSpace H] in
@[simp] theorem conjugated_apply (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) (g : G) (x : H) :
    conjugated π S g x = S (π g (S.symm x)) := rfl

/-- The conclusion supplies one bounded projection; it assumes only the
actual similarity and closed invariance, not a cocycle implementer. -/
theorem exists_commuting_projection (π : G →* (H →L[ℂ] H))
    (hπ : SimilarToUnitary π) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → π g x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ ∀ g, Commute P (π g) := by
  rcases hπ with ⟨S, hS⟩
  let N : ClosedSubmodule ℂ H := M.mapEquiv S
  have hN : ∀ g x, x ∈ N → conjugated π S g x ∈ N := by
    intro g x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨π g y, hM g y hy, by simp⟩
  let Q := N.toSubmodule.starProjection
  let P : H →L[ℂ] H := S.symm.toContinuousLinearMap.comp (Q.comp S.toContinuousLinearMap)
  have hmem (x : H) : P x ∈ M := by
    have h := Submodule.starProjection_apply_mem N.toSubmodule (S x)
    rcases h with ⟨y, hy, he⟩
    change S.symm (Q (S x)) ∈ M
    rw [← he]
    simpa using hy
  have hfix (x : H) (hx : x ∈ M) : P x = x := by
    have hn : S x ∈ N := ⟨x, hx, rfl⟩
    change S.symm (Q (S x)) = x
    rw [Submodule.starProjection_eq_self_iff.mpr hn]
    simp
  refine ⟨P, hmem, hfix, ?_⟩
  intro g
  have hq := orthogonal_projection_commutes (conjugated π S) hS N hN g
  change P * π g = π g * P
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => S.symm (T (S x))) hq.eq
  simpa [P, Q, mul_apply_eq_comp] using h

end InvariantProjection
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Unitarizer

namespace OAI

/-! The bounded implementer forced by a unitarizing similarity.
The commuting projection onto H ⊕ 0 has upper-right block equal to the
negative implementer, avoiding a bounded inverse for graph coordinates. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A global cocycle implementer obtained from the similarity itself. -/
theorem implementer_of_similar (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hπ : SimilarToUnitary (representation U D h1 hD)) :
    ∃ B : H →L[ℂ] H, ∀ g, D g = coboundary U B g := by
  let π := representation U D h1 hD
  let M : ClosedSubmodule ℂ (Double H) :=
    ⟨(WithLp.sndL 2 ℂ H H).ker, (WithLp.sndL 2 ℂ H H).isClosed_ker⟩
  have hM : ∀ g x, x ∈ M → π g x ∈ M := by
    intro g x hx
    change x.snd = 0 at hx
    change (operator (U g) (D g) x).snd = 0
    simp [hx]
  rcases InvariantProjection.exists_commuting_projection π hπ M hM with ⟨P, hm, hf, hp⟩
  let q : H →L[ℂ] H := (WithLp.fstL 2 ℂ H H).comp (P.comp inr)
  have hzero (x : Double H) : (P x).snd = 0 := hm x
  have hfix (x : H) : P (inl x) = inl x := hf _ (by change (inl x).snd = 0; simp)
  have hdecomp (x : Double H) : x = inl x.fst + inr x.snd := by
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp
  have hfst (x : Double H) : (P x).fst = x.fst + q x.snd := by
    nth_rw 1 [hdecomp x]
    rw [map_add, hfix]
    simp [q]
  refine ⟨-q, ?_⟩
  intro g
  ext x
  have h := congrArg (fun T : Double H →L[ℂ] Double H => (T (inr (U g⁻¹ x))).fst) (hp g).eq
  change (P (operator (U g) (D g) (inr (U g⁻¹ x)))).fst =
    (operator (U g) (D g) (P (inr (U g⁻¹ x)))).fst at h
  rw [hfst, operator_fst, operator_snd, operator_fst, hzero] at h
  have hinv : U g (U g⁻¹ x) = x := InvariantProjection.rep_inv U g x
  simp only [inr_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_zero, zero_add, hinv,
    add_zero] at h
  change D g x = (-q) x - U g ((-q) (U g⁻¹ x))
  simp only [neg_apply, map_neg, sub_neg_eq_add]
  change D g x + q x = U g (q (U g⁻¹ x)) at h
  apply eq_neg_add_iff_add_eq.mpr
  simpa only [add_comm] using h

end Triangular
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.SumObstruction

namespace OAI

/-! The operator-theoretic direct-sum obstruction, constructed from stage operators
without any uniform bound on their norms. -/
noncomputable section
namespace Dixmier
namespace DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

abbrev Stage (G : Type*) (k : ℕ → ℕ) (j : ℕ) : Type _ := KernelObstruction.Space G (Fin (k j))
abbrev Total (G : Type*) (k : ℕ → ℕ) : Type _ := HilbertSum.Space (Stage G k)
abbrev Carrier (G : Type*) (k : ℕ → ℕ) := Triangular.Double (Total G k)

theorem stage_unitary (k : ℕ → ℕ) (j : ℕ) (g : G) (x : Stage G k j) :
    ‖KernelObstruction.translation g x‖ = ‖x‖ :=
  KernelObstruction.reindex_norm (Equiv.mulLeft g⁻¹) x

/-- The direct-sum obstruction with its representation and bound.
The stage operators A_j and T_j need not be uniformly bounded. -/
theorem direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π := by
  let U : ∀ j, G →* (Stage G k j →L[ℂ] Stage G k j) := fun _ => KernelObstruction.translation
  have hU : ∀ j g x, ‖U j g x‖ = ‖x‖ := stage_unitary k
  let D : ∀ j, G → (Stage G k j →L[ℂ] Stage G k j) := fun j => coboundary (U j) (T j)
  have h1 : ∀ j, D j 1 = 0 := fun j => coboundary_one (U j) (T j)
  have hD : ∀ j g h, D j (g*h) = D j g + conjugate (U j) g (D j h) :=
    fun j => coboundary_cocycle (U j) (T j)
  let V := HilbertSum.representation U hU
  let δ := HilbertSum.cocycle D hκ hb
  have hδ1 : δ 1 = 0 := HilbertSum.cocycle_one D hκ hb h1
  have hδ : ∀ g h, δ (g*h) = δ g + conjugate V g (δ h) :=
    HilbertSum.cocycle_identity U hU D hκ hb hD
  let π := Triangular.representation V δ hδ1 hδ
  have hδb : ∀ g, ‖δ g‖ ≤ κ := fun g => HilbertSum.boundedSum_norm_le _ hκ _
  refine ⟨π, Triangular.representation_bound V δ hδ1 hδ
    (HilbertSum.representation_norm_map U hU) hδb, ?_⟩
  intro hπ
  rcases Triangular.implementer_of_similar V δ hδ1 hδ hπ with ⟨B, hB⟩
  have hbound (j : ℕ) : KernelObstruction.energy (A j) / k j ≤ 4 * (κ + ‖B‖)^2 := by
    let Bj := HilbertSum.compression B j
    have hBj (g : G) : D j g = coboundary (U j) Bj g :=
      HilbertSum.compression_implementer U hU D hκ hb B hB j g
    have hC : T j - Bj ∈ KernelObstruction.Commutant := by
      intro g
      exact ((equal_coboundaries_iff_commute_sub (U j) (T j) Bj g).mp (hBj g)).symm
    have henergy := KernelObstruction.kernel_obstruction (hA j) hκ (hr j) (hc j) hC
    simp only [Fintype.card_fin, sub_sub_cancel] at henergy
    have hnorm : ‖Bj‖ ≤ ‖B‖ := HilbertSum.compression_norm_le B j
    have hs : (κ + ‖Bj‖)^2 ≤ (κ + ‖B‖)^2 :=
      pow_le_pow_left₀ (add_nonneg hκ (norm_nonneg _)) (add_le_add (le_refl _) hnorm) 2
    have henergy' : KernelObstruction.energy (A j) ≤ 4 * (k j : ℝ) * (κ + ‖B‖)^2 :=
      henergy.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hk j))).mpr
    nlinarith [henergy']
  obtain ⟨j, hj⟩ := (he.eventually (eventually_gt_atTop (4 * (κ + ‖B‖)^2))).exists
  exact (not_lt_of_ge (hbound j)) hj

omit [Group G] in
/-- The concrete carrier is separable when the group is countable. -/
theorem carrier_separable [Countable G] (k : ℕ → ℕ) :
    TopologicalSpace.SeparableSpace (Carrier G k) := by
  have (j : ℕ) : TopologicalSpace.SeparableSpace (Stage G k j) := HilbertSum.separableSpace
  have : TopologicalSpace.SeparableSpace (Total G k) := HilbertSum.separableSpace
  infer_instance

/-- The direct-sum obstruction with all Hilbert-space structure and separability
explicit in the conclusion. -/
theorem separable_direct_sum_obstruction [Countable G] (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    TopologicalSpace.SeparableSpace (Carrier G k) ∧
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π :=
  ⟨carrier_separable k, direct_sum_obstruction k hk A T hA hκ hr hc hb he⟩

end DirectSumObstruction
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.ScaledObstruction

namespace OAI

noncomputable section
namespace Dixmier
namespace KernelObstruction
variable {G K : Type*} [Group G] [Fintype K]

lemma coefficients_real_smul (t : ℝ) (B : Fibre K →L[ℂ] Fibre K) :
    coefficients (t • B) = t • coefficients B := by
  ext ab
  rfl

lemma energy_real_smul (t : ℝ) (A : Op G K) : energy (t • A) = t ^ 2 * energy A := by
  have hb (x y : G) : block (t • A) x y = t • block A x y := by
    simp only [block, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  simp only [energy, hb, coefficients_real_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  exact tsum_mul_left

end KernelObstruction
namespace DirectSumObstruction
open Filter
variable {G : Type*} [Group G]

theorem scaled_direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j - T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + t * κ) ∧ ¬ SimilarToUnitary π := by
  apply direct_sum_obstruction k hk (fun j => t • A j) (fun j => t • T j)
    (fun j g => by
      change (t • A j).comp (KernelObstruction.translation g) =
        (KernelObstruction.translation g).comp (t • A j)
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      exact congrArg (fun operator => t • operator) (hA j g).eq)
    (mul_nonneg ht.le hκ)
  · intro j
    simpa only [KernelObstruction.row, ContinuousLinearMap.comp_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht] using mul_le_mul_of_nonneg_left (hr j) ht.le
  · intro j
    rw [← smul_sub t (A j) (T j)]
    simpa only [KernelObstruction.col, ContinuousLinearMap.smul_comp,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht] using mul_le_mul_of_nonneg_left (hc j) ht.le
  · intro j g
    have hscale : coboundary KernelObstruction.translation (t • T j) g =
        t • coboundary KernelObstruction.translation (T j) g := by
      simp only [coboundary, conjugate, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_sub]
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hb j g) ht.le
  · simpa only [KernelObstruction.energy_real_smul, mul_div_assoc] using
      he.const_mul_atTop (sq_pos_of_pos ht)

end DirectSumObstruction

end Dixmier
end

end OAI

-- Source: OAI.Analysis.Unitarizability.SparseMask

namespace OAI

/-! Finite support estimates for mask differences.
The label type is retained even when the products s_i collide. -/
namespace Dixmier

open Finset
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]

noncomputable def rowOnes (a : G → I → Bool) (x : G) : Finset I :=
  univ.filter fun i => a x i = true

noncomputable def columnZeros (a : G → I → Bool) (s : I → G) (y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i = false

noncomputable def rowDifference (a : G → I → Bool) (g x : G) : Finset I :=
  univ.filter fun i => a x i ≠ a (g⁻¹ * x) i

noncomputable def columnDifference (a : G → I → Bool) (s : I → G)
    (g y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i ≠ a (g⁻¹ * (y * (s i)⁻¹)) i

private theorem bool_ne_true_union (b c : Bool) (h : b ≠ c) :
    b = true ∨ c = true := by cases b <;> cases c <;> simp_all

private theorem bool_ne_false_union (b c : Bool) (h : b ≠ c) :
    b = false ∨ c = false := by cases b <;> cases c <;> simp_all

/-- A row difference is supported on the union of the two one-sets. -/
theorem rowDifference_subset (a : G → I → Bool) (g x : G) :
    rowDifference a g x ⊆ rowOnes a x ∪ rowOnes a (g⁻¹ * x) := by
  intro i hi
  simp only [rowDifference, rowOnes, mem_filter, mem_univ, true_and, mem_union] at *
  exact bool_ne_true_union _ _ hi

/-- Column support uses zero-sets at y and g⁻¹y. -/
theorem columnDifference_subset (a : G → I → Bool) (s : I → G) (g y : G) :
    columnDifference a s g y ⊆ columnZeros a s y ∪ columnZeros a s (g⁻¹ * y) := by
  intro i hi
  simp only [columnDifference, columnZeros, mem_filter, mem_univ, true_and,
    mem_union, mul_assoc] at *
  exact bool_ne_false_union _ _ hi

/-- The row support bound p=min(2r,n), without distinctness of group products. -/
theorem rowDifference_card_le (a : G → I → Bool) (r : ℕ)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (g x : G) :
    (rowDifference a g x).card ≤ min (2 * r) (Fintype.card I) := by
  apply le_min
  · calc
      _ ≤ (rowOnes a x ∪ rowOnes a (g⁻¹ * x)).card := card_le_card (rowDifference_subset a g x)
      _ ≤ (rowOnes a x).card + (rowOnes a (g⁻¹ * x)).card := card_union_le _ _
      _ ≤ r + r := Nat.add_le_add (hr x) (hr (g⁻¹ * x))
      _ = 2 * r := (two_mul r).symm
  · exact card_le_univ _

/-- The column support bound p=min(2r,n). -/
theorem columnDifference_card_le (a : G → I → Bool) (s : I → G) (r : ℕ)
    (hc : ∀ y, (columnZeros a s y).card ≤ r) (g y : G) :
    (columnDifference a s g y).card ≤ min (2 * r) (Fintype.card I) := by
  apply le_min
  · calc
      _ ≤ (columnZeros a s y ∪ columnZeros a s (g⁻¹ * y)).card :=
        card_le_card (columnDifference_subset a s g y)
      _ ≤ (columnZeros a s y).card + (columnZeros a s (g⁻¹ * y)).card := card_union_le _ _
      _ ≤ r + r := Nat.add_le_add (hc y) (hc (g⁻¹ * y))
      _ = 2 * r := (two_mul r).symm
  · exact card_le_univ _

def boolComplex (b : Bool) : ℂ := if b then 1 else 0

/-- The scalar difference mask has absolute value at most one. -/
theorem difference_mask_norm (b c : Bool) : ‖boolComplex b - boolComplex c‖ ≤ 1 := by
  cases b <;> cases c <;> simp [boolComplex]

/-- Nonzero complex mask coefficients correspond exactly to unequal bits. -/
theorem difference_mask_ne_zero (b c : Bool) :
    boolComplex b - boolComplex c ≠ 0 ↔ b ≠ c := by
  cases b <;> cases c <;> simp [boolComplex]


end Dixmier

end OAI

-- Source: OAI.Analysis.Unitarizability.EndpointAssignment

namespace OAI

/-! Infinite endpoint assignment from a finite density inequality.
No countability or distinctness assumption on the edge labels is needed. -/
noncomputable section
namespace Dixmier
open Finset
open Classical

variable {E V W : Type*}

def endpointSlots (row : E → V) (col : E → W) (r : ℕ)
    (e : E) : Finset ((V × Fin r) ⊕ (W × Fin r)) :=
  (({row e} : Finset V) ×ˢ univ).disjSum (({col e} : Finset W) ×ˢ univ)

/-- All neighboring slots of a finite edge set: endpoints have distinct copies. -/
theorem endpointSlots_biUnion (row : E → V) (col : E → W) (r : ℕ)
    (F : Finset E) :
    F.biUnion (endpointSlots row col r) =
      ((F.image row) ×ˢ (univ : Finset (Fin r))).disjSum ((F.image col) ×ˢ univ) := by
  classical
  ext z
  rcases z with ⟨v, j⟩ | ⟨w, j⟩ <;> simp [endpointSlots]

/-- Infinite Hall matching with r slots at every row and every column. -/
theorem exists_endpoint_assignment (row : E → V) (col : E → W) (r : ℕ)
    (hdensity : ∀ F : Finset E, F.card ≤ r * ((F.image row).card + (F.image col).card)) :
    ∃ f : E → (V × Fin r) ⊕ (W × Fin r), Function.Injective f ∧
      ∀ e, f e ∈ endpointSlots row col r e := by
  classical
  apply (all_card_le_biUnion_card_iff_exists_injective (endpointSlots row col r)).mp
  intro F
  rw [endpointSlots_biUnion]
  simpa only [card_disjSum, card_product, card_univ, Fintype.card_fin, Nat.mul_add,
    Nat.mul_comm] using hdensity F

def slotIndex {r : ℕ} : (V × Fin r) ⊕ (W × Fin r) → Fin r
  | .inl p => p.2
  | .inr p => p.2

def isRowSlot {r : ℕ} : (V × Fin r) ⊕ (W × Fin r) → Bool
  | .inl _ => true
  | .inr _ => false

private theorem assigned_row_eq {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hf : ∀ e, f e ∈ endpointSlots row col r e) (e : E) (h : isRowSlot (f e) = true) :
    f e = Sum.inl (row e, slotIndex (f e)) := by
  have hm := hf e
  cases he : f e with
  | inl p =>
    simp [he, endpointSlots] at hm
    rcases p with ⟨v, j⟩
    simp_all [slotIndex]
  | inr p => simp [he, isRowSlot] at h

private theorem assigned_col_eq {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hf : ∀ e, f e ∈ endpointSlots row col r e) (e : E) (h : isRowSlot (f e) = false) :
    f e = Sum.inr (col e, slotIndex (f e)) := by
  have hm := hf e
  cases he : f e with
  | inl p => simp [he, isRowSlot] at h
  | inr p =>
    simp [he, endpointSlots] at hm
    rcases p with ⟨v, j⟩
    simp_all [slotIndex]

/-- Injectivity of the slot assignment bounds every finite row load. -/
theorem assigned_row_card_le {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hinj : Function.Injective f) (hf : ∀ e, f e ∈ endpointSlots row col r e)
    (v : V) (F : Finset E) (hF : ∀ e ∈ F, row e = v ∧ isRowSlot (f e) = true) :
    F.card ≤ r := by
  classical
  have hi : Set.InjOn (fun e => slotIndex (f e)) (↑F : Set E) := by
    intro e he e' he' hh
    dsimp only at hh
    apply hinj
    rw [assigned_row_eq hf e (hF e he).2, assigned_row_eq hf e' (hF e' he').2]
    rw [(hF e he).1, (hF e' he').1, hh]
  calc
    F.card = (F.image (fun e => slotIndex (f e))).card := (card_image_of_injOn hi).symm
    _ ≤ Fintype.card (Fin r) := card_le_univ _
    _ = r := Fintype.card_fin r

/-- Injectivity also bounds every finite column load. -/
theorem assigned_col_card_le {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hinj : Function.Injective f) (hf : ∀ e, f e ∈ endpointSlots row col r e)
    (w : W) (F : Finset E) (hF : ∀ e ∈ F, col e = w ∧ isRowSlot (f e) = false) :
    F.card ≤ r := by
  classical
  have hi : Set.InjOn (fun e => slotIndex (f e)) (↑F : Set E) := by
    intro e he e' he' hh
    dsimp only at hh
    apply hinj
    rw [assigned_col_eq hf e (hF e he).2, assigned_col_eq hf e' (hF e' he').2]
    rw [(hF e he).1, (hF e' he').1, hh]
  calc
    F.card = (F.image (fun e => slotIndex (f e))).card := (card_image_of_injOn hi).symm
    _ ≤ Fintype.card (Fin r) := card_le_univ _
    _ = r := Fintype.card_fin r

/-- A sparse mask from finite endpoint density. -/
theorem exists_sparse_mask {G I : Type*} [Group G] [Fintype I] (s : I → G) (r : ℕ)
    (hdensity : ∀ F : Finset (G × I), F.card ≤
      r * ((F.image Prod.fst).card + (F.image (fun e => e.1 * s e.2)).card)) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by
  classical
  obtain ⟨f, hinj, hf⟩ := exists_endpoint_assignment Prod.fst (fun e : G × I => e.1 * s e.2) r hdensity
  let a : G → I → Bool := fun x i => isRowSlot (f (x, i))
  refine ⟨a, ?_, ?_⟩
  · intro x
    let F := (rowOnes a x).image (fun i => (x, i))
    have hF : ∀ e ∈ F, e.1 = x ∧ isRowSlot (f e) = true := by
      rintro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      exact ⟨rfl, (mem_filter.mp hi).2⟩
    have hbound := assigned_row_card_le hinj hf x F hF
    have hi : Function.Injective (fun i : I => (x, i)) := by
      intro i j h
      exact congrArg Prod.snd h
    simpa only [F, card_image_of_injective _ hi] using hbound
  · intro y
    let F := (columnZeros a s y).image (fun i => (y * (s i)⁻¹, i))
    have hF : ∀ e ∈ F, e.1 * s e.2 = y ∧ isRowSlot (f e) = false := by
      rintro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      exact ⟨by simp, (mem_filter.mp hi).2⟩
    have hbound := assigned_col_card_le hinj hf y F hF
    have hi : Function.Injective (fun i => (y * (s i)⁻¹, i)) := by
      intro i j h
      exact congrArg Prod.snd h
    simpa only [F, card_image_of_injective _ hi] using hbound

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.SparseSplitting

namespace OAI

/-! Spectral norm bounds imply sparse endpoint assignments.
The input is a bounded convolution operator with its coefficient formula. -/
noncomputable section
namespace Dixmier
open Finset
open scoped InnerProductSpace
open Classical
variable {G I : Type*} [Fintype I]

abbrev ScalarL2 (G : Type*) := lp (fun _ : G => ℂ) 2

def indicatorL2 (U : Finset G) : ScalarL2 G := ∑ x ∈ U, lp.single 2 x 1

@[simp] theorem indicatorL2_apply (U : Finset G) (x : G) :
    indicatorL2 U x = if x ∈ U then 1 else 0 := by
  change (∑ i ∈ U, lp.single 2 i (1 : ℂ)) x = _
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply, lp.coeFn_single, Pi.single_apply]

theorem indicatorL2_norm_sq (U : Finset G) : ‖indicatorL2 U‖ ^ 2 = U.card := by
  have h := lp.norm_sum_single (p := 2) (by norm_num) (fun _ : G => (1 : ℂ)) U
  simpa [indicatorL2] using h

theorem indicatorL2_norm (U : Finset G) : ‖indicatorL2 U‖ = Real.sqrt U.card := by
  rw [← indicatorL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]

variable [Group G]

def rectangleEdges (s : I → G) (U V : Finset G) : Finset (G × I) :=
  (U ×ˢ univ).filter fun e => e.1 * s e.2 ∈ V

/-- Pairing convolution with the two indicator vectors counts labelled edges. -/
theorem indicator_convolution_inner (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    (U V : Finset G) :
    ⟪indicatorL2 U, A (indicatorL2 V)⟫_ℂ = (rectangleEdges s U V).card := by
  calc
    _ = ∑ x ∈ U, ∑ i, if x * s i ∈ V then (1 : ℂ) else 0 := by
      change ⟪∑ x ∈ U, lp.single 2 x (1 : ℂ), A (indicatorL2 V)⟫_ℂ = _
      simp only [sum_inner, lp.inner_single_left, hA, indicatorL2_apply]
      simp
    _ = (rectangleEdges s U V).card := by
      rw [Finset.card_eq_sum_ones]
      simp only [Nat.cast_sum, Nat.cast_one]
      rw [rectangleEdges, Finset.sum_filter, Finset.sum_product]

/-- The rectangular edge-count bound with all multiplicities retained. -/
theorem rectangleEdges_card_le (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {q : ℝ} (hq : ‖A‖ ≤ q) (U V : Finset G) :
    ((rectangleEdges s U V).card : ℝ) ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := by
  have hq0 : 0 ≤ q := (norm_nonneg A).trans hq
  calc
    _ = ‖⟪indicatorL2 U, A (indicatorL2 V)⟫_ℂ‖ := by
      rw [indicator_convolution_inner s A hA]
      simp
    _ ≤ ‖indicatorL2 U‖ * ‖A (indicatorL2 V)‖ := norm_inner_le_norm _ _
    _ ≤ ‖indicatorL2 U‖ * (q * ‖indicatorL2 V‖) :=
      mul_le_mul_of_nonneg_left ((A.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hq (norm_nonneg _))) (norm_nonneg _)
    _ = q * Real.sqrt ((U.card : ℝ) * V.card) := by
      rw [indicatorL2_norm, indicatorL2_norm, Real.sqrt_mul (Nat.cast_nonneg _)]
      ring

/-- Every finite edge family lies in the rectangle of its endpoints. -/
theorem edges_subset_endpoint_rectangle (s : I → G) (F : Finset (G × I)) :
    F ⊆ rectangleEdges s (F.image Prod.fst) (F.image fun e => e.1 * s e.2) := by
  intro e he
  simp only [rectangleEdges, mem_filter, mem_product, mem_univ, and_true]
  exact ⟨mem_image.mpr ⟨e, he, rfl⟩, mem_image.mpr ⟨e, he, rfl⟩⟩

/-- Arithmetic used in the Hall argument, including its factor one half. -/
theorem sqrt_mul_le_half_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [sq_nonneg (u - v)]

/-- The finite Hall density follows from the rectangular spectral estimate. -/
theorem endpoint_density_of_rectangle_bound (s : I → G) {q : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hqr : q ≤ r)
    (hrect : ∀ U V : Finset G, ((rectangleEdges s U V).card : ℝ) ≤
      q * Real.sqrt ((U.card : ℝ) * V.card))
    (F : Finset (G × I)) :
    F.card ≤ r * ((F.image Prod.fst).card + (F.image fun e => e.1 * s e.2).card) := by
  let U := F.image Prod.fst
  let V := F.image fun e => e.1 * s e.2
  have he : (F.card : ℝ) ≤ (rectangleEdges s U V).card := by
    exact_mod_cast card_le_card (edges_subset_endpoint_rectangle s F)
  have hsum : (0 : ℝ) ≤ (U.card : ℝ) + V.card := by positivity
  have hhalf : ((U.card : ℝ) + V.card) / 2 ≤ (U.card : ℝ) + V.card := by linarith
  have h : (F.card : ℝ) ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := calc
    _ ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := he.trans (hrect U V)
    _ ≤ q * (((U.card : ℝ) + V.card) / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_le_half_add (by positivity) (by positivity)) hq
    _ ≤ q * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_left hhalf hq
    _ ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_right hqr hsum
  exact_mod_cast h

/-- Sparse assignment from a bounded convolution operator, at any integer
capacity above its norm. -/
theorem sparse_mask_of_convolution_bound (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {r : ℕ} (hr : ‖A‖ ≤ r) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by
  apply exists_sparse_mask
  exact endpoint_density_of_rectangle_bound s (norm_nonneg A) hr
    (rectangleEdges_card_le s A hA le_rfl)

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Regular

namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
open Classical

variable {G : Type*}

def reindexL2 (e : G ≃ G) (ξ : ScalarL2 G) : ScalarL2 G :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

@[simp] theorem reindexL2_apply (e : G ≃ G) (ξ : ScalarL2 G) (x : G) :
    reindexL2 e ξ x = ξ (e x) := rfl

theorem l2_norm_sq (ξ : ScalarL2 G) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem reindexL2_norm (e : G ≃ G) (ξ : ScalarL2 G) : ‖reindexL2 e ξ‖ = ‖ξ‖ := by
  have hs : ‖reindexL2 e ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖ ^ 2)
  nlinarith [norm_nonneg (reindexL2 e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : ScalarL2 G →ₗᵢ[ℂ] ScalarL2 G where
  toFun := reindexL2 e
  map_add' ξ η := by ext x; rfl
  map_smul' z ξ := by ext x; rfl
  norm_map' := reindexL2_norm e

variable [Group G]

/-- The right regular representation R_t ξ(x)=ξ(xt). -/
def rightRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun t := (reindexIsometry (Equiv.mulRight t)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' s t := by ext ξ x; simp [reindexIsometry, reindexL2, mul_assoc]

@[simp] theorem rightRegular_apply (t : G) (ξ : ScalarL2 G) (x : G) :
    rightRegular t ξ x = ξ (x * t) := rfl

theorem rightRegular_norm_map (t : G) (ξ : ScalarL2 G) : ‖rightRegular t ξ‖ = ‖ξ‖ :=
  reindexL2_norm (Equiv.mulRight t) ξ

/-- Left regular operators U_g commute with the right regular operators. -/
def leftRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun g := (reindexIsometry (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' g h := by ext ξ x; simp [reindexIsometry, reindexL2]

@[simp] theorem leftRegular_apply (g : G) (ξ : ScalarL2 G) (x : G) :
    leftRegular g ξ x = ξ (g⁻¹ * x) := rfl

theorem left_right_commute (g t : G) : Commute (leftRegular g) (rightRegular t) := by
  change leftRegular g * rightRegular t = rightRegular t * leftRegular g
  ext ξ x
  simp [mul_assoc]

def Word (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => I × Word I n

instance wordFintype {I : Type*} [Fintype I] : (n : ℕ) → Fintype (Word I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI : Fintype (Word I n) := wordFintype n
    exact inferInstanceAs (Fintype (I × Word I n))

def wordProduct {I : Type*} (s : I → G) : (n : ℕ) → Word I n → G
  | 0, _ => 1
  | n + 1, w => s w.1 * wordProduct s n w.2

theorem word_card {I : Type*} [Fintype I] (n : ℕ) :
    Fintype.card (Word I n) = (Fintype.card I) ^ n := by
  induction n with
  | zero =>
    change Fintype.card PUnit = 1
    exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (I × Word I n) = _
    rw [Fintype.card_prod, ih, pow_succ']

/-- Product lists are indexed by words, not by their possibly colliding values. -/
theorem sum_wordProduct {I R : Type*} [Fintype I] [Semiring R]
    (s : I → G) (φ : G →* R) (n : ℕ) :
    (∑ w : Word I n, φ (wordProduct s n w)) = (∑ i, φ (s i)) ^ n := by
  induction n with
  | zero =>
    change (∑ w : PUnit, φ (1 : G)) = _
    simp
  | succ n ih =>
    change (∑ w : I × Word I n, φ (s w.1 * wordProduct s n w.2)) = _
    simp only [Fintype.sum_prod_type, map_mul, ← Finset.mul_sum, ← Finset.sum_mul, ih,
      pow_succ']

/-- Sparse splitting for words from a norm bound on the finite average. -/
theorem sparse_mask_for_words {I : Type*} [Fintype I] (s : I → G)
    {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (havg : ‖∑ i, rightRegular (s i)‖ ≤ (Fintype.card I : ℝ) * ρ) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ a : G → Word I ℓ → Bool,
      (∀ x, (rowOnes a x).card ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊) ∧
      ∀ y, (columnZeros a (wordProduct s ℓ) y).card ≤
        ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := by
  let A : ScalarL2 G →L[ℂ] ScalarL2 G := ∑ w : Word I ℓ, rightRegular (wordProduct s ℓ w)
  have hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ w, ξ (x * wordProduct s ℓ w) := by
    intro ξ x
    simp only [A, _root_.sum_apply]
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, rightRegular_apply]
  apply sparse_mask_of_convolution_bound (wordProduct s ℓ) A hA
  calc
    ‖A‖ = ‖(∑ i, rightRegular (s i)) ^ ℓ‖ := by
      dsimp only [A]
      rw [sum_wordProduct]
    _ ≤ ‖∑ i, rightRegular (s i)‖ ^ ℓ := norm_pow_le' _ hℓ
    _ ≤ ((Fintype.card I : ℝ) * ρ) ^ ℓ := pow_le_pow_left₀ (norm_nonneg _) havg ℓ
    _ = (Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ := mul_pow _ _ _
    _ ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := Nat.le_ceil _

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Average

namespace OAI

/-! Finite-average identities for contracting averages in Hilbert spaces. -/
noncomputable section
namespace Dixmier
open Finset
open scoped ComplexConjugate
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite Hilbert-space variance identity, without normalization. -/
theorem sum_pairwise_sq (S : Finset I) (v : I → H) :
    ∑ i ∈ S, ∑ j ∈ S, ‖v i - v j‖ ^ 2 =
      2 * (S.card : ℝ) * (∑ i ∈ S, ‖v i‖ ^ 2) - 2 * ‖∑ i ∈ S, v i‖ ^ 2 := by
  have hs : (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) =
      ‖∑ i ∈ S, v i‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ]
    simp only [sum_inner, inner_sum, map_sum]
    exact Finset.sum_comm
  simp_rw [@norm_sub_sq ℂ H]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp only [← Finset.mul_sum]
  change _ - 2 * (∑ i ∈ S, ∑ j ∈ S, (inner ℂ (v i) (v j)).re) + _ = _
  rw [hs]
  ring

omit [InnerProductSpace ℂ H] in
/-- A chosen pair contributes at most the total squared defect. -/
theorem pairwise_sq_le_sum (S : Finset I) (v : I → H) {i j : I}
    (hi : i ∈ S) (hj : j ∈ S) :
    ‖v i - v j‖ ^ 2 ≤ ∑ a ∈ S, ∑ b ∈ S, ‖v a - v b‖ ^ 2 := by
  exact (Finset.single_le_sum (fun b _ => sq_nonneg ‖v i - v b‖) hj).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (s := S) (fun b _ => sq_nonneg ‖v a - v b‖)) hi)

variable {G : Type*} [Group G]
/-- Defect in a finite sum of right translations of a unit vector. -/
theorem regular_sum_variance (S : Finset G) (ξ : ScalarL2 G) (hξ : ‖ξ‖ = 1) :
    ∑ g ∈ S, ∑ h ∈ S, ‖rightRegular g ξ - rightRegular h ξ‖ ^ 2 =
      2 * ((S.card : ℝ) ^ 2 - ‖∑ g ∈ S, rightRegular g ξ‖ ^ 2) := by
  rw [sum_pairwise_sq]
  simp only [rightRegular_norm_map, hξ, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- A norm-one vector witnessing any strict lower bound for an operator norm. -/
theorem exists_unit_near_opNorm (A : H →L[ℂ] H) {c : ℝ}
    (hc : 0 ≤ c) (hA : c < ‖A‖) : ∃ ξ : H, ‖ξ‖ = 1 ∧ c < ‖A ξ‖ := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hA) (ContinuousLinearMap.opNorm_le_of_unit_norm hc h)

/-- The norm-one-average hypothesis yields simultaneous almost invariance. -/
theorem almost_invariant_of_sum_norm (S : Finset G) (h1 : (1 : G) ∈ S)
    (hS : ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ScalarL2 G, ‖ξ‖ = 1 ∧ ∀ g ∈ S, ‖rightRegular g ξ - ξ‖ < ε := by
  have hd : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨1, h1⟩
  let c := Real.sqrt (max 0 ((S.card : ℝ)^2 - ε^2/2))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c^2 = max 0 ((S.card : ℝ)^2 - ε^2/2) :=
    Real.sq_sqrt (le_max_left _ _)
  have hcd : c < (S.card : ℝ) := by
    have hm : max 0 ((S.card : ℝ)^2 - ε^2/2) < (S.card : ℝ)^2 :=
      max_lt (sq_pos_of_pos hd) (by nlinarith [sq_pos_of_pos hε])
    nlinarith
  obtain ⟨ξ, hξ, hclose⟩ := exists_unit_near_opNorm
    (∑ g ∈ S, rightRegular g) hc (by rwa [hS])
  have hclose' : c < ‖∑ g ∈ S, rightRegular g ξ‖ := by
    simpa only [_root_.sum_apply] using hclose
  have hdefect : 2 * ((S.card : ℝ)^2 - ‖∑ g ∈ S, rightRegular g ξ‖^2) < ε^2 := by
    have hm := le_max_right 0 ((S.card : ℝ)^2 - ε^2/2)
    nlinarith [norm_nonneg (∑ g ∈ S, rightRegular g ξ)]
  refine ⟨ξ, hξ, fun g hg => ?_⟩
  have hp := pairwise_sq_le_sum S (fun g => rightRegular g ξ) hg h1
  rw [regular_sum_variance S ξ hξ] at hp
  have he : rightRegular (1 : G) ξ = ξ := by ext x; simp
  rw [he] at hp
  nlinarith [norm_nonneg (rightRegular g ξ - ξ)]

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.VectorMean

namespace OAI

/-! Vector means and their translation error bounds. -/
noncomputable section
namespace Dixmier
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [Group G] [TopologicalSpace G] in
theorem summable_l2_sq (ξ : ScalarL2 G) : Summable (fun x => ‖ξ x‖ ^ 2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num)

def vectorMeanValue (ξ : ScalarL2 G) (b : G →ᵇ ℂ) : ℂ :=
  ∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)

theorem vectorMean_summable (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    Summable (fun x => (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹) : G → ℂ) := by
  apply Summable.of_norm_bounded ((summable_l2_sq ξ).mul_right ‖b‖)
  intro x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
  exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)

theorem vectorMean_norm_le (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    ‖vectorMeanValue ξ b‖ ≤ ‖ξ‖ ^ 2 * ‖b‖ := by
  have hb : ∀ x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ ≤ ‖ξ x‖ ^ 2 * ‖b‖ := by
    intro x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)
  calc
    ‖vectorMeanValue ξ b‖ ≤ ∑' x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ :=
      norm_tsum_le_tsum_norm (vectorMean_summable ξ b).norm
    _ ≤ ∑' x, ‖ξ x‖ ^ 2 * ‖b‖ :=
      Summable.tsum_le_tsum hb (vectorMean_summable ξ b).norm ((summable_l2_sq ξ).mul_right ‖b‖)
    _ = ‖ξ‖ ^ 2 * ‖b‖ := by rw [tsum_mul_right, ← l2_norm_sq]

def vectorMeanLinear (ξ : ScalarL2 G) : (G →ᵇ ℂ) →ₗ[ℂ] ℂ where
  toFun := vectorMeanValue ξ
  map_add' b c := by
    simp only [vectorMeanValue, BoundedContinuousFunction.add_apply, mul_add]
    exact (vectorMean_summable ξ b).tsum_add (vectorMean_summable ξ c)
  map_smul' z b := by
    simp only [vectorMeanValue, BoundedContinuousFunction.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm _ z, mul_assoc]
    exact tsum_mul_left

def vectorMean (ξ : ScalarL2 G) : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  (vectorMeanLinear ξ).mkContinuous (‖ξ‖ ^ 2) (vectorMean_norm_le ξ)

@[simp] theorem vectorMean_apply (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    vectorMean ξ b = vectorMeanValue ξ b := rfl

theorem vectorMean_one (ξ : ScalarL2 G) :
    vectorMean ξ (BoundedContinuousFunction.const G 1) = (‖ξ‖ ^ 2 : ℝ) := by
  simp only [vectorMean_apply, vectorMeanValue, BoundedContinuousFunction.const_apply, mul_one]
  rw [← Complex.ofReal_tsum, ← l2_norm_sq]

theorem vectorMean_opNorm_le (ξ : ScalarL2 G) : ‖vectorMean ξ‖ ≤ ‖ξ‖ ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) (vectorMean_norm_le ξ)

theorem vectorMean_positive (ξ : ScalarL2 G) (b : G →ᵇ ℂ)
    (hb : ∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) :
    0 ≤ (vectorMean ξ b).re ∧ (vectorMean ξ b).im = 0 := by
  change 0 ≤ (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).re ∧
    (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)).im = 0
  rw [Complex.re_tsum (vectorMean_summable ξ b), Complex.im_tsum (vectorMean_summable ξ b)]
  constructor
  · apply tsum_nonneg
    intro x
    simpa only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_nonneg (sq_nonneg ‖ξ x‖) (hb x⁻¹).1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, fun x => (hb x).2, mul_zero, tsum_zero]

theorem vectorMean_translate [DiscreteTopology G] (ξ : ScalarL2 G) (g : G) (b : G →ᵇ ℂ) :
    vectorMean ξ (leftTranslate g b) = vectorMean (rightRegular g⁻¹ ξ) b := by
  change (∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (g⁻¹ * x⁻¹)) =
    ∑' x, (‖ξ (x * g⁻¹)‖ ^ 2 : ℝ) * b x⁻¹
  rw [← (Equiv.mulRight g).tsum_eq (fun x => (‖ξ (x * g⁻¹)‖ ^ 2 : ℝ) * b x⁻¹)]
  simp [mul_assoc]

theorem norm_sq_difference_le (a b : ℂ) :
    |‖a‖^2 - ‖b‖^2| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have he : |‖a‖^2 - ‖b‖^2| = |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) := by
    conv_rhs => rw [← abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
    rw [← abs_mul]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b)
    (add_nonneg (norm_nonneg a) (norm_nonneg b))

omit [Group G] [TopologicalSpace G] in
/-- The l2-to-l1 estimate behind the vector-mean translation error bound. -/
theorem l2_square_difference_bound (ξ η : ScalarL2 G) :
    Summable (fun x => |‖ξ x‖^2 - ‖η x‖^2|) ∧
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := by
  have hp : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    norm_num [Real.HolderConjugate]
    constructor <;> norm_num
  have h1 := lp.tsum_mul_le_mul_norm hp (ξ - η) ξ
  have h2 := lp.tsum_mul_le_mul_norm hp (ξ - η) η
  have hsum := h1.1.add h2.1
  have hb : ∀ x, |‖ξ x‖^2 - ‖η x‖^2| ≤ ‖(ξ - η) x‖ * ‖ξ x‖ + ‖(ξ - η) x‖ * ‖η x‖ := by
    intro x
    simpa [mul_add] using norm_sq_difference_le (ξ x) (η x)
  have hs := Summable.of_nonneg_of_le (fun x => abs_nonneg _) hb hsum
  refine ⟨hs, ?_⟩
  calc
    (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) ≤ ∑' x, (‖(ξ - η) x‖ * ‖ξ x‖ + ‖(ξ - η) x‖ * ‖η x‖) :=
      Summable.tsum_le_tsum hb hs hsum
    _ = (∑' x, ‖(ξ - η) x‖ * ‖ξ x‖) + ∑' x, ‖(ξ - η) x‖ * ‖η x‖ := h1.1.tsum_add h2.1
    _ ≤ ‖ξ - η‖ * ‖ξ‖ + ‖ξ - η‖ * ‖η‖ := add_le_add h1.2 h2.2
    _ = ‖ξ - η‖ * (‖ξ‖ + ‖η‖) := (mul_add _ _ _).symm

theorem vectorMean_difference_bound (ξ η : ScalarL2 G) (b : G →ᵇ ℂ) :
    ‖vectorMean ξ b - vectorMean η b‖ ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) * ‖b‖ := by
  let f : G → ℂ := fun x => ((‖ξ x‖^2 - ‖η x‖^2 : ℝ) : ℂ) * b x⁻¹
  have hf : Summable f := ((vectorMean_summable ξ b).sub (vectorMean_summable η b)).congr
    (fun x => by dsimp [f]; push_cast; ring)
  have he : vectorMean ξ b - vectorMean η b = ∑' x, f x := by
    rw [vectorMean_apply, vectorMean_apply, vectorMeanValue, vectorMeanValue,
      ← (vectorMean_summable ξ b).tsum_sub (vectorMean_summable η b)]
    apply tsum_congr
    intro x
    dsimp [f]
    push_cast
    ring
  have hsq := l2_square_difference_bound ξ η
  have hb : ∀ x, ‖f x‖ ≤ |‖ξ x‖^2 - ‖η x‖^2| * ‖b‖ := by
    intro x
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (abs_nonneg _)
  rw [he]
  calc
    ‖∑' x, f x‖ ≤ ∑' x, ‖f x‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' x, |‖ξ x‖^2 - ‖η x‖^2| * ‖b‖ :=
      Summable.tsum_le_tsum hb hf.norm (hsq.1.mul_right ‖b‖)
    _ = (∑' x, |‖ξ x‖^2 - ‖η x‖^2|) * ‖b‖ := tsum_mul_right
    _ ≤ ‖ξ - η‖ * (‖ξ‖ + ‖η‖) * ‖b‖ := mul_le_mul_of_nonneg_right hsq.2 (norm_nonneg _)

/-- The vector-mean translation error estimate. -/
theorem vectorMean_translation_bound [DiscreteTopology G] (ξ : ScalarL2 G) (hξ : ‖ξ‖ = 1)
    (g : G) (b : G →ᵇ ℂ) :
    ‖vectorMean ξ (leftTranslate g b) - vectorMean ξ b‖ ≤
      2 * ‖b‖ * ‖rightRegular g⁻¹ ξ - ξ‖ := by
  rw [vectorMean_translate]
  have h := vectorMean_difference_bound (rightRegular g⁻¹ ξ) ξ b
  rw [rightRegular_norm_map, hξ] at h
  nlinarith

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.CompactMean

namespace OAI

/-! Weak-star compactness for positive normalized invariant means. -/
noncomputable section
namespace Dixmier
open Filter Topology
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- Approximate positive normalized means, with all finite translation tests,
have a positive normalized invariant weak-star cluster point. -/
theorem amenable_of_approximate_means
    (h : ∀ (S : Finset G) (ε : ℝ), 0 < ε →
      ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
        ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
        (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
          0 ≤ (m b).re ∧ (m b).im = 0) ∧
        ∀ g ∈ S, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤ ε * ‖b‖) :
    Amenable G := by
  classical
  let J := Finset G × ℕ
  have hm : ∀ a : J, ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
      ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
      (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
        0 ≤ (m b).re ∧ (m b).im = 0) ∧
      ∀ g ∈ a.1, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤
        (1 / ((a.2 : ℝ) + 1)) * ‖b‖ := by
    intro a
    exact h a.1 _ (by positivity)
  choose m hm using hm
  let μ : J → WeakDual ℂ (G →ᵇ ℂ) := fun a => StrongDual.toWeakDual (m a)
  have hball : ∀ a, μ a ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1 := by
    intro a
    change m a ∈ Metric.closedBall 0 1
    simpa [Metric.mem_closedBall, dist_zero_right] using (hm a).1
  obtain ⟨M, _, hM⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1).exists_mapClusterPt
    (f := (atTop : Filter J)) (u := μ)
    (by
      rw [Filter.le_principal_iff]
      change ∀ᶠ a in (atTop : Filter J), μ a ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1
      exact Filter.Eventually.of_forall hball)
  refine ⟨M.toStrongDual.toLinearMap, ?_, ?_, ?_⟩
  · have hc : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | M (BoundedContinuousFunction.const G (1 : ℂ)) = 1} :=
      isClosed_eq (WeakDual.eval_continuous _) continuous_const
    exact hc.mem_of_mapClusterPt hM (Filter.Eventually.of_forall (fun a => (hm a).2.1))
  · intro b hb
    have hr : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | 0 ≤ (M b).re} :=
      isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous b))
    have hi : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | (M b).im = 0} :=
      isClosed_eq (Complex.continuous_im.comp (WeakDual.eval_continuous b)) continuous_const
    exact (hr.inter hi).mem_of_mapClusterPt hM
      (Filter.Eventually.of_forall (fun a => (hm a).2.2.1 b hb))
  · intro g b
    have hsmall : ∀ ε : ℝ, 0 < ε → ‖M (leftTranslate g b) - M b‖ ≤ ε := by
      intro ε hε
      have hc : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | ‖M (leftTranslate g b) - M b‖ ≤ ε} :=
        isClosed_le (((WeakDual.eval_continuous (leftTranslate g b)).sub
        (WeakDual.eval_continuous b)).norm) continuous_const
      apply hc.mem_of_mapClusterPt hM
      obtain ⟨n, hn⟩ := exists_nat_gt (‖b‖ / ε)
      apply Filter.eventually_atTop.mpr
      refine ⟨({g}, n), fun a ha => ?_⟩
      have hg : g ∈ a.1 := ha.1 (Finset.mem_singleton_self g)
      have hna : (n : ℝ) ≤ a.2 := by exact_mod_cast ha.2
      have hpos : (0 : ℝ) < a.2 + 1 := by positivity
      have hbn : ‖b‖ < ε * (n : ℝ) := by
        have := (div_lt_iff₀ hε).mp hn
        nlinarith
      have he : (1 / ((a.2 : ℝ) + 1)) * ‖b‖ ≤ ε := by
        rw [one_div_mul_eq_div]
        apply (div_le_iff₀ hpos).mpr
        nlinarith
      exact ((hm a).2.2.2 g hg b).trans he
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hne
    have hp : 0 < ‖M (leftTranslate g b) - M b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := hsmall (‖M (leftTranslate g b) - M b‖ / 2) (by positivity)
    linarith

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Contracting

namespace OAI

/-! Contracting averages and sparse splitting for nonamenable groups. -/
noncomputable section
namespace Dixmier
open Finset
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem rightRegular_opNorm (g : G) : ‖rightRegular g‖ = 1 := by
  classical
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro ξ
    simp [rightRegular_norm_map]
  · have h := (rightRegular g).le_opNorm (indicatorL2 ({1} : Finset G))
    simpa [rightRegular_norm_map, indicatorL2_norm] using h

omit [TopologicalSpace G] [DiscreteTopology G] in
theorem regular_sum_norm_le (S : Finset G) :
    ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) := by
  calc
    ‖∑ g ∈ S, rightRegular g‖ ≤ ∑ g ∈ S, ‖rightRegular g‖ := norm_sum_le _ _
    _ = (S.card : ℝ) := by simp [rightRegular_opNorm]

/-- Contrapositive analytic argument using the invariant-mean definition. -/
theorem amenable_of_all_sum_norm
    (h : ∀ S : Finset G, 1 ∈ S → ‖∑ g ∈ S, rightRegular g‖ = (S.card : ℝ)) :
    Amenable G := by
  classical
  apply amenable_of_approximate_means
  intro S ε hε
  let T := insert 1 (S.image fun g => g⁻¹)
  have h1 : (1 : G) ∈ T := mem_insert_self _ _
  obtain ⟨ξ, hξ, hinv⟩ := almost_invariant_of_sum_norm T h1 (h T h1)
    (show 0 < ε / 2 by positivity)
  refine ⟨vectorMean ξ, ?_, ?_, vectorMean_positive ξ, ?_⟩
  · simpa [hξ] using vectorMean_opNorm_le ξ
  · rw [vectorMean_one, hξ]
    norm_num
  · intro g hg b
    have hg' : g⁻¹ ∈ T := mem_insert_of_mem (mem_image.mpr ⟨g, hg, rfl⟩)
    have hb := vectorMean_translation_bound ξ hξ g b
    have hi := hinv g⁻¹ hg'
    calc
      ‖vectorMean ξ (leftTranslate g b) - vectorMean ξ b‖ ≤ 2 * ‖b‖ * ‖rightRegular g⁻¹ ξ - ξ‖ := hb
      _ ≤ 2 * ‖b‖ * (ε / 2) := mul_le_mul_of_nonneg_left hi.le (by positivity)
      _ = ε * ‖b‖ := by ring

/-- Nonamenability provides a strict contraction after normalization. -/
theorem exists_contracting_sum (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ) * ρ := by
  classical
  have hex : ∃ S : Finset G, 1 ∈ S ∧ ‖∑ g ∈ S, rightRegular g‖ < (S.card : ℝ) := by
    by_contra hnot
    push Not at hnot
    exact hG (amenable_of_all_sum_norm (fun S h1 => le_antisymm (regular_sum_norm_le S) (hnot S h1)))
  obtain ⟨S, h1, hlt⟩ := hex
  have hd : 0 < S.card := card_pos.mpr ⟨1, h1⟩
  have hd2 : 2 ≤ S.card := by
    by_contra hnot
    have hc : S.card = 1 := by omega
    obtain ⟨g, rfl⟩ := card_eq_one.mp hc
    have hg : g = 1 := by simpa [eq_comm] using h1
    subst g
    simp only [sum_singleton, rightRegular_opNorm, card_singleton, Nat.cast_one, lt_self_iff_false] at hlt
  have hdR : (0 : ℝ) < S.card := by exact_mod_cast hd
  obtain ⟨t, hAt, htd⟩ := exists_between hlt
  have ht : 0 < t := lt_of_le_of_lt (norm_nonneg _) hAt
  refine ⟨S, h1, hd2, t / S.card, div_pos ht hdR, (div_lt_one hdR).mpr htd, ?_⟩
  rw [mul_div_cancel₀ _ hdR.ne']
  exact hAt.le

/-- A contracting average with e ∈ S, d ≥ 2, and 0 < ρ < 1. -/
theorem contracting_average (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        ‖((S.card : ℂ)⁻¹) • (∑ g ∈ S, rightRegular g)‖ ≤ ρ := by
  obtain ⟨S, h1, hd, ρ, hρ, hρ1, hsum⟩ := exists_contracting_sum hG
  refine ⟨S, h1, hd, ρ, hρ, hρ1, ?_⟩
  have hdR : (0 : ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  rw [norm_smul, norm_inv]
  simp only [Complex.norm_natCast]
  calc
    (S.card : ℝ)⁻¹ * ‖∑ g ∈ S, rightRegular g‖ ≤ (S.card : ℝ)⁻¹ * ((S.card : ℝ) * ρ) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hdR.le)
    _ = ρ := by field_simp

/-- Sparse splitting from nonamenability. A single S and ρ work for every
positive word length; all words remain separate labels, even when their group products agree. -/
theorem sparse_splitting_of_nonamenable (hG : ¬ Amenable G) :
    ∃ S : Finset G, 1 ∈ S ∧ 2 ≤ S.card ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ ℓ : ℕ, 0 < ℓ → ∃ a : G → Word S ℓ → Bool,
        (∀ x, (rowOnes a x).card ≤ ⌈(S.card : ℝ)^ℓ * ρ^ℓ⌉₊) ∧
        ∀ y, (columnZeros a (wordProduct (fun s : S => (s : G)) ℓ) y).card ≤
          ⌈(S.card : ℝ)^ℓ * ρ^ℓ⌉₊ := by
  classical
  obtain ⟨S, h1, hd, ρ, hρ, hρ1, hsum⟩ := exists_contracting_sum hG
  refine ⟨S, h1, hd, ρ, hρ, hρ1, fun ℓ hℓ => ?_⟩
  have hsum' : ‖∑ g : S, rightRegular (g : G)‖ ≤ (Fintype.card S : ℝ) * ρ := by
    simpa only [Fintype.card_coe, Finset.sum_coe_sort] using hsum
  simpa only [Fintype.card_coe] using
    sparse_mask_for_words (fun s : S => (s : G)) hρ.le hsum' ℓ hℓ

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.FiniteSigns

namespace OAI

/-! Finite independent signs. Expectations are explicit finite sums over all sign
assignments with equal weight. -/
noncomputable section
namespace Dixmier
namespace FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
local instance : DecidableEq J := Classical.decEq J

def sign (b : Bool) : ℝ := if b then 1 else -1

def value (a : J → ℝ) (σ : J → Bool) : ℝ := ∑ j, a j * sign (σ j)

theorem sign_mgf (a : J → ℝ) :
    ∑ σ : J → Bool, Real.exp (value a σ) =
      (2 : ℝ) ^ Fintype.card J * ∏ j, Real.cosh (a j) := by
  simp only [value, Real.exp_sum]
  rw [← Fintype.prod_sum (fun j (b : Bool) => Real.exp (a j * sign b))]
  have h (j : J) : (∑ b : Bool, Real.exp (a j * sign b)) = 2 * Real.cosh (a j) := by
    simp [sign, Real.cosh_eq]
    ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

theorem sign_mgf_le (a : J → ℝ) :
    ∑ σ : J → Bool, Real.exp (value a σ) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp ((∑ j, (a j)^2) / 2) := by
  rw [sign_mgf]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ∏ j, Real.cosh (a j) ≤ ∏ j, Real.exp ((a j)^2/2) :=
      Finset.prod_le_prod (fun j _ => (Real.cosh_pos _).le) (fun j _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by rw [← Real.exp_sum]; simp only [div_eq_mul_inv, Finset.sum_mul]

theorem value_smul (a : J → ℝ) (t : ℝ) (σ : J → Bool) :
    value (fun j => t * a j) σ = t * value a σ := by
  simp only [value, Finset.mul_sum, mul_assoc]

/-- Finite Markov inequality for the equiprobable sign space. -/
theorem upper_tail_mgf (a : J → ℝ) {t u : ℝ} (ht : 0 ≤ t) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) * Real.exp (t*u) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (t^2 * (∑ j, (a j)^2) / 2) := by
  classical
  let S := univ.filter (fun σ : J → Bool => u < value a σ)
  have h1 : (S.card : ℝ) * Real.exp (t*u) ≤ ∑ σ ∈ S, Real.exp (t * value a σ) := by
    calc
      _ = ∑ σ ∈ S, Real.exp (t*u) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun σ hσ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hσ).2.le ht))
  have h2 : (∑ σ ∈ S, Real.exp (t * value a σ)) ≤ ∑ σ : J → Bool, Real.exp (t * value a σ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
  have h3 := sign_mgf_le (fun j => t*a j)
  simp only [value_smul, mul_pow, ← Finset.mul_sum] at h3
  exact h1.trans (h2.trans h3)

/-- One-sided sign tail for coefficients of total squared size 1/k. -/
theorem upper_tail (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) ≤
      (2 : ℝ) ^ Fintype.card J * Real.exp (-k*u^2/2) := by
  have h := upper_tail_mgf a (mul_nonneg hk.le hu.le) (u := u)
  rw [ha] at h
  have hexp : (k*u)^2*(1/k)/2 = (-k*u^2/2) + (k*u)*u := by field_simp; ring
  rw [hexp, Real.exp_add, ← mul_assoc] at h
  exact (mul_le_mul_iff_left₀ (Real.exp_pos ((k*u)*u))).mp h


theorem value_neg (a : J → ℝ) (σ : J → Bool) : value (fun j => -a j) σ = -value a σ := by
  simp [value, Finset.sum_neg_distrib]

/-- The two-sided sign-tail bound as a fraction of the finite equiprobable sign space. -/
theorem two_sided_tail (a : J → ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    (ha : ∑ j, (a j)^2 = 1/k) :
    (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card J ≤ 2 * Real.exp (-k*u^2/2) := by
  classical
  have hn : ∑ j, (-a j)^2 = 1/k := by simpa only [neg_sq] using ha
  have hp := upper_tail a hk hu ha
  have hm := upper_tail (fun j => -a j) hk hu hn
  have hs : (univ.filter fun σ : J → Bool => u < |value a σ|) ⊆
      (univ.filter fun σ : J → Bool => u < value a σ) ∪
      (univ.filter fun σ : J → Bool => u < value (fun j => -a j) σ) := by
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and, mem_union, value_neg] at *
    rcases lt_abs.mp hσ with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hr : (((univ.filter fun σ : J → Bool => u < |value a σ|).card : ℕ) : ℝ) ≤
      (((univ.filter fun σ : J → Bool => u < value a σ).card : ℕ) : ℝ) +
      (((univ.filter fun σ : J → Bool => u < value (fun j => -a j) σ).card : ℕ) : ℝ) := by
    exact_mod_cast hcard
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ Fintype.card J)).mpr
  nlinarith


end FiniteSigns
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.SphereNet

namespace OAI

/-! Quarter-nets and their cardinality bounds. Volume comparison with
radii 1/8 and 9/8 gives the constant 9^m. -/
noncomputable section
namespace Dixmier
namespace SphereNet
open Set Metric MeasureTheory Module
open scoped ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Function in
 theorem quarter_separated_card (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1/4 : ℝ) ≤ ‖c-d‖) : s.card ≤ 9 ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1/8
  let ρ : ℝ := 9/8
  have ρpos : 0 < ρ := by norm_num [ρ]
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert h c hc d hd hcd using 1
    norm_num [δ]
  have A_subset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by rw [dist_zero_right]; exact add_le_add le_rfl (hs x hx)
      _ = ρ := by norm_num [δ, ρ]
  have I : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [hA, measure_biUnion_finset D (fun c _ => measurableSet_ball)]
        have hd : 0 < δ := by norm_num [δ]
        simp only [μ.addHaar_ball_of_pos _ hd, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono A_subset
      _ = _ := by simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤ ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) ≤ (9 : ℝ) ^ finrank ℝ E := by
    have hh := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using hh
  exact_mod_cast K

/-- A quarter-net with all centers on the unit sphere and
at most 9^dim centers. -/
theorem exists_quarter_net : ∃ s : Finset E,
    (∀ x ∈ s, ‖x‖ = 1) ∧ s.card ≤ 9 ^ finrank ℝ E ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x-y‖ ≤ (1/4 : ℝ) := by
  classical
  let C : Set ℕ := {n | ∃ s : Finset E, s.card = n ∧ (∀ x ∈ s, ‖x‖ = 1) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1/4 : ℝ) ≤ ‖x-y‖}
  have hnonempty : C.Nonempty := ⟨0, ∅, by simp⟩
  have hbounded : BddAbove C := by
    refine ⟨9 ^ finrank ℝ E, ?_⟩
    rintro n ⟨s, rfl, hs, hsep⟩
    exact quarter_separated_card s (fun x hx => (hs x hx).le) hsep
  obtain ⟨s, hcard, hs, hsep⟩ := Nat.sSup_mem hnonempty hbounded
  refine ⟨s, hs, quarter_separated_card s (fun x hx => (hs x hx).le) hsep, ?_⟩
  intro x hx
  by_contra hnot
  push Not at hnot
  have hxnot : x ∉ s := by
    intro hmem
    have hh := hnot x hmem
    simp at hh
    linarith
  have hiunit : ∀ y ∈ insert x s, ‖y‖ = 1 := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact hs y hy
  have hisep : ∀ y ∈ insert x s, ∀ z ∈ insert x s, y ≠ z → (1/4 : ℝ) ≤ ‖y-z‖ := by
    intro y hy z hz hyz
    by_cases hyx : y = x
    · subst y
      have hz' : z ∈ s := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hyz)
      exact (hnot z hz').le
    · have hy' : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hyx
      by_cases hzx : z = x
      · subst z
        simpa only [norm_sub_rev] using (hnot y hy').le
      · have hz' : z ∈ s := (Finset.mem_insert.mp hz).resolve_left hzx
        exact hsep y hy' z hz' hyz
  have hbig : (insert x s).card ≤ sSup C := le_csSup hbounded ⟨insert x s, rfl, hiunit, hisep⟩
  rw [Finset.card_insert_of_notMem hxnot, hcard] at hbig
  omega

end SphereNet
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.NetOperator

namespace OAI

/-! Finite quarter-net tests imply the operator bound 10
for real operators. -/
noncomputable section
namespace Dixmier
namespace SphereNet
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- The two quarter-net errors each cost at most a quarter of the
operator norm. Tests bounded by 5 therefore give operator norm at most 10. -/
theorem operator_norm_le_ten (M : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (_hs : ∀ x ∈ s, ‖x‖ = 1) (ht : ∀ y ∈ t, ‖y‖ = 1)
    (hsnet : ∀ x : E, ‖x‖ = 1 → ∃ x₀ ∈ s, ‖x-x₀‖ ≤ (1/4 : ℝ))
    (htnet : ∀ y : F, ‖y‖ = 1 → ∃ y₀ ∈ t, ‖y-y₀‖ ≤ (1/4 : ℝ))
    (hM : ∀ x ∈ s, ∀ y ∈ t, |inner ℝ (M x) y| ≤ 5) : ‖M‖ ≤ 10 := by
  have hb : ‖M‖ ≤ 5 + ‖M‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨x₀, hx₀, hdx⟩ := hsnet x hx
    obtain ⟨y₀, hy₀, hdy⟩ := htnet y hy
    have heq : inner ℝ (M x) y = inner ℝ (M x₀) y₀ +
        inner ℝ (M x) (y-y₀) + inner ℝ (M (x-x₀)) y₀ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : |inner ℝ (M x) (y-y₀)| ≤ ‖M‖/4 := by
      calc
        _ ≤ ‖M x‖ * ‖y-y₀‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ ≤ (‖M‖ * ‖x‖) * (1/4) := mul_le_mul (M.le_opNorm x) hdy
          (norm_nonneg _) (mul_nonneg (norm_nonneg M) (norm_nonneg x))
        _ = _ := by rw [hx]; ring
    have h2 : |inner ℝ (M (x-x₀)) y₀| ≤ ‖M‖/4 := by
      calc
        _ ≤ ‖M (x-x₀)‖ * ‖y₀‖ := norm_inner_le_norm (𝕜 := ℝ) _ _
        _ = ‖M (x-x₀)‖ := by rw [ht y₀ hy₀, mul_one]
        _ ≤ ‖M‖ * ‖x-x₀‖ := M.le_opNorm _
        _ ≤ ‖M‖ * (1/4) := mul_le_mul_of_nonneg_left hdx (norm_nonneg M)
        _ = _ := by ring
    change inner ℝ (M x) y ≤ 5 + ‖M‖/2
    rw [heq]
    linarith [le_abs_self (inner ℝ (M x₀) y₀), hM x₀ hx₀ y₀ hy₀,
      le_abs_self (inner ℝ (M x) (y-y₀)), le_abs_self (inner ℝ (M (x-x₀)) y₀)]
  linarith

end SphereNet
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.FiniteSynthesis

namespace OAI

/-! Finite synthesis maps and their adjoints, with bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace FiniteSynthesis
open scoped ComplexConjugate
variable {I K : Type*} [Fintype K]
local instance : DecidableEq I := Classical.decEq I

def synthesis (v : I → EuclideanSpace ℂ K) (J : Finset I) :
    EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ K :=
  ∑ i : J, InnerProductSpace.rankOne ℂ (v i) (EuclideanSpace.basisFun J ℂ i)

@[simp] theorem synthesis_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (z : EuclideanSpace ℂ J) : synthesis v J z = ∑ i : J, z i • v i := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

@[simp] theorem synthesis_adjoint_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (x : EuclideanSpace ℂ K) (i : J) : (synthesis v J).adjoint x i = inner ℂ (v i) x := by
  rw [← EuclideanSpace.basisFun_inner, ContinuousLinearMap.adjoint_inner_right]
  have h : synthesis v J (EuclideanSpace.basisFun J ℂ i) = v i := by
    simp [synthesis_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  rw [h]

/-- The synthesis operator bound on subfamily coordinate spaces,
including the empty subfamily. -/
def FrameBound (v : I → EuclideanSpace ℂ K) (p : ℕ) (b : ℝ) : Prop :=
  ∀ J : Finset I, J.card ≤ p → ‖synthesis v J‖ ≤ b

theorem synthesis_sq_le (v : I → EuclideanSpace ℂ K) (J : Finset I) {b : ℝ}
    (_hb : 0 ≤ b) (hJ : ‖synthesis v J‖ ≤ b) (z : J → ℂ) :
    ‖∑ i : J, z i • v i‖^2 ≤ b^2 * ∑ i : J, ‖z i‖^2 := by
  let z' : EuclideanSpace ℂ J := WithLp.toLp 2 z
  have h := (synthesis v J).le_of_opNorm_le hJ z'
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [synthesis_apply, mul_pow, EuclideanSpace.norm_sq_eq] using hpow

theorem analysis_sq_le (v : I → EuclideanSpace ℂ K) (J : Finset I) {b : ℝ}
    (_hb : 0 ≤ b) (hJ : ‖synthesis v J‖ ≤ b) (x : EuclideanSpace ℂ K) :
    ∑ i : J, ‖inner ℂ (v i) x‖^2 ≤ b^2 * ‖x‖^2 := by
  have hj : ‖(synthesis v J).adjoint‖ ≤ b := by simpa using hJ
  have h := (synthesis v J).adjoint.le_of_opNorm_le hj x
  have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [EuclideanSpace.norm_sq_eq, synthesis_adjoint_apply, mul_pow] using hpow

end FiniteSynthesis
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.SignMatrix

namespace OAI

/-! Normalized sign matrices and their finite-dimensional bilinear
tests. The coordinate selections are injective and retain label identities. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq J := Classical.decEq J
local instance : DecidableEq K := Classical.decEq K

theorem sum_on_embedding {R : Type*} [AddCommMonoid R] (e : J ↪ I) (f : I → R)
    (hf : ∀ i, (¬ ∃ j, e j = i) → f i = 0) : ∑ i, f i = ∑ j, f (e j) := by
  calc
    _ = ∑ i ∈ univ.map e, f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hn
      apply hf i
      simpa using hn
    _ = _ := by rw [Finset.sum_map]

def extend (e : J ↪ I) (z : J → ℝ) : I → ℝ := Function.extend e z (fun _ => 0)

omit [Fintype I] [Fintype J] in
@[simp] theorem extend_apply (e : J ↪ I) (z : J → ℝ) (j : J) : extend e z (e j) = z j :=
  e.injective.extend_apply z _ j

omit [Fintype I] [Fintype J] in
theorem extend_off (e : J ↪ I) (z : J → ℝ) (i : I) (hi : ¬ ∃ j, e j = i) : extend e z i = 0 :=
  Function.extend_apply' z _ i hi

theorem sum_extend_sq (e : J ↪ I) (z : J → ℝ) : ∑ i, (extend e z i)^2 = ∑ j, (z j)^2 := by
  rw [sum_on_embedding e _ (fun i hi => by rw [extend_off e z i hi]; simp)]
  simp only [extend_apply]

def vector (σ : K × I → Bool) (i : I) : EuclideanSpace ℝ K :=
  WithLp.toLp 2 (fun a => FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K))

omit [Fintype I] in
@[simp] theorem vector_apply (σ : K × I → Bool) (i : I) (a : K) :
    vector σ i a = FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K) := rfl

theorem sign_sq (b : Bool) : (FiniteSigns.sign b)^2 = 1 := by cases b <;> norm_num [FiniteSigns.sign]

omit [Fintype I] in
theorem vector_norm [Nonempty K] (σ : K × I → Bool) (i : I) : ‖vector σ i‖ = 1 := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have h : ‖vector σ i‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vector_apply, Real.norm_eq_abs, sq_abs, div_pow, sign_sq,
      Real.sq_sqrt hk.le, Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp
  nlinarith [norm_nonneg (vector σ i)]

def synthesis (σ : K × I → Bool) (e : J ↪ I) : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ K :=
  ∑ j : J, InnerProductSpace.rankOne ℝ (vector σ (e j)) (EuclideanSpace.basisFun J ℝ j)

omit [Fintype I] in
@[simp] theorem synthesis_apply (σ : K × I → Bool) (e : J ↪ I) (z : EuclideanSpace ℝ J) :
    synthesis σ e z = ∑ j, z j • vector σ (e j) := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

def testCoefficients (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J) : K × I → ℝ :=
  fun ai => w ai.1 * extend e z ai.2 / Real.sqrt (Fintype.card K)

theorem testCoefficients_sq [Nonempty K] (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J)
    (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    ∑ ai, (testCoefficients e w z ai)^2 = 1 / (Fintype.card K : ℝ) := by
  have hk : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hw' : ∑ a, (w a)^2 = 1 := by
    have h : ‖w‖^2 = 1 := by rw [hw]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hz' : ∑ j, (z j)^2 = 1 := by
    have h : ‖z‖^2 = 1 := by rw [hz]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  simp only [testCoefficients, Fintype.sum_prod_type, mul_pow,
    div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, sum_extend_sq, hw', hz', mul_one, one_mul]
  rw [inv_pow, Real.sq_sqrt hk.le]

theorem bilinear_test (σ : K × I → Bool) (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J) :
    inner ℝ (synthesis σ e z) w = FiniteSigns.value (testCoefficients e w z) σ := by
  rw [synthesis_apply]
  simp only [sum_inner, inner_smul_left, RCLike.conj_to_real, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Pi.star_apply, star_trivial, vector_apply, FiniteSigns.value, testCoefficients,
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_on_embedding e _ (fun i hi => by rw [extend_off e z i hi]; simp)]
  simp only [extend_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The tail bound for each fixed pair of real unit test vectors and
an injective coordinate selection, on the full sign-matrix sample space. -/
theorem bilinear_tail [Nonempty K] (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J)
    (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    (((univ.filter fun σ : K × I → Bool => (5 : ℝ) < |inner ℝ (synthesis σ e z) w|).card : ℕ) : ℝ) /
      (2 : ℝ)^Fintype.card (K × I) ≤ 2 * Real.exp (-(Fintype.card K : ℝ)*25/2) := by
  simp_rw [bilinear_test]
  have h := FiniteSigns.two_sided_tail (k := (Fintype.card K : ℝ)) (u := 5) (testCoefficients e w z)
    (Nat.cast_pos.mpr (Fintype.card_pos (α := K))) (by norm_num : (0 : ℝ) < 5)
    (testCoefficients_sq e w z hw hz)
  convert h using 1 <;> try norm_num
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end SignMatrix
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Parameters

namespace OAI

/-! Ceiling parameters and dimension-ratio asymptotics. -/
noncomputable section
namespace Dixmier
open Filter Topology

def endpointCapacity (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ := ⌈(d : ℝ)^ℓ * ρ^ℓ⌉₊
def fiberDimension (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ :=
  ⌈2 * (endpointCapacity d ρ ℓ : ℝ) * Real.log (2 * (d : ℝ)^ℓ)⌉₊

theorem dimension_ratio_bound {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 ≤ ρ) (ℓ : ℕ) :
    (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ ≤
      2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hn : (0 : ℝ) < (d : ℝ)^ℓ := pow_pos (lt_of_lt_of_le zero_lt_one hdR) _
  have hn1 : (1 : ℝ) ≤ (d : ℝ)^ℓ := one_le_pow₀ hdR
  have hlog : 0 ≤ Real.log (2 * (d : ℝ)^ℓ) := Real.log_nonneg (by nlinarith)
  have hr : (endpointCapacity d ρ ℓ : ℝ) ≤ (d : ℝ)^ℓ * ρ^ℓ + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hn.le (pow_nonneg hρ _))).le
  have hk : (fiberDimension d ρ ℓ : ℝ) ≤
      2 * (endpointCapacity d ρ ℓ : ℝ) * Real.log (2 * (d : ℝ)^ℓ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (by positivity) hlog)).le
  have hk' : (fiberDimension d ρ ℓ : ℝ) ≤
      2 * ((d : ℝ)^ℓ * ρ^ℓ + 1) * Real.log (2 * (d : ℝ)^ℓ) + 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hr hlog]
  apply (div_le_iff₀ hn).mpr
  calc
    (fiberDimension d ρ ℓ : ℝ) ≤ 2 * ((d : ℝ)^ℓ * ρ^ℓ + 1) * Real.log (2 * (d : ℝ)^ℓ) + 1 := hk'
    _ = (2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ) * (d : ℝ)^ℓ := by
      field_simp

/-- The logarithm contributes only a linear factor in the word length. -/
theorem geometric_log_tendsto {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun ℓ : ℕ => a^ℓ * Real.log (2 * d^ℓ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one ha ha1
  have hl : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) * a^ℓ) atTop (𝓝 0) := by
    simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖a‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg ha] using ha1)).tendsto_atTop_zero
  have h := (hp.mul_const (Real.log 2)).add (hl.mul_const (Real.log d))
  simp only [zero_mul, zero_add] at h
  convert h using 1
  ext ℓ
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hd.ne'), Real.log_pow]
  ring

/-- The dimension ratio tends to zero. -/
theorem dimension_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ) atTop (𝓝 0) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hi0 : (0 : ℝ) ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hi1 : (d : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hdR
  have h1 := geometric_log_tendsto hρ hρ1 (lt_trans zero_lt_one hdR)
  have h2 := geometric_log_tendsto hi0 hi1 (lt_trans zero_lt_one hdR)
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1
  have hu : Tendsto (fun ℓ : ℕ =>
      2 * (ρ^ℓ + 1 / (d : ℝ)^ℓ) * Real.log (2 * (d : ℝ)^ℓ) + 1 / (d : ℝ)^ℓ)
      atTop (𝓝 0) := by
    have hh := ((h1.add h2).const_mul 2).add h3
    simp only [zero_add, mul_zero] at hh
    convert hh using 1
    ext ℓ
    simp only [one_div, inv_pow]
    ring
  exact squeeze_zero (fun ℓ => div_nonneg (Nat.cast_nonneg _) (by positivity))
    (dimension_ratio_bound hd hρ) hu

theorem endpointCapacity_pos {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (ℓ : ℕ) :
    0 < endpointCapacity d ρ ℓ := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (pow_pos (by exact_mod_cast (by omega : 0 < d)) _) (pow_pos hρ _)

theorem fiberDimension_pos {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) (ℓ : ℕ) :
    0 < fiberDimension d ρ ℓ := by
  have hr : (0 : ℝ) < endpointCapacity d ρ ℓ := by exact_mod_cast endpointCapacity_pos hd hρ ℓ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hn1 : (1 : ℝ) ≤ (d : ℝ)^ℓ := one_le_pow₀ hdR
  have hlog : 0 < Real.log (2 * (d : ℝ)^ℓ) := Real.log_pos (by nlinarith)
  apply Nat.ceil_pos.mpr
  exact mul_pos (mul_pos (by norm_num) hr) hlog

/-- Reciprocal dimension ratio used by the direct-sum obstruction. -/
theorem reciprocal_dimension_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (d : ℝ)^ℓ / (fiberDimension d ρ ℓ : ℝ)) atTop atTop := by
  have ht : Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ)
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨dimension_ratio_tendsto hd hρ.le hρ1, Filter.Eventually.of_forall (fun ℓ => ?_)⟩
    change 0 < (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ
    apply div_pos
    · exact_mod_cast fiberDimension_pos hd hρ ℓ
    · exact pow_pos (by exact_mod_cast (by omega : 0 < d)) _
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp ht

/-- A kernel energy satisfying the cardinality lower bound has
unbounded energy per fibre dimension. -/
theorem energy_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (E : ℕ → ℝ)
    (hE : ∀ ℓ, (d : ℝ)^ℓ ≤ E ℓ) :
    Tendsto (fun ℓ => E ℓ / (fiberDimension d ρ ℓ : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ (reciprocal_dimension_ratio_tendsto hd hρ hρ1)
  intro ℓ
  exact div_le_div_of_nonneg_right (hE ℓ) (Nat.cast_nonneg _)

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.FrameParameters

namespace OAI

/-! Ceiling dimensions and finite union-bound arithmetic for frames. -/
noncomputable section
namespace Dixmier
namespace FrameParameters

def dimension (n r : ℕ) : ℕ := ⌈2 * (r : ℝ) * Real.log (2 * (n : ℝ))⌉₊
def subfamilySize (n r : ℕ) : ℕ := min (2*r) n

theorem bounds {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    1 ≤ dimension n r ∧ subfamilySize n r ≤ dimension n r ∧
      (subfamilySize n r : ℝ) * Real.log n ≤ dimension n r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 1 < Real.log (2 * (n : ℝ)) := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by positivity)]
    linarith [Real.exp_one_lt_three]
  have hceil : 2 * (r : ℝ) * Real.log (2 * (n : ℝ)) ≤ dimension n r := Nat.le_ceil _
  have hp : (subfamilySize n r : ℝ) ≤ 2 * r := by exact_mod_cast Nat.min_le_left (2*r) n
  have hlogn : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hn0 (by linarith)
  have hp0 : (0 : ℝ) ≤ subfamilySize n r := Nat.cast_nonneg _
  have hkp : (subfamilySize n r : ℝ) ≤ dimension n r := by
    have hp2 := mul_le_mul_of_nonneg_left hlog.le (by positivity : (0 : ℝ) ≤ 2 * r)
    nlinarith
  refine ⟨?_, by exact_mod_cast hkp, ?_⟩
  · have : (1 : ℝ) ≤ dimension n r := by nlinarith
    exact_mod_cast this
  · calc
      _ ≤ (subfamilySize n r : ℝ) * Real.log (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left hlogn hp0
      _ ≤ 2 * (r : ℝ) * Real.log (2 * (n : ℝ)) := mul_le_mul_of_nonneg_right hp (by linarith)
      _ ≤ _ := hceil

/-- The frame failure probability is strictly below one. -/
theorem failure_bound_lt_one {n k p : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hp : p ≤ k) (hplog : (p : ℝ) * Real.log n ≤ k) :
    2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpk : (p : ℝ) ≤ k := by exact_mod_cast hp
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl9 : Real.log 9 ≤ 4 := by
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have h9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.log_pow]
      norm_num
    rw [h9]
    linarith
  have he : Real.log 2 + (p : ℝ)*Real.log n + ((k : ℝ)+p)*Real.log 9 -25*(k : ℝ)/2 < 0 := by
    have hh := mul_le_mul_of_nonneg_left hl9 (by positivity : (0 : ℝ) ≤ (k : ℝ)+p)
    nlinarith
  have hid : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) =
      Real.exp (Real.log 2 + (p : ℝ)*Real.log n + ((k : ℝ)+p)*Real.log 9 -25*(k : ℝ)/2) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add]
    simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_nat_mul,
      Real.exp_log hn0, ← Nat.cast_add]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 9)]
    congr 1
    ring_nf
  rw [hid]
  exact Real.exp_lt_one_iff.mpr he

theorem exact_failure_bound {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    2 * (n : ℝ)^(subfamilySize n r) * 9^(dimension n r + subfamilySize n r) *
      Real.exp (-25*(dimension n r : ℝ)/2) < 1 :=
  failure_bound_lt_one hn (bounds hn hr).1 (bounds hn hr).2.1 (bounds hn hr).2.2

end FrameParameters
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.FrameSelection

namespace OAI

/-! The finite union bound chooses one sign matrix that passes every real
net test for every injective subfamily of the prescribed size. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset

theorem embedding_card_le (n p : ℕ) : Fintype.card (Fin p ↪ Fin n) ≤ n^p := by
  have h := Fintype.card_le_of_injective (fun e : Fin p ↪ Fin n => (e : Fin p → Fin n))
    (by intro e f h; apply Function.Embedding.ext; intro i; exact congrFun h i)
  simpa using h

/-- A real sign-matrix realization for all size-p subfamilies. The proof
uses the actual finite sign sample space, cardinality bounds, and net tests. -/
theorem exists_sign_matrix {n k p : ℕ} (hk : 0 < k)
    (hf : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1) :
    ∃ σ : Fin k × Fin n → Bool, ∀ e : Fin p ↪ Fin n, ‖synthesis σ e‖ ≤ 10 := by
  classical
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨s, hs, hsc, hsnet⟩ := SphereNet.exists_quarter_net (E := EuclideanSpace ℝ (Fin p))
  obtain ⟨t, ht, htc, htnet⟩ := SphereNet.exists_quarter_net (E := EuclideanSpace ℝ (Fin k))
  simp only [finrank_euclideanSpace_fin] at hsc htc
  let Ω := Fin k × Fin n → Bool
  let L := (Fin p ↪ Fin n) × s × t
  let bad : L → Finset Ω := fun l => univ.filter (fun σ =>
    (5 : ℝ) < |inner ℝ (synthesis σ l.1 l.2.1) l.2.2|)
  let B : Finset Ω := univ.biUnion bad
  let N : ℝ := 2 ^ Fintype.card (Fin k × Fin n)
  let q : ℝ := 2 * Real.exp (-25*(k : ℝ)/2)
  have hN : 0 < N := by positivity
  have hq : 0 ≤ q := by positivity
  have hb (l : L) : ((bad l).card : ℝ) ≤ q * N := by
    have h := bilinear_tail l.1 l.2.2 l.2.1 (ht _ l.2.2.2) (hs _ l.2.1.2)
    simp only [Fintype.card_fin] at h
    have he : -(k : ℝ)*25/2 = -25*(k : ℝ)/2 := by ring
    rw [he] at h
    apply (div_le_iff₀ hN).mp
    convert h using 1
    try rfl
    apply congrArg (fun m : ℕ => (m : ℝ) / N)
    apply congrArg Finset.card
    ext σ
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  have hB : (B.card : ℝ) ≤ (Fintype.card L : ℝ) * (q*N) := by
    have hc := Finset.card_biUnion_le (s := (univ : Finset L)) (t := bad)
    calc
      _ ≤ ∑ l : L, ((bad l).card : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ _l : L, q*N := Finset.sum_le_sum (fun l _ => hb l)
      _ = _ := by simp
  have hL : (Fintype.card L : ℝ) ≤ (n : ℝ)^p * 9^p * 9^k := by
    have hc : Fintype.card L = Fintype.card (Fin p ↪ Fin n) * s.card * t.card := by
      simp [L, mul_assoc]
    rw [hc, Nat.cast_mul, Nat.cast_mul]
    exact mul_le_mul (mul_le_mul (by exact_mod_cast embedding_card_le n p) (by exact_mod_cast hsc)
      (by positivity) (by positivity)) (by exact_mod_cast htc) (by positivity) (by positivity)
  have hB' : (B.card : ℝ) < N := by
    have hle := hB.trans (mul_le_mul_of_nonneg_right hL (mul_nonneg hq hN.le))
    have hid : (n : ℝ)^p * 9^p * 9^k * (q*N) =
        (2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2)) * N := by
      dsimp [q]
      rw [pow_add]
      ring
    rw [hid] at hle
    exact hle.trans_lt (by simpa using mul_lt_mul_of_pos_right hf hN)
  have hcard : B.card < (univ : Finset Ω).card := by
    have hNcard : N = (Fintype.card Ω : ℝ) := by simp [N, Ω]
    rw [hNcard] at hB'
    exact_mod_cast hB'
  have hnotall : ∃ σ : Ω, σ ∉ B := by
    by_contra hh
    push Not at hh
    have hle := Finset.card_le_card (show (univ : Finset Ω) ⊆ B from fun σ _ => hh σ)
    omega
  obtain ⟨σ, hnσ⟩ := hnotall
  refine ⟨σ, ?_⟩
  intro e
  apply SphereNet.operator_norm_le_ten (synthesis σ e) s t hs ht hsnet htnet
  intro z hz w hw
  by_contra hnot
  have hbad : σ ∈ bad (e, ⟨z,hz⟩, ⟨w,hw⟩) := by
    exact mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hnot⟩
  exact hnσ (mem_biUnion.mpr ⟨(e, ⟨z,hz⟩, ⟨w,hw⟩), mem_univ _, hbad⟩)

end SignMatrix
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.ComplexFrames

namespace OAI

/-! Complexification preserves real synthesis norm bounds.
The real and imaginary coefficient vectors are handled separately. -/
noncomputable section
namespace Dixmier
namespace ComplexFrames
open Finset
variable {I K : Type*} [Fintype K]
local instance : DecidableEq I := Classical.decEq I

def ofReal (v : EuclideanSpace ℝ K) : EuclideanSpace ℂ K := WithLp.toLp 2 (fun a => (v a : ℂ))
def realPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).re)
def imagPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).im)

theorem ofReal_norm (v : EuclideanSpace ℝ K) : ‖ofReal v‖ = ‖v‖ := by
  have h : ‖ofReal v‖^2 = ‖v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, ofReal, Complex.norm_real]
  nlinarith [norm_nonneg (ofReal v), norm_nonneg v]

theorem norm_sq_split (z : EuclideanSpace ℂ K) :
    ‖z‖^2 = ‖realPart z‖^2 + ‖imagPart z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, realPart, imagPart,
    Real.norm_eq_abs, sq_abs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem synthesis_realPart (v : I → EuclideanSpace ℝ K) (J : Finset I) (z : EuclideanSpace ℂ J) :
    realPart (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z) =
      ∑ i : J, (realPart z) i • v i := by
  ext a
  simp only [FiniteSynthesis.synthesis_apply, realPart, ofReal, WithLp.ofLp_toLp,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem synthesis_imagPart (v : I → EuclideanSpace ℝ K) (J : Finset I) (z : EuclideanSpace ℂ J) :
    imagPart (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z) =
      ∑ i : J, (imagPart z) i • v i := by
  ext a
  simp only [FiniteSynthesis.synthesis_apply, imagPart, ofReal, WithLp.ofLp_toLp,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Complex.im_sum,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

theorem synthesis_bound (v : I → EuclideanSpace ℝ K) (J : Finset I) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ z : EuclideanSpace ℝ J, ‖∑ i : J, z i • v i‖ ≤ b*‖z‖) :
    ‖FiniteSynthesis.synthesis (fun i => ofReal (v i)) J‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro z
  have hr := pow_le_pow_left₀ (norm_nonneg _) (h (realPart z)) 2
  have hi := pow_le_pow_left₀ (norm_nonneg _) (h (imagPart z)) 2
  have hsq : ‖FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z‖^2 ≤ b^2*‖z‖^2 := by
    rw [norm_sq_split, synthesis_realPart, synthesis_imagPart, norm_sq_split z]
    nlinarith [hr, hi]
  nlinarith [norm_nonneg (FiniteSynthesis.synthesis (fun i => ofReal (v i)) J z),
    norm_nonneg z, mul_nonneg hb (norm_nonneg z)]

end ComplexFrames
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Frames

namespace OAI

/-! Frame existence with prescribed dimensions and bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq J := Classical.decEq J
local instance : DecidableEq L := Classical.decEq L
local instance : DecidableEq K := Classical.decEq K

def extendVector (e : J ↪ L) (z : EuclideanSpace ℝ J) : EuclideanSpace ℝ L :=
  WithLp.toLp 2 (extend e z)

theorem extendVector_norm (e : J ↪ L) (z : EuclideanSpace ℝ J) : ‖extendVector e z‖ = ‖z‖ := by
  have h : ‖extendVector e z‖^2 = ‖z‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, extendVector, Real.norm_eq_abs, sq_abs]
    exact sum_extend_sq e z
  nlinarith [norm_nonneg (extendVector e z), norm_nonneg z]

omit [Fintype I] in
theorem synthesis_extendVector (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L)
    (z : EuclideanSpace ℝ J) : synthesis σ e (extendVector f z) = synthesis σ (f.trans e) z := by
  simp only [synthesis_apply, extendVector]
  rw [sum_on_embedding f _ (fun i hi => by rw [extend_off f z i hi]; simp)]
  simp only [extend_apply, Function.Embedding.trans_apply]

omit [Fintype I] in
theorem synthesis_restrict_norm (σ : K × I → Bool) (e : L ↪ I) (f : J ↪ L) :
    ‖synthesis σ (f.trans e)‖ ≤ ‖synthesis σ e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  rw [← synthesis_extendVector]
  exact ((synthesis σ e).le_opNorm _).trans_eq (by rw [extendVector_norm])

/-- Extend each smaller subset to size p, then restrict a coordinate synthesis operator. -/
theorem all_subfamilies {k p : ℕ} (hp : p ≤ Fintype.card I) (σ : Fin k × I → Bool)
    (hσ : ∀ e : Fin p ↪ I, ‖synthesis σ e‖ ≤ 10) :
    ∀ J : Finset I, J.card ≤ p →
      ‖FiniteSynthesis.synthesis (fun i => ComplexFrames.ofReal (vector σ i)) J‖ ≤ 10 := by
  classical
  intro J hJ
  obtain ⟨L, hJL, hLu, hLc⟩ := Finset.exists_subsuperset_card_eq (s := J) (t := univ)
    (Finset.subset_univ _) hJ (by simpa using hp)
  let eL : L ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  let q : L ≃ Fin p := L.equivFinOfCardEq hLc
  let e : Fin p ↪ I := q.symm.toEmbedding.trans eL
  have he : q.toEmbedding.trans e = eL := by ext i; simp [e]
  have hL : ‖synthesis σ eL‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ e q.toEmbedding
    rw [he] at h
    exact h.trans (hσ e)
  let f : J ↪ L := ⟨fun i => ⟨i.1, hJL i.2⟩, by intro a b h; exact Subtype.ext (congrArg (fun x : L => (x : I)) h)⟩
  let eJ : J ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hf : f.trans eL = eJ := by ext i; rfl
  have hJnorm : ‖synthesis σ eJ‖ ≤ 10 := by
    have h := synthesis_restrict_norm σ eL f
    rw [hf] at h
    exact h.trans hL
  apply ComplexFrames.synthesis_bound _ J (by norm_num : (0 : ℝ) ≤ 10)
  intro z
  have h := (synthesis σ eJ).le_of_opNorm_le hJnorm z
  simpa only [synthesis_apply, eJ, Function.Embedding.coeFn_mk] using h

/-- Frames with k=ceil(2r log(2n)), p=min(2r,n), and bound 10. -/
theorem frames {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    ∃ v : Fin n → EuclideanSpace ℂ (Fin (FrameParameters.dimension n r)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (FrameParameters.subfamilySize n r) 10 := by
  have hk : 0 < FrameParameters.dimension n r := (FrameParameters.bounds hn hr).1
  let : Nonempty (Fin (FrameParameters.dimension n r)) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨σ, hσ⟩ := exists_sign_matrix hk (FrameParameters.exact_failure_bound hn hr)
  refine ⟨fun i => ComplexFrames.ofReal (vector σ i), ?_, ?_⟩
  · intro i
    rw [ComplexFrames.ofReal_norm, vector_norm]
  · exact all_subfamilies (by simpa only [FrameParameters.subfamilySize, Fintype.card_fin] using Nat.min_le_right (2*r) n) σ hσ


/-- The frame lemma for arbitrary finite label types. -/
theorem frames_for_fintype {r : ℕ} (hn : 2 ≤ Fintype.card I) (hr : 1 ≤ r) :
    ∃ v : I → EuclideanSpace ℂ (Fin (FrameParameters.dimension (Fintype.card I) r)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (FrameParameters.subfamilySize (Fintype.card I) r) 10 := by
  have hk : 0 < FrameParameters.dimension (Fintype.card I) r := (FrameParameters.bounds hn hr).1
  let : Nonempty (Fin (FrameParameters.dimension (Fintype.card I) r)) := Fin.pos_iff_nonempty.mp hk
  obtain ⟨σ, hσ⟩ := exists_sign_matrix hk (FrameParameters.exact_failure_bound hn hr)
  let q := Fintype.equivFin I
  let σ' : Fin (FrameParameters.dimension (Fintype.card I) r) × I → Bool := fun ai => σ (ai.1, q ai.2)
  have hσ' (e : Fin (FrameParameters.subfamilySize (Fintype.card I) r) ↪ I) : ‖synthesis σ' e‖ ≤ 10 := by
    have hid : synthesis σ' e = synthesis σ (e.trans q.toEmbedding) := rfl
    rw [hid]
    exact hσ _
  refine ⟨fun i => ComplexFrames.ofReal (vector σ' i), ?_, ?_⟩
  · intro i
    rw [ComplexFrames.ofReal_norm, vector_norm]
  · exact all_subfamilies (Nat.min_le_right _ _) σ' hσ'


end SignMatrix
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Masked

namespace OAI

/-! Bounded masked operators. All labels remain separate, including
repeated values of the product list. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ
abbrev Space (G K : Type*) [Fintype K] : Type _ := KernelObstruction.Space G K
abbrev Fibre (K : Type*) [Fintype K] := EuclideanSpace ℂ K

def shift (s : G) : Space G K →L[ℂ] Space G K :=
  (KernelObstruction.reindexIsometry (K := K) (Equiv.mulRight s)).toContinuousLinearMap

@[simp] theorem shift_apply (s : G) (ξ : Space G K) (x : G) : shift s ξ x = ξ (x*s) := rfl

def term (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (i : I) : Space G K →L[ℂ] Space G K :=
  (HilbertSum.boundedSum (κ := ‖v i‖ * ‖v i‖) (fun x => c x i • InnerProductSpace.rankOne ℂ (v i) (v i))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun x => by
      rw [norm_smul, InnerProductSpace.norm_rankOne]
      exact (mul_le_mul_of_nonneg_right (hc x i) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (one_mul _))).comp
    (shift (s i))

def operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) : Space G K →L[ℂ] Space G K := ∑ i, term v s c hc i

omit [Fintype I] in
@[simp] theorem term_apply (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (i : I) (ξ : Space G K) (x : G) :
    term v s c hc i ξ x = (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
  change (c x i) • (InnerProductSpace.rankOne ℂ (v i) (v i) (ξ (x*s i))) = _
  rw [InnerProductSpace.rankOne_apply, smul_smul]

@[simp] theorem operator_apply (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (ξ : Space G K) (x : G) :
    operator v s c hc ξ x = ∑ i, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
  simp only [operator, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply, term_apply]

def rowSet (c : G → I → ℂ) (x : G) : Finset I := univ.filter (fun i => c x i ≠ 0)
def columnSet (s : I → G) (c : G → I → ℂ) (y : G) : Finset I :=
  univ.filter (fun i => c (y*(s i)⁻¹) i ≠ 0)

def edgeEnergy (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (x : G) : ℝ :=
  ∑ i, if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0

omit [Fintype I] in
theorem edge_summable (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) (i : I) :
    Summable (fun x => if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) := by
  have hs := ((KernelObstruction.space_summable ξ).comp_injective
    (Equiv.mulRight (s i)).injective).mul_left (‖v i‖^2)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro x; split_ifs <;> positivity
  · intro x
    split_ifs
    · change ‖inner ℂ (v i) (ξ (x*s i))‖^2 ≤ ‖v i‖^2 * ‖ξ (x*s i)‖^2
      calc
        _ ≤ (‖v i‖ * ‖ξ (x*s i)‖)^2 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_inner_le_norm (𝕜 := ℂ) (v i) (ξ (x*s i))) 2
        _ = _ := mul_pow _ _ _
    · change 0 ≤ ‖v i‖^2 * ‖ξ (x*s i)‖^2
      positivity

theorem edgeEnergy_summable (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) :
    Summable (edgeEnergy v s c ξ) := summable_sum (fun i _ => edge_summable v s c ξ i)

theorem sum_subfamily {R : Type*} [AddCommMonoid R] (c : I → ℂ) (f : I → R) :
    (∑ i : univ.filter (fun i => c i ≠ 0), f i) = ∑ i, if c i ≠ 0 then f i else 0 := by
  rw [Finset.sum_coe_sort, Finset.sum_filter]

theorem row_estimate (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (ξ : Space G K) (x : G) :
    ‖operator v s c hc ξ x‖^2 ≤ b^2 * edgeEnergy v s c ξ x := by
  let J := rowSet c x
  have hsum : operator v s c hc ξ x =
      ∑ i : J, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
    calc
      _ = ∑ i, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := operator_apply ..
      _ = ∑ i ∈ J, (c x i * inner ℂ (v i) (ξ (x*s i))) • v i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i hi hn
        have hz : c x i = 0 := by simpa [J, rowSet] using hn
        simp [hz]
      _ = _ := (Finset.sum_coe_sort J (fun i => (c x i * inner ℂ (v i) (ξ (x*s i))) • v i)).symm
  rw [hsum]
  have h := FiniteSynthesis.synthesis_sq_le v J hb (hrow x)
    (fun i => c x i * inner ℂ (v i) (ξ (x*s i)))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
  have he : edgeEnergy v s c ξ x = ∑ i : J, ‖inner ℂ (v i) (ξ (x*s i))‖^2 := by
    exact (sum_subfamily (c x) (fun i => ‖inner ℂ (v i) (ξ (x*s i))‖^2)).symm
  rw [he]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, mul_pow]
  have hm : ‖c x i‖^2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) (hc x i) 2
  exact (mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans_eq (one_mul _)

theorem edgeEnergy_reindex (v : I → Fibre K) (s : I → G) (c : G → I → ℂ) (ξ : Space G K) :
    ∑' x, edgeEnergy v s c ξ x =
      ∑' y, ∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2 := by
  let f : G → I → ℝ := fun y i => if c (y*(s i)⁻¹) i ≠ 0 then ‖inner ℂ (v i) (ξ y)‖^2 else 0
  have he (i : I) : (fun y => f y i) =
      (fun y => if c y i ≠ 0 then ‖inner ℂ (v i) (ξ (y*s i))‖^2 else 0) ∘
        (Equiv.mulRight (s i)⁻¹) := by
    funext y
    simp [f, mul_assoc]
  have hs (i : I) : Summable (fun y => f y i) := by
    rw [he]
    exact (edge_summable v s c ξ i).comp_injective (Equiv.mulRight (s i)⁻¹).injective
  change (∑' x, ∑ i, _) = _
  rw [Summable.tsum_finsetSum (fun i _ => edge_summable v s c ξ i)]
  have ht (i : I) : (∑' x, if c x i ≠ 0 then ‖inner ℂ (v i) (ξ (x*s i))‖^2 else 0) = ∑' y, f y i := by
    rw [he]
    exact ((Equiv.mulRight (s i)⁻¹).tsum_eq _).symm
  simp_rw [ht]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  apply tsum_congr
  intro y
  exact (sum_subfamily (fun i => c (y*(s i)⁻¹) i) (fun i => ‖inner ℂ (v i) (ξ y)‖^2)).symm

/-- Row and column synthesis bounds imply the masked operator bound,
without assuming that the product labels s_i are distinct. -/
theorem masked_bound (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hrow : ∀ x, ‖FiniteSynthesis.synthesis v (rowSet c x)‖ ≤ b)
    (hcol : ∀ y, ‖FiniteSynthesis.synthesis v (columnSet s c y)‖ ≤ b) :
    ‖operator v s c hc‖ ≤ b^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg b)
  intro ξ
  have hr := (KernelObstruction.space_summable (operator v s c hc ξ)).tsum_le_tsum
    (row_estimate v s c hc hb hrow ξ) ((edgeEnergy_summable v s c ξ).mul_left (b^2))
  rw [tsum_mul_left, ← KernelObstruction.space_norm_sq, edgeEnergy_reindex] at hr
  have hcs : Summable (fun y => ∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2) := by
    have h (y : G) : (∑ i : columnSet s c y, ‖inner ℂ (v i) (ξ y)‖^2) =
        ∑ i : I, if c (y*(s i)⁻¹) i ≠ 0 then ‖inner ℂ (v i) (ξ y)‖^2 else 0 := by
      exact sum_subfamily (fun i => c (y*(s i)⁻¹) i) (fun i => ‖inner ℂ (v i) (ξ y)‖^2)
    simp_rw [h]
    apply summable_sum
    intro i hi
    have hs := (edge_summable v s c ξ i).comp_injective (Equiv.mulRight (s i)⁻¹).injective
    simpa [Function.comp_def, mul_assoc] using hs
  have hcol' := hcs.tsum_le_tsum (fun y => FiniteSynthesis.analysis_sq_le v _ hb (hcol y) (ξ y))
    ((KernelObstruction.space_summable ξ).mul_left (b^2))
  rw [tsum_mul_left, ← KernelObstruction.space_norm_sq] at hcol'
  have hh := hr.trans (mul_le_mul_of_nonneg_left hcol' (sq_nonneg b))
  have hpos : 0 ≤ b^2 * ‖ξ‖ := mul_nonneg (sq_nonneg b) (norm_nonneg ξ)
  nlinarith [norm_nonneg (operator v s c hc ξ)]

end Masked
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.MaskAlgebra

namespace OAI

/-! Sparse masks yield operator conjugation identities, and the
constant mask has a rank-one collision kernel. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
open scoped ComplexConjugate
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- The masked operator bound in finite-cardinality form. -/
theorem masked_bound_of_frame (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v p b)
    (hr : ∀ x, (rowSet c x).card ≤ p) (hcol : ∀ y, (columnSet s c y).card ≤ p) :
    ‖operator v s c hc‖ ≤ b^2 :=
  masked_bound v s c hc hb (fun x => hv _ (hr x)) (fun y => hv _ (hcol y))

theorem operator_sub (v : I → Fibre K) (s : I → G) (c d : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (hd : ∀ x i, ‖d x i‖ ≤ 1)
    (hcd : ∀ x i, ‖c x i - d x i‖ ≤ 1) :
    operator v s c hc - operator v s d hd = operator v s (fun x i => c x i-d x i) hcd := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change operator v s c hc ξ x - operator v s d hd ξ x = _
  simp only [operator_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

theorem conjugate_operator (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) (g : G) :
    conjugate KernelObstruction.translation g (operator v s c hc) =
      operator v s (fun x i => c (g⁻¹*x) i) (fun _ i => hc _ i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext x
  change KernelObstruction.translation g (operator v s c hc (KernelObstruction.translation g⁻¹ ξ)) x = _
  simp only [KernelObstruction.translation_apply, operator_apply, inv_inv,
    ← mul_assoc, mul_inv_cancel, one_mul]

def constant (v : I → Fibre K) (s : I → G) : Space G K →L[ℂ] Space G K :=
  operator v s (fun _ _ => 1) (fun _ _ => by simp)

theorem constant_commutant (v : I → Fibre K) (s : I → G) :
    constant v s ∈ KernelObstruction.Commutant := by
  intro g
  apply Commute.symm
  apply (conjugate_eq_self_iff_commute KernelObstruction.translation g (constant v s)).mp
  exact conjugate_operator v s (fun _ _ => 1) (fun _ _ => by simp) g

theorem basis_inner_right (v : Fibre K) (b : K) :
    inner ℂ v (EuclideanSpace.basisFun K ℂ b) = conj (v b) := by
  rw [← EuclideanSpace.basisFun_inner K ℂ v b, inner_conj_symm]

theorem constant_kernel (v : I → Fibre K) (s : I → G) (g : G) :
    KernelObstruction.coefficients (KernelObstruction.block (constant v s) 1 g) =
      kernelCoefficients v s g := by
  apply (WithLp.equiv 2 ((K × K) → ℂ)).injective
  funext ab
  rcases ab with ⟨a,b⟩
  change (constant v s (lp.single (E := fun _ : G => Fibre K) 2 g (EuclideanSpace.basisFun K ℂ b)) 1) a = kernelCoefficients v s g (a,b)
  simp only [constant, operator_apply, one_mul, kernelCoefficients,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : s i = g
  · simp only [h, lp.single_apply_self, ite_true]
    change inner ℂ (v i) (EuclideanSpace.basisFun K ℂ b) * v i a = v i a * conj (v i b)
    rw [basis_inner_right, mul_comm]
  · simp [h]

theorem constant_energy_ge_card (v : I → Fibre K) (hv : ∀ i, ‖v i‖ = 1) (s : I → G) :
    (Fintype.card I : ℝ) ≤ KernelObstruction.energy (constant v s) := by
  unfold KernelObstruction.energy
  simp_rw [constant_kernel]
  exact kernel_energy_ge_card v hv s

omit [Group G] [Fintype I] in
theorem bool_mask_norm (a : G → I → Bool) (x : G) (i : I) : ‖boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

def oriented (v : I → Fibre K) (s : I → G) (a : G → I → Bool) : Space G K →L[ℂ] Space G K :=
  operator v s (fun x i => boolComplex (a x i)) (bool_mask_norm a)

theorem difference_operator (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (g : G) :
    coboundary KernelObstruction.translation (oriented v s a) g =
      operator v s (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i))
        (fun _ _ => difference_mask_norm _ _) := by
  rw [coboundary, oriented, conjugate_operator]
  exact operator_sub _ _ _ _ _ _ _

theorem difference_norm_le (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (hc : ∀ y, (columnZeros a s y).card ≤ r) (g : G) :
    ‖coboundary KernelObstruction.translation (oriented v s a) g‖ ≤ b^2 := by
  rw [difference_operator]
  apply masked_bound_of_frame _ _ _ _ hb hv
  · intro x
    have h : rowSet (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i)) x = rowDifference a g x := by
      ext i
      simp [rowSet, rowDifference, difference_mask_ne_zero]
    rw [h]
    exact rowDifference_card_le a r hr g x
  · intro y
    have h : columnSet s (fun x i => boolComplex (a x i) - boolComplex (a (g⁻¹*x) i)) y = columnDifference a s g y := by
      ext i
      simp [columnSet, columnDifference, difference_mask_ne_zero]
    rw [h]
    exact columnDifference_card_le a s r hc g y

end Masked
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.LocalBounds

namespace OAI

/-! Individual block row and column bounds from the endpoint assignment. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq ℂ := Classical.decEq ℂ

theorem support_bound (v : I → Fibre K) (s : I → G) (c : G → I → ℂ)
    (hc : ∀ x i, ‖c x i‖ ≤ 1) {p : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v p b) (J : Finset I) (hJ : J.card ≤ p)
    (hs : ∀ x i, c x i ≠ 0 → i ∈ J) : ‖operator v s c hc‖ ≤ b^2 := by
  apply masked_bound_of_frame _ _ _ _ hb hv
  · intro x
    exact (Finset.card_le_card (fun i hi => hs x i (Finset.mem_filter.mp hi).2)).trans hJ
  · intro y
    exact (Finset.card_le_card (fun i hi => hs _ i (Finset.mem_filter.mp hi).2)).trans hJ

def rowMask (a : G → I → Bool) (x₀ x : G) (i : I) : ℂ :=
  if x = x₀ then boolComplex (a x i) else 0

def columnMask (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) : ℂ :=
  if x * s i = y₀ then 1 - boolComplex (a x i) else 0

omit [Group G] [Fintype I] in
theorem rowMask_norm (a : G → I → Bool) (x₀ x : G) (i : I) : ‖rowMask a x₀ x i‖ ≤ 1 := by
  unfold rowMask
  split_ifs
  · exact bool_mask_norm a x i
  · simp

omit [Group G] [Fintype I] in
theorem complement_norm (a : G → I → Bool) (x : G) (i : I) : ‖1 - boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

omit [Fintype I] in
theorem columnMask_norm (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) :
    ‖columnMask a s y₀ x i‖ ≤ 1 := by
  unfold columnMask
  split_ifs
  · exact complement_norm a x i
  · simp

omit [Group G] in
theorem rowMask_support (a : G → I → Bool) (x₀ x : G) (i : I) (h : rowMask a x₀ x i ≠ 0) :
    i ∈ rowOnes a x₀ := by
  unfold rowMask at h
  split_ifs at h with he
  · subst x
    cases ha : a x₀ i <;> simp_all [boolComplex, rowOnes]
  · exact (h rfl).elim

theorem columnMask_support (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I)
    (h : columnMask a s y₀ x i ≠ 0) : i ∈ columnZeros a s y₀ := by
  unfold columnMask at h
  split_ifs at h with he
  · have hx : y₀ * (s i)⁻¹ = x := by rw [← he, mul_inv_cancel_right]
    cases ha : a x i <;> simp_all [boolComplex, columnZeros]
  · exact (h rfl).elim

theorem row_localization (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (x₀ : G) :
    KernelObstruction.row (oriented v s a) x₀ =
      KernelObstruction.row (operator v s (rowMask a x₀) (rowMask_norm a x₀)) x₀ := by
  ext ξ z
  change (oriented v s a ξ x₀) z = (operator v s (rowMask a x₀) (rowMask_norm a x₀) ξ x₀) z
  simp [oriented, operator_apply, rowMask]

theorem column_localization (v : I → Fibre K) (s : I → G) (a : G → I → Bool) (y₀ : G) :
    KernelObstruction.col (constant v s - oriented v s a) y₀ =
      KernelObstruction.col (operator v s (columnMask a s y₀) (columnMask_norm a s y₀)) y₀ := by
  have hsub : constant v s - oriented v s a =
      operator v s (fun x i => 1 - boolComplex (a x i)) (complement_norm a) :=
    operator_sub _ _ _ _ _ _ _
  rw [hsub]
  apply ContinuousLinearMap.ext
  intro z
  apply lp.ext
  funext x
  change operator v s (fun x i => 1 - boolComplex (a x i)) (complement_norm a) (lp.single 2 y₀ z) x =
    operator v s (columnMask a s y₀) (columnMask_norm a s y₀) (lp.single 2 y₀ z) x
  simp only [operator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x * s i = y₀
  · simp [columnMask, h]
  · rw [lp.single_apply_ne _ _ _ h]
    simp [columnMask, h]

theorem local_row_bound (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (x₀ : G) :
    ‖KernelObstruction.row (oriented v s a) x₀‖ ≤ b^2 := by
  have hJ : (rowOnes a x₀).card ≤ min (2*r) (Fintype.card I) :=
    le_min ((hr x₀).trans (by omega)) (Finset.card_le_univ _)
  have h := support_bound v s (rowMask a x₀) (rowMask_norm a x₀) hb hv (rowOnes a x₀) hJ
    (rowMask_support a x₀)
  rw [row_localization]
  exact (KernelObstruction.row_norm_le _ _).trans h

theorem local_column_bound (v : I → Fibre K) (s : I → G) (a : G → I → Bool)
    {r : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hv : FiniteSynthesis.FrameBound v (min (2*r) (Fintype.card I)) b)
    (hc : ∀ y, (columnZeros a s y).card ≤ r) (y₀ : G) :
    ‖KernelObstruction.col (constant v s - oriented v s a) y₀‖ ≤ b^2 := by
  have hJ : (columnZeros a s y₀).card ≤ min (2*r) (Fintype.card I) :=
    le_min ((hc y₀).trans (by omega)) (Finset.card_le_univ _)
  have h := support_bound v s (columnMask a s y₀) (columnMask_norm a s y₀) hb hv (columnZeros a s y₀) hJ
    (columnMask_support a s y₀)
  rw [column_localization]
  exact (KernelObstruction.col_norm_le _ _).trans h

end Masked
end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.Main

namespace OAI

/-! The uniformly bounded nonunitarizable representation of a countable
nonamenable group, assembled from sparse masks, frames, and the direct-sum obstruction. -/
noncomputable section
namespace Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [Countable G] [TopologicalSpace G] [DiscreteTopology G]

/-- A uniformly 101-bounded representation on a separable Hilbert space,
not similar to a unitary representation, constructed from nonamenability. -/
theorem nonamenable_witness (hG : ¬ Amenable G) : NonamenableWitness.{u,u} G := by
  classical
  obtain ⟨S, hS, hd, ρ, hρ, hρ1, hmask⟩ := sparse_splitting_of_nonamenable hG
  let d := S.card
  let k : ℕ → ℕ := fun j => fiberDimension d ρ (j+1)
  let r : ℕ → ℕ := fun j => endpointCapacity d ρ (j+1)
  let Labels : ℕ → Type u := fun j => Word S (j+1)
  let s : ∀ j, Labels j → G := fun j => wordProduct (fun x : S => (x : G)) (j+1)
  have hlabel (j : ℕ) : Fintype.card (Labels j) = d^(j+1) := by
    simp [Labels, word_card, d]
  have hn (j : ℕ) : 2 ≤ Fintype.card (Labels j) := by
    rw [hlabel]
    have hp : 1 ≤ d^j := one_le_pow₀ (by omega : 1 ≤ d)
    rw [pow_succ']
    dsimp [d] at *
    nlinarith
  have hr (j : ℕ) : 1 ≤ r j := endpointCapacity_pos hd hρ (j+1)
  have hk (j : ℕ) : 0 < k j := fiberDimension_pos hd hρ (j+1)
  have hdim (j : ℕ) : FrameParameters.dimension (Fintype.card (Labels j)) (r j) = k j := by
    simp [FrameParameters.dimension, hlabel, k, fiberDimension, r, Nat.cast_pow]
  have hframes (j : ℕ) : ∃ v : Labels j → EuclideanSpace ℂ (Fin (k j)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (min (2*r j) (Fintype.card (Labels j))) 10 := by
    have h := SignMatrix.frames_for_fintype (hn j) (hr j)
    rw [hdim j] at h
    exact h
  choose v hvunit hvframe using hframes
  have hmasks (j : ℕ) : ∃ a : G → Labels j → Bool,
      (∀ x, (rowOnes a x).card ≤ r j) ∧ ∀ y, (columnZeros a (s j) y).card ≤ r j :=
    hmask (j+1) (by omega)
  choose a har hac using hmasks
  let A : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.constant (v j) (s j)
  let T : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.oriented (v j) (s j) (a j)
  have hA (j : ℕ) : A j ∈ KernelObstruction.Commutant := Masked.constant_commutant _ _
  have hrow (j : ℕ) : ‖KernelObstruction.row (T j) 1‖ ≤ 100 := by
    have h := Masked.local_row_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) 1
    norm_num at h
    exact h
  have hcol (j : ℕ) : ‖KernelObstruction.col (A j-T j) 1‖ ≤ 100 := by
    have h := Masked.local_column_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (hac j) 1
    norm_num at h
    exact h
  have hdiff (j : ℕ) (g : G) : ‖coboundary KernelObstruction.translation (T j) g‖ ≤ 100 := by
    have h := Masked.difference_norm_le (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) (hac j) g
    norm_num at h
    exact h
  have henergy (j : ℕ) : (d : ℝ)^(j+1) ≤ KernelObstruction.energy (A j) := by
    have h := Masked.constant_energy_ge_card (v j) (hvunit j) (s j)
    rw [hlabel] at h
    simpa only [Nat.cast_pow] using h
  have hratio : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop := by
    have hbase := (reciprocal_dimension_ratio_tendsto hd hρ hρ1).comp (tendsto_add_atTop_nat 1)
    apply tendsto_atTop_mono _ hbase
    intro j
    exact div_le_div_of_nonneg_right (henergy j) (Nat.cast_nonneg _)
  obtain ⟨π, hπbound, hπnot⟩ := DirectSumObstruction.direct_sum_obstruction k hk A T hA
    (by norm_num : (0 : ℝ) ≤ 100) hrow hcol hdiff hratio
  let : TopologicalSpace.SeparableSpace (DirectSumObstruction.Carrier G k) :=
    DirectSumObstruction.carrier_separable k
  refine ⟨DirectSumObstruction.Carrier G k, inferInstance, inferInstance, inferInstance, inferInstance,
    π, ?_, hπnot⟩
  intro g
  convert hπbound g using 1
  norm_num

/-- The conclusion at the common group/Hilbert-space universe. -/
theorem main_theorem : MainTheorem.{u,u} := by
  intro G _ _ _ _ hG
  exact nonamenable_witness hG

/-- Unitarizability implies amenability, without a common similarity bound. -/
theorem amenable_of_unitarizable (hG : Unitarizable.{u,u} G) : Amenable G := by
  by_contra hnot
  exact witness_not_unitarizable (nonamenable_witness hnot) hG

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.UniverseTransport

namespace OAI

/-! Countability lets a group be represented in any universe.
Transport by group equivalences preserves the positive normalized invariant mean
and the bounded nonunitarizable witness. -/
noncomputable section
namespace Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

def meanPullback (e : G ≃* Q) : (G →ᵇ ℂ) →ₗ[ℂ] (Q →ᵇ ℂ) where
  toFun f := f.compContinuous ⟨e.symm, continuous_of_discreteTopology⟩
  map_add' f h := by ext q; rfl
  map_smul' z f := by ext q; rfl

omit [DiscreteTopology G] in
@[simp] theorem meanPullback_apply (e : G ≃* Q) (f : G →ᵇ ℂ) (q : Q) :
    meanPullback e f q = f (e.symm q) := rfl

/-- Amenability transport uses the same positive normalized invariant mean. -/
theorem amenable_of_mulEquiv (e : G ≃* Q) (hQ : Amenable Q) : Amenable G := by
  rcases hQ with ⟨m, h1, hp, hi⟩
  refine ⟨m.comp (meanPullback e), ?_, ?_, ?_⟩
  · have hc : meanPullback e (BoundedContinuousFunction.const G 1) =
        BoundedContinuousFunction.const Q 1 := by ext q; rfl
    simpa only [LinearMap.comp_apply, hc] using h1
  · intro f hf
    exact hp _ (fun q => hf (e.symm q))
  · intro g f
    have hc : meanPullback e (leftTranslate g f) = leftTranslate (e g) (meanPullback e f) := by
      ext q
      simp [meanPullback_apply, leftTranslate, map_mul, map_inv]
    simpa only [LinearMap.comp_apply, hc] using hi (e g) (meanPullback e f)

omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace Q] [DiscreteTopology Q] in
/-- Reindexing the group does not change the Hilbert space, bound or similarities. -/
theorem witness_of_mulEquiv (e : G ≃* Q) (hQ : NonamenableWitness.{v,w} Q) :
    NonamenableWitness.{u,w} G := by
  rcases hQ with ⟨H, hnorm, hinner, hcomplete, hsep, π, hb, hn⟩
  refine ⟨H, hnorm, hinner, hcomplete, hsep, π.comp e.toMonoidHom, fun g => hb (e g), ?_⟩
  rintro ⟨S, hS⟩
  apply hn
  refine ⟨S, ?_⟩
  intro q x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hS (e.symm q) x

/-- The main theorem with independent group and Hilbert-space universes. -/
theorem main_theorem_all_universes : MainTheorem.{u,v} := by
  intro G _ _ _ _ hG
  let Q := Shrink.{v} G
  let e : G ≃* Q := Shrink.mulEquiv.symm
  let : Countable Q := e.surjective.countable
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  have hQ : ¬ Amenable Q := fun h => hG (amenable_of_mulEquiv e h)
  exact witness_of_mulEquiv e (nonamenable_witness hQ)

/-- Unitarizability implies amenability, with no uniform similarity bound. -/
theorem amenable_of_unitarizable_all_universes [Countable G]
    (h : Unitarizable.{u,v} G) : Amenable G := by
  by_contra hn
  exact witness_not_unitarizable (main_theorem_all_universes G hn) h

end Dixmier

end

end OAI

-- Source: OAI.Analysis.Unitarizability.NearOne

namespace OAI

noncomputable section
namespace Dixmier
universe u
open Filter
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem nonamenable_near_one (hG : ¬ Amenable G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
      (Countable G → TopologicalSpace.SeparableSpace H) ∧
      (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π := by
  classical
  obtain ⟨S, hS, hd, ρ, hρ, hρ1, hmask⟩ := sparse_splitting_of_nonamenable hG
  let d := S.card
  let k : ℕ → ℕ := fun j => fiberDimension d ρ (j+1)
  let r : ℕ → ℕ := fun j => endpointCapacity d ρ (j+1)
  let Labels : ℕ → Type u := fun j => Word S (j+1)
  let s : ∀ j, Labels j → G := fun j => wordProduct (fun x : S => (x : G)) (j+1)
  have hlabel (j : ℕ) : Fintype.card (Labels j) = d^(j+1) := by
    simp [Labels, word_card, d]
  have hn (j : ℕ) : 2 ≤ Fintype.card (Labels j) := by
    rw [hlabel]
    have hp : 1 ≤ d^j := one_le_pow₀ (by omega : 1 ≤ d)
    rw [pow_succ']
    dsimp [d] at *
    nlinarith
  have hr (j : ℕ) : 1 ≤ r j := endpointCapacity_pos hd hρ (j+1)
  have hk (j : ℕ) : 0 < k j := fiberDimension_pos hd hρ (j+1)
  have hdim (j : ℕ) : FrameParameters.dimension (Fintype.card (Labels j)) (r j) = k j := by
    simp [FrameParameters.dimension, hlabel, k, fiberDimension, r, Nat.cast_pow]
  have hframes (j : ℕ) : ∃ v : Labels j → EuclideanSpace ℂ (Fin (k j)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (min (2*r j) (Fintype.card (Labels j))) 10 := by
    have h := SignMatrix.frames_for_fintype (hn j) (hr j)
    rw [hdim j] at h
    exact h
  choose v hvunit hvframe using hframes
  have hmasks (j : ℕ) : ∃ a : G → Labels j → Bool,
      (∀ x, (rowOnes a x).card ≤ r j) ∧ ∀ y, (columnZeros a (s j) y).card ≤ r j :=
    hmask (j+1) (by omega)
  choose a har hac using hmasks
  let A : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.constant (v j) (s j)
  let T : ∀ j, DirectSumObstruction.Stage G k j →L[ℂ] DirectSumObstruction.Stage G k j :=
    fun j => Masked.oriented (v j) (s j) (a j)
  have hA (j : ℕ) : A j ∈ KernelObstruction.Commutant := Masked.constant_commutant _ _
  have hrow (j : ℕ) : ‖KernelObstruction.row (T j) 1‖ ≤ 100 := by
    have h := Masked.local_row_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) 1
    norm_num at h
    exact h
  have hcol (j : ℕ) : ‖KernelObstruction.col (A j-T j) 1‖ ≤ 100 := by
    have h := Masked.local_column_bound (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (hac j) 1
    norm_num at h
    exact h
  have hdiff (j : ℕ) (g : G) : ‖coboundary KernelObstruction.translation (T j) g‖ ≤ 100 := by
    have h := Masked.difference_norm_le (v j) (s j) (a j) (by norm_num : (0 : ℝ) ≤ 10) (hvframe j) (har j) (hac j) g
    norm_num at h
    exact h
  have henergy (j : ℕ) : (d : ℝ)^(j+1) ≤ KernelObstruction.energy (A j) := by
    have h := Masked.constant_energy_ge_card (v j) (hvunit j) (s j)
    rw [hlabel] at h
    simpa only [Nat.cast_pow] using h
  have hratio : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop := by
    have hbase := (reciprocal_dimension_ratio_tendsto hd hρ hρ1).comp (tendsto_add_atTop_nat 1)
    apply tendsto_atTop_mono _ hbase
    intro j
    exact div_le_div_of_nonneg_right (henergy j) (Nat.cast_nonneg _)
  obtain ⟨π, hπbound, hπnot⟩ := DirectSumObstruction.scaled_direct_sum_obstruction k hk A T hA
    (by norm_num : (0 : ℝ) ≤ 100) hrow hcol hdiff hratio
    (show 0 < ε / 100 by positivity)
  refine ⟨DirectSumObstruction.Carrier G k, inferInstance, inferInstance, inferInstance,
    π, ?_, ?_, hπnot⟩
  · intro hcount
    let := hcount
    exact DirectSumObstruction.carrier_separable k
  · intro g
    simpa only [div_mul_cancel₀ ε (by norm_num : (100 : ℝ) ≠ 0)] using hπbound g

universe v

theorem nonamenable_near_one_large (hG : ¬ Amenable G) (ε : ℝ) (hε : 0 < ε) :
    ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
      (Countable G → TopologicalSpace.SeparableSpace H) ∧
      (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π := by
  let Q := ULift.{v} G
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let e : G ≃* Q := MulEquiv.ulift.symm
  have hQ : ¬ Amenable Q := fun h => hG (amenable_of_mulEquiv e h)
  obtain ⟨H, hnorm, hinner, hcomplete, π, hsep, hb, hn⟩ := nonamenable_near_one hQ ε hε
  refine ⟨H, hnorm, hinner, hcomplete, π.comp e.toMonoidHom, ?_, fun g => hb (e g), ?_⟩
  · intro hcount
    let := hcount
    exact hsep (e.surjective.countable)
  · rintro ⟨S, hS⟩
    apply hn
    refine ⟨S, ?_⟩
    intro q x
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply]
      using hS (e.symm q) x

end Dixmier
end

end OAI

-- Source: OAI.Analysis.Unitarizability.MeanBounds

namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [TopologicalSpace G]

lemma mean_const (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1) (z : ℂ) :
    m (BoundedContinuousFunction.const G z) = z := by
  have hc : BoundedContinuousFunction.const G z =
      z • BoundedContinuousFunction.const G (1 : ℂ) := by
    ext g
    simp
  rw [hc, map_smul, h1, smul_eq_mul, mul_one]

lemma mean_real_bound (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0)
    (f : G →ᵇ ℂ) (C : ℝ) (hf : ∀ x, (f x).im = 0)
    (hC : ∀ x, |(f x).re| ≤ C) : (m f).im = 0 ∧ ‖m f‖ ≤ C := by
  have hplus := hp (BoundedContinuousFunction.const G (C : ℂ) + f) (by
    intro x
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply,
      Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, hf, add_zero]
    exact ⟨by have := (abs_le.mp (hC x)).1; linarith, trivial⟩)
  have hminus := hp (BoundedContinuousFunction.const G (C : ℂ) - f) (by
    intro x
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply,
      Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, hf, sub_zero]
    exact ⟨sub_nonneg.mpr (abs_le.mp (hC x)).2, trivial⟩)
  rw [map_add, mean_const m h1] at hplus
  rw [map_sub, mean_const m h1] at hminus
  have hi : (m f).im = 0 := by simpa using hplus.2
  refine ⟨hi, ?_⟩
  have hr : |(m f).re| ≤ C := by
    apply abs_le.mpr
    constructor <;> simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at * <;>
      linarith [hplus.1, hminus.1]
  have heq : m f = ((m f).re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact hr

variable [DiscreteTopology G]

def realComponent (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun g => ((f g).re : ℂ)) ‖f‖
    (fun g => by simpa using (Complex.abs_re_le_norm (f g)).trans (f.norm_coe_le_norm g))

def imagComponent (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun g => ((f g).im : ℂ)) ‖f‖
    (fun g => by simpa using (Complex.abs_im_le_norm (f g)).trans (f.norm_coe_le_norm g))

lemma mean_norm_le (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (f : G →ᵇ ℂ) : ‖m f‖ ≤ 2 * ‖f‖ := by
  have hr : ‖m (realComponent f)‖ ≤ ‖f‖ :=
    (mean_real_bound m h1 hp _ ‖f‖ (fun _ => rfl)
      (fun g => by
        change |(f g).re| ≤ ‖f‖
        exact (Complex.abs_re_le_norm _).trans (f.norm_coe_le_norm g))).2
  have hi : ‖m (imagComponent f)‖ ≤ ‖f‖ :=
    (mean_real_bound m h1 hp _ ‖f‖ (fun _ => rfl)
      (fun g => by
        change |(f g).im| ≤ ‖f‖
        exact (Complex.abs_im_le_norm _).trans (f.norm_coe_le_norm g))).2
  have hf : f = realComponent f + Complex.I • imagComponent f := by
    ext g
    change f g = ((f g).re : ℂ) + Complex.I * ((f g).im : ℂ)
    apply Complex.ext <;> simp
  have hm := congrArg m hf
  rw [map_add, map_smul] at hm
  rw [hm]
  calc
    ‖m (realComponent f) + Complex.I • m (imagComponent f)‖ ≤
        ‖m (realComponent f)‖ + ‖Complex.I • m (imagComponent f)‖ := norm_add_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by simpa using add_le_add hr hi
    _ = 2 * ‖f‖ := by ring

end DayDixmier
end Dixmier
end

end OAI

-- Source: OAI.Analysis.Unitarizability.AveragedForm

namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

section Form
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (π : G →* (H →L[ℂ] H)) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ g, ‖π g‖ ≤ M)

def coefficient (x y : H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => inner ℂ (π g⁻¹ x) (π g⁻¹ y)) (M^2 * ‖x‖ * ‖y‖) (fun g => by
      calc
        ‖inner ℂ (π g⁻¹ x) (π g⁻¹ y)‖ ≤ ‖π g⁻¹ x‖ * ‖π g⁻¹ y‖ := norm_inner_le_norm _ _
        _ ≤ (M * ‖x‖) * (M * ‖y‖) := mul_le_mul
          ((π g⁻¹).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hπ _) (norm_nonneg _)))
          ((π g⁻¹).le_opNorm y |>.trans (mul_le_mul_of_nonneg_right (hπ _) (norm_nonneg _)))
          (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
        _ = M^2 * ‖x‖ * ‖y‖ := by ring)

@[simp] lemma coefficient_apply (x y : H) (g : G) :
    coefficient π hM hπ x y g = inner ℂ (π g⁻¹ x) (π g⁻¹ y) := rfl

lemma coefficient_norm_le (x y : H) :
    ‖coefficient π hM hπ x y‖ ≤ M^2 * ‖x‖ * ‖y‖ := by
  unfold coefficient BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

lemma coefficient_add_left (x y z : H) :
    coefficient π hM hπ (x + y) z = coefficient π hM hπ x z + coefficient π hM hπ y z := by
  ext g
  simp

lemma coefficient_add_right (x y z : H) :
    coefficient π hM hπ x (y + z) = coefficient π hM hπ x y + coefficient π hM hπ x z := by
  ext g
  simp

lemma coefficient_smul_left (c : ℂ) (x y : H) :
    coefficient π hM hπ (c • x) y = (starRingEnd ℂ c) • coefficient π hM hπ x y := by
  ext g
  simp [mul_comm]

lemma coefficient_smul_right (c : ℂ) (x y : H) :
    coefficient π hM hπ x (c • y) = c • coefficient π hM hπ x y := by
  ext g
  simp

lemma coefficient_translate (h : G) (x y : H) :
    coefficient π hM hπ (π h x) (π h y) = leftTranslate h (coefficient π hM hπ x y) := by
  ext g
  simp [leftTranslate, coefficient, map_mul, mul_apply_eq_comp]

def averagedForm (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun y := m (coefficient π hM hπ x y)
      map_add' y z := by rw [coefficient_add_right, map_add]
      map_smul' c y := by rw [coefficient_smul_right, map_smul]; rfl }
  map_add' x y := by
    ext z
    change m (coefficient π hM hπ (x + y) z) = _
    rw [coefficient_add_left, map_add]
    rfl
  map_smul' c x := by
    ext y
    change m (coefficient π hM hπ (c • x) y) = _
    rw [coefficient_smul_left, map_smul]
    rfl

lemma averagedForm_bound (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x y : H) :
    ‖averagedForm π hM hπ m x y‖ ≤ (2 * M^2) * ‖x‖ * ‖y‖ := by
  change ‖m (coefficient π hM hπ x y)‖ ≤ _
  calc
    _ ≤ 2 * ‖coefficient π hM hπ x y‖ := mean_norm_le m h1 hp _
    _ ≤ 2 * (M^2 * ‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left
      (coefficient_norm_le π hM hπ x y) (by norm_num)
    _ = _ := by ring

lemma averagedForm_nonneg (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x : H) :
    0 ≤ (m (coefficient π hM hπ x x)).re ∧ (m (coefficient π hM hπ x x)).im = 0 := by
  apply hp
  intro g
  simpa only [coefficient_apply, RCLike.re_to_complex, RCLike.im_to_complex] using
    And.intro (inner_self_nonneg (𝕜 := ℂ) (x := π g⁻¹ x)) (inner_self_im (𝕜 := ℂ) (π g⁻¹ x))

lemma averagedForm_lower (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ)
    (h1 : m (BoundedContinuousFunction.const G 1) = 1)
    (hp : ∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) (x : H) :
    ‖x‖^2 ≤ M^2 * (m (coefficient π hM hπ x x)).re := by
  have hnorm (g : G) : ‖x‖ ≤ M * ‖π g⁻¹ x‖ := by
    calc
      ‖x‖ = ‖π g (π g⁻¹ x)‖ := by simp [← mul_apply_eq_comp, ← map_mul]
      _ ≤ ‖π g‖ * ‖π g⁻¹ x‖ := (π g).le_opNorm _
      _ ≤ M * ‖π g⁻¹ x‖ := mul_le_mul_of_nonneg_right (hπ g) (norm_nonneg _)
  have hpos := hp (((M^2 : ℝ) : ℂ) • coefficient π hM hπ x x -
      BoundedContinuousFunction.const G ((‖x‖^2 : ℝ) : ℂ)) (by
    intro g
    have hre : (inner ℂ (π g⁻¹ x) (π g⁻¹ x)).re = ‖π g⁻¹ x‖^2 := by
      simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (π g⁻¹ x)
    have him : (inner ℂ (π g⁻¹ x) (π g⁻¹ x)).im = 0 := by
      simpa only [RCLike.im_to_complex] using inner_self_im (𝕜 := ℂ) (π g⁻¹ x)
    simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.const_apply, coefficient_apply, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_im, Complex.mul_im, zero_add, hre, him, mul_zero]
    constructor
    · have hsqr := (sq_le_sq₀ (norm_nonneg x)
        (mul_nonneg hM (norm_nonneg (π g⁻¹ x)))).mpr (hnorm g)
      nlinarith [hsqr]
    · simp)
  rw [map_sub, map_smul, mean_const m h1] at hpos
  simpa only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using hpos.1

end Form

end DayDixmier
end Dixmier
end

end OAI

-- Source: OAI.Analysis.Unitarizability.Amenable

namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem representation_similar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hG : Amenable G) (π : G →* (H →L[ℂ] H))
    (hb : ∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) : SimilarToUnitary π := by
  obtain ⟨m, h1, hp, hinv⟩ := hG
  obtain ⟨C, hC⟩ := hb
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hπ : ∀ g, ‖π g‖ ≤ M := fun g => (hC g).trans (le_max_left _ _)
  let B : H →L⋆[ℂ] H →L[ℂ] ℂ := (averagedForm π hM.le hπ m).mkContinuous₂
    (2 * M^2) (averagedForm_bound π hM.le hπ m h1 hp)
  let Q : H →L[ℂ] H := InnerProductSpace.continuousLinearMapOfBilin B
  have hQ (x y : H) : inner ℂ (Q x) y = m (coefficient π hM.le hπ x y) := by
    exact InnerProductSpace.continuousLinearMapOfBilin_apply B x y
  have hQpos : Q.IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    rw [hQ]
    have h := averagedForm_nonneg π hM.le hπ m hp x
    refine ⟨?_, h.1⟩
    apply Complex.ext <;> simp [h.2]
  have hQnonneg : 0 ≤ Q := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hQpos
  have hunit : IsUnit Q := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map Q
      (c := ⟨(M^2)⁻¹, inv_nonneg.mpr (sq_nonneg M)⟩)
        (by change (0 : ℝ) < (M^2)⁻¹; positivity)
    intro x
    change ‖x‖^2 * (M^2)⁻¹ ≤ _
    rw [hQ]
    calc
      ‖x‖^2 * (M^2)⁻¹ ≤ (m (coefficient π hM.le hπ x x)).re := by
        rw [← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos hM)]
        simpa only [mul_comm] using averagedForm_lower π hM.le hπ m h1 hp x
      _ ≤ ‖m (coefficient π hM.le hπ x x)‖ := Complex.re_le_norm _
  obtain ⟨s, hs⟩ := (CFC.isUnit_sqrt_iff Q hQnonneg).mpr hunit
  let S : H ≃L[ℂ] H := ContinuousLinearEquiv.ofUnit s
  have hS (x : H) : S x = CFC.sqrt Q x := by
    change (s : H →L[ℂ] H) x = _
    rw [hs]
  have hSsymmetric := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (CFC.sqrt_nonneg Q)).isSymmetric
  have hdiag (x : H) : ‖S x‖^2 = (m (coefficient π hM.le hπ x x)).re := by
    rw [hS, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have heq : inner ℂ (CFC.sqrt Q x) (CFC.sqrt Q x) = inner ℂ (Q x) x := by
      calc
        _ = inner ℂ (CFC.sqrt Q (CFC.sqrt Q x)) x := (hSsymmetric _ _).symm
        _ = inner ℂ (Q x) x := by
          congr 1
          exact congrArg (fun T : H →L[ℂ] H => T x) (CFC.sqrt_mul_sqrt_self Q hQnonneg)
    rw [heq, hQ, RCLike.re_to_complex]
  refine ⟨S, ?_⟩
  intro g x
  have hequal : ‖S (π g (S.symm x))‖^2 = ‖x‖^2 := by
    rw [hdiag, coefficient_translate, hinv, ← hdiag, S.apply_symm_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hequal

end DayDixmier

universe v
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  
theorem amenable_unitarizable (hG : Amenable G) : Unitarizable.{_, v} G := by
  intro H _ _ _ π hπ
  exact DayDixmier.representation_similar hG π hπ

end Dixmier
end

end OAI

-- Source: OAI.Analysis.Unitarizability.AllDiscrete

namespace OAI

noncomputable section
namespace Dixmier
universe u v

theorem current_main_theorem : CurrentMainTheorem.{u,v} := by
  intro G _ _ _
  constructor
  · constructor
    · intro hG
      exact amenable_unitarizable hG
    · intro hunit
      by_contra hnot
      obtain ⟨H, hnorm, hinner, hcomplete, π, _, hb, hn⟩ :=
        nonamenable_near_one_large.{u,v} hnot 1 zero_lt_one
      exact hn (@hunit H hnorm hinner hcomplete π ⟨1 + 1, hb⟩)
  · intro ε hε hG
    exact nonamenable_near_one_large.{u,v} hG ε hε

end Dixmier
end

end OAI

universe u v
theorem OMA.solution : type_of% @OMA.S_wpc_dixmier_unitarizability.main := by
  intro G _ _ _ h
  exact (OAI.Dixmier.current_main_theorem G).1.mpr h
