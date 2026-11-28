import OMAReductions.R_Erdos661_erdos_661_R1
import Mathlib

/-! Step Erdos661.erdos_661.R1.H2: hypothesis H2 of reduction Erdos661.erdos_661.R1 (planar realization of a
rank at most two Gram matrix). -/

-- Credit: @ivillar (proof written by local worker P5; checked and queued by P7)

open scoped MatrixOrder

namespace Erdos661StepH2

open Matrix

/-- Padding a vector of length at most two to the plane preserves the sum of squares. -/
theorem pad_sum (d : ℕ) (hd : d ≤ 2) (f : Fin d → ℝ) :
    (∑ a : Fin 2, (if h : (a : ℕ) < d then f ⟨a, h⟩ else 0) ^ 2) = ∑ a : Fin d, f a ^ 2 := by
  interval_cases d <;> simp [Fin.sum_univ_succ]

/-- A real positive semidefinite matrix of rank at most two is the Gram matrix of planar
vectors, so its squared-distance table is realized in the plane. -/
theorem gram {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : G.PosSemidef)
    (hr : G.rank ≤ 2) :
    ∃ x : ι → EuclideanSpace ℝ (Fin 2), ∀ i j,
      dist (x i) (x j) ^ 2 = G i i + G j j - 2 * G i j := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  let L := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  let b : ι → EuclideanSpace ℝ ι := fun i => L (B.col i)
  have hinner : ∀ i j, inner ℝ (b i) (b j) = G i j := by
    intro i j
    rw [hB]
    simp [b, L, Matrix.mul_apply, star_eq_conjTranspose, PiLp.inner_apply, Matrix.col, mul_comm]
  let W : Submodule ℝ (EuclideanSpace ℝ ι) := Submodule.span ℝ (Set.range b)
  have hW : Module.finrank ℝ W ≤ 2 := by
    have h1 : W = (Submodule.span ℝ (Set.range B.col)).map (L : (ι → ℝ) →ₗ[ℝ] _) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have h2 : Module.finrank ℝ W = B.rank := by
      rw [h1, LinearEquiv.finrank_map_eq, Matrix.rank_eq_finrank_span_cols]
    have h3 : G.rank = B.rank := by
      rw [hB, star_eq_conjTranspose, Matrix.rank_conjTranspose_mul_self]
    omega
  let e := stdOrthonormalBasis ℝ W
  have hbW : ∀ i, b i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  let f : ι → Fin (Module.finrank ℝ W) → ℝ := fun i a => inner ℝ ((e a : W) : EuclideanSpace ℝ ι) (b i)
  let x : ι → EuclideanSpace ℝ (Fin 2) := fun i =>
    WithLp.toLp 2 (fun a => if h : (a : ℕ) < Module.finrank ℝ W then f i ⟨a, h⟩ else 0)
  refine ⟨x, fun i j => ?_⟩
  have hv : b i - b j ∈ W := W.sub_mem (hbW i) (hbW j)
  have hnorm : ‖b i - b j‖ ^ 2 = G i i + G j j - 2 * G i j := by
    rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hinner, hinner, hinner]
    ring
  have hpars : ∑ a, inner ℝ ((⟨b i - b j, hv⟩ : W)) (e a) ^ 2 = ‖b i - b j‖ ^ 2 := by
    rw [e.sum_sq_inner_left]
    rfl
  rw [← hnorm, ← hpars, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  have hcoord : ∀ a : Fin 2, dist (x i a) (x j a) ^ 2 =
      (if h : (a : ℕ) < Module.finrank ℝ W then
        inner ℝ ((⟨b i - b j, hv⟩ : W)) (e ⟨a, h⟩) else 0) ^ 2 := by
    intro a
    rw [Real.dist_eq, sq_abs]
    simp only [x, f]
    split_ifs with h
    · rw [← inner_sub_right, real_inner_comm, Submodule.coe_inner]
    · simp
  simp_rw [hcoord]
  exact pad_sum _ hW (fun a => inner ℝ (⟨b i - b j, hv⟩ : W) (e a))

end Erdos661StepH2

theorem OMA.solution : OMA.R_Erdos661_erdos_661_R1.H2 := by
  intro m G hG hr
  exact Erdos661StepH2.gram G hG hr
