import OMAReductions.R_Green100_green_100_variants_operator_norm_R1
import Mathlib

/-!
Eckhardt Theorem 3.1: Nested Kazhdan projections coincide under matrix domination.

We prove `OMA.R_Green100_green_100_variants_operator_norm_R1.H3`:
if `Γ ≤ G` has Property (FH) (every Hilbert 1-cocycle is a coboundary), `t * Γ * t⁻¹ ≤ Γ`,
and a unitary representation `ρ : G →* E ≃ₗᵢ[ℂ] E` is dominated in operator norm by
asymptotically multiplicative unitary matrix models `U j : G → U(n j)`, then any vector
`v : E` fixed by `t * Γ * t⁻¹` is also fixed by `Γ`.
-/

namespace OMA.Green100KazhdanProj

open Filter Finset Matrix Green100
open scoped Topology InnerProductSpace

/- Section 1: Operator norm and spectral projections of Hermitian matrices -/

private noncomputable def opNorm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖

private lemma toEuclideanCLM_apply_ofLp {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) M v).ofLp = M.mulVec v.ofLp :=
  congrArg WithLp.ofLp (Matrix.toEuclideanCLM_toLp (𝕜 := ℂ) M v.ofLp)

private lemma toEuclideanCLM_mul_apply {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (A * B) v =
      Matrix.toEuclideanCLM (𝕜 := ℂ) A (Matrix.toEuclideanCLM (𝕜 := ℂ) B v) := by
  rw [map_mul]; rfl

private lemma toEuclideanCLM_sub_apply {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (A - B) v =
      Matrix.toEuclideanCLM (𝕜 := ℂ) A v - Matrix.toEuclideanCLM (𝕜 := ℂ) B v := by
  rw [map_sub]; rfl

private lemma toEuclideanCLM_one_apply {m : ℕ} (v : EuclideanSpace ℂ (Fin m)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) v = v := by
  rw [map_one]; rfl

private lemma opNorm_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ opNorm M :=
  norm_nonneg _

private lemma opNorm_zero {m : ℕ} : opNorm (0 : Matrix (Fin m) (Fin m) ℂ) = 0 := by
  simp [opNorm]

private lemma opNorm_neg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : opNorm (-M) = opNorm M := by
  unfold opNorm; rw [map_neg, norm_neg]

private lemma opNorm_add_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (A + B) ≤ opNorm A + opNorm B := by
  unfold opNorm; rw [map_add]; exact norm_add_le _ _

private lemma opNorm_sub_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  unfold opNorm; rw [map_sub]; exact norm_sub_le _ _

private lemma opNorm_sub_comm {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (A - B) = opNorm (B - A) := by
  rw [← opNorm_neg (B - A), neg_sub]

private lemma opNorm_smul {m : ℕ} (c : ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (c • M) = ‖c‖ * opNorm M := by
  unfold opNorm; rw [map_smul, norm_smul]

private lemma opNorm_mul_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm; rw [map_mul]; exact ContinuousLinearMap.opNorm_comp_le _ _

private lemma opNorm_sum_le {ι : Type*} {m : ℕ} (s : Finset ι)
    (f : ι → Matrix (Fin m) (Fin m) ℂ) :
    opNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, opNorm (f i) := by
  unfold opNorm; rw [map_sum]; exact norm_sum_le s _

private lemma opNorm_sub_eq_opDist {m : ℕ} (U V : Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm ((U : Matrix (Fin m) (Fin m) ℂ) - (V : Matrix (Fin m) (Fin m) ℂ)) = opDist U V := by
  simp only [opNorm, opDist, map_sub]

private lemma toEuclideanCLM_conjTranspose_adjoint {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) Mᴴ = ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (star M) = ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
  rw [map_star]; rfl

private lemma opNorm_conjTranspose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm Mᴴ = opNorm M := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (star M)‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖
  rw [map_star]
  exact ContinuousLinearMap.adjoint.norm_map _

private lemma norm_toEuclideanCLM_unitary {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v‖ = ‖v‖ := by
  have hu : (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp u.2
  have h1 : ⟪Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← toEuclideanCLM_conjTranspose_adjoint,
      ← toEuclideanCLM_mul_apply, hu, toEuclideanCLM_one_apply]
  have h2 := congrArg (RCLike.re (K := ℂ)) h1
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), inner_self_eq_norm_sq (𝕜 := ℂ)] at h2
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v),
    norm_nonneg v]

private lemma opNorm_unitary_le_one {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm (u : Matrix (Fin m) (Fin m) ℂ) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, norm_toEuclideanCLM_unitary]

private lemma opNorm_one_le_one {m : ℕ} : opNorm (1 : Matrix (Fin m) (Fin m) ℂ) ≤ 1 :=
  opNorm_unitary_le_one 1

private lemma opNorm_mul_unitary_left {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) = opNorm M := by
  have hu : (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp u.2
  have h1 : opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) ≤ opNorm M := by
    calc opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M)
        ≤ opNorm (u : Matrix (Fin m) (Fin m) ℂ) * opNorm M := opNorm_mul_le _ _
      _ ≤ 1 * opNorm M := mul_le_mul_of_nonneg_right (opNorm_unitary_le_one u) (opNorm_nonneg M)
      _ = opNorm M := one_mul _
  have h2 : opNorm M ≤ opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) := by
    have hEq : M = (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * ((u : Matrix (Fin m) (Fin m) ℂ) * M) := by
      rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
    conv_lhs => rw [hEq]
    calc opNorm ((u : Matrix (Fin m) (Fin m) ℂ)ᴴ * ((u : Matrix (Fin m) (Fin m) ℂ) * M))
        ≤ opNorm (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) :=
          opNorm_mul_le _ _
      _ = opNorm (u : Matrix (Fin m) (Fin m) ℂ) * opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) := by
          rw [opNorm_conjTranspose]
      _ ≤ 1 * opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) :=
          mul_le_mul_of_nonneg_right (opNorm_unitary_le_one u) (opNorm_nonneg _)
      _ = opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) := one_mul _
  exact le_antisymm h1 h2

private lemma opNorm_mul_unitary_conjTranspose_left {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm ((u : Matrix (Fin m) (Fin m) ℂ)ᴴ * M) = opNorm M :=
  opNorm_mul_unitary_left (star u) M

private lemma opNorm_mul_unitary_right {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ)) = opNorm M := by
  have hu : (u : Matrix (Fin m) (Fin m) ℂ) * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp u.2
  have h1 : opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ)) ≤ opNorm M := by
    calc opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ))
        ≤ opNorm M * opNorm (u : Matrix (Fin m) (Fin m) ℂ) := opNorm_mul_le _ _
      _ ≤ opNorm M * 1 := mul_le_mul_of_nonneg_left (opNorm_unitary_le_one u) (opNorm_nonneg M)
      _ = opNorm M := mul_one _
  have h2 : opNorm M ≤ opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ)) := by
    have hEq : M = (M * (u : Matrix (Fin m) (Fin m) ℂ)) * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
      rw [Matrix.mul_assoc, hu, Matrix.mul_one]
    conv_lhs => rw [hEq]
    calc opNorm ((M * (u : Matrix (Fin m) (Fin m) ℂ)) * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)
        ≤ opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ)) * opNorm (u : Matrix (Fin m) (Fin m) ℂ)ᴴ :=
          opNorm_mul_le _ _
      _ = opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ)) * opNorm (u : Matrix (Fin m) (Fin m) ℂ) := by
          rw [opNorm_conjTranspose]
      _ ≤ opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ)) * 1 :=
          mul_le_mul_of_nonneg_left (opNorm_unitary_le_one u) (opNorm_nonneg _)
      _ = opNorm (M * (u : Matrix (Fin m) (Fin m) ℂ)) := mul_one _
  exact le_antisymm h1 h2

private lemma opNorm_conj_unitary {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) = opNorm M := by
  have hu' : (u : Matrix (Fin m) (Fin m) ℂ)ᴴ = (star u : Matrix.unitaryGroup (Fin m) ℂ) := rfl
  rw [hu', opNorm_mul_unitary_right, opNorm_mul_unitary_left]

private lemma unitary_conj_pow {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    ∀ k : ℕ, ((u : Matrix (Fin m) (Fin m) ℂ) * M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) ^ k =
      (u : Matrix (Fin m) (Fin m) ℂ) * M ^ k * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ
  | 0 => by
    have hu : (u : Matrix (Fin m) (Fin m) ℂ) * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp u.2
    simp [hu]
  | k + 1 => by
    have hu : (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp u.2
    rw [pow_succ, unitary_conj_pow u M k, pow_succ]
    calc (u : Matrix (Fin m) (Fin m) ℂ) * M ^ k * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ *
          ((u : Matrix (Fin m) (Fin m) ℂ) * M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)
        = (u : Matrix (Fin m) (Fin m) ℂ) * M ^ k *
            ((u : Matrix (Fin m) (Fin m) ℂ)ᴴ * (u : Matrix (Fin m) (Fin m) ℂ)) *
            M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = (u : Matrix (Fin m) (Fin m) ℂ) * (M ^ k * M) * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
          rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private noncomputable def hermPart {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  ((2 : ℂ)⁻¹) • (M + Mᴴ)

private lemma hermPart_isHermitian {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    (hermPart M).IsHermitian := by
  unfold hermPart Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    add_comm]
  congr 1
  simp

private lemma opNorm_hermPart_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (hermPart M) ≤ opNorm M := by
  unfold hermPart
  rw [opNorm_smul]
  have h2 : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [h2]
  have hle := opNorm_add_le M Mᴴ
  rw [opNorm_conjTranspose] at hle
  linarith

private noncomputable def highProj {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i l =>
    ∑ k : Fin m, if θ ≤ hH.eigenvalues k then
      (hH.eigenvectorBasis k).ofLp i * star ((hH.eigenvectorBasis k).ofLp l)
    else 0

private lemma highProj_isHermitian {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) : (highProj hH θ).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i l
  simp only [Matrix.conjTranspose_apply, highProj, Matrix.of_apply, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [star_mul, star_star]
  · simp

private lemma highProj_apply_eigenvector {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) (k : Fin m) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (highProj hH θ) (hH.eigenvectorBasis k) =
      (if θ ≤ hH.eigenvalues k then (1 : ℂ) else 0) • hH.eigenvectorBasis k := by
  ext i
  rw [toEuclideanCLM_apply_ofLp]
  simp only [Matrix.mulVec, dotProduct, highProj, Matrix.of_apply]
  trans ∑ r : Fin m, (if θ ≤ hH.eigenvalues r then
      (hH.eigenvectorBasis r).ofLp i * ⟪hH.eigenvectorBasis r, hH.eigenvectorBasis k⟫_ℂ else 0)
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs
    · rw [PiLp.inner_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      change (hH.eigenvectorBasis r).ofLp i * star ((hH.eigenvectorBasis r).ofLp l) *
          (hH.eigenvectorBasis k).ofLp l =
        (hH.eigenvectorBasis r).ofLp i *
          ((hH.eigenvectorBasis k).ofLp l * star ((hH.eigenvectorBasis r).ofLp l))
      ring
    · simp
  · have hite : ∀ r : Fin m, ⟪hH.eigenvectorBasis r, hH.eigenvectorBasis k⟫_ℂ = if r = k then 1 else 0 :=
      fun r => orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal r k
    simp_rw [hite]
    rw [Finset.sum_eq_single k]
    · simp only [↓reduceIte, mul_one, PiLp.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    · intro r _ hrk
      simp only [hrk, ↓reduceIte, mul_zero, ite_self]
    · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma highProj_mul_self {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) : highProj hH θ * highProj hH θ = highProj hH θ := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ)).injective
  apply ContinuousLinearMap.ext
  intro v
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (highProj hH θ * highProj hH θ) v =
    Matrix.toEuclideanCLM (𝕜 := ℂ) (highProj hH θ) v
  set b := hH.eigenvectorBasis
  rw [← b.sum_repr' v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, toEuclideanCLM_mul_apply, highProj_apply_eigenvector hH θ k,
    map_smul, highProj_apply_eigenvector hH θ k, smul_smul]
  by_cases h : θ ≤ hH.eigenvalues k <;> simp [h]

private lemma hermitian_apply_eigenvector {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (k : Fin m) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) H (hH.eigenvectorBasis k) =
      (hH.eigenvalues k : ℂ) • hH.eigenvectorBasis k := by
  ext i
  rw [toEuclideanCLM_apply_ofLp, hH.mulVec_eigenvectorBasis]
  simp [Complex.real_smul]

private lemma hermitian_pow_apply_eigenvector {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) :
    ∀ (r : ℕ) (k : Fin m),
      Matrix.toEuclideanCLM (𝕜 := ℂ) (H ^ r) (hH.eigenvectorBasis k) =
        ((hH.eigenvalues k : ℂ) ^ r) • hH.eigenvectorBasis k
  | 0, k => by simp
  | r + 1, k => by
    rw [pow_succ, toEuclideanCLM_mul_apply, hermitian_apply_eigenvector hH k, map_smul,
      hermitian_pow_apply_eigenvector hH r k, smul_smul, pow_succ, mul_comm]

private lemma onb_norm_sq_sum {m : ℕ} (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (d : Fin m → ℂ) :
    ‖∑ k : Fin m, d k • b k‖ ^ 2 = ∑ k : Fin m, ‖d k‖ ^ 2 := by
  rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcoord : (b.repr (∑ j : Fin m, d j • b j)).ofLp k = d k := by
    rw [b.repr_apply_apply, inner_sum]
    rw [Finset.sum_eq_single k]
    · rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k k]
      simp
    · intro j _ hjk
      rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k j]
      simp [Ne.symm hjk]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hcoord]

private lemma opNorm_le_of_eigenvector_mul {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (A : Matrix (Fin m) (Fin m) ℂ) (c : Fin m → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ k, Matrix.toEuclideanCLM (𝕜 := ℂ) A (hH.eigenvectorBasis k) = c k • hH.eigenvectorBasis k)
    (hc : ∀ k, ‖c k‖ ≤ C) :
    opNorm A ≤ C := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v => ?_
  set b := hH.eigenvectorBasis
  have hv_exp : v = ∑ k : Fin m, ⟪b k, v⟫_ℂ • b k := (b.sum_repr' v).symm
  have hAv_exp : Matrix.toEuclideanCLM (𝕜 := ℂ) A v =
      ∑ k : Fin m, (⟪b k, v⟫_ℂ * c k) • b k := by
    conv_lhs => rw [hv_exp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hA k, smul_smul]
  have hnorm_sq : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖ ^ 2 =
      ∑ k : Fin m, ‖⟪b k, v⟫_ℂ * c k‖ ^ 2 := by
    rw [hAv_exp, onb_norm_sq_sum b]
  have hv_norm_sq : ‖v‖ ^ 2 = ∑ k : Fin m, ‖⟪b k, v⟫_ℂ‖ ^ 2 := by
    conv_lhs => rw [hv_exp]
    exact onb_norm_sq_sum b _
  have hle_sq : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖ ^ 2 ≤ (C * ‖v‖) ^ 2 := by
    rw [hnorm_sq, mul_pow, hv_norm_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, mul_pow, mul_comm (C ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hc k) 2) (sq_nonneg _)
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) A v), mul_nonneg hC (norm_nonneg v)]

private lemma opNorm_highProj_le_one {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) : opNorm (highProj hH θ) ≤ 1 := by
  refine opNorm_le_of_eigenvector_mul hH (highProj hH θ)
    (fun k => if θ ≤ hH.eigenvalues k then 1 else 0) zero_le_one
    (highProj_apply_eigenvector hH θ) fun k => ?_
  by_cases h : θ ≤ hH.eigenvalues k <;> simp [h]

private lemma opNorm_one_sub_highProj_le_one {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) : opNorm (1 - highProj hH θ) ≤ 1 := by
  refine opNorm_le_of_eigenvector_mul hH (1 - highProj hH θ)
    (fun k => if θ ≤ hH.eigenvalues k then 0 else 1) zero_le_one (fun k => ?_) fun k => ?_
  · rw [toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply, highProj_apply_eigenvector hH θ k]
    by_cases h : θ ≤ hH.eigenvalues k <;> simp [h]
  · by_cases h : θ ≤ hH.eigenvalues k <;> simp [h]

private lemma opNorm_sub_one_mul_highProj_le {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ k, θ ≤ hH.eigenvalues k → |hH.eigenvalues k - 1| ≤ ε) :
    opNorm ((H - 1) * highProj hH θ) ≤ ε := by
  refine opNorm_le_of_eigenvector_mul hH ((H - 1) * highProj hH θ)
    (fun k => if θ ≤ hH.eigenvalues k then ((hH.eigenvalues k - 1 : ℝ) : ℂ) else 0) hε
    (fun k => ?_) fun k => ?_
  · rw [toEuclideanCLM_mul_apply, highProj_apply_eigenvector hH θ k, map_smul,
      toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply, hermitian_apply_eigenvector hH k]
    by_cases h : θ ≤ hH.eigenvalues k
    · simp only [h, ↓reduceIte, one_smul]
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    · simp only [h, ↓reduceIte, zero_smul]
  · by_cases h : θ ≤ hH.eigenvalues k
    · simp only [h, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
      exact hb k h
    · simp only [h, ↓reduceIte, norm_zero]
      exact hε

private lemma opNorm_pow_sub_highProj_le {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) (r : ℕ) (a ε : ℝ) (ha : 0 ≤ a) (hε1 : ε ≤ 1)
    (hb : ∀ k, (0 ≤ hH.eigenvalues k ∧ hH.eigenvalues k ≤ a ∧ hH.eigenvalues k < θ) ∨
      (θ ≤ hH.eigenvalues k ∧ 1 - ε ≤ hH.eigenvalues k ∧ hH.eigenvalues k ≤ 1)) :
    opNorm (H ^ r - highProj hH θ) ≤ max (a ^ r) (1 - (1 - ε) ^ r) := by
  have hC : 0 ≤ max (a ^ r) (1 - (1 - ε) ^ r) :=
    le_trans (pow_nonneg ha r) (le_max_left _ _)
  refine opNorm_le_of_eigenvector_mul hH (H ^ r - highProj hH θ)
    (fun k => ((hH.eigenvalues k : ℂ) ^ r) - (if θ ≤ hH.eigenvalues k then 1 else 0)) hC
    (fun k => ?_) fun k => ?_
  · rw [toEuclideanCLM_sub_apply, hermitian_pow_apply_eigenvector hH r k,
      highProj_apply_eigenvector hH θ k, sub_smul]
  · rcases hb k with ⟨h0, hle_a, hlt_θ⟩ | ⟨hge_θ, hge_e, hle_1⟩
    · have hnot : ¬ (θ ≤ hH.eigenvalues k) := not_le.mpr hlt_θ
      simp only [hnot, ↓reduceIte, sub_zero, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg h0]
      exact (pow_le_pow_left₀ h0 hle_a r).trans (le_max_left _ _)
    · simp only [hge_θ, ↓reduceIte]
      have hcast : ((hH.eigenvalues k : ℂ) ^ r - 1) = (((hH.eigenvalues k ^ r - 1 : ℝ) : ℂ)) := by
        push_cast; rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      have hpow_le : hH.eigenvalues k ^ r ≤ 1 :=
        pow_le_one₀ (by linarith) hle_1
      have hpow_ge : (1 - ε) ^ r ≤ hH.eigenvalues k ^ r :=
        pow_le_pow_left₀ (by linarith) hge_e r
      rw [abs_of_nonpos (by linarith)]
      exact (by linarith : -(hH.eigenvalues k ^ r - 1) ≤ 1 - (1 - ε) ^ r).trans (le_max_right _ _)

private lemma norm_one_sub_highProj_le_norm_one_sub_H {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) (hθ : θ < 1) (v : EuclideanSpace ℂ (Fin m)) :
    (1 - θ) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - highProj hH θ) v‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - H) v‖ := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ
  set b := hH.eigenvectorBasis
  have hv_exp : v = ∑ k : Fin m, ⟪b k, v⟫_ℂ • b k := (b.sum_repr' v).symm
  have hP_exp : Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - highProj hH θ) v =
      ∑ k : Fin m, (⟪b k, v⟫_ℂ * (if θ ≤ hH.eigenvalues k then (0 : ℂ) else 1)) • b k := by
    conv_lhs => rw [hv_exp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply,
      highProj_apply_eigenvector hH θ k]
    by_cases h : θ ≤ hH.eigenvalues k <;> simp [b, h]
  have hH_exp : Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - H) v =
      ∑ k : Fin m, (⟪b k, v⟫_ℂ * ((1 - hH.eigenvalues k : ℝ) : ℂ)) • b k := by
    conv_lhs => rw [hv_exp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply,
      hermitian_apply_eigenvector hH k, Complex.ofReal_sub, Complex.ofReal_one,
      mul_sub, mul_one, sub_smul, smul_sub, smul_smul]
  have hnormP : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - highProj hH θ) v‖ ^ 2 =
      ∑ k : Fin m, ‖⟪b k, v⟫_ℂ * (if θ ≤ hH.eigenvalues k then (0 : ℂ) else 1)‖ ^ 2 := by
    rw [hP_exp, onb_norm_sq_sum b]
  have hnormH : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - H) v‖ ^ 2 =
      ∑ k : Fin m, ‖⟪b k, v⟫_ℂ * ((1 - hH.eigenvalues k : ℝ) : ℂ)‖ ^ 2 := by
    rw [hH_exp, onb_norm_sq_sum b]
  have hsq : ((1 - θ) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - highProj hH θ) v‖) ^ 2 ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - H) v‖ ^ 2 := by
    rw [mul_pow, hnormP, hnormH, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases h : θ ≤ hH.eigenvalues k
    · simp only [h, ↓reduceIte, mul_zero, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact sq_nonneg _
    · simp only [h, ↓reduceIte, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
      have hlt : hH.eigenvalues k < θ := not_le.mp h
      have habs : 1 - θ ≤ |1 - hH.eigenvalues k| := by
        rw [abs_of_pos (by linarith)]
        linarith
      rw [mul_comm ((1 - θ) ^ 2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1θ.le habs 2) (sq_nonneg _)
  nlinarith [mul_nonneg h1θ.le (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - highProj hH θ) v)),
    norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - H) v)]

private lemma opNorm_one_sub_highProj_mul_le {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (θ : ℝ) (hθ : θ < 1) (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm ((1 - highProj hH θ) * M) ≤ (1 - θ)⁻¹ * opNorm ((1 - H) * M) := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ
  have hbound : 0 ≤ (1 - θ)⁻¹ * opNorm ((1 - H) * M) :=
    mul_nonneg (inv_nonneg.mpr h1θ.le) (opNorm_nonneg _)
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hbound fun u => ?_
  rw [toEuclideanCLM_mul_apply]
  have h1 := norm_one_sub_highProj_le_norm_one_sub_H hH θ hθ (Matrix.toEuclideanCLM (𝕜 := ℂ) M u)
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - H) * M) u‖ ≤ opNorm ((1 - H) * M) * ‖u‖ :=
    ContinuousLinearMap.le_opNorm _ u
  rw [toEuclideanCLM_mul_apply] at h2
  have h3 : (1 - θ) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - highProj hH θ)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) M u)‖ ≤
      opNorm ((1 - H) * M) * ‖u‖ := h1.trans h2
  have h4 := mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr h1θ.le)
  rw [← mul_assoc, inv_mul_cancel₀ h1θ.ne', one_mul, ← mul_assoc] at h4
  exact h4

private lemma eigenvalue_mem_Icc_of_hermPart {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : opNorm A ≤ 1) (k : Fin m) :
    0 ≤ (hermPart_isHermitian ((2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) + (2 : ℂ)⁻¹ • A)).eigenvalues k ∧
    (hermPart_isHermitian ((2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) + (2 : ℂ)⁻¹ • A)).eigenvalues k ≤ 1 := by
  set H := hermPart ((2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) + (2 : ℂ)⁻¹ • A)
  set hH := hermPart_isHermitian ((2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) + (2 : ℂ)⁻¹ • A)
  have hH_eq : H = (2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) + (2 : ℂ)⁻¹ • hermPart A := by
    simp only [H, hermPart, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one]
    have h2s : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
    rw [h2s]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  set v := hH.eigenvectorBasis k
  have hv_norm : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.1 k
  have hvv : ⟪v, v⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hv_norm]; simp
  have heig : (hH.eigenvalues k : ℂ) = ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ) H v⟫_ℂ := by
    rw [hermitian_apply_eigenvector hH k, inner_smul_right, hvv, mul_one]
  have hH_v : Matrix.toEuclideanCLM (𝕜 := ℂ) H v =
      (2 : ℂ)⁻¹ • v + (2 : ℂ)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v := by
    rw [hH_eq, map_add, map_smul, map_smul, map_one]; rfl
  have hre : hH.eigenvalues k = (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ *
      RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v⟫_ℂ := by
    have h1 := congrArg (RCLike.re (K := ℂ)) heig
    rw [hH_v, inner_add_right, inner_smul_right, inner_smul_right, hvv, mul_one,
      RCLike.re_eq_complex_re, Complex.ofReal_re] at h1
    have hre_rhs : RCLike.re ((2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ * ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v⟫_ℂ) =
        (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ * RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v⟫_ℂ := by
      rw [RCLike.re_eq_complex_re, Complex.add_re,
        show (2 : ℂ)⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by norm_num,
        Complex.ofReal_re, Complex.re_ofReal_mul, ← RCLike.re_eq_complex_re]
    rw [← RCLike.re_eq_complex_re, hre_rhs] at h1
    exact h1
  have habs : |RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v⟫_ℂ| ≤ 1 := by
    calc |RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v⟫_ℂ|
        ≤ ‖⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart A) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (opNorm (hermPart A) * ‖v‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = opNorm (hermPart A) := by rw [hv_norm]; ring
      _ ≤ opNorm A := opNorm_hermPart_le A
      _ ≤ 1 := hA
  have hbounds := abs_le.mp habs
  constructor <;> linarith

private noncomputable def unitaryLinEquiv {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    EuclideanSpace ℂ (Fin m) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  LinearEquiv.ofLinearMap
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)).toLinearMap
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ).toLinearMap
    (by
      ext v i
      have hu : (u : Matrix (Fin m) (Fin m) ℂ) * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 :=
        Matrix.mem_unitaryGroup_iff.mp u.2
      change (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ v)).ofLp i = v.ofLp i
      rw [← toEuclideanCLM_mul_apply, hu, toEuclideanCLM_one_apply])
    (by
      ext v i
      have hu : (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp u.2
      change (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v)).ofLp i = v.ofLp i
      rw [← toEuclideanCLM_mul_apply, hu, toEuclideanCLM_one_apply])

private lemma range_conj_finrank_eq {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix.unitaryGroup (Fin m) ℂ) :
    Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℂ) P).toLinearMap) =
      Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)).toLinearMap) := by
  set Q : Matrix (Fin m) (Fin m) ℂ := (u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ
  have hVQ_eq : LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℂ) Q).toLinearMap =
      Submodule.map (unitaryLinEquiv u).toLinearMap
        (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℂ) P).toLinearMap) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) P
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ z),
        ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ z, rfl⟩, ?_⟩
      change Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) P
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ z)) =
        Matrix.toEuclideanCLM (𝕜 := ℂ) Q z
      rw [← toEuclideanCLM_mul_apply, ← toEuclideanCLM_mul_apply]
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      refine ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) z, ?_⟩
      have hu : (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp u.2
      change Matrix.toEuclideanCLM (𝕜 := ℂ) Q (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) z) =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (Matrix.toEuclideanCLM (𝕜 := ℂ) P z)
      rw [← toEuclideanCLM_mul_apply, ← toEuclideanCLM_mul_apply]
      have hmat : Q * (u : Matrix (Fin m) (Fin m) ℂ) = (u : Matrix (Fin m) (Fin m) ℂ) * P := by
        simp only [Q, Matrix.mul_assoc, hu, Matrix.mul_one]
      rw [hmat]
  rw [hVQ_eq, LinearEquiv.finrank_map_eq]

private lemma opNorm_one_sub_proj_mul_conj_le {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ)
    (hPp : P * P = P) (hP1 : opNorm P ≤ 1) (h1P : opNorm (1 - P) ≤ 1)
    (u : Matrix.unitaryGroup (Fin m) ℂ)
    (hlt : opNorm ((1 - (u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) * P) < 1) :
    let Q := (u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ
    opNorm ((1 - P) * Q) ≤ opNorm ((1 - Q) * P) / (1 - opNorm ((1 - Q) * P)) := by
  set Q : Matrix (Fin m) (Fin m) ℂ := (u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ
  set ε : ℝ := opNorm ((1 - Q) * P)
  have hε0 : 0 ≤ ε := opNorm_nonneg _
  have h1ε : 0 < 1 - ε := sub_pos.mpr hlt
  have hQ1 : opNorm Q ≤ 1 := by
    rw [show opNorm Q = opNorm P from opNorm_conj_unitary u P]
    exact hP1
  set VP : Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℂ) P).toLinearMap
  set VQ : Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℂ) Q).toLinearMap
  have hmemP : ∀ x ∈ VP, Matrix.toEuclideanCLM (𝕜 := ℂ) P x = x := by
    rintro x ⟨y, rfl⟩
    change Matrix.toEuclideanCLM (𝕜 := ℂ) P (Matrix.toEuclideanCLM (𝕜 := ℂ) P y) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) P y
    rw [← toEuclideanCLM_mul_apply, hPp]
  have hfinrank : Module.finrank ℂ VP = Module.finrank ℂ VQ := range_conj_finrank_eq P u
  let T : VP →ₗ[ℂ] VQ :=
    { toFun := fun x => ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) Q x.1, ⟨x.1, rfl⟩⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun c x => by ext; simp }
  have hT_lb : ∀ x : VP, (1 - ε) * ‖x.1‖ ≤ ‖(T x).1‖ := by
    intro x
    have hPx : Matrix.toEuclideanCLM (𝕜 := ℂ) P x.1 = x.1 := hmemP x.1 x.2
    have hdiff : x.1 - Matrix.toEuclideanCLM (𝕜 := ℂ) Q x.1 =
        Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - Q) * P) x.1 := by
      rw [toEuclideanCLM_mul_apply (1 - Q) P, hPx, toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply]
    have hle1 : ‖x.1 - Matrix.toEuclideanCLM (𝕜 := ℂ) Q x.1‖ ≤ ε * ‖x.1‖ := by
      rw [hdiff]
      exact ContinuousLinearMap.le_opNorm _ _
    have hle2 : ‖x.1‖ - ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q x.1‖ ≤
        ‖x.1 - Matrix.toEuclideanCLM (𝕜 := ℂ) Q x.1‖ := norm_sub_norm_le _ _
    change (1 - ε) * ‖x.1‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q x.1‖
    linarith
  have hT_inj : Function.Injective T := by
    intro x₁ x₂ hEq
    have hzero : T (x₁ - x₂) = 0 := by rw [map_sub, hEq, sub_self]
    have hlb := hT_lb (x₁ - x₂)
    rw [hzero] at hlb
    have hnorm0 : ‖(x₁ - x₂).1‖ = 0 := by
      have : (1 - ε) * ‖(x₁ - x₂).1‖ ≤ 0 := by simpa using hlb
      nlinarith [norm_nonneg (x₁ - x₂).1]
    exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hnorm0))
  have hT_surj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hT_inj
  dsimp only
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - P) * Q) :
      EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))‖ ≤ ε / (1 - ε)
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hε0 h1ε.le) fun z => ?_
  let y : VQ := ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) Q z, ⟨z, rfl⟩⟩
  obtain ⟨x, hx⟩ := hT_surj y
  have hQx : Matrix.toEuclideanCLM (𝕜 := ℂ) Q x.1 = Matrix.toEuclideanCLM (𝕜 := ℂ) Q z :=
    congrArg Subtype.val hx
  have hx_le : (1 - ε) * ‖x.1‖ ≤ ‖z‖ := by
    calc (1 - ε) * ‖x.1‖ ≤ ‖(T x).1‖ := hT_lb x
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Q z‖ := by rw [hx]
      _ ≤ opNorm Q * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hQ1 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  have hPx : Matrix.toEuclideanCLM (𝕜 := ℂ) P x.1 = x.1 := hmemP x.1 x.2
  have h1Px : Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - P) x.1 = 0 := by
    rw [toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply, hPx, sub_self]
  have hrewrite : Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - P) * Q) z =
      -(Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - P) (Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - Q) * P) x.1)) := by
    rw [toEuclideanCLM_mul_apply (1 - P) Q, ← hQx, toEuclideanCLM_mul_apply (1 - Q) P, hPx,
      toEuclideanCLM_sub_apply 1 Q, toEuclideanCLM_one_apply,
      map_sub (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - P)), h1Px, zero_sub, neg_neg]
  have hbd : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - P) * Q) z‖ ≤ ε * ‖x.1‖ := by
    rw [hrewrite, norm_neg]
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - P) (Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - Q) * P) x.1)‖
        ≤ opNorm (1 - P) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - Q) * P) x.1‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (ε * ‖x.1‖) :=
          mul_le_mul h1P (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
      _ = ε * ‖x.1‖ := one_mul _
  have hmul : (1 - ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - P) * Q) z‖ ≤ ε * ‖z‖ := by
    calc (1 - ε) * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((1 - P) * Q) z‖
        ≤ (1 - ε) * (ε * ‖x.1‖) := mul_le_mul_of_nonneg_left hbd h1ε.le
      _ = ε * ((1 - ε) * ‖x.1‖) := by ring
      _ ≤ ε * ‖z‖ := mul_le_mul_of_nonneg_left hx_le hε0
  rw [div_mul_eq_mul_div, le_div_iff₀ h1ε, mul_comm]
  exact hmul

private lemma opNorm_proj_sub_conj_le {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ)
    (hPh : P.IsHermitian) (hPp : P * P = P) (hP1 : opNorm P ≤ 1) (h1P : opNorm (1 - P) ≤ 1)
    (u : Matrix.unitaryGroup (Fin m) ℂ)
    (hlt : opNorm ((1 - (u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) * P) < 1) :
    let Q := (u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ
    opNorm (P - Q) ≤ opNorm ((1 - Q) * P) + opNorm ((1 - Q) * P) / (1 - opNorm ((1 - Q) * P)) := by
  set Q : Matrix (Fin m) (Fin m) ℂ := (u : Matrix (Fin m) (Fin m) ℂ) * P * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ
  have hQh : Q.IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [Q, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hPh.eq]
  have h1PQ : opNorm ((1 - P) * Q) ≤ opNorm ((1 - Q) * P) / (1 - opNorm ((1 - Q) * P)) :=
    opNorm_one_sub_proj_mul_conj_le P hPp hP1 h1P u hlt
  have hQ1P : opNorm (Q * (1 - P)) ≤ opNorm ((1 - Q) * P) / (1 - opNorm ((1 - Q) * P)) := by
    have hadj : ((1 - P) * Q)ᴴ = Q * (1 - P) := by
      rw [Matrix.conjTranspose_mul, hQh.eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh.eq]
    rw [← hadj, opNorm_conjTranspose]
    exact h1PQ
  have hsplit : P - Q = (1 - Q) * P - Q * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  dsimp only
  rw [hsplit]
  have htri := opNorm_sub_le ((1 - Q) * P) (Q * (1 - P))
  linarith

/- Section 2: Guichardet theorem (Property (FH) implies Kazhdan pair and spectral gap) -/

private def fixedSubspace {Γ E : Type} [Group Γ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ρ : Γ →* E ≃ₗᵢ[ℂ] E) : Submodule ℂ E where
  carrier := {w | ∀ g : Γ, ρ g w = w}
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  zero_mem' g := map_zero _
  smul_mem' c x hx g := by rw [map_smul, hx g]

private lemma isClosed_fixedSubspace {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : Γ →* E ≃ₗᵢ[ℂ] E) :
    IsClosed (fixedSubspace ρ : Set E) := by
  have heq : (fixedSubspace ρ : Set E) = ⋂ g : Γ, {w : E | ρ g w = w} := by
    ext w; simp [fixedSubspace]
  rw [heq]
  exact isClosed_iInter fun g => isClosed_eq (ρ g).continuous continuous_id

private lemma completeSpace_fixedSubspace {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : Γ →* E ≃ₗᵢ[ℂ] E) :
    CompleteSpace ↥(fixedSubspace ρ) :=
  (isClosed_fixedSubspace ρ).completeSpace_coe

private lemma completeSpace_fixedSubspace_orth {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : Γ →* E ≃ₗᵢ[ℂ] E) :
    CompleteSpace ↥(fixedSubspace ρ)ᗮ :=
  (Submodule.isClosed_orthogonal (fixedSubspace ρ)).completeSpace_coe

private lemma mem_orth_fixedSubspace_map {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : Γ →* E ≃ₗᵢ[ℂ] E) (g : Γ) {w : E}
    (hw : w ∈ (fixedSubspace ρ)ᗮ) : ρ g w ∈ (fixedSubspace ρ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro u hu
  have hgu : ρ g⁻¹ u = u := hu g⁻¹
  have h1 : ρ g (ρ g⁻¹ u) = u := by
    change (ρ g * ρ g⁻¹) u = u
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  calc ⟪u, ρ g w⟫_ℂ = ⟪ρ g (ρ g⁻¹ u), ρ g w⟫_ℂ := by rw [h1]
    _ = ⟪ρ g⁻¹ u, w⟫_ℂ := (ρ g).inner_map_map _ _
    _ = ⟪u, w⟫_ℂ := by rw [hgu]
    _ = 0 := hw u hu

private noncomputable def orthRep {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : Γ →* E ≃ₗᵢ[ℂ] E) :
    Γ →* ↥(fixedSubspace ρ)ᗮ ≃ₗᵢ[ℂ] ↥(fixedSubspace ρ)ᗮ where
  toFun g :=
    { toFun := fun w => ⟨ρ g w.1, mem_orth_fixedSubspace_map ρ g w.2⟩
      invFun := fun w => ⟨ρ g⁻¹ w.1, mem_orth_fixedSubspace_map ρ g⁻¹ w.2⟩
      map_add' := fun x y => by ext; exact map_add (ρ g) x.1 y.1
      map_smul' := fun c x => by ext; exact map_smul (ρ g) c x.1
      left_inv := fun w => by
        ext; change (ρ g⁻¹ * ρ g) w.1 = w.1
        rw [← map_mul, inv_mul_cancel, map_one]; rfl
      right_inv := fun w => by
        ext; change (ρ g * ρ g⁻¹) w.1 = w.1
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      norm_map' := fun w => (ρ g).norm_map w.1 }
  map_one' := by ext w; change ρ 1 w.1 = w.1; rw [map_one]; rfl
  map_mul' g h := by ext w; change ρ (g * h) w.1 = ρ g (ρ h w.1); rw [map_mul]; rfl

private lemma orthRep_no_fixed {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : Γ →* E ≃ₗᵢ[ℂ] E) (w : ↥(fixedSubspace ρ)ᗮ)
    (hw : ∀ g : Γ, orthRep ρ g w = w) : w = 0 := by
  have hmem : w.1 ∈ fixedSubspace ρ := fun g => congrArg Subtype.val (hw g)
  have h0 : ⟪w.1, w.1⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp w.2 w.1 hmem
  exact Subtype.ext (inner_self_eq_zero.mp h0)

private lemma exists_kazhdan_pair_of_FH {Γ : Type} [Group Γ] [Countable Γ]
    (hFH : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Γ →* H ≃ₗᵢ[ℂ] H) (c : Γ → H), (∀ g h, c (g * h) = c g + σ g (c h)) →
      ∃ w : H, ∀ g, c g = σ g w - w) :
    ∃ (F : Finset Γ) (κ : ℝ), 1 ∈ F ∧ (∀ g ∈ F, g⁻¹ ∈ F) ∧ 0 < κ ∧ κ ≤ 1 ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (σ : Γ →* H ≃ₗᵢ[ℂ] H),
        (∀ w : H, (∀ g : Γ, σ g w = w) → w = 0) →
        ∀ w : H, κ ^ 2 * ‖w‖ ^ 2 ≤ ∑ g ∈ F, ‖σ g w - w‖ ^ 2 := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  let F : ℕ → Finset Γ := fun k =>
    insert 1 (((Finset.range k).image e) ∪ ((Finset.range k).image fun i => (e i)⁻¹))
  have hF1 : ∀ k, (1 : Γ) ∈ F k := fun k => Finset.mem_insert_self _ _
  have hFsym : ∀ k, ∀ g ∈ F k, g⁻¹ ∈ F k := by
    intro k g hg
    simp only [F, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hg ⊢
    rcases hg with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · left; simp
    · right; right; exact ⟨i, hi, rfl⟩
    · right; left; exact ⟨i, hi, (inv_inv (e i)).symm⟩
  have hFexh : ∀ g : Γ, ∃ k₀ : ℕ, ∀ k ≥ k₀, g ∈ F k := by
    intro g
    obtain ⟨i, rfl⟩ := he g
    refine ⟨i + 1, fun k hk => ?_⟩
    simp only [F, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    right; left; exact ⟨i, by omega, rfl⟩
  have hex_k : ∃ k : ℕ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Γ →* H ≃ₗᵢ[ℂ] H),
      (∀ w : H, (∀ g : Γ, σ g w = w) → w = 0) →
      ∀ u : H, ‖u‖ = 1 → ∃ g ∈ F k, (1 / 4 : ℝ) ^ k < ‖σ g u - u‖ := by
    by_contra hno
    push Not at hno
    choose H instN instI instC σ hfix u hu hsmall using hno
    let : ∀ k, NormedAddCommGroup (H k) := instN
    let : ∀ k, InnerProductSpace ℂ (H k) := instI
    let : ∀ k, CompleteSpace (H k) := instC
    let L : Type := lp H 2
    have hp2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have h2r : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
    have hmem_act : ∀ (g : Γ) (f : L), Memℓp (fun k => σ k g (f k)) 2 := by
      intro g f
      rw [memℓp_gen_iff hp2]
      have hf := (memℓp_gen_iff hp2).mp f.2
      simpa only [(σ _ g).norm_map] using hf
    let σSum : Γ →* L ≃ₗᵢ[ℂ] L :=
      { toFun := fun g =>
          { toFun := fun f => ⟨fun k => σ k g (f k), hmem_act g f⟩
            invFun := fun f => ⟨fun k => σ k g⁻¹ (f k), hmem_act g⁻¹ f⟩
            map_add' := fun f₁ f₂ => by
              apply lp.ext; funext k
              exact map_add (σ k g) (f₁ k) (f₂ k)
            map_smul' := fun a f => by
              apply lp.ext; funext k
              exact map_smul (σ k g) a (f k)
            left_inv := fun f => by
              apply lp.ext; funext k
              change (σ k g⁻¹ * σ k g) (f k) = f k
              rw [← map_mul, inv_mul_cancel, map_one]; rfl
            right_inv := fun f => by
              apply lp.ext; funext k
              change (σ k g * σ k g⁻¹) (f k) = f k
              rw [← map_mul, mul_inv_cancel, map_one]; rfl
            norm_map' := fun f => by
              rw [lp.norm_eq_tsum_rpow hp2, lp.norm_eq_tsum_rpow hp2]
              congr 1; refine tsum_congr fun k => ?_
              change ‖σ k g (f k)‖ ^ (2 : ENNReal).toReal = ‖f k‖ ^ (2 : ENNReal).toReal
              rw [(σ k g).norm_map] }
        map_one' := by
          ext f k
          change σ k 1 (f k) = f k
          rw [map_one]; rfl
        map_mul' := fun g h => by
          ext f k
          change σ k (g * h) (f k) = σ k g (σ k h (f k))
          rw [map_mul]; rfl }
    have hmem_c : ∀ g : Γ, Memℓp (fun k => ((2 : ℂ) ^ k) • (σ k g (u k) - u k)) 2 := by
      intro g
      rw [memℓp_gen_iff hp2, h2r]
      obtain ⟨k₀, hk₀⟩ := hFexh g
      rw [← summable_nat_add_iff k₀]
      have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + k₀)) :=
        (summable_nat_add_iff k₀).mpr summable_geometric_two
      refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (norm_nonneg _) 2) (fun k => ?_) hgeom
      have hgk : g ∈ F (k + k₀) := hk₀ (k + k₀) (Nat.le_add_left k₀ k)
      have hbd1 : ‖((2 : ℂ) ^ (k + k₀)) • (σ (k + k₀) g (u (k + k₀)) - u (k + k₀))‖ ≤
          (1 / 2 : ℝ) ^ (k + k₀) := by
        rw [norm_smul, norm_pow]
        have h2n : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
        rw [h2n]
        calc (2 : ℝ) ^ (k + k₀) * ‖σ (k + k₀) g (u (k + k₀)) - u (k + k₀)‖
            ≤ (2 : ℝ) ^ (k + k₀) * (1 / 4 : ℝ) ^ (k + k₀) :=
              mul_le_mul_of_nonneg_left (hsmall (k + k₀) g hgk) (by positivity)
          _ = (2 * (1 / 4 : ℝ)) ^ (k + k₀) := (mul_pow 2 (1 / 4) (k + k₀)).symm
          _ = (1 / 2 : ℝ) ^ (k + k₀) := by norm_num
      rw [Real.rpow_two]
      have hsq : ‖((2 : ℂ) ^ (k + k₀)) • (σ (k + k₀) g (u (k + k₀)) - u (k + k₀))‖ ^ 2 ≤
          ((1 / 2 : ℝ) ^ (k + k₀)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbd1 2
      have hle_self : ((1 / 2 : ℝ) ^ (k + k₀)) ^ 2 ≤ (1 / 2 : ℝ) ^ (k + k₀) := by
        have h0 : 0 ≤ (1 / 2 : ℝ) ^ (k + k₀) := by positivity
        have h1 : (1 / 2 : ℝ) ^ (k + k₀) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      exact hsq.trans hle_self
    let c : Γ → L := fun g => ⟨fun k => ((2 : ℂ) ^ k) • (σ k g (u k) - u k), hmem_c g⟩
    have hcoc : ∀ g h : Γ, c (g * h) = c g + σSum g (c h) := by
      intro g h
      apply lp.ext; funext k
      change ((2 : ℂ) ^ k) • (σ k (g * h) (u k) - u k) =
        ((2 : ℂ) ^ k) • (σ k g (u k) - u k) +
          σ k g (((2 : ℂ) ^ k) • (σ k h (u k) - u k))
      rw [map_smul, map_sub, map_mul]
      change ((2 : ℂ) ^ k) • (σ k g (σ k h (u k)) - u k) =
        ((2 : ℂ) ^ k) • (σ k g (u k) - u k) +
          ((2 : ℂ) ^ k) • (σ k g (σ k h (u k)) - σ k g (u k))
      rw [← smul_add]
      congr 1
      abel
    obtain ⟨w, hw⟩ := hFH L σSum c hcoc
    have hwk : ∀ k : ℕ, w k = ((2 : ℂ) ^ k) • u k := by
      intro k
      have hinv : ∀ g : Γ, σ k g (((2 : ℂ) ^ k) • u k - w k) = ((2 : ℂ) ^ k) • u k - w k := by
        intro g
        have hwg := congrFun (congrArg (fun f : L => (f : ∀ j, H j)) (hw g)) k
        change ((2 : ℂ) ^ k) • (σ k g (u k) - u k) = σ k g (w k) - w k at hwg
        rw [map_sub, map_smul]
        rw [smul_sub] at hwg
        have hstep : σ k g (((2 : ℂ) ^ k) • u k) - ((2 : ℂ) ^ k) • u k = σ k g (w k) - w k := by
          rw [map_smul]; exact hwg
        exact sub_eq_sub_iff_sub_eq_sub.mp (by rw [← map_smul]; exact hstep)
      have h0 := hfix k (((2 : ℂ) ^ k) • u k - w k) hinv
      exact (sub_eq_zero.mp h0).symm
    obtain ⟨k, hk⟩ := exists_nat_gt ‖w‖
    have hle : (2 : ℝ) ^ k ≤ ‖w‖ := by
      have h1 := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) w k
      rw [hwk k, norm_smul, norm_pow, hu k, mul_one] at h1
      have h2n : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rwa [h2n] at h1
    have hlt : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
    linarith
  obtain ⟨k, hk⟩ := hex_k
  refine ⟨F k, (1 / 4 : ℝ) ^ k, hF1 k, hFsym k, by positivity,
    pow_le_one₀ (by norm_num) (by norm_num), ?_⟩
  intro H _ _ _ σ hfix w
  by_cases hw : w = 0
  · subst hw; simp
  · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let u : H := ((‖w‖⁻¹ : ℝ) : ℂ) • w
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hwn.le)]
      exact inv_mul_cancel₀ hwn.ne'
    obtain ⟨g, hgF, hgt⟩ := hk H σ hfix u hu
    have hscale : ‖σ g u - u‖ = ‖w‖⁻¹ * ‖σ g w - w‖ := by
      simp only [u, map_smul, ← smul_sub, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr hwn.le)]
    rw [hscale] at hgt
    have hle1 : (1 / 4 : ℝ) ^ k * ‖w‖ ≤ ‖σ g w - w‖ := by
      have hmul := mul_le_mul_of_nonneg_left hgt.le hwn.le
      rw [← mul_assoc, mul_inv_cancel₀ hwn.ne', one_mul, mul_comm] at hmul
      exact hmul
    have hsq : ((1 / 4 : ℝ) ^ k) ^ 2 * ‖w‖ ^ 2 ≤ ‖σ g w - w‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hle1 2
    exact hsq.trans (Finset.single_le_sum (fun x _ => sq_nonneg ‖σ x w - w‖) hgF)

private noncomputable def M_op {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : Finset Γ) (ρ : Γ →* E ≃ₗᵢ[ℂ] E) : E →L[ℂ] E :=
  (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ E +
    ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (ρ g).toLinearIsometry.toContinuousLinearMap

private lemma M_op_apply {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : Finset Γ) (ρ : Γ →* E ≃ₗᵢ[ℂ] E) (w : E) :
    M_op F ρ w = (2 : ℂ)⁻¹ • w + ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, ρ g w := by
  simp only [M_op, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.id_apply,
    _root_.sum_apply]
  rfl

private lemma M_op_sub_inner_re {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : Finset Γ) (hFpos : 0 < F.card)
    (ρ : Γ →* E ≃ₗᵢ[ℂ] E) (w : E) :
    RCLike.re ⟪w - M_op F ρ w, w⟫_ℂ = (4 * (F.card : ℝ))⁻¹ * ∑ g ∈ F, ‖ρ g w - w‖ ^ 2 := by
  have hFne : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hFpos.ne'
  have hsum : ∑ g ∈ F, ‖ρ g w - w‖ ^ 2 =
      2 * (F.card : ℝ) * ‖w‖ ^ 2 - 2 * ∑ g ∈ F, RCLike.re ⟪ρ g w, w⟫_ℂ := by
    have hterm : ∀ g : Γ, ‖ρ g w - w‖ ^ 2 = 2 * ‖w‖ ^ 2 - 2 * RCLike.re ⟪ρ g w, w⟫_ℂ := by
      intro g
      rw [norm_sub_sq (𝕜 := ℂ), (ρ g).norm_map]
      ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hlhs : RCLike.re ⟪w - M_op F ρ w, w⟫_ℂ =
      (2 : ℝ)⁻¹ * ‖w‖ ^ 2 - (2 * (F.card : ℝ))⁻¹ * ∑ g ∈ F, RCLike.re ⟪ρ g w, w⟫_ℂ := by
    rw [M_op_apply, inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left, sum_inner]
    have hcast1 : (starRingEnd ℂ) (2 : ℂ)⁻¹ = (((2 : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [map_inv₀, map_ofNat]; norm_num
    have hcast2 : (starRingEnd ℂ) (2 * (F.card : ℂ))⁻¹ = (((2 * (F.card : ℝ))⁻¹ : ℝ) : ℂ) := by
      rw [map_inv₀, map_mul, map_ofNat, Complex.conj_natCast]; push_cast; rfl
    rw [hcast1, hcast2, map_sub, map_add]
    simp only [RCLike.re_eq_complex_re, Complex.re_ofReal_mul]
    simp only [← RCLike.re_eq_complex_re, map_sum, inner_self_eq_norm_sq (𝕜 := ℂ)]
    ring
  rw [hlhs, hsum]
  field_simp [hFne]
  ring

private lemma M_op_fixed {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : Finset Γ) (hFpos : 0 < F.card)
    (ρ : Γ →* E ≃ₗᵢ[ℂ] E) {w : E} (hw : w ∈ fixedSubspace ρ) :
    M_op F ρ w = w := by
  have hFne : (F.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hFpos.ne'
  rw [M_op_apply]
  have hsum : ∑ g ∈ F, ρ g w = (F.card : ℂ) • w := by
    calc ∑ g ∈ F, ρ g w = ∑ _g ∈ F, w := Finset.sum_congr rfl fun g _ => hw g
      _ = F.card • w := Finset.sum_const _
      _ = (F.card : ℂ) • w := by rw [Nat.cast_smul_eq_nsmul]
  rw [hsum, smul_smul, ← add_smul]
  have hcoeff : (2 : ℂ)⁻¹ + (2 * (F.card : ℂ))⁻¹ * (F.card : ℂ) = 1 := by
    field_simp [hFne]; ring
  rw [hcoeff, one_smul]

private lemma M_op_maps_orth {Γ E : Type} [Group Γ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : Finset Γ) (ρ : Γ →* E ≃ₗᵢ[ℂ] E) {w : E}
    (hw : w ∈ (fixedSubspace ρ)ᗮ) :
    M_op F ρ w ∈ (fixedSubspace ρ)ᗮ := by
  rw [M_op_apply]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hw)
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => mem_orth_fixedSubspace_map ρ g hw))

private lemma M_op_no_eigenvalue_in_gap {Γ H : Type} [Group Γ]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F : Finset Γ) (hFpos : 0 < F.card) {κ : ℝ}
    (hKaz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (σ : Γ →* E ≃ₗᵢ[ℂ] E),
      (∀ w : E, (∀ g : Γ, σ g w = w) → w = 0) →
      ∀ w : E, κ ^ 2 * ‖w‖ ^ 2 ≤ ∑ g ∈ F, ‖σ g w - w‖ ^ 2)
    (σ : Γ →* H ≃ₗᵢ[ℂ] H) {lam : ℝ}
    (hlam1 : 1 - κ ^ 2 / (4 * (F.card : ℝ)) < lam) (hlam2 : lam < 1)
    {w : H} (hw : M_op F σ w = (lam : ℂ) • w) : w = 0 := by
  have : CompleteSpace ↥(fixedSubspace σ) := completeSpace_fixedSubspace σ
  have : (fixedSubspace σ).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have : CompleteSpace ↥(fixedSubspace σ)ᗮ := completeSpace_fixedSubspace_orth σ
  let w₁ : H := (fixedSubspace σ).starProjection w
  let w₂ : H := (fixedSubspace σ)ᗮ.starProjection w
  have hw_eq : w₁ + w₂ = w := Submodule.starProjection_add_starProjection_orthogonal w
  have hw₁_mem : w₁ ∈ fixedSubspace σ := Submodule.coe_mem _
  have hw₂_mem : w₂ ∈ (fixedSubspace σ)ᗮ := Submodule.coe_mem _
  have hM1 : M_op F σ w₁ = w₁ := M_op_fixed F hFpos σ hw₁_mem
  have hM2_mem : M_op F σ w₂ ∈ (fixedSubspace σ)ᗮ := M_op_maps_orth F σ hw₂_mem
  have hcomb : w₁ + M_op F σ w₂ = (lam : ℂ) • w₁ + (lam : ℂ) • w₂ := by
    calc w₁ + M_op F σ w₂ = M_op F σ (w₁ + w₂) := by rw [map_add, hM1]
      _ = M_op F σ w := by rw [hw_eq]
      _ = (lam : ℂ) • w := hw
      _ = (lam : ℂ) • (w₁ + w₂) := by rw [hw_eq]
      _ = (lam : ℂ) • w₁ + (lam : ℂ) • w₂ := smul_add _ _ _
  have hdiff_eq : ((1 - lam : ℝ) : ℂ) • w₁ = (lam : ℂ) • w₂ - M_op F σ w₂ := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    exact sub_eq_sub_iff_add_eq_add.mpr (by rw [hcomb, add_comm ((lam : ℂ) • w₁)])
  have hw₁_zero : w₁ = 0 := by
    have hmem1 : ((1 - lam : ℝ) : ℂ) • w₁ ∈ fixedSubspace σ :=
      Submodule.smul_mem _ _ hw₁_mem
    have hmem2 : ((1 - lam : ℝ) : ℂ) • w₁ ∈ (fixedSubspace σ)ᗮ := by
      rw [hdiff_eq]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hw₂_mem) hM2_mem
    have h0 : ⟪((1 - lam : ℝ) : ℂ) • w₁, ((1 - lam : ℝ) : ℂ) • w₁⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hmem2 _ hmem1
    have hsm0 : ((1 - lam : ℝ) : ℂ) • w₁ = 0 := inner_self_eq_zero.mp h0
    have hne : ((1 - lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    exact (smul_eq_zero.mp hsm0).resolve_left hne
  have hw_orth : w ∈ (fixedSubspace σ)ᗮ := by
    rw [← hw_eq, hw₁_zero, zero_add]; exact hw₂_mem
  have hkaz := hKaz ↥(fixedSubspace σ)ᗮ (orthRep σ) (orthRep_no_fixed σ) ⟨w, hw_orth⟩
  have hkaz' : κ ^ 2 * ‖w‖ ^ 2 ≤ ∑ g ∈ F, ‖σ g w - w‖ ^ 2 := hkaz
  have hre_sub := M_op_sub_inner_re F hFpos σ w
  have hre_lhs : RCLike.re ⟪w - M_op F σ w, w⟫_ℂ = (1 - lam) * ‖w‖ ^ 2 := by
    have hsub : w - M_op F σ w = ((1 - lam : ℝ) : ℂ) • w := by
      rw [hw, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [hsub, inner_smul_left, Complex.conj_ofReal, RCLike.re_eq_complex_re,
      Complex.re_ofReal_mul, ← RCLike.re_eq_complex_re, inner_self_eq_norm_sq (𝕜 := ℂ)]
  have hFposR : (0 : ℝ) < 4 * (F.card : ℝ) := by positivity
  have hle_gap : κ ^ 2 / (4 * (F.card : ℝ)) * ‖w‖ ^ 2 ≤ (1 - lam) * ‖w‖ ^ 2 := by
    rw [← hre_lhs, hre_sub, div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hkaz' (inv_nonneg.mpr hFposR.le)
  have hnorm0 : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm0)

private lemma M_op_fixed_implies_invariant {Γ H : Type} [Group Γ]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F : Finset Γ) (hFpos : 0 < F.card) {κ : ℝ} (hκ0 : 0 < κ)
    (hKaz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (σ : Γ →* E ≃ₗᵢ[ℂ] E),
      (∀ w : E, (∀ g : Γ, σ g w = w) → w = 0) →
      ∀ w : E, κ ^ 2 * ‖w‖ ^ 2 ≤ ∑ g ∈ F, ‖σ g w - w‖ ^ 2)
    (σ : Γ →* H ≃ₗᵢ[ℂ] H) {w : H} (hw : M_op F σ w = w) :
    ∀ g : Γ, σ g w = w := by
  have : CompleteSpace ↥(fixedSubspace σ) := completeSpace_fixedSubspace σ
  have : (fixedSubspace σ).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have : CompleteSpace ↥(fixedSubspace σ)ᗮ := completeSpace_fixedSubspace_orth σ
  let w₁ : H := (fixedSubspace σ).starProjection w
  let w₂ : H := (fixedSubspace σ)ᗮ.starProjection w
  have hw_eq : w₁ + w₂ = w := Submodule.starProjection_add_starProjection_orthogonal w
  have hM1 : M_op F σ w₁ = w₁ := M_op_fixed F hFpos σ (Submodule.coe_mem _)
  have hM2 : M_op F σ w₂ = w₂ := by
    have h1 : w₁ + M_op F σ w₂ = w₁ + w₂ := by
      calc w₁ + M_op F σ w₂ = M_op F σ (w₁ + w₂) := by rw [map_add, hM1]
        _ = M_op F σ w := by rw [hw_eq]
        _ = w := hw
        _ = w₁ + w₂ := hw_eq.symm
    exact add_left_cancel h1
  have hkaz := hKaz ↥(fixedSubspace σ)ᗮ (orthRep σ) (orthRep_no_fixed σ) ⟨w₂, Submodule.coe_mem _⟩
  have hre := M_op_sub_inner_re F hFpos σ w₂
  rw [hM2, sub_self, inner_zero_left, map_zero] at hre
  have hFposR : (0 : ℝ) < 4 * (F.card : ℝ) := by positivity
  have hsum0 : ∑ g ∈ F, ‖σ g w₂ - w₂‖ ^ 2 = 0 := by
    have := mul_eq_zero.mp hre.symm
    exact this.resolve_left (inv_ne_zero hFposR.ne')
  have hkaz' : κ ^ 2 * ‖w₂‖ ^ 2 ≤ 0 := by
    have h1 : κ ^ 2 * ‖w₂‖ ^ 2 ≤ ∑ g ∈ F, ‖σ g w₂ - w₂‖ ^ 2 := hkaz
    linarith
  have hw₂_zero : w₂ = 0 := by
    have h0 : ‖w₂‖ ^ 2 = 0 := by nlinarith [sq_pos_of_pos hκ0, sq_nonneg ‖w₂‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
  have hw_mem : w ∈ fixedSubspace σ := by
    rw [← hw_eq, hw₂_zero, add_zero]; exact Submodule.coe_mem _
  exact hw_mem

/- Section 3: Vector ultraproduct Hilbert space and asymptotic unitary representation -/

private lemma hyperfilter_le_atTop : (Filter.hyperfilter ℕ : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  exact Filter.hyperfilter_le_cofinite

private lemma tendsto_limUnder_of_bdd_complex {f : ℕ → ℂ} (hb : ∃ C : ℝ, ∀ j, ‖f j‖ ≤ C) :
    Tendsto f (Filter.hyperfilter ℕ) (𝓝 (limUnder (Filter.hyperfilter ℕ) f)) := by
  obtain ⟨C, hC⟩ := hb
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) C) := isCompact_closedBall 0 C
  have hmem : ∀ j, f j ∈ Metric.closedBall (0 : ℂ) C := fun j => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hC j
  have hle : ((Filter.hyperfilter ℕ).map f : Filter ℂ) ≤ Filter.principal (Metric.closedBall 0 C) :=
    Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hmem)
  obtain ⟨L, _, hL⟩ := hcomp.ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map f) hle
  exact tendsto_nhds_limUnder ⟨L, hL⟩

private structure BVec (n : ℕ → ℕ) : Type where
  seq : ∀ j : ℕ, EuclideanSpace ℂ (Fin (n j))
  bdd : ∃ C : ℝ, ∀ j : ℕ, ‖seq j‖ ≤ C

namespace BVec

variable {n : ℕ → ℕ}

private lemma ext {f g : BVec n} (h : ∀ j, f.seq j = g.seq j) : f = g := by
  cases f; cases g; simp only [mk.injEq]; funext j; exact h j

private instance : Zero (BVec n) := ⟨⟨fun _ => 0, ⟨0, fun _ => by simp⟩⟩⟩

private instance : Add (BVec n) :=
  ⟨fun f g => ⟨fun j => f.seq j + g.seq j, by
    obtain ⟨C1, h1⟩ := f.bdd
    obtain ⟨C2, h2⟩ := g.bdd
    exact ⟨C1 + C2, fun j => (norm_add_le _ _).trans (add_le_add (h1 j) (h2 j))⟩⟩⟩

private instance : Neg (BVec n) :=
  ⟨fun f => ⟨fun j => -f.seq j, by
    obtain ⟨C, h⟩ := f.bdd
    exact ⟨C, fun j => by rw [norm_neg]; exact h j⟩⟩⟩

private instance : Sub (BVec n) :=
  ⟨fun f g => ⟨fun j => f.seq j - g.seq j, by
    obtain ⟨C1, h1⟩ := f.bdd
    obtain ⟨C2, h2⟩ := g.bdd
    exact ⟨C1 + C2, fun j => (norm_sub_le _ _).trans (add_le_add (h1 j) (h2 j))⟩⟩⟩

private instance : SMul ℂ (BVec n) :=
  ⟨fun c f => ⟨fun j => c • f.seq j, by
    obtain ⟨C, h⟩ := f.bdd
    exact ⟨‖c‖ * max C 0, fun j => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left ((h j).trans (le_max_left _ _)) (norm_nonneg _)⟩⟩⟩

private instance : AddCommGroup (BVec n) where
  add_assoc a b c := BVec.ext fun j => add_assoc (a.seq j) (b.seq j) (c.seq j)
  zero_add a := BVec.ext fun j => zero_add (a.seq j)
  add_zero a := BVec.ext fun j => add_zero (a.seq j)
  add_comm a b := BVec.ext fun j => add_comm (a.seq j) (b.seq j)
  sub_eq_add_neg a b := BVec.ext fun j => sub_eq_add_neg (a.seq j) (b.seq j)
  neg_add_cancel a := BVec.ext fun j => neg_add_cancel (a.seq j)
  nsmul := nsmulRec
  zsmul := zsmulRec

private instance : Module ℂ (BVec n) where
  one_smul a := BVec.ext fun j => one_smul ℂ (a.seq j)
  mul_smul c1 c2 a := BVec.ext fun j => mul_smul c1 c2 (a.seq j)
  smul_zero c := BVec.ext fun _ => smul_zero c
  smul_add c a b := BVec.ext fun j => smul_add c (a.seq j) (b.seq j)
  add_smul c1 c2 a := BVec.ext fun j => add_smul c1 c2 (a.seq j)
  zero_smul a := BVec.ext fun j => zero_smul ℂ (a.seq j)

private lemma inner_bdd (f g : BVec n) : ∃ C : ℝ, ∀ j, ‖⟪f.seq j, g.seq j⟫_ℂ‖ ≤ C := by
  obtain ⟨C1, h1⟩ := f.bdd
  obtain ⟨C2, h2⟩ := g.bdd
  refine ⟨max C1 0 * max C2 0, fun j => (norm_inner_le_norm _ _).trans ?_⟩
  exact mul_le_mul ((h1 j).trans (le_max_left _ _)) ((h2 j).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

private noncomputable def ultraInner (f g : BVec n) : ℂ :=
  limUnder (Filter.hyperfilter ℕ) (fun j => ⟪f.seq j, g.seq j⟫_ℂ)

private lemma tendsto_ultraInner (f g : BVec n) :
    Tendsto (fun j => ⟪f.seq j, g.seq j⟫_ℂ) (Filter.hyperfilter ℕ) (𝓝 (ultraInner f g)) :=
  tendsto_limUnder_of_bdd_complex (inner_bdd f g)

private noncomputable instance instPreInnerCore : PreInnerProductSpace.Core ℂ (BVec n) where
  inner := ultraInner
  conj_inner_symm f g := by
    have h1 := (continuous_star.continuousAt.tendsto (x := ultraInner g f)).comp (tendsto_ultraInner g f)
    have h2 := tendsto_ultraInner f g
    have heq : (fun j => star ⟪g.seq j, f.seq j⟫_ℂ) = (fun j => ⟪f.seq j, g.seq j⟫_ℂ) := by
      funext j; exact inner_conj_symm _ _
    change star (ultraInner g f) = ultraInner f g
    rw [Function.comp_def, heq] at h1
    exact tendsto_nhds_unique h1 h2
  re_inner_nonneg f := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_ultraInner f f)
    exact ge_of_tendsto' h (fun j => inner_self_nonneg (𝕜 := ℂ) (x := f.seq j))
  add_left f g h := by
    have h1 := (tendsto_ultraInner f h).add (tendsto_ultraInner g h)
    have h2 := tendsto_ultraInner (f + g) h
    have heq : (fun j => ⟪(f + g).seq j, h.seq j⟫_ℂ) =
        (fun j => ⟪f.seq j, h.seq j⟫_ℂ + ⟪g.seq j, h.seq j⟫_ℂ) := by
      funext j; exact inner_add_left _ _ _
    rw [heq] at h2
    exact tendsto_nhds_unique h2 h1
  smul_left f g r := by
    have h1 := (tendsto_ultraInner f g).const_mul ((starRingEnd ℂ) r)
    have h2 := tendsto_ultraInner (r • f) g
    have heq : (fun j => ⟪(r • f).seq j, g.seq j⟫_ℂ) =
        (fun j => (starRingEnd ℂ) r * ⟪f.seq j, g.seq j⟫_ℂ) := by
      funext j; exact inner_smul_left _ _ _
    rw [heq] at h2
    exact tendsto_nhds_unique h2 h1

private noncomputable instance instSeminormedAddCommGroup : SeminormedAddCommGroup (BVec n) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (BVec n) _ _ _ instPreInnerCore

private noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (BVec n) :=
  InnerProductSpace.ofCore instPreInnerCore

private lemma tendsto_norm_sq (f : BVec n) :
    Tendsto (fun j => ‖f.seq j‖ ^ 2) (Filter.hyperfilter ℕ) (𝓝 (‖f‖ ^ 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_ultraInner f f)
  have hre : (ultraInner f f).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  rw [hre] at h
  have heq : (fun j => (⟪f.seq j, f.seq j⟫_ℂ).re) = (fun j => ‖f.seq j‖ ^ 2) := by
    funext j; exact inner_self_eq_norm_sq (𝕜 := ℂ) (f.seq j)
  rwa [Function.comp_def, heq] at h

private lemma norm_eq_zero_of_tendsto_zero_hyper (f : BVec n)
    (h : Tendsto (fun j => ‖f.seq j‖) (Filter.hyperfilter ℕ) (𝓝 0)) : ‖f‖ = 0 := by
  have hsq : Tendsto (fun j => ‖f.seq j‖ ^ 2) (Filter.hyperfilter ℕ) (𝓝 0) := by
    have h0 := h.pow 2
    rwa [zero_pow two_ne_zero] at h0
  have heq : ‖f‖ ^ 2 = 0 := tendsto_nhds_unique (tendsto_norm_sq f) hsq
  exact sq_eq_zero_iff.mp heq

private lemma norm_eq_zero_of_tendsto_zero (f : BVec n)
    (h : Tendsto (fun j => ‖f.seq j‖) atTop (𝓝 0)) : ‖f‖ = 0 :=
  norm_eq_zero_of_tendsto_zero_hyper f (h.mono_left hyperfilter_le_atTop)

private lemma coe_eq_of_norm_sub_eq_zero {f g : BVec n} (h : ‖f - g‖ = 0) :
    (f : UniformSpace.Completion (BVec n)) = (g : UniformSpace.Completion (BVec n)) := by
  apply sub_eq_zero.mp
  rw [← UniformSpace.Completion.coe_sub]
  apply norm_eq_zero.mp
  rw [UniformSpace.Completion.norm_coe]
  exact h

end BVec

private noncomputable def liftLinearIsometry {E₀ : Type} [SeminormedAddCommGroup E₀]
    [InnerProductSpace ℂ E₀] (f : E₀ →ₗᵢ[ℂ] E₀) :
    UniformSpace.Completion E₀ →ₗᵢ[ℂ] UniformSpace.Completion E₀ where
  toFun := UniformSpace.Completion.map f
  map_add' x y := by
    refine UniformSpace.Completion.induction_on₂ x y ?_ fun a b => ?_
    · exact isClosed_eq
        ((UniformSpace.Completion.continuous_map (f := f)).comp continuous_add)
        (((UniformSpace.Completion.continuous_map (f := f)).comp continuous_fst).add
          ((UniformSpace.Completion.continuous_map (f := f)).comp continuous_snd))
    · rw [← UniformSpace.Completion.coe_add,
        UniformSpace.Completion.map_coe f.isometry.uniformContinuous,
        UniformSpace.Completion.map_coe f.isometry.uniformContinuous,
        UniformSpace.Completion.map_coe f.isometry.uniformContinuous,
        map_add, UniformSpace.Completion.coe_add]
  map_smul' c x := by
    refine UniformSpace.Completion.induction_on x ?_ fun a => ?_
    · exact isClosed_eq
        ((UniformSpace.Completion.continuous_map (f := f)).comp (continuous_const_smul c))
        ((continuous_const_smul c).comp (UniformSpace.Completion.continuous_map (f := f)))
    · rw [← UniformSpace.Completion.coe_smul,
        UniformSpace.Completion.map_coe f.isometry.uniformContinuous,
        UniformSpace.Completion.map_coe f.isometry.uniformContinuous,
        map_smul, UniformSpace.Completion.coe_smul]
      rfl
  norm_map' x := by
    change ‖UniformSpace.Completion.map f x‖ = ‖x‖
    refine UniformSpace.Completion.induction_on x ?_ fun a => ?_
    · exact isClosed_eq
        (continuous_norm.comp (UniformSpace.Completion.continuous_map (f := f)))
        continuous_norm
    · rw [UniformSpace.Completion.map_coe f.isometry.uniformContinuous,
        UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, f.norm_map]

private lemma liftLinearIsometry_coe {E₀ : Type} [SeminormedAddCommGroup E₀]
    [InnerProductSpace ℂ E₀] (f : E₀ →ₗᵢ[ℂ] E₀) (a : E₀) :
    liftLinearIsometry f (a : UniformSpace.Completion E₀) = (f a : UniformSpace.Completion E₀) :=
  UniformSpace.Completion.map_coe f.isometry.uniformContinuous a

private lemma U_one_tendsto {G : Type} [Group G] {n : ℕ → ℕ}
    {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0)) :
    Tendsto (fun j => opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1)) atTop (𝓝 0) := by
  have h1 := hUmul 1 1
  simp only [mul_one] at h1
  refine h1.congr fun j => ?_
  rw [← opNorm_sub_eq_opDist]
  have hu : (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ *
      (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (U j 1).2
  have hEq : (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ *
      ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
        (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)) =
      1 - (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  change opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)) =
    opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1)
  rw [← opNorm_mul_unitary_conjTranspose_left (U j 1), hEq, opNorm_sub_comm]

private lemma U_inv_tendsto {G : Type} [Group G] {n : ℕ → ℕ}
    {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (g : G) :
    Tendsto (fun j => opNorm ((U j g⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ)) atTop (𝓝 0) := by
  have h1 := hUmul g g⁻¹
  rw [mul_inv_cancel] at h1
  have h2 := U_one_tendsto hUmul
  have hsum : Tendsto (fun j => opDist (U j 1) (U j g * U j g⁻¹) +
      opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1)) atTop (𝓝 0) := by
    simpa using h1.add h2
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
  have hu : (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ *
      (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (U j g).2
  have hEq : (U j g⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ =
      (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ *
        ((U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hu, Matrix.one_mul, Matrix.mul_one]
  rw [hEq, opNorm_mul_unitary_conjTranspose_left (U j g)]
  have hsplit : (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1 =
      ((U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
        (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)) +
      ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := by abel
  rw [hsplit]
  have hle := opNorm_add_le
    ((U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ))
    ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1)
  have hcomm : opNorm ((U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)) = opDist (U j 1) (U j g * U j g⁻¹) := by
    rw [opNorm_sub_comm]
    exact opNorm_sub_eq_opDist (U j 1) (U j g * U j g⁻¹)
  linarith

private lemma U_conj_tendsto {G : Type} [Group G] {n : ℕ → ℕ}
    {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (t g : G) :
    Tendsto (fun j => opNorm ((U j (t * g * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
        (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ)) atTop (𝓝 0) := by
  have h1 := hUmul (t * g) t⁻¹
  have h2 := hUmul t g
  have h3 := U_inv_tendsto hUmul t
  have hsum : Tendsto (fun j => opDist (U j (t * g * t⁻¹)) (U j (t * g) * U j t⁻¹) +
      (opDist (U j (t * g)) (U j t * U j g) +
        opNorm ((U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ))) atTop (𝓝 0) := by
    simpa using h1.add (h2.add h3)
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
  have hsplit : (U j (t * g * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
        (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ =
      ((U j (t * g * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
        (U j (t * g) : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ)) +
      (((U j (t * g) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
          (U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
          ((U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hsplit]
  have ha := opNorm_add_le
    ((U j (t * g * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j (t * g) : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ))
    (((U j (t * g) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
        (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
        (U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
      ((U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
        ((U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ))
  have hb := opNorm_add_le
    (((U j (t * g) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
        (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
        (U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ))
    (((U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
        ((U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ))
  have ht1 : opNorm ((U j (t * g * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j (t * g) : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ)) =
      opDist (U j (t * g * t⁻¹)) (U j (t * g) * U j t⁻¹) :=
    opNorm_sub_eq_opDist (U j (t * g * t⁻¹)) (U j (t * g) * U j t⁻¹)
  have ht2 : opNorm (((U j (t * g) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
      (U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ)) = opDist (U j (t * g)) (U j t * U j g) := by
    rw [opNorm_mul_unitary_right]
    exact opNorm_sub_eq_opDist (U j (t * g)) (U j t * U j g)
  have ht3 : opNorm (((U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
      (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ)) *
      ((U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ)) =
      opNorm ((U j t⁻¹ : Matrix (Fin (n j)) (Fin (n j)) ℂ) - (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ) := by
    rw [Matrix.mul_assoc (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)
      (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ),
      opNorm_mul_unitary_left (U j t), opNorm_mul_unitary_left (U j g)]
  linarith

private noncomputable def actBVecFun {G : Type} {n : ℕ → ℕ}
    (U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ) (g : G) (f : BVec n) : BVec n :=
  ⟨fun j => Matrix.toEuclideanCLM (𝕜 := ℂ) (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) (f.seq j), by
    obtain ⟨C, hC⟩ := f.bdd
    exact ⟨C, fun j => by rw [norm_toEuclideanCLM_unitary]; exact hC j⟩⟩

private noncomputable def actBVec {G : Type} {n : ℕ → ℕ}
    (U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ) (g : G) :
    BVec n →ₗᵢ[ℂ] BVec n where
  toFun := actBVecFun U g
  map_add' f₁ f₂ := BVec.ext fun j => map_add _ _ _
  map_smul' c f := BVec.ext fun j => map_smul _ _ _
  norm_map' f := by
    change ‖actBVecFun U g f‖ = ‖f‖
    have h1 := BVec.tendsto_norm_sq f
    have h2 := BVec.tendsto_norm_sq (actBVecFun U g f)
    have heq : (fun j => ‖(actBVecFun U g f).seq j‖ ^ 2) = (fun j => ‖f.seq j‖ ^ 2) := by
      funext j; exact congrArg (· ^ 2) (norm_toEuclideanCLM_unitary (U j g) (f.seq j))
    rw [heq] at h2
    have hsq := tendsto_nhds_unique h2 h1
    nlinarith [norm_nonneg f, norm_nonneg (actBVecFun U g f)]

private noncomputable def ultraRep {G : Type} [Group G] {n : ℕ → ℕ}
    (U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ)
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0)) :
    G →* UniformSpace.Completion (BVec n) ≃ₗᵢ[ℂ] UniformSpace.Completion (BVec n) := by
  let L : G → UniformSpace.Completion (BVec n) →ₗᵢ[ℂ] UniformSpace.Completion (BVec n) :=
    fun g => liftLinearIsometry (actBVec U g)
  have hL1 : ∀ v, L 1 v = v := by
    intro v
    refine UniformSpace.Completion.induction_on v
      (isClosed_eq (L 1).continuous continuous_id) fun f => ?_
    rw [liftLinearIsometry_coe]
    apply BVec.coe_eq_of_norm_sub_eq_zero
    apply BVec.norm_eq_zero_of_tendsto_zero
    obtain ⟨C, hC⟩ := f.bdd
    have h0 : Tendsto (fun j => opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * max C 0)
        atTop (𝓝 0) := by
      simpa using (U_one_tendsto hUmul).mul_const (max C 0)
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h0
    have hdiff : (actBVec U 1 f - f).seq j =
        Matrix.toEuclideanCLM (𝕜 := ℂ) ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) (f.seq j) := by
      rw [toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply]; rfl
    rw [hdiff]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left ((hC j).trans (le_max_left _ _)) (opNorm_nonneg _))
  have hLmul : ∀ g h v, L (g * h) v = L g (L h v) := by
    intro g h v
    refine UniformSpace.Completion.induction_on v
      (isClosed_eq (L (g * h)).continuous ((L g).continuous.comp (L h).continuous)) fun f => ?_
    rw [liftLinearIsometry_coe, liftLinearIsometry_coe, liftLinearIsometry_coe]
    apply BVec.coe_eq_of_norm_sub_eq_zero
    apply BVec.norm_eq_zero_of_tendsto_zero
    obtain ⟨C, hC⟩ := f.bdd
    have h0 : Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h) * max C 0) atTop (𝓝 0) := by
      simpa using (hUmul g h).mul_const (max C 0)
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h0
    have hdiff : (actBVec U (g * h) f - actBVec U g (actBVec U h f)).seq j =
        Matrix.toEuclideanCLM (𝕜 := ℂ)
          ((U j (g * h) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j h : Matrix (Fin (n j)) (Fin (n j)) ℂ))
          (f.seq j) := by
      rw [toEuclideanCLM_sub_apply, toEuclideanCLM_mul_apply]; rfl
    rw [hdiff]
    have hnorm : opNorm ((U j (g * h) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
        (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j h : Matrix (Fin (n j)) (Fin (n j)) ℂ)) =
        opDist (U j (g * h)) (U j g * U j h) :=
      opNorm_sub_eq_opDist (U j (g * h)) (U j g * U j h)
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
          ((U j (g * h) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j h : Matrix (Fin (n j)) (Fin (n j)) ℂ))
          (f.seq j)‖
        ≤ opDist (U j (g * h)) (U j g * U j h) * ‖f.seq j‖ := by
          rw [← hnorm]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ opDist (U j (g * h)) (U j g * U j h) * max C 0 :=
          mul_le_mul_of_nonneg_left ((hC j).trans (le_max_left _ _)) (norm_nonneg _)
  exact
    { toFun := fun g =>
        { toFun := L g
          invFun := L g⁻¹
          map_add' := (L g).map_add
          map_smul' := (L g).map_smul
          left_inv := fun v => by rw [← hLmul, inv_mul_cancel, hL1]
          right_inv := fun v => by rw [← hLmul, mul_inv_cancel, hL1]
          norm_map' := (L g).norm_map }
      map_one' := by ext v; exact hL1 v
      map_mul' := fun g h => by ext v; exact hLmul g h v }

private lemma ultraRep_coe {G : Type} [Group G] {n : ℕ → ℕ}
    (U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ)
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (g : G) (f : BVec n) :
    ultraRep U hUmul g (f : UniformSpace.Completion (BVec n)) =
      (actBVec U g f : UniformSpace.Completion (BVec n)) :=
  liftLinearIsometry_coe (actBVec U g) f

/- Section 4: Finite-support group-ring evaluation and asymptotic multiplicativity -/

private noncomputable def gmul {G : Type} [Group G] (a b : G →₀ ℂ) : G →₀ ℂ :=
  a.sum fun g z => b.sum fun h w => Finsupp.single (g * h) (z * w)

private noncomputable def gpow {G : Type} [Group G] (a : G →₀ ℂ) : ℕ → (G →₀ ℂ)
  | 0 => Finsupp.single 1 1
  | k + 1 => gmul (gpow a k) a

private noncomputable def evalU {G : Type} {m : ℕ}
    (U : G → Matrix.unitaryGroup (Fin m) ℂ) (a : G →₀ ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  a.sum fun g z => z • (U g : Matrix (Fin m) (Fin m) ℂ)

private noncomputable def evalρ {G E : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (a : G →₀ ℂ) (v : E) : E :=
  a.sum fun g z => z • ρ g v

private lemma evalU_single {G : Type} {m : ℕ} (U : G → Matrix.unitaryGroup (Fin m) ℂ)
    (g : G) (z : ℂ) :
    evalU U (Finsupp.single g z) = z • (U g : Matrix (Fin m) (Fin m) ℂ) := by
  unfold evalU
  exact Finsupp.sum_single_index (zero_smul _ _)

private lemma evalU_add {G : Type} {m : ℕ} (U : G → Matrix.unitaryGroup (Fin m) ℂ)
    (a b : G →₀ ℂ) : evalU U (a + b) = evalU U a + evalU U b := by
  unfold evalU
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

private lemma evalU_sub {G : Type} {m : ℕ} (U : G → Matrix.unitaryGroup (Fin m) ℂ)
    (a b : G →₀ ℂ) : evalU U (a - b) = evalU U a - evalU U b := by
  have h := evalU_add U (a - b) b
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private lemma evalU_smul {G : Type} {m : ℕ} (U : G → Matrix.unitaryGroup (Fin m) ℂ)
    (c : ℂ) (a : G →₀ ℂ) : evalU U (c • a) = c • evalU U a := by
  induction a using Finsupp.induction with
  | zero => simp [evalU]
  | single_add g z b _ _ ih =>
    rw [smul_add, evalU_add, evalU_add, smul_add, ih, Finsupp.smul_single,
      evalU_single, evalU_single, smul_smul, smul_eq_mul]

private lemma evalU_finset_sum {G ι : Type} {m : ℕ} (U : G → Matrix.unitaryGroup (Fin m) ℂ)
    (s : Finset ι) (f : ι → G →₀ ℂ) :
    evalU U (∑ i ∈ s, f i) = ∑ i ∈ s, evalU U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalU]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, evalU_add, ih]

private lemma evalU_finsupp_sum {G α : Type} {m : ℕ} (U : G → Matrix.unitaryGroup (Fin m) ℂ)
    (a : α →₀ ℂ) (f : α → ℂ → G →₀ ℂ) :
    evalU U (a.sum f) = a.sum fun x z => evalU U (f x z) :=
  evalU_finset_sum U a.support (fun x => f x (a x))

private lemma opNorm_evalU_le {G : Type} {m : ℕ} (U : G → Matrix.unitaryGroup (Fin m) ℂ)
    (a : G →₀ ℂ) : opNorm (evalU U a) ≤ a.sum fun _ z => ‖z‖ := by
  unfold evalU Finsupp.sum
  refine (opNorm_sum_le a.support _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [opNorm_smul]
  calc ‖a g‖ * opNorm (U g : Matrix (Fin m) (Fin m) ℂ)
      ≤ ‖a g‖ * 1 := mul_le_mul_of_nonneg_left (opNorm_unitary_le_one (U g)) (norm_nonneg _)
    _ = ‖a g‖ := mul_one _

private lemma evalρ_single {G E : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (g : G) (z : ℂ) (v : E) :
    evalρ ρ (Finsupp.single g z) v = z • ρ g v := by
  unfold evalρ
  exact Finsupp.sum_single_index (zero_smul _ _)

private lemma evalρ_add {G E : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (a b : G →₀ ℂ) (v : E) :
    evalρ ρ (a + b) v = evalρ ρ a v + evalρ ρ b v := by
  unfold evalρ
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

private lemma evalρ_sub {G E : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (a b : G →₀ ℂ) (v : E) :
    evalρ ρ (a - b) v = evalρ ρ a v - evalρ ρ b v := by
  have h := evalρ_add ρ (a - b) b v
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private lemma evalρ_smul {G E : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (c : ℂ) (a : G →₀ ℂ) (v : E) :
    evalρ ρ (c • a) v = c • evalρ ρ a v := by
  induction a using Finsupp.induction with
  | zero => simp [evalρ]
  | single_add g z b _ _ ih =>
    rw [smul_add, evalρ_add, evalρ_add, smul_add, ih, Finsupp.smul_single,
      evalρ_single, evalρ_single, smul_smul, smul_eq_mul]

private lemma evalρ_finset_sum {G E ι : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (s : Finset ι) (f : ι → G →₀ ℂ) (v : E) :
    evalρ ρ (∑ i ∈ s, f i) v = ∑ i ∈ s, evalρ ρ (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalρ]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, evalρ_add, ih]

private lemma evalρ_finsupp_sum {G E α : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (a : α →₀ ℂ) (f : α → ℂ → G →₀ ℂ) (v : E) :
    evalρ ρ (a.sum f) v = a.sum fun x z => evalρ ρ (f x z) v :=
  evalρ_finset_sum ρ a.support (fun x => f x (a x)) v

private lemma evalρ_gmul {G E : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (a b : G →₀ ℂ) (v : E) :
    evalρ ρ (gmul a b) v = evalρ ρ a (evalρ ρ b v) := by
  unfold gmul
  rw [evalρ_finsupp_sum]
  conv_rhs => unfold evalρ
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun g _ => ?_
  dsimp only
  rw [evalρ_finset_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [evalρ_single, map_smul, map_mul, smul_smul]
  rfl

private lemma evalρ_gpow {G E : Type} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : G →* E ≃ₗᵢ[ℂ] E) (a : G →₀ ℂ) :
    ∀ (k : ℕ) (v : E), evalρ ρ (gpow a k) v = (evalρ ρ a)^[k] v
  | 0, v => by simp [gpow, evalρ_single]
  | k + 1, v => by
    rw [gpow, evalρ_gmul, evalρ_gpow ρ a k, Function.iterate_succ_apply]

private lemma evalU_gmul_sub_tendsto {G : Type} [Group G] {n : ℕ → ℕ}
    {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (a b : G →₀ ℂ) :
    Tendsto (fun j => opNorm (evalU (U j) (gmul a b) - evalU (U j) a * evalU (U j) b))
      atTop (𝓝 0) := by
  have hsum_zero : Tendsto (fun j =>
      ∑ g ∈ a.support, ∑ h ∈ b.support, ‖a g * b h‖ * opDist (U j (g * h)) (U j g * U j h))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun j =>
        ∑ g ∈ a.support, ∑ h ∈ b.support, ‖a g * b h‖ * opDist (U j (g * h)) (U j g * U j h))
        atTop (𝓝 (∑ _g ∈ a.support, ∑ _h ∈ b.support, (0 : ℝ))) := by
      refine tendsto_finsetSum a.support fun g _ => tendsto_finsetSum b.support fun h _ => ?_
      simpa using (hUmul g h).const_mul ‖a g * b h‖
    simpa using h1
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum_zero
  have hrew : evalU (U j) (gmul a b) - evalU (U j) a * evalU (U j) b =
      ∑ g ∈ a.support, ∑ h ∈ b.support,
        (a g * b h) • ((U j (g * h) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j h : Matrix (Fin (n j)) (Fin (n j)) ℂ)) := by
    unfold gmul
    rw [evalU_finsupp_sum]
    have hlhs : (a.sum fun g z => evalU (U j) (b.sum fun h w => Finsupp.single (g * h) (z * w))) =
        ∑ g ∈ a.support, ∑ h ∈ b.support,
          (a g * b h) • (U j (g * h) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
      unfold Finsupp.sum
      refine Finset.sum_congr rfl fun g _ => ?_
      dsimp only
      rw [evalU_finset_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      exact evalU_single (U j) (g * h) (a g * b h)
    have hrhs : evalU (U j) a * evalU (U j) b =
        ∑ g ∈ a.support, ∑ h ∈ b.support,
          (a g * b h) • ((U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
            (U j h : Matrix (Fin (n j)) (Fin (n j)) ℂ)) := by
      unfold evalU Finsupp.sum
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hlhs, hrhs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_sub]
  rw [hrew]
  refine (opNorm_sum_le a.support _).trans (Finset.sum_le_sum fun g _ => ?_)
  refine (opNorm_sum_le b.support _).trans (Finset.sum_le_sum fun h _ => ?_)
  have hd : opNorm ((U j (g * h) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
      (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j h : Matrix (Fin (n j)) (Fin (n j)) ℂ)) =
      opDist (U j (g * h)) (U j g * U j h) :=
    opNorm_sub_eq_opDist (U j (g * h)) (U j g * U j h)
  rw [opNorm_smul, hd]

private lemma evalU_gpow_sub_tendsto {G : Type} [Group G] {n : ℕ → ℕ}
    {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (a : G →₀ ℂ) :
    ∀ k : ℕ, Tendsto (fun j => opNorm (evalU (U j) (gpow a k) - (evalU (U j) a) ^ k)) atTop (𝓝 0)
  | 0 => by
    have h1 := U_one_tendsto hUmul
    refine h1.congr fun j => ?_
    simp [gpow, evalU_single]
  | k + 1 => by
    have ih := evalU_gpow_sub_tendsto hUmul a k
    have hmul := evalU_gmul_sub_tendsto hUmul (gpow a k) a
    set C : ℝ := a.sum fun _ z => ‖z‖
    have hsum : Tendsto (fun j =>
        opNorm (evalU (U j) (gmul (gpow a k) a) - evalU (U j) (gpow a k) * evalU (U j) a) +
        opNorm (evalU (U j) (gpow a k) - (evalU (U j) a) ^ k) * C) atTop (𝓝 0) := by
      simpa using hmul.add (ih.mul_const C)
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
    have hsplit : evalU (U j) (gpow a (k + 1)) - (evalU (U j) a) ^ (k + 1) =
        (evalU (U j) (gmul (gpow a k) a) - evalU (U j) (gpow a k) * evalU (U j) a) +
        (evalU (U j) (gpow a k) - (evalU (U j) a) ^ k) * evalU (U j) a := by
      rw [gpow, pow_succ, Matrix.sub_mul]
      abel
    rw [hsplit]
    have h1 := opNorm_add_le
      (evalU (U j) (gmul (gpow a k) a) - evalU (U j) (gpow a k) * evalU (U j) a)
      ((evalU (U j) (gpow a k) - (evalU (U j) a) ^ k) * evalU (U j) a)
    have h2 : opNorm ((evalU (U j) (gpow a k) - (evalU (U j) a) ^ k) * evalU (U j) a) ≤
        opNorm (evalU (U j) (gpow a k) - (evalU (U j) a) ^ k) * C :=
      (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_evalU_le (U j) a) (opNorm_nonneg _))
    linarith

private lemma opNorm_pow_le {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) {C : ℝ}
    (hB : opNorm B ≤ C) : ∀ r : ℕ, opNorm (B ^ r) ≤ max C 1 ^ r
  | 0 => by simpa using opNorm_one_le_one
  | r + 1 => by
    rw [pow_succ, pow_succ]
    exact (opNorm_mul_le _ _).trans
      (mul_le_mul (opNorm_pow_le B hB r) (hB.trans (le_max_left _ _)) (opNorm_nonneg _)
        (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) r))

private lemma opNorm_pow_sub_pow_tendsto {n : ℕ → ℕ}
    {A B : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ j, opNorm (A j) ≤ C) (hB : ∀ j, opNorm (B j) ≤ C)
    (hdiff : Tendsto (fun j => opNorm (A j - B j)) atTop (𝓝 0)) :
    ∀ k : ℕ, Tendsto (fun j => opNorm ((A j) ^ k - (B j) ^ k)) atTop (𝓝 0)
  | 0 => by simp [opNorm_zero]
  | k + 1 => by
    have ih := opNorm_pow_sub_pow_tendsto hC hA hB hdiff k
    have hsum : Tendsto (fun j =>
        opNorm ((A j) ^ k - (B j) ^ k) * C + max C 1 ^ k * opNorm (A j - B j)) atTop (𝓝 0) := by
      simpa using (ih.mul_const C).add (hdiff.const_mul (max C 1 ^ k))
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
    have hsplit : (A j) ^ (k + 1) - (B j) ^ (k + 1) =
        ((A j) ^ k - (B j) ^ k) * A j + (B j) ^ k * (A j - B j) := by
      rw [pow_succ, pow_succ, Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [hsplit]
    have h1 := opNorm_add_le (((A j) ^ k - (B j) ^ k) * A j) ((B j) ^ k * (A j - B j))
    have h2 : opNorm (((A j) ^ k - (B j) ^ k) * A j) ≤ opNorm ((A j) ^ k - (B j) ^ k) * C :=
      (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hA j) (opNorm_nonneg _))
    have h3 : opNorm ((B j) ^ k * (A j - B j)) ≤ max C 1 ^ k * opNorm (A j - B j) :=
      (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_pow_le (B j) (hB j) k) (opNorm_nonneg _))
    linarith

/- Section 5: Spectral gap, projection alignment, and main proof of H3 -/

private lemma avg_hermPart_diff_tendsto {G : Type} [Group G] {Γ : Subgroup G}
    (F : Finset Γ) (hFpos : 0 < F.card) (hFsym : ∀ g ∈ F, g⁻¹ ∈ F)
    {n : ℕ → ℕ} {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0)) :
    let mΓ : G →₀ ℂ := (2 : ℂ)⁻¹ • Finsupp.single (1 : G) 1 +
      ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, Finsupp.single (g : G) 1
    let M0 : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
      (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)
    Tendsto (fun j => opNorm (evalU (U j) mΓ - hermPart (M0 j))) atTop (𝓝 0) := by
  intro mΓ M0
  have hFposR : (0 : ℝ) < (F.card : ℝ) := Nat.cast_pos.mpr hFpos
  have hinv_sum : Tendsto (fun j =>
      (2 : ℝ)⁻¹ * opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) +
      (4 * (F.card : ℝ))⁻¹ * ∑ g ∈ F,
        opNorm ((U j (g⁻¹ : Γ) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ)) atTop (𝓝 0) := by
    have h1 := (U_one_tendsto hUmul).const_mul (2 : ℝ)⁻¹
    have h2 : Tendsto (fun j =>
        ∑ g ∈ F, opNorm ((U j (g⁻¹ : Γ) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ))
        atTop (𝓝 (∑ _g ∈ F, (0 : ℝ))) :=
      tendsto_finsetSum F fun g _ => U_inv_tendsto hUmul (g : G)
    have h2' : Tendsto (fun j => (4 * (F.card : ℝ))⁻¹ *
        ∑ g ∈ F, opNorm ((U j (g⁻¹ : Γ) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ)) atTop (𝓝 0) := by
      simpa using h2.const_mul (4 * (F.card : ℝ))⁻¹
    simpa using h1.add h2'
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hinv_sum
  have heval : evalU (U j) mΓ =
      (2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
    simp only [mΓ, evalU_add, evalU_smul, evalU_single, evalU_finset_sum, one_smul]
  have h1 : evalU (U j) mΓ - M0 j =
      (2 : ℂ)⁻¹ • ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := by
    rw [heval]
    simp only [M0, smul_sub]
    abel
  have hsym_sum : ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) =
      ∑ g ∈ F, (U j (g⁻¹ : Γ) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
    refine Finset.sum_bij (fun g _ => g⁻¹) (fun g hg => hFsym g hg)
      (fun a _ b _ hab => inv_injective hab)
      (fun g hg => ⟨g⁻¹, hFsym g hg, inv_inv g⟩)
      (fun g _ => by simp)
  have h2 : M0 j - hermPart (M0 j) =
      ((4 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
        ((U j (g⁻¹ : Γ) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ) := by
    have hMH : (M0 j)ᴴ = (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ := by
      simp only [M0, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Matrix.conjTranspose_sum]
      have h2s : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
      have hFs : star ((2 * (F.card : ℂ))⁻¹) = (2 * (F.card : ℂ))⁻¹ := by simp
      rw [h2s, hFs]
    have hdiffM : M0 j - (M0 j)ᴴ = ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
        ((U j (g⁻¹ : Γ) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
          (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ) := by
      rw [hMH]
      have hstep : M0 j - ((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ) =
          ((2 * (F.card : ℂ))⁻¹) • (∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ) := by
        simp only [M0, smul_sub]
        abel
      rw [hstep, hsym_sum, Finset.sum_sub_distrib]
    have hhalf : M0 j - hermPart (M0 j) = (2 : ℂ)⁻¹ • (M0 j - (M0 j)ᴴ) := by
      unfold hermPart
      ext a b
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hhalf, hdiffM, smul_smul]
    congr 1
    ring
  have hsplit : evalU (U j) mΓ - hermPart (M0 j) = (evalU (U j) mΓ - M0 j) + (M0 j - hermPart (M0 j)) := by
    abel
  rw [hsplit]
  refine (opNorm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [h1, opNorm_smul]
    have h2n : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    rw [h2n]
  · rw [h2, opNorm_smul]
    have h4n : ‖(4 * (F.card : ℂ))⁻¹‖ = (4 * (F.card : ℝ))⁻¹ := by
      have : (4 * (F.card : ℂ))⁻¹ = (((4 * (F.card : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h4n]
    exact mul_le_mul_of_nonneg_left (opNorm_sum_le F _) (by positivity)

private lemma opNorm_M0_le_one {G : Type} [Group G] {Γ : Subgroup G}
    (F : Finset Γ) (hFpos : 0 < F.card) {m : ℕ}
    (U : G → Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm ((2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) +
      ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U (g : G) : Matrix (Fin m) (Fin m) ℂ)) ≤ 1 := by
  have hFposR : (0 : ℝ) < (F.card : ℝ) := Nat.cast_pos.mpr hFpos
  have h1 := opNorm_add_le
    ((2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ))
    (((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U (g : G) : Matrix (Fin m) (Fin m) ℂ))
  have h2 : opNorm ((2 : ℂ)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ)) ≤ (2 : ℝ)⁻¹ := by
    rw [opNorm_smul]
    have h2n : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    rw [h2n]
    calc (2 : ℝ)⁻¹ * opNorm (1 : Matrix (Fin m) (Fin m) ℂ) ≤ (2 : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left opNorm_one_le_one (by norm_num)
      _ = (2 : ℝ)⁻¹ := mul_one _
  have h3 : opNorm (((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U (g : G) : Matrix (Fin m) (Fin m) ℂ)) ≤
      (2 : ℝ)⁻¹ := by
    rw [opNorm_smul]
    have h2Fn : ‖(2 * (F.card : ℂ))⁻¹‖ = (2 * (F.card : ℝ))⁻¹ := by
      have : (2 * (F.card : ℂ))⁻¹ = (((2 * (F.card : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2Fn]
    have hsum : opNorm (∑ g ∈ F, (U (g : G) : Matrix (Fin m) (Fin m) ℂ)) ≤ (F.card : ℝ) := by
      calc opNorm (∑ g ∈ F, (U (g : G) : Matrix (Fin m) (Fin m) ℂ))
          ≤ ∑ g ∈ F, opNorm (U (g : G) : Matrix (Fin m) (Fin m) ℂ) := opNorm_sum_le F _
        _ ≤ ∑ _g ∈ F, (1 : ℝ) := Finset.sum_le_sum fun g _ => opNorm_unitary_le_one _
        _ = (F.card : ℝ) := by simp
    calc (2 * (F.card : ℝ))⁻¹ * opNorm (∑ g ∈ F, (U (g : G) : Matrix (Fin m) (Fin m) ℂ))
        ≤ (2 * (F.card : ℝ))⁻¹ * (F.card : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 : ℝ)⁻¹ := by field_simp [hFposR.ne']
  linarith

private lemma M_op_ultraRep_coe {G : Type} [Group G] {Γ : Subgroup G}
    (F : Finset Γ) {n : ℕ → ℕ} (U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ)
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (f : BVec n) :
    let M0 : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
      (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)
    ∃ Mf : BVec n,
      (∀ j, Mf.seq j = Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 j) (f.seq j)) ∧
      M_op F ((ultraRep U hUmul).comp Γ.subtype) (f : UniformSpace.Completion (BVec n)) =
        (Mf : UniformSpace.Completion (BVec n)) := by
  intro M0
  let Mf : BVec n := (2 : ℂ)⁻¹ • f + ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, actBVec U (g : G) f
  have hMf_seq : ∀ j, Mf.seq j = Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 j) (f.seq j) := by
    intro j
    have hsum_seq : ∀ (s : Finset Γ),
        (∑ g ∈ s, actBVec U (g : G) f).seq j =
          ∑ g ∈ s, Matrix.toEuclideanCLM (𝕜 := ℂ) (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) (f.seq j) := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (U j (a : G) : Matrix _ _ ℂ) (f.seq j) + ·) ih
    change (2 : ℂ)⁻¹ • f.seq j + ((2 * (F.card : ℂ))⁻¹) • (∑ g ∈ F, actBVec U (g : G) f).seq j = _
    rw [hsum_seq F]
    simp only [M0, map_add, map_smul, map_one, map_sum, _root_.add_apply,
      _root_.smul_apply, one_apply_eq_self, _root_.sum_apply]
  refine ⟨Mf, hMf_seq, ?_⟩
  rw [M_op_apply]
  have hcoe_sum : ∀ (s : Finset Γ),
      ∑ g ∈ s, ((ultraRep U hUmul).comp Γ.subtype) g (f : UniformSpace.Completion (BVec n)) =
        ((∑ g ∈ s, actBVec U (g : G) f : BVec n) : UniformSpace.Completion (BVec n)) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, UniformSpace.Completion.coe_add]
      congr 1
      exact ultraRep_coe U hUmul (a : G) f
  rw [hcoe_sum F, ← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_smul,
    ← UniformSpace.Completion.coe_add]

private lemma spec_gap_eventually {G : Type} [Group G] {Γ : Subgroup G}
    (F : Finset Γ) (hFpos : 0 < F.card) {κ : ℝ}
    (hKaz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (σ : Γ →* E ≃ₗᵢ[ℂ] E),
      (∀ w : E, (∀ g : Γ, σ g w = w) → w = 0) →
      ∀ w : E, κ ^ 2 * ‖w‖ ^ 2 ≤ ∑ g ∈ F, ‖σ g w - w‖ ^ 2)
    {n : ℕ → ℕ} {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (hM0_B_tendsto : Tendsto (fun j =>
      opNorm (((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)) -
        hermPart ((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ))))
      atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    let δ : ℝ := κ ^ 2 / (4 * (F.card : ℝ))
    let M0 : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
      (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)
    ∀ᶠ j in atTop, ∀ i : Fin (n j),
      (hermPart_isHermitian (M0 j)).eigenvalues i ≤ 1 - 3 * δ / 4 ∨
      1 - ε ≤ (hermPart_isHermitian (M0 j)).eigenvalues i := by
  intro δ M0
  by_contra hnot
  have hfreq : ∃ᶠ j in atTop, ∃ i : Fin (n j),
      1 - 3 * δ / 4 < (hermPart_isHermitian (M0 j)).eigenvalues i ∧
      (hermPart_isHermitian (M0 j)).eigenvalues i < 1 - ε := by
    rw [Filter.not_eventually] at hnot
    refine hnot.mono fun j hj => ?_
    push Not at hj
    exact hj
  obtain ⟨φ, hφ_mono, hφ_prop⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose idx hidx_gt hidx_lt using hφ_prop
  have hδ0 : 0 < δ := by
    have hlt : 1 - 3 * δ / 4 < 1 - ε := (hidx_gt 0).trans (hidx_lt 0)
    linarith
  let n' : ℕ → ℕ := fun k => n (φ k)
  let U' : ∀ k, G → Matrix.unitaryGroup (Fin (n' k)) ℂ := fun k g => U (φ k) g
  have hUmul' : ∀ g h, Tendsto (fun k => opDist (U' k (g * h)) (U' k g * U' k h)) atTop (𝓝 0) :=
    fun g h => (hUmul g h).comp hφ_mono.tendsto_atTop
  let wSeq : BVec n' := ⟨fun k => (hermPart_isHermitian (M0 (φ k))).eigenvectorBasis (idx k),
    ⟨1, fun k => by rw [(hermPart_isHermitian (M0 (φ k))).eigenvectorBasis.orthonormal.1 (idx k)]⟩⟩
  let lamSeq : ℕ → ℝ := fun k => (hermPart_isHermitian (M0 (φ k))).eigenvalues (idx k)
  have hlam_mem : ∀ k, lamSeq k ∈ Set.Icc (1 - 3 * δ / 4) (1 - ε) :=
    fun k => ⟨(hidx_gt k).le, (hidx_lt k).le⟩
  have hle_princ : ((Filter.hyperfilter ℕ).map lamSeq : Filter ℝ) ≤
      Filter.principal (Set.Icc (1 - 3 * δ / 4) (1 - ε)) :=
    Filter.tendsto_principal.mpr (Eventually.of_forall hlam_mem)
  obtain ⟨lam, hlam_Icc, hlam_tend⟩ :=
    (isCompact_Icc (a := 1 - 3 * δ / 4) (b := 1 - ε)).ultrafilter_le_nhds
      ((Filter.hyperfilter ℕ).map lamSeq) hle_princ
  have hlam_tend' : Tendsto lamSeq (Filter.hyperfilter ℕ) (𝓝 lam) := hlam_tend
  let H := UniformSpace.Completion (BVec n')
  let σ := (ultraRep U' hUmul').comp Γ.subtype
  let w : H := (wSeq : H)
  have hnorm_w : ‖w‖ = 1 := by
    rw [UniformSpace.Completion.norm_coe]
    have hsq1 := BVec.tendsto_norm_sq wSeq
    have hsq2 : Tendsto (fun k => ‖wSeq.seq k‖ ^ 2) (Filter.hyperfilter ℕ) (𝓝 1) := by
      have heq : (fun k => ‖wSeq.seq k‖ ^ 2) = fun _ => (1 : ℝ) := by
        funext k; simp [wSeq, (hermPart_isHermitian (M0 (φ k))).eigenvectorBasis.orthonormal.1 (idx k)]
      rw [heq]; exact tendsto_const_nhds
    have h1 : ‖wSeq‖ ^ 2 = 1 := tendsto_nhds_unique hsq1 hsq2
    nlinarith [norm_nonneg wSeq]
  obtain ⟨Mf, hMf_seq, hMf_coe⟩ := M_op_ultraRep_coe F U' hUmul' wSeq
  have heig_eq : M_op F σ w = (lam : ℂ) • w := by
    rw [hMf_coe, ← UniformSpace.Completion.coe_smul]
    apply BVec.coe_eq_of_norm_sub_eq_zero
    apply BVec.norm_eq_zero_of_tendsto_zero_hyper
    have ht1 : Tendsto (fun k => opNorm (M0 (φ k) - hermPart (M0 (φ k)))) (Filter.hyperfilter ℕ) (𝓝 0) :=
      (hM0_B_tendsto.comp hφ_mono.tendsto_atTop).mono_left hyperfilter_le_atTop
    have ht2 : Tendsto (fun k => |lamSeq k - lam|) (Filter.hyperfilter ℕ) (𝓝 0) := by
      have hsub : Tendsto (fun k => lamSeq k - lam) (Filter.hyperfilter ℕ) (𝓝 (lam - lam)) :=
        hlam_tend'.sub tendsto_const_nhds
      rw [sub_self] at hsub
      have habs := (continuous_abs.continuousAt (x := 0)).tendsto.comp hsub
      rw [abs_zero] at habs
      exact habs
    have hsum : Tendsto (fun k => opNorm (M0 (φ k) - hermPart (M0 (φ k))) + |lamSeq k - lam|)
        (Filter.hyperfilter ℕ) (𝓝 0) := by
      simpa using ht1.add ht2
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hsum
    have hseq : (Mf - (lam : ℂ) • wSeq).seq k =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k) - hermPart (M0 (φ k))) (wSeq.seq k) +
          ((lamSeq k - lam : ℝ) : ℂ) • wSeq.seq k := by
      change Mf.seq k - (lam : ℂ) • wSeq.seq k = _
      rw [hMf_seq k, toEuclideanCLM_sub_apply]
      have hBw : Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart (M0 (φ k))) (wSeq.seq k) =
          (lamSeq k : ℂ) • wSeq.seq k :=
        hermitian_apply_eigenvector (hermPart_isHermitian (M0 (φ k))) (idx k)
      rw [hBw, Complex.ofReal_sub, sub_smul]
      abel
    rw [hseq]
    have hw1 : ‖wSeq.seq k‖ = 1 := (hermPart_isHermitian (M0 (φ k))).eigenvectorBasis.orthonormal.1 (idx k)
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k) - hermPart (M0 (φ k))) (wSeq.seq k) +
            ((lamSeq k - lam : ℝ) : ℂ) • wSeq.seq k‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k) - hermPart (M0 (φ k))) (wSeq.seq k)‖ +
            ‖((lamSeq k - lam : ℝ) : ℂ) • wSeq.seq k‖ := norm_add_le _ _
      _ ≤ opNorm (M0 (φ k) - hermPart (M0 (φ k))) * ‖wSeq.seq k‖ +
            ‖((lamSeq k - lam : ℝ) : ℂ)‖ * ‖wSeq.seq k‖ := by
          refine add_le_add (ContinuousLinearMap.le_opNorm _ _) ?_
          rw [norm_smul]
      _ = opNorm (M0 (φ k) - hermPart (M0 (φ k))) + |lamSeq k - lam| := by
          rw [hw1, mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hw0 := M_op_no_eigenvalue_in_gap F hFpos hKaz σ
    (by linarith [hlam_Icc.1]) (by linarith [hlam_Icc.2]) heig_eq
  rw [hw0, norm_zero] at hnorm_w
  norm_num at hnorm_w

private lemma opNorm_unitary_sub_one_mul_P_tendsto {G : Type} [Group G] {Γ : Subgroup G}
    (F : Finset Γ) (hFpos : 0 < F.card) {κ : ℝ} (hκ0 : 0 < κ)
    (hKaz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (σ : Γ →* E ≃ₗᵢ[ℂ] E),
      (∀ w : E, (∀ g : Γ, σ g w = w) → w = 0) →
      ∀ w : E, κ ^ 2 * ‖w‖ ^ 2 ≤ ∑ g ∈ F, ‖σ g w - w‖ ^ 2)
    {n : ℕ → ℕ} {U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ}
    (hUmul : ∀ g h, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0))
    (hM0_B_tendsto : Tendsto (fun j =>
      opNorm (((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)) -
        hermPart ((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ))))
      atTop (𝓝 0))
    (hBP_tendsto : Tendsto (fun j =>
      opNorm ((hermPart ((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)) - 1) *
        highProj (hermPart_isHermitian ((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)))
          (1 - κ ^ 2 / (4 * (F.card : ℝ)) / 2))) atTop (𝓝 0))
    (g : Γ) :
    let M0 : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
      (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)
    let P : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
      highProj (hermPart_isHermitian (M0 j)) (1 - κ ^ 2 / (4 * (F.card : ℝ)) / 2)
    Tendsto (fun j => opNorm (((U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j))
      atTop (𝓝 0) := by
  intro M0 P
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨η, hη, hfreq_raw⟩ := hnot
  have hfreq : ∃ᶠ j in atTop, η ≤ opNorm (((U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j) := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨j, hj, hge⟩ := hfreq_raw N
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (opNorm_nonneg _)] at hge
    exact ⟨j, hj, hge⟩
  obtain ⟨φ, hφ_mono, hφ_prop⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hex_u : ∀ k, ∃ u : EuclideanSpace ℂ (Fin (n (φ k))), ‖u‖ ≤ 1 ∧
      η / 2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (((U (φ k) (g : G) : Matrix (Fin (n (φ k))) (Fin (n (φ k))) ℂ) - 1) * P (φ k)) u‖ := by
    intro k
    by_contra hno
    push Not at hno
    have hle : opNorm (((U (φ k) (g : G) : Matrix (Fin (n (φ k))) (Fin (n (φ k))) ℂ) - 1) * P (φ k)) ≤ η / 2 := by
      unfold opNorm
      refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun x => ?_
      by_cases hx : x = 0
      · subst hx; simp
      · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let x1 := ((‖x‖⁻¹ : ℝ) : ℂ) • x
        have hx1 : ‖x1‖ ≤ 1 := by
          simp only [x1, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hxn.le),
            inv_mul_cancel₀ hxn.ne', le_refl]
        have hlt := hno x1 hx1
        rw [map_smul, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.mpr hxn.le)] at hlt
        have hmul := mul_le_mul_of_nonneg_left hlt.le hxn.le
        rw [← mul_assoc, mul_inv_cancel₀ hxn.ne', one_mul, mul_comm] at hmul
        exact hmul
    linarith [hφ_prop k]
  choose u hu1 hu_lb using hex_u
  let n' : ℕ → ℕ := fun k => n (φ k)
  let U' : ∀ k, G → Matrix.unitaryGroup (Fin (n' k)) ℂ := fun k h => U (φ k) h
  have hUmul' : ∀ a b, Tendsto (fun k => opDist (U' k (a * b)) (U' k a * U' k b)) atTop (𝓝 0) :=
    fun a b => (hUmul a b).comp hφ_mono.tendsto_atTop
  have hw_bd : ∀ k, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (P (φ k)) (u k)‖ ≤ 1 := fun k => by
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (P (φ k)) (u k)‖
        ≤ opNorm (P (φ k)) * ‖u k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * 1 := mul_le_mul (opNorm_highProj_le_one _ _) (hu1 k) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  let wSeq : BVec n' := ⟨fun k => Matrix.toEuclideanCLM (𝕜 := ℂ) (P (φ k)) (u k), ⟨1, hw_bd⟩⟩
  let H := UniformSpace.Completion (BVec n')
  let σ := (ultraRep U' hUmul').comp Γ.subtype
  let w : H := (wSeq : H)
  obtain ⟨Mf, hMf_seq, hMf_coe⟩ := M_op_ultraRep_coe F U' hUmul' wSeq
  have hMw : M_op F σ w = w := by
    rw [hMf_coe]
    apply BVec.coe_eq_of_norm_sub_eq_zero
    apply BVec.norm_eq_zero_of_tendsto_zero
    have hsum : Tendsto (fun k =>
        opNorm (M0 (φ k) - hermPart (M0 (φ k))) + opNorm ((hermPart (M0 (φ k)) - 1) * P (φ k)))
        atTop (𝓝 0) := by
      have h1 := (hM0_B_tendsto.comp hφ_mono.tendsto_atTop).add (hBP_tendsto.comp hφ_mono.tendsto_atTop)
      rw [add_zero] at h1
      exact h1
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hsum
    have hseq : (Mf - wSeq).seq k =
        Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k) - hermPart (M0 (φ k))) (wSeq.seq k) +
          Matrix.toEuclideanCLM (𝕜 := ℂ) ((hermPart (M0 (φ k)) - 1) * P (φ k)) (u k) := by
      change Mf.seq k - wSeq.seq k = _
      rw [hMf_seq k, toEuclideanCLM_mul_apply (hermPart (M0 (φ k)) - 1) (P (φ k)),
        toEuclideanCLM_sub_apply, toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply]
      change Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k)) (wSeq.seq k) - wSeq.seq k =
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k)) (wSeq.seq k) -
          Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart (M0 (φ k))) (wSeq.seq k)) +
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (hermPart (M0 (φ k))) (wSeq.seq k) - wSeq.seq k)
      abel
    rw [hseq]
    calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k) - hermPart (M0 (φ k))) (wSeq.seq k) +
            Matrix.toEuclideanCLM (𝕜 := ℂ) ((hermPart (M0 (φ k)) - 1) * P (φ k)) (u k)‖
        ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (M0 (φ k) - hermPart (M0 (φ k))) (wSeq.seq k)‖ +
            ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((hermPart (M0 (φ k)) - 1) * P (φ k)) (u k)‖ := norm_add_le _ _
      _ ≤ opNorm (M0 (φ k) - hermPart (M0 (φ k))) * ‖wSeq.seq k‖ +
            opNorm ((hermPart (M0 (φ k)) - 1) * P (φ k)) * ‖u k‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ opNorm (M0 (φ k) - hermPart (M0 (φ k))) * 1 +
            opNorm ((hermPart (M0 (φ k)) - 1) * P (φ k)) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hw_bd k) (opNorm_nonneg _))
            (mul_le_mul_of_nonneg_left (hu1 k) (opNorm_nonneg _))
      _ = opNorm (M0 (φ k) - hermPart (M0 (φ k))) +
            opNorm ((hermPart (M0 (φ k)) - 1) * P (φ k)) := by ring
  have hgw : σ g w = w := M_op_fixed_implies_invariant F hFpos hκ0 hKaz σ hMw g
  have hnorm0 : ‖actBVec U' (g : G) wSeq - wSeq‖ = 0 := by
    rw [← UniformSpace.Completion.norm_coe, UniformSpace.Completion.coe_sub,
      ← ultraRep_coe U' hUmul' (g : G) wSeq]
    change ‖σ g w - w‖ = 0
    rw [hgw, sub_self, norm_zero]
  have ht0 := BVec.tendsto_norm_sq (actBVec U' (g : G) wSeq - wSeq)
  rw [hnorm0, zero_pow two_ne_zero] at ht0
  have hlb : ∀ k, (η / 2) ^ 2 ≤ ‖(actBVec U' (g : G) wSeq - wSeq).seq k‖ ^ 2 := by
    intro k
    have hseq : (actBVec U' (g : G) wSeq - wSeq).seq k =
        Matrix.toEuclideanCLM (𝕜 := ℂ)
          (((U (φ k) (g : G) : Matrix (Fin (n (φ k))) (Fin (n (φ k))) ℂ) - 1) * P (φ k)) (u k) := by
      rw [toEuclideanCLM_mul_apply ((U (φ k) (g : G) : Matrix (Fin (n (φ k))) (Fin (n (φ k))) ℂ) - 1) (P (φ k)),
        toEuclideanCLM_sub_apply, toEuclideanCLM_one_apply]
      rfl
    rw [hseq]
    exact pow_le_pow_left₀ (by linarith) (hu_lb k) 2
  have hge0 : (η / 2) ^ 2 ≤ 0 := ge_of_tendsto' ht0 hlb
  nlinarith

private lemma opNorm_avg_unitary_le_one {G ι : Type} {m : ℕ} (F : Finset ι) (hFpos : 0 < F.card)
    (U : G → Matrix.unitaryGroup (Fin m) ℂ) (g0 : G) (f : ι → G) :
    opNorm ((2 : ℂ)⁻¹ • (U g0 : Matrix (Fin m) (Fin m) ℂ) +
      ((2 * (F.card : ℂ))⁻¹) • ∑ i ∈ F, (U (f i) : Matrix (Fin m) (Fin m) ℂ)) ≤ 1 := by
  have hFposR : (0 : ℝ) < (F.card : ℝ) := Nat.cast_pos.mpr hFpos
  have h1 := opNorm_add_le
    ((2 : ℂ)⁻¹ • (U g0 : Matrix (Fin m) (Fin m) ℂ))
    (((2 * (F.card : ℂ))⁻¹) • ∑ i ∈ F, (U (f i) : Matrix (Fin m) (Fin m) ℂ))
  have h2 : opNorm ((2 : ℂ)⁻¹ • (U g0 : Matrix (Fin m) (Fin m) ℂ)) ≤ (2 : ℝ)⁻¹ := by
    rw [opNorm_smul]
    have h2n : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    rw [h2n]
    calc (2 : ℝ)⁻¹ * opNorm (U g0 : Matrix (Fin m) (Fin m) ℂ) ≤ (2 : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (opNorm_unitary_le_one (U g0)) (by norm_num)
      _ = (2 : ℝ)⁻¹ := mul_one _
  have h3 : opNorm (((2 * (F.card : ℂ))⁻¹) • ∑ i ∈ F, (U (f i) : Matrix (Fin m) (Fin m) ℂ)) ≤
      (2 : ℝ)⁻¹ := by
    rw [opNorm_smul]
    have h2Fn : ‖(2 * (F.card : ℂ))⁻¹‖ = (2 * (F.card : ℝ))⁻¹ := by
      have : (2 * (F.card : ℂ))⁻¹ = (((2 * (F.card : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2Fn]
    have hsum : opNorm (∑ i ∈ F, (U (f i) : Matrix (Fin m) (Fin m) ℂ)) ≤ (F.card : ℝ) := by
      calc opNorm (∑ i ∈ F, (U (f i) : Matrix (Fin m) (Fin m) ℂ))
          ≤ ∑ i ∈ F, opNorm (U (f i) : Matrix (Fin m) (Fin m) ℂ) := opNorm_sum_le F _
        _ ≤ ∑ _i ∈ F, (1 : ℝ) := Finset.sum_le_sum fun i _ => opNorm_unitary_le_one (U (f i))
        _ = (F.card : ℝ) := by simp
    calc (2 * (F.card : ℝ))⁻¹ * opNorm (∑ i ∈ F, (U (f i) : Matrix (Fin m) (Fin m) ℂ))
        ≤ (2 * (F.card : ℝ))⁻¹ * (F.card : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2 : ℝ)⁻¹ := by field_simp [hFposR.ne']
  linarith

private theorem kazhdan_proj_proof :
    OMA.R_Green100_green_100_variants_operator_norm_R1.H3 := by
  classical
  intro G _ _ Γ hFH t hconj E _ _ _ ρ ⟨n, U, hUmul, hdom⟩ v hv
  obtain ⟨F, κ, hF1, hFsym, hκ0, hκ1, hKaz⟩ := exists_kazhdan_pair_of_FH hFH
  have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨1, hF1⟩
  have hFposR : (0 : ℝ) < (F.card : ℝ) := Nat.cast_pos.mpr hFpos
  set δ : ℝ := κ ^ 2 / (4 * (F.card : ℝ))
  have hδ0 : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 4 := by
    have hκsq : κ ^ 2 ≤ 1 := by nlinarith
    have hFge1 : (1 : ℝ) ≤ (F.card : ℝ) := Nat.one_le_cast.mpr hFpos
    rw [show δ = κ ^ 2 / (4 * (F.card : ℝ)) from rfl, div_le_iff₀ (by positivity)]
    nlinarith
  let mΓ : G →₀ ℂ := (2 : ℂ)⁻¹ • Finsupp.single (1 : G) 1 +
    ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, Finsupp.single (g : G) 1
  let mConj : G →₀ ℂ := (2 : ℂ)⁻¹ • Finsupp.single (1 : G) 1 +
    ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, Finsupp.single (t * (g : G) * t⁻¹) 1
  let M0 : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
    (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
      ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)
  let B : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j => hermPart (M0 j)
  let hB : ∀ j, (B j).IsHermitian := fun j => hermPart_isHermitian (M0 j)
  let P : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j => highProj (hB j) (1 - δ / 2)
  let Cmat : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
    (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * B j * (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ
  let Q : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℂ := fun j =>
    (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * P j * (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ
  have hB_eig_Icc : ∀ j (i : Fin (n j)),
      0 ≤ (hB j).eigenvalues i ∧ (hB j).eigenvalues i ≤ 1 := by
    intro j i
    let A : Matrix (Fin (n j)) (Fin (n j)) ℂ :=
      ((F.card : ℂ)⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)
    have hA1 : opNorm A ≤ 1 := by
      simp only [A, opNorm_smul]
      have hFn : ‖(F.card : ℂ)⁻¹‖ = (F.card : ℝ)⁻¹ := by
        have : (F.card : ℂ)⁻¹ = (((F.card : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hFn]
      have hsum : opNorm (∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ)) ≤ (F.card : ℝ) := by
        calc opNorm (∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ))
            ≤ ∑ g ∈ F, opNorm (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := opNorm_sum_le F _
          _ ≤ ∑ _g ∈ F, (1 : ℝ) := Finset.sum_le_sum fun g _ => opNorm_unitary_le_one _
          _ = (F.card : ℝ) := by simp
      calc (F.card : ℝ)⁻¹ * opNorm (∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ))
          ≤ (F.card : ℝ)⁻¹ * (F.card : ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 := inv_mul_cancel₀ hFposR.ne'
    have hM0_eq : M0 j = (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) + (2 : ℂ)⁻¹ • A := by
      simp only [M0, A, smul_smul]
      congr 2; ring
    have heig := eigenvalue_mem_Icc_of_hermPart A hA1 i
    simpa only [B, hB, hM0_eq] using heig
  have hMΓ_B_tendsto : Tendsto (fun j => opNorm (evalU (U j) mΓ - B j)) atTop (𝓝 0) :=
    avg_hermPart_diff_tendsto F hFpos hFsym hUmul
  have hM0_B_tendsto : Tendsto (fun j => opNorm (M0 j - B j)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun j => opNorm (evalU (U j) mΓ - B j) +
        (2 : ℝ)⁻¹ * opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1)) atTop (𝓝 0) := by
      simpa using hMΓ_B_tendsto.add ((U_one_tendsto hUmul).const_mul (2 : ℝ)⁻¹)
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
    have heval : evalU (U j) mΓ - M0 j =
        (2 : ℂ)⁻¹ • ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := by
      simp only [mΓ, M0, evalU_add, evalU_smul, evalU_single, evalU_finset_sum, one_smul, smul_sub]
      abel
    have hsplit : M0 j - B j = (evalU (U j) mΓ - B j) - (evalU (U j) mΓ - M0 j) := by abel
    rw [hsplit]
    have hle := opNorm_sub_le (evalU (U j) mΓ - B j) (evalU (U j) mΓ - M0 j)
    have hrhs : opNorm (evalU (U j) mΓ - M0 j) =
        (2 : ℝ)⁻¹ * opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := by
      rw [heval, opNorm_smul]
      have h2n : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
      rw [h2n]
    linarith
  have hspec_gap : ∀ ε > 0, ∀ᶠ j in atTop, ∀ i : Fin (n j),
      (hB j).eigenvalues i ≤ 1 - 3 * δ / 4 ∨ 1 - ε ≤ (hB j).eigenvalues i :=
    fun _ hε => spec_gap_eventually F hFpos hKaz hUmul hM0_B_tendsto hε
  have hBP_tendsto : Tendsto (fun j => opNorm ((B j - 1) * P j)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let ε' : ℝ := min (ε / 2) (δ / 4)
    have hε'0 : 0 < ε' := lt_min (half_pos hε) (by linarith)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hspec_gap ε' hε'0)
    refine ⟨N, fun j hj => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (opNorm_nonneg _)]
    have hle : opNorm ((B j - 1) * P j) ≤ ε' := by
      refine opNorm_sub_one_mul_highProj_le (hB j) (1 - δ / 2) ε' hε'0.le fun i hi => ?_
      have hcase := hN j hj i
      have hge : 1 - ε' ≤ (hB j).eigenvalues i := by
        rcases hcase with hlo | hhi
        · linarith
        · exact hhi
      have hle1 : (hB j).eigenvalues i ≤ 1 := (hB_eig_Icc j i).2
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hε'lt : ε' < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
    exact hle.trans_lt hε'lt
  have hUP_tendsto : ∀ g : Γ,
      Tendsto (fun j => opNorm (((U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j))
        atTop (𝓝 0) :=
    fun g => opNorm_unitary_sub_one_mul_P_tendsto F hFpos hκ0 hKaz hUmul hM0_B_tendsto hBP_tendsto g
  have hmConj_C_tendsto : Tendsto (fun j => opNorm (evalU (U j) mConj - Cmat j)) atTop (𝓝 0) := by
    have hconj_sum : Tendsto (fun j =>
        (2 : ℝ)⁻¹ * opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) +
        (2 * (F.card : ℝ))⁻¹ * ∑ g ∈ F,
          opNorm ((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
              (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ) +
        opNorm (M0 j - B j)) atTop (𝓝 0) := by
      have h1 := (U_one_tendsto hUmul).const_mul (2 : ℝ)⁻¹
      have h2 : Tendsto (fun j =>
          ∑ g ∈ F, opNorm ((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
              (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ))
          atTop (𝓝 (∑ _g ∈ F, (0 : ℝ))) :=
        tendsto_finsetSum F fun g _ => U_conj_tendsto hUmul t (g : G)
      have h2' : Tendsto (fun j => (2 * (F.card : ℝ))⁻¹ *
          ∑ g ∈ F, opNorm ((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
              (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ)) atTop (𝓝 0) := by
        simpa using h2.const_mul (2 * (F.card : ℝ))⁻¹
      simpa using (h1.add h2').add hM0_B_tendsto
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hconj_sum
    have hu : (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
        (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (U j t).2
    let C0 : Matrix (Fin (n j)) (Fin (n j)) ℂ :=
      (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * M0 j * (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ
    have hC0_eq : C0 = (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
          (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
            (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ := by
      simp only [C0, M0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hu, Finset.mul_sum, Finset.sum_mul]
    have heval : evalU (U j) mConj =
        (2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
            (U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
      simp only [mConj, evalU_add, evalU_smul, evalU_single, evalU_finset_sum, one_smul]
    have hsplit : evalU (U j) mConj - Cmat j = (evalU (U j) mConj - C0) + (C0 - Cmat j) := by abel
    rw [hsplit]
    have h1 : evalU (U j) mConj - C0 =
        (2 : ℂ)⁻¹ • ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) +
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
          ((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
              (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ) := by
      rw [heval, hC0_eq, Finset.sum_sub_distrib, smul_sub, smul_sub]
      abel
    have h2 : opNorm (C0 - Cmat j) = opNorm (M0 j - B j) := by
      have heq : C0 - Cmat j = (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (M0 j - B j) *
          (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ := by
        simp only [C0, Cmat, Matrix.mul_sub, Matrix.sub_mul]
      rw [heq]
      exact opNorm_conj_unitary (U j t) (M0 j - B j)
    refine (opNorm_add_le _ _).trans (add_le_add ?_ h2.le)
    rw [h1]
    refine (opNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [opNorm_smul]
      have h2n : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
      rw [h2n]
    · rw [opNorm_smul]
      have h2Fn : ‖(2 * (F.card : ℂ))⁻¹‖ = (2 * (F.card : ℝ))⁻¹ := by
        have : (2 * (F.card : ℂ))⁻¹ = (((2 * (F.card : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [h2Fn]
      exact mul_le_mul_of_nonneg_left (opNorm_sum_le F _) (by positivity)
  have h1CP_tendsto : Tendsto (fun j => opNorm ((1 - Cmat j) * P j)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun j =>
        (2 : ℝ)⁻¹ * opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) +
        (2 * (F.card : ℝ))⁻¹ * ∑ g ∈ F,
          opNorm (((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j) +
        opNorm (evalU (U j) mConj - Cmat j)) atTop (𝓝 0) := by
      have h1 := (U_one_tendsto hUmul).const_mul (2 : ℝ)⁻¹
      have h2 : Tendsto (fun j =>
          ∑ g ∈ F, opNorm (((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j))
          atTop (𝓝 (∑ _g ∈ F, (0 : ℝ))) :=
        tendsto_finsetSum F fun g _ => hUP_tendsto ⟨t * (g : G) * t⁻¹, hconj (g : G) g.2⟩
      have h2' : Tendsto (fun j => (2 * (F.card : ℝ))⁻¹ *
          ∑ g ∈ F, opNorm (((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j))
          atTop (𝓝 0) := by
        simpa using h2.const_mul (2 * (F.card : ℝ))⁻¹
      simpa using (h1.add h2').add hmConj_C_tendsto
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
    have hsplit : (1 - Cmat j) * P j =
        (1 - evalU (U j) mConj) * P j + (evalU (U j) mConj - Cmat j) * P j := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul]
      abel
    have h1mConj : 1 - evalU (U j) mConj =
        -((2 : ℂ)⁻¹ • ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1)) -
        ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
          ((U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := by
      have heval : evalU (U j) mConj =
          (2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
            ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
              (U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
        simp only [mConj, evalU_add, evalU_smul, evalU_single, evalU_finset_sum, one_smul]
      have hsum1 : ∑ _g ∈ F, (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) =
          (F.card : ℂ) • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
        rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
      have hcomb : (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ((F.card : ℂ) • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)) =
          (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
        rw [smul_smul, ← add_smul]
        have hFne : (F.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hFpos.ne'
        have hc : (2 : ℂ)⁻¹ + (2 * (F.card : ℂ))⁻¹ * (F.card : ℂ) = 1 := by
          field_simp [hFne]; ring
        rw [hc, one_smul]
      rw [heval, Finset.sum_sub_distrib, hsum1, smul_sub, smul_sub]
      calc (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
            ((2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
              ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
                (U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ))
          = ((2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
              ((2 * (F.card : ℂ))⁻¹) • ((F.card : ℂ) • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ))) -
            ((2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
              ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
                (U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ)) := by rw [hcomb]
        _ = -((2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
              (2 : ℂ)⁻¹ • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ)) -
            (((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
                (U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) -
              ((2 * (F.card : ℂ))⁻¹) • ((F.card : ℂ) • (1 : Matrix (Fin (n j)) (Fin (n j)) ℂ))) := by abel
    rw [hsplit]
    refine (opNorm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [h1mConj, Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.smul_mul, Finset.sum_mul]
      refine (opNorm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [opNorm_neg, opNorm_smul]
        have h2n : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
        rw [h2n]
        have hmulP : opNorm (((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j) ≤
            opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := by
          calc opNorm (((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * P j)
              ≤ opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * opNorm (P j) :=
                opNorm_mul_le _ _
            _ ≤ opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) * 1 :=
                mul_le_mul_of_nonneg_left (opNorm_highProj_le_one _ _) (opNorm_nonneg _)
            _ = opNorm ((U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) - 1) := mul_one _
        exact mul_le_mul_of_nonneg_left hmulP (by norm_num)
      · rw [opNorm_smul]
        have h2Fn : ‖(2 * (F.card : ℂ))⁻¹‖ = (2 * (F.card : ℝ))⁻¹ := by
          have : (2 * (F.card : ℂ))⁻¹ = (((2 * (F.card : ℝ))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        rw [h2Fn]
        exact mul_le_mul_of_nonneg_left (opNorm_sum_le F _) (by positivity)
    · calc opNorm ((evalU (U j) mConj - Cmat j) * P j)
          ≤ opNorm (evalU (U j) mConj - Cmat j) * opNorm (P j) := opNorm_mul_le _ _
        _ ≤ opNorm (evalU (U j) mConj - Cmat j) * 1 :=
            mul_le_mul_of_nonneg_left (opNorm_highProj_le_one _ _) (opNorm_nonneg _)
        _ = opNorm (evalU (U j) mConj - Cmat j) := mul_one _
  have h1QP_tendsto : Tendsto (fun j => opNorm ((1 - Q j) * P j)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun j => (1 - (1 - δ / 2))⁻¹ * opNorm ((1 - Cmat j) * P j)) atTop (𝓝 0) := by
      simpa using h1CP_tendsto.const_mul (1 - (1 - δ / 2))⁻¹
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) h0
    have hu : (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) *
        (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (U j t).2
    set Ut : Matrix (Fin (n j)) (Fin (n j)) ℂ := (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)
    have h1Q : (1 - Q j) * P j = Ut * ((1 - P j) * (Utᴴ * P j)) := by
      have h1 : (1 - Q j) * P j = P j - Ut * (P j * (Utᴴ * P j)) := by
        simp only [Q, Ut, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      have h2 : Ut * ((1 - P j) * (Utᴴ * P j)) = P j - Ut * (P j * (Utᴴ * P j)) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
        rw [← Matrix.mul_assoc Ut Utᴴ, hu, Matrix.one_mul]
      rw [h1, h2]
    have h1C : (1 - Cmat j) * P j = Ut * ((1 - B j) * (Utᴴ * P j)) := by
      have h1 : (1 - Cmat j) * P j = P j - Ut * (B j * (Utᴴ * P j)) := by
        simp only [Cmat, Ut, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      have h2 : Ut * ((1 - B j) * (Utᴴ * P j)) = P j - Ut * (B j * (Utᴴ * P j)) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
        rw [← Matrix.mul_assoc Ut Utᴴ, hu, Matrix.one_mul]
      rw [h1, h2]
    rw [h1Q, opNorm_mul_unitary_left (U j t), h1C, opNorm_mul_unitary_left (U j t)]
    exact opNorm_one_sub_highProj_mul_le (hB j) (1 - δ / 2) (by linarith) _
  have hPQ_tendsto : Tendsto (fun j => opNorm (P j - Q j)) atTop (𝓝 0) := by
    have hlt1 : ∀ᶠ j in atTop, opNorm ((1 - Q j) * P j) < 1 :=
      h1QP_tendsto.eventually (Iio_mem_nhds zero_lt_one)
    have hcont : Tendsto (fun x : ℝ => x + x / (1 - x)) (𝓝 0) (𝓝 0) := by
      have hsub : ContinuousAt (fun x : ℝ => x + x / (1 - x)) 0 := by
        refine continuousAt_id.add (continuousAt_id.div (continuousAt_const.sub continuousAt_id) ?_)
        norm_num
      simpa using hsub.tendsto
    have hrhs : Tendsto (fun j => opNorm ((1 - Q j) * P j) +
        opNorm ((1 - Q j) * P j) / (1 - opNorm ((1 - Q j) * P j))) atTop (𝓝 0) :=
      hcont.comp h1QP_tendsto
    refine squeeze_zero' (Eventually.of_forall fun j => opNorm_nonneg _) ?_ hrhs
    filter_upwards [hlt1] with j hlt
    exact opNorm_proj_sub_conj_le (P j) (highProj_isHermitian _ _) (highProj_mul_self _ _)
      (opNorm_highProj_le_one _ _) (opNorm_one_sub_highProj_le_one _ _) (U j t) hlt
  have hB1 : ∀ j, opNorm (B j) ≤ 1 := fun j =>
    (opNorm_hermPart_le (M0 j)).trans (opNorm_M0_le_one F hFpos (U j))
  have hC1 : ∀ j, opNorm (Cmat j) ≤ 1 := fun j => by
    rw [show opNorm (Cmat j) = opNorm (B j) from opNorm_conj_unitary (U j t) (B j)]
    exact hB1 j
  have hmΓ1 : ∀ j, opNorm (evalU (U j) mΓ) ≤ 1 := fun j => by
    have heval : evalU (U j) mΓ =
        (2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, (U j (g : G) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
      simp only [mΓ, evalU_add, evalU_smul, evalU_single, evalU_finset_sum, one_smul]
    rw [heval]
    exact opNorm_avg_unitary_le_one F hFpos (U j) 1 (fun g : Γ => (g : G))
  have hmConj1 : ∀ j, opNorm (evalU (U j) mConj) ≤ 1 := fun j => by
    have heval : evalU (U j) mConj =
        (2 : ℂ)⁻¹ • (U j 1 : Matrix (Fin (n j)) (Fin (n j)) ℂ) +
          ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F,
            (U j (t * (g : G) * t⁻¹) : Matrix (Fin (n j)) (Fin (n j)) ℂ) := by
      simp only [mConj, evalU_add, evalU_smul, evalU_single, evalU_finset_sum, one_smul]
    rw [heval]
    exact opNorm_avg_unitary_le_one F hFpos (U j) 1 (fun g : Γ => t * (g : G) * t⁻¹)
  have heval_mΓ : ∀ w : E, evalρ ρ mΓ w = M_op F (ρ.comp Γ.subtype) w := by
    intro w
    simp only [mΓ, evalρ_add, evalρ_smul, evalρ_single, evalρ_finset_sum, one_smul, map_one,
      M_op_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rfl
  have heval_mConj_v : evalρ ρ mConj v = v := by
    simp only [mConj, evalρ_add, evalρ_smul, evalρ_single, evalρ_finset_sum, one_smul, map_one]
    change (2 : ℂ)⁻¹ • v + ((2 * (F.card : ℂ))⁻¹) • ∑ g ∈ F, ρ (t * (g : G) * t⁻¹) v = v
    have hsum : ∑ g ∈ F, ρ (t * (g : G) * t⁻¹) v = (F.card : ℂ) • v := by
      calc ∑ g ∈ F, ρ (t * (g : G) * t⁻¹) v = ∑ _g ∈ F, v := Finset.sum_congr rfl fun g _ => hv (g : G) g.2
        _ = F.card • v := Finset.sum_const _
        _ = (F.card : ℂ) • v := by rw [Nat.cast_smul_eq_nsmul]
    rw [hsum, smul_smul, ← add_smul]
    have hFne : (F.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hFpos.ne'
    have hc : (2 : ℂ)⁻¹ + (2 * (F.card : ℂ))⁻¹ * (F.card : ℂ) = 1 := by field_simp [hFne]; ring
    rw [hc, one_smul]
  have heval_mConj_pow_v : ∀ k : ℕ, evalρ ρ (gpow mConj k) v = v := by
    intro k
    rw [evalρ_gpow]
    induction k with
    | zero => rfl
    | succ r ihr => rw [Function.iterate_succ_apply', ihr, heval_mConj_v]
  have hiter_bd : ∀ k : ℕ, ‖(M_op F (ρ.comp Γ.subtype))^[k] v - v‖ ≤
      2 * (1 - 3 * δ / 4) ^ k * ‖v‖ := by
    intro k
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hpos_r : 0 < (1 - 3 * δ / 4) ^ k := pow_pos (by linarith) k
    have hcont_eps : Tendsto (fun x : ℝ => 1 - (1 - x) ^ k) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun x : ℝ => 1 - (1 - x) ^ k) :=
        continuous_const.sub ((continuous_const.sub continuous_id).pow k)
      simpa using hc.continuousAt (x := 0) |>.tendsto
    have hnhds : ∀ᶠ x in 𝓝 (0 : ℝ), 1 - (1 - x) ^ k < (1 - 3 * δ / 4) ^ k :=
      hcont_eps.eventually (Iio_mem_nhds hpos_r)
    rw [Metric.eventually_nhds_iff] at hnhds
    obtain ⟨r₀, hr₀, hr₀_prop⟩ := hnhds
    let ε : ℝ := min (r₀ / 2) (δ / 4)
    have hε0 : 0 < ε := lt_min (half_pos hr₀) (by linarith)
    have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by linarith)
    have hε_lt : 1 - (1 - ε) ^ k < (1 - 3 * δ / 4) ^ k := by
      apply hr₀_prop
      rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
      exact (min_le_left _ _).trans_lt (half_lt_self hr₀)
    have hBP_pow_ev : ∀ᶠ j in atTop, opNorm (B j ^ k - P j) ≤ (1 - 3 * δ / 4) ^ k := by
      filter_upwards [hspec_gap ε hε0] with j hj
      have hle := opNorm_pow_sub_highProj_le (hB j) (1 - δ / 2) k (1 - 3 * δ / 4) ε
        (by linarith) hε1 fun i => by
          rcases hj i with hlo | hhi
          · left; exact ⟨(hB_eig_Icc j i).1, hlo, by linarith⟩
          · right
            have hge_θ : 1 - δ / 2 ≤ (hB j).eigenvalues i := by
              have hε_le : ε ≤ δ / 4 := min_le_right _ _
              linarith
            exact ⟨hge_θ, hhi, (hB_eig_Icc j i).2⟩
      exact hle.trans (max_le le_rfl hε_lt.le)
    have ht1 := evalU_gpow_sub_tendsto hUmul mΓ k
    have ht2 := opNorm_pow_sub_pow_tendsto zero_le_one hmΓ1 hB1 hMΓ_B_tendsto k
    have ht4 := hPQ_tendsto
    have ht6 := opNorm_pow_sub_pow_tendsto zero_le_one hC1 hmConj1
      (hmConj_C_tendsto.congr fun j => opNorm_sub_comm _ _) k
    have ht7 := (evalU_gpow_sub_tendsto hUmul mConj k).congr fun j => opNorm_sub_comm _ _
    have hzero5 : Tendsto (fun j =>
        opNorm (evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) +
        opNorm (evalU (U j) mΓ ^ k - B j ^ k) +
        opNorm (P j - Q j) +
        opNorm (Cmat j ^ k - evalU (U j) mConj ^ k) +
        opNorm (evalU (U j) mConj ^ k - evalU (U j) (gpow mConj k))) atTop (𝓝 0) := by
      simpa using (((ht1.add ht2).add ht4).add ht6).add ht7
    let η' : ℝ := if ‖v‖ = 0 then 1 else η / ‖v‖
    have hη' : 0 < η' := by
      by_cases hv0 : ‖v‖ = 0
      · simp [η', hv0]
      · simp only [η', hv0, ↓reduceIte]
        exact div_pos hη (lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv0))
    have hzero5_ev : ∀ᶠ j in atTop,
        opNorm (evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) +
        opNorm (evalU (U j) mΓ ^ k - B j ^ k) +
        opNorm (P j - Q j) +
        opNorm (Cmat j ^ k - evalU (U j) mConj ^ k) +
        opNorm (evalU (U j) mConj ^ k - evalU (U j) (gpow mConj k)) ≤ η' :=
      (hzero5.eventually (Iio_mem_nhds hη')).mono fun _ h => h.le
    let a : G →₀ ℂ := gpow mΓ k - gpow mConj k
    have ha_ev : ∀ᶠ j in atTop,
        ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
          (∑ g ∈ a.support, a g • (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ))‖ ≤
        2 * (1 - 3 * δ / 4) ^ k + η' := by
      filter_upwards [hBP_pow_ev, hzero5_ev] with j hBPj h5j
      change opNorm (evalU (U j) a) ≤ 2 * (1 - 3 * δ / 4) ^ k + η'
      rw [show evalU (U j) a = evalU (U j) (gpow mΓ k) - evalU (U j) (gpow mConj k) from
        evalU_sub (U j) (gpow mΓ k) (gpow mConj k)]
      have hsplit : evalU (U j) (gpow mΓ k) - evalU (U j) (gpow mConj k) =
          (evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) +
          (evalU (U j) mΓ ^ k - B j ^ k) +
          (B j ^ k - P j) +
          (P j - Q j) +
          (Q j - Cmat j ^ k) +
          (Cmat j ^ k - evalU (U j) mConj ^ k) +
          (evalU (U j) mConj ^ k - evalU (U j) (gpow mConj k)) := by abel
      rw [hsplit]
      have hQC : opNorm (Q j - Cmat j ^ k) = opNorm (B j ^ k - P j) := by
        rw [opNorm_sub_comm]
        have heq : Cmat j ^ k - Q j =
            (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ) * (B j ^ k - P j) *
              (U j t : Matrix (Fin (n j)) (Fin (n j)) ℂ)ᴴ := by
          rw [show Cmat j ^ k = (U j t : Matrix _ _ ℂ) * B j ^ k * (U j t : Matrix _ _ ℂ)ᴴ from
            unitary_conj_pow (U j t) (B j) k]
          simp only [Q, Matrix.mul_sub, Matrix.sub_mul]
        rw [heq]
        exact opNorm_conj_unitary (U j t) (B j ^ k - P j)
      have ha1 := opNorm_add_le
        ((evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) + (evalU (U j) mΓ ^ k - B j ^ k) +
          (B j ^ k - P j) + (P j - Q j) + (Q j - Cmat j ^ k) +
          (Cmat j ^ k - evalU (U j) mConj ^ k))
        (evalU (U j) mConj ^ k - evalU (U j) (gpow mConj k))
      have ha2 := opNorm_add_le
        ((evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) + (evalU (U j) mΓ ^ k - B j ^ k) +
          (B j ^ k - P j) + (P j - Q j) + (Q j - Cmat j ^ k))
        (Cmat j ^ k - evalU (U j) mConj ^ k)
      have ha3 := opNorm_add_le
        ((evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) + (evalU (U j) mΓ ^ k - B j ^ k) +
          (B j ^ k - P j) + (P j - Q j))
        (Q j - Cmat j ^ k)
      have ha4 := opNorm_add_le
        ((evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) + (evalU (U j) mΓ ^ k - B j ^ k) +
          (B j ^ k - P j))
        (P j - Q j)
      have ha5 := opNorm_add_le
        ((evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k) + (evalU (U j) mΓ ^ k - B j ^ k))
        (B j ^ k - P j)
      have ha6 := opNorm_add_le
        (evalU (U j) (gpow mΓ k) - evalU (U j) mΓ ^ k)
        (evalU (U j) mΓ ^ k - B j ^ k)
      linarith
    have hdom_v := hdom a.support (fun g => a g) (2 * (1 - 3 * δ / 4) ^ k + η') ha_ev v
    have hdom_lhs : ∑ g ∈ a.support, a g • ρ g v = (M_op F (ρ.comp Γ.subtype))^[k] v - v := by
      change evalρ ρ a v = _
      rw [show evalρ ρ a v = evalρ ρ (gpow mΓ k) v - evalρ ρ (gpow mConj k) v from
        evalρ_sub ρ (gpow mΓ k) (gpow mConj k) v]
      rw [heval_mConj_pow_v k, evalρ_gpow]
      have heq_fn : evalρ ρ mΓ = M_op F (ρ.comp Γ.subtype) := funext heval_mΓ
      rw [heq_fn]
    rw [hdom_lhs] at hdom_v
    by_cases hv0 : ‖v‖ = 0
    · have hvz : v = 0 := norm_eq_zero.mp hv0
      subst hvz
      simp only [norm_zero, mul_zero] at hdom_v ⊢
      linarith
    · have hη_mul : η' * ‖v‖ = η := by
        simp only [η', hv0, ↓reduceIte]
        exact div_mul_cancel₀ η hv0
      linarith
  have htend_v : Tendsto (fun k => (M_op F (ρ.comp Γ.subtype))^[k] v) atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hgeom : Tendsto (fun k : ℕ => 2 * (1 - 3 * δ / 4) ^ k * ‖v‖) atTop (𝓝 0) := by
      have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - 3 * δ / 4)
        (by linarith : 1 - 3 * δ / 4 < 1)
      simpa using (h0.const_mul 2).mul_const ‖v‖
    exact squeeze_zero (fun k => norm_nonneg _) hiter_bd hgeom
  have htend_Mv : Tendsto (fun k => (M_op F (ρ.comp Γ.subtype))^[k + 1] v) atTop
      (𝓝 (M_op F (ρ.comp Γ.subtype) v)) := by
    have hcomp := (M_op F (ρ.comp Γ.subtype)).continuous.continuousAt.tendsto.comp htend_v
    refine hcomp.congr fun k => ?_
    exact (Function.iterate_succ_apply' (M_op F (ρ.comp Γ.subtype)) k v).symm
  have htend_shift : Tendsto (fun k => (M_op F (ρ.comp Γ.subtype))^[k + 1] v) atTop (𝓝 v) :=
    htend_v.comp (tendsto_add_atTop_nat 1)
  have hMv : M_op F (ρ.comp Γ.subtype) v = v := tendsto_nhds_unique htend_Mv htend_shift
  have hinv := M_op_fixed_implies_invariant F hFpos hκ0 hKaz (ρ.comp Γ.subtype) hMv
  intro g hg
  exact hinv ⟨g, hg⟩

end OMA.Green100KazhdanProj

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1.H3 :=
  OMA.Green100KazhdanProj.kazhdan_proj_proof
