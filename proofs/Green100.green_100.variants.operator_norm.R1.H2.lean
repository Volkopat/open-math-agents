import OMAReductions.R_Green100_green_100_variants_operator_norm_R1
import Mathlib

/-!
Weighted Hilbert-Schmidt ultraproduct construction (Eckhardt Theorem 4.3)

We prove `OMA.R_Green100_green_100_variants_operator_norm_R1.H2`:
given an asymptotic unitary representation `φ j : W → U(d j)` in operator norm of a group `W`
containing commuting involutions `a y` conjugated by `r g` (`r g * a y = a (g • y) * r g`),
such that `opDist (φ j (a (γ • x) * a x)) 1 ≥ 1` eventually, we construct a Hilbert space `E`,
a unitary representation `ρ : G →* E ≃ₗᵢ[ℂ] E`, a 1-cocycle `c : Γ → E` vanishing on the
stabilizer of `x` with `∃ g, c g ≠ 0`, and matrix models `U j g ∈ U(d j * d j)` dominating `ρ`.
-/

namespace OMA.Green100WeightedHS

open Filter Finset Matrix Green100
open scoped Topology InnerProductSpace

/- Section 1: Operator-norm and Hilbert-Schmidt helpers on finite matrices -/

abbrev matVec (m : ℕ) : Type := EuclideanSpace ℂ (Fin m × Fin m)

noncomputable def opNorm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖

lemma opNorm_sub_eq_opDist {m : ℕ} (u v : Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm ((u : Matrix (Fin m) (Fin m) ℂ) - (v : Matrix (Fin m) (Fin m) ℂ)) = opDist u v :=
  rfl

noncomputable def toMatVec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : matVec m :=
  WithLp.toLp 2 (fun p : Fin m × Fin m => M p.1 p.2)

noncomputable def ofMatVec {m : ℕ} (v : matVec m) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => v.ofLp (i, j)

lemma toMatVec_ofMatVec {m : ℕ} (v : matVec m) : toMatVec (ofMatVec v) = v := by
  ext ⟨i, j⟩
  rfl

lemma ofMatVec_toMatVec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : ofMatVec (toMatVec M) = M := by
  ext i j
  rfl

lemma toMatVec_zero {m : ℕ} : toMatVec (0 : Matrix (Fin m) (Fin m) ℂ) = 0 := by
  ext ⟨i, j⟩; rfl

lemma toMatVec_add {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    toMatVec (A + B) = toMatVec A + toMatVec B := by
  ext ⟨i, j⟩; rfl

lemma toMatVec_sub {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    toMatVec (A - B) = toMatVec A - toMatVec B := by
  ext ⟨i, j⟩; rfl

lemma toMatVec_smul {m : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    toMatVec (c • A) = c • toMatVec A := by
  ext ⟨i, j⟩; rfl

lemma toMatVec_sum {m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin m) (Fin m) ℂ) :
    toMatVec (∑ i ∈ s, f i) = ∑ i ∈ s, toMatVec (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toMatVec_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, toMatVec_add, ih, Finset.sum_insert ha]

lemma norm_toMatVec_sq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    ‖toMatVec M‖ ^ 2 = ∑ i : Fin m, ∑ j : Fin m, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

lemma inner_toMatVec {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ⟪toMatVec A, toMatVec B⟫_ℂ = ∑ i : Fin m, ∑ j : Fin m, star (A i j) * B i j := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [toMatVec, mul_comm]

lemma norm_toMatVec_conjTranspose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    ‖toMatVec Mᴴ‖ = ‖toMatVec M‖ := by
  have hsq : ‖toMatVec Mᴴ‖ ^ 2 = ‖toMatVec M‖ ^ 2 := by
    rw [norm_toMatVec_sq, norm_toMatVec_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.conjTranspose_apply]
  nlinarith [norm_nonneg (toMatVec Mᴴ), norm_nonneg (toMatVec M)]

lemma toEuclideanCLM_apply_ofLp {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) M v).ofLp = M.mulVec v.ofLp := by
  exact congrArg WithLp.ofLp (Matrix.toEuclideanCLM_toLp (𝕜 := ℂ) M v.ofLp)

lemma opNorm_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ opNorm M :=
  norm_nonneg _

lemma opNorm_neg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : opNorm (-M) = opNorm M := by
  unfold opNorm; rw [map_neg, norm_neg]

lemma opNorm_sub_comm {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) : opNorm (A - B) = opNorm (B - A) := by
  rw [← opNorm_neg (B - A), neg_sub]

lemma opNorm_add_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (A + B) ≤ opNorm A + opNorm B := by
  unfold opNorm; rw [map_add]; exact norm_add_le _ _

lemma opNorm_sub_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  unfold opNorm; rw [map_sub]; exact norm_sub_le _ _

lemma opNorm_smul {m : ℕ} (c : ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (c • M) = ‖c‖ * opNorm M := by
  unfold opNorm; rw [map_smul, norm_smul]

lemma opNorm_conjTranspose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm Mᴴ = opNorm M := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (star M)‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖
  rw [map_star]
  exact ContinuousLinearMap.adjoint.norm_map (Matrix.toEuclideanCLM (𝕜 := ℂ) M)

lemma opNorm_mul_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm; rw [map_mul]; exact norm_mul_le _ _

lemma unitary_inner_mulVec {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (v w : EuclideanSpace ℂ (Fin m)) :
    ⟪Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) w⟫_ℂ = ⟪v, w⟫_ℂ := by
  have hu : star (u : Matrix (Fin m) (Fin m) ℂ) * (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp u.2
  have hadj : ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (star (u : Matrix (Fin m) (Fin m) ℂ)) := by
    rw [map_star]; rfl
  rw [← ContinuousLinearMap.adjoint_inner_right, hadj]
  change ⟪v, (Matrix.toEuclideanCLM (𝕜 := ℂ) (star (u : Matrix (Fin m) (Fin m) ℂ)) *
    Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)) w⟫_ℂ = ⟪v, w⟫_ℂ
  rw [← map_mul, hu, map_one]
  rfl

lemma unitary_norm_mulVec {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v‖ = ‖v‖ := by
  have hre := congrArg (RCLike.re (K := ℂ)) (unitary_inner_mulVec u v v)
  simp only [inner_self_eq_norm_sq] at hre
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) v), norm_nonneg v]

lemma opNorm_unitary_le_one {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm (u : Matrix (Fin m) (Fin m) ℂ) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [unitary_norm_mulVec, one_mul]

lemma opNorm_unitary_conjTranspose_le_one {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm (u : Matrix (Fin m) (Fin m) ℂ)ᴴ ≤ 1 := by
  rw [opNorm_conjTranspose]
  exact opNorm_unitary_le_one u

lemma norm_toMatVec_mul_le {m : ℕ} (E A : Matrix (Fin m) (Fin m) ℂ) :
    ‖toMatVec (E * A)‖ ≤ opNorm E * ‖toMatVec A‖ := by
  unfold opNorm
  have hsq : ‖toMatVec (E * A)‖ ^ 2 ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℂ) E‖ * ‖toMatVec A‖) ^ 2 := by
    rw [mul_pow, norm_toMatVec_sq, norm_toMatVec_sq, Finset.sum_comm (s := Finset.univ) (t := Finset.univ),
      Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i j => ‖A i j‖ ^ 2),
      Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    let col : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => A i j)
    have h1 : ∑ i : Fin m, ‖(E * A) i j‖ ^ 2 = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) E col‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [toEuclideanCLM_apply_ofLp]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, col]
    have h2 : ∑ i : Fin m, ‖A i j‖ ^ 2 = ‖col‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h1, h2, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ col) 2
  nlinarith [norm_nonneg (toMatVec (E * A)), mul_nonneg (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) E)) (norm_nonneg (toMatVec A))]

lemma norm_toMatVec_mul_right_le {m : ℕ} (A E : Matrix (Fin m) (Fin m) ℂ) :
    ‖toMatVec (A * E)‖ ≤ ‖toMatVec A‖ * opNorm E := by
  calc ‖toMatVec (A * E)‖ = ‖toMatVec (A * E)ᴴ‖ := (norm_toMatVec_conjTranspose _).symm
    _ = ‖toMatVec (Eᴴ * Aᴴ)‖ := by rw [Matrix.conjTranspose_mul]
    _ ≤ opNorm Eᴴ * ‖toMatVec Aᴴ‖ := norm_toMatVec_mul_le Eᴴ Aᴴ
    _ = ‖toMatVec A‖ * opNorm E := by
        rw [opNorm_conjTranspose, norm_toMatVec_conjTranspose, mul_comm]

lemma inner_toMatVec_unitary_mul_left {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (A B : Matrix (Fin m) (Fin m) ℂ) :
    ⟪toMatVec ((u : Matrix (Fin m) (Fin m) ℂ) * A),
      toMatVec ((u : Matrix (Fin m) (Fin m) ℂ) * B)⟫_ℂ = ⟪toMatVec A, toMatVec B⟫_ℂ := by
  rw [inner_toMatVec, inner_toMatVec,
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ),
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun i j => star (A i j) * B i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  let colA : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => A i j)
  let colB : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => B i j)
  have h := unitary_inner_mulVec u colA colB
  simp only [PiLp.inner_apply, toEuclideanCLM_apply_ofLp, Matrix.mulVec, dotProduct, colA, colB] at h
  simpa [Matrix.mul_apply, mul_comm] using h

lemma inner_toMatVec_conjTranspose {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ⟪toMatVec Aᴴ, toMatVec Bᴴ⟫_ℂ = ⟪toMatVec B, toMatVec A⟫_ℂ := by
  rw [inner_toMatVec, inner_toMatVec, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.conjTranspose_apply, mul_comm]

lemma inner_toMatVec_conj {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (A B : Matrix (Fin m) (Fin m) ℂ) :
    ⟪toMatVec ((u : Matrix (Fin m) (Fin m) ℂ) * A * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ),
      toMatVec ((u : Matrix (Fin m) (Fin m) ℂ) * B * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)⟫_ℂ =
      ⟪toMatVec A, toMatVec B⟫_ℂ := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, inner_toMatVec_unitary_mul_left u]
  rw [← inner_toMatVec_conjTranspose (B * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)
    (A * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [inner_toMatVec_unitary_mul_left u, inner_toMatVec_conjTranspose]

lemma norm_toMatVec_conj {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) :
    ‖toMatVec ((u : Matrix (Fin m) (Fin m) ℂ) * A * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)‖ =
      ‖toMatVec A‖ := by
  have hre := congrArg (RCLike.re (K := ℂ)) (inner_toMatVec_conj u A A)
  simp only [inner_self_eq_norm_sq] at hre
  nlinarith [norm_nonneg (toMatVec ((u : Matrix (Fin m) (Fin m) ℂ) * A *
    (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)), norm_nonneg (toMatVec A)]

lemma norm_toMatVec_sq_eq_sum_onb {m : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin m) (Fin m) ℂ) (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Fin m))) :
    ‖toMatVec M‖ ^ 2 = ∑ k : ι, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M (b k)‖ ^ 2 := by
  rw [norm_toMatVec_sq]
  have hstep : ∀ k : ι, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M (b k)‖ ^ 2 =
      ∑ i : Fin m, ‖⟪(WithLp.toLp 2 (fun j => star (M i j)) : EuclideanSpace ℂ (Fin m)), b k⟫_ℂ‖ ^ 2 := by
    intro k
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toEuclideanCLM_apply_ofLp, PiLp.inner_apply]
    congr 2
    change ∑ j : Fin m, M i j * (b k).ofLp j =
      ∑ j : Fin m, (b k).ofLp j * star (star (M i j))
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_star, mul_comm]
  simp_rw [hstep]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  let r : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun j => star (M i j))
  have hr1 : ‖r‖ ^ 2 = ∑ j : Fin m, ‖M i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [r]
  have hr2 : ‖r‖ ^ 2 = ∑ k : ι, ‖⟪r, b k⟫_ℂ‖ ^ 2 := by
    rw [← b.repr.norm_map r, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [b.repr_apply_apply, norm_inner_symm]
  rw [← hr1, hr2]

lemma norm_toMatVec_le_of_vanish_on {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (K : Submodule ℂ (EuclideanSpace ℂ (Fin m)))
    (hK : ∀ v ∈ K, Matrix.toEuclideanCLM (𝕜 := ℂ) M v = 0) :
    ‖toMatVec M‖ ^ 2 ≤ (Module.finrank ℂ Kᗮ : ℝ) * opNorm M ^ 2 := by
  let e1 := stdOrthonormalBasis ℂ K
  let e2 := stdOrthonormalBasis ℂ Kᗮ
  let f : Fin (Module.finrank ℂ K) ⊕ Fin (Module.finrank ℂ Kᗮ) → EuclideanSpace ℂ (Fin m) :=
    Sum.elim (fun i => (e1 i : EuclideanSpace ℂ (Fin m))) (fun j => (e2 j : EuclideanSpace ℂ (Fin m)))
  have hon : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    rintro (i | i) (j | j)
    · simpa [f] using (orthonormal_iff_ite.mp e1.orthonormal) i j
    · simp only [f, Sum.elim_inl, Sum.elim_inr, Sum.inl_ne_inr, ↓reduceIte]
      exact (Submodule.mem_orthogonal K _).mp (e2 j).2 (e1 i) (e1 i).2
    · simp only [f, Sum.elim_inl, Sum.elim_inr, Sum.inr_ne_inl, ↓reduceIte]
      have h0 : ⟪(e1 j : EuclideanSpace ℂ (Fin m)), (e2 i : EuclideanSpace ℂ (Fin m))⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal K _).mp (e2 i).2 (e1 j) (e1 j).2
      rw [← inner_conj_symm, h0, map_zero]
    · simpa [f] using (orthonormal_iff_ite.mp e2.orthonormal) i j
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    have hfr : Module.finrank ℂ (Submodule.span ℂ (Set.range f)) =
        Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) := by
      rw [finrank_span_eq_card hon.linearIndependent, Fintype.card_sum, Fintype.card_fin,
        Fintype.card_fin, Submodule.finrank_add_finrank_orthogonal]
    rw [Submodule.eq_top_of_finrank_eq hfr]
  let b : OrthonormalBasis (Fin (Module.finrank ℂ K) ⊕ Fin (Module.finrank ℂ Kᗮ)) ℂ
      (EuclideanSpace ℂ (Fin m)) := OrthonormalBasis.mk hon hspan
  rw [norm_toMatVec_sq_eq_sum_onb M b, Fintype.sum_sum_type]
  have hzero : ∑ i : Fin (Module.finrank ℂ K), ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M (b (Sum.inl i))‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hb : b (Sum.inl i) = (e1 i : EuclideanSpace ℂ (Fin m)) := by
      simp [b, f]
    rw [hb, hK _ (e1 i).2, norm_zero, zero_pow two_ne_zero]
  rw [hzero, zero_add]
  calc ∑ j : Fin (Module.finrank ℂ Kᗮ), ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M (b (Sum.inr j))‖ ^ 2
      ≤ ∑ _j : Fin (Module.finrank ℂ Kᗮ), opNorm M ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hbn : ‖b (Sum.inr j)‖ = 1 := b.orthonormal.1 (Sum.inr j)
        have hle := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℂ) M) (b (Sum.inr j))
        rw [hbn, mul_one] at hle
        exact pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = (Module.finrank ℂ Kᗮ : ℝ) * opNorm M ^ 2 := by
        simp

/- Section 2: Spectral negative-eigenspace projection of Hermitian matrices -/

noncomputable def negProj {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i l =>
    ∑ k : Fin m, if hH.eigenvalues k < 0 then
      (hH.eigenvectorBasis k).ofLp i * star ((hH.eigenvectorBasis k).ofLp l)
    else 0

noncomputable def negRank {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) : ℕ :=
  (Finset.univ.filter (fun k : Fin m => hH.eigenvalues k < 0)).card

lemma toEuclideanCLM_negProj_basis {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (k : Fin m) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj hH) (hH.eigenvectorBasis k) =
      if hH.eigenvalues k < 0 then hH.eigenvectorBasis k else 0 := by
  ext i
  rw [toEuclideanCLM_apply_ofLp]
  simp only [Matrix.mulVec, dotProduct, negProj, Matrix.of_apply]
  trans ∑ r : Fin m, (if hH.eigenvalues r < 0 then
      (hH.eigenvectorBasis r).ofLp i * ⟪hH.eigenvectorBasis r, hH.eigenvectorBasis k⟫_ℂ else 0)
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with h
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
    · simp only [↓reduceIte, mul_one]
      split_ifs <;> rfl
    · intro r _ hrk
      simp only [hrk, ↓reduceIte, mul_zero, ite_self]
    · intro hk; exact absurd (Finset.mem_univ k) hk

lemma toEuclideanCLM_hermitian_basis {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (k : Fin m) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) H (hH.eigenvectorBasis k) =
      (hH.eigenvalues k : ℂ) • hH.eigenvectorBasis k := by
  ext i
  rw [toEuclideanCLM_apply_ofLp, hH.mulVec_eigenvectorBasis]
  simp [Complex.real_smul]

lemma negProj_eq_zero_of_one {m : ℕ} (h1 : (1 : Matrix (Fin m) (Fin m) ℂ).IsHermitian) :
    negProj h1 = 0 := by
  have hev : ∀ k : Fin m, ¬ h1.eigenvalues k < 0 := by
    intro k
    have h := h1.eigenvalues_eq k
    have h1v : (1 : Matrix (Fin m) (Fin m) ℂ).mulVec (h1.eigenvectorBasis k).ofLp =
        (h1.eigenvectorBasis k).ofLp := Matrix.one_mulVec _
    rw [h1v] at h
    have hdot : star (h1.eigenvectorBasis k).ofLp ⬝ᵥ (h1.eigenvectorBasis k).ofLp = 1 := by
      have hn : ⟪h1.eigenvectorBasis k, h1.eigenvectorBasis k⟫_ℂ = 1 := by
        have h0 := orthonormal_iff_ite.mp h1.eigenvectorBasis.orthonormal k k
        simp only [↓reduceIte] at h0
        exact h0
      rw [← hn, PiLp.inner_apply, dotProduct]
      refine Finset.sum_congr rfl fun x _ => ?_
      change star ((h1.eigenvectorBasis k).ofLp x) * (h1.eigenvectorBasis k).ofLp x =
        (h1.eigenvectorBasis k).ofLp x * star ((h1.eigenvectorBasis k).ofLp x)
      rw [mul_comm]
    rw [hdot, RCLike.one_re] at h
    linarith
  ext i l
  simp [negProj, hev]

lemma norm_toMatVec_negProj_sq {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    ‖toMatVec (negProj hH)‖ ^ 2 = (negRank hH : ℝ) := by
  rw [norm_toMatVec_sq_eq_sum_onb (negProj hH) hH.eigenvectorBasis]
  simp_rw [toEuclideanCLM_negProj_basis]
  trans ∑ k : Fin m, if hH.eigenvalues k < 0 then (1 : ℝ) else 0
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [hH.eigenvectorBasis.orthonormal.1 k, one_pow]
    · simp
  · simp [negRank, Finset.sum_boole]

lemma abs_sign_sub_le_abs_sq_sub_one (t : ℝ) :
    |(if t < 0 then (-1 : ℝ) else 1) - t| ≤ |t ^ 2 - 1| := by
  split_ifs with ht
  · have h1 : 1 - t ≥ 1 := by linarith
    have h2 : |t ^ 2 - 1| = |-(1 + t)| * |1 - t| := by
      rw [show t ^ 2 - 1 = (-(1 + t)) * (1 - t) by ring, abs_mul]
    rw [show (-1 : ℝ) - t = -(1 + t) by ring, h2, abs_of_pos (by linarith : 0 < 1 - t)]
    nlinarith [abs_nonneg (-(1 + t))]
  · have h1 : 1 + t ≥ 1 := by linarith
    have h2 : |t ^ 2 - 1| = |1 - t| * |1 + t| := by
      rw [show t ^ 2 - 1 = -((1 - t) * (1 + t)) by ring, abs_neg, abs_mul]
    rw [h2, abs_of_pos (by linarith : 0 < 1 + t)]
    nlinarith [abs_nonneg (1 - t)]

lemma opNorm_one_sub_two_negProj_sub_le {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) :
    opNorm (1 - (2 : ℂ) • negProj hH - H) ≤ opNorm (H * H - 1) := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  let b := hH.eigenvectorBasis
  let ev := hH.eigenvalues
  have hv : v = ∑ k : Fin m, ⟪b k, v⟫_ℂ • b k := (b.sum_repr' v).symm
  let A : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (2 : ℂ) • negProj hH - H)
  let B : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanCLM (𝕜 := ℂ) (H * H - 1)
  have hAb : ∀ k : Fin m, A (b k) = (((if ev k < 0 then (-1 : ℝ) else 1) - ev k : ℝ) : ℂ) • b k := by
    intro k
    have hlin : A (b k) = b k - (2 : ℂ) • Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj hH) (b k) -
        Matrix.toEuclideanCLM (𝕜 := ℂ) H (b k) := by
      simp [A]
    rw [hlin, toEuclideanCLM_negProj_basis, toEuclideanCLM_hermitian_basis]
    split_ifs with hk
    · change b k - (2 : ℂ) • b k - (ev k : ℂ) • b k = (((-1 : ℝ) - ev k : ℝ) : ℂ) • b k
      push_cast
      module
    · change b k - (2 : ℂ) • (0 : EuclideanSpace ℂ (Fin m)) - (ev k : ℂ) • b k =
        (((1 : ℝ) - ev k : ℝ) : ℂ) • b k
      push_cast
      module
  have hBb : ∀ k : Fin m, B (b k) = (((ev k) ^ 2 - 1 : ℝ) : ℂ) • b k := by
    intro k
    have hlin : B (b k) = Matrix.toEuclideanCLM (𝕜 := ℂ) H (Matrix.toEuclideanCLM (𝕜 := ℂ) H (b k)) - b k := by
      simp [B]
    rw [hlin, toEuclideanCLM_hermitian_basis, map_smul, toEuclideanCLM_hermitian_basis]
    change (ev k : ℂ) • (ev k : ℂ) • b k - b k = (((ev k) ^ 2 - 1 : ℝ) : ℂ) • b k
    push_cast
    rw [sq]
    module
  have hAv : A v = ∑ k : Fin m,
      ((((if ev k < 0 then (-1 : ℝ) else 1) - ev k : ℝ) : ℂ) * ⟪b k, v⟫_ℂ) • b k := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hAb k, smul_smul, mul_comm]
  have hBv : B v = ∑ k : Fin m, ((((ev k) ^ 2 - 1 : ℝ) : ℂ) * ⟪b k, v⟫_ℂ) • b k := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hBb k, smul_smul, mul_comm]
  have hsq : ‖A v‖ ^ 2 ≤ ‖B v‖ ^ 2 := by
    rw [← b.repr.norm_map (A v), ← b.repr.norm_map (B v),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [b.repr_apply_apply, b.repr_apply_apply, hAv, hBv, inner_sum, inner_sum]
    have hcoeff : ∀ (f : Fin m → ℂ), ∑ r : Fin m, ⟪b k, f r • b r⟫_ℂ = f k := by
      intro f
      rw [Finset.sum_eq_single k]
      · rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k k]
        simp
      · intro r _ hrk
        rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal k r]
        simp [Ne.symm hrk]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [hcoeff, hcoeff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    have hle := abs_sign_sub_le_abs_sq_sub_one (ev k)
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hle (norm_nonneg _)) 2
  have hAB : ‖A v‖ ≤ ‖B v‖ := by nlinarith [norm_nonneg (A v), norm_nonneg (B v)]
  exact hAB.trans (ContinuousLinearMap.le_opNorm B v)

noncomputable def negSubspace {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  Submodule.span ℂ (Set.range fun k : {k : Fin m // hH.eigenvalues k < 0} => hH.eigenvectorBasis k.1)

noncomputable def nonnegSubspace {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  Submodule.span ℂ (Set.range fun k : {k : Fin m // ¬ hH.eigenvalues k < 0} => hH.eigenvectorBasis k.1)

lemma finrank_negSubspace {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    Module.finrank ℂ (negSubspace hH) = negRank hH := by
  have hli : LinearIndependent ℂ
      (fun k : {k : Fin m // hH.eigenvalues k < 0} => hH.eigenvectorBasis k.1) :=
    hH.eigenvectorBasis.toBasis.linearIndependent.comp Subtype.val Subtype.val_injective
  rw [negSubspace, finrank_span_eq_card hli, Fintype.card_subtype, negRank]

lemma finrank_nonnegSubspace {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    Module.finrank ℂ (nonnegSubspace hH) = m - negRank hH := by
  have hli : LinearIndependent ℂ
      (fun k : {k : Fin m // ¬ hH.eigenvalues k < 0} => hH.eigenvectorBasis k.1) :=
    hH.eigenvectorBasis.toBasis.linearIndependent.comp Subtype.val Subtype.val_injective
  rw [nonnegSubspace, finrank_span_eq_card hli, Fintype.card_subtype, negRank]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := fun k => hH.eigenvalues k < 0)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  omega

lemma negProj_apply_eq_self_of_mem_negSubspace {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) {v : EuclideanSpace ℂ (Fin m)} (hv : v ∈ negSubspace hH) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj hH) v = v := by
  refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
    (fun c x _ hx => by simp [hx]) hv
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  rw [toEuclideanCLM_negProj_basis]
  simp only [hk, ↓reduceIte]

lemma negProj_apply_eq_zero_of_mem_nonnegSubspace {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) {v : EuclideanSpace ℂ (Fin m)} (hv : v ∈ nonnegSubspace hH) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj hH) v = 0 := by
  refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
    (fun c x _ hx => by simp [hx]) hv
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  rw [toEuclideanCLM_negProj_basis]
  simp only [hk, ↓reduceIte]

/- Section 3: Kronecker-product conjugation matrix models -/

def kronConj {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin (m * m)) (Fin (m * m)) ℂ :=
  Matrix.of fun a b =>
    let p := finProdFinEquiv.symm a
    let q := finProdFinEquiv.symm b
    (u : Matrix (Fin m) (Fin m) ℂ) p.1 q.1 * star ((u : Matrix (Fin m) (Fin m) ℂ) p.2 q.2)

lemma kronConj_mem_unitaryGroup {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    kronConj u ∈ Matrix.unitaryGroup (Fin (m * m)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hu : (u : Matrix (Fin m) (Fin m) ℂ) * star (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp u.2
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  let p := finProdFinEquiv.symm a
  let q := finProdFinEquiv.symm b
  have hsum : ∑ c : Fin (m * m), kronConj u a c * (star (kronConj u)) c b =
      (∑ c1 : Fin m, (u : Matrix (Fin m) (Fin m) ℂ) p.1 c1 *
        star ((u : Matrix (Fin m) (Fin m) ℂ) q.1 c1)) *
      (∑ c2 : Fin m, (u : Matrix (Fin m) (Fin m) ℂ) q.2 c2 *
        star ((u : Matrix (Fin m) (Fin m) ℂ) p.2 c2)) := by
    rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv finProdFinEquiv.symm _ _ fun c => ?_
    simp only [kronConj, Matrix.star_apply, Matrix.of_apply, p, q, star_mul', star_star]
    ring
  rw [hsum]
  have h1 : ∑ c1 : Fin m, (u : Matrix (Fin m) (Fin m) ℂ) p.1 c1 *
      star ((u : Matrix (Fin m) (Fin m) ℂ) q.1 c1) = if p.1 = q.1 then 1 else 0 := by
    have := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M p.1 q.1) hu
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this
  have h2 : ∑ c2 : Fin m, (u : Matrix (Fin m) (Fin m) ℂ) q.2 c2 *
      star ((u : Matrix (Fin m) (Fin m) ℂ) p.2 c2) = if q.2 = p.2 then 1 else 0 := by
    have := congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M q.2 p.2) hu
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this
  rw [h1, h2]
  by_cases hab : a = b
  · subst hab; simp [p, q]
  · have hpq : p ≠ q := fun h => hab (finProdFinEquiv.symm.injective h)
    by_cases h1eq : p.1 = q.1
    · have h2ne : q.2 ≠ p.2 := fun h => hpq (Prod.ext h1eq h.symm)
      simp [hab, h1eq, h2ne]
    · simp [hab, h1eq]

def kronConjUnitary {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    Matrix.unitaryGroup (Fin (m * m)) ℂ :=
  ⟨kronConj u, kronConj_mem_unitaryGroup u⟩

noncomputable def matVecEquiv (m : ℕ) : matVec m ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m * m)) where
  toFun v := WithLp.toLp 2 (fun a => v.ofLp (finProdFinEquiv.symm a))
  invFun w := WithLp.toLp 2 (fun p => w.ofLp (finProdFinEquiv p))
  left_inv v := by
    ext p
    exact congrArg v.ofLp (finProdFinEquiv.symm_apply_apply p)
  right_inv w := by
    ext a
    exact congrArg w.ofLp (finProdFinEquiv.apply_symm_apply a)
  map_add' _ _ := by ext a; rfl
  map_smul' _ _ := by ext a; rfl
  norm_map' v := by
    change ‖(WithLp.toLp 2 (fun a => v.ofLp (finProdFinEquiv.symm a)) :
      EuclideanSpace ℂ (Fin (m * m)))‖ = ‖v‖
    have hsq : ‖(WithLp.toLp 2 (fun a => v.ofLp (finProdFinEquiv.symm a)) :
        EuclideanSpace ℂ (Fin (m * m)))‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun a => v.ofLp (finProdFinEquiv.symm a)) :
      EuclideanSpace ℂ (Fin (m * m))), norm_nonneg v]

lemma matVecEquiv_toMatVec_ofLp {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (a : Fin (m * m)) :
    (matVecEquiv m (toMatVec M)).ofLp a = M (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 :=
  rfl

lemma toEuclideanCLM_kronConj_apply {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (kronConj u) (matVecEquiv m (toMatVec M)) =
      matVecEquiv m (toMatVec ((u : Matrix (Fin m) (Fin m) ℂ) * M *
        (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)) := by
  ext a
  rw [toEuclideanCLM_apply_ofLp, matVecEquiv_toMatVec_ofLp]
  simp only [Matrix.mulVec, dotProduct, matVecEquiv_toMatVec_ofLp, kronConj, Matrix.of_apply]
  let p := finProdFinEquiv.symm a
  have hrhs : ((u : Matrix (Fin m) (Fin m) ℂ) * M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) p.1 p.2 =
      ∑ q : Fin m × Fin m,
        (u : Matrix (Fin m) (Fin m) ℂ) p.1 q.1 *
          star ((u : Matrix (Fin m) (Fin m) ℂ) p.2 q.2) * M q.1 q.2 := by
    rw [Fintype.sum_prod_type, Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q1 _ => Finset.sum_congr rfl fun q2 _ => by ring
  change ∑ b : Fin (m * m),
      (u : Matrix (Fin m) (Fin m) ℂ) p.1 (finProdFinEquiv.symm b).1 *
        star ((u : Matrix (Fin m) (Fin m) ℂ) p.2 (finProdFinEquiv.symm b).2) *
        M (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2 =
    ((u : Matrix (Fin m) (Fin m) ℂ) * M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) p.1 p.2
  rw [hrhs]
  exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)

lemma norm_toMatVec_conj_diff_le {m : ℕ} (u1 u2 : Matrix.unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    ‖toMatVec ((u1 : Matrix (Fin m) (Fin m) ℂ) * M * (u1 : Matrix (Fin m) (Fin m) ℂ)ᴴ -
      (u2 : Matrix (Fin m) (Fin m) ℂ) * M * (u2 : Matrix (Fin m) (Fin m) ℂ)ᴴ)‖ ≤
      2 * opDist u1 u2 * ‖toMatVec M‖ := by
  let A : Matrix (Fin m) (Fin m) ℂ := u1
  let B : Matrix (Fin m) (Fin m) ℂ := u2
  have hsplit : A * M * Aᴴ - B * M * Bᴴ = (A - B) * M * Aᴴ + B * M * (A - B)ᴴ := by
    simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.conjTranspose_sub]
  change ‖toMatVec (A * M * Aᴴ - B * M * Bᴴ)‖ ≤ 2 * opNorm (A - B) * ‖toMatVec M‖
  rw [hsplit, toMatVec_add]
  have h1 : ‖toMatVec ((A - B) * M * Aᴴ)‖ ≤ opNorm (A - B) * ‖toMatVec M‖ := by
    calc ‖toMatVec ((A - B) * M * Aᴴ)‖
        ≤ ‖toMatVec ((A - B) * M)‖ * opNorm Aᴴ := norm_toMatVec_mul_right_le _ _
      _ ≤ (opNorm (A - B) * ‖toMatVec M‖) * 1 :=
          mul_le_mul (norm_toMatVec_mul_le _ _) (opNorm_unitary_conjTranspose_le_one u1)
            (opNorm_nonneg _) (mul_nonneg (opNorm_nonneg _) (norm_nonneg _))
      _ = opNorm (A - B) * ‖toMatVec M‖ := mul_one _
  have h2 : ‖toMatVec (B * M * (A - B)ᴴ)‖ ≤ opNorm (A - B) * ‖toMatVec M‖ := by
    calc ‖toMatVec (B * M * (A - B)ᴴ)‖
        ≤ ‖toMatVec (B * M)‖ * opNorm (A - B)ᴴ := norm_toMatVec_mul_right_le _ _
      _ ≤ (opNorm B * ‖toMatVec M‖) * opNorm (A - B) := by
          rw [opNorm_conjTranspose]
          exact mul_le_mul_of_nonneg_right (norm_toMatVec_mul_le _ _) (opNorm_nonneg _)
      _ ≤ (1 * ‖toMatVec M‖) * opNorm (A - B) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (opNorm_unitary_le_one u2) (norm_nonneg _))
            (opNorm_nonneg _)
      _ = opNorm (A - B) * ‖toMatVec M‖ := by ring
  calc ‖toMatVec ((A - B) * M * Aᴴ) + toMatVec (B * M * (A - B)ᴴ)‖
      ≤ ‖toMatVec ((A - B) * M * Aᴴ)‖ + ‖toMatVec (B * M * (A - B)ᴴ)‖ := norm_add_le _ _
    _ ≤ opNorm (A - B) * ‖toMatVec M‖ + opNorm (A - B) * ‖toMatVec M‖ := add_le_add h1 h2
    _ = 2 * opNorm (A - B) * ‖toMatVec M‖ := by ring

lemma opDist_kronConj_le {m : ℕ} (u1 u2 u3 : Matrix.unitaryGroup (Fin m) ℂ) :
    opDist (kronConjUnitary u1) (kronConjUnitary u2 * kronConjUnitary u3) ≤
      2 * opDist u1 (u2 * u3) := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
    ((kronConjUnitary u1 : Matrix (Fin (m * m)) (Fin (m * m)) ℂ) -
      ((kronConjUnitary u2 * kronConjUnitary u3 : Matrix.unitaryGroup (Fin (m * m)) ℂ) :
        Matrix (Fin (m * m)) (Fin (m * m)) ℂ))‖ ≤ 2 * opDist u1 (u2 * u3)
  refine ContinuousLinearMap.opNorm_le_bound _ (by unfold opDist; positivity) fun v => ?_
  let M : Matrix (Fin m) (Fin m) ℂ := ofMatVec ((matVecEquiv m).symm v)
  have hMv : matVecEquiv m (toMatVec M) = v := by simp [M, toMatVec_ofMatVec]
  have hMn : ‖toMatVec M‖ = ‖v‖ := by rw [← hMv, (matVecEquiv m).norm_map]
  have hdiff : Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((kronConjUnitary u1 : Matrix (Fin (m * m)) (Fin (m * m)) ℂ) -
        ((kronConjUnitary u2 * kronConjUnitary u3 : Matrix.unitaryGroup (Fin (m * m)) ℂ) :
          Matrix (Fin (m * m)) (Fin (m * m)) ℂ)) v =
      matVecEquiv m (toMatVec ((u1 : Matrix (Fin m) (Fin m) ℂ) * M * (u1 : Matrix (Fin m) (Fin m) ℂ)ᴴ -
        ((u2 * u3 : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * M *
          ((u2 * u3 : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)ᴴ)) := by
    rw [← hMv, map_sub]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (kronConj u1) (matVecEquiv m (toMatVec M)) -
      Matrix.toEuclideanCLM (𝕜 := ℂ) (kronConj u2 * kronConj u3) (matVecEquiv m (toMatVec M)) = _
    rw [map_mul]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (kronConj u1) (matVecEquiv m (toMatVec M)) -
      Matrix.toEuclideanCLM (𝕜 := ℂ) (kronConj u2)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (kronConj u3) (matVecEquiv m (toMatVec M))) = _
    rw [toEuclideanCLM_kronConj_apply u1 M, toEuclideanCLM_kronConj_apply u3 M,
      toEuclideanCLM_kronConj_apply u2, ← map_sub, ← toMatVec_sub]
    congr 2
    simp [Matrix.mul_assoc, Matrix.conjTranspose_mul]
  rw [hdiff, (matVecEquiv m).norm_map]
  have hbound := norm_toMatVec_conj_diff_le u1 (u2 * u3) M
  rw [hMn] at hbound
  exact hbound

/- Section 4: Ultraproduct pre-Hilbert space and its completion -/

lemma hyperfilter_le_atTop : (Filter.hyperfilter ℕ : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  exact Filter.hyperfilter_le_cofinite

lemma tendsto_limUnder_of_bdd_complex {f : ℕ → ℂ} (hb : ∃ C : ℝ, ∀ j, ‖f j‖ ≤ C) :
    Tendsto f (Filter.hyperfilter ℕ) (𝓝 (limUnder (Filter.hyperfilter ℕ) f)) := by
  obtain ⟨C, hC⟩ := hb
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) C) := isCompact_closedBall 0 C
  have hmem : ∀ j, f j ∈ Metric.closedBall (0 : ℂ) C := fun j => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hC j
  have hle : ((Filter.hyperfilter ℕ).map f : Filter ℂ) ≤ Filter.principal (Metric.closedBall 0 C) :=
    Filter.tendsto_principal.mpr (Filter.Eventually.of_forall hmem)
  obtain ⟨L, _, hL⟩ := hcomp.ultrafilter_le_nhds ((Filter.hyperfilter ℕ).map f) hle
  exact tendsto_nhds_limUnder ⟨L, hL⟩

lemma bdd_of_eventually_bdd {f : ℕ → ℝ}
    (h : ∃ C : ℝ, ∀ᶠ j in atTop, f j ≤ C) :
    ∃ C : ℝ, ∀ j : ℕ, f j ≤ C := by
  obtain ⟨C, hC⟩ := h
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  refine ⟨max C ((Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩ f), fun j => ?_⟩
  by_cases hj : N ≤ j
  · exact (hN j hj).trans (le_max_left _ _)
  · exact (Finset.le_sup' f (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _)

structure BSeq (d : ℕ → ℕ) : Type where
  seq : ∀ j : ℕ, matVec (d j)
  bdd : ∃ C : ℝ, ∀ j : ℕ, ‖seq j‖ ≤ C

namespace BSeq

variable {d : ℕ → ℕ}

lemma ext {f g : BSeq d} (h : ∀ j, f.seq j = g.seq j) : f = g := by
  cases f; cases g; simp only [mk.injEq]; funext j; exact h j

instance : Zero (BSeq d) where
  zero := ⟨fun _ => 0, ⟨0, fun _ => by simp⟩⟩

instance : Add (BSeq d) where
  add f g := ⟨fun j => f.seq j + g.seq j, by
    obtain ⟨C1, h1⟩ := f.bdd
    obtain ⟨C2, h2⟩ := g.bdd
    exact ⟨C1 + C2, fun j => (norm_add_le _ _).trans (add_le_add (h1 j) (h2 j))⟩⟩

instance : Neg (BSeq d) where
  neg f := ⟨fun j => -f.seq j, by
    obtain ⟨C, h⟩ := f.bdd
    exact ⟨C, fun j => by rw [norm_neg]; exact h j⟩⟩

instance : Sub (BSeq d) where
  sub f g := ⟨fun j => f.seq j - g.seq j, by
    obtain ⟨C1, h1⟩ := f.bdd
    obtain ⟨C2, h2⟩ := g.bdd
    exact ⟨C1 + C2, fun j => (norm_sub_le _ _).trans (add_le_add (h1 j) (h2 j))⟩⟩

instance : SMul ℂ (BSeq d) where
  smul c f := ⟨fun j => c • f.seq j, by
    obtain ⟨C, h⟩ := f.bdd
    exact ⟨‖c‖ * C, fun j => by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h j) (norm_nonneg c)⟩⟩

instance : AddCommGroup (BSeq d) where
  add_assoc a b c := BSeq.ext fun j => add_assoc (a.seq j) (b.seq j) (c.seq j)
  zero_add a := BSeq.ext fun j => zero_add (a.seq j)
  add_zero a := BSeq.ext fun j => add_zero (a.seq j)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := BSeq.ext fun j => neg_add_cancel (a.seq j)
  add_comm a b := BSeq.ext fun j => add_comm (a.seq j) (b.seq j)
  sub_eq_add_neg a b := BSeq.ext fun j => sub_eq_add_neg (a.seq j) (b.seq j)

instance : Module ℂ (BSeq d) where
  one_smul a := BSeq.ext fun j => one_smul ℂ (a.seq j)
  mul_smul c1 c2 a := BSeq.ext fun j => mul_smul c1 c2 (a.seq j)
  smul_zero c := BSeq.ext fun _ => smul_zero c
  smul_add c a b := BSeq.ext fun j => smul_add c (a.seq j) (b.seq j)
  add_smul c1 c2 a := BSeq.ext fun j => add_smul c1 c2 (a.seq j)
  zero_smul a := BSeq.ext fun j => zero_smul ℂ (a.seq j)

lemma inner_bdd (f g : BSeq d) : ∃ C : ℝ, ∀ j : ℕ, ‖⟪f.seq j, g.seq j⟫_ℂ‖ ≤ C := by
  obtain ⟨C1, h1⟩ := f.bdd
  obtain ⟨C2, h2⟩ := g.bdd
  refine ⟨max C1 0 * max C2 0, fun j => ?_⟩
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul ((h1 j).trans (le_max_left _ _)) ((h2 j).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _))

noncomputable def ultraInner (f g : BSeq d) : ℂ :=
  limUnder (Filter.hyperfilter ℕ) (fun j => ⟪f.seq j, g.seq j⟫_ℂ)

lemma tendsto_ultraInner (f g : BSeq d) :
    Tendsto (fun j => ⟪f.seq j, g.seq j⟫_ℂ) (Filter.hyperfilter ℕ) (𝓝 (ultraInner f g)) :=
  tendsto_limUnder_of_bdd_complex (inner_bdd f g)

noncomputable instance instPreInnerCore : PreInnerProductSpace.Core ℂ (BSeq d) where
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
    have heq : (fun j => ⟪(f + g).seq j, h.seq j⟫_ℂ) = (fun j => ⟪f.seq j, h.seq j⟫_ℂ + ⟪g.seq j, h.seq j⟫_ℂ) := by
      funext j; exact inner_add_left _ _ _
    rw [heq] at h2
    exact tendsto_nhds_unique h2 h1
  smul_left f g r := by
    have h1 := (tendsto_ultraInner f g).const_mul ((starRingEnd ℂ) r)
    have h2 := tendsto_ultraInner (r • f) g
    have heq : (fun j => ⟪(r • f).seq j, g.seq j⟫_ℂ) = (fun j => (starRingEnd ℂ) r * ⟪f.seq j, g.seq j⟫_ℂ) := by
      funext j; exact inner_smul_left _ _ _
    rw [heq] at h2
    exact tendsto_nhds_unique h2 h1

noncomputable instance instSeminormedAddCommGroup : SeminormedAddCommGroup (BSeq d) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ (BSeq d) _ _ _ instPreInnerCore

noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (BSeq d) :=
  InnerProductSpace.ofCore instPreInnerCore

lemma tendsto_norm_sq (f : BSeq d) :
    Tendsto (fun j => ‖f.seq j‖ ^ 2) (Filter.hyperfilter ℕ) (𝓝 (‖f‖ ^ 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_ultraInner f f)
  have hre : (ultraInner f f).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  rw [hre] at h
  have heq : (fun j => (⟪f.seq j, f.seq j⟫_ℂ).re) = (fun j => ‖f.seq j‖ ^ 2) := by
    funext j
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (f.seq j)
  rwa [Function.comp_def, heq] at h

lemma norm_eq_zero_of_tendsto_zero (f : BSeq d)
    (h : Tendsto (fun j => ‖f.seq j‖) atTop (𝓝 0)) : ‖f‖ = 0 := by
  have hsq : Tendsto (fun j => ‖f.seq j‖ ^ 2) (Filter.hyperfilter ℕ) (𝓝 0) := by
    have h0 : Tendsto (fun j => ‖f.seq j‖ ^ 2) atTop (𝓝 (0 ^ 2)) := h.pow 2
    rw [zero_pow two_ne_zero] at h0
    exact h0.mono_left hyperfilter_le_atTop
  have heq : ‖f‖ ^ 2 = 0 := tendsto_nhds_unique (tendsto_norm_sq f) hsq
  nlinarith [norm_nonneg f]

lemma seq_sum {ι : Type*} (s : Finset ι) (F : ι → BSeq d) (j : ℕ) :
    (∑ i ∈ s, F i).seq j = ∑ i ∈ s, (F i).seq j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change (F a).seq j + (∑ i ∈ s, F i).seq j = _
    rw [ih]

end BSeq

/- Section 5: Lifting linear isometries to `UniformSpace.Completion` -/

noncomputable def liftLinearIsometry {E₀ : Type*} [SeminormedAddCommGroup E₀]
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

lemma liftLinearIsometry_coe {E₀ : Type*} [SeminormedAddCommGroup E₀]
    [InnerProductSpace ℂ E₀] (f : E₀ →ₗᵢ[ℂ] E₀) (a : E₀) :
    liftLinearIsometry f (a : UniformSpace.Completion E₀) = (f a : UniformSpace.Completion E₀) :=
  UniformSpace.Completion.map_coe f.isometry.uniformContinuous a

/- Section 6: Asymptotic estimates for the lamp-group spectral projections -/

private lemma φ_inv_tendsto {W : Type} [Group W] {d : ℕ → ℕ}
    {φ : ∀ j, W → Matrix.unitaryGroup (Fin (d j)) ℂ}
    (hφ1 : ∀ j, φ j 1 = 1)
    (hmul : ∀ g h, Tendsto (fun j => opDist (φ j (g * h)) (φ j g * φ j h)) atTop (𝓝 0))
    (w : W) :
    Tendsto (fun j => opNorm ((φ j w⁻¹ : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ)) atTop (𝓝 0) := by
  have h0 := hmul w⁻¹ w
  rw [inv_mul_cancel] at h0
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) h0
  have heq : (φ j w⁻¹ : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ =
      ((φ j w⁻¹ : Matrix (Fin (d j)) (Fin (d j)) ℂ) * (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
        (φ j 1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) *
        (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hφ1]
    have hu : (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
        (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (φ j w).2
    rw [hu, Matrix.mul_one, Submonoid.coe_one, Matrix.one_mul]
  rw [heq]
  calc opNorm (((φ j w⁻¹ : Matrix (Fin (d j)) (Fin (d j)) ℂ) * (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          (φ j 1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) *
          (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ)
      ≤ opNorm ((φ j w⁻¹ : Matrix (Fin (d j)) (Fin (d j)) ℂ) * (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          (φ j 1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) *
          opNorm (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ := opNorm_mul_le _ _
    _ ≤ opNorm ((φ j 1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          ((φ j w⁻¹ * φ j w : Matrix.unitaryGroup (Fin (d j)) ℂ) : Matrix (Fin (d j)) (Fin (d j)) ℂ)) * 1 := by
        have hneg : opNorm ((φ j w⁻¹ : Matrix (Fin (d j)) (Fin (d j)) ℂ) * (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
            (φ j 1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) =
            opNorm ((φ j 1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
              ((φ j w⁻¹ * φ j w : Matrix.unitaryGroup (Fin (d j)) ℂ) : Matrix (Fin (d j)) (Fin (d j)) ℂ)) := by
          rw [← opNorm_neg, neg_sub]; rfl
        rw [hneg]
        exact mul_le_mul_of_nonneg_left (opNorm_unitary_conjTranspose_le_one (φ j w)) (opNorm_nonneg _)
    _ = opDist (φ j 1) (φ j w⁻¹ * φ j w) := by rw [mul_one, opNorm_sub_eq_opDist]

private noncomputable def hermPart {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • (M + Mᴴ)

private lemma hermPart_isHermitian {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    (hermPart M).IsHermitian := by
  change (((1 / 2 : ℝ) : ℂ) • (M + Mᴴ))ᴴ = ((1 / 2 : ℝ) : ℂ) • (M + Mᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
    Complex.star_def, Complex.conj_ofReal, add_comm]

private lemma hermPart_one {m : ℕ} : hermPart (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  unfold hermPart
  rw [Matrix.conjTranspose_one, smul_add, ← add_smul]
  have h12 : (((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ)) = 1 := by norm_num
  rw [h12, one_smul]

private lemma hermPart_opNorm_le_one {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm (hermPart (u : Matrix (Fin m) (Fin m) ℂ)) ≤ 1 := by
  unfold hermPart
  rw [opNorm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 := opNorm_unitary_le_one u
  have h2 := opNorm_unitary_conjTranspose_le_one u
  linarith [opNorm_add_le (u : Matrix (Fin m) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ]

private lemma alg_half_sub {α : Type*} [AddCommGroup α] [Module ℂ α] (A B : α) :
    ((1 / 2 : ℝ) : ℂ) • (A + B) - A = -(((1 / 2 : ℝ) : ℂ) • (A - B)) := by
  push_cast; module

private lemma alg_sq_split {R : Type*} [Ring R] (H B : R) :
    H * H - 1 = (H - B) * H + B * (H - B) + (B * B - 1) := by
  rw [sub_mul, mul_sub]; abel

private lemma invol_hermPart_diff {W : Type} [Group W] {d : ℕ → ℕ}
    {φ : ∀ j, W → Matrix.unitaryGroup (Fin (d j)) ℂ}
    (hφ1 : ∀ j, φ j 1 = 1)
    (hmul : ∀ g h, Tendsto (fun j => opDist (φ j (g * h)) (φ j g * φ j h)) atTop (𝓝 0))
    {w : W} (hw : w * w = 1) :
    Tendsto (fun j => opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ))) atTop (𝓝 0) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  have h0 := φ_inv_tendsto hφ1 hmul w
  rw [hwinv] at h0
  have hhalf : Tendsto (fun j => (1 / 2 : ℝ) * opNorm ((φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ)) atTop (𝓝 0) := by
    simpa using h0.const_mul (1 / 2 : ℝ)
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hhalf
  rw [hermPart, alg_half_sub, opNorm_neg, opNorm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

private lemma invol_hermPart_sq_diff {W : Type} [Group W] {d : ℕ → ℕ}
    {φ : ∀ j, W → Matrix.unitaryGroup (Fin (d j)) ℂ}
    (hφ1 : ∀ j, φ j 1 = 1)
    (hmul : ∀ g h, Tendsto (fun j => opDist (φ j (g * h)) (φ j g * φ j h)) atTop (𝓝 0))
    {w : W} (hw : w * w = 1) :
    Tendsto (fun j => opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - 1)) atTop (𝓝 0) := by
  have hHB := invol_hermPart_diff hφ1 hmul hw
  have hBsq : Tendsto (fun j => opNorm ((φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - 1)) atTop (𝓝 0) := by
    have h0 := hmul w w
    rw [hw] at h0
    refine h0.congr fun j => ?_
    rw [← opNorm_sub_eq_opDist, hφ1, Submonoid.coe_one, Submonoid.coe_mul]
    exact opNorm_sub_comm 1 ((φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) * (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ))
  have hsum : Tendsto (fun j =>
      opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) +
      opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) +
      opNorm ((φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) * (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - 1))
      atTop (𝓝 0) := by
    simpa using (hHB.add hHB).add hBsq
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
  rw [alg_sq_split (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)]
  have h1 : opNorm ((hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) * hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) ≤
      opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) :=
    (opNorm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (hermPart_opNorm_le_one (φ j w)) (opNorm_nonneg _)).trans (mul_one _).le)
  have h2 : opNorm ((φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ))) ≤
      opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) :=
    (opNorm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (opNorm_unitary_le_one (φ j w)) (opNorm_nonneg _)).trans (one_mul _).le)
  have h3 := opNorm_add_le
    ((hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) *
      hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) +
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
        (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)))
    ((φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) * (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - 1)
  have h4 := opNorm_add_le
    ((hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) *
      hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ))
    ((φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)))
  linarith

private lemma opNorm_tri_helper {m : ℕ} (P M H : Matrix (Fin m) (Fin m) ℂ)
    (hle : opNorm (1 - P - H) ≤ opNorm (H * H - 1)) :
    opNorm (P - (1 - M)) ≤ opNorm (H * H - 1) + opNorm (H - M) := by
  have hsplit : P - (1 - M) = -(1 - P - H) - (H - M) := by abel
  rw [hsplit]
  have h1 := opNorm_sub_le (-(1 - P - H)) (H - M)
  rw [opNorm_neg] at h1
  linarith

private lemma invol_proj_approx {W : Type} [Group W] {d : ℕ → ℕ}
    {φ : ∀ j, W → Matrix.unitaryGroup (Fin (d j)) ℂ}
    (hφ1 : ∀ j, φ j 1 = 1)
    (hmul : ∀ g h, Tendsto (fun j => opDist (φ j (g * h)) (φ j g * φ j h)) atTop (𝓝 0))
    {w : W} (hw : w * w = 1) :
    Tendsto (fun j => opNorm ((2 : ℂ) • negProj (hermPart_isHermitian (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)) -
      (1 - (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)))) atTop (𝓝 0) := by
  have hHB := invol_hermPart_diff hφ1 hmul hw
  have hHsq := invol_hermPart_sq_diff hφ1 hmul hw
  have hsum : Tendsto (fun j =>
      opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
        hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) - 1) +
      opNorm (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
        (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ))) atTop (𝓝 0) := by
    simpa using hHsq.add hHB
  exact squeeze_zero (fun j => opNorm_nonneg _)
    (fun j => opNorm_tri_helper
      ((2 : ℂ) • negProj (hermPart_isHermitian (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)))
      (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)
      (hermPart (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ))
      (opNorm_one_sub_two_negProj_sub_le (hermPart_isHermitian (φ j w : Matrix (Fin (d j)) (Fin (d j)) ℂ)))) hsum

private lemma conj_lamp_approx {G X W : Type} [Group G] [MulAction G X] [Group W]
    {r : G →* W} {a : X → W} (hact : ∀ g y, r g * a y = a (g • y) * r g)
    {d : ℕ → ℕ} {φ : ∀ j, W → Matrix.unitaryGroup (Fin (d j)) ℂ}
    (hmul : ∀ g h, Tendsto (fun j => opDist (φ j (g * h)) (φ j g * φ j h)) atTop (𝓝 0))
    (g : G) (y : X) :
    Tendsto (fun j => opNorm ((φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (φ j (a y) : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ -
      (φ j (a (g • y)) : Matrix (Fin (d j)) (Fin (d j)) ℂ))) atTop (𝓝 0) := by
  have h1 := hmul (r g) (a y)
  have h2 := hmul (a (g • y)) (r g)
  rw [hact g y] at h1
  have hsum : Tendsto (fun j =>
      opDist (φ j (a (g • y) * r g)) (φ j (r g) * φ j (a y)) +
      opDist (φ j (a (g • y) * r g)) (φ j (a (g • y)) * φ j (r g))) atTop (𝓝 0) := by
    simpa using h1.add h2
  refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
  have hu : (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (φ j (r g)).2
  have hsplit : (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (φ j (a y) : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
      (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ -
      (φ j (a (g • y)) : Matrix (Fin (d j)) (Fin (d j)) ℂ) =
      ((((φ j (r g) * φ j (a y) : Matrix.unitaryGroup (Fin (d j)) ℂ) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
        (φ j (a (g • y) * r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)) +
        ((φ j (a (g • y) * r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          ((φ j (a (g • y)) * φ j (r g) : Matrix.unitaryGroup (Fin (d j)) ℂ) :
            Matrix (Fin (d j)) (Fin (d j)) ℂ))) *
        (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ := by
    simp only [Submonoid.coe_mul, sub_add_sub_cancel, Matrix.sub_mul, Matrix.mul_assoc, hu, Matrix.mul_one]
  rw [hsplit]
  calc opNorm _
      ≤ opNorm ((((φ j (r g) * φ j (a y) : Matrix.unitaryGroup (Fin (d j)) ℂ) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          (φ j (a (g • y) * r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)) +
          ((φ j (a (g • y) * r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
            ((φ j (a (g • y)) * φ j (r g) : Matrix.unitaryGroup (Fin (d j)) ℂ) :
              Matrix (Fin (d j)) (Fin (d j)) ℂ))) *
        opNorm (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ := opNorm_mul_le _ _
    _ ≤ (opDist (φ j (a (g • y) * r g)) (φ j (r g) * φ j (a y)) +
          opDist (φ j (a (g • y) * r g)) (φ j (a (g • y)) * φ j (r g))) * 1 := by
        refine mul_le_mul ?_ (opNorm_unitary_conjTranspose_le_one (φ j (r g)))
          (opNorm_nonneg _) (by unfold opDist; positivity)
        refine (opNorm_add_le _ _).trans (add_le_add ?_ (le_of_eq (opNorm_sub_eq_opDist _ _)))
        rw [opNorm_sub_comm, opNorm_sub_eq_opDist]
    _ = _ := mul_one _

private lemma unitary_conj_opNorm_le {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) ≤ opNorm M := by
  calc opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ)
      ≤ opNorm ((u : Matrix (Fin m) (Fin m) ℂ) * M) * opNorm (u : Matrix (Fin m) (Fin m) ℂ)ᴴ :=
        opNorm_mul_le _ _
    _ ≤ (opNorm (u : Matrix (Fin m) (Fin m) ℂ) * opNorm M) * 1 :=
        mul_le_mul (opNorm_mul_le _ _) (opNorm_unitary_conjTranspose_le_one u)
          (opNorm_nonneg _) (mul_nonneg (opNorm_nonneg _) (opNorm_nonneg _))
    _ ≤ (1 * opNorm M) * 1 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (opNorm_unitary_le_one u) (opNorm_nonneg _)) zero_le_one
    _ = opNorm M := by ring

private noncomputable def unitary_equiv_lin {m : ℕ} (u : Matrix.unitaryGroup (Fin m) ℂ) :
    EuclideanSpace ℂ (Fin m) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  LinearEquiv.ofLinearMap
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)).toLinearMap
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ).toLinearMap
    (LinearMap.ext fun v => by
      have hu : (u : Matrix (Fin m) (Fin m) ℂ) * (u : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 :=
        Matrix.mem_unitaryGroup_iff.mp u.2
      change (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ) v = v
      rw [← map_mul, hu, map_one]; rfl)
    (LinearMap.ext fun v => by
      have hu : (u : Matrix (Fin m) (Fin m) ℂ)ᴴ * (u : Matrix (Fin m) (Fin m) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp u.2
      change (Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)ᴴ *
        Matrix.toEuclideanCLM (𝕜 := ℂ) (u : Matrix (Fin m) (Fin m) ℂ)) v = v
      rw [← map_mul, hu, map_one]; rfl)

private lemma rank_subadd_and_hs_bound {m : ℕ}
    (uA uG : Matrix.unitaryGroup (Fin m) ℂ)
    {H0 H1 H2 : Matrix (Fin m) (Fin m) ℂ}
    (h0 : H0.IsHermitian) (h1 : H1.IsHermitian) (h2 : H2.IsHermitian) :
    let T0 := (uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0
    let T1 := (uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1
    let T2 := (uG : Matrix (Fin m) (Fin m) ℂ) * ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) *
      (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ
    let D := T0 - (T1 + T2)
    (opNorm D < 1 → negRank h0 ≤ negRank h1 + negRank h2) ∧
    ‖toMatVec D‖ ^ 2 ≤ ((negRank h0 + negRank h1 + negRank h2 : ℕ) : ℝ) * opNorm D ^ 2 := by
  dsimp only
  let K0 := nonnegSubspace h0
  let K1 := nonnegSubspace h1
  let eU := unitary_equiv_lin uG
  let K2 := Submodule.map (eU : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)) (nonnegSubspace h2)
  have htot : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = m := by simp
  have hK0_dim : Module.finrank ℂ K0 = m - negRank h0 := finrank_nonnegSubspace h0
  have hK1_dim : Module.finrank ℂ K1 = m - negRank h1 := finrank_nonnegSubspace h1
  have hK2_dim : Module.finrank ℂ K2 = m - negRank h2 := by
    rw [LinearEquiv.finrank_map_eq, finrank_nonnegSubspace h2]
  have hK1_van : ∀ v ∈ K1, Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1) v = 0 := by
    intro v hv
    rw [map_mul]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (uA : Matrix (Fin m) (Fin m) ℂ)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj h1) v) = 0
    rw [negProj_apply_eq_zero_of_mem_nonnegSubspace h1 hv, map_zero]
  have hK2_van : ∀ v ∈ K2,
      Matrix.toEuclideanCLM (𝕜 := ℂ) ((uG : Matrix (Fin m) (Fin m) ℂ) *
        ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) * (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ) v = 0 := by
    rintro _ ⟨v, hv, rfl⟩
    have hcancel : Matrix.toEuclideanCLM (𝕜 := ℂ) (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ (eU v) = v := by
      have hu : (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ * (uG : Matrix (Fin m) (Fin m) ℂ) = 1 :=
        Matrix.mem_unitaryGroup_iff'.mp uG.2
      change (Matrix.toEuclideanCLM (𝕜 := ℂ) (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ *
        Matrix.toEuclideanCLM (𝕜 := ℂ) (uG : Matrix (Fin m) (Fin m) ℂ)) v = v
      rw [← map_mul, hu, map_one]; rfl
    rw [map_mul, map_mul, map_mul]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (uG : Matrix (Fin m) (Fin m) ℂ)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (uA : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj h2)
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ (eU v)))) = 0
    rw [hcancel, negProj_apply_eq_zero_of_mem_nonnegSubspace h2 hv, map_zero, map_zero]
  have hK12_sup : Module.finrank ℂ (K1 ⊔ K2 : Submodule ℂ _) ≤ m :=
    (Submodule.finrank_le _).trans_eq htot
  have hK12_eq := Submodule.finrank_sup_add_finrank_inf_eq K1 K2
  constructor
  · intro hlt
    let V := negSubspace h0
    have hV_dim : Module.finrank ℂ V = negRank h0 := finrank_negSubspace h0
    have hVK_sup : Module.finrank ℂ (V ⊔ (K1 ⊓ K2) : Submodule ℂ _) ≤ m :=
      (Submodule.finrank_le _).trans_eq htot
    have hVK_eq := Submodule.finrank_sup_add_finrank_inf_eq V (K1 ⊓ K2)
    by_contra hgt
    have hpos : 0 < Module.finrank ℂ (V ⊓ (K1 ⊓ K2) : Submodule ℂ _) := by omega
    have hne : (V ⊓ (K1 ⊓ K2) : Submodule ℂ _) ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hpos; omega
    obtain ⟨v, ⟨hvV, hvK1, hvK2⟩, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hDv : Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0 -
          ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1 +
            (uG : Matrix (Fin m) (Fin m) ℂ) * ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) *
              (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ)) v =
        Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0) v := by
      rw [map_sub, map_add]
      change Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0) v -
        (Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1) v +
          Matrix.toEuclideanCLM (𝕜 := ℂ) ((uG : Matrix (Fin m) (Fin m) ℂ) *
            ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) * (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ) v) = _
      rw [hK1_van v hvK1, hK2_van v hvK2, add_zero, sub_zero]
    have hTv_norm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0) v‖ = ‖v‖ := by
      rw [map_mul]
      change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (uA : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj h0) v)‖ = ‖v‖
      rw [negProj_apply_eq_self_of_mem_negSubspace h0 hvV]
      exact unitary_norm_mulVec uA v
    have hle := ContinuousLinearMap.le_opNorm
      (Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0 -
        ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1 +
          (uG : Matrix (Fin m) (Fin m) ℂ) * ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) *
            (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ))) v
    rw [hDv, hTv_norm] at hle
    have hlt' : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0 -
        ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1 +
          (uG : Matrix (Fin m) (Fin m) ℂ) * ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) *
            (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ))‖ < 1 := hlt
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    nlinarith
  · have hK_sup : Module.finrank ℂ (K0 ⊔ (K1 ⊓ K2) : Submodule ℂ _) ≤ m :=
      (Submodule.finrank_le _).trans_eq htot
    have hK_eq := Submodule.finrank_sup_add_finrank_inf_eq K0 (K1 ⊓ K2)
    have hK_orth := Submodule.finrank_add_finrank_orthogonal (K0 ⊓ (K1 ⊓ K2))
    rw [htot] at hK_orth
    have hKorth_le : Module.finrank ℂ (K0 ⊓ (K1 ⊓ K2))ᗮ ≤ negRank h0 + negRank h1 + negRank h2 := by omega
    have hvan : ∀ v ∈ (K0 ⊓ (K1 ⊓ K2) : Submodule ℂ _), Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0 -
          ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1 +
            (uG : Matrix (Fin m) (Fin m) ℂ) * ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) *
              (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ)) v = 0 := by
      rintro v ⟨hv0, hv1, hv2⟩
      rw [map_sub, map_add]
      change Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h0) v -
        (Matrix.toEuclideanCLM (𝕜 := ℂ) ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h1) v +
          Matrix.toEuclideanCLM (𝕜 := ℂ) ((uG : Matrix (Fin m) (Fin m) ℂ) *
            ((uA : Matrix (Fin m) (Fin m) ℂ) * negProj h2) * (uG : Matrix (Fin m) (Fin m) ℂ)ᴴ) v) = 0
      rw [hK1_van v hv1, hK2_van v hv2, add_zero, sub_zero, map_mul]
      change Matrix.toEuclideanCLM (𝕜 := ℂ) (uA : Matrix (Fin m) (Fin m) ℂ)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (negProj h0) v) = 0
      rw [negProj_apply_eq_zero_of_mem_nonnegSubspace h0 hv0, map_zero]
    exact (norm_toMatVec_le_of_vanish_on _ (K0 ⊓ (K1 ⊓ K2)) hvan).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKorth_le) (sq_nonneg _))

/- Section 7: Main proof of `H2` -/

theorem weighted_hs_proof : OMA.R_Green100_green_100_variants_operator_norm_R1.H2 := by
  classical
  intro G _ _ Γ hFG X _ _ x γ W _ _ r a hsq hcomm hact d φ hφ1 hmul hsep
  have hprod_sq : ∀ y z : X, (a y * a z) * (a y * a z) = 1 := by
    intro y z
    calc (a y * a z) * (a y * a z) = a y * (a z * a y) * a z := by group
      _ = a y * (a y * a z) * a z := by rw [(hcomm z y).eq]
      _ = (a y * a y) * (a z * a z) := by group
      _ = 1 := by rw [hsq y, hsq z, mul_one]
  let B : ∀ j, G → Matrix (Fin (d j)) (Fin (d j)) ℂ :=
    fun j g => (φ j (a (g • x) * a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ)
  let hH_herm : ∀ j g, (hermPart (B j g)).IsHermitian :=
    fun j g => hermPart_isHermitian (B j g)
  let q : ∀ j, G → Matrix (Fin (d j)) (Fin (d j)) ℂ := fun j g => negProj (hH_herm j g)
  let rk : ∀ j, G → ℕ := fun j g => negRank (hH_herm j g)
  let T : ∀ j, G → Matrix (Fin (d j)) (Fin (d j)) ℂ :=
    fun j g => (φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) * q j g
  let Conj : ∀ j, G → Matrix (Fin (d j)) (Fin (d j)) ℂ → Matrix (Fin (d j)) (Fin (d j)) ℂ :=
    fun j g M => (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ) * M *
      (φ j (r g) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ
  let cocDef : ∀ j, G → G → Matrix (Fin (d j)) (Fin (d j)) ℂ :=
    fun j g h => T j (g * h) - (T j g + Conj j g (T j h))
  -- Exact vanishing on stabilize
  have hT_fix : ∀ j (g : G), g • x = x → T j g = 0 := by
    intro j g hgx
    have hB1 : B j g = 1 := by simp only [B, hgx, hsq x, hφ1]; rfl
    have hH1 : hermPart (B j g) = 1 := by rw [hB1, hermPart_one]
    have hq0 : q j g = 0 := by
      have hsub : ∀ {M : Matrix (Fin (d j)) (Fin (d j)) ℂ} (hM : M.IsHermitian),
          M = 1 → negProj hM = 0 := by
        rintro M hM rfl; exact negProj_eq_zero_of_one hM
      exact hsub (hH_herm j g) hH1
    simp [T, hq0]
  -- Exact HS norm: ‖toMatVec (T j g)‖^2 = rk j g
  have hT_norm_sq : ∀ j g, ‖toMatVec (T j g)‖ ^ 2 = (rk j g : ℝ) := by
    intro j g
    have hre := congrArg (RCLike.re (K := ℂ)) (inner_toMatVec_unitary_mul_left (φ j (a x)) (q j g) (q j g))
    simp only [inner_self_eq_norm_sq] at hre
    exact hre.trans (norm_toMatVec_negProj_sq (hH_herm j g))
  -- ‖2 • q j g - (1 - B j g)‖_op → 0
  have h2q_tendsto : ∀ g : G, Tendsto (fun j => opNorm ((2 : ℂ) • q j g - (1 - B j g))) atTop (𝓝 0) :=
    fun g => invol_proj_approx hφ1 hmul (hprod_sq (g • x) x)
  -- Eventually rk j γ ≥ 1
  have hrk_gamma : ∀ᶠ j in atTop, 1 ≤ rk j (γ : G) := by
    have hlt := (h2q_tendsto (γ : G)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsep, hlt] with j hsepj hltj
    by_contra h0
    have hr0 : rk j (γ : G) = 0 := by omega
    have hq0 : q j (γ : G) = 0 := by
      have hn : ‖toMatVec (q j (γ : G))‖ ^ 2 = 0 := by
        rw [norm_toMatVec_negProj_sq (hH_herm j (γ : G))]
        exact_mod_cast hr0
      have hn0 : ‖toMatVec (q j (γ : G))‖ = 0 := by nlinarith [norm_nonneg (toMatVec (q j (γ : G)))]
      have hmv : toMatVec (q j (γ : G)) = 0 := norm_eq_zero.mp hn0
      rw [← ofMatVec_toMatVec (q j (γ : G)), hmv]
      ext i l; rfl
    rw [hq0, smul_zero, zero_sub, opNorm_neg] at hltj
    have hsepj' : 1 ≤ opNorm (1 - B j (γ : G)) := by
      have : opDist (φ j (a ((γ : G) • x) * a x)) 1 = opNorm (1 - B j (γ : G)) := by
        rw [← opNorm_sub_eq_opDist, Submonoid.coe_one]
        exact opNorm_sub_comm (B j (γ : G)) 1
      linarith
    linarith
  -- ‖2 • T j g - (φ j (a x) - φ j (a (g • x)))‖_op → 0
  have h2T_tendsto : ∀ g : G,
      Tendsto (fun j => opNorm ((2 : ℂ) • T j g - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
        (φ j (a (g • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ)))) atTop (𝓝 0) := by
    intro g
    have hmul_ax : a x * (a (g • x) * a x) = a (g • x) := by
      calc a x * (a (g • x) * a x) = (a x * a (g • x)) * a x := by group
        _ = (a (g • x) * a x) * a x := by rw [(hcomm x (g • x)).eq]
        _ = a (g • x) * (a x * a x) := by group
        _ = a (g • x) := by rw [hsq x, mul_one]
    have hm1 := hmul (a x) (a (g • x) * a x)
    rw [hmul_ax] at hm1
    have hsum : Tendsto (fun j => opNorm ((2 : ℂ) • q j g - (1 - B j g)) +
        opDist (φ j (a (g • x))) (φ j (a x) * φ j (a (g • x) * a x))) atTop (𝓝 0) := by
      simpa using (h2q_tendsto g).add hm1
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
    have hsplit : (2 : ℂ) • T j g - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
        (φ j (a (g • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ)) =
        (φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) * ((2 : ℂ) • q j g - (1 - B j g)) +
        ((φ j (a (g • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          ((φ j (a x) * φ j (a (g • x) * a x) : Matrix.unitaryGroup (Fin (d j)) ℂ) :
            Matrix (Fin (d j)) (Fin (d j)) ℂ)) := by
      dsimp only [T, B]
      rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Submonoid.coe_mul]
      abel
    rw [hsplit]
    have h1 : opNorm ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) * ((2 : ℂ) • q j g - (1 - B j g))) ≤
        opNorm ((2 : ℂ) • q j g - (1 - B j g)) :=
      (opNorm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (opNorm_unitary_le_one (φ j (a x))) (opNorm_nonneg _)).trans (one_mul _).le)
    exact (opNorm_add_le _ _).trans (add_le_add h1 (le_of_eq (opNorm_sub_eq_opDist _ _)))
  -- Cocycle defect in operator norm → 0
  have hcocDef_op : ∀ g h : G, Tendsto (fun j => opNorm (cocDef j g h)) atTop (𝓝 0) := by
    intro g h
    have hsum : Tendsto (fun j => (1 / 2 : ℝ) * (
        opNorm ((2 : ℂ) • T j (g * h) - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          (φ j (a ((g * h) • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ))) +
        opNorm ((2 : ℂ) • T j g - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          (φ j (a (g • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ))) +
        opNorm ((2 : ℂ) • T j h - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
          (φ j (a (h • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ))) +
        opNorm (Conj j g (φ j (a x)) - (φ j (a (g • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ)) +
        opNorm (Conj j g (φ j (a (h • x))) - (φ j (a (g • (h • x))) : Matrix (Fin (d j)) (Fin (d j)) ℂ))))
        atTop (𝓝 0) := by
      simpa using (((((h2T_tendsto (g * h)).add (h2T_tendsto g)).add
        (h2T_tendsto h)).add (conj_lamp_approx hact hmul g x)).add
          (conj_lamp_approx hact hmul g (h • x))).const_mul (1 / 2 : ℝ)
    refine squeeze_zero (fun j => opNorm_nonneg _) (fun j => ?_) hsum
    let A1 := (2 : ℂ) • T j (g * h) - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j (a ((g * h) • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ))
    let A2 := (2 : ℂ) • T j g - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j (a (g • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ))
    let A3 := (2 : ℂ) • T j h - ((φ j (a x) : Matrix (Fin (d j)) (Fin (d j)) ℂ) -
      (φ j (a (h • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ))
    let A4 := Conj j g (φ j (a x)) - (φ j (a (g • x)) : Matrix (Fin (d j)) (Fin (d j)) ℂ)
    let A5 := Conj j g (φ j (a (h • x))) - (φ j (a (g • (h • x))) : Matrix (Fin (d j)) (Fin (d j)) ℂ)
    have h2eq : (2 : ℂ) • cocDef j g h = A1 - A2 - Conj j g A3 - A4 + A5 := by
      have hact_mul : (g * h) • x = g • (h • x) := mul_smul g h x
      dsimp only [cocDef, Conj, A1, A2, A3, A4, A5]
      rw [hact_mul, smul_sub, smul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul]
      abel
    have h2norm : 2 * opNorm (cocDef j g h) = opNorm (A1 - A2 - Conj j g A3 - A4 + A5) := by
      rw [← h2eq, opNorm_smul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hC3 : opNorm (Conj j g A3) ≤ opNorm A3 := unitary_conj_opNorm_le (φ j (r g)) A3
    have t1 := opNorm_add_le (A1 - A2 - Conj j g A3 - A4) A5
    have t2 := opNorm_sub_le (A1 - A2 - Conj j g A3) A4
    have t3 := opNorm_sub_le (A1 - A2) (Conj j g A3)
    have t4 := opNorm_sub_le A1 A2
    linarith
  -- Rank subadditivity and HS cocycle defect bound
  have hrk_subadd : ∀ g h : G, ∀ᶠ j in atTop, rk j (g * h) ≤ rk j g + rk j h := by
    intro g h
    filter_upwards [(hcocDef_op g h).eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with j hlt
    exact (rank_subadd_and_hs_bound (φ j (a x)) (φ j (r g))
      (hH_herm j (g * h)) (hH_herm j g) (hH_herm j h)).1 hlt
  have hcocDef_hs : ∀ (j : ℕ) (g h : G),
      ‖toMatVec (cocDef j g h)‖ ^ 2 ≤
        ((rk j (g * h) + rk j g + rk j h : ℕ) : ℝ) * opNorm (cocDef j g h) ^ 2 :=
    fun j g h => (rank_subadd_and_hs_bound (φ j (a x)) (φ j (r g))
      (hH_herm j (g * h)) (hH_herm j g) (hH_herm j h)).2
  -- Finite symmetric generating set S of Γ containing γ
  obtain ⟨S₀, hS₀⟩ := hFG.out
  let S : Finset Γ := insert γ (insert γ⁻¹ (S₀ ∪ S₀.image (·⁻¹)))
  have hγS : γ ∈ S := Finset.mem_insert_self _ _
  have hS_symm : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hs ⊢
    rcases hs with rfl | rfl | hs | ⟨t, ht, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (inv_inv γ)
    · exact Or.inr (Or.inr (Or.inr ⟨s, hs, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl (by simpa using ht)))
  have hS_gen : Subgroup.closure (S : Set Γ) = ⊤ := by
    rw [eq_top_iff, ← hS₀]
    refine Subgroup.closure_mono ?_
    intro s hs
    simp [S, hs]
  have hS_monoid : ∀ g : Γ, g ∈ Submonoid.closure (S : Set Γ) := by
    have hinv : ∀ u ∈ Submonoid.closure (S : Set Γ), u⁻¹ ∈ Submonoid.closure (S : Set Γ) := by
      intro u hu
      induction hu using Submonoid.closure_induction with
      | mem s hs => exact Submonoid.subset_closure (hS_symm s hs)
      | one => rw [inv_one]; exact Submonoid.one_mem _
      | mul u1 u2 _ _ h1 h2 => rw [_root_.mul_inv_rev]; exact Submonoid.mul_mem _ h2 h1
    intro g
    have hg : g ∈ Subgroup.closure (S : Set Γ) := by rw [hS_gen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact Submonoid.subset_closure hs
    | one => exact Submonoid.one_mem _
    | mul u v _ _ hu hv => exact Submonoid.mul_mem _ hu hv
    | inv u _ hu => exact hinv u hu
  let wt : ℕ → ℝ := fun j => ∑ s ∈ S, (rk j (s : G) : ℝ)
  have hwt_ge_one : ∀ᶠ j in atTop, 1 ≤ wt j := by
    filter_upwards [hrk_gamma] with j hj
    have hterm : (rk j (γ : G) : ℝ) ≤ ∑ s ∈ S, (rk j (s : G) : ℝ) :=
      Finset.single_le_sum (f := fun s : Γ => (rk j (s : G) : ℝ))
        (fun s _ => Nat.cast_nonneg _) hγS
    have h1 : (1 : ℝ) ≤ (rk j (γ : G) : ℝ) := by exact_mod_cast hj
    exact h1.trans hterm
  have hrk_le_wt : ∀ g : Γ, ∃ C : ℕ, ∀ᶠ j in atTop, rk j (g : G) ≤ C * ∑ s ∈ S, rk j (s : G) := by
    intro g
    have hgm := hS_monoid g
    induction hgm using Submonoid.closure_induction with
    | mem s hs =>
      refine ⟨1, Filter.Eventually.of_forall fun j => ?_⟩
      rw [one_mul]
      exact Finset.single_le_sum (f := fun s : Γ => rk j (s : G)) (fun _ _ => Nat.zero_le _) hs
    | one =>
      refine ⟨0, Filter.Eventually.of_forall fun j => ?_⟩
      have hT1 : T j (1 : G) = 0 := hT_fix j 1 (one_smul G x)
      have hn : ‖toMatVec (T j 1)‖ ^ 2 = 0 := by
        rw [hT1, toMatVec_zero, norm_zero, zero_pow two_ne_zero]
      rw [hT_norm_sq j 1] at hn
      have hr0 : rk j 1 = 0 := by exact_mod_cast hn
      simp [hr0]
    | mul u v _ _ h1' h2' =>
      rcases h1' with ⟨C1, h1⟩
      rcases h2' with ⟨C2, h2⟩
      refine ⟨C1 + C2, ?_⟩
      filter_upwards [hrk_subadd (u : G) (v : G), h1, h2] with j hsub h1j h2j
      change rk j ((u : G) * (v : G)) ≤ (C1 + C2) * ∑ s ∈ S, rk j (s : G)
      rw [add_mul]
      omega
  -- Construct the Hilbert space E = Completion (BSeq d)
  let E : Type := UniformSpace.Completion (BSeq d)
  let ρ0Fun : G → BSeq d → BSeq d := fun g f =>
    ⟨fun j => toMatVec (Conj j g (ofMatVec (f.seq j))), by
      obtain ⟨C, hC⟩ := f.bdd
      refine ⟨C, fun j => ?_⟩
      have hnorm : ‖toMatVec (Conj j g (ofMatVec (f.seq j)))‖ = ‖f.seq j‖ := by
        simpa [Conj, toMatVec_ofMatVec] using norm_toMatVec_conj (φ j (r g)) (ofMatVec (f.seq j))
      rw [hnorm]; exact hC j⟩
  let ρ0 : G → (BSeq d →ₗᵢ[ℂ] BSeq d) := fun g =>
    { toFun := ρ0Fun g
      map_add' := fun f1 f2 => BSeq.ext fun j => by
        change toMatVec (Conj j g (ofMatVec (f1.seq j + f2.seq j))) =
          toMatVec (Conj j g (ofMatVec (f1.seq j))) + toMatVec (Conj j g (ofMatVec (f2.seq j)))
        rw [← toMatVec_add]
        congr 1
        have hof : ofMatVec (f1.seq j + f2.seq j) = ofMatVec (f1.seq j) + ofMatVec (f2.seq j) := by
          ext i l; rfl
        rw [hof]; simp [Conj, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun s f => BSeq.ext fun j => by
        change toMatVec (Conj j g (ofMatVec (s • f.seq j))) =
          s • toMatVec (Conj j g (ofMatVec (f.seq j)))
        rw [← toMatVec_smul]
        congr 1
        have hof : ofMatVec (s • f.seq j) = s • ofMatVec (f.seq j) := by
          ext i l; rfl
        rw [hof]; simp [Conj]
      norm_map' := fun f => by
        change ‖ρ0Fun g f‖ = ‖f‖
        have h1 := BSeq.tendsto_norm_sq (ρ0Fun g f)
        have h2 := BSeq.tendsto_norm_sq f
        have hfun : (fun j => ‖(ρ0Fun g f).seq j‖ ^ 2) = (fun j => ‖f.seq j‖ ^ 2) := by
          funext j
          have hn : ‖toMatVec (Conj j g (ofMatVec (f.seq j)))‖ = ‖f.seq j‖ := by
            simpa [Conj, toMatVec_ofMatVec] using norm_toMatVec_conj (φ j (r g)) (ofMatVec (f.seq j))
          change ‖toMatVec (Conj j g (ofMatVec (f.seq j)))‖ ^ 2 = ‖f.seq j‖ ^ 2
          rw [hn]
        rw [hfun] at h1
        have hsq : ‖ρ0Fun g f‖ ^ 2 = ‖f‖ ^ 2 := tendsto_nhds_unique h1 h2
        nlinarith [norm_nonneg (ρ0Fun g f), norm_nonneg f] }
  let ρ1 : G → (E →ₗᵢ[ℂ] E) := fun g => liftLinearIsometry (ρ0 g)
  have hρ1_one : ∀ v : E, ρ1 1 v = v := by
    intro v
    refine UniformSpace.Completion.induction_on v ?_ fun f => ?_
    · exact isClosed_eq (ρ1 1).continuous continuous_id
    · rw [liftLinearIsometry_coe]
      congr 1
      refine BSeq.ext fun j => ?_
      change toMatVec (Conj j 1 (ofMatVec (f.seq j))) = f.seq j
      simp [Conj, map_one, hφ1, toMatVec_ofMatVec]
  have hρ1_mul : ∀ g h : G, ∀ v : E, ρ1 (g * h) v = ρ1 g (ρ1 h v) := by
    intro g h v
    refine UniformSpace.Completion.induction_on v ?_ fun f => ?_
    · exact isClosed_eq (ρ1 (g * h)).continuous ((ρ1 g).continuous.comp (ρ1 h).continuous)
    · rw [liftLinearIsometry_coe, liftLinearIsometry_coe, liftLinearIsometry_coe]
      rw [← sub_eq_zero, ← norm_eq_zero, ← UniformSpace.Completion.coe_sub,
        UniformSpace.Completion.norm_coe]
      refine BSeq.norm_eq_zero_of_tendsto_zero (ρ0 (g * h) f - ρ0 g (ρ0 h f)) ?_
      obtain ⟨C, hC⟩ := f.bdd
      have hbound : Tendsto (fun j => 2 * opDist (φ j (r g * r h)) (φ j (r g) * φ j (r h)) * max C 0)
          atTop (𝓝 0) := by
        simpa using ((hmul (r g) (r h)).const_mul 2).mul_const (max C 0)
      refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hbound
      change ‖toMatVec (Conj j (g * h) (ofMatVec (f.seq j))) -
          toMatVec (Conj j g (ofMatVec (toMatVec (Conj j h (ofMatVec (f.seq j))))))‖ ≤ _
      rw [ofMatVec_toMatVec, ← toMatVec_sub]
      have hsub_eq : Conj j (g * h) (ofMatVec (f.seq j)) - Conj j g (Conj j h (ofMatVec (f.seq j))) =
          (φ j (r (g * h)) : Matrix (Fin (d j)) (Fin (d j)) ℂ) * ofMatVec (f.seq j) *
            (φ j (r (g * h)) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ -
          ((φ j (r g) * φ j (r h) : Matrix.unitaryGroup (Fin (d j)) ℂ) : Matrix (Fin (d j)) (Fin (d j)) ℂ) *
            ofMatVec (f.seq j) *
            ((φ j (r g) * φ j (r h) : Matrix.unitaryGroup (Fin (d j)) ℂ) : Matrix (Fin (d j)) (Fin (d j)) ℂ)ᴴ := by
        simp [Conj, Submonoid.coe_mul, Matrix.mul_assoc, Matrix.conjTranspose_mul]
      rw [hsub_eq, map_mul]
      have hstep := norm_toMatVec_conj_diff_le (φ j (r g * r h)) (φ j (r g) * φ j (r h)) (ofMatVec (f.seq j))
      rw [toMatVec_ofMatVec] at hstep
      exact hstep.trans (mul_le_mul_of_nonneg_left ((hC j).trans (le_max_left C 0)) (by unfold opDist; positivity))
  let ρEquiv : G → (E ≃ₗᵢ[ℂ] E) := fun g =>
    { toLinearEquiv :=
        { toFun := ρ1 g
          invFun := ρ1 g⁻¹
          left_inv := fun v => by rw [← hρ1_mul g⁻¹ g v, inv_mul_cancel, hρ1_one]
          right_inv := fun v => by rw [← hρ1_mul g g⁻¹ v, mul_inv_cancel, hρ1_one]
          map_add' := (ρ1 g).map_add
          map_smul' := (ρ1 g).map_smul }
      norm_map' := (ρ1 g).norm_map }
  let ρ : G →* (E ≃ₗᵢ[ℂ] E) :=
    { toFun := ρEquiv
      map_one' := by ext v; exact hρ1_one v
      map_mul' := fun g h => by ext v; exact hρ1_mul g h v }
  -- Construct the rescaled cocycle c : Γ → E
  let cRaw : Γ → ∀ j : ℕ, matVec (d j) := fun g j =>
    if wt j = 0 then 0 else (((Real.sqrt (wt j))⁻¹ : ℝ) : ℂ) • toMatVec (T j (g : G))
  have hcRaw_bdd : ∀ g : Γ, ∃ C : ℝ, ∀ j : ℕ, ‖cRaw g j‖ ≤ C := by
    intro g
    obtain ⟨Cg, hCg⟩ := hrk_le_wt g
    refine bdd_of_eventually_bdd ⟨Real.sqrt (Cg : ℝ), ?_⟩
    filter_upwards [hwt_ge_one, hCg] with j hwt1 hle
    have hwt_pos : 0 < wt j := by linarith
    have hwt_ne : wt j ≠ 0 := hwt_pos.ne'
    simp only [cRaw, hwt_ne, ↓reduceIte, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have hsq : ((Real.sqrt (wt j))⁻¹ * ‖toMatVec (T j (g : G))‖) ^ 2 ≤ (Real.sqrt (Cg : ℝ)) ^ 2 := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hwt_pos.le, Real.sq_sqrt (Nat.cast_nonneg Cg),
        hT_norm_sq j (g : G), inv_mul_le_iff₀ hwt_pos, mul_comm]
      have hcast : (rk j (g : G) : ℝ) ≤ ((Cg * ∑ s ∈ S, rk j (s : G) : ℕ) : ℝ) := by exact_mod_cast hle
      simpa [wt, Nat.cast_sum] using hcast
    nlinarith [mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (wt j))) (norm_nonneg (toMatVec (T j (g : G)))),
      Real.sqrt_nonneg (Cg : ℝ)]
  let cSeq : Γ → BSeq d := fun g => ⟨cRaw g, hcRaw_bdd g⟩
  let c : Γ → E := fun g => (cSeq g : E)
  -- Cocycle identity
  have hc_cocycle : ∀ g h : Γ, c (g * h) = c g + ρ (g : G) (c h) := by
    intro g h
    change (cSeq (g * h) : E) = (cSeq g : E) + ρ1 (g : G) (cSeq h : E)
    rw [liftLinearIsometry_coe, ← UniformSpace.Completion.coe_add,
      ← sub_eq_zero, ← norm_eq_zero, ← UniformSpace.Completion.coe_sub,
      UniformSpace.Completion.norm_coe]
    refine BSeq.norm_eq_zero_of_tendsto_zero (cSeq (g * h) - (cSeq g + ρ0 (g : G) (cSeq h))) ?_
    obtain ⟨Cg, hCg⟩ := hrk_le_wt g
    obtain ⟨Ch, hCh⟩ := hrk_le_wt h
    let Kconst : ℝ := Real.sqrt (2 * ((Cg : ℝ) + (Ch : ℝ)))
    have hlim : Tendsto (fun j => Kconst * opNorm (cocDef j (g : G) (h : G))) atTop (𝓝 0) := by
      simpa using (hcocDef_op (g : G) (h : G)).const_mul Kconst
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hwt_ge_one, hCg, hCh, hrk_subadd (g : G) (h : G)] with j hwt1 hgj hhj hsub
    have hwt_pos : 0 < wt j := by linarith
    have hwt_ne : wt j ≠ 0 := hwt_pos.ne'
    have hseq : (cSeq (g * h) - (cSeq g + ρ0 (g : G) (cSeq h))).seq j =
        (((Real.sqrt (wt j))⁻¹ : ℝ) : ℂ) • toMatVec (cocDef j (g : G) (h : G)) := by
      change cRaw (g * h) j - (cRaw g j + toMatVec (Conj j (g : G) (ofMatVec (cRaw h j)))) = _
      simp only [cRaw, hwt_ne, ↓reduceIte, Subgroup.coe_mul]
      have hof : ofMatVec ((((Real.sqrt (wt j))⁻¹ : ℝ) : ℂ) • toMatVec (T j (h : G))) =
          (((Real.sqrt (wt j))⁻¹ : ℝ) : ℂ) • T j (h : G) := by
        rw [← toMatVec_smul, ofMatVec_toMatVec]
      rw [hof]
      simp only [Conj, Matrix.mul_smul, Matrix.smul_mul, toMatVec_smul, ← smul_add, ← smul_sub,
        ← toMatVec_add, ← toMatVec_sub, cocDef]
    rw [hseq, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have hsq : ((Real.sqrt (wt j))⁻¹ * ‖toMatVec (cocDef j (g : G) (h : G))‖) ^ 2 ≤
        (Kconst * opNorm (cocDef j (g : G) (h : G))) ^ 2 := by
      rw [mul_pow, mul_pow, inv_pow, Real.sq_sqrt hwt_pos.le,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * ((Cg : ℝ) + (Ch : ℝ))), inv_mul_le_iff₀ hwt_pos]
      have hhs := hcocDef_hs j (g : G) (h : G)
      have hsum_rk : ((rk j ((g : G) * (h : G)) + rk j (g : G) + rk j (h : G) : ℕ) : ℝ) ≤
          2 * ((Cg : ℝ) + (Ch : ℝ)) * wt j := by
        have hnat : rk j ((g : G) * (h : G)) + rk j (g : G) + rk j (h : G) ≤
            2 * (Cg + Ch) * ∑ s ∈ S, rk j (s : G) := by
          have hgh : rk j (g : G) + rk j (h : G) ≤ (Cg + Ch) * ∑ s ∈ S, rk j (s : G) := by
            rw [add_mul]; omega
          rw [mul_assoc, two_mul]
          omega
        have hcast : ((rk j ((g : G) * (h : G)) + rk j (g : G) + rk j (h : G) : ℕ) : ℝ) ≤
            ((2 * (Cg + Ch) * ∑ s ∈ S, rk j (s : G) : ℕ) : ℝ) := by exact_mod_cast hnat
        simpa [wt, Nat.cast_sum, mul_assoc] using hcast
      calc ‖toMatVec (cocDef j (g : G) (h : G))‖ ^ 2
          ≤ ((rk j ((g : G) * (h : G)) + rk j (g : G) + rk j (h : G) : ℕ) : ℝ) *
              opNorm (cocDef j (g : G) (h : G)) ^ 2 := hhs
        _ ≤ (2 * ((Cg : ℝ) + (Ch : ℝ)) * wt j) * opNorm (cocDef j (g : G) (h : G)) ^ 2 :=
            mul_le_mul_of_nonneg_right hsum_rk (sq_nonneg _)
        _ = wt j * (2 * ((Cg : ℝ) + (Ch : ℝ)) * opNorm (cocDef j (g : G) (h : G)) ^ 2) := by ring
    nlinarith [mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (wt j)))
        (norm_nonneg (toMatVec (cocDef j (g : G) (h : G)))),
      mul_nonneg (Real.sqrt_nonneg (2 * ((Cg : ℝ) + (Ch : ℝ)))) (opNorm_nonneg (cocDef j (g : G) (h : G)))]
  -- Stabilizer vanishing
  have hc_fix : ∀ g : Γ, (g : G) • x = x → c g = 0 := by
    intro g hgx
    have hzero : cSeq g = 0 := BSeq.ext fun j => by
      simp only [cSeq, cRaw, hT_fix j (g : G) hgx, toMatVec_zero, smul_zero, ite_self]
      rfl
    change (cSeq g : E) = 0
    rw [hzero]; rfl
  -- Non-vanishing
  have hc_nonzero : ∃ g : Γ, c g ≠ 0 := by
    have hsum1 : ∑ s ∈ S, ‖c s‖ ^ 2 = 1 := by
      have ht1 : Tendsto (fun j => ∑ s ∈ S, ‖(cSeq s).seq j‖ ^ 2) (Filter.hyperfilter ℕ)
          (𝓝 (∑ s ∈ S, ‖cSeq s‖ ^ 2)) :=
        tendsto_finsetSum S fun s _ => BSeq.tendsto_norm_sq (cSeq s)
      have ht2 : Tendsto (fun j => ∑ s ∈ S, ‖(cSeq s).seq j‖ ^ 2) (Filter.hyperfilter ℕ) (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hwt_ge_one.filter_mono hyperfilter_le_atTop] with j hwt1
        have hwt_pos : 0 < wt j := by linarith
        have hwt_ne : wt j ≠ 0 := hwt_pos.ne'
        symm
        calc ∑ s ∈ S, ‖(cSeq s).seq j‖ ^ 2
            = ∑ s ∈ S, (wt j)⁻¹ * (rk j (s : G) : ℝ) := by
              refine Finset.sum_congr rfl fun s _ => ?_
              simp only [cSeq, cRaw, hwt_ne, ↓reduceIte, norm_smul, Complex.norm_real,
                Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow, inv_pow,
                Real.sq_sqrt hwt_pos.le, hT_norm_sq j (s : G)]
          _ = (wt j)⁻¹ * ∑ s ∈ S, (rk j (s : G) : ℝ) := (Finset.mul_sum _ _ _).symm
          _ = (wt j)⁻¹ * wt j := rfl
          _ = 1 := inv_mul_cancel₀ hwt_ne
      have heq : ∑ s ∈ S, ‖cSeq s‖ ^ 2 = 1 := tendsto_nhds_unique ht1 ht2
      rw [← heq]
      refine Finset.sum_congr rfl fun s _ => ?_
      change ‖(cSeq s : E)‖ ^ 2 = ‖cSeq s‖ ^ 2
      rw [UniformSpace.Completion.norm_coe]
    by_contra hall
    push Not at hall
    have h0 : ∑ s ∈ S, ‖c s‖ ^ 2 = 0 := Finset.sum_eq_zero fun s _ => by simp [hall s]
    linarith
  -- Matrix models n j = d j * d j, U j g = kronConjUnitary (φ j (r g))
  let n : ℕ → ℕ := fun j => d j * d j
  let U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ := fun j g => kronConjUnitary (φ j (r g))
  have hU_mul : ∀ g h : G, Tendsto (fun j => opDist (U j (g * h)) (U j g * U j h)) atTop (𝓝 0) := by
    intro g h
    have h0 : Tendsto (fun j => 2 * opDist (φ j (r g * r h)) (φ j (r g) * φ j (r h))) atTop (𝓝 0) := by
      simpa using (hmul (r g) (r h)).const_mul 2
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h0
    simpa only [U, map_mul] using opDist_kronConj_le (φ j (r (g * h))) (φ j (r g)) (φ j (r h))
  -- Norm domination bound
  have hU_dom : ∀ (A : Finset G) (z : G → ℂ) (b : ℝ),
      (∀ᶠ j in atTop, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (∑ g ∈ A, z g • (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ))‖ ≤ b) →
      ∀ v : E, ‖∑ g ∈ A, z g • ρ g v‖ ≤ b * ‖v‖ := by
    intro A z b hb v
    have hb0 : 0 ≤ b := by
      obtain ⟨j, hj⟩ := hb.exists
      exact (norm_nonneg _).trans hj
    refine UniformSpace.Completion.induction_on v ?_ fun f => ?_
    · refine isClosed_le ?_ (continuous_const.mul continuous_norm)
      refine continuous_norm.comp ?_
      exact continuous_finsetSum A fun g _ => (continuous_const_smul (z g)).comp (ρ g).continuous
    · let F : BSeq d := ∑ g ∈ A, z g • ρ0 g f
      have hFcoe : ∑ g ∈ A, z g • ρ g (f : E) = (F : E) := by
        have hstep : ∀ (s : Finset G), ∑ g ∈ s, z g • ρ g (f : E) = ((∑ g ∈ s, z g • ρ0 g f : BSeq d) : E) := by
          intro s
          induction s using Finset.induction_on with
          | empty => rfl
          | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
              UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul]
            congr 2
            exact liftLinearIsometry_coe (ρ0 a) f
        exact hstep A
      rw [hFcoe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      have hsq : ‖F‖ ^ 2 ≤ (b * ‖f‖) ^ 2 := by
        have h1 := BSeq.tendsto_norm_sq F
        have h2 : Tendsto (fun j => b ^ 2 * ‖f.seq j‖ ^ 2) (Filter.hyperfilter ℕ) (𝓝 (b ^ 2 * ‖f‖ ^ 2)) :=
          (BSeq.tendsto_norm_sq f).const_mul (b ^ 2)
        rw [mul_pow]
        refine le_of_tendsto_of_tendsto h1 h2 ?_
        filter_upwards [hb.filter_mono hyperfilter_le_atTop] with j hbj
        have hFseq : F.seq j = toMatVec (∑ g ∈ A, z g • Conj j g (ofMatVec (f.seq j))) := by
          simp only [F, BSeq.seq_sum, toMatVec_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          change z g • toMatVec (Conj j g (ofMatVec (f.seq j))) = _
          rw [toMatVec_smul]
        have heq_vec : matVecEquiv (d j) (F.seq j) =
            Matrix.toEuclideanCLM (𝕜 := ℂ)
              (∑ g ∈ A, z g • (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ))
              (matVecEquiv (d j) (f.seq j)) := by
          rw [hFseq, toMatVec_sum, map_sum, map_sum, _root_.sum_apply]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [toMatVec_smul, map_smul, map_smul, _root_.smul_apply]
          congr 1
          have happly := toEuclideanCLM_kronConj_apply (φ j (r g)) (ofMatVec (f.seq j))
          rw [toMatVec_ofMatVec] at happly
          exact happly.symm
        have hle_norm : ‖F.seq j‖ ≤ b * ‖f.seq j‖ := by
          rw [← (matVecEquiv (d j)).norm_map (F.seq j), heq_vec]
          calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
                (∑ g ∈ A, z g • (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ))
                (matVecEquiv (d j) (f.seq j))‖
              ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
                  (∑ g ∈ A, z g • (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ))‖ *
                ‖matVecEquiv (d j) (f.seq j)‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ b * ‖f.seq j‖ := by
                rw [(matVecEquiv (d j)).norm_map]
                exact mul_le_mul_of_nonneg_right hbj (norm_nonneg _)
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hle_norm 2
      nlinarith [norm_nonneg F, mul_nonneg hb0 (norm_nonneg f)]
  exact ⟨E, inferInstance, inferInstance, inferInstance, ρ, c,
    hc_cocycle, hc_fix, hc_nonzero, n, U, hU_mul, hU_dom⟩

end OMA.Green100WeightedHS

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1.H2 :=
  OMA.Green100WeightedHS.weighted_hs_proof
