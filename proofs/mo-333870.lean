import OMAStatements.S_mo_333870

-- Problem: Minimum and maximum eigenvalue
-- Upstream: formal-conjectures statements/mo-333870.lean:0 (declaration OMA.S_mo_333870.main)
-- Credit: @umarsxlim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped InnerProductSpace RealInnerProductSpace BigOperators
open InnerProductSpace Matrix

theorem OMA.solution : type_of% @OMA.S_mo_333870.main := by
  intro n A hA y _hy
  let z : Fin (n + 2) → ℝ := A *ᵥ WithLp.ofLp y
  have hMsymm : (OMA.S_mo_333870.schurMatrix A y).IsHermitian := by
    ext i j
    have hAij : A j i = A i j := by
      have h := congrFun (congrFun hA.1 i) j
      simpa [Matrix.conjTranspose_apply] using h
    simp only [OMA.S_mo_333870.schurMatrix, Matrix.conjTranspose_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, star_trivial, hAij]
    ring
  have hM : (OMA.S_mo_333870.schurMatrix A y).toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hMsymm
  refine ⟨hM, ?_⟩
  let hA_symm : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.1
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = n + 2 := by
    simp [finrank_euclideanSpace]
  let bM := hM.eigenvectorBasis hdim
  let bA := hA_symm.eigenvectorBasis hdim
  let k₁ : Fin (n + 2) := Fin.castSucc (Fin.last n)
  let k₂ : Fin (n + 2) := Fin.last (n + 1)
  have hk_ne : k₁ ≠ k₂ := by
    intro h
    have hv := congrArg Fin.val h
    simp [k₁, k₂] at hv
  have hk_le : k₁ ≤ k₂ := by
    change k₁.val ≤ k₂.val
    simp [k₁, k₂]
  let v₁ : EuclideanSpace ℝ (Fin (n + 2)) := bM k₁
  let v₂ : EuclideanSpace ℝ (Fin (n + 2)) := bM k₂
  let μ₁ : ℝ := hM.eigenvalues hdim k₁
  let μ₂ : ℝ := hM.eigenvalues hdim k₂
  let α : ℝ := if WithLp.ofLp v₁ ⬝ᵥ z = 0 then 1 else WithLp.ofLp v₂ ⬝ᵥ z
  let β : ℝ := if WithLp.ofLp v₁ ⬝ᵥ z = 0 then 0 else -(WithLp.ofLp v₁ ⬝ᵥ z)
  let x : EuclideanSpace ℝ (Fin (n + 2)) := α • v₁ + β • v₂
  have hpos : 0 < α ^ 2 + β ^ 2 := by
    by_cases h1 : WithLp.ofLp v₁ ⬝ᵥ z = 0
    · simp [α, β, h1]
    · simp only [α, β, h1, ↓reduceIte]
      have hsq : 0 < (-(WithLp.ofLp v₁ ⬝ᵥ z)) ^ 2 := sq_pos_of_ne_zero (neg_ne_zero.mpr h1)
      nlinarith [sq_nonneg (WithLp.ofLp v₂ ⬝ᵥ z)]
  have hxz : WithLp.ofLp x ⬝ᵥ z = 0 := by
    have hlin : WithLp.ofLp x ⬝ᵥ z = α * (WithLp.ofLp v₁ ⬝ᵥ z) + β * (WithLp.ofLp v₂ ⬝ᵥ z) := by
      simp only [x, WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hlin]
    by_cases h1 : WithLp.ofLp v₁ ⬝ᵥ z = 0
    · simp [α, β, h1]
    · simp only [α, β, h1, ↓reduceIte]
      ring
  have hMx_vec : OMA.S_mo_333870.schurMatrix A y *ᵥ WithLp.ofLp x = A *ᵥ WithLp.ofLp x := by
    ext i
    have hentry : ∀ j, OMA.S_mo_333870.schurMatrix A y i j =
        A i j - (WithLp.ofLp y ⬝ᵥ z)⁻¹ * (z i * z j) := fun _ => rfl
    change ∑ j, OMA.S_mo_333870.schurMatrix A y i j * WithLp.ofLp x j =
      ∑ j, A i j * WithLp.ofLp x j
    simp_rw [hentry]
    have hsplit : ∑ j, (A i j - (WithLp.ofLp y ⬝ᵥ z)⁻¹ * (z i * z j)) * WithLp.ofLp x j =
        (∑ j, A i j * WithLp.ofLp x j) -
          (WithLp.ofLp y ⬝ᵥ z)⁻¹ * z i * ∑ j, WithLp.ofLp x j * z j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit]
    change (∑ j, A i j * WithLp.ofLp x j) -
        (WithLp.ofLp y ⬝ᵥ z)⁻¹ * z i * (WithLp.ofLp x ⬝ᵥ z) =
      ∑ j, A i j * WithLp.ofLp x j
    rw [hxz, mul_zero, sub_zero]
  have hMx : (OMA.S_mo_333870.schurMatrix A y).toEuclideanLin x = A.toEuclideanLin x := by
    change Matrix.toLpLin 2 2 (OMA.S_mo_333870.schurMatrix A y) x = Matrix.toLpLin 2 2 A x
    rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, hMx_vec]
  have hv11 : ⟪v₁, v₁⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, bM.orthonormal.1 k₁, one_pow]
  have hv22 : ⟪v₂, v₂⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, bM.orthonormal.1 k₂, one_pow]
  have hv12 : ⟪v₁, v₂⟫_ℝ = 0 := bM.orthonormal.2 hk_ne
  have hv21 : ⟪v₂, v₁⟫_ℝ = 0 := bM.orthonormal.2 hk_ne.symm
  have hinner_xx_M : ⟪x, x⟫_ℝ = α ^ 2 + β ^ 2 := by
    simp only [x, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hv11, hv22, hv12, hv21]
    ring
  have hv1_eig : (OMA.S_mo_333870.schurMatrix A y).toEuclideanLin v₁ = μ₁ • v₁ := by
    simp [v₁, μ₁, bM]
  have hv2_eig : (OMA.S_mo_333870.schurMatrix A y).toEuclideanLin v₂ = μ₂ • v₂ := by
    simp [v₂, μ₂, bM]
  have hMx_eig : (OMA.S_mo_333870.schurMatrix A y).toEuclideanLin x = (α * μ₁) • v₁ + (β * μ₂) • v₂ := by
    simp only [x, map_add, map_smul, hv1_eig, hv2_eig, smul_smul]
  have hinner_Mx : ⟪x, (OMA.S_mo_333870.schurMatrix A y).toEuclideanLin x⟫_ℝ =
      μ₁ * α ^ 2 + μ₂ * β ^ 2 := by
    rw [hMx_eig]
    simp only [x, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hv11, hv22, hv12, hv21]
    ring
  have hupper : ⟪x, (OMA.S_mo_333870.schurMatrix A y).toEuclideanLin x⟫_ℝ ≤ μ₁ * ⟪x, x⟫_ℝ := by
    have hμ : μ₂ ≤ μ₁ := hM.eigenvalues_antitone hdim hk_le
    rw [hinner_Mx, hinner_xx_M]
    nlinarith [sq_nonneg β]
  have hx_eq : ∑ i, ⟪bA i, x⟫_ℝ • bA i = x := bA.sum_repr' x
  have hAx_eq : A.toEuclideanLin x = ∑ i, (⟪bA i, x⟫_ℝ * hA_symm.eigenvalues hdim i) • bA i := by
    calc
      A.toEuclideanLin x = A.toEuclideanLin (∑ i, ⟪bA i, x⟫_ℝ • bA i) := by rw [hx_eq]
      _ = ∑ i, ⟪bA i, x⟫_ℝ • A.toEuclideanLin (bA i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => map_smul _ _ _
      _ = ∑ i, (⟪bA i, x⟫_ℝ * hA_symm.eigenvalues hdim i) • bA i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have heig : A.toEuclideanLin (bA i) = hA_symm.eigenvalues hdim i • bA i := by
            simp [bA]
          rw [heig, smul_smul]
  have hinner_Ax : ⟪x, A.toEuclideanLin x⟫_ℝ = ∑ i, hA_symm.eigenvalues hdim i * ⟪bA i, x⟫_ℝ ^ 2 := by
    rw [hAx_eq, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, real_inner_comm x (bA i)]
    ring
  have hinner_xx_A : ⟪x, x⟫_ℝ = ∑ i, ⟪bA i, x⟫_ℝ ^ 2 := by
    calc
      ⟪x, x⟫_ℝ = ⟪x, ∑ i, ⟪bA i, x⟫_ℝ • bA i⟫_ℝ := by rw [hx_eq]
      _ = ∑ i, ⟪x, ⟪bA i, x⟫_ℝ • bA i⟫_ℝ := inner_sum _ _ _
      _ = ∑ i, ⟪bA i, x⟫_ℝ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [inner_smul_right, real_inner_comm x (bA i)]
          ring
  have hlower : hA_symm.eigenvalues hdim (Fin.last (n + 1)) * ⟪x, x⟫_ℝ ≤ ⟪x, A.toEuclideanLin x⟫_ℝ := by
    rw [hinner_xx_A, hinner_Ax, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right
      (hA_symm.eigenvalues_antitone hdim (Fin.le_last i)) (sq_nonneg _)
  rw [hMx] at hupper
  rw [hinner_xx_M] at hlower hupper
  nlinarith
