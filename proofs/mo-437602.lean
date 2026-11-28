import OMAStatements.S_mo_437602

open Matrix Finset
open scoped Matrix.Norms.L2Operator

namespace OMA_mo_437602_Aux

private lemma norm_sq_apply_eq_sum_eigenvalues
    {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) (x : E) :
    ‖T x‖ ^ 2 =
      ∑ k : Fin (Module.finrank 𝕜 E),
        (T.isSymmetric_adjoint_comp_self.eigenvalues rfl k) *
          ‖@inner 𝕜 E _ (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl k) x‖ ^ 2 := by
  set hS := T.isSymmetric_adjoint_comp_self
  set b := hS.eigenvectorBasis rfl
  have h1 : ‖T x‖ ^ 2 = RCLike.re (@inner 𝕜 F _ (T x) (T x)) :=
    InnerProductSpace.norm_sq_eq_re_inner (T x)
  have h2 : @inner 𝕜 F _ (T x) (T x) = @inner 𝕜 E _ x ((LinearMap.adjoint T ∘ₗ T) x) := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  rw [h1, h2, ← b.sum_inner_mul_inner x ((LinearMap.adjoint T ∘ₗ T) x), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have heig : @inner 𝕜 E _ (b k) ((LinearMap.adjoint T ∘ₗ T) x) =
      (hS.eigenvalues rfl k : 𝕜) * @inner 𝕜 E _ (b k) x := by
    rw [← hS (b k) x, hS.apply_eigenvectorBasis rfl k, inner_smul_left, RCLike.conj_ofReal]
  have hconj : @inner 𝕜 E _ x (b k) = starRingEnd 𝕜 (@inner 𝕜 E _ (b k) x) :=
    (inner_conj_symm x (b k)).symm
  rw [heig, hconj]
  have hcm : (starRingEnd 𝕜) (@inner 𝕜 E _ (b k) x) *
      ((hS.eigenvalues rfl k : 𝕜) * @inner 𝕜 E _ (b k) x) =
      (((hS.eigenvalues rfl k) * ‖@inner 𝕜 E _ (b k) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [mul_left_comm, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
  rw [hcm, RCLike.ofReal_re]

private lemma singularValues_comp_le
    {𝕜 : Type*} [RCLike 𝕜]
    {D E F G : Type*}
    [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [FiniteDimensional 𝕜 D]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (L : F →ₗ[𝕜] G) (T : E →ₗ[𝕜] F) (R : D →ₗ[𝕜] E)
    (hL : ∀ v, ‖L v‖ ≤ ‖v‖) (hR : ∀ v, ‖R v‖ ≤ ‖v‖) (i : ℕ) :
    (L ∘ₗ T ∘ₗ R).singularValues i ≤ T.singularValues i := by
  set B : D →ₗ[𝕜] G := L ∘ₗ T ∘ₗ R
  set d := Module.finrank 𝕜 D
  set c := Module.finrank 𝕜 E
  by_cases hi : d ≤ i
  · rw [B.singularValues_of_finrank_le hi]
    exact T.singularValues_nonneg i
  push Not at hi
  set hB := B.isSymmetric_adjoint_comp_self
  set bB := hB.eigenvectorBasis rfl
  set hT := T.isSymmetric_adjoint_comp_self
  set bT := hT.eigenvectorBasis rfl
  let g : (Fin (i + 1) → 𝕜) →ₗ[𝕜] D :=
    { toFun := fun w => ∑ j : Fin (i + 1), w j • bB ⟨j.1, by omega⟩
      map_add' := fun w₁ w₂ => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r w => by simp [Finset.smul_sum, mul_smul] }
  let phi : (Fin (i + 1) → 𝕜) →ₗ[𝕜] (Fin (min i c) → 𝕜) :=
    { toFun := fun w k => @inner 𝕜 E _ (bT ⟨k.1, by omega⟩) (R (g w))
      map_add' := fun w₁ w₂ => by ext k; simp [map_add, inner_add_right]
      map_smul' := fun r w => by ext k; simp [map_smul, inner_smul_right] }
  have hfin : Module.finrank 𝕜 (Fin (min i c) → 𝕜) < Module.finrank 𝕜 (Fin (i + 1) → 𝕜) := by
    simp only [Module.finrank_pi, Fintype.card_fin]
    omega
  have hker : LinearMap.ker phi ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hfin
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hw_mem
  set x : D := g w
  have hx_ne : x ≠ 0 := by
    intro hx0
    apply hw_ne
    ext j
    have hinner : @inner 𝕜 D _ (bB ⟨j.1, by omega⟩) x = 0 := by simp [hx0]
    have hcomp : @inner 𝕜 D _ (bB ⟨j.1, by omega⟩) x = w j := by
      simp only [x, g, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
      rw [Finset.sum_eq_single j]
      · simp [bB.orthonormal.1]
      · intro j' _ hj'
        have hne : (⟨j.1, by omega⟩ : Fin d) ≠ ⟨j'.1, by omega⟩ := by
          intro heq
          apply hj'
          exact Fin.ext (congrArg Fin.val heq).symm
        simp [bB.orthonormal.2 hne]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    exact hcomp.symm.trans hinner
  have hx_norm_pos : 0 < ‖x‖ ^ 2 := by positivity
  have hB_lower : B.singularValues i ^ 2 * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2 := by
    rw [norm_sq_apply_eq_sum_eigenvalues B x, ← bB.sum_sq_norm_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hki : k.1 ≤ i
    · have heq : hB.eigenvalues rfl k = B.singularValues k.1 ^ 2 := (B.sq_singularValues_fin rfl k).symm
      rw [heq]
      have hmono : B.singularValues i ≤ B.singularValues k.1 := B.singularValues_antitone hki
      have hsq : B.singularValues i ^ 2 ≤ B.singularValues k.1 ^ 2 :=
        pow_le_pow_left₀ (B.singularValues_nonneg i) hmono 2
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · have hzero : @inner 𝕜 D _ (bB k) x = 0 := by
        simp only [x, g, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
        refine Finset.sum_eq_zero fun j _ => ?_
        have hne : k ≠ ⟨j.1, by omega⟩ := by
          intro heq
          have : k.1 = j.1 := congrArg Fin.val heq
          omega
        simp [bB.orthonormal.2 hne]
      simp [bB, hzero]
  set y : E := R x
  have hT_upper : ‖T y‖ ^ 2 ≤ T.singularValues i ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_sq_apply_eq_sum_eigenvalues T y, ← bT.sum_sq_norm_inner_right y, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hik : i ≤ k.1
    · have heq : hT.eigenvalues rfl k = T.singularValues k.1 ^ 2 := (T.sq_singularValues_fin rfl k).symm
      rw [heq]
      have hmono : T.singularValues k.1 ≤ T.singularValues i := T.singularValues_antitone hik
      have hsq : T.singularValues k.1 ^ 2 ≤ T.singularValues i ^ 2 :=
        pow_le_pow_left₀ (T.singularValues_nonneg k.1) hmono 2
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · have hzero : @inner 𝕜 E _ (bT k) y = 0 := by
        have hklt : k.1 < min i c := by omega
        have hphi := congrFun hw_mem ⟨k.1, hklt⟩
        simpa [phi, y, x] using hphi
      simp [bT, hzero]
  have hL_sq : ‖B x‖ ^ 2 ≤ ‖T y‖ ^ 2 := by
    have hBx : B x = L (T y) := rfl
    rw [hBx]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL (T y)) 2
  have hR_sq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hR x) 2
  have hchain : B.singularValues i ^ 2 * ‖x‖ ^ 2 ≤ T.singularValues i ^ 2 * ‖x‖ ^ 2 :=
    calc B.singularValues i ^ 2 * ‖x‖ ^ 2
        ≤ ‖B x‖ ^ 2 := hB_lower
      _ ≤ ‖T y‖ ^ 2 := hL_sq
      _ ≤ T.singularValues i ^ 2 * ‖y‖ ^ 2 := hT_upper
      _ ≤ T.singularValues i ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hR_sq (sq_nonneg _)
  have hsq : B.singularValues i ^ 2 ≤ T.singularValues i ^ 2 :=
    le_of_mul_le_mul_right hchain hx_norm_pos
  exact le_of_sq_le_sq hsq (T.singularValues_nonneg i)

private lemma toEuclideanLin_mul {𝕜 : Type*} [RCLike 𝕜] {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) 𝕜) (B : Matrix (Fin b) (Fin c) 𝕜) :
    (A * B).toEuclideanLin = A.toEuclideanLin ∘ₗ B.toEuclideanLin := by
  ext v i
  exact congrFun (Matrix.mulVec_mulVec (WithLp.ofLp v) A B).symm i

private lemma norm_toEuclideanLin_le_of_norm_le_one {𝕜 : Type*} [RCLike 𝕜] {a b : ℕ}
    (M : Matrix (Fin a) (Fin b) 𝕜) (hM : ‖M‖ ≤ 1) (v : EuclideanSpace 𝕜 (Fin b)) :
    ‖M.toEuclideanLin v‖ ≤ ‖v‖ := by
  have h1 : ‖M.toEuclideanLin v‖ ≤ ‖M‖ * ‖v‖ := by
    rw [Matrix.l2_opNorm_def]
    exact ((Matrix.toEuclideanLin (𝕜 := 𝕜)).trans LinearMap.toContinuousLinearMap M).le_opNorm v
  calc ‖M.toEuclideanLin v‖
      ≤ ‖M‖ * ‖v‖ := h1
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg v)
    _ = ‖v‖ := one_mul _

private lemma l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
    {𝕜 : Type*} [RCLike 𝕜] {n k : ℕ}
    (M : Matrix (Fin n) (Fin k) 𝕜) (hM : M.conjTranspose * M = 1) :
    ‖M‖ ≤ 1 := by
  have h1 : ‖(1 : Matrix (Fin k) (Fin k) 𝕜)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
  have hmul : ‖M‖ * ‖M‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self M, hM]
    exact h1
  by_contra hlt
  push Not at hlt
  nlinarith [norm_nonneg M]

end OMA_mo_437602_Aux

theorem OMA.solution : type_of% @OMA.S_mo_437602.main := by
  have hpart1 :
      ∀ (𝕜 : Type) [RCLike 𝕜] (a b c d : ℕ)
        (L : Matrix (Fin a) (Fin b) 𝕜) (A : Matrix (Fin b) (Fin c) 𝕜)
        (R : Matrix (Fin c) (Fin d) 𝕜), ‖L‖ ≤ 1 → ‖R‖ ≤ 1 →
        ∀ i : ℕ, OMA.S_mo_437602.sv (L * A * R) i ≤ OMA.S_mo_437602.sv A i := by
    intro 𝕜 _ a b c d L A R hL hR i
    unfold OMA.S_mo_437602.sv
    rw [OMA_mo_437602_Aux.toEuclideanLin_mul, OMA_mo_437602_Aux.toEuclideanLin_mul,
      LinearMap.comp_assoc]
    exact OMA_mo_437602_Aux.singularValues_comp_le
      L.toEuclideanLin A.toEuclideanLin R.toEuclideanLin
      (OMA_mo_437602_Aux.norm_toEuclideanLin_le_of_norm_le_one L hL)
      (OMA_mo_437602_Aux.norm_toEuclideanLin_le_of_norm_le_one R hR) i
  refine ⟨hpart1, ?_⟩
  intro 𝕜 _ n k A M₁ M₂ hM₁ hM₂ r p hp
  have hL : ‖M₁.conjTranspose‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact OMA_mo_437602_Aux.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one M₁ hM₁
  have hR : ‖M₂‖ ≤ 1 :=
    OMA_mo_437602_Aux.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one M₂ hM₂
  refine Finset.sum_le_sum fun i _ => ?_
  exact Real.rpow_le_rpow
    ((M₁.conjTranspose * A * M₂).toEuclideanLin.singularValues_nonneg i)
    (hpart1 𝕜 k n n k M₁.conjTranspose A M₂ hL hR i) hp
