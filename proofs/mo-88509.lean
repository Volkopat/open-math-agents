import OMAStatements.S_mo_88509

-- Problem mo-88509: (1) if A is a real m x m matrix with det (A - A^T) != 0 then m is even and m <= 2 rank A;
-- (2) for every k there is a real 2k x 2k matrix A with det (A - A^T) != 0 and rank A = k.
-- Upstream: statements/mo-88509.lean (declaration OMA.S_mo_88509.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: (1) S = A - A^T satisfies S^T = -S, so det S = (-1)^m det S, which forces det S = 0 when m is odd.
-- Also m = rank S <= rank A + rank (-A^T) <= 2 rank A, because the rank is subadditive and -A^T = A^T (-1).
-- (2) Let M be the block matrix (0 1; 0 0) with k x k blocks. Then M - M^T = (0 1; -1 0) squares to -1, so its
-- determinant is not 0. Since M M = 0, rank M + rank M <= 2k, so rank M <= k, and part (1) gives 2k <= 2 rank M.
-- The matrix A is M with its index set identified with {0, ..., 2k - 1}.

open Matrix

private lemma rank_add_le' {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact le_trans (Submodule.finrank_mono (LinearMap.range_add_le _ _))
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

private lemma part1 (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) (hdet : (A - Aᵀ).det ≠ 0) :
    Even m ∧ m ≤ 2 * A.rank := by
  constructor
  · by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    apply hdet
    have h1 : (A - Aᵀ)ᵀ = -(A - Aᵀ) := by
      rw [Matrix.transpose_sub, Matrix.transpose_transpose, neg_sub]
    have h2 : (A - Aᵀ).det = -(A - Aᵀ).det := by
      have h3 : ((A - Aᵀ)ᵀ).det = (A - Aᵀ).det := Matrix.det_transpose _
      rw [h1, Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, neg_one_mul] at h3
      exact h3.symm
    linarith
  · have hu : IsUnit (A - Aᵀ) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have h1 : (A - Aᵀ).rank = m := by rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
    have h2 : (A - Aᵀ).rank ≤ A.rank + (-Aᵀ).rank := by
      rw [sub_eq_add_neg]
      exact rank_add_le' _ _
    have h3 : (-Aᵀ).rank ≤ Aᵀ.rank := by
      have e : -Aᵀ = Aᵀ * (-1 : Matrix (Fin m) (Fin m) ℝ) := by rw [Matrix.mul_neg, Matrix.mul_one]
      rw [e]
      exact Matrix.rank_mul_le_left _ _
    rw [Matrix.rank_transpose] at h3
    omega

theorem OMA.solution : type_of% @OMA.S_mo_88509.main := by
  refine ⟨part1, fun k => ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ,
      M = Matrix.fromBlocks 0 1 0 0 := ⟨_, rfl⟩
  have hMM : M * M = 0 := by
    rw [hM, Matrix.fromBlocks_multiply]
    simp
  have hS : M - Mᵀ = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [hM]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, eq_comm]
  have hneg : (-1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ) = Matrix.fromBlocks (-1) 0 0 (-1) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have hSS : (M - Mᵀ) * (M - Mᵀ) = -1 := by
    rw [hS, Matrix.fromBlocks_multiply, hneg]
    simp
  have hdetS : (M - Mᵀ).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse (B := -(M - Mᵀ))
    rw [Matrix.mul_neg, hSS, neg_neg]
  have hA : (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) -
      (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)ᵀ =
      (M - Mᵀ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    rfl
  have hdetA : ((M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) -
      (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)ᵀ).det ≠ 0 := by
    rw [hA, Matrix.det_submatrix_equiv_self]
    exact hdetS
  have hAA : (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) *
      (M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = 0 := by
    rw [Matrix.submatrix_mul_equiv, hMM]
    rfl
  refine ⟨M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, hdetA, ?_⟩
  have h1 := Matrix.rank_add_rank_le_card_of_mul_eq_zero hAA
  rw [Fintype.card_fin] at h1
  have h2 := (part1 (k + k) _ hdetA).2
  omega
