import OMAStatements.S_mo_100387

-- Problem: MathOverflow 100387
-- Credit: @EmadY
--
-- Let P consist of the first r columns of an n x n real orthogonal matrix Q (1 < r < n),
-- and let J = mask n have zeros on the diagonal and ones off the diagonal. If S is a real
-- symmetric r x r matrix satisfying P^T (J o (P S P^T)) P = I_r, then subtracting the
-- diagonal part D = diag((P S P^T)_{ii}) gives I_r = S - P^T D P, so for every v in R^r:
--   ||v||^2 = v^T S v - sum_i (p_i^T S p_i) (p_i . v)^2,
-- where p_i is the i-th row of P (satisfying ||p_i||^2 <= 1) and ||P v||^2 = ||v||^2.
-- At a unit eigenvector v_0 for the minimum eigenvalue mu of S, if mu <= 0 then each row
-- satisfies p_i^T S p_i >= mu ||p_i||^2 >= mu, yielding 1 <= mu - mu ||P v_0||^2 = 0,
-- a contradiction. Hence mu > 0 and S is positive definite.
-- (Note: existence of a symmetric solution S for arbitrary Q can fail for large r, e.g.
-- when r(r+1)/2 > n, since P^T D P only spans an at-most-n-dimensional subspace.)

open Matrix OMA.S_mo_100387

private lemma pt_mul_p {n r : ℕ} (hle : r ≤ n) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.transpose * Q = 1) :
    (firstColumns hle Q).transpose * firstColumns hle Q = 1 := by
  ext a b
  have hab := congr_fun (congr_fun hQ (Fin.castLE hle a)) (Fin.castLE hle b)
  simpa [firstColumns, Matrix.mul_apply, Matrix.one_apply] using hab

private lemma stiefel_col_sq {n r : ℕ} {P : Matrix (Fin n) (Fin r) ℝ}
    (hP : P.transpose * P = 1) (v : Fin r → ℝ) :
    ∑ i : Fin n, (P.mulVec v i) ^ 2 = ∑ j : Fin r, (v j) ^ 2 := by
  have hdot : dotProduct (P.mulVec v) (P.mulVec v) = dotProduct v v :=
    calc dotProduct (P.mulVec v) (P.mulVec v)
        = dotProduct (vecMul v P.transpose) (P.mulVec v) := by rw [Matrix.vecMul_transpose]
      _ = dotProduct v (P.transpose.mulVec (P.mulVec v)) :=
          (Matrix.dotProduct_mulVec v P.transpose (P.mulVec v)).symm
      _ = dotProduct v ((P.transpose * P).mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = dotProduct v v := by rw [hP, Matrix.one_mulVec]
  simpa only [dotProduct, sq] using hdot

private lemma stiefel_row_sq_le {n r : ℕ} (hle : r ≤ n) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.transpose * Q = 1) (i : Fin n) :
    ∑ j : Fin r, (firstColumns hle Q i j) ^ 2 ≤ 1 := by
  have hQ' : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQ
  have hi : ∑ k : Fin n, (Q i k) ^ 2 = 1 := by
    have h1 := congr_fun (congr_fun hQ' i) i
    simpa [Matrix.mul_apply, sq] using h1
  have himg : ∑ j : Fin r, (firstColumns hle Q i j) ^ 2 =
      ∑ k ∈ Finset.univ.image (Fin.castLE hle), (Q i k) ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective hle hab)]
    rfl
  rw [himg, ← hi]
  exact Finset.sum_le_univ_sum_of_nonneg (fun k => sq_nonneg (Q i k))

private lemma hadamard_quad_eq {n r : ℕ} {P : Matrix (Fin n) (Fin r) ℝ}
    {S : Matrix (Fin r) (Fin r) ℝ} (hP : P.transpose * P = 1)
    (hM : P.transpose * ((mask n).hadamard (P * S * P.transpose)) * P = 1)
    (v : Fin r → ℝ) :
    ∑ j : Fin r, (v j) ^ 2 =
      dotProduct v (S.mulVec v) -
        ∑ i : Fin n, dotProduct (P i) (S.mulVec (P i)) * (P.mulVec v i) ^ 2 := by
  set M : Matrix (Fin n) (Fin n) ℝ := P * S * P.transpose
  have hmask : (mask n).hadamard M = M - Matrix.diagonal M.diag := by
    ext i k
    by_cases hik : i = k <;> simp [mask, Matrix.hadamard, Matrix.diagonal, hik]
  have hPSP : P.transpose * M * P = S := by
    calc P.transpose * (P * S * P.transpose) * P
        = (P.transpose * P) * S * (P.transpose * P) := by simp only [Matrix.mul_assoc]
      _ = S := by simp [hP]
  have hS1 : (1 : Matrix (Fin r) (Fin r) ℝ) = S - P.transpose * Matrix.diagonal M.diag * P := by
    calc (1 : Matrix (Fin r) (Fin r) ℝ)
        = P.transpose * ((mask n).hadamard M) * P := hM.symm
      _ = P.transpose * M * P - P.transpose * Matrix.diagonal M.diag * P := by
          rw [hmask, Matrix.mul_sub, Matrix.sub_mul]
      _ = S - P.transpose * Matrix.diagonal M.diag * P := by rw [hPSP]
  have hq := congr_arg (fun A => dotProduct v (A.mulVec v)) hS1
  have hdiag : dotProduct v ((P.transpose * Matrix.diagonal M.diag * P).mulVec v) =
      ∑ i : Fin n, dotProduct (P i) (S.mulVec (P i)) * (P.mulVec v i) ^ 2 :=
    calc dotProduct v ((P.transpose * Matrix.diagonal M.diag * P).mulVec v)
        = dotProduct v (P.transpose.mulVec ((Matrix.diagonal M.diag).mulVec (P.mulVec v))) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = dotProduct (P.mulVec v) ((Matrix.diagonal M.diag).mulVec (P.mulVec v)) := by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = ∑ i : Fin n, M i i * (P.mulVec v i) ^ 2 := by
            simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.diag_apply]
            exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i : Fin n, dotProduct (P i) (S.mulVec (P i)) * (P.mulVec v i) ^ 2 := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have hMii : M i i = dotProduct (P i) (S.mulVec (P i)) := by
              simp [M, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mulVec, dotProduct]
            rw [hMii]
  rw [Matrix.one_mulVec, Matrix.sub_mulVec, dotProduct_sub, hdiag] at hq
  simpa only [dotProduct, sq] using hq

private theorem posDef_of_stiefel_hadamard {n r : ℕ} (hr : 1 < r)
    (S : Matrix (Fin r) (Fin r) ℝ) (hS : S.IsSymm)
    (P : Matrix (Fin n) (Fin r) ℝ)
    (hcol : ∀ v : Fin r → ℝ, ∑ i : Fin n, (P.mulVec v i) ^ 2 = ∑ j : Fin r, (v j) ^ 2)
    (hrow : ∀ i : Fin n, ∑ j : Fin r, (P i j) ^ 2 ≤ 1)
    (heq : ∀ v : Fin r → ℝ, ∑ j : Fin r, (v j) ^ 2 =
      dotProduct v (S.mulVec v) -
        ∑ i : Fin n, dotProduct (P i) (S.mulVec (P i)) * (P.mulVec v i) ^ 2) :
    S.PosDef := by
  have hH : S.IsHermitian := isHermitian_iff_isSymm.mpr hS
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ hH.eigenvalues
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set μ := hH.eigenvalues j₀
  have hpsd : (S - μ • 1).PosSemidef := by
    have h1 : S - μ • 1 = Unitary.conjStarAlgAut ℝ _ hH.eigenvectorUnitary
        (diagonal fun j => hH.eigenvalues j - μ) := by
      have hd : (diagonal fun j => hH.eigenvalues j - μ) =
          diagonal (RCLike.ofReal ∘ hH.eigenvalues) - μ • 1 := by
        ext i j; by_cases hij : i = j <;> simp [diagonal, hij]
      rw [hd, map_sub, map_smul, map_one, ← hH.spectral_theorem]
    rw [h1, Unitary.conjStarAlgAut_apply]
    exact Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff.mpr
      (.diagonal fun j => sub_nonneg.mpr (hj₀ j (Finset.mem_univ j)))
  have hray (u : Fin r → ℝ) : μ * ∑ j : Fin r, (u j) ^ 2 ≤ dotProduct u (S.mulVec u) := by
    have hu := hpsd.dotProduct_mulVec_nonneg u
    have hsq : dotProduct u u = ∑ j : Fin r, (u j) ^ 2 := by
      simp [dotProduct, sq]
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, sub_nonneg, hsq] at hu
    exact hu
  have hμ_pos : 0 < μ := by
    by_contra hle
    have hμ : μ ≤ 0 := le_of_not_gt hle
    set v₀ : Fin r → ℝ := ⇑(hH.eigenvectorBasis j₀)
    have hv₀_norm : ∑ j : Fin r, (v₀ j) ^ 2 = 1 := by
      have hnorm := hH.eigenvectorBasis.orthonormal.1 j₀
      have hinner : @inner ℝ _ _ (hH.eigenvectorBasis j₀) (hH.eigenvectorBasis j₀) =
          ∑ j : Fin r, (v₀ j) ^ 2 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp [v₀, dotProduct, sq]
      rw [real_inner_self_eq_norm_sq, hnorm, one_pow] at hinner
      exact hinner.symm
    have hv₀_quad : dotProduct v₀ (S.mulVec v₀) = μ := by
      simpa [v₀, μ] using (hH.eigenvalues_eq j₀).symm
    have hsum : μ * ∑ i : Fin n, (P.mulVec v₀ i) ^ 2 ≤
        ∑ i : Fin n, dotProduct (P i) (S.mulVec (P i)) * (P.mulVec v₀ i) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hPi : μ ≤ dotProduct (P i) (S.mulVec (P i)) :=
        (le_mul_of_le_one_right hμ (hrow i)).trans (hray (P i))
      exact mul_le_mul_of_nonneg_right hPi (sq_nonneg _)
    have heq0 := heq v₀
    rw [hcol v₀, hv₀_norm, mul_one] at hsum
    rw [hv₀_norm, hv₀_quad] at heq0
    linarith
  exact hH.posDef_iff_eigenvalues_pos.mpr fun j => lt_of_lt_of_le hμ_pos (hj₀ j (Finset.mem_univ j))

theorem OMA.solution : type_of% @OMA.S_mo_100387.main := by
  intro n r hr h Q hQ S hS P hM
  have hP := pt_mul_p h.le hQ
  exact posDef_of_stiefel_hadamard hr S hS P
    (stiefel_col_sq hP) (stiefel_row_sq_le h.le hQ) (hadamard_quad_eq hP hM)
