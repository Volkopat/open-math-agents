import OMAStatements.S_mo_92798

open Matrix OMA.S_mo_92798

private def leftDiagonal : Fin 3 → ℝ := ![3, 12, 10]
private noncomputable def rightDiagonal : Fin 3 → ℝ := ![4, 21 / 5, 22]

private theorem jacobiHermitian (d : Fin 3 → ℝ) : (jacobiMatrix d (-2)).IsHermitian := by
  change (jacobiMatrix d (-2))ᴴ = jacobiMatrix d (-2)
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [jacobiMatrix, Matrix.conjTranspose_apply]

private theorem zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem one_ne_two : (1 : Fin 3) ≠ 2 := by decide
private theorem fin_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
private theorem two_ne_one : (2 : Fin 3) ≠ 1 := by decide

private theorem jacobiQuad (d x : Fin 3 → ℝ) :
    star x ⬝ᵥ (jacobiMatrix d (-2) *ᵥ x) =
      d 0 * x 0 ^ 2 + d 1 * x 1 ^ 2 + d 2 * x 2 ^ 2 - 4 * x 0 * x 1 - 4 * x 1 * x 2 := by
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_three, jacobiMatrix,
    zero_ne_two, one_ne_two, fin_two_ne_zero, two_ne_one]
  ring

private theorem dotSquare (x : Fin 3 → ℝ) :
    star x ⬝ᵥ x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  simp [dotProduct, Fin.sum_univ_three, pow_two]

private theorem dotPositive {x : Fin 3 → ℝ} (hx : x ≠ 0) : 0 < star x ⬝ᵥ x := by
  have hex : ∃ i, x i ≠ 0 := by
    by_contra! hh
    exact hx (funext hh)
  obtain ⟨i, hi⟩ := hex
  rw [dotSquare]
  fin_cases i
  · exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg
      (show 0 < x 0 ^ 2 from sq_pos_of_ne_zero hi) (sq_nonneg (x 1))) (sq_nonneg (x 2))
  · exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos
      (sq_nonneg (x 0)) (show 0 < x 1 ^ 2 from sq_pos_of_ne_zero hi)) (sq_nonneg (x 2))
  · exact add_pos_of_nonneg_of_pos (add_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1)))
      (show 0 < x 2 ^ 2 from sq_pos_of_ne_zero hi)

private theorem leftBound (x : Fin 3 → ℝ) :
    (5 / 2) * (star x ⬝ᵥ x) ≤ star x ⬝ᵥ (jacobiMatrix leftDiagonal (-2) *ᵥ x) := by
  rw [dotSquare, jacobiQuad]
  norm_num [leftDiagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith [sq_nonneg (x 0 - 4 * x 1), sq_nonneg (x 1 - 2 * x 2),
    sq_nonneg (x 1), sq_nonneg (x 2)]

private theorem rightBound (x : Fin 3 → ℝ) :
    star x ⬝ᵥ x ≤ star x ⬝ᵥ (jacobiMatrix rightDiagonal (-2) *ᵥ x) := by
  rw [dotSquare, jacobiQuad]
  norm_num [rightDiagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - 2 * x 2),
    sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_92798.main) := by
  intro h
  have hJ : (jacobiMatrix leftDiagonal (-2)).PosDef := by
    refine posDef_iff_dotProduct_mulVec.mpr ⟨jacobiHermitian _, fun x hx => ?_⟩
    exact (mul_pos (by norm_num) (dotPositive hx)).trans_le (leftBound x)
  have hL : (jacobiMatrix rightDiagonal (-2)).PosDef := by
    refine posDef_iff_dotProduct_mulVec.mpr ⟨jacobiHermitian _, fun x hx => ?_⟩
    exact (dotPositive hx).trans_le (rightBound x)
  have hstrict := h 2 leftDiagonal rightDiagonal (-2) (by norm_num)
    (by intro i; fin_cases i <;> norm_num [leftDiagonal, rightDiagonal])
    (by refine ⟨0, ?_⟩; intro j; fin_cases j <;> norm_num [leftDiagonal, rightDiagonal])
    (by
      change 0 < ∑ i : Fin 3, (rightDiagonal i - leftDiagonal i)
      rw [Fin.sum_univ_three]
      norm_num [leftDiagonal, rightDiagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]) hJ hL
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let hSymJ := isSymmetric_toEuclideanLin_iff.mpr hJ.1
  let hSymL := isSymmetric_toEuclideanLin_iff.mpr hL.1
  have leJ : (5 : ℝ) / 2 ≤ smallestEigenvalue hJ.1 := by
    let i : Fin 3 := Fin.last 2
    let u := hSymJ.eigenvectorBasis hdim i
    have hu : u ≠ 0 := (hSymJ.hasEigenvector_eigenvectorBasis hdim i).2
    have hx : u.ofLp ≠ 0 := fun hx => hu (WithLp.ofLp_injective 2 hx)
    have hvec : jacobiMatrix leftDiagonal (-2) *ᵥ u.ofLp =
        hSymJ.eigenvalues hdim i • u.ofLp :=
      congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w.ofLp) (hSymJ.apply_eigenvectorBasis hdim i)
    have hbound := leftBound u.ofLp
    rw [hvec, dotProduct_smul, smul_eq_mul] at hbound
    exact le_of_not_gt fun hlt => (not_lt_of_ge hbound) (mul_lt_mul_of_pos_right hlt (dotPositive hx))
  have leL : smallestEigenvalue hL.1 ≤ 2 := by
    let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, 1, 1 / 10]
    have hv : v ≠ 0 := by
      intro hv
      have hv0 := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 0) hv
      norm_num [v] at hv0
    have hvApply : Matrix.toEuclideanLin (jacobiMatrix rightDiagonal (-2)) v = (2 : ℝ) • v := by
      apply WithLp.ofLp_injective 2
      funext i
      fin_cases i <;> norm_num [v, Matrix.ofLp_toLpLin, Matrix.mulVec, Fin.sum_univ_three,
        dotProduct, jacobiMatrix, rightDiagonal, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        zero_ne_two, one_ne_two, fin_two_ne_zero, two_ne_one]
      split_ifs with heq
      · norm_num
      · exact (heq rfl).elim
    have hvEigen := Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hvApply, hv⟩
    obtain ⟨i, hi⟩ := hSymL.exists_eigenvalues_eq hdim hvEigen
    exact (hSymL.eigenvalues_antitone hdim (Fin.le_last i)).trans_eq hi
  linarith