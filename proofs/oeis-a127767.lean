import OMAStatements.S_oeis_a127767

open OMA.S_oeis_a127767

theorem OMA.solution : type_of% @OMA.S_oeis_a127767.main := by
  intro N i j
  let U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun r c =>
    if c.val ≤ r.val ∧ r.val ≤ 2 * c.val then 1 else 0
  let f : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ →+*
      Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ := (Int.castRingHom ℚ).mapMatrix
  let d (r : Fin (N + 1)) : ℚ := catalan r.val
  have tri : U.IsLowerTriangular := by
    intro r c h
    exact if_neg (fun hh => (Nat.not_le_of_gt (show r.val < c.val from h)) hh.1)
  have unit_det : IsUnit U.det := by
    rw [Matrix.det_of_isLowerTriangular _ tri]
    have diag (r : Fin (N + 1)) : U r r = 1 := if_pos ⟨le_rfl, by omega⟩
    simp [diag]
  have nonzero (k : ℕ) : (catalan k : ℚ) ≠ 0 := by
    have hk : catalan k ≠ 0 := by
      intro hc
      have h := succ_mul_catalan_eq_centralBinom k
      rw [hc, Nat.mul_zero] at h
      exact (Nat.centralBinom_pos k).ne h
    exact_mod_cast hk
  have scale : Matrix.diagonal d * triangle N = f U := by
    ext r c
    rw [Matrix.diagonal_mul]
    change (catalan r.val : ℚ) * (if _ then _ else _) = ((if _ then 1 else 0 : ℤ) : ℚ)
    by_cases h : c.val ≤ r.val ∧ r.val ≤ 2 * c.val <;> simp [h, nonzero]
  have inv : (triangle N)⁻¹ = f (U⁻¹) * Matrix.diagonal d := by
    apply Matrix.inv_eq_left_inv
    rw [mul_assoc, scale, ← map_mul, Matrix.nonsing_inv_mul _ unit_det, map_one]
  refine ⟨U⁻¹ i j * (catalan j.val : ℤ), ?_⟩
  rw [inv, Matrix.mul_diagonal, Int.cast_mul, Int.cast_natCast]
  rfl
