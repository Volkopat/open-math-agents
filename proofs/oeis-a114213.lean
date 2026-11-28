import OMAStatements.S_oeis_a114213

-- The first column is all ones, so multiplying it by the inverse gives the first basis vector.

open OMA.S_oeis_a114213

lemma OMA.a114213_first_column (i : ℕ) : entry i 0 = 1 := by
  simp only [entry, Nat.zero_le, if_true, Nat.sub_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
  · simp

theorem OMA.solution : type_of% @OMA.S_oeis_a114213.main := by
  intro n
  have tri : (corner n).IsLowerTriangular := by
    intro i j h
    have h' : i.val < j.val := h
    change ((if j.val ≤ i.val then _ else 0 : ℕ) : ℚ) = 0
    rw [if_neg (Nat.not_le_of_gt h')]
    rfl
  have det : (corner n).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ tri]
    simp [corner, entry]
  have inv := Matrix.nonsing_inv_mul (corner n) (det ▸ isUnit_one)
  have eq := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ =>
    A (Fin.last n) 0) inv
  have col (i : Fin (n+1)) : corner n i 0 = 1 := by
    change (entry i.val 0 : ℚ) = 1
    rw [OMA.a114213_first_column, Nat.cast_one]
  simp only [Matrix.mul_apply, col, mul_one] at eq
  rw [eq, Matrix.one_apply]
  cases n <;> simp
