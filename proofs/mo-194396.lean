import OMAStatements.S_mo_194396

/-! Credit: @Genbox for the original counterexample proof. -/

open Matrix
open scoped Matrix

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_194396.main) := by
  intro h
  let α : Fin 3 → ℝ := ![2, 2, -1]
  let β : Fin 3 → ℝ := ![1, -2, 1]
  let γ : Fin 3 → ℝ := ![1, 1, -2]
  have hcoeff (i : Fin 3) : α i ≠ 0 ∧ β i ≠ 0 ∧ γ i ≠ 0 := by
    fin_cases i <;> norm_num [α, β, γ]
  obtain ⟨T, -, hT, hn⟩ := h 0 α β γ hcoeff
  let A : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    if i = j then α i else if j = i + 1 then β i else if i = j + 1 then γ j else 0
  change (T⁻¹ * A * T) * (T⁻¹ * A * T)ᵀ =
    (T⁻¹ * A * T)ᵀ * (T⁻¹ * A * T) at hn
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun _ j => γ j
  have hA : A = 1 + M := by
    ext i j
    rw [Matrix.add_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> norm_num [A, M, α, β, γ, Fin.ext_iff, Fin.val_add]
  have hM : M * M = 0 := by
    ext i j
    have hsum : γ 0 + (γ 1 + γ 2) = 0 := by
      change (1 : ℝ) + (1 + -2) = 0
      norm_num
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    simp only [M, ← add_mul, add_assoc, hsum, zero_mul, Matrix.zero_apply]
  have hMne : M ≠ 0 := by
    intro heq
    have he := congrArg (fun U : Matrix (Fin 3) (Fin 3) ℝ => U 0 0) heq
    norm_num [M, γ] at he
  let E := T⁻¹ * M * T
  have hshift : T⁻¹ * A * T = 1 + E := by
    rw [hA, mul_add, add_mul, mul_one, Matrix.nonsing_inv_mul T hT]
  rw [hshift, Matrix.transpose_add, Matrix.transpose_one] at hn
  have hcomm : E * Eᵀ = Eᵀ * E := by
    calc
      _ = (1 + E) * (1 + Eᵀ) - (1 + E + Eᵀ) := by noncomm_ring
      _ = (1 + Eᵀ) * (1 + E) - (1 + E + Eᵀ) := by rw [hn]
      _ = _ := by noncomm_ring
  have hsq : E * E = 0 := by
    calc
      _ = T⁻¹ * M * (T * T⁻¹) * M * T := by dsimp [E]; noncomm_ring
      _ = 0 := by rw [Matrix.mul_nonsing_inv T hT, mul_one,
        Matrix.mul_assoc (T⁻¹) M M, hM, mul_zero, zero_mul]
  let R := Eᵀ * E
  have hRsq : R * R = 0 := by
    calc
      _ = Eᵀ * (E * Eᵀ) * E := by dsimp [R]; noncomm_ring
      _ = Eᵀ * (Eᵀ * E) * E := by rw [hcomm]
      _ = (Eᵀ * Eᵀ) * (E * E) := by noncomm_ring
      _ = 0 := by rw [hsq, mul_zero]
  have hEzero : E = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, R]
      using hRsq
  apply hMne
  calc
    M = (T * T⁻¹) * M * (T * T⁻¹) := by
      rw [Matrix.mul_nonsing_inv T hT, one_mul, mul_one]
    _ = T * E * T⁻¹ := by dsimp [E]; noncomm_ring
    _ = 0 := by rw [hEzero, mul_zero, zero_mul]