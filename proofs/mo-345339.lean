import OMAStatements.S_mo_345339
import Mathlib

namespace PositiveJordan

open OMA.S_mo_345339 Matrix Polynomial Finset

private abbrev dim (m : ℕ) := 4*m+7
private def r (m : ℕ) : ℚ := (m : ℚ)+2
@[simp] private theorem idx_0_1 (m : ℕ) : (0 : Fin (dim m)) ≠ 1 := by
  intro h
  have he := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (show 0 < dim m by change 0 < 4*m+7; omega), Nat.mod_eq_of_lt (show 1 < dim m by change 1 < 4*m+7; omega)] at he

@[simp] private theorem idx_1_0 (m : ℕ) : (1 : Fin (dim m)) ≠ 0 :=
  (idx_0_1 m).symm

@[simp] private theorem idx_0_2 (m : ℕ) : (0 : Fin (dim m)) ≠ 2 := by
  intro h
  have he := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (show 0 < dim m by change 0 < 4*m+7; omega), Nat.mod_eq_of_lt (show 2 < dim m by change 2 < 4*m+7; omega)] at he

@[simp] private theorem idx_2_0 (m : ℕ) : (2 : Fin (dim m)) ≠ 0 :=
  (idx_0_2 m).symm

@[simp] private theorem idx_0_3 (m : ℕ) : (0 : Fin (dim m)) ≠ 3 := by
  intro h
  have he := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (show 0 < dim m by change 0 < 4*m+7; omega), Nat.mod_eq_of_lt (show 3 < dim m by change 3 < 4*m+7; omega)] at he

@[simp] private theorem idx_3_0 (m : ℕ) : (3 : Fin (dim m)) ≠ 0 :=
  (idx_0_3 m).symm

@[simp] private theorem idx_1_2 (m : ℕ) : (1 : Fin (dim m)) ≠ 2 := by
  intro h
  have he := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < dim m by change 1 < 4*m+7; omega), Nat.mod_eq_of_lt (show 2 < dim m by change 2 < 4*m+7; omega)] at he

@[simp] private theorem idx_2_1 (m : ℕ) : (2 : Fin (dim m)) ≠ 1 :=
  (idx_1_2 m).symm

@[simp] private theorem idx_1_3 (m : ℕ) : (1 : Fin (dim m)) ≠ 3 := by
  intro h
  have he := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (show 1 < dim m by change 1 < 4*m+7; omega), Nat.mod_eq_of_lt (show 3 < dim m by change 3 < 4*m+7; omega)] at he

@[simp] private theorem idx_3_1 (m : ℕ) : (3 : Fin (dim m)) ≠ 1 :=
  (idx_1_3 m).symm

@[simp] private theorem idx_2_3 (m : ℕ) : (2 : Fin (dim m)) ≠ 3 := by
  intro h
  have he := congrArg Fin.val h
  norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (show 2 < dim m by change 2 < 4*m+7; omega), Nat.mod_eq_of_lt (show 3 < dim m by change 3 < 4*m+7; omega)] at he

@[simp] private theorem idx_3_2 (m : ℕ) : (3 : Fin (dim m)) ≠ 2 :=
  (idx_2_3 m).symm

private def E {m : ℕ} (j : Fin (dim m)) (i : Fin (dim m)) : ℚ :=
  if i = j then 1 else 0

private def U (m : ℕ) : Matrix (Fin (dim m)) (Fin 4) ℚ :=
  fun i j => (![1,E 0 i,E 1 i,E 2 i] : Fin 4 → ℚ) j

private def V (m : ℕ) : Matrix (Fin 4) (Fin (dim m)) ℚ :=
  fun i j => (![1,r m * E 1 j,r m * E 2 j,r m * E 2 j] : Fin 4 → ℚ) i

private def A (m : ℕ) : Mat (dim m) := 1 + U m * V m

private theorem update_apply (m : ℕ) (i j : Fin (dim m)) :
    (U m * V m) i j = 1 + r m * (E 0 i * E 1 j + E 1 i * E 2 j + E 2 i * E 2 j) := by
  simp [Matrix.mul_apply, U, V, Fin.sum_univ_four]
  ring

private theorem sum_E {m : ℕ} (j : Fin (dim m)) : (∑ i, E j i) = 1 := by
  simp [E]

private theorem small_product (m : ℕ) :
    V m * U m =
      !![(dim m : ℚ), 1, 1, 1; r m, 0, r m, 0; r m, 0, 0, r m; r m, 0, 0, r m] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, U, V, E]

private theorem small_charpoly (m : ℕ) :
    (V m * U m).charpoly =
      X^2 * (X - C (r m - 1)) * (X - C ((dim m:ℚ) + 1)) := by
  rw [small_product]
  have hM : charmatrix (!![(dim m : ℚ), 1, 1, 1; r m, 0, r m, 0;
      r m, 0, 0, r m; r m, 0, 0, r m] : Matrix (Fin 4) (Fin 4) ℚ) =
      !![X-C (dim m:ℚ), -1, -1, -1; -C (r m), X, -C (r m), 0;
          -C (r m), 0, X, -C (r m); -C (r m), 0, 0, X-C (r m)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.charpoly, hM, det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, Matrix.submatrix_apply]
  change
    (-1 : ℚ[X]) ^ (0:ℕ) * (X-C (dim m:ℚ)) * (X * X * (X-C (r m)) - X * (-C (r m)) * 0 - (-C (r m)) * 0 * (X-C (r m)) + (-C (r m)) * (-C (r m)) * 0 + 0 * 0 * 0 - 0 * X * 0) +
    (-1 : ℚ[X]) ^ (1:ℕ) * (-1) * ((-C (r m)) * X * (X-C (r m))
      - (-C (r m)) * (-C (r m)) * 0
      - (-C (r m)) * (-C (r m)) * (X-C (r m))
      + (-C (r m)) * (-C (r m)) * (-C (r m))
      + 0 * (-C (r m)) * 0
      - 0 * X * (-C (r m))) +
    (-1 : ℚ[X]) ^ (2:ℕ) * (-1) * ((-C (r m)) * 0 * (X-C (r m))
      - (-C (r m)) * (-C (r m)) * 0
      - X * (-C (r m)) * (X-C (r m))
      + X * (-C (r m)) * (-C (r m))
      + 0 * (-C (r m)) * 0
      - 0 * 0 * (-C (r m))) +
    (-1 : ℚ[X]) ^ (3:ℕ) * (-1) * ((-C (r m)) * 0 * 0
      - (-C (r m)) * X * 0
      - X * (-C (r m)) * 0
      + X * X * (-C (r m))
      + (-C (r m)) * (-C (r m)) * 0
      - (-C (r m)) * 0 * (-C (r m))) = _
  push_cast
  simp [r, Polynomial.C_ofNat]
  ring

private theorem polynomial_update (m : ℕ) :
    (A m).charpoly = (X-1)^(dim m-2)*(X-C (r m))*(X-C ((dim m:ℚ)+2)) := by
  have hB := Matrix.charpoly_mul_comm_of_le (U m) (V m) (by simp [dim])
  have hshift : A m = U m * V m - Matrix.scalar (Fin (dim m)) (-1 : ℚ) := by
    rw [map_neg, map_one, sub_neg_eq_add]
    exact add_comm _ _
  rw [hshift, Matrix.charpoly_sub_scalar, hB, small_charpoly]
  simp only [Fintype.card_fin, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.sub_comp, Polynomial.C_comp, Polynomial.C_neg, Polynomial.C_1]
  have h₁ : X + -1 - C (r m - 1) = X - C (r m) := by simp [Polynomial.C_sub]; ring
  have h₂ : X + -1 - C ((dim m:ℚ)+1) = X - C ((dim m:ℚ)+2) := by
    simp [Polynomial.C_add, show (2:ℚ) = 1+1 by norm_num]
    ring
  rw [h₁, h₂, ← mul_assoc, ← mul_assoc, ← pow_add,
    show dim m-4+2=dim m-2 by change (4*m+7)-4+2=(4*m+7)-2; omega,
    ← sub_eq_add_neg X (1:ℚ[X])]

private theorem V_mulVec (m : ℕ) (w : Fin (dim m) → ℚ) :
    V m *ᵥ w = ![∑ i, w i, r m * w 1, r m * w 2, r m * w 2] := by
  ext i
  fin_cases i <;> simp [V, mulVec, dotProduct, E, ite_mul]

private theorem U_mulVec (m : ℕ) (w : Fin 4 → ℚ) (i : Fin (dim m)) :
    (U m *ᵥ w) i = w 0 + E 0 i * w 1 + E 1 i * w 2 + E 2 i * w 3 := by
  simp [U, mulVec, dotProduct, Fin.sum_univ_four]

private def firstVec (m : ℕ) (i : Fin (dim m)) : ℚ :=
  1 + (2 - (dim m:ℚ)) * E 0 i - E 1 i - E 2 i

private def secondVec (m : ℕ) (i : Fin (dim m)) : ℚ :=
  (r m - 1 + (dim m:ℚ)) * E 0 i + (2 - (dim m:ℚ)) * E 1 i - E 2 i

private theorem jordan (m : ℕ) :
    ∃ v : Fin (dim m) → ℚ,
      (A m - 1) *ᵥ ((A m - 1) *ᵥ v) = 0 ∧ (A m - 1) *ᵥ v ≠ 0 := by
  have hA : A m - 1 = U m * V m := by simp [A]
  have hu : (U m * V m) *ᵥ firstVec m = 0 := by
    rw [← mulVec_mulVec, V_mulVec]
    have hs : (∑ i, firstVec m i) = 0 := by
      simp [firstVec, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, sum_E]
      ring
    ext i
    rw [U_mulVec, hs]
    simp [firstVec, E]
  have hv : (U m * V m) *ᵥ secondVec m = r m • firstVec m := by
    rw [← mulVec_mulVec, V_mulVec]
    have hs : (∑ i, secondVec m i) = r m := by
      simp [secondVec, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, sum_E]
      ring
    ext i
    rw [U_mulVec, hs]
    simp [secondVec, firstVec, E, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  refine ⟨secondVec m, ?_, ?_⟩
  · rw [hA, hv, Matrix.mulVec_smul, hu, smul_zero]
  · rw [hA, hv]
    intro h
    have ht := congrFun h (3 : Fin (dim m))
    have hr : 0 < r m := by unfold r; positivity
    exact hr.ne' (by simpa [firstVec, E, Pi.smul_apply, smul_eq_mul] using ht)

private theorem diagonal_no_chain {n : ℕ} {A : Mat n} (hA : rationalDiagonalizable A)
    (v : Fin n → ℚ) (hz : (A - 1) *ᵥ ((A - 1) *ᵥ v) = 0) :
    (A - 1) *ᵥ v = 0 := by
  obtain ⟨P, d, hd⟩ := hA
  let Q : Mat n := P
  let R : Mat n := (P⁻¹ : (Mat n)ˣ)
  have hQR : Q * R = 1 := by exact Units.mul_inv P
  have hRQ : R * Q = 1 := by exact Units.inv_mul P
  let D : Mat n := diagonal (fun i => d i - 1)
  have hD : A - 1 = Q * D * R := by
    change A = Q * diagonal d * R at hd
    have hdiag : D = diagonal d - 1 := by
      ext i j
      by_cases h : i=j <;> simp [D, h]
    rw [hd, hdiag, mul_sub, sub_mul, mul_one, hQR]
  have hv (x : Fin n → ℚ) : (A - 1) *ᵥ x = Q *ᵥ (D *ᵥ (R *ᵥ x)) := by
    rw [hD, ← mulVec_mulVec, ← mulVec_mulVec]
  have inv_vec (x : Fin n → ℚ) : R *ᵥ (Q *ᵥ x) = x := by
    rw [mulVec_mulVec, hRQ, one_mulVec]
  rw [hv, hv v, inv_vec] at hz
  have hh : D *ᵥ (D *ᵥ (R *ᵥ v)) = 0 := by
    have h := congrArg (fun x => R *ᵥ x) hz
    rwa [inv_vec, mulVec_zero] at h
  have hinner : D *ᵥ (R *ᵥ v) = 0 := by
    ext i
    have h := congrFun hh i
    simp only [D, mulVec_diagonal, Pi.zero_apply] at h ⊢
    rcases mul_eq_zero.mp h with hf | hf
    · simp [hf]
    · exact hf
  rw [hv, hinner, mulVec_zero]

private theorem positive (m : ℕ) (i j : Fin (dim m)) : ∃ k : ℕ, 0 < k ∧ A m i j = k := by
  let d : ℕ := if i = j then 1 else 0
  let s : ℕ := (if i=0 then 1 else 0) * (if j=1 then 1 else 0) +
    (if i=1 then 1 else 0) * (if j=2 then 1 else 0) +
    (if i=2 then 1 else 0) * (if j=2 then 1 else 0)
  refine ⟨1 + d + (m+2)*s, by omega, ?_⟩
  simp only [A, Matrix.add_apply, Matrix.one_apply, update_apply, Nat.cast_add, Nat.cast_mul]
  dsimp [d, s, E, r]
  push_cast
  split_ifs <;> ring

private theorem sum_entries (m : ℕ) :
    (∑ i, ∑ j, A m i j) = (dim m : ℚ)^2 + dim m + 3*r m := by
  have hA (i j : Fin (dim m)) : A m i j = E i j +
      (1 + r m * (E 0 i * E 1 j + E 1 i * E 2 j + E 2 i * E 2 j)) := by
    simp [A, Matrix.one_apply, update_apply, E, eq_comm]
  have hs (c : ℚ) (j : Fin (dim m)) : (∑ i, c * E j i) = c := by
    rw [← Finset.mul_sum, sum_E, mul_one]
  have hrow (i : Fin (dim m)) : (∑ j, A m i j) = 1 + dim m + r m * (E 0 i + E 1 i + E 2 i) := by
    simp_rw [hA, mul_add, ← mul_assoc, Finset.sum_add_distrib]
    simp only [sum_E, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  simp_rw [hrow, mul_add, Finset.sum_add_distrib]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

theorem result : type_of% @main := by
  intro m
  refine ⟨A m, positive m, ?_, ?_, ?_, ?_⟩
  · rw [show (((m+2:ℕ):ℚ)) = r m by simp [r]]
    exact polynomial_update m
  · intro h
    obtain ⟨v,h₁,h₂⟩ := jordan m
    exact h₂ (diagonal_no_chain h v h₁)
  · simpa [r] using sum_entries m
  · rw [sum_entries]
    simp [dim, r]
    nlinarith

end PositiveJordan

theorem OMA.solution : type_of% @OMA.S_mo_345339.main := PositiveJordan.result