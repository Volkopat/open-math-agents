import OMAStatements.S_oeis_a176610

namespace A176610Convolution

open OMA.S_oeis_a176610
open PowerSeries Finset
open scoped PowerSeries

theorem list_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n using Nat.twoStepInduction
  · rfl
  · rfl
  · rename_i n ih₀ ih₁
    simp [aList, ih₁]

theorem list_coherent (n m : ℕ) (hm : m ≤ n) : (aList n).getD m 0 = a m := by
  induction n using Nat.twoStepInduction
  · obtain rfl : m = 0 := by omega
    rfl
  · interval_cases m <;> rfl
  · rename_i n ih₀ ih₁
    rcases lt_or_eq_of_le hm with hlt | rfl
    · rw [aList, List.getD_append _ _ _ _ (by rw [list_length]; omega)]
      exact ih₁ (by omega)
    · rfl

theorem convolution (n : ℕ) :
    a (n + 2) = (∑ j ∈ range (n + 2), a j * a (n + 1 - j)) + ((n : ℤ) + 2) + 1 := by
  change (aList (n + 2)).getD (n + 2) 0 = _
  rw [aList, List.getD_append_right _ _ _ _ (by rw [list_length])]
  simp only [list_length, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  rw [list_coherent _ _ (by omega), list_coherent _ _ (by omega)]

def A : ℤ⟦X⟧ := mk a

def T : ℤ⟦X⟧ := mk (fun _ => 1)

theorem coeff_X_mul_any (P : ℤ⟦X⟧) (n : ℕ) :
    coeff n (X * P) = if 1 ≤ n then coeff (n - 1) P else 0 := by
  simpa using coeff_X_pow_mul' P 1 n

theorem geom : (1 - X) * T = 1 := by
  ext n
  cases n <;> simp [sub_mul, T, coeff_one]

def W : ℤ⟦X⟧ := mk (fun n => (n : ℤ) + 1)

theorem weighted_geom : (1 - X) * W = T := by
  ext n
  cases n <;> simp [sub_mul, W, T, Nat.cast_succ]

theorem series_eq : A = X * A ^ 2 - C 3 * X + W := by
  ext n
  induction n using Nat.twoStepInduction
  · simp [A, W, a, aList]
  · simp only [map_add, map_sub, coeff_C_mul, coeff_X, coeff_X_mul_any, le_refl,
      Nat.sub_self, W, coeff_mk]
    have h0 : coeff 0 (A ^ 2) = 1 := by
      rw [coeff_zero_eq_constantCoeff, map_pow]
      simp [A, a, aList]
    rw [h0]
    norm_num [A, a, aList]
  · rename_i n _ _
    have h1 : n + 2 ≠ 1 := by omega
    have h2 : 1 ≤ n + 2 := by omega
    simp only [map_add, map_sub, coeff_C_mul, coeff_X, h1, if_false, mul_zero, sub_zero,
      coeff_X_mul_any, h2, if_true, W, coeff_mk]
    rw [show n + 2 - 1 = n + 1 by omega]
    simp only [A, coeff_mk, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Nat.cast_add, Nat.cast_ofNat]
    simpa only [add_assoc] using convolution n

noncomputable def R : ℤ⟦X⟧ := 1 - X

noncomputable def P : ℤ⟦X⟧ := 1 - 6 * X + 13 * X ^ 2 - 24 * X ^ 3 + 12 * X ^ 4

noncomputable def S : ℤ⟦X⟧ := 1 - 2 * X * A

noncomputable def D : ℤ⟦X⟧ := 1 - 5 * X + 18 * X ^ 2 - 18 * X ^ 3 + 6 * X ^ 4

-- Clear the geometric-series denominator before completing the square.
theorem quadratic : R ^ 2 * (A - X * A ^ 2) = 1 - 3 * X * R ^ 2 := by
  have hA := congrArg (fun f : ℤ⟦X⟧ => R ^ 2 * f) series_eq
  have hW : R ^ 2 * W = 1 := by
    dsimp [R]
    rw [pow_two, mul_assoc, weighted_geom, geom]
  simp only [map_ofNat] at hA
  linear_combination hA + hW

theorem discriminant : R ^ 2 * S ^ 2 = P := by
  have h := quadratic
  dsimp [R] at h
  dsimp [R, S, P]
  linear_combination (-4 * X) * h

theorem derivative_nat (n : ℕ) : derivative ℤ (n : ℤ⟦X⟧) = 0 := by
  rw [← map_natCast (C (R := ℤ)) n, derivative_C]

theorem discriminant_derivative :
    -2 * R * S ^ 2 + R ^ 2 * (2 * S * derivative ℤ S) =
      -6 + 26 * X - 72 * X ^ 2 + 48 * X ^ 3 := by
  have h := congrArg (derivative ℤ) discriminant
  dsimp only [R, P] at h
  have h6 : derivative ℤ (6 : ℤ⟦X⟧) = 0 := derivative_nat 6
  have h13 : derivative ℤ (13 : ℤ⟦X⟧) = 0 := derivative_nat 13
  have h24 : derivative ℤ (24 : ℤ⟦X⟧) = 0 := derivative_nat 24
  have h12 : derivative ℤ (12 : ℤ⟦X⟧) = 0 := derivative_nat 12
  simp [Derivation.leibniz, smul_eq_mul, h6, h13, h24, h12] at h
  dsimp only [R]
  convert h using 1 <;> ring

theorem derivative_S : derivative ℤ S = -2 * (A + X * derivative ℤ A) := by
  have h2 : derivative ℤ (2 : ℤ⟦X⟧) = 0 := derivative_nat 2
  simp [S, Derivation.leibniz, smul_eq_mul, h2]
  ring

-- Multiply the differentiated equation by R*S and eliminate R²*S².
theorem differential :
    R * P * (X * derivative ℤ A) + (1 - 5 * X + 9 * X ^ 2 - X ^ 3) * A = D := by
  have h := discriminant_derivative
  have hSq := discriminant
  have hlin : 2 * R * P * derivative ℤ S + 4 * D * S = 0 := by
    dsimp only [R, P, D] at h hSq ⊢
    linear_combination ((1 - X) * S) * h +
      (2 * S - 2 * (1 - X) * derivative ℤ S) * hSq
  rw [derivative_S] at hlin
  dsimp only [R, P, S, D] at hlin ⊢
  apply mul_left_cancel₀ (show (-4 : ℤ⟦X⟧) ≠ 0 by
    intro h0
    rw [show (4 : ℤ⟦X⟧) = C (4 : ℤ) by simp] at h0
    have hc : -(4 : ℤ) = 0 := by
      apply C_injective (R := ℤ)
      simpa only [map_neg, map_zero] using h0
    norm_num at hc)
  linear_combination hlin

noncomputable def V : ℤ⟦X⟧ := X * derivative ℤ A

theorem coeff_V (n : ℕ) : coeff n V = (n : ℤ) * a n := by
  cases n with
  | zero => simp [V, coeff_X_mul_any]
  | succ n =>
    simp [V, coeff_derivative, A, mul_comm]

theorem coeff_weight (c : ℤ) (j n : ℕ) (hj : j ≤ n) (F : ℤ⟦X⟧) :
    coeff n (C c * X ^ j * F) = c * coeff (n - j) F := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos hj]

theorem expanded :
    C 1 * X ^ 0 * V + C (-7) * X ^ 1 * V + C 19 * X ^ 2 * V + C (-37) * X ^ 3 * V +
      C 36 * X ^ 4 * V + C (-12) * X ^ 5 * V +
      C 1 * X ^ 0 * A + C (-5) * X ^ 1 * A + C 9 * X ^ 2 * A + C (-1) * X ^ 3 * A =
    C 1 * X ^ 0 + C (-5) * X ^ 1 + C 18 * X ^ 2 + C (-18) * X ^ 3 + C 6 * X ^ 4 := by
  have h := differential
  change R * P * V + _ = D at h
  dsimp [R, P, D] at h
  simp only [map_one, map_neg, map_ofNat, pow_zero, pow_one]
  linear_combination h

end A176610Convolution

open A176610Convolution OMA.S_oeis_a176610 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a176610.main := by
  intro n hn
  have h := congrArg (coeff n) expanded
  simp only [map_add, coeff_weight _ 0 n (by omega), coeff_weight _ 1 n (by omega),
    coeff_weight _ 2 n (by omega), coeff_weight _ 3 n (by omega),
    coeff_weight _ 4 n (by omega), coeff_weight _ 5 n hn, coeff_C_mul_X_pow, show n ≠ 0 by omega, show n ≠ 1 by omega,
    show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, if_false, coeff_V, A, coeff_mk,
    Nat.sub_zero, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub hn, Nat.cast_one, Nat.cast_ofNat] at h
  linear_combination h
