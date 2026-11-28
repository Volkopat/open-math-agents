import OMAStatements.S_oeis_a091699

/-!
# The recurrence for OEIS A091699

Let R_n encode row n of A063967 and let M send X^n to the nth inverse row
sum. The matrix inverse identity gives M(R_n) = 1. The two-step recurrence
for R_n yields a differential operator D with M(D(R_n)) = 0 for every n.
The unit diagonal transfers this identity to all monomials. Expanding
D(X^(m+1)) then gives Mathar's recurrence at index m+3.
-/

namespace A091699Proof

open OMA.S_oeis_a091699 Polynomial

theorem source_diagonal (n : ℕ) : triangle n n = 1 := by
  unfold triangle
  rw [Finset.sum_eq_single n]
  · simp
  · intro j hj hne
    have h := Finset.mem_range.mp hj
    simp [Nat.choose_eq_zero_of_lt (show j < n by omega)]
  · simp

theorem source_above (n k : ℕ) (h : n < k) : triangle n k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have h' := Finset.mem_range.mp hj
  simp [Nat.choose_eq_zero_of_lt (show j < k by omega)]

theorem inverse_above (n k : ℕ) (h : n < k) : inverseEntry n k = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [inverseEntry, if_neg (by omega : n ≠ k)]
    have hz : (∑ i : Fin n, triangle n i.val * inverseEntry i.val k) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [ih i.val i.isLt (lt_trans i.isLt h), mul_zero]
    rw [hz, sub_zero]

theorem inverse_identity (n k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), triangle n i * inverseEntry i k) =
      (if n = k then 1 else 0) := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range, source_diagonal, one_mul]
  conv_lhs => rhs; rw [inverseEntry]
  abel

theorem row_weight (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), triangle n i * a i) = 1 := by
  have pad (i : ℕ) (hi : i ≤ n) :
      a i = ∑ k ∈ Finset.range (n + 1), inverseEntry i k := by
    apply Finset.sum_subset (Finset.range_mono (by omega : i + 1 ≤ n + 1))
    intro k _ hk
    apply inverse_above
    simp only [Finset.mem_range] at hk
    omega
  calc
    _ = ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          triangle n i * inverseEntry i k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pad i (by have := Finset.mem_range.mp hi; omega), Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (n + 1), (if n = k then (1 : ℤ) else 0) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => inverse_identity n k
    _ = 1 := by simp

abbrev P := Polynomial ℤ

noncomputable def q : P := X + 1

/-- Binomial weights of the source row in powers of q. -/
def weight (n j : ℕ) : ℤ := if j ≤ n then (j.choose (n - j) : ℤ) else 0

theorem weight_step (n j : ℕ) :
    weight (n + 2) (j + 1) = weight (n + 1) j + weight n j := by
  by_cases h : j ≤ n
  · have h₁ : n + 2 - (j + 1) = (n - j) + 1 := by omega
    have h₂ : n + 1 - j = (n - j) + 1 := by omega
    simp [weight, h, show j + 1 ≤ n + 2 by omega, show j ≤ n + 1 by omega,
      h₁, h₂, Nat.choose_succ_succ, add_comm]
  · by_cases he : j = n + 1
    · subst j; simp [weight]
    · simp [weight, h, show ¬ j + 1 ≤ n + 2 by omega, show ¬ j ≤ n + 1 by omega]

noncomputable def row (n : ℕ) : P :=
  ∑ j ∈ Finset.range (n + 1), C (weight n j) * q ^ j

theorem row_zero : row 0 = 1 := by simp [row, weight]

theorem row_one : row 1 = q := by simp [row, weight, Finset.sum_range_succ]

theorem row_step (n : ℕ) : row (n + 2) = q * (row (n + 1) + row n) := by
  have extend : (∑ j ∈ Finset.range (n + 2), C (weight n j) * q ^ j) = row n := by
    rw [Finset.sum_range_succ]
    simp [row, weight]
  conv_lhs => unfold row; rw [Finset.sum_range_succ']
  have hz : weight (n + 2) 0 = 0 := by simp [weight]
  rw [hz]
  simp only [map_zero, zero_mul, add_zero]
  rw [← extend]
  change _ = q * ((∑ j ∈ Finset.range (n + 2), C (weight (n + 1) j) * q ^ j) + _)
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [weight_step, map_add, pow_succ]
  ring

theorem row_coeff (n k : ℕ) : (row n).coeff k = triangle n k := by
  unfold row triangle
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  simp [q, coeff_X_add_one_pow, weight, Nat.le_of_lt_succ (Finset.mem_range.mp hj)]

theorem row_expansion (n : ℕ) :
    row n = ∑ k ∈ Finset.range (n + 1), C (triangle n k) * X ^ k := by
  ext k
  rw [row_coeff, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases h : k < n + 1
  · simp [h]
  · simp [h, source_above n k (by omega)]

/-- The moment of X^k is the kth row sum of the inverse triangle. -/
noncomputable def moment : P →ₗ[ℤ] ℤ :=
  Polynomial.lsum fun k => a k • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)

theorem moment_pow (k : ℕ) : moment (X ^ k) = a k := by
  rw [← monomial_one_right_eq_X_pow]
  simp [moment, Polynomial.lsum_apply, sum_monomial_index]

theorem apply_C_mul (L : P →ₗ[ℤ] ℤ) (z : ℤ) (p : P) :
    L (C z * p) = z * L p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul]
  rfl

theorem moment_row (n : ℕ) : moment (row n) = 1 := by
  rw [row_expansion, map_sum]
  simpa only [apply_C_mul, moment_pow] using row_weight n

noncomputable def b (n : ℕ) : ℤ := moment (q * row n)

noncomputable def c (n : ℕ) : ℤ := moment (q ^ 2 * row n)

theorem b_step (n : ℕ) : b (n + 1) + b n = 1 := by
  simpa only [row_step, mul_add, map_add, b] using moment_row (n + 2)

theorem c_step (n : ℕ) : c (n + 1) + c n = b (n + 2) := by
  unfold b c
  rw [← map_add, row_step]
  congr 1
  ring

/-- A relation between the first two shifts of the row under the moment map. -/
theorem moments_relation (n : ℕ) : 2 * c n + (2 * (n : ℤ) + 1) * b n = n + 1 := by
  have hb₀ : b 0 = 1 := by rw [b, row_zero, mul_one, ← row_one, moment_row]
  induction n with
  | zero =>
    have hc₀ : c 0 = b 1 := by simp only [b, c, row_zero, row_one, mul_one, pow_two]
    have hb₁ := b_step 0
    rw [hc₀, hb₀]
    norm_num at hb₁ ⊢
    omega
  | succ n ih =>
    have hb : b (n + 1) = 1 - b n := by linarith only [b_step n]
    have hc : c (n + 1) = b n - c n := by
      linarith only [c_step n, b_step n, b_step (n + 1)]
    rw [hc, hb]
    push_cast
    linear_combination -ih

theorem derivative_q : derivative q = 1 := by simp [q]

/-- Differentiating the row recurrence gives an identity involving two adjacent rows. -/
theorem row_derivative (n : ℕ) :
    q * (q + 4) * derivative (row n) =
      (n + 1 : P) * row (n + 1) + (2 * (n : P) - q) * row n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [row_zero, row_one]
  | one =>
    rw [show (1 : ℕ) + 1 = 0 + 2 by decide, row_step, row_one, row_zero, derivative_q]
    push_cast
    ring
  | more n h₀ h₁ =>
    rw [row_step n] at h₁
    rw [row_step (n + 1), row_step n, derivative_mul, derivative_q, map_add]
    push_cast at h₁ ⊢
    linear_combination q * h₀ + q * h₁

/-- A polynomial differential operator whose moments give Mathar's recurrence. -/
noncomputable def operator : P →ₗ[ℤ] P :=
  (LinearMap.mulLeft ℤ ((2 * q - 1) * (q * (q + 4)))).comp derivative +
    LinearMap.mulLeft ℤ (4 * q ^ 2 + 2 * q - 2)

theorem operator_apply (p : P) :
    operator p = (2 * q - 1) * (q * (q + 4) * derivative p) +
      (4 * q ^ 2 + 2 * q - 2) * p := by
  simp only [operator, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  ring

noncomputable def residual : P →ₗ[ℤ] ℤ := moment.comp operator

theorem residual_row (n : ℕ) : residual (row n) = 0 := by
  have h : operator (row n) =
      C (2 * ((n : ℤ) + 1)) * (q * row (n + 1)) - C ((n : ℤ) + 1) * row (n + 1) +
      C (2 : ℤ) * (q ^ 2 * row n) + C (4 * (n : ℤ) + 3) * (q * row n) -
      C (2 * (n : ℤ) + 2) * row n := by
    rw [operator_apply, row_derivative]
    simp only [map_add, map_mul, map_ofNat, map_natCast, map_one]
    ring
  change moment (operator (row n)) = 0
  rw [h, map_sub, map_add, map_add, map_sub]
  simp only [apply_C_mul, moment_row, mul_one]
  change 2 * ((n : ℤ) + 1) * b (n + 1) - ((n : ℤ) + 1) + 2 * c n +
    (4 * (n : ℤ) + 3) * b n - (2 * (n : ℤ) + 2) = 0
  have hb : b (n + 1) = 1 - b n := by linarith only [b_step n]
  rw [hb]
  linear_combination moments_relation n

/-- The unit diagonal lets us pass from rows to all monomials by induction. -/
theorem residual_pow (n : ℕ) : residual (X ^ n) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h := residual_row n
    rw [row_expansion, map_sum, Finset.sum_range_succ] at h
    simp only [apply_C_mul, source_diagonal, one_mul] at h
    have hz : (∑ k ∈ Finset.range n, triangle n k * residual (X ^ k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [ih k (Finset.mem_range.mp hk), mul_zero]
    simpa only [hz, zero_add] using h

theorem recurrence (m : ℕ) :
    2 * ((m : ℤ) + 3) * a (m + 3) + (13 * ((m : ℤ) + 3) - 16) * a (m + 2) +
      4 * (4 * ((m : ℤ) + 3) - 7) * a (m + 1) + 5 * (((m : ℤ) + 3) - 2) * a m = 0 := by
  have h : operator (X ^ (m + 1)) =
      C (2 * ((m : ℤ) + 3)) * X ^ (m + 3) +
      C (13 * ((m : ℤ) + 3) - 16) * X ^ (m + 2) +
      C (4 * (4 * ((m : ℤ) + 3) - 7)) * X ^ (m + 1) +
      C (5 * (((m : ℤ) + 3) - 2)) * X ^ m := by
    rw [operator_apply, derivative_X_pow_succ]
    simp only [q, map_sub, map_add, map_mul, map_ofNat, map_natCast, map_one, pow_succ]
    ring
  have hz := residual_pow (m + 1)
  change moment (operator (X ^ (m + 1))) = 0 at hz
  simpa only [h, map_add, apply_C_mul, moment_pow] using hz

end A091699Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a091699.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.add_sub_cancel,
    show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega] using
    A091699Proof.recurrence m
