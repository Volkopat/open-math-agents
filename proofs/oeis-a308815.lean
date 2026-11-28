import OMAStatements.S_oeis_a308815

/-! Proof of the Mathar recurrence for A308815 (known-result formalization: creative telescoping).
Reflect the sum to c(n) = sum_j C(n,j) (-1/2)^j Catalan(n+j), so a(n) = (-32)^n c(n).
A Zeilberger certificate G gives the order-2 recurrence for c by telescoping;
(3m+5) times Mathar at m+3 equals 32768 (-32)^m times the sum of two shifted copies. -/

namespace OMA.S_oeis_a308815

open Finset

/-- Reflected summand: `C(n,j) (-1/2)^j Catalan(n+j)`. -/
def H (n j : ℕ) : ℚ := (n.choose j : ℚ) * (-1 / 2 : ℚ) ^ j * (catalan (n + j) : ℚ)

def c (n : ℕ) : ℚ := ∑ j ∈ range (n + 1), H n j

/-- Certificate polynomial. -/
def Nc (n j : ℚ) : ℚ := 6*j^2*n^2 + 13*j^2*n + 5*j^2 + 48*j*n^3 + 185*j*n^2 + 225*j*n + 82*j + 42*n^4 + 226*n^3 + 430*n^2 + 340*n + 96

/-- Certificate. -/
def G (n j : ℕ) : ℚ := 2 * (j : ℚ) * Nc n j / (((n : ℚ) + 2) * ((n : ℚ) + j + 2))
  * ((n + 2).choose j : ℚ) * (-1 / 2 : ℚ) ^ j * (catalan (n + j) : ℚ)

lemma chU (N j : ℕ) : ((N : ℚ) + 1) * (N.choose j : ℚ) = ((N : ℚ) + 1 - j) * ((N + 1).choose j : ℚ) := by
  rcases le_or_gt j (N + 1) with h | h
  · have e := Nat.choose_mul_succ_eq N j
    have e' : ((N.choose j * (N + 1) : ℕ) : ℚ) = (((N + 1).choose j * (N + 1 - j) : ℕ) : ℚ) := by
      rw [e]
    push_cast [Nat.cast_sub h] at e'
    linear_combination e'
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma chS (N r : ℕ) : ((r : ℚ) + 1) * (N.choose (r + 1) : ℚ) = ((N : ℚ) - r) * (N.choose r : ℚ) := by
  rcases Nat.lt_or_ge N r with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have e := Nat.choose_succ_right_eq N r
    have e' : ((N.choose (r + 1) * (r + 1) : ℕ) : ℚ) = ((N.choose r * (N - r) : ℕ) : ℚ) := by rw [e]
    push_cast [Nat.cast_sub h] at e'
    linear_combination e'

lemma catS (m : ℕ) : (catalan (m + 1) : ℚ) = 2 * (2 * (m : ℚ) + 1) / ((m : ℚ) + 2) * (catalan m : ℚ) := by
  have e1 := succ_mul_catalan_eq_centralBinom (m + 1)
  have e2 := succ_mul_catalan_eq_centralBinom m
  have e3 := Nat.succ_mul_centralBinom_succ m
  have e1' : (((m + 1 + 1) * catalan (m + 1) : ℕ) : ℚ) = ((Nat.centralBinom (m + 1) : ℕ) : ℚ) := by rw [e1]
  have e2' : (((m + 1) * catalan m : ℕ) : ℚ) = ((Nat.centralBinom m : ℕ) : ℚ) := by rw [e2]
  have e3' : (((m + 1) * Nat.centralBinom (m + 1) : ℕ) : ℚ) = ((2 * (2 * m + 1) * Nat.centralBinom m : ℕ) : ℚ) := by
    rw [e3]
  push_cast at e1' e2' e3'
  have d : ((m : ℚ) + 2) ≠ 0 := by positivity
  have d1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff d]
  apply mul_left_cancel₀ d1
  linear_combination ((m : ℚ) + 1) * e1' + e3' - 2 * (2 * (m : ℚ) + 1) * e2'

lemma s0 (n j : ℕ) : (n.choose j : ℚ)
    = ((n + 2).choose j : ℚ) * ((n : ℚ) + 1 - j) * ((n : ℚ) + 2 - j) / (((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
  have h1 := chU n j
  have h2 := chU (n + 1) j
  push_cast at h2
  have d1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have d2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  rw [eq_div_iff (mul_ne_zero d1 d2)]
  linear_combination ((n : ℚ) + 2) * h1 + ((n : ℚ) + 1 - j) * h2

lemma s1 (n j : ℕ) : ((n + 1).choose j : ℚ) = ((n + 2).choose j : ℚ) * ((n : ℚ) + 2 - j) / ((n : ℚ) + 2) := by
  have h2 := chU (n + 1) j
  push_cast at h2
  have d2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  rw [eq_div_iff d2]
  linear_combination h2

lemma s3 (n j : ℕ) : ((n + 2).choose (j + 1) : ℚ) = ((n + 2).choose j : ℚ) * ((n : ℚ) + 2 - j) / ((j : ℚ) + 1) := by
  have h := chS (n + 2) j
  push_cast at h
  have d : ((j : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff d]
  linear_combination h

lemma tel (n j : ℕ) :
    (2 * (n : ℚ) + 1) * (2 * n + 2) * (3 * n + 5) * H n j
      - ((n : ℚ) + 1) * (21 * n ^ 2 + 53 * n + 31) * H (n + 1) j
      - ((n : ℚ) + 2) * (2 * n + 5) * (3 * n + 2) * H (n + 2) j
      = G n (j + 1) - G n j := by
  unfold H G
  rw [show n + 1 + j = (n + j) + 1 by ring, show n + 2 + j = (n + j + 1) + 1 by ring,
    show n + (j + 1) = (n + j) + 1 by ring, catS (n + j + 1), catS (n + j), s0 n j, s1 n j, s3 n j, pow_succ]
  unfold Nc
  push_cast
  have d1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have d2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  have d3 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have d4 : ((n : ℚ) + j + 2) ≠ 0 := by positivity
  have d5 : ((n : ℚ) + j + 1 + 2) ≠ 0 := by positivity
  have d6 : ((n : ℚ) + (j + 1) + 2) ≠ 0 := by positivity
  field_simp
  ring

lemma ext (m k : ℕ) : ∑ j ∈ range (m + 1 + k), H m j = c m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, sum_range_succ, ih]
    unfold H
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma L2 (n : ℕ) :
    (2 * (n : ℚ) + 1) * (2 * n + 2) * (3 * n + 5) * c n
      - ((n : ℚ) + 1) * (21 * n ^ 2 + 53 * n + 31) * c (n + 1)
      - ((n : ℚ) + 2) * (2 * n + 5) * (3 * n + 2) * c (n + 2) = 0 := by
  have hs := sum_range_sub (G n) (n + 3)
  have hG0 : G n 0 = 0 := by simp [G]
  have hGe : G n (n + 3) = 0 := by
    unfold G; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hG0, hGe] at hs
  have e0 := ext n 2
  have e1 := ext (n + 1) 1
  have e2 := ext (n + 2) 0
  rw [show n + 1 + 2 = n + 3 by ring] at e0
  rw [show n + 1 + 1 + 1 = n + 3 by ring] at e1
  rw [show n + 2 + 1 + 0 = n + 3 by ring] at e2
  rw [← e0, ← e1, ← e2, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  rw [sum_congr rfl (fun j _ => tel n j), hs]
  ring

lemma refl (n : ℕ) : (a n : ℚ) = (-32 : ℚ) ^ n * c n := by
  unfold a c H
  push_cast
  rw [← sum_range_reflect, mul_sum, mul_sum]
  refine sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ n := by simp at hj; omega
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  rw [show j + k + 1 - 1 - j = k by omega, show 2 * (j + k) - k = j + k + j by omega,
    ← Nat.choose_symm_add]
  have key : (-32 : ℚ) ^ (j + k) * (-1 / 2) ^ j = 16 ^ (j + k) * (-2) ^ k := by
    rw [show (-32 : ℚ) = 16 * (-2) by norm_num, mul_pow, pow_add (-2 : ℚ),
      show (16 : ℚ) ^ (j + k) * ((-2) ^ j * (-2) ^ k) * (-1 / 2) ^ j
        = 16 ^ (j + k) * (-2) ^ k * ((-2) * (-1 / 2)) ^ j by rw [mul_pow]; ring]
    norm_num
  linear_combination (-(((j + k).choose j : ℚ) * (catalan (j + k + j) : ℚ))) * key

theorem solution_main :
    ∀ n : ℕ, 3 ≤ n →
      (n : ℤ) * (2 * n + 1) * a n - 32 * (9 * (n : ℤ) - 4) * (n - 1) * a (n - 1)
        + 1024 * (3 * (n : ℤ) ^ 2 - 23 * n + 29) * a (n - 2)
        + 65536 * ((n : ℤ) - 2) * (2 * n - 5) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega]
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  rw [refl, refl, refl, refl]
  have h0 := L2 m
  have h1 := L2 (m + 1)
  push_cast at h1
  have d : (3 * (m : ℚ) + 5) ≠ 0 := by positivity
  apply mul_left_cancel₀ d
  simp only [pow_succ]
  linear_combination (32768 * (-32 : ℚ) ^ m) * (h1 + h0)

end OMA.S_oeis_a308815

theorem OMA.solution : type_of% @OMA.S_oeis_a308815.main := OMA.S_oeis_a308815.solution_main
