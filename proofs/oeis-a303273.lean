import OMAStatements.S_oeis_a303273
import Mathlib

open OMA.S_oeis_a303273


theorem choose2 (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd

theorem T_val (m k : ℕ) : (2 * T m k : ℤ) = (m : ℤ) * ((m : ℤ) - 1) + 2 * k * m + 2 := by
  have h := choose2 m
  unfold T
  have e : 2 * (m.choose 2 + k * m + 1) = m * (m - 1) + 2 * k * m + 2 := by
    rw [mul_add, mul_add, h]; ring
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel] at e
    have e' : ((2 * ((m + 1).choose 2 + k * (m + 1) + 1) : ℕ) : ℤ) = (((m + 1) * m + 2 * k * (m + 1) + 2 : ℕ) : ℤ) := by
      rw [e]
    push_cast at e' ⊢
    linarith

theorem conj1 (n : ℕ) : T (2 * n) (n + 4) = A186353 (4 * n + 1) := by
  unfold A186353
  have hM : (4 * n + 1) * (4 * n + 1 + 1) / 2 = 8 * n ^ 2 + 6 * n + 1 := by
    rw [show (4 * n + 1) * (4 * n + 1 + 1) = 2 * (8 * n ^ 2 + 6 * n + 1) by ring]
    simp
  rw [hM]
  have hf : ((Finset.Icc 1 (8 * n ^ 2 + 6 * n + 1)).filter fun i => 2 * i - 1 < 8 * n ^ 2 + 6 * n + 1) =
      Finset.Icc 1 (4 * n ^ 2 + 3 * n) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    generalize n ^ 2 = q
    omega
  rw [hf, Nat.card_Icc]
  have h := T_val (2 * n) (n + 4)
  have : (T (2 * n) (n + 4) : ℤ) = ((4 * n + 1 + (4 * n ^ 2 + 3 * n + 1 - 1) : ℕ) : ℤ) := by
    push_cast at h ⊢
    nlinarith
  exact_mod_cast this

theorem conj2 (n : ℕ) : (T (2 * n) (n + 5) : ℤ) = A184103 (8 * n + 1) := by
  unfold A184103
  have hc : ⌈(((8 * n + 1 : ℕ) : ℚ) ^ 2 / 16)⌉ = 4 * (n : ℤ) ^ 2 + n + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor
    · nlinarith [sq_nonneg (n : ℚ)]
    · nlinarith [sq_nonneg (n : ℚ)]
  rw [hc]
  have h := T_val (2 * n) (n + 5)
  push_cast at h ⊢
  nlinarith

theorem conj3 (n : ℕ) : (T (n + 2) (2 * n) : ℤ) = A249013 (5 * n + 4) := by
  unfold A249013
  have hpar : ∃ q : ℕ, 5 * n ^ 2 + 11 * n = 2 * q := by
    rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨10 * r ^ 2 + 11 * r, by ring⟩
    · exact ⟨10 * r ^ 2 + 21 * r + 8, by ring⟩
  obtain ⟨q, hq⟩ := hpar
  have hq' : (5 * (n : ℚ) ^ 2 + 11 * n) = 2 * q := by exact_mod_cast hq
  have hf : ⌊((((5 * n + 4 : ℕ) : ℚ) - 1) * (((5 * n + 4 : ℕ) : ℚ) + 4) / 10)⌋ = (q : ℤ) + 2 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · nlinarith
    · nlinarith
  rw [hf]
  have h := T_val (n + 2) (2 * n)
  have hqz : (5 * (n : ℤ) ^ 2 + 11 * n) = 2 * q := by exact_mod_cast hq
  push_cast at h ⊢
  nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a303273.main := fun n => ⟨conj1 n, conj2 n, conj3 n⟩
