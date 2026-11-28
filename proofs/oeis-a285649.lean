import OMAStatements.S_oeis_a285649
import Mathlib

open OMA.S_oeis_a285649 PowerSeries

namespace P285649

def N0 (x y : ℤ) : Prop := x = 0 ∧ y = 0

def N1 (x y : ℤ) : Prop :=
  (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1)

def N3 (x y : ℤ) : Prop :=
  (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = 0) ∨ (x = -2 ∧ y = 0) ∨ (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = -2) ∨
  (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = 1) ∨ (x = -1 ∧ y = -1)

instance (x y : ℤ) : Decidable (N0 x y) := by unfold N0; infer_instance
instance (x y : ℤ) : Decidable (N1 x y) := by unfold N1; infer_instance
instance (x y : ℤ) : Decidable (N3 x y) := by unfold N3; infer_instance

theorem step (t : ℕ) (x y : ℤ) : state 73 (t + 1) x y = Nat.testBit 73
    ((state 73 t x y).toNat + 2 * ((state 73 t (x - 1) y).toNat + (state 73 t (x + 1) y).toNat +
      (state 73 t x (y - 1)).toNat + (state 73 t x (y + 1)).toNat)) := rfl

theorem s0 (x y : ℤ) : state 73 0 x y = if N0 x y then true else false := by
  show decide (x = 0 ∧ y = 0) = _
  unfold N0
  split_ifs with h <;> simp [h]

theorem s1 (x y : ℤ) : state 73 1 x y = if N1 x y then false else true := by
  rw [step, s0, s0, s0, s0, s0]
  by_cases hf : x ≤ -4 ∨ 4 ≤ x ∨ y ≤ -4 ∨ 4 ≤ y
  · have g0 : ¬ N0 x y := by unfold N0; omega
    have g1 : ¬ N0 (x - 1) y := by unfold N0; omega
    have g2 : ¬ N0 (x + 1) y := by unfold N0; omega
    have g3 : ¬ N0 x (y - 1) := by unfold N0; omega
    have g4 : ¬ N0 x (y + 1) := by unfold N0; omega
    have g5 : ¬ N1 x y := by unfold N1; omega
    simp only [g0, g1, g2, g3, g4, g5, if_false]
    decide
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    interval_cases x <;> interval_cases y <;> decide

theorem s2 (x y : ℤ) : state 73 2 x y = if N1 x y then true else false := by
  rw [step, s1, s1, s1, s1, s1]
  by_cases hf : x ≤ -4 ∨ 4 ≤ x ∨ y ≤ -4 ∨ 4 ≤ y
  · have g0 : ¬ N1 x y := by unfold N1; omega
    have g1 : ¬ N1 (x - 1) y := by unfold N1; omega
    have g2 : ¬ N1 (x + 1) y := by unfold N1; omega
    have g3 : ¬ N1 x (y - 1) := by unfold N1; omega
    have g4 : ¬ N1 x (y + 1) := by unfold N1; omega
    simp only [g0, g1, g2, g3, g4, if_false]
    decide
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    interval_cases x <;> interval_cases y <;> decide

theorem s3 (x y : ℤ) : state 73 3 x y = if N3 x y then false else true := by
  rw [step, s2, s2, s2, s2, s2]
  by_cases hf : x ≤ -4 ∨ 4 ≤ x ∨ y ≤ -4 ∨ 4 ≤ y
  · have g0 : ¬ N1 x y := by unfold N1; omega
    have g1 : ¬ N1 (x - 1) y := by unfold N1; omega
    have g2 : ¬ N1 (x + 1) y := by unfold N1; omega
    have g3 : ¬ N1 x (y - 1) := by unfold N1; omega
    have g4 : ¬ N1 x (y + 1) := by unfold N1; omega
    have g5 : ¬ N3 x y := by unfold N3; omega
    simp only [g0, g1, g2, g3, g4, g5, if_false]
    decide
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    interval_cases x <;> interval_cases y <;> decide

theorem s4 (x y : ℤ) : state 73 4 x y = false := by
  rw [step, s3, s3, s3, s3, s3]
  by_cases hf : x ≤ -4 ∨ 4 ≤ x ∨ y ≤ -4 ∨ 4 ≤ y
  · have g0 : ¬ N3 x y := by unfold N3; omega
    have g1 : ¬ N3 (x - 1) y := by unfold N3; omega
    have g2 : ¬ N3 (x + 1) y := by unfold N3; omega
    have g3 : ¬ N3 x (y - 1) := by unfold N3; omega
    have g4 : ¬ N3 x (y + 1) := by unfold N3; omega
    simp only [g0, g1, g2, g3, g4, if_false]
    decide
  · have hx1 : -3 ≤ x := by omega
    have hx2 : x ≤ 3 := by omega
    have hy1 : -3 ≤ y := by omega
    have hy2 : y ≤ 3 := by omega
    interval_cases x <;> interval_cases y <;> decide

theorem sk (k : ℕ) : (∀ x y, state 73 (4 + 2 * k) x y = false) ∧
    (∀ x y, state 73 (4 + 2 * k + 1) x y = true) := by
  induction k with
  | zero =>
    refine ⟨fun x y => s4 x y, fun x y => ?_⟩
    rw [step]; simp only [s4]; decide
  | succ k ih =>
    have h1 : ∀ x y, state 73 (4 + 2 * (k + 1)) x y = false := by
      intro x y
      rw [show 4 + 2 * (k + 1) = (4 + 2 * k + 1) + 1 by ring, step]
      simp only [ih.2]; decide
    refine ⟨h1, fun x y => ?_⟩
    rw [step]; simp only [h1]; decide

theorem st (n : ℕ) (hn : 4 ≤ n) (x y : ℤ) : state 73 n x y = decide (n % 2 = 1) := by
  obtain ⟨k, hk⟩ : ∃ k, n = 4 + 2 * k ∨ n = 4 + 2 * k + 1 := ⟨(n - 4) / 2, by omega⟩
  rcases hk with rfl | rfl
  · rw [(sk k).1]; exact (decide_eq_false (by omega)).symm
  · rw [(sk k).2]; exact (decide_eq_true (by omega)).symm

theorem geo (n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℤ) ^ i = 2 ^ n - 1 := by
  have := geom_sum_mul (2 : ℤ) n
  norm_num at this
  linarith

theorem geo' (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (2 : ℤ) ^ (n - i) = 2 ^ (n + 1) - 1 := by
  rw [← geo (n + 1)]
  have := Finset.sum_range_reflect (fun i => (2 : ℤ) ^ i) (n + 1)
  simpa using this

theorem ha (n : ℕ) (hn : 4 ≤ n) : a n = if n % 2 = 0 then 0 else 2 ^ (n + 1) - 1 := by
  unfold a digits
  simp only [st n hn]
  split_ifs with h
  · simp [show ¬ (n % 2 = 1) by omega]
  · simp only [show n % 2 = 1 by omega, decide_true, Bool.toNat_true, Nat.cast_one, one_mul]
    exact geo' n

theorem rec8 (n : ℕ) (hn : 7 < n) : a n = 5 * a (n - 2) - 4 * a (n - 4) := by
  rw [ha n (by omega), ha (n - 2) (by omega), ha (n - 4) (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]; ring
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring

end P285649

open P285649 in
theorem OMA.solution : type_of% @OMA.S_oeis_a285649.main := by
  have v0 : a 0 = 1 := by decide +kernel
  have v1 : a 1 = 2 := by decide +kernel
  have v2 : a 2 = 1 := by decide +kernel
  have v3 : a 3 = 12 := by decide +kernel
  have v4 : a 4 = 0 := by rw [ha 4 (by norm_num)]; norm_num
  have v5 : a 5 = 63 := by rw [ha 5 (by norm_num)]; norm_num
  have v6 : a 6 = 0 := by rw [ha 6 (by norm_num)]; norm_num
  have v7 : a 7 = 255 := by rw [ha 7 (by norm_num)]; norm_num
  refine ⟨?_, fun n h1 h2 => by rw [ha n (by omega)]; simp [h2],
    fun n h1 h2 => by rw [ha n (by omega)]; simp [h2]; (try ring), rec8⟩
  have hL : (PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) : PowerSeries ℤ) =
      PowerSeries.mk a - C (5 : ℤ) * (PowerSeries.mk a * X ^ 2) + C (4 : ℤ) * (PowerSeries.mk a * X ^ 4) := by
    (try simp only [map_ofNat, pow_one]) <;> ring
  have hR : (1 + 2 * X - 4 * X ^ 2 + 2 * X ^ 3 - X ^ 4 + 11 * X ^ 5 + 4 * X ^ 6 - 12 * X ^ 7 : PowerSeries ℤ) = 1 + C (2 : ℤ) * X ^ 1 - C (4 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 3 - X ^ 4 + C (11 : ℤ) * X ^ 5 + C (4 : ℤ) * X ^ 6 - C (12 : ℤ) * X ^ 7 := by
    (try simp only [map_ofNat, pow_one]) <;> ring
  rw [hL, hR]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
    coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  · norm_num [v0]
  · norm_num [v1]
  · norm_num [v0, v2]
  · norm_num [v1, v3]
  · norm_num [v0, v2, v4]
  · norm_num [v1, v3, v5]
  · norm_num [v2, v4, v6]
  · norm_num [v3, v5, v7]
  · have := rec8 (n + 8) (by omega)
    simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 8 by omega] at *
    simp only [show 2 ≤ n + 8 by omega, show 4 ≤ n + 8 by omega, if_true]
    simp only [show n + 8 - 2 = n + 6 by omega, show n + 8 - 4 = n + 4 by omega] at *
    have e : ∀ k : ℕ, k ≤ 7 → (n + 8 = k) = False := fun k hk => by simp only [eq_iff_iff, iff_false]; omega
    have e2 : ∀ k : ℕ, 1 ≤ k → k ≤ 7 → (n + 8 - k = 0) = False := fun k h1 h2 => by
      simp only [eq_iff_iff, iff_false]; omega
    have e3 : ∀ k : ℕ, k ≤ 8 → (k ≤ n + 8) = True := fun k hk => by simp only [eq_iff_iff, iff_true]; omega
    have e4 : (n + 4 = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
    have e5 : (n + 6 = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
    simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
      e 5 (by omega), e 6 (by omega), e 7 (by omega), e2 1 (by omega) (by omega),
      e2 3 (by omega) (by omega), e2 5 (by omega) (by omega), e2 6 (by omega) (by omega),
      e2 7 (by omega) (by omega), e3 1 (by omega), e3 3 (by omega), e3 5 (by omega),
      e3 6 (by omega), e3 7 (by omega), e4, e5, if_false, if_true]
    linarith

