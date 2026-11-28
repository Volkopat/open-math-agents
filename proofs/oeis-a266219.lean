import OMAStatements.S_oeis_a266219
import Mathlib

namespace OMA.S_oeis_a266219

open PowerSeries

theorem state_one : state 7 1 = fun x => decide (x ≠ 1) := by
  funext x
  simp only [state, step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 1 by omega)]
    decide

theorem state_two : state 7 2 = fun _ => false := by
  funext x
  rw [show state 7 2 = step 7 (state 7 1) from rfl, state_one]
  simp only [step]
  rcases (show x ≤ -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ 1 by omega), decide_eq_true (show x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ 1 by omega), decide_eq_true (show x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ 1 by omega)]
    decide

theorem state_ge (n : ℕ) (hn : 2 ≤ n) : state 7 n = fun _ => decide (n % 2 = 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact state_two
  | succ n hn ih =>
    funext x
    rw [show state 7 (n + 1) = step 7 (state 7 n) from rfl, ih]
    simp only [step]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [decide_eq_false (show ¬ (n % 2 = 1) by omega),
        decide_eq_true (show (n + 1) % 2 = 1 by omega)]
      decide
    · rw [decide_eq_true h, decide_eq_false (show ¬ ((n + 1) % 2 = 1) by omega)]
      decide

theorem c_pos (n : ℕ) (hn : 1 ≤ n) : c n = n % 2 := by
  rcases (show n = 1 ∨ 2 ≤ n by omega) with h | h
  · subst h; decide
  · rw [c, state_ge n h]
    rcases Nat.mod_two_eq_zero_or_one n with h' | h'
    · rw [decide_eq_false (show ¬ (n % 2 = 1) by omega), h']
      rfl
    · rw [decide_eq_true h', h']
      rfl

theorem a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  rw [a, a, Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
  ring

theorem a0 : a 0 = 1 := by decide

/-- The exact form: 99 a(n) = 109 * 10^n - 10 for even n and - 1 for odd n. -/
theorem exact (n : ℕ) :
    (n % 2 = 0 → 99 * a n + 10 = 109 * 10 ^ n) ∧ (n % 2 = 1 → 99 * a n + 1 = 109 * 10 ^ n) := by
  induction n with
  | zero => exact ⟨fun _ => by rw [a0]; norm_num, fun h => absurd h (by norm_num)⟩
  | succ n ih =>
    rw [a_succ, c_pos (n + 1) (by omega), pow_succ]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have e := ih.1 h
      refine ⟨fun h' => absurd h' (by omega), fun _ => ?_⟩
      rw [show (n + 1) % 2 = 1 by omega]
      linarith
    · have e := ih.2 h
      refine ⟨fun _ => ?_, fun h' => absurd h' (by omega)⟩
      rw [show (n + 1) % 2 = 0 by omega]
      linarith

theorem closed (n : ℕ) :
    (a n : ℚ) = 1 / 198 * (-9 * (-1) ^ n + 109 * 2 ^ (n + 1) * 5 ^ n - 11) := by
  have h10 : (2 : ℚ) ^ (n + 1) * 5 ^ n = 2 * 10 ^ n := by
    rw [pow_succ, show (10 : ℚ) ^ n = 2 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
    ring
  rw [mul_assoc (109 : ℚ), h10]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have e : (99 : ℚ) * a n + 10 = 109 * 10 ^ n := by exact_mod_cast (exact n).1 h
    have hp : ((-1 : ℚ)) ^ n = 1 := (Nat.even_iff.mpr h).neg_one_pow
    rw [hp]
    linarith
  · have e : (99 : ℚ) * a n + 1 = 109 * 10 ^ n := by exact_mod_cast (exact n).2 h
    have hp : ((-1 : ℚ)) ^ n = -1 := (Nat.odd_iff.mpr h).neg_one_pow
    rw [hp]
    linarith

theorem recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  have hq : (a (k + 3) : ℚ) = 10 * a (k + 2) + a (k + 1) - 10 * a k := by
    rw [closed, closed, closed, closed]
    ring
  exact_mod_cast hq

theorem a1 : a 1 = 11 := by decide
theorem a2 : a 2 = 110 := by decide

theorem gf_mul : A * ((1 - X) * (1 + X) * (1 - 10 * X)) = 1 + X - X ^ 2 := by
  have hD : A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      A - C 10 * (A * X ^ 1) - C 1 * (A * X ^ 2) + C 10 * (A * X ^ 3) := by
    simp only [map_ofNat, map_one]
    ring
  have hN : (1 + X - X ^ 2 : ℚ⟦X⟧) = C 1 * X ^ 0 + C 1 * X ^ 1 - C 1 * X ^ 2 := by
    simp only [map_one]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m <;> norm_num [a0, a1, a2]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 10 * a (m - 1) + a (m - 2) - 10 * a (m - 3) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    simp only [h1, h2, h3, Nat.zero_le, k0, k1, k2, coeff_C, if_true, if_false, hq]
    ring

theorem floor_form (n : ℕ) : (a n : ℤ) = ⌊(109 * 10 ^ n / 99 : ℚ)⌋ := by
  symm
  rw [Int.floor_eq_iff]
  push_cast
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have e : (99 : ℚ) * a n + 10 = 109 * 10 ^ n := by exact_mod_cast (exact n).1 h
    constructor
    · rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [div_lt_iff₀ (by norm_num)]; linarith
  · have e : (99 : ℚ) * a n + 1 = 109 * 10 ^ n := by exact_mod_cast (exact n).2 h
    constructor
    · rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [div_lt_iff₀ (by norm_num)]; linarith

end OMA.S_oeis_a266219

theorem OMA.solution : type_of% @OMA.S_oeis_a266219.main := by
  refine ⟨OMA.S_oeis_a266219.closed, OMA.S_oeis_a266219.recurrence, ?_,
    OMA.S_oeis_a266219.floor_form⟩
  have h0 : PowerSeries.constantCoeff ((1 - PowerSeries.X) * (1 + PowerSeries.X) *
      (1 - 10 * PowerSeries.X) : PowerSeries ℚ) ≠ 0 := by simp
  rw [← OMA.S_oeis_a266219.gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]
