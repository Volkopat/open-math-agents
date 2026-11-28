import OMAStatements.S_oeis_a267354
import Mathlib

namespace A267354Aux

open OMA.S_oeis_a267354 in
lemma rule_iff (l c r : Bool) : ruleOut 123 l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ ¬ c = true ∧ r = true) ∨ (¬ l = true ∧ c = true ∧ r = true) ∨ (l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (l = true ∧ ¬ c = true ∧ r = true) ∨ (l = true ∧ c = true ∧ ¬ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267354 in
lemma s0 (i : ℤ) : cell 123 0 i = true ↔ i = 0 := by
  simp [cell]

open OMA.S_oeis_a267354 in
lemma s1 (i : ℤ) : cell 123 1 i = true ↔ ¬(i = 0) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a267354 in
lemma state (t : ℕ) (ht : 1 ≤ t) : ∀ i : ℤ, cell 123 t i = true ↔
    ((t % 2 = 0 ∧ (i = -1 ∨ i = 0 ∨ i = 1)) ∨ (t % 2 = 1 ∧ ¬(i = 0))) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s1]
    omega
  | succ t ht ih =>
    intro i
    rw [cell, rule_iff]
    simp only [ih]
    omega

open OMA.S_oeis_a267354 in
lemma on_even (t : ℕ) (ht : 2 ≤ t) (he : t % 2 = 0) : ((onCount 123 t : ℕ) : ℤ) = 3 := by
  have h := state t (by omega)
  unfold onCount
  push_cast
  have val : ∀ j : ℕ, (if cell 123 t ((j : ℤ) - t) = true then (1 : ℤ) else 0) =
      (if j = t - 1 then (1 : ℤ) else 0) + (if j = t then (1 : ℤ) else 0) +
      (if j = t + 1 then (1 : ℤ) else 0) := by
    intro j
    simp only [h]
    split_ifs <;> omega
  have h1 : t - 1 < 2 * t + 1 := by omega
  have h2 : t < 2 * t + 1 := by omega
  have h3 : t + 1 < 2 * t + 1 := by omega
  simp only [val, Finset.sum_add_distrib]
  simp [h1, h2, h3]

open OMA.S_oeis_a267354 in
lemma on_odd (t : ℕ) (ho : t % 2 = 1) :
    ((onCount 123 t : ℕ) : ℤ) = 2 * (t : ℤ) := by
  have h := state t (by omega)
  unfold onCount
  push_cast
  have val : ∀ j : ℕ, (if cell 123 t ((j : ℤ) - t) = true then (1 : ℤ) else 0) =
      1 - (if j = t then (1 : ℤ) else 0) := by
    intro j
    simp only [h]
    split_ifs <;> omega
  have h2 : t < 2 * t + 1 := by omega
  simp only [val, Finset.sum_sub_distrib]
  simp [h2]

open OMA.S_oeis_a267354 in
lemma a_cl (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = ((2 * (-1 : ℚ) ^ n + 2) * (n : ℚ) - 3 * (-1 : ℚ) ^ n - 1) / 2 := by
  unfold a
  rcases Nat.even_or_odd n with he | ho
  · have h := on_even n (by rcases he with ⟨k, rfl⟩; omega) (Nat.even_iff.mp he)
    rw [h, he.neg_one_pow]
    push_cast
    ring
  · have h := on_odd n (Nat.odd_iff.mp ho)
    rw [h, ho.neg_one_pow]
    push_cast
    ring

open OMA.S_oeis_a267354 in
lemma a_0 : (a 0 : ℚ) = 0 := by
  have h : a 0 = 0 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267354 in
lemma a_1 : (a 1 : ℚ) = 1 := by
  rw [a_cl 1 (by norm_num)]; norm_num

open OMA.S_oeis_a267354 in
lemma a_2 : (a 2 : ℚ) = 2 := by
  rw [a_cl 2 (by norm_num)]; norm_num

open OMA.S_oeis_a267354 in
lemma a_3 : (a 3 : ℚ) = 1 := by
  rw [a_cl 3 (by norm_num)]; norm_num

open OMA.S_oeis_a267354 in
lemma a_4 : (a 4 : ℚ) = 6 := by
  rw [a_cl 4 (by norm_num)]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267354Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267354 A267354Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267354.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    refine (a_cl n (by omega)).trans ?_
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 2 = m + 3 by omega, show m + 5 - 4 = m + 1 by omega]
    rw [a_cl (m + 5) (by omega), a_cl (m + 3) (by omega), a_cl (m + 1) (by omega)]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (PowerSeries.X * (1 + 2 * PowerSeries.X - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 1 + PowerSeries.C 2 * PowerSeries.X ^ 2 + PowerSeries.C (-1) * PowerSeries.X ^ 3 + PowerSeries.C 2 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_0, a_1, a_2, a_3] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4] <;> norm_num
    · have f0 := a_cl (n + 5) (by omega)
      have f2 := a_cl (n + 3) (by omega)
      have f4 := a_cl (n + 1) (by omega)
      simp [f0, f2, f4]
      ring
