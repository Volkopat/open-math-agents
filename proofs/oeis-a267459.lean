import OMAStatements.S_oeis_a267459
import Mathlib

namespace A267459Aux

open OMA.S_oeis_a267459 in
lemma rule_iff (l c r : Bool) : ruleOut 133 l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267459 in
lemma s0 (i : ℤ) : cell 133 0 i = true ↔ i = 0 := by
  simp [cell]

open OMA.S_oeis_a267459 in
lemma s1 (i : ℤ) : cell 133 1 i = true ↔ ¬(i = -1 ∨ i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a267459 in
lemma s2 (i : ℤ) : cell 133 2 i = true ↔ ¬(i = -2 ∨ i = -1 ∨ i = 1 ∨ i = 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell, rule_iff]
  simp only [s1]
  omega

open OMA.S_oeis_a267459 in
lemma state (t : ℕ) (ht : 2 ≤ t) : ∀ i : ℤ, cell 133 t i = true ↔
    ((i < -(t : ℤ) ∨ (t : ℤ) < i) ∨ (i % 2 = 0 ∧
      ((t % 2 = 0 ∧ -((t : ℤ) - 2) ≤ i ∧ i ≤ (t : ℤ) - 2) ∨
       (t % 2 = 1 ∧ -((t : ℤ) - 3) ≤ i ∧ i ≤ (t : ℤ) - 3)))) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s2]
    omega
  | succ t ht ih =>
    intro i
    rw [cell, rule_iff]
    simp only [ih]
    push_cast
    omega

open OMA.S_oeis_a267459 in
lemma on_even (t : ℕ) (ht : 2 ≤ t) (he : t % 2 = 0) : onCount 133 t = t - 1 := by
  have h := state t ht
  unfold onCount
  rw [← Finset.card_filter]
  have hset : (Finset.range (2 * t + 1)).filter (fun j : ℕ => cell 133 t ((j : ℤ) - t) = true) =
      (Finset.range (t - 1)).image (fun s => 2 * s + 2) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, h]
    constructor
    · rintro ⟨hj, hc⟩
      exact ⟨(j - 2) / 2, by omega, by omega⟩
    · rintro ⟨s, hs, rfl⟩
      constructor
      · omega
      · push_cast
        omega
  rw [hset, Finset.card_image_of_injective _ (by intro x y hxy; simp only at hxy; omega),
    Finset.card_range]

open OMA.S_oeis_a267459 in
lemma on_odd (t : ℕ) (ht : 3 ≤ t) (ho : t % 2 = 1) : onCount 133 t = t - 2 := by
  have h := state t (by omega)
  unfold onCount
  rw [← Finset.card_filter]
  have hset : (Finset.range (2 * t + 1)).filter (fun j : ℕ => cell 133 t ((j : ℤ) - t) = true) =
      (Finset.range (t - 2)).image (fun s => 2 * s + 3) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, h]
    constructor
    · rintro ⟨hj, hc⟩
      exact ⟨(j - 3) / 2, by omega, by omega⟩
    · rintro ⟨s, hs, rfl⟩
      constructor
      · omega
      · push_cast
        omega
  rw [hset, Finset.card_image_of_injective _ (by intro x y hxy; simp only at hxy; omega),
    Finset.card_range]

open OMA.S_oeis_a267459 in
lemma on_big (t : ℕ) (ht : 2 ≤ t) : ((onCount 133 t : ℕ) : ℚ) =
    (2 * (t : ℚ) - 3) / 2 + (-1 : ℚ) ^ t / 2 := by
  rcases Nat.even_or_odd t with he | ho
  · rw [on_even t ht (Nat.even_iff.mp he), he.neg_one_pow, Nat.cast_sub (by omega)]
    push_cast
    ring
  · have h3 : 3 ≤ t := by
      rcases ho with ⟨k, rfl⟩
      omega
    rw [on_odd t h3 (Nat.odd_iff.mp ho), ho.neg_one_pow, Nat.cast_sub (by omega)]
    push_cast
    ring

open OMA.S_oeis_a267459 in
lemma a_succ (n : ℕ) : (a (n + 1) : ℚ) = (a n : ℚ) + ((onCount 133 (n + 1) : ℕ) : ℚ) := by
  unfold a
  rw [Finset.sum_range_succ]
  push_cast
  ring

open OMA.S_oeis_a267459 in
lemma a_one : (a 1 : ℚ) = 2 := by
  have h : a 1 = 2 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267459 in
lemma a_cl (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (2 * (n : ℚ) ^ 2 - 4 * (n : ℚ) + (-1 : ℚ) ^ n + 11) / 4 := by
  induction n, hn using Nat.le_induction with
  | base => rw [a_one]; norm_num
  | succ n hn2 ih =>
    rw [a_succ, ih, on_big (n + 1) (by omega)]
    push_cast
    ring

open OMA.S_oeis_a267459 in
lemma a_0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267459 in
lemma a_1 : (a 1 : ℚ) = 2 := by
  rw [a_cl 1 (by norm_num)]; norm_num

open OMA.S_oeis_a267459 in
lemma a_2 : (a 2 : ℚ) = 3 := by
  rw [a_cl 2 (by norm_num)]; norm_num

open OMA.S_oeis_a267459 in
lemma a_3 : (a 3 : ℚ) = 4 := by
  rw [a_cl 3 (by norm_num)]; norm_num

open OMA.S_oeis_a267459 in
lemma a_4 : (a 4 : ℚ) = 7 := by
  rw [a_cl 4 (by norm_num)]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267459Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267459 A267459Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267459.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    refine (a_cl n (by omega)).trans ?_
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    rw [a_cl (m + 5) (by omega), a_cl (m + 4) (by omega), a_cl (m + 2) (by omega), a_cl (m + 1) (by omega)]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 1 + PowerSeries.C 2 * PowerSeries.X ^ 3 + PowerSeries.C (-1) * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 4 := by
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
      have f1 := a_cl (n + 4) (by omega)
      have f3 := a_cl (n + 2) (by omega)
      have f4 := a_cl (n + 1) (by omega)
      simp [f0, f1, f3, f4]
      ring
