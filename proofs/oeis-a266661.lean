import OMAStatements.S_oeis_a266661
import Mathlib

namespace A266661Aux

open OMA.S_oeis_a266661 in
lemma rule_iff (l c r : Bool) : rule l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ ¬ c = true ∧ r = true) ∨ (¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ r = true) ∨ (l = true ∧ ¬ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a266661 in
lemma s0 (i : ℤ) : row 0 i = true ↔ i = 0 := by
  simp [row]

open OMA.S_oeis_a266661 in
lemma s1 (i : ℤ) : row 1 i = true ↔ ¬(i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, row, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a266661 in
lemma s2 (i : ℤ) : row 2 i = true ↔ i = 1 ∨ i = 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, row, rule_iff]
  simp only [s1]
  omega

open OMA.S_oeis_a266661 in
lemma state (t : ℕ) (ht : 2 ≤ t) : ∀ i : ℤ, row t i = true ↔
    ((t % 2 = 0 ∧ (i = (t : ℤ) - 1 ∨ i = t)) ∨ (t % 2 = 1 ∧ ¬(i = (t : ℤ) - 1 ∨ i = t))) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s2]
    omega
  | succ t ht ih =>
    intro i
    rw [row, rule_iff]
    simp only [ih]
    push_cast
    omega

lemma geom2 (m : ℕ) : ∑ e ∈ Finset.range m, (2 : ℤ) ^ e = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

open OMA.S_oeis_a266661 in
lemma a_even (n : ℕ) (hn : 2 ≤ n) (he : n % 2 = 0) : ((a n : ℕ) : ℤ) = 3 := by
  unfold a
  push_cast
  have h := state n hn
  have val : ∀ e : ℕ, (if row n ((n : ℤ) - e) = true then (2 : ℤ) ^ e else 0) =
      (if e = 0 then (1 : ℤ) else 0) + (if e = 1 then (2 : ℤ) else 0) := by
    intro e
    simp only [h]
    by_cases h0 : e = 0
    · subst h0
      rw [if_pos (by omega)]
      norm_num
    · by_cases h1 : e = 1
      · subst h1
        rw [if_pos (by omega)]
        norm_num
      · rw [if_neg (by omega), if_neg h0, if_neg h1]
        norm_num
  simp only [val, Finset.sum_add_distrib]
  have h1 : 1 < 2 * n + 1 := by omega
  simp [h1]

open OMA.S_oeis_a266661 in
lemma a_odd (n : ℕ) (hn : 2 ≤ n) (ho : n % 2 = 1) : ((a n : ℕ) : ℤ) = 2 ^ (2 * n + 1) - 4 := by
  unfold a
  push_cast
  have h := state n hn
  have val : ∀ e : ℕ, (if row n ((n : ℤ) - e) = true then (2 : ℤ) ^ e else 0) =
      2 ^ e - (if e = 0 then (1 : ℤ) else 0) - (if e = 1 then (2 : ℤ) else 0) := by
    intro e
    simp only [h]
    by_cases h0 : e = 0
    · subst h0
      rw [if_neg (by omega)]
      norm_num
    · by_cases h1 : e = 1
      · subst h1
        rw [if_neg (by omega)]
        norm_num
      · rw [if_pos (by omega), if_neg h0, if_neg h1]
        ring
  simp only [val, Finset.sum_sub_distrib, geom2]
  have h1 : 1 < 2 * n + 1 := by omega
  simp [h1]
  ring

open OMA.S_oeis_a266661 in
lemma a_rec (m : ℕ) : ((a (m + 6) : ℕ) : ℤ) = 17 * a (m + 4) - 16 * a (m + 2) := by
  rcases Nat.even_or_odd m with he | ho
  · have e := Nat.even_iff.mp he
    rw [a_even (m + 6) (by omega) (by omega), a_even (m + 4) (by omega) (by omega),
      a_even (m + 2) (by omega) (by omega)]
    norm_num
  · have e := Nat.odd_iff.mp ho
    rw [a_odd (m + 6) (by omega) (by omega), a_odd (m + 4) (by omega) (by omega),
      a_odd (m + 2) (by omega) (by omega)]
    ring

open OMA.S_oeis_a266661 in
lemma a_0 : ((a 0 : ℕ) : ℤ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a266661 in
lemma a_1 : ((a 1 : ℕ) : ℤ) = 6 := by
  have h : a 1 = 6 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a266661 in
lemma a_2 : ((a 2 : ℕ) : ℤ) = 3 := a_even 2 (by norm_num) (by norm_num)

open OMA.S_oeis_a266661 in
lemma a_3 : ((a 3 : ℕ) : ℤ) = 124 := by
  rw [a_odd 3 (by norm_num) (by norm_num)]; norm_num

open OMA.S_oeis_a266661 in
lemma a_4 : ((a 4 : ℕ) : ℤ) = 3 := a_even 4 (by norm_num) (by norm_num)

open OMA.S_oeis_a266661 in
lemma a_5 : ((a 5 : ℕ) : ℤ) = 2044 := by
  rw [a_odd 5 (by norm_num) (by norm_num)]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A266661Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a266661 A266661Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266661.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.even_or_odd n with he | ho
    · have h := a_even n (by omega) (Nat.even_iff.mp he)
      have h' : ((a n : ℕ) : ℚ) = 3 := by exact_mod_cast h
      rw [h', he.neg_one_pow]
      ring
    · have h := a_odd n (by omega) (Nat.odd_iff.mp ho)
      have h' : ((a n : ℕ) : ℚ) = 2 ^ (2 * n + 1) - 4 := by exact_mod_cast h
      rw [h', ho.neg_one_pow]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega]
    exact a_rec m
  · have hD : ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 + 4 * PowerSeries.X) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-17) * PowerSeries.X ^ 2 + PowerSeries.C 16 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 6 * PowerSeries.X - 14 * PowerSeries.X ^ 2 + 22 * PowerSeries.X ^ 3 - 32 * PowerSeries.X ^ 4 + 32 * PowerSeries.X ^ 5 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 6 * PowerSeries.X ^ 1 + PowerSeries.C (-14) * PowerSeries.X ^ 2 + PowerSeries.C 22 * PowerSeries.X ^ 3 + PowerSeries.C (-32) * PowerSeries.X ^ 4 + PowerSeries.C 32 * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_0, a_1, a_2, a_3] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4] <;> norm_num
    · simp [a_1, a_2, a_3, a_4, a_5] <;> norm_num
    · have h := a_rec n
      simp
      linarith
  · intro n hn ho
    rw [a_odd n (by omega) (Nat.odd_iff.mp ho), pow_succ, pow_mul]
    norm_num
    ring
  · intro n hn he
    have h := a_even n (by omega) (Nat.even_iff.mp he)
    exact_mod_cast h
