import OMAStatements.S_oeis_a267051
import Mathlib

namespace A267051Aux

open OMA.S_oeis_a267051 in
lemma rule_iff (l c r : Bool) : ruleOut 92 l c r = true ↔
    ((¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ r = true) ∨ (l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ ¬ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267051 in
lemma s0 (i : ℤ) : cell 92 0 i = true ↔ i = 0 := by
  simp [cell]

open OMA.S_oeis_a267051 in
lemma s1 (i : ℤ) : cell 92 1 i = true ↔ i = 0 ∨ i = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a267051 in
lemma state (t : ℕ) (ht : 1 ≤ t) : ∀ i : ℤ, cell 92 t i = true ↔
    ((0 ≤ i ∧ i ≤ (t : ℤ) - 2 ∧ i % 2 = 0) ∨ i = (t : ℤ) - 1 ∨ i = t) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s1]
    omega
  | succ t ht ih =>
    intro i
    rw [cell, rule_iff]
    simp only [ih]
    push_cast
    omega

open OMA.S_oeis_a267051 in
lemma a_reflect (n : ℕ) : a n = ∑ e ∈ Finset.range (2 * n + 1),
    if cell 92 n ((n : ℤ) - e) = true then (10 : ℤ) ^ e else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < 2 * n + 1 := Finset.mem_range.mp hj
  have e1 : 2 * n + 1 - 1 - j = 2 * n - j := by omega
  have e2 : ((2 * n - j : ℕ) : ℤ) - n = (n : ℤ) - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : 2 * n - (2 * n - j) = j := by omega
  rw [e1, e2, e3]

lemma geo (r m : ℕ) : 99 * ∑ s ∈ Finset.range m, (10 : ℤ) ^ (r + 2 * s) =
    10 ^ (r + 2 * m) - 10 ^ r := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

open OMA.S_oeis_a267051 in
lemma a_val (n : ℕ) (hn : 1 ≤ n) :
    99 * a n = 1089 + 10 ^ (n + 2) - 10 ^ (2 + n % 2) := by
  rw [a_reflect]
  have h := state n hn
  have hsum : (∑ e ∈ Finset.range (2 * n + 1),
      if cell 92 n ((n : ℤ) - e) = true then (10 : ℤ) ^ e else 0) =
      ∑ e ∈ (Finset.range (2 * n + 1)).filter (fun e : ℕ => cell 92 n ((n : ℤ) - e) = true),
        (10 : ℤ) ^ e := (Finset.sum_filter _ _).symm
  have hset : (Finset.range (2 * n + 1)).filter (fun e : ℕ => cell 92 n ((n : ℤ) - e) = true) =
      insert 0 (insert 1 ((Finset.range (n / 2)).image (fun s => 2 + n % 2 + 2 * s))) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image, h]
    constructor
    · rintro ⟨he, hc⟩
      by_cases h0 : e = 0
      · exact Or.inl h0
      · by_cases h1 : e = 1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr ⟨(e - 2 - n % 2) / 2, by omega, by omega⟩)
    · rintro (rfl | rfl | ⟨s, hs, rfl⟩)
      · refine ⟨by omega, ?_⟩
        push_cast
        omega
      · refine ⟨by omega, ?_⟩
        push_cast
        omega
      · refine ⟨by omega, ?_⟩
        push_cast
        omega
  have hn0 : (0 : ℕ) ∉ insert 1 ((Finset.range (n / 2)).image (fun s => 2 + n % 2 + 2 * s)) := by
    rw [Finset.mem_insert, Finset.mem_image]
    rintro (h0 | ⟨s, _, hs⟩)
    · omega
    · omega
  have hn1 : (1 : ℕ) ∉ (Finset.range (n / 2)).image (fun s => 2 + n % 2 + 2 * s) := by
    rw [Finset.mem_image]
    rintro ⟨s, _, hs⟩
    omega
  rw [hsum, hset, Finset.sum_insert hn0, Finset.sum_insert hn1,
    Finset.sum_image (by intro x _ y _ hxy; dsimp only at hxy; omega)]
  have g := geo (2 + n % 2) (n / 2)
  have e : 2 + n % 2 + 2 * (n / 2) = n + 2 := by omega
  rw [e] at g
  simp only [pow_zero, pow_one]
  linarith

open OMA.S_oeis_a267051 in
lemma a_cl (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (539 + 450 * (-1 : ℚ) ^ n + (10 : ℚ) ^ (2 + n)) / 99 := by
  have h := a_val n hn
  have h' : 99 * (a n : ℚ) = 1089 + (10 : ℚ) ^ (n + 2) - (10 : ℚ) ^ (2 + n % 2) := by
    exact_mod_cast h
  rw [eq_div_iff (by norm_num), show 2 + n = n + 2 by ring]
  rcases Nat.even_or_odd n with he | ho
  · rw [Nat.even_iff.mp he] at h'
    rw [he.neg_one_pow]
    norm_num at h'
    linarith
  · rw [Nat.odd_iff.mp ho] at h'
    rw [ho.neg_one_pow]
    norm_num at h'
    linarith

open OMA.S_oeis_a267051 in
lemma a_0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267051 in
lemma a_1 : (a 1 : ℚ) = 11 := by
  rw [a_cl 1 (by norm_num)]; norm_num

open OMA.S_oeis_a267051 in
lemma a_2 : (a 2 : ℚ) = 111 := by
  rw [a_cl 2 (by norm_num)]; norm_num

open OMA.S_oeis_a267051 in
lemma a_3 : (a 3 : ℚ) = 1011 := by
  rw [a_cl 3 (by norm_num)]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267051Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267051 A267051Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267051.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    refine (a_cl n (by omega)).trans ?_
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
    rw [a_cl (m + 4) (by omega), a_cl (m + 3) (by omega), a_cl (m + 2) (by omega), a_cl (m + 1) (by omega)]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-10) * PowerSeries.X ^ 1 + PowerSeries.C (-1) * PowerSeries.X ^ 2 + PowerSeries.C 10 * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + PowerSeries.X - 100 * PowerSeries.X ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 1 * PowerSeries.X ^ 1 + PowerSeries.C (-100) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_0, a_1, a_2, a_3] <;> norm_num
    · have f0 := a_cl (n + 4) (by omega)
      have f1 := a_cl (n + 3) (by omega)
      have f2 := a_cl (n + 2) (by omega)
      have f3 := a_cl (n + 1) (by omega)
      simp [f0, f1, f2, f3]
      ring
