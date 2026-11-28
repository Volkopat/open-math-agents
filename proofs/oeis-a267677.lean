import OMAStatements.S_oeis_a267677
import Mathlib

namespace A267677Aux

open OMA.S_oeis_a267677 in
lemma rule_iff (l c r : Bool) : ruleOut 197 l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267677 in
lemma s0 (i : ℤ) : cell 197 0 i = true ↔ i = 0 := by
  simp [cell]

open OMA.S_oeis_a267677 in
lemma s1 (i : ℤ) : cell 197 1 i = true ↔ ¬(i = -1 ∨ i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a267677 in
lemma s2 (i : ℤ) : cell 197 2 i = true ↔ ¬(i = -1 ∨ i = 1 ∨ i = 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell, rule_iff]
  simp only [s1]
  omega

open OMA.S_oeis_a267677 in
lemma state (t : ℕ) (ht : 2 ≤ t) : ∀ i : ℤ, cell 197 t i = true ↔
    ¬(i = -1 ∨ (1 ≤ i ∧ i ≤ (t : ℤ) ∧
      ((i % 2 = 1 ∧ ((t % 2 = 0 ∧ i ≤ (t : ℤ) - 1) ∨ (t % 2 = 1 ∧ i ≤ (t : ℤ) - 2))) ∨
       (t % 2 = 0 ∧ (t : ℤ) ≤ i) ∨ (t % 2 = 1 ∧ (t : ℤ) - 1 ≤ i)))) := by
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

open OMA.S_oeis_a267677 in
lemma a_reflect (n : ℕ) : a n = ∑ e ∈ Finset.range (2 * n + 1),
    if cell 197 n ((n : ℤ) - e) = true then (10 : ℤ) ^ e else 0 := by
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

lemma geo9 (m : ℕ) : 9 * ∑ e ∈ Finset.range m, (10 : ℤ) ^ e = 10 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

open OMA.S_oeis_a267677 in
lemma a_even (n : ℕ) (hn : 2 ≤ n) (hpar : n % 2 = 0) :
    99 * a n = 11 * 10 ^ (2 * n + 1) - 100 * 10 ^ (n + 1) - 100 := by
  rw [a_reflect]
  have h := state n hn
  have hsplit : (∑ e ∈ Finset.range (2 * n + 1),
      if cell 197 n ((n : ℤ) - e) = true then (10 : ℤ) ^ e else 0) =
      ∑ e ∈ Finset.range (2 * n + 1), (10 : ℤ) ^ e -
      ∑ e ∈ (Finset.range (2 * n + 1)).filter (fun e : ℕ => ¬ cell 197 n ((n : ℤ) - e) = true),
        (10 : ℤ) ^ e := by
    rw [← Finset.sum_filter, eq_sub_iff_add_eq]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hset : (Finset.range (2 * n + 1)).filter
      (fun e : ℕ => ¬ cell 197 n ((n : ℤ) - e) = true) =
      insert (n + 1) (insert 0 ((Finset.range (n / 2)).image (fun s => 1 + 2 * s))) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image, h, not_not]
    constructor
    · rintro ⟨he, hc⟩
      by_cases h1 : e = n + 1
      · exact Or.inl h1
      · by_cases h0 : e = 0
        · exact Or.inr (Or.inl h0)
        · exact Or.inr (Or.inr ⟨(e - 1) / 2, by omega, by omega⟩)
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
  have hn1 : (n + 1) ∉ insert 0 ((Finset.range (n / 2)).image (fun s => 1 + 2 * s)) := by
    rw [Finset.mem_insert, Finset.mem_image]
    rintro (h0 | ⟨s, hs, hs2⟩)
    · omega
    · have hs' := Finset.mem_range.mp hs
      omega
  have hn0 : (0 : ℕ) ∉ (Finset.range (n / 2)).image (fun s => 1 + 2 * s) := by
    rw [Finset.mem_image]
    rintro ⟨s, _, hs⟩
    omega
  rw [hsplit, hset, Finset.sum_insert hn1, Finset.sum_insert hn0,
    Finset.sum_image (by intro x _ y _ hxy; dsimp only at hxy; omega)]
  have g := geo 1 (n / 2)
  have g9 := geo9 (2 * n + 1)
  have e : 1 + 2 * (n / 2) = n + 1 := by omega
  rw [e] at g
  simp only [pow_zero, pow_one] at g ⊢
  linarith

open OMA.S_oeis_a267677 in
lemma a_odd (n : ℕ) (hn : 2 ≤ n) (hpar : n % 2 = 1) :
    99 * a n = 11 * 10 ^ (2 * n + 1) - 100 * 10 ^ (n + 1) - 1000 := by
  rw [a_reflect]
  have h := state n hn
  have hsplit : (∑ e ∈ Finset.range (2 * n + 1),
      if cell 197 n ((n : ℤ) - e) = true then (10 : ℤ) ^ e else 0) =
      ∑ e ∈ Finset.range (2 * n + 1), (10 : ℤ) ^ e -
      ∑ e ∈ (Finset.range (2 * n + 1)).filter (fun e : ℕ => ¬ cell 197 n ((n : ℤ) - e) = true),
        (10 : ℤ) ^ e := by
    rw [← Finset.sum_filter, eq_sub_iff_add_eq]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hset : (Finset.range (2 * n + 1)).filter
      (fun e : ℕ => ¬ cell 197 n ((n : ℤ) - e) = true) =
      insert (n + 1) (insert 0 (insert 1 ((Finset.range (n / 2)).image (fun s => 2 + 2 * s)))) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image, h, not_not]
    constructor
    · rintro ⟨he, hc⟩
      by_cases h1 : e = n + 1
      · exact Or.inl h1
      · by_cases h0 : e = 0
        · exact Or.inr (Or.inl h0)
        · by_cases h2 : e = 1
          · exact Or.inr (Or.inr (Or.inl h2))
          · exact Or.inr (Or.inr (Or.inr ⟨(e - 2) / 2, by omega, by omega⟩))
    · rintro (rfl | rfl | rfl | ⟨s, hs, rfl⟩)
      · refine ⟨by omega, ?_⟩
        push_cast
        omega
      · refine ⟨by omega, ?_⟩
        push_cast
        omega
      · refine ⟨by omega, ?_⟩
        push_cast
        omega
      · refine ⟨by omega, ?_⟩
        push_cast
        omega
  have hn1 : (n + 1) ∉ insert 0 (insert 1 ((Finset.range (n / 2)).image (fun s => 2 + 2 * s))) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_image]
    rintro (h0 | h0 | ⟨s, hs, hs2⟩)
    · omega
    · omega
    · have hs' := Finset.mem_range.mp hs
      omega
  have hn0 : (0 : ℕ) ∉ insert 1 ((Finset.range (n / 2)).image (fun s => 2 + 2 * s)) := by
    rw [Finset.mem_insert, Finset.mem_image]
    rintro (h0 | ⟨s, _, hs⟩)
    · omega
    · omega
  have hn2 : (1 : ℕ) ∉ (Finset.range (n / 2)).image (fun s => 2 + 2 * s) := by
    rw [Finset.mem_image]
    rintro ⟨s, _, hs⟩
    omega
  rw [hsplit, hset, Finset.sum_insert hn1, Finset.sum_insert hn0, Finset.sum_insert hn2,
    Finset.sum_image (by intro x _ y _ hxy; dsimp only at hxy; omega)]
  have g := geo 2 (n / 2)
  have g9 := geo9 (2 * n + 1)
  have e : 2 + 2 * (n / 2) = n + 1 := by omega
  rw [e] at g
  simp only [pow_zero, pow_one] at g ⊢
  linarith

open OMA.S_oeis_a267677 in
lemma a_cl (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = (110 * (100 : ℚ) ^ n - 1000 * (10 : ℚ) ^ n - 550 + 450 * (-1 : ℚ) ^ n) / 99 := by
  have e1 : (10 : ℚ) ^ (2 * n + 1) = 10 * (100 : ℚ) ^ n := by
    have h100 : (100 : ℚ) = 10 ^ 2 := by norm_num
    rw [h100, ← pow_mul]
    ring
  have e2 : (10 : ℚ) ^ (n + 1) = 10 * (10 : ℚ) ^ n := by ring
  rw [eq_div_iff (by norm_num)]
  rcases Nat.even_or_odd n with he | ho
  · have h := a_even n hn (Nat.even_iff.mp he)
    have h' : 99 * (a n : ℚ) = 11 * (10 : ℚ) ^ (2 * n + 1) - 100 * (10 : ℚ) ^ (n + 1) - 100 := by
      exact_mod_cast h
    rw [e1, e2] at h'
    rw [he.neg_one_pow]
    linarith
  · have h := a_odd n hn (Nat.odd_iff.mp ho)
    have h' : 99 * (a n : ℚ) = 11 * (10 : ℚ) ^ (2 * n + 1) - 100 * (10 : ℚ) ^ (n + 1) - 1000 := by
      exact_mod_cast h
    rw [e1, e2] at h'
    rw [ho.neg_one_pow]
    linarith

open OMA.S_oeis_a267677 in
lemma a_0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267677 in
lemma a_1 : (a 1 : ℚ) = 10 := by
  have h : a 1 = 10 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267677 in
lemma a_2 : (a 2 : ℚ) = 10100 := by
  rw [a_cl 2 (by norm_num)]; norm_num

open OMA.S_oeis_a267677 in
lemma a_3 : (a 3 : ℚ) = 1101000 := by
  rw [a_cl 3 (by norm_num)]; norm_num

open OMA.S_oeis_a267677 in
lemma a_4 : (a 4 : ℚ) = 111010100 := by
  rw [a_cl 4 (by norm_num)]; norm_num

open OMA.S_oeis_a267677 in
lemma a_5 : (a 5 : ℚ) = 11110101000 := by
  rw [a_cl 5 (by norm_num)]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267677Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267677 A267677Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267677.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega]
    rw [a_cl (m + 6) (by omega), a_cl (m + 5) (by omega), a_cl (m + 4) (by omega), a_cl (m + 3) (by omega), a_cl (m + 2) (by omega)]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 10 * PowerSeries.X) * (1 - 100 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-110) * PowerSeries.X ^ 1 + PowerSeries.C 999 * PowerSeries.X ^ 2 + PowerSeries.C 110 * PowerSeries.X ^ 3 + PowerSeries.C (-1000) * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - 100 * PowerSeries.X + 9999 * PowerSeries.X ^ 2 + 100 * PowerSeries.X ^ 3 - 9900 * PowerSeries.X ^ 4 - 10000 * PowerSeries.X ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-100) * PowerSeries.X ^ 1 + PowerSeries.C 9999 * PowerSeries.X ^ 2 + PowerSeries.C 100 * PowerSeries.X ^ 3 + PowerSeries.C (-9900) * PowerSeries.X ^ 4 + PowerSeries.C (-10000) * PowerSeries.X ^ 5 := by
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
    · have f0 := a_cl (n + 6) (by omega)
      have f1 := a_cl (n + 5) (by omega)
      have f2 := a_cl (n + 4) (by omega)
      have f3 := a_cl (n + 3) (by omega)
      have f4 := a_cl (n + 2) (by omega)
      simp [f0, f1, f2, f3, f4]
      ring
