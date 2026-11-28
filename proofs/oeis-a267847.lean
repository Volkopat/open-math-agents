import OMAStatements.S_oeis_a267847
import Mathlib

namespace A267847Aux

open OMA.S_oeis_a267847 in
lemma rule_iff (l c r : Bool) : ruleOut 227 l c r = true ↔
    ((¬ l = true ∧ ¬ c = true) ∨ (l = true ∧ (c = true ∨ r = true))) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267847 in
lemma s0 (i : ℤ) : cell 227 0 i = true ↔ i = 0 := by
  simp [cell]

open OMA.S_oeis_a267847 in
lemma s1 (i : ℤ) : cell 227 1 i = true ↔ ¬(i = 0 ∨ i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a267847 in
lemma s2 (i : ℤ) : cell 227 2 i = true ↔ ¬(i = 0 ∨ i = 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell, rule_iff]
  simp only [s1]
  omega

open OMA.S_oeis_a267847 in
lemma sgen (t : ℕ) (ht : 2 ≤ t) : ∀ i : ℤ, cell 227 t i = true ↔ ¬(i = (t : ℤ) - 2 ∨ i = t) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s2]
    norm_num
  | succ t ht ih =>
    intro i
    rw [cell, rule_iff]
    simp only [ih]
    push_cast
    omega

lemma geom2 (m : ℕ) : ∑ e ∈ Finset.range m, (2 : ℤ) ^ e = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

open OMA.S_oeis_a267847 in
lemma a_reflect (n : ℕ) : a n = ∑ e ∈ Finset.range (2 * n + 1),
    if cell 227 n ((n : ℤ) - e) = true then (2 : ℤ) ^ e else 0 := by
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

open OMA.S_oeis_a267847 in
lemma a_int (n : ℕ) (hn : 2 ≤ n) : a n = 2 ^ (2 * n + 1) - 6 := by
  rw [a_reflect]
  have h := sgen n hn
  have val : ∀ e : ℕ, (if cell 227 n ((n : ℤ) - e) = true then (2 : ℤ) ^ e else 0) =
      2 ^ e - (if e = 2 then (4 : ℤ) else 0) - (if e = 0 then (1 : ℤ) else 0) := by
    intro e
    simp only [h]
    by_cases h2 : e = 2
    · subst h2
      norm_num
    · by_cases h0 : e = 0
      · subst h0
        norm_num
      · have hc : ¬(((n : ℤ) - e = (n : ℤ) - 2) ∨ ((n : ℤ) - e = n)) := by omega
        rw [if_pos hc, if_neg h2, if_neg h0]
        ring
  simp only [val, Finset.sum_sub_distrib, geom2]
  have h2 : 2 < 2 * n + 1 := by omega
  simp [h2]
  ring

open OMA.S_oeis_a267847 in
lemma a_cl (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = 2 * ((4 : ℚ) ^ n - 3) := by
  rw [a_int n hn]
  push_cast
  rw [pow_succ, pow_mul]
  norm_num
  ring

open OMA.S_oeis_a267847 in
lemma a_0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267847 in
lemma a_1 : (a 1 : ℚ) = 4 := by
  have h : a 1 = 4 := by decide
  rw [h]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267847Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267847 A267847Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267847.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    rw [a_cl (m + 4) (by omega), a_cl (m + 3) (by omega), a_cl (m + 2) (by omega)]
    ring
  · have hD : ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-5) * PowerSeries.X ^ 1 +
        PowerSeries.C 4 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - PowerSeries.X + 10 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 +
        PowerSeries.C 10 * PowerSeries.X ^ 2 + PowerSeries.C 8 * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have a_2 := a_cl 2 (by norm_num)
    have a_3 := a_cl 3 (by norm_num)
    norm_num at a_2 a_3
    rcases n with _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_1, a_2, a_3] <;> norm_num
    · have f0 := a_cl (n + 4) (by omega)
      have f1 := a_cl (n + 3) (by omega)
      have f2 := a_cl (n + 2) (by omega)
      simp [f0, f1, f2]
      ring
  · intro n hn
    exact a_cl n hn
