import OMAStatements.S_oeis_a267851
import Mathlib

namespace A267851Aux

open OMA.S_oeis_a267851 in
lemma rule_iff (l c r : Bool) : rule l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ ¬ c = true ∧ r = true) ∨ (l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267851 in
lemma s0 (i : ℤ) : row 0 i = true ↔ i = 0 := by
  simp [row]

open OMA.S_oeis_a267851 in
lemma s1 (i : ℤ) : row 1 i = true ↔ ¬(i = -1 ∨ i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, row, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a267851 in
lemma s2 (i : ℤ) : row 2 i = true ↔ ¬(i = 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, row, rule_iff]
  simp only [s1]
  omega

open OMA.S_oeis_a267851 in
lemma sgen (t : ℕ) (ht : 2 ≤ t) : ∀ i : ℤ, row t i = true ↔ ¬(i = t) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s2]
    norm_num
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

open OMA.S_oeis_a267851 in
lemma a_cl (n : ℕ) (hn : 2 ≤ n) : ((a n : ℕ) : ℤ) = 2 ^ (2 * n + 1) - 2 := by
  unfold a
  push_cast
  have h := sgen n hn
  have val : ∀ e : ℕ, (if row n ((n : ℤ) - e) = true then (2 : ℤ) ^ e else 0) =
      2 ^ e - (if e = 0 then (1 : ℤ) else 0) := by
    intro e
    simp only [h]
    by_cases h0 : e = 0
    · subst h0
      norm_num
    · have hc : ¬((n : ℤ) - e = n) := by omega
      rw [if_pos hc, if_neg h0]
      ring
  simp only [val, Finset.sum_sub_distrib, geom2]
  simp
  ring

open OMA.S_oeis_a267851 in
lemma a_0 : ((a 0 : ℕ) : ℤ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267851 in
lemma a_1 : ((a 1 : ℕ) : ℤ) = 2 := by
  have h : a 1 = 2 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267851 in
lemma a_2 : ((a 2 : ℕ) : ℤ) = 30 := by
  rw [a_cl 2 (by norm_num)]; norm_num

open OMA.S_oeis_a267851 in
lemma a_3 : ((a 3 : ℕ) : ℤ) = 126 := by
  rw [a_cl 3 (by norm_num)]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267851Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267851 A267851Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267851.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    rw [a_cl (m + 4) (by omega), a_cl (m + 3) (by omega), a_cl (m + 2) (by omega)]
    ring
  · have hD : ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-5) * PowerSeries.X ^ 1 + PowerSeries.C 4 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - 3 * PowerSeries.X + 24 * PowerSeries.X ^ 2 - 16 * PowerSeries.X ^ 3 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 1 + PowerSeries.C 24 * PowerSeries.X ^ 2 + PowerSeries.C (-16) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
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
    have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have e : 2 ^ (2 * n + 1) = 2 * 4 ^ n := by rw [pow_succ, pow_mul]; ring
    refine ⟨?_, ?_⟩
    · have h := a_cl n (by omega)
      zify [h1]
      rw [h, pow_succ, pow_mul]
      norm_num
      ring
    · unfold A002446
      rw [e]
      omega
