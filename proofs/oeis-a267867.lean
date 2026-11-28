import OMAStatements.S_oeis_a267867
import Mathlib

namespace A267867Aux

open OMA.S_oeis_a267867 in
lemma rule_iffA (l c r : Bool) : rule 231 l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ ¬ c = true ∧ r = true) ∨ (¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ ¬ c = true ∧ r = true) ∨ (l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267867 in
lemma rule_iffB (l c r : Bool) : rule 229 l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ ¬ c = true ∧ r = true) ∨ (l = true ∧ c = true ∧ ¬ r = true) ∨ (l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267867 in
lemma sA0 (i : ℤ) : row 231 0 i = true ↔ i = 0 := by
  simp [row]

open OMA.S_oeis_a267867 in
lemma sA1 (i : ℤ) : row 231 1 i = true ↔ ¬(i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, row, rule_iffA]
  simp only [sA0]
  omega

open OMA.S_oeis_a267867 in
lemma sB0 (i : ℤ) : row 229 0 i = true ↔ i = 0 := by
  simp [row]

open OMA.S_oeis_a267867 in
lemma sB1 (i : ℤ) : row 229 1 i = true ↔ ¬(i = -1 ∨ i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, row, rule_iffB]
  simp only [sB0]
  omega

open OMA.S_oeis_a267867 in
lemma sB2 (i : ℤ) : row 229 2 i = true ↔ ¬(i = 2) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, row, rule_iffB]
  simp only [sB1]
  omega

open OMA.S_oeis_a267867 in
lemma sgenA (t : ℕ) (ht : 1 ≤ t) : ∀ i : ℤ, row 231 t i = true ↔ ¬(i = t) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [sA1]
    norm_num
  | succ t ht ih =>
    intro i
    rw [row, rule_iffA]
    simp only [ih]
    push_cast
    omega

open OMA.S_oeis_a267867 in
lemma sgenB (t : ℕ) (ht : 2 ≤ t) : ∀ i : ℤ, row 229 t i = true ↔ ¬(i = t) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [sB2]
    norm_num
  | succ t ht ih =>
    intro i
    rw [row, rule_iffB]
    simp only [ih]
    push_cast
    omega

lemma geom10 (m : ℕ) : 9 * ∑ e ∈ Finset.range m, (10 : ℤ) ^ e = 10 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

open OMA.S_oeis_a267867 in
lemma dig (R n : ℕ) (h : ∀ i : ℤ, row R n i = true ↔ ¬(i = n)) :
    9 * ((digits R n : ℕ) : ℤ) = 10 ^ (2 * n + 1) - 10 := by
  unfold digits
  push_cast
  have val : ∀ e : ℕ, (if row R n ((n : ℤ) - e) = true then (10 : ℤ) ^ e else 0) =
      10 ^ e - (if e = 0 then (1 : ℤ) else 0) := by
    intro e
    simp only [h]
    by_cases h0 : e = 0
    · subst h0
      norm_num
    · have hc : ¬((n : ℤ) - e = n) := by omega
      rw [if_pos hc, if_neg h0]
      ring
  simp only [val, Finset.sum_sub_distrib, mul_sub, geom10]
  simp
  ring

open OMA.S_oeis_a267867 in
lemma a_cl (n : ℕ) (hn : 1 ≤ n) : 9 * ((a n : ℕ) : ℤ) = 10 ^ (2 * n + 1) - 10 :=
  dig 231 n (sgenA n hn)

open OMA.S_oeis_a267867 in
lemma b_cl (n : ℕ) (hn : 2 ≤ n) : 9 * ((A267850 n : ℕ) : ℤ) = 10 ^ (2 * n + 1) - 10 :=
  dig 229 n (sgenB n hn)

open OMA.S_oeis_a267867 in
lemma a_0 : ((a 0 : ℕ) : ℤ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267867 in
lemma a_1 : ((a 1 : ℕ) : ℤ) = 110 := by
  have h := a_cl 1 (by norm_num)
  norm_num at h
  omega

open OMA.S_oeis_a267867 in
lemma a_2 : ((a 2 : ℕ) : ℤ) = 11110 := by
  have h := a_cl 2 (by norm_num)
  norm_num at h
  omega

open OMA.S_oeis_a267867 in
lemma a_rec (m : ℕ) : ((a (m + 3) : ℕ) : ℤ) = 101 * a (m + 2) - 100 * a (m + 1) := by
  have h3 := a_cl (m + 3) (by omega)
  have h2 := a_cl (m + 2) (by omega)
  have h1 := a_cl (m + 1) (by omega)
  have e3 : (10 : ℤ) ^ (2 * (m + 3) + 1) = 10000 * 10 ^ (2 * (m + 1) + 1) := by ring
  have e2 : (10 : ℤ) ^ (2 * (m + 2) + 1) = 100 * 10 ^ (2 * (m + 1) + 1) := by ring
  rw [e3] at h3
  rw [e2] at h2
  linarith

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267867Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267867 A267867Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267867.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    refine ⟨a_rec m, ?_⟩
    rw [← a_rec m]
    have h3 := a_cl (m + 3) (by omega)
    have h4 := b_cl (m + 3) (by omega)
    linarith
  · have hD : ((1 - PowerSeries.X) * (1 - 100 * PowerSeries.X) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-101) * PowerSeries.X ^ 1 + PowerSeries.C 100 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 9 * PowerSeries.X + 100 * PowerSeries.X ^ 2 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 9 * PowerSeries.X ^ 1 + PowerSeries.C 100 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · have h := a_rec n
      simp
      linarith
