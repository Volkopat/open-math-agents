import OMAStatements.S_oeis_a266615
import Mathlib

namespace A266615Aux

/-- the rows have period 4 in `t` and are anchored at the right end `i = t` of the row -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide ((t % 4 = 0 ∧ i = t) ∨ (t % 4 = 1 ∧ ¬((t : ℤ) - 2 ≤ i ∧ i ≤ t)) ∨
    (t % 4 = 2 ∧ (i = (t : ℤ) - 2 ∨ i = t)) ∨ (t % 4 = 3 ∧ (i = (t : ℤ) - 2 ∨ i < (t : ℤ) - 4 ∨ (t : ℤ) < i)))

set_option maxHeartbeats 4000000 in
lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 41 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a266615 in
lemma cellP (t : ℕ) : ∀ i, cell 41 t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show ruleOut 41 (cell 41 k (i - 1)) (cell 41 k i) (cell 41 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

open OMA.S_oeis_a266615 in
lemma on_step (t : ℕ) : onCount 41 (t + 4) = onCount 41 t + (if t % 2 = 0 then 0 else 8) := by
  unfold onCount
  rw [show 2 * (t + 4) + 1 = 8 + (2 * t + 1) by ring, Finset.sum_range_add]
  have hmain : ∀ j ∈ Finset.range (2 * t + 1),
      (if cell 41 (t + 4) (((8 + j : ℕ) : ℤ) - ((t + 4 : ℕ) : ℤ)) then 1 else 0) =
      (if cell 41 t ((j : ℤ) - (t : ℤ)) then 1 else 0) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [cellP, cellP]
    have e : p (t + 4) (((8 + j : ℕ) : ℤ) - ((t + 4 : ℕ) : ℤ)) = p t ((j : ℤ) - (t : ℤ)) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> omega
    rw [e]
  have hhead : ∀ j ∈ Finset.range 8,
      (if cell 41 (t + 4) ((j : ℤ) - ((t + 4 : ℕ) : ℤ)) then 1 else 0) =
      (if t % 2 = 0 then 0 else 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [cellP]
    have e : p (t + 4) ((j : ℤ) - ((t + 4 : ℕ) : ℤ)) = decide (t % 2 = 1) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> omega
    rw [e]
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]
  rw [Finset.sum_congr rfl hmain, Finset.sum_congr rfl hhead]
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h] <;> omega

open OMA.S_oeis_a266615 in
lemma stepE (t : ℕ) (h : t % 2 = 0) : (onCount 41 (t + 4) : ℚ) = (onCount 41 t : ℚ) := by
  rw [on_step, if_pos h]
  norm_num

open OMA.S_oeis_a266615 in
lemma stepO (t : ℕ) (h : t % 2 = 1) : (onCount 41 (t + 4) : ℚ) = (onCount 41 t : ℚ) + 8 := by
  rw [on_step, if_neg (by omega)]
  norm_num

open OMA.S_oeis_a266615 in
lemma on0 : onCount 41 0 = 1 := by decide

open OMA.S_oeis_a266615 in
lemma on1 : onCount 41 1 = 0 := by decide

open OMA.S_oeis_a266615 in
lemma on2 : onCount 41 2 = 2 := by decide

open OMA.S_oeis_a266615 in
lemma on3 : onCount 41 3 = 3 := by decide

open OMA.S_oeis_a266615 in
lemma on4 : onCount 41 4 = 1 := by
  rw [on_step 0, on0]
  norm_num

open OMA.S_oeis_a266615 in
lemma on5 : onCount 41 5 = 8 := by
  rw [on_step 1, on1]
  norm_num

open OMA.S_oeis_a266615 in
lemma on6 : onCount 41 6 = 2 := by
  rw [on_step 2, on2]
  norm_num

open OMA.S_oeis_a266615 in
lemma aS (n : ℕ) : (a (n + 1) : ℚ) = a n + (onCount 41 (n + 1) : ℚ) := by
  unfold a
  rw [Finset.sum_range_succ]
  push_cast
  ring

open OMA.S_oeis_a266615 in
lemma e0 : (a 0 : ℚ) = 1 := by
  unfold a
  rw [Finset.sum_range_one]
  push_cast
  rw [on0]
  norm_num

open OMA.S_oeis_a266615 in
lemma e1 : (a 1 : ℚ) = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, aS, e0, on1]
  norm_num

open OMA.S_oeis_a266615 in
lemma e2 : (a 2 : ℚ) = 3 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, aS, e1, on2]
  norm_num

open OMA.S_oeis_a266615 in
lemma e3 : (a 3 : ℚ) = 6 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, aS, e2, on3]
  norm_num

open OMA.S_oeis_a266615 in
lemma e4 : (a 4 : ℚ) = 7 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, aS, e3, on4]
  norm_num

open OMA.S_oeis_a266615 in
lemma e5 : (a 5 : ℚ) = 15 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, aS, e4, on5]
  norm_num

open OMA.S_oeis_a266615 in
lemma e6 : (a 6 : ℚ) = 17 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, aS, e5, on6]
  norm_num

open OMA.S_oeis_a266615 in
lemma recQ (m : ℕ) : (a (m + 7) : ℚ) = a (m + 6) + a (m + 5) - a (m + 4) + a (m + 3)
    - a (m + 2) - a (m + 1) + a m := by
  have s7 := aS (m + 6)
  have s5 := aS (m + 4)
  have s3 := aS (m + 2)
  have s1 := aS m
  rw [show m + 6 + 1 = m + 7 by ring] at s7
  rw [show m + 4 + 1 = m + 5 by ring] at s5
  rw [show m + 2 + 1 = m + 3 by ring] at s3
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have d1 := stepO (m + 3) (by omega)
    have d2 := stepO (m + 1) (by omega)
    rw [show m + 3 + 4 = m + 7 by ring] at d1
    rw [show m + 1 + 4 = m + 5 by ring] at d2
    push_cast at s7 s5 s3 s1
    linarith
  · have d1 := stepE (m + 3) (by omega)
    have d2 := stepE (m + 1) (by omega)
    rw [show m + 3 + 4 = m + 7 by ring] at d1
    rw [show m + 1 + 4 = m + 5 by ring] at d2
    push_cast at s7 s5 s3 s1
    linarith

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A266615Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a266615 A266615Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a266615.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
    linarith [recQ m]
  · have hD : ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 + PowerSeries.C (-1) * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 3 + PowerSeries.C (-1) * PowerSeries.X ^ 4 + PowerSeries.C 1 * PowerSeries.X ^ 5 + PowerSeries.C 1 * PowerSeries.X ^ 6 + PowerSeries.C (-1) * PowerSeries.X ^ 7 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + 5 * X ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 1 * PowerSeries.X ^ 2 + PowerSeries.C 3 * PowerSeries.X ^ 3 + PowerSeries.C (-2) * PowerSeries.X ^ 4 + PowerSeries.C 5 * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · norm_num [e0, e1, e2, e3]
    · norm_num [e0, e1, e2, e3, e4]
    · norm_num [e0, e1, e2, e3, e4, e5]
    · norm_num [e0, e1, e2, e3, e4, e5, e6]
    · have hr := recQ (n)
      simp [show n + 7 - 1 = n + 6 by omega, show n + 7 - 2 = n + 5 by omega, show n + 7 - 3 = n + 4 by omega, show n + 7 - 4 = n + 3 by omega, show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega, show n + 7 - 7 = n by omega]
      linarith
