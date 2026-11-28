import OMAStatements.S_oeis_a267688
import Mathlib

namespace A267688Aux

/-- for `t ≥ 1` the cells `i ≤ 0` and `i > t` are ON, and for `1 ≤ i ≤ t` a cell is ON iff `i` is even and `i < t` -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide ((t = 0 ∧ i = 0) ∨ (1 ≤ t ∧ (i ≤ 0 ∨ (t : ℤ) < i ∨ (i % 2 = 0 ∧ i < t))))

set_option maxHeartbeats 4000000 in
lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 199 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a267688 in
lemma cellP (t : ℕ) : ∀ i, cell 199 t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show ruleOut 199 (cell 199 k (i - 1)) (cell 199 k i) (cell 199 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

/-- the digit contributed by cell `j - n` of row `n` -/
def w (n j : ℕ) : ℤ :=
  if OMA.S_oeis_a267688.cell 199 n ((j : ℤ) - (n : ℤ)) then (10 : ℤ) ^ (2 * n - j) else 0

open OMA.S_oeis_a267688 in
lemma a_w (n : ℕ) : a n = ∑ j ∈ Finset.range (2 * n + 1), w n j := rfl

lemma w_on (n j : ℕ) (h : p n ((j : ℤ) - (n : ℤ)) = true) : w n j = 10 ^ (2 * n - j) := by
  unfold w
  rw [cellP, h]
  rfl

lemma w_off (n j : ℕ) (h : p n ((j : ℤ) - (n : ℤ)) = false) : w n j = 0 := by
  unfold w
  rw [cellP, h]
  rfl

lemma head2 (n : ℕ) (hn : 1 ≤ n) :
    ∑ x ∈ Finset.range 2, w (n + 2) x = 11 * 10 ^ (2 * n + 3) := by
  rw [Finset.sum_range_succ, Finset.sum_range_one, w_on (n + 2) 0 (by unfold p; rw [decide_eq_true_eq]; omega),
    w_on (n + 2) 1 (by unfold p; rw [decide_eq_true_eq]; omega), show 2 * (n + 2) - 0 = (2 * n + 3) + 1 by omega,
    show 2 * (n + 2) - 1 = 2 * n + 3 by omega, pow_succ]
  ring

lemma main_even (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 0) :
    ∑ x ∈ Finset.range (2 * n + 1), w (n + 2) (2 + x) =
      100 * ∑ j ∈ Finset.range (2 * n + 1), w n j + 100 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  have hm : ∀ j ∈ Finset.range (2 * n), w (n + 2) (2 + j) = 100 * w n j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    unfold w
    rw [cellP, cellP]
    have e : p (n + 2) (((2 + j : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
      unfold p
      apply decide_eq_decide.mpr
      constructor <;> intro h' <;> omega
    rw [e, show 2 * (n + 2) - (2 + j) = (2 * n - j) + 2 by omega, pow_add]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hm, w_off n (2 * n) (by unfold p; rw [decide_eq_false_iff_not]; omega), w_on (n + 2) (2 + 2 * n) (by unfold p; rw [decide_eq_true_eq]; omega)]
  rw [show 2 * (n + 2) - (2 + 2 * n) = 2 by omega]
  norm_num

lemma tail_even (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 0) :
    ∑ x ∈ Finset.range 2, w (n + 2) (2 + (2 * n + 1 + x)) = 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one, w_off (n + 2) (2 + (2 * n + 1 + 0)) (by unfold p; rw [decide_eq_false_iff_not]; omega),
    w_off (n + 2) (2 + (2 * n + 1 + 1)) (by unfold p; rw [decide_eq_false_iff_not]; omega)]
  
  norm_num

open OMA.S_oeis_a267688 in
lemma a_step_even (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 0) :
    a (n + 2) = 100 * a n + 11 * 10 ^ (2 * n + 3) + 100 := by
  rw [a_w, a_w, show 2 * (n + 2) + 1 = 2 + ((2 * n + 1) + 2) by ring, Finset.sum_range_add,
    Finset.sum_range_add, head2 n hn, main_even n hn h, tail_even n hn h]
  ring

lemma main_odd (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 1) :
    ∑ x ∈ Finset.range (2 * n + 1), w (n + 2) (2 + x) =
      100 * ∑ j ∈ Finset.range (2 * n + 1), w n j + 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  have hm : ∀ j ∈ Finset.range (2 * n), w (n + 2) (2 + j) = 100 * w n j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    unfold w
    rw [cellP, cellP]
    have e : p (n + 2) (((2 + j : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
      unfold p
      apply decide_eq_decide.mpr
      constructor <;> intro h' <;> omega
    rw [e, show 2 * (n + 2) - (2 + j) = (2 * n - j) + 2 by omega, pow_add]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hm, w_off n (2 * n) (by unfold p; rw [decide_eq_false_iff_not]; omega), w_off (n + 2) (2 + 2 * n) (by unfold p; rw [decide_eq_false_iff_not]; omega)]
  
  norm_num

lemma tail_odd (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 1) :
    ∑ x ∈ Finset.range 2, w (n + 2) (2 + (2 * n + 1 + x)) = 10 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one, w_on (n + 2) (2 + (2 * n + 1 + 0)) (by unfold p; rw [decide_eq_true_eq]; omega),
    w_off (n + 2) (2 + (2 * n + 1 + 1)) (by unfold p; rw [decide_eq_false_iff_not]; omega)]
  rw [show 2 * (n + 2) - (2 + (2 * n + 1 + 0)) = 1 by omega]
  norm_num

open OMA.S_oeis_a267688 in
lemma a_step_odd (n : ℕ) (hn : 1 ≤ n) (h : n % 2 = 1) :
    a (n + 2) = 100 * a n + 11 * 10 ^ (2 * n + 3) + 10 := by
  rw [a_w, a_w, show 2 * (n + 2) + 1 = 2 + ((2 * n + 1) + 2) by ring, Finset.sum_range_add,
    Finset.sum_range_add, head2 n hn, main_odd n hn h, tail_odd n hn h]
  ring

open OMA.S_oeis_a267688 in
lemma e0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267688 in
lemma e1 : (a 1 : ℚ) = 110 := by
  have h : a 1 = 110 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267688 in
lemma e2 : (a 2 : ℚ) = 11100 := by
  have h : a 2 = 11100 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267688 in
lemma aQ2 (m : ℕ) : ((a (2 * m + 1) : ℚ) = (110 * (100 : ℚ) ^ (2 * m + 1) - 10 * (10 : ℚ) ^ (2 * m + 1)
      - 55 - 45 * (-1 : ℚ) ^ (2 * m + 1)) / 99) ∧
    ((a (2 * m + 2) : ℚ) = (110 * (100 : ℚ) ^ (2 * m + 2) - 10 * (10 : ℚ) ^ (2 * m + 2)
      - 55 - 45 * (-1 : ℚ) ^ (2 * m + 2)) / 99) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * 0 + 1 = 1 by norm_num, e1]; norm_num
    · rw [show 2 * 0 + 2 = 2 by norm_num, e2]; norm_num
  | succ k ih =>
    have h1 := a_step_odd (2 * k + 1) (by omega) (by omega)
    have h2 := a_step_even (2 * k + 2) (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, h1]
      push_cast
      rw [ih.1]
      have e : (-1 : ℚ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      have e' : (-1 : ℚ) ^ (2 * k + 1 + 2) = -1 := by
        rw [pow_add, e]; norm_num
      have hp : (10 : ℚ) ^ (2 * (2 * k + 1) + 3) = 1000 * 100 ^ (2 * k + 1) := by
        rw [show 2 * (2 * k + 1) + 3 = 3 + 2 * (2 * k + 1) by ring, pow_add, pow_mul]
        norm_num
      rw [e, e', hp]
      ring
    · rw [show 2 * (k + 1) + 2 = 2 * k + 2 + 2 by ring, h2]
      push_cast
      rw [ih.2]
      have e : (-1 : ℚ) ^ (2 * k + 2) = 1 := by rw [pow_add, pow_mul]; norm_num
      have e' : (-1 : ℚ) ^ (2 * k + 2 + 2) = 1 := by
        rw [pow_add, e]; norm_num
      have hp : (10 : ℚ) ^ (2 * (2 * k + 2) + 3) = 1000 * 100 ^ (2 * k + 2) := by
        rw [show 2 * (2 * k + 2) + 3 = 3 + 2 * (2 * k + 2) by ring, pow_add, pow_mul]
        norm_num
      rw [e, e', hp]
      ring

open OMA.S_oeis_a267688 in
lemma aQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (110 * (100 : ℚ) ^ n - 10 * (10 : ℚ) ^ n - 55 - 45 * (-1 : ℚ) ^ n) / 99 := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨(n - 2) / 2, by have := Nat.even_iff.mp he; omega⟩
    exact (aQ2 m).2
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨(n - 1) / 2, by have := Nat.odd_iff.mp ho; omega⟩
    exact (aQ2 m).1

open OMA.S_oeis_a267688 in
lemma e3 : (a 3 : ℚ) = 1111010 := by
  have h := aQ 3 (by norm_num)
  norm_num at h
  exact h

open OMA.S_oeis_a267688 in
lemma e4 : (a 4 : ℚ) = 111110100 := by
  have h := aQ 4 (by norm_num)
  norm_num at h
  exact h

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267688Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267688 A267688Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267688.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    rw [aQ (m + 5) (by omega), aQ (m + 4) (by omega), aQ (m + 3) (by omega), aQ (m + 2) (by omega), aQ (m + 1) (by omega)]
    push_cast
    ring
  · have hD : ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 100 * X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-110) * PowerSeries.X ^ 1 + PowerSeries.C 999 * PowerSeries.X ^ 2 + PowerSeries.C 110 * PowerSeries.X ^ 3 + PowerSeries.C (-1000) * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - X ^ 2 + 10 * X ^ 3 - 1000 * X ^ 4 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 2 + PowerSeries.C 10 * PowerSeries.X ^ 3 + PowerSeries.C (-1000) * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · norm_num [e0, e1, e2, e3]
    · norm_num [e0, e1, e2, e3, e4]
    · have f1 := aQ (n + 1) (by omega)
      have f2 := aQ (n + 2) (by omega)
      have f3 := aQ (n + 3) (by omega)
      have f4 := aQ (n + 4) (by omega)
      have f5 := aQ (n + 5) (by omega)
      simp [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega, show n + 5 - 3 = n + 2 by omega, show n + 5 - 4 = n + 1 by omega, f1, f2, f3, f4, f5]
      ring
