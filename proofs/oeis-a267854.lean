import OMAStatements.S_oeis_a267854
import Mathlib

namespace A267854Aux

/-- row `t` occupies the cells `-t..0`; cell `0` is ON and, counted from the left end, the cells `x = 1 mod 4` (even `t`) or `x = 3 mod 4` (odd `t`) are OFF -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide (-(t : ℤ) ≤ i ∧ i ≤ 0 ∧ (i = 0 ∨ (t % 2 = 0 ∧ (i + t) % 4 ≠ 1) ∨ (t % 2 = 1 ∧ (i + t) % 4 ≠ 3)))

set_option maxHeartbeats 4000000 in
lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 230 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a267854 in
lemma cellP (t : ℕ) : ∀ i, cell 230 t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show ruleOut 230 (cell 230 k (i - 1)) (cell 230 k i) (cell 230 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

/-- the digit contributed by cell `j - n` of row `n` -/
def w (n j : ℕ) : ℤ :=
  if OMA.S_oeis_a267854.cell 230 n ((j : ℤ) - (n : ℤ)) then (10 : ℤ) ^ (2 * n - j) else 0

open OMA.S_oeis_a267854 in
lemma a_w (n : ℕ) : a n = ∑ j ∈ Finset.range (2 * n + 1), w n j := rfl

lemma w_on (n j : ℕ) (h : p n ((j : ℤ) - (n : ℤ)) = true) : w n j = 10 ^ (2 * n - j) := by
  unfold w
  rw [cellP, h]
  rfl

lemma w_off (n j : ℕ) (h : p n ((j : ℤ) - (n : ℤ)) = false) : w n j = 0 := by
  unfold w
  rw [cellP, h]
  rfl

lemma split2 (n : ℕ) : ∑ j ∈ Finset.range (2 * (n + 2) + 1), w (n + 2) j =
    ∑ j ∈ Finset.range n, w (n + 2) j + (∑ x ∈ Finset.range 3, w (n + 2) (n + x) +
      ∑ y ∈ Finset.range (n + 2), w (n + 2) (n + (3 + y))) := by
  rw [show 2 * (n + 2) + 1 = n + (3 + (n + 2)) by ring, Finset.sum_range_add,
    Finset.sum_range_add]

lemma split0 (n : ℕ) : ∑ j ∈ Finset.range (2 * n + 1), w n j =
    ∑ j ∈ Finset.range n, w n j + (∑ x ∈ Finset.range 1, w n (n + x) +
      ∑ y ∈ Finset.range n, w n (n + (1 + y))) := by
  rw [show 2 * n + 1 = n + (1 + n) by ring, Finset.sum_range_add, Finset.sum_range_add]

lemma zero2 (n : ℕ) : ∑ y ∈ Finset.range (n + 2), w (n + 2) (n + (3 + y)) = 0 :=
  Finset.sum_eq_zero (fun y _ => w_off (n + 2) (n + (3 + y)) (by unfold p; rw [decide_eq_false_iff_not]; omega))

lemma zero0 (n : ℕ) : ∑ y ∈ Finset.range n, w n (n + (1 + y)) = 0 :=
  Finset.sum_eq_zero (fun y _ => w_off n (n + (1 + y)) (by unfold p; rw [decide_eq_false_iff_not]; omega))

lemma mid0 (n : ℕ) : ∑ x ∈ Finset.range 1, w n (n + x) = 10 ^ n := by
  rw [Finset.sum_range_one, w_on n (n + 0) (by unfold p; rw [decide_eq_true_eq]; omega), show 2 * n - (n + 0) = n by omega]

lemma main (n : ℕ) :
    ∑ j ∈ Finset.range n, w (n + 2) j = 10000 * ∑ j ∈ Finset.range n, w n j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  unfold w
  rw [cellP, cellP]
  have e : p (n + 2) ((j : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h' <;> omega
  rw [e, show 2 * (n + 2) - j = (2 * n - j) + 4 by omega, pow_add]
  split_ifs <;> ring

lemma mid2_0 (n : ℕ) (h : n % 4 = 0) :
    ∑ x ∈ Finset.range 3, w (n + 2) (n + x) = 10 ^ (n + 4) + 10 ^ (n + 2) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, w_on (n + 2) (n + 0) (by unfold p; rw [decide_eq_true_eq]; omega), w_off (n + 2) (n + 1) (by unfold p; rw [decide_eq_false_iff_not]; omega),
    w_on (n + 2) (n + 2) (by unfold p; rw [decide_eq_true_eq]; omega), show 2 * (n + 2) - (n + 0) = n + 4 by omega, show 2 * (n + 2) - (n + 2) = n + 2 by omega]
  first | done | ring

open OMA.S_oeis_a267854 in
lemma a_step_0 (n : ℕ) (h : n % 4 = 0) : a (n + 2) = 10000 * a n + (100) * 10 ^ n := by
  rw [a_w, a_w, split2 n, split0 n, main n, mid2_0 n h, zero2 n, mid0 n, zero0 n]
  ring

lemma mid2_1 (n : ℕ) (h : n % 4 = 1) :
    ∑ x ∈ Finset.range 3, w (n + 2) (n + x) = 10 ^ (n + 4) + 10 ^ (n + 3) + 10 ^ (n + 2) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, w_on (n + 2) (n + 0) (by unfold p; rw [decide_eq_true_eq]; omega), w_on (n + 2) (n + 1) (by unfold p; rw [decide_eq_true_eq]; omega),
    w_on (n + 2) (n + 2) (by unfold p; rw [decide_eq_true_eq]; omega), show 2 * (n + 2) - (n + 0) = n + 4 by omega, show 2 * (n + 2) - (n + 1) = n + 3 by omega, show 2 * (n + 2) - (n + 2) = n + 2 by omega]
  first | done | ring

open OMA.S_oeis_a267854 in
lemma a_step_1 (n : ℕ) (h : n % 4 = 1) : a (n + 2) = 10000 * a n + (1100) * 10 ^ n := by
  rw [a_w, a_w, split2 n, split0 n, main n, mid2_1 n h, zero2 n, mid0 n, zero0 n]
  ring

lemma mid2_2 (n : ℕ) (h : n % 4 = 2) :
    ∑ x ∈ Finset.range 3, w (n + 2) (n + x) = 10 ^ (n + 4) + 10 ^ (n + 3) + 10 ^ (n + 2) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, w_on (n + 2) (n + 0) (by unfold p; rw [decide_eq_true_eq]; omega), w_on (n + 2) (n + 1) (by unfold p; rw [decide_eq_true_eq]; omega),
    w_on (n + 2) (n + 2) (by unfold p; rw [decide_eq_true_eq]; omega), show 2 * (n + 2) - (n + 0) = n + 4 by omega, show 2 * (n + 2) - (n + 1) = n + 3 by omega, show 2 * (n + 2) - (n + 2) = n + 2 by omega]
  first | done | ring

open OMA.S_oeis_a267854 in
lemma a_step_2 (n : ℕ) (h : n % 4 = 2) : a (n + 2) = 10000 * a n + (1100) * 10 ^ n := by
  rw [a_w, a_w, split2 n, split0 n, main n, mid2_2 n h, zero2 n, mid0 n, zero0 n]
  ring

lemma mid2_3 (n : ℕ) (h : n % 4 = 3) :
    ∑ x ∈ Finset.range 3, w (n + 2) (n + x) = 10 ^ (n + 3) + 10 ^ (n + 2) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, w_off (n + 2) (n + 0) (by unfold p; rw [decide_eq_false_iff_not]; omega), w_on (n + 2) (n + 1) (by unfold p; rw [decide_eq_true_eq]; omega),
    w_on (n + 2) (n + 2) (by unfold p; rw [decide_eq_true_eq]; omega), show 2 * (n + 2) - (n + 1) = n + 3 by omega, show 2 * (n + 2) - (n + 2) = n + 2 by omega]
  first | done | ring

open OMA.S_oeis_a267854 in
lemma a_step_3 (n : ℕ) (h : n % 4 = 3) : a (n + 2) = 10000 * a n + (-8900) * 10 ^ n := by
  rw [a_w, a_w, split2 n, split0 n, main n, mid2_3 n h, zero2 n, mid0 n, zero0 n]
  ring

open OMA.S_oeis_a267854 in
lemma e0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267854 in
lemma e1 : (a 1 : ℚ) = 110 := by
  have h : a 1 = 110 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267854 in
lemma e2 : (a 2 : ℚ) = 10100 := by
  have h : a 2 = 10100 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267854 in
lemma e3 : (a 3 : ℚ) = 1111000 := by
  have h : a 3 = 1111000 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267854 in
lemma e4 : (a 4 : ℚ) = 101110000 := by
  have h : a 4 = 101110000 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267854 in
lemma e5 : (a 5 : ℚ) = 11101100000 := by
  have h : a 5 = 11101100000 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267854 in
lemma recQ (m : ℕ) : (a (m + 6) : ℚ) = 10000 * a (m + 4) + 10000 * a (m + 2) - 100000000 * a m := by
  have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases hm with h | h | h | h
  · have h1 := a_step_0 (m + 4) (by omega)
    have h2 := a_step_0 m h
    rw [show m + 4 + 2 = m + 6 by ring] at h1
    rw [h1, h2]
    push_cast
    ring
  · have h1 := a_step_1 (m + 4) (by omega)
    have h2 := a_step_1 m h
    rw [show m + 4 + 2 = m + 6 by ring] at h1
    rw [h1, h2]
    push_cast
    ring
  · have h1 := a_step_2 (m + 4) (by omega)
    have h2 := a_step_2 m h
    rw [show m + 4 + 2 = m + 6 by ring] at h1
    rw [h1, h2]
    push_cast
    ring
  · have h1 := a_step_3 (m + 4) (by omega)
    have h2 := a_step_3 m h
    rw [show m + 4 + 2 = m + 6 by ring] at h1
    rw [h1, h2]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267854Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267854 A267854Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267854.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 6 = m by omega]
    linarith [recQ m]
  · have hD : ((1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X) * (1 + 100 * X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-10000) * PowerSeries.X ^ 2 + PowerSeries.C (-10000) * PowerSeries.X ^ 4 + PowerSeries.C 100000000 * PowerSeries.X ^ 6 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 110 * X + 100 * X ^ 2 + 11000 * X ^ 3 + 100000 * X ^ 4 - 10000000 * X ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 110 * PowerSeries.X ^ 1 + PowerSeries.C 100 * PowerSeries.X ^ 2 + PowerSeries.C 11000 * PowerSeries.X ^ 3 + PowerSeries.C 100000 * PowerSeries.X ^ 4 + PowerSeries.C (-10000000) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e1]
    · norm_num [e0, e2]
    · norm_num [e1, e3]
    · norm_num [e0, e2, e4]
    · norm_num [e1, e3, e5]
    · have hr := recQ (n)
      simp [show n + 6 - 2 = n + 4 by omega, show n + 6 - 4 = n + 2 by omega, show n + 6 - 6 = n by omega]
      linarith
