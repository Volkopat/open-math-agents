import OMAStatements.S_oeis_a267805
import Mathlib

namespace A267805Aux

/-- row `t` occupies the cells `-t..t`; the pattern is periodic mod 4 in the distance from the right end and depends on the parity of `t` -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide (-(t : ℤ) ≤ i ∧ i ≤ t ∧ ((t % 2 = 0 ∧ ((t : ℤ) - i) % 4 ≠ 3) ∨
    (t % 2 = 1 ∧ (i = t ∨ ((t : ℤ) - i) % 4 = 1 ∨ ((t : ℤ) - i) % 4 = 2))))

lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 214 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a267805 in
lemma cellP (t : ℕ) : ∀ i, cell 214 t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show ruleOut 214 (cell 214 k (i - 1)) (cell 214 k i) (cell 214 k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

/-- the digit contributed by cell `j - n` of row `n` -/
def w (n j : ℕ) : ℤ :=
  if OMA.S_oeis_a267805.cell 214 n ((j : ℤ) - (n : ℤ)) then (2 : ℤ) ^ (2 * n - j) else 0

open OMA.S_oeis_a267805 in
lemma a_w (n : ℕ) : a n = ∑ j ∈ Finset.range (2 * n + 1), w n j := rfl

lemma main_even (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 0) :
    ∑ j ∈ Finset.range (2 * n), w (n + 2) j = 16 * ∑ j ∈ Finset.range (2 * n), w n j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  unfold w
  rw [cellP, cellP]
  have e : p (n + 2) ((j : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
    unfold p
    apply decide_eq_decide.mpr
    push_cast
    constructor <;> intro h' <;> omega
  rw [e, show 2 * (n + 2) - j = (2 * n - j) + 4 by omega, pow_add]
  split_ifs <;> ring

lemma tail2_even (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 0) :
    ∑ x ∈ Finset.range 5, w (n + 2) (2 * n + x) = 23 := by
  have hv : ∀ x ∈ Finset.range 5, w (n + 2) (2 * n + x) =
      (if x ≠ 1 then (2 : ℤ) ^ (4 - x) else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    unfold w
    rw [cellP]
    have e : p (n + 2) (((2 * n + x : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = decide (x ≠ 1) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> omega
    rw [e, show 2 * (n + 2) - (2 * n + x) = 4 - x by omega]
    by_cases hT : x ≠ 1 <;> simp [hT]
  rw [Finset.sum_congr rfl hv]
  decide

lemma tail0_even (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 0) :
    ∑ x ∈ Finset.range 1, w n (2 * n + x) = 1 := by
  have hv : ∀ x ∈ Finset.range 1, w n (2 * n + x) =
      (if x = 0 then (2 : ℤ) ^ (0 - x) else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    unfold w
    rw [cellP]
    have e : p n (((2 * n + x : ℕ) : ℤ) - (n : ℤ)) = decide (x = 0) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> omega
    rw [e, show 2 * n - (2 * n + x) = 0 - x by omega]
    by_cases hT : x = 0 <;> simp [hT]
  rw [Finset.sum_congr rfl hv]
  decide

open OMA.S_oeis_a267805 in
lemma a_step_even (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 0) : a (n + 2) = 16 * a n + (7) := by
  rw [a_w, a_w, show 2 * (n + 2) + 1 = 2 * n + 5 by ring, Finset.sum_range_add,
    show 2 * n + 1 = 2 * n + 1 by ring, Finset.sum_range_add, main_even n hn h,
    tail2_even n hn h, tail0_even n hn h]
  ring

lemma main_odd (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 1) :
    ∑ j ∈ Finset.range (2 * n), w (n + 2) j = 16 * ∑ j ∈ Finset.range (2 * n), w n j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  unfold w
  rw [cellP, cellP]
  have e : p (n + 2) ((j : ℤ) - ((n + 2 : ℕ) : ℤ)) = p n ((j : ℤ) - (n : ℤ)) := by
    unfold p
    apply decide_eq_decide.mpr
    push_cast
    constructor <;> intro h' <;> omega
  rw [e, show 2 * (n + 2) - j = (2 * n - j) + 4 by omega, pow_add]
  split_ifs <;> ring

lemma tail2_odd (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 1) :
    ∑ x ∈ Finset.range 5, w (n + 2) (2 * n + x) = 7 := by
  have hv : ∀ x ∈ Finset.range 5, w (n + 2) (2 * n + x) =
      (if 2 ≤ x then (2 : ℤ) ^ (4 - x) else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    unfold w
    rw [cellP]
    have e : p (n + 2) (((2 * n + x : ℕ) : ℤ) - ((n + 2 : ℕ) : ℤ)) = decide (2 ≤ x) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> omega
    rw [e, show 2 * (n + 2) - (2 * n + x) = 4 - x by omega]
    by_cases hT : 2 ≤ x <;> simp [hT]
  rw [Finset.sum_congr rfl hv]
  decide

lemma tail0_odd (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 1) :
    ∑ x ∈ Finset.range 1, w n (2 * n + x) = 1 := by
  have hv : ∀ x ∈ Finset.range 1, w n (2 * n + x) =
      (if x = 0 then (2 : ℤ) ^ (0 - x) else 0) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    unfold w
    rw [cellP]
    have e : p n (((2 * n + x : ℕ) : ℤ) - (n : ℤ)) = decide (x = 0) := by
      unfold p
      apply decide_eq_decide.mpr
      push_cast
      constructor <;> intro h' <;> omega
    rw [e, show 2 * n - (2 * n + x) = 0 - x by omega]
    by_cases hT : x = 0 <;> simp [hT]
  rw [Finset.sum_congr rfl hv]
  decide

open OMA.S_oeis_a267805 in
lemma a_step_odd (n : ℕ) (hn : 0 ≤ n) (h : n % 2 = 1) : a (n + 2) = 16 * a n + (-9) := by
  rw [a_w, a_w, show 2 * (n + 2) + 1 = 2 * n + 5 by ring, Finset.sum_range_add,
    show 2 * n + 1 = 2 * n + 1 by ring, Finset.sum_range_add, main_odd n hn h,
    tail2_odd n hn h, tail0_odd n hn h]
  ring

open OMA.S_oeis_a267805 in
lemma recQ (m : ℕ) : (a (m + 4) : ℚ) = 17 * a (m + 2) - 16 * a (m) := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h1 := a_step_even (m + 2) (by omega) (by omega)
    have h2 := a_step_even (m) (by omega) (by omega)
    rw [show m + 2 + 2 = m + 4 by ring] at h1
    
    rw [h1, h2]
    push_cast
    ring
  · have h1 := a_step_odd (m + 2) (by omega) (by omega)
    have h2 := a_step_odd (m) (by omega) (by omega)
    rw [show m + 2 + 2 = m + 4 by ring] at h1
    
    rw [h1, h2]
    push_cast
    ring

open OMA.S_oeis_a267805 in
lemma e0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267805 in
lemma e1 : (a 1 : ℚ) = 7 := by
  have h : a 1 = 7 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267805 in
lemma e2 : (a 2 : ℚ) = 23 := by
  rw [a_step_even 0 (by norm_num) (by norm_num)]
  push_cast
  rw [e0]
  norm_num

open OMA.S_oeis_a267805 in
lemma e3 : (a 3 : ℚ) = 103 := by
  rw [a_step_odd 1 (by norm_num) (by norm_num)]
  push_cast
  rw [e1]
  norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267805Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267805 A267805Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267805.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega]
    linarith [recQ m]
  · have hD : ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-17) * PowerSeries.X ^ 2 + PowerSeries.C 16 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 7 * X + 6 * X ^ 2 - 16 * X ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 7 * PowerSeries.X ^ 1 + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C (-16) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e1]
    · norm_num [e0, e2]
    · norm_num [e1, e3]
    · have hr := recQ (n)
      simp [show n + 4 - 2 = n + 2 by omega, show n + 4 - 4 = n by omega]
      linarith
