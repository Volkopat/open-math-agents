import OMAStatements.S_oeis_a267458
import Mathlib

namespace A267458Aux

lemma cntAP (t : ℕ) (r lo hi : ℤ) (hr : r = 0 ∨ r = 1) (hlo : -(t : ℤ) ≤ lo) (hhi : hi ≤ t) :
    ((Finset.range (2 * t + 1)).filter (fun j : ℕ =>
      ((j : ℤ) - t) % 2 = r ∧ lo ≤ (j : ℤ) - t ∧ (j : ℤ) - t ≤ hi)).card =
      ((hi - r) / 2 + 1 - (lo - r + 1) / 2).toNat := by
  rw [← Int.card_Icc ((lo - r + 1) / 2) ((hi - r) / 2)]
  refine Finset.card_bij' (fun (j : ℕ) _ => ((j : ℤ) - t - r) / 2)
    (fun (k : ℤ) _ => (2 * k + r + t).toNat) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    rw [Finset.mem_Icc]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_filter, Finset.mem_range]
    omega
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    show (2 * (((j : ℤ) - t - r) / 2) + r + t).toNat = j
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    show ((((2 * k + r + t).toNat : ℕ) : ℤ) - t - r) / 2 = k
    omega

/-- Closed form of the rows of Rule 133. -/
def Fb (t : ℕ) (i : ℤ) : Bool :=
  decide ((t = 0 ∧ i = 0) ∨ (t = 1 ∧ i ≠ -1 ∧ i ≠ 1) ∨
    (2 ≤ t ∧ (i < -(t : ℤ) ∨ (t : ℤ) < i ∨ (i % 2 = 0 ∧ 2 - (t : ℤ) ≤ i ∧ i ≤ (t : ℤ) - 2))))

open OMA.S_oeis_a267458 in
lemma rule_iff (x1 x2 x3 : Bool) : ruleOut 133 x1 x2 x3 = true ↔
    (x1 = false ∧ x3 = false) ∨ (x1 = true ∧ x2 = true ∧ x3 = true) := by
  revert x1 x2 x3
  decide

open OMA.S_oeis_a267458 in
lemma cellF (t : ℕ) : ∀ i : ℤ, cell 133 t i = Fb t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = Fb 0 i
    unfold Fb
    apply decide_eq_decide.mpr
    omega
  | succ t ih =>
    intro i
    show ruleOut 133 (cell 133 t (i - 1)) (cell 133 t i) (cell 133 t (i + 1)) = Fb (t + 1) i
    rw [ih (i - 1), ih i, ih (i + 1), Bool.eq_iff_iff, rule_iff]
    simp only [Fb, decide_eq_true_eq, decide_eq_false_iff_not]
    omega

open OMA.S_oeis_a267458 in
lemma on_card (t : ℕ) : onCount 133 t =
    ((Finset.range (2 * t + 1)).filter (fun j : ℕ => Fb t ((j : ℤ) - t) = true)).card := by
  unfold onCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cellF]

open OMA.S_oeis_a267458 in
lemma on_ge2 (t : ℕ) (h : 2 ≤ t) :
    onCount 133 t = (((t : ℤ) - 2 - 0) / 2 + 1 - (2 - (t : ℤ) - 0 + 1) / 2).toNat := by
  rw [on_card, ← cntAP t 0 (2 - (t : ℤ)) ((t : ℤ) - 2) (Or.inl rfl) (by omega) (by omega)]
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_range] at hj
  simp only [Fb, decide_eq_true_eq]
  omega

open OMA.S_oeis_a267458 in
lemma onQ0 (t : ℕ) (h0 : 2 ≤ t) (hp : t % 2 = 0) :
    ((onCount 133 t : ℤ) : ℚ) = (t : ℚ) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 2 * m := ⟨t / 2, by omega⟩
  have h : (onCount 133 (2 * m) : ℤ) = 2 * (m : ℤ) - 1 := by
    rw [on_ge2 (2 * m) h0]
    omega
  rw [h]
  push_cast
  ring

open OMA.S_oeis_a267458 in
lemma onQ1 (t : ℕ) (h0 : 3 ≤ t) (hp : t % 2 = 1) :
    ((onCount 133 t : ℤ) : ℚ) = (t : ℚ) - 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 2 * m + 1 := ⟨t / 2, by omega⟩
  have h : (onCount 133 (2 * m + 1) : ℤ) = 2 * (m : ℤ) - 1 := by
    rw [on_ge2 (2 * m + 1) (by omega)]
    omega
  rw [h]
  push_cast
  ring


open OMA.S_oeis_a267458 in
lemma aC0 (n : ℕ) (h0 : 2 ≤ n) (hp : n % 2 = 0) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (0 : ℚ) * (n : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) + (-1 : ℚ) := by
  unfold a
  rw [onQ0 n (by omega) hp]
  ring

open OMA.S_oeis_a267458 in
lemma aC1 (n : ℕ) (h0 : 3 ≤ n) (hp : n % 2 = 1) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (0 : ℚ) * (n : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) + (-2 : ℚ) := by
  unfold a
  rw [onQ1 n (by omega) hp]
  ring

open OMA.S_oeis_a267458 in
lemma av0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]
  norm_num

open OMA.S_oeis_a267458 in
lemma av1 : (a 1 : ℚ) = 1 := by
  have h : a 1 = 1 := by decide
  rw [h]
  norm_num

open OMA.S_oeis_a267458 in
lemma av2 : (a 2 : ℚ) = 1 := by
  rw [aC0 2 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a267458 in
lemma av3 : (a 3 : ℚ) = 1 := by
  rw [aC1 3 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a267458 in
lemma av4 : (a 4 : ℚ) = 3 := by
  rw [aC0 4 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a267458 in
lemma av5 : (a 5 : ℚ) = 3 := by
  rw [aC1 5 (by norm_num) (by norm_num)]
  norm_num

open OMA.S_oeis_a267458 in
lemma rec_gen (m : ℕ) : (1 : ℚ) * (a (m + 6) : ℚ) + (-1 : ℚ) * (a (m + 5) : ℚ) + (-1 : ℚ) * (a (m + 4) : ℚ) + (1 : ℚ) * (a (m + 3) : ℚ) = 0 := by
  rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with h | h
  · rw [aC0 (m + 6) (by omega) (by omega),
      aC1 (m + 5) (by omega) (by omega),
      aC0 (m + 4) (by omega) (by omega),
      aC1 (m + 3) (by omega) (by omega)]
    push_cast
    ring
  · rw [aC1 (m + 6) (by omega) (by omega),
      aC0 (m + 5) (by omega) (by omega),
      aC1 (m + 4) (by omega) (by omega),
      aC0 (m + 3) (by omega) (by omega)]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267458Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267458 A267458Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267458.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 3 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5]
    · rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
      · have h1 : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (by rw [Nat.even_iff]; omega)
        rw [aC0 n (by omega) h]
        rw [h1]
        ring
      · have h1 : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (by rw [Nat.odd_iff]; omega)
        rw [aC1 n (by omega) h]
        rw [h1]
        ring
  · intro n hn
    rcases Nat.lt_or_ge n 6 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      rw [show j + 3 - 1 = j + 2 from by omega, show j + 3 - 2 = j + 1 from by omega, show j + 3 - 3 = j from by omega]
      rcases (show j % 2 = 0 ∨ j % 2 = 1 by omega) with h | h
      · rw [aC1 (j + 3) (by omega) (by omega), aC0 (j + 2) (by omega) (by omega), aC1 (j + 1) (by omega) (by omega), aC0 (j) (by omega) (by omega)]
        push_cast
        ring
      · rw [aC0 (j + 3) (by omega) (by omega), aC1 (j + 2) (by omega) (by omega), aC0 (j + 1) (by omega) (by omega), aC1 (j) (by omega) (by omega)]
        push_cast
        ring
  · have hD : (((1 - X) ^ 2 * (1 + X) : PowerSeries ℚ)) = C (1 : ℚ) * X ^ 0 + C (-1 : ℚ) * X ^ 1 + C (-1 : ℚ) * X ^ 2 + C (1 : ℚ) * X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (1 - X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-1 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 6 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [if_pos (show 0 ≤ m + 6 by omega),
        if_pos (show 1 ≤ m + 6 by omega),
        if_pos (show 2 ≤ m + 6 by omega),
        if_pos (show 3 ≤ m + 6 by omega),
        if_neg (show ¬ (m + 6 = 0) by omega),
        if_neg (show ¬ (m + 6 = 2) by omega),
        if_neg (show ¬ (m + 6 = 4) by omega)]
      rw [show m + 6 - 1 = m + 5 from by omega,
        show m + 6 - 2 = m + 4 from by omega,
        show m + 6 - 3 = m + 3 from by omega]
      rw [show m + 6 - 0 = m + 6 from by omega]
      have hrec := rec_gen m
      linarith
