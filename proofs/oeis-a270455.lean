import OMAStatements.S_oeis_a270455
import Mathlib

namespace A270455Aux

open OMA.S_oeis_a270455 in
lemma step_gen (code t : ℕ) (f g : ℤ → ℤ → Bool)
    (hf : ∀ i j, cell code t i j = f i j)
    (h : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), f i j = c → f (i + 1) j = n1 → f (i - 1) j = n2 →
      f i (j + 1) = n3 → f i (j - 1) = n4 →
      g i j = code.testBit (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat))) :
    ∀ i j, cell code (t + 1) i j = g i j := by
  intro i j
  show code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat +
      (cell code t i (j - 1)).toNat)) = g i j
  rw [hf, hf, hf, hf, hf]
  exact (h i j _ _ _ _ _ rfl rfl rfl rfl rfl).symm

/-- the diamond of radius `t` restricted to the cells with `i + j + t` even -/
def dmb (t : ℕ) (i j : ℤ) : Bool :=
  decide (i + j ≤ t ∧ -(t : ℤ) ≤ i + j ∧ i - j ≤ t ∧ -(t : ℤ) ≤ i - j ∧ (i + j + t) % 2 = 0)

def pb (t : ℕ) (i j : ℤ) : Bool :=
  decide ((t % 2 = 0 ∧ (i + j ≤ t ∧ -(t : ℤ) ≤ i + j ∧ i - j ≤ t ∧ -(t : ℤ) ≤ i - j ∧
    (i + j + t) % 2 = 0)) ∨ (t % 2 = 1 ∧ ¬(i + j ≤ t ∧ -(t : ℤ) ≤ i + j ∧ i - j ≤ t ∧
    -(t : ℤ) ≤ i - j ∧ (i + j + t) % 2 = 0)))

set_option maxHeartbeats 4000000 in
lemma tr_b (t : ℕ) : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), pb t i j = c →
    pb t (i + 1) j = n1 → pb t (i - 1) j = n2 → pb t i (j + 1) = n3 → pb t i (j - 1) = n4 →
    pb (t + 1) i j =
      Nat.testBit 163 (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat)) := by
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp only [pb, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a270455 in
lemma cN (t : ℕ) : ∀ i j, cell 163 t i j = pb t i j := by
  induction t with
  | zero =>
    intro i j
    show decide (i = 0 ∧ j = 0) = pb 0 i j
    unfold pb
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih => exact step_gen 163 k (pb k) (pb (k + 1)) ih (tr_b k)

lemma pb_even (t : ℕ) (ht : t % 2 = 0) (i j : ℤ) : pb t i j = dmb t i j := by
  unfold pb dmb
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

lemma pb_odd (t : ℕ) (ht : t % 2 = 1) (i j : ℤ) : pb t i j = !dmb t i j := by
  unfold pb dmb
  rw [← decide_not]
  apply decide_eq_decide.mpr
  constructor <;> intro h <;> omega

lemma cnt_par (lo m N : ℕ) :
    ∑ j ∈ Finset.range N, (if lo ≤ j ∧ j ≤ lo + 2 * m ∧ (j + lo) % 2 = 0 then 1 else 0) =
      (min N (lo + 2 * m + 1) + 1 - lo) / 2 := by
  induction N with
  | zero =>
    simp
    omega
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

lemma dia_row (t i : ℕ) (hi : i ≤ 2 * t) :
    ∑ j ∈ Finset.range (2 * t + 1),
      (if dmb t ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) = min i (2 * t - i) + 1 := by
  have h := cnt_par (t - min i (2 * t - i)) (min i (2 * t - i)) (2 * t + 1)
  rw [show (min (2 * t + 1) (t - min i (2 * t - i) + 2 * min i (2 * t - i) + 1) + 1 -
    (t - min i (2 * t - i))) / 2 = min i (2 * t - i) + 1 by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  simp only [dmb, decide_eq_true_eq]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

lemma tri (t : ℕ) : ∑ i ∈ Finset.range (2 * t + 1), (min i (2 * t - i) + 1) = (t + 1) ^ 2 := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ']
    have h : ∀ i ∈ Finset.range (2 * k + 1),
        min (i + 1) (2 * (k + 1) - (i + 1)) + 1 = (min i (2 * k - i) + 1) + 1 := by
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih]
    have e1 : min 0 (2 * (k + 1) - 0) + 1 = 1 := by omega
    have e2 : min (2 * k + 1 + 1) (2 * (k + 1) - (2 * k + 1 + 1)) + 1 = 1 := by omega
    rw [e1, e2]
    simp
    ring

lemma dia_total (t : ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if dmb t ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) = (t + 1) ^ 2 := by
  rw [Finset.sum_congr rfl (fun i hi => dia_row t i (by have := Finset.mem_range.mp hi; omega))]
  exact tri t

lemma compl2 (p : ℤ → ℤ → Bool) (t : ℕ) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1)) =
      (2 * t + 1) * (2 * t + 1) := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ Finset.range (2 * t + 1),
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1))
      = 2 * t + 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    have h2 : ∀ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) +
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1) = 1 := by
      intro j _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl h2]
    simp
  rw [Finset.sum_congr rfl h]
  simp

open OMA.S_oeis_a270455 in
lemma onE (t : ℕ) (ht : t % 2 = 0) : (onCount 163 t : ℤ) = ((t : ℤ) + 1) ^ 2 := by
  unfold onCount
  simp only [cN t, pb_even t ht]
  rw [dia_total]
  push_cast
  ring

open OMA.S_oeis_a270455 in
lemma onO (t : ℕ) (ht : t % 2 = 1) :
    (onCount 163 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - ((t : ℤ) + 1) ^ 2 := by
  unfold onCount
  simp only [cN t, pb_odd t ht]
  have h1 := compl2 (dmb t) t
  rw [dia_total] at h1
  have h4 : ∀ b : Bool, (if (!b) = true then (1 : ℕ) else 0) = (if b = true then 0 else 1) := by
    intro b
    cases b <;> rfl
  simp only [h4]
  have h3 := congrArg (fun z : ℕ => (z : ℤ)) h1
  push_cast at h3 ⊢
  linarith

open OMA.S_oeis_a270455 in
lemma onQ (t : ℕ) (ht : 0 ≤ t) : (onCount 163 t : ℚ) = (1 + (-1 : ℚ) ^ t) / 2 * (((t : ℚ) + 1) ^ 2) + (1 - (-1 : ℚ) ^ t) / 2 * ((2 * (t : ℚ) + 1) ^ 2 - ((t : ℚ) + 1) ^ 2) := by
  rcases Nat.even_or_odd t with h | h
  · have h1 := onE t (Nat.even_iff.mp h)
    have h2 : ((onCount 163 t : ℤ) : ℚ) = ((t : ℚ) + 1) ^ 2 := by rw [h1]; push_cast; ring
    rw [h.neg_one_pow]
    have h3 : (onCount 163 t : ℚ) = ((t : ℚ) + 1) ^ 2 := by exact_mod_cast h2
    rw [h3]; ring
  · have h1 := onO t (Nat.odd_iff.mp h)
    have h2 : ((onCount 163 t : ℤ) : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - ((t : ℚ) + 1) ^ 2 := by rw [h1]; push_cast; ring
    rw [h.neg_one_pow]
    have h3 : (onCount 163 t : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - ((t : ℚ) + 1) ^ 2 := by exact_mod_cast h2
    rw [h3]; ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a270455 in
lemma oq0 : (onCount 163 0 : ℚ) = 1 := by
  rw [onQ 0 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq1 : (onCount 163 1 : ℚ) = 5 := by
  rw [onQ 1 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq2 : (onCount 163 2 : ℚ) = 9 := by
  rw [onQ 2 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq3 : (onCount 163 3 : ℚ) = 33 := by
  rw [onQ 3 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq4 : (onCount 163 4 : ℚ) = 25 := by
  rw [onQ 4 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq5 : (onCount 163 5 : ℚ) = 85 := by
  rw [onQ 5 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq6 : (onCount 163 6 : ℚ) = 49 := by
  rw [onQ 6 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq7 : (onCount 163 7 : ℚ) = 161 := by
  rw [onQ 7 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq8 : (onCount 163 8 : ℚ) = 81 := by
  rw [onQ 8 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma oq9 : (onCount 163 9 : ℚ) = 261 := by
  rw [onQ 9 (by norm_num)]; norm_num

open OMA.S_oeis_a270455 in
lemma aS (n : ℕ) : (a (n + 1) : ℚ) = a n + (onCount 163 (n + 1) : ℚ) := by
  unfold a; rw [Finset.sum_range_succ]; push_cast; ring

open OMA.S_oeis_a270455 in
lemma e0 : (a 0 : ℚ) = 1 := by
  unfold a; rw [Finset.sum_range_one]; push_cast; rw [oq0]

open OMA.S_oeis_a270455 in
lemma e1 : (a 1 : ℚ) = 6 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, aS, e0, oq1]; norm_num

open OMA.S_oeis_a270455 in
lemma e2 : (a 2 : ℚ) = 15 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, aS, e1, oq2]; norm_num

open OMA.S_oeis_a270455 in
lemma e3 : (a 3 : ℚ) = 48 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, aS, e2, oq3]; norm_num

open OMA.S_oeis_a270455 in
lemma e4 : (a 4 : ℚ) = 73 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, aS, e3, oq4]; norm_num

open OMA.S_oeis_a270455 in
lemma e5 : (a 5 : ℚ) = 158 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, aS, e4, oq5]; norm_num

open OMA.S_oeis_a270455 in
lemma e6 : (a 6 : ℚ) = 207 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, aS, e5, oq6]; norm_num

open OMA.S_oeis_a270455 in
lemma e7 : (a 7 : ℚ) = 368 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, aS, e6, oq7]; norm_num

open OMA.S_oeis_a270455 in
lemma aQ (n : ℕ) (hn : 0 ≤ n) : (a n : ℚ) = (3 * (3 + (-1 : ℚ) ^ n) + (22 - 6 * (-1 : ℚ) ^ n) * (n : ℚ) - 6 * (-4 + (-1 : ℚ) ^ n) * (n : ℚ) ^ 2 + 8 * (n : ℚ) ^ 3) / 12 := by
  induction n, hn using Nat.le_induction with
  | base => rw [e0]; norm_num
  | succ k hk ih =>
    rw [aS, ih, onQ (k + 1) (by omega)]; push_cast; ring

end A270455Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a270455 A270455Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270455.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [aQ n (by omega)]
    first | done | ring
  · intro n hpar
    rw [aQ n (by omega)]
    first | done | rw [hpar.neg_one_pow]
    first | done | ring
  · intro n hpar
    rw [aQ n (by omega)]
    first | done | rw [hpar.neg_one_pow]
    first | done | ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m by omega]
    rw [aQ (m + 7) (by omega), aQ (m + 6) (by omega), aQ (m + 5) (by omega), aQ (m + 4) (by omega), aQ (m + 3) (by omega), aQ (m + 2) (by omega), aQ (m + 1) (by omega), aQ (m) (by omega)]
    push_cast
    ring
  · have hD : ((1 - X) ^ 4 * (1 + X) ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 + PowerSeries.C (-3) * PowerSeries.X ^ 2 + PowerSeries.C 3 * PowerSeries.X ^ 3 + PowerSeries.C 3 * PowerSeries.X ^ 4 + PowerSeries.C (-3) * PowerSeries.X ^ 5 + PowerSeries.C (-1) * PowerSeries.X ^ 6 + PowerSeries.C 1 * PowerSeries.X ^ 7 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 5 * X + 6 * X ^ 2 + 18 * X ^ 3 + X ^ 4 + X ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 5 * PowerSeries.X ^ 1 + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C 18 * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 + PowerSeries.C 1 * PowerSeries.X ^ 5 := by
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
    · have f0 := aQ (n) (by omega)
      have f1 := aQ (n + 1) (by omega)
      have f2 := aQ (n + 2) (by omega)
      have f3 := aQ (n + 3) (by omega)
      have f4 := aQ (n + 4) (by omega)
      have f5 := aQ (n + 5) (by omega)
      have f6 := aQ (n + 6) (by omega)
      have f7 := aQ (n + 7) (by omega)
      simp [show n + 7 - 1 = n + 6 by omega, show n + 7 - 2 = n + 5 by omega, show n + 7 - 3 = n + 4 by omega, show n + 7 - 4 = n + 3 by omega, show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega, show n + 7 - 7 = n by omega, f0, f1, f2, f3, f4, f5, f6, f7]
      ring
