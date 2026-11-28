import OMAStatements.S_oeis_a266596
import Mathlib

open OMA.S_oeis_a266596

private def live (t : ℕ) (i : ℤ) : Prop :=
  (t = 0 ∧ i = 0) ∨ (t = 1 ∧ i ≠ -1 ∧ i ≠ 1) ∨ (2 ≤ t ∧ t % 2 = 0 ∧ -1 ≤ i ∧ i ≤ 1) ∨ (3 ≤ t ∧ t % 2 = 1 ∧ (i ≤ -3 ∨ 3 ≤ i))

private lemma table (l c r : Bool) :
    eca 37 l c r = true ↔ (l = false ∧ r = false) ∨ (l = true ∧ c = false ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih, live]
    omega

private lemma cnt2 (t : ℕ) (ht : 2 ≤ t) (p : ℕ → Bool) (c : Bool)
    (h : ∀ k < 2 * t + 1, (k < t - 2 ∨ t + 2 < k) → p k = c) :
    ((Finset.range (2 * t + 1)).filter fun k => p k = true).card =
      (if c then 2 * t - 4 else 0) + ((if p (t - 2) then 1 else 0) + (if p (t - 2 + 1) then 1 else 0) +
        (if p (t - 2 + 2) then 1 else 0) + (if p (t - 2 + 3) then 1 else 0) +
        (if p (t - 2 + 4) then 1 else 0)) := by
  have h1 : ∑ x ∈ Finset.range (t - 2), (if p x = true then 1 else 0) =
      ∑ x ∈ Finset.range (t - 2), (if c = true then 1 else 0) :=
    Finset.sum_congr rfl (fun k hk => by simp at hk; rw [h k (by omega) (by omega)])
  have h3 : ∑ x ∈ Finset.range (t - 2), (if p (t - 2 + 5 + x) = true then 1 else 0) =
      ∑ x ∈ Finset.range (t - 2), (if c = true then 1 else 0) :=
    Finset.sum_congr rfl (fun k hk => by simp at hk; rw [h _ (by omega) (by omega)])
  rw [Finset.card_filter, show 2 * t + 1 = (t - 2) + 5 + (t - 2) by omega, Finset.sum_range_add,
    Finset.sum_range_add, h1, h3]
  simp only [Finset.sum_const, Finset.card_range, Finset.sum_range_succ, Finset.sum_range_zero,
    smul_eq_mul, zero_add, Nat.add_zero]
  cases c <;> simp <;> omega

private def blk (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

private def bf (t : ℕ) : ℕ := if t ≤ 1 then 1 else if t % 2 = 0 then 3 else 2 * t - 4

private def bz (t : ℕ) : ℤ := if t ≤ 1 then 1 else if t % 2 = 0 then 3 else 2 * (t : ℤ) - 4

private lemma bfz (t : ℕ) : (bf t : ℤ) = bz t := by
  unfold bf bz; split_ifs <;> push_cast <;> omega

private lemma blk_eq (t : ℕ) : blk t = bf t := by
  rcases Nat.lt_or_ge t 2 with h | h
  · interval_cases t <;> decide
  · unfold blk
    rw [cnt2 t h _ (decide (t % 2 = 1))]
    · unfold bf
      have e0 : state t (((t - 2 : ℕ) : ℤ) - t) = decide (t = t + 1) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e1 : state t (((t - 2 + 1 : ℕ) : ℤ) - t) = decide (t % 2 = 0) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e2 : state t (((t - 2 + 2 : ℕ) : ℤ) - t) = decide (t % 2 = 0) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e3 : state t (((t - 2 + 3 : ℕ) : ℤ) - t) = decide (t % 2 = 0) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      have e4 : state t (((t - 2 + 4 : ℕ) : ℤ) - t) = decide (t = t + 1) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff, decide_eq_true_iff]; unfold live
        omega
      rw [e0, e1, e2, e3, e4]
      split_ifs <;> simp_all <;> omega
    · intro k hk hk'
      apply Bool.eq_iff_iff.mpr; rw [state_iff]; simp only [decide_eq_true_eq, live]
      omega

private lemma white_eq (t : ℕ) : white t = 2 * t + 1 - blk t := by
  unfold white blk
  have := Finset.card_filter_add_card_filter_not (s := Finset.range (2 * t + 1))
    (p := fun i : ℕ => state t ((i : ℤ) - (t : ℤ)) = true)
  simp only [Bool.not_eq_true, Finset.card_range] at this
  omega

private lemma cf (t : ℕ) : (white t : ℤ) = 2 * t + 1 - bz t := by
  have h1 := white_eq t
  have h2 : blk t ≤ 2 * t + 1 := by
    unfold blk; exact (Finset.card_filter_le _ _).trans (by simp)
  rw [← bfz, h1, blk_eq] at *; push_cast [h2]; omega

private lemma cn (t : ℕ) : white t = 2 * t + 1 - bf t := by rw [white_eq, blk_eq]

private lemma ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
private lemma od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

private lemma closed' (n : ℕ) (hn : 0 < n) : 2 * (a n : ℤ) = n ^ 2 + 4 * n + (-1) ^ n * (n - 3) - 3 := by
  induction n, hn using Nat.le_induction with
  | base => simp [a, Finset.sum_range_succ, cn, bf]
  | succ n hn ih =>
    have hs : a (n + 1) = a n + white (n + 1) := Finset.sum_range_succ _ _
    push_cast [hs, cf]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [ev] at ih; rw [od]; unfold bz
      split_ifs <;> push_cast at ih ⊢ <;> first | contradiction | omega | linear_combination ih
    · rw [od] at ih; rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, ev]; unfold bz
      split_ifs <;> push_cast at ih ⊢ <;> first | contradiction | omega | linear_combination ih

private lemma closed (n : ℕ) (hn : 0 < n) : 2 * (a n : ℤ) = n ^ 2 + 4 * n + (-1) ^ n * (n - 3) - 3 := closed' n hn

private lemma recur (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = (1 : ℤ) * a (n - 1) + (2 : ℤ) * a (n - 2) + (-2 : ℤ) * a (n - 3) + (-1 : ℤ) * a (n - 4) + (1 : ℤ) * a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  have h0 := closed (m + 6) (by omega)
  have h1 := closed (m + 5) (by omega)
  have h2 := closed (m + 4) (by omega)
  have h3 := closed (m + 3) (by omega)
  have h4 := closed (m + 2) (by omega)
  have h5 := closed (m + 1) (by omega)
  simp only [pow_add] at h0 h1 h2 h3 h4 h5
  push_cast at h0 h1 h2 h3 h4 h5
  have : (2 : ℤ) * (a (m + 6) - ((1 : ℤ) * a (m + 5) + (2 : ℤ) * a (m + 4) + (-2 : ℤ) * a (m + 3) + (-1 : ℤ) * a (m + 2) + (1 : ℤ) * a (m + 1))) = 0 := by
    linear_combination h0 - (1) * h1 - (2) * h2 - (-2) * h3 - (-1) * h4 - (1) * h5
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

set_option maxHeartbeats 2300000 in
open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) = (X * (2 + 2 * X + X ^ 2 + 2 * X ^ 3 - 3 * X ^ 4) : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 3 * (1 + X) ^ 2) = F + (-1 : ℤ) • (F * X ^ 1) + (-2 : ℤ) • (F * X ^ 2) + (2 : ℤ) • (F * X ^ 3) + (1 : ℤ) • (F * X ^ 4) + (-1 : ℤ) • (F * X ^ 5) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (X * (2 + 2 * X + X ^ 2 + 2 * X ^ 3 - 3 * X ^ 4) : PowerSeries ℤ) = (2 : ℤ) • X ^ 1 + (2 : ℤ) • X ^ 2 + (1 : ℤ) • X ^ 3 + (2 : ℤ) • X ^ 4 + (-3 : ℤ) • X ^ 5 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 5 < n
  · have hr := recur n (by omega)
    split_ifs <;> first | omega | linarith
  · interval_cases n <;> simp [a, Finset.sum_range_succ, cn, bf] <;> decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a266596.main := by
  exact ⟨closed, fun n hn => by have := recur n hn; linarith, gf⟩
