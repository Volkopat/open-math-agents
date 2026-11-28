import OMAStatements.S_oeis_a266440
import Mathlib

open OMA.S_oeis_a266440

private def live (t : ℕ) (i : ℤ) : Prop :=
  (t = 0 ∧ i = 0) ∨ t % 2 = 1

private lemma table (l c r : Bool) :
    eca 23 l c r = true ↔ (c = false ∧ r = false) ∨ (l = false ∧ r = false) ∨ (l = false ∧ c = false) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih, live]
    omega

private lemma cnt (t : ℕ) (ht : 1 ≤ t) (p : ℕ → Bool) (c : Bool)
    (h : ∀ k < 2 * t - 1, p k = c) :
    ((Finset.range (2 * t + 1)).filter fun k => p k = true).card =
      (if c then 2 * t - 1 else 0) + (if p (2 * t - 1) then 1 else 0) +
        (if p (2 * t) then 1 else 0) := by
  rw [Finset.card_filter, show 2 * t + 1 = (2 * t - 1) + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_congr rfl (fun k hk => by rw [h k (Finset.mem_range.mp hk)]),
    Finset.sum_const, Finset.card_range, show 2 * t - 1 + 1 = 2 * t by omega]
  cases c <;> simp

private def blk (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

private def bf (t : ℕ) : ℕ := if t = 0 then 1 else if t % 2 = 1 then 2 * t + 1 else 0

private def bz (t : ℕ) : ℤ := if t = 0 then 1 else if t % 2 = 1 then 2 * (t : ℤ) + 1 else 0

private lemma bfz (t : ℕ) : (bf t : ℤ) = bz t := by
  unfold bf bz; split_ifs <;> push_cast <;> omega

private lemma blk_eq (t : ℕ) : blk t = bf t := by
  rcases Nat.lt_or_ge t 1 with h | h
  · obtain rfl : t = 0 := by omega
    decide
  · unfold blk
    rw [cnt t h _ (decide (t % 2 = 1))]
    · unfold bf
      have e1 : state t (((2 * t - 1 : ℕ) : ℤ) - t) = decide (t % 2 = 1) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff]; simp only [decide_eq_true_eq, live]; push_cast
        omega
      have e2 : state t (((2 * t : ℕ) : ℤ) - t) = decide (t % 2 = 1) := by
        apply Bool.eq_iff_iff.mpr; rw [state_iff]; simp only [decide_eq_true_eq, live]; push_cast
        omega
      rw [e1, e2]
      split_ifs <;> simp_all <;> omega
    · intro k hk
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

private lemma closed' (n : ℕ) (hn : 0 < n) : 2 * (a n : ℤ) = n ^ 2 + ((-1) ^ n + 2) * n + (-1) ^ n - 1 := by
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

private lemma closed (n : ℕ) : 2 * (a n : ℤ) = n ^ 2 + ((-1) ^ n + 2) * n + (-1) ^ n - 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [a, cn, bf]
  · exact closed' n h

private lemma recur (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = (1 : ℤ) * a (n - 1) + (2 : ℤ) * a (n - 2) + (-2 : ℤ) * a (n - 3) + (-1 : ℤ) * a (n - 4) + (1 : ℤ) * a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m + 0 by omega]
  have h0 := closed (m + 5)
  have h1 := closed (m + 4)
  have h2 := closed (m + 3)
  have h3 := closed (m + 2)
  have h4 := closed (m + 1)
  have h5 := closed (m + 0)
  simp only [pow_add] at h0 h1 h2 h3 h4 h5
  push_cast at h0 h1 h2 h3 h4 h5
  have : (2 : ℤ) * (a (m + 5) - ((1 : ℤ) * a (m + 4) + (2 : ℤ) * a (m + 3) + (-2 : ℤ) * a (m + 2) + (-1 : ℤ) * a (m + 1) + (1 : ℤ) * a (m + 0))) = 0 := by
    linear_combination h0 - (1) * h1 - (2) * h2 - (-2) * h3 - (-1) * h4 - (1) * h5
  have := (mul_eq_zero.mp this).resolve_left (by norm_num)
  linarith

open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) = (X ^ 2 * (5 - X ^ 2) : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 3 * (1 + X) ^ 2) = F + (-1 : ℤ) • (F * X ^ 1) + (-2 : ℤ) • (F * X ^ 2) + (2 : ℤ) • (F * X ^ 3) + (1 : ℤ) • (F * X ^ 4) + (-1 : ℤ) • (F * X ^ 5) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (X ^ 2 * (5 - X ^ 2) : PowerSeries ℤ) = (5 : ℤ) • X ^ 2 + (-1 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 5 < n
  · have hr := recur n (by omega)
    split_ifs <;> first | omega | linarith
  · interval_cases n <;> simp [a, Finset.sum_range_succ, cn, bf] <;> decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a266440.main := by
  exact ⟨closed, fun n hn => by have := recur n hn; linarith, gf⟩
