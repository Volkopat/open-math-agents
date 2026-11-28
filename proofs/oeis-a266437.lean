import OMAStatements.S_oeis_a266437
import Mathlib

open OMA.S_oeis_a266437

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

private lemma cf (t : ℕ) : (black t : ℤ) = bz t := by
  rw [← bfz, ← blk_eq]; rfl

private lemma cn (t : ℕ) : black t = bf t := blk_eq t

private lemma ev (m : ℕ) : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
private lemma od (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num

private lemma closed (n : ℕ) (hn : 0 < n) : 2 * (a n : ℤ) = (1 - (-1) ^ n) * (2 * n + 1) := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [ev, a, cf]; unfold bz; split_ifs <;> push_cast <;> first | contradiction | omega | ring
  · rw [od, a, cf]; unfold bz; split_ifs <;> push_cast <;> first | contradiction | omega | ring

private lemma recur (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = (2 : ℤ) * a (n - 2) + (-1 : ℤ) * a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 2 = m + 3 by omega, show m + 5 - 4 = m + 1 by omega]
  have h0 := closed (m + 5) (by omega)
  have h2 := closed (m + 3) (by omega)
  have h4 := closed (m + 1) (by omega)
  simp only [pow_add] at h0 h2 h4
  push_cast at h0 h2 h4
  apply mul_left_cancel₀ (a := (2 : ℤ)) (by decide)
  linear_combination h0 - (2) * h2 - (-1) * h4

open PowerSeries in
private lemma gf : mk (fun n => (a n : ℤ)) * ((-1 + X ^ 2) ^ 2) = (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ) := by
  have v0 : a 0 = 1 := by simp [a, cn, bf]
  have v1 : a 1 = 3 := by simp [a, cn, bf]
  have v2 : a 2 = 0 := by simp [a, cn, bf]
  have v3 : a 3 = 7 := by simp [a, cn, bf]
  have v4 : a 4 = 0 := by simp [a, cn, bf]
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((-1 + X ^ 2) ^ 2) = F + (-2 : ℤ) • (F * X ^ 2) + (1 : ℤ) • (F * X ^ 4) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (3 : ℤ) • X ^ 1 + (-2 : ℤ) • X ^ 2 + (1 : ℤ) • X ^ 3 + (1 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_sub, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 4 < n
  · have hr := recur n (by omega)
    split_ifs <;> first | omega | linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]

theorem OMA.solution : type_of% @OMA.S_oeis_a266437.main := by
  exact ⟨gf, closed, fun n hn => by have := recur n hn; linarith⟩
