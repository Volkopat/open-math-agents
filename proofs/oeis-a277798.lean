import OMAStatements.S_oeis_a277798

open OMA.S_oeis_a277798 PowerSeries

namespace Rule1

def update (c r l u d : Bool) : Bool :=
  (1 : ℕ).testBit (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

lemma step (t : ℕ) (i j : ℤ) :
    cell 1 (t + 1) i j = update (cell 1 t i j) (cell 1 t (i + 1) j)
      (cell 1 t (i - 1) j) (cell 1 t i (j + 1)) (cell 1 t i (j - 1)) := rfl

lemma update_true_iff (c r l u d : Bool) :
    update c r l u d = true ↔ (c = false ∧ r = false ∧ l = false ∧ u = false ∧ d = false) := by
  cases c <;> cases r <;> cases l <;> cases u <;> cases d <;> decide

lemma step_from_even {t : ℕ} (h : ∀ i j : ℤ, cell 1 t i j = decide (i = 0 ∧ j = 0))
    (i j : ℤ) : cell 1 (t + 1) i j = decide (1 < i.natAbs + j.natAbs) := by
  rw [Bool.eq_iff_iff, step, update_true_iff]
  simp only [h, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

lemma step_from_odd {t : ℕ} (h : ∀ i j : ℤ, cell 1 t i j = decide (1 < i.natAbs + j.natAbs))
    (i j : ℤ) : cell 1 (t + 1) i j = decide (i = 0 ∧ j = 0) := by
  rw [Bool.eq_iff_iff, step, update_true_iff]
  simp only [h, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

lemma cell_even (m : ℕ) : ∀ i j : ℤ, cell 1 (2 * m) i j = decide (i = 0 ∧ j = 0) := by
  induction m with
  | zero => intro i j; rfl
  | succ m ih =>
    intro i j
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
    exact step_from_odd (step_from_even ih) i j

lemma cell_odd (m : ℕ) (i j : ℤ) : cell 1 (2 * m + 1) i j = decide (1 < i.natAbs + j.natAbs) :=
  step_from_even (cell_even m) i j

lemma a_even (m : ℕ) : a (2 * m) = (10 : ℤ) ^ (2 * m) := by
  unfold a
  have hcongr : ∑ k ∈ Finset.range (2 * m + 1),
      (if cell 1 (2 * m) (k : ℤ) 0 then (10 : ℤ) ^ (2 * m - k) else 0) =
      ∑ k ∈ Finset.range (2 * m + 1), (if k = 0 then (10 : ℤ) ^ (2 * m - k) else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cell_even]
    simp
  rw [hcongr, Finset.sum_ite_eq' (Finset.range (2 * m + 1)) 0 (fun k => (10 : ℤ) ^ (2 * m - k))]
  simp

lemma a_odd_mul (m : ℕ) : (a (2 * m + 1) : ℚ) * 9 = (10 : ℚ) ^ (2 * m) - 1 := by
  have ha : a (2 * m + 1) = ∑ j ∈ Finset.range (2 * m), (10 : ℤ) ^ j := by
    unfold a
    rw [← Finset.sum_range_reflect (fun k => if cell 1 (2 * m + 1) (k : ℤ) 0 then (10 : ℤ) ^ (2 * m + 1 - k) else 0) (2 * m + 1 + 1)]
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : cell 1 (2 * m + 1) ((2 * m + 1 - (2 * m + 1) : ℕ) : ℤ) 0 = false := by
      rw [cell_odd]; simp
    have h2 : cell 1 (2 * m + 1) ((2 * m + 1 - 2 * m : ℕ) : ℤ) 0 = false := by
      rw [cell_odd]; simp [show 2 * m + 1 - 2 * m = 1 by omega]
    rw [h1, h2]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 2 * m := Finset.mem_range.mp hj
    have hc : cell 1 (2 * m + 1) ((2 * m + 1 - j : ℕ) : ℤ) 0 = true := by
      rw [cell_odd, decide_eq_true_eq]
      omega
    rw [hc, if_pos rfl]
    congr 1
    omega
  rw [ha]
  push_cast
  have hg := geom_sum_mul (10 : ℚ) (2 * m)
  linarith

lemma closed_form (n : ℕ) :
    (a n : ℚ) = (-10 + 89 * (-10 : ℚ) ^ n + 10 * (-1 : ℚ) ^ n + 91 * (10 : ℚ) ^ n) / 180 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [a_even]
    push_cast
    have h1 : (-10 : ℚ) ^ (2 * m) = (10 : ℚ) ^ (2 * m) := by
      rw [pow_mul, pow_mul]; norm_num
    have h2 : (-1 : ℚ) ^ (2 * m) = 1 := by
      rw [pow_mul]; norm_num
    rw [h1, h2]
    ring
  · have hm := a_odd_mul m
    have h1 : (-10 : ℚ) ^ (2 * m + 1) = -10 * (10 : ℚ) ^ (2 * m) := by
      rw [pow_succ, pow_mul, pow_mul]; norm_num; ring
    have h2 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    have h3 : (10 : ℚ) ^ (2 * m + 1) = 10 * (10 : ℚ) ^ (2 * m) := by ring
    rw [h1, h2, h3]
    linarith

lemma recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 101 * a (n - 2) - 100 * a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega, closed_form]
  ring

end Rule1

open Rule1

theorem OMA.solution : type_of% @OMA.S_oeis_a277798.main := by
  refine ⟨?_, recurrence, closed_form⟩
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  have hd : s * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      C (1 : ℚ) * (s * X ^ 0)
      + C (-101 : ℚ) * (s * X ^ 2)
      + C (100 : ℚ) * (s * X ^ 4) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  have hp : (1 - X ^ 2 + 11 * X ^ 3 : PowerSeries ℚ) =
      C (1 : ℚ) * (X ^ 0 : PowerSeries ℚ)
      + C (-1 : ℚ) * (X ^ 2 : PowerSeries ℚ)
      + C (11 : ℚ) * (X ^ 3 : PowerSeries ℚ) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hd, hp]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [closed_form]
  · have hr := recurrence n (by omega)
    simp [show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
          show 2 ≤ n by omega, show 4 ≤ n by omega]
    linarith
