import OMAStatements.S_oeis_a266976
import Mathlib

/-!
# oeis-a266976: Rule 78 from a single ON cell

The cell formula is proved by induction: after t steps the cells -t..t (offsets j = 0..2t from the
left edge) are ON exactly at offsets j = 0, j = 1 and j <= t with j + t even, and all other cells are OFF. So row t + 2 is row t followed by four OFF
cells, plus one ON cell at offset t + 2, which gives a(t + 2) = 16 a(t) + 2^(t + 2). The recurrence,
the closed form (two-step induction) and the generating function (coefficient comparison) follow.

Source: OEIS A266976, https://oeis.org/A266976.
-/
namespace OMA.P_oeis_a266976

open OMA.S_oeis_a266976

lemma ruleOut_eq (l c r : Bool) : ruleOut 78 l c r = ((!l && (c || r)) || (l && c && !r)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cell_eq (t : ℕ) (i : ℤ) :
    cell 78 t i = decide (-(t:ℤ) ≤ i ∧ i ≤ 0 ∧ (i = -(t:ℤ) ∨ i = -(t:ℤ) + 1 ∨ i % 2 = 0)) := by
  induction t generalizing i with
  | zero =>
    show decide (i = 0) = _
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    push_cast
    omega
  | succ t ih =>
    simp only [cell, ruleOut_eq]
    rw [ih, ih, ih, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq]
    push_cast
    omega

abbrev D (t j : ℕ) : Prop := j ≤ t ∧ (j = 0 ∨ j = 1 ∨ (j + t) % 2 = 0)

lemma digit (t j : ℕ) : cell 78 t ((j : ℤ) - t) = decide (D t j) := by
  rw [cell_eq, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  omega

lemma a_eq (t : ℕ) :
    a t = ∑ j ∈ Finset.range (t + 1), if D t j then (2 : ℤ) ^ (2 * t - j) else 0 := by
  unfold a
  rw [show 2 * t + 1 = (t + 1) + t by ring, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range t,
      (if cell 78 t (((t + 1 + x : ℕ) : ℤ) - t) then (2 : ℤ) ^ (2 * t - (t + 1 + x)) else 0)
      = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [digit]
    simp only [decide_eq_true_eq]
    rw [if_neg (by omega)]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [digit]
  simp

theorem key (t : ℕ) (ht : 1 ≤ t) : a (t + 2) = 16 * a t + 2 ^ (t + 2) := by
  rw [a_eq (t + 2), a_eq t, Finset.sum_range_succ, Finset.sum_range_succ, Finset.mul_sum]
  rw [if_neg (by omega), if_pos (by omega), show 2 * (t + 2) - (t + 2) = t + 2 by omega]
  have : ∀ j ∈ Finset.range (t + 1),
      (if D (t + 2) j then (2 : ℤ) ^ (2 * (t + 2) - j) else 0) =
        16 * (if D t j then (2 : ℤ) ^ (2 * t - j) else 0) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    by_cases h : D t j
    · rw [if_pos (by omega), if_pos h,
        show 2 * (t + 2) - j = (2 * t - j) + 4 by omega, pow_add]; ring
    · rw [if_neg (by omega), if_neg h]; simp
  rw [Finset.sum_congr rfl this]
  ring

theorem rec3 (t : ℕ) (ht : 1 ≤ t) : a (t + 3) = 2 * a (t + 2) + 16 * a (t + 1) - 32 * a t := by
  have e1 := key (t + 1) (by omega)
  have e2 := key t ht
  rw [show t + 1 + 2 = t + 3 by ring, show t + 1 + 2 = t + 3 by ring] at e1
  rw [show (2 : ℤ) ^ (t + 3) = 2 * 2 ^ (t + 2) by ring] at e1
  linarith

lemma a0 : a 0 = 1 := by decide
lemma a1 : a 1 = 6 := by decide
lemma a2 : a 2 = 28 := by decide
lemma a3 : a 3 = 104 := by decide

lemma zp (n : ℕ) (c : ℤ) : (2 : ℚ) ^ ((((n + 2 : ℕ)) : ℤ) - c) = 4 * (2 : ℚ) ^ ((n : ℤ) - c) := by
  rw [show (((n + 2 : ℕ)) : ℤ) - c = ((n : ℤ) - c) + 2 by push_cast; ring,
    zpow_add₀ (by norm_num)]
  norm_num; ring

lemma zn (n c : ℕ) : (2 : ℚ) ^ n = 2 ^ c * (2 : ℚ) ^ ((n : ℤ) - (c : ℤ)) := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 1; ring

theorem closed (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 2) * ((-2 : ℚ) ^ n + 21 * 2 ^ n - 4) / 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => omega
    | 1, _ => rw [a1]; norm_num
    | 2, _ => rw [a2]; norm_num
    | n + 3, ih =>
      have hk : ((a (n + 1 + 2) : ℤ) : ℚ) = 16 * (a (n + 1) : ℚ) + 2 ^ (n + 1 + 2) := by
        rw [key (n + 1) (by omega)]; push_cast; ring
      rw [show n + 3 = n + 1 + 2 by ring, hk, ih (n + 1) (by omega) (by omega), zp (n + 1) 2]
      have h := zn (n + 1) 2
      push_cast at h
      have p1 : (2 : ℚ) ^ (n + 1 + 2) = 4 * 2 ^ (n + 1) := by ring
      have p2 : (-2 : ℚ) ^ (n + 1 + 2) = 4 * (-2) ^ (n + 1) := by ring
      rw [p1, p2, h]
      push_cast
      ring

open PowerSeries in
theorem full :
    (∀ n > 0, (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 2) * ((-2 : ℚ) ^ n + 21 * 2 ^ n - 4) / 3) ∧
    (∀ n > 3, a n = 2 * a (n - 1) + 16 * a (n - 2) - 32 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 2 * X) * (1 - 4 * X) * (1 + 4 * X)) =
      1 + 4 * X - 16 * X ^ 3) := by
  refine ⟨fun n hn => closed n hn, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa [show m + 4 = (m + 1) + 3 by ring] using rec3 (m + 1) (by omega)
  · have hX : (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - 2 * X) * (1 - 4 * X) * (1 + 4 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
          - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
          - C (16 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
          + C (32 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat]
      ring
    rw [hX, show (1 + 4 * X - 16 * X ^ 3 : PowerSeries ℚ) =
      1 + C (4 : ℚ) * X ^ 1 - C (16 : ℚ) * X ^ 3 by simp only [map_ofNat]; ring]
    ext k
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases k with _ | _ | _ | _ | m
    · simp [a0]
    · simp [a0, a1, coeff_X]; norm_num
    · simp [a0, a1, a2, coeff_X]; norm_num
    · simp [a0, a1, a2, a3, coeff_X]; norm_num
    · have h := rec3 (m + 1) (by omega)
      simp only [show m + 1 + 1 + 1 + 1 - 1 = m + 1 + 2 by omega,
        show m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 by omega,
        show m + 1 + 1 + 1 + 1 - 3 = m + 1 by omega, show 1 ≤ m + 1 + 1 + 1 + 1 by omega,
        show 2 ≤ m + 1 + 1 + 1 + 1 by omega, show 3 ≤ m + 1 + 1 + 1 + 1 by omega, if_true]
      have hq : ((a (m + 1 + 3) : ℤ) : ℚ) =
          2 * (a (m + 1 + 2) : ℚ) + 16 * (a (m + 1 + 1) : ℚ) - 32 * (a (m + 1) : ℚ) := by
        exact_mod_cast h
      rw [show m + 1 + 1 + 1 + 1 = m + 1 + 3 by ring, hq]
      simp [coeff_X, coeff_one, coeff_X_pow]
      ring

end OMA.P_oeis_a266976

theorem OMA.solution : type_of% @OMA.S_oeis_a266976.main := OMA.P_oeis_a266976.full
