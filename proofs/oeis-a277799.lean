import OMAStatements.S_oeis_a277799

/- The even generations are a single live cell. The odd generations are the
   complement of the five-cell cross. This determines the binary digits on the axis. -/

open OMA.S_oeis_a277799 PowerSeries

namespace OMA.P_a277799

lemma step (t : ℕ) (i j : ℤ) : cell 1 (t+1) i j = !(cell 1 t i j || cell 1 t (i+1) j ||
    cell 1 t (i-1) j || cell 1 t i (j+1) || cell 1 t i (j-1)) := by
  rw [cell]
  dsimp only
  generalize cell 1 t i j = a
  generalize cell 1 t (i+1) j = b
  generalize cell 1 t (i-1) j = c
  generalize cell 1 t i (j+1) = d
  generalize cell 1 t i (j-1) = e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

lemma pattern (t : ℕ) : ∀ i j : ℤ, cell 1 t i j = if Even t then decide (i = 0 ∧ j = 0) else
    decide (¬ ((i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = -1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = -1))) := by
  induction t with
  | zero => intro i j; simp [cell]
  | succ t ih =>
    intro i j
    rw [step]
    rcases Nat.even_or_odd t with h | h
    · have h' : ¬ Even (t+1) := by rw [Nat.even_add_one]; simpa using h
      simp only [ih, h, h', if_true, if_false]
      rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq]
      omega
    · have h0 : ¬ Even t := Nat.not_even_iff_odd.mpr h
      have h' : Even (t+1) := by rw [Nat.even_add_one]; exact h0
      simp only [ih, h0, h', if_true, if_false]
      rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, not_not]
      omega

lemma geom (c : ℕ) : ∀ N : ℕ, ∑ k ∈ Finset.range N, (2 : ℤ) ^ (N + c - k) = 2 ^ (N + c + 1) - 2 ^ (c + 1) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    have : ∀ k ∈ Finset.range N, (2:ℤ) ^ (N + 1 + c - (k + 1)) = 2 ^ (N + c - k) := by
      intro k _; congr 1; omega
    rw [Finset.sum_congr rfl this, ih]
    have e : N + 1 + c - 0 = N + c + 1 := by omega
    rw [e, pow_succ, pow_succ, pow_succ]; ring

lemma a_even (m : ℕ) : a (2 * m) = 1 := by
  unfold a
  rw [Finset.sum_eq_single (2 * m)]
  · simp [pattern]
  · intro k hk hne
    have hk' : k < 2 * m + 1 := Finset.mem_range.mp hk
    rw [pattern]; simp; omega
  · intro h; simp at h

lemma a_odd (m : ℕ) : a (2 * m + 1) = 2 ^ (2 * m + 2) - 4 := by
  have ho : ¬ Even (2 * m + 1) := by simp
  unfold a
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : (cell 1 (2 * m + 1) ((↑(2 * m + 1) : ℤ) - ↑(2 * m + 1)) 0) = false := by
    rw [pattern, if_neg ho]; simp
  have h2 : (cell 1 (2 * m + 1) ((↑(2 * m) : ℤ) - ↑(2 * m + 1)) 0) = false := by
    rw [pattern, if_neg ho]; simp
  have h3 : ∀ k ∈ Finset.range (2 * m), (if cell 1 (2 * m + 1) ((k : ℤ) - ↑(2 * m + 1)) 0 then (2:ℤ) ^ (2 * m + 1 - k) else 0) = 2 ^ (2 * m + 1 - k) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [if_pos]; rw [pattern, if_neg ho]; simp; omega
  rw [h1, h2, Finset.sum_congr rfl h3, geom 1 (2 * m)]
  simp

lemma closed (n : ℕ) : (a n : ℚ) = -3 / 2 - (-2 : ℚ) ^ n + 5 * (-1 : ℚ) ^ n / 2 + (2 : ℚ) ^ n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [a_even]; simp [pow_mul]; ring
  · rw [a_odd]; push_cast; simp [pow_succ, pow_mul]; ring

end OMA.P_a277799

open OMA.P_a277799

theorem OMA.solution : type_of% @OMA.S_oeis_a277799.main := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 5 * a (n - 2) - 4 * a (n - 4) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [closed, closed, closed, show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega]
    ring
  refine ⟨?_, hrec, closed⟩
  have hp : ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) : PowerSeries ℚ) =
      1 - C (5 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 4 := by
    simp only [map_ofNat]; ring
  have hr : (1 - 4 * X ^ 2 + 12 * X ^ 3 : PowerSeries ℚ) = 1 - C (4 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 := by
    simp only [map_ofNat]
  rw [hp, hr]
  ext n
  have e : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - C (5 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 4) =
      PowerSeries.mk (fun n => (a n : ℚ)) - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) := by ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases n with _ | _ | _ | _ | n
  · norm_num [closed]
  · norm_num [closed]
  · norm_num [closed]
  · norm_num [closed]
  · simp only [show 2 ≤ n + 4 by omega, show 4 ≤ n + 4 by omega, if_true]
    rw [hrec (n + 4) (by omega)]
    simp

