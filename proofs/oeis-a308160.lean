import OMAStatements.S_oeis_a308160

namespace OMA.S_oeis_a308160

open Finset PowerSeries






/-- The possible legs. -/
def legs (n : ℕ) : Finset ℕ := (range (n + 1)).filter (fun l => n < 4 * l ∧ 2 * l < n)

lemma a_eq_legs (n : ℕ) : a n = ∑ l ∈ legs n, l := by
  unfold a
  refine Finset.sum_nbij' (fun t => if t.1 = t.2.1 then t.1 else t.2.2)
    (fun l => if n - 2 * l ≤ l then (n - 2 * l, l, l) else (l, l, n - 2 * l)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨x, y, z⟩ := t
    have ht' : (x < n + 1 ∧ y < n + 1 ∧ z < n + 1) ∧ 1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
        z < x + y ∧ (x = y ∨ y = z) := by simpa [tri] using ht
    show (if x = y then x else z) ∈ legs n
    rw [legs, Finset.mem_filter, mem_range]
    by_cases h : x = y
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  · intro l hl
    have hl' : l < n + 1 ∧ n < 4 * l ∧ 2 * l < n := by simpa [legs] using hl
    by_cases h : n - 2 * l ≤ l
    · rw [if_pos h]
      simp only [tri, Finset.mem_coe, Finset.mem_filter, mem_product, mem_range, le_refl,
        or_true, true_or, and_true, true_and]
      omega
    · rw [if_neg h]
      simp only [tri, Finset.mem_coe, Finset.mem_filter, mem_product, mem_range, le_refl,
        or_true, true_or, and_true, true_and]
      omega
  · intro t ht
    obtain ⟨x, y, z⟩ := t
    have ht' : (x < n + 1 ∧ y < n + 1 ∧ z < n + 1) ∧ 1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
        z < x + y ∧ (x = y ∨ y = z) := by simpa [tri] using ht
    show (if n - 2 * (if x = y then x else z) ≤ (if x = y then x else z) then
      (n - 2 * (if x = y then x else z), (if x = y then x else z), (if x = y then x else z)) else
      ((if x = y then x else z), (if x = y then x else z), n - 2 * (if x = y then x else z))) =
      (x, y, z)
    by_cases h : x = y
    · rw [if_pos h]
      by_cases h2 : n - 2 * x ≤ x
      · rw [if_pos h2]; simp only [Prod.mk.injEq, true_and, and_true]; omega
      · rw [if_neg h2]; simp only [Prod.mk.injEq, true_and, and_true]; omega
    · rw [if_neg h]
      by_cases h2 : n - 2 * z ≤ z
      · rw [if_pos h2]; simp only [Prod.mk.injEq, true_and, and_true]; omega
      · rw [if_neg h2]; simp only [Prod.mk.injEq, true_and, and_true]; omega
  · intro l hl
    have hl' : l < n + 1 ∧ n < 4 * l ∧ 2 * l < n := by simpa [legs] using hl
    by_cases h : n - 2 * l ≤ l
    · rw [if_pos h]
      show (if n - 2 * l = l then n - 2 * l else l) = l
      by_cases h2 : n - 2 * l = l
      · rw [if_pos h2]; exact h2
      · rw [if_neg h2]
    · rw [if_neg h]
      show (if l = l then l else n - 2 * l) = l
      rw [if_pos rfl]
  · intro t ht
    obtain ⟨x, y, z⟩ := t
    have ht' : (x < n + 1 ∧ y < n + 1 ∧ z < n + 1) ∧ 1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
        z < x + y ∧ (x = y ∨ y = z) := by simpa [tri] using ht
    show y = (if x = y then x else z)
    by_cases h : x = y
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- The closed form: the sum of the integers l with n/4 < l < n/2. -/
def F (n : ℕ) : ℚ :=
  ((((n + 1) / 2 - 1 : ℕ) : ℚ) * ((((n + 1) / 2 - 1 : ℕ) : ℚ) + 1) -
    ((n / 4 : ℕ) : ℚ) * (((n / 4 : ℕ) : ℚ) + 1)) / 2

lemma sum_Icc_id (L U : ℕ) (h : L ≤ U) :
    ∑ x ∈ Icc (L + 1) U, (x : ℚ) = ((U : ℚ) * (U + 1) - (L : ℚ) * (L + 1)) / 2 := by
  induction U, h using Nat.le_induction with
  | base => simp
  | succ U hU ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

lemma a_eq_F (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = F n := by
  rw [a_eq_legs, Nat.cast_sum]
  have h1 : legs n = Icc (n / 4 + 1) ((n + 1) / 2 - 1) := by
    ext l; simp only [legs, mem_filter, mem_range, mem_Icc]; omega
  rw [h1, sum_Icc_id _ _ (by omega)]
  rfl

lemma F_eval (q k : ℕ) (hk : 1 ≤ k) : F (4 * q + k) =
    ((((2 * q + ((k + 1) / 2 - 1)) : ℕ) : ℚ) * (((2 * q + ((k + 1) / 2 - 1) : ℕ) : ℚ) + 1) -
      ((q + k / 4 : ℕ) : ℚ) * (((q + k / 4 : ℕ) : ℚ) + 1)) / 2 := by
  unfold F
  rw [show (4 * q + k + 1) / 2 - 1 = 2 * q + ((k + 1) / 2 - 1) by omega,
    show (4 * q + k) / 4 = q + k / 4 by omega]

lemma F_rec (q r : ℕ) (hr : r < 4) :
    F (4 * q + (r + 10)) = F (4 * q + (r + 9)) + 2 * F (4 * q + (r + 6)) -
      2 * F (4 * q + (r + 5)) - F (4 * q + (r + 2)) + F (4 * q + (r + 1)) := by
  rw [F_eval q (r + 10) (by omega), F_eval q (r + 9) (by omega), F_eval q (r + 6) (by omega),
    F_eval q (r + 5) (by omega), F_eval q (r + 2) (by omega), F_eval q (r + 1) (by omega)]
  interval_cases r <;> norm_num <;> push_cast <;> ring

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 4) - 2 * a (n - 5) - a (n - 8) + a (n - 9) := by
  have hq : (a n : ℚ) = a (n - 1) + 2 * a (n - 4) - 2 * a (n - 5) - a (n - 8) + a (n - 9) := by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + (r + 10) :=
      ⟨(n - 10) / 4, (n - 10) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    rw [a_eq_F _ (by omega), a_eq_F _ (by omega), a_eq_F _ (by omega), a_eq_F _ (by omega),
      a_eq_F _ (by omega), a_eq_F _ (by omega)]
    rw [show 4 * q + (r + 10) - 1 = 4 * q + (r + 9) by omega,
      show 4 * q + (r + 10) - 4 = 4 * q + (r + 6) by omega,
      show 4 * q + (r + 10) - 5 = 4 * q + (r + 5) by omega,
      show 4 * q + (r + 10) - 8 = 4 * q + (r + 2) by omega,
      show 4 * q + (r + 10) - 9 = 4 * q + (r + 1) by omega, F_rec q r hr]
  exact_mod_cast hq

lemma den_eq : den = 1 - X - X ^ 4 - X ^ 4 + X ^ 5 + X ^ 5 + X ^ 8 - X ^ 9 := by
  unfold den; ring

lemma num_eq : num = X ^ 3 - X ^ 4 + X ^ 5 + X ^ 5 + X ^ 7 := by
  unfold num; ring

lemma a_small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 1 ∧ a 4 = 0 ∧ a 5 = 2 ∧ a 6 = 2 ∧ a 7 = 5 ∧
    a 8 = 3 ∧ a 9 = 7 := by
  simp only [a_eq_legs]
  decide

/-- Controls: the entry's data a(1..26). -/
theorem controls : (List.range 26).map (fun i => a (i + 1)) =
    [0, 0, 1, 0, 2, 2, 5, 3, 7, 7, 12, 9, 15, 15, 22, 18, 26, 26, 35, 30, 40, 40, 51, 45, 57,
      57] := by
  rw [show (fun i => a (i + 1)) = (fun i => ∑ l ∈ legs (i + 1), l) from
    funext (fun i => a_eq_legs (i + 1))]
  decide

lemma mul_den : A * den = num := by
  rw [den_eq, num_eq]
  ext n
  have e : A * (1 - X - X ^ 4 - X ^ 4 + X ^ 5 + X ^ 5 + X ^ 8 - X ^ 9) =
      A - A * X ^ 1 - A * X ^ 4 - A * X ^ 4 + A * X ^ 5 + A * X ^ 5 + A * X ^ 8 - A * X ^ 9 := by
    ring
  rw [e]
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := a_small
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] <;> norm_num
  · have hr := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show 8 ≤ n by omega, show 9 ≤ n by omega, if_true, show ¬ (n = 3) by omega,
      show ¬ (n = 4) by omega, show ¬ (n = 5) by omega, show ¬ (n = 7) by omega, if_false]
    have hq : (a n : ℚ) = a (n - 1) + 2 * a (n - 4) - 2 * a (n - 5) - a (n - 8) + a (n - 9) := by
      exact_mod_cast hr
    linarith

/-- Barker's two conjectures. -/
theorem conjecture : A = num * den⁻¹ ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 4) - 2 * a (n - 5) - a (n - 8) + a (n - 9) := by
  refine ⟨?_, recurrence⟩
  have h : constantCoeff den ≠ 0 := by rw [den_eq]; simp
  rw [← mul_den, mul_assoc, PowerSeries.mul_inv_cancel _ h, mul_one]

end OMA.S_oeis_a308160

theorem OMA.solution : type_of% @OMA.S_oeis_a308160.main :=
  OMA.S_oeis_a308160.conjecture
