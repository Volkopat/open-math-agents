import OMAStatements.S_oeis_a308159

namespace OMA.S_oeis_a308159

open Finset PowerSeries



/-- The possible legs. -/
def legs (n : ℕ) : Finset ℕ := (range (n + 1)).filter (fun l => n < 4 * l ∧ 2 * l < n)

lemma a_eq_legs (n : ℕ) : a n = ∑ l ∈ legs n, max l (n - 2 * l) := by
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
    show z = max (if x = y then x else z) (n - 2 * (if x = y then x else z))
    by_cases h : x = y
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- The closed form. -/
def F (n : ℕ) : ℚ :=
  ((((n + 2) / 3 - 1 : ℕ) : ℚ) - ((n / 4 : ℕ) : ℚ)) * n -
    ((((n + 2) / 3 - 1 : ℕ) : ℚ) * ((((n + 2) / 3 - 1 : ℕ) : ℚ) + 1) -
      ((n / 4 : ℕ) : ℚ) * (((n / 4 : ℕ) : ℚ) + 1)) +
    (if n % 3 = 0 then (n : ℚ) / 3 else 0) +
    (((((n + 1) / 2 - 1 : ℕ) : ℚ) * ((((n + 1) / 2 - 1 : ℕ) : ℚ) + 1) -
      ((n / 3 : ℕ) : ℚ) * (((n / 3 : ℕ) : ℚ) + 1)) / 2)

lemma sum_Icc_id (L U : ℕ) (h : L ≤ U) :
    ∑ x ∈ Icc (L + 1) U, (x : ℚ) = ((U : ℚ) * (U + 1) - (L : ℚ) * (L + 1)) / 2 := by
  induction U, h using Nat.le_induction with
  | base => simp
  | succ U hU ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

lemma sum_Icc_lin (L U n : ℕ) (h : L ≤ U) (hn : 2 * U ≤ n) :
    ∑ x ∈ Icc (L + 1) U, ((n - 2 * x : ℕ) : ℚ) =
      ((U : ℚ) - L) * n - ((U : ℚ) * (U + 1) - (L : ℚ) * (L + 1)) := by
  have : ∀ x ∈ Icc (L + 1) U, ((n - 2 * x : ℕ) : ℚ) = (n : ℚ) - 2 * (x : ℚ) := by
    intro x hx
    rw [mem_Icc] at hx
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  rw [sum_congr rfl this, sum_sub_distrib, ← mul_sum, sum_Icc_id L U h, sum_const,
    Nat.card_Icc]
  rw [show U + 1 - (L + 1) = U - L by omega, nsmul_eq_mul, Nat.cast_sub h]
  ring

lemma legs_sum_eq (n : ℕ) (hn : 1 ≤ n) : ((∑ l ∈ legs n, max l (n - 2 * l) : ℕ) : ℚ) = F n := by
  rw [Nat.cast_sum]
  rw [← sum_filter_add_sum_filter_not (legs n) (fun l => 3 * l < n)]
  rw [← sum_filter_add_sum_filter_not ((legs n).filter (fun l => ¬ 3 * l < n)) (fun l => 3 * l = n)]
  have h1 : (legs n).filter (fun l => 3 * l < n) = Icc (n / 4 + 1) ((n + 2) / 3 - 1) := by
    ext l; simp only [legs, mem_filter, mem_range, mem_Icc]; omega
  have h3 : ((legs n).filter (fun l => ¬ 3 * l < n)).filter (fun l => ¬ 3 * l = n) =
      Icc (n / 3 + 1) ((n + 1) / 2 - 1) := by
    ext l; simp only [legs, mem_filter, mem_range, mem_Icc]; omega
  have h2 : ((legs n).filter (fun l => ¬ 3 * l < n)).filter (fun l => 3 * l = n) =
      if n % 3 = 0 then {n / 3} else ∅ := by
    ext l
    simp only [legs, mem_filter, mem_range]
    split_ifs with h
    · simp only [mem_singleton]; omega
    · simp only [Finset.notMem_empty, iff_false]; omega
  rw [h1, h2, h3]
  have e1 : ∀ l ∈ Icc (n / 4 + 1) ((n + 2) / 3 - 1), ((max l (n - 2 * l) : ℕ) : ℚ) =
      ((n - 2 * l : ℕ) : ℚ) := by
    intro l hl; rw [mem_Icc] at hl; congr 1; omega
  have e3 : ∀ l ∈ Icc (n / 3 + 1) ((n + 1) / 2 - 1), ((max l (n - 2 * l) : ℕ) : ℚ) = (l : ℚ) := by
    intro l hl; rw [mem_Icc] at hl; congr 1; omega
  rw [sum_congr rfl e1, sum_congr rfl e3, sum_Icc_lin _ _ _ (by omega) (by omega),
    sum_Icc_id _ _ (by omega)]
  unfold F
  split_ifs with h
  · rw [sum_singleton]
    have : ((max (n / 3) (n - 2 * (n / 3)) : ℕ) : ℚ) = (n : ℚ) / 3 := by
      rw [show max (n / 3) (n - 2 * (n / 3)) = n / 3 by omega]
      rw [Nat.cast_div (Nat.dvd_of_mod_eq_zero h) (by norm_num)]
      norm_num
    rw [this]
    ring
  · rw [sum_empty]
    ring

lemma a_eq_F (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = F n := by
  rw [a_eq_legs]
  exact legs_sum_eq n hn

lemma F_eval (q k : ℕ) (hk : 1 ≤ k) : F (12 * q + k) =
    (((4 * q + ((k + 2) / 3 - 1) : ℕ) : ℚ) - ((3 * q + k / 4 : ℕ) : ℚ)) * (12 * q + k : ℕ) -
    (((4 * q + ((k + 2) / 3 - 1) : ℕ) : ℚ) * (((4 * q + ((k + 2) / 3 - 1) : ℕ) : ℚ) + 1) -
      ((3 * q + k / 4 : ℕ) : ℚ) * (((3 * q + k / 4 : ℕ) : ℚ) + 1)) +
    (if k % 3 = 0 then ((12 * q + k : ℕ) : ℚ) / 3 else 0) +
    ((((6 * q + ((k + 1) / 2 - 1) : ℕ) : ℚ) * (((6 * q + ((k + 1) / 2 - 1) : ℕ) : ℚ) + 1) -
      ((4 * q + k / 3 : ℕ) : ℚ) * (((4 * q + k / 3 : ℕ) : ℚ) + 1)) / 2) := by
  unfold F
  rw [show (12 * q + k + 2) / 3 - 1 = 4 * q + ((k + 2) / 3 - 1) by omega,
    show (12 * q + k) / 4 = 3 * q + k / 4 by omega,
    show (12 * q + k + 1) / 2 - 1 = 6 * q + ((k + 1) / 2 - 1) by omega,
    show (12 * q + k) / 3 = 4 * q + k / 3 by omega,
    show (12 * q + k) % 3 = k % 3 by omega]

lemma F_rec (q r : ℕ) (hr : r < 12) :
    F (12 * q + (r + 12)) = F (12 * q + (r + 9)) + 2 * F (12 * q + (r + 8)) -
      2 * F (12 * q + (r + 5)) - F (12 * q + (r + 4)) + F (12 * q + (r + 1)) := by
  rw [F_eval q (r + 12) (by omega), F_eval q (r + 9) (by omega), F_eval q (r + 8) (by omega),
    F_eval q (r + 5) (by omega), F_eval q (r + 4) (by omega), F_eval q (r + 1) (by omega)]
  interval_cases r <;> norm_num <;> push_cast <;> ring

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 11 < n) :
    (a n : ℤ) = a (n - 3) + 2 * a (n - 4) - 2 * a (n - 7) - a (n - 8) + a (n - 11) := by
  have hq : (a n : ℚ) = a (n - 3) + 2 * a (n - 4) - 2 * a (n - 7) - a (n - 8) + a (n - 11) := by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 12 ∧ n = 12 * q + (r + 12) :=
      ⟨(n - 12) / 12, (n - 12) % 12, Nat.mod_lt _ (by norm_num), by omega⟩
    rw [a_eq_F _ (by omega), a_eq_F _ (by omega), a_eq_F _ (by omega), a_eq_F _ (by omega),
      a_eq_F _ (by omega), a_eq_F _ (by omega)]
    rw [show 12 * q + (r + 12) - 3 = 12 * q + (r + 9) by omega,
      show 12 * q + (r + 12) - 4 = 12 * q + (r + 8) by omega,
      show 12 * q + (r + 12) - 7 = 12 * q + (r + 5) by omega,
      show 12 * q + (r + 12) - 8 = 12 * q + (r + 4) by omega,
      show 12 * q + (r + 12) - 11 = 12 * q + (r + 1) by omega, F_rec q r hr]
  exact_mod_cast hq




lemma den_eq : den = 1 - X ^ 3 - X ^ 4 - X ^ 4 + X ^ 7 + X ^ 7 + X ^ 8 - X ^ 11 := by
  unfold den; ring

lemma num_eq : num = X ^ 3 + X ^ 5 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 7 + X ^ 7 + X ^ 7 + X ^ 8 + X ^ 9 := by
  unfold num; ring

lemma a_small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 1 ∧ a 4 = 0 ∧ a 5 = 2 ∧ a 6 = 2 ∧ a 7 = 6 ∧
    a 8 = 3 ∧ a 9 = 7 ∧ a 10 = 8 ∧ a 11 = 14 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

lemma mul_den : A * den = num := by
  rw [den_eq, num_eq]
  ext n
  have e : A * (1 - X ^ 3 - X ^ 4 - X ^ 4 + X ^ 7 + X ^ 7 + X ^ 8 - X ^ 11) =
      A - A * X ^ 3 - A * X ^ 4 - A * X ^ 4 + A * X ^ 7 + A * X ^ 7 + A * X ^ 8 - A * X ^ 11 := by
    ring
  rw [e]
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := a_small
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] <;> norm_num
  · have hr := recurrence n (by omega)
    simp only [show 3 ≤ n by omega, show 4 ≤ n by omega, show 7 ≤ n by omega,
      show 8 ≤ n by omega, show 11 ≤ n by omega, if_true, show ¬ (n = 3) by omega,
      show ¬ (n = 5) by omega, show ¬ (n = 6) by omega, show ¬ (n = 7) by omega,
      show ¬ (n = 8) by omega, show ¬ (n = 9) by omega, if_false]
    have hq : (a n : ℚ) = a (n - 3) + 2 * a (n - 4) - 2 * a (n - 7) - a (n - 8) + a (n - 11) := by
      exact_mod_cast hr
    linarith

/-- Barker's two conjectures. -/
theorem conjecture : A = num * den⁻¹ ∧
    ∀ n : ℕ, 11 < n →
      (a n : ℤ) = a (n - 3) + 2 * a (n - 4) - 2 * a (n - 7) - a (n - 8) + a (n - 11) := by
  refine ⟨?_, recurrence⟩
  have h : constantCoeff den ≠ 0 := by rw [den_eq]; simp
  rw [← mul_den, mul_assoc, PowerSeries.mul_inv_cancel _ h, mul_one]

end OMA.S_oeis_a308159

theorem OMA.solution : type_of% @OMA.S_oeis_a308159.main :=
  OMA.S_oeis_a308159.conjecture
