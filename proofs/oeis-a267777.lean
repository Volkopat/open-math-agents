import OMAStatements.S_oeis_a267777

/-!
# A267777: the rows of Rule 209, read in base 10

From row 1 on, exactly the cells number 2, 3 of the {edge} are OFF (and every cell outside the row is ON). Row `n + 1` is
therefore two ON cells followed by row `n`, so `a (n + 1) = a n + 11 * 10 ^ (2 * n + 1)` from there on.
-/

namespace OMA.S_oeis_a267777

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 209 l c r = true ↔
    (¬l = true ∧ ¬c = true ∧ ¬r = true) ∨ (l = true ∧ ¬c = true ∧ ¬r = true) ∨ (l = true ∧ c = true ∧ ¬r = true) ∨ (l = true ∧ c = true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 1) i = true ↔ i ≠ t ∧ i ≠ t - 1 := by
  induction t with
  | zero => intro i; simp only [state, eca_iff, decide_eq_true_eq]; omega
  | succ t ih => intro i; rw [state, eca_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : a (n + 2) = a (n + 1) + 11 * 10 ^ (2 * (n + 1) + 1) := by
  unfold a
  rw [show 2 * (n + 2) + 1 = 2 * (n + 1) + 1 + 1 + 1 from rfl, Finset.sum_range_succ',
    Finset.sum_range_succ', if_pos ((state_iff (n + 1) _).2 (by omega)),
    if_pos ((state_iff (n + 1) _).2 (by omega)), add_assoc,
    show 10 ^ (2 * (n + 2) - (0 + 1)) + 10 ^ (2 * (n + 2) - 0) =
      11 * 10 ^ (2 * (n + 1) + 1) by
      rw [show 2 * (n + 2) - (0 + 1) = 2 * (n + 1) + 1 from rfl,
        show 2 * (n + 2) - 0 = 2 * (n + 1) + 1 + 1 from rfl, pow_succ _ (2 * (n + 1) + 1)]
      ring]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk := Finset.mem_range.mp hk
  rw [show state (n + 2) ((k + 1 + 1 : ℕ) - (n + 2 : ℕ)) = state (n + 1) (k - (n + 1 : ℕ)) from
    Bool.eq_iff_iff.2 (by rw [state_iff (n + 1), state_iff n]; omega),
    show 2 * (n + 2) - (k + 1 + 1) = 2 * (n + 1) - k by omega]

end OMA.S_oeis_a267777

open OMA.S_oeis_a267777 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267777.main := by
  have P : ∀ n, 2 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h1 : a (m + 3) = a (m + 2) + 11 * 10 ^ (2 * (m + 2) + 1) := a_step (m + 1)
    have h2 : a (m + 2) = a (m + 1) + 11 * 10 ^ (2 * (m + 1) + 1) := a_step m
    have h3 : 10 ^ (2 * (m + 2) + 1) = 100 * 10 ^ (2 * (m + 1) + 1) := by ring
    show (a (m + 3) : ℤ) = 101 * a (m + 2) - 100 * a (m + 1)
    omega
  refine ⟨P, ?_⟩
  have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 - 100 * X)) =
      B - C 101 * (B * X ^ 1) + C 100 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
  rw [e, show (1 - 100 * X + 11000 * X ^ 2 : ℤ⟦X⟧) =
    1 - C 100 * X ^ 1 + C 11000 * X ^ 2 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_one, coeff_mk]
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 1 by decide, show a 2 = 11001 by decide]
  · split_ifs <;> first | omega | linarith [P n (by omega)]
