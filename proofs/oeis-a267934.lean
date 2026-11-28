import OMAStatements.S_oeis_a267934

/-!
# A267934: the rows of Rule 249, read in base 10

From row 3 on, every cell is ON (and every cell outside the row is ON). Row `n + 1` is
therefore row `n` followed by two ON cells, so `a (n + 4) = 100 * a (n + 3) + 11`.
-/

namespace OMA.S_oeis_a267934

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 249 l c r = true ↔
    ¬((¬l = true ∧ ¬c = true ∧ r = true) ∨ (¬l = true ∧ c = true ∧ ¬r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 3) i = true := by
  have r1 : ∀ i : ℤ, state 1 i = true ↔ ¬(i = -1 ∨ i = 0) := fun i => by
    simp only [state, eca_iff, decide_eq_true_eq]; omega
  have r2 : ∀ i : ℤ, state 2 i = true ↔ ¬(i = 0) := fun i => by
    rw [state, eca_iff]; simp only [r1]; omega
  induction t with
  | zero => intro i; show state 3 i = true; rw [state, eca_iff, r2, r2, r2]; omega
  | succ t ih => intro i; rw [state, ih, ih, ih]; rfl

lemma a_step (n : ℕ) : a (n + 4) = 100 * a (n + 3) + 11 := by
  unfold a
  simp only [show ∀ i, state (n + 4) i = true from state_iff (n + 1), state_iff n, ↓reduceIte]
  rw [show 2 * (n + 4) + 1 = 2 * (n + 3) + 1 + 1 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.mul_sum, add_assoc,
    show 2 * (n + 4) - (2 * (n + 3) + 1) = 1 by omega,
    show 2 * (n + 4) - (2 * (n + 3) + 1 + 1) = 0 by omega]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show 2 * (n + 4) - k = 2 * (n + 3) - k + 2 by omega, pow_add]
  ring

end OMA.S_oeis_a267934

open OMA.S_oeis_a267934 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267934.main := by
  have P : ∀ n, 4 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h1 : a (m + 5) = 100 * a (m + 4) + 11 := a_step (m + 1)
    have h2 : a (m + 4) = 100 * a (m + 3) + 11 := a_step m
    show (a (m + 5) : ℤ) = 101 * a (m + 4) - 100 * a (m + 3)
    omega
  refine ⟨P, ?_⟩
  have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 - 100 * X)) =
      B - C 101 * (B * X ^ 1) + C 100 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
  rw [e, show (1 - 100 * X + 11010 * X ^ 2 - 900 * X ^ 3 - 10000 * X ^ 4 : ℤ⟦X⟧) =
    1 - C 100 * X ^ 1 + C 11010 * X ^ 2 - C 900 * X ^ 3 - C 10000 * X ^ 4 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_one, coeff_mk]
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 1 by decide, show a 2 = 11011 by decide, show a 3 = 1111111 by decide, show a 4 = 111111111 by decide]
  · split_ifs <;> first | omega | linarith [P n (by omega)]
