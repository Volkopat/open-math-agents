import OMAStatements.S_oeis_a267890

/-!
# A267890: the rows of Rule 239, read in base 2

From row 2 on, every cell is ON (and every cell outside the row is ON). Row `n + 1` is
therefore row `n` followed by two ON cells, so `a (n + 3) = 4 * a (n + 2) + 3`.
-/

namespace OMA.S_oeis_a267890

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 239 l c r = true ↔
    ¬((l = true ∧ ¬c = true ∧ ¬r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 2) i = true := by
  have r1 : ∀ i : ℤ, state 1 i = true ↔ ¬(i = 1) := fun i => by
    simp only [state, eca_iff, decide_eq_true_eq]; omega
  induction t with
  | zero => intro i; show state 2 i = true; rw [state, eca_iff, r1, r1, r1]; omega
  | succ t ih => intro i; rw [state, ih, ih, ih]; rfl

lemma a_step (n : ℕ) : a (n + 3) = 4 * a (n + 2) + 3 := by
  unfold a
  simp only [show ∀ i, state (n + 3) i = true from state_iff (n + 1), state_iff n, ↓reduceIte]
  rw [show 2 * (n + 3) + 1 = 2 * (n + 2) + 1 + 1 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.mul_sum, add_assoc,
    show 2 * (n + 3) - (2 * (n + 2) + 1) = 1 by omega,
    show 2 * (n + 3) - (2 * (n + 2) + 1 + 1) = 0 by omega]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show 2 * (n + 3) - k = 2 * (n + 2) - k + 2 by omega, pow_add]
  ring

end OMA.S_oeis_a267890

open OMA.S_oeis_a267890 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267890.main := by
  have P : ∀ n, 3 < n → (a n : ℤ) = 5 * a (n - 1) - 4 * a (n - 2) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h1 : a (m + 4) = 4 * a (m + 3) + 3 := a_step (m + 1)
    have h2 : a (m + 3) = 4 * a (m + 2) + 3 := a_step m
    show (a (m + 4) : ℤ) = 5 * a (m + 3) - 4 * a (m + 2)
    omega
  refine ⟨P, ?_⟩
  have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 - 4 * X)) =
      B - C 5 * (B * X ^ 1) + C 4 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
  rw [e, show (1 + X + 5 * X ^ 2 - 4 * X ^ 3 : ℤ⟦X⟧) =
    1 + C 1 * X ^ 1 + C 5 * X ^ 2 - C 4 * X ^ 3 by simp only [map_ofNat, map_one]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_one, coeff_mk]
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 6 by decide, show a 2 = 31 by decide, show a 3 = 127 by decide]
  · split_ifs <;> first | omega | linarith [P n (by omega)]
