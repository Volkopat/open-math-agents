import OMAStatements.S_oeis_a267940

/-!
# A267940: the rows of Rule 253, read in base 10

From row 2 on, every cell is ON (and every cell outside the row is ON). Row `n + 1` is
therefore row `n` followed by two ON cells, so `a (n + 3) = 100 * a (n + 2) + 11`.
-/

namespace OMA.S_oeis_a267940

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 253 l c r = true ↔
    ¬((¬l = true ∧ ¬c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 2) i = true := by
  have r1 : ∀ i : ℤ, state 1 i = true ↔ ¬(i = -1) := fun i => by
    simp only [state, eca_iff, decide_eq_true_eq]; omega
  induction t with
  | zero => intro i; show state 2 i = true; rw [state, eca_iff, r1, r1, r1]; omega
  | succ t ih => intro i; rw [state, ih, ih, ih]; rfl

lemma a_step (n : ℕ) : a (n + 3) = 100 * a (n + 2) + 11 := by
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

end OMA.S_oeis_a267940

open OMA.S_oeis_a267940 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267940.main := by
  have P : ∀ n, 3 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h1 : a (m + 4) = 100 * a (m + 3) + 11 := a_step (m + 1)
    have h2 : a (m + 3) = 100 * a (m + 2) + 11 := a_step m
    show (a (m + 4) : ℤ) = 101 * a (m + 3) - 100 * a (m + 2)
    omega
  refine ⟨P, ?_⟩
  have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 - 100 * X)) =
      B - C 101 * (B * X ^ 1) + C 100 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
  rw [e, show (1 - 90 * X + 10100 * X ^ 2 - 10000 * X ^ 3 : ℤ⟦X⟧) =
    1 - C 90 * X ^ 1 + C 10100 * X ^ 2 - C 10000 * X ^ 3 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_one, coeff_mk]
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 11 by decide, show a 2 = 11111 by decide, show a 3 = 1111111 by decide]
  · split_ifs <;> first | omega | linarith [P n (by omega)]
