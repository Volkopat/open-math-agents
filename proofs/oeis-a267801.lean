import OMAStatements.S_oeis_a267801

/-!
# A267801: the rows of Rule 213, read in base 10

From row 2 on, exactly the cells number 3, 4 of the {edge} are OFF (and every cell outside the row is ON). Row `n + 1` is
therefore two ON cells followed by row `n`, so `a (n + 1) = a n + 11 * 10 ^ (2 * n + 1)` from there on.
-/

namespace OMA.S_oeis_a267801

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 213 l c r = true ↔
    ¬((¬l = true ∧ ¬c = true ∧ r = true) ∨ (¬l = true ∧ c = true ∧ r = true) ∨ (l = true ∧ ¬c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 2) i = true ↔ i ≠ t ∧ i ≠ t - 1 := by
  have r1 : ∀ i : ℤ, state 1 i = true ↔ ¬(i = -1) := fun i => by
    simp only [state, eca_iff, decide_eq_true_eq]; omega
  induction t with
  | zero => intro i; show state 2 i = true ↔ _; rw [state, eca_iff, r1, r1, r1]; omega
  | succ t ih => intro i; rw [state, eca_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : a (n + 3) = a (n + 2) + 11 * 10 ^ (2 * (n + 2) + 1) := by
  unfold a
  rw [show 2 * (n + 3) + 1 = 2 * (n + 2) + 1 + 1 + 1 from rfl, Finset.sum_range_succ',
    Finset.sum_range_succ', if_pos ((state_iff (n + 1) _).2 (by omega)),
    if_pos ((state_iff (n + 1) _).2 (by omega)), add_assoc,
    show 10 ^ (2 * (n + 3) - (0 + 1)) + 10 ^ (2 * (n + 3) - 0) =
      11 * 10 ^ (2 * (n + 2) + 1) by
      rw [show 2 * (n + 3) - (0 + 1) = 2 * (n + 2) + 1 from rfl,
        show 2 * (n + 3) - 0 = 2 * (n + 2) + 1 + 1 from rfl, pow_succ _ (2 * (n + 2) + 1)]
      ring]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk := Finset.mem_range.mp hk
  rw [show state (n + 3) ((k + 1 + 1 : ℕ) - (n + 3 : ℕ)) = state (n + 2) (k - (n + 2 : ℕ)) from
    Bool.eq_iff_iff.2 (by rw [state_iff (n + 1), state_iff n]; omega),
    show 2 * (n + 3) - (k + 1 + 1) = 2 * (n + 2) - k by omega]

end OMA.S_oeis_a267801

open OMA.S_oeis_a267801 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267801.main := by
  have P : ∀ n, 3 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h1 : a (m + 4) = a (m + 3) + 11 * 10 ^ (2 * (m + 3) + 1) := a_step (m + 1)
    have h2 : a (m + 3) = a (m + 2) + 11 * 10 ^ (2 * (m + 2) + 1) := a_step m
    have h3 : 10 ^ (2 * (m + 3) + 1) = 100 * 10 ^ (2 * (m + 2) + 1) := by ring
    show (a (m + 4) : ℤ) = 101 * a (m + 3) - 100 * a (m + 2)
    omega
  refine ⟨P, ?_⟩
  have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 - 100 * X)) =
      B - C 101 * (B * X ^ 1) + C 100 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
  rw [e, show ((1 + 10 * X) * (1 - 100 * X + 10000 * X ^ 2) : ℤ⟦X⟧) =
    1 - C 90 * X ^ 1 + C 9000 * X ^ 2 + C 100000 * X ^ 3 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_one, coeff_mk]
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 11 by decide, show a 2 = 10011 by decide, show a 3 = 1110011 by decide]
  · split_ifs <;> first | omega | linarith [P n (by omega)]
