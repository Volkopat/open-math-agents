import OMAStatements.S_oeis_a267535

/-!
# A267535: the rows of Rule 143, read in base 10

Rule 143 turns a cell ON unless its left neighbour is ON while the cell or its right neighbour is
OFF. From row 2 on, exactly two cells are OFF, the third and fourth cells of the row. Row `n + 1`
is therefore row `n` followed by two ON cells, so `a (n + 3) = 100 * a (n + 2) + 11`.
-/

namespace OMA.S_oeis_a267535

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 143 l c r = true ↔ (l = true → c = true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 2) i = true ↔ i ≠ -t ∧ i ≠ 1 - t := by
  induction t with
  | zero => intro i; simp only [state, eca_iff, decide_eq_true_eq]; omega
  | succ t ih => intro i; rw [state, eca_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : a (n + 3) = 100 * a (n + 2) + 11 := by
  unfold a
  rw [show 2 * (n + 3) + 1 = 2 * (n + 2) + 1 + 1 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.mul_sum, if_pos ((state_iff (n + 1) _).2 (by omega)),
    if_pos ((state_iff (n + 1) _).2 (by omega)), add_assoc,
    show 2 * (n + 3) - (2 * (n + 2) + 1) = 1 by omega,
    show 2 * (n + 3) - (2 * (n + 2) + 1 + 1) = 0 by omega]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk := Finset.mem_range.mp hk
  rw [show state (n + 3) (k - (n + 3 : ℕ)) = state (n + 2) (k - (n + 2 : ℕ)) from
    Bool.eq_iff_iff.2 (by rw [state_iff (n + 1), state_iff n]; omega),
    show 2 * (n + 3) - k = 2 * (n + 2) - k + 2 by omega, pow_add]
  split_ifs <;> ring

end OMA.S_oeis_a267535

open OMA.S_oeis_a267535 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267535.main := by
  have P : ∀ n, 3 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h1 : a (m + 4) = 100 * a (m + 3) + 11 := a_step (m + 1)
    have h2 := a_step m
    show (a (m + 4) : ℤ) = 101 * a (m + 3) - 100 * a (m + 2)
    omega
  refine ⟨P, ?_⟩
  have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 - 100 * X)) =
      B - C 101 * (B * X ^ 1) + C 100 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
  rw [e, show ((1 + 10 * X) * (1 - X + X ^ 2) : ℤ⟦X⟧) = 1 + C 9 * X ^ 1 - C 9 * X ^ 2 + C 10 * X ^ 3 by
    simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_one,
    coeff_mk]
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 110 by decide, show a 2 = 11001 by decide, show a 3 = 1100111 by decide]
  · split_ifs <;> first | omega | linarith [P n h]
