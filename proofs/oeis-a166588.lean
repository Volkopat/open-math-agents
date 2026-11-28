import OMAStatements.S_oeis_a166588

/- Successive differences isolate the Catalan coefficients at odd indices.
   The Catalan convolution then gives the claimed identity. -/

open OMA.S_oeis_a166588

namespace OMA.P_a166588

theorem b_odd (j : ℕ) : b (2 * j + 1) = catalan j := by
  unfold b
  rw [if_neg (by omega), if_pos (by omega), show (2 * j + 1 - 1) / 2 = j by omega]

theorem b_even (j : ℕ) : b (2 * j + 2) = 0 := by
  unfold b
  rw [if_neg (by omega), if_neg (by omega)]

theorem a_succ (n : ℕ) : a (n + 1) = a n + b (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]

theorem cat_rec (j : ℕ) :
    ((j : ℤ) + 2) * (catalan (j + 1) : ℤ) = 2 * (2 * (j : ℤ) + 1) * (catalan j : ℤ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (j + 1)
  have h2 := succ_mul_catalan_eq_centralBinom j
  have h3 := Nat.succ_mul_centralBinom_succ j
  have key : (j + 1) * ((j + 2) * catalan (j + 1)) = (j + 1) * (2 * (2 * j + 1) * catalan j) := by
    rw [h1, h3, ← h2]; ring
  have := Nat.eq_of_mul_eq_mul_left (by omega) key
  exact_mod_cast this

end OMA.P_a166588

open OMA.P_a166588

theorem OMA.solution : type_of% @OMA.S_oeis_a166588.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m - 1 = m + 2 by omega, show 3 + m - 2 = m + 1 by omega,
    show 3 + m - 3 = m by omega, show 3 + m = m + 2 + 1 by omega, a_succ (m + 2), a_succ m]
  push_cast
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j + 2 + 1 = 2 * (j + 1) + 1 by omega, show j + j + 1 = 2 * j + 1 by omega,
      b_odd, b_odd]
    push_cast
    linear_combination (-2 : ℤ) * cat_rec j
  · rw [show 2 * j + 1 + 2 + 1 = 2 * (j + 1) + 2 by omega,
      show 2 * j + 1 + 1 = 2 * j + 2 by omega, b_even, b_even]
    ring

