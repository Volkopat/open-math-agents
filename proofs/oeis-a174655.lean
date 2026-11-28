import OMAStatements.S_oeis_a174655

/-! Credit: @unserus

The tail of A049486 has the closed form 2 t(m) = (-1)^(m+1) + 4m^2 + 16m + 21 (induction on
its recurrence); summing gives the closed form for a(n), and the generating function follows
coefficientwise from the closed form, with the first seven coefficients computed directly. -/

namespace OMAA174655Helpers
open OMA.S_oeis_a174655 PowerSeries

theorem tail_closed : ∀ m : ℕ, 2 * tail m = (-1 : ℤ) ^ (m + 1) + 4 * (m : ℤ) ^ 2 + 16 * m + 21
  | 0 => by simp [tail]
  | 1 => by norm_num [tail]
  | 2 => by norm_num [tail]
  | 3 => by norm_num [tail]
  | n + 4 => by
    have h0 := tail_closed n
    have h1 := tail_closed (n + 1)
    have h3 := tail_closed (n + 3)
    rw [tail]
    push_cast at h0 h1 h3 ⊢
    linear_combination 2 * h3 - 2 * h1 + h0

theorem a_closed (n : ℕ) :
    12 * a (n + 2) = 3 * (-9 + (-1 : ℤ) ^ (n + 2)) + 34 * ((n + 2 : ℕ) : ℤ)
      - 12 * ((n + 2 : ℕ) : ℤ) ^ 2 + 8 * ((n + 2 : ℕ) : ℤ) ^ 3 := by
  induction n with
  | zero => norm_num [a, b, Finset.sum_range_succ]
  | succ n ih =>
    have hs : a (n + 1 + 2) = a (n + 2) + tail n := by
      simp only [a]
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, Finset.sum_range_succ]
      rfl
    have ht := tail_closed n
    rw [hs]
    push_cast at ih ht ⊢
    linear_combination ih + 6 * ht

theorem a_closed' (n : ℕ) (hn : 1 < n) :
    12 * a n = 3 * (-9 + (-1 : ℤ) ^ n) + 34 * (n : ℤ) - 12 * (n : ℤ) ^ 2 + 8 * (n : ℤ) ^ 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact a_closed m

theorem small : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 15 ∧ a 4 = 36 ∧ a 5 = 70 ∧ a 6 = 123 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end OMAA174655Helpers

open OMAA174655Helpers OMA.S_oeis_a174655 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a174655.main := by
  refine ⟨fun n hn => a_closed' n hn, ?_⟩
  have hL : ((X - 1) ^ 4 * (X + 1) * mk a : ℤ⟦X⟧) =
      X ^ 5 * mk a - C (3 : ℤ) * (X ^ 4 * mk a) + C (2 : ℤ) * (X ^ 3 * mk a)
        + C (2 : ℤ) * (X ^ 2 * mk a) - C (3 : ℤ) * (X ^ 1 * mk a) + mk a := by
    simp only [map_ofNat]; ring
  have hR : (X * (X ^ 5 - X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 + 2 * X + 1) : ℤ⟦X⟧) =
      X ^ 6 - X ^ 5 + C (3 : ℤ) * X ^ 4 + C (2 : ℤ) * X ^ 3 + C (2 : ℤ) * X ^ 2 + X ^ 1 := by
    simp only [map_ofNat]; ring
  rw [hL, hR]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge k 7 with hk | hk
  · obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := small
    interval_cases k <;> simp [s0, s1, s2, s3, s4, s5, s6]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    rw [if_pos (by omega : 5 ≤ m + 7), if_pos (by omega : 4 ≤ m + 7), if_pos (by omega : 3 ≤ m + 7),
      if_pos (by omega : 2 ≤ m + 7), if_pos (by omega : 1 ≤ m + 7),
      if_neg (by omega : ¬ m + 7 = 6), if_neg (by omega : ¬ m + 7 = 5),
      if_neg (by omega : ¬ m + 7 = 4), if_neg (by omega : ¬ m + 7 = 3),
      if_neg (by omega : ¬ m + 7 = 2), if_neg (by omega : ¬ m + 7 = 1),
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 1 = m + 6 by omega]
    have e5 := a_closed' (m + 2) (by omega)
    have e4 := a_closed' (m + 3) (by omega)
    have e3 := a_closed' (m + 4) (by omega)
    have e2 := a_closed' (m + 5) (by omega)
    have e1 := a_closed' (m + 6) (by omega)
    have e0 := a_closed' (m + 7) (by omega)
    push_cast at e0 e1 e2 e3 e4 e5
    generalize a (m + 2) = x2 at *
    generalize a (m + 3) = x3 at *
    generalize a (m + 4) = x4 at *
    generalize a (m + 5) = x5 at *
    generalize a (m + 6) = x6 at *
    generalize a (m + 7) = x7 at *
    have h12 : 12 * (x2 - 3 * x3 + 2 * x4 + 2 * x5 - 3 * x6 + x7) = 0 := by
      linear_combination e5 - 3 * e4 + 2 * e3 + 2 * e2 - 3 * e1 + e0
    have h0 : x2 - 3 * x3 + 2 * x4 + 2 * x5 - 3 * x6 + x7 = 0 :=
      (mul_eq_zero.mp h12).resolve_left (by norm_num)
    linear_combination h0
