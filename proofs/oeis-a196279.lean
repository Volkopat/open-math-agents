import OMAStatements.S_oeis_a196279

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: 7(n+10) = 7n + 70 has the same last digit and leading part larger by 7, so
-- a(n+10) = a(n) + 1; this gives the recurrence. The denominator polynomial equals
-- (1 - X)(1 - X^10) = 1 - X - X^10 + X^11, so the g.f. identity is a coefficient check:
-- coefficients n >= 11 vanish by the recurrence, n <= 10 are computed.

namespace OMA.A196279Proof

open OMA.S_oeis_a196279 PowerSeries

lemma step (n : ℕ) : a (n + 10) = a n + 1 := by
  unfold a
  have h1 : 7 * (n + 10) / 10 = 7 * n / 10 + 7 := by omega
  have h2 : 7 * (n + 10) % 10 = 7 * n % 10 := by omega
  rw [h1, h2, Nat.cast_add, Nat.cast_ofNat]
  generalize ((7 * n / 10 : ℕ) : ℤ) = x
  generalize ((7 * n % 10 : ℕ) : ℤ) = r
  rw [show x + 7 - 2 * r = (x - 2 * r) + 1 * 7 by ring, Int.add_mul_ediv_right _ _ (by norm_num)]

lemma rec' (m : ℕ) : a (m + 11) = a (m + 10) + a (m + 1) - a m := by
  rw [show m + 11 = (m + 1) + 10 by ring, step, step]; ring

end OMA.A196279Proof

open OMA.S_oeis_a196279 OMA.A196279Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a196279.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    rw [show m + 11 - 1 = m + 10 by omega, show m + 11 - 10 = m + 1 by omega,
      show m + 11 - 11 = m by omega, rec']
  · have hprod : ((1 + X) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1) *
        (X - 1) ^ 2 : PowerSeries ℤ) = 1 - X ^ 1 - X ^ 10 + X ^ 11 := by ring
    have hr : (X * (-2 + X - 2 * X ^ 3 + X ^ 4 - 2 * X ^ 6 + X ^ 7 + X ^ 9 + X ^ 2 + X ^ 5 + X ^ 8) :
        PowerSeries ℤ) = C (-2) * X ^ 1 + C 1 * X ^ 2 + C 1 * X ^ 3 + C (-2) * X ^ 4
          + C 1 * X ^ 5 + C 1 * X ^ 6 + C (-2) * X ^ 7 + C 1 * X ^ 8 + C 1 * X ^ 9
          + C 1 * X ^ 10 := by
      simp only [map_neg, map_one, map_ofNat]; ring
    rw [hprod, hr]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mk, coeff_mul_X_pow',
      coeff_C_mul_X_pow, coeff_C]
    rcases lt_or_ge n 11 with h | h
    · interval_cases n <;> simp [a]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
      simp only [show 1 ≤ m + 11 by omega,
        show 2 ≤ m + 11 by omega,
        show 3 ≤ m + 11 by omega,
        show 4 ≤ m + 11 by omega,
        show 5 ≤ m + 11 by omega,
        show 6 ≤ m + 11 by omega,
        show 7 ≤ m + 11 by omega,
        show 8 ≤ m + 11 by omega,
        show 9 ≤ m + 11 by omega,
        show 10 ≤ m + 11 by omega,
        show 11 ≤ m + 11 by omega,
        show ¬ (m + 11 - 1 = 0) by omega,
        show ¬ (m + 11 - 2 = 0) by omega,
        show ¬ (m + 11 - 3 = 0) by omega,
        show ¬ (m + 11 - 4 = 0) by omega,
        show ¬ (m + 11 - 5 = 0) by omega,
        show ¬ (m + 11 - 6 = 0) by omega,
        show ¬ (m + 11 - 7 = 0) by omega,
        show ¬ (m + 11 - 8 = 0) by omega,
        show ¬ (m + 11 - 9 = 0) by omega,
        show ¬ (m + 11 - 10 = 0) by omega, if_true, if_false]
      rw [show m + 11 - 1 = m + 10 by omega, show m + 11 - 10 = m + 1 by omega,
        show m + 11 - 11 = m by omega, rec']
      ring
