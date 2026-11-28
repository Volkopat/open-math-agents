import OMAStatements.S_oeis_a065919

-- Problem: A065919: Bessel polynomial y_n(4).
-- Upstream: formal-conjectures statements/oeis-a065919.lean:0 (declaration OMA.S_oeis_a065919.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: write P, Q = 1 + X*F and R for the three series. Q has constant term 1, so P * Q⁻¹ = R
-- gives P = R * Q. Compare the coefficients of x^2: with a(0), a(1), a(2) = 1, 5, 61 and
-- A059304(0), A059304(1), A059304(2) = 1, 4, 24 the left side is 61/2, the right side is
-- 1 * (5/2) + 4 * 1 + 12 * 1 = 37/2.

namespace S08A065919

open OMA.S_oeis_a065919

theorem ha0 : a 0 = 1 := by decide

theorem ha1 : a 1 = 5 := by decide

theorem ha2 : a 2 = 61 := by decide

theorem hb0 : A059304 0 = 1 := by decide

theorem hb1 : A059304 1 = 4 := by decide

theorem hb2 : A059304 2 = 24 := by decide

theorem cc (F : PowerSeries ℚ) : PowerSeries.constantCoeff (1 + PowerSeries.X * F) ≠ 0 := by
  rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_X, zero_mul, add_zero]
  exact one_ne_zero

theorem key (P Q R : PowerSeries ℚ) (hQ : PowerSeries.constantCoeff Q ≠ 0) (h : P * Q⁻¹ = R) :
    P = R * Q := by
  rw [← h, mul_assoc, PowerSeries.inv_mul_cancel Q hQ, mul_one]

theorem coeff2 (R Q : PowerSeries ℚ) : PowerSeries.coeff 2 (R * Q) =
    PowerSeries.coeff 0 R * PowerSeries.coeff 2 Q +
      (PowerSeries.coeff 1 R * PowerSeries.coeff 1 Q +
        PowerSeries.coeff 2 R * PowerSeries.coeff 0 Q) := by
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.sum_antidiagonal_succ]

theorem cG (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (1 + PowerSeries.X * F) = PowerSeries.coeff n F := by
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_succ_X_mul,
    if_neg (show n + 1 ≠ 0 by omega), zero_add]

theorem cG0 (F : PowerSeries ℚ) : PowerSeries.coeff 0 (1 + PowerSeries.X * F) = 1 := by
  rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_zero_X_mul, if_pos rfl, add_zero]

theorem cG1 (F : PowerSeries ℚ) :
    PowerSeries.coeff 1 (1 + PowerSeries.X * F) = PowerSeries.coeff 0 F :=
  cG F 0

theorem cG2 (F : PowerSeries ℚ) :
    PowerSeries.coeff 2 (1 + PowerSeries.X * F) = PowerSeries.coeff 1 F :=
  cG F 1

end S08A065919

open OMA.S_oeis_a065919 S08A065919 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a065919.main) := by
  intro h
  obtain ⟨P, hP⟩ : ∃ P : PowerSeries ℚ,
      P = PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : PowerSeries ℚ,
      F = PowerSeries.mk (fun n => (a n : ℚ) / ((n + 1).factorial : ℚ)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : PowerSeries ℚ,
      R = PowerSeries.mk (fun n => (A059304 n : ℚ) / (n.factorial : ℚ)) := ⟨_, rfl⟩
  rw [← hP, ← hF, ← hR] at h
  have h2 := key P (1 + PowerSeries.X * F) R (cc F) h
  have c : PowerSeries.coeff 2 P = PowerSeries.coeff 2 (R * (1 + PowerSeries.X * F)) := by
    rw [h2]
  rw [coeff2, cG0, cG1, cG2, hP, hR, hF] at c
  simp only [PowerSeries.coeff_mk] at c
  rw [ha0, ha1, ha2, hb0, hb1, hb2] at c
  norm_num at c
