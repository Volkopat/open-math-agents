import OMAStatements.S_oeis_a187430

-- Problem: A187430: Number of nonnegative walks of n steps with step sizes 1 and 2, starting and ending at 0.
-- Upstream: formal-conjectures statements/oeis-a187430.lean:0 (declaration OMA.S_oeis_a187430.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let y = -x/(1-x)^2 and H = F(y). Substituting y in the equation of F gives
H*(1 - H^2)^2 = y*(1 + H^3)^2, that is H*(1 - H^2)^2*(1 - x)^2 + x*(1 + H^3)^2 = 0. The series K = 1 - C
satisfies the same equation (a polynomial consequence of C = 1 + x*C^2), and both have constant term 0.
The difference of the two equations is (H - K) times a series with constant term 1, so H = K. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a187430.main := by
  intro F C hF0 hF hC
  obtain ⟨a, had⟩ : ∃ a : PowerSeries ℚ, a = -(PowerSeries.X * ((1 - PowerSeries.X : PowerSeries ℚ)⁻¹) ^ 2) :=
    ⟨_, rfl⟩
  rw [← had]
  have ha0 : PowerSeries.constantCoeff a = 0 := by
    rw [had]
    simp
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha0
  have hinv : (1 - PowerSeries.X : PowerSeries ℚ) * (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  have hay : a * (1 - PowerSeries.X) ^ 2 = -PowerSeries.X := by
    rw [had]
    linear_combination (-(PowerSeries.X) * ((1 - PowerSeries.X : PowerSeries ℚ) * (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ + 1)) * hinv
  have hF0' : PowerSeries.constantCoeff F = 0 := by simpa using hF0
  obtain ⟨H, hHd⟩ : ∃ H : PowerSeries ℚ, H = PowerSeries.subst a F := ⟨_, rfl⟩
  rw [← hHd]
  have hH : H * (1 - H ^ 2) ^ 2 = a * (1 + H ^ 3) ^ 2 := by
    have h := congrArg (PowerSeries.substAlgHom ha) hF
    simp only [map_mul, map_sub, map_add, map_pow, map_one, PowerSeries.substAlgHom_X,
      PowerSeries.coe_substAlgHom] at h
    rw [hHd]
    exact h
  have hH0 : PowerSeries.constantCoeff H = 0 := by
    rw [hHd]
    exact PowerSeries.constantCoeff_subst_eq_zero ha0 F hF0'
  have hC0 : PowerSeries.constantCoeff C = 1 := by
    have h := congrArg PowerSeries.constantCoeff hC
    simpa using h
  have hK : (1 - C) * (1 - (1 - C) ^ 2) ^ 2 * (1 - PowerSeries.X) ^ 2 +
      PowerSeries.X * (1 + (1 - C) ^ 3) ^ 2 = 0 := by
    have h5 : PowerSeries.X ^ 5 * ((1 - C) * (1 - (1 - C) ^ 2) ^ 2 * (1 - PowerSeries.X) ^ 2 +
        PowerSeries.X * (1 + (1 - C) ^ 3) ^ 2) = 0 := by
      linear_combination (-(4 * PowerSeries.X ^ 5 * C ^ 2 - 4 * PowerSeries.X ^ 5 * C ^ 3 + PowerSeries.X ^ 5 * C ^ 4 +
        4 * PowerSeries.X ^ 6 - 8 * PowerSeries.X ^ 6 * C + 5 * PowerSeries.X ^ 6 * C ^ 2 - PowerSeries.X ^ 6 * C ^ 3)) * hC
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h (pow_ne_zero 5 PowerSeries.X_ne_zero)
    · exact h
  have hH2 : H * (1 - H ^ 2) ^ 2 * (1 - PowerSeries.X) ^ 2 + PowerSeries.X * (1 + H ^ 3) ^ 2 = 0 := by
    linear_combination (1 - PowerSeries.X) ^ 2 * hH + (1 + H ^ 3) ^ 2 * hay
  have hdiff : (H - (1 - C)) *
      ((1 - PowerSeries.X) ^ 2 * (1 - 2 * (H ^ 2 + H * (1 - C) + (1 - C) ^ 2) +
          (H ^ 4 + H ^ 3 * (1 - C) + H ^ 2 * (1 - C) ^ 2 + H * (1 - C) ^ 3 + (1 - C) ^ 4)) +
        PowerSeries.X * (2 * (H ^ 2 + H * (1 - C) + (1 - C) ^ 2) +
          (H ^ 5 + H ^ 4 * (1 - C) + H ^ 3 * (1 - C) ^ 2 + H ^ 2 * (1 - C) ^ 3 + H * (1 - C) ^ 4 + (1 - C) ^ 5))) = 0 := by
    linear_combination hH2 - hK
  have hQ : ((1 - PowerSeries.X) ^ 2 * (1 - 2 * (H ^ 2 + H * (1 - C) + (1 - C) ^ 2) +
          (H ^ 4 + H ^ 3 * (1 - C) + H ^ 2 * (1 - C) ^ 2 + H * (1 - C) ^ 3 + (1 - C) ^ 4)) +
        PowerSeries.X * (2 * (H ^ 2 + H * (1 - C) + (1 - C) ^ 2) +
          (H ^ 5 + H ^ 4 * (1 - C) + H ^ 3 * (1 - C) ^ 2 + H ^ 2 * (1 - C) ^ 3 + H * (1 - C) ^ 4 + (1 - C) ^ 5))) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hH0, hC0] at h'
  have hHK : H = 1 - C := by
    rcases mul_eq_zero.mp hdiff with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hQ
  rw [hHK]
  ring
