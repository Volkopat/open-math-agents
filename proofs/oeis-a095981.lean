import OMAStatements.S_oeis_a095981
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a095981.main := by
  intro S G hS h0 hG n hn
  have hSe : S = 2 * (X - 1) * X ^ 2 * G + (1 - 2 * X - X ^ 2 + X ^ 3) := by
    linear_combination (-1 : ℚ⟦X⟧) * hG
  have h1 := congrArg (PowerSeries.derivative ℚ) hS
  have hD : ∀ f g : ℚ⟦X⟧, PowerSeries.derivative ℚ (f * g) = f * PowerSeries.derivative ℚ g + g * PowerSeries.derivative ℚ f := by
    intro f g; rw [Derivation.leibniz]; simp [smul_eq_mul]
  have hX : PowerSeries.derivative ℚ (X : ℚ⟦X⟧) = 1 := by simp
  have hC : ∀ c : ℚ, PowerSeries.derivative ℚ (PowerSeries.C c : ℚ⟦X⟧) = 0 := fun c => by simp
  have hN : ∀ k : ℕ, PowerSeries.derivative ℚ ((k : ℕ) : ℚ⟦X⟧) = 0 := fun k => Derivation.map_natCast _ _
  have d2 : PowerSeries.derivative ℚ (2 : ℚ⟦X⟧) = 0 := by simpa using hN 2
  have d4 : PowerSeries.derivative ℚ (4 : ℚ⟦X⟧) = 0 := by simpa using hN 4
  have d6 : PowerSeries.derivative ℚ (6 : ℚ⟦X⟧) = 0 := by simpa using hN 6
  have d7 : PowerSeries.derivative ℚ (7 : ℚ⟦X⟧) = 0 := by simpa using hN 7
  have h2 : 2 * S * PowerSeries.derivative ℚ S =
      -4 + 4 * X + 18 * X ^ 2 - 28 * X ^ 3 + 10 * X ^ 4 + 6 * X ^ 5 := by
    have := h1
    simp only [hD, Derivation.leibniz_pow, map_add, map_sub, hX, Derivation.map_one_eq_zero, d2, d4, d6, d7,
      smul_eq_mul, nsmul_eq_mul] at this
    norm_num at this
    linear_combination this
  have hP2 : 2 * (1 - 4 * X + 2 * X ^ 2 + 6 * X ^ 3 - 7 * X ^ 4 + 2 * X ^ 5 + X ^ 6 : ℚ⟦X⟧) *
      PowerSeries.derivative ℚ S =
      (-4 + 4 * X + 18 * X ^ 2 - 28 * X ^ 3 + 10 * X ^ 4 + 6 * X ^ 5) * S := by
    linear_combination S * h2 - 2 * PowerSeries.derivative ℚ S * hS
  have hS' : PowerSeries.derivative ℚ S = 2 * (3 * X ^ 2 - 2 * X) * G + 2 * (X - 1) * X ^ 2 *
      PowerSeries.derivative ℚ G + (-2 - 2 * X + 3 * X ^ 2) := by
    rw [hSe]
    simp only [hD, Derivation.leibniz_pow, map_add, map_sub, hX, Derivation.map_one_eq_zero, d2, d4, d6, d7,
      smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  rw [hS', hSe] at hP2
  have hR : (C (4:ℚ) * (X ^ 9 * PowerSeries.derivative ℚ G) + C (4:ℚ) * (X ^ 8 * PowerSeries.derivative ℚ G)
      - C (36:ℚ) * (X ^ 7 * PowerSeries.derivative ℚ G) + C (52:ℚ) * (X ^ 6 * PowerSeries.derivative ℚ G)
      - C (16:ℚ) * (X ^ 5 * PowerSeries.derivative ℚ G) - C (24:ℚ) * (X ^ 4 * PowerSeries.derivative ℚ G)
      + C (20:ℚ) * (X ^ 3 * PowerSeries.derivative ℚ G) - C (4:ℚ) * (X ^ 2 * PowerSeries.derivative ℚ G))
      + (C (8:ℚ) * (X ^ 7 * G) - C (24:ℚ) * (X ^ 6 * G) + C (36:ℚ) * (X ^ 5 * G)
      + C (4:ℚ) * (X ^ 4 * G) - C (48:ℚ) * (X ^ 3 * G) + C (36:ℚ) * (X ^ 2 * G) - C (8:ℚ) * (X ^ 1 * G))
      + (C (4:ℚ) * X ^ 7 - C (4:ℚ) * X ^ 6 + C (24:ℚ) * X ^ 5 - C (36:ℚ) * X ^ 4 + C (16:ℚ) * X ^ 3) = 0 := by
    simp only [map_ofNat]
    linear_combination hP2
  have hc := congrArg (PowerSeries.coeff (n + 1)) hR
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 7 + k + 1 = k + 8 by omega] at hc
  have hk : ∀ j : ℕ, j ≤ k + 8 → j = j := fun _ _ => rfl
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', PowerSeries.coeff_derivative,
    coeff_X_pow, coeff_zero_eq_constantCoeff, map_zero] at hc
  rcases k with _ | k
  · simp at hc ⊢
    push_cast at hc ⊢
    linear_combination (-1/4 : ℚ) * hc
  · simp at hc ⊢
    push_cast at hc ⊢
    simp only [show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega,
      show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega,
      show k + 8 - 6 = k + 2 by omega, show 7 + (k + 1) = k + 8 by omega,
      show 7 + k = k + 7 by omega, show k + 1 + 1 = k + 2 by omega, show k + 2 + 1 = k + 3 by omega,
      show k + 3 + 1 = k + 4 by omega, show k + 4 + 1 = k + 5 by omega, show k + 5 + 1 = k + 6 by omega,
      show k + 6 + 1 = k + 7 by omega, show k + 7 + 1 = k + 8 by omega] at hc ⊢
    linear_combination (-1/4 : ℚ) * hc
