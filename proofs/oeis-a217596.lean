import OMAStatements.S_oeis_a217596
import Mathlib

namespace OMA.A217596Proof

open PowerSeries

theorem d_sq (f : ℚ⟦X⟧) : d⁄dX ℚ (f ^ 2) = 2 * f * d⁄dX ℚ f := by
  rw [Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem d_cube (f : ℚ⟦X⟧) : d⁄dX ℚ (f ^ 3) = 3 * f ^ 2 * d⁄dX ℚ f := by
  rw [Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- The g.f. satisfies a second-order linear differential equation. -/
theorem ode (R G : ℚ⟦X⟧) (h0 : coeff 0 R = 0) (hR : R - R ^ 2 - R ^ 3 = X) (hGR : G * R = X) :
    (25 - 125 * X - 69 * X ^ 2 + 81 * X ^ 3) * d⁄dX ℚ (d⁄dX ℚ G)
      - (40 + 168 * X) * d⁄dX ℚ G + (90 + 18 * X) * G = 30 + 6 * X := by
  have hRne : R ≠ 0 := by
    intro hz
    rw [hz] at hR
    have := congrArg (coeff 1) hR
    simp at this
  have hG : G = 1 - R - R ^ 2 := by
    have h : (G - (1 - R - R ^ 2)) * R = 0 := by linear_combination hGR - hR
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hRne)
  set R1 := d⁄dX ℚ R with hR1
  set R2 := d⁄dX ℚ R1 with hR2
  have hd := congrArg (d⁄dX ℚ) hR
  simp only [map_sub, d_sq, d_cube, derivative_X] at hd
  -- hd : R1 - 2 R R1 - 3 R^2 R1 = 1
  have h1 : R1 * (1 - 2 * R - 3 * R ^ 2) = 1 := by linear_combination hd
  have hd2 := congrArg (d⁄dX ℚ) h1
  rw [Derivation.leibniz] at hd2
  simp only [map_sub, smul_eq_mul, Derivation.map_one_eq_zero] at hd2
  have h2' : d⁄dX ℚ (2 * R) = 2 * R1 := by
    rw [show (2 * R : ℚ⟦X⟧) = R + R by ring, map_add]; ring
  have h3' : d⁄dX ℚ (3 * R ^ 2) = 6 * R * R1 := by
    rw [show (3 * R ^ 2 : ℚ⟦X⟧) = R ^ 2 + R ^ 2 + R ^ 2 by ring, map_add, map_add, d_sq]; ring
  rw [h2', h3'] at hd2
  have h2 : R2 * (1 - 2 * R - 3 * R ^ 2) + R1 ^ 2 * (-2 - 6 * R) = 0 := by
    linear_combination hd2
  have hdG : d⁄dX ℚ G = -(1 + 2 * R) * R1 := by
    rw [hG, map_sub, map_sub, d_sq, Derivation.map_one_eq_zero]; ring
  have hddG : d⁄dX ℚ (d⁄dX ℚ G) = -2 * R1 ^ 2 - (1 + 2 * R) * R2 := by
    rw [hdG, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_neg, map_add,
      Derivation.map_one_eq_zero, h2']
    ring
  have key : (1 - 2 * R - 3 * R ^ 2) ^ 3 *
      ((25 - 125 * (R - R ^ 2 - R ^ 3) - 69 * (R - R ^ 2 - R ^ 3) ^ 2
          + 81 * (R - R ^ 2 - R ^ 3) ^ 3) * d⁄dX ℚ (d⁄dX ℚ G)
        - (40 + 168 * (R - R ^ 2 - R ^ 3)) * d⁄dX ℚ G
        + (90 + 18 * (R - R ^ 2 - R ^ 3)) * G - (30 + 6 * (R - R ^ 2 - R ^ 3))) = 0 := by
    linear_combination
      (-2 * (25 - 125 * (R - R ^ 2 - R ^ 3) - 69 * (R - R ^ 2 - R ^ 3) ^ 2
          + 81 * (R - R ^ 2 - R ^ 3) ^ 3) * (1 - 2 * R - 3 * R ^ 2)
          * ((1 - 2 * R - 3 * R ^ 2) * R1 + 1)
        + (1 + 2 * R) * (25 - 125 * (R - R ^ 2 - R ^ 3) - 69 * (R - R ^ 2 - R ^ 3) ^ 2
          + 81 * (R - R ^ 2 - R ^ 3) ^ 3) * (-2 - 6 * R)
          * ((1 - 2 * R - 3 * R ^ 2) * R1 + 1)
        + (40 + 168 * (R - R ^ 2 - R ^ 3)) * (1 + 2 * R) * (1 - 2 * R - 3 * R ^ 2) ^ 2) * h1
      + (-(1 + 2 * R) * (25 - 125 * (R - R ^ 2 - R ^ 3) - 69 * (R - R ^ 2 - R ^ 3) ^ 2
          + 81 * (R - R ^ 2 - R ^ 3) ^ 3) * (1 - 2 * R - 3 * R ^ 2) ^ 2) * h2
      + ((1 - 2 * R - 3 * R ^ 2) ^ 3 * (25 - 125 * (R - R ^ 2 - R ^ 3)
          - 69 * (R - R ^ 2 - R ^ 3) ^ 2 + 81 * (R - R ^ 2 - R ^ 3) ^ 3)) * hddG
      - ((1 - 2 * R - 3 * R ^ 2) ^ 3 * (40 + 168 * (R - R ^ 2 - R ^ 3))) * hdG
      + ((1 - 2 * R - 3 * R ^ 2) ^ 3 * (90 + 18 * (R - R ^ 2 - R ^ 3))) * hG
  rw [hR] at key
  have hne : (1 - 2 * R - 3 * R ^ 2) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    intro hz
    have := congrArg (coeff 0) hz
    simp only [map_sub, coeff_one, if_true, map_zero] at this
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm,
      show (3 : ℚ⟦X⟧) = C 3 from (map_ofNat C 3).symm] at this
    have h0' : constantCoeff R = 0 := by rw [← coeff_zero_eq_constantCoeff_apply]; exact h0
    simp [coeff_C_mul, h0', pow_two] at this
  have := (mul_eq_zero.1 key).resolve_left hne
  linear_combination this

end OMA.A217596Proof

open OMA.A217596Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a217596.main := by
  intro R G h0 hR hGR n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h := congrArg (coeff (k + 2)) (ode R G h0 hR hGR)
  have hL : (25 - 125 * X - 69 * X ^ 2 + 81 * X ^ 3) * d⁄dX ℚ (d⁄dX ℚ G)
      - (40 + 168 * X) * d⁄dX ℚ G + (90 + 18 * X) * G =
      C (25 : ℚ) * d⁄dX ℚ (d⁄dX ℚ G) - C (125 : ℚ) * (d⁄dX ℚ (d⁄dX ℚ G) * X ^ 1)
        - C (69 : ℚ) * (d⁄dX ℚ (d⁄dX ℚ G) * X ^ 2) + C (81 : ℚ) * (d⁄dX ℚ (d⁄dX ℚ G) * X ^ 3)
        - C (40 : ℚ) * d⁄dX ℚ G - C (168 : ℚ) * (d⁄dX ℚ G * X ^ 1)
        + C (90 : ℚ) * G + C (18 : ℚ) * (G * X ^ 1) := by
    simp only [map_ofNat]; ring
  have hRhs : (30 + 6 * X : ℚ⟦X⟧) = C (30 : ℚ) + C (6 : ℚ) * X ^ 1 := by
    simp only [map_ofNat]; ring
  rw [hL, hRhs] at h
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_derivative, coeff_C,
    if_pos (show 1 ≤ k + 2 by omega), if_pos (show 2 ≤ k + 2 by omega),
    show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega,
    if_neg (show k + 2 ≠ 0 by omega), if_neg (show k + 1 ≠ 0 by omega)] at h
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp at h
    push_cast at h ⊢
    linear_combination h
  · simp only [if_pos (show 3 ≤ k + 2 by omega), show k + 2 - 3 = k - 1 by omega,
      show k - 1 + 1 = k by omega] at h
    have hc : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub hk]; simp
    rw [hc] at h
    push_cast at h ⊢
    linear_combination h
