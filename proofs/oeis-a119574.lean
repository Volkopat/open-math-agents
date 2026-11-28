import OMAStatements.S_oeis_a119574
import Mathlib

-- Problem: A119574, a(n) = binomial(2n,n)*(n+2)^2/(n+1) (statement from PR #18530 by @connoranderson).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: a(n) = Catalan(n)*(n+2)^2, so with the Catalan series K (K = 1 + X*K^2) and the Euler
-- operator theta = X*d/dX, the g.f. is theta^2 K + 4 theta K + 4 K. Take S = 1 - 2*X*K; then
-- S^2 = 1 - 4X, (theta K) S = X K^2 and (theta^2 K) S = X K^2 + 4 X K theta K + 2 X (theta K)^2,
-- and the claimed identity is a polynomial consequence of these relations.

namespace OMA.A119574Proof

open PowerSeries OMA.S_oeis_a119574

noncomputable def K : ℚ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

theorem coeff_K (n : ℕ) : coeff n K = (catalan n : ℚ) := by
  simp [K, coeff_map, catalanSeries_coeff]

theorem hK : K ^ 2 * X + 1 = K := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  rw [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h
  exact h

theorem coeff_theta (f : ℚ⟦X⟧) (n : ℕ) : coeff n (X * d⁄dX ℚ f) = n * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem a_eq (n : ℕ) : a n = (catalan n : ℚ) * ((n : ℚ) + 2) ^ 2 := by
  have h := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  have h' : (((2 * n).choose n : ℕ) : ℚ) = ((n : ℚ) + 1) * (catalan n : ℚ) := by
    rw [← h]; push_cast; ring
  unfold a
  rw [h']
  field_simp

theorem hG : PowerSeries.mk a =
    X * d⁄dX ℚ (X * d⁄dX ℚ K) + 4 * (X * d⁄dX ℚ K) + 4 * K := by
  ext n
  have h4 : ∀ f : ℚ⟦X⟧, coeff n (4 * f) = 4 * coeff n f := by
    intro f
    rw [show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm, coeff_C_mul]
  rw [coeff_mk, map_add, map_add, h4, h4]
  simp only [coeff_theta, coeff_K]
  rw [a_eq]
  ring

theorem hD1 : d⁄dX ℚ K = K * K + X * K * d⁄dX ℚ K + X * K * d⁄dX ℚ K := by
  have h := congrArg (d⁄dX ℚ) hK
  rw [sq] at h
  simp only [map_add, Derivation.leibniz, derivative_X, smul_eq_mul, derivative_one] at h
  linear_combination -h

theorem hD2 : d⁄dX ℚ (d⁄dX ℚ K) = 4 * K * d⁄dX ℚ K + 2 * X * (d⁄dX ℚ K) ^ 2 +
    2 * X * K * d⁄dX ℚ (d⁄dX ℚ K) := by
  have h := congrArg (d⁄dX ℚ) hD1
  simp only [map_add, Derivation.leibniz, derivative_X, smul_eq_mul] at h
  linear_combination h

end OMA.A119574Proof

open OMA.A119574Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a119574.main := by
  refine ⟨1 - 2 * X * K, by simp, by linear_combination (4 * X) * hK, ?_⟩
  obtain ⟨u, hu_def⟩ : ∃ u, u = X * d⁄dX ℚ K := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v, v = X * d⁄dX ℚ u := ⟨_, rfl⟩
  have G := hG
  rw [← hu_def, ← hv_def] at G
  have hDu : d⁄dX ℚ u = d⁄dX ℚ K + X * d⁄dX ℚ (d⁄dX ℚ K) := by
    rw [hu_def]
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul]
    ring
  have hu : u * (1 - 2 * X * K) = X * K ^ 2 := by
    rw [hu_def]
    linear_combination X * hD1
  have hv : v * (1 - 2 * X * K) = X * K ^ 2 + 4 * X * K * u + 2 * X * u ^ 2 := by
    rw [hv_def, hDu, hu_def]
    linear_combination X * hD1 + X ^ 2 * hD2
  rw [G]
  linear_combination (2 * X * (1 - 2 * X * K) ^ 2) * hv +
    (8 * X ^ 2 * K * (1 - 2 * X * K) + 4 * X ^ 2 * (u * (1 - 2 * X * K) + X * K ^ 2) +
      8 * X * (1 - 2 * X * K) ^ 2) * hu +
    (-14 * X + 36 * X ^ 2 + 36 * X ^ 2 * K - 36 * X ^ 3 * K ^ 2) * hK
