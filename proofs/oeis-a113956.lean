import OMAStatements.S_oeis_a113956
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a113956.main := by
  intro S c G hS _ hc hg n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  have t (i : ℕ) : coeff i (X * derivative ℚ G) = i * coeff i G := by
    cases i <;> simp [coeff_derivative, mul_comm]
  have hG : (-16*X + 112*X^2 - 128*X^3 - 240*X^4 - 64*X^5)*G = -8*X + 24*X^2 + 32*X^3 + (-8*X + 24*X^2 + 16*X^3)*S := by
    linear_combination ((-2 + 6*X + 4*X^2)-(2 + 2*X)*S)*(4*X*hg - G*(1-4*X)*(2*S - X*(2*X*c+1-S))*hc + G*(1-4*X)*(2+X)*hS) + (G*(1-4*X)*(2 + 2*X)^2 - 4*X*(2 + 2*X))*hS
  have h1 := congrArg (derivative ℚ) hS
  have h2 := congrArg (derivative ℚ) hG
  simp [e, Derivation.leibniz] at h1 h2
  simp only [map_ofNat] at h1 h2
  have key : 256*(X*derivative ℚ G) - 2560*(X*(X*derivative ℚ G)) + 6912*(X^2*(X*derivative ℚ G)) + 1280*(X^3*(X*derivative ℚ G)) - 14592*(X^4*(X*derivative ℚ G)) - 10752*(X^5*(X*derivative ℚ G)) - 2048*(X^6*(X*derivative ℚ G)) - 512*(X*G) + 2048*(X^2*G) + 3328*(X^3*G) - 10240*(X^4*G) - 11264*(X^5*G) - 3072*(X^6*G) = 256*X - 1024*X^2 - 512*X^3 - 512*X^4 := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 X_ne_zero) (fun h => by simpa [e] using congrArg (coeff 0) h : (1 - 4*X : ℚ⟦X⟧) ≠ 0)) (by
    linear_combination X*((-16*X + 112*X^2 - 160*X^3 - 128*X^4)*h2 - (-16 + 192*X - 384*X^2 - 448*X^3)*hG + (-8*X + 24*X^2 + 16*X^3)^2*(-((2)*derivative ℚ S + (0)*S)*hS + (1)*S*h1)))
  have h := congrArg (coeff (m+6)) key
  simp [e, coeff_C_mul, t, coeff_X_pow_mul'] at h ⊢
  linear_combination h/(256)
