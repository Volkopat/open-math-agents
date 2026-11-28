import OMAStatements.S_oeis_a250917

-- Problem: A250917: Expansion of e.g.f. exp( x*C(x)^3 ) where C(x) = (1 - sqrt(1-4*x))/(2*x) is the g.f. of the Catalan numbers, A000108.
-- Upstream: formal-conjectures statements/oeis-a250917.lean:0 (declaration OMA.S_oeis_a250917.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A250917Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem key (G S c U W : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hU : U = X * (c * c * c))
    (hG : G = (PowerSeries.exp ℚ).subst U)
    (hW : W = S * G) :
    (X ^ 8 - 4 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))))) + (2 * X ^ 5 - 11 * X ^ 6 + 27 * X ^ 7 - 69 * X ^ 8 - 36 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (-35 * X ^ 5 + 74 * X ^ 6 - 237 * X ^ 7 - 528 * X ^ 8 + 24 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-66 * X ^ 5 + 195 * X ^ 6 - 2250 * X ^ 7 + 228 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (657 * X ^ 5 - 2928 * X ^ 6 + 504 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-708 * X ^ 5 + 216 * X ^ 6) * derivative ℚ G =
      0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d56 : derivative ℚ (56 : ℚ⟦X⟧) = 0 := dnum 56
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d88 : derivative ℚ (88 : ℚ⟦X⟧) = 0 := dnum 88
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d120 : derivative ℚ (120 : ℚ⟦X⟧) = 0 := dnum 120
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d240 : derivative ℚ (240 : ℚ⟦X⟧) = 0 := dnum 240
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d480 : derivative ℚ (480 : ℚ⟦X⟧) = 0 := dnum 480
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d1536 : derivative ℚ (1536 : ℚ⟦X⟧) = 0 := dnum 1536
  have dd2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have dd4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hU0 : constantCoeff U = 0 := by
    rw [hU]
    simp
  have hsub : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  have dG : derivative ℚ G = G * derivative ℚ U := by
    rw [hG, derivative_subst hsub, derivative_exp]
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, dd4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have dS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have rS : 2 * ((1 - 4 * X) * derivative ℚ S) = -4 * S := by
    linear_combination S * dS - 2 * derivative ℚ S * hS
  have hLc : derivative ℚ (2 * X * c) = 2 * c + 2 * X * derivative ℚ c := by
    simp [Derivation.leibniz, dd2]
    ring
  have hRc : derivative ℚ (1 - S) = -derivative ℚ S := by
    simp
  have dc : 2 * c + 2 * X * derivative ℚ c = -derivative ℚ S := by rw [← hLc, hc, hRc]
  have dU : derivative ℚ U = c ^ 3 + 3 * X * c ^ 2 * derivative ℚ c := by
    rw [hU]
    simp [Derivation.leibniz]
    ring
  have dW : derivative ℚ W = derivative ℚ S * G + S * derivative ℚ G := by
    rw [hW]
    simp [Derivation.leibniz]
    ring
  have k2 : 4 * X ^ 2 * c ^ 2 = 2 - 4 * X - 2 * S := by
    linear_combination (2 * X * c + 1 - S) * hc + hS
  have k3 : 8 * X ^ 3 * c ^ 3 = 4 - 12 * X - (4 - 4 * X) * S := by
    linear_combination (4 * X ^ 2 * c ^ 2 + 2 * X * c * (1 - S) + (1 - S) ^ 2) * hc + (3 - S) * hS
  have r0_1 : (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G =
      (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * G + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * W := by
    linear_combination (16 * X ^ 3 - 64 * X ^ 4) * dG +
      G * ((16 * X ^ 3 * (1 - 4 * X)) * dU - 4 * (1 - 4 * X) * k3 + 24 * X ^ 3 * (1 - 4 * X) * c ^ 2 * dc -
        12 * X ^ 3 * c ^ 2 * rS + 12 * X * S * k2 - 24 * X * hS) - (16 - 56 * X + 16 * X ^ 2) * hW
  have hLr0_2 : derivative ℚ ((16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ G + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, d16, d64]
    ring
  have hRr0_2 : derivative ℚ ((-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * G + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * W) =
      (88 - 192 * X) * G + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ G + (-56 + 32 * X) * W + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ W := by
    simp [Derivation.leibniz, d16, d56, d88, d96]
    ring
  have r0_2 : (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ G + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ G) =
      (88 - 192 * X) * G + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ G + (-56 + 32 * X) * W + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ W := by
    rw [← hLr0_2, ← hRr0_2, r0_1]
  have r0_2p : (48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) =
      (88 - 192 * X : ℚ⟦X⟧) * G + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ G + (-56 + 32 * X : ℚ⟦X⟧) * W + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ W := by linear_combination r0_2
  have hLr0_3 : derivative ℚ ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) =
      (96 * X - 768 * X ^ 2) * derivative ℚ G + 2 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ G) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d16, d48, d64, d256]
    ring
  have hRr0_3 : derivative ℚ ((88 - 192 * X : ℚ⟦X⟧) * G + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ G + (-56 + 32 * X : ℚ⟦X⟧) * W + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ W) =
      (-192) * G + 2 * (88 - 192 * X) * derivative ℚ G + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ G) + (32) * W + 2 * (-56 + 32 * X) * derivative ℚ W + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d16, d32, d56, d88, d96, d192]
    ring
  have r0_3 : (96 * X - 768 * X ^ 2) * derivative ℚ G + 2 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ G) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (-192) * G + 2 * (88 - 192 * X) * derivative ℚ G + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ G) + (32) * W + 2 * (-56 + 32 * X) * derivative ℚ W + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ W) := by
    rw [← hLr0_3, ← hRr0_3, r0_2p]
  have r0_3p : (96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ G + 2 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (-192 : ℚ⟦X⟧) * G + 2 * ((88 - 192 * X : ℚ⟦X⟧) * derivative ℚ G) + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (32 : ℚ⟦X⟧) * W + 2 * ((-56 + 32 * X : ℚ⟦X⟧) * derivative ℚ W) + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W) := by linear_combination r0_3
  have hLr0_4 : derivative ℚ ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ G + 2 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (96 - 1536 * X) * derivative ℚ G + 3 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ G) + 3 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d16, d48, d64, d96, d256, d768]
    ring
  have hRr0_4 : derivative ℚ ((-192 : ℚ⟦X⟧) * G + 2 * ((88 - 192 * X : ℚ⟦X⟧) * derivative ℚ G) + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (32 : ℚ⟦X⟧) * W + 2 * ((-56 + 32 * X : ℚ⟦X⟧) * derivative ℚ W) + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) =
      (0) * G + 3 * (-192) * derivative ℚ G + 3 * (88 - 192 * X) * derivative ℚ (derivative ℚ G) + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (0) * W + 3 * (32) * derivative ℚ W + 3 * (-56 + 32 * X) * derivative ℚ (derivative ℚ W) + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    simp [Derivation.leibniz, d2, d16, d32, d56, d88, d96, d192]
    ring
  have r0_4 : (96 - 1536 * X) * derivative ℚ G + 3 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ G) + 3 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0) * G + 3 * (-192) * derivative ℚ G + 3 * (88 - 192 * X) * derivative ℚ (derivative ℚ G) + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (0) * W + 3 * (32) * derivative ℚ W + 3 * (-56 + 32 * X) * derivative ℚ (derivative ℚ W) + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    rw [← hLr0_4, ← hRr0_4, r0_3p]
  have r0_4p : (96 - 1536 * X : ℚ⟦X⟧) * derivative ℚ G + 3 * ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 3 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0 : ℚ⟦X⟧) * G + 3 * ((-192 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((88 - 192 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (0 : ℚ⟦X⟧) * W + 3 * ((32 : ℚ⟦X⟧) * derivative ℚ W) + 3 * ((-56 + 32 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by linear_combination r0_4
  have hLr0_5 : derivative ℚ ((96 - 1536 * X : ℚ⟦X⟧) * derivative ℚ G + 3 * ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 3 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (-1536) * derivative ℚ G + 4 * (96 - 1536 * X) * derivative ℚ (derivative ℚ G) + 6 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 4 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) := by
    simp [Derivation.leibniz, d3, d16, d48, d64, d96, d256, d768, d1536]
    ring
  have hRr0_5 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 3 * ((-192 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((88 - 192 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (0 : ℚ⟦X⟧) * W + 3 * ((32 : ℚ⟦X⟧) * derivative ℚ W) + 3 * ((-56 + 32 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W))) =
      (0) * G + 4 * (0) * derivative ℚ G + 6 * (-192) * derivative ℚ (derivative ℚ G) + 4 * (88 - 192 * X) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (0) * W + 4 * (0) * derivative ℚ W + 6 * (32) * derivative ℚ (derivative ℚ W) + 4 * (-56 + 32 * X) * derivative ℚ (derivative ℚ (derivative ℚ W)) + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) := by
    simp [Derivation.leibniz, d3, d16, d32, d56, d88, d96, d192]
    ring
  have r0_5 : (-1536) * derivative ℚ G + 4 * (96 - 1536 * X) * derivative ℚ (derivative ℚ G) + 6 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 4 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (0) * G + 4 * (0) * derivative ℚ G + 6 * (-192) * derivative ℚ (derivative ℚ G) + 4 * (88 - 192 * X) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (0) * W + 4 * (0) * derivative ℚ W + 6 * (32) * derivative ℚ (derivative ℚ W) + 4 * (-56 + 32 * X) * derivative ℚ (derivative ℚ (derivative ℚ W)) + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) := by
    rw [← hLr0_5, ← hRr0_5, r0_4p]
  have r0_5p : (-1536 : ℚ⟦X⟧) * derivative ℚ G + 4 * ((96 - 1536 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 6 * ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + 4 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (0 : ℚ⟦X⟧) * G + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 6 * ((-192 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 4 * ((88 - 192 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (0 : ℚ⟦X⟧) * W + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ W) + 6 * ((32 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + 4 * ((-56 + 32 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) := by linear_combination r0_5
  have hLr0_6 : derivative ℚ ((-1536 : ℚ⟦X⟧) * derivative ℚ G + 4 * ((96 - 1536 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 6 * ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + 4 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))))) =
      (0) * derivative ℚ G + 5 * (-1536) * derivative ℚ (derivative ℚ G) + 10 * (96 - 1536 * X) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 10 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + 5 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))))) := by
    simp [Derivation.leibniz, d4, d6, d16, d48, d64, d96, d256, d768, d1536]
    ring
  have hRr0_6 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 6 * ((-192 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 4 * ((88 - 192 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (-16 + 88 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (0 : ℚ⟦X⟧) * W + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ W) + 6 * ((32 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + 4 * ((-56 + 32 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 - 56 * X + 16 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W)))) =
      (0) * G + 5 * (0) * derivative ℚ G + 10 * (0) * derivative ℚ (derivative ℚ G) + 10 * (-192) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 5 * (88 - 192 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (0) * W + 5 * (0) * derivative ℚ W + 10 * (0) * derivative ℚ (derivative ℚ W) + 10 * (32) * derivative ℚ (derivative ℚ (derivative ℚ W)) + 5 * (-56 + 32 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W)))) := by
    simp [Derivation.leibniz, d4, d6, d16, d32, d56, d88, d96, d192]
    ring
  have r0_6 : (0) * derivative ℚ G + 5 * (-1536) * derivative ℚ (derivative ℚ G) + 10 * (96 - 1536 * X) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 10 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + 5 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))))) =
      (0) * G + 5 * (0) * derivative ℚ G + 10 * (0) * derivative ℚ (derivative ℚ G) + 10 * (-192) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 5 * (88 - 192 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-16 + 88 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (0) * W + 5 * (0) * derivative ℚ W + 10 * (0) * derivative ℚ (derivative ℚ W) + 10 * (32) * derivative ℚ (derivative ℚ (derivative ℚ W)) + 5 * (-56 + 32 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 - 56 * X + 16 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W)))) := by
    rw [← hLr0_6, ← hRr0_6, r0_5p]
  have r1_1 : (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ W =
      (16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * G + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * W := by
    linear_combination (16 * X ^ 3 - 64 * X ^ 4) * dW + 8 * X ^ 3 * G * rS + S * r0_1 +
      (32 * X ^ 3 - (-16 + 88 * X - 96 * X ^ 2) + (16 - 56 * X + 16 * X ^ 2) * S) * hW +
      (16 - 56 * X + 16 * X ^ 2) * G * hS
  have hLr1_2 : derivative ℚ ((16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ W) =
      (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ W + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d16, d64]
    ring
  have hRr1_2 : derivative ℚ ((16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * G + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * W) =
      (-120 + 480 * X - 192 * X ^ 2) * G + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ G + (88 - 192 * X - 96 * X ^ 2) * W + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ W := by
    simp [Derivation.leibniz, d16, d32, d64, d88, d96, d120, d240]
    ring
  have r1_2 : (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ W + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ W) =
      (-120 + 480 * X - 192 * X ^ 2) * G + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ G + (88 - 192 * X - 96 * X ^ 2) * W + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ W := by
    rw [← hLr1_2, ← hRr1_2, r1_1]
  have r1_2p : (48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W) =
      (-120 + 480 * X - 192 * (X * X) : ℚ⟦X⟧) * G + (16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (88 - 192 * X - 96 * (X * X) : ℚ⟦X⟧) * W + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W := by linear_combination r1_2
  have hLr1_3 : derivative ℚ ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) =
      (96 * X - 768 * X ^ 2) * derivative ℚ W + 2 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ W) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    simp [Derivation.leibniz, d16, d48, d64, d256]
    ring
  have hRr1_3 : derivative ℚ ((-120 + 480 * X - 192 * (X * X) : ℚ⟦X⟧) * G + (16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (88 - 192 * X - 96 * (X * X) : ℚ⟦X⟧) * W + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ W) =
      (480 - 384 * X) * G + 2 * (-120 + 480 * X - 192 * X ^ 2) * derivative ℚ G + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ (derivative ℚ G) + (-192 - 192 * X) * W + 2 * (88 - 192 * X - 96 * X ^ 2) * derivative ℚ W + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ (derivative ℚ W) := by
    simp [Derivation.leibniz, d16, d32, d64, d88, d96, d120, d192, d240, d480]
    ring
  have r1_3 : (96 * X - 768 * X ^ 2) * derivative ℚ W + 2 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ W) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ W)) =
      (480 - 384 * X) * G + 2 * (-120 + 480 * X - 192 * X ^ 2) * derivative ℚ G + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ (derivative ℚ G) + (-192 - 192 * X) * W + 2 * (88 - 192 * X - 96 * X ^ 2) * derivative ℚ W + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ (derivative ℚ W) := by
    rw [← hLr1_3, ← hRr1_3, r1_2p]
  have r1_3p : (96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ W + 2 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W)) =
      (480 - 384 * X : ℚ⟦X⟧) * G + 2 * ((-120 + 480 * X - 192 * (X * X) : ℚ⟦X⟧) * derivative ℚ G) + (16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-192 - 192 * X : ℚ⟦X⟧) * W + 2 * ((88 - 192 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ W) + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W) := by linear_combination r1_3
  have hLr1_4 : derivative ℚ ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ W + 2 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W))) =
      (96 - 1536 * X) * derivative ℚ W + 3 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ W) + 3 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ W)) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) := by
    simp [Derivation.leibniz, d2, d16, d48, d64, d96, d256, d768]
    ring
  have hRr1_4 : derivative ℚ ((480 - 384 * X : ℚ⟦X⟧) * G + 2 * ((-120 + 480 * X - 192 * (X * X) : ℚ⟦X⟧) * derivative ℚ G) + (16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-192 - 192 * X : ℚ⟦X⟧) * W + 2 * ((88 - 192 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ W) + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) =
      (-384) * G + 3 * (480 - 384 * X) * derivative ℚ G + 3 * (-120 + 480 * X - 192 * X ^ 2) * derivative ℚ (derivative ℚ G) + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-192) * W + 3 * (-192 - 192 * X) * derivative ℚ W + 3 * (88 - 192 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ W) + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    simp [Derivation.leibniz, d2, d16, d32, d64, d88, d96, d120, d192, d240, d384, d480]
    ring
  have r1_4 : (96 - 1536 * X) * derivative ℚ W + 3 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ W) + 3 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ W)) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) =
      (-384) * G + 3 * (480 - 384 * X) * derivative ℚ G + 3 * (-120 + 480 * X - 192 * X ^ 2) * derivative ℚ (derivative ℚ G) + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-192) * W + 3 * (-192 - 192 * X) * derivative ℚ W + 3 * (88 - 192 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ W) + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by
    rw [← hLr1_4, ← hRr1_4, r1_3p]
  have r1_4p : (96 - 1536 * X : ℚ⟦X⟧) * derivative ℚ W + 3 * ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + 3 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) =
      (-384 : ℚ⟦X⟧) * G + 3 * ((480 - 384 * X : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((-120 + 480 * X - 192 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-192 : ℚ⟦X⟧) * W + 3 * ((-192 - 192 * X : ℚ⟦X⟧) * derivative ℚ W) + 3 * ((88 - 192 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W)) := by linear_combination r1_4
  have hLr1_5 : derivative ℚ ((96 - 1536 * X : ℚ⟦X⟧) * derivative ℚ W + 3 * ((96 * X - 768 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + 3 * ((48 * (X * X) - 256 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W)))) =
      (-1536) * derivative ℚ W + 4 * (96 - 1536 * X) * derivative ℚ (derivative ℚ W) + 6 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ W)) + 4 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W)))) := by
    simp [Derivation.leibniz, d3, d16, d48, d64, d96, d256, d768, d1536]
    ring
  have hRr1_5 : derivative ℚ ((-384 : ℚ⟦X⟧) * G + 3 * ((480 - 384 * X : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((-120 + 480 * X - 192 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (16 - 120 * X + 240 * (X * X) - 64 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-192 : ℚ⟦X⟧) * W + 3 * ((-192 - 192 * X : ℚ⟦X⟧) * derivative ℚ W) + 3 * ((88 - 192 * X - 96 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ W)) + (-16 + 88 * X - 96 * (X * X) - 32 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ W))) =
      (0) * G + 4 * (-384) * derivative ℚ G + 6 * (480 - 384 * X) * derivative ℚ (derivative ℚ G) + 4 * (-120 + 480 * X - 192 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (0) * W + 4 * (-192) * derivative ℚ W + 6 * (-192 - 192 * X) * derivative ℚ (derivative ℚ W) + 4 * (88 - 192 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ W)) + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) := by
    simp [Derivation.leibniz, d3, d16, d32, d64, d88, d96, d120, d192, d240, d384, d480]
    ring
  have r1_5 : (-1536) * derivative ℚ W + 4 * (96 - 1536 * X) * derivative ℚ (derivative ℚ W) + 6 * (96 * X - 768 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ W)) + 4 * (48 * X ^ 2 - 256 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) + (16 * X ^ 3 - 64 * X ^ 4) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W)))) =
      (0) * G + 4 * (-384) * derivative ℚ G + 6 * (480 - 384 * X) * derivative ℚ (derivative ℚ G) + 4 * (-120 + 480 * X - 192 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (16 - 120 * X + 240 * X ^ 2 - 64 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (0) * W + 4 * (-192) * derivative ℚ W + 6 * (-192 - 192 * X) * derivative ℚ (derivative ℚ W) + 4 * (88 - 192 * X - 96 * X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ W)) + (-16 + 88 * X - 96 * X ^ 2 - 32 * X ^ 3) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ W))) := by
    rw [← hLr1_5, ← hRr1_5, r1_4p]
  have hfull : (32 * X ^ 2 - 640 * X ^ 3 + 5120 * X ^ 4 - 20480 * X ^ 5 + 40960 * X ^ 6 - 32768 * X ^ 7 : ℚ⟦X⟧) * ((X ^ 8 - 4 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))))) + (2 * X ^ 5 - 11 * X ^ 6 + 27 * X ^ 7 - 69 * X ^ 8 - 36 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (-35 * X ^ 5 + 74 * X ^ 6 - 237 * X ^ 7 - 528 * X ^ 8 + 24 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-66 * X ^ 5 + 195 * X ^ 6 - 2250 * X ^ 7 + 228 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (657 * X ^ 5 - 2928 * X ^ 6 + 504 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-708 * X ^ 5 + 216 * X ^ 6) * derivative ℚ G - (0)) = 0 := by
    linear_combination (2 * X ^ 7 - 40 * X ^ 8 + 320 * X ^ 9 - 1280 * X ^ 10 + 2560 * X ^ 11 - 2048 * X ^ 12) * r0_6 +
      (2 * X ^ 4 - 43 * X ^ 5 + 380 * X ^ 6 - 1738 * X ^ 7 + 4056 * X ^ 8 - 2624 * X ^ 9 - 9472 * X ^ 10 + 24064 * X ^ 11 - 18432 * X ^ 12) * r0_5 +
      (2 * X ^ 4 - 39 * X ^ 5 + 306 * X ^ 6 - 1216 * X ^ 7 + 2496 * X ^ 8 - 2304 * X ^ 9 + 512 * X ^ 10) * r1_5 +
      (-24 * X ^ 3 + 515 * X ^ 4 - 4577 * X ^ 5 + 21666 * X ^ 6 - 58336 * X ^ 7 + 87536 * X ^ 8 - 62976 * X ^ 9 + 5120 * X ^ 10 + 12288 * X ^ 11 + 12288 * X ^ 12) * r0_4 +
      (-24 * X ^ 3 + 483 * X ^ 4 - 3939 * X ^ 5 + 16578 * X ^ 6 - 37824 * X ^ 7 + 44736 * X ^ 8 - 23808 * X ^ 9 + 4608 * X ^ 10) * r1_4 +
      (144 * X ^ 2 - 3087 * X ^ 3 + 27390 * X ^ 4 - 129342 * X ^ 5 + 347676 * X ^ 6 - 525000 * X ^ 7 + 395712 * X ^ 8 - 62976 * X ^ 9 - 79872 * X ^ 10 - 30720 * X ^ 11) * r0_3 +
      (144 * X ^ 2 - 2943 * X ^ 3 + 24450 * X ^ 4 - 105102 * X ^ 5 + 245916 * X ^ 6 - 300000 * X ^ 7 + 158976 * X ^ 8 - 9216 * X ^ 9 - 3072 * X ^ 10) * r1_3 +
      (-480 * X + 10284 * X ^ 2 - 91074 * X ^ 3 + 428172 * X ^ 4 - 1140312 * X ^ 5 + 1692960 * X ^ 6 - 1245888 * X ^ 7 + 203520 * X ^ 8 + 230400 * X ^ 9 + 61440 * X ^ 10) * r0_2 +
      (-480 * X + 9900 * X ^ 2 - 83142 * X ^ 3 + 361740 * X ^ 4 - 855192 * X ^ 5 + 1047840 * X ^ 6 - 542592 * X ^ 7 - 19968 * X ^ 8 + 12288 * X ^ 9) * r1_2 +
      (720 - 15420 * X + 136344 * X ^ 2 - 638460 * X ^ 3 + 1685112 * X ^ 4 - 2453280 * X ^ 5 + 1739520 * X ^ 6 - 255744 * X ^ 7 - 301056 * X ^ 8 - 61440 * X ^ 9) * r0_1 +
      (720 - 14940 * X + 126360 * X ^ 2 - 554076 * X ^ 3 + 1318392 * X ^ 4 - 1608480 * X ^ 5 + 817920 * X ^ 6 + 87552 * X ^ 7 - 18432 * X ^ 8) * r1_1
  have hM0 : (32 - 640 * X + 5120 * X ^ 2 - 20480 * X ^ 3 + 40960 * X ^ 4 - 32768 * X ^ 5 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (32 : ℚ⟦X⟧) = 32 := cnum 32
    simp [kc] at h'
  have hM : (32 * X ^ 2 - 640 * X ^ 3 + 5120 * X ^ 4 - 20480 * X ^ 5 + 40960 * X ^ 6 - 32768 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    have e : (32 * X ^ 2 - 640 * X ^ 3 + 5120 * X ^ 4 - 20480 * X ^ 5 + 40960 * X ^ 6 - 32768 * X ^ 7 : ℚ⟦X⟧) = X ^ 2 * (32 - 640 * X + 5120 * X ^ 2 - 20480 * X ^ 3 + 40960 * X ^ 4 - 32768 * X ^ 5 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) hM0
  have h := (mul_eq_zero.mp hfull).resolve_left hM
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem keyC (G S c U W : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hU : U = X * (c * c * c))
    (hG : G = (PowerSeries.exp ℚ).subst U)
    (hW : W = S * G) :
    derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))))) * X * X * X * X * X * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))))) * X * X * X * X * X * X * X * X * X * C (-4) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * C 2 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * X * C (-11) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * X * X * C 27 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * X * X * X * C (-69) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * X * X * X * X * C (-36) + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * C (-35) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * C 74 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * C (-237) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * X * C (-528) + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * X * X * C 24 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-66) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 195 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-2250) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C 228 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 657 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-2928) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 504 + derivative ℚ G * X * X * X * X * X * C (-708) +
      derivative ℚ G * X * X * X * X * X * X * C 216 =
      0 := by
  have h := key G S c U W hS hc hU hG hW
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem rel (G S c U W : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hU : U = X * (c * c * c))
    (hG : G = (PowerSeries.exp ℚ).subst U)
    (hW : W = S * G) (m : ℕ) :
    1 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-11) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      27 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-69) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-36) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-35) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      74 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-237) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-528) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 24 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1) G +
      (-66) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 195 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-2250) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 228 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      657 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-2928) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      504 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-708) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      216 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G S c U W hS hc hU hG hW)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem relE0 (G S c U W : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hU : U = X * (c * c * c))
    (hG : G = (PowerSeries.exp ℚ).subst U)
    (hW : W = S * G) :
    240 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-840) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-396) * coeff (0 + 1 + 1 + 1) G + 1314 * coeff (0 + 1 + 1) G +
      (-708) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G S c U W hS hc hU hG hW)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem relE1 (G S c U W : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hU : U = X * (c * c * c))
    (hG : G = (PowerSeries.exp ℚ).subst U)
    (hW : W = S * G) :
    1440 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1320) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-4200) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1776 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1584) * coeff (0 + 1 + 1 + 1 + 1) G + 1170 * coeff (0 + 1 + 1 + 1) G +
      3942 * coeff (0 + 1 + 1 + 1) G + (-5856) * coeff (0 + 1 + 1) G +
      (-1416) * coeff (0 + 1 + 1) G + 216 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G S c U W hS hc hU hG hW)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem relE2 (G S c U W : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hU : U = X * (c * c * c))
    (hG : G = (PowerSeries.exp ℚ).subst U)
    (hW : W = S * G) :
    5040 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-7920) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      3240 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-12600) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      8880 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-5688) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-3960) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 4680 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-13500) * coeff (0 + 1 + 1 + 1) G + 7884 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-17568) * coeff (0 + 1 + 1 + 1) G + 1008 * coeff (0 + 1 + 1) G +
      (-2124) * coeff (0 + 1 + 1 + 1) G + 432 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G S c U W hS hc hU hG hW)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem relE3 (G S c U W : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hc : 2 * X * c = 1 - S)
    (hU : U = X * (c * c * c))
    (hG : G = (PowerSeries.exp ℚ).subst U)
    (hW : W = S * G) :
    720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 13440 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-27720) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 19440 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-8280) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-29400) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      26640 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-28440) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-12672) * coeff (0 + 1 + 1 + 1 + 1) G + (-7920) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      11700 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-54000) * coeff (0 + 1 + 1 + 1 + 1) G +
      1368 * coeff (0 + 1 + 1 + 1) G + 13140 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-35136) * coeff (0 + 1 + 1 + 1 + 1) G + 3024 * coeff (0 + 1 + 1 + 1) G +
      (-2832) * coeff (0 + 1 + 1 + 1 + 1) G + 648 * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G S c U W hS hc hU hG hW)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A250917Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250917.main := by
  intro S c U G hS _ hc hU hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  have hU3 : U = PowerSeries.X * (c * c * c) := by
    rw [hU]
    ring
  unfold OMA.S_oeis_a250917.a
  cases m with
  | zero =>
    have r := A250917Aux.relE0 G S c U (S * G) hS hc hU3 hG rfl
    simp only [Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    linear_combination (1 : ℚ) * r
  | succ m =>
    cases m with
    | zero =>
      have r := A250917Aux.relE1 G S c U (S * G) hS hc hU3 hG rfl
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      linear_combination (1 : ℚ) * r
    | succ m =>
      cases m with
      | zero =>
        have r := A250917Aux.relE2 G S c U (S * G) hS hc hU3 hG rfl
        simp only [Nat.factorial_succ, Nat.factorial_zero]
        push_cast
        linear_combination (2 : ℚ) * r
      | succ m =>
        cases m with
        | zero =>
          have r := A250917Aux.relE3 G S c U (S * G) hS hc hU3 hG rfl
          simp only [Nat.factorial_succ, Nat.factorial_zero]
          push_cast
          linear_combination (6 : ℚ) * r
        | succ m =>
          have r := A250917Aux.rel G S c U (S * G) hS hc hU3 hG rfl m
          simp only [Nat.factorial_succ]
          push_cast
          linear_combination (((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4) * (m.factorial : ℚ)) * r
