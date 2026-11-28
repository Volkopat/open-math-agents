import OMAStatements.S_oeis_a386566
import Mathlib

namespace OMA.Helpers_a386566
open OMA.S_oeis_a386566 PowerSeries

noncomputable def Q0 : ℚ⟦X⟧ := (1 + X) ^ 5
noncomputable def P0 : ℚ⟦X⟧ := X * Q0⁻¹

theorem cQ0 : constantCoeff Q0 = 1 := by simp [Q0]

theorem P0c1 : coeff 1 P0 = 1 := by
  rw [P0, mul_comm, coeff_succ_mul_X, coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv, cQ0]
  simp

noncomputable def W : ℚ⟦X⟧ := P0.substInvOfIsUnit (by rw [P0c1]; exact isUnit_one)
noncomputable def B : ℚ⟦X⟧ := 1 + W

theorem hB : X * B ^ 5 = B - 1 := by
  have hs : HasSubst W := HasSubst.substInvOfIsUnit _ _
  have h : P0.subst W = X := subst_substInvOfIsUnit_right _ (by simp [P0]) _
  have hinv : Q0 * Q0⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [cQ0]; norm_num)
  have e1 := congrArg (substAlgHom hs) hinv
  rw [← coe_substAlgHom hs] at h
  simp only [P0, map_mul, map_one] at h e1
  have hX : substAlgHom hs (X : ℚ⟦X⟧) = W := by rw [coe_substAlgHom]; exact subst_X hs
  have hQ : substAlgHom hs Q0 = B ^ 5 := by
    simp only [Q0, map_pow, map_add, map_one, hX, B]
  rw [hX] at h
  rw [hQ] at e1
  unfold B at *
  linear_combination (-(1 + W) ^ 5) * h + W * e1


theorem Dnum (k : ℕ) [k.AtLeastTwo] : (d⁄dX ℚ) (no_index (OfNat.ofNat k : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C k]; exact derivative_C

theorem Bd : (5 - 4 * B) * (d⁄dX ℚ) B = B ^ 6 := by
  have dh := congrArg (d⁄dX ℚ) hB
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, smul_eq_mul, nsmul_eq_mul, derivative_X, derivative_one] at dh
  push_cast at dh
  linear_combination (-B) * dh + 5 * (d⁄dX ℚ) B * hB

theorem cB : constantCoeff B = 1 := by
  simp [B, W, constantCoeff_substInvOfIsUnit]

theorem ne0 (s M : ℕ) : B ^ s * (5 - 4 * B) ^ M ≠ (0 : ℚ⟦X⟧) := by
  intro h
  have := congrArg constantCoeff h
  simp only [map_mul, map_pow, map_sub, cB, map_ofNat, map_zero] at this
  norm_num at this

noncomputable def E : ℚ⟦X⟧ := (5 - 4 * B)⁻¹

theorem E_base : (5 - 4 * B) ^ 1 * E = 1 := by
  rw [pow_one, E, PowerSeries.mul_inv_cancel]
  simp only [map_sub, map_mul, cB, map_ofNat]; norm_num

noncomputable def F : ℚ⟦X⟧ := X * B ^ 6 * E

theorem F_base : (5 - 4 * B) ^ 1 * F = X * B ^ 6 := by
  unfold F; linear_combination (X * B ^ 6) * E_base

noncomputable def th (G : ℚ⟦X⟧) : ℚ⟦X⟧ := X * (d⁄dX ℚ) G

theorem coeff_th (G : ℚ⟦X⟧) (k : ℕ) : coeff k (th G) = (k : ℚ) * coeff k G := by
  unfold th
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem E_h0 : (5 - 4 * B) ^ 1 * E = 1 := by linear_combination E_base

theorem E_h1 : (5 - 4 * B) ^ 3 * ((d⁄dX ℚ) (E)) = 4*B^6 := by
  have dh := congrArg (d⁄dX ℚ) E_h0
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, smul_eq_mul, nsmul_eq_mul, Dnum, derivative_one] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (4 * (5 - 4 * B) ^ 1 * (E) + (5 - 4 * B) * (0)) * Bd + 4 * B ^ 6 * E_h0

theorem E_h2 : (5 - 4 * B) ^ 5 * ((d⁄dX ℚ) ((d⁄dX ℚ) (E))) = -48*B^12 + 120*B^11 := by
  have dh := congrArg (d⁄dX ℚ) E_h1
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, smul_eq_mul, nsmul_eq_mul, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (12 * (5 - 4 * B) ^ 3 * ((d⁄dX ℚ) (E)) + (5 - 4 * B) * (24*B^5)) * Bd + 12 * B ^ 6 * E_h1

theorem E_h3 : (5 - 4 * B) ^ 7 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (E)))) = 1344*B^18 - 5760*B^17 + 6600*B^16 := by
  have dh := congrArg (d⁄dX ℚ) E_h2
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, map_neg, smul_eq_mul, nsmul_eq_mul, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (20 * (5 - 4 * B) ^ 5 * ((d⁄dX ℚ) ((d⁄dX ℚ) (E))) + (5 - 4 * B) * (-576*B^11 + 1320*B^10)) * Bd + 20 * B ^ 6 * E_h2

theorem E_h4 : (5 - 4 * B) ^ 9 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (E))))) = -59136*B^24 + 351360*B^23 - 727200*B^22 + 528000*B^21 := by
  have dh := congrArg (d⁄dX ℚ) E_h3
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul, nsmul_eq_mul, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (28 * (5 - 4 * B) ^ 7 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (E)))) + (5 - 4 * B) * (24192*B^17 - 97920*B^16 + 105600*B^15)) * Bd + 28 * B ^ 6 * E_h3

noncomputable def E_L : ℚ⟦X⟧ := X ^ 0 * (C (-24 : ℚ) * th (E) + C (176 : ℚ) * th (th (E)) + C (-384 : ℚ) * th (th (th (E))) + C (256 : ℚ) * th (th (th (th (E))))) + X ^ 1 * (C (-120 : ℚ) * E + C (-1250 : ℚ) * th (E) + C (-4375 : ℚ) * th (th (E)) + C (-6250 : ℚ) * th (th (th (E))) + C (-3125 : ℚ) * th (th (th (th (E)))))

theorem E_Lmul : B ^ 25 * (5 - 4 * B) ^ 9 * E_L = B ^ 25 * (5 - 4 * B) ^ 9 * (C (-24 : ℚ) * X ^ 1) := by
  unfold E_L th
  simp only [Derivation.leibniz, map_add, map_neg, smul_eq_mul, derivative_X, map_ofNat, pow_zero, one_mul, mul_one, map_neg]
  linear_combination B ^ 25 * (-120*X) * (5 - 4 * B) ^ 8 * E_h0 + B ^ 25 * (-15000*X^2 + 24*X) * (5 - 4 * B) ^ 6 * E_h1 + B ^ 25 * (-45000*X^3 + 816*X^2) * (5 - 4 * B) ^ 4 * E_h2 + B ^ 25 * (-25000*X^4 + 1152*X^3) * (5 - 4 * B) ^ 2 * E_h3 + B ^ 25 * (-3125*X^5 + 256*X^4) * (5 - 4 * B) ^ 0 * E_h4 + (184800000*B^44*X^4 - 15138816*B^44*X^3 - 1098000000*B^43*X^4 + 89948160*B^43*X^3 + 2272500000*B^42*X^4 - 186163200*B^42*X^3 - 1650000000*B^41*X^4 + 135168000*B^41*X^3 - 352800000*B^40*X^3 + 9633792*B^40*X^2 + 2365200000*B^39*X^3 - 63012864*B^39*X^2 - 5869500000*B^38*X^3 + 149667840*B^38*X^2 + 6277500000*B^37*X^3 - 148684800*B^37*X^2 - 2475000000*B^36*X^3 + 255072000*B^36*X^2 - 393216*B^36*X - 1429200000*B^35*X^2 + 2555904*B^35*X + 3861300000*B^34*X^2 - 6660096*B^34*X - 5133000000*B^33*X^2 + 14991360*B^33*X + 3397500000*B^32*X^2 - 62323200*B^32*X - 900000000*B^31*X^2 + 220128000*B^31*X - 469500000*B^30*X + 605700000*B^29*X - 469500000*B^28*X + 202500000*B^27*X - 37500000*B^26*X) * hB

theorem E_Leq : E_L = C (-24 : ℚ) * X ^ 1 := mul_left_cancel₀ (ne0 25 9) E_Lmul

theorem F_h0 : (5 - 4 * B) ^ 1 * F = B^6*X := by linear_combination F_base

theorem F_h1 : (5 - 4 * B) ^ 3 * ((d⁄dX ℚ) (F)) = -20*B^12*X + 30*B^11*X + 16*B^8 - 40*B^7 + 25*B^6 := by
  have dh := congrArg (d⁄dX ℚ) F_h0
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (4 * (5 - 4 * B) ^ 1 * (F) + (5 - 4 * B) * (6*B^5*X)) * Bd + 4 * B ^ 6 * F_h0

theorem F_h2 : (5 - 4 * B) ^ 5 * ((d⁄dX ℚ) ((d⁄dX ℚ) (F))) = 720*B^18*X - 2160*B^17*X + 1650*B^16*X - 640*B^14 + 2560*B^13 - 3400*B^12 + 1500*B^11 := by
  have dh := congrArg (d⁄dX ℚ) F_h1
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, map_neg, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (12 * (5 - 4 * B) ^ 3 * ((d⁄dX ℚ) (F)) + (5 - 4 * B) * (-240*B^11*X + 330*B^10*X + 128*B^7 - 280*B^6 + 150*B^5)) * Bd + 12 * B ^ 6 * F_h1

theorem F_h3 : (5 - 4 * B) ^ 7 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (F)))) = -37440*B^24*X + 168480*B^23*X - 256200*B^22*X + 132000*B^21*X + 34560*B^20 - 190080*B^19 + 392400*B^18 - 360000*B^17 + 123750*B^16 := by
  have dh := congrArg (d⁄dX ℚ) F_h2
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (20 * (5 - 4 * B) ^ 5 * ((d⁄dX ℚ) ((d⁄dX ℚ) (F))) + (5 - 4 * B) * (12960*B^17*X - 36720*B^16*X + 26400*B^15*X - 8960*B^13 + 33280*B^12 - 40800*B^11 + 16500*B^10)) * Bd + 20 * B ^ 6 * F_h2

theorem F_h4 : (5 - 4 * B) ^ 9 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (F))))) = 2545920*B^30*X - 15275520*B^29*X + 34747200*B^28*X - 35574000*B^27*X + 13860000*B^26*X - 2396160*B^26 + 16773120*B^25 - 47097600*B^24 + 66288000*B^23 - 46740000*B^22 + 13200000*B^21 := by
  have dh := congrArg (d⁄dX ℚ) F_h3
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, map_neg, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (28 * (5 - 4 * B) ^ 7 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (F)))) + (5 - 4 * B) * (-898560*B^23*X + 3875040*B^22*X - 5636400*B^21*X + 2772000*B^20*X + 691200*B^19 - 3611520*B^18 + 7063200*B^17 - 6120000*B^16 + 1980000*B^15)) * Bd + 28 * B ^ 6 * F_h3

theorem F_h5 : (5 - 4 * B) ^ 11 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (F)))))) = -213857280*B^36*X + 1603929600*B^35*X - 4855737600*B^34*X + 7425936000*B^33*X - 5744970000*B^32*X + 203673600*B^32 + 1801800000*B^31*X - 1731225600*B^31 + 6153120000*B^30 - 11704800000*B^29 + 12567000000*B^28 - 7218750000*B^27 + 1732500000*B^26 := by
  have dh := congrArg (d⁄dX ℚ) F_h4
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (36 * (5 - 4 * B) ^ 9 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (F))))) + (5 - 4 * B) * (76377600*B^29*X - 442990080*B^28*X + 972921600*B^27*X - 960498000*B^26*X + 360360000*B^25*X - 62300160*B^25 + 419328000*B^24 - 1130342400*B^23 + 1524624000*B^22 - 1028280000*B^21 + 277200000*B^20)) * Bd + 36 * B ^ 6 * F_h4

noncomputable def F_L : ℚ⟦X⟧ := X ^ 0 * (C (-8 : ℚ) * th (F) + C (24 : ℚ) * th (th (F)) + C (112 : ℚ) * th (th (th (F))) + C (-384 : ℚ) * th (th (th (th (F)))) + C (256 : ℚ) * th (th (th (th (th (F)))))) + X ^ 1 * (C (-120 : ℚ) * F + C (-1370 : ℚ) * th (F) + C (-5625 : ℚ) * th (th (F)) + C (-10625 : ℚ) * th (th (th (F))) + C (-9375 : ℚ) * th (th (th (th (F)))) + C (-3125 : ℚ) * th (th (th (th (th (F))))))

theorem F_Lmul : B ^ 35 * (5 - 4 * B) ^ 11 * F_L = B ^ 35 * (5 - 4 * B) ^ 11 * (0) := by
  unfold F_L th
  simp only [Derivation.leibniz, map_add, map_neg, smul_eq_mul, derivative_X, map_ofNat, pow_zero, one_mul, mul_one, map_neg, mul_zero]
  linear_combination B ^ 35 * (-120*X) * (5 - 4 * B) ^ 10 * F_h0 + B ^ 35 * (-30120*X^2) * (5 - 4 * B) ^ 8 * F_h1 + B ^ 35 * (-150000*X^3 + 1512*X^2) * (5 - 4 * B) ^ 6 * F_h2 + B ^ 35 * (-145000*X^4 + 4208*X^3) * (5 - 4 * B) ^ 4 * F_h3 + B ^ 35 * (-40625*X^5 + 2176*X^4) * (5 - 4 * B) ^ 2 * F_h4 + B ^ 35 * (-3125*X^6 + 256*X^5) * (5 - 4 * B) ^ 0 * F_h5 + (668304000000*B^66*X^6 - 54747463680*B^66*X^5 - 5012280000000*B^65*X^6 + 410605977600*B^65*X^5 + 15174180000000*B^64*X^6 - 1243068825600*B^64*X^5 - 23206050000000*B^63*X^6 + 1901039616000*B^63*X^5 + 17953031250000*B^62*X^6 - 3093736320000*B^62*X^5 + 86031728640*B^62*X^4 - 5630625000000*B^61*X^6 + 14256964800000*B^61*X^5 - 731269693440*B^61*X^4 - 49036140000000*B^60*X^5 + 2599361740800*B^60*X^4 + 93298770000000*B^59*X^5 - 4946249318400*B^59*X^4 - 100219668750000*B^58*X^5 + 6638811264000*B^58*X^4 - 37725143040*B^58*X^3 + 57627281250000*B^57*X^5 - 15638028480000*B^57*X^4 + 358388858880*B^57*X^3 - 13860000000000*B^56*X^5 + 52016911200000*B^56*X^4 - 1460980776960*B^56*X^3 - 116260290000000*B^55*X^4 + 3312864460800*B^55*X^3 + 158323061250000*B^54*X^4 - 4914085017600*B^54*X^3 + 3963617280*B^54*X^2 - 129511800000000*B^53*X^4 + 7904393856000*B^53*X^3 - 41617981440*B^53*X^2 + 58931156250000*B^52*X^4 - 21028018320000*B^52*X^3 + 191244533760*B^52*X^2 - 11508750000000*B^51*X^4 + 51138118800000*B^51*X^3 - 502388490240*B^51*X^2 - 83436648750000*B^50*X^3 + 856977408000*B^50*X^2 + 87735138750000*B^49*X^3 - 1232824320000*B^49*X^2 - 57695793750000*B^48*X^3 + 2436134400000*B^48*X^2 + 21697593750000*B^47*X^3 - 5781888000000*B^47*X^2 - 3573281250000*B^46*X^3 + 10725561000000*B^46*X^2 - 13695412500000*B^45*X^2 + 11706187500000*B^44*X^2 - 6437812500000*B^43*X^2 + 2067187500000*B^42*X^2 - 295312500000*B^41*X^2) * hB

theorem F_Leq : F_L = 0 := mul_left_cancel₀ (ne0 35 11) F_Lmul


def c (k : ℕ) : ℚ := ((5 * k - 1).choose k : ℚ)
def d (j : ℕ) : ℚ := if j = 0 then 0 else ((5 * j).choose (j - 1) : ℚ)

theorem c_rec (m : ℕ) : 4 * ((m : ℚ) + 2) * (4 * ((m : ℚ) + 1) + 1) * (4 * ((m : ℚ) + 1) + 2) *
    (4 * ((m : ℚ) + 1) + 3) * c (m + 2) =
    5 * (5 * ((m : ℚ) + 1) + 1) * (5 * ((m : ℚ) + 1) + 2) * (5 * ((m : ℚ) + 1) + 3) *
    (5 * ((m : ℚ) + 1) + 4) * c (m + 1) := by
  unfold c
  rw [show 5 * (m + 2) - 1 = 5 * m + 9 by omega, show 5 * (m + 1) - 1 = 5 * m + 4 by omega,
    Nat.cast_choose ℚ (by omega : m + 2 ≤ 5 * m + 9), Nat.cast_choose ℚ (by omega : m + 1 ≤ 5 * m + 4),
    show 5 * m + 9 - (m + 2) = 4 * m + 7 by omega, show 5 * m + 4 - (m + 1) = 4 * m + 3 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

theorem d_rec (m : ℕ) : ((m : ℚ) + 1) * (4 * ((m : ℚ) + 1) + 2) * (4 * ((m : ℚ) + 1) + 3) *
    (4 * ((m : ℚ) + 1) + 4) * (4 * ((m : ℚ) + 1) + 5) * d (m + 2) =
    (5 * ((m : ℚ) + 1) + 1) * (5 * ((m : ℚ) + 1) + 2) * (5 * ((m : ℚ) + 1) + 3) *
    (5 * ((m : ℚ) + 1) + 4) * (5 * ((m : ℚ) + 1) + 5) * d (m + 1) := by
  unfold d
  rw [if_neg (by omega), if_neg (by omega), show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega,
    show 5 * (m + 2) = 5 * m + 10 by omega, show 5 * (m + 1) = 5 * m + 5 by omega,
    Nat.cast_choose ℚ (by omega : m + 1 ≤ 5 * m + 10), Nat.cast_choose ℚ (by omega : m ≤ 5 * m + 5),
    show 5 * m + 10 - (m + 1) = 4 * m + 9 by omega, show 5 * m + 5 - m = 4 * m + 5 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

theorem pE (k : ℕ) : (0 : ℚ) < 4 * ((k : ℚ) + 1) * (4 * k + 1) * (4 * k + 2) * (4 * k + 3) := by positivity

theorem E_eqn (k : ℕ) (hk : 1 ≤ k) :
    4 * ((k : ℚ) + 1) * (4 * k + 1) * (4 * k + 2) * (4 * k + 3) * coeff (k + 1) E =
      5 * (5 * (k : ℚ) + 1) * (5 * k + 2) * (5 * k + 3) * (5 * k + 4) * coeff k E := by
  have h := congrArg (coeff (k + 1)) E_Leq
  unfold E_L at h
  simp only [map_add, coeff_X_pow_mul', coeff_C_mul, coeff_th, coeff_X_pow, show 0 ≤ k + 1 by omega,
    show 1 ≤ k + 1 by omega, if_true, Nat.sub_zero, Nat.add_sub_cancel, show k + 1 ≠ 1 by omega,
    if_false, mul_zero] at h
  push_cast at h
  linear_combination h

theorem E_one : coeff 1 E = 4 := by
  have h := congrArg (coeff 1) E_Leq
  unfold E_L at h
  simp only [map_add, coeff_X_pow_mul', coeff_C_mul, coeff_th, coeff_X_pow, show 0 ≤ 1 by omega,
    if_true, Nat.sub_zero, Nat.sub_self, mul_one] at h
  have h0 : coeff 0 E = 1 := by
    have := congrArg constantCoeff E_base
    simp only [pow_one, map_mul, map_sub, cB, map_ofNat, map_one] at this
    rw [coeff_zero_eq_constantCoeff_apply]; linear_combination this
  rw [h0] at h
  push_cast at h
  linear_combination h / 24

theorem E_eq_c (k : ℕ) : coeff k E = c k := by
  rcases k with _ | k
  · have := congrArg constantCoeff E_base
    simp only [pow_one, map_mul, map_sub, cB, map_ofNat, map_one] at this
    rw [coeff_zero_eq_constantCoeff_apply]; simp [c]; linear_combination this
  induction k with
  | zero => rw [E_one]; simp [c]
  | succ m ih =>
    have h1 := E_eqn (m + 1) (by omega)
    have h2 := c_rec m
    rw [ih] at h1
    push_cast at h1
    have hp : (4 * ((m : ℚ) + 2) * (4 * ((m : ℚ) + 1) + 1) * (4 * ((m : ℚ) + 1) + 2) *
        (4 * ((m : ℚ) + 1) + 3)) ≠ 0 := by positivity
    apply mul_left_cancel₀ hp
    linear_combination h1 - h2

theorem F_eqn (k : ℕ) :
    (k : ℚ) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5) * coeff (k + 1) F =
      (5 * (k : ℚ) + 1) * (5 * k + 2) * (5 * k + 3) * (5 * k + 4) * (5 * k + 5) * coeff k F := by
  have h := congrArg (coeff (k + 1)) F_Leq
  unfold F_L at h
  simp only [map_add, coeff_X_pow_mul', coeff_C_mul, coeff_th, show 0 ≤ k + 1 by omega,
    show 1 ≤ k + 1 by omega, if_true, Nat.sub_zero, Nat.add_sub_cancel, map_zero] at h
  push_cast at h
  linear_combination h

theorem F_eq_d (k : ℕ) : coeff k F = d k := by
  rcases k with _ | k
  · simp [F, d, mul_assoc]
  induction k with
  | zero =>
    have h0 : coeff 0 E = 1 := by rw [E_eq_c]; simp [c]
    rw [F, mul_assoc, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, cB,
      ← coeff_zero_eq_constantCoeff_apply, h0]
    simp [d]
  | succ m ih =>
    have h1 := F_eqn (m + 1)
    have h2 := d_rec m
    rw [ih] at h1
    push_cast at h1
    have hp : ((m : ℚ) + 1) * (4 * ((m : ℚ) + 1) + 2) * (4 * ((m : ℚ) + 1) + 3) *
        (4 * ((m : ℚ) + 1) + 4) * (4 * ((m : ℚ) + 1) + 5) ≠ 0 := by positivity
    apply mul_left_cancel₀ hp
    linear_combination h1 - h2

noncomputable def A : ℚ⟦X⟧ := E * F

theorem a_eq (n : ℕ) : ((a n : ℤ) : ℚ) = coeff n A := by
  rw [A, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  simp only [E_eq_c, F_eq_d, Nat.sub_self, d, if_true, mul_zero, add_zero]
  unfold a
  push_cast
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [if_neg (by omega), c, show 5 * n - 5 * k = 5 * (n - k) by omega, show n - k - 1 = n - k - 1 from rfl]

theorem A_base : (5 - 4 * B) ^ 2 * A = X * B ^ 6 := by
  unfold A; linear_combination ((5 - 4 * B) * F) * E_base + F_base

theorem A_h0 : (5 - 4 * B) ^ 2 * A = B^6*X := by linear_combination A_base

theorem A_h1 : (5 - 4 * B) ^ 4 * ((d⁄dX ℚ) (A)) = -16*B^12*X + 30*B^11*X + 16*B^8 - 40*B^7 + 25*B^6 := by
  have dh := congrArg (d⁄dX ℚ) A_h0
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (8 * (5 - 4 * B) ^ 2 * (A) + (5 - 4 * B) * (6*B^5*X)) * Bd + 8 * B ^ 6 * A_h0

theorem A_h2 : (5 - 4 * B) ^ 6 * ((d⁄dX ℚ) ((d⁄dX ℚ) (A))) = 512*B^18*X - 1800*B^17*X + 1650*B^16*X - 512*B^14 + 2240*B^13 - 3200*B^12 + 1500*B^11 := by
  have dh := congrArg (d⁄dX ℚ) A_h1
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, map_neg, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (16 * (5 - 4 * B) ^ 4 * ((d⁄dX ℚ) (A)) + (5 - 4 * B) * (-192*B^11*X + 330*B^10*X + 128*B^7 - 280*B^6 + 150*B^5)) * Bd + 16 * B ^ 6 * A_h1

theorem A_h3 : (5 - 4 * B) ^ 8 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (A)))) = -24576*B^24*X + 125280*B^23*X - 219000*B^22*X + 132000*B^21*X + 24576*B^20 - 147840*B^19 + 333600*B^18 - 333000*B^17 + 123750*B^16 := by
  have dh := congrArg (d⁄dX ℚ) A_h2
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (24 * (5 - 4 * B) ^ 6 * ((d⁄dX ℚ) ((d⁄dX ℚ) (A))) + (5 - 4 * B) * (9216*B^17*X - 30600*B^16*X + 26400*B^15*X - 7168*B^13 + 29120*B^12 - 38400*B^11 + 16500*B^10)) * Bd + 24 * B ^ 6 * A_h2

theorem A_h4 : (5 - 4 * B) ^ 10 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (A))))) = 1572864*B^30*X - 10465920*B^29*X + 26671200*B^28*X - 30954000*B^27*X + 13860000*B^26*X - 1572864*B^26 + 11950080*B^25 - 36518400*B^24 + 56016000*B^23 - 43020000*B^22 + 13200000*B^21 := by
  have dh := congrArg (d⁄dX ℚ) A_h3
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, map_neg, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (32 * (5 - 4 * B) ^ 8 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (A)))) + (5 - 4 * B) * (-589824*B^23*X + 2881440*B^22*X - 4818000*B^21*X + 2772000*B^20*X + 491520*B^19 - 2808960*B^18 + 6004800*B^17 - 5661000*B^16 + 1980000*B^15)) * Bd + 32 * B ^ 6 * A_h3

theorem A_h5 : (5 - 4 * B) ^ 12 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (A)))))) = -125829120*B^36*X + 1031339520*B^35*X - 3437884800*B^34*X + 5838840000*B^33*X - 5065830000*B^32*X + 125829120*B^32 + 1801800000*B^31*X - 1151846400*B^31 + 4423488000*B^30 - 9118800000*B^29 + 10633500000*B^28 - 6641250000*B^27 + 1732500000*B^26 := by
  have dh := congrArg (d⁄dX ℚ) A_h4
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul, nsmul_eq_mul, derivative_X, Dnum] at dh
  push_cast at dh
  linear_combination (5 - 4 * B) ^ 2 * dh + (40 * (5 - 4 * B) ^ 10 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) (A))))) + (5 - 4 * B) * (47185920*B^29*X - 303511680*B^28*X + 746793600*B^27*X - 835758000*B^26*X + 360360000*B^25*X - 40894464*B^25 + 298752000*B^24 - 876441600*B^23 + 1288368000*B^22 - 946440000*B^21 + 277200000*B^20)) * Bd + 40 * B ^ 6 * A_h4

noncomputable def A_L : ℚ⟦X⟧ := X ^ 0 * (C (19204758407282688 : ℚ) * th (A) + C (-151611494548242432 : ℚ) * th (th (A)) + C (386304531300876288 : ℚ) * th (th (th (A))) + C (-377276349328392192 : ℚ) * th (th (th (th (A)))) + C (114950395322695680 : ℚ) * th (th (th (th (th (A)))))) + X ^ 1 * (C (-65680378505199360 : ℚ) * A + C (2133131101261382400 : ℚ) * th (A) + C (-4888071807442880000 : ℚ) * th (th (A)) + C (9941023310233600000 : ℚ) * th (th (th (A))) + C (-7646269592320000000 : ℚ) * th (th (th (th (A)))) + C (-1790957827072000000 : ℚ) * th (th (th (th (th (A)))))) + X ^ 2 * (C (3478346131892625000 : ℚ) * A + C (40052111996841250000 : ℚ) * th (A) + C (124171704872296875000 : ℚ) * th (th (A)) + C (176291413649218750000 : ℚ) * th (th (th (A))) + C (104373474629062500000 : ℚ) * th (th (th (th (A)))) + C (-7662274775000000000 : ℚ) * th (th (th (th (th (A)))))) + X ^ 3 * (C (9558804241406250000 : ℚ) * A + C (105381319344726562500 : ℚ) * th (A) + C (409023507031250000000 : ℚ) * th (th (A)) + C (709693412628173828125 : ℚ) * th (th (th (A))) + C (551554372436523437500 : ℚ) * th (th (th (th (A)))) + C (151313589324951171875 : ℚ) * th (th (th (th (th (A))))))

theorem A_Lmul : B ^ 45 * (5 - 4 * B) ^ 12 * A_L = B ^ 45 * (5 - 4 * B) ^ 12 * (C (-15353292436800000 : ℚ) * X ^ 2 + C (-8428158845779968 : ℚ) * X ^ 1) := by
  unfold A_L th
  simp only [Derivation.leibniz, map_add, map_neg, smul_eq_mul, derivative_X, map_ofNat, pow_zero, one_mul, mul_one, map_neg]
  linear_combination B ^ 45 * (9558804241406250000*X^3 + 3478346131892625000*X^2 - 65680378505199360*X) * (5 - 4 * B) ^ 10 * A_h0 + B ^ 45 * (1926966200765625000000*X^4 + 437226430372419375000*X^3 - 2251144815339897600*X^2 - 8428158845779968*X) * (5 - 4 * B) ^ 8 * A_h1 + B ^ 45 * (8668688191845703125000*X^5 + 1268726146598390625000*X^4 - 55453256429062080000*X^3 + 90623583896076288*X^2) * (5 - 4 * B) ^ 6 * A_h2 + B ^ 45 * (7801859380371093750000*X^6 + 610975392048593750000*X^5 - 80710539920486400000*X^4 + 996406318397915136*X^3) * (5 - 4 * B) ^ 4 * A_h3 + B ^ 45 * (2064690265686035156250*X^7 + 27750726879062500000*X^6 - 25555847863040000000*X^5 + 772227603898564608*X^4) * (5 - 4 * B) ^ 2 * A_h4 + B ^ 45 * (151313589324951171875*X^8 - 7662274775000000000*X^7 - 1790957827072000000*X^6 + 114950395322695680*X^5) * (5 - 4 * B) ^ 0 * A_h5 + (-19039655788800000000000000000*B^76*X^8 + 964137292136448000000000000*B^76*X^7 + 225354647337581936640000000*B^76*X^6 - 14464107087106913442201600*B^76*X^5 + 156055684583872265625000000000*B^75*X^8 - 7902406788556608000000000000*B^75*X^7 - 1847085585712679485440000000*B^75*X^6 + 118552885535919207717273600*B^75*X^5 - 520198688773691894531250000000*B^74*X^8 + 26342017982395920000000000000*B^74*X^7 + 6157106691131857305600000000*B^74*X^6 - 395186216833886573297664000*B^74*X^5 + 883495837894097900390625000000*B^73*X^8 - 44738796447261000000000000000*B^73*X^7 - 10457116199021076480000000000*B^73*X^6 + 671176966225968444211200000*B^73*X^5 - 766528920210017395019531250000*B^72*X^8 + 90775413264206250000000000000*B^72*X^7 + 9771057797626705920000000000*B^72*X^6 - 1225453130629612201574400000*B^72*X^5 + 19433743967652990777556992*B^72*X^4 + 272636825245697021484375000000*B^71*X^8 - 488641769381046796875000000000*B^71*X^7 - 9660643248723100800000000000*B^71*X^6 + 6084867986904940806144000000*B^71*X^5 - 177285723514235257922519040*B^71*X^4 + 1819705996054083105468750000000*B^70*X^7 + 24901445719199412000000000000*B^70*X^6 - 22527285450111147048960000000*B^70*X^5 + 677930499758205439259443200*B^70*X^4 - 3741603350616138427734375000000*B^69*X^7 - 51820728864345945000000000000*B^69*X^6 + 46324896442049050214400000000*B^69*X^5 - 1390204296694788538761216000*B^69*X^4 + 4349945082017243957519531250000*B^68*X^7 + 12010194894646968750000000000*B^68*X^6 - 57707892412516531200000000000*B^68*X^5 + 2118912157157405648486400000*B^68*X^4 - 6268846510322473569878016*B^68*X^3 - 2708170475046093750000000000000*B^67*X^7 + 454924510432950937500000000000*B^67*X^6 + 72273583060697969280000000000*B^67*X^5 - 6100406919096166357401600000*B^67*X^4 + 62816455899231186214453248*B^67*X^3 + 704929145319992065429687500000*B^66*X^7 - 2118483459761024941406250000000*B^66*X^6 - 176232135948018967200000000000*B^66*X^5 + 22235457770528742309888000000*B^66*X^4 - 269899614789327065878364160*B^66*X^3 + 5101914747849934716796875000000*B^65*X^6 + 402625209716338743000000000000*B^65*X^5 - 52604240767669162967040000000*B^65*X^4 + 644254054646833772022988800*B^65*X^3 - 7334356290569937927246093750000*B^64*X^6 - 562350181618350611250000000000*B^64*X^5 + 78176229922181418393600000000*B^64*X^4 - 1038829281085312764739584000*B^64*X^3 + 190051430214824179531776*B^64*X^2 + 6321987334095964050292968750000*B^63*X^6 + 303432697670903296875000000000*B^63*X^5 - 94073417788072337280000000000*B^63*X^4 + 2058797457058063712256000000*B^63*X^3 - 2063495216677510736510976*B^63*X^2 - 3025201599767733764648437500000*B^62*X^6 + 704032670497537382812500000000*B^62*X^5 + 169751509594310164320000000000*B^62*X^4 - 6395179431707789583974400000*B^62*X^3 + 9782130650480095361236992*B^62*X^2 + 620072041237014770507812500000*B^61*X^6 - 2515776114891278232421875000000*B^61*X^5 - 383504136258537661800000000000*B^61*X^4 + 16382141959951172124672000000*B^61*X^3 - 26454880742183426630615040*B^61*X^2 + 4344985106984267980957031250000*B^60*X^5 + 637608976635221754750000000000*B^60*X^4 - 28035113250275450449920000000*B^60*X^3 + 46944684772258422246604800*B^60*X^2 + 8837565089872575725568*B^60*X - 4702966424319820678710937500000*B^59*X^5 - 669726398682664633125000000000*B^59*X^4 + 35128158938488540108800000000*B^59*X^3 - 74296179356384152780800000*B^59*X^2 - 101631998533534620844032*B^59*X + 3177812069156785583496093750000*B^58*X^5 + 349287249243257203125000000000*B^58*X^4 - 47330511597847190400000000000*B^58*X^3 + 164601876036862554931200000*B^58*X^2 + 519759296848130859859968*B^58*X - 1226005558313397216796875000000*B^57*X^5 + 175558382165277281250000000000*B^57*X^4 + 88969975753820435520000000000*B^57*X^3 - 401624219660235177984000000*B^57*X^2 - 1551545021090754075820032*B^57*X + 206842637659584045410156250000*B^56*X^5 - 654048724675045605468750000000*B^56*X^4 - 157265743531798861800000000000*B^56*X^3 + 735534393148542418944000000*B^56*X^2 + 2838032132962595509370880*B^56*X + 877037768208173840332031250000*B^55*X^4 + 199836682519337614125000000000*B^55*X^3 - 911958691202010163200000000*B^55*X^2 - 1837419538704952511692800*B^55*X - 749646984360143737792968750000*B^54*X^4 - 170866304663921643750000000000*B^54*X^3 + 728241863486082432000000000*B^54*X^2 - 9339748506539529338880000*B^54*X + 412268018644075012207031250000*B^53*X^4 + 94020428583792234375000000000*B^53*X^3 - 296532940398105600000000000*B^53*X^2 + 46361616178866447974400000*B^53*X - 132379639014152526855468750000*B^52*X^4 - 30223910438540437500000000000*B^52*X^3 - 118771750932211440000000000*B^52*X^2 - 122150570375715943219200000*B^52*X + 18911377002021789550781250000*B^51*X^4 + 4332245137376015625000000000*B^51*X^3 + 392027977198372200000000000*B^51*X^2 + 218956192174373511168000000*B^51*X - 3748362411328125000000000*B^50*X^3 - 510974919637177875000000000*B^50*X^2 - 279369103090942356480000000*B^50*X + 463867345126678125000000000*B^49*X^2 + 254639041377676416000000000*B^49*X - 296120630494921875000000000*B^48*X^2 - 162554821488432000000000000*B^48*X + 126094911517078125000000000*B^47*X^2 + 69219546770517120000000000*B^47*X - 32235916737421875000000000*B^46*X^2 - 17695841326588800000000000*B^46*X + 3748362411328125000000000*B^45*X^2 + 2057655968208000000000000*B^45*X) * hB

theorem A_Leq : A_L = C (-15353292436800000 : ℚ) * X ^ 2 + C (-8428158845779968 : ℚ) * X ^ 1 := mul_left_cancel₀ (ne0 45 12) A_Lmul

theorem rec (n : ℕ) (hn : 3 ≤ n) :
    (114950395322695680 * (n : ℤ) ^ 5 - 377276349328392192 * (n : ℤ) ^ 4 + 386304531300876288 * (n : ℤ) ^ 3 - 151611494548242432 * (n : ℤ) ^ 2 + 19204758407282688 * (n : ℤ)) * a n
      + (-1790957827072000000 * (n : ℤ) ^ 5 + 1308519543040000000 * (n : ℤ) ^ 4 + 22616523408793600000 * (n : ℤ) ^ 3 - 62679181021343680000 * (n : ℤ) ^ 2 + 63362633880767942400 * (n : ℤ) - 22883218362691061760) * a (n - 1)
      + (-7662274775000000000 * (n : ℤ) ^ 5 + 180996222379062500000 * (n : ℤ) ^ 4 - 965187374383281250000 * (n : ℤ) ^ 3 + 2184368596074484375000 * (n : ℤ) ^ 2 - 2294070913831721250000 * (n : ℤ) + 924898019298647625000) * a (n - 2)
      + (151313589324951171875 * (n : ℤ) ^ 5 - 1718149467437744140625 * (n : ℤ) ^ 4 + 7709263982635498046875 * (n : ℤ) ^ 3 - 17048950212786865234375 * (n : ℤ) ^ 2 + 18527093871578613281250 * (n : ℤ) - 7880393770076953125000) * a (n - 3) = 0 := by
  have h := congrArg (coeff n) A_Leq
  unfold A_L at h
  simp only [map_add, coeff_X_pow_mul', coeff_C_mul, coeff_th, coeff_X_pow, show 0 ≤ n by omega,
    show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true, Nat.sub_zero,
    show n ≠ 1 by omega, show n ≠ 2 by omega, if_false, mul_zero, add_zero] at h
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n)] at h
  rw [← a_eq, ← a_eq, ← a_eq, ← a_eq] at h
  push_cast at h
  have key : ((114950395322695680 * (n : ℤ) ^ 5 - 377276349328392192 * (n : ℤ) ^ 4 + 386304531300876288 * (n : ℤ) ^ 3 - 151611494548242432 * (n : ℤ) ^ 2 + 19204758407282688 * (n : ℤ)) * a n
      + (-1790957827072000000 * (n : ℤ) ^ 5 + 1308519543040000000 * (n : ℤ) ^ 4 + 22616523408793600000 * (n : ℤ) ^ 3 - 62679181021343680000 * (n : ℤ) ^ 2 + 63362633880767942400 * (n : ℤ) - 22883218362691061760) * a (n - 1)
      + (-7662274775000000000 * (n : ℤ) ^ 5 + 180996222379062500000 * (n : ℤ) ^ 4 - 965187374383281250000 * (n : ℤ) ^ 3 + 2184368596074484375000 * (n : ℤ) ^ 2 - 2294070913831721250000 * (n : ℤ) + 924898019298647625000) * a (n - 2)
      + (151313589324951171875 * (n : ℤ) ^ 5 - 1718149467437744140625 * (n : ℤ) ^ 4 + 7709263982635498046875 * (n : ℤ) ^ 3 - 17048950212786865234375 * (n : ℤ) ^ 2 + 18527093871578613281250 * (n : ℤ) - 7880393770076953125000) * a (n - 3) : ℤ) = ((0 : ℤ) : ℚ) := by
    push_cast
    linear_combination h
  exact_mod_cast key

end OMA.Helpers_a386566

theorem OMA.solution : type_of% @OMA.S_oeis_a386566.main := OMA.Helpers_a386566.rec

