import OMAStatements.S_oeis_a025758
import Mathlib

namespace OMA.Helpers_a025758
open OMA.S_oeis_a025758 PowerSeries


theorem B_pow (k : ℕ) : (PowerSeries.binomialSeries ℚ (1/5 : ℚ)) ^ k =
    PowerSeries.binomialSeries ℚ ((k : ℚ) / 5) := by
  induction k with
  | zero => simp [PowerSeries.binomialSeries_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← PowerSeries.binomialSeries_add]
    congr 1; push_cast; ring

theorem hT5 : T ^ 5 = 1 - 25 * X := by
  unfold T H
  rw [← map_pow, B_pow]
  rw [show ((5 : ℕ) : ℚ) / 5 = ((1 : ℕ) : ℚ) by norm_num, PowerSeries.binomialSeries_nat]
  simp only [pow_one, map_add, map_one, rescale_X, map_neg, map_ofNat]
  ring

theorem Dnum (k : ℕ) [k.AtLeastTwo] : (d⁄dX ℚ) (no_index (OfNat.ofNat k : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C k]; exact derivative_C

theorem inv5 : C (1 / 5 : ℚ) * (5 : ℚ⟦X⟧) = 1 := by
  rw [← map_ofNat C 5, ← map_mul]; norm_num

theorem hT1 : (1 - 25 * X) * (d⁄dX ℚ) T = -5 * T := by
  have h := congrArg (d⁄dX ℚ) hT5
  simp only [derivative_pow, map_sub, derivative_one, Derivation.leibniz, smul_eq_mul, derivative_X,
    Dnum] at h
  push_cast at h
  have h5 : (5 : ℚ⟦X⟧) * ((1 - 25 * X) * (d⁄dX ℚ) T - -5 * T) = 0 := by
    linear_combination (-5 * (d⁄dX ℚ) T) * hT5 + T * h
  have := congrArg (fun F => C (1 / 5 : ℚ) * F) h5
  simp only [← mul_assoc, inv5, one_mul, mul_zero] at this
  linear_combination this

theorem cT : constantCoeff T = 1 := by
  unfold T H
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
    PowerSeries.binomialSeries_constantCoeff]
  simp

theorem hG : (4 + T) * G = 5 := by
  unfold G
  rw [mul_comm (5 : ℚ⟦X⟧), ← mul_assoc, PowerSeries.mul_inv_cancel, one_mul]
  rw [map_add, cT, map_ofNat]; norm_num

theorem h0 : (4 + T) * G = 5 := hG

theorem h1 : (1 - 25 * X) ^ 1 * (4 + T) ^ 2 * ((d⁄dX ℚ) G) = 25*T := by
  have dh := congrArg (d⁄dX ℚ) h0
  simp only [Derivation.leibniz, map_add, smul_eq_mul,
    Dnum] at dh
  push_cast at dh
  linear_combination (1 - 25 * X) * (4 + T) * dh + (0 * (4 + T) + 5 * T) * h0 + ((4 + T) * (0) - 1 * (4 + T) * G) * hT1

theorem h2 : (1 - 25 * X) ^ 2 * (4 + T) ^ 3 * ((d⁄dX ℚ) ((d⁄dX ℚ) G)) = 750*T^2 + 2000*T := by
  have dh := congrArg (d⁄dX ℚ) h1
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul,
    nsmul_eq_mul, derivative_X, Dnum, derivative_one] at dh
  push_cast at dh
  linear_combination (1 - 25 * X) * (4 + T) * dh + (25 * (4 + T) + 10 * T) * h1 + ((4 + T) * (25) - 2 * (1 - 25 * X) ^ 1 * (4 + T) ^ 2 * ((d⁄dX ℚ) G)) * hT1

theorem h3 : (1 - 25 * X) ^ 3 * (4 + T) ^ 4 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) G))) = 41250*T^3 + 240000*T^2 + 360000*T := by
  have dh := congrArg (d⁄dX ℚ) h2
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul,
    nsmul_eq_mul, derivative_X, Dnum, derivative_one] at dh
  push_cast at dh
  linear_combination (1 - 25 * X) * (4 + T) * dh + (50 * (4 + T) + 15 * T) * h2 + ((4 + T) * (1500*T + 2000) - 3 * (1 - 25 * X) ^ 2 * (4 + T) ^ 3 * ((d⁄dX ℚ) ((d⁄dX ℚ) G))) * hT1

theorem h4 : (1 - 25 * X) ^ 4 * (4 + T) ^ 5 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) G)))) = 3300000*T^4 + 30300000*T^3 + 94800000*T^2 + 100800000*T := by
  have dh := congrArg (d⁄dX ℚ) h3
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub, smul_eq_mul,
    nsmul_eq_mul, derivative_X, Dnum, derivative_one] at dh
  push_cast at dh
  linear_combination (1 - 25 * X) * (4 + T) * dh + (75 * (4 + T) + 20 * T) * h3 + ((4 + T) * (123750*T^2 + 480000*T + 360000) - 4 * (1 - 25 * X) ^ 3 * (4 + T) ^ 4 * ((d⁄dX ℚ) ((d⁄dX ℚ) ((d⁄dX ℚ) G)))) * hT1

noncomputable def th (F : ℚ⟦X⟧) : ℚ⟦X⟧ := X * (d⁄dX ℚ) F

theorem coeff_th (F : ℚ⟦X⟧) (k : ℕ) : coeff k (th F) = (k : ℚ) * coeff k F := by
  unfold th
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

noncomputable def LG : ℚ⟦X⟧ := X ^ 0 * (C (-246 : ℚ) * th (G) + C (451 : ℚ) * th (th (G)) + C (-246 : ℚ) * th (th (th (G))) + C (41 : ℚ) * th (th (th (th (G))))) + X ^ 1 * (C (16398 : ℚ) * th (G) + C (-32799 : ℚ) * th (th (G)) + C (20502 : ℚ) * th (th (th (G))) + C (-4101 : ℚ) * th (th (th (th (G))))) + X ^ 2 * (C (-368900 : ℚ) * th (G) + C (830150 : ℚ) * th (th (G)) + C (-615100 : ℚ) * th (th (th (G))) + C (153850 : ℚ) * th (th (th (th (G))))) + X ^ 3 * (C (3073500 : ℚ) * th (G) + C (-8197750 : ℚ) * th (th (G)) + C (7687500 : ℚ) * th (th (th (G))) + C (-2566250 : ℚ) * th (th (th (th (G))))) + X ^ 4 * (C (615000 : ℚ) * G + C (-6393750 : ℚ) * th (G) + C (22434375 : ℚ) * th (th (G)) + C (-31968750 : ℚ) * th (th (th (G))) + C (16078125 : ℚ) * th (th (th (th (G))))) + X ^ 5 * (C (-15000 : ℚ) * G + C (-156250 : ℚ) * th (G) + C (-546875 : ℚ) * th (th (G)) + C (-781250 : ℚ) * th (th (th (G))) + C (-390625 : ℚ) * th (th (th (th (G)))))

theorem LG_mul : (1 - 25 * X) ^ 4 * (4 + T) ^ 5 * LG = (1 - 25 * X) ^ 4 * (4 + T) ^ 5 * (768000 * X ^ 4) := by
  unfold LG th
  simp only [Derivation.leibniz, map_add, smul_eq_mul, derivative_X, map_neg, map_ofNat,
    pow_zero, one_mul, mul_one]
  linear_combination (-5859375000*T^4*X^9 + 241171875000*T^4*X^8 - 38493750000*T^4*X^7 + 2307750000*T^4*X^6 - 61515000*T^4*X^5 + 615000*T^4*X^4 - 93750000000*T^3*X^9 + 3858750000000*T^3*X^8 - 615900000000*T^3*X^7 + 36924000000*T^3*X^6 - 984240000*T^3*X^5 + 9840000*T^3*X^4 - 562500000000*T^2*X^9 + 23152500000000*T^2*X^8 - 3695400000000*T^2*X^7 + 221544000000*T^2*X^6 - 5905440000*T^2*X^5 + 59040000*T^2*X^4 - 1500000000000*T*X^9 + 61740000000000*T*X^8 - 9854400000000*T*X^7 + 590784000000*T*X^6 - 15747840000*T*X^5 + 157440000*T*X^4 - 1500000000000*X^9 + 61740000000000*X^8 - 9854400000000*X^7 + 590784000000*X^6 - 15747840000*X^5 + 157440000*X^4) * h0 + (29296875000*T^3*X^9 - 5859375000*T^3*X^8 + 468750000*T^3*X^7 - 18750000*T^3*X^6 + 375000*T^3*X^5 - 3000*T^3*X^4 + 351562500000*T^2*X^9 - 70312500000*T^2*X^8 + 5625000000*T^2*X^7 - 225000000*T^2*X^6 + 4500000*T^2*X^5 - 36000*T^2*X^4 + 1406250000000*T*X^9 - 281250000000*T*X^8 + 22500000000*T*X^7 - 900000000*T*X^6 + 18000000*T*X^5 - 144000*T*X^4 + 1875000000000*X^9 - 375000000000*X^8 + 30000000000*X^7 - 1200000000*X^6 + 24000000*X^5 - 192000*X^4) * h1 + (-3515625000*T^2*X^9 + 24703125000*T^2*X^8 - 3896250000*T^2*X^7 + 232650000*T^2*X^6 - 6189000*T^2*X^5 + 61800*T^2*X^4 - 28125000000*T*X^9 + 197625000000*T*X^8 - 31170000000*T*X^7 + 1861200000*T*X^6 - 49512000*T*X^5 + 494400*T*X^4 - 56250000000*X^9 + 395250000000*X^8 - 62340000000*X^7 + 3722400000*X^6 - 99024000*X^5 + 988800*X^4) * h2 + (78125000*T*X^9 - 1615625000*T*X^8 + 257250000*T*X^7 - 15410000*T*X^6 + 410600*T*X^5 - 4104*T*X^4 + 312500000*X^9 - 6462500000*X^8 + 1029000000*X^7 - 61640000*X^6 + 1642400*X^5 - 16416*X^4) * h3 + (-390625*X^9 + 16078125*X^8 - 2566250*X^7 + 153850*X^6 - 4101*X^5 + 41*X^4) * h4 + (-300000000000*X^8 + 48000000000*X^7 - 2880000000*X^6 + 76800000*X^5 - 768000*X^4) * hT5

theorem ne0 : (1 - 25 * X) ^ 4 * (4 + T) ^ 5 ≠ (0 : ℚ⟦X⟧) := by
  intro h
  have := congrArg constantCoeff h
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, constantCoeff_X, cT, map_zero] at this
  norm_num at this

theorem LG_eq : LG = 768000 * X ^ 4 := mul_left_cancel₀ ne0 LG_mul

theorem rec (n : ℕ) (hn : 5 ≤ n) :
    41*(n : ℚ)*((n : ℚ)-1)*((n : ℚ)-2)*((n : ℚ)-3)*a n -
      3*(1367*(n : ℚ)-4100)*((n : ℚ)-1)*((n : ℚ)-2)*((n : ℚ)-3)*a (n-1) +
      50*((n : ℚ)-2)*((n : ℚ)-3)*(3077*(n : ℚ)^2-21533*(n : ℚ)+38136)*a (n-2) -
      250*((n : ℚ)-3)*(10265*(n : ℚ)^3-123135*(n : ℚ)^2+494446*(n : ℚ)-664572)*a (n-3) +
      1875*(8575*(n : ℚ)^4-154250*(n : ℚ)^3+1039765*(n : ℚ)^2-3112730*(n : ℚ)+3491808)*a (n-4) -
      625*(5*(n : ℚ)-22)*(5*(n : ℚ)-21)*(5*(n : ℚ)-24)*(5*(n : ℚ)-23)*a (n-5) = 0 := by
  have h := congrArg (coeff n) LG_eq
  unfold LG at h
  simp only [map_add, coeff_X_pow_mul', coeff_C_mul, coeff_th, show 0 ≤ n by omega, show 1 ≤ n by omega,
    show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, if_true,
    Nat.sub_zero] at h
  rw [← map_ofNat C 768000, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero] at h
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_sub (by omega : 3 ≤ n),
    Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 5 ≤ n)] at h
  simp only [a]
  push_cast at h
  linear_combination h

end OMA.Helpers_a025758

theorem OMA.solution : type_of% @OMA.S_oeis_a025758.main := OMA.Helpers_a025758.rec

