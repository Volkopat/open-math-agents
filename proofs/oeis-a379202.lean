import OMAStatements.S_oeis_a379202
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a379202

open OMA.S_oeis_a379202

private lemma zmod2_ps_two : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← map_ofNat (PowerSeries.C (R := ZMod 2)), h, map_zero]

private lemma zmod2_ps_add_self (f : PowerSeries (ZMod 2)) : f + f = 0 := by
  rw [← two_mul, zmod2_ps_two, zero_mul]

private lemma even_of_zmod2_eq_zero (z : ℤ) (h : (z : ZMod 2) = 0) : Even z := by
  rcases Int.even_or_odd z with hev | ⟨k, rfl⟩
  · exact hev
  · push_cast at h
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add] at h
    exact absurd h (by decide)

theorem solution : type_of% @OMA.S_oeis_a379202.main := by
  intro A hA0 _hA1 hEq k hk
  apply even_of_zmod2_eq_zero
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let a2 : PowerSeries (ZMod 2) := φ A
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := zmod2_ps_two
  have h := congrArg (Int.castRingHom (ZMod 2)) (hEq k (by omega))
  rw [if_neg (by omega), zero_add, map_sum] at h
  change (Int.castRingHom (ZMod 2)) (PowerSeries.coeff k A) = 0
  rw [h]
  refine Finset.sum_eq_zero fun n _ => ?_
  have hinv_one : φ (Ring.inverse (1 + 2 * A ^ (n + 2))) = 1 := by
    have hu : IsUnit (1 + 2 * A ^ (n + 2)) := by
      apply PowerSeries.isUnit_iff_constantCoeff.mpr
      simp [map_add, map_mul, map_pow, hA0]
    have hmul : (1 + 2 * A ^ (n + 2)) * Ring.inverse (1 + 2 * A ^ (n + 2)) = 1 :=
      Ring.mul_inverse_cancel _ hu
    have hm := congrArg φ hmul
    rw [map_mul, map_add, map_one, map_mul, map_ofNat, h2, zero_mul, add_zero, one_mul] at hm
    exact hm
  have hterm : φ (A ^ (n + 1) * (A ^ n + 2) ^ (n + 1) +
      A ^ ((n + 1) ^ 2) * (Ring.inverse (1 + 2 * A ^ (n + 2))) ^ (n + 1)) = 0 := by
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
        map_add, map_pow, map_ofNat, h2, add_zero, hinv_one, one_pow, mul_one,
        ← pow_mul, ← pow_add, show (n + 1) + n * (n + 1) = (n + 1) ^ 2 by ring,
        zmod2_ps_add_self]
  rw [← PowerSeries.coeff_map, hterm, map_zero]

end OMA.P_oeis_a379202

theorem OMA.solution : type_of% @OMA.S_oeis_a379202.main := OMA.P_oeis_a379202.solution
