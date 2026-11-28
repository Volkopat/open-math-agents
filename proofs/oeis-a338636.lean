import OMAStatements.S_oeis_a338636
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a338636

open OMA.S_oeis_a338636

private lemma odd_sq_mod8 (k : ℕ) : (((2 * k + 3) ^ 2 : ℕ) : ZMod 8) = 1 := by
  have h : ((2 * k + 3) ^ 2) % 8 = 1 := by
    have hmod : (2 * k + 3) % 8 = 1 ∨ (2 * k + 3) % 8 = 3 ∨
        (2 * k + 3) % 8 = 5 ∨ (2 * k + 3) % 8 = 7 := by omega
    rw [sq, Nat.mul_mod]
    rcases hmod with h1 | h1 | h1 | h1 <;> rw [h1]
  rw [← ZMod.natCast_mod, h]; rfl

theorem solution : type_of% @OMA.S_oeis_a338636.main := by
  intro A hA0 ⟨R, hR0, hRk⟩
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 8) := PowerSeries.map (Int.castRingHom (ZMod 8))
  let a8 : PowerSeries (ZMod 8) := φ A
  let r : ℕ → PowerSeries (ZMod 8) := fun k => φ (R k)
  have ha8_0 : PowerSeries.constantCoeff a8 = 1 := by
    dsimp only [a8, φ]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  have ha8_eq : a8 = 1 + PowerSeries.X * r 0 := by
    have h := congrArg φ hR0
    rw [map_sub, map_one, map_mul, PowerSeries.map_X] at h
    exact eq_add_of_sub_eq' h
  have hrk_eq : ∀ k : ℕ, r k * (a8 - PowerSeries.X * r (k + 1)) = 1 := by
    intro k
    have h := congrArg φ (hRk k)
    rw [map_mul, map_sub, map_mul, map_mul, PowerSeries.map_X, map_one] at h
    have hc : φ ((((2 * k + 3) ^ 2 : ℕ) : PowerSeries ℤ)) = 1 := by
      rw [map_natCast, ← map_natCast (PowerSeries.C (R := ZMod 8)), odd_sq_mod8, map_one]
    rw [hc, one_mul] at h
    exact h
  have hr_coeff : ∀ n : ℕ, ∀ k : ℕ, PowerSeries.coeff n (r k) = if n = 0 then 1 else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k
      cases n with
      | zero =>
        rw [if_pos rfl]
        have h := congrArg PowerSeries.constantCoeff (hrk_eq k)
        rw [map_mul, map_sub, map_mul, PowerSeries.constantCoeff_X, zero_mul, sub_zero,
            ha8_0, mul_one, map_one] at h
        rw [PowerSeries.coeff_zero_eq_constantCoeff, h]
      | succ m =>
        rw [if_neg (by omega)]
        have h := congrArg (PowerSeries.coeff (m + 1)) (hrk_eq k)
        rw [PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (r k) * PowerSeries.coeff j (a8 - PowerSeries.X * r (k + 1)))] at h
        rw [Finset.sum_range_succ] at h
        have hlow : ∑ i ∈ Finset.range (m + 1),
            PowerSeries.coeff i (r k) * PowerSeries.coeff (m + 1 - i) (a8 - PowerSeries.X * r (k + 1)) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          rw [Finset.mem_range] at hi
          have hsub : PowerSeries.coeff (m + 1 - i) (a8 - PowerSeries.X * r (k + 1)) = 0 := by
            rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries (ZMod 8)),
                PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
            have ha_val : PowerSeries.coeff (m + 1 - i) a8 =
                PowerSeries.coeff (m + 1 - i - 1) (r 0) := by
              rw [ha8_eq, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
                  ← pow_one (PowerSeries.X : PowerSeries (ZMod 8)), PowerSeries.coeff_X_pow_mul',
                  if_pos (by omega)]
            rw [ha_val, ih (m + 1 - i - 1) (by omega) 0, ih (m + 1 - i - 1) (by omega) (k + 1), sub_self]
          rw [hsub, mul_zero]
        rw [hlow, zero_add, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff,
            map_sub, map_mul, PowerSeries.constantCoeff_X, zero_mul, sub_zero, ha8_0, mul_one] at h
        exact h
  intro n hn
  have h0 : ((PowerSeries.coeff n A : ℤ) : ZMod 8) = 0 := by
    have h1 : ((PowerSeries.coeff n A : ℤ) : ZMod 8) = PowerSeries.coeff n a8 := by
      dsimp only [a8, φ]; rw [PowerSeries.coeff_map]; rfl
    rw [h1, ha8_eq, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
        ← pow_one (PowerSeries.X : PowerSeries (ZMod 8)), PowerSeries.coeff_X_pow_mul',
        if_pos (by omega), hr_coeff (n - 1) 0, if_neg (by omega)]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h0

end OMA.P_oeis_a338636

theorem OMA.solution : type_of% @OMA.S_oeis_a338636.main := OMA.P_oeis_a338636.solution
