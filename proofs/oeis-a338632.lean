import OMAStatements.S_oeis_a338632
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a338632

open OMA.S_oeis_a338632

private lemma odd_mod4 (k : ℕ) :
    ((2 * k + 3 : ℕ) : ZMod 4) = if Even k then 3 else 1 := by
  by_cases h : Even k
  · rw [if_pos h]
    rcases h with ⟨m, rfl⟩
    have hmod : (2 * (m + m) + 3) % 4 = 3 := by omega
    rw [← ZMod.natCast_mod, hmod]; rfl
  · rw [if_neg h]
    have hodd : k % 2 = 1 := by
      by_contra hne; exact h ⟨k / 2, by omega⟩
    have hmod : (2 * k + 3) % 4 = 1 := by omega
    rw [← ZMod.natCast_mod, hmod]; rfl

theorem solution : type_of% @OMA.S_oeis_a338632.main := by
  intro A hA0 ⟨R, hR0, hRk⟩
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 4) := PowerSeries.map (Int.castRingHom (ZMod 4))
  let a4 : PowerSeries (ZMod 4) := φ A
  let r : ℕ → PowerSeries (ZMod 4) := fun k => φ (R k)
  have ha4_0 : PowerSeries.constantCoeff a4 = 1 := by
    dsimp only [a4, φ]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_one]
  have ha4_eq : a4 = 1 + PowerSeries.X * r 0 := by
    have h := congrArg φ hR0
    rw [map_sub, map_one, map_mul, PowerSeries.map_X] at h
    exact eq_add_of_sub_eq' h
  have hrk_eq : ∀ k : ℕ,
      r k * (if Even k then a4 + PowerSeries.X * r (k + 1) else a4 - PowerSeries.X * r (k + 1)) = 1 := by
    intro k
    have h := congrArg φ (hRk k)
    rw [map_mul, map_sub, map_mul, map_mul, PowerSeries.map_X, map_one] at h
    have hc : φ (((2 * k + 3 : ℕ) : PowerSeries ℤ)) =
        PowerSeries.C (if Even k then (3 : ZMod 4) else 1) := by
      rw [map_natCast, ← map_natCast (PowerSeries.C (R := ZMod 4)), odd_mod4]
    rw [hc] at h
    by_cases hk : Even k
    · rw [if_pos hk] at h ⊢
      have h3 : (PowerSeries.C (3 : ZMod 4)) = -1 := by
        rw [← map_one PowerSeries.C, ← map_neg]; congr 1
      rw [h3, neg_mul, one_mul, neg_mul, sub_neg_eq_add] at h
      exact h
    · rw [if_neg hk] at h ⊢
      rw [map_one, one_mul] at h
      exact h
  have hr_coeff : ∀ n : ℕ, ∀ k : ℕ,
      PowerSeries.coeff n (r k) = if n = 0 then 1 else if Even k then 2 else 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k
      cases n with
      | zero =>
        rw [if_pos rfl]
        have h := congrArg PowerSeries.constantCoeff (hrk_eq k)
        by_cases hk : Even k
        · rw [if_pos hk, map_mul, map_add, map_mul, PowerSeries.constantCoeff_X, zero_mul,
              add_zero, ha4_0, mul_one, map_one] at h
          rw [PowerSeries.coeff_zero_eq_constantCoeff, h]
        · rw [if_neg hk, map_mul, map_sub, map_mul, PowerSeries.constantCoeff_X, zero_mul,
              sub_zero, ha4_0, mul_one, map_one] at h
          rw [PowerSeries.coeff_zero_eq_constantCoeff, h]
      | succ m =>
        rw [if_neg (by omega)]
        have h := congrArg (PowerSeries.coeff (m + 1)) (hrk_eq k)
        rw [PowerSeries.coeff_one, if_neg (by omega : m + 1 ≠ 0)] at h
        by_cases hk : Even k
        · rw [if_pos hk] at h ⊢
          rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => PowerSeries.coeff i (r k) * PowerSeries.coeff j (a4 + PowerSeries.X * r (k + 1)))] at h
          rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h
          have hhk1 : ¬ Even (k + 1) := by
            rcases hk with ⟨j, rfl⟩; rintro ⟨t, ht⟩; omega
          have hterm_j : ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 →
              PowerSeries.coeff j (a4 + PowerSeries.X * r (k + 1)) = 2 := by
            intro j hj1 hjm
            rw [map_add, ← pow_one (PowerSeries.X : PowerSeries (ZMod 4)),
                PowerSeries.coeff_X_pow_mul', if_pos hj1]
            have ha_val : PowerSeries.coeff j a4 = PowerSeries.coeff (j - 1) (r 0) := by
              rw [ha4_eq, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
                  ← pow_one (PowerSeries.X : PowerSeries (ZMod 4)), PowerSeries.coeff_X_pow_mul',
                  if_pos hj1]
            rw [ha_val, ih (j - 1) (by omega) 0, ih (j - 1) (by omega) (k + 1)]
            by_cases hj : j - 1 = 0
            · rw [if_pos hj, if_pos hj]; decide
            · rw [if_neg hj, if_neg hj, if_pos (by decide : Even 0), if_neg hhk1]; decide
          have hmid : ∑ i ∈ Finset.range m,
              PowerSeries.coeff (i + 1) (r k) *
                PowerSeries.coeff (m + 1 - (i + 1)) (a4 + PowerSeries.X * r (k + 1)) = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            rw [Finset.mem_range] at hi
            rw [ih (i + 1) (by omega) k, if_neg (by omega), if_pos hk,
                hterm_j (m + 1 - (i + 1)) (by omega) (by omega)]
            decide
          rw [hmid, zero_add, Nat.sub_zero, Nat.sub_self,
              ih 0 (by omega) k, if_pos rfl, hterm_j (m + 1) (by omega) le_rfl, one_mul,
              PowerSeries.coeff_zero_eq_constantCoeff, map_add, map_mul,
              PowerSeries.constantCoeff_X, zero_mul, add_zero, ha4_0, mul_one] at h
          have hsolve : ∀ x : ZMod 4, 2 + x = 0 → x = 2 := by decide
          exact hsolve _ h
        · rw [if_neg hk] at h ⊢
          rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => PowerSeries.coeff i (r k) * PowerSeries.coeff j (a4 - PowerSeries.X * r (k + 1)))] at h
          rw [Finset.sum_range_succ] at h
          have hhk1 : Even (k + 1) := by
            have hodd : k % 2 = 1 := by by_contra hne; exact hk ⟨k / 2, by omega⟩
            exact ⟨k / 2 + 1, by omega⟩
          have hlow : ∑ i ∈ Finset.range (m + 1),
              PowerSeries.coeff i (r k) *
                PowerSeries.coeff (m + 1 - i) (a4 - PowerSeries.X * r (k + 1)) = 0 := by
            refine Finset.sum_eq_zero fun i hi => ?_
            rw [Finset.mem_range] at hi
            have hsub : PowerSeries.coeff (m + 1 - i) (a4 - PowerSeries.X * r (k + 1)) = 0 := by
              rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries (ZMod 4)),
                  PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
              have ha_val : PowerSeries.coeff (m + 1 - i) a4 =
                  PowerSeries.coeff (m + 1 - i - 1) (r 0) := by
                rw [ha4_eq, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
                    ← pow_one (PowerSeries.X : PowerSeries (ZMod 4)), PowerSeries.coeff_X_pow_mul',
                    if_pos (by omega)]
              rw [ha_val, ih (m + 1 - i - 1) (by omega) 0, ih (m + 1 - i - 1) (by omega) (k + 1)]
              by_cases hj : m + 1 - i - 1 = 0
              · rw [if_pos hj, if_pos hj, sub_self]
              · rw [if_neg hj, if_neg hj, if_pos (by decide : Even 0), if_pos hhk1, sub_self]
            rw [hsub, mul_zero]
          rw [hlow, zero_add, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff,
              map_sub, map_mul, PowerSeries.constantCoeff_X, zero_mul, sub_zero, ha4_0, mul_one] at h
          exact h
  intro n hn
  have h2 : ((PowerSeries.coeff n A : ℤ) : ZMod 4) = 2 := by
    have h1 : ((PowerSeries.coeff n A : ℤ) : ZMod 4) = PowerSeries.coeff n a4 := by
      dsimp only [a4, φ]; rw [PowerSeries.coeff_map]; rfl
    rw [h1, ha4_eq, map_add, PowerSeries.coeff_one, if_neg (by omega), zero_add,
        ← pow_one (PowerSeries.X : PowerSeries (ZMod 4)), PowerSeries.coeff_X_pow_mul',
        if_pos (by omega), hr_coeff (n - 1) 0, if_neg (by omega), if_pos (by decide : Even 0)]
  have hdvd : ((4 : ℕ) : ℤ) ∣ PowerSeries.coeff n A - 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h2]; decide
  rcases hdvd with ⟨q, hq⟩
  norm_num at hq
  omega

end OMA.P_oeis_a338632

theorem OMA.solution : type_of% @OMA.S_oeis_a338632.main := OMA.P_oeis_a338632.solution
