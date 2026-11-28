import OMAStatements.S_oeis_a381363
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a381363

open OMA.S_oeis_a381363

theorem solution : type_of% @OMA.S_oeis_a381363.main := by
  intro A hA0 hEq
  -- Step 1: Prove by strong induction that coeff r (A + 1) is even for all r ≥ 0!
  have heven : ∀ r : ℕ, 2 ∣ PowerSeries.coeff r (A + 1) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      have hr := hEq r
      cases r with
      | zero =>
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add, hA0, map_one]
        decide
      | succ m =>
        conv_lhs at hr =>
          rw [add_mul, one_mul, map_add, ← pow_one (PowerSeries.X : PowerSeries ℤ),
              PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]
        rw [if_neg (by omega), zero_add] at hr
        have hih := ih m (by omega)
        rcases hih with ⟨q, hq⟩
        refine ⟨(∑ n ∈ Finset.Icc 1 (m + 1),
          PowerSeries.coeff (m + 1)
            ((1 + PowerSeries.X) * (A + 1) *
              (PowerSeries.X ^ n * A ^ n * (A ^ n + PowerSeries.X) ^ (3 * n - 1) *
                  (A + PowerSeries.X ^ n) ^ (3 * n - 1) +
                PowerSeries.X ^ (3 * n ^ 2) * A ^ (3 * n ^ 2) *
                  (Ring.inverse (1 + PowerSeries.X * A ^ n)) ^ (3 * n + 1) *
                  (Ring.inverse (1 + PowerSeries.X ^ n * A)) ^ (3 * n + 1)))) - q, ?_⟩
        linarith
  -- Step 2: Therefore every term (1 + X) * (A + 1) * (...) has even coefficients,
  -- so 2 * ∑ ... is divisible by 4!
  have h4sum : ∀ r : ℕ, (4 : ℤ) ∣ 2 * ∑ n ∈ Finset.Icc 1 r,
      PowerSeries.coeff r
        ((1 + PowerSeries.X) * (A + 1) *
          (PowerSeries.X ^ n * A ^ n * (A ^ n + PowerSeries.X) ^ (3 * n - 1) *
              (A + PowerSeries.X ^ n) ^ (3 * n - 1) +
            PowerSeries.X ^ (3 * n ^ 2) * A ^ (3 * n ^ 2) *
              (Ring.inverse (1 + PowerSeries.X * A ^ n)) ^ (3 * n + 1) *
              (Ring.inverse (1 + PowerSeries.X ^ n * A)) ^ (3 * n + 1))) := by
    intro r
    have h2 : (2 : ℤ) ∣ ∑ n ∈ Finset.Icc 1 r,
        PowerSeries.coeff r
          ((1 + PowerSeries.X) * (A + 1) *
            (PowerSeries.X ^ n * A ^ n * (A ^ n + PowerSeries.X) ^ (3 * n - 1) *
                (A + PowerSeries.X ^ n) ^ (3 * n - 1) +
              PowerSeries.X ^ (3 * n ^ 2) * A ^ (3 * n ^ 2) *
                (Ring.inverse (1 + PowerSeries.X * A ^ n)) ^ (3 * n + 1) *
                (Ring.inverse (1 + PowerSeries.X ^ n * A)) ^ (3 * n + 1))) := by
      refine Finset.dvd_sum fun n _ => ?_
      rw [mul_assoc, mul_comm (1 + PowerSeries.X), mul_assoc, PowerSeries.coeff_mul]
      refine Finset.dvd_sum fun p _ => dvd_mul_of_dvd_left (heven p.1) _
    rcases h2 with ⟨q, hq⟩
    exact ⟨q, by linarith⟩
  -- Step 3: Now coeff r ((1 + X) * (A + 1)) ≡ 0 (mod 4) for all r ≥ 1,
  -- so coeff (m + 1) (A + 1) + coeff m (A + 1) ≡ 0 (mod 4), hence coeff r (A + 1) ≡ 2 (mod 4) for all r ≥ 0!
  have hmod4 : ∀ r : ℕ, PowerSeries.coeff r (A + 1) % 4 = 2 := by
    intro r
    induction r with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_add, hA0, map_one]; decide
    | succ m ih =>
      have hr := hEq (m + 1)
      conv_lhs at hr =>
        rw [add_mul, one_mul, map_add, ← pow_one (PowerSeries.X : PowerSeries ℤ),
            PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]
      rw [if_neg (by omega), zero_add] at hr
      rcases h4sum (m + 1) with ⟨q, hq⟩
      omega
  intro r hr
  have h := hmod4 r
  rw [map_add, PowerSeries.coeff_one, if_neg (by omega), add_zero] at h
  exact h

end OMA.P_oeis_a381363

theorem OMA.solution : type_of% @OMA.S_oeis_a381363.main := OMA.P_oeis_a381363.solution
