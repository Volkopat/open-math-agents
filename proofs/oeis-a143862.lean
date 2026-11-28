import OMAStatements.S_oeis_a143862

-- uses note #98035
-- Companion proof by Heart-galaxy, published in statement PR 21609.
-- Rechecked and assembled for the registered statement without a novelty claim.

namespace OMA.S_oeis_a143862

open PowerSeries
open scoped BigOperators PowerSeries.WithPiTopology

private theorem one_sub_X_pow_const {d : ℕ} (hd : 0 < d) :
    constantCoeff (1 - X ^ d : PowerSeries ℚ) = 1 := by
  simp [Nat.ne_of_gt hd]

private theorem summand_expand {d : ℕ} (hd : 0 < d) :
    summand d = expand d hd.ne' (X ^ d * (invOneSubPow ℚ d).val) := by
  have hunit : (1 - X : PowerSeries ℚ) ^ d * (invOneSubPow ℚ d).val = 1 := by
    rw [← invOneSubPow_inv_eq_one_sub_pow]
    exact (invOneSubPow ℚ d).inv_val
  have hmap := congrArg (expand d hd.ne') hunit
  simp only [map_mul, map_pow, map_sub, map_one, expand_X] at hmap
  have hconst : constantCoeff (1 - X ^ d : PowerSeries ℚ) ≠ 0 :=
    (one_sub_X_pow_const hd).symm ▸ one_ne_zero
  have hzero : (1 - X ^ d : PowerSeries ℚ) ≠ 0 := by
    intro h
    exact hconst (h ▸ map_zero constantCoeff)
  have hinv : ((1 - X ^ d : PowerSeries ℚ)⁻¹) ^ d =
      expand d hd.ne' (invOneSubPow ℚ d).val := by
    apply mul_left_cancel₀ (a := (1 - X ^ d : PowerSeries ℚ) ^ d) (pow_ne_zero _ hzero)
    rw [← mul_pow, PowerSeries.mul_inv_cancel _ hconst, one_pow, hmap]
  rw [summand, if_neg hd.ne', mul_pow, map_mul, map_pow, expand_X, hinv]

private theorem coeff_summand_zero (d : ℕ) : coeff 0 (summand d) = 0 := by
  by_cases hd : d = 0
  · simp [summand, hd]
  · have hp : 0 < d := Nat.pos_of_ne_zero hd
    rw [summand, if_neg hd, mul_pow, ← pow_mul, coeff_X_pow_mul']
    simp [Nat.ne_of_gt (Nat.mul_pos hp hp)]

private theorem coeff_summand_pos {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    coeff m (summand d) = if d ∣ m then ((m / d - 1).choose (d - 1) : ℚ) else 0 := by
  rw [summand_expand hd, coeff_expand]
  split_ifs with hdiv
  · rw [coeff_X_pow_mul']
    split_ifs with hle
    · rw [invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℚ d hd, coeff_mk,
        show d - 1 + (m / d - d) = m / d - 1 by omega]
    · have hpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hdiv) hd
      rw [Nat.choose_eq_zero_of_lt (show m / d - 1 < d - 1 by omega), Nat.cast_zero]
  · rfl

private theorem hasSum_coeff_summand (m : ℕ) :
    HasSum (fun d : ℕ => coeff m (summand d)) (coeff m (generatingFunction - 1)) := by
  by_cases hm : m = 0
  · subst m
    simp [coeff_summand_zero, generatingFunction, a]
  · classical
    have hp := Nat.pos_of_ne_zero hm
    have hfin : ∀ d ∉ m.divisors, coeff m (summand d) = 0 := by
      intro d hd
      by_cases hd0 : d = 0
      · simp [summand, hd0]
      · rw [coeff_summand_pos hp (Nat.pos_of_ne_zero hd0)]
        exact if_neg (fun hdiv => hd (Nat.mem_divisors.mpr ⟨hdiv, hm⟩))
    have hs : HasSum (fun d : ℕ => coeff m (summand d))
        (∑ d ∈ m.divisors, coeff m (summand d)) :=
      hasSum_sum_of_ne_finset_zero hfin
    have heq : (∑ d ∈ m.divisors, coeff m (summand d)) =
        coeff m (generatingFunction - 1) := by
      simp only [map_sub, generatingFunction, coeff_mk, coeff_one, if_neg hm, sub_zero,
        a, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [coeff_summand_pos hp (Nat.pos_of_mem_divisors hd),
        if_pos (Nat.mem_divisors.mp hd).1]
    exact heq ▸ hs

/-- Arndt's conjectured ordinary generating function, with the sum over d ≥ 1. -/
theorem complete : generatingFunction = 1 + ∑' d : ℕ, summand d := by
  have hs : HasSum summand (generatingFunction - 1) := by
    exact (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℚ).mpr hasSum_coeff_summand
  rw [hs.tsum_eq]
  abel

end OMA.S_oeis_a143862


theorem OMA.solution : type_of% @OMA.S_oeis_a143862.main :=
  OMA.S_oeis_a143862.complete
