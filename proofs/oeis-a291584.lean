import OMAStatements.S_oeis_a291584
import Mathlib

namespace OMA.S_oeis_a291584

open Finset PowerSeries

private theorem large_value (n d : ℕ) (hn : 0 < n) (hd : 8 < d) :
    val n 8 8 d = 1 := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hmq : (8 : ℚ) ≤ d := by exact_mod_cast hd.le
  have hc : ⌈(8 : ℚ) / (d : ℚ)⌉ = 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · simpa using div_pos (by norm_num : (0 : ℚ) < 8) hdq
    · simpa using (div_le_iff₀ hdq).mpr (by simpa using hmq)
  have hguard : (8 : ℤ) ≤ min 8 ((d : ℤ) - 1) := le_min le_rfl (by omega)
  have hdn : (1 : ℤ) ≤ d := by omega
  have hnn : (1 : ℤ) ≤ n := by omega
  norm_num [val, hc, hguard, min_eq_right hdn, min_eq_right hnn]

private theorem small_value (n d : ℕ) (hd : 0 < d) (hbound : d ≤ 8) :
    val n 8 8 d = min (n : ℤ) (if d ∣ 8 then 2 - (d : ℤ) else 1) := by
  interval_cases d
  · have hc : ⌈(8 : ℚ) / 1⌉ = 8 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(8 : ℚ) / 2⌉ = 4 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(8 : ℚ) / 3⌉ = 3 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(8 : ℚ) / 4⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(8 : ℚ) / 5⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(8 : ℚ) / 6⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(8 : ℚ) / 7⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(8 : ℚ) / 8⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]

private theorem divisor_value (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    val n 8 8 d = if d ∣ 8 then 2 - (d : ℤ) else 1 := by
  by_cases h : 8 < d
  · have hnmod : ¬ d ∣ 8 := fun h' => h.not_ge (Nat.le_of_dvd (by decide) h')
    rw [large_value n d hn h, if_neg hnmod]
  · rw [small_value n d hd (by omega)]
    split_ifs <;> exact min_eq_right (by omega)

private theorem closed (n : ℕ) (hn : 0 < n) :
    a n = 2 - (Nat.gcd n 8 : ℤ) := by
  have hp : 0 < Nat.gcd n 8 := Nat.gcd_pos_of_pos_left 8 hn
  have hne : n ≠ 0 := by omega
  unfold a uhat
  apply le_antisymm
  · rw [fold_min_le]
    refine Or.inr ⟨n.gcd 8, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n 8, hne⟩, ?_⟩
    rw [divisor_value n _ hn hp, if_pos (Nat.gcd_dvd_right n 8)]
  · rw [le_fold_min]
    refine ⟨by omega, ?_⟩
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    rw [divisor_value n d hn (Nat.pos_of_dvd_of_pos hdvd hn)]
    by_cases h : d ∣ 8
    · have hle := Nat.le_of_dvd hp (Nat.dvd_gcd hdvd h)
      rw [if_pos h]
      omega
    · rw [if_neg h]
      omega

private theorem period (n : ℕ) (hn : 8 < n) : a n = a (n - 8) := by
  rw [closed n (by omega), closed (n - 8) (by omega), Nat.gcd_sub_self_left (by omega)]

set_option maxHeartbeats 1500000 in
private theorem series_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 8 - 1) =
      X * (6 * X ^ 7 - X ^ 6 - X ^ 4 + 2 * X ^ 3 - X ^ 2 - 1) := by
  have hp : (X * (6 * X ^ 7 - X ^ 6 - X ^ 4 + 2 * X ^ 3 - X ^ 2 - 1) : ℤ⟦X⟧) = C 6 * X ^ 8 - X ^ 7 - X ^ 5 + C 2 * X ^ 4 - X ^ 3 - X ^ 1 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [hp]
  ext n
  simp only [mul_sub, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_C,
    coeff_mk, coeff_X_pow]
  by_cases hn : 8 < n
  · have hge : 8 ≤ n := by omega
    have h0 : n ≠ 0 := by omega
    have hz : n - 8 ≠ 0 := by omega
    have h4ge : 4 ≤ n := by omega
    have hz4 : n - 4 ≠ 0 := by omega
    have h1: n ≠ 1 := by omega
    have h2: n ≠ 2 := by omega
    have h3: n ≠ 3 := by omega
    have h4: n ≠ 4 := by omega
    have h5: n ≠ 5 := by omega
    have h6: n ≠ 6 := by omega
    have h7: n ≠ 7 := by omega
    have h8: n ≠ 8 := by omega
    simpa only [if_pos hge, if_pos h4ge, if_neg hz4, if_neg h0, if_neg hz, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
      mul_zero, neg_zero, add_zero, sub_zero] using sub_eq_zero.mpr (period n hn).symm
  · interval_cases n <;> norm_num [closed, Nat.gcd, constantCoeff_C]

end OMA.S_oeis_a291584

open OMA.S_oeis_a291584 in
theorem OMA.solution : type_of% @OMA.S_oeis_a291584.main := by
  exact ⟨period, series_identity⟩