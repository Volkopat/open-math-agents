import OMAStatements.S_oeis_a291568
import Mathlib

namespace OMA.S_oeis_a291568

open Finset PowerSeries

private theorem large_value (n d : ℕ) (hn : 0 < n) (hd : 5 < d) :
    val n 5 5 d = 1 := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hmq : (5 : ℚ) ≤ d := by exact_mod_cast hd.le
  have hc : ⌈(5 : ℚ) / (d : ℚ)⌉ = 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · simpa using div_pos (by norm_num : (0 : ℚ) < 5) hdq
    · simpa using (div_le_iff₀ hdq).mpr (by simpa using hmq)
  have hguard : (5 : ℤ) ≤ min 5 ((d : ℤ) - 1) := le_min le_rfl (by omega)
  have hdn : (1 : ℤ) ≤ d := by omega
  have hnn : (1 : ℤ) ≤ n := by omega
  norm_num [val, hc, hguard, min_eq_right hdn, min_eq_right hnn]

private theorem small_value (n d : ℕ) (hd : 0 < d) (hbound : d ≤ 5) :
    val n 5 5 d = min (n : ℤ) (if d ∣ 5 then 2 - (d : ℤ) else 1) := by
  interval_cases d
  · have hc : ⌈(5 : ℚ) / 1⌉ = 5 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(5 : ℚ) / 2⌉ = 3 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(5 : ℚ) / 3⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(5 : ℚ) / 4⌉ = 2 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]
  · have hc : ⌈(5 : ℚ) / 5⌉ = 1 := Int.ceil_eq_iff.mpr (by norm_num)
    norm_num [val, delta, hc]

private theorem divisor_value (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    val n 5 5 d = if d ∣ 5 then 2 - (d : ℤ) else 1 := by
  by_cases h : 5 < d
  · have hnmod : ¬ d ∣ 5 := fun h' => h.not_ge (Nat.le_of_dvd (by decide) h')
    rw [large_value n d hn h, if_neg hnmod]
  · rw [small_value n d hd (by omega)]
    split_ifs <;> exact min_eq_right (by omega)

private theorem closed (n : ℕ) (hn : 0 < n) :
    a n = 2 - (Nat.gcd n 5 : ℤ) := by
  have hp : 0 < Nat.gcd n 5 := Nat.gcd_pos_of_pos_left 5 hn
  have hne : n ≠ 0 := by omega
  unfold a uhat
  apply le_antisymm
  · rw [fold_min_le]
    refine Or.inr ⟨n.gcd 5, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n 5, hne⟩, ?_⟩
    rw [divisor_value n _ hn hp, if_pos (Nat.gcd_dvd_right n 5)]
  · rw [le_fold_min]
    refine ⟨by omega, ?_⟩
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    rw [divisor_value n d hn (Nat.pos_of_dvd_of_pos hdvd hn)]
    by_cases h : d ∣ 5
    · have hle := Nat.le_of_dvd hp (Nat.dvd_gcd hdvd h)
      rw [if_pos h]
      omega
    · rw [if_neg h]
      omega

private theorem period (n : ℕ) (hn : 5 < n) : a n = a (n - 5) := by
  rw [closed n (by omega), closed (n - 5) (by omega), Nat.gcd_sub_self_left (by omega)]

set_option maxHeartbeats 1500000 in
private theorem series_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 - 1) =
      X * (3 * X ^ 4 - X ^ 3 - X ^ 2 - X - 1) := by
  have hp : (X * (3 * X ^ 4 - X ^ 3 - X ^ 2 - X - 1) : ℤ⟦X⟧) = C 3 * X ^ 5 - X ^ 4 - X ^ 3 - X ^ 2 - X ^ 1 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [hp]
  ext n
  simp only [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_C,
    coeff_mk, coeff_X_pow]
  by_cases hn : 5 < n
  · have hge : 5 ≤ n := by omega
    have h0 : n ≠ 0 := by omega
    have hz : n - 5 ≠ 0 := by omega
    have h1: n ≠ 1 := by omega
    have h2: n ≠ 2 := by omega
    have h3: n ≠ 3 := by omega
    have h4: n ≠ 4 := by omega
    have h5: n ≠ 5 := by omega
    simpa only [if_pos hge, if_neg h0, if_neg hz, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
      mul_zero, neg_zero, add_zero, sub_zero] using sub_eq_zero.mpr (period n hn).symm
  · interval_cases n <;> norm_num [closed, Nat.gcd, constantCoeff_C]

end OMA.S_oeis_a291568

open OMA.S_oeis_a291568 in
theorem OMA.solution : type_of% @OMA.S_oeis_a291568.main := by
  exact ⟨period, series_identity⟩