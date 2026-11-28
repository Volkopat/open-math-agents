import OMAStatements.S_oeis_a291515
import Mathlib

open PowerSeries OMA.S_oeis_a291515

private theorem ceil_div_eq_one (h d : ℕ) (hh : 0 < h) (hd : h ≤ d) :
    ⌈(h : ℚ) / d⌉ = 1 := by
  have hpos : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hle : (h : ℚ) ≤ d := by exact_mod_cast hd
  apply Int.ceil_eq_iff.mpr
  norm_num
  exact ⟨div_pos (by exact_mod_cast hh) hpos, (div_le_iff₀ hpos).mpr (by simpa using hle)⟩

private theorem val_large (n d : ℕ) (hd : 6 < d) :
    val n 3 6 d = -2 * (d : ℤ) := by
  have hm := ceil_div_eq_one 3 d (by decide) (by omega)
  have hh := ceil_div_eq_one 6 d (by decide) (by omega)
  have hz : (6 : ℤ) < d := by exact_mod_cast hd
  unfold val
  rw [hm, hh]
  norm_num [delta, min_def]
  split_ifs <;> omega

private theorem val_small (n d : ℕ) (hd : 0 < d) (hs : d ≤ 6) :
    -19 ≤ val n 3 6 d := by
  interval_cases d <;> norm_num [val, delta, le_min_iff]

private theorem a_large (n : ℕ) (hn : 10 ≤ n) : a n = -2 * (n : ℤ) := by
  unfold a uhat
  apply le_antisymm
  · apply (Finset.fold_min_le _).mpr
    exact Or.inr ⟨n, Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩, (val_large n n (by omega)).le⟩
  · apply (Finset.le_fold_min _).mpr
    refine ⟨by omega, ?_⟩
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hpos := Nat.pos_of_dvd_of_pos hdvd (show 0 < n by omega)
    have hle := Nat.le_of_dvd (show 0 < n by omega) hdvd
    by_cases h : 6 < d
    · rw [val_large n d h]
      omega
    · have := val_small n d hpos (by omega)
      omega

private theorem a_small (n : ℕ) (hn : n < 10) :
    a n = ([0, -17, -17, -19, -17, -17, -19, -17, -17, -19] : List ℤ)[n]?.getD 0 := by
  interval_cases n <;> decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a291515.main := by
  constructor
  · intro n hn
    rw [a_large n (by omega), a_large (n-1) (by omega), a_large (n-2) (by omega)]
    omega
  · let f : ℤ⟦X⟧ := mk (fun n => if n = 0 then (0 : ℤ) else a n)
    change f * (X-1)^2 = _
    rw [show f * (X-1)^2 = f * X^2 - C (2 : ℤ) * (f * X^1) + f by simp; ring]
    rw [show (X * (-X^10 + X^9 - 2*X^8 - 2*X^7 + 4*X^6 - 2*X^5 - 2*X^4 +
        4*X^3 - 2*X^2 + 17*X - 17) : ℤ⟦X⟧) =
        -X^11 + X^10 - C 2 * X^9 - C 2 * X^8 + C 4 * X^7 - C 2 * X^6 -
        C 2 * X^5 + C 4 * X^4 - C 2 * X^3 + C 17 * X^2 - C 17 * X^1 by simp; ring]
    ext n
    simp only [map_add, map_sub, map_neg, coeff_C_mul_X_pow]
    simp only [coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', f, coeff_mk]
    by_cases h : n < 12
    · interval_cases n <;> norm_num [a_small, a_large]
    · have h0 : 10 ≤ n := by omega
      have h1 : 10 ≤ n-1 := by omega
      have h2 : 10 ≤ n-2 := by omega
      simp only [if_neg (show n ≠ 11 by omega), if_neg (show n ≠ 10 by omega),
        if_neg (show n ≠ 9 by omega), if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 7 by omega),
        if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 4 by omega),
        if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 1 by omega),
        if_neg (show n ≠ 0 by omega), if_neg (show n-2 ≠ 0 by omega), if_neg (show n-1 ≠ 0 by omega),
        if_pos (show 2 ≤ n by omega), if_pos (show 1 ≤ n by omega), a_large n h0,
        a_large (n-1) h1, a_large (n-2) h2]
      omega