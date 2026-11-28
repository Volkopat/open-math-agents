import OMAStatements.S_oeis_a291520
import Mathlib

open PowerSeries OMA.S_oeis_a291520

private theorem ceil_div_eq_one (h d : ℕ) (hh : 0 < h) (hd : h ≤ d) :
    ⌈(h : ℚ) / d⌉ = 1 := by
  have hpos : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
  have hle : (h : ℚ) ≤ d := by exact_mod_cast hd
  apply Int.ceil_eq_iff.mpr
  norm_num
  exact ⟨div_pos (by exact_mod_cast hh) hpos, (div_le_iff₀ hpos).mpr (by simpa using hle)⟩

private theorem val_large (n d : ℕ) (hn : 5 ≤ n) (hd : 4 < d) :
    val n 4 2 d = 5 := by
  have hm := ceil_div_eq_one 4 d (by decide) (by omega)
  have hh := ceil_div_eq_one 2 d (by decide) (by omega)
  unfold val
  rw [hm, hh]
  norm_num [delta, min_def]
  split_ifs <;> omega

private theorem val_small (n d : ℕ) (hn : 5 ≤ n) (hd : 0 < d) (hs : d ≤ 4) :
    val n 4 2 d = if 2 ∣ d then 4 else if d = 3 then min 6 (n : ℤ) else 5 := by
  interval_cases d <;> norm_num [val, delta, min_def] <;> omega

private theorem a_large (n : ℕ) (hn : 5 ≤ n) : a n = if 2 ∣ n then 4 else 5 := by
  unfold a uhat
  apply le_antisymm
  · apply (Finset.fold_min_le _).mpr
    split_ifs with he
    · exact Or.inr ⟨2, Nat.mem_divisors.mpr ⟨he, by omega⟩, by
        rw [val_small n 2 hn (by decide) (by decide)]
        norm_num⟩
    · exact Or.inr ⟨n, Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩,
        (val_large n n hn (by omega)).le⟩
  · apply (Finset.le_fold_min _).mpr
    refine ⟨by split_ifs <;> omega, ?_⟩
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hp := Nat.pos_of_dvd_of_pos hdvd (show 0 < n by omega)
    by_cases h : 4 < d
    · rw [val_large n d hn h]
      split_ifs <;> decide
    · rw [val_small n d hn hp (by omega)]
      have he : 2 ∣ d → 2 ∣ n := fun hv => hv.trans hdvd
      simp only [min_def]
      split_ifs at * <;> omega

private theorem a_small (n : ℕ) (hn : n < 5) : a n = n := by
  interval_cases n <;> decide +kernel

private theorem periodic (n : ℕ) (hn : 5 < n) : a n = a (n - 2) := by
  by_cases h : 7 ≤ n
  · rw [a_large n (by omega), a_large (n-2) (by omega)]
    have he : (2 ∣ n) ↔ (2 ∣ n-2) := by omega
    simp only [he]
  · obtain rfl : n = 6 := by omega
    decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a291520.main := by
  refine ⟨periodic, ?_⟩
  let f : ℤ⟦X⟧ := mk (fun n => if n = 0 then (0 : ℤ) else a n)
  change f * (X^2-1) = _
  rw [show f * (X^2-1) = f * X^2 - f by ring]
  rw [show (X * (-2 * X^4 - 2 * X^3 - 2 * X^2 - 2 * X - 1) : ℤ⟦X⟧) =
      -(C 2 * X^5) - C 2 * X^4 - C 2 * X^3 - C 2 * X^2 - X^1 by simp; ring]
  ext n
  simp only [map_sub, map_neg, coeff_C_mul_X_pow]
  simp only [coeff_X_pow, coeff_mul_X_pow', f, coeff_mk]
  by_cases h : n < 7
  · interval_cases n <;> norm_num [a_small, a_large]
  · simp only [if_pos (show 2 ≤ n by omega), if_neg (show n-2 ≠ 0 by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 1 by omega),
      periodic n (by omega), sub_self, neg_zero]