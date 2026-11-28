import OMAStatements.S_oeis_a331944

-- Problem: A331944: a(n)/ceiling(6^(n-7)) is the expected number of rolls of a fair 6-sided die in a game where the player starts at 0, advances the position by the outcome of the die's roll until exactly position n is reached. Positions beyond n are avoided by staying at the last visited position, but counting the rolls.
-- Upstream: formal-conjectures statements/oeis-a331944.lean:0 (declaration OMA.S_oeis_a331944.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: E(1..6) = 6 and E(7) = 7 by the recursion; for d ≥ 6 the recursion reads
-- E(d) = (6 + E(d-1) + ... + E(d-6))/6, and subtracting two consecutive instances gives
-- E(j+7) = (7/6) E(j+6) - (1/6) E(j). Since ceiling(6^(n-7)) = 6^(n-7) for n ≥ 7 (and 1 below),
-- a(j+14) = 6^(j+7) E(j+14) = 7 a(j+13) - 46656 a(j+7). The denominator of the g.f. is exactly
-- 1 - 7x + 46656x^7, so the g.f. follows by comparing coefficients, with a(1..13) computed.

open OMA.S_oeis_a331944 in
theorem OMA.solution : type_of% @OMA.S_oeis_a331944.main := by
  have E0 : E 0 = 0 := by
    rw [E]
  have Erec : ∀ d : ℕ, E (d + 1) =
      (6 + ∑ k ∈ Finset.range 6, if k + 1 ≤ d + 1 then E (d - k) else 0) /
        ((min (d + 1) 6 : ℕ) : ℚ) := by
    intro d
    rw [E]
  have E1 : E 1 = 6 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Erec 0, show min (0 + 1) 6 = 1 from rfl]
    norm_num [Finset.sum_range_succ, E0]
  have E2 : E 2 = 6 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Erec 1, show min (1 + 1) 6 = 2 from rfl]
    norm_num [Finset.sum_range_succ, E0, E1]
  have E3 : E 3 = 6 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Erec 2, show min (2 + 1) 6 = 3 from rfl]
    norm_num [Finset.sum_range_succ, E0, E1, E2]
  have E4 : E 4 = 6 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Erec 3, show min (3 + 1) 6 = 4 from rfl]
    norm_num [Finset.sum_range_succ, E0, E1, E2, E3]
  have E5 : E 5 = 6 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, Erec 4, show min (4 + 1) 6 = 5 from rfl]
    norm_num [Finset.sum_range_succ, E0, E1, E2, E3, E4]
  have E6 : E 6 = 6 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, Erec 5, show min (5 + 1) 6 = 6 from rfl]
    norm_num [Finset.sum_range_succ, E0, E1, E2, E3, E4, E5]
  have Erec6 : ∀ j : ℕ, E (j + 6) =
      (6 + E (j + 5) + E (j + 4) + E (j + 3) + E (j + 2) + E (j + 1) + E j) / 6 := by
    intro j
    have h := Erec (j + 5)
    rw [show j + 5 + 1 = j + 6 from rfl] at h
    rw [h]
    have hs : ∀ k ∈ Finset.range 6,
        (if k + 1 ≤ j + 6 then E (j + 5 - k) else 0) = E (j + 5 - k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact if_pos (by omega)
    rw [Finset.sum_congr rfl hs, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, show min (j + 6) 6 = 6 from Nat.min_eq_right (by omega),
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega, show j + 5 - 5 = j by omega]
    push_cast
    ring
  have Erec7 : ∀ j : ℕ, E (j + 7) = 7 / 6 * E (j + 6) - 1 / 6 * E j := by
    intro j
    have h1 : E (j + 7) =
        (6 + E (j + 6) + E (j + 5) + E (j + 4) + E (j + 3) + E (j + 2) + E (j + 1)) / 6 :=
      Erec6 (j + 1)
    have h0 := Erec6 j
    rw [h1, h0]
    ring
  have hc1 : ∀ n : ℕ, n ≤ 7 → ⌈(6 : ℚ) ^ ((n : ℤ) - 7)⌉ = 1 := by
    intro n hn
    have h0 : (0 : ℚ) < (6 : ℚ) ^ ((n : ℤ) - 7) := zpow_pos (by norm_num) _
    have h1 : (6 : ℚ) ^ ((n : ℤ) - 7) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
    rw [Int.ceil_eq_iff, Int.cast_one]
    exact ⟨by linarith, h1⟩
  have hc2 : ∀ j : ℕ, ⌈(6 : ℚ) ^ (((j + 7 : ℕ) : ℤ) - 7)⌉ = 6 ^ j := by
    intro j
    have e : ((j + 7 : ℕ) : ℤ) - 7 = (j : ℤ) := by omega
    have e2 : (6 : ℚ) ^ j = ((6 ^ j : ℤ) : ℚ) := by norm_num
    rw [e, zpow_natCast, e2, Int.ceil_intCast]
  have ha_small : ∀ n : ℕ, n ≤ 7 → a n = E n := by
    intro n hn
    rw [a, hc1 n hn]
    norm_num
  have ha7 : ∀ j : ℕ, a (j + 7) = E (j + 7) * (6 : ℚ) ^ j := by
    intro j
    rw [a, hc2 j]
    norm_num
  have hrec : ∀ n : ℕ, 14 ≤ n → a n = 7 * a (n - 1) - 46656 * a (n - 7) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 14 := ⟨n - 14, by omega⟩
    rw [show j + 14 - 1 = j + 13 by omega, show j + 14 - 7 = j + 7 by omega]
    have e1 : a (j + 14) = E (j + 14) * (6 : ℚ) ^ (j + 7) := ha7 (j + 7)
    have e2 : a (j + 13) = E (j + 13) * (6 : ℚ) ^ (j + 6) := ha7 (j + 6)
    have e3 : a (j + 7) = E (j + 7) * (6 : ℚ) ^ j := ha7 j
    have r : E (j + 14) = 7 / 6 * E (j + 13) - 1 / 6 * E (j + 7) := Erec7 (j + 7)
    rw [e1, e2, e3, r]
    ring
  refine ⟨?_, hrec⟩
  have E7 : E 7 = 7 := by
    have h : E 7 = (6 + E 6 + E 5 + E 4 + E 3 + E 2 + E 1) / 6 := Erec6 1
    rw [h, E6, E5, E4, E3, E2, E1]
    norm_num
  have E8 : E 8 = 43 / 6 := by
    have h : E 8 = 7 / 6 * E 7 - 1 / 6 * E 1 := Erec7 1
    rw [h, E7, E1]
    norm_num
  have E9 : E 9 = 265 / 36 := by
    have h : E 9 = 7 / 6 * E 8 - 1 / 6 * E 2 := Erec7 2
    rw [h, E8, E2]
    norm_num
  have E10 : E 10 = 1639 / 216 := by
    have h : E 10 = 7 / 6 * E 9 - 1 / 6 * E 3 := Erec7 3
    rw [h, E9, E3]
    norm_num
  have E11 : E 11 = 10177 / 1296 := by
    have h : E 11 = 7 / 6 * E 10 - 1 / 6 * E 4 := Erec7 4
    rw [h, E10, E4]
    norm_num
  have E12 : E 12 = 63463 / 7776 := by
    have h : E 12 = 7 / 6 * E 11 - 1 / 6 * E 5 := Erec7 5
    rw [h, E11, E5]
    norm_num
  have E13 : E 13 = 397585 / 46656 := by
    have h : E 13 = 7 / 6 * E 12 - 1 / 6 * E 6 := Erec7 6
    rw [h, E12, E6]
    norm_num
  have q1 : a 1 = 6 := by rw [ha_small 1 (by norm_num), E1]
  have q2 : a 2 = 6 := by rw [ha_small 2 (by norm_num), E2]
  have q3 : a 3 = 6 := by rw [ha_small 3 (by norm_num), E3]
  have q4 : a 4 = 6 := by rw [ha_small 4 (by norm_num), E4]
  have q5 : a 5 = 6 := by rw [ha_small 5 (by norm_num), E5]
  have q6 : a 6 = 6 := by rw [ha_small 6 (by norm_num), E6]
  have q7 : a 7 = 7 := by rw [ha_small 7 (by norm_num), E7]
  have q8 : a 8 = 43 := by
    have h : a 8 = E 8 * (6 : ℚ) ^ 1 := ha7 1
    rw [h, E8]
    norm_num
  have q9 : a 9 = 265 := by
    have h : a 9 = E 9 * (6 : ℚ) ^ 2 := ha7 2
    rw [h, E9]
    norm_num
  have q10 : a 10 = 1639 := by
    have h : a 10 = E 10 * (6 : ℚ) ^ 3 := ha7 3
    rw [h, E10]
    norm_num
  have q11 : a 11 = 10177 := by
    have h : a 11 = E 11 * (6 : ℚ) ^ 4 := ha7 4
    rw [h, E11]
    norm_num
  have q12 : a 12 = 63463 := by
    have h : a 12 = E 12 * (6 : ℚ) ^ 5 := ha7 5
    rw [h, E12]
    norm_num
  have q13 : a 13 = 397585 := by
    have h : a 13 = E 13 * (6 : ℚ) ^ 6 := ha7 6
    rw [h, E13]
    norm_num
  obtain ⟨B, hB⟩ : ∃ B : PowerSeries ℚ,
      B = PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) := ⟨_, rfl⟩
  rw [← hB]
  have cB : ∀ m, PowerSeries.coeff m B = if m = 0 then (0 : ℚ) else a m := by
    intro m
    rw [hB, PowerSeries.coeff_mk]
  have h6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
  have h7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
  have h35 : (PowerSeries.C (35 : ℚ) : PowerSeries ℚ) = 35 := map_ofNat _ 35
  have h36 : (PowerSeries.C (36 : ℚ) : PowerSeries ℚ) = 36 := map_ofNat _ 36
  have h46656 : (PowerSeries.C (46656 : ℚ) : PowerSeries ℚ) = 46656 := map_ofNat _ 46656
  have h233280 : (PowerSeries.C (233280 : ℚ) : PowerSeries ℚ) = 233280 := map_ofNat _ 233280
  have h272160 : (PowerSeries.C (272160 : ℚ) : PowerSeries ℚ) = 272160 := map_ofNat _ 272160
  have h278640 : (PowerSeries.C (278640 : ℚ) : PowerSeries ℚ) = 278640 := map_ofNat _ 278640
  have h279720 : (PowerSeries.C (279720 : ℚ) : PowerSeries ℚ) = 279720 := map_ofNat _ 279720
  have h279900 : (PowerSeries.C (279900 : ℚ) : PowerSeries ℚ) = 279900 := map_ofNat _ 279900
  have h279930 : (PowerSeries.C (279930 : ℚ) : PowerSeries ℚ) = 279930 := map_ofNat _ 279930
  have e : B * ((1 - 6 * PowerSeries.X) ^ 2 *
      (1 + 5 * PowerSeries.X + 24 * PowerSeries.X ^ 2 + 108 * PowerSeries.X ^ 3 +
        432 * PowerSeries.X ^ 4 + 1296 * PowerSeries.X ^ 5)) =
      B - PowerSeries.C (7 : ℚ) * (B * PowerSeries.X ^ 1) +
        PowerSeries.C (46656 : ℚ) * (B * PowerSeries.X ^ 7) := by
    rw [h7, h46656]
    ring
  have e2 : (PowerSeries.X * (6 - 36 * PowerSeries.X - 36 * PowerSeries.X ^ 2 -
      36 * PowerSeries.X ^ 3 - 36 * PowerSeries.X ^ 4 - 36 * PowerSeries.X ^ 5 -
      35 * PowerSeries.X ^ 6 + 279930 * PowerSeries.X ^ 7 + 279900 * PowerSeries.X ^ 8 +
      279720 * PowerSeries.X ^ 9 + 278640 * PowerSeries.X ^ 10 + 272160 * PowerSeries.X ^ 11 +
      233280 * PowerSeries.X ^ 12) : PowerSeries ℚ) =
      PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (36 : ℚ) * PowerSeries.X ^ 2 -
        PowerSeries.C (36 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (36 : ℚ) * PowerSeries.X ^ 4 -
        PowerSeries.C (36 : ℚ) * PowerSeries.X ^ 5 - PowerSeries.C (36 : ℚ) * PowerSeries.X ^ 6 -
        PowerSeries.C (35 : ℚ) * PowerSeries.X ^ 7 +
        PowerSeries.C (279930 : ℚ) * PowerSeries.X ^ 8 +
        PowerSeries.C (279900 : ℚ) * PowerSeries.X ^ 9 +
        PowerSeries.C (279720 : ℚ) * PowerSeries.X ^ 10 +
        PowerSeries.C (278640 : ℚ) * PowerSeries.X ^ 11 +
        PowerSeries.C (272160 : ℚ) * PowerSeries.X ^ 12 +
        PowerSeries.C (233280 : ℚ) * PowerSeries.X ^ 13 := by
    rw [h6, h36, h35, h279930, h279900, h279720, h278640, h272160, h233280]
    ring
  refine e.trans (Eq.trans ?_ e2.symm)
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
  rcases Nat.lt_or_ge m 14 with hm | hm
  · interval_cases m <;> simp only [PowerSeries.coeff_mul_X_pow', cB, PowerSeries.coeff_X_pow] <;>
      norm_num [q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 14 := ⟨m - 14, by omega⟩
    have t0 : PowerSeries.coeff (k + 14) B = a (k + 14) := by
      rw [cB, if_neg (show ¬(k + 14 = 0) by omega)]
    have t1 : PowerSeries.coeff (k + 14) (B * PowerSeries.X ^ 1) = a (k + 13) := by
      rw [show k + 14 = k + 13 + 1 by omega, PowerSeries.coeff_mul_X_pow, cB,
        if_neg (show ¬(k + 13 = 0) by omega)]
    have t7 : PowerSeries.coeff (k + 14) (B * PowerSeries.X ^ 7) = a (k + 7) := by
      rw [show k + 14 = k + 7 + 7 by omega, PowerSeries.coeff_mul_X_pow, cB,
        if_neg (show ¬(k + 7 = 0) by omega)]
    have u1 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 1) by omega)]
    have u2 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 2) by omega)]
    have u3 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 3 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 3) by omega)]
    have u4 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 4 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 4) by omega)]
    have u5 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 5 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 5) by omega)]
    have u6 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 6 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 6) by omega)]
    have u7 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 7 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 7) by omega)]
    have u8 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 8 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 8) by omega)]
    have u9 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 9 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 9) by omega)]
    have u10 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 10 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 10) by omega)]
    have u11 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 11 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 11) by omega)]
    have u12 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 12 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 12) by omega)]
    have u13 : PowerSeries.coeff (k + 14) (PowerSeries.X ^ 13 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 14 = 13) by omega)]
    have hq : a (k + 14) = 7 * a (k + 13) - 46656 * a (k + 7) := by
      have h := hrec (k + 14) (by omega)
      rw [show k + 14 - 1 = k + 13 by omega, show k + 14 - 7 = k + 7 by omega] at h
      exact h
    rw [t0, t1, t7, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13]
    linear_combination hq