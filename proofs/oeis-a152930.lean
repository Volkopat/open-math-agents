import OMAStatements.S_oeis_a152930

-- Problem: A152930: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of k 4-gonal polygonal components chained with string components of length 2 as k varies.
-- Upstream: formal-conjectures statements/oeis-a152930.lean:0 (declaration OMA.S_oeis_a152930.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with F(0..6) = 0, 1, 1, 2, 3, 5, 8 one gets aa = 8, b = 15, c = 9, d = 17, so
-- (d - aa)^2 + 4bc = 621, and with s = sqrt 621: lambda = (25 + s)/2, delta = (25 - s)/2, the
-- roots of t^2 - 25t + 1, and 2 lambda - d - aa = s, R s = 7 lambda + 1, S s = 7 lambda - 176.
-- Hence R + S = 7 and R lambda + S delta = 176 (multiply by s, use s^2 = 621), so a(1) = 7,
-- a(2) = 176, and a(n+1) = R lambda^n + S delta^n satisfies a(k+3) = 25a(k+2) - a(k+1). The g.f.
-- follows by comparing coefficients (a(0) = 0, a(1) - 25a(0) = 7, a(2) - 25a(1) + a(0) = 1).

open OMA.S_oeis_a152930 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152930.main := by
  have hs2 : Real.sqrt 621 ^ 2 = 621 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 621 := Real.sqrt_pos.mpr (by norm_num)
  have hF6 : fibR (2 * 2 + 2) = 8 := by norm_num [fibR]
  have hL4 : lucR (2 * 2) = 7 := by norm_num [lucR, fibR]
  have hdd : dd 2 2 = 17 := by norm_num [dd, fibR]
  have haa : aa 2 2 = 8 := by norm_num [aa, lucR, fibR]
  have hbb : bb 2 2 = 15 := by norm_num [bb, lucR, fibR]
  have hcc : cc 2 2 = 9 := by norm_num [cc, fibR]
  have hdisc : (dd 2 2 - aa 2 2) ^ 2 + 4 * bb 2 2 * cc 2 2 = 621 := by
    norm_num [hdd, haa, hbb, hcc]
  have hlam : lamb 2 2 = (25 + Real.sqrt 621) / 2 := by
    rw [lamb, hdisc, hdd, haa]
    ring
  have hdel : delt 2 2 = (25 - Real.sqrt 621) / 2 := by
    rw [delt, hdisc, hdd, haa]
    ring
  have hden : 2 * lamb 2 2 - dd 2 2 - aa 2 2 = Real.sqrt 621 := by
    rw [hlam, hdd, haa]
    ring
  have hA : RR 2 2 * Real.sqrt 621 = 7 * lamb 2 2 + 1 := by
    rw [RR, hden, hdd, hbb, hL4, hF6, div_mul_cancel₀ _ hs0.ne']
    ring
  have hB : SS 2 2 * Real.sqrt 621 = 7 * lamb 2 2 - 176 := by
    rw [SS, hden, haa, hbb, hL4, hF6, div_mul_cancel₀ _ hs0.ne']
    ring
  have hLs : 2 * lamb 2 2 = 25 + Real.sqrt 621 := by
    rw [hlam]
    ring
  have hL2 : lamb 2 2 ^ 2 = 25 * lamb 2 2 - 1 := by
    rw [hlam]
    linear_combination (1 / 4 : ℝ) * hs2
  have hD2 : delt 2 2 ^ 2 = 25 * delt 2 2 - 1 := by
    rw [hdel]
    linear_combination (1 / 4 : ℝ) * hs2
  have hLD : lamb 2 2 * delt 2 2 = 1 := by
    rw [hlam, hdel]
    linear_combination (-1 / 4 : ℝ) * hs2
  have hsum : lamb 2 2 + delt 2 2 = 25 := by
    rw [hlam, hdel]
    ring
  have hAB : RR 2 2 + SS 2 2 = 7 := by
    have h1 : (RR 2 2 + SS 2 2 - 7) * Real.sqrt 621 = 0 := by
      linear_combination hA + hB + 7 * hLs
    have h2 := (mul_eq_zero.mp h1).resolve_right hs0.ne'
    linarith
  have hALBD : RR 2 2 * lamb 2 2 + SS 2 2 * delt 2 2 = 176 := by
    have h1 : (RR 2 2 * lamb 2 2 + SS 2 2 * delt 2 2 - 176) * Real.sqrt 621 = 0 := by
      linear_combination lamb 2 2 * hA + delt 2 2 * hB + 7 * hLD - 176 * hsum + 7 * hL2 +
        176 * hLs
    have h2 := (mul_eq_zero.mp h1).resolve_right hs0.ne'
    linarith
  have ha : ∀ k : ℕ, a (k + 1) = RR 2 2 * lamb 2 2 ^ k + SS 2 2 * delt 2 2 ^ k := by
    intro k
    rw [a, if_neg (show ¬ (k + 1 = 0) by omega), show k + 1 - 1 = k by omega]
  have a0 : a 0 = 0 := by
    rw [a, if_pos rfl]
  have a1 : a 1 = 7 := by
    have h := ha 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, pow_zero, pow_zero, mul_one, mul_one] at h
    rw [h]
    exact hAB
  have a2 : a 2 = 176 := by
    have h := ha 1
    rw [show (1 : ℕ) + 1 = 2 from rfl, pow_one, pow_one] at h
    rw [h]
    exact hALBD
  have hrec : ∀ k : ℕ, a (k + 3) = 25 * a (k + 2) - a (k + 1) := by
    intro k
    have h3 := ha (k + 2)
    have h2 := ha (k + 1)
    have h1 := ha k
    rw [show k + 2 + 1 = k + 3 by omega] at h3
    rw [show k + 1 + 1 = k + 2 by omega] at h2
    rw [h3, h2, h1]
    linear_combination (RR 2 2 * lamb 2 2 ^ k) * hL2 + (SS 2 2 * delt 2 2 ^ k) * hD2
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    exact hrec k
  · have e : PowerSeries.mk a * (1 - 25 * PowerSeries.X + PowerSeries.X ^ 2) =
        PowerSeries.mk a
          - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 25 * (PowerSeries.mk a * PowerSeries.X ^ 1)
          + PowerSeries.mk a * PowerSeries.X ^ 2 := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 25]
      ring
    have e2 : (PowerSeries.X * (7 + PowerSeries.X) : PowerSeries ℝ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 7 + PowerSeries.X ^ 2 := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 7]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m <;> norm_num [a0, a1, a2]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [if_pos (show 1 ≤ k + 3 by omega), if_pos (show 2 ≤ k + 3 by omega),
        if_neg (show ¬ (k + 3 = 1) by omega), if_neg (show ¬ (k + 3 = 2) by omega),
        show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, hrec k]
      ring
