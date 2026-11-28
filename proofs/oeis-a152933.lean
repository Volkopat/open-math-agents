import OMAStatements.S_oeis_a152933

-- Problem: A152933: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of k 6-gonal polygonal components chained with string components of length 2 as k varies.
-- Upstream: formal-conjectures statements/oeis-a152933.lean:0 (declaration OMA.S_oeis_a152933.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with F(0..8) = 0, 1, 1, 2, 3, 5, 8, 13, 21 one gets L(6) = 18, aa = 21, b = 39,
-- c = 25, d = 46, so (d - aa)^2 + 4bc = 4525, and with s = sqrt 4525: lambda = (67 + s)/2,
-- delta = (67 - s)/2, the roots of t^2 - 67t - 9, and 2 lambda - d - aa = s, R s = 18 lambda - 9,
-- S s = 18 lambda - 1197. Hence R + S = 18 and R lambda + S delta = 1197 (multiply by s, use
-- s^2 = 4525), so a(1) = 18, a(2) = 1197, and a(n+1) = R lambda^n + S delta^n satisfies
-- a(k+3) = 67a(k+2) + 9a(k+1). The g.f. follows by comparing coefficients (a(0) = 0,
-- a(1) - 67a(0) = 18, a(2) - 67a(1) - 9a(0) = -9).

open OMA.S_oeis_a152933 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152933.main := by
  have hs2 : Real.sqrt 4525 ^ 2 = 4525 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 4525 := Real.sqrt_pos.mpr (by norm_num)
  have hF8 : fibR (2 * 3 + 2) = 21 := by norm_num [fibR]
  have hL6 : lucR (2 * 3) = 18 := by norm_num [lucR, fibR]
  have hdd : dd 3 2 = 46 := by norm_num [dd, fibR]
  have haa : aa 3 2 = 21 := by norm_num [aa, lucR, fibR]
  have hbb : bb 3 2 = 39 := by norm_num [bb, lucR, fibR]
  have hcc : cc 3 2 = 25 := by norm_num [cc, fibR]
  have hdisc : (dd 3 2 - aa 3 2) ^ 2 + 4 * bb 3 2 * cc 3 2 = 4525 := by
    norm_num [hdd, haa, hbb, hcc]
  have hlam : lamb 3 2 = (67 + Real.sqrt 4525) / 2 := by
    rw [lamb, hdisc, hdd, haa]
    ring
  have hdel : delt 3 2 = (67 - Real.sqrt 4525) / 2 := by
    rw [delt, hdisc, hdd, haa]
    ring
  have hden : 2 * lamb 3 2 - dd 3 2 - aa 3 2 = Real.sqrt 4525 := by
    rw [hlam, hdd, haa]
    ring
  have hA : RR 3 2 * Real.sqrt 4525 = 18 * lamb 3 2 - 9 := by
    rw [RR, hden, hdd, hbb, hL6, hF8, div_mul_cancel₀ _ hs0.ne']
    ring
  have hB : SS 3 2 * Real.sqrt 4525 = 18 * lamb 3 2 - 1197 := by
    rw [SS, hden, haa, hbb, hL6, hF8, div_mul_cancel₀ _ hs0.ne']
    ring
  have hLs : 2 * lamb 3 2 = 67 + Real.sqrt 4525 := by
    rw [hlam]
    ring
  have hL2 : lamb 3 2 ^ 2 = 67 * lamb 3 2 + 9 := by
    rw [hlam]
    linear_combination (1 / 4 : ℝ) * hs2
  have hD2 : delt 3 2 ^ 2 = 67 * delt 3 2 + 9 := by
    rw [hdel]
    linear_combination (1 / 4 : ℝ) * hs2
  have hLD : lamb 3 2 * delt 3 2 = -9 := by
    rw [hlam, hdel]
    linear_combination (-1 / 4 : ℝ) * hs2
  have hsum : lamb 3 2 + delt 3 2 = 67 := by
    rw [hlam, hdel]
    ring
  have hAB : RR 3 2 + SS 3 2 = 18 := by
    have h1 : (RR 3 2 + SS 3 2 - 18) * Real.sqrt 4525 = 0 := by
      linear_combination hA + hB + 18 * hLs
    have h2 := (mul_eq_zero.mp h1).resolve_right hs0.ne'
    linarith
  have hALBD : RR 3 2 * lamb 3 2 + SS 3 2 * delt 3 2 = 1197 := by
    have h1 : (RR 3 2 * lamb 3 2 + SS 3 2 * delt 3 2 - 1197) * Real.sqrt 4525 = 0 := by
      linear_combination lamb 3 2 * hA + delt 3 2 * hB + 18 * hLD - 1197 * hsum + 18 * hL2 +
        1197 * hLs
    have h2 := (mul_eq_zero.mp h1).resolve_right hs0.ne'
    linarith
  have ha : ∀ k : ℕ, a (k + 1) = RR 3 2 * lamb 3 2 ^ k + SS 3 2 * delt 3 2 ^ k := by
    intro k
    rw [a, if_neg (show ¬ (k + 1 = 0) by omega), show k + 1 - 1 = k by omega]
  have a0 : a 0 = 0 := by
    rw [a, if_pos rfl]
  have a1 : a 1 = 18 := by
    have h := ha 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, pow_zero, pow_zero, mul_one, mul_one] at h
    rw [h]
    exact hAB
  have a2 : a 2 = 1197 := by
    have h := ha 1
    rw [show (1 : ℕ) + 1 = 2 from rfl, pow_one, pow_one] at h
    rw [h]
    exact hALBD
  have hrec : ∀ k : ℕ, a (k + 3) = 67 * a (k + 2) + 9 * a (k + 1) := by
    intro k
    have h3 := ha (k + 2)
    have h2 := ha (k + 1)
    have h1 := ha k
    rw [show k + 2 + 1 = k + 3 by omega] at h3
    rw [show k + 1 + 1 = k + 2 by omega] at h2
    rw [h3, h2, h1]
    linear_combination (RR 3 2 * lamb 3 2 ^ k) * hL2 + (SS 3 2 * delt 3 2 ^ k) * hD2
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    exact hrec k
  · have e : PowerSeries.mk a * (1 - 67 * PowerSeries.X - 9 * PowerSeries.X ^ 2) =
        PowerSeries.mk a
          - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 67 * (PowerSeries.mk a * PowerSeries.X ^ 1)
          - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 9 * (PowerSeries.mk a * PowerSeries.X ^ 2) := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 67,
        map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 9]
      ring
    have e2 : (9 * PowerSeries.X * (2 - PowerSeries.X) : PowerSeries ℝ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 18
          - PowerSeries.X ^ 2 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 9 := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 18,
        map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 9]
      ring
    rw [e, e2]
    ext m
    simp only [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m <;> norm_num [a0, a1, a2]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [if_pos (show 1 ≤ k + 3 by omega), if_pos (show 2 ≤ k + 3 by omega),
        if_neg (show ¬ (k + 3 = 1) by omega), if_neg (show ¬ (k + 3 = 2) by omega),
        show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, hrec k]
      ring
