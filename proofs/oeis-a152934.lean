import OMAStatements.S_oeis_a152934

-- Problem: A152934: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of two m-gonal polygonal components chained with string components of length 3 as m varies.
-- Upstream: formal-conjectures statements/oeis-a152934.lean:0 (declaration OMA.S_oeis_a152934.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: lambda + delta = d + aa and 2 lambda - d - aa = s = sqrt(disc) > 0 (b, c > 0), so
-- R lambda + S delta = L(2n) aa + b F(2n+2) (multiply by s). With l = 3: aa = L + F,
-- b = L + 2F (L = L(2n), F = F(2n+2)). With P = F(2j+3), Q = F(2j+4) this gives
-- a(j+2) = (2P+Q)^2 + 2(2P+Q)(P+2Q) + 2(P+2Q)^2, and the shift j -> j+1 maps (P, Q) to
-- (P+Q, P+2Q); a quadratic form along this map satisfies x(j+3) = 8x(j+2) - 8x(j+1) + x(j)
-- identically. The g.f. follows by comparing coefficients (a(0) = a(1) = 0, a(2) = 289,
-- a(3) = 1962, a(4) = 13429).

namespace FS1A152934

open OMA.S_oeis_a152934

theorem fibR_add_two (k : ℕ) : fibR (k + 2) = fibR k + fibR (k + 1) := by
  show (Nat.fib (k + 2) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ)
  rw [Nat.fib_add_two, Nat.cast_add]

theorem fibR_nonneg (k : ℕ) : 0 ≤ fibR k := by
  unfold fibR
  positivity

theorem fibR_pos (k : ℕ) (hk : 0 < k) : 0 < fibR k := by
  unfold fibR
  exact_mod_cast Nat.fib_pos.mpr hk

theorem f32 : fibR (3 - 2) = 1 := by norm_num [fibR]

theorem f31 : fibR (3 - 1) = 1 := by norm_num [fibR]

theorem f3 : fibR 3 = 2 := by norm_num [fibR]

theorem aa3 (n : ℕ) : aa n 3 = lucR (2 * n) + fibR (2 * n + 2) := by
  rw [aa]
  rw [f32, f31]
  ring

theorem bb3 (n : ℕ) : bb n 3 = lucR (2 * n) + 2 * fibR (2 * n + 2) := by
  rw [bb]
  rw [f31, f3]
  ring

theorem cc3 (n : ℕ) : cc n 3 = fibR (2 * n + 2) + fibR (n + 2) ^ 2 := by
  rw [cc]
  rw [f32, f31]
  ring

theorem key (n l : ℕ) (hD : 0 < (dd n l - aa n l) ^ 2 + 4 * bb n l * cc n l) :
    RR n l * lamb n l + SS n l * delt n l =
      lucR (2 * n) * aa n l + bb n l * fibR (2 * n + 2) := by
  have hs0 : Real.sqrt ((dd n l - aa n l) ^ 2 + 4 * bb n l * cc n l) ≠ 0 :=
    (Real.sqrt_pos.mpr hD).ne'
  have hden : 2 * lamb n l - dd n l - aa n l =
      Real.sqrt ((dd n l - aa n l) ^ 2 + 4 * bb n l * cc n l) := by
    rw [lamb]
    ring
  rw [RR, SS]
  rw [hden, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hs0]
  rw [lamb, delt]
  ring

theorem disc_pos (n : ℕ) : 0 < (dd n 3 - aa n 3) ^ 2 + 4 * bb n 3 * cc n 3 := by
  have hF : 0 < fibR (2 * n + 2) := fibR_pos _ (by omega)
  have hL : 0 ≤ lucR (2 * n) := by
    rw [lucR]
    have h1 := fibR_nonneg (2 * n - 1)
    have h2 := fibR_nonneg (2 * n + 1)
    linarith
  have hG := sq_nonneg (fibR (n + 2))
  have hb : 0 < bb n 3 := by
    rw [bb3]
    linarith
  have hc : 0 < cc n 3 := by
    rw [cc3]
    linarith
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (mul_pos (by norm_num) hb) hc)

theorem a_form (n : ℕ) (hn : 2 ≤ n) :
    a n = lucR (2 * n) * (lucR (2 * n) + fibR (2 * n + 2)) +
      (lucR (2 * n) + 2 * fibR (2 * n + 2)) * fibR (2 * n + 2) := by
  have h := key n 3 (disc_pos n)
  rw [aa3, bb3] at h
  rw [a, if_neg (show ¬ (n < 2) by omega), pow_one, pow_one]
  exact h

theorem a_PQ (j : ℕ) : a (j + 2) =
    (2 * fibR (2 * j + 3) + fibR (2 * j + 4)) ^ 2 +
      2 * (2 * fibR (2 * j + 3) + fibR (2 * j + 4)) * (fibR (2 * j + 3) + 2 * fibR (2 * j + 4)) +
      2 * (fibR (2 * j + 3) + 2 * fibR (2 * j + 4)) ^ 2 := by
  have h5 := fibR_add_two (2 * j + 3)
  rw [show 2 * j + 3 + 2 = 2 * j + 5 by omega, show 2 * j + 3 + 1 = 2 * j + 4 by omega] at h5
  have h6 := fibR_add_two (2 * j + 4)
  rw [show 2 * j + 4 + 2 = 2 * (j + 2) + 2 by omega, show 2 * j + 4 + 1 = 2 * j + 5 by omega,
    h5] at h6
  have e1 : lucR (2 * (j + 2)) = 2 * fibR (2 * j + 3) + fibR (2 * j + 4) := by
    rw [lucR, show 2 * (j + 2) - 1 = 2 * j + 3 by omega, show 2 * (j + 2) + 1 = 2 * j + 5 by omega, h5]
    ring
  rw [a_form (j + 2) (by omega), e1, h6]
  ring

theorem hrec (j : ℕ) : a (j + 5) = 8 * a (j + 4) - 8 * a (j + 3) + a (j + 2) := by
  have f5 := fibR_add_two (2 * j + 3)
  rw [show 2 * j + 3 + 2 = 2 * j + 5 by omega, show 2 * j + 3 + 1 = 2 * j + 4 by omega] at f5
  have f6 := fibR_add_two (2 * j + 4)
  rw [show 2 * j + 4 + 2 = 2 * j + 6 by omega, show 2 * j + 4 + 1 = 2 * j + 5 by omega] at f6
  have f7 := fibR_add_two (2 * j + 5)
  rw [show 2 * j + 5 + 2 = 2 * j + 7 by omega, show 2 * j + 5 + 1 = 2 * j + 6 by omega] at f7
  have f8 := fibR_add_two (2 * j + 6)
  rw [show 2 * j + 6 + 2 = 2 * j + 8 by omega, show 2 * j + 6 + 1 = 2 * j + 7 by omega] at f8
  have f9 := fibR_add_two (2 * j + 7)
  rw [show 2 * j + 7 + 2 = 2 * j + 9 by omega, show 2 * j + 7 + 1 = 2 * j + 8 by omega] at f9
  have f10 := fibR_add_two (2 * j + 8)
  rw [show 2 * j + 8 + 2 = 2 * j + 10 by omega, show 2 * j + 8 + 1 = 2 * j + 9 by omega] at f10
  have e2 := a_PQ j
  have e3 := a_PQ (j + 1)
  rw [show j + 1 + 2 = j + 3 by omega, show 2 * (j + 1) + 3 = 2 * j + 5 by omega,
    show 2 * (j + 1) + 4 = 2 * j + 6 by omega] at e3
  have e4 := a_PQ (j + 2)
  rw [show j + 2 + 2 = j + 4 by omega, show 2 * (j + 2) + 3 = 2 * j + 7 by omega,
    show 2 * (j + 2) + 4 = 2 * j + 8 by omega] at e4
  have e5 := a_PQ (j + 3)
  rw [show j + 3 + 2 = j + 5 by omega, show 2 * (j + 3) + 3 = 2 * j + 9 by omega,
    show 2 * (j + 3) + 4 = 2 * j + 10 by omega] at e5
  rw [e5, e4, e3, e2, f10, f9, f8, f7, f6, f5]
  ring

theorem a0 : a 0 = 0 := by
  rw [a, if_pos (show (0 : ℕ) < 2 by norm_num)]

theorem a1 : a 1 = 0 := by
  rw [a, if_pos (show (1 : ℕ) < 2 by norm_num)]

theorem a2 : a 2 = 289 := by
  have h := a_PQ 0
  have p : fibR (2 * 0 + 3) = 2 := by norm_num [fibR]
  have q : fibR (2 * 0 + 4) = 3 := by norm_num [fibR]
  rw [p, q, show (0 : ℕ) + 2 = 2 from rfl] at h
  rw [h]
  norm_num

theorem a3 : a 3 = 1962 := by
  have h := a_PQ 1
  have p : fibR (2 * 1 + 3) = 5 := by norm_num [fibR]
  have q : fibR (2 * 1 + 4) = 8 := by norm_num [fibR]
  rw [p, q, show (1 : ℕ) + 2 = 3 from rfl] at h
  rw [h]
  norm_num

theorem a4 : a 4 = 13429 := by
  have h := a_PQ 2
  have p : fibR (2 * 2 + 3) = 13 := by norm_num [fibR]
  have q : fibR (2 * 2 + 4) = 21 := by norm_num [fibR]
  rw [p, q, show (2 : ℕ) + 2 = 4 from rfl] at h
  rw [h]
  norm_num

end FS1A152934

open OMA.S_oeis_a152934 FS1A152934 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152934.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega]
    exact hrec k
  · have e : PowerSeries.mk a *
          ((1 - PowerSeries.X) * (1 - 7 * PowerSeries.X + PowerSeries.X ^ 2)) =
        PowerSeries.mk a
          - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 8 * (PowerSeries.mk a * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℝ →+* PowerSeries ℝ) 8 * (PowerSeries.mk a * PowerSeries.X ^ 2)
          - PowerSeries.mk a * PowerSeries.X ^ 3 := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 8]
      ring
    have e2 : (PowerSeries.X ^ 2 * (289 - 350 * PowerSeries.X + 45 * PowerSeries.X ^ 2) :
          PowerSeries ℝ) =
        PowerSeries.X ^ 2 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 289
          - PowerSeries.X ^ 3 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 350
          + PowerSeries.X ^ 4 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 45 := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 289,
        map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 350,
        map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 45]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 5 with hm | hm
    · interval_cases m <;> norm_num [a0, a1, a2, a3, a4]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
      rw [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
        if_pos (show 3 ≤ k + 5 by omega),
        if_neg (show ¬ (k + 5 = 2) by omega), if_neg (show ¬ (k + 5 = 3) by omega),
        if_neg (show ¬ (k + 5 = 4) by omega),
        show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
        show k + 5 - 3 = k + 2 by omega, hrec k]
      ring
