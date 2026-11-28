import OMAStatements.S_oeis_a152932

-- Problem: A152932: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of three 6-gonal polygonal components chained with string components of length l as l varies.
-- Upstream: formal-conjectures statements/oeis-a152932.lean:0 (declaration OMA.S_oeis_a152932.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: lambda + delta = d + aa, 2 lambda - d - aa = s = sqrt(disc) > 0 and s^2 = disc give
-- R lambda^2 + S delta^2 = L(6) (aa^2 + bc) + F(8) b (aa + d). For n = j + 1, with P = F(j),
-- Q = F(j+1) and F(n-2) = Q - P (also at n = 1, where F(-1) = 1): aa = 3P + 18Q, b = 18P + 21Q,
-- c = 4P + 21Q, d = 21P + 25Q. So a(j+1) is a quadratic form in (P, Q); the shift j -> j+1 maps
-- (P, Q) to (Q, P + Q), and such a form satisfies x(j+3) = 2x(j+2) + 2x(j+1) - x(j)
-- identically. The g.f. follows by comparing coefficients (a(0) = 0, a(1) = 32733,
-- a(2) = 80361, a(3) = 215658).

namespace FS1A152932

open OMA.S_oeis_a152932

theorem fibM_nat (k : ℕ) : fibM (k : ℤ) = (Nat.fib k : ℝ) := by
  rw [fibM, if_neg (show ¬ ((k : ℤ) = -1) by omega), show ((k : ℤ)).toNat = k by omega]

theorem fibM_eq (t : ℤ) (k : ℕ) (h : t = k) : fibM t = (Nat.fib k : ℝ) := by
  rw [h, fibM_nat]

theorem fibM_neg1 : fibM (-1) = 1 := by
  rw [fibM, if_pos rfl]

theorem hL6 : lucM (2 * 3) = 18 := by
  rw [lucM, fibM_eq (2 * 3 - 1) 5 (by norm_num), fibM_eq (2 * 3 + 1) 7 (by norm_num)]
  norm_num

theorem hF8 : fibM (2 * 3 + 2) = 21 := by
  rw [fibM_eq (2 * 3 + 2) 8 (by norm_num)]
  norm_num

theorem hF5 : fibM (3 + 2) = 5 := by
  rw [fibM_eq (3 + 2) 5 (by norm_num)]
  norm_num

theorem fibC (k : ℕ) : (Nat.fib (k + 2) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k + 1) : ℝ) := by
  rw [Nat.fib_add_two, Nat.cast_add]

theorem fm1 (j : ℕ) : fibM (((j + 1 : ℕ) : ℤ) - 1) = (Nat.fib j : ℝ) :=
  fibM_eq _ j (by omega)

theorem fm2 (j : ℕ) :
    fibM (((j + 1 : ℕ) : ℤ) - 2) = (Nat.fib (j + 1) : ℝ) - (Nat.fib j : ℝ) := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [show (((0 + 1 : ℕ) : ℤ) - 2) = -1 by norm_num, fibM_neg1]
    norm_num
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [fibM_eq (((i + 1 + 1 : ℕ) : ℤ) - 2) i (by omega), show i + 1 + 1 = i + 2 by omega, fibC i]
    ring

theorem haa (j : ℕ) :
    aa 3 ((j + 1 : ℕ) : ℤ) = 3 * (Nat.fib j : ℝ) + 18 * (Nat.fib (j + 1) : ℝ) := by
  rw [aa, hL6, hF8, fm2 j, fm1 j]
  ring

theorem hbb (j : ℕ) :
    bb 3 ((j + 1 : ℕ) : ℤ) = 21 * (Nat.fib (j + 1) : ℝ) + 18 * (Nat.fib j : ℝ) := by
  rw [bb, hL6, hF8, fm1 j, fibM_nat (j + 1)]
  ring

theorem hcc (j : ℕ) :
    cc 3 ((j + 1 : ℕ) : ℤ) = 4 * (Nat.fib j : ℝ) + 21 * (Nat.fib (j + 1) : ℝ) := by
  rw [cc, hF8, hF5, fm2 j, fm1 j]
  ring

theorem hdd (j : ℕ) :
    dd 3 ((j + 1 : ℕ) : ℤ) = 25 * (Nat.fib (j + 1) : ℝ) + 21 * (Nat.fib j : ℝ) := by
  rw [dd, hF8, hF5, fm1 j, fibM_nat (j + 1)]
  ring

theorem key3 (m n : ℤ) (hD : 0 < (dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n) :
    RR m n * lamb m n ^ 2 + SS m n * delt m n ^ 2 =
      lucM (2 * m) * (aa m n ^ 2 + bb m n * cc m n) +
        fibM (2 * m + 2) * bb m n * (aa m n + dd m n) := by
  have hs0 : Real.sqrt ((dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n) ≠ 0 :=
    (Real.sqrt_pos.mpr hD).ne'
  have hs2 : Real.sqrt ((dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n) ^ 2 =
      (dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n := Real.sq_sqrt hD.le
  have hden : 2 * lamb m n - dd m n - aa m n =
      Real.sqrt ((dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n) := by
    rw [lamb]
    ring
  rw [RR, SS, hden, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hs0, lamb,
    delt]
  linear_combination
    (lucM (2 * m) * Real.sqrt ((dd m n - aa m n) ^ 2 + 4 * bb m n * cc m n) / 4) * hs2

theorem disc_pos (j : ℕ) : 0 < (dd 3 ((j + 1 : ℕ) : ℤ) - aa 3 ((j + 1 : ℕ) : ℤ)) ^ 2 +
    4 * bb 3 ((j + 1 : ℕ) : ℤ) * cc 3 ((j + 1 : ℕ) : ℤ) := by
  rw [hdd, haa, hbb, hcc]
  have hQ : (0 : ℝ) < (Nat.fib (j + 1) : ℝ) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hP : (0 : ℝ) ≤ (Nat.fib j : ℝ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) < 21 * (Nat.fib (j + 1) : ℝ) + 18 * (Nat.fib j : ℝ) := by linarith
  have hc : (0 : ℝ) < 4 * (Nat.fib j : ℝ) + 21 * (Nat.fib (j + 1) : ℝ) := by linarith
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (mul_pos (by norm_num) hb) hc)

theorem a_form (j : ℕ) : a (j + 1) =
    18 * ((3 * (Nat.fib j : ℝ) + 18 * (Nat.fib (j + 1) : ℝ)) ^ 2 +
      (21 * (Nat.fib (j + 1) : ℝ) + 18 * (Nat.fib j : ℝ)) *
        (4 * (Nat.fib j : ℝ) + 21 * (Nat.fib (j + 1) : ℝ))) +
    21 * (21 * (Nat.fib (j + 1) : ℝ) + 18 * (Nat.fib j : ℝ)) *
      ((3 * (Nat.fib j : ℝ) + 18 * (Nat.fib (j + 1) : ℝ)) +
        (25 * (Nat.fib (j + 1) : ℝ) + 21 * (Nat.fib j : ℝ))) := by
  have h := key3 3 ((j + 1 : ℕ) : ℤ) (disc_pos j)
  rw [haa, hbb, hcc, hdd, hL6, hF8] at h
  rw [a, if_neg (show ¬ (j + 1 = 0) by omega)]
  linear_combination h

theorem hrec (j : ℕ) : a (j + 4) = 2 * a (j + 3) + 2 * a (j + 2) - a (j + 1) := by
  have g2 := fibC j
  have g3 := fibC (j + 1)
  rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega] at g3
  have g4 := fibC (j + 2)
  rw [show j + 2 + 2 = j + 4 by omega, show j + 2 + 1 = j + 3 by omega] at g4
  have e1 := a_form j
  have e2 := a_form (j + 1)
  rw [show j + 1 + 1 = j + 2 by omega] at e2
  have e3 := a_form (j + 2)
  rw [show j + 2 + 1 = j + 3 by omega] at e3
  have e4 := a_form (j + 3)
  rw [show j + 3 + 1 = j + 4 by omega] at e4
  rw [e4, e3, e2, e1, g4, g3, g2]
  ring

theorem a0 : a 0 = 0 := by
  rw [a, if_pos rfl]

theorem a1 : a 1 = 32733 := by
  have h := a_form 0
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h
  rw [h]
  norm_num

theorem a2 : a 2 = 80361 := by
  have h := a_form 1
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  rw [h]
  norm_num

theorem a3 : a 3 = 215658 := by
  have h := a_form 2
  rw [show (2 : ℕ) + 1 = 3 from rfl] at h
  rw [h]
  norm_num

end FS1A152932

open OMA.S_oeis_a152932 FS1A152932 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152932.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega]
    exact hrec k
  · have e : PowerSeries.mk a *
          ((1 + PowerSeries.X) * (1 - 3 * PowerSeries.X + PowerSeries.X ^ 2)) =
        PowerSeries.mk a
          - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 2 * (PowerSeries.mk a * PowerSeries.X ^ 1)
          - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 2 * (PowerSeries.mk a * PowerSeries.X ^ 2)
          + PowerSeries.mk a * PowerSeries.X ^ 3 := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 2]
      ring
    have e2 : (9 * PowerSeries.X * (3637 + 1655 * PowerSeries.X - 1170 * PowerSeries.X ^ 2) :
          PowerSeries ℝ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 32733
          + PowerSeries.X ^ 2 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 14895
          - PowerSeries.X ^ 3 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 10530 := by
      rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 32733,
        map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 14895,
        map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 10530]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m <;> norm_num [a0, a1, a2, a3]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
        if_pos (show 3 ≤ k + 4 by omega),
        if_neg (show ¬ (k + 4 = 1) by omega), if_neg (show ¬ (k + 4 = 2) by omega),
        if_neg (show ¬ (k + 4 = 3) by omega),
        show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 - 3 = k + 1 by omega, hrec k]
      ring
