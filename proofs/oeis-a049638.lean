import OMAStatements.S_oeis_a049638

-- Problem: A049638: a(n) = T(n,4), array T as in A049627.
-- Upstream: formal-conjectures statements/oeis-a049638.lean:0 (declaration OMA.S_oeis_a049638.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with g(i) = #{j <= 4 : gcd(i,j) > 1} we have a(n) = 5(n+1) - Sum_{i <= n} g(i), so
-- a(n+1) = a(n) + 5 - g(n+1). For i >= 2, gcd(i,0) = i > 1, gcd(i,1) = 1, gcd(i,2) > 1 and
-- gcd(i,4) > 1 iff i is even, gcd(i,3) > 1 iff 3 divides i (gcd(i,j) = gcd(i mod j, j)), so
-- g(i) = 1 + 2[2 | i] + [3 | i]. Then g(m+5) + g(m+6) = g(m+2) + g(m+3), which gives
-- a(k+6) - a(k+4) - a(k+3) + a(k+1) = 0, the recurrence of D = (1+x)(1+x+x^2)(x-1)^2
-- = 1 - x^2 - x^3 + x^5. The g.f. follows by comparing coefficients, with a(0..5) = 2, 7, 9, 12, 14, 18.

namespace P1A049638

open OMA.S_oeis_a049638

/-- g(i) = number of j in 0..4 with gcd(i,j) > 1. -/
def g (i : ℕ) : ℤ := ∑ j ∈ Finset.range (4 + 1), if 1 < Nat.gcd i j then (1 : ℤ) else 0

theorem a_formula (n : ℕ) : a n = 5 * ((n : ℤ) + 1) - ∑ i ∈ Finset.range (n + 1), g i := by
  show ((n : ℤ) + 1) * (((4 : ℕ) : ℤ) + 1) - ∑ i ∈ Finset.range (n + 1), g i =
    5 * ((n : ℤ) + 1) - ∑ i ∈ Finset.range (n + 1), g i
  push_cast
  ring

theorem a_succ (n : ℕ) : a (n + 1) = a n + 5 - g (n + 1) := by
  rw [a_formula (n + 1), a_formula n, Finset.sum_range_succ _ (n + 1)]
  push_cast
  ring

theorem t2 (i : ℕ) : (if 1 < Nat.gcd i 2 then (1 : ℤ) else 0) = if i % 2 = 0 then 1 else 0 := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases (show i % 2 = 0 ∨ i % 2 = 1 by omega) with h | h
  · rw [if_pos h, h, Nat.gcd_zero_left, if_pos (show 1 < 2 by norm_num)]
  · rw [if_neg (show ¬ (i % 2 = 0) by omega), h, Nat.gcd_one_left,
      if_neg (show ¬ (1 < 1) by omega)]

theorem t3 (i : ℕ) : (if 1 < Nat.gcd i 3 then (1 : ℤ) else 0) = if i % 3 = 0 then 1 else 0 := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h | h | h
  · rw [if_pos h, h, Nat.gcd_zero_left, if_pos (show 1 < 3 by norm_num)]
  · rw [if_neg (show ¬ (i % 3 = 0) by omega), h, Nat.gcd_one_left,
      if_neg (show ¬ (1 < 1) by omega)]
  · rw [if_neg (show ¬ (i % 3 = 0) by omega), h, show Nat.gcd 2 3 = 1 by norm_num,
      if_neg (show ¬ (1 < 1) by omega)]

theorem t4 (i : ℕ) : (if 1 < Nat.gcd i 4 then (1 : ℤ) else 0) = if i % 2 = 0 then 1 else 0 := by
  rw [Nat.gcd_comm, Nat.gcd_rec]
  rcases (show i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 by omega) with h | h | h | h
  · rw [if_pos (show i % 2 = 0 by omega), h, Nat.gcd_zero_left, if_pos (show 1 < 4 by norm_num)]
  · rw [if_neg (show ¬ (i % 2 = 0) by omega), h, Nat.gcd_one_left,
      if_neg (show ¬ (1 < 1) by omega)]
  · rw [if_pos (show i % 2 = 0 by omega), h, show Nat.gcd 2 4 = 2 by norm_num,
      if_pos (show 1 < 2 by norm_num)]
  · rw [if_neg (show ¬ (i % 2 = 0) by omega), h, show Nat.gcd 3 4 = 1 by norm_num,
      if_neg (show ¬ (1 < 1) by omega)]

theorem gform (i : ℕ) (hi : 2 ≤ i) :
    g i = 1 + 2 * (if i % 2 = 0 then 1 else 0) + (if i % 3 = 0 then 1 else 0) := by
  have e : g i = (if 1 < Nat.gcd i 0 then (1 : ℤ) else 0) + (if 1 < Nat.gcd i 1 then (1 : ℤ) else 0) +
      (if 1 < Nat.gcd i 2 then (1 : ℤ) else 0) + (if 1 < Nat.gcd i 3 then (1 : ℤ) else 0) +
      (if 1 < Nat.gcd i 4 then (1 : ℤ) else 0) := by
    simp only [g, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [e, t2 i, t3 i, t4 i, Nat.gcd_zero_right, Nat.gcd_one_right, if_pos (show 1 < i by omega),
    if_neg (show ¬ ((1 : ℕ) < 1) by omega)]
  ring

theorem g0 : g 0 = 3 := by
  rw [g, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  norm_num

theorem g1 : g 1 = 0 := by
  norm_num [g, Finset.sum_range_succ]

theorem gper (m : ℕ) : g (m + 5) + g (m + 6) = g (m + 2) + g (m + 3) := by
  rw [gform (m + 5) (by omega), gform (m + 6) (by omega), gform (m + 2) (by omega),
    gform (m + 3) (by omega), show (m + 5) % 2 = (m + 3) % 2 by omega,
    show (m + 6) % 2 = (m + 2) % 2 by omega, show (m + 5) % 3 = (m + 2) % 3 by omega,
    show (m + 6) % 3 = (m + 3) % 3 by omega]
  ring

theorem a_rec (k : ℕ) : a (k + 6) - a (k + 4) - a (k + 3) + a (k + 1) = 0 := by
  have h6 : a (k + 6) = a (k + 5) + 5 - g (k + 6) := a_succ (k + 5)
  have h5 : a (k + 5) = a (k + 4) + 5 - g (k + 5) := a_succ (k + 4)
  have h3 : a (k + 3) = a (k + 2) + 5 - g (k + 3) := a_succ (k + 2)
  have h2 : a (k + 2) = a (k + 1) + 5 - g (k + 2) := a_succ (k + 1)
  have hg : g (k + 5) + g (k + 6) = g (k + 2) + g (k + 3) := gper k
  linear_combination h6 + h5 - h3 - h2 - hg

theorem a0 : a 0 = 2 := by
  rw [a_formula 0, Finset.sum_range_succ, Finset.sum_range_zero, g0]
  norm_num

theorem a1 : a 1 = 7 := by
  have h : a 1 = a 0 + 5 - g 1 := a_succ 0
  rw [h, a0, g1]
  norm_num

theorem a2 : a 2 = 9 := by
  have h : a 2 = a 1 + 5 - g 2 := a_succ 1
  rw [h, a1, gform 2 (by norm_num)]
  norm_num

theorem a3 : a 3 = 12 := by
  have h : a 3 = a 2 + 5 - g 3 := a_succ 2
  rw [h, a2, gform 3 (by norm_num)]
  norm_num

theorem a4 : a 4 = 14 := by
  have h : a 4 = a 3 + 5 - g 4 := a_succ 3
  rw [h, a3, gform 4 (by norm_num)]
  norm_num

theorem a5 : a 5 = 18 := by
  have h : a 5 = a 4 + 5 - g 5 := a_succ 4
  rw [h, a4, gform 5 (by norm_num)]
  norm_num

end P1A049638

open OMA.S_oeis_a049638 P1A049638 in
theorem OMA.solution : type_of% @OMA.S_oeis_a049638.main := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℚ, ∀ n, s n = (a n : ℚ) := ⟨_, fun _ => rfl⟩
  have srec : ∀ k, s (k + 6) - s (k + 4) - s (k + 3) + s (k + 1) = 0 := by
    intro k
    rw [hs, hs, hs, hs]
    exact_mod_cast a_rec k
  have s0 : s 0 = 2 := by
    rw [hs]
    exact_mod_cast a0
  have s1 : s 1 = 7 := by
    rw [hs]
    exact_mod_cast a1
  have s2 : s 2 = 9 := by
    rw [hs]
    exact_mod_cast a2
  have s3 : s 3 = 12 := by
    rw [hs]
    exact_mod_cast a3
  have s4 : s 4 = 14 := by
    rw [hs]
    exact_mod_cast a4
  have s5 : s 5 = 18 := by
    rw [hs]
    exact_mod_cast a5
  have e1 : PowerSeries.mk (fun n => (a n : ℚ)) = PowerSeries.mk s := by
    congr 1
    funext n
    show (a n : ℚ) = s n
    rw [hs]
  rw [e1]
  have e : PowerSeries.mk s *
      ((1 + PowerSeries.X) * (1 + PowerSeries.X + PowerSeries.X ^ 2) * (PowerSeries.X - 1) ^ 2) =
      PowerSeries.mk s - PowerSeries.mk s * PowerSeries.X ^ 2 - PowerSeries.mk s * PowerSeries.X ^ 3
        + PowerSeries.mk s * PowerSeries.X ^ 5 := by
    ring
  have e2 : (2 * ((1 + PowerSeries.X) * (1 + PowerSeries.X + PowerSeries.X ^ 2) *
      (PowerSeries.X - 1) ^ 2) -
      PowerSeries.X * (-7 - 9 * PowerSeries.X - 5 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
        3 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 * (PowerSeries.X ^ 1 + PowerSeries.X ^ 2)
        + PowerSeries.X ^ 3 + PowerSeries.X ^ 3 + PowerSeries.X ^ 3
        - PowerSeries.X ^ 4 - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m
    · norm_num [s0]
    · norm_num [s1]
    · norm_num [s0, s2]
    · norm_num [s0, s1, s3]
    · norm_num [s1, s2, s4]
    · norm_num [s0, s2, s3, s5]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
    rw [if_pos (show 2 ≤ k + 6 by omega), if_pos (show 3 ≤ k + 6 by omega),
      if_pos (show 5 ≤ k + 6 by omega), if_neg (show ¬ (k + 6 = 0) by omega),
      if_neg (show ¬ (k + 6 = 1) by omega), if_neg (show ¬ (k + 6 = 2) by omega),
      if_neg (show ¬ (k + 6 = 3) by omega), if_neg (show ¬ (k + 6 = 4) by omega),
      if_neg (show ¬ (k + 6 = 5) by omega), show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 5 = k + 1 by omega]
    linear_combination srec k
