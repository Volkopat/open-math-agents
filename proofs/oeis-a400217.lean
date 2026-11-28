import OMAStatements.S_oeis_a400217

-- Problem: A400217: Scaled y-coordinates of the vertices of a Boerdijk-Coxeter helix starting at a tetrahedron with vertices (-1,-1,-1), (1, -1, 1), (-1, 1, 1), and (1, 1, -1).
-- Upstream: formal-conjectures statements/oeis-a400217.lean:0 (declaration OMA.S_oeis_a400217.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the y-coordinates satisfy y(n+4) = (2/3)(y(n+1) + y(n+2) + y(n+3)) - y(n), and
-- a(k+3) = 3^k y(k+3), so a(k+7) - 2a(k+6) - 6a(k+5) - 18a(k+4) + 81a(k+3) = 81 * 3^k * 0 = 0 for all
-- k, the recurrence of (3x-1)^2 (9x^2+4x+1) = 1 - 2x - 6x^2 - 18x^3 + 81x^4. The g.f. follows by
-- comparing coefficients, with a(0..6) = -1, 1, -1, 1, 5, 1, 77 computed from the definition.

namespace P1A400217

open OMA.S_oeis_a400217

theorem yrec (n : ℕ) :
    v (n + 4) 1 = 2 / 3 * (v (n + 1) 1 + v (n + 2) 1 + v (n + 3) 1) - v n 1 := rfl

theorem y0 : v 0 1 = -1 := rfl

theorem y1 : v 1 1 = 1 := rfl

theorem y2 : v 2 1 = -1 := rfl

theorem y3 : v 3 1 = 1 := rfl

theorem y4 : v 4 1 = 5 / 3 := by
  have h : v 4 1 = 2 / 3 * (v 1 1 + v 2 1 + v 3 1) - v 0 1 := yrec 0
  rw [h, y1, y2, y3, y0]
  norm_num

theorem y5 : v 5 1 = 1 / 9 := by
  have h : v 5 1 = 2 / 3 * (v 2 1 + v 3 1 + v 4 1) - v 1 1 := yrec 1
  rw [h, y2, y3, y4, y1]
  norm_num

theorem y6 : v 6 1 = 77 / 27 := by
  have h : v 6 1 = 2 / 3 * (v 3 1 + v 4 1 + v 5 1) - v 2 1 := yrec 2
  rw [h, y3, y4, y5, y2]
  norm_num

theorem a_le (n : ℕ) (h : n ≤ 3) : a n = v n 1 := by
  show (if n ≤ 3 then 1 else (3 : ℚ) ^ (n - 3)) * v n 1 = v n 1
  rw [if_pos h, one_mul]

theorem a_big (n : ℕ) : a (n + 3) = 3 ^ n * v (n + 3) 1 := by
  show (if n + 3 ≤ 3 then 1 else (3 : ℚ) ^ (n + 3 - 3)) * v (n + 3) 1 = 3 ^ n * v (n + 3) 1
  rw [show n + 3 - 3 = n by omega]
  by_cases h : n + 3 ≤ 3
  · rw [if_pos h, show n = 0 by omega, pow_zero]
  · rw [if_neg h]

theorem a_rec (k : ℕ) :
    a (k + 7) - 2 * a (k + 6) - 6 * a (k + 5) - 18 * a (k + 4) + 81 * a (k + 3) = 0 := by
  have h7 : a (k + 7) = 3 ^ (k + 4) * v (k + 7) 1 := a_big (k + 4)
  have h6 : a (k + 6) = 3 ^ (k + 3) * v (k + 6) 1 := a_big (k + 3)
  have h5 : a (k + 5) = 3 ^ (k + 2) * v (k + 5) 1 := a_big (k + 2)
  have h4 : a (k + 4) = 3 ^ (k + 1) * v (k + 4) 1 := a_big (k + 1)
  have h3 : a (k + 3) = 3 ^ k * v (k + 3) 1 := a_big k
  have hy : v (k + 7) 1 = 2 / 3 * (v (k + 4) 1 + v (k + 5) 1 + v (k + 6) 1) - v (k + 3) 1 :=
    yrec (k + 3)
  rw [h7, h6, h5, h4, h3, hy]
  ring

theorem a0 : a 0 = -1 := by
  rw [a_le 0 (by norm_num), y0]

theorem a1 : a 1 = 1 := by
  rw [a_le 1 (by norm_num), y1]

theorem a2 : a 2 = -1 := by
  rw [a_le 2 (by norm_num), y2]

theorem a3 : a 3 = 1 := by
  rw [a_le 3 (by norm_num), y3]

theorem a4 : a 4 = 5 := by
  have h : a 4 = 3 ^ 1 * v 4 1 := a_big 1
  rw [h, y4]
  norm_num

theorem a5 : a 5 = 1 := by
  have h : a 5 = 3 ^ 2 * v 5 1 := a_big 2
  rw [h, y5]
  norm_num

theorem a6 : a 6 = 77 := by
  have h : a 6 = 3 ^ 3 * v 6 1 := a_big 3
  rw [h, y6]
  norm_num

end P1A400217

open OMA.S_oeis_a400217 P1A400217 in
theorem OMA.solution : type_of% @OMA.S_oeis_a400217.main := by
  have e : PowerSeries.mk a *
      ((3 * PowerSeries.X - 1) ^ 2 * (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) =
      PowerSeries.mk a
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk a * PowerSeries.X ^ 1)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk a * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18 * (PowerSeries.mk a * PowerSeries.X ^ 3)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 81 * (PowerSeries.mk a * PowerSeries.X ^ 4) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 81]
    ring
  have e2 : (-54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 - 90 * PowerSeries.X ^ 4 +
        15 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 : PowerSeries ℚ) =
      PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
        + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
        + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15
        + PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84
        - PowerSeries.X ^ 0
        - PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 90
        - PowerSeries.X ^ 6 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 15,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 90,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · interval_cases m
    · norm_num [a0]
    · norm_num [a0, a1]
    · norm_num [a0, a1, a2]
    · norm_num [a0, a1, a2, a3]
    · norm_num [a0, a1, a2, a3, a4]
    · norm_num [a1, a2, a3, a4, a5]
    · norm_num [a2, a3, a4, a5, a6]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
    rw [if_pos (show 1 ≤ k + 7 by omega), if_pos (show 2 ≤ k + 7 by omega),
      if_pos (show 3 ≤ k + 7 by omega), if_pos (show 4 ≤ k + 7 by omega),
      if_neg (show ¬ (k + 7 = 0) by omega), if_neg (show ¬ (k + 7 = 1) by omega),
      if_neg (show ¬ (k + 7 = 2) by omega), if_neg (show ¬ (k + 7 = 3) by omega),
      if_neg (show ¬ (k + 7 = 4) by omega), if_neg (show ¬ (k + 7 = 5) by omega),
      if_neg (show ¬ (k + 7 = 6) by omega),
      show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega]
    linear_combination a_rec k
