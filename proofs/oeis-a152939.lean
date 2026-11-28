import OMAStatements.S_oeis_a152939

-- Problem: A152939: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of four 4-gonal polygonal components chained with string components of length l as l varies.
-- Upstream: formal-conjectures statements/oeis-a152939.lean:0 (declaration OMA.S_oeis_a152939.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: L(4) = 7, F(6) = 8, F(4)^2 = 9. With r = sqrt((d - aa)^2 + 4bc) > 0 one has
-- 2 lambda - d - aa = r, and R lambda^3 + S delta^3 = Q(aa, b, c, d), a polynomial (multiply by r
-- and use r^2 = (d - aa)^2 + 4bc). With g(i) = F(i - 1) (so g(0) = F(-1) = 1, g(i+1) = F(i)) and
-- n = j + 1, the four quantities are linear in g(j), g(j+1), g(j+2), so a(j+1) = P(j) is a cubic
-- form in two consecutive values of a Fibonacci-type sequence; such forms satisfy the order-4
-- recurrence with roots phi^3, -phi, -psi, psi^3 (a polynomial identity, checked by ring). The
-- g.f. follows by comparing coefficients (a(0..4) = 0, 29153, 109649, 486385, 2024613).

namespace FS5A152939

open OMA.S_oeis_a152939

theorem fib_nat (i : ℕ) : fibR (i : ℤ) = (Nat.fib i : ℝ) := by
  unfold fibR
  rw [if_pos (Int.natCast_nonneg i), Int.toNat_natCast]

theorem fib_neg_one : fibR (-1) = 1 := by
  unfold fibR
  rw [if_neg (show ¬ ((0 : ℤ) ≤ -1) by norm_num), show (-(-1 : ℤ)).toNat = 1 from rfl]
  norm_num

theorem hL : lucR (2 * 2) = 7 := by
  unfold lucR
  rw [show (2 * 2 - 1 : ℤ) = ((3 : ℕ) : ℤ) by norm_num,
    show (2 * 2 + 1 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, fib_nat, fib_nat]
  norm_num

theorem hF6 : fibR (2 * 2 + 2) = 8 := by
  rw [show (2 * 2 + 2 : ℤ) = ((6 : ℕ) : ℤ) by norm_num, fib_nat]
  norm_num

theorem hF4 : fibR (2 + 2) ^ 2 = 9 := by
  rw [show (2 + 2 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, fib_nat]
  norm_num

theorem alg (A B C D r : ℝ) (hr2 : r ^ 2 = (D - A) ^ 2 + 4 * B * C) (hr0 : r ≠ 0) :
    (((D + A + r) * (1 / 2) - D) * 7 + B * 8) / (2 * ((D + A + r) * (1 / 2)) - D - A) *
        ((D + A + r) * (1 / 2)) ^ 3 +
      (((D + A + r) * (1 / 2) - A) * 7 - B * 8) / (2 * ((D + A + r) * (1 / 2)) - D - A) *
        ((D + A - r) * (1 / 2)) ^ 3 =
      7 * ((A + D) * ((A + D) ^ 2 - 2 * (A * D - B * C)) - D * ((A + D) ^ 2 - (A * D - B * C))) +
        B * 8 * ((A + D) ^ 2 - (A * D - B * C)) := by
  have hden : 2 * ((D + A + r) * (1 / 2)) - D - A = r := by ring
  rw [hden]
  have hR : (((D + A + r) * (1 / 2) - D) * 7 + B * 8) / r * r =
      ((D + A + r) * (1 / 2) - D) * 7 + B * 8 := div_mul_cancel₀ _ hr0
  have hS : (((D + A + r) * (1 / 2) - A) * 7 - B * 8) / r * r =
      ((D + A + r) * (1 / 2) - A) * 7 - B * 8 := div_mul_cancel₀ _ hr0
  have h1 : ((((D + A + r) * (1 / 2) - D) * 7 + B * 8) / r * ((D + A + r) * (1 / 2)) ^ 3 +
      (((D + A + r) * (1 / 2) - A) * 7 - B * 8) / r * ((D + A - r) * (1 / 2)) ^ 3 -
        (7 * ((A + D) * ((A + D) ^ 2 - 2 * (A * D - B * C)) -
          D * ((A + D) ^ 2 - (A * D - B * C))) +
          B * 8 * ((A + D) ^ 2 - (A * D - B * C)))) * r = 0 := by
    linear_combination ((D + A + r) * (1 / 2)) ^ 3 * hR + ((D + A - r) * (1 / 2)) ^ 3 * hS +
      (r * (7 * (D + 2 * A) / 4 + 2 * B)) * hr2
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hr0)

theorem closed (n : ℤ) (A B C D : ℝ) (hA : aa 2 n = A) (hB : bb 2 n = B) (hC : cc 2 n = C)
    (hD : dd 2 n = D) (hpos : 0 < (D - A) ^ 2 + 4 * B * C) :
    RR 2 n * lamb 2 n ^ 3 + SS 2 n * delt 2 n ^ 3 =
      7 * ((A + D) * ((A + D) ^ 2 - 2 * (A * D - B * C)) - D * ((A + D) ^ 2 - (A * D - B * C))) +
        B * 8 * ((A + D) ^ 2 - (A * D - B * C)) := by
  unfold RR SS lamb delt
  rw [hL, hF6, hA, hB, hC, hD]
  exact alg A B C D _ (Real.sq_sqrt hpos.le) (Real.sqrt_pos.mpr hpos).ne'

end FS5A152939

open OMA.S_oeis_a152939 FS5A152939 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152939.main := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ i : ℕ, g i = fibR ((i : ℤ) - 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ → ℝ → ℝ → ℝ, ∀ A B C D : ℝ, Q A B C D =
      7 * ((A + D) * ((A + D) ^ 2 - 2 * (A * D - B * C)) - D * ((A + D) ^ 2 - (A * D - B * C))) +
        B * 8 * ((A + D) ^ 2 - (A * D - B * C)) := ⟨_, fun _ _ _ _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℝ, ∀ j : ℕ, P j =
      Q (7 * g j + 8 * g (j + 1)) (7 * g (j + 1) + 8 * g (j + 2)) (8 * g j + 9 * g (j + 1))
        (8 * g (j + 1) + 9 * g (j + 2)) := ⟨_, fun _ => rfl⟩
  have g_zero : g 0 = 1 := by
    rw [hg, show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num]
    exact fib_neg_one
  have g_succ : ∀ i : ℕ, g (i + 1) = (Nat.fib i : ℝ) := by
    intro i
    rw [hg, show ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) by omega]
    exact fib_nat i
  have g_rec : ∀ i : ℕ, g (i + 2) = g (i + 1) + g i := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [show g (0 + 2) = g (1 + 1) from rfl, g_succ 1, g_succ 0, g_zero]
      norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [show g (k + 1 + 2) = g (k + 2 + 1) from rfl, g_succ (k + 2), g_succ (k + 1),
        g_succ k, Nat.fib_add_two]
      push_cast
      ring
  have g_nonneg : ∀ i : ℕ, 0 ≤ g i := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [g_zero]
      norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [g_succ]
      exact Nat.cast_nonneg _
  have g_pos2 : ∀ i : ℕ, 1 ≤ g (i + 2) := by
    intro i
    have h := g_succ (i + 1)
    rw [show i + 1 + 1 = i + 2 by omega] at h
    rw [h]
    have h1 : 1 ≤ Nat.fib (i + 1) := by
      have h0 := Nat.fib_pos.mpr (show 0 < i + 1 by omega)
      omega
    exact_mod_cast h1
  have a_succ : ∀ j : ℕ, a (j + 1) = P j := by
    intro j
    have e1 : fibR (((j + 1 : ℕ) : ℤ) - 2) = g j := by
      rw [hg, show ((j + 1 : ℕ) : ℤ) - 2 = (j : ℤ) - 1 by omega]
    have e2 : fibR (((j + 1 : ℕ) : ℤ) - 1) = g (j + 1) := (hg (j + 1)).symm
    have e3 : fibR ((j + 1 : ℕ) : ℤ) = g (j + 2) := by
      rw [hg, show ((j + 2 : ℕ) : ℤ) - 1 = ((j + 1 : ℕ) : ℤ) by omega]
    have haa : aa 2 ((j + 1 : ℕ) : ℤ) = 7 * g j + 8 * g (j + 1) := by
      unfold aa
      rw [hL, hF6, e1, e2]
    have hbb : bb 2 ((j + 1 : ℕ) : ℤ) = 7 * g (j + 1) + 8 * g (j + 2) := by
      unfold bb
      rw [hL, hF6, e2, e3]
    have hcc : cc 2 ((j + 1 : ℕ) : ℤ) = 8 * g j + 9 * g (j + 1) := by
      unfold cc
      rw [hF6, hF4, e1, e2]
    have hdd : dd 2 ((j + 1 : ℕ) : ℤ) = 8 * g (j + 1) + 9 * g (j + 2) := by
      unfold dd
      rw [hF6, hF4, e2, e3]
    have hpos : 0 < (8 * g (j + 1) + 9 * g (j + 2) - (7 * g j + 8 * g (j + 1))) ^ 2 +
        4 * (7 * g (j + 1) + 8 * g (j + 2)) * (8 * g j + 9 * g (j + 1)) := by
      have q0 := g_nonneg j
      have q1 := g_nonneg (j + 1)
      have q2 := g_pos2 j
      have q3 := g_rec j
      have hB : 0 < 7 * g (j + 1) + 8 * g (j + 2) := by linarith
      have hC : 0 < 8 * g j + 9 * g (j + 1) := by linarith
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (mul_pos (by norm_num) hB) hC)
    rw [hP, a, if_neg (show ¬ (j + 1 = 0) by omega), closed _ _ _ _ _ haa hbb hcc hdd hpos, hQ]
  have P_rec : ∀ j : ℕ,
      P (j + 4) = 3 * P (j + 3) + 6 * P (j + 2) - 3 * P (j + 1) - P j := by
    intro j
    have h2 := g_rec j
    have h3 := g_rec (j + 1)
    rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega] at h3
    have h4 := g_rec (j + 2)
    rw [show j + 2 + 2 = j + 4 by omega, show j + 2 + 1 = j + 3 by omega] at h4
    have h5 := g_rec (j + 3)
    rw [show j + 3 + 2 = j + 5 by omega, show j + 3 + 1 = j + 4 by omega] at h5
    have h6 := g_rec (j + 4)
    rw [show j + 4 + 2 = j + 6 by omega, show j + 4 + 1 = j + 5 by omega] at h6
    have e2 : g (j + 2) = g j + g (j + 1) := by linarith
    have e3 : g (j + 3) = g j + 2 * g (j + 1) := by linarith
    have e4 : g (j + 4) = 2 * g j + 3 * g (j + 1) := by linarith
    have e5 : g (j + 5) = 3 * g j + 5 * g (j + 1) := by linarith
    have e6 : g (j + 6) = 5 * g j + 8 * g (j + 1) := by linarith
    rw [hP (j + 4), hP (j + 3), hP (j + 2), hP (j + 1), hP j,
      show j + 4 + 1 = j + 5 by omega, show j + 4 + 2 = j + 6 by omega,
      show j + 3 + 1 = j + 4 by omega, show j + 3 + 2 = j + 5 by omega,
      show j + 2 + 1 = j + 3 by omega, show j + 2 + 2 = j + 4 by omega,
      show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega]
    simp only [hQ, e2, e3, e4, e5, e6]
    ring
  have a_rec : ∀ n : ℕ, 5 ≤ n →
      a n = 3 * a (n - 1) + 6 * a (n - 2) - 3 * a (n - 3) - a (n - 4) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    rw [show j + 5 - 1 = j + 3 + 1 by omega, show j + 5 - 2 = j + 2 + 1 by omega,
      show j + 5 - 3 = j + 1 + 1 by omega, show j + 5 - 4 = j + 1 by omega,
      show j + 5 = j + 4 + 1 by omega, a_succ (j + 4), a_succ (j + 3), a_succ (j + 2),
      a_succ (j + 1), a_succ j]
    exact P_rec j
  have gv1 : g 1 = 0 := by
    have h := g_succ 0
    norm_num at h
    exact h
  have gv2 : g 2 = 1 := by
    have h := g_succ 1
    norm_num at h
    exact h
  have gv3 : g 3 = 1 := by
    have h := g_succ 2
    norm_num at h
    exact h
  have gv4 : g 4 = 2 := by
    have h := g_succ 3
    norm_num at h
    exact h
  have gv5 : g 5 = 3 := by
    have h := g_succ 4
    norm_num at h
    exact h
  have a0 : a 0 = 0 := by
    rw [a, if_pos rfl]
  have a1 : a 1 = 29153 := by
    have h := a_succ 0
    rw [hP, hQ] at h
    norm_num [g_zero, gv1, gv2] at h
    exact h
  have a2 : a 2 = 109649 := by
    have h := a_succ 1
    rw [hP, hQ] at h
    norm_num [gv1, gv2, gv3] at h
    exact h
  have a3 : a 3 = 486385 := by
    have h := a_succ 2
    rw [hP, hQ] at h
    norm_num [gv2, gv3, gv4] at h
    exact h
  have a4 : a 4 = 2024613 := by
    have h := a_succ 3
    rw [hP, hQ] at h
    norm_num [gv3, gv4, gv5] at h
    exact h
  refine ⟨a_rec, ?_⟩
  have e : PowerSeries.mk a * ((1 + PowerSeries.X - PowerSeries.X ^ 2) *
      (1 - 4 * PowerSeries.X - PowerSeries.X ^ 2)) =
      PowerSeries.mk a
        - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 3 * (PowerSeries.mk a * PowerSeries.X ^ 1)
        - (PowerSeries.C : ℝ →+* PowerSeries ℝ) 6 * (PowerSeries.mk a * PowerSeries.X ^ 2)
        + (PowerSeries.C : ℝ →+* PowerSeries ℝ) 3 * (PowerSeries.mk a * PowerSeries.X ^ 3)
        + PowerSeries.mk a * PowerSeries.X ^ 4 := by
    rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 3,
      map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 6]
    ring
  have e2 : (PowerSeries.X * (29153 + 22190 * PowerSeries.X - 17480 * PowerSeries.X ^ 2 -
      4977 * PowerSeries.X ^ 3) : PowerSeries ℝ) =
      PowerSeries.X ^ 1 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 29153
        + PowerSeries.X ^ 2 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 22190
        - PowerSeries.X ^ 3 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 17480
        - PowerSeries.X ^ 4 * (PowerSeries.C : ℝ →+* PowerSeries ℝ) 4977 := by
    rw [map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 29153,
      map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 22190,
      map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 17480,
      map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 4977]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> norm_num [a0, a1, a2, a3, a4]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    rw [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
      if_pos (show 3 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
      if_neg (show ¬ (k + 5 = 1) by omega), if_neg (show ¬ (k + 5 = 2) by omega),
      if_neg (show ¬ (k + 5 = 3) by omega), if_neg (show ¬ (k + 5 = 4) by omega),
      a_rec (k + 5) (by omega)]
    ring
