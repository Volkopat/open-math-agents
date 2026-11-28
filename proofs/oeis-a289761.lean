import OMAStatements.S_oeis_a289761

-- Problem: A289761: Maximum length of a perfect Wichmann ruler with n segments.
-- Upstream: formal-conjectures statements/oeis-a289761.lean:0 (declaration OMA.S_oeis_a289761.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (n + 6) mod 6 = n mod 6 and (n + 6)^2 = n^2 + 3 (4n + 12), so the exact division
-- gives a(n + 6) = a(n) + 4n + 18 for every n. Hence a(n) - 2a(n-1) + a(n-2) equals
-- a(n-6) - 2a(n-7) + a(n-8) (the linear terms cancel), which is the recurrence. The denominator
-- (1 - x)^3 (1 + x) (1 - x + x^2) (1 + x + x^2) is 1 - 2x + x^2 - x^6 + 2x^7 - x^8, so the
-- coefficient of x^m in (Sum a(n+2) x^n) times it vanishes for m >= 8 by the recurrence, and
-- for m < 8 it is computed from a(2..9) = 3, 6, 9, 12, 15, 22, 29, 36.

namespace P1A289761

open OMA.S_oeis_a289761

theorem hdiv (N r : ℤ) : ((N + 6) ^ 2 - r) / 3 = (N ^ 2 - r) / 3 + 4 * N + 12 := by
  rw [show (N + 6) ^ 2 - r = (N ^ 2 - r) + (4 * N + 12) * 3 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num : (3 : ℤ) ≠ 0)]
  ring

theorem hstep (N : ℤ) : ((N + 6) ^ 2 - ((N + 6) % 6 - 3) ^ 2) / 3 + (N + 6) =
    (N ^ 2 - (N % 6 - 3) ^ 2) / 3 + N + 4 * N + 18 := by
  rw [Int.add_emod_right, hdiv]
  ring

theorem shift (n : ℕ) : a (n + 6) = a n + 4 * (n : ℤ) + 18 := by
  have hc : ((n + 6 : ℕ) : ℤ) = (n : ℤ) + 6 := by norm_num
  unfold a
  rw [hc]
  exact hstep (n : ℤ)

theorem arec (k : ℕ) :
    a (k + 10) = 2 * a (k + 9) - a (k + 8) + a (k + 4) - 2 * a (k + 3) + a (k + 2) := by
  have h1 : a (k + 10) = a (k + 4) + 4 * ((k + 4 : ℕ) : ℤ) + 18 := shift (k + 4)
  have h2 : a (k + 9) = a (k + 3) + 4 * ((k + 3 : ℕ) : ℤ) + 18 := shift (k + 3)
  have h3 : a (k + 8) = a (k + 2) + 4 * ((k + 2 : ℕ) : ℤ) + 18 := shift (k + 2)
  push_cast at h1 h2 h3
  linear_combination h1 - 2 * h2 + h3

theorem gf : PowerSeries.mk (fun n => (a (n + 2) : ℚ)) *
    ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) * (1 - PowerSeries.X + PowerSeries.X ^ 2) *
      (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
    (3 : PowerSeries ℚ) + 4 * PowerSeries.X ^ 5 - 3 * PowerSeries.X ^ 6 := by
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = (a (n + 2) : ℚ) := ⟨_, fun _ => rfl⟩
  have hmk : PowerSeries.mk (fun n => (a (n + 2) : ℚ)) = PowerSeries.mk b := by
    congr 1
    funext n
    exact (hb n).symm
  have hq : ∀ m, 8 ≤ m → b m - 2 * b (m - 1) + b (m - 2) - b (m - 6) + 2 * b (m - 7) -
      b (m - 8) = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
    rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega,
      show k + 8 - 8 = k by omega,
      hb (k + 8), hb (k + 7), hb (k + 6), hb (k + 2), hb (k + 1), hb k,
      show k + 8 + 2 = k + 10 by omega, show k + 7 + 2 = k + 9 by omega,
      show k + 6 + 2 = k + 8 by omega, show k + 2 + 2 = k + 4 by omega,
      show k + 1 + 2 = k + 3 by omega]
    have h : (a (k + 10) : ℚ) = 2 * (a (k + 9) : ℚ) - (a (k + 8) : ℚ) + (a (k + 4) : ℚ) -
        2 * (a (k + 3) : ℚ) + (a (k + 2) : ℚ) := by
      exact_mod_cast arec k
    linarith
  rw [hmk]
  have e : PowerSeries.mk b *
      ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) * (1 - PowerSeries.X + PowerSeries.X ^ 2) *
        (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      PowerSeries.mk b
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk b * PowerSeries.X ^ 1)
        + PowerSeries.mk b * PowerSeries.X ^ 2
        - PowerSeries.mk b * PowerSeries.X ^ 6
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk b * PowerSeries.X ^ 7)
        - PowerSeries.mk b * PowerSeries.X ^ 8 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have e2 : (3 : PowerSeries ℚ) + 4 * PowerSeries.X ^ 5 - 3 * PowerSeries.X ^ 6 =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * PowerSeries.X ^ 0
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * PowerSeries.X ^ 5
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * PowerSeries.X ^ 6 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases Nat.lt_or_ge m 8 with hm | hm
  · interval_cases m
    · norm_num [hb, a]
    · norm_num [hb, a]
    · norm_num [hb, a]
    · norm_num [hb, a]
    · norm_num [hb, a]
    · norm_num [hb, a]
    · norm_num [hb, a]
    · norm_num [hb, a]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [hq m hm]

end P1A289761

open OMA.S_oeis_a289761 P1A289761 in
theorem OMA.solution : type_of% @OMA.S_oeis_a289761.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    rw [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega,
      show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega,
      show k + 10 - 8 = k + 2 by omega]
    exact arec k
  · calc PowerSeries.X ^ 2 * PowerSeries.mk (fun n => (a (n + 2) : ℚ)) *
          ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) *
            (1 - PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X + PowerSeries.X ^ 2))
        = PowerSeries.X ^ 2 * (PowerSeries.mk (fun n => (a (n + 2) : ℚ)) *
          ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) *
            (1 - PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X + PowerSeries.X ^ 2))) := by
          ring
      _ = PowerSeries.X ^ 2 * ((3 : PowerSeries ℚ) + 4 * PowerSeries.X ^ 5 -
          3 * PowerSeries.X ^ 6) := by
          rw [gf]
