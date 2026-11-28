import OMAStatements.S_oeis_a253778

-- Problem: A253778: Numbers b that are the first of m^3 consecutive cubes whose sum is a cube c^3, where m^3 is not divisible by 3 (A118719).
-- Upstream: formal-conjectures statements/oeis-a253778.lean:0 (declaration OMA.S_oeis_a253778.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: A001651(2i+1) = 3i+1 and A001651(2i+2) = 3i+2, so for each parity a(n) is a
-- polynomial in n, and both closed forms are polynomial identities. Together, for n >= 1,
-- a(n) = U(n) + (-1)^n V(n) with U of degree 4 and V of degree 3, which is killed by
-- (x-1)^5 (x+1)^4: this gives the order-9 recurrence for b(n) = a(n+1), and the g.f. follows by
-- comparing coefficients (the first nine by evaluation).

open OMA.S_oeis_a253778 in
theorem OMA.solution : type_of% @OMA.S_oeis_a253778.main := by
  have hE : ∀ j : ℕ, a (2 * j + 2) = (54 * ((2 * j + 2 : ℕ) : ℚ) ^ 4 -
      252 * ((2 * j + 2 : ℕ) : ℚ) ^ 3 + 312 * ((2 * j + 2 : ℕ) : ℚ) ^ 2 -
      144 * ((2 * j + 2 : ℕ) : ℚ) + 64) / 64 := by
    intro j
    have hm : A001651 (2 * j + 2) = 3 * j + 2 := by
      unfold A001651
      omega
    rw [a, hm]
    push_cast
    ring
  have hO : ∀ i : ℕ, a (2 * i + 1) = (54 * ((2 * i + 1 : ℕ) : ℚ) ^ 4 -
      180 * ((2 * i + 1 : ℕ) : ℚ) ^ 3 + 96 * ((2 * i + 1 : ℕ) : ℚ) ^ 2 -
      12 * ((2 * i + 1 : ℕ) : ℚ) + 42) / 64 := by
    intro i
    have hm : A001651 (2 * i + 1) = 3 * i + 1 := by
      unfold A001651
      omega
    rw [a, hm]
    push_cast
    ring
  have hA : ∀ n : ℕ, a (n + 1) = (108 * ((n : ℚ) + 1) ^ 4 - 432 * ((n : ℚ) + 1) ^ 3 +
      408 * ((n : ℚ) + 1) ^ 2 - 156 * ((n : ℚ) + 1) + 106) / 128 -
      (-1 : ℚ) ^ n * (-72 * ((n : ℚ) + 1) ^ 3 + 216 * ((n : ℚ) + 1) ^ 2 -
        132 * ((n : ℚ) + 1) + 22) / 128 := by
    intro n
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [(even_two_mul i).neg_one_pow, hO i]
      push_cast
      ring
    · rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring, (odd_two_mul_add_one i).neg_one_pow, hE i]
      push_cast
      ring
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = a (n + 1) := ⟨_, fun _ => rfl⟩
  have hbq : ∀ n : ℕ, b n = (108 * ((n : ℚ) + 1) ^ 4 - 432 * ((n : ℚ) + 1) ^ 3 +
      408 * ((n : ℚ) + 1) ^ 2 - 156 * ((n : ℚ) + 1) + 106) / 128 -
      (-1 : ℚ) ^ n * (-72 * ((n : ℚ) + 1) ^ 3 + 216 * ((n : ℚ) + 1) ^ 2 -
        132 * ((n : ℚ) + 1) + 22) / 128 :=
    fun n => (hb n).trans (hA n)
  have hrec : ∀ m, 9 ≤ m → -b m + b (m - 1) + 4 * b (m - 2) - 4 * b (m - 3) - 6 * b (m - 4) +
      6 * b (m - 5) + 4 * b (m - 6) - 4 * b (m - 7) - b (m - 8) + b (m - 9) = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 9 := ⟨m - 9, by omega⟩
    rw [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega,
      show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega,
      show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega,
      show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega,
      show k + 9 - 9 = k by omega,
      hbq (k + 9), hbq (k + 8), hbq (k + 7), hbq (k + 6), hbq (k + 5), hbq (k + 4),
      hbq (k + 3), hbq (k + 2), hbq (k + 1), hbq k]
    have hp : ∀ t : ℕ, (-1 : ℚ) ^ (k + t) = (-1 : ℚ) ^ k * (-1 : ℚ) ^ t := fun t => pow_add _ _ _
    rw [hp 9, hp 8, hp 7, hp 6, hp 5, hp 4, hp 3, hp 2, hp 1]
    generalize (-1 : ℚ) ^ k = s
    push_cast
    ring
  refine ⟨fun n hn1 hn => ?_, fun n _ hn => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := hn
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [show j + 1 + (j + 1) = 2 * j + 2 by ring]
    exact hE j
  · obtain ⟨i, rfl⟩ := hn
    exact hO i
  · have hmk : PowerSeries.mk (fun n => a (n + 1)) = PowerSeries.mk b := by
      congr 1
      funext n
      exact (hb n).symm
    have gfb : PowerSeries.mk b * ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) ^ 4) =
        -PowerSeries.X * (PowerSeries.X ^ 7 + 5 * PowerSeries.X ^ 6 + 60 * PowerSeries.X ^ 5 +
          69 * PowerSeries.X ^ 4 + 147 * PowerSeries.X ^ 3 + 36 * PowerSeries.X ^ 2 +
          8 * PowerSeries.X - 2) := by
      have e : PowerSeries.mk b * ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) ^ 4) =
          -PowerSeries.mk b + PowerSeries.mk b * PowerSeries.X ^ 1
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk b * PowerSeries.X ^ 2)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk b * PowerSeries.X ^ 3)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk b * PowerSeries.X ^ 4)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk b * PowerSeries.X ^ 5)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk b * PowerSeries.X ^ 6)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk b * PowerSeries.X ^ 7)
            - PowerSeries.mk b * PowerSeries.X ^ 8 + PowerSeries.mk b * PowerSeries.X ^ 9 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
        ring
      have e2 : (-PowerSeries.X * (PowerSeries.X ^ 7 + 5 * PowerSeries.X ^ 6 +
          60 * PowerSeries.X ^ 5 + 69 * PowerSeries.X ^ 4 + 147 * PowerSeries.X ^ 3 +
          36 * PowerSeries.X ^ 2 + 8 * PowerSeries.X - 2) : PowerSeries ℚ) =
          PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
            - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8
            - PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36
            - PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 147
            - PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 69
            - PowerSeries.X ^ 6 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 60
            - PowerSeries.X ^ 7 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5
            - PowerSeries.X ^ 8 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 147,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 69,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 60,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5]
        ring
      rw [e, e2]
      ext m
      simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
        PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
      rcases Nat.lt_or_ge m 9 with hm | hm
      · interval_cases m
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
      · simp (disch := omega) only [if_pos, if_neg]
        linarith [hrec m hm]
    rw [hmk]
    calc PowerSeries.X * PowerSeries.mk b * ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) ^ 4)
        = PowerSeries.X * (PowerSeries.mk b *
          ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) ^ 4)) := by
          ring
      _ = PowerSeries.X * (-PowerSeries.X * (PowerSeries.X ^ 7 + 5 * PowerSeries.X ^ 6 +
          60 * PowerSeries.X ^ 5 + 69 * PowerSeries.X ^ 4 + 147 * PowerSeries.X ^ 3 +
          36 * PowerSeries.X ^ 2 + 8 * PowerSeries.X - 2)) := by
          rw [gfb]
      _ = -PowerSeries.X ^ 2 * (PowerSeries.X ^ 7 + 5 * PowerSeries.X ^ 6 +
          60 * PowerSeries.X ^ 5 + 69 * PowerSeries.X ^ 4 + 147 * PowerSeries.X ^ 3 +
          36 * PowerSeries.X ^ 2 + 8 * PowerSeries.X - 2) := by
          ring
