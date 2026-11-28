import OMAStatements.S_oeis_a235088

-- Problem: A235088: a(n)*Pi is the total length of irregular spiral (center points: 1, 2, 3, 4) after n rotations.
-- Upstream: formal-conjectures statements/oeis-a235088.lean:0 (declaration OMA.S_oeis_a235088.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: d(n) = 3 + 8 floor(n/2) by induction, hence a(2m+1) = 8m^2 + 6m + 3 and
-- a(2m+2) = 8m^2 + 14m + 6 by induction on m. Every claim then follows by a parity split:
-- the floors and ceilings are evaluated with Int.floor_eq_iff and Int.ceil_eq_iff, the closed form
-- 1 - (-1)^n - n + 2n^2 by ring, the recurrence from the closed form by ring, and the g.f. by
-- comparing coefficients (coefficient m >= 5 is the recurrence, m <= 4 is checked from a(0..4)).

open OMA.S_oeis_a235088 in
theorem OMA.solution : type_of% @OMA.S_oeis_a235088.main := by
  have hd : ∀ n : ℕ, d n = 3 + 8 * (n / 2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show (if (n + 1 + 3) % 2 = 1 then d n + 8 else d n) = 3 + 8 * ((n + 1) / 2)
      split_ifs with h
      · rw [ih]
        omega
      · rw [ih]
        omega
  have step : ∀ n : ℕ, a (n + 2) = a (n + 1) + d (n + 1) := fun n => rfl
  have hA : ∀ m : ℕ, a (2 * m + 1) = 8 * m ^ 2 + 6 * m + 3 ∧
      a (2 * m + 2) = 8 * m ^ 2 + 14 * m + 6 := by
    intro m
    induction m with
    | zero => exact ⟨by decide, by decide⟩
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      have k1 : a (2 * (m + 1) + 1) = 8 * (m + 1) ^ 2 + 6 * (m + 1) + 3 := by
        rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, step,
          show 2 * m + 1 + 1 = 2 * m + 2 by ring, h2, hd, show (2 * m + 2) / 2 = m + 1 by omega]
        ring
      refine ⟨k1, ?_⟩
      have k2 : a (2 * (m + 1) + 2) = a (2 * (m + 1) + 1) + d (2 * (m + 1) + 1) :=
        step (2 * (m + 1))
      rw [k2, k1, hd, show (2 * (m + 1) + 1) / 2 = m + 1 by omega]
      ring
  -- Barker's closed form
  have hB : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 1 - (-1) ^ n - n + 2 * n ^ 2 := by
    intro n hn
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 1 ∨ n = 2 * m + 2 := ⟨(n - 1) / 2, by omega⟩
    · rw [(hA m).1, Odd.neg_one_pow (show Odd (2 * m + 1) from ⟨m, rfl⟩)]
      push_cast
      ring
    · rw [(hA m).2, Even.neg_one_pow (show Even (2 * m + 2) from ⟨m + 1, by ring⟩)]
      push_cast
      ring
  -- Stephan's formula
  have hS : ∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = 2 * ⌊((n : ℚ) - 1) ^ 2 / 4⌋ + 3 * ⌈(n : ℚ) ^ 2 / 2⌉ := by
    intro n hn
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 1 ∨ n = 2 * m + 2 := ⟨(n - 1) / 2, by omega⟩
    · have f1 : ⌊(((2 * m + 1 : ℕ) : ℚ) - 1) ^ 2 / 4⌋ = (m : ℤ) ^ 2 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor
        · linarith
        · linarith
      have c1 : ⌈((2 * m + 1 : ℕ) : ℚ) ^ 2 / 2⌉ = 2 * (m : ℤ) ^ 2 + 2 * m + 1 := by
        rw [Int.ceil_eq_iff]
        push_cast
        constructor
        · linarith
        · linarith
      rw [(hA m).1, f1, c1]
      push_cast
      ring
    · have f2 : ⌊(((2 * m + 2 : ℕ) : ℚ) - 1) ^ 2 / 4⌋ = (m : ℤ) ^ 2 + m := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor
        · linarith
        · linarith
      have c2 : ⌈((2 * m + 2 : ℕ) : ℚ) ^ 2 / 2⌉ = 2 * ((m : ℤ) + 1) ^ 2 := by
        rw [Int.ceil_eq_iff]
        push_cast
        constructor
        · linarith
        · linarith
      rw [(hA m).2, f2, c2]
      push_cast
      ring
  -- Fried's formula
  have hF : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 2 * n ^ 2 + n - 4 * ⌊(n : ℚ) / 2⌋ := by
    intro n hn
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 1 ∨ n = 2 * m + 2 := ⟨(n - 1) / 2, by omega⟩
    · have f1 : ⌊((2 * m + 1 : ℕ) : ℚ) / 2⌋ = (m : ℤ) := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor
        · linarith
        · linarith
      rw [(hA m).1, f1]
      push_cast
      ring
    · have f2 : ⌊((2 * m + 2 : ℕ) : ℚ) / 2⌋ = (m : ℤ) + 1 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor
        · linarith
        · linarith
      rw [(hA m).2, f2]
      push_cast
      ring
  -- Barker's recurrence
  have hrec : ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    rw [show j + 5 - 1 = j + 4 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega]
    rw [hB (j + 5) (by omega), hB (j + 4) (by omega), hB (j + 2) (by omega),
      hB (j + 1) (by omega)]
    push_cast
    ring
  refine ⟨hS, hB, hrec, ?_, hF⟩
  -- Barker's g.f.
  have hq : ∀ n : ℕ, 5 ≤ n →
      (a n : ℚ) = 2 * (a (n - 1) : ℚ) - 2 * (a (n - 3) : ℚ) + (a (n - 4) : ℚ) := by
    intro n hn
    have h := congrArg (Int.cast : ℤ → ℚ) (hrec n hn)
    push_cast at h
    exact h
  have v0 : a 0 = 0 := rfl
  have v1 : a 1 = 3 := rfl
  have v2 : a 2 = 6 := by decide
  have v3 : a 3 = 17 := by decide
  have v4 : a 4 = 28 := by decide
  have eL : PowerSeries.mk (fun n => (a n : ℚ)) * ((PowerSeries.X - 1) ^ 3 * (PowerSeries.X + 1)) =
      PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
        - PowerSeries.mk (fun n => (a n : ℚ)) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have eR : (-PowerSeries.X * (5 * PowerSeries.X ^ 2 + 3) : PowerSeries ℚ) =
      -(PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5)
        - PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
    ring
  rw [eL, eR]
  ext m
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v1, v2]
    · norm_num [v0, v2, v3]
    · norm_num [v0, v1, v3, v4]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [hq m hm]
