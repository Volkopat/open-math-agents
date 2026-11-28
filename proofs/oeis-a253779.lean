import OMAStatements.S_oeis_a253779

-- Problem: A253779: Numbers c whose cubes are equal to the sum of m^3 consecutive cubes for m^3 not divisible by 3 (A118719).
-- Upstream: formal-conjectures statements/oeis-a253779.lean:0 (declaration OMA.S_oeis_a253779.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: A001651(2i+1) = 3i+1 and A001651(2i+2) = 3i+2, so for each parity a(n) is a
-- polynomial in n, and both closed forms are polynomial identities (n = 0 included for the even
-- one). Together a(n) = U(n) + (-1)^n V(n) with U of degree 5 and V of degree 4, which is killed
-- by (1-x)^6 (1+x)^5 = (x-1)^6 (x+1)^5: this gives the order-11 recurrence, and the g.f. follows
-- by comparing coefficients (the first eleven by evaluation).

open OMA.S_oeis_a253779 in
theorem OMA.solution : type_of% @OMA.S_oeis_a253779.main := by
  have hE : ∀ i : ℕ, a (2 * i) = (81 * ((2 * i : ℕ) : ℚ) ^ 5 - 270 * ((2 * i : ℕ) : ℚ) ^ 4 +
      396 * ((2 * i : ℕ) : ℚ) ^ 3 - 312 * ((2 * i : ℕ) : ℚ) ^ 2 + 96 * ((2 * i : ℕ) : ℚ)) / 64 := by
    intro i
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      norm_num [a, A001651]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hm : A001651 (2 * (j + 1)) = 3 * j + 2 := by
        unfold A001651
        omega
      rw [a, hm]
      push_cast
      ring
  have hO : ∀ i : ℕ, a (2 * i + 1) = (81 * ((2 * i + 1 : ℕ) : ℚ) ^ 5 -
      135 * ((2 * i + 1 : ℕ) : ℚ) ^ 4 + 126 * ((2 * i + 1 : ℕ) : ℚ) ^ 3 -
      66 * ((2 * i + 1 : ℕ) : ℚ) ^ 2 - 15 * ((2 * i + 1 : ℕ) : ℚ) + 9) / 64 := by
    intro i
    have hm : A001651 (2 * i + 1) = 3 * i + 1 := by
      unfold A001651
      omega
    rw [a, hm]
    push_cast
    ring
  have hA : ∀ n : ℕ, a n = (162 * (n : ℚ) ^ 5 - 405 * (n : ℚ) ^ 4 + 522 * (n : ℚ) ^ 3 -
      378 * (n : ℚ) ^ 2 + 81 * (n : ℚ) + 9) / 128 + (-1 : ℚ) ^ n * (-135 * (n : ℚ) ^ 4 +
      270 * (n : ℚ) ^ 3 - 246 * (n : ℚ) ^ 2 + 111 * (n : ℚ) - 9) / 128 := by
    intro n
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' n
    · have h1 : (-1 : ℚ) ^ (2 * i) = 1 := (even_two_mul i).neg_one_pow
      rw [h1, hE i]
      ring
    · have h1 : (-1 : ℚ) ^ (2 * i + 1) = -1 := (odd_two_mul_add_one i).neg_one_pow
      rw [h1, hO i]
      ring
  have hrec : ∀ k : ℕ, a (k + 11) - a (k + 10) - 5 * a (k + 9) + 5 * a (k + 8) +
      10 * a (k + 7) - 10 * a (k + 6) - 10 * a (k + 5) + 10 * a (k + 4) + 5 * a (k + 3) -
      5 * a (k + 2) - a (k + 1) + a k = 0 := by
    intro k
    have hp : ∀ t : ℕ, (-1 : ℚ) ^ (k + t) = (-1 : ℚ) ^ k * (-1 : ℚ) ^ t := fun t => pow_add _ _ _
    rw [hA (k + 11), hA (k + 10), hA (k + 9), hA (k + 8), hA (k + 7), hA (k + 6), hA (k + 5),
      hA (k + 4), hA (k + 3), hA (k + 2), hA (k + 1), hA k, hp 11, hp 10, hp 9, hp 8, hp 7,
      hp 6, hp 5, hp 4, hp 3, hp 2, hp 1]
    generalize (-1 : ℚ) ^ k = s
    push_cast
    ring
  refine ⟨fun n _ hn => ?_, fun n _ hn => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := hn
    rw [show i + i = 2 * i by ring]
    exact hE i
  · obtain ⟨i, rfl⟩ := hn
    exact hO i
  · have a0 : a 0 = 0 := by norm_num [a, A001651]
    have a1 : a 1 = 0 := by norm_num [a, A001651]
    have a2 : a 2 = 6 := by norm_num [a, A001651]
    have a3 : a 3 = 180 := by norm_num [a, A001651]
    have a4 : a 4 = 540 := by norm_num [a, A001651]
    have a5 : a 5 = 2856 := by norm_num [a, A001651]
    have a6 : a 6 = 5544 := by norm_num [a, A001651]
    have a7 : a 7 = 16830 := by norm_num [a, A001651]
    have a8 : a 8 = 27060 := by norm_num [a, A001651]
    have a9 : a 9 = 62244 := by norm_num [a, A001651]
    have a10 : a 10 = 90090 := by norm_num [a, A001651]
    have e : PowerSeries.mk a * ((PowerSeries.X - 1) ^ 6 * (PowerSeries.X + 1) ^ 5) =
        PowerSeries.mk a - PowerSeries.mk a * PowerSeries.X ^ 1
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk a * PowerSeries.X ^ 2)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk a * PowerSeries.X ^ 3)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * (PowerSeries.mk a * PowerSeries.X ^ 4)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * (PowerSeries.mk a * PowerSeries.X ^ 5)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * (PowerSeries.mk a * PowerSeries.X ^ 6)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * (PowerSeries.mk a * PowerSeries.X ^ 7)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk a * PowerSeries.X ^ 8)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk a * PowerSeries.X ^ 9)
          - PowerSeries.mk a * PowerSeries.X ^ 10 + PowerSeries.mk a * PowerSeries.X ^ 11 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10]
      ring
    have e2 : (6 * PowerSeries.X ^ 2 * (PowerSeries.X ^ 8 + 29 * PowerSeries.X ^ 7 +
        55 * PowerSeries.X ^ 6 + 241 * PowerSeries.X ^ 5 + 158 * PowerSeries.X ^ 4 +
        241 * PowerSeries.X ^ 3 + 55 * PowerSeries.X ^ 2 + 29 * PowerSeries.X + 1) :
          PowerSeries ℚ) =
        PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6
          + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 174
          + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 330
          + PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1446
          + PowerSeries.X ^ 6 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 948
          + PowerSeries.X ^ 7 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1446
          + PowerSeries.X ^ 8 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 330
          + PowerSeries.X ^ 9 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 174
          + PowerSeries.X ^ 10 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 174,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 330,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1446,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 948]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge n 11 with hn | hn
    · interval_cases n
      · norm_num [a0]
      · norm_num [a0, a1]
      · norm_num [a0, a1, a2]
      · norm_num [a0, a1, a2, a3]
      · norm_num [a0, a1, a2, a3, a4]
      · norm_num [a0, a1, a2, a3, a4, a5]
      · norm_num [a0, a1, a2, a3, a4, a5, a6]
      · norm_num [a0, a1, a2, a3, a4, a5, a6, a7]
      · norm_num [a0, a1, a2, a3, a4, a5, a6, a7, a8]
      · norm_num [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
      · norm_num [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
      rw [if_pos (show 1 ≤ k + 11 by omega), if_pos (show 2 ≤ k + 11 by omega),
        if_pos (show 3 ≤ k + 11 by omega), if_pos (show 4 ≤ k + 11 by omega),
        if_pos (show 5 ≤ k + 11 by omega), if_pos (show 6 ≤ k + 11 by omega),
        if_pos (show 7 ≤ k + 11 by omega), if_pos (show 8 ≤ k + 11 by omega),
        if_pos (show 9 ≤ k + 11 by omega), if_pos (show 10 ≤ k + 11 by omega),
        if_pos (show 11 ≤ k + 11 by omega),
        if_neg (show ¬ (k + 11 = 2) by omega), if_neg (show ¬ (k + 11 = 3) by omega),
        if_neg (show ¬ (k + 11 = 4) by omega), if_neg (show ¬ (k + 11 = 5) by omega),
        if_neg (show ¬ (k + 11 = 6) by omega), if_neg (show ¬ (k + 11 = 7) by omega),
        if_neg (show ¬ (k + 11 = 8) by omega), if_neg (show ¬ (k + 11 = 9) by omega),
        if_neg (show ¬ (k + 11 = 10) by omega),
        show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega,
        show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega,
        show k + 11 - 5 = k + 6 by omega, show k + 11 - 6 = k + 5 by omega,
        show k + 11 - 7 = k + 4 by omega, show k + 11 - 8 = k + 3 by omega,
        show k + 11 - 9 = k + 2 by omega, show k + 11 - 10 = k + 1 by omega,
        show k + 11 - 11 = k by omega]
      linear_combination hrec k
