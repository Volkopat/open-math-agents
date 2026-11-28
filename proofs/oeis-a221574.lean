import OMAStatements.S_oeis_a221574

-- Problem: A221574: Number of 0..n arrays of length 3 with each element differing from at least one neighbor by something other than 1.
-- Upstream: formal-conjectures statements/oeis-a221574.lean:0 (declaration OMA.S_oeis_a221574.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the condition on x1 follows from the one on x0, so the arrays are the (x0, x1, x2)
-- with x0 and x2 both not adjacent to x1, and a(n) = sum over x1 of c(x1)^2, where c(y) counts the
-- x in 0..n with x not y + 1 and y not x + 1. By induction on n, c(y) = n + 1 - [y + 1 <= n] -
-- [1 <= y <= n + 1]; so c = n at both ends and n - 1 inside, and a(m + 1) = m^3 + 2(m + 1)^2.
-- The recurrence and the g.f. then follow from this cubic (fourth differences vanish).

namespace N10A221574

open OMA.S_oeis_a221574

/-- c(n, y): the number of x in 0..n with neither x = y + 1 nor y = x + 1. -/
def c (n y : ℕ) : ℕ := ∑ x ∈ Finset.range (n + 1), if ¬ (x = y + 1 ∨ y = x + 1) then 1 else 0

theorem ite_and_one (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℕ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem a_eq_sum (n : ℕ) : a n = ∑ y ∈ Finset.range (n + 1), c n y * c n y := by
  have h1 : a n = ((Finset.range (n + 1) ×ˢ (Finset.range (n + 1) ×ˢ Finset.range (n + 1))).filter
      (fun x : ℕ × ℕ × ℕ => ¬ (x.1 = x.2.1 + 1 ∨ x.2.1 = x.1 + 1) ∧
        ¬ (x.2.2 = x.2.1 + 1 ∨ x.2.1 = x.2.2 + 1))).card := by
    unfold a
    congr 1
    apply Finset.filter_congr
    intro x _
    tauto
  rw [h1, Finset.card_filter]
  simp only [Finset.sum_product]
  simp only [ite_and_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  unfold c
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem c_formula (n y : ℕ) : (c n y : ℤ) = (n : ℤ) + 1 - (if y + 1 ≤ n then 1 else 0)
    - (if 1 ≤ y ∧ y ≤ n + 1 then 1 else 0) := by
  induction n with
  | zero =>
    have hs : c 0 y = if ¬ (0 = y + 1 ∨ y = 0 + 1) then 1 else 0 := by
      unfold c
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hs]
    rcases Nat.lt_or_ge y 2 with hy | hy
    · interval_cases y <;> norm_num
    · rw [if_pos (show ¬ (0 = y + 1 ∨ y = 0 + 1) by omega), if_neg (show ¬ (y + 1 ≤ 0) by omega),
        if_neg (show ¬ (1 ≤ y ∧ y ≤ 0 + 1) by omega)]
      norm_num
  | succ k ih =>
    have hs : c (k + 1) y = c k y + (if ¬ (k + 1 = y + 1 ∨ y = k + 1 + 1) then 1 else 0) := by
      unfold c
      rw [Finset.sum_range_succ]
    rw [hs]
    split_ifs at ih ⊢ <;> omega

theorem c_mid (n y : ℕ) (h1 : 1 ≤ y) (h2 : y + 1 ≤ n) : c n y = n - 1 := by
  have h := c_formula n y
  split_ifs at h <;> omega

theorem c_left (n : ℕ) (hn : 1 ≤ n) : c n 0 = n := by
  have h := c_formula n 0
  split_ifs at h <;> omega

theorem c_right (n : ℕ) (hn : 1 ≤ n) : c n n = n := by
  have h := c_formula n n
  split_ifs at h <;> omega

theorem poly (m : ℕ) : a (m + 1) = m ^ 3 + 2 * (m + 1) ^ 2 := by
  rw [a_eq_sum (m + 1), Finset.sum_range_succ, Finset.sum_range_succ',
    c_left (m + 1) (by omega), c_right (m + 1) (by omega)]
  have hmid : ∑ i ∈ Finset.range m, c (m + 1) (i + 1) * c (m + 1) (i + 1) =
      ∑ i ∈ Finset.range m, m * m := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [c_mid (m + 1) (i + 1) (by omega) (by omega), show m + 1 - 1 = m by omega]
  rw [hmid, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

end N10A221574

open OMA.S_oeis_a221574 N10A221574 in
theorem OMA.solution : type_of% @OMA.S_oeis_a221574.main := by
  have q : ∀ m : ℕ, (a (m + 1) : ℚ) = (m : ℚ) ^ 3 + 2 * ((m : ℚ) + 1) ^ 2 := by
    intro m
    exact_mod_cast poly m
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
    rw [show k + 5 - 1 = k + 3 + 1 by omega, show k + 5 - 2 = k + 2 + 1 by omega,
      show k + 5 - 3 = k + 1 + 1 by omega, show k + 5 - 4 = k + 1 by omega,
      show k + 5 = k + 4 + 1 by omega, poly (k + 4), poly (k + 3), poly (k + 2), poly (k + 1),
      poly k]
    push_cast
    ring
  · have v1 : a 1 = 2 := by simpa using poly 0
    have v2 : a 2 = 9 := by simpa using poly 1
    have v3 : a 3 = 26 := by simpa using poly 2
    have v4 : a 4 = 59 := by simpa using poly 3
    have q1 : (a 1 : ℚ) = 2 := by exact_mod_cast v1
    have q2 : (a 2 : ℚ) = 9 := by exact_mod_cast v2
    have q3 : (a 3 : ℚ) = 26 := by exact_mod_cast v3
    have q4 : (a 4 : ℚ) = 59 := by exact_mod_cast v4
    obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ,
        A = PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) := ⟨_, rfl⟩
    rw [← hA]
    have cA : ∀ m, PowerSeries.coeff m A = if m = 0 then (0 : ℚ) else (a m : ℚ) := by
      intro m
      rw [hA, PowerSeries.coeff_mk]
    have h2 : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat _ 2
    have h4 : (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = 4 := map_ofNat _ 4
    have h6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
    have e : A * (1 - PowerSeries.X) ^ 4 =
        A - PowerSeries.C (4 : ℚ) * (A * PowerSeries.X ^ 1) +
          PowerSeries.C (6 : ℚ) * (A * PowerSeries.X ^ 2) -
          PowerSeries.C (4 : ℚ) * (A * PowerSeries.X ^ 3) + A * PowerSeries.X ^ 4 := by
      rw [h4, h6]
      ring
    have e2 : (PowerSeries.X * (2 + PowerSeries.X) * (1 + PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 +
          PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
      rw [h2]
      ring
    refine e.trans (Eq.trans ?_ e2.symm)
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
    rcases Nat.lt_or_ge m 5 with hm | hm
    · interval_cases m <;> simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow] <;>
        norm_num [q1, q2, q3, q4]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
      have t0 : PowerSeries.coeff (k + 5) A = (a (k + 5) : ℚ) := by
        rw [cA, if_neg (show ¬(k + 5 = 0) by omega)]
      have t1 : PowerSeries.coeff (k + 5) (A * PowerSeries.X ^ 1) = (a (k + 4) : ℚ) := by
        rw [show k + 5 = k + 4 + 1 by omega, PowerSeries.coeff_mul_X_pow, cA,
          if_neg (show ¬(k + 4 = 0) by omega)]
      have t2 : PowerSeries.coeff (k + 5) (A * PowerSeries.X ^ 2) = (a (k + 3) : ℚ) := by
        rw [show k + 5 = k + 3 + 2 by omega, PowerSeries.coeff_mul_X_pow, cA,
          if_neg (show ¬(k + 3 = 0) by omega)]
      have t3 : PowerSeries.coeff (k + 5) (A * PowerSeries.X ^ 3) = (a (k + 2) : ℚ) := by
        rw [show k + 5 = k + 2 + 3 by omega, PowerSeries.coeff_mul_X_pow, cA,
          if_neg (show ¬(k + 2 = 0) by omega)]
      have t4 : PowerSeries.coeff (k + 5) (A * PowerSeries.X ^ 4) = (a (k + 1) : ℚ) := by
        rw [show k + 5 = k + 1 + 4 by omega, PowerSeries.coeff_mul_X_pow, cA,
          if_neg (show ¬(k + 1 = 0) by omega)]
      have u1 : PowerSeries.coeff (k + 5) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 5 = 1) by omega)]
      have u2 : PowerSeries.coeff (k + 5) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 5 = 2) by omega)]
      have u3 : PowerSeries.coeff (k + 5) (PowerSeries.X ^ 3 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 5 = 3) by omega)]
      have u4 : PowerSeries.coeff (k + 5) (PowerSeries.X ^ 4 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 5 = 4) by omega)]
      rw [t0, t1, t2, t3, t4, u1, u2, u3, u4]
      have r4 := q (k + 4)
      have r3 := q (k + 3)
      have r2 := q (k + 2)
      have r1 := q (k + 1)
      have r0 := q k
      rw [show k + 4 + 1 = k + 5 by omega] at r4
      rw [show k + 3 + 1 = k + 4 by omega] at r3
      rw [show k + 2 + 1 = k + 3 by omega] at r2
      rw [show k + 1 + 1 = k + 2 by omega] at r1
      push_cast at r4 r3 r2 r1
      linear_combination r4 - 4 * r3 + 6 * r2 - 4 * r1 + r0
