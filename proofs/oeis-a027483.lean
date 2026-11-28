import OMAStatements.S_oeis_a027483

-- Problem: A027483: Second subdiagonal of triangle A027478, constructed from the Stirling numbers of the first kind.
-- Upstream: formal-conjectures statements/oeis-a027483.lean:0 (declaration OMA.S_oeis_a027483.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: A(i, j) = 0 for j > i, so in T(n, n-2) = n!^3 Sum_{k,l} A(n,k) A(k,l) A(l,n-2) only the
-- six terms with n-2 <= l <= k <= n remain. With |s(i,i)| = 1, |s(i+1,i)| = C(i+1,2) and
-- |s(i+2,i)| = (i+2)(i+1)i(3i+5)/24 (induction on the Stirling recurrence) this gives
-- a(m+3) = P(m) for an explicit polynomial P of degree 8. Then (1 - x)^9 annihilates P (a ring
-- identity), which gives the recurrence, and the g.f. follows by comparing coefficients.

namespace P1A027483

open OMA.S_oeis_a027483

theorem Azero (i k : ℕ) (h : i < k) : A i k = 0 := by
  show (Nat.stirlingFirst i k : ℚ) / (i.factorial : ℚ) = 0
  rw [Nat.stirlingFirst_eq_zero_of_lt h, Nat.cast_zero, zero_div]

theorem sum3 (m : ℕ) (g : ℕ → ℚ) (hg : ∀ l, l ≤ m → g l = 0) :
    ∑ l ∈ Finset.Icc 1 (m + 3), g l = g (m + 1) + g (m + 2) + g (m + 3) := by
  have h0 : ∑ l ∈ Finset.Icc 1 m, g l = 0 :=
    Finset.sum_eq_zero (fun l hl => hg l (Finset.mem_Icc.mp hl).2)
  have h1 : ∑ l ∈ Finset.Icc 1 (m + 1), g l = g (m + 1) := by
    rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega), h0, zero_add]
  have h2 : ∑ l ∈ Finset.Icc 1 (m + 1 + 1), g l = g (m + 1) + g (m + 1 + 1) := by
    rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 + 1 by omega), h1]
  have h3 : ∑ l ∈ Finset.Icc 1 (m + 1 + 1 + 1), g l =
      g (m + 1) + g (m + 1 + 1) + g (m + 1 + 1 + 1) := by
    rw [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 + 1 + 1 by omega), h2]
  exact h3

theorem dsum (m : ℕ) (f : ℕ → ℕ → ℚ) (hz : ∀ k l, l ≤ m ∨ k < l → f k l = 0) :
    ∑ k ∈ Finset.Icc 1 (m + 3), ∑ l ∈ Finset.Icc 1 (m + 3), f k l =
      f (m + 1) (m + 1) + f (m + 2) (m + 1) + f (m + 2) (m + 2) + f (m + 3) (m + 1) +
        f (m + 3) (m + 2) + f (m + 3) (m + 3) := by
  have hrow : ∀ k, ∑ l ∈ Finset.Icc 1 (m + 3), f k l = f k (m + 1) + f k (m + 2) + f k (m + 3) :=
    fun k => sum3 m (f k) (fun l hl => hz k l (Or.inl hl))
  have hcol : ∀ k, k ≤ m → ∑ l ∈ Finset.Icc 1 (m + 3), f k l = 0 := by
    intro k hk
    rw [hrow k, hz k (m + 1) (Or.inr (by omega)), hz k (m + 2) (Or.inr (by omega)),
      hz k (m + 3) (Or.inr (by omega)), add_zero, add_zero]
  rw [sum3 m (fun k => ∑ l ∈ Finset.Icc 1 (m + 3), f k l) hcol, hrow (m + 1), hrow (m + 2),
    hrow (m + 3), hz (m + 1) (m + 2) (Or.inr (by omega)), hz (m + 1) (m + 3) (Or.inr (by omega)),
    hz (m + 2) (m + 3) (Or.inr (by omega))]
  ring

theorem s1 (n : ℕ) : (Nat.stirlingFirst (n + 1) n : ℚ) = ((n : ℚ) + 1) * (n : ℚ) / 2 := by
  rw [Nat.stirlingFirst_succ_self_left, Nat.cast_choose_two, Nat.cast_add_one]
  ring

theorem s2 (n : ℕ) : (Nat.stirlingFirst (n + 2) n : ℚ) =
    ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n : ℚ) * (3 * (n : ℚ) + 5) / 24 := by
  induction n with
  | zero =>
    rw [show Nat.stirlingFirst (0 + 2) 0 = 0 from rfl]
    simp
  | succ k ih =>
    have h : Nat.stirlingFirst (k + 1 + 2) (k + 1) =
        (k + 2) * Nat.stirlingFirst (k + 2) (k + 1) + Nat.stirlingFirst (k + 2) k :=
      Nat.stirlingFirst_succ_succ (k + 2) k
    have h1 : (Nat.stirlingFirst (k + 2) (k + 1) : ℚ) = ((k : ℚ) + 2) * ((k : ℚ) + 1) / 2 := by
      have h' : (Nat.stirlingFirst (k + 2) (k + 1) : ℚ) =
          (((k + 1 : ℕ) : ℚ) + 1) * ((k + 1 : ℕ) : ℚ) / 2 := s1 (k + 1)
      rw [h', Nat.cast_add_one]
      ring
    rw [h]
    push_cast
    rw [h1, ih]
    ring

/-- a(m+3) as an explicit polynomial in m. -/
def P (m : ℕ) : ℚ :=
  ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (3 * (m : ℚ) + 8) / 24 *
      (1 + ((m : ℚ) + 3) * ((m : ℚ) + 2) + (((m : ℚ) + 3) * ((m : ℚ) + 2)) ^ 2) +
    ((m : ℚ) + 3) * ((m : ℚ) + 2) / 2 * (((m : ℚ) + 2) * ((m : ℚ) + 1) / 2) *
      (((m : ℚ) + 3) + ((m : ℚ) + 3) ^ 2 + ((m : ℚ) + 3) ^ 2 * ((m : ℚ) + 2))

theorem a_closed (m : ℕ) : a (m + 3) = P m := by
  have hz : ∀ k l, l ≤ m ∨ k < l → A (m + 3) k * A k l * A l (m + 1) = 0 := by
    intro k l h
    rcases h with h | h
    · rw [Azero l (m + 1) (by omega), mul_zero]
    · rw [Azero k l h, mul_zero, zero_mul]
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ m
  have f2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ (m + 1)
  have f3 : ((m + 3).factorial : ℚ) = ((m : ℚ) + 3) * ((m + 2).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ (m + 2)
  have c11 : (Nat.stirlingFirst (m + 1) (m + 1) : ℚ) = 1 := by
    rw [Nat.stirlingFirst_self, Nat.cast_one]
  have c22 : (Nat.stirlingFirst (m + 2) (m + 2) : ℚ) = 1 := by
    rw [Nat.stirlingFirst_self, Nat.cast_one]
  have c33 : (Nat.stirlingFirst (m + 3) (m + 3) : ℚ) = 1 := by
    rw [Nat.stirlingFirst_self, Nat.cast_one]
  have c21 : (Nat.stirlingFirst (m + 2) (m + 1) : ℚ) = ((m : ℚ) + 2) * ((m : ℚ) + 1) / 2 := by
    have h' : (Nat.stirlingFirst (m + 2) (m + 1) : ℚ) =
        (((m + 1 : ℕ) : ℚ) + 1) * ((m + 1 : ℕ) : ℚ) / 2 := s1 (m + 1)
    rw [h', Nat.cast_add_one]
    ring
  have c32 : (Nat.stirlingFirst (m + 3) (m + 2) : ℚ) = ((m : ℚ) + 3) * ((m : ℚ) + 2) / 2 := by
    have h' : (Nat.stirlingFirst (m + 3) (m + 2) : ℚ) =
        (((m + 2 : ℕ) : ℚ) + 1) * ((m + 2 : ℕ) : ℚ) / 2 := s1 (m + 2)
    rw [h']
    push_cast
    ring
  have c31 : (Nat.stirlingFirst (m + 3) (m + 1) : ℚ) =
      ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (3 * (m : ℚ) + 8) / 24 := by
    have h' : (Nat.stirlingFirst (m + 3) (m + 1) : ℚ) =
        (((m + 1 : ℕ) : ℚ) + 2) * (((m + 1 : ℕ) : ℚ) + 1) * ((m + 1 : ℕ) : ℚ) *
          (3 * ((m + 1 : ℕ) : ℚ) + 5) / 24 := s2 (m + 1)
    rw [h', Nat.cast_add_one]
    ring
  have hF : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (m : ℚ) + 3 ≠ 0 := by positivity
  show ((m + 3).factorial : ℚ) ^ 3 * ∑ k ∈ Finset.Icc 1 (m + 3), ∑ l ∈ Finset.Icc 1 (m + 3),
    A (m + 3) k * A k l * A l (m + 3 - 2) = P m
  rw [show m + 3 - 2 = m + 1 by omega, dsum m (fun k l => A (m + 3) k * A k l * A l (m + 1)) hz]
  unfold A
  rw [c11, c22, c33, c21, c32, c31, f3, f2, f1]
  unfold P
  field_simp
  ring

theorem Prec (k : ℕ) : P (k + 9) - 9 * P (k + 8) + 36 * P (k + 7) - 84 * P (k + 6) +
    126 * P (k + 5) - 126 * P (k + 4) + 84 * P (k + 3) - 36 * P (k + 2) + 9 * P (k + 1) -
    P k = 0 := by
  unfold P
  push_cast
  ring

theorem gf : PowerSeries.mk P * (1 - PowerSeries.X) ^ 9 =
    (176 : PowerSeries ℚ) + 1367 * PowerSeries.X + 2312 * PowerSeries.X ^ 2 +
      1072 * PowerSeries.X ^ 3 + 112 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5 := by
  have e : PowerSeries.mk P * (1 - PowerSeries.X) ^ 9 =
      PowerSeries.mk P
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9 * (PowerSeries.mk P * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36 * (PowerSeries.mk P * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84 * (PowerSeries.mk P * PowerSeries.X ^ 3)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 126 * (PowerSeries.mk P * PowerSeries.X ^ 4)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 126 * (PowerSeries.mk P * PowerSeries.X ^ 5)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84 * (PowerSeries.mk P * PowerSeries.X ^ 6)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36 * (PowerSeries.mk P * PowerSeries.X ^ 7)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9 * (PowerSeries.mk P * PowerSeries.X ^ 8)
        - PowerSeries.mk P * PowerSeries.X ^ 9 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 126]
    ring
  have e2 : (176 : PowerSeries ℚ) + 1367 * PowerSeries.X + 2312 * PowerSeries.X ^ 2 +
      1072 * PowerSeries.X ^ 3 + 112 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5 =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 176
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1367 * PowerSeries.X ^ 1
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2312 * PowerSeries.X ^ 2
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1072 * PowerSeries.X ^ 3
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 112 * PowerSeries.X ^ 4
        + PowerSeries.X ^ 5 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 176,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1367,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2312,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1072,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 112]
    ring
  rw [e, e2]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    rw [if_pos (show 1 ≤ k + 9 by omega), if_pos (show 2 ≤ k + 9 by omega),
      if_pos (show 3 ≤ k + 9 by omega), if_pos (show 4 ≤ k + 9 by omega),
      if_pos (show 5 ≤ k + 9 by omega), if_pos (show 6 ≤ k + 9 by omega),
      if_pos (show 7 ≤ k + 9 by omega), if_pos (show 8 ≤ k + 9 by omega),
      if_pos (show 9 ≤ k + 9 by omega),
      if_pos (show 1 ≤ k + 9 by omega), if_pos (show 2 ≤ k + 9 by omega),
      if_pos (show 3 ≤ k + 9 by omega), if_pos (show 4 ≤ k + 9 by omega),
      if_neg (show ¬ (k + 9 = 0) by omega), if_neg (show ¬ (k + 9 = 5) by omega),
      show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega,
      show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega,
      show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega,
      show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega,
      show k + 9 - 9 = k by omega,
      if_neg (show ¬ (k + 8 = 0) by omega), if_neg (show ¬ (k + 7 = 0) by omega),
      if_neg (show ¬ (k + 6 = 0) by omega), if_neg (show ¬ (k + 5 = 0) by omega)]
    linear_combination Prec k

end P1A027483

open OMA.S_oeis_a027483 P1A027483 in
theorem OMA.solution : type_of% @OMA.S_oeis_a027483.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    rw [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
      show m + 12 - 3 = m + 9 by omega, show m + 12 - 4 = m + 8 by omega,
      show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega,
      show m + 12 - 7 = m + 5 by omega, show m + 12 - 8 = m + 4 by omega,
      show m + 12 - 9 = m + 3 by omega]
    have q0 : a (m + 3) = P m := a_closed m
    have q1 : a (m + 4) = P (m + 1) := a_closed (m + 1)
    have q2 : a (m + 5) = P (m + 2) := a_closed (m + 2)
    have q3 : a (m + 6) = P (m + 3) := a_closed (m + 3)
    have q4 : a (m + 7) = P (m + 4) := a_closed (m + 4)
    have q5 : a (m + 8) = P (m + 5) := a_closed (m + 5)
    have q6 : a (m + 9) = P (m + 6) := a_closed (m + 6)
    have q7 : a (m + 10) = P (m + 7) := a_closed (m + 7)
    have q8 : a (m + 11) = P (m + 8) := a_closed (m + 8)
    have q9 : a (m + 12) = P (m + 9) := a_closed (m + 9)
    rw [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9]
    linear_combination Prec m
  · have e1 : PowerSeries.mk (fun n => a (n + 3)) = PowerSeries.mk P := by
      congr 1
      funext n
      exact a_closed n
    rw [e1]
    calc PowerSeries.X ^ 3 * PowerSeries.mk P * (1 - PowerSeries.X) ^ 9
        = PowerSeries.X ^ 3 * (PowerSeries.mk P * (1 - PowerSeries.X) ^ 9) := by ring
      _ = PowerSeries.X ^ 3 * ((176 : PowerSeries ℚ) + 1367 * PowerSeries.X +
          2312 * PowerSeries.X ^ 2 + 1072 * PowerSeries.X ^ 3 + 112 * PowerSeries.X ^ 4 +
          PowerSeries.X ^ 5) := by rw [gf]
      _ = PowerSeries.X ^ 3 * (PowerSeries.X ^ 5 + 112 * PowerSeries.X ^ 4 +
          1072 * PowerSeries.X ^ 3 + 2312 * PowerSeries.X ^ 2 + 1367 * PowerSeries.X + 176) := by
        ring
