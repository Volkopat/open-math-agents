import OMAStatements.S_oeis_a027481

-- Problem: A027481: Second subdiagonal of triangle A027477, constructed from the Stirling numbers of the first kind.
-- Upstream: formal-conjectures statements/oeis-a027481.lean:0 (declaration OMA.S_oeis_a027481.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: A(i, j) = 0 for j > i, so in T(n, n-2) = n!^2 Sum_k A(n,k) A(k,n-2) only the three
-- terms with n-2 <= k <= n remain. With |s(i,i)| = 1, |s(i+1,i)| = C(i+1,2) and
-- |s(i+2,i)| = (i+2)(i+1)i(3i+5)/24 (induction on the Stirling recurrence) this gives
-- a(m+3) = P(m) for an explicit polynomial P of degree 6. Then (1 - x)^7 annihilates P (a ring
-- identity), which gives the recurrence, and the g.f. follows by comparing coefficients.

namespace P1A027481

open OMA.S_oeis_a027481

theorem Azero (i k : ℕ) (h : i < k) : A i k = 0 := by
  show (Nat.stirlingFirst i k : ℚ) / (i.factorial : ℚ) = 0
  rw [Nat.stirlingFirst_eq_zero_of_lt h, Nat.cast_zero, zero_div]

theorem sum3 (m : ℕ) (g : ℕ → ℚ) (hg : ∀ l, l ≤ m → g l = 0) :
    ∑ l ∈ Finset.Icc 1 (m + 3), g l = g (m + 1) + g (m + 2) + g (m + 3) := by
  have hz : ∑ l ∈ Finset.Icc 1 m, g l = 0 :=
    Finset.sum_eq_zero fun l hl ↦ hg l (Finset.mem_Icc.mp hl).2
  rw [Finset.sum_Icc_succ_top (Nat.succ_pos (m + 2)),
    Finset.sum_Icc_succ_top (Nat.succ_pos (m + 1)),
    Finset.sum_Icc_succ_top (Nat.succ_pos m), hz, zero_add]

theorem s1 (n : ℕ) : (Nat.stirlingFirst (n + 1) n : ℚ) = ((n : ℚ) + 1) * (n : ℚ) / 2 := by
  rw [Nat.stirlingFirst_succ_self_left, Nat.cast_choose_two, Nat.cast_add_one]
  ring

theorem s2 (n : ℕ) : (Nat.stirlingFirst (n + 2) n : ℚ) =
    ((n : ℚ) + 2) * ((n : ℚ) + 1) * (n : ℚ) * (3 * (n : ℚ) + 5) / 24 := by
  induction n with
  | zero => norm_num [Nat.stirlingFirst]
  | succ k ih =>
    rw [Nat.stirlingFirst_succ_succ]
    push_cast
    rw [s1, ih]
    push_cast
    ring

/-- a(m+3) as an explicit polynomial in m. -/
def P (m : ℕ) : ℚ :=
  ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (3 * (m : ℚ) + 8) / 24 *
      (1 + ((m : ℚ) + 3) * ((m : ℚ) + 2)) +
    ((m : ℚ) + 3) * ((m : ℚ) + 2) / 2 * (((m : ℚ) + 2) * ((m : ℚ) + 1) / 2) * ((m : ℚ) + 3)

theorem a_closed (m : ℕ) : a (m + 3) = P m := by
  have hz : ∀ l, l ≤ m → A (m + 3) l * A l (m + 1) = 0 := by
    intro l hl
    rw [Azero l (m + 1) (by omega), mul_zero]
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ m
  have f2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ (m + 1)
  have f3 : ((m + 3).factorial : ℚ) = ((m : ℚ) + 3) * ((m + 2).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ (m + 2)
  have c11 : (Nat.stirlingFirst (m + 1) (m + 1) : ℚ) = 1 := by
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
  show ((m + 3).factorial : ℚ) ^ 2 * ∑ k ∈ Finset.Icc 1 (m + 3),
    A (m + 3) k * A k (m + 3 - 2) = P m
  rw [show m + 3 - 2 = m + 1 by omega, sum3 m (fun k => A (m + 3) k * A k (m + 1)) hz]
  unfold A
  rw [c11, c33, c21, c32, c31, f3, f2, f1]
  unfold P
  field_simp
  ring

theorem Prec (k : ℕ) : P (k + 7) - 7 * P (k + 6) + 21 * P (k + 5) - 35 * P (k + 4) +
    35 * P (k + 3) - 21 * P (k + 2) + 7 * P (k + 1) - P k = 0 := by
  unfold P
  push_cast
  ring

theorem Pq (n : ℕ) (hn : 7 ≤ n) : P n - 7 * P (n - 1) + 21 * P (n - 2) - 35 * P (n - 3) +
    35 * P (n - 4) - 21 * P (n - 5) + 7 * P (n - 6) - P (n - 7) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa [Nat.add_sub_assoc] using Prec k

theorem gf : PowerSeries.mk P * (1 - PowerSeries.X) ^ 7 =
    (23 : PowerSeries ℚ) + 54 * PowerSeries.X + 13 * PowerSeries.X ^ 2 := by
  have e : PowerSeries.mk P * (1 - PowerSeries.X) ^ 7 =
      PowerSeries.mk P
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 * (PowerSeries.mk P * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21 * (PowerSeries.mk P * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 35 * (PowerSeries.mk P * PowerSeries.X ^ 3)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 35 * (PowerSeries.mk P * PowerSeries.X ^ 4)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21 * (PowerSeries.mk P * PowerSeries.X ^ 5)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 * (PowerSeries.mk P * PowerSeries.X ^ 6)
        - PowerSeries.mk P * PowerSeries.X ^ 7 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 35]
    ring
  have e2 : (23 : PowerSeries ℚ) + 54 * PowerSeries.X + 13 * PowerSeries.X ^ 2 =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 23
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54 * PowerSeries.X ^ 1
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 13 * PowerSeries.X ^ 2 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 23,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 13]
    ring
  rw [e, e2]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
    · norm_num [P]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [Pq n hn]

end P1A027481

open OMA.S_oeis_a027481 P1A027481 in
theorem OMA.solution : type_of% @OMA.S_oeis_a027481.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
      show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
      show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
      show m + 10 - 7 = m + 3 by omega]
    have q0 : a (m + 3) = P m := a_closed m
    have q1 : a (m + 4) = P (m + 1) := a_closed (m + 1)
    have q2 : a (m + 5) = P (m + 2) := a_closed (m + 2)
    have q3 : a (m + 6) = P (m + 3) := a_closed (m + 3)
    have q4 : a (m + 7) = P (m + 4) := a_closed (m + 4)
    have q5 : a (m + 8) = P (m + 5) := a_closed (m + 5)
    have q6 : a (m + 9) = P (m + 6) := a_closed (m + 6)
    have q7 : a (m + 10) = P (m + 7) := a_closed (m + 7)
    rw [q0, q1, q2, q3, q4, q5, q6, q7]
    linear_combination Prec m
  · have e1 : PowerSeries.mk (fun n => a (n + 3)) = PowerSeries.mk P := by
      congr 1
      funext n
      exact a_closed n
    rw [e1]
    calc PowerSeries.X ^ 3 * PowerSeries.mk P * (PowerSeries.X - 1) ^ 7
        = -(PowerSeries.X ^ 3 * (PowerSeries.mk P * (1 - PowerSeries.X) ^ 7)) := by ring
      _ = -(PowerSeries.X ^ 3 * ((23 : PowerSeries ℚ) + 54 * PowerSeries.X +
          13 * PowerSeries.X ^ 2)) := by rw [gf]
      _ = PowerSeries.X ^ 3 * (-13 * PowerSeries.X ^ 2 - 54 * PowerSeries.X - 23) := by
        ring
