import OMAStatements.S_oeis_a289683

-- Problem: A289683: Mixing moments of the busy period of mean steady-state 1/2 in an M/M/1 waiting process.
-- Upstream: formal-conjectures statements/oeis-a289683.lean:0 (declaration OMA.S_oeis_a289683.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with u(N,k) = binomial(N+k,2k) catalan(k) one has b(N+1) = c(N) = Sum_k u(N,k)/2^k, and
-- the terms satisfy (N+1)u(N,k) + (N-2)u(N-2,k) = (2N-1)(u(N-1,k) + 2u(N-1,k-1)) (a linear combination
-- of three binomial ratio identities and the Catalan recurrence). Summing gives
-- (M+3)c(M+2) - 2(2M+3)c(M+1) + M c(M) = 0, which is the conjecture after multiplying by (m+2)(m+1)!.

namespace P1A289683

open OMA.S_oeis_a289683

/-- u N k = binomial(N + k, 2k) * catalan k; it is 0 for k > N. -/
def u (N k : ℕ) : ℚ := ((N + k).choose (2 * k) : ℚ) * (catalan k : ℚ)

/-- c N = Sum_{k=0..N} u N k / 2^k. -/
def c (N : ℕ) : ℚ := ∑ k ∈ Finset.range (N + 1), u N k * (1 / 2) ^ k

theorem cat_q (k : ℕ) :
    ((k : ℚ) + 2) * (catalan (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) * (catalan k : ℚ) := by
  have e1 : ((k : ℚ) + 1 + 1) * (catalan (k + 1) : ℚ) = ((k + 1).centralBinom : ℚ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (k + 1)
  have e2 : ((k : ℚ) + 1) * (catalan k : ℚ) = (k.centralBinom : ℚ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom k
  have e3 : ((k : ℚ) + 1) * ((k + 1).centralBinom : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (k.centralBinom : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  apply mul_left_cancel₀ (show ((k : ℚ) + 1) ≠ 0 by positivity)
  linear_combination ((k : ℚ) + 1) * e1 + e3 - 2 * (2 * (k : ℚ) + 1) * e2

theorem u_zero (N : ℕ) : u N 0 = 1 := by
  simp [u, catalan_zero]

theorem u_eq_zero (N k : ℕ) (h : N < k) : u N k = 0 := by
  unfold u
  rw [Nat.choose_eq_zero_of_lt (show N + k < 2 * k by omega)]
  simp

theorem u_diag (N : ℕ) : u N N = (catalan N : ℚ) := by
  unfold u
  rw [show N + N = 2 * N by omega, Nat.choose_self]
  simp

/-- The pointwise identity behind the recurrence. -/
theorem pw (M j : ℕ) :
    ((M : ℚ) + 3) * u (M + 2) (j + 1) + (M : ℚ) * u M (j + 1)
      = (2 * (M : ℚ) + 3) * (u (M + 1) (j + 1) + 2 * u (M + 1) j) := by
  rcases (show j ≤ M ∨ j = M + 1 ∨ M + 2 ≤ j by omega) with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, M = j + d := ⟨M - j, by omega⟩
    have h1 : ((2 * j + d + 2).choose (2 * j + 2) : ℚ) * (2 * (j : ℚ) + d + 3)
        = ((2 * j + d + 3).choose (2 * j + 2) : ℚ) * ((d : ℚ) + 1) := by
      have h0 := Nat.choose_mul_succ_eq (2 * j + d + 2) (2 * j + 2)
      rw [show 2 * j + d + 2 + 1 = 2 * j + d + 3 by omega,
        show 2 * j + d + 3 - (2 * j + 2) = d + 1 by omega] at h0
      exact_mod_cast h0
    have h2 : ((2 * j + d + 1).choose (2 * j + 2) : ℚ) * (2 * (j : ℚ) + d + 2)
        = ((2 * j + d + 2).choose (2 * j + 2) : ℚ) * (d : ℚ) := by
      have h0 := Nat.choose_mul_succ_eq (2 * j + d + 1) (2 * j + 2)
      rw [show 2 * j + d + 1 + 1 = 2 * j + d + 2 by omega,
        show 2 * j + d + 2 - (2 * j + 2) = d by omega] at h0
      exact_mod_cast h0
    have h3 : ((2 * j + d + 2).choose (2 * j + 2) : ℚ) * (2 * (j : ℚ) + 2)
        = ((2 * j + d + 2).choose (2 * j + 1) : ℚ) * ((d : ℚ) + 1) := by
      have h0 := Nat.choose_succ_right_eq (2 * j + d + 2) (2 * j + 1)
      rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega,
        show 2 * j + d + 2 - (2 * j + 1) = d + 1 by omega] at h0
      exact_mod_cast h0
    have h4 : (2 * (j : ℚ) + d + 2) * ((2 * j + d + 1).choose (2 * j) : ℚ)
        = ((2 * j + d + 2).choose (2 * j + 1) : ℚ) * (2 * (j : ℚ) + 1) := by
      have h0 := Nat.add_one_mul_choose_eq (2 * j + d + 1) (2 * j)
      rw [show 2 * j + d + 1 + 1 = 2 * j + d + 2 by omega] at h0
      exact_mod_cast h0
    have hc := cat_q j
    unfold u
    rw [show j + d + 2 + (j + 1) = 2 * j + d + 3 by omega,
      show j + d + (j + 1) = 2 * j + d + 1 by omega,
      show j + d + 1 + (j + 1) = 2 * j + d + 2 by omega,
      show j + d + 1 + j = 2 * j + d + 1 by omega,
      show 2 * (j + 1) = 2 * j + 2 by omega]
    push_cast
    apply mul_left_cancel₀ (show ((d : ℚ) + 1) * (2 * (j : ℚ) + d + 2) ≠ 0 by positivity)
    linear_combination (-((j : ℚ) + d + 3) * (2 * (j : ℚ) + d + 2) * (catalan (j + 1) : ℚ)) * h1
      + ((j : ℚ) + d) * ((d : ℚ) + 1) * (catalan (j + 1) : ℚ) * h2
      + 2 * (2 * ((j : ℚ) + d) + 3) * (2 * (j : ℚ) + 1) * (catalan j : ℚ) * h3
      - 2 * (2 * ((j : ℚ) + d) + 3) * ((d : ℚ) + 1) * (catalan j : ℚ) * h4
      + 2 * (2 * ((j : ℚ) + d) + 3) * ((j : ℚ) + 1)
        * ((2 * j + d + 2).choose (2 * j + 2) : ℚ) * hc
  · subst h
    rw [u_eq_zero M (M + 1 + 1) (by omega), u_eq_zero (M + 1) (M + 1 + 1) (by omega),
      show M + 1 + 1 = M + 2 by omega, u_diag, u_diag]
    have hc := cat_q (M + 1)
    rw [show M + 1 + 1 = M + 2 by omega] at hc
    push_cast at hc
    linear_combination hc
  · rw [u_eq_zero (M + 2) (j + 1) (by omega), u_eq_zero M (j + 1) (by omega),
      u_eq_zero (M + 1) (j + 1) (by omega), u_eq_zero (M + 1) j (by omega)]
    ring

theorem sum_ext (N L : ℕ) (h : N < L) :
    ∑ k ∈ Finset.range (L + 1), u N k * (1 / 2) ^ k
      = ∑ k ∈ Finset.range L, u N k * (1 / 2) ^ k := by
  rw [Finset.sum_range_succ, u_eq_zero N L h, zero_mul, add_zero]

theorem crec (M : ℕ) :
    ((M : ℚ) + 3) * c (M + 2) - 2 * (2 * (M : ℚ) + 3) * c (M + 1) + (M : ℚ) * c M = 0 := by
  have e2 : c (M + 2) = ∑ j ∈ Finset.range (M + 2), u (M + 2) (j + 1) * (1 / 2) ^ (j + 1)
      + u (M + 2) 0 * (1 / 2) ^ 0 :=
    Finset.sum_range_succ' (fun k => u (M + 2) k * (1 / 2) ^ k) (M + 2)
  have e1b : c (M + 1) = ∑ j ∈ Finset.range (M + 2), u (M + 1) j * (1 / 2) ^ j := rfl
  have e1a : c (M + 1) = ∑ j ∈ Finset.range (M + 2), u (M + 1) (j + 1) * (1 / 2) ^ (j + 1)
      + u (M + 1) 0 * (1 / 2) ^ 0 := by
    rw [e1b, ← sum_ext (M + 1) (M + 2) (by omega)]
    exact Finset.sum_range_succ' (fun k => u (M + 1) k * (1 / 2) ^ k) (M + 2)
  have e0 : c M = ∑ j ∈ Finset.range (M + 2), u M (j + 1) * (1 / 2) ^ (j + 1)
      + u M 0 * (1 / 2) ^ 0 := by
    have h1 : c M = ∑ k ∈ Finset.range (M + 1), u M k * (1 / 2) ^ k := rfl
    rw [h1, ← sum_ext M (M + 1) (by omega), show M + 1 + 1 = M + 2 by omega,
      ← sum_ext M (M + 2) (by omega)]
    exact Finset.sum_range_succ' (fun k => u M k * (1 / 2) ^ k) (M + 2)
  have hL : ∑ j ∈ Finset.range (M + 2),
      (((M : ℚ) + 3) * (u (M + 2) (j + 1) * (1 / 2) ^ (j + 1))
        + (M : ℚ) * (u M (j + 1) * (1 / 2) ^ (j + 1)))
      = ∑ j ∈ Finset.range (M + 2),
      ((2 * (M : ℚ) + 3) * (u (M + 1) (j + 1) * (1 / 2) ^ (j + 1))
        + (2 * (M : ℚ) + 3) * (u (M + 1) j * (1 / 2) ^ j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    linear_combination (1 / 2 : ℚ) ^ j * (1 / 2) * pw M j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum] at hL
  have z2 := u_zero (M + 2)
  have z1 := u_zero (M + 1)
  have z0 := u_zero M
  linear_combination ((M : ℚ) + 3) * e2 + (M : ℚ) * e0 - (2 * (M : ℚ) + 3) * e1a
    - (2 * (M : ℚ) + 3) * e1b + hL + ((M : ℚ) + 3) * z2 + (M : ℚ) * z0
    - (2 * (M : ℚ) + 3) * z1

theorem bc (N : ℕ) : b (N + 1) = c N := by
  unfold b
  rw [if_neg (show ¬ (N + 1 = 0) by omega)]
  unfold c
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  unfold u
  rw [show N + 1 - 1 + k = N + k by omega, show N + 1 - 1 - k = N - k by omega,
    Nat.choose_symm_of_eq_add (show N + k = (N - k) + 2 * k by omega)]

theorem b0 : b 0 = 1 := by
  simp [b]

theorem c0 : c 0 = 1 := by
  simp [c, u_zero]

theorem c1 : c 1 = 3 / 2 := by
  norm_num [c, Finset.sum_range_succ, u_zero, u_diag, catalan_one]

theorem a0 : a 0 = 1 := by
  show (Nat.factorial 0 : ℚ) * b 0 = 1
  rw [b0]
  simp

theorem a1 : a 1 = 1 := by
  show (Nat.factorial 1 : ℚ) * b (0 + 1) = 1
  rw [bc 0, c0]
  simp

theorem a2 : a 2 = 3 := by
  show (Nat.factorial 2 : ℚ) * b (1 + 1) = 3
  rw [bc 1, c1, Nat.factorial_two]
  norm_num

end P1A289683

open OMA.S_oeis_a289683 P1A289683 in
theorem OMA.solution : type_of% @OMA.S_oeis_a289683.main := by
  intro n hn
  rcases (show n = 2 ∨ 3 ≤ n by omega) with h | h
  · subst h
    rw [show (2 - 1 : ℕ) = 1 from rfl, show (2 - 2 : ℕ) = 0 from rfl, a2, a1, a0]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    have h3 : b (m + 3) = c (m + 2) := bc (m + 2)
    have h2 : b (m + 2) = c (m + 1) := bc (m + 1)
    have h1 : b (m + 1) = c m := bc m
    have g3 : (m + 3).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ (m + 2)
    have g2 : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
    have q3 := congrArg (Nat.cast : ℕ → ℚ) g3
    have q2 := congrArg (Nat.cast : ℕ → ℚ) g2
    push_cast at q3 q2
    have cr := crec m
    unfold a
    rw [h3, h2, h1]
    push_cast
    linear_combination c (m + 2) * q3
      + (((m : ℚ) + 3) * c (m + 2) - 2 * (2 * (m : ℚ) + 3) * c (m + 1)) * q2
      + ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) * cr
