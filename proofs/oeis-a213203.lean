import OMAStatements.S_oeis_a213203

-- Problem: A213203: The sum of the first n! integers, with every n-th integer taken as negative.
-- Upstream: formal-conjectures statements/oeis-a213203.lean:0 (declaration OMA.S_oeis_a213203.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: 2 a(k+1) = (k+1) k! ((k-1) k! - 1) (sum of 1..N minus twice the multiples of n); the recurrence is then a polynomial identity in m and m!.

open OMA.S_oeis_a213203 in
theorem OMA.solution : type_of% @OMA.S_oeis_a213203.main := by
  have hT : ∀ n N : ℕ, 2 * (∑ k ∈ Finset.Icc 1 N, if n ∣ k then -(k : ℤ) else (k : ℤ))
      = (N : ℤ) * ((N : ℤ) + 1) - 2 * (n : ℤ) * ((N / n : ℕ) : ℤ) * (((N / n : ℕ) : ℤ) + 1) := by
    intro n N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), mul_add (2 : ℤ), ih]
      obtain ⟨d, hd⟩ : ∃ d, N / n = d := ⟨_, rfl⟩
      by_cases h : n ∣ N + 1
      · have hq : (d + 1) * n = N + 1 := by
          rw [← hd, ← Nat.succ_div_of_dvd h]
          exact Nat.div_mul_cancel h
        have hq' : ((d : ℤ) + 1) * (n : ℤ) = (N : ℤ) + 1 := by
          exact_mod_cast hq
        rw [if_pos h, Nat.succ_div_of_dvd h, hd]
        push_cast
        linear_combination 4 * hq'
      · rw [if_neg h, Nat.succ_div_of_not_dvd h, hd]
        push_cast
        ring
  have ha : ∀ k : ℕ, 2 * a (k + 1)
      = ((k : ℤ) + 1) * (k.factorial : ℤ) * (((k : ℤ) - 1) * (k.factorial : ℤ) - 1) := by
    intro k
    have h := hT (k + 1) (k + 1).factorial
    rw [Nat.factorial_succ k, Nat.mul_div_cancel_left _ (by omega : 0 < k + 1)] at h
    unfold a
    rw [Nat.factorial_succ k, h]
    push_cast
    ring
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have H5 := ha (m + 4)
  have H4 := ha (m + 3)
  have H3 := ha (m + 2)
  have H2 := ha (m + 1)
  have H1 := ha m
  have f4 := Nat.factorial_succ (m + 3)
  have f3 := Nat.factorial_succ (m + 2)
  have f2 := Nat.factorial_succ (m + 1)
  have f1 := Nat.factorial_succ m
  rw [show m + 4 + 1 = m + 5 by omega] at H5
  rw [show m + 3 + 1 = m + 4 by omega] at H4 f4
  rw [show m + 2 + 1 = m + 3 by omega] at H3 f3
  rw [show m + 1 + 1 = m + 2 by omega] at H2 f2
  rw [f4, f3, f2, f1] at H5
  rw [f3, f2, f1] at H4
  rw [f2, f1] at H3
  rw [f1] at H2
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  push_cast at H5 H4 H3 H2 ⊢
  linear_combination H5 + (-(((m : ℤ) + 5) ^ 2) - ((m : ℤ) + 5) - 11) * H4
    + (((m : ℤ) + 5) ^ 3 + 7 * ((m : ℤ) + 5) ^ 2 - 13 * ((m : ℤ) + 5) + 39) * H3
    - 2 * ((m : ℤ) + 3) * (4 * ((m : ℤ) + 5) ^ 2 - 2 * ((m : ℤ) + 5) - 15) * H2
    + 20 * ((m : ℤ) + 3) * ((m : ℤ) + 2) * ((m : ℤ) + 1) * H1
