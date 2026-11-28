import OMAStatements.S_oeis_a165433

-- Problem: A165433: A transform of the double factorial numbers A001147.
-- Upstream: formal-conjectures statements/oeis-a165433.lean:0 (declaration OMA.S_oeis_a165433.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with d(k) = (2k-1)!! and b(n) = Sum k C(n-k,k) d(k), Pascal gives a(n+2) = a(n+1) + a(n) + 2 b(n), and Pascal plus absorption give 2 b(p+1) - b(p) = (p+1)(a(p+1) - a(p)) term by term; the claim is a combination of these.

open OMA.S_oeis_a165433 in
theorem OMA.solution : type_of% @OMA.S_oeis_a165433.main := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℚ, ∀ k : ℕ,
      d k = ((2 * k).factorial : ℚ) / ((k.factorial : ℚ) * 2 ^ k) := ⟨_, fun _ => rfl⟩
  have hds : ∀ k : ℕ, d (k + 1) = (2 * (k : ℚ) + 1) * d k := by
    intro k
    rw [hd, hd, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simp only [Nat.factorial_succ]
    push_cast
    field
  have hext : ∀ n M : ℕ, n / 2 + 1 ≤ M →
      a n = ∑ k ∈ Finset.range M, ((n - k).choose k : ℚ) * d k := by
    intro n M hM
    have e : a n = ∑ k ∈ Finset.range (n / 2 + 1), ((n - k).choose k : ℚ) * d k :=
      Finset.sum_congr rfl fun k _ => by rw [hd, mul_div_assoc]
    rw [e]
    apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
    intro k _ hk
    simp at hk
    simp [Nat.choose_eq_zero_of_lt (by omega : n - k < k)]
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n : ℕ,
      b n = ∑ k ∈ Finset.range (n + 1), (k : ℚ) * (((n - k).choose k : ℚ) * d k) :=
    ⟨_, fun _ => rfl⟩
  have L1 : ∀ n : ℕ, a (n + 2) = a (n + 1) + a n + 2 * b n := by
    intro n
    rw [hext (n + 2) (n + 1 + 1) (by omega), hext (n + 1) (n + 1 + 1) (by omega),
      hext n (n + 1) (by omega), hb, Finset.sum_range_succ' _ (n + 1),
      Finset.sum_range_succ' _ (n + 1)]
    have key : ∀ k ∈ Finset.range (n + 1),
        ((n + 2 - (k + 1)).choose (k + 1) : ℚ) * d (k + 1)
          = ((n + 1 - (k + 1)).choose (k + 1) : ℚ) * d (k + 1) + ((n - k).choose k : ℚ) * d k
            + 2 * ((k : ℚ) * (((n - k).choose k : ℚ) * d k)) := by
      intro k hk
      simp at hk
      rw [show n + 2 - (k + 1) = n - k + 1 by omega, show n + 1 - (k + 1) = n - k by omega,
        Nat.choose_succ_succ' (n - k) k, hds k]
      push_cast
      ring
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Nat.choose_zero_right, Nat.cast_one]
    ring
  have L2 : ∀ p : ℕ, 2 * b (p + 1) - b p = ((p : ℚ) + 1) * (a (p + 1) - a p) := by
    intro p
    have hbp : b p
        = ∑ k ∈ Finset.range (p + 1 + 1), (k : ℚ) * (((p - k).choose k : ℚ) * d k) := by
      rw [hb, Finset.sum_range_succ _ (p + 1),
        Nat.choose_eq_zero_of_lt (by omega : p - (p + 1) < p + 1)]
      simp
    rw [hbp, hb (p + 1), hext (p + 1) (p + 1 + 1) (by omega), hext p (p + 1 + 1) (by omega),
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp at hk
    rcases k with _ | j
    · simp
    rcases Nat.lt_or_ge j p with hj | hj
    · obtain ⟨N, rfl⟩ : ∃ N, p = N + j + 1 := ⟨p - j - 1, by omega⟩
      rw [show N + j + 1 + 1 - (j + 1) = N + 1 by omega, show N + j + 1 - (j + 1) = N by omega]
      have z1 : ((N + 1).choose (j + 1) : ℚ) = (N.choose j : ℚ) + (N.choose (j + 1) : ℚ) := by
        exact_mod_cast Nat.choose_succ_succ' N j
      have z2 : ((N : ℚ) + 1) * (N.choose j : ℚ) = ((N + 1).choose (j + 1) : ℚ) * ((j : ℚ) + 1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq N j
      push_cast
      linear_combination (-((N : ℚ) + 1) * d (j + 1)) * z1 - d (j + 1) * z2
    · simp [show p + 1 - (j + 1) = 0 by omega, show p - (j + 1) = 0 by omega]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have E1 := L1 (m + 1)
  have E0 := L1 m
  have E2 := L2 m
  rw [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at E1
  push_cast
  linear_combination 2 * E1 - E0 + 2 * E2
