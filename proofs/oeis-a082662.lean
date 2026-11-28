import OMAStatements.S_oeis_a082662

-- Problem: A082662 core. s^2 < 2 (2^m s) iff s < 2^(m+1) (s > 0), and the divisors of 2^m sum to
-- 2^(m+1) - 1, so the right side is s <= 2^(m+1) - 1.

theorem OMA.solution : type_of% @OMA.S_oeis_a082662.main := by
  intro m s hs hs0
  have hg : ∀ e : ℕ, ∑ k ∈ Finset.range (e + 1), 2 ^ k + 1 = 2 ^ (e + 1) := by
    intro e
    induction e with
    | zero => simp
    | succ e ih => rw [Finset.sum_range_succ, add_right_comm, ih]; ring
  have hsum : ∑ d ∈ (2 ^ m).divisors, d = ∑ k ∈ Finset.range (m + 1), 2 ^ k := by
    rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  rw [hsum]
  have h1 := hg m
  rw [pow_succ] at h1
  constructor
  · intro h
    have : s < 2 ^ m * 2 := by rw [sq] at h; nlinarith
    omega
  · intro h
    have : s < 2 ^ m * 2 := by omega
    rw [sq]; nlinarith
