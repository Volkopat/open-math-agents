import OMAStatements.S_oeis_a090523

-- Original Lean proof: @ivillar.
-- Bertrand supplies a prime p with 2p ≤ n! < 4p, so the prime quotient is 2 or 3.

open OMA.S_oeis_a090523 in
theorem OMA.solution : type_of% @OMA.S_oeis_a090523.main := by
  intro n hn
  let N := n.factorial
  have hN : 6 ≤ N := Nat.factorial_le (show 3 ≤ n by omega)
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 4) (by omega)
  have hlo : 2 ≤ N / p := (Nat.le_div_iff_mul_le hp.pos).2 (by omega)
  have hhi : N / p < 4 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
  have hprime : (N / p).Prime := by
    obtain h | h : N / p = 2 ∨ N / p = 3 := by omega
    all_goals rw [h] <;> decide
  have h : a n ∈ {q : ℕ | q.Prime ∧ (N / q).Prime} := Nat.sInf_mem ⟨p, hp, hprime⟩
  exact h.1.ne_zero
