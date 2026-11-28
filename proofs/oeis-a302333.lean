import OMAStatements.S_oeis_a302333

-- Problem: A302333: Wagstaff primes related to The New Mersenne Conjecture that are the indices of perfect numbers in a list of centered 9-gonal numbers.
-- Upstream: formal-conjectures statements/oeis-a302333.lean:0 (declaration OMA.S_oeis_a302333.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: write q = k + 1 and M = 2^(k+1) - 1. From 3p = 2^(k+1) + 1 we get 3p - 2 = M and
-- 3p - 1 = 2 * 2^k, so (3p-2)(3p-1)/2 = 2^k * M. Euclid: sigma(2^k * M) = (2^(k+1) - 1)(M + 1)
-- = M * 2^(k+1) = 2 * (2^k * M) by multiplicativity, since M is an odd prime.

namespace H11A302333

theorem geom2 (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

theorem sig_prime (p : ℕ) (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one] at h
  omega

theorem perfect_euclid (k M : ℕ) (hM : M.Prime) (hMk : M + 1 = 2 * 2 ^ k) :
    Nat.Perfect (2 ^ k * M) := by
  have hk : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hpos : 0 < 2 ^ k * M := Nat.mul_pos hk hM.pos
  have hodd : Odd M := ⟨2 ^ k - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hS : ∑ i ∈ Finset.range (k + 1), 2 ^ i = M := by
    have h := geom2 (k + 1)
    rw [pow_succ] at h
    omega
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← ArithmeticFunction.sigma_one_apply,
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, sig_prime M hM, hMk, hS]
  ring

end H11A302333

open OMA.S_oeis_a302333 H11A302333 in
theorem OMA.solution : type_of% @OMA.S_oeis_a302333.main := by
  intro p q _hp h3 hq
  cases q with
  | zero => exact absurd hq (by norm_num)
  | succ k =>
    obtain ⟨M, hMdef⟩ : ∃ M, M = 2 ^ (k + 1) - 1 := ⟨_, rfl⟩
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    have hk : 0 < 2 ^ k := pow_pos (by norm_num) k
    have hM1 : M + 1 = 2 * 2 ^ k := by omega
    rw [← hMdef] at hq
    have e1 : 3 * p - 2 = M := by omega
    have e2 : 3 * p - 1 = 2 * 2 ^ k := by omega
    have hval : (3 * p - 2) * (3 * p - 1) / 2 = 2 ^ k * M := by
      rw [e1, e2, show M * (2 * 2 ^ k) = 2 * (2 ^ k * M) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    refine ⟨?_, ?_⟩
    · unfold c9
      rw [Nat.mul_comm (3 * p - 1) (3 * p - 2)]
    · rw [hval]
      exact perfect_euclid k M hq hM1
