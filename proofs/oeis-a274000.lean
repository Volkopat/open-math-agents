import OMAStatements.S_oeis_a274000

-- Problem: A274000: Primes p of the form k^2 + 1 that divide 4^k - 1.
-- Upstream: formal-conjectures statements/oeis-a274000.lean:0 (declaration OMA.S_oeis_a274000.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (4^k)^n - 1 = (4^n)^k - 1 is divisible by 4^n - 1; conversely take k = 1.

open OMA.S_oeis_a274000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274000.main := by
  intro p
  unfold IsTerm
  constructor
  · rintro ⟨hp, k, hk, hdvd⟩
    refine ⟨hp, k, hk, fun j => ?_⟩
    have hswap : (4 ^ j) ^ k = (4 ^ k) ^ j := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hswap]
    exact Nat.dvd_trans hdvd (Nat.sub_one_dvd_pow_sub_one (4 ^ k) j)
  · rintro ⟨hp, n, hn, h⟩
    refine ⟨hp, n, hn, ?_⟩
    have h1 := h 1
    rw [pow_one] at h1
    exact h1
