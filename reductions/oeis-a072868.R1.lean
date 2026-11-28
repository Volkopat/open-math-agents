import OMAStatements.S_oeis_a072868

-- Reduction oeis-a072868.R1 of A072868: Numbers k such that sigma(sigma(k) - k) = k.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a072868_R1

open ArithmeticFunction

/-- Odd `k`: no odd `k ≥ 1` satisfies `σ(σ(k) - k) = k`. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 ≤ k → Odd k → sigma 1 (sigma 1 k - k) ≠ k

/-- Even `k` that is not a power of two: no solution of `σ(σ(k) - k) = k`. -/
def H2 : Prop :=
  ∀ k : ℕ, 1 ≤ k → Even k → (∀ q : ℕ, k ≠ 2 ^ q) → sigma 1 (sigma 1 k - k) ≠ k

/-- `1 + 2 + ... + 2^q = 2^(q+1) - 1`. -/
theorem geom_two (q : ℕ) : ∑ i ∈ Finset.range (q + 1), 2 ^ i + 1 = 2 ^ (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (q + 1)]
    omega

/-- For `k = 2^q`: `σ(k) - k = 2^q - 1`. -/
theorem sigma_sub_two_pow (q : ℕ) : sigma 1 (2 ^ q) - 2 ^ q = 2 ^ q - 1 := by
  have hs := geom_two q
  rw [← sigma_one_apply_prime_pow Nat.prime_two, pow_succ] at hs
  omega

/-- The powers of two are settled here: `σ(2^q - 1) = 2^q` holds exactly when `2^q - 1` is prime,
since `σ(m) = m + 1` characterises primes. That gives the reverse implication and the
power-of-two case of the forward one; odd `k` and even non-powers of two are `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a072868.main := by
  intro h1 h2 k hk
  constructor
  · intro h
    by_cases hpow : ∃ q : ℕ, k = 2 ^ q
    · obtain ⟨q, rfl⟩ := hpow
      refine ⟨q, ?_, rfl⟩
      have hq : 1 ≤ 2 ^ q := Nat.one_le_two_pow
      rw [sigma_sub_two_pow, sigma_one_apply,
        Nat.sum_divisors_eq_sum_properDivisors_add_self] at h
      rw [← Nat.sum_properDivisors_eq_one_iff_prime]
      omega
    · push_neg at hpow
      rcases Nat.even_or_odd k with he | ho
      · exact absurd h (h2 k hk he hpow)
      · exact absurd h (h1 k hk ho)
  · rintro ⟨q, hp, rfl⟩
    have hq : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    rw [sigma_sub_two_pow, sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
      Nat.sum_properDivisors_eq_one_iff_prime.mpr hp]
    omega

end OMA.R_oeis_a072868_R1
