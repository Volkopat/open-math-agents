import OMAStatements.S_oeis_a246907

-- Reduction oeis-a246907.R1 of A246907: Numbers n such that sigma(n + sigma(n)) = 3n.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a246907_R1

open ArithmeticFunction

/-- Odd `n`: the equation `σ(n + σ(n)) = 3n` has no odd solution `n ≥ 2`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → Odd n → sigma 1 (n + sigma 1 n) ≠ 3 * n

/-- Even `n` that is not a power of two: no solution of `σ(n + σ(n)) = 3n`. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → Even n → (∀ k : ℕ, n ≠ 2 ^ k) → sigma 1 (n + sigma 1 n) ≠ 3 * n

/-- `1 + 2 + ... + 2^k = 2^(k+1) - 1`. -/
theorem geom_two (k : ℕ) : ∑ i ∈ Finset.range (k + 1), 2 ^ i + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ 2 (k + 1)]
    omega

/-- For `n = 2^k`: `n + σ(n) = 3·2^k - 1`. -/
theorem add_sigma_two_pow (k : ℕ) : 2 ^ k + sigma 1 (2 ^ k) = 3 * 2 ^ k - 1 := by
  have hs := geom_two k
  rw [← sigma_one_apply_prime_pow Nat.prime_two, pow_succ] at hs
  omega

/-- The powers of two are settled here: `σ(3·2^k - 1) = 3·2^k` holds exactly when `3·2^k - 1` is
prime, since `σ(q) = q + 1` characterises primes. That gives the reverse implication and the
power-of-two case of the forward one; odd `n` and even non-powers of two are `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a246907.main := by
  intro h1 h2 n hn
  constructor
  · intro h
    by_cases hpow : ∃ k : ℕ, n = 2 ^ k
    · obtain ⟨k, rfl⟩ := hpow
      refine ⟨k, rfl, ?_⟩
      have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [add_sigma_two_pow, sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at h
      rw [← Nat.sum_properDivisors_eq_one_iff_prime]
      omega
    · push_neg at hpow
      rcases Nat.even_or_odd n with he | ho
      · exact absurd h (h2 n hn he hpow)
      · exact absurd h (h1 n hn ho)
  · rintro ⟨k, rfl, hp⟩
    have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [add_sigma_two_pow, sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
      Nat.sum_properDivisors_eq_one_iff_prime.mpr hp]
    omega

end OMA.R_oeis_a246907_R1
