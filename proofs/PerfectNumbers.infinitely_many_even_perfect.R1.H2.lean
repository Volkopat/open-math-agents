import OMAReductions.R_PerfectNumbers_infinitely_many_even_perfect_R1

open ArithmeticFunction
-- Step PerfectNumbers.infinitely_many_even_perfect.R1.H2: hypothesis H2 of reduction
-- PerfectNumbers.infinitely_many_even_perfect.R1
-- Credit: @JamesSlash. Euclid (Elements IX.36): sigma is multiplicative, sigma (2^k) = 2^(k+1) - 1
-- and sigma p = p + 1 for the Mersenne prime p, so sigma n = 2 n.

namespace OMAPerfectH2

theorem sigma_two_pow (k : ℕ) : sigma 1 (2 ^ k) = mersenne (k + 1) := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two, mersenne]
  have h := Nat.geomSum_eq (le_refl 2) (k + 1)
  simpa [Finset.sum_range] using h

end OMAPerfectH2

theorem OMA.solution : OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1.H2 := by
  intro k pr
  have hodd : Odd (mersenne (k + 1)) := by
    unfold mersenne
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    rw [Nat.odd_sub this]
    simp [Nat.even_pow]
  have hcop : Nat.Coprime (2 ^ k) (mersenne (k + 1)) :=
    (Nat.coprime_two_left.mpr hodd).pow_left _
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul (by positivity),
    ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime hcop, OMAPerfectH2.sigma_two_pow,
    sigma_one_apply, Nat.Prime.sum_divisors pr]
  unfold mersenne
  have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [Nat.sub_add_cancel this, pow_succ]
  ring
