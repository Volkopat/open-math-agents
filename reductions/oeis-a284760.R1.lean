import OMAStatements.S_oeis_a284760

-- Reduction oeis-a284760.R1 of A284760: a(n) = Sum_{i=1..n-1}(i^(n-2)) mod n^4.
-- Credit: @adanthar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The split is by the shape of `n`:
--   H1: `n ≡ 2 (mod 4)`. Easy: the sum is odd while `n^4` is even.
--   H2: `4 ∣ n`. A 2-adic argument: the even terms vanish to high 2-adic order, the odd ones
--       can be controlled.
--   H3: `n` odd and composite. The sum is divisible by `n`. If a prime `p` divides `n` exactly
--       once and `p - 1 ∣ n - 3`, then `p²` does not divide the sum; if `p^k ∥ n` with `k ≥ 2`
--       and `p - 1 ∣ n - 3`, numerically `p^(2k-1) ∥` the sum. When no prime factor satisfies
--       `p - 1 ∣ n - 3`, the valuations depend on `B_{n-3}`, as in H4.
--   H4: `n` an odd prime `p`. For `p ≥ 5` the sum is divisible by `p²` but, generically, not by
--       `p³`; its `p`-adic valuation is governed by the Bernoulli number `B_{p-3}` (compare
--       Wolstenholme primes). This is the open core.

namespace OMA.R_oeis_a284760_R1

/-- The case `n ≡ 2 (mod 4)`. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 4 = 2 → (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) % n ^ 4 ≠ 0

/-- The case `4 ∣ n`. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → 4 ∣ n → (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) % n ^ 4 ≠ 0

/-- The case `n` odd and composite. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ n.Prime → (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) % n ^ 4 ≠ 0

/-- The case `n` an odd prime. -/
def H4 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → (∑ i ∈ Finset.Ico 1 p, i ^ (p - 2)) % p ^ 4 ≠ 0

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a284760.main := by
  intro h1 h2 h3 h4 n hn
  rcases Nat.even_or_odd n with he | ho
  · have hcases : n % 4 = 2 ∨ 4 ∣ n := by
      obtain ⟨k, rfl⟩ := he
      omega
    rcases hcases with h | h
    · exact h1 n h
    · exact h2 n (by omega) h
  · by_cases hp : n.Prime
    · exact h4 n hp ho
    · exact h3 n hn ho hp

end OMA.R_oeis_a284760_R1
