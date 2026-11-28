import OMAReductions.R_oeis_a284760_R1

-- Reduction oeis-a284760.R1.H3.R1 of step H3 of oeis-a284760.R1 (odd composite n).
-- Credit: @adanthar
-- Each H becomes its own step once this file is accepted.
--
-- For odd n the exponent n - 2 is odd, so pairing i with n - i shows that n divides the sum,
-- and modulo n^2 the sum is n (n - 2) times the sum of i^(n-3) over 1 ≤ i ≤ (n-1)/2. Whether
-- a prime p dividing n can control the sum depends on whether p - 1 divides n - 3:
--   H1: p divides n exactly once and p - 1 ∣ n - 3. Then p^2 does not divide the sum
--       (the inner sum is ≡ -(n/p)/2 mod p, by Fermat). Elementary.
--   H2: p^2 ∣ n and p - 1 ∣ n - 3. Numerically p^(2k-1) exactly divides the sum when p^k ∥ n
--       (checked for n ≤ 6000), as the leading Faulhaber term (n-2)/2 · B_{n-3} · n^2 predicts.
--   H3: no prime factor p of n has p - 1 ∣ n - 3. Then each p^(2k) divides the sum, and the
--       question is a divisibility property of B_{n-3}, as in step H4. Open core.

namespace OMA.R_oeis_a284760_R1_H3_R1

/-- Some prime `p` divides `n` exactly once and `p - 1 ∣ n - 3`. -/
def H1 : Prop :=
  ∀ n p : ℕ, Odd n → p.Prime → p ∣ n → ¬ p ^ 2 ∣ n → (p - 1) ∣ (n - 3) →
    (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) % n ^ 4 ≠ 0

/-- Some prime `p` with `p² ∣ n` has `p - 1 ∣ n - 3`. -/
def H2 : Prop :=
  ∀ n p : ℕ, Odd n → p.Prime → p ^ 2 ∣ n → (p - 1) ∣ (n - 3) →
    (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) % n ^ 4 ≠ 0

/-- No prime factor `p` of the odd composite `n` has `p - 1 ∣ n - 3`. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ n.Prime → (∀ p : ℕ, p.Prime → p ∣ n → ¬ (p - 1) ∣ (n - 3)) →
    (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) % n ^ 4 ≠ 0

theorem main : H1 → H2 → H3 → OMA.R_oeis_a284760_R1.H3 := by
  intro h1 h2 h3
  unfold OMA.R_oeis_a284760_R1.H3
  intro n hn hodd hnp
  by_cases hex : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p - 1) ∣ (n - 3)
  · obtain ⟨p, hp, hpn, hpd⟩ := hex
    by_cases hsq : p ^ 2 ∣ n
    · exact h2 n p hodd hp hsq hpd
    · exact h1 n p hodd hp hpn hsq hpd
  · exact h3 n hn hodd hnp fun p hp hpn hpd => hex ⟨p, hp, hpn, hpd⟩

end OMA.R_oeis_a284760_R1_H3_R1
