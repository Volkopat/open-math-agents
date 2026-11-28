import OMAReductions.R_oeis_a284760_R1

-- Reduction oeis-a284760.R1.H4.R1 of step H4 of oeis-a284760.R1 (n an odd prime p).
-- Credit: @adanthar
-- Each H becomes its own step once this file is accepted.
--
-- Mestrović (arXiv:1211.4570, (2.12)): for primes p ≥ 5, S(p) ≡ (p-2) p²/2 · B_{p-3} (mod p⁴),
-- so p⁴ ∣ S(p) exactly when p² divides the numerator of B_{p-3}. By Kummer, p ∣ B_{p-3}
-- exactly when p² ∣ ∑_{i<p} i^(p-3) (Wolstenholme primes: 16843, 2124679 are the only known).
--   H1: p² ∤ ∑_{i<p} i^(p-3) (non-Wolstenholme primes). Then exactly p² divides S(p).
--       Elementary (pairing to second order plus Fermat); same argument as step
--       oeis-a284760.R1.H3.R1.H3.R1.H1 with n = p.
--   H2: p² ∣ ∑_{i<p} i^(p-3) (Wolstenholme primes). Open core: needs p² ∤ B_{p-3}.
-- The prime p = 3 is checked directly.

namespace OMA.R_oeis_a284760_R1_H4_R1

/-- Non-Wolstenholme primes `p ≥ 5`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 2 ∣ ∑ i ∈ Finset.Ico 1 p, i ^ (p - 3) →
    (∑ i ∈ Finset.Ico 1 p, i ^ (p - 2)) % p ^ 4 ≠ 0

/-- Wolstenholme-type primes `p ≥ 5`. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p ^ 2 ∣ ∑ i ∈ Finset.Ico 1 p, i ^ (p - 3) →
    (∑ i ∈ Finset.Ico 1 p, i ^ (p - 2)) % p ^ 4 ≠ 0

theorem main : H1 → H2 → OMA.R_oeis_a284760_R1.H4 := by
  intro h1 h2
  unfold OMA.R_oeis_a284760_R1.H4
  intro p hp hodd
  rcases (show p = 3 ∨ 5 ≤ p by
    have h2le := hp.two_le
    have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hodd) even_two
    have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
    omega) with rfl | hp5
  · decide
  · by_cases hA : p ^ 2 ∣ ∑ i ∈ Finset.Ico 1 p, i ^ (p - 3)
    · exact h2 p hp hp5 hA
    · exact h1 p hp hp5 hA

end OMA.R_oeis_a284760_R1_H4_R1
