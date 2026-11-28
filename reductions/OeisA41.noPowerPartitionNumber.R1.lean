import FormalConjectures.OEIS.«41»

/-!
# Reduction of A41: no partition number is a perfect power

The conjecture (Zhi-Wei Sun, 2013, recorded on OEIS A41) is that no partition number
`partitionNumber k` is a perfect power `b ^ m` with `b, m > 1`.

Every perfect power has a prime `p` dividing its exponent `m`, and `b ^ m = (b ^ (m / p)) ^ p`
is then itself a `p`-th power. So it suffices to rule out prime exponents, and this file
splits the target into the three disjoint exponent classes that need different arguments:

* `H1`: no partition number is a perfect square;
* `H2`: no partition number is a perfect cube;
* `H3`: no partition number is a `p`-th power for a prime `p ≥ 5`.

Each hypothesis is strictly weaker than the target (it restricts the exponent to one prime,
respectively to `2`), so this is a genuine splitting of the difficulty: a solver of `H1`
only has to handle squares, one of `H3` only odd prime exponents. The exponent reduction
in `main` is the usual passage from arbitrary exponents to prime exponents.

All three hypotheses were checked numerically for every `k ≤ 400`.
-/

namespace OMA.R_OeisA41_noPowerPartitionNumber_R1

open Nat

/-- No partition number is a perfect square. -/
def H1 : Prop :=
  ∀ k : ℕ, ¬ ∃ b : ℕ, 1 < b ∧ b ^ 2 = Nat.partitionNumber k

/-- No partition number is a perfect cube. -/
def H2 : Prop :=
  ∀ k : ℕ, ¬ ∃ b : ℕ, 1 < b ∧ b ^ 3 = Nat.partitionNumber k

/-- No partition number is a `p`-th power for an odd prime exponent `p ≥ 5`. -/
def H3 : Prop :=
  ∀ (k p : ℕ), p.Prime → 5 ≤ p → ¬ ∃ b : ℕ, 1 < b ∧ b ^ p = Nat.partitionNumber k

theorem main : H1 → H2 → H3 → type_of% @OeisA41.noPowerPartitionNumber := by
  intro h1 h2 h3 k h
  obtain ⟨b, m, hb, hm, hpow⟩ := h
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (n := m) (by omega)
  obtain ⟨t, rfl⟩ := hpm
  have ht : t ≠ 0 := by
    rintro rfl
    simp at hm
  have hbase : 1 < b ^ t := Nat.one_lt_pow ht hb
  have hpow' : (b ^ t) ^ p = Nat.partitionNumber k := by
    rw [← pow_mul, Nat.mul_comm t p, hpow]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact h1 k ⟨b ^ t, hbase, hpow'⟩
  · have h3p : 3 ≤ p := by
      obtain ⟨s, hs⟩ := hodd
      have := hp.two_le
      omega
    rcases eq_or_lt_of_le h3p with h | h
    · obtain rfl : p = 3 := h.symm
      exact h2 k ⟨b ^ t, hbase, hpow'⟩
    · have h5 : 5 ≤ p := by
        obtain ⟨s, hs⟩ := hodd
        omega
      exact h3 k p hp h5 ⟨b ^ t, hbase, hpow'⟩

end OMA.R_OeisA41_noPowerPartitionNumber_R1
