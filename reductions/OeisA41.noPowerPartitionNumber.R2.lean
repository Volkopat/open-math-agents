import FormalConjectures.OEIS.«41»

/-!
# Sieve for power exponents of partition numbers

If the least prime factor of a partition number has multiplicity one, that
already excludes all perfect powers. Otherwise only prime exponents dividing
that multiplicity need to be tested, and it suffices to test the cofactor.
This includes the case of a pure prime power, for which the cofactor is one.

Credit: @Pixelstorm44
-/
namespace OMA.R_OeisA41_noPowerPartitionNumber_R2

open Nat

/-- When the least prime occurs to even order, the cofactor lies above
the square of its integer square root. -/
def H1 : Prop := ∀ k : ℕ, let n := partitionNumber k
  1 < n → 2 ∣ n.factorization n.minFac → (ordCompl[n.minFac] n).sqrt ^ 2 < (ordCompl[n.minFac] n)

/-- For each odd prime dividing the least factor's multiplicity, the cofactor
lies strictly between two consecutive powers of that exponent. -/
def H2 : Prop := ∀ k : ℕ, let n := partitionNumber k
  1 < n → ∀ q : ℕ, q.Prime → 2 < q → q ∣ n.factorization n.minFac →
    ∃ t : ℕ, t ^ q < (ordCompl[n.minFac] n) ∧ (ordCompl[n.minFac] n) < (t + 1) ^ q

private theorem strip_pow (x q p : ℕ) :
    ordCompl[p] (x ^ q) = (ordCompl[p] x) ^ q := by
  rw [Nat.factorization_pow]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Nat.mul_comm q, pow_mul, Nat.div_pow (Nat.ordProj_dvd x p)]

theorem main : H1 → H2 → type_of% @OeisA41.noPowerPartitionNumber := by
  intro squares oddPowers k
  rintro ⟨b, m, hb, hm, heq⟩
  let n := partitionNumber k
  let q := m.minFac
  have hprime : q.Prime := Nat.minFac_prime (by omega)
  obtain ⟨d, hd⟩ := Nat.minFac_dvd m
  let x := b ^ d
  have hn : n = x ^ q := by
    calc n = b ^ m := heq.symm
         _ = (b ^ d) ^ q := by rw [← pow_mul, hd, Nat.mul_comm d]
  have hn1 : 1 < n := by
    change 1 < partitionNumber k
    rw [← heq]
    exact one_lt_pow' hb (by omega)
  have hdiv : q ∣ n.factorization n.minFac := by
    generalize n.minFac = p
    rw [hn, Nat.factorization_pow]
    exact dvd_mul_right q _
  have hstrip : (ordCompl[n.minFac] n) = (ordCompl[n.minFac] x) ^ q := by
    generalize n.minFac = p
    rw [hn, strip_pow]
  by_cases htwo : q = 2
  · have h := squares k hn1 (htwo ▸ hdiv)
    change (ordCompl[n.minFac] n).sqrt ^ 2 < (ordCompl[n.minFac] n) at h
    rw [hstrip, htwo, Nat.sqrt_eq'] at h
    exact (lt_irrefl _ h)
  · obtain ⟨t, hlo, hhi⟩ := oddPowers k hn1 q hprime (by have := hprime.two_le; omega) hdiv
    rw [hstrip] at hlo hhi
    by_cases h : ordCompl[n.minFac] x ≤ t
    · exact (Nat.not_lt_of_ge (Nat.pow_le_pow_left h q)) hlo
    · exact (Nat.not_lt_of_ge (Nat.pow_le_pow_left (by omega) q)) hhi

end OMA.R_OeisA41_noPowerPartitionNumber_R2
