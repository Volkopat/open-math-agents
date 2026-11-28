import OMAStatements.S_oeis_a006972
import Mathlib

open OMA.S_oeis_a006972

theorem OMA.solution : type_of% @OMA.S_oeis_a006972.main := by
  intro p q r a b c d hp hq hr _ _ _ hpq hpr hqr ha hb hc _ hdiv
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have cpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 hpr
  have cqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
    exact ⟨Nat.Coprime.mul_left cpr cqr, ⟨cpq, hp.squarefree, hq.squarefree⟩, hr.squarefree⟩
  · have := hp.two_le; have := hq.two_le; have := hr.two_le
    have : 1 < p * q := by nlinarith
    nlinarith
  · apply Nat.not_prime_mul
    · have := hp.two_le; have := hq.two_le
      intro h; nlinarith
    · exact hr.one_lt.ne'
  · intro s hs hsd
    have hd : ∀ x y z w : ℕ, x * w ∣ x * y * z * w := by
      intro x y z w; exact ⟨y * z, by ring⟩
    rcases (Nat.Prime.dvd_mul hs).1 hsd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hs).1 h1 with h2 | h2
      · rw [(Nat.prime_dvd_prime_iff_eq hs hp).1 h2, ha]
        exact (hd a b c d).trans hdiv
      · rw [(Nat.prime_dvd_prime_iff_eq hs hq).1 h2, hb]
        exact Nat.dvd_trans ⟨a * c, by ring⟩ hdiv
    · rw [(Nat.prime_dvd_prime_iff_eq hs hr).1 h1, hc]
      exact Nat.dvd_trans ⟨a * b, by ring⟩ hdiv
