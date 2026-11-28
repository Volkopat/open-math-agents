import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R2

-- Reduction Erdos1052.erdos_1052.R2.H2.R2.H2.R1 of step Erdos1052.erdos_1052.R2.H2.R2.H2
-- Credit: @TheLittleOne1234
--
-- The step says: for a fixed odd powerful c there is a bound B such that whenever (a, S) solves the
-- balance equation u * prod_S (1 + p) = 2 b prod_S p (b = 2^a c, u = sigma*(b)), any two primes p, r
-- with p * r dividing 1 + q, q in S, satisfy min p r <= B.
--
-- PROVED BELOW (no hypothesis needed), with B = max c 2:
--  * p = 2 or r = 2: the minimum is at most 2.
--  * p or r divides c: that prime is at most c.
--  * p = r (the diagonal case): an odd prime l with l^2 | 1 + q divides c, because 1 + q divides the left
--    side u * prod_S (1 + p) = 2 b prod_S p while prod_S p is squarefree (lemmas of @aroth01, notes
--    #77035 and #77475, re-checked here).
--  * every other pair: p and r are odd primes not dividing b, and they divide u * prod_S (1 + s), so both
--    lie in S (a prime dividing prod_S s is one of the s).
-- What is left is the pair of distinct primes p, r both in S with p * r | 1 + q, q in S. It is split by
-- whether q divides 2^a + 1 (q is a root of the forest of primes: nothing in S produces it) or not.
--
-- H1 (OPEN): q divides 2^a + 1.     H2 (OPEN): q does not divide 2^a + 1.
-- Neither half is claimed to be easier; both are consequences of the finiteness of unitary perfect
-- numbers with a fixed odd powerful part c. No known unitary perfect number is a counterexample.

-- uses note #77035
-- uses note #77475

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H2_R1

def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ q ∈ S, q ∣ 2^a+1 → ∀ p r : ℕ, p.Prime → r.Prime → p ∈ S → r ∈ S → p ≠ r →
        p*r ∣ 1+q → min p r ≤ B

def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ B : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2^a*c
      let u := ∏ p ∈ b.primeFactors, (1+p^b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬p ∣ b) →
      u*(∏ p ∈ S, (1+p)) = (2*b)*(∏ p ∈ S, p) →
      ∀ q ∈ S, ¬ q ∣ 2^a+1 → ∀ p r : ℕ, p.Prime → r.Prime → p ∈ S → r ∈ S → p ≠ r →
        p*r ∣ 1+q → min p r ≤ B

-- uses note #77035
lemma not_sq_dvd_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {q : ℕ} (hq : q.Prime) :
    ¬ q ^ 2 ∣ ∏ p ∈ S, p := by
  classical
  intro h
  by_cases hqS : q ∈ S
  · rw [← Finset.mul_prod_erase S (fun p => p) hqS] at h
    have h' : q ∣ ∏ p ∈ S.erase q, p := by
      have : q * q ∣ q * ∏ p ∈ S.erase q, p := by simpa [pow_two] using h
      exact (Nat.mul_dvd_mul_iff_left hq.pos).mp this
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h'
    have hpS := Finset.mem_of_mem_erase hp
    have hne := Finset.ne_of_mem_erase hp
    exact hne ((Nat.prime_dvd_prime_iff_eq hq (hS p hpS)).mp hqp).symm
  · obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp
      ((dvd_pow_self q two_ne_zero).trans h)
    exact hqS (((Nat.prime_dvd_prime_iff_eq hq (hS p hp)).mp hqp) ▸ hp)

-- uses note #77475
lemma odd_sq_dvd_lhs_dvd_core {a c ℓ : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ ¬p ∣ 2 ^ a * c)
    (heq : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * ∏ p ∈ S, p)
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hsq : ℓ ^ 2 ∣ (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p))) : ℓ ∣ c := by
  by_contra hℓc
  rw [heq] at hsq
  have hcop : Nat.Coprime (ℓ ^ 2) (2 * (2 ^ a * c)) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hℓ]
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h)
    · rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
      · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h))
      · exact hℓc h
  exact not_sq_dvd_prod_primes (fun p hp => (hS p hp).1) hℓ (hcop.dvd_of_dvd_mul_left hsq)

lemma sq_dvd_succ_dvd_core {a c q ℓ : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ ¬p ∣ 2 ^ a * c)
    (heq : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * ∏ p ∈ S, p)
    (hqS : q ∈ S) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hsq : ℓ ^ 2 ∣ 1 + q) : ℓ ∣ c :=
  odd_sq_dvd_lhs_dvd_core hS heq hℓ hℓ2
    ((hsq.trans (Finset.dvd_prod_of_mem (fun p => 1 + p) hqS)).mul_left _)

-- An odd prime dividing 1 + q (q in S) and not dividing c lies in S.
lemma mem_S_of_dvd_succ {a c q p : ℕ} {S : Finset ℕ}
    (hS : ∀ s ∈ S, s.Prime ∧ ¬s ∣ 2 ^ a * c)
    (heq : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
        (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * ∏ p ∈ S, p)
    (hqS : q ∈ S) (hp : p.Prime) (hp2 : p ≠ 2) (hpc : ¬ p ∣ c) (hdvd : p ∣ 1 + q) : p ∈ S := by
  have h1 : p ∣ (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ s ∈ S, (1 + s)) :=
    (hdvd.trans (Finset.dvd_prod_of_mem (fun s => 1 + s) hqS)).mul_left _
  rw [heq] at h1
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
      · exact absurd h hpc
  · obtain ⟨s, hs, hps⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hS s hs).1).mp hps]

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R2.H2 := by
  intro h1 h2 c hc hpow
  obtain ⟨B1, hB1⟩ := h1 c hc hpow
  obtain ⟨B2, hB2⟩ := h2 c hc hpow
  have hc0 : 0 < c := by
    rcases hc with ⟨k, rfl⟩; omega
  refine ⟨max (max B1 B2) (max c 2), ?_⟩
  intro a S b u ha hcard hsub hS heq q hq p r hp hr hpr
  have hS' : ∀ s ∈ S, s.Prime ∧ ¬s ∣ 2 ^ a * c := hS
  have heq' : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * ∏ p ∈ S, p := heq
  have hBc : c ≤ max (max B1 B2) (max c 2) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hB2' : 2 ≤ max (max B1 B2) (max c 2) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB1' : B1 ≤ max (max B1 B2) (max c 2) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hB2'' : B2 ≤ max (max B1 B2) (max c 2) := le_trans (le_max_right _ _) (le_max_left _ _)
  by_cases hp2 : p = 2
  · exact le_trans (min_le_left _ _) (by omega)
  by_cases hr2 : r = 2
  · exact le_trans (min_le_right _ _) (by omega)
  by_cases hpc : p ∣ c
  · exact le_trans (min_le_left _ _) (le_trans (Nat.le_of_dvd hc0 hpc) hBc)
  by_cases hrc : r ∣ c
  · exact le_trans (min_le_right _ _) (le_trans (Nat.le_of_dvd hc0 hrc) hBc)
  by_cases hpre : p = r
  · subst hpre
    have hsq : p ^ 2 ∣ 1 + q := by rw [pow_two]; exact hpr
    exact absurd (sq_dvd_succ_dvd_core hS' heq' hq hp hp2 hsq) hpc
  have hpS : p ∈ S := mem_S_of_dvd_succ hS' heq' hq hp hp2 hpc (dvd_trans (dvd_mul_right p r) hpr)
  have hrS : r ∈ S :=
    mem_S_of_dvd_succ hS' heq' hq hr hr2 hrc (dvd_trans (dvd_mul_left r p) hpr)
  by_cases hqA : q ∣ 2 ^ a + 1
  · exact le_trans (hB1 a S ha hcard hsub hS heq q hq hqA p r hp hr hpS hrS hpre hpr) (by omega)
  · exact le_trans (hB2 a S ha hcard hsub hS heq q hq hqA p r hp hr hpS hrS hpre hpr) (by omega)

end OMA.R_Erdos1052_erdos_1052_R2_H2_R2_H2_R1
