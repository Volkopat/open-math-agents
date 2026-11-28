import OMAStatements.S_oeis_a239614
import Mathlib

-- Problem: A239614: a(n) = A239611(n) / A079458(n).
-- Credit: @mhismail3 (the owner of the agent is credited as the solver)
-- Split every product over the prime factors into the factor at 2 and the odd part P.

namespace OMA.A239614Proof

open OMA.S_oeis_a239614

/-- The odd part of the divisor-count product. -/
def P (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors.filter (fun p => ¬ p = 2), (n.factorization p + 1)

lemma fac2_zero {n : ℕ} (hn : n ≠ 0) (h : 2 ∉ n.primeFactors) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun hd => h (Nat.mem_primeFactors.2 ⟨Nat.prime_two, hd, hn⟩)

lemma tau_eq {n : ℕ} (hn : n ≠ 0) : tau n = (n.factorization 2 + 1) * P n := by
  rw [tau, Nat.card_divisors hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (· = 2),
    Finset.filter_eq']
  split_ifs with h
  · simp [P]
  · simp [P, fac2_zero hn h]

lemma a_eq (n : ℕ) :
    a n = (if 2 ∈ n.primeFactors then 2 * n.factorization 2 else 1) * P n := by
  rw [a, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (· = 2), Finset.filter_eq']
  have hP : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p = 2),
      (if p = 2 then 2 * n.factorization p else n.factorization p + 1) = P n :=
    Finset.prod_congr rfl fun p hp => if_neg (Finset.mem_filter.1 hp).2
  rw [hP]
  split_ifs with h <;> simp

lemma fac2_double {n : ℕ} (hn : n ≠ 0) : (2 * n).factorization 2 = n.factorization 2 + 1 := by
  rw [Nat.factorization_mul (by norm_num) hn, Finsupp.add_apply, Nat.prime_two.factorization]
  simp [add_comm]

lemma P_double {n : ℕ} (hn : n ≠ 0) : P (2 * n) = P n := by
  unfold P
  have hs : (2 * n).primeFactors.filter (fun p => ¬ p = 2) =
      n.primeFactors.filter (fun p => ¬ p = 2) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hd, -⟩, h2⟩
      exact ⟨⟨hp, ((Nat.coprime_primes hp Nat.prime_two).2 h2).dvd_of_dvd_mul_left hd, hn⟩, h2⟩
    · rintro ⟨⟨hp, hd, -⟩, h2⟩
      exact ⟨⟨hp, Dvd.dvd.mul_left hd 2, by omega⟩, h2⟩
  rw [hs]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 : ¬ p = 2 := (Finset.mem_filter.1 hp).2
  rw [Nat.factorization_mul (by norm_num) hn, Finsupp.add_apply, Nat.prime_two.factorization,
    Finsupp.single_apply, if_neg (Ne.symm h2), zero_add]

lemma two_mem_double {n : ℕ} (hn : n ≠ 0) : 2 ∈ (2 * n).primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.prime_two, dvd_mul_right 2 n, by omega⟩

lemma tau_double {n : ℕ} (hn : n ≠ 0) : tau (2 * n) = (n.factorization 2 + 2) * P n := by
  rw [tau_eq (by omega), fac2_double hn, P_double hn]

end OMA.A239614Proof

open OMA.A239614Proof OMA.S_oeis_a239614 in
theorem OMA.solution : type_of% @OMA.S_oeis_a239614.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hn0 : n ≠ 0 := hn.ne'
    rw [a_eq, tau_double hn0, tau_eq hn0]
    by_cases h : 2 ∈ n.primeFactors
    · have hm : n % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors h)
      rw [if_pos h, hm]
      ring
    · have hm : n % 2 = 1 := by
        have : ¬ 2 ∣ n := fun hd => h (Nat.mem_primeFactors.2 ⟨Nat.prime_two, hd, hn0⟩)
        omega
      rw [if_neg h, hm, fac2_zero hn0 h]
      ring
  · intro n hn
    have hn0 : n ≠ 0 := hn.ne'
    rw [a_eq, if_pos (two_mem_double hn0), fac2_double hn0, P_double hn0, tau_eq hn0]
    ring
  · intro n
    have hn0 : 2 * n + 1 ≠ 0 := by omega
    have h : 2 ∉ (2 * n + 1).primeFactors := fun hm => by
      have := Nat.dvd_of_mem_primeFactors hm
      omega
    rw [a_eq, if_neg h, tau_eq hn0, fac2_zero hn0 h]
