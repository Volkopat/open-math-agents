import OMAStatements.S_oeis_a070226
import Mathlib

/-
A070226: if the number of divisors tau(k) divides the squarefree kernel rad(k), they are equal.

Let S be the set of primes dividing k and e_p >= 1 the exponents, so tau(k) is the product
over S of (e_p + 1) and rad(k) the product over S of p. Count prime factors with multiplicity
(Omega): Omega(rad k) = |S|, while Omega(tau k) is a sum of |S| terms, each at least 1 because
e_p + 1 >= 2. If rad k = tau k * c, additivity of Omega gives Omega(c) = 0, hence c = 1.
-/

namespace OMA.P070226
open ArithmeticFunction

lemma omega_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ) (hg : ∀ i ∈ s, g i ≠ 0) :
    cardFactors (∏ i ∈ s, g i) = ∑ i ∈ s, cardFactors (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      cardFactors_mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

lemma omega_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ cardFactors n := by
  rw [cardFactors_apply]
  rcases h : n.primeFactorsList with _ | ⟨x, l⟩
  · rcases (Nat.primeFactorsList_eq_nil n).1 h with h | h <;> omega
  · simp

lemma main' : ∀ k : ℕ, 1 ≤ k → k.divisors.card ∣ ∏ p ∈ k.primeFactors, p →
    ∏ p ∈ k.primeFactors, p = k.divisors.card := by
  intro k hk hdvd
  rw [Nat.card_divisors (by omega)] at hdvd ⊢
  obtain ⟨c, hc⟩ := hdvd
  have hP0 : ∏ p ∈ k.primeFactors, p ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hT0 : ∏ p ∈ k.primeFactors, (k.factorization p + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p _ => Nat.succ_ne_zero _
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hP0 (by simpa using hc)
  have h1 : cardFactors (∏ p ∈ k.primeFactors, p) = k.primeFactors.card := by
    rw [omega_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero,
      Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun p hp =>
      cardFactors_apply_prime (Nat.prime_of_mem_primeFactors hp)
  have h2 : k.primeFactors.card ≤
      cardFactors (∏ p ∈ k.primeFactors, (k.factorization p + 1)) := by
    rw [omega_prod _ _ fun p _ => Nat.succ_ne_zero _, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun p hp => omega_pos ?_
    have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have h3 := congrArg cardFactors hc
  rw [cardFactors_mul hT0 hc0, h1] at h3
  have hc1 : c = 1 := by
    by_contra hne
    have := omega_pos (n := c) (by omega)
    omega
  rw [hc, hc1, mul_one]

end OMA.P070226

theorem OMA.solution : type_of% @OMA.S_oeis_a070226.main := by
  intro k hk h
  exact OMA.P070226.main' k hk h
