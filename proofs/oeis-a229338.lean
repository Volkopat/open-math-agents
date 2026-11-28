import OMAStatements.S_oeis_a229338
import Mathlib

-- Problem: A229338, the product over all subsets S of the divisors of n of the product of S
--   equals n^(tau(n) * 2^(tau(n) - 2)).
-- Credit: @canneyi
-- Each divisor lies in half of the subsets, so the square of the double product is
-- (product of the divisors)^(2^tau(n)). The square of the product of the divisors is n^tau(n).

open OMA.S_oeis_a229338

namespace OMAa229338

open Finset

theorem powerset_sq (s : Finset ℕ) :
    (∏ S ∈ s.powerset, ∏ d ∈ S, d) ^ 2 = (∏ d ∈ s, d) ^ 2 ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : ∏ t ∈ s.powerset, ∏ d ∈ insert a t, d =
        a ^ 2 ^ s.card * ∏ t ∈ s.powerset, ∏ d ∈ t, d := by
      rw [← card_powerset, ← prod_const, ← prod_mul_distrib]
      refine prod_congr rfl fun t ht => ?_
      exact prod_insert fun hat => ha (mem_powerset.mp ht hat)
    have key : (a * ∏ d ∈ s, d) ^ 2 ^ (s.card + 1) =
        (a ^ 2 ^ s.card) ^ 2 * ((∏ d ∈ s, d) ^ 2 ^ s.card) ^ 2 := by
      rw [pow_succ 2 s.card, pow_mul, mul_pow]
      ring
    rw [prod_powerset_insert ha, h1, prod_insert ha, card_insert_of_notMem ha, key, ← ih]
    ring

theorem divisors_prod_sq (n : ℕ) : (∏ d ∈ n.divisors, d) ^ 2 = n ^ n.divisors.card := by
  have h1 : ∏ d ∈ n.divisors, n / d = ∏ d ∈ n.divisors, d := Nat.prod_div_divisors n fun d => d
  have h2 : ∏ d ∈ n.divisors, d * (n / d) = n ^ n.divisors.card := by
    rw [← prod_const]
    exact prod_congr rfl fun d hd => Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  rw [sq, ← h2, prod_mul_distrib, h1]

theorem a_one : a 1 = 1 := by
  have h := powerset_sq (Nat.divisors 1)
  rw [Nat.divisors_one, prod_singleton, one_pow] at h
  have h' : a 1 ^ 2 = 1 ^ 2 := by
    unfold a
    rw [Nat.divisors_one, h, one_pow]
  exact (Nat.pow_left_inj two_ne_zero).mp h'

theorem a_ge_two (n : ℕ) (hn : 2 ≤ n) :
    a n = n ^ (n.divisors.card * 2 ^ (n.divisors.card - 2)) := by
  have hc : 1 < n.divisors.card :=
    one_lt_card_iff.mpr ⟨1, n, Nat.one_mem_divisors.mpr (by omega),
      Nat.mem_divisors_self n (by omega), by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, n.divisors.card = t + 2 := ⟨n.divisors.card - 2, by omega⟩
  have hA : a n ^ 2 = (∏ d ∈ n.divisors, d) ^ 2 ^ n.divisors.card := powerset_sq n.divisors
  have hB := divisors_prod_sq n
  have e1 : n.divisors.card - 2 = t := by omega
  have e2 : (2 : ℕ) ^ n.divisors.card = 2 * 2 ^ (t + 1) := by
    rw [ht]
    ring
  have hsq : a n ^ 2 = (n ^ (n.divisors.card * 2 ^ (n.divisors.card - 2))) ^ 2 := by
    rw [hA, e2, pow_mul (∏ d ∈ n.divisors, d) 2 (2 ^ (t + 1)), hB, e1]
    ring
  exact (Nat.pow_left_inj two_ne_zero).mp hsq

end OMAa229338

theorem OMA.solution : type_of% @OMA.S_oeis_a229338.main := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    rw [OMAa229338.a_one, one_pow]
  · exact OMAa229338.a_ge_two n h
