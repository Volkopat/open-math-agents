import OMAStatements.S_oeis_a173614
import Mathlib

open ArithmeticFunction Nat in
theorem OMA.solution : type_of% @OMA.S_oeis_a173614.main := by
  intro n _
  rw [radical_eq_prod_primeFactors, carmichael_finsetProd (f := fun p => p) fun p hp q hq h =>
    (coprime_primes (prime_of_mem_primeFactors hp) (prime_of_mem_primeFactors hq)).2 h]
  refine Finset.lcm_congr rfl fun p hp => ?_
  have hp := prime_of_mem_primeFactors hp
  have : carmichael p = p.totient := by
    rcases eq_or_ne p 2 with rfl | h
    · exact carmichael_two_pow_of_le_two_eq_totient (n := 1) one_le_two
    · simpa using carmichael_pow_of_prime_ne_two 1 hp h
  simp [this, totient_prime hp]
