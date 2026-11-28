import OMAStatements.S_oeis_a350142
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a350142.main := by
  simp [OMA.S_oeis_a350142.tau, Nat.divisors_prime_pow Nat.prime_two]
