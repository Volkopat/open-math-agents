import OMAStatements.S_oeis_a088982
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a088982.main := by
  intro x hx
  have hsm := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have h2 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime (x - 1) := hsm (by omega)
  have hab : Nat.nth Nat.Prime (x - 1) < Nat.nth Nat.Prime x := hsm (by omega)
  have := (Nat.prime_nth_prime (x - 1)).eq_two_or_odd
  have := (Nat.prime_nth_prime x).eq_two_or_odd
  rw [Nat.nth_prime_zero_eq_two] at h2
  simp only [OMA.S_oeis_a088982.prime, Nat.add_sub_cancel]
  refine ⟨Nat.nth Nat.Prime (Nat.nth Nat.Prime (x - 1)), Nat.prime_nth_prime _, hsm ?_, hsm ?_⟩ <;> omega
