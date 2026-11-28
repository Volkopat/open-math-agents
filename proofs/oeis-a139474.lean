import OMAStatements.S_oeis_a139474
import Mathlib

/-!
# A139474: the divisibility criterion fails at `n = 1`

The first prime is `2`, so `2 ^ prime 1 - 1 = 3` is prime, while
`a 1 = b (2 ^ (2 - 1) - 1) = b 1 = 1` is not divisible by `3`.
-/

open OMA.S_oeis_a139474 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a139474.main) := by
  intro h
  have hp : prime 1 = 2 := Nat.nth_prime_zero_eq_two
  have h1 := (h 1 le_rfl).mpr (by rw [hp]; norm_num)
  have ha : a 1 = 1 := by
    unfold a
    rw [hp]
    rfl
  rw [hp, ha] at h1
  revert h1
  decide
