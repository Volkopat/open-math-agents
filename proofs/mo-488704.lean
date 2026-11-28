import OMAStatements.S_mo_488704
import Mathlib

open OMA.S_mo_488704

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_488704.main) := by
  intro h
  apply h.2.2.2.2.2 6 8241414 (le_refl 6)
  refine ⟨72990721, by norm_num, ?_⟩
  have hp : Nat.Prime 72990721 := by norm_num
  rw [Nat.totient_prime hp]
  have e : 6 * 72990721 + 8241414 = 2 ^ 2 * (3 * (5 * (7 * (11 * (13 * (17 * (19 * 23))))))) := by
    norm_num
  rw [e, Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
    Nat.totient_prime_pow Nat.prime_two (by norm_num),
    Nat.totient_prime (by norm_num : Nat.Prime 3), Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 7), Nat.totient_prime (by norm_num : Nat.Prime 11),
    Nat.totient_prime (by norm_num : Nat.Prime 13), Nat.totient_prime (by norm_num : Nat.Prime 17),
    Nat.totient_prime (by norm_num : Nat.Prime 19), Nat.totient_prime (by norm_num : Nat.Prime 23)]
  norm_num
