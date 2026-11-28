import OMAStatements.S_oeis_a215461
import Mathlib

namespace OMA.A215461Proof

open OMA.S_oeis_a215461

theorem main_proof : ∀ n : ℕ, 5 < n → ∃ p q : ℕ, Odd p ∧ Odd q ∧ p.Prime ∧ ¬ q.Prime ∧ p + q = 2 * n := by
  intro n hn
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h
  · refine ⟨3, 2 * n - 3, by decide, ⟨n - 2, by omega⟩, Nat.prime_three, ?_, by omega⟩
    intro hp
    have : 3 ∣ 2 * n - 3 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this
    omega
  · refine ⟨5, 2 * n - 5, by decide, ⟨n - 3, by omega⟩, by norm_num, ?_, by omega⟩
    intro hp
    have : 3 ∣ 2 * n - 5 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this
    omega
  · refine ⟨7, 2 * n - 7, by decide, ⟨n - 4, by omega⟩, by norm_num, ?_, by omega⟩
    intro hp
    have : 3 ∣ 2 * n - 7 := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 this
    omega

end OMA.A215461Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a215461.main := OMA.A215461Proof.main_proof

