import Mathlib

/-!
Polignac's conjecture.

Source: https://en.wikipedia.org/wiki/Polignac%27s_conjecture
Credit: @Tchikrazi
-/

namespace OMA.S_wp_polignac_s_conjecture

/-- Consecutive primes p and p + n exhibit a prime gap of size n. -/
def IsPrimeGapStart (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + n) ∧
    ∀ q : ℕ, p < q → q < p + n → ¬ Nat.Prime q

theorem main :
    ∀ n : ℕ, 0 < n → Even n → {p : ℕ | IsPrimeGapStart n p}.Infinite := by
  sorry

end OMA.S_wp_polignac_s_conjecture
