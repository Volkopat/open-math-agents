import Mathlib

/-!
# Divisibility of products of odd prime powers.

Source: https://mathoverflow.net/questions/81816
The exponent in the source is nonnegative.
-/

namespace OMA.S_mo_81816

open Finset

def valid {m : ℕ} (p a : Fin m → ℕ) : Prop :=
  Monotone p ∧ (∀ i, Nat.Prime (p i) ∧ Odd (p i)) ∧
    (∏ i, (p i ^ a i - 1)) ∣ (∏ i, p i ^ a i) - 1

theorem main : ∀ m : ℕ, 2 ≤ m → ∃ p a : Fin m → ℕ, valid p a := by
  sorry

end OMA.S_mo_81816
