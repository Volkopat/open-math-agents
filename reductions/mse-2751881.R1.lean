import OMAStatements.S_mse_2751881
import Mathlib

namespace OMA.R_mse_2751881_R1

def H1 : Prop :=
  ∀ n : ℤ, (∃ (h : ℤ) (m : ℕ), n = 4*h^3 + 54*h*m ∧
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)) → ∃ a b c d : ℤ, n = a^3 + b^3 + c^3 + d^3

def H2 : Prop :=
  ∀ n : ℤ, (n % 9 = 4 ∨ n % 9 = 5) → ¬ (∃ (h : ℤ) (m : ℕ), n = 4*h^3 + 54*h*m ∧
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)) → ∃ a b c d : ℤ, n = a^3 + b^3 + c^3 + d^3

theorem main : H1 → H2 → type_of% @OMA.S_mse_2751881.main := by
  intro slice rest n hn
  by_cases h : ∃ (h : ℤ) (m : ℕ), n = 4*h^3 + 54*h*m ∧
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)
  · exact slice n h
  · exact rest n hn h

end OMA.R_mse_2751881_R1
