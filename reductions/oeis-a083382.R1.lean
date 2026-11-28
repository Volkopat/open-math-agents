import OMAStatements.S_oeis_a083382
import Mathlib

namespace OMA.R_oeis_a083382_R1

def H1 : Prop := ∀ n : ℕ, 1 < n → ∀ row : ℕ, row ≤ 1 →
  ∃ p : ℕ, p.Prime ∧ row * n < p ∧ p ≤ (row + 1) * n

def H2 : Prop := ∀ n : ℕ, 1 < n → ∀ row : ℕ, 2 ≤ row → row < n →
  ∃ p : ℕ, p.Prime ∧ row * n < p ∧ p ≤ (row + 1) * n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a083382.main := by
  intro h₁ h₂ n hn row hr
  by_cases h : row ≤ 1
  · exact h₁ n hn row h
  · exact h₂ n hn row (by omega) hr

end OMA.R_oeis_a083382_R1
