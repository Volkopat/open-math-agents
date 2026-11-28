import OMAStatements.S_oeis_a160326
import Mathlib

namespace OMA.R_oeis_a160326_R1

def H1 : Prop := ∀ n : ℕ, (∀ p ∈ n.primeFactors, p % 4 = 3 → Even (padicValNat p n)) →
  ∃ x y : ℕ, n = x ^ 2 + y ^ 2

def H2 : Prop := ∀ n : ℕ, (∃ p ∈ n.primeFactors, p % 4 = 3 ∧ ¬ Even (padicValNat p n)) →
  ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z * (3 * z - 1) / 2 = n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a160326.main := by
  intro h₁ h₂ n
  by_cases h : ∀ p ∈ n.primeFactors, p % 4 = 3 → Even (padicValNat p n)
  · obtain ⟨x, y, hxy⟩ := h₁ n h
    exact ⟨x, y, 0, by simpa using hxy.symm⟩
  · push_neg at h
    exact h₂ n h

end OMA.R_oeis_a160326_R1
