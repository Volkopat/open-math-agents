import OMAStatements.S_mo_301581
import Mathlib

namespace OMA.R_mo_301581_R1

def H1 : Prop :=
  ∀ n : ℕ, (∃ s : ℕ, 2 ≤ s ∧ s ≤ 4 ∧ s ≤ n ∧ (∀ q ∈ (n - s).primeFactors, q % 4 = 3 → Even (padicValNat q (n - s)))) → ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + Nat.centralBinom c + Nat.centralBinom d

def H2 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ (∃ s : ℕ, 2 ≤ s ∧ s ≤ 4 ∧ s ≤ n ∧ (∀ q ∈ (n - s).primeFactors, q % 4 = 3 → Even (padicValNat q (n - s)))) → ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + Nat.centralBinom c + Nat.centralBinom d

theorem main : H1 → H2 → type_of% @OMA.S_mo_301581.main := by
  intro slice rest n hn
  by_cases h : ∃ s : ℕ, 2 ≤ s ∧ s ≤ 4 ∧ s ≤ n ∧ (∀ q ∈ (n - s).primeFactors, q % 4 = 3 → Even (padicValNat q (n - s)))
  · exact slice n h
  · exact rest n hn h

end OMA.R_mo_301581_R1
