import OMAReductions.R_oeis_a064708_R1

-- Reduction of the residue class into exponent classification and three cases.
namespace OMA.R_oeis_a064708_R1_H1_R1

def H1 : Prop := ∀ a b : ℕ, 13 ≤ a → 13 ≤ b → a % 12 = 1 → b % 12 = 1 →
  (∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2) →
  Nat.gcd a b = 1 ∨ (a = b ∧ a.Prime)

def H2 : Prop := ∀ a : ℕ, 13 ≤ a → a % 12 = 1 → a.Prime →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ a - 5 + i).primeFactors.card = 2

def H3 : Prop := ∀ a b : ℕ, 13 ≤ a → 13 ≤ b → a % 12 = 1 → b % 12 = 1 →
  Nat.gcd a b = 1 → ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2

def H4 : Prop := ∀ a b : ℕ, a % 12 = 1 → b % 12 = 1 → a = 1 ∨ b = 1 →
  ¬ ∀ i < 9, (2 ^ a * 3 ^ b - 5 + i).primeFactors.card = 2

theorem main : H1 → H2 → H3 → H4 → OMA.R_oeis_a064708_R1.H1 := by
  intro classify diagonal coprime boundary a b ha hb hw
  by_cases he : a = 1 ∨ b = 1
  · exact boundary a b ha hb he hw
  · have ha13 : 13 ≤ a := by omega
    have hb13 : 13 ≤ b := by omega
    rcases classify a b ha13 hb13 ha hb hw with hg | ⟨hab, hp⟩
    · exact coprime a b ha13 hb13 ha hb hg hw
    · subst b
      exact diagonal a ha13 ha hp hw

end OMA.R_oeis_a064708_R1_H1_R1
