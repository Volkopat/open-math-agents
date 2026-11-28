import OMAReductions.R_oeis_a237721_R1

namespace OMA.R_oeis_a237721_R1_H2_R1

def H1 : Prop := ∀ R : ℕ, 131072 ≤ R → R < 4705446956544 →
  ∃ b p q : ℕ, 9*b^3 ≤ R ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ R ∧ R ≤ p+2*b^2

def H2 : Prop := ∀ R : ℕ, 4705446956544 ≤ R → R < 36808731643392 →
  ∃ b p q : ℕ, 9*b^3 ≤ R ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ R ∧ R ≤ p+2*b^2

def H3 : Prop := ∀ R : ℕ, 36808731643392 ≤ R → R < 123299611872768 →
  ∃ b p q : ℕ, 9*b^3 ≤ R ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ R ∧ R ≤ p+2*b^2

def H4 : Prop := ∀ R : ℕ, 123299611872768 ≤ R → R < 281474976972800 →
  ∃ b p q : ℕ, 9*b^3 ≤ R ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ R ∧ R ≤ p+2*b^2

theorem main : H1 → H2 → H3 → H4 → OMA.R_oeis_a237721_R1.H2 := by
  intro h1 h2 h3 h4 R lo hi
  by_cases c1 : R < 4705446956544
  · exact h1 R (by omega) c1
  by_cases c2 : R < 36808731643392
  · exact h2 R (by omega) c2
  by_cases c3 : R < 123299611872768
  · exact h3 R (by omega) c3
  exact h4 R (by omega) (by omega)

end OMA.R_oeis_a237721_R1_H2_R1
