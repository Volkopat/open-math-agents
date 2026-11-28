import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.bounded.R1.H1.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.bounded.R1.H1
-- Credit: @hyprspacecoyote
--
-- Split the first vanishing degree K_(m+1)(C(x_1, ..., x_m))/p = 0 into the known cases
-- (m <= 2 for every p: explicit computation for C(x), Milnor's degree filtration with Tsen-Lang
-- and the Kummer norm relation for C(x, y); p = 2 for every m: Lang's count and Pfister forms)
-- and the open core: an odd prime p and m >= 3.

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1_H1_R1

def H1 : Prop := ∀ m p : ℕ, 0 < m → p.Prime → (m ≤ 2 ∨ p = 2) →
  MilnorK.grade (MvRatFunc (Fin m) ℂ) p (m + 1) = ⊥

def H2 : Prop := ∀ m p : ℕ, 3 ≤ m → p.Prime → p ≠ 2 →
  MilnorK.grade (MvRatFunc (Fin m) ℂ) p (m + 1) = ⊥

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1.H1 := by
  intro h1 h2 m p hm hp
  by_cases hc : m ≤ 2 ∨ p = 2
  · exact h1 m p hm hp hc
  · push_neg at hc
    exact h2 m p (by omega) hp hc.2

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1_H1_R1
