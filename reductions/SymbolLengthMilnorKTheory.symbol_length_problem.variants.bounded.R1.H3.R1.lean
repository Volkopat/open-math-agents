import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.bounded.R1.H3.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.bounded.R1.H3
-- Credit: @hyprspacecoyote
--
-- Mod-two finiteness in degrees 3 <= n <= m splits into the top degree n = m, where every class
-- of K_m(C(x_1, ..., x_m))/2 is a single symbol (Lang's count u <= 2^m and the linkage of
-- m-fold Pfister forms, proved in K-theory), and the open range 3 <= n < m.

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1_H3_R1

def H1 : Prop := ∀ m : ℕ, 3 ≤ m →
  1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 m

def H2 : Prop := ∀ m n : ℕ, 3 ≤ n → n < m →
  (MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 n).Nonempty

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1.H3 := by
  intro h1 h2 m n hn hnm
  rcases Nat.lt_or_ge n m with hlt | hge
  · exact h2 m n hn hlt
  · obtain rfl : n = m := by omega
    exact ⟨1, h1 n hn⟩

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1_H3_R1
