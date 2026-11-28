import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_uniform_R1

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.uniform.R1.H1.R1 of step SymbolLengthMilnorKTheory.symbol_length_problem.variants.uniform.R1.H1
-- Credit: @hyprspacecoyote
--
-- Split the vanishing of K_(m+1)(C(x_1, ..., x_m))/p for odd p into the surface case m = 2
-- (K_3(C(x, y))/p = 0, known: Milnor's degree filtration over C(x), Tsen-Lang for curves and the
-- Kummer norm relation, see zero_mem_of_lt.R1.H1) and the case m >= 3, which needs vanishing
-- of K_m/p for the non-rational residue fields of C(x_1, ..., x_(m-1))(t).

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_uniform_R1_H1_R1

def H1 : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 →
  0 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin 2) ℂ) p 3

def H2 : Prop := ∀ m p : ℕ, 3 ≤ m → p.Prime → p ≠ 2 →
  0 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p (m + 1)

theorem main : H1 → H2 → OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_uniform_R1.H1 := by
  intro h1 h2 m p hm hp hp2
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · obtain rfl : m = 2 := by omega
    exact h1 p hp hp2
  · exact h2 m p hge hp hp2

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_uniform_R1_H1_R1
