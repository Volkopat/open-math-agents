import FormalConjectures.Other.SymbolLengthMilnorKTheory

-- Reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1 of Matzri's theorem
-- Credit: @hyprspacecoyote
--
-- Matzri: t (p^(m-1) - 1) symbols suffice in K_2(C(x_1..x_m))/p^t. Proved here: t = 0 (the
-- coefficient ring Z/1 is trivial). Split:
--   H1  p = 2, t = 1: every class of K_2/2 is a sum of 2^(m-1) - 1 symbols. Elementary from the
--       u-invariant: Milnor's second Stiefel-Whitney class e<c> = sum_{i<j} {c_i, c_j} is invariant
--       under the 2-dimensional moves <c, d> = <c x^2 + d y^2, ...>, so the anisotropic form
--       (dimension <= 2^m) gives the count. A complete Lean proof is ready as the step proof.
--   H2  every other (p, t) with t >= 1 (Matzri's C_m argument with norm forms of degree p).

namespace OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1

def H1 : Prop := ∀ m : ℕ, 1 ≤ m →
  2 ^ (m - 1) - 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 2

def H2 : Prop := ∀ m : ℕ, 1 ≤ m → ∀ p t : ℕ, p.Prime → 1 ≤ t → ¬ (p = 2 ∧ t = 1) →
  t * (p ^ (m - 1) - 1) ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) (p ^ t) 2

theorem main : H1 → H2 → type_of% @SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two := by
  intro h1 h2 m hm p t hp
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp only [zero_mul, pow_zero]
    rw [MilnorK.zero_mem_symbolLengthBounds_iff, eq_bot_iff]
    intro x _
    rw [AddSubgroup.mem_bot]
    have h1' : (1 : MilnorK (MvRatFunc (Fin m) ℂ) 1) = 0 := by
      exact_mod_cast MilnorK.natCast_eq_zero (F := MvRatFunc (Fin m) ℂ) 1
    calc x = x * 1 := (mul_one x).symm
      _ = 0 := by rw [h1', mul_zero]
  · by_cases h : p = 2 ∧ t = 1
    · obtain ⟨rfl, rfl⟩ := h
      simpa using h1 m hm
    · exact h2 m hm p t hp ht h

end OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1
