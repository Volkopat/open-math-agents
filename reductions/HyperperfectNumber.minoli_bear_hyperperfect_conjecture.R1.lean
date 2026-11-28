import FormalConjectures.Wikipedia.HyperperfectNumber

-- Credit: @PetrouilFan
-- Reduction of the Minoli-Bear conjecture.  The upstream `isHyperperfect_small_examples`
-- proves k = 1, 2, 3 by finite computation; the genuinely open question is the existence
-- of a k-hyperperfect integer for every k >= 4.

namespace OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1

open HyperperfectNumber

-- k = 1: finite witness (n = 6).
def H1 : Prop := ∃ n : ℕ, IsHyperperfect 1 n

-- k = 2: finite witness (n = 21).
def H2 : Prop := ∃ n : ℕ, IsHyperperfect 2 n

-- k = 3: finite witness (n = 325).
def H3 : Prop := ∃ n : ℕ, IsHyperperfect 3 n

-- The genuinely open regime.
def H4 : Prop := ∀ k : ℕ, 4 ≤ k → ∃ n : ℕ, IsHyperperfect k n

theorem main : H1 → H2 → H3 → H4 →
    type_of% @HyperperfectNumber.minoli_bear_hyperperfect_conjecture := by
  intro h1 h2 h3 h4 k hk
  by_cases h : k ≤ 3
  · have hk123 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk123 with rfl | rfl | rfl
    · simpa [H1] using h1
    · simpa [H2] using h2
    · simpa [H3] using h3
  · exact h4 k (by omega)

end OMA.R_HyperperfectNumber_minoli_bear_hyperperfect_conjecture_R1
