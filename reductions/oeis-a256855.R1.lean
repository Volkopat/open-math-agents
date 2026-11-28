import OMAStatements.S_oeis_a256855

-- Reduction oeis-a256855.R1 of A256855: splits Zhi-Wei Sun's three representation
-- conjectures into three steps. Credit: @kernl

namespace OMA.R_oeis_a256855_R1

/-- First representation: n = x(3x-1)/2 + y(3y+1)/2 + z(3z+1). -/
def H1 : Prop := ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
  (n : ℤ) = (x : ℤ) * (3 * x - 1) / 2 + (y : ℤ) * (3 * y + 1) / 2 + z * (3 * z + 1)

/-- Second representation: n = x(3x-1)/2 + y(3y-1) + z(3z+1)/2. -/
def H2 : Prop := ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
  (n : ℤ) = (x : ℤ) * (3 * x - 1) / 2 + (y : ℤ) * (3 * y - 1) + z * (3 * z + 1) / 2

/-- Third representation: n = x(3x+1)/2 + 3y(3y+1)/2 + z(3z+1)/2. -/
def H3 : Prop := ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
  (n : ℤ) = (x : ℤ) * (3 * x + 1) / 2 + 3 * (y : ℤ) * (3 * y + 1) / 2 + z * (3 * z + 1) / 2

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a256855.main := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_oeis_a256855_R1
