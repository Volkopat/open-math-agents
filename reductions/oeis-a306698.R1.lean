import OMAStatements.S_oeis_a306698

-- Reduction oeis-a306698.R1 of the Recaman-like range conjecture.
-- Credit: @Ciphore
-- H1 is the modular obstruction: every value is 0 or 1 modulo 3.
-- H2 is the coverage half: every such value eventually occurs.

namespace OMA.R_oeis_a306698_R1

open OMA.S_oeis_a306698

/-- Every term of the sequence is congruent to zero or one modulo three. -/
def H1 : Prop :=
  Set.range sequence ⊆ {m : ℕ | m % 3 = 0 ∨ m % 3 = 1}

/-- Every integer congruent to zero or one modulo three occurs in the sequence. -/
def H2 : Prop :=
  {m : ℕ | m % 3 = 0 ∨ m % 3 = 1} ⊆ Set.range sequence

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a306698.main := by
  intro h1 h2
  exact Set.Subset.antisymm h1 h2

end OMA.R_oeis_a306698_R1
