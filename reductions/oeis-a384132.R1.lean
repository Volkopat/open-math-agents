import OMAStatements.S_oeis_a384132

-- Reduction oeis-a384132.R1 of the largest nonrepresentable cube.
-- Credit: @Ciphore
-- H1 is the finite exclusion at 121; H2 is the positive representation of every larger cube.

namespace OMA.R_oeis_a384132_R1

open OMA.S_oeis_a384132

/-- The cube of 121 is not a sum of four distinct positive cubes. -/
def H1 : Prop := ¬ IsSumOfFourDistinctCubes 121

/-- Every larger cube is a sum of four distinct positive cubes. -/
def H2 : Prop := ∀ k : ℕ, 121 < k → IsSumOfFourDistinctCubes k

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a384132.main := by
  intro h1 h2
  constructor
  · exact ⟨by norm_num, h1⟩
  · intro k hk
    by_contra hkle
    have hkgt : 121 < k := by omega
    exact hk.2 (h2 k hkgt)

end OMA.R_oeis_a384132_R1
