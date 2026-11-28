import FormalConjectures.ErdosProblems.«125»

-- Reduction Erdos125.erdos_125.variants.zero_lower_positive_upper_density.R1 of Erdős Problem 125
-- (the case where the lower density vanishes but the upper density does not).
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction of two independent facts about the sumset of the base-3 and base-4
-- digit sets: its lower density is zero, and its upper density is positive. The first is a counting
-- upper bound, the second is a counting lower bound, so the two are attacked separately.

namespace OMA.R_Erdos125_erdos_125_variants_zero_lower_positive_upper_density_R1

open Nat Pointwise

/-- The lower density of the sumset vanishes. -/
def H1 : Prop :=
  ({x : ℕ | (digits 3 x).toFinset ⊆ {0, 1}} + {x : ℕ | (digits 4 x).toFinset ⊆ {0, 1}}).lowerDensity
    = 0

/-- The upper density of the sumset is strictly positive. -/
def H2 : Prop :=
  0 < ({x : ℕ | (digits 3 x).toFinset ⊆ {0, 1}} + {x : ℕ | (digits 4 x).toFinset ⊆ {0, 1}}).upperDensity

theorem main : H1 → H2 →
    type_of% @Erdos125.erdos_125.variants.zero_lower_positive_upper_density := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos125_erdos_125_variants_zero_lower_positive_upper_density_R1
