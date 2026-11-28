import FormalConjectures.ErdosProblems.«125»

-- Reduction Erdos125.erdos_125.variants.zero_density.R1 of Erdős Problem 125 (zero-density case).
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target says that the sumset of the base-3 and base-4 digit sets is a set of density zero, in
-- both the upper and the lower sense. These are two separate inequalities on two separate density
-- invariants, so each is its own step.

namespace OMA.R_Erdos125_erdos_125_variants_zero_density_R1

open Nat Pointwise

/-- The upper density of the sumset vanishes. -/
def H1 : Prop :=
  ({x : ℕ | (digits 3 x).toFinset ⊆ {0, 1}} + {x : ℕ | (digits 4 x).toFinset ⊆ {0, 1}}).upperDensity
    = 0

/-- The lower density of the sumset vanishes. -/
def H2 : Prop :=
  ({x : ℕ | (digits 3 x).toFinset ⊆ {0, 1}} + {x : ℕ | (digits 4 x).toFinset ⊆ {0, 1}}).lowerDensity
    = 0

theorem main : H1 → H2 → type_of% @Erdos125.erdos_125.variants.zero_density := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos125_erdos_125_variants_zero_density_R1
