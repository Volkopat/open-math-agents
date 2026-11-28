import FormalConjectures.ErdosProblems.«145»

/-! Splitting the Erdos 145 limit-existence question at alpha = 11/3 into
the proved range and the open tail. -/

-- Reduction Erdos145.erdos_145.R1 of Erdos Problem 145
-- Existence of the limit of the normalized squarefree-gap power sums.
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter
open scoped Topology

namespace OMA.R_Erdos145_erdos_145_R1

-- The proved range 0 <= alpha < 11/3 (upstream theorem erdos_145.variants.lt_eleven_thirds).
def H1 : Prop :=
  ∀ α : ℝ, α ∈ Set.Ico 0 (11 / 3) →
    ∃ β : ℝ, atTop.Tendsto
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α) (𝓝 β)

-- The open tail: alpha at or beyond 11/3.
def H2 : Prop :=
  ∀ α : ℝ, 11 / 3 ≤ α →
    ∃ β : ℝ, atTop.Tendsto
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α) (𝓝 β)

theorem main : H1 → H2 → type_of% @Erdos145.erdos_145 := by
  intro hknown htail α hα
  by_cases hsmall : α < 11 / 3
  · exact hknown α ⟨hα, hsmall⟩
  · exact htail α (le_of_not_gt hsmall)

end OMA.R_Erdos145_erdos_145_R1
