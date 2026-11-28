import Mathlib

namespace OMA.S_mo_98493

abbrev GroupOfMoves := FreeGroup (Fin 2)

structure FinitelyAdditiveProbability where
  mass : Set GroupOfMoves → ℝ
  empty : mass ∅ = 0
  univ : mass Set.univ = 1
  nonneg : ∀ s, 0 ≤ mass s
  union : ∀ s t, Disjoint s t → mass (s ∪ t) = mass s + mass t

/-- Integrate the indicator first over the first move, then over the second.
The outer integral uses the measures of the superlevel sets. -/
noncomputable def payoff (W : Set GroupOfMoves)
    (μ ν : FinitelyAdditiveProbability) : ℝ :=
  ∫ t in (0 : ℝ)..1, ν.mass {y | t < μ.mass {x | x * y ∈ W}}

/-- Does the multiplication game on the free group on two generators
always have a saddle point for the specified iterated payoff? -/
theorem main :
    ∀ W : Set GroupOfMoves,
      ∃ μ₀ ν₀ : FinitelyAdditiveProbability,
        ∀ μ ν : FinitelyAdditiveProbability,
          payoff W μ ν₀ ≤ payoff W μ₀ ν₀ ∧ payoff W μ₀ ν₀ ≤ payoff W μ₀ ν := by
  sorry

end OMA.S_mo_98493
