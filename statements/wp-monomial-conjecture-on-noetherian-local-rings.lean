import Mathlib

/-!
# Monomial conjecture on Noetherian local rings

Source: https://en.wikipedia.org/wiki/Monomial_conjecture
Hochster's monomial conjecture: if `R` is a Noetherian local ring of Krull dimension `d` and
`x₁, …, x_d` is a system of parameters, then for every `t ≥ 0`
`(x₁ ⋯ x_d) ^ t ∉ (x₁ ^ (t+1), …, x_d ^ (t+1))`.
(Settled in mixed characteristic by André, 2018; listed as open on the source page.)

Conventions. A system of parameters is a family `x : Fin d → R` of `d = dim R` elements whose
ideal has radical the maximal ideal (equivalently, is primary to it).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_monomial_conjecture_on_noetherian_local_rings

open IsLocalRing

theorem main :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (d : ℕ),
      ringKrullDim R = d →
      ∀ x : Fin d → R, (Ideal.span (Set.range x)).radical = maximalIdeal R →
      ∀ t : ℕ, (∏ i, x i) ^ t ∉ Ideal.span (Set.range fun i => x i ^ (t + 1)) := by
  sorry

end OMA.S_wp_monomial_conjecture_on_noetherian_local_rings
