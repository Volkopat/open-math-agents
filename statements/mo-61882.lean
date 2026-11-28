import Mathlib

/-!
# Meromorphic 1-form and Picard's theorem

Source: https://mathoverflow.net/questions/61882
Let `U₁, …, Uₙ` be an open cover of the punctured unit disc `D*` and `fⱼ` injective
holomorphic functions on `Uⱼ` with `dfⱼ = dfₖ` on every `Uⱼ ∩ Uₖ`. Do the differentials glue
to a meromorphic 1-form on `D`? `main` states the affirmative answer.

Conventions. A 1-form `g dz` on `D*` is identified with the function `g`; the glued form is
`g = fⱼ'` on `Uⱼ`, and it extends meromorphically to `D` exactly when `g` is meromorphic at
`0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_61882

open Metric

theorem main :
    ∀ (n : ℕ) (U : Fin n → Set ℂ) (f : Fin n → ℂ → ℂ),
      (∀ j, IsOpen (U j)) → (⋃ j, U j) = ball 0 1 \ {0} →
      (∀ j, DifferentiableOn ℂ (f j) (U j)) → (∀ j, Set.InjOn (f j) (U j)) →
      (∀ j k, ∀ z ∈ U j ∩ U k, deriv (f j) z = deriv (f k) z) →
      ∃ g : ℂ → ℂ, MeromorphicAt g 0 ∧ ∀ j, ∀ z ∈ U j, g z = deriv (f j) z := by
  sorry

end OMA.S_mo_61882
