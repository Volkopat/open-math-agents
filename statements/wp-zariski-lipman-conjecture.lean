import Mathlib

/-!
# Zariski–Lipman conjecture

Source: https://en.wikipedia.org/wiki/Zariski–Lipman_conjecture
For a complex algebraic variety `V` with coordinate ring `R`, if the module of derivations of
`R` is a free `R`-module, then `V` is smooth.

Conventions. `V` is an affine complex variety: `R` is a finitely generated `ℂ`-algebra that is
an integral domain. The derivations are `Derivation ℂ R R`; smoothness of `V` is Mathlib's
`Algebra.Smooth ℂ R`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_wp_zariski_lipman_conjecture

theorem main :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℂ R], Algebra.FiniteType ℂ R →
      Module.Free R (Derivation ℂ R R) → Algebra.Smooth ℂ R := by
  sorry

end OMA.S_wp_zariski_lipman_conjecture
