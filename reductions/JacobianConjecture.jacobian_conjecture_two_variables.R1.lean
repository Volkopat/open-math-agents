import FormalConjectures.Wikipedia.JacobianConjecture

/-!
# Jacobian conjecture, two variables

The target asks that every regular function in two variables over a field of characteristic zero
with invertible Jacobian determinant has a regular inverse. The pinned module proves the bridge
`sanity_check_condition_1`: an invertible Jacobian determinant is exactly a nonzero constant
determinant. This reduction separates that proved reformulation of the hypothesis from the
genuinely open invertibility core.
-/

namespace OMA.R_JacobianConjecture_jacobian_conjecture_two_variables_R1

open MvPolynomial RegularFunction

-- Reduction JacobianConjecture.jacobian_conjecture_two_variables.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-- Open core: a two-variable regular function over a characteristic-zero field whose Jacobian
    determinant is a nonzero constant has a regular inverse. -/
def H1 : Prop :=
  ∀ {k : Type} [Field k] [CharZero k] (F : RegularFunction k (Fin 2) (Fin 2)),
    (∃ c : k, c ≠ 0 ∧ F.Jacobian.det = .C c) →
      ∃ (G : RegularFunction k (Fin 2) (Fin 2)),
        G.comp F = id k (Fin 2) ∧ F.comp G = id k (Fin 2)

/-- Proved bridge (`sanity_check_condition_1`, JacobianConjecture.lean:134): an invertible
    Jacobian determinant is exactly a nonzero constant determinant. -/
def H2 : Prop :=
  ∀ {k σ : Type} [Fintype σ] [DecidableEq σ] [Field k] (F : RegularFunction k σ σ),
    IsUnit F.Jacobian.det ↔ (∃ c : k, c ≠ 0 ∧ F.Jacobian.det = .C c)

theorem main :
    H1 → H2 → type_of% @JacobianConjecture.jacobian_conjecture_two_variables := by
  intro h1 h2 k instF instCZ F hF
  exact h1 F ((h2 (σ := Fin 2) F).1 hF)

end OMA.R_JacobianConjecture_jacobian_conjecture_two_variables_R1
