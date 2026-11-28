import Mathlib

/-!
# Polynomial identification of natural numbers

Source: https://mathoverflow.net/questions/501564
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Prunescu's Open Question A): is there a polynomial `f(x, y, n) ∈ ℤ[x, y, n]` such that,
for every integer `n`, `n ≥ 0 ⟺ ∃ x, y ∈ ℤ, f(x, y, n) = 0`?

Conventions:
* Polynomials in `x, y, n` are `MvPolynomial (Fin 3) ℤ`, evaluated at `![x, y, n]`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_501564

/-- Some `f ∈ ℤ[x, y, n]` defines `ℕ ⊆ ℤ` with two existential integer variables. -/
theorem main : ∃ f : MvPolynomial (Fin 3) ℤ, ∀ n : ℤ,
    (0 ≤ n ↔ ∃ x y : ℤ, MvPolynomial.eval ![x, y, n] f = 0) := by
  sorry

end OMA.S_mo_501564
