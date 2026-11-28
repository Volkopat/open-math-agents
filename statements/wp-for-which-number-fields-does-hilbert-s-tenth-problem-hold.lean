import Mathlib.Computability.RE
import Mathlib.NumberTheory.NumberField.Basic

namespace OMA.S_wp_for_which_number_fields_does_hilbert_s_tenth_problem_hold

open scoped BigOperators NumberField

universe u

/-- The arity and a finite list of monomials, each with an exponent vector and
an integer coordinate vector for its coefficient. -/
abbrev PolynomialInput (degree : ℕ) := ℕ × List (List ℕ × (Fin degree → ℤ))

/-- A valid polynomial input has a zero with all coordinates in the ring of integers. -/
def HasIntegralSolution {K : Type u} [Field K] [NumberField K] {degree : ℕ}
    (basis : Module.Basis (Fin degree) ℤ (𝓞 K)) (input : PolynomialInput degree) : Prop :=
  (∀ monomial ∈ input.2, monomial.1.length = input.1) ∧
  ∃ x : Fin input.1 → 𝓞 K,
    (input.2.map (fun monomial =>
      basis.equivFun.symm monomial.2 *
        ∏ i : Fin input.1, x i ^ monomial.1.getD i.val 0)).sum = 0

/-- Hilbert's tenth problem is undecidable over the ring of integers of every
number field. Coefficients are supplied in any integral basis. -/
theorem main :
    ∀ (K : Type u) [Field K] [NumberField K] (degree : ℕ)
      (basis : Module.Basis (Fin degree) ℤ (𝓞 K)),
      ¬ ComputablePred (HasIntegralSolution basis) := by
  sorry

end OMA.S_wp_for_which_number_fields_does_hilbert_s_tenth_problem_hold
