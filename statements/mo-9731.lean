import Mathlib

/-!
# Polynomial representing all nonnegative integers

Source: https://mathoverflow.net/questions/9731/polynomial-representing-all-nonnegative-integers
Credit: @shc261392

Lagrange proved that every nonnegative integer is a sum of 4 squares, and Gauss that every
nonnegative integer is a sum of 3 triangular numbers.

Question. Is there a 2-variable polynomial `f(x, y) ∈ ℚ[x, y]` such that `f(ℤ × ℤ) = ℕ`?

Reading used here (the affirmative answer): `ℕ` is the set of nonnegative integers, viewed in `ℚ`;
the polynomial is an element of `MvPolynomial (Fin 2) ℚ` evaluated at integer points.
-/

namespace OMA.S_mo_9731

theorem main :
    ∃ f : MvPolynomial (Fin 2) ℚ,
      Set.range (fun p : ℤ × ℤ => MvPolynomial.eval ![(p.1 : ℚ), (p.2 : ℚ)] f) =
        Set.range (fun n : ℕ => (n : ℚ)) := by
  sorry

end OMA.S_mo_9731
