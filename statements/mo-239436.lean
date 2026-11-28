import Mathlib

/-!
# MathOverflow 239436

Source: https://mathoverflow.net/questions/239436
-/

namespace OMA.S_mo_239436

open Polynomial Finset

noncomputable def polynomialOfCoeffs {n : ℕ} (a : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ i : Fin (n + 1), monomial i.val (a i)

noncomputable def wronskianMap (n : ℕ) (ab : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ))
    (i : Fin (2 * n - 1)) : ℝ :=
  let a := polynomialOfCoeffs ab.1
  let b := polynomialOfCoeffs ab.2
  (a * b.derivative - a.derivative * b).coeff i.val

theorem main : ∀ n : ℕ, 1 ≤ n → Function.Surjective (wronskianMap n) := by
  sorry

end OMA.S_mo_239436
