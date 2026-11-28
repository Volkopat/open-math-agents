import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Nat.Choose.Basic

/-!
# Constant coefficients in the A092674 polynomial recurrence

The first polynomial is X. Thereafter the construction uses the triangular
number and the original floor weights. The extra index zero contributes
zero and lets Fin n represent the preceding indices. The conjecture
asserts nonnegativity of every constant coefficient.

Source: https://oeis.org/A092674
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a092674

open Polynomial Finset

noncomputable def polynomial : ℕ → ℤ[X]
  | 0 => 0
  | 1 => X
  | n+2 => C (((n+3).choose 2 : ℕ) : ℤ) -
      ∑ i : Fin (n+2), polynomial i.val * C (((n+2)/i.val : ℕ) : ℤ)
termination_by n => n
decreasing_by exact Fin.isLt _

theorem main : ∀ n : ℕ, 0 < n → 0 ≤ (polynomial n).coeff 0 := by
  sorry

end OMA.S_oeis_a092674
