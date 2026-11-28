import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Field.Rat

/-! Sources: https://mathoverflow.net/questions/220631 and https://mathoverflow.net/questions/220440.
The inverse-squared-norm weights give the normalized polynomials shown in the examples. -/

open scoped BigOperators
open Polynomial

namespace OMA.S_mo_220631

/-- The Legendre polynomial in Rodrigues' formula. -/
noncomputable def legendre (n : ℕ) : ℚ[X] :=
  C (1 / ((2 : ℚ) ^ n * n.factorial)) * (derivative^[n]) ((X ^ 2 - 1) ^ n)

/-- The normalized minimizer from the linked problem.
The inverse squared norms of the Legendre polynomials are (2k+1)/2.
These weights give the source's displayed polynomial for n = 2. -/
noncomputable def minimizer (n : ℕ) : ℚ[X] :=
  C (2 / ((n + 1 : ℚ) * (n + 2 : ℚ))) *
    ∑ i ∈ Finset.range (n / 2 + 1), C ((2 * (n - 2 * i) + 1 : ℕ) : ℚ) * legendre (n - 2 * i)

/-- Borel's triangle (OEIS A234950), with row and column indices starting at zero. -/
def borel (n k : ℕ) : ℚ :=
  ((2 * n + 2).choose (n - k) : ℚ) * ((n + k).choose k : ℚ) / (n + 1 : ℚ)

theorem main : ∀ n : ℕ, minimizer n =
    ∑ i ∈ Finset.range (n / 2 + 1),
      C ((-1 : ℚ) ^ i * borel (n - i) i / (2 : ℚ) ^ n) * X ^ (n - 2 * i) := by
  sorry

end OMA.S_mo_220631
