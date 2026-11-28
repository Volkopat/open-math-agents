import Mathlib

/-!
# OEIS A202077: 5-integer zero-sum arrays with odd adjacent sums

Source: https://oeis.org/A202077
Credit: Sudharsan Rajendiran

A202077(n) is the number of arrays of 5 integers in `-n..n` with sum zero and the sum of every
adjacent pair being odd. Colin Barker conjectured (May 2018) the g.f.
`2x(1 + 12x + 22x^2 + 45x^3 + 22x^4 + 12x^5 + x^6)/((1 - x)^5 (1 + x)^4)` and the matching closed
forms for even and odd `n`. We state the g.f. as an identity of formal power series over `ℚ` (with the
denominator multiplied across); here `a(0) = 0`, matching the factor `x`.

Conventions: an array is `v : Fin 5 → ℤ` with entries in `[-n, n]`; "every adjacent pair has odd sum"
is `∀ i : Fin 4, Odd (v i.castSucc + v i.succ)`.
-/

namespace OMA.S_oeis_a202077

/-- A202077(n): the number of arrays of 5 integers in `-n..n` with sum zero and the sum of every
adjacent pair being odd. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(n : ℤ)) n).filter
    (fun v => ∑ i, v i = 0 ∧ ∀ i : Fin 4, Odd (v i.castSucc + v i.succ))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 4) =
      2 * X * (1 + 12 * X + 22 * X ^ 2 + 45 * X ^ 3 + 22 * X ^ 4 + 12 * X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a202077
