import Mathlib

/-!
# OEIS A200432: 5 integers in -n..n with sum zero and no two or three adjacent ones summing to zero

Source: https://oeis.org/A200432
Credit: Sudharsan Rajendiran

A200432(n) is the number of arrays `x(0..4)` of 5 integers in `-n..n` with zero sum and no two or
three adjacent elements summing to zero. Colin Barker conjectured (May 2018) the g.f.
`10x^2(8 + 12x + 3x^2)/(1 - x)^5` and the recurrence
`a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 5`. We state the g.f. as an
identity of formal power series over `ℚ`, with the denominator multiplied across:
`(∑_(n ≥ 0) a(n) x^n) (1 - x)^5 = 10x^2(8 + 12x + 3x^2)`
(the definition gives `a(0) = a(1) = 0`, in agreement with the g.f.).

Conventions: an array is `v : Fin 5 → ℤ` with entries in `[-n, n]`; the conditions are
`v i + v (i+1) ≠ 0` for `i = 0..3` and `v i + v (i+1) + v (i+2) ≠ 0` for `i = 0..2`.
-/

namespace OMA.S_oeis_a200432

/-- A200432(n): the number of arrays `x(0..4)` of 5 integers in `-n..n` with zero sum and no two or
three adjacent elements summing to zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(n : ℤ)) n).filter (fun v => ∑ i, v i = 0 ∧
    (∀ i : Fin 4, v i.castSucc + v i.succ ≠ 0) ∧
    ∀ i : Fin 3, v i.castSucc.castSucc + v i.succ.castSucc + v i.succ.succ ≠ 0)).card

open PowerSeries in
/-- Barker's conjectured g.f. `10x^2(8 + 12x + 3x^2)/(1 - x)^5`. -/
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - X) ^ 5 = 10 * X ^ 2 * (8 + 12 * X + 3 * X ^ 2) := by
  sorry

end OMA.S_oeis_a200432
