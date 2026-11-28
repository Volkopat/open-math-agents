import Mathlib

/-!
# OEIS A269438: length-6 arrays with non-increasing repeated values

Source: https://oeis.org/A269438
Credit: Sudharsan Rajendiran

A269438(n) is the number of length-6 arrays with entries in `0..n` with no repeated value greater
than the previous repeated value. A "repeated value" is an entry equal to its
predecessor; the condition says the list of repeated values, in order, is non-increasing. Colin
Barker conjectured (Jan 2019) the g.f. `x(51 + 265x + 391x^2 + 14x^3 + 5x^4 - 7x^5 + x^6)/(1 - x)^7` (offset 1) and the matching order-7 linear
recurrence. We state the g.f. as an identity of formal power series over `ℚ` for the shifted series
`Σ_(n ≥ 0) a(n + 1) x^n`, i.e. with the factor `x` cancelled (the definition also gives `a(0) = 1`,
which the g.f. does not describe).

Conventions: an array is `v : Fin 6 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`repVals` lists its repeated values in order and the condition is `(repVals _).IsChain (· ≥ ·)`.
-/

namespace OMA.S_oeis_a269438

/-- The repeated values of a list, in order: the entries `x_i` with `x_i = x_(i-1)`. -/
def repVals : List ℕ → List ℕ
  | a :: b :: t => (if b = a then [b] else []) ++ repVals (b :: t)
  | _ => []

/-- A269438(n): the number of length-6 arrays with entries in `0..n` with no repeated value greater
than the previous repeated value, i.e. the repeated values form a non-increasing list. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 6 => Finset.range (n + 1)).filter
    (fun v => (repVals (List.ofFn v)).IsChain (· ≥ ·))).card

open PowerSeries in
/-- Barker's g.f. `x(51 + 265x + 391x^2 + 14x^3 + 5x^4 - 7x^5 + x^6)/(1 - x)^7` for `Σ_(n ≥ 1) a(n) x^n`, written
with the factor `x` cancelled, i.e. for the shifted series `Σ_(n ≥ 0) a(n + 1) x^n`. -/
theorem main :
    (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 = 51 + 265 * X + 391 * X ^ 2 + 14 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + X ^ 6 := by
  sorry

end OMA.S_oeis_a269438
