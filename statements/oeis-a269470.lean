import Mathlib

/-!
# OEIS A269470: length-6 arrays with no repeated value equal to the previous one

Source: https://oeis.org/A269470
Credit: Sudharsan Rajendiran

A269470(n) is the number of length-6 arrays with entries in `0..n` with no repeated value equal to
the previous repeated value (row 6 of A269467). A "repeated value" is an entry equal to its
predecessor; the condition says that no two consecutive repeated values are equal. Colin Barker
conjectured (Jan 23 2019) the g.f. `2x(11 + 154x + 204x^2 - 14x^3 + 5x^4)/(1 - x)^7` and the order-7 recurrence with coefficients from (1 - x)^7, for n > 7. We state the g.f. as an identity
of formal power series over `ℚ` (it implies the recurrence); `a(0) = 0`, matching the factor `x`.

Conventions: an array is `v : Fin 6 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`repVals` lists its repeated values in order and the condition is `(repVals _).IsChain (· ≠ ·)`.
-/

namespace OMA.S_oeis_a269470

/-- The repeated values of a list, in order: the entries `x_i` with `x_i = x_(i-1)`. -/
def repVals : List ℕ → List ℕ
  | a :: b :: t => (if b = a then [b] else []) ++ repVals (b :: t)
  | _ => []

/-- A269470(n): the number of length-6 arrays with entries in `0..n` with no repeated value equal to
the previous repeated value, i.e. no two consecutive entries of `repVals` are equal. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 6 => Finset.range (n + 1)).filter
    (fun v => (repVals (List.ofFn v)).IsChain (· ≠ ·))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - X) ^ 7 = 2 * X * (11 + 154 * X + 204 * X ^ 2 - 14 * X ^ 3 + 5 * X ^ 4) := by
  sorry

end OMA.S_oeis_a269470
