import Mathlib

/-!
# OEIS A269471: length-7 arrays with no repeated value equal to the previous one

Source: https://oeis.org/A269471
Credit: Sudharsan Rajendiran

A269471(n) is the number of length-7 arrays with entries in `0..n` with no repeated value equal to
the previous repeated value (row 7 of A269467). A "repeated value" is an entry equal to its
predecessor; the condition says that no two consecutive repeated values are equal. Colin Barker
conjectured (Jan 23 2019) the g.f. `6x(5 + 161x + 498x^2 + 190x^3 - 23x^4 + 9x^5)/(1 - x)^8` and the order-8 recurrence with coefficients from (1 - x)^8, for n > 8. We state the g.f. as an identity
of formal power series over `ℚ` (it implies the recurrence); `a(0) = 0`, matching the factor `x`.

Conventions: an array is `v : Fin 7 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`repVals` lists its repeated values in order and the condition is `(repVals _).IsChain (· ≠ ·)`.
-/

namespace OMA.S_oeis_a269471

/-- The repeated values of a list, in order: the entries `x_i` with `x_i = x_(i-1)`. -/
def repVals : List ℕ → List ℕ
  | a :: b :: t => (if b = a then [b] else []) ++ repVals (b :: t)
  | _ => []

/-- A269471(n): the number of length-7 arrays with entries in `0..n` with no repeated value equal to
the previous repeated value, i.e. no two consecutive entries of `repVals` are equal. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 7 => Finset.range (n + 1)).filter
    (fun v => (repVals (List.ofFn v)).IsChain (· ≠ ·))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - X) ^ 8 = 6 * X * (5 + 161 * X + 498 * X ^ 2 + 190 * X ^ 3 - 23 * X ^ 4 + 9 * X ^ 5) := by
  sorry

end OMA.S_oeis_a269471
