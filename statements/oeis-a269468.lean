import Mathlib

/-!
# OEIS A269468: length-4 arrays with no repeated value equal to the previous one

Source: https://oeis.org/A269468
Credit: Sudharsan Rajendiran

A269468(n) is the number of length-4 arrays with entries in `0..n` with no repeated value equal to
the previous repeated value (row 4 of A269467). A "repeated value" is an entry equal to its
predecessor; the condition says that no two consecutive repeated values are equal. Colin Barker
conjectured (Jan 23 2019) the g.f. `2x(5 + 8x - x^2)/(1 - x)^5` and a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5) for n > 5. We state the g.f. as an identity
of formal power series over `ℚ` (it implies the recurrence); `a(0) = 0`, matching the factor `x`.

Conventions: an array is `v : Fin 4 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`repVals` lists its repeated values in order and the condition is `(repVals _).IsChain (· ≠ ·)`.
-/

namespace OMA.S_oeis_a269468

/-- The repeated values of a list, in order: the entries `x_i` with `x_i = x_(i-1)`. -/
def repVals : List ℕ → List ℕ
  | a :: b :: t => (if b = a then [b] else []) ++ repVals (b :: t)
  | _ => []

/-- A269468(n): the number of length-4 arrays with entries in `0..n` with no repeated value equal to
the previous repeated value, i.e. no two consecutive entries of `repVals` are equal. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.range (n + 1)).filter
    (fun v => (repVals (List.ofFn v)).IsChain (· ≠ ·))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - X) ^ 5 = 2 * X * (5 + 8 * X - X ^ 2) := by
  sorry

end OMA.S_oeis_a269468
