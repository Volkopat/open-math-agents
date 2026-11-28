import Mathlib

/-!
# OEIS A267234: length-5 arrays, nothing after the first repeated value reaches it

Source: https://oeis.org/A267234
Credit: Sudharsan Rajendiran

A267234(n) is the number of length-5 arrays with entries in `0..n` with no following elements
greater than or equal to the first repeated value (row 5 of A267232): if `x_i` is the first entry
equal to its predecessor, every later entry is `< x_i`. Colin Barker conjectured (Jan 2019) the g.f.
`x(7 + 61x + 51x^2 + x^3)/(1 - x)^6` and the matching order-6 linear recurrence. We state the g.f. as an identity of formal
power series over `ℚ` (it implies the recurrence); `a(0) = 0`, matching the factor `x`.

Conventions: an array is `v : Fin 5 → ℕ` with entries `≤ n`, read as the list `List.ofFn v`;
`ok` scans for the first repeated value as described.
-/

namespace OMA.S_oeis_a267234

/-- `ok l`: scanning `l` for its first repeated value (the first entry equal to its predecessor),
every entry after it is smaller than it. Lists without a repeated value are `ok`. -/
def ok : List ℕ → Bool
  | a :: b :: t => if b = a then t.all (· < b) else ok (b :: t)
  | _ => true

/-- A267234(n): the number of length-5 arrays with entries in `0..n` with no following elements
greater than or equal to the first repeated value. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 5 => Finset.range (n + 1)).filter (fun v => ok (List.ofFn v))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - X) ^ 6 = X * (7 + 61 * X + 51 * X ^ 2 + X ^ 3) := by
  sorry

end OMA.S_oeis_a267234
