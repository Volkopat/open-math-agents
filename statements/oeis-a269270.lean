import Mathlib

/-!
# Two-column arrays with exactly one complementary pair (A269270)

In row-major order, each horizontal edge joins the two entries of a row.
Each antidiagonal edge joins the right entry of a row to the left entry
immediately below it. These are precisely the consecutive pairs of the
word of length 2n. Entries lie between 0 and 3 inclusive. A complementary
pair is an unordered edge whose entries sum to 3.

The enumeration tries every next entry and records how many complementary
edges are still required. The empty height contributes zero to the series.
The formula below uses height n+1 so its exponent is always nonnegative.
The recurrence is empirical in the source. Colin Barker conjectured the
generating function and closed formula on January 20, 2019.

Source: https://oeis.org/A269270
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a269270
open PowerSeries

abbrev Color := Fin 4
def colors : List Color := [0, 1, 2, 3]

/-- Number of suffixes with k more cells, previous color x, and exactly j matching edges. -/
def count : ℕ → Color → ℕ → ℕ
  | 0, _, j => if j=0 then 1 else 0
  | k+1, x, j => (colors.map fun y =>
      if x.val + y.val = 3 then
        match j with
        | 0 => 0
        | m+1 => count k y m
      else count k y j).sum

def a : ℕ → ℕ
  | 0 => 0
  | n+1 => (colors.map fun x => count (2*n+1) x 1).sum

theorem main :
    (∀ n : ℕ, a (n+3)+81*a (n+1)=18*a (n+2)) ∧
    ((1-9*X)^2*(PowerSeries.mk (fun n => (a n : ℚ))) = 4*X*(1+9*X)) ∧
    ∀ n : ℕ, a (n+1) = 9^n*(8*n+4) := by
  sorry

end OMA.S_oeis_a269270
