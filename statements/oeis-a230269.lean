import Mathlib

/-!
# Two-column ternary arrays with a successor neighbor (OEIS A230269)

In each row, a cell may see its partner, the cell above it, or the cell
below it. The required neighbor has the cell's color plus one modulo three.
The top left cell is fixed to zero. The row recursion enumerates each array
once and checks both cells of a row as soon as its neighbors are known.
The empty height contributes zero to the ordinary generating series.

R. H. Hardin recorded the empirical recurrence. Colin Barker conjectured the
generating function and radical formula in 2018. The twos inside the powers absorb the
factor of two to the power minus n in his formula.

Source: https://oeis.org/A230269
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a230269
open PowerSeries

abbrev Color := Fin 3
abbrev Row := Color × Color

def colors : List Color := [0, 1, 2]
def rows : List Row := colors.flatMap fun l => colors.map fun r => (l,r)

def satisfied (cell partner : Color) (above below : Option Color) : Bool :=
  let target := cell+1
  partner == target || above == some target || below == some target

def legal (above : Option Row) (row : Row) (below : Option Row) : Bool :=
  satisfied row.1 row.2 (above.map Prod.fst) (below.map Prod.fst) &&
    satisfied row.2 row.1 (above.map Prod.snd) (below.map Prod.snd)

def nextRows (above : Option Row) (row : Row) : List Row :=
  rows.filter fun s => legal above row (some s)

/-- Completions with this current row and exactly k rows still to append. -/
def completions : ℕ → Option Row → Row → ℕ
  | 0, above, r => if legal above r none then 1 else 0
  | k+1, above, r => ((nextRows above r).map (completions k (some r))).sum

def a : ℕ → ℕ
  | 0 => 0
  | k+1 => (colors.map fun d => completions k none (0,d)).sum

noncomputable def closedValue (n : ℕ) : ℝ :=
  let s := Real.sqrt 17
  ((5-s)*((3+s)/2)^n - (5+s)*((3-s)/2)^n)/(4*s) - 1/2

theorem main :
    (∀ n : ℕ, a (n+4) + a (n+2) + 2*a (n+1) = 4*a (n+3)) ∧
    ((1-X)*(1-3*X-2*X^2)*(PowerSeries.mk (fun n => (a n : ℚ))) = 2*X^3) ∧
    ∀ n : ℕ, (a (n+1) : ℝ) = closedValue (n+1) := by
  sorry

end OMA.S_oeis_a230269
