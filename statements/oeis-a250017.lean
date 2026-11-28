import Mathlib

/-!
# A250017. Eight-letter words with no tied middle ranks in a six-letter window

Source: https://oeis.org/A250017
Credit: @etaubman

R. H. Hardin counts eight positions over the ordered alphabet from 0 to n.
In a sorted six-letter window there is a split whose lower maximum equals the
upper minimum precisely when positions three and four have the same value.
Scanning alphabet values in increasing order, a forbidden tie occurs when a
single value takes the occupied window size from at most two to at least four.

The same four middle positions belong to all three windows. Keep the exact
occupancy of the outer four positions and the number of occupied middle
positions. At a new value the binomial factor chooses the newly occupied
middle slots among the remaining labelled slots. Every sequence of these
choices fills each word in exactly one way, including values used nowhere.
Colin Barker proposed the recurrence and generating function in 2018.
-/

namespace OMA.S_oeis_a250017

abbrev State := Fin 80

private def center (s : State) : ℕ := s.val / 16
private def outer (s : State) (i : ℕ) : ℕ := s.val / 2^i % 2
private def window (s : State) (i : ℕ) : ℕ := center s + outer s i + outer s (i+1)

/-- A strict transition assigns the current value to one or more actual
positions. The four outer bits correspond, in order, to positions 0,1,6,7. -/
def multiplicity (s t : State) : ℕ :=
  if s = t || center t < center s ||
      (List.range 4).any (fun i => outer t i < outer s i) ||
      (List.range 3).any (fun i => window s i < 3 && 3 < window t i) then 0
  else (4 - center s).choose (center t - center s)

private def edges (s : State) : List (State × ℕ) :=
  (List.finRange 80).filterMap fun t =>
    let w := multiplicity s t
    if w = 0 then none else some (t,w)

private def weighted : List (State × ℕ) → (State → ℕ) → ℕ
  | [], _ => 0
  | (t,w)::rest, f => w * f t + weighted rest f

private def advance (f : State → ℕ) (s : State) : ℕ := weighted (edges s) f

/-- Count ways to fill the remaining positions using q alphabet values. -/
def ways : ℕ → State → ℕ
  | 0, s => if s.val = 79 then 1 else 0
  | q+1, s => ways q s + advance (ways q) s

def total (n : ℕ) : ℚ := ways (n+1) 0

open PowerSeries

theorem main :
    (∀ n : ℕ, total n = (n:ℚ)^8 + 41/35*(n:ℚ)^7 + 56/15*(n:ℚ)^6 + 22/5*(n:ℚ)^5 +
      19/3*(n:ℚ)^4 + 17/5*(n:ℚ)^3 - 16/15*(n:ℚ)^2 + 36/35*n) ∧
    (∀ n : ℕ, total (n+9) = 9*total (n+8) - 36*total (n+7) + 84*total (n+6) - 126*total (n+5) +
      126*total (n+4) - 84*total (n+3) + 36*total (n+2) - 9*total (n+1) + total n) ∧
    (1-X)^9 * mk total =
      (4*X*(5+183*X+1506*X^2+3974*X^3+3441*X^4+903*X^5+68*X^6) : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a250017
