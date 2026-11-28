import Mathlib

/-!
# Four-square tours by a queen with a two-square move limit

R. H. Hardin counts ordered tours of four distinct squares on an n by n board.
The source examples label the squares 1 through 4. Each of the three moves
travels one or two squares along a row, column or diagonal.

Colin Barker gives the generating function and recurrence in OEIS A187029.
Source: https://oeis.org/A187029 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @physbuzz.
-/

namespace OMA.S_oeis_a187029

abbrev Point := ℤ × ℤ

/-- The sixteen allowed directed displacements. -/
def move : Fin 16 → Point :=
  ![(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1),
    (-2,-2),(-2,0),(-2,2),(0,-2),(0,2),(2,-2),(2,0),(2,2)]

/-- Extent of the projection of the four visited points onto one coordinate. -/
def extent (a b c : ℤ) : ℕ :=
  (max 0 (max a (max b c)) - min 0 (min a (min b c))).toNat

/-- Bounding-box spans, provided all four squares are distinct. -/
def spans (i j k : Fin 16) : Option (ℕ × ℕ) :=
  let p := move i
  let q := p + move j
  let r := q + move k
  if ([0,p,q,r] : List Point).Nodup then
    some (extent p.1 q.1 r.1, extent p.2 q.2 r.2)
  else none

/-- The lower left corner of the bounding box has n-w possible columns
and n-h possible rows. Natural subtraction gives zero if the tour cannot fit. -/
def placements (n : ℕ) : Option (ℕ × ℕ) → ℕ
  | some (w,h) => (n-w)*(n-h)
  | none => 0

def term (n : ℕ) : ℕ :=
  ∑ i : Fin 16, ∑ j : Fin 16, ∑ k : Fin 16, placements n (spans i j k)

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => (term n : ℤ)) * (1 - X)^3 =
      4*X^2*(6 + 318*X + 774*X^2 + 602*X^3 + 117*X^4 - 9*X^5 - 56*X^6)) ∧
    ∀ n > 8, (term n : ℤ) = 3*(term (n-1) : ℤ) - 3*(term (n-2) : ℤ) + term (n-3) := by
  sorry

end OMA.S_oeis_a187029
