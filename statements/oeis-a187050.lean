import Mathlib

/-!
# Six-square bishop tours with a two-square move limit

R. H. Hardin counts ordered tours of six distinct squares. At each of the
five moves the bishop travels one or two squares diagonally. Translations
of a fixed relative tour are indexed by the lower left corner of its box.

The OEIS offset is one. The listed counts at side lengths 1, 2, 3 and 4
are 0, 0, 0 and 584. Colin Barker's displayed series starts with 584 X³,
so its coefficient at exponent k counts boards of side k+1. The recurrence
uses the board side itself.

Source: https://oeis.org/A187050 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @physbuzz.
-/

namespace OMA.S_oeis_a187050

abbrev Point := ℤ × ℤ

def directions : List Point :=
  [(-1,-1),(-1,1),(1,-1),(1,1),(-2,-2),(-2,2),(2,-2),(2,2)]

/-- Coordinate span for a relative tour whose starting coordinate is zero. -/
def extent (v : List ℤ) := (v.foldl max 0 - v.foldl min 0).toNat

/-- Enumerate one pair of spans per completion of an ordered partial tour.
The shorter span comes first since the board is square. -/
def shapes : ℕ → Point → List Point → List (ℕ × ℕ)
  | 0, _, seen =>
    let w := extent (seen.map Prod.fst)
    let h := extent (seen.map Prod.snd)
    [(min w h, max w h)]
  | n+1, p, seen => directions.flatMap fun d =>
    let q := p+d
    if q ∈ seen then [] else shapes n q (q::seen)

def placements (n : ℕ) (s : ℕ × ℕ) := (n-s.1)*(n-s.2)

/-- One starting position per translated bounding box, summed over all tours. -/
def term (n : ℕ) := ((shapes 5 0 [0]).map (placements n)).sum

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun k => (term (k+1) : ℤ)) * (1-X)^3 =
      4*X^3*(146 + 1300*X + 2599*X^2 + 2715*X^3 + 1651*X^4 +
        531*X^5 - 163*X^6 - 290*X^7 - 113*X^8)) ∧
    ∀ n > 12, (term n : ℤ) = 3*(term (n-1) : ℤ) - 3*(term (n-2) : ℤ) + term (n-3) := by
  sorry

end OMA.S_oeis_a187050
