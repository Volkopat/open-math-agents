import Mathlib.RingTheory.PowerSeries.Basic

/-!
# OEIS A207452

Width 7. Forbidden horizontal triples are 000 and 001, and forbidden
vertical triples are 001 and 101. Source: https://oeis.org/A207452

R. H. Hardin defined the sequence. Colin Barker conjectured these formulas in 2018.
Formalization: @blakestone-x.
-/

namespace OMA.S_oeis_a207452

/-- A mask is a width-w row, with its leftmost cell the most significant bit.
The three-bit number at position j reads one contiguous horizontal triple. -/
def rows (w p q : Nat) : List Nat :=
  (List.range (2^w)).filter fun r => (List.range (w-2)).all fun j =>
    let triple := (r >>> j) % 8
    triple != p && triple != q

/-- Vertical 001 and 101 are precisely the triples ending in 01. -/
def below (rs : List Nat) (r : Nat) : List Nat :=
  rs.filter fun s => s &&& r == s

/-- Enumerate length-h suffixes in which each row is a subset of its predecessor. -/
def tails (rs : List Nat) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | h+1, r => (below rs r).flatMap fun s => (tails rs h s).map (s :: ·)

/-- The first row is free. Starting the suffix below an all-ones mask gives
the second row a free choice as well. Zero is the generating series offset. -/
def gridCount (w p q : Nat) : Nat → Int
  | 0 => 0
  | h+1 =>
    let rs := rows w p q
    ((rs.flatMap fun r => (tails rs h (2^w-1)).map (r :: ·)).length : Int)


def a : Nat → Int := gridCount 7 0 1

theorem main :
    (PowerSeries.mk a * (1-PowerSeries.X)^5 =
      42 * PowerSeries.X * (1 + 37*PowerSeries.X + 55*PowerSeries.X^2 + 3*PowerSeries.X^3)) ∧
    (∀ n : Nat, a (n+6) = 5*a (n+5) - 10*a (n+4) + 10*a (n+3) - 5*a (n+2) + a (n+1)) := by
  sorry

end OMA.S_oeis_a207452
