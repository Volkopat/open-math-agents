import Mathlib

/-!
# A298023. Balls about a trivalent node of the dual elongated triangular tiling

Source: https://oeis.org/A298023 and https://oeis.org/A298022
Credit: @etaubman

The primal tiling consists of alternating horizontal bands of squares and
triangles. A square in band j lies between an up-triangle in band j and a
down-triangle in band j-1. The two orientations alternate across each
triangle band. Index i runs along a band. The vertices of the dual are these
faces, with an edge across each shared side. Both trivalent orientations give
isomorphic rooted graphs by a half-turn. A298023 counts the vertices in the
closed ball, the partial sum of the coordination sequence A298022.
-/

namespace OMA.S_oeis_a298023

inductive Face where
  | square (j i : ℤ)
  | up (j i : ℤ)
  | down (j i : ℤ)
  deriving DecidableEq

open Face

def neighbors : Face → Finset Face
  | square j i => {square j (i-1), square j (i+1), up j i, down (j-1) i}
  | up j i => {square j i, down j i, down j (i-1)}
  | down j i => {square (j+1) i, up j i, up j (i+1)}

def ball : ℕ → Finset Face
  | 0 => {up 0 0}
  | n+1 => let s := ball n; s ∪ s.biUnion neighbors

def a (n : ℕ) : ℤ := (ball n).card

def conjecture : Prop :=
  let A : PowerSeries ℤ := PowerSeries.mk a
  let X : PowerSeries ℤ := PowerSeries.X
  A * ((1-X)^3 * (1+X+X^2)) = 1+2*X+4*X^2+4*X^3+3*X^4+2*X^5-2*X^8 ∧
  ∀ n : ℕ, 5 < n → a n = 2*a (n-1) - a (n-2) + a (n-3) - 2*a (n-4) + a (n-5)

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a298023
