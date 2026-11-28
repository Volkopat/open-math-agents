import Mathlib

/-!
# A298022. Coordination sequence at a trivalent vertex of the dual elongated triangular tiling

Source: https://oeis.org/A298022 and https://oeis.org/A049347
Credit: @Aryan-Poonacha

The face coordinates and adjacency below are from @etaubman's A298023 statement.
Each shared side in the primal tiling gives one edge in the dual. The root is
the up-triangle at (0,0). A half-turn exchanges the two triangular orientations.
-/

namespace OMA.S_oeis_a298022

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

/-- The sphere of radius zero consists of the root. Later spheres are ball differences. -/
def a : ℕ → ℤ
  | 0 => 1
  | n+1 => (ball (n+1)).card - ((ball n).card : ℤ)

/-- A049347, with offset zero, repeats 1, −1, 0. -/
def periodThree (n : ℕ) : ℤ :=
  match n % 3 with
  | 0 => 1
  | 1 => -1
  | _ => 0

/-- Colin Barker's generating function and recurrence, and Stefano Spezia's formula.
The last equality clears the rational factors in the source. -/
def conjecture : Prop :=
  let S : PowerSeries ℤ := PowerSeries.mk a
  let X : PowerSeries ℤ := PowerSeries.X
  S * ((1-X)^2 * (1+X+X^2)) = 1+2*X+4*X^2+4*X^3+3*X^4+2*X^5-2*X^8 ∧
  (∀ n : ℕ, 5 < n → a n = a (n-1) + a (n-3) - a (n-4)) ∧
  (∀ n : ℕ, 4 < n → 9 * a n = 42 * (n : ℤ) + 3 * periodThree (n+2))

theorem main : conjecture := by
  sorry

end OMA.S_oeis_a298022
