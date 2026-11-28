import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Relation

/-!
# Nonprime islands on the square spiral

Source: Ya-Ping Lu, OEIS A341541, https://oeis.org/A341541 (CC BY-SA 4.0).
Credit: @jatin6

Number the lattice starting at 1 at the origin, then go right to 2, up to 3,
and continue counterclockwise. Each ring ends at its bottom-right corner,
whose label is (2r+1)². An island is a finite component of nonprime cells
separated from square 1. Walks move through shared sides.
-/

namespace OMA.S_oeis_a341541

abbrev Point := ℤ × ℤ

def label (p : Point) : ℕ :=
  let x := p.1
  let y := p.2
  let r : ℤ := (max x.natAbs y.natAbs : ℕ)
  let back := if y = -r then r-x else if x = -r then 3*r+y
    else if y = r then 5*r+x else 7*r-y
  ((2*r+1)^2 - back).toNat

def neighbors (p : Point) : List Point :=
  [(p.1+1,p.2), (p.1-1,p.2), (p.1,p.2+1), (p.1,p.2-1)]

def step (p q : Point) : Prop :=
  q ∈ neighbors p ∧ ¬ (label p).Prime ∧ ¬ (label q).Prime

def component (p : Point) : Set Point := {q | Relation.ReflTransGen step p q}

theorem main : ∀ p : Point, ¬ (label p).Prime → (component p).Finite →
    (0,0) ∉ component p → ∀ q ∈ component p, q = p := by
  sorry

end OMA.S_oeis_a341541
