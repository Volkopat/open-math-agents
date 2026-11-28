import Mathlib

/-!
# The minimum visible pip count for a polycube of dice

Matt Donahoe conjectured in OEIS A363609 that a polycube on k³ standard
dice has minimum visible pip sum 6k(k+2) for k > 1. Positions are on the
cubic lattice, face adjacency defines connectedness, and each die may be
rotated independently. A face is exposed when the adjacent cell is empty.

For a single die an axis with two exposed faces contributes seven pips.
If s axes have a single exposed face, their smallest possible joint
contribution is 1+...+s. These values can all be exposed together by a
rotation: the small labels 1, 2 and 3 meet at a corner, and the rotation
group is transitive on corners, on edges and on faces. When one or two
whole opposite pairs are exposed one first assigns the smallest label
pairs to the singly exposed axes. With two single axes one can exchange
their assignments to obtain the required handedness. The score below
adds these independently attainable local minima.

Source: https://oeis.org/A363609
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a363609

abbrev Cell := ℤ × ℤ × ℤ

def dx (i : ℤ) : Cell := (i, 0, 0)
def dy (i : ℤ) : Cell := (0, i, 0)
def dz (i : ℤ) : Cell := (0, 0, i)

def axisNeighbor (u v : Cell) : Prop :=
  ∃ i : ℤ, (i = 1 ∨ i = -1) ∧
    (v = u + dx i ∨ v = u + dy i ∨ v = u + dz i)

def connected (S : Finset Cell) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S,
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ axisNeighbor a b) u v

def bare (S : Finset Cell) (u d : Cell) : ℕ := if u + d ∈ S then 0 else 1

def localCost (a b c : ℕ) : ℕ :=
  let s := a%2 + b%2 + c%2
  7 * (a/2 + b/2 + c/2) + s*(s+1)/2

def score (S : Finset Cell) : ℕ :=
  ∑ u ∈ S, localCost (bare S u (dx 1) + bare S u (dx (-1)))
    (bare S u (dy 1) + bare S u (dy (-1)))
    (bare S u (dz 1) + bare S u (dz (-1)))

theorem main : ∀ k : ℕ, 1 < k →
    IsLeast {s : ℕ | ∃ S : Finset Cell, S.card = k^3 ∧ connected S ∧ score S = s}
      (6*(k+2)*k) := by
  sorry

end OMA.S_oeis_a363609
