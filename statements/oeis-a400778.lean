import Mathlib

/-!
# OEIS A400778: the width-two, width-three and width-four mirror counts

Source: https://oeis.org/A400778
Credit: @arcstone09

A placement chooses two-sided mirrors on internal shared sides of a rectangle of
unit cells. The four arcs inside each cell join adjacent side midpoints. At a
mirror or an outside boundary they reflect; at an unmirrored internal side they
continue collinearly into the neighbouring cell. A single loop uses every arc.

Each arc is represented by its two ends. Joining ends along their arc and across
a reflection or transmission gives exactly the unoriented physical components.
Placements remain labelled; neither geometric symmetries nor ray orientations
introduce a quotient or multiplicity.

Prior proof: Cyril Shtabtsovsky, Light in a box of mirrors, 2026, Corollary 2(a-c).
https://doi.org/10.5281/zenodo.24546586
This file states the three assertions and does not formalise that proof.
-/

namespace OMA.S_oeis_a400778

abbrev Point := ℕ × ℕ
abbrev Cell (n k : ℕ) := Fin n × Fin k
abbrev Arc (n k : ℕ) := Cell n k × Fin 4
abbrev Flag (n k : ℕ) := Arc n k × Bool

/-- Coordinates are doubled. The first coordinate is horizontal. -/
def internalSides (n k : ℕ) : Finset Point :=
  ((Finset.range n ×ˢ Finset.range (k - 1)).image
    fun rc => (2 * rc.2 + 2, 2 * rc.1 + 1)) ∪
  ((Finset.range (n - 1) ×ˢ Finset.range k).image
    fun rc => (2 * rc.2 + 1, 2 * rc.1 + 2))

/-- A placement chooses a subset of precisely the internal shared sides. -/
abbrev Placement (n k : ℕ) := ↥(internalSides n k).powerset

/-- N, E, S, W are side indices 0, 1, 2, 3. -/
def side {n k : ℕ} (f : Flag n k) : ℕ :=
  (f.1.2.val + if f.2 then 1 else 0) % 4

/-- Arc indices NE, ES, SW, WN connect consecutive side midpoints. -/
def midpoint {n k : ℕ} (f : Flag n k) : Point :=
  let r := f.1.1.1.val
  let c := f.1.1.2.val
  match side f with
  | 0 => (2 * c + 1, 2 * r)
  | 1 => (2 * c + 2, 2 * r + 1)
  | 2 => (2 * c + 1, 2 * r + 2)
  | _ => (2 * c, 2 * r + 1)

/-- Following one of the four fixed straight segments inside a cell. -/
def alongArc {n k : ℕ} (f g : Flag n k) : Prop :=
  f.1 = g.1 ∧ f.2 ≠ g.2

/-- Reflection pairs ends in the same cell. Transmission pairs collinear ends
in opposite cells; equal arc-index parity means equal diagonal slope. -/
def atSide {n k : ℕ} (p : Placement n k) (f g : Flag n k) : Prop :=
  f ≠ g ∧ midpoint f = midpoint g ∧
    if midpoint f ∉ internalSides n k ∨ midpoint f ∈ p.val then
      f.1.1 = g.1.1
    else
      f.1.1 ≠ g.1.1 ∧ f.1.2.val % 2 = g.1.2.val % 2

/-- A physical curve alternates an internal arc with a reflection/transmission. -/
def connected {n k : ℕ} (p : Placement n k) (f g : Flag n k) : Prop :=
  Relation.EqvGen (fun a b => alongArc a b ∨ atSide p a b) f g

/-- All physical arc ends lie in one nonempty component. -/
def singleLoop {n k : ℕ} (p : Placement n k) : Prop :=
  Nonempty (Flag n k) ∧ ∀ f g, connected p f g

/-- Count labelled subsets of internal sides, without quotienting symmetries
or distinguishing the two directions of traversal. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.card {p : Placement n k // singleLoop p}

/-- OEIS A001353, defined independently of the mirror count. -/
def a001353 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => 4 * a001353 (k + 1) - a001353 k

/-- All three assertions in the site's problem, with their original domains.
The width-four recurrence is written without truncated natural subtraction. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → T 2 k = 4 ^ (k - 1)) ∧
    (∀ k : ℕ, 1 ≤ k → T 3 k = 4 ^ (k - 1) * a001353 k) ∧
    (∀ k : ℕ, 4 ≤ k → T 4 k + 512 * T 4 (k - 2) = 64 * T 4 (k - 1)) := by
  sorry

end OMA.S_oeis_a400778
