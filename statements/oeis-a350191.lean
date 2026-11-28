import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Logic.Equiv.Defs

/-!
# Nonattacking rook placements on triangular and hexagonal boards

A350191 counts maximum placements on the triangular board up to rotations
and reflections of the placement. Its side-10 illustration distinguishes this
convention from A350041, which only allows symmetries preserving the triangle.
A309260 uses the twelve symmetries preserving the regular hexagonal board.

Sources: https://oeis.org/A350191, https://oeis.org/A350191/a350191.pdf,
https://oeis.org/A350041, https://oeis.org/A309260
Credit: @wtho704
-/

namespace OMA.S_oeis_a350191

open Finset

abbrev Cell := ℕ × ℕ × ℕ
abbrev Placement := Finset Cell

/-- The three families of parallel rook lines. -/
def line (i : Fin 3) (p : Cell) : ℕ :=
  if i = 0 then p.1 else if i = 1 then p.2.1 else p.2.2

/-- The triangle with d+1 cells along each edge in barycentric coordinates. -/
def triangle (d : ℕ) : Finset Cell :=
  let r := range (d + 1)
  (r ×ˢ (r ×ˢ r)).filter fun p => p.1 + p.2.1 + p.2.2 = d

/-- The regular hexagon of side m+1, centered at (m,m,m). -/
def hexagon (m : ℕ) : Finset Cell :=
  (triangle (3 * m)).filter fun p => ∀ i : Fin 3, line i p ≤ 2 * m

def Nonattacking (s : Placement) : Prop :=
  ∀ i : Fin 3, Set.InjOn (line i) (s : Set Cell)

open Classical in
noncomputable def placements (board : Finset Cell) : Finset Placement :=
  board.powerset.filter Nonattacking

open Classical in
noncomputable def maximumPlacements (family : Finset Placement) : Finset Placement :=
  family.filter fun s => ∀ t ∈ family, t.card ≤ s.card

/-- A lattice isometry permutes the three coordinates and either preserves
all their signs or reverses all three. Its translation is allowed explicitly. -/
def moved (σ : Equiv.Perm (Fin 3)) (flip : Bool) (shift : Fin 3 → ℤ) (p q : Cell) : Prop :=
  ∀ i, (line i q : ℤ) =
    (if flip then -(line (σ i) p : ℤ) else (line (σ i) p : ℤ)) + shift i

def mapsPlacement (s t : Placement) (σ : Equiv.Perm (Fin 3)) (flip : Bool)
    (shift : Fin 3 → ℤ) : Prop :=
  (∀ p ∈ s, ∃ q ∈ t, moved σ flip shift p q) ∧
  (∀ q ∈ t, ∃ p ∈ s, moved σ flip shift p q)

def congruent (s t : Placement) : Prop :=
  ∃ σ flip shift, mapsPlacement s t σ flip shift

/-- Coordinate permutations and simultaneous complementation around the
hexagon's center are the twelve board symmetries. -/
def hexCongruent (m : ℕ) (s t : Placement) : Prop :=
  ∃ σ flip, mapsPlacement s t σ flip (fun _ => if flip then (2 * m : ℕ) else (0 : ℤ))

open Classical in
/-- Each equivalence class is a finite set of placements on the given board. -/
noncomputable def classCount (family : Finset Placement) (r : Placement → Placement → Prop) : ℕ :=
  (family.image fun s => family.filter (r s)).card

noncomputable def triangleCount (n : ℕ) : ℕ :=
  classCount (maximumPlacements (placements (triangle (n - 1)))) congruent

noncomputable def hexCount (n : ℕ) : ℕ :=
  let m := n - 1
  classCount ((placements (hexagon m)).filter fun s => s.card = 2 * m + 1) (hexCongruent m)

theorem main : ∀ n : ℕ, 0 < n → triangleCount (3 * n - 2) = hexCount n := by
  sorry

end OMA.S_oeis_a350191
