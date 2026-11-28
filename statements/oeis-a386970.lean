import Mathlib

/-!
# OEIS A386970: Period of Langton's ant on an `n × 3` torus

Source: https://oeis.org/A386970 (OEIS Foundation, CC BY-SA 4.0).
Langton's ant moves on a toroidal grid `ZMod W × ZMod 3`, starting at `(0, 0)` on an all-white
(`false`) grid facing along the 3-cell axis (`dir = 1`). At each step, on a white (`false`) cell
the ant turns 90 degrees right (`+1 mod 4`), flips the cell to black (`true`), and advances one
cell; on a black (`true`) cell it turns 90 degrees left (`+3 mod 4`), flips the cell to white
(`false`), and advances one cell.

Conjecture (OEIS A386970):
For every `n ≥ 2`, the period of Langton's ant on a `(3*n + 1) × 3` torus is `96*n + 16`.
-/

namespace OMA.S_oeis_a386970

/-- State of Langton's ant on a `W × 3` torus.
Directions `dir : Fin 4` are `0 = East (+x)`, `1 = South (+y)`, `2 = West (-x)`, `3 = North (-y)`. -/
structure AntState (W : ℕ) where
  x : ZMod W
  y : ZMod 3
  dir : Fin 4
  grid : ZMod W → ZMod 3 → Bool

/-- Horizontal displacement for direction `d : Fin 4`. -/
def dx (W : ℕ) (d : Fin 4) : ZMod W :=
  match d.val with
  | 0 => 1
  | 2 => -1
  | _ => 0

/-- Vertical displacement for direction `d : Fin 4`. -/
def dy (d : Fin 4) : ZMod 3 :=
  match d.val with
  | 1 => 1
  | 3 => -1
  | _ => 0

/-- One step of Langton's ant on a `W × 3` torus. -/
def antStep {W : ℕ} (s : AntState W) : AntState W :=
  let c := s.grid s.x s.y
  let d' : Fin 4 := if c then s.dir + 3 else s.dir + 1
  let g' : ZMod W → ZMod 3 → Bool :=
    fun a b => if a = s.x ∧ b = s.y then !c else s.grid a b
  { x := s.x + dx W d'
    y := s.y + dy d'
    dir := d'
    grid := g' }

/-- Initial state on a `W × 3` torus: ant at `(0, 0)` facing South (`dir = 1`) on an all-white grid. -/
def initState (W : ℕ) : AntState W :=
  { x := 0
    y := 0
    dir := 1
    grid := fun _ _ => false }

/-- `p` is the minimal positive period of Langton's ant on a `W × 3` torus starting from `initState W`. -/
def IsPeriod (W p : ℕ) : Prop :=
  0 < p ∧
  antStep^[p] (initState W) = initState W ∧
  ∀ t : ℕ, 0 < t → t < p → antStep^[t] (initState W) ≠ initState W

/-- Conjecture (OEIS A386970):
For every `n ≥ 2`, the period of Langton's ant on a `(3*n + 1) × 3` torus is `96*n + 16`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n → IsPeriod (3 * n + 1) (96 * n + 16) := by
  sorry

end OMA.S_oeis_a386970
