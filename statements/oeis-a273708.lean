import Mathlib

/-!
# A273708: Number of active cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 873, based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273708 (OEIS Foundation, CC BY-SA 4.0).
Conjecture: Lars Blomberg, Jul 24 2016.
Formalization: @longling12 (drafted with AI assistance)

A board stores the entire central square at the current stage, together with the
common state outside it. The square grows by one cell on all four sides per step.
The exterior updates by the same outer totalistic rule, with four equal neighbors.
The count covers the square of side 2t+1 at t = 2^n-1. The initial index is zero.
-/

namespace OMA.S_oeis_a273708

def bit (rule : ℕ) (c l r d u : Bool) : Bool :=
  rule.testBit (c.toNat + 2 * (l.toNat + r.toNat + d.toNat + u.toNat))

def background (rule : ℕ) : ℕ → Bool
  | 0 => false
  | t+1 => rule.testBit (9 * (background rule t).toNat)

abbrev Grid (t : ℕ) := Vector (Vector Bool (2*t+1)) (2*t+1)

def fill (t : ℕ) (f : ℤ → ℤ → Bool) : Grid t :=
  Vector.ofFn fun j => Vector.ofFn fun i => f ((i.val : ℤ) - t) ((j.val : ℤ) - t)

def cell (t : ℕ) (exterior : Bool) (rows : Grid t) (x y : ℤ) : Bool :=
  if h : -(t : ℤ) ≤ x ∧ x ≤ t ∧ -(t : ℤ) ≤ y ∧ y ≤ t then
    rows[(y+t).toNat]'(by omega) |>.get ⟨(x+t).toNat, by omega⟩
  else exterior

def board (rule : ℕ) : (t : ℕ) → Grid t
  | 0 => fill 0 fun x y => decide (x = 0 ∧ y = 0)
  | t+1 =>
    let rows := board rule t
    let b := cell t (background rule t) rows
    fill (t+1) fun x y => bit rule (b x y) (b (x-1) y) (b (x+1) y) (b x (y-1)) (b x (y+1))

def stage (rule t : ℕ) : ℤ → ℤ → Bool := cell t (background rule t) (board rule t)

def total (t : ℕ) (bg : Bool) (rows : Grid t) : ℕ :=
  ∑ j ∈ Finset.range (2*t+1), ∑ i ∈ Finset.range (2*t+1),
    (cell t bg rows ((i : ℤ)-t) ((j : ℤ)-t)).toNat

def sampled (rule n : ℕ) : ℕ :=
  let t := 2^n-1
  total t (background rule t) (board rule t)

def a (n : ℕ) : ℕ := sampled 873 n

theorem main : ∀ n : ℕ, a n = sampled 889 n := by
  sorry

end OMA.S_oeis_a273708
