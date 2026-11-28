import Mathlib

/-!
# Minimum size of a universal container for fixed polyominoes

Peter Exley's conjecture, OEIS A395495.
Source: https://oeis.org/A395495
Credit: @VestigeClub

A cell is indexed by its integer coordinates. Connectivity uses shared sides
and permits holes. A single translation must place every cell of each piece
in the container. Every orientation of a piece is quantified over.
-/

namespace OMA.S_oeis_a395495

abbrev Cell := ℤ × ℤ

def squareGrid : SimpleGraph Cell where
  Adj p q := |p.1 - q.1| + |p.2 - q.2| = 1
  symm := ⟨fun p q h => by
    rw [abs_sub_comm q.1 p.1, abs_sub_comm q.2 p.2]
    exact h⟩
  loopless := ⟨fun p => by simp⟩

def Polyomino (cells : Finset Cell) : Prop :=
  (squareGrid.induce (cells : Set Cell)).Connected

def Universal (n : ℕ) (container : Finset Cell) : Prop :=
  Polyomino container ∧ ∀ piece : Finset Cell, piece.card = n → Polyomino piece →
    ∃ shift : Cell, ∀ p ∈ piece, p + shift ∈ container

theorem main : ∀ n : ℕ, 1 ≤ n →
    IsLeast {k : ℕ | ∃ container : Finset Cell, Universal n container ∧ container.card = k}
      (if n ≤ 3 then 2 * n - 1 else n * (n - 1) / 2 + 3) := by
  sorry

end OMA.S_oeis_a395495
