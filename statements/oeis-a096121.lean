import Mathlib

/-!
# Full-spectrum rook walks on a two-row board

Mikhail Kurkov conjectured that the number of directed walks visiting every
square of a 2 × n board exactly once is twice n! times A102038(n).
Sources: https://oeis.org/A096121 and https://oeis.org/A102038
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a096121

def continuant : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n+2 => (n+1) * continuant (n+1) + continuant n

abbrev StarPositions (slots stars : ℕ) := {s : Finset (Fin slots) // s.card = stars}

/-- A run encoding of a directed full-spectrum rook walk on 2 × (m+1).
Let k be the number of columns without a vertical move, so r = m+1-k ≥ 1
columns carry a switch. Record the starting row. A permutation of the board
columns lists the r switch columns in traversal order, followed by the k
remaining columns in the order visited in the starting row. The permutation
of k records their order in the other row.

The switches delimit r+1 alternating horizontal runs. In each row, cut
its ordered list of k unswitched visits into its successive runs, allowing
empty lists. The two subsets give the star positions in the corresponding
stars-and-bars words. Their lengths are k+⌈(r+1)/2⌉-1 and k+⌊(r+1)/2⌋-1,
respectively. To decode, read each run in order and cross vertically in the
next switch column. Reading the switches and intervening runs of any walk
recovers these data uniquely. -/
abbrev RookWalk (m : ℕ) :=
  Σ k : Fin (m+1), Bool × Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin k.val) ×
    StarPositions ((m+k.val+1)/2) k.val × StarPositions ((m+k.val)/2) k.val

theorem main : ∀ m : ℕ,
    Fintype.card (RookWalk m) = 2 * (m+1).factorial * continuant (m+1) := by
  sorry

end OMA.S_oeis_a096121
