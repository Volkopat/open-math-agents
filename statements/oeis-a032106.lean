import Mathlib

/-!
# Black-and-white strings counted up to reversal

A string in A032106 has `n` black beads and `n-1` white beads. Its two halves
are indexed outward from the center, so reversing the string exchanges their
black-position sets. The third set marks whether the center is black. A strict
lexicographic comparison selects one orientation of each nonpalindromic string.
The OEIS entry counts the single black bead at index one.

The parity formulas are those of Stephan's conjecture 74, as proved by
Elizabeth Wilmer in Proposition 3 of her notes.

Sources: https://oeis.org/A032106 (OEIS Foundation, CC BY-SA 4.0),
https://arxiv.org/abs/math/0409509 and https://oeis.org/A032106/a032106.pdf.
Credit: @connoranderson
-/

namespace OMA.S_oeis_a032106

abbrev Word (n : ℕ) := Finset (Fin (n-1)) × Finset (Fin (n-1)) × Finset Unit

def blackCount {n : ℕ} (w : Word n) : ℕ := w.1.card + w.2.1.card + w.2.2.card

def halfKey {m : ℕ} (s : Finset (Fin m)) : List Bool :=
  List.ofFn fun i : Fin m => decide (i ∈ s)

def words (n : ℕ) : Finset (Word n) := Finset.univ.filter fun w : Word n => blackCount (n:=n) w = n

def beadCount (n : ℕ) : ℕ :=
  ((words n).filter fun w => n=1 ∨ halfKey w.1 < halfKey w.2.1).card

theorem main : beadCount 1 = 1 ∧ ∀ n : ℕ, 1 < n → beadCount n =
    if Even n then ((2*n).choose n - n.choose (n/2))/4
    else ((2*n-1).choose (n-1) - (n-1).choose ((n-1)/2))/2 := by
  sorry

end OMA.S_oeis_a032106
