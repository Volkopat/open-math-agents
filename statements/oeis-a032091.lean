import Mathlib

/-!
# Four black beads in a string counted up to reversal

Index both halves of a word outward from the center. The pair of black-position
sets therefore switches under reversal. The last set describes the central
position when the word has odd length. A strict lexicographic comparison selects
one representative of each nonpalindromic reversal class.

Stephan's conjecture 73 concerns words of length `n-1` with four black beads.
We give the polynomial formulas with the corrected parities in Elizabeth
Wilmer's Proposition 2, over the published sequence's range beginning at six.

Source: https://oeis.org/A032091 (OEIS Foundation, CC BY-SA 4.0)
References: https://arxiv.org/abs/math/0409509 and https://oeis.org/A032091/a032091.pdf
Credit: @connoranderson
-/

namespace OMA.S_oeis_a032091

abbrev Word (l : ℕ) := Finset (Fin (l/2)) × Finset (Fin (l/2)) × Finset (Fin (l%2))

def blackCount {l : ℕ} (w : Word l) : ℕ := w.1.card + w.2.1.card + w.2.2.card

def halfKey {m : ℕ} (s : Finset (Fin m)) : List Bool :=
  List.ofFn fun i : Fin m => decide (i ∈ s)

def words (l : ℕ) : Finset (Word l) := Finset.univ.filter fun w : Word l => blackCount (l:=l) w = 4

def beadCount (n : ℕ) : ℕ :=
  ((words (n-1)).filter fun w => halfKey w.1 < halfKey w.2.1).card

theorem main : ∀ n : ℕ, 6 ≤ n → (beadCount n : ℚ) =
    if Even n then ((n:ℚ)^4 - 10*n^3 + 32*n^2 - 32*n)/48
    else ((n:ℚ)^4 - 10*n^3 + 32*n^2 - 38*n + 15)/48 := by
  sorry

end OMA.S_oeis_a032091
