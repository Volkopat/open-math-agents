import Mathlib

/-!
# A005943: Factor complexity (number of subwords of length n) of the Golay-Rudin-Shapiro binary word A020987.

Source: https://oeis.org/A005943
Credit: @Aijy0264561

The entry's conjecture is Joerg Arndt's generating function (Jun 10 2012)
`(1 + x^2 + 2x^3 + 4x^4 + 4x^6 - 2x^7 - 2x^9) / (1 - x)^2`.

Conventions:
* `grs n` is A020987(n), the zero-one Golay-Rudin-Shapiro word: the parity of the number of
  (possibly overlapping) occurrences of the block `11` in the binary expansion of `n`, i.e. of the
  number of positions `i` with bits `i` and `i + 1` of `n` both set. Every set bit of `n` has
  index below `n`, so it suffices to look at `i < n`. This gives
  `0,0,0,1,0,0,1,0,0,0,0,1,1,1,0,1,...`, the data of A020987 (offset 0).
* A subword (factor) of length `n` is a block `grs i, grs (i+1), …, grs (i+n-1)` of consecutive
  letters, recorded as a function `Fin n → ℕ`; `a n` is the number of distinct such blocks
  (offset 0, with the empty word counted once: `a 0 = 1`).
* Expanding the generating function: the numerator coefficients have first partial sums
  `1,1,2,4,8,8,12,10,10,8,8,8,…` (constantly `8` from the ninth on), and second partial sums
  `1,2,4,8,16,24,36,46,56,64,72,…`. So the generating function says exactly that `a 0, …, a 7`
  are `1,2,4,8,16,24,36,46` and `a n = 8n - 8` for every `n ≥ 8`; the statement below is this
  coefficientwise form.
-/

namespace OMA.S_oeis_a005943

/-- A020987: the parity of the number of blocks `11` in the binary expansion of `n`. -/
def grs (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => n.testBit i = true ∧ n.testBit (i + 1) = true).card % 2

/-- A005943(n): the number of distinct subwords of length `n` of the word `grs`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (Set.range fun i : ℕ => fun j : Fin n => grs (i + j)).ncard

/-- Arndt's conjectured generating function, coefficient by coefficient. -/
theorem main :
    (a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 8 ∧ a 4 = 16 ∧ a 5 = 24 ∧ a 6 = 36 ∧ a 7 = 46) ∧
      ∀ n : ℕ, 8 ≤ n → a n = 8 * n - 8 := by
  sorry

end OMA.S_oeis_a005943
