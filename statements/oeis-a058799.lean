import Mathlib

/-!
# Partial sums for column two of the frieze A007754

A058799 is the column with zero-based index two. The definition below uses
Henry Bottomley's column recurrence for the whole frieze. For the one-based
sequence A093935, use Amarnath Murthy's defining recurrence, storing the
current term and its sum through that term. Sean A. Irvine conjectured the
partial-sum identity in 2022.

https://oeis.org/A058799 · https://oeis.org/A007754 · https://oeis.org/A093935
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a058799

def frieze (k : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => (k : ℤ) + 1
  | n + 2 => ((n : ℤ) + k + 2) * frieze k (n + 1) - frieze k n

def running : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 =>
    let (term, total) := running n
    let next := term + ((n : ℤ) + 1) * total
    (next, total + next)

theorem main : ∀ n : ℕ, frieze 2 n = ∑ j ∈ Finset.range (n + 1), (running j).1 := by
  sorry

end OMA.S_oeis_a058799
