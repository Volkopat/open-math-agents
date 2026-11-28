import Mathlib

/-!
# A215229. Circular squarefree words of length six

Source: https://oeis.org/A215229
Credit: @etaubman

R. H. Hardin defines the sequence on the alphabet 0 through k. We count
labeled words by their equality pattern. Number the distinct letters in
order of first appearance starting at zero. The next symbol of the pattern
is either a previously used number or the next fresh number. Conversely,
given a pattern with j numbers, an ordered choice of j distinct letters
from the alphabet reconstructs exactly one word, and the circular square
test is unchanged. This gives a counting algorithm for every alphabet
size, independent of the empirical polynomial and of Colin Barker's
2018 generating-function and recurrence conjectures.
-/

namespace OMA.S_oeis_a215229

/-- No circular square with starting position s and half-length 1 through 5. -/
def squarefree (w : List ℕ) : Bool :=
  (List.range 6).all fun s =>
    (List.range 5).all fun t =>
      (List.range (t+1)).any fun j =>
        w[(s+j)%6]? != w[(s+t+1+j)%6]?

/-- A215229, directly as the cardinality of circular squarefree words on the
alphabet 0 through k, with their six positions distinguished. -/
noncomputable def total (k : ℕ) : ℤ :=
  (Nat.card {w : List ℕ // w.length = 6 ∧ (∀ c ∈ w, c < k+1) ∧ squarefree w = true} : ℤ)

open PowerSeries

theorem main :
    (∀ k : ℕ, total k = (k:ℤ)^6 - 6*(k:ℤ)^4 + 5*(k:ℤ)^3 + 5*(k:ℤ)^2 - 5*k) ∧
    (∀ k : ℕ, total (k+7) = 7*total (k+6) - 21*total (k+5) + 35*total (k+4) -
        35*total (k+3) + 21*total (k+2) - 7*total (k+1) + total k) ∧
    (1-X)^7 * mk total = (6*X^2*(3+47*X+77*X^2-7*X^3) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a215229
