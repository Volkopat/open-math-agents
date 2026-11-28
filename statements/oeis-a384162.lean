import Mathlib

/-!
# Marked runs in words over an n-letter alphabet (OEIS A384162)

A384162(n) counts words of length n over n letters with exactly one position
marked in each maximal constant run. A run of length r offers r choices.
A342168(j) is U_j((j+3)/2), with U the Chebyshev polynomial of the second kind.
Its scaled recurrence below uses the integer argument t=2x. John Tyler Rascoe's
entry conjectures `A384162(n) = n * A342168(n-1)` at every positive index.

Sources: https://oeis.org/A384162 (offset 1), https://oeis.org/A342168 (offset 0).
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a384162

def words (q : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (List.range q).flatMap fun c => (words q k).map (c :: ·)

def markings (w : List ℕ) : ℕ := ((w.splitBy (· == ·)).map List.length).prod

def markedWords (n : ℕ) : ℕ := ((words n n).map markings).sum

/-- `U_j(t/2)` obtained from the Chebyshev recurrence. -/
def scaledU (t : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => t
  | j + 2 => t * scaledU t (j + 1) - scaledU t j

def companion (j : ℕ) : ℤ := scaledU ((j : ℤ) + 3) j

theorem main : ∀ n : ℕ, 1 ≤ n → (markedWords n : ℤ) = (n : ℤ) * companion (n - 1) := by
  sorry

end OMA.S_oeis_a384162
