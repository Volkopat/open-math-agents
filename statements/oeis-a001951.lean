import Mathlib

/-!
# A001951: A Beatty sequence: a(n) = floor(n*sqrt(2)).

Source: https://oeis.org/A001951
Credit: @ShoQo

It appears that the distance between the a(n)-th triangular number and the nearest square is
not greater than floor(a(n)/2). - Ralf Stephan, Sep 14 2013
(Sela Fried, 2025: Stephan's conjecture is true.)

Formalization notes:
* Offset 0: `a n = ⌊n √2⌋`.
* The m-th triangular number is `m (m+1) / 2` (exact division).
* "The distance to the nearest square is at most B" is stated as: some square `k^2` is within
  distance B (the nearest square is then within B as well).
-/

namespace OMA.S_oeis_a001951

/-- a(n) = floor(n * sqrt(2)). -/
noncomputable def a (n : ℕ) : ℕ := ⌊(n : ℝ) * Real.sqrt 2⌋₊

theorem main : ∀ n : ℕ, ∃ k : ℕ,
    |((a n * (a n + 1) / 2 : ℕ) : ℤ) - (k : ℤ) ^ 2| ≤ ((a n / 2 : ℕ) : ℤ) := by
  sorry

end OMA.S_oeis_a001951
