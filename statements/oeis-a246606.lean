import Mathlib

/-!
# Central entries of the factorial difference triangle (OEIS A246606)

Source: https://oeis.org/A246606. Triangle and indexing: https://oeis.org/A116853.
R. J. Mathar conjectured this recurrence on 1 July 2022.

The central entry in row `2n-1` of the displayed one-based triangle is the
`(n-1)`st forward difference of the factorial function at `n`. The sequence
starts at one. At `n=2` the coefficient multiplying its index-zero extension vanishes.
-/

namespace OMA.S_oeis_a246606

/-- `diff k t` is the `k`th forward difference of factorial at `t`. -/
def diff : ℕ → ℕ → ℤ
  | 0, t => t.factorial
  | k + 1, t => diff k (t + 1) - diff k t

/-- Central terms of A116853, extended by zero at the unused index zero. -/
def a : ℕ → ℤ
  | 0 => 0
  | k + 1 => diff k (k + 1)

theorem main : ∀ k : ℕ, let n : ℤ := (k : ℤ) + 2
    (-2*n + 3) * a (k+2) + 4*(n-1)*(2*n^2 - 4*n + 1) * a (k+1) +
    (n-1)*(n-2)*(2*n-1) * a k = 0 := by
  sorry

end OMA.S_oeis_a246606
