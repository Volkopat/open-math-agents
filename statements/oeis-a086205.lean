import Mathlib

/-!
# OEIS A086205: determinant of the `n × n` matrix `M(i,j) = binomial(i², j)`

Source: https://oeis.org/A086205
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n) = det (binomial(i², j))_{1 ≤ i, j ≤ n}`, offset 0 (`1, 1, 6, 360, 302400, …`); the entry's
PARI program is `matdet(matrix(n,n,i,j,binomial(i^2,j)))`, with indices from 1.

The entry (Peter Bala, Feb 19 2023) adds: "Conjecture: a(n) = the determinant of the n X n matrix
( binomial(i^2 + z, j) ) for arbitrary complex z." This file states that conjecture.

Reading of the conjecture (the source does not give the index range of the second matrix):
* With the indices of the definition, `1 ≤ i, j ≤ n`, the claim is false already for `n = 1`: the
  determinant is `binomial(1 + z, 1) = 1 + z`. So the conjecture cannot use that range.
* With indices from `0`, `0 ≤ i, j ≤ n`, the matrix has the row `i = 0` equal to
  `binomial(z, j)`, and at `z = 0` that row is `(1, 0, …, 0)`, so the determinant at `z = 0` is
  exactly `a(n)`. This is the reading stated here: for every complex `z`,
  `det (binomial(i² + z, j))_{0 ≤ i, j ≤ n} = a(n)`.
  (Equivalently, the `n × n` matrix with indices `0 ≤ i, j ≤ n - 1` has determinant `a(n - 1)`.)
* A computation with exact rationals confirms that this reading holds for `n < 7` at more values
  of `z` than the degree in `z` of the determinant, so it holds identically in `z` for those `n`.

Conventions:
* For a complex `x`, `binomial(x, j)` is the generalized binomial coefficient
  `x (x - 1) ⋯ (x - j + 1) / j!`, written with Mathlib's `descPochhammer`.
* `a(n)` is defined with Mathlib's `Nat.choose` and `Matrix.det`, over `ℤ`.
-/

namespace OMA.S_oeis_a086205

/-- The generalized binomial coefficient `binomial(x, j) = x (x - 1) ⋯ (x - j + 1) / j!`. -/
noncomputable def gchoose (x : ℂ) (j : ℕ) : ℂ :=
  (descPochhammer ℂ j).eval x / (j.factorial : ℂ)

/-- `A086205(n)`: the determinant of the `n × n` matrix `(binomial(i², j))_{1 ≤ i, j ≤ n}`. -/
def a (n : ℕ) : ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n => (((i.val + 1) ^ 2).choose (j.val + 1) : ℤ))

/-- Conjecture (Bala): for every complex `z`, the determinant of
`(binomial(i² + z, j))_{0 ≤ i, j ≤ n}` is `a(n)`. -/
theorem main :
    ∀ (n : ℕ) (z : ℂ),
      Matrix.det (Matrix.of fun i j : Fin (n + 1) => gchoose ((i.val : ℂ) ^ 2 + z) j.val)
        = (a n : ℂ) := by
  sorry

end OMA.S_oeis_a086205
