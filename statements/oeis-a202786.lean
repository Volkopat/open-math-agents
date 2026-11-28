import Mathlib

/-!
# OEIS A202786: number of `4 × 4` arrays over `0..n` with row and column sums equal

Source: https://oeis.org/A202786
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `4 × 4` arrays with entries in `0..n` whose row sums and column sums are
all equal, offset 0 (`1, 140, 5673, 89520, 790425, …`).

The entry (Robert Israel, May 03 2019): "Conjecture: a(n) = (29 + 3*(-1)^n)/32 + (34/7)*n +
(7202/525)*n^2 + (4658/189)*n^3 + (118873/3780)*n^4 + (5321/180)*n^5 + (36827/1800)*n^6 +
(1285/126)*n^7 + (17581/5040)*n^8 + (2789/3780)*n^9 + (2789/37800)*n^10." This file states that
conjecture, for every `n ≥ 0`.

Conventions:
* An array is a function `M : Fin 4 → Fin 4 → ℕ` with every entry `≤ n`. "Row and column sums
  equal" means that the eight sums (four row sums, four column sums) are all the same number; this
  is the reading of the entry's own comment (Israel), which describes `a(n)` as the lattice points of
  `n C` for the polytope with every row sum and every column sum equal to the first column sum.
  It is stated as: every row sum and every column sum equals the sum of row `0`.
* The count is the `Set.ncard` of the (finite) set of such arrays. A brute-force count with these
  conventions reproduces the first six terms of the entry, and the conjectured formula reproduces
  all twenty-four terms of its data.
* The formula is stated in `ℚ`.
-/

namespace OMA.S_oeis_a202786

/-- `A202786(n)`: `4 × 4` arrays over `0..n` whose row sums and column sums are all equal. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {M : Fin 4 → Fin 4 → ℕ |
    (∀ i j, M i j ≤ n) ∧
      (∀ i, ∑ j, M i j = ∑ j, M 0 j) ∧ (∀ j, ∑ i, M i j = ∑ k, M 0 k)}

/-- Conjecture (Israel): the quasi-polynomial formula for `a(n)`. -/
theorem main :
    ∀ n : ℕ, (a n : ℚ) =
      (29 + 3 * (-1) ^ n) / 32 + 34 / 7 * n + 7202 / 525 * n ^ 2 + 4658 / 189 * n ^ 3
        + 118873 / 3780 * n ^ 4 + 5321 / 180 * n ^ 5 + 36827 / 1800 * n ^ 6
        + 1285 / 126 * n ^ 7 + 17581 / 5040 * n ^ 8 + 2789 / 3780 * n ^ 9
        + 2789 / 37800 * n ^ 10 := by
  sorry

end OMA.S_oeis_a202786
