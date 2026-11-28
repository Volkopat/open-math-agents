import Mathlib

/-!
# A177258: Number of derangements of {1,2,...,n} having no adjacent transpositions.

Source: https://oeis.org/A177258
Credit: @Drogobo

`a n` is the number of permutations `σ` of `{1, ..., n}` (here `Fin n = {0, ..., n - 1}`, which
changes nothing) that are derangements (no fixed point) and whose cycle decomposition contains no
adjacent transposition, i.e. no 2-cycle `(i, i + 1)`: there is no `i` with `σ i = i + 1` and
`σ (i + 1) = i`. The sequence starts `1, 0, 0, 2, 7, 36, 225, 1610, ...` (`a 0 = 1` counts the
empty permutation).

The OEIS entry records the conjecture (R. J. Mathar, Jul 26 2022) that the sequence is D-finite
with the recurrence `a(n) = (n-1)*a(n-1) + (n-1)*a(n-2) + (n-1)*a(n-3) + a(n-4)`. The recurrence
involves `a(n - 4)`, so it is stated for `n ≥ 4`.
-/

namespace OMA.S_oeis_a177258

/-- The number of derangements of `Fin n` with no adjacent transposition `(i, i + 1)` in their
cycle decomposition. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    (∀ i, σ i ≠ i) ∧ ∀ i j : Fin n, (j : ℕ) = i + 1 → ¬ (σ i = j ∧ σ j = i)).card

/-- Mathar's conjectured recurrence for A177258. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n = (n - 1) * a (n - 1) + (n - 1) * a (n - 2) + (n - 1) * a (n - 3) + a (n - 4) := by
  sorry

end OMA.S_oeis_a177258
