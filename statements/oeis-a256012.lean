import Mathlib

/-!
# A256012: Number of partitions of n into distinct parts that are not squarefree.

Source: https://oeis.org/A256012
Credit: @ceejcake

Conjecture (OEIS A256012, unsigned comment in the entry by Reinhard Zumkeller, Jun 01 2015):
`a(n) > 0` for `n > 23`.

Formalization notes:
* The sequence has offset `0` (`n : ℕ`).
* A partition of `n` into distinct parts is the same as a finite set `s` of positive integers
  with `∑ k ∈ s, k = n`. Every part of such a partition lies in `[1, n]`, so it suffices to
  range over subsets of `Finset.Icc 1 n`; nothing is lost.
* A part is required to be not squarefree, i.e. `¬ Squarefree k` (Mathlib's `Squarefree`).
  Parts are positive by construction (`k ∈ Finset.Icc 1 n`), so the nonsquarefree number `0`
  never appears as a part.
* For `n = 0` the only such set is the empty set, so `a 0 = 1`.
* The definition is computable. Initial values for `n = 0, 1, ..., 25`:
  `a(n) = 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 2, 1, 0, 0, 2, 1, 1, 0, 3, 2, 1, 0, 4, 3`,
  so `a 23 = 0` and the bound in the conjecture is sharp.
-/

namespace OMA.S_oeis_a256012

/-- `a n` is the number of partitions of `n` into distinct parts that are not squarefree,
counted as finite sets of positive integers, none squarefree, whose sum is `n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter
    fun s => (∀ k ∈ s, ¬ Squarefree k) ∧ ∑ k ∈ s, k = n).card

/-- OEIS A256012 conjecture: `a n > 0` for every `n > 23`. -/
theorem main : ∀ n : ℕ, 23 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a256012
