import Mathlib

/-!
# A394957: rows of Pascal's triangle whose pairwise sumset is not maximal

Source: https://oeis.org/A394957
Credit: @jagraj28

For a row `n` of Pascal's triangle, the distinct binomial coefficients are `C(n, i)` for
`0 ≤ i ≤ ⌊n/2⌋`. Their pairwise sumset `{C(n, i) + C(n, j) : 0 ≤ i ≤ j ≤ ⌊n/2⌋}` has at most
`C(⌊n/2⌋ + 2, 2)` elements (the number of pairs `i ≤ j`); it is *maximal* when it has exactly that
many elements. A394957 lists the `n` for which the sumset is not maximal
(`6, 7, 12, 13, 14, 19, 21, 22, 23, 32, …`) and records:

  Conjecture: the sequence is `{6, 7, 19, 52} ∪ {d² - 4, d² - 3, d² - 2 : d ≥ 4}`.

(The comments of the entry give the defect formula with `0 ≤ i ≤ j ≤ ⌊n/2⌋`, so the sumset
includes the doubles `2 C(n, i)`.) A computation for all `n ≤ 400` confirms the conjecture; the
entry reports a search up to `n ≤ 1000`.

Conventions.
* `n` ranges over all natural numbers (the entry's terms start at `6`; small rows are maximal).
* `sumset n` is the `Finset` image of the pairs `(i, j)` with `i ≤ j ≤ n / 2` under
  `C(n, i) + C(n, j)`; non-maximal means `(sumset n).card < C(n / 2 + 2, 2)`.
-/

namespace OMA.S_oeis_a394957

/-- The pairwise sumset `{C(n, i) + C(n, j) : 0 ≤ i ≤ j ≤ ⌊n/2⌋}`. -/
def sumset (n : ℕ) : Finset ℕ :=
  (((Finset.range (n / 2 + 1)) ×ˢ (Finset.range (n / 2 + 1))).filter fun ij => ij.1 ≤ ij.2).image
    fun ij => n.choose ij.1 + n.choose ij.2

/-- Conjecture in OEIS A394957: the pairwise sumset of row `n` is not maximal exactly for
`n ∈ {6, 7, 19, 52}` and `n = d² - 4, d² - 3, d² - 2` with `d ≥ 4`. -/
theorem main : ∀ n : ℕ, (sumset n).card < (n / 2 + 2).choose 2 ↔
    (n = 6 ∨ n = 7 ∨ n = 19 ∨ n = 52 ∨
      ∃ d : ℕ, 4 ≤ d ∧ (n + 4 = d ^ 2 ∨ n + 3 = d ^ 2 ∨ n + 2 = d ^ 2)) := by
  sorry

end OMA.S_oeis_a394957
