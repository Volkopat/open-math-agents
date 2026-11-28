import Mathlib

/-!
# A033810: Birthday problem

Source: https://oeis.org/A033810
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of people needed so that the probability of at least two sharing a birthday
out of `n` equally likely days is at least `50%` (offset `1`). The formula
`a(n) = ⌈√(2n log 2) + (3 - 2 log 2)/6 + (9 - 4 (log 2)²)/(72 √(2n log 2)) - 2 (log 2)²/(135 n)⌉`
is known for `n ≤ 10¹⁸` and conjectured to hold for all `n`.

## Encoding

* With `k` people, the probability that all birthdays differ is `∏_{i<k} (n - i)/n`; `a n` is the
  least `k` with `1 - ∏_{i<k} (n - i)/n ≥ 1/2` (computed in `ℝ`; for `k > n` the product is `0`).
* `log` is the natural logarithm; `main` states the formula for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a033810

/-- Probability that `k` people have pairwise distinct birthdays among `n` days. -/
noncomputable def pDistinct (n k : ℕ) : ℝ := ∏ i ∈ Finset.range k, ((n : ℝ) - i) / n

/-- `a n`: the least number of people for which a shared birthday has probability `≥ 1/2`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 / 2 ≤ 1 - pDistinct n k}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = ⌈Real.sqrt (2 * n * Real.log 2) + (3 - 2 * Real.log 2) / 6 +
        (9 - 4 * Real.log 2 ^ 2) / (72 * Real.sqrt (2 * n * Real.log 2)) -
        2 * Real.log 2 ^ 2 / (135 * n)⌉ := by
  sorry

end OMA.S_oeis_a033810
