import Mathlib

/-!
# Do any Taxicab(5, 2, n) exist for n > 1?

Source: https://en.wikipedia.org/wiki/Generalized_taxicab_number
Credit: @Andyi955

The generalized taxicab number `Taxicab(k, j, n)` is the smallest number — if it exists — that can
be expressed as the sum of `j` numbers to the `k`th positive power in `n` different ways
(Wikipedia, Generalized taxicab number). The question is whether `Taxicab(5, 2, n)` exists for
some `n > 1`, i.e. whether some positive integer is a sum of two positive fifth powers in two
different ways. No example is known, so this is open.

## Encoding

* A representation as a sum of `j = 2` positive `k = 5`-th powers is a pair `(a, b)` of positive
  integers with sum `a ^ 5 + b ^ 5`. Each representation is put in increasing order, `a ≤ b`, so
  that a pair and its reverse are the same representation.
* Two different ways means the ordered-increasing pairs are different, `(a, b) ≠ (c, d)`; a
  solution with more than two representations also contains two, so `n > 1` is exactly this
  existential statement.
* `Taxicab(5, 2, n)` itself is the smallest such number; the question asked is only whether one
  exists, so the statement is the existential form and no minimisation is needed.
-/

namespace OMA.S_wp_do_any_taxicab_5_2_n_exist_for_n_1

/-- **Taxicab(5, 2, n) for n > 1**: some integer is a sum of two positive fifth powers in two
different ways. -/
theorem main : ∃ a b c d : ℕ,
    0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧ (a, b) ≠ (c, d) ∧ a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5 := by
  sorry

end OMA.S_wp_do_any_taxicab_5_2_n_exist_for_n_1
