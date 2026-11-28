import FormalConjectures.OEIS.«110854»

-- Reduction OeisA110854.conjecture.R1 of Conjectures associated with A110854
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The absolute values of A110854: the checked values and the open tail

With `p k` the `k`-th prime, `a n = p (2n + 2) - p (2n + 1) - p (2n) + p (2n - 1)`, a second
difference of consecutive primes that measures the irregularity of the pair of gaps around `p (2n)`.
The conjecture says that `|a n|` takes every value of A004275, that is `1` together with all the
nonnegative even numbers.

Each value is decided by finitely many terms, but nothing rules out a small value such as `34` being
skipped forever: the primes are compared only through the local pattern of two consecutive gaps, and
prime gaps are famously irregular at every scale, so the question is genuinely open.

The OEIS entry A110854 publishes the table of `a n` for `n = 1..1000` (Harvey P. Dale, 2020; the
current entry also shows the first 88 terms). Computing that table from the primes up to `2 * 10 ^ 5`
gives terms `1, 0, 0, 4, 0, -4, 4, -4, 2, 2, …` as listed, and over the `1000` terms the absolute
values cover `1` and every even number up to `32`, while `34` does not occur (the same holds for
`38` and all larger even numbers up to `58`). So the target splits at `32`:

* `H1` (checked values): every `d ≤ 32` that is `1` or even occurs as `|a n|`. Finite: `1000` terms.
* `H2` (the open tail): every even `d > 32` occurs. Nothing is known here; `34` is the first value
  that the table misses, and `1` is the only odd value ever attained as far as the table goes.

`H1` also contains the trivial value `d = 0`, which occurs at `n = 2` (`a 2 = 0`). Neither hypothesis
mentions the target, the other one, or `main`; `main` is the case split at `32`.
-/

namespace OMA.R_OeisA110854_conjecture_R1

/-- The checked values: every `d ≤ 32` that is `1` or even occurs as `|a n|` (table of `1000` terms). -/
def H1 : Prop :=
  ∀ d : ℕ, d ≤ 32 → (d = 1 ∨ Even d) →
    ∃ n : ℕ, 0 < n ∧ d = (OeisA110854.a n).natAbs

/-- The open tail: every even `d > 32` occurs; `34` is the first value the table misses. -/
def H2 : Prop :=
  ∀ d : ℕ, 32 < d → (d = 1 ∨ Even d) →
    ∃ n : ℕ, 0 < n ∧ d = (OeisA110854.a n).natAbs

theorem main : H1 → H2 → type_of% @OeisA110854.conjecture := by
  intro h1 h2 d hd
  by_cases h : d ≤ 32
  · exact h1 d h hd
  · exact h2 d (Nat.lt_of_not_le h) hd

end OMA.R_OeisA110854_conjecture_R1
