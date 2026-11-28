import Mathlib

/-!
# The first sequence without a collinear triple: does each value appear exactly twice?

Source: https://mathoverflow.net/questions/338528
Credit: @jagraj28

Let `u` be the lexicographically first sequence of nonnegative integers `u 0, u 1, …` whose
graph `{(n, u n)}` contains no three collinear points (OEIS A236266:
`0, 0, 1, 1, 4, 3, 8, 2, 2, 5, 7, 4, 5, 8, 16, …`). It is built greedily: `u n` is the least
nonnegative integer `m` such that `(n, m)` is not on a line through two earlier points
`(i, u i)` and `(j, u j)`, `i < j < n`. No value occurs more than twice (three points of the
graph at the same height would be collinear).

The question: does each nonnegative integer appear in the sequence? Exactly two times? It has
no answer. `main` states the strongest form: every nonnegative integer appears exactly twice.

Conventions.
* Indices start at `0`, as in A236266 and in the question's list of terms.
* Three points `(i, a)`, `(j, b)`, `(n, m)` with `i < j < n` are collinear if and only if
  `(b - a) * (n - j) = (m - b) * (j - i)` in `ℤ`; this is the condition used below.
* `u` is defined by well-founded recursion as the infimum of the allowed values. The set of
  allowed values is nonempty (each pair `i < j` forbids at most one value), so the infimum is the
  least allowed value. A computation of the first 70 terms with this definition gives exactly the
  terms of A236266. In the first 600 terms, every value below 40 occurs exactly twice and no value
  occurs three times.
* "Appears exactly twice" is `Set.ncard {n | u n = v} = 2`.
-/

namespace OMA.S_mo_338528

/-- A236266: the greedy sequence with no three collinear points `(n, u n)`. -/
noncomputable def u (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ j (_hj : j < n), ∀ i (_hi : i < j),
    ((u j : ℤ) - u i) * ((n : ℤ) - j) ≠ ((m : ℤ) - u j) * ((j : ℤ) - i)}
termination_by n
decreasing_by all_goals omega

/-- Every nonnegative integer appears exactly twice in the greedy sequence `u`. -/
theorem main : ∀ v : ℕ, Set.ncard {n : ℕ | u n = v} = 2 := by
  sorry

end OMA.S_mo_338528
