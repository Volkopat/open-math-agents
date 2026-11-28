import Mathlib

/-!
# A335898: a(n) = a(floor((n-1)/a(n-1))) + a(floor((n-2)/a(n-2))) with a(1) = a(2) = 1.

Source: https://oeis.org/A335898
Credit: @eltociear

`a(1) = a(2) = 1` and `a(n) = a(⌊(n-1)/a(n-1)⌋) + a(⌊(n-2)/a(n-2)⌋)` for `n ≥ 3`
(`1, 1, 2, 2, 2, 2, 3, 3, 2, 3, ...`). The entry conjectures:

  This sequence hits every positive integer.

`main` states that every `v ≥ 1` equals `a(n)` for some `n ≥ 1`.

The recursion refers back to terms at data-dependent indices, so the sequence is built as a
list of its first terms: `pref k` lists `a(0), a(1), …, a(k+2)` (with a placeholder `a(0) = 0`,
never used: every term is positive, so `⌊(n-1)/a(n-1)⌋` and `⌊(n-2)/a(n-2)⌋` lie in `[1, n-1]`;
a direct computation of the first `2·10^6` terms confirms the indices never reach `0`, and that
it reproduces the data).
-/

namespace OMA.S_oeis_a335898

/-- `pref k` is the list `[a 0, a 1, …, a (k + 2)]`, with the placeholder `a 0 = 0`. -/
def pref : ℕ → List ℕ
  | 0 => [0, 1, 1]
  | k + 1 =>
    let l := pref k
    let n := l.length
    l ++ [l.getD ((n - 1) / l.getD (n - 1) 0) 0 + l.getD ((n - 2) / l.getD (n - 2) 0) 0]

/-- OEIS A335898. -/
def a (n : ℕ) : ℕ := (pref n).getD n 0

/-- The conjecture in OEIS A335898: every positive integer is a term. -/
theorem main : ∀ v : ℕ, 1 ≤ v → ∃ n : ℕ, 1 ≤ n ∧ a n = v := by
  sorry

end OMA.S_oeis_a335898
