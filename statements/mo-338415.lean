import Mathlib

/-!
# MathOverflow 338415: does `1` occur infinitely often in A229037?

Source: https://mathoverflow.net/questions/338415 (CC BY-SA 4.0).

OEIS A229037 (Jack W. Grahl) is the lexicographically first sequence of positive integers
`a(1), a(2), …` with no three terms in arithmetic progression at equally spaced indices:
`a(n+k) - a(n) ≠ a(n+2k) - a(n+k)` for all `n, k ≥ 1`. It begins
`1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 4, 4, 5, 5, 8, …`. Question (due to
Charles R. Greathouse): does the term `1` appear infinitely many times in this sequence? The
post also asks further questions (recurring blocks, variants); we state only this one, and
`main` asserts the affirmative.

Conventions: the constraints on a term involve only earlier terms and exclude finitely many
values, so the lexicographically first sequence is the greedy one: each term is the least
positive integer not completing such a progression with earlier terms. We index from `0`
(`a 0` is the OEIS `a(1)`), which does not affect the question.
-/

namespace OMA.S_mo_338415

/-- A229037, indexed from `0`: `a n` is the least positive `m` such that no `k ≥ 1` with
`2k ≤ n` has `a (n - 2k), a (n - k), m` in arithmetic progression. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ k : Fin (n / 2), (m : ℤ) - a (n - (k + 1)) ≠ (a (n - (k + 1)) : ℤ) - a (n - 2 * (k + 1))}
decreasing_by all_goals omega

theorem main : {n : ℕ | a n = 1}.Infinite := by
  sorry

end OMA.S_mo_338415
