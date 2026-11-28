import Mathlib

/-!
# OEIS A086524: every prime of the form 6k - 1 is the mean of two successive terms of A086523

Source: https://oeis.org/A086524 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Amarnath Murthy, Jul 30 2003), offset 1: Primes arising as the arithmetic mean of a pair
of successive terms of A086523. Data: 11, 23, 41, 47, 71, 107, 101, 113, 167, ... Comment: Every
term == -1 (mod 6). Conjecture: every prime of the form 6k-1 is a member.

A086523 (Amarnath Murthy, Jul 30 2003), offset 1: Beginning with 5, distinct odd primes such
that the arithmetic mean of every pair of successive terms is prime. Data: 5, 17, 29, 53, 41,
101, 113, 89, 137, ...

Formalization notes:
* A086523 is the greedy sequence: after the terms so far, the next term is the least odd prime
  not used yet whose arithmetic mean with the last term is a prime (`next`). This reproduces the
  entry's data. If no such prime existed, `next` would give 0 (sInf of the empty set); the
  statement is meaningful either way.
* The mean of t and q is a prime m exactly when t + q = 2m with m prime.
* With offset 1, a(n) is the last element of `terms (n - 1)`, the list of the first n terms.
* A prime p is a member of A086524 when a(n) + a(n+1) = 2p for some n >= 1. The comment's first
  sentence (every member is == -1 mod 6) is a stated property, not a conjecture; `main` is the
  conjecture: every prime p with p == 5 (mod 6), that is p = 6k - 1, is a member.
-/

namespace OMA.S_oeis_a086524

/-- The greedy choice after the terms L: the least odd prime q not in L such that the arithmetic
mean of the last term of L and q is a prime. -/
noncomputable def next (L : List ℕ) : ℕ :=
  sInf {q | q.Prime ∧ q ≠ 2 ∧ q ∉ L ∧ ∃ m, m.Prime ∧ L.getLast?.getD 0 + q = 2 * m}

/-- The first n + 1 terms of A086523, beginning with 5. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [5]
  | n + 1 => terms n ++ [next (terms n)]

/-- A086523 (offset 1): a(n) is the n-th term. -/
noncomputable def a (n : ℕ) : ℕ := (terms (n - 1)).getLast?.getD 0

/-- Murthy's conjecture: every prime of the form 6k - 1 is the arithmetic mean of two successive
terms of A086523. -/
theorem main : ∀ p : ℕ, p.Prime → p % 6 = 5 → ∃ n : ℕ, 1 ≤ n ∧ a n + a (n + 1) = 2 * p := by
  sorry

end OMA.S_oeis_a086524
