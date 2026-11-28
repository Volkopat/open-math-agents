import Mathlib

/-!
# A249265: distinct least nonnegative numbers whose running averages are Fibonacci numbers

Source: https://oeis.org/A249265
Credit: @avivorly

A249265 (offset 1): Sequence of distinct least nonnegative numbers such that the average of the first `n` terms is a
Fibonacci number. The entry adds: this is the same concept as A248982, but with `a(1) = 0`, the zeroth Fibonacci
number. Data: `0, 2, 1, 5, 7, 3, 17, 29, 8, 58, 13, 109, 21, 203, 34, 370, 55, 667, 89, 1189, 144, ...`;
for example `a(4) = 5` (the average of `{0, 2, 1, 5}` is `2`) and `a(5) = 7` (the average of `{0, 2, 1, 5, 7}` is `3`).

Definition: `a(n)` is the least `x ≥ 0` that is not among `a(1), ..., a(n-1)` and makes the average
`(a(1) + ... + a(n-1) + x) / n` a Fibonacci number, i.e. `a(1) + ... + a(n-1) + x = n * F(k)` for some `k`.

Conjecture (Colin Barker, Oct 24 2014, in the entry): `a(n) = 2*a(n-2) + a(n-4) - 2*a(n-6) - a(n-8)` for `n > 15`.

Conventions:
- `Nat.fib` is the Fibonacci sequence `F(0) = 0, F(1) = 1, F(n+2) = F(n) + F(n+1)` (A000045); a Fibonacci number is a
  value `Nat.fib k`, `k ≥ 0` (so `0` counts, as the entry's comment requires for `a(1) = 0`).
- The average must be an exact Fibonacci number: the sum of the first `n` terms equals `n * Nat.fib k`.
- `firstTerms n` is the list `[a(1), ..., a(n)]`, built greedily; `nextTerm l` is the term that follows the list `l`
  of earlier terms: the least `x` not in `l` with `l.sum + x = (l.length + 1) * Nat.fib k` for some `k`.
  That set is never empty (for large `k`, `(l.length + 1) * Nat.fib k - l.sum` exceeds every element of `l`), so the
  junk value `sInf ∅ = 0` never arises; it would be harmless anyway.
- `a 0 = 0` is a junk value outside the offset; the statement only uses indices `n - 8 ≥ 8`.
- The recurrence is stated in `ℤ` (it has minus signs); the indices `n - 2, ..., n - 8` are natural numbers, exact
  since `n > 15`.
-/

namespace OMA.S_oeis_a249265

/-- The greedy term after the list `l` of earlier terms: the least `x` not in `l` such that `l.sum + x` is
`(l.length + 1)` times a Fibonacci number. -/
noncomputable def nextTerm (l : List ℕ) : ℕ :=
  sInf {x : ℕ | x ∉ l ∧ ∃ k : ℕ, l.sum + x = (l.length + 1) * Nat.fib k}

/-- `firstTerms n` is the list `[a(1), ..., a(n)]` of the first `n` terms. -/
noncomputable def firstTerms : ℕ → List ℕ
  | 0 => []
  | n + 1 => firstTerms n ++ [nextTerm (firstTerms n)]

/-- A249265(n), offset 1: `a (n + 1)` is the greedy term after the first `n` terms (`a 0 = 0` is junk). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => nextTerm (firstTerms n)

theorem main : ∀ n : ℕ, 15 < n →
    (a n : ℤ) = 2 * (a (n - 2) : ℤ) + (a (n - 4) : ℤ) - 2 * (a (n - 6) : ℤ) - (a (n - 8) : ℤ) := by
  sorry

end OMA.S_oeis_a249265
