import Mathlib

/-!
# A249264: Sequence of distinct least nonnegative numbers such that the average of the first n terms is a triangular number.

Source: https://oeis.org/A249264
Credit: @avivorly

A249264 (Derek Orr, Oct 2014): "Sequence of distinct least nonnegative numbers such that the average of the first
n terms is a triangular number." That is, `a(n)` is the least `m ≥ 0`, not among `a(1), ..., a(n-1)`, such that
`(a(1) + ... + a(n-1) + m) / n` is a triangular number `k(k+1)/2`, `k ≥ 0`. Data: 0, 2, 1, 9, 3, 21, 6, 38, 10, 60,
15, 87, 112, 28, 148, 36, ...

Conjecture (in the entry): "Conjectured: For n > 6, a(2*n-1) = A000566(n) and a(2*n) = A000217(n)."
Here A000566(n) = n(5n-3)/2 (heptagonal numbers) and A000217(n) = n(n+1)/2 (triangular numbers).

Conventions:
- Offset 1. `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms, built by recursion on `n`; for `n ≥ 1`,
  `a n = next n (pre (n - 1))` is the least admissible `n`-th term after the first `n - 1` terms. `a 0 = 0` is a
  junk value; the conjecture only uses the indices `2n - 1` and `2n` with `n > 6`.
- The average of `n ≥ 1` numbers with sum `S` equals the triangular number `T(k) = k(k+1)/2` iff `S = n * T(k)`
  (`k(k+1)` is even, so `/ 2` in `ℕ` is exact). Triangular numbers start at `T(0) = 0` (the entry: a(1) = 0, the
  zeroth triangular number), and with the empty prefix `m = 0` is admissible, so the definition gives `a(1) = 0`.
- "least" is `sInf` on `ℕ`. The admissible set is never empty (`m = n * T(k) - S` with `k` large exceeds every
  earlier term), so the least admissible number exists at every step; this is a property of the definition, proved
  where needed, not an assumption.
- `n * (5 * n - 3) / 2` and `n * (n + 1) / 2` are read in `ℕ`; for `n > 6` neither `5 * n - 3` nor `/ 2` truncates.
-/

namespace OMA.S_oeis_a249264

/-- The least `m ≥ 0`, not in the list `l` of earlier terms, such that the sum of `l` and `m` is `n` times a
triangular number `k(k+1)/2`: the `n`-th term after the prefix `l` of the first `n - 1` terms. -/
noncomputable def next (n : ℕ) (l : List ℕ) : ℕ :=
  sInf {m : ℕ | m ∉ l ∧ ∃ k : ℕ, l.sum + m = n * (k * (k + 1) / 2)}

/-- `pre n = [a(1), ..., a(n)]`, the first `n` terms. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++ [next (n + 1) (pre n)]

/-- `a n` is A249264(n) for `n ≥ 1` (offset 1); `a 0 = 0` is a junk value. -/
noncomputable def a (n : ℕ) : ℕ := next n (pre (n - 1))

/-- The conjecture: for `n > 6`, `a(2n-1) = n(5n-3)/2` (A000566) and `a(2n) = n(n+1)/2` (A000217). -/
theorem main :
    ∀ n : ℕ, n > 6 → a (2 * n - 1) = n * (5 * n - 3) / 2 ∧ a (2 * n) = n * (n + 1) / 2 := by
  sorry

end OMA.S_oeis_a249264
