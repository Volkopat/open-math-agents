import Mathlib

/-!
# A217866: last time n appears in the first differences of n*log(n)

Source: https://oeis.org/A217866
Credit: @avivorly

A217866 (Jon Perry, 2012): Last time n appears in the first differences of n*log(n): A217865.

A217865: First differences of A050504. Formula: a(n) = A050504(n+1) - A050504(n). Offset 1.

A050504: Integer part of n*log(n). Formula: a(n) = floor(n*log(n)). Offset 1 (data 0, 1, 3, 5, 8, 10, 13, ...).

Conjecture (in the entry): the last time n appears is always before the first time n+2 appears.

Conventions:
- `log` is the natural logarithm `Real.log`. `A050504 n = ⌊n * log n⌋`, an integer (for `n ≥ 1`, `n * log n ≥ 0`,
  so its integer part is its floor). It is used for `n ≥ 1` only (offset 1); its value at `n = 0` is never used.
- `A217865 k = A050504 (k + 1) - A050504 k` for `k ≥ 1` (offset 1), computed in `ℤ`, so there is no truncated
  subtraction. This is the entry's JavaScript `floor((i+1)*log(i+1)) - floor(i*log(i))`.
- `A217866 n` is the last index `i ≥ 1` with `A217865 i = n`, written as the supremum of that set of indices: it is
  the largest element whenever the set is nonempty and bounded above; Lean's `sSup` on `ℕ` is `0` otherwise (the
  entry's program prints `-1` when `n` does not occur). It is context only: `main` does not use it.
- `main`: for every `n`, every index `i ≥ 1` with `A217865 i = n` is smaller than every index `j ≥ 1` with
  `A217865 j = n + 2`. When `n` and `n + 2` both occur, and `n` occurs only finitely often, this is exactly the
  conjecture: the last time `n` appears (`A217866 n`) is before the first time `n + 2` appears (A217976 (n + 2)).
  When `n` or `n + 2` does not occur it is vacuous. If `n` occurred infinitely often, its last occurrence would not
  exist and `main` would still require every occurrence of `n` to precede every occurrence of `n + 2`.
- `n` ranges over all natural numbers (A217866 has offset 1; the extra case `n = 0` only adds a claim).
-/

namespace OMA.S_oeis_a217866

/-- A050504: the integer part of `n * log n`, that is `⌊n * log n⌋` (offset 1). -/
noncomputable def A050504 (n : ℕ) : ℤ := ⌊(n : ℝ) * Real.log (n : ℝ)⌋

/-- A217865: the first differences of A050504, `A217865 k = A050504 (k + 1) - A050504 k` (offset 1). -/
noncomputable def A217865 (k : ℕ) : ℤ := A050504 (k + 1) - A050504 k

/-- A217866: the last index `i ≥ 1` with `A217865 i = n` (the largest element of that set when it is nonempty and
bounded above; `0` otherwise). -/
noncomputable def A217866 (n : ℕ) : ℕ := sSup {i : ℕ | 1 ≤ i ∧ A217865 i = n}

/-- The conjecture: the last time `n` appears in A217865 is before the first time `n + 2` appears, stated as: every
index `i ≥ 1` with `A217865 i = n` is smaller than every index `j ≥ 1` with `A217865 j = n + 2`. -/
theorem main :
    ∀ n : ℕ, ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → A217865 i = n → A217865 j = n + 2 → i < j := by
  sorry

end OMA.S_oeis_a217866
