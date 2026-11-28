import Mathlib

/-!
# A387243: the smallest positive `k` with `(k+n)^k < (k+1)^(k+1)`

Source: https://oeis.org/A387243
Credit: @avivorly

A387243 (offset 1): `a(n)` is the smallest positive `k` such that `(k+n)^k < (k+1)^(k+1)`.
Data: 1, 1, 2, 11, 41, 130, 378, 1064, 2940, 8053, 21966, ...

A381767 (offset 1): `a(n) = ceiling(n^(n/(n-1)))` with `a(1) = 1`.
Data: 1, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, ...

A382131 (offset 1): the complement of A381767.
Data: 2, 3, 5, 15, 46, 136, 385, 1072, 2949, 8063, 21977, ...

Conjecture (in the entry A387243): `a(n) = A382131(n) - n`.

Conventions:
- A381767 is written in integer form: `A381767 1 = 1`, and for `m ≥ 2`, `A381767 m` is the least natural number
  `N` with `m^m ≤ N^(m-1)`. This is `⌈m^(m/(m-1))⌉`: the map `y ↦ y^(m-1)` is strictly increasing on `y ≥ 0` and
  `(m^(m/(m-1)))^(m-1) = m^m`, so a natural number `N` has `m^m ≤ N^(m-1)` exactly when `m^(m/(m-1)) ≤ N`, and the
  least such `N` is the ceiling. The entry's own Python program computes it the same way: the integer `(n-1)`-th
  root of `n^n`, rounded up. (The value at `0`, outside the offset, is `0` and plays no role below.)
- A382131 is the complement of A381767 in the positive integers: `A382131 n` is the `n`-th smallest positive integer
  that is not `A381767 m` for any `m ≥ 1` (`Nat.nth` counts from `0`, hence `n - 1`).
- `A387243 n` is the least element (`sInf`) of the set of positive `k` with `(k+n)^k < (k+1)^(k+1)`.
- The subtraction `A382131 n - n` is in `ℕ`; it is exact, as `A382131 n ≥ n + 1` (the complement consists of
  integers `≥ 2`, since `1 = A381767 1`). So `main` says that for every `n ≥ 1` such a `k` exists and the least one
  is `A382131 n - n` (if no such `k` existed, `A387243 n` would be `sInf ∅ = 0 < A382131 n - n`).
-/

namespace OMA.S_oeis_a387243

/-- A381767: `A381767 1 = 1`, and for `m ≥ 2` the least `N` with `m^m ≤ N^(m-1)`, i.e. `⌈m^(m/(m-1))⌉`. -/
noncomputable def A381767 (m : ℕ) : ℕ :=
  if m = 1 then 1 else sInf {N : ℕ | m ^ m ≤ N ^ (m - 1)}

/-- A382131 (offset 1): the `n`-th smallest positive integer not in the range of A381767 (on `m ≥ 1`). -/
noncomputable def A382131 (n : ℕ) : ℕ :=
  Nat.nth (fun x : ℕ => 0 < x ∧ ∀ m : ℕ, 1 ≤ m → A381767 m ≠ x) (n - 1)

/-- A387243 (offset 1): the smallest positive `k` with `(k+n)^k < (k+1)^(k+1)`. -/
noncomputable def A387243 (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (k + n) ^ k < (k + 1) ^ (k + 1)}

theorem main : ∀ n : ℕ, 1 ≤ n → A387243 n = A382131 n - n := by
  sorry

end OMA.S_oeis_a387243
