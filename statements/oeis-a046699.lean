import Mathlib

/-!
# A046699: a(1) = a(2) = 1, a(n) = a(n - a(n-1)) + a(n-1 - a(n-2))

Source: https://oeis.org/A046699
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (OEIS): `a(n+1) = a(n) + A215530(a(n) + n)` for all `n > 0`, where A215530 (offset
`0`) is the limit of the string `0, 1` under the operation "repeat the string twice and append
`0`": `0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, …`.

## Encoding

* `prefixA k` is the list `[0, a(1), …, a(k+2)]` (index `0` is a dummy), built by the
  recurrence; `a n` reads entry `n` of `prefixA n`.
* `str k` is the `k`-th string of the A215530 construction (`str 0 = [0, 1]`); it has length
  `3 · 2ᵏ - 1 > k`, and each string is a prefix of the next, so `A215530(i)` is entry `i` of
  `str i`.
-/

namespace OMA.S_oeis_a046699

/-- `[0, a(1), …, a(k+2)]`. -/
def prefixA : ℕ → List ℕ
  | 0 => [0, 1, 1]
  | k + 1 =>
    let L := prefixA k
    let m := k + 3
    L ++ [L.getD (m - L.getD (m - 1) 0) 0 + L.getD (m - 1 - L.getD (m - 2) 0) 0]

/-- `a(n)` (offset `1`). -/
def a (n : ℕ) : ℕ := (prefixA n).getD n 0

/-- The strings of the A215530 construction. -/
def str : ℕ → List ℕ
  | 0 => [0, 1]
  | k + 1 => str k ++ str k ++ [0]

/-- `A215530(i)` (offset `0`). -/
def b (i : ℕ) : ℕ := (str i).getD i 0

theorem main : ∀ n : ℕ, 0 < n → a (n + 1) = a n + b (a n + n) := by
  sorry

end OMA.S_oeis_a046699
