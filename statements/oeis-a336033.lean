import Mathlib

/-!
# A336033: a(n) is the number of k such that 1 <= k < n and a(k) XOR ... XOR a(n-1) = 0 (where XOR
denotes the bitwise XOR operator).

Source: https://oeis.org/A336033 (Rémy Sigrist). Related: https://oeis.org/A340488
Credit: @Squee451

Data (offset 1): 0, 1, 0, 1, 2, 0, 1, 0, 1, 2, 3, 2, 2, 3, 4, 0, 1, 0, 1, 2, 0, 1, 0, 1, 2, 3, ...

The entry's comment: These are (a strong conjecture) the "y" values from A340488.

A340488 (offset 1; data 0, 0, 1, 1, 0, 2, 2, 3, 3, 2, 0, 3, 1, 3, 0, 4, ...) is defined by:
a(n+1) = XOR(a(n), y) for n >= 1, where y is the number of m < n such that a(m) = a(n); a(1) = 0.
Its entry states the same conjecture: "the y sequence appears to be A336033".
So the conjecture is: for every n >= 1, A336033(n) equals y(n), the number of m with 1 <= m < n and
A340488(m) = A340488(n).

Conventions.
* Both sequences have offset 1. `aPrefix n` is the list of the first `n` terms of A336033 and
  `xPrefix n` the list of the first `n` terms of A340488, each built term by term from its
  definition; `a n`, `x n` and `y n` read off the n-th term (1-indexed; the value at `n = 0` is a
  placeholder and the statement is only about `n ≥ 1`).
* In `aPrefix (n+1)`, with `xs = [a(1), ..., a(n)]`, the index `k` of the definition is `j + 1` for
  `j` in `List.range n`, and `xs.drop j = [a(j+1), ..., a(n)]` is the block whose XOR must vanish.
-/

namespace OMA.S_oeis_a336033

/-- The first `n` terms of A336033. -/
def aPrefix : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let xs := aPrefix n
    xs ++ [((List.range n).filter fun j => (xs.drop j).foldl (· ^^^ ·) 0 = 0).length]

/-- A336033 (1-indexed). -/
def a (n : ℕ) : ℕ := (aPrefix n).getD (n - 1) 0

/-- The first `n` terms of A340488. -/
def xPrefix : ℕ → List ℕ
  | 0 => []
  | 1 => [0]
  | n + 2 =>
    let xs := xPrefix (n + 1)
    let cur := xs.getD n 0
    xs ++ [cur ^^^ (xs.take n).count cur]

/-- A340488 (1-indexed). -/
def x (n : ℕ) : ℕ := (xPrefix n).getD (n - 1) 0

/-- The "y" value at index `n`: the number of `m` with `1 ≤ m < n` and `x m = x n`. -/
def y (n : ℕ) : ℕ := ((xPrefix n).take (n - 1)).count (x n)

/-- For every `n ≥ 1`, A336033(n) is the y value of A340488 at index n. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = y n := by
  sorry

end OMA.S_oeis_a336033
