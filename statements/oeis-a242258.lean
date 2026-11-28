import Mathlib

/-!
# A242258: Number of summands in s-greedy sum of s(n), where s(n) = A000041(n), the partitions numbers.

Source: https://oeis.org/A242258
Credit: @avivorly

A242258 (offset 2): the number of summands in the `s`-greedy sum of `s(n)`, where `s(n) = A000041(n)` is the number
of partitions of `n`: 1, 2, 2, 2, 3, 3, 2, 3, ... (e.g. `s(6) = 11 = 7 + 3 + 1`, `s(8) = 22 = 15 + 7`).
The greedy sum and greedy summability are defined in A242252: starting from `x = s(n)`, repeatedly subtract the
largest available term of `s` (the first one taken is the largest term `< x`); the greedy residue is what remains
when no term fits, and `x` is greedy summable when the residue is `0`.

Conjecture (in the entry, 2014): `A000041(n)` is `A000041`-greedy summable for `n >= 3`.

Conventions:
- `s(n) = A000041(n)` is the number of partitions of `n` (`Nat.Partition n`), for `n ≥ 1`: 1, 2, 3, 5, 7, 11, ...;
  these terms are strictly increasing, so the terms below `s(n)` are `s(n-1), ..., s(1)`.
- The greedy algorithm is the one of the entry's Mathematica program and examples: start with `r = s(n)` and, for
  `j = n - 1` down to `1`, subtract `s(j)` from `r` whenever `s(j) ≤ r` (each term below `s(n)` is tried once, largest
  first). The residue is the final `r`. (A242252's prose says the next term is the largest `s(j) < d` for the current
  remainder `d`; with a strict `<` at every step no residue could ever be `0`, contradicting the entry's examples such as
  `5 = 3 + 2`, so the remainder steps use `≤`, as the program does. With `s(j) ≤ r` a term is never needed twice here,
  but the program's reading is the one stated.)
-/

namespace OMA.S_oeis_a242258

/-- `s(n) = A000041(n)`, the number of partitions of `n`. -/
def s (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- One greedy step with the term `s j`: subtract it if it fits. -/
def greedyStep (r j : ℕ) : ℕ := if s j ≤ r then r - s j else r

/-- The `s`-greedy residue of `s(n)`: start with `s(n)` and try `s(n-1), s(n-2), ..., s(1)` in turn. -/
def greedyResidue (n : ℕ) : ℕ :=
  ((List.range (n - 1)).map (· + 1)).reverse.foldl greedyStep (s n)

theorem main : ∀ n : ℕ, 3 ≤ n → greedyResidue n = 0 := by
  sorry

end OMA.S_oeis_a242258
