import Mathlib

/-!
# A000959: Lucky numbers

Source: https://oeis.org/A000959
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

OEIS comment: a line of 1's is formed, as in Gilbreath's conjecture, if instead of the lucky
numbers `1, 3, 7, 9, 13, 15, 21, 25, …` one uses `2` (or `4`), `3`, `5` (instead of `7`),
`9, 13, 15, 21, 25, …`.

## Encoding

* Lucky numbers via Ulam's sieve, starting from the odd numbers: `s 0 i = 2i + 1`; at stage `k`
  the survivor `L = s k (k + 1)` (that is `3, 7, 9, …`) is used and every `L`-th remaining
  number is removed, so the `i`-th survivor (0-indexed) is `s k (i + i / (L - 1))`. Positions
  `≤ k` no longer change after stage `k`, so `lucky n = s n n`.
* The modified sequence `b` replaces the first term by `c ∈ {2, 4}` and the third term `7` by
  `5`, keeping the rest of the lucky numbers.
* Gilbreath's process: row `0` is `b`, row `k + 1` lists the absolute differences of consecutive
  entries of row `k`. "A line of 1's is formed" means the first entry of every row `k ≥ 1` is `1`.
-/

namespace OMA.S_oeis_a000959

/-- Stages of the lucky-number sieve. -/
def s : ℕ → ℕ → ℕ
  | 0, i => 2 * i + 1
  | k + 1, i => s k (i + i / (s k (k + 1) - 1))

/-- The `n`-th lucky number (0-indexed): `1, 3, 7, 9, 13, …` -/
def lucky (n : ℕ) : ℕ := s n n

/-- The modified sequence: first term `c`, third term `5`, otherwise the lucky numbers. -/
def b (c : ℕ) (i : ℕ) : ℤ :=
  if i = 0 then c else if i = 2 then 5 else lucky i

/-- Gilbreath's iterated absolute differences of a sequence `x`. -/
def gilbreath (x : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, i => x i
  | k + 1, i => |gilbreath x k (i + 1) - gilbreath x k i|

theorem main :
    ∀ c ∈ ({2, 4} : Set ℕ), ∀ k : ℕ, 1 ≤ k → gilbreath (b c) k 0 = 1 := by
  sorry

end OMA.S_oeis_a000959
