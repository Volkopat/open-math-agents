import Mathlib

/-!
# A265283: Number of ON cells in the n-th iteration of the Rule 94 elementary cellular automaton

Source: https://oeis.org/A265283
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 1, 3, 4, 6, 6, 8, 8, 10, 10, 12, 12, 14, ...) records in its FORMULA
section:

  Conjectures from Colin Barker, Dec 07 2015 and Apr 16 2019:
  a(n) = (5-(-1)^n+2*n)/2 = A213222(n+3) for n>1.
  a(n) = n+2 for n>1 and even.
  a(n) = n+3 for n>1 and odd.
  a(n) = a(n-1) + a(n-2) - a(n-3) for n>2.
  G.f.: (1+2*x-x^4) / ((1-x)^2*(1+x)).

Conventions:
* Cells are indexed by `ℤ`; a configuration is a function `ℤ → Bool` (`true` = ON, black).
* Generation `0` has a single ON cell, at position `0`.
* Wolfram's rule-number convention: the new state of cell `i` is bit number
  `4 * l + 2 * c + r` of the binary expansion of `94`, where `l`, `c`, `r` (each `0` or `1`)
  are the current states of cells `i - 1`, `i`, `i + 1`.
* `a n` is the number of ON cells in generation `n`. Since the rule maps an all-OFF
  neighbourhood to OFF (bit `0` of `94` is `0`), all ON cells of generation `n` lie in
  `[-n, n]`, so `a n` counts the ON cells `i = k - n` with `0 ≤ k ≤ 2 n`.
* The statement is the first conjectured formula, `a(n) = (5 - (-1)^n + 2 n) / 2` for `n > 1`,
  written without division as `2 * a(n) = 5 - (-1)^n + 2 * n` in `ℤ`; it is equivalent to the
  two parity cases. (The recurrence as printed fails at `n = 4`, since `a(4) = 6` but
  `a(3) + a(2) - a(1) = 7`; it holds for `n > 4`, which the generating function reflects.
  Those lines are not part of this statement.)
-/

namespace OMA.S_oeis_a265283

/-- The Rule 94 local update: bit `4 * l + 2 * c + r` of `94`. -/
def rule94 (l c r : Bool) : Bool :=
  Nat.testBit 94 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `ca n i` is the state of cell `i` in generation `n`, starting from a single ON cell at `0`. -/
def ca : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | n + 1 => fun i => rule94 (ca n (i - 1)) (ca n i) (ca n (i + 1))

/-- `a n` is the number of ON cells in generation `n` (all of which lie in `[-n, n]`):
the number of `k` with `0 ≤ k ≤ 2 n` such that cell `k - n` is ON. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter fun k : ℕ => ca n ((k : ℤ) - (n : ℤ)) = true).card

/-- The conjecture of A265283: `a(n) = (5 - (-1)^n + 2 n) / 2` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 2 * (a n : ℤ) = 5 - (-1) ^ n + 2 * n := by
  sorry

end OMA.S_oeis_a265283
